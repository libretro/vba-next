#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <memalign.h>
#include <time.h>

#include <compat/msvc.h>

#include <streams/file_stream.h>

#include "system.h"
#include "globals.h"

#ifdef __PS3__
#include <ppu_intrinsics.h>
#endif

#include "port.h"
#include "gba.h"
#include "memory.h"
#include "sound.h"




#define CLOCKTICKS_UPDATE_TYPE16  codeTicksAccessSeq16(bus.armNextPC) + 1
#define CLOCKTICKS_UPDATE_TYPE32  codeTicksAccessSeq32(bus.armNextPC) + 1
#define CLOCKTICKS_UPDATE_TYPE16P (codeTicksAccessSeq16(bus.armNextPC) << 1) + codeTicksAccess(bus.armNextPC, BITS_16) + 3
#define CLOCKTICKS_UPDATE_TYPE32P (codeTicksAccessSeq32(bus.armNextPC) << 1) + codeTicksAccess(bus.armNextPC, BITS_32) + 3

/* Indexes into the line array */
#define Layer_BG0 0
#define Layer_BG1 1
#define Layer_BG2 2
#define Layer_BG3 3
#define Layer_OBJ 4
#define Layer_WIN_OBJ 5 /* Used by VBA for OBJ opacity tests */

#define LayerMask_BG0  (1 << Layer_BG0)
#define LayerMask_BG1  (1 << Layer_BG1)
#define LayerMask_BG2  (1 << Layer_BG2)
#define LayerMask_BG3  (1 << Layer_BG3)
#define LayerMask_OBJ  (1 << Layer_OBJ)
/* Used in R_WIN_* to indicate whether color effects are enabled */
#define LayerMask_SFX  (1 << 5)

#if USE_FRAME_SKIP

/* Frameskip state: used only within gba.c (SetFrameskip below is the
 * public accessor, declared in gba.h). These were non-static, i.e.
 * accidental global symbols. */
static int fs_count = 0;
static int fs_type = 0;
static int fs_type_a = 0;
static int fs_type_b = 0;
static bool fs_draw = false;

void SetFrameskip(int code)
{
	fs_type = code;
	fs_type_a = (0xF0 & fs_type) >> 4;
	fs_type_b = 0xF & fs_type;
}
#endif

typedef void (*renderfunc_t)(int renderer_idx);

renderfunc_t GetRenderFunc(int renderer_idx, int mode, int type);

/* (max/min helpers removed; their two call sites in gfxDrawRotScreen
 * inline the ternary directly to avoid colliding with MSVC's
 * <stdlib.h> max/min macros and to drop the unused helper symbols.) */

uint8_t *rom = 0;
uint8_t *bios = 0;
uint8_t *vram = 0;
uint16_t *pix = 0;
uint8_t *oam = 0;
uint8_t *ioMem = 0;
uint8_t *internalRAM = 0;
uint8_t *workRAM = 0;
uint8_t *paletteRAM = 0;

#ifdef MSB_FIRST
/* Host-endian shadows of paletteRAM and OAM, refreshed once per scanline.
 * The renderer reads palette/OAM entries millions of times per frame via
 * READ16LE in the per-pixel and per-sprite loops; on BE that's a __lhbrx
 * byteswap on every access.  By snapshotting the byteswapped form into a
 * host-endian shadow once per scanline (0x200+0x200 swaps), the per-pixel
 * reads become plain `*ptr` loads with no swap.  Net ~210k byteswaps/frame
 * eliminated for the cost of ~64k sync swaps - ~3x reduction.
 *
 * Storage strategy:
 *  - !THREADED_RENDERER: a pair of file-scope shadows shared by the single
 *    render thread.  Main thread is the only writer; worker is the same
 *    thread, so no synchronization needed.
 *  - THREADED_RENDERER:  one pair of shadows per renderer_context (see the
 *    struct below).  Main thread syncs into the destination context's buffer
 *    BEFORE setting renderer_state=1, so each worker reads its own snapshot
 *    with no shared state and no race against subsequent scanline setup. */
static INLINE void palette_native_sync(uint16_t *dst)
{
	int i;
	/* paletteRAM is stored byte-swapped on BE so READ16LE returns the natural
	 * (LE-host-equivalent) value; copy that into dst and the renderer reads
	 * it without swapping. */
	const uint16_t *src = (const uint16_t *)paletteRAM;
	for(i = 0; i < 0x200; ++i)
		dst[i] = READ16LE(&src[i]);
}

static INLINE void oam_native_sync(uint16_t *dst)
{
	int i;
	const uint16_t *src = (const uint16_t *)oam;
	for(i = 0; i < 0x200; ++i)
		dst[i] = READ16LE(&src[i]);
}

#if !THREADED_RENDERER
/* Non-threaded BE: shared shadows live at file scope. */
static uint16_t palette_native[0x200];
static uint16_t oam_native[0x200];
#define PAL_U16 palette_native
#define OAM_U16 oam_native
#else
/* Threaded BE: shadows live in the renderer_context; PAL_U16 / OAM_U16
 * resolve via the renderer_ctx in scope at the use site. */
#define PAL_U16 renderer_ctx.palette_native
#define OAM_U16 renderer_ctx.oam_native
#endif

#else /* !MSB_FIRST: LE host - paletteRAM / oam are already host-endian. */
#ifdef PER_FRAME_BATCHED
/* Batched mode on LE needs per-context palette/OAM snapshots because all 160
 * scanlines render at end-of-frame; reading paletteRAM/oam directly would
 * give every scanline the END-OF-FRAME palette/OAM rather than each line's
 * own state.  The data is already host-endian, so the sync is a plain
 * memcpy, and PAL_U16/OAM_U16 resolve via renderer_ctx like the BE path. */
static INLINE void palette_native_sync(uint16_t *dst)
{
	memcpy(dst, paletteRAM, 0x200 * sizeof(uint16_t));
}
static INLINE void oam_native_sync(uint16_t *dst)
{
	memcpy(dst, oam, 0x200 * sizeof(uint16_t));
}
#define PAL_U16 renderer_ctx.palette_native
#define OAM_U16 renderer_ctx.oam_native
#else
#define PAL_U16 ((uint16_t *)paletteRAM)
#define OAM_U16 ((uint16_t *)oam)
static INLINE void palette_native_sync(uint16_t *dst) { (void)dst; /* no-op on LE */ }
static INLINE void oam_native_sync(uint16_t *dst)     { (void)dst; /* no-op on LE */ }
#endif
#endif

/* Used only within gba.c (the renderer_ctx struct has its own
 * same-named members; these file-scope ones were non-static by
 * oversight). */
static int renderfunc_mode = 0;
static int renderfunc_type = 0;

#if USE_MOTION_SENSOR
hardware_t hardware;

static void hardware_reset(void)
{
	hardware.tilt_x = 0;
	hardware.tilt_y = 0;
	hardware.direction = 0;
	hardware.pinState = 0;
	hardware.gyroSample = 0;
	hardware.readWrite = false;
	hardware.gyroEdge = false;
}
#endif

#if THREADED_RENDERER

	/*THREADED_RENDERER_COUNT: 1 to 4, or BATCHED_LINES (160) in PER_FRAME_BATCHED mode */
	#ifdef PER_FRAME_BATCHED
		#define THREADED_RENDERER_COUNT 160
	#elif VITA
		#define THREADED_RENDERER_COUNT 2
	#else
		#define THREADED_RENDERER_COUNT 1
	#endif

	#include "thread.h"

	/* Runtime flag controlling whether the renderer worker thread is
	 * actually used.  Initialized from DEFAULT_THREADED_RENDERER_ENABLED
	 * (set in the Vita Makefile to 1, default 0 elsewhere) and
	 * overridable via the vbanext_threaded_renderer core option, which
	 * is read once at retro_init time before ThreadedRendererStart runs.
	 * When 0, the worker thread is never spawned and the render-loop
	 * body is invoked synchronously on the emulation thread immediately
	 * after each postRender() publish. */
	#ifndef DEFAULT_THREADED_RENDERER_ENABLED
		#define DEFAULT_THREADED_RENDERER_ENABLED 0
	#endif
	int g_threaded_renderer_enabled = DEFAULT_THREADED_RENDERER_ENABLED;

	static int threaded_renderer_idx = 0;
#ifdef PER_FRAME_BATCHED
	static int batched_publish_idx = 0;
#endif
	static uint32_t threaded_gfxinwin_ver[2] = {1, 1};
	static volatile uint32_t threaded_background_ver = 0;
	static volatile int threaded_renderer_ready = 0;

	static void threaded_renderer_loop(void* p);
	static void threaded_renderer_loop0(void* p);

	typedef struct {
		thread_t renderer_thread_id;

		volatile int renderer_control;
		volatile int renderer_state;
		int renderfunc_mode;
		int renderfunc_type;
		int vcount;

		uint32_t background_ver;
		uint32_t gfxinwin_ver[2];

		uint16_t io_registers[0x200];
		uint32_t line[6][240];
		int lineOBJpixleft[128];
		bool gfxInWin[2][240];

#if defined(MSB_FIRST) || defined(PER_FRAME_BATCHED)
		/* Per-context host-endian shadow of paletteRAM and OAM.  On BE this is
		 * a byte-swapped snapshot that lets the renderer skip per-pixel swaps.
		 * In batched mode on LE the snapshot is a plain memcpy and is required
		 * for correctness: rendering happens at end-of-frame, so reading
		 * paletteRAM/oam directly would give every scanline the end-of-frame
		 * state.  Synced in postRender before the scanline is considered
		 * published; read by the renderer during processing. */
		uint16_t palette_native[0x200];
		uint16_t oam_native[0x200];
#endif

		bool draw_objwin;
		bool draw_sprites;
		uint16_t mosaic;
		uint16_t bldmod;
		uint16_t layers;

		int bg2c;
		int bg3c;
		int bg2x;
		int bg2y;
		int bg3x;
		int bg3y;

		int bg2x_l;
		int bg2x_h;
		int bg2y_l;
		int bg2y_h;
		int bg3x_l;
		int bg3x_h;
		int bg3y_l;
		int bg3y_h;
	} renderer_context;

	static void init_renderer_context(renderer_context *ctx) {
		ctx->renderer_control = 0;
		ctx->renderer_state = 0;
		ctx->background_ver = 0;
		ctx->gfxinwin_ver[0] = 0;
		ctx->gfxinwin_ver[1] = 0;
		memset(ctx->line[Layer_BG0], -1, 240 * sizeof(uint32_t));
		memset(ctx->line[Layer_BG1], -1, 240 * sizeof(uint32_t));
		memset(ctx->line[Layer_BG2], -1, 240 * sizeof(uint32_t));
		memset(ctx->line[Layer_BG3], -1, 240 * sizeof(uint32_t));
	}

	static renderer_context threaded_renderer_contexts[THREADED_RENDERER_COUNT];

	/* C89 has no references.  Provide `renderer_ctx` as a textual alias for
	 * (*_renderer_ctx_) so that the 100+ existing `renderer_ctx.field` use
	 * sites compile unchanged.  INIT_RENDERER_CONTEXT introduces the pointer
	 * in local scope; subsequent macro expansions of `renderer_ctx.field`
	 * resolve via the pointer with no source changes. */
	#define INIT_RENDERER_CONTEXT(__renderer_idx__) renderer_context *_renderer_ctx_ = &threaded_renderer_contexts[__renderer_idx__]
	#define renderer_ctx (*_renderer_ctx_)

	#define RENDERER_BG2C renderer_ctx.bg2c
	#define RENDERER_BG3C renderer_ctx.bg3c

	#define RENDERER_BG2X renderer_ctx.bg2x
	#define RENDERER_BG2Y renderer_ctx.bg2y
	#define RENDERER_BG3X renderer_ctx.bg3x
	#define RENDERER_BG3Y renderer_ctx.bg3y

	#define RENDERER_BG2X_L renderer_ctx.bg2x_l
	#define RENDERER_BG2X_H renderer_ctx.bg2x_h
	#define RENDERER_BG2Y_L renderer_ctx.bg2y_l
	#define RENDERER_BG2Y_H renderer_ctx.bg2y_h
	#define RENDERER_BG3X_L renderer_ctx.bg3x_l
	#define RENDERER_BG3X_H renderer_ctx.bg3x_h
	#define RENDERER_BG3Y_L renderer_ctx.bg3y_l
	#define RENDERER_BG3Y_H renderer_ctx.bg3y_h

	#define RENDERER_PALETTE paletteRAM
	#define RENDERER_OAM oam

	#define RENDERER_LINE renderer_ctx.line
	#define RENDERER_IO_REGISTERS renderer_ctx.io_registers
	#define RENDERER_MOSAIC renderer_ctx.mosaic
	#define RENDERER_BLDMOD renderer_ctx.bldmod
	#define RENDERER_GRAPHICS_LAYERS renderer_ctx.layers
	#define RENDERER_LINE_OBJ_PIX_LEFT renderer_ctx.lineOBJpixleft
	#define RENDERER_GFX_IN_WIN renderer_ctx.gfxInWin

	#define RENDERER_R_VCOUNT renderer_ctx.vcount
	#define RENDERER_R_DISPCNT_Video_Mode renderer_ctx.renderfunc_mode

	#define RENDERER_R_DISPCNT_Screen_Display_BG0 (RENDERER_GRAPHICS_LAYERS & (1 <<  8))
	#define RENDERER_R_DISPCNT_Screen_Display_BG1 (RENDERER_GRAPHICS_LAYERS & (1 <<  9))
	#define RENDERER_R_DISPCNT_Screen_Display_BG2 (RENDERER_GRAPHICS_LAYERS & (1 << 10))
	#define RENDERER_R_DISPCNT_Screen_Display_BG3 (RENDERER_GRAPHICS_LAYERS & (1 << 11))
	#define RENDERER_R_DISPCNT_Screen_Display_OBJ (RENDERER_GRAPHICS_LAYERS & (1 << 12))
	#define RENDERER_R_DISPCNT_Window_0_Display   (RENDERER_GRAPHICS_LAYERS & (1 << 13))
	#define RENDERER_R_DISPCNT_Window_1_Display   (RENDERER_GRAPHICS_LAYERS & (1 << 14))
	#define RENDERER_R_DISPCNT_OBJ_Window_Display (RENDERER_GRAPHICS_LAYERS & (1 << 15))

	#define RENDERER_R_WIN_Window0_X1 (RENDERER_IO_REGISTERS[REG_WIN0H] >> 8)
	#define RENDERER_R_WIN_Window0_X2 (RENDERER_IO_REGISTERS[REG_WIN0H] & 0xFF)
	#define RENDERER_R_WIN_Window0_Y1 (RENDERER_IO_REGISTERS[REG_WIN0V] >> 8)
	#define RENDERER_R_WIN_Window0_Y2 (RENDERER_IO_REGISTERS[REG_WIN0V] & 0xFF)

	#define RENDERER_R_WIN_Window1_X1 (RENDERER_IO_REGISTERS[REG_WIN1H] >> 8)
	#define RENDERER_R_WIN_Window1_X2 (RENDERER_IO_REGISTERS[REG_WIN1H] & 0xFF)
	#define RENDERER_R_WIN_Window1_Y1 (RENDERER_IO_REGISTERS[REG_WIN1V] >> 8)
	#define RENDERER_R_WIN_Window1_Y2 (RENDERER_IO_REGISTERS[REG_WIN1V] & 0xFF)

	#define RENDERER_R_WIN_Window0_Mask (RENDERER_IO_REGISTERS[REG_WININ] & 0xFF)
	#define RENDERER_R_WIN_Window1_Mask (RENDERER_IO_REGISTERS[REG_WININ] >> 8)
	#define RENDERER_R_WIN_Outside_Mask (RENDERER_IO_REGISTERS[REG_WINOUT] & 0xFF)
	#define RENDERER_R_WIN_OBJ_Mask     (RENDERER_IO_REGISTERS[REG_WINOUT] >> 8)

#else
	#define INIT_RENDERER_CONTEXT(__renderer_idx__) 0

    #define RENDERER_BG2C gfxBG2Changed
	#define RENDERER_BG3C gfxBG3Changed

	#define RENDERER_BG2X gfxBG2X
	#define RENDERER_BG2Y gfxBG2Y
	#define RENDERER_BG3X gfxBG3X
	#define RENDERER_BG3Y gfxBG3Y

	#define RENDERER_BG2X_L BG2X_L
	#define RENDERER_BG2X_H BG2X_H
	#define RENDERER_BG2Y_L BG2Y_L
	#define RENDERER_BG2Y_H BG2Y_H
	#define RENDERER_BG3X_L BG3X_L
	#define RENDERER_BG3X_H BG3X_H
	#define RENDERER_BG3Y_L BG3Y_L
	#define RENDERER_BG3Y_H BG3Y_H

	#define RENDERER_PALETTE paletteRAM
	#define RENDERER_IO_REGISTERS io_registers
	#define RENDERER_LINE line
	#define RENDERER_OAM oam
	#define RENDERER_MOSAIC MOSAIC
	#define RENDERER_BLDMOD BLDMOD
	#define RENDERER_GRAPHICS_LAYERS graphics.layerEnable
	#define RENDERER_LINE_OBJ_PIX_LEFT lineOBJpixleft
	#define RENDERER_GFX_IN_WIN gfxInWin

	#define RENDERER_R_VCOUNT (RENDERER_IO_REGISTERS[REG_VCOUNT])
	#define RENDERER_R_DISPCNT_Video_Mode (RENDERER_IO_REGISTERS[REG_DISPCNT] & 7)

	#define RENDERER_R_DISPCNT_Screen_Display_BG0 (RENDERER_GRAPHICS_LAYERS & (1 <<  8))
	#define RENDERER_R_DISPCNT_Screen_Display_BG1 (RENDERER_GRAPHICS_LAYERS & (1 <<  9))
	#define RENDERER_R_DISPCNT_Screen_Display_BG2 (RENDERER_GRAPHICS_LAYERS & (1 << 10))
	#define RENDERER_R_DISPCNT_Screen_Display_BG3 (RENDERER_GRAPHICS_LAYERS & (1 << 11))
	#define RENDERER_R_DISPCNT_Screen_Display_OBJ (RENDERER_GRAPHICS_LAYERS & (1 << 12))
	#define RENDERER_R_DISPCNT_Window_0_Display   (RENDERER_GRAPHICS_LAYERS & (1 << 13))
	#define RENDERER_R_DISPCNT_Window_1_Display   (RENDERER_GRAPHICS_LAYERS & (1 << 14))
	#define RENDERER_R_DISPCNT_OBJ_Window_Display (RENDERER_GRAPHICS_LAYERS & (1 << 15))

	#define RENDERER_R_WIN_Window0_X1 (RENDERER_IO_REGISTERS[REG_WIN0H] >> 8)
	#define RENDERER_R_WIN_Window0_X2 (RENDERER_IO_REGISTERS[REG_WIN0H] & 0xFF)
	#define RENDERER_R_WIN_Window0_Y1 (RENDERER_IO_REGISTERS[REG_WIN0V] >> 8)
	#define RENDERER_R_WIN_Window0_Y2 (RENDERER_IO_REGISTERS[REG_WIN0V] & 0xFF)

	#define RENDERER_R_WIN_Window1_X1 (RENDERER_IO_REGISTERS[REG_WIN1H] >> 8)
	#define RENDERER_R_WIN_Window1_X2 (RENDERER_IO_REGISTERS[REG_WIN1H] & 0xFF)
	#define RENDERER_R_WIN_Window1_Y1 (RENDERER_IO_REGISTERS[REG_WIN1V] >> 8)
	#define RENDERER_R_WIN_Window1_Y2 (RENDERER_IO_REGISTERS[REG_WIN1V] & 0xFF)

	#define RENDERER_R_WIN_Window0_Mask (RENDERER_IO_REGISTERS[REG_WININ] & 0xFF)
	#define RENDERER_R_WIN_Window1_Mask (RENDERER_IO_REGISTERS[REG_WININ] >> 8)
	#define RENDERER_R_WIN_Outside_Mask (RENDERER_IO_REGISTERS[REG_WINOUT] & 0xFF)
	#define RENDERER_R_WIN_OBJ_Mask     (RENDERER_IO_REGISTERS[REG_WINOUT] >> 8)

#endif

#define RENDERER_BACKDROP (PAL_U16[0] | 0x30000000)
#define RENDERER_R_BLDCNT_Color_Special_Effect ((RENDERER_BLDMOD >> 6) & 3)
#define RENDERER_R_BLDCNT_IsTarget1(target) ((target) & (RENDERER_BLDMOD     ))
#define RENDERER_R_BLDCNT_IsTarget2(target) ((target) & (RENDERER_BLDMOD >> 8))

/*============================================================
	GBA INLINE
============================================================ */

#define UPDATE_REG(address, value)	WRITE16LE(((uint16_t *)&ioMem[address]),value);
#define ARM_PREFETCH_NEXT		cpuPrefetch[1] = CPUReadMemoryQuick(bus.armNextPC+4);
#define THUMB_PREFETCH_NEXT		cpuPrefetch[1] = CPUReadHalfWordQuick(bus.armNextPC+2);

#define ARM_PREFETCH \
  {\
    cpuPrefetch[0] = CPUReadMemoryQuick(bus.armNextPC);\
    cpuPrefetch[1] = CPUReadMemoryQuick(bus.armNextPC+4);\
  }

#define THUMB_PREFETCH \
  {\
    cpuPrefetch[0] = CPUReadHalfWordQuick(bus.armNextPC);\
    cpuPrefetch[1] = CPUReadHalfWordQuick(bus.armNextPC+2);\
  }

#define MOSAIC_LOOP(__layer__, __mosaicX__) { \
	int m = 1; \
	int i = 0; \
	for (; i < 239; i++) { \
		RENDERER_LINE[__layer__][i+1] = RENDERER_LINE[__layer__][i]; \
		if (++m == __mosaicX__) { m = 1; i++; } \
	} \
}

static INLINE uint32_t gfxIncreaseBrightness(uint32_t color, int coeff) {
	color = (((color & 0xffff) << 16) | (color & 0xffff)) & 0x3E07C1F;
	color += ((((0x3E07C1F - color) * coeff) >> 4) & 0x3E07C1F);
	return (color >> 16) | color;
}

static INLINE uint32_t gfxDecreaseBrightness(uint32_t color, int coeff) {
	color = (((color & 0xffff) << 16) | (color & 0xffff)) & 0x3E07C1F;
	color -= (((color * coeff) >> 4) & 0x3E07C1F);
	return (color >> 16) | color;
}

static const uint8_t AlphaClampLUT[64] =
{
	0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
	0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
	0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F,
	0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F
};

#define GFX_ALPHA_BLEND(color, color2, ca, cb) {                                                         \
	int r = AlphaClampLUT[(((color & 0x1F) * ca) >> 4) + (((color2 & 0x1F) * cb) >> 4)];                 \
	int g = AlphaClampLUT[((((color >> 5) & 0x1F) * ca) >> 4) + ((((color2 >> 5) & 0x1F) * cb) >> 4)];   \
	int b = AlphaClampLUT[((((color >> 10) & 0x1F) * ca) >> 4) + ((((color2 >> 10) & 0x1F) * cb) >> 4)]; \
	color = (color & 0xFFFF0000) | (b << 10) | (g << 5) | r;	\
}

#define brightness_switch()                                                                \
	switch(RENDERER_R_BLDCNT_Color_Special_Effect) { \
		case SpecialEffect_Brightness_Increase:                                            \
			color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]); break;               \
		case SpecialEffect_Brightness_Decrease:                                            \
			color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]); break;               \
	}

#define alpha_blend_brightness_switch()                                                    \
	if(RENDERER_R_BLDCNT_IsTarget2(top2)) { \
		if(color < 0x80000000) {	\
			GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]); \
		} else if (RENDERER_R_BLDCNT_IsTarget1(top)) { \
			brightness_switch();                                                           \
		} \
	}

static int cpuNextEvent = 0;
static bool holdState = false;
static uint32_t cpuPrefetch[2];
static int cpuTotalTicks = 0;

static uint8_t memoryWait[16] =
  { 0, 0, 2, 0, 0, 0, 0, 0, 4, 4, 4, 4, 4, 4, 4, 0 };
static uint8_t memoryWaitSeq[16] =
  { 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 4, 4, 8, 8, 4, 0 };
static uint8_t memoryWait32[16] =
  { 0, 0, 5, 0, 0, 1, 1, 0, 7, 7, 9, 9, 13, 13, 4, 0 };
static uint8_t memoryWaitSeq32[16] =
  { 0, 0, 5, 0, 0, 1, 1, 0, 5, 5, 9, 9, 17, 17, 4, 0 };

/* GB sound-register address lookup; used only within this file.
 * Was non-static (accidental external linkage). */
static const int table [0x40] =
{
		0xFF10,     0,0xFF11,0xFF12,0xFF13,0xFF14,     0,     0,
		0xFF16,0xFF17,     0,     0,0xFF18,0xFF19,     0,     0,
		0xFF1A,     0,0xFF1B,0xFF1C,0xFF1D,0xFF1E,     0,     0,
		0xFF20,0xFF21,     0,     0,0xFF22,0xFF23,     0,     0,
		0xFF24,0xFF25,     0,     0,0xFF26,     0,     0,     0,
		     0,     0,     0,     0,     0,     0,     0,     0,
		0xFF30,0xFF31,0xFF32,0xFF33,0xFF34,0xFF35,0xFF36,0xFF37,
		0xFF38,0xFF39,0xFF3A,0xFF3B,0xFF3C,0xFF3D,0xFF3E,0xFF3F,
};

static int coeff[32] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
			11, 12, 13, 14, 15, 16, 16, 16, 16,
			16, 16, 16, 16, 16, 16, 16, 16, 16,
			16, 16, 16};

static uint8_t biosProtected[4];
static uint8_t cpuBitsSet[256];

static void CPUSwitchMode(int mode, bool saveState, bool breakLoop);
static bool N_FLAG = 0;
static bool C_FLAG = 0;
static bool Z_FLAG = 0;
static bool V_FLAG = 0;
static bool armState = true;
static bool armIrqEnable = true;
static int armMode = 0x1f;

typedef enum
{
  REG_DISPCNT = 0x000,
  REG_DISPSTAT = 0x002,
  REG_VCOUNT = 0x003,
  REG_BG0CNT = 0x004,
  REG_BG1CNT = 0x005,
  REG_BG2CNT = 0x006,
  REG_BG3CNT = 0x007,
  REG_BG0HOFS = 0x08,
  REG_BG0VOFS = 0x09,
  REG_BG1HOFS = 0x0A,
  REG_BG1VOFS = 0x0B,
  REG_BG2HOFS = 0x0C,
  REG_BG2VOFS = 0x0D,
  REG_BG3HOFS = 0x0E,
  REG_BG3VOFS = 0x0F,
  REG_BG2PA = 0x10,
  REG_BG2PB = 0x11,
  REG_BG2PC = 0x12,
  REG_BG2PD = 0x13,
  REG_BG2X_L = 0x14,
  REG_BG2X_H = 0x15,
  REG_BG2Y_L = 0x16,
  REG_BG2Y_H = 0x17,
  REG_BG3PA = 0x18,
  REG_BG3PB = 0x19,
  REG_BG3PC = 0x1A,
  REG_BG3PD = 0x1B,
  REG_BG3X_L = 0x1C,
  REG_BG3X_H = 0x1D,
  REG_BG3Y_L = 0x1E,
  REG_BG3Y_H = 0x1F,
  REG_WIN0H = 0x20,
  REG_WIN1H = 0x21,
  REG_WIN0V = 0x22,
  REG_WIN1V = 0x23,
  REG_WININ = 0x24,
  REG_WINOUT = 0x25,
  REG_BLDCNT = 0x28,
  REG_BLDALPHA = 0x29,
  REG_BLDY = 0x2A,
  REG_TM0D = 0x80,
  REG_TM0CNT = 0x81,
  REG_TM1D = 0x82,
  REG_TM1CNT = 0x83,
  REG_TM2D = 0x84,
  REG_TM2CNT = 0x85,
  REG_TM3D = 0x86,
  REG_TM3CNT = 0x87,
  REG_P1 = 0x098,
  REG_P1CNT = 0x099,
  REG_RCNT = 0x9A,
  REG_IE = 0x100,
  REG_IF = 0x101,
  REG_IME = 0x104,
  REG_HALTCNT = 0x180
} hardware_register;

static uint16_t io_registers[0x200];

/* Note: Some comments below are from the GBATEK document */
/* (http://problemkaputt.de/gbatek.htm). */

#define R_DISPCNT_Video_Mode (io_registers[REG_DISPCNT] & 7)

/* By default, BG0-3 and OBJ Display Flags (Bit 8-12) are used to */
/* enable/disable BGs and OBJ. When enabling Window 0 and/or 1 */
/* (Bit 13-14), color special effects may be used, and BG0-3 and */
/* OBJ are controlled by the window(s). */

#define R_DISPCNT_Screen_Display_BG0 (graphics.layerEnable & (1 <<  8))
#define R_DISPCNT_Screen_Display_BG1 (graphics.layerEnable & (1 <<  9))
#define R_DISPCNT_Screen_Display_BG2 (graphics.layerEnable & (1 << 10))
#define R_DISPCNT_Screen_Display_BG3 (graphics.layerEnable & (1 << 11))
#define R_DISPCNT_Screen_Display_OBJ (graphics.layerEnable & (1 << 12))
#define R_DISPCNT_Window_0_Display   (graphics.layerEnable & (1 << 13))
#define R_DISPCNT_Window_1_Display   (graphics.layerEnable & (1 << 14))
#define R_DISPCNT_OBJ_Window_Display (graphics.layerEnable & (1 << 15))

#define R_WIN_Window0_X1 (io_registers[REG_WIN0H] >> 8)
#define R_WIN_Window0_X2 (io_registers[REG_WIN0H] & 0xFF)
#define R_WIN_Window0_Y1 (io_registers[REG_WIN0V] >> 8)
#define R_WIN_Window0_Y2 (io_registers[REG_WIN0V] & 0xFF)

#define R_WIN_Window1_X1 (io_registers[REG_WIN1H] >> 8)
#define R_WIN_Window1_X2 (io_registers[REG_WIN1H] & 0xFF)
#define R_WIN_Window1_Y1 (io_registers[REG_WIN1V] >> 8)
#define R_WIN_Window1_Y2 (io_registers[REG_WIN1V] & 0xFF)

/* These return a 6-bit mask which corresponds which layers are */
/* visible in the corresponding window/region: */
/* Bits 0-3 : Whether BG0-BG3 are visible */
/* Bit   4  : Whether OBJ is visible */
/* Bit   5  : Whether special effects are enabled */

#define R_WIN_Window0_Mask (io_registers[REG_WININ] & 0xFF)
#define R_WIN_Window1_Mask (io_registers[REG_WININ] >> 8)
#define R_WIN_Outside_Mask (io_registers[REG_WINOUT] & 0xFF)
#define R_WIN_OBJ_Mask     (io_registers[REG_WINOUT] >> 8)

/* Indicates the currently drawn scanline, values in range from */
/* 160..227 indicate 'hidden' scanlines within VBlank area. */

#define R_VCOUNT (io_registers[REG_VCOUNT])

/* Two types of Special Effects are supported: */
/* Alpha Blending (Semi-Transparency) allows to combine colors */
/* of two selected surfaces. Brightness Increase/Decrease */
/* adjust the brightness of the selected surface. */

#define R_BLDCNT_Color_Special_Effect ((BLDMOD >> 6) & 3)
#define SpecialEffect_None                (0)
#define SpecialEffect_Alpha_Blending      (1)
#define SpecialEffect_Brightness_Increase (2)
#define SpecialEffect_Brightness_Decrease (3)

/* Special effect targets. */
#define R_BLDCNT_IsTarget1(target) ((target) & (BLDMOD     ))
#define R_BLDCNT_IsTarget2(target) ((target) & (BLDMOD >> 8))

/* The first 5 entries coincide with LayerMask_*. */
#define SpecialEffectTarget_BG0  (1 << Layer_BG0)
#define SpecialEffectTarget_BG1  (1 << Layer_BG1)
#define SpecialEffectTarget_BG2  (1 << Layer_BG2)
#define SpecialEffectTarget_BG3  (1 << Layer_BG3)
#define SpecialEffectTarget_OBJ  (1 << Layer_OBJ) /* Top-most OBJ */
#define SpecialEffectTarget_BD   (1 << 5        ) /* Backdrop */


/* Fast implementation of ternary operator. */
/* Implemented as a function (as opposed to a macro) to avoid */
/* evaluating the parameters more than once. */
FORCE_INLINE uint32_t SELECT(bool condition, uint32_t ifTrue, uint32_t ifFalse)
{
	/* Will be 0 if condition==true or 0xFFFFFFFF */
	/* if condition==false. */
	uint32_t testmask = (uint32_t)condition - 1;

	return (testmask & ifFalse) | (~testmask & ifTrue);
}

static uint16_t MOSAIC;

static uint16_t BG2X_L   = 0x0000;
static uint16_t BG2X_H   = 0x0000;
static uint16_t BG2Y_L   = 0x0000;
static uint16_t BG2Y_H   = 0x0000;
static uint16_t BG3X_L   = 0x0000;
static uint16_t BG3X_H   = 0x0000;
static uint16_t BG3Y_L   = 0x0000;
static uint16_t BG3Y_H   = 0x0000;
static uint16_t BLDMOD   = 0x0000; /* aka BLDCNT */
static uint16_t COLEV    = 0x0000; /* aka BLDALPHA */
static uint16_t COLY     = 0x0000; /* aka BLDY */
static uint16_t DM0SAD_L = 0x0000;
static uint16_t DM0SAD_H = 0x0000;
static uint16_t DM0DAD_L = 0x0000;
static uint16_t DM0DAD_H = 0x0000;
static uint16_t DM0CNT_L = 0x0000;
static uint16_t DM0CNT_H = 0x0000;
static uint16_t DM1SAD_L = 0x0000;
static uint16_t DM1SAD_H = 0x0000;
static uint16_t DM1DAD_L = 0x0000;
static uint16_t DM1DAD_H = 0x0000;
static uint16_t DM1CNT_L = 0x0000;
static uint16_t DM1CNT_H = 0x0000;
static uint16_t DM2SAD_L = 0x0000;
static uint16_t DM2SAD_H = 0x0000;
static uint16_t DM2DAD_L = 0x0000;
static uint16_t DM2DAD_H = 0x0000;
static uint16_t DM2CNT_L = 0x0000;
static uint16_t DM2CNT_H = 0x0000;
static uint16_t DM3SAD_L = 0x0000;
static uint16_t DM3SAD_H = 0x0000;
static uint16_t DM3DAD_L = 0x0000;
static uint16_t DM3DAD_H = 0x0000;
static uint16_t DM3CNT_L = 0x0000;
static uint16_t DM3CNT_H = 0x0000;

static uint8_t timerOnOffDelay = 0;
static uint16_t timer0Value = 0;
static uint32_t dma0Source = 0;
static uint32_t dma0Dest = 0;
static uint32_t dma1Source = 0;
static uint32_t dma1Dest = 0;
static uint32_t dma2Source = 0;
static uint32_t dma2Dest = 0;
static uint32_t dma3Source = 0;
static uint32_t dma3Dest = 0;
void (*cpuSaveGameFunc)(uint32_t,uint8_t) = flashSaveDecide;
static bool fxOn = false;
static bool windowOn = false;

/* Used only within gba.c. Was non-static; the redundant
 * `extern uint32_t mastercode;` forward declaration further down
 * (the definition here already precedes every use) is removed too. */
static uint32_t mastercode = 0;
static int cpuDmaTicksToUpdate = 0;

static const uint32_t TIMER_TICKS[4] = {0, 6, 8, 10};

static const uint8_t gamepakRamWaitState[4] = { 4, 3, 2, 8 };
static const uint8_t gamepakWaitState[4] = { 4, 3, 2, 8 };
static const uint8_t gamepakWaitState0[2] = { 2, 1 };
static const uint8_t gamepakWaitState1[2] = { 4, 1 };
static const uint8_t gamepakWaitState2[2] = { 8, 1 };

static int IRQTicks = 0;
static bool intState = false;

static bus_t bus;
static graphics_t graphics;

static memoryMap map[256];
static int clockTicks;

static int romSize = 0x2000000;
static uint32_t line[6][240];
static bool gfxInWin[2][240];
static int lineOBJpixleft[128];
uint64_t joy = 0;

static int gfxBG2Changed = 0;
static int gfxBG3Changed = 0;

static int gfxBG2X = 0;
static int gfxBG2Y = 0;
static int gfxBG3X = 0;
static int gfxBG3Y = 0;

static bool ioReadable[0x400];
static int gbaSaveType = 0; /* used to remember the save type on reset */

/*static int gfxLastVCOUNT = 0; */

/* Waitstates when accessing data */

#define DATATICKS_ACCESS_BUS_PREFETCH(address, value) \
do { \
	int addr = (address >> 24) & 15; \
	if ((addr>=0x08) || (addr < 0x02)) \
	{ \
		bus.busPrefetchCount=0; \
		bus.busPrefetch=false; \
	} \
	else if (bus.busPrefetch) \
	{ \
		int waitState = value; \
		waitState = (1 & ~waitState) | (waitState & waitState); \
		bus.busPrefetchCount = ((bus.busPrefetchCount+1)<<waitState) - 1; \
	} \
} while (0)

/* Waitstates when accessing data */

#define DATATICKS_ACCESS_32BIT(address)  (memoryWait32[(address >> 24) & 15])
#define DATATICKS_ACCESS_32BIT_SEQ(address) (memoryWaitSeq32[(address >> 24) & 15])
#define DATATICKS_ACCESS_16BIT(address) (memoryWait[(address >> 24) & 15])
#define DATATICKS_ACCESS_16BIT_SEQ(address) (memoryWaitSeq[(address >> 24) & 15])

/* Waitstates when executing opcode */
static INLINE int codeTicksAccess(uint32_t address, uint8_t bit32) /* THUMB NON SEQ */
{
	int addr = (address>>24) & 15;

	if ((unsigned)(addr - 0x08) <= 5)
	{
		if (bus.busPrefetchCount&0x1)
		{
			if (bus.busPrefetchCount&0x2)
			{
				bus.busPrefetchCount = ((bus.busPrefetchCount&0xFF)>>2) | (bus.busPrefetchCount&0xFFFFFF00);
				return 0;
			}
			bus.busPrefetchCount = ((bus.busPrefetchCount&0xFF)>>1) | (bus.busPrefetchCount&0xFFFFFF00);
			return memoryWaitSeq[addr]-1;
		}
	}
	bus.busPrefetchCount = 0;

	if(bit32)		/* ARM NON SEQ */
		return memoryWait32[addr];
   /* THUMB NON SEQ */
   return memoryWait[addr];
}

static INLINE int codeTicksAccessSeq16(uint32_t address) /* THUMB SEQ */
{
	int addr = (address>>24) & 15;

	if ((unsigned)(addr - 0x08) <= 5)
	{
		if (bus.busPrefetchCount&0x1)
		{
			bus.busPrefetchCount = ((bus.busPrefetchCount&0xFF)>>1) | (bus.busPrefetchCount&0xFFFFFF00);
			return 0;
		}
		else if (bus.busPrefetchCount>0xFF)
		{
			bus.busPrefetchCount=0;
			return memoryWait[addr];
		}
	}
	else
		bus.busPrefetchCount = 0;

	return memoryWaitSeq[addr];
}

static INLINE int codeTicksAccessSeq32(uint32_t address) /* ARM SEQ */
{
	int addr = (address>>24)&15;

	if ((unsigned)(addr - 0x08) <= 5)
	{
		if (bus.busPrefetchCount&0x1)
		{
			if (bus.busPrefetchCount&0x2)
			{
				bus.busPrefetchCount = ((bus.busPrefetchCount&0xFF)>>2) | (bus.busPrefetchCount&0xFFFFFF00);
				return 0;
			}
			bus.busPrefetchCount = ((bus.busPrefetchCount&0xFF)>>1) | (bus.busPrefetchCount&0xFFFFFF00);
			return memoryWaitSeq[addr];
		}
		else if (bus.busPrefetchCount > 0xFF)
		{
			bus.busPrefetchCount=0;
			return memoryWait32[addr];
		}
	}
	return memoryWaitSeq32[addr];
}

#define CPUReadByteQuick(addr)		map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]
#define CPUReadHalfWordQuick(addr)	READ16LE(((uint16_t*)&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]))
#define CPUReadMemoryQuick(addr)	READ32LE(((uint32_t*)&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]))

static bool stopState = false;
extern bool cpuSramEnabled;
extern bool cpuFlashEnabled;
extern bool cpuEEPROMEnabled;

static bool timer0On = false;
static int timer0Ticks = 0;
static int timer0Reload = 0;
static int timer0ClockReload  = 0;
static uint16_t timer1Value = 0;
static bool timer1On = false;
static int timer1Ticks = 0;
static int timer1Reload = 0;
static int timer1ClockReload  = 0;
static uint16_t timer2Value = 0;
static bool timer2On = false;
static int timer2Ticks = 0;
static int timer2Reload = 0;
static int timer2ClockReload  = 0;
static uint16_t timer3Value = 0;
static bool timer3On = false;
static int timer3Ticks = 0;
static int timer3Reload = 0;
static int timer3ClockReload  = 0;

int cpuDmaCount = 0;
static uint32_t cpuDmaLast = 0;
static uint32_t cpuDmaPC = 0;
static bool cpuDmaRunning = false;

static const uint32_t  objTilesAddress [3] = {0x010000, 0x014000, 0x014000};

static INLINE uint32_t CPUReadMemory(uint32_t address)
{
	uint32_t value;
	switch(address >> 24)
	{
		case 0:
			/* BIOS */
			if(bus.reg[15].I >> 24)
			{
				if(address < 0x4000)
					value = READ32LE(((uint32_t *)&biosProtected));
				else goto unreadable;
			}
			else
				value = READ32LE(bios + (address & 0x3FFC));
			break;
		case 0x02:
			/* external work RAM */
			value = READ32LE(workRAM + (address & 0x3FFFC));
			break;
		case 0x03:
			/* internal work RAM */
			value = READ32LE(internalRAM + (address & 0x7ffC));
			break;
		case 0x04:
			/* I/O registers */
			if((address < 0x4000400) && ioReadable[address & 0x3fc])
			{
				if(ioReadable[(address & 0x3fc) + 2])
					value = READ32LE(ioMem + (address & 0x3fC));
				else
					value = READ16LE(ioMem + (address & 0x3fc));
			}
			else
				goto unreadable;
			break;
		case 0x05:
			/* palette RAM */
			value = READ32LE(paletteRAM + (address & 0x3fC));
			break;
		case 0x06: {
			/* VRAM */
			uint32_t addr = (address & 0x1fffc);
			if ((R_DISPCNT_Video_Mode > 2) && ((addr & 0x1C000) == 0x18000))
			{
				value = 0;
				break;
			}
			if ((addr & 0x18000) == 0x18000)
				addr &= 0x17ffc;
			value = READ32LE(vram + addr);
		} break;
		case 0x07:
			/* OAM RAM */
			value = READ32LE(oam + (address & 0x3FC));
			break;
		case 0x08:
		case 0x09:
		case 0x0A:
		case 0x0B:
		case 0x0C:
			/* gamepak ROM */
			value = READ32LE(rom + (address&0x1FFFFFC));
			break;
		case 0x0D:
         value = eepromRead();
         break;
		case 14:
      case 15:
		  	value = flashRead(address) * 0x01010101;
            break;
		default:
unreadable:
			if (cpuDmaRunning || ((bus.reg[15].I - cpuDmaPC) == (armState ? 4 : 2))) {
				value = cpuDmaLast;
			} else {
				if (armState)
					value = CPUReadMemoryQuick(bus.reg[15].I);
				else
					value = CPUReadHalfWordQuick(bus.reg[15].I) | CPUReadHalfWordQuick(bus.reg[15].I) << 16;
			}
	}

	if(address & 3) {
		int shift = (address & 3) << 3;
		value = (value >> shift) | (value << (32 - shift));
	}
	return value;
}

static INLINE uint32_t CPUReadHalfWord(uint32_t address)
{
	uint32_t value;

	switch(address >> 24)
	{
		case 0:
			if (bus.reg[15].I >> 24)
			{
				if(address < 0x4000)
					value = READ16LE(biosProtected + (address & 2));
				else
					goto unreadable;
			}
			else
				value = READ16LE(bios + (address & 0x3FFE));
			break;
		case 2:
			value = READ16LE(workRAM + (address & 0x3FFFE));
			break;
		case 3:
			value = READ16LE(internalRAM + (address & 0x7ffe));
			break;
		case 4:
			if((address < 0x4000400) && ioReadable[address & 0x3fe])
			{
				value =  READ16LE(ioMem + (address & 0x3fe));
				if (((address & 0x3fe)>0xFF) && ((address & 0x3fe)<0x10E))
				{
					if (((address & 0x3fe) == 0x100) && timer0On)
						value = 0xFFFF - ((timer0Ticks-cpuTotalTicks) >> timer0ClockReload);
					else
						if (((address & 0x3fe) == 0x104) && timer1On && !(io_registers[REG_TM1CNT] & 4))
							value = 0xFFFF - ((timer1Ticks-cpuTotalTicks) >> timer1ClockReload);
						else
							if (((address & 0x3fe) == 0x108) && timer2On && !(io_registers[REG_TM2CNT] & 4))
								value = 0xFFFF - ((timer2Ticks-cpuTotalTicks) >> timer2ClockReload);
							else
								if (((address & 0x3fe) == 0x10C) && timer3On && !(io_registers[REG_TM3CNT] & 4))
									value = 0xFFFF - ((timer3Ticks-cpuTotalTicks) >> timer3ClockReload);
				}
			}
			else goto unreadable;
			break;
		case 5:
			value = READ16LE(paletteRAM + (address & 0x3fe));
			break;
		case 6: {
			uint32_t addr = (address & 0x1fffe);
			if ((R_DISPCNT_Video_Mode > 2) && ((addr & 0x1C000) == 0x18000))
			{
				value = 0;
				break;
			}
			if ((addr & 0x18000) == 0x18000)
				addr &= 0x17fff;
			value = READ16LE(vram + addr);
		} break;
		case 7:
			value = READ16LE(oam + (address & 0x3fe));
			break;
		case 8:
		case 9:
		case 10:
		case 11:
		case 12:
			switch(address) {
			case 0x80000c4:
			case 0x80000c6:
			case 0x80000c8:
#if USE_MOTION_SENSOR
				if(hardware.sensor & HARDWARE_SENSOR_GYRO)
					return gyroRead(address);
				else
#endif
					return rtcRead(address);
				break;
			default:
				value = READ16LE(rom + (address & 0x1FFFFFE)); break;
			}
			break;
		case 13:
         value =  eepromRead();
         break;
		case 14:
		case 15:
         value = flashRead(address) * 0x0101;
         break;
		default:
unreadable:
			if (cpuDmaRunning || ((bus.reg[15].I - cpuDmaPC) == (armState ? 4 : 2))) {
				value = cpuDmaLast & 0xFFFF;
			} else {
				int param = bus.reg[15].I;
				if(armState)
					param += (address & 2);
				value = CPUReadHalfWordQuick(param);
			}
			break;
	}

	if(address & 1)
		value = (value >> 8) | (value << 24);

	return value;
}

static INLINE uint16_t CPUReadHalfWordSigned(uint32_t address)
{
	uint16_t value = CPUReadHalfWord(address);
	if((address & 1))
		value = (int8_t)value;
	return value;
}

static INLINE uint8_t CPUReadByte(uint32_t address)
{
	switch(address >> 24)
	{
		case 0:
			if (bus.reg[15].I >> 24)
			{
				if(address < 0x4000)
					return biosProtected[address & 3];
				else
					goto unreadable;
			}
			return bios[address & 0x3FFF];
		case 2:
			return workRAM[address & 0x3FFFF];
		case 3:
			return internalRAM[address & 0x7fff];
		case 4:
			if((address < 0x4000400) && ioReadable[address & 0x3ff])
				return ioMem[address & 0x3ff];
			else goto unreadable;
		case 5:
			return paletteRAM[address & 0x3ff];
		case 6:
			address = (address & 0x1ffff);
			if ((R_DISPCNT_Video_Mode >2) && ((address & 0x1C000) == 0x18000))
				return 0;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;
			return vram[address];
		case 7:
			return oam[address & 0x3ff];
		case 8:
		case 9:
		case 10:
		case 11:
		case 12:
			return rom[address & 0x1FFFFFF];
		case 13:
         	return eepromRead();
		case 14:
		case 15:
#ifdef USE_MOTION_SENSOR
		if(hardware.sensor)
        {
			switch(address & 0x00008f00)
            {
				case 0x8200:
					return hardware.tilt_x & 0xFF;
				case 0x8300:
					return ((hardware.tilt_x >> 8) & 0xF) | 0x80;
				case 0x8400:
					return hardware.tilt_y & 0xFF;
				case 0x8500:
					return ((hardware.tilt_y >> 8) & 0xF) | 0x80;
			}
		}
#endif
         	return flashRead(address);
		default:
unreadable:
			if (cpuDmaRunning || ((bus.reg[15].I - cpuDmaPC) == (armState ? 4 : 2))) {
				return cpuDmaLast & 0xFF;
			} else {
				if(armState)
					return CPUReadByteQuick(bus.reg[15].I+(address & 3));
				else
					return CPUReadByteQuick(bus.reg[15].I+(address & 1));
			}
	}
}

static INLINE void CPUWriteMemory(uint32_t address, uint32_t value)
{
	switch(address >> 24)
	{
		case 0x02:
			WRITE32LE(workRAM + (address & 0x3FFFC), value);
			break;
		case 0x03:
			WRITE32LE(internalRAM + (address & 0x7ffC), value);
			break;
		case 0x04:
			if(address < 0x4000400)
			{
				CPUUpdateRegister((address & 0x3FC), value & 0xFFFF);
				CPUUpdateRegister((address & 0x3FC) + 2, (value >> 16));
			}
			break;
		case 0x05:
			WRITE32LE(paletteRAM + (address & 0x3FC), value);
			break;
		case 0x06:
			address = (address & 0x1fffc);
			if ((R_DISPCNT_Video_Mode >2) && ((address & 0x1C000) == 0x18000))
				return;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;


			WRITE32LE(vram + address, value);
			break;
		case 0x07:
			WRITE32LE(oam + (address & 0x3fc), value);
			break;
		case 0x0D:
			if(cpuEEPROMEnabled) {
				eepromWrite(value);
				break;
			}
			break;
		case 0x0E:
		case 0x0F:
			if((!eepromInUse) | cpuSramEnabled | cpuFlashEnabled)
				(*cpuSaveGameFunc)(address, (uint8_t)value);
			break;
		default:
			break;
	}
}

static INLINE void CPUWriteHalfWord(uint32_t address, uint16_t value)
{
	switch(address >> 24)
	{
		case 2:
			WRITE16LE(workRAM + (address & 0x3FFFE),value);
			break;
		case 3:
			WRITE16LE(internalRAM + (address & 0x7ffe), value);
			break;
		case 4:
			if(address < 0x4000400)
				CPUUpdateRegister(address & 0x3fe, value);
			break;
		case 5:
			WRITE16LE(paletteRAM + (address & 0x3fe), value);
			break;
		case 6:
			address = (address & 0x1fffe);
			if ((R_DISPCNT_Video_Mode >2) && ((address & 0x1C000) == 0x18000))
				return;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;
			WRITE16LE(vram + address, value);
			break;
		case 7:
			WRITE16LE(oam + (address & 0x3fe), value);
			break;
		case 8:
		case 9:
			switch(address) {
			case 0x80000c4:
			case 0x80000c6:
			case 0x80000c8:
#if USE_MOTION_SENSOR
				if(hardware.sensor & HARDWARE_SENSOR_GYRO)
					gyroWrite(address, value);
				else
#endif
					rtcWrite(address, value);
				break;
			}
			break;
		case 13:
			if(cpuEEPROMEnabled)
				eepromWrite((uint8_t)value);
			break;
		case 14:
		case 15:
			if((!eepromInUse) | cpuSramEnabled | cpuFlashEnabled)
				(*cpuSaveGameFunc)(address, (uint8_t)value);
			break;
		default:
			break;
	}
}

static INLINE void CPUWriteByte(uint32_t address, uint8_t b)
{
	switch(address >> 24)
	{
		case 2:
			workRAM[address & 0x3FFFF] = b;
			break;
		case 3:
			internalRAM[address & 0x7fff] = b;
			break;
		case 4:
			if(address < 0x4000400)
			{
				switch(address & 0x3FF)
				{
					case 0x60:
					case 0x61:
					case 0x62:
					case 0x63:
					case 0x64:
					case 0x65:
					case 0x68:
					case 0x69:
					case 0x6c:
					case 0x6d:
					case 0x70:
					case 0x71:
					case 0x72:
					case 0x73:
					case 0x74:
					case 0x75:
					case 0x78:
					case 0x79:
					case 0x7c:
					case 0x7d:
					case 0x80:
					case 0x81:
					case 0x84:
					case 0x85:
					case 0x90:
					case 0x91:
					case 0x92:
					case 0x93:
					case 0x94:
					case 0x95:
					case 0x96:
					case 0x97:
					case 0x98:
					case 0x99:
					case 0x9a:
					case 0x9b:
					case 0x9c:
					case 0x9d:
					case 0x9e:
					case 0x9f:
						{
							int gb_addr = table[(address & 0xFF) - 0x60];
							soundEvent_u8(gb_addr, address&0xFF, b);
						}
						break;
					case 0x301: /* HALTCNT, undocumented */
						if(b == 0x80)
							stopState = true;
						holdState = 1;
						cpuNextEvent = cpuTotalTicks;
						break;
					default: /* every other register */
						{
							uint32_t lowerBits = address & 0x3fe;
							uint16_t param;
							/* Read the unaffected half as a direct byte to avoid an
							 * unnecessary READ16LE byteswap on BE: we discard one byte
							 * of the load anyway. */
							if(address & 1)
								param = ioMem[lowerBits] | (b << 8);
							else
								param = (ioMem[lowerBits+1] << 8) | b;

							CPUUpdateRegister(lowerBits, param);
						}
					break;
				}
			}
			break;
		case 5:
			/* no need to switch */
			*(uint16_t *)(paletteRAM + (address & 0x3FE)) = (b << 8) | b;
			break;
		case 6:
			address = (address & 0x1fffe);
			if ((R_DISPCNT_Video_Mode >2) && ((address & 0x1C000) == 0x18000))
				return;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;

			/* no need to switch */
			/* byte writes to OBJ VRAM are ignored */
			if ((address) < objTilesAddress[(R_DISPCNT_Video_Mode+1)>>2])
				*(uint16_t *)(vram + address) = (b << 8) | b;
			break;
		case 7:
			/* no need to switch */
			/* byte writes to OAM are ignored */
			/*    *((uint16_t *)&oam[address & 0x3FE]) = (b << 8) | b; */
			break;
		case 13:
			if(cpuEEPROMEnabled)
				eepromWrite(b);
			break;
		case 14:
		case 15:
			if ((saveType != 5) && ((!eepromInUse) | cpuSramEnabled | cpuFlashEnabled))
			{
				(*cpuSaveGameFunc)(address, b);
				break;
			}
		default:
			break;
	}
}


/*============================================================
	BIOS
============================================================ */
static INLINE int16_t fast_sin(uint8_t val)
{
	uint8_t p = 0x7F & val;
	int16_t q = 1 - ((0x80 & val) >> 6);
	return ((p << 9) + (-4 * p * p)) * q;
}

static INLINE int16_t fast_cos(uint8_t val)
{
	return fast_sin(val + 0x40);
}

/* 2020-08-12 negativeExponent */
/* ArcTan/ArcTan2 fixes based from mgba hle bios */

static void BIOS_ArcTan (void)
{
	int32_t i = bus.reg[0].I;
	int32_t a =  -((i * i) >> 14);
	int32_t b = ((0xA9 * a) >> 14) + 0x390;
	b = ((b * a) >> 14) + 0x91C;
	b = ((b * a) >> 14) + 0xFB6;
	b = ((b * a) >> 14) + 0x16AA;
	b = ((b * a) >> 14) + 0x2081;
	b = ((b * a) >> 14) + 0x3651;
	b = ((b * a) >> 14) + 0xA2F9;
   bus.reg[0].I = (i * b) >> 16;
   bus.reg[1].I = a;
   bus.reg[3].I = b;
}

static void BIOS_Div (void)
{
	int number = bus.reg[0].I;
	int denom  = bus.reg[1].I;

	if (denom != 0)
	{
      int32_t temp;
		bus.reg[0].I = number / denom;
		bus.reg[1].I = number % denom;
		temp         = (int32_t)bus.reg[0].I;
		bus.reg[3].I = temp < 0 ? (uint32_t)-temp : (uint32_t)temp;
	}
}

static void BIOS_ArcTan2 (void)
{
	int32_t x = bus.reg[0].I;
	int32_t y = bus.reg[1].I;
	uint32_t res = 0;
	if (y == 0)
		res = ((x>>16) & 0x8000);
	else
	{
		if (x == 0)
			res = ((y>>16) & 0x8000) + 0x4000;
		else
		{
			if ((abs(x) > abs(y)) || ((abs(x) == abs(y)) && (!((x<0) && (y<0)))))
			{
				bus.reg[1].I = x;
				bus.reg[0].I = y << 14;
				BIOS_Div();
				BIOS_ArcTan();
				if (x < 0)
					res = 0x8000 + bus.reg[0].I;
				else
					res = (((y>>16) & 0x8000)<<1) + bus.reg[0].I;
			}
			else
			{
				bus.reg[0].I = x << 14;
				BIOS_Div();
				BIOS_ArcTan();
				res = (0x4000 + ((y>>16) & 0x8000)) - bus.reg[0].I;
			}
		}
	}
	bus.reg[0].I = res;
	bus.reg[3].I = 0x170;
}

static void BIOS_BitUnPack(void)
{
	int bits;
	int revbits;
	uint32_t base;
	bool addBase;
	int dataSize;
	int data;
	int bitwritecount;
	uint32_t source = bus.reg[0].I;
	uint32_t dest   = bus.reg[1].I;
	uint32_t header = bus.reg[2].I;
	int len    = CPUReadHalfWord(header);
	/* check address */
   if(       ((source & 0xe000000)        == 0)
         || (((source + len) & 0xe000000) == 0)
     )
		return;

	bits = CPUReadByte(header+2);
	revbits = 8 - bits;
	/* uint32_t value = 0; */
	base = CPUReadMemory(header+4);
	addBase = (base & 0x80000000) ? true : false;
	base &= 0x7fffffff;
	dataSize = CPUReadByte(header+3);
	data = 0;
	bitwritecount = 0;
	while(1)
	{
		int mask;
		uint8_t b;
		int bitcount;
		len -= 1;
		if(len < 0)
			break;
		mask = 0xff >> revbits;
		b = CPUReadByte(source);
		source++;
		bitcount = 0;
		while(1) {
			uint32_t d;
			uint32_t temp;
			if(bitcount >= 8)
				break;
			d = b & mask;
			temp = d >> bitcount;
			if(d || addBase) {
				temp += base;
			}
			data |= temp << bitwritecount;
			bitwritecount += dataSize;
			if(bitwritecount >= 32) {
				CPUWriteMemory(dest, data);
				dest += 4;
				data = 0;
				bitwritecount = 0;
			}
			mask <<= bits;
			bitcount += bits;
		}
	}
}

static void BIOS_BgAffineSet (void)
{
   int i;
	uint32_t src  = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;
	int num  = bus.reg[2].I;

	for(i = 0; i < num; i++)
	{
		int32_t cy;
		int16_t dispx;
		int16_t dispy;
		int16_t rx;
		int16_t ry;
		uint16_t theta;
		int32_t a;
		int32_t b;
		int16_t dx;
		int16_t dmx;
		int16_t dy;
		int16_t dmy;
		int32_t startx;
		int32_t starty;
		int32_t cx = CPUReadMemory(src);
		src+=4;
		cy = CPUReadMemory(src);
		src+=4;
		dispx = CPUReadHalfWord(src);
		src+=2;
		dispy = CPUReadHalfWord(src);
		src+=2;
		rx = CPUReadHalfWord(src);
		src+=2;
		ry = CPUReadHalfWord(src);
		src+=2;
		theta = CPUReadHalfWord(src)>>8;
		src+=4; /* keep structure alignment */
		a = fast_cos(theta);
		b = fast_sin(theta);

		dx = (rx * a)>>14;
		dmx = (rx * b)>>14;
		dy = (ry * b)>>14;
		dmy = (ry * a)>>14;

		CPUWriteHalfWord(dest, dx);
		dest += 2;
		CPUWriteHalfWord(dest, -dmx);
		dest += 2;
		CPUWriteHalfWord(dest, dy);
		dest += 2;
		CPUWriteHalfWord(dest, dmy);

		dest += 2;

		startx = cx - dx * dispx + dmx * dispy;
		starty = cy - dy * dispx - dmy * dispy;

		CPUWriteMemory(dest, startx);
		dest += 4;
		CPUWriteMemory(dest, starty);
		dest += 4;
	}
}

static void BIOS_CpuSet (void)
{
	uint32_t source = bus.reg[0].I;
	uint32_t dest   = bus.reg[1].I;
	uint32_t cnt    = bus.reg[2].I;
	int count  = cnt & 0x1FFFFF;

	/* 32-bit ? */
	if((cnt >> 26) & 1)
	{
		/* needed for 32-bit mode! */
		source &= 0xFFFFFFFC;
		dest   &= 0xFFFFFFFC;
		/* fill ? */
		if((cnt >> 24) & 1) {
			uint32_t value = (source>0x0EFFFFFF ? 0x1CAD1CAD : CPUReadMemory(source));
			while(count > 0) {
				CPUWriteMemory(dest, value);
				dest += 4;
				count--;
			}
		} else {
#if USE_TWEAK_MEMFUNC
			if(source > 0x0EFFFFFF) {
				while(count > 0) {
					CPUWriteMemory(dest, 0x1CAD1CAD);
					dest += 4;
					count--;
				}
			} else {
				while(count > 0) {
					CPUWriteMemory(dest, CPUReadMemory(source));
					source += 4;
					dest += 4;
					count--;
				}
			}
#else
			/* copy */
			while(count > 0) {
				CPUWriteMemory(dest, (source>0x0EFFFFFF ? 0x1CAD1CAD : CPUReadMemory(source)));
				source += 4;
				dest += 4;
				count--;
			}
#endif
		}
	}
	else
	{
		/* 16-bit fill? */
		if((cnt >> 24) & 1) {
			uint16_t value = (source>0x0EFFFFFF ? 0x1CAD : CPUReadHalfWord(source));
			while(count > 0) {
				CPUWriteHalfWord(dest, value);
				dest += 2;
				count--;
			}
		} else {
#if USE_TWEAK_MEMFUNC
			if(source > 0x0EFFFFFF) {
				while(count > 0) {
					CPUWriteHalfWord(dest, 0x1CAD);
					dest += 2;
					count--;
				}
			} else {
				while(count > 0) {
					CPUWriteHalfWord(dest, CPUReadHalfWord(source));
					source += 2;
					dest += 2;
					count--;
				}
			}
#else
			/* copy */
			while(count > 0) {
				CPUWriteHalfWord(dest, (source>0x0EFFFFFF ? 0x1CAD : CPUReadHalfWord(source)));
				source += 2;
				dest += 2;
				count--;
			}
#endif
		}
	}
}

static void BIOS_CpuFastSet (void)
{
	int count;
	uint32_t source = bus.reg[0].I;
	uint32_t dest   = bus.reg[1].I;
	uint32_t cnt    = bus.reg[2].I;

	/* needed for 32-bit mode! */
	source    &= 0xFFFFFFFC;
	dest      &= 0xFFFFFFFC;

	count = cnt & 0x1FFFFF;

	/* fill? */
	if((cnt >> 24) & 1) {
		while(count > 0) {
			/* BIOS always transfers 32 bytes at a time */
			uint32_t value = (source>0x0EFFFFFF ? 0xBAFFFFFB : CPUReadMemory(source));
			{
				int i;
				for(i = 0; i < 8; i++) {
				CPUWriteMemory(dest, value);
				dest += 4;
			}
			}
			count -= 8;
		}
	} else {
#if USE_TWEAK_MEMFUNC
		if(source > 0x0EFFFFFF) {
			while(count > 0) {
				int i;
				for(i = 0; i < 8; i++) {
					CPUWriteMemory(dest, 0xBAFFFFFB);
					dest += 4;
				}
				count -= 8;
			}
		} else {
			while(count > 0) {
				int i;
				for(i = 0; i < 8; i++) {
					CPUWriteMemory(dest, CPUReadMemory(source));
					source += 4;
					dest += 4;
				}
				count -= 8;
			}
		}
#else
		/* copy */
		while(count > 0) {
			/* BIOS always transfers 32 bytes at a time */
			{
				int i;
				for(i = 0; i < 8; i++) {
				CPUWriteMemory(dest, (source>0x0EFFFFFF ? 0xBAFFFFFB :CPUReadMemory(source)));
				source += 4;
				dest += 4;
			}
			}
			count -= 8;
		}
#endif
	}
}

static void BIOS_Diff8bitUnFilterWram (void)
{
	int len;
	uint8_t data;
	uint32_t source = bus.reg[0].I;
	uint32_t dest   = bus.reg[1].I;
	uint32_t header = CPUReadMemory(source);
	source    += 4;

	if(((source & 0xe000000) == 0) ||
	(((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0))
		return;

	len = header >> 8;

	data = CPUReadByte(source++);
	CPUWriteByte(dest++, data);
	len--;

	while(len > 0) {
		uint8_t diff = CPUReadByte(source++);
		data += diff;
		CPUWriteByte(dest++, data);
		len--;
	}
}

static void BIOS_Diff8bitUnFilterVram (void)
{
	int len;
	uint8_t data;
	uint16_t writeData;
	int shift;
	int bytes;
	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	len = header >> 8;

	data = CPUReadByte(source++);
	writeData = data;
	shift = 8;
	bytes = 1;

	while(len >= 2) {
		uint8_t diff = CPUReadByte(source++);
		data += diff;
		writeData |= (data << shift);
		bytes++;
		shift += 8;
		if(bytes == 2) {
			CPUWriteHalfWord(dest, writeData);
			dest += 2;
			len -= 2;
			bytes = 0;
			writeData = 0;
			shift = 0;
		}
	}
}

static void BIOS_Diff16bitUnFilter (void)
{
	int len;
	uint16_t data;
	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	len = header >> 8;

	data = CPUReadHalfWord(source);
	source += 2;
	CPUWriteHalfWord(dest, data);
	dest += 2;
	len -= 2;

	while(len >= 2) {
		uint16_t diff = CPUReadHalfWord(source);
		source += 2;
		data += diff;
		CPUWriteHalfWord(dest, data);
		dest += 2;
		len -= 2;
	}
}

static void BIOS_HuffUnComp (void)
{
	uint8_t treeSize;
	uint32_t treeStart;
	int len;
	uint32_t mask;
	uint32_t data;
	int pos;
	uint8_t rootNode;
	uint8_t currentNode;
	bool writeData;
	int byteShift;
	int byteCount;
	uint32_t writeValue;
	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
	((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	treeSize = CPUReadByte(source++);

	treeStart = source;

	source += ((treeSize+1)<<1)-1; /* minus because we already skipped one byte */

	len = header >> 8;

	mask = 0x80000000;
	data = CPUReadMemory(source);
	source += 4;

	pos = 0;
	rootNode = CPUReadByte(treeStart);
	currentNode = rootNode;
	writeData = false;
	byteShift = 0;
	byteCount = 0;
	writeValue = 0;

	if((header & 0x0F) == 8) {
		while(len > 0) {
			/* take left */
			if(pos == 0)
				pos++;
			else
				pos += (((currentNode & 0x3F)+1)<<1);

			if(data & mask) {
				/* right */
				if(currentNode & 0x40)
					writeData = true;
				currentNode = CPUReadByte(treeStart+pos+1);
			} else {
				/* left */
				if(currentNode & 0x80)
					writeData = true;
				currentNode = CPUReadByte(treeStart+pos);
			}

			if(writeData) {
				writeValue |= (currentNode << byteShift);
				byteCount++;
				byteShift += 8;

				pos = 0;
				currentNode = rootNode;
				writeData = false;

				if(byteCount == 4) {
					byteCount = 0;
					byteShift = 0;
					CPUWriteMemory(dest, writeValue);
					writeValue = 0;
					dest += 4;
					len -= 4;
				}
			}
			mask >>= 1;
			if(mask == 0) {
				mask = 0x80000000;
				data = CPUReadMemory(source);
				source += 4;
			}
		}
	} else {
		int halfLen = 0;
		int value = 0;
		while(len > 0) {
			/* take left */
			if(pos == 0)
				pos++;
			else
				pos += (((currentNode & 0x3F)+1)<<1);

			if((data & mask)) {
				/* right */
				if(currentNode & 0x40)
					writeData = true;
				currentNode = CPUReadByte(treeStart+pos+1);
			} else {
				/* left */
				if(currentNode & 0x80)
					writeData = true;
				currentNode = CPUReadByte(treeStart+pos);
			}

			if(writeData) {
				if(halfLen == 0)
					value |= currentNode;
				else
					value |= (currentNode<<4);

				halfLen += 4;
				if(halfLen == 8) {
					writeValue |= (value << byteShift);
					byteCount++;
					byteShift += 8;

					halfLen = 0;
					value = 0;

					if(byteCount == 4) {
						byteCount = 0;
						byteShift = 0;
						CPUWriteMemory(dest, writeValue);
						dest += 4;
						writeValue = 0;
						len -= 4;
					}
				}
				pos = 0;
				currentNode = rootNode;
				writeData = false;
			}
			mask >>= 1;
			if(mask == 0) {
				mask = 0x80000000;
				data = CPUReadMemory(source);
				source += 4;
			}
		}
	}
}

static void BIOS_LZ77UnCompVram (void)
{
int byteCount;
int byteShift;
uint32_t writeValue;
int len;

	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	byteCount = 0;
	byteShift = 0;
	writeValue = 0;

	len = header >> 8;

	while(len > 0) {
		uint8_t d = CPUReadByte(source++);

		if(d) {
			{
				int i;
				for(i = 0; i < 8; i++) {
				if(d & 0x80) {
					int length;
					int offset;
					uint32_t windowOffset;
					uint16_t data = CPUReadByte(source++) << 8;
					data |= CPUReadByte(source++);
					length = (data >> 12) + 3;
					offset = (data & 0x0FFF);
					windowOffset = dest + byteCount - offset - 1;
					{
						int i2;
						for(i2 = 0; i2 < length; i2++) {
						writeValue |= (CPUReadByte(windowOffset++) << byteShift);
						byteShift += 8;
						byteCount++;

						if(byteCount == 2) {
							CPUWriteHalfWord(dest, writeValue);
							dest += 2;
							byteCount = 0;
							byteShift = 0;
							writeValue = 0;
						}
						len--;
						if(len == 0)
							return;
					}
					}
				} else {
					writeValue |= (CPUReadByte(source++) << byteShift);
					byteShift += 8;
					byteCount++;
					if(byteCount == 2) {
						CPUWriteHalfWord(dest, writeValue);
						dest += 2;
						byteCount = 0;
						byteShift = 0;
						writeValue = 0;
					}
					len--;
					if(len == 0)
						return;
				}
				d <<= 1;
			}
			}
		} else {
			{
				int i;
				for(i = 0; i < 8; i++) {
				writeValue |= (CPUReadByte(source++) << byteShift);
				byteShift += 8;
				byteCount++;
				if(byteCount == 2) {
					CPUWriteHalfWord(dest, writeValue);
					dest += 2;
					byteShift = 0;
					byteCount = 0;
					writeValue = 0;
				}
				len--;
				if(len == 0)
					return;
			}
			}
		}
	}
}

static void BIOS_LZ77UnCompWram (void)
{
	int len;
	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	len = header >> 8;

	while(len > 0) {
		uint8_t d = CPUReadByte(source++);

		if(d) {
			{
				int i;
				for(i = 0; i < 8; i++) {
				if(d & 0x80) {
					int length;
					int offset;
					uint32_t windowOffset;
					uint16_t data = CPUReadByte(source++) << 8;
					data |= CPUReadByte(source++);
					length = (data >> 12) + 3;
					offset = (data & 0x0FFF);
					windowOffset = dest - offset - 1;
					{
						int i2;
						for(i2 = 0; i2 < length; i2++) {
						CPUWriteByte(dest++, CPUReadByte(windowOffset++));
						len--;
						if(len == 0)
							return;
					}
					}
				} else {
					CPUWriteByte(dest++, CPUReadByte(source++));
					len--;
					if(len == 0)
						return;
				}
				d <<= 1;
			}
			}
		} else {
			{
				int i;
				for(i = 0; i < 8; i++) {
				CPUWriteByte(dest++, CPUReadByte(source++));
				len--;
				if(len == 0)
					return;
			}
			}
		}
	}
}

static void BIOS_ObjAffineSet (void)
{
	uint32_t src = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;
	int num = bus.reg[2].I;
	int offset = bus.reg[3].I;

	{
		int i;
		for(i = 0; i < num; i++) {
		int16_t ry;
		uint16_t theta;
		int32_t a;
		int32_t b;
		int16_t dx;
		int16_t dmx;
		int16_t dy;
		int16_t dmy;
		int16_t rx = CPUReadHalfWord(src);
		src+=2;
		ry = CPUReadHalfWord(src);
		src+=2;
		theta = CPUReadHalfWord(src)>>8;
		src+=4; /* keep structure alignment */

		a = fast_cos(theta);
		b = fast_sin(theta);

		dx = ((int32_t)rx * a)>>14;
		dmx = ((int32_t)rx * b)>>14;
		dy = ((int32_t)ry * b)>>14;
		dmy = ((int32_t)ry * a)>>14;

		CPUWriteHalfWord(dest, dx);
		dest += offset;
		CPUWriteHalfWord(dest, -dmx);
		dest += offset;
		CPUWriteHalfWord(dest, dy);
		dest += offset;
		CPUWriteHalfWord(dest, dmy);
		dest += offset;
	}
	}
}

static void BIOS_RegisterRamReset(uint32_t flags)
{
	/* no need to trace here. this is only called directly from GBA.cpp */
	/* to emulate bios initialization */

	CPUUpdateRegister(0x0, 0x80);

	if(flags)
	{
		if(flags & 0x01)
			memset(workRAM, 0, 0x40000);		/* clear work RAM */

		if(flags & 0x02)
			memset(internalRAM, 0, 0x7e00);		/* don't clear 0x7e00-0x7fff, clear internal RAM */

		if(flags & 0x04)
			memset(paletteRAM, 0, 0x400);	/* clear palette RAM */

		if(flags & 0x08)
			memset(vram, 0, 0x18000);		/* clear VRAM */

		if(flags & 0x10)
			memset(oam, 0, 0x400);			/* clean OAM */

		if(flags & 0x80) {
			int i;
			for(i = 0; i < 0x10; i++)
				CPUUpdateRegister(0x200+i*2, 0);

			for(i = 0; i < 0xF; i++)
				CPUUpdateRegister(0x4+i*2, 0);

			for(i = 0; i < 0x20; i++)
				CPUUpdateRegister(0x20+i*2, 0);

			for(i = 0; i < 0x18; i++)
				CPUUpdateRegister(0xb0+i*2, 0);

			CPUUpdateRegister(0x130, 0);
			CPUUpdateRegister(0x20, 0x100);
			CPUUpdateRegister(0x30, 0x100);
			CPUUpdateRegister(0x26, 0x100);
			CPUUpdateRegister(0x36, 0x100);
		}

		if(flags & 0x20) {
			int i;
			for(i = 0; i < 8; i++)
				CPUUpdateRegister(0x110+i*2, 0);
			CPUUpdateRegister(0x134, 0x8000);
			for(i = 0; i < 7; i++)
				CPUUpdateRegister(0x140+i*2, 0);
		}

		if(flags & 0x40) {
			int i;
			CPUWriteByte(0x4000084, 0);
			CPUWriteByte(0x4000084, 0x80);
			CPUWriteMemory(0x4000080, 0x880e0000);
			CPUUpdateRegister(0x88, CPUReadHalfWord(0x4000088)&0x3ff);
			CPUWriteByte(0x4000070, 0x70);
			for(i = 0; i < 8; i++)
				CPUUpdateRegister(0x90+i*2, 0);
			CPUWriteByte(0x4000070, 0);
			for(i = 0; i < 8; i++)
				CPUUpdateRegister(0x90+i*2, 0);
			CPUWriteByte(0x4000084, 0);
		}
	}
}

static void BIOS_RLUnCompVram (void)
{
	int len;
	int byteCount;
	int byteShift;
	uint32_t writeValue;
	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source & 0xFFFFFFFC);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	len = header >> 8;
	byteCount = 0;
	byteShift = 0;
	writeValue = 0;

	while(len > 0)
	{
		uint8_t d = CPUReadByte(source++);
		int l = d & 0x7F;
		if(d & 0x80) {
			uint8_t data = CPUReadByte(source++);
			l += 3;
			{
				int i;
				for(i = 0;i < l; i++) {
				writeValue |= (data << byteShift);
				byteShift += 8;
				byteCount++;

				if(byteCount == 2) {
					CPUWriteHalfWord(dest, writeValue);
					dest += 2;
					byteCount = 0;
					byteShift = 0;
					writeValue = 0;
				}
				len--;
				if(len == 0)
					return;
			}
			}
		} else {
			l++;
			{
				int i;
				for(i = 0; i < l; i++) {
				writeValue |= (CPUReadByte(source++) << byteShift);
				byteShift += 8;
				byteCount++;
				if(byteCount == 2) {
					CPUWriteHalfWord(dest, writeValue);
					dest += 2;
					byteCount = 0;
					byteShift = 0;
					writeValue = 0;
				}
				len--;
				if(len == 0)
					return;
			}
			}
		}
	}
}

static void BIOS_RLUnCompWram (void)
{
	int len;
	uint32_t source = bus.reg[0].I;
	uint32_t dest = bus.reg[1].I;

	uint32_t header = CPUReadMemory(source & 0xFFFFFFFC);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	len = header >> 8;

	while(len > 0) {
		uint8_t d = CPUReadByte(source++);
		int l = d & 0x7F;
		if(d & 0x80) {
			uint8_t data = CPUReadByte(source++);
			l += 3;
			{
				int i;
				for(i = 0;i < l; i++) {
				CPUWriteByte(dest++, data);
				len--;
				if(len == 0)
					return;
			}
			}
		} else {
			l++;
			{
				int i;
				for(i = 0; i < l; i++) {
				CPUWriteByte(dest++,  CPUReadByte(source++));
				len--;
				if(len == 0)
					return;
			}
			}
		}
	}
}

static void BIOS_SoftReset (void)
{
	uint8_t b;
	armState = true;
	armMode = 0x1F;
	armIrqEnable = false;
	C_FLAG = V_FLAG = N_FLAG = Z_FLAG = false;
	bus.reg[13].I = 0x03007F00;
	bus.reg[14].I = 0x00000000;
	bus.reg[16].I = 0x00000000;
	bus.reg[R13_IRQ].I = 0x03007FA0;
	bus.reg[R14_IRQ].I = 0x00000000;
	bus.reg[SPSR_IRQ].I = 0x00000000;
	bus.reg[R13_SVC].I = 0x03007FE0;
	bus.reg[R14_SVC].I = 0x00000000;
	bus.reg[SPSR_SVC].I = 0x00000000;
	b = internalRAM[0x7ffa];

	memset(&internalRAM[0x7e00], 0, 0x200);

	if(b) {
		bus.armNextPC = 0x02000000;
		bus.reg[15].I = 0x02000004;
	} else {
		bus.armNextPC = 0x08000000;
		bus.reg[15].I = 0x08000004;
	}
}

#define BIOS_GET_BIOS_CHECKSUM()	bus.reg[0].I=0xBAAE187F;

#define BIOS_REGISTER_RAM_RESET() BIOS_RegisterRamReset(bus.reg[0].I);

/* GBA BIOS Sqrt (SWI 0x08) returns the integer (floor) square root of a u32
 * argument.  The previous (uint32_t)sqrt((float)x) form was both inaccurate
 * and non-deterministic: casting a u32 to float (24-bit mantissa) lost
 * precision above 2^24, so e.g. 0xFFFFFFFF produced 65536 instead of the
 * correct 65535, and the final truncation was FPU-mode dependent.  Since the
 * result lands in emulated register r0 -- part of savestate / netplay state --
 * that made identical input diverge across builds and platforms.  The
 * digit-by-digit integer routine below is bit-exact, matches hardware, and is
 * deterministic on every target. */
static INLINE uint32_t bios_isqrt32(uint32_t x)
{
   uint32_t res = 0;
   uint32_t bit = 1UL << 30;
   while (bit > x)
      bit >>= 2;
   while (bit)
   {
      if (x >= res + bit)
      {
         x   -= res + bit;
         res  = (res >> 1) + bit;
      }
      else
         res >>= 1;
      bit >>= 2;
   }
   return res;
}

#define BIOS_SQRT() bus.reg[0].I = bios_isqrt32(bus.reg[0].I);

/* GBA BIOS MidiKey2Freq (SWI 0x1F): result = freq / 2^((180 - key - fineadj/256)/12)
 * where freq is the u32 at WaveData+4, key is the MIDI note (r1) and fineadj is
 * the 1/256-semitone fine adjust (r2).  The previous HLE evaluated this with
 * pow()/float, which is non-deterministic across platforms: pow() is among the
 * least reproducible libm routines (glibc/musl/newlib/MSVC disagree at the ULP
 * level), and the result lands in emulated register r0 -- part of game logic and
 * savestate/netplay state -- so the same ROM could diverge between an ARM and an
 * x86 peer.  (mGBA and VBA-M both still use float here; there is no bit-exact
 * hardware reference in common use.)
 *
 * This integer form is deterministic on every target.  Writing the exponent as
 *   P = (180 - key)*256 - fineadj      (so the divisor exponent is P/3072)
 * and splitting P = 3072*oct + rem, rem = a*256 + b (a:0..11 semitones,
 * b:0..255 micro-steps), the divisor is 2^oct * 2^(a/12) * 2^(b/3072); the two
 * fractional factors come from the Q24 tables below.  Validated over the entire
 * meaningful domain (key 0..178, fineadj 0..255, representative freqs): max
 * deviation from the exact real-valued result is 1 LSB -- identical to the float
 * path's ceiling -- and it is strictly closer to exact than the old float output
 * in the large majority of cases.  The change versus the previous output is at
 * most 2 LSB (well under one cent of pitch, inaudible), in the more-accurate
 * direction.  Over key 0..178 P is always positive, so this is a pure
 * truncating right shift (matching the old (int) cast) with no overflow. */
/* Q24 fixed-point 2^(-a/12), a = 0..11 (semitone-down ratios) */
static const uint32_t midikey_semi_neg[12] =
{
   0x01000000UL, 0x00F1A1BFUL, 0x00E411F0UL, 0x00D744FDUL,
   0x00CB2FF5UL, 0x00BFC887UL, 0x00B504F3UL, 0x00AADC08UL,
   0x00A14518UL, 0x009837F0UL, 0x008FACD6UL, 0x00879C7DUL
};

/* Q24 fixed-point 2^(-b/3072), b = 0..255 (intra-semitone micro-steps) */
static const uint32_t midikey_micro_neg[256] =
{
   0x01000000UL, 0x00FFF137UL, 0x00FFE26FUL, 0x00FFD3A7UL,
   0x00FFC4E1UL, 0x00FFB61BUL, 0x00FFA756UL, 0x00FF9892UL,
   0x00FF89CFUL, 0x00FF7B0DUL, 0x00FF6C4CUL, 0x00FF5D8BUL,
   0x00FF4ECBUL, 0x00FF400DUL, 0x00FF314FUL, 0x00FF2291UL,
   0x00FF13D5UL, 0x00FF051AUL, 0x00FEF65FUL, 0x00FEE7A5UL,
   0x00FED8ECUL, 0x00FECA34UL, 0x00FEBB7DUL, 0x00FEACC7UL,
   0x00FE9E11UL, 0x00FE8F5DUL, 0x00FE80A9UL, 0x00FE71F6UL,
   0x00FE6344UL, 0x00FE5493UL, 0x00FE45E2UL, 0x00FE3733UL,
   0x00FE2884UL, 0x00FE19D6UL, 0x00FE0B29UL, 0x00FDFC7DUL,
   0x00FDEDD2UL, 0x00FDDF27UL, 0x00FDD07EUL, 0x00FDC1D5UL,
   0x00FDB32DUL, 0x00FDA486UL, 0x00FD95E0UL, 0x00FD873AUL,
   0x00FD7896UL, 0x00FD69F2UL, 0x00FD5B4FUL, 0x00FD4CADUL,
   0x00FD3E0CUL, 0x00FD2F6CUL, 0x00FD20CCUL, 0x00FD122EUL,
   0x00FD0390UL, 0x00FCF4F3UL, 0x00FCE657UL, 0x00FCD7BCUL,
   0x00FCC921UL, 0x00FCBA88UL, 0x00FCABEFUL, 0x00FC9D57UL,
   0x00FC8EC0UL, 0x00FC802AUL, 0x00FC7195UL, 0x00FC6300UL,
   0x00FC546CUL, 0x00FC45DAUL, 0x00FC3748UL, 0x00FC28B6UL,
   0x00FC1A26UL, 0x00FC0B97UL, 0x00FBFD08UL, 0x00FBEE7AUL,
   0x00FBDFEDUL, 0x00FBD161UL, 0x00FBC2D6UL, 0x00FBB44CUL,
   0x00FBA5C2UL, 0x00FB9739UL, 0x00FB88B2UL, 0x00FB7A2AUL,
   0x00FB6BA4UL, 0x00FB5D1FUL, 0x00FB4E9AUL, 0x00FB4017UL,
   0x00FB3194UL, 0x00FB2312UL, 0x00FB1491UL, 0x00FB0610UL,
   0x00FAF791UL, 0x00FAE912UL, 0x00FADA94UL, 0x00FACC17UL,
   0x00FABD9BUL, 0x00FAAF20UL, 0x00FAA0A5UL, 0x00FA922CUL,
   0x00FA83B3UL, 0x00FA753BUL, 0x00FA66C4UL, 0x00FA584DUL,
   0x00FA49D8UL, 0x00FA3B63UL, 0x00FA2CF0UL, 0x00FA1E7DUL,
   0x00FA100AUL, 0x00FA0199UL, 0x00F9F329UL, 0x00F9E4B9UL,
   0x00F9D64AUL, 0x00F9C7DCUL, 0x00F9B96FUL, 0x00F9AB03UL,
   0x00F99C97UL, 0x00F98E2DUL, 0x00F97FC3UL, 0x00F9715AUL,
   0x00F962F2UL, 0x00F9548BUL, 0x00F94624UL, 0x00F937BFUL,
   0x00F9295AUL, 0x00F91AF6UL, 0x00F90C93UL, 0x00F8FE30UL,
   0x00F8EFCFUL, 0x00F8E16EUL, 0x00F8D30EUL, 0x00F8C4AFUL,
   0x00F8B651UL, 0x00F8A7F4UL, 0x00F89997UL, 0x00F88B3CUL,
   0x00F87CE1UL, 0x00F86E87UL, 0x00F8602EUL, 0x00F851D5UL,
   0x00F8437EUL, 0x00F83527UL, 0x00F826D1UL, 0x00F8187CUL,
   0x00F80A28UL, 0x00F7FBD5UL, 0x00F7ED82UL, 0x00F7DF30UL,
   0x00F7D0DFUL, 0x00F7C28FUL, 0x00F7B440UL, 0x00F7A5F2UL,
   0x00F797A4UL, 0x00F78957UL, 0x00F77B0BUL, 0x00F76CC0UL,
   0x00F75E76UL, 0x00F7502DUL, 0x00F741E4UL, 0x00F7339CUL,
   0x00F72555UL, 0x00F7170FUL, 0x00F708CAUL, 0x00F6FA85UL,
   0x00F6EC41UL, 0x00F6DDFEUL, 0x00F6CFBCUL, 0x00F6C17BUL,
   0x00F6B33BUL, 0x00F6A4FBUL, 0x00F696BCUL, 0x00F6887FUL,
   0x00F67A41UL, 0x00F66C05UL, 0x00F65DCAUL, 0x00F64F8FUL,
   0x00F64155UL, 0x00F6331CUL, 0x00F624E4UL, 0x00F616ADUL,
   0x00F60876UL, 0x00F5FA40UL, 0x00F5EC0CUL, 0x00F5DDD7UL,
   0x00F5CFA4UL, 0x00F5C172UL, 0x00F5B340UL, 0x00F5A50FUL,
   0x00F596DFUL, 0x00F588B0UL, 0x00F57A82UL, 0x00F56C54UL,
   0x00F55E28UL, 0x00F54FFCUL, 0x00F541D1UL, 0x00F533A7UL,
   0x00F5257DUL, 0x00F51754UL, 0x00F5092DUL, 0x00F4FB06UL,
   0x00F4ECE0UL, 0x00F4DEBAUL, 0x00F4D096UL, 0x00F4C272UL,
   0x00F4B44FUL, 0x00F4A62DUL, 0x00F4980CUL, 0x00F489EBUL,
   0x00F47BCCUL, 0x00F46DADUL, 0x00F45F8FUL, 0x00F45172UL,
   0x00F44355UL, 0x00F4353AUL, 0x00F4271FUL, 0x00F41905UL,
   0x00F40AECUL, 0x00F3FCD4UL, 0x00F3EEBCUL, 0x00F3E0A6UL,
   0x00F3D290UL, 0x00F3C47BUL, 0x00F3B667UL, 0x00F3A853UL,
   0x00F39A41UL, 0x00F38C2FUL, 0x00F37E1EUL, 0x00F3700EUL,
   0x00F361FEUL, 0x00F353F0UL, 0x00F345E2UL, 0x00F337D5UL,
   0x00F329C9UL, 0x00F31BBEUL, 0x00F30DB3UL, 0x00F2FFAAUL,
   0x00F2F1A1UL, 0x00F2E399UL, 0x00F2D592UL, 0x00F2C78BUL,
   0x00F2B986UL, 0x00F2AB81UL, 0x00F29D7DUL, 0x00F28F7AUL,
   0x00F28177UL, 0x00F27376UL, 0x00F26575UL, 0x00F25775UL,
   0x00F24976UL, 0x00F23B78UL, 0x00F22D7AUL, 0x00F21F7DUL,
   0x00F21181UL, 0x00F20386UL, 0x00F1F58CUL, 0x00F1E793UL,
   0x00F1D99AUL, 0x00F1CBA2UL, 0x00F1BDABUL, 0x00F1AFB5UL
};

static INLINE uint32_t bios_midikey2freq(uint32_t freq, uint32_t key, uint32_t fineadj)
{
   int32_t  P   = (180 - (int32_t)key) * 256 - (int32_t)fineadj;
   int32_t  oct = (P >= 0) ? (P / 3072) : -(((-P) + 3071) / 3072); /* floor div */
   int32_t  rem = P - oct * 3072;                                  /* [0, 3072) */
   uint32_t a   = (uint32_t)rem >> 8;                              /* 0..11     */
   uint32_t b   = (uint32_t)rem & 255;                            /* 0..255    */
   uint32_t fracQ24;
   uint64_t val;
   int32_t  sh;

   /* 2^(-rem/3072) in Q24, (2^23, 2^24]; round the Q48 product back to Q24 */
   fracQ24 = (uint32_t)((((uint64_t)midikey_semi_neg[a] * midikey_micro_neg[b])
                         + 0x800000UL) >> 24);
   val     = (uint64_t)freq * fracQ24;                            /* Q24 */
   sh      = 24 + oct;                                            /* result = val >> sh */

   if (sh >= 0)
   {
      uint64_t result = val >> sh; /* truncate toward zero, matching old (int) cast */
      return (result > 0xFFFFFFFFULL) ? 0xFFFFFFFFUL : (uint32_t)result;
   }
   /* Out-of-range keys (key > ~180) only: avoid UB and saturate. */
   if (-sh >= 32)
      return 0xFFFFFFFFUL;
   {
      uint64_t result = val << (-sh);
      return (result > 0xFFFFFFFFULL) ? 0xFFFFFFFFUL : (uint32_t)result;
   }
}

#define BIOS_MIDI_KEY_2_FREQ() \
	bus.reg[0].I = bios_midikey2freq((uint32_t)CPUReadMemory(bus.reg[0].I + 4), \
	                                 bus.reg[1].I, bus.reg[2].I);

/*
#define BIOS_SND_DRIVER_JMP_TABLE_COPY() \
	for(int i = 0; i < 36; i++) \
	{ \
		CPUWriteMemory(bus.reg[0].I, 0x9c); \
		bus.reg[0].I += 4; \
	}
*/

#define BIOS_SND_DRIVER_JMP_TABLE_COPY() \
	CPUWriteMemory(bus.reg[0].I, 0x9c); \
	bus.reg[0].I += 4;

#define CPU_UPDATE_CPSR() \
{ \
	uint32_t CPSR; \
	CPSR = bus.reg[16].I & 0x40; \
	if(N_FLAG) \
		CPSR |= 0x80000000; \
	if(Z_FLAG) \
		CPSR |= 0x40000000; \
	if(C_FLAG) \
		CPSR |= 0x20000000; \
	if(V_FLAG) \
		CPSR |= 0x10000000; \
	if(!armState) \
		CPSR |= 0x00000020; \
	if(!armIrqEnable) \
		CPSR |= 0x80; \
	CPSR |= (armMode & 0x1F); \
	bus.reg[16].I = CPSR; \
}

#define CPU_SOFTWARE_INTERRUPT() \
{ \
  uint32_t PC = bus.reg[15].I; \
  bool savedArmState = armState; \
  if(armMode != 0x13) \
    CPUSwitchMode(0x13, true, false); \
  bus.reg[14].I = PC - (savedArmState ? 4 : 2); \
  bus.reg[15].I = 0x08; \
  armState = true; \
  armIrqEnable = false; \
  bus.armNextPC = 0x08; \
  ARM_PREFETCH; \
  bus.reg[15].I += 4; \
}

static void CPUUpdateFlags(bool breakLoop)
{
	uint32_t CPSR = bus.reg[16].I;

	N_FLAG = (CPSR & 0x80000000) ? true: false;
	Z_FLAG = (CPSR & 0x40000000) ? true: false;
	C_FLAG = (CPSR & 0x20000000) ? true: false;
	V_FLAG = (CPSR & 0x10000000) ? true: false;
	armState = (CPSR & 0x20) ? false : true;
	armIrqEnable = (CPSR & 0x80) ? false : true;
	if (breakLoop && armIrqEnable && (io_registers[REG_IF] & io_registers[REG_IE]) && (io_registers[REG_IME] & 1))
		cpuNextEvent = cpuTotalTicks;
}

static void CPUSoftwareInterrupt(int comment)
{
	if(armState)
		comment >>= 16;

#ifdef HAVE_HLE_BIOS
	if(useBios)
	{
		CPU_SOFTWARE_INTERRUPT();
		return;
	}
#endif

	switch(comment) {
		case 0x00:
			BIOS_SoftReset();
			ARM_PREFETCH;
			break;
		case 0x01:
			BIOS_REGISTER_RAM_RESET();
			break;
		case 0x02:
			holdState = true;
			cpuNextEvent = cpuTotalTicks;
			break;
		case 0x03:
			holdState = true;
			stopState = true;
			cpuNextEvent = cpuTotalTicks;
			break;
		case 0x04:
		case 0x05:
		case 0x06:
		case 0x07:
			CPU_SOFTWARE_INTERRUPT();
			break;
		case 0x08:
			BIOS_SQRT();
			break;
		case 0x09:
			BIOS_ArcTan();
			break;
		case 0x0A:
			BIOS_ArcTan2();
			break;
		case 0x0B:
			{
			}
			if(!(((bus.reg[0].I & 0xe000000) == 0) || ((bus.reg[0].I + (((bus.reg[2].I << 11)>>9) & 0x1fffff)) & 0xe000000) == 0))
				BIOS_CpuSet();
			break;
		case 0x0C:
			{
			}
			if(!(((bus.reg[0].I & 0xe000000) == 0) || ((bus.reg[0].I + (((bus.reg[2].I << 11)>>9) & 0x1fffff)) & 0xe000000) == 0))
				BIOS_CpuFastSet();
			break;
		case 0x0D:
			BIOS_GET_BIOS_CHECKSUM();
			break;
		case 0x0E:
			BIOS_BgAffineSet();
			break;
		case 0x0F:
			BIOS_ObjAffineSet();
			break;
		case 0x10:
			{
			}
			BIOS_BitUnPack();
			break;
		case 0x11:
			BIOS_LZ77UnCompWram();
			break;
		case 0x12:
			BIOS_LZ77UnCompVram();
			break;
		case 0x13:
			BIOS_HuffUnComp();
			break;
		case 0x14:
			BIOS_RLUnCompWram();
			break;
		case 0x15:
			BIOS_RLUnCompVram();
			break;
		case 0x16:
			BIOS_Diff8bitUnFilterWram();
			break;
		case 0x17:
			BIOS_Diff8bitUnFilterVram();
			break;
		case 0x18:
			BIOS_Diff16bitUnFilter();
			break;
		case 0x19:
			break;
		case 0x1F:
			BIOS_MIDI_KEY_2_FREQ();
			break;
		case 0x2A:
			BIOS_SND_DRIVER_JMP_TABLE_COPY();
			/* let it go, because we don't really emulate this function */
		default:
			break;
	}
}

/*============================================================
	GBA ARM CORE
============================================================ */

#ifdef _MSC_VER
 /* Disable "empty statement" warnings */
 #pragma warning(disable: 4390)
 /* Visual C's inline assembler treats "offset" as a reserved word, so we */
 /* tell it otherwise.  If you want to use it, write "OFFSET" in capitals.e */
 #define offset offset_
#endif

static void armUnknownInsn(uint32_t opcode)
{
	uint32_t PC = bus.reg[15].I;
	bool savedArmState = armState;
	if(armMode != 0x1b )
		CPUSwitchMode(0x1b, true, false);
	bus.reg[14].I = PC - (savedArmState ? 4 : 2);
	bus.reg[15].I = 0x04;
	armState = true;
	armIrqEnable = false;
	bus.armNextPC = 0x04;
	ARM_PREFETCH;
	bus.reg[15].I += 4;
}

/* Common macros ////////////////////////////////////////////////////////// */

#define NEG(i) ((i) >> 31)
#define POS(i) ((~(i)) >> 31)

/* The following macros are used for optimization; any not defined for a */
/* particular compiler/CPU combination default to the C core versions. */
/* */
/*    ALU_INIT_C:   Used at the beginning of ALU instructions (AND/EOR/...). */
/*    (ALU_INIT_NC) Can consist of variable declarations, like the C core, */
/*                  or the start of a continued assembly block, like the */
/*                  x86-optimized version.  The _C version is used when the */
/*                  carry flag from the shift operation is needed (logical */
/*                  operations that set condition codes, like ANDS); the */
/*                  _NC version is used when the carry result is ignored. */
/*    VALUE_XXX: Retrieve the second operand's value for an ALU instruction. */
/*               The _C and _NC versions are used the same way as ALU_INIT. */
/*    OP_XXX: ALU operations.  XXX is the instruction name. */
/*    SETCOND_NONE: Used in multiply instructions in place of SETCOND_MUL */
/*                  when the condition codes are not set.  Usually empty. */
/*    SETCOND_MUL: Used in multiply instructions to set the condition codes. */
/*    ROR_IMM_MSR: Used to rotate the immediate operand for MSR. */
/*    ROR_OFFSET: Used to rotate the `offset' parameter for LDR and STR */
/*                instructions. */
/*    RRX_OFFSET: Used to rotate (RRX) the `offset' parameter for LDR and */
/*                STR instructions. */

/* C core */

#define C_SETCOND_LOGICAL \
    N_FLAG = ((int32_t)res < 0) ? true : false;             \
    Z_FLAG = (res == 0) ? true : false;                 \
    C_FLAG = C_OUT;
#define C_SETCOND_ADD \
    N_FLAG = ((int32_t)res < 0) ? true : false;             \
    Z_FLAG = (res == 0) ? true : false;                 \
    V_FLAG = ((NEG(lhs) & NEG(rhs) & POS(res)) |        \
              (POS(lhs) & POS(rhs) & NEG(res))) ? true : false;\
    C_FLAG = ((NEG(lhs) & NEG(rhs)) |                   \
              (NEG(lhs) & POS(res)) |                   \
              (NEG(rhs) & POS(res))) ? true : false;
#define C_SETCOND_SUB \
    N_FLAG = ((int32_t)res < 0) ? true : false;             \
    Z_FLAG = (res == 0) ? true : false;                 \
    V_FLAG = ((NEG(lhs) & POS(rhs) & POS(res)) |        \
              (POS(lhs) & NEG(rhs) & NEG(res))) ? true : false;\
    C_FLAG = ((NEG(lhs) & POS(rhs)) |                   \
              (NEG(lhs) & POS(res)) |                   \
              (POS(rhs) & POS(res))) ? true : false;

#ifndef ALU_INIT_C
 #define ALU_INIT_C \
    int dest = (opcode>>12) & 15;                       \
    bool C_OUT = C_FLAG;                                \
    uint32_t value;                                     \
    uint32_t res;                                       \
    uint32_t lhs;                                       \
    uint32_t rhs;
#endif
/* OP Rd,Rb,Rm LSL # */
#ifndef VALUE_LSL_IMM_C
 #define VALUE_LSL_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (!shift) {  /* LSL #0 most common? */    \
        value = bus.reg[opcode & 0x0F].I;                   \
    } else {                                            \
        uint32_t v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (32 - shift)) & 1 ? true : false; \
        value = v << shift;                             \
    }
#endif
/* OP Rd,Rb,Rm LSL Rs */
#ifndef VALUE_LSL_REG_C
 #define VALUE_LSL_REG_C \
    uint32_t shift = bus.reg[(opcode >> 8) & 15].I & 0xFF;                \
    uint32_t rm = bus.reg[opcode & 0x0F].I;                           \
    if ((opcode & 0x0F) == 15) {                             \
        rm += 4;                                             \
    }                                                        \
    if (shift) {                                             \
        if (shift == 32) {                                   \
            value = 0;                                       \
            C_OUT = (rm & 1 ? true : false);                 \
        } else if (shift < 32) {                     \
            uint32_t v = rm;                                      \
            C_OUT = (v >> (32 - shift)) & 1 ? true : false;  \
            value = v << shift;                              \
        } else {                                             \
            value = 0;                                       \
            C_OUT = false;                                   \
        }                                                    \
    } else {                                                 \
        value = rm;                                          \
    }
#endif
/* OP Rd,Rb,Rm LSR # */
#ifndef VALUE_LSR_IMM_C
 #define VALUE_LSR_IMM_C \
    uint32_t shift = (opcode >> 7) & 0x1F;          \
    if (shift) {                                \
        uint32_t v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = v >> shift;                             \
    } else {                                            \
        value = 0;                                      \
        C_OUT = (bus.reg[opcode & 0x0F].I & 0x80000000) ? true : false;\
    }
#endif
/* OP Rd,Rb,Rm LSR Rs */
#ifndef VALUE_LSR_REG_C
 #define VALUE_LSR_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8) & 15].I & 0xFF;  \
    uint32_t rm = bus.reg[opcode & 0x0F].I;                      \
    if ((opcode & 0x0F) == 15) {                        \
        rm += 4;                                        \
    }                                                   \
    if (shift) {                                \
        if (shift == 32) {                              \
            value = 0;                                  \
            C_OUT = (rm & 0x80000000 ? true : false);   \
        } else if (shift < 32) {                \
            uint32_t v = rm;                                 \
            C_OUT = (v >> (shift - 1)) & 1 ? true : false;\
            value = v >> shift;                         \
        } else {                                        \
            value = 0;                                  \
            C_OUT = false;                              \
        }                                               \
    } else {                                            \
        value = rm;                                     \
    }
#endif
/* OP Rd,Rb,Rm ASR # */
#ifndef VALUE_ASR_IMM_C
 #define VALUE_ASR_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (shift) {                                        \
        int32_t v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (int)(shift - 1)) & 1 ? true : false;\
        value = v >> (int)shift;                        \
    } else {                                            \
        if (bus.reg[opcode & 0x0F].I & 0x80000000) {        \
            value = 0xFFFFFFFF;                         \
            C_OUT = true;                               \
        } else {                                        \
            value = 0;                                  \
            C_OUT = false;                              \
        }                                               \
    }
#endif
/* OP Rd,Rb,Rm ASR Rs */
#ifndef VALUE_ASR_REG_C
 #define VALUE_ASR_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8)&15].I & 0xFF;    \
    uint32_t rm = bus.reg[opcode & 0x0F].I;                      \
    if ((opcode & 0x0F) == 15) {                        \
        rm += 4;                                        \
    }                                                   \
    if (shift < 32) {                           \
        if (shift) {                            \
            int32_t v = rm;                                 \
            C_OUT = (v >> (int)(shift - 1)) & 1 ? true : false;\
            value = v >> (int)shift;                    \
        } else {                                        \
            value = rm;                                 \
        }                                               \
    } else {                                            \
        if (bus.reg[opcode & 0x0F].I & 0x80000000) {        \
            value = 0xFFFFFFFF;                         \
            C_OUT = true;                               \
        } else {                                        \
            value = 0;                                  \
            C_OUT = false;                              \
        }                                               \
    }
#endif
/* OP Rd,Rb,Rm ROR # */
#ifndef VALUE_ROR_IMM_C
 #define VALUE_ROR_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (shift) {                                \
        uint32_t v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = ((v << (32 - shift)) |                  \
                 (v >> shift));                         \
    } else {                                            \
        uint32_t v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v & 1) ? true : false;                 \
        value = ((v >> 1) |                             \
                 (C_FLAG << 31));                       \
    }
#endif
/* OP Rd,Rb,Rm ROR Rs */
#ifndef VALUE_ROR_REG_C
 #define VALUE_ROR_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8)&15].I & 0xFF;    \
    uint32_t rm = bus.reg[opcode & 0x0F].I;                      \
    if ((opcode & 0x0F) == 15) {                        \
        rm += 4;                                        \
    }                                                   \
    if (shift & 0x1F) {                         \
        uint32_t v = rm;                                     \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = ((v << (32 - shift)) |                  \
                 (v >> shift));                         \
    } else {                                            \
        value = rm;                                     \
        if (shift)                                      \
            C_OUT = (value & 0x80000000 ? true : false);\
    }
#endif
/* OP Rd,Rb,# ROR # */
#ifndef VALUE_IMM_C
 #define VALUE_IMM_C \
    int shift = (opcode & 0xF00) >> 7;                  \
    if (shift) {                              \
        uint32_t v = opcode & 0xFF;                          \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = ((v << (32 - shift)) |                  \
                 (v >> shift));                         \
    } else {                                            \
        value = opcode & 0xFF;                          \
    }
#endif

/* Make the non-carry versions default to the carry versions */
/* (this is fine for C--the compiler will optimize the dead code out) */
#ifndef ALU_INIT_NC
 #define ALU_INIT_NC ALU_INIT_C
#endif
#ifndef VALUE_LSL_IMM_NC
 #define VALUE_LSL_IMM_NC VALUE_LSL_IMM_C
#endif
#ifndef VALUE_LSL_REG_NC
 #define VALUE_LSL_REG_NC VALUE_LSL_REG_C
#endif
#ifndef VALUE_LSR_IMM_NC
 #define VALUE_LSR_IMM_NC VALUE_LSR_IMM_C
#endif
#ifndef VALUE_LSR_REG_NC
 #define VALUE_LSR_REG_NC VALUE_LSR_REG_C
#endif
#ifndef VALUE_ASR_IMM_NC
 #define VALUE_ASR_IMM_NC VALUE_ASR_IMM_C
#endif
#ifndef VALUE_ASR_REG_NC
 #define VALUE_ASR_REG_NC VALUE_ASR_REG_C
#endif
#ifndef VALUE_ROR_IMM_NC
 #define VALUE_ROR_IMM_NC VALUE_ROR_IMM_C
#endif
#ifndef VALUE_ROR_REG_NC
 #define VALUE_ROR_REG_NC VALUE_ROR_REG_C
#endif
#ifndef VALUE_IMM_NC
 #define VALUE_IMM_NC VALUE_IMM_C
#endif

#define C_CHECK_PC(SETCOND) if (dest != 15) { SETCOND }
#ifndef OP_AND
 #define OP_AND \
    res = bus.reg[(opcode>>16)&15].I & value;           \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ANDS
 #define OP_ANDS   OP_AND C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_EOR
 #define OP_EOR \
    res = bus.reg[(opcode>>16)&15].I ^ value;           \
    bus.reg[dest].I = res;
#endif
#ifndef OP_EORS
 #define OP_EORS   OP_EOR C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_SUB
 #define OP_SUB \
    lhs = bus.reg[(opcode>>16)&15].I;                   \
    rhs = value;                                    \
    res = lhs - rhs;                                \
    bus.reg[dest].I = res;
#endif
#ifndef OP_SUBS
 #define OP_SUBS   OP_SUB C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_RSB
 #define OP_RSB \
    lhs = value;                                    \
    rhs = bus.reg[(opcode>>16)&15].I;               \
    res = lhs - rhs;                                \
    bus.reg[dest].I = res;
#endif
#ifndef OP_RSBS
 #define OP_RSBS   OP_RSB C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_ADD
 #define OP_ADD \
    lhs = bus.reg[(opcode>>16)&15].I;                   \
    rhs = value;                                    \
    res = lhs + rhs;                                \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ADDS
 #define OP_ADDS   OP_ADD C_CHECK_PC(C_SETCOND_ADD)
#endif
#ifndef OP_ADC
 #define OP_ADC \
    lhs = bus.reg[(opcode>>16)&15].I;                   \
    rhs = value;                                    \
    res = lhs + rhs + (uint32_t)C_FLAG;                  \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ADCS
 #define OP_ADCS   OP_ADC C_CHECK_PC(C_SETCOND_ADD)
#endif
#ifndef OP_SBC
 #define OP_SBC \
    lhs = bus.reg[(opcode>>16)&15].I;                   \
    rhs = value;                                    \
    res = lhs - rhs - !((uint32_t)C_FLAG);               \
    bus.reg[dest].I = res;
#endif
#ifndef OP_SBCS
 #define OP_SBCS   OP_SBC C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_RSC
 #define OP_RSC \
    lhs = value;                                    \
    rhs = bus.reg[(opcode>>16)&15].I;                   \
    res = lhs - rhs - !((uint32_t)C_FLAG);               \
    bus.reg[dest].I = res;
#endif
#ifndef OP_RSCS
 #define OP_RSCS   OP_RSC C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_TST
 #define OP_TST \
    res = bus.reg[(opcode >> 16) & 0x0F].I & value;     \
    C_SETCOND_LOGICAL;
#endif
#ifndef OP_TEQ
 #define OP_TEQ \
    res = bus.reg[(opcode >> 16) & 0x0F].I ^ value;     \
    C_SETCOND_LOGICAL;
#endif
#ifndef OP_CMP
 #define OP_CMP \
    lhs = bus.reg[(opcode>>16)&15].I;                   \
    rhs = value;                                    \
    res = lhs - rhs;                                \
    C_SETCOND_SUB;
#endif
#ifndef OP_CMN
 #define OP_CMN \
    lhs = bus.reg[(opcode>>16)&15].I;                   \
    rhs = value;                                    \
    res = lhs + rhs;                                \
    C_SETCOND_ADD;
#endif
#ifndef OP_ORR
 #define OP_ORR \
    res = bus.reg[(opcode >> 16) & 0x0F].I | value;     \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ORRS
 #define OP_ORRS   OP_ORR C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_MOV
 #define OP_MOV \
    res = value;                                    \
    bus.reg[dest].I = res;
#endif
#ifndef OP_MOVS
 #define OP_MOVS   OP_MOV C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_BIC
 #define OP_BIC \
    res = bus.reg[(opcode >> 16) & 0x0F].I & (~value);  \
    bus.reg[dest].I = res;
#endif
#ifndef OP_BICS
 #define OP_BICS   OP_BIC C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_MVN
 #define OP_MVN \
    res = ~value;                                   \
    bus.reg[dest].I = res;
#endif
#ifndef OP_MVNS
 #define OP_MVNS   OP_MVN C_CHECK_PC(C_SETCOND_LOGICAL)
#endif

#ifndef SETCOND_NONE
 #define SETCOND_NONE /*nothing*/
#endif
#ifndef SETCOND_MUL
 #define SETCOND_MUL \
     N_FLAG = ((int32_t)bus.reg[dest].I < 0) ? true : false;    \
     Z_FLAG = bus.reg[dest].I ? false : true;
#endif
#ifndef SETCOND_MULL
 #define SETCOND_MULL \
     N_FLAG = (bus.reg[dest].I & 0x80000000) ? true : false;\
     Z_FLAG = bus.reg[dest].I || bus.reg[acc].I ? false : true;
#endif

#ifndef ROR_IMM_MSR
 #define ROR_IMM_MSR \
    uint32_t v = opcode & 0xff;                              \
    value = ((v << (32 - shift)) | (v >> shift));
#endif
#ifndef ROR_OFFSET
 #define ROR_OFFSET \
    offset = ((offset << (32 - shift)) | (offset >> shift));
#endif
#ifndef RRX_OFFSET
 #define RRX_OFFSET \
    offset = ((offset >> 1) | ((int)C_FLAG << 31));
#endif

/* ALU ops (except multiply) ////////////////////////////////////////////// */

/* ALU_INIT: init code (ALU_INIT_C or ALU_INIT_NC) */
/* GETVALUE: load value and shift/rotate (VALUE_XXX) */
/* OP: ALU operation (OP_XXX) */
/* MODECHANGE: MODECHANGE_NO or MODECHANGE_YES */
/* ISREGSHIFT: 1 for insns of the form ...,Rn LSL/etc Rs; 0 otherwise */
/* ALU_INIT, GETVALUE and OP are concatenated in order. */

#define ALU_INSN(ALU_INIT, GETVALUE, OP, MODECHANGE, ISREGSHIFT) \
    ALU_INIT GETVALUE OP;                                        \
    if ((opcode & 0x0000F000) != 0x0000F000) {                   \
        clockTicks = CLOCKTICKS_UPDATE_TYPE32 + ISREGSHIFT;      \
    } else {                                                     \
        MODECHANGE;                                              \
        if (armState) {                                          \
            bus.reg[15].I &= 0xFFFFFFFC;                         \
            bus.armNextPC = bus.reg[15].I;                       \
            bus.reg[15].I += 4;                                  \
            ARM_PREFETCH;                                        \
        } else {                                                 \
            bus.reg[15].I &= 0xFFFFFFFE;                         \
            bus.armNextPC = bus.reg[15].I;                       \
            bus.reg[15].I += 2;                                  \
            THUMB_PREFETCH;                                      \
        }                                                        \
        clockTicks = CLOCKTICKS_UPDATE_TYPE32P + ISREGSHIFT;     \
    }

#define MODECHANGE_NO  /*nothing*/
#define MODECHANGE_YES if(armMode != (bus.reg[17].I & 0x1f)) CPUSwitchMode(bus.reg[17].I & 0x1f, false, true);

#define DEFINE_ALU_INSN_C(CODE1, CODE2, OP, MODECHANGE) \
  static  void arm##CODE1##0(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSL_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##1(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSL_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##2(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSR_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##3(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSR_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##4(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_ASR_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##5(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_ASR_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##6(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_ROR_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##7(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_ROR_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE2##0(uint32_t opcode) { ALU_INSN(ALU_INIT_C, VALUE_IMM_C,     OP_##OP, MODECHANGE_##MODECHANGE, 0); }
#define DEFINE_ALU_INSN_NC(CODE1, CODE2, OP, MODECHANGE) \
  static  void arm##CODE1##0(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSL_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##1(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSL_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##2(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSR_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##3(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSR_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##4(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ASR_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##5(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ASR_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##6(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ROR_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##7(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ROR_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE2##0(uint32_t opcode) { ALU_INSN(ALU_INIT_NC, VALUE_IMM_NC,     OP_##OP, MODECHANGE_##MODECHANGE, 0); }

/* AND */
DEFINE_ALU_INSN_NC(00, 20, AND,  NO)
/* ANDS */
DEFINE_ALU_INSN_C (01, 21, ANDS, YES)

/* EOR */
DEFINE_ALU_INSN_NC(02, 22, EOR,  NO)
/* EORS */
DEFINE_ALU_INSN_C (03, 23, EORS, YES)

/* SUB */
DEFINE_ALU_INSN_NC(04, 24, SUB,  NO)
/* SUBS */
DEFINE_ALU_INSN_NC(05, 25, SUBS, YES)

/* RSB */
DEFINE_ALU_INSN_NC(06, 26, RSB,  NO)
/* RSBS */
DEFINE_ALU_INSN_NC(07, 27, RSBS, YES)

/* ADD */
DEFINE_ALU_INSN_NC(08, 28, ADD,  NO)
/* ADDS */
DEFINE_ALU_INSN_NC(09, 29, ADDS, YES)

/* ADC */
DEFINE_ALU_INSN_NC(0A, 2A, ADC,  NO)
/* ADCS */
DEFINE_ALU_INSN_NC(0B, 2B, ADCS, YES)

/* SBC */
DEFINE_ALU_INSN_NC(0C, 2C, SBC,  NO)
/* SBCS */
DEFINE_ALU_INSN_NC(0D, 2D, SBCS, YES)

/* RSC */
DEFINE_ALU_INSN_NC(0E, 2E, RSC,  NO)
/* RSCS */
DEFINE_ALU_INSN_NC(0F, 2F, RSCS, YES)

/* TST */
DEFINE_ALU_INSN_C (11, 31, TST,  NO)

/* TEQ */
DEFINE_ALU_INSN_C (13, 33, TEQ,  NO)

/* CMP */
DEFINE_ALU_INSN_NC(15, 35, CMP,  NO)

/* CMN */
DEFINE_ALU_INSN_NC(17, 37, CMN,  NO)

/* ORR */
DEFINE_ALU_INSN_NC(18, 38, ORR,  NO)
/* ORRS */
DEFINE_ALU_INSN_C (19, 39, ORRS, YES)

/* MOV */
DEFINE_ALU_INSN_NC(1A, 3A, MOV,  NO)
/* MOVS */
DEFINE_ALU_INSN_C (1B, 3B, MOVS, YES)

/* BIC */
DEFINE_ALU_INSN_NC(1C, 3C, BIC,  NO)
/* BICS */
DEFINE_ALU_INSN_C (1D, 3D, BICS, YES)

/* MVN */
DEFINE_ALU_INSN_NC(1E, 3E, MVN,  NO)
/* MVNS */
DEFINE_ALU_INSN_C (1F, 3F, MVNS, YES)

/* Multiply instructions ////////////////////////////////////////////////// */

/* OP: OP_MUL, OP_MLA etc. */
/* SETCOND: SETCOND_NONE, SETCOND_MUL, or SETCOND_MULL */
/* CYCLES: base cycle count (1, 2, or 3) */
#define MUL_INSN(OP, SETCOND, CYCLES)                   \
    int mult = (opcode & 0x0F);                         \
    uint32_t rs = bus.reg[(opcode >> 8) & 0x0F].I;           \
    int acc = (opcode >> 12) & 0x0F;   /* or destLo */  \
    int dest = (opcode >> 16) & 0x0F;  /* or destHi */  \
    OP;                                                 \
    SETCOND;                                            \
    if ((int32_t)rs < 0)                                    \
        rs = ~rs;                                       \
    if ((rs & 0xFFFFFF00) == 0)                         \
        clockTicks += 0;                                \
    else if ((rs & 0xFFFF0000) == 0)                    \
        clockTicks += 1;                                \
    else if ((rs & 0xFF000000) == 0)                    \
        clockTicks += 2;                                \
    else                                                \
        clockTicks += 3;                                \
    if (bus.busPrefetchCount == 0)                          \
        bus.busPrefetchCount = ((bus.busPrefetchCount+1)<<clockTicks) - 1; \
    clockTicks += CYCLES + 1 + codeTicksAccess(bus.armNextPC, BITS_32);

#define OP_MUL \
    bus.reg[dest].I = bus.reg[mult].I * rs;
#define OP_MLA \
    bus.reg[dest].I = bus.reg[mult].I * rs + bus.reg[acc].I;
#define OP_MULL(T64, T32) \
    T64 res = (T64)(T32)bus.reg[mult].I      \
                 * (T64)(T32)rs;              \
    bus.reg[acc].I = (uint32_t)res;                              \
    bus.reg[dest].I = (uint32_t)(res >> 32);
#define OP_MLAL(T64, T32) \
    T64 res = ((T64)bus.reg[dest].I<<32 | bus.reg[acc].I)\
                 + ((T64)(T32)bus.reg[mult].I     \
                    * (T64)(T32)rs);          \
    bus.reg[acc].I = (uint32_t)res;                              \
    bus.reg[dest].I = (uint32_t)(res >> 32);
#define OP_UMULL OP_MULL(uint64_t, uint32_t)
#define OP_UMLAL OP_MLAL(uint64_t, uint32_t)
#define OP_SMULL OP_MULL(int64_t, int32_t)
#define OP_SMLAL OP_MLAL(int64_t, int32_t)

/* MUL Rd, Rm, Rs */
static  void arm009(uint32_t opcode) { MUL_INSN(OP_MUL, SETCOND_NONE, 1); }
/* MULS Rd, Rm, Rs */
static  void arm019(uint32_t opcode) { MUL_INSN(OP_MUL, SETCOND_MUL, 1); }

/* MLA Rd, Rm, Rs, Rn */
static  void arm029(uint32_t opcode) { MUL_INSN(OP_MLA, SETCOND_NONE, 2); }
/* MLAS Rd, Rm, Rs, Rn */
static  void arm039(uint32_t opcode) { MUL_INSN(OP_MLA, SETCOND_MUL, 2); }

/* UMULL RdLo, RdHi, Rn, Rs */
static  void arm089(uint32_t opcode) { MUL_INSN(OP_UMULL, SETCOND_NONE, 2); }
/* UMULLS RdLo, RdHi, Rn, Rs */
static  void arm099(uint32_t opcode) { MUL_INSN(OP_UMULL, SETCOND_MULL, 2); }

/* UMLAL RdLo, RdHi, Rn, Rs */
static  void arm0A9(uint32_t opcode) { MUL_INSN(OP_UMLAL, SETCOND_NONE, 3); }
/* UMLALS RdLo, RdHi, Rn, Rs */
static  void arm0B9(uint32_t opcode) { MUL_INSN(OP_UMLAL, SETCOND_MULL, 3); }

/* SMULL RdLo, RdHi, Rm, Rs */
static  void arm0C9(uint32_t opcode) { MUL_INSN(OP_SMULL, SETCOND_NONE, 2); }
/* SMULLS RdLo, RdHi, Rm, Rs */
static  void arm0D9(uint32_t opcode) { MUL_INSN(OP_SMULL, SETCOND_MULL, 2); }

/* SMLAL RdLo, RdHi, Rm, Rs */
static  void arm0E9(uint32_t opcode) { MUL_INSN(OP_SMLAL, SETCOND_NONE, 3); }
/* SMLALS RdLo, RdHi, Rm, Rs */
static  void arm0F9(uint32_t opcode) { MUL_INSN(OP_SMLAL, SETCOND_MULL, 3); }

/* Misc instructions ////////////////////////////////////////////////////// */

/* SWP Rd, Rm, [Rn] */
static  void arm109(uint32_t opcode)
{
	int dataticks_value;
	uint32_t address = bus.reg[(opcode >> 16) & 15].I;
	uint32_t temp = CPUReadMemory(address);
	CPUWriteMemory(address, bus.reg[opcode&15].I);
	bus.reg[(opcode >> 12) & 15].I = temp;
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 4 + (dataticks_value << 1) + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* SWPB Rd, Rm, [Rn] */
static  void arm149(uint32_t opcode)
{
	uint32_t dataticks_value;
	uint32_t address = bus.reg[(opcode >> 16) & 15].I;
	uint32_t temp = CPUReadByte(address);
	CPUWriteByte(address, bus.reg[opcode&15].I & 0xFF);
	bus.reg[(opcode>>12)&15].I = temp;
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 4 + (dataticks_value << 1) + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* MRS Rd, CPSR */
static  void arm100(uint32_t opcode)
{
	if ((opcode & 0x0FFF0FFF) == 0x010F0000)
	{
		CPU_UPDATE_CPSR();
		bus.reg[(opcode >> 12) & 0x0F].I = bus.reg[16].I;
	}
	else
		armUnknownInsn(opcode);
}

/* MRS Rd, SPSR */
static  void arm140(uint32_t opcode)
{
	if ((opcode & 0x0FFF0FFF) == 0x014F0000)
		bus.reg[(opcode >> 12) & 0x0F].I = bus.reg[17].I;
	else
		armUnknownInsn(opcode);
}

/* MSR CPSR_fields, Rm */
static  void arm120(uint32_t opcode)
{
    if ((opcode & 0x0FF0FFF0) == 0x0120F000)
    {
	    uint32_t value;
	    uint32_t newValue;
	    CPU_UPDATE_CPSR();
	    value = bus.reg[opcode & 15].I;
	    newValue = bus.reg[16].I;
	    if (armMode > 0x10) {
		    if (opcode & 0x00010000)
			    newValue = (newValue & 0xFFFFFF00) | (value & 0x000000FF);
		    if (opcode & 0x00020000)
			    newValue = (newValue & 0xFFFF00FF) | (value & 0x0000FF00);
		    if (opcode & 0x00040000)
			    newValue = (newValue & 0xFF00FFFF) | (value & 0x00FF0000);
	    }
	    if (opcode & 0x00080000)
		    newValue = (newValue & 0x00FFFFFF) | (value & 0xFF000000);
	    newValue |= 0x10;
	    if(armMode != (newValue & 0x1F))
		    CPUSwitchMode(newValue & 0x1F, false, true);
	    bus.reg[16].I = newValue;
	    CPUUpdateFlags(1);
	    if (!armState) {  /* this should not be allowed, but it seems to work */
		    THUMB_PREFETCH;
		    bus.reg[15].I = bus.armNextPC + 2;
	    }
    }
    else
	    armUnknownInsn(opcode);
}

/* MSR SPSR_fields, Rm */
static  void arm160(uint32_t opcode)
{
	if ((opcode & 0x0FF0FFF0) == 0x0160F000)
	{
		uint32_t value = bus.reg[opcode & 15].I;
		if (armMode > 0x10 && armMode < 0x1F)
		{
			if (opcode & 0x00010000)
				bus.reg[17].I = (bus.reg[17].I & 0xFFFFFF00) | (value & 0x000000FF);
			if (opcode & 0x00020000)
				bus.reg[17].I = (bus.reg[17].I & 0xFFFF00FF) | (value & 0x0000FF00);
			if (opcode & 0x00040000)
				bus.reg[17].I = (bus.reg[17].I & 0xFF00FFFF) | (value & 0x00FF0000);
			if (opcode & 0x00080000)
				bus.reg[17].I = (bus.reg[17].I & 0x00FFFFFF) | (value & 0xFF000000);
		}
	}
	else
		armUnknownInsn(opcode);
}

/* MSR CPSR_fields, # */
static  void arm320(uint32_t opcode)
{
	if ((opcode & 0x0FF0F000) == 0x0320F000)
	{
		uint32_t value;
		int shift;
		uint32_t newValue;
		CPU_UPDATE_CPSR();
		value = opcode & 0xFF;
		shift = (opcode & 0xF00) >> 7;
		if (shift) {
			ROR_IMM_MSR;
		}
		newValue = bus.reg[16].I;
		if (armMode > 0x10) {
			if (opcode & 0x00010000)
				newValue = (newValue & 0xFFFFFF00) | (value & 0x000000FF);
			if (opcode & 0x00020000)
				newValue = (newValue & 0xFFFF00FF) | (value & 0x0000FF00);
			if (opcode & 0x00040000)
				newValue = (newValue & 0xFF00FFFF) | (value & 0x00FF0000);
		}
		if (opcode & 0x00080000)
			newValue = (newValue & 0x00FFFFFF) | (value & 0xFF000000);

		newValue |= 0x10;

		if(armMode != (newValue & 0x1F))
			CPUSwitchMode(newValue & 0x1F, false, true);
		bus.reg[16].I = newValue;
		CPUUpdateFlags(1);
		if (!armState) {  /* this should not be allowed, but it seems to work */
			THUMB_PREFETCH;
			bus.reg[15].I = bus.armNextPC + 2;
		}
	}
	else
		armUnknownInsn(opcode);
}

/* MSR SPSR_fields, # */
static  void arm360(uint32_t opcode)
{
	if ((opcode & 0x0FF0F000) == 0x0360F000) {
		if (armMode > 0x10 && armMode < 0x1F) {
			uint32_t value = opcode & 0xFF;
			int shift = (opcode & 0xF00) >> 7;
			if (shift) {
				ROR_IMM_MSR;
			}
			if (opcode & 0x00010000)
				bus.reg[17].I = (bus.reg[17].I & 0xFFFFFF00) | (value & 0x000000FF);
			if (opcode & 0x00020000)
				bus.reg[17].I = (bus.reg[17].I & 0xFFFF00FF) | (value & 0x0000FF00);
			if (opcode & 0x00040000)
				bus.reg[17].I = (bus.reg[17].I & 0xFF00FFFF) | (value & 0x00FF0000);
			if (opcode & 0x00080000)
				bus.reg[17].I = (bus.reg[17].I & 0x00FFFFFF) | (value & 0xFF000000);
		}
	}
	else
		armUnknownInsn(opcode);
}

/* BX Rm */
static  void arm121(uint32_t opcode)
{
	if ((opcode & 0x0FFFFFF0) == 0x012FFF10) {
		int base = opcode & 0x0F;
		bus.busPrefetchCount = 0;
		armState = bus.reg[base].I & 1 ? false : true;
		if (armState) {
			bus.reg[15].I = bus.reg[base].I & 0xFFFFFFFC;
			bus.armNextPC = bus.reg[15].I;
			bus.reg[15].I += 4;
			ARM_PREFETCH;
			clockTicks = CLOCKTICKS_UPDATE_TYPE32P;
		} else {
			bus.reg[15].I = bus.reg[base].I & 0xFFFFFFFE;
			bus.armNextPC = bus.reg[15].I;
			bus.reg[15].I += 2;
			THUMB_PREFETCH;
			clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
		}
	}
	else
		armUnknownInsn(opcode);
}

/* Load/store ///////////////////////////////////////////////////////////// */

#define OFFSET_IMM \
    offset = opcode & 0xFFF;
#define OFFSET_IMM8 \
    offset = ((opcode & 0x0F) | ((opcode>>4) & 0xF0));
#define OFFSET_REG \
    offset = bus.reg[opcode & 15].I;
#define OFFSET_LSL \
    offset = bus.reg[opcode & 15].I << ((opcode>>7) & 31);
#define OFFSET_LSR \
    shift = (opcode >> 7) & 31;                         \
    offset = shift ? bus.reg[opcode & 15].I >> shift : 0;
#define OFFSET_ASR \
    shift = (opcode >> 7) & 31;                         \
    if (shift)                                          \
        offset = (uint32_t)((int32_t)bus.reg[opcode & 15].I >> shift);\
    else if (bus.reg[opcode & 15].I & 0x80000000)           \
        offset = 0xFFFFFFFF;                            \
    else                                                \
        offset = 0;
#define OFFSET_ROR \
    shift = (opcode >> 7) & 31;                         \
    offset = bus.reg[opcode & 15].I;                    \
    if (shift) {                                        \
        ROR_OFFSET;                                     \
    } else {                                            \
        RRX_OFFSET;                                     \
    }

#define ADDRESS_POST (bus.reg[base].I)
#define ADDRESS_PREDEC (bus.reg[base].I - offset)
#define ADDRESS_PREINC (bus.reg[base].I + offset)

#define OP_STR    CPUWriteMemory(address, bus.reg[dest].I)
#define OP_STRH   CPUWriteHalfWord(address, bus.reg[dest].I & 0xFFFF)
#define OP_STRB   CPUWriteByte(address, bus.reg[dest].I & 0xFF)
#define OP_LDR    bus.reg[dest].I = CPUReadMemory(address)
#define OP_LDRH   bus.reg[dest].I = CPUReadHalfWord(address)
#define OP_LDRB   bus.reg[dest].I = CPUReadByte(address)
#define OP_LDRSH  bus.reg[dest].I = (int16_t)CPUReadHalfWordSigned(address)
#define OP_LDRSB  bus.reg[dest].I = (int8_t)CPUReadByte(address)

#define WRITEBACK_NONE     /*nothing*/
#define WRITEBACK_PRE      bus.reg[base].I = address
#define WRITEBACK_POSTDEC  bus.reg[base].I = address - offset
#define WRITEBACK_POSTINC  bus.reg[base].I = address + offset

#define LDRSTR_INIT(CALC_OFFSET, CALC_ADDRESS) \
    int dest = (opcode >> 12) & 15;                     \
    int base = (opcode >> 16) & 15;                     \
    int dataticks_value;                                \
    int shift;                                          \
    uint32_t offset;                                    \
    uint32_t address;                                   \
    if (bus.busPrefetchCount == 0)                          \
        bus.busPrefetch = bus.busPrefetchEnable;                \
    CALC_OFFSET;                                        \
    address = CALC_ADDRESS;

#define STR(CALC_OFFSET, CALC_ADDRESS, STORE_DATA, WRITEBACK1, WRITEBACK2, SIZE) \
    LDRSTR_INIT(CALC_OFFSET, CALC_ADDRESS);             \
    WRITEBACK1;                                         \
    STORE_DATA;                                         \
    WRITEBACK2;                                         \
    if(SIZE == 32) \
       dataticks_value = DATATICKS_ACCESS_32BIT(address);	\
    else \
       dataticks_value = DATATICKS_ACCESS_16BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
    clockTicks = 2 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_32);

#define LDR(CALC_OFFSET, CALC_ADDRESS, LOAD_DATA, WRITEBACK, SIZE) \
    LDRSTR_INIT(CALC_OFFSET, CALC_ADDRESS);             \
    LOAD_DATA;                                          \
    if (dest != base)                                   \
    {                                                   \
        WRITEBACK;                                      \
    }                                                   \
    clockTicks = 0;                                     \
    if (dest == 15) {                                   \
        bus.reg[15].I &= 0xFFFFFFFC;                        \
        bus.armNextPC = bus.reg[15].I;                          \
        bus.reg[15].I += 4;                                 \
        ARM_PREFETCH;                                   \
	dataticks_value = DATATICKS_ACCESS_32BIT_SEQ(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
        clockTicks += 2 + (dataticks_value << 1);\
    }                                                   \
    if(SIZE == 32)					\
    dataticks_value = DATATICKS_ACCESS_32BIT(address); \
    else \
    dataticks_value = DATATICKS_ACCESS_16BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
    clockTicks += 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_32);
#define STR_POSTDEC(CALC_OFFSET, STORE_DATA, SIZE) \
  STR(CALC_OFFSET, ADDRESS_POST, STORE_DATA, WRITEBACK_NONE, WRITEBACK_POSTDEC, SIZE)
#define STR_POSTINC(CALC_OFFSET, STORE_DATA, SIZE) \
  STR(CALC_OFFSET, ADDRESS_POST, STORE_DATA, WRITEBACK_NONE, WRITEBACK_POSTINC, SIZE)
#define STR_PREDEC(CALC_OFFSET, STORE_DATA, SIZE) \
  STR(CALC_OFFSET, ADDRESS_PREDEC, STORE_DATA, WRITEBACK_NONE, WRITEBACK_NONE, SIZE)
#define STR_PREDEC_WB(CALC_OFFSET, STORE_DATA, SIZE) \
  STR(CALC_OFFSET, ADDRESS_PREDEC, STORE_DATA, WRITEBACK_PRE, WRITEBACK_NONE, SIZE)
#define STR_PREINC(CALC_OFFSET, STORE_DATA, SIZE) \
  STR(CALC_OFFSET, ADDRESS_PREINC, STORE_DATA, WRITEBACK_NONE, WRITEBACK_NONE, SIZE)
#define STR_PREINC_WB(CALC_OFFSET, STORE_DATA, SIZE) \
  STR(CALC_OFFSET, ADDRESS_PREINC, STORE_DATA, WRITEBACK_PRE, WRITEBACK_NONE, SIZE)
#define LDR_POSTDEC(CALC_OFFSET, LOAD_DATA, SIZE) \
  LDR(CALC_OFFSET, ADDRESS_POST, LOAD_DATA, WRITEBACK_POSTDEC, SIZE)
#define LDR_POSTINC(CALC_OFFSET, LOAD_DATA, SIZE) \
  LDR(CALC_OFFSET, ADDRESS_POST, LOAD_DATA, WRITEBACK_POSTINC, SIZE)
#define LDR_PREDEC(CALC_OFFSET, LOAD_DATA, SIZE) \
  LDR(CALC_OFFSET, ADDRESS_PREDEC, LOAD_DATA, WRITEBACK_NONE, SIZE)
#define LDR_PREDEC_WB(CALC_OFFSET, LOAD_DATA, SIZE) \
  LDR(CALC_OFFSET, ADDRESS_PREDEC, LOAD_DATA, WRITEBACK_PRE, SIZE)
#define LDR_PREINC(CALC_OFFSET, LOAD_DATA, SIZE) \
  LDR(CALC_OFFSET, ADDRESS_PREINC, LOAD_DATA, WRITEBACK_NONE, SIZE)
#define LDR_PREINC_WB(CALC_OFFSET, LOAD_DATA, SIZE) \
  LDR(CALC_OFFSET, ADDRESS_PREINC, LOAD_DATA, WRITEBACK_PRE, SIZE)

/* STRH Rd, [Rn], -Rm */
static  void arm00B(uint32_t opcode) { STR_POSTDEC(OFFSET_REG, OP_STRH, 16); }
/* STRH Rd, [Rn], #-offset */
static  void arm04B(uint32_t opcode) { STR_POSTDEC(OFFSET_IMM8, OP_STRH, 16); }
/* STRH Rd, [Rn], Rm */
static  void arm08B(uint32_t opcode) { STR_POSTINC(OFFSET_REG, OP_STRH, 16); }
/* STRH Rd, [Rn], #offset */
static  void arm0CB(uint32_t opcode) { STR_POSTINC(OFFSET_IMM8, OP_STRH, 16); }
/* STRH Rd, [Rn, -Rm] */
static  void arm10B(uint32_t opcode) { STR_PREDEC(OFFSET_REG, OP_STRH, 16); }
/* STRH Rd, [Rn, -Rm]! */
static  void arm12B(uint32_t opcode) { STR_PREDEC_WB(OFFSET_REG, OP_STRH, 16); }
/* STRH Rd, [Rn, -#offset] */
static  void arm14B(uint32_t opcode) { STR_PREDEC(OFFSET_IMM8, OP_STRH, 16); }
/* STRH Rd, [Rn, -#offset]! */
static  void arm16B(uint32_t opcode) { STR_PREDEC_WB(OFFSET_IMM8, OP_STRH, 16); }
/* STRH Rd, [Rn, Rm] */
static  void arm18B(uint32_t opcode) { STR_PREINC(OFFSET_REG, OP_STRH, 16); }
/* STRH Rd, [Rn, Rm]! */
static  void arm1AB(uint32_t opcode) { STR_PREINC_WB(OFFSET_REG, OP_STRH, 16); }
/* STRH Rd, [Rn, #offset] */
static  void arm1CB(uint32_t opcode) { STR_PREINC(OFFSET_IMM8, OP_STRH, 16); }
/* STRH Rd, [Rn, #offset]! */
static  void arm1EB(uint32_t opcode) { STR_PREINC_WB(OFFSET_IMM8, OP_STRH, 16); }

/* LDRH Rd, [Rn], -Rm */
static  void arm01B(uint32_t opcode) { LDR_POSTDEC(OFFSET_REG, OP_LDRH, 16); }
/* LDRH Rd, [Rn], #-offset */
static  void arm05B(uint32_t opcode) { LDR_POSTDEC(OFFSET_IMM8, OP_LDRH, 16); }
/* LDRH Rd, [Rn], Rm */
static  void arm09B(uint32_t opcode) { LDR_POSTINC(OFFSET_REG, OP_LDRH, 16); }
/* LDRH Rd, [Rn], #offset */
static  void arm0DB(uint32_t opcode) { LDR_POSTINC(OFFSET_IMM8, OP_LDRH, 16); }
/* LDRH Rd, [Rn, -Rm] */
static  void arm11B(uint32_t opcode) { LDR_PREDEC(OFFSET_REG, OP_LDRH, 16); }
/* LDRH Rd, [Rn, -Rm]! */
static  void arm13B(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_REG, OP_LDRH, 16); }
/* LDRH Rd, [Rn, -#offset] */
static  void arm15B(uint32_t opcode) { LDR_PREDEC(OFFSET_IMM8, OP_LDRH, 16); }
/* LDRH Rd, [Rn, -#offset]! */
static  void arm17B(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_IMM8, OP_LDRH, 16); }
/* LDRH Rd, [Rn, Rm] */
static  void arm19B(uint32_t opcode) { LDR_PREINC(OFFSET_REG, OP_LDRH, 16); }
/* LDRH Rd, [Rn, Rm]! */
static  void arm1BB(uint32_t opcode) { LDR_PREINC_WB(OFFSET_REG, OP_LDRH, 16); }
/* LDRH Rd, [Rn, #offset] */
static  void arm1DB(uint32_t opcode) { LDR_PREINC(OFFSET_IMM8, OP_LDRH, 16); }
/* LDRH Rd, [Rn, #offset]! */
static  void arm1FB(uint32_t opcode) { LDR_PREINC_WB(OFFSET_IMM8, OP_LDRH, 16); }

/* LDRSB Rd, [Rn], -Rm */
static  void arm01D(uint32_t opcode) { LDR_POSTDEC(OFFSET_REG, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn], #-offset */
static  void arm05D(uint32_t opcode) { LDR_POSTDEC(OFFSET_IMM8, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn], Rm */
static  void arm09D(uint32_t opcode) { LDR_POSTINC(OFFSET_REG, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn], #offset */
static  void arm0DD(uint32_t opcode) { LDR_POSTINC(OFFSET_IMM8, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, -Rm] */
static  void arm11D(uint32_t opcode) { LDR_PREDEC(OFFSET_REG, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, -Rm]! */
static  void arm13D(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_REG, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, -#offset] */
static  void arm15D(uint32_t opcode) { LDR_PREDEC(OFFSET_IMM8, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, -#offset]! */
static  void arm17D(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_IMM8, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, Rm] */
static  void arm19D(uint32_t opcode) { LDR_PREINC(OFFSET_REG, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, Rm]! */
static  void arm1BD(uint32_t opcode) { LDR_PREINC_WB(OFFSET_REG, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, #offset] */
static  void arm1DD(uint32_t opcode) { LDR_PREINC(OFFSET_IMM8, OP_LDRSB, 16); }
/* LDRSB Rd, [Rn, #offset]! */
static  void arm1FD(uint32_t opcode) { LDR_PREINC_WB(OFFSET_IMM8, OP_LDRSB, 16); }

/* LDRSH Rd, [Rn], -Rm */
static  void arm01F(uint32_t opcode) { LDR_POSTDEC(OFFSET_REG, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn], #-offset */
static  void arm05F(uint32_t opcode) { LDR_POSTDEC(OFFSET_IMM8, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn], Rm */
static  void arm09F(uint32_t opcode) { LDR_POSTINC(OFFSET_REG, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn], #offset */
static  void arm0DF(uint32_t opcode) { LDR_POSTINC(OFFSET_IMM8, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, -Rm] */
static  void arm11F(uint32_t opcode) { LDR_PREDEC(OFFSET_REG, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, -Rm]! */
static  void arm13F(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_REG, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, -#offset] */
static  void arm15F(uint32_t opcode) { LDR_PREDEC(OFFSET_IMM8, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, -#offset]! */
static  void arm17F(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_IMM8, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, Rm] */
static  void arm19F(uint32_t opcode) { LDR_PREINC(OFFSET_REG, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, Rm]! */
static  void arm1BF(uint32_t opcode) { LDR_PREINC_WB(OFFSET_REG, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, #offset] */
static  void arm1DF(uint32_t opcode) { LDR_PREINC(OFFSET_IMM8, OP_LDRSH, 16); }
/* LDRSH Rd, [Rn, #offset]! */
static  void arm1FF(uint32_t opcode) { LDR_PREINC_WB(OFFSET_IMM8, OP_LDRSH, 16); }

/* STR[T] Rd, [Rn], -# */
/* Note: STR and STRT do the same thing on the GBA (likewise for LDR/LDRT etc) */
static  void arm400(uint32_t opcode) { STR_POSTDEC(OFFSET_IMM, OP_STR, 32); }
/* LDR[T] Rd, [Rn], -# */
static  void arm410(uint32_t opcode) { LDR_POSTDEC(OFFSET_IMM, OP_LDR, 32); }
/* STRB[T] Rd, [Rn], -# */
static  void arm440(uint32_t opcode) { STR_POSTDEC(OFFSET_IMM, OP_STRB, 16); }
/* LDRB[T] Rd, [Rn], -# */
static  void arm450(uint32_t opcode) { LDR_POSTDEC(OFFSET_IMM, OP_LDRB, 16); }
/* STR[T] Rd, [Rn], # */
static  void arm480(uint32_t opcode) { STR_POSTINC(OFFSET_IMM, OP_STR, 32); }
/* LDR Rd, [Rn], # */
static  void arm490(uint32_t opcode) { LDR_POSTINC(OFFSET_IMM, OP_LDR, 32); }
/* STRB[T] Rd, [Rn], # */
static  void arm4C0(uint32_t opcode) { STR_POSTINC(OFFSET_IMM, OP_STRB, 16); }
/* LDRB[T] Rd, [Rn], # */
static  void arm4D0(uint32_t opcode) { LDR_POSTINC(OFFSET_IMM, OP_LDRB, 16); }
/* STR Rd, [Rn, -#] */
static  void arm500(uint32_t opcode) { STR_PREDEC(OFFSET_IMM, OP_STR, 32); }
/* LDR Rd, [Rn, -#] */
static  void arm510(uint32_t opcode) { LDR_PREDEC(OFFSET_IMM, OP_LDR, 32); }
/* STR Rd, [Rn, -#]! */
static  void arm520(uint32_t opcode) { STR_PREDEC_WB(OFFSET_IMM, OP_STR, 32); }
/* LDR Rd, [Rn, -#]! */
static  void arm530(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_IMM, OP_LDR, 32); }
/* STRB Rd, [Rn, -#] */
static  void arm540(uint32_t opcode) { STR_PREDEC(OFFSET_IMM, OP_STRB, 16); }
/* LDRB Rd, [Rn, -#] */
static  void arm550(uint32_t opcode) { LDR_PREDEC(OFFSET_IMM, OP_LDRB, 16); }
/* STRB Rd, [Rn, -#]! */
static  void arm560(uint32_t opcode) { STR_PREDEC_WB(OFFSET_IMM, OP_STRB, 16); }
/* LDRB Rd, [Rn, -#]! */
static  void arm570(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_IMM, OP_LDRB, 16); }
/* STR Rd, [Rn, #] */
static  void arm580(uint32_t opcode) { STR_PREINC(OFFSET_IMM, OP_STR, 32); }
/* LDR Rd, [Rn, #] */
static  void arm590(uint32_t opcode) { LDR_PREINC(OFFSET_IMM, OP_LDR, 32); }
/* STR Rd, [Rn, #]! */
static  void arm5A0(uint32_t opcode) { STR_PREINC_WB(OFFSET_IMM, OP_STR, 32); }
/* LDR Rd, [Rn, #]! */
static  void arm5B0(uint32_t opcode) { LDR_PREINC_WB(OFFSET_IMM, OP_LDR, 32); }
/* STRB Rd, [Rn, #] */
static  void arm5C0(uint32_t opcode) { STR_PREINC(OFFSET_IMM, OP_STRB, 16); }
/* LDRB Rd, [Rn, #] */
static  void arm5D0(uint32_t opcode) { LDR_PREINC(OFFSET_IMM, OP_LDRB, 16); }
/* STRB Rd, [Rn, #]! */
static  void arm5E0(uint32_t opcode) { STR_PREINC_WB(OFFSET_IMM, OP_STRB, 16); }
/* LDRB Rd, [Rn, #]! */
static  void arm5F0(uint32_t opcode) { LDR_PREINC_WB(OFFSET_IMM, OP_LDRB, 16); }

/* STR[T] Rd, [Rn], -Rm, LSL # */
static  void arm600(uint32_t opcode) { STR_POSTDEC(OFFSET_LSL, OP_STR, 32); }
/* STR[T] Rd, [Rn], -Rm, LSR # */
static  void arm602(uint32_t opcode) { STR_POSTDEC(OFFSET_LSR, OP_STR, 32); }
/* STR[T] Rd, [Rn], -Rm, ASR # */
static  void arm604(uint32_t opcode) { STR_POSTDEC(OFFSET_ASR, OP_STR, 32); }
/* STR[T] Rd, [Rn], -Rm, ROR # */
static  void arm606(uint32_t opcode) { STR_POSTDEC(OFFSET_ROR, OP_STR, 32); }
/* LDR[T] Rd, [Rn], -Rm, LSL # */
static  void arm610(uint32_t opcode) { LDR_POSTDEC(OFFSET_LSL, OP_LDR, 32); }
/* LDR[T] Rd, [Rn], -Rm, LSR # */
static  void arm612(uint32_t opcode) { LDR_POSTDEC(OFFSET_LSR, OP_LDR, 32); }
/* LDR[T] Rd, [Rn], -Rm, ASR # */
static  void arm614(uint32_t opcode) { LDR_POSTDEC(OFFSET_ASR, OP_LDR, 32); }
/* LDR[T] Rd, [Rn], -Rm, ROR # */
static  void arm616(uint32_t opcode) { LDR_POSTDEC(OFFSET_ROR, OP_LDR, 32); }
/* STRB[T] Rd, [Rn], -Rm, LSL # */
static  void arm640(uint32_t opcode) { STR_POSTDEC(OFFSET_LSL, OP_STRB, 16); }
/* STRB[T] Rd, [Rn], -Rm, LSR # */
static  void arm642(uint32_t opcode) { STR_POSTDEC(OFFSET_LSR, OP_STRB, 16); }
/* STRB[T] Rd, [Rn], -Rm, ASR # */
static  void arm644(uint32_t opcode) { STR_POSTDEC(OFFSET_ASR, OP_STRB, 16); }
/* STRB[T] Rd, [Rn], -Rm, ROR # */
static  void arm646(uint32_t opcode) { STR_POSTDEC(OFFSET_ROR, OP_STRB, 16); }
/* LDRB[T] Rd, [Rn], -Rm, LSL # */
static  void arm650(uint32_t opcode) { LDR_POSTDEC(OFFSET_LSL, OP_LDRB, 16); }
/* LDRB[T] Rd, [Rn], -Rm, LSR # */
static  void arm652(uint32_t opcode) { LDR_POSTDEC(OFFSET_LSR, OP_LDRB, 16); }
/* LDRB[T] Rd, [Rn], -Rm, ASR # */
static  void arm654(uint32_t opcode) { LDR_POSTDEC(OFFSET_ASR, OP_LDRB, 16); }
/* LDRB Rd, [Rn], -Rm, ROR # */
static  void arm656(uint32_t opcode) { LDR_POSTDEC(OFFSET_ROR, OP_LDRB, 16); }
/* STR[T] Rd, [Rn], Rm, LSL # */
static  void arm680(uint32_t opcode) { STR_POSTINC(OFFSET_LSL, OP_STR, 32); }
/* STR[T] Rd, [Rn], Rm, LSR # */
static  void arm682(uint32_t opcode) { STR_POSTINC(OFFSET_LSR, OP_STR, 32); }
/* STR[T] Rd, [Rn], Rm, ASR # */
static  void arm684(uint32_t opcode) { STR_POSTINC(OFFSET_ASR, OP_STR, 32); }
/* STR[T] Rd, [Rn], Rm, ROR # */
static  void arm686(uint32_t opcode) { STR_POSTINC(OFFSET_ROR, OP_STR, 32); }
/* LDR[T] Rd, [Rn], Rm, LSL # */
static  void arm690(uint32_t opcode) { LDR_POSTINC(OFFSET_LSL, OP_LDR, 32); }
/* LDR[T] Rd, [Rn], Rm, LSR # */
static  void arm692(uint32_t opcode) { LDR_POSTINC(OFFSET_LSR, OP_LDR, 32); }
/* LDR[T] Rd, [Rn], Rm, ASR # */
static  void arm694(uint32_t opcode) { LDR_POSTINC(OFFSET_ASR, OP_LDR, 32); }
/* LDR[T] Rd, [Rn], Rm, ROR # */
static  void arm696(uint32_t opcode) { LDR_POSTINC(OFFSET_ROR, OP_LDR, 32); }
/* STRB[T] Rd, [Rn], Rm, LSL # */
static  void arm6C0(uint32_t opcode) { STR_POSTINC(OFFSET_LSL, OP_STRB, 16); }
/* STRB[T] Rd, [Rn], Rm, LSR # */
static  void arm6C2(uint32_t opcode) { STR_POSTINC(OFFSET_LSR, OP_STRB, 16); }
/* STRB[T] Rd, [Rn], Rm, ASR # */
static  void arm6C4(uint32_t opcode) { STR_POSTINC(OFFSET_ASR, OP_STRB, 16); }
/* STRB[T] Rd, [Rn], Rm, ROR # */
static  void arm6C6(uint32_t opcode) { STR_POSTINC(OFFSET_ROR, OP_STRB, 16); }
/* LDRB[T] Rd, [Rn], Rm, LSL # */
static  void arm6D0(uint32_t opcode) { LDR_POSTINC(OFFSET_LSL, OP_LDRB, 16); }
/* LDRB[T] Rd, [Rn], Rm, LSR # */
static  void arm6D2(uint32_t opcode) { LDR_POSTINC(OFFSET_LSR, OP_LDRB, 16); }
/* LDRB[T] Rd, [Rn], Rm, ASR # */
static  void arm6D4(uint32_t opcode) { LDR_POSTINC(OFFSET_ASR, OP_LDRB, 16); }
/* LDRB[T] Rd, [Rn], Rm, ROR # */
static  void arm6D6(uint32_t opcode) { LDR_POSTINC(OFFSET_ROR, OP_LDRB, 16); }
/* STR Rd, [Rn, -Rm, LSL #] */
static  void arm700(uint32_t opcode) { STR_PREDEC(OFFSET_LSL, OP_STR, 32); }
/* STR Rd, [Rn, -Rm, LSR #] */
static  void arm702(uint32_t opcode) { STR_PREDEC(OFFSET_LSR, OP_STR, 32); }
/* STR Rd, [Rn, -Rm, ASR #] */
static  void arm704(uint32_t opcode) { STR_PREDEC(OFFSET_ASR, OP_STR, 32); }
/* STR Rd, [Rn, -Rm, ROR #] */
static  void arm706(uint32_t opcode) { STR_PREDEC(OFFSET_ROR, OP_STR, 32); }
/* LDR Rd, [Rn, -Rm, LSL #] */
static  void arm710(uint32_t opcode) { LDR_PREDEC(OFFSET_LSL, OP_LDR, 32); }
/* LDR Rd, [Rn, -Rm, LSR #] */
static  void arm712(uint32_t opcode) { LDR_PREDEC(OFFSET_LSR, OP_LDR, 32); }
/* LDR Rd, [Rn, -Rm, ASR #] */
static  void arm714(uint32_t opcode) { LDR_PREDEC(OFFSET_ASR, OP_LDR, 32); }
/* LDR Rd, [Rn, -Rm, ROR #] */
static  void arm716(uint32_t opcode) { LDR_PREDEC(OFFSET_ROR, OP_LDR, 32); }
/* STR Rd, [Rn, -Rm, LSL #]! */
static  void arm720(uint32_t opcode) { STR_PREDEC_WB(OFFSET_LSL, OP_STR, 32); }
/* STR Rd, [Rn, -Rm, LSR #]! */
static  void arm722(uint32_t opcode) { STR_PREDEC_WB(OFFSET_LSR, OP_STR, 32); }
/* STR Rd, [Rn, -Rm, ASR #]! */
static  void arm724(uint32_t opcode) { STR_PREDEC_WB(OFFSET_ASR, OP_STR, 32); }
/* STR Rd, [Rn, -Rm, ROR #]! */
static  void arm726(uint32_t opcode) { STR_PREDEC_WB(OFFSET_ROR, OP_STR, 32); }
/* LDR Rd, [Rn, -Rm, LSL #]! */
static  void arm730(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_LSL, OP_LDR, 32); }
/* LDR Rd, [Rn, -Rm, LSR #]! */
static  void arm732(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_LSR, OP_LDR, 32); }
/* LDR Rd, [Rn, -Rm, ASR #]! */
static  void arm734(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_ASR, OP_LDR, 32); }
/* LDR Rd, [Rn, -Rm, ROR #]! */
static  void arm736(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_ROR, OP_LDR, 32); }
/* STRB Rd, [Rn, -Rm, LSL #] */
static  void arm740(uint32_t opcode) { STR_PREDEC(OFFSET_LSL, OP_STRB, 16); }
/* STRB Rd, [Rn, -Rm, LSR #] */
static  void arm742(uint32_t opcode) { STR_PREDEC(OFFSET_LSR, OP_STRB, 16); }
/* STRB Rd, [Rn, -Rm, ASR #] */
static  void arm744(uint32_t opcode) { STR_PREDEC(OFFSET_ASR, OP_STRB, 16); }
/* STRB Rd, [Rn, -Rm, ROR #] */
static  void arm746(uint32_t opcode) { STR_PREDEC(OFFSET_ROR, OP_STRB, 16); }
/* LDRB Rd, [Rn, -Rm, LSL #] */
static  void arm750(uint32_t opcode) { LDR_PREDEC(OFFSET_LSL, OP_LDRB, 16); }
/* LDRB Rd, [Rn, -Rm, LSR #] */
static  void arm752(uint32_t opcode) { LDR_PREDEC(OFFSET_LSR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, -Rm, ASR #] */
static  void arm754(uint32_t opcode) { LDR_PREDEC(OFFSET_ASR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, -Rm, ROR #] */
static  void arm756(uint32_t opcode) { LDR_PREDEC(OFFSET_ROR, OP_LDRB, 16); }
/* STRB Rd, [Rn, -Rm, LSL #]! */
static  void arm760(uint32_t opcode) { STR_PREDEC_WB(OFFSET_LSL, OP_STRB, 16); }
/* STRB Rd, [Rn, -Rm, LSR #]! */
static  void arm762(uint32_t opcode) { STR_PREDEC_WB(OFFSET_LSR, OP_STRB, 16); }
/* STRB Rd, [Rn, -Rm, ASR #]! */
static  void arm764(uint32_t opcode) { STR_PREDEC_WB(OFFSET_ASR, OP_STRB, 16); }
/* STRB Rd, [Rn, -Rm, ROR #]! */
static  void arm766(uint32_t opcode) { STR_PREDEC_WB(OFFSET_ROR, OP_STRB, 16); }
/* LDRB Rd, [Rn, -Rm, LSL #]! */
static  void arm770(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_LSL, OP_LDRB, 16); }
/* LDRB Rd, [Rn, -Rm, LSR #]! */
static  void arm772(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_LSR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, -Rm, ASR #]! */
static  void arm774(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_ASR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, -Rm, ROR #]! */
static  void arm776(uint32_t opcode) { LDR_PREDEC_WB(OFFSET_ROR, OP_LDRB, 16); }
/* STR Rd, [Rn, Rm, LSL #] */
static  void arm780(uint32_t opcode) { STR_PREINC(OFFSET_LSL, OP_STR, 32); }
/* STR Rd, [Rn, Rm, LSR #] */
static  void arm782(uint32_t opcode) { STR_PREINC(OFFSET_LSR, OP_STR, 32); }
/* STR Rd, [Rn, Rm, ASR #] */
static  void arm784(uint32_t opcode) { STR_PREINC(OFFSET_ASR, OP_STR, 32); }
/* STR Rd, [Rn, Rm, ROR #] */
static  void arm786(uint32_t opcode) { STR_PREINC(OFFSET_ROR, OP_STR, 32); }
/* LDR Rd, [Rn, Rm, LSL #] */
static  void arm790(uint32_t opcode) { LDR_PREINC(OFFSET_LSL, OP_LDR, 32); }
/* LDR Rd, [Rn, Rm, LSR #] */
static  void arm792(uint32_t opcode) { LDR_PREINC(OFFSET_LSR, OP_LDR, 32); }
/* LDR Rd, [Rn, Rm, ASR #] */
static  void arm794(uint32_t opcode) { LDR_PREINC(OFFSET_ASR, OP_LDR, 32); }
/* LDR Rd, [Rn, Rm, ROR #] */
static  void arm796(uint32_t opcode) { LDR_PREINC(OFFSET_ROR, OP_LDR, 32); }
/* STR Rd, [Rn, Rm, LSL #]! */
static  void arm7A0(uint32_t opcode) { STR_PREINC_WB(OFFSET_LSL, OP_STR, 32); }
/* STR Rd, [Rn, Rm, LSR #]! */
static  void arm7A2(uint32_t opcode) { STR_PREINC_WB(OFFSET_LSR, OP_STR, 32); }
/* STR Rd, [Rn, Rm, ASR #]! */
static  void arm7A4(uint32_t opcode) { STR_PREINC_WB(OFFSET_ASR, OP_STR, 32); }
/* STR Rd, [Rn, Rm, ROR #]! */
static  void arm7A6(uint32_t opcode) { STR_PREINC_WB(OFFSET_ROR, OP_STR, 32); }
/* LDR Rd, [Rn, Rm, LSL #]! */
static  void arm7B0(uint32_t opcode) { LDR_PREINC_WB(OFFSET_LSL, OP_LDR, 32); }
/* LDR Rd, [Rn, Rm, LSR #]! */
static  void arm7B2(uint32_t opcode) { LDR_PREINC_WB(OFFSET_LSR, OP_LDR, 32); }
/* LDR Rd, [Rn, Rm, ASR #]! */
static  void arm7B4(uint32_t opcode) { LDR_PREINC_WB(OFFSET_ASR, OP_LDR, 32); }
/* LDR Rd, [Rn, Rm, ROR #]! */
static  void arm7B6(uint32_t opcode) { LDR_PREINC_WB(OFFSET_ROR, OP_LDR, 32); }
/* STRB Rd, [Rn, Rm, LSL #] */
static  void arm7C0(uint32_t opcode) { STR_PREINC(OFFSET_LSL, OP_STRB, 16); }
/* STRB Rd, [Rn, Rm, LSR #] */
static  void arm7C2(uint32_t opcode) { STR_PREINC(OFFSET_LSR, OP_STRB, 16); }
/* STRB Rd, [Rn, Rm, ASR #] */
static  void arm7C4(uint32_t opcode) { STR_PREINC(OFFSET_ASR, OP_STRB, 16); }
/* STRB Rd, [Rn, Rm, ROR #] */
static  void arm7C6(uint32_t opcode) { STR_PREINC(OFFSET_ROR, OP_STRB, 16); }
/* LDRB Rd, [Rn, Rm, LSL #] */
static  void arm7D0(uint32_t opcode) { LDR_PREINC(OFFSET_LSL, OP_LDRB, 16); }
/* LDRB Rd, [Rn, Rm, LSR #] */
static  void arm7D2(uint32_t opcode) { LDR_PREINC(OFFSET_LSR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, Rm, ASR #] */
static  void arm7D4(uint32_t opcode) { LDR_PREINC(OFFSET_ASR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, Rm, ROR #] */
static  void arm7D6(uint32_t opcode) { LDR_PREINC(OFFSET_ROR, OP_LDRB, 16); }
/* STRB Rd, [Rn, Rm, LSL #]! */
static  void arm7E0(uint32_t opcode) { STR_PREINC_WB(OFFSET_LSL, OP_STRB, 16); }
/* STRB Rd, [Rn, Rm, LSR #]! */
static  void arm7E2(uint32_t opcode) { STR_PREINC_WB(OFFSET_LSR, OP_STRB, 16); }
/* STRB Rd, [Rn, Rm, ASR #]! */
static  void arm7E4(uint32_t opcode) { STR_PREINC_WB(OFFSET_ASR, OP_STRB, 16); }
/* STRB Rd, [Rn, Rm, ROR #]! */
static  void arm7E6(uint32_t opcode) { STR_PREINC_WB(OFFSET_ROR, OP_STRB, 16); }
/* LDRB Rd, [Rn, Rm, LSL #]! */
static  void arm7F0(uint32_t opcode) { LDR_PREINC_WB(OFFSET_LSL, OP_LDRB, 16); }
/* LDRB Rd, [Rn, Rm, LSR #]! */
static  void arm7F2(uint32_t opcode) { LDR_PREINC_WB(OFFSET_LSR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, Rm, ASR #]! */
static  void arm7F4(uint32_t opcode) { LDR_PREINC_WB(OFFSET_ASR, OP_LDRB, 16); }
/* LDRB Rd, [Rn, Rm, ROR #]! */
static  void arm7F6(uint32_t opcode) { LDR_PREINC_WB(OFFSET_ROR, OP_LDRB, 16); }

/* STM/LDM //////////////////////////////////////////////////////////////// */

/* Portable count-trailing-zeros for a uint32_t. Each LDM/STM iterates over
 * the set bits of the register list (16-bit field in the opcode), pulling
 * the lowest set bit each step.  list is never zero at the call site (the
 * while-loop guards it), so the undefined-for-zero case can't arise. */
#if defined(__GNUC__) || defined(__clang__)
#define CTZ_U32(x) __builtin_ctz((unsigned int)(x))
#elif defined(_MSC_VER)
#include <intrin.h>
#pragma intrinsic(_BitScanForward)
static INLINE int _ctz_u32_msvc(uint32_t x)
{
    unsigned long idx;
    _BitScanForward(&idx, x);
    return (int)idx;
}
#define CTZ_U32(x) _ctz_u32_msvc((uint32_t)(x))
#else
static INLINE int _ctz_u32_fallback(uint32_t x)
{
    int n = 0;
    while (!(x & 1u)) { x >>= 1; n++; }
    return n;
}
#define CTZ_U32(x) _ctz_u32_fallback((uint32_t)(x))
#endif

/* Single-register bus access bodies, used inside the loops below.  The
 * timing logic (`count ? SEQ : NSEQ`) preserves the first-N-then-S access
 * pattern that the ARM7TDMI prefetcher would produce. */
#define LDM_LOAD_ONE(reg_idx) do { \
        int dataticks_value; \
        bus.reg[(reg_idx)].I = CPUReadMemory(address); \
        dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) \
                                : DATATICKS_ACCESS_32BIT(address); \
        DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
        clockTicks += 1 + dataticks_value; \
        count++; \
        address += 4; \
    } while (0)

#define STM_STORE_ONE(reg_idx) do { \
        int dataticks_value; \
        CPUWriteMemory(address, bus.reg[(reg_idx)].I); \
        dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) \
                                : DATATICKS_ACCESS_32BIT(address); \
        DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
        clockTicks += 1 + dataticks_value; \
        count++; \
        address += 4; \
    } while (0)

#define STMW_STORE_ONE(reg_idx) do { \
        int dataticks_value; \
        CPUWriteMemory(address, bus.reg[(reg_idx)].I); \
        dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) \
                                : DATATICKS_ACCESS_32BIT(address); \
        DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
        clockTicks += 1 + dataticks_value; \
        bus.reg[base].I = temp; \
        count++; \
        address += 4; \
    } while (0)

/* Iterate bits 0..7 of the register list -> regs 0..7 (no remap). */
#define LDM_LOW \
    do { uint32_t _list = opcode & 0xFFu; \
         while (_list) { LDM_LOAD_ONE(CTZ_U32(_list)); _list &= _list - 1u; } \
    } while (0)

/* Iterate bits 8..14 of the register list -> regs 8..14 (no remap). */
#define LDM_HIGH \
    do { uint32_t _list = (opcode >> 8) & 0x7Fu; \
         while (_list) { LDM_LOAD_ONE(CTZ_U32(_list) + 8); _list &= _list - 1u; } \
    } while (0)

/* Iterate bits 8..14 with S-bit semantics: r8-r12 come from FIQ-banked regs
 * when in FIQ mode, r13/r14 come from USR-banked regs when not in USR/SYS.
 * Build a 7-entry mapping once, then loop. */
#define LDM_HIGH_2 \
    do { uint8_t _map[7]; uint32_t _list = (opcode >> 8) & 0x7Fu; \
        if (armMode == 0x11) { \
            _map[0] = R8_FIQ;  _map[1] = R9_FIQ;  _map[2] = R10_FIQ; \
            _map[3] = R11_FIQ; _map[4] = R12_FIQ; \
        } else { \
            _map[0] = 8;  _map[1] = 9;  _map[2] = 10; \
            _map[3] = 11; _map[4] = 12; \
        } \
        if (armMode != 0x10 && armMode != 0x1F) { \
            _map[5] = R13_USR; _map[6] = R14_USR; \
        } else { \
            _map[5] = 13; _map[6] = 14; \
        } \
        while (_list) { int _b = CTZ_U32(_list); \
            LDM_LOAD_ONE(_map[_b]); _list &= _list - 1u; } \
    } while (0)

/* STM variants without write-back. */
#define STM_LOW \
    do { uint32_t _list = opcode & 0xFFu; \
         while (_list) { STM_STORE_ONE(CTZ_U32(_list)); _list &= _list - 1u; } \
    } while (0)

#define STM_HIGH \
    do { uint32_t _list = (opcode >> 8) & 0x7Fu; \
         while (_list) { STM_STORE_ONE(CTZ_U32(_list) + 8); _list &= _list - 1u; } \
    } while (0)

#define STM_HIGH_2 \
    do { uint8_t _map[7]; uint32_t _list = (opcode >> 8) & 0x7Fu; \
        if (armMode == 0x11) { \
            _map[0] = R8_FIQ;  _map[1] = R9_FIQ;  _map[2] = R10_FIQ; \
            _map[3] = R11_FIQ; _map[4] = R12_FIQ; \
        } else { \
            _map[0] = 8;  _map[1] = 9;  _map[2] = 10; \
            _map[3] = 11; _map[4] = 12; \
        } \
        if (armMode != 0x10 && armMode != 0x1F) { \
            _map[5] = R13_USR; _map[6] = R14_USR; \
        } else { \
            _map[5] = 13; _map[6] = 14; \
        } \
        while (_list) { int _b = CTZ_U32(_list); \
            STM_STORE_ONE(_map[_b]); _list &= _list - 1u; } \
    } while (0)

/* STM variants with per-iteration write-back of `temp` to base register.
 * Mirrors STMW_REG: temp is idempotent across iters but the write makes
 * "base in list and not lowest" store the written-back value, matching
 * ARMv4 semantics. */
#define STMW_LOW \
    do { uint32_t _list = opcode & 0xFFu; \
         while (_list) { STMW_STORE_ONE(CTZ_U32(_list)); _list &= _list - 1u; } \
    } while (0)

#define STMW_HIGH \
    do { uint32_t _list = (opcode >> 8) & 0x7Fu; \
         while (_list) { STMW_STORE_ONE(CTZ_U32(_list) + 8); _list &= _list - 1u; } \
    } while (0)

#define STMW_HIGH_2 \
    do { uint8_t _map[7]; uint32_t _list = (opcode >> 8) & 0x7Fu; \
        if (armMode == 0x11) { \
            _map[0] = R8_FIQ;  _map[1] = R9_FIQ;  _map[2] = R10_FIQ; \
            _map[3] = R11_FIQ; _map[4] = R12_FIQ; \
        } else { \
            _map[0] = 8;  _map[1] = 9;  _map[2] = 10; \
            _map[3] = 11; _map[4] = 12; \
        } \
        if (armMode != 0x10 && armMode != 0x1F) { \
            _map[5] = R13_USR; _map[6] = R14_USR; \
        } else { \
            _map[5] = 13; _map[6] = 14; \
        } \
        while (_list) { int _b = CTZ_U32(_list); \
            STMW_STORE_ONE(_map[_b]); _list &= _list - 1u; } \
    } while (0)

#define STM_PC \
    if (opcode & (1U<<15)) {                            \
        int dataticks_value;                            \
        CPUWriteMemory(address, bus.reg[15].I+4);           \
	dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
    }
#define STMW_PC \
    if (opcode & (1U<<15)) {                            \
        int dataticks_value;                            \
        CPUWriteMemory(address, bus.reg[15].I+4);           \
	dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        bus.reg[base].I = temp;                             \
        count++;                                        \
    }
#define STM_ALL \
    STM_LOW;                                            \
    STM_HIGH;                                           \
    STM_PC;
#define STMW_ALL \
    STMW_LOW;                                           \
    STMW_HIGH;                                          \
    STMW_PC;
#define LDM_ALL \
    LDM_LOW;                                            \
    LDM_HIGH;                                           \
    if (opcode & (1U<<15)) {                            \
        int dataticks_value;                            \
        bus.reg[15].I = CPUReadMemory(address);             \
	dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
    }                                                   \
    if (opcode & (1U<<15)) {                            \
        bus.armNextPC = bus.reg[15].I;                          \
        bus.reg[15].I += 4;                                 \
        ARM_PREFETCH;                                   \
        clockTicks += CLOCKTICKS_UPDATE_TYPE32;\
    }
#define STM_ALL_2 \
    STM_LOW;                                            \
    STM_HIGH_2;                                         \
    STM_PC;
#define STMW_ALL_2 \
    STMW_LOW;                                           \
    STMW_HIGH_2;                                        \
    STMW_PC;
#define LDM_ALL_2 \
    LDM_LOW;                                            \
    if (opcode & (1U<<15)) {                            \
        int dataticks_value;                            \
        LDM_HIGH;                                       \
        bus.reg[15].I = CPUReadMemory(address);             \
	dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
    } else {                                            \
        LDM_HIGH_2;                                     \
    }
#define LDM_ALL_2B \
    if (opcode & (1U<<15)) {                            \
	if(armMode != (bus.reg[17].I & 0x1F)) \
	    CPUSwitchMode(bus.reg[17].I & 0x1F, false, true);   \
        if (armState) {                                 \
            bus.armNextPC = bus.reg[15].I & 0xFFFFFFFC;         \
            bus.reg[15].I = bus.armNextPC + 4;                  \
            ARM_PREFETCH;                               \
        } else {                                        \
            bus.armNextPC = bus.reg[15].I & 0xFFFFFFFE;         \
            bus.reg[15].I = bus.armNextPC + 2;                  \
            THUMB_PREFETCH;                             \
        }                                               \
        clockTicks += CLOCKTICKS_UPDATE_TYPE32;\
    }


/* STMDA Rn, {Rlist} */
static  void arm800(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp + 4) & 0xFFFFFFFC;
    count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDA Rn, {Rlist} */
static  void arm810(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp + 4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMDA Rn!, {Rlist} */
static  void arm820(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp+4) & 0xFFFFFFFC;
    count = 0;
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDA Rn!, {Rlist} */
static  void arm830(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp + 4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

/* STMDA Rn, {Rlist}^ */
static  void arm840(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp+4) & 0xFFFFFFFC;
    count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDA Rn, {Rlist}^ */
static  void arm850(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp + 4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMDA Rn!, {Rlist}^ */
static  void arm860(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp+4) & 0xFFFFFFFC;
    count = 0;
    STMW_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDA Rn!, {Rlist}^ */
static  void arm870(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (temp + 4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMIA Rn, {Rlist} */
static  void arm880(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIA Rn, {Rlist} */
static  void arm890(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMIA Rn!, {Rlist} */
static  void arm8A0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    uint32_t temp;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIA Rn!, {Rlist} */
static  void arm8B0(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

/* STMIA Rn, {Rlist}^ */
static  void arm8C0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIA Rn, {Rlist}^ */
static  void arm8D0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMIA Rn!, {Rlist}^ */
static  void arm8E0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    uint32_t temp;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
    STMW_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIA Rn!, {Rlist}^ */
static  void arm8F0(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = bus.reg[base].I & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMDB Rn, {Rlist} */
static  void arm900(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDB Rn, {Rlist} */
static  void arm910(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMDB Rn!, {Rlist} */
static  void arm920(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDB Rn!, {Rlist} */
static  void arm930(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

/* STMDB Rn, {Rlist}^ */
static  void arm940(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDB Rn, {Rlist}^ */
static  void arm950(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMDB Rn!, {Rlist}^ */
static  void arm960(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    STMW_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMDB Rn!, {Rlist}^ */
static  void arm970(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = temp & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMIB Rn, {Rlist} */
static  void arm980(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIB Rn, {Rlist} */
static  void arm990(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMIB Rn!, {Rlist} */
static  void arm9A0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    uint32_t temp;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    count = 0;
    temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIB Rn!, {Rlist} */
static  void arm9B0(uint32_t opcode)
{
    int base;
    uint32_t temp;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

/* STMIB Rn, {Rlist}^ */
static  void arm9C0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIB Rn, {Rlist}^ */
static  void arm9D0(uint32_t opcode)
{
    int base;
    uint32_t address;
    int count;
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    base = (opcode & 0x000F0000) >> 16;
    address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* STMIB Rn!, {Rlist}^ */
static  void arm9E0(uint32_t opcode)
{
	int base;
	uint32_t address;
	int count;
	uint32_t temp;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	base = (opcode & 0x000F0000) >> 16;
	address = (bus.reg[base].I+4) & 0xFFFFFFFC;
	count = 0;
	temp = bus.reg[base].I +
		4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
	STMW_ALL_2;
	clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* LDMIB Rn!, {Rlist}^ */
static  void arm9F0(uint32_t opcode)
{
	int base;
	uint32_t temp;
	uint32_t address;
	int count;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	base = (opcode & 0x000F0000) >> 16;
	temp = bus.reg[base].I +
		4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
	address = (bus.reg[base].I+4) & 0xFFFFFFFC;
	count = 0;
	LDM_ALL_2;
	if (!(opcode & (1U << base)))
		bus.reg[base].I = temp;
	LDM_ALL_2B;
	clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

/* B/BL/SWI and (unimplemented) coproc support //////////////////////////// */

/* B <offset> */
static  void armA00(uint32_t opcode)
{
	int offset = opcode & 0x00FFFFFF;
	if (offset & 0x00800000)
		offset |= 0xFF000000;  /* negative offset */
	bus.reg[15].I += offset<<2;
	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;
	ARM_PREFETCH;

	clockTicks = CLOCKTICKS_UPDATE_TYPE32P;
	bus.busPrefetchCount = 0;
}

/* BL <offset> */
static  void armB00(uint32_t opcode)
{
	int offset = opcode & 0x00FFFFFF;
	if (offset & 0x00800000)
		offset |= 0xFF000000;  /* negative offset */
	bus.reg[14].I = bus.reg[15].I - 4;
	bus.reg[15].I += offset<<2;
	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;
	ARM_PREFETCH;

	clockTicks = CLOCKTICKS_UPDATE_TYPE32P;
	bus.busPrefetchCount = 0;
}

#define armE01 armUnknownInsn

/* SWI <comment> */
static  void armF00(uint32_t opcode)
{
	clockTicks = CLOCKTICKS_UPDATE_TYPE32P;
	bus.busPrefetchCount = 0;
	CPUSoftwareInterrupt(opcode & 0x00FFFFFF);
}

/* Instruction table ////////////////////////////////////////////////////// */

typedef  void (*insnfunc_t)(uint32_t opcode);
#define REP16(insn) \
    insn,insn,insn,insn,insn,insn,insn,insn,\
    insn,insn,insn,insn,insn,insn,insn,insn
#define REP256(insn) \
    REP16(insn),REP16(insn),REP16(insn),REP16(insn),\
    REP16(insn),REP16(insn),REP16(insn),REP16(insn),\
    REP16(insn),REP16(insn),REP16(insn),REP16(insn),\
    REP16(insn),REP16(insn),REP16(insn),REP16(insn)
#define arm_UI armUnknownInsn
#define arm_BP armUnknownInsn

static insnfunc_t armInsnTable[4096] =
{
    arm000,arm001,arm002,arm003,arm004,arm005,arm006,arm007,  /* 000 */
    arm000,arm009,arm002,arm00B,arm004,arm_UI,arm006,arm_UI,  /* 008 */
    arm010,arm011,arm012,arm013,arm014,arm015,arm016,arm017,  /* 010 */
    arm010,arm019,arm012,arm01B,arm014,arm01D,arm016,arm01F,  /* 018 */
    arm020,arm021,arm022,arm023,arm024,arm025,arm026,arm027,  /* 020 */
    arm020,arm029,arm022,arm_UI,arm024,arm_UI,arm026,arm_UI,  /* 028 */
    arm030,arm031,arm032,arm033,arm034,arm035,arm036,arm037,  /* 030 */
    arm030,arm039,arm032,arm_UI,arm034,arm01D,arm036,arm01F,  /* 038 */
    arm040,arm041,arm042,arm043,arm044,arm045,arm046,arm047,  /* 040 */
    arm040,arm_UI,arm042,arm04B,arm044,arm_UI,arm046,arm_UI,  /* 048 */
    arm050,arm051,arm052,arm053,arm054,arm055,arm056,arm057,  /* 050 */
    arm050,arm_UI,arm052,arm05B,arm054,arm05D,arm056,arm05F,  /* 058 */
    arm060,arm061,arm062,arm063,arm064,arm065,arm066,arm067,  /* 060 */
    arm060,arm_UI,arm062,arm_UI,arm064,arm_UI,arm066,arm_UI,  /* 068 */
    arm070,arm071,arm072,arm073,arm074,arm075,arm076,arm077,  /* 070 */
    arm070,arm_UI,arm072,arm_UI,arm074,arm05D,arm076,arm05F,  /* 078 */
    arm080,arm081,arm082,arm083,arm084,arm085,arm086,arm087,  /* 080 */
    arm080,arm089,arm082,arm08B,arm084,arm_UI,arm086,arm_UI,  /* 088 */
    arm090,arm091,arm092,arm093,arm094,arm095,arm096,arm097,  /* 090 */
    arm090,arm099,arm092,arm09B,arm094,arm09D,arm096,arm09F,  /* 098 */
    arm0A0,arm0A1,arm0A2,arm0A3,arm0A4,arm0A5,arm0A6,arm0A7,  /* 0A0 */
    arm0A0,arm0A9,arm0A2,arm_UI,arm0A4,arm_UI,arm0A6,arm_UI,  /* 0A8 */
    arm0B0,arm0B1,arm0B2,arm0B3,arm0B4,arm0B5,arm0B6,arm0B7,  /* 0B0 */
    arm0B0,arm0B9,arm0B2,arm_UI,arm0B4,arm09D,arm0B6,arm09F,  /* 0B8 */
    arm0C0,arm0C1,arm0C2,arm0C3,arm0C4,arm0C5,arm0C6,arm0C7,  /* 0C0 */
    arm0C0,arm0C9,arm0C2,arm0CB,arm0C4,arm_UI,arm0C6,arm_UI,  /* 0C8 */
    arm0D0,arm0D1,arm0D2,arm0D3,arm0D4,arm0D5,arm0D6,arm0D7,  /* 0D0 */
    arm0D0,arm0D9,arm0D2,arm0DB,arm0D4,arm0DD,arm0D6,arm0DF,  /* 0D8 */
    arm0E0,arm0E1,arm0E2,arm0E3,arm0E4,arm0E5,arm0E6,arm0E7,  /* 0E0 */
    arm0E0,arm0E9,arm0E2,arm0CB,arm0E4,arm_UI,arm0E6,arm_UI,  /* 0E8 */
    arm0F0,arm0F1,arm0F2,arm0F3,arm0F4,arm0F5,arm0F6,arm0F7,  /* 0F0 */
    arm0F0,arm0F9,arm0F2,arm0DB,arm0F4,arm0DD,arm0F6,arm0DF,  /* 0F8 */

    arm100,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,  /* 100 */
    arm_UI,arm109,arm_UI,arm10B,arm_UI,arm_UI,arm_UI,arm_UI,  /* 108 */
    arm110,arm111,arm112,arm113,arm114,arm115,arm116,arm117,  /* 110 */
    arm110,arm_UI,arm112,arm11B,arm114,arm11D,arm116,arm11F,  /* 118 */
    arm120,arm121,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_BP,  /* 120 */
    arm_UI,arm_UI,arm_UI,arm12B,arm_UI,arm_UI,arm_UI,arm_UI,  /* 128 */
    arm130,arm131,arm132,arm133,arm134,arm135,arm136,arm137,  /* 130 */
    arm130,arm_UI,arm132,arm13B,arm134,arm13D,arm136,arm13F,  /* 138 */
    arm140,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,  /* 140 */
    arm_UI,arm149,arm_UI,arm14B,arm_UI,arm_UI,arm_UI,arm_UI,  /* 148 */
    arm150,arm151,arm152,arm153,arm154,arm155,arm156,arm157,  /* 150 */
    arm150,arm_UI,arm152,arm15B,arm154,arm15D,arm156,arm15F,  /* 158 */
    arm160,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,  /* 160 */
    arm_UI,arm_UI,arm_UI,arm16B,arm_UI,arm_UI,arm_UI,arm_UI,  /* 168 */
    arm170,arm171,arm172,arm173,arm174,arm175,arm176,arm177,  /* 170 */
    arm170,arm_UI,arm172,arm17B,arm174,arm17D,arm176,arm17F,  /* 178 */
    arm180,arm181,arm182,arm183,arm184,arm185,arm186,arm187,  /* 180 */
    arm180,arm_UI,arm182,arm18B,arm184,arm_UI,arm186,arm_UI,  /* 188 */
    arm190,arm191,arm192,arm193,arm194,arm195,arm196,arm197,  /* 190 */
    arm190,arm_UI,arm192,arm19B,arm194,arm19D,arm196,arm19F,  /* 198 */
    arm1A0,arm1A1,arm1A2,arm1A3,arm1A4,arm1A5,arm1A6,arm1A7,  /* 1A0 */
    arm1A0,arm_UI,arm1A2,arm1AB,arm1A4,arm_UI,arm1A6,arm_UI,  /* 1A8 */
    arm1B0,arm1B1,arm1B2,arm1B3,arm1B4,arm1B5,arm1B6,arm1B7,  /* 1B0 */
    arm1B0,arm_UI,arm1B2,arm1BB,arm1B4,arm1BD,arm1B6,arm1BF,  /* 1B8 */
    arm1C0,arm1C1,arm1C2,arm1C3,arm1C4,arm1C5,arm1C6,arm1C7,  /* 1C0 */
    arm1C0,arm_UI,arm1C2,arm1CB,arm1C4,arm_UI,arm1C6,arm_UI,  /* 1C8 */
    arm1D0,arm1D1,arm1D2,arm1D3,arm1D4,arm1D5,arm1D6,arm1D7,  /* 1D0 */
    arm1D0,arm_UI,arm1D2,arm1DB,arm1D4,arm1DD,arm1D6,arm1DF,  /* 1D8 */
    arm1E0,arm1E1,arm1E2,arm1E3,arm1E4,arm1E5,arm1E6,arm1E7,  /* 1E0 */
    arm1E0,arm_UI,arm1E2,arm1EB,arm1E4,arm_UI,arm1E6,arm_UI,  /* 1E8 */
    arm1F0,arm1F1,arm1F2,arm1F3,arm1F4,arm1F5,arm1F6,arm1F7,  /* 1F0 */
    arm1F0,arm_UI,arm1F2,arm1FB,arm1F4,arm1FD,arm1F6,arm1FF,  /* 1F8 */

    REP16(arm200),REP16(arm210),REP16(arm220),REP16(arm230),  /* 200 */
    REP16(arm240),REP16(arm250),REP16(arm260),REP16(arm270),  /* 240 */
    REP16(arm280),REP16(arm290),REP16(arm2A0),REP16(arm2B0),  /* 280 */
    REP16(arm2C0),REP16(arm2D0),REP16(arm2E0),REP16(arm2F0),  /* 2C0 */
    REP16(arm_UI),REP16(arm310),REP16(arm320),REP16(arm330),  /* 300 */
    REP16(arm_UI),REP16(arm350),REP16(arm360),REP16(arm370),  /* 340 */
    REP16(arm380),REP16(arm390),REP16(arm3A0),REP16(arm3B0),  /* 380 */
    REP16(arm3C0),REP16(arm3D0),REP16(arm3E0),REP16(arm3F0),  /* 3C0 */

    REP16(arm400),REP16(arm410),REP16(arm400),REP16(arm410),  /* 400 */
    REP16(arm440),REP16(arm450),REP16(arm440),REP16(arm450),  /* 440 */
    REP16(arm480),REP16(arm490),REP16(arm480),REP16(arm490),  /* 480 */
    REP16(arm4C0),REP16(arm4D0),REP16(arm4C0),REP16(arm4D0),  /* 4C0 */
    REP16(arm500),REP16(arm510),REP16(arm520),REP16(arm530),  /* 500 */
    REP16(arm540),REP16(arm550),REP16(arm560),REP16(arm570),  /* 540 */
    REP16(arm580),REP16(arm590),REP16(arm5A0),REP16(arm5B0),  /* 580 */
    REP16(arm5C0),REP16(arm5D0),REP16(arm5E0),REP16(arm5F0),  /* 5C0 */

    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  /* 600 */
    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  /* 608 */
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  /* 610 */
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  /* 618 */
    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  /* 620 */
    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  /* 628 */
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  /* 630 */
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  /* 638 */
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  /* 640 */
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  /* 648 */
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  /* 650 */
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  /* 658 */
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  /* 660 */
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  /* 668 */
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  /* 670 */
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  /* 678 */
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  /* 680 */
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  /* 688 */
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  /* 690 */
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  /* 698 */
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  /* 6A0 */
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  /* 6A8 */
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  /* 6B0 */
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  /* 6B8 */
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  /* 6C0 */
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  /* 6C8 */
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  /* 6D0 */
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  /* 6D8 */
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  /* 6E0 */
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  /* 6E8 */
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  /* 6F0 */
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  /* 6F8 */

    arm700,arm_UI,arm702,arm_UI,arm704,arm_UI,arm706,arm_UI,  /* 700 */
    arm700,arm_UI,arm702,arm_UI,arm704,arm_UI,arm706,arm_UI,  /* 708 */
    arm710,arm_UI,arm712,arm_UI,arm714,arm_UI,arm716,arm_UI,  /* 710 */
    arm710,arm_UI,arm712,arm_UI,arm714,arm_UI,arm716,arm_UI,  /* 718 */
    arm720,arm_UI,arm722,arm_UI,arm724,arm_UI,arm726,arm_UI,  /* 720 */
    arm720,arm_UI,arm722,arm_UI,arm724,arm_UI,arm726,arm_UI,  /* 728 */
    arm730,arm_UI,arm732,arm_UI,arm734,arm_UI,arm736,arm_UI,  /* 730 */
    arm730,arm_UI,arm732,arm_UI,arm734,arm_UI,arm736,arm_UI,  /* 738 */
    arm740,arm_UI,arm742,arm_UI,arm744,arm_UI,arm746,arm_UI,  /* 740 */
    arm740,arm_UI,arm742,arm_UI,arm744,arm_UI,arm746,arm_UI,  /* 748 */
    arm750,arm_UI,arm752,arm_UI,arm754,arm_UI,arm756,arm_UI,  /* 750 */
    arm750,arm_UI,arm752,arm_UI,arm754,arm_UI,arm756,arm_UI,  /* 758 */
    arm760,arm_UI,arm762,arm_UI,arm764,arm_UI,arm766,arm_UI,  /* 760 */
    arm760,arm_UI,arm762,arm_UI,arm764,arm_UI,arm766,arm_UI,  /* 768 */
    arm770,arm_UI,arm772,arm_UI,arm774,arm_UI,arm776,arm_UI,  /* 770 */
    arm770,arm_UI,arm772,arm_UI,arm774,arm_UI,arm776,arm_UI,  /* 778 */
    arm780,arm_UI,arm782,arm_UI,arm784,arm_UI,arm786,arm_UI,  /* 780 */
    arm780,arm_UI,arm782,arm_UI,arm784,arm_UI,arm786,arm_UI,  /* 788 */
    arm790,arm_UI,arm792,arm_UI,arm794,arm_UI,arm796,arm_UI,  /* 790 */
    arm790,arm_UI,arm792,arm_UI,arm794,arm_UI,arm796,arm_UI,  /* 798 */
    arm7A0,arm_UI,arm7A2,arm_UI,arm7A4,arm_UI,arm7A6,arm_UI,  /* 7A0 */
    arm7A0,arm_UI,arm7A2,arm_UI,arm7A4,arm_UI,arm7A6,arm_UI,  /* 7A8 */
    arm7B0,arm_UI,arm7B2,arm_UI,arm7B4,arm_UI,arm7B6,arm_UI,  /* 7B0 */
    arm7B0,arm_UI,arm7B2,arm_UI,arm7B4,arm_UI,arm7B6,arm_UI,  /* 7B8 */
    arm7C0,arm_UI,arm7C2,arm_UI,arm7C4,arm_UI,arm7C6,arm_UI,  /* 7C0 */
    arm7C0,arm_UI,arm7C2,arm_UI,arm7C4,arm_UI,arm7C6,arm_UI,  /* 7C8 */
    arm7D0,arm_UI,arm7D2,arm_UI,arm7D4,arm_UI,arm7D6,arm_UI,  /* 7D0 */
    arm7D0,arm_UI,arm7D2,arm_UI,arm7D4,arm_UI,arm7D6,arm_UI,  /* 7D8 */
    arm7E0,arm_UI,arm7E2,arm_UI,arm7E4,arm_UI,arm7E6,arm_UI,  /* 7E0 */
    arm7E0,arm_UI,arm7E2,arm_UI,arm7E4,arm_UI,arm7E6,arm_UI,  /* 7E8 */
    arm7F0,arm_UI,arm7F2,arm_UI,arm7F4,arm_UI,arm7F6,arm_UI,  /* 7F0 */
    arm7F0,arm_UI,arm7F2,arm_UI,arm7F4,arm_UI,arm7F6,arm_BP,  /* 7F8 */

    REP16(arm800),REP16(arm810),REP16(arm820),REP16(arm830),  /* 800 */
    REP16(arm840),REP16(arm850),REP16(arm860),REP16(arm870),  /* 840 */
    REP16(arm880),REP16(arm890),REP16(arm8A0),REP16(arm8B0),  /* 880 */
    REP16(arm8C0),REP16(arm8D0),REP16(arm8E0),REP16(arm8F0),  /* 8C0 */
    REP16(arm900),REP16(arm910),REP16(arm920),REP16(arm930),  /* 900 */
    REP16(arm940),REP16(arm950),REP16(arm960),REP16(arm970),  /* 940 */
    REP16(arm980),REP16(arm990),REP16(arm9A0),REP16(arm9B0),  /* 980 */
    REP16(arm9C0),REP16(arm9D0),REP16(arm9E0),REP16(arm9F0),  /* 9C0 */

    REP256(armA00),                                           /* A00 */
    REP256(armB00),                                           /* B00 */
    REP256(arm_UI),                                           /* C00 */
    REP256(arm_UI),                                           /* D00 */

    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  /* E00 */
    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  /* E08 */
    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  /* E10 */
    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  /* E18 */
    REP16(arm_UI),                                            /* E20 */
    REP16(arm_UI),                                            /* E30 */
    REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),  /* E40 */
    REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),  /* E80 */
    REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),  /* EC0 */

    REP256(armF00),                                           /* F00 */
};

/* Emulates the Cheat System (m) code */
static INLINE void cpuMasterCodeCheck(void)
{
   if((mastercode) && (mastercode == bus.armNextPC))
   {
      uint32_t ext = (joy >> 10);
      cpuTotalTicks += cheatsCheckKeys(io_registers[REG_P1]^0x3FF, ext);
   }
}

/* Wrapper routine (execution loop) /////////////////////////////////////// */
static int armExecute (void)
{
   int ct    = 0;
   bool test = false;
    uint32_t cond1 = 0;
	uint32_t cond2 = 0;

	CACHE_PREFETCH(clockTicks);

	do
   {
uint32_t opcode;
int32_t busprefetch_mask;
int oldArmNextPC;
int cond;
bool cond_res;

      clockTicks = 0;

#if USE_CHEATS
      cpuMasterCodeCheck();
#endif

      if ((bus.armNextPC & 0x0803FFFF) == 0x08020000)
         bus.busPrefetchCount = 0x100;

      opcode = cpuPrefetch[0];
      cpuPrefetch[0] = cpuPrefetch[1];

      bus.busPrefetch = false;
      busprefetch_mask = ((bus.busPrefetchCount & 0xFFFFFE00) | -(bus.busPrefetchCount & 0xFFFFFE00)) >> 31;
      bus.busPrefetchCount = ((0x100 | (bus.busPrefetchCount & 0xFF)) & busprefetch_mask) | (bus.busPrefetchCount & ~busprefetch_mask);


      oldArmNextPC = bus.armNextPC;

      bus.armNextPC = bus.reg[15].I;
      bus.reg[15].I += 4;
      ARM_PREFETCH_NEXT;

      cond = opcode >> 28;
      cond_res = true;
      if (cond != 0x0E) {  /* most opcodes are AL (always) */
         switch(cond) {
            case 0x00: /* EQ */
               cond_res = Z_FLAG;
               break;
            case 0x01: /* NE */
               cond_res = !Z_FLAG;
               break;
            case 0x02: /* CS */
               cond_res = C_FLAG;
               break;
            case 0x03: /* CC */
               cond_res = !C_FLAG;
               break;
            case 0x04: /* MI */
               cond_res = N_FLAG;
               break;
            case 0x05: /* PL */
               cond_res = !N_FLAG;
               break;
            case 0x06: /* VS */
               cond_res = V_FLAG;
               break;
            case 0x07: /* VC */
               cond_res = !V_FLAG;
               break;
            case 0x08: /* HI */
               cond_res = C_FLAG && !Z_FLAG;
               break;
            case 0x09: /* LS */
               cond_res = !C_FLAG || Z_FLAG;
               break;
            case 0x0A: /* GE */
               cond_res = N_FLAG == V_FLAG;
               break;
            case 0x0B: /* LT */
               cond_res = N_FLAG != V_FLAG;
               break;
            case 0x0C: /* GT */
               cond_res = !Z_FLAG &&(N_FLAG == V_FLAG);
               break;
            case 0x0D: /* LE */
               cond_res = Z_FLAG || (N_FLAG != V_FLAG);
               break;
            case 0x0E: /* AL (impossible, checked above) */
               cond_res = true;
               break;
            case 0x0F:
            default:
               /* ??? */
               cond_res = false;
               break;
         }
      }

      if (cond_res)
      {
         cond1 = (opcode>>16)&0xFF0;
         cond2 = (opcode>>4)&0x0F;

         (*armInsnTable[(cond1| cond2)])(opcode);

      }
      ct = clockTicks;

      if (ct < 0)
         return 0;

      /*/ better pipelining */

      if (ct == 0)
         clockTicks = 1 + codeTicksAccessSeq32(oldArmNextPC);

      cpuTotalTicks += clockTicks;

      test = cpuTotalTicks < cpuNextEvent && armState && !holdState;
   }while (test);

	return 1;
}

/*============================================================
	GBA THUMB CORE
============================================================ */

static  void thumbUnknownInsn(uint32_t opcode)
{
	uint32_t PC = bus.reg[15].I;
	bool savedArmState = armState;
	if(armMode != 0x1b)
		CPUSwitchMode(0x1b, true, false);
	bus.reg[14].I = PC - (savedArmState ? 4 : 2);
	bus.reg[15].I = 0x04;
	armState = true;
	armIrqEnable = false;
	bus.armNextPC = 0x04;
	ARM_PREFETCH;
	bus.reg[15].I += 4;
}

#define NEG(i) ((i) >> 31)
#define POS(i) ((~(i)) >> 31)

/* C core */
#ifndef ADDCARRY
 #define ADDCARRY(a, b, c) \
  C_FLAG = ((NEG(a) & NEG(b)) |\
            (NEG(a) & POS(c)) |\
            (NEG(b) & POS(c))) ? true : false;
#endif

#ifndef ADDOVERFLOW
 #define ADDOVERFLOW(a, b, c) \
  V_FLAG = ((NEG(a) & NEG(b) & POS(c)) |\
            (POS(a) & POS(b) & NEG(c))) ? true : false;
#endif

#ifndef SUBCARRY
 #define SUBCARRY(a, b, c) \
  C_FLAG = ((NEG(a) & POS(b)) |\
            (NEG(a) & POS(c)) |\
            (POS(b) & POS(c))) ? true : false;
#endif

#ifndef SUBOVERFLOW
 #define SUBOVERFLOW(a, b, c)\
  V_FLAG = ((NEG(a) & POS(b) & POS(c)) |\
            (POS(a) & NEG(b) & NEG(c))) ? true : false;
#endif

#ifndef ADD_RD_RS_RN
 #define ADD_RD_RS_RN(N) \
   {\
     uint32_t lhs = bus.reg[source].I;\
     uint32_t rhs = bus.reg[N].I;\
     uint32_t res = lhs + rhs;\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     ADDCARRY(lhs, rhs, res);\
     ADDOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef ADD_RD_RS_O3
 #define ADD_RD_RS_O3(N) \
   {\
     uint32_t lhs = bus.reg[source].I;\
     uint32_t rhs = N;\
     uint32_t res = lhs + rhs;\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     ADDCARRY(lhs, rhs, res);\
     ADDOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef ADD_RD_RS_O3_0
# define ADD_RD_RS_O3_0 ADD_RD_RS_O3
#endif

#ifndef ADD_RN_O8
 #define ADD_RN_O8(d) \
   {\
     uint32_t lhs = bus.reg[(d)].I;\
     uint32_t rhs = (opcode & 255);\
     uint32_t res = lhs + rhs;\
     bus.reg[(d)].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     ADDCARRY(lhs, rhs, res);\
     ADDOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef CMN_RD_RS
 #define CMN_RD_RS \
   {\
     uint32_t lhs = bus.reg[dest].I;\
     uint32_t rhs = value;\
     uint32_t res = lhs + rhs;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     ADDCARRY(lhs, rhs, res);\
     ADDOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef ADC_RD_RS
 #define ADC_RD_RS \
   {\
     uint32_t lhs = bus.reg[dest].I;\
     uint32_t rhs = value;\
     uint32_t res = lhs + rhs + (uint32_t)C_FLAG;\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     ADDCARRY(lhs, rhs, res);\
     ADDOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef SUB_RD_RS_RN
 #define SUB_RD_RS_RN(N) \
   {\
     uint32_t lhs = bus.reg[source].I;\
     uint32_t rhs = bus.reg[N].I;\
     uint32_t res = lhs - rhs;\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef SUB_RD_RS_O3
 #define SUB_RD_RS_O3(N) \
   {\
     uint32_t lhs = bus.reg[source].I;\
     uint32_t rhs = N;\
     uint32_t res = lhs - rhs;\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef SUB_RD_RS_O3_0
# define SUB_RD_RS_O3_0 SUB_RD_RS_O3
#endif
#ifndef SUB_RN_O8
 #define SUB_RN_O8(d) \
   {\
     uint32_t lhs = bus.reg[(d)].I;\
     uint32_t rhs = (opcode & 255);\
     uint32_t res = lhs - rhs;\
     bus.reg[(d)].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif
#ifndef MOV_RN_O8
 #define MOV_RN_O8(d) \
   {\
     uint32_t val;\
	 val = (opcode & 255);\
     bus.reg[d].I = val;\
     N_FLAG = false;\
     Z_FLAG = (val ? false : true);\
   }
#endif
#ifndef CMP_RN_O8
 #define CMP_RN_O8(d) \
   {\
     uint32_t lhs = bus.reg[(d)].I;\
     uint32_t rhs = (opcode & 255);\
     uint32_t res = lhs - rhs;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif
#ifndef SBC_RD_RS
 #define SBC_RD_RS \
   {\
     uint32_t lhs = bus.reg[dest].I;\
     uint32_t rhs = value;\
     uint32_t res = lhs - rhs - !((uint32_t)C_FLAG);\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif
#ifndef LSL_RD_RM_I5
 #define LSL_RD_RM_I5 \
   {\
     C_FLAG = (bus.reg[source].I >> (32 - shift)) & 1 ? true : false;\
     value = bus.reg[source].I << shift;\
   }
#endif
#ifndef LSL_RD_RS
 #define LSL_RD_RS \
   {\
     C_FLAG = (bus.reg[dest].I >> (32 - value)) & 1 ? true : false;\
     value = bus.reg[dest].I << value;\
   }
#endif
#ifndef LSR_RD_RM_I5
 #define LSR_RD_RM_I5 \
   {\
     C_FLAG = (bus.reg[source].I >> (shift - 1)) & 1 ? true : false;\
     value = bus.reg[source].I >> shift;\
   }
#endif
#ifndef LSR_RD_RS
 #define LSR_RD_RS \
   {\
     C_FLAG = (bus.reg[dest].I >> (value - 1)) & 1 ? true : false;\
     value = bus.reg[dest].I >> value;\
   }
#endif
#ifndef ASR_RD_RM_I5
 #define ASR_RD_RM_I5 \
   {\
     C_FLAG = ((int32_t)bus.reg[source].I >> (int)(shift - 1)) & 1 ? true : false;\
     value = (int32_t)bus.reg[source].I >> (int)shift;\
   }
#endif
#ifndef ASR_RD_RS
 #define ASR_RD_RS \
   {\
     C_FLAG = ((int32_t)bus.reg[dest].I >> (int)(value - 1)) & 1 ? true : false;\
     value = (int32_t)bus.reg[dest].I >> (int)value;\
   }
#endif
#ifndef ROR_RD_RS
 #define ROR_RD_RS \
   {\
     C_FLAG = (bus.reg[dest].I >> (value - 1)) & 1 ? true : false;\
     value = ((bus.reg[dest].I << (32 - value)) |\
              (bus.reg[dest].I >> value));\
   }
#endif
#ifndef NEG_RD_RS
 #define NEG_RD_RS \
   {\
     uint32_t lhs = bus.reg[source].I;\
     uint32_t rhs = 0;\
     uint32_t res = rhs - lhs;\
     bus.reg[dest].I = res;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(rhs, lhs, res);\
     SUBOVERFLOW(rhs, lhs, res);\
   }
#endif
#ifndef CMP_RD_RS
 #define CMP_RD_RS \
   {\
     uint32_t lhs = bus.reg[dest].I;\
     uint32_t rhs = value;\
     uint32_t res = lhs - rhs;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif
#ifndef IMM5_INSN
 #define IMM5_INSN(OP,N) \
  int dest = opcode & 0x07;\
  int source = (opcode >> 3) & 0x07;\
  uint32_t value;\
  OP(N);\
  bus.reg[dest].I = value;\
  N_FLAG = (value & 0x80000000 ? true : false);\
  Z_FLAG = (value ? false : true);
 #define IMM5_INSN_0(OP) \
  int dest = opcode & 0x07;\
  int source = (opcode >> 3) & 0x07;\
  uint32_t value;\
  OP;\
  bus.reg[dest].I = value;\
  N_FLAG = (value & 0x80000000 ? true : false);\
  Z_FLAG = (value ? false : true);
 #define IMM5_LSL(N) \
  int shift = N;\
  LSL_RD_RM_I5;
 #define IMM5_LSL_0 \
  value = bus.reg[source].I;
 #define IMM5_LSR(N) \
  int shift = N;\
  LSR_RD_RM_I5;
 #define IMM5_LSR_0 \
  C_FLAG = bus.reg[source].I & 0x80000000 ? true : false;\
  value = 0;
 #define IMM5_ASR(N) \
  int shift = N;\
  ASR_RD_RM_I5;
 #define IMM5_ASR_0 \
  if(bus.reg[source].I & 0x80000000) {\
    value = 0xFFFFFFFF;\
    C_FLAG = true;\
  } else {\
    value = 0;\
    C_FLAG = false;\
  }
#endif
#ifndef THREEARG_INSN
 #define THREEARG_INSN(OP,N) \
  int dest = opcode & 0x07;          \
  int source = (opcode >> 3) & 0x07; \
  OP(N);
#endif

/* Shift instructions ///////////////////////////////////////////////////// */

#define DEFINE_IMM5_INSN(OP,BASE) \
  static  void thumb##BASE##_00(uint32_t opcode) { IMM5_INSN_0(OP##_0); } \
  static  void thumb##BASE##_01(uint32_t opcode) { IMM5_INSN(OP, 1); } \
  static  void thumb##BASE##_02(uint32_t opcode) { IMM5_INSN(OP, 2); } \
  static  void thumb##BASE##_03(uint32_t opcode) { IMM5_INSN(OP, 3); } \
  static  void thumb##BASE##_04(uint32_t opcode) { IMM5_INSN(OP, 4); } \
  static  void thumb##BASE##_05(uint32_t opcode) { IMM5_INSN(OP, 5); } \
  static  void thumb##BASE##_06(uint32_t opcode) { IMM5_INSN(OP, 6); } \
  static  void thumb##BASE##_07(uint32_t opcode) { IMM5_INSN(OP, 7); } \
  static  void thumb##BASE##_08(uint32_t opcode) { IMM5_INSN(OP, 8); } \
  static  void thumb##BASE##_09(uint32_t opcode) { IMM5_INSN(OP, 9); } \
  static  void thumb##BASE##_0A(uint32_t opcode) { IMM5_INSN(OP,10); } \
  static  void thumb##BASE##_0B(uint32_t opcode) { IMM5_INSN(OP,11); } \
  static  void thumb##BASE##_0C(uint32_t opcode) { IMM5_INSN(OP,12); } \
  static  void thumb##BASE##_0D(uint32_t opcode) { IMM5_INSN(OP,13); } \
  static  void thumb##BASE##_0E(uint32_t opcode) { IMM5_INSN(OP,14); } \
  static  void thumb##BASE##_0F(uint32_t opcode) { IMM5_INSN(OP,15); } \
  static  void thumb##BASE##_10(uint32_t opcode) { IMM5_INSN(OP,16); } \
  static  void thumb##BASE##_11(uint32_t opcode) { IMM5_INSN(OP,17); } \
  static  void thumb##BASE##_12(uint32_t opcode) { IMM5_INSN(OP,18); } \
  static  void thumb##BASE##_13(uint32_t opcode) { IMM5_INSN(OP,19); } \
  static  void thumb##BASE##_14(uint32_t opcode) { IMM5_INSN(OP,20); } \
  static  void thumb##BASE##_15(uint32_t opcode) { IMM5_INSN(OP,21); } \
  static  void thumb##BASE##_16(uint32_t opcode) { IMM5_INSN(OP,22); } \
  static  void thumb##BASE##_17(uint32_t opcode) { IMM5_INSN(OP,23); } \
  static  void thumb##BASE##_18(uint32_t opcode) { IMM5_INSN(OP,24); } \
  static  void thumb##BASE##_19(uint32_t opcode) { IMM5_INSN(OP,25); } \
  static  void thumb##BASE##_1A(uint32_t opcode) { IMM5_INSN(OP,26); } \
  static  void thumb##BASE##_1B(uint32_t opcode) { IMM5_INSN(OP,27); } \
  static  void thumb##BASE##_1C(uint32_t opcode) { IMM5_INSN(OP,28); } \
  static  void thumb##BASE##_1D(uint32_t opcode) { IMM5_INSN(OP,29); } \
  static  void thumb##BASE##_1E(uint32_t opcode) { IMM5_INSN(OP,30); } \
  static  void thumb##BASE##_1F(uint32_t opcode) { IMM5_INSN(OP,31); }

/* LSL Rd, Rm, #Imm 5 */
DEFINE_IMM5_INSN(IMM5_LSL,00)
/* LSR Rd, Rm, #Imm 5 */
DEFINE_IMM5_INSN(IMM5_LSR,08)
/* ASR Rd, Rm, #Imm 5 */
DEFINE_IMM5_INSN(IMM5_ASR,10)

/* 3-argument ADD/SUB ///////////////////////////////////////////////////// */

#define DEFINE_REG3_INSN(OP,BASE) \
  static  void thumb##BASE##_0(uint32_t opcode) { THREEARG_INSN(OP,0); } \
  static  void thumb##BASE##_1(uint32_t opcode) { THREEARG_INSN(OP,1); } \
  static  void thumb##BASE##_2(uint32_t opcode) { THREEARG_INSN(OP,2); } \
  static  void thumb##BASE##_3(uint32_t opcode) { THREEARG_INSN(OP,3); } \
  static  void thumb##BASE##_4(uint32_t opcode) { THREEARG_INSN(OP,4); } \
  static  void thumb##BASE##_5(uint32_t opcode) { THREEARG_INSN(OP,5); } \
  static  void thumb##BASE##_6(uint32_t opcode) { THREEARG_INSN(OP,6); } \
  static  void thumb##BASE##_7(uint32_t opcode) { THREEARG_INSN(OP,7); }

#define DEFINE_IMM3_INSN(OP,BASE) \
  static  void thumb##BASE##_0(uint32_t opcode) { THREEARG_INSN(OP##_0,0); } \
  static  void thumb##BASE##_1(uint32_t opcode) { THREEARG_INSN(OP,1); } \
  static  void thumb##BASE##_2(uint32_t opcode) { THREEARG_INSN(OP,2); } \
  static  void thumb##BASE##_3(uint32_t opcode) { THREEARG_INSN(OP,3); } \
  static  void thumb##BASE##_4(uint32_t opcode) { THREEARG_INSN(OP,4); } \
  static  void thumb##BASE##_5(uint32_t opcode) { THREEARG_INSN(OP,5); } \
  static  void thumb##BASE##_6(uint32_t opcode) { THREEARG_INSN(OP,6); } \
  static  void thumb##BASE##_7(uint32_t opcode) { THREEARG_INSN(OP,7); }

/* ADD Rd, Rs, Rn */
DEFINE_REG3_INSN(ADD_RD_RS_RN,18)
/* SUB Rd, Rs, Rn */
DEFINE_REG3_INSN(SUB_RD_RS_RN,1A)
/* ADD Rd, Rs, #Offset3 */
DEFINE_IMM3_INSN(ADD_RD_RS_O3,1C)
/* SUB Rd, Rs, #Offset3 */
DEFINE_IMM3_INSN(SUB_RD_RS_O3,1E)

/* MOV/CMP/ADD/SUB immediate ////////////////////////////////////////////// */

/* MOV R0, #Offset8 */
static  void thumb20(uint32_t opcode) { MOV_RN_O8(0); }
/* MOV R1, #Offset8 */
static  void thumb21(uint32_t opcode) { MOV_RN_O8(1); }
/* MOV R2, #Offset8 */
static  void thumb22(uint32_t opcode) { MOV_RN_O8(2); }
/* MOV R3, #Offset8 */
static  void thumb23(uint32_t opcode) { MOV_RN_O8(3); }
/* MOV R4, #Offset8 */
static  void thumb24(uint32_t opcode) { MOV_RN_O8(4); }
/* MOV R5, #Offset8 */
static  void thumb25(uint32_t opcode) { MOV_RN_O8(5); }
/* MOV R6, #Offset8 */
static  void thumb26(uint32_t opcode) { MOV_RN_O8(6); }
/* MOV R7, #Offset8 */
static  void thumb27(uint32_t opcode) { MOV_RN_O8(7); }

/* CMP R0, #Offset8 */
static  void thumb28(uint32_t opcode) { CMP_RN_O8(0); }
/* CMP R1, #Offset8 */
static  void thumb29(uint32_t opcode) { CMP_RN_O8(1); }
/* CMP R2, #Offset8 */
static  void thumb2A(uint32_t opcode) { CMP_RN_O8(2); }
/* CMP R3, #Offset8 */
static  void thumb2B(uint32_t opcode) { CMP_RN_O8(3); }
/* CMP R4, #Offset8 */
static  void thumb2C(uint32_t opcode) { CMP_RN_O8(4); }
/* CMP R5, #Offset8 */
static  void thumb2D(uint32_t opcode) { CMP_RN_O8(5); }
/* CMP R6, #Offset8 */
static  void thumb2E(uint32_t opcode) { CMP_RN_O8(6); }
/* CMP R7, #Offset8 */
static  void thumb2F(uint32_t opcode) { CMP_RN_O8(7); }

/* ADD R0,#Offset8 */
static  void thumb30(uint32_t opcode) { ADD_RN_O8(0); }
/* ADD R1,#Offset8 */
static  void thumb31(uint32_t opcode) { ADD_RN_O8(1); }
/* ADD R2,#Offset8 */
static  void thumb32(uint32_t opcode) { ADD_RN_O8(2); }
/* ADD R3,#Offset8 */
static  void thumb33(uint32_t opcode) { ADD_RN_O8(3); }
/* ADD R4,#Offset8 */
static  void thumb34(uint32_t opcode) { ADD_RN_O8(4); }
/* ADD R5,#Offset8 */
static  void thumb35(uint32_t opcode) { ADD_RN_O8(5); }
/* ADD R6,#Offset8 */
static  void thumb36(uint32_t opcode) { ADD_RN_O8(6); }
/* ADD R7,#Offset8 */
static  void thumb37(uint32_t opcode) { ADD_RN_O8(7); }

/* SUB R0,#Offset8 */
static  void thumb38(uint32_t opcode) { SUB_RN_O8(0); }
/* SUB R1,#Offset8 */
static  void thumb39(uint32_t opcode) { SUB_RN_O8(1); }
/* SUB R2,#Offset8 */
static  void thumb3A(uint32_t opcode) { SUB_RN_O8(2); }
/* SUB R3,#Offset8 */
static  void thumb3B(uint32_t opcode) { SUB_RN_O8(3); }
/* SUB R4,#Offset8 */
static  void thumb3C(uint32_t opcode) { SUB_RN_O8(4); }
/* SUB R5,#Offset8 */
static  void thumb3D(uint32_t opcode) { SUB_RN_O8(5); }
/* SUB R6,#Offset8 */
static  void thumb3E(uint32_t opcode) { SUB_RN_O8(6); }
/* SUB R7,#Offset8 */
static  void thumb3F(uint32_t opcode) { SUB_RN_O8(7); }

/* ALU operations ///////////////////////////////////////////////////////// */

/* AND Rd, Rs */
static  void thumb40_0(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t val = (bus.reg[dest].I & bus.reg[(opcode >> 3)&7].I);

  /*bus.reg[dest].I &= bus.reg[(opcode >> 3)&7].I; */
  N_FLAG = val & 0x80000000 ? true : false;
  Z_FLAG = val ? false : true;

  bus.reg[dest].I = val;

}

/* EOR Rd, Rs */
static  void thumb40_1(uint32_t opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I ^= bus.reg[(opcode >> 3)&7].I;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
  Z_FLAG = bus.reg[dest].I ? false : true;
}

/* LSL Rd, Rs */
static  void thumb40_2(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[(opcode >> 3)&7].I & 0xFF;
  uint32_t val = value;
  if(val) {
    if(val == 32) {
      value = 0;
      C_FLAG = (bus.reg[dest].I & 1 ? true : false);
    } else if(val < 32) {
      LSL_RD_RS;
    } else {
      value = 0;
      C_FLAG = false;
    }
    bus.reg[dest].I = value;
  }
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
  Z_FLAG = bus.reg[dest].I ? false : true;
  clockTicks = codeTicksAccess(bus.armNextPC, BITS_16)+2;
}

/* LSR Rd, Rs */
static  void thumb40_3(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[(opcode >> 3)&7].I & 0xFF;
  uint32_t val = value;
  if(val) {
    if(val == 32) {
      value = 0;
      C_FLAG = (bus.reg[dest].I & 0x80000000 ? true : false);
    } else if(val < 32) {
      LSR_RD_RS;
    } else {
      value = 0;
      C_FLAG = false;
    }
    bus.reg[dest].I = value;
  }
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
  Z_FLAG = bus.reg[dest].I ? false : true;
  clockTicks = codeTicksAccess(bus.armNextPC, BITS_16)+2;
}

/* ASR Rd, Rs */
static  void thumb41_0(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[(opcode >> 3)&7].I & 0xFF;

  if(value) {
    if(value < 32) {
      ASR_RD_RS;
      bus.reg[dest].I = value;
    } else {
      if(bus.reg[dest].I & 0x80000000){
        bus.reg[dest].I = 0xFFFFFFFF;
        C_FLAG = true;
      } else {
        bus.reg[dest].I = 0x00000000;
        C_FLAG = false;
      }
    }
  }
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
  Z_FLAG = bus.reg[dest].I ? false : true;
  clockTicks = codeTicksAccess(bus.armNextPC, BITS_16)+2;
}

/* ADC Rd, Rs */
static  void thumb41_1(uint32_t opcode)
{
  int dest = opcode & 0x07;
  uint32_t value = bus.reg[(opcode >> 3)&7].I;
  ADC_RD_RS;
}

/* SBC Rd, Rs */
static  void thumb41_2(uint32_t opcode)
{
  int dest = opcode & 0x07;
  uint32_t value = bus.reg[(opcode >> 3)&7].I;
  SBC_RD_RS;
}

/* ROR Rd, Rs */
static  void thumb41_3(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[(opcode >> 3)&7].I & 0xFF;
  uint32_t val = value;
  if(val) {
    value = value & 0x1f;
    if(val == 0) {
      C_FLAG = (bus.reg[dest].I & 0x80000000 ? true : false);
    } else {
      ROR_RD_RS;
      bus.reg[dest].I = value;
    }
  }
  clockTicks = codeTicksAccess(bus.armNextPC, BITS_16)+2;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
  Z_FLAG = bus.reg[dest].I ? false : true;
}

/* TST Rd, Rs */
static  void thumb42_0(uint32_t opcode)
{
  uint32_t value = bus.reg[opcode & 7].I & bus.reg[(opcode >> 3) & 7].I;
  N_FLAG = value & 0x80000000 ? true : false;
  Z_FLAG = value ? false : true;
}

/* NEG Rd, Rs */
static  void thumb42_1(uint32_t opcode)
{
  int dest = opcode & 7;
  int source = (opcode >> 3) & 7;
  NEG_RD_RS;
}

/* CMP Rd, Rs */
static  void thumb42_2(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[(opcode >> 3)&7].I;
  CMP_RD_RS;
}

/* CMN Rd, Rs */
static  void thumb42_3(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[(opcode >> 3)&7].I;
  CMN_RD_RS;
}

/* ORR Rd, Rs */
static  void thumb43_0(uint32_t opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I |= bus.reg[(opcode >> 3) & 7].I;
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

/* MUL Rd, Rs */
static  void thumb43_1(uint32_t opcode)
{
  int dest;
  uint32_t rm;
  clockTicks = 1;
  dest = opcode & 7;
  rm = bus.reg[dest].I;
  bus.reg[dest].I = bus.reg[(opcode >> 3) & 7].I * rm;
  if (((int32_t)rm) < 0)
    rm = ~rm;
  if ((rm & 0xFFFFFF00) == 0) {
    /* clockTicks += 0; */
  } else if ((rm & 0xFFFF0000) == 0)
    clockTicks += 1;
  else if ((rm & 0xFF000000) == 0)
    clockTicks += 2;
  else
    clockTicks += 3;
  bus.busPrefetchCount = (bus.busPrefetchCount<<clockTicks) | (0xFF>>(8-clockTicks));
  clockTicks += codeTicksAccess(bus.armNextPC, BITS_16) + 1;
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

/* BIC Rd, Rs */
static  void thumb43_2(uint32_t opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I &= (~bus.reg[(opcode >> 3) & 7].I);
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

/* MVN Rd, Rs */
static  void thumb43_3(uint32_t opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I = ~bus.reg[(opcode >> 3) & 7].I;
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

/* High-register instructions and BX ////////////////////////////////////// */

/* ADD Rd, Hs */
static  void thumb44_1(uint32_t opcode)
{
  bus.reg[opcode&7].I += bus.reg[((opcode>>3)&7)+8].I;
}

/* ADD Hd, Rs */
static  void thumb44_2(uint32_t opcode)
{
  bus.reg[(opcode&7)+8].I += bus.reg[(opcode>>3)&7].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
  }
}

/* ADD Hd, Hs */
static  void thumb44_3(uint32_t opcode)
{
  bus.reg[(opcode&7)+8].I += bus.reg[((opcode>>3)&7)+8].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
  }
}

/* CMP Rd, Hs */
static  void thumb45_1(uint32_t opcode)
{
  int dest = opcode & 7;
  uint32_t value = bus.reg[((opcode>>3)&7)+8].I;
  CMP_RD_RS;
}

/* CMP Hd, Rs */
static  void thumb45_2(uint32_t opcode)
{
  int dest = (opcode & 7) + 8;
  uint32_t value = bus.reg[(opcode>>3)&7].I;
  CMP_RD_RS;
}

/* CMP Hd, Hs */
static  void thumb45_3(uint32_t opcode)
{
  int dest = (opcode & 7) + 8;
  uint32_t value = bus.reg[((opcode>>3)&7)+8].I;
  CMP_RD_RS;
}

/* MOV Rd, Rs */
static  void thumb46_0(uint32_t opcode)
{
  bus.reg[opcode&7].I = bus.reg[((opcode>>3)&7)].I;
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
}


/* MOV Rd, Hs */
static  void thumb46_1(uint32_t opcode)
{
  bus.reg[opcode&7].I = bus.reg[((opcode>>3)&7)+8].I;
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
}

/* MOV Hd, Rs */
static  void thumb46_2(uint32_t opcode)
{
  bus.reg[(opcode&7)+8].I = bus.reg[(opcode>>3)&7].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
  }
}

/* MOV Hd, Hs */
static  void thumb46_3(uint32_t opcode)
{
  bus.reg[(opcode&7)+8].I = bus.reg[((opcode>>3)&7)+8].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
  }
}


/* BX Rs */
static  void thumb47(uint32_t opcode)
{
	int base = (opcode >> 3) & 15;
	bus.busPrefetchCount=0;
	bus.reg[15].I = bus.reg[base].I;
	if(bus.reg[base].I & 1) {
		armState = false;
		bus.reg[15].I &= 0xFFFFFFFE;
		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 2;
		THUMB_PREFETCH;
		clockTicks = CLOCKTICKS_UPDATE_TYPE16P;

	} else {
		armState = true;
		bus.reg[15].I &= 0xFFFFFFFC;
		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 4;
		ARM_PREFETCH;
		clockTicks = CLOCKTICKS_UPDATE_TYPE32P;
	}
}

/* Load/store instructions //////////////////////////////////////////////// */

/* LDR R0~R7,[PC, #Imm] */
static  void thumb48(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	uint8_t regist = (opcode >> 8) & 7;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = (bus.reg[15].I & 0xFFFFFFFC) + ((opcode & 0xFF) << 2);
	bus.reg[regist].I = CPUReadMemoryQuick(address);
	bus.busPrefetchCount=0;
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* STR Rd, [Rs, Rn] */
static  void thumb50(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	CPUWriteMemory(address, bus.reg[opcode & 7].I);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* STRH Rd, [Rs, Rn] */
static  void thumb52(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	CPUWriteHalfWord(address, bus.reg[opcode&7].I & 0xFFFF);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* STRB Rd, [Rs, Rn] */
static  void thumb54(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode >>6)&7].I;
	CPUWriteByte(address, bus.reg[opcode & 7].I & 0xFF);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* LDSB Rd, [Rs, Rn] */
static  void thumb56(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = (int8_t)CPUReadByte(address);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* LDR Rd, [Rs, Rn] */
static  void thumb58(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = CPUReadMemory(address);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* LDRH Rd, [Rs, Rn] */
static  void thumb5A(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = CPUReadHalfWord(address);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* LDRB Rd, [Rs, Rn] */
static  void thumb5C(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = CPUReadByte(address);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* LDSH Rd, [Rs, Rn] */
static  void thumb5E(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = (int16_t)CPUReadHalfWordSigned(address);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* STR Rd, [Rs, #Imm] */
static  void thumb60(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<2);
	CPUWriteMemory(address, bus.reg[opcode&7].I);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* LDR Rd, [Rs, #Imm] */
static  void thumb68(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<2);
	bus.reg[opcode&7].I = CPUReadMemory(address);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* STRB Rd, [Rs, #Imm] */
static  void thumb70(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31));
	CPUWriteByte(address, bus.reg[opcode&7].I & 0xFF);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* LDRB Rd, [Rs, #Imm] */
static  void thumb78(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31));
	bus.reg[opcode&7].I = CPUReadByte(address);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* STRH Rd, [Rs, #Imm] */
static  void thumb80(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<1);
	CPUWriteHalfWord(address, bus.reg[opcode&7].I & 0xFFFF);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* LDRH Rd, [Rs, #Imm] */
static  void thumb88(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<1);
	bus.reg[opcode&7].I = CPUReadHalfWord(address);
	dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* STR R0~R7, [SP, #Imm] */
static  void thumb90(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	uint8_t regist = (opcode >> 8) & 7;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[13].I + ((opcode&255)<<2);
	CPUWriteMemory(address, bus.reg[regist].I);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

/* LDR R0~R7, [SP, #Imm] */
static  void thumb98(uint32_t opcode)
{
	uint32_t address;
	int dataticks_value;
	uint8_t regist = (opcode >> 8) & 7;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	address = bus.reg[13].I + ((opcode&255)<<2);
	bus.reg[regist].I = CPUReadMemoryQuick(address);
	dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* PC/stack-related /////////////////////////////////////////////////////// */

/* ADD R0~R7, PC, Imm */
static  void thumbA0(uint32_t opcode)
{
  uint8_t regist = (opcode >> 8) & 7;
  bus.reg[regist].I = (bus.reg[15].I & 0xFFFFFFFC) + ((opcode&255)<<2);
  clockTicks = 1 + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* ADD R0~R7, SP, Imm */
static  void thumbA8(uint32_t opcode)
{
  uint8_t regist = (opcode >> 8) & 7;
  bus.reg[regist].I = bus.reg[13].I + ((opcode&255)<<2);
  clockTicks = 1 + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* ADD SP, Imm */
static  void thumbB0(uint32_t opcode)
{
  int offset = (opcode & 127) << 2;
  if(opcode & 0x80)
    offset = -offset;
  bus.reg[13].I += offset;
  clockTicks = 1 + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* Push and pop /////////////////////////////////////////////////////////// */

/* Thumb PUSH/POP iterate bits 0..7 of the 8-bit register list.  Same
 * idea as the ARM LDM/STM ctz-loop rewrite (commit c7a870a): one
 * predictable loop branch with N iterations beats 8 unconditional
 * `if (opcode & (1<<i))` checks where typically half are not-taken.
 * Reuses the LDM_LOAD_ONE / STM_STORE_ONE single-access bodies from
 * the ARM section above. */
#define PUSH_LOOP \
    do { uint32_t _list = opcode & 0xFFu; \
         while (_list) { STM_STORE_ONE(CTZ_U32(_list)); _list &= _list - 1u; } \
    } while (0)

#define POP_LOOP \
    do { uint32_t _list = opcode & 0xFFu; \
         while (_list) { LDM_LOAD_ONE(CTZ_U32(_list)); _list &= _list - 1u; } \
    } while (0)

/* PUSH {Rlist} */
static  void thumbB4(uint32_t opcode)
{
  int count;
  uint32_t temp;
  uint32_t address;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  count = 0;
  temp = bus.reg[13].I - 4 * cpuBitsSet[opcode & 0xff];
  address = temp & 0xFFFFFFFC;
  PUSH_LOOP;
  clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_16);
  bus.reg[13].I = temp;
}

/* PUSH {Rlist, LR} */
static  void thumbB5(uint32_t opcode)
{
  int count;
  uint32_t temp;
  uint32_t address;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  count = 0;
  temp = bus.reg[13].I - 4 - 4 * cpuBitsSet[opcode & 0xff];
  address = temp & 0xFFFFFFFC;
  PUSH_LOOP;
  if (opcode & 0x100) {
    /* LR push (bit 8 of opcode -> r14); single-reg form of the loop body */
    STM_STORE_ONE(14);
  }
  clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_16);
  bus.reg[13].I = temp;
}

/* POP {Rlist} */
static  void thumbBC(uint32_t opcode)
{
  int count;
  uint32_t address;
  uint32_t temp;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  count = 0;
  address = bus.reg[13].I & 0xFFFFFFFC;
  temp = bus.reg[13].I + 4*cpuBitsSet[opcode & 0xFF];
  POP_LOOP;
  bus.reg[13].I = temp;
  clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* POP {Rlist, PC} */
static  void thumbBD(uint32_t opcode)
{
  int count;
  uint32_t address;
  uint32_t temp;
  int dataticks_value;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  count = 0;
  address = bus.reg[13].I & 0xFFFFFFFC;
  temp = bus.reg[13].I + 4 + 4*cpuBitsSet[opcode & 0xFF];
  POP_LOOP;
  /* PC load (bit 8); kept inline because it has special semantics:
   * 0xFFFFFFFE mask for Thumb alignment, pipeline flush via THUMB_PREFETCH,
   * extra +3 clockTicks for the branch, and busPrefetchCount reset. */
  bus.reg[15].I = (CPUReadMemory(address) & 0xFFFFFFFE);
  dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address);
  DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
  clockTicks += 1 + dataticks_value;
  count++;
  bus.armNextPC = bus.reg[15].I;
  bus.reg[15].I += 2;
  bus.reg[13].I = temp;
  THUMB_PREFETCH;
  bus.busPrefetchCount = 0;
  clockTicks += 3 + (codeTicksAccess(bus.armNextPC, BITS_16) << 1);
}

/* Load/store multiple //////////////////////////////////////////////////// */

/* Thumb LDMIA/STMIA iterate bits 0..7 of the register list with base reg
 * encoded in bits 8..10 of the opcode (resolved at handler entry).  STM
 * does per-iter write-back of `temp` to bus.reg[regist].I -- matches the
 * ARMv4 semantics where storing the base register after the first iter
 * stores the written-back value.  LDM has no per-iter side effect; the
 * post-loop conditional write-back in the handler handles the base reg
 * when it's not in the list. */

#define THUMB_STM_LOOP(b) \
    do { uint32_t _list = opcode & 0xFFu; \
         while (_list) { \
             int _r = CTZ_U32(_list); \
             int dataticks_val; \
             CPUWriteMemory(address, bus.reg[_r].I); \
             bus.reg[(b)].I = temp; \
             dataticks_val = count ? DATATICKS_ACCESS_32BIT_SEQ(address) \
                                   : DATATICKS_ACCESS_32BIT(address); \
             DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_val); \
             clockTicks += 1 + dataticks_val; \
             count++; \
             address += 4; \
             _list &= _list - 1u; \
         } \
    } while (0)

/* THUMB_LDM_LOOP is structurally identical to POP_LOOP -- iterate bits
 * 0..7 and load each into the matching low reg.  Kept as an alias for
 * caller readability. */
#define THUMB_LDM_LOOP POP_LOOP

/* STM R0~7!, {Rlist} */
static  void thumbC0(uint32_t opcode)
{
  uint32_t address;
  uint32_t temp;
  int count;
  uint8_t regist = (opcode >> 8) & 7;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  address = bus.reg[regist].I & 0xFFFFFFFC;
  temp = bus.reg[regist].I + 4*cpuBitsSet[opcode & 0xff];
  count = 0;
  /* store */
  THUMB_STM_LOOP(regist);
  clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_16);
}

/* LDM R0~R7!, {Rlist} */
static  void thumbC8(uint32_t opcode)
{
  uint32_t address;
  uint32_t temp;
  int count;
  uint8_t regist = (opcode >> 8) & 7;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  address = bus.reg[regist].I & 0xFFFFFFFC;
  temp = bus.reg[regist].I + 4*cpuBitsSet[opcode & 0xFF];
  count = 0;
  /* load */
  THUMB_LDM_LOOP;
  clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_16);
  if(!(opcode & (1<<regist)))
    bus.reg[regist].I = temp;
}

/* Conditional branches /////////////////////////////////////////////////// */

/* BEQ offset */
static  void thumbD0(uint32_t opcode)
{
#if !USE_TWEAK_SPEEDHACK
	clockTicks = CLOCKTICKS_UPDATE_TYPE16;
#endif
	if(Z_FLAG)
	{
		bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 2;
		THUMB_PREFETCH;
#if USE_TWEAK_SPEEDHACK
		clockTicks = 30;
#else
        clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
#endif
		bus.busPrefetchCount=0;
	}
}

/* BNE offset */
static  void thumbD1(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(!Z_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BCS offset */
static  void thumbD2(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(C_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BCC offset */
static  void thumbD3(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(!C_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BMI offset */
static  void thumbD4(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(N_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BPL offset */
static  void thumbD5(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(!N_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BVS offset */
static  void thumbD6(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(V_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BVC offset */
static  void thumbD7(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(!V_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BHI offset */
static  void thumbD8(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(C_FLAG && !Z_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BLS offset */
static  void thumbD9(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(!C_FLAG || Z_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BGE offset */
static  void thumbDA(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(N_FLAG == V_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BLT offset */
static  void thumbDB(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(N_FLAG != V_FLAG) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BGT offset */
static  void thumbDC(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(!Z_FLAG && (N_FLAG == V_FLAG)) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* BLE offset */
static  void thumbDD(uint32_t opcode)
{
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
  if(Z_FLAG || (N_FLAG != V_FLAG)) {
    bus.reg[15].I += ((int8_t)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks += codeTicksAccessSeq16(bus.armNextPC) + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
    bus.busPrefetchCount=0;
  }
}

/* SWI, B, BL ///////////////////////////////////////////////////////////// */

/* SWI #comment */
static  void thumbDF(uint32_t opcode)
{
  clockTicks = 3;
  bus.busPrefetchCount=0;
  CPUSoftwareInterrupt(opcode & 0xFF);
}

/* B offset */
static  void thumbE0(uint32_t opcode)
{
  int offset = (opcode & 0x3FF) << 1;
  if(opcode & 0x0400)
    offset |= 0xFFFFF800;
  bus.reg[15].I += offset;
  bus.armNextPC = bus.reg[15].I;
  bus.reg[15].I += 2;
  THUMB_PREFETCH;
  clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
  bus.busPrefetchCount=0;
}

/* BLL #offset (forward) */
static  void thumbF0(uint32_t opcode)
{
  int offset = (opcode & 0x7FF);
  bus.reg[14].I = bus.reg[15].I + (offset << 12);
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
}

/* BLL #offset (backward) */
static  void thumbF4(uint32_t opcode)
{
  int offset = (opcode & 0x7FF);
  bus.reg[14].I = bus.reg[15].I + ((offset << 12) | 0xFF800000);
  clockTicks = CLOCKTICKS_UPDATE_TYPE16;
}

/* BLH #offset */
static  void thumbF8(uint32_t opcode)
{
  int offset = (opcode & 0x7FF);
  uint32_t temp = bus.reg[15].I-2;
  bus.reg[15].I = (bus.reg[14].I + (offset<<1))&0xFFFFFFFE;
  bus.armNextPC = bus.reg[15].I;
  bus.reg[15].I += 2;
  bus.reg[14].I = temp|1;
  THUMB_PREFETCH;
  clockTicks = CLOCKTICKS_UPDATE_TYPE16P;
  bus.busPrefetchCount = 0;
}

/* Instruction table ////////////////////////////////////////////////////// */

typedef  void (*insnfunc_t)(uint32_t opcode);
#define thumbUI thumbUnknownInsn
#define thumbBP thumbUnknownInsn

static insnfunc_t thumbInsnTable[1024] =
{
  thumb00_00,thumb00_01,thumb00_02,thumb00_03,thumb00_04,thumb00_05,thumb00_06,thumb00_07,  /* 00 */
  thumb00_08,thumb00_09,thumb00_0A,thumb00_0B,thumb00_0C,thumb00_0D,thumb00_0E,thumb00_0F,
  thumb00_10,thumb00_11,thumb00_12,thumb00_13,thumb00_14,thumb00_15,thumb00_16,thumb00_17,
  thumb00_18,thumb00_19,thumb00_1A,thumb00_1B,thumb00_1C,thumb00_1D,thumb00_1E,thumb00_1F,
  thumb08_00,thumb08_01,thumb08_02,thumb08_03,thumb08_04,thumb08_05,thumb08_06,thumb08_07,  /* 08 */
  thumb08_08,thumb08_09,thumb08_0A,thumb08_0B,thumb08_0C,thumb08_0D,thumb08_0E,thumb08_0F,
  thumb08_10,thumb08_11,thumb08_12,thumb08_13,thumb08_14,thumb08_15,thumb08_16,thumb08_17,
  thumb08_18,thumb08_19,thumb08_1A,thumb08_1B,thumb08_1C,thumb08_1D,thumb08_1E,thumb08_1F,
  thumb10_00,thumb10_01,thumb10_02,thumb10_03,thumb10_04,thumb10_05,thumb10_06,thumb10_07,  /* 10 */
  thumb10_08,thumb10_09,thumb10_0A,thumb10_0B,thumb10_0C,thumb10_0D,thumb10_0E,thumb10_0F,
  thumb10_10,thumb10_11,thumb10_12,thumb10_13,thumb10_14,thumb10_15,thumb10_16,thumb10_17,
  thumb10_18,thumb10_19,thumb10_1A,thumb10_1B,thumb10_1C,thumb10_1D,thumb10_1E,thumb10_1F,
  thumb18_0,thumb18_1,thumb18_2,thumb18_3,thumb18_4,thumb18_5,thumb18_6,thumb18_7,          /* 18 */
  thumb1A_0,thumb1A_1,thumb1A_2,thumb1A_3,thumb1A_4,thumb1A_5,thumb1A_6,thumb1A_7,
  thumb1C_0,thumb1C_1,thumb1C_2,thumb1C_3,thumb1C_4,thumb1C_5,thumb1C_6,thumb1C_7,
  thumb1E_0,thumb1E_1,thumb1E_2,thumb1E_3,thumb1E_4,thumb1E_5,thumb1E_6,thumb1E_7,
  thumb20,thumb20,thumb20,thumb20,thumb21,thumb21,thumb21,thumb21,  /* 20 */
  thumb22,thumb22,thumb22,thumb22,thumb23,thumb23,thumb23,thumb23,
  thumb24,thumb24,thumb24,thumb24,thumb25,thumb25,thumb25,thumb25,
  thumb26,thumb26,thumb26,thumb26,thumb27,thumb27,thumb27,thumb27,
  thumb28,thumb28,thumb28,thumb28,thumb29,thumb29,thumb29,thumb29,  /* 28 */
  thumb2A,thumb2A,thumb2A,thumb2A,thumb2B,thumb2B,thumb2B,thumb2B,
  thumb2C,thumb2C,thumb2C,thumb2C,thumb2D,thumb2D,thumb2D,thumb2D,
  thumb2E,thumb2E,thumb2E,thumb2E,thumb2F,thumb2F,thumb2F,thumb2F,
  thumb30,thumb30,thumb30,thumb30,thumb31,thumb31,thumb31,thumb31,  /* 30 */
  thumb32,thumb32,thumb32,thumb32,thumb33,thumb33,thumb33,thumb33,
  thumb34,thumb34,thumb34,thumb34,thumb35,thumb35,thumb35,thumb35,
  thumb36,thumb36,thumb36,thumb36,thumb37,thumb37,thumb37,thumb37,
  thumb38,thumb38,thumb38,thumb38,thumb39,thumb39,thumb39,thumb39,  /* 38 */
  thumb3A,thumb3A,thumb3A,thumb3A,thumb3B,thumb3B,thumb3B,thumb3B,
  thumb3C,thumb3C,thumb3C,thumb3C,thumb3D,thumb3D,thumb3D,thumb3D,
  thumb3E,thumb3E,thumb3E,thumb3E,thumb3F,thumb3F,thumb3F,thumb3F,
  thumb40_0,thumb40_1,thumb40_2,thumb40_3,thumb41_0,thumb41_1,thumb41_2,thumb41_3,  /* 40 */
  thumb42_0,thumb42_1,thumb42_2,thumb42_3,thumb43_0,thumb43_1,thumb43_2,thumb43_3,
  thumbUI,thumb44_1,thumb44_2,thumb44_3,thumbUI,thumb45_1,thumb45_2,thumb45_3,
  thumb46_0,thumb46_1,thumb46_2,thumb46_3,thumb47,thumb47,thumbUI,thumbUI,
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,  /* 48 */
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,
  thumb50,thumb50,thumb50,thumb50,thumb50,thumb50,thumb50,thumb50,  /* 50 */
  thumb52,thumb52,thumb52,thumb52,thumb52,thumb52,thumb52,thumb52,
  thumb54,thumb54,thumb54,thumb54,thumb54,thumb54,thumb54,thumb54,
  thumb56,thumb56,thumb56,thumb56,thumb56,thumb56,thumb56,thumb56,
  thumb58,thumb58,thumb58,thumb58,thumb58,thumb58,thumb58,thumb58,  /* 58 */
  thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,
  thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,
  thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,  /* 60 */
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,  /* 68 */
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,  /* 70 */
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,  /* 78 */
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,  /* 80 */
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,  /* 88 */
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,  /* 90 */
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,  /* 98 */
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,  /* A0 */
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,  /* A8 */
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,
  thumbB0,thumbB0,thumbB0,thumbB0,thumbUI,thumbUI,thumbUI,thumbUI,  /* B0 */
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbB4,thumbB4,thumbB4,thumbB4,thumbB5,thumbB5,thumbB5,thumbB5,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,  /* B8 */
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbBC,thumbBC,thumbBC,thumbBC,thumbBD,thumbBD,thumbBD,thumbBD,
  thumbBP,thumbBP,thumbBP,thumbBP,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,  /* C0 */
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,  /* C8 */
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,
  thumbD0,thumbD0,thumbD0,thumbD0,thumbD1,thumbD1,thumbD1,thumbD1,  /* D0 */
  thumbD2,thumbD2,thumbD2,thumbD2,thumbD3,thumbD3,thumbD3,thumbD3,
  thumbD4,thumbD4,thumbD4,thumbD4,thumbD5,thumbD5,thumbD5,thumbD5,
  thumbD6,thumbD6,thumbD6,thumbD6,thumbD7,thumbD7,thumbD7,thumbD7,
  thumbD8,thumbD8,thumbD8,thumbD8,thumbD9,thumbD9,thumbD9,thumbD9,  /* D8 */
  thumbDA,thumbDA,thumbDA,thumbDA,thumbDB,thumbDB,thumbDB,thumbDB,
  thumbDC,thumbDC,thumbDC,thumbDC,thumbDD,thumbDD,thumbDD,thumbDD,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbDF,thumbDF,thumbDF,thumbDF,
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,  /* E0 */
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,  /* E8 */
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,  /* F0 */
  thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,
  thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,
  thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,  /* F8 */
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,
};

/* Wrapper routine (execution loop) /////////////////////////////////////// */


static int thumbExecute (void)
{
   int ct    = 0;
   bool test = false;

   CACHE_PREFETCH(clockTicks);

   do
   {
      uint32_t opcode;
      uint32_t oldArmNextPC;
      clockTicks = 0;

#if USE_CHEATS
      cpuMasterCodeCheck();
#endif


      opcode = cpuPrefetch[0];
      cpuPrefetch[0] = cpuPrefetch[1];

      bus.busPrefetch = false;

      oldArmNextPC = bus.armNextPC;

      bus.armNextPC = bus.reg[15].I;
      bus.reg[15].I += 2;
      THUMB_PREFETCH_NEXT;

      (*thumbInsnTable[opcode>>6])(opcode);

      ct = clockTicks;

      if (ct < 0)
         return 0;

      /*/ better pipelining */
      if (ct==0)
         clockTicks = codeTicksAccessSeq16(oldArmNextPC) + 1;

      cpuTotalTicks += clockTicks;


      test = cpuTotalTicks < cpuNextEvent && !armState && !holdState;
   }while (test);

   return 1;
}

/*============================================================
	GBA GFX
============================================================ */

static uint32_t map_widths [] = { 256, 512, 256, 512 };
static uint32_t map_heights[] = { 256, 256, 512, 512 };

#ifdef TILED_RENDERING
#ifdef _MSC_VER
union u8h
{
   __pragma( pack(push, 1));
   struct
   {
#ifdef MSB_FIRST
      /* 4*/	unsigned char hi:4;
      /* 0*/	unsigned char lo:4;
#else
      /* 0*/	unsigned char lo:4;
      /* 4*/	unsigned char hi:4;
#endif
   }
   __pragma(pack(pop));
   uint8_t val;
};
#else
union u8h
{
   struct
   {
#ifdef MSB_FIRST
      /* 4*/	unsigned char hi:4;
      /* 0*/	unsigned char lo:4;
#else
      /* 0*/	unsigned char lo:4;
      /* 4*/	unsigned char hi:4;
#endif
   } __attribute__ ((packed));
   uint8_t val;
};
#endif
typedef union u8h u8h;

union TileEntry
{
   struct
   {
#ifdef MSB_FIRST
      /*14*/	unsigned palette:4;
      /*13*/	unsigned vFlip:1;
      /*12*/	unsigned hFlip:1;
      /* 0*/	unsigned tileNum:10;
#else
      /* 0*/	unsigned tileNum:10;
      /*12*/	unsigned hFlip:1;
      /*13*/	unsigned vFlip:1;
      /*14*/	unsigned palette:4;
#endif
   };
   uint16_t val;
};
typedef union TileEntry TileEntry;

struct TileLine
{
   uint32_t pixels[8];
};
typedef struct TileLine TileLine;

typedef TileLine (*TileReader) (const uint16_t *, const int, const uint8_t *, uint16_t *, const uint32_t);

static INLINE void gfxDrawPixel(uint32_t *dest, const uint8_t color, const uint16_t *palette, const uint32_t prio)
{
   *dest = color ? (palette[color] | prio): 0x80000000;
}

static INLINE TileLine gfxReadTile(const uint16_t *screenSource, const int yyy, const uint8_t *charBase, uint16_t *palette, const uint32_t prio)
{
   int tileY;
   /* Zero-init suppresses a false-positive uninitialized warning: every
    * field is written by the gfxDrawPixel calls below before any read,
    * but the compiler can't see that through the pointer-to-field. */
   TileLine tileLine = {{0}};
   TileEntry tile;
   const uint8_t *tileBase;
   tile.val = READ16LE(screenSource);

   tileY = yyy & 7;
   if (tile.vFlip) tileY = 7 - tileY;

   tileBase = &charBase[tile.tileNum * 64 + tileY * 8];

   if (!tile.hFlip)
   {
      gfxDrawPixel(&tileLine.pixels[0], tileBase[0], palette, prio);
      gfxDrawPixel(&tileLine.pixels[1], tileBase[1], palette, prio);
      gfxDrawPixel(&tileLine.pixels[2], tileBase[2], palette, prio);
      gfxDrawPixel(&tileLine.pixels[3], tileBase[3], palette, prio);
      gfxDrawPixel(&tileLine.pixels[4], tileBase[4], palette, prio);
      gfxDrawPixel(&tileLine.pixels[5], tileBase[5], palette, prio);
      gfxDrawPixel(&tileLine.pixels[6], tileBase[6], palette, prio);
      gfxDrawPixel(&tileLine.pixels[7], tileBase[7], palette, prio);
   }
   else
   {
      gfxDrawPixel(&tileLine.pixels[0], tileBase[7], palette, prio);
      gfxDrawPixel(&tileLine.pixels[1], tileBase[6], palette, prio);
      gfxDrawPixel(&tileLine.pixels[2], tileBase[5], palette, prio);
      gfxDrawPixel(&tileLine.pixels[3], tileBase[4], palette, prio);
      gfxDrawPixel(&tileLine.pixels[4], tileBase[3], palette, prio);
      gfxDrawPixel(&tileLine.pixels[5], tileBase[2], palette, prio);
      gfxDrawPixel(&tileLine.pixels[6], tileBase[1], palette, prio);
      gfxDrawPixel(&tileLine.pixels[7], tileBase[0], palette, prio);
   }

   return tileLine;
}

static INLINE TileLine gfxReadTilePal(const uint16_t *screenSource, const int yyy, const uint8_t *charBase, uint16_t *palette, const uint32_t prio)
{
   int tileY;
   /* Zero-init suppresses a false-positive uninitialized warning; see
    * the matching note in gfxReadTile above. */
   TileLine tileLine = {{0}};
   TileEntry tile;
   const u8h *tileBase;
   tile.val = READ16LE(screenSource);

   tileY = yyy & 7;
   if (tile.vFlip) tileY = 7 - tileY;
   palette += tile.palette * 16;

   tileBase = (u8h*) &charBase[tile.tileNum * 32 + tileY * 4];

   if (!tile.hFlip)
   {
      gfxDrawPixel(&tileLine.pixels[0], tileBase[0].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[1], tileBase[0].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[2], tileBase[1].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[3], tileBase[1].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[4], tileBase[2].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[5], tileBase[2].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[6], tileBase[3].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[7], tileBase[3].hi, palette, prio);
   }
   else
   {
      gfxDrawPixel(&tileLine.pixels[0], tileBase[3].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[1], tileBase[3].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[2], tileBase[2].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[3], tileBase[2].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[4], tileBase[1].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[5], tileBase[1].lo, palette, prio);
      gfxDrawPixel(&tileLine.pixels[6], tileBase[0].hi, palette, prio);
      gfxDrawPixel(&tileLine.pixels[7], tileBase[0].lo, palette, prio);
   }

   return tileLine;
}

static INLINE void gfxDrawTile(TileLine tileLine, uint32_t* _line)
{
#if HAVE_NEON
   neon_memcpy(_line, tileLine.pixels, sizeof(tileLine.pixels));
#else
   memcpy(_line, tileLine.pixels, sizeof(tileLine.pixels));
#endif
}

static INLINE void gfxDrawTileClipped(TileLine tileLine, uint32_t* _line, const int start, int w)
{
#if HAVE_NEON
   neon_memcpy(_line, tileLine.pixels + start, w * sizeof(uint32_t));
#else
   memcpy(_line, tileLine.pixels + start, w * sizeof(uint32_t));
#endif
}

static void gfxDrawTextScreenImpl(TileReader readTile, int layer, int renderer_idx, uint16_t control, uint16_t hofs, uint16_t vofs)
{
	uint16_t * palette;
	uint8_t * charBase;
	uint16_t * screenBase;
	uint32_t prio;
	int sizeX;
	int sizeY;
	int maskX;
	int maskY;
	bool mosaicOn;
	int xxx;
	int yyy;
	int mosaicX;
	int mosaicY;
	int yshift;
	uint16_t * screenSource;
	int x;
	int firstTileX;
	INIT_RENDERER_CONTEXT(renderer_idx);

   palette = PAL_U16;
   charBase = &vram[((control >> 2) & 0x03) * 0x4000];
   screenBase = (uint16_t *)&vram[((control >> 8) & 0x1f) * 0x800];
   prio = ((control & 3)<<25) + 0x1000000;
   sizeX = 256;
   sizeY = 256;
   switch ((control >> 14) & 3)
   {
      case 0:
         break;
      case 1:
         sizeX = 512;
         break;
      case 2:
         sizeY = 512;
         break;
      case 3:
         sizeX = 512;
         sizeY = 512;
         break;
   }

   maskX = sizeX-1;
   maskY = sizeY-1;

   mosaicOn = (control & 0x40) ? true : false;

   xxx = hofs & maskX;
   yyy = (vofs + RENDERER_R_VCOUNT) & maskY;
   mosaicX = (RENDERER_MOSAIC & 0x000F)+1;
   mosaicY = ((RENDERER_MOSAIC & 0x00F0)>>4)+1;

   if (mosaicOn)
   {
      if ((RENDERER_R_VCOUNT % mosaicY) != 0)
      {
         mosaicY = RENDERER_R_VCOUNT - (RENDERER_R_VCOUNT % mosaicY);
         yyy = (vofs + mosaicY) & maskY;
      }
   }

   if (yyy > 255 && sizeY > 256)
   {
      yyy &= 255;
      screenBase += 0x400;
      if (sizeX > 256)
         screenBase += 0x400;
   }

   yshift = ((yyy>>3)<<5);

   screenSource = screenBase + 0x400 * (xxx>>8) + ((xxx & 255)>>3) + yshift;
   x = 0;
   firstTileX = xxx & 7;

   /* First tile, if clipped */
   if (firstTileX)
   {
      gfxDrawTileClipped(readTile(screenSource, yyy, charBase, palette, prio), &RENDERER_LINE[layer][x], firstTileX, 8 - firstTileX);
      screenSource++;
      x += 8 - firstTileX;
      xxx += 8 - firstTileX;

      if (xxx == 256 && sizeX > 256)
      {
         screenSource = screenBase + 0x400 + yshift;
      }
      else if (xxx >= sizeX)
      {
         xxx = 0;
         screenSource = screenBase + yshift;
      }
   }

   /* Middle tiles, full */
   while (x < 240 - firstTileX)
   {
      gfxDrawTile(readTile(screenSource, yyy, charBase, palette, prio), &RENDERER_LINE[layer][x]);
      screenSource++;
      xxx += 8;
      x += 8;

      if (xxx == 256 && sizeX > 256)
         screenSource = screenBase + 0x400 + yshift;
      else if (xxx >= sizeX)
      {
         xxx = 0;
         screenSource = screenBase + yshift;
      }
   }

   /* Last tile, if clipped */
   if (firstTileX)
      gfxDrawTileClipped(readTile(screenSource, yyy, charBase, palette, prio), &RENDERER_LINE[layer][x], 0, firstTileX);

   if (mosaicOn)
   {
      if (mosaicX > 1)
      {
		 MOSAIC_LOOP(layer, mosaicX);
      }
   }
}

static void gfxDrawTextScreen(int layer, int renderer_idx, uint16_t control, uint16_t hofs, uint16_t vofs)
{
   if (control & 0x80) /* 1 pal / 256 col */
      gfxDrawTextScreenImpl(gfxReadTile, layer, renderer_idx, control, hofs, vofs);
   else /* 16 pal / 16 col */
      gfxDrawTextScreenImpl(gfxReadTilePal, layer, renderer_idx, control, hofs, vofs);
}
#else

static INLINE void gfxDrawTextScreen(int layer, int renderer_idx, uint16_t control, uint16_t hofs, uint16_t vofs)
{
  uint16_t *palette;
  uint8_t *charBase = &vram[((control >> 2) & 0x03) * 0x4000];
  uint16_t *screenBase = (uint16_t *)&vram[((control >> 8) & 0x1f) * 0x800];
  uint32_t prio = ((control & 3)<<25) + 0x1000000;
  int sizeX = 256;
  int sizeY = 256;
  int maskX;
  int maskY;
  bool mosaicOn;
  int xxx;
  int yyy;
  int mosaicX;
  int mosaicY;
  int yshift;
  int x;
  uint16_t *screenSource;
  INIT_RENDERER_CONTEXT(renderer_idx);
  palette = PAL_U16;
  switch((control >> 14) & 3) {
  case 0:
    break;
  case 1:
    sizeX = 512;
    break;
  case 2:
    sizeY = 512;
    break;
  case 3:
    sizeX = 512;
    sizeY = 512;
    break;
  }

  maskX = sizeX-1;
  maskY = sizeY-1;

  mosaicOn = (control & 0x40) ? true : false;

  xxx = hofs & maskX;
  yyy = (vofs + RENDERER_R_VCOUNT) & maskY;
  mosaicX = (RENDERER_MOSAIC & 0x000F)+1;
  mosaicY = ((RENDERER_MOSAIC & 0x00F0)>>4)+1;

  if(mosaicOn) {
    if((RENDERER_R_VCOUNT % mosaicY) != 0) {
      mosaicY = RENDERER_R_VCOUNT - (RENDERER_R_VCOUNT % mosaicY);
      yyy = (vofs + mosaicY) & maskY;
    }
  }

  if(yyy > 255 && sizeY > 256) {
    yyy &= 255;
    screenBase += 0x400;
    if(sizeX > 256)
      screenBase += 0x400;
  }

  yshift = ((yyy>>3)<<5);
  if((control) & 0x80) {
    screenSource = screenBase + 0x400 * (xxx>>8) + ((xxx & 255)>>3) + yshift;
    for(x = 0; x < 240; x++) {
      uint16_t data = READ16LE(screenSource);
      int tile = data & 0x3FF;
      int tileX = (xxx & 7);
      int tileY = yyy & 7;
      uint8_t color;

      if(tileX == 7)
        screenSource++;

      if(data & 0x0400)
        tileX = 7 - tileX;
      if(data & 0x0800)
        tileY = 7 - tileY;

      color = charBase[tile * 64 + tileY * 8 + tileX];

      RENDERER_LINE[layer][x] = color ? (palette[color] | prio): 0x80000000;

      xxx++;
      if(xxx == 256) {
        if(sizeX > 256)
          screenSource = screenBase + 0x400 + yshift;
        else {
          screenSource = screenBase + yshift;
          xxx = 0;
        }
      } else if(xxx >= sizeX) {
        xxx = 0;
        screenSource = screenBase + yshift;
      }
    }
  } else {
    screenSource = screenBase + 0x400*(xxx>>8)+((xxx&255)>>3) +
      yshift;
    for(x = 0; x < 240; x++) {
      uint16_t data = READ16LE(screenSource);
      int tile = data & 0x3FF;
      int tileX = (xxx & 7);
      int tileY = yyy & 7;
      uint8_t color;
      int pal;

      if(tileX == 7)
        screenSource++;

      if(data & 0x0400)
        tileX = 7 - tileX;
      if(data & 0x0800)
        tileY = 7 - tileY;

      color = charBase[(tile<<5) + (tileY<<2) + (tileX>>1)];

      if(tileX & 1) {
        color = (color >> 4);
      } else {
        color &= 0x0F;
      }

      pal = (data>>8) & 0xF0;
      RENDERER_LINE[layer][x] = color ? (palette[pal + color]|prio): 0x80000000;

      xxx++;
      if(xxx == 256) {
        if(sizeX > 256)
          screenSource = screenBase + 0x400 + yshift;
        else {
          screenSource = screenBase + yshift;
          xxx = 0;
        }
      } else if(xxx >= sizeX) {
        xxx = 0;
        screenSource = screenBase + yshift;
      }
    }
  }
  if(mosaicOn) {
    if(mosaicX > 1) {
      MOSAIC_LOOP(layer, mosaicX);
    }
  }
}
#endif

static uint32_t map_sizes_rot[] = { 128, 256, 512, 1024 };

#if THREADED_RENDERER
static INLINE void fetchDrawRotScreen(uint16_t control, uint16_t x_l, uint16_t x_h, uint16_t y_l, uint16_t y_h, uint16_t pa, uint16_t pb, uint16_t pc, uint16_t pd, int *p_currentX, int *p_currentY, int changed)
{
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	/* Only dmx/dmy (per-line increments) are consumed here; dx/dy are per-pixel
	 * and live in the renderer thread. Single-cast sign-extension compiles to
	 * one extsh on PPC / sxth on ARM. */
	int dmx = (int)(int16_t)pb;
	int dmy = (int)(int16_t)pd;
	(void)pa; (void)pc; (void)control;

	if(io_registers[REG_VCOUNT] == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (x_l) | ((x_h & 0x07FF)<<16);
		if(x_h & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (y_l) | ((y_h & 0x07FF)<<16);
		if(y_h & 0x0800)
			currentY |= 0xF8000000;
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

static INLINE void fetchDrawRotScreen16Bit( int *p_currentX,  int *p_currentY, int changed)
{
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	int dmx = (int)(int16_t)io_registers[REG_BG2PB];
	int dmy = (int)(int16_t)io_registers[REG_BG2PD];

	if(io_registers[REG_VCOUNT] == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
		if(BG2X_H & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
		if(BG2Y_H & 0x0800)
			currentY |= 0xF8000000;
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

static INLINE void fetchDrawRotScreen256(int *p_currentX, int *p_currentY, int changed)
{
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	int dmx = (int)(int16_t)io_registers[REG_BG2PB];
	int dmy = (int)(int16_t)io_registers[REG_BG2PD];

	if(io_registers[REG_VCOUNT] == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
		if(BG2X_H & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
		if(BG2Y_H & 0x0800)
			currentY |= 0xF8000000;
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

static INLINE void fetchDrawRotScreen16Bit160(int *p_currentX, int *p_currentY, int changed)
{
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	int dmx = (int)(int16_t)io_registers[REG_BG2PB];
	int dmy = (int)(int16_t)io_registers[REG_BG2PD];

	if(io_registers[REG_VCOUNT] == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
		if(BG2X_H & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
		if(BG2Y_H & 0x0800)
			currentY |= 0xF8000000;
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}
#endif

static INLINE void gfxDrawRotScreen(int layer, int renderer_idx, uint16_t control, uint16_t x_l, uint16_t x_h, uint16_t y_l, uint16_t y_h,
uint16_t pa,  uint16_t pb, uint16_t pc,  uint16_t pd, int *p_currentX, int *p_currentY, int changed)
{
	uint16_t * palette;
	uint8_t * charBase;
	uint8_t * screenBase;
	int prio;
	uint32_t map_size;
	uint32_t sizeX;
	uint32_t sizeY;
	int maskX;
	int maskY;
	int yshift;
	int dx;
	int dmx;
	int dy;
	int dmy;
	int realX;
	int realY;
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	INIT_RENDERER_CONTEXT(renderer_idx);

	palette = PAL_U16;
	charBase = &vram[((control >> 2) & 0x03) << 14];
	screenBase = (uint8_t *)&vram[((control >> 8) & 0x1f) << 11];
	prio = ((control & 3) << 25) + 0x1000000;

	map_size = (control >> 14) & 3;
	sizeX = map_sizes_rot[map_size];
	sizeY = map_sizes_rot[map_size];

	maskX = sizeX-1;
	maskY = sizeY-1;

	yshift = ((control >> 14) & 3)+4;

	dx = (int)(int16_t)pa;
	dmx = (int)(int16_t)pb;
	dy = (int)(int16_t)pc;
	dmy = (int)(int16_t)pd;

	if(RENDERER_R_VCOUNT == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (x_l) | ((x_h & 0x07FF)<<16);
		if(x_h & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (y_l) | ((y_h & 0x07FF)<<16);
		if(y_h & 0x0800)
			currentY |= 0xF8000000;
	}

	realX = currentX;
	realY = currentY;

	if(control & 0x40)
	{
		int mosaicY = ((RENDERER_MOSAIC & 0xF0)>>4) + 1;
		int y = (RENDERER_R_VCOUNT % mosaicY);
		realX -= y*dmx;
		realY -= y*dmy;
	}

	memset(RENDERER_LINE[layer], -1, 240 * sizeof(uint32_t));
	if(control & 0x2000) /* Wraparound */
	{
		if(dx > 0 && dy == 0) /* Common subcase: no rotation or flipping */
		{
			unsigned yyy = (realY >> 8) & maskY;
			unsigned yyyshift = (yyy>>3)<<yshift;
			unsigned tileY = yyy & 7;
			unsigned tileYshift = (tileY<<3);

			{
				uint32_t x;
				for(x = 0; x < 240u; ++x)
			{
				unsigned xxx = (realX >> 8) & maskX;

				unsigned tile = screenBase[(xxx>>3) | yyyshift];

				unsigned tileX = (xxx & 7);

				uint8_t color = charBase[(tile<<6) | tileYshift | tileX];

				if(color) RENDERER_LINE[layer][x] = (palette[color]|prio);

				realX += dx;
			}
			}
		}
		else
			{
				uint32_t x;
				for(x = 0; x < 240u; ++x)
			{
				unsigned xxx = (realX >> 8) & maskX;
				unsigned yyy = (realY >> 8) & maskY;

				unsigned tile = screenBase[(xxx>>3) | ((yyy>>3)<<yshift)];

				unsigned tileX = (xxx & 7);
				unsigned tileY = yyy & 7;

				uint8_t color = charBase[(tile<<6) | (tileY<<3) | tileX];

				if(color) RENDERER_LINE[layer][x] = (palette[color]|prio);

				realX += dx;
				realY += dy;
			}
			}
	}
	else /* Culling */
	{
		if(dx > 0 && dy == 0) /* Common subcase: no rotation or flipping */
		{
			unsigned yyyshift;
			unsigned tileY;
			unsigned tileYshift;
			int32_t x0;
			int32_t x1;
			unsigned yyy = (realY >> 8);
			if (yyy >= sizeY)
				goto skipLine;
			yyyshift = (yyy>>3)<<yshift;
			tileY = yyy & 7;
			tileYshift = (tileY<<3);

			{
				int32_t a = (int32_t)(             + (-realX + dx - 1)) / dx;
				int32_t b = (int32_t)((sizeX << 8) + (-realX + dx - 1)) / dx;
				x0 = a >   0 ? a :   0;
				x1 = b < 240 ? b : 240;
			}

			realX += dx * x0;

			{
				int32_t x;
				for(x = x0; x < x1; ++x)
			{
				unsigned xxx = (realX >> 8);

				unsigned tile = screenBase[(xxx>>3) | yyyshift];

				unsigned tileX = (xxx & 7);

				uint8_t color = charBase[(tile<<6) | tileYshift | tileX];

				if(color) RENDERER_LINE[layer][x] = (palette[color]|prio);

				realX += dx;
			}
			}
		}
		else
			{
				uint32_t x;
				for(x = 0; x < 240u; ++x)
			{
				unsigned xxx = (realX >> 8);
				unsigned yyy = (realY >> 8);

				if(xxx < sizeX && yyy < sizeY)
				{
					unsigned tile = screenBase[(xxx>>3) | ((yyy>>3)<<yshift)];

					unsigned tileX = (xxx & 7);
					unsigned tileY = yyy & 7;

					uint8_t color = charBase[(tile<<6) | (tileY<<3) | tileX];

					if(color) RENDERER_LINE[layer][x] = (palette[color]|prio);
				}

				realX += dx;
				realY += dy;
			}
			}
	}
	skipLine:

	if(control & 0x40)
	{
		int mosaicX = (RENDERER_MOSAIC & 0xF) + 1;
		if(mosaicX > 1)
		{
			MOSAIC_LOOP(layer, mosaicX);
		}
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

static INLINE void gfxDrawRotScreen16Bit(int renderer_idx, int *p_currentX,  int *p_currentY, int changed)
{
	uint16_t * screenBase;
	int prio;
	uint32_t sizeX;
	uint32_t sizeY;
	int startX;
	int startY;
	int dx;
	int dmx;
	int dy;
	int dmy;
	int realX;
	int realY;
	unsigned xxx;
	unsigned yyy;
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	INIT_RENDERER_CONTEXT(renderer_idx);

	screenBase = (uint16_t *)&vram[0];
	prio = ((RENDERER_IO_REGISTERS[REG_BG2CNT] & 3) << 25) + 0x1000000;

	sizeX = 240;
	sizeY = 160;

	startX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
	if(BG2X_H & 0x0800)
		startX |= 0xF8000000;
	startY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
	if(BG2Y_H & 0x0800)
		startY |= 0xF8000000;

	dx = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PA];
	dmx = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PB];
	dy = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PC];
	dmy = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PD];

	if(RENDERER_R_VCOUNT == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
		if(BG2X_H & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
		if(BG2Y_H & 0x0800)
			currentY |= 0xF8000000;
	}

	realX = currentX;
	realY = currentY;

	if(RENDERER_IO_REGISTERS[REG_BG2CNT] & 0x40) {
		int mosaicY = ((RENDERER_MOSAIC & 0xF0)>>4) + 1;
		int y = (RENDERER_R_VCOUNT % mosaicY);
		realX -= y*dmx;
		realY -= y*dmy;
	}

	xxx = (realX >> 8);
	yyy = (realY >> 8);

	memset(RENDERER_LINE[Layer_BG2], -1, 240 * sizeof(uint32_t));
	{
		uint32_t x;
		for(x = 0; x < 240u; ++x)
	{
		if(xxx < sizeX && yyy < sizeY)
			RENDERER_LINE[Layer_BG2][x] = (READ16LE(&screenBase[yyy * sizeX + xxx]) | prio);

		realX += dx;
		realY += dy;

		xxx = (realX >> 8);
		yyy = (realY >> 8);
	}
	}

	if(RENDERER_IO_REGISTERS[REG_BG2CNT] & 0x40) {
		int mosaicX = (MOSAIC & 0xF) + 1;
		if(mosaicX > 1) {
			MOSAIC_LOOP(Layer_BG2, mosaicX);
		}
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

static INLINE void gfxDrawRotScreen256(int renderer_idx, int *p_currentX, int *p_currentY, int changed)
{
	uint16_t * palette;
	uint8_t * screenBase;
	int prio;
	uint32_t sizeX;
	uint32_t sizeY;
	int startX;
	int startY;
	int dx;
	int dmx;
	int dy;
	int dmy;
	int realX;
	int realY;
	int xxx;
	int yyy;
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	INIT_RENDERER_CONTEXT(renderer_idx);

	palette = PAL_U16;
	screenBase = (RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x0010) ? &vram[0xA000] : &vram[0x0000];
	prio = ((RENDERER_IO_REGISTERS[REG_BG2CNT] & 3) << 25) + 0x1000000;
	sizeX = 240;
	sizeY = 160;

	startX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
	if(BG2X_H & 0x0800)
		startX |= 0xF8000000;
	startY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
	if(BG2Y_H & 0x0800)
		startY |= 0xF8000000;

	dx = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PA];
	dmx = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PB];
	dy = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PC];
	dmy = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PD];

	if(RENDERER_R_VCOUNT == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
		if(BG2X_H & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
		if(BG2Y_H & 0x0800)
			currentY |= 0xF8000000;
	}

	realX = currentX;
	realY = currentY;

	if(RENDERER_IO_REGISTERS[REG_BG2CNT] & 0x40) {
		int mosaicY = ((RENDERER_MOSAIC & 0xF0)>>4) + 1;
		int y = RENDERER_R_VCOUNT - (RENDERER_R_VCOUNT % mosaicY);
		realX = startX + y*dmx;
		realY = startY + y*dmy;
	}

	xxx = (realX >> 8);
	yyy = (realY >> 8);

	memset(RENDERER_LINE[Layer_BG2], -1, 240 * sizeof(uint32_t));
	{
		uint32_t x;
		for(x = 0; x < 240; ++x)
	{
		if((unsigned)(xxx) < sizeX && (unsigned)(yyy) < sizeY) {
			uint8_t color = screenBase[yyy * 240 + xxx];
			if (color) RENDERER_LINE[Layer_BG2][x] = (palette[color] | prio);
		}
		realX += dx;
		realY += dy;

		xxx = (realX >> 8);
		yyy = (realY >> 8);
	}
	}

	if(RENDERER_IO_REGISTERS[REG_BG2CNT] & 0x40)
	{
		int mosaicX = (RENDERER_MOSAIC & 0xF) + 1;
		if(mosaicX > 1)
		{
			MOSAIC_LOOP(Layer_BG2, mosaicX);
		}
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

static INLINE void gfxDrawRotScreen16Bit160(int renderer_idx, int *p_currentX, int *p_currentY, int changed)
{
	uint16_t * screenBase;
	int prio;
	uint32_t sizeX;
	uint32_t sizeY;
	int startX;
	int startY;
	int dx;
	int dmx;
	int dy;
	int dmy;
	int realX;
	int realY;
	int xxx;
	int yyy;
	int mosaicX;
	int currentX = *p_currentX;
	int currentY = *p_currentY;
	INIT_RENDERER_CONTEXT(renderer_idx);

	screenBase = (RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x0010) ? (uint16_t *)&vram[0xa000] :
		(uint16_t *)&vram[0];
	prio = ((RENDERER_IO_REGISTERS[REG_BG2CNT] & 3) << 25) + 0x1000000;
	sizeX = 160;
	sizeY = 128;

	startX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
	if(BG2X_H & 0x0800)
		startX |= 0xF8000000;
	startY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
	if(BG2Y_H & 0x0800)
		startY |= 0xF8000000;

	dx = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PA];
	dmx = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PB];
	dy = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PC];
	dmy = (int)(int16_t)RENDERER_IO_REGISTERS[REG_BG2PD];

	if(RENDERER_R_VCOUNT == 0)
		changed = 3;

	currentX += dmx;
	currentY += dmy;

	if(changed & 1)
	{
		currentX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
		if(BG2X_H & 0x0800)
			currentX |= 0xF8000000;
	}

	if(changed & 2)
	{
		currentY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
		if(BG2Y_H & 0x0800)
			currentY |= 0xF8000000;
	}

	realX = currentX;
	realY = currentY;

	if(RENDERER_IO_REGISTERS[REG_BG2CNT] & 0x40) {
		int mosaicY = ((RENDERER_MOSAIC & 0xF0)>>4) + 1;
		int y = RENDERER_R_VCOUNT - (RENDERER_R_VCOUNT % mosaicY);
		realX = startX + y*dmx;
		realY = startY + y*dmy;
	}

	xxx = (realX >> 8);
	yyy = (realY >> 8);

	memset(RENDERER_LINE[Layer_BG2], -1, 240 * sizeof(uint32_t));
	{
		uint32_t x;
		for(x = 0; x < 240u; ++x)
	{
		if((unsigned)(xxx) < sizeX && (unsigned)(yyy) < sizeY)
			RENDERER_LINE[Layer_BG2][x] = (READ16LE(&screenBase[yyy * sizeX + xxx]) | prio);

		realX += dx;
		realY += dy;

		xxx = (realX >> 8);
		yyy = (realY >> 8);
	}
	}


	mosaicX = (RENDERER_MOSAIC & 0xF) + 1;
	if(RENDERER_IO_REGISTERS[REG_BG2CNT] & 0x40 && (mosaicX > 1))
	{
		MOSAIC_LOOP(Layer_BG2, mosaicX);
	}
	*p_currentX = currentX;
	*p_currentY = currentY;
}

/* lineOBJpix is used to keep track of the drawn OBJs
   and to stop drawing them if the 'maximum number of OBJ per line'
   has been reached. */

static void gfxDrawSprites (int renderer_idx)
{
	uint16_t * sprites;
	uint16_t * spritePalette;
	int mosaicY;
	int mosaicX;
	unsigned lineOBJpix, m;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineOBJpix = (RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x20) ? 954 : 1226;
	m = 0;

	sprites = OAM_U16;
	spritePalette = &PAL_U16[256];
	mosaicY = ((RENDERER_MOSAIC & 0xF000)>>12) + 1;
	mosaicX = ((RENDERER_MOSAIC & 0xF00)>>8) + 1;
	{
		uint32_t x;
		for(x = 0; x < 128; x++)
	{
		uint16_t a0val;
		uint32_t sizeX;
		uint32_t sizeY;
		int sy;
		int sx;
		uint16_t a0 = *sprites++;
		uint16_t a1 = *sprites++;
		uint16_t a2 = *sprites++;
		++sprites;

		RENDERER_LINE_OBJ_PIX_LEFT[x]=lineOBJpix;

		lineOBJpix-=2;
		if (lineOBJpix<=0)
			return;

		if ((a0 & 0x0c00) == 0x0c00)
			a0 &=0xF3FF;

		a0val = a0>>14;

		if (a0val == 3)
		{
			a0 &= 0x3FFF;
			a1 &= 0x3FFF;
		}

		sizeX = 8<<(a1>>14);
		sizeY = sizeX;


		if (a0val & 1)
		{
#ifdef BRANCHLESS_GBA_GFX
			sizeX <<= isel(-(sizeX & (~31u)), 1, 0);
			sizeY >>= isel(-(sizeY>8), 0, 1);
#else
			if (sizeX<32)
				sizeX<<=1;
			if (sizeY>8)
				sizeY>>=1;
#endif
		}
		else if (a0val & 2)
		{
#ifdef BRANCHLESS_GBA_GFX
			sizeX >>= isel(-(sizeX > 8), 0, 1);
			sizeY <<= isel(-(sizeY & (~31u)), 1, 0);
#else
			if (sizeX > 8)
				sizeX >>= 1;
			if (sizeY < 32)
				sizeY <<= 1;
#endif

		}


		sy = (a0 & 255);
		sx = (a1 & 0x1FF);

		/* computes ticks used by OBJ-WIN if OBJWIN is enabled */
		if (((a0 & 0x0c00) == 0x0800) && (RENDERER_R_DISPCNT_OBJ_Window_Display))
		{
			if ((a0 & 0x0300) == 0x0300)
			{
				sizeX<<=1;
				sizeY<<=1;
			}

#ifdef BRANCHLESS_GBA_GFX
			sy -= isel(256 - sy - sizeY, 0, 256);
			sx -= isel(512 - sx - sizeX, 0, 512);
#else
			if((sy+sizeY) > 256)
				sy -= 256;
			if ((sx+sizeX)> 512)
				sx -= 512;
#endif

			if (sx < 0)
			{
				sizeX+=sx;
				sx = 0;
			}
			else if ((sx+sizeX)>240)
				sizeX=240-sx;

			if ((RENDERER_R_VCOUNT>=sy) && (RENDERER_R_VCOUNT<sy+sizeY) && (sx<240))
			{
				lineOBJpix -= (sizeX-2);

				if (a0 & 0x0100)
					lineOBJpix -= (10+sizeX);
			}
			continue;
		}

		/* else ignores OBJ-WIN if OBJWIN is disabled, and ignored disabled OBJ */
		else if(((a0 & 0x0c00) == 0x0800) || ((a0 & 0x0300) == 0x0200))
			continue;

		if(a0 & 0x0100)
		{
			int t;
			uint32_t fieldX = sizeX;
			uint32_t fieldY = sizeY;
			if(a0 & 0x0200)
			{
				fieldX <<= 1;
				fieldY <<= 1;
			}
			if((sy+fieldY) > 256)
				sy -= 256;
			t = RENDERER_R_VCOUNT - sy;
			if((unsigned)(t) < fieldY)
			{
				uint32_t startpix = 0;
				if ((sx+fieldX)> 512)
					startpix=512-sx;

				if (lineOBJpix && ((sx < 240) || startpix))
				{
					int rot;
					uint16_t * OAM;
					int dx;
					int dmx;
					int dy;
					int dmy;
					int realX;
					int realY;
					uint32_t prio;
					int c;
					lineOBJpix-=8;
					rot = (((a1 >> 9) & 0x1F) << 4);
					OAM = OAM_U16;
					dx = (int)(int16_t)OAM[3 + rot];
					dmx = (int)(int16_t)OAM[7 + rot];
					dy = (int)(int16_t)OAM[11 + rot];
					dmy = (int)(int16_t)OAM[15 + rot];

					if(a0 & 0x1000)
						t -= (t % mosaicY);

					realX = ((sizeX) << 7) - (fieldX >> 1)*dx + ((t - (fieldY>>1))* dmx);
					realY = ((sizeY) << 7) - (fieldX >> 1)*dy + ((t - (fieldY>>1))* dmy);

					prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);

					c = (a2 & 0x3FF);
					if(RENDERER_R_DISPCNT_Video_Mode > 2 && (c < 512))
						continue;

					if(a0 & 0x2000)
					{
						int inc = 32;
						if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
							inc = sizeX >> 2;
						else
							c &= 0x3FE;
						{
							uint32_t x;
							for(x = 0; x < fieldX; x++)
						{
							unsigned xxx;
							unsigned yyy;
							if (x >= startpix)
								lineOBJpix-=2;
							xxx = realX >> 8;
							yyy = realY >> 8;
							if(xxx < sizeX && yyy < sizeY && sx < 240)
							{

								uint32_t color = vram[0x10000 + ((((c + (yyy>>3) * inc)<<5)
								+ ((yyy & 7)<<3) + ((xxx >> 3)<<6) + (xxx & 7))&0x7FFF)];

								if ((color==0) && (((prio >> 25)&3) < ((RENDERER_LINE[Layer_OBJ][sx]>>25)&3)))
								{
									RENDERER_LINE[Layer_OBJ][sx] = (RENDERER_LINE[Layer_OBJ][sx] & 0xF9FFFFFF) | prio;
									if((a0 & 0x1000) && m)
										RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
								}
								else if((color) && (prio < (RENDERER_LINE[Layer_OBJ][sx]&0xFF000000)))
								{
									RENDERER_LINE[Layer_OBJ][sx] = spritePalette[color] | prio;
									if((a0 & 0x1000) && m)
										RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
								}

								if ((a0 & 0x1000) && ((m+1) == mosaicX))
									m = 0;
							}
							sx = (sx+1)&511;
							realX += dx;
							realY += dy;
						}
						}
					}
					else
					{
						int palette;
						int inc = 32;
						if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
							inc = sizeX >> 3;
						palette = (a2 >> 8) & 0xF0;
						{
							uint32_t x;
							for(x = 0; x < fieldX; ++x)
						{
							unsigned xxx;
							unsigned yyy;
							if (x >= startpix)
								lineOBJpix-=2;
							xxx = realX >> 8;
							yyy = realY >> 8;
							if(xxx < sizeX && yyy < sizeY && sx < 240)
							{

								uint32_t color = vram[0x10000 + ((((c + (yyy>>3) * inc)<<5)
											+ ((yyy & 7)<<2) + ((xxx >> 3)<<5)
											+ ((xxx & 7)>>1))&0x7FFF)];
								if(xxx & 1)
									color >>= 4;
								else
									color &= 0x0F;

								if ((color==0) && (((prio >> 25)&3) <
											((RENDERER_LINE[Layer_OBJ][sx]>>25)&3)))
								{
									RENDERER_LINE[Layer_OBJ][sx] = (RENDERER_LINE[Layer_OBJ][sx] & 0xF9FFFFFF) | prio;
									if((a0 & 0x1000) && m)
										RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
								}
								else if((color) && (prio < (RENDERER_LINE[Layer_OBJ][sx]&0xFF000000)))
								{
									RENDERER_LINE[Layer_OBJ][sx] = spritePalette[palette+color] | prio;
									if((a0 & 0x1000) && m)
										RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
								}
							}
							if((a0 & 0x1000) && m)
							{
								if (++m==mosaicX)
									m=0;
							}

							sx = (sx+1)&511;
							realX += dx;
							realY += dy;

						}
						}
					}
				}
			}
		}
		else
		{
			int t;
			if(sy+sizeY > 256)
				sy -= 256;
			t = RENDERER_R_VCOUNT - sy;
			if((unsigned)(t) < sizeY)
			{
				uint32_t startpix = 0;
				if ((sx+sizeX)> 512)
					startpix=512-sx;

				if((sx < 240) || startpix)
				{
					int c;
					int inc;
					int xxx;
					lineOBJpix+=2;

					if(a1 & 0x2000)
						t = sizeY - t - 1;

					c = (a2 & 0x3FF);
					if(RENDERER_R_DISPCNT_Video_Mode > 2 && (c < 512))
						continue;

					inc = 32;
					xxx = 0;
					if(a1 & 0x1000)
						xxx = sizeX-1;

					if(a0 & 0x1000)
						t -= (t % mosaicY);

					if(a0 & 0x2000)
					{
						int address;
						uint32_t prio;
						if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
							inc = sizeX >> 2;
						else
							c &= 0x3FE;

						address = 0x10000 + ((((c+ (t>>3) * inc) << 5)
									+ ((t & 7) << 3) + ((xxx>>3)<<6) + (xxx & 7)) & 0x7FFF);

						if(a1 & 0x1000)
							xxx = 7;
						prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);

						{
							uint32_t xx;
							for(xx = 0; xx < sizeX; xx++)
						{
							if (xx >= startpix)
								--lineOBJpix;
							if(sx < 240)
							{
								uint8_t color = vram[address];
								if ((color==0) && (((prio >> 25)&3) <
											((RENDERER_LINE[Layer_OBJ][sx]>>25)&3)))
								{
									RENDERER_LINE[Layer_OBJ][sx] = (RENDERER_LINE[Layer_OBJ][sx] & 0xF9FFFFFF) | prio;
									if((a0 & 0x1000) && m)
										RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
								}
								else if((color) && (prio < (RENDERER_LINE[Layer_OBJ][sx]&0xFF000000)))
								{
									RENDERER_LINE[Layer_OBJ][sx] = spritePalette[color] | prio;
									if((a0 & 0x1000) && m)
										RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
								}

								if ((a0 & 0x1000) && ((m+1) == mosaicX))
									m = 0;
							}

							sx = (sx+1) & 511;
							if(a1 & 0x1000)
							{
								--address;
								if(--xxx == -1)
								{
									address -= 56;
									xxx = 7;
								}
								if(address < 0x10000)
									address += 0x8000;
							}
							else
							{
								++address;
								if(++xxx == 8)
								{
									address += 56;
									xxx = 0;
								}
								if(address > 0x17fff)
									address -= 0x8000;
							}
						}
						}
					}
					else
					{
						int address;
						uint32_t prio;
						int palette;
						if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
							inc = sizeX >> 3;

						address = 0x10000 + ((((c + (t>>3) * inc)<<5)
									+ ((t & 7)<<2) + ((xxx>>3)<<5) + ((xxx & 7) >> 1))&0x7FFF);

						prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);
						palette = (a2 >> 8) & 0xF0;
						if(a1 & 0x1000)
						{
							int xx;
							xxx = 7;
							xx = sizeX - 1;
							do
							{
								if (xx >= (int)(startpix))
									--lineOBJpix;
								/*if (lineOBJpix<0) */
								/*  continue; */
								if(sx < 240)
								{
									uint8_t color = vram[address];
									if(xx & 1)
										color >>= 4;
									else
										color &= 0x0F;

									if ((color==0) && (((prio >> 25)&3) <
												((RENDERER_LINE[Layer_OBJ][sx]>>25)&3)))
									{
										RENDERER_LINE[Layer_OBJ][sx] = (RENDERER_LINE[Layer_OBJ][sx] & 0xF9FFFFFF) | prio;
										if((a0 & 0x1000) && m)
											RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
									}
									else if((color) && (prio < (RENDERER_LINE[Layer_OBJ][sx]&0xFF000000)))
									{
										RENDERER_LINE[Layer_OBJ][sx] = spritePalette[palette + color] | prio;
										if((a0 & 0x1000) && m)
											RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
									}
								}

								if ((a0 & 0x1000) && ((m+1) == mosaicX))
									m=0;

								sx = (sx+1) & 511;
								if(!(xx & 1))
									--address;
								if(--xxx == -1)
								{
									xxx = 7;
									address -= 28;
								}
								if(address < 0x10000)
									address += 0x8000;
							}while(--xx >= 0);
						}
						else
						{
							{
								uint32_t xx;
								for(xx = 0; xx < sizeX; ++xx)
							{
								if (xx >= startpix)
									--lineOBJpix;
								/*if (lineOBJpix<0) */
								/*  continue; */
								if(sx < 240)
								{
									uint8_t color = vram[address];
									if(xx & 1)
										color >>= 4;
									else
										color &= 0x0F;

									if ((color==0) && (((prio >> 25)&3) <
												((RENDERER_LINE[Layer_OBJ][sx]>>25)&3)))
									{
										RENDERER_LINE[Layer_OBJ][sx] = (RENDERER_LINE[Layer_OBJ][sx] & 0xF9FFFFFF) | prio;
										if((a0 & 0x1000) && m)
											RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;
									}
									else if((color) && (prio < (RENDERER_LINE[Layer_OBJ][sx]&0xFF000000)))
									{
										RENDERER_LINE[Layer_OBJ][sx] = spritePalette[palette + color] | prio;
										if((a0 & 0x1000) && m)
											RENDERER_LINE[Layer_OBJ][sx]=(RENDERER_LINE[Layer_OBJ][sx-1] & 0xF9FFFFFF) | prio;

									}
								}
								if ((a0 & 0x1000) && ((m+1) == mosaicX))
									m=0;

								sx = (sx+1) & 511;
								if(xx & 1)
									++address;
								if(++xxx == 8)
								{
									address += 28;
									xxx = 0;
								}
								if(address > 0x17fff)
									address -= 0x8000;
							}
							}
						}
					}
				}
			}
		}
	}
	}
}

static void gfxDrawOBJWin (int renderer_idx)
{
	uint16_t * sprites;
	INIT_RENDERER_CONTEXT(renderer_idx);

	sprites = OAM_U16;
	{
		int x;
		for(x = 0; x < 128 ; x++)
	{
		uint16_t a0val;
		int sizeX;
		int sizeY;
		int sy;
		int lineOBJpix = RENDERER_LINE_OBJ_PIX_LEFT[x];
		uint16_t a0 = *sprites++;
		uint16_t a1 = *sprites++;
		uint16_t a2 = *sprites++;
		sprites++;

		if (lineOBJpix<=0)
			return;

		/* ignores non OBJ-WIN and disabled OBJ-WIN */
		if(((a0 & 0x0c00) != 0x0800) || ((a0 & 0x0300) == 0x0200))
			continue;

		a0val = a0>>14;

		if ((a0 & 0x0c00) == 0x0c00)
			a0 &=0xF3FF;

		if (a0val == 3)
		{
			a0 &= 0x3FFF;
			a1 &= 0x3FFF;
		}

		sizeX = 8<<(a1>>14);
		sizeY = sizeX;

		if (a0val & 1)
		{
#ifdef BRANCHLESS_GBA_GFX
			sizeX <<= isel(-(sizeX & (~31u)), 1, 0);
			sizeY >>= isel(-(sizeY>8), 0, 1);
#else
			if (sizeX<32)
				sizeX<<=1;
			if (sizeY>8)
				sizeY>>=1;
#endif
		}
		else if (a0val & 2)
		{
#ifdef BRANCHLESS_GBA_GFX
			sizeX >>= isel(-(sizeX>8), 0, 1);
			sizeY <<= isel(-(sizeY & (~31u)), 1, 0);
#else
			if (sizeX>8)
				sizeX>>=1;
			if (sizeY<32)
				sizeY<<=1;
#endif

		}

		sy = (a0 & 255);

		if(a0 & 0x0100)
		{
			int t;
			int fieldX = sizeX;
			int fieldY = sizeY;
			if(a0 & 0x0200)
			{
				fieldX <<= 1;
				fieldY <<= 1;
			}
			if((sy+fieldY) > 256)
				sy -= 256;
			t = RENDERER_R_VCOUNT - sy;
			if((t >= 0) && (t < fieldY))
			{
				int sx = (a1 & 0x1FF);
				int startpix = 0;
				if ((sx+fieldX)> 512)
					startpix=512-sx;

				if((sx < 240) || startpix)
				{
					int rot;
					uint16_t * OAM;
					int dx;
					int dmx;
					int dy;
					int dmy;
					int realX;
					int realY;
					int c;
					int inc;
					bool condition1;
					lineOBJpix-=8;
					/* int t2 = t - (fieldY >> 1); */
					rot = (a1 >> 9) & 0x1F;
					OAM = OAM_U16;
					dx = OAM[3 + (rot << 4)];
					if(dx & 0x8000)
						dx |= 0xFFFF8000;
					dmx = OAM[7 + (rot << 4)];
					if(dmx & 0x8000)
						dmx |= 0xFFFF8000;
					dy = OAM[11 + (rot << 4)];
					if(dy & 0x8000)
						dy |= 0xFFFF8000;
					dmy = OAM[15 + (rot << 4)];
					if(dmy & 0x8000)
						dmy |= 0xFFFF8000;

					realX = ((sizeX) << 7) - (fieldX >> 1)*dx - (fieldY>>1)*dmx
						+ t * dmx;
					realY = ((sizeY) << 7) - (fieldX >> 1)*dy - (fieldY>>1)*dmy
						+ t * dmy;

					c = (a2 & 0x3FF);
					if(RENDERER_R_DISPCNT_Video_Mode > 2 && (c < 512))
						continue;

					inc = 32;
					condition1 = a0 & 0x2000;

					if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
						inc = sizeX >> 3;

					{
						int x;
						for(x = 0; x < fieldX; x++)
					{
						int xxx;
						int yyy;
						bool cont = true;
						if (x >= startpix)
							lineOBJpix-=2;
						if (lineOBJpix<0)
							continue;
						xxx = realX >> 8;
						yyy = realY >> 8;

						if(xxx < 0 || xxx >= sizeX || yyy < 0 || yyy >= sizeY || sx >= 240)
							cont = false;

						if(cont)
						{
							uint32_t color;
							if(condition1)
								color = vram[0x10000 + ((((c + (yyy>>3) * inc)<<5)
											+ ((yyy & 7)<<3) + ((xxx >> 3)<<6) +
											(xxx & 7))&0x7fff)];
							else
							{
								color = vram[0x10000 + ((((c + (yyy>>3) * inc)<<5)
											+ ((yyy & 7)<<2) + ((xxx >> 3)<<5) +
											((xxx & 7)>>1))&0x7fff)];
								if(xxx & 1)
									color >>= 4;
								else
									color &= 0x0F;
							}

							if(color)
								RENDERER_LINE[Layer_WIN_OBJ][sx] = 1;
						}
						sx = (sx+1)&511;
						realX += dx;
						realY += dy;
					}
					}
				}
			}
		}
		else
		{
			int t;
			if((sy+sizeY) > 256)
				sy -= 256;
			t = RENDERER_R_VCOUNT - sy;
			if((t >= 0) && (t < sizeY))
			{
				int sx = (a1 & 0x1FF);
				int startpix = 0;
				if ((sx+sizeX)> 512)
					startpix=512-sx;

				if((sx < 240) || startpix)
				{
					int c;
					lineOBJpix+=2;
					if(a1 & 0x2000)
						t = sizeY - t - 1;
					c = (a2 & 0x3FF);
					if(RENDERER_R_DISPCNT_Video_Mode > 2 && (c < 512))
						continue;
					if(a0 & 0x2000)
					{
int xxx;
int address;

						int inc = 32;
						if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
							inc = sizeX >> 2;
						else
							c &= 0x3FE;

						xxx = 0;
						if(a1 & 0x1000)
							xxx = sizeX-1;
						address = 0x10000 + ((((c+ (t>>3) * inc) << 5)
									+ ((t & 7) << 3) + ((xxx>>3)<<6) + (xxx & 7))&0x7fff);
						if(a1 & 0x1000)
							xxx = 7;
						{
							int xx;
							for(xx = 0; xx < sizeX; xx++)
						{
							if (xx >= startpix)
								lineOBJpix--;
							if (lineOBJpix<0)
								continue;
							if(sx < 240)
							{
								uint8_t color = vram[address];
								if(color)
									RENDERER_LINE[Layer_WIN_OBJ][sx] = 1;
							}

							sx = (sx+1) & 511;
							if(a1 & 0x1000) {
								xxx--;
								address--;
								if(xxx == -1) {
									address -= 56;
									xxx = 7;
								}
								if(address < 0x10000)
									address += 0x8000;
							} else {
								xxx++;
								address++;
								if(xxx == 8) {
									address += 56;
									xxx = 0;
								}
								if(address > 0x17fff)
									address -= 0x8000;
							}
						}
						}
					}
					else
					{
						int xxx;
						int address;
						int inc = 32;
						if(RENDERER_IO_REGISTERS[REG_DISPCNT] & 0x40)
							inc = sizeX >> 3;
						xxx = 0;
						if(a1 & 0x1000)
							xxx = sizeX - 1;
						address = 0x10000 + ((((c + (t>>3) * inc)<<5)
									+ ((t & 7)<<2) + ((xxx>>3)<<5) + ((xxx & 7) >> 1))&0x7fff);
						/* uint32_t prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6); */
						/* int palette = (a2 >> 8) & 0xF0; */
						if(a1 & 0x1000)
						{
							xxx = 7;
							{
								int xx;
								for(xx = sizeX - 1; xx >= 0; xx--)
							{
								if (xx >= startpix)
									lineOBJpix--;
								if (lineOBJpix<0)
									continue;
								if(sx < 240)
								{
									uint8_t color = vram[address];
									if(xx & 1)
										color = (color >> 4);
									else
										color &= 0x0F;

									if(color)
										RENDERER_LINE[Layer_WIN_OBJ][sx] = 1;
								}
								sx = (sx+1) & 511;
								xxx--;
								if(!(xx & 1))
									address--;
								if(xxx == -1) {
									xxx = 7;
									address -= 28;
								}
								if(address < 0x10000)
									address += 0x8000;
							}
							}
						}
						else
						{
							{
								int xx;
								for(xx = 0; xx < sizeX; xx++)
							{
								if (xx >= startpix)
									lineOBJpix--;
								if (lineOBJpix<0)
									continue;
								if(sx < 240)
								{
									uint8_t color = vram[address];
									if(xx & 1)
										color = (color >> 4);
									else
										color &= 0x0F;

									if(color)
										RENDERER_LINE[Layer_WIN_OBJ][sx] = 1;
								}
								sx = (sx+1) & 511;
								xxx++;
								if(xx & 1)
									address++;
								if(xxx == 8) {
									address += 28;
									xxx = 0;
								}
								if(address > 0x17fff)
									address -= 0x8000;
							}
							}
						}
					}
				}
			}
		}
	}
	}
}

/*============================================================
	GBA.CPP
============================================================ */
int saveType = 0;
bool useBios = false;
bool skipBios = false;
int cpuSaveType = 0;
bool enableRtc = false;
bool mirroringEnable = false;
bool skipSaveGameBattery = false;


bool cpuSramEnabled = true;
bool cpuFlashEnabled = true;
bool cpuEEPROMEnabled = true;

#ifdef MSB_FIRST
bool cpuBiosSwapped = false;
#endif

uint32_t myROM[] = {
0xEA000006,
0xEA000093,
0xEA000006,
0x00000000,
0x00000000,
0x00000000,
0xEA000088,
0x00000000,
0xE3A00302,
0xE1A0F000,
0xE92D5800,
0xE55EC002,
0xE28FB03C,
0xE79BC10C,
0xE14FB000,
0xE92D0800,
0xE20BB080,
0xE38BB01F,
0xE129F00B,
0xE92D4004,
0xE1A0E00F,
0xE12FFF1C,
0xE8BD4004,
0xE3A0C0D3,
0xE129F00C,
0xE8BD0800,
0xE169F00B,
0xE8BD5800,
0xE1B0F00E,
0x0000009C,
0x0000009C,
0x0000009C,
0x0000009C,
0x000001F8,
0x000001F0,
0x000000AC,
0x000000A0,
0x000000FC,
0x00000168,
0xE12FFF1E,
0xE1A03000,
0xE1A00001,
0xE1A01003,
0xE2113102,
0x42611000,
0xE033C040,
0x22600000,
0xE1B02001,
0xE15200A0,
0x91A02082,
0x3AFFFFFC,
0xE1500002,
0xE0A33003,
0x20400002,
0xE1320001,
0x11A020A2,
0x1AFFFFF9,
0xE1A01000,
0xE1A00003,
0xE1B0C08C,
0x22600000,
0x42611000,
0xE12FFF1E,
0xE92D0010,
0xE1A0C000,
0xE3A01001,
0xE1500001,
0x81A000A0,
0x81A01081,
0x8AFFFFFB,
0xE1A0000C,
0xE1A04001,
0xE3A03000,
0xE1A02001,
0xE15200A0,
0x91A02082,
0x3AFFFFFC,
0xE1500002,
0xE0A33003,
0x20400002,
0xE1320001,
0x11A020A2,
0x1AFFFFF9,
0xE0811003,
0xE1B010A1,
0xE1510004,
0x3AFFFFEE,
0xE1A00004,
0xE8BD0010,
0xE12FFF1E,
0xE0010090,
0xE1A01741,
0xE2611000,
0xE3A030A9,
0xE0030391,
0xE1A03743,
0xE2833E39,
0xE0030391,
0xE1A03743,
0xE2833C09,
0xE283301C,
0xE0030391,
0xE1A03743,
0xE2833C0F,
0xE28330B6,
0xE0030391,
0xE1A03743,
0xE2833C16,
0xE28330AA,
0xE0030391,
0xE1A03743,
0xE2833A02,
0xE2833081,
0xE0030391,
0xE1A03743,
0xE2833C36,
0xE2833051,
0xE0030391,
0xE1A03743,
0xE2833CA2,
0xE28330F9,
0xE0000093,
0xE1A00840,
0xE12FFF1E,
0xE3A00001,
0xE3A01001,
0xE92D4010,
0xE3A03000,
0xE3A04001,
0xE3500000,
0x1B000004,
0xE5CC3301,
0xEB000002,
0x0AFFFFFC,
0xE8BD4010,
0xE12FFF1E,
0xE3A0C301,
0xE5CC3208,
0xE15C20B8,
0xE0110002,
0x10222000,
0x114C20B8,
0xE5CC4208,
0xE12FFF1E,
0xE92D500F,
0xE3A00301,
0xE1A0E00F,
0xE510F004,
0xE8BD500F,
0xE25EF004,
0xE59FD044,
0xE92D5000,
0xE14FC000,
0xE10FE000,
0xE92D5000,
0xE3A0C302,
0xE5DCE09C,
0xE35E00A5,
0x1A000004,
0x05DCE0B4,
0x021EE080,
0xE28FE004,
0x159FF018,
0x059FF018,
0xE59FD018,
0xE8BD5000,
0xE169F00C,
0xE8BD5000,
0xE25EF004,
0x03007FF0,
0x09FE2000,
0x09FFC000,
0x03007FE0
};

static variable_desc saveGameStruct[] = {
	{ &io_registers[REG_DISPCNT]  , sizeof(uint16_t) },
	{ &io_registers[REG_DISPSTAT] , sizeof(uint16_t) },
	{ &io_registers[REG_VCOUNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_BG0CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_BG1CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_BG2CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_BG3CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_BG0HOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG0VOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG1HOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG1VOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG2HOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG2VOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG3HOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG3VOFS]  , sizeof(uint16_t) },
	{ &io_registers[REG_BG2PA]    , sizeof(uint16_t) },
	{ &io_registers[REG_BG2PB]    , sizeof(uint16_t) },
	{ &io_registers[REG_BG2PC]    , sizeof(uint16_t) },
	{ &io_registers[REG_BG2PD]    , sizeof(uint16_t) },
	{ &BG2X_L   , sizeof(uint16_t) },
	{ &BG2X_H   , sizeof(uint16_t) },
	{ &BG2Y_L   , sizeof(uint16_t) },
	{ &BG2Y_H   , sizeof(uint16_t) },
	{ &io_registers[REG_BG3PA]    , sizeof(uint16_t) },
	{ &io_registers[REG_BG3PB]    , sizeof(uint16_t) },
	{ &io_registers[REG_BG3PC]    , sizeof(uint16_t) },
	{ &io_registers[REG_BG3PD]    , sizeof(uint16_t) },
	{ &BG3X_L   , sizeof(uint16_t) },
	{ &BG3X_H   , sizeof(uint16_t) },
	{ &BG3Y_L   , sizeof(uint16_t) },
	{ &BG3Y_H   , sizeof(uint16_t) },
	{ &io_registers[REG_WIN0H]    , sizeof(uint16_t) },
	{ &io_registers[REG_WIN1H]    , sizeof(uint16_t) },
	{ &io_registers[REG_WIN0V]    , sizeof(uint16_t) },
	{ &io_registers[REG_WIN1V]    , sizeof(uint16_t) },
	{ &io_registers[REG_WININ]    , sizeof(uint16_t) },
	{ &io_registers[REG_WINOUT]   , sizeof(uint16_t) },
	{ &MOSAIC   , sizeof(uint16_t) },
	{ &BLDMOD   , sizeof(uint16_t) },
	{ &COLEV    , sizeof(uint16_t) },
	{ &COLY     , sizeof(uint16_t) },
	{ &DM0SAD_L , sizeof(uint16_t) },
	{ &DM0SAD_H , sizeof(uint16_t) },
	{ &DM0DAD_L , sizeof(uint16_t) },
	{ &DM0DAD_H , sizeof(uint16_t) },
	{ &DM0CNT_L , sizeof(uint16_t) },
	{ &DM0CNT_H , sizeof(uint16_t) },
	{ &DM1SAD_L , sizeof(uint16_t) },
	{ &DM1SAD_H , sizeof(uint16_t) },
	{ &DM1DAD_L , sizeof(uint16_t) },
	{ &DM1DAD_H , sizeof(uint16_t) },
	{ &DM1CNT_L , sizeof(uint16_t) },
	{ &DM1CNT_H , sizeof(uint16_t) },
	{ &DM2SAD_L , sizeof(uint16_t) },
	{ &DM2SAD_H , sizeof(uint16_t) },
	{ &DM2DAD_L , sizeof(uint16_t) },
	{ &DM2DAD_H , sizeof(uint16_t) },
	{ &DM2CNT_L , sizeof(uint16_t) },
	{ &DM2CNT_H , sizeof(uint16_t) },
	{ &DM3SAD_L , sizeof(uint16_t) },
	{ &DM3SAD_H , sizeof(uint16_t) },
	{ &DM3DAD_L , sizeof(uint16_t) },
	{ &DM3DAD_H , sizeof(uint16_t) },
	{ &DM3CNT_L , sizeof(uint16_t) },
	{ &DM3CNT_H , sizeof(uint16_t) },
	{ &io_registers[REG_TM0D]     , sizeof(uint16_t) },
	{ &io_registers[REG_TM0CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_TM1D]     , sizeof(uint16_t) },
	{ &io_registers[REG_TM1CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_TM2D]     , sizeof(uint16_t) },
	{ &io_registers[REG_TM2CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_TM3D]     , sizeof(uint16_t) },
	{ &io_registers[REG_TM3CNT]   , sizeof(uint16_t) },
	{ &io_registers[REG_P1]       , sizeof(uint16_t) },
	{ &io_registers[REG_IE]       , sizeof(uint16_t) },
	{ &io_registers[REG_IF]       , sizeof(uint16_t) },
	{ &io_registers[REG_IME]      , sizeof(uint16_t) },
	{ &holdState, sizeof(bool) },
	{ &graphics.lcdTicks, sizeof(int) },
	{ &timer0On , sizeof(bool) },
	{ &timer0Ticks , sizeof(int) },
	{ &timer0Reload , sizeof(int) },
	{ &timer0ClockReload  , sizeof(int) },
	{ &timer1On , sizeof(bool) },
	{ &timer1Ticks , sizeof(int) },
	{ &timer1Reload , sizeof(int) },
	{ &timer1ClockReload  , sizeof(int) },
	{ &timer2On , sizeof(bool) },
	{ &timer2Ticks , sizeof(int) },
	{ &timer2Reload , sizeof(int) },
	{ &timer2ClockReload  , sizeof(int) },
	{ &timer3On , sizeof(bool) },
	{ &timer3Ticks , sizeof(int) },
	{ &timer3Reload , sizeof(int) },
	{ &timer3ClockReload  , sizeof(int) },
	{ &dma0Source , sizeof(uint32_t) },
	{ &dma0Dest , sizeof(uint32_t) },
	{ &dma1Source , sizeof(uint32_t) },
	{ &dma1Dest , sizeof(uint32_t) },
	{ &dma2Source , sizeof(uint32_t) },
	{ &dma2Dest , sizeof(uint32_t) },
	{ &dma3Source , sizeof(uint32_t) },
	{ &dma3Dest , sizeof(uint32_t) },
	{ &fxOn, sizeof(bool) },
	{ &windowOn, sizeof(bool) },
	{ &N_FLAG , sizeof(bool) },
	{ &C_FLAG , sizeof(bool) },
	{ &Z_FLAG , sizeof(bool) },
	{ &V_FLAG , sizeof(bool) },
	{ &armState , sizeof(bool) },
	{ &armIrqEnable , sizeof(bool) },
	{ &bus.armNextPC , sizeof(uint32_t) },
	{ &armMode , sizeof(int) },
	{ &saveType , sizeof(int) },
	{ NULL, 0 }
};

static INLINE int CPUUpdateTicks (void)
{
	int cpuLoopTicks = graphics.lcdTicks;

	if(soundTicks < cpuLoopTicks)
		cpuLoopTicks = soundTicks;

	if(timer0On && (timer0Ticks < cpuLoopTicks))
		cpuLoopTicks = timer0Ticks;

	if(timer1On && !(io_registers[REG_TM1CNT] & 4) && (timer1Ticks < cpuLoopTicks))
		cpuLoopTicks = timer1Ticks;

	if(timer2On && !(io_registers[REG_TM2CNT] & 4) && (timer2Ticks < cpuLoopTicks))
		cpuLoopTicks = timer2Ticks;

	if(timer3On && !(io_registers[REG_TM3CNT] & 4) && (timer3Ticks < cpuLoopTicks))
		cpuLoopTicks = timer3Ticks;


	if (IRQTicks)
	{
		if (IRQTicks < cpuLoopTicks)
			cpuLoopTicks = IRQTicks;
	}

	return cpuLoopTicks;
}

#if THREADED_RENDERER

	#define CPUUpdateWindow0() \
	{ \
	  int i; \
	  int x00_window0 = R_WIN_Window0_X1; \
	  int x01_window0 = R_WIN_Window0_X2; \
	  int x00_lte_x01 = x00_window0 <= x01_window0; \
	  for(i = 0; i < 240; i++) \
		  gfxInWin[0][i] = ((i >= x00_window0 && i < x01_window0) & x00_lte_x01) | ((i >= x00_window0 || i < x01_window0) & ~x00_lte_x01); \
	  ++threaded_gfxinwin_ver[0]; \
	}

	#define CPUUpdateWindow1() \
	{ \
	  int i; \
	  int x00_window1 = R_WIN_Window1_X1; \
	  int x01_window1 = R_WIN_Window1_X2; \
	  int x00_lte_x01 = x00_window1 <= x01_window1; \
	  for(i = 0; i < 240; i++) \
	   gfxInWin[1][i] = ((i >= x00_window1 && i < x01_window1) & x00_lte_x01) | ((i >= x00_window1 || i < x01_window1) & ~x00_lte_x01); \
	  ++threaded_gfxinwin_ver[1]; \
	}

#else

	#define CPUUpdateWindow0() \
	{ \
	  int i; \
	  int x00_window0 = R_WIN_Window0_X1; \
	  int x01_window0 = R_WIN_Window0_X2; \
	  int x00_lte_x01 = x00_window0 <= x01_window0; \
	  for(i = 0; i < 240; i++) \
		  gfxInWin[0][i] = ((i >= x00_window0 && i < x01_window0) & x00_lte_x01) | ((i >= x00_window0 || i < x01_window0) & ~x00_lte_x01); \
	}

	#define CPUUpdateWindow1() \
	{ \
	  int i; \
	  int x00_window1 = R_WIN_Window1_X1; \
	  int x01_window1 = R_WIN_Window1_X2; \
	  int x00_lte_x01 = x00_window1 <= x01_window1; \
	  for(i = 0; i < 240; i++) \
	   gfxInWin[1][i] = ((i >= x00_window1 && i < x01_window1) & x00_lte_x01) | ((i >= x00_window1 || i < x01_window1) & ~x00_lte_x01); \
	}

#endif

#define CPUCompareVCOUNT() \
  if(R_VCOUNT == (io_registers[REG_DISPSTAT] >> 8)) \
  { \
    { uint16_t _v = (io_registers[REG_DISPSTAT]) | (4); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); } \
    if(io_registers[REG_DISPSTAT] & 0x20) \
    { \
      { uint16_t _v = (io_registers[REG_IF]) | (4); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); } \
    } \
  } \
  else \
  { \
    { uint16_t _v = (io_registers[REG_DISPSTAT]) & (0xFFFB); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x4, _v); } \
  } \
  if (graphics.layerEnableDelay > 0) \
  { \
      graphics.layerEnableDelay--; \
      if (graphics.layerEnableDelay == 1) \
          graphics.layerEnable = io_registers[REG_DISPCNT]; \
  }

unsigned CPUWriteState(uint8_t* data, unsigned size)
{
	uint8_t *orig = data;

	utilWriteIntMem(&data, SAVE_GAME_VERSION);
	utilWriteMem(&data, &rom[0xa0], 16);
	utilWriteIntMem(&data, useBios);
	utilWriteMem(&data, &bus.reg[0], sizeof(bus.reg));

	utilWriteDataMem(&data, saveGameStruct);

	utilWriteIntMem(&data, stopState);
	utilWriteIntMem(&data, IRQTicks);

	utilWriteMem(&data, internalRAM, 0x8000);
	utilWriteMem(&data, paletteRAM, 0x400);
	utilWriteMem(&data, workRAM, 0x40000);
	utilWriteMem(&data, vram, 0x20000);
	utilWriteMem(&data, oam, 0x400);
	/* pix (framebuffer) is no longer serialized as of SAVE_GAME_VERSION_11.
	 * It's overwritten on the next scanline by the renderer; saving it
	 * cost 160KB and polluted cache on rewind/runahead. */
	utilWriteMem(&data, ioMem, 0x400);

	eepromSaveGameMem(&data);
	flashSaveGameMem(&data);
	soundSaveGameMem(&data);
	rtcSaveGameMem(&data);

	return (ptrdiff_t)data - (ptrdiff_t)orig;
}


void CPUCleanUp (void)
{
   if(rom != NULL)
   {
      memalign_free(rom);
      rom = NULL;
   }

   if(vram != NULL)
   {
      memalign_free(vram);
      vram = NULL;
   }

   if(paletteRAM != NULL)
   {
      memalign_free(paletteRAM);
      paletteRAM = NULL;
   }

   if(internalRAM != NULL)
   {
      memalign_free(internalRAM);
      internalRAM = NULL;
   }

   if(workRAM != NULL)
   {
      memalign_free(workRAM);
      workRAM = NULL;
   }

   if(bios != NULL)
   {
      memalign_free(bios);
      bios = NULL;
   }

   if(pix != NULL)
   {
      memalign_free(pix);
      pix = NULL;
   }

   if(oam != NULL)
   {
      memalign_free(oam);
      oam = NULL;
   }

   if(ioMem != NULL)
   {
      memalign_free(ioMem);
      ioMem = NULL;
   }
}

static bool CPUSetupBuffers(void)
{
	romSize = 0x2000000;
	if(rom != NULL)
		CPUCleanUp();

	/*systemSaveUpdateCounter = SYSTEM_SAVE_NOT_UPDATED; */

	rom = (uint8_t *)memalign_alloc_aligned(0x2000000);
	workRAM = (uint8_t *)memalign_alloc_aligned(0x40000);
	bios = (uint8_t *)memalign_alloc_aligned(0x4000);
	internalRAM = (uint8_t *)memalign_alloc_aligned(0x8000);
	paletteRAM = (uint8_t *)memalign_alloc_aligned(0x400);
	vram = (uint8_t *)memalign_alloc_aligned(0x20000);
	oam = (uint8_t *)memalign_alloc_aligned(0x400);
	pix = (uint16_t *)memalign_alloc_aligned(2 * PIX_BUFFER_SCREEN_WIDTH * 160);
	ioMem = (uint8_t *)memalign_alloc_aligned(0x400);

	if(rom == NULL || workRAM == NULL || bios == NULL ||
	   internalRAM == NULL || paletteRAM == NULL ||
	   vram == NULL || oam == NULL || pix == NULL || ioMem == NULL) {
		CPUCleanUp();
		return false;
	}

	memset(rom, 0, 0x2000000);
	memset(workRAM, 1, 0x40000);
	memset(bios, 1, 0x4000);
	memset(internalRAM, 1, 0x8000);
	memset(paletteRAM, 1, 0x400);
	memset(vram, 1, 0x20000);
	memset(oam, 1, 0x400);
	memset(pix, 1, 2 * PIX_BUFFER_SCREEN_WIDTH * 160);
	memset(ioMem, 1, 0x400);

	flashInit();
	eepromInit();

	/*CPUUpdateRenderBuffers(true); */
#if !THREADED_RENDERER
	memset(line[Layer_BG0], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG1], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG2], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG3], -1, 240 * sizeof(uint32_t));
#endif

	return true;
}

static void applyCartridgeOverride(char* code) {
#if USE_MOTION_SENSOR
	hardware.sensor = HARDWARE_SENSOR_NONE;

	do {
		/* Koro Koro Puzzle - Happy Panechu! */
		if(memcmp(code, "KHPJ", 4) == 0) {
			hardware.sensor = HARDWARE_SENSOR_TILT;
			break;
		}

		/* Yoshi's Universal Gravitation */
		if(memcmp(code, "KYGJ", 4) == 0 || memcmp(code, "KYGE", 4) == 0 || memcmp(code, "KYGP", 4) == 0) {
			hardware.sensor = HARDWARE_SENSOR_TILT;
			break;
		}

		/* Wario Ware Twisted */
		if(memcmp(code, "RZWJ", 4) == 0 || memcmp(code, "RZWE", 4) == 0 || memcmp(code, "RZWP", 4) == 0) {
			hardware.sensor = HARDWARE_SENSOR_GYRO;
			break;
		}
	} while(0);

	systemSetSensorState(hardware.sensor);

	if(hardware.sensor) {
		hardware.tilt_x = 0xFFF;
		hardware.tilt_y = 0xFFF;
	}

	/*if(hardware.sensor) while(1); */
#endif
}

static void CPULoadRomGeneric(uint8_t *whereToLoad)
{
	int i;
   char cartridgeCode[4];
   uint16_t *temp;

	/*load cartridge code */
	memcpy(cartridgeCode, whereToLoad + 0xAC, 4);
	applyCartridgeOverride(cartridgeCode);

	temp = (uint16_t *)(rom+((romSize+1)&~1));

	for(i = (romSize+1)&~1; i < 0x2000000; i+=2)
   {
		WRITE16LE(temp, (i >> 1) & 0xFFFF);
		temp++;
	}
}

static uint8_t *utilLoad(const char *file, uint8_t *data, int *size)
{
   RFILE *fp = filestream_open(file, RETRO_VFS_FILE_ACCESS_READ,
         RETRO_VFS_FILE_ACCESS_HINT_NONE);
   if (!fp)
      return NULL;

   filestream_seek(fp, 0, SEEK_END); /*go to end*/
   *size = filestream_tell(fp); /* get position at end (length)*/
   filestream_rewind(fp);

   /* All call sites pass a non-NULL pre-allocated buffer; the malloc-on-NULL
    * branch this function used to carry was dead code, so the contract is
    * now explicit: data must be a writable buffer of at least *size bytes. */
   filestream_read(fp, data, *size);
   filestream_close(fp);
   return data;
}


#ifdef LOAD_FROM_MEMORY
int CPULoadRomData(const char *data, int size)
{
   uint8_t *whereToLoad;
	if (!CPUSetupBuffers())
      return 0;

	whereToLoad = rom;
	romSize     = (size % 2 == 0) ? size    : size + 1;

	memcpy(whereToLoad, data, size);

   CPULoadRomGeneric(whereToLoad);

   return romSize;
}
#else
int CPULoadRom(const char * file)
{
	uint8_t *whereToLoad;
	if (!CPUSetupBuffers())
      return 0;

	whereToLoad = rom;

	if (file)
	{
		if(!utilLoad(file, whereToLoad, &romSize))
      {
         CPUCleanUp();
         return 0;
      }
	}

   CPULoadRomGeneric(whereToLoad);

   return romSize;
}
#endif

void doMirroring (bool b)
{
	uint32_t mirroredRomSize = (((romSize)>>20) & 0x3F)<<20;
	uint32_t mirroredRomAddress = romSize;
	if ((mirroredRomSize <=0x800000) && (b))
	{
		mirroredRomAddress = mirroredRomSize;
		if (mirroredRomSize==0)
			mirroredRomSize=0x100000;
		while (mirroredRomAddress<0x01000000)
		{
			memcpy((uint16_t *)(rom+mirroredRomAddress), (uint16_t *)(rom), mirroredRomSize);
			mirroredRomAddress+=mirroredRomSize;
		}
	}
}

#if THREADED_RENDERER
void ThreadedRendererStart(void)
{
   int u;
   /* Always init all contexts -- the synchronous dispatch path uses
    * context 0 even when no worker is spawned. */
   for(u = 0; u < THREADED_RENDERER_COUNT; ++u)
      init_renderer_context(&threaded_renderer_contexts[u]);

#ifdef PER_FRAME_BATCHED
   /* Batched mode does not yet plumb worker threads -- postRender writes
    * into per-line snapshots and all 160 are rendered inline at end of
    * frame.  Force the worker off so a stale option setting doesn't spawn
    * a thread that would spin forever on renderer_state and burn a core
    * during benchmarks. */
   g_threaded_renderer_enabled = 0;
#endif

   if(!g_threaded_renderer_enabled)
      return;

	for(u = 0; u < THREADED_RENDERER_COUNT; ++u)
   {
      threaded_renderer_contexts[u].renderer_control = 1;

      threaded_renderer_contexts[u].renderer_thread_id =
         thread_run((u == 0) ? threaded_renderer_loop0 : threaded_renderer_loop, (void*)(intptr_t)(u),
#if VITA
               (u == 0) ? THREAD_PRIORITY_NORMAL : THREAD_PRIORITY_LOW);
#else
      THREAD_PRIORITY_NORMAL);
#endif
   }
}

void ThreadedRendererStop(void)
{
   int u;

   if(!g_threaded_renderer_enabled)
      return;

   for(u = 0; u < THREADED_RENDERER_COUNT; ++u)
      threaded_renderer_contexts[u].renderer_control = 2;

   /* Wait for renderer threads to acknowledge the stop request. Yield rather
    * than spin: on in-order PPC the busy-spin contended L2 with the renderer
    * thread we're waiting on, slowing the very wait it implements. */
   for (;;)
   {
      int still_running = 0;
      for(u = 0; u < THREADED_RENDERER_COUNT; ++u)
         if(threaded_renderer_contexts[u].renderer_control == 2)
            still_running = 1;
      if (!still_running)
         break;
      thread_sleep(1);
   }
}
#endif

/* we only use 16bit color depth */
#if THREADED_RENDERER
	#define GET_LINE_MIX (pix + PIX_BUFFER_SCREEN_WIDTH * RENDERER_R_VCOUNT)
#else
	#define GET_LINE_MIX (pix + PIX_BUFFER_SCREEN_WIDTH * R_VCOUNT)
#endif

static void mode0RenderLine (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG0) {
		gfxDrawTextScreen(Layer_BG0, renderer_idx, RENDERER_IO_REGISTERS[REG_BG0CNT], RENDERER_IO_REGISTERS[REG_BG0HOFS], RENDERER_IO_REGISTERS[REG_BG0VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG1) {
		gfxDrawTextScreen(Layer_BG1, renderer_idx, RENDERER_IO_REGISTERS[REG_BG1CNT], RENDERER_IO_REGISTERS[REG_BG1HOFS], RENDERER_IO_REGISTERS[REG_BG1VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawTextScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_IO_REGISTERS[REG_BG2HOFS], RENDERER_IO_REGISTERS[REG_BG2VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG3) {
		gfxDrawTextScreen(Layer_BG3, renderer_idx, RENDERER_IO_REGISTERS[REG_BG3CNT], RENDERER_IO_REGISTERS[REG_BG3HOFS], RENDERER_IO_REGISTERS[REG_BG3VOFS]);
	}

	{
		int x;
		for(x = 0; x < 240; x++)
	{
		uint32_t color = backdrop;
		uint8_t top    = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG0][x] < color)
      {
         color = RENDERER_LINE[Layer_BG0][x];
         top   = SpecialEffectTarget_BG0;
      }

		if((uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) 
            < (uint8_t)(color >> 24))
      {
         color = RENDERER_LINE[Layer_BG1][x];
         top   = SpecialEffectTarget_BG1;
      }

		if((uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) 
            < (uint8_t)(color >> 24))
      {
         color = RENDERER_LINE[Layer_BG2][x];
         top   = SpecialEffectTarget_BG2;
      }

		if((uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) 
            < (uint8_t)(color >> 24))
      {
         color = RENDERER_LINE[Layer_BG3][x];
         top   = SpecialEffectTarget_BG3;
      }

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) 
            < (uint8_t)(color >> 24))
      {
         color = RENDERER_LINE[Layer_OBJ][x];
         top = SpecialEffectTarget_OBJ;

         if(color & 0x00010000)
         {
            /* semi-transparent OBJ */
            uint32_t back = backdrop;
            uint8_t  top2 = SpecialEffectTarget_BD;

            if((uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24) 
                  < (uint8_t)(back >> 24))
            {
               back = RENDERER_LINE[Layer_BG0][x];
               top2 = SpecialEffectTarget_BG0;
            }

            if((uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) 
                  < (uint8_t)(back >> 24))
            {
               back = RENDERER_LINE[Layer_BG1][x];
               top2 = SpecialEffectTarget_BG1;
            }

            if((uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) 
                  < (uint8_t)(back >> 24))
            {
               back = RENDERER_LINE[Layer_BG2][x];
               top2 = SpecialEffectTarget_BG2;
            }

            if((uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) 
                  < (uint8_t)(back >> 24))
            {
               back = RENDERER_LINE[Layer_BG3][x];
               top2 = SpecialEffectTarget_BG3;
            }

            alpha_blend_brightness_switch();
         }
      }


		lineMix[x] = CONVERT_COLOR(color);
	}
	}
}

static void mode0RenderLineNoWindow (int renderer_idx)
{
   uint16_t* lineMix;
   uint32_t backdrop;
   int x;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG0)
      gfxDrawTextScreen(Layer_BG0, renderer_idx, RENDERER_IO_REGISTERS[REG_BG0CNT], RENDERER_IO_REGISTERS[REG_BG0HOFS], RENDERER_IO_REGISTERS[REG_BG0VOFS]);

	if(RENDERER_R_DISPCNT_Screen_Display_BG1)
		gfxDrawTextScreen(Layer_BG1, renderer_idx, RENDERER_IO_REGISTERS[REG_BG1CNT], RENDERER_IO_REGISTERS[REG_BG1HOFS], RENDERER_IO_REGISTERS[REG_BG1VOFS]);

	if(RENDERER_R_DISPCNT_Screen_Display_BG2)
		gfxDrawTextScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_IO_REGISTERS[REG_BG2HOFS], RENDERER_IO_REGISTERS[REG_BG2VOFS]);

	if(RENDERER_R_DISPCNT_Screen_Display_BG3)
		gfxDrawTextScreen(Layer_BG3, renderer_idx, RENDERER_IO_REGISTERS[REG_BG3CNT], RENDERER_IO_REGISTERS[REG_BG3HOFS], RENDERER_IO_REGISTERS[REG_BG3VOFS]);

	for(x = 0; x < 240; x++)
   {
      uint32_t color = backdrop;
      uint8_t top    = SpecialEffectTarget_BD;

      if(RENDERER_LINE[Layer_BG0][x] < color)
      {
         color = RENDERER_LINE[Layer_BG0][x];
         top   = SpecialEffectTarget_BG0;
      }

      if(RENDERER_LINE[Layer_BG1][x] < (color & 0xFF000000))
      {
         color = RENDERER_LINE[Layer_BG1][x];
         top   = SpecialEffectTarget_BG1;
      }

      if(RENDERER_LINE[Layer_BG2][x] < (color & 0xFF000000))
      {
         color = RENDERER_LINE[Layer_BG2][x];
         top   = SpecialEffectTarget_BG2;
      }

      if(RENDERER_LINE[Layer_BG3][x] < (color & 0xFF000000))
      {
         color = RENDERER_LINE[Layer_BG3][x];
         top   = SpecialEffectTarget_BG3;
      }

      if(RENDERER_LINE[Layer_OBJ][x] < (color & 0xFF000000))
      {
         color = RENDERER_LINE[Layer_OBJ][x];
         top   = SpecialEffectTarget_OBJ;
      }

      if(!(color & 0x00010000))
      {
         switch(RENDERER_R_BLDCNT_Color_Special_Effect)
         {
            case SpecialEffect_None:
               break;
            case SpecialEffect_Alpha_Blending:
               if(RENDERER_R_BLDCNT_IsTarget1(top))
               {
                  uint32_t back = backdrop;
                  uint8_t top2 = SpecialEffectTarget_BD;
                  if((RENDERER_LINE[Layer_BG0][x] < back) && (top != SpecialEffectTarget_BG0))
                  {
                     back = RENDERER_LINE[Layer_BG0][x];
                     top2 = SpecialEffectTarget_BG0;
                  }

                  if((RENDERER_LINE[Layer_BG1][x] < (back & 0xFF000000)) && (top != SpecialEffectTarget_BG1))
                  {
                     back = RENDERER_LINE[Layer_BG1][x];
                     top2 = SpecialEffectTarget_BG1;
                  }

                  if((RENDERER_LINE[Layer_BG2][x] < (back & 0xFF000000)) && (top != SpecialEffectTarget_BG2))
                  {
                     back = RENDERER_LINE[Layer_BG2][x];
                     top2 = SpecialEffectTarget_BG2;
                  }

                  if((RENDERER_LINE[Layer_BG3][x] < (back & 0xFF000000)) && (top != SpecialEffectTarget_BG3))
                  {
                     back = RENDERER_LINE[Layer_BG3][x];
                     top2 = SpecialEffectTarget_BG3;
                  }

                  if((RENDERER_LINE[Layer_OBJ][x] < (back & 0xFF000000)) && (top != SpecialEffectTarget_OBJ))
                  {
                     back = RENDERER_LINE[Layer_OBJ][x];
                     top2 = SpecialEffectTarget_OBJ;
                  }

                  if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
                  {
                     GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
                  }

               }
               break;
            case SpecialEffect_Brightness_Increase:
               if(RENDERER_R_BLDCNT_IsTarget1(top))
                  color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
               break;
            case SpecialEffect_Brightness_Decrease:
               if(RENDERER_R_BLDCNT_IsTarget1(top))
                  color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
               break;
         }
      }
      else
      {
         /* semi-transparent OBJ */
         uint32_t back = backdrop;
         uint8_t top2 = SpecialEffectTarget_BD;

         if(RENDERER_LINE[Layer_BG0][x] < back) {
            back = RENDERER_LINE[Layer_BG0][x];
            top2 = SpecialEffectTarget_BG0;
         }

         if(RENDERER_LINE[Layer_BG1][x] < (back & 0xFF000000)) {
            back = RENDERER_LINE[Layer_BG1][x];
            top2 = SpecialEffectTarget_BG1;
         }

         if(RENDERER_LINE[Layer_BG2][x] < (back & 0xFF000000)) {
            back = RENDERER_LINE[Layer_BG2][x];
            top2 = SpecialEffectTarget_BG2;
         }

         if(RENDERER_LINE[Layer_BG3][x] < (back & 0xFF000000)) {
            back = RENDERER_LINE[Layer_BG3][x];
            top2 = SpecialEffectTarget_BG3;
         }

         alpha_blend_brightness_switch();
      }

      lineMix[x] = CONVERT_COLOR(color);
   }
}

static void mode0RenderLineAll (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	bool inWindow0;
	bool inWindow1;
	uint8_t inWin0Mask;
	uint8_t inWin1Mask;
	uint8_t outMask;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	inWindow0 = false;
	inWindow1 = false;

	if(RENDERER_R_DISPCNT_Window_0_Display) {
		uint8_t v0 = RENDERER_R_WIN_Window0_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window0_Y2;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
		if(v1 >= v0)
			inWindow0 |= (RENDERER_R_VCOUNT >= v0 && RENDERER_R_VCOUNT < v1);
		else
			inWindow0 |= (RENDERER_R_VCOUNT >= v0 || RENDERER_R_VCOUNT < v1);
	}
	if(RENDERER_R_DISPCNT_Window_1_Display) {
		uint8_t v0 = RENDERER_R_WIN_Window1_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window1_Y2;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
		if(v1 >= v0)
			inWindow1 |= (RENDERER_R_VCOUNT >= v0 && RENDERER_R_VCOUNT < v1);
		else
			inWindow1 |= (RENDERER_R_VCOUNT >= v0 || RENDERER_R_VCOUNT < v1);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG0) {
		gfxDrawTextScreen(Layer_BG0, renderer_idx, RENDERER_IO_REGISTERS[REG_BG0CNT], RENDERER_IO_REGISTERS[REG_BG0HOFS], RENDERER_IO_REGISTERS[REG_BG0VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG1) {
		gfxDrawTextScreen(Layer_BG1, renderer_idx, RENDERER_IO_REGISTERS[REG_BG1CNT], RENDERER_IO_REGISTERS[REG_BG1HOFS], RENDERER_IO_REGISTERS[REG_BG1VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawTextScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_IO_REGISTERS[REG_BG2HOFS], RENDERER_IO_REGISTERS[REG_BG2VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG3) {
		gfxDrawTextScreen(Layer_BG3, renderer_idx, RENDERER_IO_REGISTERS[REG_BG3CNT], RENDERER_IO_REGISTERS[REG_BG3HOFS], RENDERER_IO_REGISTERS[REG_BG3VOFS]);
	}

	inWin0Mask = RENDERER_R_WIN_Window0_Mask;
	inWin1Mask = RENDERER_R_WIN_Window1_Mask;
	outMask = RENDERER_R_WIN_Outside_Mask;

	{
		int x;
		for(x = 0; x < 240; x++) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;
		uint8_t mask = outMask;

		if(!(RENDERER_LINE[Layer_WIN_OBJ][x] & 0x80000000)) {
			mask = RENDERER_R_WIN_OBJ_Mask;
		}

		mask = SELECT(inWindow1 && RENDERER_GFX_IN_WIN[1][x], inWin1Mask, mask);
		mask = SELECT(inWindow0 && RENDERER_GFX_IN_WIN[0][x], inWin0Mask, mask);

		if((mask & LayerMask_BG0) && (RENDERER_LINE[Layer_BG0][x] < color)) {
			color = RENDERER_LINE[Layer_BG0][x];
			top = SpecialEffectTarget_BG0;
		}

		if((mask & LayerMask_BG1) && ((uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(color >> 24))) {
			color = RENDERER_LINE[Layer_BG1][x];
			top = SpecialEffectTarget_BG1;
		}

		if((mask & LayerMask_BG2) && ((uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(color >> 24))) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((mask & LayerMask_BG3) && ((uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(color >> 24))) {
			color = RENDERER_LINE[Layer_BG3][x];
			top = SpecialEffectTarget_BG3;
		}

		if((mask & LayerMask_OBJ) && ((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >> 24))) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(color & 0x00010000)
		{
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			if((mask & LayerMask_BG0) && ((uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24) < (uint8_t)(back >> 24))) {
				back = RENDERER_LINE[Layer_BG0][x];
				top2 = SpecialEffectTarget_BG0;
			}

			if((mask & LayerMask_BG1) && ((uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(back >> 24))) {
				back = RENDERER_LINE[Layer_BG1][x];
				top2 = SpecialEffectTarget_BG1;
			}

			if((mask & LayerMask_BG2) && ((uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(back >> 24))) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			if((mask & LayerMask_BG3) && ((uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(back >> 24))) {
				back = RENDERER_LINE[Layer_BG3][x];
				top2 = SpecialEffectTarget_BG3;
			}

			alpha_blend_brightness_switch();
		}
		else if((mask & LayerMask_SFX) && (RENDERER_R_BLDCNT_IsTarget1(top)))
		{
			/* special FX on in the window */
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;
						if(((mask & LayerMask_BG0) && (uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24) < (uint8_t)(back >> 24)) && top != SpecialEffectTarget_BG0)
						{
							back = RENDERER_LINE[Layer_BG0][x];
							top2 = SpecialEffectTarget_BG0;
						}

						if(((mask & LayerMask_BG1) && (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(back >> 24)) && top != SpecialEffectTarget_BG1)
						{
							back = RENDERER_LINE[Layer_BG1][x];
							top2 = SpecialEffectTarget_BG1;
						}

						if(((mask & LayerMask_BG2) && (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(back >> 24)) && top != SpecialEffectTarget_BG2)
						{
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if(((mask & LayerMask_BG3) && (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(back >> 24)) && top != SpecialEffectTarget_BG3)
						{
							back = RENDERER_LINE[Layer_BG3][x];
							top2 = SpecialEffectTarget_BG3;
						}

						if(((mask & LayerMask_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) && top != SpecialEffectTarget_OBJ) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}
}

/*
Mode 1 is a tiled graphics mode, but with background layer 2 supporting scaling and rotation.
There is no layer 3 in this mode.
Layers 0 and 1 can be either 16 colours (with 16 different palettes) or 256 colours.
There are 1024 tiles available.
Layer 2 is 256 colours and allows only 256 tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode1RenderLine (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG0) {
		gfxDrawTextScreen(Layer_BG0, renderer_idx, RENDERER_IO_REGISTERS[REG_BG0CNT], RENDERER_IO_REGISTERS[REG_BG0HOFS], RENDERER_IO_REGISTERS[REG_BG0VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG1) {
		gfxDrawTextScreen(Layer_BG1, renderer_idx, RENDERER_IO_REGISTERS[REG_BG1CNT], RENDERER_IO_REGISTERS[REG_BG1HOFS], RENDERER_IO_REGISTERS[REG_BG1VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_BG2X_L, RENDERER_BG2X_H, RENDERER_BG2Y_L, RENDERER_BG2Y_H,
				RENDERER_IO_REGISTERS[REG_BG2PA], RENDERER_IO_REGISTERS[REG_BG2PB], RENDERER_IO_REGISTERS[REG_BG2PC], RENDERER_IO_REGISTERS[REG_BG2PD],
				&RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		uint32_t x;
		for(x = 0; x < 240u; ++x) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;

		uint8_t li1 = (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24);
		uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
		uint8_t li4 = (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24);

		uint8_t r = 	(li2 < li1) ? (li2) : (li1);

		if(li4 < r){
			r = 	(li4);
		}

		if(RENDERER_LINE[Layer_BG0][x] < backdrop) {
			color = RENDERER_LINE[Layer_BG0][x];
			top = SpecialEffectTarget_BG0;
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li1){
				color = RENDERER_LINE[Layer_BG1][x];
				top = SpecialEffectTarget_BG1;
			}else if(r == li2){
				color = RENDERER_LINE[Layer_BG2][x];
				top = SpecialEffectTarget_BG2;
			}else if(r == li4){
				color = RENDERER_LINE[Layer_OBJ][x];
				top = SpecialEffectTarget_OBJ;
				if((color & 0x00010000))
				{
					/* semi-transparent OBJ */
					uint32_t back = backdrop;
					uint8_t top2 = SpecialEffectTarget_BD;

					uint8_t li0 = (uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24);
					uint8_t li1 = (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24);
					uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
					uint8_t r = 	(li1 < li0) ? (li1) : (li0);

					if(li2 < r) {
						r =  (li2);
					}

					if(r < (uint8_t)(back >> 24)) {
						if(r == li0){
							back = RENDERER_LINE[Layer_BG0][x];
							top2 = SpecialEffectTarget_BG0;
						}else if(r == li1){
							back = RENDERER_LINE[Layer_BG1][x];
							top2 = SpecialEffectTarget_BG1;
						}else if(r == li2){
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}
					}

					alpha_blend_brightness_switch();
				}
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode1RenderLineNoWindow (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG0) {
		gfxDrawTextScreen(Layer_BG0, renderer_idx, RENDERER_IO_REGISTERS[REG_BG0CNT], RENDERER_IO_REGISTERS[REG_BG0HOFS], RENDERER_IO_REGISTERS[REG_BG0VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG1) {
		gfxDrawTextScreen(Layer_BG1, renderer_idx, RENDERER_IO_REGISTERS[REG_BG1CNT], RENDERER_IO_REGISTERS[REG_BG1HOFS], RENDERER_IO_REGISTERS[REG_BG1VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_BG2X_L, RENDERER_BG2X_H, RENDERER_BG2Y_L, RENDERER_BG2Y_H,
				RENDERER_IO_REGISTERS[REG_BG2PA], RENDERER_IO_REGISTERS[REG_BG2PB], RENDERER_IO_REGISTERS[REG_BG2PC], RENDERER_IO_REGISTERS[REG_BG2PD],
				&RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;

		uint8_t li1 = (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24);
		uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
		uint8_t li4 = (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24);

		uint8_t r = 	(li2 < li1) ? (li2) : (li1);

		if(li4 < r){
			r = 	(li4);
		}

		if(RENDERER_LINE[Layer_BG0][x] < backdrop) {
			color = RENDERER_LINE[Layer_BG0][x];
			top = SpecialEffectTarget_BG0;
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li1){
				color = RENDERER_LINE[Layer_BG1][x];
				top = SpecialEffectTarget_BG1;
			}else if(r == li2){
				color = RENDERER_LINE[Layer_BG2][x];
				top = SpecialEffectTarget_BG2;
			}else if(r == li4){
				color = RENDERER_LINE[Layer_OBJ][x];
				top = SpecialEffectTarget_OBJ;
			}
		}

		if(!(color & 0x00010000)) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((top != SpecialEffectTarget_BG0) && (uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG0][x];
							top2 = SpecialEffectTarget_BG0;
						}

						if((top != SpecialEffectTarget_BG1) && (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG1][x];
							top2 = SpecialEffectTarget_BG1;
						}

						if((top != SpecialEffectTarget_BG2) && (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			uint8_t li0 = (uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24);
			uint8_t li1 = (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24);
			uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);

			uint8_t r = 	(li1 < li0) ? (li1) : (li0);

			if(li2 < r) {
				r =  (li2);
			}

			if(r < (uint8_t)(back >> 24))
			{
				if(r == li0)
				{
					back = RENDERER_LINE[Layer_BG0][x];
					top2 = SpecialEffectTarget_BG0;
				}
				else if(r == li1)
				{
					back = RENDERER_LINE[Layer_BG1][x];
					top2 = SpecialEffectTarget_BG1;
				}
				else if(r == li2)
				{
					back = RENDERER_LINE[Layer_BG2][x];
					top2 = SpecialEffectTarget_BG2;
				}
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode1RenderLineAll (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	bool inWindow0;
	bool inWindow1;
	uint8_t inWin0Mask;
	uint8_t inWin1Mask;
	uint8_t outMask;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	inWindow0 = false;
	inWindow1 = false;

	if(RENDERER_R_DISPCNT_Window_0_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window0_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window0_Y2;
		inWindow0 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}
	if(RENDERER_R_DISPCNT_Window_1_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window1_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window1_Y2;
		inWindow1 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG0) {
		gfxDrawTextScreen(Layer_BG0, renderer_idx, RENDERER_IO_REGISTERS[REG_BG0CNT], RENDERER_IO_REGISTERS[REG_BG0HOFS], RENDERER_IO_REGISTERS[REG_BG0VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG1) {
		gfxDrawTextScreen(Layer_BG1, renderer_idx, RENDERER_IO_REGISTERS[REG_BG1CNT], RENDERER_IO_REGISTERS[REG_BG1HOFS], RENDERER_IO_REGISTERS[REG_BG1VOFS]);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_BG2X_L, RENDERER_BG2X_H, RENDERER_BG2Y_L, RENDERER_BG2Y_H,
				RENDERER_IO_REGISTERS[REG_BG2PA], RENDERER_IO_REGISTERS[REG_BG2PB], RENDERER_IO_REGISTERS[REG_BG2PC], RENDERER_IO_REGISTERS[REG_BG2PD],
				&RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	inWin0Mask = RENDERER_R_WIN_Window0_Mask;
	inWin1Mask = RENDERER_R_WIN_Window1_Mask;
	outMask = RENDERER_R_WIN_Outside_Mask;

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;
		uint8_t mask = outMask;

		if(!(RENDERER_LINE[Layer_WIN_OBJ][x] & 0x80000000)) {
			mask = RENDERER_R_WIN_OBJ_Mask;
		}

		mask = SELECT(inWindow1 && RENDERER_GFX_IN_WIN[1][x], inWin1Mask, mask);
		mask = SELECT(inWindow0 && RENDERER_GFX_IN_WIN[0][x], inWin0Mask, mask);

		/* At the very least, move the inexpensive 'mask' operation up front */
		if((mask & LayerMask_BG0) && RENDERER_LINE[Layer_BG0][x] < backdrop) {
			color = RENDERER_LINE[Layer_BG0][x];
			top = SpecialEffectTarget_BG0;
		}

		if((mask & LayerMask_BG1) && (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_BG1][x];
			top = SpecialEffectTarget_BG1;
		}

		if((mask & LayerMask_BG2) && (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((mask & LayerMask_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(color & 0x00010000) {
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			if((mask & LayerMask_BG0) && (uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24) < (uint8_t)(backdrop >> 24)) {
				back = RENDERER_LINE[Layer_BG0][x];
				top2 = SpecialEffectTarget_BG0;
			}

			if((mask & LayerMask_BG1) && (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(back >> 24)) {
				back = RENDERER_LINE[Layer_BG1][x];
				top2 = SpecialEffectTarget_BG1;
			}

			if((mask & LayerMask_BG2) && (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(back >> 24)) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		} else if(mask & LayerMask_SFX) {
			/* special FX on the window */
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((mask & LayerMask_BG0) && (top != SpecialEffectTarget_BG0) && (uint8_t)(RENDERER_LINE[Layer_BG0][x]>>24) < (uint8_t)(backdrop >> 24)) {
							back = RENDERER_LINE[Layer_BG0][x];
							top2 = SpecialEffectTarget_BG0;
						}

						if((mask & LayerMask_BG1) && (top != SpecialEffectTarget_BG1) && (uint8_t)(RENDERER_LINE[Layer_BG1][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG1][x];
							top2 = SpecialEffectTarget_BG1;
						}

						if((mask & LayerMask_BG2) && (top != SpecialEffectTarget_BG2) && (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((mask & LayerMask_OBJ) && (top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

/*
Mode 2 is a 256 colour tiled graphics mode which supports scaling and rotation.
There is no background layer 0 or 1 in this mode. Only background layers 2 and 3.
There are 256 tiles available.
It does not support flipping.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode2RenderLine (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_BG2X_L, RENDERER_BG2X_H, RENDERER_BG2Y_L, RENDERER_BG2Y_H,
				RENDERER_IO_REGISTERS[REG_BG2PA], RENDERER_IO_REGISTERS[REG_BG2PB], RENDERER_IO_REGISTERS[REG_BG2PC], RENDERER_IO_REGISTERS[REG_BG2PD],
				&RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG3) {
		gfxDrawRotScreen(Layer_BG3, renderer_idx, RENDERER_IO_REGISTERS[REG_BG3CNT], RENDERER_BG3X_L, RENDERER_BG3X_H, RENDERER_BG3Y_L, RENDERER_BG3Y_H,
				RENDERER_IO_REGISTERS[REG_BG3PA], RENDERER_IO_REGISTERS[REG_BG3PB], RENDERER_IO_REGISTERS[REG_BG3PC], RENDERER_IO_REGISTERS[REG_BG3PD],
				&RENDERER_BG3X, &RENDERER_BG3Y, RENDERER_BG3C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;

		uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
		uint8_t li3 = (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24);
		uint8_t li4 = (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24);

		uint8_t r = 	(li3 < li2) ? (li3) : (li2);

		if(li4 < r){
			r = 	(li4);
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li2){
				color = RENDERER_LINE[Layer_BG2][x];
				top = SpecialEffectTarget_BG2;
			}else if(r == li3){
				color = RENDERER_LINE[Layer_BG3][x];
				top = SpecialEffectTarget_BG3;
			}else if(r == li4){
				color = RENDERER_LINE[Layer_OBJ][x];
				top = SpecialEffectTarget_OBJ;

				if(color & 0x00010000) {
					/* semi-transparent OBJ */
					uint32_t back = backdrop;
					uint8_t top2 = SpecialEffectTarget_BD;

					uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
					uint8_t li3 = (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24);
					uint8_t r = 	(li3 < li2) ? (li3) : (li2);

					if(r < (uint8_t)(back >> 24)) {
						if(r == li2){
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}else if(r == li3){
							back = RENDERER_LINE[Layer_BG3][x];
							top2 = SpecialEffectTarget_BG3;
						}
					}

					alpha_blend_brightness_switch();
				}
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
	RENDERER_BG3C = 0;
#endif
}

static void mode2RenderLineNoWindow (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_BG2X_L, RENDERER_BG2X_H, RENDERER_BG2Y_L, RENDERER_BG2Y_H,
				RENDERER_IO_REGISTERS[REG_BG2PA], RENDERER_IO_REGISTERS[REG_BG2PB], RENDERER_IO_REGISTERS[REG_BG2PC], RENDERER_IO_REGISTERS[REG_BG2PD],
				&RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG3) {
		gfxDrawRotScreen(Layer_BG3, renderer_idx, RENDERER_IO_REGISTERS[REG_BG3CNT], RENDERER_BG3X_L, RENDERER_BG3X_H, RENDERER_BG3Y_L, RENDERER_BG3Y_H,
				RENDERER_IO_REGISTERS[REG_BG3PA], RENDERER_IO_REGISTERS[REG_BG3PB], RENDERER_IO_REGISTERS[REG_BG3PC], RENDERER_IO_REGISTERS[REG_BG3PD],
				&RENDERER_BG3X, &RENDERER_BG3Y, RENDERER_BG3C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;

		uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
		uint8_t li3 = (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24);
		uint8_t li4 = (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24);

		uint8_t r = 	(li3 < li2) ? (li3) : (li2);

		if(li4 < r){
			r = 	(li4);
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li2){
				color = RENDERER_LINE[Layer_BG2][x];
				top = SpecialEffectTarget_BG2;
			}else if(r == li3){
				color = RENDERER_LINE[Layer_BG3][x];
				top = SpecialEffectTarget_BG3;
			}else if(r == li4){
				color = RENDERER_LINE[Layer_OBJ][x];
				top = SpecialEffectTarget_OBJ;
			}
		}

		if(!(color & 0x00010000)) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((top != SpecialEffectTarget_BG2) && (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((top != SpecialEffectTarget_BG3) && (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG3][x];
							top2 = SpecialEffectTarget_BG3;
						}

						if((top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			uint8_t li2 = (uint8_t)(RENDERER_LINE[Layer_BG2][x]>>24);
			uint8_t li3 = (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24);
			uint8_t r = 	(li3 < li2) ? (li3) : (li2);

			if(r < (uint8_t)(back >> 24)) {
				if(r == li2){
					back = RENDERER_LINE[Layer_BG2][x];
					top2 = SpecialEffectTarget_BG2;
				}else if(r == li3){
					back = RENDERER_LINE[Layer_BG3][x];
					top2 = SpecialEffectTarget_BG3;
				}
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
	RENDERER_BG3C = 0;
#endif
}

static void mode2RenderLineAll (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	bool inWindow0;
	bool inWindow1;
	uint8_t inWin0Mask;
	uint8_t inWin1Mask;
	uint8_t outMask;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;

	backdrop = RENDERER_BACKDROP;

	inWindow0 = false;
	inWindow1 = false;

	if(RENDERER_R_DISPCNT_Window_0_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window0_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window0_Y2;
		inWindow0 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}
	if(RENDERER_R_DISPCNT_Window_1_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window1_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window1_Y2;
		inWindow1 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen(Layer_BG2, renderer_idx, RENDERER_IO_REGISTERS[REG_BG2CNT], RENDERER_BG2X_L, RENDERER_BG2X_H, RENDERER_BG2Y_L, RENDERER_BG2Y_H,
				RENDERER_IO_REGISTERS[REG_BG2PA], RENDERER_IO_REGISTERS[REG_BG2PB], RENDERER_IO_REGISTERS[REG_BG2PC], RENDERER_IO_REGISTERS[REG_BG2PD],
				&RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG3) {
		gfxDrawRotScreen(Layer_BG3, renderer_idx, RENDERER_IO_REGISTERS[REG_BG3CNT], RENDERER_BG3X_L, RENDERER_BG3X_H, RENDERER_BG3Y_L, RENDERER_BG3Y_H,
				RENDERER_IO_REGISTERS[REG_BG3PA], RENDERER_IO_REGISTERS[REG_BG3PB], RENDERER_IO_REGISTERS[REG_BG3PC], RENDERER_IO_REGISTERS[REG_BG3PD],
				&RENDERER_BG3X, &RENDERER_BG3Y, RENDERER_BG3C);
	}

	inWin0Mask = RENDERER_R_WIN_Window0_Mask;
	inWin1Mask = RENDERER_R_WIN_Window1_Mask;
	outMask = RENDERER_R_WIN_Outside_Mask;

	{
		int x;
		for(x = 0; x < 240; x++) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;
		uint8_t mask = outMask;

		if(!(RENDERER_LINE[Layer_WIN_OBJ][x] & 0x80000000)) {
			mask = RENDERER_R_WIN_OBJ_Mask;
		}

		mask = SELECT(inWindow1 && RENDERER_GFX_IN_WIN[1][x], inWin1Mask, mask);
		mask = SELECT(inWindow0 && RENDERER_GFX_IN_WIN[0][x], inWin0Mask, mask);

		if((mask & LayerMask_BG2) && RENDERER_LINE[Layer_BG2][x] < color) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((mask & LayerMask_BG3) && (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_BG3][x];
			top = SpecialEffectTarget_BG3;
		}

		if((mask & LayerMask_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(color & 0x00010000) {
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			if((mask & LayerMask_BG2) && RENDERER_LINE[Layer_BG2][x] < back) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			if((mask & LayerMask_BG3) && (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(back >> 24)) {
				back = RENDERER_LINE[Layer_BG3][x];
				top2 = SpecialEffectTarget_BG3;
			}

			alpha_blend_brightness_switch();
		} else if(mask & LayerMask_SFX) {
			/* special FX on the window */
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((mask & LayerMask_BG2) && (top != SpecialEffectTarget_BG2) && RENDERER_LINE[Layer_BG2][x] < back) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((mask & LayerMask_BG3) && (top != SpecialEffectTarget_BG3) && (uint8_t)(RENDERER_LINE[Layer_BG3][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_BG3][x];
							top2 = SpecialEffectTarget_BG3;
						}

						if((mask & LayerMask_OBJ) && (top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
	RENDERER_BG3C = 0;
#endif
}

/*
Mode 3 is a 15-bit (32768) colour bitmap graphics mode.
It has a single layer, background layer 2, the same size as the screen.
It doesn't support paging, scrolling, flipping, rotation or tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode3RenderLine (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t background;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	background = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen16Bit(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG2][x] < color) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;

			if(color & 0x00010000) {
				/* semi-transparent OBJ */
				uint32_t back = background;
				uint8_t top2 = SpecialEffectTarget_BD;

				if(RENDERER_LINE[Layer_BG2][x] < background) {
					back = RENDERER_LINE[Layer_BG2][x];
					top2 = SpecialEffectTarget_BG2;
				}

				alpha_blend_brightness_switch();
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode3RenderLineNoWindow (int renderer_idx)
{
uint16_t* lineMix;
uint32_t background;
INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	background = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen16Bit(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG2][x] < background) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(!(color & 0x00010000)) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = background;
						uint8_t top2 = SpecialEffectTarget_BD;

						if(top != SpecialEffectTarget_BG2 && (RENDERER_LINE[Layer_BG2][x] < background) ) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if(top != SpecialEffectTarget_OBJ && ((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24))) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}

					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			/* semi-transparent OBJ */
			uint32_t back = background;
			uint8_t top2 = SpecialEffectTarget_BD;

			if(RENDERER_LINE[Layer_BG2][x] < background) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode3RenderLineAll (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t background;
	bool inWindow0;
	bool inWindow1;
	uint8_t inWin0Mask;
	uint8_t inWin1Mask;
	uint8_t outMask;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	background = RENDERER_BACKDROP;

	inWindow0 = false;
	inWindow1 = false;

	if(RENDERER_R_DISPCNT_Window_0_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window0_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window0_Y2;
		inWindow0 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Window_1_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window1_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window1_Y2;
		inWindow1 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen16Bit(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	inWin0Mask = RENDERER_R_WIN_Window0_Mask;
	inWin1Mask = RENDERER_R_WIN_Window1_Mask;
	outMask = RENDERER_R_WIN_Outside_Mask;

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = SpecialEffectTarget_BD;
		uint8_t mask = outMask;

		if(!(RENDERER_LINE[Layer_WIN_OBJ][x] & 0x80000000)) {
			mask = RENDERER_R_WIN_OBJ_Mask;
		}

		mask = SELECT(inWindow1 && RENDERER_GFX_IN_WIN[1][x], inWin1Mask, mask);
		mask = SELECT(inWindow0 && RENDERER_GFX_IN_WIN[0][x], inWin0Mask, mask);

		if((mask & LayerMask_BG2) && RENDERER_LINE[Layer_BG2][x] < background) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((mask & LayerMask_OBJ) && ((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24))) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(color & 0x00010000) {
			/* semi-transparent OBJ */
			uint32_t back = background;
			uint8_t top2 = SpecialEffectTarget_BD;

			if((mask & LayerMask_BG2) && RENDERER_LINE[Layer_BG2][x] < background) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		} else if(mask & LayerMask_SFX) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = background;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((mask & LayerMask_BG2) && (top != SpecialEffectTarget_BG2) && RENDERER_LINE[Layer_BG2][x] < back) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((mask & LayerMask_OBJ) && (top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

/*
Mode 4 is a 256 colour bitmap graphics mode with 2 swappable pages.
It has a single layer, background layer 2, the same size as the screen.
It doesn't support scrolling, flipping, rotation or tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode4RenderLine (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen256(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x)
	{
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG2][x] < backdrop) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;

			if(color & 0x00010000) {
				/* semi-transparent OBJ */
				uint32_t back = backdrop;
				uint8_t top2 = SpecialEffectTarget_BD;

				if(RENDERER_LINE[Layer_BG2][x] < backdrop) {
					back = RENDERER_LINE[Layer_BG2][x];
					top2 = SpecialEffectTarget_BG2;
				}

				alpha_blend_brightness_switch();
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode4RenderLineNoWindow (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	backdrop = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen256(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x)
	{
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG2][x] < backdrop) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >> 24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(!(color & 0x00010000)) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((top != SpecialEffectTarget_BG2) && RENDERER_LINE[Layer_BG2][x] < backdrop) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			if(RENDERER_LINE[Layer_BG2][x] < back) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode4RenderLineAll (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t backdrop;
	bool inWindow0;
	bool inWindow1;
	uint8_t inWin0Mask;
	uint8_t inWin1Mask;
	uint8_t outMask;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	backdrop = RENDERER_BACKDROP;

	inWindow0 = false;
	inWindow1 = false;

	if(RENDERER_R_DISPCNT_Window_0_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window0_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window0_Y2;
		inWindow0 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Window_1_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window1_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window1_Y2;
		inWindow1 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen256(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	inWin0Mask = RENDERER_R_WIN_Window0_Mask;
	inWin1Mask = RENDERER_R_WIN_Window1_Mask;
	outMask = RENDERER_R_WIN_Outside_Mask;

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = SpecialEffectTarget_BD;
		uint8_t mask = outMask;

		if(!(RENDERER_LINE[Layer_WIN_OBJ][x] & 0x80000000))
			mask = RENDERER_R_WIN_OBJ_Mask;

		mask = SELECT(inWindow1 && RENDERER_GFX_IN_WIN[1][x], inWin1Mask, mask);
		mask = SELECT(inWindow0 && RENDERER_GFX_IN_WIN[0][x], inWin0Mask, mask);

		if((mask & LayerMask_BG2) && (RENDERER_LINE[Layer_BG2][x] < backdrop))
		{
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((mask & LayerMask_OBJ) && ((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24)))
		{
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(color & 0x00010000) {
			/* semi-transparent OBJ */
			uint32_t back = backdrop;
			uint8_t top2 = SpecialEffectTarget_BD;

			if((mask & LayerMask_BG2) && RENDERER_LINE[Layer_BG2][x] < back) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		} else if(mask & LayerMask_SFX) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = backdrop;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((mask & LayerMask_BG2) && (top != SpecialEffectTarget_BG2) && (RENDERER_LINE[Layer_BG2][x] < backdrop)) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((mask & LayerMask_OBJ) && (top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

/*
Mode 5 is a low resolution (160x128) 15-bit colour bitmap graphics mode
with 2 swappable pages!
It has a single layer, background layer 2, lower resolution than the screen.
It doesn't support scrolling, flipping, rotation or tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode5RenderLine (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t background;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	background = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen16Bit160(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG2][x] < background) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;

			if(color & 0x00010000) {
				/* semi-transparent OBJ */
				uint32_t back = background;
				uint8_t top2 = SpecialEffectTarget_BD;

				if(RENDERER_LINE[Layer_BG2][x] < back) {
					back = RENDERER_LINE[Layer_BG2][x];
					top2 = SpecialEffectTarget_BG2;
				}

				alpha_blend_brightness_switch();
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode5RenderLineNoWindow (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t background;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	background = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen16Bit160(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = SpecialEffectTarget_BD;

		if(RENDERER_LINE[Layer_BG2][x] < background) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24)) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(!(color & 0x00010000)) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = background;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((top != SpecialEffectTarget_BG2) && RENDERER_LINE[Layer_BG2][x] < background) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}

					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			/* semi-transparent OBJ */
			uint32_t back = background;
			uint8_t top2 = SpecialEffectTarget_BD;

			if(RENDERER_LINE[Layer_BG2][x] < back) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

static void mode5RenderLineAll (int renderer_idx)
{
	uint16_t* lineMix;
	uint32_t background;
	bool inWindow0;
	bool inWindow1;
	uint8_t inWin0Mask;
	uint8_t inWin1Mask;
	uint8_t outMask;
	INIT_RENDERER_CONTEXT(renderer_idx);

	lineMix = GET_LINE_MIX;
	background = RENDERER_BACKDROP;

	if(RENDERER_R_DISPCNT_Screen_Display_BG2) {
		gfxDrawRotScreen16Bit160(renderer_idx, &RENDERER_BG2X, &RENDERER_BG2Y, RENDERER_BG2C);
	}

	inWindow0 = false;
	inWindow1 = false;

	if(RENDERER_R_DISPCNT_Window_0_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window0_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window0_Y2;
		inWindow0 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	if(RENDERER_R_DISPCNT_Window_1_Display)
	{
		uint8_t v0 = RENDERER_R_WIN_Window1_Y1;
		uint8_t v1 = RENDERER_R_WIN_Window1_Y2;
		inWindow1 = (uint8_t)(RENDERER_R_VCOUNT - v0) < (uint8_t)(v1 - v0) || ((v0 == v1) && (v0 >= 0xe8));
	}

	inWin0Mask = RENDERER_R_WIN_Window0_Mask;
	inWin1Mask = RENDERER_R_WIN_Window1_Mask;
	outMask = RENDERER_R_WIN_Outside_Mask;

	{
		int x;
		for(x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = SpecialEffectTarget_BD;
		uint8_t mask = outMask;

		if(!(RENDERER_LINE[Layer_WIN_OBJ][x] & 0x80000000)) {
			mask = RENDERER_R_WIN_OBJ_Mask;
		}

		mask = SELECT(inWindow1 && RENDERER_GFX_IN_WIN[1][x], inWin1Mask, mask);
		mask = SELECT(inWindow0 && RENDERER_GFX_IN_WIN[0][x], inWin0Mask, mask);

		if((mask & LayerMask_BG2) && (RENDERER_LINE[Layer_BG2][x] < background)) {
			color = RENDERER_LINE[Layer_BG2][x];
			top = SpecialEffectTarget_BG2;
		}

		if((mask & LayerMask_OBJ) && ((uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(color >>24))) {
			color = RENDERER_LINE[Layer_OBJ][x];
			top = SpecialEffectTarget_OBJ;
		}

		if(color & 0x00010000) {
			/* semi-transparent OBJ */
			uint32_t back = background;
			uint8_t top2 = SpecialEffectTarget_BD;

			if((mask & LayerMask_BG2) && RENDERER_LINE[Layer_BG2][x] < back) {
				back = RENDERER_LINE[Layer_BG2][x];
				top2 = SpecialEffectTarget_BG2;
			}

			alpha_blend_brightness_switch();
		} else if(mask & LayerMask_SFX) {
			switch(RENDERER_R_BLDCNT_Color_Special_Effect)
			{
				case SpecialEffect_None:
					break;
				case SpecialEffect_Alpha_Blending:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
					{
						uint32_t back = background;
						uint8_t top2 = SpecialEffectTarget_BD;

						if((mask & LayerMask_BG2) && (top != SpecialEffectTarget_BG2) && (RENDERER_LINE[Layer_BG2][x] < background)) {
							back = RENDERER_LINE[Layer_BG2][x];
							top2 = SpecialEffectTarget_BG2;
						}

						if((mask & LayerMask_OBJ) && (top != SpecialEffectTarget_OBJ) && (uint8_t)(RENDERER_LINE[Layer_OBJ][x]>>24) < (uint8_t)(back >> 24)) {
							back = RENDERER_LINE[Layer_OBJ][x];
							top2 = SpecialEffectTarget_OBJ;
						}

						if(RENDERER_R_BLDCNT_IsTarget2(top2) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case SpecialEffect_Brightness_Increase:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case SpecialEffect_Brightness_Decrease:
					if(RENDERER_R_BLDCNT_IsTarget1(top))
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	}

#if !THREADED_RENDERER
	RENDERER_BG2C = 0;
#endif
}

#if THREADED_RENDERER
/* Per-line rendering work, sans spin-wait.  Used by the worker thread
 * (after it observes renderer_state==1) and by the synchronous dispatch
 * path when g_threaded_renderer_enabled==0.  On entry renderer_state==1;
 * on exit it is reset to 0 so the next postRender() can publish a fresh
 * line. */
static INLINE void renderer_process_line(int renderer_idx)
{
	INIT_RENDERER_CONTEXT(renderer_idx);

	if(renderer_ctx.background_ver < threaded_background_ver) {
		renderer_ctx.background_ver = threaded_background_ver;
		if(!RENDERER_R_DISPCNT_Screen_Display_BG0)
			memset(renderer_ctx.line[Layer_BG0], -1, 240 * sizeof(uint32_t));
		if(!RENDERER_R_DISPCNT_Screen_Display_BG1)
			memset(renderer_ctx.line[Layer_BG1], -1, 240 * sizeof(uint32_t));
		if(!RENDERER_R_DISPCNT_Screen_Display_BG2)
			memset(renderer_ctx.line[Layer_BG2], -1, 240 * sizeof(uint32_t));
		if(!RENDERER_R_DISPCNT_Screen_Display_BG3)
			memset(renderer_ctx.line[Layer_BG3], -1, 240 * sizeof(uint32_t));
	}

	memset(RENDERER_LINE[Layer_OBJ], -1, 240 * sizeof(uint32_t));
	if(renderer_ctx.draw_sprites) gfxDrawSprites(renderer_idx);

	if(renderer_ctx.renderfunc_type == 2) {
		memset(RENDERER_LINE[Layer_WIN_OBJ], -1, 240 * sizeof(uint32_t));
		if(renderer_ctx.draw_objwin) gfxDrawOBJWin(renderer_idx);
	}

	GetRenderFunc(renderer_idx, renderer_ctx.renderfunc_mode, renderer_ctx.renderfunc_type)(renderer_idx);

	renderer_ctx.renderer_state = 0;
}

static void threaded_renderer_loop0(void* p) {
	int renderer_idx = 0;
	INIT_RENDERER_CONTEXT(renderer_idx);
	(void)p;

	/* Worker does line rendering only.  systemDrawScreen() (which calls
	 * the libretro video_refresh callback) is driven by the main thread
	 * after postRender() publishes vcount==159 -- video_refresh has
	 * window-thread affinity on Windows (cross-thread SendMessageW from
	 * vulkan_frame's SetWindowTextW title update deadlocks against the
	 * main thread's spin-wait in postRender), and libretro's contract
	 * already requires the callback to run on the retro_run thread. */
	while(renderer_ctx.renderer_control == 1) {
		if(renderer_ctx.renderer_state == 0) {
			SPIN_HINT();
			continue;
		}
		renderer_process_line(renderer_idx);
	}

	renderer_ctx.renderer_control = 0; /*loop is terminated. */
}

static void threaded_renderer_loop(void* p) {
	int renderer_idx = (int)(intptr_t)(p);
	INIT_RENDERER_CONTEXT(renderer_idx);

	if(renderer_idx < 1 || renderer_idx > 3)
		return;

	while(renderer_ctx.renderer_control == 1) {
		if(renderer_ctx.renderer_state == 0) {
			SPIN_HINT();
			continue;
		}
		renderer_process_line(renderer_idx);
	}

	renderer_ctx.renderer_control = 0; /*loop is terminated. */
}

static void fetchBackgroundOffset(int video_mode) {
	/*update gfxBG2X, gfxBG2Y, gfxBG3X, gfxBG3Y */
	switch(video_mode) {
	case 0:
		break;
	case 1:
		fetchDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
			io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD],
			&gfxBG2X, &gfxBG2Y, gfxBG2Changed);
		break;
	case 2:
		fetchDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
			io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD],
			&gfxBG2X, &gfxBG2Y, gfxBG2Changed);
		fetchDrawRotScreen(io_registers[REG_BG3CNT], BG3X_L, BG3X_H, BG3Y_L, BG3Y_H,
			io_registers[REG_BG3PA], io_registers[REG_BG3PB], io_registers[REG_BG3PC], io_registers[REG_BG3PD],
			&gfxBG3X, &gfxBG3Y, gfxBG3Changed);
		break;
	case 3:
		fetchDrawRotScreen16Bit(&gfxBG2X, &gfxBG2Y, gfxBG2Changed);
		break;
	case 4:
		fetchDrawRotScreen256(&gfxBG2X, &gfxBG2Y, gfxBG2Changed);
		break;
	case 5:
		fetchDrawRotScreen16Bit160(&gfxBG2X, &gfxBG2Y, gfxBG2Changed);
		break;
	default:
		return;
	}
}

static void postRender() {
	int u;

	int video_mode = R_DISPCNT_Video_Mode;
	bool draw_objwin = (graphics.layerEnable & 0x9000) == 0x9000;
	bool draw_sprites = R_DISPCNT_Screen_Display_OBJ;
	/* INIT_RENDERER_CONTEXT expands to a declaration in threaded mode and to a
	 * no-op expression in non-threaded mode; in C89 it must come BEFORE any
	 * statement (the spin-wait below) so the decl-after-statement rule is
	 * satisfied for the threaded build. */
#ifdef PER_FRAME_BATCHED
	INIT_RENDERER_CONTEXT(batched_publish_idx);
	/* No spin-wait and no state=1 publish in batched mode: each scanline gets
	 * its own dedicated context, so there is no producer/consumer overlap on
	 * a single context during the frame.  Rendering for all 160 scanlines is
	 * dispatched once at end-of-frame from the CPULoop. */
#else
	INIT_RENDERER_CONTEXT(threaded_renderer_idx);

	while(threaded_renderer_contexts[threaded_renderer_idx].renderer_state)
		SPIN_HINT();
#endif

	renderer_ctx.renderfunc_mode = renderfunc_mode;
	renderer_ctx.renderfunc_type = renderfunc_type;
	renderer_ctx.draw_objwin = draw_objwin;
	renderer_ctx.draw_sprites = draw_sprites;
	renderer_ctx.layers = graphics.layerEnable;
	renderer_ctx.mosaic = MOSAIC;
	renderer_ctx.bldmod = BLDMOD;
	renderer_ctx.vcount = io_registers[REG_VCOUNT];

	renderer_ctx.io_registers[REG_DISPCNT] = io_registers[REG_DISPCNT];
	renderer_ctx.io_registers[REG_DISPSTAT] = io_registers[REG_DISPSTAT];
	renderer_ctx.io_registers[REG_VCOUNT] = io_registers[REG_VCOUNT];

	renderer_ctx.io_registers[REG_BG0CNT] = io_registers[REG_BG0CNT];
	renderer_ctx.io_registers[REG_BG1CNT] = io_registers[REG_BG1CNT];
	renderer_ctx.io_registers[REG_BG2CNT] = io_registers[REG_BG2CNT];
	renderer_ctx.io_registers[REG_BG3CNT] = io_registers[REG_BG3CNT];

	renderer_ctx.io_registers[REG_BG0HOFS] = io_registers[REG_BG0HOFS];
	renderer_ctx.io_registers[REG_BG1HOFS] = io_registers[REG_BG1HOFS];
	renderer_ctx.io_registers[REG_BG2HOFS] = io_registers[REG_BG2HOFS];
	renderer_ctx.io_registers[REG_BG3HOFS] = io_registers[REG_BG3HOFS];
	renderer_ctx.io_registers[REG_BG0VOFS] = io_registers[REG_BG0VOFS];
	renderer_ctx.io_registers[REG_BG1VOFS] = io_registers[REG_BG1VOFS];
	renderer_ctx.io_registers[REG_BG2VOFS] = io_registers[REG_BG2VOFS];
	renderer_ctx.io_registers[REG_BG3VOFS] = io_registers[REG_BG3VOFS];

	renderer_ctx.io_registers[REG_BG2PA] = io_registers[REG_BG2PA];
	renderer_ctx.io_registers[REG_BG2PB] = io_registers[REG_BG2PB];
	renderer_ctx.io_registers[REG_BG2PC] = io_registers[REG_BG2PC];
	renderer_ctx.io_registers[REG_BG2PD] = io_registers[REG_BG2PD];
	renderer_ctx.io_registers[REG_BG3PA] = io_registers[REG_BG3PA];
	renderer_ctx.io_registers[REG_BG3PB] = io_registers[REG_BG3PB];
	renderer_ctx.io_registers[REG_BG3PC] = io_registers[REG_BG3PC];
	renderer_ctx.io_registers[REG_BG3PD] = io_registers[REG_BG3PD];

	renderer_ctx.io_registers[REG_BG2X_L] = io_registers[REG_BG2X_L];
	renderer_ctx.io_registers[REG_BG2X_H] = io_registers[REG_BG2X_H];
	renderer_ctx.io_registers[REG_BG2Y_L] = io_registers[REG_BG2Y_L];
	renderer_ctx.io_registers[REG_BG2Y_H] = io_registers[REG_BG2Y_H];
	renderer_ctx.io_registers[REG_BG3X_L] = io_registers[REG_BG3X_L];
	renderer_ctx.io_registers[REG_BG3X_H] = io_registers[REG_BG3X_H];
	renderer_ctx.io_registers[REG_BG3Y_L] = io_registers[REG_BG3Y_L];
	renderer_ctx.io_registers[REG_BG3Y_H] = io_registers[REG_BG3Y_H];

	renderer_ctx.io_registers[REG_WIN0H] = io_registers[REG_WIN0H];
	renderer_ctx.io_registers[REG_WIN1H] = io_registers[REG_WIN1H];
	renderer_ctx.io_registers[REG_WIN0V] = io_registers[REG_WIN0V];
	renderer_ctx.io_registers[REG_WIN1V] = io_registers[REG_WIN1V];
	renderer_ctx.io_registers[REG_WININ] = io_registers[REG_WININ];
	renderer_ctx.io_registers[REG_WINOUT] = io_registers[REG_WINOUT];

	renderer_ctx.io_registers[REG_BLDCNT] = io_registers[REG_BLDCNT];
	renderer_ctx.io_registers[REG_BLDALPHA] = io_registers[REG_BLDALPHA];
	renderer_ctx.io_registers[REG_BLDY] = io_registers[REG_BLDY];

	renderer_ctx.io_registers[REG_TM0D] = io_registers[REG_TM0D];
	renderer_ctx.io_registers[REG_TM1D] = io_registers[REG_TM1D];
	renderer_ctx.io_registers[REG_TM2D] = io_registers[REG_TM2D];
	renderer_ctx.io_registers[REG_TM3D] = io_registers[REG_TM3D];

	renderer_ctx.io_registers[REG_TM0CNT] = io_registers[REG_TM0CNT];
	renderer_ctx.io_registers[REG_TM1CNT] = io_registers[REG_TM1CNT];
	renderer_ctx.io_registers[REG_TM2CNT] = io_registers[REG_TM2CNT];
	renderer_ctx.io_registers[REG_TM3CNT] = io_registers[REG_TM3CNT];

	renderer_ctx.io_registers[REG_P1] = io_registers[REG_P1];
	renderer_ctx.io_registers[REG_P1CNT] = io_registers[REG_P1CNT];
	renderer_ctx.io_registers[REG_RCNT] = io_registers[REG_RCNT];
	renderer_ctx.io_registers[REG_IE] = io_registers[REG_IE];
	renderer_ctx.io_registers[REG_IF] = io_registers[REG_IF];
	renderer_ctx.io_registers[REG_IME] = io_registers[REG_IME];
	renderer_ctx.io_registers[REG_HALTCNT] = io_registers[REG_HALTCNT];

	renderer_ctx.bg2c = gfxBG2Changed;
	renderer_ctx.bg2x = gfxBG2X;
	renderer_ctx.bg2y = gfxBG2Y;
	renderer_ctx.bg2x_l = BG2X_L;
	renderer_ctx.bg2x_h = BG2X_H;
	renderer_ctx.bg2y_l = BG2Y_L;
	renderer_ctx.bg2y_h = BG2Y_H;

	if(video_mode == 2) {
		renderer_ctx.bg3c = gfxBG3Changed;
		renderer_ctx.bg3x = gfxBG3X;
		renderer_ctx.bg3y = gfxBG3Y;
		renderer_ctx.bg3x_l = BG3X_L;
		renderer_ctx.bg3x_h = BG3X_H;
		renderer_ctx.bg3y_l = BG3Y_L;
		renderer_ctx.bg3y_h = BG3Y_H;
	}

	for(u = 0; u < 2; ++u) {
		if(renderer_ctx.gfxinwin_ver[u] < threaded_gfxinwin_ver[u]) {
			renderer_ctx.gfxinwin_ver[u] = threaded_gfxinwin_ver[u];
#if HAVE_NEON
			neon_memcpy(renderer_ctx.gfxInWin[u], gfxInWin[u], sizeof(gfxInWin) / 2);
#else
			memcpy(renderer_ctx.gfxInWin[u], gfxInWin[u], sizeof(gfxInWin) / 2);
#endif
		}
	}

	fetchBackgroundOffset(video_mode);

	gfxBG2Changed = 0;
	if(video_mode == 2)	gfxBG3Changed = 0;

#if defined(MSB_FIRST) || defined(PER_FRAME_BATCHED)
	/* Snapshot host-endian palette + OAM into THIS context's buffers before
	 * the renderer reads them.  On BE this is the existing byte-swap shadow
	 * that lets the renderer skip per-pixel swaps.  In batched mode on LE
	 * it is required for correctness: all 160 scanlines render at
	 * end-of-frame, so without the per-line snapshot they would all see
	 * end-of-frame paletteRAM/oam rather than their own per-line state. */
	palette_native_sync(renderer_ctx.palette_native);
	oam_native_sync(renderer_ctx.oam_native);
#endif

	/*buffer is ready. */
#ifdef PER_FRAME_BATCHED
	/* No state=1 publish: in batched mode each context is private until
	 * end-of-frame, when the renderer drains all 160 in one pass. */
#else
	renderer_ctx.renderer_state = 1;
#endif

	/*notify screen is done. */
	if(renderer_ctx.vcount == 159) threaded_renderer_ready = 1;

#ifdef PER_FRAME_BATCHED
	/* Advance per-line publish index; clamp at 159 for safety in case a
	 * runaway vcount causes more than BATCHED_LINES postRender calls within
	 * one frame (shouldn't happen but cheap to guard).  Reset to 0 happens
	 * at end-of-frame in CPULoop after rendering is dispatched. */
	if(batched_publish_idx < THREADED_RENDERER_COUNT - 1)
		++batched_publish_idx;
#else
	threaded_renderer_idx = (threaded_renderer_idx + 1) % THREADED_RENDERER_COUNT;
#endif
}

#endif

#define CPUUpdateRender() { \
  	renderfunc_mode = R_DISPCNT_Video_Mode; \
    if((!fxOn && !windowOn && !R_DISPCNT_OBJ_Window_Display)) \
      	renderfunc_type = 0; \
    else if(fxOn && !windowOn && !R_DISPCNT_OBJ_Window_Display) \
      	renderfunc_type = 1; \
    else \
      	renderfunc_type = 2; \
}

renderfunc_t GetRenderFunc(int renderer_idx, int mode, int type) {
	switch((mode << 4) | type) {
		case 0x00: return mode0RenderLine;
		case 0x01: return mode0RenderLineNoWindow;
		case 0x02: return mode0RenderLineAll;
		case 0x10: return mode1RenderLine;
		case 0x11: return mode1RenderLineNoWindow;
		case 0x12: return mode1RenderLineAll;
		case 0x20: return mode2RenderLine;
		case 0x21: return mode2RenderLineNoWindow;
		case 0x22: return mode2RenderLineAll;
		case 0x30: return mode3RenderLine;
		case 0x31: return mode3RenderLineNoWindow;
		case 0x32: return mode3RenderLineAll;
		case 0x40: return mode4RenderLine;
		case 0x41: return mode4RenderLineNoWindow;
		case 0x42: return mode4RenderLineAll;
		case 0x50: return mode5RenderLine;
		case 0x51: return mode5RenderLineNoWindow;
		case 0x52: return mode5RenderLineAll;
		default: return NULL;
	}
}

bool CPUReadState(const uint8_t* data, unsigned size)
{
	int version;
	char romname[16];
	/* Track the end of the input buffer so each read can be bounds-checked.
	 * Frontends should pass the same `size` they got from retro_serialize_size,
	 * but a misbehaving or malicious caller could pass a smaller buffer. */
	const uint8_t* const data_end = data + size;
	#define BOUNDS_CHECK(n) do { \
		if ((size_t)(data_end - data) < (size_t)(n)) return false; \
	} while (0)

	BOUNDS_CHECK(sizeof(int));
	version = utilReadIntMem(&data);
	/* Accept the current version and the immediately previous one
	 * (v10 -> v11 changed pix removal and EEPROM layout). */
	if (version != SAVE_GAME_VERSION && version != SAVE_GAME_VERSION_10)
		return false;

	BOUNDS_CHECK(16);
	utilReadMem(romname, &data, 16);
	if (memcmp(&rom[0xa0], romname, 16) != 0)
		return false;

	/* Don't care about use bios ... */
	BOUNDS_CHECK(sizeof(int));
	utilReadIntMem(&data);

	BOUNDS_CHECK(sizeof(bus.reg));
	utilReadMem(&bus.reg[0], &data, sizeof(bus.reg));

	utilReadDataMem(&data, saveGameStruct);

	BOUNDS_CHECK(2 * sizeof(int));
	stopState = utilReadIntMem(&data) ? true : false;

	IRQTicks = utilReadIntMem(&data);
	if (IRQTicks > 0)
		intState = true;
	else
	{
		intState = false;
		IRQTicks = 0;
	}

	BOUNDS_CHECK(0x8000 + 0x400 + 0x40000 + 0x20000 + 0x400 + 0x400);
	utilReadMem(internalRAM, &data, 0x8000);
	utilReadMem(paletteRAM, &data, 0x400);
	utilReadMem(workRAM, &data, 0x40000);
	utilReadMem(vram, &data, 0x20000);
	utilReadMem(oam, &data, 0x400);
	if (version < SAVE_GAME_VERSION_11) {
		/* v10 saved a 160KB framebuffer mirror here. Skip past it -
		 * the renderer overwrites pix on the next scanline anyway. */
		const size_t old_pix_bytes = 4 * PIX_BUFFER_SCREEN_WIDTH * 160;
		BOUNDS_CHECK(old_pix_bytes);
		data += old_pix_bytes;
	}
	utilReadMem(ioMem, &data, 0x400);

	eepromReadGameMem(&data, version);
	flashReadGameMem(&data, version);
	soundReadGameMem(&data, version);
	rtcReadGameMem(&data);

	#undef BOUNDS_CHECK

	/*// Copypasta stuff ... */
	/* set pointers! */
	graphics.layerEnable = io_registers[REG_DISPCNT];

	CPUUpdateRender();

#if !THREADED_RENDERER
	memset(line[Layer_BG0], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG1], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG2], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG3], -1, 240 * sizeof(uint32_t));
#endif

	CPUUpdateWindow0();
	CPUUpdateWindow1();
	gbaSaveType = 0;
	switch(saveType) {
		case 0:
			cpuSaveGameFunc = flashSaveDecide;
			break;
		case 1:
			cpuSaveGameFunc = sramWrite;
			gbaSaveType = 1;
			break;
		case 2:
			cpuSaveGameFunc = flashWrite;
			gbaSaveType = 2;
			break;
		case 3:
			break;
		case 5:
			gbaSaveType = 5;
			break;
		default:
			break;
	}
	if(eepromInUse)
		gbaSaveType = 3;

	if(armState) {
		ARM_PREFETCH;
	} else {
		THUMB_PREFETCH;
	}

	CPUUpdateRegister(0x204, CPUReadHalfWordQuick(0x4000204));

	return true;
}


#define CPUSwap(a, b) \
a ^= b; \
b ^= a; \
a ^= b;

static void CPUSwitchMode(int mode, bool saveState, bool breakLoop)
{
	uint32_t CPSR;
	uint32_t SPSR;
	CPU_UPDATE_CPSR();

	switch(armMode) {
		case 0x10:
		case 0x1F:
			bus.reg[R13_USR].I = bus.reg[13].I;
			bus.reg[R14_USR].I = bus.reg[14].I;
			bus.reg[17].I = bus.reg[16].I;
			break;
		case 0x11:
			CPUSwap(bus.reg[R8_FIQ].I, bus.reg[8].I);
			CPUSwap(bus.reg[R9_FIQ].I, bus.reg[9].I);
			CPUSwap(bus.reg[R10_FIQ].I, bus.reg[10].I);
			CPUSwap(bus.reg[R11_FIQ].I, bus.reg[11].I);
			CPUSwap(bus.reg[R12_FIQ].I, bus.reg[12].I);
			bus.reg[R13_FIQ].I = bus.reg[13].I;
			bus.reg[R14_FIQ].I = bus.reg[14].I;
			bus.reg[SPSR_FIQ].I = bus.reg[17].I;
			break;
		case 0x12:
			bus.reg[R13_IRQ].I  = bus.reg[13].I;
			bus.reg[R14_IRQ].I  = bus.reg[14].I;
			bus.reg[SPSR_IRQ].I =  bus.reg[17].I;
			break;
		case 0x13:
			bus.reg[R13_SVC].I  = bus.reg[13].I;
			bus.reg[R14_SVC].I  = bus.reg[14].I;
			bus.reg[SPSR_SVC].I =  bus.reg[17].I;
			break;
		case 0x17:
			bus.reg[R13_ABT].I  = bus.reg[13].I;
			bus.reg[R14_ABT].I  = bus.reg[14].I;
			bus.reg[SPSR_ABT].I =  bus.reg[17].I;
			break;
		case 0x1b:
			bus.reg[R13_UND].I  = bus.reg[13].I;
			bus.reg[R14_UND].I  = bus.reg[14].I;
			bus.reg[SPSR_UND].I =  bus.reg[17].I;
			break;
	}

	CPSR = bus.reg[16].I;
	SPSR = bus.reg[17].I;

	switch(mode) {
		case 0x10:
		case 0x1F:
			bus.reg[13].I = bus.reg[R13_USR].I;
			bus.reg[14].I = bus.reg[R14_USR].I;
			bus.reg[16].I = SPSR;
			break;
		case 0x11:
			CPUSwap(bus.reg[8].I, bus.reg[R8_FIQ].I);
			CPUSwap(bus.reg[9].I, bus.reg[R9_FIQ].I);
			CPUSwap(bus.reg[10].I, bus.reg[R10_FIQ].I);
			CPUSwap(bus.reg[11].I, bus.reg[R11_FIQ].I);
			CPUSwap(bus.reg[12].I, bus.reg[R12_FIQ].I);
			bus.reg[13].I = bus.reg[R13_FIQ].I;
			bus.reg[14].I = bus.reg[R14_FIQ].I;
			if(saveState)
				bus.reg[17].I = CPSR; else
				bus.reg[17].I = bus.reg[SPSR_FIQ].I;
			break;
		case 0x12:
			bus.reg[13].I = bus.reg[R13_IRQ].I;
			bus.reg[14].I = bus.reg[R14_IRQ].I;
			bus.reg[16].I = SPSR;
			if(saveState)
				bus.reg[17].I = CPSR;
			else
				bus.reg[17].I = bus.reg[SPSR_IRQ].I;
			break;
		case 0x13:
			bus.reg[13].I = bus.reg[R13_SVC].I;
			bus.reg[14].I = bus.reg[R14_SVC].I;
			bus.reg[16].I = SPSR;
			if(saveState)
				bus.reg[17].I = CPSR;
			else
				bus.reg[17].I = bus.reg[SPSR_SVC].I;
			break;
		case 0x17:
			bus.reg[13].I = bus.reg[R13_ABT].I;
			bus.reg[14].I = bus.reg[R14_ABT].I;
			bus.reg[16].I = SPSR;
			if(saveState)
				bus.reg[17].I = CPSR;
			else
				bus.reg[17].I = bus.reg[SPSR_ABT].I;
			break;
		case 0x1b:
			bus.reg[13].I = bus.reg[R13_UND].I;
			bus.reg[14].I = bus.reg[R14_UND].I;
			bus.reg[16].I = SPSR;
			if(saveState)
				bus.reg[17].I = CPSR;
			else
				bus.reg[17].I = bus.reg[SPSR_UND].I;
			break;
		default:
			break;
	}
	armMode = mode;
	CPUUpdateFlags(breakLoop);
	CPU_UPDATE_CPSR();
}



static void doDMA(uint32_t *p_s, uint32_t *p_d, uint32_t si, uint32_t di, uint32_t c, int transfer32)
{
	uint32_t s = *p_s;
	uint32_t d = *p_d;
	int sm = s >> 24;
	int dm = d >> 24;
	int sw = 0;
	int dw = 0;
	int sc = c;
	int32_t sm_gt_15_mask;
	int32_t dm_gt_15_mask;

	cpuDmaRunning = true;
	cpuDmaPC = bus.reg[15].I;
	cpuDmaCount = c;

	/* This is done to get the correct waitstates. */
	sm_gt_15_mask = ((sm>15) | -(sm>15)) >> 31;
	dm_gt_15_mask = ((dm>15) | -(dm>15)) >> 31;
	sm = ((((15) & sm_gt_15_mask) | ((((sm) & ~(sm_gt_15_mask))))));
	dm = ((((15) & dm_gt_15_mask) | ((((dm) & ~(dm_gt_15_mask))))));

	/*if ((sm>=0x05) && (sm<=0x07) || (dm>=0x05) && (dm <=0x07)) */
	/*    blank = (((io_registers[REG_DISPSTAT] | ((io_registers[REG_DISPSTAT] >> 1)&1))==1) ?  true : false); */

	if(transfer32)
	{
		s &= 0xFFFFFFFC;
		if(s < 0x02000000 && (bus.reg[15].I >> 24))
		{
			while(c != 0)
			{
				CPUWriteMemory(d, 0);
				d += di;
				c--;
			};
		}
		else
		{
			while(c != 0)
			{
				uint32_t v = CPUReadMemory(s);
				cpuDmaLast = v;
				CPUWriteMemory(d, v);
				d += di;
				s += si;
				c--;
			};
		}
	}
	else
	{
		s &= 0xFFFFFFFE;
		si = (int)si >> 1;
		di = (int)di >> 1;
		if(s < 0x02000000 && (bus.reg[15].I >> 24))
		{
			while(c != 0)
			{
				CPUWriteHalfWord(d, 0);
				d += di;
				c--;
			};
		}
		else
		{
			while(c != 0)
			{
				cpuDmaLast = CPUReadHalfWord(s);
				CPUWriteHalfWord(d, cpuDmaLast);
				cpuDmaLast |= cpuDmaLast << 16;
				d += di;
				s += si;
				c--;
			};
		}
	}

	cpuDmaCount = 0;
	cpuDmaRunning = false;

	if(transfer32)
	{
		sw = 1+memoryWaitSeq32[sm & 15];
		dw = 1+memoryWaitSeq32[dm & 15];
		cpuDmaTicksToUpdate += (sw+dw)*(sc-1) + 6 + memoryWait32[sm & 15] + memoryWaitSeq32[dm & 15];
	}
	else
	{
		sw = 1+memoryWaitSeq[sm & 15];
		dw = 1+memoryWaitSeq[dm & 15];
		cpuDmaTicksToUpdate += (sw+dw)*(sc-1) + 6 + memoryWait[sm & 15] + memoryWaitSeq[dm & 15];
	}
	*p_s = s;
	*p_d = d;
}


void CPUCheckDMA(int reason, int dmamask)
{
	uint32_t arrayval[] = {4, (uint32_t)-4, 0, 4};
	/* DMA 0 */
	if((DM0CNT_H & 0x8000) && (dmamask & 1))
	{
		if(((DM0CNT_H >> 12) & 3) == reason)
		{
			uint32_t sourceIncrement, destIncrement;
			uint32_t condition1 = ((DM0CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM0CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			doDMA(&dma0Source, &dma0Dest, sourceIncrement, destIncrement,
					DM0CNT_L ? DM0CNT_L : 0x4000,
					DM0CNT_H & 0x0400);

			if(DM0CNT_H & 0x4000)
			{
				{ uint16_t _v = (io_registers[REG_IF]) | (0x0100); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM0CNT_H >> 5) & 3) == 3) {
				dma0Dest = DM0DAD_L | (DM0DAD_H << 16);
			}

			if(!(DM0CNT_H & 0x0200) || (reason == 0)) {
				{ uint16_t _v = (DM0CNT_H) & (0x7FFF); DM0CNT_H = _v; UPDATE_REG(0xBA, _v); }
			}
		}
	}

	/* DMA 1 */
	if((DM1CNT_H & 0x8000) && (dmamask & 2)) {
		if(((DM1CNT_H >> 12) & 3) == reason) {
			uint32_t sourceIncrement, destIncrement;
			uint32_t di_value, c_value, transfer_value;
			uint32_t condition1 = ((DM1CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM1CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			if(reason == 3)
			{
				di_value = 0;
				c_value = 4;
				transfer_value = 0x0400;
			}
			else
			{
				di_value = destIncrement;
				c_value = DM1CNT_L ? DM1CNT_L : 0x4000;
				transfer_value = DM1CNT_H & 0x0400;
			}
			doDMA(&dma1Source, &dma1Dest, sourceIncrement, di_value, c_value, transfer_value);

			if(DM1CNT_H & 0x4000) {
				{ uint16_t _v = (io_registers[REG_IF]) | (0x0200); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM1CNT_H >> 5) & 3) == 3) {
				dma1Dest = DM1DAD_L | (DM1DAD_H << 16);
			}

			if(!(DM1CNT_H & 0x0200) || (reason == 0)) {
				{ uint16_t _v = (DM1CNT_H) & (0x7FFF); DM1CNT_H = _v; UPDATE_REG(0xC6, _v); }
			}
		}
	}

	/* DMA 2 */
	if((DM2CNT_H & 0x8000) && (dmamask & 4)) {
		if(((DM2CNT_H >> 12) & 3) == reason) {
			uint32_t sourceIncrement, destIncrement;
			uint32_t di_value, c_value, transfer_value;
			uint32_t condition1 = ((DM2CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM2CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			if(reason == 3)
			{
				di_value = 0;
				c_value = 4;
				transfer_value = 0x0400;
			}
			else
			{
				di_value = destIncrement;
				c_value = DM2CNT_L ? DM2CNT_L : 0x4000;
				transfer_value = DM2CNT_H & 0x0400;
			}
			doDMA(&dma2Source, &dma2Dest, sourceIncrement, di_value, c_value, transfer_value);

			if(DM2CNT_H & 0x4000) {
				{ uint16_t _v = (io_registers[REG_IF]) | (0x0400); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM2CNT_H >> 5) & 3) == 3) {
				dma2Dest = DM2DAD_L | (DM2DAD_H << 16);
			}

			if(!(DM2CNT_H & 0x0200) || (reason == 0)) {
				{ uint16_t _v = (DM2CNT_H) & (0x7FFF); DM2CNT_H = _v; UPDATE_REG(0xD2, _v); }
			}
		}
	}

	/* DMA 3 */
	if((DM3CNT_H & 0x8000) && (dmamask & 8))
	{
		if(((DM3CNT_H >> 12) & 3) == reason)
		{
			uint32_t sourceIncrement, destIncrement;
			uint32_t condition1 = ((DM3CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM3CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			doDMA(&dma3Source, &dma3Dest, sourceIncrement, destIncrement,
					DM3CNT_L ? DM3CNT_L : 0x10000,
					DM3CNT_H & 0x0400);
			if(DM3CNT_H & 0x4000) {
				{ uint16_t _v = (io_registers[REG_IF]) | (0x0800); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM3CNT_H >> 5) & 3) == 3) {
				dma3Dest = DM3DAD_L | (DM3DAD_H << 16);
			}

			if(!(DM3CNT_H & 0x0200) || (reason == 0)) {
				{ uint16_t _v = (DM3CNT_H) & (0x7FFF); DM3CNT_H = _v; UPDATE_REG(0xDE, _v); }
			}
		}
	}
}

/* address_lut indirection table removed; CPUUpdateRegister now uses
 * io_registers[address >> 1] directly. Saved ~6 KB of pointer storage
 * and eliminated a NULL-deref hazard on unmapped IO addresses. */


void CPUUpdateRegister(uint32_t address, uint16_t value)
{
	switch(address)
	{
		case 0x00: /* DISPCNT */
			{
				bool change;
				bool changeBG;
				uint16_t changeBGon;
				if((value & 7) > 5) /* display modes 6,7 are prohibited - keep prior mode */
					value = (value & ~7) | (io_registers[REG_DISPCNT] & 7);

				change = (0 != ((io_registers[REG_DISPCNT] ^ value) & 0x80));
				changeBG = (0 != ((io_registers[REG_DISPCNT] ^ value) & 0x0F00));
				changeBGon = ((~io_registers[REG_DISPCNT]) & value) & 0x0F00; /* these layers are being activated */

				{ uint16_t _v = (value & 0xFFF7); io_registers[REG_DISPCNT] = _v; UPDATE_REG(0x00, _v); }

				graphics.layerEnable = value;

				if(changeBGon)
				{
					graphics.layerEnableDelay = 4;
					graphics.layerEnable &= ~changeBGon;
				}

				windowOn = (graphics.layerEnable & 0x6000) ? true : false;
				if(change && !((value & 0x80)))
				{
					if(!(io_registers[REG_DISPSTAT] & 1))
					{
						graphics.lcdTicks = 1008;
						{ uint16_t _v = (io_registers[REG_DISPSTAT]) & (0xFFFC); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
						CPUCompareVCOUNT();
					}
				}

				CPUUpdateRender();

				/* we only care about changes in BG0-BG3 */
				if(changeBG)
				{
#if THREADED_RENDERER
					++threaded_background_ver;
#else
					if(!R_DISPCNT_Screen_Display_BG0)
						memset(line[Layer_BG0], -1, 240 * sizeof(uint32_t));
					if(!R_DISPCNT_Screen_Display_BG1)
						memset(line[Layer_BG1], -1, 240 * sizeof(uint32_t));
					if(!R_DISPCNT_Screen_Display_BG2)
						memset(line[Layer_BG2], -1, 240 * sizeof(uint32_t));
					if(!R_DISPCNT_Screen_Display_BG3)
						memset(line[Layer_BG3], -1, 240 * sizeof(uint32_t));
#endif
				}
				break;
			}
		case 0x04: /* DISPSTAT */
			{ uint16_t _v = (value & 0xFF38) | (io_registers[REG_DISPSTAT] & 7); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
			break;
		case 0x06:
			/* not writable */
			break;
		case 0x08: /* BG0CNT */
		case 0x0A: /* BG1CNT */
		{
			uint16_t v = value & 0xDFCF;
			io_registers[address >> 1] = v;
			UPDATE_REG(address, v);
			break;
		}
		case 0x0C: /* BG2CNT */
		case 0x0E: /* BG3CNT */
		{
			uint16_t v = value & 0xFFCF;
			io_registers[address >> 1] = v;
			UPDATE_REG(address, v);
			break;
		}
		case 0x10: /* BG0HOFS */
		case 0x12: /* BG0VOFS */
		case 0x14: /* BG1HOFS */
		case 0x16: /* BG1VOFS */
		case 0x18: /* BG2HOFS */
		case 0x1A: /* BG2VOFS */
		case 0x1C: /* BG3HOFS */
		case 0x1E: /* BG3VOFS */
		{
			uint16_t v = value & 511;
			io_registers[address >> 1] = v;
			UPDATE_REG(address, v);
			break;
		}
		case 0x20: /* BG2PA */
		case 0x22: /* BG2PB */
		case 0x24: /* BG2PC */
		case 0x26: /* BG2PD */
			io_registers[address >> 1] = value;
			UPDATE_REG(address, value);
			break;
		case 0x28:
			{ uint16_t _v = value; BG2X_L = _v; UPDATE_REG(0x28, _v); }
			gfxBG2Changed |= 1;
			break;
		case 0x2A:
			{ uint16_t _v = (value & 0xFFF); BG2X_H = _v; UPDATE_REG(0x2A, _v); }
			gfxBG2Changed |= 1;
			break;
		case 0x2C:
			{ uint16_t _v = value; BG2Y_L = _v; UPDATE_REG(0x2C, _v); }
			gfxBG2Changed |= 2;
			break;
		case 0x2E:
			{ uint16_t _v = value & 0xFFF; BG2Y_H = _v; UPDATE_REG(0x2E, _v); }
			gfxBG2Changed |= 2;
			break;
		case 0x30: /* BG3PA */
		case 0x32: /* BG3PB */
		case 0x34: /* BG3PC */
		case 0x36: /* BG3PD */
			io_registers[address >> 1] = value;
			UPDATE_REG(address, value);
			break;
		case 0x38:
			{ uint16_t _v = value; BG3X_L = _v; UPDATE_REG(0x38, _v); }
			gfxBG3Changed |= 1;
			break;
		case 0x3A:
			{ uint16_t _v = value & 0xFFF; BG3X_H = _v; UPDATE_REG(0x3A, _v); }
			gfxBG3Changed |= 1;
			break;
		case 0x3C:
			{ uint16_t _v = value; BG3Y_L = _v; UPDATE_REG(0x3C, _v); }
			gfxBG3Changed |= 2;
			break;
		case 0x3E:
			{ uint16_t _v = value & 0xFFF; BG3Y_H = _v; UPDATE_REG(0x3E, _v); }
			gfxBG3Changed |= 2;
			break;
		case 0x40:
			{ uint16_t _v = value; io_registers[REG_WIN0H] = _v; UPDATE_REG(0x40, _v); }
			CPUUpdateWindow0();
			break;
		case 0x42:
			{ uint16_t _v = value; io_registers[REG_WIN1H] = _v; UPDATE_REG(0x42, _v); }
			CPUUpdateWindow1();
			break;
		case 0x44:
		case 0x46:
			io_registers[address >> 1] = value;
			UPDATE_REG(address, value);
			break;
		case 0x48: /* WININ */
		case 0x4A: /* WINOUT */
		{
			uint16_t v = value & 0x3F3F;
			io_registers[address >> 1] = v;
			UPDATE_REG(address, v);
			break;
		}
		case 0x4C:
			{ uint16_t _v = value; MOSAIC = _v; UPDATE_REG(0x4C, _v); }
			break;
		case 0x50:
			{ uint16_t _v = value & 0x3FFF; BLDMOD = _v; UPDATE_REG(0x50, _v); }
			fxOn = ((BLDMOD>>6)&3) != 0;
			CPUUpdateRender();
			break;
		case 0x52:
			{ uint16_t _v = value & 0x1F1F; COLEV = _v; UPDATE_REG(0x52, _v); }
			break;
		case 0x54:
			{ uint16_t _v = value & 0x1F; COLY = _v; UPDATE_REG(0x54, _v); }
			break;
		case 0x60:
		case 0x62:
		case 0x64:
		case 0x68:
		case 0x6c:
		case 0x70:
		case 0x72:
		case 0x74:
		case 0x78:
		case 0x7c:
		case 0x80:
		case 0x84:
			soundEvent_u8(table[(int32_t)(address & 0xFF) - 0x60], (uint32_t)(address & 0xFF), (uint8_t)(value & 0xFF));
			soundEvent_u8(table[(int32_t)((address & 0xFF) + 1) - 0x60], (uint32_t)((address & 0xFF) + 1), (uint8_t)(value >> 8));
			break;
		case 0x82:
		case 0x88:
		case 0xa0:
		case 0xa2:
		case 0xa4:
		case 0xa6:
		case 0x90:
		case 0x92:
		case 0x94:
		case 0x96:
		case 0x98:
		case 0x9a:
		case 0x9c:
		case 0x9e:
			soundEvent_u16(address&0xFF, value);
			break;
		case 0xB0:
			{ uint16_t _v = value; DM0SAD_L = _v; UPDATE_REG(0xB0, _v); }
			break;
		case 0xB2:
			{ uint16_t _v = value & 0x07FF; DM0SAD_H = _v; UPDATE_REG(0xB2, _v); }
			break;
		case 0xB4:
			{ uint16_t _v = value; DM0DAD_L = _v; UPDATE_REG(0xB4, _v); }
			break;
		case 0xB6:
			{ uint16_t _v = value & 0x07FF; DM0DAD_H = _v; UPDATE_REG(0xB6, _v); }
			break;
		case 0xB8:
			DM0CNT_L = value & 0x3FFF;
			UPDATE_REG(0xB8, 0);
			break;
		case 0xBA:
			{
				bool start = ((DM0CNT_H ^ value) & 0x8000) ? true : false;
				value &= 0xF7E0;

				{ uint16_t _v = value; DM0CNT_H = _v; UPDATE_REG(0xBA, _v); }

				if(start && (value & 0x8000))
				{
					dma0Source = DM0SAD_L | (DM0SAD_H << 16);
					dma0Dest = DM0DAD_L | (DM0DAD_H << 16);
					CPUCheckDMA(0, 1);
				}
			}
			break;
		case 0xBC:
			{ uint16_t _v = value; DM1SAD_L = _v; UPDATE_REG(0xBC, _v); }
			break;
		case 0xBE:
			{ uint16_t _v = value & 0x0FFF; DM1SAD_H = _v; UPDATE_REG(0xBE, _v); }
			break;
		case 0xC0:
			{ uint16_t _v = value; DM1DAD_L = _v; UPDATE_REG(0xC0, _v); }
			break;
		case 0xC2:
			{ uint16_t _v = value & 0x07FF; DM1DAD_H = _v; UPDATE_REG(0xC2, _v); }
			break;
		case 0xC4:
			DM1CNT_L = value & 0x3FFF;
			UPDATE_REG(0xC4, 0);
			break;
		case 0xC6:
			{
				bool start = ((DM1CNT_H ^ value) & 0x8000) ? true : false;
				value &= 0xF7E0;

				{ uint16_t _v = value; DM1CNT_H = _v; UPDATE_REG(0xC6, _v); }

				if(start && (value & 0x8000))
				{
					dma1Source = DM1SAD_L | (DM1SAD_H << 16);
					dma1Dest = DM1DAD_L | (DM1DAD_H << 16);
					CPUCheckDMA(0, 2);
				}
			}
			break;
		case 0xC8:
			{ uint16_t _v = value; DM2SAD_L = _v; UPDATE_REG(0xC8, _v); }
			break;
		case 0xCA:
			{ uint16_t _v = value & 0x0FFF; DM2SAD_H = _v; UPDATE_REG(0xCA, _v); }
			break;
		case 0xCC:
			{ uint16_t _v = value; DM2DAD_L = _v; UPDATE_REG(0xCC, _v); }
			break;
		case 0xCE:
			{ uint16_t _v = value & 0x07FF; DM2DAD_H = _v; UPDATE_REG(0xCE, _v); }
			break;
		case 0xD0:
			DM2CNT_L = value & 0x3FFF;
			UPDATE_REG(0xD0, 0);
			break;
		case 0xD2:
			{
				bool start = ((DM2CNT_H ^ value) & 0x8000) ? true : false;

				value &= 0xF7E0;

				{ uint16_t _v = value; DM2CNT_H = _v; UPDATE_REG(0xD2, _v); }

				if(start && (value & 0x8000)) {
					dma2Source = DM2SAD_L | (DM2SAD_H << 16);
					dma2Dest = DM2DAD_L | (DM2DAD_H << 16);

					CPUCheckDMA(0, 4);
				}
			}
			break;
		case 0xD4:
			{ uint16_t _v = value; DM3SAD_L = _v; UPDATE_REG(0xD4, _v); }
			break;
		case 0xD6:
			{ uint16_t _v = value & 0x0FFF; DM3SAD_H = _v; UPDATE_REG(0xD6, _v); }
			break;
		case 0xD8:
			{ uint16_t _v = value; DM3DAD_L = _v; UPDATE_REG(0xD8, _v); }
			break;
		case 0xDA:
			{ uint16_t _v = value & 0x0FFF; DM3DAD_H = _v; UPDATE_REG(0xDA, _v); }
			break;
		case 0xDC:
			DM3CNT_L = value;
			UPDATE_REG(0xDC, 0);
			break;
		case 0xDE:
			{
				bool start = ((DM3CNT_H ^ value) & 0x8000) ? true : false;

				value &= 0xFFE0;

				{ uint16_t _v = value; DM3CNT_H = _v; UPDATE_REG(0xDE, _v); }

				if(start && (value & 0x8000)) {
					dma3Source = DM3SAD_L | (DM3SAD_H << 16);
					dma3Dest = DM3DAD_L | (DM3DAD_H << 16);
					CPUCheckDMA(0,8);
				}
			}
			break;
		case 0x100:
			timer0Reload = value;
			break;
		case 0x102:
			timer0Value = value;
			timerOnOffDelay|=1;
			cpuNextEvent = cpuTotalTicks;
			break;
		case 0x104:
			timer1Reload = value;
			break;
		case 0x106:
			timer1Value = value;
			timerOnOffDelay|=2;
			cpuNextEvent = cpuTotalTicks;
			break;
		case 0x108:
			timer2Reload = value;
			break;
		case 0x10A:
			timer2Value = value;
			timerOnOffDelay|=4;
			cpuNextEvent = cpuTotalTicks;
			break;
		case 0x10C:
			timer3Reload = value;
			break;
		case 0x10E:
			timer3Value = value;
			timerOnOffDelay|=8;
			cpuNextEvent = cpuTotalTicks;
			break;
		case 0x130:
			{ uint16_t _v = (io_registers[REG_P1]) | ((value & 0x3FF)); io_registers[REG_P1] = _v; UPDATE_REG(0x130, _v); }
			break;
		case 0x132:
			UPDATE_REG(0x132, value & 0xC3FF);
			break;
		case 0x200:
			{ uint16_t _v = value & 0x3FFF; io_registers[REG_IE] = _v; UPDATE_REG(0x200, _v); }
			if ((io_registers[REG_IME] & 1) && (io_registers[REG_IF] & io_registers[REG_IE]) && armIrqEnable)
				cpuNextEvent = cpuTotalTicks;
			break;
		case 0x202:
			{ uint16_t _v = (io_registers[REG_IF]) ^ ((value & io_registers[REG_IF])); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
			break;
		case 0x204:
		    memoryWait[0x0e] = memoryWaitSeq[0x0e] = gamepakRamWaitState[value & 3];

#if  USE_TWEAK_SPEEDHACK
            memoryWait[0x08] = memoryWait[0x09] = 3;
            memoryWaitSeq[0x08] = memoryWaitSeq[0x09] = 1;
            memoryWait[0x0a] = memoryWait[0x0b] = 3;
            memoryWaitSeq[0x0a] = memoryWaitSeq[0x0b] = 1;
            memoryWait[0x0c] = memoryWait[0x0d] = 3;
            memoryWaitSeq[0x0c] = memoryWaitSeq[0x0d] = 1;
#else
            memoryWait[0x08] = memoryWait[0x09] = gamepakWaitState[(value >> 2) & 3];
            memoryWaitSeq[0x08] = memoryWaitSeq[0x09] = gamepakWaitState0[(value >> 4) & 1];
            memoryWait[0x0a] = memoryWait[0x0b] = gamepakWaitState[(value >> 5) & 3];
            memoryWaitSeq[0x0a] = memoryWaitSeq[0x0b] = gamepakWaitState1[(value >> 7) & 1];
            memoryWait[0x0c] = memoryWait[0x0d] = gamepakWaitState[(value >> 8) & 3];
            memoryWaitSeq[0x0c] = memoryWaitSeq[0x0d] = gamepakWaitState2[(value >> 10) & 1];
#endif

			memoryWait32[8] = memoryWait[8] + memoryWaitSeq[8] + 1;
			memoryWaitSeq32[8] = (memoryWaitSeq[8] << 1) + 1;
			memoryWait32[9] = memoryWait[9] + memoryWaitSeq[9] + 1;
			memoryWaitSeq32[9] = (memoryWaitSeq[9] << 1) + 1;
			memoryWait32[10] = memoryWait[10] + memoryWaitSeq[10] + 1;
			memoryWaitSeq32[10] = (memoryWaitSeq[10] << 1) + 1;
			memoryWait32[11] = memoryWait[11] + memoryWaitSeq[11] + 1;
			memoryWaitSeq32[11] = (memoryWaitSeq[11] << 1) + 1;
			memoryWait32[12] = memoryWait[12] + memoryWaitSeq[12] + 1;
			memoryWaitSeq32[12] = (memoryWaitSeq[12] << 1) + 1;
			memoryWait32[13] = memoryWait[13] + memoryWaitSeq[13] + 1;
			memoryWaitSeq32[13] = (memoryWaitSeq[13] << 1) + 1;
			memoryWait32[14] = memoryWait[14] + memoryWaitSeq[14] + 1;
			memoryWaitSeq32[14] = (memoryWaitSeq[14] << 1) + 1;

			if((value & 0x4000) == 0x4000)
				bus.busPrefetchEnable = true;
			else
				bus.busPrefetchEnable = false;

			bus.busPrefetch = false;
			bus.busPrefetchCount = 0;

			UPDATE_REG(0x204, value & 0x7FFF);
			break;
		case 0x208:
			{ uint16_t _v = value & 1; io_registers[REG_IME] = _v; UPDATE_REG(0x208, _v); }
			if ((io_registers[REG_IME] & 1) && (io_registers[REG_IF] & io_registers[REG_IE]) && armIrqEnable)
				cpuNextEvent = cpuTotalTicks;
			break;
		case 0x300:
			if(value != 0)
				value &= 0xFFFE;
			UPDATE_REG(0x300, value);
			break;
		default:
			UPDATE_REG(address&0x3FE, value);
			break;
	}
}

/* The CBA cheat CRC table is built from the ROM and cached across calls.
 * Defined here (earlier in the file) so CPUInit can reset the flag on game
 * load. The remaining cheat-system globals stay grouped lower down. */
static bool cheatsCBATableGenerated = false;

void CPUInit(const char *biosFileName, bool useBiosFile)
{
	int i = 0;
	/* The CBA cheat CRC table is built from the ROM's first 64KB and cached
	 * across calls. When a new ROM is loaded into the same process the cache
	 * goes stale - reset the flag here so the next CBA cheat triggers a
	 * fresh table build. */
	cheatsCBATableGenerated = false;

#ifdef MSB_FIRST
	if(!cpuBiosSwapped)
   {
		for(i = 0; i < (int)(sizeof(myROM)/4); i++)
      {
			WRITE32LE(&myROM[i], myROM[i]);
		}
		cpuBiosSwapped = true;
	}
#endif
	gbaSaveType = 0;
	eepromInUse = 0;
	saveType = 0;
	useBios = false;

#ifdef HAVE_HLE_BIOS
	if(useBiosFile)
	{
		int size = 0x4000;
		if(utilLoad(biosFileName, bios, &size))
		{
			if(size == 0x4000)
				useBios = true;
		}
	}

	if(!useBios)
#endif
		memcpy(bios, myROM, sizeof(myROM));

	biosProtected[0] = 0x00;
	biosProtected[1] = 0xf0;
	biosProtected[2] = 0x29;
	biosProtected[3] = 0xe1;

	for(i = 0; i < 256; i++)
	{
		int count = 0;
		int j;
		for(j = 0; j < 8; j++)
			if(i & (1 << j))
				count++;
		cpuBitsSet[i] = count;
		/* (a second `for(j=0;j<8;j++) if(i&(1<<j)) break;` loop used to live
		 * here, but its result `j` was never stored anywhere - dead code.) */
	}

	for(i = 0; i < 0x400; i++)
		ioReadable[i] = true;
	for(i = 0x10; i < 0x48; i++)
		ioReadable[i] = false;
	for(i = 0x4c; i < 0x50; i++)
		ioReadable[i] = false;
	for(i = 0x54; i < 0x60; i++)
		ioReadable[i] = false;
	for(i = 0x8c; i < 0x90; i++)
		ioReadable[i] = false;
	for(i = 0xa0; i < 0xb8; i++)
		ioReadable[i] = false;
	for(i = 0xbc; i < 0xc4; i++)
		ioReadable[i] = false;
	for(i = 0xc8; i < 0xd0; i++)
		ioReadable[i] = false;
	for(i = 0xd4; i < 0xdc; i++)
		ioReadable[i] = false;
	for(i = 0xe0; i < 0x100; i++)
		ioReadable[i] = false;
	for(i = 0x110; i < 0x120; i++)
		ioReadable[i] = false;
	for(i = 0x12c; i < 0x130; i++)
		ioReadable[i] = false;
	for(i = 0x138; i < 0x140; i++)
		ioReadable[i] = false;
	for(i = 0x144; i < 0x150; i++)
		ioReadable[i] = false;
	for(i = 0x15c; i < 0x200; i++)
		ioReadable[i] = false;
	for(i = 0x20c; i < 0x300; i++)
		ioReadable[i] = false;
	for(i = 0x304; i < 0x400; i++)
		ioReadable[i] = false;

	if(romSize < 0x1fe2000) {
		WRITE16LE(&rom[0x1fe209c], 0xdffa); /* SWI 0xFA */
		WRITE16LE(&rom[0x1fe209e], 0x4770); /* BX LR */
	}

	graphics.layerEnable = 0xff00;
	graphics.layerEnableDelay = 1;
	io_registers[REG_DISPCNT] = 0x0080;
	io_registers[REG_DISPSTAT] = 0;
	graphics.lcdTicks = (useBios && !skipBios) ? 1008 : 208;

	/* address_lut init removed: CPUUpdateRegister addresses io_registers
	 * directly via address >> 1, which is the same mapping the lut encoded. */
}

void CPUReset (void)
{
	int i;
	if(gbaSaveType == 0)
	{
		if(eepromInUse)
			gbaSaveType = 3;
		else
			switch(saveType)
			{
				case 1:
					gbaSaveType = 1;
					break;
				case 2:
					gbaSaveType = 2;
					break;
			}
	}
	rtcReset();
#if USE_MOTION_SENSOR
	hardware_reset();
#endif
	memset(&bus.reg[0], 0, sizeof(bus.reg));	/* clean registers */
	memset(oam, 0, 0x400);				/* clean OAM */
	memset(paletteRAM, 0, 0x400);		/* clean palette */
	memset(pix, 0, 2 * PIX_BUFFER_SCREEN_WIDTH * 160);	/* clean picture (match alloc size) */
	memset(vram, 0, 0x20000);			/* clean vram */
	memset(ioMem, 0, 0x400);			/* clean io memory */

	io_registers[REG_DISPCNT]  = 0x0080;
	io_registers[REG_DISPSTAT] = 0x0000;
	io_registers[REG_VCOUNT]   = (useBios && !skipBios) ? 0 :0x007E;
	io_registers[REG_BG0CNT]   = 0x0000;
	io_registers[REG_BG1CNT]   = 0x0000;
	io_registers[REG_BG2CNT]   = 0x0000;
	io_registers[REG_BG3CNT]   = 0x0000;
	io_registers[REG_BG0HOFS]  = 0x0000;
	io_registers[REG_BG0VOFS]  = 0x0000;
	io_registers[REG_BG1HOFS]  = 0x0000;
	io_registers[REG_BG1VOFS]  = 0x0000;
	io_registers[REG_BG2HOFS]  = 0x0000;
	io_registers[REG_BG2VOFS]  = 0x0000;
	io_registers[REG_BG3HOFS]  = 0x0000;
	io_registers[REG_BG3VOFS]  = 0x0000;
	io_registers[REG_BG2PA]    = 0x0100;
	io_registers[REG_BG2PB]    = 0x0000;
	io_registers[REG_BG2PC]    = 0x0000;
	io_registers[REG_BG2PD]    = 0x0100;
	BG2X_L   = 0x0000;
	BG2X_H   = 0x0000;
	BG2Y_L   = 0x0000;
	BG2Y_H   = 0x0000;
	io_registers[REG_BG3PA]    = 0x0100;
	io_registers[REG_BG3PB]    = 0x0000;
	io_registers[REG_BG3PC]    = 0x0000;
	io_registers[REG_BG3PD]    = 0x0100;
	BG3X_L   = 0x0000;
	BG3X_H   = 0x0000;
	BG3Y_L   = 0x0000;
	BG3Y_H   = 0x0000;
	io_registers[REG_WIN0H]    = 0x0000;
	io_registers[REG_WIN1H]    = 0x0000;
	io_registers[REG_WIN0V]    = 0x0000;
	io_registers[REG_WIN1V]    = 0x0000;
	io_registers[REG_WININ]    = 0x0000;
	io_registers[REG_WINOUT]   = 0x0000;
	MOSAIC   = 0x0000;
	BLDMOD   = 0x0000;
	COLEV    = 0x0000;
	COLY     = 0x0000;
	DM0SAD_L = 0x0000;
	DM0SAD_H = 0x0000;
	DM0DAD_L = 0x0000;
	DM0DAD_H = 0x0000;
	DM0CNT_L = 0x0000;
	DM0CNT_H = 0x0000;
	DM1SAD_L = 0x0000;
	DM1SAD_H = 0x0000;
	DM1DAD_L = 0x0000;
	DM1DAD_H = 0x0000;
	DM1CNT_L = 0x0000;
	DM1CNT_H = 0x0000;
	DM2SAD_L = 0x0000;
	DM2SAD_H = 0x0000;
	DM2DAD_L = 0x0000;
	DM2DAD_H = 0x0000;
	DM2CNT_L = 0x0000;
	DM2CNT_H = 0x0000;
	DM3SAD_L = 0x0000;
	DM3SAD_H = 0x0000;
	DM3DAD_L = 0x0000;
	DM3DAD_H = 0x0000;
	DM3CNT_L = 0x0000;
	DM3CNT_H = 0x0000;
	io_registers[REG_TM0D]     = 0x0000;
	io_registers[REG_TM0CNT]   = 0x0000;
	io_registers[REG_TM1D]     = 0x0000;
	io_registers[REG_TM1CNT]   = 0x0000;
	io_registers[REG_TM2D]     = 0x0000;
	io_registers[REG_TM2CNT]   = 0x0000;
	io_registers[REG_TM3D]     = 0x0000;
	io_registers[REG_TM3CNT]   = 0x0000;
	io_registers[REG_P1]       = 0x03FF;
	io_registers[REG_IE]       = 0x0000;
	io_registers[REG_IF]       = 0x0000;
	io_registers[REG_IME]      = 0x0000;

	armMode = 0x1F;

#ifdef HAVE_HLE_BIOS
	if(useBios && !skipBios)
	{
		bus.reg[15].I = 0x00000000;
		armMode = 0x13;
		armIrqEnable = false;
	}
	else
#endif
	{
		bus.reg[13].I = 0x03007F00;
		bus.reg[15].I = 0x08000000;
		bus.reg[16].I = 0x00000000;
		bus.reg[R13_IRQ].I = 0x03007FA0;
		bus.reg[R13_SVC].I = 0x03007FE0;
		armIrqEnable = true;
	}

	armState = true;
	C_FLAG = V_FLAG = N_FLAG = Z_FLAG = false;
	UPDATE_REG(0x00, io_registers[REG_DISPCNT]);
	UPDATE_REG(0x06, io_registers[REG_VCOUNT]);
	UPDATE_REG(0x20, io_registers[REG_BG2PA]);
	UPDATE_REG(0x26, io_registers[REG_BG2PD]);
	UPDATE_REG(0x30, io_registers[REG_BG3PA]);
	UPDATE_REG(0x36, io_registers[REG_BG3PD]);
	UPDATE_REG(0x130, io_registers[REG_P1]);
	UPDATE_REG(0x88, 0x200);

	/* disable FIQ */
	bus.reg[16].I |= 0x40;

	CPU_UPDATE_CPSR();

	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;

	/* reset internal state */
	holdState = false;

	biosProtected[0] = 0x00;
	biosProtected[1] = 0xf0;
	biosProtected[2] = 0x29;
	biosProtected[3] = 0xe1;

	graphics.lcdTicks = (useBios && !skipBios) ? 1008 : 208;
	timer0On = false;
	timer0Ticks = 0;
	timer0Reload = 0;
	timer0ClockReload  = 0;
	timer1On = false;
	timer1Ticks = 0;
	timer1Reload = 0;
	timer1ClockReload  = 0;
	timer2On = false;
	timer2Ticks = 0;
	timer2Reload = 0;
	timer2ClockReload  = 0;
	timer3On = false;
	timer3Ticks = 0;
	timer3Reload = 0;
	timer3ClockReload  = 0;
	dma0Source = 0;
	dma0Dest = 0;
	dma1Source = 0;
	dma1Dest = 0;
	dma2Source = 0;
	dma2Dest = 0;
	dma3Source = 0;
	dma3Dest = 0;
	cpuSaveGameFunc = flashSaveDecide;
	fxOn = false;
	windowOn = false;
	saveType = 0;
	graphics.layerEnable = io_registers[REG_DISPCNT];

#if !THREADED_RENDERER
	memset(line[Layer_BG0], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG1], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG2], -1, 240 * sizeof(uint32_t));
	memset(line[Layer_BG3], -1, 240 * sizeof(uint32_t));
#endif

	for(i = 0; i < 256; i++) {
		map[i].address = 0;
		map[i].mask = 0;
	}

	map[0].address = bios;
	map[0].mask = 0x3FFF;
	map[2].address = workRAM;
	map[2].mask = 0x3FFFF;
	map[3].address = internalRAM;
	map[3].mask = 0x7FFF;
	map[4].address = ioMem;
	map[4].mask = 0x3FF;
	map[5].address = paletteRAM;
	map[5].mask = 0x3FF;
	map[6].address = vram;
	map[6].mask = 0x1FFFF;
	map[7].address = oam;
	map[7].mask = 0x3FF;
	map[8].address = rom;
	map[8].mask = 0x1FFFFFF;
	map[9].address = rom;
	map[9].mask = 0x1FFFFFF;
	map[10].address = rom;
	map[10].mask = 0x1FFFFFF;
	map[12].address = rom;
	map[12].mask = 0x1FFFFFF;
	map[14].address = flashSaveMemory;
	map[14].mask = 0xFFFF;

	eepromReset();
	flashReset();

	soundReset();

	CPUUpdateWindow0();
	CPUUpdateWindow1();

	/* make sure registers are correctly initialized if not using BIOS */
	if(!useBios)
		BIOS_RegisterRamReset(0xff);

	switch(cpuSaveType) {
		case 0: /* automatic */
			cpuSramEnabled = true;
			cpuFlashEnabled = true;
			cpuEEPROMEnabled = true;
			saveType = gbaSaveType = 0;
			break;
		case 1: /* EEPROM */
			cpuSramEnabled = false;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = true;
			saveType = gbaSaveType = 3;
			/* EEPROM usage is automatically detected */
			break;
		case 2: /* SRAM */
			cpuSramEnabled = true;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = false;
			cpuSaveGameFunc = sramDelayedWrite; /* to insure we detect the write */
			saveType = gbaSaveType = 1;
			break;
		case 3: /* FLASH */
			cpuSramEnabled = false;
			cpuFlashEnabled = true;
			cpuEEPROMEnabled = false;
			cpuSaveGameFunc = flashDelayedWrite; /* to insure we detect the write */
			saveType = gbaSaveType = 2;
			break;
		case 4: /* EEPROM+Sensor */
			cpuSramEnabled = false;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = true;
			/* EEPROM usage is automatically detected */
			saveType = gbaSaveType = 3;
			break;
		case 5: /* NONE */
			cpuSramEnabled = false;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = false;
			/* no save at all */
			saveType = gbaSaveType = 5;
			break;
	}

	ARM_PREFETCH;


	cpuDmaLast = 0;
	cpuDmaRunning = false;
}

static void CPUInterrupt(void)
{
	uint32_t PC = bus.reg[15].I;
	bool savedState = armState;

	if(armMode != 0x12 )
		CPUSwitchMode(0x12, true, false);

	bus.reg[14].I = PC;
	if(!savedState)
		bus.reg[14].I += 2;
	bus.reg[15].I = 0x18;
	armState = true;
	armIrqEnable = false;

	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;
	ARM_PREFETCH;

	/*  if(!holdState) */
	biosProtected[0] = 0x02;
	biosProtected[1] = 0xc0;
	biosProtected[2] = 0x5e;
	biosProtected[3] = 0xe5;
}

void UpdateJoypad(void)
{
   /* update joystick information */
   uint16_t joypad = 0x03FF ^ (joy & 0x3FF);
   io_registers[REG_P1] = joypad;
#if USE_MOTION_SENSOR
	if(hardware.sensor) {
		systemUpdateMotionSensor();
		hardware.tilt_x = (systemGetAccelX() >> 21) + 0x3A0;
		hardware.tilt_y = (systemGetAccelY() >> 21) + 0x3A0;
	}
#endif
   UPDATE_REG(0x130, joypad);
   io_registers[REG_P1CNT] = READ16LE(((uint16_t *)&ioMem[0x132]));

   /* this seems wrong, but there are cases where the game */
   /* can enter the stop state without requesting an IRQ from */
   /* the joypad. */
   if((io_registers[REG_P1CNT] & 0x4000) || stopState) {
      uint16_t p1 = (0x3FF ^ io_registers[REG_P1CNT]) & 0x3FF;
      if(io_registers[REG_P1CNT] & 0x8000) {
         if(p1 == (io_registers[REG_P1CNT] & 0x3FF)) {
            { uint16_t _v = (io_registers[REG_IF]) | (0x1000); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
         }
      } else {
         if(p1 & io_registers[REG_P1CNT]) {
            { uint16_t _v = (io_registers[REG_IF]) | (0x1000); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
         }
      }
   }
}

void CPULoop (void)
{
	bool framedone;
	int timerOverflow = 0;
	int ticks = 300000;

	bus.busPrefetchCount = 0;
	/* variable used by the CPU core */
	cpuTotalTicks = 0;

	cpuNextEvent = CPUUpdateTicks();
	if(cpuNextEvent > ticks)
	cpuNextEvent = ticks;

	framedone = false;

	do
	{
		if(!holdState)
		{
			if(armState)
			{
				if (!armExecute())
					return;
			}
			else
			{
				if (!thumbExecute())
					return;
			}
			clockTicks = 0;
		}
		else
			clockTicks = CPUUpdateTicks();

		cpuTotalTicks += clockTicks;

		if(cpuTotalTicks >= cpuNextEvent) {
			int remainingTicks = cpuTotalTicks - cpuNextEvent;


			clockTicks = cpuNextEvent;
			cpuTotalTicks = 0;

updateLoop:

			if (IRQTicks) {
				IRQTicks -= clockTicks;
				if (IRQTicks<0)
					IRQTicks = 0;
			}

			graphics.lcdTicks -= clockTicks;

			if(graphics.lcdTicks <= 0)
			{
				if(io_registers[REG_DISPSTAT] & 1)
				{ /* V-BLANK */
					/* if in V-Blank mode, keep computing... */
					if(io_registers[REG_DISPSTAT] & 2)
					{
						graphics.lcdTicks += 1008;
						{ uint16_t _v = (R_VCOUNT) + (1); R_VCOUNT = _v; UPDATE_REG(0x06, _v); }
						{ uint16_t _v = (io_registers[REG_DISPSTAT]) & (0xFFFD); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
						CPUCompareVCOUNT();
					}
					else
					{
						graphics.lcdTicks += 224;
						{ uint16_t _v = (io_registers[REG_DISPSTAT]) | (2); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
						if(io_registers[REG_DISPSTAT] & 16)
						{
							{ uint16_t _v = (io_registers[REG_IF]) | (2); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
						}
					}

					if(R_VCOUNT >= 228)
					{
						/*Reaching last line */
						{ uint16_t _v = (io_registers[REG_DISPSTAT]) & (0xFFFC); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
						{ uint16_t _v = 0; R_VCOUNT = _v; UPDATE_REG(0x06, _v); }
						CPUCompareVCOUNT();
					}
				}
				else if(io_registers[REG_DISPSTAT] & 2)
				{
					/* if in H-Blank, leave it and move to drawing mode */
					{ uint16_t _v = (R_VCOUNT) + (1); R_VCOUNT = _v; UPDATE_REG(0x06, _v); }

					graphics.lcdTicks += 1008;
					io_registers[REG_DISPSTAT] &= 0xFFFD;

					if(R_VCOUNT == 160)
		        	{
		            	uint32_t ext = (joy >> 10);
		            	/* If no (m) code is enabled, apply the cheats at each LCDline */
#if USE_CHEATS
		            	if(mastercode == 0)
		                	remainingTicks += cheatsCheckKeys(io_registers[REG_P1] ^ 0x3FF, ext);
#endif
		            	io_registers[REG_DISPSTAT] |= 1;
		            	{ uint16_t _v = (io_registers[REG_DISPSTAT]) & (0xFFFD); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
		            	if(io_registers[REG_DISPSTAT] & 0x0008)
		            	{
		                	{ uint16_t _v = (io_registers[REG_IF]) | (1); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
		            	}
		            	CPUCheckDMA(1, 0x0f);

#if !THREADED_RENDERER
		            	systemDrawScreen();
#endif

#if USE_FRAME_SKIP
						++fs_count;

						if(fs_type_b == 0) {
							fs_draw = true;
						} else {
							if(fs_type_a > 0) {
								fs_draw = (fs_count % (fs_type_b + 1));
							} else {
								fs_draw = ((fs_count % (fs_type_b + 1)) == 0);
							}
						}
#endif
		            	framedone = true;
		        	}

					UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
					CPUCompareVCOUNT();
				}
				else
				{
#if USE_FRAME_SKIP
					if(fs_draw) {
#endif
#if THREADED_RENDERER
						postRender();
#ifdef PER_FRAME_BATCHED
						/* Batched mode: no per-line worker dispatch.  All 160
						 * scanlines have been snapshotted into their own
						 * context; render them all here when the frame is
						 * complete. */
						if(threaded_renderer_ready) {
							int _bi;
							for(_bi = 0; _bi < THREADED_RENDERER_COUNT; ++_bi)
								renderer_process_line(_bi);
							batched_publish_idx = 0;
							threaded_renderer_ready = 0;
							systemDrawScreen();
						}
#else
						if(!g_threaded_renderer_enabled) {
							/* Synchronous fallback: postRender() already advanced
							 * threaded_renderer_idx and set renderer_state=1 on the
							 * just-published context.  Drive the worker body inline
							 * for that context. */
							int idx = (threaded_renderer_idx + THREADED_RENDERER_COUNT - 1) % THREADED_RENDERER_COUNT;
							renderer_process_line(idx);
						}
						if(threaded_renderer_ready) {
							/* End-of-visible-frame: present from the main (retro_run)
							 * thread.  libretro requires it, and on Windows the
							 * frontend's title-update path (SetWindowTextW ->
							 * SendMessageW) deadlocks if called from a worker
							 * while the main thread is spinning in postRender.
							 * In threaded mode the worker may still be processing
							 * the line-159 publish, so spin-wait for renderer_state
							 * to drain first; in sync mode the inline
							 * renderer_process_line above already cleared it. */
							int idx = (threaded_renderer_idx + THREADED_RENDERER_COUNT - 1) % THREADED_RENDERER_COUNT;
							while(threaded_renderer_contexts[idx].renderer_state)
								SPIN_HINT();
							threaded_renderer_ready = 0;
							systemDrawScreen();
						}
#endif
#else
						bool draw_objwin = (graphics.layerEnable & 0x9000) == 0x9000;
						bool draw_sprites = R_DISPCNT_Screen_Display_OBJ;

#ifdef MSB_FIRST
						/* §5b/C: sync host-endian palette + OAM shadows once
						 * per scanline.  No call on LE because the shadows
						 * don't exist there (renderer reads paletteRAM/oam
						 * directly via the LE branch of PAL_U16/OAM_U16). */
						palette_native_sync(palette_native);
						oam_native_sync(oam_native);
#endif

						memset(RENDERER_LINE[Layer_OBJ], -1, 240 * sizeof(uint32_t));	/* erase all sprites */
						if(draw_sprites) gfxDrawSprites(0);

						if(renderfunc_type == 2) {
							memset(RENDERER_LINE[Layer_WIN_OBJ], -1, 240 * sizeof(uint32_t));	/* erase all OBJ Win */
							if(draw_objwin) gfxDrawOBJWin(0);
						}

						GetRenderFunc(0, renderfunc_mode, renderfunc_type)(0);
#endif
#if USE_FRAME_SKIP
					}
#endif

					/* entering H-Blank */
					{ uint16_t _v = (io_registers[REG_DISPSTAT]) | (2); io_registers[REG_DISPSTAT] = _v; UPDATE_REG(0x04, _v); }
					graphics.lcdTicks += 224;
					CPUCheckDMA(2, 0x0f);
					if(io_registers[REG_DISPSTAT] & 16)
					{
						{ uint16_t _v = (io_registers[REG_IF]) | (2); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
					}
				}
			}

			/* we shouldn't be doing sound in stop state, but we lose synchronization */
			/* if sound is disabled, so in stop state, soundTick will just produce */
			/* mute sound */
			soundTicks -= clockTicks;
			if(!soundTicks)
			{
				process_sound_tick_fn();
				soundTicks += SOUND_CLOCK_TICKS;
			}

			if(!stopState) {
				if(timer0On) {
					timer0Ticks -= clockTicks;
					if(timer0Ticks <= 0) {
						timer0Ticks += (0x10000 - timer0Reload) << timer0ClockReload;
						timerOverflow |= 1;
						soundTimerOverflow(0);
						if(io_registers[REG_TM0CNT] & 0x40) {
							{ uint16_t _v = (io_registers[REG_IF]) | (0x08); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
						}
					}
					{ uint16_t _v = 0xFFFF - (timer0Ticks >> timer0ClockReload); io_registers[REG_TM0D] = _v; UPDATE_REG(0x100, _v); }
				}

				if(timer1On) {
					if(io_registers[REG_TM1CNT] & 4) {
						if(timerOverflow & 1) {
							/* §B+: hold TM1D in a local across the inc /
							 * overflow-check / reload so neither the check
							 * nor the final UPDATE_REG hits LHS on the
							 * just-written io_registers slot.  soundTimerOverflow
							 * touches only pcm[] state, never io_registers. */
							uint16_t tm1d = io_registers[REG_TM1D] + 1;
							if(tm1d == 0) {
								tm1d = timer1Reload;
								timerOverflow |= 2;
								soundTimerOverflow(1);
								if(io_registers[REG_TM1CNT] & 0x40) {
									{ uint16_t _v = (io_registers[REG_IF]) | (0x10); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
								}
							}
							io_registers[REG_TM1D] = tm1d;
							UPDATE_REG(0x104, tm1d);
						}
					} else {
						timer1Ticks -= clockTicks;
						if(timer1Ticks <= 0) {
							timer1Ticks += (0x10000 - timer1Reload) << timer1ClockReload;
							timerOverflow |= 2;
							soundTimerOverflow(1);
							if(io_registers[REG_TM1CNT] & 0x40) {
								{ uint16_t _v = (io_registers[REG_IF]) | (0x10); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
							}
						}
						{ uint16_t _v = 0xFFFF - (timer1Ticks >> timer1ClockReload); io_registers[REG_TM1D] = _v; UPDATE_REG(0x104, _v); }
					}
				}

				if(timer2On) {
					if(io_registers[REG_TM2CNT] & 4) {
						if(timerOverflow & 2) {
							/* §B+: see timer1-cascade comment above. */
							uint16_t tm2d = io_registers[REG_TM2D] + 1;
							if(tm2d == 0) {
								tm2d = timer2Reload;
								timerOverflow |= 4;
								if(io_registers[REG_TM2CNT] & 0x40) {
									{ uint16_t _v = (io_registers[REG_IF]) | (0x20); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
								}
							}
							io_registers[REG_TM2D] = tm2d;
							UPDATE_REG(0x108, tm2d);
						}
					} else {
						timer2Ticks -= clockTicks;
						if(timer2Ticks <= 0) {
							timer2Ticks += (0x10000 - timer2Reload) << timer2ClockReload;
							timerOverflow |= 4;
							if(io_registers[REG_TM2CNT] & 0x40) {
								{ uint16_t _v = (io_registers[REG_IF]) | (0x20); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
							}
						}
						{ uint16_t _v = 0xFFFF - (timer2Ticks >> timer2ClockReload); io_registers[REG_TM2D] = _v; UPDATE_REG(0x108, _v); }
					}
				}

				if(timer3On) {
					if(io_registers[REG_TM3CNT] & 4) {
						if(timerOverflow & 4) {
							/* §B+: see timer1-cascade comment above. */
							uint16_t tm3d = io_registers[REG_TM3D] + 1;
							if(tm3d == 0) {
								tm3d = timer3Reload;
								if(io_registers[REG_TM3CNT] & 0x40) {
									{ uint16_t _v = (io_registers[REG_IF]) | (0x40); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
								}
							}
							io_registers[REG_TM3D] = tm3d;
							UPDATE_REG(0x10C, tm3d);
						}
					} else {
						timer3Ticks -= clockTicks;
						if(timer3Ticks <= 0) {
							timer3Ticks += (0x10000 - timer3Reload) << timer3ClockReload;
							if(io_registers[REG_TM3CNT] & 0x40) {
								{ uint16_t _v = (io_registers[REG_IF]) | (0x40); io_registers[REG_IF] = _v; UPDATE_REG(0x202, _v); }
							}
						}
						{ uint16_t _v = 0xFFFF - (timer3Ticks >> timer3ClockReload); io_registers[REG_TM3D] = _v; UPDATE_REG(0x10C, _v); }
					}
				}
			}

			timerOverflow = 0;
			ticks -= clockTicks;
			cpuNextEvent = CPUUpdateTicks();

			if(cpuDmaTicksToUpdate > 0)
			{
				if(cpuDmaTicksToUpdate > cpuNextEvent)
					clockTicks = cpuNextEvent;
				else
					clockTicks = cpuDmaTicksToUpdate;
				cpuDmaTicksToUpdate -= clockTicks;
				if(cpuDmaTicksToUpdate < 0)
					cpuDmaTicksToUpdate = 0;
				goto updateLoop;
			}

			if(io_registers[REG_IF] && (io_registers[REG_IME] & 1) && armIrqEnable)
			{
				int res = io_registers[REG_IF] & io_registers[REG_IE];
				if(stopState)
					res &= 0x3080;
				if(res)
				{
					if (intState)
					{
						if (!IRQTicks)
						{
							CPUInterrupt();
							intState = false;
							holdState = false;
							stopState = false;
						}
					}
					else
					{
						if (!holdState)
						{
							intState = true;
							IRQTicks=7;
							if (cpuNextEvent> IRQTicks)
								cpuNextEvent = IRQTicks;
						}
						else
						{
							CPUInterrupt();
							holdState = false;
							stopState = false;
						}
					}

				}
			}

			if(remainingTicks > 0) {
				if(remainingTicks > cpuNextEvent)
					clockTicks = cpuNextEvent;
				else
					clockTicks = remainingTicks;
				remainingTicks -= clockTicks;
				if(remainingTicks < 0)
					remainingTicks = 0;
				goto updateLoop;
			}

			if (timerOnOffDelay)
			{
				/* Apply Timer */
				if (timerOnOffDelay & 1)
				{
					timer0ClockReload = TIMER_TICKS[timer0Value & 3];
					if(!timer0On && (timer0Value & 0x80)) {
						/* §B+: avoid two LHS reads of REG_TM0D (one for the
						 * timer0Ticks calc, one for UPDATE_REG) by holding the
						 * reload value in a local across the store. */
						uint16_t tm0d = timer0Reload;
						io_registers[REG_TM0D] = tm0d;
						timer0Ticks = (0x10000 - tm0d) << timer0ClockReload;
						UPDATE_REG(0x100, tm0d);
					}
					timer0On = timer0Value & 0x80 ? true : false;
					{ uint16_t _v = timer0Value & 0xC7; io_registers[REG_TM0CNT] = _v; UPDATE_REG(0x102, _v); }
				}
				if (timerOnOffDelay & 2)
				{
					timer1ClockReload = TIMER_TICKS[timer1Value & 3];
					if(!timer1On && (timer1Value & 0x80)) {
						/* §B+: see timer0 reload comment above. */
						uint16_t tm1d = timer1Reload;
						io_registers[REG_TM1D] = tm1d;
						timer1Ticks = (0x10000 - tm1d) << timer1ClockReload;
						UPDATE_REG(0x104, tm1d);
					}
					timer1On = timer1Value & 0x80 ? true : false;
					{ uint16_t _v = timer1Value & 0xC7; io_registers[REG_TM1CNT] = _v; UPDATE_REG(0x106, _v); }
				}
				if (timerOnOffDelay & 4)
				{
					timer2ClockReload = TIMER_TICKS[timer2Value & 3];
					if(!timer2On && (timer2Value & 0x80)) {
						/* §B+: see timer0 reload comment above. */
						uint16_t tm2d = timer2Reload;
						io_registers[REG_TM2D] = tm2d;
						timer2Ticks = (0x10000 - tm2d) << timer2ClockReload;
						UPDATE_REG(0x108, tm2d);
					}
					timer2On = timer2Value & 0x80 ? true : false;
					{ uint16_t _v = timer2Value & 0xC7; io_registers[REG_TM2CNT] = _v; UPDATE_REG(0x10A, _v); }
				}
				if (timerOnOffDelay & 8)
				{
					timer3ClockReload = TIMER_TICKS[timer3Value & 3];
					if(!timer3On && (timer3Value & 0x80)) {
						/* §B+: see timer0 reload comment above. */
						uint16_t tm3d = timer3Reload;
						io_registers[REG_TM3D] = tm3d;
						timer3Ticks = (0x10000 - tm3d) << timer3ClockReload;
						UPDATE_REG(0x10C, tm3d);
					}
					timer3On = timer3Value & 0x80 ? true : false;
					{ uint16_t _v = timer3Value & 0xC7; io_registers[REG_TM3CNT] = _v; UPDATE_REG(0x10E, _v); }
				}
				cpuNextEvent = CPUUpdateTicks();
				timerOnOffDelay = 0;
				/* End of Apply Timer */
			}

			if(cpuNextEvent > ticks)
				cpuNextEvent = ticks;

			if(ticks <= 0 || framedone)
				break;
		}
	} while(1);
}

/* GBA CHEATS */

/**
 * Gameshark code types: (based on AR v1.0)
 *
 * NNNNNNNN 001DC0DE - ID code for the game (game 4 character name) from ROM
 * DEADFACE XXXXXXXX - changes decryption seeds // Not supported by VBA.
 * 0AAAAAAA 000000YY - 8-bit constant write
 * 1AAAAAAA 0000YYYY - 16-bit constant write
 * 2AAAAAAA YYYYYYYY - 32-bit constant write
 * 30XXAAAA YYYYYYYY - 32bit Group Write, 8/16/32bit Sub/Add (depending on the XX value).
 * 6AAAAAAA Z000YYYY - 16-bit ROM Patch (address >> 1). Z selects the Rom Patching register.
 *                   - AR v1/2 hardware only supports Z=0.
 *                   - AR v3 hardware should support Z=0,1,2 or 3.
 * 8A1AAAAA 000000YY - 8-bit button write
 * 8A2AAAAA 0000YYYY - 16-bit button write
 * 8A4AAAAA YYYYYYYY - 32-bit button write // BUGGY ! Only writes 00000000 on the AR v1.0.
 * 80F00000 0000YYYY - button slow motion
 * DAAAAAAA 00Z0YYYY - Z = 0 : if 16-bit value at address != YYYY skip next line
 *                   - Z = 1 : if 16-bit value at address == YYYY skip next line
 *                   - Z = 2 : if 16-bit value at address > YYYY (Unsigned) skip next line
 *                   - Z = 3 : if 16-bit value at address < YYYY (Unsigned) skip next line
 * E0CCYYYY ZAAAAAAA - Z = 0 : if 16-bit value at address != YYYY skip CC lines
 *                   - Z = 1 : if 16-bit value at address == YYYY skip CC lines
 *                   - Z = 2 : if 16-bit value at address > YYYY (Unsigned) skip CC lines
 *                   - Z = 3 : if 16-bit value at address < YYYY (Unsigned) skip CC lines
 * FAAAAAAA 0000YYYY - Master code function
 *
 *
 *
 * CodeBreaker codes types: (based on the CBA clone "Cheatcode S" v1.1)
 *
 * 0000AAAA 000Y - Game CRC (Y are flags: 8 - CRC, 2 - DI)
 * 1AAAAAAA YYYY - Master Code function (store address at ((YYYY << 0x16)
 *                 + 0x08000100))
 * 2AAAAAAA YYYY - 16-bit or
 * 3AAAAAAA YYYY - 8-bit constant write
 * 4AAAAAAA YYYY - Slide code
 * XXXXCCCC IIII   (C is count and I is address increment, X is value incr.)
 * 5AAAAAAA CCCC - Super code (Write bytes to address, 2*CCCC is count)
 * BBBBBBBB BBBB
 * 6AAAAAAA YYYY - 16-bit and
 * 7AAAAAAA YYYY - if address contains 16-bit value enable next code
 * 8AAAAAAA YYYY - 16-bit constant write
 * 9AAAAAAA YYYY - change decryption (when first code only?)
 * AAAAAAAA YYYY - if address does not contain 16-bit value enable next code
 * BAAAAAAA YYYY - if 16-bit value at address  <= YYYY skip next code
 * CAAAAAAA YYYY - if 16-bit value at address  >= YYYY skip next code
 * D00000X0 YYYY - if button keys ... enable next code (else skip next code)
 * EAAAAAAA YYYY - increase 16/32bit value stored in address
 * FAAAAAAA YYYY - if 16-bit value at address AND YYYY = 0 then skip next code
 **/

#define UNKNOWN_CODE                  -1
#define INT_8_BIT_WRITE               0
#define INT_16_BIT_WRITE              1
#define INT_32_BIT_WRITE              2
#define GSA_16_BIT_ROM_PATCH          3
#define GSA_8_BIT_GS_WRITE            4
#define GSA_16_BIT_GS_WRITE           5
#define GSA_32_BIT_GS_WRITE           6
#define CBA_IF_KEYS_PRESSED           7
#define CBA_IF_TRUE                   8
#define CBA_SLIDE_CODE                9
#define CBA_IF_FALSE                  10
#define CBA_AND                       11
#define GSA_8_BIT_GS_WRITE2           12
#define GSA_16_BIT_GS_WRITE2          13
#define GSA_32_BIT_GS_WRITE2          14
#define GSA_16_BIT_ROM_PATCH2C        15
#define GSA_8_BIT_SLIDE               16
#define GSA_16_BIT_SLIDE              17
#define GSA_32_BIT_SLIDE              18
#define GSA_8_BIT_IF_TRUE             19
#define GSA_32_BIT_IF_TRUE            20
#define GSA_8_BIT_IF_FALSE            21
#define GSA_32_BIT_IF_FALSE           22
#define GSA_8_BIT_FILL                23
#define GSA_16_BIT_FILL               24
#define GSA_8_BIT_IF_TRUE2            25
#define GSA_16_BIT_IF_TRUE2           26
#define GSA_32_BIT_IF_TRUE2           27
#define GSA_8_BIT_IF_FALSE2           28
#define GSA_16_BIT_IF_FALSE2          29
#define GSA_32_BIT_IF_FALSE2          30
#define GSA_SLOWDOWN                  31
#define CBA_ADD                       32
#define CBA_OR                        33
#define CBA_LT                        34
#define CBA_GT                        35
#define CBA_SUPER                     36
#define GSA_8_BIT_POINTER             37
#define GSA_16_BIT_POINTER            38
#define GSA_32_BIT_POINTER            39
#define GSA_8_BIT_ADD                 40
#define GSA_16_BIT_ADD                41
#define GSA_32_BIT_ADD                42
#define GSA_8_BIT_IF_LOWER_U          43
#define GSA_16_BIT_IF_LOWER_U         44
#define GSA_32_BIT_IF_LOWER_U         45
#define GSA_8_BIT_IF_HIGHER_U         46
#define GSA_16_BIT_IF_HIGHER_U        47
#define GSA_32_BIT_IF_HIGHER_U        48
#define GSA_8_BIT_IF_AND              49
#define GSA_16_BIT_IF_AND             50
#define GSA_32_BIT_IF_AND             51
#define GSA_8_BIT_IF_LOWER_U2         52
#define GSA_16_BIT_IF_LOWER_U2        53
#define GSA_32_BIT_IF_LOWER_U2        54
#define GSA_8_BIT_IF_HIGHER_U2        55
#define GSA_16_BIT_IF_HIGHER_U2       56
#define GSA_32_BIT_IF_HIGHER_U2       57
#define GSA_8_BIT_IF_AND2             58
#define GSA_16_BIT_IF_AND2            59
#define GSA_32_BIT_IF_AND2            60
#define GSA_ALWAYS                    61
#define GSA_ALWAYS2                   62
#define GSA_8_BIT_IF_LOWER_S          63
#define GSA_16_BIT_IF_LOWER_S         64
#define GSA_32_BIT_IF_LOWER_S         65
#define GSA_8_BIT_IF_HIGHER_S         66
#define GSA_16_BIT_IF_HIGHER_S        67
#define GSA_32_BIT_IF_HIGHER_S        68
#define GSA_8_BIT_IF_LOWER_S2         69
#define GSA_16_BIT_IF_LOWER_S2        70
#define GSA_32_BIT_IF_LOWER_S2        71
#define GSA_8_BIT_IF_HIGHER_S2        72
#define GSA_16_BIT_IF_HIGHER_S2       73
#define GSA_32_BIT_IF_HIGHER_S2       74
#define GSA_16_BIT_WRITE_IOREGS       75
#define GSA_32_BIT_WRITE_IOREGS       76
#define GSA_CODES_ON                  77
#define GSA_8_BIT_IF_TRUE3            78
#define GSA_16_BIT_IF_TRUE3           79
#define GSA_32_BIT_IF_TRUE3           80
#define GSA_8_BIT_IF_FALSE3           81
#define GSA_16_BIT_IF_FALSE3          82
#define GSA_32_BIT_IF_FALSE3          83
#define GSA_8_BIT_IF_LOWER_S3         84
#define GSA_16_BIT_IF_LOWER_S3        85
#define GSA_32_BIT_IF_LOWER_S3        86
#define GSA_8_BIT_IF_HIGHER_S3        87
#define GSA_16_BIT_IF_HIGHER_S3       88
#define GSA_32_BIT_IF_HIGHER_S3       89
#define GSA_8_BIT_IF_LOWER_U3         90
#define GSA_16_BIT_IF_LOWER_U3        91
#define GSA_32_BIT_IF_LOWER_U3        92
#define GSA_8_BIT_IF_HIGHER_U3        93
#define GSA_16_BIT_IF_HIGHER_U3       94
#define GSA_32_BIT_IF_HIGHER_U3       95
#define GSA_8_BIT_IF_AND3             96
#define GSA_16_BIT_IF_AND3            97
#define GSA_32_BIT_IF_AND3            98
#define GSA_ALWAYS3                   99
#define GSA_16_BIT_ROM_PATCH2D        100
#define GSA_16_BIT_ROM_PATCH2E        101
#define GSA_16_BIT_ROM_PATCH2F        102
#define GSA_GROUP_WRITE               103
#define GSA_32_BIT_ADD2               104
#define GSA_32_BIT_SUB2               105
#define GSA_16_BIT_IF_LOWER_OR_EQ_U   106
#define GSA_16_BIT_IF_HIGHER_OR_EQ_U  107
#define GSA_16_BIT_MIF_TRUE           108
#define GSA_16_BIT_MIF_FALSE          109
#define GSA_16_BIT_MIF_LOWER_OR_EQ_U  110
#define GSA_16_BIT_MIF_HIGHER_OR_EQ_U 111
#define MASTER_CODE                   112
#define CHEATS_16_BIT_WRITE           114
#define CHEATS_32_BIT_WRITE           115

/* Cheat list and count: used only within gba.c. Were non-static
 * (accidental external linkage); the neighbouring rompatch2* arrays
 * below were already static. */
static CheatsData cheatsList[100];
static int cheatsNumber = 0;
static uint32_t rompatch2addr [4];
static uint16_t rompatch2val [4];
static uint16_t rompatch2oldval [4];

static uint8_t cheatsCBASeedBuffer[0x30];
static uint32_t cheatsCBASeed[4];
static uint32_t cheatsCBATemporaryValue = 0;
static uint16_t cheatsCBATable[256];
/* (cheatsCBATableGenerated is defined earlier near CPUInit so the init code
 * can reset it on game load.) */
/* Was `uint16_t super = 0;` with external linkage - one-letter identifier
 * collides with reserved words / macros in some platform SDKs. */
static uint16_t cba_super_count = 0;

#if (0)
extern GameStorage xStorage;
#endif

static uint8_t cheatsCBACurrentSeed[12] = {
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00
};

static uint32_t seeds_v1[4];
static uint32_t seeds_v3[4];

uint32_t seed_gen(uint8_t upper, uint8_t seed, uint8_t *deadtable1, uint8_t *deadtable2);

/*seed tables for AR v1 */
static uint8_t v1_deadtable1[256] = {
	0x31, 0x1C, 0x23, 0xE5, 0x89, 0x8E, 0xA1, 0x37, 0x74, 0x6D, 0x67, 0xFC, 0x1F, 0xC0, 0xB1, 0x94,
	0x3B, 0x05, 0x56, 0x86, 0x00, 0x24, 0xF0, 0x17, 0x72, 0xA2, 0x3D, 0x1B, 0xE3, 0x17, 0xC5, 0x0B,
	0xB9, 0xE2, 0xBD, 0x58, 0x71, 0x1B, 0x2C, 0xFF, 0xE4, 0xC9, 0x4C, 0x5E, 0xC9, 0x55, 0x33, 0x45,
	0x7C, 0x3F, 0xB2, 0x51, 0xFE, 0x10, 0x7E, 0x75, 0x3C, 0x90, 0x8D, 0xDA, 0x94, 0x38, 0xC3, 0xE9,
	0x95, 0xEA, 0xCE, 0xA6, 0x06, 0xE0, 0x4F, 0x3F, 0x2A, 0xE3, 0x3A, 0xE4, 0x43, 0xBD, 0x7F, 0xDA,
	0x55, 0xF0, 0xEA, 0xCB, 0x2C, 0xA8, 0x47, 0x61, 0xA0, 0xEF, 0xCB, 0x13, 0x18, 0x20, 0xAF, 0x3E,
	0x4D, 0x9E, 0x1E, 0x77, 0x51, 0xC5, 0x51, 0x20, 0xCF, 0x21, 0xF9, 0x39, 0x94, 0xDE, 0xDD, 0x79,
	0x4E, 0x80, 0xC4, 0x9D, 0x94, 0xD5, 0x95, 0x01, 0x27, 0x27, 0xBD, 0x6D, 0x78, 0xB5, 0xD1, 0x31,
	0x6A, 0x65, 0x74, 0x74, 0x58, 0xB3, 0x7C, 0xC9, 0x5A, 0xED, 0x50, 0x03, 0xC4, 0xA2, 0x94, 0x4B,
	0xF0, 0x58, 0x09, 0x6F, 0x3E, 0x7D, 0xAE, 0x7D, 0x58, 0xA0, 0x2C, 0x91, 0xBB, 0xE1, 0x70, 0xEB,
	0x73, 0xA6, 0x9A, 0x44, 0x25, 0x90, 0x16, 0x62, 0x53, 0xAE, 0x08, 0xEB, 0xDC, 0xF0, 0xEE, 0x77,
	0xC2, 0xDE, 0x81, 0xE8, 0x30, 0x89, 0xDB, 0xFE, 0xBC, 0xC2, 0xDF, 0x26, 0xE9, 0x8B, 0xD6, 0x93,
	0xF0, 0xCB, 0x56, 0x90, 0xC0, 0x46, 0x68, 0x15, 0x43, 0xCB, 0xE9, 0x98, 0xE3, 0xAF, 0x31, 0x25,
	0x4D, 0x7B, 0xF3, 0xB1, 0x74, 0xE2, 0x64, 0xAC, 0xD9, 0xF6, 0xA0, 0xD5, 0x0B, 0x9B, 0x49, 0x52,
	0x69, 0x3B, 0x71, 0x00, 0x2F, 0xBB, 0xBA, 0x08, 0xB1, 0xAE, 0xBB, 0xB3, 0xE1, 0xC9, 0xA6, 0x7F,
	0x17, 0x97, 0x28, 0x72, 0x12, 0x6E, 0x91, 0xAE, 0x3A, 0xA2, 0x35, 0x46, 0x27, 0xF8, 0x12, 0x50
};
static uint8_t v1_deadtable2[256] = {
	0xD8, 0x65, 0x04, 0xC2, 0x65, 0xD5, 0xB0, 0x0C, 0xDF, 0x9D, 0xF0, 0xC3, 0x9A, 0x17, 0xC9, 0xA6,
	0xE1, 0xAC, 0x0D, 0x14, 0x2F, 0x3C, 0x2C, 0x87, 0xA2, 0xBF, 0x4D, 0x5F, 0xAC, 0x2D, 0x9D, 0xE1,
	0x0C, 0x9C, 0xE7, 0x7F, 0xFC, 0xA8, 0x66, 0x59, 0xAC, 0x18, 0xD7, 0x05, 0xF0, 0xBF, 0xD1, 0x8B,
	0x35, 0x9F, 0x59, 0xB4, 0xBA, 0x55, 0xB2, 0x85, 0xFD, 0xB1, 0x72, 0x06, 0x73, 0xA4, 0xDB, 0x48,
	0x7B, 0x5F, 0x67, 0xA5, 0x95, 0xB9, 0xA5, 0x4A, 0xCF, 0xD1, 0x44, 0xF3, 0x81, 0xF5, 0x6D, 0xF6,
	0x3A, 0xC3, 0x57, 0x83, 0xFA, 0x8E, 0x15, 0x2A, 0xA2, 0x04, 0xB2, 0x9D, 0xA8, 0x0D, 0x7F, 0xB8,
	0x0F, 0xF6, 0xAC, 0xBE, 0x97, 0xCE, 0x16, 0xE6, 0x31, 0x10, 0x60, 0x16, 0xB5, 0x83, 0x45, 0xEE,
	0xD7, 0x5F, 0x2C, 0x08, 0x58, 0xB1, 0xFD, 0x7E, 0x79, 0x00, 0x34, 0xAD, 0xB5, 0x31, 0x34, 0x39,
	0xAF, 0xA8, 0xDD, 0x52, 0x6A, 0xB0, 0x60, 0x35, 0xB8, 0x1D, 0x52, 0xF5, 0xF5, 0x30, 0x00, 0x7B,
	0xF4, 0xBA, 0x03, 0xCB, 0x3A, 0x84, 0x14, 0x8A, 0x6A, 0xEF, 0x21, 0xBD, 0x01, 0xD8, 0xA0, 0xD4,
	0x43, 0xBE, 0x23, 0xE7, 0x76, 0x27, 0x2C, 0x3F, 0x4D, 0x3F, 0x43, 0x18, 0xA7, 0xC3, 0x47, 0xA5,
	0x7A, 0x1D, 0x02, 0x55, 0x09, 0xD1, 0xFF, 0x55, 0x5E, 0x17, 0xA0, 0x56, 0xF4, 0xC9, 0x6B, 0x90,
	0xB4, 0x80, 0xA5, 0x07, 0x22, 0xFB, 0x22, 0x0D, 0xD9, 0xC0, 0x5B, 0x08, 0x35, 0x05, 0xC1, 0x75,
	0x4F, 0xD0, 0x51, 0x2D, 0x2E, 0x5E, 0x69, 0xE7, 0x3B, 0xC2, 0xDA, 0xFF, 0xF6, 0xCE, 0x3E, 0x76,
	0xE8, 0x36, 0x8C, 0x39, 0xD8, 0xF3, 0xE9, 0xA6, 0x42, 0xE6, 0xC1, 0x4C, 0x05, 0xBE, 0x17, 0xF2,
	0x5C, 0x1B, 0x19, 0xDB, 0x0F, 0xF3, 0xF8, 0x49, 0xEB, 0x36, 0xF6, 0x40, 0x6F, 0xAD, 0xC1, 0x8C
};

/*seed tables for AR v3 */
uint8_t v3_deadtable1[256] = {
    0xD0, 0xFF, 0xBA, 0xE5, 0xC1, 0xC7, 0xDB, 0x5B, 0x16, 0xE3, 0x6E, 0x26, 0x62, 0x31, 0x2E, 0x2A,
    0xD1, 0xBB, 0x4A, 0xE6, 0xAE, 0x2F, 0x0A, 0x90, 0x29, 0x90, 0xB6, 0x67, 0x58, 0x2A, 0xB4, 0x45,
    0x7B, 0xCB, 0xF0, 0x73, 0x84, 0x30, 0x81, 0xC2, 0xD7, 0xBE, 0x89, 0xD7, 0x4E, 0x73, 0x5C, 0xC7,
    0x80, 0x1B, 0xE5, 0xE4, 0x43, 0xC7, 0x46, 0xD6, 0x6F, 0x7B, 0xBF, 0xED, 0xE5, 0x27, 0xD1, 0xB5,
    0xD0, 0xD8, 0xA3, 0xCB, 0x2B, 0x30, 0xA4, 0xF0, 0x84, 0x14, 0x72, 0x5C, 0xFF, 0xA4, 0xFB, 0x54,
    0x9D, 0x70, 0xE2, 0xFF, 0xBE, 0xE8, 0x24, 0x76, 0xE5, 0x15, 0xFB, 0x1A, 0xBC, 0x87, 0x02, 0x2A,
    0x58, 0x8F, 0x9A, 0x95, 0xBD, 0xAE, 0x8D, 0x0C, 0xA5, 0x4C, 0xF2, 0x5C, 0x7D, 0xAD, 0x51, 0xFB,
    0xB1, 0x22, 0x07, 0xE0, 0x29, 0x7C, 0xEB, 0x98, 0x14, 0xC6, 0x31, 0x97, 0xE4, 0x34, 0x8F, 0xCC,
    0x99, 0x56, 0x9F, 0x78, 0x43, 0x91, 0x85, 0x3F, 0xC2, 0xD0, 0xD1, 0x80, 0xD1, 0x77, 0xA7, 0xE2,
    0x43, 0x99, 0x1D, 0x2F, 0x8B, 0x6A, 0xE4, 0x66, 0x82, 0xF7, 0x2B, 0x0B, 0x65, 0x14, 0xC0, 0xC2,
    0x1D, 0x96, 0x78, 0x1C, 0xC4, 0xC3, 0xD2, 0xB1, 0x64, 0x07, 0xD7, 0x6F, 0x02, 0xE9, 0x44, 0x31,
    0xDB, 0x3C, 0xEB, 0x93, 0xED, 0x9A, 0x57, 0x05, 0xB9, 0x0E, 0xAF, 0x1F, 0x48, 0x11, 0xDC, 0x35,
    0x6C, 0xB8, 0xEE, 0x2A, 0x48, 0x2B, 0xBC, 0x89, 0x12, 0x59, 0xCB, 0xD1, 0x18, 0xEA, 0x72, 0x11,
    0x01, 0x75, 0x3B, 0xB5, 0x56, 0xF4, 0x8B, 0xA0, 0x41, 0x75, 0x86, 0x7B, 0x94, 0x12, 0x2D, 0x4C,
    0x0C, 0x22, 0xC9, 0x4A, 0xD8, 0xB1, 0x8D, 0xF0, 0x55, 0x2E, 0x77, 0x50, 0x1C, 0x64, 0x77, 0xAA,
    0x3E, 0xAC, 0xD3, 0x3D, 0xCE, 0x60, 0xCA, 0x5D, 0xA0, 0x92, 0x78, 0xC6, 0x51, 0xFE, 0xF9, 0x30
};
uint8_t v3_deadtable2[256] = {
    0xAA, 0xAF, 0xF0, 0x72, 0x90, 0xF7, 0x71, 0x27, 0x06, 0x11, 0xEB, 0x9C, 0x37, 0x12, 0x72, 0xAA,
    0x65, 0xBC, 0x0D, 0x4A, 0x76, 0xF6, 0x5C, 0xAA, 0xB0, 0x7A, 0x7D, 0x81, 0xC1, 0xCE, 0x2F, 0x9F,
    0x02, 0x75, 0x38, 0xC8, 0xFC, 0x66, 0x05, 0xC2, 0x2C, 0xBD, 0x91, 0xAD, 0x03, 0xB1, 0x88, 0x93,
    0x31, 0xC6, 0xAB, 0x40, 0x23, 0x43, 0x76, 0x54, 0xCA, 0xE7, 0x00, 0x96, 0x9F, 0xD8, 0x24, 0x8B,
    0xE4, 0xDC, 0xDE, 0x48, 0x2C, 0xCB, 0xF7, 0x84, 0x1D, 0x45, 0xE5, 0xF1, 0x75, 0xA0, 0xED, 0xCD,
    0x4B, 0x24, 0x8A, 0xB3, 0x98, 0x7B, 0x12, 0xB8, 0xF5, 0x63, 0x97, 0xB3, 0xA6, 0xA6, 0x0B, 0xDC,
    0xD8, 0x4C, 0xA8, 0x99, 0x27, 0x0F, 0x8F, 0x94, 0x63, 0x0F, 0xB0, 0x11, 0x94, 0xC7, 0xE9, 0x7F,
    0x3B, 0x40, 0x72, 0x4C, 0xDB, 0x84, 0x78, 0xFE, 0xB8, 0x56, 0x08, 0x80, 0xDF, 0x20, 0x2F, 0xB9,
    0x66, 0x2D, 0x60, 0x63, 0xF5, 0x18, 0x15, 0x1B, 0x86, 0x85, 0xB9, 0xB4, 0x68, 0x0E, 0xC6, 0xD1,
    0x8A, 0x81, 0x2B, 0xB3, 0xF6, 0x48, 0xF0, 0x4F, 0x9C, 0x28, 0x1C, 0xA4, 0x51, 0x2F, 0xD7, 0x4B,
    0x17, 0xE7, 0xCC, 0x50, 0x9F, 0xD0, 0xD1, 0x40, 0x0C, 0x0D, 0xCA, 0x83, 0xFA, 0x5E, 0xCA, 0xEC,
    0xBF, 0x4E, 0x7C, 0x8F, 0xF0, 0xAE, 0xC2, 0xD3, 0x28, 0x41, 0x9B, 0xC8, 0x04, 0xB9, 0x4A, 0xBA,
    0x72, 0xE2, 0xB5, 0x06, 0x2C, 0x1E, 0x0B, 0x2C, 0x7F, 0x11, 0xA9, 0x26, 0x51, 0x9D, 0x3F, 0xF8,
    0x62, 0x11, 0x2E, 0x89, 0xD2, 0x9D, 0x35, 0xB1, 0xE4, 0x0A, 0x4D, 0x93, 0x01, 0xA7, 0xD1, 0x2D,
    0x00, 0x87, 0xE2, 0x2D, 0xA4, 0xE9, 0x0A, 0x06, 0x66, 0xF8, 0x1F, 0x44, 0x75, 0xB5, 0x6B, 0x1C,
    0xFC, 0x31, 0x09, 0x48, 0xA3, 0xFF, 0x92, 0x12, 0x58, 0xE9, 0xFA, 0xAE, 0x4F, 0xE2, 0xB4, 0xCC
};

#define debuggerReadMemory(addr) \
  READ32LE((&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]))

#define debuggerReadHalfWord(addr) \
  READ16LE((&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]))

#define debuggerReadByte(addr) \
  map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]

#define debuggerWriteMemory(addr, value) \
  WRITE32LE(&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask], value)

#define debuggerWriteHalfWord(addr, value) \
  WRITE16LE(&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask], value)

#define debuggerWriteByte(addr, value) \
  map[(addr)>>24].address[(addr) & map[(addr)>>24].mask] = (value)


#define CHEAT_IS_HEX(a) ( ((a)>='A' && (a) <='F') || ((a) >='0' && (a) <= '9'))

#define CHEAT_PATCH_ROM_16BIT(a,v) \
  WRITE16LE(((uint16_t *)&rom[(a) & 0x1ffffff]), v);

#define CHEAT_PATCH_ROM_32BIT(a,v) \
  WRITE32LE(((uint32_t *)&rom[(a) & 0x1ffffff]), v);

static bool isMultilineWithData(int i)
{
  /* we consider it a multiline code if it has more than one line of data */
  /* otherwise, it can still be considered a single code */
  /* (Only CBA codes can be true multilines !!!) */
  if(i < cheatsNumber && i >= 0)
    switch(cheatsList[i].size) {
    case INT_8_BIT_WRITE:
    case INT_16_BIT_WRITE:
    case INT_32_BIT_WRITE:
    case GSA_16_BIT_ROM_PATCH:
    case GSA_8_BIT_GS_WRITE:
    case GSA_16_BIT_GS_WRITE:
    case GSA_32_BIT_GS_WRITE:
    case CBA_AND:
    case CBA_IF_KEYS_PRESSED:
    case CBA_IF_TRUE:
    case CBA_IF_FALSE:
    case GSA_8_BIT_IF_TRUE:
    case GSA_32_BIT_IF_TRUE:
    case GSA_8_BIT_IF_FALSE:
    case GSA_32_BIT_IF_FALSE:
    case GSA_8_BIT_FILL:
    case GSA_16_BIT_FILL:
    case GSA_8_BIT_IF_TRUE2:
    case GSA_16_BIT_IF_TRUE2:
    case GSA_32_BIT_IF_TRUE2:
    case GSA_8_BIT_IF_FALSE2:
    case GSA_16_BIT_IF_FALSE2:
    case GSA_32_BIT_IF_FALSE2:
    case GSA_SLOWDOWN:
    case CBA_ADD:
    case CBA_OR:
    case CBA_LT:
    case CBA_GT:
    case GSA_8_BIT_POINTER:
    case GSA_16_BIT_POINTER:
    case GSA_32_BIT_POINTER:
    case GSA_8_BIT_ADD:
    case GSA_16_BIT_ADD:
    case GSA_32_BIT_ADD:
    case GSA_8_BIT_IF_LOWER_U:
    case GSA_16_BIT_IF_LOWER_U:
    case GSA_32_BIT_IF_LOWER_U:
    case GSA_8_BIT_IF_HIGHER_U:
    case GSA_16_BIT_IF_HIGHER_U:
    case GSA_32_BIT_IF_HIGHER_U:
    case GSA_8_BIT_IF_AND:
    case GSA_16_BIT_IF_AND:
    case GSA_32_BIT_IF_AND:
    case GSA_8_BIT_IF_LOWER_U2:
    case GSA_16_BIT_IF_LOWER_U2:
    case GSA_32_BIT_IF_LOWER_U2:
    case GSA_8_BIT_IF_HIGHER_U2:
    case GSA_16_BIT_IF_HIGHER_U2:
    case GSA_32_BIT_IF_HIGHER_U2:
    case GSA_8_BIT_IF_AND2:
    case GSA_16_BIT_IF_AND2:
    case GSA_32_BIT_IF_AND2:
    case GSA_ALWAYS:
    case GSA_ALWAYS2:
    case GSA_8_BIT_IF_LOWER_S:
    case GSA_16_BIT_IF_LOWER_S:
    case GSA_32_BIT_IF_LOWER_S:
    case GSA_8_BIT_IF_HIGHER_S:
    case GSA_16_BIT_IF_HIGHER_S:
    case GSA_32_BIT_IF_HIGHER_S:
    case GSA_8_BIT_IF_LOWER_S2:
    case GSA_16_BIT_IF_LOWER_S2:
    case GSA_32_BIT_IF_LOWER_S2:
    case GSA_8_BIT_IF_HIGHER_S2:
    case GSA_16_BIT_IF_HIGHER_S2:
    case GSA_32_BIT_IF_HIGHER_S2:
    case GSA_16_BIT_WRITE_IOREGS:
    case GSA_32_BIT_WRITE_IOREGS:
    case GSA_CODES_ON:
    case GSA_8_BIT_IF_TRUE3:
    case GSA_16_BIT_IF_TRUE3:
    case GSA_32_BIT_IF_TRUE3:
    case GSA_8_BIT_IF_FALSE3:
    case GSA_16_BIT_IF_FALSE3:
    case GSA_32_BIT_IF_FALSE3:
    case GSA_8_BIT_IF_LOWER_S3:
    case GSA_16_BIT_IF_LOWER_S3:
    case GSA_32_BIT_IF_LOWER_S3:
    case GSA_8_BIT_IF_HIGHER_S3:
    case GSA_16_BIT_IF_HIGHER_S3:
    case GSA_32_BIT_IF_HIGHER_S3:
    case GSA_8_BIT_IF_LOWER_U3:
    case GSA_16_BIT_IF_LOWER_U3:
    case GSA_32_BIT_IF_LOWER_U3:
    case GSA_8_BIT_IF_HIGHER_U3:
    case GSA_16_BIT_IF_HIGHER_U3:
    case GSA_32_BIT_IF_HIGHER_U3:
    case GSA_8_BIT_IF_AND3:
    case GSA_16_BIT_IF_AND3:
    case GSA_32_BIT_IF_AND3:
    case GSA_ALWAYS3:
    case GSA_8_BIT_GS_WRITE2:
    case GSA_16_BIT_GS_WRITE2:
    case GSA_32_BIT_GS_WRITE2:
    case GSA_16_BIT_ROM_PATCH2C:
    case GSA_16_BIT_ROM_PATCH2D:
    case GSA_16_BIT_ROM_PATCH2E:
    case GSA_16_BIT_ROM_PATCH2F:
    case GSA_8_BIT_SLIDE:
    case GSA_16_BIT_SLIDE:
    case GSA_32_BIT_SLIDE:
    case GSA_GROUP_WRITE:
    case GSA_32_BIT_ADD2:
    case GSA_32_BIT_SUB2:
    case GSA_16_BIT_IF_LOWER_OR_EQ_U:
    case GSA_16_BIT_IF_HIGHER_OR_EQ_U:
    case GSA_16_BIT_MIF_TRUE:
    case GSA_16_BIT_MIF_FALSE:
    case GSA_16_BIT_MIF_LOWER_OR_EQ_U:
    case GSA_16_BIT_MIF_HIGHER_OR_EQ_U:
    case MASTER_CODE:
    case CHEATS_16_BIT_WRITE:
    case CHEATS_32_BIT_WRITE:
      return false;
      /* the codes below have two lines of data */
    case CBA_SLIDE_CODE:
    case CBA_SUPER:
      return true;
    }
  return false;
}

static int getCodeLength(int num)
{
  if(num >= cheatsNumber || num < 0)
    return 1;

  /* this is for all the codes that are true multiline */
  switch(cheatsList[num].size) {
  case INT_8_BIT_WRITE:
  case INT_16_BIT_WRITE:
  case INT_32_BIT_WRITE:
  case GSA_16_BIT_ROM_PATCH:
  case GSA_8_BIT_GS_WRITE:
  case GSA_16_BIT_GS_WRITE:
  case GSA_32_BIT_GS_WRITE:
  case CBA_AND:
  case GSA_8_BIT_FILL:
  case GSA_16_BIT_FILL:
  case GSA_SLOWDOWN:
  case CBA_ADD:
  case CBA_OR:
  case GSA_8_BIT_POINTER:
  case GSA_16_BIT_POINTER:
  case GSA_32_BIT_POINTER:
  case GSA_8_BIT_ADD:
  case GSA_16_BIT_ADD:
  case GSA_32_BIT_ADD:
  case GSA_CODES_ON:
  case GSA_8_BIT_IF_TRUE3:
  case GSA_16_BIT_IF_TRUE3:
  case GSA_32_BIT_IF_TRUE3:
  case GSA_8_BIT_IF_FALSE3:
  case GSA_16_BIT_IF_FALSE3:
  case GSA_32_BIT_IF_FALSE3:
  case GSA_8_BIT_IF_LOWER_S3:
  case GSA_16_BIT_IF_LOWER_S3:
  case GSA_32_BIT_IF_LOWER_S3:
  case GSA_8_BIT_IF_HIGHER_S3:
  case GSA_16_BIT_IF_HIGHER_S3:
  case GSA_32_BIT_IF_HIGHER_S3:
  case GSA_8_BIT_IF_LOWER_U3:
  case GSA_16_BIT_IF_LOWER_U3:
  case GSA_32_BIT_IF_LOWER_U3:
  case GSA_8_BIT_IF_HIGHER_U3:
  case GSA_16_BIT_IF_HIGHER_U3:
  case GSA_32_BIT_IF_HIGHER_U3:
  case GSA_8_BIT_IF_AND3:
  case GSA_16_BIT_IF_AND3:
  case GSA_32_BIT_IF_AND3:
  case GSA_8_BIT_IF_LOWER_U:
  case GSA_16_BIT_IF_LOWER_U:
  case GSA_32_BIT_IF_LOWER_U:
  case GSA_8_BIT_IF_HIGHER_U:
  case GSA_16_BIT_IF_HIGHER_U:
  case GSA_32_BIT_IF_HIGHER_U:
  case GSA_8_BIT_IF_AND:
  case GSA_16_BIT_IF_AND:
  case GSA_32_BIT_IF_AND:
  case GSA_ALWAYS:
  case GSA_8_BIT_IF_LOWER_S:
  case GSA_16_BIT_IF_LOWER_S:
  case GSA_32_BIT_IF_LOWER_S:
  case GSA_8_BIT_IF_HIGHER_S:
  case GSA_16_BIT_IF_HIGHER_S:
  case GSA_32_BIT_IF_HIGHER_S:
  case GSA_16_BIT_WRITE_IOREGS:
  case GSA_32_BIT_WRITE_IOREGS:
  case GSA_8_BIT_GS_WRITE2:
  case GSA_16_BIT_GS_WRITE2:
  case GSA_32_BIT_GS_WRITE2:
  case GSA_16_BIT_ROM_PATCH2C:
  case GSA_16_BIT_ROM_PATCH2D:
  case GSA_16_BIT_ROM_PATCH2E:
  case GSA_16_BIT_ROM_PATCH2F:
  case GSA_8_BIT_SLIDE:
  case GSA_16_BIT_SLIDE:
  case GSA_32_BIT_SLIDE:
  case GSA_8_BIT_IF_TRUE:
  case GSA_32_BIT_IF_TRUE:
  case GSA_8_BIT_IF_FALSE:
  case GSA_32_BIT_IF_FALSE:
  case CBA_LT:
  case CBA_GT:
  case CBA_IF_TRUE:
  case CBA_IF_FALSE:
  case GSA_8_BIT_IF_TRUE2:
  case GSA_16_BIT_IF_TRUE2:
  case GSA_32_BIT_IF_TRUE2:
  case GSA_8_BIT_IF_FALSE2:
  case GSA_16_BIT_IF_FALSE2:
  case GSA_32_BIT_IF_FALSE2:
  case GSA_8_BIT_IF_LOWER_U2:
  case GSA_16_BIT_IF_LOWER_U2:
  case GSA_32_BIT_IF_LOWER_U2:
  case GSA_8_BIT_IF_HIGHER_U2:
  case GSA_16_BIT_IF_HIGHER_U2:
  case GSA_32_BIT_IF_HIGHER_U2:
  case GSA_8_BIT_IF_AND2:
  case GSA_16_BIT_IF_AND2:
  case GSA_32_BIT_IF_AND2:
  case GSA_ALWAYS2:
  case GSA_8_BIT_IF_LOWER_S2:
  case GSA_16_BIT_IF_LOWER_S2:
  case GSA_32_BIT_IF_LOWER_S2:
  case GSA_8_BIT_IF_HIGHER_S2:
  case GSA_16_BIT_IF_HIGHER_S2:
  case GSA_32_BIT_IF_HIGHER_S2:
  case GSA_GROUP_WRITE:
  case GSA_32_BIT_ADD2:
  case GSA_32_BIT_SUB2:
  case GSA_16_BIT_IF_LOWER_OR_EQ_U:
  case GSA_16_BIT_IF_HIGHER_OR_EQ_U:
  case GSA_16_BIT_MIF_TRUE:
  case GSA_16_BIT_MIF_FALSE:
  case GSA_16_BIT_MIF_LOWER_OR_EQ_U:
  case GSA_16_BIT_MIF_HIGHER_OR_EQ_U:
  case MASTER_CODE:
  case CHEATS_16_BIT_WRITE:
  case CHEATS_32_BIT_WRITE:
  case UNKNOWN_CODE:
    return 1;
  case CBA_IF_KEYS_PRESSED:
  case CBA_SLIDE_CODE:
    return 2;
  case CBA_SUPER:
    return ((((cheatsList[num].value-1) & 0xFFFF)/3) + 1);
  }
  return 1;
}

int cheatsCheckKeys(uint32_t keys, uint32_t extended)
{
  bool onoff = true;
  int ticks = 0;
  int i;
  mastercode = 0;

  for (i = 0; i<4; i++)
    if (rompatch2addr [i] != 0) {
      CHEAT_PATCH_ROM_16BIT(rompatch2addr [i],rompatch2oldval [i]);
      rompatch2addr [i] = 0;
    }

  for (i = 0; i < cheatsNumber; i++) {
    if(!cheatsList[i].enabled) {
      /* make sure we skip other lines in this code */
      i += getCodeLength(i)-1;
      continue;
    }
    switch(cheatsList[i].size) {
    case GSA_CODES_ON:
      onoff = true;
      break;
    case GSA_SLOWDOWN:
      /* check if button was pressed and released, if so toggle our state */
      if((cheatsList[i].status & 4) && !(extended & 4))
        cheatsList[i].status ^= 1;
      if(extended & 4)
        cheatsList[i].status |= 4;
      else
        cheatsList[i].status &= ~4;

      if(cheatsList[i].status & 1)
        ticks += ((cheatsList[i].value  & 0xFFFF) * 7);
      break;
    case GSA_8_BIT_SLIDE:
      i++;
      if(i < cheatsNumber) {
        uint32_t addr = cheatsList[i-1].value;
        uint8_t value = cheatsList[i].rawaddress;
        int vinc = (cheatsList[i].value >> 24) & 255;
        int count = (cheatsList[i].value >> 16) & 255;
        int ainc = (cheatsList[i].value & 0xffff);
        while(count > 0) {
          CPUWriteByte(addr, value);
          value += vinc;
          addr += ainc;
          count--;
        }
      }
      break;
    case GSA_16_BIT_SLIDE:
      i++;
      if(i < cheatsNumber) {
        uint32_t addr = cheatsList[i-1].value;
        uint16_t value = cheatsList[i].rawaddress;
        int vinc = (cheatsList[i].value >> 24) & 255;
        int count = (cheatsList[i].value >> 16) & 255;
        int ainc = (cheatsList[i].value & 0xffff)*2;
        while(count > 0) {
          CPUWriteHalfWord(addr, value);
          value += vinc;
          addr += ainc;
          count--;
        }
      }
      break;
    case GSA_32_BIT_SLIDE:
      i++;
      if(i < cheatsNumber) {
        uint32_t addr = cheatsList[i-1].value;
        uint32_t value = cheatsList[i].rawaddress;
        int vinc = (cheatsList[i].value >> 24) & 255;
        int count = (cheatsList[i].value >> 16) & 255;
        int ainc = (cheatsList[i].value & 0xffff)*4;
        while(count > 0) {
          CPUWriteMemory(addr, value);
          value += vinc;
          addr += ainc;
          count--;
        }
      }
      break;
    case GSA_8_BIT_GS_WRITE2:
      i++;
      if(i < cheatsNumber) {
        if(extended & 4) {
          CPUWriteByte(cheatsList[i-1].value, cheatsList[i].address);
        }
      }
      break;
    case GSA_16_BIT_GS_WRITE2:
      i++;
      if(i < cheatsNumber) {
        if(extended & 4) {
          CPUWriteHalfWord(cheatsList[i-1].value, cheatsList[i].address);
        }
      }
      break;
    case GSA_32_BIT_GS_WRITE2:
      i++;
      if(i < cheatsNumber) {
        if(extended & 4) {
          CPUWriteMemory(cheatsList[i-1].value, cheatsList[i].address);
        }
      }
      break;
      case GSA_16_BIT_ROM_PATCH:
        if((cheatsList[i].status & 1) == 0) {
          if(CPUReadHalfWord(cheatsList[i].address) != cheatsList[i].value) {
            cheatsList[i].oldValue = CPUReadHalfWord(cheatsList[i].address);
            cheatsList[i].status |= 1;
            CHEAT_PATCH_ROM_16BIT(cheatsList[i].address, cheatsList[i].value);
          }
        }
        break;
    case GSA_16_BIT_ROM_PATCH2C:
      i++;
      if(i < cheatsNumber) {
		  rompatch2addr [0] = ((cheatsList[i-1].value & 0x00FFFFFF) << 1) + 0x8000000;
		  rompatch2oldval [0] = CPUReadHalfWord(rompatch2addr [0]);
		  rompatch2val [0] = cheatsList[i].rawaddress & 0xFFFF;
      }
      break;
    case GSA_16_BIT_ROM_PATCH2D:
      i++;
      if(i < cheatsNumber) {
		  rompatch2addr [1] = ((cheatsList[i-1].value & 0x00FFFFFF) << 1) + 0x8000000;
		  rompatch2oldval [1] = CPUReadHalfWord(rompatch2addr [1]);
		  rompatch2val [1] = cheatsList[i].rawaddress & 0xFFFF;
      }
      break;
    case GSA_16_BIT_ROM_PATCH2E:
      i++;
      if(i < cheatsNumber) {
		  rompatch2addr [2] = ((cheatsList[i-1].value & 0x00FFFFFF) << 1) + 0x8000000;
		  rompatch2oldval [2] = CPUReadHalfWord(rompatch2addr [2]);
		  rompatch2val [2] = cheatsList[i].rawaddress & 0xFFFF;
      }
      break;
    case GSA_16_BIT_ROM_PATCH2F:
      i++;
      if(i < cheatsNumber) {
		  rompatch2addr [3] = ((cheatsList[i-1].value & 0x00FFFFFF) << 1) + 0x8000000;
		  rompatch2oldval [3] = CPUReadHalfWord(rompatch2addr [3]);
		  rompatch2val [3] = cheatsList[i].rawaddress & 0xFFFF;
      }
      break;
    case MASTER_CODE:
        mastercode = cheatsList[i].address;
      break;
    }
    if (onoff) {
      switch(cheatsList[i].size) {
      case INT_8_BIT_WRITE:
        CPUWriteByte(cheatsList[i].address, cheatsList[i].value);
        break;
      case INT_16_BIT_WRITE:
        CPUWriteHalfWord(cheatsList[i].address, cheatsList[i].value);
        break;
      case INT_32_BIT_WRITE:
        CPUWriteMemory(cheatsList[i].address, cheatsList[i].value);
        break;
      case GSA_8_BIT_GS_WRITE:
        if(extended & 4) {
          CPUWriteByte(cheatsList[i].address, cheatsList[i].value);
        }
        break;
      case GSA_16_BIT_GS_WRITE:
        if(extended & 4) {
          CPUWriteHalfWord(cheatsList[i].address, cheatsList[i].value);
        }
        break;
      case GSA_32_BIT_GS_WRITE:
        if(extended & 4) {
          CPUWriteMemory(cheatsList[i].address, cheatsList[i].value);
        }
        break;
      case CBA_IF_KEYS_PRESSED:
        {
          uint16_t value = cheatsList[i].value;
          uint32_t addr = cheatsList[i].address;
          if((addr & 0xF0) == 0x20) {
            if((keys & value) == 0) {
              i++;
			}
		  } else if((addr & 0xF0) == 0x10) {
            if((keys & value) == value) {
              i++;
			}
		  } else if((addr & 0xF0) == 0x00) {
            if(((~keys) & 0x3FF) == value) {
              i++;
			}
		  }
		}
        break;
      case CBA_IF_TRUE:
        if(CPUReadHalfWord(cheatsList[i].address) != cheatsList[i].value) {
          i++;
        }
        break;
      case CBA_SLIDE_CODE:
		{
          uint32_t address = cheatsList[i].address;
          uint16_t value = cheatsList[i].value;
          i++;
          if(i < cheatsNumber) {
            int x;
            int count = ((cheatsList[i].address - 1) & 0xFFFF);
            uint16_t vinc = (cheatsList[i].address >> 16) & 0xFFFF;
            int inc = cheatsList[i].value;
            for(x = 0; x <= count ; x++) {
              CPUWriteHalfWord(address, value);
              address += inc;
              value += vinc;
			}
		  }
		}
        break;
      case CBA_IF_FALSE:
        if(CPUReadHalfWord(cheatsList[i].address) == cheatsList[i].value){
          i++;
        }
      break;
      case CBA_AND:
        CPUWriteHalfWord(cheatsList[i].address,
                         CPUReadHalfWord(cheatsList[i].address) &
                         cheatsList[i].value);
        break;
      case GSA_8_BIT_IF_TRUE:
        if(CPUReadByte(cheatsList[i].address) != cheatsList[i].value) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_TRUE:
        if(CPUReadMemory(cheatsList[i].address) != cheatsList[i].value) {
          i++;
        }
        break;
      case GSA_8_BIT_IF_FALSE:
        if(CPUReadByte(cheatsList[i].address) == cheatsList[i].value) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_FALSE:
        if(CPUReadMemory(cheatsList[i].address) == cheatsList[i].value) {
          i++;
        }
        break;
      case GSA_8_BIT_FILL:
		{
          uint32_t addr = cheatsList[i].address;
          uint8_t v = cheatsList[i].value & 0xff;
          uint32_t end = addr + (cheatsList[i].value >> 8);
          do {
            CPUWriteByte(addr, v);
            addr++;
		  } while (addr <= end);
		}
        break;
      case GSA_16_BIT_FILL:
		{
          uint32_t addr = cheatsList[i].address;
          uint16_t v = cheatsList[i].value & 0xffff;
          uint32_t end = addr + ((cheatsList[i].value >> 16) << 1);
          do {
            CPUWriteHalfWord(addr, v);
            addr+=2;
		  } while (addr <= end);
		}
        break;
      case GSA_8_BIT_IF_TRUE2:
        if(CPUReadByte(cheatsList[i].address) != cheatsList[i].value) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_TRUE2:
        if(CPUReadHalfWord(cheatsList[i].address) != cheatsList[i].value) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_TRUE2:
        if(CPUReadMemory(cheatsList[i].address) != cheatsList[i].value) {
          i+=2;
        }
        break;
      case GSA_8_BIT_IF_FALSE2:
        if(CPUReadByte(cheatsList[i].address) == cheatsList[i].value) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_FALSE2:
        if(CPUReadHalfWord(cheatsList[i].address) == cheatsList[i].value) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_FALSE2:
        if(CPUReadMemory(cheatsList[i].address) == cheatsList[i].value) {
          i+=2;
        }
        break;
      case CBA_ADD:
        if ((cheatsList[i].address & 1) == 0) {
          CPUWriteHalfWord(cheatsList[i].address,
                           CPUReadHalfWord(cheatsList[i].address) +
                           cheatsList[i].value);
        } else {
          CPUWriteMemory(cheatsList[i].address & 0x0FFFFFFE,
                           CPUReadMemory(cheatsList[i].address & 0x0FFFFFFE) +
                           cheatsList[i].value);
        }
        break;
      case CBA_OR:
        CPUWriteHalfWord(cheatsList[i].address,
                         CPUReadHalfWord(cheatsList[i].address) |
                         cheatsList[i].value);
        break;
      case CBA_GT:
        if (!(CPUReadHalfWord(cheatsList[i].address) > cheatsList[i].value)){
          i++;
        }
        break;
      case CBA_LT:
        if (!(CPUReadHalfWord(cheatsList[i].address) < cheatsList[i].value)){
          i++;
        }
        break;
      case CBA_SUPER:
		{
          int x;
          int count = 2*((cheatsList[i].value -1) & 0xFFFF)+1;
          uint32_t address = cheatsList[i].address;
          for(x = 0; x <= count; x++) {
            uint8_t b;
            int res = x % 6;
		    if (res==0)
		 	  i++;
            if(res < 4)
              b = (cheatsList[i].address >> (24-8*res)) & 0xFF;
            else
              b = (cheatsList[i].value >> (8 - 8*(res-4))) & 0xFF;
            CPUWriteByte(address, b);
            address++;
		  }
		}
        break;
      case GSA_8_BIT_POINTER :
        if (((CPUReadMemory(cheatsList[i].address)>=0x02000000) && (CPUReadMemory(cheatsList[i].address)<0x02040000)) ||
            ((CPUReadMemory(cheatsList[i].address)>=0x03000000) && (CPUReadMemory(cheatsList[i].address)<0x03008000)))
        {
          CPUWriteByte(CPUReadMemory(cheatsList[i].address)+((cheatsList[i].value & 0xFFFFFF00) >> 8),
                       cheatsList[i].value & 0xFF);
        }
        break;
      case GSA_16_BIT_POINTER :
        if (((CPUReadMemory(cheatsList[i].address)>=0x02000000) && (CPUReadMemory(cheatsList[i].address)<0x02040000)) ||
            ((CPUReadMemory(cheatsList[i].address)>=0x03000000) && (CPUReadMemory(cheatsList[i].address)<0x03008000)))
        {
          CPUWriteHalfWord(CPUReadMemory(cheatsList[i].address)+((cheatsList[i].value & 0xFFFF0000) >> 15),
                       cheatsList[i].value & 0xFFFF);
        }
        break;
      case GSA_32_BIT_POINTER :
        if (((CPUReadMemory(cheatsList[i].address)>=0x02000000) && (CPUReadMemory(cheatsList[i].address)<0x02040000)) ||
            ((CPUReadMemory(cheatsList[i].address)>=0x03000000) && (CPUReadMemory(cheatsList[i].address)<0x03008000)))
        {
          CPUWriteMemory(CPUReadMemory(cheatsList[i].address),
                       cheatsList[i].value);
        }
        break;
      case GSA_8_BIT_ADD :
        CPUWriteByte(cheatsList[i].address,
                    (cheatsList[i].value & 0xFF) + (CPUReadMemory(cheatsList[i].address) & 0xFF));
        break;
      case GSA_16_BIT_ADD :
        CPUWriteHalfWord(cheatsList[i].address,
                        (cheatsList[i].value & 0xFFFF) + (CPUReadMemory(cheatsList[i].address) & 0xFFFF));
        break;
      case GSA_32_BIT_ADD :
        CPUWriteMemory(cheatsList[i].address ,
                       cheatsList[i].value + (CPUReadMemory(cheatsList[i].address) & 0xFFFFFFFF));
        break;
      case GSA_8_BIT_IF_LOWER_U:
        if (!(CPUReadByte(cheatsList[i].address) < (cheatsList[i].value & 0xFF))) {
          i++;
        }
        break;
      case GSA_16_BIT_IF_LOWER_U:
        if (!(CPUReadHalfWord(cheatsList[i].address) < (cheatsList[i].value & 0xFFFF))) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_LOWER_U:
        if (!(CPUReadMemory(cheatsList[i].address) < cheatsList[i].value)) {
          i++;
        }
        break;
      case GSA_8_BIT_IF_HIGHER_U:
        if (!(CPUReadByte(cheatsList[i].address) > (cheatsList[i].value & 0xFF))) {
          i++;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_U:
        if (!(CPUReadHalfWord(cheatsList[i].address) > (cheatsList[i].value & 0xFFFF))) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_HIGHER_U:
        if (!(CPUReadMemory(cheatsList[i].address) > cheatsList[i].value)) {
          i++;
        }
        break;
      case GSA_8_BIT_IF_AND:
        if (!(CPUReadByte(cheatsList[i].address) & (cheatsList[i].value & 0xFF))) {
          i++;
        }
        break;
      case GSA_16_BIT_IF_AND:
        if (!(CPUReadHalfWord(cheatsList[i].address) & (cheatsList[i].value & 0xFFFF))) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_AND:
        if (!(CPUReadMemory(cheatsList[i].address) & cheatsList[i].value)) {
          i++;
        }
        break;
      case GSA_8_BIT_IF_LOWER_U2:
        if (!(CPUReadByte(cheatsList[i].address) < (cheatsList[i].value & 0xFF))) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_LOWER_U2:
        if (!(CPUReadHalfWord(cheatsList[i].address) < (cheatsList[i].value & 0xFFFF))) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_LOWER_U2:
        if (!(CPUReadMemory(cheatsList[i].address) < cheatsList[i].value)) {
          i+=2;
        }
        break;
      case GSA_8_BIT_IF_HIGHER_U2:
        if (!(CPUReadByte(cheatsList[i].address) > (cheatsList[i].value & 0xFF))) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_U2:
        if (!(CPUReadHalfWord(cheatsList[i].address) > (cheatsList[i].value & 0xFFFF))) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_HIGHER_U2:
        if (!(CPUReadMemory(cheatsList[i].address) > cheatsList[i].value)) {
          i+=2;
        }
        break;
      case GSA_8_BIT_IF_AND2:
        if (!(CPUReadByte(cheatsList[i].address) & (cheatsList[i].value & 0xFF))) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_AND2:
        if (!(CPUReadHalfWord(cheatsList[i].address) & (cheatsList[i].value & 0xFFFF))) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_AND2:
        if (!(CPUReadMemory(cheatsList[i].address) & cheatsList[i].value)) {
          i+=2;
        }
        break;
      case GSA_ALWAYS:
        i++;
        break;
      case GSA_ALWAYS2:
        i+=2;
        break;
      case GSA_8_BIT_IF_LOWER_S:
        if (!((int8_t)CPUReadByte(cheatsList[i].address) < ((int8_t)cheatsList[i].value & 0xFF))) {
          i++;
        }
        break;
      case GSA_16_BIT_IF_LOWER_S:
        if (!((int16_t)CPUReadHalfWord(cheatsList[i].address) < ((int16_t)cheatsList[i].value & 0xFFFF))) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_LOWER_S:
        if (!((int32_t)CPUReadMemory(cheatsList[i].address) < (int32_t)cheatsList[i].value)) {
          i++;
        }
        break;
      case GSA_8_BIT_IF_HIGHER_S:
        if (!((int8_t)CPUReadByte(cheatsList[i].address) > ((int8_t)cheatsList[i].value & 0xFF))) {
          i++;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_S:
        if (!((int16_t)CPUReadHalfWord(cheatsList[i].address) > ((int16_t)cheatsList[i].value & 0xFFFF))) {
          i++;
        }
        break;
      case GSA_32_BIT_IF_HIGHER_S:
        if (!((int32_t)CPUReadMemory(cheatsList[i].address) > (int32_t)cheatsList[i].value)) {
          i++;
        }
        break;
      case GSA_8_BIT_IF_LOWER_S2:
        if (!((int8_t)CPUReadByte(cheatsList[i].address) < ((int8_t)cheatsList[i].value & 0xFF))) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_LOWER_S2:
        if (!((int16_t)CPUReadHalfWord(cheatsList[i].address) < ((int16_t)cheatsList[i].value & 0xFFFF))) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_LOWER_S2:
        if (!((int32_t)CPUReadMemory(cheatsList[i].address) < (int32_t)cheatsList[i].value)) {
          i+=2;
        }
        break;
      case GSA_8_BIT_IF_HIGHER_S2:
        if (!((int8_t)CPUReadByte(cheatsList[i].address) > ((int8_t)cheatsList[i].value & 0xFF))) {
          i+=2;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_S2:
        if (!((int16_t)CPUReadHalfWord(cheatsList[i].address) > ((int16_t)cheatsList[i].value & 0xFFFF))) {
          i+=2;
        }
        break;
      case GSA_32_BIT_IF_HIGHER_S2:
        if (!((int32_t)CPUReadMemory(cheatsList[i].address) > (int32_t)cheatsList[i].value)) {
          i+=2;
        }
        break;
      case GSA_16_BIT_WRITE_IOREGS:
        if ((cheatsList[i].address <= 0x3FF) && (cheatsList[i].address != 0x6) &&
            (cheatsList[i].address != 0x130))
          ioMem[cheatsList[i].address & 0x3FE]=cheatsList[i].value & 0xFFFF;
        break;
      case GSA_32_BIT_WRITE_IOREGS:
        if (cheatsList[i].address<=0x3FF)
        {
          /* Exclude 32-bit writes that would clobber REG_VCOUNT (0x006) or
           * REG_KEYINPUT (0x130).  The 4-byte block containing VCOUNT is
           * aligned at 0x004 (it shares the word with DISPSTAT at 0x004).
           * The original check compared `addr & 0x3FC` against 0x6, which
           * is unreachable post-mask (bit 1 is always cleared) -- so the
           * VCOUNT guard was always-true and never excluded anything.  The
           * +2 second-half guard is fine: `(addr & 0x3FC) + 2` reaches 0x6
           * legitimately when the source word lies at 0x4. */
          if (((cheatsList[i].address & 0x3FC) != 0x4) && ((cheatsList[i].address & 0x3FC) != 0x130))
            ioMem[cheatsList[i].address & 0x3FC]= (cheatsList[i].value & 0xFFFF);
          if ((((cheatsList[i].address & 0x3FC)+2) != 0x6) && ((cheatsList[i].address & 0x3FC) +2) != 0x130)
            ioMem[(cheatsList[i].address & 0x3FC) + 2 ]= ((cheatsList[i].value>>16 ) & 0xFFFF);
        }
        break;
      case GSA_8_BIT_IF_TRUE3:
        if(CPUReadByte(cheatsList[i].address) != cheatsList[i].value) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_TRUE3:
        if(CPUReadHalfWord(cheatsList[i].address) != cheatsList[i].value) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_TRUE3:
        if(CPUReadMemory(cheatsList[i].address) != cheatsList[i].value) {
          onoff=false;
        }
        break;
      case GSA_8_BIT_IF_FALSE3:
        if(CPUReadByte(cheatsList[i].address) == cheatsList[i].value) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_FALSE3:
        if(CPUReadHalfWord(cheatsList[i].address) == cheatsList[i].value) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_FALSE3:
        if(CPUReadMemory(cheatsList[i].address) == cheatsList[i].value) {
          onoff=false;
        }
        break;
      case GSA_8_BIT_IF_LOWER_S3:
        if (!((int8_t)CPUReadByte(cheatsList[i].address) < ((int8_t)cheatsList[i].value & 0xFF))) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_LOWER_S3:
        if (!((int16_t)CPUReadHalfWord(cheatsList[i].address) < ((int16_t)cheatsList[i].value & 0xFFFF))) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_LOWER_S3:
        if (!((int32_t)CPUReadMemory(cheatsList[i].address) < (int32_t)cheatsList[i].value)) {
          onoff=false;
        }
        break;
      case GSA_8_BIT_IF_HIGHER_S3:
        if (!((int8_t)CPUReadByte(cheatsList[i].address) > ((int8_t)cheatsList[i].value & 0xFF))) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_S3:
        if (!((int16_t)CPUReadHalfWord(cheatsList[i].address) > ((int16_t)cheatsList[i].value & 0xFFFF))) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_HIGHER_S3:
        if (!((int32_t)CPUReadMemory(cheatsList[i].address) > (int32_t)cheatsList[i].value)) {
          onoff=false;
        }
        break;
      case GSA_8_BIT_IF_LOWER_U3:
        if (!(CPUReadByte(cheatsList[i].address) < (cheatsList[i].value & 0xFF))) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_LOWER_U3:
        if (!(CPUReadHalfWord(cheatsList[i].address) < (cheatsList[i].value & 0xFFFF))) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_LOWER_U3:
        if (!(CPUReadMemory(cheatsList[i].address) < cheatsList[i].value)) {
          onoff=false;
        }
        break;
      case GSA_8_BIT_IF_HIGHER_U3:
        if (!(CPUReadByte(cheatsList[i].address) > (cheatsList[i].value & 0xFF))) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_U3:
        if (!(CPUReadHalfWord(cheatsList[i].address) > (cheatsList[i].value & 0xFFFF))) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_HIGHER_U3:
        if (!(CPUReadMemory(cheatsList[i].address) > cheatsList[i].value)) {
          onoff=false;
        }
        break;
      case GSA_8_BIT_IF_AND3:
        if (!(CPUReadByte(cheatsList[i].address) & (cheatsList[i].value & 0xFF))) {
          onoff=false;
        }
        break;
      case GSA_16_BIT_IF_AND3:
        if (!(CPUReadHalfWord(cheatsList[i].address) & (cheatsList[i].value & 0xFFFF))) {
          onoff=false;
        }
        break;
      case GSA_32_BIT_IF_AND3:
        if (!(CPUReadMemory(cheatsList[i].address) & cheatsList[i].value)) {
          onoff=false;
        }
        break;
      case GSA_ALWAYS3:
        if (!(CPUReadMemory(cheatsList[i].address) & cheatsList[i].value)) {
          onoff=false;
        }
        break;
      case GSA_GROUP_WRITE:
      	{
          int x;
          int count = ((cheatsList[i].address) & 0xFFFE) +1;
          uint32_t value = cheatsList[i].value;
		  if (count==0)
			  i++;
		  else
            for(x = 1; x <= count; x++) {
				if ((x % 2) ==0){
					if (x<count)
						i++;
					CPUWriteMemory(cheatsList[i].rawaddress, value);
				}
				else
					CPUWriteMemory(cheatsList[i].value, value);
			}
		}
		break;
      case GSA_32_BIT_ADD2:
        CPUWriteMemory(cheatsList[i].value ,
                       (CPUReadMemory(cheatsList[i].value) + cheatsList[i+1].rawaddress) & 0xFFFFFFFF);
        i++;
		break;
      case GSA_32_BIT_SUB2:
        CPUWriteMemory(cheatsList[i].value ,
                       (CPUReadMemory(cheatsList[i].value) - cheatsList[i+1].rawaddress) & 0xFFFFFFFF);
        i++;
		break;
      case GSA_16_BIT_IF_LOWER_OR_EQ_U:
        if(CPUReadHalfWord(cheatsList[i].address) > cheatsList[i].value) {
          i++;
        }
        break;
      case GSA_16_BIT_IF_HIGHER_OR_EQ_U:
        if(CPUReadHalfWord(cheatsList[i].address) < cheatsList[i].value) {
          i++;
        }
        break;
      case GSA_16_BIT_MIF_TRUE:
        if(CPUReadHalfWord(cheatsList[i].address) != cheatsList[i].value) {
          i+=((cheatsList[i].rawaddress >> 0x10) & 0xFF);
        }
        break;
      case GSA_16_BIT_MIF_FALSE:
        if(CPUReadHalfWord(cheatsList[i].address) == cheatsList[i].value) {
          i+=(cheatsList[i].rawaddress >> 0x10) & 0xFF;
        }
        break;
      case GSA_16_BIT_MIF_LOWER_OR_EQ_U:
        if(CPUReadHalfWord(cheatsList[i].address) > cheatsList[i].value) {
          i+=(cheatsList[i].rawaddress >> 0x10) & 0xFF;
        }
        break;
      case GSA_16_BIT_MIF_HIGHER_OR_EQ_U:
        if(CPUReadHalfWord(cheatsList[i].address) < cheatsList[i].value) {
          i+=(cheatsList[i].rawaddress >> 0x10) & 0xFF;
        }
        break;
      case CHEATS_16_BIT_WRITE:
        if ((cheatsList[i].address>>24)>=0x08) {
          CHEAT_PATCH_ROM_16BIT(cheatsList[i].address, cheatsList[i].value);
        } else {
          CPUWriteHalfWord(cheatsList[i].address, cheatsList[i].value);
        }
        break;
      case CHEATS_32_BIT_WRITE:
        if ((cheatsList[i].address>>24)>=0x08) {
          CHEAT_PATCH_ROM_32BIT(cheatsList[i].address, cheatsList[i].value);
        } else {
          CPUWriteMemory(cheatsList[i].address, cheatsList[i].value);
        }
        break;
      }
    }
  }
  for (i = 0; i<4; i++)
    if (rompatch2addr [i] != 0)
      CHEAT_PATCH_ROM_16BIT(rompatch2addr [i],rompatch2val [i]);
  return ticks;
}

void cheatsAdd(const char *codeStr,
               const char *desc,
               uint32_t rawaddress,
               uint32_t address,
               uint32_t value,
               int code,
               int size)
{
  if(cheatsNumber < 100) {
    int x = cheatsNumber;
    cheatsList[x].code = code;
    cheatsList[x].size = size;
    cheatsList[x].rawaddress = rawaddress;
    cheatsList[x].address = address;
    cheatsList[x].value = value;
    /* Use snprintf to bound the copy. Callers currently stay under the limits
     * (16 chars for codeStr from retro_cheat_set; ~8 for "cheat_NNN" desc),
     * but defending here costs nothing. */
    snprintf(cheatsList[x].codestring, sizeof(cheatsList[x].codestring), "%s", codeStr ? codeStr : "");
    snprintf(cheatsList[x].desc, sizeof(cheatsList[x].desc), "%s", desc ? desc : "");
    cheatsList[x].enabled = true;
    cheatsList[x].status = 0;

    /* we only store the old value for this simple codes. ROM patching */
    /* is taken care when it actually patches the ROM */
    switch(cheatsList[x].size) {
    case INT_8_BIT_WRITE:
      cheatsList[x].oldValue = CPUReadByte(address);
      break;
    case INT_16_BIT_WRITE:
      cheatsList[x].oldValue = CPUReadHalfWord(address);
      break;
    case INT_32_BIT_WRITE:
      cheatsList[x].oldValue = CPUReadMemory(address);
      break;
    case CHEATS_16_BIT_WRITE:
      cheatsList[x].oldValue = CPUReadHalfWord(address);
      break;
    case CHEATS_32_BIT_WRITE:
      cheatsList[x].oldValue = CPUReadMemory(address);
      break;
    }
    cheatsNumber++;
  }
}

void cheatsDelete(int number, bool restore)
{
  if(number < cheatsNumber && number >= 0) {
    int x = number;

    if(restore) {
      switch(cheatsList[x].size) {
      case INT_8_BIT_WRITE:
        CPUWriteByte(cheatsList[x].address, (uint8_t)cheatsList[x].oldValue);
        break;
      case INT_16_BIT_WRITE:
        CPUWriteHalfWord(cheatsList[x].address, (uint16_t)cheatsList[x].oldValue);
        break;
      case INT_32_BIT_WRITE:
        CPUWriteMemory(cheatsList[x].address, cheatsList[x].oldValue);
        break;
      case CHEATS_16_BIT_WRITE:
        if ((cheatsList[x].address>>24)>=0x08) {
          CHEAT_PATCH_ROM_16BIT(cheatsList[x].address, cheatsList[x].oldValue);
        } else {
          CPUWriteHalfWord(cheatsList[x].address, cheatsList[x].oldValue);
        }
        break;
      case CHEATS_32_BIT_WRITE:
        if ((cheatsList[x].address>>24)>=0x08) {
          CHEAT_PATCH_ROM_32BIT(cheatsList[x].address, cheatsList[x].oldValue);
        } else {
          CPUWriteMemory(cheatsList[x].address, cheatsList[x].oldValue);
        }
        break;
      case GSA_16_BIT_ROM_PATCH:
        if(cheatsList[x].status & 1) {
          cheatsList[x].status &= ~1;
          CHEAT_PATCH_ROM_16BIT(cheatsList[x].address,
                                cheatsList[x].oldValue);
        }
        break;
      case GSA_16_BIT_ROM_PATCH2C:
      case GSA_16_BIT_ROM_PATCH2D:
      case GSA_16_BIT_ROM_PATCH2E:
      case GSA_16_BIT_ROM_PATCH2F:
        if(cheatsList[x].status & 1) {
          cheatsList[x].status &= ~1;
        }
        break;
      case MASTER_CODE:
        mastercode=0;
        break;
      }
    }
    if((x+1) <  cheatsNumber) {
      memcpy(&cheatsList[x], &cheatsList[x+1], sizeof(CheatsData)*
             (cheatsNumber-x-1));
    }
    cheatsNumber--;
  }
}

void cheatsDeleteAll(bool restore)
{
  int i;
  for(i = cheatsNumber-1; i >= 0; i--) {
    cheatsDelete(i, restore);
  }
}

static uint16_t cheatsGSAGetDeadface(bool v3)
{
  int i;
  for(i = cheatsNumber-1; i >= 0; i--)
    if ((cheatsList[i].address == 0xDEADFACE) && (cheatsList[i].code == (v3 ? 257 : 256)))
      return cheatsList[i].value & 0xFFFF;
	return 0;
}

static void cheatsGSAChangeEncryption(uint16_t value, bool v3) {
	int i;
	uint8_t *deadtable1, *deadtable2;

	if (v3) {
		deadtable1 = (uint8_t*)(&v3_deadtable1);
		deadtable2 = (uint8_t*)(&v3_deadtable2);
	        for (i = 0; i < 4; i++)
		  seeds_v3[i] = seed_gen(((value & 0xFF00) >> 8), (value & 0xFF) + i, deadtable1, deadtable2);
	}
	else {
		deadtable1 = (uint8_t*)(&v1_deadtable1);
		deadtable2 = (uint8_t*)(&v1_deadtable2);
		for (i = 0; i < 4; i++){
		  seeds_v1[i] = seed_gen(((value & 0xFF00) >> 8), (value & 0xFF) + i, deadtable1, deadtable2);
		}
	}
}

uint32_t seed_gen(uint8_t upper, uint8_t seed, uint8_t *deadtable1, uint8_t *deadtable2) {
	int i;
	uint32_t newseed = 0;

	for (i = 0; i < 4; i++)
		newseed = ((newseed << 8) | ((deadtable1[(i + upper) & 0xFF] + deadtable2[seed]) & 0xFF));

	return newseed;
}

static void cheatsDecryptGSACode(uint32_t *address, uint32_t *value, bool v3)
{
  uint32_t rollingseed = 0xC6EF3720;
  uint32_t *seeds = v3 ? seeds_v3 : seeds_v1;

  int bitsleft = 32;
  while (bitsleft > 0) {
    *value -= ((((*address << 4) + seeds[2]) ^ (*address + rollingseed)) ^
              ((*address >> 5) + seeds[3]));
    *address -= ((((*value << 4) + seeds[0]) ^ (*value + rollingseed)) ^
                ((*value >> 5) + seeds[1]));
    rollingseed -= 0x9E3779B9;
    bitsleft--;
  }
}

void cheatsAddGSACode(const char *code, const char *desc, bool v3)
{
  int i;
  char buffer[10];
  uint32_t address;
  uint32_t value;
  if(strlen(code) != 16) {
    /* wrong cheat */
    systemMessage("Invalid GSA code. Format is XXXXXXXXYYYYYYYY");
    return;
  }

  for(i = 0; i < 16; i++) {
    if(!CHEAT_IS_HEX(code[i])) {
      /* wrong cheat */
      systemMessage("Invalid GSA code. Format is XXXXXXXXYYYYYYYY");
      return;
    }
  }

  strncpy(buffer, code, 8);
  buffer[8] = 0;
  sscanf(buffer, "%x", &address);
  strncpy(buffer, &code[8], 8);
  buffer[8] = 0;
  sscanf(buffer, "%x", &value);
  cheatsGSAChangeEncryption(cheatsGSAGetDeadface (v3), v3);
  cheatsDecryptGSACode(&address, &value, v3);

  if(value == 0x1DC0DE) {
    uint32_t gamecode = READ32LE(((uint32_t *)&rom[0xac]));
    if(gamecode != address) {
      char buffer[5];
      char buffer2[5];
      uint32_t gid;
      /* address is a host-byte-order uint32_t of 4 ASCII chars; write byte-by-byte
       * to avoid unaligned uint32_t stores (UB on strict-alignment BE: PPC/Wii/X360)
       * and to keep the ASCII order consistent on both endians. */
      buffer[0] = (char)(address & 0xff);
      buffer[1] = (char)((address >> 8) & 0xff);
      buffer[2] = (char)((address >> 16) & 0xff);
      buffer[3] = (char)((address >> 24) & 0xff);
      buffer[4] = 0;
      gid = READ32LE(((uint32_t *)&rom[0xac]));
      buffer2[0] = (char)(gid & 0xff);
      buffer2[1] = (char)((gid >> 8) & 0xff);
      buffer2[2] = (char)((gid >> 16) & 0xff);
      buffer2[3] = (char)((gid >> 24) & 0xff);
      buffer2[4] = 0;
      systemMessage("Warning: cheats are for game %s. Current game is %s.\nCodes may not work correctly.",
                    buffer, buffer2);
    }
    cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, v3 ? 257 : 256,
              UNKNOWN_CODE);
    return;
  }
  if(isMultilineWithData(cheatsNumber-1)) {
    cheatsAdd(code, desc, address, address, value, v3 ? 257 : 256, UNKNOWN_CODE);
    return;
  }
  if(v3) {
    int type = ((address >> 25) & 127) | ((address >> 17) & 0x80);
    uint32_t addr = (address & 0x00F00000) << 4 | (address & 0x0003FFFF);
    uint16_t mcode = (address>>24 & 0xFF);

    if ((mcode & 0xFE) == 0xC4)
    {
      cheatsAdd(code, desc, address, (address & 0x1FFFFFF) | (0x08000000),
        value, 257, MASTER_CODE);
      mastercode = (address & 0x1FFFFFF) | (0x08000000);
    }
    else
    switch(type) {
    case 0x00:
      if(address == 0) {
        type = (value >> 25) & 127;
        addr = (value & 0x00F00000) << 4 | (value & 0x0003FFFF);
        switch(type) {
        case 0x04:
          cheatsAdd(code, desc, address, 0, value & 0x00FFFFFF, 257, GSA_SLOWDOWN);
          break;
        case 0x08:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_8_BIT_GS_WRITE2);
          break;
        case 0x09:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_16_BIT_GS_WRITE2);
          break;
        case 0x0a:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_32_BIT_GS_WRITE2);
          break;
        case 0x0c:
          cheatsAdd(code, desc, address, 0, value & 0x00FFFFFF, 257, GSA_16_BIT_ROM_PATCH2C);
          break;
        case 0x0d:
          cheatsAdd(code, desc, address, 0, value & 0x00FFFFFF, 257, GSA_16_BIT_ROM_PATCH2D);
          break;
        case 0x0e:
          cheatsAdd(code, desc, address, 0, value & 0x00FFFFFF, 257, GSA_16_BIT_ROM_PATCH2E);
          break;
        case 0x0f:
          cheatsAdd(code, desc, address, 0, value & 0x00FFFFFF, 257, GSA_16_BIT_ROM_PATCH2F);
          break;
        case 0x20:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_CODES_ON);
          break;
        case 0x40:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_8_BIT_SLIDE);
          break;
        case 0x41:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_16_BIT_SLIDE);
          break;
        case 0x42:
          cheatsAdd(code, desc, address, 0, addr, 257, GSA_32_BIT_SLIDE);
          break;
        default:
          cheatsAdd(code, desc, address, address, value, 257, UNKNOWN_CODE);
          break;
        }
      } else
        cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_FILL);
      break;
    case 0x01:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_FILL);
      break;
    case 0x02:
      cheatsAdd(code, desc, address, addr, value, 257, INT_32_BIT_WRITE);
      break;
    case 0x04:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_TRUE);
      break;
    case 0x05:
      cheatsAdd(code, desc, address, addr, value, 257, CBA_IF_TRUE);
      break;
    case 0x06:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_TRUE);
      break;
    case 0x07:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_ALWAYS);
      break;
    case 0x08:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_FALSE);
      break;
    case 0x09:
      cheatsAdd(code, desc, address, addr, value, 257, CBA_IF_FALSE);
      break;
    case 0x0a:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_FALSE);
      break;
    case 0xc:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_LOWER_S);
      break;
    case 0xd:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_LOWER_S);
      break;
    case 0xe:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_LOWER_S);
      break;
    case 0x10:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_HIGHER_S);
      break;
    case 0x11:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_HIGHER_S);
      break;
    case 0x12:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_HIGHER_S);
      break;
    case 0x14:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_LOWER_U);
      break;
    case 0x15:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_LOWER_U);
      break;
    case 0x16:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_LOWER_U);
      break;
    case 0x18:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_HIGHER_U);
      break;
    case 0x19:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_HIGHER_U);
      break;
    case 0x1A:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_HIGHER_U);
      break;
    case 0x1C:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_AND);
      break;
    case 0x1D:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_AND);
      break;
    case 0x1E:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_AND);
      break;
    case 0x20:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_POINTER);
      break;
    case 0x21:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_POINTER);
      break;
    case 0x22:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_POINTER);
      break;
    case 0x24:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_TRUE2);
      break;
    case 0x25:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_TRUE2);
      break;
    case 0x26:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_TRUE2);
      break;
    case 0x27:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_ALWAYS2);
      break;
    case 0x28:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_FALSE2);
      break;
    case 0x29:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_FALSE2);
      break;
    case 0x2a:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_FALSE2);
      break;
    case 0x2c:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_LOWER_S2);
      break;
    case 0x2d:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_LOWER_S2);
      break;
    case 0x2e:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_LOWER_S2);
      break;
    case 0x30:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_HIGHER_S2);
      break;
    case 0x31:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_HIGHER_S2);
      break;
    case 0x32:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_HIGHER_S2);
      break;
    case 0x34:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_LOWER_U2);
      break;
    case 0x35:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_LOWER_U2);
      break;
    case 0x36:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_LOWER_U2);
      break;
    case 0x38:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_HIGHER_U2);
      break;
    case 0x39:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_HIGHER_U2);
      break;
    case 0x3A:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_HIGHER_U2);
      break;
    case 0x3C:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_AND2);
      break;
    case 0x3D:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_AND2);
      break;
    case 0x3E:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_AND2);
      break;
    case 0x40:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_ADD);
      break;
    case 0x41:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_ADD);
      break;
    case 0x42:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_ADD);
      break;
    case 0x44:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_TRUE3);
      break;
    case 0x45:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_TRUE3);
      break;
    case 0x46:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_TRUE3);
      break;
	  case 0x47:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_ALWAYS3);
      break;
    case 0x48:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_FALSE3);
      break;
    case 0x49:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_FALSE3);
      break;
    case 0x4a:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_FALSE3);
      break;
    case 0x4c:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_LOWER_S3);
      break;
    case 0x4d:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_LOWER_S3);
      break;
    case 0x4e:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_LOWER_S3);
      break;
    case 0x50:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_HIGHER_S3);
      break;
    case 0x51:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_HIGHER_S3);
      break;
    case 0x52:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_HIGHER_S3);
      break;
    case 0x54:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_LOWER_U3);
      break;
    case 0x55:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_LOWER_U3);
      break;
    case 0x56:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_LOWER_U3);
      break;
    case 0x58:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_HIGHER_U3);
      break;
    case 0x59:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_HIGHER_U3);
      break;
    case 0x5a:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_HIGHER_U3);
      break;
    case 0x5c:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_8_BIT_IF_AND3);
      break;
    case 0x5d:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_IF_AND3);
      break;
    case 0x5e:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_IF_AND3);
      break;
    case 0x63:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_16_BIT_WRITE_IOREGS);
      break;
    case 0xE3:
      cheatsAdd(code, desc, address, addr, value, 257, GSA_32_BIT_WRITE_IOREGS);
      break;
    default:
      cheatsAdd(code, desc, address, address, value, 257, UNKNOWN_CODE);
      break;
    }
  } else {
    int type = (address >> 28) & 15;
    switch(type) {
    case 0:
    case 1:
    case 2:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 256, type);
      break;
    case 3:
	  switch ((address >> 0x10) & 0xFF){
	  case 0x00:
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 256, GSA_GROUP_WRITE);
	    break;
	  case 0x10:
	    cheatsAdd(code, desc, address, value & 0x0FFFFFFF, address & 0xFF, 256, GSA_32_BIT_ADD );
	    break;
	  case 0x20:
	    cheatsAdd(code, desc, address, value & 0x0FFFFFFF, (~(address & 0xFF)+1), 256, GSA_32_BIT_ADD );
	    break;
	  case 0x30:
	    cheatsAdd(code, desc, address, value & 0x0FFFFFFF, address & 0xFFFF, 256, GSA_32_BIT_ADD );
	    break;
	  case 0x40:
	    cheatsAdd(code, desc, address, value & 0x0FFFFFFF, (~(address & 0xFFFF)+1), 256, GSA_32_BIT_ADD );
	    break;
	  case 0x50:
	    cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 256, GSA_32_BIT_ADD2);
	    break;
	  case 0x60:
	    cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 256, GSA_32_BIT_SUB2);
	    break;
      default:
        /* unsupported code */
        cheatsAdd(code, desc, address, address, value, 256,
                  UNKNOWN_CODE);
        break;
      }
      break;
    case 6:
      address <<= 1;
      type = (value >> 24) & 0xFF;
      if(type == 0x00) {
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value & 0xFFFF, 256,
                  GSA_16_BIT_ROM_PATCH);
        break;
      }
      /* unsupported code */
      cheatsAdd(code, desc, address, address, value, 256,
                UNKNOWN_CODE);
      break;
    case 8:
      switch((address >> 20) & 15) {
      case 1:
        cheatsAdd(code, desc, address, address & 0x0F0FFFFF, value, 256,
                  GSA_8_BIT_GS_WRITE);
        break;
      case 2:
        cheatsAdd(code, desc, address, address & 0x0F0FFFFF, value, 256,
                  GSA_16_BIT_GS_WRITE);
        break;
      case 4:
		/* This code is buggy : the value is always set to 0 ! */
        cheatsAdd(code, desc, address, address & 0x0F0FFFFF, 0, 256,
                  GSA_32_BIT_GS_WRITE);
        break;
      case 15:
        cheatsAdd(code, desc, address, 0, value & 0xFFFF, 256, GSA_SLOWDOWN);
        break;
      default:
        /* unsupported code */
        cheatsAdd(code, desc, address, address, value, 256,
                  UNKNOWN_CODE);
        break;
      }
      break;
    case 0x0d:
      if(address != 0xDEADFACE) {
        switch((value >> 20) & 0xF) {
        case 0:
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value & 0xFFFF, 256,
                  CBA_IF_TRUE);
          break;
        case 1:
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value & 0xFFFF, 256,
                  CBA_IF_FALSE);
          break;
        case 2:
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value & 0xFFFF, 256,
                  GSA_16_BIT_IF_LOWER_OR_EQ_U);
          break;
        case 3:
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value & 0xFFFF, 256,
                  GSA_16_BIT_IF_HIGHER_OR_EQ_U);
          break;
        default:
        /* unsupported code */
        cheatsAdd(code, desc, address, address, value, 256,
                  UNKNOWN_CODE);
          break;
		}
      } else
        cheatsAdd(code, desc, address, address, value, 256,
                  UNKNOWN_CODE);
      break;
    case 0x0e:
      switch((value >> 28) & 0xF) {
      case 0:
      cheatsAdd(code, desc, address, value & 0x0FFFFFFF, address & 0xFFFF, 256,
                GSA_16_BIT_MIF_TRUE);
        break;
      case 1:
      cheatsAdd(code, desc, address, value & 0x0FFFFFFF, address & 0xFFFF, 256,
                GSA_16_BIT_MIF_FALSE);
        break;
      case 2:
      cheatsAdd(code, desc, address, value & 0x0FFFFFFF, address & 0xFFFF, 256,
                GSA_16_BIT_MIF_LOWER_OR_EQ_U);
        break;
      case 3:
      cheatsAdd(code, desc, address, value & 0x0FFFFFFF, address & 0xFFFF, 256,
                GSA_16_BIT_MIF_HIGHER_OR_EQ_U);
        break;
      default:
        /* unsupported code */
        cheatsAdd(code, desc, address, address, value, 256,
                  UNKNOWN_CODE);
        break;
      }
      break;
      case 0x0f:
        cheatsAdd(code, desc, address, (address & 0xFFFFFFF), value, 256, MASTER_CODE);
        mastercode = (address & 0xFFFFFFF);
        break;
      default:
      /* unsupported code */
      cheatsAdd(code, desc, address, address, value, 256,
                UNKNOWN_CODE);
      break;
    }
  }
}

static void cheatsCBAReverseArray(uint8_t *array, uint8_t *dest)
{
  dest[0] = array[3];
  dest[1] = array[2];
  dest[2] = array[1];
  dest[3] = array[0];
  dest[4] = array[5];
  dest[5] = array[4];
}

static void chatsCBAScramble(uint8_t *array, int count, uint8_t b)
{
  uint8_t *x = array + (count >> 3);
  uint8_t *y = array + (b >> 3);
  uint32_t z = *x & (1 << (count & 7));
  uint32_t x0 = (*x & (~(1 << (count & 7))));
  uint32_t temp;
  if (z != 0)
    z = 1;
  if ((*y & (1 << (b & 7))) != 0)
    x0 |= (1 << (count & 7));
  *x = x0;
  temp = *y & (~(1 << (b & 7)));
  if (z != 0)
    temp |= (1 << (b & 7));
  *y = temp;
}

static uint32_t cheatsCBAGetValue(uint8_t *array)
{
  return array[0] | array[1]<<8 | array[2] << 16 | array[3]<<24;
}

static uint16_t cheatsCBAGetData(uint8_t *array)
{
  return array[4] | array[5]<<8;
}

static void cheatsCBAArrayToValue(uint8_t *array, uint8_t *dest)
{
  dest[0] = array[3];
  dest[1] = array[2];
  dest[2] = array[1];
  dest[3] = array[0];
  dest[4] = array[5];
  dest[5] = array[4];
}

static void cheatsCBAParseSeedCode(uint32_t address, uint32_t value, uint32_t *array)
{
  array[0] = 1;
  array[1] = value & 0xFF;
  array[2] = (address >> 0x10) & 0xFF;
  array[3] = (value >> 8) & 0xFF;
  array[4] = (address >> 0x18) & 0x0F;
  array[5] = address & 0xFFFF;
  array[6] = address;
  array[7] = value;
}

static uint32_t cheatsCBAEncWorker(void)
{
  uint32_t x = (cheatsCBATemporaryValue * 0x41c64e6d) + 0x3039;
  uint32_t y = (x * 0x41c64e6d) + 0x3039;
  uint32_t z = x >> 0x10;
  x = ((y >> 0x10) & 0x7fff) << 0x0f;
  z = (z << 0x1e) | x;
  x = (y * 0x41c64e6d) + 0x3039;
  cheatsCBATemporaryValue = x;
  return z | ((x >> 0x10) & 0x7fff);
}

#define ROR(v, s) (((v) >> (s)) | (((v) & ((1 << (s))-1)) << (32 - (s))))

static uint32_t cheatsCBACalcIndex(uint32_t x, uint32_t y)
{
  uint32_t x0;
  uint32_t z;
  uint32_t temp;
  if(y != 0)
  {
    if(y == 1)
      x = 0;
    else if(x == y)
      x = 0;
    if(y < 1)
      return x;
    else if(x < y)
      return x;
    x0 = 1;

    while(y < 0x10000000) {
      if(y < x) {
        y = y << 4;
        x0 = x0 << 4;
      } else break;
    }

    while(y < 0x80000000) {
      if(y < x) {
        y = y << 1;
        x0 = x0 << 1;
      } else break;
    }

  loop:
    /* C89: a label must be followed by a statement, not a declaration.
     * The `z = 0;` assignment serves as that statement; the decls are
     * hoisted to the top of the function. */
    z = 0;
    if(x >= y)
      x -= y;
    if(x >= (y >> 1)) {
      x -= (y >> 1);
      z |= ROR(x0, 1);
    }
    if(x >= (y >> 2)) {
      x -= (y >> 2);
      z |= ROR(x0, 2);
    }
    if(x >= (y >> 3)) {
      x -= (y >> 3);
      z |= ROR(x0, 3);
    }

    temp = x0;

    if(x != 0) {
      x0 = x0 >> 4;
      if(x0 != 0) {
        y = y >> 4;
        goto loop;
      }
    }

    z = z & 0xe0000000;

    if(z != 0) {
      if((temp & 7) == 0)
        return x;
    } else
      return x;

    if((z & ROR(temp, 3)) != 0)
      x += y >> 3;
    if((z & ROR(temp, 2)) != 0)
      x += y >> 2;
    if((z & ROR(temp, 1)) != 0)
      x += y >> 1;
    return x;
  }
  /* should not happen in the current code */
  return 0;
}

static void cheatsCBAUpdateSeedBuffer(uint32_t a, uint8_t *buffer, int count)
{
  int i;
  for(i = 0; i < count; i++)
    buffer[i] = i;
  for(i = 0; (uint32_t)i < a; i++) {
    uint32_t a = cheatsCBACalcIndex(cheatsCBAEncWorker(), count);
    uint32_t b = cheatsCBACalcIndex(cheatsCBAEncWorker(), count);
    uint32_t t = buffer[a];
    buffer[a] = buffer[b];
    buffer[b] = t;
  }
}

static void cheatsCBAChangeEncryption(uint32_t *seed)
{
  int i;

  cheatsCBATemporaryValue = (seed[1] ^ 0x1111);
  cheatsCBAUpdateSeedBuffer(0x50, cheatsCBASeedBuffer, 0x30);
  cheatsCBATemporaryValue = 0x4efad1c3;

  for(i = 0; (uint32_t)i < seed[4]; i++)
    cheatsCBATemporaryValue = cheatsCBAEncWorker();
  cheatsCBASeed[2] = cheatsCBAEncWorker();
  cheatsCBASeed[3] = cheatsCBAEncWorker();

  cheatsCBATemporaryValue = seed[3] ^ 0xf254;

  for(i = 0; (uint32_t)i < seed[3]; i++)
    cheatsCBATemporaryValue = cheatsCBAEncWorker();

  cheatsCBASeed[0] = cheatsCBAEncWorker();
  cheatsCBASeed[1] = cheatsCBAEncWorker();

  *((uint32_t *)&cheatsCBACurrentSeed[0]) = seed[6];
  *((uint32_t *)&cheatsCBACurrentSeed[4]) = seed[7];
  *((uint32_t *)&cheatsCBACurrentSeed[8]) = 0;
}

static uint16_t cheatsCBAGenValue(uint32_t x, uint32_t y, uint32_t z)
{
  int i;
  uint32_t x0;
  y <<= 0x10;
  z <<= 0x10;
  x <<= 0x18;
  x0 = (int)y >> 0x10;
  z = (int)z >> 0x10;
  x = (int)x >> 0x10;
  for(i = 0; i < 8; i++) {
    uint32_t temp = z ^ x;
    if ((int)temp >= 0)
      temp = z << 0x11;
    else {
      temp = z << 0x01;
      temp ^= x0;
      temp = temp << 0x10;
    }
    z = (int)temp >> 0x10;
    temp = x << 0x11;
    x = (int)temp >> 0x10;
  }
  return z & 0xffff;
}

static void cheatsCBAGenTable(void)
{
  int i;
  for(i = 0; i < 0x100; i++)
    cheatsCBATable[i] = cheatsCBAGenValue(i, 0x1021, 0);
  cheatsCBATableGenerated = true;
}

static uint16_t cheatsCBACalcCRC(uint8_t *rom, int count)
{
  uint32_t crc = 0xffffffff;

  if (count & 3) {
    /* 0x08000EAE */
  } else {
    count = (count >> 2) - 1;
    if(count != -1) {
      while(count != -1) {
        crc = (((crc << 0x08) ^ cheatsCBATable[(((uint32_t)crc << 0x10) >> 0x18)
                                               ^ *rom++]) << 0x10) >> 0x10;
        crc = (((crc << 0x08) ^ cheatsCBATable[(((uint32_t)crc << 0x10) >> 0x18)
                                               ^ *rom++]) << 0x10) >> 0x10;
        crc = (((crc << 0x08) ^ cheatsCBATable[(((uint32_t)crc << 0x10) >> 0x18)
                                               ^ *rom++]) << 0x10) >> 0x10;
        crc = (((crc << 0x08) ^ cheatsCBATable[(((uint32_t)crc << 0x10) >> 0x18)
                                               ^ *rom++]) << 0x10) >> 0x10;
        count--;
      }
    }
  }
  return crc & 0xffff;
}

static void cheatsCBADecrypt(uint8_t *decrypt)
{
  int count, i, j;
  uint8_t buffer[8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
  uint8_t *array = &buffer[1];
  uint32_t cs;

  cheatsCBAReverseArray(decrypt, array);

  for(count = 0x2f; count >= 0; count--)
    chatsCBAScramble(array, count, cheatsCBASeedBuffer[count]);
  cheatsCBAArrayToValue(array, decrypt);
  *((uint32_t *)decrypt) = cheatsCBAGetValue(decrypt) ^
    cheatsCBASeed[0];
  *((uint16_t *)(decrypt+4)) = (cheatsCBAGetData(decrypt) ^
                           cheatsCBASeed[1]) & 0xffff;

  cheatsCBAReverseArray(decrypt, array);

  cs = cheatsCBAGetValue(cheatsCBACurrentSeed);
  for(i = 0; i <= 4; i++)
    array[i] = ((cs >> 8) ^ array[i+1]) ^ array[i] ;

  array[5] = (cs >> 8) ^ array[5];

  for(j = 5; j >=0; j--)
    array[j] = (cs ^ array[j-1]) ^ array[j];

  cheatsCBAArrayToValue(array, decrypt);

  *((uint32_t *)decrypt) = cheatsCBAGetValue(decrypt)
    ^ cheatsCBASeed[2];
  *((uint16_t *)(decrypt+4)) = (cheatsCBAGetData(decrypt)
                           ^ cheatsCBASeed[3]) & 0xffff;
}

static int cheatsCBAGetCount(void)
{
  int i;
  int count = 0;
  for(i = 0; i < cheatsNumber; i++)
  {
    if(cheatsList[i].code == 512)
      count++;
  }
  return count;
}

static bool cheatsCBAShouldDecrypt(void)
{
  int i;
  for(i = 0; i < cheatsNumber; i++)
  {
    if(cheatsList[i].code == 512)
      return (cheatsList[i].codestring[0] == '9');
  }
  return false;
}

void cheatsAddCBACode(const char *code, const char *desc)
{
  int i;
  char buffer[10];
  uint32_t address;
  uint32_t value;
  uint8_t array[8];
  if(strlen(code) != 13) {
    /* wrong cheat */
    systemMessage("Invalid CBA code. Format is XXXXXXXX YYYY.");
    return;
  }

  for(i = 0; i < 8; i++) {
    if(!CHEAT_IS_HEX(code[i])) {
      /* wrong cheat */
      systemMessage("Invalid CBA code. Format is XXXXXXXX YYYY.");
      return;
    }
  }

  if(code[8] != ' ') {
    systemMessage("Invalid CBA code. Format is XXXXXXXX YYYY.");
    return;
  }

  for(i = 9; i < 13; i++) {
    if(!CHEAT_IS_HEX(code[i])) {
      /* wrong cheat */
      systemMessage("Invalid CBA code. Format is XXXXXXXX YYYY.");
      return;
    }
  }

  strncpy(buffer, code, 8);
  buffer[8] = 0;
  sscanf(buffer, "%x", &address);
  strncpy(buffer, &code[9], 4);
  buffer[4] = 0;
  sscanf(buffer, "%x", &value);

  array[0] = (uint8_t)(address & 255);
  array[1] = (uint8_t)((address >> 8) & 255);
  array[2] = (uint8_t)((address >> 16) & 255);
  array[3] = (uint8_t)((address >> 24) & 255);
  array[4] = (uint8_t)(value & 255);
  array[5] = (uint8_t)((value >> 8) & 255);
  array[6] = 0;
  array[7] = 0;

  if(cheatsCBAGetCount() == 0 &&
     (address >> 28) == 9) {
    uint32_t seed[8];
    cheatsCBAParseSeedCode(address, value, seed);
    cheatsCBAChangeEncryption(seed);
    cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 512, UNKNOWN_CODE);
  } else {
    int type;
    if(cheatsCBAShouldDecrypt())
      cheatsCBADecrypt(array);

    address = READ32LE(((uint32_t *)array));
    value = READ16LE(((uint16_t *)&array[4]));

    type = (address >> 28) & 15;

    if(isMultilineWithData(cheatsNumber-1) || (cba_super_count>0)) {
      cheatsAdd(code, desc, address, address, value, 512, UNKNOWN_CODE);
	  if (cba_super_count>0)
		  cba_super_count-= 1;
      return;
    }

    switch(type) {
    case 0x00:
      {
        uint32_t crc;
        if(!cheatsCBATableGenerated)
          cheatsCBAGenTable();
        crc = cheatsCBACalcCRC(rom, 0x10000);
        if(crc != address) {
          systemMessage("Warning: Codes seem to be for a different game.\nCodes may not work correctly.");
        }
        cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 512,
                  UNKNOWN_CODE);
      }
      break;
    case 0x01:
      cheatsAdd(code, desc, address, (address & 0x1FFFFFF) | 0x08000000, value, 512, MASTER_CODE);
      mastercode = (address & 0x1FFFFFF) | 0x08000000;
      break;
    case 0x02:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_OR);
      break;
    case 0x03:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value, 512,
                INT_8_BIT_WRITE);
      break;
    case 0x04:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_SLIDE_CODE);
      break;
    case 0x05:
		cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                  CBA_SUPER);
		cba_super_count = getCodeLength(cheatsNumber-1);
      break;
    case 0x06:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_AND);
      break;
    case 0x07:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_IF_TRUE);
      break;
    case 0x08:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                INT_16_BIT_WRITE);
      break;
    case 0x0a:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_IF_FALSE);
      break;
    case 0x0b:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_GT);
      break;
    case 0x0c:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                CBA_LT);
      break;
    case 0x0d:
      if ((address & 0xF0)<0x30) {
        cheatsAdd(code, desc, address, address & 0xF0, value, 512,
                  CBA_IF_KEYS_PRESSED);
      }
      break;
    case 0x0e:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFF, value & 0x8000 ? value | 0xFFFF0000 : value, 512,
                CBA_ADD);
      break;
    case 0x0f:
      cheatsAdd(code, desc, address, address & 0x0FFFFFFE, value, 512,
                GSA_16_BIT_IF_AND);
      break;
    default:
      /* unsupported code */
      cheatsAdd(code, desc, address, address & 0xFFFFFFFF, value, 512,
                UNKNOWN_CODE);
      break;
    }
  }
}
