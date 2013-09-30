#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stddef.h>

#include "system.h"
#include "globals.h"

#ifdef __CELLOS_LV2__
#include <ppu_intrinsics.h>
#endif

#include "port.h"
#include "gba.h"
#include "memory.h"
#include "sound.h" 

#ifdef ELF
#include "elf.h"
#endif

/*============================================================
	GBA INLINE
============================================================ */

#define UPDATE_REG(address, value)	WRITE16LE(((u16 *)&ioMem[address]),value);
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
 
#ifdef USE_SWITICKS
extern int SWITicks;
#endif
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

static int coeff[32] = {0,1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 
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

static uint16_t io_registers[1024 * 16];

static u16 MOSAIC;

static uint16_t BG2X_L   = 0x0000;
static uint16_t BG2X_H   = 0x0000;
static uint16_t BG2Y_L   = 0x0000;
static uint16_t BG2Y_H   = 0x0000;
static uint16_t BG3X_L   = 0x0000;
static uint16_t BG3X_H   = 0x0000;
static uint16_t BG3Y_L   = 0x0000;
static uint16_t BG3Y_H   = 0x0000;
static uint16_t BLDMOD   = 0x0000;
static uint16_t COLEV    = 0x0000;
static uint16_t COLY     = 0x0000;
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

static int cpuDmaTicksToUpdate = 0;

static const uint32_t TIMER_TICKS[4] = {0, 6, 8, 10};

static const uint8_t gamepakRamWaitState[4] = { 4, 3, 2, 8 };

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
static int gbaSaveType = 0; // used to remember the save type on reset

//static int gfxLastVCOUNT = 0;

// Waitstates when accessing data

#define DATATICKS_ACCESS_BUS_PREFETCH(address, value) \
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
	}

/* Waitstates when accessing data */

#define DATATICKS_ACCESS_32BIT(address)  (memoryWait32[(address >> 24) & 15])
#define DATATICKS_ACCESS_32BIT_SEQ(address) (memoryWaitSeq32[(address >> 24) & 15])
#define DATATICKS_ACCESS_16BIT(address) (memoryWait[(address >> 24) & 15])
#define DATATICKS_ACCESS_16BIT_SEQ(address) (memoryWaitSeq[(address >> 24) & 15])

// Waitstates when executing opcode
static INLINE int codeTicksAccess(u32 address, u8 bit32) // THUMB NON SEQ
{
	int addr, ret;

	addr = (address>>24) & 15;

	if (unsigned(addr - 0x08) <= 5)
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
		ret = memoryWait32[addr];
	else			/* THUMB NON SEQ */
		ret = memoryWait[addr];

	return ret;
}

static INLINE int codeTicksAccessSeq16(u32 address) // THUMB SEQ
{
	int addr = (address>>24) & 15;

	if (unsigned(addr - 0x08) <= 5)
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

static INLINE int codeTicksAccessSeq32(u32 address) // ARM SEQ
{
	int addr = (address>>24)&15;

	if (unsigned(addr - 0x08) <= 5)
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
#define CPUReadHalfWordQuick(addr)	READ16LE(((u16*)&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]))
#define CPUReadMemoryQuick(addr)	READ32LE(((u32*)&map[(addr)>>24].address[(addr) & map[(addr)>>24].mask]))

static bool stopState = false;
extern bool cpuSramEnabled;
extern bool cpuFlashEnabled;
extern bool cpuEEPROMEnabled;
#ifdef USE_MOTION_SENSOR
extern bool cpuEEPROMSensorEnabled;
#endif
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

static const uint32_t  objTilesAddress [3] = {0x010000, 0x014000, 0x014000};

static INLINE u32 CPUReadMemory(u32 address)
{
	u32 value;
	switch(address >> 24)
	{
		case 0:
			/* BIOS */
			if(bus.reg[15].I >> 24)
			{
				if(address < 0x4000)
					value = READ32LE(((u32 *)&biosProtected));
				else goto unreadable;
			}
			else
				value = READ32LE(((u32 *)&bios[address & 0x3FFC]));
			break;
		case 0x02:
			/* external work RAM */
			value = READ32LE(((u32 *)&workRAM[address & 0x3FFFC]));
			break;
		case 0x03:
			/* internal work RAM */
			value = READ32LE(((u32 *)&internalRAM[address & 0x7ffC]));
			break;
		case 0x04:
			/* I/O registers */
			if((address < 0x4000400) && ioReadable[address & 0x3fc])
			{
				if(ioReadable[(address & 0x3fc) + 2])
					value = READ32LE(((u32 *)&ioMem[address & 0x3fC]));
				else
					value = READ16LE(((u16 *)&ioMem[address & 0x3fc]));
			}
			else
				goto unreadable;
			break;
		case 0x05:
			/* palette RAM */
			value = READ32LE(((u32 *)&graphics.paletteRAM[address & 0x3fC]));
			break;
		case 0x06:
			/* VRAM */
			address = (address & 0x1fffc);
			if (((io_registers[REG_DISPCNT] & 7) >2) && ((address & 0x1C000) == 0x18000))
			{
				value = 0;
				break;
			}
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;
			value = READ32LE(((u32 *)&vram[address]));
			break;
		case 0x07:
			/* OAM RAM */
			value = READ32LE(((u32 *)&oam[address & 0x3FC]));
			break;
		case 0x08:
		case 0x09:
		case 0x0A:
		case 0x0B: 
		case 0x0C: 
			/* gamepak ROM */
			value = READ32LE(((u32 *)&rom[address&0x1FFFFFC]));
			break;
		case 0x0D:
			if(cpuEEPROMEnabled)
				return eepromRead();	// no need to swap this
			goto unreadable;
		case 14:
			if(cpuFlashEnabled | cpuSramEnabled)
				return flashRead(address);	// no need to swap this
		default:
unreadable:

			if(armState)
				value = CPUReadMemoryQuick(bus.reg[15].I);
			else
			{
				value = CPUReadHalfWordQuick(bus.reg[15].I) |
					CPUReadHalfWordQuick(bus.reg[15].I) << 16;
			}
	}

	if(address & 3) {
		int shift = (address & 3) << 3;
		value = (value >> shift) | (value << (32 - shift));
	}
	return value;
}

static INLINE u32 CPUReadHalfWord(u32 address)
{
	u32 value;

	switch(address >> 24)
	{
		case 0:
			if (bus.reg[15].I >> 24)
			{
				if(address < 0x4000)
					value = READ16LE(((u16 *)&biosProtected[address&2]));
				else
					goto unreadable;
			}
			else
				value = READ16LE(((u16 *)&bios[address & 0x3FFE]));
			break;
		case 2:
			value = READ16LE(((u16 *)&workRAM[address & 0x3FFFE]));
			break;
		case 3:
			value = READ16LE(((u16 *)&internalRAM[address & 0x7ffe]));
			break;
		case 4:
			if((address < 0x4000400) && ioReadable[address & 0x3fe])
			{
				value =  READ16LE(((u16 *)&ioMem[address & 0x3fe]));
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
			value = READ16LE(((u16 *)&graphics.paletteRAM[address & 0x3fe]));
			break;
		case 6:
			address = (address & 0x1fffe);
			if (((io_registers[REG_DISPCNT] & 7) >2) && ((address & 0x1C000) == 0x18000))
			{
				value = 0;
				break;
			}
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;
			value = READ16LE(((u16 *)&vram[address]));
			break;
		case 7:
			value = READ16LE(((u16 *)&oam[address & 0x3fe]));
			break;
		case 8:
		case 9:
		case 10:
		case 11:
		case 12:
			if(address == 0x80000c4 || address == 0x80000c6 || address == 0x80000c8)
				value = rtcRead(address);
			else
				value = READ16LE(((u16 *)&rom[address & 0x1FFFFFE]));
			break;
		case 13:
			if(cpuEEPROMEnabled)
				return  eepromRead();		// no need to swap this
			goto unreadable;
		case 14:
			if(cpuFlashEnabled | cpuSramEnabled)
				return flashRead(address);	// no need to swap this
		default:
unreadable:
			{
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

static INLINE u16 CPUReadHalfWordSigned(u32 address)
{
	u16 value = CPUReadHalfWord(address);
	if((address & 1))
		value = (s8)value;
	return value;
}

static INLINE u8 CPUReadByte(u32 address)
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
			return graphics.paletteRAM[address & 0x3ff];
		case 6:
			address = (address & 0x1ffff);
			if (((io_registers[REG_DISPCNT] & 7) >2) && ((address & 0x1C000) == 0x18000))
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
			if(cpuEEPROMEnabled)
				return eepromRead();
			goto unreadable;
		case 14:
			if(cpuSramEnabled | cpuFlashEnabled)
				return flashRead(address);
#ifdef USE_MOTION_SENSOR
			if(cpuEEPROMSensorEnabled) {
				switch(address & 0x00008f00) {
					case 0x8200:
						return systemGetSensorX() & 255;
					case 0x8300:
						return (systemGetSensorX() >> 8)|0x80;
					case 0x8400:
						return systemGetSensorY() & 255;
					case 0x8500:
						return systemGetSensorY() >> 8;
				}
			}
#endif
		default:
unreadable:
			if(armState)
				return CPUReadByteQuick(bus.reg[15].I+(address & 3));
			else
				return CPUReadByteQuick(bus.reg[15].I+(address & 1));
	}
}

static INLINE void CPUWriteMemory(u32 address, u32 value)
{
	switch(address >> 24)
	{
		case 0x02:
			WRITE32LE(((u32 *)&workRAM[address & 0x3FFFC]), value);
			break;
		case 0x03:
			WRITE32LE(((u32 *)&internalRAM[address & 0x7ffC]), value);
			break;
		case 0x04:
			if(address < 0x4000400)
			{
				CPUUpdateRegister((address & 0x3FC), value & 0xFFFF);
				CPUUpdateRegister((address & 0x3FC) + 2, (value >> 16));
			}
			break;
		case 0x05:
			WRITE32LE(((u32 *)&graphics.paletteRAM[address & 0x3FC]), value);
			break;
		case 0x06:
			address = (address & 0x1fffc);
			if (((io_registers[REG_DISPCNT] & 7) >2) && ((address & 0x1C000) == 0x18000))
				return;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;


			WRITE32LE(((u32 *)&vram[address]), value);
			break;
		case 0x07:
			WRITE32LE(((u32 *)&oam[address & 0x3fc]), value);
			break;
		case 0x0D:
			if(cpuEEPROMEnabled) {
				eepromWrite(value);
				break;
			}
			break;
		case 0x0E:
			if((!eepromInUse) | cpuSramEnabled | cpuFlashEnabled)
				(*cpuSaveGameFunc)(address, (u8)value);
			break;
		default:
			break;
	}
}

static INLINE void CPUWriteHalfWord(u32 address, u16 value)
{
	switch(address >> 24)
	{
		case 2:
			WRITE16LE(((u16 *)&workRAM[address & 0x3FFFE]),value);
			break;
		case 3:
			WRITE16LE(((u16 *)&internalRAM[address & 0x7ffe]), value);
			break;
		case 4:
			if(address < 0x4000400)
				CPUUpdateRegister(address & 0x3fe, value);
			break;
		case 5:
			WRITE16LE(((u16 *)&graphics.paletteRAM[address & 0x3fe]), value);
			break;
		case 6:
			address = (address & 0x1fffe);
			if (((io_registers[REG_DISPCNT] & 7) >2) && ((address & 0x1C000) == 0x18000))
				return;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;
			WRITE16LE(((u16 *)&vram[address]), value);
			break;
		case 7:
			WRITE16LE(((u16 *)&oam[address & 0x3fe]), value);
			break;
		case 8:
		case 9:
			if(address == 0x80000c4 || address == 0x80000c6 || address == 0x80000c8)
				if(!rtcWrite(address, value))
					break;
			break;
		case 13:
			if(cpuEEPROMEnabled)
				eepromWrite((u8)value);
			break;
		case 14:
			if((!eepromInUse) | cpuSramEnabled | cpuFlashEnabled)
				(*cpuSaveGameFunc)(address, (u8)value);
			break;
		default:
			break;
	}
}

static INLINE void CPUWriteByte(u32 address, u8 b)
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
					case 0x301: // HALTCNT, undocumented
						if(b == 0x80)
							stopState = true;
						holdState = 1;
						cpuNextEvent = cpuTotalTicks;
						break;
					default: // every other register
						{
							u32 lowerBits = address & 0x3fe;
							uint16_t param;
							if(address & 1)
								param = (READ16LE(&ioMem[lowerBits]) & 0x00FF) | (b << 8);
							else
								param = (READ16LE(&ioMem[lowerBits]) & 0xFF00) | b;

							CPUUpdateRegister(lowerBits, param);
						}
					break;
				}
			}
			break;
		case 5:
			// no need to switch
			*((u16 *)&graphics.paletteRAM[address & 0x3FE]) = (b << 8) | b;
			break;
		case 6:
			address = (address & 0x1fffe);
			if (((io_registers[REG_DISPCNT] & 7) >2) && ((address & 0x1C000) == 0x18000))
				return;
			if ((address & 0x18000) == 0x18000)
				address &= 0x17fff;

			// no need to switch
			// byte writes to OBJ VRAM are ignored
			if ((address) < objTilesAddress[((io_registers[REG_DISPCNT] & 7)+1)>>2])
				*((u16 *)&vram[address]) = (b << 8) | b;
			break;
		case 7:
			// no need to switch
			// byte writes to OAM are ignored
			//    *((u16 *)&oam[address & 0x3FE]) = (b << 8) | b;
			break;
		case 13:
			if(cpuEEPROMEnabled)
				eepromWrite(b);
			break;
		case 14:
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

s16 sineTable[256] = {
  (s16)0x0000, (s16)0x0192, (s16)0x0323, (s16)0x04B5, (s16)0x0645, (s16)0x07D5, (s16)0x0964, (s16)0x0AF1,
  (s16)0x0C7C, (s16)0x0E05, (s16)0x0F8C, (s16)0x1111, (s16)0x1294, (s16)0x1413, (s16)0x158F, (s16)0x1708,
  (s16)0x187D, (s16)0x19EF, (s16)0x1B5D, (s16)0x1CC6, (s16)0x1E2B, (s16)0x1F8B, (s16)0x20E7, (s16)0x223D,
  (s16)0x238E, (s16)0x24DA, (s16)0x261F, (s16)0x275F, (s16)0x2899, (s16)0x29CD, (s16)0x2AFA, (s16)0x2C21,
  (s16)0x2D41, (s16)0x2E5A, (s16)0x2F6B, (s16)0x3076, (s16)0x3179, (s16)0x3274, (s16)0x3367, (s16)0x3453,
  (s16)0x3536, (s16)0x3612, (s16)0x36E5, (s16)0x37AF, (s16)0x3871, (s16)0x392A, (s16)0x39DA, (s16)0x3A82,
  (s16)0x3B20, (s16)0x3BB6, (s16)0x3C42, (s16)0x3CC5, (s16)0x3D3E, (s16)0x3DAE, (s16)0x3E14, (s16)0x3E71,
  (s16)0x3EC5, (s16)0x3F0E, (s16)0x3F4E, (s16)0x3F84, (s16)0x3FB1, (s16)0x3FD3, (s16)0x3FEC, (s16)0x3FFB,
  (s16)0x4000, (s16)0x3FFB, (s16)0x3FEC, (s16)0x3FD3, (s16)0x3FB1, (s16)0x3F84, (s16)0x3F4E, (s16)0x3F0E,
  (s16)0x3EC5, (s16)0x3E71, (s16)0x3E14, (s16)0x3DAE, (s16)0x3D3E, (s16)0x3CC5, (s16)0x3C42, (s16)0x3BB6,
  (s16)0x3B20, (s16)0x3A82, (s16)0x39DA, (s16)0x392A, (s16)0x3871, (s16)0x37AF, (s16)0x36E5, (s16)0x3612,
  (s16)0x3536, (s16)0x3453, (s16)0x3367, (s16)0x3274, (s16)0x3179, (s16)0x3076, (s16)0x2F6B, (s16)0x2E5A,
  (s16)0x2D41, (s16)0x2C21, (s16)0x2AFA, (s16)0x29CD, (s16)0x2899, (s16)0x275F, (s16)0x261F, (s16)0x24DA,
  (s16)0x238E, (s16)0x223D, (s16)0x20E7, (s16)0x1F8B, (s16)0x1E2B, (s16)0x1CC6, (s16)0x1B5D, (s16)0x19EF,
  (s16)0x187D, (s16)0x1708, (s16)0x158F, (s16)0x1413, (s16)0x1294, (s16)0x1111, (s16)0x0F8C, (s16)0x0E05,
  (s16)0x0C7C, (s16)0x0AF1, (s16)0x0964, (s16)0x07D5, (s16)0x0645, (s16)0x04B5, (s16)0x0323, (s16)0x0192,
  (s16)0x0000, (s16)0xFE6E, (s16)0xFCDD, (s16)0xFB4B, (s16)0xF9BB, (s16)0xF82B, (s16)0xF69C, (s16)0xF50F,
  (s16)0xF384, (s16)0xF1FB, (s16)0xF074, (s16)0xEEEF, (s16)0xED6C, (s16)0xEBED, (s16)0xEA71, (s16)0xE8F8,
  (s16)0xE783, (s16)0xE611, (s16)0xE4A3, (s16)0xE33A, (s16)0xE1D5, (s16)0xE075, (s16)0xDF19, (s16)0xDDC3,
  (s16)0xDC72, (s16)0xDB26, (s16)0xD9E1, (s16)0xD8A1, (s16)0xD767, (s16)0xD633, (s16)0xD506, (s16)0xD3DF,
  (s16)0xD2BF, (s16)0xD1A6, (s16)0xD095, (s16)0xCF8A, (s16)0xCE87, (s16)0xCD8C, (s16)0xCC99, (s16)0xCBAD,
  (s16)0xCACA, (s16)0xC9EE, (s16)0xC91B, (s16)0xC851, (s16)0xC78F, (s16)0xC6D6, (s16)0xC626, (s16)0xC57E,
  (s16)0xC4E0, (s16)0xC44A, (s16)0xC3BE, (s16)0xC33B, (s16)0xC2C2, (s16)0xC252, (s16)0xC1EC, (s16)0xC18F,
  (s16)0xC13B, (s16)0xC0F2, (s16)0xC0B2, (s16)0xC07C, (s16)0xC04F, (s16)0xC02D, (s16)0xC014, (s16)0xC005,
  (s16)0xC000, (s16)0xC005, (s16)0xC014, (s16)0xC02D, (s16)0xC04F, (s16)0xC07C, (s16)0xC0B2, (s16)0xC0F2,
  (s16)0xC13B, (s16)0xC18F, (s16)0xC1EC, (s16)0xC252, (s16)0xC2C2, (s16)0xC33B, (s16)0xC3BE, (s16)0xC44A,
  (s16)0xC4E0, (s16)0xC57E, (s16)0xC626, (s16)0xC6D6, (s16)0xC78F, (s16)0xC851, (s16)0xC91B, (s16)0xC9EE,
  (s16)0xCACA, (s16)0xCBAD, (s16)0xCC99, (s16)0xCD8C, (s16)0xCE87, (s16)0xCF8A, (s16)0xD095, (s16)0xD1A6,
  (s16)0xD2BF, (s16)0xD3DF, (s16)0xD506, (s16)0xD633, (s16)0xD767, (s16)0xD8A1, (s16)0xD9E1, (s16)0xDB26,
  (s16)0xDC72, (s16)0xDDC3, (s16)0xDF19, (s16)0xE075, (s16)0xE1D5, (s16)0xE33A, (s16)0xE4A3, (s16)0xE611,
  (s16)0xE783, (s16)0xE8F8, (s16)0xEA71, (s16)0xEBED, (s16)0xED6C, (s16)0xEEEF, (s16)0xF074, (s16)0xF1FB,
  (s16)0xF384, (s16)0xF50F, (s16)0xF69C, (s16)0xF82B, (s16)0xF9BB, (s16)0xFB4B, (s16)0xFCDD, (s16)0xFE6E
};

static void BIOS_ArcTan (void)
{
	s32 a =  -(((s32)(bus.reg[0].I*bus.reg[0].I)) >> 14);
	s32 b = ((0xA9 * a) >> 14) + 0x390;
	b = ((b * a) >> 14) + 0x91C;
	b = ((b * a) >> 14) + 0xFB6;
	b = ((b * a) >> 14) + 0x16AA;
	b = ((b * a) >> 14) + 0x2081;
	b = ((b * a) >> 14) + 0x3651;
	b = ((b * a) >> 14) + 0xA2F9;
	a = ((s32)bus.reg[0].I * b) >> 16;
	bus.reg[0].I = a;
}

static void BIOS_Div (void)
{
	int number = bus.reg[0].I;
	int denom = bus.reg[1].I;

	if(denom != 0)
	{
		bus.reg[0].I = number / denom;
		bus.reg[1].I = number % denom;
		s32 temp = (s32)bus.reg[0].I;
		bus.reg[3].I = temp < 0 ? (u32)-temp : (u32)temp;
	}
}

static void BIOS_ArcTan2 (void)
{
	s32 x = bus.reg[0].I;
	s32 y = bus.reg[1].I;
	u32 res = 0;
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
}

static void BIOS_BitUnPack (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;
	u32 header = bus.reg[2].I;

	int len = CPUReadHalfWord(header);
	// check address
	if(((source & 0xe000000) == 0) ||
			((source + len) & 0xe000000) == 0)
		return;

	int bits = CPUReadByte(header+2);
	int revbits = 8 - bits;
	// u32 value = 0;
	u32 base = CPUReadMemory(header+4);
	bool addBase = (base & 0x80000000) ? true : false;
	base &= 0x7fffffff;
	int dataSize = CPUReadByte(header+3);

	int data = 0;
	int bitwritecount = 0;
	while(1)
	{
		len -= 1;
		if(len < 0)
			break;
		int mask = 0xff >> revbits;
		u8 b = CPUReadByte(source);
		source++;
		int bitcount = 0;
		while(1) {
			if(bitcount >= 8)
				break;
			u32 d = b & mask;
			u32 temp = d >> bitcount;
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
	u32 src = bus.reg[0].I;
	u32 dest = bus.reg[1].I;
	int num = bus.reg[2].I;

	for(int i = 0; i < num; i++)
	{
		s32 cx = CPUReadMemory(src);
		src+=4;
		s32 cy = CPUReadMemory(src);
		src+=4;
		s16 dispx = CPUReadHalfWord(src);
		src+=2;
		s16 dispy = CPUReadHalfWord(src);
		src+=2;
		s16 rx = CPUReadHalfWord(src);
		src+=2;
		s16 ry = CPUReadHalfWord(src);
		src+=2;
		u16 theta = CPUReadHalfWord(src)>>8;
		src+=4; // keep structure alignment
		s32 a = sineTable[(theta+0x40)&255];
		s32 b = sineTable[theta];

		s16 dx =  (rx * a)>>14;
		s16 dmx = (rx * b)>>14;
		s16 dy =  (ry * b)>>14;
		s16 dmy = (ry * a)>>14;

		CPUWriteHalfWord(dest, dx);
		dest += 2;
		CPUWriteHalfWord(dest, -dmx);
		dest += 2;
		CPUWriteHalfWord(dest, dy);
		dest += 2;
		CPUWriteHalfWord(dest, dmy);
		dest += 2;

		s32 startx = cx - dx * dispx + dmx * dispy;
		s32 starty = cy - dy * dispx - dmy * dispy;

		CPUWriteMemory(dest, startx);
		dest += 4;
		CPUWriteMemory(dest, starty);
		dest += 4;
	}
}

static void BIOS_CpuSet (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;
	u32 cnt = bus.reg[2].I;

	int count = cnt & 0x1FFFFF;

	// 32-bit ?
	if((cnt >> 26) & 1)
	{
		// needed for 32-bit mode!
		source &= 0xFFFFFFFC;
		dest &= 0xFFFFFFFC;
		// fill ?
		if((cnt >> 24) & 1) {
			u32 value = (source>0x0EFFFFFF ? 0x1CAD1CAD : CPUReadMemory(source));
			while(count) {
				CPUWriteMemory(dest, value);
				dest += 4;
				count--;
			}
		} else {
			// copy
			while(count) {
				CPUWriteMemory(dest, (source>0x0EFFFFFF ? 0x1CAD1CAD : CPUReadMemory(source)));
				source += 4;
				dest += 4;
				count--;
			}
		}
	}
	else
	{
		// 16-bit fill?
		if((cnt >> 24) & 1) {
			u16 value = (source>0x0EFFFFFF ? 0x1CAD : CPUReadHalfWord(source));
			while(count) {
				CPUWriteHalfWord(dest, value);
				dest += 2;
				count--;
			}
		} else {
			// copy
			while(count) {
				CPUWriteHalfWord(dest, (source>0x0EFFFFFF ? 0x1CAD : CPUReadHalfWord(source)));
				source += 2;
				dest += 2;
				count--;
			}
		}
	}
}

static void BIOS_CpuFastSet (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;
	u32 cnt = bus.reg[2].I;

	// needed for 32-bit mode!
	source &= 0xFFFFFFFC;
	dest &= 0xFFFFFFFC;

	int count = cnt & 0x1FFFFF;

	// fill?
	if((cnt >> 24) & 1) {
		while(count > 0) {
			// BIOS always transfers 32 bytes at a time
			u32 value = (source>0x0EFFFFFF ? 0xBAFFFFFB : CPUReadMemory(source));
			for(int i = 0; i < 8; i++) {
				CPUWriteMemory(dest, value);
				dest += 4;
			}
			count -= 8;
		}
	} else {
		// copy
		while(count > 0) {
			// BIOS always transfers 32 bytes at a time
			for(int i = 0; i < 8; i++) {
				CPUWriteMemory(dest, (source>0x0EFFFFFF ? 0xBAFFFFFB :CPUReadMemory(source)));
				source += 4;
				dest += 4;
			}
			count -= 8;
		}
	}
}

static void BIOS_Diff8bitUnFilterWram (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
	(((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0))
		return;

	int len = header >> 8;

	u8 data = CPUReadByte(source++);
	CPUWriteByte(dest++, data);
	len--;

	while(len > 0) {
		u8 diff = CPUReadByte(source++);
		data += diff;
		CPUWriteByte(dest++, data);
		len--;
	}
}

static void BIOS_Diff8bitUnFilterVram (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	int len = header >> 8;

	u8 data = CPUReadByte(source++);
	u16 writeData = data;
	int shift = 8;
	int bytes = 1;

	while(len >= 2) {
		u8 diff = CPUReadByte(source++);
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
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	int len = header >> 8;

	u16 data = CPUReadHalfWord(source);
	source += 2;
	CPUWriteHalfWord(dest, data);
	dest += 2;
	len -= 2;

	while(len >= 2) {
		u16 diff = CPUReadHalfWord(source);
		source += 2;
		data += diff;
		CPUWriteHalfWord(dest, data);
		dest += 2;
		len -= 2;
	}
}

static void BIOS_HuffUnComp (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
	((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	u8 treeSize = CPUReadByte(source++);

	u32 treeStart = source;

	source += ((treeSize+1)<<1)-1; // minus because we already skipped one byte

	int len = header >> 8;

	u32 mask = 0x80000000;
	u32 data = CPUReadMemory(source);
	source += 4;

	int pos = 0;
	u8 rootNode = CPUReadByte(treeStart);
	u8 currentNode = rootNode;
	bool writeData = false;
	int byteShift = 0;
	int byteCount = 0;
	u32 writeValue = 0;

	if((header & 0x0F) == 8) {
		while(len > 0) {
			// take left
			if(pos == 0)
				pos++;
			else
				pos += (((currentNode & 0x3F)+1)<<1);

			if(data & mask) {
				// right
				if(currentNode & 0x40)
					writeData = true;
				currentNode = CPUReadByte(treeStart+pos+1);
			} else {
				// left
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
			// take left
			if(pos == 0)
				pos++;
			else
				pos += (((currentNode & 0x3F)+1)<<1);

			if((data & mask)) {
				// right
				if(currentNode & 0x40)
					writeData = true;
				currentNode = CPUReadByte(treeStart+pos+1);
			} else {
				// left
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

	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	int byteCount = 0;
	int byteShift = 0;
	u32 writeValue = 0;

	int len = header >> 8;

	while(len > 0) {
		u8 d = CPUReadByte(source++);

		if(d) {
			for(int i = 0; i < 8; i++) {
				if(d & 0x80) {
					u16 data = CPUReadByte(source++) << 8;
					data |= CPUReadByte(source++);
					int length = (data >> 12) + 3;
					int offset = (data & 0x0FFF);
					u32 windowOffset = dest + byteCount - offset - 1;
					for(int i2 = 0; i2 < length; i2++) {
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
		} else {
			for(int i = 0; i < 8; i++) {
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

static void BIOS_LZ77UnCompWram (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	int len = header >> 8;

	while(len > 0) {
		u8 d = CPUReadByte(source++);

		if(d) {
			for(int i = 0; i < 8; i++) {
				if(d & 0x80) {
					u16 data = CPUReadByte(source++) << 8;
					data |= CPUReadByte(source++);
					int length = (data >> 12) + 3;
					int offset = (data & 0x0FFF);
					u32 windowOffset = dest - offset - 1;
					for(int i2 = 0; i2 < length; i2++) {
						CPUWriteByte(dest++, CPUReadByte(windowOffset++));
						len--;
						if(len == 0)
							return;
					}
				} else {
					CPUWriteByte(dest++, CPUReadByte(source++));
					len--;
					if(len == 0)
						return;
				}
				d <<= 1;
			}
		} else {
			for(int i = 0; i < 8; i++) {
				CPUWriteByte(dest++, CPUReadByte(source++));
				len--;
				if(len == 0)
					return;
			}
		}
	}
}

static void BIOS_ObjAffineSet (void)
{
	u32 src = bus.reg[0].I;
	u32 dest = bus.reg[1].I;
	int num = bus.reg[2].I;
	int offset = bus.reg[3].I;

	for(int i = 0; i < num; i++) {
		s16 rx = CPUReadHalfWord(src);
		src+=2;
		s16 ry = CPUReadHalfWord(src);
		src+=2;
		u16 theta = CPUReadHalfWord(src)>>8;
		src+=4; // keep structure alignment

		s32 a = (s32)sineTable[(theta+0x40)&255];
		s32 b = (s32)sineTable[theta];

		s16 dx =  ((s32)rx * a)>>14;
		s16 dmx = ((s32)rx * b)>>14;
		s16 dy =  ((s32)ry * b)>>14;
		s16 dmy = ((s32)ry * a)>>14;

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

static void BIOS_RegisterRamReset(u32 flags)
{
	// no need to trace here. this is only called directly from GBA.cpp
	// to emulate bios initialization

	CPUUpdateRegister(0x0, 0x80);

	if(flags)
	{
		if(flags & 0x01)
			memset(workRAM, 0, 0x40000);		// clear work RAM

		if(flags & 0x02)
			memset(internalRAM, 0, 0x7e00);		// don't clear 0x7e00-0x7fff, clear internal RAM

		if(flags & 0x04)
			memset(graphics.paletteRAM, 0, 0x400);	// clear palette RAM

		if(flags & 0x08)
			memset(vram, 0, 0x18000);		// clear VRAM

		if(flags & 0x10)
			memset(oam, 0, 0x400);			// clean OAM

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
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source & 0xFFFFFFFC);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	int len = header >> 8;
	int byteCount = 0;
	int byteShift = 0;
	u32 writeValue = 0;

	while(len > 0)
	{
		u8 d = CPUReadByte(source++);
		int l = d & 0x7F;
		if(d & 0x80) {
			u8 data = CPUReadByte(source++);
			l += 3;
			for(int i = 0;i < l; i++) {
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
		} else {
			l++;
			for(int i = 0; i < l; i++) {
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

static void BIOS_RLUnCompWram (void)
{
	u32 source = bus.reg[0].I;
	u32 dest = bus.reg[1].I;

	u32 header = CPUReadMemory(source & 0xFFFFFFFC);
	source += 4;

	if(((source & 0xe000000) == 0) ||
			((source + ((header >> 8) & 0x1fffff)) & 0xe000000) == 0)
		return;

	int len = header >> 8;

	while(len > 0) {
		u8 d = CPUReadByte(source++);
		int l = d & 0x7F;
		if(d & 0x80) {
			u8 data = CPUReadByte(source++);
			l += 3;
			for(int i = 0;i < l; i++) {
				CPUWriteByte(dest++, data);
				len--;
				if(len == 0)
					return;
			}
		} else {
			l++;
			for(int i = 0; i < l; i++) {
				CPUWriteByte(dest++,  CPUReadByte(source++));
				len--;
				if(len == 0)
					return;
			}
		}
	}
}

static void BIOS_SoftReset (void)
{
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
	u8 b = internalRAM[0x7ffa];

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

#define BIOS_SQRT() bus.reg[0].I = (u32)sqrt((double)bus.reg[0].I);

#define BIOS_MIDI_KEY_2_FREQ() \
{ \
	int freq = CPUReadMemory(bus.reg[0].I+4); \
	double tmp; \
	tmp = ((double)(180 - bus.reg[1].I)) - ((double)bus.reg[2].I / 256.f); \
	tmp = pow((double)2.f, tmp / 12.f); \
	bus.reg[0].I = (int)((double)freq / tmp); \
}

#define BIOS_SND_DRIVER_JMP_TABLE_COPY() \
	for(int i = 0; i < 36; i++) \
	{ \
		CPUWriteMemory(bus.reg[0].I, 0x9c); \
		bus.reg[0].I += 4; \
	}



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
#ifdef USE_SWITICKS
				int len = (bus.reg[2].I & 0x1FFFFF) >>1;
				if (!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + len) & 0xe000000) == 0))
				{
					if ((bus.reg[2].I >> 24) & 1)
					{
						if ((bus.reg[2].I >> 26) & 1)
							SWITicks = (7 + memoryWait32[(bus.reg[1].I>>24) & 0xF]) * (len>>1);
						else
							SWITicks = (8 + memoryWait[(bus.reg[1].I>>24) & 0xF]) * (len);
					}
					else
					{
						if ((bus.reg[2].I >> 26) & 1)
							SWITicks = (10 + memoryWait32[(bus.reg[0].I>>24) & 0xF] +
									memoryWait32[(bus.reg[1].I>>24) & 0xF]) * (len>>1);
						else
							SWITicks = (11 + memoryWait[(bus.reg[0].I>>24) & 0xF] +
									memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
					}
				}
#endif
			}
			if(!(((bus.reg[0].I & 0xe000000) == 0) || ((bus.reg[0].I + (((bus.reg[2].I << 11)>>9) & 0x1fffff)) & 0xe000000) == 0))
				BIOS_CpuSet();
			break;
		case 0x0C:
			{
#ifdef USE_SWITICKS
				int len = (bus.reg[2].I & 0x1FFFFF) >>5;
				if (!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + len) & 0xe000000) == 0))
				{
					if ((bus.reg[2].I >> 24) & 1)
						SWITicks = (6 + memoryWait32[(bus.reg[1].I>>24) & 0xF] +
								7 * (memoryWaitSeq32[(bus.reg[1].I>>24) & 0xF] + 1)) * len;
					else
						SWITicks = (9 + memoryWait32[(bus.reg[0].I>>24) & 0xF] +
								memoryWait32[(bus.reg[1].I>>24) & 0xF] +
								7 * (memoryWaitSeq32[(bus.reg[0].I>>24) & 0xF] +
									memoryWaitSeq32[(bus.reg[1].I>>24) & 0xF] + 2)) * len;
				}
#endif
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
#ifdef USE_SWITICKS
				int len = CPUReadHalfWord(bus.reg[2].I);
				if (!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + len) & 0xe000000) == 0))
					SWITicks = (32 + memoryWait[(bus.reg[0].I>>24) & 0xF]) * len;
#endif
			}
			BIOS_BitUnPack();
			break;
		case 0x11:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 8;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (9 + memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_LZ77UnCompWram();
			break;
		case 0x12:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 8;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (19 + memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_LZ77UnCompVram();
			break;
		case 0x13:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 8;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (29 + (memoryWait[(bus.reg[0].I>>24) & 0xF]<<1)) * len;
			}
#endif
			BIOS_HuffUnComp();
			break;
		case 0x14:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 8;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (11 + memoryWait[(bus.reg[0].I>>24) & 0xF] +
							memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_RLUnCompWram();
			break;
		case 0x15:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 9;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (34 + (memoryWait[(bus.reg[0].I>>24) & 0xF] << 1) +
							memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_RLUnCompVram();
			break;
		case 0x16:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 8;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (13 + memoryWait[(bus.reg[0].I>>24) & 0xF] +
							memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_Diff8bitUnFilterWram();
			break;
		case 0x17:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 9;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (39 + (memoryWait[(bus.reg[0].I>>24) & 0xF]<<1) +
							memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_Diff8bitUnFilterVram();
			break;
		case 0x18:
#ifdef USE_SWITICKS
			{
				uint32_t len = CPUReadMemory(bus.reg[0].I) >> 9;
				if(!(((bus.reg[0].I & 0xe000000) == 0) ||
							((bus.reg[0].I + (len & 0x1fffff)) & 0xe000000) == 0))
					SWITicks = (13 + memoryWait[(bus.reg[0].I>>24) & 0xF] +
							memoryWait[(bus.reg[1].I>>24) & 0xF]) * len;
			}
#endif
			BIOS_Diff16bitUnFilter();
			break;
		case 0x19:
			break;
		case 0x1F:
			BIOS_MIDI_KEY_2_FREQ();
			break;
		case 0x2A:
			BIOS_SND_DRIVER_JMP_TABLE_COPY();
			// let it go, because we don't really emulate this function
		default:
			break;
	}
}


/*============================================================
	GBA ARM CORE
============================================================ */

#ifdef _MSC_VER
 // Disable "empty statement" warnings
 #pragma warning(disable: 4390)
 // Visual C's inline assembler treats "offset" as a reserved word, so we
 // tell it otherwise.  If you want to use it, write "OFFSET" in capitals.
 #define offset offset_
#endif

static void armUnknownInsn(u32 opcode)
{
	u32 PC = bus.reg[15].I;
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

// Common macros //////////////////////////////////////////////////////////

#define NEG(i) ((i) >> 31)
#define POS(i) ((~(i)) >> 31)

// The following macros are used for optimization; any not defined for a
// particular compiler/CPU combination default to the C core versions.
//
//    ALU_INIT_C:   Used at the beginning of ALU instructions (AND/EOR/...).
//    (ALU_INIT_NC) Can consist of variable declarations, like the C core,
//                  or the start of a continued assembly block, like the
//                  x86-optimized version.  The _C version is used when the
//                  carry flag from the shift operation is needed (logical
//                  operations that set condition codes, like ANDS); the
//                  _NC version is used when the carry result is ignored.
//    VALUE_XXX: Retrieve the second operand's value for an ALU instruction.
//               The _C and _NC versions are used the same way as ALU_INIT.
//    OP_XXX: ALU operations.  XXX is the instruction name.
//    SETCOND_NONE: Used in multiply instructions in place of SETCOND_MUL
//                  when the condition codes are not set.  Usually empty.
//    SETCOND_MUL: Used in multiply instructions to set the condition codes.
//    ROR_IMM_MSR: Used to rotate the immediate operand for MSR.
//    ROR_OFFSET: Used to rotate the `offset' parameter for LDR and STR
//                instructions.
//    RRX_OFFSET: Used to rotate (RRX) the `offset' parameter for LDR and
//                STR instructions.

// C core

#define C_SETCOND_LOGICAL \
    N_FLAG = ((s32)res < 0) ? true : false;             \
    Z_FLAG = (res == 0) ? true : false;                 \
    C_FLAG = C_OUT;
#define C_SETCOND_ADD \
    N_FLAG = ((s32)res < 0) ? true : false;             \
    Z_FLAG = (res == 0) ? true : false;                 \
    V_FLAG = ((NEG(lhs) & NEG(rhs) & POS(res)) |        \
              (POS(lhs) & POS(rhs) & NEG(res))) ? true : false;\
    C_FLAG = ((NEG(lhs) & NEG(rhs)) |                   \
              (NEG(lhs) & POS(res)) |                   \
              (NEG(rhs) & POS(res))) ? true : false;
#define C_SETCOND_SUB \
    N_FLAG = ((s32)res < 0) ? true : false;             \
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
    u32 value;
#endif
// OP Rd,Rb,Rm LSL #
#ifndef VALUE_LSL_IMM_C
 #define VALUE_LSL_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (!shift) {  /* LSL #0 most common? */    \
        value = bus.reg[opcode & 0x0F].I;                   \
    } else {                                            \
        u32 v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (32 - shift)) & 1 ? true : false; \
        value = v << shift;                             \
    }
#endif
// OP Rd,Rb,Rm LSL Rs
#ifndef VALUE_LSL_REG_C
 #define VALUE_LSL_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8)&15].B.B0;    \
    if (shift) {                                \
        if (shift == 32) {                              \
            value = 0;                                  \
            C_OUT = (bus.reg[opcode & 0x0F].I & 1 ? true : false);\
        } else if (shift < 32) {                \
            u32 v = bus.reg[opcode & 0x0F].I;               \
            C_OUT = (v >> (32 - shift)) & 1 ? true : false;\
            value = v << shift;                         \
        } else {                                        \
            value = 0;                                  \
            C_OUT = false;                              \
        }                                               \
    } else {                                            \
        value = bus.reg[opcode & 0x0F].I;                   \
    }
#endif
// OP Rd,Rb,Rm LSR #
#ifndef VALUE_LSR_IMM_C
 #define VALUE_LSR_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (shift) {                                \
        u32 v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = v >> shift;                             \
    } else {                                            \
        value = 0;                                      \
        C_OUT = (bus.reg[opcode & 0x0F].I & 0x80000000) ? true : false;\
    }
#endif
// OP Rd,Rb,Rm LSR Rs
#ifndef VALUE_LSR_REG_C
 #define VALUE_LSR_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8)&15].B.B0;    \
    if (shift) {                                \
        if (shift == 32) {                              \
            value = 0;                                  \
            C_OUT = (bus.reg[opcode & 0x0F].I & 0x80000000 ? true : false);\
        } else if (shift < 32) {                \
            u32 v = bus.reg[opcode & 0x0F].I;               \
            C_OUT = (v >> (shift - 1)) & 1 ? true : false;\
            value = v >> shift;                         \
        } else {                                        \
            value = 0;                                  \
            C_OUT = false;                              \
        }                                               \
    } else {                                            \
        value = bus.reg[opcode & 0x0F].I;                   \
    }
#endif
// OP Rd,Rb,Rm ASR #
#ifndef VALUE_ASR_IMM_C
 #define VALUE_ASR_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (shift) {                                \
        s32 v = bus.reg[opcode & 0x0F].I;                   \
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
// OP Rd,Rb,Rm ASR Rs
#ifndef VALUE_ASR_REG_C
 #define VALUE_ASR_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8)&15].B.B0;    \
    if (shift < 32) {                           \
        if (shift) {                            \
            s32 v = bus.reg[opcode & 0x0F].I;               \
            C_OUT = (v >> (int)(shift - 1)) & 1 ? true : false;\
            value = v >> (int)shift;                    \
        } else {                                        \
            value = bus.reg[opcode & 0x0F].I;               \
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
// OP Rd,Rb,Rm ROR #
#ifndef VALUE_ROR_IMM_C
 #define VALUE_ROR_IMM_C \
    unsigned int shift = (opcode >> 7) & 0x1F;          \
    if (shift) {                                \
        u32 v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = ((v << (32 - shift)) |                  \
                 (v >> shift));                         \
    } else {                                            \
        u32 v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v & 1) ? true : false;                 \
        value = ((v >> 1) |                             \
                 (C_FLAG << 31));                       \
    }
#endif
// OP Rd,Rb,Rm ROR Rs
#ifndef VALUE_ROR_REG_C
 #define VALUE_ROR_REG_C \
    unsigned int shift = bus.reg[(opcode >> 8)&15].B.B0;    \
    if (shift & 0x1F) {                         \
        u32 v = bus.reg[opcode & 0x0F].I;                   \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = ((v << (32 - shift)) |                  \
                 (v >> shift));                         \
    } else {                                            \
        value = bus.reg[opcode & 0x0F].I;                   \
        if (shift)                                      \
            C_OUT = (value & 0x80000000 ? true : false);\
    }
#endif
// OP Rd,Rb,# ROR #
#ifndef VALUE_IMM_C
 #define VALUE_IMM_C \
    int shift = (opcode & 0xF00) >> 7;                  \
    if (shift) {                              \
        u32 v = opcode & 0xFF;                          \
        C_OUT = (v >> (shift - 1)) & 1 ? true : false;  \
        value = ((v << (32 - shift)) |                  \
                 (v >> shift));                         \
    } else {                                            \
        value = opcode & 0xFF;                          \
    }
#endif

// Make the non-carry versions default to the carry versions
// (this is fine for C--the compiler will optimize the dead code out)
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
    u32 res = bus.reg[(opcode>>16)&15].I & value;           \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ANDS
 #define OP_ANDS   OP_AND C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_EOR
 #define OP_EOR \
    u32 res = bus.reg[(opcode>>16)&15].I ^ value;           \
    bus.reg[dest].I = res;
#endif
#ifndef OP_EORS
 #define OP_EORS   OP_EOR C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_SUB
 #define OP_SUB \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = lhs - rhs;                                \
    bus.reg[dest].I = res;
#endif
#ifndef OP_SUBS
 #define OP_SUBS   OP_SUB C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_RSB
 #define OP_RSB \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = rhs - lhs;                                \
    bus.reg[dest].I = res;
#endif
#ifndef OP_RSBS
 #define OP_RSBS   OP_RSB C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_ADD
 #define OP_ADD \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = lhs + rhs;                                \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ADDS
 #define OP_ADDS   OP_ADD C_CHECK_PC(C_SETCOND_ADD)
#endif
#ifndef OP_ADC
 #define OP_ADC \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = lhs + rhs + (u32)C_FLAG;                  \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ADCS
 #define OP_ADCS   OP_ADC C_CHECK_PC(C_SETCOND_ADD)
#endif
#ifndef OP_SBC
 #define OP_SBC \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = lhs - rhs - !((u32)C_FLAG);               \
    bus.reg[dest].I = res;
#endif
#ifndef OP_SBCS
 #define OP_SBCS   OP_SBC C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_RSC
 #define OP_RSC \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = rhs - lhs - !((u32)C_FLAG);               \
    bus.reg[dest].I = res;
#endif
#ifndef OP_RSCS
 #define OP_RSCS   OP_RSC C_CHECK_PC(C_SETCOND_SUB)
#endif
#ifndef OP_TST
 #define OP_TST \
    u32 res = bus.reg[(opcode >> 16) & 0x0F].I & value;     \
    C_SETCOND_LOGICAL;
#endif
#ifndef OP_TEQ
 #define OP_TEQ \
    u32 res = bus.reg[(opcode >> 16) & 0x0F].I ^ value;     \
    C_SETCOND_LOGICAL;
#endif
#ifndef OP_CMP
 #define OP_CMP \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = lhs - rhs;                                \
    C_SETCOND_SUB;
#endif
#ifndef OP_CMN
 #define OP_CMN \
    u32 lhs = bus.reg[(opcode>>16)&15].I;                   \
    u32 rhs = value;                                    \
    u32 res = lhs + rhs;                                \
    C_SETCOND_ADD;
#endif
#ifndef OP_ORR
 #define OP_ORR \
    u32 res = bus.reg[(opcode >> 16) & 0x0F].I | value;     \
    bus.reg[dest].I = res;
#endif
#ifndef OP_ORRS
 #define OP_ORRS   OP_ORR C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_MOV
 #define OP_MOV \
    u32 res = value;                                    \
    bus.reg[dest].I = res;
#endif
#ifndef OP_MOVS
 #define OP_MOVS   OP_MOV C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_BIC
 #define OP_BIC \
    u32 res = bus.reg[(opcode >> 16) & 0x0F].I & (~value);  \
    bus.reg[dest].I = res;
#endif
#ifndef OP_BICS
 #define OP_BICS   OP_BIC C_CHECK_PC(C_SETCOND_LOGICAL)
#endif
#ifndef OP_MVN
 #define OP_MVN \
    u32 res = ~value;                                   \
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
     N_FLAG = ((s32)bus.reg[dest].I < 0) ? true : false;    \
     Z_FLAG = bus.reg[dest].I ? false : true;
#endif
#ifndef SETCOND_MULL
 #define SETCOND_MULL \
     N_FLAG = (bus.reg[dest].I & 0x80000000) ? true : false;\
     Z_FLAG = bus.reg[dest].I || bus.reg[acc].I ? false : true;
#endif

#ifndef ROR_IMM_MSR
 #define ROR_IMM_MSR \
    u32 v = opcode & 0xff;                              \
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

// ALU ops (except multiply) //////////////////////////////////////////////

// ALU_INIT: init code (ALU_INIT_C or ALU_INIT_NC)
// GETVALUE: load value and shift/rotate (VALUE_XXX)
// OP: ALU operation (OP_XXX)
// MODECHANGE: MODECHANGE_NO or MODECHANGE_YES
// ISREGSHIFT: 1 for insns of the form ...,Rn LSL/etc Rs; 0 otherwise
// ALU_INIT, GETVALUE and OP are concatenated in order.
#define ALU_INSN(ALU_INIT, GETVALUE, OP, MODECHANGE, ISREGSHIFT) \
    ALU_INIT GETVALUE OP;                            \
    if ((opcode & 0x0000F000) != 0x0000F000) {          \
        clockTicks = 1 + ISREGSHIFT                             \
                       + codeTicksAccessSeq32(bus.armNextPC);       \
    } else {                                                    \
        MODECHANGE;                                             \
        if (armState) {                                         \
            bus.reg[15].I &= 0xFFFFFFFC;                            \
            bus.armNextPC = bus.reg[15].I;                              \
            bus.reg[15].I += 4;                                     \
            ARM_PREFETCH;                                       \
        } else {                                                \
            bus.reg[15].I &= 0xFFFFFFFE;                            \
            bus.armNextPC = bus.reg[15].I;                              \
            bus.reg[15].I += 2;                                     \
            THUMB_PREFETCH;                                     \
        }                                                       \
        clockTicks = 3 + ISREGSHIFT                             \
                       + codeTicksAccess(bus.armNextPC, BITS_32)           \
                       + ((codeTicksAccessSeq32(bus.armNextPC)) << 1);       \
    }

#define MODECHANGE_NO  /*nothing*/
#define MODECHANGE_YES if(armMode != (bus.reg[17].I & 0x1f)) CPUSwitchMode(bus.reg[17].I & 0x1f, false, true);

#define DEFINE_ALU_INSN_C(CODE1, CODE2, OP, MODECHANGE) \
  static  void arm##CODE1##0(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSL_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##1(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSL_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##2(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSR_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##3(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_LSR_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##4(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_ASR_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##5(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_ASR_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##6(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_ROR_IMM_C, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##7(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_ROR_REG_C, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE2##0(u32 opcode) { ALU_INSN(ALU_INIT_C, VALUE_IMM_C,     OP_##OP, MODECHANGE_##MODECHANGE, 0); }
#define DEFINE_ALU_INSN_NC(CODE1, CODE2, OP, MODECHANGE) \
  static  void arm##CODE1##0(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSL_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##1(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSL_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##2(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSR_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##3(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_LSR_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##4(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ASR_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##5(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ASR_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE1##6(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ROR_IMM_NC, OP_##OP, MODECHANGE_##MODECHANGE, 0); }\
  static  void arm##CODE1##7(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_ROR_REG_NC, OP_##OP, MODECHANGE_##MODECHANGE, 1); }\
  static  void arm##CODE2##0(u32 opcode) { ALU_INSN(ALU_INIT_NC, VALUE_IMM_NC,     OP_##OP, MODECHANGE_##MODECHANGE, 0); }

// AND
DEFINE_ALU_INSN_NC(00, 20, AND,  NO)
// ANDS
DEFINE_ALU_INSN_C (01, 21, ANDS, YES)

// EOR
DEFINE_ALU_INSN_NC(02, 22, EOR,  NO)
// EORS
DEFINE_ALU_INSN_C (03, 23, EORS, YES)

// SUB
DEFINE_ALU_INSN_NC(04, 24, SUB,  NO)
// SUBS
DEFINE_ALU_INSN_NC(05, 25, SUBS, YES)

// RSB
DEFINE_ALU_INSN_NC(06, 26, RSB,  NO)
// RSBS
DEFINE_ALU_INSN_NC(07, 27, RSBS, YES)

// ADD
DEFINE_ALU_INSN_NC(08, 28, ADD,  NO)
// ADDS
DEFINE_ALU_INSN_NC(09, 29, ADDS, YES)

// ADC
DEFINE_ALU_INSN_NC(0A, 2A, ADC,  NO)
// ADCS
DEFINE_ALU_INSN_NC(0B, 2B, ADCS, YES)

// SBC
DEFINE_ALU_INSN_NC(0C, 2C, SBC,  NO)
// SBCS
DEFINE_ALU_INSN_NC(0D, 2D, SBCS, YES)

// RSC
DEFINE_ALU_INSN_NC(0E, 2E, RSC,  NO)
// RSCS
DEFINE_ALU_INSN_NC(0F, 2F, RSCS, YES)

// TST
DEFINE_ALU_INSN_C (11, 31, TST,  NO)

// TEQ
DEFINE_ALU_INSN_C (13, 33, TEQ,  NO)

// CMP
DEFINE_ALU_INSN_NC(15, 35, CMP,  NO)

// CMN
DEFINE_ALU_INSN_NC(17, 37, CMN,  NO)

// ORR
DEFINE_ALU_INSN_NC(18, 38, ORR,  NO)
// ORRS
DEFINE_ALU_INSN_C (19, 39, ORRS, YES)

// MOV
DEFINE_ALU_INSN_NC(1A, 3A, MOV,  NO)
// MOVS
DEFINE_ALU_INSN_C (1B, 3B, MOVS, YES)

// BIC
DEFINE_ALU_INSN_NC(1C, 3C, BIC,  NO)
// BICS
DEFINE_ALU_INSN_C (1D, 3D, BICS, YES)

// MVN
DEFINE_ALU_INSN_NC(1E, 3E, MVN,  NO)
// MVNS
DEFINE_ALU_INSN_C (1F, 3F, MVNS, YES)

// Multiply instructions //////////////////////////////////////////////////

// OP: OP_MUL, OP_MLA etc.
// SETCOND: SETCOND_NONE, SETCOND_MUL, or SETCOND_MULL
// CYCLES: base cycle count (1, 2, or 3)
#define MUL_INSN(OP, SETCOND, CYCLES) \
    int mult = (opcode & 0x0F);                         \
    u32 rs = bus.reg[(opcode >> 8) & 0x0F].I;               \
    int acc = (opcode >> 12) & 0x0F;   /* or destLo */  \
    int dest = (opcode >> 16) & 0x0F;  /* or destHi */  \
    OP;                                                 \
    SETCOND;                                            \
    if ((s32)rs < 0)                                    \
        rs = ~rs;                                       \
    if ((rs & 0xFFFF0000) == 0)                         \
        clockTicks += 1;                                \
    else if ((rs & 0xFF000000) == 0)                    \
        clockTicks += 2;                                \
    else                                                \
        clockTicks += 3;                                \
    if (bus.busPrefetchCount == 0)                          \
        bus.busPrefetchCount = ((bus.busPrefetchCount+1)<<clockTicks) - 1; \
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);

#define OP_MUL \
    bus.reg[dest].I = bus.reg[mult].I * rs;
#define OP_MLA \
    bus.reg[dest].I = bus.reg[mult].I * rs + bus.reg[acc].I;
#define OP_MULL(SIGN) \
    SIGN##64 res = (SIGN##64)(SIGN##32)bus.reg[mult].I      \
                 * (SIGN##64)(SIGN##32)rs;              \
    bus.reg[acc].I = (u32)res;                              \
    bus.reg[dest].I = (u32)(res >> 32);
#define OP_MLAL(SIGN) \
    SIGN##64 res = ((SIGN##64)bus.reg[dest].I<<32 | bus.reg[acc].I)\
                 + ((SIGN##64)(SIGN##32)bus.reg[mult].I     \
                    * (SIGN##64)(SIGN##32)rs);          \
    bus.reg[acc].I = (u32)res;                              \
    bus.reg[dest].I = (u32)(res >> 32);
#define OP_UMULL OP_MULL(u)
#define OP_UMLAL OP_MLAL(u)
#define OP_SMULL OP_MULL(s)
#define OP_SMLAL OP_MLAL(s)

// MUL Rd, Rm, Rs
static  void arm009(u32 opcode) { MUL_INSN(OP_MUL, SETCOND_NONE, 1); }
// MULS Rd, Rm, Rs
static  void arm019(u32 opcode) { MUL_INSN(OP_MUL, SETCOND_MUL, 1); }

// MLA Rd, Rm, Rs, Rn
static  void arm029(u32 opcode) { MUL_INSN(OP_MLA, SETCOND_NONE, 2); }
// MLAS Rd, Rm, Rs, Rn
static  void arm039(u32 opcode) { MUL_INSN(OP_MLA, SETCOND_MUL, 2); }

// UMULL RdLo, RdHi, Rn, Rs
static  void arm089(u32 opcode) { MUL_INSN(OP_UMULL, SETCOND_NONE, 2); }
// UMULLS RdLo, RdHi, Rn, Rs
static  void arm099(u32 opcode) { MUL_INSN(OP_UMULL, SETCOND_MULL, 2); }

// UMLAL RdLo, RdHi, Rn, Rs
static  void arm0A9(u32 opcode) { MUL_INSN(OP_UMLAL, SETCOND_NONE, 3); }
// UMLALS RdLo, RdHi, Rn, Rs
static  void arm0B9(u32 opcode) { MUL_INSN(OP_UMLAL, SETCOND_MULL, 3); }

// SMULL RdLo, RdHi, Rm, Rs
static  void arm0C9(u32 opcode) { MUL_INSN(OP_SMULL, SETCOND_NONE, 2); }
// SMULLS RdLo, RdHi, Rm, Rs
static  void arm0D9(u32 opcode) { MUL_INSN(OP_SMULL, SETCOND_MULL, 2); }

// SMLAL RdLo, RdHi, Rm, Rs
static  void arm0E9(u32 opcode) { MUL_INSN(OP_SMLAL, SETCOND_NONE, 3); }
// SMLALS RdLo, RdHi, Rm, Rs
static  void arm0F9(u32 opcode) { MUL_INSN(OP_SMLAL, SETCOND_MULL, 3); }

// Misc instructions //////////////////////////////////////////////////////

// SWP Rd, Rm, [Rn]
static  void arm109(u32 opcode)
{
	u32 address = bus.reg[(opcode >> 16) & 15].I;
	u32 temp = CPUReadMemory(address);
	CPUWriteMemory(address, bus.reg[opcode&15].I);
	bus.reg[(opcode >> 12) & 15].I = temp;
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 4 + (dataticks_value << 1) + codeTicksAccess(bus.armNextPC, BITS_32);
}

// SWPB Rd, Rm, [Rn]
static  void arm149(u32 opcode)
{
	u32 address = bus.reg[(opcode >> 16) & 15].I;
	u32 temp = CPUReadByte(address);
	CPUWriteByte(address, bus.reg[opcode&15].B.B0);
	bus.reg[(opcode>>12)&15].I = temp;
	u32 dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 4 + (dataticks_value << 1) + codeTicksAccess(bus.armNextPC, BITS_32);
}

// MRS Rd, CPSR
static  void arm100(u32 opcode)
{
	if ((opcode & 0x0FFF0FFF) == 0x010F0000)
	{
		CPU_UPDATE_CPSR();
		bus.reg[(opcode >> 12) & 0x0F].I = bus.reg[16].I;
	}
	else
		armUnknownInsn(opcode);
}

// MRS Rd, SPSR
static  void arm140(u32 opcode)
{
	if ((opcode & 0x0FFF0FFF) == 0x014F0000)
		bus.reg[(opcode >> 12) & 0x0F].I = bus.reg[17].I;
	else
		armUnknownInsn(opcode);
}

// MSR CPSR_fields, Rm
static  void arm120(u32 opcode)
{
    if ((opcode & 0x0FF0FFF0) == 0x0120F000)
    {
	    CPU_UPDATE_CPSR();
	    u32 value = bus.reg[opcode & 15].I;
	    u32 newValue = bus.reg[16].I;
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
	    if (!armState) {  // this should not be allowed, but it seems to work
		    THUMB_PREFETCH;
		    bus.reg[15].I = bus.armNextPC + 2;
	    }
    }
    else
	    armUnknownInsn(opcode);
}

// MSR SPSR_fields, Rm
static  void arm160(u32 opcode)
{
	if ((opcode & 0x0FF0FFF0) == 0x0160F000)
	{
		u32 value = bus.reg[opcode & 15].I;
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

// MSR CPSR_fields, #
static  void arm320(u32 opcode)
{
	if ((opcode & 0x0FF0F000) == 0x0320F000)
	{
		CPU_UPDATE_CPSR();
		u32 value = opcode & 0xFF;
		int shift = (opcode & 0xF00) >> 7;
		if (shift) {
			ROR_IMM_MSR;
		}
		u32 newValue = bus.reg[16].I;
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
		if (!armState) {  // this should not be allowed, but it seems to work
			THUMB_PREFETCH;
			bus.reg[15].I = bus.armNextPC + 2;
		}
	}
	else
		armUnknownInsn(opcode);
}

// MSR SPSR_fields, #
static  void arm360(u32 opcode)
{
	if ((opcode & 0x0FF0F000) == 0x0360F000) {
		if (armMode > 0x10 && armMode < 0x1F) {
			u32 value = opcode & 0xFF;
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

// BX Rm
static  void arm121(u32 opcode)
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
			clockTicks = 3 + (codeTicksAccessSeq32(bus.armNextPC)<<1)
				+ codeTicksAccess(bus.armNextPC, BITS_32);
		} else {
			bus.reg[15].I = bus.reg[base].I & 0xFFFFFFFE;
			bus.armNextPC = bus.reg[15].I;
			bus.reg[15].I += 2;
			THUMB_PREFETCH;
			clockTicks = 3 + (codeTicksAccessSeq16(bus.armNextPC)<<1)
				+ codeTicksAccess(bus.armNextPC, BITS_16);
		}
	}
	else
		armUnknownInsn(opcode);
}

// Load/store /////////////////////////////////////////////////////////////

#define OFFSET_IMM \
    int offset = opcode & 0xFFF;
#define OFFSET_IMM8 \
    int offset = ((opcode & 0x0F) | ((opcode>>4) & 0xF0));
#define OFFSET_REG \
    int offset = bus.reg[opcode & 15].I;
#define OFFSET_LSL \
    int offset = bus.reg[opcode & 15].I << ((opcode>>7) & 31);
#define OFFSET_LSR \
    int shift = (opcode >> 7) & 31;                     \
    int offset = shift ? bus.reg[opcode & 15].I >> shift : 0;
#define OFFSET_ASR \
    int shift = (opcode >> 7) & 31;                     \
    int offset;                                         \
    if (shift)                                          \
        offset = (int)((s32)bus.reg[opcode & 15].I >> shift);\
    else if (bus.reg[opcode & 15].I & 0x80000000)           \
        offset = 0xFFFFFFFF;                            \
    else                                                \
        offset = 0;
#define OFFSET_ROR \
    int shift = (opcode >> 7) & 31;                     \
    u32 offset = bus.reg[opcode & 15].I;                    \
    if (shift) {                                        \
        ROR_OFFSET;                                     \
    } else {                                            \
        RRX_OFFSET;                                     \
    }

#define ADDRESS_POST (bus.reg[base].I)
#define ADDRESS_PREDEC (bus.reg[base].I - offset)
#define ADDRESS_PREINC (bus.reg[base].I + offset)

#define OP_STR    CPUWriteMemory(address, bus.reg[dest].I)
#define OP_STRH   CPUWriteHalfWord(address, bus.reg[dest].W.W0)
#define OP_STRB   CPUWriteByte(address, bus.reg[dest].B.B0)
#define OP_LDR    bus.reg[dest].I = CPUReadMemory(address)
#define OP_LDRH   bus.reg[dest].I = CPUReadHalfWord(address)
#define OP_LDRB   bus.reg[dest].I = CPUReadByte(address)
#define OP_LDRSH  bus.reg[dest].I = (s16)CPUReadHalfWordSigned(address)
#define OP_LDRSB  bus.reg[dest].I = (s8)CPUReadByte(address)

#define WRITEBACK_NONE     /*nothing*/
#define WRITEBACK_PRE      bus.reg[base].I = address
#define WRITEBACK_POSTDEC  bus.reg[base].I = address - offset
#define WRITEBACK_POSTINC  bus.reg[base].I = address + offset

#define LDRSTR_INIT(CALC_OFFSET, CALC_ADDRESS) \
    if (bus.busPrefetchCount == 0)                          \
        bus.busPrefetch = bus.busPrefetchEnable;                \
    int dest = (opcode >> 12) & 15;                     \
    int base = (opcode >> 16) & 15;                     \
    CALC_OFFSET;                                        \
    u32 address = CALC_ADDRESS;

#define STR(CALC_OFFSET, CALC_ADDRESS, STORE_DATA, WRITEBACK1, WRITEBACK2, SIZE) \
    LDRSTR_INIT(CALC_OFFSET, CALC_ADDRESS);             \
    WRITEBACK1;                                         \
    STORE_DATA;                                         \
    WRITEBACK2;                                         \
    int dataticks_val;					\
    if(SIZE == 32) \
       dataticks_val = DATATICKS_ACCESS_32BIT(address);	\
    else \
       dataticks_val = DATATICKS_ACCESS_16BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_val); \
    clockTicks = 2 + dataticks_val + codeTicksAccess(bus.armNextPC, BITS_32); 

#define LDR(CALC_OFFSET, CALC_ADDRESS, LOAD_DATA, WRITEBACK, SIZE) \
    LDRSTR_INIT(CALC_OFFSET, CALC_ADDRESS);             \
    LOAD_DATA;                                          \
    if (dest != base)                                   \
    {                                                   \
        WRITEBACK;                                      \
    }                                                   \
    clockTicks = 0;                                     \
    int dataticks_value; \
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

// STRH Rd, [Rn], -Rm
static  void arm00B(u32 opcode) { STR_POSTDEC(OFFSET_REG, OP_STRH, 16); }
// STRH Rd, [Rn], #-offset
static  void arm04B(u32 opcode) { STR_POSTDEC(OFFSET_IMM8, OP_STRH, 16); }
// STRH Rd, [Rn], Rm
static  void arm08B(u32 opcode) { STR_POSTINC(OFFSET_REG, OP_STRH, 16); }
// STRH Rd, [Rn], #offset
static  void arm0CB(u32 opcode) { STR_POSTINC(OFFSET_IMM8, OP_STRH, 16); }
// STRH Rd, [Rn, -Rm]
static  void arm10B(u32 opcode) { STR_PREDEC(OFFSET_REG, OP_STRH, 16); }
// STRH Rd, [Rn, -Rm]!
static  void arm12B(u32 opcode) { STR_PREDEC_WB(OFFSET_REG, OP_STRH, 16); }
// STRH Rd, [Rn, -#offset]
static  void arm14B(u32 opcode) { STR_PREDEC(OFFSET_IMM8, OP_STRH, 16); }
// STRH Rd, [Rn, -#offset]!
static  void arm16B(u32 opcode) { STR_PREDEC_WB(OFFSET_IMM8, OP_STRH, 16); }
// STRH Rd, [Rn, Rm]
static  void arm18B(u32 opcode) { STR_PREINC(OFFSET_REG, OP_STRH, 16); }
// STRH Rd, [Rn, Rm]!
static  void arm1AB(u32 opcode) { STR_PREINC_WB(OFFSET_REG, OP_STRH, 16); }
// STRH Rd, [Rn, #offset]
static  void arm1CB(u32 opcode) { STR_PREINC(OFFSET_IMM8, OP_STRH, 16); }
// STRH Rd, [Rn, #offset]!
static  void arm1EB(u32 opcode) { STR_PREINC_WB(OFFSET_IMM8, OP_STRH, 16); }

// LDRH Rd, [Rn], -Rm
static  void arm01B(u32 opcode) { LDR_POSTDEC(OFFSET_REG, OP_LDRH, 16); }
// LDRH Rd, [Rn], #-offset
static  void arm05B(u32 opcode) { LDR_POSTDEC(OFFSET_IMM8, OP_LDRH, 16); }
// LDRH Rd, [Rn], Rm
static  void arm09B(u32 opcode) { LDR_POSTINC(OFFSET_REG, OP_LDRH, 16); }
// LDRH Rd, [Rn], #offset
static  void arm0DB(u32 opcode) { LDR_POSTINC(OFFSET_IMM8, OP_LDRH, 16); }
// LDRH Rd, [Rn, -Rm]
static  void arm11B(u32 opcode) { LDR_PREDEC(OFFSET_REG, OP_LDRH, 16); }
// LDRH Rd, [Rn, -Rm]!
static  void arm13B(u32 opcode) { LDR_PREDEC_WB(OFFSET_REG, OP_LDRH, 16); }
// LDRH Rd, [Rn, -#offset]
static  void arm15B(u32 opcode) { LDR_PREDEC(OFFSET_IMM8, OP_LDRH, 16); }
// LDRH Rd, [Rn, -#offset]!
static  void arm17B(u32 opcode) { LDR_PREDEC_WB(OFFSET_IMM8, OP_LDRH, 16); }
// LDRH Rd, [Rn, Rm]
static  void arm19B(u32 opcode) { LDR_PREINC(OFFSET_REG, OP_LDRH, 16); }
// LDRH Rd, [Rn, Rm]!
static  void arm1BB(u32 opcode) { LDR_PREINC_WB(OFFSET_REG, OP_LDRH, 16); }
// LDRH Rd, [Rn, #offset]
static  void arm1DB(u32 opcode) { LDR_PREINC(OFFSET_IMM8, OP_LDRH, 16); }
// LDRH Rd, [Rn, #offset]!
static  void arm1FB(u32 opcode) { LDR_PREINC_WB(OFFSET_IMM8, OP_LDRH, 16); }

// LDRSB Rd, [Rn], -Rm
static  void arm01D(u32 opcode) { LDR_POSTDEC(OFFSET_REG, OP_LDRSB, 16); }
// LDRSB Rd, [Rn], #-offset
static  void arm05D(u32 opcode) { LDR_POSTDEC(OFFSET_IMM8, OP_LDRSB, 16); }
// LDRSB Rd, [Rn], Rm
static  void arm09D(u32 opcode) { LDR_POSTINC(OFFSET_REG, OP_LDRSB, 16); }
// LDRSB Rd, [Rn], #offset
static  void arm0DD(u32 opcode) { LDR_POSTINC(OFFSET_IMM8, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, -Rm]
static  void arm11D(u32 opcode) { LDR_PREDEC(OFFSET_REG, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, -Rm]!
static  void arm13D(u32 opcode) { LDR_PREDEC_WB(OFFSET_REG, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, -#offset]
static  void arm15D(u32 opcode) { LDR_PREDEC(OFFSET_IMM8, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, -#offset]!
static  void arm17D(u32 opcode) { LDR_PREDEC_WB(OFFSET_IMM8, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, Rm]
static  void arm19D(u32 opcode) { LDR_PREINC(OFFSET_REG, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, Rm]!
static  void arm1BD(u32 opcode) { LDR_PREINC_WB(OFFSET_REG, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, #offset]
static  void arm1DD(u32 opcode) { LDR_PREINC(OFFSET_IMM8, OP_LDRSB, 16); }
// LDRSB Rd, [Rn, #offset]!
static  void arm1FD(u32 opcode) { LDR_PREINC_WB(OFFSET_IMM8, OP_LDRSB, 16); }

// LDRSH Rd, [Rn], -Rm
static  void arm01F(u32 opcode) { LDR_POSTDEC(OFFSET_REG, OP_LDRSH, 16); }
// LDRSH Rd, [Rn], #-offset
static  void arm05F(u32 opcode) { LDR_POSTDEC(OFFSET_IMM8, OP_LDRSH, 16); }
// LDRSH Rd, [Rn], Rm
static  void arm09F(u32 opcode) { LDR_POSTINC(OFFSET_REG, OP_LDRSH, 16); }
// LDRSH Rd, [Rn], #offset
static  void arm0DF(u32 opcode) { LDR_POSTINC(OFFSET_IMM8, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, -Rm]
static  void arm11F(u32 opcode) { LDR_PREDEC(OFFSET_REG, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, -Rm]!
static  void arm13F(u32 opcode) { LDR_PREDEC_WB(OFFSET_REG, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, -#offset]
static  void arm15F(u32 opcode) { LDR_PREDEC(OFFSET_IMM8, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, -#offset]!
static  void arm17F(u32 opcode) { LDR_PREDEC_WB(OFFSET_IMM8, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, Rm]
static  void arm19F(u32 opcode) { LDR_PREINC(OFFSET_REG, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, Rm]!
static  void arm1BF(u32 opcode) { LDR_PREINC_WB(OFFSET_REG, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, #offset]
static  void arm1DF(u32 opcode) { LDR_PREINC(OFFSET_IMM8, OP_LDRSH, 16); }
// LDRSH Rd, [Rn, #offset]!
static  void arm1FF(u32 opcode) { LDR_PREINC_WB(OFFSET_IMM8, OP_LDRSH, 16); }

// STR[T] Rd, [Rn], -#
// Note: STR and STRT do the same thing on the GBA (likewise for LDR/LDRT etc)
static  void arm400(u32 opcode) { STR_POSTDEC(OFFSET_IMM, OP_STR, 32); }
// LDR[T] Rd, [Rn], -#
static  void arm410(u32 opcode) { LDR_POSTDEC(OFFSET_IMM, OP_LDR, 32); }
// STRB[T] Rd, [Rn], -#
static  void arm440(u32 opcode) { STR_POSTDEC(OFFSET_IMM, OP_STRB, 16); }
// LDRB[T] Rd, [Rn], -#
static  void arm450(u32 opcode) { LDR_POSTDEC(OFFSET_IMM, OP_LDRB, 16); }
// STR[T] Rd, [Rn], #
static  void arm480(u32 opcode) { STR_POSTINC(OFFSET_IMM, OP_STR, 32); }
// LDR Rd, [Rn], #
static  void arm490(u32 opcode) { LDR_POSTINC(OFFSET_IMM, OP_LDR, 32); }
// STRB[T] Rd, [Rn], #
static  void arm4C0(u32 opcode) { STR_POSTINC(OFFSET_IMM, OP_STRB, 16); }
// LDRB[T] Rd, [Rn], #
static  void arm4D0(u32 opcode) { LDR_POSTINC(OFFSET_IMM, OP_LDRB, 16); }
// STR Rd, [Rn, -#]
static  void arm500(u32 opcode) { STR_PREDEC(OFFSET_IMM, OP_STR, 32); }
// LDR Rd, [Rn, -#]
static  void arm510(u32 opcode) { LDR_PREDEC(OFFSET_IMM, OP_LDR, 32); }
// STR Rd, [Rn, -#]!
static  void arm520(u32 opcode) { STR_PREDEC_WB(OFFSET_IMM, OP_STR, 32); }
// LDR Rd, [Rn, -#]!
static  void arm530(u32 opcode) { LDR_PREDEC_WB(OFFSET_IMM, OP_LDR, 32); }
// STRB Rd, [Rn, -#]
static  void arm540(u32 opcode) { STR_PREDEC(OFFSET_IMM, OP_STRB, 16); }
// LDRB Rd, [Rn, -#]
static  void arm550(u32 opcode) { LDR_PREDEC(OFFSET_IMM, OP_LDRB, 16); }
// STRB Rd, [Rn, -#]!
static  void arm560(u32 opcode) { STR_PREDEC_WB(OFFSET_IMM, OP_STRB, 16); }
// LDRB Rd, [Rn, -#]!
static  void arm570(u32 opcode) { LDR_PREDEC_WB(OFFSET_IMM, OP_LDRB, 16); }
// STR Rd, [Rn, #]
static  void arm580(u32 opcode) { STR_PREINC(OFFSET_IMM, OP_STR, 32); }
// LDR Rd, [Rn, #]
static  void arm590(u32 opcode) { LDR_PREINC(OFFSET_IMM, OP_LDR, 32); }
// STR Rd, [Rn, #]!
static  void arm5A0(u32 opcode) { STR_PREINC_WB(OFFSET_IMM, OP_STR, 32); }
// LDR Rd, [Rn, #]!
static  void arm5B0(u32 opcode) { LDR_PREINC_WB(OFFSET_IMM, OP_LDR, 32); }
// STRB Rd, [Rn, #]
static  void arm5C0(u32 opcode) { STR_PREINC(OFFSET_IMM, OP_STRB, 16); }
// LDRB Rd, [Rn, #]
static  void arm5D0(u32 opcode) { LDR_PREINC(OFFSET_IMM, OP_LDRB, 16); }
// STRB Rd, [Rn, #]!
static  void arm5E0(u32 opcode) { STR_PREINC_WB(OFFSET_IMM, OP_STRB, 16); }
// LDRB Rd, [Rn, #]!
static  void arm5F0(u32 opcode) { LDR_PREINC_WB(OFFSET_IMM, OP_LDRB, 16); }

// STR[T] Rd, [Rn], -Rm, LSL #
static  void arm600(u32 opcode) { STR_POSTDEC(OFFSET_LSL, OP_STR, 32); }
// STR[T] Rd, [Rn], -Rm, LSR #
static  void arm602(u32 opcode) { STR_POSTDEC(OFFSET_LSR, OP_STR, 32); }
// STR[T] Rd, [Rn], -Rm, ASR #
static  void arm604(u32 opcode) { STR_POSTDEC(OFFSET_ASR, OP_STR, 32); }
// STR[T] Rd, [Rn], -Rm, ROR #
static  void arm606(u32 opcode) { STR_POSTDEC(OFFSET_ROR, OP_STR, 32); }
// LDR[T] Rd, [Rn], -Rm, LSL #
static  void arm610(u32 opcode) { LDR_POSTDEC(OFFSET_LSL, OP_LDR, 32); }
// LDR[T] Rd, [Rn], -Rm, LSR #
static  void arm612(u32 opcode) { LDR_POSTDEC(OFFSET_LSR, OP_LDR, 32); }
// LDR[T] Rd, [Rn], -Rm, ASR #
static  void arm614(u32 opcode) { LDR_POSTDEC(OFFSET_ASR, OP_LDR, 32); }
// LDR[T] Rd, [Rn], -Rm, ROR #
static  void arm616(u32 opcode) { LDR_POSTDEC(OFFSET_ROR, OP_LDR, 32); }
// STRB[T] Rd, [Rn], -Rm, LSL #
static  void arm640(u32 opcode) { STR_POSTDEC(OFFSET_LSL, OP_STRB, 16); }
// STRB[T] Rd, [Rn], -Rm, LSR #
static  void arm642(u32 opcode) { STR_POSTDEC(OFFSET_LSR, OP_STRB, 16); }
// STRB[T] Rd, [Rn], -Rm, ASR #
static  void arm644(u32 opcode) { STR_POSTDEC(OFFSET_ASR, OP_STRB, 16); }
// STRB[T] Rd, [Rn], -Rm, ROR #
static  void arm646(u32 opcode) { STR_POSTDEC(OFFSET_ROR, OP_STRB, 16); }
// LDRB[T] Rd, [Rn], -Rm, LSL #
static  void arm650(u32 opcode) { LDR_POSTDEC(OFFSET_LSL, OP_LDRB, 16); }
// LDRB[T] Rd, [Rn], -Rm, LSR #
static  void arm652(u32 opcode) { LDR_POSTDEC(OFFSET_LSR, OP_LDRB, 16); }
// LDRB[T] Rd, [Rn], -Rm, ASR #
static  void arm654(u32 opcode) { LDR_POSTDEC(OFFSET_ASR, OP_LDRB, 16); }
// LDRB Rd, [Rn], -Rm, ROR #
static  void arm656(u32 opcode) { LDR_POSTDEC(OFFSET_ROR, OP_LDRB, 16); }
// STR[T] Rd, [Rn], Rm, LSL #
static  void arm680(u32 opcode) { STR_POSTINC(OFFSET_LSL, OP_STR, 32); }
// STR[T] Rd, [Rn], Rm, LSR #
static  void arm682(u32 opcode) { STR_POSTINC(OFFSET_LSR, OP_STR, 32); }
// STR[T] Rd, [Rn], Rm, ASR #
static  void arm684(u32 opcode) { STR_POSTINC(OFFSET_ASR, OP_STR, 32); }
// STR[T] Rd, [Rn], Rm, ROR #
static  void arm686(u32 opcode) { STR_POSTINC(OFFSET_ROR, OP_STR, 32); }
// LDR[T] Rd, [Rn], Rm, LSL #
static  void arm690(u32 opcode) { LDR_POSTINC(OFFSET_LSL, OP_LDR, 32); }
// LDR[T] Rd, [Rn], Rm, LSR #
static  void arm692(u32 opcode) { LDR_POSTINC(OFFSET_LSR, OP_LDR, 32); }
// LDR[T] Rd, [Rn], Rm, ASR #
static  void arm694(u32 opcode) { LDR_POSTINC(OFFSET_ASR, OP_LDR, 32); }
// LDR[T] Rd, [Rn], Rm, ROR #
static  void arm696(u32 opcode) { LDR_POSTINC(OFFSET_ROR, OP_LDR, 32); }
// STRB[T] Rd, [Rn], Rm, LSL #
static  void arm6C0(u32 opcode) { STR_POSTINC(OFFSET_LSL, OP_STRB, 16); }
// STRB[T] Rd, [Rn], Rm, LSR #
static  void arm6C2(u32 opcode) { STR_POSTINC(OFFSET_LSR, OP_STRB, 16); }
// STRB[T] Rd, [Rn], Rm, ASR #
static  void arm6C4(u32 opcode) { STR_POSTINC(OFFSET_ASR, OP_STRB, 16); }
// STRB[T] Rd, [Rn], Rm, ROR #
static  void arm6C6(u32 opcode) { STR_POSTINC(OFFSET_ROR, OP_STRB, 16); }
// LDRB[T] Rd, [Rn], Rm, LSL #
static  void arm6D0(u32 opcode) { LDR_POSTINC(OFFSET_LSL, OP_LDRB, 16); }
// LDRB[T] Rd, [Rn], Rm, LSR #
static  void arm6D2(u32 opcode) { LDR_POSTINC(OFFSET_LSR, OP_LDRB, 16); }
// LDRB[T] Rd, [Rn], Rm, ASR #
static  void arm6D4(u32 opcode) { LDR_POSTINC(OFFSET_ASR, OP_LDRB, 16); }
// LDRB[T] Rd, [Rn], Rm, ROR #
static  void arm6D6(u32 opcode) { LDR_POSTINC(OFFSET_ROR, OP_LDRB, 16); }
// STR Rd, [Rn, -Rm, LSL #]
static  void arm700(u32 opcode) { STR_PREDEC(OFFSET_LSL, OP_STR, 32); }
// STR Rd, [Rn, -Rm, LSR #]
static  void arm702(u32 opcode) { STR_PREDEC(OFFSET_LSR, OP_STR, 32); }
// STR Rd, [Rn, -Rm, ASR #]
static  void arm704(u32 opcode) { STR_PREDEC(OFFSET_ASR, OP_STR, 32); }
// STR Rd, [Rn, -Rm, ROR #]
static  void arm706(u32 opcode) { STR_PREDEC(OFFSET_ROR, OP_STR, 32); }
// LDR Rd, [Rn, -Rm, LSL #]
static  void arm710(u32 opcode) { LDR_PREDEC(OFFSET_LSL, OP_LDR, 32); }
// LDR Rd, [Rn, -Rm, LSR #]
static  void arm712(u32 opcode) { LDR_PREDEC(OFFSET_LSR, OP_LDR, 32); }
// LDR Rd, [Rn, -Rm, ASR #]
static  void arm714(u32 opcode) { LDR_PREDEC(OFFSET_ASR, OP_LDR, 32); }
// LDR Rd, [Rn, -Rm, ROR #]
static  void arm716(u32 opcode) { LDR_PREDEC(OFFSET_ROR, OP_LDR, 32); }
// STR Rd, [Rn, -Rm, LSL #]!
static  void arm720(u32 opcode) { STR_PREDEC_WB(OFFSET_LSL, OP_STR, 32); }
// STR Rd, [Rn, -Rm, LSR #]!
static  void arm722(u32 opcode) { STR_PREDEC_WB(OFFSET_LSR, OP_STR, 32); }
// STR Rd, [Rn, -Rm, ASR #]!
static  void arm724(u32 opcode) { STR_PREDEC_WB(OFFSET_ASR, OP_STR, 32); }
// STR Rd, [Rn, -Rm, ROR #]!
static  void arm726(u32 opcode) { STR_PREDEC_WB(OFFSET_ROR, OP_STR, 32); }
// LDR Rd, [Rn, -Rm, LSL #]!
static  void arm730(u32 opcode) { LDR_PREDEC_WB(OFFSET_LSL, OP_LDR, 32); }
// LDR Rd, [Rn, -Rm, LSR #]!
static  void arm732(u32 opcode) { LDR_PREDEC_WB(OFFSET_LSR, OP_LDR, 32); }
// LDR Rd, [Rn, -Rm, ASR #]!
static  void arm734(u32 opcode) { LDR_PREDEC_WB(OFFSET_ASR, OP_LDR, 32); }
// LDR Rd, [Rn, -Rm, ROR #]!
static  void arm736(u32 opcode) { LDR_PREDEC_WB(OFFSET_ROR, OP_LDR, 32); }
// STRB Rd, [Rn, -Rm, LSL #]
static  void arm740(u32 opcode) { STR_PREDEC(OFFSET_LSL, OP_STRB, 16); }
// STRB Rd, [Rn, -Rm, LSR #]
static  void arm742(u32 opcode) { STR_PREDEC(OFFSET_LSR, OP_STRB, 16); }
// STRB Rd, [Rn, -Rm, ASR #]
static  void arm744(u32 opcode) { STR_PREDEC(OFFSET_ASR, OP_STRB, 16); }
// STRB Rd, [Rn, -Rm, ROR #]
static  void arm746(u32 opcode) { STR_PREDEC(OFFSET_ROR, OP_STRB, 16); }
// LDRB Rd, [Rn, -Rm, LSL #]
static  void arm750(u32 opcode) { LDR_PREDEC(OFFSET_LSL, OP_LDRB, 16); }
// LDRB Rd, [Rn, -Rm, LSR #]
static  void arm752(u32 opcode) { LDR_PREDEC(OFFSET_LSR, OP_LDRB, 16); }
// LDRB Rd, [Rn, -Rm, ASR #]
static  void arm754(u32 opcode) { LDR_PREDEC(OFFSET_ASR, OP_LDRB, 16); }
// LDRB Rd, [Rn, -Rm, ROR #]
static  void arm756(u32 opcode) { LDR_PREDEC(OFFSET_ROR, OP_LDRB, 16); }
// STRB Rd, [Rn, -Rm, LSL #]!
static  void arm760(u32 opcode) { STR_PREDEC_WB(OFFSET_LSL, OP_STRB, 16); }
// STRB Rd, [Rn, -Rm, LSR #]!
static  void arm762(u32 opcode) { STR_PREDEC_WB(OFFSET_LSR, OP_STRB, 16); }
// STRB Rd, [Rn, -Rm, ASR #]!
static  void arm764(u32 opcode) { STR_PREDEC_WB(OFFSET_ASR, OP_STRB, 16); }
// STRB Rd, [Rn, -Rm, ROR #]!
static  void arm766(u32 opcode) { STR_PREDEC_WB(OFFSET_ROR, OP_STRB, 16); }
// LDRB Rd, [Rn, -Rm, LSL #]!
static  void arm770(u32 opcode) { LDR_PREDEC_WB(OFFSET_LSL, OP_LDRB, 16); }
// LDRB Rd, [Rn, -Rm, LSR #]!
static  void arm772(u32 opcode) { LDR_PREDEC_WB(OFFSET_LSR, OP_LDRB, 16); }
// LDRB Rd, [Rn, -Rm, ASR #]!
static  void arm774(u32 opcode) { LDR_PREDEC_WB(OFFSET_ASR, OP_LDRB, 16); }
// LDRB Rd, [Rn, -Rm, ROR #]!
static  void arm776(u32 opcode) { LDR_PREDEC_WB(OFFSET_ROR, OP_LDRB, 16); }
// STR Rd, [Rn, Rm, LSL #]
static  void arm780(u32 opcode) { STR_PREINC(OFFSET_LSL, OP_STR, 32); }
// STR Rd, [Rn, Rm, LSR #]
static  void arm782(u32 opcode) { STR_PREINC(OFFSET_LSR, OP_STR, 32); }
// STR Rd, [Rn, Rm, ASR #]
static  void arm784(u32 opcode) { STR_PREINC(OFFSET_ASR, OP_STR, 32); }
// STR Rd, [Rn, Rm, ROR #]
static  void arm786(u32 opcode) { STR_PREINC(OFFSET_ROR, OP_STR, 32); }
// LDR Rd, [Rn, Rm, LSL #]
static  void arm790(u32 opcode) { LDR_PREINC(OFFSET_LSL, OP_LDR, 32); }
// LDR Rd, [Rn, Rm, LSR #]
static  void arm792(u32 opcode) { LDR_PREINC(OFFSET_LSR, OP_LDR, 32); }
// LDR Rd, [Rn, Rm, ASR #]
static  void arm794(u32 opcode) { LDR_PREINC(OFFSET_ASR, OP_LDR, 32); }
// LDR Rd, [Rn, Rm, ROR #]
static  void arm796(u32 opcode) { LDR_PREINC(OFFSET_ROR, OP_LDR, 32); }
// STR Rd, [Rn, Rm, LSL #]!
static  void arm7A0(u32 opcode) { STR_PREINC_WB(OFFSET_LSL, OP_STR, 32); }
// STR Rd, [Rn, Rm, LSR #]!
static  void arm7A2(u32 opcode) { STR_PREINC_WB(OFFSET_LSR, OP_STR, 32); }
// STR Rd, [Rn, Rm, ASR #]!
static  void arm7A4(u32 opcode) { STR_PREINC_WB(OFFSET_ASR, OP_STR, 32); }
// STR Rd, [Rn, Rm, ROR #]!
static  void arm7A6(u32 opcode) { STR_PREINC_WB(OFFSET_ROR, OP_STR, 32); }
// LDR Rd, [Rn, Rm, LSL #]!
static  void arm7B0(u32 opcode) { LDR_PREINC_WB(OFFSET_LSL, OP_LDR, 32); }
// LDR Rd, [Rn, Rm, LSR #]!
static  void arm7B2(u32 opcode) { LDR_PREINC_WB(OFFSET_LSR, OP_LDR, 32); }
// LDR Rd, [Rn, Rm, ASR #]!
static  void arm7B4(u32 opcode) { LDR_PREINC_WB(OFFSET_ASR, OP_LDR, 32); }
// LDR Rd, [Rn, Rm, ROR #]!
static  void arm7B6(u32 opcode) { LDR_PREINC_WB(OFFSET_ROR, OP_LDR, 32); }
// STRB Rd, [Rn, Rm, LSL #]
static  void arm7C0(u32 opcode) { STR_PREINC(OFFSET_LSL, OP_STRB, 16); }
// STRB Rd, [Rn, Rm, LSR #]
static  void arm7C2(u32 opcode) { STR_PREINC(OFFSET_LSR, OP_STRB, 16); }
// STRB Rd, [Rn, Rm, ASR #]
static  void arm7C4(u32 opcode) { STR_PREINC(OFFSET_ASR, OP_STRB, 16); }
// STRB Rd, [Rn, Rm, ROR #]
static  void arm7C6(u32 opcode) { STR_PREINC(OFFSET_ROR, OP_STRB, 16); }
// LDRB Rd, [Rn, Rm, LSL #]
static  void arm7D0(u32 opcode) { LDR_PREINC(OFFSET_LSL, OP_LDRB, 16); }
// LDRB Rd, [Rn, Rm, LSR #]
static  void arm7D2(u32 opcode) { LDR_PREINC(OFFSET_LSR, OP_LDRB, 16); }
// LDRB Rd, [Rn, Rm, ASR #]
static  void arm7D4(u32 opcode) { LDR_PREINC(OFFSET_ASR, OP_LDRB, 16); }
// LDRB Rd, [Rn, Rm, ROR #]
static  void arm7D6(u32 opcode) { LDR_PREINC(OFFSET_ROR, OP_LDRB, 16); }
// STRB Rd, [Rn, Rm, LSL #]!
static  void arm7E0(u32 opcode) { STR_PREINC_WB(OFFSET_LSL, OP_STRB, 16); }
// STRB Rd, [Rn, Rm, LSR #]!
static  void arm7E2(u32 opcode) { STR_PREINC_WB(OFFSET_LSR, OP_STRB, 16); }
// STRB Rd, [Rn, Rm, ASR #]!
static  void arm7E4(u32 opcode) { STR_PREINC_WB(OFFSET_ASR, OP_STRB, 16); }
// STRB Rd, [Rn, Rm, ROR #]!
static  void arm7E6(u32 opcode) { STR_PREINC_WB(OFFSET_ROR, OP_STRB, 16); }
// LDRB Rd, [Rn, Rm, LSL #]!
static  void arm7F0(u32 opcode) { LDR_PREINC_WB(OFFSET_LSL, OP_LDRB, 16); }
// LDRB Rd, [Rn, Rm, LSR #]!
static  void arm7F2(u32 opcode) { LDR_PREINC_WB(OFFSET_LSR, OP_LDRB, 16); }
// LDRB Rd, [Rn, Rm, ASR #]!
static  void arm7F4(u32 opcode) { LDR_PREINC_WB(OFFSET_ASR, OP_LDRB, 16); }
// LDRB Rd, [Rn, Rm, ROR #]!
static  void arm7F6(u32 opcode) { LDR_PREINC_WB(OFFSET_ROR, OP_LDRB, 16); }

// STM/LDM ////////////////////////////////////////////////////////////////

#define STM_REG(bit,num) \
    if (opcode & (1U<<(bit))) {                         \
        CPUWriteMemory(address, bus.reg[(num)].I);          \
	int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
        address += 4;                                   \
    }
#define STMW_REG(bit,num) \
    if (opcode & (1U<<(bit))) {                         \
        CPUWriteMemory(address, bus.reg[(num)].I);          \
	int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        bus.reg[base].I = temp;                             \
        count++;                                        \
        address += 4;                                   \
    }
#define LDM_REG(bit,num) \
    if (opcode & (1U<<(bit))) {                         \
	int dataticks_value; \
        bus.reg[(num)].I = CPUReadMemory(address); \
	dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
        address += 4;                                   \
    }
#define STM_LOW(STORE_REG) \
    STORE_REG(0, 0);                                    \
    STORE_REG(1, 1);                                    \
    STORE_REG(2, 2);                                    \
    STORE_REG(3, 3);                                    \
    STORE_REG(4, 4);                                    \
    STORE_REG(5, 5);                                    \
    STORE_REG(6, 6);                                    \
    STORE_REG(7, 7);
#define STM_HIGH(STORE_REG) \
    STORE_REG(8, 8);                                    \
    STORE_REG(9, 9);                                    \
    STORE_REG(10, 10);                                  \
    STORE_REG(11, 11);                                  \
    STORE_REG(12, 12);                                  \
    STORE_REG(13, 13);                                  \
    STORE_REG(14, 14);
#define STM_HIGH_2(STORE_REG) \
    if (armMode == 0x11) {                              \
        STORE_REG(8, R8_FIQ);                           \
        STORE_REG(9, R9_FIQ);                           \
        STORE_REG(10, R10_FIQ);                         \
        STORE_REG(11, R11_FIQ);                         \
        STORE_REG(12, R12_FIQ);                         \
    } else {                                            \
        STORE_REG(8, 8);                                \
        STORE_REG(9, 9);                                \
        STORE_REG(10, 10);                              \
        STORE_REG(11, 11);                              \
        STORE_REG(12, 12);                              \
    }                                                   \
    if (armMode != 0x10 && armMode != 0x1F) {           \
        STORE_REG(13, R13_USR);                         \
        STORE_REG(14, R14_USR);                         \
    } else {                                            \
        STORE_REG(13, 13);                              \
        STORE_REG(14, 14);                              \
    }
#define STM_PC \
    if (opcode & (1U<<15)) {                            \
        CPUWriteMemory(address, bus.reg[15].I+4);           \
	int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
    }
#define STMW_PC \
    if (opcode & (1U<<15)) {                            \
        CPUWriteMemory(address, bus.reg[15].I+4);           \
	int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        bus.reg[base].I = temp;                             \
        count++;                                        \
    }
#define LDM_LOW \
    LDM_REG(0, 0);                                      \
    LDM_REG(1, 1);                                      \
    LDM_REG(2, 2);                                      \
    LDM_REG(3, 3);                                      \
    LDM_REG(4, 4);                                      \
    LDM_REG(5, 5);                                      \
    LDM_REG(6, 6);                                      \
    LDM_REG(7, 7);
#define LDM_HIGH \
    LDM_REG(8, 8);                                      \
    LDM_REG(9, 9);                                      \
    LDM_REG(10, 10);                                    \
    LDM_REG(11, 11);                                    \
    LDM_REG(12, 12);                                    \
    LDM_REG(13, 13);                                    \
    LDM_REG(14, 14);
#define LDM_HIGH_2 \
    if (armMode == 0x11) {                              \
        LDM_REG(8, R8_FIQ);                             \
        LDM_REG(9, R9_FIQ);                             \
        LDM_REG(10, R10_FIQ);                           \
        LDM_REG(11, R11_FIQ);                           \
        LDM_REG(12, R12_FIQ);                           \
    } else {                                            \
        LDM_REG(8, 8);                                  \
        LDM_REG(9, 9);                                  \
        LDM_REG(10, 10);                                \
        LDM_REG(11, 11);                                \
        LDM_REG(12, 12);                                \
    }                                                   \
    if (armMode != 0x10 && armMode != 0x1F) {           \
        LDM_REG(13, R13_USR);                           \
        LDM_REG(14, R14_USR);                           \
    } else {                                            \
        LDM_REG(13, 13);                                \
        LDM_REG(14, 14);                                \
    }
#define STM_ALL \
    STM_LOW(STM_REG);                                   \
    STM_HIGH(STM_REG);                                  \
    STM_PC;
#define STMW_ALL \
    STM_LOW(STMW_REG);                                  \
    STM_HIGH(STMW_REG);                                 \
    STMW_PC;
#define LDM_ALL \
    LDM_LOW;                                            \
    LDM_HIGH;                                           \
    if (opcode & (1U<<15)) {                            \
        bus.reg[15].I = CPUReadMemory(address);             \
	int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
	clockTicks += 1 + dataticks_value; \
        count++;                                        \
    }                                                   \
    if (opcode & (1U<<15)) {                            \
        bus.armNextPC = bus.reg[15].I;                          \
        bus.reg[15].I += 4;                                 \
        ARM_PREFETCH;                                   \
        clockTicks += 1 + codeTicksAccessSeq32(bus.armNextPC);\
    }
#define STM_ALL_2 \
    STM_LOW(STM_REG);                                   \
    STM_HIGH_2(STM_REG);                                \
    STM_PC;
#define STMW_ALL_2 \
    STM_LOW(STMW_REG);                                  \
    STM_HIGH_2(STMW_REG);                               \
    STMW_PC;
#define LDM_ALL_2 \
    LDM_LOW;                                            \
    if (opcode & (1U<<15)) {                            \
        LDM_HIGH;                                       \
        bus.reg[15].I = CPUReadMemory(address);             \
	int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
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
        clockTicks += 1 + codeTicksAccessSeq32(bus.armNextPC);\
    }


// STMDA Rn, {Rlist}
static  void arm800(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp + 4) & 0xFFFFFFFC;
    int count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDA Rn, {Rlist}
static  void arm810(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp + 4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMDA Rn!, {Rlist}
static  void arm820(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp+4) & 0xFFFFFFFC;
    int count = 0;
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDA Rn!, {Rlist}
static  void arm830(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp + 4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

// STMDA Rn, {Rlist}^
static  void arm840(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp+4) & 0xFFFFFFFC;
    int count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDA Rn, {Rlist}^
static  void arm850(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp + 4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMDA Rn!, {Rlist}^
static  void arm860(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp+4) & 0xFFFFFFFC;
    int count = 0;
    STMW_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDA Rn!, {Rlist}^
static  void arm870(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (temp + 4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMIA Rn, {Rlist}
static  void arm880(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIA Rn, {Rlist}
static  void arm890(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMIA Rn!, {Rlist}
static  void arm8A0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    u32 temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIA Rn!, {Rlist}
static  void arm8B0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

// STMIA Rn, {Rlist}^
static  void arm8C0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIA Rn, {Rlist}^
static  void arm8D0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMIA Rn!, {Rlist}^
static  void arm8E0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    u32 temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
    STMW_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIA Rn!, {Rlist}^
static  void arm8F0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = bus.reg[base].I & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMDB Rn, {Rlist}
static  void arm900(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDB Rn, {Rlist}
static  void arm910(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMDB Rn!, {Rlist}
static  void arm920(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDB Rn!, {Rlist}
static  void arm930(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

// STMDB Rn, {Rlist}^
static  void arm940(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDB Rn, {Rlist}^
static  void arm950(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMDB Rn!, {Rlist}^
static  void arm960(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    STMW_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMDB Rn!, {Rlist}^
static  void arm970(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I -
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = temp & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMIB Rn, {Rlist}
static  void arm980(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    int count = 0;
    STM_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIB Rn, {Rlist}
static  void arm990(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMIB Rn!, {Rlist}
static  void arm9A0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    int count = 0;
    u32 temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
    STMW_ALL;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIB Rn!, {Rlist}
static  void arm9B0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 temp = bus.reg[base].I +
        4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
    u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
    if (!(opcode & (1U << base)))
        bus.reg[base].I = temp;
}

// STMIB Rn, {Rlist}^
static  void arm9C0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    int count = 0;
    STM_ALL_2;
    clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIB Rn, {Rlist}^
static  void arm9D0(u32 opcode)
{
    if (bus.busPrefetchCount == 0)
        bus.busPrefetch = bus.busPrefetchEnable;
    int base = (opcode & 0x000F0000) >> 16;
    u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
    int count = 0;
    LDM_ALL_2;
    LDM_ALL_2B;
    clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// STMIB Rn!, {Rlist}^
static  void arm9E0(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	int base = (opcode & 0x000F0000) >> 16;
	u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
	int count = 0;
	u32 temp = bus.reg[base].I +
		4 * (cpuBitsSet[opcode & 0xFF] + cpuBitsSet[(opcode >> 8) & 255]);
	STMW_ALL_2;
	clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// LDMIB Rn!, {Rlist}^
static  void arm9F0(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	int base = (opcode & 0x000F0000) >> 16;
	u32 temp = bus.reg[base].I +
		4 * (cpuBitsSet[opcode & 255] + cpuBitsSet[(opcode >> 8) & 255]);
	u32 address = (bus.reg[base].I+4) & 0xFFFFFFFC;
	int count = 0;
	LDM_ALL_2;
	if (!(opcode & (1U << base)))
		bus.reg[base].I = temp;
	LDM_ALL_2B;
	clockTicks += 2 + codeTicksAccess(bus.armNextPC, BITS_32);
}

// B/BL/SWI and (unimplemented) coproc support ////////////////////////////

// B <offset>
static  void armA00(u32 opcode)
{
	int codeTicksVal = 0;
	int ct = 0;
	int offset = opcode & 0x00FFFFFF;
	if (offset & 0x00800000)
		offset |= 0xFF000000;  // negative offset
	bus.reg[15].I += offset<<2;
	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;
	ARM_PREFETCH;

	codeTicksVal = codeTicksAccessSeq32(bus.armNextPC);
	ct = codeTicksVal + 3;
	ct += 2 + codeTicksAccess(bus.armNextPC, BITS_32) + codeTicksVal;

	bus.busPrefetchCount = 0;
	clockTicks = ct;
}

// BL <offset>
static  void armB00(u32 opcode)
{
	int codeTicksVal = 0;
	int ct = 0;

	int offset = opcode & 0x00FFFFFF;
	if (offset & 0x00800000)
		offset |= 0xFF000000;  // negative offset
	bus.reg[14].I = bus.reg[15].I - 4;
	bus.reg[15].I += offset<<2;
	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;
	ARM_PREFETCH;

	codeTicksVal = codeTicksAccessSeq32(bus.armNextPC);
	ct = codeTicksVal + 3;
	ct += 2 + codeTicksAccess(bus.armNextPC, BITS_32) + codeTicksVal;

	bus.busPrefetchCount = 0;
	clockTicks = ct;
}

#define armE01 armUnknownInsn

// SWI <comment>
static  void armF00(u32 opcode)
{
	int codeTicksVal = 0;
	int ct = 0;

	codeTicksVal = codeTicksAccessSeq32(bus.armNextPC);
	ct = codeTicksVal + 3;
	ct += 2 + codeTicksAccess(bus.armNextPC, BITS_32) + codeTicksVal;

	bus.busPrefetchCount = 0;

	clockTicks = ct;
	CPUSoftwareInterrupt(opcode & 0x00FFFFFF);

}

// Instruction table //////////////////////////////////////////////////////

typedef  void (*insnfunc_t)(u32 opcode);
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
static insnfunc_t armInsnTable[4096] = {
    arm000,arm001,arm002,arm003,arm004,arm005,arm006,arm007,  // 000
    arm000,arm009,arm002,arm00B,arm004,arm_UI,arm006,arm_UI,  // 008
    arm010,arm011,arm012,arm013,arm014,arm015,arm016,arm017,  // 010
    arm010,arm019,arm012,arm01B,arm014,arm01D,arm016,arm01F,  // 018
    arm020,arm021,arm022,arm023,arm024,arm025,arm026,arm027,  // 020
    arm020,arm029,arm022,arm_UI,arm024,arm_UI,arm026,arm_UI,  // 028
    arm030,arm031,arm032,arm033,arm034,arm035,arm036,arm037,  // 030
    arm030,arm039,arm032,arm_UI,arm034,arm01D,arm036,arm01F,  // 038
    arm040,arm041,arm042,arm043,arm044,arm045,arm046,arm047,  // 040
    arm040,arm_UI,arm042,arm04B,arm044,arm_UI,arm046,arm_UI,  // 048
    arm050,arm051,arm052,arm053,arm054,arm055,arm056,arm057,  // 050
    arm050,arm_UI,arm052,arm05B,arm054,arm05D,arm056,arm05F,  // 058
    arm060,arm061,arm062,arm063,arm064,arm065,arm066,arm067,  // 060
    arm060,arm_UI,arm062,arm_UI,arm064,arm_UI,arm066,arm_UI,  // 068
    arm070,arm071,arm072,arm073,arm074,arm075,arm076,arm077,  // 070
    arm070,arm_UI,arm072,arm_UI,arm074,arm05D,arm076,arm05F,  // 078
    arm080,arm081,arm082,arm083,arm084,arm085,arm086,arm087,  // 080
    arm080,arm089,arm082,arm08B,arm084,arm_UI,arm086,arm_UI,  // 088
    arm090,arm091,arm092,arm093,arm094,arm095,arm096,arm097,  // 090
    arm090,arm099,arm092,arm09B,arm094,arm09D,arm096,arm09F,  // 098
    arm0A0,arm0A1,arm0A2,arm0A3,arm0A4,arm0A5,arm0A6,arm0A7,  // 0A0
    arm0A0,arm0A9,arm0A2,arm_UI,arm0A4,arm_UI,arm0A6,arm_UI,  // 0A8
    arm0B0,arm0B1,arm0B2,arm0B3,arm0B4,arm0B5,arm0B6,arm0B7,  // 0B0
    arm0B0,arm0B9,arm0B2,arm_UI,arm0B4,arm09D,arm0B6,arm09F,  // 0B8
    arm0C0,arm0C1,arm0C2,arm0C3,arm0C4,arm0C5,arm0C6,arm0C7,  // 0C0
    arm0C0,arm0C9,arm0C2,arm0CB,arm0C4,arm_UI,arm0C6,arm_UI,  // 0C8
    arm0D0,arm0D1,arm0D2,arm0D3,arm0D4,arm0D5,arm0D6,arm0D7,  // 0D0
    arm0D0,arm0D9,arm0D2,arm0DB,arm0D4,arm0DD,arm0D6,arm0DF,  // 0D8
    arm0E0,arm0E1,arm0E2,arm0E3,arm0E4,arm0E5,arm0E6,arm0E7,  // 0E0
    arm0E0,arm0E9,arm0E2,arm_UI,arm0E4,arm_UI,arm0E6,arm_UI,  // 0E8
    arm0F0,arm0F1,arm0F2,arm0F3,arm0F4,arm0F5,arm0F6,arm0F7,  // 0F0
    arm0F0,arm0F9,arm0F2,arm_UI,arm0F4,arm0DD,arm0F6,arm0DF,  // 0F8

    arm100,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,  // 100
    arm_UI,arm109,arm_UI,arm10B,arm_UI,arm_UI,arm_UI,arm_UI,  // 108
    arm110,arm111,arm112,arm113,arm114,arm115,arm116,arm117,  // 110
    arm110,arm_UI,arm112,arm11B,arm114,arm11D,arm116,arm11F,  // 118
    arm120,arm121,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_BP,  // 120
    arm_UI,arm_UI,arm_UI,arm12B,arm_UI,arm_UI,arm_UI,arm_UI,  // 128
    arm130,arm131,arm132,arm133,arm134,arm135,arm136,arm137,  // 130
    arm130,arm_UI,arm132,arm13B,arm134,arm13D,arm136,arm13F,  // 138
    arm140,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,  // 140
    arm_UI,arm149,arm_UI,arm14B,arm_UI,arm_UI,arm_UI,arm_UI,  // 148
    arm150,arm151,arm152,arm153,arm154,arm155,arm156,arm157,  // 150
    arm150,arm_UI,arm152,arm15B,arm154,arm15D,arm156,arm15F,  // 158
    arm160,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,arm_UI,  // 160
    arm_UI,arm_UI,arm_UI,arm16B,arm_UI,arm_UI,arm_UI,arm_UI,  // 168
    arm170,arm171,arm172,arm173,arm174,arm175,arm176,arm177,  // 170
    arm170,arm_UI,arm172,arm17B,arm174,arm17D,arm176,arm17F,  // 178
    arm180,arm181,arm182,arm183,arm184,arm185,arm186,arm187,  // 180
    arm180,arm_UI,arm182,arm18B,arm184,arm_UI,arm186,arm_UI,  // 188
    arm190,arm191,arm192,arm193,arm194,arm195,arm196,arm197,  // 190
    arm190,arm_UI,arm192,arm19B,arm194,arm19D,arm196,arm19F,  // 198
    arm1A0,arm1A1,arm1A2,arm1A3,arm1A4,arm1A5,arm1A6,arm1A7,  // 1A0
    arm1A0,arm_UI,arm1A2,arm1AB,arm1A4,arm_UI,arm1A6,arm_UI,  // 1A8
    arm1B0,arm1B1,arm1B2,arm1B3,arm1B4,arm1B5,arm1B6,arm1B7,  // 1B0
    arm1B0,arm_UI,arm1B2,arm1BB,arm1B4,arm1BD,arm1B6,arm1BF,  // 1B8
    arm1C0,arm1C1,arm1C2,arm1C3,arm1C4,arm1C5,arm1C6,arm1C7,  // 1C0
    arm1C0,arm_UI,arm1C2,arm1CB,arm1C4,arm_UI,arm1C6,arm_UI,  // 1C8
    arm1D0,arm1D1,arm1D2,arm1D3,arm1D4,arm1D5,arm1D6,arm1D7,  // 1D0
    arm1D0,arm_UI,arm1D2,arm1DB,arm1D4,arm1DD,arm1D6,arm1DF,  // 1D8
    arm1E0,arm1E1,arm1E2,arm1E3,arm1E4,arm1E5,arm1E6,arm1E7,  // 1E0
    arm1E0,arm_UI,arm1E2,arm1EB,arm1E4,arm_UI,arm1E6,arm_UI,  // 1E8
    arm1F0,arm1F1,arm1F2,arm1F3,arm1F4,arm1F5,arm1F6,arm1F7,  // 1F0
    arm1F0,arm_UI,arm1F2,arm1FB,arm1F4,arm1FD,arm1F6,arm1FF,  // 1F8

    REP16(arm200),REP16(arm210),REP16(arm220),REP16(arm230),  // 200
    REP16(arm240),REP16(arm250),REP16(arm260),REP16(arm270),  // 240
    REP16(arm280),REP16(arm290),REP16(arm2A0),REP16(arm2B0),  // 280
    REP16(arm2C0),REP16(arm2D0),REP16(arm2E0),REP16(arm2F0),  // 2C0
    REP16(arm_UI),REP16(arm310),REP16(arm320),REP16(arm330),  // 300
    REP16(arm_UI),REP16(arm350),REP16(arm360),REP16(arm370),  // 340
    REP16(arm380),REP16(arm390),REP16(arm3A0),REP16(arm3B0),  // 380
    REP16(arm3C0),REP16(arm3D0),REP16(arm3E0),REP16(arm3F0),  // 3C0

    REP16(arm400),REP16(arm410),REP16(arm400),REP16(arm410),  // 400
    REP16(arm440),REP16(arm450),REP16(arm440),REP16(arm450),  // 440
    REP16(arm480),REP16(arm490),REP16(arm480),REP16(arm490),  // 480
    REP16(arm4C0),REP16(arm4D0),REP16(arm4C0),REP16(arm4D0),  // 4C0
    REP16(arm500),REP16(arm510),REP16(arm520),REP16(arm530),  // 500
    REP16(arm540),REP16(arm550),REP16(arm560),REP16(arm570),  // 540
    REP16(arm580),REP16(arm590),REP16(arm5A0),REP16(arm5B0),  // 580
    REP16(arm5C0),REP16(arm5D0),REP16(arm5E0),REP16(arm5F0),  // 5C0

    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  // 600
    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  // 608
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  // 610
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  // 618
    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  // 620
    arm600,arm_UI,arm602,arm_UI,arm604,arm_UI,arm606,arm_UI,  // 628
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  // 630
    arm610,arm_UI,arm612,arm_UI,arm614,arm_UI,arm616,arm_UI,  // 638
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  // 640
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  // 648
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  // 650
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  // 658
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  // 660
    arm640,arm_UI,arm642,arm_UI,arm644,arm_UI,arm646,arm_UI,  // 668
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  // 670
    arm650,arm_UI,arm652,arm_UI,arm654,arm_UI,arm656,arm_UI,  // 678
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  // 680
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  // 688
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  // 690
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  // 698
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  // 6A0
    arm680,arm_UI,arm682,arm_UI,arm684,arm_UI,arm686,arm_UI,  // 6A8
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  // 6B0
    arm690,arm_UI,arm692,arm_UI,arm694,arm_UI,arm696,arm_UI,  // 6B8
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  // 6C0
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  // 6C8
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  // 6D0
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  // 6D8
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  // 6E0
    arm6C0,arm_UI,arm6C2,arm_UI,arm6C4,arm_UI,arm6C6,arm_UI,  // 6E8
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  // 6F0
    arm6D0,arm_UI,arm6D2,arm_UI,arm6D4,arm_UI,arm6D6,arm_UI,  // 6F8

    arm700,arm_UI,arm702,arm_UI,arm704,arm_UI,arm706,arm_UI,  // 700
    arm700,arm_UI,arm702,arm_UI,arm704,arm_UI,arm706,arm_UI,  // 708
    arm710,arm_UI,arm712,arm_UI,arm714,arm_UI,arm716,arm_UI,  // 710
    arm710,arm_UI,arm712,arm_UI,arm714,arm_UI,arm716,arm_UI,  // 718
    arm720,arm_UI,arm722,arm_UI,arm724,arm_UI,arm726,arm_UI,  // 720
    arm720,arm_UI,arm722,arm_UI,arm724,arm_UI,arm726,arm_UI,  // 728
    arm730,arm_UI,arm732,arm_UI,arm734,arm_UI,arm736,arm_UI,  // 730
    arm730,arm_UI,arm732,arm_UI,arm734,arm_UI,arm736,arm_UI,  // 738
    arm740,arm_UI,arm742,arm_UI,arm744,arm_UI,arm746,arm_UI,  // 740
    arm740,arm_UI,arm742,arm_UI,arm744,arm_UI,arm746,arm_UI,  // 748
    arm750,arm_UI,arm752,arm_UI,arm754,arm_UI,arm756,arm_UI,  // 750
    arm750,arm_UI,arm752,arm_UI,arm754,arm_UI,arm756,arm_UI,  // 758
    arm760,arm_UI,arm762,arm_UI,arm764,arm_UI,arm766,arm_UI,  // 760
    arm760,arm_UI,arm762,arm_UI,arm764,arm_UI,arm766,arm_UI,  // 768
    arm770,arm_UI,arm772,arm_UI,arm774,arm_UI,arm776,arm_UI,  // 770
    arm770,arm_UI,arm772,arm_UI,arm774,arm_UI,arm776,arm_UI,  // 778
    arm780,arm_UI,arm782,arm_UI,arm784,arm_UI,arm786,arm_UI,  // 780
    arm780,arm_UI,arm782,arm_UI,arm784,arm_UI,arm786,arm_UI,  // 788
    arm790,arm_UI,arm792,arm_UI,arm794,arm_UI,arm796,arm_UI,  // 790
    arm790,arm_UI,arm792,arm_UI,arm794,arm_UI,arm796,arm_UI,  // 798
    arm7A0,arm_UI,arm7A2,arm_UI,arm7A4,arm_UI,arm7A6,arm_UI,  // 7A0
    arm7A0,arm_UI,arm7A2,arm_UI,arm7A4,arm_UI,arm7A6,arm_UI,  // 7A8
    arm7B0,arm_UI,arm7B2,arm_UI,arm7B4,arm_UI,arm7B6,arm_UI,  // 7B0
    arm7B0,arm_UI,arm7B2,arm_UI,arm7B4,arm_UI,arm7B6,arm_UI,  // 7B8
    arm7C0,arm_UI,arm7C2,arm_UI,arm7C4,arm_UI,arm7C6,arm_UI,  // 7C0
    arm7C0,arm_UI,arm7C2,arm_UI,arm7C4,arm_UI,arm7C6,arm_UI,  // 7C8
    arm7D0,arm_UI,arm7D2,arm_UI,arm7D4,arm_UI,arm7D6,arm_UI,  // 7D0
    arm7D0,arm_UI,arm7D2,arm_UI,arm7D4,arm_UI,arm7D6,arm_UI,  // 7D8
    arm7E0,arm_UI,arm7E2,arm_UI,arm7E4,arm_UI,arm7E6,arm_UI,  // 7E0
    arm7E0,arm_UI,arm7E2,arm_UI,arm7E4,arm_UI,arm7E6,arm_UI,  // 7E8
    arm7F0,arm_UI,arm7F2,arm_UI,arm7F4,arm_UI,arm7F6,arm_UI,  // 7F0
    arm7F0,arm_UI,arm7F2,arm_UI,arm7F4,arm_UI,arm7F6,arm_BP,  // 7F8

    REP16(arm800),REP16(arm810),REP16(arm820),REP16(arm830),  // 800
    REP16(arm840),REP16(arm850),REP16(arm860),REP16(arm870),  // 840
    REP16(arm880),REP16(arm890),REP16(arm8A0),REP16(arm8B0),  // 880
    REP16(arm8C0),REP16(arm8D0),REP16(arm8E0),REP16(arm8F0),  // 8C0
    REP16(arm900),REP16(arm910),REP16(arm920),REP16(arm930),  // 900
    REP16(arm940),REP16(arm950),REP16(arm960),REP16(arm970),  // 940
    REP16(arm980),REP16(arm990),REP16(arm9A0),REP16(arm9B0),  // 980
    REP16(arm9C0),REP16(arm9D0),REP16(arm9E0),REP16(arm9F0),  // 9C0

    REP256(armA00),                                           // A00
    REP256(armB00),                                           // B00
    REP256(arm_UI),                                           // C00
    REP256(arm_UI),                                           // D00

    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  // E00
    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  // E08
    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  // E10
    arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,arm_UI,armE01,  // E18
    REP16(arm_UI),                                            // E20
    REP16(arm_UI),                                            // E30
    REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),  // E40
    REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),  // E80
    REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),REP16(arm_UI),  // EC0

    REP256(armF00),                                           // F00
};

// Wrapper routine (execution loop) ///////////////////////////////////////
static int armExecute (void)
{
	CACHE_PREFETCH(clockTicks);

	u32 cond1;
	u32 cond2;

	int ct = 0;

	do
	{

		clockTicks = 0;

		if ((bus.armNextPC & 0x0803FFFF) == 0x08020000)
			bus.busPrefetchCount = 0x100;

		u32 opcode = cpuPrefetch[0];
		cpuPrefetch[0] = cpuPrefetch[1];

		bus.busPrefetch = false;
		int32_t busprefetch_mask = ((bus.busPrefetchCount & 0xFFFFFE00) | -(bus.busPrefetchCount & 0xFFFFFE00)) >> 31;
		bus.busPrefetchCount = (0x100 | (bus.busPrefetchCount & 0xFF) & busprefetch_mask) | (bus.busPrefetchCount & ~busprefetch_mask);
#if 0
		if (bus.busPrefetchCount & 0xFFFFFE00)
			bus.busPrefetchCount = 0x100 | (bus.busPrefetchCount & 0xFF);
#endif


		int oldArmNextPC = bus.armNextPC;

		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 4;
		ARM_PREFETCH_NEXT;

		int cond = opcode >> 28;
		bool cond_res = true;
		if (cond != 0x0E) {  // most opcodes are AL (always)
			switch(cond) {
				case 0x00: // EQ
					cond_res = Z_FLAG;
					break;
				case 0x01: // NE
					cond_res = !Z_FLAG;
					break;
				case 0x02: // CS
					cond_res = C_FLAG;
					break;
				case 0x03: // CC
					cond_res = !C_FLAG;
					break;
				case 0x04: // MI
					cond_res = N_FLAG;
					break;
				case 0x05: // PL
					cond_res = !N_FLAG;
					break;
				case 0x06: // VS
					cond_res = V_FLAG;
					break;
				case 0x07: // VC
					cond_res = !V_FLAG;
					break;
				case 0x08: // HI
					cond_res = C_FLAG && !Z_FLAG;
					break;
				case 0x09: // LS
					cond_res = !C_FLAG || Z_FLAG;
					break;
				case 0x0A: // GE
					cond_res = N_FLAG == V_FLAG;
					break;
				case 0x0B: // LT
					cond_res = N_FLAG != V_FLAG;
					break;
				case 0x0C: // GT
					cond_res = !Z_FLAG &&(N_FLAG == V_FLAG);
					break;
				case 0x0D: // LE
					cond_res = Z_FLAG || (N_FLAG != V_FLAG);
					break;
				case 0x0E: // AL (impossible, checked above)
					cond_res = true;
					break;
				case 0x0F:
				default:
					// ???
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

		/// better pipelining

		if (ct == 0)
			clockTicks = 1 + codeTicksAccessSeq32(oldArmNextPC);

		cpuTotalTicks += clockTicks;

#ifdef USE_SWITICKS
	} while (cpuTotalTicks<cpuNextEvent && armState && !holdState && !SWITicks);
#else
} while ((cpuTotalTicks < cpuNextEvent) & armState & ~holdState);
#endif
	return 1;
}


/*============================================================
	GBA THUMB CORE
============================================================ */

static  void thumbUnknownInsn(u32 opcode)
{
	u32 PC = bus.reg[15].I;
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

// C core
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
     u32 lhs = bus.reg[source].I;\
     u32 rhs = bus.reg[N].I;\
     u32 res = lhs + rhs;\
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
     u32 lhs = bus.reg[source].I;\
     u32 rhs = N;\
     u32 res = lhs + rhs;\
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
     u32 lhs = bus.reg[(d)].I;\
     u32 rhs = (opcode & 255);\
     u32 res = lhs + rhs;\
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
     u32 lhs = bus.reg[dest].I;\
     u32 rhs = value;\
     u32 res = lhs + rhs;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     ADDCARRY(lhs, rhs, res);\
     ADDOVERFLOW(lhs, rhs, res);\
   }
#endif

#ifndef ADC_RD_RS
 #define ADC_RD_RS \
   {\
     u32 lhs = bus.reg[dest].I;\
     u32 rhs = value;\
     u32 res = lhs + rhs + (u32)C_FLAG;\
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
     u32 lhs = bus.reg[source].I;\
     u32 rhs = bus.reg[N].I;\
     u32 res = lhs - rhs;\
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
     u32 lhs = bus.reg[source].I;\
     u32 rhs = N;\
     u32 res = lhs - rhs;\
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
     u32 lhs = bus.reg[(d)].I;\
     u32 rhs = (opcode & 255);\
     u32 res = lhs - rhs;\
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
     u32 val;\
	 val = (opcode & 255);\
     bus.reg[d].I = val;\
     N_FLAG = false;\
     Z_FLAG = (val ? false : true);\
   }
#endif
#ifndef CMP_RN_O8
 #define CMP_RN_O8(d) \
   {\
     u32 lhs = bus.reg[(d)].I;\
     u32 rhs = (opcode & 255);\
     u32 res = lhs - rhs;\
     Z_FLAG = (res == 0) ? true : false;\
     N_FLAG = NEG(res) ? true : false;\
     SUBCARRY(lhs, rhs, res);\
     SUBOVERFLOW(lhs, rhs, res);\
   }
#endif
#ifndef SBC_RD_RS
 #define SBC_RD_RS \
   {\
     u32 lhs = bus.reg[dest].I;\
     u32 rhs = value;\
     u32 res = lhs - rhs - !((u32)C_FLAG);\
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
     C_FLAG = ((s32)bus.reg[source].I >> (int)(shift - 1)) & 1 ? true : false;\
     value = (s32)bus.reg[source].I >> (int)shift;\
   }
#endif
#ifndef ASR_RD_RS
 #define ASR_RD_RS \
   {\
     C_FLAG = ((s32)bus.reg[dest].I >> (int)(value - 1)) & 1 ? true : false;\
     value = (s32)bus.reg[dest].I >> (int)value;\
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
     u32 lhs = bus.reg[source].I;\
     u32 rhs = 0;\
     u32 res = rhs - lhs;\
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
     u32 lhs = bus.reg[dest].I;\
     u32 rhs = value;\
     u32 res = lhs - rhs;\
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
  u32 value;\
  OP(N);\
  bus.reg[dest].I = value;\
  N_FLAG = (value & 0x80000000 ? true : false);\
  Z_FLAG = (value ? false : true);
 #define IMM5_INSN_0(OP) \
  int dest = opcode & 0x07;\
  int source = (opcode >> 3) & 0x07;\
  u32 value;\
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

// Shift instructions /////////////////////////////////////////////////////

#define DEFINE_IMM5_INSN(OP,BASE) \
  static  void thumb##BASE##_00(u32 opcode) { IMM5_INSN_0(OP##_0); } \
  static  void thumb##BASE##_01(u32 opcode) { IMM5_INSN(OP, 1); } \
  static  void thumb##BASE##_02(u32 opcode) { IMM5_INSN(OP, 2); } \
  static  void thumb##BASE##_03(u32 opcode) { IMM5_INSN(OP, 3); } \
  static  void thumb##BASE##_04(u32 opcode) { IMM5_INSN(OP, 4); } \
  static  void thumb##BASE##_05(u32 opcode) { IMM5_INSN(OP, 5); } \
  static  void thumb##BASE##_06(u32 opcode) { IMM5_INSN(OP, 6); } \
  static  void thumb##BASE##_07(u32 opcode) { IMM5_INSN(OP, 7); } \
  static  void thumb##BASE##_08(u32 opcode) { IMM5_INSN(OP, 8); } \
  static  void thumb##BASE##_09(u32 opcode) { IMM5_INSN(OP, 9); } \
  static  void thumb##BASE##_0A(u32 opcode) { IMM5_INSN(OP,10); } \
  static  void thumb##BASE##_0B(u32 opcode) { IMM5_INSN(OP,11); } \
  static  void thumb##BASE##_0C(u32 opcode) { IMM5_INSN(OP,12); } \
  static  void thumb##BASE##_0D(u32 opcode) { IMM5_INSN(OP,13); } \
  static  void thumb##BASE##_0E(u32 opcode) { IMM5_INSN(OP,14); } \
  static  void thumb##BASE##_0F(u32 opcode) { IMM5_INSN(OP,15); } \
  static  void thumb##BASE##_10(u32 opcode) { IMM5_INSN(OP,16); } \
  static  void thumb##BASE##_11(u32 opcode) { IMM5_INSN(OP,17); } \
  static  void thumb##BASE##_12(u32 opcode) { IMM5_INSN(OP,18); } \
  static  void thumb##BASE##_13(u32 opcode) { IMM5_INSN(OP,19); } \
  static  void thumb##BASE##_14(u32 opcode) { IMM5_INSN(OP,20); } \
  static  void thumb##BASE##_15(u32 opcode) { IMM5_INSN(OP,21); } \
  static  void thumb##BASE##_16(u32 opcode) { IMM5_INSN(OP,22); } \
  static  void thumb##BASE##_17(u32 opcode) { IMM5_INSN(OP,23); } \
  static  void thumb##BASE##_18(u32 opcode) { IMM5_INSN(OP,24); } \
  static  void thumb##BASE##_19(u32 opcode) { IMM5_INSN(OP,25); } \
  static  void thumb##BASE##_1A(u32 opcode) { IMM5_INSN(OP,26); } \
  static  void thumb##BASE##_1B(u32 opcode) { IMM5_INSN(OP,27); } \
  static  void thumb##BASE##_1C(u32 opcode) { IMM5_INSN(OP,28); } \
  static  void thumb##BASE##_1D(u32 opcode) { IMM5_INSN(OP,29); } \
  static  void thumb##BASE##_1E(u32 opcode) { IMM5_INSN(OP,30); } \
  static  void thumb##BASE##_1F(u32 opcode) { IMM5_INSN(OP,31); }

// LSL Rd, Rm, #Imm 5
DEFINE_IMM5_INSN(IMM5_LSL,00)
// LSR Rd, Rm, #Imm 5
DEFINE_IMM5_INSN(IMM5_LSR,08)
// ASR Rd, Rm, #Imm 5
DEFINE_IMM5_INSN(IMM5_ASR,10)

// 3-argument ADD/SUB /////////////////////////////////////////////////////

#define DEFINE_REG3_INSN(OP,BASE) \
  static  void thumb##BASE##_0(u32 opcode) { THREEARG_INSN(OP,0); } \
  static  void thumb##BASE##_1(u32 opcode) { THREEARG_INSN(OP,1); } \
  static  void thumb##BASE##_2(u32 opcode) { THREEARG_INSN(OP,2); } \
  static  void thumb##BASE##_3(u32 opcode) { THREEARG_INSN(OP,3); } \
  static  void thumb##BASE##_4(u32 opcode) { THREEARG_INSN(OP,4); } \
  static  void thumb##BASE##_5(u32 opcode) { THREEARG_INSN(OP,5); } \
  static  void thumb##BASE##_6(u32 opcode) { THREEARG_INSN(OP,6); } \
  static  void thumb##BASE##_7(u32 opcode) { THREEARG_INSN(OP,7); }

#define DEFINE_IMM3_INSN(OP,BASE) \
  static  void thumb##BASE##_0(u32 opcode) { THREEARG_INSN(OP##_0,0); } \
  static  void thumb##BASE##_1(u32 opcode) { THREEARG_INSN(OP,1); } \
  static  void thumb##BASE##_2(u32 opcode) { THREEARG_INSN(OP,2); } \
  static  void thumb##BASE##_3(u32 opcode) { THREEARG_INSN(OP,3); } \
  static  void thumb##BASE##_4(u32 opcode) { THREEARG_INSN(OP,4); } \
  static  void thumb##BASE##_5(u32 opcode) { THREEARG_INSN(OP,5); } \
  static  void thumb##BASE##_6(u32 opcode) { THREEARG_INSN(OP,6); } \
  static  void thumb##BASE##_7(u32 opcode) { THREEARG_INSN(OP,7); }

// ADD Rd, Rs, Rn
DEFINE_REG3_INSN(ADD_RD_RS_RN,18)
// SUB Rd, Rs, Rn
DEFINE_REG3_INSN(SUB_RD_RS_RN,1A)
// ADD Rd, Rs, #Offset3
DEFINE_IMM3_INSN(ADD_RD_RS_O3,1C)
// SUB Rd, Rs, #Offset3
DEFINE_IMM3_INSN(SUB_RD_RS_O3,1E)

// MOV/CMP/ADD/SUB immediate //////////////////////////////////////////////

// MOV R0, #Offset8
static  void thumb20(u32 opcode) { MOV_RN_O8(0); }
// MOV R1, #Offset8
static  void thumb21(u32 opcode) { MOV_RN_O8(1); }
// MOV R2, #Offset8
static  void thumb22(u32 opcode) { MOV_RN_O8(2); }
// MOV R3, #Offset8
static  void thumb23(u32 opcode) { MOV_RN_O8(3); }
// MOV R4, #Offset8
static  void thumb24(u32 opcode) { MOV_RN_O8(4); }
// MOV R5, #Offset8
static  void thumb25(u32 opcode) { MOV_RN_O8(5); }
// MOV R6, #Offset8
static  void thumb26(u32 opcode) { MOV_RN_O8(6); }
// MOV R7, #Offset8
static  void thumb27(u32 opcode) { MOV_RN_O8(7); }

// CMP R0, #Offset8
static  void thumb28(u32 opcode) { CMP_RN_O8(0); }
// CMP R1, #Offset8
static  void thumb29(u32 opcode) { CMP_RN_O8(1); }
// CMP R2, #Offset8
static  void thumb2A(u32 opcode) { CMP_RN_O8(2); }
// CMP R3, #Offset8
static  void thumb2B(u32 opcode) { CMP_RN_O8(3); }
// CMP R4, #Offset8
static  void thumb2C(u32 opcode) { CMP_RN_O8(4); }
// CMP R5, #Offset8
static  void thumb2D(u32 opcode) { CMP_RN_O8(5); }
// CMP R6, #Offset8
static  void thumb2E(u32 opcode) { CMP_RN_O8(6); }
// CMP R7, #Offset8
static  void thumb2F(u32 opcode) { CMP_RN_O8(7); }

// ADD R0,#Offset8
static  void thumb30(u32 opcode) { ADD_RN_O8(0); }
// ADD R1,#Offset8
static  void thumb31(u32 opcode) { ADD_RN_O8(1); }
// ADD R2,#Offset8
static  void thumb32(u32 opcode) { ADD_RN_O8(2); }
// ADD R3,#Offset8
static  void thumb33(u32 opcode) { ADD_RN_O8(3); }
// ADD R4,#Offset8
static  void thumb34(u32 opcode) { ADD_RN_O8(4); }
// ADD R5,#Offset8
static  void thumb35(u32 opcode) { ADD_RN_O8(5); }
// ADD R6,#Offset8
static  void thumb36(u32 opcode) { ADD_RN_O8(6); }
// ADD R7,#Offset8
static  void thumb37(u32 opcode) { ADD_RN_O8(7); }

// SUB R0,#Offset8
static  void thumb38(u32 opcode) { SUB_RN_O8(0); }
// SUB R1,#Offset8
static  void thumb39(u32 opcode) { SUB_RN_O8(1); }
// SUB R2,#Offset8
static  void thumb3A(u32 opcode) { SUB_RN_O8(2); }
// SUB R3,#Offset8
static  void thumb3B(u32 opcode) { SUB_RN_O8(3); }
// SUB R4,#Offset8
static  void thumb3C(u32 opcode) { SUB_RN_O8(4); }
// SUB R5,#Offset8
static  void thumb3D(u32 opcode) { SUB_RN_O8(5); }
// SUB R6,#Offset8
static  void thumb3E(u32 opcode) { SUB_RN_O8(6); }
// SUB R7,#Offset8
static  void thumb3F(u32 opcode) { SUB_RN_O8(7); }

// ALU operations /////////////////////////////////////////////////////////

// AND Rd, Rs
static  void thumb40_0(u32 opcode)
{
  int dest = opcode & 7;
  u32 val = (bus.reg[dest].I & bus.reg[(opcode >> 3)&7].I);
  
  //bus.reg[dest].I &= bus.reg[(opcode >> 3)&7].I;
  N_FLAG = val & 0x80000000 ? true : false;
  Z_FLAG = val ? false : true;

  bus.reg[dest].I = val;

}

// EOR Rd, Rs
static  void thumb40_1(u32 opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I ^= bus.reg[(opcode >> 3)&7].I;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
  Z_FLAG = bus.reg[dest].I ? false : true;
}

// LSL Rd, Rs
static  void thumb40_2(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[(opcode >> 3)&7].B.B0;
  u32 val = value;
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

// LSR Rd, Rs
static  void thumb40_3(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[(opcode >> 3)&7].B.B0;
  u32 val = value;
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

// ASR Rd, Rs
static  void thumb41_0(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[(opcode >> 3)&7].B.B0;
  
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

// ADC Rd, Rs
static  void thumb41_1(u32 opcode)
{
  int dest = opcode & 0x07;
  u32 value = bus.reg[(opcode >> 3)&7].I;
  ADC_RD_RS;
}

// SBC Rd, Rs
static  void thumb41_2(u32 opcode)
{
  int dest = opcode & 0x07;
  u32 value = bus.reg[(opcode >> 3)&7].I;
  SBC_RD_RS;
}

// ROR Rd, Rs
static  void thumb41_3(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[(opcode >> 3)&7].B.B0;
  u32 val = value;
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

// TST Rd, Rs
static  void thumb42_0(u32 opcode)
{
  u32 value = bus.reg[opcode & 7].I & bus.reg[(opcode >> 3) & 7].I;
  N_FLAG = value & 0x80000000 ? true : false;
  Z_FLAG = value ? false : true;
}

// NEG Rd, Rs
static  void thumb42_1(u32 opcode)
{
  int dest = opcode & 7;
  int source = (opcode >> 3) & 7;
  NEG_RD_RS;
}

// CMP Rd, Rs
static  void thumb42_2(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[(opcode >> 3)&7].I;
  CMP_RD_RS;
}

// CMN Rd, Rs
static  void thumb42_3(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[(opcode >> 3)&7].I;
  CMN_RD_RS;
}

// ORR Rd, Rs
static  void thumb43_0(u32 opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I |= bus.reg[(opcode >> 3) & 7].I;
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

// MUL Rd, Rs
static  void thumb43_1(u32 opcode)
{
  clockTicks = 1;
  int dest = opcode & 7;
  u32 rm = bus.reg[dest].I;
  bus.reg[dest].I = bus.reg[(opcode >> 3) & 7].I * rm;
  if (((s32)rm) < 0)
    rm = ~rm;
  if ((rm & 0xFFFF0000) == 0)
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

// BIC Rd, Rs
static  void thumb43_2(u32 opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I &= (~bus.reg[(opcode >> 3) & 7].I);
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

// MVN Rd, Rs
static  void thumb43_3(u32 opcode)
{
  int dest = opcode & 7;
  bus.reg[dest].I = ~bus.reg[(opcode >> 3) & 7].I;
  Z_FLAG = bus.reg[dest].I ? false : true;
  N_FLAG = bus.reg[dest].I & 0x80000000 ? true : false;
}

// High-register instructions and BX //////////////////////////////////////

// ADD Rd, Hs
static  void thumb44_1(u32 opcode)
{
  bus.reg[opcode&7].I += bus.reg[((opcode>>3)&7)+8].I;
}

// ADD Hd, Rs
static  void thumb44_2(u32 opcode)
{
  bus.reg[(opcode&7)+8].I += bus.reg[(opcode>>3)&7].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = codeTicksAccessSeq16(bus.armNextPC)<<1
        + codeTicksAccess(bus.armNextPC, BITS_16) + 3;
  }
}

// ADD Hd, Hs
static  void thumb44_3(u32 opcode)
{
  bus.reg[(opcode&7)+8].I += bus.reg[((opcode>>3)&7)+8].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = codeTicksAccessSeq16(bus.armNextPC)<<1
        + codeTicksAccess(bus.armNextPC, BITS_16) + 3;
  }
}

// CMP Rd, Hs
static  void thumb45_1(u32 opcode)
{
  int dest = opcode & 7;
  u32 value = bus.reg[((opcode>>3)&7)+8].I;
  CMP_RD_RS;
}

// CMP Hd, Rs
static  void thumb45_2(u32 opcode)
{
  int dest = (opcode & 7) + 8;
  u32 value = bus.reg[(opcode>>3)&7].I;
  CMP_RD_RS;
}

// CMP Hd, Hs
static  void thumb45_3(u32 opcode)
{
  int dest = (opcode & 7) + 8;
  u32 value = bus.reg[((opcode>>3)&7)+8].I;
  CMP_RD_RS;
}

// MOV Rd, Hs
static  void thumb46_1(u32 opcode)
{
  bus.reg[opcode&7].I = bus.reg[((opcode>>3)&7)+8].I;
}

// MOV Hd, Rs
static  void thumb46_2(u32 opcode)
{
  bus.reg[(opcode&7)+8].I = bus.reg[(opcode>>3)&7].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = codeTicksAccessSeq16(bus.armNextPC)<<1
        + codeTicksAccess(bus.armNextPC, BITS_16) + 3;
  }
}

// MOV Hd, Hs
static  void thumb46_3(u32 opcode)
{
  bus.reg[(opcode&7)+8].I = bus.reg[((opcode>>3)&7)+8].I;
  if((opcode&7) == 7) {
    bus.reg[15].I &= 0xFFFFFFFE;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = codeTicksAccessSeq16(bus.armNextPC)<<1
        + codeTicksAccess(bus.armNextPC, BITS_16) + 3;
  }
}


// BX Rs
static  void thumb47(u32 opcode)
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
		clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1)
			+ codeTicksAccess(bus.armNextPC, BITS_16) + 3;
	} else {
		armState = true;
		bus.reg[15].I &= 0xFFFFFFFC;
		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 4;
		ARM_PREFETCH;
		clockTicks = ((codeTicksAccessSeq32(bus.armNextPC)) << 1) 
			+ codeTicksAccess(bus.armNextPC, BITS_32) + 3;
	}
}

// Load/store instructions ////////////////////////////////////////////////

// LDR R0~R7,[PC, #Imm]
static  void thumb48(u32 opcode)
{
	u8 regist = (opcode >> 8) & 7;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = (bus.reg[15].I & 0xFFFFFFFC) + ((opcode & 0xFF) << 2);
	bus.reg[regist].I = CPUReadMemoryQuick(address);
	bus.busPrefetchCount=0;
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// STR Rd, [Rs, Rn]
static  void thumb50(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	CPUWriteMemory(address, bus.reg[opcode & 7].I);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// STRH Rd, [Rs, Rn]
static  void thumb52(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	CPUWriteHalfWord(address, bus.reg[opcode&7].W.W0);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// STRB Rd, [Rs, Rn]
static  void thumb54(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode >>6)&7].I;
	CPUWriteByte(address, bus.reg[opcode & 7].B.B0);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// LDSB Rd, [Rs, Rn]
static  void thumb56(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = (s8)CPUReadByte(address);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// LDR Rd, [Rs, Rn]
static  void thumb58(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = CPUReadMemory(address);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// LDRH Rd, [Rs, Rn]
static  void thumb5A(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = CPUReadHalfWord(address);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// LDRB Rd, [Rs, Rn]
static  void thumb5C(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = CPUReadByte(address);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// LDSH Rd, [Rs, Rn]
static  void thumb5E(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + bus.reg[(opcode>>6)&7].I;
	bus.reg[opcode&7].I = (s16)CPUReadHalfWordSigned(address);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// STR Rd, [Rs, #Imm]
static  void thumb60(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<2);
	CPUWriteMemory(address, bus.reg[opcode&7].I);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// LDR Rd, [Rs, #Imm]
static  void thumb68(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<2);
	bus.reg[opcode&7].I = CPUReadMemory(address);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// STRB Rd, [Rs, #Imm]
static  void thumb70(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31));
	CPUWriteByte(address, bus.reg[opcode&7].B.B0);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// LDRB Rd, [Rs, #Imm]
static  void thumb78(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31));
	bus.reg[opcode&7].I = CPUReadByte(address);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// STRH Rd, [Rs, #Imm]
static  void thumb80(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<1);
	CPUWriteHalfWord(address, bus.reg[opcode&7].W.W0);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// LDRH Rd, [Rs, #Imm]
static  void thumb88(u32 opcode)
{
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[(opcode>>3)&7].I + (((opcode>>6)&31)<<1);
	bus.reg[opcode&7].I = CPUReadHalfWord(address);
	int dataticks_value = DATATICKS_ACCESS_16BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// STR R0~R7, [SP, #Imm]
static  void thumb90(u32 opcode)
{
	u8 regist = (opcode >> 8) & 7;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[13].I + ((opcode&255)<<2);
	CPUWriteMemory(address, bus.reg[regist].I);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16) + 2;
}

// LDR R0~R7, [SP, #Imm]
static  void thumb98(u32 opcode)
{
	u8 regist = (opcode >> 8) & 7;
	if (bus.busPrefetchCount == 0)
		bus.busPrefetch = bus.busPrefetchEnable;
	u32 address = bus.reg[13].I + ((opcode&255)<<2);
	bus.reg[regist].I = CPUReadMemoryQuick(address);
	int dataticks_value = DATATICKS_ACCESS_32BIT(address);
	DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
	clockTicks = 3 + dataticks_value + codeTicksAccess(bus.armNextPC, BITS_16);
}

// PC/stack-related ///////////////////////////////////////////////////////

// ADD R0~R7, PC, Imm
static  void thumbA0(u32 opcode)
{
  u8 regist = (opcode >> 8) & 7;
  bus.reg[regist].I = (bus.reg[15].I & 0xFFFFFFFC) + ((opcode&255)<<2);
}

// ADD R0~R7, SP, Imm
static  void thumbA8(u32 opcode)
{
  u8 regist = (opcode >> 8) & 7;
  bus.reg[regist].I = bus.reg[13].I + ((opcode&255)<<2);
}

// ADD SP, Imm
static  void thumbB0(u32 opcode)
{
  int offset = (opcode & 127) << 2;
  if(opcode & 0x80)
    offset = -offset;
  bus.reg[13].I += offset;
}

// Push and pop ///////////////////////////////////////////////////////////

#define PUSH_REG(val, r)                                    \
  if (opcode & (val)) {                                     \
    CPUWriteMemory(address, bus.reg[(r)].I);                    \
    int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
    clockTicks += 1 + dataticks_value;				\
    count++;                                                \
    address += 4;                                           \
  }

#define POP_REG(val, r)                                     \
  if (opcode & (val)) {                                     \
    bus.reg[(r)].I = CPUReadMemory(address);                    \
int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value); \
    clockTicks += 1 + dataticks_value; \
    count++;                                                \
    address += 4;                                           \
  }

// PUSH {Rlist}
static  void thumbB4(u32 opcode)
{
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  int count = 0;
  u32 temp = bus.reg[13].I - 4 * cpuBitsSet[opcode & 0xff];
  u32 address = temp & 0xFFFFFFFC;
  PUSH_REG(1, 0);
  PUSH_REG(2, 1);
  PUSH_REG(4, 2);
  PUSH_REG(8, 3);
  PUSH_REG(16, 4);
  PUSH_REG(32, 5);
  PUSH_REG(64, 6);
  PUSH_REG(128, 7);
  clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_16);
  bus.reg[13].I = temp;
}

// PUSH {Rlist, LR}
static  void thumbB5(u32 opcode)
{
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  int count = 0;
  u32 temp = bus.reg[13].I - 4 - 4 * cpuBitsSet[opcode & 0xff];
  u32 address = temp & 0xFFFFFFFC;
  PUSH_REG(1, 0);
  PUSH_REG(2, 1);
  PUSH_REG(4, 2);
  PUSH_REG(8, 3);
  PUSH_REG(16, 4);
  PUSH_REG(32, 5);
  PUSH_REG(64, 6);
  PUSH_REG(128, 7);
  PUSH_REG(256, 14);
  clockTicks += 1 + codeTicksAccess(bus.armNextPC, BITS_16);
  bus.reg[13].I = temp;
}

// POP {Rlist}
static  void thumbBC(u32 opcode)
{
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  int count = 0;
  u32 address = bus.reg[13].I & 0xFFFFFFFC;
  u32 temp = bus.reg[13].I + 4*cpuBitsSet[opcode & 0xFF];
  POP_REG(1, 0);
  POP_REG(2, 1);
  POP_REG(4, 2);
  POP_REG(8, 3);
  POP_REG(16, 4);
  POP_REG(32, 5);
  POP_REG(64, 6);
  POP_REG(128, 7);
  bus.reg[13].I = temp;
  clockTicks = 2 + codeTicksAccess(bus.armNextPC, BITS_16);
}

// POP {Rlist, PC}
static  void thumbBD(u32 opcode)
{
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  int count = 0;
  u32 address = bus.reg[13].I & 0xFFFFFFFC;
  u32 temp = bus.reg[13].I + 4 + 4*cpuBitsSet[opcode & 0xFF];
  POP_REG(1, 0);
  POP_REG(2, 1);
  POP_REG(4, 2);
  POP_REG(8, 3);
  POP_REG(16, 4);
  POP_REG(32, 5);
  POP_REG(64, 6);
  POP_REG(128, 7);
  bus.reg[15].I = (CPUReadMemory(address) & 0xFFFFFFFE);
  int dataticks_value = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address);
  DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_value);
  clockTicks += 1 + dataticks_value;
  count++;
  bus.armNextPC = bus.reg[15].I;
  bus.reg[15].I += 2;
  bus.reg[13].I = temp;
  THUMB_PREFETCH;
  bus.busPrefetchCount = 0;
  clockTicks += 3 + ((codeTicksAccess(bus.armNextPC, BITS_16)) << 1);
}

// Load/store multiple ////////////////////////////////////////////////////

#define THUMB_STM_REG(val,r,b)                              \
  if(opcode & (val)) {                                      \
    CPUWriteMemory(address, bus.reg[(r)].I);                    \
    bus.reg[(b)].I = temp;                                      \
    int dataticks_val = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_val); \
    clockTicks += 1 + dataticks_val; \
    count++;                                                \
    address += 4;                                           \
  }

#define THUMB_LDM_REG(val,r)                                \
  if(opcode & (val)) {                                      \
    bus.reg[(r)].I = CPUReadMemory(address);                    \
    int dataticks_val = count ? DATATICKS_ACCESS_32BIT_SEQ(address) : DATATICKS_ACCESS_32BIT(address); \
    DATATICKS_ACCESS_BUS_PREFETCH(address, dataticks_val); \
    clockTicks += 1 + dataticks_val; \
    count++;                                                \
    address += 4;                                           \
  }

// STM R0~7!, {Rlist}
static  void thumbC0(u32 opcode)
{
  u8 regist = (opcode >> 8) & 7;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  u32 address = bus.reg[regist].I & 0xFFFFFFFC;
  u32 temp = bus.reg[regist].I + 4*cpuBitsSet[opcode & 0xff];
  int count = 0;
  // store
  THUMB_STM_REG(1, 0, regist);
  THUMB_STM_REG(2, 1, regist);
  THUMB_STM_REG(4, 2, regist);
  THUMB_STM_REG(8, 3, regist);
  THUMB_STM_REG(16, 4, regist);
  THUMB_STM_REG(32, 5, regist);
  THUMB_STM_REG(64, 6, regist);
  THUMB_STM_REG(128, 7, regist);
  clockTicks = 1 + codeTicksAccess(bus.armNextPC, BITS_16);
}

// LDM R0~R7!, {Rlist}
static  void thumbC8(u32 opcode)
{
  u8 regist = (opcode >> 8) & 7;
  if (bus.busPrefetchCount == 0)
    bus.busPrefetch = bus.busPrefetchEnable;
  u32 address = bus.reg[regist].I & 0xFFFFFFFC;
  u32 temp = bus.reg[regist].I + 4*cpuBitsSet[opcode & 0xFF];
  int count = 0;
  // load
  THUMB_LDM_REG(1, 0);
  THUMB_LDM_REG(2, 1);
  THUMB_LDM_REG(4, 2);
  THUMB_LDM_REG(8, 3);
  THUMB_LDM_REG(16, 4);
  THUMB_LDM_REG(32, 5);
  THUMB_LDM_REG(64, 6);
  THUMB_LDM_REG(128, 7);
  clockTicks = 2 + codeTicksAccess(bus.armNextPC, BITS_16);
  if(!(opcode & (1<<regist)))
    bus.reg[regist].I = temp;
}

// Conditional branches ///////////////////////////////////////////////////

// BEQ offset
static  void thumbD0(u32 opcode)
{
	if(Z_FLAG)
	{
		bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 2;
		THUMB_PREFETCH;
#if defined (SPEEDHAX)
		clockTicks = 30;
#else
		clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
			codeTicksAccess(bus.armNextPC, BITS_16)+3;
#endif
		bus.busPrefetchCount=0;
	}
}

// BNE offset
static  void thumbD1(u32 opcode)
{
  if(!Z_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BCS offset
static  void thumbD2(u32 opcode)
{
  if(C_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BCC offset
static  void thumbD3(u32 opcode)
{
  if(!C_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BMI offset
static  void thumbD4(u32 opcode)
{
  if(N_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BPL offset
static  void thumbD5(u32 opcode)
{
  if(!N_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BVS offset
static  void thumbD6(u32 opcode)
{
  if(V_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BVC offset
static  void thumbD7(u32 opcode)
{
  if(!V_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BHI offset
static  void thumbD8(u32 opcode)
{
  if(C_FLAG && !Z_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BLS offset
static  void thumbD9(u32 opcode)
{
  if(!C_FLAG || Z_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BGE offset
static  void thumbDA(u32 opcode)
{
  if(N_FLAG == V_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BLT offset
static  void thumbDB(u32 opcode)
{
  if(N_FLAG != V_FLAG) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BGT offset
static  void thumbDC(u32 opcode)
{
  if(!Z_FLAG && (N_FLAG == V_FLAG)) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = (codeTicksAccessSeq16(bus.armNextPC) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// BLE offset
static  void thumbDD(u32 opcode)
{
  if(Z_FLAG || (N_FLAG != V_FLAG)) {
    bus.reg[15].I += ((s8)(opcode & 0xFF)) << 1;
    bus.armNextPC = bus.reg[15].I;
    bus.reg[15].I += 2;
    THUMB_PREFETCH;
    clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
        codeTicksAccess(bus.armNextPC, BITS_16)+3;
    bus.busPrefetchCount=0;
  }
}

// SWI, B, BL /////////////////////////////////////////////////////////////

// SWI #comment
static  void thumbDF(u32 opcode)
{
  u32 address = 0;
  clockTicks = ((codeTicksAccessSeq16(address)) << 1) +
      codeTicksAccess(address, BITS_16)+3;
  bus.busPrefetchCount=0;
  CPUSoftwareInterrupt(opcode & 0xFF);
}

// B offset
static  void thumbE0(u32 opcode)
{
  int offset = (opcode & 0x3FF) << 1;
  if(opcode & 0x0400)
    offset |= 0xFFFFF800;
  bus.reg[15].I += offset;
  bus.armNextPC = bus.reg[15].I;
  bus.reg[15].I += 2;
  THUMB_PREFETCH;
  clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
      codeTicksAccess(bus.armNextPC, BITS_16) + 3;
  bus.busPrefetchCount=0;
}

// BLL #offset (forward)
static  void thumbF0(u32 opcode)
{
  int offset = (opcode & 0x7FF);
  bus.reg[14].I = bus.reg[15].I + (offset << 12);
  clockTicks = codeTicksAccessSeq16(bus.armNextPC) + 1;
}

// BLL #offset (backward)
static  void thumbF4(u32 opcode)
{
  int offset = (opcode & 0x7FF);
  bus.reg[14].I = bus.reg[15].I + ((offset << 12) | 0xFF800000);
  clockTicks = codeTicksAccessSeq16(bus.armNextPC) + 1;
}

// BLH #offset
static  void thumbF8(u32 opcode)
{
  int offset = (opcode & 0x7FF);
  u32 temp = bus.reg[15].I-2;
  bus.reg[15].I = (bus.reg[14].I + (offset<<1))&0xFFFFFFFE;
  bus.armNextPC = bus.reg[15].I;
  bus.reg[15].I += 2;
  bus.reg[14].I = temp|1;
  THUMB_PREFETCH;
  clockTicks = ((codeTicksAccessSeq16(bus.armNextPC)) << 1) +
      codeTicksAccess(bus.armNextPC, BITS_16) + 3;
  bus.busPrefetchCount = 0;
}

// Instruction table //////////////////////////////////////////////////////

typedef  void (*insnfunc_t)(u32 opcode);
#define thumbUI thumbUnknownInsn
#define thumbBP thumbUnknownInsn
static insnfunc_t thumbInsnTable[1024] = {
  thumb00_00,thumb00_01,thumb00_02,thumb00_03,thumb00_04,thumb00_05,thumb00_06,thumb00_07,  // 00
  thumb00_08,thumb00_09,thumb00_0A,thumb00_0B,thumb00_0C,thumb00_0D,thumb00_0E,thumb00_0F,
  thumb00_10,thumb00_11,thumb00_12,thumb00_13,thumb00_14,thumb00_15,thumb00_16,thumb00_17,
  thumb00_18,thumb00_19,thumb00_1A,thumb00_1B,thumb00_1C,thumb00_1D,thumb00_1E,thumb00_1F,
  thumb08_00,thumb08_01,thumb08_02,thumb08_03,thumb08_04,thumb08_05,thumb08_06,thumb08_07,  // 08
  thumb08_08,thumb08_09,thumb08_0A,thumb08_0B,thumb08_0C,thumb08_0D,thumb08_0E,thumb08_0F,
  thumb08_10,thumb08_11,thumb08_12,thumb08_13,thumb08_14,thumb08_15,thumb08_16,thumb08_17,
  thumb08_18,thumb08_19,thumb08_1A,thumb08_1B,thumb08_1C,thumb08_1D,thumb08_1E,thumb08_1F,
  thumb10_00,thumb10_01,thumb10_02,thumb10_03,thumb10_04,thumb10_05,thumb10_06,thumb10_07,  // 10
  thumb10_08,thumb10_09,thumb10_0A,thumb10_0B,thumb10_0C,thumb10_0D,thumb10_0E,thumb10_0F,
  thumb10_10,thumb10_11,thumb10_12,thumb10_13,thumb10_14,thumb10_15,thumb10_16,thumb10_17,
  thumb10_18,thumb10_19,thumb10_1A,thumb10_1B,thumb10_1C,thumb10_1D,thumb10_1E,thumb10_1F,
  thumb18_0,thumb18_1,thumb18_2,thumb18_3,thumb18_4,thumb18_5,thumb18_6,thumb18_7,          // 18
  thumb1A_0,thumb1A_1,thumb1A_2,thumb1A_3,thumb1A_4,thumb1A_5,thumb1A_6,thumb1A_7,
  thumb1C_0,thumb1C_1,thumb1C_2,thumb1C_3,thumb1C_4,thumb1C_5,thumb1C_6,thumb1C_7,
  thumb1E_0,thumb1E_1,thumb1E_2,thumb1E_3,thumb1E_4,thumb1E_5,thumb1E_6,thumb1E_7,
  thumb20,thumb20,thumb20,thumb20,thumb21,thumb21,thumb21,thumb21,  // 20
  thumb22,thumb22,thumb22,thumb22,thumb23,thumb23,thumb23,thumb23,
  thumb24,thumb24,thumb24,thumb24,thumb25,thumb25,thumb25,thumb25,
  thumb26,thumb26,thumb26,thumb26,thumb27,thumb27,thumb27,thumb27,
  thumb28,thumb28,thumb28,thumb28,thumb29,thumb29,thumb29,thumb29,  // 28
  thumb2A,thumb2A,thumb2A,thumb2A,thumb2B,thumb2B,thumb2B,thumb2B,
  thumb2C,thumb2C,thumb2C,thumb2C,thumb2D,thumb2D,thumb2D,thumb2D,
  thumb2E,thumb2E,thumb2E,thumb2E,thumb2F,thumb2F,thumb2F,thumb2F,
  thumb30,thumb30,thumb30,thumb30,thumb31,thumb31,thumb31,thumb31,  // 30
  thumb32,thumb32,thumb32,thumb32,thumb33,thumb33,thumb33,thumb33,
  thumb34,thumb34,thumb34,thumb34,thumb35,thumb35,thumb35,thumb35,
  thumb36,thumb36,thumb36,thumb36,thumb37,thumb37,thumb37,thumb37,
  thumb38,thumb38,thumb38,thumb38,thumb39,thumb39,thumb39,thumb39,  // 38
  thumb3A,thumb3A,thumb3A,thumb3A,thumb3B,thumb3B,thumb3B,thumb3B,
  thumb3C,thumb3C,thumb3C,thumb3C,thumb3D,thumb3D,thumb3D,thumb3D,
  thumb3E,thumb3E,thumb3E,thumb3E,thumb3F,thumb3F,thumb3F,thumb3F,
  thumb40_0,thumb40_1,thumb40_2,thumb40_3,thumb41_0,thumb41_1,thumb41_2,thumb41_3,  // 40
  thumb42_0,thumb42_1,thumb42_2,thumb42_3,thumb43_0,thumb43_1,thumb43_2,thumb43_3,
  thumbUI,thumb44_1,thumb44_2,thumb44_3,thumbUI,thumb45_1,thumb45_2,thumb45_3,
  thumbUI,thumb46_1,thumb46_2,thumb46_3,thumb47,thumb47,thumbUI,thumbUI,
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,  // 48
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,
  thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,thumb48,
  thumb50,thumb50,thumb50,thumb50,thumb50,thumb50,thumb50,thumb50,  // 50
  thumb52,thumb52,thumb52,thumb52,thumb52,thumb52,thumb52,thumb52,
  thumb54,thumb54,thumb54,thumb54,thumb54,thumb54,thumb54,thumb54,
  thumb56,thumb56,thumb56,thumb56,thumb56,thumb56,thumb56,thumb56,
  thumb58,thumb58,thumb58,thumb58,thumb58,thumb58,thumb58,thumb58,  // 58
  thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,thumb5A,
  thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,thumb5C,
  thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,thumb5E,
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,  // 60
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,
  thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,thumb60,
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,  // 68
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,
  thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,thumb68,
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,  // 70
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,
  thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,thumb70,
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,  // 78
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,
  thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,thumb78,
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,  // 80
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,
  thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,thumb80,
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,  // 88
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,
  thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,thumb88,
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,  // 90
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,
  thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,thumb90,
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,  // 98
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,
  thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,thumb98,
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,  // A0
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,
  thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,thumbA0,
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,  // A8
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,
  thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,thumbA8,
  thumbB0,thumbB0,thumbB0,thumbB0,thumbUI,thumbUI,thumbUI,thumbUI,  // B0
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbB4,thumbB4,thumbB4,thumbB4,thumbB5,thumbB5,thumbB5,thumbB5,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,  // B8
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbBC,thumbBC,thumbBC,thumbBC,thumbBD,thumbBD,thumbBD,thumbBD,
  thumbBP,thumbBP,thumbBP,thumbBP,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,  // C0
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,
  thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,thumbC0,
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,  // C8
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,
  thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,thumbC8,
  thumbD0,thumbD0,thumbD0,thumbD0,thumbD1,thumbD1,thumbD1,thumbD1,  // D0
  thumbD2,thumbD2,thumbD2,thumbD2,thumbD3,thumbD3,thumbD3,thumbD3,
  thumbD4,thumbD4,thumbD4,thumbD4,thumbD5,thumbD5,thumbD5,thumbD5,
  thumbD6,thumbD6,thumbD6,thumbD6,thumbD7,thumbD7,thumbD7,thumbD7,
  thumbD8,thumbD8,thumbD8,thumbD8,thumbD9,thumbD9,thumbD9,thumbD9,  // D8
  thumbDA,thumbDA,thumbDA,thumbDA,thumbDB,thumbDB,thumbDB,thumbDB,
  thumbDC,thumbDC,thumbDC,thumbDC,thumbDD,thumbDD,thumbDD,thumbDD,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbDF,thumbDF,thumbDF,thumbDF,
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,  // E0
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,
  thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,thumbE0,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,  // E8
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,thumbUI,
  thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,  // F0
  thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,thumbF0,
  thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,
  thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,thumbF4,
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,  // F8
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,
  thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,thumbF8,
};

// Wrapper routine (execution loop) ///////////////////////////////////////


static int thumbExecute (void)
{
	CACHE_PREFETCH(clockTicks);

	int ct = 0;

	do {

		clockTicks = 0;

#if 0
		if ((bus.armNextPC & 0x0803FFFF) == 0x08020000)
		   bus.busPrefetchCount=0x100;
#endif

		u32 opcode = cpuPrefetch[0];
		cpuPrefetch[0] = cpuPrefetch[1];

		bus.busPrefetch = false;
#if 0
		if (bus.busPrefetchCount & 0xFFFFFF00)
			bus.busPrefetchCount = 0x100 | (bus.busPrefetchCount & 0xFF);
#endif

		u32 oldArmNextPC = bus.armNextPC;

		bus.armNextPC = bus.reg[15].I;
		bus.reg[15].I += 2;
		THUMB_PREFETCH_NEXT;

		(*thumbInsnTable[opcode>>6])(opcode);

		ct = clockTicks;

		if (ct < 0)
			return 0;

		/// better pipelining
		if (ct==0)
			clockTicks = codeTicksAccessSeq16(oldArmNextPC) + 1;

		cpuTotalTicks += clockTicks;


#ifdef USE_SWITICKS
	} while (cpuTotalTicks < cpuNextEvent && !armState && !holdState && !SWITicks);
#else
} while ((cpuTotalTicks < cpuNextEvent) & ~armState & ~holdState);
#endif
	return 1;
}


/*============================================================
	GBA GFX
============================================================ */

static u32 map_widths[] = { 256, 512, 256, 512 };
static u32 map_heights[] = { 256, 256, 512, 512 };

#ifdef TILED_RENDERING
#ifdef _MSC_VER
union u8h
{
   __pragma( pack(push, 1));
   struct
#ifdef LSB_FIRST
   {
      /* 0*/	unsigned char lo:4;
      /* 4*/	unsigned char hi:4;
#else
   {
      /* 4*/	unsigned char hi:4;
      /* 0*/	unsigned char lo:4;
#endif
   }
   __pragma(pack(pop));
   u8 val;
};
#else
union u8h
{
   struct
#ifdef LSB_FIRST
   {
      /* 0*/	unsigned lo:4;
      /* 4*/	unsigned hi:4;
#else
   {
      /* 4*/	unsigned hi:4;
      /* 0*/	unsigned lo:4;
#endif
   } __attribute__ ((packed));
   u8 val;
};
#endif

union TileEntry
{
#ifdef LSB_FIRST
   struct
   {
      /* 0*/	unsigned tileNum:10;
      /*12*/	unsigned hFlip:1;
      /*13*/	unsigned vFlip:1;
      /*14*/	unsigned palette:4;
   };
#else
   struct
   {
      /*14*/	unsigned palette:4;
      /*13*/	unsigned vFlip:1;
      /*12*/	unsigned hFlip:1;
      /* 0*/	unsigned tileNum:10;
   };
#endif
   u16 val;
};

struct TileLine
{
   u32 pixels[8];
};

typedef const TileLine (*TileReader) (const u16 *, const int, const u8 *, u16 *, const u32);

static inline void gfxDrawPixel(u32 *dest, const u8 color, const u16 *palette, const u32 prio)
{
   *dest = color ? (READ16LE(&palette[color]) | prio): 0x80000000;
}

inline const TileLine gfxReadTile(const u16 *screenSource, const int yyy, const u8 *charBase, u16 *palette, const u32 prio)
{
   TileEntry tile;
   tile.val = READ16LE(screenSource);

   int tileY = yyy & 7;
   if (tile.vFlip) tileY = 7 - tileY;
   TileLine tileLine;

   const u8 *tileBase = &charBase[tile.tileNum * 64 + tileY * 8];

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

inline const TileLine gfxReadTilePal(const u16 *screenSource, const int yyy, const u8 *charBase, u16 *palette, const u32 prio)
{
   TileEntry tile;
   tile.val = READ16LE(screenSource);

   int tileY = yyy & 7;
   if (tile.vFlip) tileY = 7 - tileY;
   palette += tile.palette * 16;
   TileLine tileLine;

   const u8h *tileBase = (u8h*) &charBase[tile.tileNum * 32 + tileY * 4];

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

static inline void gfxDrawTile(const TileLine &tileLine, u32 *line)
{
   memcpy(line, tileLine.pixels, sizeof(tileLine.pixels));
}

static inline void gfxDrawTileClipped(const TileLine &tileLine, u32 *line, const int start, int w)
{
   memcpy(line, tileLine.pixels + start, w * sizeof(u32));
}

template<TileReader readTile>
static void gfxDrawTextScreen(u16 control, u16 hofs, u16 vofs,
                       u32 *line)
{
   u16 *palette = (u16 *)graphics.paletteRAM;
   u8 *charBase = &vram[((control >> 2) & 0x03) * 0x4000];
   u16 *screenBase = (u16 *)&vram[((control >> 8) & 0x1f) * 0x800];
   u32 prio = ((control & 3)<<25) + 0x1000000;
   int sizeX = 256;
   int sizeY = 256;
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

   int maskX = sizeX-1;
   int maskY = sizeY-1;

   bool mosaicOn = (control & 0x40) ? true : false;

   int xxx = hofs & maskX;
   int yyy = (vofs + io_registers[REG_VCOUNT]) & maskY;
   int mosaicX = (MOSAIC & 0x000F)+1;
   int mosaicY = ((MOSAIC & 0x00F0)>>4)+1;

   if (mosaicOn)
   {
      if ((io_registers[REG_VCOUNT] % mosaicY) != 0)
      {
         mosaicY = io_registers[REG_VCOUNT] - (io_registers[REG_VCOUNT] % mosaicY);
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

   int yshift = ((yyy>>3)<<5);

   u16 *screenSource = screenBase + 0x400 * (xxx>>8) + ((xxx & 255)>>3) + yshift;
   int x = 0;
   const int firstTileX = xxx & 7;

   // First tile, if clipped
   if (firstTileX)
   {
      gfxDrawTileClipped(readTile(screenSource, yyy, charBase, palette, prio), &line[x], firstTileX, 8 - firstTileX);
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

   // Middle tiles, full
   while (x < 240 - firstTileX)
   {
      gfxDrawTile(readTile(screenSource, yyy, charBase, palette, prio), &line[x]);
      screenSource++;
      xxx += 8;
      x += 8;

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

   // Last tile, if clipped
   if (firstTileX)
   {
      gfxDrawTileClipped(readTile(screenSource, yyy, charBase, palette, prio), &line[x], 0, firstTileX);
   }

   if (mosaicOn)
   {
      if (mosaicX > 1)
      {
         int m = 1;
         for (int i = 0; i < 239; i++)
         {
            line[i+1] = line[i];
            m++;
            if (m == mosaicX)
            {
               m = 1;
               i++;
            }
         }
      }
   }
}

void gfxDrawTextScreen(u16 control, u16 hofs, u16 vofs, u32 *line)
{
   if (control & 0x80) // 1 pal / 256 col
      gfxDrawTextScreen<gfxReadTile>(control, hofs, vofs, line);
   else // 16 pal / 16 col
      gfxDrawTextScreen<gfxReadTilePal>(control, hofs, vofs, line);
}
#else
static inline void gfxDrawTextScreen(u16 control, u16 hofs, u16 vofs,
				     u32 *line)
{
  u16 *palette = (u16 *)graphics.paletteRAM;
  u8 *charBase = &vram[((control >> 2) & 0x03) * 0x4000];
  u16 *screenBase = (u16 *)&vram[((control >> 8) & 0x1f) * 0x800];
  u32 prio = ((control & 3)<<25) + 0x1000000;
  int sizeX = 256;
  int sizeY = 256;
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

  int maskX = sizeX-1;
  int maskY = sizeY-1;

  bool mosaicOn = (control & 0x40) ? true : false;

  int xxx = hofs & maskX;
  int yyy = (vofs + io_registers[REG_VCOUNT]) & maskY;
  int mosaicX = (MOSAIC & 0x000F)+1;
  int mosaicY = ((MOSAIC & 0x00F0)>>4)+1;

  if(mosaicOn) {
    if((io_registers[REG_VCOUNT] % mosaicY) != 0) {
      mosaicY = io_registers[REG_VCOUNT] - (io_registers[REG_VCOUNT] % mosaicY);
      yyy = (vofs + mosaicY) & maskY;
    }
  }

  if(yyy > 255 && sizeY > 256) {
    yyy &= 255;
    screenBase += 0x400;
    if(sizeX > 256)
      screenBase += 0x400;
  }

  int yshift = ((yyy>>3)<<5);
  if((control) & 0x80) {
    u16 *screenSource = screenBase + 0x400 * (xxx>>8) + ((xxx & 255)>>3) + yshift;
    for(int x = 0; x < 240; x++) {
      u16 data = READ16LE(screenSource);

      int tile = data & 0x3FF;
      int tileX = (xxx & 7);
      int tileY = yyy & 7;

      if(tileX == 7)
        screenSource++;

      if(data & 0x0400)
        tileX = 7 - tileX;
      if(data & 0x0800)
        tileY = 7 - tileY;

      u8 color = charBase[tile * 64 + tileY * 8 + tileX];

      line[x] = color ? (READ16LE(&palette[color]) | prio): 0x80000000;

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
    u16 *screenSource = screenBase + 0x400*(xxx>>8)+((xxx&255)>>3) +
      yshift;
    for(int x = 0; x < 240; x++) {
      u16 data = READ16LE(screenSource);

      int tile = data & 0x3FF;
      int tileX = (xxx & 7);
      int tileY = yyy & 7;

      if(tileX == 7)
        screenSource++;

      if(data & 0x0400)
        tileX = 7 - tileX;
      if(data & 0x0800)
        tileY = 7 - tileY;

      u8 color = charBase[(tile<<5) + (tileY<<2) + (tileX>>1)];

      if(tileX & 1) {
        color = (color >> 4);
      } else {
        color &= 0x0F;
      }

      int pal = (data>>8) & 0xF0;
      line[x] = color ? (READ16LE(&palette[pal + color])|prio): 0x80000000;

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
      int m = 1;
      for(int i = 0; i < 239; i++) {
        line[i+1] = line[i];
        m++;
        if(m == mosaicX) {
          m = 1;
          i++;
        }
      }
    }
  }
}
#endif

static u32 map_sizes_rot[] = { 128, 256, 512, 1024 };

static INLINE void gfxDrawRotScreen(u16 control, u16 x_l, u16 x_h, u16 y_l, u16 y_h,
u16 pa,  u16 pb, u16 pc,  u16 pd, int& currentX, int& currentY, int changed, u32 *line)
{
	u16 *palette = (u16 *)graphics.paletteRAM;
	u8 *charBase = &vram[((control >> 2) & 0x03) << 14];
	u8 *screenBase = (u8 *)&vram[((control >> 8) & 0x1f) << 11];
	int prio = ((control & 3) << 25) + 0x1000000;

	u32 map_size = (control >> 14) & 3;
	u32 sizeX = map_sizes_rot[map_size];
	u32 sizeY = map_sizes_rot[map_size];

	int maskX = sizeX-1;
	int maskY = sizeY-1;

	int yshift = ((control >> 14) & 3)+4;

#ifdef BRANCHLESS_GBA_GFX
	int dx = pa & 0x7FFF;
	int dmx = pb & 0x7FFF;
	int dy = pc & 0x7FFF;
	int dmy = pd & 0x7FFF;

	dx |= isel(-(pa & 0x8000), 0, 0xFFFF8000);

	dmx |= isel(-(pb & 0x8000), 0, 0xFFFF8000);

	dy |= isel(-(pc & 0x8000), 0, 0xFFFF8000);

	dmy |= isel(-(pd & 0x8000), 0, 0xFFFF8000);
#else
	int dx = pa & 0x7FFF;
	if(pa & 0x8000)
		dx |= 0xFFFF8000;
	int dmx = pb & 0x7FFF;
	if(pb & 0x8000)
		dmx |= 0xFFFF8000;
	int dy = pc & 0x7FFF;
	if(pc & 0x8000)
		dy |= 0xFFFF8000;
	int dmy = pd & 0x7FFF;
	if(pd & 0x8000)
		dmy |= 0xFFFF8000;
#endif

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

	int realX = currentX;
	int realY = currentY;

	if(control & 0x40)
	{
		int mosaicY = ((MOSAIC & 0xF0)>>4) + 1;
		int y = (io_registers[REG_VCOUNT] % mosaicY);
		realX -= y*dmx;
		realY -= y*dmy;
	}

	memset(line, -1, 240 * sizeof(u32));
	if(control & 0x2000)
	{
		for(u32 x = 0; x < 240u; ++x)
		{
			int xxx = (realX >> 8) & maskX;
			int yyy = (realY >> 8) & maskY;

			int tile = screenBase[(xxx>>3) + ((yyy>>3)<<yshift)];

			int tileX = (xxx & 7);
			int tileY = yyy & 7;

			u8 color = charBase[(tile<<6) + (tileY<<3) + tileX];

			if(color)
				line[x] = (READ16LE(&palette[color])|prio);

			realX += dx;
			realY += dy;
		}
	}
	else
	{
		for(u32 x = 0; x < 240u; ++x)
		{
			unsigned xxx = (realX >> 8);
			unsigned yyy = (realY >> 8);

			if(xxx < sizeX && yyy < sizeY)
			{
				int tile = screenBase[(xxx>>3) + ((yyy>>3)<<yshift)];

				int tileX = (xxx & 7);
				int tileY = yyy & 7;

				u8 color = charBase[(tile<<6) + (tileY<<3) + tileX];

				if(color)
					line[x] = (READ16LE(&palette[color])|prio);
			}

			realX += dx;
			realY += dy;
		}
	}

	if(control & 0x40)
	{
		int mosaicX = (MOSAIC & 0xF) + 1;
		if(mosaicX > 1)
		{
			int m = 1;
			for(u32 i = 0; i < 239u; ++i)
			{
				line[i+1] = line[i];
				if(++m == mosaicX)
				{
					m = 1;
					++i;
				}
			}
		}
	}
}

static INLINE void gfxDrawRotScreen16Bit( int& currentX,  int& currentY, int changed)
{
	u16 *screenBase = (u16 *)&vram[0];
	int prio = ((io_registers[REG_BG2CNT] & 3) << 25) + 0x1000000;

	u32 sizeX = 240;
	u32 sizeY = 160;

	int startX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
	if(BG2X_H & 0x0800)
		startX |= 0xF8000000;
	int startY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
	if(BG2Y_H & 0x0800)
		startY |= 0xF8000000;

#ifdef BRANCHLESS_GBA_GFX
	int dx = io_registers[REG_BG2PA] & 0x7FFF;
	dx |= isel(-(io_registers[REG_BG2PA] & 0x8000), 0, 0xFFFF8000);

	int dmx = io_registers[REG_BG2PB] & 0x7FFF;
	dmx |= isel(-(io_registers[REG_BG2PB] & 0x8000), 0, 0xFFFF8000);

	int dy = io_registers[REG_BG2PC] & 0x7FFF;
	dy |= isel(-(io_registers[REG_BG2PC] & 0x8000), 0, 0xFFFF8000);

	int dmy = io_registers[REG_BG2PD] & 0x7FFF;
	dmy |= isel(-(io_registers[REG_BG2PD] & 0x8000), 0, 0xFFFF8000);
#else
	int dx = io_registers[REG_BG2PA] & 0x7FFF;
	if(io_registers[REG_BG2PA] & 0x8000)
		dx |= 0xFFFF8000;
	int dmx = io_registers[REG_BG2PB] & 0x7FFF;
	if(io_registers[REG_BG2PB] & 0x8000)
		dmx |= 0xFFFF8000;
	int dy = io_registers[REG_BG2PC] & 0x7FFF;
	if(io_registers[REG_BG2PC] & 0x8000)
		dy |= 0xFFFF8000;
	int dmy = io_registers[REG_BG2PD] & 0x7FFF;
	if(io_registers[REG_BG2PD] & 0x8000)
		dmy |= 0xFFFF8000;
#endif

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

	int realX = currentX;
	int realY = currentY;

	if(io_registers[REG_BG2CNT] & 0x40) {
		int mosaicY = ((MOSAIC & 0xF0)>>4) + 1;
		int y = (io_registers[REG_VCOUNT] % mosaicY);
		realX -= y*dmx;
		realY -= y*dmy;
	}

	unsigned xxx = (realX >> 8);
	unsigned yyy = (realY >> 8);

	memset(line[2], -1, 240 * sizeof(u32));
	for(u32 x = 0; x < 240u; ++x)
	{
		if(xxx < sizeX && yyy < sizeY)
			line[2][x] = (READ16LE(&screenBase[yyy * sizeX + xxx]) | prio);

		realX += dx;
		realY += dy;

		xxx = (realX >> 8);
		yyy = (realY >> 8);
	}

	if(io_registers[REG_BG2CNT] & 0x40) {
		int mosaicX = (MOSAIC & 0xF) + 1;
		if(mosaicX > 1) {
			int m = 1;
			for(u32 i = 0; i < 239u; ++i)
			{
				line[2][i+1] = line[2][i];
				if(++m == mosaicX)
				{
					m = 1;
					++i;
				}
			}
		}
	}
}

static INLINE void gfxDrawRotScreen256(int &currentX, int& currentY, int changed)
{
	u16 *palette = (u16 *)graphics.paletteRAM;
	u8 *screenBase = (io_registers[REG_DISPCNT] & 0x0010) ? &vram[0xA000] : &vram[0x0000];
	int prio = ((io_registers[REG_BG2CNT] & 3) << 25) + 0x1000000;
	u32 sizeX = 240;
	u32 sizeY = 160;

	int startX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
	if(BG2X_H & 0x0800)
		startX |= 0xF8000000;
	int startY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
	if(BG2Y_H & 0x0800)
		startY |= 0xF8000000;

#ifdef BRANCHLESS_GBA_GFX
	int dx = io_registers[REG_BG2PA] & 0x7FFF;
	dx |= isel(-(io_registers[REG_BG2PA] & 0x8000), 0, 0xFFFF8000);

	int dmx = io_registers[REG_BG2PB] & 0x7FFF;
	dmx |= isel(-(io_registers[REG_BG2PB] & 0x8000), 0, 0xFFFF8000);

	int dy = io_registers[REG_BG2PC] & 0x7FFF;
	dy |= isel(-(io_registers[REG_BG2PC] & 0x8000), 0, 0xFFFF8000);

	int dmy = io_registers[REG_BG2PD] & 0x7FFF;
	dmy |= isel(-(io_registers[REG_BG2PD] & 0x8000), 0, 0xFFFF8000);
#else
	int dx = io_registers[REG_BG2PA] & 0x7FFF;
	if(io_registers[REG_BG2PA] & 0x8000)
		dx |= 0xFFFF8000;
	int dmx = io_registers[REG_BG2PB] & 0x7FFF;
	if(io_registers[REG_BG2PB] & 0x8000)
		dmx |= 0xFFFF8000;
	int dy = io_registers[REG_BG2PC] & 0x7FFF;
	if(io_registers[REG_BG2PC] & 0x8000)
		dy |= 0xFFFF8000;
	int dmy = io_registers[REG_BG2PD] & 0x7FFF;
	if(io_registers[REG_BG2PD] & 0x8000)
		dmy |= 0xFFFF8000;
#endif

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

	int realX = currentX;
	int realY = currentY;

	if(io_registers[REG_BG2CNT] & 0x40) {
		int mosaicY = ((MOSAIC & 0xF0)>>4) + 1;
		int y = io_registers[REG_VCOUNT] - (io_registers[REG_VCOUNT] % mosaicY);
		realX = startX + y*dmx;
		realY = startY + y*dmy;
	}

	int xxx = (realX >> 8);
	int yyy = (realY >> 8);

	memset(line[2], -1, 240 * sizeof(u32));
	for(u32 x = 0; x < 240; ++x)
	{
		u8 color = screenBase[yyy * 240 + xxx];
		if(unsigned(xxx) < sizeX && unsigned(yyy) < sizeY && color)
			line[2][x] = (READ16LE(&palette[color])|prio);
		realX += dx;
		realY += dy;

		xxx = (realX >> 8);
		yyy = (realY >> 8);
	}

	if(io_registers[REG_BG2CNT] & 0x40)
	{
		int mosaicX = (MOSAIC & 0xF) + 1;
		if(mosaicX > 1)
		{
			int m = 1;
			for(u32 i = 0; i < 239u; ++i)
			{
				line[2][i+1] = line[2][i];
				if(++m == mosaicX)
				{
					m = 1;
					++i;
				}
			}
		}
	}
}

static INLINE void gfxDrawRotScreen16Bit160(int& currentX, int& currentY, int changed)
{
	u16 *screenBase = (io_registers[REG_DISPCNT] & 0x0010) ? (u16 *)&vram[0xa000] :
		(u16 *)&vram[0];
	int prio = ((io_registers[REG_BG2CNT] & 3) << 25) + 0x1000000;
	u32 sizeX = 160;
	u32 sizeY = 128;

	int startX = (BG2X_L) | ((BG2X_H & 0x07FF)<<16);
	if(BG2X_H & 0x0800)
		startX |= 0xF8000000;
	int startY = (BG2Y_L) | ((BG2Y_H & 0x07FF)<<16);
	if(BG2Y_H & 0x0800)
		startY |= 0xF8000000;

#ifdef BRANCHLESS_GBA_GFX
	int dx = io_registers[REG_BG2PA] & 0x7FFF;
	dx |= isel(-(io_registers[REG_BG2PA] & 0x8000), 0, 0xFFFF8000);

	int dmx = io_registers[REG_BG2PB] & 0x7FFF;
	dmx |= isel(-(io_registers[REG_BG2PB] & 0x8000), 0, 0xFFFF8000);

	int dy = io_registers[REG_BG2PC] & 0x7FFF;
	dy |= isel(-(io_registers[REG_BG2PC] & 0x8000), 0, 0xFFFF8000);

	int dmy = io_registers[REG_BG2PD] & 0x7FFF;
	dmy |= isel(-(io_registers[REG_BG2PD] & 0x8000), 0, 0xFFFF8000);
#else
	int dx = io_registers[REG_BG2PA] & 0x7FFF;
	if(io_registers[REG_BG2PA] & 0x8000)
		dx |= 0xFFFF8000;
	int dmx = io_registers[REG_BG2PB] & 0x7FFF;
	if(io_registers[REG_BG2PB] & 0x8000)
		dmx |= 0xFFFF8000;
	int dy = io_registers[REG_BG2PC] & 0x7FFF;
	if(io_registers[REG_BG2PC] & 0x8000)
		dy |= 0xFFFF8000;
	int dmy = io_registers[REG_BG2PD] & 0x7FFF;
	if(io_registers[REG_BG2PD] & 0x8000)
		dmy |= 0xFFFF8000;
#endif

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

	int realX = currentX;
	int realY = currentY;

	if(io_registers[REG_BG2CNT] & 0x40) {
		int mosaicY = ((MOSAIC & 0xF0)>>4) + 1;
		int y = io_registers[REG_VCOUNT] - (io_registers[REG_VCOUNT] % mosaicY);
		realX = startX + y*dmx;
		realY = startY + y*dmy;
	}

	int xxx = (realX >> 8);
	int yyy = (realY >> 8);

	memset(line[2], -1, 240 * sizeof(u32));
	for(u32 x = 0; x < 240u; ++x)
	{
		if(unsigned(xxx) < sizeX && unsigned(yyy) < sizeY)
			line[2][x] = (READ16LE(&screenBase[yyy * sizeX + xxx]) | prio);

		realX += dx;
		realY += dy;

		xxx = (realX >> 8);
		yyy = (realY >> 8);
	}


	int mosaicX = (MOSAIC & 0xF) + 1;
	if(io_registers[REG_BG2CNT] & 0x40 && (mosaicX > 1))
	{
		int m = 1;
		for(u32 i = 0; i < 239u; ++i)
		{
			line[2][i+1] = line[2][i];
			if(++m == mosaicX)
			{
				m = 1;
				++i;
			}
		}
	}
}

/* lineOBJpix is used to keep track of the drawn OBJs
   and to stop drawing them if the 'maximum number of OBJ per line'
   has been reached. */

static INLINE void gfxDrawSprites (void)
{
	unsigned lineOBJpix, m;

	lineOBJpix = (io_registers[REG_DISPCNT] & 0x20) ? 954 : 1226;
	m = 0;

	u16 *sprites = (u16 *)oam;
	u16 *spritePalette = &((u16 *)graphics.paletteRAM)[256];
	int mosaicY = ((MOSAIC & 0xF000)>>12) + 1;
	int mosaicX = ((MOSAIC & 0xF00)>>8) + 1;
	for(u32 x = 0; x < 128; x++)
	{
		u16 a0 = READ16LE(sprites++);
		u16 a1 = READ16LE(sprites++);
		u16 a2 = READ16LE(sprites++);
		++sprites;

		lineOBJpixleft[x]=lineOBJpix;

		lineOBJpix-=2;
		if (lineOBJpix<=0)
			return;

		if ((a0 & 0x0c00) == 0x0c00)
			a0 &=0xF3FF;

		u16 a0val = a0>>14;

		if (a0val == 3)
		{
			a0 &= 0x3FFF;
			a1 &= 0x3FFF;
		}

		u32 sizeX = 8<<(a1>>14);
		u32 sizeY = sizeX;


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


		int sy = (a0 & 255);
		int sx = (a1 & 0x1FF);

		// computes ticks used by OBJ-WIN if OBJWIN is enabled
		if (((a0 & 0x0c00) == 0x0800) && (graphics.layerEnable & 0x8000))
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

			if ((io_registers[REG_VCOUNT]>=sy) && (io_registers[REG_VCOUNT]<sy+sizeY) && (sx<240))
			{
				lineOBJpix -= (sizeX-2);

				if (a0 & 0x0100)
					lineOBJpix -= (10+sizeX); 
			}
			continue;
		}

		// else ignores OBJ-WIN if OBJWIN is disabled, and ignored disabled OBJ
		else if(((a0 & 0x0c00) == 0x0800) || ((a0 & 0x0300) == 0x0200))
			continue;

		if(a0 & 0x0100)
		{
			u32 fieldX = sizeX;
			u32 fieldY = sizeY;
			if(a0 & 0x0200)
			{
				fieldX <<= 1;
				fieldY <<= 1;
			}
			if((sy+fieldY) > 256)
				sy -= 256;
			int t = io_registers[REG_VCOUNT] - sy;
			if(unsigned(t) < fieldY)
			{
				u32 startpix = 0;
				if ((sx+fieldX)> 512)
					startpix=512-sx;

				if (lineOBJpix && ((sx < 240) || startpix))
				{
					lineOBJpix-=8;
					int rot = (((a1 >> 9) & 0x1F) << 4);
					u16 *OAM = (u16 *)oam;
					int dx = READ16LE(&OAM[3 + rot]);
					if(dx & 0x8000)
						dx |= 0xFFFF8000;
					int dmx = READ16LE(&OAM[7 + rot]);
					if(dmx & 0x8000)
						dmx |= 0xFFFF8000;
					int dy = READ16LE(&OAM[11 + rot]);
					if(dy & 0x8000)
						dy |= 0xFFFF8000;
					int dmy = READ16LE(&OAM[15 + rot]);
					if(dmy & 0x8000)
						dmy |= 0xFFFF8000;

					if(a0 & 0x1000)
						t -= (t % mosaicY);

					int realX = ((sizeX) << 7) - (fieldX >> 1)*dx + ((t - (fieldY>>1))* dmx);
					int realY = ((sizeY) << 7) - (fieldX >> 1)*dy + ((t - (fieldY>>1))* dmy);

					u32 prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);

					int c = (a2 & 0x3FF);
					if((io_registers[REG_DISPCNT] & 7) > 2 && (c < 512))
						continue;

					if(a0 & 0x2000)
					{
						int inc = 32;
						if(io_registers[REG_DISPCNT] & 0x40)
							inc = sizeX >> 2;
						else
							c &= 0x3FE;
						for(u32 x = 0; x < fieldX; x++)
						{
							if (x >= startpix)
								lineOBJpix-=2;
							unsigned xxx = realX >> 8;
							unsigned yyy = realY >> 8;
							if(xxx < sizeX && yyy < sizeY && sx < 240)
							{

								u32 color = vram[0x10000 + ((((c + (yyy>>3) * inc)<<5)
								+ ((yyy & 7)<<3) + ((xxx >> 3)<<6) + (xxx & 7))&0x7FFF)];

								if ((color==0) && (((prio >> 25)&3) < ((line[4][sx]>>25)&3)))
								{
									line[4][sx] = (line[4][sx] & 0xF9FFFFFF) | prio;
									if((a0 & 0x1000) && m)
										line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
								}
								else if((color) && (prio < (line[4][sx]&0xFF000000)))
								{
									line[4][sx] = READ16LE(&spritePalette[color]) | prio;
									if((a0 & 0x1000) && m)
										line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
								}

								if ((a0 & 0x1000) && ((m+1) == mosaicX))
									m = 0;
							}
							sx = (sx+1)&511;
							realX += dx;
							realY += dy;
						}
					}
					else
					{
						int inc = 32;
						if(io_registers[REG_DISPCNT] & 0x40)
							inc = sizeX >> 3;
						int palette = (a2 >> 8) & 0xF0;
						for(u32 x = 0; x < fieldX; ++x)
						{
							if (x >= startpix)
								lineOBJpix-=2;
							unsigned xxx = realX >> 8;
							unsigned yyy = realY >> 8;
							if(xxx < sizeX && yyy < sizeY && sx < 240)
							{

								u32 color = vram[0x10000 + ((((c + (yyy>>3) * inc)<<5)
											+ ((yyy & 7)<<2) + ((xxx >> 3)<<5)
											+ ((xxx & 7)>>1))&0x7FFF)];
								if(xxx & 1)
									color >>= 4;
								else
									color &= 0x0F;

								if ((color==0) && (((prio >> 25)&3) <
											((line[4][sx]>>25)&3)))
								{
									line[4][sx] = (line[4][sx] & 0xF9FFFFFF) | prio;
									if((a0 & 0x1000) && m)
										line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
								}
								else if((color) && (prio < (line[4][sx]&0xFF000000)))
								{
									line[4][sx] = READ16LE(&spritePalette[palette+color]) | prio;
									if((a0 & 0x1000) && m)
										line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
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
		else
		{
			if(sy+sizeY > 256)
				sy -= 256;
			int t = io_registers[REG_VCOUNT] - sy;
			if(unsigned(t) < sizeY)
			{
				u32 startpix = 0;
				if ((sx+sizeX)> 512)
					startpix=512-sx;

				if((sx < 240) || startpix)
				{
					lineOBJpix+=2;

					if(a1 & 0x2000)
						t = sizeY - t - 1;

					int c = (a2 & 0x3FF);
					if((io_registers[REG_DISPCNT] & 7) > 2 && (c < 512))
						continue;

					int inc = 32;
					int xxx = 0;
					if(a1 & 0x1000)
						xxx = sizeX-1;

					if(a0 & 0x1000)
						t -= (t % mosaicY);

					if(a0 & 0x2000)
					{
						if(io_registers[REG_DISPCNT] & 0x40)
							inc = sizeX >> 2;
						else
							c &= 0x3FE;

						int address = 0x10000 + ((((c+ (t>>3) * inc) << 5)
									+ ((t & 7) << 3) + ((xxx>>3)<<6) + (xxx & 7)) & 0x7FFF);

						if(a1 & 0x1000)
							xxx = 7;
						u32 prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);

						for(u32 xx = 0; xx < sizeX; xx++)
						{
							if (xx >= startpix)
								--lineOBJpix;
							if(sx < 240)
							{
								u8 color = vram[address];
								if ((color==0) && (((prio >> 25)&3) <
											((line[4][sx]>>25)&3)))
								{
									line[4][sx] = (line[4][sx] & 0xF9FFFFFF) | prio;
									if((a0 & 0x1000) && m)
										line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
								}
								else if((color) && (prio < (line[4][sx]&0xFF000000)))
								{
									line[4][sx] = READ16LE(&spritePalette[color]) | prio;
									if((a0 & 0x1000) && m)
										line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
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
					else
					{
						if(io_registers[REG_DISPCNT] & 0x40)
							inc = sizeX >> 3;

						int address = 0x10000 + ((((c + (t>>3) * inc)<<5)
									+ ((t & 7)<<2) + ((xxx>>3)<<5) + ((xxx & 7) >> 1))&0x7FFF);

						u32 prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);
						int palette = (a2 >> 8) & 0xF0;
						if(a1 & 0x1000)
						{
							xxx = 7;
							int xx = sizeX - 1;
							do
							{
								if (xx >= (int)(startpix))
									--lineOBJpix;
								//if (lineOBJpix<0)
								//  continue;
								if(sx < 240)
								{
									u8 color = vram[address];
									if(xx & 1)
										color >>= 4;
									else
										color &= 0x0F;

									if ((color==0) && (((prio >> 25)&3) <
												((line[4][sx]>>25)&3)))
									{
										line[4][sx] = (line[4][sx] & 0xF9FFFFFF) | prio;
										if((a0 & 0x1000) && m)
											line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
									}
									else if((color) && (prio < (line[4][sx]&0xFF000000)))
									{
										line[4][sx] = READ16LE(&spritePalette[palette + color]) | prio;
										if((a0 & 0x1000) && m)
											line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
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
							for(u32 xx = 0; xx < sizeX; ++xx)
							{
								if (xx >= startpix)
									--lineOBJpix;
								//if (lineOBJpix<0)
								//  continue;
								if(sx < 240)
								{
									u8 color = vram[address];
									if(xx & 1)
										color >>= 4;
									else
										color &= 0x0F;

									if ((color==0) && (((prio >> 25)&3) <
												((line[4][sx]>>25)&3)))
									{
										line[4][sx] = (line[4][sx] & 0xF9FFFFFF) | prio;
										if((a0 & 0x1000) && m)
											line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;
									}
									else if((color) && (prio < (line[4][sx]&0xFF000000)))
									{
										line[4][sx] = READ16LE(&spritePalette[palette + color]) | prio;
										if((a0 & 0x1000) && m)
											line[4][sx]=(line[4][sx-1] & 0xF9FFFFFF) | prio;

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

static INLINE void gfxDrawOBJWin (void)
{
	u16 *sprites = (u16 *)oam;
	for(int x = 0; x < 128 ; x++)
	{
		int lineOBJpix = lineOBJpixleft[x];
		u16 a0 = READ16LE(sprites++);
		u16 a1 = READ16LE(sprites++);
		u16 a2 = READ16LE(sprites++);
		sprites++;

		if (lineOBJpix<=0)
			return;

		// ignores non OBJ-WIN and disabled OBJ-WIN
		if(((a0 & 0x0c00) != 0x0800) || ((a0 & 0x0300) == 0x0200))
			continue;

		u16 a0val = a0>>14;

		if ((a0 & 0x0c00) == 0x0c00)
			a0 &=0xF3FF;

		if (a0val == 3)
		{
			a0 &= 0x3FFF;
			a1 &= 0x3FFF;
		}

		int sizeX = 8<<(a1>>14);
		int sizeY = sizeX;

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

		int sy = (a0 & 255);

		if(a0 & 0x0100)
		{
			int fieldX = sizeX;
			int fieldY = sizeY;
			if(a0 & 0x0200)
			{
				fieldX <<= 1;
				fieldY <<= 1;
			}
			if((sy+fieldY) > 256)
				sy -= 256;
			int t = io_registers[REG_VCOUNT] - sy;
			if((t >= 0) && (t < fieldY))
			{
				int sx = (a1 & 0x1FF);
				int startpix = 0;
				if ((sx+fieldX)> 512)
					startpix=512-sx;

				if((sx < 240) || startpix)
				{
					lineOBJpix-=8;
					// int t2 = t - (fieldY >> 1);
					int rot = (a1 >> 9) & 0x1F;
					u16 *OAM = (u16 *)oam;
					int dx = READ16LE(&OAM[3 + (rot << 4)]);
					if(dx & 0x8000)
						dx |= 0xFFFF8000;
					int dmx = READ16LE(&OAM[7 + (rot << 4)]);
					if(dmx & 0x8000)
						dmx |= 0xFFFF8000;
					int dy = READ16LE(&OAM[11 + (rot << 4)]);
					if(dy & 0x8000)
						dy |= 0xFFFF8000;
					int dmy = READ16LE(&OAM[15 + (rot << 4)]);
					if(dmy & 0x8000)
						dmy |= 0xFFFF8000;

					int realX = ((sizeX) << 7) - (fieldX >> 1)*dx - (fieldY>>1)*dmx
						+ t * dmx;
					int realY = ((sizeY) << 7) - (fieldX >> 1)*dy - (fieldY>>1)*dmy
						+ t * dmy;

					int c = (a2 & 0x3FF);
					if((io_registers[REG_DISPCNT] & 7) > 2 && (c < 512))
						continue;

					int inc = 32;
					bool condition1 = a0 & 0x2000;

					if(io_registers[REG_DISPCNT] & 0x40)
						inc = sizeX >> 3;

					for(int x = 0; x < fieldX; x++)
					{
						bool cont = true;
						if (x >= startpix)
							lineOBJpix-=2;
						if (lineOBJpix<0)
							continue;
						int xxx = realX >> 8;
						int yyy = realY >> 8;

						if(xxx < 0 || xxx >= sizeX || yyy < 0 || yyy >= sizeY || sx >= 240)
							cont = false;

						if(cont)
						{
							u32 color;
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
								line[5][sx] = 1;
						}
						sx = (sx+1)&511;
						realX += dx;
						realY += dy;
					}
				}
			}
		}
		else
		{
			if((sy+sizeY) > 256)
				sy -= 256;
			int t = io_registers[REG_VCOUNT] - sy;
			if((t >= 0) && (t < sizeY))
			{
				int sx = (a1 & 0x1FF);
				int startpix = 0;
				if ((sx+sizeX)> 512)
					startpix=512-sx;

				if((sx < 240) || startpix)
				{
					lineOBJpix+=2;
					if(a1 & 0x2000)
						t = sizeY - t - 1;
					int c = (a2 & 0x3FF);
					if((io_registers[REG_DISPCNT] & 7) > 2 && (c < 512))
						continue;
					if(a0 & 0x2000)
					{

						int inc = 32;
						if(io_registers[REG_DISPCNT] & 0x40)
							inc = sizeX >> 2;
						else
							c &= 0x3FE;

						int xxx = 0;
						if(a1 & 0x1000)
							xxx = sizeX-1;
						int address = 0x10000 + ((((c+ (t>>3) * inc) << 5)
									+ ((t & 7) << 3) + ((xxx>>3)<<6) + (xxx & 7))&0x7fff);
						if(a1 & 0x1000)
							xxx = 7;
						for(int xx = 0; xx < sizeX; xx++)
						{
							if (xx >= startpix)
								lineOBJpix--;
							if (lineOBJpix<0)
								continue;
							if(sx < 240)
							{
								u8 color = vram[address];
								if(color)
									line[5][sx] = 1;
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
					else
					{
						int inc = 32;
						if(io_registers[REG_DISPCNT] & 0x40)
							inc = sizeX >> 3;
						int xxx = 0;
						if(a1 & 0x1000)
							xxx = sizeX - 1;
						int address = 0x10000 + ((((c + (t>>3) * inc)<<5)
									+ ((t & 7)<<2) + ((xxx>>3)<<5) + ((xxx & 7) >> 1))&0x7fff);
						// u32 prio = (((a2 >> 10) & 3) << 25) | ((a0 & 0x0c00)<<6);
						// int palette = (a2 >> 8) & 0xF0;
						if(a1 & 0x1000)
						{
							xxx = 7;
							for(int xx = sizeX - 1; xx >= 0; xx--)
							{
								if (xx >= startpix)
									lineOBJpix--;
								if (lineOBJpix<0)
									continue;
								if(sx < 240)
								{
									u8 color = vram[address];
									if(xx & 1)
										color = (color >> 4);
									else
										color &= 0x0F;

									if(color)
										line[5][sx] = 1;
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
						else
						{
							for(int xx = 0; xx < sizeX; xx++)
							{
								if (xx >= startpix)
									lineOBJpix--;
								if (lineOBJpix<0)
									continue;
								if(sx < 240)
								{
									u8 color = vram[address];
									if(xx & 1)
										color = (color >> 4);
									else
										color &= 0x0F;

									if(color)
										line[5][sx] = 1;
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

static INLINE u32 gfxIncreaseBrightness(u32 color, int coeff)
{
	color = (((color & 0xffff) << 16) | (color & 0xffff)) & 0x3E07C1F;

	color += ((((0x3E07C1F - color) * coeff) >> 4) & 0x3E07C1F);

	return (color >> 16) | color;
}

static INLINE u32 gfxDecreaseBrightness(u32 color, int coeff)
{
	color = (((color & 0xffff) << 16) | (color & 0xffff)) & 0x3E07C1F;

	color -= (((color * coeff) >> 4) & 0x3E07C1F);

	return (color >> 16) | color;
}

static u32 AlphaClampLUT[64] = 
{
 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F,
 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F,
 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F,
 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F, 0x1F
};  

#define GFX_ALPHA_BLEND(color, color2, ca, cb) \
	int r = AlphaClampLUT[(((color & 0x1F) * ca) >> 4) + (((color2 & 0x1F) * cb) >> 4)]; \
	int g = AlphaClampLUT[((((color >> 5) & 0x1F) * ca) >> 4) + ((((color2 >> 5) & 0x1F) * cb) >> 4)]; \
	int b = AlphaClampLUT[((((color >> 10) & 0x1F) * ca) >> 4) + ((((color2 >> 10) & 0x1F) * cb) >> 4)]; \
	color = (color & 0xFFFF0000) | (b << 10) | (g << 5) | r;

/*============================================================
	GBA.CPP
============================================================ */
int saveType = 0;
bool useBios = false;
bool skipBios = false;
bool cpuIsMultiBoot = false;
int cpuSaveType = 0;
bool enableRtc = false;
bool mirroringEnable = false;
bool skipSaveGameBattery = false;

int cpuDmaCount = 0;

uint8_t *bios = 0;
uint8_t *rom = 0;
uint8_t *internalRAM = 0;
uint8_t *workRAM = 0;
uint8_t *vram = 0;
u16 *pix = 0;
uint8_t *oam = 0;
uint8_t *ioMem = 0;

#ifdef USE_SWITICKS
int SWITicks = 0;
#endif

bool cpuSramEnabled = true;
bool cpuFlashEnabled = true;
bool cpuEEPROMEnabled = true;
bool cpuEEPROMSensorEnabled = false;

#ifndef LSB_FIRST
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

#ifdef USE_SWITICKS
	if (SWITicks)
	{
		if (SWITicks < cpuLoopTicks)
			cpuLoopTicks = SWITicks;
	}
#endif

	if (IRQTicks)
	{
		if (IRQTicks < cpuLoopTicks)
			cpuLoopTicks = IRQTicks;
	}

	return cpuLoopTicks;
}

#define CPUUpdateWindow0() \
{ \
  int x00_window0 = io_registers[REG_WIN0H] >>8; \
  int x01_window0 = io_registers[REG_WIN0H] & 255; \
  int x00_lte_x01 = x00_window0 <= x01_window0; \
  for(int i = 0; i < 240; i++) \
      gfxInWin[0][i] = ((i >= x00_window0 && i < x01_window0) & x00_lte_x01) | ((i >= x00_window0 || i < x01_window0) & ~x00_lte_x01); \
}

#define CPUUpdateWindow1() \
{ \
  int x00_window1 = io_registers[REG_WIN1H]>>8; \
  int x01_window1 = io_registers[REG_WIN1H] & 255; \
  int x00_lte_x01 = x00_window1 <= x01_window1; \
  for(int i = 0; i < 240; i++) \
   gfxInWin[1][i] = ((i >= x00_window1 && i < x01_window1) & x00_lte_x01) | ((i >= x00_window1 || i < x01_window1) & ~x00_lte_x01); \
}

#define CPUCompareVCOUNT() \
  if(io_registers[REG_VCOUNT] == (io_registers[REG_DISPSTAT] >> 8)) \
  { \
    io_registers[REG_DISPSTAT] |= 4; \
    UPDATE_REG(0x04, io_registers[REG_DISPSTAT]); \
    if(io_registers[REG_DISPSTAT] & 0x20) \
    { \
      io_registers[REG_IF] |= 4; \
      UPDATE_REG(0x202, io_registers[REG_IF]); \
    } \
  } \
  else \
  { \
    io_registers[REG_DISPSTAT] &= 0xFFFB; \
    UPDATE_REG(0x4, io_registers[REG_DISPSTAT]); \
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

	utilWriteIntMem(data, SAVE_GAME_VERSION);
	utilWriteMem(data, &rom[0xa0], 16);
	utilWriteIntMem(data, useBios);
	utilWriteMem(data, &bus.reg[0], sizeof(bus.reg));

	utilWriteDataMem(data, saveGameStruct);

	utilWriteIntMem(data, stopState);
	utilWriteIntMem(data, IRQTicks);

	utilWriteMem(data, internalRAM, 0x8000);
	utilWriteMem(data, graphics.paletteRAM, 0x400);
	utilWriteMem(data, workRAM, 0x40000);
	utilWriteMem(data, vram, 0x20000);
	utilWriteMem(data, oam, 0x400);
	utilWriteMem(data, pix, 4 * PIX_BUFFER_SCREEN_WIDTH * 160);
	utilWriteMem(data, ioMem, 0x400);

	eepromSaveGameMem(data);
	flashSaveGameMem(data);
	soundSaveGameMem(data);
	rtcSaveGameMem(data);

	return (ptrdiff_t)data - (ptrdiff_t)orig;
}

bool CPUWriteBatteryFile(const char *fileName)
{
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

	if((gbaSaveType) && (gbaSaveType!=5))
	{
		FILE *file = fopen(fileName, "wb");

		if(!file) {
			systemMessage("Error creating file %s", fileName);
			return false;
		}

		// only save if Flash/Sram in use or EEprom in use
		if(gbaSaveType != 3) {
			if(gbaSaveType == 2) {
				if(fwrite(flashSaveMemory, 1, flashSize, file) != (size_t)flashSize) {
					fclose(file);
					return false;
				}
			} else {
				if(fwrite(flashSaveMemory, 1, 0x10000, file) != 0x10000) {
					fclose(file);
					return false;
				}
			}
		} else {
			if(fwrite(eepromData, 1, eepromSize, file) != (size_t)eepromSize) {
				fclose(file);
				return false;
			}
		}
		fclose(file);
	}
	return true;
}

bool CPUReadBatteryFile(const char *fileName)
{
	FILE *file = fopen(fileName, "rb");

	if(!file)
		return false;

	// check file size to know what we should read
	fseek(file, 0, SEEK_END);

	long size = ftell(file);
	fseek(file, 0, SEEK_SET);

	if(size == 512 || size == 0x2000) {
		if(fread(eepromData, 1, size, file) != (size_t)size) {
			fclose(file);
			return false;
		}
	} else {
		if(size == 0x20000) {
			if(fread(flashSaveMemory, 1, 0x20000, file) != 0x20000) {
				fclose(file);
				return false;
			}
			flashSetSize(0x20000);
		} else {
			if(fread(flashSaveMemory, 1, 0x10000, file) != 0x10000) {
				fclose(file);
				return false;
			}
			flashSetSize(0x10000);
		}
	}
	fclose(file);
	return true;
}

#ifdef HAVE_HLE_BIOS
static bool CPUIsGBABios(const char * file)
{
	if(strlen(file) > 4)
	{
		const char * p = strrchr(file,'.');

		if(p != NULL)
		{
			if(strcasecmp(p, ".gba") == 0)
				return true;
			if(strcasecmp(p, ".agb") == 0)
				return true;
			if(strcasecmp(p, ".bin") == 0)
				return true;
			if(strcasecmp(p, ".bios") == 0)
				return true;
			if(strcasecmp(p, ".rom") == 0)
				return true;
		}
	}

	return false;
}
#endif

#ifdef ELF
static bool CPUIsELF(const char *file)
{
	if(file == NULL)
		return false;

	if(strlen(file) > 4)
	{
		const char * p = strrchr(file,'.');

		if(p != NULL)
		{
			if(strcasecmp(p, ".elf") == 0)
				return true;
		}
	}
	return false;
}
#endif

static void CPUCleanUp (void)
{
	if(rom != NULL) {
		free(rom);
		rom = NULL;
	}

	if(vram != NULL) {
		free(vram);
		vram = NULL;
	}

	if(graphics.paletteRAM != NULL) {
		free(graphics.paletteRAM);
		graphics.paletteRAM = NULL;
	}

	if(internalRAM != NULL) {
		free(internalRAM);
		internalRAM = NULL;
	}

	if(workRAM != NULL) {
		free(workRAM);
		workRAM = NULL;
	}

	if(bios != NULL) {
		free(bios);
		bios = NULL;
	}

	if(pix != NULL) {
		free(pix);
		pix = NULL;
	}

	if(oam != NULL) {
		free(oam);
		oam = NULL;
	}

	if(ioMem != NULL) {
		free(ioMem);
		ioMem = NULL;
	}
}

int CPULoadRom(const char * file)
{
	romSize = 0x2000000;
	if(rom != NULL)
		CPUCleanUp();

	rom = (uint8_t *)malloc(0x2000000);

	if(rom == NULL)
		return 0;

	workRAM = (uint8_t *)calloc(1, 0x40000);

	if(workRAM == NULL)
		return 0;

	uint8_t *whereToLoad = cpuIsMultiBoot ? workRAM : rom;

		if(file != NULL)
		{
			if(!utilLoad(file,
						utilIsGBAImage,
						whereToLoad,
						romSize)) {
				free(rom);
				rom = NULL;
				free(workRAM);
				workRAM = NULL;
				return 0;
			}
		}

	uint16_t *temp = (uint16_t *)(rom+((romSize+1)&~1));
	int i;
	for(i = (romSize+1)&~1; i < 0x2000000; i+=2) {
		WRITE16LE(temp, (i >> 1) & 0xFFFF);
		temp++;
	}

	bios = (uint8_t *)calloc(1,0x4000);
	if(bios == NULL) {
		CPUCleanUp();
		return 0;
	}
	internalRAM = (uint8_t *)calloc(1,0x8000);
	if(internalRAM == NULL) {
		CPUCleanUp();
		return 0;
	}
	graphics.paletteRAM = (uint8_t *)calloc(1,0x400);
	if(graphics.paletteRAM == NULL) {
		CPUCleanUp();
		return 0;
	}
	vram = (uint8_t *)calloc(1, 0x20000);
	if(vram == NULL) {
		CPUCleanUp();
		return 0;
	}
	oam = (uint8_t *)calloc(1, 0x400);
	if(oam == NULL) {
		CPUCleanUp();
		return 0;
	}
	pix = (u16 *)calloc(1, 4 * PIX_BUFFER_SCREEN_WIDTH * 160);
	if(pix == NULL) {
		CPUCleanUp();
		return 0;
	}
	ioMem = (uint8_t *)calloc(1, 0x400);
	if(ioMem == NULL) {
		CPUCleanUp();
		return 0;
	}

	flashInit();
	eepromInit();

	memset(line[0], -1, 240 * sizeof(u32));
	memset(line[1], -1, 240 * sizeof(u32));
	memset(line[2], -1, 240 * sizeof(u32));
	memset(line[3], -1, 240 * sizeof(u32));

	return romSize;
}

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

#define brightness_switch() \
      switch((BLDMOD >> 6) & 3) \
      { \
         case 2: \
               color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]); \
               break; \
         case 3: \
               color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]); \
               break; \
      }

#define alpha_blend_brightness_switch() \
      if(top2 & (BLDMOD>>8)) \
	if(color < 0x80000000) \
	{ \
		GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]); \
	} \
      else if(BLDMOD & top) \
      { \
         brightness_switch(); \
      }

/* we only use 16bit color depth */
#define INIT_COLOR_DEPTH_LINE_MIX() uint16_t * lineMix = (pix + PIX_BUFFER_SCREEN_WIDTH * io_registers[REG_VCOUNT])

static void mode0RenderLine (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 0: Render Line\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

  if(graphics.layerEnable & 0x0100) {
    gfxDrawTextScreen(io_registers[REG_BG0CNT], io_registers[REG_BG0HOFS], io_registers[REG_BG0VOFS], line[0]);
  }

  if(graphics.layerEnable & 0x0200) {
    gfxDrawTextScreen(io_registers[REG_BG1CNT], io_registers[REG_BG1HOFS], io_registers[REG_BG1VOFS], line[1]);
  }

  if(graphics.layerEnable & 0x0400) {
    gfxDrawTextScreen(io_registers[REG_BG2CNT], io_registers[REG_BG2HOFS], io_registers[REG_BG2VOFS], line[2]);
  }

  if(graphics.layerEnable & 0x0800) {
    gfxDrawTextScreen(io_registers[REG_BG3CNT], io_registers[REG_BG3HOFS], io_registers[REG_BG3VOFS], line[3]);
  }


	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; x++)
	{
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		if(line[0][x] < color) {
			color = line[0][x];
			top = 0x01;
		}

		if((uint8_t)(line[1][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[1][x];
			top = 0x02;
		}

		if((uint8_t)(line[2][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[3][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[3][x];
			top = 0x08;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[4][x];
			top = 0x10;

			if(color & 0x00010000) {
				// semi-transparent OBJ
				uint32_t back = backdrop;
				uint8_t top2 = 0x20;

				if((uint8_t)(line[0][x]>>24) < (uint8_t)(back >> 24)) {
					back = line[0][x];
					top2 = 0x01;
				}

				if((uint8_t)(line[1][x]>>24) < (uint8_t)(back >> 24)) {
					back = line[1][x];
					top2 = 0x02;
				}

				if((uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24)) {
					back = line[2][x];
					top2 = 0x04;
				}

				if((uint8_t)(line[3][x]>>24) < (uint8_t)(back >> 24)) {
					back = line[3][x];
					top2 = 0x08;
				}

				alpha_blend_brightness_switch();
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
}

static void mode0RenderLineNoWindow (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 0: Render Line No Window\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;
	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

   if(graphics.layerEnable & 0x0100) {
      gfxDrawTextScreen(io_registers[REG_BG0CNT], io_registers[REG_BG0HOFS], io_registers[REG_BG0VOFS], line[0]);
   }

   if(graphics.layerEnable & 0x0200) {
      gfxDrawTextScreen(io_registers[REG_BG1CNT], io_registers[REG_BG1HOFS], io_registers[REG_BG1VOFS], line[1]);
   }

   if(graphics.layerEnable & 0x0400) {
      gfxDrawTextScreen(io_registers[REG_BG2CNT], io_registers[REG_BG2HOFS], io_registers[REG_BG2VOFS], line[2]);
   }

   if(graphics.layerEnable & 0x0800) {
      gfxDrawTextScreen(io_registers[REG_BG3CNT], io_registers[REG_BG3HOFS], io_registers[REG_BG3VOFS], line[3]);
   }

	int effect = (BLDMOD >> 6) & 3;

	for(int x = 0; x < 240; x++) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		if(line[0][x] < color) {
			color = line[0][x];
			top = 0x01;
		}

		if(line[1][x] < (color & 0xFF000000)) {
			color = line[1][x];
			top = 0x02;
		}

		if(line[2][x] < (color & 0xFF000000)) {
			color = line[2][x];
			top = 0x04;
		}

		if(line[3][x] < (color & 0xFF000000)) {
			color = line[3][x];
			top = 0x08;
		}

		if(line[4][x] < (color & 0xFF000000)) {
			color = line[4][x];
			top = 0x10;
		}

		if(!(color & 0x00010000)) {
			switch(effect) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;
						if((line[0][x] < back) && (top != 0x01))
						{
							back = line[0][x];
							top2 = 0x01;
						}

						if((line[1][x] < (back & 0xFF000000)) && (top != 0x02))
						{
							back = line[1][x];
							top2 = 0x02;
						}

						if((line[2][x] < (back & 0xFF000000)) && (top != 0x04))
						{
							back = line[2][x];
							top2 = 0x04;
						}

						if((line[3][x] < (back & 0xFF000000)) && (top != 0x08))
						{
							back = line[3][x];
							top2 = 0x08;
						}

						if((line[4][x] < (back & 0xFF000000)) && (top != 0x10))
						{
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}

					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			if(line[0][x] < back) {
				back = line[0][x];
				top2 = 0x01;
			}

			if(line[1][x] < (back & 0xFF000000)) {
				back = line[1][x];
				top2 = 0x02;
			}

			if(line[2][x] < (back & 0xFF000000)) {
				back = line[2][x];
				top2 = 0x04;
			}

			if(line[3][x] < (back & 0xFF000000)) {
				back = line[3][x];
				top2 = 0x08;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
}

static void mode0RenderLineAll (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 0: Render Line All\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	bool inWindow0 = false;
	bool inWindow1 = false;

	if(graphics.layerEnable & 0x2000) {
		uint8_t v0 = io_registers[REG_WIN0V] >> 8;
		uint8_t v1 = io_registers[REG_WIN0V] & 255;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
		if(v1 >= v0)
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
	}
	if(graphics.layerEnable & 0x4000) {
		uint8_t v0 = io_registers[REG_WIN1V] >> 8;
		uint8_t v1 = io_registers[REG_WIN1V] & 255;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
		if(v1 >= v0)
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
	}

  if((graphics.layerEnable & 0x0100)) {
    gfxDrawTextScreen(io_registers[REG_BG0CNT], io_registers[REG_BG0HOFS], io_registers[REG_BG0VOFS], line[0]);
  }

  if((graphics.layerEnable & 0x0200)) {
    gfxDrawTextScreen(io_registers[REG_BG1CNT], io_registers[REG_BG1HOFS], io_registers[REG_BG1VOFS], line[1]);
  }

  if((graphics.layerEnable & 0x0400)) {
    gfxDrawTextScreen(io_registers[REG_BG2CNT], io_registers[REG_BG2HOFS], io_registers[REG_BG2VOFS], line[2]);
  }

  if((graphics.layerEnable & 0x0800)) {
    gfxDrawTextScreen(io_registers[REG_BG3CNT], io_registers[REG_BG3HOFS], io_registers[REG_BG3VOFS], line[3]);
  }

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	uint8_t inWin0Mask = io_registers[REG_WININ] & 0xFF;
	uint8_t inWin1Mask = io_registers[REG_WININ] >> 8;
	uint8_t outMask = io_registers[REG_WINOUT] & 0xFF;

	for(int x = 0; x < 240; x++) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;
		uint8_t mask = outMask;

		if(!(line[5][x] & 0x80000000)) {
			mask = io_registers[REG_WINOUT] >> 8;
		}

		int32_t window1_mask = ((inWindow1 & gfxInWin[1][x]) | -(inWindow1 & gfxInWin[1][x])) >> 31;
		int32_t window0_mask = ((inWindow0 & gfxInWin[0][x]) | -(inWindow0 & gfxInWin[0][x])) >> 31;
		mask = (inWin1Mask & window1_mask) | (mask & ~window1_mask);
		mask = (inWin0Mask & window0_mask) | (mask & ~window0_mask);

		if((mask & 1) && (line[0][x] < color)) {
			color = line[0][x];
			top = 0x01;
		}

		if((mask & 2) && ((uint8_t)(line[1][x]>>24) < (uint8_t)(color >> 24))) {
			color = line[1][x];
			top = 0x02;
		}

		if((mask & 4) && ((uint8_t)(line[2][x]>>24) < (uint8_t)(color >> 24))) {
			color = line[2][x];
			top = 0x04;
		}

		if((mask & 8) && ((uint8_t)(line[3][x]>>24) < (uint8_t)(color >> 24))) {
			color = line[3][x];
			top = 0x08;
		}

		if((mask & 16) && ((uint8_t)(line[4][x]>>24) < (uint8_t)(color >> 24))) {
			color = line[4][x];
			top = 0x10;
		}

		if(color & 0x00010000)
		{
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			if((mask & 1) && ((uint8_t)(line[0][x]>>24) < (uint8_t)(back >> 24))) {
				back = line[0][x];
				top2 = 0x01;
			}

			if((mask & 2) && ((uint8_t)(line[1][x]>>24) < (uint8_t)(back >> 24))) {
				back = line[1][x];
				top2 = 0x02;
			}

			if((mask & 4) && ((uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24))) {
				back = line[2][x];
				top2 = 0x04;
			}

			if((mask & 8) && ((uint8_t)(line[3][x]>>24) < (uint8_t)(back >> 24))) {
				back = line[3][x];
				top2 = 0x08;
			}

			alpha_blend_brightness_switch();
		}
		else if((mask & 32) && (top & BLDMOD))
		{
			// special FX on in the window
			switch((BLDMOD >> 6) & 3)
			{
				case 0:
					break;
				case 1:
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;
						if(((mask & 1) && (uint8_t)(line[0][x]>>24) < (uint8_t)(back >> 24)) && top != 0x01)
						{
							back = line[0][x];
							top2 = 0x01;
						}

						if(((mask & 2) && (uint8_t)(line[1][x]>>24) < (uint8_t)(back >> 24)) && top != 0x02)
						{
							back = line[1][x];
							top2 = 0x02;
						}

						if(((mask & 4) && (uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24)) && top != 0x04)
						{
							back = line[2][x];
							top2 = 0x04;
						}

						if(((mask & 8) && (uint8_t)(line[3][x]>>24) < (uint8_t)(back >> 24)) && top != 0x08)
						{
							back = line[3][x];
							top2 = 0x08;
						}

						if(((mask & 16) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) && top != 0x10) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
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

static void mode1RenderLine (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 1: Render Line\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

  if(graphics.layerEnable & 0x0100) {
    gfxDrawTextScreen(io_registers[REG_BG0CNT], io_registers[REG_BG0HOFS], io_registers[REG_BG0VOFS], line[0]);
  }

  if(graphics.layerEnable & 0x0200) {
    gfxDrawTextScreen(io_registers[REG_BG1CNT], io_registers[REG_BG1HOFS], io_registers[REG_BG1VOFS], line[1]);
  }

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif
		gfxDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
				io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD],
				gfxBG2X, gfxBG2Y, changed, line[2]);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(uint32_t x = 0; x < 240u; ++x) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		uint8_t li1 = (uint8_t)(line[1][x]>>24);
		uint8_t li2 = (uint8_t)(line[2][x]>>24);
		uint8_t li4 = (uint8_t)(line[4][x]>>24);	

		uint8_t r = 	(li2 < li1) ? (li2) : (li1);

		if(li4 < r){
			r = 	(li4);
		}

		if(line[0][x] < backdrop) {
			color = line[0][x];
			top = 0x01;
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li1){
				color = line[1][x];
				top = 0x02;
			}else if(r == li2){
				color = line[2][x];
				top = 0x04;
			}else if(r == li4){
				color = line[4][x];
				top = 0x10;
				if((color & 0x00010000))
				{
					// semi-transparent OBJ
					uint32_t back = backdrop;
					uint8_t top2 = 0x20;

					uint8_t li0 = (uint8_t)(line[0][x]>>24);
					uint8_t li1 = (uint8_t)(line[1][x]>>24);
					uint8_t li2 = (uint8_t)(line[2][x]>>24);
					uint8_t r = 	(li1 < li0) ? (li1) : (li0);

					if(li2 < r) {
						r =  (li2);
					}

					if(r < (uint8_t)(back >> 24)) {
						if(r == li0){
							back = line[0][x];
							top2 = 0x01;
						}else if(r == li1){
							back = line[1][x];
							top2 = 0x02;
						}else if(r == li2){
							back = line[2][x];
							top2 = 0x04;
						}
					}

					alpha_blend_brightness_switch();
				}
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode1RenderLineNoWindow (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 1: Render Line No Window\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

  if(graphics.layerEnable & 0x0100) {
    gfxDrawTextScreen(io_registers[REG_BG0CNT], io_registers[REG_BG0HOFS], io_registers[REG_BG0VOFS], line[0]);
  }


  if(graphics.layerEnable & 0x0200) {
    gfxDrawTextScreen(io_registers[REG_BG1CNT], io_registers[REG_BG1HOFS], io_registers[REG_BG1VOFS], line[1]);
  }

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif
		gfxDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
				io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD],
				gfxBG2X, gfxBG2Y, changed, line[2]);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		uint8_t li1 = (uint8_t)(line[1][x]>>24);
		uint8_t li2 = (uint8_t)(line[2][x]>>24);
		uint8_t li4 = (uint8_t)(line[4][x]>>24);	

		uint8_t r = 	(li2 < li1) ? (li2) : (li1);

		if(li4 < r){
			r = 	(li4);
		}

		if(line[0][x] < backdrop) {
			color = line[0][x];
			top = 0x01;
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li1){
				color = line[1][x];
				top = 0x02;
			}else if(r == li2){
				color = line[2][x];
				top = 0x04;
			}else if(r == li4){
				color = line[4][x];
				top = 0x10;
			}
		}

		if(!(color & 0x00010000)) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;

						if((top != 0x01) && (uint8_t)(line[0][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[0][x];
							top2 = 0x01;
						}

						if((top != 0x02) && (uint8_t)(line[1][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[1][x];
							top2 = 0x02;
						}

						if((top != 0x04) && (uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			uint8_t li0 = (uint8_t)(line[0][x]>>24);
			uint8_t li1 = (uint8_t)(line[1][x]>>24);
			uint8_t li2 = (uint8_t)(line[2][x]>>24);	

			uint8_t r = 	(li1 < li0) ? (li1) : (li0);

			if(li2 < r) {
				r =  (li2);
			}

			if(r < (uint8_t)(back >> 24))
			{
				if(r == li0)
				{
					back = line[0][x];
					top2 = 0x01;
				}
				else if(r == li1)
				{
					back = line[1][x];
					top2 = 0x02;
				}
				else if(r == li2)
				{
					back = line[2][x];
					top2 = 0x04;
				}
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode1RenderLineAll (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 1: Render Line All\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	bool inWindow0 = false;
	bool inWindow1 = false;

	if(graphics.layerEnable & 0x2000)
	{
		uint8_t v0 = io_registers[REG_WIN0V] >> 8;
		uint8_t v1 = io_registers[REG_WIN0V] & 255;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow0 = (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}
	if(graphics.layerEnable & 0x4000)
	{
		uint8_t v0 = io_registers[REG_WIN1V] >> 8;
		uint8_t v1 = io_registers[REG_WIN1V] & 255;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow1 = (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

  if(graphics.layerEnable & 0x0100) {
    gfxDrawTextScreen(io_registers[REG_BG0CNT], io_registers[REG_BG0HOFS], io_registers[REG_BG0VOFS], line[0]);
  }

  if(graphics.layerEnable & 0x0200) {
    gfxDrawTextScreen(io_registers[REG_BG1CNT], io_registers[REG_BG1HOFS], io_registers[REG_BG1VOFS], line[1]);
  }

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif
		gfxDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
				io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD],
				gfxBG2X, gfxBG2Y, changed, line[2]);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	uint8_t inWin0Mask = io_registers[REG_WININ] & 0xFF;
	uint8_t inWin1Mask = io_registers[REG_WININ] >> 8;
	uint8_t outMask = io_registers[REG_WINOUT] & 0xFF;

	for(int x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;
		uint8_t mask = outMask;

		if(!(line[5][x] & 0x80000000)) {
			mask = io_registers[REG_WINOUT] >> 8;
		}

		int32_t window1_mask = ((inWindow1 & gfxInWin[1][x]) | -(inWindow1 & gfxInWin[1][x])) >> 31;
		int32_t window0_mask = ((inWindow0 & gfxInWin[0][x]) | -(inWindow0 & gfxInWin[0][x])) >> 31;
		mask = (inWin1Mask & window1_mask) | (mask & ~window1_mask);
		mask = (inWin0Mask & window0_mask) | (mask & ~window0_mask);

		// At the very least, move the inexpensive 'mask' operation up front
		if((mask & 1) && line[0][x] < backdrop) {
			color = line[0][x];
			top = 0x01;
		}

		if((mask & 2) && (uint8_t)(line[1][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[1][x];
			top = 0x02;
		}

		if((mask & 4) && (uint8_t)(line[2][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[2][x];
			top = 0x04;
		}

		if((mask & 16) && (uint8_t)(line[4][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[4][x];
			top = 0x10;
		}

		if(color & 0x00010000) {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			if((mask & 1) && (uint8_t)(line[0][x]>>24) < (uint8_t)(backdrop >> 24)) {
				back = line[0][x];
				top2 = 0x01;
			}

			if((mask & 2) && (uint8_t)(line[1][x]>>24) < (uint8_t)(back >> 24)) {
				back = line[1][x];
				top2 = 0x02;
			}

			if((mask & 4) && (uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24)) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		} else if(mask & 32) {
			// special FX on the window
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;

						if((mask & 1) && (top != 0x01) && (uint8_t)(line[0][x]>>24) < (uint8_t)(backdrop >> 24)) {
							back = line[0][x];
							top2 = 0x01;
						}

						if((mask & 2) && (top != 0x02) && (uint8_t)(line[1][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[1][x];
							top2 = 0x02;
						}

						if((mask & 4) && (top != 0x04) && (uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((mask & 16) && (top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

/*
Mode 2 is a 256 colour tiled graphics mode which supports scaling and rotation.
There is no background layer 0 or 1 in this mode. Only background layers 2 and 3.
There are 256 tiles available.
It does not support flipping.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode2RenderLine (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 2: Render Line\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
				io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD], gfxBG2X, gfxBG2Y,
				changed, line[2]);
	}

	if(graphics.layerEnable & 0x0800) {
		int changed = gfxBG3Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen(io_registers[REG_BG3CNT], BG3X_L, BG3X_H, BG3Y_L, BG3Y_H,
				io_registers[REG_BG3PA], io_registers[REG_BG3PB], io_registers[REG_BG3PC], io_registers[REG_BG3PD], gfxBG3X, gfxBG3Y,
				changed, line[3]);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		uint8_t li2 = (uint8_t)(line[2][x]>>24);
		uint8_t li3 = (uint8_t)(line[3][x]>>24);
		uint8_t li4 = (uint8_t)(line[4][x]>>24);	

		uint8_t r = 	(li3 < li2) ? (li3) : (li2);

		if(li4 < r){
			r = 	(li4);
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li2){
				color = line[2][x];
				top = 0x04;
			}else if(r == li3){
				color = line[3][x];
				top = 0x08;
			}else if(r == li4){
				color = line[4][x];
				top = 0x10;

				if(color & 0x00010000) {
					// semi-transparent OBJ
					uint32_t back = backdrop;
					uint8_t top2 = 0x20;

					uint8_t li2 = (uint8_t)(line[2][x]>>24);
					uint8_t li3 = (uint8_t)(line[3][x]>>24);
					uint8_t r = 	(li3 < li2) ? (li3) : (li2);

					if(r < (uint8_t)(back >> 24)) {
						if(r == li2){
							back = line[2][x];
							top2 = 0x04;
						}else if(r == li3){
							back = line[3][x];
							top2 = 0x08;
						}
					}

					alpha_blend_brightness_switch();
				}
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	gfxBG3Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode2RenderLineNoWindow (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 2: Render Line No Window\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
				io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD], gfxBG2X, gfxBG2Y,
				changed, line[2]);
	}

	if(graphics.layerEnable & 0x0800) {
		int changed = gfxBG3Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen(io_registers[REG_BG3CNT], BG3X_L, BG3X_H, BG3Y_L, BG3Y_H,
				io_registers[REG_BG3PA], io_registers[REG_BG3PB], io_registers[REG_BG3PC], io_registers[REG_BG3PD], gfxBG3X, gfxBG3Y,
				changed, line[3]);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		uint8_t li2 = (uint8_t)(line[2][x]>>24);
		uint8_t li3 = (uint8_t)(line[3][x]>>24);
		uint8_t li4 = (uint8_t)(line[4][x]>>24);	

		uint8_t r = 	(li3 < li2) ? (li3) : (li2);

		if(li4 < r){
			r = 	(li4);
		}

		if(r < (uint8_t)(color >> 24)) {
			if(r == li2){
				color = line[2][x];
				top = 0x04;
			}else if(r == li3){
				color = line[3][x];
				top = 0x08;
			}else if(r == li4){
				color = line[4][x];
				top = 0x10;
			}
		}

		if(!(color & 0x00010000)) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;

						if((top != 0x04) && (uint8_t)(line[2][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((top != 0x08) && (uint8_t)(line[3][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[3][x];
							top2 = 0x08;
						}

						if((top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			uint8_t li2 = (uint8_t)(line[2][x]>>24);
			uint8_t li3 = (uint8_t)(line[3][x]>>24);
			uint8_t r = 	(li3 < li2) ? (li3) : (li2);

			if(r < (uint8_t)(back >> 24)) {
				if(r == li2){
					back = line[2][x];
					top2 = 0x04;
				}else if(r == li3){
					back = line[3][x];
					top2 = 0x08;
				}
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	gfxBG3Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode2RenderLineAll (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 2: Render Line All\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	bool inWindow0 = false;
	bool inWindow1 = false;

	if(graphics.layerEnable & 0x2000)
	{
		uint8_t v0 = io_registers[REG_WIN0V] >> 8;
		uint8_t v1 = io_registers[REG_WIN0V] & 255;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow0 = (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}
	if(graphics.layerEnable & 0x4000)
	{
		uint8_t v0 = io_registers[REG_WIN1V] >> 8;
		uint8_t v1 = io_registers[REG_WIN1V] & 255;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow1 = (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen(io_registers[REG_BG2CNT], BG2X_L, BG2X_H, BG2Y_L, BG2Y_H,
				io_registers[REG_BG2PA], io_registers[REG_BG2PB], io_registers[REG_BG2PC], io_registers[REG_BG2PD], gfxBG2X, gfxBG2Y,
				changed, line[2]);
	}

	if(graphics.layerEnable & 0x0800) {
		int changed = gfxBG3Changed;
#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen(io_registers[REG_BG3CNT], BG3X_L, BG3X_H, BG3Y_L, BG3Y_H,
				io_registers[REG_BG3PA], io_registers[REG_BG3PB], io_registers[REG_BG3PC], io_registers[REG_BG3PD], gfxBG3X, gfxBG3Y,
				changed, line[3]);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	uint8_t inWin0Mask = io_registers[REG_WININ] & 0xFF;
	uint8_t inWin1Mask = io_registers[REG_WININ] >> 8;
	uint8_t outMask = io_registers[REG_WINOUT] & 0xFF;

	for(int x = 0; x < 240; x++) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;
		uint8_t mask = outMask;

		if(!(line[5][x] & 0x80000000)) {
			mask = io_registers[REG_WINOUT] >> 8;
		}

		int32_t window1_mask = ((inWindow1 & gfxInWin[1][x]) | -(inWindow1 & gfxInWin[1][x])) >> 31;
		int32_t window0_mask = ((inWindow0 & gfxInWin[0][x]) | -(inWindow0 & gfxInWin[0][x])) >> 31;
		mask = (inWin1Mask & window1_mask) | (mask & ~window1_mask);
		mask = (inWin0Mask & window0_mask) | (mask & ~window0_mask);

		if((mask & 4) && line[2][x] < color) {
			color = line[2][x];
			top = 0x04;
		}

		if((mask & 8) && (uint8_t)(line[3][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[3][x];
			top = 0x08;
		}

		if((mask & 16) && (uint8_t)(line[4][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[4][x];
			top = 0x10;
		}

		if(color & 0x00010000) {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			if((mask & 4) && line[2][x] < back) {
				back = line[2][x];
				top2 = 0x04;
			}

			if((mask & 8) && (uint8_t)(line[3][x]>>24) < (uint8_t)(back >> 24)) {
				back = line[3][x];
				top2 = 0x08;
			}

			alpha_blend_brightness_switch();
		} else if(mask & 32) {
			// special FX on the window
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;

						if((mask & 4) && (top != 0x04) && line[2][x] < back) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((mask & 8) && (top != 0x08) && (uint8_t)(line[3][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[3][x];
							top2 = 0x08;
						}

						if((mask & 16) && (top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	gfxBG3Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

/*
Mode 3 is a 15-bit (32768) colour bitmap graphics mode.
It has a single layer, background layer 2, the same size as the screen.
It doesn't support paging, scrolling, flipping, rotation or tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode3RenderLine (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 3: Render Line\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen16Bit(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t background = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = 0x20;

		if(line[2][x] < color) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24)) {
			color = line[4][x];
			top = 0x10;

			if(color & 0x00010000) {
				// semi-transparent OBJ
				uint32_t back = background;
				uint8_t top2 = 0x20;

				if(line[2][x] < background) {
					back = line[2][x];
					top2 = 0x04;
				}

				alpha_blend_brightness_switch();
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode3RenderLineNoWindow (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 3: Render Line No Window\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen16Bit(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t background = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = 0x20;

		if(line[2][x] < background) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24)) {
			color = line[4][x];
			top = 0x10;
		}

		if(!(color & 0x00010000)) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = background;
						uint8_t top2 = 0x20;

						if(top != 0x04 && (line[2][x] < background) ) {
							back = line[2][x];
							top2 = 0x04;
						}

						if(top != 0x10 && ((uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24))) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}

					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			// semi-transparent OBJ
			uint32_t back = background;
			uint8_t top2 = 0x20;

			if(line[2][x] < background) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode3RenderLineAll (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 3: Render Line All\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	bool inWindow0 = false;
	bool inWindow1 = false;

	if(graphics.layerEnable & 0x2000)
	{
		uint8_t v0 = io_registers[REG_WIN0V] >> 8;
		uint8_t v1 = io_registers[REG_WIN0V] & 255;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow0 = (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	if(graphics.layerEnable & 0x4000)
	{
		uint8_t v0 = io_registers[REG_WIN1V] >> 8;
		uint8_t v1 = io_registers[REG_WIN1V] & 255;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow1 = (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen16Bit(gfxBG2X, gfxBG2Y, changed);
	}

	uint8_t inWin0Mask = io_registers[REG_WININ] & 0xFF;
	uint8_t inWin1Mask = io_registers[REG_WININ] >> 8;
	uint8_t outMask = io_registers[REG_WINOUT] & 0xFF;

	uint32_t background = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = 0x20;
		uint8_t mask = outMask;

		if(!(line[5][x] & 0x80000000)) {
			mask = io_registers[REG_WINOUT] >> 8;
		}

		int32_t window1_mask = ((inWindow1 & gfxInWin[1][x]) | -(inWindow1 & gfxInWin[1][x])) >> 31;
		int32_t window0_mask = ((inWindow0 & gfxInWin[0][x]) | -(inWindow0 & gfxInWin[0][x])) >> 31;
		mask = (inWin1Mask & window1_mask) | (mask & ~window1_mask);
		mask = (inWin0Mask & window0_mask) | (mask & ~window0_mask);

		if((mask & 4) && line[2][x] < background) {
			color = line[2][x];
			top = 0x04;
		}

		if((mask & 16) && ((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24))) {
			color = line[4][x];
			top = 0x10;
		}

		if(color & 0x00010000) {
			// semi-transparent OBJ
			uint32_t back = background;
			uint8_t top2 = 0x20;

			if((mask & 4) && line[2][x] < background) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		} else if(mask & 32) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = background;
						uint8_t top2 = 0x20;

						if((mask & 4) && (top != 0x04) && line[2][x] < back) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((mask & 16) && (top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

/*
Mode 4 is a 256 colour bitmap graphics mode with 2 swappable pages.
It has a single layer, background layer 2, the same size as the screen.
It doesn't support scrolling, flipping, rotation or tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode4RenderLine (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 4: Render Line\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x400)
	{
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen256(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x)
	{
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		if(line[2][x] < backdrop) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[4][x];
			top = 0x10;

			if(color & 0x00010000) {
				// semi-transparent OBJ
				uint32_t back = backdrop;
				uint8_t top2 = 0x20;

				if(line[2][x] < backdrop) {
					back = line[2][x];
					top2 = 0x04;
				}

				alpha_blend_brightness_switch();
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode4RenderLineNoWindow (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 4: Render Line No Window\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x400)
	{
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen256(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x)
	{
		uint32_t color = backdrop;
		uint8_t top = 0x20;

		if(line[2][x] < backdrop) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >> 24)) {
			color = line[4][x];
			top = 0x10;
		}

		if(!(color & 0x00010000)) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;

						if((top != 0x04) && line[2][x] < backdrop) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			if(line[2][x] < back) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode4RenderLineAll (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 4: Render Line All\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	bool inWindow0 = false;
	bool inWindow1 = false;

	if(graphics.layerEnable & 0x2000)
	{
		uint8_t v0 = io_registers[REG_WIN0V] >> 8;
		uint8_t v1 = io_registers[REG_WIN0V] & 255;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow0 = (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	if(graphics.layerEnable & 0x4000)
	{
		uint8_t v0 = io_registers[REG_WIN1V] >> 8;
		uint8_t v1 = io_registers[REG_WIN1V] & 255;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow1 = (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	if(graphics.layerEnable & 0x400)
	{
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen256(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t backdrop = (READ16LE(&palette[0]) | 0x30000000);

	uint8_t inWin0Mask = io_registers[REG_WININ] & 0xFF;
	uint8_t inWin1Mask = io_registers[REG_WININ] >> 8;
	uint8_t outMask = io_registers[REG_WINOUT] & 0xFF;

	for(int x = 0; x < 240; ++x) {
		uint32_t color = backdrop;
		uint8_t top = 0x20;
		uint8_t mask = outMask;

		if(!(line[5][x] & 0x80000000))
			mask = io_registers[REG_WINOUT] >> 8;

		int32_t window1_mask = ((inWindow1 & gfxInWin[1][x]) | -(inWindow1 & gfxInWin[1][x])) >> 31;
		int32_t window0_mask = ((inWindow0 & gfxInWin[0][x]) | -(inWindow0 & gfxInWin[0][x])) >> 31;
		mask = (inWin1Mask & window1_mask) | (mask & ~window1_mask);
		mask = (inWin0Mask & window0_mask) | (mask & ~window0_mask);

		if((mask & 4) && (line[2][x] < backdrop))
		{
			color = line[2][x];
			top = 0x04;
		}

		if((mask & 16) && ((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24)))
		{
			color = line[4][x];
			top = 0x10;
		}

		if(color & 0x00010000) {
			// semi-transparent OBJ
			uint32_t back = backdrop;
			uint8_t top2 = 0x20;

			if((mask & 4) && line[2][x] < back) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		} else if(mask & 32) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = backdrop;
						uint8_t top2 = 0x20;

						if((mask & 4) && (top != 0x04) && (line[2][x] < backdrop)) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((mask & 16) && (top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

/*
Mode 5 is a low resolution (160x128) 15-bit colour bitmap graphics mode 
with 2 swappable pages!
It has a single layer, background layer 2, lower resolution than the screen.
It doesn't support scrolling, flipping, rotation or tiles.

These routines only render a single line at a time, because of the way the GBA does events.
*/

static void mode5RenderLine (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 5: Render Line\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();
	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen16Bit160(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t background;
	background = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = 0x20;

		if(line[2][x] < background) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24)) {
			color = line[4][x];
			top = 0x10;

			if(color & 0x00010000) {
				// semi-transparent OBJ
				uint32_t back = background;
				uint8_t top2 = 0x20;

				if(line[2][x] < back) {
					back = line[2][x];
					top2 = 0x04;
				}

				alpha_blend_brightness_switch();
			}
		}


		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode5RenderLineNoWindow (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 5: Render Line No Window\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400) {
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen16Bit160(gfxBG2X, gfxBG2Y, changed);
	}

	uint32_t background;
	background = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = 0x20;

		if(line[2][x] < background) {
			color = line[2][x];
			top = 0x04;
		}

		if((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24)) {
			color = line[4][x];
			top = 0x10;
		}

		if(!(color & 0x00010000)) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = background;
						uint8_t top2 = 0x20;

						if((top != 0x04) && line[2][x] < background) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}

					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		} else {
			// semi-transparent OBJ
			uint32_t back = background;
			uint8_t top2 = 0x20;

			if(line[2][x] < back) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void mode5RenderLineAll (void)
{
#ifdef REPORT_VIDEO_MODES
	fprintf(stderr, "MODE 5: Render Line All\n");
#endif
	INIT_COLOR_DEPTH_LINE_MIX();

	uint16_t *palette = (uint16_t *)graphics.paletteRAM;

	if(graphics.layerEnable & 0x0400)
	{
		int changed = gfxBG2Changed;

#if 0
		if(gfxLastVCOUNT > io_registers[REG_VCOUNT])
			changed = 3;
#endif

		gfxDrawRotScreen16Bit160(gfxBG2X, gfxBG2Y, changed);
	}



	bool inWindow0 = false;
	bool inWindow1 = false;

	if(graphics.layerEnable & 0x2000)
	{
		uint8_t v0 = io_registers[REG_WIN0V] >> 8;
		uint8_t v1 = io_registers[REG_WIN0V] & 255;
		inWindow0 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow0 = (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow0 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow0 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	if(graphics.layerEnable & 0x4000)
	{
		uint8_t v0 = io_registers[REG_WIN1V] >> 8;
		uint8_t v1 = io_registers[REG_WIN1V] & 255;
		inWindow1 = ((v0 == v1) && (v0 >= 0xe8));
#ifndef ORIGINAL_BRANCHES
		uint32_t condition = v1 >= v0;
		int32_t condition_mask = ((condition) | -(condition)) >> 31;
		inWindow1 = (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1)) & condition_mask) | (((inWindow1 | (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1)) & ~(condition_mask))));
#else
		if(v1 >= v0)
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 && io_registers[REG_VCOUNT] < v1);
		else
			inWindow1 |= (io_registers[REG_VCOUNT] >= v0 || io_registers[REG_VCOUNT] < v1);
#endif
	}

	uint8_t inWin0Mask = io_registers[REG_WININ] & 0xFF;
	uint8_t inWin1Mask = io_registers[REG_WININ] >> 8;
	uint8_t outMask = io_registers[REG_WINOUT] & 0xFF;

	uint32_t background;
	background = (READ16LE(&palette[0]) | 0x30000000);

	for(int x = 0; x < 240; ++x) {
		uint32_t color = background;
		uint8_t top = 0x20;
		uint8_t mask = outMask;

		if(!(line[5][x] & 0x80000000)) {
			mask = io_registers[REG_WINOUT] >> 8;
		}

		int32_t window1_mask = ((inWindow1 & gfxInWin[1][x]) | -(inWindow1 & gfxInWin[1][x])) >> 31;
		int32_t window0_mask = ((inWindow0 & gfxInWin[0][x]) | -(inWindow0 & gfxInWin[0][x])) >> 31;
		mask = (inWin1Mask & window1_mask) | (mask & ~window1_mask);
		mask = (inWin0Mask & window0_mask) | (mask & ~window0_mask);

		if((mask & 4) && (line[2][x] < background)) {
			color = line[2][x];
			top = 0x04;
		}

		if((mask & 16) && ((uint8_t)(line[4][x]>>24) < (uint8_t)(color >>24))) {
			color = line[4][x];
			top = 0x10;
		}

		if(color & 0x00010000) {
			// semi-transparent OBJ
			uint32_t back = background;
			uint8_t top2 = 0x20;

			if((mask & 4) && line[2][x] < back) {
				back = line[2][x];
				top2 = 0x04;
			}

			alpha_blend_brightness_switch();
		} else if(mask & 32) {
			switch((BLDMOD >> 6) & 3) {
				case 0:
					break;
				case 1:
					if(top & BLDMOD)
					{
						uint32_t back = background;
						uint8_t top2 = 0x20;

						if((mask & 4) && (top != 0x04) && (line[2][x] < background)) {
							back = line[2][x];
							top2 = 0x04;
						}

						if((mask & 16) && (top != 0x10) && (uint8_t)(line[4][x]>>24) < (uint8_t)(back >> 24)) {
							back = line[4][x];
							top2 = 0x10;
						}

						if(top2 & (BLDMOD>>8) && color < 0x80000000)
						{
							GFX_ALPHA_BLEND(color, back, coeff[COLEV & 0x1F], coeff[(COLEV >> 8) & 0x1F]);
						}
					}
					break;
				case 2:
					if(BLDMOD & top)
						color = gfxIncreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
				case 3:
					if(BLDMOD & top)
						color = gfxDecreaseBrightness(color, coeff[COLY & 0x1F]);
					break;
			}
		}

		lineMix[x] = CONVERT_COLOR(color);
	}
	gfxBG2Changed = 0;
	//gfxLastVCOUNT = io_registers[REG_VCOUNT];
}

static void (*renderLine)(void) = mode0RenderLine;
static bool render_line_all_enabled = false;

#define CPUUpdateRender() \
  render_line_all_enabled = false; \
  switch(io_registers[REG_DISPCNT] & 7) { \
  case 0: \
    if((!fxOn && !windowOn && !(graphics.layerEnable & 0x8000))) \
      renderLine = mode0RenderLine; \
    else if(fxOn && !windowOn && !(graphics.layerEnable & 0x8000)) \
      renderLine = mode0RenderLineNoWindow; \
    else { \
      renderLine = mode0RenderLineAll; \
      render_line_all_enabled = true; \
    } \
    break; \
  case 1: \
    if((!fxOn && !windowOn && !(graphics.layerEnable & 0x8000))) \
      renderLine = mode1RenderLine; \
    else if(fxOn && !windowOn && !(graphics.layerEnable & 0x8000)) \
      renderLine = mode1RenderLineNoWindow; \
    else { \
      renderLine = mode1RenderLineAll; \
      render_line_all_enabled = true; \
    } \
    break; \
  case 2: \
    if((!fxOn && !windowOn && !(graphics.layerEnable & 0x8000))) \
      renderLine = mode2RenderLine; \
    else if(fxOn && !windowOn && !(graphics.layerEnable & 0x8000)) \
      renderLine = mode2RenderLineNoWindow; \
    else { \
      renderLine = mode2RenderLineAll; \
      render_line_all_enabled = true; \
    } \
    break; \
  case 3: \
    if((!fxOn && !windowOn && !(graphics.layerEnable & 0x8000))) \
      renderLine = mode3RenderLine; \
    else if(fxOn && !windowOn && !(graphics.layerEnable & 0x8000)) \
      renderLine = mode3RenderLineNoWindow; \
    else { \
      renderLine = mode3RenderLineAll; \
      render_line_all_enabled = true; \
    } \
    break; \
  case 4: \
    if((!fxOn && !windowOn && !(graphics.layerEnable & 0x8000))) \
      renderLine = mode4RenderLine; \
    else if(fxOn && !windowOn && !(graphics.layerEnable & 0x8000)) \
      renderLine = mode4RenderLineNoWindow; \
    else { \
      renderLine = mode4RenderLineAll; \
      render_line_all_enabled = true; \
    } \
    break; \
  case 5: \
    if((!fxOn && !windowOn && !(graphics.layerEnable & 0x8000))) \
      renderLine = mode5RenderLine; \
    else if(fxOn && !windowOn && !(graphics.layerEnable & 0x8000)) \
      renderLine = mode5RenderLineNoWindow; \
    else { \
      renderLine = mode5RenderLineAll; \
      render_line_all_enabled = true; \
    } \
  }

bool CPUReadState(const uint8_t* data, unsigned size)
{
	// Don't really care about version.
	int version = utilReadIntMem(data);
	if (version != SAVE_GAME_VERSION)
		return false;

	char romname[16];
	utilReadMem(romname, data, 16);
	if (memcmp(&rom[0xa0], romname, 16) != 0)
		return false;

	// Don't care about use bios ...
	utilReadIntMem(data);

	utilReadMem(&bus.reg[0], data, sizeof(bus.reg));

	utilReadDataMem(data, saveGameStruct);

	stopState = utilReadIntMem(data) ? true : false;

	IRQTicks = utilReadIntMem(data);
	if (IRQTicks > 0)
		intState = true;
	else
	{
		intState = false;
		IRQTicks = 0;
	}

	utilReadMem(internalRAM, data, 0x8000);
	utilReadMem(graphics.paletteRAM, data, 0x400);
	utilReadMem(workRAM, data, 0x40000);
	utilReadMem(vram, data, 0x20000);
	utilReadMem(oam, data, 0x400);
	utilReadMem(pix, data, 4* PIX_BUFFER_SCREEN_WIDTH * 160);
	utilReadMem(ioMem, data, 0x400);

	eepromReadGameMem(data, version);
	flashReadGameMem(data, version);
	soundReadGameMem(data, version);
	rtcReadGameMem(data);

	//// Copypasta stuff ...
	// set pointers!
	graphics.layerEnable = io_registers[REG_DISPCNT];

	CPUUpdateRender();

	memset(line[0], -1, 240 * sizeof(u32));
	memset(line[1], -1, 240 * sizeof(u32));
	memset(line[2], -1, 240 * sizeof(u32));
	memset(line[3], -1, 240 * sizeof(u32));

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

	uint32_t CPSR = bus.reg[16].I;
	uint32_t SPSR = bus.reg[17].I;

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



void doDMA(uint32_t &s, uint32_t &d, uint32_t si, uint32_t di, uint32_t c, int transfer32)
{
	int sm = s >> 24;
	int dm = d >> 24;
	int sw = 0;
	int dw = 0;
	int sc = c;

	cpuDmaCount = c;
	// This is done to get the correct waitstates.
	int32_t sm_gt_15_mask = ((sm>15) | -(sm>15)) >> 31;
	int32_t dm_gt_15_mask = ((dm>15) | -(dm>15)) >> 31;
	sm = ((((15) & sm_gt_15_mask) | ((((sm) & ~(sm_gt_15_mask))))));
	dm = ((((15) & dm_gt_15_mask) | ((((dm) & ~(dm_gt_15_mask))))));

	//if ((sm>=0x05) && (sm<=0x07) || (dm>=0x05) && (dm <=0x07))
	//    blank = (((io_registers[REG_DISPSTAT] | ((io_registers[REG_DISPSTAT] >> 1)&1))==1) ?  true : false);

	if(transfer32)
	{
		s &= 0xFFFFFFFC;
		if(s < 0x02000000 && (bus.reg[15].I >> 24))
		{
			do
			{
				CPUWriteMemory(d, 0);
				d += di;
				c--;
			}while(c != 0);
		}
		else
		{
			do {
				CPUWriteMemory(d, CPUReadMemory(s));
				d += di;
				s += si;
				c--;
			}while(c != 0);
		}
	}
	else
	{
		s &= 0xFFFFFFFE;
		si = (int)si >> 1;
		di = (int)di >> 1;
		if(s < 0x02000000 && (bus.reg[15].I >> 24))
		{
			do {
				CPUWriteHalfWord(d, 0);
				d += di;
				c--;
			}while(c != 0);
		}
		else
		{
			do{
				CPUWriteHalfWord(d, CPUReadHalfWord(s));
				d += di;
				s += si;
				c--;
			}while(c != 0);
		}
	}

	cpuDmaCount = 0;

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
}


void CPUCheckDMA(int reason, int dmamask)
{
	uint32_t arrayval[] = {4, (uint32_t)-4, 0, 4};
	// DMA 0
	if((DM0CNT_H & 0x8000) && (dmamask & 1))
	{
		if(((DM0CNT_H >> 12) & 3) == reason)
		{
			uint32_t sourceIncrement, destIncrement;
			uint32_t condition1 = ((DM0CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM0CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			doDMA(dma0Source, dma0Dest, sourceIncrement, destIncrement,
					DM0CNT_L ? DM0CNT_L : 0x4000,
					DM0CNT_H & 0x0400);

			if(DM0CNT_H & 0x4000)
			{
				io_registers[REG_IF] |= 0x0100;
				UPDATE_REG(0x202, io_registers[REG_IF]);
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM0CNT_H >> 5) & 3) == 3) {
				dma0Dest = DM0DAD_L | (DM0DAD_H << 16);
			}

			if(!(DM0CNT_H & 0x0200) || (reason == 0)) {
				DM0CNT_H &= 0x7FFF;
				UPDATE_REG(0xBA, DM0CNT_H);
			}
		}
	}

	// DMA 1
	if((DM1CNT_H & 0x8000) && (dmamask & 2)) {
		if(((DM1CNT_H >> 12) & 3) == reason) {
			uint32_t sourceIncrement, destIncrement;
			uint32_t condition1 = ((DM1CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM1CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			uint32_t di_value, c_value, transfer_value;
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
			doDMA(dma1Source, dma1Dest, sourceIncrement, di_value, c_value, transfer_value);

			if(DM1CNT_H & 0x4000) {
				io_registers[REG_IF] |= 0x0200;
				UPDATE_REG(0x202, io_registers[REG_IF]);
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM1CNT_H >> 5) & 3) == 3) {
				dma1Dest = DM1DAD_L | (DM1DAD_H << 16);
			}

			if(!(DM1CNT_H & 0x0200) || (reason == 0)) {
				DM1CNT_H &= 0x7FFF;
				UPDATE_REG(0xC6, DM1CNT_H);
			}
		}
	}

	// DMA 2
	if((DM2CNT_H & 0x8000) && (dmamask & 4)) {
		if(((DM2CNT_H >> 12) & 3) == reason) {
			uint32_t sourceIncrement, destIncrement;
			uint32_t condition1 = ((DM2CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM2CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			uint32_t di_value, c_value, transfer_value;
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
			doDMA(dma2Source, dma2Dest, sourceIncrement, di_value, c_value, transfer_value);

			if(DM2CNT_H & 0x4000) {
				io_registers[REG_IF] |= 0x0400;
				UPDATE_REG(0x202, io_registers[REG_IF]);
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM2CNT_H >> 5) & 3) == 3) {
				dma2Dest = DM2DAD_L | (DM2DAD_H << 16);
			}

			if(!(DM2CNT_H & 0x0200) || (reason == 0)) {
				DM2CNT_H &= 0x7FFF;
				UPDATE_REG(0xD2, DM2CNT_H);
			}
		}
	}

	// DMA 3
	if((DM3CNT_H & 0x8000) && (dmamask & 8))
	{
		if(((DM3CNT_H >> 12) & 3) == reason)
		{
			uint32_t sourceIncrement, destIncrement;
			uint32_t condition1 = ((DM3CNT_H >> 7) & 3);
			uint32_t condition2 = ((DM3CNT_H >> 5) & 3);
			sourceIncrement = arrayval[condition1];
			destIncrement = arrayval[condition2];
			doDMA(dma3Source, dma3Dest, sourceIncrement, destIncrement,
					DM3CNT_L ? DM3CNT_L : 0x10000,
					DM3CNT_H & 0x0400);
			if(DM3CNT_H & 0x4000) {
				io_registers[REG_IF] |= 0x0800;
				UPDATE_REG(0x202, io_registers[REG_IF]);
				cpuNextEvent = cpuTotalTicks;
			}

			if(((DM3CNT_H >> 5) & 3) == 3) {
				dma3Dest = DM3DAD_L | (DM3DAD_H << 16);
			}

			if(!(DM3CNT_H & 0x0200) || (reason == 0)) {
				DM3CNT_H &= 0x7FFF;
				UPDATE_REG(0xDE, DM3CNT_H);
			}
		}
	}
}

static uint16_t *address_lut[0x300];

void CPUUpdateRegister(uint32_t address, uint16_t value)
{
	switch(address)
	{
		case 0x00:
			{
				if((value & 7) > 5) // display modes above 0-5 are prohibited
					io_registers[REG_DISPCNT] = (value & 7);

				bool change = (0 != ((io_registers[REG_DISPCNT] ^ value) & 0x80));
				bool changeBG = (0 != ((io_registers[REG_DISPCNT] ^ value) & 0x0F00));
				uint16_t changeBGon = ((~io_registers[REG_DISPCNT]) & value) & 0x0F00; // these layers are being activated

				io_registers[REG_DISPCNT] = (value & 0xFFF7); // bit 3 can only be accessed by the BIOS to enable GBC mode
				UPDATE_REG(0x00, io_registers[REG_DISPCNT]);

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
						io_registers[REG_DISPSTAT] &= 0xFFFC;
						UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
						CPUCompareVCOUNT();
					}
				}
				CPUUpdateRender();
				// we only care about changes in BG0-BG3
				if(changeBG)
				{
					if(!(graphics.layerEnable & 0x0100))
						memset(line[0], -1, 240 * sizeof(u32));
					if(!(graphics.layerEnable & 0x0200))
						memset(line[1], -1, 240 * sizeof(u32));
					if(!(graphics.layerEnable & 0x0400))
						memset(line[2], -1, 240 * sizeof(u32));
					if(!(graphics.layerEnable & 0x0800))
						memset(line[3], -1, 240 * sizeof(u32));
				}
				break;
			}
		case 0x04:
			io_registers[REG_DISPSTAT] = (value & 0xFF38) | (io_registers[REG_DISPSTAT] & 7);
			UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
			break;
		case 0x06:
			// not writable
			break;
		case 0x08: /* BG0CNT */
		case 0x0A: /* BG1CNT */
			*address_lut[address] = (value & 0xDFCF);
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x0C: /* BG2CNT */
		case 0x0E: /* BG3CNT */
			*address_lut[address] = (value & 0xFFCF);
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x10: /* BG0HOFS */
		case 0x12: /* BG0VOFS */
		case 0x14: /* BG1HOFS */
		case 0x16: /* BG1VOFS */
		case 0x18: /* BG2HOFS */
		case 0x1A: /* BG2VOFS */
		case 0x1C: /* BG3HOFS */
		case 0x1E: /* BG3VOFS */
			*address_lut[address] = value & 511;
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x20: /* BG2PA */
		case 0x22: /* BG2PB */
		case 0x24: /* BG2PC */
		case 0x26: /* BG2PD */
			*address_lut[address] = value;
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x28:
			BG2X_L = value;
			UPDATE_REG(0x28, BG2X_L);
			gfxBG2Changed |= 1;
			break;
		case 0x2A:
			BG2X_H = (value & 0xFFF);
			UPDATE_REG(0x2A, BG2X_H);
			gfxBG2Changed |= 1;
			break;
		case 0x2C:
			BG2Y_L = value;
			UPDATE_REG(0x2C, BG2Y_L);
			gfxBG2Changed |= 2;
			break;
		case 0x2E:
			BG2Y_H = value & 0xFFF;
			UPDATE_REG(0x2E, BG2Y_H);
			gfxBG2Changed |= 2;
			break;
		case 0x30: /* BG3PA */
		case 0x32: /* BG3PB */
		case 0x34: /* BG3PC */
		case 0x36: /* BG3PD */
			*address_lut[address] = value;
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x38:
			BG3X_L = value;
			UPDATE_REG(0x38, BG3X_L);
			gfxBG3Changed |= 1;
			break;
		case 0x3A:
			BG3X_H = value & 0xFFF;
			UPDATE_REG(0x3A, BG3X_H);
			gfxBG3Changed |= 1;
			break;
		case 0x3C:
			BG3Y_L = value;
			UPDATE_REG(0x3C, BG3Y_L);
			gfxBG3Changed |= 2;
			break;
		case 0x3E:
			BG3Y_H = value & 0xFFF;
			UPDATE_REG(0x3E, BG3Y_H);
			gfxBG3Changed |= 2;
			break;
		case 0x40:
			io_registers[REG_WIN0H] = value;
			UPDATE_REG(0x40, io_registers[REG_WIN0H]);
			CPUUpdateWindow0();
			break;
		case 0x42:
			io_registers[REG_WIN1H] = value;
			UPDATE_REG(0x42, io_registers[REG_WIN1H]);
			CPUUpdateWindow1();
			break;
		case 0x44:
		case 0x46:
			*address_lut[address] = value;
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x48: /* WININ */
		case 0x4A: /* WINOUT */
			*address_lut[address] = value & 0x3F3F;
			UPDATE_REG(address, *address_lut[address]);
			break;
		case 0x4C:
			MOSAIC = value;
			UPDATE_REG(0x4C, MOSAIC);
			break;
		case 0x50:
			BLDMOD = value & 0x3FFF;
			UPDATE_REG(0x50, BLDMOD);
			fxOn = ((BLDMOD>>6)&3) != 0;
			CPUUpdateRender();
			break;
		case 0x52:
			COLEV = value & 0x1F1F;
			UPDATE_REG(0x52, COLEV);
			break;
		case 0x54:
			COLY = value & 0x1F;
			UPDATE_REG(0x54, COLY);
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
			{
				int gb_addr[2] = {address & 0xFF, (address & 0xFF) + 1};
				uint32_t address_array[2] = {address & 0xFF, (address&0xFF)+1};
				uint8_t data_array[2] = {(uint8_t)(value & 0xFF), (uint8_t)(value>>8)};
				gb_addr[0] = table[gb_addr[0] - 0x60];
				gb_addr[1] = table[gb_addr[1] - 0x60];
				soundEvent_u8_parallel(gb_addr, address_array, data_array);
				break;
			}
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
			DM0SAD_L = value;
			UPDATE_REG(0xB0, DM0SAD_L);
			break;
		case 0xB2:
			DM0SAD_H = value & 0x07FF;
			UPDATE_REG(0xB2, DM0SAD_H);
			break;
		case 0xB4:
			DM0DAD_L = value;
			UPDATE_REG(0xB4, DM0DAD_L);
			break;
		case 0xB6:
			DM0DAD_H = value & 0x07FF;
			UPDATE_REG(0xB6, DM0DAD_H);
			break;
		case 0xB8:
			DM0CNT_L = value & 0x3FFF;
			UPDATE_REG(0xB8, 0);
			break;
		case 0xBA:
			{
				bool start = ((DM0CNT_H ^ value) & 0x8000) ? true : false;
				value &= 0xF7E0;

				DM0CNT_H = value;
				UPDATE_REG(0xBA, DM0CNT_H);

				if(start && (value & 0x8000))
				{
					dma0Source = DM0SAD_L | (DM0SAD_H << 16);
					dma0Dest = DM0DAD_L | (DM0DAD_H << 16);
					CPUCheckDMA(0, 1);
				}
			}
			break;
		case 0xBC:
			DM1SAD_L = value;
			UPDATE_REG(0xBC, DM1SAD_L);
			break;
		case 0xBE:
			DM1SAD_H = value & 0x0FFF;
			UPDATE_REG(0xBE, DM1SAD_H);
			break;
		case 0xC0:
			DM1DAD_L = value;
			UPDATE_REG(0xC0, DM1DAD_L);
			break;
		case 0xC2:
			DM1DAD_H = value & 0x07FF;
			UPDATE_REG(0xC2, DM1DAD_H);
			break;
		case 0xC4:
			DM1CNT_L = value & 0x3FFF;
			UPDATE_REG(0xC4, 0);
			break;
		case 0xC6:
			{
				bool start = ((DM1CNT_H ^ value) & 0x8000) ? true : false;
				value &= 0xF7E0;

				DM1CNT_H = value;
				UPDATE_REG(0xC6, DM1CNT_H);

				if(start && (value & 0x8000))
				{
					dma1Source = DM1SAD_L | (DM1SAD_H << 16);
					dma1Dest = DM1DAD_L | (DM1DAD_H << 16);
					CPUCheckDMA(0, 2);
				}
			}
			break;
		case 0xC8:
			DM2SAD_L = value;
			UPDATE_REG(0xC8, DM2SAD_L);
			break;
		case 0xCA:
			DM2SAD_H = value & 0x0FFF;
			UPDATE_REG(0xCA, DM2SAD_H);
			break;
		case 0xCC:
			DM2DAD_L = value;
			UPDATE_REG(0xCC, DM2DAD_L);
			break;
		case 0xCE:
			DM2DAD_H = value & 0x07FF;
			UPDATE_REG(0xCE, DM2DAD_H);
			break;
		case 0xD0:
			DM2CNT_L = value & 0x3FFF;
			UPDATE_REG(0xD0, 0);
			break;
		case 0xD2:
			{
				bool start = ((DM2CNT_H ^ value) & 0x8000) ? true : false;

				value &= 0xF7E0;

				DM2CNT_H = value;
				UPDATE_REG(0xD2, DM2CNT_H);

				if(start && (value & 0x8000)) {
					dma2Source = DM2SAD_L | (DM2SAD_H << 16);
					dma2Dest = DM2DAD_L | (DM2DAD_H << 16);

					CPUCheckDMA(0, 4);
				}
			}
			break;
		case 0xD4:
			DM3SAD_L = value;
			UPDATE_REG(0xD4, DM3SAD_L);
			break;
		case 0xD6:
			DM3SAD_H = value & 0x0FFF;
			UPDATE_REG(0xD6, DM3SAD_H);
			break;
		case 0xD8:
			DM3DAD_L = value;
			UPDATE_REG(0xD8, DM3DAD_L);
			break;
		case 0xDA:
			DM3DAD_H = value & 0x0FFF;
			UPDATE_REG(0xDA, DM3DAD_H);
			break;
		case 0xDC:
			DM3CNT_L = value;
			UPDATE_REG(0xDC, 0);
			break;
		case 0xDE:
			{
				bool start = ((DM3CNT_H ^ value) & 0x8000) ? true : false;

				value &= 0xFFE0;

				DM3CNT_H = value;
				UPDATE_REG(0xDE, DM3CNT_H);

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
			io_registers[REG_P1] |= (value & 0x3FF);
			UPDATE_REG(0x130, io_registers[REG_P1]);
			break;
		case 0x132:
			UPDATE_REG(0x132, value & 0xC3FF);
			break;


		case 0x200:
			io_registers[REG_IE] = value & 0x3FFF;
			UPDATE_REG(0x200, io_registers[REG_IE]);
			if ((io_registers[REG_IME] & 1) && (io_registers[REG_IF] & io_registers[REG_IE]) && armIrqEnable)
				cpuNextEvent = cpuTotalTicks;
			break;
		case 0x202:
			io_registers[REG_IF] ^= (value & io_registers[REG_IF]);
			UPDATE_REG(0x202, io_registers[REG_IF]);
			break;
		case 0x204:
			{
				memoryWait[0x0e] = memoryWaitSeq[0x0e] = gamepakRamWaitState[value & 3];

				memoryWait[0x08] = memoryWait[0x09] = 3;
				memoryWaitSeq[0x08] = memoryWaitSeq[0x09] = 1;

				memoryWait[0x0a] = memoryWait[0x0b] = 3;
				memoryWaitSeq[0x0a] = memoryWaitSeq[0x0b] = 1;

				memoryWait[0x0c] = memoryWait[0x0d] = 3;
				memoryWaitSeq[0x0c] = memoryWaitSeq[0x0d] = 1;

				memoryWait32[8] = memoryWait[8] + memoryWaitSeq[8] + 1;
				memoryWaitSeq32[8] = memoryWaitSeq[8]*2 + 1;

				memoryWait32[9] = memoryWait[9] + memoryWaitSeq[9] + 1;
				memoryWaitSeq32[9] = memoryWaitSeq[9]*2 + 1;

				memoryWait32[10] = memoryWait[10] + memoryWaitSeq[10] + 1;
				memoryWaitSeq32[10] = memoryWaitSeq[10]*2 + 1;

				memoryWait32[11] = memoryWait[11] + memoryWaitSeq[11] + 1;
				memoryWaitSeq32[11] = memoryWaitSeq[11]*2 + 1;

				memoryWait32[12] = memoryWait[12] + memoryWaitSeq[12] + 1;
				memoryWaitSeq32[12] = memoryWaitSeq[12]*2 + 1;

				memoryWait32[13] = memoryWait[13] + memoryWaitSeq[13] + 1;
				memoryWaitSeq32[13] = memoryWaitSeq[13]*2 + 1;

				memoryWait32[14] = memoryWait[14] + memoryWaitSeq[14] + 1;
				memoryWaitSeq32[14] = memoryWaitSeq[14]*2 + 1;

				if((value & 0x4000) == 0x4000)
					bus.busPrefetchEnable = true;
				else
					bus.busPrefetchEnable = false;

				bus.busPrefetch = false;
				bus.busPrefetchCount = 0;

				UPDATE_REG(0x204, value & 0x7FFF);

			}
			break;
		case 0x208:
			io_registers[REG_IME] = value & 1;
			UPDATE_REG(0x208, io_registers[REG_IME]);
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


void CPUInit(const char *biosFileName, bool useBiosFile)
{
#ifndef LSB_FIRST
	if(!cpuBiosSwapped) {
		for(unsigned int i = 0; i < sizeof(myROM)/4; i++) {
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
		if(utilLoad(biosFileName, CPUIsGBABios, bios, size))
		{
			if(size == 0x4000)
				useBios = true;
		}
	}
#endif

#ifdef HAVE_HLE_BIOS
	if(!useBios)
#endif
		memcpy(bios, myROM, sizeof(myROM));

	int i = 0;

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

		for(j = 0; j < 8; j++)
			if(i & (1 << j))
				break;
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
		*((uint16_t *)&rom[0x1fe209c]) = 0xdffa; // SWI 0xFA
		*((uint16_t *)&rom[0x1fe209e]) = 0x4770; // BX LR
	}

	graphics.layerEnable = 0xff00;
	graphics.layerEnableDelay = 1;
	io_registers[REG_DISPCNT] = 0x0080;
	io_registers[REG_DISPSTAT] = 0;
	graphics.lcdTicks = (useBios && !skipBios) ? 1008 : 208;

	/* address lut for use in CPUUpdateRegister */
	address_lut[0x08] = &io_registers[REG_BG0CNT];
	address_lut[0x0A] = &io_registers[REG_BG1CNT];
	address_lut[0x0C] = &io_registers[REG_BG2CNT];
	address_lut[0x0E] = &io_registers[REG_BG3CNT];
	address_lut[0x10] = &io_registers[REG_BG0HOFS];
	address_lut[0x12] = &io_registers[REG_BG0VOFS];
	address_lut[0x14] = &io_registers[REG_BG1HOFS];
	address_lut[0x16] = &io_registers[REG_BG1VOFS];
	address_lut[0x18] = &io_registers[REG_BG2HOFS];
	address_lut[0x1A] = &io_registers[REG_BG2VOFS];
	address_lut[0x1C] = &io_registers[REG_BG3HOFS];
	address_lut[0x1E] = &io_registers[REG_BG3VOFS];
	address_lut[0x20] = &io_registers[REG_BG2PA];
	address_lut[0x22] = &io_registers[REG_BG2PB];
	address_lut[0x24] = &io_registers[REG_BG2PC];
	address_lut[0x26] = &io_registers[REG_BG2PD];
	address_lut[0x48] = &io_registers[REG_WININ];
	address_lut[0x4A] = &io_registers[REG_WINOUT];
	address_lut[0x30] = &io_registers[REG_BG3PA];
	address_lut[0x32] = &io_registers[REG_BG3PB];
	address_lut[0x34] = &io_registers[REG_BG3PC];
	address_lut[0x36] = &io_registers[REG_BG3PD];
        address_lut[0x40] = &io_registers[REG_WIN0H];
        address_lut[0x42] = &io_registers[REG_WIN1H];
        address_lut[0x44] = &io_registers[REG_WIN0V];
        address_lut[0x46] = &io_registers[REG_WIN1V];
}

void CPUReset (void)
{
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
	memset(&bus.reg[0], 0, sizeof(bus.reg));	// clean registers
	memset(oam, 0, 0x400);				// clean OAM
	memset(graphics.paletteRAM, 0, 0x400);		// clean palette
	memset(pix, 0, 4 * 160 * 240);			// clean picture
	memset(vram, 0, 0x20000);			// clean vram
	memset(ioMem, 0, 0x400);			// clean io memory

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

	if(cpuIsMultiBoot) {
		bus.reg[13].I = 0x03007F00;
		bus.reg[15].I = 0x02000000;
		bus.reg[16].I = 0x00000000;
		bus.reg[R13_IRQ].I = 0x03007FA0;
		bus.reg[R13_SVC].I = 0x03007FE0;
		armIrqEnable = true;
	} else {
#ifdef HAVE_HLE_BIOS
		if(useBios && !skipBios)
		{
			bus.reg[15].I = 0x00000000;
			armMode = 0x13;
			armIrqEnable = false;
		}
		else
		{
#endif
			bus.reg[13].I = 0x03007F00;
			bus.reg[15].I = 0x08000000;
			bus.reg[16].I = 0x00000000;
			bus.reg[R13_IRQ].I = 0x03007FA0;
			bus.reg[R13_SVC].I = 0x03007FE0;
			armIrqEnable = true;
#ifdef HAVE_HLE_BIOS
		}
#endif
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

	// disable FIQ
	bus.reg[16].I |= 0x40;

	CPU_UPDATE_CPSR();

	bus.armNextPC = bus.reg[15].I;
	bus.reg[15].I += 4;

	// reset internal state
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
	renderLine = mode0RenderLine;
	fxOn = false;
	windowOn = false;
	saveType = 0;
	graphics.layerEnable = io_registers[REG_DISPCNT];

	memset(line[0], -1, 240 * sizeof(u32));
	memset(line[1], -1, 240 * sizeof(u32));
	memset(line[2], -1, 240 * sizeof(u32));
	memset(line[3], -1, 240 * sizeof(u32));

	for(int i = 0; i < 256; i++) {
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
	map[5].address = graphics.paletteRAM;
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

	// make sure registers are correctly initialized if not using BIOS
	if(cpuIsMultiBoot)
		BIOS_RegisterRamReset(0xfe);
	else if(!useBios && !cpuIsMultiBoot)
		BIOS_RegisterRamReset(0xff);
		
	switch(cpuSaveType) {
		case 0: // automatic
			cpuSramEnabled = true;
			cpuFlashEnabled = true;
			cpuEEPROMEnabled = true;
			cpuEEPROMSensorEnabled = false;
			saveType = gbaSaveType = 0;
			break;
		case 1: // EEPROM
			cpuSramEnabled = false;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = true;
			cpuEEPROMSensorEnabled = false;
			saveType = gbaSaveType = 3;
			// EEPROM usage is automatically detected
			break;
		case 2: // SRAM
			cpuSramEnabled = true;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = false;
			cpuEEPROMSensorEnabled = false;
			cpuSaveGameFunc = sramDelayedWrite; // to insure we detect the write
			saveType = gbaSaveType = 1;
			break;
		case 3: // FLASH
			cpuSramEnabled = false;
			cpuFlashEnabled = true;
			cpuEEPROMEnabled = false;
			cpuEEPROMSensorEnabled = false;
			cpuSaveGameFunc = flashDelayedWrite; // to insure we detect the write
			saveType = gbaSaveType = 2;
			break;
		case 4: // EEPROM+Sensor
			cpuSramEnabled = false;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = true;
			cpuEEPROMSensorEnabled = true;
			// EEPROM usage is automatically detected
			saveType = gbaSaveType = 3;
			break;
		case 5: // NONE
			cpuSramEnabled = false;
			cpuFlashEnabled = false;
			cpuEEPROMEnabled = false;
			cpuEEPROMSensorEnabled = false;
			// no save at all
			saveType = gbaSaveType = 5;
			break;
	}

	ARM_PREFETCH;

#ifdef USE_SWITICKS
	SWITicks = 0;
#endif
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

	//  if(!holdState)
	biosProtected[0] = 0x02;
	biosProtected[1] = 0xc0;
	biosProtected[2] = 0x5e;
	biosProtected[3] = 0xe5;
}

void CPULoop (void)
{
	bus.busPrefetchCount = 0;
	int ticks = 250000;
	int timerOverflow = 0;
	// variable used by the CPU core
	cpuTotalTicks = 0;

	cpuNextEvent = CPUUpdateTicks();
	if(cpuNextEvent > ticks)
		cpuNextEvent = ticks;


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

#ifdef USE_SWITICKS
			if (SWITicks)
			{
				SWITicks-=clockTicks;
				if (SWITicks<0)
					SWITicks = 0;
			}
#endif

			clockTicks = cpuNextEvent;
			cpuTotalTicks = 0;

updateLoop:

			if (IRQTicks)
			{
				IRQTicks -= clockTicks;
				if (IRQTicks<0)
					IRQTicks = 0;
			}

			graphics.lcdTicks -= clockTicks;

			if(graphics.lcdTicks <= 0)
			{
				if(io_registers[REG_DISPSTAT] & 1)
				{ // V-BLANK
					// if in V-Blank mode, keep computing...
					if(io_registers[REG_DISPSTAT] & 2)
					{
						graphics.lcdTicks += 1008;
						io_registers[REG_VCOUNT] += 1;
						UPDATE_REG(0x06, io_registers[REG_VCOUNT]);
						io_registers[REG_DISPSTAT] &= 0xFFFD;
						UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
						CPUCompareVCOUNT();
					}
					else
					{
						graphics.lcdTicks += 224;
						io_registers[REG_DISPSTAT] |= 2;
						UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
						if(io_registers[REG_DISPSTAT] & 16)
						{
							io_registers[REG_IF] |= 2;
							UPDATE_REG(0x202, io_registers[REG_IF]);
						}
					}

					if(io_registers[REG_VCOUNT] >= 228)
					{
						//Reaching last line
						io_registers[REG_DISPSTAT] &= 0xFFFC;
						UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
						io_registers[REG_VCOUNT] = 0;
						UPDATE_REG(0x06, io_registers[REG_VCOUNT]);
						CPUCompareVCOUNT();
					}
				}
				else if(io_registers[REG_DISPSTAT] & 2)
				{
					// if in H-Blank, leave it and move to drawing mode
					io_registers[REG_VCOUNT] += 1;
					UPDATE_REG(0x06, io_registers[REG_VCOUNT]);

					graphics.lcdTicks += 1008;
					io_registers[REG_DISPSTAT] &= 0xFFFD;
					if(io_registers[REG_VCOUNT] == 160)
					{
						/* update joystick information */
						io_registers[REG_P1] = 0x03FF ^ (joy & 0x3FF);
#if 0
						if(cpuEEPROMSensorEnabled)
							systemUpdateMotionSensor();
#endif
						UPDATE_REG(0x130, io_registers[REG_P1]);
						io_registers[REG_P1CNT] = READ16LE(((uint16_t *)&ioMem[0x132]));

						// this seems wrong, but there are cases where the game
						// can enter the stop state without requesting an IRQ from
						// the joypad.
						if((io_registers[REG_P1CNT] & 0x4000) || stopState) {
							uint16_t p1 = (0x3FF ^ io_registers[REG_P1CNT]) & 0x3FF;
							if(io_registers[REG_P1CNT] & 0x8000) {
								if(p1 == (io_registers[REG_P1CNT] & 0x3FF)) {
									io_registers[REG_IF] |= 0x1000;
									UPDATE_REG(0x202, io_registers[REG_IF]);
								}
							} else {
								if(p1 & io_registers[REG_P1CNT]) {
									io_registers[REG_IF] |= 0x1000;
									UPDATE_REG(0x202, io_registers[REG_IF]);
								}
							}
						}

						io_registers[REG_DISPSTAT] |= 1;
						io_registers[REG_DISPSTAT] &= 0xFFFD;
						UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
						if(io_registers[REG_DISPSTAT] & 0x0008)
						{
							io_registers[REG_IF] |= 1;
							UPDATE_REG(0x202, io_registers[REG_IF]);
						}
						CPUCheckDMA(1, 0x0f);
						systemDrawScreen();
					}

					UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
					CPUCompareVCOUNT();
				}
				else
				{
					bool draw_objwin = (graphics.layerEnable & 0x9000) == 0x9000;
					bool draw_sprites = graphics.layerEnable & 0x1000;
					memset(line[4], -1, 240 * sizeof(u32));	// erase all sprites

					if(draw_sprites)
						gfxDrawSprites();

					if(render_line_all_enabled)
					{
						memset(line[5], -1, 240 * sizeof(u32));	// erase all OBJ Win 
						if(draw_objwin)
							gfxDrawOBJWin();
					}

					(*renderLine)();

					// entering H-Blank
					io_registers[REG_DISPSTAT] |= 2;
					UPDATE_REG(0x04, io_registers[REG_DISPSTAT]);
					graphics.lcdTicks += 224;
					CPUCheckDMA(2, 0x0f);
					if(io_registers[REG_DISPSTAT] & 16)
					{
						io_registers[REG_IF] |= 2;
						UPDATE_REG(0x202, io_registers[REG_IF]);
					}
				}
			}

			// we shouldn't be doing sound in stop state, but we lose synchronization
			// if sound is disabled, so in stop state, soundTick will just produce
			// mute sound
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
							io_registers[REG_IF] |= 0x08;
							UPDATE_REG(0x202, io_registers[REG_IF]);
						}
					}
					io_registers[REG_TM0D] = 0xFFFF - (timer0Ticks >> timer0ClockReload);
					UPDATE_REG(0x100, io_registers[REG_TM0D]);
				}

				if(timer1On) {
					if(io_registers[REG_TM1CNT] & 4) {
						if(timerOverflow & 1) {
							io_registers[REG_TM1D]++;
							if(io_registers[REG_TM1D] == 0) {
								io_registers[REG_TM1D] += timer1Reload;
								timerOverflow |= 2;
								soundTimerOverflow(1);
								if(io_registers[REG_TM1CNT] & 0x40) {
									io_registers[REG_IF] |= 0x10;
									UPDATE_REG(0x202, io_registers[REG_IF]);
								}
							}
							UPDATE_REG(0x104, io_registers[REG_TM1D]);
						}
					} else {
						timer1Ticks -= clockTicks;
						if(timer1Ticks <= 0) {
							timer1Ticks += (0x10000 - timer1Reload) << timer1ClockReload;
							timerOverflow |= 2;
							soundTimerOverflow(1);
							if(io_registers[REG_TM1CNT] & 0x40) {
								io_registers[REG_IF] |= 0x10;
								UPDATE_REG(0x202, io_registers[REG_IF]);
							}
						}
						io_registers[REG_TM1D] = 0xFFFF - (timer1Ticks >> timer1ClockReload);
						UPDATE_REG(0x104, io_registers[REG_TM1D]);
					}
				}

				if(timer2On) {
					if(io_registers[REG_TM2CNT] & 4) {
						if(timerOverflow & 2) {
							io_registers[REG_TM2D]++;
							if(io_registers[REG_TM2D] == 0) {
								io_registers[REG_TM2D] += timer2Reload;
								timerOverflow |= 4;
								if(io_registers[REG_TM2CNT] & 0x40) {
									io_registers[REG_IF] |= 0x20;
									UPDATE_REG(0x202, io_registers[REG_IF]);
								}
							}
							UPDATE_REG(0x108, io_registers[REG_TM2D]);
						}
					} else {
						timer2Ticks -= clockTicks;
						if(timer2Ticks <= 0) {
							timer2Ticks += (0x10000 - timer2Reload) << timer2ClockReload;
							timerOverflow |= 4;
							if(io_registers[REG_TM2CNT] & 0x40) {
								io_registers[REG_IF] |= 0x20;
								UPDATE_REG(0x202, io_registers[REG_IF]);
							}
						}
						io_registers[REG_TM2D] = 0xFFFF - (timer2Ticks >> timer2ClockReload);
						UPDATE_REG(0x108, io_registers[REG_TM2D]);
					}
				}

				if(timer3On) {
					if(io_registers[REG_TM3CNT] & 4) {
						if(timerOverflow & 4) {
							io_registers[REG_TM3D]++;
							if(io_registers[REG_TM3D] == 0) {
								io_registers[REG_TM3D] += timer3Reload;
								if(io_registers[REG_TM3CNT] & 0x40) {
									io_registers[REG_IF] |= 0x40;
									UPDATE_REG(0x202, io_registers[REG_IF]);
								}
							}
							UPDATE_REG(0x10C, io_registers[REG_TM3D]);
						}
					} else {
						timer3Ticks -= clockTicks;
						if(timer3Ticks <= 0) {
							timer3Ticks += (0x10000 - timer3Reload) << timer3ClockReload;
							if(io_registers[REG_TM3CNT] & 0x40) {
								io_registers[REG_IF] |= 0x40;
								UPDATE_REG(0x202, io_registers[REG_IF]);
							}
						}
						io_registers[REG_TM3D] = 0xFFFF - (timer3Ticks >> timer3ClockReload);
						UPDATE_REG(0x10C, io_registers[REG_TM3D]);
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

#ifdef USE_SWITICKS
					// Stops the SWI Ticks emulation if an IRQ is executed
					//(to avoid problems with nested IRQ/SWI)
					if (SWITicks)
						SWITicks = 0;
#endif
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
				// Apply Timer
				if (timerOnOffDelay & 1)
				{
					timer0ClockReload = TIMER_TICKS[timer0Value & 3];
					if(!timer0On && (timer0Value & 0x80)) {
						// reload the counter
						io_registers[REG_TM0D] = timer0Reload;
						timer0Ticks = (0x10000 - io_registers[REG_TM0D]) << timer0ClockReload;
						UPDATE_REG(0x100, io_registers[REG_TM0D]);
					}
					timer0On = timer0Value & 0x80 ? true : false;
					io_registers[REG_TM0CNT] = timer0Value & 0xC7;
					UPDATE_REG(0x102, io_registers[REG_TM0CNT]);
				}
				if (timerOnOffDelay & 2)
				{
					timer1ClockReload = TIMER_TICKS[timer1Value & 3];
					if(!timer1On && (timer1Value & 0x80)) {
						// reload the counter
						io_registers[REG_TM1D] = timer1Reload;
						timer1Ticks = (0x10000 - io_registers[REG_TM1D]) << timer1ClockReload;
						UPDATE_REG(0x104, io_registers[REG_TM1D]);
					}
					timer1On = timer1Value & 0x80 ? true : false;
					io_registers[REG_TM1CNT] = timer1Value & 0xC7;
					UPDATE_REG(0x106, io_registers[REG_TM1CNT]);
				}
				if (timerOnOffDelay & 4)
				{
					timer2ClockReload = TIMER_TICKS[timer2Value & 3];
					if(!timer2On && (timer2Value & 0x80)) {
						// reload the counter
						io_registers[REG_TM2D] = timer2Reload;
						timer2Ticks = (0x10000 - io_registers[REG_TM2D]) << timer2ClockReload;
						UPDATE_REG(0x108, io_registers[REG_TM2D]);
					}
					timer2On = timer2Value & 0x80 ? true : false;
					io_registers[REG_TM2CNT] = timer2Value & 0xC7;
					UPDATE_REG(0x10A, io_registers[REG_TM2CNT]);
				}
				if (timerOnOffDelay & 8)
				{
					timer3ClockReload = TIMER_TICKS[timer3Value & 3];
					if(!timer3On && (timer3Value & 0x80)) {
						// reload the counter
						io_registers[REG_TM3D] = timer3Reload;
						timer3Ticks = (0x10000 - io_registers[REG_TM3D]) << timer3ClockReload;
						UPDATE_REG(0x10C, io_registers[REG_TM3D]);
					}
					timer3On = timer3Value & 0x80 ? true : false;
					io_registers[REG_TM3CNT] = timer3Value & 0xC7;
					UPDATE_REG(0x10E, io_registers[REG_TM3CNT]);
				}
				cpuNextEvent = CPUUpdateTicks();
				timerOnOffDelay = 0;
				// End of Apply Timer
			}

			if(cpuNextEvent > ticks)
				cpuNextEvent = ticks;

			if(ticks <= 0)
				break;

		}
	}while(1);
}
