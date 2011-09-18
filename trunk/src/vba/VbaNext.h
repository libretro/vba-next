//Iterate macros
#define REPEAT256(x) { REPEAT128(x) REPEAT128(x) }
#define REPEAT240(x) { REPEAT120(x) REPEAT120(x) }
#define REPEAT160(x) { REPEAT120(x) REPEAT40(x) }
#define REPEAT128(x) { REPEAT64(x) REPEAT64(x) }
#define REPEAT120(x) { REPEAT60(x) REPEAT60(x) }
#define REPEAT64(x) { REPEAT32(x) REPEAT32(x) }
#define REPEAT60(x) { REPEAT30(x) REPEAT30(x) }
#define REPEAT40(x) { REPEAT32(x) REPEAT8(x) }
#define REPEAT32(x) { REPEAT16(x) REPEAT16(x) }
#define REPEAT30(x) { REPEAT15(x) REPEAT15(x) }
#define REPEAT16(x) { REPEAT8(x) REPEAT8(x) }
#define REPEAT15(x) { REPEAT7(x) REPEAT7(x) }
#define REPEAT10(x) { REPEAT8(x) REPEAT2(x) }
#define REPEAT8(x) { REPEAT4(x) REPEAT4(x) }
#define REPEAT7(x) { REPEAT4(x) REPEAT2(x) REPEAT1(x) }
#define REPEAT4(x) { REPEAT2(x) REPEAT2(x) }
#define REPEAT2(x) { REPEAT1(x) REPEAT1(x) }
#define REPEAT1(x) { x; }

#define SYSTEMCOLORMAP16_LINE() { *dest++ = systemColorMap16[line[lineMix][x++]&0xFFFF];}

#define SYSTEMCOLORMAP24_LINE() { *((u32 *)dest) = systemColorMap32[line[lineMix][x++] & 0xFFFF]; dest += 3; }

#define SYSTEMCOLORMAP32_LINE() { *dest++ = systemColorMap32[line[lineMix][x++] & 0xFFFF]; }

#define SYSTEMCOLORMAP16_LINE_GB() { *dest++ = systemColorMap16[gbLineMix[x++]]; }

#define SYSTEMCOLORMAP24_LINE_GB() { *((u32 *)dest) = systemColorMap32[gbLineMix[x++]]; dest+= 3; }

#define SYSTEMCOLORMAP32_LINE_GB() { *dest++ = systemColorMap32[gbLineMix[x++]]; }

#define SYSTEMCOLORMAP24_LINE_SGB(p, v) { *((u32*) p) = systemColorMap32[v]; }

#define SYSTEMCOLORMAP32_LINE_SGB(p, v) { *p = systemColorMap32[v]; }

#ifdef __CELLOS_LV2__
#define systemDrawScreen() \
	Graphics->Draw(pix); \
	if(Graphics->frame_count < special_action_msg_expired) \
	{ \
		cellDbgFontPrintf (0.09f, 0.90f, 1.51f, BLUE,	special_action_msg); \
		cellDbgFontPrintf (0.09f, 0.90f, 1.50f, WHITE,	special_action_msg); \
		cellDbgFontDraw(); \
	} \
	else \
		special_action_msg_expired = 0; \
	psglSwap();
#endif
