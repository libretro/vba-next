/* Loads a cartridge image by path, the way builds without
 * LOAD_FROM_MEMORY (GameCube, Wii) receive content, and checks that the
 * program in it runs.  The image fills the screen in mode 3 with pure
 * red.  It is loaded twice, so the second load goes through
 * CPUSetupBuffers releasing the first load's buffers. */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "libretro.h"

#define IMAGE_PATH "load_path_test.gba"
#define IMAGE_SIZE 0x200

/* ARM, at 0x08000000: branch over the header to 0xC0; set DISPCNT to
 * mode 3 with BG2; fill the 240x160 frame with BGR555 0x001F, forever. */
static const unsigned long image_code[] = {
   0xe3a00301UL, /* mov  r0, #0x04000000 */
   0xe3a01b01UL, /* mov  r1, #0x400      */
   0xe3811003UL, /* orr  r1, r1, #3      */
   0xe1c010b0UL, /* strh r1, [r0]        */
   0xe3a0401fUL, /* mov  r4, #0x1f       */
   0xe3a05406UL, /* mov  r5, #0x06000000 */
   0xe3a06c96UL, /* mov  r6, #38400      */
   0xe0c540b2UL, /* strh r4, [r5], #2    */
   0xe2566001UL, /* subs r6, r6, #1      */
   0x1afffffcUL, /* bne  -4 words        */
   0xeafffff8UL  /* b    to the mov r4   */
};

static enum retro_pixel_format pixel_format = RETRO_PIXEL_FORMAT_0RGB1555;
static unsigned centre_pixel;
static unsigned frames_seen;

static void put_word(unsigned char *p, unsigned long w)
{
   p[0] = (unsigned char)(w & 0xff);
   p[1] = (unsigned char)((w >> 8) & 0xff);
   p[2] = (unsigned char)((w >> 16) & 0xff);
   p[3] = (unsigned char)((w >> 24) & 0xff);
}

static int write_image(void)
{
   unsigned char image[IMAGE_SIZE];
   size_t i;
   FILE *fp;

   memset(image, 0, sizeof(image));
   put_word(image, 0xea00002eUL); /* b 0x080000c0 */
   memcpy(image + 0xa0, "LOADPATHTEST", 12);
   memcpy(image + 0xac, "ALPT", 4);
   image[0xb2] = 0x96;
   for (i = 0; i < sizeof(image_code) / sizeof(image_code[0]); i++)
      put_word(image + 0xc0 + i * 4, image_code[i]);

   fp = fopen(IMAGE_PATH, "wb");
   if (!fp)
      return 0;
   if (fwrite(image, 1, sizeof(image), fp) != sizeof(image))
   {
      fclose(fp);
      return 0;
   }
   return fclose(fp) == 0;
}

static void video_cb(const void *data, unsigned width, unsigned height,
      size_t pitch)
{
   const unsigned short *row;
   if (!data)
      return;
   row          = (const unsigned short*)((const unsigned char*)data
         + (height / 2) * pitch);
   centre_pixel = row[width / 2];
   frames_seen++;
}

static bool environ_cb(unsigned cmd, void *data)
{
   if (cmd == RETRO_ENVIRONMENT_SET_PIXEL_FORMAT)
   {
      pixel_format = *(const enum retro_pixel_format*)data;
      return pixel_format == RETRO_PIXEL_FORMAT_RGB565
          || pixel_format == RETRO_PIXEL_FORMAT_0RGB1555;
   }
   return false;
}

static void audio_cb(int16_t left, int16_t right)
{
   (void)left;
   (void)right;
}

static size_t audio_batch_cb(const int16_t *data, size_t frames)
{
   (void)data;
   return frames;
}

static void input_poll_cb(void) { }

static int16_t input_state_cb(unsigned port, unsigned device,
      unsigned index, unsigned id)
{
   (void)port;
   (void)device;
   (void)index;
   (void)id;
   return 0;
}

static int centre_is_red(void)
{
   unsigned r, g, b;
   if (pixel_format == RETRO_PIXEL_FORMAT_RGB565)
   {
      r = (centre_pixel >> 11) & 0x1f;
      g = (centre_pixel >> 6) & 0x1f;
      b = centre_pixel & 0x1f;
   }
   else
   {
      r = (centre_pixel >> 10) & 0x1f;
      g = (centre_pixel >> 5) & 0x1f;
      b = centre_pixel & 0x1f;
   }
   return r == 0x1f && g == 0 && b == 0;
}

static int load_and_run(int pass)
{
   struct retro_game_info info;
   int i;

   memset(&info, 0, sizeof(info));
   info.path    = IMAGE_PATH;
   frames_seen  = 0;
   centre_pixel = 0;

   if (!retro_load_game(&info))
   {
      printf("FAIL load %d: retro_load_game returned false\n", pass);
      return 0;
   }
   for (i = 0; i < 30; i++)
      retro_run();
   retro_unload_game();

   if (!frames_seen || !centre_is_red())
   {
      printf("FAIL load %d: %u frames, centre pixel 0x%04x, not red\n",
            pass, frames_seen, centre_pixel);
      return 0;
   }
   printf("ok   load %d: %u frames, centre pixel red\n", pass, frames_seen);
   return 1;
}

int main(void)
{
   struct retro_system_info sys;
   int ok = 1;

   if (!write_image())
   {
      printf("FAIL cannot write %s\n", IMAGE_PATH);
      return 1;
   }

   retro_set_environment(environ_cb);
   retro_set_video_refresh(video_cb);
   retro_set_audio_sample(audio_cb);
   retro_set_audio_sample_batch(audio_batch_cb);
   retro_set_input_poll(input_poll_cb);
   retro_set_input_state(input_state_cb);
   retro_init();

   memset(&sys, 0, sizeof(sys));
   retro_get_system_info(&sys);
   if (!sys.need_fullpath)
   {
      printf("FAIL core built with LOAD_FROM_MEMORY; nothing to test\n");
      ok = 0;
   }

   if (ok && !load_and_run(1))
      ok = 0;
   if (ok && !load_and_run(2))
      ok = 0;

   retro_deinit();
   remove(IMAGE_PATH);

   printf("%s\n", ok ? "PASSED" : "FAILED");
   return ok ? 0 : 1;
}
