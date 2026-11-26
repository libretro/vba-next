# Path-loading regression test: the core built as the GameCube and Wii
# builds use it (no LOAD_FROM_MEMORY), linked straight into the test.
#   make check
#   make SANITIZER=address,undefined check
CORE_DIR                 := ../..
LOAD_FROM_MEMORY         := 0
USE_THREADED_RENDERER    := 0
FRONTEND_SUPPORTS_RGB565 := 1
USE_CHEATS               := 1
STATIC_LINKING           := 0

include $(CORE_DIR)/build/Makefile.common

CC        ?= cc
CFLAGS    ?= -O2 -g
SANITIZER ?=
ifneq ($(SANITIZER),)
CFLAGS    += -fsanitize=$(SANITIZER) -fno-omit-frame-pointer
LDFLAGS   += -fsanitize=$(SANITIZER)
endif

TARGET := load_path_test

all: $(TARGET)

$(TARGET): load_path_test.c $(SOURCES_C)
	$(CC) $(CFLAGS) $(INCFLAGS) $(COREDEFINES) -DHAVE_STDINT_H \
		-DHAVE_INTTYPES_H -o $@ load_path_test.c $(SOURCES_C) $(LDFLAGS) -lm

check: $(TARGET)
	./$(TARGET)

clean:
	rm -f $(TARGET) $(TARGET).exe load_path_test.gba

.PHONY: all check clean
