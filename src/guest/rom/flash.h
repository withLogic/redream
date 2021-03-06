#ifndef FLASHROM_H
#define FLASHROM_H

#include "guest/memory.h"

struct dreamcast;
struct flash;

AM_DECLARE(flash_rom_map);

struct flash *flash_create(struct dreamcast *dc);
void flash_destroy(struct flash *flash);

void flash_read(struct flash *flash, int offset, void *data, int n);
void flash_write(struct flash *flash, int offset, const void *data, int n);
void flash_program(struct flash *flash, int offset, const void *data, int n);
void flash_erase(struct flash *flash, int offset, int n);

#endif
