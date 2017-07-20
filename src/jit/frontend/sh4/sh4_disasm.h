#ifndef SH4_DISASM_H
#define SH4_DISASM_H

#include <stddef.h>
#include "jit/frontend/jit_frontend.h"

enum {
  SH4_FLAG_INVALID = 0x1,
  SH4_FLAG_LOAD = 0x2,
  SH4_FLAG_STORE = 0x4,
  SH4_FLAG_COND = 0x8,
  SH4_FLAG_CMP = 0x10,
  SH4_FLAG_DELAYED = 0x20,
  SH4_FLAG_LOAD_PC = 0x40,
  SH4_FLAG_STORE_PC = 0x80,
  SH4_FLAG_STORE_FPSCR = 0x100,
  SH4_FLAG_STORE_SR = 0x200,
};

enum sh4_op {
#define SH4_INSTR(name, desc, instr_code, cycles, flags) SH4_OP_##name,
#include "jit/frontend/sh4/sh4_instr.inc"
#undef SH4_INSTR
  NUM_SH4_OPS,
};

union sh4_instr {
  uint16_t raw;

  struct {
    uint32_t disp : 4;
    uint32_t rm : 4;
    uint32_t rn : 4;
    uint32_t : 4;
  } def;

  struct {
    uint32_t imm : 8;
    uint32_t rn : 4;
    uint32_t : 4;
  } imm;

  struct {
    uint32_t disp : 8;
    uint32_t : 8;
  } disp_8;

  struct {
    uint32_t disp : 12;
    uint32_t : 4;
  } disp_12;
};

extern int sh4_optable[UINT16_MAX + 1];
extern struct jit_opdef sh4_opdefs[NUM_SH4_OPS];

static inline int sh4_get_op(uint16_t instr) {
  return sh4_optable[instr];
}

static struct jit_opdef *sh4_get_opdef(uint16_t instr) {
  return &sh4_opdefs[sh4_get_op(instr)];
}

void sh4_format(uint32_t addr, union sh4_instr i, char *buffer,
                size_t buffer_size);

#endif
