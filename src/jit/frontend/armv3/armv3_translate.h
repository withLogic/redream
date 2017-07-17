#ifndef ARMV3_TRANSLATE_H
#define ARMV3_TRANSLATE_H

#include "jit/frontend/armv3/armv3_disasm.h"

struct ir;
struct jit_block;
struct armv3_guest;

typedef void (*armv3_translate_cb)(struct armv3_guest *, struct jit_block *,
                                 struct ir *, uint32_t, union armv3_instr, int);

extern armv3_translate_cb armv3_translators[NUM_ARMV3_OPS];

static inline armv3_translate_cb armv3_get_translator(uint16_t instr) {
  return armv3_translators[armv3_get_op(instr)];
}

#endif
