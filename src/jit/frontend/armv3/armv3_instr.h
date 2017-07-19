static inline void armv3_translate_shift_lsl( struct armv3_guest *guest,
                                              struct jit_block *block,
                                              struct ir *ir,
                                              I32 in, I32 n,
                                              I32 *out, I32 *carry) {
  /*
   * LSL by 32 has result zero carry out equal to bit 0 of input
   * LSL by more than 32 has result zero, carry out zero
   */
  I64 tmp = SHL_I64(ZEXT_I32_I64(in), n);
  *out = TRUNC_I64_I32(tmp);
  *carry = TRUNC_I64_I32(LSHR_IMM_I64(AND_IMM_I64(tmp, UINT64_C(0x100000000)), 32));
  //uint64_t tmp = (uint64_t)in << n;
  //*out = (uint32_t)tmp;
  //*carry = (uint32_t)((tmp & 0x100000000) >> 32);
}

static inline void armv3_translate_shift_lsr( struct armv3_guest *guest,
                                              struct jit_block *block,
                                              struct ir *ir,
                                              I32 in, I32 n,
                                              I32 *out, I32 *carry) {
  /*
   * LSR by 32 has result zero, carry out equal to bit 31 of Rm
   * LSR by more than 32 has result zero, carry out zero
   */
  I64 tmp1 = ZEXT_I32_I64(in);
  *out = TRUNC_I64_I32(LSHR_I64(tmp1, n));
  I32 n2 = SUB_IMM_I32(n, 1);
  I64 tmp2 = LSHR_I64(tmp1, n2);
  *carry = TRUNC_I64_I32(AND_IMM_I64(tmp2, 0x1));
  //uint64_t tmp = (uint64_t)in;
  //*out = (uint32_t)(tmp >> n);
  //*carry = (uint32_t)((tmp >> (n - 1)) & 0x1);
}

static inline void armv3_translate_shift_asr( struct armv3_guest *guest,
                                              struct jit_block *block,
                                              struct ir *ir,
                                              I32 in, I32 n,
                                              I32 *out, I32 *carry) {
  /*
   * ASR by 32 or more has result filled with and carry out equal to bit 31 of
   * input
   */
  I64 tmp1 = SEXT_I32_I64(in);
  *out = TRUNC_I64_I32(ASHR_I64(tmp1, n));
  I32 n2 = SUB_IMM_I32(n, 1);
  I64 tmp2 = ASHR_I64(tmp1, n2);
  *carry = TRUNC_I64_I32(AND_IMM_I64(tmp2, 0x1));
  //int64_t tmp = (int64_t)(int32_t)in;
  //*out = (uint32_t)(tmp >> n);
  //*carry = (uint32_t)((tmp >> (n - 1)) & 0x1);
}

static inline void armv3_translate_shift_ror( struct armv3_guest *guest,
                                              struct jit_block *block,
                                              struct ir *ir,
                                              I32 in, I32 n,
                                              I32 *out, I32 *carry) {
  /*
   * ROR by 32 has result equal to input, carry out equal to bit 31 of input
   * ROR by n where n is greater than 32 will give the same result and carry
   * out as ROR by n-32; therefore repeatedly subtract 32 from n until the
   * amount is in the range 1 to 32 and see above
   */
  I64 tmp1 = ZEXT_I32_I64(in);
  n = AND_IMM_I32(n, 31);
  I64 tmp2 = SHL_I64(tmp1, ir_sub(ir, ir_alloc_i32(ir, 32), n));
  I64 tmp3 = LSHR_I64(tmp1, n);
  *out = TRUNC_I64_I32(OR_I64(tmp2, tmp3));
  *carry = TRUNC_I64_I32(AND_IMM_I64(LSHR_IMM_I64(*out, 31), 0x1));
  //uint64_t tmp = (uint64_t)in;
  //n &= 31;
  //*out = (uint32_t)((tmp << (32 - n)) | (tmp >> n));
  //*carry = (*out >> 31) & 0x1;
}

static void armv3_translate_shift(  struct armv3_guest *guest,
                                    struct jit_block *block,
                                    struct ir *ir,
                                    enum armv3_shift_source src,
                                    enum armv3_shift_type type, I32 in,
                                    uint32_t n, I32 *out, I32 *carry) {
  *out = in;
  // TODO: HANDLE CARRY
  *carry = ir_alloc_i32(ir, 0);
  //*carry = C_SET(ctx->r[CPSR]);

  I32 shifts;
  if (src == SHIFT_REG) {
    shifts = LOAD_GPR_I32(n);
  }
  else {
    shifts = ir_alloc_i32(ir, n);
  }

  // TODO make sure we don't generate code if shifts==0
  /*if (shifts)*/ {
    switch (type) {
      case SHIFT_LSL:
        armv3_translate_shift_lsl(guest, block, ir, in, shifts, out, carry);
        break;
      case SHIFT_LSR:
        armv3_translate_shift_lsr(guest, block, ir, in, shifts, out, carry);
        break;
      case SHIFT_ASR:
        armv3_translate_shift_asr(guest, block, ir, in, shifts, out, carry);
        break;
      case SHIFT_ROR:
        armv3_translate_shift_ror(guest, block, ir, in, shifts, out, carry);
        break;
      default:
        LOG_FATAL("Unsupported shift type");
        break;
    }
  }
}
static inline void armv3_translate_parse_shift( struct armv3_guest *guest,
                                                struct jit_block *block,
                                                struct ir *ir,
                                                uint32_t addr, uint32_t reg,
                                                uint32_t shift, I32 *value,
                                                I32 *carry) {
  enum armv3_shift_source src;
  enum armv3_shift_type type;
  uint32_t n;
  armv3_disasm_shift(shift, &src, &type, &n);

  I32 data;
  if (reg == 15) {
    /*
     * if the shift amount is specified in the instruction, PC will be 8 bytes
     * ahead. if a register is used to specify the shift amount the PC will be
     * 12 bytes ahead
     */
    if (src == SHIFT_IMM) {
      data = LOAD_IMM_I32(addr + 8);
    } else {
      data = LOAD_IMM_I32(addr + 12);
    }
  } else {
    data = LOAD_GPR_I32(reg);
  }
  armv3_translate_shift(guest, block, ir, src, type, data, n, value, carry);
}

INSTR(INVALID) {
  /* TODO */
  // INVALID_INSTR();
}

//ARMV3_INSTR(B,       "b{cond} {expr}",                                 xxxx1010xxxxxxxxxxxxxxxxxxxxxxxx, 1, FLAG_SET_PC)
/* B{cond} {expr} */
INSTR(B) {
  /* TODO */
}

//ARMV3_INSTR(BL,      "bl{cond} {expr}",                                xxxx1011xxxxxxxxxxxxxxxxxxxxxxxx, 1, FLAG_SET_PC)
/* BL{cond} {expr} */
INSTR(BL) {
  /* TODO */
}

//ARMV3_INSTR(AND,     "and{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0000xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* AND{cond}{s} {rd}, {rn}, {expr} */
INSTR(AND) {
  /* TODO */
}

//ARMV3_INSTR(EOR,     "eor{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0001xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* EOR{cond}{s} {rd}, {rn}, {expr} */
INSTR(EOR) {
  /* TODO */
}

//ARMV3_INSTR(SUB,     "sub{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0010xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* SUB{cond}{s} {rd}, {rn}, {expr} */
INSTR(SUB) {
  /* TODO */
}

//ARMV3_INSTR(RSB,     "rsb{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0011xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* RSB{cond}{s} {rd}, {rn}, {expr} */
INSTR(RSB) {
  /* TODO */
}

//ARMV3_INSTR(ADD,     "add{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0100xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* ADD{cond}{s} {rd}, {rn}, {expr} */
INSTR(ADD) {
  /* TODO */
}

//ARMV3_INSTR(ADC,     "adc{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0101xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* ADC{cond}{s} {rd}, {rn}, {expr} */
INSTR(ADC) {
  /* TODO */
}

//ARMV3_INSTR(SBC,     "sbc{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0110xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* SBC{cond}{s} {rd}, {rn}, {expr} */
INSTR(SBC) {
  /* TODO */
}

//ARMV3_INSTR(RSC,     "rsc{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0111xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* RSC{cond}{s} {rd}, {rn}, {expr} */
INSTR(RSC) {
  /* TODO */
}

//ARMV3_INSTR(TST,     "tst{cond} {rn}, {expr}",                         xxxx00x10001xxxx0000xxxxxxxxxxxx, 1, FLAG_DATA)
/* TST{cond} {rn}, {expr} */
INSTR(TST) {
  /* TODO */
}

//ARMV3_INSTR(TEQ,     "teq{cond} {rn}, {expr}",                         xxxx00x10011xxxx0000xxxxxxxxxxxx, 1, FLAG_DATA)
/* TEQ{cond} {rn}, {expr} */
INSTR(TEQ) {
  /* TODO */
}

//ARMV3_INSTR(CMP,     "cmp{cond} {rn}, {expr}",                         xxxx00x10101xxxx0000xxxxxxxxxxxx, 1, FLAG_DATA)
/* CMP{cond} {rn}, {expr} */
INSTR(CMP) {
  /* TODO */
}

//ARMV3_INSTR(CMN,     "cmn{cond} {rn}, {expr}",                         xxxx00x10111xxxx0000xxxxxxxxxxxx, 1, FLAG_DATA)
/* CMN{cond} {rn}, {expr} */
INSTR(CMN) {
  /* TODO */
}

//ARMV3_INSTR(ORR,     "orr{cond}{s} {rd}, {rn}, {expr}",                xxxx00x1100xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* ORR{cond}{s} {rd}, {rn}, {expr} */
INSTR(ORR) {
  /* TODO */
}

//ARMV3_INSTR(MOV,     "mov{cond}{s} {rd}, {expr}",                      xxxx00x1101x0000xxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* MOV{cond}{s} {rd}, {expr} */
INSTR(MOV) {
  /* TODO */
}

//ARMV3_INSTR(BIC,     "bic{cond}{s} {rd}, {rn}, {expr}",                xxxx00x1110xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* BIC{cond}{s} {rd}, {rn}, {expr} */
INSTR(BIC) {
 /* TODO */
}

//ARMV3_INSTR(MVN,     "mvn{cond}{s} {rd}, {expr}",                      xxxx00x1111x0000xxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* MVN{cond}{s} {rd}, {expr} */
INSTR(MVN) {
  /* TODO */
}

//ARMV3_INSTR(MRS,     "mrs{cond} {rd}, {psr}",                          xxxx00010x001111xxxx000000000000, 1, FLAG_PSR)
/* MRS{cond} {rd}, {psr} */
INSTR(MRS) {
  /* TODO */
}

//ARMV3_INSTR(MSR,     "msr{cond} {psr}, {expr}",                        xxxx00x10x10xxxx111100000000xxxx, 1, FLAG_PSR)
/* MSR{cond} {psr}, {expr} */
INSTR(MSR) {
  /* TODO */
}

//ARMV3_INSTR(MUL,     "mul{cond}{s} {rd}, {rm}, {rs}",                  xxxx0000000xxxxxxxxxxxxx1001xxxx, 1, FLAG_MUL)
/* MUL{cond}{s} {rd}, {rm}, {rs} */
INSTR(MUL) {
  /* TODO */
}

//ARMV3_INSTR(MLA,     "mla{cond}{s} {rd}, {rm}, {rs}, {rn}",            xxxx0000001xxxxxxxxxxxxx1001xxxx, 1, FLAG_MUL)
/* MLA{cond}{s} {rd}, {rm}, {rs}, {rn} */
INSTR(MLA) {
  /* TODO */
}


static inline void armv3_translate_memop(struct armv3_guest *guest, struct jit_block *block,
                            struct ir *ir, uint32_t addr, union armv3_instr i, 
                            int flags) {
  I32 base;
  I32 final;
  I32 ea;
  I32 data;
  I32 offset = 0;
  I32 carry = 0;

  /* parse offset */
  if (i.xfr.i) {
    armv3_translate_parse_shift(guest, block, ir, addr, i.xfr_reg.rm, i.xfr_reg.shift, &offset, &carry);
  } else  {
    offset = ir_alloc_i32(ir, i.xfr_imm.imm);
  }

  base = LOAD_RN_I32(i.xfr.rn);
  if (i.xfr.u)
    final = ADD_I32(base, offset);
  else
    final = SUB_I32(base, offset);
  ea = i.xfr.p ? final : base;

  /*
   * writeback is applied in pipeline before memory is read.
   * note, post-increment mode always writes back
   */
  if (i.xfr.w || !i.xfr.p) {
    STORE_GPR_I32(i.xfr.rn, final);
  }

  if (i.xfr.l) {
    /* load data */
    if (i.xfr.b) {
      data = LOAD_I8(ea);
    } else {
      data = LOAD_I32(ea);
    }

    STORE_GPR_IMM_I32(15, addr + 4);
    STORE_GPR_I32(i.xfr.rd, data);
  } 
  else {
    /* store data */
    if (i.xfr.b) {
      data = LOAD_RD_I8(i.xfr.rd);
      STORE_I8(ea, data);
    } else {
      data = LOAD_RD_I32(i.xfr.rd);
      STORE_I32(ea, data);
    }

    STORE_GPR_IMM_I32(15, addr + 4);
  }
}

//ARMV3_INSTR(LDR,     "ldr{cond}{b}{t} {rd}, {addr}",                   xxxx01xxxxx1xxxxxxxxxxxxxxxxxxxx, 1, FLAG_XFR)
/* LDR{cond}{b}{t} {rd}, {addr} */
INSTR(LDR) {
  armv3_translate_memop(guest, block, ir, addr, i, flags);
}

//ARMV3_INSTR(STR,     "str{cond}{b}{t} {rd}, {addr}",                   xxxx01xxxxx0xxxxxxxxxxxxxxxxxxxx, 1, FLAG_XFR)
/* STR{cond}{b}{t} {rd}, {addr} */
INSTR(STR) {
  armv3_translate_memop(guest, block, ir, addr, i, flags);
}

//ARMV3_INSTR(LDM,     "ldm{cond}{stack} {rn}{!}, {rlist}{^}",           xxxx100xxxx1xxxxxxxxxxxxxxxxxxxx, 1, FLAG_BLK)
/* LDM{cond}{stack} {rn}{!}, {rlist}{^} */
INSTR(LDM) {
  /* TODO */
}

//ARMV3_INSTR(STM,     "stm{cond}{stack} {rn}{!}, {rlist}{^}",           xxxx100xxxx0xxxxxxxxxxxxxxxxxxxx, 1, FLAG_BLK)
/* STM{cond}{stack} {rn}{!}, {rlist}{^} */
INSTR(STM) {
  /* TODO */
}

//ARMV3_INSTR(SWP,     "swp{cond}{b} {rd}, {rm}, [{rn}]",                xxxx00010x00xxxxxxxx00001001xxxx, 1, FLAG_SWP)
/* SWP{cond}{b} {rd}, {rm}, [{rn}] */
INSTR(SWP) {
  /* TODO */
}

//ARMV3_INSTR(SWI,     "swi{cond} {imm}",                                xxxx1111xxxxxxxxxxxxxxxxxxxxxxxx, 1, FLAG_SWI)
/* SWI{cond} {imm} */
INSTR(SWI) {
  /* TODO */
}
