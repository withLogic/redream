static inline void armv3_translate_shift_lsl( struct ir *ir,
                                              I32 in, I32 nshifts,
                                              I32 *out, I32 *carry) {
  /*
   * LSL by 32 has result zero carry out equal to bit 0 of input
   * LSL by more than 32 has result zero, carry out zero
   */
  I64 tmp = SHL_I64(ZEXT_I32_I64(in), nshifts);
  *out = TRUNC_I64_I32(tmp);
  *carry = TRUNC_I64_I32(LSHR_IMM_I64(AND_IMM_I64(tmp, UINT64_C(0x100000000)), 32));
  //uint64_t tmp = (uint64_t)in << n;
  //*out = (uint32_t)tmp;
  //*carry = (uint32_t)((tmp & 0x100000000) >> 32);
}

static inline void armv3_translate_shift_lsr( struct ir *ir,
                                              I32 in, I32 nshifts,
                                              I32 *out, I32 *carry) {
  /*
   * LSR by 32 has result zero, carry out equal to bit 31 of Rm
   * LSR by more than 32 has result zero, carry out zero
   */
  I64 tmp = ZEXT_I32_I64(in);
  *out = TRUNC_I64_I32(LSHR_I64(tmp, nshifts));
  *carry = TRUNC_I64_I32(AND_IMM_I64(LSHR_I64(tmp, SUB_IMM_I32(nshifts, 1)), 0x1));
  //uint64_t tmp = (uint64_t)in;
  //*out = (uint32_t)(tmp >> n);
  //*carry = (uint32_t)((tmp >> (n - 1)) & 0x1);
}

static inline void armv3_translate_shift_asr( struct ir *ir,
                                              I32 in, I32 nshifts,
                                              I32 *out, I32 *carry) {
  /*
   * ASR by 32 or more has result filled with and carry out equal to bit 31 of
   * input
   */
  I64 tmp = SEXT_I32_I64(in);
  *out = TRUNC_I64_I32(ASHR_I64(tmp, nshifts));
  *carry = TRUNC_I64_I32(AND_IMM_I64(ASHR_I64(tmp, SUB_IMM_I32(nshifts, 1)), 0x1));
  //int64_t tmp = (int64_t)(int32_t)in;
  //*out = (uint32_t)(tmp >> n);
  //*carry = (uint32_t)((tmp >> (n - 1)) & 0x1);
}

static inline void armv3_translate_shift_ror( struct ir *ir,
                                              I32 in, I32 nshifts,
                                              I32 *out, I32 *carry) {
  /*
   * ROR by 32 has result equal to input, carry out equal to bit 31 of input
   * ROR by n where n is greater than 32 will give the same result and carry
   * out as ROR by n-32; therefore repeatedly subtract 32 from n until the
   * amount is in the range 1 to 32 and see above
   */
  I64 tmp = ZEXT_I32_I64(in);
  nshifts = AND_IMM_I32(nshifts, 31);
  *out = TRUNC_I64_I32(OR_I64(SHL_I64(tmp, SUB_I32(I32_IMM(32), nshifts)), LSHR_I64(tmp, nshifts)));
  *carry = AND_IMM_I32(LSHR_IMM_I32(*out, 31), 0x1);
  //uint64_t tmp = (uint64_t)in;
  //n &= 31;
  //*out = (uint32_t)((tmp << (32 - n)) | (tmp >> n));
  //*carry = (*out >> 31) & 0x1;
}

static void armv3_translate_shift(  struct jit_block *block,
                                    struct ir *ir,
                                    enum armv3_shift_source src,
                                    enum armv3_shift_type type, I32 in,
                                    uint32_t n, I32 *out, I32 *carry) {
  *out = in;
  // TODO: HANDLE CARRY
  *carry = I32_IMM(0);
  //*carry = C_SET(ctx->r[CPSR]);

  I32 shifts;
  if (src == SHIFT_REG) {
    shifts = LOAD_GPR_I32(n);
  }
  else {
    shifts = I32_IMM(n);
  }

  // TODO make sure we don't generate code if shifts==0
  /*if (shifts)*/ {
    switch (type) {
      case SHIFT_LSL:
        armv3_translate_shift_lsl(ir, in, shifts, out, carry);
        break;
      case SHIFT_LSR:
        armv3_translate_shift_lsr(ir, in, shifts, out, carry);
        break;
      case SHIFT_ASR:
        armv3_translate_shift_asr(ir, in, shifts, out, carry);
        break;
      case SHIFT_ROR:
        armv3_translate_shift_ror(ir, in, shifts, out, carry);
        break;
      default:
        LOG_FATAL("Unsupported shift type");
        break;
    }
  }
}
static inline void armv3_translate_parse_shift( struct jit_block *block,
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
  armv3_translate_shift(block, ir, src, type, data, n, value, carry);
}

static inline void armv3_translate_parse_op2( struct jit_block *block,
                                              struct ir* ir, uint32_t addr, 
                                              union armv3_instr i,
                                              I32 *value, I32 *carry) {
  if (i.data.i) {
    /* op2 is an immediate */
    uint32_t n = i.data_imm.rot << 1;

    I32 imm = I32_IMM(i.data_imm.imm);
    if (n) {
      armv3_translate_shift_ror(ir, imm, I32_IMM(n), value, carry);
    } else {
      *value = imm;
      *carry = I32_IMM(0);
      // TODO HANDLE CARRY
      //*carry = C_SET(ctx->r[CPSR]);
    }
  } else {
    /* op2 is as shifted register */
    armv3_translate_parse_shift(block, ir, addr, i.data_reg.rm,
                                i.data_reg.shift, value, carry);
  }
}
/*
 * data processing
 */

#define PARSE_OP2(value, carry) \
  armv3_translate_parse_op2(block, ir, addr, i, value, carry)

//#define CARRY() (C_SET(CTX->r[CPSR]))

static inline void armv3_translate_make_cpsr( struct jit_block *block,
                                              struct ir* ir,
                                              I32* cpsr, I32 n, I32 z,
                                              I32 c, I32 v)
{
  *cpsr = OR_I32(
          OR_I32(
          OR_I32(
          OR_I32(AND_IMM_I32(*cpsr, ~(N_MASK | Z_MASK | C_MASK | V_MASK)),
                              SHL_IMM_I32(n, N_BIT)),
                              SHL_IMM_I32(z, Z_BIT)),
                              SHL_IMM_I32(c, C_BIT)),
                              SHL_IMM_I32(v, V_BIT));
}

#define MAKE_CPSR(cpsr, n, z, c, v)                                   \
  armv3_translate_make_cpsr(block, ir, cpsr, n, z, c, v);

static inline void armv3_translate_update_flags_logical(
                                              struct jit_block *block,
                                              struct ir* ir,
                                              I32 res, I32 carry) {
  I32 zero = I32_IMM(0);
  I32 one = I32_IMM(1);
  I32 n = SELECT_I32(AND_IMM_I32(res, 0x80000000), one, zero);
  I32 z = SELECT_I32(res, zero, one);
  I32 c = carry;
  I32 v = zero;
  I32 cpsr = LOAD_CPSR();
  MAKE_CPSR(&cpsr, n, z, c ,v);
  STORE_CPSR(cpsr);
}

static inline void armv3_translate_update_flags_sub(  struct jit_block *block,
                                                      struct ir* ir,
                                                      I32 lhs, I32 rhs,
                                                      I32 res) {
  I32 zero = I32_IMM(0);
  I32 one = I32_IMM(1);
  I32 n = SELECT_I32(AND_IMM_I32(res, 0x80000000), one, zero);
  I32 z = SELECT_I32(res, zero, one);
  I32 c = LSHR_IMM_I32(NOT_I32(OR_I32(AND_I32(NOT_I32(lhs), rhs), AND_I32(OR_I32(NOT_I32(lhs), rhs), res))), 31);
  I32 v = LSHR_IMM_I32(AND_I32(XOR_I32(lhs, rhs), XOR_I32(res, lhs)), 31);
  I32 cpsr = LOAD_CPSR();
  MAKE_CPSR(&cpsr, n, z, c ,v);
  STORE_CPSR(cpsr);
}

static inline void armv3_translate_update_flags_add(  struct jit_block *block,
                                                      struct ir* ir,
                                                      I32 lhs, I32 rhs,
                                                      I32 res) {
  I32 zero = I32_IMM(0);
  I32 one = I32_IMM(1);
  I32 n = SELECT_I32(AND_IMM_I32(res, 0x80000000), one, zero);
  I32 z = SELECT_I32(res, zero, one);
  I32 c = LSHR_IMM_I32(OR_I32(AND_I32(lhs, rhs), AND_I32(OR_I32(lhs, rhs), NOT_I32(res))), 31);
  I32 v = LSHR_IMM_I32(AND_I32(XOR_I32(res, lhs), XOR_I32(res, rhs)), 31);
  I32 cpsr = LOAD_CPSR();
  MAKE_CPSR(&cpsr, n, z, c ,v);
  STORE_CPSR(cpsr);
}

#define UPDATE_FLAGS_LOGICAL()                                      \
  if (i.data.s) {                                                   \
    armv3_translate_update_flags_logical(block, ir, res, carry);    \
    if (i.data.rd == 15) {                                          \
      RESTORE_MODE();                                               \
    }                                                               \
  }

#define UPDATE_FLAGS_SUB()                                        \
  if (i.data.s) {                                                 \
    armv3_translate_update_flags_sub(block, ir, lhs, rhs, res);   \
    if (i.data.rd == 15) {                                        \
      RESTORE_MODE();                                             \
    }                                                             \
  }

#define UPDATE_FLAGS_ADD()                                        \
  if (i.data.s) {                                                 \
    armv3_translate_update_flags_add(block, ir, lhs, rhs, res);   \
    if (i.data.rd == 15) {                                        \
      RESTORE_MODE();                                             \
    }                                                             \
  }

INSTR(INVALID) {
  /* TODO */
  // INVALID_INSTR();
}

#define BRANCH_OFFSET() armv3_disasm_offset(i.branch.offset)

//ARMV3_INSTR(B,       "b{cond} {expr}",                                 xxxx1010xxxxxxxxxxxxxxxxxxxxxxxx, 1, FLAG_SET_PC)
/* B{cond} {expr} */
INSTR(B) {
  // TODO
  // CHECK_COND();

  STORE_GPR_IMM_I32(15,  addr + 8 + BRANCH_OFFSET());
  // ?? BRANCH_IMM_I32(addr + 8 + BRANCH_OFFSET());
}

//ARMV3_INSTR(BL,      "bl{cond} {expr}",                                xxxx1011xxxxxxxxxxxxxxxxxxxxxxxx, 1, FLAG_SET_PC)
/* BL{cond} {expr} */
INSTR(BL) {
  // TODO
  // CHECK_COND();

  STORE_GPR_IMM_I32(14, addr + 4);
  STORE_GPR_IMM_I32(15, addr + 8 + BRANCH_OFFSET());
  // ?? BRANCH_IMM_I32(addr + 8 + BRANCH_OFFSET());
}

//ARMV3_INSTR(AND,     "and{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0000xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* AND{cond}{s} {rd}, {rn}, {expr} */
INSTR(AND) {
  // TODO
  //CHECK_COND();

  I32 rhs;
  I32 carry;
  I32 lhs = LOAD_RN_I32(i.data.rn);
  PARSE_OP2(&rhs, &carry);
  I32 res = AND_I32(lhs, rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_LOGICAL();
}

//ARMV3_INSTR(EOR,     "eor{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0001xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* EOR{cond}{s} {rd}, {rn}, {expr} */
INSTR(EOR) {
  // TODO
  //CHECK_COND();

  I32 rhs;
  I32 carry;
  I32 lhs = LOAD_RN_I32(i.data.rn);
  PARSE_OP2(&rhs, &carry);
  I32 res = XOR_I32(lhs, rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_LOGICAL();
}

//ARMV3_INSTR(SUB,     "sub{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0010xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* SUB{cond}{s} {rd}, {rn}, {expr} */
INSTR(SUB) {
  // TODO
  //CHECK_COND();

  I32 rhs;
  I32 carry;
  I32 lhs = LOAD_RN_I32(i.data.rn);
  PARSE_OP2(&rhs, &carry);
  I32 res = SUB_I32(lhs, rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_SUB();
}

//ARMV3_INSTR(RSB,     "rsb{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0011xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* RSB{cond}{s} {rd}, {rn}, {expr} */
INSTR(RSB) {
  // TODO
  //CHECK_COND();

  I32 lhs;
  I32 carry;
  PARSE_OP2(&lhs, &carry);
  I32 rhs = LOAD_RN_I32(i.data.rn);
  I32 res = SUB_I32(lhs, rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_SUB();
}

//ARMV3_INSTR(ADD,     "add{cond}{s} {rd}, {rn}, {expr}",                xxxx00x0100xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* ADD{cond}{s} {rd}, {rn}, {expr} */
INSTR(ADD) {
  // TODO
  //CHECK_COND();

  I32 rhs;
  I32 carry;
  I32 lhs = LOAD_RN_I32(i.data.rn);
  PARSE_OP2(&rhs, &carry);
  I32 res = ADD_I32(lhs, rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_ADD();
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
  // TODO
  //CHECK_COND();

  I32 rhs;
  I32 carry;
  I32 lhs = LOAD_RN_I32(i.data.rn);
  PARSE_OP2(&rhs, &carry);
  I32 res = OR_I32(lhs, rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_LOGICAL();
}

//ARMV3_INSTR(MOV,     "mov{cond}{s} {rd}, {expr}",                      xxxx00x1101x0000xxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* MOV{cond}{s} {rd}, {expr} */
INSTR(MOV) {
  // TODO
  // CHECK_COND();

  I32 res;
  I32 carry;
  PARSE_OP2(&res, &carry);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_LOGICAL();
}

//ARMV3_INSTR(BIC,     "bic{cond}{s} {rd}, {rn}, {expr}",                xxxx00x1110xxxxxxxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* BIC{cond}{s} {rd}, {rn}, {expr} */
INSTR(BIC) {
  // TODO
  // CHECK_COND();

  I32 rhs;
  I32 carry;
  I32 lhs = LOAD_RN_I32(i.data.rn);
  PARSE_OP2(&rhs, &carry);
  I32 res = AND_I32(lhs, NOT_I32(rhs));

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_LOGICAL();
}

//ARMV3_INSTR(MVN,     "mvn{cond}{s} {rd}, {expr}",                      xxxx00x1111x0000xxxxxxxxxxxxxxxx, 1, FLAG_DATA)
/* MVN{cond}{s} {rd}, {expr} */
INSTR(MVN) {
  // TODO
  // CHECK_COND();

  I32 rhs;
  I32 carry;
  PARSE_OP2(&rhs, &carry);
  I32 res = NOT_I32(rhs);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.data.rd, res);

  UPDATE_FLAGS_LOGICAL();
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

/*
 * multiply and multiply-accumulate
 */
#define UPDATE_FLAGS_MUL()                              \
  if (i.mul.s) {                                        \
    armv3_translate_update_flags_mul(block, ir, res);   \
  }

static inline void armv3_translate_make_cpsr_nz( struct jit_block *block,
                                                struct ir* ir,
                                                I32* cpsr, I32 n, I32 z)
{
  *cpsr = OR_I32(
          OR_I32(AND_IMM_I32(*cpsr, ~(N_MASK | Z_MASK)),
                              SHL_IMM_I32(n, N_BIT)),
                              SHL_IMM_I32(z, Z_BIT));
}

#define MAKE_CPSR_NZ(cpsr, n, z)                                   \
  armv3_translate_make_cpsr_nz(block, ir, cpsr, n, z);

static void armv3_translate_update_flags_mul( struct jit_block *block,
                                              struct ir *ir, I32 res) {
  I32 zero = I32_IMM(0);
  I32 one = I32_IMM(1);
  I32 n = SELECT_I32(AND_IMM_I32(res, 0x80000000), one, zero);
  I32 z = SELECT_I32(res, zero, one);
  I32 cpsr = LOAD_CPSR();
  MAKE_CPSR_NZ(&cpsr, n, z);
  STORE_CPSR(cpsr);
}

//ARMV3_INSTR(MUL,     "mul{cond}{s} {rd}, {rm}, {rs}",                  xxxx0000000xxxxxxxxxxxxx1001xxxx, 1, FLAG_MUL)
/* MUL{cond}{s} {rd}, {rm}, {rs} */
INSTR(MUL) {
  // TODO
  // CHECK_COND();

  I32 a = LOAD_RN_I32(i.mul.rm);
  I32 b = LOAD_RN_I32(i.mul.rs);
  I32 res = UMUL_I32(a, b); // UMUL or SMUL ??

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.mul.rd, res);

  UPDATE_FLAGS_MUL();
}

//ARMV3_INSTR(MLA,     "mla{cond}{s} {rd}, {rm}, {rs}, {rn}",            xxxx0000001xxxxxxxxxxxxx1001xxxx, 1, FLAG_MUL)
/* MLA{cond}{s} {rd}, {rm}, {rs}, {rn} */
INSTR(MLA) {
  // TODO
  // CHECK_COND();

  I32 a = LOAD_RN_I32(i.mul.rm);
  I32 b = LOAD_RN_I32(i.mul.rs);
  I32 c = LOAD_RN_I32(i.mul.rn);
  I32 res = ADD_I32(UMUL_I32(a, b), c);

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.mul.rd, res);

  UPDATE_FLAGS_MUL();
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

  //TODO
  //CHECK_COND();

  /* parse offset */
  if (i.xfr.i) {
    armv3_translate_parse_shift(block, ir, addr, i.xfr_reg.rm, i.xfr_reg.shift, &offset, &carry);
  } else  {
    offset = I32_IMM(i.xfr_imm.imm);
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

#define USER_MODE_REG_OFFSET    0 /* TODO */
#define GET_USER_MODE_REG(r)    (r+USER_MODE_REG_OFFSET)

//ARMV3_INSTR(LDM,     "ldm{cond}{stack} {rn}{!}, {rlist}{^}",           xxxx100xxxx1xxxxxxxxxxxxxxxxxxxx, 1, FLAG_BLK)
/* LDM{cond}{stack} {rn}{!}, {rlist}{^} */
INSTR(LDM) {
  // TODO
  // CHECK_COND();

  I32 base = LOAD_RN_I32(i.blk.rn);
  uint32_t offset = popcnt32(i.blk.rlist) * 4;
  I32 final = i.blk.u ? ADD_IMM_I32(base, offset) : SUB_IMM_I32(base, offset);
  I32 ea = base;

  /* writeback is applied in pipeline before memory is read */
  if (i.blk.w) {
    STORE_GPR_I32(i.blk.rn, final);
  }

  STORE_GPR_IMM_I32(15, addr + 4);

  for (int bit = 0; bit < 16; bit++) {
    int reg = bit;

    if (!i.blk.u) {
      reg = 15 - bit;
    }

    if (i.blk.rlist & (1 << reg)) {
      /* pre-increment */
      if (i.blk.p) {
        ea = i.blk.u ? ADD_IMM_I32(ea, 4) : SUB_IMM_I32(ea, 4);
      }

      /* user bank transfer */
      if (i.blk.s && (i.blk.rlist & 0x8000) == 0) {
        reg = GET_USER_MODE_REG(reg);
      }

      STORE_GPR_I32(reg, LOAD_I32(ea));

      /* post-increment */
      if (!i.blk.p) {
        ea = i.blk.u ? ADD_IMM_I32(ea, 4) : SUB_IMM_I32(ea, 4);
      }
    }
  }

  if ((i.blk.rlist & 0x8000) && i.blk.s) {
    /* move SPSR into CPSR */
    RESTORE_MODE();
  }  
}

//ARMV3_INSTR(STM,     "stm{cond}{stack} {rn}{!}, {rlist}{^}",           xxxx100xxxx0xxxxxxxxxxxxxxxxxxxx, 1, FLAG_BLK)
/* STM{cond}{stack} {rn}{!}, {rlist}{^} */
INSTR(STM) {
  // TODO
  // CHECK_COND();

  I32 base = LOAD_RN_I32(i.blk.rn);
  uint32_t offset = popcnt32(i.blk.rlist) * 4;
  I32 final = i.blk.u ? ADD_IMM_I32(base, offset) : SUB_IMM_I32(base, offset);
  int wrote = 0;

  for (int bit = 0; bit < 16; bit++) {
    int reg = bit;

    if (!i.blk.u) {
      reg = 15 - bit;
    }

    if (i.blk.rlist & (1 << reg)) {
      /* pre-increment */
      if (i.blk.p) {
        base = i.blk.u ? ADD_IMM_I32(base, 4) : SUB_IMM_I32(base, 4);
      }

      /* user bank transfer */
      if (i.blk.s) {
        reg = GET_USER_MODE_REG(reg);
      }

      I32 data = LOAD_RD_I32(reg);
      STORE_I32(base, data);

      /* post-increment */
      if (!i.blk.p) {
        base = i.blk.u ? ADD_IMM_I32(base, 4) : SUB_IMM_I32(base, 4);
      }

      /*
       * when write-back is specified, the base is written back at the end of
       * the second cycle of the instruction. during a STM, the first register
       * is written out at the start of the second cycle. a STM which includes
       * storing the base, with the base as the first register to be stored,
       * will therefore store the unchanged value, whereas with the base second
       * or later in the transfer order, will store the modified value
       */
      if (i.blk.w && !wrote) {
        STORE_GPR_I32(i.blk.rn, final);
        wrote = 1;
      }
    }
  }

  STORE_GPR_IMM_I32(15, addr + 4);
}

//ARMV3_INSTR(SWP,     "swp{cond}{b} {rd}, {rm}, [{rn}]",                xxxx00010x00xxxxxxxx00001001xxxx, 1, FLAG_SWP)
/* SWP{cond}{b} {rd}, {rm}, [{rn}] */
INSTR(SWP) {
  // TODO
  // CHECK_COND();

  I32 ea = LOAD_RN_I32(i.swp.rn);
  I32 new_value = LOAD_RN_I32(i.swp.rm);
  I32 old_value = I32_IMM(0);

  if (i.swp.b) {
    old_value = LOAD_I8(ea);
    STORE_I8(ea, new_value);
  } else {
    old_value = LOAD_I32(ea);
    STORE_I32(ea, new_value);
  }

  STORE_GPR_IMM_I32(15, addr + 4);
  STORE_GPR_I32(i.swp.rd, old_value);
}

//ARMV3_INSTR(SWI,     "swi{cond} {imm}",                                xxxx1111xxxxxxxxxxxxxxxxxxxxxxxx, 1, FLAG_SWI)
/* SWI{cond} {imm} */
INSTR(SWI) {
  // TODO
  //CHECK_COND();

  STORE_GPR_IMM_I32(15, addr + 4);
  CALL_SWI();
}
