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

//ARMV3_INSTR(LDR,     "ldr{cond}{b}{t} {rd}, {addr}",                   xxxx01xxxxx1xxxxxxxxxxxxxxxxxxxx, 1, FLAG_XFR)
/* LDR{cond}{b}{t} {rd}, {addr} */
INSTR(LDR) {
  I32 base;
  I32 final;
  I32 ea;
  I32 data;

  /* parse offset */
  uint32_t offset = 0;
  if (i.xfr.i) {
    // TODO (this should not happen yet)
    //uint32_t carry;
    //PARSE_SHIFT(addr, i.xfr_reg.rm, i.xfr_reg.shift, offset, carry);
  } else  {
    offset = i.xfr_imm.imm;
  }

  base = LOAD_RN(i.xfr.rn);
  if (i.xfr.u)
    final = ADD_IMM_I32(base, offset);
  else
    final = SUB_IMM_I32(base, offset);
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
}

//ARMV3_INSTR(STR,     "str{cond}{b}{t} {rd}, {addr}",                   xxxx01xxxxx0xxxxxxxxxxxxxxxxxxxx, 1, FLAG_XFR)
/* STR{cond}{b}{t} {rd}, {addr} */
INSTR(STR) {
  /* TODO */
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
