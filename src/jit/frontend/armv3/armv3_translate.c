#include "jit/frontend/armv3/armv3_translate.h"
#include "core/assert.h"
#include "core/log.h"
#include "jit/frontend/armv3/armv3_context.h"
#include "jit/frontend/armv3/armv3_frontend.h"
#include "jit/frontend/armv3/armv3_guest.h"
#include "jit/ir/ir.h"
#include "jit/jit.h"

static inline int use_fastmem(struct jit_block *block, uint32_t addr) {
  int index = (addr - block->guest_addr) / 2;
  return block->fastmem[index];
}

static struct ir_value *load_guest(struct ir *ir, struct ir_value *addr,
                                   enum ir_type type, int fastmem) {
  if (fastmem) {
    return ir_load_fast(ir, addr, type);
  }
  return ir_load_guest(ir, addr, type);
}

static void store_guest(struct ir *ir, struct ir_value *addr,
                        struct ir_value *v, int fastmem) {
  if (fastmem) {
    ir_store_fast(ir, addr, v);
    return;
  }
  ir_store_guest(ir, addr, v);
}

/* clang-format off */
#define I8                          struct ir_value*
#define I16                         struct ir_value*
#define I32                         struct ir_value*
#define I64                         struct ir_value*
//#define F32                         struct ir_value*
//#define F64                         struct ir_value*
//#define V128                        struct ir_value*

#define I32_IMM(x)                  ir_alloc_i32(ir, x)
#define CTX                         ((struct armv3_context *)jit->guest->ctx)

#define NEXT_INSTR()               
#define NEXT_NEXT_INSTR()               

#define LOAD_CTX_I8(m)              ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_I8)
#define LOAD_CTX_I16(m)             ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_I16)
#define LOAD_CTX_I32(m)             ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_I32)
//#define LOAD_CTX_I64(m)           ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_I64)
//#define LOAD_CTX_F32(m)           ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_F32)
//#define LOAD_CTX_F64(m)           ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_F64)
//#define LOAD_CTX_V128(m)          ir_load_context(ir, offsetof(struct armv3_context, m), VALUE_V128)
#define STORE_CTX_I32(m, v)         ir_store_context(ir, offsetof(struct armv3_context, m), v);
//#define STORE_CTX_I64(m, v)       ir_store_context(ir, offsetof(struct armv3_context, m), v);
//#define STORE_CTX_F32(m, v)       ir_store_context(ir, offsetof(struct armv3_context, m), v);
//#define STORE_CTX_F64(m, v)       ir_store_context(ir, offsetof(struct armv3_context, m), v);
//#define STORE_CTX_V128(m, v)      ir_store_context(ir, offsetof(struct armv3_context, m), v);
#define STORE_CTX_IMM_I32(m, v)     STORE_CTX_I32(m, ir_alloc_i32(ir, v))

#define LOAD_GPR_I8(n)              LOAD_CTX_I8(r[n])
#define LOAD_GPR_I16(n)             LOAD_CTX_I16(r[n])
#define LOAD_GPR_I32(n)             LOAD_CTX_I32(r[n])
#define STORE_GPR_I32(n, v)         STORE_CTX_I32(r[n], v);
#define STORE_GPR_IMM_I32(n, v)     STORE_CTX_IMM_I32(r[n], v)

#define LOAD_I8(ea)                 ZEXT_I8_I32(load_guest(ir, ea, VALUE_I8,  use_fastmem(block, addr)))
#define LOAD_I16(ea)                load_guest(ir, ea, VALUE_I16, use_fastmem(block, addr))
#define LOAD_I32(ea)                load_guest(ir, ea, VALUE_I32, use_fastmem(block, addr))
//#define LOAD_I64(ea)              load_guest(ir, ea, VALUE_I64, use_fastmem(block, addr))
#define LOAD_IMM_I8(ea)             LOAD_I8(ir_alloc_i32(ir, ea))
#define LOAD_IMM_I16(ea)            LOAD_I16(ir_alloc_i32(ir, ea))
#define LOAD_IMM_I32(ea)            LOAD_I32(ir_alloc_i32(ir, ea))
//#define LOAD_IMM_I64(ea)          LOAD_I64(ir_alloc_i32(ir, ea))

#define STORE_I8(ea, v)             store_guest(ir, ea, v, use_fastmem(block, addr))
#define STORE_I16                   STORE_I8
#define STORE_I32                   STORE_I8
//#define STORE_I64                   STORE_I8

#define SEXT_I8_I32(v)              ir_sext(ir, v, VALUE_I32)
#define SEXT_I16_I32(v)             ir_sext(ir, v, VALUE_I32)
#define SEXT_I16_I64(v)             ir_sext(ir, v, VALUE_I64)
#define SEXT_I32_I64(v)             ir_sext(ir, v, VALUE_I64)

#define ZEXT_I8_I32(v)              ir_zext(ir, v, VALUE_I32)
#define ZEXT_I16_I32(v)             ir_zext(ir, v, VALUE_I32)
#define ZEXT_I16_I64(v)             ir_zext(ir, v, VALUE_I64)
#define ZEXT_I32_I64(v)             ir_zext(ir, v, VALUE_I64)

#define TRUNC_I64_I32(v)            ir_trunc(ir, v, VALUE_I32)

#define SELECT_I8(c, a, b)          ir_select(ir, c, a, b)
#define SELECT_I16                  SELECT_I8
#define SELECT_I32                  SELECT_I8
#define SELECT_I64                  SELECT_I8

#define CMPEQ_I8(a, b)              ir_cmp_eq(ir, a, b)
#define CMPEQ_I16                   CMPEQ_I8
#define CMPEQ_I32                   CMPEQ_I8
#define CMPEQ_I64                   CMPEQ_I8
#define CMPEQ_IMM_I8(a, b)          CMPEQ_I8(a, ir_alloc_i8(ir, b))
#define CMPEQ_IMM_I16(a, b)         CMPEQ_I8(a, ir_alloc_i16(ir, b))
#define CMPEQ_IMM_I32(a, b)         CMPEQ_I8(a, ir_alloc_i32(ir, b))
#define CMPEQ_IMM_I64(a, b)         CMPEQ_I8(a, ir_alloc_i64(ir, b))

#define CMPSLT_I32(a, b)            ir_cmp_slt(ir, a, b)
#define CMPSLT_IMM_I32(a, b)        CMPSLT_I32(a, ir_alloc_i32(ir, b))
#define CMPSLE_I32(a, b)            ir_cmp_sle(ir, a, b)
#define CMPSLE_IMM_I32              CMPSLE_I32(a, ir_alloc_i32(ir, b))
#define CMPSGT_I32(a, b)            ir_cmp_sgt(ir, a, b)
#define CMPSGT_IMM_I32(a, b)        CMPSGT_I32(a, ir_alloc_i32(ir, b))
#define CMPSGE_I32(a, b)            ir_cmp_sge(ir, a, b)
#define CMPSGE_IMM_I32(a, b)        CMPSGE_I32(a, ir_alloc_i32(ir, b))

#define CMPULT_I32(a, b)            ir_cmp_ult(ir, a, b)
#define CMPULT_IMM_I32(a, b)        CMPULT_I32(a, ir_alloc_i32(ir, b))
#define CMPULE_I32(a, b)            ir_cmp_ule(ir, a, b)
#define CMPULE_IMM_I32(a, b)        CMPULE_I32(a, ir_alloc_i32(ir, b))
#define CMPUGT_I32(a, b)            ir_cmp_ugt(ir, a, b)
#define CMPUGT_IMM_I32(a, b)        CMPUGT_I32(a, ir_alloc_i32(ir, b))
#define CMPUGE_I32(a, b)            ir_cmp_uge(ir, a, b)
#define CMPUGE_IMM_I32(a, b)        CMPUGE_I32(a, ir_alloc_i32(ir, b))

#define ADD_I8(a, b)                ir_add(ir, a, b)
#define ADD_I16                     ADD_I8
#define ADD_I32                     ADD_I8
//#define ADD_I64                     ADD_I8
#define ADD_IMM_I8(a, b)            ADD_I8(a, ir_alloc_i8(ir, b))
#define ADD_IMM_I16(a, b)           ADD_I8(a, ir_alloc_i16(ir, b))
#define ADD_IMM_I32(a, b)           ADD_I8(a, ir_alloc_i32(ir, b))
//#define ADD_IMM_I64(a, b)           ADD_I8(a, ir_alloc_i64(ir, b))

#define SUB_I8(a, b)                ir_sub(ir, a, b)
#define SUB_I16                     SUB_I8
#define SUB_I32                     SUB_I8
//#define SUB_I64                     SUB_I8
#define SUB_IMM_I8(a, b)            SUB_I8(a, ir_alloc_i8(ir, b))
#define SUB_IMM_I16(a, b)           SUB_I8(a, ir_alloc_i16(ir, b))
#define SUB_IMM_I32(a, b)           SUB_I8(a, ir_alloc_i32(ir, b))
//#define SUB_IMM_I64(a, b)           SUB_I8(a, ir_alloc_i64(ir, b))

#define SMUL_I8(a, b)               ir_smul(ir, a, b)
#define SMUL_I16                    SMUL_I8
#define SMUL_I32                    SMUL_I8
//#define SMUL_I64                    SMUL_I8
#define SMUL_IMM_I8(a, b)           SMUL_I8(a, ir_alloc_i8(ir, b))
#define SMUL_IMM_I16(a, b)          SMUL_I8(a, ir_alloc_i16(ir, b))
#define SMUL_IMM_I32(a, b)          SMUL_I8(a, ir_alloc_i32(ir, b))
//#define SMUL_IMM_I64(a, b)          SMUL_I8(a, ir_alloc_i64(ir, b))

#define UMUL_I8(a, b)               ir_umul(ir, a, b)
#define UMUL_I16                    UMUL_I8
#define UMUL_I32                    UMUL_I8
//#define UMUL_I64                    UMUL_I8
#define UMUL_IMM_I8(a, b)           UMUL_I8(a, ir_alloc_i8(ir, b))
#define UMUL_IMM_I16(a, b)          UMUL_I8(a, ir_alloc_i16(ir, b))
#define UMUL_IMM_I32(a, b)          UMUL_I8(a, ir_alloc_i32(ir, b))
//#define UMUL_IMM_I64(a, b)          UMUL_I8(a, ir_alloc_i64(ir, b))

#define NEG_I8(a)                   ir_neg(ir, a)
#define NEG_I16                     NEG_I8
#define NEG_I32                     NEG_I8
//#define NEG_I64                     NEG_I8

#define AND_I8(a, b)                ir_and(ir, a, b)
#define AND_I16                     AND_I8
#define AND_I32                     AND_I8
#define AND_I64                     AND_I8
#define AND_IMM_I8(a, b)            AND_I8(a, ir_alloc_i8(ir, b))
#define AND_IMM_I16(a, b)           AND_I8(a, ir_alloc_i16(ir, b))
#define AND_IMM_I32(a, b)           AND_I8(a, ir_alloc_i32(ir, b))
#define AND_IMM_I64(a, b)           AND_I8(a, ir_alloc_i64(ir, b))

#define OR_I8(a, b)                 ir_or(ir, a, b)
#define OR_I16                      OR_I8
#define OR_I32                      OR_I8
#define OR_I64                      OR_I8
#define OR_IMM_I8(a, b)             OR_I8(a, ir_alloc_i8(ir, b))
#define OR_IMM_I16(a, b)            OR_I8(a, ir_alloc_i16(ir, b))
#define OR_IMM_I32(a, b)            OR_I8(a, ir_alloc_i32(ir, b))
//#define OR_IMM_I64(a, b)            OR_I8(a, ir_alloc_i64(ir, b))

#define XOR_I8(a, b)                ir_xor(ir, a, b)
#define XOR_I16                     XOR_I8
#define XOR_I32                     XOR_I8
//#define XOR_I64                     XOR_I8
#define XOR_IMM_I8(a, b)            XOR_I8(a, ir_alloc_i8(ir, b))
#define XOR_IMM_I16(a, b)           XOR_I8(a, ir_alloc_i16(ir, b))
#define XOR_IMM_I32(a, b)           XOR_I8(a, ir_alloc_i32(ir, b))
//#define XOR_IMM_I64(a, b)           XOR_I8(a, ir_alloc_i64(ir, b))

#define NOT_I8(a)                   ir_not(ir, a)
#define NOT_I16                     NOT_I8
#define NOT_I32                     NOT_I8
//#define NOT_I64                     NOT_I8

#define SHL_I8(v, n)                ir_shl(ir, v, n)
#define SHL_I16                     SHL_I8
#define SHL_I32                     SHL_I8
#define SHL_I64                     SHL_I8
#define SHL_IMM_I8(v, n)            ir_shli(ir, v, n)
#define SHL_IMM_I16                 SHL_IMM_I8
#define SHL_IMM_I32                 SHL_IMM_I8
//#define SHL_IMM_I64                 SHL_IMM_I8

#define ASHR_I8(v, n)               ir_ashr(ir, v, n)
#define ASHR_I16                    ASHR_I8
#define ASHR_I32                    ASHR_I8
#define ASHR_I64                    ASHR_I8
#define ASHR_IMM_I8(v, n)           ir_ashri(ir, v, n)
#define ASHR_IMM_I16                ASHR_IMM_I8
#define ASHR_IMM_I32                ASHR_IMM_I8
//#define ASHR_IMM_I64                ASHR_IMM_I8

#define LSHR_I8(v, n)               ir_lshr(ir, v, n)
#define LSHR_I16                    LSHR_I8
#define LSHR_I32                    LSHR_I8
#define LSHR_I64                    LSHR_I8
#define LSHR_IMM_I8(v, n)           ir_lshri(ir, v, n)
#define LSHR_IMM_I16                LSHR_IMM_I8
#define LSHR_IMM_I32                LSHR_IMM_I8
#define LSHR_IMM_I64                LSHR_IMM_I8

#define ASHD_I32(v, n)              ir_ashd(ir, v, n)
#define LSHD_I32(v, n)              ir_lshd(ir, v, n)

#define BRANCH_I32(d)               ir_branch(ir, d)
#define BRANCH_IMM_I32(d)           BRANCH_I32(ir_alloc_i32(ir, d))
#define BRANCH_TRUE_IMM_I32(c, d)   ir_branch_true(ir, c, ir_alloc_i32(ir, d))
#define BRANCH_FALSE_IMM_I32(c, d)  ir_branch_false(ir, c, ir_alloc_i32(ir, d))

#define INVALID_INSTR()             {                                                                                    \
                                      struct ir_value *invalid_instr = ir_alloc_i64(ir, (uint64_t)guest->invalid_instr); \
                                      struct ir_value *data = ir_alloc_i64(ir, (uint64_t)guest->data);                   \
                                      ir_call_1(ir, invalid_instr, data);                                                \
                                    }

#define PREF_SQ_COND(c, addr)       {                                                                                \
                                      struct ir_value *sq_prefetch = ir_alloc_i64(ir, (uint64_t)guest->sq_prefetch); \
                                      struct ir_value *data = ir_alloc_i64(ir, (uint64_t)guest->data);               \
                                      ir_call_cond_2(ir, c, sq_prefetch, data, addr);                                \
                                    }

#define SLEEP()                     {                                                                    \
                                      struct ir_value *sleep = ir_alloc_i64(ir, (uint64_t)guest->sleep); \
                                      struct ir_value *data = ir_alloc_i64(ir, (uint64_t)guest->data);   \
                                      ir_call_1(ir, sleep, data);                                        \
                                    }
                                    
#define LDTLB()                     {                                                                          \
                                      struct ir_value *load_tlb = ir_alloc_i64(ir, (uint64_t)guest->load_tlb); \
                                      struct ir_value *data = ir_alloc_i64(ir, (uint64_t)guest->data);         \
                                      ir_call_1(ir, load_tlb, data);                                           \
                                    }

#define LOAD_RN_I8(n)   ((n==15) ? ADD_IMM_I32(ir_alloc_i32(ir, addr),  8) : LOAD_GPR_I8(n))
#define LOAD_RD_I8(d)   ((d==15) ? ADD_IMM_I32(ir_alloc_i32(ir, addr), 12) : LOAD_GPR_I8(d))
#define LOAD_RN_I32(n)  ((n==15) ? ADD_IMM_I32(ir_alloc_i32(ir, addr),  8) : LOAD_GPR_I32(n))
#define LOAD_RD_I32(d)  ((d==15) ? ADD_IMM_I32(ir_alloc_i32(ir, addr), 12) : LOAD_GPR_I32(d))

//TODO #define PARSE_SHIFT(addr, reg, shift, offset, carry)        { armv3_translate_parse_shift(addr, reg, shift, &offset, &carry); }

/* clang-format on */

#define INSTR(name)                                                           \
  void armv3_translate_##name(struct armv3_guest *guest, struct jit_block *block, \
                            struct ir *ir, uint32_t addr, union armv3_instr i,  \
                            int flags)
#include "jit/frontend/armv3/armv3_instr.h"
#undef INSTR

armv3_translate_cb armv3_translators[NUM_ARMV3_OPS] = {
#define ARMV3_INSTR(name, desc, sig, cycles, flags) &armv3_translate_##name,
#include "jit/frontend/armv3/armv3_instr.inc"
#undef ARMV3_INSTR
};
