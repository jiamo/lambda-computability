#ifndef CT_MINSKY_H
#define CT_MINSKY_H

/*
 * Counter machines and their compilation to two-counter machines
 * (the Lean development, `Start/`; Start/FsubGhelli.lean for `CMInstr`, `CM`, `CMConf`;
 * Start/Minsky.lean for `KInstr`, `KInstr.reg`, `KM`, `KConf`, `base`,
 * `godel`, `incF`, `exitL`, `testF`, `isize`, `off`, `blockF`,
 * `compileAux`, `compile`, `encC`).
 *
 * Registers `ℕ → ℕ` are given by an array `r[0..nr-1]`; registers from `nr`
 * on are 0.  Every `ℕ` is a `uint64_t`; CT_EOVERFLOW when a value does not
 * fit.  Results are written only on CT_OK.
 */

#include "ct/base.h"

/* `KInstr`: `inc reg l1` or `test reg l1 l2`. */
enum { CT_KINSTR_INC = 0, CT_KINSTR_TEST = 1 };

typedef struct ct_kinstr {
  int kind;
  uint64_t reg;
  uint64_t l1;
  uint64_t l2; /* test only; 0 for inc */
} ct_kinstr;

/* `CMInstr`: `inc ctr l1` or `test ctr l1 l2` (`ctr` true: the first
   counter `a`, false: the second counter `b`). */
enum { CT_CMINSTR_INC = 0, CT_CMINSTR_TEST = 1 };

typedef struct ct_cminstr {
  int kind;
  bool ctr;
  uint64_t l1;
  uint64_t l2; /* test only; 0 for inc */
} ct_cminstr;

/* `CMConf`. */
typedef struct ct_cmconf {
  uint64_t pc;
  uint64_t a;
  uint64_t b;
} ct_cmconf;

/* A machine `KM = List KInstr`: `prog[0..len-1]`. */
typedef struct ct_km {
  uint64_t len;
  const ct_kinstr *prog;
} ct_km;

/* `KInstr.reg ins`. */
ct_status ct_minsky_reg(const ct_kinstr *ins, uint64_t *out);

/* `base i = Nat.fermatNumber i = 2^(2^i) + 1` (fits only for i <= 5). */
ct_status ct_minsky_base(uint64_t i, uint64_t *out);

/* `godel k r = ∏ i < k, base i ^ r i`. */
ct_status ct_minsky_godel(uint64_t k, const uint64_t *r, uint64_t nr,
                          uint64_t *out);

/* `incF p o t j` and `testF p o t1 t2 j`; CT_EOVERFLOW also when a label of
   the block (at most `o + 3p + 2`) does not fit. */
ct_status ct_minsky_inc_f(uint64_t p, uint64_t o, uint64_t t, uint64_t j,
                          ct_cminstr *out);
ct_status ct_minsky_test_f(uint64_t p, uint64_t o, uint64_t t1, uint64_t t2,
                           uint64_t j, ct_cminstr *out);

/* `exitL p o j` (with the truncated subtraction of `ℕ`). */
ct_status ct_minsky_exit_l(uint64_t p, uint64_t o, uint64_t j,
                           uint64_t *out);

/* `isize ins`, `off M l` and `blockF M o ins j`. */
ct_status ct_minsky_isize(const ct_kinstr *ins, uint64_t *out);
ct_status ct_minsky_off(const ct_km *m, uint64_t l, uint64_t *out);
ct_status ct_minsky_block_f(const ct_km *m, uint64_t o, const ct_kinstr *ins,
                            uint64_t j, ct_cminstr *out);

/* `compile M`, written to `out[0..*out_len-1]`; CT_ELIMIT if it has more
   than `cap` instructions. */
ct_status ct_minsky_compile(const ct_km *m, ct_cminstr *out, uint64_t cap,
                            uint64_t *out_len);

/* `compileAux M (M.drop s) s`: the blocks of the instructions from label
   `s` on, written as in `ct_minsky_compile`. */
ct_status ct_minsky_compile_aux(const ct_km *m, uint64_t s, ct_cminstr *out,
                                uint64_t cap, uint64_t *out_len);

/* `encC M k ⟨pc, r⟩ = ⟨off M pc, godel k r, 0⟩`. */
ct_status ct_minsky_enc_c(const ct_km *m, uint64_t k, uint64_t pc,
                          const uint64_t *r, uint64_t nr, ct_cmconf *out);

#endif
