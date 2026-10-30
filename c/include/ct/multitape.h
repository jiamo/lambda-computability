#ifndef CT_MULTITAPE_H
#define CT_MULTITAPE_H

/*
 * Multi-tape machines and the gate inputs of depth-three circuits
 * (the Lean development, `Start/`, namespace `CT.DepthThreeLowerBound`;
 * Start/DepthThreeModel.lean): `Literal.eval`, `GateInput.eval`,
 * `Circuit3.gateCount`, `runSteps`, `HeadMove.apply`, `multiTapeUpdate`,
 * `multiTapeStep`, `FiniteMultiTapeMachine.step` and `.init`.
 *
 * Finite types are `Fin n`: the variables of a cube `V = Fin nv`, the tapes
 * `K = Fin nk` (nk <= CT_MT_MAX_TAPES), the alphabet `Γ = Fin ng` with blank
 * `default = 0`, the states `Q = Fin nq`.
 *
 * A tape `Turing.Tape Γ` is a window `cells[0..len-1]` with the head at
 * `pos < len`; every cell outside the window is blank.  It stands for the
 * tape with head `cells[pos]`, left part `cells[pos-1], ..., cells[0]` and
 * right part `cells[pos+1], ..., cells[len-1]` (then blanks).  A move out of
 * the window returns CT_ELIMIT.
 */

#include "ct/base.h"

#define CT_MT_MAX_TAPES 8

/* `HeadMove`. */
enum { CT_MT_LEFT = 0, CT_MT_STAY = 1, CT_MT_RIGHT = 2 };

typedef struct ct_mt_tape {
  uint64_t len;
  uint64_t pos;
  uint32_t *cells;
} ct_mt_tape;

/* `MultiTapeCfg`: the state and the tapes `tapes[0..nk-1]`. */
typedef struct ct_mt_cfg {
  uint32_t q;
  ct_mt_tape tapes[CT_MT_MAX_TAPES];
} ct_mt_cfg;

/* One entry `Option (Q × (K → Γ) × (K → HeadMove))` of a code table. */
typedef struct ct_mt_entry {
  bool defined; /* false: none */
  uint32_t q;
  uint32_t writes[CT_MT_MAX_TAPES];
  int moves[CT_MT_MAX_TAPES];
} ct_mt_entry;

/*
 * A `FiniteMultiTapeMachine`.  The code `MultiTapeCode K Γ Q` is the table
 * `code[0..nq * ng^nk - 1]`: the entry for state `q` and read symbols
 * `r : K → Γ` is at index `q * ng^nk + Σ_k r k * ng^k`.  `accept[0..nq-1]`.
 * Preconditions: 1 <= nk <= CT_MT_MAX_TAPES, ng >= 1, nq >= 1, every state,
 * symbol and move stored in the machine is in range, input_tape < nk.
 */
typedef struct ct_mt_machine {
  uint32_t nk;
  uint32_t ng;
  uint32_t nq;
  uint32_t input_tape;
  uint32_t initial_state;
  uint32_t input_symbol[2]; /* inputSymbol false, inputSymbol true */
  const ct_mt_entry *code;
  const bool *accept;
} ct_mt_machine;

/* A gate input `Sum (Literal V) Bool`: `inl (var, val)` or `inr val`. */
typedef struct ct_mt_gate_input {
  bool is_literal;
  uint64_t var;
  bool val;
} ct_mt_gate_input;

/* `Literal.eval (var, val) x`; the cube is `x[0..nv-1]`; CT_EINVAL if
   var >= nv. */
ct_status ct_mt_literal_eval(uint64_t var, bool val, const bool *x,
                             uint64_t nv, bool *out);

/* `GateInput.eval g x`. */
ct_status ct_mt_gate_input_eval(const ct_mt_gate_input *g, const bool *x,
                                uint64_t nv, bool *out);

/* `Circuit3.gateCount` of a circuit with the given counts. */
ct_status ct_mt_gate_count(uint64_t bottom_count, uint64_t middle_count,
                           uint64_t *out);

/* `HeadMove.apply m t`, in place. */
ct_status ct_mt_headmove_apply(int move, ct_mt_tape *t);

/* `multiTapeUpdate c q writes moves` on the `nk` tapes, in place (`c` is
   unchanged unless CT_OK is returned). */
ct_status ct_mt_update(uint32_t nk, ct_mt_cfg *c, uint32_t q,
                       const uint32_t *writes, const int *moves);

/* `M.step c` (`multiTapeStep M.code c`), in place: on CT_OK `*halted` is true
   iff the result is `none` (then `*c` is unchanged). */
ct_status ct_mt_step(const ct_mt_machine *m, ct_mt_cfg *c, bool *halted);

/*
 * `M.init input`: every tape gets the window `bufs[k][0..len-1]`, filled with
 * blanks, with the head at `origin`; the input tape holds the symbols of
 * `input[0..n-1]` from `origin` on.  CT_ELIMIT unless `origin < len` and
 * `origin + n <= len`.
 */
ct_status ct_mt_init(const ct_mt_machine *m, const bool *input, uint64_t n,
                     uint32_t *const *bufs, uint64_t len, uint64_t origin,
                     ct_mt_cfg *out);

/* `runSteps M.step n (some c)`, in place: on CT_OK, `*none` is true iff the
   result is `none` (the machine halted after fewer than `n` steps; `*c` is
   then its last configuration), and otherwise `*c` is the result. */
ct_status ct_mt_run_steps(const ct_mt_machine *m, ct_mt_cfg *c, uint64_t n,
                          bool *none);

#endif
