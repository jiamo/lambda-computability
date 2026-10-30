#ifndef CT_SPACEMACHINE_H
#define CT_SPACEMACHINE_H

/*
 * Offline space-bounded machines (the Lean development, `Start/`, namespace
 * `CT.Complexity.Space`; Start/SpaceMachine.lean): `Config.space`,
 * `writeAt`, `moveWork`, `moveIn`, `Machine.stepList`, `init`,
 * `Machine.constMachine`.
 *
 * A work tape `List Bool` is `bits[0..len-1]` in a buffer of capacity `cap`.
 * A machine is given by a table: `delta q a b` for `q < states` is the list
 * `instrs[start .. start + count - 1]` of the entry
 * `entries[q * 6 + ai * 2 + (b ? 1 : 0)]`, where `ai` is 0 for `none` (the end
 * marker), 1 for `some false`, 2 for `some true`; for `q >= states` it is
 * `[]`.  `accept q` is `accept[q]` for `q < states`, false otherwise.  Results
 * are written only on CT_OK (except the output arrays of `ct_sp_step_list`,
 * whose contents are unspecified after an error).
 */

#include "ct/base.h"

/* `Dir`. */
enum { CT_SP_LEFT = 0, CT_SP_RIGHT = 1, CT_SP_STAY = 2 };

typedef struct ct_sp_config {
  uint64_t state;
  uint64_t in_head;
  uint64_t tape_len;
  uint64_t tape_cap;
  bool *tape;
  uint64_t w_head;
} ct_sp_config;

/* An instruction `(state, bit, input move, work move)`. */
typedef struct ct_sp_instr {
  uint64_t state;
  bool bit;
  int in_move;
  int work_move;
} ct_sp_instr;

typedef struct ct_sp_entry {
  uint64_t start;
  uint64_t count;
} ct_sp_entry;

typedef struct ct_sp_machine {
  uint64_t states;
  const bool *accept;        /* states entries */
  const ct_sp_entry *entries; /* 6 * states entries */
  const ct_sp_instr *instrs;
  uint64_t n_instrs;
} ct_sp_machine;

/* `Config.space c = max c.tape.length (c.wHead + 1)`. */
ct_status ct_sp_config_space(const ct_sp_config *c, uint64_t *out);

/* `writeAt l i b`, in place on `bits[0..*len-1]` (capacity `cap`): CT_ELIMIT
   if the result is longer than `cap`. */
ct_status ct_sp_write_at(bool *bits, uint64_t *len, uint64_t cap, uint64_t i,
                         bool b);

/* `moveWork i d` and `moveIn n i d`. */
ct_status ct_sp_move_work(uint64_t i, int d, uint64_t *out);
ct_status ct_sp_move_in(uint64_t n, uint64_t i, int d, uint64_t *out);

/* `M.accept q` for a table machine. */
ct_status ct_sp_accept(const ct_sp_machine *m, uint64_t q, bool *out);

/*
 * `M.stepList x c` on the input `x[0..n-1]`: the successors are written to
 * `out[0..*count-1]` (CT_ELIMIT if there are more than `out_cap`); the work
 * tape of `out[i]` is built in `bufs[i]`, of capacity `buf_cap` (CT_ELIMIT if
 * it does not fit).  Every instruction index must be below `m->n_instrs`
 * (otherwise CT_EINVAL).
 */
ct_status ct_sp_step_list(const ct_sp_machine *m, const bool *x, uint64_t n,
                          const ct_sp_config *c, ct_sp_config *out,
                          uint64_t out_cap, bool *const *bufs,
                          uint64_t buf_cap, uint64_t *count);

/* `init = ⟨0, 0, [], 0⟩`, with the work tape buffer `buf` of capacity
   `cap`. */
ct_status ct_sp_init(bool *buf, uint64_t cap, ct_sp_config *out);

/* `constMachine b`: one state, `accept = fun _ => b`, `delta = []`; `accept`
   and `entries` are caller arrays of 1 and 6 elements. */
ct_status ct_sp_const_machine(bool b, bool *accept, ct_sp_entry *entries,
                              ct_sp_machine *out);

#endif
