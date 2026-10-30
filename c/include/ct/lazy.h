#ifndef CT_LAZY_H
#define CT_LAZY_H

/*
 * The lazy (call-by-need) machine (the Lean development, `Start/`, namespace `CT.Lazy`;
 * Start/LazyMachine.lean and Start/LazyStepFn.lean):
 *
 * - closures, heap cells, stack frames and states (`LClos`, `Cell`, `Frame`,
 *   `LState`), `Cell.orig`, `LState.init`;
 * - the labels of the transitions with `LLabel.betaCount` and
 *   `LLabel.forced`;
 * - one transition as a function (`lstepFn`), performed in place.
 */

#include "ct/base.h"
#include "ct/lambda.h"

/* An environment `List ℕ` of heap addresses: NULL is `[]`.  Immutable; lives
   in an arena; tails are shared. */
typedef struct ct_lenv ct_lenv;
struct ct_lenv {
  uint64_t addr;
  const ct_lenv *tail;
};

/* The closure `⟨code, env⟩` (`LClos`). */
typedef struct ct_lclos {
  const ct_lambda *code;
  const ct_lenv *env;
} ct_lclos;

enum {
  CT_LCELL_THUNK = 0, /* Cell.thunk c   */
  CT_LCELL_HOLE = 1,  /* Cell.hole c    */
  CT_LCELL_VALUE = 2  /* Cell.value c v */
};

/* A heap cell; `v` is used by CT_LCELL_VALUE only. */
typedef struct ct_lcell {
  int kind;
  ct_lclos c;
  ct_lclos v;
} ct_lcell;

enum {
  CT_LFRAME_ARG = 0, /* Frame.arg a */
  CT_LFRAME_UPD = 1  /* Frame.upd a */
};

typedef struct ct_lframe {
  int kind;
  uint64_t addr;
} ct_lframe;

/*
 * A state `⟨code, env, stack, heap⟩` (`LState`):
 * - the stack `stack[0..stack_len-1]` is stored bottom first: the Lean stack
 *   is `[stack[stack_len-1], ..., stack[0]]`;
 * - the heap is `heap[0..heap_len-1]` (the Lean list, in order).
 * The arrays have room for `stack_cap` and `heap_cap` elements.
 */
typedef struct ct_lstate {
  const ct_lambda *code;
  const ct_lenv *env;
  uint64_t stack_len;
  uint64_t stack_cap;
  ct_lframe *stack;
  uint64_t heap_len;
  uint64_t heap_cap;
  ct_lcell *heap;
} ct_lstate;

enum {
  CT_LLABEL_APP = 0,
  CT_LLABEL_BETA = 1,
  CT_LLABEL_FORCE = 2, /* LLabel.force addr */
  CT_LLABEL_FETCH = 3,
  CT_LLABEL_UPDATE = 4
};

typedef struct ct_llabel {
  int kind;
  uint64_t addr; /* CT_LLABEL_FORCE only */
} ct_llabel;

/* `a :: e`. */
ct_status ct_lenv_cons(ct_arena *a, uint64_t addr, const ct_lenv *e,
                       const ct_lenv **out);

/* `Cell.orig c`. */
ct_status ct_lazy_cell_orig(const ct_lcell *c, ct_lclos *out);

/* `LState.init t`, using the caller's arrays (empty stack and heap). */
ct_status ct_lazy_init(const ct_lambda *t, ct_lframe *stack,
                       uint64_t stack_cap, ct_lcell *heap, uint64_t heap_cap,
                       ct_lstate *out);

/* `LLabel.betaCount l`. */
ct_status ct_lazy_beta_count(const ct_llabel *l, uint64_t *out);

/* `LLabel.forced l`: `*has` is false for `[]`, true for `[*addr]`. */
ct_status ct_lazy_forced(const ct_llabel *l, bool *has, uint64_t *addr);

/*
 * One transition `lstepFn s`, in place.  On CT_OK, `*halted` is true when
 * `lstepFn s = none` (then `*s` is unchanged), and false when
 * `lstepFn s = some s'`, with `*s` now representing `s'`.  CT_ELIMIT (with
 * `*s` unchanged) when the transition needs a stack entry or a heap cell
 * beyond the capacities; CT_ENOMEM when the environment cell cannot be
 * allocated in `a`.
 */
ct_status ct_lazy_step(ct_arena *a, ct_lstate *s, bool *halted);

#endif
