#ifndef CT_KRIVINE_H
#define CT_KRIVINE_H

/*
 * The Krivine machine (the Lean development, `Start/`, namespace `CT.Krivine`):
 *
 * - closures, environments and states (`Clos`, `Env`, `State`);
 * - the code table of a term (`Impl.Node`, `Impl.Tab`, `Impl.decTermF`,
 *   `Impl.decTerm`, `Impl.flatten`, `Impl.tabOf`, `Impl.rootOf`;
 *   Start/KrivineTable.lean);
 * - the heap implementation (`Impl.Cell`, `Impl.Heap`, `Impl.decClF`,
 *   `Impl.decEnvF`, `Impl.decClos`, `Impl.decEnvP`, `Impl.envNth`,
 *   `Impl.HState`, `Impl.decState`, `Impl.initState`, `Impl.hstep`;
 *   Start/KrivineHeap.lean);
 * - the decoding of a state into a term (`Clos.unfold`, `unfoldEnv`, `spine`,
 *   `State.decode`; Start/KrivineDecode.lean).
 *
 * Every function writes its results only when it returns CT_OK, except
 * `ct_krivine_hstep`, which updates the state it is given (see there).
 * Objects written by a call must not overlap its inputs.
 */

#include "ct/base.h"
#include "ct/lambda.h"

/* ------------------------------------------------------------------------ */
/* Closures, environments and states                                          */
/* ------------------------------------------------------------------------ */

typedef struct ct_kclos ct_kclos;
typedef struct ct_kenv ct_kenv;

/* The closure `Clos.mk code env`.  Immutable; lives in an arena. */
struct ct_kclos {
  const ct_lambda *code;
  const ct_kenv *env; /* NULL is the empty environment */
};

/*
 * A list of closures (`Env = List Clos`, also used for stacks): NULL is `[]`,
 * a node is `head :: tail`.  Immutable; lives in an arena; tails are shared.
 */
struct ct_kenv {
  const ct_kclos *head;
  const ct_kenv *tail;
};

/* The state `⟨code, env, stack⟩` of the machine (`Krivine.State`). */
typedef struct ct_kstate {
  const ct_lambda *code;
  const ct_kenv *env;   /* the environment */
  const ct_kenv *stack; /* the stack, top (outermost argument) first */
} ct_kstate;

/* `Clos.mk code env`. */
ct_status ct_kclos_mk(ct_arena *a, const ct_lambda *code, const ct_kenv *env,
                      const ct_kclos **out);

/* `head :: tail`. */
ct_status ct_kenv_cons(ct_arena *a, const ct_kclos *head, const ct_kenv *tail,
                       const ct_kenv **out);

/* The labels of the transitions (`Krivine.Label`). */
enum {
  CT_KRIVINE_APP = 0,  /* Label.app  */
  CT_KRIVINE_BETA = 1, /* Label.beta */
  CT_KRIVINE_VAR = 2   /* Label.var  */
};

/* ------------------------------------------------------------------------ */
/* The code table (Start/KrivineTable.lean)                                   */
/* ------------------------------------------------------------------------ */

enum {
  CT_KNODE_VAR = 0, /* Node.var x   */
  CT_KNODE_APP = 1, /* Node.app x y */
  CT_KNODE_LAM = 2  /* Node.lam x   */
};

/*
 * A node of the table: `kind` is one of CT_KNODE_*; unused fields are 0 (`y`
 * for a variable or an abstraction).
 */
typedef struct ct_knode {
  int kind;
  uint64_t x;
  uint64_t y;
} ct_knode;

/* A table `Tab = List Node`: `len` nodes at `nodes` (not read if len == 0). */
typedef struct ct_ktab {
  uint64_t len;
  const ct_knode *nodes;
} ct_ktab;

/*
 * `Impl.flatten t tab`: `*out_tab` is a new table (allocated in `a`) whose
 * nodes are those of `tab` followed by the nodes of `t`, and `*out_root` the
 * address of `t` in it.  CT_ELIMIT if the height of `t` exceeds `max_depth`
 * (a variable has height 1); CT_EOVERFLOW if the size would wrap around.
 */
ct_status ct_krivine_flatten(ct_arena *a, const ct_lambda *t,
                             const ct_ktab *tab, uint64_t max_depth,
                             ct_ktab *out_tab, uint64_t *out_root);

/* `Impl.tabOf t` and `Impl.rootOf t`, i.e. `Impl.flatten t []`. */
ct_status ct_krivine_tab_of(ct_arena *a, const ct_lambda *t,
                            uint64_t max_depth, ct_ktab *out_tab,
                            uint64_t *out_root);

/*
 * `Impl.decTermF tab fuel p`.  The term is built in `a`; `lim->max_nodes`
 * bounds the number of nodes built and `lim->max_depth` the depth of the
 * recursion (CT_ELIMIT when exceeded).
 */
ct_status ct_krivine_dec_term_f(ct_arena *a, const ct_ktab *tab, uint64_t fuel,
                                uint64_t p, const ct_lambda_limits *lim,
                                const ct_lambda **out);

/* `Impl.decTerm tab p`, with the limits of `ct_krivine_dec_term_f`. */
ct_status ct_krivine_dec_term(ct_arena *a, const ct_ktab *tab, uint64_t p,
                              const ct_lambda_limits *lim,
                              const ct_lambda **out);

/* ------------------------------------------------------------------------ */
/* The heap (Start/KrivineHeap.lean)                                          */
/* ------------------------------------------------------------------------ */

enum {
  CT_KCELL_CLOS = 0, /* Cell.clos x y */
  CT_KCELL_CONS = 1  /* Cell.cons x y */
};

/*
 * A cell of the heap: `kind` is one of CT_KCELL_*.  The second component, an
 * `Option ℕ`, is `some y` when `has_y` is true and `none` otherwise (then `y`
 * is 0).
 */
typedef struct ct_kcell {
  int kind;
  uint64_t x;
  bool has_y;
  uint64_t y;
} ct_kcell;

/*
 * Decoding (`Impl.decClF`, `Impl.decEnvF`, `Impl.decClos`, `Impl.decEnvP`).
 * The heap is `heap[0..heap_len-1]` (not read if heap_len == 0).  The
 * environment pointer `Option ℕ` is `some e` if `has_e`, `none` otherwise.
 * The result is built in `a`; `lim->max_nodes` bounds the number of nodes
 * built (terms, closures and list cells) and `lim->max_depth` the depth of
 * the recursion.
 */
ct_status ct_krivine_dec_clos_f(ct_arena *a, const ct_ktab *tab,
                                const ct_kcell *heap, uint64_t heap_len,
                                uint64_t fuel, uint64_t p,
                                const ct_lambda_limits *lim,
                                const ct_kclos **out);
ct_status ct_krivine_dec_env_f(ct_arena *a, const ct_ktab *tab,
                               const ct_kcell *heap, uint64_t heap_len,
                               uint64_t fuel, bool has_e, uint64_t e,
                               const ct_lambda_limits *lim,
                               const ct_kenv **out);
ct_status ct_krivine_dec_clos(ct_arena *a, const ct_ktab *tab,
                              const ct_kcell *heap, uint64_t heap_len,
                              uint64_t p, const ct_lambda_limits *lim,
                              const ct_kclos **out);
ct_status ct_krivine_dec_env(ct_arena *a, const ct_ktab *tab,
                             const ct_kcell *heap, uint64_t heap_len,
                             bool has_e, uint64_t e,
                             const ct_lambda_limits *lim, const ct_kenv **out);

/*
 * `Impl.envNth heap e n`: returns true and writes `*out = q` when the result
 * is `some q`; returns false (and writes nothing) when it is `none`.
 */
bool ct_krivine_env_nth(const ct_kcell *heap, uint64_t heap_len, bool has_e,
                        uint64_t e, uint64_t n, uint64_t *out);

/*
 * A state of the implementation (`Impl.HState`):
 * - `code`, and the environment pointer: `some env` if `has_env`, `none`
 *   otherwise (then `env` is 0);
 * - the stack `stack[0..stack_len-1]`, stored bottom first: the Lean stack is
 *   the list `[stack[stack_len-1], ..., stack[0]]`;
 * - the heap `heap[0..heap_len-1]`.
 * `stack` and `heap` have room for `stack_cap` and `heap_cap` elements;
 * `stack_len <= stack_cap` and `heap_len <= heap_cap`.
 */
typedef struct ct_khstate {
  uint64_t code;
  bool has_env;
  uint64_t env;
  uint64_t stack_len;
  uint64_t stack_cap;
  uint64_t *stack;
  uint64_t heap_len;
  uint64_t heap_cap;
  ct_kcell *heap;
} ct_khstate;

/* `Impl.decState tab s`, with the limits of `ct_krivine_dec_clos`. */
ct_status ct_krivine_dec_state(ct_arena *a, const ct_ktab *tab,
                               const ct_khstate *s,
                               const ct_lambda_limits *lim, ct_kstate *out);

/*
 * `Impl.initState t`: `*out` gets code `rootOf t`, no environment, an empty
 * stack and an empty heap, using the caller's arrays `heap` (room for
 * `heap_cap` cells) and `stack` (room for `stack_cap` entries).  CT_ELIMIT if
 * the height of `t` exceeds `max_depth`; CT_EOVERFLOW if its size would wrap.
 */
ct_status ct_krivine_init_state(const ct_lambda *t, uint64_t max_depth,
                                ct_kcell *heap, uint64_t heap_cap,
                                uint64_t *stack, uint64_t stack_cap,
                                ct_khstate *out);

/*
 * One transition `Impl.hstep tab s`, in place.  On CT_OK:
 * - if `hstep tab s = none`, `*stuck` is true and `*s` is unchanged;
 * - if `hstep tab s = some (l, s')`, `*stuck` is false, `*label` is `l` and
 *   `*s` now represents `s'` (at most one cell is appended to the heap and
 *   one entry pushed on the stack).
 * CT_ELIMIT (with `*s`, `*stuck`, `*label` unchanged) if the transition needs
 * a cell or a stack entry beyond `heap_cap` or `stack_cap`.
 */
ct_status ct_krivine_hstep(const ct_ktab *tab, ct_khstate *s, bool *stuck,
                           int *label);

/* ------------------------------------------------------------------------ */
/* Decoding a state into a term (Start/KrivineDecode.lean)                    */
/* ------------------------------------------------------------------------ */

/*
 * The decoders build their result in `a`.  `lim->max_depth` bounds the depth
 * of the recursion and `lim->max_nodes` the number of nodes built directly;
 * each lifting of an environment entry under binders (`CT.Lambda.lift`) is
 * done by `ct_lambda_lift` under the limits `lim`.
 */

/* `Clos.unfold c`. */
ct_status ct_krivine_unfold(ct_arena *a, const ct_kclos *c,
                            const ct_lambda_limits *lim,
                            const ct_lambda **out);

/* `unfoldEnv e i`. */
ct_status ct_krivine_unfold_env(ct_arena *a, const ct_kenv *e, uint64_t i,
                                const ct_lambda_limits *lim,
                                const ct_lambda **out);

/* `spine t stack`. */
ct_status ct_krivine_spine(ct_arena *a, const ct_lambda *t,
                           const ct_kenv *stack, const ct_lambda_limits *lim,
                           const ct_lambda **out);

/* `State.decode s`. */
ct_status ct_krivine_state_decode(ct_arena *a, const ct_kstate *s,
                                  const ct_lambda_limits *lim,
                                  const ct_lambda **out);

#endif
