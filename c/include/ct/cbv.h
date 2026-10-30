#ifndef CT_CBV_H
#define CT_CBV_H

/*
 * The CEK machine for call-by-value reduction (the Lean development, `Start/`, namespace
 * `CT.CEK`; Start/CbvMachine.lean and Start/CbvStepFn.lean):
 *
 * - frames, continuations and states (`Frame`, `List Frame`, `State`);
 * - the initial state (`State.init`);
 * - one transition as a function (`stepFn`);
 * - the number of β-steps of a label (`Label.betaCount`);
 * - the decoding of a state into a term (`plug`, `State.decode`);
 * - the termination measure of the administrative transitions (`kWeight`,
 *   `measure`).
 *
 * Closures and environments are those of the Krivine machine (`Krivine.Clos`,
 * `Krivine.Env`, see ct/krivine.h).  Every function writes its results only
 * when it returns CT_OK.
 */

#include "ct/base.h"
#include "ct/krivine.h"
#include "ct/lambda.h"

/* The kinds of frames (`Frame`). */
enum {
  CT_CEK_ARG = 0, /* Frame.arg u e */
  CT_CEK_FN = 1   /* Frame.fn c    */
};

typedef struct ct_cek_cont ct_cek_cont;

/*
 * A continuation `List Frame`: NULL is `[]`, a node is `frame :: tail`, where
 * the frame is `Frame.arg u e` if `kind == CT_CEK_ARG` (then `c` is NULL) and
 * `Frame.fn c` if `kind == CT_CEK_FN` (then `u` and `e` are NULL).  Immutable;
 * lives in an arena; tails are shared.
 */
struct ct_cek_cont {
  int kind;
  const ct_lambda *u;   /* Frame.arg: the argument still to be evaluated */
  const ct_kenv *e;     /* Frame.arg: its environment (NULL is [])       */
  const ct_kclos *c;    /* Frame.fn: the function value                  */
  const ct_cek_cont *tail;
};

/* The kinds of states (`State`). */
enum {
  CT_CEK_EVAL = 0, /* State.eval t e k */
  CT_CEK_RET = 1   /* State.ret c k    */
};

/*
 * A state: `State.eval t e k` if `kind == CT_CEK_EVAL` (then `c` is NULL),
 * `State.ret c k` if `kind == CT_CEK_RET` (then `t` and `e` are NULL).
 */
typedef struct ct_cek_state {
  int kind;
  const ct_lambda *t;
  const ct_kenv *e;
  const ct_kclos *c;
  const ct_cek_cont *k;
} ct_cek_state;

/* The labels of the transitions (`Label`). */
enum {
  CT_CEK_ADMIN = 0, /* Label.admin */
  CT_CEK_BETA = 1   /* Label.beta  */
};

/* `Frame.arg u e :: tail`. */
ct_status ct_cek_cont_arg(ct_arena *a, const ct_lambda *u, const ct_kenv *e,
                          const ct_cek_cont *tail, const ct_cek_cont **out);

/* `Frame.fn c :: tail`. */
ct_status ct_cek_cont_fn(ct_arena *a, const ct_kclos *c,
                         const ct_cek_cont *tail, const ct_cek_cont **out);

/* `State.init t`. */
ct_status ct_cek_init(const ct_lambda *t, ct_cek_state *out);

/*
 * One transition `stepFn s`.  On CT_OK, `*halted` is true when
 * `stepFn s = none` (then `*out` is not written), and false when
 * `stepFn s = some s'`, with `*out` set to `s'` (built in `a`; it shares the
 * parts of `s` it keeps).
 */
ct_status ct_cek_step(ct_arena *a, const ct_cek_state *s, bool *halted,
                      ct_cek_state *out);

/* `Label.betaCount l` for `l` one of CT_CEK_ADMIN, CT_CEK_BETA. */
ct_status ct_cek_beta_count(int label, uint64_t *out);

/*
 * `plug k M` and `State.decode s`.  The term is built in `a`; `lim->max_nodes`
 * bounds the number of application nodes built directly and the work of each
 * unfolding of a closure (`Krivine.Clos.unfold`, see `ct_krivine_unfold`),
 * and `lim->max_depth` the depth of the recursion of each unfolding.
 */
ct_status ct_cek_plug(ct_arena *a, const ct_cek_cont *k, const ct_lambda *m,
                      const ct_lambda_limits *lim, const ct_lambda **out);
ct_status ct_cek_decode(ct_arena *a, const ct_cek_state *s,
                        const ct_lambda_limits *lim, const ct_lambda **out);

/*
 * `kWeight k` and `measure s`.  `max_depth` bounds the depth of each term
 * whose size is computed (see `ct_lambda_size`); CT_EOVERFLOW if the value
 * does not fit in `uint64_t`.
 */
ct_status ct_cek_kweight(const ct_cek_cont *k, uint64_t max_depth,
                         uint64_t *out);
ct_status ct_cek_measure(const ct_cek_state *s, uint64_t max_depth,
                         uint64_t *out);

#endif
