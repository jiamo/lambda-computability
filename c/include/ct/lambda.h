#ifndef CT_LAMBDA_H
#define CT_LAMBDA_H

/*
 * The untyped λ-calculus with de Bruijn indices: the Lean type `CT.Lambda`
 * and the functions `CT.Lambda.lift`, `.subst`, `.size`, `.church` and the
 * one-step reduction `CT.Lambda.step` (see spec/CTSpec.lean).
 *
 * Terms are immutable and live in an arena; they may share subterms.  They
 * are built only with the constructors below.  Every function writes its
 * results only when it returns CT_OK.
 */

#include "ct/base.h"

enum {
  CT_LAMBDA_VAR = 0, /* var index             */
  CT_LAMBDA_APP = 1, /* app left right        */
  CT_LAMBDA_LAM = 2  /* lam left (the body)   */
};

typedef struct ct_lambda ct_lambda;

/* A term node.  Read-only for clients. */
struct ct_lambda {
  int kind;               /* CT_LAMBDA_VAR, CT_LAMBDA_APP or CT_LAMBDA_LAM */
  uint64_t index;         /* var: the de Bruijn index; otherwise 0 */
  const ct_lambda *left;  /* app: the function; lam: the body; var: NULL */
  const ct_lambda *right; /* app: the argument; otherwise NULL */
};

/*
 * Limits of a computation:
 * - `max_nodes`: the number of nodes one call may allocate;
 * - `max_depth`: the recursion depth one call may reach (a term of height h,
 *   a variable having height 1, needs max_depth >= h).
 * Reaching a limit makes the call return CT_ELIMIT.
 */
typedef struct ct_lambda_limits {
  uint64_t max_nodes;
  uint64_t max_depth;
} ct_lambda_limits;

/* Constructors: `var i`, `app f x`, `lam body`. */
ct_status ct_lambda_var(ct_arena *a, uint64_t i, const ct_lambda **out);
ct_status ct_lambda_app(ct_arena *a, const ct_lambda *f, const ct_lambda *x,
                        const ct_lambda **out);
ct_status ct_lambda_lam(ct_arena *a, const ct_lambda *body,
                        const ct_lambda **out);

/* Structural equality `s = t`. */
ct_status ct_lambda_equal(const ct_lambda *s, const ct_lambda *t,
                          uint64_t max_depth, bool *out);

/* `CT.Lambda.lift n k t`. */
ct_status ct_lambda_lift(ct_arena *a, uint64_t n, uint64_t k,
                         const ct_lambda *t, const ct_lambda_limits *lim,
                         const ct_lambda **out);

/* `CT.Lambda.subst s x t`. */
ct_status ct_lambda_subst(ct_arena *a, const ct_lambda *s, uint64_t x,
                          const ct_lambda *t, const ct_lambda_limits *lim,
                          const ct_lambda **out);

/* `CT.Lambda.size t`; CT_EOVERFLOW if it exceeds UINT64_MAX. */
ct_status ct_lambda_size(const ct_lambda *t, uint64_t max_depth,
                         uint64_t *out);

/* `CT.Lambda.church n`. */
ct_status ct_lambda_church(ct_arena *a, uint64_t n, const ct_lambda_limits *lim,
                           const ct_lambda **out);

/*
 * One leftmost-outermost β-step.  On CT_OK:
 * - if `t` has no redex, `*normal` is true and `*out` is `t`;
 * - otherwise `*normal` is false and `*out` is the term obtained by
 *   contracting the leftmost-outermost redex of `t`.
 */
ct_status ct_lambda_step(ct_arena *a, const ct_lambda *t,
                         const ct_lambda_limits *lim, const ct_lambda **out,
                         bool *normal);

/*
 * Repeats `ct_lambda_step` until a normal form is reached, taking at most
 * `fuel` steps (each step under the limits `lim`).  On CT_OK, `*out` is the
 * normal form and `*steps` the number of steps taken.  Once `fuel` steps have
 * been taken no further step is computed: the term is only checked for
 * normality, and CT_ELIMIT is returned if it is still reducible.  Hence an
 * error other than CT_ELIMIT can only come from one of the first `fuel` steps
 * (with `fuel == 0` the result is CT_OK or CT_ELIMIT).
 */
ct_status ct_lambda_normalize(ct_arena *a, const ct_lambda *t, uint64_t fuel,
                              const ct_lambda_limits *lim,
                              const ct_lambda **out, uint64_t *steps);

#endif
