#ifndef CT_LEFTMOST_H
#define CT_LEFTMOST_H

/*
 * Leftmost-outermost reduction as a function (the Lean development, `Start/`):
 * `CT.Lambda.step_normal` (Start/EvalSound.lean), `CT.Lambda.nstep` and
 * `CT.Lambda.closure` (Start/LeftmostRun.lean).
 *
 * The limits `lim` are those of `ct_lambda_step` (ct/lambda.h).  Results are
 * written only on CT_OK.
 */

#include "ct/base.h"
#include "ct/lambda.h"

/*
 * `Lambda.step_normal t`: on CT_OK, `*none` is true when the result is
 * `none` (then `*out` is not written), and false when it is `some t'`, with
 * `*out = t'`.
 */
ct_status ct_leftmost_step_normal(ct_arena *a, const ct_lambda *t,
                                  const ct_lambda_limits *lim,
                                  const ct_lambda **out, bool *none);

/* `Lambda.nstep t = (step_normal t).getD t`. */
ct_status ct_leftmost_nstep(ct_arena *a, const ct_lambda *t,
                            const ct_lambda_limits *lim,
                            const ct_lambda **out);

/* `Lambda.closure k t` (`k` abstractions around `t`); CT_ELIMIT if `k`
   exceeds `lim->max_nodes`. */
ct_status ct_leftmost_closure(ct_arena *a, uint64_t k, const ct_lambda *t,
                              const ct_lambda_limits *lim,
                              const ct_lambda **out);

#endif
