#include "ct/leftmost.h"

ct_status ct_leftmost_step_normal(ct_arena *a, const ct_lambda *t,
                                  const ct_lambda_limits *lim,
                                  const ct_lambda **out, bool *none) {
  const ct_lambda *r = NULL;
  bool normal = false;
  ct_status st = ct_lambda_step(a, t, lim, &r, &normal);
  if (st != CT_OK) {
    return st;
  }
  if (normal) {
    *none = true;
  } else {
    *none = false;
    *out = r;
  }
  return CT_OK;
}

ct_status ct_leftmost_nstep(ct_arena *a, const ct_lambda *t,
                            const ct_lambda_limits *lim,
                            const ct_lambda **out) {
  const ct_lambda *r = NULL;
  bool none = false;
  ct_status st = ct_leftmost_step_normal(a, t, lim, &r, &none);
  if (st != CT_OK) {
    return st;
  }
  *out = none ? t : r;
  return CT_OK;
}

ct_status ct_leftmost_closure(ct_arena *a, uint64_t k, const ct_lambda *t,
                              const ct_lambda_limits *lim,
                              const ct_lambda **out) {
  const ct_lambda *acc = t;
  uint64_t i;
  ct_status st;
  if (k > lim->max_nodes) {
    return CT_ELIMIT;
  }
  for (i = 0; i < k; i++) {
    st = ct_lambda_lam(a, acc, &acc);
    if (st != CT_OK) {
      return st;
    }
  }
  *out = acc;
  return CT_OK;
}
