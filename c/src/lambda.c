#include "ct/lambda.h"

/* Allocates a node, charging it to `*budget`. */
static ct_status mk_node(ct_arena *a, uint64_t *budget, int kind,
                         uint64_t index, const ct_lambda *left,
                         const ct_lambda *right, const ct_lambda **out) {
  void *mem;
  ct_lambda *node;
  ct_status st;
  if (*budget == 0) {
    return CT_ELIMIT;
  }
  st = ct_arena_alloc(a, sizeof(ct_lambda), _Alignof(ct_lambda), &mem);
  if (st != CT_OK) {
    return st;
  }
  *budget = *budget - 1;
  node = mem;
  node->kind = kind;
  node->index = index;
  node->left = left;
  node->right = right;
  *out = node;
  return CT_OK;
}

ct_status ct_lambda_var(ct_arena *a, uint64_t i, const ct_lambda **out) {
  uint64_t budget = 1;
  return mk_node(a, &budget, CT_LAMBDA_VAR, i, NULL, NULL, out);
}

ct_status ct_lambda_app(ct_arena *a, const ct_lambda *f, const ct_lambda *x,
                        const ct_lambda **out) {
  uint64_t budget = 1;
  return mk_node(a, &budget, CT_LAMBDA_APP, 0, f, x, out);
}

ct_status ct_lambda_lam(ct_arena *a, const ct_lambda *body,
                        const ct_lambda **out) {
  uint64_t budget = 1;
  return mk_node(a, &budget, CT_LAMBDA_LAM, 0, body, NULL, out);
}

/* ------------------------------------------------------------------------ */
/* Equality                                                                   */
/* ------------------------------------------------------------------------ */

static ct_status equal_rec(const ct_lambda *s, const ct_lambda *t,
                           uint64_t depth, bool *out) {
  bool r;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (s->kind != t->kind) {
    *out = false;
    return CT_OK;
  }
  if (s->kind == CT_LAMBDA_VAR) {
    *out = s->index == t->index;
    return CT_OK;
  }
  st = equal_rec(s->left, t->left, depth - 1, &r);
  if (st != CT_OK) {
    return st;
  }
  if (!r || s->kind == CT_LAMBDA_LAM) {
    *out = r;
    return CT_OK;
  }
  return equal_rec(s->right, t->right, depth - 1, out);
}

ct_status ct_lambda_equal(const ct_lambda *s, const ct_lambda *t,
                          uint64_t max_depth, bool *out) {
  return equal_rec(s, t, max_depth, out);
}

/* ------------------------------------------------------------------------ */
/* Lifting                                                                    */
/* ------------------------------------------------------------------------ */

/* `lift n k t`.  Unchanged variables are shared with `t`. */
static ct_status lift_rec(ct_arena *a, uint64_t n, uint64_t k,
                          const ct_lambda *t, uint64_t depth, uint64_t *budget,
                          const ct_lambda **out) {
  const ct_lambda *l;
  const ct_lambda *r;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (t->kind == CT_LAMBDA_VAR) {
    if (t->index < k) {
      *out = t;
      return CT_OK;
    }
    if (t->index > UINT64_MAX - n) {
      return CT_EOVERFLOW;
    }
    return mk_node(a, budget, CT_LAMBDA_VAR, t->index + n, NULL, NULL, out);
  }
  if (t->kind == CT_LAMBDA_APP) {
    st = lift_rec(a, n, k, t->left, depth - 1, budget, &l);
    if (st != CT_OK) {
      return st;
    }
    st = lift_rec(a, n, k, t->right, depth - 1, budget, &r);
    if (st != CT_OK) {
      return st;
    }
    return mk_node(a, budget, CT_LAMBDA_APP, 0, l, r, out);
  }
  if (k == UINT64_MAX) {
    return CT_EOVERFLOW;
  }
  st = lift_rec(a, n, k + 1, t->left, depth - 1, budget, &l);
  if (st != CT_OK) {
    return st;
  }
  return mk_node(a, budget, CT_LAMBDA_LAM, 0, l, NULL, out);
}

ct_status ct_lambda_lift(ct_arena *a, uint64_t n, uint64_t k,
                         const ct_lambda *t, const ct_lambda_limits *lim,
                         const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return lift_rec(a, n, k, t, lim->max_depth, &budget, out);
}

/* ------------------------------------------------------------------------ */
/* Substitution                                                               */
/* ------------------------------------------------------------------------ */

/*
 * `subst (lift d 0 s) x t`, for d <= x.  Under d binders, `subst s x0 t` is
 * `subst (lift d 0 s) (x0 + d) t`; the lifted copies of `s` are built only
 * where they are used.  Unchanged variables are shared with `t`.
 */
static ct_status subst_rec(ct_arena *a, const ct_lambda *s, uint64_t x,
                           uint64_t d, const ct_lambda *t, uint64_t depth,
                           uint64_t *budget, const ct_lambda **out) {
  const ct_lambda *l;
  const ct_lambda *r;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (t->kind == CT_LAMBDA_VAR) {
    if (t->index == x) {
      return lift_rec(a, d, 0, s, depth - 1, budget, out);
    }
    if (t->index > x) {
      return mk_node(a, budget, CT_LAMBDA_VAR, t->index - 1, NULL, NULL, out);
    }
    *out = t;
    return CT_OK;
  }
  if (t->kind == CT_LAMBDA_APP) {
    st = subst_rec(a, s, x, d, t->left, depth - 1, budget, &l);
    if (st != CT_OK) {
      return st;
    }
    st = subst_rec(a, s, x, d, t->right, depth - 1, budget, &r);
    if (st != CT_OK) {
      return st;
    }
    return mk_node(a, budget, CT_LAMBDA_APP, 0, l, r, out);
  }
  if (x == UINT64_MAX) {
    return CT_EOVERFLOW;
  }
  st = subst_rec(a, s, x + 1, d + 1, t->left, depth - 1, budget, &l);
  if (st != CT_OK) {
    return st;
  }
  return mk_node(a, budget, CT_LAMBDA_LAM, 0, l, NULL, out);
}

ct_status ct_lambda_subst(ct_arena *a, const ct_lambda *s, uint64_t x,
                          const ct_lambda *t, const ct_lambda_limits *lim,
                          const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return subst_rec(a, s, x, 0, t, lim->max_depth, &budget, out);
}

/* ------------------------------------------------------------------------ */
/* Size                                                                       */
/* ------------------------------------------------------------------------ */

static ct_status size_rec(const ct_lambda *t, uint64_t depth, uint64_t *out) {
  uint64_t sl;
  uint64_t sr;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (t->kind == CT_LAMBDA_VAR) {
    if (t->index == UINT64_MAX) {
      return CT_EOVERFLOW;
    }
    *out = t->index + 1;
    return CT_OK;
  }
  st = size_rec(t->left, depth - 1, &sl);
  if (st != CT_OK) {
    return st;
  }
  if (t->kind == CT_LAMBDA_LAM) {
    if (sl == UINT64_MAX) {
      return CT_EOVERFLOW;
    }
    *out = sl + 1;
    return CT_OK;
  }
  st = size_rec(t->right, depth - 1, &sr);
  if (st != CT_OK) {
    return st;
  }
  if (sl >= UINT64_MAX - sr) {
    return CT_EOVERFLOW;
  }
  *out = sl + sr + 1;
  return CT_OK;
}

ct_status ct_lambda_size(const ct_lambda *t, uint64_t max_depth,
                         uint64_t *out) {
  return size_rec(t, max_depth, out);
}

/* ------------------------------------------------------------------------ */
/* Church numerals                                                            */
/* ------------------------------------------------------------------------ */

ct_status ct_lambda_church(ct_arena *a, uint64_t n, const ct_lambda_limits *lim,
                           const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  uint64_t i;
  const ct_lambda *f;
  const ct_lambda *body;
  ct_status st;
  st = mk_node(a, &budget, CT_LAMBDA_VAR, 1, NULL, NULL, &f);
  if (st != CT_OK) {
    return st;
  }
  st = mk_node(a, &budget, CT_LAMBDA_VAR, 0, NULL, NULL, &body);
  if (st != CT_OK) {
    return st;
  }
  for (i = 0; i < n; i++) {
    st = mk_node(a, &budget, CT_LAMBDA_APP, 0, f, body, &body);
    if (st != CT_OK) {
      return st;
    }
  }
  st = mk_node(a, &budget, CT_LAMBDA_LAM, 0, body, NULL, &body);
  if (st != CT_OK) {
    return st;
  }
  return mk_node(a, &budget, CT_LAMBDA_LAM, 0, body, NULL, out);
}

/* ------------------------------------------------------------------------ */
/* Leftmost-outermost reduction                                               */
/* ------------------------------------------------------------------------ */

/*
 * One leftmost-outermost step.  On CT_OK, `*reduced` tells whether `t` has a
 * redex, and if so `*out` is the reduct (otherwise `*out` is not written).
 */
static ct_status step_rec(ct_arena *a, const ct_lambda *t, uint64_t depth,
                          uint64_t *budget, const ct_lambda **out,
                          bool *reduced) {
  const ct_lambda *u;
  bool red;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (t->kind == CT_LAMBDA_VAR) {
    *reduced = false;
    return CT_OK;
  }
  if (t->kind == CT_LAMBDA_LAM) {
    st = step_rec(a, t->left, depth - 1, budget, &u, &red);
    if (st != CT_OK) {
      return st;
    }
    if (!red) {
      *reduced = false;
      return CT_OK;
    }
    st = mk_node(a, budget, CT_LAMBDA_LAM, 0, u, NULL, out);
    if (st != CT_OK) {
      return st;
    }
    *reduced = true;
    return CT_OK;
  }
  /* An application: contract it if it is a redex, otherwise reduce in the
     function first and in the argument only if the function is normal. */
  if (t->left->kind == CT_LAMBDA_LAM) {
    st = subst_rec(a, t->right, 0, 0, t->left->left, depth - 1, budget, out);
    if (st != CT_OK) {
      return st;
    }
    *reduced = true;
    return CT_OK;
  }
  st = step_rec(a, t->left, depth - 1, budget, &u, &red);
  if (st != CT_OK) {
    return st;
  }
  if (red) {
    st = mk_node(a, budget, CT_LAMBDA_APP, 0, u, t->right, out);
    if (st != CT_OK) {
      return st;
    }
    *reduced = true;
    return CT_OK;
  }
  st = step_rec(a, t->right, depth - 1, budget, &u, &red);
  if (st != CT_OK) {
    return st;
  }
  if (!red) {
    *reduced = false;
    return CT_OK;
  }
  st = mk_node(a, budget, CT_LAMBDA_APP, 0, t->left, u, out);
  if (st != CT_OK) {
    return st;
  }
  *reduced = true;
  return CT_OK;
}

ct_status ct_lambda_step(ct_arena *a, const ct_lambda *t,
                         const ct_lambda_limits *lim, const ct_lambda **out,
                         bool *normal) {
  uint64_t budget = lim->max_nodes;
  const ct_lambda *u;
  bool red;
  ct_status st;
  st = step_rec(a, t, lim->max_depth, &budget, &u, &red);
  if (st != CT_OK) {
    return st;
  }
  if (red) {
    *out = u;
  } else {
    *out = t;
  }
  *normal = !red;
  return CT_OK;
}

/*
 * Whether `t` is a normal form (contains no beta-redex).  CT_ELIMIT if `t` is
 * deeper than `depth`.  It never allocates.  On CT_OK, `*out` is the answer.
 */
static ct_status normal_rec(const ct_lambda *t, uint64_t depth, bool *out) {
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (t->kind == CT_LAMBDA_VAR) {
    *out = true;
    return CT_OK;
  }
  if (t->kind == CT_LAMBDA_LAM) {
    return normal_rec(t->left, depth - 1, out);
  }
  if (t->left->kind == CT_LAMBDA_LAM) {
    *out = false;
    return CT_OK;
  }
  st = normal_rec(t->left, depth - 1, out);
  if (st != CT_OK) {
    return st;
  }
  if (!*out) {
    return CT_OK;
  }
  return normal_rec(t->right, depth - 1, out);
}

ct_status ct_lambda_normalize(ct_arena *a, const ct_lambda *t, uint64_t fuel,
                              const ct_lambda_limits *lim,
                              const ct_lambda **out, uint64_t *steps) {
  const ct_lambda *cur = t;
  const ct_lambda *next;
  uint64_t i = 0;
  uint64_t budget;
  bool red;
  bool nf;
  ct_status st;
  for (;;) {
    if (i == fuel) {
      /* The fuel is exhausted: no further step is computed, only a check
         that the current term is normal. */
      st = normal_rec(cur, lim->max_depth, &nf);
      if (st != CT_OK) {
        return st;
      }
      if (!nf) {
        return CT_ELIMIT;
      }
      *out = cur;
      *steps = i;
      return CT_OK;
    }
    budget = lim->max_nodes;
    st = step_rec(a, cur, lim->max_depth, &budget, &next, &red);
    if (st != CT_OK) {
      return st;
    }
    if (!red) {
      *out = cur;
      *steps = i;
      return CT_OK;
    }
    cur = next;
    i++;
  }
}
