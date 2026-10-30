#include "ct/cbv.h"

/* ------------------------------------------------------------------------ */
/* Continuations                                                              */
/* ------------------------------------------------------------------------ */

static ct_status mk_frame(ct_arena *a, int kind, const ct_lambda *u,
                          const ct_kenv *e, const ct_kclos *c,
                          const ct_cek_cont *tail, const ct_cek_cont **out) {
  void *mem;
  ct_cek_cont *k;
  ct_status st =
      ct_arena_alloc(a, sizeof(ct_cek_cont), _Alignof(ct_cek_cont), &mem);
  if (st != CT_OK) {
    return st;
  }
  k = mem;
  k->kind = kind;
  k->u = u;
  k->e = e;
  k->c = c;
  k->tail = tail;
  *out = k;
  return CT_OK;
}

ct_status ct_cek_cont_arg(ct_arena *a, const ct_lambda *u, const ct_kenv *e,
                          const ct_cek_cont *tail, const ct_cek_cont **out) {
  return mk_frame(a, CT_CEK_ARG, u, e, NULL, tail, out);
}

ct_status ct_cek_cont_fn(ct_arena *a, const ct_kclos *c,
                         const ct_cek_cont *tail, const ct_cek_cont **out) {
  return mk_frame(a, CT_CEK_FN, NULL, NULL, c, tail, out);
}

/* ------------------------------------------------------------------------ */
/* The machine                                                                */
/* ------------------------------------------------------------------------ */

ct_status ct_cek_init(const ct_lambda *t, ct_cek_state *out) {
  out->kind = CT_CEK_EVAL;
  out->t = t;
  out->e = NULL;
  out->c = NULL;
  out->k = NULL;
  return CT_OK;
}

/* `e[n]?`: the closure at position `n` of `e`, or NULL if there is none. */
static const ct_kclos *env_get(const ct_kenv *e, uint64_t n) {
  while (e != NULL && n > 0) {
    e = e->tail;
    n = n - 1;
  }
  if (e == NULL) {
    return NULL;
  }
  return e->head;
}

ct_status ct_cek_step(ct_arena *a, const ct_cek_state *s, bool *halted,
                      ct_cek_state *out) {
  ct_status st;
  if (s->kind == CT_CEK_EVAL) {
    const ct_lambda *t = s->t;
    if (t->kind == CT_LAMBDA_APP) {
      /* eval (app t u) e k  ↦  eval t e (arg u e :: k) */
      const ct_cek_cont *k2;
      st = mk_frame(a, CT_CEK_ARG, t->right, s->e, NULL, s->k, &k2);
      if (st != CT_OK) {
        return st;
      }
      out->kind = CT_CEK_EVAL;
      out->t = t->left;
      out->e = s->e;
      out->c = NULL;
      out->k = k2;
    } else if (t->kind == CT_LAMBDA_LAM) {
      /* eval (lam t) e k  ↦  ret (Clos.mk (lam t) e) k */
      const ct_kclos *c;
      st = ct_kclos_mk(a, t, s->e, &c);
      if (st != CT_OK) {
        return st;
      }
      out->kind = CT_CEK_RET;
      out->t = NULL;
      out->e = NULL;
      out->c = c;
      out->k = s->k;
    } else {
      /* eval (var n) e k  ↦  ret c k  if e[n]? = some c,
                              ret (Clos.mk (var n) e) k  otherwise */
      const ct_kclos *c = env_get(s->e, t->index);
      if (c == NULL) {
        st = ct_kclos_mk(a, t, s->e, &c);
        if (st != CT_OK) {
          return st;
        }
      }
      out->kind = CT_CEK_RET;
      out->t = NULL;
      out->e = NULL;
      out->c = c;
      out->k = s->k;
    }
    *halted = false;
    return CT_OK;
  }
  /* s = ret c k */
  if (s->k == NULL) {
    /* ret _ []  ↦  none */
    *halted = true;
    return CT_OK;
  }
  if (s->k->kind == CT_CEK_ARG) {
    /* ret c (arg u e :: k)  ↦  eval u e (fn c :: k) */
    const ct_cek_cont *k2;
    st = mk_frame(a, CT_CEK_FN, NULL, NULL, s->c, s->k->tail, &k2);
    if (st != CT_OK) {
      return st;
    }
    out->kind = CT_CEK_EVAL;
    out->t = s->k->u;
    out->e = s->k->e;
    out->c = NULL;
    out->k = k2;
    *halted = false;
    return CT_OK;
  }
  /* s = ret v (fn f :: k) */
  if (s->k->c->code->kind == CT_LAMBDA_LAM) {
    /* ret v (fn (Clos.mk (lam t) e) :: k)  ↦  eval t (v :: e) k */
    const ct_kenv *e2;
    st = ct_kenv_cons(a, s->c, s->k->c->env, &e2);
    if (st != CT_OK) {
      return st;
    }
    out->kind = CT_CEK_EVAL;
    out->t = s->k->c->code->left;
    out->e = e2;
    out->c = NULL;
    out->k = s->k->tail;
    *halted = false;
    return CT_OK;
  }
  /* the function value is not an abstraction  ↦  none */
  *halted = true;
  return CT_OK;
}

ct_status ct_cek_beta_count(int label, uint64_t *out) {
  if (label == CT_CEK_ADMIN) {
    *out = 0;
    return CT_OK;
  }
  if (label == CT_CEK_BETA) {
    *out = 1;
    return CT_OK;
  }
  return CT_EINVAL;
}

/* ------------------------------------------------------------------------ */
/* Decoding a state                                                           */
/* ------------------------------------------------------------------------ */

/* `plug k m`, charging the application nodes built to `*budget`. */
static ct_status plug_loop(ct_arena *a, const ct_cek_cont *k,
                           const ct_lambda *m, uint64_t *budget,
                           const ct_lambda_limits *lim,
                           const ct_lambda **out) {
  const ct_lambda *acc = m;
  const ct_lambda *v;
  ct_status st;
  while (k != NULL) {
    if (k->kind == CT_CEK_ARG) {
      ct_kclos c;
      c.code = k->u;
      c.env = k->e;
      st = ct_krivine_unfold(a, &c, lim, &v);
      if (st != CT_OK) {
        return st;
      }
      if (*budget == 0) {
        return CT_ELIMIT;
      }
      *budget = *budget - 1;
      st = ct_lambda_app(a, acc, v, &acc);
    } else {
      st = ct_krivine_unfold(a, k->c, lim, &v);
      if (st != CT_OK) {
        return st;
      }
      if (*budget == 0) {
        return CT_ELIMIT;
      }
      *budget = *budget - 1;
      st = ct_lambda_app(a, v, acc, &acc);
    }
    if (st != CT_OK) {
      return st;
    }
    k = k->tail;
  }
  *out = acc;
  return CT_OK;
}

ct_status ct_cek_plug(ct_arena *a, const ct_cek_cont *k, const ct_lambda *m,
                      const ct_lambda_limits *lim, const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return plug_loop(a, k, m, &budget, lim, out);
}

ct_status ct_cek_decode(ct_arena *a, const ct_cek_state *s,
                        const ct_lambda_limits *lim, const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  const ct_lambda *m;
  ct_status st;
  if (s->kind == CT_CEK_EVAL) {
    ct_kclos c;
    c.code = s->t;
    c.env = s->e;
    st = ct_krivine_unfold(a, &c, lim, &m);
  } else {
    st = ct_krivine_unfold(a, s->c, lim, &m);
  }
  if (st != CT_OK) {
    return st;
  }
  return plug_loop(a, s->k, m, &budget, lim, out);
}

/* ------------------------------------------------------------------------ */
/* The measure                                                                */
/* ------------------------------------------------------------------------ */

/* `*acc + 3 * size t + extra`, checked. */
static ct_status add_weight(const ct_lambda *t, uint64_t extra,
                            uint64_t max_depth, uint64_t *acc) {
  uint64_t n;
  ct_status st = ct_lambda_size(t, max_depth, &n);
  if (st != CT_OK) {
    return st;
  }
  st = ct_u64_mul(3, n, &n);
  if (st != CT_OK) {
    return st;
  }
  st = ct_u64_add(n, extra, &n);
  if (st != CT_OK) {
    return st;
  }
  return ct_u64_add(*acc, n, acc);
}

ct_status ct_cek_kweight(const ct_cek_cont *k, uint64_t max_depth,
                         uint64_t *out) {
  uint64_t acc = 0;
  ct_status st;
  while (k != NULL) {
    if (k->kind == CT_CEK_ARG) {
      st = add_weight(k->u, 2, max_depth, &acc);
      if (st != CT_OK) {
        return st;
      }
    }
    k = k->tail;
  }
  *out = acc;
  return CT_OK;
}

ct_status ct_cek_measure(const ct_cek_state *s, uint64_t max_depth,
                         uint64_t *out) {
  uint64_t acc;
  ct_status st = ct_cek_kweight(s->k, max_depth, &acc);
  if (st != CT_OK) {
    return st;
  }
  if (s->kind == CT_CEK_EVAL) {
    st = add_weight(s->t, 0, max_depth, &acc);
    if (st != CT_OK) {
      return st;
    }
  }
  *out = acc;
  return CT_OK;
}
