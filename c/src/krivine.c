#include "ct/krivine.h"

/* ------------------------------------------------------------------------ */
/* Allocation helpers                                                         */
/* ------------------------------------------------------------------------ */

/* Charges one node to `*budget`; CT_ELIMIT when it is exhausted. */
static ct_status charge(uint64_t *budget) {
  if (*budget == 0) {
    return CT_ELIMIT;
  }
  *budget = *budget - 1;
  return CT_OK;
}

static ct_status mk_var(ct_arena *a, uint64_t *budget, uint64_t i,
                        const ct_lambda **out) {
  ct_status st = charge(budget);
  if (st != CT_OK) {
    return st;
  }
  return ct_lambda_var(a, i, out);
}

static ct_status mk_app(ct_arena *a, uint64_t *budget, const ct_lambda *f,
                        const ct_lambda *x, const ct_lambda **out) {
  ct_status st = charge(budget);
  if (st != CT_OK) {
    return st;
  }
  return ct_lambda_app(a, f, x, out);
}

static ct_status mk_lam(ct_arena *a, uint64_t *budget, const ct_lambda *body,
                        const ct_lambda **out) {
  ct_status st = charge(budget);
  if (st != CT_OK) {
    return st;
  }
  return ct_lambda_lam(a, body, out);
}

static ct_status mk_clos(ct_arena *a, uint64_t *budget, const ct_lambda *code,
                         const ct_kenv *env, const ct_kclos **out) {
  ct_status st = charge(budget);
  if (st != CT_OK) {
    return st;
  }
  return ct_kclos_mk(a, code, env, out);
}

static ct_status mk_cons(ct_arena *a, uint64_t *budget, const ct_kclos *head,
                         const ct_kenv *tail, const ct_kenv **out) {
  ct_status st = charge(budget);
  if (st != CT_OK) {
    return st;
  }
  return ct_kenv_cons(a, head, tail, out);
}

/* ------------------------------------------------------------------------ */
/* Closures and environments                                                  */
/* ------------------------------------------------------------------------ */

ct_status ct_kclos_mk(ct_arena *a, const ct_lambda *code, const ct_kenv *env,
                      const ct_kclos **out) {
  void *mem;
  ct_kclos *c;
  ct_status st = ct_arena_alloc(a, sizeof(ct_kclos), _Alignof(ct_kclos), &mem);
  if (st != CT_OK) {
    return st;
  }
  c = mem;
  c->code = code;
  c->env = env;
  *out = c;
  return CT_OK;
}

ct_status ct_kenv_cons(ct_arena *a, const ct_kclos *head, const ct_kenv *tail,
                       const ct_kenv **out) {
  void *mem;
  ct_kenv *e;
  ct_status st = ct_arena_alloc(a, sizeof(ct_kenv), _Alignof(ct_kenv), &mem);
  if (st != CT_OK) {
    return st;
  }
  e = mem;
  e->head = head;
  e->tail = tail;
  *out = e;
  return CT_OK;
}

/* ------------------------------------------------------------------------ */
/* The code table                                                             */
/* ------------------------------------------------------------------------ */

/* The number of nodes of `t` (`Lambda.nodes t`), added to `*n`. */
static ct_status count_rec(const ct_lambda *t, uint64_t depth, uint64_t *n) {
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (*n == UINT64_MAX) {
    return CT_EOVERFLOW;
  }
  *n = *n + 1;
  if (t->kind == CT_LAMBDA_VAR) {
    return CT_OK;
  }
  st = count_rec(t->left, depth - 1, n);
  if (st != CT_OK) {
    return st;
  }
  if (t->kind == CT_LAMBDA_LAM) {
    return CT_OK;
  }
  return count_rec(t->right, depth - 1, n);
}

/*
 * Appends the nodes of `t` to `nodes[0..*len-1]` (room is available: the
 * caller counted them) and writes the address of `t` to `*root`.
 */
static void fill_rec(const ct_lambda *t, ct_knode *nodes, uint64_t *len,
                     uint64_t *root) {
  uint64_t r1;
  uint64_t r2;
  if (t->kind == CT_LAMBDA_VAR) {
    nodes[*len].kind = CT_KNODE_VAR;
    nodes[*len].x = t->index;
    nodes[*len].y = 0;
  } else if (t->kind == CT_LAMBDA_APP) {
    fill_rec(t->left, nodes, len, &r1);
    fill_rec(t->right, nodes, len, &r2);
    nodes[*len].kind = CT_KNODE_APP;
    nodes[*len].x = r1;
    nodes[*len].y = r2;
  } else {
    fill_rec(t->left, nodes, len, &r1);
    nodes[*len].kind = CT_KNODE_LAM;
    nodes[*len].x = r1;
    nodes[*len].y = 0;
  }
  *root = *len;
  *len = *len + 1;
}

ct_status ct_krivine_flatten(ct_arena *a, const ct_lambda *t,
                             const ct_ktab *tab, uint64_t max_depth,
                             ct_ktab *out_tab, uint64_t *out_root) {
  uint64_t total = tab->len;
  uint64_t len = 0;
  uint64_t root;
  size_t n;
  void *mem;
  ct_knode *nodes;
  ct_status st = count_rec(t, max_depth, &total);
  if (st != CT_OK) {
    return st;
  }
  n = (size_t)total;
  if ((uint64_t)n != total) {
    return CT_EOVERFLOW;
  }
  st = ct_arena_alloc_array(a, n, sizeof(ct_knode), _Alignof(ct_knode), &mem);
  if (st != CT_OK) {
    return st;
  }
  nodes = mem;
  while (len < tab->len) {
    nodes[len].kind = tab->nodes[len].kind;
    nodes[len].x = tab->nodes[len].x;
    nodes[len].y = tab->nodes[len].y;
    len = len + 1;
  }
  fill_rec(t, nodes, &len, &root);
  out_tab->len = len;
  out_tab->nodes = nodes;
  *out_root = root;
  return CT_OK;
}

ct_status ct_krivine_tab_of(ct_arena *a, const ct_lambda *t,
                            uint64_t max_depth, ct_ktab *out_tab,
                            uint64_t *out_root) {
  ct_ktab empty;
  empty.len = 0;
  empty.nodes = NULL;
  return ct_krivine_flatten(a, t, &empty, max_depth, out_tab, out_root);
}

/* `decTermF tab fuel p`. */
static ct_status dec_term_rec(ct_arena *a, const ct_ktab *tab, uint64_t fuel,
                              uint64_t p, uint64_t depth, uint64_t *budget,
                              const ct_lambda **out) {
  const ct_lambda *l;
  const ct_lambda *r;
  ct_status st;
  if (fuel == 0 || p >= tab->len) {
    return mk_var(a, budget, 0, out);
  }
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (tab->nodes[p].kind == CT_KNODE_VAR) {
    return mk_var(a, budget, tab->nodes[p].x, out);
  }
  st = dec_term_rec(a, tab, fuel - 1, tab->nodes[p].x, depth - 1, budget, &l);
  if (st != CT_OK) {
    return st;
  }
  if (tab->nodes[p].kind == CT_KNODE_LAM) {
    return mk_lam(a, budget, l, out);
  }
  st = dec_term_rec(a, tab, fuel - 1, tab->nodes[p].y, depth - 1, budget, &r);
  if (st != CT_OK) {
    return st;
  }
  return mk_app(a, budget, l, r, out);
}

/* `decTerm tab p = decTermF tab (p + 1) p`. */
static ct_status dec_term_at(ct_arena *a, const ct_ktab *tab, uint64_t p,
                             uint64_t depth, uint64_t *budget,
                             const ct_lambda **out) {
  if (p >= tab->len) {
    /* decTermF tab (p + 1) p reads no node: the result is `var 0`. */
    return mk_var(a, budget, 0, out);
  }
  return dec_term_rec(a, tab, p + 1, p, depth, budget, out);
}

ct_status ct_krivine_dec_term_f(ct_arena *a, const ct_ktab *tab, uint64_t fuel,
                                uint64_t p, const ct_lambda_limits *lim,
                                const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return dec_term_rec(a, tab, fuel, p, lim->max_depth, &budget, out);
}

ct_status ct_krivine_dec_term(ct_arena *a, const ct_ktab *tab, uint64_t p,
                              const ct_lambda_limits *lim,
                              const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return dec_term_at(a, tab, p, lim->max_depth, &budget, out);
}

/* ------------------------------------------------------------------------ */
/* The heap                                                                   */
/* ------------------------------------------------------------------------ */

static ct_status dec_env_rec(ct_arena *a, const ct_ktab *tab,
                             const ct_kcell *heap, uint64_t heap_len,
                             uint64_t fuel, bool has_e, uint64_t e,
                             uint64_t depth, uint64_t *budget,
                             const ct_kenv **out);

/* `decClF tab heap fuel p`. */
static ct_status dec_clos_rec(ct_arena *a, const ct_ktab *tab,
                              const ct_kcell *heap, uint64_t heap_len,
                              uint64_t fuel, uint64_t p, uint64_t depth,
                              uint64_t *budget, const ct_kclos **out) {
  const ct_lambda *code;
  const ct_kenv *env;
  ct_status st;
  if (fuel == 0 || p >= heap_len || heap[p].kind != CT_KCELL_CLOS) {
    st = mk_var(a, budget, 0, &code);
    if (st != CT_OK) {
      return st;
    }
    return mk_clos(a, budget, code, NULL, out);
  }
  if (depth == 0) {
    return CT_ELIMIT;
  }
  st = dec_term_at(a, tab, heap[p].x, depth - 1, budget, &code);
  if (st != CT_OK) {
    return st;
  }
  st = dec_env_rec(a, tab, heap, heap_len, fuel - 1, heap[p].has_y, heap[p].y,
                   depth - 1, budget, &env);
  if (st != CT_OK) {
    return st;
  }
  return mk_clos(a, budget, code, env, out);
}

/* `decEnvF tab heap fuel e`, where `e` is `some e` if `has_e`. */
static ct_status dec_env_rec(ct_arena *a, const ct_ktab *tab,
                             const ct_kcell *heap, uint64_t heap_len,
                             uint64_t fuel, bool has_e, uint64_t e,
                             uint64_t depth, uint64_t *budget,
                             const ct_kenv **out) {
  const ct_kclos *c;
  const ct_kenv *rest;
  ct_status st;
  if (fuel == 0 || !has_e || e >= heap_len || heap[e].kind != CT_KCELL_CONS) {
    *out = NULL;
    return CT_OK;
  }
  if (depth == 0) {
    return CT_ELIMIT;
  }
  st = dec_clos_rec(a, tab, heap, heap_len, fuel - 1, heap[e].x, depth - 1,
                    budget, &c);
  if (st != CT_OK) {
    return st;
  }
  st = dec_env_rec(a, tab, heap, heap_len, fuel - 1, heap[e].has_y, heap[e].y,
                   depth - 1, budget, &rest);
  if (st != CT_OK) {
    return st;
  }
  return mk_cons(a, budget, c, rest, out);
}

ct_status ct_krivine_dec_clos_f(ct_arena *a, const ct_ktab *tab,
                                const ct_kcell *heap, uint64_t heap_len,
                                uint64_t fuel, uint64_t p,
                                const ct_lambda_limits *lim,
                                const ct_kclos **out) {
  uint64_t budget = lim->max_nodes;
  return dec_clos_rec(a, tab, heap, heap_len, fuel, p, lim->max_depth, &budget,
                      out);
}

ct_status ct_krivine_dec_env_f(ct_arena *a, const ct_ktab *tab,
                               const ct_kcell *heap, uint64_t heap_len,
                               uint64_t fuel, bool has_e, uint64_t e,
                               const ct_lambda_limits *lim,
                               const ct_kenv **out) {
  uint64_t budget = lim->max_nodes;
  return dec_env_rec(a, tab, heap, heap_len, fuel, has_e, e, lim->max_depth,
                     &budget, out);
}

ct_status ct_krivine_dec_clos(ct_arena *a, const ct_ktab *tab,
                              const ct_kcell *heap, uint64_t heap_len,
                              uint64_t p, const ct_lambda_limits *lim,
                              const ct_kclos **out) {
  return ct_krivine_dec_clos_f(a, tab, heap, heap_len, heap_len, p, lim, out);
}

ct_status ct_krivine_dec_env(ct_arena *a, const ct_ktab *tab,
                             const ct_kcell *heap, uint64_t heap_len,
                             bool has_e, uint64_t e,
                             const ct_lambda_limits *lim, const ct_kenv **out) {
  return ct_krivine_dec_env_f(a, tab, heap, heap_len, heap_len, has_e, e, lim,
                              out);
}

bool ct_krivine_env_nth(const ct_kcell *heap, uint64_t heap_len, bool has_e,
                        uint64_t e, uint64_t n, uint64_t *out) {
  while (has_e && e < heap_len && heap[e].kind == CT_KCELL_CONS) {
    if (n == 0) {
      *out = heap[e].x;
      return true;
    }
    has_e = heap[e].has_y;
    e = heap[e].y;
    n = n - 1;
  }
  return false;
}

ct_status ct_krivine_dec_state(ct_arena *a, const ct_ktab *tab,
                               const ct_khstate *s,
                               const ct_lambda_limits *lim, ct_kstate *out) {
  uint64_t budget = lim->max_nodes;
  uint64_t i = 0;
  const ct_lambda *code;
  const ct_kenv *env;
  const ct_kenv *stack = NULL;
  const ct_kclos *c;
  ct_status st = dec_term_at(a, tab, s->code, lim->max_depth, &budget, &code);
  if (st != CT_OK) {
    return st;
  }
  st = dec_env_rec(a, tab, s->heap, s->heap_len, s->heap_len, s->has_env,
                   s->env, lim->max_depth, &budget, &env);
  if (st != CT_OK) {
    return st;
  }
  /* The bottom of the stack is consed first, so the top ends up first. */
  while (i < s->stack_len) {
    st = dec_clos_rec(a, tab, s->heap, s->heap_len, s->heap_len, s->stack[i],
                      lim->max_depth, &budget, &c);
    if (st != CT_OK) {
      return st;
    }
    st = mk_cons(a, &budget, c, stack, &stack);
    if (st != CT_OK) {
      return st;
    }
    i = i + 1;
  }
  out->code = code;
  out->env = env;
  out->stack = stack;
  return CT_OK;
}

ct_status ct_krivine_init_state(const ct_lambda *t, uint64_t max_depth,
                                ct_kcell *heap, uint64_t heap_cap,
                                uint64_t *stack, uint64_t stack_cap,
                                ct_khstate *out) {
  uint64_t n = 0;
  ct_status st = count_rec(t, max_depth, &n);
  if (st != CT_OK) {
    return st;
  }
  /* The root of `flatten t []` is its last node. */
  out->code = n - 1;
  out->has_env = false;
  out->env = 0;
  out->stack_len = 0;
  out->stack_cap = stack_cap;
  out->stack = stack;
  out->heap_len = 0;
  out->heap_cap = heap_cap;
  out->heap = heap;
  return CT_OK;
}

ct_status ct_krivine_hstep(const ct_ktab *tab, ct_khstate *s, bool *stuck,
                           int *label) {
  uint64_t code = s->code;
  uint64_t q;
  if (code >= tab->len) {
    *stuck = true;
    return CT_OK;
  }
  if (tab->nodes[code].kind == CT_KNODE_APP) {
    if (s->heap_len >= s->heap_cap || s->stack_len >= s->stack_cap) {
      return CT_ELIMIT;
    }
    s->heap[s->heap_len].kind = CT_KCELL_CLOS;
    s->heap[s->heap_len].x = tab->nodes[code].y;
    s->heap[s->heap_len].has_y = s->has_env;
    s->heap[s->heap_len].y = s->env;
    s->stack[s->stack_len] = s->heap_len;
    s->stack_len = s->stack_len + 1;
    s->heap_len = s->heap_len + 1;
    s->code = tab->nodes[code].x;
    *stuck = false;
    *label = CT_KRIVINE_APP;
    return CT_OK;
  }
  if (tab->nodes[code].kind == CT_KNODE_LAM) {
    if (s->stack_len == 0) {
      *stuck = true;
      return CT_OK;
    }
    if (s->heap_len >= s->heap_cap) {
      return CT_ELIMIT;
    }
    s->heap[s->heap_len].kind = CT_KCELL_CONS;
    s->heap[s->heap_len].x = s->stack[s->stack_len - 1];
    s->heap[s->heap_len].has_y = s->has_env;
    s->heap[s->heap_len].y = s->env;
    s->has_env = true;
    s->env = s->heap_len;
    s->stack_len = s->stack_len - 1;
    s->heap_len = s->heap_len + 1;
    s->code = tab->nodes[code].x;
    *stuck = false;
    *label = CT_KRIVINE_BETA;
    return CT_OK;
  }
  if (!ct_krivine_env_nth(s->heap, s->heap_len, s->has_env, s->env,
                          tab->nodes[code].x, &q) ||
      q >= s->heap_len || s->heap[q].kind != CT_KCELL_CLOS) {
    *stuck = true;
    return CT_OK;
  }
  s->code = s->heap[q].x;
  s->has_env = s->heap[q].has_y;
  s->env = s->heap[q].y;
  *stuck = false;
  *label = CT_KRIVINE_VAR;
  return CT_OK;
}

/* ------------------------------------------------------------------------ */
/* Decoding a state into a term                                               */
/* ------------------------------------------------------------------------ */

static ct_status unfold_env_rec(ct_arena *a, const ct_kenv *e, uint64_t i,
                                uint64_t depth, uint64_t *budget,
                                const ct_lambda_limits *lim,
                                const ct_lambda **out);

/*
 * `substEnv (envCons^[d] (unfoldEnv e)) t`: the parallel substitution of the
 * environment `e` under `d` binders.  Below the binders a variable `n < d` is
 * left alone; a variable `n >= d` becomes `lift d 0 (unfoldEnv e (n - d))`.
 */
static ct_status subst_env_rec(ct_arena *a, const ct_lambda *t,
                               const ct_kenv *e, uint64_t d, uint64_t depth,
                               uint64_t *budget, const ct_lambda_limits *lim,
                               const ct_lambda **out) {
  const ct_lambda *l;
  const ct_lambda *r;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (t->kind == CT_LAMBDA_VAR) {
    if (t->index < d) {
      *out = t;
      return CT_OK;
    }
    st = unfold_env_rec(a, e, t->index - d, depth - 1, budget, lim, &l);
    if (st != CT_OK) {
      return st;
    }
    if (d == 0) {
      *out = l;
      return CT_OK;
    }
    return ct_lambda_lift(a, d, 0, l, lim, out);
  }
  if (t->kind == CT_LAMBDA_APP) {
    st = subst_env_rec(a, t->left, e, d, depth - 1, budget, lim, &l);
    if (st != CT_OK) {
      return st;
    }
    st = subst_env_rec(a, t->right, e, d, depth - 1, budget, lim, &r);
    if (st != CT_OK) {
      return st;
    }
    return mk_app(a, budget, l, r, out);
  }
  if (d == UINT64_MAX) {
    return CT_EOVERFLOW;
  }
  st = subst_env_rec(a, t->left, e, d + 1, depth - 1, budget, lim, &l);
  if (st != CT_OK) {
    return st;
  }
  return mk_lam(a, budget, l, out);
}

/* `unfoldEnv e i`. */
static ct_status unfold_env_rec(ct_arena *a, const ct_kenv *e, uint64_t i,
                                uint64_t depth, uint64_t *budget,
                                const ct_lambda_limits *lim,
                                const ct_lambda **out) {
  while (e != NULL && i != 0) {
    e = e->tail;
    i = i - 1;
  }
  if (e == NULL) {
    return mk_var(a, budget, i, out);
  }
  if (depth == 0) {
    return CT_ELIMIT;
  }
  return subst_env_rec(a, e->head->code, e->head->env, 0, depth - 1, budget,
                       lim, out);
}

ct_status ct_krivine_unfold(ct_arena *a, const ct_kclos *c,
                            const ct_lambda_limits *lim,
                            const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return subst_env_rec(a, c->code, c->env, 0, lim->max_depth, &budget, lim,
                       out);
}

ct_status ct_krivine_unfold_env(ct_arena *a, const ct_kenv *e, uint64_t i,
                                const ct_lambda_limits *lim,
                                const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return unfold_env_rec(a, e, i, lim->max_depth, &budget, lim, out);
}

/* `spine t stack`, charging the nodes built to `*budget`. */
static ct_status spine_loop(ct_arena *a, const ct_lambda *t,
                            const ct_kenv *stack, uint64_t *budget,
                            const ct_lambda_limits *lim,
                            const ct_lambda **out) {
  const ct_lambda *acc = t;
  const ct_lambda *u;
  ct_status st;
  while (stack != NULL) {
    st = subst_env_rec(a, stack->head->code, stack->head->env, 0,
                       lim->max_depth, budget, lim, &u);
    if (st != CT_OK) {
      return st;
    }
    st = mk_app(a, budget, acc, u, &acc);
    if (st != CT_OK) {
      return st;
    }
    stack = stack->tail;
  }
  *out = acc;
  return CT_OK;
}

ct_status ct_krivine_spine(ct_arena *a, const ct_lambda *t,
                           const ct_kenv *stack, const ct_lambda_limits *lim,
                           const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  return spine_loop(a, t, stack, &budget, lim, out);
}

ct_status ct_krivine_state_decode(ct_arena *a, const ct_kstate *s,
                                  const ct_lambda_limits *lim,
                                  const ct_lambda **out) {
  uint64_t budget = lim->max_nodes;
  const ct_lambda *u;
  ct_status st = subst_env_rec(a, s->code, s->env, 0, lim->max_depth, &budget,
                               lim, &u);
  if (st != CT_OK) {
    return st;
  }
  return spine_loop(a, u, s->stack, &budget, lim, out);
}
