#include "ct/cob.h"

#include <string.h>

static ct_status mk_node(ct_arena *a, int kind, bool bit, uint64_t index,
                         const ct_cob *f, const ct_cob *h0, const ct_cob *h1,
                         const ct_cob *bd, uint64_t ngs,
                         const ct_cob *const *gs, const ct_cob **out) {
  void *mem;
  ct_cob *node;
  ct_status st;
  st = ct_arena_alloc(a, sizeof(ct_cob), _Alignof(ct_cob), &mem);
  if (st != CT_OK) {
    return st;
  }
  node = mem;
  node->kind = kind;
  node->bit = bit;
  node->index = index;
  node->f = f;
  node->h0 = h0;
  node->h1 = h1;
  node->bd = bd;
  node->ngs = ngs;
  node->gs = gs;
  *out = node;
  return CT_OK;
}

ct_status ct_cob_proj(ct_arena *a, uint64_t i, const ct_cob **out) {
  return mk_node(a, CT_COB_PROJ, false, i, NULL, NULL, NULL, NULL, 0, NULL,
                 out);
}

ct_status ct_cob_empty(ct_arena *a, const ct_cob **out) {
  return mk_node(a, CT_COB_EMPTY, false, 0, NULL, NULL, NULL, NULL, 0, NULL,
                 out);
}

ct_status ct_cob_app(ct_arena *a, bool b, const ct_cob **out) {
  return mk_node(a, CT_COB_APP, b, 0, NULL, NULL, NULL, NULL, 0, NULL, out);
}

ct_status ct_cob_smash(ct_arena *a, const ct_cob **out) {
  return mk_node(a, CT_COB_SMASH, false, 0, NULL, NULL, NULL, NULL, 0, NULL,
                 out);
}

ct_status ct_cob_comp(ct_arena *a, const ct_cob *f, const ct_cob *const *gs,
                      uint64_t ngs, const ct_cob **out) {
  size_t cnt = (size_t)ngs;
  void *mem;
  const ct_cob **copy;
  ct_status st;
  if (ngs == 0) {
    return mk_node(a, CT_COB_COMP, false, 0, f, NULL, NULL, NULL, 0, NULL,
                   out);
  }
  if ((uint64_t)cnt != ngs) {
    return CT_EOVERFLOW;
  }
  st = ct_arena_alloc_array(a, cnt, sizeof(const ct_cob *),
                            _Alignof(const ct_cob *), &mem);
  if (st != CT_OK) {
    return st;
  }
  copy = mem;
  memcpy(copy, gs, cnt * sizeof(const ct_cob *));
  return mk_node(a, CT_COB_COMP, false, 0, f, NULL, NULL, NULL, ngs, copy,
                 out);
}

ct_status ct_cob_brec(ct_arena *a, const ct_cob *g, const ct_cob *h0,
                      const ct_cob *h1, const ct_cob *bd, const ct_cob **out) {
  return mk_node(a, CT_COB_BREC, false, 0, g, h0, h1, bd, 0, NULL, out);
}

/* ------------------------------------------------------------------------ */
/* Evaluation                                                                 */
/* ------------------------------------------------------------------------ */

static ct_status eval_rec(ct_arena *a, const ct_cob *c, const ct_vec *args,
                          uint64_t depth, uint64_t max_len, uint64_t *work,
                          ct_word *out);

/*
 * `f.eval (gs.map (·.eval args))`.  The vector of the values of the gs is
 * built from the last one to the first.
 */
static ct_status eval_comp(ct_arena *a, const ct_cob *c, const ct_vec *args,
                           uint64_t depth, uint64_t max_len, uint64_t *work,
                           ct_word *out) {
  ct_vec v;
  ct_vec v2;
  ct_word w;
  uint64_t i = c->ngs;
  ct_status st;
  v.len = 0;
  v.items = NULL;
  while (i > 0) {
    i--;
    st = eval_rec(a, c->gs[i], args, depth, max_len, work, &w);
    if (st != CT_OK) {
      return st;
    }
    st = ct_vec_cons(a, &w, &v, &v2);
    if (st != CT_OK) {
      return st;
    }
    v = v2;
  }
  return eval_rec(a, c->f, &v, depth, max_len, work, out);
}

/*
 * Bounded recursion on notation, on the first argument x.  The value on the
 * suffix `x.drop j` is computed for j = x.length, ..., 1, 0:
 *   value on []        = g.eval args.tail
 *   value on (b :: x') = ((if b then h₁ else h₀).eval (x' :: ih :: args.tail))
 *                          .take (bd.eval ((b :: x') :: args.tail)).length
 * where ih is the value on x'.
 */
static ct_status eval_brec(ct_arena *a, const ct_cob *c, const ct_vec *args,
                           uint64_t depth, uint64_t max_len, uint64_t *work,
                           ct_word *out) {
  ct_word x;
  ct_word r;
  ct_word xs;
  ct_word suffix;
  ct_word h;
  ct_word bound;
  ct_vec rest;
  ct_vec v1;
  ct_vec v2;
  ct_vec v3;
  uint64_t j;
  bool b;
  ct_status st;
  ct_vec_get(args, 0, &x);
  ct_vec_tail(args, &rest);
  st = eval_rec(a, c->f, &rest, depth, max_len, work, &r);
  if (st != CT_OK) {
    return st;
  }
  j = x.len;
  while (j > 0) {
    j--;
    ct_word_drop(&x, j + 1, &xs);
    st = ct_vec_cons(a, &r, &rest, &v1);
    if (st != CT_OK) {
      return st;
    }
    st = ct_vec_cons(a, &xs, &v1, &v2);
    if (st != CT_OK) {
      return st;
    }
    st = ct_word_get(&x, j, &b);
    if (st != CT_OK) {
      return st;
    }
    if (b) {
      st = eval_rec(a, c->h1, &v2, depth, max_len, work, &h);
    } else {
      st = eval_rec(a, c->h0, &v2, depth, max_len, work, &h);
    }
    if (st != CT_OK) {
      return st;
    }
    ct_word_drop(&x, j, &suffix);
    st = ct_vec_cons(a, &suffix, &rest, &v3);
    if (st != CT_OK) {
      return st;
    }
    st = eval_rec(a, c->bd, &v3, depth, max_len, work, &bound);
    if (st != CT_OK) {
      return st;
    }
    ct_word_take(&h, bound.len, &r);
  }
  *out = r;
  return CT_OK;
}

static ct_status eval_rec(ct_arena *a, const ct_cob *c, const ct_vec *args,
                          uint64_t depth, uint64_t max_len, uint64_t *work,
                          ct_word *out) {
  ct_word x;
  ct_word y;
  uint64_t n;
  ct_status st;
  if (depth == 0 || *work == 0) {
    return CT_ELIMIT;
  }
  *work = *work - 1;
  if (c->kind == CT_COB_PROJ) {
    ct_vec_get(args, c->index, &x);
    if (x.len > max_len) {
      return CT_ELIMIT;
    }
    *out = x;
    return CT_OK;
  }
  if (c->kind == CT_COB_EMPTY) {
    ct_word_empty(out);
    return CT_OK;
  }
  if (c->kind == CT_COB_APP) {
    ct_vec_get(args, 0, &x);
    if (x.len >= max_len) {
      return CT_ELIMIT;
    }
    return ct_word_cons(a, c->bit, &x, out);
  }
  if (c->kind == CT_COB_SMASH) {
    ct_vec_get(args, 0, &x);
    ct_vec_get(args, 1, &y);
    st = ct_u64_mul(x.len, y.len, &n);
    if (st != CT_OK) {
      return st;
    }
    if (n > max_len) {
      return CT_ELIMIT;
    }
    return ct_word_replicate(a, n, true, out);
  }
  if (c->kind == CT_COB_COMP) {
    return eval_comp(a, c, args, depth - 1, max_len, work, out);
  }
  return eval_brec(a, c, args, depth - 1, max_len, work, out);
}

ct_status ct_cob_eval(ct_arena *a, const ct_cob *c, const ct_vec *args,
                      const ct_cob_limits *lim, ct_word *out) {
  uint64_t work = lim->max_work;
  return eval_rec(a, c, args, lim->max_depth, lim->max_len, &work, out);
}
