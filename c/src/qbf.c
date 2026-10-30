#include "ct/qbf.h"

static ct_status mk_node(ct_arena *a, int kind, uint64_t var,
                         const ct_qbf *left, const ct_qbf *right,
                         const ct_qbf **out) {
  void *mem;
  ct_qbf *node;
  ct_status st;
  st = ct_arena_alloc(a, sizeof(ct_qbf), _Alignof(ct_qbf), &mem);
  if (st != CT_OK) {
    return st;
  }
  node = mem;
  node->kind = kind;
  node->var = var;
  node->left = left;
  node->right = right;
  *out = node;
  return CT_OK;
}

ct_status ct_qbf_var(ct_arena *a, uint64_t i, const ct_qbf **out) {
  return mk_node(a, CT_QBF_VAR, i, NULL, NULL, out);
}

ct_status ct_qbf_neg(ct_arena *a, const ct_qbf *p, const ct_qbf **out) {
  return mk_node(a, CT_QBF_NEG, 0, p, NULL, out);
}

ct_status ct_qbf_conj(ct_arena *a, const ct_qbf *p, const ct_qbf *q,
                      const ct_qbf **out) {
  return mk_node(a, CT_QBF_CONJ, 0, p, q, out);
}

ct_status ct_qbf_disj(ct_arena *a, const ct_qbf *p, const ct_qbf *q,
                      const ct_qbf **out) {
  return mk_node(a, CT_QBF_DISJ, 0, p, q, out);
}

ct_status ct_qbf_all(ct_arena *a, uint64_t i, const ct_qbf *p,
                     const ct_qbf **out) {
  return mk_node(a, CT_QBF_ALL, i, p, NULL, out);
}

ct_status ct_qbf_ex(ct_arena *a, uint64_t i, const ct_qbf *p,
                    const ct_qbf **out) {
  return mk_node(a, CT_QBF_EX, i, p, NULL, out);
}

/*
 * The assignment seen by a subformula is the caller's assignment updated by
 * the quantifiers above it: a list of bindings, innermost first, each living
 * in the stack frame of its quantifier.
 */
struct binding {
  uint64_t var;
  bool val;
  const struct binding *next;
};

/* σ i, for σ = the assignment `assign`/`n` updated by `env`. */
static bool lookup(const bool *assign, uint64_t n, const struct binding *env,
                   uint64_t i) {
  while (env != NULL) {
    if (env->var == i) {
      return env->val;
    }
    env = env->next;
  }
  if (i < n) {
    return assign[i];
  }
  return false;
}

static ct_status eval_rec(const ct_qbf *p, const bool *assign, uint64_t n,
                          const struct binding *env, uint64_t depth,
                          bool *out) {
  struct binding b;
  bool r;
  ct_status st;
  if (depth == 0) {
    return CT_ELIMIT;
  }
  if (p->kind == CT_QBF_VAR) {
    *out = lookup(assign, n, env, p->var);
    return CT_OK;
  }
  if (p->kind == CT_QBF_NEG) {
    st = eval_rec(p->left, assign, n, env, depth - 1, &r);
    if (st != CT_OK) {
      return st;
    }
    *out = !r;
    return CT_OK;
  }
  if (p->kind == CT_QBF_CONJ) {
    st = eval_rec(p->left, assign, n, env, depth - 1, &r);
    if (st != CT_OK) {
      return st;
    }
    if (!r) {
      *out = false;
      return CT_OK;
    }
    return eval_rec(p->right, assign, n, env, depth - 1, out);
  }
  if (p->kind == CT_QBF_DISJ) {
    st = eval_rec(p->left, assign, n, env, depth - 1, &r);
    if (st != CT_OK) {
      return st;
    }
    if (r) {
      *out = true;
      return CT_OK;
    }
    return eval_rec(p->right, assign, n, env, depth - 1, out);
  }
  /* A quantifier: evaluate the body with the variable false, then true. */
  b.var = p->var;
  b.val = false;
  b.next = env;
  st = eval_rec(p->left, assign, n, &b, depth - 1, &r);
  if (st != CT_OK) {
    return st;
  }
  if (p->kind == CT_QBF_ALL) {
    if (!r) {
      *out = false;
      return CT_OK;
    }
  } else {
    if (r) {
      *out = true;
      return CT_OK;
    }
  }
  b.val = true;
  return eval_rec(p->left, assign, n, &b, depth - 1, out);
}

ct_status ct_qbf_eval(const ct_qbf *p, const bool *assign, uint64_t n,
                      uint64_t max_depth, bool *out) {
  return eval_rec(p, assign, n, NULL, max_depth, out);
}
