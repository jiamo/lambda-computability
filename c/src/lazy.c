#include "ct/lazy.h"

ct_status ct_lenv_cons(ct_arena *a, uint64_t addr, const ct_lenv *e,
                       const ct_lenv **out) {
  void *mem;
  ct_lenv *n;
  ct_status st = ct_arena_alloc(a, sizeof(ct_lenv), _Alignof(ct_lenv), &mem);
  if (st != CT_OK) {
    return st;
  }
  n = mem;
  n->addr = addr;
  n->tail = e;
  *out = n;
  return CT_OK;
}

ct_status ct_lazy_cell_orig(const ct_lcell *c, ct_lclos *out) {
  *out = c->c;
  return CT_OK;
}

ct_status ct_lazy_init(const ct_lambda *t, ct_lframe *stack,
                       uint64_t stack_cap, ct_lcell *heap, uint64_t heap_cap,
                       ct_lstate *out) {
  out->code = t;
  out->env = NULL;
  out->stack_len = 0;
  out->stack_cap = stack_cap;
  out->stack = stack;
  out->heap_len = 0;
  out->heap_cap = heap_cap;
  out->heap = heap;
  return CT_OK;
}

ct_status ct_lazy_beta_count(const ct_llabel *l, uint64_t *out) {
  *out = (l->kind == CT_LLABEL_BETA) ? 1 : 0;
  return CT_OK;
}

ct_status ct_lazy_forced(const ct_llabel *l, bool *has, uint64_t *addr) {
  if (l->kind == CT_LLABEL_FORCE) {
    *has = true;
    *addr = l->addr;
  } else {
    *has = false;
  }
  return CT_OK;
}

/* `e[n]?`: true and `*out` the address if it exists. */
static bool env_get(const ct_lenv *e, uint64_t n, uint64_t *out) {
  while (e != NULL && n > 0) {
    e = e->tail;
    n = n - 1;
  }
  if (e == NULL) {
    return false;
  }
  *out = e->addr;
  return true;
}

ct_status ct_lazy_step(ct_arena *a, ct_lstate *s, bool *halted) {
  const ct_lambda *t = s->code;
  if (t->kind == CT_LAMBDA_APP) {
    /* ⟨app t u, e, S, H⟩ ↦ ⟨t, e, arg |H| :: S, H ++ [thunk ⟨u, e⟩]⟩ */
    if (s->stack_len >= s->stack_cap || s->heap_len >= s->heap_cap) {
      return CT_ELIMIT;
    }
    s->heap[s->heap_len].kind = CT_LCELL_THUNK;
    s->heap[s->heap_len].c.code = t->right;
    s->heap[s->heap_len].c.env = s->env;
    s->heap[s->heap_len].v.code = NULL;
    s->heap[s->heap_len].v.env = NULL;
    s->stack[s->stack_len].kind = CT_LFRAME_ARG;
    s->stack[s->stack_len].addr = s->heap_len;
    s->stack_len = s->stack_len + 1;
    s->heap_len = s->heap_len + 1;
    s->code = t->left;
    *halted = false;
    return CT_OK;
  }
  if (t->kind == CT_LAMBDA_LAM) {
    ct_lframe top;
    if (s->stack_len == 0) {
      /* ⟨lam _, _, [], _⟩ ↦ none */
      *halted = true;
      return CT_OK;
    }
    top = s->stack[s->stack_len - 1];
    if (top.kind == CT_LFRAME_ARG) {
      /* ⟨lam t, e, arg a :: S, H⟩ ↦ ⟨t, a :: e, S, H⟩ */
      const ct_lenv *e2;
      ct_status st = ct_lenv_cons(a, top.addr, s->env, &e2);
      if (st != CT_OK) {
        return st;
      }
      s->code = t->left;
      s->env = e2;
      s->stack_len = s->stack_len - 1;
      *halted = false;
      return CT_OK;
    }
    /* ⟨lam t, e, upd a :: S, H⟩ ↦ ⟨lam t, e, S, H.set a (value c ⟨lam t, e⟩)⟩
       if H[a]? = some (hole c), none otherwise */
    if (top.addr < s->heap_len && s->heap[top.addr].kind == CT_LCELL_HOLE) {
      s->heap[top.addr].kind = CT_LCELL_VALUE;
      s->heap[top.addr].v.code = t;
      s->heap[top.addr].v.env = s->env;
      s->stack_len = s->stack_len - 1;
      *halted = false;
      return CT_OK;
    }
    *halted = true;
    return CT_OK;
  }
  /* ⟨var n, e, S, H⟩ */
  {
    uint64_t addr;
    if (!env_get(s->env, t->index, &addr) || addr >= s->heap_len) {
      *halted = true;
      return CT_OK;
    }
    if (s->heap[addr].kind == CT_LCELL_THUNK) {
      /* thunk c ↦ ⟨c.code, c.env, upd a :: S, H.set a (hole c)⟩ */
      if (s->stack_len >= s->stack_cap) {
        return CT_ELIMIT;
      }
      s->heap[addr].kind = CT_LCELL_HOLE;
      s->stack[s->stack_len].kind = CT_LFRAME_UPD;
      s->stack[s->stack_len].addr = addr;
      s->stack_len = s->stack_len + 1;
      s->code = s->heap[addr].c.code;
      s->env = s->heap[addr].c.env;
      *halted = false;
      return CT_OK;
    }
    if (s->heap[addr].kind == CT_LCELL_VALUE) {
      /* value _ v ↦ ⟨v.code, v.env, S, H⟩ */
      s->code = s->heap[addr].v.code;
      s->env = s->heap[addr].v.env;
      *halted = false;
      return CT_OK;
    }
    *halted = true;
    return CT_OK;
  }
}
