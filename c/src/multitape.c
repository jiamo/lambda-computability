#include "ct/multitape.h"

ct_status ct_mt_literal_eval(uint64_t var, bool val, const bool *x,
                             uint64_t nv, bool *out) {
  if (var >= nv) {
    return CT_EINVAL;
  }
  *out = (x[var] == val);
  return CT_OK;
}

ct_status ct_mt_gate_input_eval(const ct_mt_gate_input *g, const bool *x,
                                uint64_t nv, bool *out) {
  if (g->is_literal) {
    return ct_mt_literal_eval(g->var, g->val, x, nv, out);
  }
  *out = g->val;
  return CT_OK;
}

ct_status ct_mt_gate_count(uint64_t bottom_count, uint64_t middle_count,
                           uint64_t *out) {
  uint64_t s;
  ct_status st = ct_u64_add(bottom_count, middle_count, &s);
  if (st != CT_OK) {
    return st;
  }
  return ct_u64_add(s, 1, out);
}

/* Whether `move` can be applied to `t` without leaving the window. */
static bool move_ok(int move, const ct_mt_tape *t) {
  if (move == CT_MT_LEFT) {
    return t->pos > 0;
  }
  if (move == CT_MT_RIGHT) {
    return t->pos + 1 < t->len;
  }
  return true;
}

ct_status ct_mt_headmove_apply(int move, ct_mt_tape *t) {
  if (move != CT_MT_LEFT && move != CT_MT_STAY && move != CT_MT_RIGHT) {
    return CT_EINVAL;
  }
  if (!move_ok(move, t)) {
    return CT_ELIMIT;
  }
  if (move == CT_MT_LEFT) {
    t->pos = t->pos - 1;
  } else if (move == CT_MT_RIGHT) {
    t->pos = t->pos + 1;
  }
  return CT_OK;
}

ct_status ct_mt_update(uint32_t nk, ct_mt_cfg *c, uint32_t q,
                       const uint32_t *writes, const int *moves) {
  uint32_t k;
  if (nk > CT_MT_MAX_TAPES) {
    return CT_EINVAL;
  }
  for (k = 0; k < nk; k++) {
    if (moves[k] != CT_MT_LEFT && moves[k] != CT_MT_STAY &&
        moves[k] != CT_MT_RIGHT) {
      return CT_EINVAL;
    }
    if (!move_ok(moves[k], &c->tapes[k])) {
      return CT_ELIMIT;
    }
  }
  for (k = 0; k < nk; k++) {
    c->tapes[k].cells[c->tapes[k].pos] = writes[k];
    (void)ct_mt_headmove_apply(moves[k], &c->tapes[k]);
  }
  c->q = q;
  return CT_OK;
}

ct_status ct_mt_step(const ct_mt_machine *m, ct_mt_cfg *c, bool *halted) {
  uint64_t idx = 0;
  uint64_t mult = 1;
  uint32_t k;
  ct_status st;
  const ct_mt_entry *e;
  if (m->nk == 0 || m->nk > CT_MT_MAX_TAPES || c->q >= m->nq) {
    return CT_EINVAL;
  }
  for (k = 0; k < m->nk; k++) {
    uint64_t term;
    uint32_t r = c->tapes[k].cells[c->tapes[k].pos];
    if (r >= m->ng) {
      return CT_EINVAL;
    }
    st = ct_u64_mul(r, mult, &term);
    if (st != CT_OK) {
      return st;
    }
    st = ct_u64_add(idx, term, &idx);
    if (st != CT_OK) {
      return st;
    }
    st = ct_u64_mul(mult, m->ng, &mult);
    if (st != CT_OK) {
      return st;
    }
  }
  st = ct_u64_mul(c->q, mult, &mult);
  if (st != CT_OK) {
    return st;
  }
  st = ct_u64_add(mult, idx, &idx);
  if (st != CT_OK) {
    return st;
  }
  e = &m->code[idx];
  if (!e->defined) {
    *halted = true;
    return CT_OK;
  }
  st = ct_mt_update(m->nk, c, e->q, e->writes, e->moves);
  if (st != CT_OK) {
    return st;
  }
  *halted = false;
  return CT_OK;
}

ct_status ct_mt_init(const ct_mt_machine *m, const bool *input, uint64_t n,
                     uint32_t *const *bufs, uint64_t len, uint64_t origin,
                     ct_mt_cfg *out) {
  uint32_t k;
  uint64_t i;
  if (m->nk == 0 || m->nk > CT_MT_MAX_TAPES || m->input_tape >= m->nk) {
    return CT_EINVAL;
  }
  if (origin >= len || n > len - origin) {
    return CT_ELIMIT;
  }
  for (k = 0; k < m->nk; k++) {
    for (i = 0; i < len; i++) {
      bufs[k][i] = 0;
    }
    out->tapes[k].len = len;
    out->tapes[k].pos = origin;
    out->tapes[k].cells = bufs[k];
  }
  for (i = 0; i < n; i++) {
    bufs[m->input_tape][origin + i] = m->input_symbol[input[i] ? 1 : 0];
  }
  out->q = m->initial_state;
  return CT_OK;
}

ct_status ct_mt_run_steps(const ct_mt_machine *m, ct_mt_cfg *c, uint64_t n,
                          bool *none) {
  uint64_t i;
  bool halted = false;
  for (i = 0; i < n; i++) {
    ct_status st = ct_mt_step(m, c, &halted);
    if (st != CT_OK) {
      return st;
    }
    if (halted) {
      *none = true;
      return CT_OK;
    }
  }
  *none = false;
  return CT_OK;
}
