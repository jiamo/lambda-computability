#include "ct/spacemachine.h"

ct_status ct_sp_config_space(const ct_sp_config *c, uint64_t *out) {
  uint64_t w;
  ct_status st = ct_u64_add(c->w_head, 1, &w);
  if (st != CT_OK) {
    return st;
  }
  *out = c->tape_len > w ? c->tape_len : w;
  return CT_OK;
}

ct_status ct_sp_write_at(bool *bits, uint64_t *len, uint64_t cap, uint64_t i,
                         bool b) {
  uint64_t k;
  if (i < *len) {
    bits[i] = b;
    return CT_OK;
  }
  /* the result has length i + 1 */
  if (i >= cap) {
    return CT_ELIMIT;
  }
  for (k = *len; k < i; k++) {
    bits[k] = false;
  }
  bits[i] = b;
  *len = i + 1;
  return CT_OK;
}

ct_status ct_sp_move_work(uint64_t i, int d, uint64_t *out) {
  if (d == CT_SP_LEFT) {
    *out = i > 0 ? i - 1 : 0;
    return CT_OK;
  }
  if (d == CT_SP_RIGHT) {
    return ct_u64_add(i, 1, out);
  }
  if (d == CT_SP_STAY) {
    *out = i;
    return CT_OK;
  }
  return CT_EINVAL;
}

ct_status ct_sp_move_in(uint64_t n, uint64_t i, int d, uint64_t *out) {
  if (d == CT_SP_LEFT) {
    *out = i > 0 ? i - 1 : 0;
    return CT_OK;
  }
  if (d == CT_SP_RIGHT) {
    /* min (i + 1) n, without overflow */
    *out = i < n ? i + 1 : n;
    return CT_OK;
  }
  if (d == CT_SP_STAY) {
    *out = i;
    return CT_OK;
  }
  return CT_EINVAL;
}

ct_status ct_sp_accept(const ct_sp_machine *m, uint64_t q, bool *out) {
  *out = q < m->states ? m->accept[q] : false;
  return CT_OK;
}

ct_status ct_sp_step_list(const ct_sp_machine *m, const bool *x, uint64_t n,
                          const ct_sp_config *c, ct_sp_config *out,
                          uint64_t out_cap, bool *const *bufs,
                          uint64_t buf_cap, uint64_t *count) {
  const ct_sp_entry *e;
  uint64_t ai;
  uint64_t idx;
  uint64_t i;
  bool b;
  ct_status st;
  if (c->state >= m->states) {
    *count = 0;
    return CT_OK;
  }
  ai = c->in_head < n ? (x[c->in_head] ? 2 : 1) : 0;
  b = c->w_head < c->tape_len ? c->tape[c->w_head] : false;
  /* state < states, and the table has 6 * states entries */
  idx = c->state * 6 + ai * 2 + (b ? 1 : 0);
  e = &m->entries[idx];
  if (e->start > m->n_instrs || e->count > m->n_instrs - e->start) {
    return CT_EINVAL;
  }
  if (e->count > out_cap) {
    return CT_ELIMIT;
  }
  for (i = 0; i < e->count; i++) {
    const ct_sp_instr *t = &m->instrs[e->start + i];
    ct_sp_config *o = &out[i];
    uint64_t k;
    uint64_t len = c->tape_len;
    if (len > buf_cap) {
      return CT_ELIMIT;
    }
    for (k = 0; k < len; k++) {
      bufs[i][k] = c->tape[k];
    }
    st = ct_sp_write_at(bufs[i], &len, buf_cap, c->w_head, t->bit);
    if (st != CT_OK) {
      return st;
    }
    st = ct_sp_move_in(n, c->in_head, t->in_move, &o->in_head);
    if (st != CT_OK) {
      return st;
    }
    st = ct_sp_move_work(c->w_head, t->work_move, &o->w_head);
    if (st != CT_OK) {
      return st;
    }
    o->state = t->state;
    o->tape = bufs[i];
    o->tape_len = len;
    o->tape_cap = buf_cap;
  }
  *count = e->count;
  return CT_OK;
}

ct_status ct_sp_init(bool *buf, uint64_t cap, ct_sp_config *out) {
  out->state = 0;
  out->in_head = 0;
  out->tape_len = 0;
  out->tape_cap = cap;
  out->tape = buf;
  out->w_head = 0;
  return CT_OK;
}

ct_status ct_sp_const_machine(bool b, bool *accept, ct_sp_entry *entries,
                              ct_sp_machine *out) {
  int k;
  accept[0] = b;
  for (k = 0; k < 6; k++) {
    entries[k].start = 0;
    entries[k].count = 0;
  }
  out->states = 1;
  out->accept = accept;
  out->entries = entries;
  out->instrs = NULL;
  out->n_instrs = 0;
  return CT_OK;
}
