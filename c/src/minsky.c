#include "ct/minsky.h"

ct_status ct_minsky_reg(const ct_kinstr *ins, uint64_t *out) {
  *out = ins->reg;
  return CT_OK;
}

ct_status ct_minsky_base(uint64_t i, uint64_t *out) {
  if (i > 5) {
    return CT_EOVERFLOW;
  }
  if (i == 5) {
    /* 2^32 + 1 */
    *out = (UINT64_C(1) << 32) + 1;
    return CT_OK;
  }
  *out = (UINT64_C(1) << (UINT64_C(1) << i)) + 1;
  return CT_OK;
}

/* `b ^ e`, checked. */
static ct_status pow_u64(uint64_t b, uint64_t e, uint64_t *out) {
  uint64_t acc = 1;
  ct_status st;
  while (e > 0) {
    st = ct_u64_mul(acc, b, &acc);
    if (st != CT_OK) {
      return st;
    }
    e = e - 1;
  }
  *out = acc;
  return CT_OK;
}

ct_status ct_minsky_godel(uint64_t k, const uint64_t *r, uint64_t nr,
                          uint64_t *out) {
  uint64_t acc = 1;
  uint64_t i;
  ct_status st;
  /* only the registers below min(k, nr) can be nonzero */
  uint64_t n = k < nr ? k : nr;
  for (i = 0; i < n; i++) {
    uint64_t b;
    uint64_t f;
    if (r[i] == 0) {
      continue;
    }
    st = ct_minsky_base(i, &b);
    if (st != CT_OK) {
      return st;
    }
    st = pow_u64(b, r[i], &f);
    if (st != CT_OK) {
      return st;
    }
    st = ct_u64_mul(acc, f, &acc);
    if (st != CT_OK) {
      return st;
    }
  }
  *out = acc;
  return CT_OK;
}

static void set_inc(ct_cminstr *out, bool ctr, uint64_t l) {
  out->kind = CT_CMINSTR_INC;
  out->ctr = ctr;
  out->l1 = l;
  out->l2 = 0;
}

static void set_test(ct_cminstr *out, bool ctr, uint64_t l1, uint64_t l2) {
  out->kind = CT_CMINSTR_TEST;
  out->ctr = ctr;
  out->l1 = l1;
  out->l2 = l2;
}

/* Checks that `o + 3p + 3` fits, so that every label below it does. */
static ct_status block_fits(uint64_t p, uint64_t o) {
  uint64_t x;
  ct_status st = ct_u64_mul(3, p, &x);
  if (st != CT_OK) {
    return st;
  }
  st = ct_u64_add(x, 3, &x);
  if (st != CT_OK) {
    return st;
  }
  return ct_u64_add(x, o, &x);
}

ct_status ct_minsky_inc_f(uint64_t p, uint64_t o, uint64_t t, uint64_t j,
                          ct_cminstr *out) {
  ct_status st = block_fits(p, o);
  if (st != CT_OK) {
    return st;
  }
  if (j == 0) {
    set_test(out, true, o + p + 1, o + 1);
  } else if (j < p) {
    if (j > UINT64_MAX - o - 1) {
      return CT_EOVERFLOW;
    }
    set_inc(out, false, o + j + 1);
  } else if (j == p) {
    set_inc(out, false, o);
  } else if (j == p + 1) {
    set_test(out, false, t, o + p + 2);
  } else {
    set_inc(out, true, o + p + 1);
  }
  return CT_OK;
}

ct_status ct_minsky_exit_l(uint64_t p, uint64_t o, uint64_t j,
                           uint64_t *out) {
  uint64_t x;
  uint64_t d;
  ct_status st;
  if (j == 0) {
    st = ct_u64_add(o, p, &x);
    if (st != CT_OK) {
      return st;
    }
    return ct_u64_add(x, 1, out);
  }
  /* p - 1 - j, truncated at 0 */
  d = (p >= 1 && p - 1 >= j) ? p - 1 - j : 0;
  st = ct_u64_add(o, p, &x);
  if (st != CT_OK) {
    return st;
  }
  st = ct_u64_add(x, 3, &x);
  if (st != CT_OK) {
    return st;
  }
  return ct_u64_add(x, d, out);
}

ct_status ct_minsky_test_f(uint64_t p, uint64_t o, uint64_t t1, uint64_t t2,
                           uint64_t j, ct_cminstr *out) {
  ct_status st = block_fits(p, o);
  if (st != CT_OK) {
    return st;
  }
  if (j < p) {
    uint64_t e;
    st = ct_minsky_exit_l(p, o, j, &e);
    if (st != CT_OK) {
      return st;
    }
    set_test(out, true, e, o + j + 1);
  } else if (j == p) {
    set_inc(out, false, o);
  } else if (j == p + 1) {
    set_test(out, false, t2, o + p + 2);
  } else if (j == p + 2) {
    set_inc(out, true, o + p + 1);
  } else if (j < 2 * p + 2) {
    set_inc(out, true, o + j + 1);
  } else if (j == 2 * p + 2) {
    set_test(out, false, t1, o + 2 * p + 3);
  } else if (j < 3 * p + 2) {
    set_inc(out, true, o + j + 1);
  } else {
    set_inc(out, true, o + 2 * p + 2);
  }
  return CT_OK;
}

ct_status ct_minsky_isize(const ct_kinstr *ins, uint64_t *out) {
  uint64_t b;
  ct_status st = ct_minsky_base(ins->reg, &b);
  if (st != CT_OK) {
    return st;
  }
  if (ins->kind == CT_KINSTR_TEST) {
    st = ct_u64_mul(3, b, &b);
    if (st != CT_OK) {
      return st;
    }
  }
  return ct_u64_add(b, 3, out);
}

ct_status ct_minsky_off(const ct_km *m, uint64_t l, uint64_t *out) {
  uint64_t acc = 0;
  uint64_t i;
  uint64_t n = l < m->len ? l : m->len;
  ct_status st;
  for (i = 0; i < n; i++) {
    uint64_t s;
    st = ct_minsky_isize(&m->prog[i], &s);
    if (st != CT_OK) {
      return st;
    }
    st = ct_u64_add(acc, s, &acc);
    if (st != CT_OK) {
      return st;
    }
  }
  *out = acc;
  return CT_OK;
}

ct_status ct_minsky_block_f(const ct_km *m, uint64_t o, const ct_kinstr *ins,
                            uint64_t j, ct_cminstr *out) {
  uint64_t p;
  uint64_t t1;
  ct_status st = ct_minsky_base(ins->reg, &p);
  if (st != CT_OK) {
    return st;
  }
  st = ct_minsky_off(m, ins->l1, &t1);
  if (st != CT_OK) {
    return st;
  }
  if (ins->kind == CT_KINSTR_INC) {
    return ct_minsky_inc_f(p, o, t1, j, out);
  } else {
    uint64_t t2;
    st = ct_minsky_off(m, ins->l2, &t2);
    if (st != CT_OK) {
      return st;
    }
    return ct_minsky_test_f(p, o, t1, t2, j, out);
  }
}

ct_status ct_minsky_compile_aux(const ct_km *m, uint64_t s, ct_cminstr *out,
                                uint64_t cap, uint64_t *out_len) {
  uint64_t n = 0;
  uint64_t l;
  ct_status st;
  for (l = s; l < m->len; l++) {
    const ct_kinstr *ins = &m->prog[l];
    uint64_t size;
    uint64_t o;
    uint64_t j;
    st = ct_minsky_isize(ins, &size);
    if (st != CT_OK) {
      return st;
    }
    st = ct_minsky_off(m, l, &o);
    if (st != CT_OK) {
      return st;
    }
    if (size > cap - n) {
      return CT_ELIMIT;
    }
    for (j = 0; j < size; j++) {
      st = ct_minsky_block_f(m, o, ins, j, &out[n + j]);
      if (st != CT_OK) {
        return st;
      }
    }
    n = n + size;
  }
  *out_len = n;
  return CT_OK;
}

ct_status ct_minsky_compile(const ct_km *m, ct_cminstr *out, uint64_t cap,
                            uint64_t *out_len) {
  return ct_minsky_compile_aux(m, 0, out, cap, out_len);
}

ct_status ct_minsky_enc_c(const ct_km *m, uint64_t k, uint64_t pc,
                          const uint64_t *r, uint64_t nr, ct_cmconf *out) {
  uint64_t o;
  uint64_t g;
  ct_status st = ct_minsky_off(m, pc, &o);
  if (st != CT_OK) {
    return st;
  }
  st = ct_minsky_godel(k, r, nr, &g);
  if (st != CT_OK) {
    return st;
  }
  out->pc = o;
  out->a = g;
  out->b = 0;
  return CT_OK;
}
