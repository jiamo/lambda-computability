/*
 * Tests of the counter machine module (include/ct/minsky.h).  Expected values
 * are computed by hand from the definitions of the Lean development, `Start/`, and the
 * compiled programs are run (with the transitions `CM.Step` of
 * Start/FsubGhelli.lean) to check the simulation theorem of Start/Minsky.lean
 * on small cases: the compiled block of an instruction maps the Gödel number
 * of the registers before it to the one after it.
 */
#include <stdio.h>

#include "ct/minsky.h"

static int failures = 0;

#define CHECK(cond)                                                     \
  do {                                                                  \
    if (!(cond)) {                                                      \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, \
              #cond);                                                   \
      failures++;                                                       \
    }                                                                   \
  } while (0)

/* Runs a two-counter program (CM.Step) until the label leaves the program. */
static int run_cm(const ct_cminstr *p, uint64_t n, ct_cmconf *c,
                  uint64_t fuel) {
  while (c->pc < n) {
    const ct_cminstr *i = &p[c->pc];
    if (fuel-- == 0) {
      return 0;
    }
    if (i->kind == CT_CMINSTR_INC) {
      if (i->ctr) {
        c->a++;
      } else {
        c->b++;
      }
      c->pc = i->l1;
    } else {
      uint64_t *r = i->ctr ? &c->a : &c->b;
      if (*r == 0) {
        c->pc = i->l1;
      } else {
        (*r)--;
        c->pc = i->l2;
      }
    }
  }
  return 1;
}

static int is_inc(const ct_cminstr *i, bool ctr, uint64_t l) {
  return i->kind == CT_CMINSTR_INC && i->ctr == ctr && i->l1 == l;
}
static int is_test(const ct_cminstr *i, bool ctr, uint64_t l1, uint64_t l2) {
  return i->kind == CT_CMINSTR_TEST && i->ctr == ctr && i->l1 == l1 &&
         i->l2 == l2;
}

static void test_numbers(void) {
  uint64_t v = 0;
  uint64_t r[3] = {2, 0, 1};
  ct_kinstr ins = {CT_KINSTR_TEST, 7, 1, 2};
  CHECK(ct_minsky_base(0, &v) == CT_OK && v == 3);
  CHECK(ct_minsky_base(1, &v) == CT_OK && v == 5);
  CHECK(ct_minsky_base(2, &v) == CT_OK && v == 17);
  CHECK(ct_minsky_base(4, &v) == CT_OK && v == 65537);
  CHECK(ct_minsky_base(5, &v) == CT_OK && v == UINT64_C(4294967297));
  CHECK(ct_minsky_base(6, &v) == CT_EOVERFLOW);
  /* godel 3 [2, 0, 1] = 3^2 * 5^0 * 17^1 = 153 */
  CHECK(ct_minsky_godel(3, r, 3, &v) == CT_OK && v == 153);
  /* godel 2 [2, 0, 1] = 9; godel 0 r = 1; registers past nr are 0 */
  CHECK(ct_minsky_godel(2, r, 3, &v) == CT_OK && v == 9);
  CHECK(ct_minsky_godel(0, r, 3, &v) == CT_OK && v == 1);
  CHECK(ct_minsky_godel(100, r, 3, &v) == CT_OK && v == 153);
  CHECK(ct_minsky_reg(&ins, &v) == CT_OK && v == 7);
  /* exitL 3 10 0 = 14, exitL 3 10 1 = 10 + 3 + 3 + 1 = 17,
     exitL 3 10 5 = 16 (truncated subtraction) */
  CHECK(ct_minsky_exit_l(3, 10, 0, &v) == CT_OK && v == 14);
  CHECK(ct_minsky_exit_l(3, 10, 1, &v) == CT_OK && v == 17);
  CHECK(ct_minsky_exit_l(3, 10, 5, &v) == CT_OK && v == 16);
}

static void test_blocks(void) {
  ct_cminstr i;
  /* incF 3 0 6 j, j = 0..5 */
  CHECK(ct_minsky_inc_f(3, 0, 6, 0, &i) == CT_OK && is_test(&i, true, 4, 1));
  CHECK(ct_minsky_inc_f(3, 0, 6, 1, &i) == CT_OK && is_inc(&i, false, 2));
  CHECK(ct_minsky_inc_f(3, 0, 6, 2, &i) == CT_OK && is_inc(&i, false, 3));
  CHECK(ct_minsky_inc_f(3, 0, 6, 3, &i) == CT_OK && is_inc(&i, false, 0));
  CHECK(ct_minsky_inc_f(3, 0, 6, 4, &i) == CT_OK && is_test(&i, false, 6, 5));
  CHECK(ct_minsky_inc_f(3, 0, 6, 5, &i) == CT_OK && is_inc(&i, true, 4));
  /* testF 3 0 20 30 j at a few j */
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 0, &i) == CT_OK &&
        is_test(&i, true, 4, 1));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 1, &i) == CT_OK &&
        is_test(&i, true, 7, 2));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 3, &i) == CT_OK && is_inc(&i, false, 0));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 4, &i) == CT_OK &&
        is_test(&i, false, 30, 5));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 5, &i) == CT_OK && is_inc(&i, true, 4));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 7, &i) == CT_OK && is_inc(&i, true, 8));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 8, &i) == CT_OK &&
        is_test(&i, false, 20, 9));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 10, &i) == CT_OK &&
        is_inc(&i, true, 11));
  CHECK(ct_minsky_test_f(3, 0, 20, 30, 11, &i) == CT_OK &&
        is_inc(&i, true, 8));
  CHECK(ct_minsky_inc_f(UINT64_MAX / 2, 0, 0, 0, &i) == CT_EOVERFLOW);
}

static void test_compile(void) {
  /* M = [inc 1 1, test 0 3 0]: inc r1; loop: if r0 = 0 halt else dec r0 */
  ct_kinstr prog[2] = {{CT_KINSTR_INC, 1, 1, 0}, {CT_KINSTR_TEST, 0, 3, 0}};
  ct_km m = {2, prog};
  ct_cminstr out[64];
  uint64_t n = 0;
  uint64_t v = 0;
  uint64_t r[2] = {2, 4};
  ct_cmconf c;
  /* isize (inc 1 _) = 5 + 3 = 8, isize (test 0 _ _) = 9 + 3 = 12 */
  CHECK(ct_minsky_isize(&prog[0], &v) == CT_OK && v == 8);
  CHECK(ct_minsky_isize(&prog[1], &v) == CT_OK && v == 12);
  CHECK(ct_minsky_off(&m, 0, &v) == CT_OK && v == 0);
  CHECK(ct_minsky_off(&m, 1, &v) == CT_OK && v == 8);
  CHECK(ct_minsky_off(&m, 5, &v) == CT_OK && v == 20);
  CHECK(ct_minsky_compile(&m, out, 64, &n) == CT_OK && n == 20);
  CHECK(ct_minsky_compile(&m, out, 19, &n) == CT_ELIMIT);
  CHECK(ct_minsky_compile_aux(&m, 1, out, 64, &n) == CT_OK && n == 12);
  CHECK(ct_minsky_compile(&m, out, 64, &n) == CT_OK && n == 20);
  /* encC M 2 ⟨0, [2, 4]⟩ = ⟨0, 3^2 * 5^4, 0⟩ */
  CHECK(ct_minsky_enc_c(&m, 2, 0, r, 2, &c) == CT_OK && c.pc == 0 &&
        c.a == 5625 && c.b == 0);
  /* The counter machine ends with r = [0, 7] (r1 is incremented 3 times);
     the compiled machine ends at
     the end of the program with a = godel 2 [0, 7] = 78125, b = 0. */
  CHECK(run_cm(out, n, &c, 1000000) && c.pc == 20 && c.a == 78125 &&
        c.b == 0);
}

int main(void) {
  test_numbers();
  test_blocks();
  test_compile();
  if (failures != 0) {
    fprintf(stderr, "test_minsky: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_minsky: all checks passed\n");
  return 0;
}
