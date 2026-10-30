/*
 * Tests of the leftmost-outermost reduction module (include/ct/leftmost.h).
 * Expected values are computed by hand from `Lambda.step_normal`,
 * `Lambda.nstep` and `Lambda.closure` (the Lean development, `Start/`).
 */
#include <stdio.h>

#include "ct/leftmost.h"

static int failures = 0;

#define CHECK(cond)                                                     \
  do {                                                                  \
    if (!(cond)) {                                                      \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, \
              #cond);                                                   \
      failures++;                                                       \
    }                                                                   \
  } while (0)

static const ct_lambda_limits LIM = {1000, 1000};

static const ct_lambda *V(ct_arena *a, uint64_t i) {
  const ct_lambda *t = NULL;
  CHECK(ct_lambda_var(a, i, &t) == CT_OK);
  return t;
}
static const ct_lambda *A(ct_arena *a, const ct_lambda *f,
                          const ct_lambda *x) {
  const ct_lambda *t = NULL;
  CHECK(ct_lambda_app(a, f, x, &t) == CT_OK);
  return t;
}
static const ct_lambda *L(ct_arena *a, const ct_lambda *b) {
  const ct_lambda *t = NULL;
  CHECK(ct_lambda_lam(a, b, &t) == CT_OK);
  return t;
}
static int eq(const ct_lambda *s, const ct_lambda *t) {
  bool r = false;
  if (s == NULL || t == NULL || ct_lambda_equal(s, t, 1000, &r) != CT_OK) {
    return 0;
  }
  return r;
}

int main(void) {
  ct_arena *a;
  const ct_lambda *I;
  const ct_lambda *r = NULL;
  const ct_lambda *t;
  bool none = false;
  ct_lambda_limits small = {1, 1000};
  if (ct_arena_create(&a) != CT_OK) {
    fprintf(stderr, "test_leftmost: no memory\n");
    return 1;
  }
  I = L(a, V(a, 0));
  /* step_normal ((λx.x) y) = some y */
  CHECK(ct_leftmost_step_normal(a, A(a, I, V(a, 3)), &LIM, &r, &none) ==
            CT_OK &&
        !none && eq(r, V(a, 3)));
  /* step_normal (var 0) = none */
  r = NULL;
  CHECK(ct_leftmost_step_normal(a, V(a, 0), &LIM, &r, &none) == CT_OK &&
        none && r == NULL);
  /* step_normal (y ((λx.x) z)) = some (y z): the function part is normal */
  t = A(a, V(a, 5), A(a, I, V(a, 6)));
  CHECK(ct_leftmost_step_normal(a, t, &LIM, &r, &none) == CT_OK && !none &&
        eq(r, A(a, V(a, 5), V(a, 6))));
  /* step_normal (λ. (λx.x) 0) = some (λ. 0) */
  t = L(a, A(a, I, V(a, 0)));
  CHECK(ct_leftmost_step_normal(a, t, &LIM, &r, &none) == CT_OK && !none &&
        eq(r, L(a, V(a, 0))));
  /* leftmost: ((λx.x) a) ((λx.x) b) contracts the left redex first */
  t = A(a, A(a, I, V(a, 1)), A(a, I, V(a, 2)));
  CHECK(ct_leftmost_step_normal(a, t, &LIM, &r, &none) == CT_OK && !none &&
        eq(r, A(a, V(a, 1), A(a, I, V(a, 2)))));
  /* nstep fixes normal forms and steps otherwise */
  CHECK(ct_leftmost_nstep(a, I, &LIM, &r) == CT_OK && r == I);
  CHECK(ct_leftmost_nstep(a, A(a, I, I), &LIM, &r) == CT_OK && eq(r, I));
  /* closure 0 t = t, closure 2 (var 0) = λλ0 */
  CHECK(ct_leftmost_closure(a, 0, V(a, 4), &LIM, &r) == CT_OK &&
        eq(r, V(a, 4)));
  CHECK(ct_leftmost_closure(a, 2, V(a, 0), &LIM, &r) == CT_OK &&
        eq(r, L(a, L(a, V(a, 0)))));
  CHECK(ct_leftmost_closure(a, 2, V(a, 0), &small, &r) == CT_ELIMIT);
  ct_arena_destroy(a);
  if (failures != 0) {
    fprintf(stderr, "test_leftmost: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_leftmost: all checks passed\n");
  return 0;
}
