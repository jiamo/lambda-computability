#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "ct/lambda.h"

static int failures = 0;

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond); \
      failures++;                                                            \
    }                                                                        \
  } while (0)

static const ct_lambda_limits LIM = {1000000, 100000};

static ct_arena *arena;

static const ct_lambda *V(uint64_t i) {
  const ct_lambda *t = NULL;
  if (ct_lambda_var(arena, i, &t) != CT_OK) {
    failures++;
  }
  return t;
}

static const ct_lambda *A(const ct_lambda *f, const ct_lambda *x) {
  const ct_lambda *t = NULL;
  if (ct_lambda_app(arena, f, x, &t) != CT_OK) {
    failures++;
  }
  return t;
}

static const ct_lambda *L(const ct_lambda *b) {
  const ct_lambda *t = NULL;
  if (ct_lambda_lam(arena, b, &t) != CT_OK) {
    failures++;
  }
  return t;
}

static bool eq(const ct_lambda *s, const ct_lambda *t) {
  bool r = false;
  if (ct_lambda_equal(s, t, 1000000, &r) != CT_OK) {
    failures++;
    return false;
  }
  return r;
}

static const ct_lambda *church(uint64_t n) {
  const ct_lambda *t = NULL;
  if (ct_lambda_church(arena, n, &LIM, &t) != CT_OK) {
    failures++;
  }
  return t;
}

static void test_constructors_and_equality(void) {
  const ct_lambda *t = A(L(V(0)), V(3));
  bool r;
  CHECK(t->kind == CT_LAMBDA_APP);
  CHECK(t->left->kind == CT_LAMBDA_LAM);
  CHECK(t->left->left->kind == CT_LAMBDA_VAR && t->left->left->index == 0);
  CHECK(t->right->kind == CT_LAMBDA_VAR && t->right->index == 3);
  CHECK(eq(t, A(L(V(0)), V(3))));
  CHECK(!eq(t, A(L(V(1)), V(3))));
  CHECK(!eq(t, A(L(V(0)), V(2))));
  CHECK(!eq(t, L(V(0))));
  CHECK(!eq(V(0), V(1)));
  CHECK(eq(V(7), V(7)));
  /* the depth limit */
  CHECK(ct_lambda_equal(t, t, 3, &r) == CT_OK && r);
  CHECK(ct_lambda_equal(t, t, 2, &r) == CT_ELIMIT);
}

static void test_church(void) {
  /* church 0 = λ λ 0, church 2 = λ λ (1 (1 0)) */
  CHECK(eq(church(0), L(L(V(0)))));
  CHECK(eq(church(1), L(L(A(V(1), V(0))))));
  CHECK(eq(church(2), L(L(A(V(1), A(V(1), V(0)))))));
  CHECK(eq(church(3), L(L(A(V(1), A(V(1), A(V(1), V(0))))))));
  CHECK(!eq(church(2), church(3)));
  {
    const ct_lambda *t;
    ct_lambda_limits small = {5, 10};
    /* church 3 needs 2 + 3 + 2 = 7 nodes */
    CHECK(ct_lambda_church(arena, 3, &small, &t) == CT_ELIMIT);
    small.max_nodes = 7;
    CHECK(ct_lambda_church(arena, 3, &small, &t) == CT_OK);
    CHECK(eq(t, church(3)));
  }
}

static void test_lift_subst_size(void) {
  const ct_lambda *t;
  uint64_t s;
  /* lift 2 1 (λ (0 1 2)) = λ (0 1 4)  (under the binder the cutoff is 2) */
  CHECK(ct_lambda_lift(arena, 2, 1, L(A(A(V(0), V(1)), V(2))), &LIM, &t) ==
        CT_OK);
  CHECK(eq(t, L(A(A(V(0), V(1)), V(4)))));
  /* lift 1 0 (0 3) = 1 4 */
  CHECK(ct_lambda_lift(arena, 1, 0, A(V(0), V(3)), &LIM, &t) == CT_OK);
  CHECK(eq(t, A(V(1), V(4))));
  /* overflow of an index */
  CHECK(ct_lambda_lift(arena, 1, 0, V(UINT64_MAX), &LIM, &t) == CT_EOVERFLOW);

  /* subst s 0 (0 1 (λ 1)) = s 0 (λ (lift 1 0 s)) for s = 5 */
  CHECK(ct_lambda_subst(arena, V(5), 0, A(A(V(0), V(1)), L(V(1))), &LIM, &t) ==
        CT_OK);
  CHECK(eq(t, A(A(V(5), V(0)), L(V(6)))));
  /* subst s 1 (λ (0 1 2 3)) = λ (0 1 (lift 1 0 s) 2), s = λ 1 */
  CHECK(ct_lambda_subst(arena, L(V(1)), 1, L(A(A(A(V(0), V(1)), V(2)), V(3))),
                        &LIM, &t) == CT_OK);
  CHECK(eq(t, L(A(A(A(V(0), V(1)), L(V(2))), V(2)))));

  /* size: var i counts i + 1 */
  CHECK(ct_lambda_size(V(0), 10, &s) == CT_OK && s == 1);
  CHECK(ct_lambda_size(V(4), 10, &s) == CT_OK && s == 5);
  CHECK(ct_lambda_size(A(L(V(0)), V(2)), 10, &s) == CT_OK && s == 1 + 1 + 3 + 1);
  /* church 2 = λ λ (1 (1 0)): 1 + 1 + (2 + (2 + 1 + 1) + 1) = 9 */
  CHECK(ct_lambda_size(church(2), 10, &s) == CT_OK && s == 9);
  CHECK(ct_lambda_size(V(UINT64_MAX), 10, &s) == CT_EOVERFLOW);
  CHECK(ct_lambda_size(L(V(UINT64_MAX - 1)), 10, &s) == CT_EOVERFLOW);
  CHECK(ct_lambda_size(church(2), 3, &s) == CT_ELIMIT);
}

static void test_step(void) {
  const ct_lambda *t;
  bool normal;
  /* (λx.x) y → y, with y = var 0 */
  CHECK(ct_lambda_step(arena, A(L(V(0)), V(0)), &LIM, &t, &normal) == CT_OK);
  CHECK(!normal && eq(t, V(0)));
  /* (λx.x) y with y = var 7 */
  CHECK(ct_lambda_step(arena, A(L(V(0)), V(7)), &LIM, &t, &normal) == CT_OK);
  CHECK(!normal && eq(t, V(7)));
  /* normal forms */
  CHECK(ct_lambda_step(arena, V(3), &LIM, &t, &normal) == CT_OK && normal);
  CHECK(ct_lambda_step(arena, church(4), &LIM, &t, &normal) == CT_OK && normal);
  CHECK(ct_lambda_step(arena, A(V(0), L(V(0))), &LIM, &t, &normal) == CT_OK &&
        normal);
  /* the leftmost-outermost redex: in (λ0) ((λ0) 1) the outer one */
  CHECK(ct_lambda_step(arena, A(L(V(0)), A(L(V(0)), V(1))), &LIM, &t,
                       &normal) == CT_OK);
  CHECK(!normal && eq(t, A(L(V(0)), V(1))));
  /* in x ((λ0) 1) ((λ0) 2) the redex in the first argument */
  CHECK(ct_lambda_step(arena, A(A(V(5), A(L(V(0)), V(1))), A(L(V(0)), V(2))),
                       &LIM, &t, &normal) == CT_OK);
  CHECK(!normal && eq(t, A(A(V(5), V(1)), A(L(V(0)), V(2)))));
  /* under a binder: λ ((λ 1) 0) → λ 0 */
  CHECK(ct_lambda_step(arena, L(A(L(V(1)), V(0))), &LIM, &t, &normal) == CT_OK);
  CHECK(!normal && eq(t, L(V(0))));
  /* the substitution lowers the free variables: (λ λ 2) 0 → λ 1 */
  CHECK(ct_lambda_step(arena, A(L(L(V(2))), V(0)), &LIM, &t, &normal) == CT_OK);
  CHECK(!normal && eq(t, L(V(1))));
}

static void test_normalize(void) {
  const ct_lambda *plus;
  const ct_lambda *t;
  const ct_lambda *omega;
  uint64_t steps;
  /* PLUS = λm.λn.λf.λx. m f (n f x) */
  plus = L(L(L(L(A(A(V(3), V(1)), A(A(V(2), V(1)), V(0)))))));
  CHECK(ct_lambda_normalize(arena, A(A(plus, church(2)), church(3)), 1000,
                            &LIM, &t, &steps) == CT_OK);
  CHECK(eq(t, church(5)));
  printf("test_lambda: PLUS 2 3 normalizes to church 5 in %llu steps\n",
         (unsigned long long)steps);
  CHECK(steps > 0);
  /* a normal form takes no step */
  CHECK(ct_lambda_normalize(arena, church(3), 10, &LIM, &t, &steps) == CT_OK);
  CHECK(steps == 0 && eq(t, church(3)));
  /* (λx.x) y takes exactly one step */
  CHECK(ct_lambda_normalize(arena, A(L(V(0)), V(9)), 1, &LIM, &t, &steps) ==
        CT_OK);
  CHECK(steps == 1 && eq(t, V(9)));
  /* Ω = (λ 0 0)(λ 0 0) does not normalize */
  omega = A(L(A(V(0), V(0))), L(A(V(0), V(0))));
  CHECK(ct_lambda_normalize(arena, omega, 50, &LIM, &t, &steps) == CT_ELIMIT);
  /* not enough fuel */
  CHECK(ct_lambda_normalize(arena, A(A(plus, church(2)), church(3)), 1, &LIM,
                            &t, &steps) == CT_ELIMIT);
  /* no fuel: a normal form is returned as is, a redex gives CT_ELIMIT */
  CHECK(ct_lambda_normalize(arena, church(2), 0, &LIM, &t, &steps) == CT_OK);
  CHECK(steps == 0 && eq(t, church(2)));
  CHECK(ct_lambda_normalize(arena, A(L(V(0)), V(9)), 0, &LIM, &t, &steps) ==
        CT_ELIMIT);
  /* once the fuel is exhausted no further step is computed: the step from
     (λ λ 1) UINT64_MAX would overflow, but with fuel 0 it is not attempted */
  CHECK(ct_lambda_normalize(arena, A(L(L(V(1))), V(UINT64_MAX)), 0, &LIM, &t,
                            &steps) == CT_ELIMIT);
  CHECK(ct_lambda_normalize(arena, A(L(L(V(1))), V(UINT64_MAX)), 1, &LIM, &t,
                            &steps) == CT_EOVERFLOW);
  /* a term reducible only under an abstraction, or only in an argument */
  CHECK(ct_lambda_normalize(arena, L(A(L(V(0)), V(0))), 0, &LIM, &t, &steps) ==
        CT_ELIMIT);
  CHECK(ct_lambda_normalize(arena, A(V(0), A(L(V(0)), V(1))), 0, &LIM, &t,
                            &steps) == CT_ELIMIT);
  CHECK(ct_lambda_normalize(arena, A(V(0), A(L(V(0)), V(1))), 1, &LIM, &t,
                            &steps) == CT_OK);
  CHECK(steps == 1 && eq(t, A(V(0), V(1))));
}

int main(void) {
  if (ct_arena_create(&arena) != CT_OK) {
    return 1;
  }
  test_constructors_and_equality();
  test_church();
  test_lift_subst_size();
  test_step();
  test_normalize();
  ct_arena_destroy(arena);
  if (failures != 0) {
    fprintf(stderr, "test_lambda: %d failure(s)\n", failures);
    return 1;
  }
  printf("test_lambda: all checks passed\n");
  return 0;
}
