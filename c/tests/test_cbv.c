/*
 * Tests of the CEK machine module (include/ct/cbv.h).  Expected values are
 * computed by hand from the definitions of the Lean development, `Start/` (`CEK.stepFn`,
 * `CEK.plug`, `CEK.State.decode`, `CEK.kWeight`, `CEK.measure`), or are
 * instances of theorems of the Lean sources (`State.decode_init`,
 * `Trans.measure_lt`, `stepFn_eq_none_iff`).
 */
#include <stdio.h>

#include "ct/cbv.h"

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
  if (s == NULL || t == NULL) {
    return 0;
  }
  if (ct_lambda_equal(s, t, 1000, &r) != CT_OK) {
    return 0;
  }
  return r;
}
static const ct_kclos *C(ct_arena *a, const ct_lambda *t, const ct_kenv *e) {
  const ct_kclos *c = NULL;
  CHECK(ct_kclos_mk(a, t, e, &c) == CT_OK);
  return c;
}
static const ct_kenv *E(ct_arena *a, const ct_kclos *c, const ct_kenv *e) {
  const ct_kenv *r = NULL;
  CHECK(ct_kenv_cons(a, c, e, &r) == CT_OK);
  return r;
}
static uint64_t measure(const ct_cek_state *s) {
  uint64_t m = 999999;
  CHECK(ct_cek_measure(s, 1000, &m) == CT_OK);
  return m;
}
static const ct_lambda *decode(ct_arena *a, const ct_cek_state *s) {
  const ct_lambda *d = NULL;
  CHECK(ct_cek_decode(a, s, &LIM, &d) == CT_OK);
  return d;
}

/* The run of the machine on `(λx.x) (λy.y)`, state by state. */
static void test_identity_run(ct_arena *a) {
  const ct_lambda *I = L(a, V(a, 0));
  const ct_lambda *t = A(a, I, I);
  ct_cek_state s[8];
  bool halted = true;
  int i;

  CHECK(ct_cek_init(t, &s[0]) == CT_OK);
  /* State.init t = eval t [] []. */
  CHECK(s[0].kind == CT_CEK_EVAL && s[0].t == t && s[0].e == NULL &&
        s[0].k == NULL);
  for (i = 0; i < 6; i++) {
    CHECK(ct_cek_step(a, &s[i], &halted, &s[i + 1]) == CT_OK);
    CHECK(!halted);
  }
  /* s1 = eval I [] [arg I []] */
  CHECK(s[1].kind == CT_CEK_EVAL && s[1].t == I && s[1].e == NULL);
  CHECK(s[1].k != NULL && s[1].k->kind == CT_CEK_ARG && s[1].k->u == I &&
        s[1].k->e == NULL && s[1].k->tail == NULL);
  /* s2 = ret (Clos.mk I []) [arg I []] */
  CHECK(s[2].kind == CT_CEK_RET && s[2].c->code == I && s[2].c->env == NULL);
  CHECK(s[2].k == s[1].k);
  /* s3 = eval I [] [fn (Clos.mk I [])] */
  CHECK(s[3].kind == CT_CEK_EVAL && s[3].t == I && s[3].e == NULL);
  CHECK(s[3].k != NULL && s[3].k->kind == CT_CEK_FN && s[3].k->c == s[2].c &&
        s[3].k->tail == NULL);
  /* s4 = ret (Clos.mk I []) [fn (Clos.mk I [])] */
  CHECK(s[4].kind == CT_CEK_RET && s[4].c->code == I && s[4].c->env == NULL);
  /* s5 = eval (var 0) [Clos.mk I []] [] (the β transition) */
  CHECK(s[5].kind == CT_CEK_EVAL && s[5].t == I->left && s[5].k == NULL);
  CHECK(s[5].e != NULL && s[5].e->head == s[4].c && s[5].e->tail == NULL);
  /* s6 = ret (Clos.mk I []) [] */
  CHECK(s[6].kind == CT_CEK_RET && s[6].c == s[4].c && s[6].k == NULL);
  /* stepFn s6 = none. */
  halted = false;
  CHECK(ct_cek_step(a, &s[6], &halted, &s[7]) == CT_OK);
  CHECK(halted);

  /* The decodings: app I I up to s4, then I. */
  for (i = 0; i <= 4; i++) {
    CHECK(eq(decode(a, &s[i]), t));
  }
  CHECK(eq(decode(a, &s[5]), I));
  CHECK(eq(decode(a, &s[6]), I));

  /* The measures: size I = 2, size (app I I) = 5. */
  CHECK(measure(&s[0]) == 15);
  CHECK(measure(&s[1]) == 14);
  CHECK(measure(&s[2]) == 8);
  CHECK(measure(&s[3]) == 6);
  CHECK(measure(&s[4]) == 0);
  CHECK(measure(&s[5]) == 3);
  CHECK(measure(&s[6]) == 0);
}

/* Free variables, environments and stuck states. */
static void test_transitions(ct_arena *a) {
  const ct_lambda *I = L(a, V(a, 0));
  const ct_lambda *K = L(a, L(a, V(a, 1)));
  const ct_kclos *cI = C(a, I, NULL);
  const ct_kclos *cK = C(a, K, NULL);
  ct_cek_state s;
  ct_cek_state s2;
  const ct_cek_cont *k = NULL;
  bool halted = true;

  /* eval (var 3) [] []  ↦  ret (Clos.mk (var 3) []) [] */
  s.kind = CT_CEK_EVAL;
  s.t = V(a, 3);
  s.e = NULL;
  s.c = NULL;
  s.k = NULL;
  CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
  CHECK(!halted && s2.kind == CT_CEK_RET && s2.c->code == s.t &&
        s2.c->env == NULL && s2.k == NULL);

  /* eval (var 1) [cI, cK] k  ↦  ret cK k */
  CHECK(ct_cek_cont_fn(a, cI, NULL, &k) == CT_OK);
  s.t = V(a, 1);
  s.e = E(a, cI, E(a, cK, NULL));
  s.k = k;
  CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
  CHECK(!halted && s2.kind == CT_CEK_RET && s2.c == cK && s2.k == k);

  /* eval (var 2) [cI, cK] k  ↦  ret (Clos.mk (var 2) [cI, cK]) k */
  s.t = V(a, 2);
  CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
  CHECK(!halted && s2.kind == CT_CEK_RET && s2.c->code == s.t &&
        s2.c->env == s.e && s2.k == k);

  /* ret cI (fn (Clos.mk (var 0) []) :: [])  ↦  none */
  s.kind = CT_CEK_RET;
  s.t = NULL;
  s.e = NULL;
  s.c = cI;
  CHECK(ct_cek_cont_fn(a, C(a, V(a, 0), NULL), NULL, &k) == CT_OK);
  s.k = k;
  CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
  CHECK(halted);
  /* ret cI (fn (Clos.mk (app I I) []) :: [])  ↦  none */
  CHECK(ct_cek_cont_fn(a, C(a, A(a, I, I), NULL), NULL, &k) == CT_OK);
  s.k = k;
  CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
  CHECK(halted);
  /* ret cI []  ↦  none */
  s.k = NULL;
  CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
  CHECK(halted);
}

/* `K I (λλ0)` runs to the value `I`. */
static void test_run_to_value(ct_arena *a) {
  const ct_lambda *I = L(a, V(a, 0));
  const ct_lambda *K = L(a, L(a, V(a, 1)));
  const ct_lambda *F = L(a, L(a, V(a, 0)));
  const ct_lambda *t = A(a, A(a, K, I), F);
  ct_cek_state s;
  ct_cek_state s2;
  bool halted = false;
  int steps = 0;
  CHECK(ct_cek_init(t, &s) == CT_OK);
  while (steps < 100) {
    CHECK(ct_cek_step(a, &s, &halted, &s2) == CT_OK);
    if (halted) {
      break;
    }
    s = s2;
    steps++;
  }
  CHECK(halted);
  /* eval (app (app K I) F) → eval (app K I) → eval K → ret K → eval I →
     ret I → eval (λ0+1) [I] → ret ⟨λ1,[I]⟩ → eval F → ret F →
     eval (var 1) [F, I] → ret I: 11 transitions. */
  CHECK(steps == 11);
  CHECK(s.kind == CT_CEK_RET && s.k == NULL && s.c->code == I);
  CHECK(eq(decode(a, &s), I));
}

static void test_plug_decode(ct_arena *a) {
  const ct_lambda *I = L(a, V(a, 0));
  const ct_lambda *M = V(a, 7);
  const ct_kclos *cI = C(a, I, NULL);
  const ct_cek_cont *k = NULL;
  const ct_lambda *d = NULL;
  ct_cek_state s;
  ct_lambda_limits tiny = {0, 1000};

  /* plug [] M = M */
  CHECK(ct_cek_plug(a, NULL, M, &LIM, &d) == CT_OK && eq(d, M));
  /* plug [arg (var 0) [cI]] M = app M I */
  CHECK(ct_cek_cont_arg(a, V(a, 0), E(a, cI, NULL), NULL, &k) == CT_OK);
  CHECK(ct_cek_plug(a, k, M, &LIM, &d) == CT_OK && eq(d, A(a, M, I)));
  /* plug [fn cI, arg (var 0) [cI]] M = app (app I M) I */
  CHECK(ct_cek_cont_fn(a, cI, k, &k) == CT_OK);
  CHECK(ct_cek_plug(a, k, M, &LIM, &d) == CT_OK &&
        eq(d, A(a, A(a, I, M), I)));
  /* No application node may be built under a zero node budget. */
  CHECK(ct_cek_plug(a, k, M, &tiny, &d) == CT_ELIMIT);

  /* State.decode (State.init t) = t, on an open term. */
  CHECK(ct_cek_init(A(a, L(a, V(a, 1)), V(a, 4)), &s) == CT_OK);
  CHECK(eq(decode(a, &s), s.t));
  /* decode (ret (Clos.mk (lam (var 1)) [cI]) []) = lam I' where the free
     variable 1 under one binder is replaced by I lifted: λ (λ0). */
  s.kind = CT_CEK_RET;
  s.t = NULL;
  s.e = NULL;
  s.c = C(a, L(a, V(a, 1)), E(a, cI, NULL));
  s.k = NULL;
  CHECK(eq(decode(a, &s), L(a, I)));
}

static void test_measure(ct_arena *a) {
  const ct_lambda *I = L(a, V(a, 0));
  const ct_cek_cont *k = NULL;
  uint64_t w = 0;
  uint64_t b = 9;
  /* kWeight [] = 0 */
  CHECK(ct_cek_kweight(NULL, 1000, &w) == CT_OK && w == 0);
  /* kWeight [arg (var 4) [], fn ⟨I,[]⟩, arg I []] = (3*5+2) + (3*2+2) = 25 */
  CHECK(ct_cek_cont_arg(a, I, NULL, NULL, &k) == CT_OK);
  CHECK(ct_cek_cont_fn(a, C(a, I, NULL), k, &k) == CT_OK);
  CHECK(ct_cek_cont_arg(a, V(a, 4), NULL, k, &k) == CT_OK);
  CHECK(ct_cek_kweight(k, 1000, &w) == CT_OK && w == 25);
  /* 3 * size (var (2^63)) overflows. */
  CHECK(ct_cek_cont_arg(a, V(a, UINT64_C(1) << 63), NULL, NULL, &k) == CT_OK);
  CHECK(ct_cek_kweight(k, 1000, &w) == CT_EOVERFLOW);
  /* Label.betaCount */
  CHECK(ct_cek_beta_count(CT_CEK_ADMIN, &b) == CT_OK && b == 0);
  CHECK(ct_cek_beta_count(CT_CEK_BETA, &b) == CT_OK && b == 1);
  CHECK(ct_cek_beta_count(7, &b) == CT_EINVAL);
}

int main(void) {
  ct_arena *a;
  if (ct_arena_create(&a) != CT_OK) {
    fprintf(stderr, "test_cbv: no memory\n");
    return 1;
  }
  test_identity_run(a);
  test_transitions(a);
  test_run_to_value(a);
  test_plug_decode(a);
  test_measure(a);
  ct_arena_destroy(a);
  if (failures != 0) {
    fprintf(stderr, "test_cbv: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_cbv: all checks passed\n");
  return 0;
}
