/*
 * Tests of the lazy machine module (include/ct/lazy.h).  Expected values are
 * computed by hand from `Lazy.lstepFn`, `Lazy.LState.init`, `Cell.orig`,
 * `LLabel.betaCount` and `LLabel.forced` (the Lean development, `Start/`).
 */
#include <stdio.h>

#include "ct/lazy.h"

static int failures = 0;

#define CHECK(cond)                                                     \
  do {                                                                  \
    if (!(cond)) {                                                      \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, \
              #cond);                                                   \
      failures++;                                                       \
    }                                                                   \
  } while (0)

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

/* Runs the machine until it halts (at most `max` steps); returns the number
   of transitions, or -1 on an error. */
static int run(ct_arena *a, ct_lstate *s, int max) {
  int n = 0;
  bool halted = false;
  while (n <= max) {
    if (ct_lazy_step(a, s, &halted) != CT_OK) {
      return -1;
    }
    if (halted) {
      return n;
    }
    n++;
  }
  return -1;
}

static void test_identity(ct_arena *a) {
  ct_lframe stack[8];
  ct_lcell heap[8];
  ct_lstate s;
  bool halted = true;
  const ct_lambda *I = L(a, V(a, 0));
  const ct_lambda *t = A(a, I, I);
  CHECK(ct_lazy_init(t, stack, 8, heap, 8, &s) == CT_OK);
  /* LState.init t = ⟨t, [], [], []⟩ */
  CHECK(s.code == t && s.env == NULL && s.stack_len == 0 && s.heap_len == 0);
  /* ⟨app I I, [], [], []⟩ ↦ ⟨I, [], [arg 0], [thunk ⟨I, []⟩]⟩ */
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && !halted);
  CHECK(s.code == I && s.env == NULL && s.stack_len == 1 &&
        stack[0].kind == CT_LFRAME_ARG && stack[0].addr == 0);
  CHECK(s.heap_len == 1 && heap[0].kind == CT_LCELL_THUNK &&
        heap[0].c.code == I && heap[0].c.env == NULL);
  /* ↦ ⟨var 0, [0], [], H⟩ */
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && !halted);
  CHECK(s.code == I->left && s.env != NULL && s.env->addr == 0 &&
        s.env->tail == NULL && s.stack_len == 0);
  /* ↦ ⟨I, [], [upd 0], [hole ⟨I, []⟩]⟩ */
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && !halted);
  CHECK(s.code == I && s.env == NULL && s.stack_len == 1 &&
        stack[0].kind == CT_LFRAME_UPD && stack[0].addr == 0);
  CHECK(heap[0].kind == CT_LCELL_HOLE && heap[0].c.code == I);
  /* ↦ ⟨I, [], [], [value ⟨I, []⟩ ⟨I, []⟩]⟩ */
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && !halted);
  CHECK(s.stack_len == 0 && heap[0].kind == CT_LCELL_VALUE &&
        heap[0].c.code == I && heap[0].v.code == I && heap[0].v.env == NULL);
  /* final */
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && halted);
  CHECK(s.code == I && s.heap_len == 1);
}

/* `(λx. x x) I`: the argument is evaluated once and then shared. */
static void test_sharing(ct_arena *a) {
  ct_lframe stack[8];
  ct_lcell heap[8];
  ct_lstate s;
  const ct_lambda *I = L(a, V(a, 0));
  const ct_lambda *D = L(a, A(a, V(a, 0), V(a, 0)));
  CHECK(ct_lazy_init(A(a, D, I), stack, 8, heap, 8, &s) == CT_OK);
  CHECK(run(a, &s, 100) == 9);
  CHECK(s.code == I && s.env == NULL && s.stack_len == 0);
  CHECK(s.heap_len == 2);
  CHECK(heap[0].kind == CT_LCELL_VALUE && heap[0].v.code == I);
  CHECK(heap[1].kind == CT_LCELL_VALUE && heap[1].v.code == I &&
        heap[1].c.code->kind == CT_LAMBDA_VAR);
}

static void test_stuck_and_limits(ct_arena *a) {
  ct_lframe stack[2];
  ct_lcell heap[2];
  ct_lstate s;
  bool halted = false;
  const ct_lenv *e = NULL;
  const ct_lambda *I = L(a, V(a, 0));
  /* a free variable: e[0]? = none */
  CHECK(ct_lazy_init(V(a, 0), stack, 2, heap, 2, &s) == CT_OK);
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && halted);
  /* a black hole: H[0] = hole c */
  CHECK(ct_lenv_cons(a, 0, NULL, &e) == CT_OK);
  s.env = e;
  s.heap_len = 1;
  heap[0].kind = CT_LCELL_HOLE;
  heap[0].c.code = I;
  heap[0].c.env = NULL;
  halted = false;
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && halted);
  /* an address outside the heap */
  s.heap_len = 0;
  halted = false;
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && halted);
  /* lam with an update marker for a cell that is not a hole */
  s.code = I;
  s.env = NULL;
  s.heap_len = 1;
  heap[0].kind = CT_LCELL_THUNK;
  s.stack_len = 1;
  stack[0].kind = CT_LFRAME_UPD;
  stack[0].addr = 0;
  halted = false;
  CHECK(ct_lazy_step(a, &s, &halted) == CT_OK && halted);
  CHECK(s.stack_len == 1 && heap[0].kind == CT_LCELL_THUNK);
  /* no room in the heap for the thunk of an application */
  CHECK(ct_lazy_init(A(a, I, I), stack, 2, heap, 0, &s) == CT_OK);
  CHECK(ct_lazy_step(a, &s, &halted) == CT_ELIMIT);
  CHECK(s.heap_len == 0 && s.stack_len == 0);
}

static void test_labels(void) {
  ct_lcell c;
  ct_lclos o;
  ct_llabel l;
  uint64_t n = 7;
  bool has = true;
  uint64_t addr = 0;
  c.kind = CT_LCELL_VALUE;
  c.c.code = NULL;
  c.c.env = NULL;
  c.v.code = NULL;
  c.v.env = NULL;
  CHECK(ct_lazy_cell_orig(&c, &o) == CT_OK && o.code == NULL);
  l.kind = CT_LLABEL_BETA;
  l.addr = 0;
  CHECK(ct_lazy_beta_count(&l, &n) == CT_OK && n == 1);
  CHECK(ct_lazy_forced(&l, &has, &addr) == CT_OK && !has);
  l.kind = CT_LLABEL_FORCE;
  l.addr = 5;
  CHECK(ct_lazy_beta_count(&l, &n) == CT_OK && n == 0);
  CHECK(ct_lazy_forced(&l, &has, &addr) == CT_OK && has && addr == 5);
}

int main(void) {
  ct_arena *a;
  if (ct_arena_create(&a) != CT_OK) {
    fprintf(stderr, "test_lazy: no memory\n");
    return 1;
  }
  test_identity(a);
  test_sharing(a);
  test_stuck_and_limits(a);
  test_labels();
  ct_arena_destroy(a);
  if (failures != 0) {
    fprintf(stderr, "test_lazy: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_lazy: all checks passed\n");
  return 0;
}
