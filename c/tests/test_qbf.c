#include <stdint.h>
#include <stdio.h>

#include "ct/qbf.h"

static int failures = 0;

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond); \
      failures++;                                                            \
    }                                                                        \
  } while (0)

static ct_arena *arena;

static const ct_qbf *Var(uint64_t i) {
  const ct_qbf *p = NULL;
  if (ct_qbf_var(arena, i, &p) != CT_OK) failures++;
  return p;
}
static const ct_qbf *Neg(const ct_qbf *q) {
  const ct_qbf *p = NULL;
  if (ct_qbf_neg(arena, q, &p) != CT_OK) failures++;
  return p;
}
static const ct_qbf *Conj(const ct_qbf *q, const ct_qbf *r) {
  const ct_qbf *p = NULL;
  if (ct_qbf_conj(arena, q, r, &p) != CT_OK) failures++;
  return p;
}
static const ct_qbf *Disj(const ct_qbf *q, const ct_qbf *r) {
  const ct_qbf *p = NULL;
  if (ct_qbf_disj(arena, q, r, &p) != CT_OK) failures++;
  return p;
}
static const ct_qbf *All(uint64_t i, const ct_qbf *q) {
  const ct_qbf *p = NULL;
  if (ct_qbf_all(arena, i, q, &p) != CT_OK) failures++;
  return p;
}
static const ct_qbf *Ex(uint64_t i, const ct_qbf *q) {
  const ct_qbf *p = NULL;
  if (ct_qbf_ex(arena, i, q, &p) != CT_OK) failures++;
  return p;
}

/* eval with the assignment `assign`/`n`; -1 on error */
static int ev(const ct_qbf *p, const bool *assign, uint64_t n) {
  bool r = false;
  if (ct_qbf_eval(p, assign, n, 1000, &r) != CT_OK) {
    return -1;
  }
  return r ? 1 : 0;
}

int main(void) {
  const bool tf[2] = {true, false};
  const bool ft[2] = {false, true};
  const ct_qbf *x0, *x1, *x7, *p;
  bool r;
  if (ct_arena_create(&arena) != CT_OK) {
    return 1;
  }
  x0 = Var(0);
  x1 = Var(1);
  x7 = Var(7);

  /* free variables read the assignment; variables >= n read as false */
  CHECK(ev(x0, tf, 2) == 1);
  CHECK(ev(x1, tf, 2) == 0);
  CHECK(ev(x1, ft, 2) == 1);
  CHECK(ev(x7, tf, 2) == 0);
  CHECK(ev(x0, NULL, 0) == 0);
  CHECK(ev(Neg(x7), tf, 2) == 1);

  /* connectives */
  CHECK(ev(Conj(x0, x1), tf, 2) == 0);
  CHECK(ev(Conj(x0, Neg(x1)), tf, 2) == 1);
  CHECK(ev(Disj(x1, x7), tf, 2) == 0);
  CHECK(ev(Disj(x1, x0), tf, 2) == 1);
  CHECK(ev(Neg(Disj(x1, x0)), tf, 2) == 0);

  /* quantifiers */
  CHECK(ev(All(0, Disj(x0, Neg(x0))), NULL, 0) == 1);
  CHECK(ev(Ex(0, Conj(x0, Neg(x0))), NULL, 0) == 0);
  CHECK(ev(All(0, x0), tf, 2) == 0);
  CHECK(ev(Ex(1, x1), tf, 2) == 1);
  /* a quantified variable beyond the assignment */
  CHECK(ev(Ex(7, x7), tf, 2) == 1);
  CHECK(ev(All(7, x7), tf, 2) == 0);
  CHECK(ev(All(7, Disj(x7, x0)), tf, 2) == 1);
  /* the innermost quantifier wins; outside it the assignment is unchanged */
  p = All(0, Ex(0, x0));
  CHECK(ev(p, NULL, 0) == 1);
  p = Conj(Ex(0, Neg(x0)), x0);
  CHECK(ev(p, tf, 2) == 1);
  /* ∀x ∃y. x ↔ y  (as (x ∧ y) ∨ (¬x ∧ ¬y)) */
  p = All(0, Ex(1, Disj(Conj(x0, x1), Conj(Neg(x0), Neg(x1)))));
  CHECK(ev(p, NULL, 0) == 1);
  /* ∃y ∀x. x ↔ y is false */
  p = Ex(1, All(0, Disj(Conj(x0, x1), Conj(Neg(x0), Neg(x1)))));
  CHECK(ev(p, NULL, 0) == 0);
  /* the depth limit: All(0, Disj(x0, Neg(x0))) has height 4 */
  p = All(0, Disj(x0, Neg(x0)));
  CHECK(ct_qbf_eval(p, NULL, 0, 4, &r) == CT_OK && r);
  CHECK(ct_qbf_eval(p, NULL, 0, 3, &r) == CT_ELIMIT);

  ct_arena_destroy(arena);
  if (failures != 0) {
    fprintf(stderr, "test_qbf: %d failure(s)\n", failures);
    return 1;
  }
  printf("test_qbf: all checks passed\n");
  return 0;
}
