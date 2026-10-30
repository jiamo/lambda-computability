/*
 * Tests of the Krivine machine module (include/ct/krivine.h).  Expected values
 * are computed by hand from the definitions of the Lean development, `Start/`, or are
 * instances of theorems of the Lean sources (`decTerm_flatten`,
 * `hstep_trans`, `State.decode_init`).
 */
#include <stdio.h>

#include "ct/krivine.h"

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
static int node_is(const ct_ktab *tab, uint64_t i, int kind, uint64_t x,
                   uint64_t y) {
  return i < tab->len && tab->nodes[i].kind == kind && tab->nodes[i].x == x &&
         tab->nodes[i].y == y;
}

static void test_table(ct_arena *a) {
  ct_ktab tab;
  ct_ktab tab2;
  uint64_t root = 99;
  const ct_lambda *t;
  const ct_lambda *d;
  ct_lambda_limits small = {2, 1000};

  /* tabOf (var 3) = [var 3], rootOf (var 3) = 0. */
  CHECK(ct_krivine_tab_of(a, V(a, 3), 10, &tab, &root) == CT_OK);
  CHECK(tab.len == 1 && root == 0 && node_is(&tab, 0, CT_KNODE_VAR, 3, 0));

  /* flatten (app (lam (var 0)) (var 5)) [] =
     ([var 0, lam 0, var 5, app 1 2], 3). */
  t = A(a, L(a, V(a, 0)), V(a, 5));
  CHECK(ct_krivine_tab_of(a, t, 10, &tab, &root) == CT_OK);
  CHECK(tab.len == 4 && root == 3);
  CHECK(node_is(&tab, 0, CT_KNODE_VAR, 0, 0));
  CHECK(node_is(&tab, 1, CT_KNODE_LAM, 0, 0));
  CHECK(node_is(&tab, 2, CT_KNODE_VAR, 5, 0));
  CHECK(node_is(&tab, 3, CT_KNODE_APP, 1, 2));

  /* decTerm (tabOf t) (rootOf t) = t  (theorem decTerm_tabOf). */
  CHECK(ct_krivine_dec_term(a, &tab, root, &LIM, &d) == CT_OK);
  CHECK(eq(d, t));
  /* decTerm tab 1 = lam (var 0); decTerm tab 7 = var 0 (no node). */
  CHECK(ct_krivine_dec_term(a, &tab, 1, &LIM, &d) == CT_OK);
  CHECK(eq(d, L(a, V(a, 0))));
  CHECK(ct_krivine_dec_term(a, &tab, 7, &LIM, &d) == CT_OK);
  CHECK(eq(d, V(a, 0)));
  /* decTermF tab 0 p = var 0;  decTermF tab 1 3 = app (var 0) (var 0). */
  CHECK(ct_krivine_dec_term_f(a, &tab, 0, 3, &LIM, &d) == CT_OK);
  CHECK(eq(d, V(a, 0)));
  CHECK(ct_krivine_dec_term_f(a, &tab, 1, 3, &LIM, &d) == CT_OK);
  CHECK(eq(d, A(a, V(a, 0), V(a, 0))));
  /* Limits. */
  CHECK(ct_krivine_dec_term(a, &tab, root, &small, &d) == CT_ELIMIT);
  CHECK(ct_krivine_tab_of(a, t, 2, &tab2, &root) == CT_ELIMIT);

  /* flatten (var 7) tab = (tab ++ [var 7], 4). */
  CHECK(ct_krivine_flatten(a, V(a, 7), &tab, 10, &tab2, &root) == CT_OK);
  CHECK(tab2.len == 5 && root == 4 && node_is(&tab2, 3, CT_KNODE_APP, 1, 2) &&
        node_is(&tab2, 4, CT_KNODE_VAR, 7, 0));
}

static void test_env_nth(void) {
  /* Heap: 0 = clos 4 none, 1 = cons 0 none, 2 = cons 0 (some 1),
     3 = clos 5 (some 2). */
  ct_kcell heap[4] = {{CT_KCELL_CLOS, 4, false, 0},
                      {CT_KCELL_CONS, 0, false, 0},
                      {CT_KCELL_CONS, 0, true, 1},
                      {CT_KCELL_CLOS, 5, true, 2}};
  uint64_t q = 77;
  CHECK(ct_krivine_env_nth(heap, 4, true, 2, 0, &q) && q == 0);
  q = 77;
  CHECK(ct_krivine_env_nth(heap, 4, true, 2, 1, &q) && q == 0);
  CHECK(!ct_krivine_env_nth(heap, 4, true, 2, 2, &q));
  CHECK(!ct_krivine_env_nth(heap, 4, false, 0, 0, &q));
  CHECK(!ct_krivine_env_nth(heap, 4, true, 3, 0, &q)); /* a closure cell */
  CHECK(!ct_krivine_env_nth(heap, 4, true, 9, 0, &q)); /* out of the heap */
}

static void test_heap_decode(ct_arena *a) {
  /* Table of `app (lam (var 0)) (var 5)`, heap as in test_env_nth. */
  ct_ktab tab;
  uint64_t root;
  ct_kcell heap[4] = {{CT_KCELL_CLOS, 2, false, 0},
                      {CT_KCELL_CONS, 0, false, 0},
                      {CT_KCELL_CONS, 0, true, 1},
                      {CT_KCELL_CLOS, 1, true, 2}};
  const ct_kclos *c;
  const ct_kenv *e;
  CHECK(ct_krivine_tab_of(a, A(a, L(a, V(a, 0)), V(a, 5)), 10, &tab, &root) ==
        CT_OK);
  /* decClos tab heap 0 = mk (var 5) []. */
  CHECK(ct_krivine_dec_clos(a, &tab, heap, 4, 0, &LIM, &c) == CT_OK);
  CHECK(eq(c->code, V(a, 5)) && c->env == NULL);
  /* decClos tab heap 3 = mk (lam (var 0)) [mk (var 5) [], mk (var 5) []]. */
  CHECK(ct_krivine_dec_clos(a, &tab, heap, 4, 3, &LIM, &c) == CT_OK);
  CHECK(eq(c->code, L(a, V(a, 0))));
  e = c->env;
  CHECK(e != NULL && eq(e->head->code, V(a, 5)) && e->head->env == NULL);
  CHECK(e != NULL && e->tail != NULL && eq(e->tail->head->code, V(a, 5)) &&
        e->tail->tail == NULL);
  /* decClos on a cons cell, or out of the heap: mk (var 0) []. */
  CHECK(ct_krivine_dec_clos(a, &tab, heap, 4, 1, &LIM, &c) == CT_OK);
  CHECK(eq(c->code, V(a, 0)) && c->env == NULL);
  CHECK(ct_krivine_dec_clos(a, &tab, heap, 4, 8, &LIM, &c) == CT_OK);
  CHECK(eq(c->code, V(a, 0)) && c->env == NULL);
  /* decEnvP tab heap (some 2) has two entries; decEnvP none = []. */
  CHECK(ct_krivine_dec_env(a, &tab, heap, 4, true, 2, &LIM, &e) == CT_OK);
  CHECK(e != NULL && e->tail != NULL && e->tail->tail == NULL);
  CHECK(ct_krivine_dec_env(a, &tab, heap, 4, false, 0, &LIM, &e) == CT_OK);
  CHECK(e == NULL);
  /* Fuel: decEnvF tab heap 1 (some 2) = [decClF tab heap 0 0] =
     [mk (var 0) []];  decClF tab heap 0 p = mk (var 0) []. */
  CHECK(ct_krivine_dec_env_f(a, &tab, heap, 4, 1, true, 2, &LIM, &e) == CT_OK);
  CHECK(e != NULL && eq(e->head->code, V(a, 0)) && e->tail == NULL);
  CHECK(ct_krivine_dec_clos_f(a, &tab, heap, 4, 0, 3, &LIM, &c) == CT_OK);
  CHECK(eq(c->code, V(a, 0)) && c->env == NULL);
}

/* Runs the implementation on `(λ.0) (var 5)` and on `K (var 3) (var 4)`. */
static void test_hstep(ct_arena *a) {
  ct_ktab tab;
  uint64_t root;
  ct_kcell heap[8];
  uint64_t stack[8];
  ct_khstate s;
  bool stuck = true;
  int label = -1;
  ct_kstate ds;
  const ct_lambda *t;
  const ct_lambda *d;

  t = A(a, L(a, V(a, 0)), V(a, 5));
  CHECK(ct_krivine_tab_of(a, t, 10, &tab, &root) == CT_OK);
  CHECK(ct_krivine_init_state(t, 10, heap, 8, stack, 8, &s) == CT_OK);
  CHECK(s.code == root && !s.has_env && s.stack_len == 0 && s.heap_len == 0);
  /* State.decode (decState tab (initState t)) = t. */
  CHECK(ct_krivine_dec_state(a, &tab, &s, &LIM, &ds) == CT_OK);
  CHECK(ct_krivine_state_decode(a, &ds, &LIM, &d) == CT_OK);
  CHECK(eq(d, t));

  /* app: heap [clos 2 none], stack [0], code 1. */
  CHECK(ct_krivine_hstep(&tab, &s, &stuck, &label) == CT_OK);
  CHECK(!stuck && label == CT_KRIVINE_APP && s.code == 1 && !s.has_env);
  CHECK(s.stack_len == 1 && s.stack[0] == 0 && s.heap_len == 1);
  CHECK(s.heap[0].kind == CT_KCELL_CLOS && s.heap[0].x == 2 &&
        !s.heap[0].has_y);
  /* The decoded term is unchanged by an administrative transition. */
  CHECK(ct_krivine_dec_state(a, &tab, &s, &LIM, &ds) == CT_OK);
  CHECK(ct_krivine_state_decode(a, &ds, &LIM, &d) == CT_OK);
  CHECK(eq(d, t));
  /* beta: heap [clos 2 none, cons 0 none], env some 1, stack [], code 0. */
  CHECK(ct_krivine_hstep(&tab, &s, &stuck, &label) == CT_OK);
  CHECK(!stuck && label == CT_KRIVINE_BETA && s.code == 0 && s.has_env &&
        s.env == 1 && s.stack_len == 0 && s.heap_len == 2);
  CHECK(s.heap[1].kind == CT_KCELL_CONS && s.heap[1].x == 0 &&
        !s.heap[1].has_y);
  /* After the β transition the state decodes to the reduct `var 5`. */
  CHECK(ct_krivine_dec_state(a, &tab, &s, &LIM, &ds) == CT_OK);
  CHECK(ct_krivine_state_decode(a, &ds, &LIM, &d) == CT_OK);
  CHECK(eq(d, V(a, 5)));
  /* var: the variable 0 is the closure at 0: code 2, env none. */
  CHECK(ct_krivine_hstep(&tab, &s, &stuck, &label) == CT_OK);
  CHECK(!stuck && label == CT_KRIVINE_VAR && s.code == 2 && !s.has_env &&
        s.heap_len == 2 && s.stack_len == 0);
  /* var 5 in the empty environment: stuck, state unchanged. */
  CHECK(ct_krivine_hstep(&tab, &s, &stuck, &label) == CT_OK);
  CHECK(stuck && label == CT_KRIVINE_VAR && s.code == 2 && s.heap_len == 2);

  /* K (var 3) (var 4) = app (app (lam (lam (var 1))) (var 3)) (var 4). */
  t = A(a, A(a, L(a, L(a, V(a, 1))), V(a, 3)), V(a, 4));
  CHECK(ct_krivine_tab_of(a, t, 10, &tab, &root) == CT_OK);
  CHECK(ct_krivine_init_state(t, 10, heap, 8, stack, 8, &s) == CT_OK);
  {
    int expected[6] = {CT_KRIVINE_APP, CT_KRIVINE_APP, CT_KRIVINE_BETA,
                       CT_KRIVINE_BETA, CT_KRIVINE_VAR, -1};
    int i;
    for (i = 0; i < 6; i++) {
      CHECK(ct_krivine_hstep(&tab, &s, &stuck, &label) == CT_OK);
      if (expected[i] < 0) {
        CHECK(stuck);
      } else {
        CHECK(!stuck && label == expected[i]);
      }
    }
  }
  /* The machine stops on `var 3`, the head normal form of K 3 4. */
  CHECK(ct_krivine_dec_state(a, &tab, &s, &LIM, &ds) == CT_OK);
  CHECK(ct_krivine_state_decode(a, &ds, &LIM, &d) == CT_OK);
  CHECK(eq(d, V(a, 3)));

  /* Capacity: an application needs a heap cell and a stack entry. */
  CHECK(ct_krivine_init_state(t, 10, heap, 0, stack, 8, &s) == CT_OK);
  CHECK(ct_krivine_hstep(&tab, &s, &stuck, &label) == CT_ELIMIT);
  CHECK(s.heap_len == 0 && s.stack_len == 0 && s.code == root);
  /* Depth limit of initState. */
  CHECK(ct_krivine_init_state(t, 2, heap, 8, stack, 8, &s) == CT_ELIMIT);
}

static void test_decode(ct_arena *a) {
  const ct_kclos *c7 = C(a, V(a, 7), NULL);
  const ct_kclos *c;
  const ct_kenv *e;
  const ct_lambda *d;
  ct_kstate s;
  /* unfold (mk (lam (app (var 0) (var 1))) [mk (var 7) []])
       = lam (app (var 0) (var 8)). */
  c = C(a, L(a, A(a, V(a, 0), V(a, 1))), E(a, c7, NULL));
  CHECK(ct_krivine_unfold(a, c, &LIM, &d) == CT_OK);
  CHECK(eq(d, L(a, A(a, V(a, 0), V(a, 8)))));
  /* unfoldEnv [mk (var 7) []] 0 = var 7; unfoldEnv [_] 3 = var 2. */
  e = E(a, c7, NULL);
  CHECK(ct_krivine_unfold_env(a, e, 0, &LIM, &d) == CT_OK);
  CHECK(eq(d, V(a, 7)));
  CHECK(ct_krivine_unfold_env(a, e, 3, &LIM, &d) == CT_OK);
  CHECK(eq(d, V(a, 2)));
  /* unfold (mk (var 2) [c7, c7]) = var 0 (the free index 2 is shifted down
     by the two entries of the environment). */
  CHECK(ct_krivine_unfold(a, C(a, V(a, 2), E(a, c7, E(a, c7, NULL))), &LIM,
                          &d) == CT_OK);
  CHECK(eq(d, V(a, 0)));
  /* spine (var 9) [c7, mk (var 1) [c7]] = app (app (var 9) (var 7)) (var 0). */
  e = E(a, c7, E(a, C(a, V(a, 1), E(a, c7, NULL)), NULL));
  CHECK(ct_krivine_spine(a, V(a, 9), e, &LIM, &d) == CT_OK);
  CHECK(eq(d, A(a, A(a, V(a, 9), V(a, 7)), V(a, 0))));
  /* State.decode ⟨lam (var 1), [c7], [c7]⟩ = app (lam (var 8)) (var 7). */
  s.code = L(a, V(a, 1));
  s.env = E(a, c7, NULL);
  s.stack = E(a, c7, NULL);
  CHECK(ct_krivine_state_decode(a, &s, &LIM, &d) == CT_OK);
  CHECK(eq(d, A(a, L(a, V(a, 8)), V(a, 7))));
  /* State.decode (State.init t) = t. */
  s.code = A(a, L(a, V(a, 0)), V(a, 3));
  s.env = NULL;
  s.stack = NULL;
  CHECK(ct_krivine_state_decode(a, &s, &LIM, &d) == CT_OK);
  CHECK(eq(d, s.code));
}

int main(void) {
  ct_arena *a;
  if (ct_arena_create(&a) != CT_OK) {
    fprintf(stderr, "test_krivine: no memory\n");
    return 1;
  }
  test_table(a);
  test_env_nth();
  test_heap_decode(a);
  test_hstep(a);
  test_decode(a);
  ct_arena_destroy(a);
  if (failures != 0) {
    fprintf(stderr, "test_krivine: %d check(s) failed\n", failures);
    return 1;
  }
  printf("test_krivine: all checks passed\n");
  return 0;
}
