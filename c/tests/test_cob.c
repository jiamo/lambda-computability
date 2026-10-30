#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "ct/cob.h"

static int failures = 0;

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond); \
      failures++;                                                            \
    }                                                                        \
  } while (0)

static ct_arena *arena;
static const ct_cob_limits LIM = {1u << 20, 1u << 20, 1000};

static const ct_cob *Proj(uint64_t i) {
  const ct_cob *c = NULL;
  if (ct_cob_proj(arena, i, &c) != CT_OK) failures++;
  return c;
}
static const ct_cob *Empty(void) {
  const ct_cob *c = NULL;
  if (ct_cob_empty(arena, &c) != CT_OK) failures++;
  return c;
}
static const ct_cob *App(bool b) {
  const ct_cob *c = NULL;
  if (ct_cob_app(arena, b, &c) != CT_OK) failures++;
  return c;
}
static const ct_cob *Smash(void) {
  const ct_cob *c = NULL;
  if (ct_cob_smash(arena, &c) != CT_OK) failures++;
  return c;
}
static const ct_cob *Comp(const ct_cob *f, const ct_cob *const *gs,
                          uint64_t n) {
  const ct_cob *c = NULL;
  if (ct_cob_comp(arena, f, gs, n, &c) != CT_OK) failures++;
  return c;
}
static const ct_cob *Comp1(const ct_cob *f, const ct_cob *g) {
  const ct_cob *gs[1];
  gs[0] = g;
  return Comp(f, gs, 1);
}
static const ct_cob *Comp2(const ct_cob *f, const ct_cob *g0,
                           const ct_cob *g1) {
  const ct_cob *gs[2];
  gs[0] = g0;
  gs[1] = g1;
  return Comp(f, gs, 2);
}
static const ct_cob *BRec(const ct_cob *g, const ct_cob *h0, const ct_cob *h1,
                          const ct_cob *bd) {
  const ct_cob *c = NULL;
  if (ct_cob_brec(arena, g, h0, h1, bd, &c) != CT_OK) failures++;
  return c;
}

/* Builds the vector of the words spelled by `strs`. */
static ct_vec args_of(const char *const *strs, uint64_t n) {
  ct_word ws[8];
  ct_vec v;
  uint64_t i;
  v.len = 0;
  v.items = NULL;
  for (i = 0; i < n; i++) {
    if (ct_word_from_string(arena, strs[i], &ws[i]) != CT_OK) failures++;
  }
  if (ct_vec_make(arena, ws, n, &v) != CT_OK) failures++;
  return v;
}

/* Evaluates `c` on `strs` and compares the spelling of the result. */
static int eval_is(const ct_cob *c, const char *const *strs, uint64_t n,
                   const char *expected) {
  ct_vec v = args_of(strs, n);
  ct_word w;
  char buf[256];
  if (ct_cob_eval(arena, c, &v, &LIM, &w) != CT_OK) {
    return 0;
  }
  if (ct_word_to_string(&w, buf, sizeof buf) != CT_OK) {
    return 0;
  }
  if (strcmp(buf, expected) != 0) {
    fprintf(stderr, "got \"%s\", expected \"%s\"\n", buf, expected);
    return 0;
  }
  return 1;
}

int main(void) {
  const char *const a2[2] = {"101", "11"};
  const char *const a3[3] = {"0", "", "1101"};
  const char *const a1[1] = {"1001"};
  const ct_cob *id;
  const ct_cob *concat;
  const ct_cob *bound;
  const ct_cob *c;
  ct_vec v;
  ct_word w;
  ct_cob_limits lim;
  if (ct_arena_create(&arena) != CT_OK) {
    return 1;
  }

  /* proj: missing arguments read as the empty word */
  CHECK(eval_is(Proj(0), a2, 2, "101"));
  CHECK(eval_is(Proj(1), a2, 2, "11"));
  CHECK(eval_is(Proj(2), a2, 2, ""));
  CHECK(eval_is(Proj(0), NULL, 0, ""));
  CHECK(eval_is(Proj(2), a3, 3, "1101"));

  /* empty */
  CHECK(eval_is(Empty(), a2, 2, ""));

  /* app b: b :: first argument */
  CHECK(eval_is(App(true), a2, 2, "1101"));
  CHECK(eval_is(App(false), a2, 2, "0101"));
  CHECK(eval_is(App(true), NULL, 0, "1"));

  /* smash: |x| * |y| ones */
  CHECK(eval_is(Smash(), a2, 2, "111111"));
  CHECK(eval_is(Smash(), a3, 3, ""));
  CHECK(eval_is(Smash(), a1, 1, ""));

  /* composition */
  CHECK(eval_is(Comp1(App(false), Proj(1)), a2, 2, "011"));
  CHECK(eval_is(Comp2(Smash(), Proj(1), Proj(0)), a2, 2, "111111"));
  CHECK(eval_is(Comp2(Proj(1), Proj(1), Comp1(App(true), Proj(0))), a2, 2,
                "1101"));
  CHECK(eval_is(Comp(Proj(0), NULL, 0), a2, 2, ""));

  /* bRec: the identity by recursion on notation:
       id [] = [],  id (b :: x') = (b :: id x').take |b :: x'| */
  id = BRec(Empty(), Comp1(App(false), Proj(1)), Comp1(App(true), Proj(1)),
            Proj(0));
  CHECK(eval_is(id, a1, 1, "1001"));
  CHECK(eval_is(id, a2, 2, "101"));
  CHECK(eval_is(id, NULL, 0, ""));

  /* bRec: concatenation, by recursion on the first argument:
       x ++ y with [] ++ y = y and (b :: x') ++ y = b :: (x' ++ y),
       bounded by smash (1 :: x) (1 :: y), of length (|x| + 1) (|y| + 1). */
  bound = Comp2(Smash(), Comp1(App(true), Proj(0)), Comp1(App(true), Proj(1)));
  concat = BRec(Proj(0), Comp1(App(false), Proj(1)), Comp1(App(true), Proj(1)),
                bound);
  CHECK(eval_is(concat, a2, 2, "10111"));
  CHECK(eval_is(concat, a3, 3, "0"));
  {
    const char *const b2[2] = {"", "0110"};
    const char *const c2[2] = {"1100", ""};
    CHECK(eval_is(concat, b2, 2, "0110"));
    CHECK(eval_is(concat, c2, 2, "1100"));
  }

  /* a bound shorter than the step result truncates it: bound = proj 1 */
  c = BRec(Empty(), Comp1(App(false), Proj(1)), Comp1(App(true), Proj(1)),
           Proj(1));
  {
    const char *const d2[2] = {"111", "11"};
    /* value on the suffixes: [] -> "", "1" -> "1".take 2 = "1",
       "11" -> "11".take 2 = "11", "111" -> "111".take 2 = "11" */
    CHECK(eval_is(c, d2, 2, "11"));
  }

  /* limits */
  v = args_of(a2, 2);
  lim = LIM;
  lim.max_len = 5;
  CHECK(ct_cob_eval(arena, Smash(), &v, &lim, &w) == CT_ELIMIT);
  lim.max_len = 6;
  CHECK(ct_cob_eval(arena, Smash(), &v, &lim, &w) == CT_OK && w.len == 6);
  lim.max_len = 3;
  CHECK(ct_cob_eval(arena, App(true), &v, &lim, &w) == CT_ELIMIT);
  /* a projection is a computed word too: proj 0 selects a word of length 3 */
  CHECK(ct_cob_eval(arena, Proj(0), &v, &lim, &w) == CT_OK && w.len == 3);
  lim.max_len = 2;
  CHECK(ct_cob_eval(arena, Proj(0), &v, &lim, &w) == CT_ELIMIT);
  CHECK(ct_cob_eval(arena, Proj(1), &v, &lim, &w) == CT_OK && w.len == 2);
  lim = LIM;
  lim.max_work = 3;
  CHECK(ct_cob_eval(arena, concat, &v, &lim, &w) == CT_ELIMIT);
  lim = LIM;
  lim.max_depth = 1;
  CHECK(ct_cob_eval(arena, Comp1(App(false), Proj(1)), &v, &lim, &w) ==
        CT_ELIMIT);
  lim.max_depth = 2;
  CHECK(ct_cob_eval(arena, Comp1(App(false), Proj(1)), &v, &lim, &w) == CT_OK);

  ct_arena_destroy(arena);
  if (failures != 0) {
    fprintf(stderr, "test_cob: %d failure(s)\n", failures);
    return 1;
  }
  printf("test_cob: all checks passed\n");
  return 0;
}
