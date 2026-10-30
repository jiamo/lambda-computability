#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "ct/base.h"

static int failures = 0;

#define CHECK(cond)                                                          \
  do {                                                                       \
    if (!(cond)) {                                                           \
      fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__, __LINE__, #cond); \
      failures++;                                                            \
    }                                                                        \
  } while (0)

/* Spells `w` into a static-free buffer supplied by the caller. */
static const char *spell(const ct_word *w, char *buf, size_t cap) {
  if (ct_word_to_string(w, buf, cap) != CT_OK) {
    return "<error>";
  }
  return buf;
}

static void test_arena(void) {
  ct_arena *a = NULL;
  void *p = NULL;
  void *q = NULL;
  size_t i;
  CHECK(ct_arena_create(&a) == CT_OK);
  CHECK(a != NULL);
  CHECK(ct_arena_alloc(a, 24, 8, &p) == CT_OK);
  CHECK(p != NULL);
  CHECK(((uintptr_t)p % 8) == 0);
  memset(p, 0xAB, 24);
  CHECK(ct_arena_alloc(a, 1, 1, &q) == CT_OK);
  CHECK(q != NULL && q != p);
  CHECK(ct_arena_alloc(a, 40, _Alignof(max_align_t), &q) == CT_OK);
  CHECK(((uintptr_t)q % _Alignof(max_align_t)) == 0);
  /* invalid sizes and alignments */
  CHECK(ct_arena_alloc(a, 0, 8, &q) == CT_EINVAL);
  CHECK(ct_arena_alloc(a, 8, 0, &q) == CT_EINVAL);
  CHECK(ct_arena_alloc(a, 8, 3, &q) == CT_EINVAL);
  CHECK(ct_arena_alloc(a, 8, 2 * _Alignof(max_align_t), &q) == CT_EINVAL);
  /* arrays: overflow-checked sizes */
  CHECK(ct_arena_alloc_array(a, 10, sizeof(uint64_t), _Alignof(uint64_t), &q) ==
        CT_OK);
  for (i = 0; i < 10; i++) {
    ((uint64_t *)q)[i] = i;
  }
  CHECK(ct_arena_alloc_array(a, SIZE_MAX / 2 + 1, 2, 1, &q) == CT_EOVERFLOW);
  CHECK(ct_arena_alloc_array(a, 0, 8, 8, &q) == CT_EINVAL);
  /* many small blocks */
  for (i = 0; i < 1000; i++) {
    CHECK(ct_arena_alloc(a, 16, _Alignof(max_align_t), &q) == CT_OK);
  }
  ct_arena_destroy(a);
  ct_arena_destroy(NULL);
}

static void test_checked(void) {
  uint64_t r = 7;
  CHECK(ct_u64_add(2, 3, &r) == CT_OK && r == 5);
  CHECK(ct_u64_add(UINT64_MAX - 1, 1, &r) == CT_OK && r == UINT64_MAX);
  r = 7;
  CHECK(ct_u64_add(UINT64_MAX, 1, &r) == CT_EOVERFLOW && r == 7);
  CHECK(ct_u64_sub(5, 3, &r) == CT_OK && r == 2);
  CHECK(ct_u64_sub(3, 3, &r) == CT_OK && r == 0);
  r = 7;
  CHECK(ct_u64_sub(3, 5, &r) == CT_EOVERFLOW && r == 7);
  CHECK(ct_u64_mul(6, 7, &r) == CT_OK && r == 42);
  CHECK(ct_u64_mul(0, UINT64_MAX, &r) == CT_OK && r == 0);
  CHECK(ct_u64_mul(UINT64_MAX, 1, &r) == CT_OK && r == UINT64_MAX);
  CHECK(ct_u64_mul((uint64_t)1 << 32, (uint64_t)1 << 31, &r) == CT_OK &&
        r == (uint64_t)1 << 63);
  r = 7;
  CHECK(ct_u64_mul((uint64_t)1 << 32, (uint64_t)1 << 32, &r) == CT_EOVERFLOW &&
        r == 7);
}

static void test_words(void) {
  ct_arena *a = NULL;
  ct_word w, u, v, e, t;
  char buf[64];
  bool b;
  CHECK(ct_arena_create(&a) == CT_OK);

  ct_word_empty(&e);
  CHECK(ct_word_length(&e) == 0);
  CHECK(strcmp(spell(&e, buf, sizeof buf), "") == 0);

  CHECK(ct_word_from_string(a, "10110", &w) == CT_OK);
  CHECK(ct_word_length(&w) == 5);
  CHECK(ct_word_get(&w, 0, &b) == CT_OK && b);
  CHECK(ct_word_get(&w, 1, &b) == CT_OK && !b);
  CHECK(ct_word_get(&w, 4, &b) == CT_OK && !b);
  CHECK(ct_word_get(&w, 5, &b) == CT_EINVAL);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "10110") == 0);
  CHECK(ct_word_from_string(a, "", &u) == CT_OK && ct_word_length(&u) == 0);
  CHECK(ct_word_from_string(a, "10a1", &u) == CT_EINVAL);

  /* to_string capacity */
  CHECK(ct_word_to_string(&w, buf, 5) == CT_EINVAL);
  CHECK(ct_word_to_string(&w, buf, 6) == CT_OK && strcmp(buf, "10110") == 0);
  CHECK(ct_word_to_string(&e, buf, 0) == CT_EINVAL);
  CHECK(ct_word_to_string(&e, buf, 1) == CT_OK && buf[0] == '\0');

  /* cons, tail */
  CHECK(ct_word_cons(a, false, &w, &u) == CT_OK);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "010110") == 0);
  CHECK(ct_word_cons(a, true, &e, &u) == CT_OK);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "1") == 0);
  ct_word_tail(&w, &u);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "0110") == 0);
  ct_word_tail(&e, &u);
  CHECK(ct_word_length(&u) == 0);

  /* take, drop */
  ct_word_take(&w, 2, &u);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "10") == 0);
  ct_word_take(&w, 0, &u);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "") == 0);
  ct_word_take(&w, 99, &u);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "10110") == 0);
  ct_word_drop(&w, 2, &u);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "110") == 0);
  ct_word_drop(&u, 1, &v);
  CHECK(strcmp(spell(&v, buf, sizeof buf), "10") == 0);
  ct_word_drop(&w, 5, &u);
  CHECK(ct_word_length(&u) == 0);
  ct_word_drop(&w, UINT64_MAX, &u);
  CHECK(ct_word_length(&u) == 0);

  /* replicate */
  CHECK(ct_word_replicate(a, 4, true, &u) == CT_OK);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "1111") == 0);
  CHECK(ct_word_replicate(a, 3, false, &u) == CT_OK);
  CHECK(strcmp(spell(&u, buf, sizeof buf), "000") == 0);
  CHECK(ct_word_replicate(a, 0, true, &u) == CT_OK && ct_word_length(&u) == 0);

  /* concat, of shared slices too */
  ct_word_drop(&w, 3, &u);   /* "10" */
  ct_word_take(&w, 3, &v);   /* "101" */
  CHECK(ct_word_concat(a, &u, &v, &t) == CT_OK);
  CHECK(strcmp(spell(&t, buf, sizeof buf), "10101") == 0);
  CHECK(ct_word_concat(a, &e, &v, &t) == CT_OK);
  CHECK(strcmp(spell(&t, buf, sizeof buf), "101") == 0);
  CHECK(ct_word_concat(a, &u, &e, &t) == CT_OK);
  CHECK(strcmp(spell(&t, buf, sizeof buf), "10") == 0);
  CHECK(ct_word_concat(a, &e, &e, &t) == CT_OK && ct_word_length(&t) == 0);

  /* equality */
  CHECK(ct_word_from_string(a, "10110", &u) == CT_OK);
  CHECK(ct_word_equal(&w, &u));
  CHECK(ct_word_from_string(a, "10111", &u) == CT_OK);
  CHECK(!ct_word_equal(&w, &u));
  CHECK(!ct_word_equal(&w, &e));
  CHECK(ct_word_equal(&e, &e));
  ct_word_take(&w, 0, &u);
  CHECK(ct_word_equal(&u, &e));
  ct_word_drop(&w, 2, &u);              /* "110" */
  CHECK(ct_word_from_string(a, "110", &v) == CT_OK);
  CHECK(ct_word_equal(&u, &v));

  /* overflow checks */
  u.len = UINT64_MAX;
  u.bits = w.bits;
  CHECK(ct_word_cons(a, true, &u, &v) == CT_EOVERFLOW);
  CHECK(ct_word_concat(a, &u, &w, &v) == CT_EOVERFLOW);

  ct_arena_destroy(a);
}

static void test_vectors(void) {
  ct_arena *a = NULL;
  ct_word ws[3];
  ct_word w;
  ct_vec v, t, c, e;
  char buf[64];
  CHECK(ct_arena_create(&a) == CT_OK);
  CHECK(ct_word_from_string(a, "1", &ws[0]) == CT_OK);
  CHECK(ct_word_from_string(a, "01", &ws[1]) == CT_OK);
  CHECK(ct_word_from_string(a, "", &ws[2]) == CT_OK);
  CHECK(ct_vec_make(a, ws, 3, &v) == CT_OK);
  CHECK(ct_vec_length(&v) == 3);
  ct_vec_get(&v, 0, &w);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "1") == 0);
  ct_vec_get(&v, 1, &w);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "01") == 0);
  ct_vec_get(&v, 2, &w);
  CHECK(ct_word_length(&w) == 0);
  /* getD: a missing index reads as the empty word */
  ct_vec_get(&v, 3, &w);
  CHECK(ct_word_length(&w) == 0);
  ct_vec_get(&v, UINT64_MAX, &w);
  CHECK(ct_word_length(&w) == 0);

  ct_vec_tail(&v, &t);
  CHECK(ct_vec_length(&t) == 2);
  ct_vec_get(&t, 0, &w);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "01") == 0);

  CHECK(ct_vec_cons(a, &ws[0], &t, &c) == CT_OK);
  CHECK(ct_vec_length(&c) == 3);
  ct_vec_get(&c, 0, &w);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "1") == 0);
  ct_vec_get(&c, 1, &w);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "01") == 0);

  CHECK(ct_vec_make(a, ws, 0, &e) == CT_OK && ct_vec_length(&e) == 0);
  ct_vec_get(&e, 0, &w);
  CHECK(ct_word_length(&w) == 0);
  ct_vec_tail(&e, &t);
  CHECK(ct_vec_length(&t) == 0);
  CHECK(ct_vec_cons(a, &ws[1], &e, &c) == CT_OK && ct_vec_length(&c) == 1);
  ct_vec_get(&c, 0, &w);
  CHECK(strcmp(spell(&w, buf, sizeof buf), "01") == 0);
  ct_arena_destroy(a);
}

int main(void) {
  test_arena();
  test_checked();
  test_words();
  test_vectors();
  if (failures != 0) {
    fprintf(stderr, "test_base: %d failure(s)\n", failures);
    return 1;
  }
  printf("test_base: all checks passed\n");
  return 0;
}
