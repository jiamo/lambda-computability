#include "ct/base.h"

#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------------ */
/* Arenas                                                                     */
/* ------------------------------------------------------------------------ */

/*
 * An arena is a list of blocks, each obtained from malloc.  Every block is
 * released by ct_arena_destroy.
 */
struct ct_arena_block {
  void *mem;
  struct ct_arena_block *next;
};

struct ct_arena {
  struct ct_arena_block *blocks;
};

ct_status ct_arena_create(ct_arena **out) {
  ct_arena *a = malloc(sizeof(ct_arena));
  if (a == NULL) {
    return CT_ENOMEM;
  }
  a->blocks = NULL;
  *out = a;
  return CT_OK;
}

ct_status ct_arena_alloc(ct_arena *a, size_t size, size_t align, void **out) {
  struct ct_arena_block *b;
  void *mem;
  if (size == 0 || align == 0 || (align & (align - 1)) != 0 ||
      align > _Alignof(max_align_t)) {
    return CT_EINVAL;
  }
  b = malloc(sizeof(struct ct_arena_block));
  if (b == NULL) {
    return CT_ENOMEM;
  }
  /* malloc returns storage aligned for every fundamental alignment. */
  mem = malloc(size);
  if (mem == NULL) {
    free(b);
    return CT_ENOMEM;
  }
  b->mem = mem;
  b->next = a->blocks;
  a->blocks = b;
  *out = mem;
  return CT_OK;
}

ct_status ct_arena_alloc_array(ct_arena *a, size_t count, size_t elem_size,
                               size_t align, void **out) {
  if (count != 0 && elem_size > SIZE_MAX / count) {
    return CT_EOVERFLOW;
  }
  return ct_arena_alloc(a, count * elem_size, align, out);
}

void ct_arena_destroy(ct_arena *a) {
  struct ct_arena_block *b;
  struct ct_arena_block *next;
  if (a == NULL) {
    return;
  }
  b = a->blocks;
  while (b != NULL) {
    next = b->next;
    free(b->mem);
    free(b);
    b = next;
  }
  free(a);
}

/* ------------------------------------------------------------------------ */
/* Checked uint64_t arithmetic                                                */
/* ------------------------------------------------------------------------ */

ct_status ct_u64_add(uint64_t x, uint64_t y, uint64_t *out) {
  if (x > UINT64_MAX - y) {
    return CT_EOVERFLOW;
  }
  *out = x + y;
  return CT_OK;
}

ct_status ct_u64_sub(uint64_t x, uint64_t y, uint64_t *out) {
  if (x < y) {
    return CT_EOVERFLOW;
  }
  *out = x - y;
  return CT_OK;
}

ct_status ct_u64_mul(uint64_t x, uint64_t y, uint64_t *out) {
  if (x != 0 && y > UINT64_MAX / x) {
    return CT_EOVERFLOW;
  }
  *out = x * y;
  return CT_OK;
}

/* ------------------------------------------------------------------------ */
/* Bit words                                                                  */
/* ------------------------------------------------------------------------ */

/* Allocates the storage of a word of `len` > 0 bits. */
static ct_status bits_alloc(ct_arena *a, uint64_t len, uint8_t **out) {
  size_t n = (size_t)len;
  void *mem;
  ct_status st;
  if ((uint64_t)n != len) {
    return CT_EOVERFLOW;
  }
  st = ct_arena_alloc(a, n, 1, &mem);
  if (st != CT_OK) {
    return st;
  }
  *out = mem;
  return CT_OK;
}

void ct_word_empty(ct_word *out) {
  out->len = 0;
  out->bits = NULL;
}

uint64_t ct_word_length(const ct_word *w) { return w->len; }

ct_status ct_word_get(const ct_word *w, uint64_t i, bool *out) {
  if (i >= w->len) {
    return CT_EINVAL;
  }
  *out = w->bits[i] != 0;
  return CT_OK;
}

ct_status ct_word_from_string(ct_arena *a, const char *s, ct_word *out) {
  size_t n = strlen(s);
  size_t i;
  uint8_t *bits;
  ct_status st;
  if (n == 0) {
    out->len = 0;
    out->bits = NULL;
    return CT_OK;
  }
  st = bits_alloc(a, n, &bits);
  if (st != CT_OK) {
    return st;
  }
  for (i = 0; i < n; i++) {
    if (s[i] == '0') {
      bits[i] = 0;
    } else if (s[i] == '1') {
      bits[i] = 1;
    } else {
      return CT_EINVAL;
    }
  }
  out->len = n;
  out->bits = bits;
  return CT_OK;
}

ct_status ct_word_to_string(const ct_word *w, char *buf, size_t cap) {
  uint64_t len = w->len;
  uint64_t i;
  if (cap == 0 || len > cap - 1) {
    return CT_EINVAL;
  }
  for (i = 0; i < len; i++) {
    buf[i] = w->bits[i] != 0 ? '1' : '0';
  }
  buf[len] = '\0';
  return CT_OK;
}

ct_status ct_word_cons(ct_arena *a, bool b, const ct_word *w, ct_word *out) {
  uint64_t len = w->len;
  uint8_t *bits;
  ct_status st;
  if (len == UINT64_MAX) {
    return CT_EOVERFLOW;
  }
  st = bits_alloc(a, len + 1, &bits);
  if (st != CT_OK) {
    return st;
  }
  bits[0] = b ? 1 : 0;
  if (len > 0) {
    memcpy(bits + 1, w->bits, (size_t)len);
  }
  out->len = len + 1;
  out->bits = bits;
  return CT_OK;
}

void ct_word_drop(const ct_word *w, uint64_t n, ct_word *out) {
  uint64_t len = w->len;
  if (n >= len) {
    out->len = 0;
    out->bits = NULL;
  } else {
    out->len = len - n;
    out->bits = w->bits + n;
  }
}

void ct_word_tail(const ct_word *w, ct_word *out) { ct_word_drop(w, 1, out); }

void ct_word_take(const ct_word *w, uint64_t n, ct_word *out) {
  uint64_t len = w->len;
  out->len = n < len ? n : len;
  out->bits = w->bits;
}

ct_status ct_word_replicate(ct_arena *a, uint64_t n, bool b, ct_word *out) {
  uint8_t *bits;
  ct_status st;
  if (n == 0) {
    out->len = 0;
    out->bits = NULL;
    return CT_OK;
  }
  st = bits_alloc(a, n, &bits);
  if (st != CT_OK) {
    return st;
  }
  memset(bits, b ? 1 : 0, (size_t)n);
  out->len = n;
  out->bits = bits;
  return CT_OK;
}

ct_status ct_word_concat(ct_arena *a, const ct_word *u, const ct_word *v,
                         ct_word *out) {
  uint64_t ul = u->len;
  uint64_t vl = v->len;
  uint8_t *bits;
  ct_status st;
  if (ul > UINT64_MAX - vl) {
    return CT_EOVERFLOW;
  }
  if (ul + vl == 0) {
    out->len = 0;
    out->bits = NULL;
    return CT_OK;
  }
  st = bits_alloc(a, ul + vl, &bits);
  if (st != CT_OK) {
    return st;
  }
  if (ul > 0) {
    memcpy(bits, u->bits, (size_t)ul);
  }
  if (vl > 0) {
    memcpy(bits + ul, v->bits, (size_t)vl);
  }
  out->len = ul + vl;
  out->bits = bits;
  return CT_OK;
}

bool ct_word_equal(const ct_word *u, const ct_word *v) {
  uint64_t i;
  if (u->len != v->len) {
    return false;
  }
  for (i = 0; i < u->len; i++) {
    if (u->bits[i] != v->bits[i]) {
      return false;
    }
  }
  return true;
}

/* ------------------------------------------------------------------------ */
/* Vectors of words                                                           */
/* ------------------------------------------------------------------------ */

/* Allocates the storage of a vector of `n` > 0 words. */
static ct_status items_alloc(ct_arena *a, uint64_t n, ct_word **out) {
  size_t cnt = (size_t)n;
  void *mem;
  ct_status st;
  if ((uint64_t)cnt != n) {
    return CT_EOVERFLOW;
  }
  st = ct_arena_alloc_array(a, cnt, sizeof(ct_word), _Alignof(ct_word), &mem);
  if (st != CT_OK) {
    return st;
  }
  *out = mem;
  return CT_OK;
}

ct_status ct_vec_make(ct_arena *a, const ct_word *ws, uint64_t n, ct_vec *out) {
  ct_word *items;
  ct_status st;
  if (n == 0) {
    out->len = 0;
    out->items = NULL;
    return CT_OK;
  }
  st = items_alloc(a, n, &items);
  if (st != CT_OK) {
    return st;
  }
  memcpy(items, ws, (size_t)n * sizeof(ct_word));
  out->len = n;
  out->items = items;
  return CT_OK;
}

uint64_t ct_vec_length(const ct_vec *v) { return v->len; }

void ct_vec_get(const ct_vec *v, uint64_t i, ct_word *out) {
  if (i < v->len) {
    *out = v->items[i];
  } else {
    out->len = 0;
    out->bits = NULL;
  }
}

void ct_vec_tail(const ct_vec *v, ct_vec *out) {
  uint64_t n = v->len;
  if (n == 0) {
    out->len = 0;
    out->items = NULL;
  } else {
    out->len = n - 1;
    out->items = v->items + 1;
  }
}

ct_status ct_vec_cons(ct_arena *a, const ct_word *w, const ct_vec *v,
                      ct_vec *out) {
  uint64_t n = v->len;
  ct_word *items;
  ct_status st;
  if (n == UINT64_MAX) {
    return CT_EOVERFLOW;
  }
  st = items_alloc(a, n + 1, &items);
  if (st != CT_OK) {
    return st;
  }
  items[0] = *w;
  if (n > 0) {
    memcpy(items + 1, v->items, (size_t)n * sizeof(ct_word));
  }
  out->len = n + 1;
  out->items = items;
  return CT_OK;
}
