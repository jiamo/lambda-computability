#ifndef CT_BASE_H
#define CT_BASE_H

/*
 * The base of the C implementation: status codes, arenas, checked uint64_t
 * arithmetic, bit words (the Lean type `CT.Word = List Bool`) and vectors of
 * words.
 *
 * Conventions (see README.md):
 * - every function that can fail returns a `ct_status` and writes its results
 *   through pointers; results are written only when it returns `CT_OK`;
 * - output objects must not overlap the inputs of the same call;
 * - memory comes from arenas; nothing is freed individually.
 */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

/* ------------------------------------------------------------------------ */
/* Status codes                                                               */
/* ------------------------------------------------------------------------ */

typedef enum ct_status {
  CT_OK = 0,        /* success; the results equal the Lean values */
  CT_ENOMEM = 1,    /* the allocator failed */
  CT_EOVERFLOW = 2, /* a uint64_t / size_t computation would wrap around */
  CT_ELIMIT = 3,    /* an explicit limit (fuel, nodes, length, depth) was hit */
  CT_EINVAL = 4     /* an argument is outside the documented domain */
} ct_status;

/* ------------------------------------------------------------------------ */
/* Arenas                                                                     */
/* ------------------------------------------------------------------------ */

/*
 * An arena owns every block it hands out.  Blocks stay valid until the arena
 * is destroyed; `ct_arena_destroy` releases all of them at once.
 */
typedef struct ct_arena ct_arena;

/* Creates an empty arena.  CT_ENOMEM if the allocator fails. */
ct_status ct_arena_create(ct_arena **out);

/*
 * Allocates `size` bytes aligned to `align`.
 * `align` must be a power of two not larger than `_Alignof(max_align_t)`, and
 * `size` must be positive; otherwise CT_EINVAL.  The block is uninitialized.
 */
ct_status ct_arena_alloc(ct_arena *a, size_t size, size_t align, void **out);

/*
 * Allocates an array of `count` elements of `elem_size` bytes each, aligned
 * to `align`.  CT_EOVERFLOW if `count * elem_size` does not fit in a size_t;
 * otherwise as `ct_arena_alloc(a, count * elem_size, align, out)`.
 */
ct_status ct_arena_alloc_array(ct_arena *a, size_t count, size_t elem_size,
                               size_t align, void **out);

/* Releases the arena and every block allocated from it.  `a` may be NULL. */
void ct_arena_destroy(ct_arena *a);

/* ------------------------------------------------------------------------ */
/* Checked uint64_t arithmetic                                                */
/* ------------------------------------------------------------------------ */

/* *out = x + y, or CT_EOVERFLOW if the sum exceeds UINT64_MAX. */
ct_status ct_u64_add(uint64_t x, uint64_t y, uint64_t *out);

/* *out = x - y, or CT_EOVERFLOW (underflow) if x < y. */
ct_status ct_u64_sub(uint64_t x, uint64_t y, uint64_t *out);

/* *out = x * y, or CT_EOVERFLOW if the product exceeds UINT64_MAX. */
ct_status ct_u64_mul(uint64_t x, uint64_t y, uint64_t *out);

/* ------------------------------------------------------------------------ */
/* Bit words: the Lean type `CT.Word = List Bool`                             */
/* ------------------------------------------------------------------------ */

/*
 * A word is an immutable value: `len` bits, bit i being `bits[i]` (0 or 1).
 * When `len` is 0, `bits` is not read.  Otherwise `bits` points to `len`
 * consecutive bytes, each 0 or 1, inside a block of an arena; the bits are
 * shared between words (tail, take and drop do not copy): never write them.
 */
typedef struct ct_word {
  uint64_t len;
  const uint8_t *bits;
} ct_word;

/* The empty word `[]`. */
void ct_word_empty(ct_word *out);

/* `w.length`. */
uint64_t ct_word_length(const ct_word *w);

/* `w[i]`; CT_EINVAL if i >= length. */
ct_status ct_word_get(const ct_word *w, uint64_t i, bool *out);

/*
 * The word spelled by the NUL-terminated string `s` ('0' = false,
 * '1' = true); CT_EINVAL if `s` contains another character.
 */
ct_status ct_word_from_string(ct_arena *a, const char *s, ct_word *out);

/*
 * Writes the '0'/'1' spelling of `w` and a terminating NUL into `buf`, of
 * capacity `cap` bytes; CT_EINVAL if `cap < length + 1`.
 */
ct_status ct_word_to_string(const ct_word *w, char *buf, size_t cap);

/* `b :: w`; CT_EOVERFLOW if the length would exceed UINT64_MAX. */
ct_status ct_word_cons(ct_arena *a, bool b, const ct_word *w, ct_word *out);

/* `w.tail` (the tail of `[]` is `[]`).  Shares the bits of `w`. */
void ct_word_tail(const ct_word *w, ct_word *out);

/* `w.take n`.  Shares the bits of `w`. */
void ct_word_take(const ct_word *w, uint64_t n, ct_word *out);

/* `w.drop n`.  Shares the bits of `w`. */
void ct_word_drop(const ct_word *w, uint64_t n, ct_word *out);

/* `List.replicate n b`. */
ct_status ct_word_replicate(ct_arena *a, uint64_t n, bool b, ct_word *out);

/* `u ++ v`; CT_EOVERFLOW if the length would exceed UINT64_MAX. */
ct_status ct_word_concat(ct_arena *a, const ct_word *u, const ct_word *v,
                         ct_word *out);

/* `u = v`. */
bool ct_word_equal(const ct_word *u, const ct_word *v);

/* ------------------------------------------------------------------------ */
/* Vectors of words (`List Word`, read with `getD _ _ []`)                    */
/* ------------------------------------------------------------------------ */

/* An immutable vector of `len` words; the items live in an arena. */
typedef struct ct_vec {
  uint64_t len;
  const ct_word *items;
} ct_vec;

/* The vector `[ws[0], ..., ws[n-1]]` (the word values are copied). */
ct_status ct_vec_make(ct_arena *a, const ct_word *ws, uint64_t n, ct_vec *out);

/* `v.length`. */
uint64_t ct_vec_length(const ct_vec *v);

/* `v.getD i []`: a missing index reads as the empty word. */
void ct_vec_get(const ct_vec *v, uint64_t i, ct_word *out);

/* `v.tail`.  Shares the items of `v`. */
void ct_vec_tail(const ct_vec *v, ct_vec *out);

/* `w :: v`; CT_EOVERFLOW if the length would exceed UINT64_MAX. */
ct_status ct_vec_cons(ct_arena *a, const ct_word *w, const ct_vec *v,
                      ct_vec *out);

#endif
