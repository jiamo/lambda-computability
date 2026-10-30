#ifndef CT_COB_H
#define CT_COB_H

/*
 * Cobham's terms for the polynomial-time functions on binary words: the Lean
 * type `CT.Cob` and its evaluation `CT.Cob.eval` (see spec/CTSpec.lean).
 *
 * Terms are immutable, live in an arena, may share subterms, and are built
 * only with the constructors below.  Every function writes its results only
 * when it returns CT_OK.
 */

#include "ct/base.h"

enum {
  CT_COB_PROJ = 0,  /* proj index                 */
  CT_COB_EMPTY = 1, /* empty                      */
  CT_COB_APP = 2,   /* app bit                    */
  CT_COB_SMASH = 3, /* smash                      */
  CT_COB_COMP = 4,  /* comp f [gs[0], ..., gs[ngs-1]] */
  CT_COB_BREC = 5   /* bRec f h0 h1 bd (f is g)   */
};

typedef struct ct_cob ct_cob;

/* A term node.  Read-only for clients. */
struct ct_cob {
  int kind;                /* one of the CT_COB_* constants */
  bool bit;                /* app: b; otherwise false */
  uint64_t index;          /* proj: i; otherwise 0 */
  const ct_cob *f;         /* comp: f; bRec: g; otherwise NULL */
  const ct_cob *h0;        /* bRec: h₀; otherwise NULL */
  const ct_cob *h1;        /* bRec: h₁; otherwise NULL */
  const ct_cob *bd;        /* bRec: the bound; otherwise NULL */
  uint64_t ngs;            /* comp: the number of gs; otherwise 0 */
  const ct_cob *const *gs; /* comp: the gs (NULL when ngs is 0) */
};

/*
 * Limits of an evaluation:
 * - `max_len`: the maximal length of every word computed by the evaluation,
 *   i.e. of the value of every subterm evaluated (a projection of an
 *   argument longer than max_len, or an `app` or `smash` that would build a
 *   longer word, fails); in particular a successful result has length at
 *   most max_len;
 * - `max_work`: the number of (sub)term evaluations, counting each step of a
 *   bounded recursion;
 * - `max_depth`: the nesting depth of the evaluation (a term of height h, a
 *   leaf having height 1, needs max_depth >= h).
 * Reaching a limit makes the evaluation return CT_ELIMIT.
 */
typedef struct ct_cob_limits {
  uint64_t max_len;
  uint64_t max_work;
  uint64_t max_depth;
} ct_cob_limits;

/* Constructors.  `ct_cob_comp` copies the array `gs` of `ngs` terms. */
ct_status ct_cob_proj(ct_arena *a, uint64_t i, const ct_cob **out);
ct_status ct_cob_empty(ct_arena *a, const ct_cob **out);
ct_status ct_cob_app(ct_arena *a, bool b, const ct_cob **out);
ct_status ct_cob_smash(ct_arena *a, const ct_cob **out);
ct_status ct_cob_comp(ct_arena *a, const ct_cob *f, const ct_cob *const *gs,
                      uint64_t ngs, const ct_cob **out);
ct_status ct_cob_brec(ct_arena *a, const ct_cob *g, const ct_cob *h0,
                      const ct_cob *h1, const ct_cob *bd, const ct_cob **out);

/*
 * `CT.Cob.eval c args`.  The words built by the evaluation are allocated in
 * `a`.  CT_EOVERFLOW if a length computation overflows, CT_ELIMIT if a limit
 * of `lim` is reached.
 */
ct_status ct_cob_eval(ct_arena *a, const ct_cob *c, const ct_vec *args,
                      const ct_cob_limits *lim, ct_word *out);

#endif
