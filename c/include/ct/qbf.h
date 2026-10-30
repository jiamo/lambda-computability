#ifndef CT_QBF_H
#define CT_QBF_H

/*
 * Quantified Boolean formulas: the Lean type `CT.QBF` and its evaluation
 * `CT.QBF.eval` (see spec/CTSpec.lean).
 *
 * Formulas are immutable, live in an arena, may share subformulas, and are
 * built only with the constructors below.  Every function writes its results
 * only when it returns CT_OK.
 */

#include "ct/base.h"

enum {
  CT_QBF_VAR = 0,  /* var var                    */
  CT_QBF_NEG = 1,  /* neg left                   */
  CT_QBF_CONJ = 2, /* conj left right            */
  CT_QBF_DISJ = 3, /* disj left right            */
  CT_QBF_ALL = 4,  /* all var left  (∀ var, left) */
  CT_QBF_EX = 5    /* ex var left   (∃ var, left) */
};

typedef struct ct_qbf ct_qbf;

/* A formula node.  Read-only for clients. */
struct ct_qbf {
  int kind;           /* one of the CT_QBF_* constants */
  uint64_t var;       /* var, all, ex: the variable; otherwise 0 */
  const ct_qbf *left; /* the (first) subformula, or NULL */
  const ct_qbf *right; /* conj, disj: the second subformula, or NULL */
};

/* Constructors: `var i`, `neg p`, `conj p q`, `disj p q`, `all i p`,
   `ex i p`. */
ct_status ct_qbf_var(ct_arena *a, uint64_t i, const ct_qbf **out);
ct_status ct_qbf_neg(ct_arena *a, const ct_qbf *p, const ct_qbf **out);
ct_status ct_qbf_conj(ct_arena *a, const ct_qbf *p, const ct_qbf *q,
                      const ct_qbf **out);
ct_status ct_qbf_disj(ct_arena *a, const ct_qbf *p, const ct_qbf *q,
                      const ct_qbf **out);
ct_status ct_qbf_all(ct_arena *a, uint64_t i, const ct_qbf *p,
                     const ct_qbf **out);
ct_status ct_qbf_ex(ct_arena *a, uint64_t i, const ct_qbf *p,
                    const ct_qbf **out);

/*
 * `CT.QBF.eval σ p`, where σ i = assign[i] for i < n and σ i = false for
 * i >= n.  `assign` may be NULL when n is 0.  CT_ELIMIT if the evaluation
 * nests deeper than `max_depth` (a formula of height h, a variable having
 * height 1, needs max_depth >= h).
 */
ct_status ct_qbf_eval(const ct_qbf *p, const bool *assign, uint64_t n,
                      uint64_t max_depth, bool *out);

#endif
