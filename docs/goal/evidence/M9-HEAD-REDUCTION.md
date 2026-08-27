# M9-HEAD-REDUCTION

**Status:** DONE_STRONG

`Start/HeadNormal.lean` defines head normal forms and head normalizability (`Lambda.HasHnf`)
through *arbitrary* reductions.  That definition says nothing about *how* a head normal form is
found, so the structural laws of head normalizability — that it is inherited by the function part
of an application, and that it cannot be created by substituting into a head-divergent term —
were out of reach.  This task builds the head reduction strategy and proves them.

## The strategy — `Start/HeadReduction.lean`

* **`Lambda.hstep`** — one head step: a weak head step of `Start/WeakHead.lean`, or a head step
  underneath a leading abstraction.  `Lambda.hstep_imp_step` and `Lambda.hstep_reduces` place it
  inside ordinary β-reduction, and `Lambda.hstep_deterministic` shows the strategy is
  deterministic.
* **`Lambda.isHnf_iff_no_hstep`** — head normal forms are exactly the terms with no head redex
  (`Lambda.not_hstep_of_isHnf` and `Lambda.exists_hstep_of_not_isHnf`).  Supporting facts:
  `Lambda.IsHnf.of_lam`, `Lambda.isWhnf_of_neutral`, `Lambda.IsWhnf.of_isHnf`.
* **`Lambda.HNIn`, `Lambda.HasHeadEval`** — termination of the strategy within `n` steps, and at
  all, with the expected closure lemmas (`Lambda.hnIn_mono`, `Lambda.hasHeadEval_of_hstep`,
  `Lambda.hnIn_lam`, `Lambda.hasHeadEval_lam`, `Lambda.exists_hnf_of_hnIn`).

## Head normalization

* `Lambda.IsHnf.reduces_shape` — a head normal form stays one under reduction and keeps its
  abstraction prefix (`Lambda.lamCount`).
* `Lambda.hasHeadEval_of_whnIn` — if the weak head strategy terminates and every weak head normal
  form reduct is head-evaluable, then the head strategy terminates.
* `Lambda.hasHeadEval_peel` — the inductive step: standardization for weak head reduction
  (`Lambda.hasWhnfEval_of_reduces_whnf`) drives the term to a weak head normal form, which
  confluence identifies as neutral — already a head normal form — or as an abstraction whose body
  has one abstraction fewer in front of its head normal form.
* **`Lambda.hasHnf_iff_hasHeadEval`** — a term has a head normal form exactly when the head
  strategy terminates on it.

## Structural consequences

* `Lambda.hstep_subst` — head steps are preserved by substitution;
* **`Lambda.hasHnf_of_hasHnf_subst`** — if `t[s/x]` has a head normal form then so does `t`;
* **`Lambda.HasHnf.app_left`** — if `M N` has a head normal form then so does `M`;
* `Lambda.hasHnf_lam_iff` — an abstraction has a head normal form exactly when its body does.

## Solvability, syntactically — `Start/HeadSolvable.lean`

* `Lambda.hasHnf_appList_left` — head normalizability of `t M₁ … Mₙ` is inherited by `t`;
* **`Lambda.hasHnf_of_solvable`** — every solvable term has a head normal form: by confluence the
  convertibility `t M₁ … Mₙ ≃ I` is a reduction to the normal form `I`, which is a head normal
  form, and the previous lemma carries this back to `t`.

`Start/HnfSolvable.lean` now takes this direction of `Lambda.solvable_iff_hasHnf` from the
syntactic proof, so Wadsworth's characterization for closed terms no longer depends on the graph
model (`GraphModel.hasHnf_of_solvable` remains available as the semantic proof).

## Gates

* `python3 scripts/goal_state.py validate`
* `lake build` — clean, no `sorry`, axioms `propext, Classical.choice, Quot.sound`.
