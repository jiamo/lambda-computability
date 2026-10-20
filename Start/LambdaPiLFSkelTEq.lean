/-
**The skeleton under raw β- and η-steps** — task `M23-LF-EQUIV-COMPLETE` (round 10, part C).

The first missing lemma of round 9 was `skel_teq` (the skeleton of a type-level term is invariant
under the declarative equality `TEq`).  The first question was whether `skel` is invariant under
single *raw* β- and η-steps, in which case `skel_teq` would follow from
`TEq.betaEtaConv` without any validity lemma for `TEq`.

* `LambdaPi.skel_eta` — **η is harmless**: `skel Γs (λA. (↑f) 0) = skel Γs f` for every raw `f`;
* `LambdaPi.skel_beta_raw_counterexample` — **raw β is not**: the β-step
  `(λx:∗. x) (Πy:∗. ∗) ⟶ Πy:∗. ∗` changes the skeleton from `base` to `base → base`.  The
  bound variable sits in a skeleton-relevant (head) position of the body, and the argument
  substituted there has an arrow skeleton.  In a well-typed type-level redex the bound variable
  is an object variable and never occurs in such a position (`skel_step` uses `TypeLevel`), so
  the invariance genuinely needs typing information on the redex;
* `LambdaPi.skel_not_betaEta_invariant` — consequently the skeleton is not invariant under raw
  βη-conversion, and `skel_teq` cannot be obtained from `TEq.betaEtaConv` alone.

So `skel_teq` needs the typing of every type-level redex occurring in a `TEq` derivation, i.e. a
validity lemma for `TEq` (see `docs/goal/evidence/M23-LF-EQUIV.md`, round 10).
-/

import Start.LambdaPiLFFundamental

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-- **The skeleton is invariant under raw η-expansion.** -/
theorem skel_eta (Γs : List STy) (A f : Tm) :
    skel Γs (lam A (app (shift f) (var 0))) = skel Γs f := by
  simp only [skel_lam, skel_app, shift]
  exact skel_rename_succ _ _ _

/-- **The skeleton is not invariant under raw β-steps.** -/
theorem skel_beta_raw_counterexample :
    ∃ t t' : Tm, Step t t' ∧ skel [] t ≠ skel [] t' := by
  refine ⟨app (lam (sort Srt.star) (var 0)) (pi (sort Srt.star) (sort Srt.star)),
    (var 0)[pi (sort Srt.star) (sort Srt.star)], Step.beta _ _ _, ?_⟩
  simp [inst, skel]

/-- The skeleton is not invariant under raw βη-conversion. -/
theorem skel_not_betaEta_invariant :
    ¬ ∀ (Γs : List STy) (t t' : Tm), BetaEtaConv t t' → skel Γs t = skel Γs t' := by
  intro h
  obtain ⟨t, t', hst, hne⟩ := skel_beta_raw_counterexample
  exact hne (h [] t t' ((BetaEtaConv.refl _).step (Or.inl hst)))

end LambdaPi
