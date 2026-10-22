import Start.TLCA4TUnfold

/-!
# TLCA open problem 4: the candidate `Q = M ∘ M ∘ (B M) ∘ B ∘ B` unfolds through `T`
(row M20-TLCA4-BETAETA; series V, round 4, run 2, part A)

The bounded search of this round (experiment, `docs/goal/evidence/M20-TLCA4-BETAETA.md`) finds
the family `Q_k = M ∘ Mᵏ ∘ BM ∘ Bᵏ⁺¹` with `Q₀ = T` and `Q_k = M ∘ Q_{k-1} ∘ B`.  This module
records the first instance in Lean:

* `tQ` — the polynomial `Q = M ∘ (M ∘ (BM ∘ (B ∘ B)))`;
* **`Q_unfold`** — `Q x` and `M (T (B x))` have the common weak reduct
  `M (M (B M (B (B x))))`;
* `Q_weq_MT`, `Q_betaEta_MT` — hence `Q x` is weakly, so βη-, equal to `M (T (B x))`, whose
  `M`-redex is `(T (B x)) (T (B x))`.

This is a starting point for `Q_not_fixedPoint` (not proved): the residual components of `Q x`
have no normal form, so the index of the `T` proof does not apply (see the evidence note).
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- The polynomial `Q = M ∘ (M ∘ (BM ∘ (B ∘ B)))`. -/
def tQ : Tm := comp M (comp M (comp (app B M) (comp B B)))

theorem tQ_eq_poly : tQ = polyTm ⟨0, .M⟩ [⟨0, .M⟩, ⟨1, .M⟩, ⟨0, .B⟩, ⟨0, .B⟩] := rfl

/-- The common reduct `M (M (B M (B (B x))))`. -/
def qK (x : ℕ) : Tm := app M (app M (app (app B M) (app B (app B (var x)))))

/-- **`Q x` and `M (T (B x))` have a common weak reduct.** -/
theorem Q_unfold (x : ℕ) :
    Relation.ReflTransGen WStep (app tQ (var x)) (qK x) ∧
      Relation.ReflTransGen WStep (app M (app tT (app B (var x)))) (qK x) := by
  constructor
  · -- Q x → M (P x) → M (M (P₂ x)) → M (M (BM (BBB x))) → M (M (BM (B (B x))))
    exact (((Relation.ReflTransGen.single (WStep.b _ _ _)).tail
      (WStep.appR _ (WStep.b _ _ _))).tail
      (WStep.appR _ (WStep.appR _ (WStep.b _ _ _)))).tail
      (WStep.appR _ (WStep.appR _ (WStep.appR _ (WStep.b _ _ _))))
  · -- M (T (B x)) → M (M (B (BM) B (B x))) → M (M (BM (B (B x))))
    refine (Relation.ReflTransGen.single (WStep.appR _ (WStep.b _ _ _))).tail ?_
    exact WStep.appR _ (WStep.appR _ (WStep.b _ _ _))

/-- `Q x` is weakly equal to `M (T (B x))`. -/
theorem Q_weq_MT (x : ℕ) : WEq (app tQ (var x)) (app M (app tT (app B (var x)))) :=
  (weq_of_rtg (Q_unfold x).1).trans (weq_of_rtg (Q_unfold x).2).symm

/-- The βη-form: `Q x =βη M (T (B x))`. -/
theorem Q_betaEta_MT (x : ℕ) :
    Lambda.betaEtaConv (toLam (app tQ (var x))) (toLam (app M (app tT (app B (var x))))) :=
  toLam_weq (Q_weq_MT x)

end TLCA4
