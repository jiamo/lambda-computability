import Start.TLCA4StatmanProof

/-!
# TLCA open problem 4: the unfolding of `T = B M (B (B M) B)` (row M20-TLCA4-T-NOT-FIXPOINT;
series V, round 3, run 1, part A5)

With Statman's first step proved (`statmanStepOne`), Problem 5.1 is a question about polynomials
(`problemFiveOne_iff_polyFiveOne`).  Imamura's polynomial `T = B M (B (B M) B)` has the Böhm tree
of a fixed-point combinator; this module records its weak unfolding (Imamura, §4.2), with
`A₀ = B M (B x)` and `Aₙ₊₁ = B x Aₙ`:

* `tA_app` — `Aₙ Z →w xⁿ (M (B x Z))`;
* **`T_unfold`** — `T x →w M A₀`;
* **`MtA_step`** — `M Aₙ →w xⁿ (M Aₙ₊₁)`;
* `TNotFixedPoint` — the open statement `¬ T x =βη x (T x)` (stated only; **not** proved).
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- Imamura's polynomial `T = B M (B (B M) B)`. -/
def tT : Tm := app (app B M) (app (app B (app B M)) B)

theorem tT_eq_poly : tT = polyTm ⟨0, .M⟩ [⟨1, .M⟩, ⟨0, .B⟩] := rfl

/-- `A₀ = B M (B x)`, `Aₙ₊₁ = B x Aₙ`. -/
def tA (x : ℕ) : ℕ → Tm
  | 0 => app (app B M) (app B (var x))
  | n + 1 => app (app B (var x)) (tA x n)

theorem tA_app (x : ℕ) : ∀ (n : ℕ) (Z : Tm),
    Relation.ReflTransGen WStep (app (tA x n) Z) (iterX x n (app M (app (app B (var x)) Z)))
  | 0, _ => .single (WStep.b _ _ _)
  | n + 1, Z => (Relation.ReflTransGen.single (WStep.b _ _ _)).trans (rtg_appR _ (tA_app x n Z))

/-- **`T x →w M A₀`.** -/
theorem T_unfold (x : ℕ) : Relation.ReflTransGen WStep (app tT (var x)) (app M (tA x 0)) :=
  (Relation.ReflTransGen.single (WStep.b _ _ _)).tail (WStep.appR _ (WStep.b _ _ _))

/-- **`M Aₙ →w xⁿ (M Aₙ₊₁)`.** -/
theorem MtA_step (x n : ℕ) :
    Relation.ReflTransGen WStep (app M (tA x n)) (iterX x n (app M (tA x (n + 1)))) :=
  (Relation.ReflTransGen.single (WStep.m _)).trans (tA_app x n (tA x n))

/-- The open statement for `T`: it is not a βη fixed-point combinator.  Stated only; **not**
proved. -/
def TNotFixedPoint : Prop :=
  ¬ Lambda.betaEtaConv (toLam (app tT (var 0))) (toLam (app (var 0) (app tT (var 0))))

end TLCA4
