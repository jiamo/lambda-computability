/-
**Bridges: recursion theory, Blum complexity and universal search over the λ-calculus** —
milestone M31 (`M31-BRIDGE-INSEPARABLE`, `M31-BRIDGE-BLUM`).

Three developments of the library were stated over Mathlib's partial recursive codes only:
recursive inseparability (`Start/Inseparable.lean`), the Blum step measure and the gap theorem
(`Start/StepComplexity.lean`, `Start/GapTheorem.lean`), and Levin's universal search
(`Start/LevinSearch.lean`, over an arbitrary step-indexed evaluator).  Through the Church–Turing
theorem of the λ core (`lambdaComputable_iff_partrec`, `lambdaComputable_iff_computable`) they
are restated over λ-definability.

* `LambdaDecidable p` — the characteristic function of `p` is λ-definable;
  **`lambdaDecidable_iff_computablePred`**: exactly the computable predicates;
* `Lambda.Inseparable.no_lambda_separation` — **no λ-decidable set separates the two halves of
  the diagonal**;
* `Complexity.exists_lambda_not_withinFuel` — for every λ-definable bound there is a total
  λ-definable function no code computes within the bound;
* `Complexity.exists_gap_lambda` — **the gap theorem for λ-definable bounds**;
* `Complexity.levin_optimal_codes` — **Levin search over the partial recursive codes**, with
  the fuel of `Code.evaln` as the step count: if code number `p` outputs an accepted answer
  within `t` units of fuel, universal search finds an accepted answer within `8 · 2^p · t`
  simulated units.
-/

import Start.PartialCapstone
import Start.Inseparable
import Start.GapTheorem
import Start.LevinSearch

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Encodable Denumerable
open Nat.Partrec (Code)

/-! ### λ-decidable predicates -/

/-- `p` is **λ-decidable**: its characteristic function is λ-definable. -/
def LambdaDecidable (p : ℕ → Prop) : Prop :=
  ∃ c : ℕ → Bool, (∀ n, p n ↔ c n = true) ∧ LambdaComputable (fun n => Part.some (cond (c n) 1 0))

/-- **The λ-decidable predicates are exactly the computable ones.** -/
theorem lambdaDecidable_iff_computablePred {p : ℕ → Prop} : LambdaDecidable p ↔ ComputablePred p := by
  constructor
  · rintro ⟨c, hc, hlam⟩
    have hg : Computable fun n => cond (c n) 1 0 := lambdaComputable_iff_computable.mp hlam
    have hc' : Computable c := by
      have h₁ : Computable fun n => (cond (c n) 1 0 == 1) :=
        (Primrec.beq.to_comp).comp hg (Computable.const 1)
      refine h₁.of_eq fun n => ?_
      cases c n <;> rfl
    refine ComputablePred.computable_iff.mpr ⟨c, hc', ?_⟩
    funext n
    exact propext (hc n)
  · intro hp
    obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp hp
    exact ⟨f, fun n => Iff.rfl,
      lambdaComputable_iff_computable.mpr (Computable.cond hf (Computable.const 1) (Computable.const 0))⟩

/-! ### Recursive inseparability -/

/-- **No λ-decidable set separates the two halves of the diagonal.** -/
theorem Lambda.Inseparable.no_lambda_separation {p : ℕ → Prop} (hp : LambdaDecidable p)
    (h₁ : ∀ e, leftDiag e → p e) (h₂ : ∀ e, rightDiag e → ¬ p e) : False :=
  no_computable_separation (lambdaDecidable_iff_computablePred.mp hp) h₁ h₂

theorem Lambda.Inseparable.not_lambdaDecidable_leftDiag : ¬ LambdaDecidable leftDiag :=
  fun h => not_computablePred_leftDiag (lambdaDecidable_iff_computablePred.mp h)

/-! ### Blum complexity over λ-definable bounds -/

namespace Complexity

/-- For every λ-definable bound there is a total λ-definable function that no code computes
within the bound. -/
theorem exists_lambda_not_withinFuel {t : ℕ → ℕ} (ht : LambdaComputable fun n => Part.some (t n)) :
    ∃ f : ℕ → ℕ, LambdaComputable (fun n => Part.some (f n)) ∧ ∀ c : Code, ¬ WithinFuel c t f := by
  obtain ⟨f, hf, hnot⟩ := exists_computable_not_withinFuel (lambdaComputable_iff_computable.mp ht)
  exact ⟨f, lambdaComputable_iff_computable.mpr hf, hnot⟩

/-- **The gap theorem for λ-definable bounds**: for every λ-definable `g` with `g n ≥ n` there is
a λ-definable bound `t` such that converging within `g ∘ t` and within `t` agree for every code on
every input above it. -/
theorem exists_gap_lambda {g : ℕ → ℕ} (hg : LambdaComputable fun n => Part.some (g n))
    (hle : ∀ n, n ≤ g n) :
    ∃ t : ℕ → ℕ, LambdaComputable (fun n => Part.some (t n)) ∧
      ∀ (c : Code) (x : ℕ), encode c < x → (StepsLe c x (g (t x)) ↔ StepsLe c x (t x)) := by
  obtain ⟨t, ht, hgap⟩ := exists_gap (lambdaComputable_iff_computable.mp hg) hle
  exact ⟨t, lambdaComputable_iff_computable.mpr ht, hgap⟩

/-! ### Levin search over the codes -/

/-- The step-indexed evaluation of code number `p` on the input `x`, with `t` units of fuel. -/
def codeRun (x : ℕ) (p t : ℕ) : Option ℕ := Code.evaln t (ofNat Code p) x

theorem codeRun_mono (x : ℕ) :
    ∀ (p t t' : ℕ) (a : ℕ), t ≤ t' → codeRun x p t = some a → codeRun x p t' = some a := by
  intro p t t' a htt' h
  exact Code.evaln_mono htt' h

/-- **Levin's optimality for the partial recursive codes**: if code `c` outputs, within `t` units
of fuel, an answer accepted by `V`, then universal search over all codes finds an accepted answer
after simulating at most `8 · 2^(encode c) · t` units. -/
theorem levin_optimal_codes {V : ℕ → Bool} {x t a : ℕ} (c : Code) (ht : t ≠ 0)
    (hrun : Code.evaln t c x = some a) (hV : V a = true) :
    ∃ a' : ℕ, levinSearch (codeRun x) V (encode c + Nat.log 2 t + 1) = some a' ∧ V a' = true ∧
      searchCost (encode c + Nat.log 2 t + 1) ≤ 8 * 2 ^ encode c * t := by
  have hrun' : codeRun x (encode c) t = some a := by
    rw [codeRun, ofNat_encode]
    exact hrun
  exact levin_optimal (codeRun_mono x) ht hrun' hV

end Complexity
