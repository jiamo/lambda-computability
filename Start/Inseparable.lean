/-
**A recursively inseparable pair of r.e. sets.**

The two halves of the diagonal,

```
K₀ = { e | Φ_e(e) ↓ = 0 }      K₁ = { e | Φ_e(e) ↓ = 1 }
```

are disjoint (`Lambda.Inseparable.diag_disjoint`) and both recursively enumerable
(`Lambda.Inseparable.rePred_leftDiag`, `Lambda.Inseparable.rePred_rightDiag`), yet **no** decidable
set separates them (`Lambda.Inseparable.no_computable_separation`): a decision procedure for a
separating set could be turned into a total computable function whose own index escapes it on both
sides.

This is the recursion-theoretic core of Rosser's trick: any consistent, decidable theory strong
enough to represent computable functions would separate the two halves of the diagonal, and there
is no such separation.  In particular neither half is decidable
(`Lambda.Inseparable.not_computablePred_leftDiag`).
-/

import Mathlib.Computability.Halting
import Mathlib.Computability.PartrecCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Inseparable

open Encodable Denumerable
open Nat.Partrec (Code)

/-- The left half of the diagonal: the `e`-th machine converges to `0` on input `e`. -/
def leftDiag (e : ℕ) : Prop := 0 ∈ Code.eval (ofNat Code e) e

/-- The right half of the diagonal: the `e`-th machine converges to `1` on input `e`. -/
def rightDiag (e : ℕ) : Prop := 1 ∈ Code.eval (ofNat Code e) e

theorem diag_disjoint (e : ℕ) : ¬ (leftDiag e ∧ rightDiag e) := by
  rintro ⟨h0, h1⟩
  exact absurd (Part.mem_unique h0 h1) (by decide)

theorem partrec_diag : Partrec fun e : ℕ => Code.eval (ofNat Code e) e :=
  Code.eval_part.comp (Computable.ofNat Code) Computable.id

/-- The test "the diagonal computation converges to `k`", as a partial recursive function whose
domain is the corresponding half of the diagonal. -/
theorem rePred_diag (k : ℕ) : REPred fun e : ℕ => k ∈ Code.eval (ofNat Code e) e := by
  have hp : Partrec₂ fun (e : ℕ) (_ : ℕ) =>
      (Code.eval (ofNat Code e) e).map fun v => v == k :=
    (partrec_diag.comp Computable.fst).map
      (Primrec.to_comp (Primrec.beq.comp Primrec.snd (Primrec.const k))).to₂
  refine (Partrec.rfind hp).dom_re.of_eq fun e => ?_
  constructor
  · intro hdom
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.1 hdom
    have hn' := Nat.mem_rfind.mp hn
    obtain ⟨v, hv, hvk⟩ := (Part.mem_map_iff _).1 hn'.1
    simpa [eq_of_beq hvk] using hv
  · intro hk
    have : (0 : ℕ) ∈ Nat.rfind fun _ : ℕ =>
        (Code.eval (ofNat Code e) e).map fun v => v == k := by
      exact Nat.mem_rfind.mpr
        ⟨(Part.mem_map_iff _).2 ⟨k, hk, by simp⟩, fun hm => absurd hm (by omega)⟩
    exact Part.dom_iff_mem.2 ⟨0, this⟩

theorem rePred_leftDiag : REPred leftDiag := rePred_diag 0

theorem rePred_rightDiag : REPred rightDiag := rePred_diag 1

/-- **The two halves of the diagonal are recursively inseparable.**  No computable `Bool`-valued
test can answer `true` on all of the left half and `false` on all of the right half. -/
theorem no_computable_separation_bool {c : ℕ → Bool} (hc : Computable c)
    (h₁ : ∀ e, leftDiag e → c e = true) (h₂ : ∀ e, rightDiag e → c e = false) : False := by
  have hf : Nat.Partrec fun e : ℕ => (Part.some (if c e then 1 else 0) : Part ℕ) :=
    Partrec.nat_iff.1 (Computable.partrec
      ((Computable.cond hc (Computable.const 1) (Computable.const 0)).of_eq
        fun e => by cases c e <;> simp))
  obtain ⟨cf, hcf⟩ := Code.exists_code.1 hf
  set e := encode cf with he
  have hev : Code.eval (ofNat Code e) e = Part.some (if c e then 1 else 0) := by
    rw [he]
    simp only [Denumerable.ofNat_encode]
    rw [hcf]
  by_cases hce : c e = true
  · have : rightDiag e := by
      rw [rightDiag, hev, hce]
      simp
    exact absurd (h₂ e this) (by simp [hce])
  · have hce' : c e = false := by simpa using hce
    have : leftDiag e := by
      rw [leftDiag, hev, hce']
      simp
    exact absurd (h₁ e this) (by simp [hce'])

/-- The same statement for a decidable separating set. -/
theorem no_computable_separation {p : ℕ → Prop} (hp : ComputablePred p)
    (h₁ : ∀ e, leftDiag e → p e) (h₂ : ∀ e, rightDiag e → ¬ p e) : False := by
  obtain ⟨inst, hc⟩ := hp
  refine no_computable_separation_bool hc (fun e he => ?_) (fun e he => ?_)
  · simpa using h₁ e he
  · simpa using h₂ e he

theorem not_computablePred_leftDiag : ¬ ComputablePred leftDiag := fun h =>
  no_computable_separation h (fun _ he => he) fun e he hl => diag_disjoint e ⟨hl, he⟩

theorem not_computablePred_rightDiag : ¬ ComputablePred rightDiag := fun h =>
  no_computable_separation (p := fun e => ¬ rightDiag e) (ComputablePred.not h)
    (fun e he hr => diag_disjoint e ⟨he, hr⟩) fun _ he hn => hn he

end Inseparable
end Lambda
