/-
**Every language in polynomial space has quantified Boolean formulas of polynomial size.**

`Start/QbfMachine.lean` turns a machine running in space `s` on an input `x` into a closed
quantified Boolean formula `machineF M x s` that is true exactly when the machine accepts `x`.
This module reads that off for a whole class: for a language in `Complexity.Space.PSPACE` the
formulas of its inputs have size bounded by *one polynomial in the length of the input*.

That is the part of the PSPACE-hardness of `TQBF` which does not mention computation.  What the
hardness theorem needs on top of it is that the map from an input to its formula is itself
computable in polynomial time; that is not formalised here, and is recorded as the open task
`M14-TQBF-PSPACE-HARD`.

Main definitions:

* `Complexity.Qbf.QBF.wBound`, `.kBound`, `.sizeBound` — the width of a configuration word, the
  depth of the recursion and the size of the whole formula, as functions of the input length.

Main results:

* `Complexity.PolyBound.mul` — polynomial bounds are closed under products;
* `Complexity.Qbf.QBF.size_machineF_le_sizeBound` — the formula of an input of length `n` has size
  at most `sizeBound M s n`;
* `Complexity.Qbf.QBF.polyBound_sizeBound` — that bound is polynomial when the space bound is;
* `Complexity.Qbf.QBF.npspace_polySize_qbf` — **every language in `NPSPACE` has a family of
  quantified Boolean formulas of polynomial size, one per input, true exactly on the members of
  the language**;
* `Complexity.Qbf.QBF.npspace_polySize_tqbf`, `.pspace_polySize_tqbf` — the same family read as
  instances of `Complexity.Qbf.TQBF`, the formulas being closed, for `NPSPACE` and for its
  sub-class `PSPACE`.
-/

import Mathlib
import Start.QbfClosed

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- Polynomial bounds are closed under products. -/
theorem PolyBound.mul {p q : ℕ → ℕ} (hp : PolyBound p) (hq : PolyBound q) :
    PolyBound (fun n => p n * q n) := by
  obtain ⟨a, k, ha⟩ := hp
  obtain ⟨b, l, hb⟩ := hq
  refine ⟨a * b, k + l, fun n => ?_⟩
  calc p n * q n ≤ (a * (n + 1) ^ k) * (b * (n + 1) ^ l) :=
        Nat.mul_le_mul (ha n) (hb n)
    _ = a * b * (n + 1) ^ (k + l) := by rw [pow_add]; ring

/-- The identity is polynomially bounded. -/
theorem polyBound_id : PolyBound (fun n => n) := ⟨1, 1, fun n => by simp⟩

namespace Qbf

namespace QBF

open Complexity.Space

/-! ### The bound, as a function of the input length -/

/-- The width of a configuration word of a machine running in space `s` on an input of length
`n`. -/
def wBound (M : Machine) (s : ℕ → ℕ) (n : ℕ) : ℕ := M.states + (n + 1) + s n + s n

/-- A bound on the depth of the midpoint recursion. -/
def kBound (M : Machine) (s : ℕ → ℕ) (n : ℕ) : ℕ :=
  M.states + (n + 1) + 2 * (s n + 1) + s n

/-- The size of the formula of an input of length `n`, for a machine running in space `s`. -/
def sizeBound (M : Machine) (s : ℕ → ℕ) (n : ℕ) : ℕ :=
  (M.states * (n + 1) * s n * 2 * (M.states * 18) * (wBound M s n * 15 + 13) + 4)
    + 10 * wBound M s n + 5
    + kBound M s n * (43 * wBound M s n + 21)
    + (wBound M s n * 5 + 4) + (s n * 3 + 4) + 1
    + (M.states * (n + 1) * s n * (wBound M s n * 5 + 5) + 4)
    + 2 * wBound M s n + 2

theorem clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow (le_of_lt Nat.lt_two_pow_self)

theorem cfgWidth_eq_wBound (M : Machine) (s : ℕ → ℕ) (x : List Bool) :
    cfgWidth M x (s x.length) = wBound M s x.length := rfl

theorem savitchDepth_le_kBound (M : Machine) (s : ℕ → ℕ) (x : List Bool) :
    savitchDepth M x (s x.length) ≤ kBound M s x.length := by
  refine le_trans (savitchDepth_le M x (s x.length)) ?_
  have h1 := clog_two_le_self M.states
  have h2 := clog_two_le_self (x.length + 1)
  have h3 := clog_two_le_self (s x.length + 1)
  simp only [kBound]
  omega

/-- The formula of an input of length `n` has size at most `sizeBound M s n`. -/
theorem size_machineF_le_sizeBound (M : Machine) (s : ℕ → ℕ)
    (x : List Bool) : (machineF M x (s x.length)).size ≤ sizeBound M s x.length := by
  have h := size_machineF_le (M := M) (x := x) (s := s x.length)
  have hk : savitchDepth M x (s x.length) * (43 * wBound M s x.length + 21)
      ≤ kBound M s x.length * (43 * wBound M s x.length + 21) :=
    Nat.mul_le_mul_right _ (savitchDepth_le_kBound M s x)
  rw [cfgWidth_eq_wBound] at h
  refine le_trans h ?_
  simp only [sizeBound]
  omega

/-- The bound is polynomial when the space bound is. -/
theorem polyBound_sizeBound (M : Machine) {s : ℕ → ℕ} (hs : PolyBound s) :
    PolyBound (sizeBound M s) := by
  have hconst : ∀ c : ℕ, PolyBound (fun _ => c) := polyBound_const
  have hsucc : PolyBound (fun n => n + 1) := (polyBound_id).add (hconst 1)
  have hw : PolyBound (wBound M s) := by
    have : PolyBound (fun n => M.states + (n + 1) + s n + s n) :=
      (((hconst M.states).add hsucc).add hs).add hs
    exact this
  have hk : PolyBound (kBound M s) := by
    have : PolyBound (fun n => M.states + (n + 1) + 2 * (s n + 1) + s n) :=
      (((hconst M.states).add hsucc).add ((hconst 2).mul (hs.add (hconst 1)))).add hs
    exact this
  have hmain : PolyBound (fun n => M.states * (n + 1) * s n) :=
    ((hconst M.states).mul hsucc).mul hs
  have h1 : PolyBound (fun n =>
      M.states * (n + 1) * s n * 2 * (M.states * 18) * (wBound M s n * 15 + 13) + 4) :=
    (((hmain.mul (hconst 2)).mul (hconst (M.states * 18))).mul
      ((hw.mul (hconst 15)).add (hconst 13))).add (hconst 4)
  have h2 : PolyBound (fun n => 10 * wBound M s n + 5) :=
    ((hconst 10).mul hw).add (hconst 5)
  have h3 : PolyBound (fun n => kBound M s n * (43 * wBound M s n + 21)) :=
    hk.mul (((hconst 43).mul hw).add (hconst 21))
  have h4 : PolyBound (fun n => wBound M s n * 5 + 4) :=
    (hw.mul (hconst 5)).add (hconst 4)
  have h5 : PolyBound (fun n => s n * 3 + 4) := (hs.mul (hconst 3)).add (hconst 4)
  have h6 : PolyBound (fun n =>
      M.states * (n + 1) * s n * (wBound M s n * 5 + 5) + 4) :=
    (hmain.mul ((hw.mul (hconst 5)).add (hconst 5))).add (hconst 4)
  have h7 : PolyBound (fun n => 2 * wBound M s n + 2) :=
    ((hconst 2).mul hw).add (hconst 2)
  have : PolyBound (fun n =>
      (M.states * (n + 1) * s n * 2 * (M.states * 18) * (wBound M s n * 15 + 13) + 4)
        + (10 * wBound M s n + 5)
        + (kBound M s n * (43 * wBound M s n + 21))
        + (wBound M s n * 5 + 4) + (s n * 3 + 4) + 1
        + (M.states * (n + 1) * s n * (wBound M s n * 5 + 5) + 4)
        + (2 * wBound M s n + 2)) :=
    (((((((h1.add h2).add h3).add h4).add h5).add (polyBound_const 1)).add h6).add h7)
  refine this.mono fun n => ?_
  simp only [sizeBound]
  omega

/-! ### The class statement -/

/-- **Every language in polynomial space has quantified Boolean formulas of polynomial size**:
one formula per input, of size bounded by a single polynomial in the length of the input, whose
value is `true` exactly on the members of the language. -/
theorem npspace_polySize_qbf {L : Complexity.Space.Language} (h : Complexity.Space.NPSPACE L) :
    ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ x : List Bool, ∃ F : QBF,
      F.size ≤ p x.length ∧ ∀ σ : ℕ → Bool, (F.eval σ = true ↔ L x) := by
  obtain ⟨s, hs, M, hwf, hsp, hL⟩ := h
  refine ⟨sizeBound M (fun n => s n + 1), polyBound_sizeBound M (hs.add (polyBound_const 1)), ?_⟩
  intro x
  refine ⟨machineF M x (s x.length + 1), ?_, ?_⟩
  · exact size_machineF_le_sizeBound M (fun n => s n + 1) x
  · intro σ
    have hspx : M.SpaceBoundedOn x (s x.length + 1) := fun n c hc =>
      le_trans (hsp x n c hc) (Nat.le_succ _)
    rw [eval_machineF hwf hspx (Nat.succ_pos _) σ]
    exact (hL x).symm

/-- **Every language in polynomial space reduces to `TQBF` by a map of polynomial size**: one
closed formula per input, of size bounded by a single polynomial in the length of the input, true
exactly on the members of the language.  What this does *not* say — and what the
`PSPACE`-hardness of `TQBF` needs on top of it — is that the map is computable in polynomial
time. -/
theorem npspace_polySize_tqbf {L : Complexity.Space.Language} (h : Complexity.Space.NPSPACE L) :
    ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ x : List Bool, ∃ F : QBF,
      F.size ≤ p x.length ∧ (Complexity.Qbf.TQBF F ↔ L x) := by
  obtain ⟨s, hs, M, hwf, hsp, hL⟩ := h
  refine ⟨sizeBound M (fun n => s n + 1), polyBound_sizeBound M (hs.add (polyBound_const 1)), ?_⟩
  intro x
  refine ⟨machineF M x (s x.length + 1),
    size_machineF_le_sizeBound M (fun n => s n + 1) x, ?_⟩
  have hspx : M.SpaceBoundedOn x (s x.length + 1) := fun n c hc =>
    le_trans (hsp x n c hc) (Nat.le_succ _)
  rw [tqbf_machineF_iff hwf hspx (Nat.succ_pos _)]
  exact (hL x).symm

/-- The same for a language in `PSPACE`, which is a special case of `NPSPACE`. -/
theorem pspace_polySize_qbf {L : Complexity.Space.Language} (h : Complexity.Space.PSPACE L) :
    ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ x : List Bool, ∃ F : QBF,
      F.size ≤ p x.length ∧ ∀ σ : ℕ → Bool, (F.eval σ = true ↔ L x) :=
  npspace_polySize_qbf (Complexity.Space.npspace_of_pspace h)

/-- The same for a language in `PSPACE`, which is a special case of `NPSPACE`. -/
theorem pspace_polySize_tqbf {L : Complexity.Space.Language} (h : Complexity.Space.PSPACE L) :
    ∃ p : ℕ → ℕ, PolyBound p ∧ ∀ x : List Bool, ∃ F : QBF,
      F.size ≤ p x.length ∧ (Complexity.Qbf.TQBF F ↔ L x) :=
  npspace_polySize_tqbf (Complexity.Space.npspace_of_pspace h)

end QBF

end Qbf

end Complexity
