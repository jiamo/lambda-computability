import Start.StarHeightCoreClasses

/-!
# Generalized star height one for `coreLang`, and for `A₄`

* `coreLang_height_one_all`: `coreLang k n` has height at most one for every `n` and `k < n`.
  On the words in state `0`, `3·coreCount u ≡ |u|₀ − acCount u + Σᵢ dᵢ·Nᵢ(u) (mod 3n)` determines
  `coreCount u` modulo `n`, and every term on the right, counted modulo `3n`, has height at most
  one (Pin–Straubing–Thérien, Proposition 6.2).  Words in states `1` and `2` reach state `0` by
  appending `2` or `1` (right quotients), which does not change `coreCount`.
* `coreLang_height_one`: the case `n = 2`.
* `height_one_alternatingGroup_four`: every language recognized by `A₄` has generalized star
  height at most one.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- The identity in the form used below. -/
lemma core_identity' {w : W3} (h : dsum step3 w = 0) :
    (w.count 0 : ℤ) - (acCount w : ℤ) + ∑ i : Fin 12, dval i.succ * (Ncnt i w : ℤ) =
      3 * (coreCount w : ℤ) := by
  have := core_identity h
  linarith

/-- The words in state `0` with `coreCount ≡ k (mod n)`. -/
def coreK (k n : ℕ) : Language (Fin 3) := {w | dsum step3 w = 0 ∧ coreCount w % n = k}

/-- The residue condition. -/
def resCond (k n : ℕ) (r : Fin (3 * n) × Fin (3 * n) × (Fin 12 → Fin (3 * n))) : Prop :=
  ((r.1 : ℤ) - (r.2.1 : ℤ) + ∑ i : Fin 12, dval i.succ * (r.2.2 i : ℤ) - 3 * k : ZMod (3 * n)) = 0

lemma coreK_eq (k n : ℕ) (hk : k < n) : coreK k n =
    ⨆ r : {r : Fin (3 * n) × Fin (3 * n) × (Fin 12 → Fin (3 * n)) // resCond k n r},
      (({w | w.count 0 % (3 * n) = r.1.1} : Language (Fin 3)) ⊓
        {w | acCount w % (3 * n) = r.1.2.1} ⊓
        ⨅ i : Fin 12, bmod coreX (Fcls i) (3 * n) (r.1.2.2 i)) := by
  have hM : 0 < 3 * n := by omega
  have key : ∀ w : W3, dsum step3 w = 0 →
      (((w.count 0 % (3 * n) : ℕ) : ℤ) - ((acCount w % (3 * n) : ℕ) : ℤ) +
        ∑ i : Fin 12, dval i.succ * ((Ncnt i w % (3 * n) : ℕ) : ℤ) - 3 * k : ZMod (3 * n)) =
        ((3 * ((coreCount w : ℤ) - k) : ℤ) : ZMod (3 * n)) := by
    intro w hw
    have := congrArg (fun z : ℤ => (z : ZMod (3 * n))) (core_identity' hw)
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_sum,
      Int.cast_ofNat] at this ⊢
    simp only [ZMod.natCast_mod]
    rw [this]
    ring
  have hdvd : ∀ c : ℕ, (((3 * ((c : ℤ) - k) : ℤ) : ZMod (3 * n)) = 0 ↔ c % n = k) := by
    intro c
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [mul_dvd_mul_iff_left (by norm_num : (3 : ℤ) ≠ 0), ← Nat.modEq_iff_dvd]
    constructor
    · intro h
      have := h.symm
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hk]
    · intro h
      unfold Nat.ModEq
      rw [h, Nat.mod_eq_of_lt hk]
  ext w
  constructor
  · rintro ⟨hw, hc⟩
    refine Language.mem_iSup.mpr ⟨⟨(⟨w.count 0 % (3 * n), Nat.mod_lt _ hM⟩,
      ⟨acCount w % (3 * n), Nat.mod_lt _ hM⟩, fun i => ⟨Ncnt i w % (3 * n), Nat.mod_lt _ hM⟩),
      ?_⟩, ?_⟩
    · show (_ : ZMod (3 * n)) = 0
      rw [key w hw]
      exact (hdvd _).mpr hc
    · refine ⟨⟨rfl, rfl⟩, HasHeightAtMost.mem_iInf_lang.mpr fun i => ?_⟩
      exact (mem_bmod_coreX _ _ _ w).mpr ⟨hw, rfl⟩
  · intro h
    obtain ⟨r, ⟨h0, h1⟩, h2⟩ := Language.mem_iSup.mp h
    have h2' := fun i => (mem_bmod_coreX _ _ _ w).mp (HasHeightAtMost.mem_iInf_lang.mp h2 i)
    have hw : dsum step3 w = 0 := (h2' 0).1
    refine ⟨hw, (hdvd _).mp ?_⟩
    rw [← key w hw]
    have hr := r.2
    unfold resCond at hr
    have e0 : w.count 0 % (3 * n) = r.1.1 := h0
    have e1 : acCount w % (3 * n) = r.1.2.1 := h1
    have e2 : ∀ i, Ncnt i w % (3 * n) = r.1.2.2 i := fun i => (h2' i).2
    simp only [e0, e1, e2]
    exact hr

theorem coreK_height (k n : ℕ) (hk : k < n) : HasHeightAtMost (coreK k n) 1 := by
  have hM : 0 < 3 * n := by omega
  rw [coreK_eq k n hk]
  refine HasHeightAtMost.iSup _ fun r => ?_
  refine HasHeightAtMost.inter (HasHeightAtMost.inter ?_ ?_) ?_
  · exact countMod_height 0 hM _ r.1.1.2
  · exact acCount_height r.1.2.1.2
  · exact HasHeightAtMost.iInf _ fun i => bmodF_height i (r.1.2.2 i).2

lemma coreLang_eq_quot (k n : ℕ) :
    coreLang k n = coreK k n + rightQuot 2 (coreK k n) + rightQuot 1 (coreK k n) := by
  ext w
  rw [Language.mem_add, Language.mem_add]
  show coreCount w % n = k ↔ ((dsum step3 w = 0 ∧ coreCount w % n = k) ∨
    (dsum step3 (w ++ [2]) = 0 ∧ coreCount (w ++ [2]) % n = k)) ∨
    (dsum step3 (w ++ [1]) = 0 ∧ coreCount (w ++ [1]) % n = k)
  rw [coreCount_snoc, coreCount_snoc, dsum_append, dsum_append]
  have e2 : dsum step3 [2] = 2 := rfl
  have e1 : dsum step3 [1] = 1 := rfl
  rw [e1, e2]
  simp only [show (2 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 0 by decide, false_and,
    ite_false, add_zero]
  constructor
  · intro hc
    rcases zmod3_cases (dsum step3 w) with h | h | h
    · exact Or.inl (Or.inl ⟨h, hc⟩)
    · exact Or.inl (Or.inr ⟨by rw [h]; decide, hc⟩)
    · exact Or.inr ⟨by rw [h]; decide, hc⟩
  · rintro ((⟨-, hc⟩ | ⟨-, hc⟩) | ⟨-, hc⟩) <;> exact hc

/-- **Bourne's Conjecture 4.12 for `r = 1`**: `coreLang k n` has generalized star height at most
one, for every modulus `n`. -/
theorem coreLang_height_one_all (n k : ℕ) (hk : k < n) : HasHeightAtMost (coreLang k n) 1 := by
  rw [coreLang_eq_quot]
  have h := coreK_height k n hk
  exact (h.union (h.rightQuot 2)).union (h.rightQuot 1)

/-- **The core language has height one.** -/
theorem coreLang_height_one (k : ℕ) (hk : k < 2) : HasHeightAtMost (coreLang k 2) 1 :=
  coreLang_height_one_all 2 k hk

/-- **Generalized star height one for `A₄`.** -/
theorem height_one_alternatingGroup_four {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4)) (F : Set (alternatingGroup (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_alternatingGroup_four_of_core coreLang_height_one T F

end GeneralizedStarHeight
