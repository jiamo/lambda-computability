/-
**The Kleene–Post theorem: incomparable Turing degrees.**

There are two oracles `A` and `B` with neither computable from the other.  The construction is the
classical *finite extension* argument: one builds two finite strings step by step, meeting at
stage `2e` the requirement "`A` is not `Φ_e^B`" and at stage `2e+1` the requirement
"`B` is not `Φ_e^A`".

A single step is `Lambda.Oracle.diag σ τ e`.  Writing `x := σ.length` for the fresh point, it asks
whether some extension of `τ` forces a value for `Φ_e(x)`:

* if it does, extend `τ` to such a string and extend `σ` at `x` by the *opposite* answer, so the
  computation converges to a value different from the characteristic function of `A`;
* if no extension forces a value, then by `Lambda.Oracle.not_mem_of_no_forcing_extension` the
  computation diverges for *every* oracle extending `τ`, while the characteristic function is
  total; extending both strings by one bit keeps the construction going.

Iterating gives `Lambda.Oracle.kpA` and `Lambda.Oracle.kpB`, and the requirements become
`Lambda.Oracle.kleene_post`:

```
¬ (oracleFun kpA ≤ᵀ oracleFun kpB) ∧ ¬ (oracleFun kpB ≤ᵀ oracleFun kpA)
```

so their Turing degrees are incomparable (`Lambda.Oracle.turingDegree_incomparable`); in
particular the Turing degrees are not linearly ordered.
-/

import Start.OracleForcing

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Nat.Partrec (Code)
open scoped Computability

/-- One step of the finite extension construction: diagonalise the characteristic function of the
`σ`-side against the `e`-th machine with the `τ`-side as oracle, at the fresh point `σ.length`. -/
noncomputable def diag (sigma tau : List Bool) (e : ℕ) : List Bool × List Bool := by
  classical
  exact
    if h : ∃ p : List Bool × ℕ, tau <+: p.1 ∧ Forces p.1 e sigma.length p.2 then
      (sigma ++ [decide (h.choose.2 ≠ 1)], h.choose.1 ++ [false])
    else (sigma ++ [false], tau ++ [false])

theorem diag_fst_prefix (sigma tau : List Bool) (e : ℕ) : sigma <+: (diag sigma tau e).1 := by
  classical
  rw [diag]
  split <;> exact ⟨_, rfl⟩

theorem diag_snd_prefix (sigma tau : List Bool) (e : ℕ) : tau <+: (diag sigma tau e).2 := by
  classical
  rw [diag]
  split
  · rename_i h
    exact List.IsPrefix.trans h.choose_spec.1 ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem diag_fst_length (sigma tau : List Bool) (e : ℕ) :
    sigma.length < (diag sigma tau e).1.length := by
  classical
  rw [diag]
  split <;> simp

theorem diag_snd_length (sigma tau : List Bool) (e : ℕ) :
    tau.length < (diag sigma tau e).2.length := by
  classical
  rw [diag]
  split
  · rename_i h
    have := h.choose_spec.1.length_le
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · simp

/-- **The step meets its requirement**: for any oracles extending the two strings produced by the
step, the `e`-th machine with the second oracle does not compute the characteristic function of
the first at the diagonal point. -/
theorem diag_spec (sigma tau : List Bool) (e : ℕ) (A B : ℕ → Bool)
    (hA : strAgree (diag sigma tau e).1 A) (hB : strAgree (diag sigma tau e).2 B) :
    Phi B e sigma.length ≠ oracleFun A sigma.length := by
  classical
  intro hEq
  rw [diag] at hA hB
  split at hA
  · rename_i h
    rw [dif_pos h] at hB
    -- the forced value converges, but the characteristic function was chosen to differ from it
    have hpre : h.choose.1 <+: h.choose.1 ++ [false] := ⟨_, rfl⟩
    have hforce : h.choose.2 ∈ Phi B e sigma.length :=
      (h.choose_spec.2.mono hpre) B hB
    have hval : h.choose.2 ∈ oracleFun A sigma.length := hEq ▸ hforce
    have hAx : A sigma.length = decide (h.choose.2 ≠ 1) := by
      have hlt : sigma.length < (sigma ++ [decide (h.choose.2 ≠ 1)]).length := by simp
      have := hA sigma.length hlt
      rw [this, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
      simp
    simp only [oracleFun, Part.mem_some_iff] at hval
    by_cases hone : h.choose.2 = 1
    · rw [hAx] at hval; simp [hone] at hval
    · rw [hAx] at hval; simp [hone] at hval
  · rename_i h
    rw [dif_neg h] at hB
    -- no extension forces a value, so the computation diverges while the oracle answer does not
    have hdiv := not_mem_of_no_forcing_extension h (strAgree_of_prefix ⟨_, rfl⟩ hB)
    exact hdiv _ (hEq ▸ (by simp [oracleFun] : (if A sigma.length then 1 else 0) ∈
      oracleFun A sigma.length))

/-- The stages of the Kleene–Post construction: a pair of finite strings, extended at every
stage, diagonalising alternately on the two sides. -/
noncomputable def kpPair : ℕ → List Bool × List Bool
  | 0 => ([], [])
  | n + 1 =>
      if n % 2 = 0 then diag (kpPair n).1 (kpPair n).2 (n / 2)
      else Prod.swap (diag (kpPair n).2 (kpPair n).1 (n / 2))

theorem kpPair_succ_fst_prefix (n : ℕ) : (kpPair n).1 <+: (kpPair (n + 1)).1 := by
  rw [kpPair]
  split
  · exact diag_fst_prefix _ _ _
  · exact diag_snd_prefix _ _ _

theorem kpPair_succ_snd_prefix (n : ℕ) : (kpPair n).2 <+: (kpPair (n + 1)).2 := by
  rw [kpPair]
  split
  · exact diag_snd_prefix _ _ _
  · exact diag_fst_prefix _ _ _

theorem kpPair_fst_prefix {n m : ℕ} (h : n ≤ m) : (kpPair n).1 <+: (kpPair m).1 := by
  induction m with
  | zero => simp_all
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | h'
      · exact (ih (Nat.lt_succ_iff.1 h')).trans (kpPair_succ_fst_prefix m)
      · subst h'; exact List.prefix_rfl

theorem kpPair_snd_prefix {n m : ℕ} (h : n ≤ m) : (kpPair n).2 <+: (kpPair m).2 := by
  induction m with
  | zero => simp_all
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | h'
      · exact (ih (Nat.lt_succ_iff.1 h')).trans (kpPair_succ_snd_prefix m)
      · subst h'; exact List.prefix_rfl

theorem kpPair_fst_length (n : ℕ) : n ≤ (kpPair n).1.length := by
  induction n with
  | zero => simp [kpPair]
  | succ n ih =>
      have hlt : (kpPair n).1.length < (kpPair (n + 1)).1.length := by
        rw [kpPair]
        split
        · exact diag_fst_length _ _ _
        · exact diag_snd_length _ _ _
      omega

theorem kpPair_snd_length (n : ℕ) : n ≤ (kpPair n).2.length := by
  induction n with
  | zero => simp [kpPair]
  | succ n ih =>
      have hlt : (kpPair n).2.length < (kpPair (n + 1)).2.length := by
        rw [kpPair]
        split
        · exact diag_snd_length _ _ _
        · exact diag_fst_length _ _ _
      omega

/-- The first oracle built by the Kleene–Post construction. -/
noncomputable def kpA (n : ℕ) : Bool := (kpPair (n + 1)).1.getD n false

/-- The second oracle built by the Kleene–Post construction. -/
noncomputable def kpB (n : ℕ) : Bool := (kpPair (n + 1)).2.getD n false

theorem kpA_agree (n : ℕ) : strAgree (kpPair n).1 kpA := by
  intro i hi
  have h1 : (kpPair (i + 1)).1 <+: (kpPair (max n (i + 1))).1 :=
    kpPair_fst_prefix (le_max_right _ _)
  have h2 : (kpPair n).1 <+: (kpPair (max n (i + 1))).1 := kpPair_fst_prefix (le_max_left _ _)
  have hi1 : i < (kpPair (i + 1)).1.length := lt_of_lt_of_le (Nat.lt_succ_self i)
    (kpPair_fst_length (i + 1))
  rw [kpA, getD_eq_of_prefix h1 hi1, ← getD_eq_of_prefix h2 hi]

theorem kpB_agree (n : ℕ) : strAgree (kpPair n).2 kpB := by
  intro i hi
  have h1 : (kpPair (i + 1)).2 <+: (kpPair (max n (i + 1))).2 :=
    kpPair_snd_prefix (le_max_right _ _)
  have h2 : (kpPair n).2 <+: (kpPair (max n (i + 1))).2 := kpPair_snd_prefix (le_max_left _ _)
  have hi1 : i < (kpPair (i + 1)).2.length := lt_of_lt_of_le (Nat.lt_succ_self i)
    (kpPair_snd_length (i + 1))
  rw [kpB, getD_eq_of_prefix h1 hi1, ← getD_eq_of_prefix h2 hi]

/-- The requirement met at the even stages: `kpA` is not computed by the `e`-th machine with
oracle `kpB`. -/
theorem kpA_ne_phi (e : ℕ) : Phi kpB e ≠ oracleFun kpA := by
  intro hEq
  have hstage : kpPair (2 * e + 1) = diag (kpPair (2 * e)).1 (kpPair (2 * e)).2 e := by
    rw [kpPair]
    rw [if_pos (by omega), show 2 * e / 2 = e by omega]
  have hA : strAgree (diag (kpPair (2 * e)).1 (kpPair (2 * e)).2 e).1 kpA := by
    rw [← hstage]; exact kpA_agree _
  have hB : strAgree (diag (kpPair (2 * e)).1 (kpPair (2 * e)).2 e).2 kpB := by
    rw [← hstage]; exact kpB_agree _
  exact diag_spec _ _ e kpA kpB hA hB (by rw [hEq])

/-- The requirement met at the odd stages: `kpB` is not computed by the `e`-th machine with
oracle `kpA`. -/
theorem kpB_ne_phi (e : ℕ) : Phi kpA e ≠ oracleFun kpB := by
  intro hEq
  have hstage : kpPair (2 * e + 2) =
      Prod.swap (diag (kpPair (2 * e + 1)).2 (kpPair (2 * e + 1)).1 e) := by
    rw [show 2 * e + 2 = (2 * e + 1) + 1 from rfl, kpPair]
    rw [if_neg (by omega), show (2 * e + 1) / 2 = e by omega]
  have hA : strAgree
      (diag (kpPair (2 * e + 1)).2 (kpPair (2 * e + 1)).1 e).1 kpB := by
    have := kpB_agree (2 * e + 2)
    rwa [hstage] at this
  have hB : strAgree
      (diag (kpPair (2 * e + 1)).2 (kpPair (2 * e + 1)).1 e).2 kpA := by
    have := kpA_agree (2 * e + 2)
    rwa [hstage] at this
  exact diag_spec _ _ e kpB kpA hA hB (by rw [hEq])

/-- **The Kleene–Post theorem.**  There are two oracles neither of which is computable from the
other. -/
theorem kleene_post :
    ¬ (oracleFun kpA ≤ᵀ oracleFun kpB) ∧ ¬ (oracleFun kpB ≤ᵀ oracleFun kpA) := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := recursiveIn_iff_exists_index.1 h
    exact kpA_ne_phi e he
  · intro h
    obtain ⟨e, he⟩ := recursiveIn_iff_exists_index.1 h
    exact kpB_ne_phi e he

/-- The Turing degrees are not linearly ordered: the degrees of `kpA` and `kpB` are incomparable.
-/
theorem turingDegree_incomparable :
    ¬ (toAntisymmetrization TuringReducible (oracleFun kpA) ≤
        toAntisymmetrization TuringReducible (oracleFun kpB)) ∧
    ¬ (toAntisymmetrization TuringReducible (oracleFun kpB) ≤
        toAntisymmetrization TuringReducible (oracleFun kpA)) := by
  refine ⟨fun h => kleene_post.1 ?_, fun h => kleene_post.2 ?_⟩ <;>
    exact toAntisymmetrization_le_toAntisymmetrization_iff.1 h

end Oracle
end Lambda
