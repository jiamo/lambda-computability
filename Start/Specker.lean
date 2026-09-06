/-
**A Specker sequence.**

A *Specker sequence* is a computable, nondecreasing, bounded sequence of rationals whose limit is
not computable: the classical monotone convergence theorem fails effectively.  The sequence built
here is the standard one, driven by the halting set `K` of `Start/KleeneK.lean`: at stage `n` add
`2^{-(k+1)}` for every `k < n` that has entered `K` by stage `n`.

* `Lambda.entered` — "`k` has entered `K` by stage `s`", primitive recursive and monotone in `s`,
  with `Lambda.haltK_iff_entered` relating it to `Lambda.HaltK`;
* `Lambda.speckerVal` — the sequence, with `Lambda.speckerVal_monotone` and
  `Lambda.speckerVal_lt_one`; it is computable in the sense that its dyadic numerators are
  (`Lambda.computable_speckerNum`, `Lambda.speckerVal_eq`);
* `Lambda.speckerVal_jump` — when a new element enters, the sequence jumps by at least
  `2^{-(k+1)}`;
* `Lambda.specker_no_computable_modulus` — **the sequence has no computable modulus of
  convergence**: from one, the halting set would be decidable.  So the limit of a computable
  monotone bounded sequence of rationals need not be a computable real.
-/

import Start.KleeneK
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

open Nat.Partrec (Code)
open Nat.Partrec.Code
open Encodable Denumerable

/-! ### Entering the halting set -/

/-- `k` has entered the halting set by stage `s`: the `k`-th code, run on `k`, halts within `s`
steps. -/
def entered (k s : ℕ) : Bool := (Code.evaln s (ofNat Code k) k).isSome

theorem primrec_entered : Primrec₂ entered := by
  have h : Primrec fun p : ℕ × ℕ => Code.evaln p.2 (ofNat Code p.1) p.1 :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd ((Primrec.ofNat Code).comp Primrec.fst))
        Primrec.fst)
  exact (Primrec.option_isSome.comp h).to₂

theorem entered_mono {k s s' : ℕ} (h : s ≤ s') (hk : entered k s = Bool.true) :
    entered k s' = Bool.true := by
  simp only [entered, Option.isSome_iff_exists] at hk ⊢
  obtain ⟨x, hx⟩ := hk
  exact ⟨x, evaln_mono h hx⟩

theorem haltK_iff_entered (k : ℕ) : HaltK k ↔ ∃ s, entered k s = Bool.true := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
    obtain ⟨s, hs⟩ := evaln_complete.1 hx
    refine ⟨s, ?_⟩
    simp only [entered, Option.isSome_iff_exists]
    exact ⟨x, hs⟩
  · rintro ⟨s, hs⟩
    simp only [entered, Option.isSome_iff_exists] at hs
    obtain ⟨x, hx⟩ := hs
    exact Part.dom_iff_mem.2 ⟨x, evaln_complete.2 ⟨s, hx⟩⟩

/-! ### The sequence -/

/-- The term contributed at stage `n` by the index `k`. -/
def speckerTerm (n k : ℕ) : ℚ :=
  if k < n ∧ entered k n = Bool.true then (1 : ℚ) / 2 ^ (k + 1) else 0

theorem speckerTerm_nonneg (n k : ℕ) : 0 ≤ speckerTerm n k := by
  unfold speckerTerm
  split
  · positivity
  · exact le_rfl

/-- **The Specker sequence**: at stage `n`, the sum of `2^{-(k+1)}` over the indices `k < n` that
have entered the halting set by stage `n`. -/
def speckerVal (n : ℕ) : ℚ := ∑ k ∈ Finset.range n, speckerTerm n k

theorem speckerVal_eq_sum_range {s s' : ℕ} (h : s ≤ s') :
    speckerVal s = ∑ k ∈ Finset.range s', speckerTerm s k := by
  change ∑ k ∈ Finset.range s, speckerTerm s k = _
  refine Finset.sum_subset (Finset.range_subset_range.mpr h) ?_
  intro k _ hk
  simp only [speckerTerm, Finset.mem_range] at hk ⊢
  rw [if_neg]
  rintro ⟨h1, _⟩
  exact hk h1

theorem speckerTerm_le {s s' k : ℕ} (h : s ≤ s') : speckerTerm s k ≤ speckerTerm s' k := by
  unfold speckerTerm
  split
  · rename_i hs
    rw [if_pos ⟨lt_of_lt_of_le hs.1 h, entered_mono h hs.2⟩]
  · exact speckerTerm_nonneg _ _

theorem speckerVal_monotone : Monotone speckerVal := by
  intro s s' h
  rw [speckerVal_eq_sum_range h]
  exact Finset.sum_le_sum fun k _ => speckerTerm_le h

theorem sum_half_pow (n : ℕ) : ∑ k ∈ Finset.range n, (1 : ℚ) / 2 ^ (k + 1) = 1 - 1 / 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring

theorem speckerVal_lt_one (n : ℕ) : speckerVal n < 1 := by
  have h1 : speckerVal n ≤ ∑ k ∈ Finset.range n, (1 : ℚ) / 2 ^ (k + 1) := by
    refine Finset.sum_le_sum fun k _ => ?_
    unfold speckerTerm
    split
    · exact le_rfl
    · positivity
  have h2 : (0 : ℚ) < 1 / 2 ^ n := by positivity
  rw [sum_half_pow] at h1
  linarith

/-- When a new index enters the halting set, the sequence jumps by at least `2^{-(k+1)}`. -/
theorem speckerVal_jump {k s s' : ℕ} (hss : s ≤ s') (hk : k < s') (hne : entered k s = Bool.false)
    (he : entered k s' = Bool.true) :
    speckerVal s + 1 / 2 ^ (k + 1) ≤ speckerVal s' := by
  have hsplit : ∀ j ∈ Finset.range s',
      speckerTerm s j + (if j = k then (1 : ℚ) / 2 ^ (k + 1) else 0) ≤ speckerTerm s' j := by
    intro j _
    by_cases hjk : j = k
    · subst hjk
      have h1 : speckerTerm s j = 0 := by
        unfold speckerTerm
        rw [if_neg]
        rintro ⟨_, h2⟩
        rw [hne] at h2
        exact Bool.noConfusion h2
      have h2 : speckerTerm s' j = (1 : ℚ) / 2 ^ (j + 1) := by
        unfold speckerTerm
        rw [if_pos ⟨hk, he⟩]
      rw [h1, h2, if_pos rfl]
      simp
    · rw [if_neg hjk, add_zero]
      exact speckerTerm_le hss
  have hsum := Finset.sum_le_sum hsplit
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range s') k
    (fun _ => (1 : ℚ) / 2 ^ (k + 1)), if_pos (Finset.mem_range.2 hk)] at hsum
  rw [speckerVal_eq_sum_range hss]
  exact hsum

/-! ### The numerators are computable -/

/-- The numerator of `speckerVal n` over the denominator `2 ^ n`, summed up to `j`. -/
def speckerNumAux (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => speckerNumAux n j + (bif entered j n then 2 ^ (n - (j + 1)) else 0)

/-- The numerator of `speckerVal n` over the denominator `2 ^ n`. -/
def speckerNum (n : ℕ) : ℕ := speckerNumAux n n

theorem computable_speckerNum : Computable speckerNum := by
  have hstep : Primrec₂ fun n : ℕ => fun p : ℕ × ℕ =>
      p.2 + (bif entered p.1 n then 2 ^ (n - (p.1 + 1)) else 0) := by
    have hcond : Primrec fun q : ℕ × (ℕ × ℕ) => entered q.2.1 q.1 :=
      primrec_entered.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
    have hnatpow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
    have hpow : Primrec fun q : ℕ × (ℕ × ℕ) => 2 ^ (q.1 - (q.2.1 + 1)) :=
      hnatpow.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
    have hc : Primrec fun q : ℕ × (ℕ × ℕ) =>
        bif entered q.2.1 q.1 then 2 ^ (q.1 - (q.2.1 + 1)) else 0 :=
      Primrec.cond hcond hpow (Primrec.const 0)
    exact (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) hc).to₂
  have haux : Primrec₂ fun n j : ℕ => speckerNumAux n j := by
    have := Primrec.nat_rec (f := fun _ : ℕ => (0 : ℕ)) (g := fun n : ℕ => fun p : ℕ × ℕ =>
      p.2 + (bif entered p.1 n then 2 ^ (n - (p.1 + 1)) else 0))
      (Primrec.const 0) hstep
    refine this.of_eq fun n j => ?_
    induction j with
    | zero => rfl
    | succ j ih => simp only [speckerNumAux, ih]
  exact (haux.comp Primrec.id Primrec.id).to_comp

theorem speckerNumAux_eq (n : ℕ) : ∀ j, j ≤ n →
    (speckerNumAux n j : ℚ) / 2 ^ n = ∑ k ∈ Finset.range j, speckerTerm n k := by
  intro j
  induction j with
  | zero => intro _; simp [speckerNumAux]
  | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ← ih (by omega), speckerNumAux]
      have hterm : speckerTerm n j =
          ((bif entered j n then (2 : ℚ) ^ (n - (j + 1)) else 0)) / 2 ^ n := by
        unfold speckerTerm
        obtain ⟨m, rfl⟩ : ∃ m, n = m + (j + 1) := ⟨n - (j + 1), by omega⟩
        cases entered j (m + (j + 1)) with
        | false => simp
        | true =>
            rw [if_pos (And.intro (show j < m + (j + 1) by omega) rfl)]
            simp only [Bool.cond_true, Nat.add_sub_cancel, pow_add]
            field_simp
      rw [hterm]
      push_cast
      rw [add_div]
      congr 1
      cases entered j n <;> simp

theorem speckerVal_eq (n : ℕ) : speckerVal n = (speckerNum n : ℚ) / 2 ^ n :=
  (speckerNumAux_eq n n le_rfl).symm

/-! ### No computable modulus of convergence -/

/-- **Specker's theorem**: the sequence, though computable, nondecreasing and bounded, has no
computable modulus of convergence — from one the halting set would be decidable. -/
theorem specker_no_computable_modulus :
    ¬ ∃ g : ℕ → ℕ, Computable g ∧
      ∀ m n, g m ≤ n → speckerVal n - speckerVal (g m) < 1 / 2 ^ m := by
  rintro ⟨g, hg, hmod⟩
  have hdec : ∀ k, HaltK k ↔ entered k (g (k + 2)) = Bool.true := by
    intro k
    constructor
    · intro hk
      by_contra hne
      rw [Bool.not_eq_true] at hne
      obtain ⟨s, hs⟩ := (haltK_iff_entered k).1 hk
      set s' := max (max s (g (k + 2))) (k + 1) with hs'
      have h1 : entered k s' = Bool.true := entered_mono (le_trans (le_max_left _ _)
        (le_max_left _ _)) hs
      have h2 : g (k + 2) ≤ s' := le_trans (le_max_right _ _) (le_max_left _ _)
      have h3 : k < s' := lt_of_lt_of_le (by omega) (le_max_right _ _)
      have hjump := speckerVal_jump h2 h3 hne h1
      have hlt := hmod (k + 2) s' h2
      have hpos : (0 : ℚ) < 1 / 2 ^ (k + 1) := by positivity
      have hhalf : (1 : ℚ) / 2 ^ (k + 2) = (1 / 2 ^ (k + 1)) / 2 := by
        rw [pow_succ]
        ring
      have hpow : (1 : ℚ) / 2 ^ (k + 2) < 1 / 2 ^ (k + 1) := by
        rw [hhalf]; linarith
      linarith
    · intro h
      exact (haltK_iff_entered k).2 ⟨_, h⟩
  have hcomp : ComputablePred HaltK := by
    refine ComputablePred.computable_iff.2 ⟨fun k => entered k (g (k + 2)), ?_, ?_⟩
    · exact (Primrec₂.to_comp primrec_entered).comp Computable.id
        (hg.comp ((Primrec.succ.comp Primrec.succ).to_comp))
    · funext k
      simp only [hdec k]
  exact not_rePred_not_haltK (ComputablePred.to_re hcomp.not)

end Lambda
