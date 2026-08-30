/-
**Post's theorem at level two.**

`Start/ArithHierarchy.lean` builds the arithmetical hierarchy `Σ⁰ₙ`, `Π⁰ₙ`, `Δ⁰ₙ`, and
`Start/LimitLemma.lean` proves Shoenfield's limit lemma: a set is the pointwise limit of a
computable sequence of guesses exactly when it is computable from the halting oracle `∅'`.  This
module joins the two at level two:

```
P ∈ Δ⁰₂  ↔  P is limit computable  ↔  P ≤ᵀ ∅'
```

The easy direction reads a limit off as a pair of two-quantifier definitions: `A x = true` says
both "some stage is followed only by `true` guesses" (`Σ⁰₂`) and "after every stage there is a
`true` guess" (`Π⁰₂`).  For the converse, write `P x ↔ ∃u ∀t R` and `¬P x ↔ ∃u ∀t S` with `R`, `S`
computable, and let the stage-`n` guess compare the least `u ≤ n` whose `R`-run has not yet been
refuted with the least such `u` for `S`: the true side settles on its least witness while every
candidate on the false side is eventually refuted, so the comparison settles correctly.

* `Lambda.Arith.LimitComputablePred` — limit computability, as a predicate on `ℕ`;
* `Lambda.Arith.deltaAt_two_of_limitComputablePred` — limit computable predicates are `Δ⁰₂`;
* `Lambda.Arith.limitComputablePred_of_deltaAt_two` — and conversely;
* `Lambda.Arith.deltaAt_two_iff_limitComputablePred` — **Post's theorem at level two**;
* `Lambda.Arith.deltaAt_two_iff_turingReducible_haltingOracle` — hence `Δ⁰₂` is exactly the class
  of predicates decidable from `∅'`.
-/

import Start.ArithHierarchy
import Start.LimitLemma

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Arith

open Oracle
open scoped Computability

/-- A predicate is **limit computable** when its characteristic function is the pointwise limit of
a computable sequence of guesses. -/
def LimitComputablePred (P : ℕ → Prop) : Prop :=
  ∃ A : ℕ → Bool, LimitComputable A ∧ ∀ x, P x ↔ A x = Bool.true

/-! ## Limit computable predicates are `Δ⁰₂` -/

theorem sigmaAt_two_of_limitComputablePred {P : ℕ → Prop} (h : LimitComputablePred P) :
    SigmaAt 2 P := by
  obtain ⟨A, ⟨g, hg, hlim⟩, hPA⟩ := h
  have hx1 : Computable fun w : ℕ => w.unpair.1.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
  have hx3 : Computable fun w : ℕ => w.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
  have hlt : Computable fun w : ℕ => decide (w.unpair.2 < w.unpair.1.unpair.2) :=
    (Post.primrec_decide (Primrec.nat_lt.comp (Primrec.snd.comp Primrec.unpair)
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))).to_comp
  have hmat : Computable fun w : ℕ =>
      (decide (w.unpair.2 < w.unpair.1.unpair.2) || g w.unpair.1.unpair.1 w.unpair.2) :=
    (Primrec.dom_bool₂ (fun a b => a || b)).to_comp.comp hlt (hg.comp hx1 hx3)
  refine ⟨fun w => (decide (w.unpair.2 < w.unpair.1.unpair.2) ||
      g w.unpair.1.unpair.1 w.unpair.2) = Bool.true,
    ComputablePred.computable_iff.2 ⟨_, hmat, rfl⟩, fun x => ?_⟩
  simp only [qAlt_true_succ, qAlt_false_succ, qAlt_zero, Nat.unpair_pair, Bool.or_eq_true,
    decide_eq_true_eq]
  rw [hPA x]
  obtain ⟨s₀, hs₀⟩ := hlim x
  constructor
  · intro hA
    refine ⟨s₀, fun t => ?_⟩
    rcases lt_or_ge t s₀ with hts | hts
    · exact Or.inl hts
    · exact Or.inr (by rw [hs₀ t hts, hA])
  · rintro ⟨u, hu⟩
    rcases hu (max u s₀) with hlt' | hval
    · exact absurd hlt' (by omega)
    · rw [hs₀ (max u s₀) (le_max_right u s₀)] at hval
      exact hval

theorem piAt_two_of_limitComputablePred {P : ℕ → Prop} (h : LimitComputablePred P) :
    PiAt 2 P := by
  obtain ⟨A, ⟨g, hg, hlim⟩, hPA⟩ := h
  have hx1 : Computable fun w : ℕ => w.unpair.1.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp
  have hx3 : Computable fun w : ℕ => w.unpair.2 := (Primrec.snd.comp Primrec.unpair).to_comp
  have hle : Computable fun w : ℕ => decide (w.unpair.1.unpair.2 ≤ w.unpair.2) :=
    (Post.primrec_decide (Primrec.nat_le.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp Primrec.unpair))).to_comp
  have hmat : Computable fun w : ℕ =>
      (decide (w.unpair.1.unpair.2 ≤ w.unpair.2) && g w.unpair.1.unpair.1 w.unpair.2) :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hle (hg.comp hx1 hx3)
  refine ⟨fun w => (decide (w.unpair.1.unpair.2 ≤ w.unpair.2) &&
      g w.unpair.1.unpair.1 w.unpair.2) = Bool.true,
    ComputablePred.computable_iff.2 ⟨_, hmat, rfl⟩, fun x => ?_⟩
  simp only [qAlt_false_succ, qAlt_true_succ, qAlt_zero, Nat.unpair_pair, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [hPA x]
  obtain ⟨s₀, hs₀⟩ := hlim x
  constructor
  · intro hA y
    refine ⟨max y s₀, le_max_left y s₀, ?_⟩
    rw [hs₀ (max y s₀) (le_max_right y s₀), hA]
  · intro hall
    obtain ⟨z, hz, hgz⟩ := hall s₀
    rw [hs₀ z hz] at hgz
    exact hgz

theorem deltaAt_two_of_limitComputablePred {P : ℕ → Prop} (h : LimitComputablePred P) :
    DeltaAt 2 P :=
  ⟨sigmaAt_two_of_limitComputablePred h, piAt_two_of_limitComputablePred h⟩

/-! ## Bounded search -/

/-- `allB p n`: the bounded conjunction `p 0 && ⋯ && p n`. -/
def allB (p : ℕ → Bool) : ℕ → Bool
  | 0 => p 0
  | (n + 1) => allB p n && p (n + 1)

theorem allB_eq_true_iff (p : ℕ → Bool) (n : ℕ) :
    allB p n = Bool.true ↔ ∀ t ≤ n, p t = Bool.true := by
  induction n with
  | zero => simp [allB]
  | succ n ih =>
      simp only [allB, Bool.and_eq_true, ih]
      constructor
      · rintro ⟨h1, h2⟩ t ht
        rcases Nat.eq_or_lt_of_le ht with rfl | h
        · exact h2
        · exact h1 t (Nat.lt_succ_iff.1 h)
      · intro h
        exact ⟨fun t ht => h t (le_trans ht (Nat.le_succ n)), h (n + 1) le_rfl⟩

/-- `leastB p m`: the least `u ≤ m` with `p u = true`, and `m + 1` if there is none. -/
def leastB (p : ℕ → Bool) : ℕ → ℕ
  | 0 => bif p 0 then 0 else 1
  | (m + 1) => if leastB p m ≤ m then leastB p m else bif p (m + 1) then m + 1 else m + 2

theorem leastB_spec (p : ℕ → Bool) (m : ℕ) (h : leastB p m ≤ m) :
    p (leastB p m) = Bool.true := by
  induction m with
  | zero =>
      cases hp : p 0 with
      | true => simp [leastB, hp]
      | false => simp [leastB, hp] at h
  | succ m ih =>
      by_cases hc : leastB p m ≤ m
      · simp only [leastB, if_pos hc] at h ⊢
        exact ih hc
      · simp only [leastB, if_neg hc] at h ⊢
        cases hp : p (m + 1) with
        | true => simp [hp]
        | false => simp [hp] at h

theorem leastB_le (p : ℕ → Bool) : ∀ (m u : ℕ), u ≤ m → p u = Bool.true → leastB p m ≤ u := by
  intro m
  induction m with
  | zero =>
      intro u hu hp
      interval_cases u
      simp [leastB, hp]
  | succ m ih =>
      intro u hu hp
      by_cases hc : leastB p m ≤ m
      · simp only [leastB, if_pos hc]
        rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hu) with h | rfl
        · exact ih u (Nat.lt_succ_iff.1 h) hp
        · omega
      · simp only [leastB, if_neg hc]
        rcases Nat.eq_or_lt_of_le hu with rfl | h
        · simp [hp]
        · have hle := ih u (Nat.lt_succ_iff.1 h) hp
          exact absurd (le_trans hle (Nat.lt_succ_iff.1 h)) hc

/-! ## The stagewise guess -/

/-- `aliveUpTo r a n`: the run of the matrix `r` at parameter `a` has not been refuted by stage
`n`. -/
def aliveUpTo (r : ℕ → Bool) (a n : ℕ) : Bool := allB (fun t => r (Nat.pair a t)) n

/-- `bestWitness r x n`: the least candidate witness `u ≤ n` still alive at stage `n`. -/
def bestWitness (r : ℕ → Bool) (x n : ℕ) : ℕ :=
  leastB (fun u => aliveUpTo r (Nat.pair x u) n) n

/-- The guess at stage `n`: the `r`-side is winning, i.e. its least surviving candidate is at
least as small as the `s`-side's. -/
def twoGuess (r s : ℕ → Bool) (x n : ℕ) : Bool := decide (bestWitness r x n ≤ bestWitness s x n)

theorem computable₂_allB_family {f : ℕ → ℕ → Bool} (hf : Computable₂ f) :
    Computable₂ fun a n => allB (f a) n := by
  have hstep : Computable₂ fun (a : ℕ × ℕ) (p : ℕ × Bool) => p.2 && f a.1 (p.1 + 1) :=
    (Primrec.dom_bool₂ (fun b c => b && c)).to_comp.comp
      (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
  have h := Computable.nat_rec (f := fun q : ℕ × ℕ => q.2)
    (g := fun q : ℕ × ℕ => f q.1 0)
    (h := fun (a : ℕ × ℕ) (p : ℕ × Bool) => p.2 && f a.1 (p.1 + 1))
    Computable.snd (hf.comp Computable.fst (Computable.const 0)) hstep
  refine h.of_eq fun q => ?_
  obtain ⟨a, n⟩ := q
  simp only
  induction n with
  | zero => rfl
  | succ n ih => simp [allB, ih]

theorem computable₂_leastB_family {f : ℕ → ℕ → Bool} (hf : Computable₂ f) :
    Computable₂ fun a m => leastB (f a) m := by
  have hdec : Computable fun z : (ℕ × ℕ) × (ℕ × ℕ) => decide (z.2.2 ≤ z.2.1) :=
    (Post.primrec_decide (Primrec.nat_le.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd))).to_comp
  have hstep : Computable₂ fun (a : ℕ × ℕ) (p : ℕ × ℕ) =>
      cond (decide (p.2 ≤ p.1)) p.2 (cond (f a.1 (p.1 + 1)) (p.1 + 1) (p.1 + 2)) := by
    refine Computable.cond hdec (Computable.snd.comp Computable.snd) ?_
    exact Computable.cond
      (hf.comp (Computable.fst.comp Computable.fst)
        (Computable.succ.comp (Computable.fst.comp Computable.snd)))
      (Computable.succ.comp (Computable.fst.comp Computable.snd))
      ((Primrec.succ.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))).to_comp)
  have hbase : Computable fun q : ℕ × ℕ => cond (f q.1 0) 0 1 :=
    Computable.cond (hf.comp Computable.fst (Computable.const 0))
      (Computable.const 0) (Computable.const 1)
  have h := Computable.nat_rec (f := fun q : ℕ × ℕ => q.2)
    (g := fun q : ℕ × ℕ => cond (f q.1 0) 0 1)
    (h := fun (a : ℕ × ℕ) (p : ℕ × ℕ) =>
      cond (decide (p.2 ≤ p.1)) p.2 (cond (f a.1 (p.1 + 1)) (p.1 + 1) (p.1 + 2)))
    Computable.snd hbase hstep
  refine h.of_eq fun q => ?_
  obtain ⟨a, m⟩ := q
  simp only
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [leastB, ← ih]
      by_cases hc : (Nat.rec (motive := fun _ => ℕ) (cond (f a 0) 0 1)
        (fun y IH => cond (decide (IH ≤ y)) IH (cond (f a (y + 1)) (y + 1) (y + 2))) m) ≤ m
      · simp [hc]
      · simp [hc]

theorem computable₂_aliveUpTo {r : ℕ → Bool} (hr : Computable r) :
    Computable₂ (aliveUpTo r) :=
  computable₂_allB_family (hr.comp (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd))

theorem computable₂_bestWitness {r : ℕ → Bool} (hr : Computable r) :
    Computable₂ (bestWitness r) := by
  have hF : Computable₂ fun a u : ℕ => aliveUpTo r (Nat.pair a.unpair.1 u) a.unpair.2 :=
    (computable₂_aliveUpTo hr).comp
      (Primrec₂.natPair.to_comp.comp
        ((Primrec.fst.comp Primrec.unpair).to_comp.comp Computable.fst) Computable.snd)
      ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst)
  have h : Computable fun q : ℕ × ℕ =>
      leastB (fun u => aliveUpTo r (Nat.pair (Nat.pair q.1 q.2).unpair.1 u)
        (Nat.pair q.1 q.2).unpair.2) q.2 :=
    (computable₂_leastB_family hF).comp
      (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd) Computable.snd
  exact h.of_eq fun q => by simp [bestWitness]

theorem computable₂_twoGuess {r s : ℕ → Bool} (hr : Computable r) (hs : Computable s) :
    Computable₂ (twoGuess r s) :=
  (Post.primrec_decide Primrec.nat_le).to_comp.comp
    ((computable₂_bestWitness hr).pair (computable₂_bestWitness hs))

/-! ## Convergence of the guesses -/

/-- If every candidate below `a` is refuted at some stage, then from some stage on they are all
refuted simultaneously. -/
theorem exists_stage_dead (r : ℕ → Bool) (x a : ℕ)
    (h : ∀ u < a, ∃ t, r (Nat.pair (Nat.pair x u) t) ≠ Bool.true) :
    ∃ N, ∀ n, N ≤ n → ∀ u < a, aliveUpTo r (Nat.pair x u) n ≠ Bool.true := by
  induction a with
  | zero => exact ⟨0, fun n _ u hu => absurd hu (Nat.not_lt_zero u)⟩
  | succ a ih =>
      obtain ⟨N, hN⟩ := ih fun u hu => h u (Nat.lt_succ_of_lt hu)
      obtain ⟨t, ht⟩ := h a (Nat.lt_succ_self a)
      refine ⟨max N t, fun n hn u hu => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hlt | rfl
      · exact hN n (le_trans (le_max_left N t) hn) u hlt
      · intro hcon
        exact ht ((allB_eq_true_iff _ n).1 hcon t (le_trans (le_max_right N t) hn))

/-- If `a` is the least true witness then the surviving candidate settles on it. -/
theorem bestWitness_eventually (r : ℕ → Bool) {x a : ℕ}
    (ha : ∀ t, r (Nat.pair (Nat.pair x a) t) = Bool.true)
    (hmin : ∀ u < a, ∃ t, r (Nat.pair (Nat.pair x u) t) ≠ Bool.true) :
    ∃ N, ∀ n, N ≤ n → bestWitness r x n = a := by
  obtain ⟨N, hN⟩ := exists_stage_dead r x a hmin
  refine ⟨max N a, fun n hn => ?_⟩
  have hna : a ≤ n := le_trans (le_max_right N a) hn
  have halive : aliveUpTo r (Nat.pair x a) n = Bool.true :=
    (allB_eq_true_iff _ n).2 fun t _ => ha t
  have hle : bestWitness r x n ≤ a :=
    leastB_le (fun u => aliveUpTo r (Nat.pair x u) n) n a hna halive
  by_contra hne
  have hlt : bestWitness r x n < a := lt_of_le_of_ne hle hne
  have hspec := leastB_spec (fun u => aliveUpTo r (Nat.pair x u) n) n (le_trans hle hna)
  exact hN n (le_trans (le_max_left N a) hn) _ hlt hspec

/-- If there is no true witness at all then the surviving candidate escapes every bound. -/
theorem bestWitness_large (r : ℕ → Bool) {x : ℕ}
    (h : ∀ u, ∃ t, r (Nat.pair (Nat.pair x u) t) ≠ Bool.true) (a : ℕ) :
    ∃ N, ∀ n, N ≤ n → a < bestWitness r x n := by
  obtain ⟨N, hN⟩ := exists_stage_dead r x (a + 1) fun u _ => h u
  refine ⟨max N (a + 1), fun n hn => ?_⟩
  by_contra hcon
  have hle : bestWitness r x n ≤ a := Nat.le_of_not_lt hcon
  have hna : a + 1 ≤ n := le_trans (le_max_right N (a + 1)) hn
  have hbn : bestWitness r x n ≤ n := by omega
  have hspec := leastB_spec (fun u => aliveUpTo r (Nat.pair x u) n) n hbn
  have hlt : bestWitness r x n < a + 1 := by omega
  exact hN n (le_trans (le_max_left N (a + 1)) hn) _ hlt hspec

/-! ## `Δ⁰₂` predicates are limit computable -/

theorem limitComputablePred_of_deltaAt_two {P : ℕ → Prop} (h : DeltaAt 2 P) :
    LimitComputablePred P := by
  classical
  obtain ⟨hsig, hpi⟩ := h
  obtain ⟨R, hR, hPR⟩ := hsig
  obtain ⟨S, hS, hPS⟩ := piAt_iff_sigmaAt_not.1 hpi
  obtain ⟨r, hr, hRr⟩ := ComputablePred.computable_iff.1 hR
  obtain ⟨s, hs, hSs⟩ := ComputablePred.computable_iff.1 hS
  subst hRr
  subst hSs
  have hP : ∀ x, P x ↔ ∃ u, ∀ t, r (Nat.pair (Nat.pair x u) t) = Bool.true := by
    intro x
    rw [hPR x]
    simp only [qAlt_true_succ, qAlt_false_succ, qAlt_zero]
  have hnP : ∀ x, ¬ P x ↔ ∃ u, ∀ t, s (Nat.pair (Nat.pair x u) t) = Bool.true := by
    intro x
    have hx := hPS x
    simp only [qAlt_true_succ, qAlt_false_succ, qAlt_zero] at hx
    exact hx
  refine ⟨fun x => decide (P x),
    ⟨twoGuess r s, computable₂_twoGuess hr hs, fun x => ?_⟩, fun x => by simp⟩
  by_cases hx : P x
  · have hex := (hP x).1 hx
    have ha : ∀ t, r (Nat.pair (Nat.pair x (Nat.find hex)) t) = Bool.true := Nat.find_spec hex
    have hamin : ∀ u < Nat.find hex, ∃ t, r (Nat.pair (Nat.pair x u) t) ≠ Bool.true :=
      fun u hu => not_forall.1 (Nat.find_min hex hu)
    obtain ⟨N₁, hN₁⟩ := bestWitness_eventually r ha hamin
    have hnos : ∀ u, ∃ t, s (Nat.pair (Nat.pair x u) t) ≠ Bool.true := by
      intro u
      by_contra hcon
      exact (hnP x).2 ⟨u, fun t => not_not.1 (not_exists.1 hcon t)⟩ hx
    obtain ⟨N₂, hN₂⟩ := bestWitness_large s hnos (Nat.find hex)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have e1 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    have e2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
    simp only [twoGuess, hx, decide_true, decide_eq_true_eq]
    omega
  · have hex := (hnP x).1 hx
    have hb : ∀ t, s (Nat.pair (Nat.pair x (Nat.find hex)) t) = Bool.true := Nat.find_spec hex
    have hbmin : ∀ u < Nat.find hex, ∃ t, s (Nat.pair (Nat.pair x u) t) ≠ Bool.true :=
      fun u hu => not_forall.1 (Nat.find_min hex hu)
    obtain ⟨N₁, hN₁⟩ := bestWitness_eventually s hb hbmin
    have hnor : ∀ u, ∃ t, r (Nat.pair (Nat.pair x u) t) ≠ Bool.true := by
      intro u
      by_contra hcon
      exact hx ((hP x).2 ⟨u, fun t => not_not.1 (not_exists.1 hcon t)⟩)
    obtain ⟨N₂, hN₂⟩ := bestWitness_large r hnor (Nat.find hex)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have e1 := hN₁ n (le_trans (le_max_left N₁ N₂) hn)
    have e2 := hN₂ n (le_trans (le_max_right N₁ N₂) hn)
    simp only [twoGuess, hx, decide_false, decide_eq_false_iff_not, not_le]
    omega

/-- **Post's theorem at level two**: `Δ⁰₂` is exactly the class of limit computable
predicates. -/
theorem deltaAt_two_iff_limitComputablePred {P : ℕ → Prop} :
    DeltaAt 2 P ↔ LimitComputablePred P :=
  ⟨limitComputablePred_of_deltaAt_two, deltaAt_two_of_limitComputablePred⟩

/-- Combining with Shoenfield's limit lemma: `Δ⁰₂` is exactly the class of predicates decidable
from the halting oracle `∅'`. -/
theorem deltaAt_two_iff_turingReducible_haltingOracle {P : ℕ → Prop} :
    DeltaAt 2 P ↔ ∃ A : ℕ → Bool, (∀ x, P x ↔ A x = Bool.true) ∧
      oracleFun A ≤ᵀ oracleFun haltingOracle := by
  rw [deltaAt_two_iff_limitComputablePred]
  constructor
  · rintro ⟨A, hA, hPA⟩
    exact ⟨A, hPA, (limitComputable_iff_turingReducible_haltingOracle A).1 hA⟩
  · rintro ⟨A, hPA, hA⟩
    exact ⟨A, (limitComputable_iff_turingReducible_haltingOracle A).2 hA, hPA⟩

end Arith
end Lambda
