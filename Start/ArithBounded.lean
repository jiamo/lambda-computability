/-
**Bounded quantification in the arithmetical hierarchy.**

Unbounded quantifiers raise the level of a predicate; *bounded* ones do not.  This module proves
that every level `Σ⁰ₙ` and `Π⁰ₙ` of the hierarchy of `Start/ArithHierarchy.lean` is closed under
both bounded quantifiers, with a computable bound.

* `Lambda.Arith.allLt`, `Lambda.Arith.exLt` — bounded conjunction and disjunction of a `Bool`
  test, with their characterizations and their computability.
* `Lambda.Arith.computablePred_ball_lt`, `Lambda.Arith.computablePred_bex_lt` — the level-zero
  case: computable predicates are closed under bounded quantification.
* `Lambda.Arith.exists_code_of_ball_exists` — the collection principle: finitely many witnesses
  can be packed into a single number.
* `Lambda.Arith.SigmaAt.ball_lt`, `Lambda.Arith.SigmaAt.bex_lt`, `Lambda.Arith.PiAt.ball_lt`,
  `Lambda.Arith.PiAt.bex_lt` — the closure theorems, proved by one induction on the level: the
  bounded existential is absorbed into the outermost existential quantifier, and the bounded
  universal is moved inside it by collection.
-/

import Start.ArithHierarchy

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Arith

open Encodable Denumerable

/-! ## Bounded conjunction and disjunction of a test -/

/-- `allLt p k` is `true` exactly when the test `p` succeeds at every argument below `k`. -/
def allLt (p : ℕ → Bool) : ℕ → Bool
  | 0 => Bool.true
  | (k + 1) => cond (allLt p k) (p k) Bool.false

/-- `exLt p k` is `true` exactly when the test `p` succeeds at some argument below `k`. -/
def exLt (p : ℕ → Bool) : ℕ → Bool
  | 0 => Bool.false
  | (k + 1) => cond (exLt p k) Bool.true (p k)

theorem allLt_eq_true_iff (p : ℕ → Bool) :
    ∀ k : ℕ, allLt p k = Bool.true ↔ ∀ y < k, p y = Bool.true := by
  intro k
  induction k with
  | zero => simp [allLt]
  | succ k ih =>
      constructor
      · intro h y hy
        rw [allLt] at h
        cases hk : allLt p k with
        | false => rw [hk] at h; simp at h
        | true =>
            rw [hk] at h
            simp only [cond_true] at h
            rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy' | rfl
            · exact (ih.1 hk) y hy'
            · exact h
      · intro h
        rw [allLt, ih.2 fun y hy => h y (by omega)]
        simpa using h k (Nat.lt_succ_self k)

theorem exLt_eq_true_iff (p : ℕ → Bool) :
    ∀ k : ℕ, exLt p k = Bool.true ↔ ∃ y < k, p y = Bool.true := by
  intro k
  induction k with
  | zero => simp [exLt]
  | succ k ih =>
      constructor
      · intro h
        rw [exLt] at h
        cases hk : exLt p k with
        | true =>
            obtain ⟨y, hy, hpy⟩ := ih.1 hk
            exact ⟨y, by omega, hpy⟩
        | false =>
            rw [hk] at h
            simp only [cond_false] at h
            exact ⟨k, Nat.lt_succ_self k, h⟩
      · rintro ⟨y, hy, hpy⟩
        rw [exLt]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy' | rfl
        · rw [ih.2 ⟨y, hy', hpy⟩]
          simp
        · cases hk : exLt p y with
          | true => simp
          | false => simpa using hpy

/-- The bounded conjunction of a computable test, at a computable bound, is computable. -/
theorem computable_allLt {f : ℕ → ℕ → Bool} (hf : Computable₂ f) {b : ℕ → ℕ}
    (hb : Computable b) : Computable fun x => allLt (f x) (b x) := by
  have hstep : Computable₂ fun (x : ℕ) (q : ℕ × Bool) => cond q.2 (f x q.1) Bool.false :=
    Computable.cond (Computable.snd.comp Computable.snd)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.const Bool.false)
  exact (Computable.nat_rec hb (Computable.const Bool.true) hstep).of_eq fun x => by
    induction b x with
    | zero => rfl
    | succ k ih => simp only [allLt, ih]

/-- The bounded disjunction of a computable test, at a computable bound, is computable. -/
theorem computable_exLt {f : ℕ → ℕ → Bool} (hf : Computable₂ f) {b : ℕ → ℕ}
    (hb : Computable b) : Computable fun x => exLt (f x) (b x) := by
  have hstep : Computable₂ fun (x : ℕ) (q : ℕ × Bool) => cond q.2 Bool.true (f x q.1) :=
    Computable.cond (Computable.snd.comp Computable.snd) (Computable.const Bool.true)
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
  exact (Computable.nat_rec hb (Computable.const Bool.false) hstep).of_eq fun x => by
    induction b x with
    | zero => rfl
    | succ k ih => simp only [exLt, ih]

/-! ## Level zero -/

/-- **Computable predicates are closed under bounded universal quantification.** -/
theorem computablePred_ball_lt {Q : ℕ → Prop} (hQ : ComputablePred Q) {b : ℕ → ℕ}
    (hb : Computable b) : ComputablePred fun x => ∀ y < b x, Q (Nat.pair x y) := by
  obtain ⟨f, hf, hQf⟩ := ComputablePred.computable_iff.1 hQ
  subst hQf
  have hf2 : Computable₂ fun x y : ℕ => f (Nat.pair x y) :=
    hf.comp (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)
  refine ComputablePred.computable_iff.2
    ⟨fun x => allLt (fun y => f (Nat.pair x y)) (b x), computable_allLt hf2 hb, ?_⟩
  funext x
  exact propext (allLt_eq_true_iff (fun y => f (Nat.pair x y)) (b x)).symm

/-- **Computable predicates are closed under bounded existential quantification.** -/
theorem computablePred_bex_lt {Q : ℕ → Prop} (hQ : ComputablePred Q) {b : ℕ → ℕ}
    (hb : Computable b) : ComputablePred fun x => ∃ y < b x, Q (Nat.pair x y) := by
  obtain ⟨f, hf, hQf⟩ := ComputablePred.computable_iff.1 hQ
  subst hQf
  have hf2 : Computable₂ fun x y : ℕ => f (Nat.pair x y) :=
    hf.comp (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)
  refine ComputablePred.computable_iff.2
    ⟨fun x => exLt (fun y => f (Nat.pair x y)) (b x), computable_exLt hf2 hb, ?_⟩
  funext x
  exact propext (exLt_eq_true_iff (fun y => f (Nat.pair x y)) (b x)).symm

/-! ## Padding a computable predicate into any level -/

theorem sigmaAt_of_computablePred {P : ℕ → Prop} (h : ComputablePred P) :
    ∀ n : ℕ, SigmaAt n P
  | 0 => sigmaAt_zero_iff.2 h
  | (n + 1) => (sigmaAt_of_computablePred h n).succ

theorem piAt_of_computablePred {P : ℕ → Prop} (h : ComputablePred P) : ∀ n : ℕ, PiAt n P
  | 0 => piAt_zero_iff.2 h
  | (n + 1) => (piAt_of_computablePred h n).succ

/-! ## Collection -/

/-- **Collection.**  If every argument below `k` has a witness, then a single number codes a
list of witnesses for all of them. -/
theorem exists_code_of_ball_exists (S : ℕ → ℕ → Prop) :
    ∀ k : ℕ, (∀ y < k, ∃ z, S y z) →
      ∃ w : ℕ, ∀ y < k, S y (List.getD (ofNat (List ℕ) w) y 0) := by
  have key : ∀ k : ℕ, (∀ y < k, ∃ z, S y z) →
      ∃ L : List ℕ, L.length = k ∧ ∀ y < k, S y (List.getD L y 0) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨[], rfl, by omega⟩
    | succ k ih =>
        intro h
        obtain ⟨L, hlen, hL⟩ := ih fun y hy => h y (by omega)
        obtain ⟨z, hz⟩ := h k (Nat.lt_succ_self k)
        refine ⟨L ++ [z], by simp [hlen], fun y hy => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy' | rfl
        · rw [List.getD_append _ _ _ _ (by omega)]
          exact hL y hy'
        · rw [List.getD_append_right _ _ _ _ (by omega)]
          simpa [hlen] using hz
  intro k h
  obtain ⟨L, -, hL⟩ := key k h
  exact ⟨Encodable.encode L, by simpa [Denumerable.ofNat_encode] using hL⟩

/-! ## The closure theorem -/

/-- Both bounded quantifiers at once, by induction on the level.  The `Π` halves are obtained
from the `Σ` halves of the same level by de Morgan. -/
theorem sigmaAt_bounded_closure : ∀ n : ℕ,
    (∀ (Q : ℕ → Prop) (b : ℕ → ℕ), SigmaAt n Q → Computable b →
      SigmaAt n fun x => ∀ y < b x, Q (Nat.pair x y)) ∧
    (∀ (Q : ℕ → Prop) (b : ℕ → ℕ), SigmaAt n Q → Computable b →
      SigmaAt n fun x => ∃ y < b x, Q (Nat.pair x y)) := by
  classical
  intro n
  induction n with
  | zero =>
      refine ⟨fun Q b hQ hb => ?_, fun Q b hQ hb => ?_⟩
      · exact sigmaAt_zero_iff.2 (computablePred_ball_lt (sigmaAt_zero_iff.1 hQ) hb)
      · exact sigmaAt_zero_iff.2 (computablePred_bex_lt (sigmaAt_zero_iff.1 hQ) hb)
  | succ n ih =>
      -- the `Π` closure at level `n`, by de Morgan from the induction hypothesis
      have hpi_ball : ∀ (R : ℕ → Prop) (c : ℕ → ℕ), PiAt n R → Computable c →
          PiAt n fun v => ∀ y < c v, R (Nat.pair v y) := by
        intro R c hR hc
        refine piAt_iff_sigmaAt_not.2 ?_
        have hnot : SigmaAt n fun v => ∃ y < c v, (fun u => ¬ R u) (Nat.pair v y) :=
          ih.2 _ c (piAt_iff_sigmaAt_not.1 hR) hc
        refine hnot.of_iff fun v => ?_
        constructor
        · intro h
          by_contra hcon
          push_neg at hcon
          exact h fun y hy => hcon y hy
        · rintro ⟨y, hy, hRy⟩ hall
          exact hRy (hall y hy)
      refine ⟨fun Q b hQ hb => ?_, fun Q b hQ hb => ?_⟩
      · -- bounded universal quantification, by collection
        obtain ⟨R, hR, hQR⟩ := sigmaAt_succ_iff.1 hQ
        have hg : Computable fun u : ℕ =>
            Nat.pair (Nat.pair u.unpair.1.unpair.1 u.unpair.2)
              (List.getD (ofNat (List ℕ) u.unpair.1.unpair.2) u.unpair.2 0) := by
          have hv : Primrec fun u : ℕ => u.unpair.1 := Primrec.fst.comp Primrec.unpair
          have hy : Primrec fun u : ℕ => u.unpair.2 := Primrec.snd.comp Primrec.unpair
          have hx : Primrec fun u : ℕ => u.unpair.1.unpair.1 :=
            Primrec.fst.comp (Primrec.unpair.comp hv)
          have hw : Primrec fun u : ℕ => u.unpair.1.unpair.2 :=
            Primrec.snd.comp (Primrec.unpair.comp hv)
          have hlist : Computable fun u : ℕ => ofNat (List ℕ) u.unpair.1.unpair.2 :=
            (Computable.ofNat (List ℕ)).comp hw.to_comp
          have hgetD : Computable fun u : ℕ =>
              List.getD (ofNat (List ℕ) u.unpair.1.unpair.2) u.unpair.2 0 :=
            (Primrec.list_getD (0 : ℕ)).to_comp.comp hlist hy.to_comp
          exact Primrec₂.natPair.to_comp.comp
            (Primrec₂.natPair.to_comp.comp hx.to_comp hy.to_comp) hgetD
        have hc : Computable fun v : ℕ => b v.unpair.1 :=
          hb.comp (Primrec.fst.comp Primrec.unpair).to_comp
        have hM : PiAt n fun v => ∀ y < b v.unpair.1,
            (fun u => R (Nat.pair (Nat.pair u.unpair.1.unpair.1 u.unpair.2)
              (List.getD (ofNat (List ℕ) u.unpair.1.unpair.2) u.unpair.2 0)))
                (Nat.pair v y) :=
          hpi_ball _ _ (hR.subst hg) hc
        refine sigmaAt_succ_iff.2 ⟨_, hM, fun x => ?_⟩
        simp only [Nat.unpair_pair]
        constructor
        · intro hx
          obtain ⟨w, hw⟩ := exists_code_of_ball_exists
            (fun y z => R (Nat.pair (Nat.pair x y) z)) (b x)
            (fun y hy => (hQR (Nat.pair x y)).1 (hx y hy))
          exact ⟨w, fun y hy => by simpa [Nat.unpair_pair] using hw y hy⟩
        · rintro ⟨w, hw⟩ y hy
          exact (hQR (Nat.pair x y)).2
            ⟨List.getD (ofNat (List ℕ) w) y 0, by simpa [Nat.unpair_pair] using hw y hy⟩
      · -- bounded existential quantification, absorbed into the outermost quantifier
        obtain ⟨R, hR, hQR⟩ := sigmaAt_succ_iff.1 hQ
        have hlt : ComputablePred fun w : ℕ => w.unpair.2.unpair.1 < b w.unpair.1 := by
          have hltnat : ComputablePred fun q : ℕ => q.unpair.1 < q.unpair.2 :=
            (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.unpair)
              (Primrec.snd.comp Primrec.unpair)).computablePred
          have hpr : Computable fun w : ℕ => Nat.pair w.unpair.2.unpair.1 (b w.unpair.1) := by
            have h1 : Primrec fun w : ℕ => w.unpair.2.unpair.1 :=
              Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
            have h2 : Computable fun w : ℕ => b w.unpair.1 :=
              hb.comp (Primrec.fst.comp Primrec.unpair).to_comp
            exact Primrec₂.natPair.to_comp.comp h1.to_comp h2
          have h := computablePred_comp hltnat hpr
          simpa using h
        have hg : Computable fun w : ℕ =>
            Nat.pair (Nat.pair w.unpair.1 w.unpair.2.unpair.1) w.unpair.2.unpair.2 := by
          have h1 : Primrec fun w : ℕ => w.unpair.1 := Primrec.fst.comp Primrec.unpair
          have h2 : Primrec fun w : ℕ => w.unpair.2 := Primrec.snd.comp Primrec.unpair
          exact (Primrec₂.natPair.comp
            (Primrec₂.natPair.comp h1 (Primrec.fst.comp (Primrec.unpair.comp h2)))
            (Primrec.snd.comp (Primrec.unpair.comp h2))).to_comp
        have hM : PiAt n fun w => (w.unpair.2.unpair.1 < b w.unpair.1) ∧
            R (Nat.pair (Nat.pair w.unpair.1 w.unpair.2.unpair.1) w.unpair.2.unpair.2) :=
          (piAt_of_computablePred hlt n).and (hR.subst hg)
        refine sigmaAt_succ_iff.2 ⟨_, hM, fun x => ?_⟩
        simp only [Nat.unpair_pair]
        constructor
        · rintro ⟨y, hy, hQy⟩
          obtain ⟨z, hz⟩ := (hQR (Nat.pair x y)).1 hQy
          exact ⟨Nat.pair y z, by simpa [Nat.unpair_pair] using ⟨hy, hz⟩⟩
        · rintro ⟨v, hv1, hv2⟩
          exact ⟨v.unpair.1, hv1, (hQR (Nat.pair x v.unpair.1)).2 ⟨v.unpair.2, hv2⟩⟩

theorem SigmaAt.ball_lt {n : ℕ} {Q : ℕ → Prop} (hQ : SigmaAt n Q) {b : ℕ → ℕ}
    (hb : Computable b) : SigmaAt n fun x => ∀ y < b x, Q (Nat.pair x y) :=
  (sigmaAt_bounded_closure n).1 Q b hQ hb

theorem SigmaAt.bex_lt {n : ℕ} {Q : ℕ → Prop} (hQ : SigmaAt n Q) {b : ℕ → ℕ}
    (hb : Computable b) : SigmaAt n fun x => ∃ y < b x, Q (Nat.pair x y) :=
  (sigmaAt_bounded_closure n).2 Q b hQ hb

theorem PiAt.ball_lt {n : ℕ} {Q : ℕ → Prop} (hQ : PiAt n Q) {b : ℕ → ℕ}
    (hb : Computable b) : PiAt n fun x => ∀ y < b x, Q (Nat.pair x y) := by
  classical
  refine piAt_iff_sigmaAt_not.2 ?_
  refine ((piAt_iff_sigmaAt_not.1 hQ).bex_lt hb).of_iff fun x => ?_
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact h fun y hy => hcon y hy
  · rintro ⟨y, hy, hQy⟩ hall
    exact hQy (hall y hy)

theorem PiAt.bex_lt {n : ℕ} {Q : ℕ → Prop} (hQ : PiAt n Q) {b : ℕ → ℕ}
    (hb : Computable b) : PiAt n fun x => ∃ y < b x, Q (Nat.pair x y) := by
  classical
  refine piAt_iff_sigmaAt_not.2 ?_
  refine ((piAt_iff_sigmaAt_not.1 hQ).ball_lt hb).of_iff fun x => ?_
  constructor
  · intro h y hy hQy
    exact h ⟨y, hy, hQy⟩
  · rintro h ⟨y, hy, hQy⟩
    exact h y hy hQy

end Arith
end Lambda
