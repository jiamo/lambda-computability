/-
**Shoenfield's limit lemma.**

A set of numbers is *limit computable* when it is the pointwise limit of a computable sequence of
guesses: there is a computable `g` with `A x = lim_s g x s`, the guesses being allowed to change
finitely often at each argument, with no bound on when they settle.  Shoenfield's limit lemma
identifies this class with the sets computable from the halting problem:

```
LimitComputable A ↔ A ≤ᵀ ∅'
```

Both directions use the machinery already in place.  From right to left, a reduction to `∅'` is a
machine `Φ_e^{∅'}`; running it for `s` stages against the stage-`s` approximation
`Lambda.Oracle.jumpApprox` of `∅'` (`Start/JumpApprox.lean`) gives the guesses.  They settle
because the true computation converges at some stage `t₀`, and below the finitely many oracle
questions asked up to `t₀` the approximation is eventually correct, so from some stage on the
simulated run is the true run.  From left to right, "the guess at `x` has changed after stage `t`"
is a `Σ₁` question, hence decidable from `∅'` by `Start/JumpSigmaOne.lean`; asking `∅'` for the
least `t` after which the guess never changes and reading off `g x t` computes `A`.

* `Lambda.Oracle.LimitComputable` — the definition;
* `Lambda.Oracle.limitGuess` — the stagewise guess of a machine with the approximated oracle;
* `Lambda.Oracle.limitComputable_of_turingReducible`,
  `Lambda.Oracle.turingReducible_of_limitComputable` — the two directions;
* `Lambda.Oracle.limitComputable_iff_turingReducible_haltingOracle` — **the limit lemma**;
* `Lambda.Oracle.limitComputable_of_repred` — every r.e. set is limit computable;
* `Lambda.Oracle.not_limitComputable_jumpChar_haltingOracle` — `∅''` is not.
-/

import Start.JumpApprox
import Start.OracleSound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)
open scoped Computability

/-- `A` is **limit computable**: some computable sequence of guesses converges to `A`
pointwise. -/
def LimitComputable (A : ℕ → Bool) : Prop :=
  ∃ g : ℕ → ℕ → Bool, Computable₂ g ∧ ∀ x, ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → g x s = A x

/-! ## A reduction to `∅'` gives a computable approximation -/

/-- The stagewise guess: run the machine `c` on `x` for `s` stages against the stage-`s`
approximation of `∅'`, and accept when the first value found is `1`. -/
def limitGuess (c : Code) (x s : ℕ) : Bool :=
  decide (scanOf (fun t => oracleStep (fun n => jumpApprox s n) c x t) s = some 1)

theorem primrec₂_limitGuess (c : Code) : Primrec₂ (limitGuess c) := by
  have hstep : Primrec fun p : (ℕ × ℕ) × ℕ =>
      oracleStep (fun n => jumpApprox p.1.1 n) c p.1.2 p.2 :=
    primrec_oracleStep_family primrec₂_jumpApprox c
  have hbody : Primrec₂ fun (a : ℕ × ℕ) (q : ℕ × Option ℕ) =>
      Option.casesOn (motive := fun _ => Option ℕ) q.2
        (oracleStep (fun n => jumpApprox a.2 n) c a.1 q.1) fun y => some y := by
    refine Primrec.option_casesOn (Primrec.snd.comp Primrec.snd) ?_ ?_
    · exact hstep.comp
        (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair
          (Primrec.fst.comp Primrec.snd))
    · exact (Primrec.option_some.comp Primrec.snd).to₂
  have hscan : Primrec fun a : ℕ × ℕ =>
      scanOf (fun t => oracleStep (fun n => jumpApprox a.2 n) c a.1 t) a.2 :=
    Primrec.nat_rec' Primrec.snd (Primrec.const none) hbody
  exact primrec_decide_pred (Primrec.eq.comp hscan (Primrec.const (some 1)))

theorem computable₂_limitGuess (c : Code) : Computable₂ (limitGuess c) :=
  Primrec₂.to_comp (primrec₂_limitGuess c)

/-- The guesses settle: from some stage on, the simulated run is the true run. -/
theorem limitGuess_eventually {A : ℕ → Bool} {c : Code}
    (hc : ∀ x, evalOracle haltingOracle c x = oracleFun A x) (x : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → limitGuess c x s = A x := by
  have hmem : (if A x then 1 else 0) ∈ evalOracle haltingOracle c x := by
    rw [hc x]
    exact Part.mem_some _
  obtain ⟨t₀, ht₀, hlt⟩ := mem_evalOracle_iff.1 hmem
  obtain ⟨s₀, hs₀⟩ := exists_jumpApprox_agree (t₀ + 1)
  refine ⟨max s₀ (t₀ + 1), fun s hs => ?_⟩
  have hagree : ∀ t, t ≤ t₀ →
      oracleStep (fun n => jumpApprox s n) c x t = oracleStep haltingOracle c x t := by
    intro t ht
    refine oracleStep_congr (u := t₀ + 1) (Nat.lt_succ_of_le ht) ?_
    intro n hn
    exact hs₀ s (le_trans (le_max_left _ _) hs) n hn
  have hnone : ∀ u < t₀, oracleStep (fun n => jumpApprox s n) c x u = none := by
    intro u hu
    rw [hagree u (le_of_lt hu)]
    exact hlt u hu
  have hval : oracleStep (fun n => jumpApprox s n) c x t₀ = some (if A x then 1 else 0) := by
    rw [hagree t₀ le_rfl]
    exact ht₀
  have hb : t₀ < s := lt_of_lt_of_le (Nat.lt_succ_self t₀) (le_trans (le_max_right _ _) hs)
  have hscan := scanOf_eq_some hnone hval hb
  by_cases hA : A x
  · simp [limitGuess, hscan, hA]
  · simp [limitGuess, hscan, hA]

/-- **A set computable from `∅'` is limit computable.** -/
theorem limitComputable_of_turingReducible {A : ℕ → Bool}
    (h : oracleFun A ≤ᵀ oracleFun haltingOracle) : LimitComputable A := by
  obtain ⟨e, he⟩ := exists_index_of_recursiveIn h
  exact ⟨limitGuess (ofNat Code e), computable₂_limitGuess _,
    limitGuess_eventually fun y => congrFun he y⟩

/-! ## A computable approximation gives a reduction to `∅'` -/

/-- Enumerability from a computable test, for a test that is only computable (not primitive
recursive). -/
theorem rePred_of_exists_test_comp {P : ℕ → Prop} (test : ℕ → ℕ → Bool)
    (htest : Computable₂ test) (hiff : ∀ x, P x ↔ ∃ k, test x k = true) : REPred P := by
  have hr : Partrec fun x : ℕ => Nat.rfind fun k => (Part.some (test x k) : Part Bool) :=
    Partrec.rfind htest.partrec₂
  refine hr.dom_re.of_eq fun x => ?_
  rw [hiff x]
  constructor
  · intro hdom
    obtain ⟨k, hk, -⟩ := Nat.rfind_dom.1 hdom
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact Nat.rfind_dom.2 ⟨k, by simp [hk], fun {_} _ => trivial⟩

/-- **A limit computable set is computable from `∅'`.** -/
theorem turingReducible_of_limitComputable {A : ℕ → Bool} (h : LimitComputable A) :
    oracleFun A ≤ᵀ oracleFun haltingOracle := by
  classical
  obtain ⟨g, hg, hlim⟩ := h
  -- "the guess at `z.unpair.1` still changes after stage `z.unpair.2`" is a `Σ₁` question
  set P : ℕ → Prop := fun z =>
    ∃ s, z.unpair.2 ≤ s ∧ g z.unpair.1 s ≠ g z.unpair.1 z.unpair.2 with hPdef
  have hPre : REPred P := by
    refine rePred_of_exists_test_comp
      (fun z s => decide (z.unpair.2 ≤ s) && (g z.unpair.1 s != g z.unpair.1 z.unpair.2)) ?_ ?_
    · have hle : Computable fun p : ℕ × ℕ => decide (p.1.unpair.2 ≤ p.2) := by
        have hpred : PrimrecPred fun p : ℕ × ℕ => p.1.unpair.2 ≤ p.2 :=
          Primrec.nat_le.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)) Primrec.snd
        exact (primrec_decide_pred hpred).to_comp
      have hg₁ : Computable fun p : ℕ × ℕ => g p.1.unpair.1 p.2 :=
        hg.comp (Primrec.to_comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
          Computable.snd
      have hg₂ : Computable fun p : ℕ × ℕ => g p.1.unpair.1 p.1.unpair.2 :=
        hg.comp (Primrec.to_comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
          (Primrec.to_comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))
      exact ((Primrec.dom_bool₂ (· && ·)).to_comp.comp hle
        ((Primrec.dom_bool₂ (· != ·)).to_comp.comp hg₁ hg₂))
    · intro z
      simp only [hPdef, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
  obtain ⟨k, hk, hspec⟩ := exists_index_repred hPre
  have hkP : ∀ z, haltingOracle (k z) = true ↔ P z := by
    intro z
    rw [haltingOracle_eq, jumpChar_eq_true_iff]
    exact (hspec emptyOracle z).symm
  -- the oracle, asked at the reduction
  have hor : RecursiveIn {oracleFun haltingOracle} (oracleFun haltingOracle) :=
    RecursiveIn.oracle _ (by simp)
  have hkfun : RecursiveIn {oracleFun haltingOracle} (fun z => (k z : Part ℕ)) :=
    RecursiveIn.iff_nat.mpr (Nat.Partrec.recursiveIn (Partrec.nat_iff.1 hk.partrec))
  have hq : RecursiveIn {oracleFun haltingOracle}
      (fun z => Part.some (if haltingOracle (k z) then 1 else 0)) := by
    have h := recIn_comp hor hkfun
    refine recursiveIn_of_eq h fun z => ?_
    have hb : ((k z : ℕ) : Part ℕ) >>= oracleFun haltingOracle
        = oracleFun haltingOracle (k z) := Part.bind_some _ _
    rw [hb]
    rfl
  -- search for the least stage after which the guess never changes
  have hr := recIn_rfind hq
  -- read off the guess at that stage
  have hgval : RecursiveIn {oracleFun haltingOracle}
      (fun w : ℕ => Part.some (if g w.unpair.1 w.unpair.2 then 1 else 0)) := by
    refine recursiveIn_of_partrec (Partrec.nat_iff.1 ?_)
    have : Computable fun w : ℕ => (if g w.unpair.1 w.unpair.2 then 1 else 0 : ℕ) := by
      have hgw : Computable fun w : ℕ => g w.unpair.1 w.unpair.2 :=
        hg.comp (Primrec.to_comp (Primrec.fst.comp Primrec.unpair))
          (Primrec.to_comp (Primrec.snd.comp Primrec.unpair))
      refine (Computable.cond hgw (Computable.const 1) (Computable.const 0)).of_eq fun w => ?_
      cases hw : g w.unpair.1 w.unpair.2 <;> simp
    exact this.partrec
  have hbind := recursiveIn_bindPair hgval hr
  refine recursiveIn_of_eq hbind fun x => ?_
  -- the search converges to the first stage at which the guess has settled
  have hsettle : ∃ t, ¬ P (Nat.pair x t) := by
    obtain ⟨s₀, hs₀⟩ := hlim x
    refine ⟨s₀, ?_⟩
    rintro ⟨s, hs, hne⟩
    simp only [Nat.unpair_pair] at hs hne
    exact hne ((hs₀ s hs).trans (hs₀ s₀ le_rfl).symm)
  classical
  set t₀ := Nat.find hsettle with ht₀def
  have ht₀ : ¬ P (Nat.pair x t₀) := Nat.find_spec hsettle
  have hmin : ∀ m < t₀, P (Nat.pair x m) := by
    intro m hm
    by_contra hcon
    exact absurd hm (not_lt.2 (Nat.find_le hcon))
  have hgt₀ : g x t₀ = A x := by
    obtain ⟨s₀, hs₀⟩ := hlim x
    have hkey : g x (max t₀ s₀) = g x t₀ := by
      by_contra hne
      exact ht₀ ⟨max t₀ s₀, by simp, by simp [hne]⟩
    rw [← hkey]
    exact hs₀ _ (le_max_right _ _)
  -- the value of the reduction at `x`
  have hmemr : t₀ ∈ (fun a => Nat.rfind fun n => (fun m => decide (m = 0)) <$>
      (fun z => Part.some (if haltingOracle (k z) then 1 else 0)) (Nat.pair a n)) x := by
    refine mem_rfind_iff.2 ⟨?_, ?_⟩
    · have : haltingOracle (k (Nat.pair x t₀)) = false := by
        rcases Bool.eq_false_or_eq_true (haltingOracle (k (Nat.pair x t₀))) with h' | h'
        · exact absurd ((hkP _).1 h') ht₀
        · exact h'
      simp [this]
    · intro m hm
      have : haltingOracle (k (Nat.pair x m)) = true := (hkP _).2 (hmin m hm)
      exact ⟨1, by simp [this], one_ne_zero⟩
  have hrhs : oracleFun A x = Part.some (if A x then 1 else 0) := rfl
  rw [hrhs]
  refine Part.eq_some_iff.2 (Part.mem_bind_iff.2 ⟨t₀, hmemr, ?_⟩)
  simp [hgt₀]

/-- **Shoenfield's limit lemma.** -/
theorem limitComputable_iff_turingReducible_haltingOracle (A : ℕ → Bool) :
    LimitComputable A ↔ oracleFun A ≤ᵀ oracleFun haltingOracle :=
  ⟨turingReducible_of_limitComputable, limitComputable_of_turingReducible⟩

/-! ## Two consequences -/

/-- Every recursively enumerable set is limit computable. -/
theorem limitComputable_of_repred {P : ℕ → Prop} (hP : REPred P) :
    LimitComputable (charOracle P) :=
  limitComputable_of_turingReducible (turingReducible_haltingOracle_of_repred hP)

/-- The second jump `∅''` is not limit computable. -/
theorem not_limitComputable_jumpChar_haltingOracle :
    ¬ LimitComputable (jumpChar haltingOracle) := by
  intro h
  exact not_turingReducible_jumpChar haltingOracle
    ((limitComputable_iff_turingReducible_haltingOracle _).1 h)

end Oracle
end Lambda
