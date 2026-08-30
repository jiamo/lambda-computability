/-
**Post's problem for many-one reducibility.**

`Start/PostSimple.lean` builds Post's simple set: an r.e. set whose complement is infinite but
meets every infinite r.e. set.  This module shows that such a set cannot be many-one complete,
which answers Post's question for many-one degrees: *there is a recursively enumerable set which
is neither computable nor many-one complete.*

The argument is the classical one.

* `Lambda.Post.Productive` — a set is **productive** when a computable function produces, from any
  index of an r.e. subset of it, an element outside that subset but inside the set;
* `Lambda.Post.productive_compl_haltK` — the complement of the halting set is productive, with the
  identity as production function;
* `Lambda.Post.Productive.of_manyOneReducible` — productivity of a complement travels along a
  many-one reduction, using the s-m-n theorem to name the preimage of an r.e. set;
* `Lambda.Post.exists_infinite_re_subset` — **a productive set contains an infinite r.e. set**:
  iterate the production function, adding each new element to the r.e. set produced so far;
* `Lambda.Post.not_manyOneReducible_haltK_simpleSet` — hence the halting set does not reduce to
  Post's set, so `Lambda.Post.simpleSet_not_manyOneComplete`;
* `Lambda.Post.exists_rePred_not_computable_not_manyOneComplete` — **Post's problem for many-one
  reducibility**, solved.

The auxiliary results about the standard numbering that the argument needs — an index for the
empty set, an index for a set with one more element, and an index for the preimage of an r.e. set
under a computable function — are collected first; each is an instance of the s-m-n theorem in the
form of `Nat.Partrec.Code.curry`.
-/

import Start.PostSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

namespace Post

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### Naming r.e. sets: the s-m-n theorem -/

/-- A predicate is r.e. as soon as it is "some stage of a computable test succeeds". -/
theorem rePred_of_exists_comp {P : ℕ → Prop} (g : ℕ → ℕ → Bool) (hg : Computable₂ g)
    (h : ∀ x, P x ↔ ∃ k, g x k = Bool.true) : REPred P := by
  have hr : Partrec fun x : ℕ => Nat.rfind fun k => Part.some (g x k) := Partrec.rfind hg.partrec
  refine hr.dom_re.of_eq fun x => ?_
  rw [h x]
  constructor
  · intro hdom
    obtain ⟨k, hk, -⟩ := Nat.rfind_dom.1 hdom
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact Nat.rfind_dom.2 ⟨k, by simp [hk], fun {_} _ => trivial⟩

/-- **The s-m-n theorem in the form used below**: a partial recursive function of two arguments
has a computable indexing of its sections. -/
theorem exists_index_fun (F : ℕ → ℕ →. ℕ) (hF : Partrec₂ F) :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ n x, (Wset (h n) x ↔ (F n x).Dom) := by
  have hG : Nat.Partrec fun q : ℕ => F (Nat.unpair q).1 (Nat.unpair q).2 :=
    Partrec.nat_iff.1 (hF.comp (Computable.fst.comp Primrec.unpair.to_comp)
      (Computable.snd.comp Primrec.unpair.to_comp))
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hG
  refine ⟨fun n => Encodable.encode (Code.curry c n),
    (Primrec.encode.comp (Nat.Partrec.Code.primrec₂_curry.comp
      (Primrec.const c) Primrec.id)).to_comp, fun n x => ?_⟩
  simp only [Wset, Denumerable.ofNat_encode, Code.eval_curry, hc]
  simp

/-- An index for the empty set. -/
theorem exists_empty_index : ∃ e : ℕ, ∀ x, ¬ Wset e x := by
  obtain ⟨h, -, hspec⟩ := exists_index_fun (fun _ _ => Part.none) Partrec.none
  exact ⟨h 0, fun x hx => by simpa using (hspec 0 x).1 hx⟩

/-- A computable function naming, from an index `e` and a number `a`, the r.e. set `W e ∪ {a}`. -/
theorem exists_adjoin :
    ∃ adj : ℕ → ℕ → ℕ, Computable₂ adj ∧
      ∀ e a x, (Wset (adj e a) x ↔ (x = a ∨ Wset e x)) := by
  have hcond : Computable fun q : ℕ × ℕ => decide (q.2 = (Nat.unpair q.1).2) :=
    (primrec_decide (Primrec.eq.comp Primrec.snd
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)))).to_comp
  have hbr : Partrec₂ fun p x : ℕ => Code.eval (ofNat Code (Nat.unpair p).1) x :=
    Code.eval_part.comp
      ((Primrec.ofNat Code).comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).to_comp
      Computable.snd
  have hF : Partrec₂ fun p x : ℕ =>
      bif decide (x = (Nat.unpair p).2) then Part.some 0
      else Code.eval (ofNat Code (Nat.unpair p).1) x :=
    Partrec.cond hcond (Partrec.const' (Part.some 0)) hbr
  obtain ⟨h, hcomp, hspec⟩ := exists_index_fun _ hF
  refine ⟨fun e a => h (Nat.pair e a), hcomp.comp (Primrec₂.natPair.to_comp), fun e a x => ?_⟩
  rw [hspec (Nat.pair e a) x]
  by_cases hx : x = a
  · simp [hx, Wset]
  · simp [hx, Wset]

/-- A computable function naming the preimage of an r.e. set under a computable function. -/
theorem exists_preimage_index {g : ℕ → ℕ} (hg : Computable g) :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ e x, (Wset (h e) x ↔ Wset e (g x)) := by
  have hF : Partrec₂ fun e x : ℕ => Code.eval (ofNat Code e) (g x) :=
    Code.eval_part.comp ((Primrec.ofNat Code).comp Primrec.fst).to_comp (hg.comp Computable.snd)
  obtain ⟨h, hcomp, hspec⟩ := exists_index_fun _ hF
  exact ⟨h, hcomp, fun e x => hspec e x⟩

/-! ### Productive sets -/

/-- A set is **productive** when there is a computable function which, given an index of an r.e.
subset of the set, produces an element of the set outside that subset. -/
def Productive (P : ℕ → Prop) : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, (∀ x, Wset e x → P x) → P (f e) ∧ ¬ Wset e (f e)

/-- **The complement of the halting set is productive**, with the identity as production
function. -/
theorem productive_compl_haltK : Productive fun n => ¬ HaltK n := by
  refine ⟨id, Computable.id, fun e he => ?_⟩
  have hWK : Wset e e ↔ HaltK e := Iff.rfl
  have hne : ¬ Wset e e := by
    intro hEe
    exact (he e hEe) (hWK.1 hEe)
  exact ⟨fun hK => hne (hWK.2 hK), hne⟩

/-- **Productivity of a complement travels along a many-one reduction.** -/
theorem Productive.of_manyOneReducible {p q : ℕ → Prop} (hred : p ≤₀ q)
    (hp : Productive fun x => ¬ p x) : Productive fun x => ¬ q x := by
  obtain ⟨g, hg, hgspec⟩ := hred
  obtain ⟨f, hf, hfspec⟩ := hp
  obtain ⟨h, hh, hhspec⟩ := exists_preimage_index hg
  refine ⟨fun e => g (f (h e)), hg.comp (hf.comp hh), fun e he => ?_⟩
  have hsub : ∀ x, Wset (h e) x → ¬ p x := by
    intro x hx
    have : Wset e (g x) := (hhspec e x).1 hx
    exact fun hpx => he _ this ((hgspec x).1 hpx)
  obtain ⟨hmem, hout⟩ := hfspec (h e) hsub
  refine ⟨fun hq => hmem ((hgspec _).2 hq), fun hW => hout ((hhspec e _).2 hW)⟩

/-! ### A productive set contains an infinite r.e. set -/

/-- **A productive set contains an infinite recursively enumerable subset**: iterating the
production function on the index of the set built so far produces new elements for ever. -/
theorem exists_infinite_re_subset {P : ℕ → Prop} (hP : Productive P) :
    ∃ p : ℕ → Prop, REPred p ∧ {x : ℕ | p x}.Infinite ∧ ∀ x, p x → P x := by
  obtain ⟨f, hf, hfspec⟩ := hP
  obtain ⟨e₀, he₀⟩ := exists_empty_index
  obtain ⟨adj, hadjC, hadj⟩ := exists_adjoin
  -- the sequence of indices, each naming the finite set of elements produced so far
  set E : ℕ → ℕ := fun n => Nat.rec e₀ (fun _ IH => adj IH (f IH)) n with hE
  have hEcomp : Computable E := by
    have hstep : Computable₂ fun (_ : ℕ) (p : ℕ × ℕ) => adj p.2 (f p.2) :=
      hadjC.comp (Computable.snd.comp Computable.snd)
        (hf.comp (Computable.snd.comp Computable.snd))
    simpa [hE] using
      (Computable.nat_rec (f := fun n : ℕ => n) (g := fun _ : ℕ => e₀)
        Computable.id (Computable.const e₀) hstep)
  set a : ℕ → ℕ := fun n => f (E n) with ha
  have hacomp : Computable a := hf.comp hEcomp
  -- the invariant
  have key : ∀ n, (∀ x, Wset (E n) x ↔ ∃ j < n, x = a j) ∧ ∀ j < n, P (a j) := by
    intro n
    induction n with
    | zero =>
        refine ⟨fun x => ⟨fun hx => absurd hx (he₀ x), ?_⟩, fun j hj => absurd hj (by omega)⟩
        rintro ⟨j, hj, -⟩
        omega
    | succ n ih =>
        obtain ⟨hmem, hin⟩ := ih
        have hsub : ∀ x, Wset (E n) x → P x := by
          intro x hx
          obtain ⟨j, hj, rfl⟩ := (hmem x).1 hx
          exact hin j hj
        obtain ⟨hPa, -⟩ := hfspec (E n) hsub
        refine ⟨fun x => ?_, fun j hj => ?_⟩
        · have hstep : E (n + 1) = adj (E n) (a n) := rfl
          rw [hstep, hadj]
          constructor
          · rintro (rfl | hx)
            · exact ⟨n, by omega, rfl⟩
            · obtain ⟨j, hj, rfl⟩ := (hmem x).1 hx
              exact ⟨j, by omega, rfl⟩
          · rintro ⟨j, hj, rfl⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
            · exact Or.inr ((hmem _).2 ⟨j, hj', rfl⟩)
            · exact Or.inl rfl
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
          · exact hin j hj'
          · exact hPa
  have hmemP : ∀ n, P (a n) := fun n => (key (n + 1)).2 n (by omega)
  -- the produced elements are pairwise distinct
  have hnew : ∀ n, ¬ Wset (E n) (a n) := by
    intro n
    have hsub : ∀ x, Wset (E n) x → P x := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := ((key n).1 x).1 hx
      exact (key n).2 j hj
    exact (hfspec (E n) hsub).2
  have hinj : Function.Injective a := by
    have hlt : ∀ {j n : ℕ}, j < n → a j ≠ a n := by
      intro j n hj hEq
      exact hnew n (hEq ▸ ((key n).1 (a j)).2 ⟨j, hj, rfl⟩)
    intro m n hmn
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd hmn (hlt h)
    · exact h
    · exact absurd hmn.symm (hlt h)
  refine ⟨fun x => ∃ n, a n = x, ?_, ?_, ?_⟩
  · refine rePred_of_exists_comp (fun x n => decide (a n = x)) ?_ (fun x => by simp)
    exact ((primrec_decide (Primrec.eq (α := ℕ))).to_comp).comp
      ((hacomp.comp Computable.snd).pair Computable.fst)
  · have : {x : ℕ | ∃ n, a n = x} = Set.range a := by ext x; simp [Set.mem_range, eq_comm]
    rw [this]
    exact Set.infinite_range_of_injective hinj
  · rintro x ⟨n, rfl⟩
    exact hmemP n

/-! ### Post's problem for many-one reducibility -/

/-- **The halting set does not reduce to a simple set.** -/
theorem Simple.not_manyOneReducible_haltK {S : ℕ → Prop} (hS : Simple S) : ¬ (HaltK ≤₀ S) := by
  intro hred
  have hprod : Productive fun x => ¬ S x :=
    Productive.of_manyOneReducible hred productive_compl_haltK
  obtain ⟨p, hre, hinf, hsub⟩ := exists_infinite_re_subset hprod
  obtain ⟨x, hx, hxs⟩ := hS.2.2 p hre hinf
  exact hxs (hsub x hx)

/-- **A simple set is not many-one complete**, so it is neither computable
(`Lambda.Post.Simple.not_computablePred`) nor complete. -/
theorem Simple.not_manyOneComplete {S : ℕ → Prop} (hS : Simple S) :
    ¬ ∀ p : ℕ → Prop, REPred p → p ≤₀ S := fun h =>
  hS.not_manyOneReducible_haltK (h HaltK rePred_haltK)

/-- **The halting set does not reduce to Post's simple set.** -/
theorem not_manyOneReducible_haltK_simpleSet : ¬ (HaltK ≤₀ simpleSet) :=
  simple_simpleSet.not_manyOneReducible_haltK

/-- **Post's simple set is not many-one complete.** -/
theorem simpleSet_not_manyOneComplete : ¬ ∀ p : ℕ → Prop, REPred p → p ≤₀ simpleSet :=
  simple_simpleSet.not_manyOneComplete

/-- **Post's problem, for many-one reducibility**: there is a recursively enumerable set which is
neither computable nor many-one complete. -/
theorem exists_rePred_not_computable_not_manyOneComplete :
    ∃ p : ℕ → Prop, REPred p ∧ ¬ ComputablePred p ∧ ¬ ∀ q : ℕ → Prop, REPred q → q ≤₀ p :=
  ⟨simpleSet, rePred_simpleSet, not_computablePred_simpleSet, simpleSet_not_manyOneComplete⟩

end Post

end Lambda
