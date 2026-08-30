/-
**Post's simple set.**

`Start/KleeneK.lean` shows that the halting set `K` is one-one complete: every recursively
enumerable set reduces to it.  Post asked whether every r.e. set that is not computable is
complete in this sense, and answered the many-one form of his own question by constructing a
*simple* set: an r.e. set whose complement is infinite but contains no infinite r.e. set.

This module carries out that construction, with mathlib's numbering of the partial recursive
functions (`Nat.Partrec.Code`).

* `Lambda.Post.Wset e` — the `e`-th r.e. set, the domain of the `e`-th partial recursive function,
  and `Lambda.Post.exists_index` — every r.e. predicate occurs in the numbering;
* `Lambda.Post.simpleSet` — **Post's set**: for each index `e`, run the `e`-th machine on all
  inputs in parallel and keep the *first* input it accepts among those exceeding `2 * e`;
* `Lambda.Post.rePred_simpleSet` — it is r.e.;
* `Lambda.Post.card_filter_simpleSet_le` — at most `n` of the numbers below `2 * n` belong to it,
  since only the indices `e < n` can contribute there and each contributes at most one number;
  hence `Lambda.Post.simpleSet_compl_infinite` — its complement is infinite;
* `Lambda.Post.simpleSet_meets` — it meets every infinite r.e. set, i.e. its complement is
  **immune**;
* `Lambda.Post.not_rePred_compl_simpleSet`, `Lambda.Post.not_computablePred_simpleSet` — hence its
  complement is not r.e. and it is not computable, and `Lambda.Post.simpleSet_infinite` — it is
  itself infinite.

`Start/PostIncomplete.lean` uses this to solve Post's problem for many-one reducibility: the set
is not many-one complete, so it is an r.e. set that is neither computable nor complete.
-/

import Start.KleeneK

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

namespace Post

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### Two auxiliary facts about primitive recursion -/

/-- A decidable predicate that is primitive recursive as a predicate is primitive recursive as a
`Bool`-valued function, for whichever decision procedure is at hand. -/
theorem primrec_decide {α : Type} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (h : PrimrecPred p) : Primrec fun a => decide (p a) := by
  obtain ⟨_, h'⟩ := h
  exact h'.of_eq fun a => by congr 1

/-- The conjunction of two primitive recursive `Bool`-valued functions. -/
theorem primrec_band {α : Type} [Primcodable α] {f g : α → Bool} (hf : Primrec f)
    (hg : Primrec g) : Primrec fun n => f n && g n :=
  (Primrec.dom_bool₂ (fun a b => a && b)).comp hf hg

/-- A predicate is r.e. as soon as it is "some stage of a primitive recursive test succeeds". -/
theorem rePred_of_exists_test {α : Type} [Primcodable α] {P : α → Prop} (g : α → ℕ → Bool)
    (hg : Primrec₂ g) (h : ∀ x, P x ↔ ∃ k, g x k = Bool.true) : REPred P := by
  have hr : Partrec fun x : α => Nat.rfind fun k => Part.some (g x k) :=
    Partrec.rfind (Primrec₂.to_comp hg).partrec
  refine hr.dom_re.of_eq fun x => ?_
  rw [h x]
  constructor
  · intro hdom
    obtain ⟨k, hk, -⟩ := Nat.rfind_dom.1 hdom
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact Nat.rfind_dom.2 ⟨k, by simp [hk], fun {_} _ => trivial⟩

/-! ### The standard numbering of the r.e. sets -/

/-- The `e`-th recursively enumerable set: the domain of the `e`-th partial recursive
function. -/
def Wset (e : ℕ) (x : ℕ) : Prop := (Code.eval (ofNat Code e) x).Dom

/-- Every r.e. predicate occurs in the numbering. -/
theorem exists_index {p : ℕ → Prop} (hp : REPred p) : ∃ e, ∀ x, p x ↔ Wset e x := by
  obtain ⟨f, hf, hdom⟩ := exists_partrec_dom_iff hp
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  refine ⟨Encodable.encode c, fun x => ?_⟩
  have hW : Wset (Encodable.encode c) x ↔ (f x).Dom := by
    simp [Wset, Denumerable.ofNat_encode, hc]
  exact (hdom x).symm.trans hW.symm

theorem rePred_Wset (e : ℕ) : REPred (Wset e) :=
  (Code.eval_part.comp (Computable.const _) Computable.id).dom_re

/-- The converse of `Lambda.Post.rePred_of_exists_test`: every r.e. predicate is of the form
"some stage of a primitive recursive test succeeds". -/
theorem exists_test_of_rePred {P : ℕ → Prop} (hP : REPred P) :
    ∃ g : ℕ → ℕ → Bool, Primrec₂ g ∧ ∀ x, P x ↔ ∃ k, g x k = Bool.true := by
  obtain ⟨e, he⟩ := exists_index hP
  refine ⟨fun x k => (Code.evaln k (ofNat Code e) x).isSome, ?_, fun x => ?_⟩
  · have hev : Primrec fun p : ℕ × ℕ => Code.evaln p.2 (ofNat Code e) p.1 :=
      Nat.Partrec.Code.primrec_evaln.comp
        ((Primrec.snd.pair (Primrec.const (ofNat Code e))).pair Primrec.fst)
    exact Primrec.option_isSome.comp hev
  · rw [he x, Wset]
    constructor
    · intro h
      obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 h
      obtain ⟨k, hk⟩ := Code.evaln_complete.1 hy
      exact ⟨k, by simp [Option.mem_def.1 hk]⟩
    · rintro ⟨k, hk⟩
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hk
      exact Part.dom_iff_mem.2 ⟨y, Code.evaln_sound (Option.mem_def.2 hy)⟩

/-! ### The construction -/

/-- The test run at stage `s`: the `e`-th machine accepts the input `x` within `s` steps, and `x`
is large enough, `2 * e < x`. -/
def found (e s x : ℕ) : Bool :=
  decide (2 * e < x) && (Code.evaln s (ofNat Code e) x).isSome

/-- The search is over a single number `k`, coding the pair (stage, input). -/
def test (e k : ℕ) : Bool := found e (Nat.unpair k).1 (Nat.unpair k).2

/-- No `j < k` passes the test. -/
def noneBelow (e : ℕ) : ℕ → Bool
  | 0 => Bool.true
  | k + 1 => noneBelow e k && !test e k

theorem noneBelow_spec (e k : ℕ) :
    noneBelow e k = Bool.true ↔ ∀ j < k, test e j = Bool.false := by
  induction k with
  | zero => simp [noneBelow]
  | succ k ih =>
      simp only [noneBelow, Bool.and_eq_true, Bool.not_eq_true', ih]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h1 j hj
        · exact h2
      · intro h
        exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h k (Nat.lt_succ_self k)⟩

/-- `k` is the *first* pair (stage, input) at which the `e`-th machine yields a witness. -/
def hit (e k : ℕ) : Bool := test e k && noneBelow e k

theorem hit_unique {e k k' : ℕ} (h : hit e k = Bool.true) (h' : hit e k' = Bool.true) : k = k' := by
  simp only [hit, Bool.and_eq_true] at h h'
  rcases Nat.lt_trichotomy k k' with hlt | heq | hgt
  · exact absurd h.1 (by simp [(noneBelow_spec e k').1 h'.2 k hlt])
  · exact heq
  · exact absurd h'.1 (by simp [(noneBelow_spec e k).1 h.2 k' hgt])

/-- If the test succeeds at all, it succeeds first at a unique place. -/
theorem exists_hit {e : ℕ} (h : ∃ k, test e k = Bool.true) : ∃ k, hit e k = Bool.true := by
  classical
  refine ⟨Nat.find h, ?_⟩
  simp only [hit, Bool.and_eq_true]
  refine ⟨Nat.find_spec h, (noneBelow_spec e _).2 fun j hj => ?_⟩
  simpa using Nat.find_min h hj

/-- **Post's simple set**: the numbers that are the first witness found for some index. -/
def simpleSet (x : ℕ) : Prop := ∃ e k, hit e k = Bool.true ∧ (Nat.unpair k).2 = x

/-! ### The search is primitive recursive, so the set is r.e. -/

theorem primrec_found : Primrec fun p : ℕ × ℕ × ℕ => found p.1 p.2.1 p.2.2 := by
  have hcode : Primrec fun p : ℕ × ℕ × ℕ => ofNat Code p.1 :=
    (Primrec.ofNat Code).comp Primrec.fst
  have hev : Primrec fun p : ℕ × ℕ × ℕ => Code.evaln p.2.1 (ofNat Code p.1) p.2.2 :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.snd).pair hcode).pair (Primrec.snd.comp Primrec.snd))
  exact primrec_band
    (primrec_decide (Primrec.nat_lt.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      (Primrec.snd.comp Primrec.snd)))
    (Primrec.option_isSome.comp hev)

theorem primrec_test : Primrec₂ test :=
  primrec_found.comp (Primrec.fst.pair
    ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))

theorem primrec_noneBelow : Primrec₂ noneBelow := by
  have h : Primrec₂ fun (e : ℕ) (p : ℕ × Bool) => p.2 && !test e p.1 :=
    primrec_band (Primrec.snd.comp Primrec.snd)
      (Primrec.not.comp (primrec_test.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
  exact (Primrec.nat_rec (Primrec.const Bool.true) h).of_eq (by
    intro e k
    induction k with
    | zero => rfl
    | succ k ih => simp [noneBelow, ih])

theorem primrec_hit : Primrec₂ hit := primrec_band primrec_test primrec_noneBelow

/-- Membership in the simple set is a single unbounded search. -/
theorem simpleSet_iff (x : ℕ) :
    simpleSet x ↔ ∃ p : ℕ,
      (hit (Nat.unpair p).1 (Nat.unpair p).2 &&
        decide ((Nat.unpair (Nat.unpair p).2).2 = x)) = Bool.true := by
  constructor
  · rintro ⟨e, k, hk, hx⟩
    exact ⟨Nat.pair e k, by simp [hk, hx]⟩
  · rintro ⟨p, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨(Nat.unpair p).1, (Nat.unpair p).2, hp.1, hp.2⟩

/-- **Post's set is recursively enumerable.** -/
theorem rePred_simpleSet : REPred simpleSet := by
  refine rePred_of_exists_test
    (fun x p => hit (Nat.unpair p).1 (Nat.unpair p).2 &&
      decide ((Nat.unpair (Nat.unpair p).2).2 = x)) ?_ simpleSet_iff
  have h1 : Primrec fun q : ℕ × ℕ => hit (Nat.unpair q.2).1 (Nat.unpair q.2).2 :=
    primrec_hit.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have h2 : Primrec fun q : ℕ × ℕ => decide ((Nat.unpair (Nat.unpair q.2).2).2 = q.1) :=
    primrec_decide (Primrec.eq.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
      Primrec.fst)
  exact primrec_band h1 h2

/-! ### The complement is infinite -/

/-- Each index contributes at most one number to the set: the input part of the first pair at
which its test succeeds. -/
noncomputable def wit (e : ℕ) : ℕ :=
  open Classical in
  if h : ∃ k, hit e k = Bool.true then (Nat.unpair (Exists.choose h)).2 else 0

theorem wit_eq {e k : ℕ} (hk : hit e k = Bool.true) : wit e = (Nat.unpair k).2 := by
  have hex : ∃ k, hit e k = Bool.true := ⟨k, hk⟩
  rw [wit, dif_pos hex]
  exact congrArg (fun j => (Nat.unpair j).2) (hit_unique (Exists.choose_spec hex) hk)

/-- An element of the set that is smaller than `2 * n` comes from an index smaller than `n`. -/
theorem index_lt_of_mem {e k : ℕ} (hk : hit e k = Bool.true) {n : ℕ}
    (hlt : (Nat.unpair k).2 < 2 * n) : e < n := by
  have h : test e k = Bool.true := (Bool.and_eq_true _ _ ▸ hk).1
  have h2 : 2 * e < (Nat.unpair k).2 := by
    have := (Bool.and_eq_true _ _ ▸ h).1
    simpa [found, test] using this
  omega

open scoped Classical in
theorem card_filter_simpleSet_le (n : ℕ) :
    ((Finset.range (2 * n)).filter (fun x => simpleSet x)).card ≤ n := by
  classical
  have hsub : (Finset.range (2 * n)).filter (fun x => simpleSet x) ⊆
      (Finset.range n).image wit := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨e, k, hk, hxk⟩ := hx.2
    refine Finset.mem_image.2 ⟨e, Finset.mem_range.2 ?_, ?_⟩
    · exact index_lt_of_mem hk (by rw [hxk]; exact hx.1)
    · rw [wit_eq hk, hxk]
  calc ((Finset.range (2 * n)).filter (fun x => simpleSet x)).card
      ≤ ((Finset.range n).image wit).card := Finset.card_le_card hsub
    _ ≤ (Finset.range n).card := Finset.card_image_le
    _ = n := Finset.card_range n

/-- **The complement of Post's set is infinite.** -/
theorem simpleSet_compl_infinite : {x : ℕ | ¬ simpleSet x}.Infinite := by
  classical
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  -- every element of the complement is at most `N`, so all numbers in `(N, 2 * n)` are in the set
  have key : ∀ n : ℕ, 2 * n ≤ N + 1 + n := by
    intro n
    have hsub : (Finset.range (2 * n)).filter (fun x => ¬ simpleSet x) ⊆ Finset.range (N + 1) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      exact Finset.mem_range.2 (Nat.lt_succ_of_le (hN hx.2))
    have hcard : ((Finset.range (2 * n)).filter (fun x => ¬ simpleSet x)).card ≤ N + 1 :=
      (Finset.card_le_card hsub).trans_eq (Finset.card_range (N + 1))
    have := Finset.card_filter_add_card_filter_not
      (s := Finset.range (2 * n)) (p := fun x => simpleSet x)
    have hsum : ((Finset.range (2 * n)).filter (fun x => simpleSet x)).card +
        ((Finset.range (2 * n)).filter (fun x => ¬ simpleSet x)).card = 2 * n := by
      simpa [Finset.card_range] using this
    have h1 := card_filter_simpleSet_le n
    omega
  exact absurd (key (N + 2)) (by omega)

/-! ### The set meets every infinite r.e. set -/

theorem mem_Wset_of_found {e s x : ℕ} (h : found e s x = Bool.true) : Wset e x := by
  have hs : (Code.evaln s (ofNat Code e) x).isSome = Bool.true :=
    (Bool.and_eq_true _ _ ▸ h).2
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hs
  exact Part.dom_iff_mem.2 ⟨y, Code.evaln_sound (by rw [hy]; rfl)⟩

theorem simpleSet_of_hit {e k : ℕ} (hk : hit e k = Bool.true) : simpleSet (Nat.unpair k).2 :=
  ⟨e, k, hk, rfl⟩

/-- **Post's set meets every infinite r.e. set**: its complement is immune. -/
theorem simpleSet_meets {e : ℕ} (h : {x : ℕ | Wset e x}.Infinite) :
    ∃ x, Wset e x ∧ simpleSet x := by
  obtain ⟨x, hxW, hx⟩ := h.exists_gt (2 * e)
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.1 hxW
  obtain ⟨s, hs⟩ := Code.evaln_complete.1 hy
  have htest : test e (Nat.pair s x) = Bool.true := by
    simp only [test, Nat.unpair_pair, found, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hx, Option.isSome_iff_exists.2 ⟨y, hs⟩⟩
  obtain ⟨k, hk⟩ := exists_hit ⟨_, htest⟩
  have htest' : test e k = Bool.true := (Bool.and_eq_true _ _ ▸ hk).1
  exact ⟨(Nat.unpair k).2, mem_Wset_of_found htest', simpleSet_of_hit hk⟩

/-- Every infinite r.e. set meets Post's set. -/
theorem simpleSet_meets_rePred {p : ℕ → Prop} (hp : REPred p) (hinf : {x : ℕ | p x}.Infinite) :
    ∃ x, p x ∧ simpleSet x := by
  obtain ⟨e, he⟩ := exists_index hp
  have : {x : ℕ | Wset e x}.Infinite := by
    refine hinf.mono ?_
    intro x hx
    exact (he x).1 hx
  obtain ⟨x, hx, hxs⟩ := simpleSet_meets this
  exact ⟨x, (he x).2 hx, hxs⟩

/-! ### Immune and simple sets -/

/-- A set is **immune** when it is infinite and contains no infinite r.e. subset: every infinite
r.e. set has an element outside it. -/
def Immune (P : ℕ → Prop) : Prop :=
  {x : ℕ | P x}.Infinite ∧
    ∀ p : ℕ → Prop, REPred p → {x : ℕ | p x}.Infinite → ∃ x, p x ∧ ¬ P x

/-- A set is **simple** when it is r.e. and its complement is immune. -/
def Simple (S : ℕ → Prop) : Prop := REPred S ∧ Immune fun x => ¬ S x

/-- **Post's set is simple.** -/
theorem simple_simpleSet : Simple simpleSet :=
  ⟨rePred_simpleSet, simpleSet_compl_infinite, fun p hp hinf => by
    obtain ⟨x, hx, hxs⟩ := simpleSet_meets_rePred hp hinf
    exact ⟨x, hx, not_not_intro hxs⟩⟩

/-- **A simple set is not computable**: its complement is infinite and r.e. sets cannot exhaust
it. -/
theorem Simple.not_computablePred {S : ℕ → Prop} (hS : Simple S) : ¬ ComputablePred S := by
  classical
  intro hcomp
  obtain ⟨x, hx, hxs⟩ :=
    hS.2.2 (fun x => ¬ S x) (ComputablePred.computable_iff_re_compl_re.1 hcomp).2 hS.2.1
  exact hxs hx

/-! ### Consequences -/

/-- **The complement of Post's set is not r.e.** -/
theorem not_rePred_compl_simpleSet : ¬ REPred fun x => ¬ simpleSet x := by
  intro h
  obtain ⟨x, hx, hxs⟩ := simpleSet_meets_rePred h simpleSet_compl_infinite
  exact hx hxs

/-- **Post's set is not computable.** -/
theorem not_computablePred_simpleSet : ¬ ComputablePred simpleSet := by
  classical
  intro h
  exact not_rePred_compl_simpleSet (ComputablePred.computable_iff_re_compl_re.1 h).2

/-- **Post's set is infinite**: otherwise its complement would contain an infinite computable
set, which it meets. -/
theorem simpleSet_infinite : {x : ℕ | simpleSet x}.Infinite := by
  intro hfin
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have hre : REPred fun x : ℕ => N < x := by
    have hc : ComputablePred fun x : ℕ => N < x :=
      ⟨inferInstance, (primrec_decide
        (Primrec.nat_lt.comp (Primrec.const N) Primrec.id)).to_comp⟩
    exact hc.to_re
  have hinf : {x : ℕ | N < x}.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨M, hM⟩
    have hmem : max N M + 1 ∈ {x : ℕ | N < x} := by
      simp only [Set.mem_ofPred_eq]
      omega
    have := hM hmem
    omega
  obtain ⟨x, hx, hxs⟩ := simpleSet_meets_rePred hre hinf
  exact absurd (hN hxs) (by omega)

end Post

end Lambda
