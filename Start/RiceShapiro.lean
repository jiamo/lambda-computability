/-
**The Rice–Shapiro theorem.**

Rice's theorem (proved for the lambda calculus in `Start/Scott.lean`) says that no non-trivial
extensional class of programs is decidable.  Rice–Shapiro is the sharper, positive statement about
the classes that are merely *recursively enumerable*: an r.e. extensional class of r.e. sets is
exactly the class of the sets containing one of a family of finite sets.

* `Lambda.Post.Extensional` — a predicate on indices which only depends on the set named;
* `Lambda.Post.exists_index_of_test` — a uniformly computable family of semi-decision tests names a
  computable family of r.e. sets (from the s-m-n theorem of `Start/PostIncomplete.lean`);
* `Lambda.Post.rePred_extensional_mono` — an r.e. extensional class is **upward closed**;
* `Lambda.Post.rePred_extensional_finite_witness` — a member of an r.e. extensional class has a
  **finite** subset in the class;
* `Lambda.Post.rice_shapiro` — the two together: `A e ↔ ∃ d, W d finite, W d ⊆ W e and A d`;
* `Lambda.Post.not_rePred_emptyIndex`, `Lambda.Post.not_rePred_totalIndex` — two consequences: the
  class of indices of the empty set is not r.e., and neither is the class of indices of the
  everywhere-defined functions.

Both halves are proved the same way: from a failure of the statement one builds a computable
family of r.e. sets whose membership in the class is equivalent to a number *not* being in the
halting set, so the complement of the halting set would be r.e.
-/

import Start.PostCreative

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

namespace Post

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### Stage-by-stage acceptance -/

/-- The `e`-th machine accepts `x` within `s` steps. -/
def acc (e s x : ℕ) : Bool := (Code.evaln s (ofNat Code e) x).isSome

theorem primrec_acc : Primrec fun q : ℕ × ℕ × ℕ => acc q.1 q.2.1 q.2.2 := by
  have hcode : Primrec fun q : ℕ × ℕ × ℕ => ofNat Code q.1 :=
    (Primrec.ofNat Code).comp Primrec.fst
  have hev : Primrec fun q : ℕ × ℕ × ℕ => Code.evaln q.2.1 (ofNat Code q.1) q.2.2 :=
    Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.snd).pair hcode).pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_isSome.comp hev

theorem computable_acc {α : Type} [Primcodable α] {u v w : α → ℕ}
    (hu : Computable u) (hv : Computable v) (hw : Computable w) :
    Computable fun a => acc (u a) (v a) (w a) :=
  primrec_acc.to_comp.comp (hu.pair (hv.pair hw))

theorem acc_mono {e s s' x : ℕ} (hs : s ≤ s') (h : acc e s x = Bool.true) :
    acc e s' x = Bool.true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  exact Option.isSome_iff_exists.2 ⟨v, Code.evaln_mono hs (by simpa using hv)⟩

theorem acc_bound {e s x : ℕ} (h : acc e s x = Bool.true) : x < s := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  exact Code.evaln_bound (by simpa using hv)

theorem Wset_iff_exists_acc (e x : ℕ) : Wset e x ↔ ∃ s, acc e s x = Bool.true := by
  constructor
  · intro hx
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hx
    obtain ⟨s, hs⟩ := Code.evaln_complete.1 hv
    exact ⟨s, Option.isSome_iff_exists.2 ⟨v, by simpa using hs⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    exact Part.dom_iff_mem.2 ⟨v, Code.evaln_sound (by rw [hv]; rfl)⟩

theorem haltK_iff_exists_acc (n : ℕ) : HaltK n ↔ ∃ s, acc n s n = Bool.true :=
  Wset_iff_exists_acc n n

/-! ### Naming a computable family of r.e. sets -/

/-- A uniformly computable family of tests names a computable family of r.e. sets: `h n` is an
index of `{x | ∃ s, g n x s}`. -/
theorem exists_index_of_test (g : ℕ → ℕ → ℕ → Bool)
    (hg : Computable fun q : (ℕ × ℕ) × ℕ => g q.1.1 q.1.2 q.2) :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ n x, (Wset (h n) x ↔ ∃ s, g n x s = Bool.true) := by
  have hF : Partrec₂ fun n x : ℕ => Nat.rfind fun s => Part.some (g n x s) :=
    Partrec.rfind (Computable₂.partrec₂ hg)
  obtain ⟨h, hh, hspec⟩ := exists_index_fun _ hF
  refine ⟨h, hh, fun n x => ?_⟩
  rw [hspec n x]
  constructor
  · intro hdom
    obtain ⟨s, hs, -⟩ := Nat.rfind_dom.1 hdom
    exact ⟨s, by simpa using hs⟩
  · rintro ⟨s, hs⟩
    exact Nat.rfind_dom.2 ⟨s, by simp [hs], fun {_} _ => trivial⟩

/-! ### Extensional classes -/

/-- A predicate on indices is **extensional** when it depends only on the set named. -/
def Extensional (A : ℕ → Prop) : Prop :=
  ∀ e e' : ℕ, (∀ x, Wset e x ↔ Wset e' x) → (A e ↔ A e')

/-- If membership of a computable family of r.e. sets in `A` is exactly non-membership in the
halting set, and `A` is r.e., we have a contradiction: the complement of the halting set would be
r.e. -/
theorem false_of_compl_haltK_iff {A : ℕ → Prop} (hA : REPred A) {f : ℕ → ℕ} (hf : Computable f)
    (hspec : ∀ n, ¬ HaltK n ↔ A (f n)) : False := by
  refine not_rePred_not_haltK ?_
  refine (hA.comp hf).of_eq fun n => ?_
  change (Part.assert (A (f n)) fun _ => Part.some ()) =
    Part.assert (¬ HaltK n) fun _ => Part.some ()
  rw [propext (hspec n)]

/-! ### An r.e. extensional class is upward closed -/

/-- **An r.e. extensional class is upward closed.**  If `A` holds of an index `d` and the set named
by `d` is contained in the set named by `e`, then `A` holds of `e`.

Otherwise the family `W (h n) = W d ∪ (W e if n halts)` would satisfy `n ∉ K ↔ A (h n)`. -/
theorem rePred_extensional_mono {A : ℕ → Prop} (hA : REPred A) (hext : Extensional A)
    {d e : ℕ} (hAd : A d) (hsub : ∀ x, Wset d x → Wset e x) : A e := by
  by_contra hne
  have h1 : Computable fun q : (ℕ × ℕ) × ℕ => acc d q.2 q.1.2 :=
    computable_acc (Computable.const d) Computable.snd (Computable.snd.comp Computable.fst)
  have h2 : Computable fun q : (ℕ × ℕ) × ℕ => acc q.1.1 q.2 q.1.1 :=
    computable_acc (Computable.fst.comp Computable.fst) Computable.snd
      (Computable.fst.comp Computable.fst)
  have h3 : Computable fun q : (ℕ × ℕ) × ℕ => acc e q.2 q.1.2 :=
    computable_acc (Computable.const e) Computable.snd (Computable.snd.comp Computable.fst)
  have hcomp : Computable fun q : (ℕ × ℕ) × ℕ =>
      acc d q.2 q.1.2 || (acc q.1.1 q.2 q.1.1 && acc e q.2 q.1.2) :=
    (Primrec.dom_bool₂ (fun a b => a || b)).to_comp.comp h1
      ((Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp h2 h3)
  obtain ⟨h, hh, hspec⟩ :=
    exists_index_of_test (fun n x s => acc d s x || (acc n s n && acc e s x)) hcomp
  have hmem : ∀ n x, Wset (h n) x ↔ (Wset d x ∨ (HaltK n ∧ Wset e x)) := by
    intro n x
    rw [hspec n x]
    constructor
    · rintro ⟨s, hs⟩
      rcases Bool.or_eq_true_iff.1 hs with hd | hk
      · exact Or.inl ((Wset_iff_exists_acc d x).2 ⟨s, hd⟩)
      · obtain ⟨hk1, hk2⟩ := Bool.and_eq_true_iff.1 hk
        exact Or.inr ⟨(haltK_iff_exists_acc n).2 ⟨s, hk1⟩,
          (Wset_iff_exists_acc e x).2 ⟨s, hk2⟩⟩
    · rintro (hd | ⟨hk, hx⟩)
      · obtain ⟨s, hs⟩ := (Wset_iff_exists_acc d x).1 hd
        exact ⟨s, by simp [hs]⟩
      · obtain ⟨s₁, hs₁⟩ := (haltK_iff_exists_acc n).1 hk
        obtain ⟨s₂, hs₂⟩ := (Wset_iff_exists_acc e x).1 hx
        refine ⟨max s₁ s₂, ?_⟩
        simp [acc_mono (le_max_left s₁ s₂) hs₁, acc_mono (le_max_right s₁ s₂) hs₂]
  refine false_of_compl_haltK_iff hA hh fun n => ?_
  by_cases hk : HaltK n
  · have hAe : A (h n) ↔ A e := by
      refine hext _ _ fun x => ?_
      rw [hmem n x]
      exact ⟨fun hx => hx.elim (hsub x) fun hx' => hx'.2, fun hx => Or.inr ⟨hk, hx⟩⟩
    simp [hk, hAe, hne]
  · have hAd' : A (h n) ↔ A d := by
      refine hext _ _ fun x => ?_
      rw [hmem n x]
      exact ⟨fun hx => hx.elim id fun hx' => absurd hx'.1 hk, Or.inl⟩
    simp [hk, hAd', hAd]

/-! ### A member of an r.e. extensional class has a finite member below it -/

/-- **A member of an r.e. extensional class contains a finite member of the class.**

Otherwise the family `W (h n) = {x ∈ W e enumerated before n halts}` would satisfy
`n ∉ K ↔ A (h n)`: if `n` never halts this is `W e`, and if `n` halts at stage `s₀` it is a finite
subset of `W e`. -/
theorem rePred_extensional_finite_witness {A : ℕ → Prop} (hA : REPred A) (hext : Extensional A)
    {e : ℕ} (he : A e) :
    ∃ d : ℕ, {x : ℕ | Wset d x}.Finite ∧ (∀ x, Wset d x → Wset e x) ∧ A d := by
  by_contra hno
  push Not at hno
  have h1 : Computable fun q : (ℕ × ℕ) × ℕ => acc e q.2 q.1.2 :=
    computable_acc (Computable.const e) Computable.snd (Computable.snd.comp Computable.fst)
  have h2 : Computable fun q : (ℕ × ℕ) × ℕ => acc q.1.1 q.2 q.1.1 :=
    computable_acc (Computable.fst.comp Computable.fst) Computable.snd
      (Computable.fst.comp Computable.fst)
  have hcomp : Computable fun q : (ℕ × ℕ) × ℕ => acc e q.2 q.1.2 && !(acc q.1.1 q.2 q.1.1) :=
    (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp h1 (Primrec.not.to_comp.comp h2)
  obtain ⟨h, hh, hspec⟩ :=
    exists_index_of_test (fun n x s => acc e s x && !(acc n s n)) hcomp
  have hmem : ∀ n x, Wset (h n) x ↔ ∃ s, acc e s x = Bool.true ∧ acc n s n = Bool.false := by
    intro n x
    rw [hspec n x]
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hs
      exact ⟨s, h1, by simpa using h2⟩
    · rintro ⟨s, h1, h2⟩
      exact ⟨s, by simp [h1, h2]⟩
  have hsub : ∀ n x, Wset (h n) x → Wset e x := by
    intro n x hx
    obtain ⟨s, hs, -⟩ := (hmem n x).1 hx
    exact (Wset_iff_exists_acc e x).2 ⟨s, hs⟩
  refine false_of_compl_haltK_iff hA hh fun n => ?_
  by_cases hk : HaltK n
  · -- the set named by `h n` is finite, so it is not in `A`
    obtain ⟨s₀, hs₀⟩ := (haltK_iff_exists_acc n).1 hk
    have hfin : {x : ℕ | Wset (h n) x}.Finite := by
      refine Set.Finite.subset (Set.finite_Iio s₀) fun x hx => ?_
      obtain ⟨s, hs, hns⟩ := (hmem n x).1 hx
      have hlt : s < s₀ := by
        by_contra hle
        rw [acc_mono (Nat.le_of_not_lt hle) hs₀] at hns
        exact Bool.noConfusion hns
      exact lt_trans (acc_bound hs) hlt
    have : ¬ A (h n) := hno (h n) hfin (hsub n)
    simp [hk, this]
  · -- the set named by `h n` is all of `W e`
    have hAe : A (h n) ↔ A e := by
      refine hext _ _ fun x => ?_
      rw [hmem n x]
      constructor
      · rintro ⟨s, hs, -⟩
        exact (Wset_iff_exists_acc e x).2 ⟨s, hs⟩
      · intro hx
        obtain ⟨s, hs⟩ := (Wset_iff_exists_acc e x).1 hx
        refine ⟨s, hs, ?_⟩
        by_contra hcon
        exact hk ((haltK_iff_exists_acc n).2 ⟨s, by simpa using hcon⟩)
    simp [hk, hAe, he]

/-! ### The theorem -/

/-- **The Rice–Shapiro theorem.**  An r.e. extensional class contains the set named by `e` exactly
when it contains a finite subset of it. -/
theorem rice_shapiro {A : ℕ → Prop} (hA : REPred A) (hext : Extensional A) (e : ℕ) :
    A e ↔ ∃ d : ℕ, {x : ℕ | Wset d x}.Finite ∧ (∀ x, Wset d x → Wset e x) ∧ A d :=
  ⟨rePred_extensional_finite_witness hA hext,
    fun ⟨_, _, hsub, hAd⟩ => rePred_extensional_mono hA hext hAd hsub⟩

/-! ### Two consequences -/

/-- The class of indices of the empty set is extensional. -/
theorem extensional_emptyIndex : Extensional fun d => ∀ x, ¬ Wset d x := by
  intro e e' hee'
  exact ⟨fun h x hx => h x ((hee' x).2 hx), fun h x hx => h x ((hee' x).1 hx)⟩

/-- The index of the code `zero`, whose set is all of `ℕ`. -/
theorem Wset_encode_zero (x : ℕ) : Wset (Encodable.encode Code.zero) x := by
  simp only [Wset, Denumerable.ofNat_encode, Code.eval]
  trivial

/-- **The class of indices of the empty set is not r.e.**  It would be upward closed by
Rice–Shapiro, which is absurd since the empty set is contained in every set. -/
theorem not_rePred_emptyIndex : ¬ REPred fun d => ∀ x, ¬ Wset d x := by
  intro hA
  obtain ⟨e₀, he₀⟩ := exists_empty_index
  have hall : ∀ x, ¬ Wset (Encodable.encode Code.zero) x :=
    rePred_extensional_mono hA extensional_emptyIndex (d := e₀) he₀
      (fun x hx => absurd hx (he₀ x))
  exact hall 0 (Wset_encode_zero 0)

/-- The class of indices of the everywhere-defined functions is extensional. -/
theorem extensional_totalIndex : Extensional fun d => ∀ x, Wset d x := by
  intro e e' hee'
  exact ⟨fun h x => (hee' x).1 (h x), fun h x => (hee' x).2 (h x)⟩

/-- **The class of indices of the total functions is not r.e.**: by Rice–Shapiro it would contain
a finite set, but no finite set of numbers is all of `ℕ`. -/
theorem not_rePred_totalIndex : ¬ REPred fun d => ∀ x, Wset d x := by
  intro hA
  obtain ⟨d, hfin, -, hd⟩ := rePred_extensional_finite_witness hA extensional_totalIndex
    (e := Encodable.encode Code.zero) Wset_encode_zero
  have huniv : {x : ℕ | Wset d x} = Set.univ := Set.eq_univ_of_forall hd
  rw [huniv] at hfin
  exact Set.infinite_univ hfin

end Post

end Lambda
