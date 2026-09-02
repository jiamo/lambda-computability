/-
Booleans and decidable subobjects over Kleene's first algebra.

`Start/AssemblyKleene.lean` describes the standard assembly of natural numbers over `K₁` and shows
that its maps are exactly the computable functions.  This file does the same for the *booleans*
and draws the expected consequence: a predicate on the numbers is cut out by a characteristic map
into the assembly of booleans exactly when it is a computable predicate.  Since self-halting is
not computable, it is a predicate on the numbers with no characteristic boolean map: in `Asm(K₁)`
the booleans do *not* classify sub-assemblies, in sharp contrast with the object of propositions
of `Start/AssemblySubobject.lean`, which classifies every sub-assembly precisely because it
carries no computational content.

* `Realizability.Kleene.exists_index_of_partrec`, `.exists_index_of_computable` — every partial
  recursive function is Turing application of a fixed index;
* `Realizability.Kleene.boolK1` — the standard assembly of booleans, `true` realized by `1` and
  `false` by `0`, and `Realizability.Kleene.modest_boolK1`;
* `Realizability.Kleene.tracked_boolK1_iff` — a boolean-valued function of natural numbers is
  tracked exactly when it is computable, and `Realizability.Kleene.boolHomEquiv`;
* `Realizability.Kleene.exists_charBool_iff` — a predicate on the numbers has a characteristic
  morphism into the booleans exactly when it is a computable predicate;
* `Realizability.Kleene.not_computable_selfHalt` — undecidability of self-halting, and
  `Realizability.Kleene.no_charBool_selfHalt`, `.boolK1_not_classifier` — the booleans of
  `Asm(K₁)` therefore classify no subobject of the numbers cut out by self-halting;
* `Realizability.Kleene.rePred_iff_exists_index`, `.rePred_selfHalt`,
  `.not_computablePred_selfHalt` — a predicate is recursively enumerable exactly when it is the
  domain of convergence of an element of `K₁`, and self-halting is such a predicate: it is
  semidecidable but not decidable;
* `Realizability.Kleene.boolK1IsoCoprod`, `.boolCofanIsColimit` — the booleans are nonetheless the
  coproduct `1 + 1` of `Start/AssemblyColimits.lean`: their two points exhibit them as a
  coproduct of two copies of the terminal assembly.
-/

import Start.AssemblyKleene
import Start.AssemblyColimits
import Mathlib.Computability.Halting

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

namespace Kleene

open CategoryTheory CategoryTheory.Limits
open Nat.Partrec (Code)
open Nat.Partrec.Code
open Encodable Denumerable
open Realizability.Assembly

/-! ### Indices for partial recursive functions -/

/-- Every partial recursive function of one variable is Turing application of a fixed index. -/
theorem exists_index_of_partrec {h : ℕ →. ℕ} (hh : Partrec h) : ∃ r : ℕ, ∀ n, natApp r n = h n := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 hh)
  exact ⟨encode c, fun n => by rw [natApp_encode, hc]⟩

/-- Every computable function is Turing application of a fixed index. -/
theorem exists_index_of_computable {h : ℕ → ℕ} (hh : Computable h) :
    ∃ r : ℕ, ∀ n, natApp r n = Part.some (h n) := by
  obtain ⟨c, hc⟩ := exists_code_of_computable hh
  exact ⟨encode c, fun n => by rw [natApp_encode, hc]⟩

/-! ### The standard assembly of booleans -/

/-- The numeral of a boolean: `1` for `true`, `0` for `false`. -/
def boolNum (b : Bool) : ℕ := cond b 1 0

@[simp] theorem boolNum_true : boolNum true = 1 := rfl

@[simp] theorem boolNum_false : boolNum false = 0 := rfl

theorem boolNum_eq_encode (b : Bool) : boolNum b = encode b := by cases b <;> rfl

theorem eq_of_boolNum_eq {b c : Bool} (h : boolNum b = boolNum c) : b = c := by
  cases b <;> cases c <;> simp_all [boolNum]

/-- The **standard assembly of booleans** over `K₁`: `true` is realized by `1`, `false` by `0`. -/
def boolK1 : Assembly.{0, 0} ℕ where
  carrier := Bool
  realizes a b := a = boolNum b
  exists_realizer b := ⟨boolNum b, rfl⟩

@[simp] theorem boolK1_realizes (a : ℕ) (b : Bool) : boolK1.realizes a b ↔ a = boolNum b := Iff.rfl

/-- The booleans assembly is modest: a realizer determines its element. -/
theorem modest_boolK1 : boolK1.Modest := by
  intro a x y hx hy
  exact eq_of_boolNum_eq ((hx : a = boolNum x).symm.trans (hy : a = boolNum y))

/-! ### The maps into the booleans are the computable predicates -/

/-- **Effective Church's thesis for boolean-valued functions**: a function `ℕ → Bool` is tracked
from the standard numbers assembly to the standard booleans assembly exactly when it is
computable. -/
theorem tracked_boolK1_iff {f : ℕ → Bool} : Tracked natK1 boolK1 f ↔ Computable f := by
  constructor
  · rintro ⟨r, hr⟩
    have hmem : ∀ n : ℕ, boolNum (f n) ∈ natApp r n := by
      intro n
      obtain ⟨v, hv, hvx⟩ := hr n n rfl
      have hv' : v ∈ natApp r n := hv
      have hveq : v = boolNum (f n) := hvx
      rwa [hveq] at hv'
    have hpart : Partrec fun n : ℕ => natApp r n :=
      Partrec₂.comp (f := natApp) partrec_natApp (Computable.const r) Computable.id
    have hnum : Computable fun n : ℕ => boolNum (f n) := by
      refine Computable.of_eq (Partrec.of_eq hpart fun n => ?_) fun _ => rfl
      rw [Part.eq_some_iff.2 (hmem n)]
      rfl
    exact Computable.encode_iff.1 (hnum.of_eq fun n => boolNum_eq_encode (f n))
  · intro hf
    have hnum : Computable fun n : ℕ => boolNum (f n) :=
      (Computable.encode_iff.2 hf).of_eq fun n => (boolNum_eq_encode (f n)).symm
    obtain ⟨r, hr⟩ := exists_index_of_computable hnum
    refine ⟨r, fun a n ha => ?_⟩
    have hna : a = n := ha
    subst hna
    have hmem : boolNum (f a) ∈ natApp r a := by rw [hr a]; exact Part.mem_some _
    exact ⟨boolNum (f a), hmem, rfl⟩

/-- The underlying boolean-valued function of a morphism into the standard booleans assembly. -/
def toBoolFun (g : natK1 ⟶ boolK1) : ℕ → Bool := fun n => g.toFun n

theorem computable_toBoolFun (g : natK1 ⟶ boolK1) : Computable (toBoolFun g) :=
  tracked_boolK1_iff.1 g.tracked

/-- The maps from the standard numbers assembly to the standard booleans assembly are exactly the
computable boolean-valued functions. -/
noncomputable def boolHomEquiv : (natK1 ⟶ boolK1) ≃ {f : ℕ → Bool // Computable f} where
  toFun g := ⟨g.toFun, tracked_boolK1_iff.1 g.tracked⟩
  invFun f := ⟨f.1, tracked_boolK1_iff.2 f.2⟩
  left_inv _ := AsmHom.ext rfl
  right_inv _ := Subtype.ext rfl

/-- **Decidable predicates on the numbers**: a predicate on the natural numbers is cut out by a
characteristic morphism into the booleans exactly when it is a computable predicate. -/
theorem exists_charBool_iff {P : ℕ → Prop} :
    (∃ g : natK1 ⟶ boolK1, ∀ n, g.toFun n = true ↔ P n) ↔ ComputablePred P := by
  constructor
  · rintro ⟨g, hg⟩
    exact ComputablePred.computable_iff.2
      ⟨toBoolFun g, computable_toBoolFun g, funext fun n => propext (hg n).symm⟩
  · intro hP
    obtain ⟨f, hf, hPf⟩ := ComputablePred.computable_iff.1 hP
    exact ⟨⟨f, tracked_boolK1_iff.2 hf⟩, fun n => by rw [hPf]; exact Iff.rfl⟩

/-! ### Self-halting has no characteristic boolean map -/

/-- Self-halting: the machine with index `n` converges on the input `n`. -/
def selfHalt (n : ℕ) : Prop := (natApp n n).Dom

/-- **Undecidability of self-halting**: no computable boolean function decides whether the
machine with index `n` converges on `n`.  Feeding such a decision procedure to the machine that
diverges exactly when it says "halts" contradicts it on its own index. -/
theorem not_computable_selfHalt :
    ¬ ∃ f : ℕ → Bool, Computable f ∧ ∀ n, f n = true ↔ selfHalt n := by
  rintro ⟨f, hf, hfs⟩
  have hpart : Partrec fun n : ℕ => cond (f n) (Part.none : Part ℕ) (Part.some 0) :=
    Partrec.cond hf Partrec.none (Computable.const 0).partrec
  obtain ⟨r, hr⟩ := exists_index_of_partrec hpart
  have hdom : selfHalt r ↔ f r = false := by
    rw [selfHalt, hr r]
    cases h : f r <;> simp
  cases h : f r with
  | false =>
      have hs : selfHalt r := hdom.2 h
      rw [(hfs r).2 hs] at h
      exact Bool.noConfusion h
  | true =>
      have hs : selfHalt r := (hfs r).1 h
      rw [hdom.1 hs] at h
      exact Bool.noConfusion h

/-- The dual form: no computable boolean function decides self-halting "the other way round". -/
theorem not_computable_selfHalt_false :
    ¬ ∃ f : ℕ → Bool, Computable f ∧ ∀ n, f n = false ↔ selfHalt n := by
  rintro ⟨f, hf, hfs⟩
  refine not_computable_selfHalt ⟨fun n => !f n, (Primrec.not.to_comp).comp hf, fun n => ?_⟩
  rw [Bool.not_eq_true', hfs n]

/-- The predicate of self-halting has **no characteristic map into the booleans**: in `Asm(K₁)`
the booleans do not decide every predicate on the numbers. -/
theorem no_charBool_selfHalt : ¬ ∃ g : natK1 ⟶ boolK1, ∀ n, g.toFun n = true ↔ selfHalt n := by
  rintro ⟨g, hg⟩
  exact not_computable_selfHalt ⟨toBoolFun g, computable_toBoolFun g, hg⟩

/-- **The booleans do not classify sub-assemblies in `Asm(K₁)`**: self-halting is a predicate on
the numbers which is not the preimage of *either* boolean along a morphism into the booleans,
whereas it is of course cut out by a morphism into the object of propositions of
`Start/AssemblySubobject.lean`. -/
theorem boolK1_not_classifier (b : Bool) :
    ¬ ∃ g : natK1 ⟶ boolK1, ∀ n, g.toFun n = b ↔ selfHalt n := by
  rintro ⟨g, hg⟩
  cases b with
  | true => exact not_computable_selfHalt ⟨toBoolFun g, computable_toBoolFun g, hg⟩
  | false => exact not_computable_selfHalt_false ⟨toBoolFun g, computable_toBoolFun g, hg⟩

/-! ### Semidecidability: self-halting is recursively enumerable but not decidable -/

/-- A predicate on the natural numbers is **recursively enumerable exactly when it is the domain
of convergence of a single element of `K₁`**. -/
theorem rePred_iff_exists_index {P : ℕ → Prop} :
    REPred P ↔ ∃ r : ℕ, ∀ n, P n ↔ (natApp r n).Dom := by
  constructor
  · intro hP
    have hpart : Partrec fun n : ℕ => (Part.assert (P n) fun _ => Part.some (0 : ℕ)) := by
      refine (hP.map (Computable.const (0 : ℕ)).to₂).of_eq fun n => ?_
      rfl
    obtain ⟨r, hr⟩ := exists_index_of_partrec hpart
    exact ⟨r, fun n => by rw [hr n]; exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩⟩
  · rintro ⟨r, hr⟩
    have hpart : Partrec fun n : ℕ => natApp r n :=
      Partrec₂.comp (f := natApp) partrec_natApp (Computable.const r) Computable.id
    have hdom : REPred fun n : ℕ => (natApp r n).Dom := hpart.dom_re
    exact (funext fun n => propext (hr n) : P = fun n => (natApp r n).Dom) ▸ hdom

/-- Self-halting is **recursively enumerable**: run the machine and see. -/
theorem rePred_selfHalt : REPred selfHalt := by
  have hpart : Partrec fun n : ℕ => natApp n n :=
    Partrec₂.comp (f := natApp) partrec_natApp Computable.id Computable.id
  exact hpart.dom_re

/-- Self-halting is **not decidable**, so a recursively enumerable predicate on the numbers need
have no characteristic morphism into the booleans of `Asm(K₁)`. -/
theorem not_computablePred_selfHalt : ¬ ComputablePred selfHalt := fun h =>
  no_charBool_selfHalt (exists_charBool_iff.2 h)


/-! ### The booleans are the coproduct of two copies of the terminal assembly -/

/-- Decoding a coproduct tag: the first component of a Church pair, applied to `0` and then to
`1`.  The tag `k` of the left summand yields `0`, the tag `k i` of the right summand yields `1`. -/
noncomputable def tagDecode (p : ℕ) : Part ℕ :=
  (natApp (PCA.fstComb ℕ) p).bind fun t => (natApp t 0).bind fun u => natApp u 1

theorem partrec_tagDecode : Partrec tagDecode := by
  refine Partrec.bind (Partrec₂.comp (f := natApp) partrec_natApp
    (Computable.const (PCA.fstComb ℕ)) Computable.id) ?_
  refine Partrec.bind (Partrec₂.comp (f := natApp) partrec_natApp Computable.snd
    (Computable.const 0)) ?_
  exact Partrec₂.comp (f := natApp) partrec_natApp Computable.snd (Computable.const 1)

theorem natApp_bind_natApp (a b c : ℕ) :
    ((natApp a b).bind fun u => natApp u c) = (Part.some a ⬝ Part.some b) ⬝ Part.some c := by
  rw [papp_some_some, papp_some_right]
  rfl

theorem tagDecode_pairEl_k (a : ℕ) : tagDecode (PCA.pairEl (PCA.k : ℕ) a) = Part.some 0 := by
  rw [tagDecode, natApp_fstComb_pairEl, Part.bind_some, natApp_bind_natApp, PCA.k_app_app]

theorem tagDecode_pairEl_kI (a : ℕ) : tagDecode (PCA.pairEl (PCA.kI ℕ) a) = Part.some 1 := by
  rw [tagDecode, natApp_fstComb_pairEl, Part.bind_some, natApp_bind_natApp, PCA.kI_app]

/-- The morphism reading a tagged element of `1 + 1` as a boolean. -/
noncomputable def boolOfSum :
    coprodAsm (unitAsm.{0, 0} ℕ) (unitAsm.{0, 0} ℕ) ⟶ boolK1 where
  toFun := Sum.elim (fun _ => false) (fun _ => true)
  tracked := by
    obtain ⟨r, hr⟩ := exists_index_of_partrec partrec_tagDecode
    refine ⟨r, fun p z hz => ?_⟩
    cases z with
    | inl x =>
        obtain ⟨a, _, rfl⟩ := hz
        refine ⟨0, ?_, rfl⟩
        have : (0 : ℕ) ∈ natApp r (PCA.pairEl (PCA.k : ℕ) a) := by
          rw [hr, tagDecode_pairEl_k]; exact Part.mem_some _
        exact this
    | inr y =>
        obtain ⟨b, _, rfl⟩ := hz
        refine ⟨1, ?_, rfl⟩
        have : (1 : ℕ) ∈ natApp r (PCA.pairEl (PCA.kI ℕ) b) := by
          rw [hr, tagDecode_pairEl_kI]; exact Part.mem_some _
        exact this

/-- The morphism tagging a boolean as an element of `1 + 1`. -/
noncomputable def sumOfBool :
    boolK1 ⟶ coprodAsm (unitAsm.{0, 0} ℕ) (unitAsm.{0, 0} ℕ) where
  toFun b := cond b (Sum.inr PUnit.unit) (Sum.inl PUnit.unit)
  tracked := by
    have hcomp : Computable fun a : ℕ =>
        if a = 1 then PCA.pairEl (PCA.kI ℕ) 0 else PCA.pairEl (PCA.k : ℕ) 0 :=
      Primrec.to_comp (Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const 1))
        (Primrec.const _) (Primrec.const _))
    obtain ⟨r, hr⟩ := exists_index_of_computable hcomp
    refine ⟨r, fun a b hb => ?_⟩
    have hab : a = boolNum b := hb
    subst hab
    cases b with
    | false =>
        refine ⟨PCA.pairEl (PCA.k : ℕ) 0, ?_, 0, trivial, rfl⟩
        have : PCA.pairEl (PCA.k : ℕ) 0 ∈ natApp r (boolNum false) := by
          rw [hr]; simp [boolNum]
        exact this
    | true =>
        refine ⟨PCA.pairEl (PCA.kI ℕ) 0, ?_, 0, trivial, rfl⟩
        have : PCA.pairEl (PCA.kI ℕ) 0 ∈ natApp r (boolNum true) := by
          rw [hr]; simp [boolNum]
        exact this

/-- **The standard booleans are the coproduct `1 + 1`** in `Asm(K₁)`: reading a tag as a boolean
and tagging a boolean are mutually inverse morphisms.  With
`Realizability.Assembly.coprodCofanIsColimit` this exhibits `boolK1` as a coproduct of two copies
of the terminal assembly. -/
noncomputable def boolK1IsoCoprod :
    boolK1 ≅ coprodAsm (unitAsm.{0, 0} ℕ) (unitAsm.{0, 0} ℕ) where
  hom := sumOfBool
  inv := boolOfSum
  hom_inv_id := hom_ext fun b => by cases b <;> rfl
  inv_hom_id := hom_ext fun z => by cases z with
    | inl x => cases x; rfl
    | inr y => cases y; rfl


/-- The point `false` of the booleans, realized by `0`. -/
noncomputable def falsePt : unitAsm.{0, 0} ℕ ⟶ boolK1 where
  toFun _ := false
  tracked := ⟨kFun 0, fun a _ _ => ⟨0, mem_natApp_kFun a 0, rfl⟩⟩

/-- The point `true` of the booleans, realized by `1`. -/
noncomputable def truePt : unitAsm.{0, 0} ℕ ⟶ boolK1 where
  toFun _ := true
  tracked := ⟨kFun 1, fun a _ _ => ⟨1, mem_natApp_kFun a 1, rfl⟩⟩

/-- The cofan of the two points of the booleans. -/
noncomputable def boolCofan : BinaryCofan (unitAsm.{0, 0} ℕ) (unitAsm.{0, 0} ℕ) :=
  BinaryCofan.mk falsePt truePt

/-- **The booleans of `Asm(K₁)` are the coproduct `1 + 1`**: the two points `false` and `true`
exhibit `boolK1` as a coproduct of two copies of the terminal assembly.  The copairing of two
points of an assembly is tracked because the tag of a boolean can be tested effectively — it is
the number `0` or the number `1`. -/
noncomputable def boolCofanIsColimit : IsColimit boolCofan :=
  BinaryCofan.isColimitMk
    (fun s => sumOfBool ≫ coprodDesc (BinaryCofan.inl s) (BinaryCofan.inr s))
    (fun _ => hom_ext fun x => by cases x; rfl) (fun _ => hom_ext fun x => by cases x; rfl)
    (fun s m h₁ h₂ => hom_ext fun b => by
      cases b with
      | false => exact congrArg (fun k : unitAsm.{0, 0} ℕ ⟶ s.pt => k.toFun PUnit.unit) h₁
      | true => exact congrArg (fun k : unitAsm.{0, 0} ℕ ⟶ s.pt => k.toFun PUnit.unit) h₂)


end Kleene

end Realizability
