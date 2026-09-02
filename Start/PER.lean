/-
Partial equivalence relations over a partial combinatory algebra.

A **PER** on a PCA `A` is a symmetric and transitive relation on `A`; its *domain* is the set of
elements related to themselves, and the quotient of that domain is the set the PER presents.
PERs are the modest sets of realizability in their most economical form, and they are the
standard semantics of impredicative polymorphism: the **intersection** of an arbitrary family of
PERs is again a PER, which is what makes `∀X. A` interpretable.

* `Realizability.PER` — the structure, with `dom`, `Setoid` and `Quot`;
* `Realizability.PER.arrow` — the function-space PER `R ⇒ S`;
* `Realizability.PER.iInter` — the intersection of an arbitrary family, and
  `Realizability.PER.top`;
* `Realizability.PER.toAsm` — the assembly presented by a PER, and
  `Realizability.PER.modest_toAsm` — it is modest: distinct elements have disjoint sets of
  realizers.

The interpretation of System F in this setting is `Start/PERSystemF.lean`.
-/

import Start.Assembly

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u w

namespace Realizability

variable {A : Type u} [PCA A]

/-- A **partial equivalence relation** on a partial combinatory algebra. -/
structure PER (A : Type u) [PCA A] where
  /-- The relation. -/
  rel : A → A → Prop
  /-- Symmetry. -/
  symm : ∀ {a b : A}, rel a b → rel b a
  /-- Transitivity. -/
  trans : ∀ {a b c : A}, rel a b → rel b c → rel a c

namespace PER

@[ext] theorem ext {R S : PER A} (h : ∀ a b, R.rel a b ↔ S.rel a b) : R = S := by
  cases R; cases S
  simp only [PER.mk.injEq]
  funext a b
  exact propext (h a b)

/-- The domain of a PER: the elements it relates to themselves. -/
def dom (R : PER A) (a : A) : Prop := R.rel a a

theorem dom_left {R : PER A} {a b : A} (h : R.rel a b) : R.dom a := R.trans h (R.symm h)

theorem dom_right {R : PER A} {a b : A} (h : R.rel a b) : R.dom b := R.trans (R.symm h) h

/-- The setoid on the domain of a PER. -/
def setoid (R : PER A) : Setoid {a : A // R.dom a} where
  r x y := R.rel x.1 y.1
  iseqv :=
    { refl := fun x => x.2
      symm := fun h => R.symm h
      trans := fun h₁ h₂ => R.trans h₁ h₂ }

/-- The set presented by a PER: the quotient of its domain. -/
def Quot (R : PER A) : Type u := Quotient R.setoid

/-- The class of an element of the domain. -/
def cls (R : PER A) (a : A) (h : R.dom a) : R.Quot := Quotient.mk R.setoid ⟨a, h⟩

theorem cls_eq_cls {R : PER A} {a b : A} (ha : R.dom a) (hb : R.dom b) :
    R.cls a ha = R.cls b hb ↔ R.rel a b :=
  ⟨fun h => Quotient.exact (s := R.setoid) h, fun h => Quotient.sound (s := R.setoid) h⟩

theorem quot_ind {R : PER A} {motive : R.Quot → Prop}
    (h : ∀ (a : A) (ha : R.dom a), motive (R.cls a ha)) (x : R.Quot) : motive x :=
  Quotient.ind (motive := motive) (fun p => h p.1 p.2) x

/-! ### The function space -/

/-- The **arrow PER** `R ⇒ S`: two elements are related when they send related elements of `R` to
related elements of `S`. -/
def arrow (R S : PER A) : PER A where
  rel r r' := ∀ a b : A, R.rel a b → ∃ u ∈ PCA.app r a, ∃ v ∈ PCA.app r' b, S.rel u v
  symm {r r'} h := by
    intro a b hab
    obtain ⟨u, hu, v, hv, huv⟩ := h b a (R.symm hab)
    exact ⟨v, hv, u, hu, S.symm huv⟩
  trans {r r' r''} h₁ h₂ := by
    intro a b hab
    obtain ⟨u, hu, w, hw, huw⟩ := h₁ a b hab
    obtain ⟨w', hw', v, hv, hwv⟩ := h₂ b b (dom_right hab)
    refine ⟨u, hu, v, hv, S.trans huw ?_⟩
    rwa [← Part.mem_unique hw hw'] at hwv

theorem arrow_apply {R S : PER A} {r r' : A} (h : (arrow R S).rel r r') {a b : A}
    (hab : R.rel a b) : ∃ u ∈ PCA.app r a, ∃ v ∈ PCA.app r' b, S.rel u v := h a b hab

/-! ### Intersections -/

/-- The **intersection** of an arbitrary family of PERs.  This is what makes impredicative
quantification interpretable: the family may be indexed by *all* PERs. -/
def iInter {ι : Sort w} (F : ι → PER A) : PER A where
  rel a b := ∀ i, (F i).rel a b
  symm h i := (F i).symm (h i)
  trans h₁ h₂ i := (F i).trans (h₁ i) (h₂ i)

theorem iInter_rel {ι : Sort w} {F : ι → PER A} {a b : A} :
    (iInter F).rel a b ↔ ∀ i, (F i).rel a b := Iff.rfl

/-- The largest PER: everything is related to everything. -/
def top (A : Type u) [PCA A] : PER A where
  rel _ _ := True
  symm _ := trivial
  trans _ _ := trivial

/-! ### PERs as assemblies -/

/-- The assembly presented by a PER: its quotient set, an element being realized by any
representative of it. -/
def toAsm (R : PER A) : Assembly.{u, u} A where
  carrier := R.Quot
  realizes a x := ∃ h : R.dom a, R.cls a h = x
  exists_realizer x :=
    quot_ind (motive := fun x => ∃ a, ∃ h : R.dom a, R.cls a h = x)
      (fun a ha => ⟨a, ha, rfl⟩) x

/-- **PERs are modest**. -/
theorem modest_toAsm (R : PER A) : R.toAsm.Modest := by
  rintro a x y ⟨h, rfl⟩ ⟨h', rfl⟩
  rfl

end PER

end Realizability
