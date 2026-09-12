/-
**The exact completion of the assemblies is not exact.**

`Start/AsmExRegRegular.lean` proves that the completion `ExReg(A)` built in `Start/AsmExReg.lean`
is a *regular* category.  Exactness is the next question: is every internal equivalence relation
of the completion the kernel pair of some morphism?  This module answers it, in the negative, for
every partial combinatory algebra with at least three elements — in particular for Kleene's first
algebra, `Realizability.Kleene.instPCANat`.

The obstruction is the one that the regularity development left open.  A morphism `T ⟶ R` of the
completion is a *function* on points together with a single element of the algebra that transports
proofs; in particular, by reflexivity, that element computes a realizer of the value `m t` from any
realizer of `t`.  So a morphism into `R` must pick one point of `R` per point of `T` *and* compute
a realizer of the chosen point uniformly.  When the points of `R` over a related pair are
realized by unrelated elements of the algebra, no such choice exists, while the pair is still
related in the quotient: the equivalence relation is not effective.

The counterexample is built from one two-element "witness" family per element of the algebra, in
such a way that the element `t` of the algebra fails to normalize the witnesses at the index `t`
itself.  A three-point pigeonhole (`Realizability.ExReg.NotExact.exists_pair_not_normalized`)
produces the family: application is single-valued, so an element of the algebra cannot map three
pairwise distinct elements into a single one of them.

Main definitions and results:

* `Realizability.ExReg.NotExact.IsInternalEquiv` — a parallel pair is an internal equivalence
  relation: jointly monic, reflexive, symmetric and transitive, the last two spelled out by their
  universal properties;
* `Realizability.ExReg.NotExact.isInternalEquiv_of_isKernelPair` — every kernel pair is one, so
  the notion is not vacuous;
* `Realizability.ExReg.NotExact.exists_internalEquiv_not_kernelPair` — **there is an internal
  equivalence relation of `ExReg(A)` which is not the kernel pair of any morphism**, whenever `A`
  has three distinct elements;
* `Realizability.ExReg.NotExact.kleene_exReg_not_exact` — the same for Kleene's first algebra:
  **the exact completion of the assemblies is not an exact category.**
-/

import Start.AsmExReg
import Start.PCAKleene
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

namespace NotExact

variable {A : Type u} [PCA A]

/-! ### Internal equivalence relations -/

/-- A parallel pair `p₁ p₂ : R ⟶ X` is an **internal equivalence relation** when it is jointly
monic, reflexive, symmetric and transitive.  Transitivity is stated by its universal property —
for every pair of morphisms into `R` whose middle endpoints agree there is a composite — which is
what a kernel pair satisfies and what the pullback formulation gives. -/
structure IsInternalEquiv {C : Type*} [Category C] {R X : C} (p₁ p₂ : R ⟶ X) : Prop where
  /-- The pair is jointly monic. -/
  jointly_mono : ∀ {T : C} (f g : T ⟶ R), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g
  /-- Reflexivity: a diagonal. -/
  refl' : ∃ d : X ⟶ R, d ≫ p₁ = 𝟙 X ∧ d ≫ p₂ = 𝟙 X
  /-- Symmetry: an involution swapping the two legs. -/
  symm' : ∃ s : R ⟶ R, s ≫ p₁ = p₂ ∧ s ≫ p₂ = p₁
  /-- Transitivity: composability of two morphisms into `R` with matching middle endpoints. -/
  trans' : ∀ {T : C} (f g : T ⟶ R), f ≫ p₂ = g ≫ p₁ →
    ∃ h : T ⟶ R, h ≫ p₁ = f ≫ p₁ ∧ h ≫ p₂ = g ≫ p₂

/-- **Every kernel pair is an internal equivalence relation.** -/
theorem isInternalEquiv_of_isKernelPair {C : Type*} [Category C] {R X Z : C} {k : X ⟶ Z}
    {p₁ p₂ : R ⟶ X} (h : IsKernelPair k p₁ p₂) : IsInternalEquiv p₁ p₂ where
  jointly_mono f g h₁ h₂ := h.hom_ext h₁ h₂
  refl' := ⟨(h.lift' (𝟙 X) (𝟙 X) rfl).1, (h.lift' (𝟙 X) (𝟙 X) rfl).2.1,
    (h.lift' (𝟙 X) (𝟙 X) rfl).2.2⟩
  symm' :=
    ⟨(h.lift' p₂ p₁ h.w.symm).1, (h.lift' p₂ p₁ h.w.symm).2.1, (h.lift' p₂ p₁ h.w.symm).2.2⟩
  trans' {T} f g hfg := by
    have hw : (f ≫ p₁) ≫ k = (g ≫ p₂) ≫ k := by
      rw [Category.assoc, Category.assoc, h.w, ← Category.assoc, hfg, Category.assoc, ← h.w]
    exact ⟨(h.lift' _ _ hw).1, (h.lift' _ _ hw).2.1, (h.lift' _ _ hw).2.2⟩

/-! ### Combinators -/

/-- The combinator `λa. pair (r a) (s a)`. -/
theorem exists_pairOf (r s : A) : ∃ q : A, ∀ a u w : A, u ∈ PCA.app r a → w ∈ PCA.app s a →
    PCA.pairEl u w ∈ PCA.app q a := by
  obtain ⟨q, hq⟩ := exists_pairApply (PCA.pairComb A) r s
  exact ⟨q, fun a u w hu hw =>
    hq a u w _ hu hw (by rw [PCA.pairComb_app]; exact Part.mem_some _)⟩

theorem mem_fstComb (a b : A) : a ∈ PCA.app (PCA.fstComb A) (PCA.pairEl a b) := by
  have h := PCA.fstComb_pairEl (A := A) a b
  rw [papp_some_some] at h
  rw [h]
  exact Part.mem_some _

theorem mem_sndComb (a b : A) : b ∈ PCA.app (PCA.sndComb A) (PCA.pairEl a b) := by
  have h := PCA.sndComb_pairEl (A := A) a b
  rw [papp_some_some] at h
  rw [h]
  exact Part.mem_some _

/-- The element `k c`, which computes the constant function with value `c`. -/
noncomputable def constEl (c : A) : A := (PCA.app (PCA.k : A) c).get (PCA.k_dom c)

theorem constEl_app (c x : A) : c ∈ PCA.app (constEl c) x := by
  have h := PCA.k_app c x
  have hk : PCA.app (PCA.k : A) c = Part.some (constEl c) := (Part.some_get _).symm
  rw [hk, Part.bind_some] at h
  rw [h]
  exact Part.mem_some _

/-- The combinator `λa. pair a c`, pairing its argument with a fixed element on the right. -/
theorem exists_pairRight (c : A) : ∃ q : A, ∀ a : A, PCA.pairEl a c ∈ PCA.app q a := by
  refine ⟨PCA.lam1 (Expr.app (Expr.app (Expr.const (PCA.pairComb A)) (Expr.var 0))
    (Expr.const c)), fun a => ?_⟩
  have h := PCA.lam1_app (Expr.app (Expr.app (Expr.const (PCA.pairComb A)) (Expr.var 0))
    (Expr.const c)) a
  rw [papp_some_some] at h
  refine h _ ?_
  simp only [Expr.eval_app, Expr.eval_const, Expr.eval_var, Function.update_self]
  rw [PCA.pairComb_app]
  exact Part.mem_some _

/-- The combinator `λab. pair (fst a) (snd b)`. -/
theorem exists_fstSndPair : ∃ t : A, ∀ (a b u w : A), u ∈ PCA.app (PCA.fstComb A) a →
    w ∈ PCA.app (PCA.sndComb A) b → PCA.pairEl u w ∈ (Part.some t ⬝ Part.some a) ⬝ Part.some b := by
  refine ⟨PCA.lam2 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
    (Expr.app (Expr.const (PCA.fstComb A)) (Expr.var 0)))
    (Expr.app (Expr.const (PCA.sndComb A)) (Expr.var 1))), fun a b u w hu hw => ?_⟩
  have hmem : PCA.pairEl u w ∈ (Part.some (PCA.pairComb A) ⬝ Part.some u) ⬝ Part.some w := by
    rw [PCA.pairComb_app]
    exact Part.mem_some _
  rw [papp_some_right] at hmem
  obtain ⟨v, hv, hvw⟩ := Part.mem_bind_iff.1 hmem
  rw [papp_some_some] at hv
  refine PCA.lam2_app_app _ a b _ ?_
  simp only [Expr.eval_app, Expr.eval_const, Expr.eval_var, Function.update_self,
    Function.update_of_ne (Nat.zero_ne_one)]
  rw [← papp_some_some] at hu hw
  exact mem_papp (mem_papp (Part.mem_some _) hu hv) hw hvw

/-- The composition combinator `B = λgh x. g (h x)`, as a statement about the element it
produces: from `g` and `h` one computes an element `b` with `b x ⊒ g (h x)`. -/
theorem exists_compComb : ∃ B : A, ∀ g h : A, ∃ b : A,
    b ∈ (Part.some B ⬝ Part.some g) ⬝ Part.some h ∧
      ∀ x v w : A, v ∈ PCA.app h x → w ∈ PCA.app g v → w ∈ PCA.app b x := by
  classical
  refine ⟨PCA.lam3 (Expr.app (Expr.var 0) (Expr.app (Expr.var 1) (Expr.var 2))), fun g h => ?_⟩
  refine ⟨PCA.lam 2 (Expr.app (Expr.var 0) (Expr.app (Expr.var 1) (Expr.var 2)))
    (Function.update (Function.update (PCA.env0 A) 0 g) 1 h), ?_, ?_⟩
  · rw [PCA.lam3_app_app]
    exact Part.mem_some _
  · intro x v w hv hw
    have h₀ := PCA.lam_app 2 (Expr.app (Expr.var 0) (Expr.app (Expr.var 1) (Expr.var 2)))
      (Function.update (Function.update (PCA.env0 A) 0 g) 1 h) x
    refine h₀ _ ?_
    simp only [Expr.eval_app, Expr.eval_var, Function.update_self]
    exact mem_papp (Part.mem_some _) (mem_papp (Part.mem_some _) (Part.mem_some _) hv) hw

/-! ### Labels -/

/-- The **labels** carried by the points of the counterexample: the identity function and the
constant functions.  They are closed under composition, with the identity as a unit, which is
what makes the counterexample an equivalence relation. -/
inductive Label (A : Type u) where
  /-- The identity label. -/
  | idL : Label A
  /-- The constant label with value `c`. -/
  | constL (c : A) : Label A

/-- The function a label denotes. -/
def Label.eval : Label A → A → A
  | Label.idL, x => x
  | Label.constL c, _ => c

/-- Composition of labels, denoting composition of the functions. -/
def Label.comp : Label A → Label A → Label A
  | Label.idL, m => m
  | Label.constL c, _ => Label.constL c

omit [PCA A] in
theorem Label.eval_comp (l m : Label A) (x : A) : (l.comp m).eval x = l.eval (m.eval x) := by
  cases l <;> rfl

/-- An element of the algebra **computes** a label when it computes the function it denotes. -/
def Label.Computes (l : Label A) (g : A) : Prop := ∀ x : A, l.eval x ∈ PCA.app g x

theorem Label.computes_idL : (Label.idL : Label A).Computes (PCA.i A) := by
  intro x
  rw [PCA.i_app]
  exact Part.mem_some _

theorem Label.computes_constL (c : A) : (Label.constL c : Label A).Computes (constEl c) :=
  fun x => constEl_app c x

theorem Label.exists_computes (l : Label A) : ∃ g : A, l.Computes g := by
  cases l with
  | idL => exact ⟨PCA.i A, Label.computes_idL⟩
  | constL c => exact ⟨constEl c, Label.computes_constL c⟩

/-- The combinator used for transitivity: from two elements `rF`, `rG` computing realizers of
points of `R` with the same index, one computes a realizer of the composite point, whose label
computing element is the composition of the two. -/
theorem exists_transComb (rF rG : A) : ∃ q : A, ∀ (a i gF gG : A),
    PCA.pairEl i gF ∈ PCA.app rF a → PCA.pairEl i gG ∈ PCA.app rG a →
    ∃ b : A, PCA.pairEl i b ∈ PCA.app q a ∧
      ∀ (l m : Label A), l.Computes gF → m.Computes gG → (l.comp m).Computes b := by
  obtain ⟨B, hB⟩ := exists_compComb (A := A)
  refine ⟨PCA.lam1 (Expr.app
      (Expr.app (Expr.const (PCA.pairComb A))
        (Expr.app (Expr.const (PCA.fstComb A)) (Expr.app (Expr.const rF) (Expr.var 0))))
      (Expr.app (Expr.app (Expr.const B)
        (Expr.app (Expr.const (PCA.sndComb A)) (Expr.app (Expr.const rF) (Expr.var 0))))
        (Expr.app (Expr.const (PCA.sndComb A)) (Expr.app (Expr.const rG) (Expr.var 0))))),
    fun a i gF gG hF hG => ?_⟩
  obtain ⟨b, hb, hbprop⟩ := hB gF gG
  refine ⟨b, ?_, ?_⟩
  · -- the value is computed by the term
    have hFa : PCA.pairEl i gF ∈ Part.some rF ⬝ Part.some a := by
      rw [papp_some_some]; exact hF
    have hGa : PCA.pairEl i gG ∈ Part.some rG ⬝ Part.some a := by
      rw [papp_some_some]; exact hG
    have hi : i ∈ Part.some (PCA.fstComb A) ⬝ (Part.some rF ⬝ Part.some a) :=
      mem_papp (Part.mem_some _) hFa (mem_fstComb i gF)
    have hgF : gF ∈ Part.some (PCA.sndComb A) ⬝ (Part.some rF ⬝ Part.some a) :=
      mem_papp (Part.mem_some _) hFa (mem_sndComb i gF)
    have hgG : gG ∈ Part.some (PCA.sndComb A) ⬝ (Part.some rG ⬝ Part.some a) :=
      mem_papp (Part.mem_some _) hGa (mem_sndComb i gG)
    -- decompose the two partial applications
    rw [papp_some_right] at hb
    obtain ⟨B₁, hB₁, hb₁⟩ := Part.mem_bind_iff.1 hb
    rw [papp_some_some] at hB₁
    have hmemPair : PCA.pairEl i b ∈ (Part.some (PCA.pairComb A) ⬝ Part.some i) ⬝ Part.some b := by
      rw [PCA.pairComb_app]; exact Part.mem_some _
    rw [papp_some_right] at hmemPair
    obtain ⟨P₁, hP₁, hp₁⟩ := Part.mem_bind_iff.1 hmemPair
    rw [papp_some_some] at hP₁
    have hlam := PCA.lam1_app (A := A) (Expr.app
      (Expr.app (Expr.const (PCA.pairComb A))
        (Expr.app (Expr.const (PCA.fstComb A)) (Expr.app (Expr.const rF) (Expr.var 0))))
      (Expr.app (Expr.app (Expr.const B)
        (Expr.app (Expr.const (PCA.sndComb A)) (Expr.app (Expr.const rF) (Expr.var 0))))
        (Expr.app (Expr.const (PCA.sndComb A)) (Expr.app (Expr.const rG) (Expr.var 0))))) a
    rw [papp_some_some] at hlam
    refine hlam _ ?_
    simp only [Expr.eval_app, Expr.eval_const, Expr.eval_var, Function.update_self]
    exact mem_papp (mem_papp (Part.mem_some _) hi hP₁)
      (mem_papp (mem_papp (Part.mem_some _) hgF hB₁) hgG hb₁) hp₁
  · intro l m hl hm x
    rw [Label.eval_comp]
    exact hbprop x (m.eval x) (l.eval (m.eval x)) (hm x) (hl _)

/-! ### The pigeonhole that produces the witnesses -/

omit [PCA A] in
/-- **Three distinct elements cannot be normalized to one of them.**  For any partial function
`f` given by the algebra and any three pairwise distinct elements, some pair among them is not
mapped by `f` into a single one of its two members. -/
theorem exists_pair_not_normalized (f : A → Part A) {x y z : A} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : ∃ c : Bool → A, ¬ ∃ u : Bool, ∀ j : Bool, c u ∈ f (c j) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨u₁, h₁⟩ := hcon (fun b => bif b then y else x)
  obtain ⟨u₂, h₂⟩ := hcon (fun b => bif b then z else y)
  obtain ⟨u₃, h₃⟩ := hcon (fun b => bif b then z else x)
  -- the three chosen values agree, because `f x` and `f y` are subsingletons
  have e₁ : (bif u₁ then y else x) ∈ f x := by simpa using h₁ false
  have e₁' : (bif u₁ then y else x) ∈ f y := by simpa using h₁ true
  have e₂ : (bif u₂ then z else y) ∈ f y := by simpa using h₂ false
  have e₃ : (bif u₃ then z else x) ∈ f x := by simpa using h₃ false
  have h12 : (bif u₁ then y else x) = (bif u₂ then z else y) := Part.mem_unique e₁' e₂
  have h13 : (bif u₁ then y else x) = (bif u₃ then z else x) := Part.mem_unique e₁ e₃
  cases u₁ <;> cases u₂ <;> cases u₃ <;> simp_all

/-! ### The objects of the counterexample -/

/-- The base of `X`: two points for every element of the algebra, the point `(s, b)` realized
exactly by `s`. -/
def xAsm (A : Type u) [PCA A] : Assembly.{u, u} A where
  carrier := A × Bool
  realizes r p := r = p.1
  exists_realizer p := ⟨p.1, rfl⟩

/-- `X`, an assembly with equality. -/
def xERel (A : Type u) [PCA A] : ERel.{u, u} A := eqERel (xAsm A)

/-- A point of `R`: a pair of points of `X` with the same index, together with a label; the
label is the identity only on the diagonal, and is otherwise one of the two witnesses attached
to the index. -/
structure RPt (cw : A → Bool → A) : Type u where
  /-- The common index of the two endpoints. -/
  idx : A
  /-- The tag of the first endpoint. -/
  src : Bool
  /-- The tag of the second endpoint. -/
  tgt : Bool
  /-- The label. -/
  lab : Label A
  /-- Only the diagonal carries the identity label; the others carry a witness. -/
  valid : (lab = Label.idL ∧ src = tgt) ∨ ∃ j : Bool, lab = Label.constL (cw idx j)

omit [PCA A] in
theorem RPt.ext' {cw : A → Bool → A} {p q : RPt cw} (hi : p.idx = q.idx) (hs : p.src = q.src)
    (ht : p.tgt = q.tgt) (hl : p.lab = q.lab) : p = q := by
  cases p; cases q; cases hi; cases hs; cases ht; cases hl; rfl

/-- The base of `R`: a point is realized by the pair of its index and an element computing its
label. -/
def rAsm (cw : A → Bool → A) : Assembly.{u, u} A where
  carrier := RPt cw
  realizes r p := ∃ g : A, p.lab.Computes g ∧ r = PCA.pairEl p.idx g
  exists_realizer p := by
    obtain ⟨g, hg⟩ := p.lab.exists_computes
    exact ⟨_, g, hg, rfl⟩

/-- `R`: two points of `R` are related when they have the same endpoints, a proof being the pair
of their realizers. -/
def rERel (cw : A → Bool → A) : ERel.{u, u} A where
  base := rAsm cw
  Prf w p q := (p.idx = q.idx ∧ p.src = q.src ∧ p.tgt = q.tgt) ∧
    ∃ r r' : A, (rAsm cw).realizes r p ∧ (rAsm cw).realizes r' q ∧ w = PCA.pairEl r r'
  ends := ⟨PCA.i A, by
    rintro a x y ⟨-, r, r', hr, hr', rfl⟩
    exact ⟨_, by rw [PCA.i_app]; exact Part.mem_some _, r, r', hr, hr', rfl⟩⟩
  refl' := by
    obtain ⟨q, hq⟩ := exists_dup (A := A)
    exact ⟨q, fun a x hx => ⟨_, hq a, ⟨rfl, rfl, rfl⟩, a, a, hx, hx, rfl⟩⟩
  symm' := by
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.sndComb A) (PCA.fstComb A)
    refine ⟨q, ?_⟩
    rintro a x y ⟨⟨hi, hs, ht⟩, r, r', hr, hr', rfl⟩
    exact ⟨_, hq _ r' r (mem_sndComb r r') (mem_fstComb r r'),
      ⟨hi.symm, hs.symm, ht.symm⟩, r', r, hr', hr, rfl⟩
  trans' := by
    obtain ⟨t, ht⟩ := exists_fstSndPair (A := A)
    refine ⟨t, ?_⟩
    rintro a b x y z ⟨⟨hi, hs, htg⟩, r, r', hr, hr', rfl⟩ ⟨⟨hi₂, hs₂, htg₂⟩, u, u', hu, hu', rfl⟩
    exact ⟨_, ht _ _ r u' (mem_fstComb r r') (mem_sndComb u u'),
      ⟨hi.trans hi₂, hs.trans hs₂, htg.trans htg₂⟩, r, u', hr, hu', rfl⟩

/-! ### The two legs -/

/-- The first endpoint. -/
def p1Pre (cw : A → Bool → A) : Pre (rERel cw) (xERel A) where
  toFun p := (p.idx, p.src)
  tracked := by
    refine ⟨PCA.comp (PCA.fstComb A) (PCA.fstComb A), ?_⟩
    rintro a x y ⟨⟨hi, hs, -⟩, r, r', ⟨g, -, rfl⟩, hr', rfl⟩
    exact ⟨_, mem_comp (mem_fstComb _ r') (mem_fstComb x.idx g), rfl, by
      rw [hi, hs]⟩

/-- The second endpoint. -/
def p2Pre (cw : A → Bool → A) : Pre (rERel cw) (xERel A) where
  toFun p := (p.idx, p.tgt)
  tracked := by
    refine ⟨PCA.comp (PCA.fstComb A) (PCA.fstComb A), ?_⟩
    rintro a x y ⟨⟨hi, -, ht⟩, r, r', ⟨g, -, rfl⟩, hr', rfl⟩
    exact ⟨_, mem_comp (mem_fstComb _ r') (mem_fstComb x.idx g), rfl, by
      rw [hi, ht]⟩

/-- The first leg of the relation. -/
noncomputable def p₁ (cw : A → Bool → A) : rERel cw ⟶ xERel A := homOf (p1Pre cw)

/-- The second leg of the relation. -/
noncomputable def p₂ (cw : A → Bool → A) : rERel cw ⟶ xERel A := homOf (p2Pre cw)

/-! ### The pair is an internal equivalence relation -/

/-- A homotopy into `X` is an equality of the underlying functions: `X` carries equality. -/
theorem eq_of_homotopic_x {T : ERel.{u, u} A} {f g : Pre T (xERel A)} (h : Homotopic f g)
    (x : T.base.carrier) : f.toFun x = g.toFun x := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, ha⟩ := T.base.exists_realizer x
  obtain ⟨v, -, -, he⟩ := ht a x ha
  exact he

/-- **The two legs are jointly monic.** -/
theorem jointly_mono (cw : A → Bool → A) {T : ERel.{u, u} A} (f g : T ⟶ rERel cw)
    (h₁ : f ≫ p₁ cw = g ≫ p₁ cw) (h₂ : f ≫ p₂ cw = g ≫ p₂ cw) : f = g := by
  obtain ⟨F, rfl⟩ := homOf_surjective f
  obtain ⟨G, rfl⟩ := homOf_surjective g
  rw [p₁, homOf_comp, homOf_comp, homOf_eq_iff] at h₁
  rw [p₂, homOf_comp, homOf_comp, homOf_eq_iff] at h₂
  have hfst : ∀ x, ((F.toFun x).idx, (F.toFun x).src) = ((G.toFun x).idx, (G.toFun x).src) :=
    fun x => eq_of_homotopic_x h₁ x
  have hsnd : ∀ x, ((F.toFun x).idx, (F.toFun x).tgt) = ((G.toFun x).idx, (G.toFun x).tgt) :=
    fun x => eq_of_homotopic_x h₂ x
  obtain ⟨rF, hrF⟩ := F.trackedBase
  obtain ⟨rG, hrG⟩ := G.trackedBase
  obtain ⟨q, hq⟩ := exists_pairOf rF rG
  refine homOf_eq_iff.2 ⟨q, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := hrF a x ha
  obtain ⟨w, hw, hwx⟩ := hrG a x ha
  refine ⟨_, hq a u w hu hw, ⟨?_, ?_, ?_⟩, u, w, hux, hwx, rfl⟩
  · exact congrArg Prod.fst (hfst x)
  · exact congrArg Prod.snd (hfst x)
  · exact congrArg Prod.snd (hsnd x)

/-- The diagonal: the point of `R` with the identity label. -/
def deltaPre (cw : A → Bool → A) : Pre (xERel A) (rERel cw) where
  toFun x := ⟨x.1, x.2, x.2, Label.idL, Or.inl ⟨rfl, rfl⟩⟩
  tracked := by
    obtain ⟨qp, hqp⟩ := exists_pairRight (PCA.i A)
    obtain ⟨qd, hqd⟩ := exists_dup (A := A)
    refine ⟨PCA.comp qd qp, ?_⟩
    rintro a x y ⟨rfl, rfl⟩
    exact ⟨_, mem_comp (hqp x.1) (hqd (PCA.pairEl x.1 (PCA.i A))), ⟨rfl, rfl, rfl⟩,
      _, _, ⟨PCA.i A, Label.computes_idL, rfl⟩, ⟨PCA.i A, Label.computes_idL, rfl⟩, rfl⟩

/-- The swap: the same point with its endpoints exchanged. -/
def sigmaPre (cw : A → Bool → A) : Pre (rERel cw) (rERel cw) where
  toFun p := ⟨p.idx, p.tgt, p.src, p.lab, by
    rcases p.valid with ⟨h₁, h₂⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨h₁, h₂.symm⟩
    · exact Or.inr ⟨j, hj⟩⟩
  tracked := by
    refine ⟨PCA.i A, ?_⟩
    rintro a x y ⟨⟨hi, hs, ht⟩, r, r', hr, hr', rfl⟩
    exact ⟨_, by rw [PCA.i_app]; exact Part.mem_some _, ⟨hi, ht, hs⟩, r, r', hr, hr', rfl⟩

/-- The composite of two points of `R` with matching middle endpoints: the labels compose. -/
def transPre (cw : A → Bool → A) {T : ERel.{u, u} A} (F G : Pre T (rERel cw))
    (hmid : ∀ x : T.base.carrier, (F.toFun x).idx = (G.toFun x).idx ∧
      (F.toFun x).tgt = (G.toFun x).src) : Pre T (rERel cw) where
  toFun x :=
    { idx := (F.toFun x).idx
      src := (F.toFun x).src
      tgt := (G.toFun x).tgt
      lab := (F.toFun x).lab.comp (G.toFun x).lab
      valid := by
        rcases (F.toFun x).valid with ⟨hF₁, hF₂⟩ | ⟨j, hj⟩
        · rcases (G.toFun x).valid with ⟨hG₁, hG₂⟩ | ⟨j, hj⟩
          · refine Or.inl ⟨by rw [hF₁, hG₁]; rfl, ?_⟩
            rw [hF₂, (hmid x).2, hG₂]
          · exact Or.inr ⟨j, by rw [hF₁, hj, (hmid x).1]; rfl⟩
        · exact Or.inr ⟨j, by rw [hj]; rfl⟩ }
  tracked := by
    obtain ⟨rF, hrF⟩ := F.trackedBase
    obtain ⟨rG, hrG⟩ := G.trackedBase
    obtain ⟨q, hq⟩ := exists_transComb rF rG
    obtain ⟨pf, hpf⟩ := T.exists_fstTracker
    obtain ⟨ps, hps⟩ := T.exists_sndTracker
    obtain ⟨cF, hcF⟩ := F.tracked
    obtain ⟨cG, hcG⟩ := G.tracked
    obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.comp q pf) (PCA.comp q ps)
    -- from a realizer of a point, a realizer of its composite
    have key : ∀ (a : A) (x : T.base.carrier), T.base.realizes a x →
        ∃ v ∈ PCA.app q a, (rAsm cw).realizes v
          { idx := (F.toFun x).idx, src := (F.toFun x).src, tgt := (G.toFun x).tgt,
            lab := (F.toFun x).lab.comp (G.toFun x).lab,
            valid := by
              rcases (F.toFun x).valid with ⟨hF₁, hF₂⟩ | ⟨j, hj⟩
              · rcases (G.toFun x).valid with ⟨hG₁, hG₂⟩ | ⟨j, hj⟩
                · refine Or.inl ⟨by rw [hF₁, hG₁]; rfl, ?_⟩
                  rw [hF₂, (hmid x).2, hG₂]
                · exact Or.inr ⟨j, by rw [hF₁, hj, (hmid x).1]; rfl⟩
              · exact Or.inr ⟨j, by rw [hj]; rfl⟩ } := by
      intro a x ha
      obtain ⟨u, hu, gF, hgF, rfl⟩ := hrF a x ha
      obtain ⟨w, hw, gG, hgG, hwe⟩ := hrG a x ha
      rw [← (hmid x).1] at hwe
      subst hwe
      obtain ⟨b, hb, hbl⟩ := hq a (F.toFun x).idx gF gG hu hw
      exact ⟨_, hb, b, hbl _ _ hgF hgG, rfl⟩
    refine ⟨qq, ?_⟩
    intro a x y hxy
    obtain ⟨vF, -, hvF⟩ := hcF a x y hxy
    obtain ⟨vG, -, hvG⟩ := hcG a x y hxy
    obtain ⟨ax, hax, haxr⟩ := hpf a x y hxy
    obtain ⟨ay, hay, hayr⟩ := hps a x y hxy
    obtain ⟨vx, hvx, hvxr⟩ := key ax x haxr
    obtain ⟨vy, hvy, hvyr⟩ := key ay y hayr
    refine ⟨_, hqq a vx vy (mem_comp hax hvx) (mem_comp hay hvy), ⟨?_, ?_, ?_⟩,
      vx, vy, hvxr, hvyr, rfl⟩
    · exact hvF.1.1
    · exact hvF.1.2.1
    · exact hvG.1.2.2

/-- **The two legs form an internal equivalence relation.** -/
theorem isInternalEquiv_p (cw : A → Bool → A) : IsInternalEquiv (p₁ cw) (p₂ cw) where
  jointly_mono f g h₁ h₂ := jointly_mono cw f g h₁ h₂
  refl' := by
    refine ⟨homOf (deltaPre cw), ?_, ?_⟩
    · rw [p₁, homOf_comp, id_eq]
      exact congrArg homMk (Pre.ext rfl)
    · rw [p₂, homOf_comp, id_eq]
      exact congrArg homMk (Pre.ext rfl)
  symm' := by
    refine ⟨homOf (sigmaPre cw), ?_, ?_⟩
    · rw [p₁, p₂, homOf_comp]
      exact congrArg homMk (Pre.ext rfl)
    · rw [p₁, p₂, homOf_comp]
      exact congrArg homMk (Pre.ext rfl)
  trans' {T} f g hfg := by
    obtain ⟨F, rfl⟩ := homOf_surjective f
    obtain ⟨G, rfl⟩ := homOf_surjective g
    rw [p₁, p₂, homOf_comp, homOf_comp, homOf_eq_iff] at hfg
    have hmid : ∀ x : T.base.carrier, (F.toFun x).idx = (G.toFun x).idx ∧
        (F.toFun x).tgt = (G.toFun x).src := by
      intro x
      have := eq_of_homotopic_x hfg x
      exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
    refine ⟨homOf (transPre cw F G hmid), ?_, ?_⟩
    · rw [p₁, homOf_comp, homOf_comp]
      exact congrArg homMk (Pre.ext rfl)
    · rw [p₂, homOf_comp, homOf_comp]
      refine congrArg homMk (Pre.ext (funext fun x => ?_))
      change ((F.toFun x).idx, (G.toFun x).tgt) = ((G.toFun x).idx, (G.toFun x).tgt)
      rw [(hmid x).1]

/-! ### The witnesses and the blocking property -/

/-- The partial function that a candidate normalizer `t` induces on witnesses: feed `t` the
realizer of a cross point whose label is the constant `c`, read off the second component of the
result, and evaluate it. -/
noncomputable def Psi (t c : A) : Part A :=
  (Part.some (PCA.sndComb A) ⬝ (Part.some t ⬝ Part.some (PCA.pairEl t (constEl c)))) ⬝ Part.some t

/-- A family of witnesses **blocks** every element of the algebra: at the index `t`, the element
`t` does not map both witnesses to a single one of them. -/
def Blocking (cw : A → Bool → A) : Prop :=
  ∀ t : A, ¬ ∃ u : Bool, ∀ j : Bool, cw t u ∈ Psi t (cw t j)

/-- **A blocking family exists** as soon as the algebra has three distinct elements. -/
theorem exists_blocking {x y z : A} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ∃ cw : A → Bool → A, Blocking cw := by
  choose cw hcw using fun t : A => exists_pair_not_normalized (Psi t) hxy hyz hxz
  exact ⟨cw, hcw⟩

/-! ### The test object -/

/-- The cross point of `R` over the two points of index `s`, with the `j`-th witness. -/
def crossPt (cw : A → Bool → A) (s : A) (j : Bool) : RPt cw :=
  ⟨s, false, true, Label.constL (cw s j), Or.inr ⟨j, rfl⟩⟩

/-- The base of the test object: one point per element of the algebra, realized by the realizers
of the cross points over it. -/
def bAsm (cw : A → Bool → A) : Assembly.{u, u} A where
  carrier := A
  realizes r s := ∃ (j : Bool) (g : A), (Label.constL (cw s j)).Computes g ∧ r = PCA.pairEl s g
  exists_realizer s := ⟨_, false, constEl (cw s false), Label.computes_constL _, rfl⟩

/-- The test object. -/
def tERel (cw : A → Bool → A) : ERel.{u, u} A := eqERel (bAsm cw)

/-- The base of the cover of the test object: the cross points themselves. -/
def b'Asm (cw : A → Bool → A) : Assembly.{u, u} A where
  carrier := A × Bool
  realizes r p := ∃ g : A, (Label.constL (cw p.1 p.2)).Computes g ∧ r = PCA.pairEl p.1 g
  exists_realizer p := ⟨_, constEl (cw p.1 p.2), Label.computes_constL _, rfl⟩

/-- The cover of the test object. -/
def t'ERel (cw : A → Bool → A) : ERel.{u, u} A := eqERel (b'Asm cw)

/-- The cover, which forgets the witness. -/
def piPre (cw : A → Bool → A) : Pre (t'ERel cw) (tERel cw) where
  toFun p := p.1
  tracked := by
    refine ⟨PCA.i A, ?_⟩
    rintro a x y ⟨⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, by rw [PCA.i_app]; exact Part.mem_some _, ⟨x.2, g, hg, rfl⟩, rfl⟩

/-- The cross points, as a morphism into `R`. -/
def nPre (cw : A → Bool → A) : Pre (t'ERel cw) (rERel cw) where
  toFun p := crossPt cw p.1 p.2
  tracked := by
    obtain ⟨qd, hqd⟩ := exists_dup (A := A)
    refine ⟨qd, ?_⟩
    rintro a x y ⟨⟨g, hg, rfl⟩, rfl⟩
    exact ⟨_, hqd _, ⟨rfl, rfl, rfl⟩, _, _, ⟨g, hg, rfl⟩, ⟨g, hg, rfl⟩, rfl⟩

/-- The first of the two maps of the test object into `X`. -/
def aPre (cw : A → Bool → A) : Pre (tERel cw) (xERel A) where
  toFun s := (s, false)
  tracked := by
    refine ⟨PCA.fstComb A, ?_⟩
    rintro a x y ⟨⟨j, g, hg, rfl⟩, rfl⟩
    exact ⟨_, mem_fstComb (A := A) x g, rfl, rfl⟩

/-- The second of the two maps of the test object into `X`. -/
def bPre (cw : A → Bool → A) : Pre (tERel cw) (xERel A) where
  toFun s := (s, true)
  tracked := by
    refine ⟨PCA.fstComb A, ?_⟩
    rintro a x y ⟨⟨j, g, hg, rfl⟩, rfl⟩
    exact ⟨_, mem_fstComb (A := A) x g, rfl, rfl⟩

/-- **The cover of the test object is an epimorphism**: the two objects have the same realizers,
so a homotopy out of the cover is a homotopy out of the test object. -/
instance epi_piPre (cw : A → Bool → A) : Epi (homOf (piPre cw)) where
  left_cancellation {W} f g h := by
    obtain ⟨F, rfl⟩ := homOf_surjective f
    obtain ⟨G, rfl⟩ := homOf_surjective g
    rw [homOf_comp, homOf_comp, homOf_eq_iff] at h
    obtain ⟨t, ht⟩ := h
    refine homOf_eq_iff.2 ⟨t, fun a s ha => ?_⟩
    obtain ⟨j, g, hg, rfl⟩ := ha
    exact ht _ (s, j) ⟨g, hg, rfl⟩

/-! ### The relation is not a kernel pair -/

/-- **The internal equivalence relation is not the kernel pair of any morphism.**  A morphism out
of the test object into `R` would have to choose one of the two cross points over each index and
to compute a realizer of the chosen one from a realizer of either, which is exactly what the
blocking property forbids. -/
theorem not_isKernelPair (cw : A → Bool → A) (hcw : Blocking cw) :
    ¬ ∃ (Z : ERel.{u, u} A) (k : xERel A ⟶ Z), IsKernelPair k (p₁ cw) (p₂ cw) := by
  rintro ⟨Z, k, hk⟩
  -- the two maps of the test object into `X` are equalized by `k`
  have hn₁ : homOf (nPre cw) ≫ p₁ cw = homOf (piPre cw) ≫ homOf (aPre cw) := by
    rw [p₁, homOf_comp, homOf_comp]
    exact congrArg homMk (Pre.ext rfl)
  have hn₂ : homOf (nPre cw) ≫ p₂ cw = homOf (piPre cw) ≫ homOf (bPre cw) := by
    rw [p₂, homOf_comp, homOf_comp]
    exact congrArg homMk (Pre.ext rfl)
  have hcomm : homOf (piPre cw) ≫ (homOf (aPre cw) ≫ k)
      = homOf (piPre cw) ≫ (homOf (bPre cw) ≫ k) := by
    rw [← Category.assoc, ← Category.assoc, ← hn₁, ← hn₂, Category.assoc, Category.assoc, hk.w]
  have habk : homOf (aPre cw) ≫ k = homOf (bPre cw) ≫ k := (cancel_epi _).1 hcomm
  obtain ⟨m, hm₁, hm₂⟩ := hk.lift' (homOf (aPre cw)) (homOf (bPre cw)) habk
  obtain ⟨M, rfl⟩ := homOf_surjective m
  rw [p₁, homOf_comp, homOf_eq_iff] at hm₁
  rw [p₂, homOf_comp, homOf_eq_iff] at hm₂
  -- the value of `M` at `s` is a cross point over the index `s`
  have hidx : ∀ s : A, (M.toFun s).idx = s ∧ (M.toFun s).src = false ∧ (M.toFun s).tgt = true := by
    intro s
    have h₁ := eq_of_homotopic_x hm₁ s
    have h₂ := eq_of_homotopic_x hm₂ s
    exact ⟨congrArg Prod.fst h₁, congrArg Prod.snd h₁, congrArg Prod.snd h₂⟩
  have hlab : ∀ s : A, ∃ u : Bool, (M.toFun s).lab = Label.constL (cw s u) := by
    intro s
    rcases (M.toFun s).valid with ⟨-, h⟩ | ⟨u, hu⟩
    · rw [(hidx s).2.1, (hidx s).2.2] at h
      exact absurd h (by simp)
    · exact ⟨u, by rw [hu, (hidx s).1]⟩
  -- its realizer is computed from any realizer of `s`
  obtain ⟨t, ht⟩ := M.trackedBase
  obtain ⟨u, hu⟩ := hlab t
  refine hcw t ⟨u, fun j => ?_⟩
  obtain ⟨v, hv, g, hg, hve⟩ :=
    ht (PCA.pairEl t (constEl (cw t j))) t ⟨j, constEl (cw t j), Label.computes_constL _, rfl⟩
  rw [(hidx t).1] at hve
  rw [hu] at hg
  have hvt : PCA.pairEl t g ∈ Part.some t ⬝ Part.some (PCA.pairEl t (constEl (cw t j))) := by
    rw [papp_some_some, ← hve]; exact hv
  have hgm : g ∈ Part.some (PCA.sndComb A) ⬝
      (Part.some t ⬝ Part.some (PCA.pairEl t (constEl (cw t j)))) :=
    mem_papp (Part.mem_some _) hvt (mem_sndComb t g)
  exact mem_papp hgm (Part.mem_some _) (hg t)

/-! ### The conclusion -/

/-- **The exact completion of the assemblies over a partial combinatory algebra with three
distinct elements is not exact**: it carries an internal equivalence relation which is not the
kernel pair of any morphism, hence not the kernel pair of its coequalizer. -/
theorem exists_internalEquiv_not_kernelPair {x y z : A} (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : x ≠ z) : ∃ (R X : ERel.{u, u} A) (q₁ q₂ : R ⟶ X), IsInternalEquiv q₁ q₂ ∧
      ¬ ∃ (Z : ERel.{u, u} A) (k : X ⟶ Z), IsKernelPair k q₁ q₂ := by
  obtain ⟨cw, hcw⟩ := exists_blocking hxy hyz hxz
  exact ⟨rERel cw, xERel A, p₁ cw, p₂ cw, isInternalEquiv_p cw, not_isKernelPair cw hcw⟩

open scoped Kleene in
/-- **The exact completion of the assemblies over Kleene's first algebra is not exact.** -/
theorem kleene_exReg_not_exact :
    ∃ (R X : ERel.{0, 0} ℕ) (q₁ q₂ : R ⟶ X), IsInternalEquiv q₁ q₂ ∧
      ¬ ∃ (Z : ERel.{0, 0} ℕ) (k : X ⟶ Z), IsKernelPair k q₁ q₂ :=
  exists_internalEquiv_not_kernelPair (x := 0) (y := 1) (z := 2) (by decide) (by decide)
    (by decide)

end NotExact

end ExReg

end Realizability
