/-
**The exact completion of the assemblies: pseudo-equivalence relations and tracked maps up to
homotopy.**

The effective topos is the exact completion of the regular category of assemblies.  This module
builds the underlying category of that completion and the embedding of the assemblies into it.

An object is an assembly `X` together with a *pseudo-equivalence relation* on it presented
computationally: a family `Prf a x y` of "proofs that `x` is related to `y`, realized by `a`",
closed under reflexivity, symmetry and transitivity *uniformly* — each closure property is
witnessed by an element of the algebra — and whose two endpoints are computable from a proof
(`ends`).  Such a datum is exactly a subobject of `X × X` in `Asm(A)` which is an internal
equivalence relation: the assembly of proofs has the pairs of related points as its underlying
set, but its own realizability relation, in general finer than the one inherited from `X × X`.

A morphism is a function on the underlying sets that carries related points to related points,
uniformly (a single element of the algebra turns a proof of `x ~ y` into a proof of
`f x ~ f y`); two such are identified when they are *homotopic*, i.e. when a single element of the
algebra turns a realizer of `x` into a proof of `f x ~ g x`.

Main definitions and results:

* `Realizability.ExReg.ERel` — pseudo-equivalence relations over the assemblies;
* `Realizability.ExReg.Pre`, `.Homotopic`, `.Hom` — tracked maps, homotopy, and the hom-sets of
  the completion as their quotient; `Realizability.ExReg.instCategory`;
* `Realizability.ExReg.eqERel` — an assembly with equality, and
  `Realizability.ExReg.emb` — the resulting embedding `Asm(A) ⥤ ExReg(A)`;
* `Realizability.ExReg.instFullEmb`, `.instFaithfulEmb` — **the embedding is full and
  faithful**;
* `Realizability.ExReg.isTerminalTerm` — the completion has a terminal object;
* `Realizability.ExReg.epi_quot` — **every object of the completion is covered by an assembly**:
  the canonical map from `emb X` to a pseudo-equivalence relation on `X` is an epimorphism.

What is *not* here: regularity and exactness of the completion, its universal property, and the
identification of the result with the effective topos.  The last one also needs the bases to be
restricted to the regular projectives of `Asm(A)` — the partitioned assemblies of
`Start/AssemblyProjective.lean` — for which the ex/reg and ex/lex completions agree.
-/

import Start.AssemblyRegular

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory

namespace ExReg

variable {A : Type u} [PCA A]

/-! ### Two combinators -/

/-- Composition of trackers: `comp s r` sends `a` to `s (r a)`. -/
theorem mem_comp {r s a u w : A} (hu : u ∈ PCA.app r a) (hw : w ∈ PCA.app s u) :
    w ∈ PCA.app (PCA.comp s r) a := by
  have h0 : w ∈ Part.some s ⬝ (Part.some r ⬝ Part.some a) := by
    rw [papp_some_some, papp_some_left]
    exact Part.mem_bind_iff.2 ⟨u, hu, hw⟩
  have := PCA.comp_app s r a w h0
  rwa [papp_some_some] at this

/-- The combinator `λa. t (r a) (s a)`, which turns a binary tracker `t` and two unary trackers
`r`, `s` into a single unary tracker. -/
theorem exists_pairApply (t r s : A) : ∃ q : A, ∀ a u w v : A, u ∈ PCA.app r a →
    w ∈ PCA.app s a → v ∈ (Part.some t ⬝ Part.some u) ⬝ Part.some w → v ∈ PCA.app q a := by
  refine ⟨PCA.lam 0 (Expr.app (Expr.app (Expr.const t) (Expr.app (Expr.const r) (Expr.var 0)))
    (Expr.app (Expr.const s) (Expr.var 0))) (PCA.env0 A), fun a u w v hu hw hv => ?_⟩
  have hle := PCA.lam_app 0 (Expr.app (Expr.app (Expr.const t)
    (Expr.app (Expr.const r) (Expr.var 0))) (Expr.app (Expr.const s) (Expr.var 0)))
    (PCA.env0 A) a
  refine hle _ ?_
  have hu' : Part.some u ≤ Part.some r ⬝ Part.some a := by
    rw [papp_some_some]; exact some_le_of_mem hu
  have hw' : Part.some w ≤ Part.some s ⬝ Part.some a := by
    rw [papp_some_some]; exact some_le_of_mem hw
  have hmono : (Part.some t ⬝ Part.some u) ⬝ Part.some w
      ≤ (Part.some t ⬝ (Part.some r ⬝ Part.some a)) ⬝ (Part.some s ⬝ Part.some a) :=
    papp_mono (papp_mono le_rfl hu') hw'
  simpa [Expr.eval] using hmono _ hv

/-- The combinator `λa. pair a a`. -/
theorem exists_dup : ∃ q : A, ∀ a : A, PCA.pairEl a a ∈ PCA.app q a := by
  obtain ⟨q, hq⟩ := exists_pairApply (PCA.pairComb A) (PCA.i A) (PCA.i A)
  refine ⟨q, fun a => hq a a a _ ?_ ?_ ?_⟩
  · rw [PCA.i_app]; exact Part.mem_some _
  · rw [PCA.i_app]; exact Part.mem_some _
  · rw [PCA.pairComb_app]; exact Part.mem_some _

/-! ### Pseudo-equivalence relations -/

/-- A **pseudo-equivalence relation** over the assemblies: an assembly `base`, a family of
realized proofs `Prf a x y` whose endpoints are computable from the proof, closed under
reflexivity, symmetry and transitivity uniformly in the algebra. -/
structure ERel (A : Type u) [PCA A] where
  /-- The assembly the relation lives on. -/
  base : Assembly.{u, v} A
  /-- `Prf a x y` reads "`a` realizes a proof that `x` is related to `y`". -/
  Prf : A → base.carrier → base.carrier → Prop
  /-- The two endpoints of a proof are computable from it: the relation is a subobject of
  `base × base`. -/
  ends : ∃ t : A, ∀ (a : A) (x y : base.carrier), Prf a x y →
    ∃ v ∈ PCA.app t a, ∃ b c : A, base.realizes b x ∧ base.realizes c y ∧ v = PCA.pairEl b c
  /-- Reflexivity, uniformly. -/
  refl' : ∃ r : A, ∀ (a : A) (x : base.carrier), base.realizes a x → ∃ v ∈ PCA.app r a, Prf v x x
  /-- Symmetry, uniformly. -/
  symm' : ∃ s : A, ∀ (a : A) (x y : base.carrier), Prf a x y → ∃ v ∈ PCA.app s a, Prf v y x
  /-- Transitivity, uniformly, by a binary tracker. -/
  trans' : ∃ t : A, ∀ (a b : A) (x y z : base.carrier), Prf a x y → Prf b y z →
    ∃ v ∈ (Part.some t ⬝ Part.some a) ⬝ Part.some b, Prf v x z

namespace ERel

variable (E : ERel.{u, v} A)

/-- The relation underlying a pseudo-equivalence relation: `x` and `y` are related when some
element of the algebra realizes a proof that they are. -/
def rel (x y : E.base.carrier) : Prop := ∃ a, E.Prf a x y

theorem rel_refl (x : E.base.carrier) : E.rel x x := by
  obtain ⟨r, hr⟩ := E.refl'
  obtain ⟨a, ha⟩ := E.base.exists_realizer x
  obtain ⟨v, _, hv⟩ := hr a x ha
  exact ⟨v, hv⟩

theorem rel_symm {x y : E.base.carrier} (h : E.rel x y) : E.rel y x := by
  obtain ⟨s, hs⟩ := E.symm'
  obtain ⟨a, ha⟩ := h
  obtain ⟨v, _, hv⟩ := hs a x y ha
  exact ⟨v, hv⟩

theorem rel_trans {x y z : E.base.carrier} (h₁ : E.rel x y) (h₂ : E.rel y z) : E.rel x z := by
  obtain ⟨t, ht⟩ := E.trans'
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  obtain ⟨v, _, hv⟩ := ht a b x y z ha hb
  exact ⟨v, hv⟩

/-- The underlying relation is an equivalence relation. -/
theorem equivalence_rel : Equivalence E.rel :=
  ⟨E.rel_refl, E.rel_symm, E.rel_trans⟩

/-- From a proof one computes a realizer of its first endpoint. -/
theorem exists_fstTracker : ∃ p : A, ∀ (a : A) (x y : E.base.carrier), E.Prf a x y →
    ∃ v ∈ PCA.app p a, E.base.realizes v x := by
  obtain ⟨t, ht⟩ := E.ends
  refine ⟨PCA.comp (PCA.fstComb A) t, fun a x y h => ?_⟩
  obtain ⟨v, hv, b, c, hb, _, rfl⟩ := ht a x y h
  refine ⟨b, mem_comp hv ?_, hb⟩
  have := PCA.fstComb_pairEl (A := A) b c
  rw [papp_some_some] at this
  rw [this]
  exact Part.mem_some _

/-- From a proof one computes a realizer of its second endpoint. -/
theorem exists_sndTracker : ∃ p : A, ∀ (a : A) (x y : E.base.carrier), E.Prf a x y →
    ∃ v ∈ PCA.app p a, E.base.realizes v y := by
  obtain ⟨t, ht⟩ := E.ends
  refine ⟨PCA.comp (PCA.sndComb A) t, fun a x y h => ?_⟩
  obtain ⟨v, hv, b, c, _, hc, rfl⟩ := ht a x y h
  refine ⟨c, mem_comp hv ?_, hc⟩
  have := PCA.sndComb_pairEl (A := A) b c
  rw [papp_some_some] at this
  rw [this]
  exact Part.mem_some _

end ERel

/-! ### An assembly with equality -/

/-- An assembly, seen as a pseudo-equivalence relation: the relation is equality, a proof that
`x = y` being a realizer of `x`. -/
def eqERel (X : Assembly.{u, v} A) : ERel.{u, v} A where
  base := X
  Prf a x y := X.realizes a x ∧ x = y
  ends := by
    obtain ⟨q, hq⟩ := exists_dup (A := A)
    refine ⟨q, fun a x y h => ⟨PCA.pairEl a a, hq a, a, a, h.1, ?_, rfl⟩⟩
    exact h.2 ▸ h.1
  refl' := ⟨PCA.i A, fun a x ha => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, ha, rfl⟩⟩
  symm' := ⟨PCA.i A, fun a x y h => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _,
    h.2 ▸ h.1, h.2.symm⟩⟩
  trans' := ⟨PCA.k, fun a b x y z h₁ h₂ => ⟨a, by rw [k_papp]; exact Part.mem_some _,
    h₁.1, h₁.2.trans h₂.2⟩⟩

@[simp] theorem eqERel_base (X : Assembly.{u, v} A) : (eqERel X).base = X := rfl

/-! ### Morphisms -/

/-- A **pre-morphism** of pseudo-equivalence relations: a function on the underlying sets, with
an element of the algebra turning a proof that `x` is related to `y` into a proof that `f x` is
related to `f y`. -/
structure Pre (E F : ERel.{u, v} A) where
  /-- The underlying function. -/
  toFun : E.base.carrier → F.base.carrier
  /-- Some element of the algebra transports proofs along `toFun`. -/
  tracked : ∃ c : A, ∀ (a : A) (x y : E.base.carrier), E.Prf a x y →
    ∃ v ∈ PCA.app c a, F.Prf v (toFun x) (toFun y)

namespace Pre

variable {E F G : ERel.{u, v} A}

@[ext] theorem ext {f g : Pre E F} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- A pre-morphism is in particular a morphism of assemblies on the bases: apply reflexivity,
transport the proof, and read off its first endpoint. -/
theorem trackedBase (f : Pre E F) : Assembly.Tracked E.base F.base f.toFun := by
  obtain ⟨c, hc⟩ := f.tracked
  obtain ⟨r, hr⟩ := E.refl'
  obtain ⟨p, hp⟩ := F.exists_fstTracker
  refine ⟨PCA.comp p (PCA.comp c r), fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := hr a x ha
  obtain ⟨w, hw, hwx⟩ := hc u x x hux
  obtain ⟨z, hz, hzx⟩ := hp w (f.toFun x) (f.toFun x) hwx
  exact ⟨z, mem_comp (mem_comp hu hw) hz, hzx⟩

/-- The identity pre-morphism. -/
noncomputable def id (E : ERel.{u, v} A) : Pre E E where
  toFun := _root_.id
  tracked := ⟨PCA.i A, fun a x y h => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, h⟩⟩

/-- Composition of pre-morphisms. -/
noncomputable def comp (f : Pre E F) (g : Pre F G) : Pre E G where
  toFun := g.toFun ∘ f.toFun
  tracked := by
    obtain ⟨c, hc⟩ := f.tracked
    obtain ⟨d, hd⟩ := g.tracked
    refine ⟨PCA.comp d c, fun a x y h => ?_⟩
    obtain ⟨u, hu, hux⟩ := hc a x y h
    obtain ⟨w, hw, hwx⟩ := hd u (f.toFun x) (f.toFun y) hux
    exact ⟨w, mem_comp hu hw, hwx⟩

@[simp] theorem id_toFun (E : ERel.{u, v} A) : (Pre.id E).toFun = _root_.id := rfl

@[simp] theorem comp_toFun (f : Pre E F) (g : Pre F G) :
    (f.comp g).toFun = g.toFun ∘ f.toFun := rfl

end Pre

/-! ### Homotopy -/

/-- Two pre-morphisms are **homotopic** when an element of the algebra turns a realizer of `x`
into a proof that `f x` and `g x` are related. -/
def Homotopic {E F : ERel.{u, v} A} (f g : Pre E F) : Prop :=
  ∃ h : A, ∀ (a : A) (x : E.base.carrier), E.base.realizes a x →
    ∃ v ∈ PCA.app h a, F.Prf v (f.toFun x) (g.toFun x)

namespace Homotopic

variable {E F G : ERel.{u, v} A}

@[refl] theorem refl (f : Pre E F) : Homotopic f f := by
  obtain ⟨c, hc⟩ := f.tracked
  obtain ⟨r, hr⟩ := E.refl'
  refine ⟨PCA.comp c r, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := hr a x ha
  obtain ⟨w, hw, hwx⟩ := hc u x x hux
  exact ⟨w, mem_comp hu hw, hwx⟩

theorem symm {f g : Pre E F} (h : Homotopic f g) : Homotopic g f := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨s, hs⟩ := F.symm'
  refine ⟨PCA.comp s t, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := ht a x ha
  obtain ⟨w, hw, hwx⟩ := hs u (f.toFun x) (g.toFun x) hux
  exact ⟨w, mem_comp hu hw, hwx⟩

theorem trans {f g k : Pre E F} (h₁ : Homotopic f g) (h₂ : Homotopic g k) : Homotopic f k := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  obtain ⟨t, ht⟩ := F.trans'
  obtain ⟨q, hq⟩ := exists_pairApply t t₁ t₂
  refine ⟨q, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := ht₁ a x ha
  obtain ⟨w, hw, hwx⟩ := ht₂ a x ha
  obtain ⟨z, hz, hzx⟩ := ht u w (f.toFun x) (g.toFun x) (k.toFun x) hux hwx
  exact ⟨z, hq a u w z hu hw hz, hzx⟩

/-- Homotopy is compatible with composition on the left. -/
theorem whiskerRight {f f' : Pre E F} (g : Pre F G) (h : Homotopic f f') :
    Homotopic (f.comp g) (f'.comp g) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨d, hd⟩ := g.tracked
  refine ⟨PCA.comp d t, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := ht a x ha
  obtain ⟨w, hw, hwx⟩ := hd u (f.toFun x) (f'.toFun x) hux
  exact ⟨w, mem_comp hu hw, hwx⟩

/-- Homotopy is compatible with composition on the right. -/
theorem whiskerLeft (f : Pre E F) {g g' : Pre F G} (h : Homotopic g g') :
    Homotopic (f.comp g) (f.comp g') := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨r, hr⟩ := f.trackedBase
  refine ⟨PCA.comp t r, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := hr a x ha
  obtain ⟨w, hw, hwx⟩ := ht u (f.toFun x) hux
  exact ⟨w, mem_comp hu hw, hwx⟩

end Homotopic

/-- Homotopy is an equivalence relation on pre-morphisms. -/
def homSetoid (E F : ERel.{u, v} A) : Setoid (Pre E F) where
  r := Homotopic
  iseqv := ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩

/-- The morphisms of the completion: pre-morphisms up to homotopy. -/
def Hom (E F : ERel.{u, v} A) : Type v := Quotient (homSetoid E F)

/-- The class of a pre-morphism. -/
def homMk {E F : ERel.{u, v} A} (f : Pre E F) : Hom E F := Quotient.mk _ f

theorem homMk_eq_iff {E F : ERel.{u, v} A} {f g : Pre E F} :
    homMk f = homMk g ↔ Homotopic f g :=
  Quotient.eq_iff_equiv

theorem homMk_surjective {E F : ERel.{u, v} A} (f : Hom E F) : ∃ p : Pre E F, homMk p = f :=
  Quotient.exists_rep f

/-! ### The category -/

noncomputable instance instCategoryStruct : CategoryStruct (ERel.{u, v} A) where
  Hom E F := Hom E F
  id E := homMk (Pre.id E)
  comp {_ _ _} f g := Quotient.liftOn₂ f g (fun p q => homMk (p.comp q))
    (fun _p q p' _q' hp hq =>
      homMk_eq_iff.2 ((Homotopic.whiskerRight q hp).trans (Homotopic.whiskerLeft p' hq)))

@[simp] theorem comp_homMk {E F G : ERel.{u, v} A} (f : Pre E F) (g : Pre F G) :
    (homMk f ≫ homMk g : E ⟶ G) = homMk (f.comp g) := rfl

theorem id_eq (E : ERel.{u, v} A) : (𝟙 E : E ⟶ E) = homMk (Pre.id E) := rfl

/-- The class of a pre-morphism, as a morphism of the completion. -/
abbrev homOf {E F : ERel.{u, v} A} (f : Pre E F) : E ⟶ F := homMk f

theorem homOf_eq_iff {E F : ERel.{u, v} A} {f g : Pre E F} :
    homOf f = homOf g ↔ Homotopic f g := homMk_eq_iff

theorem homOf_surjective {E F : ERel.{u, v} A} (f : E ⟶ F) : ∃ p : Pre E F, homOf p = f :=
  homMk_surjective f

@[simp] theorem homOf_comp {E F G : ERel.{u, v} A} (f : Pre E F) (g : Pre F G) :
    homOf f ≫ homOf g = homOf (f.comp g) := rfl

noncomputable instance instCategory : Category (ERel.{u, v} A) where
  id_comp f := Quotient.inductionOn f fun _ => rfl
  comp_id f := Quotient.inductionOn f fun _ => rfl
  assoc f g h := Quotient.inductionOn₃ f g h fun _ _ _ => rfl

/-! ### The embedding of the assemblies -/

/-- A morphism of assemblies as a pre-morphism between the corresponding equality relations. -/
noncomputable def embPre {X Y : Assembly.{u, v} A} (f : X ⟶ Y) : Pre (eqERel X) (eqERel Y) where
  toFun := f.toFun
  tracked := by
    obtain ⟨r, hr⟩ := f.tracked
    refine ⟨r, fun a x y h => ?_⟩
    obtain ⟨v, hv, hvx⟩ := hr a x h.1
    exact ⟨v, hv, hvx, congrArg f.toFun h.2⟩

/-- **The embedding of the assemblies into the completion**: an assembly with equality. -/
noncomputable def emb (A : Type u) [PCA A] : Assembly.{u, v} A ⥤ ERel.{u, v} A where
  obj X := eqERel X
  map f := homMk (embPre f)
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem emb_obj (X : Assembly.{u, v} A) : (emb A).obj X = eqERel X := rfl

@[simp] theorem emb_map {X Y : Assembly.{u, v} A} (f : X ⟶ Y) :
    (emb A).map f = homMk (embPre f) := rfl

/-- A pre-morphism between equality relations is a morphism of assemblies. -/
noncomputable def preToAsmHom {X Y : Assembly.{u, v} A} (p : Pre (eqERel X) (eqERel Y)) :
    X ⟶ Y where
  toFun := p.toFun
  tracked := by
    obtain ⟨c, hc⟩ := p.tracked
    refine ⟨c, fun a x ha => ?_⟩
    obtain ⟨v, hv, hvx, _⟩ := hc a x x ⟨ha, rfl⟩
    exact ⟨v, hv, hvx⟩

/-- **The embedding is full.** -/
instance instFullEmb : (emb.{u, v} A).Full where
  map_surjective {X Y} f := by
    obtain ⟨p, rfl⟩ := homMk_surjective f
    exact ⟨preToAsmHom p, congrArg homMk (Pre.ext rfl)⟩

/-- **The embedding is faithful**: homotopy between maps of assemblies with equality is
equality. -/
instance instFaithfulEmb : (emb.{u, v} A).Faithful where
  map_injective {X Y f g} h := by
    obtain ⟨t, ht⟩ := homMk_eq_iff.1 h
    refine Assembly.hom_ext fun x => ?_
    obtain ⟨a, ha⟩ := X.exists_realizer x
    obtain ⟨_, _, _, he⟩ := ht a x ha
    exact he

/-! ### The terminal object -/

/-- The terminal pseudo-equivalence relation: one point, everything a proof. -/
def termERel (A : Type u) [PCA A] : ERel.{u, v} A where
  base := Assembly.unitAsm A
  Prf _ _ _ := True
  ends := by
    obtain ⟨q, hq⟩ := exists_dup (A := A)
    exact ⟨q, fun a _ _ _ => ⟨PCA.pairEl a a, hq a, a, a, trivial, trivial, rfl⟩⟩
  refl' := ⟨PCA.i A, fun a _ _ => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, trivial⟩⟩
  symm' := ⟨PCA.i A, fun a _ _ _ => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, trivial⟩⟩
  trans' := ⟨PCA.k, fun a b _ _ _ _ _ => ⟨a, by rw [k_papp]; exact Part.mem_some _, trivial⟩⟩

/-- The unique map to the terminal object. -/
noncomputable def toTerm (E : ERel.{u, v} A) : E ⟶ termERel A :=
  homMk { toFun := fun _ => PUnit.unit
          tracked := ⟨PCA.k, fun a _ _ _ =>
            ⟨(PCA.app (PCA.k : A) a).get (PCA.k_dom a), Part.get_mem _, trivial⟩⟩ }

/-- **The completion has a terminal object.** -/
noncomputable def isTerminalTerm : Limits.IsTerminal (termERel.{u, v} A) :=
  Limits.IsTerminal.ofUniqueHom toTerm fun E f => by
    obtain ⟨p, rfl⟩ := homMk_surjective f
    exact (congrArg homMk (Pre.ext (funext fun _ => rfl))).symm

/-! ### Every object is covered by an assembly -/

/-- The canonical map from the base of a pseudo-equivalence relation, with equality, to the
relation itself: it is the identity on points, and turns a realizer into a proof by
reflexivity. -/
noncomputable def quotPre (E : ERel.{u, v} A) : Pre (eqERel E.base) E where
  toFun := _root_.id
  tracked := by
    obtain ⟨r, hr⟩ := E.refl'
    refine ⟨r, fun a x y h => ?_⟩
    obtain ⟨v, hv, hvx⟩ := hr a x h.1
    exact ⟨v, hv, h.2 ▸ hvx⟩

/-- The canonical cover of a pseudo-equivalence relation by its base. -/
noncomputable def quot (E : ERel.{u, v} A) : (emb A).obj E.base ⟶ E := homMk (quotPre E)

/-- **Every object of the completion is covered by an assembly**: the canonical map from the base
is an epimorphism, because a homotopy out of the base *is* a homotopy out of the relation. -/
instance epi_quot (E : ERel.{u, v} A) : Epi (quot E) where
  left_cancellation {G} f g h := by
    obtain ⟨p, rfl⟩ := homMk_surjective f
    obtain ⟨q, rfl⟩ := homMk_surjective g
    refine homMk_eq_iff.2 ?_
    obtain ⟨t, ht⟩ := homMk_eq_iff.1 h
    exact ⟨t, fun a x ha => ht a x ha⟩

end ExReg

end Realizability
