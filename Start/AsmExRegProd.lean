/-
**Finite products in the exact completion of the assemblies.**

`Start/AsmExReg.lean` builds the category of pseudo-equivalence relations over the assemblies and
its terminal object.  This module builds the binary products: the relation on the product of the
two bases whose proofs are the Church pairs of a proof on each side.  Every combinator needed is
assembled from the pairing combinator of the algebra — the endpoints of a pair of proofs, the
uniform reflexivity, symmetry and transitivity of the product relation, and the pairing of two
morphisms are all computed by pairing and projecting.

Main results:

* `Realizability.ExReg.prodERel` — the product of two pseudo-equivalence relations;
* `Realizability.ExReg.prodFanIsLimit` — **it is a binary product**, and the resulting
  `HasBinaryProducts` and `HasFiniteProducts` instances (the terminal object being
  `Realizability.ExReg.isTerminalTerm`);
* `Realizability.ExReg.embProdIso`, `.embTermIso` — **the embedding of the assemblies preserves
  the terminal object and binary products**: the product assembly, with equality, is the product
  of the two assemblies with equality.
-/

import Start.AsmExReg
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A]

/-! ### More combinators -/

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

/-- The combinator `λpq. pair (t₁ (fst p) (fst q)) (t₂ (snd p) (snd q))`: two binary trackers
run in parallel on Church pairs. -/
theorem exists_binPair (t₁ t₂ : A) : ∃ q : A, ∀ a b a' b' v w : A,
    v ∈ (Part.some t₁ ⬝ Part.some a) ⬝ Part.some a' →
    w ∈ (Part.some t₂ ⬝ Part.some b) ⬝ Part.some b' →
    PCA.pairEl v w ∈
      (Part.some q ⬝ Part.some (PCA.pairEl a b)) ⬝ Part.some (PCA.pairEl a' b') := by
  refine ⟨PCA.lam2 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
      (Expr.app (Expr.app (Expr.const t₁)
        (Expr.app (Expr.const (PCA.fstComb A)) (Expr.var 0)))
        (Expr.app (Expr.const (PCA.fstComb A)) (Expr.var 1))))
      (Expr.app (Expr.app (Expr.const t₂)
        (Expr.app (Expr.const (PCA.sndComb A)) (Expr.var 0)))
        (Expr.app (Expr.const (PCA.sndComb A)) (Expr.var 1)))),
    fun a b a' b' v w hv hw => ?_⟩
  refine PCA.lam2_app_app _ (PCA.pairEl a b) (PCA.pairEl a' b') _ ?_
  have e₁ : Part.some (PCA.fstComb A) ⬝ Part.some (PCA.pairEl a b) = Part.some a :=
    PCA.fstComb_pairEl a b
  have e₂ : Part.some (PCA.fstComb A) ⬝ Part.some (PCA.pairEl a' b') = Part.some a' :=
    PCA.fstComb_pairEl a' b'
  have e₃ : Part.some (PCA.sndComb A) ⬝ Part.some (PCA.pairEl a b) = Part.some b :=
    PCA.sndComb_pairEl a b
  have e₄ : Part.some (PCA.sndComb A) ⬝ Part.some (PCA.pairEl a' b') = Part.some b' :=
    PCA.sndComb_pairEl a' b'
  have hmono : (Part.some (PCA.pairComb A) ⬝ Part.some v) ⬝ Part.some w
      ≤ (Part.some (PCA.pairComb A) ⬝ ((Part.some t₁ ⬝ Part.some a) ⬝ Part.some a'))
        ⬝ ((Part.some t₂ ⬝ Part.some b) ⬝ Part.some b') :=
    papp_mono (papp_mono le_rfl (some_le_of_mem hv)) (some_le_of_mem hw)
  have hmem : PCA.pairEl v w ∈
      (Part.some (PCA.pairComb A) ⬝ ((Part.some t₁ ⬝ Part.some a) ⬝ Part.some a'))
        ⬝ ((Part.some t₂ ⬝ Part.some b) ⬝ Part.some b') := by
    refine hmono _ ?_
    rw [PCA.pairComb_app]
    exact Part.mem_some _
  simpa [Expr.eval, e₁, e₂, e₃, e₄, Function.update_of_ne] using hmem

/-! ### The product of two pseudo-equivalence relations -/

/-- The **product** of two pseudo-equivalence relations: the product of the bases, a proof being
the Church pair of a proof on each side. -/
def prodERel (E F : ERel.{u, v} A) : ERel.{u, v} A where
  base := Assembly.prodAsm E.base F.base
  Prf p x y := ∃ a b, E.Prf a x.1 y.1 ∧ F.Prf b x.2 y.2 ∧ p = PCA.pairEl a b
  ends := by
    obtain ⟨tE, htE⟩ := E.ends
    obtain ⟨tF, htF⟩ := F.ends
    obtain ⟨q₁, hq₁⟩ := exists_pairOf
      (PCA.comp (PCA.fstComb A) (PCA.comp tE (PCA.fstComb A)))
      (PCA.comp (PCA.fstComb A) (PCA.comp tF (PCA.sndComb A)))
    obtain ⟨q₂, hq₂⟩ := exists_pairOf
      (PCA.comp (PCA.sndComb A) (PCA.comp tE (PCA.fstComb A)))
      (PCA.comp (PCA.sndComb A) (PCA.comp tF (PCA.sndComb A)))
    obtain ⟨q, hq⟩ := exists_pairOf q₁ q₂
    refine ⟨q, fun p x y h => ?_⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := h
    obtain ⟨vE, hvE, e₁, e₂, he₁, he₂, rfl⟩ := htE a x.1 y.1 ha
    obtain ⟨vF, hvF, f₁, f₂, hf₁, hf₂, rfl⟩ := htF b x.2 y.2 hb
    have hE : PCA.pairEl e₁ e₂ ∈ PCA.app (PCA.comp tE (PCA.fstComb A)) (PCA.pairEl a b) :=
      mem_comp (mem_fstComb a b) hvE
    have hF : PCA.pairEl f₁ f₂ ∈ PCA.app (PCA.comp tF (PCA.sndComb A)) (PCA.pairEl a b) :=
      mem_comp (mem_sndComb a b) hvF
    refine ⟨PCA.pairEl (PCA.pairEl e₁ f₁) (PCA.pairEl e₂ f₂),
      hq _ _ _ (hq₁ _ _ _ (mem_comp hE (mem_fstComb e₁ e₂)) (mem_comp hF (mem_fstComb f₁ f₂)))
        (hq₂ _ _ _ (mem_comp hE (mem_sndComb e₁ e₂)) (mem_comp hF (mem_sndComb f₁ f₂))),
      PCA.pairEl e₁ f₁, PCA.pairEl e₂ f₂, ⟨e₁, f₁, he₁, hf₁, rfl⟩, ⟨e₂, f₂, he₂, hf₂, rfl⟩, rfl⟩
  refl' := by
    obtain ⟨rE, hrE⟩ := E.refl'
    obtain ⟨rF, hrF⟩ := F.refl'
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.comp rE (PCA.fstComb A))
      (PCA.comp rF (PCA.sndComb A))
    refine ⟨q, fun c x hc => ?_⟩
    obtain ⟨c₁, c₂, hc₁, hc₂, rfl⟩ := hc
    obtain ⟨u, hu, hux⟩ := hrE c₁ x.1 hc₁
    obtain ⟨w, hw, hwx⟩ := hrF c₂ x.2 hc₂
    exact ⟨PCA.pairEl u w,
      hq _ _ _ (mem_comp (mem_fstComb c₁ c₂) hu) (mem_comp (mem_sndComb c₁ c₂) hw),
      u, w, hux, hwx, rfl⟩
  symm' := by
    obtain ⟨sE, hsE⟩ := E.symm'
    obtain ⟨sF, hsF⟩ := F.symm'
    obtain ⟨q, hq⟩ := exists_pairOf (PCA.comp sE (PCA.fstComb A))
      (PCA.comp sF (PCA.sndComb A))
    refine ⟨q, fun p x y h => ?_⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := h
    obtain ⟨u, hu, hux⟩ := hsE a x.1 y.1 ha
    obtain ⟨w, hw, hwx⟩ := hsF b x.2 y.2 hb
    exact ⟨PCA.pairEl u w,
      hq _ _ _ (mem_comp (mem_fstComb a b) hu) (mem_comp (mem_sndComb a b) hw),
      u, w, hux, hwx, rfl⟩
  trans' := by
    obtain ⟨tE, htE⟩ := E.trans'
    obtain ⟨tF, htF⟩ := F.trans'
    obtain ⟨q, hq⟩ := exists_binPair tE tF
    refine ⟨q, fun p p' x y z hp hp' => ?_⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := hp
    obtain ⟨a', b', ha', hb', rfl⟩ := hp'
    obtain ⟨v, hv, hvx⟩ := htE a a' x.1 y.1 z.1 ha ha'
    obtain ⟨w, hw, hwx⟩ := htF b b' x.2 y.2 z.2 hb hb'
    exact ⟨PCA.pairEl v w, hq a b a' b' v w hv hw, v, w, hvx, hwx, rfl⟩

@[simp] theorem prodERel_base (E F : ERel.{u, v} A) :
    (prodERel E F).base = Assembly.prodAsm E.base F.base := rfl

/-! ### The projections and the pairing -/

variable {E F G : ERel.{u, v} A}

/-- The first projection, as a pre-morphism. -/
def prodFstPre (E F : ERel.{u, v} A) : Pre (prodERel E F) E where
  toFun := Prod.fst
  tracked := ⟨PCA.fstComb A, fun p x y h => by
    obtain ⟨a, b, ha, _, rfl⟩ := h
    exact ⟨a, mem_fstComb a b, ha⟩⟩

/-- The second projection, as a pre-morphism. -/
def prodSndPre (E F : ERel.{u, v} A) : Pre (prodERel E F) F where
  toFun := Prod.snd
  tracked := ⟨PCA.sndComb A, fun p x y h => by
    obtain ⟨a, b, _, hb, rfl⟩ := h
    exact ⟨b, mem_sndComb a b, hb⟩⟩

/-- The pairing of two pre-morphisms. -/
noncomputable def prodLiftPre (f : Pre G E) (g : Pre G F) : Pre G (prodERel E F) where
  toFun z := (f.toFun z, g.toFun z)
  tracked := by
    obtain ⟨c, hc⟩ := f.tracked
    obtain ⟨d, hd⟩ := g.tracked
    obtain ⟨q, hq⟩ := exists_pairOf c d
    refine ⟨q, fun a x y h => ?_⟩
    obtain ⟨u, hu, hux⟩ := hc a x y h
    obtain ⟨w, hw, hwx⟩ := hd a x y h
    exact ⟨PCA.pairEl u w, hq a u w hu hw, u, w, hux, hwx, rfl⟩

theorem prodLiftPre_homotopic {f f' : Pre G E} {g g' : Pre G F} (hf : Homotopic f f')
    (hg : Homotopic g g') : Homotopic (prodLiftPre f g) (prodLiftPre f' g') := by
  obtain ⟨t₁, ht₁⟩ := hf
  obtain ⟨t₂, ht₂⟩ := hg
  obtain ⟨q, hq⟩ := exists_pairOf t₁ t₂
  refine ⟨q, fun a x ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := ht₁ a x ha
  obtain ⟨w, hw, hwx⟩ := ht₂ a x ha
  exact ⟨PCA.pairEl u w, hq a u w hu hw, u, w, hux, hwx, rfl⟩

/-- The first projection. -/
def prodFst (E F : ERel.{u, v} A) : prodERel E F ⟶ E := homMk (prodFstPre E F)

/-- The second projection. -/
def prodSnd (E F : ERel.{u, v} A) : prodERel E F ⟶ F := homMk (prodSndPre E F)

/-- The pairing of two morphisms of the completion. -/
noncomputable def prodLift (f : G ⟶ E) (g : G ⟶ F) : G ⟶ prodERel E F :=
  Quotient.liftOn₂ f g (fun p q => homMk (prodLiftPre p q))
    (fun _ _ _ _ hp hq => homMk_eq_iff.2 (prodLiftPre_homotopic hp hq))

@[simp] theorem prodLift_homMk (f : Pre G E) (g : Pre G F) :
    prodLift (homMk f) (homMk g) = homMk (prodLiftPre f g) := rfl

/-- The binary fan given by the product relation. -/
noncomputable def prodFan (E F : ERel.{u, v} A) : BinaryFan E F :=
  BinaryFan.mk (prodFst E F) (prodSnd E F)

/-- **The product relation really is a binary product.** -/
noncomputable def prodFanIsLimit (E F : ERel.{u, v} A) : IsLimit (prodFan E F) :=
  BinaryFan.isLimitMk (fun s => prodLift (BinaryFan.fst s) (BinaryFan.snd s))
    (fun s => Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s) fun _ _ => rfl)
    (fun s => Quotient.inductionOn₂ (BinaryFan.fst s) (BinaryFan.snd s) fun _ _ => rfl)
    (fun s m h₁ h₂ => by
      induction m using Quotient.inductionOn with
      | h r =>
        obtain ⟨p, hp⟩ := homMk_surjective (BinaryFan.fst s)
        obtain ⟨q, hq⟩ := homMk_surjective (BinaryFan.snd s)
        rw [← hp] at h₁ ⊢
        rw [← hq] at h₂ ⊢
        have h₁' : Homotopic (r.comp (prodFstPre E F)) p := homMk_eq_iff.1 h₁
        have h₂' : Homotopic (r.comp (prodSndPre E F)) q := homMk_eq_iff.1 h₂
        obtain ⟨t₁, ht₁⟩ := h₁'
        obtain ⟨t₂, ht₂⟩ := h₂'
        obtain ⟨w, hw⟩ := exists_pairOf t₁ t₂
        refine homMk_eq_iff.2 ⟨w, fun a x ha => ?_⟩
        obtain ⟨u₁, hu₁, hux₁⟩ := ht₁ a x ha
        obtain ⟨u₂, hu₂, hux₂⟩ := ht₂ a x ha
        exact ⟨PCA.pairEl u₁ u₂, hw a u₁ u₂ hu₁ hu₂, u₁, u₂, hux₁, hux₂, rfl⟩)

instance hasBinaryProduct (E F : ERel.{u, v} A) : HasBinaryProduct E F :=
  ⟨⟨⟨prodFan E F, prodFanIsLimit E F⟩⟩⟩

instance : HasBinaryProducts (ERel.{u, v} A) :=
  hasBinaryProducts_of_hasLimit_pair _

instance : HasTerminal (ERel.{u, v} A) :=
  IsTerminal.hasTerminal isTerminalTerm

instance : HasFiniteProducts (ERel.{u, v} A) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-! ### The embedding preserves binary products -/

/-- The product assembly, with equality, is the product of the two assemblies with equality:
a realizer of a pair *is* a Church pair of realizers, so the identity is tracked both ways. -/
noncomputable def embProdIso (X Y : Assembly.{u, v} A) :
    (emb A).obj (Assembly.prodAsm X Y) ≅ prodERel (eqERel X) (eqERel Y) where
  hom := homMk
    { toFun := _root_.id
      tracked := ⟨PCA.i A, fun a x y h => by
        obtain ⟨⟨b, c, hb, hc, rfl⟩, rfl⟩ := h
        exact ⟨PCA.pairEl b c, by rw [PCA.i_app]; exact Part.mem_some _,
          b, c, ⟨hb, rfl⟩, ⟨hc, rfl⟩, rfl⟩⟩ }
  inv := homMk
    { toFun := _root_.id
      tracked := ⟨PCA.i A, fun a x y h => by
        obtain ⟨b, c, ⟨hb, hb'⟩, ⟨hc, hc'⟩, rfl⟩ := h
        exact ⟨PCA.pairEl b c, by rw [PCA.i_app]; exact Part.mem_some _,
          ⟨b, c, hb, hc, rfl⟩, Prod.ext hb' hc'⟩⟩ }
  hom_inv_id := congrArg homMk (Pre.ext rfl)
  inv_hom_id := congrArg homMk (Pre.ext rfl)

/-- The terminal assembly, with equality, is the terminal object of the completion: on a
one-point assembly every relation is the trivial one. -/
noncomputable def embTermIso :
    (emb A).obj (Assembly.unitAsm A) ≅ termERel.{u, v} A where
  hom := homMk
    { toFun := _root_.id
      tracked := ⟨PCA.k, fun a _ _ _ =>
        ⟨(PCA.app (PCA.k : A) a).get (PCA.k_dom a), Part.get_mem _, trivial⟩⟩ }
  inv := homMk
    { toFun := _root_.id
      tracked := ⟨PCA.i A, fun a x y _ =>
        ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, trivial,
          Subsingleton.elim (α := PUnit.{v + 1}) x y⟩⟩ }
  hom_inv_id := congrArg homMk (Pre.ext rfl)
  inv_hom_id := congrArg homMk (Pre.ext rfl)

end ExReg

end Realizability
