/-
**Dependent sums in the set-theoretic model of `λΠ`.**

`Start/CwaTypeModel.lean` builds the standard model — contexts are types of `Type (u + 1)`, a type
is a family of small types, a term is a dependent function — and shows that its universe of small
types is closed under dependent products.  This module does the same for dependent sums: the sum
of the codes `a` and `b` is the family `x ↦ (y : a x) × b ⟨x, y⟩`, which is small again on the
nose, and the context extended by it is the context extended first by `a` and then by `b`.

Main definitions and results:

* `CwaTypeModel.sigCode` — the code of the dependent sum of two codes, and
  `CwaTypeModel.sigCode_sub` its stability under substitution;
* `CwaTypeModel.pairIso` — **pairing**: extending by `a` and then by `b` is extending by the sum,
  and `CwaTypeModel.pairIso_disp` says that this isomorphism lies over the base context;
* `CwaTypeModel.codeSigma` — hence **the universe of small types is closed under dependent
  sums**, in the sense of `Cwa.Universe.CodeSigma`;
* `CwaTypeModel.modelSigma` — **the set-theoretic model has dependent sums**.
-/

import Start.CwaTypeModel
import Start.CwaCodeSigma

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory CwaUniv

namespace CwaTypeModel

variable {Γ Δ : Type (u + 1)}

/-! #### The code of a dependent sum -/

/-- Equality of dependent sum types, from an equality of domains and of bodies. -/
theorem sigma_type_congr {A A' : Type u} (h : A = A') {B : A → Type u} {B' : A' → Type u}
    (hB : ∀ y : A, B y = B' (cast h y)) : ((y : A) × B y) = ((y : A') × B' y) := by
  cases h
  exact congrArg (fun F : A → Type u => ((y : A) × F y)) (funext hB)

/-- The family of dependent sum types: the sum of a code `a` and a code `b` over its total
space. -/
noncomputable abbrev sigmaFam (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) : Γ ⟶ Uob.{u} :=
  ↾fun x => ((y : fam a x) × fam b ((extIso a).hom ⟨x, y⟩))

/-- The code of the dependent sum of two codes. -/
noncomputable def sigCode (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    Cwa.Tm amb Γ (un.U Γ) := (codeEquiv Γ).symm (sigmaFam a b)

@[simp] theorem fam_sigCode (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    fam (sigCode a b) = sigmaFam a b := fam_codeEquiv_symm _

theorem fam_sigCode_apply (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) (x : Γ) :
    (fam (sigCode a b)) x = ((y : fam a x) × fam b ((extIso a).hom ⟨x, y⟩)) := by
  rw [fam_sigCode]
  try rfl

/-- **The code of a sum is stable under substitution.** -/
theorem sigCode_sub (σ : Δ ⟶ Γ) (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    un.sub σ (sigCode a b) = sigCode (un.sub σ a) (un.sub (un.extHom σ a) b) := by
  refine code_ext ?_
  rw [fam_sub]
  simp only [fam_sigCode]
  refine types_hom_ext fun x => ?_
  refine sigma_type_congr (types_hom_congr_fun (fam_sub σ a) x).symm fun y => ?_
  set y' : fam (un.sub σ a) x := cast (types_hom_congr_fun (fam_sub σ a) x).symm y
  have hb : fam (un.sub (un.extHom σ a) b) = un.extHom σ a ≫ fam b :=
    fam_sub (un.extHom σ a) b
  have h1 := types_hom_congr_fun hb ((extIso (un.sub σ a)).hom ⟨x, y'⟩)
  have h2 := extHom_apply σ a ⟨x, y'⟩
  simp only [types_comp_apply] at h1
  rw [h1, h2]
  refine congrArg (ConcreteCategory.hom (fam b)) ?_
  refine congrArg (ConcreteCategory.hom (extIso a).hom) ?_
  refine Sigma.ext rfl ?_
  exact ((cast_heq _ _).trans (cast_heq _ _)).symm

/-! #### Pairing -/

/-- The total space of `b` is the total space of the sum: a point over `w` in the extended
context is a point of the base together with a point of `a` and a point of `b`. -/
noncomputable def sigmaTotalEquiv (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    sigObj (fam b) ≃ sigObj (fam (sigCode a b)) :=
  ((Equiv.sigmaCongrLeft (β := fun w => fam b w) (extIso a).toEquiv).symm.trans
      (Equiv.sigmaAssoc fun (x : Γ) (y : fam a x) => fam b ((extIso a).hom ⟨x, y⟩))).trans
    (Equiv.sigmaCongrRight fun x => Equiv.cast (fam_sigCode_apply a b x).symm)

@[simp] theorem sigmaTotalEquiv_fst (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a))))
    (z : sigObj (fam b)) :
    (sigmaTotalEquiv a b z).1 = ((extIso a).inv z.1).1 := rfl

/-- **Pairing**: the context extended by `a` and then by `b` is the context extended by the code
of their sum. -/
noncomputable def pairIso (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    amb.ext (amb.ext Γ (un.El a)) (un.El b) ≅ amb.ext Γ (un.El (sigCode a b)) :=
  (extIso b).symm ≪≫ (sigmaTotalEquiv a b).toIso ≪≫ extIso (sigCode a b)

/-- **The pairing isomorphism lies over the base context.** -/
theorem pairIso_disp (a : Cwa.Tm amb Γ (un.U Γ))
    (b : Cwa.Tm amb (amb.ext Γ (un.El a)) (un.U (amb.ext Γ (un.El a)))) :
    (pairIso a b).hom ≫ LuTy.disp (un.El (sigCode a b))
      = LuTy.disp (un.El b) ≫ LuTy.disp (un.El a) := by
  have hdisp : ∀ {Ξ : Type (u + 1)} (c : Cwa.Tm amb Ξ (un.U Ξ)) (v : sigObj (fam c)),
      LuTy.disp (un.El c) ((extIso c).hom v) = v.1 := by
    intro Ξ c v
    simpa using ConcreteCategory.congr_hom (extIso_hom_disp c) v
  have hinv : ∀ {Ξ : Type (u + 1)} (c : Cwa.Tm amb Ξ (un.U Ξ)) (w : amb.ext Ξ (un.El c)),
      LuTy.disp (un.El c) w = ((extIso c).inv w).1 := by
    intro Ξ c w
    have e : (extIso c).hom ((extIso c).inv w) = w := by
      simp
    calc LuTy.disp (un.El c) w
        = LuTy.disp (un.El c) ((extIso c).hom ((extIso c).inv w)) := by rw [e]
      _ = ((extIso c).inv w).1 := hdisp c _
  refine types_hom_ext fun s => ?_
  simp only [types_comp_apply, pairIso, Iso.trans_hom, Iso.symm_hom]
  rw [hdisp (sigCode a b), hinv b s, hinv a]
  rfl

/-! #### The model has dependent sums -/

/-- **The universe of small types is closed under dependent sums.** -/
noncomputable def codeSigma : Cwa.Universe.CodeSigma un.{u} where
  code a b := sigCode a b
  code_sub σ a b := sigCode_sub σ a b
  pair a b := pairIso a b
  pair_disp a b := pairIso_disp a b

/-- **The set-theoretic model of `λΠ` has dependent sums.** -/
noncomputable def modelSigma : Cwa.SigmaStruct model.{u} :=
  Cwa.Universe.smallSigmaOfCodeSigma (Cwa.extCoherent_ofPullbacks _) un codeSigma

/-- **The dependent sum of the model is the dependent pair type.** -/
theorem fam_modelSigma_Sig (a : model.Ty Γ) (b : model.Ty (model.ext Γ a)) :
    fam (modelSigma.Sig a b) = ↾fun x => ((y : fam a x) × fam b ((extIso a).hom ⟨x, y⟩)) :=
  fam_sigCode a b

end CwaTypeModel
