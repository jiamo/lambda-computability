/-
**The interpretation of `λΠ` is transported along a morphism of models.**

`Start/LambdaPiModelHom.lean` defines a morphism `H : ModelHom M N` of models of `λΠ` and the
image `H.semCtx s` of a semantic context, together with the comparison `H.semIso s` of the image
of the object with the object built by iterated extension.  This module proves that `H` carries
the *interpretation* in `M` to the interpretation in `N`:

* `LambdaPi.ModelHom.varVal_map` — the image of a semantic context reads its de Bruijn variables
  as the images of what they read in the source;
* `LambdaPi.TyI.map`, `LambdaPi.TmI.map` — **an expression denoting a type, resp. a term, of `M`
  denotes its image in `N`**;
* `LambdaPi.CtxI.map` — hence the image of an interpretation of a syntactic context is one.

The proofs mirror those of `Start/LambdaPiInterpSub.lean` for renaming: the same induction on the
interpretation relations, with the preservation laws of a morphism of models in place of the
naturality laws of substitution.
-/

import Start.CwaMorVal
import Start.LambdaPiModelHom
import Start.LambdaPiInterpSub

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w u' v' w'

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {M : Model.{u, v, w} C} {N : Model.{u', v', w'} D}

/-! ### Three computations in an arbitrary model -/

/-- **The value of an abstraction is carried by a substitution to the abstraction of the body**
substituted under the binder. -/
theorem val_sub_lam {Γ Δ : C} (σ : Δ ⟶ Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) (x : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) B) :
    Cwa.Val.sub σ (⟨M.SP.Pi a B, M.SP.lam x⟩ : TmVal M Γ)
      = ⟨M.SP.Pi (M.Un.sub σ a) (M.T.tySub (M.Un.extHom σ a) B),
          M.SP.lam (M.T.tmSub (M.Un.extHom σ a) x)⟩ := by
  rw [Cwa.Val.sub, Cwa.Val.mk_tmCast (M.SP.Pi_sub σ a B) (M.T.tmSub σ (M.SP.lam x)),
    M.lam_sub σ a B x]

/-- The value of an abstraction only depends on the value of its body. -/
theorem lam_val_congr {Γ : C} (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    {p q : TmVal M (M.T.ext Γ (M.Un.El a))} (h : p = q) :
    (⟨M.SP.Pi a p.1, M.SP.lam p.2⟩ : TmVal M Γ) = ⟨M.SP.Pi a q.1, M.SP.lam q.2⟩ := by
  cases h; rfl

/-- **The value of the generic application is carried by the action of a substitution on the
extended context to the generic application of the substituted function.** -/
theorem val_sub_app {Γ Δ : C} (σ : Δ ⟶ Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) (f : Cwa.Tm M.T Γ (M.SP.Pi a B)) :
    Cwa.Val.sub (M.Un.extHom σ a) (⟨B, M.SP.app f⟩ : TmVal M (M.T.ext Γ (M.Un.El a)))
      = ⟨M.T.tySub (M.Un.extHom σ a) B,
          M.SP.app (Cwa.tmCast (M.SP.Pi_sub σ a B) (M.T.tmSub σ f))⟩ := by
  rw [Cwa.Val.sub, M.app_sub σ a B f]

/-- Application commutes with the transport along an equality of the body of the product. -/
theorem app_tmCast {Γ : C} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
    {B B' : M.T.Ty (M.T.ext Γ (M.Un.El a))} (h : B = B') (u : Cwa.Tm M.T Γ (M.SP.Pi a B)) :
    Cwa.tmCast h (M.SP.app u) = M.SP.app (Cwa.tmCast (congrArg (M.SP.Pi a) h) u) := by
  cases h; rfl

namespace ModelHom

variable (H : ModelHom M N)

/-- The value of the target that a value of the source denotes: its image, read in the object over
which the image of the semantic context lives. -/
noncomputable def valMap {Γ : C} (s : SemCtx M Γ) (p : TmVal M Γ) : TmVal N (H.semObj s) :=
  Cwa.Val.sub (H.semIso s).inv (H.mor.valMap p)

/-- The comparison of an extended context, followed by the comparison of extended contexts of the
morphism, is the action of the comparison on extended contexts. -/
theorem semIso_inv_extIso {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) :
    (H.semIso (s.cons A)).inv ≫ (H.mor.extIso A).hom
      = N.T.extend (H.semIso s).inv (H.mor.tyMap A) := by
  change (N.T.extend (H.semIso s).inv (H.mor.tyMap A) ≫ (H.mor.extIso A).inv)
      ≫ (H.mor.extIso A).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The comparison of an extended context lies over the comparison of the base. -/
theorem semIso_inv_disp {Γ : C} (s : SemCtx M Γ) (A : M.T.Ty Γ) :
    (H.semIso (s.cons A)).inv ≫ H.mor.fnc.map (M.T.disp A)
      = N.T.disp (H.semTy s A) ≫ (H.semIso s).inv := by
  rw [← H.mor.extIso_disp A, ← Category.assoc, semIso_inv_extIso]
  exact (N.T.isPullback (H.semIso s).inv (H.mor.tyMap A)).w

/-- **The image of a semantic context reads its de Bruijn variables as the images of what they
read in the source.** -/
theorem varVal_map {Γ : C} (s : SemCtx M Γ) (n : ℕ) (p : TmVal M Γ)
    (hp : s.varVal n = some p) : (H.semCtx s).varVal n = some (H.valMap s p) := by
  induction s generalizing n with
  | nil => simp [SemCtx.varVal] at hp
  | @cons Γ s A ih =>
      cases n with
      | zero =>
          simp only [SemCtx.varVal, Option.some.injEq] at hp
          subst hp
          have hv : H.valMap (s.cons A) ⟨M.T.tySub (M.T.disp A) A, Cwa.var A⟩
              = Cwa.Val.sub (N.T.extend (H.semIso s).inv (H.mor.tyMap A))
                  ⟨N.T.tySub (N.T.disp (H.mor.tyMap A)) (H.mor.tyMap A),
                    Cwa.var (H.mor.tyMap A)⟩ := by
            rw [valMap, H.mor.valMap_var N.co A, N.co.val_sub_comp, semIso_inv_extIso]
            rfl
          rw [hv, N.co.val_sub_var]
          rfl
      | succ m =>
          simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          have hv : H.valMap (s.cons A) (Cwa.Val.sub (M.T.disp A) q)
              = Cwa.Val.sub (N.T.disp (H.semTy s A)) (H.valMap s q) := by
            rw [valMap, valMap, H.mor.valMap_sub, N.co.val_sub_comp, N.co.val_sub_comp,
              semIso_inv_disp]
            rfl
          rw [hv]
          have : (H.semCtx (s.cons A)).varVal (m + 1)
              = ((H.semCtx s).varVal m).map (Cwa.Val.sub (N.T.disp (H.semTy s A))) := rfl
          rw [this, ih m q hq]
          rfl

/-! ### The images of the type formers -/

/-- **The universe is carried to the universe.** -/
theorem semTy_U {Γ : C} (s : SemCtx M Γ) : H.semTy s (M.Un.U Γ) = N.Un.U (H.semObj s) := by
  rw [semTy, H.pu.U_map, N.Un.U_sub]

/-- The image of a code, read in the object over which the image of the semantic context
lives. -/
noncomputable def codeTr {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    Cwa.Tm N.T (H.semObj s) (N.Un.U (H.semObj s)) :=
  N.Un.sub (H.semIso s).inv (H.pu.codeMap a)

/-- The image of a term of the universe is the image of the code it is. -/
theorem tmMap_code {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    Cwa.tmCast (H.semTy_U s) (N.T.tmSub (H.semIso s).inv (H.mor.tmMap a)) = H.codeTr s a := by
  rw [codeTr, Cwa.Universe.sub, Cwa.Mor.PreservesUniverse.codeMap, Cwa.tmSub_tmCast,
    Cwa.tmCast_trans]
  rfl

/-- **A decoded code is carried to the decoding of the image of the code.** -/
theorem semTy_El {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    H.semTy s (M.Un.El a) = N.Un.El (H.codeTr s a) := by
  rw [semTy, H.pu.El_map a, N.Un.El_sub']
  rfl

/-- The comparison of the context extended by a decoded code with the image of the context
extended by the decoding. -/
noncomputable def consMor {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    N.T.ext (H.semObj s) (N.Un.El (H.codeTr s a)) ⟶ H.mor.fnc.obj (M.T.ext Γ (M.Un.El a)) :=
  N.Un.extHom (H.semIso s).inv (H.pu.codeMap a) ≫ (H.pu.extElIso a).inv

/-- The comparison of extended contexts is the comparison of the image of the extended context,
read through the identification of the two types. -/
theorem consMor_eq {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm
        ≫ (H.semIso (s.cons (M.Un.El a))).inv
      = H.consMor s a := by
  have h1 : (H.semIso (s.cons (M.Un.El a))).inv
      = N.T.extend (H.semIso s).inv (H.mor.tyMap (M.Un.El a))
          ≫ (H.mor.extIso (M.Un.El a)).inv := rfl
  have key := Cwa.extend_eqToHom_gen (T := N.T) (H.semIso s).inv (H.pu.El_map' a)
    (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm
    (N.Un.ext_El_sub (H.semIso s).inv (H.pu.codeMap a)).symm
    (congrArg (N.T.ext (H.mor.fnc.obj Γ)) (H.pu.El_map' a)).symm
  rw [h1, consMor, Cwa.Universe.extHom, Cwa.Mor.PreservesUniverse.extElIso]
  simp only [Iso.trans_inv, eqToIso.inv]
  have hkey := congrArg (fun m => m ≫ (H.mor.extIso (M.Un.El a)).inv) key
  simp only [Category.assoc] at hkey
  exact hkey.trans (Category.assoc _ _ _).symm

/-- The image of a type of an extended context, read over the context extended by the decoded
image of the code. -/
theorem semTy_cons {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) :
    N.T.tySub (eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm)
        (H.semTy (s.cons (M.Un.El a)) B)
      = N.T.tySub (H.consMor s a) (H.mor.tyMap B) := by
  change N.T.tySub (eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm)
      (N.T.tySub (H.semIso (s.cons (M.Un.El a))).inv (H.mor.tyMap B)) = _
  exact (N.T.tySub_comp (H.semIso (s.cons (M.Un.El a))).inv
        (eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm)
        (H.mor.tyMap B)).symm.trans
      (congrArg (fun m => N.T.tySub m (H.mor.tyMap B)) (consMor_eq H s a))

/-- **A dependent product is carried to the dependent product of the images.** -/
theorem semTy_Pi {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) :
    H.semTy s (M.SP.Pi a B)
      = N.SP.Pi (H.codeTr s a) (N.T.tySub (H.consMor s a) (H.mor.tyMap B)) := by
  rw [semTy, H.psp.Pi_map a B, N.SP.Pi_sub]
  exact congrArg (N.SP.Pi (H.codeTr s a)) (N.T.tySub_comp _ _ _).symm

/-! ### The images of values -/

/-- The image of the universe, read over an arbitrary object of the target. -/
theorem tySub_tyMap_U {Γ : C} {X : D} (σ : X ⟶ H.mor.fnc.obj Γ) :
    N.T.tySub σ (H.mor.tyMap (M.Un.U Γ)) = N.Un.U X := by
  rw [H.pu.U_map, N.Un.U_sub]

/-- **The image of a value of the universe is the image of the code it is**, read over an
arbitrary object of the target. -/
theorem val_sub_valMap_U {Γ : C} {X : D} (σ : X ⟶ H.mor.fnc.obj Γ)
    (c : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    Cwa.Val.sub σ (H.mor.valMap (⟨M.Un.U Γ, c⟩ : TmVal M Γ))
      = ⟨N.Un.U X, N.Un.sub σ (H.pu.codeMap c)⟩ := by
  have hc : Cwa.tmCast (H.tySub_tyMap_U σ) (N.T.tmSub σ (H.mor.tmMap c))
      = N.Un.sub σ (H.pu.codeMap c) := by
    rw [Cwa.Universe.sub, Cwa.Mor.PreservesUniverse.codeMap, Cwa.tmSub_tmCast, Cwa.tmCast_trans]
  rw [Cwa.Mor.valMap_mk, Cwa.Val.sub,
    Cwa.Val.mk_tmCast (H.tySub_tyMap_U σ) (N.T.tmSub σ (H.mor.tmMap c)), hc]

/-- **The image of a value of an extended context**, read over the context extended by the
decoding of the image of the code: it is the image substituted along the comparison of extended
contexts. -/
theorem val_sub_valMap_cons {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (p : TmVal M (M.T.ext Γ (M.Un.El a))) :
    Cwa.Val.sub (eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm)
        (H.valMap (s.cons (M.Un.El a)) p)
      = Cwa.Val.sub (H.consMor s a) (H.mor.valMap p) := by
  refine (N.co.val_sub_comp (H.semIso (s.cons (M.Un.El a))).inv
    (eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm) (H.mor.valMap p)).trans ?_
  exact congrArg (fun σ => Cwa.Val.sub σ (H.mor.valMap p)) (H.consMor_eq s a)

/-- **The image of an abstraction is the abstraction of the image**, read over the context
extended by the decoding of the image of the code. -/
theorem val_sub_valMap_lam {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) (x : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) B) :
    Cwa.Val.sub (H.semIso s).inv (H.mor.valMap (⟨M.SP.Pi a B, M.SP.lam x⟩ : TmVal M Γ))
      = ⟨N.SP.Pi (H.codeTr s a) (N.T.tySub (H.consMor s a) (H.mor.tyMap B)),
          N.SP.lam (N.T.tmSub (H.consMor s a) (H.mor.tmMap x))⟩ := by
  have h1 : H.mor.valMap (⟨M.SP.Pi a B, M.SP.lam x⟩ : TmVal M Γ)
      = ⟨N.SP.Pi (H.pu.codeMap a) (N.T.tySub (H.pu.extElIso a).inv (H.mor.tyMap B)),
          N.SP.lam (N.T.tmSub (H.pu.extElIso a).inv (H.mor.tmMap x))⟩ := by
    rw [Cwa.Mor.valMap_mk,
      Cwa.Val.mk_tmCast (H.psp.Pi_map a B) (H.mor.tmMap (M.SP.lam x)), H.lam_map x]
  rw [h1, val_sub_lam (M := N) (H.semIso s).inv (H.pu.codeMap a)
    (N.T.tySub (H.pu.extElIso a).inv (H.mor.tyMap B))
    (N.T.tmSub (H.pu.extElIso a).inv (H.mor.tmMap x))]
  exact lam_val_congr (M := N) (H.codeTr s a)
    (N.co.val_sub_comp (H.pu.extElIso a).inv _ (H.mor.valMap ⟨B, x⟩))

/-- **The image of the generic application is the generic application of the image**, read over
the context extended by the decoding of the image of the code. -/
theorem val_sub_valMap_app {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (B : M.T.Ty (M.T.ext Γ (M.Un.El a))) (f : Cwa.Tm M.T Γ (M.SP.Pi a B)) :
    Cwa.Val.sub (H.consMor s a)
        (H.mor.valMap (⟨B, M.SP.app f⟩ : TmVal M (M.T.ext Γ (M.Un.El a))))
      = ⟨N.T.tySub (H.consMor s a) (H.mor.tyMap B),
          N.SP.app (Cwa.tmCast (H.semTy_Pi s a B)
            (N.T.tmSub (H.semIso s).inv (H.mor.tmMap f)))⟩ := by
  have h1 : Cwa.Val.sub (H.pu.extElIso a).inv
        (H.mor.valMap (⟨B, M.SP.app f⟩ : TmVal M (M.T.ext Γ (M.Un.El a))))
      = ⟨N.T.tySub (H.pu.extElIso a).inv (H.mor.tyMap B),
          N.SP.app (Cwa.tmCast (H.psp.Pi_map a B) (H.mor.tmMap f))⟩ := by
    rw [Cwa.Mor.valMap_mk, Cwa.Val.sub, H.app_map f]
  have h2 : Cwa.Val.sub (H.consMor s a)
        (H.mor.valMap (⟨B, M.SP.app f⟩ : TmVal M (M.T.ext Γ (M.Un.El a))))
      = Cwa.Val.sub (N.Un.extHom (H.semIso s).inv (H.pu.codeMap a))
          (Cwa.Val.sub (H.pu.extElIso a).inv (H.mor.valMap ⟨B, M.SP.app f⟩)) :=
    (N.co.val_sub_comp _ _ _).symm
  rw [h2, h1, val_sub_app (M := N) (H.semIso s).inv (H.pu.codeMap a)
      (N.T.tySub (H.pu.extElIso a).inv (H.mor.tyMap B))
      (Cwa.tmCast (H.psp.Pi_map a B) (H.mor.tmMap f)),
    Cwa.Val.mk_tmCast (N.T.tySub_comp (H.pu.extElIso a).inv
      (N.Un.extHom (H.semIso s).inv (H.pu.codeMap a)) (H.mor.tyMap B)).symm]
  refine congrArg _ ?_
  rw [app_tmCast (M := N), Cwa.tmSub_tmCast, Cwa.tmCast_trans, Cwa.tmCast_trans]
  rfl

/-- **The section of the image of a term, followed by the comparison of extended contexts, is the
image of its section**: this is what makes an application commute with the morphism. -/
theorem tmCast_consMor {Γ : C} (s : SemCtx M Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (g : Cwa.Tm M.T Γ (M.Un.El a)) :
    (Cwa.tmCast (H.semTy_El s a) (N.T.tmSub (H.semIso s).inv (H.mor.tmMap g))).1
        ≫ H.consMor s a
      = (H.semIso s).inv ≫ H.mor.fnc.map g.1 := by
  have hval : (Cwa.tmCast (H.semTy_El s a)
        (N.T.tmSub (H.semIso s).inv (H.mor.tmMap g))).1
      = (N.T.tmSub (H.semIso s).inv (H.mor.tmMap g)).1
        ≫ eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)) :=
    Cwa.tmCast_val _ _
  have hcancel : eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a))
        ≫ eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)).symm
      = 𝟙 _ := by
    rw [eqToHom_trans, eqToHom_refl]
  -- the comparison of extended contexts, read from the type as the interpretation produces it
  have hphi : eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)) ≫ H.consMor s a
      = N.T.extend (H.semIso s).inv (H.mor.tyMap (M.Un.El a))
        ≫ (H.mor.extIso (M.Un.El a)).inv :=
    (congrArg (fun m => eqToHom (congrArg (N.T.ext (H.semObj s)) (H.semTy_El s a)) ≫ m)
        (H.consMor_eq s a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ (H.semIso (s.cons (M.Un.El a))).inv) hcancel).trans
          (Category.id_comp _)))
  have hfin : ((H.semIso s).inv ≫ (H.mor.tmMap g).1) ≫ (H.mor.extIso (M.Un.El a)).inv
      = (H.semIso s).inv ≫ H.mor.fnc.map g.1 := by
    simp
  exact (congrArg (fun m => m ≫ H.consMor s a) hval).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun m => (N.T.tmSub (H.semIso s).inv (H.mor.tmMap g)).1 ≫ m) hphi).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun m => m ≫ (H.mor.extIso (M.Un.El a)).inv)
              (Cwa.tmSub_extend (H.semIso s).inv (H.mor.tmMap g))).trans hfin))))

end ModelHom

/-! ### Transport along an equality of the type by which a context is extended -/

/-- The interpretation of a type in an extended semantic context is transported along an equality
of the type by which the context is extended. -/
theorem TyI.congr_cons {X : D} {r : SemCtx N X} {A A' : N.T.Ty X} (h : A = A') {t : Tm}
    {B : N.T.Ty (N.T.ext X A)} (hB : TyI (r.cons A) t B) :
    TyI (r.cons A') t (N.T.tySub (eqToHom (congrArg (N.T.ext X) h).symm) B) := by
  cases h
  simpa only [eqToHom_refl, N.T.tySub_id] using hB

/-- The interpretation of a term in an extended semantic context is transported along an equality
of the type by which the context is extended. -/
theorem TmI.congr_cons {X : D} {r : SemCtx N X} {A A' : N.T.Ty X} (h : A = A') {t : Tm}
    {B : N.T.Ty (N.T.ext X A)} {x : Cwa.Tm N.T (N.T.ext X A) B} (hx : TmI (r.cons A) t B x) :
    TmI (r.cons A') t (N.T.tySub (eqToHom (congrArg (N.T.ext X) h).symm) B)
      (N.T.tmSub (eqToHom (congrArg (N.T.ext X) h).symm) x) := by
  cases h
  simp only [eqToHom_refl]
  rw [(Cwa.tmCast_eq_iff (N.T.tySub_id B) (N.T.tmSub (𝟙 _) x) x).mp (N.co.tmSub_id x)]
  exact hx.cast (N.T.tySub_id B).symm

/-! ### The interpretation commutes with a morphism of models -/

mutual

/-- **The interpretation of a type commutes with a morphism of models.** -/
theorem TyI.map (H : ModelHom M N) {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ}
    (h : TyI s t A) : TyI (H.semCtx s) t (H.semTy s A) := by
  cases h with
  | star s =>
      rw [H.semTy_U s]
      exact TyI.star _
  | @el _ _ t c hc =>
      rw [H.semTy_El s c]
      have hc' := (hc.map H).cast (H.semTy_U s)
      rw [H.tmMap_code s c] at hc'
      exact TyI.el hc'
  | @pi _ _ A B a B' ha hB =>
      rw [H.semTy_Pi s a B']
      have ha' := (ha.map H).cast (H.semTy_U s)
      rw [H.tmMap_code s a] at ha'
      have hB' := TyI.congr_cons (H.semTy_El s a) (hB.map H)
      rw [H.semTy_cons s a B'] at hB'
      exact TyI.pi ha' hB'

/-- **The interpretation of a term commutes with a morphism of models.** -/
theorem TmI.map (H : ModelHom M N) {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ}
    {x : Cwa.Tm M.T Γ A} (h : TmI s t A x) :
    TmI (H.semCtx s) t (H.semTy s A) (N.T.tmSub (H.semIso s).inv (H.mor.tmMap x)) := by
  cases h with
  | @var _ _ n A x hv => exact TmI.var (H.varVal_map s n ⟨A, x⟩ hv)
  | @pi _ _ A B a b ha hb =>
      have ha' := (ha.map H).cast (H.semTy_U s)
      rw [H.tmMap_code s a] at ha'
      have hb' : TmI ((H.semCtx s).cons (N.Un.El (H.codeTr s a))) B
          (N.Un.U (N.T.ext (H.semObj s) (N.Un.El (H.codeTr s a))))
          (N.Un.sub (H.consMor s a) (H.pu.codeMap b)) :=
        TmI.cast_val (TmI.congr_cons (H.semTy_El s a) (hb.map H))
          ((H.val_sub_valMap_cons s a ⟨M.Un.U _, b⟩).trans
            (H.val_sub_valMap_U (H.consMor s a) b))
      refine TmI.cast_val (TmI.pi ha' hb') ?_
      change (⟨N.Un.U (H.semObj s), N.PC.code (H.codeTr s a)
            (N.Un.sub (H.consMor s a) (H.pu.codeMap b))⟩ : TmVal N (H.semObj s))
          = Cwa.Val.sub (H.semIso s).inv (H.mor.valMap ⟨M.Un.U Γ, M.PC.code a b⟩)
      rw [H.val_sub_valMap_U (H.semIso s).inv (M.PC.code a b), H.ppc.code_map a b,
        N.PC.code_sub, Cwa.Universe.sub_comp N.co]
      rfl
  | @lam _ _ A b a B' x ha hb =>
      have ha' := (ha.map H).cast (H.semTy_U s)
      rw [H.tmMap_code s a] at ha'
      have hx' : TmI ((H.semCtx s).cons (N.Un.El (H.codeTr s a))) b
          (N.T.tySub (H.consMor s a) (H.mor.tyMap B'))
          (N.T.tmSub (H.consMor s a) (H.mor.tmMap x)) :=
        TmI.cast_val (TmI.congr_cons (H.semTy_El s a) (hb.map H))
          (H.val_sub_valMap_cons s a ⟨B', x⟩)
      refine TmI.cast_val (TmI.lam ha' hx') ?_
      exact (H.val_sub_valMap_lam s a B' x).symm
  | @app _ _ f g a B' f' g' hf hg =>
      have hf' := (hf.map H).cast (H.semTy_Pi s a B')
      have hg' := (hg.map H).cast (H.semTy_El s a)
      refine TmI.cast_val (TmI.app hf' hg') ?_
      change Cwa.Val.sub
            (Cwa.tmCast (H.semTy_El s a) (N.T.tmSub (H.semIso s).inv (H.mor.tmMap g'))).1
            (⟨N.T.tySub (H.consMor s a) (H.mor.tyMap B'),
              N.SP.app (Cwa.tmCast (H.semTy_Pi s a B')
                (N.T.tmSub (H.semIso s).inv (H.mor.tmMap f')))⟩ : TmVal N _)
          = Cwa.Val.sub (H.semIso s).inv
              (H.mor.valMap (Cwa.Val.sub g'.1 (⟨B', M.SP.app f'⟩ : TmVal M _)))
      rw [← H.val_sub_valMap_app s a B' f', N.co.val_sub_comp, H.tmCast_consMor s a g',
        ← N.co.val_sub_comp, ← H.mor.valMap_sub]

end

/-- **The image of an interpretation of a syntactic context is one.** -/
theorem CtxI.map (H : ModelHom M N) {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (h : CtxI Γ s) :
    CtxI Γ (H.semCtx s) := by
  induction h with
  | nil => exact CtxI.nil
  | cons _ hA ih => exact CtxI.cons ih (hA.map H)

end LambdaPi
