/-
**The interpretation of `λΠ` commutes with substitution.**

This is the technical heart of the interpretation of `Start/LambdaPiInterp.lean`: renaming and
substituting in a raw expression corresponds, on the semantic side, to substituting along a
morphism of the category of contexts.

* `LambdaPi.RenI` — a renaming `ρ` is *carried* by a morphism `σ` of the model when it takes the
  value of every variable to the value substituted along `σ`;
* `LambdaPi.RenI.up` — a carried renaming may be lifted under a binder, by the naturality of the
  generic term (`Cwa.ExtCoherent.tmSub_extend_var`);
* `LambdaPi.TyI.ren`, `LambdaPi.TmI.ren` — **the interpretation commutes with renaming**;
* `LambdaPi.TyI.weaken`, `LambdaPi.TmI.weaken` — in particular it commutes with weakening, the
  display map carrying the shift;
* `LambdaPi.SubI` — the same notion for a parallel substitution of terms, and `LambdaPi.SubI.up`
  its lifting under a binder, which uses weakening;
* `LambdaPi.TyI.subst`, `LambdaPi.TmI.subst` — **the interpretation commutes with substitution**;
* `LambdaPi.TyI.inst`, `LambdaPi.TmI.inst` — the single-variable form: instantiating the last
  variable of the context by a term is substituting along the section that term defines.

The model laws used are exactly the naturality laws of `LambdaPi.Model`: Beck–Chevalley for the
dependent product, naturality of abstraction and of application, and stability of the codes.
-/

import Start.LambdaPiInterp

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### Transport of the interpretation along equalities -/

/-- The interpretation of a term is transported along an equality of types. -/
theorem TmI.cast {Γ : C} {s : SemCtx M Γ} {t : Tm} {A A' : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
    (h : A = A') (hx : TmI s t A x) : TmI s t A' (Cwa.tmCast h x) := by
  cases h; exact hx

/-- The interpretation of a term is determined by its value, as a pair of a type and a term. -/
theorem TmI.cast_val {Γ : C} {s : SemCtx M Γ} {t : Tm} {A A' : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
    {x' : Cwa.Tm M.T Γ A'} (hx : TmI s t A x) (h : (⟨A, x⟩ : TmVal M Γ) = ⟨A', x'⟩) :
    TmI s t A' x' := by
  rcases Sigma.mk.inj_iff.mp h with ⟨h1, h2⟩
  subst h1
  cases eq_of_heq h2
  exact hx

/-! ### Values and substitution -/

/-! ### Renaming -/

/-- **The renaming `ρ` is carried by the morphism `σ`**: every variable of the source semantic
context is taken to its value substituted along `σ`. -/
def RenI {Γ Δ : C} (s : SemCtx M Γ) (r : SemCtx M Δ) (σ : Δ ⟶ Γ) (ρ : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (p : TmVal M Γ), s.varVal n = some p → r.varVal (ρ n) = some (Cwa.Val.sub σ p)

/-- **A carried renaming may be lifted under a binder.**  At the new variable this is the
naturality of the generic term, at the others the functoriality of substitution together with the
commutativity of the extension square. -/
theorem RenI.up {Γ Δ : C} {s : SemCtx M Γ} {r : SemCtx M Δ} {σ : Δ ⟶ Γ} {ρ : ℕ → ℕ}
    (h : RenI s r σ ρ) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    RenI (s.cons (M.Un.El a)) (r.cons (M.Un.El (M.Un.sub σ a))) (M.Un.extHom σ a) (upr ρ) := by
  intro n p hp
  cases n with
  | zero =>
      simp only [SemCtx.varVal, Option.some.injEq] at hp
      subst hp
      simp only [upr, SemCtx.varVal, Option.some.injEq]
      rw [Cwa.Universe.extHom]
      exact (M.co.val_sub_var_of_eq σ (M.Un.El a) (M.Un.El_sub' σ a)).symm
  | succ m =>
      simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      simp only [upr, SemCtx.varVal, h m q hq, Option.map_some, Option.some.injEq]
      rw [M.co.val_sub_comp, M.co.val_sub_comp, (M.Un.isPullback_extHom σ a).w]

/-- The section defined by a substituted term, composed with the action of the substitution on the
extended context, is the substitution followed by the original section. -/
theorem tmCast_extHom {Γ Δ : C} (σ : Δ ⟶ Γ) (a : Cwa.Tm M.T Γ (M.Un.U Γ))
    (g : Cwa.Tm M.T Γ (M.Un.El a)) :
    (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g)).1 ≫ M.Un.extHom σ a = σ ≫ g.1 := by
  rw [Cwa.tmCast_val, Cwa.Universe.extHom, Category.assoc, ← Category.assoc (eqToHom _),
    eqToHom_trans, eqToHom_refl, Category.id_comp, Cwa.tmSub_extend]

mutual

/-- **The interpretation of a type commutes with renaming.** -/
theorem TyI.ren {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ} (h : TyI s t A)
    {Δ : C} {r : SemCtx M Δ} {σ : Δ ⟶ Γ} {ρ : ℕ → ℕ} (hρ : RenI s r σ ρ) :
    TyI r (rename ρ t) (M.T.tySub σ A) := by
  cases h with
  | star s =>
      rw [M.Un.U_sub σ]
      exact TyI.star r
  | @el _ _ t c hc =>
      rw [M.Un.El_sub' σ c]
      exact TyI.el ((hc.ren hρ).cast (M.Un.U_sub σ))
  | @pi _ _ A B a B' ha hB =>
      rw [M.SP.Pi_sub σ a B']
      exact TyI.pi ((ha.ren hρ).cast (M.Un.U_sub σ)) (hB.ren (hρ.up a))

/-- **The interpretation of a term commutes with renaming.** -/
theorem TmI.ren {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
    (h : TmI s t A x) {Δ : C} {r : SemCtx M Δ} {σ : Δ ⟶ Γ} {ρ : ℕ → ℕ} (hρ : RenI s r σ ρ) :
    TmI r (rename ρ t) (M.T.tySub σ A) (M.T.tmSub σ x) := by
  cases h with
  | @var _ _ n A x hv => exact TmI.var (hρ n ⟨A, x⟩ hv)
  | @pi _ _ A B a b ha hb =>
      refine TmI.cast_val
        (TmI.pi ((ha.ren hρ).cast (M.Un.U_sub σ))
          ((hb.ren (hρ.up a)).cast (M.Un.U_sub (M.Un.extHom σ a)))) ?_
      rw [Cwa.Val.mk_tmCast (M.Un.U_sub σ) (M.T.tmSub σ (M.PC.code a b))]
      exact congrArg _ (M.PC.code_sub σ a b).symm
  | @lam _ _ A b a B' x ha hb =>
      refine TmI.cast_val
        (TmI.lam ((ha.ren hρ).cast (M.Un.U_sub σ)) (hb.ren (hρ.up a))) ?_
      rw [Cwa.Val.mk_tmCast (M.SP.Pi_sub σ a B') (M.T.tmSub σ (M.SP.lam x))]
      exact congrArg _ (M.lam_sub σ a B' x).symm
  | @app _ _ f g a B' f' g' hf hg =>
      refine TmI.cast_val
        (TmI.app ((hf.ren hρ).cast (M.SP.Pi_sub σ a B'))
          ((hg.ren hρ).cast (M.Un.El_sub' σ a))) ?_
      have hcomp : (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1 ≫ M.Un.extHom σ a
          = σ ≫ g'.1 := tmCast_extHom σ a g'
      calc (⟨M.T.tySub (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1
                (M.T.tySub (M.Un.extHom σ a) B'),
              M.T.tmSub (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1
                (M.SP.app (Cwa.tmCast (M.SP.Pi_sub σ a B') (M.T.tmSub σ f')))⟩ : TmVal M Δ)
          = Cwa.Val.sub (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1
              (Cwa.Val.sub (M.Un.extHom σ a) ⟨B', M.SP.app f'⟩) := by
            rw [Cwa.Val.sub, Cwa.Val.sub, M.app_sub σ a B' f']
        _ = Cwa.Val.sub (σ ≫ g'.1) ⟨B', M.SP.app f'⟩ := by
            rw [M.co.val_sub_comp, hcomp]
        _ = Cwa.Val.sub σ (Cwa.Val.sub g'.1 ⟨B', M.SP.app f'⟩) := (M.co.val_sub_comp _ _ _).symm
        _ = ⟨M.T.tySub σ (M.T.tySub g'.1 B'), M.T.tmSub σ (M.T.tmSub g'.1 (M.SP.app f'))⟩ := rfl

end

/-! ### Weakening -/

/-- **The shift is carried by the display map**: this is exactly how `SemCtx.varVal` reads a
variable of an extended context. -/
theorem RenI.shift {Γ : C} (s : SemCtx M Γ) (B : M.T.Ty Γ) :
    RenI s (s.cons B) (M.T.disp B) Nat.succ := by
  intro n p hp
  simp [SemCtx.varVal, hp]

/-- **The interpretation of a type commutes with weakening.** -/
theorem TyI.weaken {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ} (h : TyI s t A)
    (B : M.T.Ty Γ) : TyI (s.cons B) (shift t) (M.T.tySub (M.T.disp B) A) :=
  h.ren (RenI.shift s B)

/-- **The interpretation of a term commutes with weakening.** -/
theorem TmI.weaken {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
    (h : TmI s t A x) (B : M.T.Ty Γ) :
    TmI (s.cons B) (shift t) (M.T.tySub (M.T.disp B) A) (M.T.tmSub (M.T.disp B) x) :=
  h.ren (RenI.shift s B)

/-! ### Parallel substitution -/

/-- The value of the variable `0` of an extended semantic context, read after the action of a
substitution: the naturality of the generic term again. -/
theorem SemCtx.varVal_zero_extHom {Γ Δ : C} (r : SemCtx M Δ) (σ : Δ ⟶ Γ)
    (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    (r.cons (M.Un.El (M.Un.sub σ a))).varVal 0
      = some (Cwa.Val.sub (M.Un.extHom σ a)
          ⟨M.T.tySub (M.T.disp (M.Un.El a)) (M.Un.El a), Cwa.var (M.Un.El a)⟩) := by
  simp only [SemCtx.varVal, Option.some.injEq]
  rw [Cwa.Universe.extHom]
  exact (M.co.val_sub_var_of_eq σ (M.Un.El a) (M.Un.El_sub' σ a)).symm

/-- **The substitution `f` is carried by the morphism `σ`**: the interpretation of the term `f n`
is the value of the variable `n`, substituted along `σ`. -/
def SubI {Γ Δ : C} (s : SemCtx M Γ) (r : SemCtx M Δ) (σ : Δ ⟶ Γ) (f : ℕ → Tm) : Prop :=
  ∀ (n : ℕ) (p : TmVal M Γ), s.varVal n = some p →
    TmI r (f n) (Cwa.Val.sub σ p).1 (Cwa.Val.sub σ p).2

/-- **A carried substitution may be lifted under a binder**: the new variable is interpreted by
the generic term, and the others by the weakening of what they were interpreted by. -/
theorem SubI.up {Γ Δ : C} {s : SemCtx M Γ} {r : SemCtx M Δ} {σ : Δ ⟶ Γ} {f : ℕ → Tm}
    (h : SubI s r σ f) (a : Cwa.Tm M.T Γ (M.Un.U Γ)) :
    SubI (s.cons (M.Un.El a)) (r.cons (M.Un.El (M.Un.sub σ a))) (M.Un.extHom σ a)
      (LambdaPi.up f) := by
  intro n p hp
  cases n with
  | zero =>
      simp only [SemCtx.varVal, Option.some.injEq] at hp
      subst hp
      exact TmI.var (SemCtx.varVal_zero_extHom r σ a)
  | succ m =>
      simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      refine TmI.cast_val ((h m q hq).weaken (M.Un.El (M.Un.sub σ a))) ?_
      change Cwa.Val.sub (M.T.disp (M.Un.El (M.Un.sub σ a))) (Cwa.Val.sub σ q)
          = Cwa.Val.sub (M.Un.extHom σ a) (Cwa.Val.sub (M.T.disp (M.Un.El a)) q)
      rw [M.co.val_sub_comp, M.co.val_sub_comp, (M.Un.isPullback_extHom σ a).w]

mutual

/-- **The interpretation of a type commutes with substitution.** -/
theorem TyI.subst {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ} (h : TyI s t A)
    {Δ : C} {r : SemCtx M Δ} {σ : Δ ⟶ Γ} {f : ℕ → Tm} (hf : SubI s r σ f) :
    TyI r (LambdaPi.subst f t) (M.T.tySub σ A) := by
  cases h with
  | star s =>
      rw [M.Un.U_sub σ]
      exact TyI.star r
  | @el _ _ t c hc =>
      rw [M.Un.El_sub' σ c]
      exact TyI.el ((hc.subst hf).cast (M.Un.U_sub σ))
  | @pi _ _ A B a B' ha hB =>
      rw [M.SP.Pi_sub σ a B']
      exact TyI.pi ((ha.subst hf).cast (M.Un.U_sub σ)) (hB.subst (hf.up a))

/-- **The interpretation of a term commutes with substitution.** -/
theorem TmI.subst {Γ : C} {s : SemCtx M Γ} {t : Tm} {A : M.T.Ty Γ} {x : Cwa.Tm M.T Γ A}
    (h : TmI s t A x) {Δ : C} {r : SemCtx M Δ} {σ : Δ ⟶ Γ} {f : ℕ → Tm} (hf : SubI s r σ f) :
    TmI r (LambdaPi.subst f t) (M.T.tySub σ A) (M.T.tmSub σ x) := by
  cases h with
  | @var _ _ n A x hv => exact hf n ⟨A, x⟩ hv
  | @pi _ _ A B a b ha hb =>
      refine TmI.cast_val
        (TmI.pi ((ha.subst hf).cast (M.Un.U_sub σ))
          ((hb.subst (hf.up a)).cast (M.Un.U_sub (M.Un.extHom σ a)))) ?_
      rw [Cwa.Val.mk_tmCast (M.Un.U_sub σ) (M.T.tmSub σ (M.PC.code a b))]
      exact congrArg _ (M.PC.code_sub σ a b).symm
  | @lam _ _ A b a B' x ha hb =>
      refine TmI.cast_val
        (TmI.lam ((ha.subst hf).cast (M.Un.U_sub σ)) (hb.subst (hf.up a))) ?_
      rw [Cwa.Val.mk_tmCast (M.SP.Pi_sub σ a B') (M.T.tmSub σ (M.SP.lam x))]
      exact congrArg _ (M.lam_sub σ a B' x).symm
  | @app _ _ f g a B' f' g' hf' hg =>
      refine TmI.cast_val
        (TmI.app ((hf'.subst hf).cast (M.SP.Pi_sub σ a B'))
          ((hg.subst hf).cast (M.Un.El_sub' σ a))) ?_
      have hcomp : (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1 ≫ M.Un.extHom σ a
          = σ ≫ g'.1 := tmCast_extHom σ a g'
      calc (⟨M.T.tySub (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1
                (M.T.tySub (M.Un.extHom σ a) B'),
              M.T.tmSub (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1
                (M.SP.app (Cwa.tmCast (M.SP.Pi_sub σ a B') (M.T.tmSub σ f')))⟩ : TmVal M Δ)
          = Cwa.Val.sub (Cwa.tmCast (M.Un.El_sub' σ a) (M.T.tmSub σ g')).1
              (Cwa.Val.sub (M.Un.extHom σ a) ⟨B', M.SP.app f'⟩) := by
            rw [Cwa.Val.sub, Cwa.Val.sub, M.app_sub σ a B' f']
        _ = Cwa.Val.sub (σ ≫ g'.1) ⟨B', M.SP.app f'⟩ := by
            rw [M.co.val_sub_comp, hcomp]
        _ = Cwa.Val.sub σ (Cwa.Val.sub g'.1 ⟨B', M.SP.app f'⟩) := (M.co.val_sub_comp _ _ _).symm
        _ = ⟨M.T.tySub σ (M.T.tySub g'.1 B'), M.T.tmSub σ (M.T.tmSub g'.1 (M.SP.app f'))⟩ := rfl

end

/-! ### Instantiating the last variable -/

/-- **The section defined by an interpreted term carries the substitution that instantiates the
last variable of the context by it.** -/
theorem SubI.sec {Γ : C} {s : SemCtx M Γ} {g : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
    {g' : Cwa.Tm M.T Γ (M.Un.El a)} (hg : TmI s g (M.Un.El a) g') :
    SubI (s.cons (M.Un.El a)) s g'.1 (scons g ids) := by
  intro n p hp
  cases n with
  | zero =>
      simp only [SemCtx.varVal, Option.some.injEq] at hp
      subst hp
      exact TmI.cast_val hg (M.co.val_sub_sec_var g').symm
  | succ m =>
      simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      refine TmI.cast_val (TmI.var hq) ?_
      change q = Cwa.Val.sub g'.1 (Cwa.Val.sub (M.T.disp (M.Un.El a)) q)
      rw [M.co.val_sub_comp, g'.2, M.co.val_sub_id]

/-- **Instantiating the last variable of the context by a term is substituting along the section
that term defines**, for the interpretation of a type. -/
theorem TyI.inst {Γ : C} {s : SemCtx M Γ} {B g : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
    {B' : M.T.Ty (M.T.ext Γ (M.Un.El a))} {g' : Cwa.Tm M.T Γ (M.Un.El a)}
    (hB : TyI (s.cons (M.Un.El a)) B B') (hg : TmI s g (M.Un.El a) g') :
    TyI s B[g] (M.T.tySub g'.1 B') :=
  hB.subst (SubI.sec hg)

/-- The same for the interpretation of a term. -/
theorem TmI.inst {Γ : C} {s : SemCtx M Γ} {b g : Tm} {a : Cwa.Tm M.T Γ (M.Un.U Γ)}
    {B' : M.T.Ty (M.T.ext Γ (M.Un.El a))} {x : Cwa.Tm M.T (M.T.ext Γ (M.Un.El a)) B'}
    {g' : Cwa.Tm M.T Γ (M.Un.El a)}
    (hb : TmI (s.cons (M.Un.El a)) b B' x) (hg : TmI s g (M.Un.El a) g') :
    TmI s b[g] (M.T.tySub g'.1 B') (M.T.tmSub g'.1 x) :=
  hb.subst (SubI.sec hg)

end LambdaPi
