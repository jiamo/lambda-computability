/-
**The syntax of `λΠ` interprets itself as the identity.**

`Start/LambdaPiSyntacticModel.lean` shows that the syntax of `λΠ` is a model of `λΠ`, and
`Start/LambdaPiInitial.lean` interprets the syntax in *any* model with injective products.  Applied
to the syntactic model itself, the interpretation must be the identity — that is what this module
proves, at the level of raw expressions:

* `LambdaPiSelf.varVal_rep_conv` — a semantic context of the syntactic model reads the de Bruijn
  variable `n` as the variable `n`;
* `LambdaPiSelf.tyI_rep_conv`, `LambdaPiSelf.tmI_rep_conv` — **the interpretation of a raw
  expression in the syntactic model is that expression**, up to conversion.

The proof is a mutual induction on the two interpretation relations; each case is one of the
computation rules for the representative of a construct of the syntactic model
(`LambdaPiUniv.rep_lamQ`, `LambdaPiUniv.rep_appQ`, `LambdaPiInitial.rep_codeQ_conv`, …).
-/

import Start.LambdaPiInitialUniv

set_option relaxedAutoImplicit false
set_option autoImplicit false

open CategoryTheory

namespace LambdaPiSelf

open LambdaPi LambdaPiCat LambdaPiFull LambdaPiUniv LambdaPiInitial

/-! ### Reading a variable in the syntactic model -/

/-- **The generic term of the syntactic model is the de Bruijn variable `0`.** -/
theorem rep_var {Γ : Ob} (A : TyQ Γ) :
    Conv (rep (Cwa.var (T := syntactic) A)) (Tm.var 0) := by
  have hpos : 0 < (extOb Γ A).ctx.length := Nat.succ_pos _
  have hsec := sec_out_conv (Cwa.var (T := syntactic) A) 0 (Nat.succ_pos _)
  have hid := id_out_conv
    ((Cwa.var (T := syntactic) A).1 ≫ syntactic.extend (syntactic.disp A) A)
    (Cwa.var_extend (T := syntactic) A) hpos
  have hcomp := comp_out_conv (Cwa.var (T := syntactic) A).1
    (syntactic.extend (syntactic.disp A) A) hpos
  have hext := extendQ_out_conv (dispQ A) A hpos
  have hup : up (dispQ A).out.sub 0 = Tm.var 0 := rfl
  rw [hup] at hext
  have hsec' : Conv ((Cwa.var (T := syntactic) A).1.out.sub 0)
      (rep (Cwa.var (T := syntactic) A)) := hsec
  have hstep : Conv ((Cwa.var (T := syntactic) A).1.out.sub 0)
      (subst (Cwa.var (T := syntactic) A).1.out.sub
        ((syntactic.extend (syntactic.disp A) A).out.sub 0)) :=
    (hext.subst (Cwa.var (T := syntactic) A).1.out.sub).symm
  exact hsec'.symm.trans (hstep.trans (hcomp.symm.trans hid))

/-- Weakening a term of the syntactic model shifts its representative. -/
theorem rep_tmSub_disp {Γ : Ob} {A : TyQ Γ} (B : TyQ Γ) (x : Cwa.Tm syntactic Γ A) {n : ℕ}
    (hn : n < Γ.ctx.length) (hx : Conv (rep x) (Tm.var n)) :
    Conv (rep (Cwa.tmSub (T := syntactic) (dispQ B) x)) (Tm.var (n + 1)) := by
  refine (rep_tmSub (dispQ B) x).trans ?_
  refine (hx.subst (dispQ B).out.sub).trans ?_
  have hd : Conv ((dispQ B).out.sub n) (Tm.var (n + 1)) := by
    have := hom_out_conv (f := dispQ B) (g := dispRaw Γ B.rep.ok) rfl hn
    simpa [dispRaw] using this
  simpa using hd

/-- A semantic context of the syntactic model has as many entries as its object. -/
theorem varVal_lt {Γ : Ob} (sc : SemCtx syntacticModel Γ) (n : ℕ)
    (p : TmVal syntacticModel Γ) (hp : sc.varVal n = some p) : n < Γ.ctx.length := by
  induction sc generalizing n with
  | nil => simp [SemCtx.varVal] at hp
  | @cons Δ s A ih =>
      cases n with
      | zero => exact Nat.succ_pos _
      | succ m =>
          simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact Nat.succ_lt_succ (ih m q hq)

/-- **A semantic context of the syntactic model reads the de Bruijn variable `n` as the variable
`n`.** -/
theorem varVal_rep_conv {Γ : Ob} (sc : SemCtx syntacticModel Γ) (n : ℕ)
    (p : TmVal syntacticModel Γ) (hp : sc.varVal n = some p) : Conv (rep p.2) (Tm.var n) := by
  induction sc generalizing n with
  | nil => simp [SemCtx.varVal] at hp
  | @cons Δ s A ih =>
      cases n with
      | zero =>
          simp only [SemCtx.varVal, Option.some.injEq] at hp
          subst hp
          exact rep_var A
      | succ m =>
          simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          exact rep_tmSub_disp A q.2 (varVal_lt s m q hq) (ih m q hq)

/-! ### The interpretation in the syntactic model is the identity -/

mutual

/-- **The type of the syntactic model denoted by a raw expression is that expression**, up to
conversion. -/
theorem tyI_rep_conv {Γ : Ob} {sc : SemCtx syntacticModel Γ} {t : Tm} {A : TyQ Γ}
    (h : TyI sc t A) : Conv A.rep.ty t := by
  cases h with
  | star _ => exact uQ_rep_conv _
  | @el _ _ _ c hc => exact (elQ_rep_conv c).trans (tmI_rep_conv hc)
  | @pi _ _ A₀ B₀ a B' ha hB =>
      exact (piQ_rep_conv a B').trans
        (Conv.pi ((elQ_rep_conv a).trans (tmI_rep_conv ha)) (tyI_rep_conv hB))

/-- **The term of the syntactic model denoted by a raw expression is that expression**, up to
conversion. -/
theorem tmI_rep_conv {Γ : Ob} {sc : SemCtx syntacticModel Γ} {t : Tm} {A : TyQ Γ}
    {x : Cwa.Tm syntactic Γ A} (h : TmI sc t A x) : Conv (rep x) t := by
  cases h with
  | @var _ _ n A x hv => exact varVal_rep_conv sc n ⟨A, x⟩ hv
  | @pi _ _ A₀ B₀ a b ha hb =>
      exact (rep_codeQ_conv a b).trans
        (Conv.pi ((elQ_rep_conv a).trans (tmI_rep_conv ha)) (tmI_rep_conv hb))
  | @lam _ _ A₀ b₀ a B' x ha hb =>
      exact (rep_lamQ x).trans
        (Conv.lam ((elQ_rep_conv a).trans (tmI_rep_conv ha)) (tmI_rep_conv hb))
  | @app _ _ f g a B' f' g' hf hg =>
      have hbnd : Bnd Γ.ctx.length (rep f') := ((rep_ok f').bnd_of_wf Γ.wf).1
      have hσ0 : Conv (g'.1.out.sub 0) (rep g') := sec_out_conv g' 0 (Nat.succ_pos _)
      have hσs : ∀ n, n < Γ.ctx.length → Conv (g'.1.out.sub (n + 1)) (ids n) := fun n hn =>
        sec_out_conv g' (n + 1) (Nat.succ_lt_succ hn)
      refine (rep_tmSub g'.1 (smallPi.app f')).trans ?_
      refine ((rep_appQ f').subst g'.1.out.sub).trans ?_
      change Conv (Tm.app (subst g'.1.out.sub (shift (rep f')))
        (subst g'.1.out.sub (Tm.var 0))) _
      refine Conv.app ?_ (hσ0.trans (tmI_rep_conv hg))
      rw [subst_shift']
      refine (conv_subst_congr hbnd hσs).trans ?_
      rw [subst_ids]
      exact tmI_rep_conv hf

end

end LambdaPiSelf
