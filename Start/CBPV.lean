/-
**Call-by-push-value** — task `M25-CBPV`.

Levy's call-by-push-value, with its two type levels:

* value types `VTy`: a base type and `U B` (thunks of computations of type `B`);
* computation types `CTy`: `F A` (computations returning a value of type `A`) and `A → B`.

Terms (`CBPV.CT`, one syntax with de Bruijn indices; the typing judgement sorts values from
computations): `var`, `thunk M`, `force V`, `ret V`, `M to x. N` (`bind`), `λx. M`, `M V`.
The typing judgement is `CBPV.CTyp`, the reduction `CBPV.CStep` (evaluation of computations).

The source is a small simply typed λ-calculus (`CBPV.STm`, typing `CBPV.STyp`) with its
call-by-name (weak head) reduction `CBPV.NStep` and its call-by-value reduction `CBPV.VStep`.

Main results:

* `CBPV.tn_typing`, `CBPV.tv_typing` — the call-by-name translation `CBPV.tn` and the call-by-value
  translation `CBPV.tv` preserve typing (`A ↦ tyN A` a computation type, contexts as `U` of it;
  `A ↦ tyV A` a value type, a term of type `A` becoming a computation of type `F (tyV A)`);
* `CBPV.tn_sim` — **call-by-name simulation**: a source step `t → t'` becomes exactly one CBPV step
  `tn t → M`, followed by administrative `force (thunk N) ⇝ N` contractions `M ⇝* tn t'`;
* `CBPV.tv_beta` — **call-by-value β**: a source β step becomes four CBPV steps, exactly;
* `CBPV.tv_sim` — **call-by-value simulation**: a source step `t → t'` gives `tv t →⁺ M` and
  `tv t' →* M` (the translations of `t` and `t'` meet after the image of `t` made at least one step).
-/

import Mathlib.Logic.Relation
import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CBPV

/-! ### Types -/

mutual
/-- Value types. -/
inductive VTy where
  | base : VTy
  /-- Thunks of computations. -/
  | U : CTy → VTy
/-- Computation types. -/
inductive CTy where
  /-- Computations returning a value. -/
  | F : VTy → CTy
  /-- Functions from values to computations. -/
  | arr : VTy → CTy → CTy
end

/-- The sort of a term: a value of a value type or a computation of a computation type. -/
inductive Sort' where
  | v : VTy → Sort'
  | c : CTy → Sort'

/-! ### Terms, renaming and substitution -/

/-- CBPV terms. -/
inductive CT where
  | var : ℕ → CT
  | thunk : CT → CT
  | force : CT → CT
  | ret : CT → CT
  /-- `bind M N` is `M to x. N`, binding `x` in `N`. -/
  | bind : CT → CT → CT
  | lam : CT → CT
  | app : CT → CT → CT

/-- Lifting a renaming under a binder. -/
def up (ξ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ξ n + 1

/-- Renaming. -/
def CT.ren (ξ : ℕ → ℕ) : CT → CT
  | var n => var (ξ n)
  | thunk M => thunk (M.ren ξ)
  | force V => force (V.ren ξ)
  | ret V => ret (V.ren ξ)
  | bind M N => bind (M.ren ξ) (N.ren (up ξ))
  | lam M => lam (M.ren (up ξ))
  | app M V => app (M.ren ξ) (V.ren ξ)

/-- Lifting a substitution under a binder. -/
def upS (σ : ℕ → CT) : ℕ → CT
  | 0 => .var 0
  | n + 1 => (σ n).ren Nat.succ

/-- Substitution. -/
def CT.subst (σ : ℕ → CT) : CT → CT
  | var n => σ n
  | thunk M => thunk (M.subst σ)
  | force V => force (V.subst σ)
  | ret V => ret (V.subst σ)
  | bind M N => bind (M.subst σ) (N.subst (upS σ))
  | lam M => lam (M.subst (upS σ))
  | app M V => app (M.subst σ) (V.subst σ)

/-- `cons V σ` maps `0` to `V` and `n + 1` to `σ n`. -/
def cons {α : Type} (a : α) (σ : ℕ → α) : ℕ → α
  | 0 => a
  | n + 1 => σ n

/-- Single substitution of `V` for the variable `0`. -/
def CT.subst1 (M V : CT) : CT := M.subst (cons V CT.var)

theorem up_comp (ξ ζ : ℕ → ℕ) : up ζ ∘ up ξ = up (ζ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem CT.ren_ren (M : CT) : ∀ (ξ ζ : ℕ → ℕ), (M.ren ξ).ren ζ = M.ren (ζ ∘ ξ) := by
  induction M with
  | var n => intros; rfl
  | thunk M ih => intros; simp [CT.ren, ih]
  | force M ih => intros; simp [CT.ren, ih]
  | ret M ih => intros; simp [CT.ren, ih]
  | bind M N ih1 ih2 => intros; simp [CT.ren, ih1, ih2, up_comp]
  | lam M ih => intros; simp [CT.ren, ih, up_comp]
  | app M V ih1 ih2 => intros; simp [CT.ren, ih1, ih2]

theorem upS_up (σ : ℕ → CT) (ξ : ℕ → ℕ) : upS σ ∘ up ξ = upS (σ ∘ ξ) := by
  funext n; cases n <;> rfl

theorem CT.subst_ren (M : CT) : ∀ (ξ : ℕ → ℕ) (σ : ℕ → CT),
    (M.ren ξ).subst σ = M.subst (σ ∘ ξ) := by
  induction M with
  | var n => intros; rfl
  | thunk M ih => intros; simp [CT.ren, CT.subst, ih]
  | force M ih => intros; simp [CT.ren, CT.subst, ih]
  | ret M ih => intros; simp [CT.ren, CT.subst, ih]
  | bind M N ih1 ih2 => intros; simp [CT.ren, CT.subst, ih1, ih2, upS_up]
  | lam M ih => intros; simp [CT.ren, CT.subst, ih, upS_up]
  | app M V ih1 ih2 => intros; simp [CT.ren, CT.subst, ih1, ih2]

theorem up_upS (σ : ℕ → CT) (ξ : ℕ → ℕ) :
    CT.ren (up ξ) ∘ upS σ = upS (CT.ren ξ ∘ σ) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [Function.comp, upS, CT.ren_ren]
      rfl

theorem CT.ren_subst (M : CT) : ∀ (σ : ℕ → CT) (ξ : ℕ → ℕ),
    (M.subst σ).ren ξ = M.subst (CT.ren ξ ∘ σ) := by
  induction M with
  | var n => intros; rfl
  | thunk M ih => intros; simp [CT.ren, CT.subst, ih]
  | force M ih => intros; simp [CT.ren, CT.subst, ih]
  | ret M ih => intros; simp [CT.ren, CT.subst, ih]
  | bind M N ih1 ih2 => intros; simp [CT.ren, CT.subst, ih1, ih2, up_upS]
  | lam M ih => intros; simp [CT.ren, CT.subst, ih, up_upS]
  | app M V ih1 ih2 => intros; simp [CT.ren, CT.subst, ih1, ih2]

theorem upS_var : upS CT.var = CT.var := by
  funext n; cases n <;> rfl

theorem CT.subst_var (M : CT) : M.subst CT.var = M := by
  induction M with
  | var n => rfl
  | thunk M ih => simp [CT.subst, ih]
  | force M ih => simp [CT.subst, ih]
  | ret M ih => simp [CT.subst, ih]
  | bind M N ih1 ih2 => simp [CT.subst, ih1, ih2, upS_var]
  | lam M ih => simp [CT.subst, ih, upS_var]
  | app M V ih1 ih2 => simp [CT.subst, ih1, ih2]

/-- Substituting into a shifted term cancels the shift. -/
theorem CT.subst1_shift (V M : CT) : (M.ren Nat.succ).subst1 V = M := by
  rw [CT.subst1, CT.subst_ren]
  exact CT.subst_var M

@[simp] theorem CT.subst_cons_shift (V M : CT) : (M.ren Nat.succ).subst (cons V CT.var) = M :=
  CT.subst1_shift V M

/-! ### Typing -/

/-- **The CBPV typing judgement**, for values (`Sort'.v A`) and computations (`Sort'.c B`). -/
inductive CTyp : List VTy → CT → Sort' → Prop
  | var {Γ : List VTy} {n : ℕ} {A : VTy} : Γ[n]? = some A → CTyp Γ (.var n) (.v A)
  | thunk {Γ : List VTy} {M : CT} {B : CTy} : CTyp Γ M (.c B) → CTyp Γ (.thunk M) (.v (.U B))
  | force {Γ : List VTy} {V : CT} {B : CTy} : CTyp Γ V (.v (.U B)) → CTyp Γ (.force V) (.c B)
  | ret {Γ : List VTy} {V : CT} {A : VTy} : CTyp Γ V (.v A) → CTyp Γ (.ret V) (.c (.F A))
  | bind {Γ : List VTy} {M N : CT} {A : VTy} {B : CTy} :
      CTyp Γ M (.c (.F A)) → CTyp (A :: Γ) N (.c B) → CTyp Γ (.bind M N) (.c B)
  | lam {Γ : List VTy} {M : CT} {A : VTy} {B : CTy} :
      CTyp (A :: Γ) M (.c B) → CTyp Γ (.lam M) (.c (.arr A B))
  | app {Γ : List VTy} {M V : CT} {A : VTy} {B : CTy} :
      CTyp Γ M (.c (.arr A B)) → CTyp Γ V (.v A) → CTyp Γ (.app M V) (.c B)

theorem CTyp.ren {Γ : List VTy} {M : CT} {T : Sort'} (h : CTyp Γ M T) :
    ∀ {Δ : List VTy} {ξ : ℕ → ℕ}, (∀ n A, Γ[n]? = some A → Δ[ξ n]? = some A) →
      CTyp Δ (M.ren ξ) T := by
  induction h with
  | var hn => intro Δ ξ hξ; exact .var (hξ _ _ hn)
  | thunk _ ih => intro Δ ξ hξ; exact .thunk (ih hξ)
  | force _ ih => intro Δ ξ hξ; exact .force (ih hξ)
  | ret _ ih => intro Δ ξ hξ; exact .ret (ih hξ)
  | bind _ _ ih1 ih2 =>
      intro Δ ξ hξ
      refine .bind (ih1 hξ) (ih2 ?_)
      intro n A hn
      cases n with
      | zero => exact hn
      | succ n => exact hξ n A hn
  | lam _ ih =>
      intro Δ ξ hξ
      refine .lam (ih ?_)
      intro n A hn
      cases n with
      | zero => exact hn
      | succ n => exact hξ n A hn
  | app _ _ ih1 ih2 => intro Δ ξ hξ; exact .app (ih1 hξ) (ih2 hξ)

/-! ### Reduction -/

/-- **CBPV reduction** (evaluation of computations). -/
inductive CStep : CT → CT → Prop
  | force (M : CT) : CStep (.force (.thunk M)) M
  | bindRet (V N : CT) : CStep (.bind (.ret V) N) (N.subst1 V)
  | beta (M V : CT) : CStep (.app (.lam M) V) (M.subst1 V)
  | bind {M M' : CT} (N : CT) : CStep M M' → CStep (.bind M N) (.bind M' N)
  | app {M M' : CT} (V : CT) : CStep M M' → CStep (.app M V) (.app M' V)

/-- **Administrative contraction** `force (thunk M) ⇝ M`, anywhere in a term. -/
inductive Admin : CT → CT → Prop
  | force (M : CT) : Admin (.force (.thunk M)) M
  | thunk {M M' : CT} : Admin M M' → Admin (.thunk M) (.thunk M')
  | forceC {M M' : CT} : Admin M M' → Admin (.force M) (.force M')
  | ret {M M' : CT} : Admin M M' → Admin (.ret M) (.ret M')
  | bindL {M M' : CT} (N : CT) : Admin M M' → Admin (.bind M N) (.bind M' N)
  | bindR (M : CT) {N N' : CT} : Admin N N' → Admin (.bind M N) (.bind M N')
  | lam {M M' : CT} : Admin M M' → Admin (.lam M) (.lam M')
  | appL {M M' : CT} (V : CT) : Admin M M' → Admin (.app M V) (.app M' V)
  | appR (M : CT) {V V' : CT} : Admin V V' → Admin (.app M V) (.app M V')

/-! ### The source calculus -/

/-- Simple types. -/
inductive STy where
  | base : STy
  | arr : STy → STy → STy

/-- Source terms. -/
inductive STm where
  | var : ℕ → STm
  | lam : STm → STm
  | app : STm → STm → STm

/-- Source typing. -/
inductive STyp : List STy → STm → STy → Prop
  | var {Γ : List STy} {n : ℕ} {A : STy} : Γ[n]? = some A → STyp Γ (.var n) A
  | lam {Γ : List STy} {t : STm} {A B : STy} : STyp (A :: Γ) t B → STyp Γ (.lam t) (.arr A B)
  | app {Γ : List STy} {t u : STm} {A B : STy} :
      STyp Γ t (.arr A B) → STyp Γ u A → STyp Γ (.app t u) B

/-- Source renaming. -/
def STm.ren (ξ : ℕ → ℕ) : STm → STm
  | var n => var (ξ n)
  | lam t => lam (t.ren (up ξ))
  | app t u => app (t.ren ξ) (u.ren ξ)

/-- Lifting a source substitution. -/
def upSS (σ : ℕ → STm) : ℕ → STm
  | 0 => .var 0
  | n + 1 => (σ n).ren Nat.succ

/-- Source substitution. -/
def STm.subst (σ : ℕ → STm) : STm → STm
  | var n => σ n
  | lam t => lam (t.subst (upSS σ))
  | app t u => app (t.subst σ) (u.subst σ)

/-- Source values (for call-by-value): variables and abstractions. -/
def STm.IsVal : STm → Prop
  | var _ => True
  | lam _ => True
  | app _ _ => False

/-- **Call-by-name (weak head) reduction.** -/
inductive NStep : STm → STm → Prop
  | beta (t u : STm) : NStep (.app (.lam t) u) (t.subst (cons u STm.var))
  | appL {t t' : STm} (u : STm) : NStep t t' → NStep (.app t u) (.app t' u)

/-- **Call-by-value reduction.** -/
inductive VStep : STm → STm → Prop
  | beta (t w : STm) : w.IsVal → VStep (.app (.lam t) w) (t.subst (cons w STm.var))
  | appL {t t' : STm} (u : STm) : VStep t t' → VStep (.app t u) (.app t' u)
  | appR {w u u' : STm} : w.IsVal → VStep u u' → VStep (.app w u) (.app w u')

/-! ### The call-by-name translation -/

/-- Call-by-name types: a computation type. -/
def tyN : STy → CTy
  | .base => .F .base
  | .arr A B => .arr (.U (tyN A)) (tyN B)

/-- **The call-by-name translation**: `x ↦ force x`, `λx.t ↦ λx.t`, `t u ↦ t (thunk u)`. -/
def tn : STm → CT
  | .var n => .force (.var n)
  | .lam t => .lam (tn t)
  | .app t u => .app (tn t) (.thunk (tn u))

/-- **The call-by-name translation preserves typing.** -/
theorem tn_typing {Γ : List STy} {t : STm} {A : STy} (h : STyp Γ t A) :
    CTyp (Γ.map fun A => .U (tyN A)) (tn t) (.c (tyN A)) := by
  induction h with
  | var hn => exact .force (.var (by simp [hn]))
  | lam _ ih => exact .lam ih
  | app _ _ ih1 ih2 => exact .app ih1 (.thunk ih2)

theorem tn_ren (t : STm) : ∀ ξ : ℕ → ℕ, tn (t.ren ξ) = (tn t).ren ξ := by
  induction t with
  | var n => intro; rfl
  | lam t ih => intro ξ; simp [tn, STm.ren, CT.ren, ih]
  | app t u ih1 ih2 => intro ξ; simp [tn, STm.ren, CT.ren, ih1, ih2]

/-- `τ` represents the source substitution `σ` under the call-by-name translation. -/
def RepN (τ : ℕ → CT) (σ : ℕ → STm) : Prop :=
  ∀ n, τ n = .thunk (tn (σ n)) ∨ ∃ m, τ n = .var m ∧ σ n = .var m

theorem RepN.up {τ : ℕ → CT} {σ : ℕ → STm} (h : RepN τ σ) : RepN (upS τ) (upSS σ) := by
  intro n
  cases n with
  | zero => exact Or.inr ⟨0, rfl, rfl⟩
  | succ n =>
      rcases h n with h | ⟨m, h1, h2⟩
      · left; simp [upS, upSS, h, CT.ren, tn_ren]
      · right; exact ⟨m + 1, by simp [upS, h1, CT.ren], by simp [upSS, h2, STm.ren]⟩

theorem admin_star_lam {M M' : CT} (h : Relation.ReflTransGen Admin M M') :
    Relation.ReflTransGen Admin (.lam M) (.lam M') :=
  Relation.ReflTransGen.lift CT.lam (fun _ _ => Admin.lam) _ _ h

theorem admin_star_app {M M' V V' : CT} (h : Relation.ReflTransGen Admin M M')
    (h' : Relation.ReflTransGen Admin V V') :
    Relation.ReflTransGen Admin (.app M V) (.app M' V') :=
  (Relation.ReflTransGen.lift (fun M => CT.app M V) (fun _ _ => Admin.appL V) _ _ h).trans
    (Relation.ReflTransGen.lift (CT.app M') (fun _ _ => Admin.appR M') _ _ h')

theorem admin_star_thunk {M M' : CT} (h : Relation.ReflTransGen Admin M M') :
    Relation.ReflTransGen Admin (.thunk M) (.thunk M') :=
  Relation.ReflTransGen.lift CT.thunk (fun _ _ => Admin.thunk) _ _ h

/-- Substitution commutes with the call-by-name translation, up to administrative contractions. -/
theorem tn_subst (t : STm) : ∀ (τ : ℕ → CT) (σ : ℕ → STm), RepN τ σ →
    Relation.ReflTransGen Admin ((tn t).subst τ) (tn (t.subst σ)) := by
  induction t with
  | var n =>
      intro τ σ h
      rcases h n with h | ⟨m, h1, h2⟩
      · simp only [tn, CT.subst, h, STm.subst]
        exact Relation.ReflTransGen.single (Admin.force _)
      · simp only [tn, CT.subst, h1, STm.subst, h2]
        exact Relation.ReflTransGen.refl
  | lam t ih => intro τ σ h; exact admin_star_lam (ih _ _ h.up)
  | app t u ih1 ih2 =>
      intro τ σ h
      exact admin_star_app (ih1 τ σ h) (admin_star_thunk (ih2 τ σ h))

/-- **Call-by-name simulation**: a source step is one CBPV step followed by administrative
contractions. -/
theorem tn_sim {t t' : STm} (h : NStep t t') :
    ∃ M, CStep (tn t) M ∧ Relation.ReflTransGen Admin M (tn t') := by
  induction h with
  | beta t u =>
      refine ⟨_, CStep.beta _ _, tn_subst t _ _ ?_⟩
      intro n
      cases n with
      | zero => exact Or.inl rfl
      | succ n => exact Or.inr ⟨n, rfl, rfl⟩
  | appL u _ ih =>
      obtain ⟨M, h1, h2⟩ := ih
      exact ⟨_, CStep.app _ h1, admin_star_app h2 Relation.ReflTransGen.refl⟩

/-! ### The call-by-value translation -/

/-- Call-by-value types: a value type. -/
def tyV : STy → VTy
  | .base => .base
  | .arr A B => .U (.arr (tyV A) (.F (tyV B)))

/-- **The call-by-value translation** of terms (`tv`), with the value translation `val` of
source values: `x ↦ ret x`, `λx.t ↦ ret (thunk (λx. t))`,
`t u ↦ t to f. (u to x. (force f) x)`. -/
def tv : STm → CT
  | .var n => .ret (.var n)
  | .lam t => .ret (.thunk (.lam (tv t)))
  | .app t u => .bind (tv t) (.bind ((tv u).ren Nat.succ) (.app (.force (.var 1)) (.var 0)))

/-- The value a source value translates to. -/
def val : STm → CT
  | .var n => .var n
  | .lam t => .thunk (.lam (tv t))
  | .app _ _ => .var 0

theorem tv_of_isVal {w : STm} (hw : w.IsVal) : tv w = .ret (val w) := by
  cases w with
  | var n => rfl
  | lam t => rfl
  | app _ _ => exact absurd hw id

/-- **The call-by-value translation preserves typing.** -/
theorem tv_typing {Γ : List STy} {t : STm} {A : STy} (h : STyp Γ t A) :
    CTyp (Γ.map tyV) (tv t) (.c (.F (tyV A))) := by
  induction h with
  | var hn => exact .ret (.var (by simp [hn]))
  | lam _ ih => exact .ret (.thunk (.lam ih))
  | app _ _ ih1 ih2 =>
      refine .bind ih1 (.bind (ih2.ren fun n A hn => hn) (.app (.force (.var rfl)) (.var rfl)))

theorem tv_ren (t : STm) : ∀ ξ : ℕ → ℕ, tv (t.ren ξ) = (tv t).ren ξ := by
  induction t with
  | var n => intro; rfl
  | lam t ih => intro ξ; simp [tv, STm.ren, CT.ren, ih]
  | app t u ih1 ih2 =>
      intro ξ
      simp only [tv, STm.ren, CT.ren, ih1, ih2, CT.ren_ren]
      rfl

theorem val_ren (w : STm) (ξ : ℕ → ℕ) (hw : w.IsVal) : val (w.ren ξ) = (val w).ren ξ := by
  cases w with
  | var n => rfl
  | lam t => simp [val, STm.ren, CT.ren, tv_ren]
  | app _ _ => exact absurd hw id

theorem isVal_ren {w : STm} (ξ : ℕ → ℕ) (hw : w.IsVal) : (w.ren ξ).IsVal := by
  cases w with
  | var n => trivial
  | lam t => trivial
  | app _ _ => exact absurd hw id

/-- Substitution of values commutes with the call-by-value translation. -/
theorem tv_subst (t : STm) : ∀ σ : ℕ → STm, (∀ n, (σ n).IsVal) →
    tv (t.subst σ) = (tv t).subst (val ∘ σ) := by
  induction t with
  | var n => intro σ hσ; simp [STm.subst, tv, CT.subst, tv_of_isVal (hσ n)]
  | lam t ih =>
      intro σ hσ
      have hσ' : ∀ n, (upSS σ n).IsVal := by
        intro n; cases n with
        | zero => trivial
        | succ n => exact isVal_ren _ (hσ n)
      have hup : val ∘ upSS σ = upS (val ∘ σ) := by
        funext n; cases n with
        | zero => rfl
        | succ n => exact val_ren _ _ (hσ n)
      simp [STm.subst, tv, CT.subst, ih _ hσ', hup]
  | app t u ih1 ih2 =>
      intro σ hσ
      simp only [STm.subst, tv, CT.subst, ih1 σ hσ, ih2 σ hσ, CT.ren_subst, CT.subst_ren]
      rfl

/-- **Call-by-value β is simulated by exactly four CBPV steps.** -/
theorem tv_beta (t w : STm) (hw : w.IsVal) :
    Relation.TransGen CStep (tv (.app (.lam t) w)) (tv (t.subst (cons w STm.var))) := by
  set V := CT.thunk (.lam (tv t))
  have h1 : CStep (tv (.app (.lam t) w))
      (.bind (tv w) (.app (.force (V.ren Nat.succ)) (.var 0))) := by
    have := CStep.bindRet V (.bind ((tv w).ren Nat.succ) (.app (.force (.var 1)) (.var 0)))
    show CStep (.bind (.ret V) (.bind ((tv w).ren Nat.succ) (.app (.force (.var 1)) (.var 0)))) _
    simpa [CT.subst1, CT.subst, upS, cons] using this
  have h2 : CStep (.bind (tv w) (.app (.force (V.ren Nat.succ)) (.var 0)))
      (.app (.force V) (val w)) := by
    rw [tv_of_isVal hw]
    have := CStep.bindRet (val w) (.app (.force (V.ren Nat.succ)) (.var 0))
    simpa [CT.subst1, CT.subst, cons] using this
  have h3 : CStep (.app (.force V) (val w)) (.app (.lam (tv t)) (val w)) :=
    CStep.app _ (CStep.force _)
  have h4 : CStep (.app (.lam (tv t)) (val w)) (tv (t.subst (cons w STm.var))) := by
    have hσ : ∀ n, (cons w STm.var n).IsVal := by
      intro n; cases n with
      | zero => exact hw
      | succ n => trivial
    have hc : val ∘ cons w STm.var = cons (val w) CT.var := by
      funext n; cases n <;> rfl
    rw [tv_subst t _ hσ, hc]
    exact CStep.beta _ _
  exact .tail (.tail (.tail (.single h1) h2) h3) h4

theorem plus_bind {M M' : CT} (N : CT) (h : Relation.TransGen CStep M M') :
    Relation.TransGen CStep (.bind M N) (.bind M' N) :=
  Relation.TransGen.lift (fun M => CT.bind M N) (fun _ _ => CStep.bind N) _ _ h

theorem star_bind {M M' : CT} (N : CT) (h : Relation.ReflTransGen CStep M M') :
    Relation.ReflTransGen CStep (.bind M N) (.bind M' N) :=
  Relation.ReflTransGen.lift (fun M => CT.bind M N) (fun _ _ => CStep.bind N) _ _ h

/-- **Call-by-value simulation**: if `t → t'` then `tv t →⁺ M` and `tv t' →* M` for some `M`. -/
theorem tv_sim {t t' : STm} (h : VStep t t') :
    ∃ M, Relation.TransGen CStep (tv t) M ∧ Relation.ReflTransGen CStep (tv t') M := by
  induction h with
  | beta t w hw => exact ⟨_, tv_beta t w hw, Relation.ReflTransGen.refl⟩
  | appL u _ ih =>
      obtain ⟨M, h1, h2⟩ := ih
      exact ⟨_, plus_bind _ h1, star_bind _ h2⟩
  | @appR w u u' hw _ ih =>
      obtain ⟨M, h1, h2⟩ := ih
      set K := CT.app (.force ((val w).ren Nat.succ)) (.var 0)
      have hstep : ∀ v : STm, CStep (tv (.app w v)) (.bind (tv v) K) := by
        intro v
        rw [tv, tv_of_isVal hw]
        have := CStep.bindRet (val w) (.bind ((tv v).ren Nat.succ)
          (.app (.force (.var 1)) (.var 0)))
        simpa [CT.subst1, CT.subst, upS, cons, K] using this
      exact ⟨_, .head (hstep u) (plus_bind K h1),
        .head (hstep u') (star_bind K h2)⟩

end CBPV
