/-
**Hindley–Milner embeds in System F.**  Every term typable in Hindley–Milner
(`Start/HindleyMilner.lean`) is typable in Curry-style System F (`Start/SystemF.lean`), after
erasing `let x = a in b` to the β-redex `(λx. b) a`, monotypes to System F types, and each type
scheme `∀ᾱ. τ` to the prefix of universal quantifiers `∀ᾱ. τ`.

* `HM.erase` — mini-ML terms to untyped λ-terms;
* `HM.tyF`, `HM.schF` — monotypes and schemes to System F types: a scheme with bound variables
  below `K = σ.bnd` becomes `K` quantifiers, its bound variable `k` the de Bruijn index `k` and
  its free variable `v` the index `K + v`; type constants are sent to the closed type `∀α. α`;
* `HM.typing_systemF` — **the embedding**: `Γ ⊢ e : τ` in Hindley–Milner implies
  `schF Γ ⊢ erase e : tyF τ` in System F.

The two System F facts used are that `K` quantifiers may be instantiated all at once
(`HM.typing_allN_inst`) and introduced all at once over a context weakened `K` times
(`HM.typing_allN_gen`).  The `let` case is the only real one: the generalization of the type of
the bound term is obtained by substituting the System F typing of that term
(`SystemF.Typing.substTy`).  As a consequence, every HM-typable term is strongly normalizing, by
`SystemF.sn_of_typing`.
-/

import Start.HindleyMilner
import Start.SystemFSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace HM

open SystemF

/-! ### Blocks of quantifiers -/

/-- `allN K A` is `∀ ... ∀. A` with `K` quantifiers; the innermost binds index `0`. -/
def allN : ℕ → FTy → FTy
  | 0, A => A
  | K + 1, A => allN K (FTy.all A)

/-- Weakening a System F type by `K` type variables. -/
def shiftN (K : ℕ) (A : FTy) : FTy := tySubst (fun i => FTy.var (i + K)) A

/-- Lifting a substitution under `K` quantifiers. -/
def upsN : ℕ → (ℕ → FTy) → ℕ → FTy
  | 0, s => s
  | K + 1, s => ups (upsN K s)

theorem tySubst_allN (K : ℕ) (s : ℕ → FTy) (A : FTy) :
    tySubst s (allN K A) = allN K (tySubst (upsN K s) A) := by
  induction K generalizing A with
  | zero => rfl
  | succ K ih => simp only [allN, ih]; rfl

theorem shiftN_succ (K : ℕ) (A : FTy) : tyShift (shiftN K A) = shiftN (K + 1) A := by
  rw [shiftN, shiftN, tyShift_eq_tySubst, tySubst_tySubst]
  rfl

theorem upsN_apply (K : ℕ) (s : ℕ → FTy) (i : ℕ) :
    upsN K s i = if i < K then FTy.var i else shiftN K (s (i - K)) := by
  induction K generalizing i with
  | zero =>
    simp only [upsN, Nat.not_lt_zero, if_false, Nat.sub_zero, shiftN, Nat.add_zero]
    exact (tySubst_var_id _).symm
  | succ K ih =>
    cases i with
    | zero => simp [upsN, ups]
    | succ j =>
      simp only [upsN, ups, ih]
      by_cases hj : j < K
      · simp [hj, tyShift, tyRename]
      · have : ¬ j + 1 < K + 1 := by omega
        simp only [hj, if_false, this, shiftN_succ]
        congr 2
        omega

/-- **Instantiating a block of quantifiers** at once. -/
theorem typing_allN_inst {Γ : List FTy} {t : Lambda} (K : ℕ) :
    ∀ {A : FTy}, SystemF.Typing Γ t (allN K A) → ∀ ts : ℕ → FTy,
      SystemF.Typing Γ t (tySubst (fun i => if i < K then ts i else FTy.var (i - K)) A) := by
  induction K with
  | zero =>
    intro A h ts
    have : (fun i => if i < 0 then ts i else FTy.var (i - 0)) = FTy.var := by funext i; simp
    rw [this, tySubst_var_id]
    exact h
  | succ K ih =>
    intro A h ts
    have h1 := ih h (fun i => ts (i + 1))
    have h2 := SystemF.Typing.tapp (ts 0) h1
    rw [tyInst, tySubst_tySubst] at h2
    convert h2 using 2
    funext i
    cases i with
    | zero => simp [ups]; rfl
    | succ j =>
      change _ = tySubst (tyScons (ts 0)) (tyShift _)
      rw [← tyInst, tyInst_tyShift]
      by_cases hj : j < K
      · simp [hj]
      · have : ¬ j + 1 < K + 1 := by omega
        simp only [hj, this, if_false]
        congr 1
        omega

/-- **Introducing a block of quantifiers** at once. -/
theorem typing_allN_gen {Γ : List FTy} {t : Lambda} (K : ℕ) :
    ∀ {A : FTy}, SystemF.Typing (Γ.map (shiftN K)) t A → SystemF.Typing Γ t (allN K A) := by
  induction K with
  | zero =>
    intro A h
    have : Γ.map (shiftN 0) = Γ := by
      conv_rhs => rw [← List.map_id Γ]
      exact List.map_congr_left fun X _ => by simpa [shiftN] using tySubst_var_id X
    rwa [this] at h
  | succ K ih =>
    intro A h
    refine ih (SystemF.Typing.tlam ?_)
    rw [List.map_map]
    convert h using 2
    funext X
    exact shiftN_succ K X

/-! ### The translation -/

/-- Monotypes as System F types; constants go to the closed type `∀α. α`. -/
def tyF : Ty → FTy
  | Ty.var v => FTy.var v
  | Ty.con _ => FTy.all (FTy.var 0)
  | Ty.arrow a b => FTy.arrow (tyF a) (tyF b)

/-- The body of a scheme, with its free variables sent by `f` and bound ones by `b`. -/
def bodyF (f b : ℕ → FTy) : Sch → FTy
  | Sch.fv v => f v
  | Sch.bv k => b k
  | Sch.con _ => FTy.all (FTy.var 0)
  | Sch.arrow x y => FTy.arrow (bodyF f b x) (bodyF f b y)

/-- A scheme as a System F type: a block of `σ.bnd` quantifiers. -/
def schF (σ : Sch) : FTy := allN σ.bnd (bodyF (fun v => FTy.var (σ.bnd + v)) FTy.var σ)

theorem tySubst_bodyF (g f b : ℕ → FTy) (σ : Sch) :
    tySubst g (bodyF f b σ) = bodyF (fun v => tySubst g (f v)) (fun k => tySubst g (b k)) σ := by
  induction σ with
  | fv v => rfl
  | bv k => rfl
  | con c => rfl
  | arrow x y ihx ihy => simp [bodyF, tySubst, ihx, ihy]

theorem bodyF_congr {f f' b b' : ℕ → FTy} {σ : Sch} (hf : ∀ v ∈ σ.fvs, f v = f' v)
    (hb : ∀ k < σ.bnd, b k = b' k) : bodyF f b σ = bodyF f' b' σ := by
  induction σ with
  | fv v => exact hf v (by simp [Sch.fvs])
  | bv k => exact hb k (by simp [Sch.bnd])
  | con c => rfl
  | arrow x y ihx ihy =>
    simp only [bodyF, FTy.arrow.injEq]
    exact ⟨ihx (fun v hv => hf v (by simp [Sch.fvs, hv]))
        (fun k hk => hb k (lt_of_lt_of_le hk (by simp [Sch.bnd]))),
      ihy (fun v hv => hf v (by simp [Sch.fvs, hv]))
        (fun k hk => hb k (lt_of_lt_of_le hk (by simp [Sch.bnd])))⟩

theorem tyF_inst2 (f ts : ℕ → Ty) (σ : Sch) :
    tyF (σ.inst2 f ts) = bodyF (fun v => tyF (f v)) (fun k => tyF (ts k)) σ := by
  induction σ with
  | fv v => rfl
  | bv k => rfl
  | con c => rfl
  | arrow x y ihx ihy => simp [Sch.inst2, tyF, bodyF, ihx, ihy]

theorem bnd_ofTy (t : Ty) : (Sch.ofTy t).bnd = 0 := by
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [Sch.ofTy, Sch.bnd, iha, ihb]

theorem schF_ofTy (t : Ty) : schF (Sch.ofTy t) = tyF t := by
  rw [schF, bnd_ofTy]
  simp only [allN, Nat.zero_add]
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [Sch.ofTy, bodyF, tyF, iha, ihb]

/-- Substituting the free variables of a translated scheme. -/
theorem tySubst_schF (g : ℕ → FTy) (σ : Sch) :
    tySubst g (schF σ) = allN σ.bnd (bodyF (fun v => shiftN σ.bnd (g v)) FTy.var σ) := by
  rw [schF, tySubst_allN, tySubst_bodyF]
  congr 1
  apply bodyF_congr
  · intro v _
    change upsN σ.bnd g (σ.bnd + v) = _
    rw [upsN_apply, if_neg (by omega), Nat.add_sub_cancel_left]
  · intro k hk
    change upsN σ.bnd g k = _
    rw [upsN_apply, if_pos hk]

/-- The erasure of a mini-ML term: `let x = a in b` becomes `(λx. b) a`. -/
def erase : Expr → Lambda
  | Expr.var i => Lambda.var i
  | Expr.app a b => Lambda.app (erase a) (erase b)
  | Expr.lam t => Lambda.lam (erase t)
  | Expr.let_ a b => Lambda.app (Lambda.lam (erase b)) (erase a)

/-- The generalization of a monotype, translated, is a substitution instance of the
translation of the monotype. -/
theorem tySubst_tyF_gen (A : Finset ℕ) (K : ℕ) (t : Ty) :
    tySubst (fun v => if v ∈ A then FTy.var (K + v) else FTy.var v) (tyF t) =
      bodyF (fun v => FTy.var (K + v)) FTy.var (gen' A t) := by
  induction t with
  | var v => by_cases h : v ∈ A <;> simp [tyF, gen', h, tySubst, bodyF]
  | con c => rfl
  | arrow a b iha ihb => simp [tyF, gen', tySubst, bodyF, iha, ihb]

/-- **Every Hindley–Milner typing is a System F typing** of the erased term, with the schemes
erased to prefixes of universal quantifiers. -/
theorem typing_systemF {Γ : List Sch} {e : Expr} {τ : Ty} (h : HM.Typing Γ e τ) :
    SystemF.Typing (Γ.map schF) (erase e) (tyF τ) := by
  induction h with
  | @var Γ i σ ts hi =>
    have h0 : SystemF.Typing (Γ.map schF) (Lambda.var i) (schF σ) :=
      SystemF.Typing.var (by simp [hi])
    have h1 := typing_allN_inst σ.bnd h0 (fun k => tyF (ts k))
    rw [tySubst_bodyF] at h1
    change SystemF.Typing _ (Lambda.var i) _
    convert h1 using 1
    unfold Sch.inst
    rw [tyF_inst2]
    apply bodyF_congr
    · intro v _; simp [tySubst, tyF]
    · intro k hk; simp [tySubst, hk]
  | app _ _ iha ihb => exact SystemF.Typing.app iha ihb
  | lam _ ih =>
    refine SystemF.Typing.lam ?_
    simpa [schF_ofTy] using ih
  | @let_ Γ a b A B _ _ iha ihb =>
    refine SystemF.Typing.app (SystemF.Typing.lam ihb) ?_
    set K := (gen Γ A).bnd
    refine typing_allN_gen K ?_
    change SystemF.Typing _ _ (bodyF (fun v => FTy.var (K + v)) FTy.var (gen' (ctxFvs Γ) A))
    have h1 := iha.substTy fun v => if v ∈ ctxFvs Γ then FTy.var (K + v) else FTy.var v
    rw [tySubst_tyF_gen] at h1
    convert h1 using 1
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro σ hσ
    simp only [Function.comp_apply, shiftN, tySubst_schF]
    congr 1
    apply bodyF_congr _ (fun _ _ => rfl)
    intro v hv
    have : v ∈ ctxFvs Γ := mem_ctxFvs.2 ⟨σ, hσ, hv⟩
    simp only [this, if_true, tySubst]
    congr 1
    omega

/-- Consequently every Hindley–Milner typable term is strongly normalizing. -/
theorem sn_of_typing {Γ : List Sch} {e : Expr} {τ : Ty} (h : HM.Typing Γ e τ) :
    Lambda.SN (erase e) :=
  SystemF.sn_of_typing (typing_systemF h)

end HM
