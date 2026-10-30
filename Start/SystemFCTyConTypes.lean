/-
**Types and coercions of System FC with data types** (task `M25-SYSTEM-FC-TYCON`, part 1).

The type language of `Start/SystemFCoerce.lean` extended by type constructors and type-level
application, with its substitution calculus, and the coercion language extended by application
coercions, their decompositions and axiom schemes over constructor applications.

* `FCTyCon.Ty` — type variables, `→`, `∀`, type constructors `con T` and application `app A B`;
  `tapps T σ` is the constructor application `T σ₁ ⋯ σₙ` (the list is stored last argument first);
* `FCTyCon.listSub σ` — the substitution of the parameters `0, 1, …` by the list `σ`;
  `FCTyCon.Scoped n A` — the free type variables of `A` are below `n`;
* `FCTyCon.Co` — coercions: `refl`, `sym`, `trans`, `arr`, `all`, `inst`, the axiom instance
  `ax i σ`, the arrow decompositions `left`/`right`, the **application coercion** `capp γ δ`
  and its decompositions `appL`/`appR`; `FCTyCon.nthCo γ j` is the `j`-th argument decomposition of
  a coercion between two constructor applications (`nth` of FC);
* `FCTyCon.CoTyping Ax γ A B` — `γ : A ~ B`; an axiom `(n, l, r)` is a scheme over `n` parameters
  and `ax i σ : l[σ] ~ r[σ]` (type-family instances and newtype axioms);
* `FCTyCon.CoTyping.substTy` — stability of coercion typing under type substitution, for
  well-scoped axiom schemes (`AxOK`);
* `FCTyCon.liftCo A cs` — the lifting of a type to a coercion, and `CoTyping.liftCo`:
  `liftCo A cs : A[s] ~ A[s']` when every `cs i : s i ~ s' i`; `CoTyping.nthCo` and
  `CoTyping.conCo` — `T γ₁ ⋯ γₙ : T σ ~ T ρ` and its decompositions `nth j : σⱼ ~ ρⱼ`.
-/

import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FCTyCon

/-! ### Types -/

/-- Types of System FC with type constructors. -/
inductive Ty where
  /-- A type variable. -/
  | var : ℕ → Ty
  /-- A function type. -/
  | arrow : Ty → Ty → Ty
  /-- A universally quantified type. -/
  | all : Ty → Ty
  /-- A type constructor. -/
  | con : ℕ → Ty
  /-- Type-level application. -/
  | app : Ty → Ty → Ty
  deriving DecidableEq

/-- Lifting a renaming under a binder. -/
def upr (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming the type variables of a type. -/
def tyRename (r : ℕ → ℕ) : Ty → Ty
  | .var i => .var (r i)
  | .arrow A B => .arrow (tyRename r A) (tyRename r B)
  | .all A => .all (tyRename (upr r) A)
  | .con T => .con T
  | .app A B => .app (tyRename r A) (tyRename r B)

/-- Weakening by one type variable. -/
def tyShift (A : Ty) : Ty := tyRename Nat.succ A

/-- Lifting a substitution under a binder. -/
def ups (s : ℕ → Ty) : ℕ → Ty
  | 0 => .var 0
  | n + 1 => tyShift (s n)

/-- Substituting the type variables of a type. -/
def tySubst (s : ℕ → Ty) : Ty → Ty
  | .var i => s i
  | .arrow A B => .arrow (tySubst s A) (tySubst s B)
  | .all A => .all (tySubst (ups s) A)
  | .con T => .con T
  | .app A B => .app (tySubst s A) (tySubst s B)

/-- Extending a substitution at index `0`. -/
def tyCons (D : Ty) (s : ℕ → Ty) : ℕ → Ty
  | 0 => D
  | n + 1 => s n

/-- Instantiating the outermost bound type variable. -/
def tyInst (B A : Ty) : Ty := tySubst (tyCons B Ty.var) A

theorem tyRename_tyRename (r r' : ℕ → ℕ) (A : Ty) :
    tyRename r (tyRename r' A) = tyRename (fun i => r (r' i)) A := by
  induction A generalizing r r' with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, ihA, ihB]
  | all A ih =>
      simp only [tyRename, ih]
      have h : (fun i => upr r (upr r' i)) = upr (fun i => r (r' i)) := by
        funext i; cases i <;> rfl
      rw [h]
  | con T => rfl
  | app A B ihA ihB => simp only [tyRename, ihA, ihB]

theorem tySubst_tyRename (s : ℕ → Ty) (r : ℕ → ℕ) (A : Ty) :
    tySubst s (tyRename r A) = tySubst (fun i => s (r i)) A := by
  induction A generalizing s r with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]
  | all A ih =>
      simp only [tyRename, tySubst, ih]
      have h : (fun i => ups s (upr r i)) = ups (fun i => s (r i)) := by
        funext i; cases i <;> rfl
      rw [h]
  | con T => rfl
  | app A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]

theorem tyRename_tySubst (r : ℕ → ℕ) (s : ℕ → Ty) (A : Ty) :
    tyRename r (tySubst s A) = tySubst (fun i => tyRename r (s i)) A := by
  induction A generalizing r s with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]
  | all A ih =>
      simp only [tyRename, tySubst, ih]
      have h : (fun i => tyRename (upr r) (ups s i)) = ups (fun i => tyRename r (s i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i =>
            simp only [ups, tyShift, tyRename_tyRename]
            rfl
      rw [h]
  | con T => rfl
  | app A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]

theorem tySubst_tyShift (s : ℕ → Ty) (A : Ty) :
    tySubst (ups s) (tyShift A) = tyShift (tySubst s A) := by
  rw [tyShift, tySubst_tyRename, tyShift, tyRename_tySubst]
  rfl

theorem tySubst_tySubst (s s' : ℕ → Ty) (A : Ty) :
    tySubst s (tySubst s' A) = tySubst (fun i => tySubst s (s' i)) A := by
  induction A generalizing s s' with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tySubst, ihA, ihB]
  | all A ih =>
      simp only [tySubst, ih]
      have h : (fun i => tySubst (ups s) (ups s' i)) = ups (fun i => tySubst s (s' i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i => exact tySubst_tyShift s (s' i)
      rw [h]
  | con T => rfl
  | app A B ihA ihB => simp only [tySubst, ihA, ihB]

theorem tySubst_var_id (A : Ty) : tySubst Ty.var A = A := by
  induction A with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tySubst, ihA, ihB]
  | all A ih =>
      have h : ups Ty.var = Ty.var := by
        funext i; cases i <;> rfl
      simp only [tySubst, h, ih]
  | con T => rfl
  | app A B ihA ihB => simp only [tySubst, ihA, ihB]

theorem tySubst_tyCons_tyShift (D : Ty) (s : ℕ → Ty) (A : Ty) :
    tySubst (tyCons D s) (tyShift A) = tySubst s A := by
  rw [tyShift, tySubst_tyRename]
  rfl

theorem tyInst_tyShift (B A : Ty) : tyInst B (tyShift A) = A := by
  rw [tyInst, tySubst_tyCons_tyShift, tySubst_var_id]

theorem tyRename_eq_tySubst (r : ℕ → ℕ) (A : Ty) :
    tyRename r A = tySubst (fun i => Ty.var (r i)) A := by
  induction A generalizing r with
  | var i => rfl
  | arrow A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]
  | all A ih =>
      have h : ups (fun i => Ty.var (r i)) = fun i => Ty.var (upr r i) := by
        funext i; cases i <;> rfl
      simp only [tyRename, tySubst, ih, h]
  | con T => rfl
  | app A B ihA ihB => simp only [tyRename, tySubst, ihA, ihB]

theorem tyShift_eq_tySubst (A : Ty) : tyShift A = tySubst (fun i => Ty.var (i + 1)) A :=
  tyRename_eq_tySubst Nat.succ A

theorem tySubst_tyInst (s : ℕ → Ty) (B A : Ty) :
    tySubst s (tyInst B A) = tyInst (tySubst s B) (tySubst (ups s) A) := by
  rw [tyInst, tyInst, tySubst_tySubst, tySubst_tySubst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ i =>
      change tySubst s (Ty.var i) = tySubst (tyCons (tySubst s B) Ty.var) (tyShift (s i))
      rw [tySubst_tyCons_tyShift, tySubst_var_id]
      rfl

/-! ### Constructor applications, parameter substitution and scoping -/

/-- The constructor application `T σ₁ ⋯ σₙ`; the list is stored last argument first. -/
def tapps (T : ℕ) : List Ty → Ty
  | [] => .con T
  | A :: σ => .app (tapps T σ) A

theorem tySubst_tapps (s : ℕ → Ty) (T : ℕ) (σ : List Ty) :
    tySubst s (tapps T σ) = tapps T (σ.map (tySubst s)) := by
  induction σ with
  | nil => rfl
  | cons A σ ih => simp only [tapps, tySubst, ih, List.map_cons]

/-- The substitution of the parameters `0, 1, …` by a list (junk `var 0` beyond its length). -/
def listSub (σ : List Ty) (i : ℕ) : Ty := σ.getD i (.var 0)

/-- The free type variables of `A` are below `n`. -/
def Scoped : ℕ → Ty → Prop
  | n, .var i => i < n
  | n, .arrow A B => Scoped n A ∧ Scoped n B
  | n, .all A => Scoped (n + 1) A
  | _, .con _ => True
  | n, .app A B => Scoped n A ∧ Scoped n B

theorem tySubst_congr_scoped : ∀ (A : Ty) (n : ℕ) (s s' : ℕ → Ty), Scoped n A →
    (∀ i, i < n → s i = s' i) → tySubst s A = tySubst s' A
  | .var i, _, _, _, h, hs => hs i h
  | .arrow A B, n, s, s', h, hs => by
      simp only [tySubst, tySubst_congr_scoped A n s s' h.1 hs,
        tySubst_congr_scoped B n s s' h.2 hs]
  | .all A, n, s, s', h, hs => by
      simp only [tySubst]
      rw [tySubst_congr_scoped A (n + 1) (ups s) (ups s') h ?_]
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp only [ups]; rw [hs i (by omega)]
  | .con _, _, _, _, _, _ => rfl
  | .app A B, n, s, s', h, hs => by
      simp only [tySubst, tySubst_congr_scoped A n s s' h.1 hs,
        tySubst_congr_scoped B n s s' h.2 hs]

/-- **Substituting into a parameter instance**, for a well-scoped scheme. -/
theorem tySubst_listSub {n : ℕ} {A : Ty} (hA : Scoped n A) (σ : List Ty) (hσ : σ.length = n)
    (s : ℕ → Ty) :
    tySubst s (tySubst (listSub σ) A) = tySubst (listSub (σ.map (tySubst s))) A := by
  rw [tySubst_tySubst]
  refine tySubst_congr_scoped A n _ _ hA ?_
  intro i hi
  have hi' : i < σ.length := by omega
  simp only [listSub, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
    Option.map_some, Option.getD_some]

/-! ### Coercions -/

/-- Coercions, the evidence of type equalities. -/
inductive Co where
  /-- Reflexivity. -/
  | refl : Ty → Co
  /-- Symmetry. -/
  | sym : Co → Co
  /-- Transitivity. -/
  | trans : Co → Co → Co
  /-- Application of the arrow constructor. -/
  | arr : Co → Co → Co
  /-- Congruence under `∀`. -/
  | all : Co → Co
  /-- Instantiation `γ @ C`. -/
  | inst : Co → Ty → Co
  /-- The instance of the `i`-th axiom scheme at the types `σ`. -/
  | ax : ℕ → List Ty → Co
  /-- Left decomposition of an arrow coercion. -/
  | left : Co → Co
  /-- Right decomposition of an arrow coercion. -/
  | right : Co → Co
  /-- The application coercion `γ δ : A₁ B₁ ~ A₂ B₂`. -/
  | capp : Co → Co → Co
  /-- Left decomposition of an application coercion. -/
  | appL : Co → Co
  /-- Right decomposition of an application coercion. -/
  | appR : Co → Co

/-- Substituting the type variables of a coercion. -/
def substTyCo (s : ℕ → Ty) : Co → Co
  | .refl A => .refl (tySubst s A)
  | .sym γ => .sym (substTyCo s γ)
  | .trans γ δ => .trans (substTyCo s γ) (substTyCo s δ)
  | .arr γ δ => .arr (substTyCo s γ) (substTyCo s δ)
  | .all γ => .all (substTyCo (ups s) γ)
  | .inst γ C => .inst (substTyCo s γ) (tySubst s C)
  | .ax i σ => .ax i (σ.map (tySubst s))
  | .left γ => .left (substTyCo s γ)
  | .right γ => .right (substTyCo s γ)
  | .capp γ δ => .capp (substTyCo s γ) (substTyCo s δ)
  | .appL γ => .appL (substTyCo s γ)
  | .appR γ => .appR (substTyCo s γ)

/-- Axiom schemes: `(n, l, r)` is `∀ α₁ ⋯ αₙ. l ~ r`. -/
abbrev AxSet := List (ℕ × Ty × Ty)

/-- **Coercion typing**: `CoTyping Ax γ A B` is `γ : A ~ B`. -/
inductive CoTyping (Ax : AxSet) : Co → Ty → Ty → Prop
  | refl (A : Ty) : CoTyping Ax (.refl A) A A
  | sym {γ : Co} {A B : Ty} : CoTyping Ax γ A B → CoTyping Ax (.sym γ) B A
  | trans {γ δ : Co} {A B C : Ty} :
      CoTyping Ax γ A B → CoTyping Ax δ B C → CoTyping Ax (.trans γ δ) A C
  | arr {γ δ : Co} {A₁ A₂ B₁ B₂ : Ty} : CoTyping Ax γ A₁ A₂ → CoTyping Ax δ B₁ B₂ →
      CoTyping Ax (.arr γ δ) (.arrow A₁ B₁) (.arrow A₂ B₂)
  | all {γ : Co} {A B : Ty} : CoTyping Ax γ A B → CoTyping Ax (.all γ) (.all A) (.all B)
  | inst {γ : Co} {A B : Ty} (C : Ty) : CoTyping Ax γ (.all A) (.all B) →
      CoTyping Ax (.inst γ C) (tyInst C A) (tyInst C B)
  | ax {i n : ℕ} {l r : Ty} {σ : List Ty} : Ax[i]? = some (n, l, r) → σ.length = n →
      CoTyping Ax (.ax i σ) (tySubst (listSub σ) l) (tySubst (listSub σ) r)
  | left {γ : Co} {A₁ A₂ B₁ B₂ : Ty} :
      CoTyping Ax γ (.arrow A₁ B₁) (.arrow A₂ B₂) → CoTyping Ax (.left γ) A₁ A₂
  | right {γ : Co} {A₁ A₂ B₁ B₂ : Ty} :
      CoTyping Ax γ (.arrow A₁ B₁) (.arrow A₂ B₂) → CoTyping Ax (.right γ) B₁ B₂
  | capp {γ δ : Co} {A₁ A₂ B₁ B₂ : Ty} : CoTyping Ax γ A₁ A₂ → CoTyping Ax δ B₁ B₂ →
      CoTyping Ax (.capp γ δ) (.app A₁ B₁) (.app A₂ B₂)
  | appL {γ : Co} {A₁ A₂ B₁ B₂ : Ty} :
      CoTyping Ax γ (.app A₁ B₁) (.app A₂ B₂) → CoTyping Ax (.appL γ) A₁ A₂
  | appR {γ : Co} {A₁ A₂ B₁ B₂ : Ty} :
      CoTyping Ax γ (.app A₁ B₁) (.app A₂ B₂) → CoTyping Ax (.appR γ) B₁ B₂

/-- The axiom schemes are well scoped: both sides of `(n, l, r)` mention only the `n`
parameters. -/
def AxOK (Ax : AxSet) : Prop := ∀ p ∈ Ax, Scoped p.1 p.2.1 ∧ Scoped p.1 p.2.2

/-- **Coercion typing is stable under type substitution**, for well-scoped axiom schemes. -/
theorem CoTyping.substTy {Ax : AxSet} (hAx : AxOK Ax) {γ : Co} {A B : Ty}
    (h : CoTyping Ax γ A B) :
    ∀ s : ℕ → Ty, CoTyping Ax (substTyCo s γ) (tySubst s A) (tySubst s B) := by
  induction h with
  | refl A => intro s; exact .refl _
  | sym _ ih => intro s; exact .sym (ih s)
  | trans _ _ ih₁ ih₂ => intro s; exact .trans (ih₁ s) (ih₂ s)
  | arr _ _ ih₁ ih₂ => intro s; exact .arr (ih₁ s) (ih₂ s)
  | all _ ih => intro s; exact .all (ih (ups s))
  | inst C _ ih =>
      intro s
      rw [tySubst_tyInst, tySubst_tyInst]
      exact .inst _ (ih s)
  | @ax i n l r σ hi hσ =>
      intro s
      obtain ⟨hl, hr⟩ := hAx (n, l, r) (List.mem_of_getElem? hi)
      rw [tySubst_listSub hl σ hσ, tySubst_listSub hr σ hσ]
      exact .ax hi (by simp [hσ])
  | left _ ih => intro s; exact .left (ih s)
  | right _ ih => intro s; exact .right (ih s)
  | capp _ _ ih₁ ih₂ => intro s; exact .capp (ih₁ s) (ih₂ s)
  | appL _ ih => intro s; exact .appL (ih s)
  | appR _ ih => intro s; exact .appR (ih s)

/-- Weakening the type variables of a coercion. -/
def shiftCo (γ : Co) : Co := substTyCo (fun i => Ty.var (i + 1)) γ

theorem CoTyping.shift {Ax : AxSet} (hAx : AxOK Ax) {γ : Co} {A B : Ty}
    (h : CoTyping Ax γ A B) : CoTyping Ax (shiftCo γ) (tyShift A) (tyShift B) := by
  rw [tyShift_eq_tySubst, tyShift_eq_tySubst]
  exact h.substTy hAx _

/-! ### Lifting types to coercions -/

/-- Lifting a family of coercions under a binder. -/
def upCo (cs : ℕ → Co) : ℕ → Co
  | 0 => .refl (.var 0)
  | n + 1 => shiftCo (cs n)

/-- **The lifting of a type to a coercion**: replace the variable `i` by `cs i`. -/
def liftCo : Ty → (ℕ → Co) → Co
  | .var i, cs => cs i
  | .arrow A B, cs => .arr (liftCo A cs) (liftCo B cs)
  | .all A, cs => .all (liftCo A (upCo cs))
  | .con T, _ => .refl (.con T)
  | .app A B, cs => .capp (liftCo A cs) (liftCo B cs)

/-- **Typing of the lifting**: `liftCo A cs : A[s] ~ A[s']` when every `cs i : s i ~ s' i`. -/
theorem CoTyping.liftCo {Ax : AxSet} (hAx : AxOK Ax) (A : Ty) :
    ∀ (cs : ℕ → Co) (s s' : ℕ → Ty), (∀ i, CoTyping Ax (cs i) (s i) (s' i)) →
      CoTyping Ax (FCTyCon.liftCo A cs) (tySubst s A) (tySubst s' A) := by
  induction A with
  | var i => intro cs s s' h; exact h i
  | arrow A B ihA ihB => intro cs s s' h; exact .arr (ihA cs s s' h) (ihB cs s s' h)
  | all A ih =>
      intro cs s s' h
      refine .all (ih (upCo cs) (ups s) (ups s') ?_)
      intro i
      cases i with
      | zero => exact .refl _
      | succ i => exact (h i).shift hAx
  | con T => intro cs s s' _; exact .refl _
  | app A B ihA ihB => intro cs s s' h; exact .capp (ihA cs s s' h) (ihB cs s s' h)

/-! ### Application coercions and their decompositions -/

/-- The coercion `T γ₁ ⋯ γₙ` (list last argument first). -/
def conCo (T : ℕ) : List Co → Co
  | [] => .refl (.con T)
  | γ :: cs => .capp (conCo T cs) γ

/-- The `j`-th argument decomposition `nth j γ` (counted from the last argument). -/
def nthCo (γ : Co) : ℕ → Co
  | 0 => .appR γ
  | j + 1 => nthCo (.appL γ) j

/-- **Typing of `T γ₁ ⋯ γₙ`.** -/
theorem CoTyping.conCo {Ax : AxSet} (T : ℕ) :
    ∀ (cs : List Co) (σ ρ : List Ty), cs.length = σ.length → σ.length = ρ.length →
      (∀ j (hj : j < cs.length) (h1 : j < σ.length) (h2 : j < ρ.length),
        CoTyping Ax cs[j] σ[j] ρ[j]) →
      CoTyping Ax (FCTyCon.conCo T cs) (tapps T σ) (tapps T ρ)
  | [], [], [], _, _, _ => .refl _
  | γ :: cs, A :: σ, B :: ρ, h1, h2, h => by
      refine .capp (CoTyping.conCo T cs σ ρ (by simpa using h1) (by simpa using h2) ?_)
        (h 0 (by simp) (by simp) (by simp))
      intro j hj h1' h2'
      exact h (j + 1) (by simpa using hj) (by simpa using h1') (by simpa using h2')
  | [], _ :: _, _, h1, _, _ => by simp at h1
  | _ :: _, [], _, h1, _, _ => by simp at h1
  | [], [], _ :: _, _, h2, _ => by simp at h2
  | _ :: _, _ :: _, [], _, h2, _ => by simp at h2

/-- **Typing of the decompositions**: a coercion between two constructor applications with the
same number of arguments decomposes into coercions between the arguments. -/
theorem CoTyping.nthCo {Ax : AxSet} {T T' : ℕ} :
    ∀ {σ ρ : List Ty} {γ : Co}, CoTyping Ax γ (tapps T σ) (tapps T' ρ) → σ.length = ρ.length →
      ∀ j (h1 : j < σ.length) (h2 : j < ρ.length), CoTyping Ax (FCTyCon.nthCo γ j) σ[j] ρ[j]
  | [], _, _, _, _, j, h1, _ => by simp at h1
  | _ :: _, [], _, _, hl, _, _, _ => by simp at hl
  | A :: σ, B :: ρ, γ, h, hl, j, h1, h2 => by
      cases j with
      | zero => exact .appR h
      | succ j =>
          exact CoTyping.nthCo (σ := σ) (ρ := ρ) (.appL h) (by simpa using hl) j
            (by simpa using h1) (by simpa using h2)

/-- The family of decompositions of a coercion between two `n`-ary constructor applications,
padded with `refl (var 0)`. -/
def nthCos (γ : Co) (n : ℕ) (j : ℕ) : Co := if j < n then nthCo γ j else .refl (.var 0)

theorem CoTyping.nthCos {Ax : AxSet} {T T' : ℕ} {σ ρ : List Ty} {γ : Co}
    (h : CoTyping Ax γ (tapps T σ) (tapps T' ρ)) (hσ : σ.length = ρ.length) :
    ∀ j, CoTyping Ax (FCTyCon.nthCos γ σ.length j) (listSub σ j) (listSub ρ j) := by
  intro j
  unfold FCTyCon.nthCos
  by_cases hj : j < σ.length
  · rw [ite_eq_left hj]
    have hj' : j < ρ.length := by omega
    have := CoTyping.nthCo h hσ j hj hj'
    simp only [listSub, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj', Option.getD_some]
    exact this
  · rw [ite_eq_right hj]
    have hj' : ¬ j < ρ.length := by omega
    simp only [listSub, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : σ.length ≤ j),
      List.getElem?_eq_none (by omega : ρ.length ≤ j), Option.getD_none]
    exact .refl _

end FCTyCon
