/-
**System F** (the polymorphic lambda calculus, Girard–Reynolds) over the de Bruijn syntax of this
development, and **strong normalization** by Girard's method of reducibility candidates.

`Start/SimpleTypes.lean` typed the untyped terms of `Start/Syntax.lean` with simple types and gave
Tait's reducibility proof of strong normalization.  System F is the next step: types may quantify
over types, so the reducibility predicate of a quantified type has to range over *all* candidate
interpretations of the bound type variable, and the predicate can no longer be defined by
recursion on the type alone — this is Girard's device of reducibility *candidates*.

The calculus is presented in Curry style (type assignment): terms are the ordinary untyped terms
of the development, and the two extra rules assign a quantified type to a term whose type is
generic in a type variable, and instantiate a quantified type.  Reduction is ordinary β-reduction
of `Start/Reduction.lean`, so strong normalization here is a statement about the untyped calculus.

* `SystemF.FTy` — types: type variables, arrows and `∀`, with de Bruijn indices for type
  variables, and the substitution calculus `SystemF.tyRename`, `SystemF.tySubst`,
  `SystemF.tyInst`;
* `SystemF.Typing Γ t A` — the five rules of Curry-style System F;
* `SystemF.Cand` — a **reducibility candidate**: a set of terms containing only strongly
  normalizing terms (CR1), closed under reduction (CR2), and containing every term that is not an
  abstraction and all of whose reducts it contains (CR3);
* `SystemF.interp A ρ` — the interpretation of a type in a valuation of its free type variables by
  candidates, and `SystemF.candOf` — the fact that it is itself a candidate;
* `SystemF.interp_tyInst`, `SystemF.interp_tyShift` — the semantic substitution and weakening
  lemmas for that interpretation;
* `SystemF.interp_substEnv` — the fundamental lemma: a typable term is reducible under any
  reducible parallel substitution;
* `SystemF.sn_of_typing` — **strong normalization for System F**.

Two corollaries record that the theorem is not vacuous and that System F is genuinely stronger
than the simply typed calculus: the self-application `λx. x x` is typable in System F
(`SystemF.typing_selfApp`) but not in the simply typed calculus
(`SystemF.not_simple_typing_selfApp`), and every typable term still has a normal form.
-/

import Start.SimpleTypes

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemF

open Lambda

/-! ### Types and their substitution calculus -/

/-- Types of System F, with de Bruijn indices for the bound type variables. -/
inductive FTy where
  /-- A type variable. -/
  | var : ℕ → FTy
  /-- A function type. -/
  | arrow : FTy → FTy → FTy
  /-- A universally quantified type. -/
  | all : FTy → FTy
  deriving DecidableEq

/-- Lifting a renaming of type variables under a `∀`. -/
def upr (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => r n + 1

/-- Renaming the type variables of a type. -/
def tyRename (r : ℕ → ℕ) : FTy → FTy
  | FTy.var i => FTy.var (r i)
  | FTy.arrow A B => FTy.arrow (tyRename r A) (tyRename r B)
  | FTy.all A => FTy.all (tyRename (upr r) A)

/-- Weakening a type by one type variable. -/
def tyShift (A : FTy) : FTy := tyRename Nat.succ A

/-- Lifting a substitution of type variables under a `∀`. -/
def ups (s : ℕ → FTy) : ℕ → FTy
  | 0 => FTy.var 0
  | n + 1 => tyShift (s n)

/-- Substituting the type variables of a type. -/
def tySubst (s : ℕ → FTy) : FTy → FTy
  | FTy.var i => s i
  | FTy.arrow A B => FTy.arrow (tySubst s A) (tySubst s B)
  | FTy.all A => FTy.all (tySubst (ups s) A)

/-- The substitution replacing the type variable `0` by `B` and lowering the others. -/
def tyScons (B : FTy) : ℕ → FTy
  | 0 => B
  | n + 1 => FTy.var n

/-- Instantiating the outermost bound type variable of a type. -/
def tyInst (B A : FTy) : FTy := tySubst (tyScons B) A

/-! ### Typing -/

/-- Curry-style typing for System F: the context lists the types of the free *term* variables,
index `0` first; the type variables are the de Bruijn indices of `FTy`, and the rule for `∀`
introduction weakens the whole context by one type variable. -/
inductive Typing : List FTy → Lambda → FTy → Prop
  /-- A variable has the type recorded in the context. -/
  | var {Γ : List FTy} {i : ℕ} {A : FTy} : Γ[i]? = some A → Typing Γ (Lambda.var i) A
  /-- Application. -/
  | app {Γ : List FTy} {a b : Lambda} {A B : FTy} :
      Typing Γ a (FTy.arrow A B) → Typing Γ b A → Typing Γ (Lambda.app a b) B
  /-- Abstraction. -/
  | lam {Γ : List FTy} {t : Lambda} {A B : FTy} :
      Typing (A :: Γ) t B → Typing Γ (Lambda.lam t) (FTy.arrow A B)
  /-- Generalization: a term typable in a context that does not mention the fresh type variable
  has the quantified type. -/
  | tlam {Γ : List FTy} {t : Lambda} {A : FTy} :
      Typing (Γ.map tyShift) t A → Typing Γ t (FTy.all A)
  /-- Instantiation. -/
  | tapp {Γ : List FTy} {t : Lambda} {A : FTy} (B : FTy) :
      Typing Γ t (FTy.all A) → Typing Γ t (tyInst B A)

/-! ### Reducibility candidates -/

/-- A **reducibility candidate**: a set of terms satisfying Girard's three conditions. -/
structure Cand where
  /-- The underlying set of terms. -/
  mem : Lambda → Prop
  /-- CR1: every term of the candidate is strongly normalizing. -/
  cr1 : ∀ {t : Lambda}, mem t → SN t
  /-- CR2: the candidate is closed under reduction. -/
  cr2 : ∀ {t t' : Lambda}, mem t → Lambda.step t t' → mem t'
  /-- CR3: a term that is not an abstraction and whose reducts are all in the candidate is in the
  candidate. -/
  cr3 : ∀ {t : Lambda}, NotAbs t → (∀ t', Lambda.step t t' → mem t') → mem t

@[ext] theorem Cand.ext' {X Y : Cand} (h : X.mem = Y.mem) : X = Y := by
  cases X; cases Y; cases h; rfl

/-- The strongly normalizing terms form a candidate. -/
def snCand : Cand where
  mem := SN
  cr1 h := h
  cr2 h hs := h.step hs
  cr3 _ h := SN.intro h

/-- Every candidate contains every variable. -/
theorem Cand.var (X : Cand) (i : ℕ) : X.mem (Lambda.var i) :=
  X.cr3 (notAbs_var i) fun _ h => absurd h not_step_var

/-- Extending a valuation of type variables by a candidate. -/
def candScons (K : Cand) (rho : ℕ → Cand) : ℕ → Cand
  | 0 => K
  | n + 1 => rho n

/-! ### The interpretation of a type -/

/-- The interpretation of a type in a valuation of its free type variables by candidates. -/
def interp : FTy → (ℕ → Cand) → Lambda → Prop
  | FTy.var i, rho => (rho i).mem
  | FTy.arrow A B, rho => fun t => ∀ u : Lambda, interp A rho u → interp B rho (Lambda.app t u)
  | FTy.all A, rho => fun t => ∀ K : Cand, interp A (candScons K rho) t

@[simp] theorem interp_var (i : ℕ) (rho : ℕ → Cand) : interp (FTy.var i) rho = (rho i).mem := rfl

@[simp] theorem interp_arrow (A B : FTy) (rho : ℕ → Cand) (t : Lambda) :
    interp (FTy.arrow A B) rho t ↔ ∀ u, interp A rho u → interp B rho (Lambda.app t u) := Iff.rfl

@[simp] theorem interp_all (A : FTy) (rho : ℕ → Cand) (t : Lambda) :
    interp (FTy.all A) rho t ↔ ∀ K : Cand, interp A (candScons K rho) t := Iff.rfl

/-- The interpretation of a type is a candidate: Girard's three conditions, proved by induction on
the type. -/
theorem interp_cr (A : FTy) :
    ∀ rho : ℕ → Cand,
      (∀ t, interp A rho t → SN t) ∧
      (∀ t t', interp A rho t → Lambda.step t t' → interp A rho t') ∧
      (∀ t, NotAbs t → (∀ t', Lambda.step t t' → interp A rho t') → interp A rho t) := by
  induction A with
  | var i =>
      intro rho
      exact ⟨fun _ h => (rho i).cr1 h, fun _ _ h hs => (rho i).cr2 h hs,
        fun _ hn h => (rho i).cr3 hn h⟩
  | arrow A B ihA ihB =>
      intro rho
      obtain ⟨ihA1, ihA2, ihA3⟩ := ihA rho
      obtain ⟨ihB1, ihB2, ihB3⟩ := ihB rho
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        have hv : interp A rho (Lambda.var 0) :=
          ihA3 _ (notAbs_var 0) fun _ h => absurd h not_step_var
        exact sn_app_left (ihB1 _ (ht _ hv))
      · intro t t' ht hs u hu
        exact ihB2 _ _ (ht u hu) (Lambda.step.app_left _ _ _ hs)
      · intro t hn h u hu
        have hsn : SN u := ihA1 u hu
        induction hsn with
        | intro u hacc ihu =>
            refine ihB3 _ (notAbs_app t u) fun w hw => ?_
            cases hw with
            | beta _ _ => exact hn.elim
            | app_left _ t' _ hstep => exact h t' hstep u hu
            | app_right _ _ u' hstep => exact ihu u' hstep (ihA2 _ _ hu hstep)
  | all A ihA =>
      intro rho
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        exact (ihA (candScons snCand rho)).1 t (ht snCand)
      · intro t t' ht hs K
        exact (ihA (candScons K rho)).2.1 t t' (ht K) hs
      · intro t hn h K
        exact (ihA (candScons K rho)).2.2 t hn fun t' hs => h t' hs K

/-- The interpretation of a type, packaged as a candidate. -/
def candOf (A : FTy) (rho : ℕ → Cand) : Cand where
  mem := interp A rho
  cr1 h := (interp_cr A rho).1 _ h
  cr2 h hs := (interp_cr A rho).2.1 _ _ h hs
  cr3 hn h := (interp_cr A rho).2.2 _ hn h

@[simp] theorem candOf_mem (A : FTy) (rho : ℕ → Cand) : (candOf A rho).mem = interp A rho := rfl

theorem interp_sn {A : FTy} {rho : ℕ → Cand} {t : Lambda} (h : interp A rho t) : SN t :=
  (candOf A rho).cr1 h

theorem interp_step {A : FTy} {rho : ℕ → Cand} {t t' : Lambda} (h : interp A rho t)
    (hs : Lambda.step t t') : interp A rho t' := (candOf A rho).cr2 h hs

theorem interp_ne {A : FTy} {rho : ℕ → Cand} {t : Lambda} (hn : NotAbs t)
    (h : ∀ t', Lambda.step t t' → interp A rho t') : interp A rho t := (candOf A rho).cr3 hn h

theorem interp_var_tm (A : FTy) (rho : ℕ → Cand) (i : ℕ) : interp A rho (Lambda.var i) :=
  (candOf A rho).var i

/-! ### The semantic substitution lemmas -/

theorem interp_tyRename (A : FTy) :
    ∀ (r : ℕ → ℕ) (rho : ℕ → Cand) (t : Lambda),
      interp (tyRename r A) rho t ↔ interp A (fun i => rho (r i)) t := by
  induction A with
  | var i => intro r rho t; exact Iff.rfl
  | arrow A B ihA ihB =>
      intro r rho t
      constructor
      · intro h u hu
        exact (ihB r rho _).1 (h u ((ihA r rho u).2 hu))
      · intro h u hu
        exact (ihB r rho _).2 (h u ((ihA r rho u).1 hu))
  | all A ihA =>
      intro r rho t
      constructor
      · intro h K
        have hK := (ihA (upr r) (candScons K rho) t).1 (h K)
        have hval : (fun i => candScons K rho (upr r i)) = candScons K (fun i => rho (r i)) := by
          funext i
          cases i with
          | zero => rfl
          | succ i => rfl
        rwa [hval] at hK
      · intro h K
        refine (ihA (upr r) (candScons K rho) t).2 ?_
        have hval : (fun i => candScons K rho (upr r i)) = candScons K (fun i => rho (r i)) := by
          funext i
          cases i with
          | zero => rfl
          | succ i => rfl
        rw [hval]
        exact h K

/-- **Semantic weakening**: a type not mentioning the fresh type variable is interpreted the same
way whatever candidate is assigned to it. -/
theorem interp_tyShift (A : FTy) (K : Cand) (rho : ℕ → Cand) (t : Lambda) :
    interp (tyShift A) (candScons K rho) t ↔ interp A rho t := by
  rw [tyShift, interp_tyRename A Nat.succ (candScons K rho) t]
  have hval : (fun i => candScons K rho (Nat.succ i)) = rho := funext fun _ => rfl
  rw [hval]

theorem candOf_tyShift (A : FTy) (K : Cand) (rho : ℕ → Cand) :
    candOf (tyShift A) (candScons K rho) = candOf A rho := by
  refine Cand.ext' ?_
  funext t
  exact propext (interp_tyShift A K rho t)

/-- **Semantic substitution**: interpreting a substituted type is interpreting the type in the
valuation that interprets the substitution. -/
theorem interp_tySubst (A : FTy) :
    ∀ (s : ℕ → FTy) (rho : ℕ → Cand) (t : Lambda),
      interp (tySubst s A) rho t ↔ interp A (fun i => candOf (s i) rho) t := by
  induction A with
  | var i => intro s rho t; exact Iff.rfl
  | arrow A B ihA ihB =>
      intro s rho t
      constructor
      · intro h u hu
        exact (ihB s rho _).1 (h u ((ihA s rho u).2 hu))
      · intro h u hu
        exact (ihB s rho _).2 (h u ((ihA s rho u).1 hu))
  | all A ihA =>
      intro s rho t
      have hval : ∀ K : Cand, (fun i => candOf (ups s i) (candScons K rho))
          = candScons K (fun i => candOf (s i) rho) := by
        intro K
        funext i
        cases i with
        | zero => exact Cand.ext' rfl
        | succ i => exact candOf_tyShift (s i) K rho
      constructor
      · intro h K
        have hK := (ihA (ups s) (candScons K rho) t).1 (h K)
        rwa [hval K] at hK
      · intro h K
        refine (ihA (ups s) (candScons K rho) t).2 ?_
        rw [hval K]
        exact h K

/-- Interpreting an instantiated type. -/
theorem interp_tyInst (A B : FTy) (rho : ℕ → Cand) (t : Lambda) :
    interp (tyInst B A) rho t ↔ interp A (candScons (candOf B rho) rho) t := by
  rw [tyInst, interp_tySubst A (tyScons B) rho t]
  have hval : (fun i => candOf (tyScons B i) rho) = candScons (candOf B rho) rho := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact Cand.ext' rfl
  rw [hval]

/-! ### The abstraction lemma -/

theorem interp_app_lam_aux (A B : FTy) (rho : ℕ → Cand) :
    ∀ s : Lambda, SN s → (∀ v, interp A rho v → interp B rho (Lambda.subst v 0 s)) →
      ∀ u : Lambda, SN u → interp A rho u →
        interp B rho (Lambda.app (Lambda.lam s) u) := by
  intro s hs
  induction hs with
  | intro s _ ihs =>
      intro hsub u hu
      induction hu with
      | intro u hacc ihu =>
          intro hru
          refine interp_ne (notAbs_app _ _) fun w hw => ?_
          cases hw with
          | beta _ _ => exact hsub u hru
          | app_left _ t₁' _ hstep =>
              cases hstep with
              | lam _ s' hs' =>
                  exact ihs s' hs'
                    (fun v hv => interp_step (hsub v hv) (step_subst hs' v 0)) u
                    (Acc.intro u hacc) hru
          | app_right _ _ u' hstep => exact ihu u' hstep (interp_step hru hstep)

/-- **Abstraction lemma**: if substituting any reducible term for the bound variable yields a
reducible body, the abstraction is reducible. -/
theorem interp_lam {A B : FTy} {rho : ℕ → Cand} {s : Lambda}
    (h : ∀ v, interp A rho v → interp B rho (Lambda.subst v 0 s)) :
    interp (FTy.arrow A B) rho (Lambda.lam s) := by
  intro u hu
  have hsns : SN s := sn_of_sn_subst (interp_sn (h _ (interp_var_tm A rho 0)))
  exact interp_app_lam_aux A B rho s hsns h u (interp_sn hu) hu

/-! ### The fundamental lemma and strong normalization -/

/-- **Fundamental lemma of the reducibility method for System F.** -/
theorem interp_substEnv {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ (rho : ℕ → Cand) (u : ℕ → Lambda),
      (∀ i A', Γ[i]? = some A' → interp A' rho (u i)) → interp A rho (substEnv u t) := by
  induction h with
  | var hi => intro rho u hu; exact hu _ _ hi
  | app _ _ iha ihb =>
      intro rho u hu
      exact iha rho u hu _ (ihb rho u hu)
  | @lam Γ t A B _ ih =>
      intro rho u hu
      have hsub : substEnv u (Lambda.lam t) = Lambda.lam (substEnv (envCons u) t) := rfl
      rw [hsub]
      refine interp_lam fun v hv => ?_
      rw [subst_zero_substEnv]
      refine ih rho (envScons v u) fun i A' hi => ?_
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA
          exact hv
      | succ i => exact hu i A' (by simpa using hi)
  | @tlam Γ t A _ ih =>
      intro rho u hu K
      refine ih (candScons K rho) u fun i A' hi => ?_
      rw [List.getElem?_map] at hi
      match hΓ : Γ[i]? with
      | none => rw [hΓ] at hi; exact absurd hi (by simp)
      | some A₀ =>
          rw [hΓ] at hi
          have hA' : tyShift A₀ = A' := by simpa using hi
          subst hA'
          exact (interp_tyShift A₀ K rho (u i)).2 (hu i A₀ hΓ)
  | @tapp Γ t A B _ ih =>
      intro rho u hu
      refine (interp_tyInst A B rho (substEnv u t)).2 ?_
      exact ih rho u hu (candOf B rho)

/-- **Strong normalization for System F**: every typable term is strongly normalizing. -/
theorem sn_of_typing {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) : SN t := by
  have hred := interp_substEnv h (fun _ => snCand) (fun k => Lambda.var k)
    fun i A' _ => interp_var_tm A' _ i
  rw [substEnv_var_id] at hred
  exact interp_sn hred

/-- Every typable term of System F has a normal form. -/
theorem hasNormalForm_of_typing {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    HasNormalForm t := hasNormalForm_of_sn (sn_of_typing h)

/-- `omega` is not typable in System F. -/
theorem not_typing_omega {Γ : List FTy} {A : FTy} : ¬ Typing Γ Lambda.omega A := fun h =>
  not_hasNormalForm_omega (hasNormalForm_of_typing h)

/-! ### System F is strictly stronger than the simply typed calculus -/

/-- The polymorphic identity type `∀ α. α → α`. -/
def idTy : FTy := FTy.all (FTy.arrow (FTy.var 0) (FTy.var 0))

/-- Non-vacuity: the identity has the polymorphic identity type. -/
theorem typing_I (Γ : List FTy) : Typing Γ Lambda.I idTy :=
  Typing.tlam (Typing.lam (Typing.var (by simp)))

/-- Self-application, `λx. x x`. -/
def selfApp : Lambda := Lambda.lam (Lambda.app (Lambda.var 0) (Lambda.var 0))

/-- **Self-application is typable in System F**, at the type `(∀ α. α → α) → (∀ α. α → α)`. -/
theorem typing_selfApp (Γ : List FTy) : Typing Γ selfApp (FTy.arrow idTy idTy) := by
  have hx : Typing (idTy :: Γ) (Lambda.var 0) idTy := Typing.var (by simp)
  have hx' : Typing (idTy :: Γ) (Lambda.var 0) (FTy.all (FTy.arrow (FTy.var 0) (FTy.var 0))) := hx
  have harr : Typing (idTy :: Γ) (Lambda.var 0) (FTy.arrow idTy idTy) := by
    have h := Typing.tapp (B := idTy) hx'
    simpa [tyInst, tySubst, tyScons] using h
  exact Typing.lam (Typing.app harr hx)

/-- The size of a simple type. -/
def simpleSize : Lambda.Ty → ℕ
  | Lambda.Ty.base => 1
  | Lambda.Ty.arrow A B => simpleSize A + simpleSize B + 1

theorem simpleSize_pos (A : Lambda.Ty) : 0 < simpleSize A := by
  cases A with
  | base => simp [simpleSize]
  | arrow A B => simp [simpleSize]

theorem ne_arrow_self (A B : Lambda.Ty) : A ≠ Lambda.Ty.arrow A B := by
  intro h
  have := congrArg simpleSize h
  have hB := simpleSize_pos B
  simp only [simpleSize] at this
  omega

/-- **Self-application is not typable in the simply typed calculus**, so System F types strictly
more terms. -/
theorem not_simple_typing_selfApp {Γ : List Lambda.Ty} {A : Lambda.Ty} :
    ¬ Lambda.Typing Γ selfApp A := by
  intro h
  cases h with
  | @lam _ _ A₀ B hbody =>
      cases hbody with
      | @app _ _ _ A₁ _ hf ha =>
          cases hf with
          | var hi =>
              cases ha with
              | var hj =>
                  have h1 : A₀ = Lambda.Ty.arrow A₁ B := by simpa using hi
                  have h2 : A₀ = A₁ := by simpa using hj
                  exact ne_arrow_self A₀ B (h2 ▸ h1)

end SystemF
