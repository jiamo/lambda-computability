import Start.PTSExpansionTop
import Start.CoCModel

/-!
# Series V, round 4, run 1, part B: skeletons with level-indexed binders for `CC^ω`
(row M29-EP-CCOMEGA)

In `CC^ω` (`PureTypeSystem.ccOmega`) the rules `(Type i, Type j, Type (max i j))` bind kind
variables inside terms (`λK : Type ℓ. …`, `ΠK : Type ℓ. …`).  The skeletons of
`Start/PTSExpansionTopSkel.lean` therefore acquire binders: `Sk.all ℓ k` is the skeleton of
`ΠK : Type ℓ. B` (with `k` the skeleton of `B`, in which `K` is the skeleton variable `svar 0`).

* `Sk`, `Sk.rename`, `Sk.ssubst`, `Sk.inst` — skeletons with binders, parallel substitution, and
  the σ-calculus laws (`Sk.ssubst_ssubst`, **`Sk.ssubst_inst`**);
* `Cls`, `clO`, `ext`, `WC` — the classifier of `CC^ω` expressions: `univ ℓ` (the sort
  `Type ℓ`), `kind ℓ k` (a kind of level `ℓ` and skeleton `k`), `constr k`, `obj`; a binder over
  `Type ℓ` makes its variable the kind `kind ℓ (svar 0)` and shifts the skeleton variables of
  the context;
* **`CCO.clV_ssubst_level`** — classification commutes with any skeleton substitution on
  well-classified expressions, the substitution moving under skeleton binders (`upFor`);
* `lev`, `V` — predicative candidate spaces: `V L ρ (all ℓ k)` is a product over the closed
  skeletons of level `≤ ℓ`, and a skeleton variable is interpreted at a strictly smaller level, so
  the recursion is on `(L, k)` lexicographically (predicativity of the `Type` rules).

The classifier is first-order in the kinds: a kind-level function (`λK : Type ℓ. B` with `B` a
kind, or `Πx : A. Type ℓ`) is given the class `obj`; these kind constructors are the first point
where this design is incomplete (see `docs/goal/evidence/M29-EP.md`).
-/

set_option autoImplicit false

namespace PureTypeSystem.CCO

/-! ### Skeletons with binders -/

/-- Skeletons: `∗`, `→` from an object, `→` from a constructor, variables, and `∀κ : ℓ. k`. -/
inductive Sk where
  | star : Sk
  | arrO : Sk → Sk
  | arr : Sk → Sk → Sk
  | svar : ℕ → Sk
  | all : ℕ → Sk → Sk
  deriving DecidableEq

def upR (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => r n + 1

def Sk.rename (r : ℕ → ℕ) : Sk → Sk
  | .star => .star
  | .arrO k => .arrO (k.rename r)
  | .arr a k => .arr (a.rename r) (k.rename r)
  | .svar n => .svar (r n)
  | .all ℓ k => .all ℓ (k.rename (upR r))

def up (σ : ℕ → Sk) : ℕ → Sk
  | 0 => .svar 0
  | n + 1 => (σ n).rename Nat.succ

def Sk.ssubst (σ : ℕ → Sk) : Sk → Sk
  | .star => .star
  | .arrO k => .arrO (k.ssubst σ)
  | .arr a k => .arr (a.ssubst σ) (k.ssubst σ)
  | .svar n => σ n
  | .all ℓ k => .all ℓ (k.ssubst (up σ))

/-- Instantiation of the bound skeleton variable `svar 0`. -/
def Sk.inst (k s : Sk) : Sk := k.ssubst (CoC.ncons s .svar)

theorem upR_comp (r r' : ℕ → ℕ) : upR r ∘ upR r' = upR (r ∘ r') := by
  funext n; cases n <;> rfl

theorem Sk.rename_rename (k : Sk) : ∀ (r r' : ℕ → ℕ), (k.rename r').rename r = k.rename (r ∘ r') := by
  induction k with
  | star => intros; rfl
  | arrO k ih => intro r r'; simp [Sk.rename, ih]
  | arr a k iha ihk => intro r r'; simp [Sk.rename, iha, ihk]
  | svar n => intros; rfl
  | all ℓ k ih => intro r r'; simp only [Sk.rename, ih, upR_comp]

theorem Sk.ssubst_rename (k : Sk) : ∀ (σ : ℕ → Sk) (r : ℕ → ℕ),
    (k.rename r).ssubst σ = k.ssubst (σ ∘ r) := by
  induction k with
  | star => intros; rfl
  | arrO k ih => intro σ r; simp [Sk.rename, Sk.ssubst, ih]
  | arr a k iha ihk => intro σ r; simp [Sk.rename, Sk.ssubst, iha, ihk]
  | svar n => intros; rfl
  | all ℓ k ih =>
    intro σ r
    simp only [Sk.rename, Sk.ssubst, ih]
    congr 2
    funext n; cases n <;> rfl

theorem Sk.rename_ssubst (k : Sk) : ∀ (σ : ℕ → Sk) (r : ℕ → ℕ),
    (k.ssubst σ).rename r = k.ssubst (Sk.rename r ∘ σ) := by
  induction k with
  | star => intros; rfl
  | arrO k ih => intro σ r; simp [Sk.rename, Sk.ssubst, ih]
  | arr a k iha ihk => intro σ r; simp [Sk.rename, Sk.ssubst, iha, ihk]
  | svar n => intros; rfl
  | all ℓ k ih =>
    intro σ r
    simp only [Sk.rename, Sk.ssubst, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Function.comp, up, Sk.rename_rename]
      rfl

theorem Sk.ssubst_ssubst (k : Sk) : ∀ (σ τ : ℕ → Sk),
    (k.ssubst τ).ssubst σ = k.ssubst (Sk.ssubst σ ∘ τ) := by
  induction k with
  | star => intros; rfl
  | arrO k ih => intro σ τ; simp [Sk.ssubst, ih]
  | arr a k iha ihk => intro σ τ; simp [Sk.ssubst, iha, ihk]
  | svar n => intros; rfl
  | all ℓ k ih =>
    intro σ τ
    simp only [Sk.ssubst, ih]
    congr 2
    funext n
    cases n with
    | zero => rfl
    | succ n =>
      simp only [Function.comp, up, Sk.ssubst_rename, Sk.rename_ssubst]
      rfl

theorem Sk.ssubst_svar (k : Sk) : k.ssubst .svar = k := by
  have h : ∀ σ : ℕ → Sk, σ = .svar → k.ssubst σ = k := by
    induction k with
    | star => intros; rfl
    | arrO k ih => intro σ hσ; simp [Sk.ssubst, ih σ hσ]
    | arr a k iha ihk => intro σ hσ; simp [Sk.ssubst, iha σ hσ, ihk σ hσ]
    | svar n => intro σ hσ; subst hσ; rfl
    | all ℓ k ih =>
      intro σ hσ
      simp only [Sk.ssubst]
      rw [ih (up σ) (by subst hσ; funext n; cases n <;> rfl)]
  exact h _ rfl

/-- **Substitution commutes with instantiation.** -/
theorem Sk.ssubst_inst (σ : ℕ → Sk) (k s : Sk) :
    (k.inst s).ssubst σ = (k.ssubst (up σ)).inst (s.ssubst σ) := by
  simp only [Sk.inst, Sk.ssubst_ssubst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp, up, Sk.ssubst_rename]
    exact (Sk.ssubst_svar (σ n)).symm

/-! ### Classes and the classifier -/

/-- Classes: the sort `Type ℓ`; a kind of level `ℓ` and skeleton `k`; a constructor of skeleton
`k`; an object. -/
inductive Cls where
  | univ : ℕ → Cls
  | kind : ℕ → Sk → Cls
  | constr : Sk → Cls
  | obj : Cls
  deriving DecidableEq

def Cls.ssubst (σ : ℕ → Sk) : Cls → Cls
  | .univ ℓ => .univ ℓ
  | .kind ℓ k => .kind ℓ (k.ssubst σ)
  | .constr k => .constr (k.ssubst σ)
  | .obj => .obj

def Cls.rename (r : ℕ → ℕ) : Cls → Cls
  | .univ ℓ => .univ ℓ
  | .kind ℓ k => .kind ℓ (k.rename r)
  | .constr k => .constr (k.rename r)
  | .obj => .obj

/-- The classifier context after a binder of class `cA`: a binder over `Type ℓ` declares a kind
variable (skeleton `svar 0`, the skeleton variables of the context shift); a binder over a kind
declares a constructor; any other binder declares an object. -/
def ext : Cls → (ℕ → Cls) → ℕ → Cls
  | .univ ℓ, Δ => CoC.ncons (.kind ℓ (.svar 0)) (Cls.rename Nat.succ ∘ Δ)
  | .kind _ a, Δ => CoC.ncons (.constr a) Δ
  | _, Δ => CoC.ncons .obj Δ

/-- The substitution to use under a binder of class `cA`. -/
def upFor : Cls → (ℕ → Sk) → ℕ → Sk
  | .univ _, σ => up σ
  | _, σ => σ

def appO : Cls → Cls → Cls
  | .constr (.all _ k), .kind _ s => .constr (k.inst s)
  | .constr (.arr _ k), _ => .constr k
  | .constr (.arrO k), _ => .constr k
  | _, _ => .obj

def lamO : Cls → Cls → Cls
  | .univ ℓ, .constr k => .constr (.all ℓ k)
  | .kind _ a, .constr k => .constr (.arr a k)
  | .constr _, .constr k => .constr (.arrO k)
  | .obj, .constr k => .constr (.arrO k)
  | _, _ => .obj

def piO : Cls → Cls → Cls
  | .univ ℓ, .kind ℓ' k => .kind (max (ℓ + 1) ℓ') (.all ℓ k)
  | .kind ℓ a, .kind ℓ' k => .kind (max ℓ ℓ') (.arr a k)
  | .constr _, .kind ℓ' k => .kind ℓ' (.arrO k)
  | .obj, .kind ℓ' k => .kind ℓ' (.arrO k)
  | _, .univ _ => .obj
  | _, _ => .constr .star

/-- **The classifier of `CC^ω` expressions.** `Prop` is a kind of level `0` and skeleton `∗`;
`Type ℓ` has class `univ ℓ`. -/
def clO : (ℕ → Cls) → Expr CSrt → Cls
  | Δ, .var n => Δ n
  | _, .sort .prop => .kind 0 .star
  | _, .sort (.type ℓ) => .univ ℓ
  | Δ, .app F U => appO (clO Δ F) (clO Δ U)
  | Δ, .lam A b => lamO (clO Δ A) (clO (ext (clO Δ A) Δ) b)
  | Δ, .pi A B => piO (clO Δ A) (clO (ext (clO Δ A) Δ) B)

/-- Well-classified: no application whose head is a constructor of variable skeleton. -/
def WC : (ℕ → Cls) → Expr CSrt → Prop
  | _, .var _ => True
  | _, .sort _ => True
  | Δ, .app F U => (∀ i, clO Δ F ≠ .constr (.svar i)) ∧ WC Δ F ∧ WC Δ U
  | Δ, .lam A b => WC Δ A ∧ WC (ext (clO Δ A) Δ) b
  | Δ, .pi A B => WC Δ A ∧ WC (ext (clO Δ A) Δ) B

/-! ### Commutation with skeleton substitution -/

theorem Cls.ssubst_rename_succ (σ : ℕ → Sk) (c : Cls) :
    (c.rename Nat.succ).ssubst (up σ) = (c.ssubst σ).rename Nat.succ := by
  cases c with
  | univ ℓ => rfl
  | kind ℓ k =>
    simp only [Cls.rename, Cls.ssubst, Sk.ssubst_rename, Sk.rename_ssubst]; rfl
  | constr k =>
    simp only [Cls.rename, Cls.ssubst, Sk.ssubst_rename, Sk.rename_ssubst]; rfl
  | obj => rfl

theorem ext_ssubst (σ : ℕ → Sk) (cA : Cls) (Δ : ℕ → Cls) :
    Cls.ssubst (upFor cA σ) ∘ ext cA Δ = ext (cA.ssubst σ) (Cls.ssubst σ ∘ Δ) := by
  funext n
  cases cA with
  | univ ℓ =>
    cases n with
    | zero => rfl
    | succ n => exact Cls.ssubst_rename_succ σ (Δ n)
  | kind ℓ a => cases n <;> rfl
  | constr k => cases n <;> rfl
  | obj => cases n <;> rfl

theorem lamO_ssubst (σ : ℕ → Sk) (cA c : Cls) :
    lamO (cA.ssubst σ) (c.ssubst (upFor cA σ)) = (lamO cA c).ssubst σ := by
  cases cA <;> cases c <;> rfl

theorem piO_ssubst (σ : ℕ → Sk) (cA c : Cls) :
    piO (cA.ssubst σ) (c.ssubst (upFor cA σ)) = (piO cA c).ssubst σ := by
  cases cA <;> cases c <;> rfl

theorem appO_ssubst (σ : ℕ → Sk) (cF cU : Cls) (hF : ∀ i, cF ≠ .constr (.svar i)) :
    appO (cF.ssubst σ) (cU.ssubst σ) = (appO cF cU).ssubst σ := by
  rcases cF with ℓ | ⟨ℓ, k⟩ | k | _
  · rfl
  · rfl
  · cases k with
    | star => rfl
    | arrO k => rfl
    | arr a k => rfl
    | svar i => exact absurd rfl (hF i)
    | all ℓ k =>
      cases cU with
      | kind ℓ' s =>
        simp only [Cls.ssubst, Sk.ssubst, appO]
        rw [Sk.ssubst_inst]
      | univ _ => rfl
      | constr _ => rfl
      | obj => rfl
  · rfl

/-- **`CCO.clV_ssubst_level`**: on well-classified `CC^ω` expressions, classification commutes
with every skeleton substitution `σ` (which moves under the skeleton binders introduced by
binders over `Type ℓ`).  The level discipline of `σ` (skeletons of level `≤ ℓ` for variables
of level `ℓ`) is not needed for this equation; it is needed by the candidate spaces `V`. -/
theorem clV_ssubst_level (M : Expr CSrt) :
    ∀ (σ : ℕ → Sk) (Δ : ℕ → Cls), WC Δ M → clO (Cls.ssubst σ ∘ Δ) M = (clO Δ M).ssubst σ := by
  induction M with
  | var n => intros; rfl
  | sort s => intros; cases s <;> rfl
  | app F U ihF ihU =>
    intro σ Δ h
    simp only [clO]
    rw [ihF σ Δ h.2.1, ihU σ Δ h.2.2, appO_ssubst σ _ _ h.1]
  | lam A b ihA ihb =>
    intro σ Δ h
    simp only [clO]
    rw [ihA σ Δ h.1, ← ext_ssubst, ihb _ _ h.2, lamO_ssubst]
  | pi A B ihA ihB =>
    intro σ Δ h
    simp only [clO]
    rw [ihA σ Δ h.1, ← ext_ssubst, ihB _ _ h.2, piO_ssubst]

/-- Without well-classification the equation fails (as for `cocTop`): `x U` with `x` a
constructor of variable skeleton `svar 0`, instantiated by `∗ → ∗`. -/
theorem clV_ssubst_level_fails :
    clO (Cls.ssubst (fun _ => .arr .star .star) ∘ CoC.ncons (.constr (.svar 0)) (fun _ => .obj))
        (.app (.var 0) (.sort .prop)) ≠
      (clO (CoC.ncons (.constr (.svar 0)) (fun _ => .obj)) (.app (.var 0) (.sort .prop))).ssubst
        (fun _ => .arr .star .star) := by
  decide

/-- The context classifier: a declaration `K : Type ℓ` declares a kind variable; the skeleton
variables count the kind declarations (de Bruijn). -/
def ctxClO : List (Expr CSrt) → ℕ → Cls
  | [], _ => .obj
  | A :: Γ, n => ext (clO (ctxClO Γ) A) (ctxClO Γ) n

/-! ### Predicative candidate spaces -/

/-- The level of a skeleton: one more than its largest binder level (`0` if it has none). -/
def lev : Sk → ℕ
  | .star => 0
  | .arrO k => lev k
  | .arr a k => max (lev a) (lev k)
  | .svar _ => 0
  | .all ℓ k => max (ℓ + 1) (lev k)

/-- A skeleton without free skeleton variables (below `d` binders). -/
def ClosedBelow : ℕ → Sk → Prop
  | _, .star => True
  | d, .arrO k => ClosedBelow d k
  | d, .arr a k => ClosedBelow d a ∧ ClosedBelow d k
  | d, .svar n => n < d
  | d, .all _ k => ClosedBelow (d + 1) k

/-- **Candidate spaces by recursion on the level.**  `V L ρ k` interprets `k` with its skeleton
variables valued by the closed skeletons `ρ n`, each read at level `L - 1`; the binder
`∀κ : ℓ. k` is a product over the closed skeletons of level `≤ ℓ`.  The recursion is on `(L, k)`
lexicographically: a variable lowers `L`, every other case is structural in `k`. -/
def V (Λ : Type) : ℕ → (ℕ → Sk) → Sk → Type
  | _, _, .star => Set Λ
  | L, ρ, .arrO k => V Λ L ρ k
  | L, ρ, .arr a k => V Λ L ρ a → V Λ L ρ k
  | 0, _, .svar _ => PUnit
  | L + 1, ρ, .svar n => V Λ L (fun _ => .star) (ρ n)
  | L, ρ, .all ℓ k => (c : {c : Sk // ClosedBelow 0 c ∧ lev c ≤ ℓ}) → V Λ L (CoC.ncons c.1 ρ) k
  termination_by L _ k => (L, k)

/-! ### The first failing case: kind-level functions -/

/-- **The first case that fails** (B3): the classifier is not invariant under β at a kind-level
redex.  `(λK : Type 0. K) Prop` is typable in `CC^ω` (rule `(Type 1, Type 1, Type 1)`) and
β-reduces to `Prop`, a kind of skeleton `∗`; the classifier gives the redex the class `obj`,
because the kind-level function `λK : Type 0. K` has no class of its own. -/
theorem clO_beta_fails :
    clO (fun _ => .obj) (.app (.lam (.sort (.type 0)) (.var 0)) (.sort .prop)) ≠
      clO (fun _ => .obj) (.sort .prop) := by
  decide

end PureTypeSystem.CCO
