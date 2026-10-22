import Start.CoCModel
import Start.PTSExpansionTop

/-!
# Series V, round 2, run 2, part A1: skeleton variables for `cocTop`
(row M29-EP-TOP-SORT-FUNDAMENTAL)

The skeleton model of `Start/CoCModel.lean` computes the skeleton of a kind from the kind
expression; a kind variable `K : □` of `cocTop` has none.  Here skeletons acquire variables
`svar i`; a closed skeleton valuation `θ : Nat → Sk` interprets them.  In `cocTop` no rule has
`s₁ = Δ`, so no binder ever binds a kind variable: kind variables `K : □` occur only in the
context, and `svar i` can be the de Bruijn *level* of the declaration (stable under weakening,
untouched by binders).

The classifier operations are re-checked against skeleton substitution:
`bindV`, `domV`, `lamV`, `piV` commute with it unconditionally; `appV` does **not**
(`appV_ssubst_fails`), and commutes exactly when the head is not a constructor of variable skeleton
(`appV_ssubst`).  In a derivation the head `F` of `F U` has a product type, and a kind variable is
convertible only to itself, so the side condition is a well-classification invariant (`WCV`) to be
carried by `classify` — that is the first missing lemma of the generalized `cl_subst`.

* `SkV`, `ClsV`, `SkV.ssubst`, `ClsV.ssubst` — skeletons and classes with skeleton variables;
* `bindV_ssubst`, `domV_ssubst`, `lamV_ssubst`, `piV_ssubst`; `appV_ssubst` (side condition) and
  `appV_ssubst_fails`;
* `clV`, `ctxClV`, `WCV` — the classifier of `cocTop` expressions, the context classifier (a kind
  variable receives `kind (svar ℓ)`, `ℓ` its level), and well-classification;
* **`clV_ssubst`** — classification commutes with assigning skeletons to skeleton variables on
  well-classified expressions (the new case of `cl_subst`), and `clV_ssubst_fails` without it;
* `VV θ` — candidate spaces relative to a closed skeleton valuation.

The fundamental lemma is **not** generalized here.  First missing lemma: `classifyV` (see
`docs/goal/evidence/M29-EP.md`, "Series V, round 2, run 2").
-/

set_option autoImplicit false

namespace PureTypeSystem.TopSkel

inductive SkV where
  | star : SkV
  | arrO : SkV → SkV
  | arr : SkV → SkV → SkV
  | svar : Nat → SkV
  deriving DecidableEq

inductive ClsV where
  | kind : SkV → ClsV
  | constr : SkV → ClsV
  | obj : ClsV
  deriving DecidableEq

def SkV.ssubst (θ : Nat → SkV) : SkV → SkV
  | .star => .star
  | .arrO k => .arrO (k.ssubst θ)
  | .arr a k => .arr (a.ssubst θ) (k.ssubst θ)
  | .svar i => θ i

def ClsV.ssubst (θ : Nat → SkV) : ClsV → ClsV
  | .kind k => .kind (k.ssubst θ)
  | .constr k => .constr (k.ssubst θ)
  | .obj => .obj

def bindV : ClsV → ClsV
  | .kind a => .constr a
  | _ => .obj

def domV : ClsV → SkV → SkV
  | .kind a, k => .arr a k
  | _, k => .arrO k

def appV : ClsV → ClsV
  | .constr (.arr _ k) => .constr k
  | .constr (.arrO k) => .constr k
  | _ => .obj

def lamV (cA : ClsV) : ClsV → ClsV
  | .constr k => .constr (domV cA k)
  | _ => .obj

def piV (cA : ClsV) : ClsV → ClsV
  | .kind k => .kind (domV cA k)
  | _ => .constr .star

theorem bindV_ssubst (θ : Nat → SkV) (c : ClsV) : bindV (c.ssubst θ) = (bindV c).ssubst θ := by
  cases c <;> rfl

theorem domV_ssubst (θ : Nat → SkV) (c : ClsV) (k : SkV) :
    domV (c.ssubst θ) (k.ssubst θ) = (domV c k).ssubst θ := by
  cases c <;> rfl

theorem lamV_ssubst (θ : Nat → SkV) (cA c : ClsV) :
    lamV (cA.ssubst θ) (c.ssubst θ) = (lamV cA c).ssubst θ := by
  cases c <;> simp only [ClsV.ssubst, lamV]
  rw [← domV_ssubst]; rfl

theorem piV_ssubst (θ : Nat → SkV) (cA c : ClsV) :
    piV (cA.ssubst θ) (c.ssubst θ) = (piV cA c).ssubst θ := by
  cases c <;> simp only [ClsV.ssubst, piV, SkV.ssubst]
  rw [← domV_ssubst]; rfl

/-- The failing equation: a constructor of variable skeleton, applied. -/
theorem appV_ssubst_fails :
    appV ((ClsV.constr (.svar 0)).ssubst (fun _ => .arr .star .star)) ≠
      (appV (ClsV.constr (.svar 0))).ssubst (fun _ => .arr .star .star) := by
  decide

/-- `appV` commutes with skeleton substitution away from constructors of variable skeleton. -/
theorem appV_ssubst (θ : Nat → SkV) (c : ClsV) (hc : ∀ i, c ≠ .constr (.svar i)) :
    appV (c.ssubst θ) = (appV c).ssubst θ := by
  rcases c with k | k | _
  · rfl
  · cases k with
    | star => rfl
    | arrO k => rfl
    | arr a k => rfl
    | svar i => exact absurd rfl (hc i)
  · rfl

/-- Closed skeletons of `Start/CoCModel.lean` embed. -/
def ofSk : CoC.Sk → SkV
  | .star => .star
  | .arrO k => .arrO (ofSk k)
  | .arr a k => .arr (ofSk a) (ofSk k)

/-- Candidate spaces relative to a closed skeleton valuation. -/
def VV (θ : Nat → CoC.Sk) : SkV → Type
  | .star => Set (Expr LambdaPi.Srt)
  | .arrO k => VV θ k
  | .arr a k => VV θ a → VV θ k
  | .svar i => CoC.V (θ i)

/-! ### The classifier of `cocTop` expressions with skeleton variables -/

open CoC (ncons)

/-- The classifier: `∗` is a kind of skeleton `∗`; `□` and `Δ` are not classified (kind
variables `K : □` receive their class `kind (svar i)` from the context). -/
def clV : (Nat → ClsV) → Expr Srt3 → ClsV
  | Δ, .var n => Δ n
  | _, .sort .star => .kind .star
  | _, .sort _ => .obj
  | Δ, .app F _ => appV (clV Δ F)
  | Δ, .lam A b => lamV (clV Δ A) (clV (ncons (bindV (clV Δ A)) Δ) b)
  | Δ, .pi A B => piV (clV Δ A) (clV (ncons (bindV (clV Δ A)) Δ) B)

/-- Well-classified: no application whose head has a variable skeleton. -/
def WCV : (Nat → ClsV) → Expr Srt3 → Prop
  | _, .var _ => True
  | _, .sort _ => True
  | Δ, .app F U => (∀ i, clV Δ F ≠ .constr (.svar i)) ∧ WCV Δ F ∧ WCV Δ U
  | Δ, .lam A b => WCV Δ A ∧ WCV (ncons (bindV (clV Δ A)) Δ) b
  | Δ, .pi A B => WCV Δ A ∧ WCV (ncons (bindV (clV Δ A)) Δ) B

theorem ssubst_ncons (θ : Nat → SkV) (c : ClsV) (Δ : Nat → ClsV) :
    ClsV.ssubst θ ∘ ncons c Δ = ncons (c.ssubst θ) (ClsV.ssubst θ ∘ Δ) := by
  funext n; cases n <;> rfl

/-- **Assigning skeletons to skeleton variables commutes with classification** on
well-classified expressions: the skeleton half of `cl_subst` for a kind variable. -/
theorem clV_ssubst (θ : Nat → SkV) (M : Expr Srt3) :
    ∀ (Δ : Nat → ClsV), WCV Δ M → clV (ClsV.ssubst θ ∘ Δ) M = (clV Δ M).ssubst θ := by
  induction M with
  | var n => intro Δ _; rfl
  | sort s => intro Δ _; cases s <;> rfl
  | app F U ihF _ =>
      intro Δ h
      simp only [clV]
      rw [ihF Δ h.2.1, appV_ssubst θ _ h.1]
  | lam A b ihA ihb =>
      intro Δ h
      simp only [clV]
      rw [ihA Δ h.1, bindV_ssubst, ← ssubst_ncons, ihb _ h.2, lamV_ssubst]
  | pi A B ihA ihB =>
      intro Δ h
      simp only [clV]
      rw [ihA Δ h.1, bindV_ssubst, ← ssubst_ncons, ihB _ h.2, piV_ssubst]

/-- Without well-classification the equation fails: `x U` with `x : K`, `K` a kind variable,
`K := ∗ → ∗`. -/
theorem clV_ssubst_fails :
    clV (ClsV.ssubst (fun _ => .arr .star .star) ∘ ncons (.constr (.svar 0)) (fun _ => .obj))
        (.app (.var 0) (.sort .star)) ≠
      (clV (ncons (.constr (.svar 0)) (fun _ => .obj)) (.app (.var 0) (.sort .star))).ssubst
        (fun _ => .arr .star .star) := by
  decide

/-- The context classifier: a declaration `K : □` makes `K` a kind of skeleton `svar ℓ`, with `ℓ`
the level of the declaration; any other declaration `A` gives its variable the class `bindV`
of `A`. -/
def ctxClV : List (Expr Srt3) → Nat → ClsV
  | [], _ => .obj
  | A :: Γ, 0 => if A = .sort .box then .kind (.svar Γ.length) else bindV (clV (ctxClV Γ) A)
  | _ :: Γ, n + 1 => ctxClV Γ n

end PureTypeSystem.TopSkel
