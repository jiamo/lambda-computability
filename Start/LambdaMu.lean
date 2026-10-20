/-
**Parigot's λμ-calculus (M23-LAMBDA-MU): typing, subject reduction, and `call/cc`.**

Syntax (de Bruijn indices).  Term variables and names (μ-variables) share one index space: a
λ binds index `0` as a term variable, a μ binds index `0` as a name.  A μ-abstraction is stored
together with its command: `mu β t` is `μα.[β]t`, where `α` is index `0` and `β`, `t` live in the
scope extended by `α`.

Typing `Typ Γ t A` is Parigot's `Γ ⊢ t : A | Δ`, with the two contexts `Γ` (term variables) and
`Δ` (names) interleaved in the single list `Γ : List Entry` in binding order (`Entry.tm A` for a
term variable of type `A`, `Entry.nm A` for a name of type `A`).

Reduction `Step`: β, structural reduction `(μα.c) u → μα.c[[α](w u)/[α]w]` (`Tm.sstr`), renaming
`[β]μα.c → c[β/α]`, and the compatible closure.

* `Typ.ren`, `Typ.subst`, `Typ.sstr`: the substitution lemmas.
* `Typ.step` / `subject_reduction`: **subject reduction**.
* `typ_callcc`: `call/cc := λf. μα.[α](f (λx. μδ.[α]x))` has type `((A → B) → A) → A`
  (Peirce's law) in every context.
-/

import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

/-- Simple types: atoms and implication. -/
inductive Ty where
  | atom : ℕ → Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq

/-- Context entries: a term variable or a name, with its type. -/
inductive Entry where
  | tm : Ty → Entry
  | nm : Ty → Entry
  deriving DecidableEq

/-- λμ-terms; `mu β t` is `μα.[β]t` (`α` = index `0`). -/
inductive Tm where
  | var : ℕ → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm
  | mu : ℕ → Tm → Tm
  deriving DecidableEq

namespace Tm

/-- Lifting a renaming under a binder. -/
def up (r : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => r i + 1

/-- Renaming (of term variables and names alike). -/
def ren (r : ℕ → ℕ) : Tm → Tm
  | var i => var (r i)
  | lam t => lam (ren (up r) t)
  | app t u => app (ren r t) (ren r u)
  | mu β t => mu (up r β) (ren (up r) t)

/-- The index of a variable (a name can only be replaced by a variable). -/
def nameOf : Tm → ℕ
  | var j => j
  | _ => 0

/-- Lifting a substitution under a binder. -/
def upS (σ : ℕ → Tm) : ℕ → Tm
  | 0 => var 0
  | i + 1 => ren Nat.succ (σ i)

/-- Parallel substitution.  A name is replaced by the index of the variable substituted for it. -/
def subst (σ : ℕ → Tm) : Tm → Tm
  | var i => σ i
  | lam t => lam (subst (upS σ) t)
  | app t u => app (subst σ t) (subst σ u)
  | mu β t => mu (nameOf (upS σ β)) (subst (upS σ) t)

/-- The substitution `0 ↦ u`, `i + 1 ↦ i`. -/
def single (u : Tm) : ℕ → Tm
  | 0 => u
  | i + 1 => var i

/-- Structural substitution `[a]w ↦ [a](w v)` for the name `a` (`v` in the scope of the term). -/
def sstr (a : ℕ) (v : Tm) : Tm → Tm
  | var i => var i
  | lam t => lam (sstr (a + 1) (ren Nat.succ v) t)
  | app t u => app (sstr a v t) (sstr a v u)
  | mu β t => mu β (if β = a + 1 then app (sstr (a + 1) (ren Nat.succ v) t) (ren Nat.succ v)
      else sstr (a + 1) (ren Nat.succ v) t)

/-- `call/cc := λf. μα.[α](f (λx. μδ.[α]x))`. -/
def callcc : Tm := lam (mu 0 (app (var 1) (lam (mu 2 (var 1)))))

end Tm

open Tm

/-- One-step reduction of λμ. -/
inductive Step : Tm → Tm → Prop
  | beta (t u : Tm) : Step (app (lam t) u) (subst (single u) t)
  | struct (β : ℕ) (t u : Tm) :
      Step (app (mu β t) u)
        (mu β (if β = 0 then app (sstr 0 (ren Nat.succ u) t) (ren Nat.succ u)
          else sstr 0 (ren Nat.succ u) t))
  | rename (β γ : ℕ) (t : Tm) :
      Step (mu β (mu γ t)) (mu (nameOf (single (var β) γ)) (subst (single (var β)) t))
  | lam {t t' : Tm} : Step t t' → Step (lam t) (lam t')
  | appL {t t' : Tm} (u : Tm) : Step t t' → Step (app t u) (app t' u)
  | appR (t : Tm) {u u' : Tm} : Step u u' → Step (app t u) (app t u')
  | mu (β : ℕ) {t t' : Tm} : Step t t' → Step (mu β t) (mu β t')

/-- Typing `Γ ⊢ t : A | Δ`, with term variables and names interleaved in `Γ`. -/
inductive Typ : List Entry → Tm → Ty → Prop
  | var {Γ : List Entry} {i : ℕ} {A : Ty} : Γ[i]? = some (.tm A) → Typ Γ (var i) A
  | lam {Γ : List Entry} {t : Tm} {A B : Ty} :
      Typ (.tm A :: Γ) t B → Typ Γ (lam t) (.arr A B)
  | app {Γ : List Entry} {t u : Tm} {A B : Ty} :
      Typ Γ t (.arr A B) → Typ Γ u A → Typ Γ (app t u) B
  | mu {Γ : List Entry} {β : ℕ} {t : Tm} {A B : Ty} :
      Typ (.nm A :: Γ) t B → (Entry.nm A :: Γ)[β]? = some (.nm B) → Typ Γ (mu β t) A

namespace Typ

theorem ren {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {Δ : List Entry} (r : ℕ → ℕ), (∀ i e, Γ[i]? = some e → Δ[r i]? = some e) →
      Typ Δ (Tm.ren r t) A := by
  induction h with
  | var hi => intro Δ r hr; exact .var (hr _ _ hi)
  | @lam Γ t A B _ ih =>
      intro Δ r hr
      refine .lam (ih (Tm.up r) ?_)
      intro i e hi
      cases i with
      | zero => simpa [Tm.up] using hi
      | succ i => simpa [Tm.up] using hr i e (by simpa using hi)
  | app _ _ iht ihu => intro Δ r hr; exact .app (iht r hr) (ihu r hr)
  | @mu Γ β t A B _ hβ ih =>
      intro Δ r hr
      have hr' : ∀ i e, (Entry.nm A :: Γ)[i]? = some e → (Entry.nm A :: Δ)[Tm.up r i]? = some e := by
        intro i e hi
        cases i with
        | zero => simpa [Tm.up] using hi
        | succ i => simpa [Tm.up] using hr i e (by simpa using hi)
      exact .mu (ih (Tm.up r) hr') (hr' _ _ hβ)

theorem weaken {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) (e : Entry) :
    Typ (e :: Γ) (Tm.ren Nat.succ t) A :=
  h.ren Nat.succ (fun i e' hi => by simpa using hi)

/-- Well-typed substitutions: terms for term variables, variables (names) for names. -/
def SubstOK (Γ Δ : List Entry) (σ : ℕ → Tm) : Prop :=
  (∀ i A, Γ[i]? = some (.tm A) → Typ Δ (σ i) A) ∧
    (∀ i A, Γ[i]? = some (.nm A) → ∃ j, σ i = Tm.var j ∧ Δ[j]? = some (.nm A))

theorem SubstOK.up {Γ Δ : List Entry} {σ : ℕ → Tm} (h : SubstOK Γ Δ σ) (e : Entry) :
    SubstOK (e :: Γ) (e :: Δ) (Tm.upS σ) := by
  refine ⟨?_, ?_⟩
  · intro i A hi
    cases i with
    | zero => simp at hi; subst hi; exact .var (by simp)
    | succ i => exact (h.1 i A (by simpa using hi)).weaken e
  · intro i A hi
    cases i with
    | zero => simp at hi; subst hi; exact ⟨0, rfl, by simp⟩
    | succ i =>
        obtain ⟨j, hj, hΔ⟩ := h.2 i A (by simpa using hi)
        exact ⟨j + 1, by simp [Tm.upS, hj, Tm.ren], by simpa using hΔ⟩

theorem subst {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {Δ : List Entry} {σ : ℕ → Tm}, SubstOK Γ Δ σ → Typ Δ (Tm.subst σ t) A := by
  induction h with
  | var hi => intro Δ σ hσ; exact hσ.1 _ _ hi
  | lam _ ih => intro Δ σ hσ; exact .lam (ih (hσ.up _))
  | app _ _ iht ihu => intro Δ σ hσ; exact .app (iht hσ) (ihu hσ)
  | @mu Γ β t A B _ hβ ih =>
      intro Δ σ hσ
      obtain ⟨j, hj, hΔ⟩ := (hσ.up (.nm A)).2 β B hβ
      refine .mu (ih (hσ.up _)) ?_
      rw [hj]; exact hΔ

theorem substOK_single {Γ : List Entry} {u : Tm} {A : Ty} (hu : Typ Γ u A) :
    SubstOK (.tm A :: Γ) Γ (Tm.single u) := by
  refine ⟨?_, ?_⟩
  · intro i B hi
    cases i with
    | zero => simp at hi; subst hi; exact hu
    | succ i => exact .var (by simpa using hi)
  · intro i B hi
    cases i with
    | zero => simp at hi
    | succ i => exact ⟨i, rfl, by simpa using hi⟩

theorem substOK_single_name {Γ : List Entry} {β : ℕ} {A : Ty} (hβ : Γ[β]? = some (.nm A)) :
    SubstOK (.nm A :: Γ) Γ (Tm.single (Tm.var β)) := by
  refine ⟨?_, ?_⟩
  · intro i B hi
    cases i with
    | zero => simp at hi
    | succ i => exact .var (by simpa using hi)
  · intro i B hi
    cases i with
    | zero => simp at hi; subst hi; exact ⟨β, rfl, hβ⟩
    | succ i => exact ⟨i, rfl, by simpa using hi⟩

/-- Typing of the structural substitution: the name `a` changes type from `C → D` to `D`. -/
theorem sstr {Γ : List Entry} {t : Tm} {B : Ty} (h : Typ Γ t B) :
    ∀ {Γ' : List Entry} {a : ℕ} {C D : Ty} {v : Tm}, Γ[a]? = some (.nm (.arr C D)) →
      Γ'[a]? = some (.nm D) → (∀ i, i ≠ a → Γ'[i]? = Γ[i]?) → Typ Γ' v C →
      Typ Γ' (Tm.sstr a v t) B := by
  induction h with
  | @var Γ i A hi =>
      intro Γ' a C D v ha ha' hrest hv
      have hia : i ≠ a := by rintro rfl; rw [ha] at hi; cases hi
      exact .var (by rw [hrest i hia]; exact hi)
  | @lam Γ t A B _ ih =>
      intro Γ' a C D v ha ha' hrest hv
      refine .lam (ih (by simpa using ha) (by simpa using ha') ?_ (hv.weaken _))
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simpa using hrest i (by omega)
  | app _ _ iht ihu =>
      intro Γ' a C D v ha ha' hrest hv
      exact .app (iht ha ha' hrest hv) (ihu ha ha' hrest hv)
  | @mu Γ β t A B _ hβ ih =>
      intro Γ' a C D v ha ha' hrest hv
      have hrest' : ∀ i, i ≠ a + 1 → (Entry.nm A :: Γ')[i]? = (Entry.nm A :: Γ)[i]? := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => simpa using hrest i (by omega)
      have ih' := ih (Γ' := Entry.nm A :: Γ') (a := a + 1) (by simpa using ha)
        (by simpa using ha') hrest' (hv.weaken _)
      simp only [Tm.sstr]
      split_ifs with hβa
      · subst hβa
        have hB : B = .arr C D := by
          have : (Entry.nm A :: Γ)[a + 1]? = Γ[a]? := by simp
          rw [this, ha] at hβ; cases hβ; rfl
        subst hB
        exact .mu (.app ih' (hv.weaken _)) (by simpa using ha')
      · exact .mu ih' (by rw [hrest' β hβa]; exact hβ)

/-- **Subject reduction** for λμ. -/
theorem step {t t' : Tm} (hs : Step t t') : ∀ {Γ : List Entry} {A : Ty}, Typ Γ t A → Typ Γ t' A := by
  induction hs with
  | beta t u =>
      intro Γ A h
      cases h with
      | app ht hu =>
          cases ht with
          | lam ht => exact ht.subst (substOK_single hu)
  | struct β t u =>
      intro Γ D h
      cases h with
      | @app _ _ _ C _ ht hu =>
          cases ht with
          | @mu _ _ _ _ B ht hβ =>
              have hv : Typ (.nm D :: Γ) (Tm.ren Nat.succ u) C := hu.weaken _
              have hrest : ∀ i, i ≠ 0 →
                  (Entry.nm D :: Γ)[i]? = (Entry.nm (.arr C D) :: Γ)[i]? := by
                intro i hi
                cases i with
                | zero => exact absurd rfl hi
                | succ i => simp
              have h' := ht.sstr (Γ' := .nm D :: Γ) (a := 0) (C := C) (D := D) (by simp) (by simp) hrest hv
              split_ifs with hβ0
              · subst hβ0
                simp at hβ; subst hβ
                exact .mu (B := D) (.app h' hv) (by simp)
              · exact .mu h' (by rw [hrest β hβ0]; exact hβ)
  | rename β γ t =>
      intro Γ A h
      cases h with
      | @mu _ _ _ _ B h hβ =>
          cases h with
          | @mu _ _ _ _ C h hγ =>
              have hβ' : (Entry.nm A :: Γ)[β]? = some (.nm B) := hβ
              have ht := h.subst (substOK_single_name hβ')
              refine .mu ht ?_
              cases γ with
              | zero => simp at hγ; subst hγ; exact hβ'
              | succ γ => simpa [Tm.single, Tm.nameOf] using hγ
  | lam _ ih =>
      intro Γ A h
      cases h with
      | lam h => exact .lam (ih h)
  | appL u _ ih =>
      intro Γ A h
      cases h with
      | app ht hu => exact .app (ih ht) hu
  | appR t _ ih =>
      intro Γ A h
      cases h with
      | app ht hu => exact .app ht (ih hu)
  | mu β _ ih =>
      intro Γ A h
      cases h with
      | mu h hβ => exact .mu (ih h) hβ

end Typ

/-- **Subject reduction** for λμ (statement form). -/
theorem subject_reduction {Γ : List Entry} {t t' : Tm} {A : Ty} (h : Typ Γ t A)
    (hs : Step t t') : Typ Γ t' A :=
  Typ.step hs h

/-- **`call/cc` has the type of Peirce's law** `((A → B) → A) → A`, in every context. -/
theorem typ_callcc (Γ : List Entry) (A B : Ty) :
    Typ Γ Tm.callcc (.arr (.arr (.arr A B) A) A) := by
  unfold Tm.callcc
  refine .lam (.mu (B := A) (.app (A := .arr A B) (.var (by simp)) (.lam (.mu (B := A) (.var (by simp))
    (by simp)))) (by simp))

end LambdaMu
