/-
Denotational semantics for Gödel's System T, and **adequacy**.

The library already contains *soundness* results for the denotational semantics of the untyped
calculus (`Start/GraphModelSemantics.lean`, `Start/ScottDinfModel.lean`): convertible terms have
equal denotations.  This file supplies the converse — the *adequacy* half — in the setting where
it can be stated for closed terms of a base type, namely Gödel's System T.

* `GodelT.tyDen` — the full set-theoretic hierarchy, `⟦nat⟧ = ℕ` and `⟦A ⇒ B⟧ = ⟦A⟧ → ⟦B⟧`;
* `GodelT.Der` — typing derivations *as data*, so that they can be interpreted;
  `GodelT.Der.toTyping` and `GodelT.nonempty_der_of_typing` identify them with the `Prop`-valued
  `GodelT.Typing`;
* `GodelT.eval` — the interpretation of a derivation in an environment, and `GodelT.denot`, the
  interpretation of a typable term (through the canonical derivation `GodelT.derOf`);
* `GodelT.LR` — the adequacy (logical) relation between a semantic value and a term, and
  `GodelT.lr_substEnv`, its fundamental lemma;
* `GodelT.adequacy` — **adequacy**: a closed term of type `nat` reduces to the numeral of its
  denotation;
* `GodelT.reduces_num_iff_denot` — combining adequacy with the confluence of
  `Start/SystemTConfluence.lean`: a closed term of type `nat` reduces to `num n` exactly when its
  denotation is `n`.  This is the base-type *soundness* companion of adequacy;
* `GodelT.denot_eq_iff_joins` — for closed terms of type `nat`, equality of denotations is
  equivalent to reduction to a common numeral, hence to convertibility;
* `GodelT.ObsEq` and `GodelT.obsEq_of_denot_eq` — equal denotations imply **observational
  equivalence**: no program context of type `nat` can tell the two terms apart.  At the base type
  the converse holds as well (`GodelT.denot_eq_of_obsEq_nat`), so there the three notions — equal
  denotation, convertibility, observational equivalence — coincide.

Boundaries.  Terms are Curry style (abstractions carry no type annotation), so a term can have
several typing derivations at the same type; `GodelT.denot` interprets a canonically chosen one,
and `GodelT.eval_irrel_nat` proves that at the base type the choice does not matter.  The converse
of observational equivalence at *higher* types (full abstraction) is not proved, and neither is
invariance of the denotation under reduction at higher types; invariance at the base type, which
is what the observational statements need, is `GodelT.reduces_num_iff_denot`.
-/

import Start.SystemTConfluence

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GodelT

------------------------------------------------------------------------
-- The set-theoretic model
------------------------------------------------------------------------

/-- The full set-theoretic hierarchy over `ℕ`. -/
def tyDen : Ty → Type
  | Ty.nat => ℕ
  | Ty.arrow A B => tyDen A → tyDen B

/-- Environments: a semantic value for each variable of the context. -/
def Env : List Ty → Type
  | [] => PUnit
  | A :: Γ => tyDen A × Env Γ

/-- The empty environment. -/
def Env.nil : Env [] := PUnit.unit

/-- Looking a variable up in an environment. -/
def Env.get : ∀ {Γ : List Ty} {i : ℕ} {A : Ty}, Γ[i]? = some A → Env Γ → tyDen A
  | [], _, _, h, _ => absurd h (by simp)
  | B :: _, 0, _, h, ρ => cast (congrArg tyDen (by simpa using h : B = _)) (Prod.fst ρ)
  | _ :: _, _ + 1, _, h, ρ => Env.get (by simpa using h) (Prod.snd ρ)

/-- Typing derivations as data, so that they can be interpreted in the model. -/
inductive Der : List Ty → Tm → Ty → Type
  | var {Γ : List Ty} {i : ℕ} {A : Ty} : Γ[i]? = some A → Der Γ (Tm.var i) A
  | app {Γ : List Ty} {a b : Tm} {A B : Ty} :
      Der Γ a (Ty.arrow A B) → Der Γ b A → Der Γ (Tm.app a b) B
  | lam {Γ : List Ty} {t : Tm} {A B : Ty} : Der (A :: Γ) t B → Der Γ (Tm.lam t) (Ty.arrow A B)
  | zero {Γ : List Ty} : Der Γ Tm.zero Ty.nat
  | succ {Γ : List Ty} {t : Tm} : Der Γ t Ty.nat → Der Γ (Tm.succ t) Ty.nat
  | natrec {Γ : List Ty} {z f n : Tm} {A : Ty} :
      Der Γ z A → Der Γ f (Ty.arrow Ty.nat (Ty.arrow A A)) → Der Γ n Ty.nat →
      Der Γ (Tm.natrec z f n) A

/-- The interpretation of a derivation. -/
def eval : ∀ {Γ : List Ty} {t : Tm} {A : Ty}, Der Γ t A → Env Γ → tyDen A
  | _, _, _, Der.var h, ρ => Env.get h ρ
  | _, _, _, Der.app d e, ρ => (eval d ρ) (eval e ρ)
  | _, _, _, Der.lam d, ρ => fun a => eval d (a, ρ)
  | _, _, _, Der.zero, _ => (0 : ℕ)
  | _, _, _, Der.succ d, ρ => Nat.succ (eval d ρ)
  | _, _, A, Der.natrec dz df dn, ρ =>
      Nat.rec (motive := fun _ => tyDen A) (eval dz ρ) (fun k ih => eval df ρ k ih) (eval dn ρ)

------------------------------------------------------------------------
-- Derivations and the typing relation
------------------------------------------------------------------------

theorem Der.toTyping : ∀ {Γ : List Ty} {t : Tm} {A : Ty}, Der Γ t A → Typing Γ t A
  | _, _, _, Der.var h => Typing.var h
  | _, _, _, Der.app d e => Typing.app d.toTyping e.toTyping
  | _, _, _, Der.lam d => Typing.lam d.toTyping
  | _, _, _, Der.zero => Typing.zero
  | _, _, _, Der.succ d => Typing.succ d.toTyping
  | _, _, _, Der.natrec dz df dn => Typing.natrec dz.toTyping df.toTyping dn.toTyping

theorem nonempty_der_of_typing {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    Nonempty (Der Γ t A) := by
  induction h with
  | var h => exact ⟨Der.var h⟩
  | app _ _ iha ihb => exact ⟨Der.app iha.some ihb.some⟩
  | lam _ ih => exact ⟨Der.lam ih.some⟩
  | zero => exact ⟨Der.zero⟩
  | succ _ ih => exact ⟨Der.succ ih.some⟩
  | natrec _ _ _ ihz ihf ihn => exact ⟨Der.natrec ihz.some ihf.some ihn.some⟩

/-- The canonical derivation of a typable term.  Since `Nonempty (Der Γ t A)` is a proposition,
this depends only on `Γ`, `t` and `A`. -/
noncomputable def derOf {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) : Der Γ t A :=
  Classical.choice (nonempty_der_of_typing h)

/-- The denotation of a typable term. -/
noncomputable def denot {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) : Env Γ → tyDen A :=
  eval (derOf h)

theorem denot_eq_eval_derOf {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) (ρ : Env Γ) :
    denot h ρ = eval (derOf h) ρ := rfl

------------------------------------------------------------------------
-- The adequacy relation
------------------------------------------------------------------------

/-- The adequacy (logical) relation: at the base type a semantic natural number is related to the
terms reducing to its numeral, and at a function type the relation is the usual one. -/
def LR : (A : Ty) → tyDen A → Tm → Prop
  | Ty.nat, n, t => reduces t (num n)
  | Ty.arrow A B, f, t => ∀ (a : tyDen A) (s : Tm), LR A a s → LR B (f a) (Tm.app t s)

/-- The relation is closed under expansion. -/
theorem LR.expand : ∀ (A : Ty) {v : tyDen A} {t t' : Tm}, reduces t t' → LR A v t' → LR A v t := by
  intro A
  induction A with
  | nat => intro v t t' hr h; exact hr.trans h
  | arrow A B _ ihB =>
      intro v t t' hr h a s hs
      exact ihB (reduces_appL hr) (h a s hs)

/-- The recursor is related to `Nat.rec`. -/
theorem lr_natrec {A : Ty} {zv : tyDen A} {fv : ℕ → tyDen A → tyDen A} {Z F : Tm}
    (hz : LR A zv Z) (hf : LR (Ty.arrow Ty.nat (Ty.arrow A A)) fv F) :
    ∀ k : ℕ, LR A (Nat.rec (motive := fun _ => tyDen A) zv fv k) (Tm.natrec Z F (num k)) := by
  intro k
  induction k with
  | zero => exact LR.expand A (reduces.step (step.recZero _ _) (reduces.refl _)) hz
  | succ k ih =>
      refine LR.expand A (reduces.step (step.recSucc _ _ _) (reduces.refl _)) ?_
      exact hf k (num k) (reduces.refl _) _ _ ih

/-- **Fundamental lemma of the adequacy relation.** -/
theorem lr_substEnv : ∀ {Γ : List Ty} {t : Tm} {A : Ty} (d : Der Γ t A) (σ : ℕ → Tm) (ρ : Env Γ),
    (∀ (i : ℕ) (A' : Ty) (h : Γ[i]? = some A'), LR A' (Env.get h ρ) (σ i)) →
      LR A (eval d ρ) (substEnv σ t) := by
  intro Γ t A d
  induction d with
  | var h => intro σ ρ hρ; exact hρ _ _ h
  | app _ _ iha ihb =>
      intro σ ρ hρ
      exact iha σ ρ hρ _ _ (ihb σ ρ hρ)
  | @lam _ t A B d ih =>
      intro σ ρ hρ a s hs
      refine LR.expand B (reduces.step (step.beta _ _) (reduces.refl _)) ?_
      rw [subst_zero_substEnv]
      refine ih (envScons s σ) (a, ρ) ?_
      intro i A' h
      cases i with
      | zero =>
          have hA : A = A' := by simpa using h
          subst hA
          exact hs
      | succ k => exact hρ k A' (by simpa using h)
  | zero => intro σ ρ _; exact reduces.refl _
  | succ d ih => intro σ ρ hρ; exact reduces_succ (ih σ ρ hρ)
  | natrec dz df dn ihz ihf ihn =>
      intro σ ρ hρ
      exact LR.expand _ (reduces_recR (ihn σ ρ hρ)) (lr_natrec (ihz σ ρ hρ) (ihf σ ρ hρ) _)

/-- The fundamental lemma for closed terms. -/
theorem lr_closed {t : Tm} {A : Ty} (d : Der [] t A) : LR A (eval d Env.nil) t := by
  have h := lr_substEnv d (fun k => Tm.var k) Env.nil (by
    intro i A' h
    simp at h)
  rwa [substEnv_var_id] at h

------------------------------------------------------------------------
-- Adequacy
------------------------------------------------------------------------

/-- **Adequacy**: a closed term of type `nat` reduces to the numeral of its denotation. -/
theorem adequacy {t : Tm} (h : Typing [] t Ty.nat) : reduces t (num (denot h Env.nil)) :=
  lr_closed (derOf h)

/-- **Adequacy and base-type soundness**: a closed term of type `nat` reduces to `num n` exactly
when its denotation is `n`. -/
theorem reduces_num_iff_denot {t : Tm} (h : Typing [] t Ty.nat) (n : ℕ) :
    reduces t (num n) ↔ denot h Env.nil = n := by
  constructor
  · intro hr
    exact eq_of_reduces_num_of_typing h (adequacy h) hr
  · intro he
    have hr := adequacy h
    rwa [he] at hr

/-- At the base type the interpretation does not depend on the chosen typing derivation. -/
theorem eval_irrel_nat {t : Tm} (d d' : Der [] t Ty.nat) :
    eval d Env.nil = eval d' Env.nil :=
  eq_of_reduces_num_of_typing d.toTyping (lr_closed d) (lr_closed d')

/-- Two closed terms of type `nat` have the same denotation exactly when they reduce to a common
numeral — in particular, exactly when they are convertible. -/
theorem denot_eq_iff_joins {t u : Tm} (ht : Typing [] t Ty.nat) (hu : Typing [] u Ty.nat) :
    denot ht Env.nil = denot hu Env.nil ↔ ∃ n : ℕ, reduces t (num n) ∧ reduces u (num n) := by
  constructor
  · intro h
    refine ⟨denot ht Env.nil, adequacy ht, ?_⟩
    rw [h]
    exact adequacy hu
  · rintro ⟨n, h1, h2⟩
    rw [(reduces_num_iff_denot ht n).1 h1, (reduces_num_iff_denot hu n).1 h2]

------------------------------------------------------------------------
-- Observational equivalence
------------------------------------------------------------------------

/-- Observational equivalence of two closed terms of type `A`: no program context of type `nat`
distinguishes them.  A context is a term `c` with a single free variable of type `A`; since `t`
and `u` are closed, filling the hole is plain substitution. -/
def ObsEq (A : Ty) (t u : Tm) : Prop :=
  ∀ c : Tm, Typing [A] c Ty.nat → ∀ n : ℕ,
    reduces (subst t 0 c) (num n) ↔ reduces (subst u 0 c) (num n)

theorem substEnv_envScons_eq_subst (v c : Tm) :
    substEnv (envScons v (fun k => Tm.var k)) c = subst v 0 c := by
  have hcons : envCons (fun k => Tm.var k) = fun k => Tm.var k := by
    funext k
    cases k with
    | zero => rfl
    | succ k => simp [envCons, lift]
  have h := subst_zero_substEnv v c (fun k => Tm.var k)
  rw [hcons, substEnv_var_id] at h
  exact h.symm

/-- Filling a `nat`-context with a closed term of the right type: the resulting closed term
reduces to the numeral computed by the semantics. -/
theorem reduces_subst_num {A : Ty} {t c : Tm} (ht : Typing [] t A) (dc : Der [A] c Ty.nat) :
    reduces (subst t 0 c) (num (eval dc (denot ht Env.nil, Env.nil))) := by
  have hlr : LR A (denot ht Env.nil) t := lr_closed (derOf ht)
  have h := lr_substEnv dc (envScons t (fun k => Tm.var k)) (denot ht Env.nil, Env.nil) (by
    intro i A' hi
    cases i with
    | zero =>
        have hA : A = A' := by simpa using hi
        subst hA
        exact hlr
    | succ k => simp at hi)
  rwa [substEnv_envScons_eq_subst] at h

/-- **Equal denotations imply observational equivalence.** -/
theorem obsEq_of_denot_eq {A : Ty} {t u : Tm} (ht : Typing [] t A) (hu : Typing [] u A)
    (h : denot ht Env.nil = denot hu Env.nil) : ObsEq A t u := by
  intro c hc n
  have h1 := reduces_subst_num ht (derOf hc)
  have h2 := reduces_subst_num hu (derOf hc)
  rw [← h] at h2
  have hct : Typing [] (subst t 0 c) Ty.nat := typing_subst_zero hc ht
  have hcu : Typing [] (subst u 0 c) Ty.nat := typing_subst_zero hc hu
  constructor
  · intro hr
    rw [← eq_of_reduces_num_of_typing hct h1 hr]
    exact h2
  · intro hr
    rw [← eq_of_reduces_num_of_typing hcu h2 hr]
    exact h1

/-- At the base type the converse holds: observationally equivalent closed terms of type `nat`
have the same denotation. -/
theorem denot_eq_of_obsEq_nat {t u : Tm} (ht : Typing [] t Ty.nat) (hu : Typing [] u Ty.nat)
    (h : ObsEq Ty.nat t u) : denot ht Env.nil = denot hu Env.nil := by
  have hvar : Typing [Ty.nat] (Tm.var 0) Ty.nat := Typing.var (by simp)
  have hsub : ∀ v : Tm, subst v 0 (Tm.var 0) = v := by
    intro v; simp [subst]
  have h1 := adequacy ht
  have h2 : reduces u (num (denot ht Env.nil)) := by
    have := (h (Tm.var 0) hvar (denot ht Env.nil)).1 (by rw [hsub]; exact h1)
    rwa [hsub] at this
  exact ((reduces_num_iff_denot hu (denot ht Env.nil)).1 h2).symm

/-- At the base type, equal denotation and observational equivalence are the same relation. -/
theorem denot_eq_iff_obsEq_nat {t u : Tm} (ht : Typing [] t Ty.nat) (hu : Typing [] u Ty.nat) :
    denot ht Env.nil = denot hu Env.nil ↔ ObsEq Ty.nat t u :=
  ⟨fun h => obsEq_of_denot_eq ht hu h, fun h => denot_eq_of_obsEq_nat ht hu h⟩

/-- Non-vacuity: the denotation of `addTm` applied to two numerals is their sum. -/
theorem denot_addTm_eq (m n : ℕ) :
    denot (Typing.app (Typing.app typing_addTm (typing_num [] m)) (typing_num [] n)) Env.nil
      = m + n :=
  (reduces_num_iff_denot _ (m + n)).1 (reduces_addTm m n)

end GodelT
