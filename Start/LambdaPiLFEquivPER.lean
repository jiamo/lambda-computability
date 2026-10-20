/-
**The LF equivalence algorithm is a partial equivalence relation** — task `M23-LF-EQUIV-COMPLETE`
(round 8, part C), continuing `Start/LambdaPiLFEquiv.lean`.

* `LambdaPi.WhStep.det` — **weak head reduction is deterministic**;
* `LambdaPi.IsPath`, `LambdaPi.IsPath.whnf` — paths (a variable applied to arguments) are weak
  head normal; `LambdaPi.WhRed.whnf_unique` — **weak head normal forms are unique**;
* `LambdaPi.Eqv.path_isPath` — structurally equivalent terms are paths;
  `LambdaPi.Eqv.path_ty_unique` — the skeleton synthesised for a path is unique;
* `LambdaPi.Eqv.symm` — **symmetry** of algorithmic and structural equivalence;
* `LambdaPi.Eqv.trans` — **transitivity** of algorithmic and structural equivalence;
* `LambdaPi.LR.symm`, `LambdaPi.LR.trans` — the Kripke logical relation is a PER.

The product rule of the algorithm carries the side condition `skel Δ A = skel Δ A'` on the two
domains (added in round 8): without it the codomains are compared in a context that remembers
only the skeleton of the left domain, and symmetry fails at that rule.  The condition is
decidable, and holds for well-typed convertible domains (`skel_conv`).
-/

import Start.LambdaPiLFEquiv

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Determinacy of weak head reduction -/

theorem WhStep.not_lam {A b u : Tm} : ¬ WhStep (lam A b) u := by
  intro h; cases h

/-- **Weak head reduction is deterministic.** -/
theorem WhStep.det {t u v : Tm} (hu : WhStep t u) (hv : WhStep t v) : u = v := by
  induction hu generalizing v with
  | beta A b a =>
      cases hv with
      | beta => rfl
      | appL _ h => exact absurd h WhStep.not_lam
  | appL a h ih =>
      cases hv with
      | beta => exact absurd h WhStep.not_lam
      | appL _ h' => rw [ih h']

/-- Weak head normal forms. -/
def WhNF (t : Tm) : Prop := ∀ u, ¬ WhStep t u

theorem whnf_sort (s : Srt) : WhNF (sort s) := fun _ h => by cases h
theorem whnf_pi (A B : Tm) : WhNF (pi A B) := fun _ h => by cases h

/-- Paths: a variable applied to arguments. -/
inductive IsPath : Tm → Prop
  | var (n : ℕ) : IsPath (var n)
  | app {p : Tm} (a : Tm) : IsPath p → IsPath (app p a)

theorem IsPath.not_lam {A b : Tm} (h : IsPath (lam A b)) : False := by cases h

theorem IsPath.whnf {p : Tm} (h : IsPath p) : WhNF p := by
  induction h with
  | var n => intro u hu; cases hu
  | app a hp ih =>
      intro u hu
      cases hu with
      | beta => exact hp.not_lam
      | appL _ h => exact ih _ h

theorem IsPath.ne_sort {p : Tm} {s : Srt} (h : IsPath p) : p ≠ sort s := by
  intro e; subst e; cases h

theorem IsPath.ne_pi {p A B : Tm} (h : IsPath p) : p ≠ pi A B := by
  intro e; subst e; cases h

/-- From a weak head normal form, weak head reduction is trivial. -/
theorem WhRed.of_whnf {t u : Tm} (h : WhRed t u) (ht : WhNF t) : u = t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | head hs _ _ => exact absurd hs (ht _)

/-- A deterministic relation: two reductions to a normal form end at the same place. -/
theorem WhRed.whnf_unique {t u v : Tm} (hu : WhRed t u) (hv : WhRed t v) (hnu : WhNF u)
    (hnv : WhNF v) : u = v := by
  induction hu using Relation.ReflTransGen.head_induction_on generalizing v with
  | refl => exact (hv.of_whnf hnu).symm
  | head hs _ ih =>
      cases hv using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd hs (hnv _)
      | head hs' hv' =>
          rw [WhStep.det hs hs'] at *
          exact ih hv' hnv

/-! ### Paths and their skeletons -/

/-- The judgements of the algorithm, with `path` giving paths on both sides. -/
theorem Eqv.path_isPath {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : Eqv k Δ M N τ) :
    k = .path → IsPath M ∧ IsPath N := by
  induction h with
  | arrow => intro h; cases h
  | basePath => intro h; cases h
  | baseSort => intro h; cases h
  | basePi => intro h; cases h
  | var n => intro _; exact ⟨.var n, .var n⟩
  | app _ _ ihp _ =>
      intro _
      obtain ⟨hp, hq⟩ := ihp rfl
      exact ⟨.app _ hp, .app _ hq⟩

theorem PathEq.isPath {Δ : List STy} {M N : Tm} {τ : STy} (h : PathEq Δ M N τ) :
    IsPath M ∧ IsPath N :=
  Eqv.path_isPath h rfl

/-! ### Symmetry -/

/-- **Symmetry of the algorithm.** -/
theorem Eqv.symm {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : Eqv k Δ M N τ) :
    Eqv k Δ N M τ := by
  induction h with
  | arrow _ ih => exact Eqv.arrow ih
  | basePath hM hN _ ih => exact Eqv.basePath hN hM ih
  | baseSort hM hN => exact Eqv.baseSort hN hM
  | basePi hM hN _ hsk _ ihA ihB =>
      refine Eqv.basePi hN hM ihA hsk.symm ?_
      rw [← hsk]; exact ihB
  | var n => exact Eqv.var n
  | app _ _ ihp iha => exact Eqv.app ihp iha

/-! ### Transitivity -/

/-- The core of transitivity: the second derivation is analysed by cases; for paths the
synthesised skeletons agree. -/
theorem Eqv.trans_aux {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : Eqv k Δ M N τ) :
    ∀ {P : Tm} {τ' : STy}, Eqv k Δ N P τ' → (k = .alg → τ = τ') →
      τ = τ' ∧ Eqv k Δ M P τ := by
  induction h with
  | @arrow Δ M N σ τ _ ih =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      cases h2 with
      | arrow h2 =>
          refine ⟨rfl, Eqv.arrow (ih h2 (fun _ => rfl)).2⟩
  | @basePath Δ M N M' N' hM hN hp ih =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      have hN'p := (PathEq.isPath hp).2
      refine ⟨rfl, ?_⟩
      cases h2 with
      | basePath hN₂ hP hp₂ =>
          have e := WhRed.whnf_unique hN hN₂ hN'p.whnf (PathEq.isPath hp₂).1.whnf
          subst e
          exact Eqv.basePath hM hP (ih hp₂ (fun h => by cases h)).2
      | baseSort hN₂ hP =>
          have e := WhRed.whnf_unique hN hN₂ hN'p.whnf (whnf_sort _)
          exact absurd e hN'p.ne_sort
      | basePi hN₂ hP _ _ _ =>
          have e := WhRed.whnf_unique hN hN₂ hN'p.whnf (whnf_pi _ _)
          exact absurd e hN'p.ne_pi
  | @baseSort Δ M N s hM hN =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      refine ⟨rfl, ?_⟩
      cases h2 with
      | basePath hN₂ hP hp₂ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_sort _) (PathEq.isPath hp₂).1.whnf
          exact absurd e.symm (PathEq.isPath hp₂).1.ne_sort
      | baseSort hN₂ hP =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_sort _) (whnf_sort _)
          cases e
          exact Eqv.baseSort hM hP
      | basePi hN₂ hP _ _ _ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_sort _) (whnf_pi _ _)
          cases e
  | @basePi Δ M N A B A' B' hM hN _ hsk _ ihA ihB =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      refine ⟨rfl, ?_⟩
      cases h2 with
      | basePath hN₂ hP hp₂ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_pi _ _) (PathEq.isPath hp₂).1.whnf
          exact absurd e.symm (PathEq.isPath hp₂).1.ne_pi
      | baseSort hN₂ hP =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_pi _ _) (whnf_sort _)
          cases e
      | basePi hN₂ hP hA₂ hsk₂ hB₂ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_pi _ _) (whnf_pi _ _)
          cases e
          refine Eqv.basePi hM hP (ihA hA₂ (fun _ => rfl)).2 (hsk.trans hsk₂) ?_
          rw [← hsk] at hB₂
          exact (ihB hB₂ (fun _ => rfl)).2
  | var n =>
      intro P τ' h2 _
      cases h2 with
      | var => exact ⟨rfl, Eqv.var n⟩
  | @app Δ p q a b σ τ _ _ ihp iha =>
      intro P τ' h2 _
      cases h2 with
      | app hq hb =>
          obtain ⟨e, hpr⟩ := ihp hq (fun h => by cases h)
          cases e
          exact ⟨rfl, Eqv.app hpr (iha hb (fun _ => rfl)).2⟩

/-- **Transitivity of the algorithm.** -/
theorem Eqv.trans {k : EqvKind} {Δ : List STy} {M N P : Tm} {τ : STy} (h : Eqv k Δ M N τ)
    (h' : Eqv k Δ N P τ) : Eqv k Δ M P τ :=
  (h.trans_aux h' (fun _ => rfl)).2

/-- The skeleton synthesised for a path is unique. -/
theorem Eqv.path_ty_unique {Δ : List STy} {p q r : Tm} {τ τ' : STy} (h : PathEq Δ p q τ)
    (h' : PathEq Δ q r τ') : τ = τ' :=
  (Eqv.trans_aux h h' (fun h => by cases h)).1

/-- Algorithmic equivalence is a PER: symmetric and transitive. -/
theorem AlgEq.per (Δ : List STy) (τ : STy) :
    (∀ {M N}, AlgEq Δ M N τ → AlgEq Δ N M τ) ∧
      (∀ {M N P}, AlgEq Δ M N τ → AlgEq Δ N P τ → AlgEq Δ M P τ) :=
  ⟨fun h => h.symm, fun h h' => h.trans h'⟩

/-! ### The logical relation is a PER -/

/-- **Symmetry of the logical relation.** -/
theorem LR.symm : ∀ {τ : STy} {Δ : List STy} {M N : Tm}, LR τ Δ M N → LR τ Δ N M
  | .base, _, _, _, h => Eqv.symm h
  | .arrow _ _, _, _, _, h => fun Δ' ρ hρ a b hab => LR.symm (h Δ' ρ hρ b a (LR.symm hab))

/-- **Transitivity of the logical relation** (using symmetry: `a ~ b` gives `b ~ b` by
`a ~ b`, `b ~ a`). -/
theorem LR.trans : ∀ {τ : STy} {Δ : List STy} {M N P : Tm}, LR τ Δ M N → LR τ Δ N P →
    LR τ Δ M P
  | .base, _, _, _, _, h, h' => Eqv.trans h h'
  | .arrow _ _, _, _, _, _, h, h' => fun Δ' ρ hρ a b hab =>
      LR.trans (h Δ' ρ hρ a b hab) (h' Δ' ρ hρ b b (LR.trans (LR.symm hab) hab))

end LambdaPi
