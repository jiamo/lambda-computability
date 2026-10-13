/-
**A normalization function for strongly normalizing PTS expressions, and decidable conversion.**

Step (f) of task `M23-COC-SN` (decidable type checking for the calculus of constructions) starts
here.  This module gives, for any pure type system:

* `Expr.step?`, a computable one-step reduction finder, with `step?_sound` (a returned expression
  is a `Beta` reduct) and `step?_none` (no result means `Normal`);
* `normalize M h`, defined by well-founded recursion on `h : StronglyNormalizing M` (accessibility
  for the converse of `Beta`); it is computable and returns a normal form reachable by `Reduces`
  (`reduces_normalize`, `normal_normalize`);
* `converts_iff_normalize_eq`: two strongly normalizing expressions are convertible exactly when
  their normal forms are equal (by `Reduces.confluent` / `Normal.eq_of_converts`), hence
  `decConverts`, a decision procedure for `Converts` on strongly normalizing expressions.

Applied to the calculus of constructions with `coc_stronglyNormalizing`, conversion of legal
expressions in valid contexts is decidable (`Start/CoCNormalize.lean`).
-/

import Start.PTSReduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

namespace Expr

variable {S : Type u}

/-- One leftmost-outermost `Beta` step, if there is one. -/
def step? : Expr S → Option (Expr S)
  | .var _ => none
  | .sort _ => none
  | .app f a =>
      match f with
      | .lam _ b => some (b.instantiate a)
      | _ =>
          match step? f with
          | some f' => some (.app f' a)
          | none => (step? a).map (.app f ·)
  | .lam A b =>
      match step? A with
      | some A' => some (.lam A' b)
      | none => (step? b).map (.lam A ·)
  | .pi A B =>
      match step? A with
      | some A' => some (.pi A' B)
      | none => (step? B).map (.pi A ·)

/-- An expression is a `λ`-abstraction. -/
def IsLam : Expr S → Prop
  | .lam _ _ => True
  | _ => False

theorem step?_app_of_not_lam {f a : Expr S} (hf : ¬ IsLam f) :
    step? (.app f a) =
      match step? f with
      | some f' => some (.app f' a)
      | none => (step? a).map (.app f ·) := by
  cases f with
  | lam A b => exact (hf trivial).elim
  | var n => rfl
  | sort s => rfl
  | app g c => rfl
  | pi A B => rfl

theorem step?_sound : ∀ {M N : Expr S}, step? M = some N → Beta M N
  | .var _, _, h => by simp [step?] at h
  | .sort _, _, h => by simp [step?] at h
  | .app f a, N, h => by
      by_cases hf : IsLam f
      · cases f with
        | lam A b =>
            simp only [step?, Option.some.injEq] at h
            subst h
            exact .head A b a
        | _ => exact hf.elim
      · rw [step?_app_of_not_lam hf] at h
        cases hs : step? f with
        | some f' =>
            rw [hs] at h
            simp only [Option.some.injEq] at h
            subst h
            exact .app_left (step?_sound hs)
        | none =>
            rw [hs] at h
            cases ha : step? a with
            | none => rw [ha] at h; simp at h
            | some a' =>
                rw [ha] at h
                simp only [Option.map_some, Option.some.injEq] at h
                subst h
                exact .app_right (step?_sound ha)
  | .lam A b, N, h => by
      simp only [step?] at h
      cases hs : step? A with
      | some A' =>
          rw [hs] at h
          simp only [Option.some.injEq] at h
          subst h
          exact .lam_domain (step?_sound hs)
      | none =>
          rw [hs] at h
          cases hb : step? b with
          | none => rw [hb] at h; simp at h
          | some b' =>
              rw [hb] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              exact .lam_body (step?_sound hb)
  | .pi A B, N, h => by
      simp only [step?] at h
      cases hs : step? A with
      | some A' =>
          rw [hs] at h
          simp only [Option.some.injEq] at h
          subst h
          exact .pi_domain (step?_sound hs)
      | none =>
          rw [hs] at h
          cases hb : step? B with
          | none => rw [hb] at h; simp at h
          | some B' =>
              rw [hb] at h
              simp only [Option.map_some, Option.some.injEq] at h
              subst h
              exact .pi_body (step?_sound hb)

theorem step?_none : ∀ {M : Expr S}, step? M = none → Normal M
  | .var _, _ => Normal.var _
  | .sort _, _ => Normal.sort _
  | .app f a, h => by
      by_cases hf : IsLam f
      · cases f with
        | lam A b => simp [step?] at h
        | _ => exact hf.elim
      · rw [step?_app_of_not_lam hf] at h
        cases hs : step? f with
        | some f' => rw [hs] at h; simp at h
        | none =>
            rw [hs] at h
            cases ha : step? a with
            | some a' => rw [ha] at h; simp at h
            | none =>
                intro N hN
                cases hN with
                | head A b _ => exact hf trivial
                | app_left h' => exact step?_none hs _ h'
                | app_right h' => exact step?_none ha _ h'
  | .lam A b, h => by
      simp only [step?] at h
      cases hs : step? A with
      | some A' => rw [hs] at h; simp at h
      | none =>
          rw [hs] at h
          cases hb : step? b with
          | some b' => rw [hb] at h; simp at h
          | none =>
              intro N hN
              cases hN with
              | lam_domain h' => exact step?_none hs _ h'
              | lam_body h' => exact step?_none hb _ h'
  | .pi A B, h => by
      simp only [step?] at h
      cases hs : step? A with
      | some A' => rw [hs] at h; simp at h
      | none =>
          rw [hs] at h
          cases hb : step? B with
          | some B' => rw [hb] at h; simp at h
          | none =>
              intro N hN
              cases hN with
              | pi_domain h' => exact step?_none hs _ h'
              | pi_body h' => exact step?_none hb _ h'

/-- `Normal` is decidable. -/
instance decNormal (M : Expr S) : Decidable (Normal M) :=
  match hs : step? M with
  | none => isTrue (step?_none hs)
  | some _ => isFalse fun hn => hn _ (step?_sound hs)

end Expr

variable {S : Type u}

/-- Strongly normalizing expressions, ordered by the converse of `Beta`. -/
structure SNExpr (S : Type u) where
  /-- The expression. -/
  expr : Expr S
  /-- Its strong normalization. -/
  sn : StronglyNormalizing expr

theorem SNExpr.acc (M : Expr S) (hM : StronglyNormalizing M) :
    Acc (fun a b : SNExpr S => Beta b.expr a.expr) ⟨M, hM⟩ := by
  induction hM with
  | intro M _ ih => exact ⟨_, fun ⟨N, _⟩ hr => ih N hr⟩

instance SNExpr.wellFoundedRelation : WellFoundedRelation (SNExpr S) where
  rel a b := Beta b.expr a.expr
  wf := ⟨fun ⟨M, hM⟩ => SNExpr.acc M hM⟩

/-- **The normal form of a strongly normalizing expression**, by well-founded recursion on the
strong normalization proof (leftmost-outermost reduction). -/
def normalize (M : Expr S) (h : StronglyNormalizing M) : Expr S :=
  match hs : Expr.step? M with
  | none => M
  | some N => normalize N (h.step (Expr.step?_sound hs))
termination_by SNExpr.mk M h
decreasing_by exact Expr.step?_sound hs

/-- `normalize` returns a normal form reachable by reduction. -/
theorem normalize_spec (M : Expr S) (h : StronglyNormalizing M) :
    Reduces M (normalize M h) ∧ Normal (normalize M h) := by
  have key : ∀ M : Expr S, StronglyNormalizing M → ∀ h : StronglyNormalizing M,
      Reduces M (normalize M h) ∧ Normal (normalize M h) := by
    intro M hM
    induction hM with
    | intro M _ ih =>
      intro h
      rw [normalize]
      split
      · next hs => exact ⟨.refl, Expr.step?_none hs⟩
      · next N hs =>
        obtain ⟨h1, h2⟩ := ih N (Expr.step?_sound hs) (h.step (Expr.step?_sound hs))
        exact ⟨Relation.ReflTransGen.head (Expr.step?_sound hs) h1, h2⟩
  exact key M h h

theorem reduces_normalize (M : Expr S) (h : StronglyNormalizing M) :
    Reduces M (normalize M h) := (normalize_spec M h).1

theorem normal_normalize (M : Expr S) (h : StronglyNormalizing M) :
    Normal (normalize M h) := (normalize_spec M h).2

/-- `normalize` computes the unique normal form. -/
theorem normalize_eq_of_reduces {M N : Expr S} (h : StronglyNormalizing M) (hr : Reduces M N)
    (hN : Normal N) : normalize M h = N :=
  Normal.eq_of_converts (normal_normalize M h) hN
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reduces_normalize M h).converts)
      hr.converts)

/-- **Conversion of strongly normalizing expressions is equality of normal forms.** -/
theorem converts_iff_normalize_eq {M N : Expr S} (hM : StronglyNormalizing M)
    (hN : StronglyNormalizing N) : Converts M N ↔ normalize M hM = normalize N hN := by
  constructor
  · intro h
    apply Normal.eq_of_converts (normal_normalize M hM) (normal_normalize N hN)
    exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (reduces_normalize M hM).converts)
      (Relation.EqvGen.trans _ _ _ h (reduces_normalize N hN).converts)
  · intro h
    refine Relation.EqvGen.trans _ _ _ (reduces_normalize M hM).converts ?_
    rw [h]
    exact Relation.EqvGen.symm _ _ (reduces_normalize N hN).converts

/-- **Conversion is decidable on strongly normalizing expressions.** -/
def decConverts [DecidableEq S] {M N : Expr S} (hM : StronglyNormalizing M)
    (hN : StronglyNormalizing N) : Decidable (Converts M N) :=
  decidable_of_iff _ (converts_iff_normalize_eq hM hN).symm

end PureTypeSystem
