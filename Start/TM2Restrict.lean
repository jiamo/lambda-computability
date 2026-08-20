/-
# Restricting a TM2 machine to a finite set of labels

`Turing.FinTM2`, the bundled form of a TM2 machine used by `Mathlib`'s
`Turing.TM2Computable`, insists that the type of function labels is finite.  A machine given
as an arbitrary `M : Λ → Turing.TM2.Stmt Γ Λ σ` together with a finite set `S : Finset Λ`
which it never leaves (`Turing.TM2.Supports M S`) can be turned into such a bundled machine
by restricting the labels to `S`: every `goto` inside a supported statement jumps into `S`,
so the target can be read as an element of the subtype `↥S`.

This file defines that restriction (`TM2Partrec.restrict`) and proves that it simulates the
original machine step by step (`TM2Partrec.mapCfg_step`, `TM2Partrec.iterate_map_opt`).  The
translation of configurations `TM2Partrec.mapCfg` simply forgets the membership proof, so it
is injective and the simulation can be read in both directions.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TM2Partrec

open Turing

section Restrict

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ : Type} [DecidableEq Λ] {σ : Type}

/-- Restriction of a statement to the labels of `S`: a `goto` whose target lies outside `S`
is redirected to the fallback label `q₀` (this never happens in a supported statement). -/
def restrictStmt (S : Finset Λ) (q₀ : {x // x ∈ S}) :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ {x // x ∈ S} σ
  | .push k f q => .push k f (restrictStmt S q₀ q)
  | .peek k f q => .peek k f (restrictStmt S q₀ q)
  | .pop k f q => .pop k f (restrictStmt S q₀ q)
  | .load a q => .load a (restrictStmt S q₀ q)
  | .branch p q₁ q₂ => .branch p (restrictStmt S q₀ q₁) (restrictStmt S q₀ q₂)
  | .goto l => .goto fun v => if h : l v ∈ S then ⟨l v, h⟩ else q₀
  | .halt => .halt

/-- The restricted machine. -/
def restrict (S : Finset Λ) (q₀ : {x // x ∈ S}) (M : Λ → TM2.Stmt Γ Λ σ) :
    {x // x ∈ S} → TM2.Stmt Γ {x // x ∈ S} σ :=
  fun q => restrictStmt S q₀ (M q)

/-- Reading a configuration of the restricted machine as a configuration of the original
machine: forget the membership proof carried by the label. -/
def mapCfg (S : Finset Λ) (c : TM2.Cfg Γ {x // x ∈ S} σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val, c.var, c.stk⟩

omit [DecidableEq K] [DecidableEq Λ] in
theorem mapCfg_injective (S : Finset Λ) :
    Function.Injective (mapCfg (Γ := Γ) (σ := σ) S) := by
  rintro ⟨l₁, v₁, T₁⟩ ⟨l₂, v₂, T₂⟩ h
  simp only [mapCfg, TM2.Cfg.mk.injEq] at h
  obtain ⟨hl, hv, hT⟩ := h
  have hl' : l₁ = l₂ := Option.map_injective Subtype.val_injective hl
  subst hl'; subst hv; subst hT
  rfl

/-- The restricted statement performs the same computation as the original one, as long as
the original statement is supported. -/
theorem mapCfg_stepAux (S : Finset Λ) (q₀ : {x // x ∈ S}) :
    ∀ (q : TM2.Stmt Γ Λ σ), TM2.SupportsStmt S q →
      ∀ (v : σ) (T : ∀ k, List (Γ k)),
        mapCfg S (TM2.stepAux (restrictStmt S q₀ q) v T) = TM2.stepAux q v T := by
  intro q
  induction q with
  | push k f q ih => intro hq v T; exact ih hq _ _
  | peek k f q ih => intro hq v T; exact ih hq _ _
  | pop k f q ih => intro hq v T; exact ih hq _ _
  | load a q ih => intro hq v T; exact ih hq _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
      intro hq v T
      simp only [restrictStmt, TM2.stepAux]
      cases hp : p v
      · simpa using ih₂ hq.2 v T
      · simpa using ih₁ hq.1 v T
  | goto l =>
      intro hq v T
      simp only [restrictStmt, TM2.stepAux, mapCfg, Option.map_some]
      rw [dif_pos (hq v)]
  | halt => intro _ v T; rfl

/-- One step of the restricted machine is one step of the original machine. -/
theorem mapCfg_step (S : Finset Λ) (q₀ : {x // x ∈ S}) (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) (c : TM2.Cfg Γ {x // x ∈ S} σ) :
    (TM2.step (restrict S q₀ M) c).map (mapCfg S) = TM2.step M (mapCfg S c) := by
  obtain ⟨l, v, T⟩ := c
  cases l with
  | none => rfl
  | some q =>
      simp only [mapCfg, Option.map_some, TM2.step, restrict]
      exact congrArg some (mapCfg_stepAux S q₀ (M q) (hM q q.2) v T)

/-- The simulation, on optional configurations. -/
theorem mapCfg_bind_step (S : Finset Λ) (q₀ : {x // x ∈ S}) (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) (o : Option (TM2.Cfg Γ {x // x ∈ S} σ)) :
    (flip Bind.bind (TM2.step (restrict S q₀ M)) o).map (mapCfg S) =
      flip Bind.bind (TM2.step M) (o.map (mapCfg S)) := by
  cases o with
  | none => rfl
  | some c => exact mapCfg_step S q₀ M hM c

/-- The restricted machine simulates the original machine for any number of steps. -/
theorem iterate_map_opt (S : Finset Λ) (q₀ : {x // x ∈ S}) (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) :
    ∀ (t : ℕ) (o : Option (TM2.Cfg Γ {x // x ∈ S} σ)),
      ((flip Bind.bind (TM2.step (restrict S q₀ M)))^[t] o).map (mapCfg S) =
        (flip Bind.bind (TM2.step M))^[t] (o.map (mapCfg S)) := by
  intro t
  induction t with
  | zero => intro o; rfl
  | succ t ih =>
      intro o
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
        mapCfg_bind_step S q₀ M hM]

end Restrict

end TM2Partrec
