/-
Scott's `D∞`, step one: the tower of function spaces and its embedding–projection pairs.

We build the classical tower

  `D 0 = Bool` (the two-point flat domain),   `D (n+1) = [D n →𝒄 D n]`

inside Lean by bundling the `OmegaCompletePartialOrder` instance and the least element into a
structure `Dom`, so that the tower can be defined by recursion on `ℕ` (a bare recursive
definition of the *type* family is impossible, since the function-space type needs the order
instance of the previous level).

The embedding–projection pairs

  `emb n : D n →𝒄 D (n+1)`,  `prj n : D (n+1) →𝒄 D n`

are defined by simultaneous recursion, and this file proves the two defining laws of an
ep-pair, `prj_emb : prj n (emb n x) = x` and `emb_prj_le : emb n (prj n f) ≤ f`.
-/

import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

/-- A bundled ω-complete partial order with a least element. -/
structure Dom : Type 1 where
  /-- The underlying type. -/
  carrier : Type
  [order : OmegaCompletePartialOrder carrier]
  /-- The least element. -/
  bot : carrier
  bot_le : ∀ x : carrier, bot ≤ x

attribute [instance] Dom.order

/-- The continuous function space of a domain, as a domain. -/
def Dom.fn (A : Dom) : Dom where
  carrier := A.carrier →𝒄 A.carrier
  bot := ContinuousHom.const A.bot
  bot_le := by
    intro f x
    exact A.bot_le (f x)

/-- The base domain: the two-point flat domain `false ⊑ true`. -/
def baseDom : Dom where
  carrier := Bool
  bot := false
  bot_le := by intro x; cases x <;> simp

/-- The tower `D 0 = Bool`, `D (n+1) = [D n →𝒄 D n]`. -/
def tower : ℕ → Dom
  | 0 => baseDom
  | (n + 1) => (tower n).fn

/-- The `n`-th level of the tower. -/
def D (n : ℕ) : Type := (tower n).carrier

instance instDOrder (n : ℕ) : OmegaCompletePartialOrder (D n) := (tower n).order

/-- The least element of `D n`. -/
def botD (n : ℕ) : D n := (tower n).bot

theorem botD_le (n : ℕ) (x : D n) : botD n ≤ x := (tower n).bot_le x

/-- `D (n+1)` *is* the function space `D n →𝒄 D n`; this is the (definitional) coercion. -/
def toFn {n : ℕ} (f : D (n + 1)) : D n →𝒄 D n := f

/-- The inverse of `toFn`. -/
def ofFn {n : ℕ} (f : D n →𝒄 D n) : D (n + 1) := f

@[simp] theorem toFn_ofFn {n : ℕ} (f : D n →𝒄 D n) : toFn (ofFn f) = f := rfl
@[simp] theorem ofFn_toFn {n : ℕ} (f : D (n + 1)) : ofFn (toFn f) = f := rfl

theorem toFn_le_iff {n : ℕ} {f g : D (n + 1)} : f ≤ g ↔ ∀ x, toFn f x ≤ toFn g x := Iff.rfl

theorem toFn_ext {n : ℕ} {f g : D (n + 1)} (h : ∀ x, toFn f x = toFn g x) : f = g := by
  have h' : toFn f = toFn g := DFunLike.ext _ _ h
  exact h'

/-- Evaluation at a point, as a monotone map on the function space. -/
def applyMono {n : ℕ} (x : D n) : D (n + 1) →o D n where
  toFun f := toFn f x
  monotone' _ _ h := h x

/-- Suprema in `D (n+1)` are computed pointwise. -/
theorem toFn_ωSup {n : ℕ} (c : Chain (D (n + 1))) (x : D n) :
    toFn (ωSup c) x = ωSup (c.map (applyMono x)) := rfl

@[simp] theorem toFn_botD (n : ℕ) (x : D n) : toFn (botD (n + 1)) x = botD n := rfl

------------------------------------------------------------------------
-- Continuity of composition in the middle argument
------------------------------------------------------------------------

/-- Sandwiching between two fixed continuous maps is a continuous operation on the function
space. -/
theorem sandwich_continuous {A B C E : Type}
    [OmegaCompletePartialOrder A] [OmegaCompletePartialOrder B]
    [OmegaCompletePartialOrder C] [OmegaCompletePartialOrder E]
    (u : B →𝒄 C) (v : A →𝒄 E) :
    ωScottContinuous (fun f : E →𝒄 B => u.comp (f.comp v)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, ?_⟩
  · intro f g hfg x
    exact u.monotone (hfg (v x))
  · intro c
    ext x
    simp only [ContinuousHom.ωSup_def, ContinuousHom.comp_assoc, ContinuousHom.comp_apply,
      ContinuousHom.ωSup_apply]
    rw [u.continuous]
    apply le_antisymm <;> apply ωSup_le <;> intro i <;> exact le_ωSup_of_le i (by rfl)

------------------------------------------------------------------------
-- The embedding–projection pairs
------------------------------------------------------------------------

/-- The embedding and projection of level `n`, defined by simultaneous recursion. -/
def ep : ∀ n : ℕ, (D n →𝒄 D (n + 1)) × (D (n + 1) →𝒄 D n)
  | 0 =>
      (ContinuousHom.ofFun (fun x : D 0 => ofFn (ContinuousHom.const x)) (by
          rw [ωScottContinuous_iff_monotone_map_ωSup]
          refine ⟨fun x y hxy _ => hxy, ?_⟩
          intro c
          refine toFn_ext ?_
          intro x
          rw [toFn_ωSup]
          have hc : (c.map ⟨fun y : D 0 => ofFn (ContinuousHom.const y),
              fun _ _ hxy _ => hxy⟩).map (applyMono x) = c := by
            ext i
            rfl
          rw [hc]
          rfl),
       ContinuousHom.ofFun (fun f : D 1 => toFn f (botD 0)) (by
          rw [ωScottContinuous_iff_monotone_map_ωSup]
          refine ⟨fun f g hfg => hfg (botD 0), ?_⟩
          intro c
          rw [toFn_ωSup]
          rfl))
  | (n + 1) =>
      (ContinuousHom.ofFun
          (fun f : D (n + 1) => ofFn (((ep n).1).comp ((toFn f).comp ((ep n).2))))
          (sandwich_continuous ((ep n).1) ((ep n).2)),
       ContinuousHom.ofFun
          (fun f : D (n + 2) => ofFn (((ep n).2).comp ((toFn f).comp ((ep n).1))))
          (sandwich_continuous ((ep n).2) ((ep n).1)))

/-- The embedding `D n → D (n+1)`. -/
def emb (n : ℕ) : D n →𝒄 D (n + 1) := (ep n).1

/-- The projection `D (n+1) → D n`. -/
def prj (n : ℕ) : D (n + 1) →𝒄 D n := (ep n).2

@[simp] theorem emb_zero_apply (x : D 0) (y : D 0) : toFn (emb 0 x) y = x := rfl
@[simp] theorem prj_zero_apply (f : D 1) : prj 0 f = toFn f (botD 0) := rfl

@[simp] theorem emb_succ_apply (n : ℕ) (f : D (n + 1)) (x : D (n + 1)) :
    toFn (emb (n + 1) f) x = emb n (toFn f (prj n x)) := rfl

@[simp] theorem prj_succ_apply (n : ℕ) (f : D (n + 2)) (x : D n) :
    toFn (prj (n + 1) f) x = prj n (toFn f (emb n x)) := rfl

/-- First ep-pair law: the projection undoes the embedding. -/
theorem prj_emb (n : ℕ) (x : D n) : prj n (emb n x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine toFn_ext ?_
      intro y
      rw [prj_succ_apply, emb_succ_apply, ih, ih]

/-- Second ep-pair law: the embedding of a projection is below the original. -/
theorem emb_prj_le (n : ℕ) (f : D (n + 1)) : emb n (prj n f) ≤ f := by
  induction n with
  | zero =>
      rw [toFn_le_iff]
      intro x
      rw [emb_zero_apply, prj_zero_apply]
      exact (toFn f).monotone (botD_le 0 x)
  | succ n ih =>
      rw [toFn_le_iff]
      intro x
      rw [emb_succ_apply]
      have h1 : emb n (prj n x) ≤ x := ih x
      calc emb n (toFn (prj (n + 1) f) (prj n x))
          = emb n (prj n (toFn f (emb n (prj n x)))) := by rw [prj_succ_apply]
        _ ≤ toFn f (emb n (prj n x)) := ih _
        _ ≤ toFn f x := (toFn f).monotone h1

/-- The projection of the least element is the least element. -/
theorem prj_botD (n : ℕ) : prj n (botD (n + 1)) = botD n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      refine toFn_ext ?_
      intro x
      rw [prj_succ_apply, toFn_botD, ih, toFn_botD]

/-- The composite `emb ∘ prj` is monotone and idempotent-like: it is below the identity. -/
theorem emb_prj_le_self (n : ℕ) (f : D (n + 1)) (x : D n) :
    toFn (emb n (prj n f)) x ≤ toFn f x := (toFn_le_iff.mp (emb_prj_le n f)) x

end

end ScottDinf
