/-
**Ghelli's divergence for full F<:** — task `M25-FSUB-UNDECIDABLE` (round 5, step F1), and the
first definitions of the reduction design (step F2).

The standard algorithmic subtyping procedure for full F<: works on goals `Γ ⊢ S <: T` and reduces
a goal to subgoals:

* `Γ ⊢ X <: T` (with `T ≠ X`, `T ≠ Top`) reduces to `Γ ⊢ Γ(X) <: T` (promotion of a variable to
  its bound);
* `Γ ⊢ ∀X<:S₁.S₂ <: ∀X<:T₁.T₂` reduces to the two subgoals `Γ ⊢ T₁ <: S₁` and
  `Γ, X<:T₁ ⊢ S₂ <: T₂` (the full, contravariant-bound rule).

Types are in de Bruijn form (`FsubGhelli.Ty`); the bound of the variable `i` in `Γ` is
`Γ[i]` lifted by `i + 1`.

* `FsubGhelli.AlgStep` — the goal-reduction step, as a relation from a goal to each of its
  subgoals;
* `FsubGhelli.ghelliGoal` — Ghelli's goal `α₀ <: ∀α₁<:Top. ¬(∀α₂<:α₁. ¬α₂) ⊢ α₀ <: ∀α₁<:α₀. ¬α₁`,
  where `¬S = ∀γ<:S. γ`;
* `FsubGhelli.cycle_step` — the goals `H k` (context `α<:α, …, α<:α, α₀<:T` with `k` extra
  entries, goal `T <: ∀α₁<:α₀'. ¬α₁`) satisfy `H k ⟶⁺ H (k+1)`;
* `FsubGhelli.ghelli_chain` — an infinite chain of goal reductions from Ghelli's goal;
* `FsubGhelli.ghelli_not_acc` — **the procedure does not terminate on Ghelli's goal**: the goal
  is not accessible for the subgoal relation.

For the reduction (F2), `FsubGhelli.CM` and `FsubGhelli.CM.Halts` define two-counter machines,
and `FsubGhelli.RowingFirstLemma` states the first lemma of the planned encoding (see
`docs/goal/evidence/M25-FSUB-UNDECIDABLE.md`).
-/

import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FsubGhelli

/-- Types of F<: in de Bruijn form. -/
inductive Ty where
  /-- The maximal type. -/
  | top : Ty
  /-- A type variable. -/
  | var : ℕ → Ty
  /-- Bounded quantification `∀X<:S. T` (the body binds index `0`). -/
  | all : Ty → Ty → Ty
  deriving DecidableEq

/-- Shift the variables at or above the cutoff `c` by `n`. -/
def Ty.lift (n c : ℕ) : Ty → Ty
  | .top => .top
  | .var i => if i < c then .var i else .var (i + n)
  | .all S T => .all (Ty.lift n c S) (Ty.lift n (c + 1) T)

/-- A subtyping goal `Γ ⊢ S <: T`; the head of the context is the innermost variable. -/
structure Goal where
  /-- The context of bounds. -/
  ctx : List Ty
  /-- The left-hand side. -/
  lhs : Ty
  /-- The right-hand side. -/
  rhs : Ty

/-- **One goal-reduction step of the algorithm for full F<:**, from a goal to one of its
subgoals. -/
inductive AlgStep : Goal → Goal → Prop
  /-- Promote a variable on the left to its bound. -/
  | promote {Γ : List Ty} {i : ℕ} {B T : Ty} : Γ[i]? = some B → T ≠ .var i → T ≠ .top →
      AlgStep ⟨Γ, .var i, T⟩ ⟨Γ, Ty.lift (i + 1) 0 B, T⟩
  /-- The bounds of two quantifiers, compared contravariantly. -/
  | allBound {Γ : List Ty} {S₁ S₂ T₁ T₂ : Ty} :
      AlgStep ⟨Γ, .all S₁ S₂, .all T₁ T₂⟩ ⟨Γ, T₁, S₁⟩
  /-- The bodies of two quantifiers, under the right-hand bound. -/
  | allBody {Γ : List Ty} {S₁ S₂ T₁ T₂ : Ty} :
      AlgStep ⟨Γ, .all S₁ S₂, .all T₁ T₂⟩ ⟨T₁ :: Γ, S₂, T₂⟩

/-- Negation `¬S = ∀γ<:S. γ`. -/
def neg (S : Ty) : Ty := .all S (.var 0)

/-- The bound of `α₀` in Ghelli's goal: `∀α₁<:Top. ¬(∀α₂<:α₁. ¬α₂)`. -/
def ghelliT : Ty := .all .top (neg (.all (.var 0) (neg (.var 0))))

/-- The right-hand side `∀α₁<:α. ¬α₁`, where `α` is the variable `0`. -/
def ghelliR : Ty := .all (.var 0) (neg (.var 0))

/-- **Ghelli's goal**: `α₀ <: ghelliT ⊢ α₀ <: ∀α₁<:α₀. ¬α₁`. -/
def ghelliGoal : Goal := ⟨[ghelliT], .var 0, ghelliR⟩

/-- The context with `k` entries `α<:α` (each bounded by the next variable) above `α₀<:T`. -/
def cycCtx (k : ℕ) : List Ty := List.replicate k (.var 0) ++ [ghelliT]

/-- The recurring goal `cycCtx k ⊢ ghelliT <: ghelliR`. -/
def H (k : ℕ) : Goal := ⟨cycCtx k, ghelliT, ghelliR⟩

theorem lift_ghelliT (n c : ℕ) : Ty.lift n c ghelliT = ghelliT := by
  simp [ghelliT, neg, Ty.lift]

theorem ghelliR_ne_var (i : ℕ) : ghelliR ≠ .var i := by simp [ghelliR]

theorem ghelliR_ne_top : ghelliR ≠ .top := by simp [ghelliR]

/-- In the context `var 0 :: cycCtx k`, promotion walks from `α_i` to `α_{k+1}` and then to
`ghelliT`. -/
theorem promote_walk (k : ℕ) : ∀ i, i ≤ k + 1 →
    Relation.TransGen AlgStep ⟨.var 0 :: cycCtx k, .var (k + 1 - i), ghelliR⟩
      ⟨.var 0 :: cycCtx k, ghelliT, ghelliR⟩ := by
  intro i
  induction i with
  | zero =>
      intro _
      refine Relation.TransGen.single ?_
      have h := AlgStep.promote (Γ := .var 0 :: cycCtx k) (i := k + 1) (B := ghelliT)
        (T := ghelliR) (by simp [cycCtx]) (ghelliR_ne_var _) ghelliR_ne_top
      simpa [lift_ghelliT] using h
  | succ i ih =>
      intro hi
      refine Relation.TransGen.head ?_ (ih (by omega))
      have hB : (Ty.var 0 :: cycCtx k)[k + 1 - (i + 1)]? = some (.var 0) := by
        rcases Nat.eq_zero_or_pos (k + 1 - (i + 1)) with h0 | hpos
        · rw [h0]; rfl
        · obtain ⟨j, hj⟩ : ∃ j, k + 1 - (i + 1) = j + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
          rw [hj, List.getElem?_cons_succ, cycCtx, List.getElem?_append_left (by simp; omega)]
          simp [List.getElem?_replicate]
          omega
      have h := AlgStep.promote (T := ghelliR) hB (ghelliR_ne_var _) ghelliR_ne_top
      have he : Ty.lift (k + 1 - (i + 1) + 1) 0 (.var 0) = .var (k + 1 - i) := by
        simp [Ty.lift]; omega
      rw [he] at h
      exact h

/-- **The cycle**: the recurring goal `H k` reduces in `k + 4` steps to `H (k + 1)`. -/
theorem cycle_step (k : ℕ) : Relation.TransGen AlgStep (H k) (H (k + 1)) := by
  have s1 : AlgStep (H k) ⟨.var 0 :: cycCtx k, neg (.all (.var 0) (neg (.var 0))), neg (.var 0)⟩ :=
    AlgStep.allBody
  have s2 : AlgStep ⟨.var 0 :: cycCtx k, neg (.all (.var 0) (neg (.var 0))), neg (.var 0)⟩
      ⟨.var 0 :: cycCtx k, .var 0, ghelliR⟩ := AlgStep.allBound
  have hw := promote_walk k (k + 1) le_rfl
  rw [Nat.sub_self] at hw
  have hctx : (Ty.var 0 :: cycCtx k) = cycCtx (k + 1) := by
    simp [cycCtx, List.replicate_succ]
  rw [hctx] at s1 s2 hw
  exact Relation.TransGen.head s1 (Relation.TransGen.head s2 hw)

/-- Ghelli's goal reduces to `H 0` by one promotion. -/
theorem ghelli_to_H0 : AlgStep ghelliGoal (H 0) := by
  have h := AlgStep.promote (Γ := [ghelliT]) (i := 0) (B := ghelliT) (T := ghelliR) rfl
    (ghelliR_ne_var 0) ghelliR_ne_top
  simpa [H, cycCtx, ghelliGoal, lift_ghelliT] using h

/-- **An infinite chain of goal reductions from Ghelli's goal.** -/
theorem ghelli_chain : ∃ f : ℕ → Goal, f 0 = ghelliGoal ∧
    ∀ n, Relation.TransGen AlgStep (f n) (f (n + 1)) :=
  ⟨fun n => match n with | 0 => ghelliGoal | k + 1 => H k, rfl, fun n => match n with
    | 0 => Relation.TransGen.single ghelli_to_H0
    | k + 1 => cycle_step k⟩

/-- **The algorithm for full F<: does not terminate on Ghelli's goal**: the goal is not
accessible for the subgoal relation (there is no well-founded measure on the search). -/
theorem ghelli_not_acc : ¬ Acc (fun g' g => AlgStep g g') ghelliGoal := by
  intro hacc
  have key : ∀ g, Acc (Relation.TransGen fun g' g => AlgStep g g') g → ∀ k, g ≠ H k := by
    intro g hg
    induction hg with
    | intro g _ ih =>
        intro k hk
        subst hk
        refine ih (H (k + 1)) ?_ (k + 1) rfl
        exact (Relation.transGen_swap).mpr (cycle_step k)
  exact key (H 0) (hacc.transGen.inv (Relation.TransGen.single ghelli_to_H0)) 0 rfl

/-! ### Two-counter machines (design step F2) -/

/-- Instructions of a two-counter machine: increment a counter and jump, or test a counter for
zero (jump to the first target if zero, else decrement and jump to the second). -/
inductive CMInstr where
  /-- `inc r; goto l`. -/
  | inc : Bool → ℕ → CMInstr
  /-- `if r = 0 then goto l₁ else (dec r; goto l₂)`. -/
  | test : Bool → ℕ → ℕ → CMInstr

/-- A two-counter machine: a program; a label outside the program halts. -/
abbrev CM := List CMInstr

/-- A configuration: label and the two counters. -/
structure CMConf where
  /-- The current label. -/
  pc : ℕ
  /-- The first counter. -/
  a : ℕ
  /-- The second counter. -/
  b : ℕ

/-- One step of a two-counter machine. -/
inductive CM.Step (M : CM) : CMConf → CMConf → Prop
  | incA {c : CMConf} {l : ℕ} : M[c.pc]? = some (.inc true l) → CM.Step M c ⟨l, c.a + 1, c.b⟩
  | incB {c : CMConf} {l : ℕ} : M[c.pc]? = some (.inc false l) → CM.Step M c ⟨l, c.a, c.b + 1⟩
  | zeroA {c : CMConf} {l₁ l₂ : ℕ} : M[c.pc]? = some (.test true l₁ l₂) → c.a = 0 →
      CM.Step M c ⟨l₁, c.a, c.b⟩
  | decA {c : CMConf} {l₁ l₂ : ℕ} {n : ℕ} : M[c.pc]? = some (.test true l₁ l₂) → c.a = n + 1 →
      CM.Step M c ⟨l₂, n, c.b⟩
  | zeroB {c : CMConf} {l₁ l₂ : ℕ} : M[c.pc]? = some (.test false l₁ l₂) → c.b = 0 →
      CM.Step M c ⟨l₁, c.a, c.b⟩
  | decB {c : CMConf} {l₁ l₂ : ℕ} {n : ℕ} : M[c.pc]? = some (.test false l₁ l₂) → c.b = n + 1 →
      CM.Step M c ⟨l₂, c.a, n⟩

/-- The machine halts from `(0, a, b)`: it reaches a label outside the program. -/
def CM.Halts (M : CM) (a b : ℕ) : Prop :=
  ∃ c, Relation.ReflTransGen (CM.Step M) ⟨0, a, b⟩ c ∧ M.length ≤ c.pc

/-- Subtyping in full F<: as the inductive closure of the algorithm (a goal holds when it is an
axiom — reflexivity of a variable or `Top` on the right — or all its subgoals hold). -/
inductive Sub : Goal → Prop
  | top {Γ : List Ty} {S : Ty} : Sub ⟨Γ, S, .top⟩
  | refl {Γ : List Ty} {i : ℕ} : Sub ⟨Γ, .var i, .var i⟩
  | promote {Γ : List Ty} {i : ℕ} {B T : Ty} : Γ[i]? = some B → T ≠ .var i → T ≠ .top →
      Sub ⟨Γ, Ty.lift (i + 1) 0 B, T⟩ → Sub ⟨Γ, .var i, T⟩
  | all {Γ : List Ty} {S₁ S₂ T₁ T₂ : Ty} : Sub ⟨Γ, T₁, S₁⟩ → Sub ⟨T₁ :: Γ, S₂, T₂⟩ →
      Sub ⟨Γ, .all S₁ S₂, .all T₁ T₂⟩

/-- **The first lemma of the planned reduction** (stated, not proved): there is an encoding of
two-counter machines and initial counters as F<: subtyping goals (Pierce's rowing-machine
encoding through F<:^D) such that a machine halts exactly when the encoded goal is derivable. -/
def RowingFirstLemma : Prop :=
  ∃ enc : CM → ℕ → ℕ → Goal, ∀ M a b, CM.Halts M a b ↔ Sub (enc M a b)

end FsubGhelli
