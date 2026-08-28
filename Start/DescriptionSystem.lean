/-
Description systems: the common shape of every complexity measure in the library.

Each of the Kolmogorov-style measures of this development — plain complexity `Lambda.kolm`,
complexity relative to an interpreter `Lambda.kolmWith`, conditional complexity
`Lambda.kolmCond`, prefix complexity `Lambda.kolmP`, the prefix complexity `KCMachine.KU` of the
universal prefix machine, the locally nameless complexity `Lambda.kolmLN`, and the time-bounded
Levin complexity `Lambda.kt` — is the same construction applied to different data: a type of
*programs*, a *size* on programs, and an *output relation* saying which objects a program
describes.  This module isolates that construction.

* `Complexity.DescSystem P α` — a description system: `size : P → ℕ` and `Outputs : P → α → Prop`;
* `Complexity.DescSystem.K` — its complexity function, `K x = inf {|p| : p describes x}`;
* `Complexity.DescSystem.K_le_of_outputs`, `exists_outputs_size_eq_K` — the two facts that make
  `K` a minimum;
* `Complexity.DescSystem.Translation` — a size-increasing-by-a-constant simulation of one system
  by another, and `K_le_add_cost`, the resulting **invariance/optimality estimate**;
* `Complexity.DescSystem.Optimal` — being no worse than another system up to an additive
  constant, `Optimal_of_translation`, and its transitivity;
* `Complexity.DescSystem.K_le_add_of_combine` — the generic **subadditivity** estimate, from a
  way of combining two programs into one.

The instances live in `Start/KolmogorovMachines.lean`, except for the two whose definitions come
later in the import order: `Lambda.kolmPSystem` (`Start/ChaitinOmega.lean`) and
`Lambda.kolmLNSystem` (`Start/KolmogorovRepresentation.lean`).
-/

import Mathlib.Order.Lattice.Nat

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

namespace Complexity

/-- A **description system**: a type `P` of programs with a size, and a relation saying which
objects of `α` a program describes.  No computability is assumed; the relation may be arbitrary,
and a program may describe several objects. -/
structure DescSystem (P : Type u) (α : Type v) where
  /-- The length of a program. -/
  size : P → ℕ
  /-- `Outputs p x` : the program `p` describes the object `x`. -/
  Outputs : P → α → Prop

namespace DescSystem

variable {P : Type u} {Q : Type v} {R : Type w} {α β γ : Type*}

/-- `x` has at least one description. -/
def Describes (M : DescSystem P α) (x : α) : Prop := ∃ p : P, M.Outputs p x

/-- The **complexity** of `x` in the system `M`: the least size of a program describing it (and
`0` if there is none). -/
noncomputable def K (M : DescSystem P α) (x : α) : ℕ :=
  sInf {n | ∃ p : P, M.Outputs p x ∧ M.size p = n}

theorem K_le_of_outputs {M : DescSystem P α} {p : P} {x : α} (h : M.Outputs p x) :
    M.K x ≤ M.size p :=
  Nat.sInf_le ⟨p, h, rfl⟩

/-- The infimum is attained as soon as `x` is described at all. -/
theorem exists_outputs_size_eq_K {M : DescSystem P α} {x : α} (h : M.Describes x) :
    ∃ p : P, M.Outputs p x ∧ M.size p = M.K x := by
  obtain ⟨p, hp⟩ := h
  exact Nat.sInf_mem (s := {n | ∃ p : P, M.Outputs p x ∧ M.size p = n}) ⟨M.size p, p, hp, rfl⟩

/-- Undescribable objects get complexity `0`, the value of `sInf ∅`. -/
theorem K_eq_zero_of_not_describes {M : DescSystem P α} {x : α} (h : ¬ M.Describes x) :
    M.K x = 0 := by
  have : {n | ∃ p : P, M.Outputs p x ∧ M.size p = n} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p, hp, -⟩
    exact h ⟨p, hp⟩
  simp [K, this]

/-- A **translation** of the system `M` into the system `N`: a map on programs that preserves the
output relation and increases the size by at most the constant `cost`. -/
structure Translation (M : DescSystem P α) (N : DescSystem Q α) where
  /-- How a program of `M` is turned into a program of `N`. -/
  map : P → Q
  /-- The constant overhead. -/
  cost : ℕ
  /-- The translation preserves descriptions. -/
  outputs : ∀ {p : P} {x : α}, M.Outputs p x → N.Outputs (map p) x
  /-- The translation costs at most `cost` extra symbols. -/
  size_le : ∀ p : P, N.size (map p) ≤ M.size p + cost

/-- **Invariance.**  A translation of `M` into `N` makes `N` at least as economical as `M`, up to
the additive constant `cost`. -/
theorem K_le_add_cost {M : DescSystem P α} {N : DescSystem Q α} (T : Translation M N) {x : α}
    (hx : M.Describes x) : N.K x ≤ M.K x + T.cost := by
  obtain ⟨p, hp, hsize⟩ := exists_outputs_size_eq_K hx
  calc N.K x ≤ N.size (T.map p) := K_le_of_outputs (T.outputs hp)
    _ ≤ M.size p + T.cost := T.size_le p
    _ = M.K x + T.cost := by rw [hsize]

/-- `N` is at least as economical as `M`, up to an additive constant. -/
def Optimal (N : DescSystem Q α) (M : DescSystem P α) : Prop :=
  ∃ c : ℕ, ∀ x : α, M.Describes x → N.K x ≤ M.K x + c

theorem optimal_of_translation {M : DescSystem P α} {N : DescSystem Q α}
    (T : Translation M N) : Optimal N M :=
  ⟨T.cost, fun _ hx => K_le_add_cost T hx⟩

theorem optimal_refl (M : DescSystem P α) : Optimal M M := ⟨0, fun _ _ => by omega⟩

/-- Being optimal is transitive, provided the intermediate system describes what the first one
describes. -/
theorem optimal_trans {M : DescSystem P α} {N : DescSystem Q α} {L : DescSystem R α}
    (h₁ : Optimal N M) (h₂ : Optimal L N) (hd : ∀ x : α, M.Describes x → N.Describes x) :
    Optimal L M := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨c₁ + c₂, fun x hx => ?_⟩
  have h1 := hc₁ x hx
  have h2 := hc₂ x (hd x hx)
  omega

/-- **Subadditivity.**  A way of combining a description of `x` and a description of `y` into a
description of `f x y`, at an extra cost `c`, bounds the complexity of `f x y`. -/
theorem K_le_add_of_combine {M : DescSystem P α} {N : DescSystem Q β} {L : DescSystem R γ}
    {f : α → β → γ} (comb : P → Q → R) (c : ℕ)
    (houts : ∀ {p : P} {q : Q} {x : α} {y : β},
      M.Outputs p x → N.Outputs q y → L.Outputs (comb p q) (f x y))
    (hsize : ∀ (p : P) (q : Q), L.size (comb p q) ≤ M.size p + N.size q + c)
    {x : α} {y : β} (hx : M.Describes x) (hy : N.Describes y) :
    L.K (f x y) ≤ M.K x + N.K y + c := by
  obtain ⟨p, hp, hps⟩ := exists_outputs_size_eq_K hx
  obtain ⟨q, hq, hqs⟩ := exists_outputs_size_eq_K hy
  calc L.K (f x y) ≤ L.size (comb p q) := K_le_of_outputs (houts hp hq)
    _ ≤ M.size p + N.size q + c := hsize p q
    _ = M.K x + N.K y + c := by rw [hps, hqs]

/-- The unary version: a description of `x` turned into a description of `f x`. -/
theorem K_le_add_of_apply {M : DescSystem P α} {N : DescSystem Q β} {f : α → β}
    (app : P → Q) (c : ℕ)
    (houts : ∀ {p : P} {x : α}, M.Outputs p x → N.Outputs (app p) (f x))
    (hsize : ∀ p : P, N.size (app p) ≤ M.size p + c)
    {x : α} (hx : M.Describes x) : N.K (f x) ≤ M.K x + c := by
  obtain ⟨p, hp, hps⟩ := exists_outputs_size_eq_K hx
  calc N.K (f x) ≤ N.size (app p) := K_le_of_outputs (houts hp)
    _ ≤ M.size p + c := hsize p
    _ = M.K x + c := by rw [hps]

end DescSystem

end Complexity
