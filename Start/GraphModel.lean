/-
Scott's graph model of the untyped lambda calculus: the reflexive object.

This file builds the domain `GraphModel.D = Set Tok` of Scott's graph model (the model
`P(ω)` of "Data types as lattices", in the token / Engeler presentation) and proves that the
*Scott-continuous function space* `[D → D]` is a **retract** of `D` itself:

* `GraphModel.graph`   — the map `[D → D] → D` sending a function to its graph;
* `GraphModel.appD`    — application, so `appD X : D → D` is the map `D → [D → D]`;
* `GraphModel.appD_graph` — `appD (graph f) = f` for every Scott-continuous `f`;
* `GraphModel.scottContinuous_appD` — `appD X` is Scott continuous for every `X`.

Together these say that `D` is a **reflexive object**: the continuous function space embeds
into the domain as a retract, which is exactly what is needed to interpret the untyped lambda
calculus (done in `Start/GraphModelSemantics.lean`).

The technical work is the equivalence `GraphModel.cont_iff_scottContinuous` between Mathlib's
`ScottContinuous` (preservation of least upper bounds of directed sets) and the concrete
"finite approximation" form `GraphModel.Cont`, which is what the graph construction consumes.

Boundary: this is the *graph* model, not Scott's `D∞` inverse limit; the retraction
`appD ∘ graph = id` holds, but `graph ∘ appD` is not the identity (the model is not
extensional).
-/

import Mathlib.Tactic
import Mathlib.Order.ScottContinuity
import Mathlib.Data.Set.Lattice

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GraphModel

/-- Tokens: the "finite pieces of information" of the graph model.  A token is either an
atom, or a step function `a ⇒ b` from a finite set of tokens `a` to a token `b`. -/
inductive Tok : Type
  | atom : ℕ → Tok
  | arrow : List Tok → Tok → Tok

/-- The domain of the graph model: sets of tokens, ordered by inclusion. -/
abbrev D : Type := Set Tok

/-- The set of tokens occurring in a list (a *finite* element of `D`). -/
def lset (a : List Tok) : D := {x | x ∈ a}

@[simp] theorem mem_lset {x : Tok} {a : List Tok} : x ∈ lset a ↔ x ∈ a := Iff.rfl

@[simp] theorem lset_nil : lset [] = (∅ : D) := by
  ext x; simp [lset]

theorem lset_append (a b : List Tok) : lset (a ++ b) = lset a ∪ lset b := by
  ext x; simp [lset]

/-- Application in the graph model: `appD X Y` collects the outputs of the step functions
in `X` whose input requirement is met by `Y`. -/
def appD (X Y : D) : D := {b | ∃ a : List Tok, lset a ⊆ Y ∧ Tok.arrow a b ∈ X}

/-- The graph of a function: all step functions `a ⇒ b` with `b ∈ f a`. -/
def graph (f : D → D) : D := {t | ∃ a b, t = Tok.arrow a b ∧ b ∈ f (lset a)}

@[simp] theorem mem_graph {f : D → D} {a : List Tok} {b : Tok} :
    Tok.arrow a b ∈ graph f ↔ b ∈ f (lset a) := by
  constructor
  · rintro ⟨a', b', h, hb⟩
    cases h
    exact hb
  · intro hb; exact ⟨a, b, rfl, hb⟩

@[simp] theorem atom_notMem_graph {f : D → D} {n : ℕ} : Tok.atom n ∉ graph f := by
  rintro ⟨a, b, h, -⟩
  cases h

/-- Concrete ("finite approximation") continuity: a value is produced from an input only if
it is already produced from some finite part of it. -/
def Cont (f : D → D) : Prop :=
  ∀ (Y : D) (b : Tok), b ∈ f Y ↔ ∃ a : List Tok, lset a ⊆ Y ∧ b ∈ f (lset a)

theorem Cont.mono {f : D → D} (hf : Cont f) : Monotone f := by
  intro Y Y' hYY' b hb
  obtain ⟨a, ha, hb'⟩ := (hf Y b).1 hb
  exact (hf Y' b).2 ⟨a, ha.trans hYY', hb'⟩

/-- The β-rule of the model: applying the graph of a continuous function is applying the
function. -/
theorem appD_graph_apply {f : D → D} (hf : Cont f) (Y : D) : appD (graph f) Y = f Y := by
  ext b
  constructor
  · rintro ⟨a, ha, hb⟩
    exact (hf Y b).2 ⟨a, ha, mem_graph.1 hb⟩
  · intro hb
    obtain ⟨a, ha, hb'⟩ := (hf Y b).1 hb
    exact ⟨a, ha, mem_graph.2 hb'⟩

/-- Application is continuous in its second argument. -/
theorem cont_appD (X : D) : Cont (appD X) := by
  intro Y b
  constructor
  · rintro ⟨a, ha, hb⟩
    exact ⟨a, ha, ⟨a, le_refl _, hb⟩⟩
  · rintro ⟨a, ha, a', ha', hb⟩
    exact ⟨a', ha'.trans ha, hb⟩

/-- A finite set of tokens contained in the union of a directed family already sits inside
one member of the family. -/
theorem exists_mem_of_lset_subset_sUnion {d : Set D} (hne : d.Nonempty)
    (hdir : DirectedOn (· ≤ ·) d) :
    ∀ (a : List Tok), lset a ⊆ ⋃₀ d → ∃ Z ∈ d, lset a ⊆ Z := by
  intro a
  induction a with
  | nil =>
      intro _
      obtain ⟨Z, hZ⟩ := hne
      exact ⟨Z, hZ, by simp⟩
  | cons x a ih =>
      intro hsub
      have hx : x ∈ ⋃₀ d := hsub (by simp [lset])
      obtain ⟨Zx, hZx, hxZ⟩ := hx
      have hsub' : lset a ⊆ ⋃₀ d := by
        intro y hy
        exact hsub (by simp only [mem_lset, List.mem_cons]; exact Or.inr hy)
      obtain ⟨Z, hZ, hZa⟩ := ih hsub'
      obtain ⟨W, hW, hZW, hZxW⟩ := hdir Z hZ Zx hZx
      refine ⟨W, hW, ?_⟩
      intro y hy
      simp only [mem_lset, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hZxW hxZ
      · exact hZW (hZa hy)

theorem cont_of_scottContinuous {f : D → D} (hf : ScottContinuous f) : Cont f := by
  intro Y b
  constructor
  · intro hb
    set d : Set D := {Z : D | ∃ a : List Tok, Z = lset a ∧ lset a ⊆ Y} with hd
    have hne : d.Nonempty := ⟨lset [], ⟨[], rfl, by simp⟩⟩
    have hdir : DirectedOn (· ≤ ·) d := by
      rintro _ ⟨a, rfl, ha⟩ _ ⟨a', rfl, ha'⟩
      refine ⟨lset (a ++ a'), ⟨a ++ a', rfl, ?_⟩, ?_, ?_⟩
      · rw [lset_append]; exact Set.union_subset ha ha'
      · rw [lset_append]; exact Set.subset_union_left
      · rw [lset_append]; exact Set.subset_union_right
    have hlub : IsLUB d Y := by
      constructor
      · rintro _ ⟨a, rfl, ha⟩; exact ha
      · intro u hu y hy
        exact hu ⟨[y], rfl, by simpa [lset] using hy⟩ (by simp [lset])
    have := hf hne hdir hlub
    have hb' : b ∈ ⋃₀ (f '' d) := by
      have : f Y ≤ ⋃₀ (f '' d) := by
        refine this.2 ?_
        rintro _ ⟨Z, hZ, rfl⟩
        exact fun y hy => ⟨f Z, ⟨Z, hZ, rfl⟩, hy⟩
      exact this hb
    obtain ⟨S, ⟨Z, ⟨a, rfl, ha⟩, rfl⟩, hbS⟩ := hb'
    exact ⟨a, ha, hbS⟩
  · rintro ⟨a, ha, hb⟩
    exact hf.monotone ha hb

theorem scottContinuous_of_cont {f : D → D} (hf : Cont f) : ScottContinuous f := by
  intro d hne hdir Y hlub
  have hYU : Y = ⋃₀ d := by
    have h1 : IsLUB d (⋃₀ d) := by
      constructor
      · intro Z hZ y hy; exact ⟨Z, hZ, hy⟩
      · rintro u hu y ⟨Z, hZ, hy⟩; exact hu hZ hy
    exact hlub.unique h1
  subst hYU
  constructor
  · rintro _ ⟨Z, hZ, rfl⟩
    exact hf.mono (fun y hy => ⟨Z, hZ, hy⟩)
  · intro u hu b hb
    obtain ⟨a, ha, hb'⟩ := (hf _ b).1 hb
    obtain ⟨Z, hZ, haZ⟩ := exists_mem_of_lset_subset_sUnion hne hdir a ha
    exact hu ⟨Z, hZ, rfl⟩ (hf.mono haZ hb')

/-- Mathlib's Scott continuity and the finite-approximation form agree on this domain. -/
theorem cont_iff_scottContinuous {f : D → D} : Cont f ↔ ScottContinuous f :=
  ⟨scottContinuous_of_cont, cont_of_scottContinuous⟩

/-- Application is Scott continuous in its second argument. -/
theorem scottContinuous_appD (X : D) : ScottContinuous (appD X) :=
  scottContinuous_of_cont (cont_appD X)

/-- **The retraction.** For a Scott-continuous `f`, applying its graph recovers `f`; hence the
continuous function space `[D → D]` is a retract of `D`, i.e. `D` is a reflexive object. -/
theorem appD_graph {f : D → D} (hf : ScottContinuous f) : appD (graph f) = f := by
  funext Y
  exact appD_graph_apply (cont_of_scottContinuous hf) Y

/-- The other composite is *not* the identity: the graph model is not extensional. -/
theorem graph_appD_ne : ∃ X : D, graph (appD X) ≠ X := by
  refine ⟨{Tok.atom 0}, ?_⟩
  intro h
  have : Tok.atom 0 ∈ graph (appD ({Tok.atom 0} : D)) := by rw [h]; rfl
  exact atom_notMem_graph this

/-- Monotonicity of `graph` in the function argument. -/
theorem graph_mono {f g : D → D} (h : ∀ X, f X ⊆ g X) : graph f ⊆ graph g := by
  rintro _ ⟨a, b, rfl, hb⟩
  exact ⟨a, b, rfl, h _ hb⟩

theorem graph_congr {f g : D → D} (h : ∀ X, f X = g X) : graph f = graph g := by
  apply Set.Subset.antisymm
  · exact graph_mono fun X => (h X).le
  · exact graph_mono fun X => (h X).ge

/-- Monotonicity of application in both arguments. -/
theorem appD_mono {X X' Y Y' : D} (hX : X ⊆ X') (hY : Y ⊆ Y') : appD X Y ⊆ appD X' Y' := by
  rintro b ⟨a, ha, hb⟩
  exact ⟨a, ha.trans hY, hX hb⟩

end GraphModel
