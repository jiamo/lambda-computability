/-
The filter model of the intersection type system, and the identification

    "`M` is typable"   =   "`⟦M⟧` is not the least element"   =   "`M` has a head normal form".

The type assignment system of `Start/IntersectionTypes.lean` is set up so that its strict types
are the tokens of Scott's graph model.  The main theorem of this file,
`Inter.deriv_iff_mem_denot`, says that this coincidence is exact: a strict type `σ` is
assignable to `M` in the basis `Γ` **iff** the token `σ` belongs to the denotation of `M` in the
environment determined by `Γ`.  The set of types of a term therefore *is* its denotation, so the
graph model is the filter model of the system, and the two presentations — syntactic type
assignment and denotational semantics — carry exactly the same information.

Everything else follows by combining that theorem with the results already proved about the
graph model:

* `Inter.deriv_reduces`, `Inter.deriv_expansion`, `Inter.deriv_conv` — **subject reduction and
  subject expansion**: the set of types of a term is invariant under β-conversion (the model is
  sound for β);
* `Inter.typable_iff_hasHnf` — **typability is head normalisation**;
* `Inter.typable_iff_solvable` — and, for closed terms, solvability;
* `Inter.not_typable_omega`, `Inter.typable_I` — the theory is not degenerate in either
  direction;
* `Inter.typeSet_eq_denot`, `Inter.typeSet_directed`, `Inter.mem_typeSet_iff` — the filter
  presentation: the types of `M` form a subset of the token preorder closed under the finite
  intersections of the system, and it is the model value of `M`.

The proof of `deriv_iff_mem_denot` is a plain induction on the term: the three typing rules are
literally the three clauses of `GraphModel.denot`, once the empty intersection is read as `ω`.
-/

import Start.IntersectionTypes
import Start.GraphAdequacy
import Start.HnfSolvable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Inter

open GraphModel

/-- The environment of the graph model determined by a basis. -/
def basisEnv (Γ : Basis) : Env := GraphModel.approx Γ

@[simp] theorem basisEnv_apply (Γ : Basis) (i : ℕ) : basisEnv Γ i = lset (Γ i) := rfl

theorem basisEnv_push (a : Ty) (Γ : Basis) :
    basisEnv (push a Γ) = cons (lset a) (basisEnv Γ) := by
  funext i
  cases i with
  | zero => rfl
  | succ j => rfl

/-! ### The types of a term are its denotation -/

/-- **Type assignment is denotation.**  A strict type `σ` can be assigned to `M` in the basis `Γ`
exactly when the token `σ` lies in the interpretation of `M` in the graph model, in the
environment given by `Γ`.  So the graph model is the filter model of the intersection type
system. -/
theorem deriv_iff_mem_denot (Γ : Basis) (M : Lambda) (σ : Sty) :
    Deriv Γ M σ ↔ σ ∈ denot M (basisEnv Γ) := by
  induction M generalizing Γ σ with
  | var i => simp [deriv_var_iff, lset]
  | app P Q ihP ihQ =>
      rw [deriv_app_iff, denot_app]
      constructor
      · rintro ⟨a, hP, hQ⟩
        refine ⟨a, ?_, (ihP Γ _).1 hP⟩
        intro τ hτ
        exact (ihQ Γ τ).1 (hQ τ hτ)
      · rintro ⟨a, ha, hP⟩
        refine ⟨a, (ihP Γ _).2 hP, ?_⟩
        intro τ hτ
        exact (ihQ Γ τ).2 (ha hτ)
  | lam P ih =>
      rw [denot_lam]
      constructor
      · intro h
        obtain ⟨a, τ, rfl, hP⟩ := deriv_lam_iff.1 h
        refine mem_graph.2 ?_
        rw [← basisEnv_push]
        exact (ih (push a Γ) τ).1 hP
      · intro h
        cases σ with
        | atom n => exact absurd h atom_notMem_graph
        | arrow a τ =>
            refine Deriv.lam ((ih (push a Γ) τ).2 ?_)
            rw [basisEnv_push]
            exact mem_graph.1 h

/-- The set of strict types assignable to `M` in the basis `Γ`. -/
def typeSet (Γ : Basis) (M : Lambda) : Set Sty := {σ | Deriv Γ M σ}

/-- **The filter of a term is its value in the model.** -/
theorem typeSet_eq_denot (Γ : Basis) (M : Lambda) : typeSet Γ M = denot M (basisEnv Γ) := by
  ext σ
  exact deriv_iff_mem_denot Γ M σ

theorem mem_typeSet_iff {Γ : Basis} {M : Lambda} {σ : Sty} :
    σ ∈ typeSet Γ M ↔ Deriv Γ M σ := Iff.rfl

/-! ### Subject reduction and subject expansion -/

/-- **Subject reduction.** -/
theorem deriv_reduces {Γ : Basis} {M N : Lambda} {σ : Sty}
    (hr : Lambda.reduces M N) (h : Deriv Γ M σ) : Deriv Γ N σ := by
  rw [deriv_iff_mem_denot] at h ⊢
  rwa [← denot_reduces hr]

/-- **Subject expansion**: unlike simple types, intersection types are also preserved
*backwards* along a reduction. -/
theorem deriv_expansion {Γ : Basis} {M N : Lambda} {σ : Sty}
    (hr : Lambda.reduces M N) (h : Deriv Γ N σ) : Deriv Γ M σ := by
  rw [deriv_iff_mem_denot] at h ⊢
  rwa [denot_reduces hr]

/-- The set of types is a β-conversion invariant. -/
theorem deriv_conv {Γ : Basis} {M N : Lambda} {σ : Sty}
    (h : Lambda.Conv M N) : Deriv Γ M σ ↔ Deriv Γ N σ := by
  rw [deriv_iff_mem_denot, deriv_iff_mem_denot, denot_conv h]

theorem typeSet_conv {Γ : Basis} {M N : Lambda} (h : Lambda.Conv M N) :
    typeSet Γ M = typeSet Γ N := by
  ext σ
  exact deriv_conv h

/-! ### Typability is head normalisation -/

/-- One half of the characterisation: a typable term has a head normal form.  This is where the
computability argument for the graph model is used. -/
theorem hasHnf_of_typable {M : Lambda} (h : Typable M) : Lambda.HasHnf M := by
  obtain ⟨Γ, σ, hd⟩ := h
  exact hasHnf_of_mem_denot ((deriv_iff_mem_denot Γ M σ).1 hd)

/-- The other half: a term with a head normal form is typable.  The finite basis is extracted
from the continuity of the interpretation. -/
theorem typable_of_hasHnf {M : Lambda} (h : Lambda.HasHnf M) : Typable M := by
  obtain ⟨ρ, hρ⟩ := exists_denot_ne_empty_of_hasHnf h
  obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hρ
  obtain ⟨Γ, -, hΓ⟩ := denot_fin M ρ b hb
  exact ⟨Γ, b, (deriv_iff_mem_denot Γ M b).2 hΓ⟩

/-- **Typability is head normalisation.**  A term of the untyped calculus can be assigned a type
in the intersection type system exactly when it has a head normal form — equivalently, exactly
when its denotation is not the least element of the model. -/
theorem typable_iff_hasHnf (M : Lambda) : Typable M ↔ Lambda.HasHnf M :=
  ⟨hasHnf_of_typable, typable_of_hasHnf⟩

/-- Typability is a semantic condition: the denotation is nonempty. -/
theorem typable_iff_exists_denot_ne_empty (M : Lambda) :
    Typable M ↔ ∃ ρ : Env, denot M ρ ≠ (∅ : D) := by
  rw [typable_iff_hasHnf]
  exact ⟨exists_denot_ne_empty_of_hasHnf, fun ⟨_, h⟩ => hasHnf_of_denot_ne_empty h⟩

/-- For a *closed* term the denotation does not depend on the environment, so typability is
non-triviality of the denotation in any single environment. -/
theorem typable_iff_denot_ne_empty {M : Lambda} (hcl : Lambda.IsClosed M) (ρ : Env) :
    Typable M ↔ denot M ρ ≠ (∅ : D) := by
  rw [typable_iff_hasHnf]
  exact (denot_ne_empty_iff_hasHnf hcl ρ).symm

/-- **Typability is solvability**, for closed terms. -/
theorem typable_iff_solvable {M : Lambda} (hcl : Lambda.IsClosed M) :
    Typable M ↔ Lambda.Solvable M := by
  rw [typable_iff_hasHnf]
  exact (Lambda.solvable_iff_hasHnf hcl).symm

/-! ### The system is not degenerate -/

/-- `Ω` has no type: the empty intersection `ω` is the only type of an unsolvable term, and it is
not a strict type. -/
theorem not_typable_omega : ¬ Typable Lambda.omega := by
  intro h
  exact not_hasHnf_omega (hasHnf_of_typable h)

theorem typable_I : Typable Lambda.I :=
  typable_of_hasHnf (Lambda.hasHnf_of_isHnf Lambda.isHnf_I)

/-- The type `[σ] → σ` of the identity, for every `σ`. -/
theorem deriv_I (Γ : Basis) (σ : Sty) : Deriv Γ Lambda.I (Tok.arrow [σ] σ) :=
  Deriv.lam (Deriv.var (by simp [push]))

end Inter
