/-
The three models of the untyped λ-calculus as instances of one definition.

`Start/LambdaModel.lean` defines what a λ-model is and derives, from the four axioms alone, the
lifting and substitution lemmas, soundness for β, the combinatory structure and the Meyer–Scott
axioms.  This file exhibits the models the library has built as instances, so the three separate
developments become three instances of one theorem:

* `GraphModel.model` — Scott's graph model `𝒫ω`;
* `ScottDinf.model` — Scott's inverse limit `D∞`;
* `Inter.filterModel`, `Inter.typeSet_eq_model_interp` — the filter model of the intersection
  type system: the filter of types of a term *is* its value in the graph λ-model.

Consequences, all now obtained from the abstract theory:

* `GraphModel.model_not_extensional` — the graph model is not extensional;
* `ScottDinf.model_extensional`, `ScottDinf.model_interp_eta` — `D∞` is extensional, hence
  validates η;
* `Lambda.LambdaModel.theory` — **every λ-model determines a λ-theory**, and
  `GraphModel.theory_model_eq`, `ScottDinf.theory_model_eq` identify the theories of the two
  models with the entries `Th(𝒫ω)` and `Th(D∞)` of the lattice of λ-theories in
  `Start/LambdaTheory.lean`.  The classical chain `B ⊊ Th(𝒫ω) ⊊ Th(D∞) = H*` is therefore a
  statement about theories of λ-models.
-/

import Start.LambdaModel
import Start.LambdaTheory
import Start.ScottDinfOmega
import Start.FilterModel

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

namespace LambdaModel

variable (M : LambdaModel)

/-- The interpretation is a congruence for one-hole contexts. -/
theorem interp_fill_congr {s t : Lambda} (h : ∀ ρ : ℕ → M.Carrier, M.interp s ρ = M.interp t ρ)
    (C : Ctx) : ∀ ρ : ℕ → M.Carrier, M.interp (C.fill s) ρ = M.interp (C.fill t) ρ := by
  induction C with
  | hole => exact h
  | appL C u ih => intro ρ; simp only [Ctx.fill, M.interp_app, ih ρ]
  | appR u C ih => intro ρ; simp only [Ctx.fill, M.interp_app, ih ρ]
  | lam C ih =>
      intro ρ
      exact M.interp_lam_ext _ _ _ _ fun d => ih (modelCons d ρ)

/-- **The theory of a λ-model**: the equations between untyped terms that it validates.  This is
a λ-theory in the sense of `Start/LambdaTheory.lean`. -/
def theory : LambdaTheory where
  Rel s t := ∀ ρ : ℕ → M.Carrier, M.interp s ρ = M.interp t ρ
  conv h := fun ρ => interp_conv M h ρ
  symm h := fun ρ => (h ρ).symm
  trans h₁ h₂ := fun ρ => (h₁ ρ).trans (h₂ ρ)
  congr C h := interp_fill_congr M h C

@[simp] theorem theory_rel (s t : Lambda) :
    (theory M).Rel s t ↔ ∀ ρ : ℕ → M.Carrier, M.interp s ρ = M.interp t ρ := Iff.rfl

end LambdaModel

end Lambda

open Lambda

/-! ### Scott's graph model -/

namespace GraphModel

theorem cons_eq_modelCons (X : D) (ρ : Env) : cons X ρ = modelCons X ρ := by
  funext i
  cases i <;> rfl

/-- **Scott's graph model is a λ-model.** -/
def model : LambdaModel where
  Carrier := D
  app := appD
  nonempty := ⟨∅⟩
  interp := denot
  interp_var := fun _ _ => rfl
  interp_app := fun _ _ _ => rfl
  interp_beta := by
    intro t ρ d
    rw [denot_lam, appD_graph_apply (cont_denot_cons t ρ), cons_eq_modelCons]
  interp_lam_ext := by
    intro t t' ρ ρ' h
    rw [denot_lam, denot_lam]
    exact graph_congr fun X => by rw [cons_eq_modelCons, cons_eq_modelCons]; exact h X

@[simp] theorem model_carrier : model.Carrier = D := rfl
@[simp] theorem model_app (X Y : D) : model.app X Y = appD X Y := rfl
@[simp] theorem model_interp (t : Lambda) (ρ : Env) : model.interp t ρ = denot t ρ := rfl

/-- The graph model is **not** extensional: distinct elements can have the same applicative
behaviour, since an atom is applicatively invisible. -/
theorem model_not_extensional : ¬ model.IsExtensional := by
  intro h
  have hz : ∀ Z : D, appD ({Tok.atom 0} : D) Z = appD (∅ : D) Z := by
    intro Z
    ext b
    constructor
    · rintro ⟨a, -, hb⟩
      exact absurd hb (by simp)
    · rintro ⟨a, -, hb⟩
      exact absurd hb (by simp)
  have := h ({Tok.atom 0} : D) (∅ : D) hz
  have hmem : Tok.atom 0 ∈ ({Tok.atom 0} : D) := rfl
  rw [this] at hmem
  exact hmem

/-- The theory of the graph model, as a λ-model, is the entry `Th(𝒫ω)` of the lattice of
λ-theories. -/
theorem theory_model_eq : LambdaModel.theory model = Lambda.LambdaTheory.graph := rfl

end GraphModel

/-! ### Scott's `D∞` -/

namespace ScottDinf

theorem dcons_eq_modelCons (X : Dinf) (ρ : DEnv) : dcons X ρ = modelCons X ρ := by
  funext i
  cases i <;> rfl

/-- **Scott's inverse limit `D∞` is a λ-model.** -/
def model : LambdaModel where
  Carrier := Dinf
  app := fun x y => Phi x y
  nonempty := ⟨Dinf.botDinf⟩
  interp := ddenot
  interp_var := fun _ _ => rfl
  interp_app := fun _ _ _ => rfl
  interp_beta := by
    intro t ρ d
    rw [ddenot_lam_apply, dcons_eq_modelCons]
  interp_lam_ext := by
    intro t t' ρ ρ' h
    rw [ddenot_lam, ddenot_lam]
    refine dlamAny_congr fun X => ?_
    rw [dcons_eq_modelCons, dcons_eq_modelCons]
    exact h X

@[simp] theorem model_carrier : model.Carrier = Dinf := rfl
@[simp] theorem model_app (x y : Dinf) : model.app x y = Phi x y := rfl
@[simp] theorem model_interp (t : Lambda) (ρ : DEnv) : model.interp t ρ = ddenot t ρ := rfl

/-- **`D∞` is extensional**: it is the inverse limit of the function spaces, so an element is
determined by the function it induces. -/
theorem model_extensional : model.IsExtensional := by
  intro x y h
  have hxy : Phi x = Phi y := by
    refine DFunLike.ext _ _ ?_
    intro z
    exact h z
  rw [← Psi_Phi x, ← Psi_Phi y, hxy]

/-- Hence `D∞` validates η. -/
theorem model_interp_eta (t : Lambda) (ρ : DEnv) :
    ddenot (Lambda.lam (Lambda.app (Lambda.lift 1 0 t) (Lambda.var 0))) ρ = ddenot t ρ :=
  model.interp_eta_of_extensional model_extensional t ρ

/-- The theory of `D∞`, as a λ-model, is the entry `Th(D∞)` of the lattice of λ-theories. -/
theorem theory_model_eq : LambdaModel.theory model = Lambda.LambdaTheory.dinf := rfl

/-- `D∞` is a nontrivial model: `Ω` and `I` are not identified. -/
theorem model_nontrivial : model.IsNontrivial :=
  ⟨ddenot Lambda.I (fun _ => Dinf.botDinf), Dinf.botDinf, ddenot_I_ne_bot _⟩

end ScottDinf

/-! ### The filter model -/

namespace Inter

/-- **The filter model of the intersection type system is a λ-model** — and it is the graph
model: by `Inter.deriv_iff_mem_denot` the filter of types of a term is exactly its value in
`GraphModel.model`. -/
def filterModel : LambdaModel := GraphModel.model

/-- The filter of the types assignable to `M` in the basis `Γ` is the interpretation of `M` in
the λ-model, at the environment determined by `Γ`. -/
theorem typeSet_eq_model_interp (Γ : Basis) (M : Lambda) :
    typeSet Γ M = filterModel.interp M (basisEnv Γ) := typeSet_eq_denot Γ M

/-- Typability is nontriviality of the value in the model. -/
theorem typable_iff_model_interp_ne_empty (M : Lambda) :
    Typable M ↔ ∃ ρ : GraphModel.Env, filterModel.interp M ρ ≠ (∅ : GraphModel.D) :=
  typable_iff_exists_denot_ne_empty M

end Inter

end
