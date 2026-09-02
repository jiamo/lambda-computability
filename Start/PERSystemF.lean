/-
**The PER model of System F.**

`Start/SystemF.lean` gives Curry-style System F over the untyped terms of the development, and
proves strong normalization by reducibility candidates — a *syntactic* interpretation of types by
sets of terms.  This file gives a *semantic* one: over any λ-model `M` (hence, by
`Start/PCATotal.lean`, any of the PCAs the library constructs), a System F type is interpreted by
a partial equivalence relation on the carrier of the model, the arrow by the function-space PER
and `∀` by the **intersection of the family of interpretations over all PERs** — impredicative
quantification is exactly the arbitrary intersection of `Start/PER.lean`.

* `SystemF.Per.tyPer` — the interpretation of types;
* `SystemF.Per.tyPer_tyRename`, `.tyPer_tySubst`, `.tyPer_tyShift`, `.tyPer_tyInst` — the semantic
  renaming and substitution lemmas;
* `SystemF.Per.sound` — **soundness**: a typable term is related to itself, and more generally
  related environments give related values, in the PER interpreting its type;
* `SystemF.Per.dom_interp_of_typing` — hence the value of a closed typable term lies in the
  domain of the PER interpreting its type: the PER model is a model of System F.

Nothing here is a reducibility argument: the interpretation is by relations on the model, and the
polymorphic case is genuinely impredicative — the intersection ranges over *all* PERs, including
the one being defined.
-/

import Start.PER
import Start.PCATotal
import Start.SystemF

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace SystemF

namespace Per

open Realizability

variable (M : Lambda.LambdaModel.{u})

/-- The PCA structure of a λ-model, as an instance for this file. -/
noncomputable scoped instance instPCACarrier : PCA M.Carrier :=
  Realizability.Lambda.lambdaModelPCA M

@[simp] theorem app_eq (a b : M.Carrier) : PCA.app a b = Part.some (M.app a b) := rfl

theorem arrow_rel_iff {R S : PER M.Carrier} {r r' : M.Carrier} :
    (PER.arrow R S).rel r r' ↔ ∀ a b, R.rel a b → S.rel (M.app r a) (M.app r' b) := by
  constructor
  · intro h a b hab
    obtain ⟨u, hu, v, hv, huv⟩ := h a b hab
    rw [app_eq, Part.mem_some_iff] at hu hv
    rwa [← hu, ← hv]
  · intro h a b hab
    exact ⟨M.app r a, by rw [app_eq]; exact Part.mem_some _,
      M.app r' b, by rw [app_eq]; exact Part.mem_some _, h a b hab⟩

/-! ### The interpretation of types -/

/-- Extending a valuation of type variables by a new PER. -/
def perCons (R : PER M.Carrier) (ρ : ℕ → PER M.Carrier) : ℕ → PER M.Carrier
  | 0 => R
  | n + 1 => ρ n

@[simp] theorem perCons_zero (R : PER M.Carrier) (ρ : ℕ → PER M.Carrier) :
    perCons M R ρ 0 = R := rfl

@[simp] theorem perCons_succ (R : PER M.Carrier) (ρ : ℕ → PER M.Carrier) (n : ℕ) :
    perCons M R ρ (n + 1) = ρ n := rfl

/-- **The interpretation of a System F type as a PER**: type variables by the valuation, arrows
by the function-space PER, and `∀` by the intersection over all PERs. -/
noncomputable def tyPer : FTy → (ℕ → PER M.Carrier) → PER M.Carrier
  | FTy.var i, ρ => ρ i
  | FTy.arrow A B, ρ => PER.arrow (tyPer A ρ) (tyPer B ρ)
  | FTy.all A, ρ => PER.iInter (fun R : PER M.Carrier => tyPer A (perCons M R ρ))

@[simp] theorem tyPer_var (i : ℕ) (ρ : ℕ → PER M.Carrier) : tyPer M (FTy.var i) ρ = ρ i := rfl

@[simp] theorem tyPer_arrow (A B : FTy) (ρ : ℕ → PER M.Carrier) :
    tyPer M (FTy.arrow A B) ρ = PER.arrow (tyPer M A ρ) (tyPer M B ρ) := rfl

@[simp] theorem tyPer_all (A : FTy) (ρ : ℕ → PER M.Carrier) :
    tyPer M (FTy.all A) ρ
      = PER.iInter (fun R : PER M.Carrier => tyPer M A (perCons M R ρ)) := rfl

/-! ### Semantic renaming and substitution -/

theorem tyPer_tyRename (A : FTy) (r : ℕ → ℕ) (ρ : ℕ → PER M.Carrier) :
    tyPer M (tyRename r A) ρ = tyPer M A (fun i => ρ (r i)) := by
  induction A generalizing r ρ with
  | var i => rfl
  | arrow A B ihA ihB => simp [tyRename, ihA, ihB]
  | all A ih =>
      simp only [tyRename, tyPer_all]
      congr 1
      funext R
      rw [ih]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ n => rfl

theorem tyPer_tyShift (A : FTy) (R : PER M.Carrier) (ρ : ℕ → PER M.Carrier) :
    tyPer M (tyShift A) (perCons M R ρ) = tyPer M A ρ := by
  rw [tyShift, tyPer_tyRename]
  rfl

theorem tyPer_tySubst (A : FTy) (s : ℕ → FTy) (ρ : ℕ → PER M.Carrier) :
    tyPer M (tySubst s A) ρ = tyPer M A (fun i => tyPer M (s i) ρ) := by
  induction A generalizing s ρ with
  | var i => rfl
  | arrow A B ihA ihB => simp [tySubst, ihA, ihB]
  | all A ih =>
      simp only [tySubst, tyPer_all]
      congr 1
      funext R
      rw [ih]
      congr 1
      funext i
      cases i with
      | zero => rfl
      | succ n => exact tyPer_tyShift M (s n) R ρ

theorem tyPer_tyInst (A B : FTy) (ρ : ℕ → PER M.Carrier) :
    tyPer M (tyInst B A) ρ = tyPer M A (perCons M (tyPer M B ρ) ρ) := by
  rw [tyInst, tyPer_tySubst]
  congr 1
  funext i
  cases i with
  | zero => rfl
  | succ n => rfl

/-! ### Soundness -/

/-- Two environments are related in a context when they are related componentwise. -/
def RelEnv (Γ : List FTy) (ρ : ℕ → PER M.Carrier) (σ σ' : ℕ → M.Carrier) : Prop :=
  ∀ (i : ℕ) (B : FTy), Γ[i]? = some B → (tyPer M B ρ).rel (σ i) (σ' i)

/-- **Soundness of the PER interpretation of System F.**  A typable term takes related
environments to related values in the PER interpreting its type. -/
theorem sound {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A)
    (ρ : ℕ → PER M.Carrier) (σ σ' : ℕ → M.Carrier) (hσ : RelEnv M Γ ρ σ σ') :
    (tyPer M A ρ).rel (M.interp t σ) (M.interp t σ') := by
  induction h generalizing ρ σ σ' with
  | @var Γ i A hi =>
      rw [M.interp_var, M.interp_var]
      exact hσ i A hi
  | @app Γ a b A B _ _ iha ihb =>
      rw [M.interp_app, M.interp_app]
      have h₁ := iha ρ σ σ' hσ
      have h₂ := ihb ρ σ σ' hσ
      rw [tyPer_arrow, arrow_rel_iff] at h₁
      exact h₁ _ _ h₂
  | @lam Γ t A B _ ih =>
      rw [tyPer_arrow, arrow_rel_iff]
      intro a b hab
      rw [M.interp_beta, M.interp_beta]
      refine ih ρ _ _ ?_
      intro i C hi
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
          subst hi
          exact hab
      | succ n =>
          simp only [List.getElem?_cons_succ] at hi
          exact hσ n C hi
  | @tlam Γ t A _ ih =>
      rw [tyPer_all]
      intro R
      refine ih (perCons M R ρ) σ σ' ?_
      intro i C hi
      rw [List.getElem?_map] at hi
      obtain ⟨B, hB, rfl⟩ : ∃ B, Γ[i]? = some B ∧ tyShift B = C := by
        cases hΓ : Γ[i]? with
        | none => rw [hΓ] at hi; simp at hi
        | some B =>
            rw [hΓ] at hi
            simp only [Option.map_some, Option.some.injEq] at hi
            exact ⟨B, rfl, hi⟩
      rw [tyPer_tyShift]
      exact hσ i B hB
  | @tapp Γ t A B _ ih =>
      have h := ih ρ σ σ' hσ
      rw [tyPer_all] at h
      rw [tyPer_tyInst]
      exact h (tyPer M B ρ)

/-- The value of a closed typable term lies in the domain of the PER interpreting its type. -/
theorem dom_interp_of_typing {t : Lambda} {A : FTy} (h : Typing [] t A)
    (ρ : ℕ → PER M.Carrier) (σ : ℕ → M.Carrier) :
    (tyPer M A ρ).dom (M.interp t σ) :=
  sound M h ρ σ σ (by intro i B hi; simp at hi)

/-- The model is not vacuous: the identity is in the domain of the PER interpreting
`∀X. X → X`. -/
theorem dom_interp_idTy (ρ : ℕ → PER M.Carrier) (σ : ℕ → M.Carrier) :
    (tyPer M idTy ρ).dom (M.interp (Lambda.lam (Lambda.var 0)) σ) :=
  dom_interp_of_typing M (Typing.tlam (Typing.lam (Typing.var rfl))) ρ σ

end Per

end SystemF
