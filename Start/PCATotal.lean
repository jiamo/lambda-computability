/-
Total combinatory algebras are partial combinatory algebras.

The simplest examples of a PCA are the ones where application happens to be total.  This file
records the general construction and applies it to the λ-models of `Start/LambdaModel.lean`: the
combinators `K` and `S` of a λ-model satisfy the total combinatory axioms
(`Lambda.LambdaModel.app_app_K`, `..._app_app_app_S`), hence every λ-model is a PCA.

* `Realizability.TCA` — total combinatory algebras;
* `Realizability.TCA.toPCA` — a TCA is a PCA;
* `Realizability.lambdaModelTCA`, `Realizability.lambdaModelPCA` — every λ-model is one, so the
  graph model, `D∞` and the filter model of the library are all PCAs.
-/

import Start.PCA
import Start.LambdaModel

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Realizability

/-- A **total combinatory algebra**: a set with a total application and the combinators `k`, `s`
satisfying the usual equations. -/
class TCA (A : Type u) where
  /-- The (total) application. -/
  tapp : A → A → A
  /-- The combinator `k`. -/
  k : A
  /-- The combinator `s`. -/
  s : A
  /-- `k a b = a`. -/
  k_eq : ∀ a b : A, tapp (tapp k a) b = a
  /-- `s a b c = (a c) (b c)`. -/
  s_eq : ∀ a b c : A, tapp (tapp (tapp s a) b) c = tapp (tapp a c) (tapp b c)

/-- A total combinatory algebra is a partial combinatory algebra with everywhere defined
application. -/
instance TCA.toPCA (A : Type u) [TCA A] : PCA A where
  app a b := Part.some (TCA.tapp a b)
  k := TCA.k
  s := TCA.s
  k_dom _ := trivial
  k_app a b := by simp [TCA.k_eq]
  s_dom _ _ := by simp
  s_app a b c := by simp [TCA.s_eq]

@[simp] theorem TCA.app_eq {A : Type u} [TCA A] (a b : A) :
    PCA.app a b = Part.some (TCA.tapp a b) := rfl

namespace Lambda

open _root_.Lambda

/-- The total combinatory algebra underlying a λ-model. -/
@[instance_reducible]
noncomputable def lambdaModelTCA (M : LambdaModel.{u}) : TCA M.Carrier where
  tapp := M.app
  k := M.K M.env0
  s := M.S M.env0
  k_eq := M.app_app_K M.env0
  s_eq := M.app_app_app_S M.env0

/-- **Every λ-model is a PCA**. -/
@[instance_reducible]
noncomputable def lambdaModelPCA (M : LambdaModel.{u}) : PCA M.Carrier :=
  letI := lambdaModelTCA M
  TCA.toPCA M.Carrier

end Lambda

end Realizability
