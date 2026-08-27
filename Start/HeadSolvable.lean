/-
Solvable terms have a head normal form — syntactically.

`Start/GraphAdequacy.lean` derives this implication from adequacy of the graph model.  With the
head reduction strategy of `Start/HeadReduction.lean` it also has a direct syntactic proof: if
`t M₁ … Mₙ` converts to the identity then, by confluence, it *reduces* to the identity, which is
a head normal form; and head normalizability of an application is inherited by its function part
(`Lambda.HasHnf.app_left`), so it travels back from `t M₁ … Mₙ` to `t`.

* `Lambda.hasHnf_appList_left` — if `t M₁ … Mₙ` has a head normal form then so does `t`;
* `Lambda.hasHnf_of_solvable`  — every solvable term has a head normal form.
-/

import Start.HeadReduction
import Start.Solvability

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Head normalizability of an application to a list of arguments is inherited by the function
part. -/
theorem hasHnf_appList_left : ∀ (args : List Lambda) {t : Lambda},
    HasHnf (appList t args) → HasHnf t := by
  intro args
  induction args with
  | nil => intro t h; exact h
  | cons a rest ih =>
      intro t h
      exact (ih h).app_left

/-- The identity is a head normal form. -/
theorem isHnf_I : IsHnf Lambda.I :=
  IsHnf.lam (IsHnf.neutral (Neutral.var 0))

/-- **Every solvable term has a head normal form.**  This is the syntactic proof; a semantic one
is `GraphModel.hasHnf_of_solvable`. -/
theorem hasHnf_of_solvable {t : Lambda} (h : Solvable t) : HasHnf t := by
  obtain ⟨args, -, u, h1, h2⟩ := h
  have hu : u = Lambda.I := (Lambda.reduces_normal_eq is_normal_I h2).symm
  subst hu
  exact hasHnf_appList_left args ⟨Lambda.I, h1, isHnf_I⟩

end Lambda

end
