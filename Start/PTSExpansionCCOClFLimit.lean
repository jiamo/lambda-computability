import Start.PTSExpansionCCOClF

/-!
# Series V, big round, run 3, item B1: the β-law of a classifier cannot hold for all classes
(row M29-EP-CCOMEGA)

`Start/PTSExpansionCCOClF.lean` reduces root β-invariance of the environment-based classifier
`clF D` to the β-law of its combinators, `D.appF (D.lamF cA f) cU = f cU` (`clF_beta_of`).  This
module records why the law can only be asked **on well-classified arguments**: if it held for
all classes, `D.lamF cA` would be a section of the application map out of `C → C`, and a diagonal
argument collapses the class type.

* **`ClfData.subsingleton_of_beta`** — a class type whose combinators satisfy the β-law for every
  class and every function `C → C` has at most one element;
* `ClfData.not_beta_of_ne` — so for any two distinct classes the unrestricted β-law fails.

A classifier for `CC^ω` must therefore restrict the β-law to classes in the image of a domain
(the classes of the arguments that the abstraction's binder type admits); see the evidence note
(`docs/goal/evidence/M29-EP.md`, series V, big round, run 3).
-/

set_option autoImplicit false

namespace PureTypeSystem.CCO

/-- **The unrestricted β-law collapses the class type.** -/
theorem ClfData.subsingleton_of_beta {C : Type} (D : ClfData C)
    (hβ : ∀ (cA : C) (f : C → C) (cU : C), D.appF (D.lamF cA f) cU = f cU) : Subsingleton C := by
  classical
  refine ⟨fun a b => ?_⟩
  let f : C → C := fun c => if D.appF c c = a then b else a
  have h := hβ a f (D.lamF a f)
  by_cases e : D.appF (D.lamF a f) (D.lamF a f) = a
  · have h' : D.appF (D.lamF a f) (D.lamF a f) = b := by
      rw [h]; simp only [f, if_pos e]
    rw [← e, h']
  · exact absurd (by rw [h]; simp only [f, if_neg e]) e

/-- With two distinct classes, the β-law fails for some abstraction class and argument. -/
theorem ClfData.not_beta_of_ne {C : Type} (D : ClfData C) {a b : C} (hab : a ≠ b) :
    ¬ ∀ (cA : C) (f : C → C) (cU : C), D.appF (D.lamF cA f) cU = f cU := fun hβ =>
  hab ((D.subsingleton_of_beta hβ).elim a b)

end PureTypeSystem.CCO
