/-
**Non-vacuity of coherence with instances of subclasses** — task `M25-TYPECLASS-SUPER-INST`
(round 10, part E1).

The example environment of `Start/TypeClassExample.lean`
(`class Eq a`, `class Eq a => Ord a`, `instance Eq Base`, `instance Eq b => Eq (a → b)`,
`instance Ord Base` whose superclass field is the `Eq Base` dictionary; `Base` plays the role of
`Int`) satisfies all the hypotheses of `coherence_unannotated_superInst`:

* `TypeClass.exampleEnv_normalSuperFields` — `NormalSuperFields`: the `Eq` field of the
  `Ord Base` dictionary is the normal derivation of `Eq Base` by its instance;
* `TypeClass.exampleEnv_superInstFragment` — `SuperInstFragment` (no overlapping instances; the
  closure conditions are vacuous for the empty constraint context);
* `TypeClass.example_superInst_coherence` — **coherence applied**: the method `eq` at `Base`
  (whose constraint `Eq Base` is entailed both by the instance and through the superclass of
  `Ord Base`) has an elaboration, and any two elaborations are β-convertible.
-/

import Start.TypeClassExample
import Start.TypeClassSuperNormalize

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

/-- The `Eq Base` dictionary is the normal dictionary of `Eq Base` (by its instance). -/
theorem dentN_eqBase : DEntN exampleEnv [] 0 true ⟨0, Mty.base⟩ eqBaseDict := by
  have h := DEntN.inst (E := exampleEnv) (P := []) (n := 0) (I := instEqBase)
    (s := fun _ => Mty.base) (ds := []) (fun _ => true) (by simp [exampleEnv]) rfl
    (fun k hk _ => absurd hk (Nat.not_lt_zero k))
  simpa [instEqBase, msubst, eqBaseDict, recMk, appsL, Lambda.substEnv, Lambda.lift] using h

/-- **The example environment has normal superclass fields.** -/
theorem exampleEnv_normalSuperFields : NormalSuperFields exampleEnv := by
  intro I hI D d hc hs
  simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl | rfl
  · simp [exampleEnv, instEqBase, eqDecl] at hc; subst hc; simp at hs
  · simp [exampleEnv, instEqArrow, eqDecl] at hc; subst hc; simp at hs
  · simp [exampleEnv, instOrdBase, ordDecl] at hc
    subst hc
    simp only [Option.some.injEq] at hs
    subst hs
    refine ⟨eqBaseDict, [Lambda.lam (Lambda.lam (Lambda.var 1))], rfl, rfl, true, ?_⟩
    exact dentN_eqBase

/-- **The example environment is in the fragment with instances of subclasses.** -/
theorem exampleEnv_superInstFragment : SuperInstFragment exampleEnv [] where
  env_ok := exampleEnv_ok
  no_overlap := by
    intro I hI I' hI' s s' hc hh
    simp only [exampleEnv, List.mem_cons, List.not_mem_nil, or_false] at hI hI'
    rcases hI with rfl | rfl | rfl <;> rcases hI' with rfl | rfl | rfl <;>
      simp_all [instEqBase, instEqArrow, instOrdBase, msubst, Cstr.subst]
  closure_rigid := by intro C hC; simp at hC
  closure_unique := by intro i j Ci Cj c hi; simp at hi

/-- The source program: the method `eq` of `Eq` at `Base`. -/
def exampleEq : Sexp := Sexp.method 0 0

/-- **Coherence applied in an environment with an instance of a subclass.** -/
theorem example_superInst_coherence :
    (∃ t, ElabS exampleEnv [] [] exampleEq (inst0 Mty.base binOp) t) ∧
      ∀ t t', ElabS exampleEnv [] [] exampleEq (inst0 Mty.base binOp) t →
        ElabS exampleEnv [] [] exampleEq (inst0 Mty.base binOp) t' → Lambda.Conv t t' := by
  refine coherence_unannotated_superInst exampleEnv_good exampleEnv_normalSuperFields
    exampleEnv_superInstFragment ?_ ?_
  · exact Bidi.method (D := eqDecl) (m := binOp) (by simp [exampleEnv]) (by simp [eqDecl])
      (by simp [binOp, HasVar])
  · exact STyping.method (D := eqDecl) (by simp [exampleEnv]) (by simp [eqDecl])
      (ent_eq_base [])

end TypeClass
