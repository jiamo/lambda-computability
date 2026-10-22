import Start.TypeClassSuperExample

/-!
# Series V, round 4, run 1, part C2: the failure at `sup (inst I ds)` (row M25-TYPECLASS-SUPER-FIELD)

An environment satisfying `SuperField` whose superclass field is **not** normal: with
`class Eq a`, `class Eq a => Ord a`, `instance Ord Base` (normal field) and a second subclass
`class Eq a => Ord₂ a` with `instance Ord₂ Base` whose `Eq` field is the superclass projection
of the `Ord Base` dictionary, i.e. the derivation `sup (inst Ord Base)`.

* `superEnv_superField` — `SuperField superEnv instOrd2Base`;
* **`superEnv_sup_inst_step`** — the redex `sup (inst Ord₂Base [])` for `Eq Base` and its
  contractum, the field derivation `sup (inst OrdBase [])`, are both derivations of the *same*
  constraint `Eq Base`, and the contractum is again a superclass projection of an instance
  dictionary.  So a termination measure for `DEnt.normalize_super` under `SuperField` cannot
  be read off the constraint (Paterson size), and one contraction of `sup (inst I ds)` can
  produce a new redex of the same kind.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-- The `Eq` field of `Ord₂ Base`: the superclass projection of the `Ord Base` dictionary. -/
def ord2Field : Lambda := recProj 2 0 ordBaseDict

/-- The dictionary of `instance Ord₂ Base`. -/
def ord2BaseDict : Lambda := recMk [ord2Field, Lambda.lam (Lambda.lam (Lambda.var 1))]

/-- `instance Ord₂ Base` (class `2`). -/
def instOrd2Base : Inst := ⟨2, Mty.base, [], ord2BaseDict⟩

/-- The environment: `Eq`, `Ord`, `Ord₂` (both subclasses of `Eq`). -/
def superEnv : Env :=
  ⟨[eqDecl, ordDecl, ordDecl], [instEqBase, instEqArrow, instOrdBase, instOrd2Base]⟩

theorem ordDecl_fields_length (rec : ℕ → Mty → FTy) (τ : Mty) :
    (dictFields rec ordDecl τ).length = 2 := by
  simp [dictFields, ordDecl]

theorem substEnv_nil_closed_ord : Lambda.substEnv (fun k => ([] : List Lambda).getD k (Lambda.var 0))
    ordBaseDict = ordBaseDict := by
  simp [ordBaseDict, eqBaseDict, recMk, appsL, Lambda.substEnv, Lambda.lift]

theorem substEnv_nil_closed_ord2 : Lambda.substEnv (fun k => ([] : List Lambda).getD k (Lambda.var 0))
    ord2BaseDict = ord2BaseDict := by
  simp [ord2BaseDict, ord2Field, recProj, ordBaseDict, eqBaseDict, recMk, appsL, Lambda.substEnv,
    Lambda.lift, sel, lams, Lambda.envCons]

/-- The field derivation: `Eq Base` by `sup (inst OrdBase [])`. -/
theorem dent_ord2Field (P : List Cstr) (n : ℕ) : DEnt superEnv P n ⟨0, Mty.base⟩ ord2Field := by
  have hi : DEnt superEnv P n ⟨1, Mty.base⟩ ordBaseDict := by
    have h := DEnt.inst (E := superEnv) (P := P) (n := n) (I := instOrdBase)
      (s := fun _ => Mty.base) (ds := []) (by simp [superEnv]) rfl
      (fun k hk _ => absurd hk (Nat.not_lt_zero k))
    rw [show instOrdBase.dict = ordBaseDict from rfl, substEnv_nil_closed_ord] at h
    simpa [instOrdBase, msubst] using h
  exact DEnt.sup (E := superEnv) (c := 1) (D := ordDecl) (by simp [superEnv]) rfl hi

/-- **`instance Ord₂ Base` is well formed for its superclass.** -/
theorem superEnv_superField : SuperField superEnv instOrd2Base := by
  intro D d hc hs
  simp only [superEnv, instOrd2Base] at hc
  simp at hc
  subst hc
  simp only [ordDecl, Option.some.injEq] at hs
  subst hs
  exact ⟨ord2Field, [Lambda.lam (Lambda.lam (Lambda.var 1))], rfl, by simp [dictFields, ordDecl],
    dent_ord2Field _ _⟩

/-- **The failure at `sup (inst I ds)`.**  The redex (the `Eq` projection of the `Ord₂ Base`
dictionary) and its contractum (the field `ord2Field`) derive the same constraint `Eq Base`, and
the contractum is again the superclass projection of an instance dictionary. -/
theorem superEnv_sup_inst_step :
    DEnt superEnv [] 0 ⟨0, Mty.base⟩ (recProj 2 0 ord2BaseDict) ∧
      DEnt superEnv [] 0 ⟨0, Mty.base⟩ ord2Field ∧
      ord2Field = recProj 2 0 instOrdBase.dict ∧ instOrdBase ∈ superEnv.insts := by
  refine ⟨?_, dent_ord2Field _ _, rfl, by simp [superEnv]⟩
  have hi : DEnt superEnv [] 0 ⟨2, Mty.base⟩ ord2BaseDict := by
    have h := DEnt.inst (E := superEnv) (P := []) (n := 0) (I := instOrd2Base)
      (s := fun _ => Mty.base) (ds := []) (by simp [superEnv]) rfl
      (fun k hk _ => absurd hk (Nat.not_lt_zero k))
    rw [show instOrd2Base.dict = ord2BaseDict from rfl, substEnv_nil_closed_ord2] at h
    simpa [instOrd2Base, msubst] using h
  exact DEnt.sup (E := superEnv) (c := 2) (D := ordDecl) (by simp [superEnv]) rfl hi

end TypeClass
