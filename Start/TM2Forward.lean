/-
# Bundling Mathlib's compiler from partial recursive functions into a `FinTM2`

`Mathlib`'s `Turing.PartrecToTM2` compiles a `Turing.ToPartrec.Code` into a TM2 machine
`Turing.PartrecToTM2.tr`, whose label type `Λ'` is infinite; only the labels reachable from a
given code are used, and `Turing.PartrecToTM2.tr_supports` records that the machine never
leaves the finite set `codeSupp c Cont'.halt`.

Restricting the labels to that finite set (`Start/TM2Restrict.lean`) turns the machine into a
bundled `Turing.FinTM2`, which is the format the arithmetization of `Start/TM2Partrec.lean`
consumes.  The main result is

* `TM2Partrec.trFinTM2_outputs` — the bundled machine started on `trList v` halts with
  `trList w` on its output stack whenever `w ∈ Code.eval c v`.
-/

import Start.TM2Restrict

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TM2Partrec

open Turing Turing.PartrecToTM2 Turing.ToPartrec

/-- The four stacks of the machine form a finite type. -/
instance : Fintype K' :=
  ⟨{K'.main, K'.rev, K'.aux, K'.stack}, fun x => by cases x <;> decide⟩

/-! ## From reachability to iteration -/

/-- A reachable configuration is reached in a definite number of steps. -/
theorem exists_iterate_of_reaches {α : Type} {f : α → Option α} {a b : α}
    (h : Turing.Reaches f a b) : ∃ t : ℕ, (flip Bind.bind f)^[t] (some a) = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨t + 1, by rw [Function.iterate_succ_apply', ht]; exact hstep⟩

/-- Conversely, a configuration reached by iteration is reachable. -/
theorem reaches_of_iterate {α : Type} {f : α → Option α} :
    ∀ (t : ℕ) {a b : α}, (flip Bind.bind f)^[t] (some a) = some b → Turing.Reaches f a b := by
  intro t
  induction t with
  | zero => intro a b h; rw [Option.some_inj.1 h]; exact Relation.ReflTransGen.refl
  | succ t ih =>
      intro a b h
      rw [Function.iterate_succ_apply'] at h
      cases hx : (flip Bind.bind f)^[t] (some a) with
      | none => rw [hx] at h; exact absurd h (by simp [flip])
      | some c =>
          rw [hx] at h
          exact Relation.ReflTransGen.tail (ih hx) h

/-! ## The bundled machine of a code -/

section Code

variable (c : Code)

/-- The finite set of labels the machine of `c` never leaves. -/
def codeLabels : Finset Λ' := codeSupp c Cont'.halt

theorem trNormal_mem_codeLabels : trNormal c Cont'.halt ∈ codeLabels c :=
  codeSupp_self c Cont'.halt (trStmts₁_self _)

/-- The main label of the machine of `c`, as an element of the finite label set. -/
def mainLabel : {x // x ∈ codeLabels c} :=
  ⟨trNormal c Cont'.halt, trNormal_mem_codeLabels c⟩

theorem supportsStmt_tr (q : Λ') (hq : q ∈ codeLabels c) :
    TM2.SupportsStmt (codeLabels c) (tr q) :=
  (tr_supports c Cont'.halt).2 q hq

/-- The bundled machine computing the code `c`: `Mathlib`'s machine with its labels
restricted to the finite set it never leaves. -/
def trFinTM2 : FinTM2 where
  K := K'
  k₀ := K'.main
  k₁ := K'.main
  Γ := fun _ => Γ'
  Λ := {x // x ∈ codeLabels c}
  main := mainLabel c
  σ := Option Γ'
  initialState := none
  m := restrict (codeLabels c) (mainLabel c) tr

instance trFinTM2_ΓFin : ∀ k, Fintype ((trFinTM2 c).Γ k) := fun _ => (inferInstance : Fintype Γ')

theorem mapCfg_initList (v : List ℕ) :
    mapCfg (codeLabels c) (initList (trFinTM2 c) (trList v)) = init c v := by
  have hstk : (initList (trFinTM2 c) (trList v)).stk = K'.elim (trList v) [] [] [] := by
    funext k
    cases k <;> rfl
  simp only [mapCfg, hstk, init]
  rfl

theorem mapCfg_haltList (w : List ℕ) :
    mapCfg (codeLabels c) (haltList (trFinTM2 c) (trList w)) = halt w := by
  have hstk : (haltList (trFinTM2 c) (trList w)).stk = K'.elim (trList w) [] [] [] := by
    funext k
    cases k <;> rfl
  simp only [mapCfg, hstk, halt]
  rfl

/-- The number of steps the bundled machine of `c` takes to halt with `trList w` on its
output stack, when `w` is a value of `c` on `v`. -/
theorem exists_steps_trFinTM2 {v w : List ℕ} (h : w ∈ Code.eval c v) :
    ∃ t : ℕ, (flip Bind.bind (trFinTM2 c).step)^[t]
      (some (initList (trFinTM2 c) (trList v))) = some (haltList (trFinTM2 c) (trList w)) := by
  have hmem : halt w ∈ Turing.eval (TM2.step tr) (init c v) := by
    rw [tr_eval c v]
    exact Part.mem_map _ h
  obtain ⟨hreach, -⟩ := Turing.mem_eval.1 hmem
  obtain ⟨t, ht⟩ := exists_iterate_of_reaches hreach
  refine ⟨t, ?_⟩
  change (flip Bind.bind (TM2.step (trFinTM2 c).m))^[t]
      (some (initList (trFinTM2 c) (trList v))) = some (haltList (trFinTM2 c) (trList w))
  have hmap := iterate_map_opt (codeLabels c) (mainLabel c) tr
    (supportsStmt_tr c) t (some (initList (trFinTM2 c) (trList v)))
  rw [Option.map_some, mapCfg_initList c v, ht] at hmap
  rw [show (trFinTM2 c).m = restrict (codeLabels c) (mainLabel c) tr from rfl]
  have hval : ((flip Bind.bind (TM2.step (restrict (codeLabels c) (mainLabel c) tr)))^[t]
      (some (initList (trFinTM2 c) (trList v)))).map (mapCfg (codeLabels c)) =
      some (mapCfg (codeLabels c) (haltList (trFinTM2 c) (trList w))) := by
    rw [hmap, mapCfg_haltList c w]
  obtain ⟨y, hy, hy'⟩ := Option.map_eq_some_iff.1 hval
  rw [hy, mapCfg_injective _ hy']

/-- **The bundled machine computes the code.**  If `w` is a value of `c` on `v`, then the
bundled machine of `c`, started with `trList v` on its input stack, halts with `trList w` on
its output stack. -/
noncomputable def trFinTM2_outputs {v w : List ℕ} (h : w ∈ Code.eval c v) :
    TM2Outputs (trFinTM2 c) (trList v) (some (trList w)) :=
  ⟨(exists_steps_trFinTM2 c h).choose, (exists_steps_trFinTM2 c h).choose_spec⟩

end Code

end TM2Partrec
