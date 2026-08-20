/-
# A representation theorem in the style of Dershowitz–Gurevich

The Church–Turing thesis itself is not a mathematical statement: one side of the identification it
proposes is informal.  What *can* be proved is a **representation theorem**: fix axioms describing
what a sequential algorithm is, and show that every object satisfying them is simulable by the
formal models of computation.  That is what this module does, for the following axiomatization.

A sequential algorithm operates on states with **finitely many locations**, each holding a natural
number (`Fin size → ℕ`).  Its transition is given by a **finite** list of *guarded update rules*:
each rule tests finitely many equalities and disequalities between terms built from the locations,
and, if the test succeeds, updates finitely many locations simultaneously.  This is the
"bounded exploration" idea in concrete form: one step of the algorithm can only look at, and only
change, a bounded part of the state, described by a fixed finite piece of syntax.

Crucially, computability of the transition is **derived, not assumed**:
`SeqAlgorithm.primrec_stepProg` proves that the induced state transition is primitive recursive.
From that, `SeqAlgorithm.partrec_run` shows that the input-output partial function of such an
algorithm is partial recursive, and hence (`lambdaComputable_run`, `tm2Computable_run`) it is
lambda-definable and computable by a Turing machine.

`SeqAlgorithm.doubling` is a genuine looping algorithm — it counts its input down while adding two
at each step — and `SeqAlgorithm.run_doubling` computes its function, so the statements above are
not vacuous.

What this is *not*: a proof of the Church–Turing thesis.  The theorem says that algorithms
*satisfying these axioms* are Turing simulable; whether the axioms capture the informal notion of
algorithm is exactly the question that cannot be settled mathematically.
-/

import Start.TM2PolyTime

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace SeqAlgorithm

/-! ## Syntax of one step -/

/-- Terms over the locations of a state. -/
inductive Expr (k : ℕ) : Type
  | loc : Fin k → Expr k
  | const : ℕ → Expr k
  | succ : Expr k → Expr k
  | pred : Expr k → Expr k
  | add : Expr k → Expr k → Expr k

/-- Value of a term in a state. -/
def evalExpr {k : ℕ} (s : Fin k → ℕ) : Expr k → ℕ
  | .loc i => s i
  | .const c => c
  | .succ e => evalExpr s e + 1
  | .pred e => evalExpr s e - 1
  | .add e₁ e₂ => evalExpr s e₁ + evalExpr s e₂

theorem primrec_evalExpr {k : ℕ} (e : Expr k) :
    Primrec fun s : Fin k → ℕ => evalExpr s e := by
  induction e with
  | loc i => exact Primrec.fin_app.comp Primrec.id (Primrec.const i)
  | const c => exact Primrec.const c
  | succ e ih => exact Primrec.nat_add.comp ih (Primrec.const 1)
  | pred e ih => exact Primrec.nat_sub.comp ih (Primrec.const 1)
  | add e₁ e₂ ih₁ ih₂ => exact Primrec.nat_add.comp ih₁ ih₂

/-- The guard of a rule: finitely many equalities and finitely many disequalities. -/
structure Guard (k : ℕ) where
  /-- equalities that must hold -/
  eqs : List (Expr k × Expr k)
  /-- disequalities that must hold -/
  neqs : List (Expr k × Expr k)

/-- All the listed equalities hold in the state. -/
def testEqs {k : ℕ} (s : Fin k → ℕ) : List (Expr k × Expr k) → Bool
  | [] => true
  | (a, b) :: rest => if evalExpr s a = evalExpr s b then testEqs s rest else false

/-- All the listed disequalities hold in the state. -/
def testNeqs {k : ℕ} (s : Fin k → ℕ) : List (Expr k × Expr k) → Bool
  | [] => true
  | (a, b) :: rest => if evalExpr s a = evalExpr s b then false else testNeqs s rest

/-- The guard holds in the state. -/
def Guard.test {k : ℕ} (g : Guard k) (s : Fin k → ℕ) : Bool :=
  if testEqs s g.eqs then testNeqs s g.neqs else false

theorem primrec_testEqs {k : ℕ} (l : List (Expr k × Expr k)) :
    Primrec fun s : Fin k → ℕ => testEqs s l := by
  induction l with
  | nil => exact Primrec.const true
  | cons p rest ih =>
      exact Primrec.ite
        (Primrec.eq.comp (primrec_evalExpr p.1) (primrec_evalExpr p.2)) ih (Primrec.const false)

theorem primrec_testNeqs {k : ℕ} (l : List (Expr k × Expr k)) :
    Primrec fun s : Fin k → ℕ => testNeqs s l := by
  induction l with
  | nil => exact Primrec.const true
  | cons p rest ih =>
      exact Primrec.ite
        (Primrec.eq.comp (primrec_evalExpr p.1) (primrec_evalExpr p.2)) (Primrec.const false) ih

theorem primrec_guard_test {k : ℕ} (g : Guard k) :
    Primrec fun s : Fin k → ℕ => g.test s :=
  Primrec.ite (Primrec.eq.comp (primrec_testEqs g.eqs) (Primrec.const true))
    (primrec_testNeqs g.neqs) (Primrec.const false)

/-- A guarded update rule: when the guard holds, the listed locations are updated
simultaneously. -/
structure Rule (k : ℕ) where
  /-- the guard -/
  guard : Guard k
  /-- the simultaneous updates -/
  updates : List (Fin k × Expr k)

/-- Applying a list of simultaneous updates: all right-hand sides are evaluated in the old
state. -/
def applyUpdates {k : ℕ} (s : Fin k → ℕ) : List (Fin k × Expr k) → Fin k → ℕ
  | [], i => s i
  | (j, e) :: rest, i => if i = j then evalExpr s e else applyUpdates s rest i

theorem primrec_applyUpdates {k : ℕ} (ups : List (Fin k × Expr k)) :
    Primrec fun s : Fin k → ℕ => applyUpdates s ups := by
  refine Primrec.fin_curry.2 ?_
  induction ups with
  | nil => exact Primrec.fin_app
  | cons p rest ih =>
      exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const p.1))
        ((primrec_evalExpr p.2).comp Primrec.fst) ih

/-- One step of the program: the first rule whose guard holds fires; if none does, the state is
unchanged. -/
def stepProg {k : ℕ} : List (Rule k) → (Fin k → ℕ) → Fin k → ℕ
  | [], s => s
  | r :: rest, s => if r.guard.test s then applyUpdates s r.updates else stepProg rest s

/-- **The transition of a bounded-exploration algorithm is primitive recursive.**  Computability
is derived from the axioms, not assumed. -/
theorem primrec_stepProg {k : ℕ} (prog : List (Rule k)) :
    Primrec fun s : Fin k → ℕ => stepProg prog s := by
  induction prog with
  | nil => exact Primrec.id
  | cons r rest ih =>
      exact Primrec.ite (Primrec.eq.comp (primrec_guard_test r.guard) (Primrec.const true))
        (primrec_applyUpdates r.updates) ih

/-! ## Algorithms and the functions they compute -/

/-- A sequential algorithm: finitely many locations, a finite list of guarded update rules, and
designated input, output and halting locations. -/
structure Algorithm where
  /-- number of locations -/
  size : ℕ
  /-- the finite list of guarded update rules -/
  prog : List (Rule size)
  /-- where the input is placed -/
  inLoc : Fin size
  /-- where the output is read off -/
  outLoc : Fin size
  /-- a nonzero value here means the algorithm has halted -/
  haltLoc : Fin size

namespace Algorithm

variable (a : Algorithm)

/-- The initial state on input `n`: the input location holds `n`, everything else `0`. -/
def init (n : ℕ) : Fin a.size → ℕ := fun i => if i = a.inLoc then n else 0

/-- The state after `t` steps on input `n`. -/
def iter (n t : ℕ) : Fin a.size → ℕ := (stepProg a.prog)^[t] (a.init n)

@[simp] theorem iter_zero (n : ℕ) : a.iter n 0 = a.init n := rfl

theorem iter_succ (n t : ℕ) : a.iter n (t + 1) = stepProg a.prog (a.iter n t) := by
  rw [iter, iter, Function.iterate_succ_apply']

/-- The observation made after `t` steps: the output, once the halting location is nonzero. -/
def probe (n t : ℕ) : Option ℕ :=
  if a.iter n t a.haltLoc = 0 then none else some (a.iter n t a.outLoc)

/-- The partial function computed by the algorithm: run it until the halting location becomes
nonzero, then read off the output location. -/
def run (n : ℕ) : Part ℕ := Nat.rfindOpt (a.probe n)

theorem primrec_init : Primrec a.init := by
  refine Primrec.fin_curry.2 ?_
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const a.inLoc)) Primrec.fst
    (Primrec.const 0)

theorem primrec_iter : Primrec₂ a.iter := by
  have hstep : Primrec₂ fun (_ : ℕ) (r : ℕ × (Fin a.size → ℕ)) => stepProg a.prog r.2 :=
    (primrec_stepProg a.prog).comp (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_rec (f := fun n : ℕ => a.init n) a.primrec_init hstep
  refine h.of_eq fun n t => ?_
  induction t with
  | zero => rfl
  | succ t ih => rw [iter_succ, ← ih]

theorem primrec_probe : Primrec₂ a.probe := by
  have hstate : Primrec fun p : ℕ × ℕ => a.iter p.1 p.2 := a.primrec_iter
  refine Primrec.ite
    (Primrec.eq.comp (Primrec.fin_app.comp hstate (Primrec.const a.haltLoc)) (Primrec.const 0))
    (Primrec.const none)
    (Primrec.option_some.comp (Primrec.fin_app.comp hstate (Primrec.const a.outLoc)))

/-- **The representation theorem.**  The input-output function of a bounded-exploration
sequential algorithm is partial recursive. -/
theorem partrec_run : Partrec a.run :=
  Partrec.rfindOpt (Primrec₂.to_comp a.primrec_probe)

/-- **Such an algorithm is simulable in the lambda calculus.** -/
theorem lambdaComputable_run : LambdaComputable a.run :=
  lambdaComputable_iff_partrec.2 a.partrec_run

/-- **Such an algorithm is simulable by a Turing machine.** -/
theorem tm2Computable_run : TM2Partrec.TM2ComputableNat a.run :=
  TM2Partrec.tm2Computable_iff_partrec.2 a.partrec_run

end Algorithm

/-! ## A looping algorithm, so the theorem is not vacuous -/

/-- Location of the counter. -/
def cnt : Fin 3 := 0
/-- Location of the accumulator. -/
def acc : Fin 3 := 1
/-- Location of the halting flag. -/
def flag : Fin 3 := 2

/-- The rule that fires when the counter has reached zero: raise the halting flag. -/
def doublingHalt : Rule 3 where
  guard := ⟨[(Expr.loc cnt, Expr.const 0)], []⟩
  updates := [(flag, Expr.const 1)]

/-- The looping rule: decrement the counter and add two to the accumulator. -/
def doublingLoop : Rule 3 where
  guard := ⟨[], [(Expr.loc cnt, Expr.const 0)]⟩
  updates := [(cnt, Expr.pred (Expr.loc cnt)), (acc, Expr.succ (Expr.succ (Expr.loc acc)))]

/-- An algorithm that doubles its input by counting it down. -/
def doubling : Algorithm where
  size := 3
  prog := [doublingHalt, doublingLoop]
  inLoc := cnt
  outLoc := acc
  haltLoc := flag

/-- The state of the doubling algorithm after `t` steps, while the counter is still positive. -/
def doublingState (n t : ℕ) : Fin 3 → ℕ := ![n - t, 2 * t, 0]

theorem doubling_init (n : ℕ) : doubling.init n = doublingState n 0 := by
  funext i
  fin_cases i <;> simp [Algorithm.init, doubling, doublingState, cnt, acc, flag]

theorem doubling_step_loop {n t : ℕ} (ht : t < n) :
    stepProg doubling.prog (doublingState n t) = doublingState n (t + 1) := by
  have hpos : n - t ≠ 0 := by omega
  funext i
  fin_cases i <;>
    simp [doubling, doublingState, stepProg, doublingHalt, doublingLoop, Guard.test, testEqs,
      testNeqs, evalExpr, applyUpdates, cnt, acc, flag, hpos] <;> omega

theorem doubling_iter (n : ℕ) : ∀ t ≤ n, doubling.iter n t = doublingState n t := by
  intro t
  induction t with
  | zero => intro _; simpa using doubling_init n
  | succ t ih =>
      intro hle
      rw [Algorithm.iter_succ, ih (by omega), doubling_step_loop (by omega)]

theorem doubling_step_halt (n : ℕ) :
    stepProg doubling.prog (doublingState n n) = ![0, 2 * n, 1] := by
  funext i
  fin_cases i <;>
    simp [doubling, doublingState, stepProg, doublingHalt, doublingLoop, Guard.test, testEqs,
      testNeqs, evalExpr, applyUpdates, cnt, acc, flag]

theorem doubling_probe_lt {n t : ℕ} (ht : t ≤ n) : doubling.probe n t = none := by
  rw [Algorithm.probe, doubling_iter n t ht]
  simp [doublingState, doubling, flag]

theorem doubling_probe_halt (n : ℕ) : doubling.probe n (n + 1) = some (2 * n) := by
  have hstate : doubling.iter n (n + 1) = ![0, 2 * n, 1] := by
    rw [Algorithm.iter_succ, doubling_iter n n (le_refl n), doubling_step_halt]
  rw [Algorithm.probe, hstate]
  simp [doubling, acc, flag]

/-- **The doubling algorithm computes doubling.**  In particular the notion of algorithm above is
not vacuous, and it really does describe looping computations. -/
theorem run_doubling (n : ℕ) : doubling.run n = Part.some (2 * n) :=
  TM2Partrec.rfindOpt_eq_some (doubling_probe_halt n) fun t ht =>
    doubling_probe_lt (by omega)

/-- The doubling function is therefore lambda-definable and machine computable, through the
representation theorem. -/
theorem lambdaComputable_doubling : LambdaComputable fun n => Part.some (2 * n) := by
  obtain ⟨F, hF⟩ := doubling.lambdaComputable_run
  refine ⟨F, fun n m => ?_⟩
  have h := hF n m
  rwa [run_doubling n] at h

end SeqAlgorithm
