import Start.RigidityNaturalTermFormula
import Mathlib.Data.Nat.Pairing

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/OrdinalCodes/NaturalPairingFormula.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
universe u
namespace Formula

def pairVars (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | _+1 => b

def pairLeftTerm : NaturalTerm := .binary false (.binary true (.var 1) (.var 1)) (.var 0)
def pairRightTerm : NaturalTerm := .binary false
  (.binary false (.binary true (.var 0) (.var 0)) (.var 0)) (.var 1)

def naturalPair (o Q x n y : ℕ) : Formula := .disj
  (.conj (.member x n) (pairLeftTerm.graph o Q y (pairVars x n)))
  (.conj (.neg (.member x n)) (pairRightTerm.graph o Q y (pairVars x n)))

theorem naturalPair_spec (o Q x n y : ℕ) (e : ℕ → ZFSet.{u})
    (ho : e o = ZFSet.omega) (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (a b : ℕ) (ha : e x = natSet a) (hb : e n = natSet b) :
    (naturalPair o Q x n y).Eval e ↔ e y = natSet (Nat.pair a b) := by
  have hv : ∀ i, e (pairVars x n i) = natSet (pairVars a b i) := by
    intro i; cases i <;> assumption
  have hl := NaturalTerm.graph_spec pairLeftTerm o Q y (pairVars x n) e ho hQ (pairVars a b) hv
  have hr := NaturalTerm.graph_spec pairRightTerm o Q y (pairVars x n) e ho hQ (pairVars a b) hv
  change (pairLeftTerm.graph o Q y (pairVars x n)).Eval e ↔ e y = natSet (b*b+a) at hl
  change (pairRightTerm.graph o Q y (pairVars x n)).Eval e ↔ e y = natSet (a*a+a+b) at hr
  simp only [naturalPair,eval_disj,Formula.Eval,hl,hr,ha,hb,natSet_mem_natSet,Nat.pair]
  by_cases h : a < b <;> simp [h]

end Formula
end TuringRigidity.BoundedSetTheory

