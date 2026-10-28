/-
**Depth-three circuits of the absorbed development as host circuits** — milestone M26
(`M26-UNIFY-DEPTHTHREE`, the circuit half).

`Start/DepthThreeHost.lean` translates every `Σ₃` host circuit (`ACCirc.IsSigma3`) into an upstream
`Circuit3` computing the same function, with at most `2 · size + 1` gates.  This module gives the
converse translation.

The host circuits are formulas (trees), while a `Circuit3` shares its bottom clauses among its
middle gates, so writing a `Circuit3` as a host circuit duplicates the shared clauses: the number
of gates grows from `b + m + 1` to at most `1 + m (b + 1)`, which is at most quadratic, and is not
linear in general for the tree form.  An exponential lower bound on the gates of one side
therefore transfers to the other with the exponent halved.

* `Complexity.DepthThreeHost.fromCircuit3` — the host circuit: an `OR` over the top gates of
  `AND`s over their bottom clauses, each clause an `OR` of literals and constants;
* `Complexity.ACCirc.gates` — the number of gates (`NOT`, `AND`, `OR` nodes) of a host circuit;
* **`Complexity.DepthThreeHost.fromCircuit3_eval`** — it computes the same function;
* **`Complexity.DepthThreeHost.fromCircuit3_isSigma3`** — it is `Σ₃`;
* **`Complexity.DepthThreeHost.fromCircuit3_gates`** — it has at most `gateCount ^ 2` gates;
* `Complexity.DepthThreeHost.toCircuit3_fromCircuit3_eval` — the round trip computes the same
  function.
-/

import Start.DepthThreeHost

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Complexity

namespace ACCirc

/-- The number of gates (`NOT`, `AND` and `OR` nodes) of a host circuit. -/
def gates : ACCirc → ℕ
  | .lit _ _ => 0
  | .const _ => 0
  | .not c => c.gates + 1
  | .and cs => (cs.attach.map (fun c => c.1.gates)).sum + 1
  | .or cs => (cs.attach.map (fun c => c.1.gates)).sum + 1
decreasing_by
  all_goals first
    | (simp only [ACCirc.not.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem (Subtype.property ‹Subtype _›)
       simp only [ACCirc.and.sizeOf_spec, ACCirc.or.sizeOf_spec]; omega)

theorem gates_and (cs : List ACCirc) : (and cs).gates = (cs.map gates).sum + 1 := by
  rw [gates, attach_map_sum cs gates]

theorem gates_or (cs : List ACCirc) : (or cs).gates = (cs.map gates).sum + 1 := by
  rw [gates, attach_map_sum cs gates]

end ACCirc

namespace DepthThreeHost

open DepthThreeLowerBound ACCirc

variable {n : ℕ}

/-- An upstream gate input as a host leaf. -/
def leafOf : GateInput (Fin n) → ACCirc
  | .inl l => .lit l.1 l.2
  | .inr b => .const b

/-- An upstream clause as a host `OR`. -/
def clauseOf (c : RawClause (Fin n)) : ACCirc := .or (c.map leafOf)

/-- **The host circuit of a `Circuit3`.** -/
def fromCircuit3 (C : Circuit3 (Fin n)) : ACCirc :=
  .or (C.top.toList.map fun j => .and ((C.middle j).toList.map fun i => clauseOf (C.bottom i)))

theorem leafOf_eval (g : GateInput (Fin n)) (x : Fin n → Bool) :
    (leafOf g).eval (List.ofFn x) = g.eval x := by
  rcases g with ⟨v, b⟩ | b
  · simp only [leafOf, eval_lit, GateInput.eval, Literal.eval]
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    cases x v <;> cases b <;> rfl
  · simp [leafOf, GateInput.eval]

/-- **The host circuit computes the function of the `Circuit3`.** -/
theorem fromCircuit3_eval (C : Circuit3 (Fin n)) (x : Fin n → Bool) :
    (fromCircuit3 C).eval (List.ofFn x) = C.eval x := by
  classical
  apply Bool.eq_iff_iff.2
  simp only [fromCircuit3, eval_or, eval_and, clauseOf, List.any_map, List.all_map,
    List.any_eq_true, List.all_eq_true, Finset.mem_toList, Function.comp_apply, leafOf_eval,
    Circuit3.eval, Circuit3.middleEval, RawClause.eval, decide_eq_true_eq]

theorem fromCircuit3_depth (C : Circuit3 (Fin n)) : (fromCircuit3 C).depth ≤ 3 := by
  simp only [fromCircuit3, depth_or, clauseOf]
  have h3 : lmax depth (C.top.toList.map fun j => ACCirc.and ((C.middle j).toList.map
      fun i => ACCirc.or ((C.bottom i).map leafOf))) ≤ 2 := by
    refine lmax_le _ fun a ha => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    rw [depth_and]
    have : lmax depth ((C.middle j).toList.map fun i => ACCirc.or ((C.bottom i).map leafOf))
        ≤ 1 := by
      refine lmax_le _ fun b hb => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
      rw [depth_or]
      have : lmax depth ((C.bottom i).map leafOf) ≤ 0 := by
        refine lmax_le _ fun c hc => ?_
        obtain ⟨g, -, rfl⟩ := List.mem_map.1 hc
        rcases g with ⟨v, b⟩ | b <;> simp [leafOf]
      omega
    omega
  omega

/-- **The host circuit is `Σ₃`.** -/
theorem fromCircuit3_isSigma3 (C : Circuit3 (Fin n)) : (fromCircuit3 C).IsSigma3 := by
  refine ⟨fromCircuit3_depth C, ?_⟩
  rw [fromCircuit3, nnf_or]
  trivial

theorem gates_clauseOf (c : RawClause (Fin n)) : (clauseOf c).gates = 1 := by
  have h0 : ((c.map leafOf).map gates).sum = 0 := List.sum_eq_zero fun x hx => by
    simp only [List.map_map, List.mem_map, Function.comp_apply] at hx
    obtain ⟨g, -, rfl⟩ := hx
    rcases g with ⟨v, b⟩ | b <;> simp [leafOf, gates]
  rw [clauseOf, gates_or, h0]

/-- **At most quadratically many gates.** -/
theorem fromCircuit3_gates (C : Circuit3 (Fin n)) :
    (fromCircuit3 C).gates ≤ C.gateCount ^ 2 := by
  classical
  have hmid : ∀ j, (ACCirc.and ((C.middle j).toList.map fun i => clauseOf (C.bottom i))).gates
      ≤ C.bottomCount + 1 := by
    intro j
    rw [gates_and, List.map_map]
    have : ((C.middle j).toList.map ((fun g => g.gates) ∘ fun i => clauseOf (C.bottom i))).sum
        = (C.middle j).card := by
      simp [Function.comp_def, gates_clauseOf]
    rw [this]
    have := Finset.card_le_univ (C.middle j)
    simp only [Fintype.card_fin] at this
    omega
  rw [fromCircuit3, gates_or, List.map_map]
  have hsum : ((C.top.toList.map ((fun g => g.gates) ∘ fun j => ACCirc.and
      ((C.middle j).toList.map fun i => clauseOf (C.bottom i))))).sum ≤
        C.top.card * (C.bottomCount + 1) := by
    rw [← Finset.length_toList C.top]
    refine (List.sum_le_card_nsmul _ (C.bottomCount + 1) fun a ha => ?_).trans
      (le_of_eq (by simp [smul_eq_mul]))
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact hmid j
  have htop := Finset.card_le_univ C.top
  simp only [Fintype.card_fin] at htop
  have : C.top.card * (C.bottomCount + 1) ≤ C.middleCount * (C.bottomCount + 1) :=
    Nat.mul_le_mul_right _ htop
  unfold Circuit3.gateCount
  nlinarith

/-- The round trip through the host circuits computes the same function. -/
theorem toCircuit3_fromCircuit3_eval (C : Circuit3 (Fin n)) (x : Fin n → Bool) :
    (toCircuit3 n (fromCircuit3 C)).eval x = C.eval x := by
  rw [toCircuit3_eval (fromCircuit3_isSigma3 C), fromCircuit3_eval]

end DepthThreeHost

end Complexity
