/-
**The absorbed depth-three lower bound, stated in the host circuit and complexity theory.**

Upstream (`Start/DepthThreeMain.lean`) gives a language `L`, decided in polynomial time by a
`FiniteMultiTapeMachine`, such that every OR-AND-OR depth-three circuit (`Circuit3`) computing `L`
on inputs of length `n` has more than `2^{A √n}` gates, for every `A > 0` and large `n`.  This
module transfers both halves to the host:

* the language is in the host class `InP` (Cobham's `P`), by
  `MultiTapeCobham.inP_of_multiTapeHaltsIn` (`Start/MultiTapeCobham.lean`);
* the circuits are the host's unbounded fan-in circuits `ACCirc` (`Start/AC0.lean`).  A host
  circuit is `Σ₃` (`ACCirc.IsSigma3`) when it has depth at most three and its negation normal form
  (`nnf true`, same function, same depth, no larger size) has an `OR`, a literal or a constant at
  the output.  Every `Σ₃` host circuit on `n` inputs is translated into an upstream `Circuit3` on
  `Fin n` computing the same function, with at most `2 · size + 1` gates
  (`DepthThreeHost.toCircuit3_eval`, `DepthThreeHost.toCircuit3_gateCount`).

Translation contract.  Basis: the host's literals `xᵢ`/`¬xᵢ` and constants (a literal with index
`i ≥ n` reads `false`, so it becomes a constant), and unbounded fan-in `AND`/`OR`; after `nnf` there
is no `NOT` gate.  The output `OR` of the host circuit (or of its `OR` children, which are merged
into it) becomes the top gate of the `Circuit3`; each remaining depth-two child becomes a middle
`AND` gate; each depth-one gate becomes a bottom clause (an `AND` of literals is split into unit
clauses).  Fan-in is not bounded on either side.  Depth: three on both sides.  Size: every bottom
clause and every middle gate is charged to a distinct node of the host tree.

Main results:

* `Complexity.DepthThreeHost.toCircuit3_eval`, `Complexity.DepthThreeHost.toCircuit3_gateCount`;
* `Complexity.DepthThreeHost.depthThree_lower_bound_host` — **a language in host `P` whose `Σ₃`
  host circuits on inputs of length `n` have size more than `2^{A √n}`**, for every `A > 0` and
  every large `n`.
-/

import Start.AC0
import Start.DepthThreeMain
import Start.MultiTapeCobham

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace ACCirc

/-- The output gate is an `OR`, a literal or a constant. -/
def IsTopShape : ACCirc → Prop
  | .or _ => True
  | .lit _ _ => True
  | .const _ => True
  | _ => False

/-- A host circuit is `Σ₃`: depth at most three, and its negation normal form has an `OR`, a
literal or a constant at the output. -/
def IsSigma3 (C : ACCirc) : Prop :=
  C.depth ≤ 3 ∧ IsTopShape (C.nnf true)

end ACCirc

namespace DepthThreeHost

open DepthThreeLowerBound ACCirc

/-! ### From host circuits to `Circuit3` -/

section Translation

variable (n : ℕ)

/-- A host literal on `n` inputs: an upstream literal, or the constant it reads beyond `n`. -/
def litIn (i : ℕ) (b : Bool) : GateInput (Fin n) :=
  if h : i < n then .inl (⟨i, h⟩, b) else .inr (!b)

/-- A leaf of a host circuit as an upstream gate input. -/
def toInput : ACCirc → GateInput (Fin n)
  | .lit i b => litIn n i b
  | .const b => .inr b
  | _ => .inr false

/-- A gate of depth at most one as a conjunction of clauses. -/
def clausesOf : ACCirc → List (RawClause (Fin n))
  | .and gs => gs.map fun g => [toInput n g]
  | .or gs => [gs.map (toInput n)]
  | c => [[toInput n c]]

/-- A gate of depth at most two, not an `OR` of depth two, as a conjunction of clauses. -/
def midOf : ACCirc → List (RawClause (Fin n))
  | .and gs => gs.flatMap (clausesOf n)
  | c => clausesOf n c

/-- A child of the output gate as a disjunction of middle gates. -/
def topChild : ACCirc → List (List (RawClause (Fin n)))
  | .or hs => hs.map (midOf n)
  | g => [midOf n g]

/-- A `Σ₃` circuit in negation normal form as a disjunction of middle gates. -/
def topOf : ACCirc → List (List (RawClause (Fin n)))
  | .or gs => gs.flatMap (topChild n)
  | c => [midOf n c]

end Translation

section Lists

variable {V : Type}

/-- The bottom clauses, each tagged with the index of its middle gate. -/
def pairsOf (ms : List (List (RawClause V))) : List (ℕ × RawClause V) :=
  (List.range ms.length).flatMap fun j => (ms.getD j []).map fun c => (j, c)

/-- The `Circuit3` with one middle gate for each list of clauses. -/
noncomputable def ofLists (ms : List (List (RawClause V))) : Circuit3 V where
  bottomCount := (pairsOf ms).length
  middleCount := ms.length
  bottom i := ((pairsOf ms)[i]).2
  middle j := Finset.univ.filter fun i => ((pairsOf ms)[i]).1 = j.val
  top := Finset.univ

theorem mem_pairsOf (ms : List (List (RawClause V))) (j : ℕ) (c : RawClause V) :
    (j, c) ∈ pairsOf ms ↔ j < ms.length ∧ c ∈ ms.getD j [] := by
  simp [pairsOf]

theorem length_pairsOf (ms : List (List (RawClause V))) :
    (pairsOf ms).length = (ms.map List.length).sum := by
  unfold pairsOf
  rw [List.length_flatMap]
  simp only [List.length_map]
  have : ∀ l : List (List (RawClause V)),
      ((List.range l.length).map fun j => (l.getD j []).length) = l.map List.length := by
    intro l
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [List.getD_eq_getElem]
  rw [this]

theorem circuit3_eval_iff (C : Circuit3 V) (x : Cube V) :
    C.eval x = true ↔ ∃ j ∈ C.top, C.middleEval j x = true := by
  unfold Circuit3.eval
  simp

theorem middleEval_iff (C : Circuit3 V) (j : Fin C.middleCount) (x : Cube V) :
    C.middleEval j x = true ↔ ∀ i ∈ C.middle j, (C.bottom i).eval x = true := by
  unfold Circuit3.middleEval
  simp

theorem eval_ofLists (ms : List (List (RawClause V))) (f : Cube V) :
    (ofLists ms).eval f = true ↔ ∃ m ∈ ms, ∀ c ∈ m, RawClause.eval c f = true := by
  rw [circuit3_eval_iff]
  simp only [middleEval_iff, ofLists, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨j, -, hj⟩
    refine ⟨ms[j.val], List.getElem_mem _, fun c hc => ?_⟩
    have hmem : (j.val, c) ∈ pairsOf ms := (mem_pairsOf ms j c).mpr
      ⟨j.2, by rw [List.getD_eq_getElem]; exact hc⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
    have := hj ⟨i, hi⟩ (by simp [he])
    simpa [he] using this
  · rintro ⟨m, hm, hall⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨j, hj⟩, Finset.mem_univ _, fun i hi => ?_⟩
    have hp : (pairsOf ms)[i.val] ∈ pairsOf ms := List.getElem_mem _
    have hp' : ((pairsOf ms)[i.val].1, (pairsOf ms)[i.val].2) ∈ pairsOf ms := hp
    rw [mem_pairsOf] at hp'
    have h2 := hp'.2
    rw [show (pairsOf ms)[i.val].1 = j from hi, List.getD_eq_getElem _ _ hj] at h2
    exact hall _ h2

theorem gateCount_ofLists (ms : List (List (RawClause V))) :
    (ofLists ms).gateCount = (ms.map fun m => m.length + 1).sum + 1 := by
  simp only [Circuit3.gateCount, ofLists, length_pairsOf]
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

end Lists

/-! ### Semantics of the translation -/

section Semantics

variable {n : ℕ} (f : Fin n → Bool)

theorem eval_litIn (i : ℕ) (b : Bool) :
    GateInput.eval (litIn n i b) f = ((List.ofFn f).getD i false == b) := by
  unfold litIn
  split
  · rename_i h
    simp only [GateInput.eval, Literal.eval]
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    cases f ⟨i, h⟩ <;> cases b <;> rfl
  · rename_i h
    simp only [GateInput.eval]
    rw [List.getD_eq_default _ _ (by simp; omega)]
    cases b <;> rfl

theorem noNot_and {gs : List ACCirc} (h : NoNot (.and gs)) : ∀ g ∈ gs, NoNot g := by
  rw [NoNot] at h; exact h

theorem noNot_or {gs : List ACCirc} (h : NoNot (.or gs)) : ∀ g ∈ gs, NoNot g := by
  rw [NoNot] at h; exact h

theorem eval_toInput {c : ACCirc} (hnn : NoNot c) (hd : c.depth = 0) :
    GateInput.eval (toInput n c) f = c.eval (List.ofFn f) := by
  cases c with
  | lit i b => simp [toInput, eval_litIn]
  | const b => simp [toInput, GateInput.eval]
  | not c => rw [NoNot] at hnn; exact hnn.elim
  | and gs => simp at hd
  | or gs => simp at hd

theorem rawClause_eval_iff (C : RawClause (Fin n)) :
    RawClause.eval C f = true ↔ ∃ l ∈ C, GateInput.eval l f = true := by
  simp [RawClause.eval]

theorem depth_le_of_mem {gs : List ACCirc} {g : ACCirc} (hg : g ∈ gs) :
    g.depth ≤ lmax depth gs := le_lmax depth hg

theorem clauses_eval {c : ACCirc} (hnn : NoNot c) (hd : c.depth ≤ 1) :
    (∀ cl ∈ clausesOf n c, RawClause.eval cl f = true) ↔ c.eval (List.ofFn f) = true := by
  cases c with
  | lit i b =>
    simp only [clausesOf, List.mem_singleton, forall_eq, rawClause_eval_iff, exists_eq_left,
      toInput]
    rw [eval_litIn, eval_lit]
  | const b =>
    simp only [clausesOf, List.mem_singleton, forall_eq, rawClause_eval_iff, exists_eq_left,
      toInput]
    simp [GateInput.eval]
  | not c => rw [NoNot] at hnn; exact hnn.elim
  | and gs =>
    simp only [depth_and] at hd
    have h0 : ∀ g ∈ gs, g.depth = 0 := fun g hg => by
      have := depth_le_of_mem hg; omega
    simp only [clausesOf, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      rawClause_eval_iff, List.mem_singleton, exists_eq_left, eval_and, List.all_eq_true]
    constructor
    · intro h g hg
      rw [← eval_toInput f (noNot_and hnn g hg) (h0 g hg)]
      exact h g hg
    · intro h g hg
      rw [eval_toInput f (noNot_and hnn g hg) (h0 g hg)]
      exact h g hg
  | or gs =>
    simp only [depth_or] at hd
    have h0 : ∀ g ∈ gs, g.depth = 0 := fun g hg => by
      have := depth_le_of_mem hg; omega
    simp only [clausesOf, List.mem_singleton, forall_eq, rawClause_eval_iff, List.mem_map,
      exists_exists_and_eq_and, eval_or, List.any_eq_true]
    constructor
    · rintro ⟨g, hg, h⟩
      exact ⟨g, hg, by rw [← eval_toInput f (noNot_or hnn g hg) (h0 g hg)]; exact h⟩
    · rintro ⟨g, hg, h⟩
      exact ⟨g, hg, by rw [eval_toInput f (noNot_or hnn g hg) (h0 g hg)]; exact h⟩

theorem mid_eval {c : ACCirc} (hnn : NoNot c) (hd : c.depth ≤ 2)
    (hor : ∀ gs, c = .or gs → c.depth ≤ 1) :
    (∀ cl ∈ midOf n c, RawClause.eval cl f = true) ↔ c.eval (List.ofFn f) = true := by
  cases c with
  | and gs =>
    simp only [depth_and] at hd
    simp only [midOf, List.mem_flatMap, forall_exists_index, and_imp, eval_and,
      List.all_eq_true]
    constructor
    · intro h g hg
      exact (clauses_eval f (noNot_and hnn g hg) (by have := depth_le_of_mem hg; omega)).mp
        (fun cl hcl => h cl g hg hcl)
    · intro h cl g hg hcl
      exact (clauses_eval f (noNot_and hnn g hg) (by have := depth_le_of_mem hg; omega)).mpr (h g hg) cl hcl
  | or gs => exact clauses_eval f hnn (hor gs rfl)
  | lit i b => exact clauses_eval f hnn (by simp)
  | const b => exact clauses_eval f hnn (by simp)
  | not c => rw [NoNot] at hnn; exact hnn.elim

theorem topChild_eval {g : ACCirc} (hnn : NoNot g) (hd : g.depth ≤ 2) :
    (∃ m ∈ topChild n g, ∀ cl ∈ m, RawClause.eval cl f = true) ↔
      g.eval (List.ofFn f) = true := by
  cases g with
  | or hs =>
    simp only [depth_or] at hd
    simp only [topChild, List.mem_map, exists_exists_and_eq_and, eval_or, List.any_eq_true]
    constructor
    · rintro ⟨h, hh, hall⟩
      exact ⟨h, hh, (mid_eval f (noNot_or hnn h hh) (by have := depth_le_of_mem hh; omega)
        (fun _ _ => by have := depth_le_of_mem hh; omega)).mp hall⟩
    · rintro ⟨h, hh, hev⟩
      exact ⟨h, hh, (mid_eval f (noNot_or hnn h hh) (by have := depth_le_of_mem hh; omega)
        (fun _ _ => by have := depth_le_of_mem hh; omega)).mpr hev⟩
  | and gs =>
    simp only [topChild, List.mem_singleton, exists_eq_left]
    exact mid_eval f hnn hd (fun _ h => by cases h)
  | lit i b =>
    simp only [topChild, List.mem_singleton, exists_eq_left]
    exact mid_eval f hnn hd (fun _ h => by cases h)
  | const b =>
    simp only [topChild, List.mem_singleton, exists_eq_left]
    exact mid_eval f hnn hd (fun _ h => by cases h)
  | not c => rw [NoNot] at hnn; exact hnn.elim

theorem topOf_eval {c : ACCirc} (hnn : NoNot c) (hd : c.depth ≤ 3)
    (htop : IsTopShape c) :
    (∃ m ∈ topOf n c, ∀ cl ∈ m, RawClause.eval cl f = true) ↔ c.eval (List.ofFn f) = true := by
  cases c with
  | or gs =>
    simp only [depth_or] at hd
    simp only [topOf, List.mem_flatMap, eval_or, List.any_eq_true]
    constructor
    · rintro ⟨m, ⟨g, hg, hm⟩, hall⟩
      exact ⟨g, hg, (topChild_eval f (noNot_or hnn g hg) (by have := depth_le_of_mem hg; omega)).mp
        ⟨m, hm, hall⟩⟩
    · rintro ⟨g, hg, hev⟩
      obtain ⟨m, hm, hall⟩ :=
        (topChild_eval f (noNot_or hnn g hg) (by have := depth_le_of_mem hg; omega)).mpr hev
      exact ⟨m, ⟨g, hg, hm⟩, hall⟩
  | lit i b =>
    simp only [topOf, List.mem_singleton, exists_eq_left]
    exact mid_eval f hnn (by simp) (fun _ h => by cases h)
  | const b =>
    simp only [topOf, List.mem_singleton, exists_eq_left]
    exact mid_eval f hnn (by simp) (fun _ h => by cases h)
  | and gs => simp [IsTopShape] at htop
  | not c => simp [IsTopShape] at htop

end Semantics

/-! ### Size of the translation -/

section Size

variable (n : ℕ)

theorem one_le_size (c : ACCirc) : 1 ≤ c.size := by
  cases c <;> simp

theorem length_le_sum_size (gs : List ACCirc) : gs.length ≤ (gs.map size).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have := one_le_size g
    omega

theorem length_clausesOf_le (c : ACCirc) : (clausesOf n c).length ≤ c.size := by
  cases c with
  | and gs =>
    simp only [clausesOf, List.length_map, size_and]
    have := length_le_sum_size gs
    omega
  | or gs => simp [clausesOf]
  | lit i b => simp [clausesOf]
  | const b => simp [clausesOf]
  | not c => simp [clausesOf]

theorem sum_le_sum_size {gs : List ACCirc} {F : ACCirc → ℕ} (h : ∀ g ∈ gs, F g ≤ g.size) :
    (gs.map F).sum ≤ (gs.map size).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h g (by simp)) (ih fun g' hg' => h g' (by simp [hg']))

theorem length_midOf_le (c : ACCirc) : (midOf n c).length ≤ c.size := by
  cases c with
  | and gs =>
    simp only [midOf, List.length_flatMap, size_and]
    have := sum_le_sum_size (gs := gs) (F := fun g => (clausesOf n g).length)
      (fun g _ => length_clausesOf_le n g)
    omega
  | or gs => simpa only [midOf] using length_clausesOf_le n (.or gs)
  | lit i b => simpa only [midOf] using length_clausesOf_le n (.lit i b)
  | const b => simpa only [midOf] using length_clausesOf_le n (.const b)
  | not c => simpa only [midOf] using length_clausesOf_le n (.not c)

/-- The cost of a list of middle gates: clauses plus gates. -/
def cost {V : Type} (ms : List (List (RawClause V))) : ℕ := (ms.map fun m => m.length + 1).sum

theorem cost_append {V : Type} (ms ms' : List (List (RawClause V))) :
    cost (ms ++ ms') = cost ms + cost ms' := by
  simp [cost]

theorem cost_flatMap {V : Type} (gs : List ACCirc) (F : ACCirc → List (List (RawClause V))) :
    cost (gs.flatMap F) = (gs.map fun g => cost (F g)).sum := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.flatMap_cons, cost_append, ih]
    simp

theorem cost_midOf_le (c : ACCirc) : cost [midOf n c] ≤ 2 * c.size := by
  simp only [cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have := length_midOf_le n c
  have := one_le_size c
  omega

theorem sum_cost_le {V : Type} (gs : List ACCirc) (F : ACCirc → List (List (RawClause V)))
    (hF : ∀ g ∈ gs, cost (F g) ≤ 2 * g.size) :
    (gs.map fun g => cost (F g)).sum ≤ 2 * (gs.map size).sum := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := hF g (by simp)
    have h2 := ih fun g' hg' => hF g' (by simp [hg'])
    omega

theorem cost_topChild_le (g : ACCirc) : cost (topChild n g) ≤ 2 * g.size := by
  cases g with
  | or hs =>
    simp only [topChild, size_or]
    have : cost (hs.map (midOf n)) = (hs.map fun h => cost [midOf n h]).sum := by
      simp [cost, List.map_map, Function.comp_def]
    rw [this]
    have := sum_cost_le hs (fun h => [midOf n h]) (fun h _ => cost_midOf_le n h)
    omega
  | and gs => simpa only [topChild] using cost_midOf_le n (.and gs)
  | lit i b => simpa only [topChild] using cost_midOf_le n (.lit i b)
  | const b => simpa only [topChild] using cost_midOf_le n (.const b)
  | not c => simpa only [topChild] using cost_midOf_le n (.not c)

theorem cost_topOf_le (c : ACCirc) : cost (topOf n c) ≤ 2 * c.size := by
  cases c with
  | or gs =>
    simp only [topOf, size_or]
    rw [cost_flatMap]
    have := sum_cost_le gs (topChild n) (fun g _ => cost_topChild_le n g)
    omega
  | and gs => simpa only [topOf] using cost_midOf_le n (.and gs)
  | lit i b => simpa only [topOf] using cost_midOf_le n (.lit i b)
  | const b => simpa only [topOf] using cost_midOf_le n (.const b)
  | not c => simpa only [topOf] using cost_midOf_le n (.not c)

end Size

/-! ### The translation -/

/-- **The upstream circuit of a host `Σ₃` circuit on `n` inputs.** -/
noncomputable def toCircuit3 (n : ℕ) (C : ACCirc) : Circuit3 (Fin n) :=
  ofLists (topOf n (C.nnf true))

theorem toCircuit3_eval {n : ℕ} {C : ACCirc} (hC : C.IsSigma3) (f : Fin n → Bool) :
    (toCircuit3 n C).eval f = C.eval (List.ofFn f) := by
  have hiff := topOf_eval f (noNot_nnf C true) (by rw [depth_nnf]; exact hC.1) hC.2
  rw [eval_nnf] at hiff
  have h := (eval_ofLists (topOf n (C.nnf true)) f).trans hiff
  rw [toCircuit3]
  cases h1 : (ofLists (topOf n (C.nnf true))).eval f <;>
    cases h2 : C.eval (List.ofFn f) <;> simp_all

theorem toCircuit3_gateCount (n : ℕ) (C : ACCirc) :
    (toCircuit3 n C).gateCount ≤ 2 * C.size + 1 := by
  rw [toCircuit3, gateCount_ofLists]
  have h1 := cost_topOf_le n (C.nnf true)
  have h2 := size_nnf C true
  unfold cost at h1
  omega

/-! ### The lower bound in the host -/

/-- **The depth-three lower bound in the host theory**: some language in host `P` (Cobham's
class) needs `Σ₃` host circuits of size more than `2^{A √n}` on inputs of length `n`, for every
`A > 0` and every large `n`. -/
theorem depthThree_lower_bound_host :
    ∃ L : Language, InP L ∧ ∀ A : ℝ, 0 < A → ∃ N : ℕ, ∀ n, N ≤ n → ∀ C : ACCirc, C.IsSigma3 →
      (∀ x : Word, x.length = n → (C.eval x = true ↔ L x)) →
        (2 : ℝ) ^ (A * Real.sqrt n) < C.size := by
  obtain ⟨L0, M, Cc, a, -, -, hM, hlb⟩ := exists_polynomial_time_language_depth_three_lower_bound
  refine ⟨fun x => L0 x = true, ?_, ?_⟩
  · exact MultiTapeCobham.inP_of_multiTapeHaltsIn M _ (fun n => Cc * (n + 1) ^ a)
      ⟨Cc, a, fun _ => le_rfl⟩ (fun x => ⟨L0 x, hM x, Iff.rfl⟩)
  · intro A hA
    obtain ⟨N, hN⟩ := hlb (A + 2) (by linarith)
    refine ⟨max N 1, fun n hn C hC hcomp => ?_⟩
    have hD : (toCircuit3 n C).Computes (fun x => L0 (List.ofFn x)) := by
      intro f
      rw [toCircuit3_eval hC f]
      have := hcomp (List.ofFn f) (by simp)
      cases h1 : C.eval (List.ofFn f) <;> cases h2 : L0 (List.ofFn f) <;> simp_all
    have hgt := hN n (le_of_max_le_left hn) (toCircuit3 n C) hD
    have hcount : ((toCircuit3 n C).gateCount : ℝ) ≤ 2 * (C.size : ℝ) + 1 := by
      exact_mod_cast toCircuit3_gateCount n C
    have hsize : (1 : ℝ) ≤ C.size := by exact_mod_cast one_le_size C
    have hn1 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]
      exact_mod_cast le_of_max_le_right hn
    have hsplit : (2 : ℝ) ^ ((A + 2) * Real.sqrt n) =
        (2 : ℝ) ^ (A * Real.sqrt n) * (2 : ℝ) ^ (2 * Real.sqrt n) := by
      rw [← Real.rpow_add (by norm_num)]
      ring_nf
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (2 * Real.sqrt n) := by
      have : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ (2 * Real.sqrt n) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
      linarith
    have hX : 0 < (2 : ℝ) ^ (A * Real.sqrt n) := Real.rpow_pos_of_pos (by norm_num) _
    rw [hsplit] at hgt
    nlinarith

end DepthThreeHost

end Complexity
