/-
# Flat layers, and the compiler's rule for the successors

A circuit whose gates are all constants or circuit inputs — a **flat layer** — realizes a word
function whenever the value of its gate `c` is the `c`-th wire of the output signal.  This module
collects that rule, and applies it to the successors `x ↦ b :: x` of the Cobham algebra: prepending
a bit to a signal is a shift of the presence and value blocks by one place, so the gate `c` reads
the wire `c - 1` of the argument, except at the two places where a constant is written.

Main definitions:

* `Complexity.Tseitin.flatGate` — a gate that reads no other gate.

Main results:

* `Complexity.sigUniform_of_flatLayer` — **a flat layer whose gates are written by a Cobham term
  realizes the function its values describe**;
* `Complexity.sigUniform_app` — **the successors are realized**, at every width.
-/

import Start.UniformSigComp

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Flat layers -/

/-- A gate that reads no other gate: a circuit input or a constant. -/
def flatGate : Gate → Prop
  | .inp _ => True
  | .cst _ => True
  | _ => False

theorem gateVal_flat {g : Gate} (h : flatGate g) (x : Word) (vs vs' : List Bool) :
    gateVal x vs g = gateVal x vs' g := by
  cases g with
  | inp i => rfl
  | cst b => rfl
  | neg r => exact absurd h (by simp [flatGate])
  | conj r s => exact absurd h (by simp [flatGate])
  | disj r s => exact absurd h (by simp [flatGate])

theorem gateWf_flat {g : Gate} (h : flatGate g) (j : ℕ) : gateWf j g := by
  cases g with
  | inp i => exact trivial
  | cst b => exact trivial
  | neg r => exact absurd h (by simp [flatGate])
  | conj r s => exact absurd h (by simp [flatGate])
  | disj r s => exact absurd h (by simp [flatGate])

/-- A layer of flat gates is well formed. -/
theorem wf_layer_of_flat {tmpl : ℕ → Gate} (h : ∀ c, flatGate (tmpl c)) (k : ℕ) :
    wf (CircCode.layer tmpl k) := by
  induction k with
  | zero => exact trivial
  | succ k ih => exact ⟨gateWf_flat (h k) _, ih⟩

/-- The inputs read by a layer of flat gates are the ones its gates read. -/
theorem inpsLt_layer_of_flat {tmpl : ℕ → Gate} {w : ℕ} (k : ℕ)
    (h : ∀ c, c < k → inpLt w (tmpl c)) : inpsLt w (CircCode.layer tmpl k) := by
  induction k with
  | zero => intro g hg; cases hg
  | succ k ih =>
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact h k (Nat.lt_succ_self k)
      · exact ih (fun c hc => h c (Nat.lt_succ_of_lt hc)) g hg'

/-- **The values of a layer of flat gates.** -/
theorem vals_layer_of_flat (x : Word) {tmpl : ℕ → Gate} (h : ∀ c, flatGate (tmpl c)) (k : ℕ) :
    vals x (CircCode.layer tmpl k) = (List.range k).map (fun c => gateVal x [] (tmpl c)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [CircCode.layer, vals, ih, List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [gateVal_flat (h k) x (List.map (fun c => gateVal x [] (tmpl c)) (List.range k)) []]

end Tseitin

open Complexity.Tseitin

/-- **A flat layer written by a Cobham term realizes the function its values describe.** -/
theorem sigUniform_of_flatLayer {r : ℕ} {m : ℕ → ℕ} {F : List Word → Word}
    {tmpl : ℕ → ℕ → Tseitin.Gate} {mT blkT : Cob} {K : ℕ}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hflat : ∀ n c, Tseitin.flatGate (tmpl n c))
    (hinp : ∀ n c, c < 2 * m n → Tseitin.inpLt (r * (2 * m n)) (tmpl n c))
    (hblk : ∀ (n : ℕ) (y : Word) (c : ℕ),
      blkT.eval [y, List.replicate c true, dmW n (2 * m n)] = CircCode.encGate (tmpl n c))
    (hbndT : ∀ n c l : ℕ, c ≤ l →
      (CircCode.encGate (tmpl n c)).length ≤ K * (l + (dmW n (2 * m n)).length + 1))
    (hval : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
      (List.range (2 * m n)).map (fun c => Tseitin.gateVal (encArgs (m n) args) [] (tmpl n c))
        = encSig (m n) (F args)) :
    SigUniform r m F := by
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  refine ⟨fun n => CircCode.layer (tmpl n) (2 * m n), ?_⟩
  refine ⟨fun n => Tseitin.wf_layer_of_flat (hflat n) _,
    fun n => Tseitin.inpsLt_layer_of_flat _ (hinp n), fun n => by simp, ?_, ?_⟩
  · refine codeUniform_layerP (K := K) (cnt := twoT)
      (padT := Cob.catL [.comp .smash [Cob.proj 0, Cob.constT [true]], Cob.constT [false], twoT])
      (pw := fun n => dmW n (2 * m n)) (blkT := blkT) (tmpl := tmpl) htwo ?_ hblk hbndT
    intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_constT, Cob.eval_comp, Cob.eval_smash, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, htwo x]
    simp [dmW]
  · intro n args hlen hle
    rw [Tseitin.vals_layer_of_flat _ (hflat n), Tseitin.topVals]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.drop_zero]
    exact hval n args hlen hle

/-! ### Reading a signal off the input word -/

theorem getD_encSig_lt {m j : ℕ} (u : Word) (hj : j < m) :
    (encSig m u).getD j false = decide (j < u.length) := by
  rw [encSig, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simpa using hj), ← List.getD_eq_getElem?_getD]
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

theorem getD_encSig_ge {m j : ℕ} (u : Word) (h1 : m ≤ j) (h2 : j < 2 * m) :
    (encSig m u).getD j false = u.getD (j - m) false := by
  rw [encSig, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simpa using h1), ← List.getD_eq_getElem?_getD]
  simp only [List.length_map, List.length_range]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]

/-- Reading a wire of the first argument off the input word, whether or not there is one. -/
theorem getD_encArgs_zero (m : ℕ) (args : List Word) {j : ℕ} (hj : j < 2 * m) :
    (encArgs m args).getD j false = (encSig m (args.getD 0 [])).getD j false := by
  cases args with
  | nil =>
      simp only [encArgs, List.map_nil, List.flatten_nil, List.getD_nil]
      rcases lt_or_ge j m with h | h
      · rw [getD_encSig_lt _ h]
        simp
      · rw [getD_encSig_ge _ h hj]
        simp
  | cons u us =>
      have h := getD_encArgs m (u :: us) (i := 0) (j := j) (by simp) hj
      simpa using h

/-- The conditional term evaluates as a conditional on whether its guard is empty. -/
theorem eval_iteT_eval (c s t : Cob) (args : List Word) :
    (Cob.iteT c s t).eval args = if c.eval args = [] then t.eval args else s.eval args := by
  simp [Cob.iteT]

/-! ### The successors -/

/-- The gate of the layer for `x ↦ b :: x`: the wire `0` of each block is a constant, and every
other wire is the wire below it in the argument. -/
def appTmpl (b : Bool) (m c : ℕ) : Tseitin.Gate :=
  if c = 0 then .cst true else if c = m then .cst b else .inp (c - 1)

/-- **The successors are realized**: prepending a bit shifts both blocks of the signal by one
place. -/
theorem sigUniform_app {r : ℕ} {b : Bool} {m : ℕ → ℕ} {mT : Cob} (hr : 0 < r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => b :: args.getD 0 []) := by
  classical
  -- the Cobham term writing the gate
  set cc : Cob := Cob.proj 1 with hcc
  set nT : Cob := .comp Cob.leadOnes [Cob.proj 2] with hnT
  set mm : Cob := .comp mT [nT] with hmm
  set neq : Cob := .comp Cob.concat [.comp Cob.dropU [mm, cc], .comp Cob.dropU [cc, mm]] with hneq
  set blkT : Cob :=
    Cob.iteT cc (Cob.iteT neq (CircCode.tokTerm 1 (.comp Cob.tail [cc]) .empty)
      (CircCode.tokTerm (if b then 3 else 2) .empty .empty))
      (CircCode.tokTerm 3 .empty .empty) with hblkT
  have hccn : ∀ (n c : ℕ) (y : Word),
      cc.eval [y, List.replicate c true, dmW n (2 * m n)] = List.replicate c true := by
    intro n c y; simp [hcc]
  have hmmn : ∀ (n c : ℕ) (y : Word),
      mm.eval [y, List.replicate c true, dmW n (2 * m n)] = List.replicate (m n) true := by
    intro n c y
    have hlead : nT.eval [y, List.replicate c true, dmW n (2 * m n)] = List.replicate n true := by
      simp only [hnT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes,
        Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero]
      rw [lead1_dmW]
    simp only [hmm, Cob.eval_comp, List.map_cons, List.map_nil, hlead]
    rw [hm (List.replicate n true), List.length_replicate]
  have hneqn : ∀ (n c : ℕ) (y : Word),
      (neq.eval [y, List.replicate c true, dmW n (2 * m n)] = []) ↔ c = m n := by
    intro n c y
    simp only [hneq, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
      Cob.eval_dropU, hccn n c y, hmmn n c y,
      List.length_replicate, List.drop_replicate, List.append_eq_nil_iff,
      List.replicate_eq_nil_iff]
    omega
  refine sigUniform_of_flatLayer (K := 11) (tmpl := fun n c => appTmpl b (m n) c) (blkT := blkT)
    hm ?_ ?_ ?_ ?_ ?_
  · intro n c
    simp only [appTmpl]
    split_ifs <;> exact trivial
  · intro n c hc
    simp only [appTmpl]
    split_ifs with h1 h2
    · exact trivial
    · exact trivial
    · change c - 1 < r * (2 * m n)
      have hmul : 1 * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hr
      rw [Nat.one_mul] at hmul
      omega
  · intro n y c
    simp only [hblkT, eval_iteT_eval, hccn n c y]
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [if_pos (show List.replicate 0 true = ([] : Word) from rfl)]
      have ht := CircCode.eval_tokTerm (g := Tseitin.Gate.cst true)
        (aT := (.empty : Cob)) (bT := (.empty : Cob))
        (args := [y, List.replicate 0 true, dmW n (2 * m n)])
        (by simp [CircCode.fld1]) (by simp [CircCode.fld2])
      rw [show CircCode.tag (Tseitin.Gate.cst true) = 3 from rfl] at ht
      rw [ht]
      simp [appTmpl]
    · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega)]
      by_cases hcm : c = m n
      · rw [if_pos ((hneqn n c y).2 hcm)]
        have ht := CircCode.eval_tokTerm (g := Tseitin.Gate.cst b)
          (aT := (.empty : Cob)) (bT := (.empty : Cob))
          (args := [y, List.replicate c true, dmW n (2 * m n)])
          (by simp [CircCode.fld1]) (by simp [CircCode.fld2])
        rw [show CircCode.tag (Tseitin.Gate.cst b) = (if b then 3 else 2) by
          cases b <;> rfl] at ht
        rw [ht]
        simp only [appTmpl, if_neg (show ¬ c = 0 by omega), if_pos hcm]
      · rw [if_neg (fun h => hcm ((hneqn n c y).1 h))]
        have htail : (Cob.comp Cob.tail [cc]).eval [y, List.replicate c true, dmW n (2 * m n)]
            = List.replicate (c - 1) true := by
          simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_tail, hccn n c y,
            List.tail_replicate]
        have ht := CircCode.eval_tokTerm (g := Tseitin.Gate.inp (c - 1))
          (aT := (.comp Cob.tail [cc])) (bT := (.empty : Cob))
          (args := [y, List.replicate c true, dmW n (2 * m n)])
          (by rw [htail]; rfl) (by simp [CircCode.fld2])
        rw [show CircCode.tag (Tseitin.Gate.inp (c - 1)) = 1 from rfl] at ht
        rw [ht]
        simp only [appTmpl, if_neg (show ¬ c = 0 by omega), if_neg hcm]
  · intro n c l hc
    rw [CircCode.length_encGate]
    simp only [appTmpl]
    split_ifs <;> cases b <;>
      simp only [CircCode.tag, CircCode.fld1, CircCode.fld2, length_dmW] <;> omega
  · intro n args hlen hle
    set u : Word := args.getD 0 [] with hu
    refine List.ext_getElem (by simp) ?_
    intro j h1 h2
    have hj : j < 2 * m n := by simpa using h1
    have hrhs : (encSig (m n) (b :: u))[j]
        = (encSig (m n) (b :: u)).getD j false :=
      (List.getD_eq_getElem _ _ (by simpa using h2)).symm
    simp only [List.getElem_map, List.getElem_range, hrhs, appTmpl]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hm0 : 0 < m n := by omega
      rw [if_pos rfl, getD_encSig_lt _ hm0]
      simp [Tseitin.gateVal]
    · rw [if_neg (by omega)]
      by_cases hjm : j = m n
      · rw [if_pos hjm, getD_encSig_ge _ (by omega) hj, hjm]
        simp [Tseitin.gateVal]
      · rw [if_neg hjm]
        have hval : Tseitin.gateVal (encArgs (m n) args) [] (Tseitin.Gate.inp (j - 1))
            = (encArgs (m n) args).getD (j - 1) false := rfl
        rw [hval, getD_encArgs_zero (m n) args (by omega), ← hu]
        rcases lt_or_ge j (m n) with hlt | hge
        · rw [getD_encSig_lt _ (by omega), getD_encSig_lt _ hlt]
          simp only [List.length_cons, decide_eq_decide]
          omega
        · rw [getD_encSig_ge _ (by omega) (by omega), getD_encSig_ge _ hge hj]
          have hjm1 : j - 1 - m n = j - m n - 1 := by omega
          have hpos : 0 < j - m n := by omega
          rw [hjm1]
          cases hk : j - m n with
          | zero => omega
          | succ k => simp

end Complexity
