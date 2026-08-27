/-
**A nontrivial P-uniform circuit family, assembled from the algebra.**

`Start/UniformCircuit.lean` gives three closure properties of `Complexity.CodeUniform`: constants,
concatenation, and layers.  This module puts them to work on a family that actually computes
something: `Complexity.CircCode.andCirc n` is the conjunction of the first `n` bits of the circuit
input, written as two layers — `n` input gates at the bottom, and above them `n` conjunction gates
accumulating the running conjunction.

Both the *semantics* and the *uniformity* of the family are proved: the output of `andCirc n` is
the conjunction of the first `n` input bits, and a single Cobham term writes the description of
`andCirc n` from any word of length `n`.  It is, in other words, a P-uniform family of circuits of
linear size deciding a nontrivial language.

Main definitions:

* `Complexity.CircCode.inpTmpl`, `Complexity.CircCode.andTmpl` — the two templates;
* `Complexity.CircCode.andCirc` — the family;
* `Complexity.CircCode.andPrefix` — the conjunction of the first bits of a word.

Main results:

* `Complexity.CircCode.wf_andCirc` — the circuits are well formed;
* `Complexity.CircCode.out_andCirc` — **they compute the conjunction of the first `n` input bits**;
* `Complexity.codeUniform_andCirc` — **their descriptions are written by a single Cobham term.**

The family is then put together with the chain of negations of `Start/CodeUniformExample.lean` in
the two ways supplied by `Start/UniformShift.lean` and `Start/UniformCompose.lean`: side by side
(`Complexity.CircCode.andOverNeg`) and one feeding the other
(`Complexity.CircCode.andAfterNeg`).  Both composites are well formed, both have a proved output,
and both are P-uniform.
-/

import Start.UniformCompose

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The two layers -/

/-- The bottom layer: the gate with identifier `c` reads the input bit `c`. -/
def inpTmpl (c : ℕ) : Gate := .inp c

/-- The top layer of a circuit with `n` input gates below it: the gate with identifier `n + c`
conjoins the running conjunction `n + c - 1` with the input gate `c`. -/
def andTmpl (n c : ℕ) : Gate := if c = 0 then .conj 0 0 else .conj (n + c - 1) c

/-- The conjunction of the first `n` bits of the circuit input, as two layers. -/
def andCirc (n : ℕ) : Circuit := layer (andTmpl n) n ++ layer inpTmpl n

@[simp] theorem length_andCirc (n : ℕ) : (andCirc n).length = n + n := by
  simp [andCirc]

/-! ### Well-formedness -/

theorem wf_layer_inp (m : ℕ) : wf (layer inpTmpl m) := by
  induction m with
  | zero => trivial
  | succ m ih => exact ⟨trivial, ih⟩

theorem wf_layer_and (n : ℕ) (hn : 0 < n) : ∀ k, wf (layer (andTmpl n) k ++ layer inpTmpl n) := by
  intro k
  induction k with
  | zero => exact wf_layer_inp n
  | succ k ih =>
      refine ⟨?_, ih⟩
      have hg : gateWf (k + n) (andTmpl n k) := by
        rw [andTmpl]
        split_ifs with h
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
      simpa using hg

theorem wf_andCirc (n : ℕ) (hn : 0 < n) : wf (andCirc n) := wf_layer_and n hn n

/-! ### Semantics -/

/-- The conjunction of the bits `0, …, j` of a word. -/
def andPrefix (x : Word) : ℕ → Bool
  | 0 => x.getD 0 false
  | j + 1 => andPrefix x j && x.getD (j + 1) false

theorem wval_layer_inp (x : Word) : ∀ (m i : ℕ), i < m →
    wval (layer inpTmpl m) i x = x.getD i false := by
  intro m
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
      intro i hi
      rcases Nat.lt_or_ge i m with h | h
      · rw [layer, wval, vals_cons_getD_lt x _ _ (by simpa using h)]
        exact ih i h
      · have hi' : i = m := by omega
        subst hi'
        have h := vals_cons_getD_length x (inpTmpl i) (layer inpTmpl i)
        rw [length_layer] at h
        rw [layer, wval, h]
        rfl

theorem wval_andCirc_below (x : Word) (n k i : ℕ) (hi : i < n) :
    wval (layer (andTmpl n) k ++ layer inpTmpl n) i x = x.getD i false := by
  rw [wval, vals_append_getD x _ _ (by simpa using hi)]
  exact wval_layer_inp x n i hi

theorem wval_andCirc_top (x : Word) (n : ℕ) : ∀ k, k ≤ n → ∀ j, j < k →
    wval (layer (andTmpl n) k ++ layer inpTmpl n) (n + j) x = andPrefix x j := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
      intro hk j hj
      have hlen : (layer (andTmpl n) k ++ layer inpTmpl n).length = k + n := by simp
      rcases Nat.lt_or_ge j k with h | h
      · have hlt : n + j < (layer (andTmpl n) k ++ layer inpTmpl n).length := by
          rw [hlen]; omega
        rw [layer, List.cons_append, wval, vals_cons_getD_lt x _ _ hlt]
        exact ih (by omega) j h
      · have hj' : j = k := by omega
        subst hj'
        have hcons : wval (layer (andTmpl n) (j + 1) ++ layer inpTmpl n) (n + j) x
            = gateVal x (vals x (layer (andTmpl n) j ++ layer inpTmpl n)) (andTmpl n j) := by
          rw [layer, List.cons_append, wval]
          have : n + j = (layer (andTmpl n) j ++ layer inpTmpl n).length := by rw [hlen]; omega
          rw [this, vals_cons_getD_length]
        rw [hcons, andTmpl]
        split_ifs with h0
        · subst h0
          have h1 : (vals x (layer (andTmpl n) 0 ++ layer inpTmpl n)).getD 0 false
              = x.getD 0 false := wval_andCirc_below x n 0 0 (by omega)
          rw [gateVal, h1]
          simp [andPrefix]
        · have hjn : j < n := by omega
          have h1 : (vals x (layer (andTmpl n) j ++ layer inpTmpl n)).getD (n + j - 1) false
              = andPrefix x (j - 1) := by
            have hidx : n + j - 1 = n + (j - 1) := by omega
            rw [hidx]
            exact ih (by omega) (j - 1) (by omega)
          have h2 : (vals x (layer (andTmpl n) j ++ layer inpTmpl n)).getD j false
              = x.getD j false := wval_andCirc_below x n j j hjn
          rw [gateVal, h1, h2]
          match j with
          | 0 => exact absurd rfl h0
          | m + 1 => simp [andPrefix]

theorem out_andCirc (x : Word) (n : ℕ) (hn : 0 < n) :
    out x (andCirc n) = andPrefix x (n - 1) := by
  match n with
  | m + 1 =>
      have hcons : out x (andCirc (m + 1)) = wval (andCirc (m + 1))
            (layer (andTmpl (m + 1)) m ++ layer inpTmpl (m + 1)).length x := by
        rw [andCirc, layer, List.cons_append, out, wval, vals_cons_getD_length]
      have hlen : (layer (andTmpl (m + 1)) m ++ layer inpTmpl (m + 1)).length = (m + 1) + m := by
        simp; omega
      rw [hcons, hlen, andCirc]
      simpa using wval_andCirc_top x (m + 1) (m + 1) le_rfl m (by omega)

/-! ### Uniformity -/

/-- The token of an input gate. -/
def inpBlkT : Cob :=
  Cob.catL [Cob.constT [false, true, false], .comp (.app true) [.proj 1], Cob.constT [false, true]]

theorem eval_inpBlkT (y : Word) (c : ℕ) (p : Word) :
    inpBlkT.eval [y, List.replicate c true, p] = encGate (inpTmpl c) := by
  simp only [inpBlkT, Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_constT, Cob.eval_comp,
    Cob.eval_app, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [inpTmpl, encGate]
  simp [tag, fld1, fld2, List.replicate_succ]

theorem length_encGate_inpTmpl (n c l : ℕ) (hc : c ≤ l) :
    (encGate (inpTmpl c)).length ≤ 12 * (l + n + 1) := by
  rw [length_encGate, inpTmpl]
  simp only [tag, fld1, fld2]
  omega

/-- The token of a conjunction gate of the top layer. -/
def andBlkT : Cob :=
  .comp Cob.iteC
    [.proj 1,
      Cob.catL [Cob.constT [false, true, true, true, true, true, false],
        .comp Cob.concat [.proj 2, .proj 1], Cob.constT [false],
        .comp (.app true) [.proj 1]],
      Cob.constT (encGate (.conj 0 0))]

theorem eval_andBlkT (n : ℕ) (y : Word) (c : ℕ) :
    andBlkT.eval [y, List.replicate c true, List.replicate n true] = encGate (andTmpl n c) := by
  rw [andBlkT]
  cases c with
  | zero => simp [andTmpl]
  | succ k =>
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_proj,
        List.getD_cons_succ, List.getD_cons_zero, Cob.eval_catL, Cob.eval_constT, Cob.eval_concat,
        Cob.eval_app, List.flatten_cons, List.flatten_nil, List.append_nil,
        if_neg (by simp : ¬ List.replicate (k + 1) true = [])]
      rw [andTmpl, if_neg (by omega), encGate]
      simp only [tag, fld1, fld2]
      rw [← List.replicate_add]
      have h1 : n + (k + 1) - 1 + 1 = n + (k + 1) := by omega
      rw [h1]
      simp [List.replicate_succ, List.replicate_add]

theorem length_encGate_andTmpl (n c l : ℕ) (hc : c ≤ l) :
    (encGate (andTmpl n c)).length ≤ 12 * (l + n + 1) := by
  rw [length_encGate, andTmpl]
  split_ifs with h
  · simp only [tag, fld1, fld2]; omega
  · simp only [tag, fld1, fld2]; omega

end CircCode

/-- The bottom layer is P-uniform. -/
theorem codeUniform_layer_inp :
    CodeUniform (fun n => CircCode.layer CircCode.inpTmpl n) := by
  have h := codeUniform_layer (tmpl := fun _ c => CircCode.inpTmpl c) (k := fun n => n)
    (cnt := .comp .smash [.proj 0, Cob.constT [true]]) (blkT := CircCode.inpBlkT) (K := 12)
    eval_lenCnt (fun _ y c => CircCode.eval_inpBlkT y c _) CircCode.length_encGate_inpTmpl
  exact h

/-- The top layer is P-uniform. -/
theorem codeUniform_layer_and :
    CodeUniform (fun n => CircCode.layer (CircCode.andTmpl n) n) :=
  codeUniform_layer (tmpl := CircCode.andTmpl) (k := fun n => n)
    (cnt := .comp .smash [.proj 0, Cob.constT [true]]) (blkT := CircCode.andBlkT) (K := 12)
    eval_lenCnt (fun n y c => CircCode.eval_andBlkT n y c) CircCode.length_encGate_andTmpl

/-- **The conjunction circuits are a P-uniform family**: a single Cobham term writes the
description of `andCirc n` from any word of length `n`.  Together with
`Complexity.CircCode.out_andCirc` and `Complexity.CircCode.wf_andCirc`, this is a P-uniform family
of well-formed circuits of linear size computing the conjunction of the first `n` input bits. -/
theorem codeUniform_andCirc : CodeUniform CircCode.andCirc :=
  codeUniform_append codeUniform_layer_and codeUniform_layer_inp

/-! ### Two families in one circuit -/

namespace CircCode

open Complexity.Tseitin

/-- The conjunction circuits stacked on the chain of negations: two unrelated families written
into a single circuit, the upper one relocated so that its references still point at its own
gates. -/
def andOverNeg (n : ℕ) : Circuit := reloc (cfNeg n).length (andCirc n) ++ cfNeg n

theorem andCirc_succ (m : ℕ) :
    andCirc (m + 1)
      = andTmpl (m + 1) m :: (layer (andTmpl (m + 1)) m ++ layer inpTmpl (m + 1)) := by
  rw [andCirc, layer, List.cons_append]

theorem wf_andOverNeg (n : ℕ) (hn : 0 < n) : wf (andOverNeg n) :=
  wf_reloc_append (cfNeg n) (wf_cfNeg n) (andCirc n) (wf_andCirc n hn)

/-- **Stacking does not disturb the upper family**: the stacked circuit still computes the
conjunction of the first `n` input bits. -/
theorem out_andOverNeg (x : Word) (n : ℕ) (hn : 0 < n) :
    out x (andOverNeg n) = andPrefix x (n - 1) := by
  match n with
  | m + 1 =>
      have hwf : wf (andTmpl (m + 1) m ::
          (layer (andTmpl (m + 1)) m ++ layer inpTmpl (m + 1))) := by
        rw [← andCirc_succ]
        exact wf_andCirc (m + 1) hn
      rw [andOverNeg, andCirc_succ, out_reloc_append x (cfNeg (m + 1)) _ _ hwf, ← andCirc_succ,
        out_andCirc x (m + 1) hn]

end CircCode

/-- The stacked family is P-uniform, by `Complexity.codeUniform_stack`. -/
theorem codeUniform_andOverNeg : CodeUniform CircCode.andOverNeg :=
  codeUniform_stack codeUniform_andCirc codeUniform_cfNeg

/-! ### One family fed by another -/

namespace CircCode

open Complexity.Tseitin

theorem mem_layer {tmpl : ℕ → Gate} {n : ℕ} {g : Gate} (h : g ∈ layer tmpl n) :
    ∃ i, i < n ∧ g = tmpl i := by
  induction n with
  | zero => cases h
  | succ n ih =>
      rw [layer, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨n, by omega, h⟩
      · obtain ⟨i, hi, hg⟩ := ih h
        exact ⟨i, by omega, hg⟩

/-- The conjunction circuit of size `n` reads only the first `n` circuit inputs. -/
theorem inpsLt_andCirc (n : ℕ) : inpsLt n (andCirc n) := by
  intro g hg
  rw [andCirc, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨i, _, rfl⟩ := mem_layer hg
    rw [andTmpl]
    split_ifs <;> trivial
  · obtain ⟨i, hi, rfl⟩ := mem_layer hg
    exact hi

/-- The conjunction circuits fed by the chain of negations: the input bits of the conjunction
circuit are the values of the gates of the negation chain. -/
def andAfterNeg (n : ℕ) : Circuit := reroute (cfNeg n).length 0 (andCirc n) ++ cfNeg n

theorem wf_andAfterNeg (n : ℕ) (hn : 0 < n) : wf (andAfterNeg n) :=
  wf_reroute_append (cfNeg n) (wf_cfNeg n) 0 (Nat.zero_le _) (andCirc n) (wf_andCirc n hn)
    (by simpa using inpsLt_andCirc n)

/-- **The composed circuit runs the conjunction circuit on the values of the negation chain.** -/
theorem out_andAfterNeg (x : Word) (n : ℕ) (hn : 0 < n) :
    out x (andAfterNeg n) = andPrefix (vals x (cfNeg n)) (n - 1) := by
  match n with
  | m + 1 =>
      have hwf : wf (andTmpl (m + 1) m ::
          (layer (andTmpl (m + 1)) m ++ layer inpTmpl (m + 1))) := by
        rw [← andCirc_succ]
        exact wf_andCirc (m + 1) hn
      have hin : inpsLt ((cfNeg (m + 1)).length - 0) (andTmpl (m + 1) m ::
          (layer (andTmpl (m + 1)) m ++ layer inpTmpl (m + 1))) := by
        rw [← andCirc_succ]
        simpa using inpsLt_andCirc (m + 1)
      rw [andAfterNeg, andCirc_succ,
        out_reroute_append x (cfNeg (m + 1)) 0 (Nat.zero_le _) _ _ hwf hin, ← andCirc_succ,
        List.drop_zero, out_andCirc _ (m + 1) hn]

end CircCode

/-- The composed family is P-uniform, by `Complexity.codeUniform_compose`. -/
theorem codeUniform_andAfterNeg : CodeUniform CircCode.andAfterNeg :=
  codeUniform_compose (e := fun _ => 0) codeUniform_andCirc codeUniform_cfNeg
    (eT := .empty) (fun _ => by simp)

end Complexity
