/-
# Deep layers: the compiler's rule for a circuit of more than one level

`Start/UniformSigApp.lean` realizes a word function whose output wires are *constants or circuit
inputs* — a **flat layer**.  Every gadget with genuine logic in it — a multiplexer, a truncation,
a test on a bit — needs gates that read *other gates*, so the flat rule cannot express it.

This module removes the restriction.  A layer written by a template may already contain references
(the chain of negations of `Start/UniformCircuit.lean` is one), so no new uniformity machinery is
needed: what is missing is only the reading of the interface of `Start/UniformSignal.lean`, namely
the observation that the topmost `2 * m n` gates of a layer of `L n + 2 * m n` gates carry the
signal of the value, and that the value of a gate is `Complexity.CircCode.lval`.

Main results:

* `Complexity.Tseitin.topVals_layer` — the topmost gates of a layer are the values of its topmost
  templates;
* `Complexity.sigUniform_of_layer` — **a layer written by a Cobham term, with the signal of the
  value on its topmost `2 * m n` gates, realizes that value**: the general rule of which
  `Complexity.sigUniform_of_flatLayer` is the depth-one case.
-/

import Start.UniformSigApp

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-- **The topmost gates of a layer**, read as a list indexed by the offset above the cut. -/
theorem topVals_layer (x : Word) (tmpl : ℕ → Gate) (L w : ℕ) :
    topVals w (vals x (CircCode.layer tmpl (L + w)))
      = (List.range w).map (fun c => CircCode.lval x tmpl (L + c)) := by
  have hlen : (vals x (CircCode.layer tmpl (L + w))).length = L + w := by simp
  refine List.ext_getElem (by simp [topVals, hlen]) ?_
  intro i h1 h2
  have hi : i < w := by
    simpa [topVals, hlen] using h1
  have hget : (topVals w (vals x (CircCode.layer tmpl (L + w))))[i]
      = (vals x (CircCode.layer tmpl (L + w))).getD (L + i) false := by
    simp only [topVals, List.getElem_drop]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; omega)]
    congr 1
    omega
  rw [hget, CircCode.vals_layer_getD x tmpl _ _ (by omega)]
  simp

end Tseitin

open Complexity.Tseitin

/-- **A layer written by a Cobham term realizes the function carried by its topmost gates.**

The layer has `L n + 2 * m n` gates; the gate `c` may refer to any gate below it, so the layer is a
circuit of arbitrary depth, and the topmost `2 * m n` gates carry the signal of the value.  This is
`Complexity.sigUniform_of_flatLayer` with the flatness dropped, at the price of a value hypothesis
stated in terms of the values `Complexity.CircCode.lval` of the gates underneath. -/
theorem sigUniform_of_layer {r : ℕ} {m L : ℕ → ℕ} {F : List Word → Word}
    {tmpl : ℕ → ℕ → Tseitin.Gate} {mT lenT blkT : Cob} {K : ℕ}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hL : ∀ x : Word, lenT.eval [x] = List.replicate (L x.length) true)
    (hwf : ∀ n c, Tseitin.gateWf c (tmpl n c))
    (hinp : ∀ n c, c < L n + 2 * m n → Tseitin.inpLt (r * (2 * m n)) (tmpl n c))
    (hblk : ∀ (n : ℕ) (y : Word) (c : ℕ),
      blkT.eval [y, List.replicate c true, dmW n (2 * m n)] = CircCode.encGate (tmpl n c))
    (hbndT : ∀ n c l : ℕ, c ≤ l →
      (CircCode.encGate (tmpl n c)).length ≤ K * (l + (dmW n (2 * m n)).length + 1))
    (hval : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
      (List.range (2 * m n)).map
          (fun c => CircCode.lval (encArgs (m n) args) (tmpl n) (L n + c))
        = encSig (m n) (F args)) :
    SigUniform r m F := by
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  refine ⟨fun n => CircCode.layer (tmpl n) (L n + 2 * m n), ?_⟩
  refine ⟨fun n => CircCode.wf_layer (fun c _ => hwf n c),
    fun n => Tseitin.inpsLt_layer_of_flat _ (hinp n), fun n => by simp, ?_, ?_⟩
  · refine codeUniform_layerP (K := K) (cnt := Cob.catL [lenT, twoT])
      (padT := Cob.catL [.comp .smash [Cob.proj 0, Cob.constT [true]], Cob.constT [false], twoT])
      (pw := fun n => dmW n (2 * m n)) (blkT := blkT) (tmpl := tmpl) ?_ ?_ hblk hbndT
    · intro x
      simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, hL x, htwo x]
      rw [← List.replicate_add]
    · intro x
      simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, Cob.eval_constT, Cob.eval_comp, Cob.eval_smash, Cob.eval_proj,
        List.getD_cons_zero, List.getD_cons_succ, htwo x]
      simp [dmW]
  · intro n args hlen hle
    rw [Tseitin.topVals_layer]
    exact hval n args hlen hle

end Complexity
