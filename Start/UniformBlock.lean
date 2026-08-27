/-
**Layers with an automaton: the loop rule for P-uniform descriptions.**

`Start/UniformCircuit.lean` proves that a *layer* — `n` gates whose kind and fields are read off
the identifier of the gate — is P-uniform as soon as one Cobham term writes the token of the gate
with identifier `c` from `1^c`.  That rule writes one gate per step of the loop, and the gate may
only depend on its own identifier.

Circuits produced by a compiler are not shaped like that: they are a sequence of *blocks*, and the
gate to write depends on which block it belongs to and on its offset inside the block.  Deciding
that from `1^c` alone means dividing `c`, which the loop of `Start/CobhamBlock.lean` cannot do in
one step.  The loop can, however, carry a finite-state control alongside its counter, and that is
exactly enough: this module generalises the layer rule so that the gate written at identifier `c`
may depend on the **state** of an arbitrary finite automaton after reading `1^c` *and* on the
**counter** it accumulates, with a separate Cobham term for each state.

Taking the automaton to be the cycle of length `K₀`, the state after `1^c` is `c % K₀` and the
counter is `c / K₀`.  So the block decomposition is available for free, and one obtains the rule
that was missing: a family of circuits made of blocks of a fixed size is P-uniform as soon as, for
each offset inside the block, one Cobham term writes that gate from the block index in unary.

Main definitions:

* `Complexity.CircCode.autoLayerGen` — the Cobham term writing the description of an
  automaton-driven layer;
* `Complexity.CircCode.cycD`, `Complexity.CircCode.cycI` — the cyclic automaton and its counter.

Main results:

* `Complexity.CircCode.brun_layer_auto` — the block-emitting recursion writes the description of
  the layer whose gate at `c` is determined by the state and the counter at `c`;
* `Complexity.codeUniform_autoLayer` — **an automaton-driven layer is P-uniform**;
* `Complexity.CircCode.rst_cyc`, `Complexity.CircCode.rcnt_cyc` — the cyclic automaton computes
  `c % K₀` and `c / K₀`;
* `Complexity.codeUniform_blockLayer` — **a family of circuits made of blocks of a fixed size is
  P-uniform**, given one Cobham term per offset inside the block.
-/

import Start.UniformCircuit

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### Layers driven by an automaton -/

/-- The description of a layer whose gate at identifier `c` is `f s c'`, where `s` and `c'` are the
state and the counter of the block-emitting recursion after reading `1^c`, is written by that
recursion. -/
theorem brun_layer_auto (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (f : ℕ → ℕ → Gate) (N : ℕ) :
    brun δ inc (fun s _ _ c => encGate (f s c)) (List.replicate N true)
      = encCirc (layer (fun c => f (rst δ 0 (List.replicate c true))
          (rcnt δ inc (List.replicate c true))) N) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [List.replicate_succ, brun, ih, layer, encCirc]

/-- The Cobham term writing the description of an automaton-driven layer: `cnt` says how many
gates the layer has, in unary, and `blkT s` writes the token of a gate reached in the state `s`,
from the counter `1^c` and from the length `1^n` of the instance. -/
def autoLayerGen (m : ℕ) (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (cnt : Cob) (blkT : ℕ → Cob)
    (Ki K : ℕ) : Cob :=
  .comp (blkRunTerm m δ inc (fun s _ => blkT s) Ki K)
    [cnt, .comp .smash [.proj 0, Cob.constT [true]]]

theorem eval_autoLayerGen {m Ki K : ℕ} {δ : ℕ → Bool → ℕ} {inc : ℕ → Bool → ℕ}
    (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (hi : ∀ s b, inc s b ≤ Ki)
    {tmpl : ℕ → ℕ → ℕ → Gate} {k : ℕ → ℕ} {cnt : Cob} {blkT : ℕ → Cob}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hblk : ∀ (n : ℕ) (y : Word) (s c : ℕ),
      (blkT s).eval [y, List.replicate c true, List.replicate n true] = encGate (tmpl n s c))
    (hb : ∀ n s c l : ℕ, c ≤ l * Ki → (encGate (tmpl n s c)).length ≤ K * (l + n + 1))
    (x : Word) :
    (autoLayerGen m δ inc cnt blkT Ki K).eval [x]
      = encCirc (layer (fun c => tmpl x.length (rst δ 0 (List.replicate c true))
          (rcnt δ inc (List.replicate c true))) (k x.length)) := by
  have h := eval_blkRunTerm (m := m) (Ki := Ki) (K := K) hm hδ hi
    (fun s _ => blkT s) (blk := fun s _ _ c => encGate (tmpl x.length s c))
    (List.replicate x.length true)
    (fun s _ y c => hblk x.length y s c)
    (fun s _ y c hc => by
      simpa using hb x.length s c y.length (by simpa using hc))
    (List.replicate (k x.length) true)
  rw [autoLayerGen]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT, hcnt x,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
  rw [h, brun_layer_auto]

end CircCode

/-- **An automaton-driven layer is a P-uniform family.**

The gate written at identifier `c` may depend on the state of an arbitrary finite automaton after
reading `1^c` and on the counter accumulated along the way, with one Cobham term for each state.
Taking a single state and the increment `1` recovers `Complexity.codeUniform_layer`. -/
theorem codeUniform_autoLayer {m Ki K : ℕ} {δ : ℕ → Bool → ℕ} {inc : ℕ → Bool → ℕ}
    (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (hi : ∀ s b, inc s b ≤ Ki)
    {tmpl : ℕ → ℕ → ℕ → Tseitin.Gate} {k : ℕ → ℕ} {cnt : Cob} {blkT : ℕ → Cob}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hblk : ∀ (n : ℕ) (y : Word) (s c : ℕ),
      (blkT s).eval [y, List.replicate c true, List.replicate n true]
        = CircCode.encGate (tmpl n s c))
    (hb : ∀ n s c l : ℕ, c ≤ l * Ki →
      (CircCode.encGate (tmpl n s c)).length ≤ K * (l + n + 1)) :
    CodeUniform (fun n => CircCode.layer
      (fun c => tmpl n (rst δ 0 (List.replicate c true))
        (rcnt δ inc (List.replicate c true))) (k n)) :=
  ⟨CircCode.autoLayerGen m δ inc cnt blkT Ki K,
    fun x => CircCode.eval_autoLayerGen hm hδ hi hcnt hblk hb x⟩

namespace CircCode

open Complexity.Tseitin

/-! ### The cyclic automaton: blocks of a fixed size -/

/-- The cycle of length `K₀`: after reading `1^c` its state is `c % K₀`. -/
def cycD (K₀ : ℕ) (s : ℕ) (_ : Bool) : ℕ := (s + 1) % K₀

/-- The counter of the cyclic automaton increments once per full turn, so after `1^c` it holds
`c / K₀`. -/
def cycI (K₀ : ℕ) (s : ℕ) (_ : Bool) : ℕ := if s + 1 = K₀ then 1 else 0

theorem cycD_lt {K₀ : ℕ} (hK : 0 < K₀) (s : ℕ) (b : Bool) : cycD K₀ s b < K₀ :=
  Nat.mod_lt _ hK

theorem cycI_le (K₀ s : ℕ) (b : Bool) : cycI K₀ s b ≤ 1 := by
  rw [cycI]; split <;> omega

theorem rst_cyc {K₀ : ℕ} (c : ℕ) :
    rst (cycD K₀) 0 (List.replicate c true) = c % K₀ := by
  induction c with
  | zero => simp [rst]
  | succ c ih => rw [List.replicate_succ, rst, ih, cycD, Nat.mod_add_mod]

/-- One step of integer division: `(c + 1) / K₀` exceeds `c / K₀` exactly when `c % K₀` is the
last residue. -/
theorem div_succ_eq {K₀ : ℕ} (hK : 0 < K₀) (c : ℕ) :
    (c + 1) / K₀ = (if c % K₀ + 1 = K₀ then 1 else 0) + c / K₀ := by
  by_cases h : c % K₀ + 1 = K₀
  · rw [if_pos h]
    have h1 : c + 1 = K₀ * (c / K₀ + 1) := by
      calc c + 1 = K₀ * (c / K₀) + c % K₀ + 1 := by rw [Nat.div_add_mod]
        _ = K₀ * (c / K₀) + K₀ := by rw [Nat.add_assoc, h]
        _ = K₀ * (c / K₀ + 1) := by ring
    rw [h1, Nat.mul_div_cancel_left _ hK]
    omega
  · rw [if_neg h]
    have hlt : c % K₀ < K₀ := Nat.mod_lt _ hK
    have h2 : c + 1 = K₀ * (c / K₀) + (c % K₀ + 1) := by
      rw [← Nat.add_assoc, Nat.div_add_mod]
    have h3 : (c % K₀ + 1) / K₀ = 0 := Nat.div_eq_of_lt (by omega)
    rw [h2, Nat.mul_add_div hK, h3, Nat.zero_add, Nat.add_zero]

theorem rcnt_cyc {K₀ : ℕ} (hK : 0 < K₀) (c : ℕ) :
    rcnt (cycD K₀) (cycI K₀) (List.replicate c true) = c / K₀ := by
  induction c with
  | zero => simp [rcnt]
  | succ c ih =>
      rw [List.replicate_succ, rcnt, ih, rst_cyc, cycI, div_succ_eq hK]

end CircCode

/-- **A family of circuits made of blocks of a fixed size is P-uniform.**

The gate with identifier `c` belongs to the block `c / K₀` at the offset `c % K₀`, and for each
offset a Cobham term writes that gate from the block index in unary and from `1^n`.  This is the
loop rule that a description-writing program needs: the body of the loop may be any fixed number
of gates. -/
theorem codeUniform_blockLayer {K₀ K : ℕ} (hK : 0 < K₀)
    {tmpl : ℕ → ℕ → ℕ → Tseitin.Gate} {k : ℕ → ℕ} {cnt : Cob} {blkT : ℕ → Cob}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hblk : ∀ (n : ℕ) (y : Word) (s c : ℕ),
      (blkT s).eval [y, List.replicate c true, List.replicate n true]
        = CircCode.encGate (tmpl n s c))
    (hb : ∀ n s c l : ℕ, c ≤ l →
      (CircCode.encGate (tmpl n s c)).length ≤ K * (l + n + 1)) :
    CodeUniform (fun n => CircCode.layer (fun c => tmpl n (c % K₀) (c / K₀)) (k n)) := by
  have h := codeUniform_autoLayer (m := K₀) (Ki := 1) (K := K)
    (δ := CircCode.cycD K₀) (inc := CircCode.cycI K₀)
    hK (CircCode.cycD_lt hK) (CircCode.cycI_le K₀) (tmpl := tmpl) (k := k) hcnt hblk
    (fun n s c l hc => hb n s c l (by omega))
  have heq : (fun n => CircCode.layer
      (fun c => tmpl n (rst (CircCode.cycD K₀) 0 (List.replicate c true))
        (rcnt (CircCode.cycD K₀) (CircCode.cycI K₀) (List.replicate c true))) (k n))
      = (fun n => CircCode.layer (fun c => tmpl n (c % K₀) (c / K₀)) (k n)) := by
    funext n
    congr 1
    funext c
    rw [CircCode.rst_cyc, CircCode.rcnt_cyc hK]
  rwa [heq] at h

end Complexity
