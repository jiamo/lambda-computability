/-
**An algebra of P-uniform circuit families.**

`Start/CookLevinCode.lean` reduces the missing half of Cook–Levin to `Complexity.CodeUniform`:
that the description of the `n`-th circuit of a family is written by a single Cobham term.  Closing
that hypothesis means *building* such descriptions, and the descriptions of the circuits produced
by the compiler of `Start/CobhamCircuit.lean` are put together out of a few repeating patterns.
This module isolates those patterns as closure properties of `Complexity.CodeUniform`, so that a
uniform family can be assembled the way a circuit is:

* a fixed circuit is uniform (`Complexity.codeUniform_const`);
* two uniform families may be written one after the other (`Complexity.codeUniform_append`) — at
  the level of *descriptions* this is concatenation, since the code of a circuit is the
  concatenation of the codes of its gates;
* a *layer* — `n` gates whose kind and fields are read off the identifier of the gate — is uniform
  as soon as one Cobham term writes the token of the gate with identifier `c` from `1^c`
  (`Complexity.codeUniform_layer`).  This is the loop of the description-writing program, and it is
  supplied by the block-emitting recursion of `Start/CobhamBlock.lean`.

The chain of negations of `Start/CodeUniformExample.lean` is a layer, and its uniformity is
recovered from the general lemma (`Complexity.CircCode.codeUniform_layer_neg`).

Main definitions:

* `Complexity.CircCode.layer` — the circuit whose gate with identifier `i` is `tmpl i`;
* `Complexity.CircCode.layerGen` — the Cobham term writing the description of a layer.

Main results:

* `Complexity.CircCode.encCirc_append` — the code of a concatenation is the concatenation of the
  codes;
* `Complexity.codeUniform_const`, `Complexity.codeUniform_append`,
  `Complexity.codeUniform_layer` — **the three closure properties**.
-/

import Start.CodeUniformExample

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The code of a concatenation -/

theorem encCirc_append (C D : Circuit) : encCirc (C ++ D) = encCirc C ++ encCirc D := by
  induction C with
  | nil => rfl
  | cons g C ih => rw [List.cons_append, encCirc, encCirc, ih, List.append_assoc]

/-! ### Layers -/

/-- The **layer** given by a template: a circuit of `n` gates in which the gate with identifier `i`
is `tmpl i`.  Gates are written output first, so the list runs from `tmpl (n - 1)` down to
`tmpl 0`. -/
def layer (tmpl : ℕ → Gate) : ℕ → Circuit
  | 0 => []
  | n + 1 => tmpl n :: layer tmpl n

@[simp] theorem length_layer (tmpl : ℕ → Gate) (n : ℕ) : (layer tmpl n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [layer, List.length_cons, ih]

/-- The control of the layer generator: one state, and the counter counts the gates already
written, so at each position it holds the identifier of the gate to write. -/
def uState (_ : ℕ) (_ : Bool) : ℕ := 0

theorem uState_lt (s : ℕ) (b : Bool) : uState s b < 1 := Nat.lt_succ_self 0

/-- The counter of the layer generator counts the gates already written. -/
def uInc (_ : ℕ) (_ : Bool) : ℕ := 1

theorem uInc_le (s : ℕ) (b : Bool) : uInc s b ≤ 1 := le_refl _

theorem rcnt_uInc (k : ℕ) : rcnt uState uInc (List.replicate k true) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h1 : uInc (rst uState 0 (List.replicate k true)) true = 1 := rfl
      rw [List.replicate_succ, rcnt, ih, h1]
      omega

theorem brun_layer (tmpl : ℕ → Gate) (k : ℕ) :
    brun uState uInc (fun _ _ _ c => encGate (tmpl c)) (List.replicate k true)
      = encCirc (layer tmpl k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, brun, ih, rcnt_uInc, layer, encCirc]

/-- The Cobham term writing the description of the `n`-th layer: `cnt` says how many gates the
layer has, in unary, and `blkT` writes the token of the gate with identifier `c` from `1^c` and
from the length `1^n` of the instance. -/
def layerGen (cnt blkT : Cob) (K : ℕ) : Cob :=
  .comp (blkRunTerm 1 uState uInc (fun _ _ => blkT) 1 K)
    [cnt, .comp .smash [.proj 0, Cob.constT [true]]]

theorem eval_layerGen {tmpl : ℕ → ℕ → Gate} {k : ℕ → ℕ} {cnt blkT : Cob} {K : ℕ}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hblk : ∀ (n : ℕ) (y : Word) (c : ℕ),
      blkT.eval [y, List.replicate c true, List.replicate n true] = encGate (tmpl n c))
    (hb : ∀ n c l : ℕ, c ≤ l → (encGate (tmpl n c)).length ≤ K * (l + n + 1)) (x : Word) :
    (layerGen cnt blkT K).eval [x] = encCirc (layer (tmpl x.length) (k x.length)) := by
  have h := eval_blkRunTerm (m := 1) (Ki := 1) (K := K) (by norm_num) uState_lt uInc_le
    (fun _ _ => blkT) (blk := fun _ _ _ c => encGate (tmpl x.length c))
    (List.replicate x.length true)
    (fun _ _ y c => hblk x.length y c)
    (fun _ _ y c hc => by
      simpa using hb x.length c y.length (by simpa using hc))
    (List.replicate (k x.length) true)
  rw [layerGen]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT, hcnt x,
    List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
  rw [h, brun_layer]

end CircCode

/-! ### The closure properties -/

/-- **A fixed circuit is a P-uniform family.** -/
theorem codeUniform_const (C : Tseitin.Circuit) : CodeUniform (fun _ => C) :=
  ⟨Cob.constW (CircCode.encCirc C), fun _ => Cob.eval_constW _ _⟩

/-- **P-uniform families may be written one after the other.**  Beware that concatenating
circuits shifts the identifiers of the gates of the first one, so the semantics of the parts is
not preserved; what the lemma says is that the *description* of the concatenation is produced in
polynomial time. -/
theorem codeUniform_append {cf cg : ℕ → Tseitin.Circuit} (hf : CodeUniform cf)
    (hg : CodeUniform cg) : CodeUniform (fun n => cf n ++ cg n) := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  refine ⟨.comp Cob.concat [f, g], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hf x, hg x]
  exact (CircCode.encCirc_append _ _).symm

/-- **A layer is a P-uniform family**: if a single Cobham term writes the token of the gate with
identifier `c` from `1^c` and from `1^n`, if those tokens are of length linear in `c` and `n`, and
if the number `k n` of gates of the layer is itself written in unary by a Cobham term, then the
family of layers has P-uniform descriptions.

This is the loop of a description-writing program: the identifier of the gate to write is supplied
by the counter of the block-emitting recursion of `Start/CobhamBlock.lean`. -/
theorem codeUniform_layer {tmpl : ℕ → ℕ → Tseitin.Gate} {k : ℕ → ℕ} {cnt blkT : Cob} {K : ℕ}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hblk : ∀ (n : ℕ) (y : Word) (c : ℕ),
      blkT.eval [y, List.replicate c true, List.replicate n true]
        = CircCode.encGate (tmpl n c))
    (hb : ∀ n c l : ℕ, c ≤ l → (CircCode.encGate (tmpl n c)).length ≤ K * (l + n + 1)) :
    CodeUniform (fun n => CircCode.layer (tmpl n) (k n)) :=
  ⟨CircCode.layerGen cnt blkT K, fun x => CircCode.eval_layerGen hcnt hblk hb x⟩

/-- The unary length of the instance: the count term of a layer with one gate per input bit. -/
theorem eval_lenCnt (x : Word) :
    (Cob.comp .smash [Cob.proj 0, Cob.constT [true]]).eval [x]
      = List.replicate x.length true := by
  simp

namespace CircCode

open Complexity.Tseitin

/-! ### The chain of negations, again -/

/-- The template of the chain of negations: the gate `0` reads the first input bit, and the gate
`i + 1` negates the gate `i`. -/
def negTmpl : ℕ → Gate
  | 0 => .inp 0
  | i + 1 => .neg i

@[simp] theorem negTmpl_zero : negTmpl 0 = .inp 0 := rfl

@[simp] theorem negTmpl_succ (i : ℕ) : negTmpl (i + 1) = .neg i := rfl

theorem layer_negTmpl (n : ℕ) : layer negTmpl n = cfNeg n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      match n with
      | 0 => rfl
      | m + 1 => rw [layer, ih, cfNeg, negTmpl_succ]

/-- The token of the gate with identifier `c` of the chain of negations. -/
def negBlkT : Cob :=
  .comp Cob.iteC
    [.proj 1,
      Cob.catL [Cob.constT [false, true, true, true, true, false],
        .comp (.app true) [.comp Cob.tail [.proj 1]], Cob.constT [false, true]],
      Cob.constT (encGate (.inp 0))]

theorem eval_negBlkT (y : Word) (c : ℕ) (p : Word) :
    negBlkT.eval [y, List.replicate c true, p] = encGate (negTmpl c) := by
  rw [negBlkT]
  cases c with
  | zero => simp
  | succ k =>
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_proj,
        List.getD_cons_succ, List.getD_cons_zero, Cob.eval_catL, Cob.eval_constT, Cob.eval_app,
        Cob.eval_tail, List.tail_replicate, List.flatten_cons, List.flatten_nil, List.append_nil,
        if_neg (by simp : ¬ List.replicate (k + 1) true = []), negTmpl_succ, encGate]
      simp only [tag, fld1, fld2]
      simp [List.replicate_succ]

theorem length_encGate_negTmpl (n c l : ℕ) (hc : c ≤ l) :
    (encGate (negTmpl c)).length ≤ 9 * (l + n + 1) := by
  rw [length_encGate]
  cases c with
  | zero => simp only [negTmpl_zero, tag, fld1, fld2]; omega
  | succ k => simp only [negTmpl_succ, tag, fld1, fld2]; omega

end CircCode

/-- **The chain of negations is P-uniform**, recovered from the general layer lemma.  This is
`Complexity.codeUniform_cfNeg`, proved again from `Complexity.codeUniform_layer` alone. -/
theorem codeUniform_cfNeg_of_layer : CodeUniform CircCode.cfNeg := by
  have h := codeUniform_layer (tmpl := fun _ c => CircCode.negTmpl c) (k := fun n => n)
    (cnt := .comp .smash [.proj 0, Cob.constT [true]]) (blkT := CircCode.negBlkT) (K := 9)
    eval_lenCnt (fun _ y c => CircCode.eval_negBlkT y c _) CircCode.length_encGate_negTmpl
  have h' : CodeUniform (fun n => CircCode.layer CircCode.negTmpl n) := h
  rwa [funext CircCode.layer_negTmpl] at h'

end Complexity
