/-
**The layer and grid rules with a padded parameter.**

`Start/UniformCircuit.lean` and `Start/UniformGrid.lean` write a layer — or a grid — of gates with
a block-emitting recursion whose parameter is the word `1^n`, `n` being the length of the instance.
Two things follow from that choice: the term writing a gate is given `1^n` and nothing else, and the
token it writes must be of length linear in `n` and in the identifier of the gate, because the
recursion of `Start/CobhamBlock.lean` bounds the emitted block by
`K * (|suffix| + |parameter| + 1)`.

The second restriction is real: a circuit assembled out of blocks that are themselves circuits of
polynomial size refers, from its very first gate, to gates whose identifiers are polynomial in `n`,
so its tokens are *not* of length linear in `n`.  The remedy is to hand the recursion a longer
parameter, and this module carries that out: the parameter is an arbitrary word `pw n` written by a
Cobham term, the gate-writing term receives it in place of `1^n`, and the length of a token has only
to be linear in the identifier and in `|pw n|`.

Main definitions:

* `Complexity.CircCode.layerGenP` — the layer generator with a parameter word of its own.

Main results:

* `Complexity.CircCode.eval_layerGenP` — it writes the description of the layer;
* `Complexity.codeUniform_layerP` — **the layer rule with a padded parameter**;
* `Complexity.codeUniform_gridLayerP` — **the grid rule with a padded parameter**.
-/

import Start.UniformGrid

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-- The Cobham term writing the description of the `n`-th layer, with a parameter word of its own:
`cnt` says how many gates the layer has, in unary, `padT` writes the parameter, and `blkT` writes
the token of the gate with identifier `c` from `1^c` and from that parameter. -/
def layerGenP (cnt blkT padT : Cob) (K : ℕ) : Cob :=
  .comp (blkRunTerm 1 uState uInc (fun _ _ => blkT) 1 K) [cnt, padT]

theorem eval_layerGenP {tmpl : ℕ → ℕ → Gate} {k : ℕ → ℕ} {pw : ℕ → Word}
    {cnt blkT padT : Cob} {K : ℕ}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hpad : ∀ x : Word, padT.eval [x] = pw x.length)
    (hblk : ∀ (n : ℕ) (y : Word) (c : ℕ),
      blkT.eval [y, List.replicate c true, pw n] = encGate (tmpl n c))
    (hb : ∀ n c l : ℕ, c ≤ l → (encGate (tmpl n c)).length ≤ K * (l + (pw n).length + 1))
    (x : Word) :
    (layerGenP cnt blkT padT K).eval [x] = encCirc (layer (tmpl x.length) (k x.length)) := by
  have h := eval_blkRunTerm (m := 1) (Ki := 1) (K := K) (by norm_num) uState_lt uInc_le
    (fun _ _ => blkT) (blk := fun _ _ _ c => encGate (tmpl x.length c))
    (pw x.length)
    (fun _ _ y c => hblk x.length y c)
    (fun _ _ y c hc => hb x.length c y.length (by simpa using hc))
    (List.replicate (k x.length) true)
  rw [layerGenP]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hcnt x, hpad x]
  rw [h, brun_layer]

end CircCode

/-- **A layer is a P-uniform family, with a parameter of its own.**  This is
`Complexity.codeUniform_layer` with the parameter `1^n` of the block-emitting recursion replaced by
an arbitrary word `pw n` written by a Cobham term: the token of a gate has then only to be of
length linear in its identifier and in `|pw n|`. -/
theorem codeUniform_layerP {tmpl : ℕ → ℕ → Tseitin.Gate} {k : ℕ → ℕ} {pw : ℕ → Word}
    {cnt blkT padT : Cob} {K : ℕ}
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hpad : ∀ x : Word, padT.eval [x] = pw x.length)
    (hblk : ∀ (n : ℕ) (y : Word) (c : ℕ),
      blkT.eval [y, List.replicate c true, pw n] = CircCode.encGate (tmpl n c))
    (hb : ∀ n c l : ℕ, c ≤ l →
      (CircCode.encGate (tmpl n c)).length ≤ K * (l + (pw n).length + 1)) :
    CodeUniform (fun n => CircCode.layer (tmpl n) (k n)) :=
  ⟨CircCode.layerGenP cnt blkT padT K,
    fun x => CircCode.eval_layerGenP hcnt hpad hblk hb x⟩

/-- **A grid of blocks of a Cobham-computable width is P-uniform, with a parameter of its own.**
This is `Complexity.codeUniform_gridLayer` with the parameter `1^n` of the block-emitting recursion
replaced by an arbitrary word `pw n`: the width and the gate at a given row and column are computed
from that word, and a token has only to be of length linear in the identifier of its gate and in
`|pw n|`. -/
theorem codeUniform_gridLayerP {tmpl : ℕ → ℕ → ℕ → Tseitin.Gate} {k w : ℕ → ℕ} {pw : ℕ → Word}
    {cnt widT gblk padT : Cob} {K : ℕ} (hw : ∀ n, 0 < w n)
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hpad : ∀ x : Word, padT.eval [x] = pw x.length)
    (hwid : ∀ n : ℕ, widT.eval [pw n] = List.replicate (w n) true)
    (hblk : ∀ (n i j : ℕ) (y : Word), j < w n →
      gblk.eval [y, List.replicate i true, List.replicate j true, pw n]
        = CircCode.encGate (tmpl n i j))
    (hb : ∀ n i j l : ℕ, j < w n → w n * i + j ≤ l →
      (CircCode.encGate (tmpl n i j)).length ≤ K * (l + (pw n).length + 1)) :
    CodeUniform (fun n => CircCode.layer (fun c => tmpl n (c / w n) (c % w n)) (k n)) := by
  refine codeUniform_layerP (K := K) (cnt := cnt) (padT := padT)
    (blkT := .comp gblk [.proj 0, Cob.divT (.proj 1) (.comp widT [.proj 2]),
      Cob.modT (.proj 1) (.comp widT [.proj 2]), .proj 2]) hcnt hpad ?_ ?_
  · intro n y c
    have hwn : (Cob.comp widT [Cob.proj 2]).eval [y, List.replicate c true, pw n]
        = List.replicate (w n) true := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
        List.getD_cons_succ, List.getD_cons_zero]
      exact hwid n
    have harg : (Cob.proj 1).eval [y, List.replicate c true, pw n]
        = List.replicate c true := by simp
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ,
      Cob.eval_divT (hw n) harg hwn, Cob.eval_modT (hw n) harg hwn]
    exact hblk n (c / w n) (c % w n) y (Nat.mod_lt c (hw n))
  · intro n c l hc
    exact hb n (c / w n) (c % w n) l (Nat.mod_lt c (hw n))
      (by rw [Nat.div_add_mod]; exact hc)

end Complexity
