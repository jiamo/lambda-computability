/-
**`IP ⊆ PSPACE`.**

For a verifier `V`, the value of the game (`Start/IPValue.lean`) is the value of a sum–max tree
whose positions are words, presented by Cobham terms (`Complexity.IPSpace.ipTree`); its depth and
the length of its positions are polynomial in the length of the input.  By
`Complexity.TreeEval.pspace_of_ctree` the test `2^{|coins|} ≤ 2 · value` is then decidable in
polynomial space, and it decides the language of any interactive proof with verifier `V`.

A position is the word `encs [1^tag, 1^k, t, q, a, s]`
(`Complexity.IPSpace.pos`): a node kind, the number `k` of rounds left, the transcript `t`, a
partial question `q`, a partial answer `a` and a partial reversed coin word `s`.  The node kinds:

* `0` — the value after `t` with `k` rounds left (a sum of a node `1` or `5` and a zero leaf);
* `1`, `2` — the sum over the questions extending `q` (`1`: this question and the longer ones,
  `2`: the longer ones);
* `3`, `4` — the maximum over the answers extending `a`;
* `5` — the count of the coin words extending `s` that are consistent with `t` and accepted;
* `6` — a zero leaf.

Main results:

* `Complexity.IPSpace.rnd_sem` — the value of the node `0` is the value of the game;
* `Complexity.IPSpace.ip_subset_pspace` — **`IP ⊆ PSPACE`**;
* `Complexity.IPSpace.ip_eq_pspace` — **Shamir's theorem: `IP = PSPACE`**.
-/

import Start.TreeEval
import Start.IPValue
import Start.CobhamTimeIter
import Start.ShamirIP

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.IPSpace

open Complexity.Shamir Complexity.IPValue Complexity.TreeEval

/-! ### Positions -/

/-- A position of the game tree. -/
def pos (tag k : ℕ) (t q a s : Word) : Word := encs [un tag, un k, t, q, a, s]

theorem length_pos (tag k : ℕ) (t q a s : Word) :
    (pos tag k t q a s).length =
      2 * (tag + k + t.length + q.length + a.length + s.length) + 6 := by
  simp [pos, encs, length_encMsg]; ring

/-- The field `i` of a position, on `[x, p]`. -/
def fldT (i : ℕ) : Cob := Cob.recGetT (Nat.iterate Cob.recSkipT i (.proj 1))

theorem eval_iterate_recSkipT' (t : Cob) (args : List Word) :
    ∀ i, (Nat.iterate Cob.recSkipT i t).eval args = recSkip^[i] (t.eval args)
  | 0 => rfl
  | i + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Cob.eval_recSkipT,
        eval_iterate_recSkipT' t args i]

theorem recSkip_iterate_encs : ∀ (l : List Word) (i : ℕ), i ≤ l.length →
    recSkip^[i] (encs l) = encs (l.drop i)
  | _, 0, _ => rfl
  | [], i + 1, h => by simp at h
  | w :: l, i + 1, h => by
      rw [Function.iterate_succ_apply, encs_cons, recSkip_encMsg,
        recSkip_iterate_encs l i (by simp at h; omega)]
      rfl

theorem eval_fldT (x : Word) (l : List Word) (i : ℕ) (hi : i < l.length) :
    (fldT i).eval [x, encs l] = l.getD i [] := by
  rw [fldT, Cob.eval_recGetT, eval_iterate_recSkipT', Cob.eval_proj, List.getD_cons_succ,
    List.getD_cons_zero, recSkip_iterate_encs l i hi.le]
  obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil (show l.drop i ≠ [] by simp; omega)
  rw [hw, encs_cons, recGet_encMsg]
  have : l.getD i [] = (l.drop i).getD 0 [] := by
    simp [List.getD_eq_getElem?_getD]
  rw [this, hw]; rfl

@[simp] theorem fld0 (x : Word) (tag k : ℕ) (t q a s : Word) :
    (fldT 0).eval [x, pos tag k t q a s] = un tag := eval_fldT x _ 0 (by simp)
@[simp] theorem fld1 (x : Word) (tag k : ℕ) (t q a s : Word) :
    (fldT 1).eval [x, pos tag k t q a s] = un k := eval_fldT x _ 1 (by simp)
@[simp] theorem fld2 (x : Word) (tag k : ℕ) (t q a s : Word) :
    (fldT 2).eval [x, pos tag k t q a s] = t := eval_fldT x _ 2 (by simp)
@[simp] theorem fld3 (x : Word) (tag k : ℕ) (t q a s : Word) :
    (fldT 3).eval [x, pos tag k t q a s] = q := eval_fldT x _ 3 (by simp)
@[simp] theorem fld4 (x : Word) (tag k : ℕ) (t q a s : Word) :
    (fldT 4).eval [x, pos tag k t q a s] = a := eval_fldT x _ 4 (by simp)
@[simp] theorem fld5 (x : Word) (tag k : ℕ) (t q a s : Word) :
    (fldT 5).eval [x, pos tag k t q a s] = s := eval_fldT x _ 5 (by simp)

/-- A position as a Cobham term. -/
def posT (tag : ℕ) (k t q a s : Cob) : Cob :=
  Cob.catT (Cob.encMsgT (Cob.constT (un tag))) (Cob.catT (Cob.encMsgT k) (Cob.catT (Cob.encMsgT t)
    (Cob.catT (Cob.encMsgT q) (Cob.catT (Cob.encMsgT a) (Cob.encMsgT s)))))

@[simp] theorem eval_posT (tag : ℕ) (k t q a s : Cob) (args : List Word) :
    (posT tag k t q a s).eval args =
      encs [un tag, k.eval args, t.eval args, q.eval args, a.eval args, s.eval args] := by
  simp [posT, encs]

/-! ### The game tree -/

section Tree

variable (V : Verifier)

/-- The message bound, on `[x, …]`. -/
def mT : Cob := .comp V.msgLen [.proj 0]
/-- The number of coins, on `[x, …]`. -/
def cT : Cob := .comp V.coins [.proj 0]

/-- One round of the run of the verifier against the answers read off `t`, on `[s, x, r, t]`. -/
def roundT : Cob :=
  let mt := Cob.comp V.msgLen [.proj 1]
  let u := Cob.catT (.proj 0) (Cob.encMsgT (Cob.takeBy mt (.comp V.ask [.proj 1, .proj 2, .proj 0])))
  Cob.catT u (Cob.encMsgT (Cob.takeBy mt (Cob.recGetT (Cob.dropBy u (.proj 3)))))

/-- A bound `1^{rounds · (4 · msgLen + 2)}` on the transcript, on `[x, r, t]`. -/
def bndT : Cob :=
  let m := Cob.comp V.msgLen [.proj 0]
  .comp .smash [.comp V.rounds [.proj 0], Cob.pre [true, true] (Cob.catT (Cob.catT m m) (Cob.catT m m))]

/-- The transcript of the coins `r` against the answers read off `t`, on `[x, r, t]`. -/
def trT : Cob := .comp (Cob.iterT .empty (roundT V) (bndT V) 3) [.comp V.rounds [.proj 0], .proj 0,
  .proj 1, .proj 2]

/-- The leaf test of a node `5`, on `[x, p]`. -/
def leafT : Cob :=
  .comp (Cob.andT (Cob.eqW (trT V) (.proj 2))
      (Cob.iteT (.comp V.decide [.proj 0, .proj 1, .proj 2]) Cob.trueC .empty))
    [.proj 0, .comp Cob.revTerm [fldT 5], fldT 2]

/-- Prepend a bit to the value of a term. -/
def consB (b : Bool) (t : Cob) : Cob := .comp (.app b) [t]

/-- **The game tree** of a verifier. -/
def ipTree : CTree where
  isLeaf := Cob.tableSel [.empty, .empty, Cob.leU (mT V) (fldT 3), .empty, Cob.leU (mT V) (fldT 4),
    Cob.leU (cT V) (fldT 5), Cob.trueC] (fldT 0)
  isMax := Cob.tableSel [.empty, .empty, .empty, Cob.trueC, Cob.trueC, .empty, .empty] (fldT 0)
  ch0 := Cob.tableSel
    [Cob.iteT (fldT 1) (posT 1 (Cob.tailN 1 (fldT 1)) (fldT 2) .empty .empty .empty)
        (posT 5 .empty (fldT 2) .empty .empty .empty),
      posT 3 (fldT 1) (fldT 2) (fldT 3) .empty .empty,
      posT 1 (fldT 1) (fldT 2) (consB false (fldT 3)) .empty .empty,
      posT 0 (fldT 1) (Cob.catT (fldT 2) (Cob.catT (Cob.encMsgT (fldT 3)) (Cob.encMsgT (fldT 4))))
        .empty .empty .empty,
      posT 3 (fldT 1) (fldT 2) (fldT 3) (consB false (fldT 4)) .empty,
      posT 5 .empty (fldT 2) .empty .empty (consB false (fldT 5)),
      .empty] (fldT 0)
  ch1 := Cob.tableSel
    [posT 6 .empty .empty .empty .empty .empty,
      posT 2 (fldT 1) (fldT 2) (fldT 3) .empty .empty,
      posT 1 (fldT 1) (fldT 2) (consB true (fldT 3)) .empty .empty,
      posT 4 (fldT 1) (fldT 2) (fldT 3) (fldT 4) .empty,
      posT 3 (fldT 1) (fldT 2) (fldT 3) (consB true (fldT 4)) .empty,
      posT 5 .empty (fldT 2) .empty .empty (consB true (fldT 5)),
      .empty] (fldT 0)
  leaf := Cob.tableSel [.empty, .empty, .empty, .empty, .empty, leafT V, .empty] (fldT 0)

end Tree

/-! ### Evaluating the tree terms at positions -/

section Facts

variable (V : Verifier) (x : Word)

theorem tsel (fs : List Cob) (tag k : ℕ) (t q a s : Word) :
    (Cob.tableSel fs (fldT 0)).eval [x, pos tag k t q a s] =
      (fs.getD tag .empty).eval [x, pos tag k t q a s] :=
  Cob.eval_tableSel fs (fldT 0) _ tag (by rw [fld0]; rfl)

theorem un_zero : un 0 = [] := rfl

theorem pos_eq (tag k : ℕ) (t q a s : Word) :
    encs [un tag, un k, t, q, a, s] = pos tag k t q a s := rfl

theorem length_iterate_round_le (P : Prover) (r : Word) : ∀ j,
    ((V.round P x r)^[j] []).length ≤ j * (2 * (2 * V.maxMsg x + 1))
  | 0 => by simp
  | j + 1 => by
      rw [Function.iterate_succ_apply']
      have h := V.length_round_le P x r ((V.round P x r)^[j] [])
      have ih := length_iterate_round_le P r j
      calc _ ≤ j * (2 * (2 * V.maxMsg x + 1)) + 2 * (2 * V.maxMsg x + 1) := by omega
        _ = (j + 1) * (2 * (2 * V.maxMsg x + 1)) := by ring

theorem eval_roundT (s r t : Word) :
    (roundT V).eval [s, x, r, t] = V.round (rd t) x r s := by
  simp [roundT, Verifier.round, rd, Verifier.maxMsg, Cob.eval_takeBy]

theorem eval_trT (r t : Word) : (trT V).eval [x, r, t] = V.transcript (rd t) x r := by
  have hstep : (fun s => (roundT V).eval (s :: [x, r, t])) = V.round (rd t) x r := by
    funext s; exact eval_roundT V x s r t
  have h := Cob.eval_iterT .empty (roundT V) (bndT V) [x, r, t] (V.rounds.eval [x]) (by
    intro j _ hj
    rw [hstep]
    simp only [Cob.eval_empty]
    have h1 := length_iterate_round_le V x (rd t) r j
    have h2 : j * (2 * (2 * V.maxMsg x + 1)) ≤ V.numRounds x * (2 * (2 * V.maxMsg x + 1)) :=
      Nat.mul_le_mul_right _ hj
    simp only [bndT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_pre,
      Cob.eval_catT, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ,
      List.length_replicate, List.length_cons, List.length_append]
    simp only [Verifier.numRounds, Verifier.maxMsg] at h2 h1
    nlinarith)
  rw [hstep] at h
  simp only [trT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    List.getD_cons_succ]
  rw [show (3 : ℕ) = [x, r, t].length from rfl, h]
  simp only [Cob.eval_empty]; rfl

theorem eval_leafT (k : ℕ) (t q a s : Word) :
    (leafT V).eval [x, pos 5 k t q a s] = bw (leafOK V x t s.reverse) := by
  have hacc : (Cob.iteT (.comp V.decide [.proj 0, .proj 1, .proj 2]) Cob.trueC .empty).eval
      [x, s.reverse, t] = bw (!(V.decide.eval [x, s.reverse, t]).isEmpty) := by
    rw [Cob.eval_iteT_word]
    cases h : V.decide.eval [x, s.reverse, t] <;> simp [h, bw]
  simp only [leafT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, fld5, fld2, Cob.eval_revTerm]
  rw [Cob.eval_andT (Cob.eval_eqW _ _ _) hacc]
  simp [eval_trT, leafOK]

/-- Facts about the node kinds. -/
theorem isLeaf_inner (tag k : ℕ) (t q a s : Word) (h : tag = 0 ∨ tag = 1 ∨ tag = 3) :
    (ipTree V).isLeaf.eval [x, pos tag k t q a s] = [] := by
  rcases h with rfl | rfl | rfl <;> simp [ipTree, tsel]

theorem isLeaf_two (k : ℕ) (t q a s : Word) :
    (ipTree V).isLeaf.eval [x, pos 2 k t q a s] = bw (decide (V.maxMsg x ≤ q.length)) := by
  simp [ipTree, tsel, Cob.eval_leU, mT, Verifier.maxMsg]
  congr

theorem isLeaf_four (k : ℕ) (t q a s : Word) :
    (ipTree V).isLeaf.eval [x, pos 4 k t q a s] = bw (decide (V.maxMsg x ≤ a.length)) := by
  simp [ipTree, tsel, Cob.eval_leU, mT, Verifier.maxMsg]
  congr

theorem isLeaf_five (k : ℕ) (t q a s : Word) :
    (ipTree V).isLeaf.eval [x, pos 5 k t q a s] = bw (decide (V.numCoins x ≤ s.length)) := by
  simp [ipTree, tsel, Cob.eval_leU, cT, Verifier.numCoins]
  congr

theorem isLeaf_six (k : ℕ) (t q a s : Word) :
    (ipTree V).isLeaf.eval [x, pos 6 k t q a s] = [true] := by
  simp [ipTree, tsel]

theorem isMax_sum (tag k : ℕ) (t q a s : Word) (h : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 5) :
    (ipTree V).isMax.eval [x, pos tag k t q a s] = [] := by
  rcases h with rfl | rfl | rfl | rfl <;> simp [ipTree, tsel]

theorem isMax_max (tag k : ℕ) (t q a s : Word) (h : tag = 3 ∨ tag = 4) :
    (ipTree V).isMax.eval [x, pos tag k t q a s] = [true] := by
  rcases h with rfl | rfl <;> simp [ipTree, tsel]

theorem lv_zero (tag k : ℕ) (t q a s : Word) (h : tag = 2 ∨ tag = 4 ∨ tag = 6) :
    lv (ipTree V) x (pos tag k t q a s) = [] := by
  rcases h with rfl | rfl | rfl <;> simp [lv, ipTree, tsel]

theorem lv_five (k : ℕ) (t q a s : Word) :
    lv (ipTree V) x (pos 5 k t q a s) = bw (leafOK V x t s.reverse) := by
  simp only [lv, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero, eval_leafT]
  cases leafOK V x t s.reverse <;> simp [bw]

theorem c0_rnd_zero (t q a s : Word) :
    c0 (ipTree V) x (pos 0 0 t q a s) = pos 5 0 t [] [] [] := by
  simp only [c0, ipTree, tsel, List.getD_cons_zero]
  simp only [fld1, fld2, eval_posT, Cob.eval_iteT_word, Cob.eval_tailN,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c0_rnd_succ (k : ℕ) (t q a s : Word) :
    c0 (ipTree V) x (pos 0 (k + 1) t q a s) = pos 1 k t [] [] [] := by
  simp only [c0, ipTree, tsel, List.getD_cons_zero]
  simp only [fld1, fld2, eval_posT, Cob.eval_iteT_word, Cob.eval_tailN,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c1_rnd (k : ℕ) (t q a s : Word) :
    c1 (ipTree V) x (pos 0 k t q a s) = pos 6 0 [] [] [] [] := by
  simp only [c1, ipTree, tsel, List.getD_cons_zero]
  simp only [eval_posT,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c0_sq (k : ℕ) (t q a s : Word) :
    c0 (ipTree V) x (pos 1 k t q a s) = pos 3 k t q [] [] := by
  simp only [c0, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, eval_posT,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c1_sq (k : ℕ) (t q a s : Word) :
    c1 (ipTree V) x (pos 1 k t q a s) = pos 2 k t q [] [] := by
  simp only [c1, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, eval_posT,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c0_se (k : ℕ) (t q a s : Word) :
    c0 (ipTree V) x (pos 2 k t q a s) = pos 1 k t (false :: q) [] [] := by
  simp only [c0, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, eval_posT,
    consB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, List.getD_cons_zero,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c1_se (k : ℕ) (t q a s : Word) :
    c1 (ipTree V) x (pos 2 k t q a s) = pos 1 k t (true :: q) [] [] := by
  simp only [c1, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, eval_posT,
    consB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, List.getD_cons_zero,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c0_ma (k : ℕ) (t q a s : Word) :
    c0 (ipTree V) x (pos 3 k t q a s) = pos 0 k (t ++ encMsg q ++ encMsg a) [] [] [] := by
  simp only [c0, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, fld4, eval_posT,
    Cob.eval_empty, Cob.eval_catT, Cob.eval_encMsgT]
  simp [pos, encs, un, List.append_assoc]

theorem c1_ma (k : ℕ) (t q a s : Word) :
    c1 (ipTree V) x (pos 3 k t q a s) = pos 4 k t q a [] := by
  simp only [c1, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, fld4, eval_posT,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c0_me (k : ℕ) (t q a s : Word) :
    c0 (ipTree V) x (pos 4 k t q a s) = pos 3 k t q (false :: a) [] := by
  simp only [c0, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, fld4, eval_posT,
    consB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, List.getD_cons_zero,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c1_me (k : ℕ) (t q a s : Word) :
    c1 (ipTree V) x (pos 4 k t q a s) = pos 3 k t q (true :: a) [] := by
  simp only [c1, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld1, fld2, fld3, fld4, eval_posT,
    consB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, List.getD_cons_zero,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c0_cnt (k : ℕ) (t q a s : Word) :
    c0 (ipTree V) x (pos 5 k t q a s) = pos 5 0 t [] [] (false :: s) := by
  simp only [c0, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld2, fld5, eval_posT,
    consB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, List.getD_cons_zero,
    Cob.eval_empty]
  simp [pos, encs, un]

theorem c1_cnt (k : ℕ) (t q a s : Word) :
    c1 (ipTree V) x (pos 5 k t q a s) = pos 5 0 t [] [] (true :: s) := by
  simp only [c1, ipTree, tsel, List.getD_cons_succ, List.getD_cons_zero]
  simp only [fld2, fld5, eval_posT,
    consB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, List.getD_cons_zero,
    Cob.eval_empty]
  simp [pos, encs, un]

end Facts

/-! ### Generic facts on values -/

section Generic

variable (T : CTree) (x : Word) (B : ℕ)

theorem good_leaf {p : Word} (hl : T.isLeaf.eval [x, p] ≠ []) (hp : p.length ≤ B) (n : ℕ) :
    Good T x B n p ∧ val T x n p = nv (lv T x p) := by
  cases n with
  | zero => exact ⟨⟨hp, hl⟩, rfl⟩
  | succ n => exact ⟨⟨hp, Or.inl hl⟩, by simp [val, hl]⟩

theorem good_inner {p : Word} {n : ℕ} (hp : p.length ≤ B)
    (h0 : Good T x B n (c0 T x p)) (h1 : Good T x B n (c1 T x p)) : Good T x B (n + 1) p :=
  ⟨hp, Or.inr ⟨h0, h1⟩⟩

theorem val_sum {p : Word} {n : ℕ} (hl : T.isLeaf.eval [x, p] = [])
    (hm : T.isMax.eval [x, p] = []) :
    val T x (n + 1) p = val T x n (c0 T x p) + val T x n (c1 T x p) := by
  simp [val, hl, hm]

theorem val_max {p : Word} {n : ℕ} (hl : T.isLeaf.eval [x, p] = [])
    (hm : T.isMax.eval [x, p] ≠ []) :
    val T x (n + 1) p = max (val T x n (c0 T x p)) (val T x n (c1 T x p)) := by
  simp [val, hl, hm]

end Generic

/-! ### The value of the tree is the value of the game -/

section Semantics

variable (V : Verifier) (x : Word) (B : ℕ)

/-- The bound on the positions of the tree. -/
def bndX : ℕ := 2 * (6 + V.numRounds x + V.numRounds x * (4 * V.maxMsg x + 2) + 2 * V.maxMsg x +
  V.numCoins x) + 6

theorem pos_le (hB : bndX V x ≤ B) {tag k : ℕ} {t q a s : Word} (htag : tag ≤ 6)
    (hk : k ≤ V.numRounds x) (ht : t.length ≤ V.numRounds x * (4 * V.maxMsg x + 2))
    (hq : q.length ≤ V.maxMsg x) (ha : a.length ≤ V.maxMsg x) (hs : s.length ≤ V.numCoins x) :
    (pos tag k t q a s).length ≤ B := by
  rw [length_pos]; unfold bndX at hB; omega

theorem zero_sem (hB : bndX V x ≤ B) (n : ℕ) :
    Good (ipTree V) x B n (pos 6 0 [] [] [] []) ∧ val (ipTree V) x n (pos 6 0 [] [] [] []) = 0 := by
  have := good_leaf (ipTree V) x B (p := pos 6 0 [] [] [] []) (by simp [isLeaf_six])
    (pos_le V x B hB (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)) n
  rw [lv_zero V x 6 0 [] [] [] [] (by omega)] at this
  simpa using this

theorem cnt_sem (hB : bndX V x ≤ B) (t : Word)
    (ht : t.length ≤ V.numRounds x * (4 * V.maxMsg x + 2)) :
    ∀ (e : ℕ) (s : Word), s.length + e = V.numCoins x → ∀ n, e ≤ n →
      Good (ipTree V) x B n (pos 5 0 t [] [] s) ∧
        val (ipTree V) x n (pos 5 0 t [] [] s) =
          sumL e (fun ρ => if leafOK V x t (s.reverse ++ ρ) then 1 else 0)
  | 0, s, hs, n, _ => by
      have hp := pos_le V x B hB (tag := 5) (k := 0) (q := []) (a := []) (s := s) (by omega)
        (by omega) ht (by simp) (by simp) (by omega)
      have hl : (ipTree V).isLeaf.eval [x, pos 5 0 t [] [] s] ≠ [] := by
        rw [isLeaf_five]; simp [bw]; omega
      refine ⟨(good_leaf _ x B hl hp n).1, ?_⟩
      rw [(good_leaf _ x B hl hp n).2, lv_five, nv_bw]
      rw [sumL_zero, List.append_nil]
      cases leafOK V x t s.reverse <;> rfl
  | e + 1, s, hs, n, hn => by
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hp := pos_le V x B hB (tag := 5) (k := 0) (q := []) (a := []) (s := s) (by omega)
        (by omega) ht (by simp) (by simp) (by omega)
      have hl : (ipTree V).isLeaf.eval [x, pos 5 0 t [] [] s] = [] := by
        rw [isLeaf_five]; simp [bw]; omega
      obtain ⟨g0, v0⟩ := cnt_sem hB t ht e (false :: s) (by simp; omega) n (by omega)
      obtain ⟨g1, v1⟩ := cnt_sem hB t ht e (true :: s) (by simp; omega) n (by omega)
      refine ⟨good_inner _ x B hp (by rwa [c0_cnt]) (by rwa [c1_cnt]), ?_⟩
      rw [val_sum _ x hl (isMax_sum V x 5 0 t [] [] s (by omega)), c0_cnt, c1_cnt, v0, v1,
        sumL_succ, Fintype.sum_bool]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      ring

/-- The depth of the tree below a node `0` with `k` rounds left. -/
def dep (k : ℕ) : ℕ := V.numCoins x + 1 + k * (4 * V.maxMsg x + 3)

/-- The statement that the node `0` with `k` rounds left has the value of the game. -/
def RndOK (k : ℕ) : Prop :=
  ∀ t : Word, t.length + k * (4 * V.maxMsg x + 2) ≤ V.numRounds x * (4 * V.maxMsg x + 2) →
    ∀ n, dep V x k ≤ n →
      Good (ipTree V) x B n (pos 0 k t [] [] []) ∧ val (ipTree V) x n (pos 0 k t [] [] []) = F V x k t

theorem ma_sem (hB : bndX V x ≤ B) (k : ℕ) (hk : k + 1 ≤ V.numRounds x) (IH : RndOK V x B k)
    (t q : Word)
    (ht : t.length + (k + 1) * (4 * V.maxMsg x + 2) ≤ V.numRounds x * (4 * V.maxMsg x + 2))
    (hq : q.length ≤ V.maxMsg x) :
    ∀ (e : ℕ) (a : Word), a.length + e = V.maxMsg x → ∀ n, dep V x k + 1 + 2 * e ≤ n →
      Good (ipTree V) x B n (pos 3 k t q a []) ∧
        val (ipTree V) x n (pos 3 k t q a []) =
          supW e (fun a' => F V x k (t ++ encMsg q ++ encMsg a')) a
  | e, a, ha, n, hn => by
      have hP : (k + 1) * (4 * V.maxMsg x + 2) = k * (4 * V.maxMsg x + 2) + (4 * V.maxMsg x + 2) :=
        Nat.succ_mul _ _
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hp := pos_le V x B hB (tag := 3) (k := k) (t := t) (q := q) (a := a) (s := [])
        (by omega) (by omega) (by omega) hq (by omega) (by simp)
      have hl := isLeaf_inner V x 3 k t q a [] (by omega)
      obtain ⟨g0, v0⟩ := IH (t ++ encMsg q ++ encMsg a) (by simp; omega) n (by omega)
      have hp4 := pos_le V x B hB (tag := 4) (k := k) (t := t) (q := q) (a := a) (s := [])
        (by omega) (by omega) (by omega) hq (by omega) (by simp)
      have key : Good (ipTree V) x B n (pos 4 k t q a []) ∧
          val (ipTree V) x n (pos 4 k t q a []) =
            (match e with
              | 0 => 0
              | e + 1 => max (supW e (fun a' => F V x k (t ++ encMsg q ++ encMsg a')) (false :: a))
                  (supW e (fun a' => F V x k (t ++ encMsg q ++ encMsg a')) (true :: a))) := by
        cases e with
        | zero =>
            have hl4 : (ipTree V).isLeaf.eval [x, pos 4 k t q a []] ≠ [] := by
              rw [isLeaf_four]; simp [bw]; omega
            obtain ⟨g, v⟩ := good_leaf _ x B hl4 hp4 n
            refine ⟨g, ?_⟩
            rw [v, lv_zero V x 4 k t q a [] (by omega)]
            rfl
        | succ e =>
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hl4 : (ipTree V).isLeaf.eval [x, pos 4 k t q a []] = [] := by
              rw [isLeaf_four]; simp [bw]; omega
            obtain ⟨g0', v0'⟩ := ma_sem hB k hk IH t q ht hq e (false :: a) (by simp; omega) m
              (by omega)
            obtain ⟨g1', v1'⟩ := ma_sem hB k hk IH t q ht hq e (true :: a) (by simp; omega) m
              (by omega)
            refine ⟨good_inner _ x B hp4 (by rwa [c0_me]) (by rwa [c1_me]), ?_⟩
            rw [val_max _ x hl4 (by rw [isMax_max V x 4 k t q a [] (by omega)]; simp), c0_me, c1_me,
              v0', v1']
      obtain ⟨g4, v4⟩ := key
      refine ⟨good_inner _ x B hp (by rwa [c0_ma]) (by rwa [c1_ma]), ?_⟩
      rw [val_max _ x hl (by rw [isMax_max V x 3 k t q a [] (by omega)]; simp), c0_ma, c1_ma, v0, v4]
      cases e with
      | zero => simp [supW]
      | succ e => simp [supW]

/-- The value of a node `3` with an empty answer. -/
def gq (k : ℕ) (t q : Word) : ℕ := supW (V.maxMsg x) (fun a => F V x k (t ++ encMsg q ++ encMsg a)) []

theorem sq_sem (hB : bndX V x ≤ B) (k : ℕ) (hk : k + 1 ≤ V.numRounds x) (IH : RndOK V x B k)
    (t : Word)
    (ht : t.length + (k + 1) * (4 * V.maxMsg x + 2) ≤ V.numRounds x * (4 * V.maxMsg x + 2)) :
    ∀ (e : ℕ) (q : Word), q.length + e = V.maxMsg x → ∀ n, dep V x k + 2 * V.maxMsg x + 2 + 2 * e ≤ n →
      Good (ipTree V) x B n (pos 1 k t q [] []) ∧
        val (ipTree V) x n (pos 1 k t q [] []) = sumW e (gq V x k t) q
  | e, q, hq, n, hn => by
      have hP : (k + 1) * (4 * V.maxMsg x + 2) = k * (4 * V.maxMsg x + 2) + (4 * V.maxMsg x + 2) :=
        Nat.succ_mul _ _
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hp := pos_le V x B hB (tag := 1) (k := k) (t := t) (q := q) (a := []) (s := [])
        (by omega) (by omega) (by omega) (by omega) (by simp) (by simp)
      have hl := isLeaf_inner V x 1 k t q [] [] (by omega)
      obtain ⟨g0, v0⟩ := ma_sem V x B hB k hk IH t q ht (by omega) (V.maxMsg x) [] (by simp) n
        (by omega)
      have hp2 := pos_le V x B hB (tag := 2) (k := k) (t := t) (q := q) (a := []) (s := [])
        (by omega) (by omega) (by omega) (by omega) (by simp) (by simp)
      have key : Good (ipTree V) x B n (pos 2 k t q [] []) ∧
          val (ipTree V) x n (pos 2 k t q [] []) =
            (match e with
              | 0 => 0
              | e + 1 => sumW e (gq V x k t) (false :: q) + sumW e (gq V x k t) (true :: q)) := by
        cases e with
        | zero =>
            have hl2 : (ipTree V).isLeaf.eval [x, pos 2 k t q [] []] ≠ [] := by
              rw [isLeaf_two]; simp [bw]; omega
            obtain ⟨g, v⟩ := good_leaf _ x B hl2 hp2 n
            refine ⟨g, ?_⟩
            rw [v, lv_zero V x 2 k t q [] [] (by omega)]
            rfl
        | succ e =>
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hl2 : (ipTree V).isLeaf.eval [x, pos 2 k t q [] []] = [] := by
              rw [isLeaf_two]; simp [bw]; omega
            obtain ⟨g0', v0'⟩ := sq_sem hB k hk IH t ht e (false :: q) (by simp; omega) m
              (by omega)
            obtain ⟨g1', v1'⟩ := sq_sem hB k hk IH t ht e (true :: q) (by simp; omega) m
              (by omega)
            refine ⟨good_inner _ x B hp2 (by rwa [c0_se]) (by rwa [c1_se]), ?_⟩
            rw [val_sum _ x hl2 (isMax_sum V x 2 k t q [] [] (by omega)), c0_se, c1_se, v0', v1']
      obtain ⟨g2, v2⟩ := key
      refine ⟨good_inner _ x B hp (by rwa [c0_sq]) (by rwa [c1_sq]), ?_⟩
      rw [val_sum _ x hl (isMax_sum V x 1 k t q [] [] (by omega)), c0_sq, c1_sq, v0, v2]
      cases e with
      | zero => simp [sumW, gq]
      | succ e => simp [sumW, gq]

/-- **The node `0` has the value of the game.** -/
theorem rnd_sem (hB : bndX V x ≤ B) : ∀ k, k ≤ V.numRounds x → RndOK V x B k
  | 0, _ => by
      intro t ht n hn
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by unfold dep at hn; omega⟩
      have hp := pos_le V x B hB (tag := 0) (k := 0) (t := t) (q := []) (a := []) (s := [])
        (by omega) (by omega) (by omega) (by simp) (by simp) (by simp)
      have hl := isLeaf_inner V x 0 0 t [] [] [] (by omega)
      obtain ⟨g0, v0⟩ := cnt_sem V x B hB t (by omega) (V.numCoins x) [] (by simp) n
        (by unfold dep at hn; omega)
      obtain ⟨g1, v1⟩ := zero_sem V x B hB n
      refine ⟨good_inner _ x B hp (by rwa [c0_rnd_zero]) (by rwa [c1_rnd]), ?_⟩
      rw [val_sum _ x hl (isMax_sum V x 0 0 t [] [] [] (by omega)), c0_rnd_zero, c1_rnd, v0, v1]
      simp only [List.reverse_nil, List.nil_append, Nat.add_zero]
      rfl
  | k + 1, hk => by
      intro t ht n hn
      have hd : dep V x (k + 1) = dep V x k + 4 * V.maxMsg x + 3 := by unfold dep; ring
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hp := pos_le V x B hB (tag := 0) (k := k + 1) (t := t) (q := []) (a := []) (s := [])
        (by omega) hk (by omega) (by simp) (by simp) (by simp)
      have hl := isLeaf_inner V x 0 (k + 1) t [] [] [] (by omega)
      obtain ⟨g0, v0⟩ := sq_sem V x B hB k hk (rnd_sem hB k (by omega)) t ht (V.maxMsg x) [] (by simp)
        n (by omega)
      obtain ⟨g1, v1⟩ := zero_sem V x B hB n
      refine ⟨good_inner _ x B hp (by rwa [c0_rnd_succ]) (by rwa [c1_rnd]), ?_⟩
      rw [val_sum _ x hl (isMax_sum V x 0 (k + 1) t [] [] [] (by omega)), c0_rnd_succ, c1_rnd, v0, v1]
      rfl

end Semantics

/-! ### `IP = PSPACE` -/

section Main

/-- The root of the game tree: the node `0` with all the rounds left and the empty transcript. -/
def rootT (V : Verifier) : Cob :=
  posT 0 (Cob.unary (.comp V.rounds [.proj 0])) .empty .empty .empty .empty

theorem eval_rootT (V : Verifier) (x : Word) :
    (rootT V).eval [x] = pos 0 (V.numRounds x) [] [] [] [] := by
  simp [rootT, pos, un, Verifier.numRounds]

/-- A polynomial in the input length, bounding the length of the value of a Cobham term. -/
theorem exists_poly (c : Cob) : ∃ p : ℕ → ℕ, PolyBound p ∧
    ∀ x : Word, (c.eval [x]).length ≤ p x.length := by
  obtain ⟨a, k, h⟩ := Cob.polyLen c
  exact ⟨fun n => a * (n + 1) ^ k, ⟨a, k, fun n => le_rfl⟩, fun x => by simpa using h [x]⟩

/-- **`IP ⊆ PSPACE`.** -/
theorem ip_subset_pspace {L : Language} (h : IP L) : Space.PSPACE L := by
  obtain ⟨V, hV⟩ := h
  obtain ⟨pr, hpr, hr⟩ := exists_poly V.rounds
  obtain ⟨pc, hpc, hc⟩ := exists_poly V.coins
  obtain ⟨pm, hpm, hm⟩ := exists_poly V.msgLen
  let fuel : ℕ → ℕ := fun n => pc n + 1 + pr n * (4 * pm n + 3)
  let B : ℕ → ℕ := fun n => 2 * (6 + pr n + pr n * (4 * pm n + 2) + 2 * pm n + pc n) + 6
  have hfuel : PolyBound fuel :=
    (hpc.add (polyBound_const 1)).add (hpr.mul (((polyBound_const 4).mul hpm).add
      (polyBound_const 3)))
  have hBp : PolyBound B :=
    ((polyBound_const 2).mul (((((polyBound_const 6).add hpr).add
      (hpr.mul (((polyBound_const 4).mul hpm).add (polyBound_const 2)))).add
      ((polyBound_const 2).mul hpm)).add hpc)).add (polyBound_const 6)
  have key : ∀ x : Word, Good (ipTree V) x (B x.length) (fuel x.length) ((rootT V).eval [x]) ∧
      val (ipTree V) x (fuel x.length) ((rootT V).eval [x]) = F V x (V.numRounds x) [] := by
    intro x
    have h1 := hr x
    have h2 := hc x
    have h3 := hm x
    have hB : bndX V x ≤ B x.length := by
      have := Nat.mul_le_mul h1 (show 4 * V.maxMsg x + 2 ≤ 4 * pm x.length + 2 by
        unfold Verifier.maxMsg; omega)
      unfold bndX Verifier.numRounds Verifier.numCoins Verifier.maxMsg at *
      simp only [B]; omega
    have hd : dep V x (V.numRounds x) ≤ fuel x.length := by
      have := Nat.mul_le_mul h1 (show 4 * V.maxMsg x + 3 ≤ 4 * pm x.length + 3 by
        unfold Verifier.maxMsg; omega)
      unfold dep Verifier.numRounds Verifier.numCoins Verifier.maxMsg at *
      simp only [fuel]; omega
    rw [eval_rootT]
    exact rnd_sem V x _ hB _ le_rfl [] (by simp) _ hd
  refine pspace_of_ctree (ipTree V) (rootT V) V.coins L fuel B hfuel hBp (fun x => (key x).1)
    (fun x => ?_)
  rw [(key x).2]
  change L x ↔ 2 ^ V.numCoins x ≤ 2 * F V x (V.numRounds x) []
  have hpos : (0 : ℚ) < 2 ^ V.numCoins x := by positivity
  constructor
  · intro hx
    obtain ⟨P, hP⟩ := (hV x).1 hx
    have hle := accCount_le_F V x P
    unfold Verifier.accProb at hP
    rw [le_div_iff₀ hpos] at hP
    have : (2 : ℚ) * 2 ^ V.numCoins x ≤ 3 * F V x (V.numRounds x) [] := by
      have : (V.accCount P x : ℚ) ≤ F V x (V.numRounds x) [] := by exact_mod_cast hle
      linarith
    have : 2 * 2 ^ V.numCoins x ≤ 3 * F V x (V.numRounds x) [] := by exact_mod_cast this
    omega
  · intro hle
    by_contra hx
    obtain ⟨P, hP⟩ := exists_F_le_accCount V x
    have h3 := (hV x).2 hx P
    unfold Verifier.accProb at h3
    rw [div_le_iff₀ hpos] at h3
    have : (3 : ℚ) * V.accCount P x ≤ 2 ^ V.numCoins x := by linarith
    have : 3 * V.accCount P x ≤ 2 ^ V.numCoins x := by exact_mod_cast this
    have : 0 < 2 ^ V.numCoins x := by positivity
    omega

/-- **Shamir's theorem: `IP = PSPACE`.** -/
theorem ip_eq_pspace {L : Language} : IP L ↔ Space.PSPACE L :=
  ⟨ip_subset_pspace, pspace_subset_ip⟩

end Main

end Complexity.IPSpace

/-- **Shamir's theorem: `IP = PSPACE`** (the statement named in the task board). -/
theorem Complexity.ip_eq_pspace {L : Complexity.Language} :
    Complexity.IP L ↔ Complexity.Space.PSPACE L :=
  Complexity.IPSpace.ip_eq_pspace
