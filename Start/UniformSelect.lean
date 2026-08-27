/-
**Reading one gate off the description of a circuit.**

Every rule of the algebra of P-uniform families built so far writes the gate with identifier `c`
out of *arithmetic* on `c`: a template, a finite-state control, a Euclidean division.  A compiler
that unrolls a loop whose body is itself a compiled circuit needs something else — it has to copy
the gates of a circuit it is *given*, in the form of its description.

This module supplies that operation.  `Complexity.CircCode.selTokTerm` is a Cobham term which,
from the code of a circuit and from `1^o`, writes the token of the gate of that circuit whose
identifier is `o`.  It is the block-emitting recursion of `Start/CobhamBlock.lean` run over the
code with the finite-state control of `Start/CircuitCode.lean`: at every marker the counter holds
the identifier of the gate whose token starts there, so the recursion has only to compare that
counter with `o` — a comparison of two words of ones — and to re-emit the token it is reading when
they agree.

Main definitions:

* `Complexity.CircCode.gateId` — the gate of a circuit with a given identifier;
* `Complexity.CircCode.selF` — the per-gate translation that keeps one gate and deletes the others;
* `Complexity.CircCode.selTokTerm` — the Cobham term.

Main results:

* `Complexity.CircCode.gmap_selF` — the translation writes the token of that gate;
* `Complexity.CircCode.eval_selTokTerm` — **the term computes it**;
* `Complexity.CircCode.eval_selTokTerm_lt` — in the form used later: from the code of `C` and
  `1^o` with `o < |C|`, the term writes `encGate (gateId C o)`.
-/

import Start.UniformCompose
import Start.UniformLayerPad

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The gate with a given identifier -/

/-- The gate of a circuit whose identifier is `o`, that is, the gate with `o` gates below it.
Out of range the value is the constant `false`, which is never used. -/
def gateId : Circuit → ℕ → Gate
  | [], _ => .cst false
  | g :: C, o => if o = C.length then g else gateId C o

theorem gateId_cons_self (g : Gate) (C : Circuit) : gateId (g :: C) C.length = g := by
  rw [gateId, if_pos rfl]

theorem gateId_cons_of_ne {g : Gate} {C : Circuit} {o : ℕ} (h : o ≠ C.length) :
    gateId (g :: C) o = gateId C o := by
  rw [gateId, if_neg h]

/-- Two templates agreeing below `n` give the same layer. -/
theorem layer_congr {f g : ℕ → Gate} :
    ∀ {n : ℕ}, (∀ i, i < n → f i = g i) → layer f n = layer g n
  | 0, _ => rfl
  | n + 1, h => by
      rw [layer, layer, h n (Nat.lt_succ_self n),
        layer_congr (fun i hi => h i (Nat.lt_succ_of_lt hi))]

/-- The gates of a circuit, listed by identifier, are the gates of the circuit. -/
theorem map_gateId (F : Gate → Gate) :
    ∀ C : Circuit, layer (fun o => F (gateId C o)) C.length = C.map F
  | [] => rfl
  | g :: C => by
      have hrec : layer (fun o => F (gateId (g :: C) o)) C.length
          = layer (fun o => F (gateId C o)) C.length := by
        refine layer_congr ?_
        intro o ho
        rw [gateId_cons_of_ne (Nat.ne_of_lt ho)]
      simp only [List.length_cons, layer, List.map_cons]
      rw [gateId_cons_self, hrec, map_gateId F C]

/-! ### Keeping one gate -/

/-- The per-gate translation that emits the token of the gate with identifier `o` and nothing
else. -/
def selF (o : ℕ) : ℕ → Gate → Word := fun c g => if c = o then encGate g else []

theorem gmap_selF_of_le {C : Circuit} {o : ℕ} (h : C.length ≤ o) : gmap (selF o) C = [] := by
  induction C with
  | nil => rfl
  | cons g C ih =>
      have hlt : C.length < o := by simpa using h
      rw [gmap, selF, if_neg (Nat.ne_of_lt hlt), ih (le_of_lt hlt), List.append_nil]

/-- **The translation writes the token of the gate with identifier `o`.** -/
theorem gmap_selF {C : Circuit} {o : ℕ} (h : o < C.length) :
    gmap (selF o) C = encGate (gateId C o) := by
  induction C with
  | nil => simp at h
  | cons g C ih =>
      rcases eq_or_ne o C.length with rfl | hne
      · rw [gmap, selF, if_pos rfl, gateId_cons_self, gmap_selF_of_le (le_refl _),
          List.append_nil]
      · have hlt : o < C.length := by
          have : o < C.length + 1 := by simpa using h
          omega
        rw [gmap, selF, if_neg (Ne.symm hne), List.nil_append, ih hlt, gateId_cons_of_ne hne]

/-! ### The Cobham term -/

/-- The test `c ≠ o`, the two numbers being given in unary as the second and the third argument:
the word is empty exactly when they agree. -/
def neqT : Cob :=
  .comp Cob.concat [.comp Cob.dropU [.proj 1, .proj 2], .comp Cob.dropU [.proj 2, .proj 1]]

theorem eval_neqT (y : Word) (c o : ℕ) :
    neqT.eval [y, List.replicate c true, List.replicate o true]
      = List.replicate (o - c) true ++ List.replicate (c - o) true := by
  simp [neqT]

theorem eval_neqT_eq_nil_iff (y : Word) (c o : ℕ) :
    neqT.eval [y, List.replicate c true, List.replicate o true] = [] ↔ c = o := by
  rw [eval_neqT]
  constructor
  · intro h
    have h1 : o - c = 0 ∧ c - o = 0 := by
      have := congrArg List.length h
      simp only [List.length_append, List.length_replicate, List.length_nil] at this
      omega
    omega
  · rintro rfl
    simp

/-- Guarding a token-writing term by the test `c = o`. -/
def selGuard (t : Cob) : Cob := .comp Cob.iteC [neqT, .empty, t]

theorem eval_selGuard (t : Cob) (y : Word) (c o : ℕ) :
    (selGuard t).eval [y, List.replicate c true, List.replicate o true]
      = if c = o then t.eval [y, List.replicate c true, List.replicate o true] else [] := by
  rw [selGuard]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_empty]
  by_cases h : c = o
  · rw [if_pos ((eval_neqT_eq_nil_iff y c o).2 h), if_pos h]
  · rw [if_neg (fun hc => h ((eval_neqT_eq_nil_iff y c o).1 hc)), if_neg h]

/-- The token of an input gate, copied. -/
def cpInpT : Cob := Cob.catL [Cob.constT [false, true, false], uFldA1, Cob.constT [false, true]]

/-- The token of a negation gate, copied. -/
def cpNegT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, false], uFldA1, Cob.constT [false, true]]

/-- The token of a conjunction gate, copied. -/
def cpConjT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, false], uFldA1,
    Cob.constT [false], uFldB1]

/-- The token of a disjunction gate, copied. -/
def cpDisjT : Cob :=
  Cob.catL [Cob.constT [false, true, true, true, true, true, true, false], uFldA1,
    Cob.constT [false], uFldB1]

/-- The term emitted at each state and bit by the selecting recursion. -/
def selBlkT (s : ℕ) (b : Bool) : Cob :=
  if b then .empty
  else
    match s with
    | 3 => selGuard cpInpT
    | 4 => selGuard (Cob.constT (encGate (.cst false)))
    | 5 => selGuard (Cob.constT (encGate (.cst true)))
    | 6 => selGuard cpNegT
    | 7 => selGuard cpConjT
    | 8 => selGuard cpDisjT
    | _ => .empty

theorem eval_selBlkT (y : Word) (s : ℕ) (b : Bool) (c o : ℕ) :
    (selBlkT s b).eval [y, List.replicate c true, List.replicate o true]
      = gblk (selF o) s b y c := by
  cases b with
  | true => simp [selBlkT, gblk]
  | false =>
      rcases Nat.lt_or_ge s 9 with h9 | h9
      · interval_cases s
        · simp [selBlkT, gblk, emits]
        · simp [selBlkT, gblk, emits]
        · simp [selBlkT, gblk, emits]
        · rw [show selBlkT 3 false = selGuard cpInpT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 3 y = Gate.inp (fldA y) from rfl, eval_selGuard, selF]
          by_cases h : c = o
          · rw [if_pos h, if_pos h, cpInpT]
            simp [encGate, tag, fld1, fld2, List.replicate_succ]
          · rw [if_neg h, if_neg h]
        · rw [show selBlkT 4 false = selGuard (Cob.constT (encGate (.cst false))) from rfl, gblk,
            if_pos (by simp [emits]), show readGate 4 y = Gate.cst false from rfl,
            eval_selGuard, selF]
          by_cases h : c = o
          · rw [if_pos h, if_pos h]; simp
          · rw [if_neg h, if_neg h]
        · rw [show selBlkT 5 false = selGuard (Cob.constT (encGate (.cst true))) from rfl, gblk,
            if_pos (by simp [emits]), show readGate 5 y = Gate.cst true from rfl,
            eval_selGuard, selF]
          by_cases h : c = o
          · rw [if_pos h, if_pos h]; simp
          · rw [if_neg h, if_neg h]
        · rw [show selBlkT 6 false = selGuard cpNegT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 6 y = Gate.neg (fldA y) from rfl, eval_selGuard, selF]
          by_cases h : c = o
          · rw [if_pos h, if_pos h, cpNegT]
            simp [encGate, tag, fld1, fld2, List.replicate_succ]
          · rw [if_neg h, if_neg h]
        · rw [show selBlkT 7 false = selGuard cpConjT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 7 y = Gate.conj (fldA y) (fldB y) from rfl, eval_selGuard, selF]
          by_cases h : c = o
          · rw [if_pos h, if_pos h, cpConjT]
            simp [encGate, tag, fld1, fld2, List.replicate_succ]
          · rw [if_neg h, if_neg h]
        · rw [show selBlkT 8 false = selGuard cpDisjT from rfl, gblk, if_pos (by simp [emits]),
            show readGate 8 y = Gate.disj (fldA y) (fldB y) from rfl, eval_selGuard, selF]
          by_cases h : c = o
          · rw [if_pos h, if_pos h, cpDisjT]
            simp [encGate, tag, fld1, fld2, List.replicate_succ]
          · rw [if_neg h, if_neg h]
      · obtain ⟨k, rfl⟩ : ∃ k, s = k + 9 := ⟨s - 9, by omega⟩
        simp [selBlkT, gblk, emits]

theorem length_gblk_selF (y : Word) (s : ℕ) (b : Bool) (c o : ℕ) :
    (gblk (selF o) s b y c).length ≤ 11 * (y.length + o + 1) := by
  rw [gblk]
  split_ifs with h
  · rw [selF]
    split_ifs with hc
    · rw [length_encGate]
      have ht := (tag_le (readGate s y)).2
      have h1 := fld1_readGate_le (y := y) s
      have h2 := fld2_readGate_le (y := y) s
      omega
    · simp
  · simp

/-- **The Cobham term selecting one gate off a description**: run over the code of a circuit with
`1^o` as parameter, it writes the token of the gate with identifier `o`. -/
def selTokTerm : Cob := blkRunTerm 10 dstate cinc selBlkT 1 11

theorem eval_selTokTerm (C : Circuit) (o : ℕ) :
    selTokTerm.eval [encCirc C, List.replicate o true] = gmap (selF o) C := by
  rw [selTokTerm, eval_blkRunTerm (by norm_num) dstate_lt cinc_le selBlkT
    (List.replicate o true) (fun s b y c => eval_selBlkT y s b c o)
    (fun s b y c _ => by simpa using length_gblk_selF y s b c o), brun_gmap]

/-- **The term writes the token of the gate with identifier `o`.** -/
theorem eval_selTokTerm_lt {C : Circuit} {o : ℕ} (h : o < C.length) :
    selTokTerm.eval [encCirc C, List.replicate o true] = encGate (gateId C o) := by
  rw [eval_selTokTerm, gmap_selF h]

end CircCode

end Complexity
