/-
**The Tseitin translation is a Cobham function.**

`Start/CircuitCode.lean` writes a circuit as a word and exhibits its Tseitin translation as a
block-emitting recursion.  This module supplies the Cobham terms: one term per kind of gate,
computing the code of the CNF defining that gate from the suffix of the word (which carries the
references of the gate) and from the counter (which carries its identifier).  Feeding those terms
to `Complexity.blkRunTerm` gives a single Cobham term taking the code of a circuit to the code of
its Tseitin translation.

Main definitions:

* `Complexity.CircCode.blkT` — the term emitted at each state;
* `Complexity.CircCode.tseitinTerm` — the Cobham term of the Tseitin translation.

Main results:

* `Complexity.CircCode.eval_tseitinTerm` — **the Tseitin translation is a Cobham function**: one
  term takes the code of a circuit to the code of an equisatisfiable CNF.
-/

import Start.CircuitCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Gadgets -/

/-- The concatenation of a list of terms. -/
def Cob.catL : List Cob → Cob
  | [] => .empty
  | [t] => t
  | t :: ts => .comp Cob.concat [t, Cob.catL ts]

@[simp] theorem Cob.eval_catL (ts : List Cob) (args : List Word) :
    (Cob.catL ts).eval args = (ts.map (fun t => t.eval args)).flatten := by
  induction ts with
  | nil => simp [Cob.catL]
  | cons t ts ih =>
      cases ts with
      | nil => simp [Cob.catL]
      | cons t' ts' => simp [Cob.catL, ih]

/-- A constant word. -/
def Cob.constT (w : Word) : Cob := Cob.pre w .empty

@[simp] theorem Cob.eval_constT (w : Word) (args : List Word) :
    (Cob.constT w).eval args = w := by simp [Cob.constT]

/-- `1^{2k+1}` from `1^k`. -/
def Cob.oddU (t : Cob) : Cob := .comp (.app true) [.comp Cob.concat [t, t]]

theorem Cob.eval_oddU {t : Cob} {args : List Word} {k : ℕ}
    (h : t.eval args = List.replicate k true) :
    (Cob.oddU t).eval args = List.replicate (2 * k + 1) true := by
  simp only [Cob.oddU, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, h,
    Cob.eval_app, List.getD_cons_zero, ← List.replicate_add]
  rw [show k + k = 2 * k by ring, ← List.replicate_succ]

/-- `1^{2(k-1)+1}` from `1^k`. -/
def Cob.oddUm1 (t : Cob) : Cob := Cob.oddU (.comp Cob.tail [t])

theorem Cob.eval_oddUm1 {t : Cob} {args : List Word} {k : ℕ}
    (h : t.eval args = List.replicate k true) :
    (Cob.oddUm1 t).eval args = List.replicate (2 * (k - 1) + 1) true := by
  refine Cob.eval_oddU ?_
  cases args with
  | nil => simp [h, List.tail_replicate]
  | cons a as => simp [h, List.tail_replicate]

/-- `1^{2(k-1)}` from `1^k`. -/
def Cob.evenUm1 (t : Cob) : Cob :=
  .comp Cob.tail [.comp Cob.tail [.comp Cob.concat [t, t]]]

theorem Cob.eval_evenUm1 {t : Cob} {args : List Word} {k : ℕ}
    (h : t.eval args = List.replicate k true) :
    (Cob.evenUm1 t).eval args = List.replicate (2 * (k - 1)) true := by
  simp only [Cob.evenUm1, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, h,
    Cob.eval_tail, ← List.replicate_add, List.tail_replicate]
  congr 1
  omega

namespace CircCode

open Complexity.Tseitin

/-! ### The unary fields available at a marker -/

/-- The identifier of the gate, doubled and shifted: `1^{2c+1}` from the counter `1^c`. -/
def uCnt : Cob := Cob.oddU (.proj 1)

/-- The first field of the token, in unary and shifted by one. -/
def uFldA : Cob := .comp Cob.leadOnes [.comp Cob.tail [.comp Cob.dropOnes [.proj 0]]]

/-- The second field of the token, in unary and shifted by one. -/
def uFldB : Cob :=
  .comp Cob.leadOnes [.comp Cob.tail [.comp Cob.dropOnes [.comp Cob.tail
    [.comp Cob.dropOnes [.proj 0]]]]]

/-- The variable of the first reference: `1^{2a+1}`. -/
def uA : Cob := Cob.oddUm1 uFldA

/-- The variable of the second reference: `1^{2b+1}`. -/
def uB : Cob := Cob.oddUm1 uFldB

/-- The variable of a circuit input: `1^{2a}`. -/
def uA0 : Cob := Cob.evenUm1 uFldA

variable (y u p : Word)

@[simp] theorem eval_uFldA : uFldA.eval [y, u, p] = List.replicate (lead1 (drop1 y).tail) true := by
  simp [uFldA]

@[simp] theorem eval_uFldB :
    uFldB.eval [y, u, p] = List.replicate (lead1 (drop1 (drop1 y).tail).tail) true := by
  simp [uFldB]

@[simp] theorem eval_uCnt (c : ℕ) :
    uCnt.eval [y, List.replicate c true, p] = List.replicate (2 * c + 1) true :=
  Cob.eval_oddU (by simp)

@[simp] theorem eval_uA : uA.eval [y, u, p] = List.replicate (2 * fldA y + 1) true :=
  Cob.eval_oddUm1 (eval_uFldA y u p)

@[simp] theorem eval_uB : uB.eval [y, u, p] = List.replicate (2 * fldB y + 1) true :=
  Cob.eval_oddUm1 (eval_uFldB y u p)

@[simp] theorem eval_uA0 : uA0.eval [y, u, p] = List.replicate (2 * fldA y) true := by
  have := Cob.eval_evenUm1 (eval_uFldA y u p)
  rwa [uA0]

/-! ### One term per kind of gate -/

/-- The term for an input gate. -/
def inpT : Cob :=
  Cob.catL [Cob.constT [false, false, false, true, false], uCnt, Cob.constT [true, false, false],
    uA0, Cob.constT [false, false, false, true, false, false], uCnt, Cob.constT [true, false], uA0]

/-- The term for the constant `false`. -/
def cstFT : Cob := Cob.catL [Cob.constT [false, false, false, true, false], uCnt]

/-- The term for the constant `true`. -/
def cstTT : Cob := Cob.catL [Cob.constT [false, false, false, true, false, false], uCnt]

/-- The term for a negation gate. -/
def negT : Cob :=
  Cob.catL [Cob.constT [false, false, false, true, false], uCnt, Cob.constT [true, false], uA,
    Cob.constT [false, false, false, true, false, false], uCnt, Cob.constT [true, false, false], uA]

/-- The term for a conjunction gate. -/
def conjT : Cob :=
  Cob.catL [Cob.constT [false, false, false, true, false], uCnt, Cob.constT [true, false, false],
    uA, Cob.constT [false, false, false, true, false], uCnt, Cob.constT [true, false, false], uB,
    Cob.constT [false, false, false, true, false, false], uCnt, Cob.constT [true, false], uA,
    Cob.constT [true, false], uB]

/-- The term for a disjunction gate. -/
def disjT : Cob :=
  Cob.catL [Cob.constT [false, false, false, true, false, false], uCnt, Cob.constT [true, false],
    uA, Cob.constT [false, false, false, true, false, false], uCnt, Cob.constT [true, false], uB,
    Cob.constT [false, false, false, true, false], uCnt, Cob.constT [true, false, false], uA,
    Cob.constT [true, false, false], uB]

theorem eval_inpT (c : ℕ) :
    inpT.eval [y, List.replicate c true, p] = Sat.encCnf (gateCnf c (.inp (fldA y))) := by
  simp [inpT, Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf]

theorem eval_cstFT (c : ℕ) :
    cstFT.eval [y, List.replicate c true, p] = Sat.encCnf (gateCnf c (.cst false)) := by
  simp [cstFT, Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf]

theorem eval_cstTT (c : ℕ) :
    cstTT.eval [y, List.replicate c true, p] = Sat.encCnf (gateCnf c (.cst true)) := by
  simp [cstTT, Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf]

theorem eval_negT (c : ℕ) :
    negT.eval [y, List.replicate c true, p] = Sat.encCnf (gateCnf c (.neg (fldA y))) := by
  simp [negT, Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf]

theorem eval_conjT (c : ℕ) :
    conjT.eval [y, List.replicate c true, p]
      = Sat.encCnf (gateCnf c (.conj (fldA y) (fldB y))) := by
  simp [conjT, Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf]

theorem eval_disjT (c : ℕ) :
    disjT.eval [y, List.replicate c true, p]
      = Sat.encCnf (gateCnf c (.disj (fldA y) (fldB y))) := by
  simp [disjT, Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf]

/-- The term emitted at each state and bit. -/
def blkT (s : ℕ) (b : Bool) : Cob :=
  if b then .empty
  else
    match s with
    | 3 => inpT
    | 4 => cstFT
    | 5 => cstTT
    | 6 => negT
    | 7 => conjT
    | 8 => disjT
    | _ => .empty

theorem eval_blkT (s : ℕ) (b : Bool) (c : ℕ) :
    (blkT s b).eval [y, List.replicate c true, p] = cblk s b y c := by
  cases b with
  | true => simp [blkT, cblk, gblk]
  | false =>
      rcases Nat.lt_or_ge s 9 with h9 | h9
      · interval_cases s
        · simp [blkT, cblk, gblk, emits]
        · simp [blkT, cblk, gblk, emits]
        · simp [blkT, cblk, gblk, emits]
        · rw [show blkT 3 false = inpT from rfl, cblk, gblk, if_pos (by simp [emits]),
            show readGate 3 y = Gate.inp (fldA y) from rfl, eval_inpT]
        · rw [show blkT 4 false = cstFT from rfl, cblk, gblk, if_pos (by simp [emits]),
            show readGate 4 y = Gate.cst false from rfl, eval_cstFT]
        · rw [show blkT 5 false = cstTT from rfl, cblk, gblk, if_pos (by simp [emits]),
            show readGate 5 y = Gate.cst true from rfl, eval_cstTT]
        · rw [show blkT 6 false = negT from rfl, cblk, gblk, if_pos (by simp [emits]),
            show readGate 6 y = Gate.neg (fldA y) from rfl, eval_negT]
        · rw [show blkT 7 false = conjT from rfl, cblk, gblk, if_pos (by simp [emits]),
            show readGate 7 y = Gate.conj (fldA y) (fldB y) from rfl, eval_conjT]
        · rw [show blkT 8 false = disjT from rfl, cblk, gblk, if_pos (by simp [emits]),
            show readGate 8 y = Gate.disj (fldA y) (fldB y) from rfl, eval_disjT]
      · obtain ⟨n, rfl⟩ : ∃ n, s = n + 9 := ⟨s - 9, by omega⟩
        simp [blkT, cblk, gblk, emits]

/-! ### The size of a block -/

theorem length_encCnf_gateCnf (j : ℕ) (g : Gate) :
    (Sat.encCnf (gateCnf j g)).length ≤ 37 + 14 * (j + fld1 g + fld2 g) := by
  cases g with
  | cst b =>
      cases b
      · simp [Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf, fld1, fld2]
        omega
      · simp [Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf, fld1, fld2]
        omega
  | _ =>
      simp [Sat.encCnf, Sat.encClause, Sat.encLit, gateCnf, fld1, fld2]
      omega

theorem length_tail_le (l : Word) : l.tail.length ≤ l.length := by
  cases l <;> simp

theorem fldA_le : fldA y ≤ y.length := by
  refine le_trans (Nat.sub_le _ _) (le_trans (lead1_le _) ?_)
  exact le_trans (length_tail_le _) (length_drop1 y)

theorem fldB_le : fldB y ≤ y.length := by
  refine le_trans (Nat.sub_le _ _) (le_trans (lead1_le _) ?_)
  refine le_trans (length_tail_le _) (le_trans (length_drop1 _) ?_)
  exact le_trans (length_tail_le _) (length_drop1 y)

theorem fld1_readGate_le (s : ℕ) : fld1 (readGate s y) ≤ y.length :=
  fld1_gateOf_le _ (fldA_le y)

theorem fld2_readGate_le (s : ℕ) : fld2 (readGate s y) ≤ y.length :=
  fld2_gateOf_le _ (fldB_le y)

theorem length_cblk (s : ℕ) (b : Bool) (c : ℕ) (hc : c ≤ y.length * 1) :
    (cblk s b y c).length ≤ 79 * (y.length + ([] : Word).length + 1) := by
  rw [cblk, gblk]
  split
  · refine le_trans (length_encCnf_gateCnf c (readGate s y)) ?_
    have h1 := fld1_readGate_le y s
    have h2 := fld2_readGate_le y s
    simp only [List.length_nil, Nat.add_zero]
    omega
  · simp

/-! ### The Cobham term of the Tseitin translation -/

/-- The Cobham term producing the code of the gate definitions from the code of a circuit. -/
def defsTerm : Cob := .comp (blkRunTerm 10 dstate cinc blkT 1 79) [.proj 0, .empty]

theorem eval_defsTerm (C : Circuit) : defsTerm.eval [encCirc C] = Sat.encCnf (defsCnf C) := by
  have h := eval_blkRunTerm (m := 10) (Ki := 1) (K := 79) (by norm_num) dstate_lt cinc_le blkT
    (blk := cblk) [] (fun s b y c => eval_blkT y [] s b c)
    (fun s b y c hc => length_cblk y s b c hc) (encCirc C)
  rw [defsTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    Cob.eval_empty]
  rw [h, brun_encCirc]

/-- The term producing the code of the clause asserting the output gate, from the number of gates
in unary. -/
def headU : Cob :=
  .bRec .empty
    (Cob.pre [true, false, false] (Cob.oddU (.proj 0)))
    (Cob.pre [true, false, false] (Cob.oddU (.proj 0)))
    (Cob.pre (List.replicate 4 true) (.comp .smash [.proj 0, Cob.constT [true, true]]))

theorem eval_headU_nil (rest : List Word) : headU.eval ([] :: rest) = [] := by
  simp [headU]

theorem eval_headU_succ (n : ℕ) (rest : List Word) :
    headU.eval (List.replicate (n + 1) true :: rest)
      = [true, false, false] ++ List.replicate (2 * n + 1) true := by
  have hb : (Cob.oddU (Cob.proj 0)).eval
      (List.replicate n true :: headU.eval (List.replicate n true :: rest) :: rest)
      = List.replicate (2 * n + 1) true := Cob.eval_oddU (by simp)
  rw [List.replicate_succ, headU, Cob.eval_bRec_cons, ← headU, ite_self, Cob.eval_pre,
    Cob.eval_pre, hb, List.take_of_length_le]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_constT,
    List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  omega

/-- **The Cobham term of the Tseitin translation.** -/
def tseitinTerm : Cob :=
  Cob.pre [false, false, false]
    (.comp Cob.concat [.comp headU [.comp (cntTerm 10 dstate cinc 1) [.proj 0]], defsTerm])

/-- **The Tseitin translation is a Cobham function**: a single Cobham term takes the code of a
circuit to the code of its Tseitin translation. -/
theorem eval_tseitinTerm (C : Circuit) :
    tseitinTerm.eval [encCirc C] = Sat.encCnf (toCnf C) := by
  have hcnt : (cntTerm 10 dstate cinc 1).eval [encCirc C] = List.replicate C.length true := by
    rw [eval_cntTerm (by norm_num) dstate_lt cinc_le (encCirc C) [], rcnt_encCirc]
  rw [tseitinTerm]
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
    Cob.eval_proj, List.getD_cons_zero, hcnt, eval_defsTerm]
  cases C with
  | nil => simp [eval_headU_nil, toCnf, Sat.encCnf, Sat.encClause, defsCnf]
  | cons g C =>
      rw [List.length_cons, eval_headU_succ]
      rw [toCnf]
      simp [Sat.encCnf, Sat.encClause, Sat.encLit]

end CircCode

end Complexity
