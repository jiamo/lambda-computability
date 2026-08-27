/-
# The description of the tableau, and P-uniform decidability for cellular automata

`Start/UniformCA.lean` builds, for a cellular automaton `A` over a fixed finite alphabet, the
tableau of its computation on a tape of width `W` for `H` steps, and shows that the tableau is a
well-formed circuit deciding the language of the automaton.  This module writes the description of
that tableau with a **single Cobham term**, and concludes that the language of a cellular
automaton whose tape and running time are Cobham functions of the length of the input is decided
by a P-uniform circuit family — hence reduces to SAT in polynomial time.

Because the alphabet is fixed, every row of the tableau falls in one of a *constant* number of
shapes, so the term is a finite table selected by the phase of the row inside its block; only the
index of the block, the width and the running time have to be computed, and they are all obtained
by Euclidean division in unary.

Main definitions:

* `Complexity.CircCode.caBlkT` — **the Cobham term writing the gate of the tableau** from its row,
  its column and the length of the input, all in unary;
* `Complexity.CALang`, `Complexity.CAUniform` — the language of a cellular automaton and the
  uniformity hypothesis on its tape and running time.

Main results:

* `Complexity.CircCode.eval_caBlkT` — the term writes exactly the gates of the tableau;
* `Complexity.codeUniform_caGrid` — **the descriptions of the tableaux are written by a single
  Cobham term**;
* `Complexity.pUniformDecidable_caLang` — **the language of a uniform cellular automaton is
  decided by a P-uniform circuit family**;
* `Complexity.polyManyOne_SAT_caLang` — and therefore reduces to SAT in polynomial time.
-/
import Start.UniformCA
import Start.UniformStateCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### Reading off a finite table -/

theorem getD_range_map (f : ℕ → Cob) {N p : ℕ} (h : p < N) :
    ((List.range N).map f).getD p Cob.empty = f p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

/-! ### The terms of the layout -/

/-- The width of the tableau, in unary. -/
def caWT (wT : Cob) : Cob := .comp wT [.proj 3]

/-- The number of steps, in unary. -/
def caHT (hT : Cob) : Cob := .comp hT [.proj 3]

/-- The index of the block of a row, in unary. -/
def caTT (K : ℕ) : Cob :=
  Cob.divT (Cob.tailN (caB K) (.proj 1)) (Cob.constT (List.replicate (caHb K) true))

/-- The phase of a row inside its block, in unary. -/
def caPhT (K : ℕ) : Cob :=
  Cob.modT (Cob.tailN (caB K) (.proj 1)) (Cob.constT (List.replicate (caHb K) true))

/-- A row of the tableau given by a constant. -/
def caRowK (c : ℕ) : Cob := Cob.constT (List.replicate c true)

/-- A row of the tableau given by `a + b * t`, the time `t` being computed by `tT`. -/
def caRowL (a : ℕ) (tT : Cob) (b : ℕ) : Cob :=
  Cob.pre (List.replicate a true) (.comp .smash [tT, Cob.constT (List.replicate b true)])

/-- The identifier of the gate at the row computed by `rowT` and the column computed by `jT`. -/
def caUid (wT rowT jT : Cob) : Cob := Cob.catL [.comp .smash [rowT, caWT wT], jT]

/-! ### The value of the terms of the layout -/

section Eval

variable {w h : ℕ → ℕ} {wT hT : Cob} {n i j : ℕ} {y : Word}

/-- The list of arguments the description term is applied to. -/
local notation "cargs" => ([y, List.replicate i true, List.replicate j true,
  List.replicate n true] : List Word)

theorem eval_caWT (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true) :
    (caWT wT).eval cargs = List.replicate (w n) true := by
  simp only [caWT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero]
  rw [hwT (List.replicate n true), List.length_replicate]

theorem eval_caHT (hhT : ∀ x : Word, hT.eval [x] = List.replicate (h x.length) true) :
    (caHT hT).eval cargs = List.replicate (h n) true := by
  simp only [caHT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero]
  rw [hhT (List.replicate n true), List.length_replicate]

theorem caHb_pos {K : ℕ} (hK : 0 < K) : 0 < caHb K := by
  rw [caHb]
  exact Nat.mul_pos (caTri_pos hK) (by omega)

theorem eval_caTT {K : ℕ} (hK : 0 < K) :
    (caTT K).eval cargs = List.replicate ((i - caB K) / caHb K) true := by
  refine Cob.eval_divT (caHb_pos hK) ?_ (by simp)
  rw [Cob.eval_tailN]
  simp

theorem eval_caPhT {K : ℕ} (hK : 0 < K) :
    (caPhT K).eval cargs = List.replicate ((i - caB K) % caHb K) true := by
  refine Cob.eval_modT (caHb_pos hK) ?_ (by simp)
  rw [Cob.eval_tailN]
  simp

theorem eval_caRowK {c : ℕ} : (caRowK c).eval cargs = List.replicate c true := by
  simp [caRowK]

theorem eval_caRowL {a b t : ℕ} {tT : Cob} (ht : tT.eval cargs = List.replicate t true) :
    (caRowL a tT b).eval cargs = List.replicate (a + b * t) true := by
  simp only [caRowL, Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
    Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, ht, List.length_replicate]
  rw [← List.replicate_add]
  congr 1
  ring

theorem eval_caUid {r c : ℕ} {rowT jT : Cob}
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hrow : rowT.eval cargs = List.replicate r true)
    (hj : jT.eval cargs = List.replicate c true) :
    (caUid wT rowT jT).eval cargs = List.replicate (w n * r + c) true := by
  simp only [caUid, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, Cob.eval_comp, Cob.eval_smash,
    List.getD_cons_zero, List.getD_cons_succ, hrow, hj, eval_caWT hwT, List.length_replicate]
  rw [← List.replicate_add]
  congr 1
  ring

/-- The column of the gate itself. -/
theorem eval_col : (Cob.proj 2).eval cargs = List.replicate j true := by simp

/-- The column to the left. -/
theorem eval_colL : (Cob.tailN 1 (Cob.proj 2)).eval cargs = List.replicate (j - 1) true := by
  rw [Cob.eval_tailN]
  simp

/-- The column to the right. -/
theorem eval_colR :
    (Cob.pre [true] (Cob.proj 2)).eval cargs = List.replicate (j + 1) true := by
  simp only [Cob.eval_pre, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero]
  rw [show j + 1 = 1 + j from Nat.add_comm _ _, List.replicate_add]
  rfl

theorem eval_empty : (Cob.empty : Cob).eval cargs = List.replicate 0 true := by simp

end Eval

/-! ### The rows of the tableau -/

/-- The identifier of the one-hot bit of the symbol `s` at the time computed by `tT`, in the
column computed by `jT`. -/
def caStRefT (K : ℕ) (wT tT jT : Cob) (s : ℕ) : Cob :=
  Cob.iteT tT
    (caUid wT (caRowL (caB K + 2 * caTri K + s * caTri K + (caTri K - 1))
      (Cob.tailN 1 tT) (caHb K)) jT)
    (caUid wT (caRowK (3 + s)) jT)

/-- The identifier of the one-hot bit of the symbol `a` in the cell to the left. -/
def caRefLT (A : CellAuto) (wT tT : Cob) (a : ℕ) : Cob :=
  Cob.iteT (.proj 2) (caStRefT A.K wT tT (Cob.tailN 1 (.proj 2)) a)
    (if a = A.blk then caWT wT else Cob.empty)

/-- The identifier of the one-hot bit of the symbol `c` in the cell to the right. -/
def caRefRT (A : CellAuto) (wT tT : Cob) (c : ℕ) : Cob :=
  Cob.iteT (.comp Cob.dropU [Cob.pre [true] (.proj 2), caWT wT])
    (caStRefT A.K wT tT (Cob.pre [true] (.proj 2)) c)
    (if c = A.blk then caWT wT else Cob.empty)

/-- The row of phase `p` in the block of a step. -/
def caBlkPT (A : CellAuto) (wT : Cob) (p : ℕ) : Cob :=
  if p < 2 * caTri A.K then
    (if p % 2 = 0 then
      tokTerm 5 (caRefLT A wT (caTT A.K) (triA A.K (p / 2)))
        (caStRefT A.K wT (caTT A.K) (.proj 2) (triB A.K (p / 2)))
     else
      tokTerm 5 (caUid wT (caRowL (caB A.K + p - 1) (caTT A.K) (caHb A.K)) (.proj 2))
        (caRefRT A wT (caTT A.K) (triC A.K (p / 2))))
  else
    tokTerm 6
      (if (p - 2 * caTri A.K) % caTri A.K = 0 then Cob.empty
        else caUid wT (caRowL (caB A.K + p - 1) (caTT A.K) (caHb A.K)) (.proj 2))
      (if A.stp (triA A.K ((p - 2 * caTri A.K) % caTri A.K))
            (triB A.K ((p - 2 * caTri A.K) % caTri A.K))
            (triC A.K ((p - 2 * caTri A.K) % caTri A.K)) = (p - 2 * caTri A.K) / caTri A.K then
        caUid wT (caRowL (caB A.K + 2 * ((p - 2 * caTri A.K) % caTri A.K) + 1)
          (caTT A.K) (caHb A.K)) (.proj 2)
       else Cob.empty)

/-- A row inside a block, selected by its phase. -/
def caBlkSelT (A : CellAuto) (wT : Cob) : Cob :=
  Cob.tableSel ((List.range (caHb A.K)).map (caBlkPT A wT)) (caPhT A.K)

/-- The one-hot row of the symbol `s` in the initial tape, inside the tape. -/
def caInitPT (A : CellAuto) (wT : Cob) (f : Bool) (s : ℕ) : Cob :=
  if A.ini f true = s then
    (if A.ini f false = s then tokTerm 3 Cob.empty Cob.empty
     else tokTerm 6 (caUid wT (caRowK 2) (.proj 2)) (caUid wT (caRowK 2) (.proj 2)))
  else
    (if A.ini f false = s then tokTerm 4 (caUid wT (caRowK 2) (.proj 2)) Cob.empty
     else tokTerm 2 Cob.empty Cob.empty)

/-- The one-hot row of the symbol `s` in the initial tape. -/
def caInitST (A : CellAuto) (wT : Cob) (s : ℕ) : Cob :=
  Cob.iteT (.comp Cob.dropU [.proj 2, .proj 3])
    (Cob.iteT (.proj 2) (caInitPT A wT false s) (caInitPT A wT true s))
    (if A.blk = s then tokTerm 3 Cob.empty Cob.empty else tokTerm 2 Cob.empty Cob.empty)

/-- An initial row, selected by its symbol. -/
def caInitSelT (A : CellAuto) (wT : Cob) : Cob :=
  Cob.tableSel ((List.range A.K).map (caInitST A wT)) (Cob.tailN 3 (.proj 1))

/-- The accumulator row of the accepting symbol `e`. -/
def caFinET (A : CellAuto) (wT hT : Cob) (e : ℕ) : Cob :=
  tokTerm 6
    (if e = 0 then Cob.empty
     else caUid wT (caRowL (caB A.K + e - 1) (caHT hT) (caHb A.K)) (.proj 2))
    (if A.ac e then caStRefT A.K wT (caHT hT) (.proj 2) e else Cob.empty)

/-- An accumulator row of the verdict, selected by its symbol. -/
def caFinSelT (A : CellAuto) (wT hT : Cob) : Cob :=
  Cob.tableSel ((List.range A.K).map (caFinET A wT hT))
    (.comp Cob.dropU [caRowL (caB A.K) (caHT hT) (caHb A.K), .proj 1])

/-- The row broadcasting the verdict. -/
def caLastT (A : CellAuto) (wT hT : Cob) : Cob :=
  tokTerm 6 (.comp .smash [caRowL (caB A.K + A.K - 1) (caHT hT) (caHb A.K), caWT wT])
    (.comp .smash [caRowL (caB A.K + A.K - 1) (caHT hT) (caHb A.K), caWT wT])

/-- The row holding the input bit of the column. -/
def caBitT : Cob :=
  Cob.iteT (.comp Cob.dropU [.proj 2, .proj 3]) (tokTerm 1 (linT 2 2 1) Cob.empty)
    (tokTerm 2 Cob.empty Cob.empty)

/-- **The Cobham term writing the gate of the tableau** from its row, its column and the length
of the input, all in unary. -/
def caBlkT (A : CellAuto) (wT hT : Cob) : Cob :=
  Cob.iteT (.proj 1)
    (Cob.iteT (Cob.tailN 1 (.proj 1))
      (Cob.iteT (Cob.tailN 2 (.proj 1))
        (Cob.iteT (Cob.tailN (caB A.K - 1) (.proj 1))
          (Cob.iteT (.comp Cob.dropU [caRowL (caB A.K - 1) (caHT hT) (caHb A.K), .proj 1])
            (Cob.iteT
              (.comp Cob.dropU [caRowL (caB A.K + A.K - 1) (caHT hT) (caHb A.K), .proj 1])
              (caLastT A wT hT) (caFinSelT A wT hT))
            (caBlkSelT A wT))
          (caInitSelT A wT))
        caBitT)
      (tokTerm 3 Cob.empty Cob.empty))
    (tokTerm 2 Cob.empty Cob.empty)

/-! ### The value of the term -/

section EvalRows

variable {A : CellAuto} {w h : ℕ → ℕ} {wT hT : Cob} {n i j : ℕ} {y : Word}

local notation "cargs" => ([y, List.replicate i true, List.replicate j true,
  List.replicate n true] : List Word)

theorem eval_caStRefT {K t c s : ℕ} {tT jT : Cob}
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (ht : tT.eval cargs = List.replicate t true)
    (hj : jT.eval cargs = List.replicate c true) :
    (caStRefT K wT tT jT s).eval cargs
      = List.replicate (w n * caStRow K t s + c) true := by
  have h1 : (Cob.tailN 1 tT).eval cargs = List.replicate (t - 1) true := by
    rw [Cob.eval_tailN, ht]
    simp
  rw [caStRefT,
    eval_iteNe ht (eval_caUid hwT (eval_caRowL h1) hj) (eval_caUid hwT eval_caRowK hj)]
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0
    rw [if_pos (by simp), caStRow, if_pos rfl]
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), caStRow,
      if_neg (by omega),
      show caB K + caHb K * (t - 1) + 2 * caTri K + s * caTri K + (caTri K - 1)
        = caB K + 2 * caTri K + s * caTri K + (caTri K - 1) + caHb K * (t - 1) by omega]

theorem eval_caRefLT {t a : ℕ} {tT : Cob}
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (ht : tT.eval cargs = List.replicate t true) :
    (caRefLT A wT tT a).eval cargs
      = List.replicate (caRefL A.K (w n) A.blk t a j) true := by
  have hb : (if a = A.blk then caWT wT else Cob.empty).eval cargs
      = List.replicate (if a = A.blk then w n else 0) true := by
    by_cases hab : a = A.blk
    · rw [if_pos hab, if_pos hab, eval_caWT hwT]
    · rw [if_neg hab, if_neg hab]
      simp
  rw [caRefLT, eval_iteNe eval_col (eval_caStRefT hwT ht eval_colL) hb, caRefL]
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0
    rw [if_pos (by simp), if_pos rfl]
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_neg (by omega),
      caStId]

theorem eval_caRefRT {t c : ℕ} {tT : Cob}
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (ht : tT.eval cargs = List.replicate t true) :
    (caRefRT A wT tT c).eval cargs
      = List.replicate (caRefR A.K (w n) A.blk t c j) true := by
  have hb : (if c = A.blk then caWT wT else Cob.empty).eval cargs
      = List.replicate (if c = A.blk then w n else 0) true := by
    by_cases hcb : c = A.blk
    · rw [if_pos hcb, if_pos hcb, eval_caWT hwT]
    · rw [if_neg hcb, if_neg hcb]
      simp
  have hcond : (Cob.comp Cob.dropU [Cob.pre [true] (Cob.proj 2), caWT wT]).eval cargs
      = List.replicate (w n - (j + 1)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, eval_caWT hwT,
      eval_colR, List.length_replicate, List.drop_replicate]
  rw [caRefRT, eval_iteNe hcond (eval_caStRefT hwT ht eval_colR) hb, caRefR]
  by_cases hjw : j + 1 < w n
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_pos hjw, caStId]
  · rw [if_pos (by simp only [List.replicate_eq_nil_iff]; omega), if_neg hjw]

theorem eval_caBitT : (caBitT : Cob).eval cargs = encGate (caBitG n j) := by
  have hcond : (Cob.comp Cob.dropU [Cob.proj 2, Cob.proj 3]).eval cargs
      = List.replicate (n - j) true := by
    simp
  rw [caBitT, eval_iteNe hcond rfl rfl, caBitG]
  by_cases hjn : j < n
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_pos hjn]
    exact eval_tokTerm (Gate.inp (2 * j + 1))
      (eval_linT (i := j) (by simp) (by simp only [fld1]; omega)) eval_empty
  · rw [if_pos (by simp only [List.replicate_eq_nil_iff]; omega), if_neg hjn]
    exact eval_tokTerm (Gate.cst false) eval_empty eval_empty

theorem eval_caInitST {s : ℕ}
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true) :
    (caInitST A wT s).eval cargs = encGate (caInitG A.blk A.ini (w n) n s j) := by
  have hu : (caUid wT (caRowK 2) (Cob.proj 2)).eval cargs
      = List.replicate (w n * 2 + j) true := eval_caUid hwT eval_caRowK eval_col
  have hb : ∀ f : Bool, (caInitPT A wT f s).eval cargs
      = encGate (if A.ini f true = s then
          (if A.ini f false = s then Gate.cst true
           else Gate.disj (w n * 2 + j) (w n * 2 + j))
        else (if A.ini f false = s then Gate.neg (w n * 2 + j) else Gate.cst false)) := by
    intro f
    rw [caInitPT]
    split_ifs
    · exact eval_tokTerm (Gate.cst true) eval_empty eval_empty
    · exact eval_tokTerm (Gate.disj _ _) hu hu
    · exact eval_tokTerm (Gate.neg _) hu eval_empty
    · exact eval_tokTerm (Gate.cst false) eval_empty eval_empty
  have hblk : (if A.blk = s then tokTerm 3 Cob.empty Cob.empty
        else tokTerm 2 Cob.empty Cob.empty).eval cargs
      = encGate (Gate.cst (decide (A.blk = s))) := by
    by_cases hbs : A.blk = s
    · rw [if_pos hbs, decide_eq_true hbs]
      exact eval_tokTerm (Gate.cst true) eval_empty eval_empty
    · rw [if_neg hbs, decide_eq_false hbs]
      exact eval_tokTerm (Gate.cst false) eval_empty eval_empty
  have hcond : (Cob.comp Cob.dropU [Cob.proj 2, Cob.proj 3]).eval cargs
      = List.replicate (n - j) true := by
    simp
  rw [caInitST, eval_iteNe hcond (eval_iteNe eval_col (hb false) (hb true)) hblk, caInitG]
  by_cases hjn : j < n
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_pos hjn]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      rw [if_pos (by simp)]
      simp
    · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega),
        decide_eq_false (by omega : ¬ (j = 0))]
  · rw [if_pos (by simp only [List.replicate_eq_nil_iff]; omega), if_neg hjn]

theorem eval_caInitSelT
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hlt : i < caB A.K) :
    (caInitSelT A wT).eval cargs = encGate (caInitG A.blk A.ini (w n) n (i - 3) j) := by
  have hK := A.Kpos
  have hidx : (Cob.tailN 3 (Cob.proj 1)).eval cargs = List.replicate (i - 3) true := by
    rw [Cob.eval_tailN]
    simp
  rw [caInitSelT, Cob.eval_tableSel _ _ _ _ hidx,
    getD_range_map _ (show i - 3 < A.K by rw [caB] at hlt; omega)]
  exact eval_caInitST hwT

theorem eval_caBlkPT (p : ℕ)
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true) :
    (caBlkPT A wT p).eval cargs
      = encGate (caBlockG A.K A.blk A.stp (w n) ((i - caB A.K) / caHb A.K) p j) := by
  have hK := A.Kpos
  have htri := caTri_pos hK
  have ht : (caTT A.K).eval cargs
      = List.replicate ((i - caB A.K) / caHb A.K) true := eval_caTT hK
  rw [caBlkPT, caBlockG]
  by_cases h1 : p < 2 * caTri A.K
  · rw [if_pos h1, if_pos h1]
    by_cases h2 : p % 2 = 0
    · rw [if_pos h2, if_pos h2]
      exact eval_tokTerm (Gate.conj _ _) (eval_caRefLT hwT ht) (eval_caStRefT hwT ht eval_col)
    · rw [if_neg h2, if_neg h2,
        show caB A.K + caHb A.K * ((i - caB A.K) / caHb A.K) + p - 1
          = caB A.K + p - 1 + caHb A.K * ((i - caB A.K) / caHb A.K) by omega]
      exact eval_tokTerm (Gate.conj _ _) (eval_caUid hwT (eval_caRowL ht) eval_col)
        (eval_caRefRT hwT ht)
  · rw [if_neg h1, if_neg h1,
      show caB A.K + caHb A.K * ((i - caB A.K) / caHb A.K) + p - 1
        = caB A.K + p - 1 + caHb A.K * ((i - caB A.K) / caHb A.K) by omega,
      show caB A.K + caHb A.K * ((i - caB A.K) / caHb A.K)
          + 2 * ((p - 2 * caTri A.K) % caTri A.K) + 1
        = caB A.K + 2 * ((p - 2 * caTri A.K) % caTri A.K) + 1
          + caHb A.K * ((i - caB A.K) / caHb A.K) by omega]
    by_cases h3 : (p - 2 * caTri A.K) % caTri A.K = 0
    · rw [if_pos h3, if_pos h3]
      by_cases h4 : A.stp (triA A.K ((p - 2 * caTri A.K) % caTri A.K))
          (triB A.K ((p - 2 * caTri A.K) % caTri A.K))
          (triC A.K ((p - 2 * caTri A.K) % caTri A.K)) = (p - 2 * caTri A.K) / caTri A.K
      · rw [if_pos h4, if_pos h4]
        exact eval_tokTerm (Gate.disj _ _) eval_empty
          (eval_caUid hwT (eval_caRowL ht) eval_col)
      · rw [if_neg h4, if_neg h4]
        exact eval_tokTerm (Gate.disj _ _) eval_empty eval_empty
    · rw [if_neg h3, if_neg h3]
      by_cases h4 : A.stp (triA A.K ((p - 2 * caTri A.K) % caTri A.K))
          (triB A.K ((p - 2 * caTri A.K) % caTri A.K))
          (triC A.K ((p - 2 * caTri A.K) % caTri A.K)) = (p - 2 * caTri A.K) / caTri A.K
      · rw [if_pos h4, if_pos h4]
        exact eval_tokTerm (Gate.disj _ _) (eval_caUid hwT (eval_caRowL ht) eval_col)
          (eval_caUid hwT (eval_caRowL ht) eval_col)
      · rw [if_neg h4, if_neg h4]
        exact eval_tokTerm (Gate.disj _ _) (eval_caUid hwT (eval_caRowL ht) eval_col)
          eval_empty

theorem eval_caBlkSelT
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true) :
    (caBlkSelT A wT).eval cargs
      = encGate (caBlockG A.K A.blk A.stp (w n) ((i - caB A.K) / caHb A.K)
          ((i - caB A.K) % caHb A.K) j) := by
  have hK := A.Kpos
  rw [caBlkSelT, Cob.eval_tableSel _ _ _ _ (eval_caPhT hK),
    getD_range_map _ (Nat.mod_lt _ (caHb_pos hK))]
  exact eval_caBlkPT _ hwT

theorem eval_caFinET {e : ℕ}
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hhT : ∀ x : Word, hT.eval [x] = List.replicate (h x.length) true) :
    (caFinET A wT hT e).eval cargs = encGate (caFinG A.K A.ac (w n) (h n) e j) := by
  have hH : (caHT hT).eval cargs = List.replicate (h n) true := eval_caHT hhT
  rw [caFinET, caFinG]
  refine eval_tokTerm (Gate.disj _ _) ?_ ?_
  · by_cases he : e = 0
    · rw [if_pos he, if_pos he]
      exact eval_empty
    · rw [if_neg he, if_neg he, caP,
        show w n * (caB A.K + caHb A.K * h n + e - 1) + j
          = w n * (caB A.K + e - 1 + caHb A.K * h n) + j from by
            congr 2
            omega]
      exact eval_caUid hwT (eval_caRowL hH) eval_col
  · by_cases hac : A.ac e
    · rw [if_pos hac, if_pos hac, caStId]
      exact eval_caStRefT hwT hH eval_col
    · rw [if_neg hac, if_neg hac]
      exact eval_empty

theorem eval_caFinSelT
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hhT : ∀ x : Word, hT.eval [x] = List.replicate (h x.length) true)
    (hlt : i < caP A.K (h n) + A.K) :
    (caFinSelT A wT hT).eval cargs
      = encGate (caFinG A.K A.ac (w n) (h n) (i - caP A.K (h n)) j) := by
  have hK := A.Kpos
  have hidx : (Cob.comp Cob.dropU
      [caRowL (caB A.K) (caHT hT) (caHb A.K), Cob.proj 1]).eval cargs
      = List.replicate (i - caP A.K (h n)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, Cob.eval_dropU, eval_caRowL (eval_caHT hhT), Cob.eval_proj,
      List.length_replicate, List.drop_replicate]
    rw [caP]
  rw [caFinSelT, Cob.eval_tableSel _ _ _ _ hidx, getD_range_map _ (by omega)]
  exact eval_caFinET hwT hhT

theorem eval_caLastT
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hhT : ∀ x : Word, hT.eval [x] = List.replicate (h x.length) true) :
    (caLastT A wT hT).eval cargs
      = encGate (Gate.disj (w n * (caP A.K (h n) + A.K - 1))
          (w n * (caP A.K (h n) + A.K - 1))) := by
  have hK := A.Kpos
  have hf : (Cob.comp Cob.smash
      [caRowL (caB A.K + A.K - 1) (caHT hT) (caHb A.K), caWT wT]).eval cargs
      = List.replicate (w n * (caP A.K (h n) + A.K - 1)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
      eval_caRowL (eval_caHT hhT), eval_caWT hwT, List.getD_cons_zero, List.getD_cons_succ,
      List.length_replicate]
    rw [caP, show caB A.K + A.K - 1 + caHb A.K * h n
        = caB A.K + caHb A.K * h n + A.K - 1 from by omega, Nat.mul_comm]
  exact eval_tokTerm (Gate.disj _ _) hf hf

/-- **The term writes exactly the gates of the tableau.** -/
theorem eval_caBlkT
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hhT : ∀ x : Word, hT.eval [x] = List.replicate (h x.length) true) :
    (caBlkT A wT hT).eval cargs = encGate (caT A (w n) (h n) n i j) := by
  have hK := A.Kpos
  have hB : caB A.K = 3 + A.K := rfl
  have hP : caP A.K (h n) = caB A.K + caHb A.K * h n := rfl
  have h1 : (Cob.proj 1).eval cargs = List.replicate i true := by simp
  have h2 : (Cob.tailN 1 (Cob.proj 1)).eval cargs = List.replicate (i - 1) true := by
    rw [Cob.eval_tailN]; simp
  have h3 : (Cob.tailN 2 (Cob.proj 1)).eval cargs = List.replicate (i - 2) true := by
    rw [Cob.eval_tailN]; simp
  have h4 : (Cob.tailN (caB A.K - 1) (Cob.proj 1)).eval cargs
      = List.replicate (i - (caB A.K - 1)) true := by
    rw [Cob.eval_tailN]; simp
  have h5 : (Cob.comp Cob.dropU
      [caRowL (caB A.K - 1) (caHT hT) (caHb A.K), Cob.proj 1]).eval cargs
      = List.replicate (i - (caB A.K - 1 + caHb A.K * h n)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, Cob.eval_dropU, eval_caRowL (eval_caHT hhT), Cob.eval_proj,
      List.length_replicate, List.drop_replicate]
  have h6 : (Cob.comp Cob.dropU
      [caRowL (caB A.K + A.K - 1) (caHT hT) (caHb A.K), Cob.proj 1]).eval cargs
      = List.replicate (i - (caB A.K + A.K - 1 + caHb A.K * h n)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ, Cob.eval_dropU, eval_caRowL (eval_caHT hhT), Cob.eval_proj,
      List.length_replicate, List.drop_replicate]
  rw [caBlkT, eval_iteNe h1 (eval_iteNe h2 (eval_iteNe h3 (eval_iteNe h4
    (eval_iteNe h5 (eval_iteNe h6 rfl rfl) rfl) rfl) rfl) rfl) rfl, caT]
  simp only [List.replicate_eq_nil_iff]
  by_cases e0 : i = 0
  · rw [if_pos (by omega), if_pos e0]
    exact eval_tokTerm (Gate.cst false) eval_empty eval_empty
  rw [if_neg (by omega), if_neg e0]
  by_cases e1 : i = 1
  · rw [if_pos (by omega), if_pos e1]
    exact eval_tokTerm (Gate.cst true) eval_empty eval_empty
  rw [if_neg (by omega), if_neg e1]
  by_cases e2 : i = 2
  · rw [if_pos (by omega), if_pos e2]
    subst e2
    exact eval_caBitT
  rw [if_neg (by omega), if_neg e2]
  by_cases e3 : i < caB A.K
  · rw [if_pos (by omega), if_pos e3]
    exact eval_caInitSelT hwT e3
  rw [if_neg (by omega), if_neg e3]
  by_cases e4 : i < caP A.K (h n)
  · rw [if_pos (by omega), if_pos e4]
    exact eval_caBlkSelT hwT
  rw [if_neg (by omega), if_neg e4]
  by_cases e5 : i < caP A.K (h n) + A.K
  · rw [if_pos (by omega), if_pos e5]
    exact eval_caFinSelT hwT hhT e5
  rw [if_neg (by omega), if_neg e5]
  exact eval_caLastT hwT hhT

end EvalRows

/-! ### The size of a gate -/

theorem caT_inp_le {A : CellAuto} {W H n i j k : ℕ} (h : caT A W H n i j = .inp k) :
    k ≤ 2 * n + 1 := by
  simp only [caT, caBitG, caInitG, caBlockG, caFinG] at h
  split_ifs at h
  simp only [Gate.inp.injEq] at h
  omega

theorem length_encGate_caT {A : CellAuto} {W H : ℕ} (hW : 0 < W) (n i j l : ℕ) (hj : j < W)
    (hl : W * i + j ≤ l) : (encGate (caT A W H n i j)).length ≤ 13 * (l + n + 1) := by
  have htag := (tag_le (caT A W H n i j)).2
  have hwf := gateWf_caT (A := A) (H := H) (n := n) (j := j) hW hj i
  have hf : fld1 (caT A W H n i j) + fld2 (caT A W H n i j) ≤ 2 * l + 2 * n + 1 := by
    cases hg : caT A W H n i j with
    | inp k =>
        have hk := caT_inp_le hg
        simp only [fld1, fld2]
        omega
    | cst b => simp only [fld1, fld2]; omega
    | neg r =>
        rw [hg] at hwf
        simp only [gateWf] at hwf
        simp only [fld1, fld2]
        omega
    | conj r t =>
        rw [hg] at hwf
        simp only [gateWf] at hwf
        simp only [fld1, fld2]
        omega
    | disj r t =>
        rw [hg] at hwf
        simp only [gateWf] at hwf
        simp only [fld1, fld2]
        omega
  rw [length_encGate]
  omega

end CircCode

/-! ### Uniformity -/

/-- **The descriptions of the tableaux of a cellular automaton with a Cobham-computable tape and
running time are written by a single Cobham term.** -/
theorem codeUniform_caGrid {A : CellAuto} {w h : ℕ → ℕ} {wT hT : Cob} (hw : ∀ n, 0 < w n)
    (hwT : ∀ x : Word, wT.eval [x] = List.replicate (w x.length) true)
    (hhT : ∀ x : Word, hT.eval [x] = List.replicate (h x.length) true) :
    CodeUniform (fun n => CircCode.caGrid A (w n) (h n) n) := by
  have hcnt : ∀ x : Word, (Cob.comp Cob.smash
      [wT, Cob.pre (List.replicate (CircCode.caB A.K + A.K + 1) true)
        (Cob.comp Cob.smash [hT, Cob.constT (List.replicate (CircCode.caHb A.K) true)])]).eval [x]
      = List.replicate (CircCode.caCnt A.K (w x.length) (h x.length)) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_pre,
      Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, hwT x, hhT x,
      List.length_append, List.length_replicate]
    rw [CircCode.caCnt, CircCode.caRows, CircCode.caP]
    congr 1
    ring
  exact codeUniform_gridLayer (K := 13) (w := w)
    (k := fun n => CircCode.caCnt A.K (w n) (h n))
    (tmpl := fun n i j => CircCode.caT A (w n) (h n) n i j)
    (gblk := CircCode.caBlkT A wT hT) hw hcnt hwT
    (fun n i j y => CircCode.eval_caBlkT hwT hhT)
    (fun n i j l hj hl => CircCode.length_encGate_caT (hw n) n i j l hj hl)

/-! ### The language -/

/-- **The language of a cellular automaton**: on a word `x` of length `n` the automaton is
started on a tape of `w n` cells carrying `x` in its first `n` cells and the blank elsewhere, is
run for `h n` steps, and accepts when the symbol of the first cell is accepting. -/
def CALang (A : CellAuto) (w h : ℕ → ℕ) : Language :=
  fun x => A.ac (CircCode.caCell A (w x.length) x.length (fun j => x.getD j false)
    (h x.length) 0) = true

/-- **The uniformity hypothesis**: the width of the tape and the number of steps are computed in
unary by Cobham terms, and the tape is not empty. -/
def CAUniform (w h : ℕ → ℕ) : Prop :=
  ∃ wT hT : Cob, (∀ n, 0 < w n) ∧
    (∀ x : Word, wT.eval [x] = List.replicate (w x.length) true) ∧
    (∀ x : Word, hT.eval [x] = List.replicate (h x.length) true)

/-- **The language of a uniform cellular automaton is decided by a P-uniform circuit family.**
This is the Cook–Levin tableau: the circuit is the space–time diagram of the computation. -/
theorem pUniformDecidable_caLang {A : CellAuto} {w h : ℕ → ℕ} (hu : CAUniform w h) :
    PUniformDecidable (CALang A w h) := by
  obtain ⟨wT, hT, hw, hwT, hhT⟩ := hu
  refine ⟨fun n => CircCode.caGrid A (w n) (h n) n,
    fun n => CircCode.caGrid_ne_nil (hw n), fun n => CircCode.wf_caGrid (hw n),
    fun n y hy => ?_, codeUniform_caGrid hw hwT hhT⟩
  have hb : ∀ j, j < n → CircCode.abit y j
      = ((List.range n).map (fun i => y.getD (2 * i + 1) false)).getD j false := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  rw [CircCode.out_caGrid (hw n), CALang, Tseitin.inWord_of_pinned n y hy, List.length_map,
    List.length_range, CircCode.caCell_congr A (w n) n hb (h n) 0]

/-- **The language of a uniform cellular automaton reduces to SAT in polynomial time**,
unconditionally. -/
theorem polyManyOne_SAT_caLang {A : CellAuto} {w h : ℕ → ℕ} (hu : CAUniform w h) :
    CALang A w h ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_caLang hu)

end Complexity
