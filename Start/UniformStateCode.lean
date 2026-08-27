/-
# The description of the poly-state grid, and P-uniform decidability

`Start/UniformState.lean` builds, for an automaton with `M = m n` states on inputs of length `n`,
a grid of circuits deciding its language.  This module writes the description of that grid with a
single Cobham term, and concludes that the language of such an automaton is decided by a P-uniform
circuit family — hence reduces to SAT in polynomial time.

The uniformity data is packaged as `Complexity.StateUniform`: the number of states, the transition
function and the acceptance predicate are all computed in unary by Cobham terms from the length of
the input, in unary.  Two instances are derived: every finite automaton (the number of states does
not depend on `n`), recovering `Complexity.pUniformDecidable_autoLang`, and the counting automaton
whose states are the possible numbers of `true` bits, recovering the symmetric languages of
`Start/UniformSym.lean`.

Main definitions:

* `Complexity.CircCode.eqU` — the unary equality test as a Cobham term;
* `Complexity.CircCode.stBlkT` — **the Cobham term writing the gate of the grid** from its row,
  its column and the length of the input, all in unary;
* `Complexity.StateLang`, `Complexity.StateUniform` — the language of the automaton and the
  uniformity hypothesis on its data.

Main results:

* `Complexity.CircCode.eval_stBlkT` — the term writes exactly the gates of the grid;
* `Complexity.codeUniform_stGrid` — **the descriptions of the grids are written by a single
  Cobham term**;
* `Complexity.pUniformDecidable_stateLang` — **the language of a uniform poly-state automaton is
  decided by a P-uniform circuit family**;
* `Complexity.polyManyOne_SAT_stateLang` — and therefore reduces to SAT in polynomial time.
-/
import Start.UniformState
import Start.UniformSym

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The unary equality test -/

/-- The Cobham term testing two unary words for equality. -/
def eqU (a b : Cob) : Cob :=
  Cob.andT (.comp Cob.notC [.comp Cob.dropU [a, b]]) (.comp Cob.notC [.comp Cob.dropU [b, a]])

theorem eval_notDropU {a b : Cob} {args : List Word} {p q : ℕ}
    (ha : a.eval args = List.replicate p true) (hb : b.eval args = List.replicate q true) :
    (Cob.comp Cob.notC [Cob.comp Cob.dropU [a, b]]).eval args = bw (decide (q ≤ p)) := by
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, ha, hb, Cob.eval_dropU,
    List.length_replicate, List.drop_replicate, Cob.eval_notC]
  by_cases h : q ≤ p
  · rw [if_pos (by simp; omega), decide_eq_true h]
    rfl
  · rw [if_neg (by simp; omega), decide_eq_false h]
    rfl

theorem eval_eqU {a b : Cob} {args : List Word} {p q : ℕ}
    (ha : a.eval args = List.replicate p true) (hb : b.eval args = List.replicate q true) :
    (eqU a b).eval args = bw (decide (p = q)) := by
  rw [eqU, Cob.eval_andT (eval_notDropU ha hb) (eval_notDropU hb ha)]
  congr 1
  by_cases h1 : q ≤ p <;> by_cases h2 : p ≤ q <;>
    simp [h1, h2] <;> omega

/-! ### The arithmetic of the layout, as Cobham terms -/

/-- The number of states, in unary. -/
def stMT (mT : Cob) : Cob := .comp mT [.proj 3]

/-- The height of a block, in unary. -/
def stHT (mT : Cob) : Cob :=
  Cob.catL [.comp .smash [stMT mT, Cob.constT [true, true]], Cob.constT (List.replicate 4 true)]

/-- The index of the block of a row, in unary. -/
def stTT (mT : Cob) : Cob := Cob.divT (.comp Cob.tail [.proj 1]) (stHT mT)

/-- The phase of a row inside its block, in unary. -/
def stPT (mT : Cob) : Cob := Cob.modT (.comp Cob.tail [.proj 1]) (stHT mT)

/-- The state of a conjunction or accumulator row, in unary. -/
def stSST (mT : Cob) : Cob := Cob.divT (Cob.tailN 4 (stPT mT)) (Cob.constT [true, true])

/-- Whether a row is a conjunction row or an accumulator row. -/
def stRRT (mT : Cob) : Cob := Cob.modT (Cob.tailN 4 (stPT mT)) (Cob.constT [true, true])

/-- The identifier of the one-hot bit of the state given by the column, at the time given by the
term `tT`. -/
def stPrevT (mT tT : Cob) : Cob :=
  Cob.iteT tT
    (Cob.catL
      [.comp .smash
        [Cob.catL [Cob.constT (List.replicate 6 true),
          .comp .smash [.comp Cob.tail [tT], stHT mT],
          .comp .smash [.proj 2, Cob.constT [true, true]]],
        stMT mT],
      .comp Cob.tail [stMT mT]])
    (.proj 2)

/-- The offset, inside its block, of the selector of the transitions into the state of the row
from the state of the column. -/
def stSelKT (mT dfT dtT : Cob) : Cob :=
  Cob.iteT (eqU (.comp dtT [.proj 2, .proj 3]) (stSST mT))
    (Cob.iteT (eqU (.comp dfT [.proj 2, .proj 3]) (stSST mT))
      (Cob.constT [true]) (Cob.constT [true, true]))
    (Cob.iteT (eqU (.comp dfT [.proj 2, .proj 3]) (stSST mT))
      (Cob.constT (List.replicate 3 true)) Cob.empty)

/-- The identifier of the selector gate. -/
def stSelRefT (mT dfT dtT : Cob) : Cob :=
  .comp .smash
    [Cob.catL [Cob.constT [true], .comp .smash [stTT mT, stHT mT], stSelKT mT dfT dtT], stMT mT]

/-- The identifier of the first gate of the current row. -/
def stIdT (mT : Cob) : Cob := .comp .smash [.proj 1, stMT mT]

/-- The identifier of the first gate of the row below. -/
def stId1T (mT : Cob) : Cob := .comp .smash [.comp Cob.tail [.proj 1], stMT mT]

/-- The identifier of the gate to the left in the current row. -/
def stAccJT (mT : Cob) : Cob := Cob.catL [stIdT mT, .comp Cob.tail [.proj 2]]

/-- The identifier of the gate of the same column in the row below. -/
def stConjJT (mT : Cob) : Cob := Cob.catL [stId1T mT, .proj 2]

/-! ### The rows -/

/-- The row holding the input bit. -/
def stBitT (mT : Cob) : Cob :=
  tokTerm 1 (Cob.pre [true] (.comp .smash [stTT mT, Cob.constT [true, true]])) Cob.empty

/-- The row holding the negation of the input bit. -/
def stNegT (mT : Cob) : Cob := tokTerm 4 (stId1T mT) Cob.empty

/-- A conjunction row. -/
def stConjT (mT dfT dtT : Cob) : Cob :=
  tokTerm 5 (stPrevT mT (stTT mT)) (stSelRefT mT dfT dtT)

/-- An accumulator row. -/
def stAccT (mT : Cob) : Cob :=
  Cob.iteT (.proj 2) (tokTerm 6 (stAccJT mT) (stConjJT mT))
    (tokTerm 6 (stId1T mT) (stId1T mT))

/-- The final row, accumulating the one-hot bits of the accepting states. -/
def stFinT (mT acT : Cob) : Cob :=
  Cob.iteT (.proj 2)
    (Cob.iteT (.comp acT [.proj 2, .proj 3])
      (tokTerm 6 (stAccJT mT) (stPrevT mT (.proj 3)))
      (tokTerm 6 (stAccJT mT) (stAccJT mT)))
    (Cob.iteT (.comp acT [.proj 2, .proj 3])
      (tokTerm 6 (stPrevT mT (.proj 3)) (stPrevT mT (.proj 3)))
      (tokTerm 2 Cob.empty Cob.empty))

/-- **The Cobham term writing the gate of the grid** from its row, its column and the length of
the input, all in unary. -/
def stBlkT (mT dfT dtT acT : Cob) : Cob :=
  Cob.iteT (.proj 1)
    (Cob.iteT (.comp Cob.dropU [stTT mT, .proj 3])
      (Cob.iteT (stPT mT)
        (Cob.iteT (Cob.tailN 1 (stPT mT))
          (Cob.iteT (Cob.tailN 2 (stPT mT))
            (Cob.iteT (Cob.tailN 3 (stPT mT))
              (Cob.iteT (stRRT mT) (stAccT mT) (stConjT mT dfT dtT))
              (stNegT mT))
            (stBitT mT))
          (tokTerm 3 Cob.empty Cob.empty))
        (tokTerm 2 Cob.empty Cob.empty))
      (stFinT mT acT))
    (Cob.iteT (.proj 2) (tokTerm 2 Cob.empty Cob.empty) (tokTerm 3 Cob.empty Cob.empty))

/-! ### The value of the term -/

section Eval

variable {m : ℕ → ℕ} {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool} {mT dfT dtT acT : Cob}
variable {n i j : ℕ} {y : Word}

theorem eval_stMT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (stMT mT).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (m n) true := by
  simp only [stMT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero]
  rw [hmT (List.replicate n true), List.length_replicate]

theorem eval_stHT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (stHT mT).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (stH (m n)) true := by
  simp only [stHT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, Cob.eval_comp, Cob.eval_smash, eval_stMT hmT,
    Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, List.length_replicate,
    List.length_cons, List.length_nil]
  rw [← List.replicate_add, stH]
  congr 1
  ring

theorem eval_stTT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (stTT mT).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate ((i - 1) / stH (m n)) true := by
  refine Cob.eval_divT (stH_pos (m n)) ?_ (eval_stHT hmT)
  simp

theorem eval_stPT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (stPT mT).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate ((i - 1) % stH (m n)) true := by
  refine Cob.eval_modT (stH_pos (m n)) ?_ (eval_stHT hmT)
  simp

theorem eval_stQT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (Cob.tailN 4 (stPT mT)).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate ((i - 1) % stH (m n) - 4) true := by
  rw [Cob.eval_tailN, eval_stPT hmT, List.drop_replicate]

theorem eval_stSST (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (stSST mT).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (((i - 1) % stH (m n) - 4) / 2) true :=
  Cob.eval_divT (by norm_num) (eval_stQT hmT) (by simp)

theorem eval_stRRT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (stRRT mT).eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (((i - 1) % stH (m n) - 4) % 2) true :=
  Cob.eval_modT (by norm_num) (eval_stQT hmT) (by simp)

theorem eval_stPrevT (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    {tT : Cob} {t : ℕ}
    (htT : tT.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate t true) :
    (stPrevT mT tT).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (stPrevId (m n) t j) true := by
  have hbig : (Cob.catL
      [Cob.comp .smash
        [Cob.catL [Cob.constT (List.replicate 6 true),
          Cob.comp .smash [Cob.comp Cob.tail [tT], stHT mT],
          Cob.comp .smash [Cob.proj 2, Cob.constT [true, true]]],
        stMT mT],
      Cob.comp Cob.tail [stMT mT]]).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (m n * (6 + stH (m n) * (t - 1) + 2 * j) + (m n - 1)) true := by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_comp, Cob.eval_smash, Cob.eval_tail, Cob.eval_proj,
      Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, htT, eval_stHT hmT,
      eval_stMT hmT, List.tail_replicate, List.length_replicate, List.length_append,
      List.length_cons, List.length_nil]
    rw [← List.replicate_add]
    congr 1
    ring
  rw [stPrevT, eval_iteNe htT hbig (by simp : (Cob.proj 2).eval
    [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate j true), stPrevId]
  by_cases h0 : t = 0
  · rw [if_pos h0, if_pos (by simp [h0])]
  · rw [if_neg h0, if_neg (by simp [h0])]

theorem eval_stSelKT
    (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hdf : ∀ s p : ℕ, dfT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s false) true)
    (hdt : ∀ s p : ℕ, dtT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s true) true) :
    (stSelKT mT dfT dtT).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (stSelK δ n (((i - 1) % stH (m n) - 4) / 2) j) true := by
  have hdfe : (Cob.comp dfT [Cob.proj 2, Cob.proj 3]).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (δ n j false) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_succ,
      List.getD_cons_zero]
    exact hdf j n
  have hdte : (Cob.comp dtT [Cob.proj 2, Cob.proj 3]).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (δ n j true) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_succ,
      List.getD_cons_zero]
    exact hdt j n
  have e1 := eval_eqU hdte (eval_stSST (m := m) (n := n) (i := i) (j := j) (y := y) hmT)
  have e2 := eval_eqU hdfe (eval_stSST (m := m) (n := n) (i := i) (j := j) (y := y) hmT)
  rw [stSelKT, Cob.eval_iteW e1 (Cob.eval_iteW e2 rfl rfl) (Cob.eval_iteW e2 rfl rfl), stSelK]
  split_ifs <;> simp_all

theorem eval_stSelRefT
    (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hdf : ∀ s p : ℕ, dfT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s false) true)
    (hdt : ∀ s p : ℕ, dtT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s true) true) :
    (stSelRefT mT dfT dtT).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (m n * (1 + stH (m n) * ((i - 1) / stH (m n))
          + stSelK δ n (((i - 1) % stH (m n) - 4) / 2) j)) true := by
  simp only [stSelRefT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
    Cob.eval_catL, List.flatten_cons, List.flatten_nil, List.append_nil, Cob.eval_constT,
    List.getD_cons_zero, List.getD_cons_succ, eval_stTT hmT, eval_stHT hmT, eval_stMT hmT,
    eval_stSelKT hmT hdf hdt, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil]
  congr 1
  ring

/-- **The term writes exactly the gates of the grid.** -/
theorem eval_stBlkT
    (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hdf : ∀ s p : ℕ, dfT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s false) true)
    (hdt : ∀ s p : ℕ, dtT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s true) true)
    (hacT : ∀ s p : ℕ, acT.eval [List.replicate s true, List.replicate p true] = bw (ac p s)) :
    (stBlkT mT dfT dtT acT).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = encGate (stT δ ac (m n) n i j) := by
  have hI : (Cob.proj 1).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate i true := by simp
  have hJ : (Cob.proj 2).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate j true := by simp
  have hN : (Cob.proj 3).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate n true := by simp
  have hT := eval_stTT (m := m) (n := n) (i := i) (j := j) (y := y) hmT
  have hP := eval_stPT (m := m) (n := n) (i := i) (j := j) (y := y) hmT
  have hR := eval_stRRT (m := m) (n := n) (i := i) (j := j) (y := y) hmT
  have hM := eval_stMT (m := m) (n := n) (i := i) (j := j) (y := y) hmT
  have hcstF : (tokTerm 2 Cob.empty Cob.empty).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = encGate (Gate.cst false) :=
    eval_tokTerm (Gate.cst false) (by simp [fld1]) (by simp [fld2])
  have hcstT : (tokTerm 3 Cob.empty Cob.empty).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = encGate (Gate.cst true) :=
    eval_tokTerm (Gate.cst true) (by simp [fld1]) (by simp [fld2])
  have hdisj : ∀ (a b : Cob) (u v : ℕ),
      a.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
        = List.replicate u true →
      b.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
        = List.replicate v true →
      (tokTerm 6 a b).eval
          [y, List.replicate i true, List.replicate j true, List.replicate n true]
        = encGate (Gate.disj u v) :=
    fun a b u v ha hb => eval_tokTerm (Gate.disj u v) ha hb
  have hid1 : (stId1T mT).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (m n * (i - 1)) true := by
    simp only [stId1T, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_tail,
      hI, hM, List.getD_cons_zero, List.getD_cons_succ, List.tail_replicate,
      List.length_replicate]
    congr 1
    ring
  have haccJ : (stAccJT mT).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (m n * i + (j - 1)) true := by
    simp only [stAccJT, stIdT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_comp, Cob.eval_smash, Cob.eval_tail, hI, hJ,
      hM, List.getD_cons_zero, List.getD_cons_succ, List.tail_replicate, List.length_replicate]
    rw [← List.replicate_add]
    congr 1
    ring
  have hconjJ : (stConjJT mT).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = List.replicate (m n * (i - 1) + j) true := by
    simp only [stConjJT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, hid1, hJ]
    rw [← List.replicate_add]
  have hacj : (Cob.comp acT [Cob.proj 2, Cob.proj 3]).eval
      [y, List.replicate i true, List.replicate j true, List.replicate n true] = bw (ac n j) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_succ,
      List.getD_cons_zero]
    exact hacT j n
  rw [stBlkT]
  by_cases h0 : i = 0
  · subst h0
    rw [eval_iteNe hI rfl rfl, if_pos (by simp), eval_iteNe hJ hcstF hcstT, stT_zero]
    by_cases hj0 : j = 0
    · subst hj0
      simp
    · rw [if_neg (by simp [hj0]), decide_eq_false hj0]
  · rw [eval_iteNe hI rfl rfl, if_neg (by simp [h0])]
    have hfin : (Cob.comp Cob.dropU [stTT mT, Cob.proj 3]).eval
        [y, List.replicate i true, List.replicate j true, List.replicate n true]
        = List.replicate (n - (i - 1) / stH (m n)) true := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, hT, hN, Cob.eval_dropU,
        List.length_replicate, List.drop_replicate]
    rw [eval_iteNe hfin rfl rfl, stT, if_neg h0]
    by_cases hf : n ≤ (i - 1) / stH (m n)
    · rw [if_pos (by simp; omega), if_pos hf]
      have hprevn := eval_stPrevT (m := m) (n := n) (i := i) (j := j) (y := y) hmT (t := n) hN
      rw [stFinT, eval_iteNe hJ rfl rfl]
      by_cases hj0 : j = 0
      · subst hj0
        rw [if_pos (by simp), if_pos rfl,
          Cob.eval_iteW hacj
            (hdisj _ _ _ _ hprevn hprevn) hcstF]
        by_cases hac0 : ac n 0
        · rw [if_pos hac0, if_pos hac0]
        · rw [if_neg hac0, if_neg hac0]
      · rw [if_neg (by simp [hj0]), if_neg hj0,
          Cob.eval_iteW hacj
            (hdisj _ _ _ _ haccJ hprevn) (hdisj _ _ _ _ haccJ haccJ)]
        by_cases hacj' : ac n j
        · rw [if_pos hacj', if_pos hacj']
        · rw [if_neg hacj', if_neg hacj']
    · rw [if_neg (by simp; omega), if_neg hf]
      rw [eval_iteNe hP rfl rfl]
      by_cases hp0 : (i - 1) % stH (m n) = 0
      · rw [if_pos (by simp [hp0]), if_pos hp0, hcstF]
      · rw [if_neg (by simp [hp0]), if_neg hp0]
        have hP1 : (Cob.tailN 1 (stPT mT)).eval
            [y, List.replicate i true, List.replicate j true, List.replicate n true]
            = List.replicate ((i - 1) % stH (m n) - 1) true := by
          rw [Cob.eval_tailN, hP, List.drop_replicate]
        rw [eval_iteNe hP1 rfl rfl]
        by_cases hp1 : (i - 1) % stH (m n) = 1
        · rw [if_pos (by simp [hp1]), if_pos hp1, hcstT]
        · rw [if_neg (by simp; omega), if_neg hp1]
          have hP2 : (Cob.tailN 2 (stPT mT)).eval
              [y, List.replicate i true, List.replicate j true, List.replicate n true]
              = List.replicate ((i - 1) % stH (m n) - 2) true := by
            rw [Cob.eval_tailN, hP, List.drop_replicate]
          rw [eval_iteNe hP2 rfl rfl]
          by_cases hp2 : (i - 1) % stH (m n) = 2
          · rw [if_pos (by simp [hp2]), if_pos hp2]
            refine eval_tokTerm (Gate.inp (2 * ((i - 1) / stH (m n)) + 1)) ?_ (by simp [fld2])
            simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil,
              Cob.eval_smash, hT, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
              List.length_replicate, List.length_cons, List.length_nil, fld1]
            rw [show ([true] : Word) = List.replicate 1 true from rfl, ← List.replicate_add]
            congr 1
            ring
          · rw [if_neg (by simp; omega), if_neg hp2]
            have hP3 : (Cob.tailN 3 (stPT mT)).eval
                [y, List.replicate i true, List.replicate j true, List.replicate n true]
                = List.replicate ((i - 1) % stH (m n) - 3) true := by
              rw [Cob.eval_tailN, hP, List.drop_replicate]
            rw [eval_iteNe hP3 rfl rfl]
            by_cases hp3 : (i - 1) % stH (m n) = 3
            · rw [if_pos (by simp [hp3]), if_pos hp3, stNegT]
              exact eval_tokTerm (Gate.neg (m n * (i - 1))) hid1 (by simp [fld2])
            · rw [if_neg (by simp; omega), if_neg hp3, eval_iteNe hR rfl rfl]
              by_cases hr : ((i - 1) % stH (m n) - 4) % 2 = 0
              · rw [if_pos (by simp [hr]), if_pos hr, stConjT]
                exact eval_tokTerm
                  (Gate.conj (stPrevId (m n) ((i - 1) / stH (m n)) j)
                    (m n * (1 + stH (m n) * ((i - 1) / stH (m n))
                      + stSelK δ n (((i - 1) % stH (m n) - 4) / 2) j)))
                  (eval_stPrevT hmT hT) (eval_stSelRefT hmT hdf hdt)
              · rw [if_neg (by simp [hr]), if_neg hr, stAccT,
                  eval_iteNe hJ (hdisj _ _ _ _ haccJ hconjJ) (hdisj _ _ _ _ hid1 hid1)]
                by_cases hj0 : j = 0
                · rw [if_pos (by simp [hj0]), if_pos hj0]
                · rw [if_neg (by simp [hj0]), if_neg hj0]

end Eval

/-! ### The size of a gate -/

theorem stT_inp_le {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool} {M n i j l k : ℕ} (hM : 0 < M)
    (hl : M * i + j ≤ l) (h : stT δ ac M n i j = .inp k) : k ≤ 2 * l + 1 := by
  have hi : i ≤ M * i := Nat.le_mul_of_pos_left i hM
  have hd : (i - 1) / stH M ≤ i - 1 := Nat.div_le_self _ _
  rw [stT] at h
  split_ifs at h
  simp only [Gate.inp.injEq] at h
  omega

theorem length_encGate_stT {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool} {M : ℕ} (hM : 0 < M)
    (n i j l : ℕ) (hj : j < M) (hl : M * i + j ≤ l) :
    (encGate (stT δ ac M n i j)).length ≤ 13 * (l + n + 1) := by
  have htag := (tag_le (stT δ ac M n i j)).2
  have hwf := gateWf_stT (δ := δ) (ac := ac) (M := M) (n := n) (j := j) hM hj i
  have hf : fld1 (stT δ ac M n i j) + fld2 (stT δ ac M n i j) ≤ 2 * l + 1 := by
    cases hg : stT δ ac M n i j with
    | inp k =>
        have hk := stT_inp_le hM hl hg
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

/-- **The descriptions of the grids of a uniform poly-state automaton are written by a single
Cobham term.** -/
theorem codeUniform_stGrid {m : ℕ → ℕ} {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool}
    {mT dfT dtT acT : Cob} (hm : ∀ n, 0 < m n)
    (hmT : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hdf : ∀ s p : ℕ, dfT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s false) true)
    (hdt : ∀ s p : ℕ, dtT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s true) true)
    (hacT : ∀ s p : ℕ, acT.eval [List.replicate s true, List.replicate p true] = bw (ac p s)) :
    CodeUniform (fun n => CircCode.stGrid δ ac (m n) n) := by
  have hcnt : ∀ x : Word, (Cob.comp Cob.smash
      [mT,
        Cob.catL
          [Cob.comp Cob.smash
            [Cob.catL [Cob.comp Cob.smash [mT, Cob.constT [true, true]],
              Cob.constT (List.replicate 4 true)],
            Cob.proj 0],
          Cob.constT [true, true]]]).eval [x]
      = List.replicate (CircCode.stCnt (m x.length) x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_catL,
      List.flatten_cons, List.flatten_nil, List.append_nil, Cob.eval_constT, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, hmT x, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil]
    rw [CircCode.stCnt, CircCode.stH]
    congr 1
    ring
  exact codeUniform_gridLayer (K := 13) (w := m) (k := fun n => CircCode.stCnt (m n) n)
    (tmpl := fun n i j => CircCode.stT δ ac (m n) n i j)
    (gblk := CircCode.stBlkT mT dfT dtT acT) hm hcnt hmT
    (fun n i j y => CircCode.eval_stBlkT hmT hdf hdt hacT)
    (fun n i j l hj hl => CircCode.length_encGate_stT (hm n) n i j l hj hl)

/-! ### The language -/

/-- **The language of a poly-state automaton**: the automaton reading a word `x` of length `n`
uses the transition function `δ n` from the state `0`, and accepts when `ac n` holds of the state
reached. -/
def StateLang (δ : ℕ → ℕ → Bool → ℕ) (ac : ℕ → ℕ → Bool) : Language :=
  fun x => ac x.length (x.foldl (fun s b => δ x.length s b) 0) = true

/-- **The uniformity hypothesis**: the number of states, the transition function and the
acceptance predicate are computed in unary by Cobham terms. -/
def StateUniform (δ : ℕ → ℕ → Bool → ℕ) (ac : ℕ → ℕ → Bool) : Prop :=
  ∃ m : ℕ → ℕ, ∃ mT dfT dtT acT : Cob,
    (∀ n, 0 < m n) ∧ (∀ n s b, δ n s b < m n) ∧
    (∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) ∧
    (∀ s p : ℕ, dfT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s false) true) ∧
    (∀ s p : ℕ, dtT.eval [List.replicate s true, List.replicate p true]
      = List.replicate (δ p s true) true) ∧
    (∀ s p : ℕ, acT.eval [List.replicate s true, List.replicate p true] = bw (ac p s))

namespace CircCode

/-- The run of the automaton on the word presented by the circuit input. -/
theorem stRun_eq_foldl (δ : ℕ → ℕ → Bool → ℕ) (n : ℕ) (y : Word) : ∀ t,
    stRun δ n y t
      = ((List.range t).map (fun i => y.getD (2 * i + 1) false)).foldl
          (fun s b => δ n s b) 0 := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [stRun, ih, List.range_succ, List.map_append, List.foldl_append]
      simp [abit]

end CircCode

/-- **The language of a uniform poly-state automaton is decided by a P-uniform circuit family.**
This subsumes both the finite automata of `Start/UniformAuto.lean` and the symmetric languages of
`Start/UniformSym.lean`. -/
theorem pUniformDecidable_stateLang {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool}
    (h : StateUniform δ ac) : PUniformDecidable (StateLang δ ac) := by
  obtain ⟨m, mT, dfT, dtT, acT, hm, hd, hmT, hdf, hdt, hacT⟩ := h
  refine ⟨fun n => CircCode.stGrid δ ac (m n) n, fun n => CircCode.stGrid_ne_nil (hm n),
    fun n => CircCode.wf_stGrid (hm n), fun n y hy => ?_,
    codeUniform_stGrid hm hmT hdf hdt hacT⟩
  rw [CircCode.out_stGrid (hm n) (fun s b => hd n s b), CircCode.stRun_eq_foldl]
  simp only [StateLang, Tseitin.inWord_of_pinned n y hy, List.length_map, List.length_range]

/-- **The language of a uniform poly-state automaton reduces to SAT in polynomial time**,
unconditionally. -/
theorem polyManyOne_SAT_stateLang {δ : ℕ → ℕ → Bool → ℕ} {ac : ℕ → ℕ → Bool}
    (h : StateUniform δ ac) : StateLang δ ac ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_stateLang h)

end Complexity
