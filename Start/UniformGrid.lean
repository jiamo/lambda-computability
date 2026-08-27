/-
**Division in unary, and the grid rule for P-uniform descriptions.**

`Start/UniformBlock.lean` makes a family of circuits P-uniform when it is a sequence of blocks of a
*fixed* size: the block index is recovered from the gate identifier by a finite automaton, which can
only count modulo a constant.  A compiler that unrolls a recursion does not produce blocks of a
fixed size: the `i`-th stage of the unrolling of a bounded recursion on an input of length `n` is a
circuit of width polynomial in `n`, so the block size grows with `n`.

What is needed to recover the position of a gate inside such a layout is genuine division, and this
module supplies it: `Complexity.Cob.divmodT` is a Cobham term that computes, from `1^c` and `1^w`,
the pair `(c / w, c % w)` written as `1^{c/w} 0 1^{c%w}`.  It is a bounded recursion on notation
over `1^c` carrying that pair, incrementing the remainder at each step and turning it over into a
carry when it reaches `w`; the bound is the length of the recursion argument plus one, which is
available because `c/w + c%w ≤ c`.

With division in hand the layer rule of `Start/UniformCircuit.lean` immediately gives the rule that
was missing, `Complexity.codeUniform_gridLayer`: a family whose `n`-th circuit is a **grid** of
blocks of width `w n`, the gate at row `i` and column `j` being written by a single Cobham term from
`1^i`, `1^j` and `1^n`, is P-uniform as soon as the width `w` is itself a Cobham function of `1^n`.

Main definitions:

* `Complexity.dmW` — a pair of natural numbers written as `1^q 0 1^r`;
* `Complexity.Cob.divmodT`, `Complexity.Cob.divT`, `Complexity.Cob.modT` — Euclidean division in
  unary, as Cobham terms.

Main results:

* `Complexity.Cob.eval_divmodT` — **division in unary is a Cobham function**;
* `Complexity.Cob.eval_divT`, `Complexity.Cob.eval_modT` — its two components;
* `Complexity.codeUniform_gridLayer` — **a grid of blocks of a Cobham-computable width is
  P-uniform**;
* `Complexity.codeUniform_gridCirc` — an instance of that rule with a width that really grows:
  `n + 1` rows of `n + 1` gates, each row reading the row below it.
-/

import Start.UniformLoop

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### A pair of numbers in unary -/

/-- The pair `(q, r)` written as `1^q 0 1^r`. -/
def dmW (q r : ℕ) : Word :=
  List.replicate q true ++ false :: List.replicate r true

@[simp] theorem length_dmW (q r : ℕ) : (dmW q r).length = q + r + 1 := by
  simp only [dmW, List.length_append, List.length_cons, List.length_replicate]
  omega

@[simp] theorem lead1_dmW (q r : ℕ) : lead1 (dmW q r) = q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [dmW, List.replicate_succ, List.cons_append]
      exact congrArg (· + 1) ih

@[simp] theorem drop1_dmW (q r : ℕ) : drop1 (dmW q r) = false :: List.replicate r true := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [dmW, List.replicate_succ, List.cons_append]
      exact ih

/-! ### The arithmetic of one step -/

/-- The two components of the division of `c` by `w` add up to at most `c`. -/
theorem div_add_mod_le {w : ℕ} (c : ℕ) (hw : 0 < w) : c / w + c % w ≤ c := by
  have h := Nat.div_add_mod c w
  have h' : c / w ≤ w * (c / w) := Nat.le_mul_of_pos_left _ hw
  omega

/-- One step of the recursion, when the remainder turns over. -/
theorem succ_div_of_carry {w c : ℕ} (hw : 0 < w) (h : c % w + 1 = w) :
    (c + 1) / w = c / w + 1 ∧ (c + 1) % w = 0 := by
  have hc : c + 1 = w * (c / w + 1) := by
    have := Nat.div_add_mod c w
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [hc, Nat.mul_div_cancel_left _ hw, Nat.mul_mod_right]
  exact ⟨rfl, rfl⟩

/-- One step of the recursion, when the remainder does not turn over. -/
theorem succ_div_of_no_carry {w c : ℕ} (hw : 0 < w) (h : c % w + 1 ≠ w) :
    (c + 1) / w = c / w ∧ (c + 1) % w = c % w + 1 := by
  have hlt : c % w + 1 < w := by
    have := Nat.mod_lt c hw
    omega
  have hc : c + 1 = w * (c / w) + (c % w + 1) := by
    have := Nat.div_add_mod c w
    omega
  rw [hc, Nat.mul_add_div hw, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt,
    Nat.div_eq_of_lt hlt]
  exact ⟨rfl, rfl⟩

/-! ### Division in unary as a Cobham term -/

/-- The quotient carried by the recursion. -/
def Cob.dmQ : Cob := .comp Cob.leadOnes [.proj 1]

/-- The remainder carried by the recursion, incremented by one. -/
def Cob.dmR1 : Cob :=
  .comp (.app true) [.comp Cob.tail [.comp Cob.dropOnes [.proj 1]]]

/-- One step of the division: increment the remainder, and turn it over into a carry when it
reaches the divisor. -/
def Cob.dmStep : Cob :=
  .comp Cob.iteC
    [.comp Cob.dropU [Cob.dmR1, .proj 2],
      Cob.catL [Cob.dmQ, Cob.constT [false], Cob.dmR1],
      Cob.catL [.comp (.app true) [Cob.dmQ], Cob.constT [false]]]

/-- **Euclidean division in unary**: from `1^c` and `1^w` the term computes `1^{c/w} 0 1^{c%w}`. -/
def Cob.divmodT : Cob :=
  .bRec (Cob.constT [false]) Cob.dmStep Cob.dmStep (.comp (.app true) [.proj 0])

theorem Cob.eval_dmStep (z : Word) {w r : ℕ} (q : ℕ) (hrw : r < w) :
    Cob.dmStep.eval [z, dmW q r, List.replicate w true]
      = if r + 1 = w then dmW (q + 1) 0 else dmW q (r + 1) := by
  have hq : Cob.dmQ.eval [z, dmW q r, List.replicate w true]
      = List.replicate q true := by
    simp [Cob.dmQ]
  have hr : Cob.dmR1.eval [z, dmW q r, List.replicate w true]
      = List.replicate (r + 1) true := by
    simp [Cob.dmR1, List.replicate_succ]
  by_cases h : r + 1 = w
  · have hdrop : (List.replicate w true).drop (r + 1) = [] := by
      simp [h]
    simp only [Cob.dmStep, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
      Cob.eval_dropU, Cob.eval_catL, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero,
      Cob.eval_app, Cob.eval_constT, hq, hr, List.length_replicate, hdrop, if_pos h]
    simp [dmW, List.replicate_succ]
  · have hdrop : (List.replicate w true).drop (r + 1) ≠ [] := by
      simp only [ne_eq, List.drop_eq_nil_iff, List.length_replicate]
      omega
    simp only [Cob.dmStep, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
      Cob.eval_dropU, Cob.eval_catL, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero,
      Cob.eval_app, Cob.eval_constT, hq, hr, List.length_replicate, if_neg hdrop, if_neg h]
    simp [dmW]

/-- The recursion equation of the division term. -/
theorem Cob.eval_divmodT_cons (b : Bool) (x : Word) (rest : List Word) :
    Cob.divmodT.eval ((b :: x) :: rest)
      = (Cob.dmStep.eval (x :: Cob.divmodT.eval (x :: rest) :: rest)).take (x.length + 2) := by
  have h := Cob.eval_bRec_cons (Cob.constT [false]) Cob.dmStep Cob.dmStep
    (.comp (.app true) [Cob.proj 0]) b x rest
  rw [ite_self] at h
  refine h.trans ?_
  congr 1
  simp

/-- **Division in unary is a Cobham function.** -/
theorem Cob.eval_divmodT {w : ℕ} (hw : 0 < w) (c : ℕ) :
    Cob.divmodT.eval [List.replicate c true, List.replicate w true] = dmW (c / w) (c % w) := by
  induction c with
  | zero => simp [Cob.divmodT, dmW]
  | succ c ih =>
      rw [List.replicate_succ, Cob.eval_divmodT_cons, ih,
        Cob.eval_dmStep _ (c / w) (Nat.mod_lt c hw), List.length_replicate]
      have hle := div_add_mod_le c hw
      by_cases h : c % w + 1 = w
      · obtain ⟨hd, hm⟩ := succ_div_of_carry hw h
        rw [if_pos h, hd, hm]
        exact List.take_of_length_le (by rw [length_dmW]; omega)
      · obtain ⟨hd, hm⟩ := succ_div_of_no_carry hw h
        rw [if_neg h, hd, hm]
        exact List.take_of_length_le (by rw [length_dmW]; omega)

/-- The quotient of two unary words. -/
def Cob.divT (t s : Cob) : Cob := .comp Cob.leadOnes [.comp Cob.divmodT [t, s]]

/-- The remainder of two unary words. -/
def Cob.modT (t s : Cob) : Cob :=
  .comp Cob.tail [.comp Cob.dropOnes [.comp Cob.divmodT [t, s]]]

theorem Cob.eval_divT {t s : Cob} {args : List Word} {c w : ℕ} (hw : 0 < w)
    (ht : t.eval args = List.replicate c true) (hs : s.eval args = List.replicate w true) :
    (Cob.divT t s).eval args = List.replicate (c / w) true := by
  simp [Cob.divT, ht, hs, Cob.eval_divmodT hw c]

theorem Cob.eval_modT {t s : Cob} {args : List Word} {c w : ℕ} (hw : 0 < w)
    (ht : t.eval args = List.replicate c true) (hs : s.eval args = List.replicate w true) :
    (Cob.modT t s).eval args = List.replicate (c % w) true := by
  simp [Cob.modT, ht, hs, Cob.eval_divmodT hw c]

/-! ### The grid rule -/

/-- **A grid of blocks of a Cobham-computable width is P-uniform.**  The `n`-th circuit of the
family is a layer of `k n` gates, the gate with identifier `c` being the one at row `c / w n` and
column `c % w n` of a grid of width `w n`; if one Cobham term writes that gate from the row and the
column in unary and from `1^n`, and the width is itself computed in unary from the instance, then
the descriptions of the family are written by a single Cobham term.

Unlike `Complexity.codeUniform_blockLayer`, the size of a block may grow with `n`, which is what
the unrolling of a recursion produces. -/
theorem codeUniform_gridLayer {tmpl : ℕ → ℕ → ℕ → Tseitin.Gate} {k w : ℕ → ℕ}
    {cnt widT gblk : Cob} {K : ℕ} (hw : ∀ n, 0 < w n)
    (hcnt : ∀ x : Word, cnt.eval [x] = List.replicate (k x.length) true)
    (hwid : ∀ x : Word, widT.eval [x] = List.replicate (w x.length) true)
    (hblk : ∀ (n i j : ℕ) (y : Word),
      gblk.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
        = CircCode.encGate (tmpl n i j))
    (hb : ∀ n i j l : ℕ, j < w n → w n * i + j ≤ l →
      (CircCode.encGate (tmpl n i j)).length ≤ K * (l + n + 1)) :
    CodeUniform (fun n => CircCode.layer (fun c => tmpl n (c / w n) (c % w n)) (k n)) := by
  refine codeUniform_layer (K := K) (cnt := cnt)
    (blkT := .comp gblk [.proj 0, Cob.divT (.proj 1) (.comp widT [.proj 2]),
      Cob.modT (.proj 1) (.comp widT [.proj 2]), .proj 2]) hcnt ?_ ?_
  · intro n y c
    have hwn : (Cob.comp widT [Cob.proj 2]).eval
        [y, List.replicate c true, List.replicate n true] = List.replicate (w n) true := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
        List.getD_cons_succ, List.getD_cons_zero]
      rw [hwid (List.replicate n true), List.length_replicate]
    have harg : (Cob.proj 1).eval [y, List.replicate c true, List.replicate n true]
        = List.replicate c true := by simp
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ,
      Cob.eval_divT (hw n) harg hwn, Cob.eval_modT (hw n) harg hwn]
    exact hblk n (c / w n) (c % w n) y
  · intro n c l hc
    exact hb n (c / w n) (c % w n) l (Nat.mod_lt c (hw n))
      (by rw [Nat.div_add_mod]; exact hc)

/-! ### A family whose blocks grow with the instance -/

namespace CircCode

open Complexity.Tseitin

/-- The gate at row `i`, column `j` of the grid of width `n + 1`: the first row reads the input,
and every later row copies the row below it. -/
def gridG (n : ℕ) : ℕ → ℕ → Gate
  | 0, j => .inp j
  | (i + 1), j => .conj ((n + 1) * i + j) ((n + 1) * i + j)

/-- The family: `n + 1` rows of `n + 1` gates, so the block of a row grows with the instance. -/
def gridCirc (n : ℕ) : Circuit :=
  layer (fun c => gridG n (c / (n + 1)) (c % (n + 1))) ((n + 1) * (n + 1))

/-- The width of a row, in unary, from the instance. -/
theorem eval_gridWid (x : Word) :
    (Cob.comp (.app true) [Cob.comp .smash [Cob.proj 0, Cob.constT [true]]]).eval [x]
      = List.replicate (x.length + 1) true := by
  simp [List.replicate_succ]

/-- The number of gates, in unary, from the instance. -/
theorem eval_gridCnt (x : Word) :
    (Cob.comp .smash [Cob.comp (.app true) [Cob.proj 0],
        Cob.comp (.app true) [Cob.proj 0]]).eval [x]
      = List.replicate ((x.length + 1) * (x.length + 1)) true := by
  simp

/-- The Cobham term writing the gate of the grid from its row, its column and the instance. -/
def gridBlk : Cob :=
  .comp Cob.iteC
    [.proj 1,
      tokTerm 5
        (Cob.catL [.comp .smash [.comp Cob.tail [.proj 1], .comp (.app true) [.proj 3]], .proj 2])
        (Cob.catL [.comp .smash [.comp Cob.tail [.proj 1], .comp (.app true) [.proj 3]], .proj 2]),
      tokTerm 1 (.proj 2) (Cob.constT [])]

theorem eval_gridBlk (n i j : ℕ) (y : Word) :
    gridBlk.eval [y, List.replicate i true, List.replicate j true, List.replicate n true]
      = encGate (gridG n i j) := by
  match i with
  | 0 =>
      simp only [gridBlk, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
        Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, List.replicate_zero]
      exact eval_tokTerm (gridG n 0 j) (by simp [gridG, fld1]) (by simp [gridG, fld2])
  | (i + 1) =>
      have hne : List.replicate (i + 1) true ≠ [] := by simp
      have hp : (Cob.catL [Cob.comp .smash [Cob.comp Cob.tail [Cob.proj 1],
            Cob.comp (.app true) [Cob.proj 3]], Cob.proj 2]).eval
          [y, List.replicate (i + 1) true, List.replicate j true, List.replicate n true]
          = List.replicate ((n + 1) * i + j) true := by
        simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, Cob.eval_comp, Cob.eval_smash, Cob.eval_tail,
          Cob.eval_app, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ,
          List.tail_replicate, List.length_replicate, List.length_cons]
        rw [← List.replicate_add]
        congr 1
        simp [Nat.mul_comm]
      simp only [gridBlk, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC,
        Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, if_neg hne]
      exact eval_tokTerm (gridG n (i + 1) j) hp hp

theorem length_encGate_gridG (n i j l : ℕ) (hj : j < n + 1) (hl : (n + 1) * i + j ≤ l) :
    (encGate (gridG n i j)).length ≤ 10 * (l + n + 1) := by
  rw [length_encGate]
  match i with
  | 0 =>
      simp only [gridG, tag, fld1, fld2]
      omega
  | (i + 1) =>
      have hexp : (n + 1) * (i + 1) = (n + 1) * i + (n + 1) := Nat.mul_succ (n + 1) i
      simp only [gridG, tag, fld1, fld2]
      omega

end CircCode

/-- **A family of grids whose rows grow with the instance is P-uniform.**  The `n`-th circuit is
made of `n + 1` rows of `n + 1` gates, so no finite automaton can recover the row of a gate from
its identifier: the division term is what makes the description writable. -/
theorem codeUniform_gridCirc : CodeUniform CircCode.gridCirc :=
  codeUniform_gridLayer (K := 10) (w := fun n => n + 1) (k := fun n => (n + 1) * (n + 1))
    (tmpl := CircCode.gridG) (gblk := CircCode.gridBlk)
    (cnt := .comp .smash [.comp (.app true) [Cob.proj 0], .comp (.app true) [Cob.proj 0]])
    (widT := .comp (.app true) [.comp .smash [Cob.proj 0, Cob.constT [true]]])
    (fun n => Nat.succ_pos n) CircCode.eval_gridCnt CircCode.eval_gridWid
    CircCode.eval_gridBlk CircCode.length_encGate_gridG

end Complexity
