/-
**The iteration rule at work: a shift register.**

`Start/UniformIterate.lean` proves that stacking polynomially many copies of a P-uniform *stage*
over a P-uniform base is again P-uniform.  This module exercises that rule on a stage that really
grows with the instance, and on a language it decides.

The stage is a **shift register with an accumulator**.  On an input of length `n` the state has
`n + 2` wires: the first `n + 1` hold the bits of the input that have not been read yet, padded
with `false`, and the last one holds the disjunction of the bits already read.  One copy of the
stage shifts the register down by one place and disjoins the bit that falls off into the
accumulator, so after `n` copies the accumulator holds the disjunction of all the bits of the
input — and it is the topmost gate of the stack, hence its output.

Main definitions:

* `Complexity.CircCode.sregT`, `Complexity.CircCode.sregB` — the stage;
* `Complexity.CircCode.sregBaseT`, `Complexity.CircCode.sregD` — the base, loading the input;
* `Complexity.CircCode.sregC` — the stack of `n` copies;
* `Complexity.CircCode.sregSpec` — the state after `t` copies.

Main results:

* `Complexity.CircCode.stateC_sreg` — **the stack really shifts the register**;
* `Complexity.CircCode.out_sregC` — its output is the disjunction of the bits of the input;
* `Complexity.codeUniform_sregC` — the family is P-uniform, by
  `Complexity.codeUniform_iterC`;
* `Complexity.pUniformDecidable_someOne_of_iter` — hence `Complexity.SomeOne` is decided by a
  P-uniform family built with the iteration rule.
-/

import Start.UniformIterLang

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CircCode

open Complexity.Tseitin

/-! ### The bits of a pinned input -/

/-- The bit `j` of the word presented by a circuit input. -/
def sregBit (x : Word) (j : ℕ) : Bool := x.getD (2 * j + 1) false

/-- The disjunction of the first `t` bits. -/
def sregOr (x : Word) (t : ℕ) : Bool := (List.range t).any (fun j => sregBit x j)

@[simp] theorem sregOr_zero (x : Word) : sregOr x 0 = false := rfl

theorem sregOr_succ (x : Word) (t : ℕ) : sregOr x (t + 1) = (sregOr x t || sregBit x t) := by
  rw [sregOr, sregOr, List.range_succ, List.any_append]
  simp

/-! ### The stage and the base -/

/-- The gate with identifier `c` of the stage, on an input of length `n`.  The state has `n + 2`
wires: `0, …, n` hold the unread bits and `n + 1` the accumulator.  The gates `0` and `1` read the
accumulator and the bit about to be read, the gates `2, …, n + 1` shift the register down, the gate
`n + 2` refills it with `false`, and the top gate `n + 3` is the new accumulator. -/
def sregT (n : ℕ) (c : ℕ) : Gate :=
  if c = 0 then .inp (n + 1)
  else if c = 1 then .inp 0
  else if c ≤ n + 1 then .inp (c - 1)
  else if c = n + 2 then .cst false
  else .disj 0 1

/-- The stage. -/
def sregB (n : ℕ) : Circuit := layer (sregT n) (n + 4)

/-- The gate with identifier `c` of the base: it loads the bits of the input into the register and
starts the accumulator at `false`. -/
def sregBaseT (n : ℕ) (c : ℕ) : Gate := if c < n then .inp (2 * c + 1) else .cst false

/-- The base. -/
def sregD (n : ℕ) : Circuit := layer (sregBaseT n) (n + 2)

/-- The stack of `n` copies of the stage over the base. -/
def sregC (n : ℕ) : Circuit := iterC (sregB n) (sregD n) (n + 2) n

@[simp] theorem length_sregB (n : ℕ) : (sregB n).length = n + 4 := by
  rw [sregB, length_layer]

@[simp] theorem length_sregD (n : ℕ) : (sregD n).length = n + 2 := by
  rw [sregD, length_layer]

/-! ### Well-formedness -/

theorem wf_sregB (n : ℕ) : wf (sregB n) := by
  refine wf_layer (fun j hj => ?_)
  rw [sregT]
  split_ifs with h0 h1 h2 h3
  · trivial
  · trivial
  · trivial
  · trivial
  · exact ⟨by omega, by omega⟩

theorem wf_sregD (n : ℕ) : wf (sregD n) := by
  refine wf_layer (fun j _ => ?_)
  rw [sregBaseT]
  split_ifs <;> trivial

theorem inpsLt_sregB (n : ℕ) : inpsLt (n + 2) (sregB n) := by
  intro g hg
  obtain ⟨c, hc, rfl⟩ := mem_layer hg
  rw [sregT]
  split_ifs with h0 h1 h2 h3
  · change n + 1 < n + 2; omega
  · change 0 < n + 2; omega
  · change c - 1 < n + 2; omega
  · trivial
  · trivial

/-! ### The state of the stack -/

/-- The state of the stack after `t` copies: the wire `i ≤ n` holds the bit `t + i` of the input if
there is one, and the wire `n + 1` holds the disjunction of the bits already read. -/
def sregSpec (x : Word) (n t i : ℕ) : Bool :=
  if i ≤ n then (if t + i < n then sregBit x (t + i) else false) else sregOr x t

theorem stateC_sreg_zero (x : Word) (n i : ℕ) (hi : i < n + 2) :
    (stateC x (sregB n) (sregD n) (n + 2) 0).getD i false = sregSpec x n 0 i := by
  have hlen : (vals x (layer (sregBaseT n) (n + 2))).length = n + 2 := by simp
  rw [stateC, iterC_zero, sregD, topVals, hlen, Nat.sub_self, List.drop_zero,
    vals_layer_getD x (sregBaseT n) (n + 2) i hi, lval, sregBaseT, sregSpec]
  by_cases hin : i < n
  · rw [if_pos hin, if_pos (by omega), if_pos (by omega), Nat.zero_add]
    rfl
  · rw [if_neg hin]
    by_cases hi' : i ≤ n
    · rw [if_pos hi', if_neg (by omega)]
      rfl
    · rw [if_neg hi', sregOr_zero]
      rfl

theorem stateC_sreg_succ (x : Word) (n t : ℕ) (ht : t < n)
    (ih : ∀ i, i < n + 2 → (stateC x (sregB n) (sregD n) (n + 2) t).getD i false
      = sregSpec x n t i) (i : ℕ) (hi : i < n + 2) :
    (stateC x (sregB n) (sregD n) (n + 2) (t + 1)).getD i false = sregSpec x n (t + 1) i := by
  set s : List Bool := stateC x (sregB n) (sregD n) (n + 2) t with hs
  have hstep : stateC x (sregB n) (sregD n) (n + 2) (t + 1)
      = stepC (sregB n) (n + 2) s :=
    stateC_succ (wf_sregB n) (inpsLt_sregB n) (by simp) (by simp) x t
  have hlen : (vals s (sregB n)).length = n + 4 := by simp
  have hval : (stepC (sregB n) (n + 2) s).getD i false
      = lval s (sregT n) (2 + i) := by
    rw [stepC, topVals, hlen, getD_drop]
    have h2 : n + 4 - (n + 2) = 2 := by omega
    rw [h2, sregB, vals_layer_getD s (sregT n) (n + 4) (2 + i) (by omega)]
  rw [hstep, hval, lval]
  rcases Nat.lt_or_ge i n with hin | hin
  · -- the register shifts down
    have hc : sregT n (2 + i) = .inp (i + 1) := by
      rw [sregT, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      congr 1
      omega
    rw [hc]
    change s.getD (i + 1) false = _
    rw [ih (i + 1) (by omega)]
    have harg : t + (i + 1) = t + 1 + i := by omega
    rw [sregSpec, sregSpec, if_pos (show i + 1 ≤ n by omega), if_pos (show i ≤ n by omega), harg]
  · rcases Nat.lt_or_ge i (n + 1) with hin1 | hin1
    · -- the register is refilled with `false`
      have hc : sregT n (2 + i) = .cst false := by
        rw [sregT, if_neg (show ¬ (2 + i = 0) by omega), if_neg (show ¬ (2 + i = 1) by omega),
          if_neg (show ¬ (2 + i ≤ n + 1) by omega), if_pos (show 2 + i = n + 2 by omega)]
      rw [hc, sregSpec, if_pos (show i ≤ n by omega),
        if_neg (show ¬ (t + 1 + i < n) by omega)]
      rfl
    · -- the accumulator
      have hieq : i = n + 1 := by omega
      subst hieq
      have hc : sregT n (2 + (n + 1)) = .disj 0 1 := by
        rw [sregT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [hc]
      have h0 : (vals s (layer (sregT n) (2 + (n + 1)))).getD 0 false = lval s (sregT n) 0 :=
        vals_layer_getD s (sregT n) (2 + (n + 1)) 0 (by omega)
      have h1 : (vals s (layer (sregT n) (2 + (n + 1)))).getD 1 false = lval s (sregT n) 1 :=
        vals_layer_getD s (sregT n) (2 + (n + 1)) 1 (by omega)
      have hg0 : lval s (sregT n) 0 = s.getD (n + 1) false := by
        rw [lval, sregT, if_pos rfl]
        rfl
      have hg1 : lval s (sregT n) 1 = s.getD 0 false := by
        rw [lval, sregT, if_neg (by omega), if_pos rfl]
        rfl
      have e1 : sregSpec x n t (n + 1) = sregOr x t := by
        rw [sregSpec, if_neg (show ¬ (n + 1 ≤ n) by omega)]
      have e2 : sregSpec x n t 0 = sregBit x t := by
        rw [sregSpec, if_pos (show 0 ≤ n by omega), if_pos (show t + 0 < n by omega), Nat.add_zero]
      have e3 : sregSpec x n (t + 1) (n + 1) = sregOr x (t + 1) := by
        rw [sregSpec, if_neg (show ¬ (n + 1 ≤ n) by omega)]
      change ((vals s (layer (sregT n) (2 + (n + 1)))).getD 0 false ||
        (vals s (layer (sregT n) (2 + (n + 1)))).getD 1 false) = _
      rw [h0, h1, hg0, hg1, ih (n + 1) (by omega), ih 0 (by omega), e1, e2, e3, sregOr_succ]

/-- **The stack really shifts the register.** -/
theorem stateC_sreg (x : Word) (n : ℕ) :
    ∀ t, t ≤ n → ∀ i, i < n + 2 →
      (stateC x (sregB n) (sregD n) (n + 2) t).getD i false = sregSpec x n t i := by
  intro t
  induction t with
  | zero => intro _ i hi; exact stateC_sreg_zero x n i hi
  | succ t ih =>
      intro ht i hi
      exact stateC_sreg_succ x n t (by omega) (ih (by omega)) i hi

/-- **The output of the stack is the disjunction of the bits of the input.** -/
theorem out_sregC (x : Word) (n : ℕ) : out x (sregC n) = sregOr x n := by
  rw [sregC, out_iterC_state (by omega) (by simp) x n]
  have h := stateC_sreg x n n (le_refl n) (n + 1) (by omega)
  have hi : n + 2 - 1 = n + 1 := by omega
  rw [hi, h, sregSpec, if_neg (by omega)]

theorem sregC_ne_nil (n : ℕ) : sregC n ≠ [] := by
  intro h
  have hlen : (sregC n).length = (n + 2) + n * (n + 4) := by
    rw [sregC, length_iterC, length_sregD, length_sregB]
  rw [h] at hlen
  simp only [List.length_nil] at hlen
  omega

theorem wf_sregC (n : ℕ) : wf (sregC n) :=
  wf_iterC (wf_sregB n) (wf_sregD n) (inpsLt_sregB n) (by simp) n

/-! ### The descriptions -/

/-- The Cobham term writing the token of the gate with identifier `c` of the stage. -/
def sregBlk : Cob :=
  .comp Cob.iteC
    [.proj 1,
      .comp Cob.iteC
        [.comp Cob.tail [.proj 1],
          .comp Cob.iteC
            [.comp Cob.dropU [.comp (.app true) [.proj 2], .proj 1],
              .comp Cob.iteC
                [.comp Cob.dropU [.comp (.app true) [.comp (.app true) [.proj 2]], .proj 1],
                  tokTerm 6 .empty (Cob.constT [true]),
                  tokTerm 2 .empty .empty],
              tokTerm 1 (.comp Cob.tail [.proj 1]) .empty],
          tokTerm 1 .empty .empty],
      tokTerm 1 (.comp (.app true) [.proj 2]) .empty]

theorem eval_sregBlk (n : ℕ) (y : Word) (c : ℕ) :
    sregBlk.eval [y, List.replicate c true, List.replicate n true]
      = encGate (sregT n c) := by
  have hargs : ∀ m : ℕ,
      (Cob.comp Cob.dropU [Cob.constT (List.replicate m true), Cob.proj 1]).eval
        [y, List.replicate c true, List.replicate n true]
        = List.replicate (c - m) true := by
    intro m
    simp [Cob.eval_dropU]
  clear hargs
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [sregBlk]
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero, List.replicate_zero]
    have hg : sregT n 0 = Gate.inp (n + 1) := by rw [sregT, if_pos rfl]
    rw [hg]
    refine eval_tokTerm (Gate.inp (n + 1)) ?_ ?_
    · simp [fld1, List.replicate_succ]
    · simp [fld2]
  · have hcne : List.replicate c true ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_replicate, List.length_nil] at this
      omega
    rcases Nat.eq_or_lt_of_le hc0 with hc1 | hc2
    · -- c = 1
      have hc : c = 1 := hc1.symm
      subst hc
      rw [sregBlk]
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_proj,
        Cob.eval_tail, List.getD_cons_succ, List.getD_cons_zero, if_neg hcne,
        List.tail_replicate]
      have hg : sregT n 1 = Gate.inp 0 := by
        rw [sregT, if_neg (by omega), if_pos rfl]
      rw [hg]
      exact eval_tokTerm (Gate.inp 0) (by simp [fld1]) (by simp [fld2])
    · -- c ≥ 2
      have htne : List.replicate (c - 1) true ≠ [] := by
        intro h
        have := congrArg List.length h
        simp only [List.length_replicate, List.length_nil] at this
        omega
      rw [sregBlk]
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_proj,
        Cob.eval_tail, Cob.eval_dropU, Cob.eval_app, List.getD_cons_succ, List.getD_cons_zero,
        if_neg hcne, if_neg htne, List.length_cons, List.length_replicate, List.drop_replicate,
        List.tail_replicate]
      by_cases hle : c ≤ n + 1
      · have hdrop : List.replicate (c - (n + 1)) true = [] := by
          rw [show c - (n + 1) = 0 by omega]
          rfl
        rw [hdrop, if_pos rfl]
        have hg : sregT n c = Gate.inp (c - 1) := by
          rw [sregT, if_neg (by omega), if_neg (by omega), if_pos hle]
        rw [hg]
        refine eval_tokTerm (Gate.inp (c - 1)) ?_ ?_
        · simp [fld1]
        · simp [fld2]
      · have hdrop : List.replicate (c - (n + 1)) true ≠ [] := by
          intro h
          have := congrArg List.length h
          simp only [List.length_replicate, List.length_nil] at this
          omega
        rw [if_neg hdrop]
        by_cases hle2 : c ≤ n + 2
        · have hc : c = n + 2 := by omega
          have hdrop2 : List.replicate (c - (n + 1 + 1)) true = [] := by
            rw [show c - (n + 1 + 1) = 0 by omega]
            rfl
          rw [hdrop2, if_pos rfl]
          have hg : sregT n c = Gate.cst false := by
            rw [sregT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hc]
          rw [hg]
          exact eval_tokTerm (Gate.cst false) (by simp [fld1]) (by simp [fld2])
        · have hdrop2 : List.replicate (c - (n + 1 + 1)) true ≠ [] := by
            intro h
            have := congrArg List.length h
            simp only [List.length_replicate, List.length_nil] at this
            omega
          rw [if_neg hdrop2]
          have hg : sregT n c = Gate.disj 0 1 := by
            rw [sregT, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          rw [hg]
          refine eval_tokTerm (Gate.disj 0 1) (by simp [fld1]) ?_
          simp [fld2, List.replicate_succ]

theorem length_encGate_sregT (n c l : ℕ) (hc : c ≤ l) :
    (encGate (sregT n c)).length ≤ 13 * (l + n + 1) := by
  rw [length_encGate, sregT]
  split_ifs <;> simp only [tag, fld1, fld2] <;> omega

/-- The Cobham term writing the token of the gate with identifier `c` of the base. -/
def sregBaseBlk : Cob :=
  .comp Cob.iteC
    [.comp Cob.dropU [.proj 1, .proj 2],
      tokTerm 1 (linT 1 2 1) .empty,
      tokTerm 2 .empty .empty]

theorem eval_sregBaseBlk (n : ℕ) (y : Word) (c : ℕ) :
    sregBaseBlk.eval [y, List.replicate c true, List.replicate n true]
      = encGate (sregBaseT n c) := by
  rw [sregBaseBlk]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_iteC, Cob.eval_dropU,
    Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, List.length_replicate,
    List.drop_replicate]
  by_cases hc : c < n
  · have hne : List.replicate (n - c) true ≠ [] := by
      intro h
      have := congrArg List.length h
      simp only [List.length_replicate, List.length_nil] at this
      omega
    rw [if_neg hne]
    have hg : sregBaseT n c = Gate.inp (2 * c + 1) := by rw [sregBaseT, if_pos hc]
    rw [hg]
    refine eval_tokTerm (Gate.inp (2 * c + 1)) ?_ ?_
    · refine eval_linT (i := c) (by simp) ?_
      simp only [fld1]
      omega
    · simp [fld2]
  · have hnil : List.replicate (n - c) true = [] := by
      rw [show n - c = 0 by omega]
      rfl
    rw [hnil, if_pos rfl]
    have hg : sregBaseT n c = Gate.cst false := by rw [sregBaseT, if_neg hc]
    rw [hg]
    exact eval_tokTerm (Gate.cst false) (by simp [fld1]) (by simp [fld2])

theorem length_encGate_sregBaseT (n c l : ℕ) (hc : c ≤ l) :
    (encGate (sregBaseT n c)).length ≤ 10 * (l + n + 1) := by
  rw [length_encGate, sregBaseT]
  split_ifs <;> simp only [tag, fld1, fld2] <;> omega

end CircCode

/-! ### The uniformity of the family -/

theorem codeUniform_sregB : CodeUniform CircCode.sregB := by
  have h := codeUniform_layer (tmpl := CircCode.sregT) (k := fun n => n + 4)
    (cnt := Cob.pre [true, true, true, true] (.comp .smash [Cob.proj 0, Cob.constT [true]]))
    (blkT := CircCode.sregBlk) (K := 13)
    (fun x => by
      simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
        Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil]
      rw [show x.length + 4 = 4 + x.length by omega, List.replicate_add,
        show x.length * (0 + 1) = x.length by omega]
      rfl)
    (fun n y c => CircCode.eval_sregBlk n y c)
    CircCode.length_encGate_sregT
  exact h

theorem codeUniform_sregD : CodeUniform CircCode.sregD := by
  have h := codeUniform_layer (tmpl := CircCode.sregBaseT) (k := fun n => n + 2)
    (cnt := Cob.pre [true, true] (.comp .smash [Cob.proj 0, Cob.constT [true]]))
    (blkT := CircCode.sregBaseBlk) (K := 10)
    (fun x => by
      simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
        Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil]
      rw [show x.length + 2 = 2 + x.length by omega, List.replicate_add,
        show x.length * (0 + 1) = x.length by omega]
      rfl)
    (fun n y c => CircCode.eval_sregBaseBlk n y c)
    CircCode.length_encGate_sregBaseT
  exact h

/-- **The stack of shift-register stages is P-uniform**, by the iteration rule. -/
theorem codeUniform_sregC : CodeUniform CircCode.sregC := by
  have h := codeUniform_iterC (cb := CircCode.sregB) (cd := CircCode.sregD)
    (k := fun n => n) (w := fun n => n + 2)
    codeUniform_sregB codeUniform_sregD
    (fun n => CircCode.wf_sregB n) (fun n => CircCode.inpsLt_sregB n)
    (fun n => by simp) (fun n => by simp)
    (kT := .comp .smash [Cob.proj 0, Cob.constT [true]])
    (wT := Cob.pre [true, true] (.comp .smash [Cob.proj 0, Cob.constT [true]]))
    (fun x => by simp)
    (fun x => by
      simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
        Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil]
      rw [show x.length + 2 = 2 + x.length by omega, List.replicate_add,
        show x.length * (0 + 1) = x.length by omega]
      rfl)
  exact h

/-- **`Complexity.SomeOne` is decided by a P-uniform family built with the iteration rule**, through
the language form `Complexity.pUniformDecidable_iterLang` of that rule: the shift register is the
transition, its accumulator the last wire of the configuration. -/
theorem pUniformDecidable_someOne_of_iter : PUniformDecidable SomeOne := by
  refine pUniformDecidable_iterLang (k := fun n => n) (w := fun n => n + 2)
    codeUniform_sregB codeUniform_sregD
    CircCode.wf_sregB CircCode.wf_sregD CircCode.inpsLt_sregB
    (fun n => by simp) (fun n => by simp) (fun n => Nat.succ_pos (n + 1))
    (kT := .comp .smash [Cob.proj 0, Cob.constT [true]])
    (wT := Cob.pre [true, true] (.comp .smash [Cob.proj 0, Cob.constT [true]]))
    (fun x => by simp)
    (fun x => by
      simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
        Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
        List.length_cons, List.length_nil]
      rw [show x.length + 2 = 2 + x.length by omega, List.replicate_add,
        show x.length * (0 + 1) = x.length by omega]
      rfl)
    (fun n y hy => ?_)
  have hout := CircCode.out_sregC y n
  rw [CircCode.sregC, Tseitin.out_iterC_state (by omega) (by simp) y n] at hout
  rw [hout, SomeOne, Tseitin.inWord_of_pinned n y hy]
  simp only [CircCode.sregOr, List.any_map, List.any_eq_true, List.mem_range,
    Function.comp_def, CircCode.sregBit]

theorem polyManyOne_SAT_someOne_of_iter : SomeOne ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable pUniformDecidable_someOne_of_iter

end Complexity
