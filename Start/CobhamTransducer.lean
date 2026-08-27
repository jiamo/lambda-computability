/-
**Finite-state transducers are Cobham functions.**

The Cook–Levin boundary of this library (`Start/CookLevinUniform.lean`) is *uniformity*: a word
transformation used by the reduction has to be exhibited as a Cobham term.  Writing such terms by
hand is laborious, and the recursion scheme of `Complexity.Cob` — bounded recursion on notation —
only ever sees the *suffix* of its argument.  This module removes that friction once and for all:
every finite-state transducer, in either scanning direction, is a Cobham function.

Main definitions:

* `Complexity.Cob.tableSel` — selecting one of finitely many terms by a unary index;
* `Complexity.Cob.revTerm` — word reversal as a Cobham term;
* `Complexity.rst`, `Complexity.rrun` — the state and the output of a transducer scanning a word
  from the right;
* `Complexity.lst`, `Complexity.lrun` — the same scanning from the left;
* `Complexity.fstStTerm`, `Complexity.fstRunTerm`, `Complexity.lrunTerm` — the Cobham terms.

Main results:

* `Complexity.Cob.eval_revTerm` — **reversal is a Cobham function**;
* `Complexity.eval_fstRunTerm` — **a right-to-left finite-state transduction is a Cobham
  function**;
* `Complexity.eval_lrunTerm` — **a left-to-right finite-state transduction is a Cobham function**.

The output blocks of the transducer are themselves given by Cobham terms in a parameter word, so
the same statement covers transducers whose emitted blocks depend on a polynomial-size parameter.
-/

import Start.CobhamPin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Selecting from a finite table by a unary index -/

/-- `Cob.tableSel fs st` evaluates to the value of `fs[s]`, where `1^s` is the value of `st`. -/
def Cob.tableSel : List Cob → Cob → Cob
  | [], _ => .empty
  | f :: fs, st => Cob.iteT (Cob.nthBit 0 st) (Cob.tableSel fs (Cob.tailN 1 st)) f

theorem Cob.eval_tableSel (fs : List Cob) : ∀ (st : Cob) (args : List Word) (s : ℕ),
    st.eval args = List.replicate s true →
    (Cob.tableSel fs st).eval args = (fs.getD s .empty).eval args := by
  induction fs with
  | nil => intro st args s _; simp [Cob.tableSel]
  | cons f fs ih =>
      intro st args s hst
      cases s with
      | zero =>
          have hc : (Cob.nthBit 0 st).eval args = bw false := by
            rw [Cob.eval_nthBit, hst]; simp
          rw [Cob.tableSel, Cob.eval_iteW hc rfl rfl]
          simp
      | succ s =>
          have hc : (Cob.nthBit 0 st).eval args = bw true := by
            rw [Cob.eval_nthBit, hst]
            simp [List.replicate_succ]
          have hst' : (Cob.tailN 1 st).eval args = List.replicate s true := by
            rw [Cob.eval_tailN, hst, List.replicate_succ]
            simp
          rw [Cob.tableSel, Cob.eval_iteW hc rfl rfl]
          simpa using ih (Cob.tailN 1 st) args s hst'

/-! ### Reversal -/

/-- The step of the reversal recursion. -/
def Cob.revStep (b : Bool) : Cob := .comp Cob.concat [.proj 1, Cob.pre [b] .empty]

/-- **Word reversal**, as a Cobham term. -/
def Cob.revTerm : Cob :=
  .bRec .empty (Cob.revStep false) (Cob.revStep true) (.comp .smash [.proj 0, Cob.trueC])

@[simp] theorem Cob.eval_revTerm (x : Word) (rest : List Word) :
    Cob.revTerm.eval (x :: rest) = x.reverse := by
  induction x with
  | nil => simp [Cob.revTerm]
  | cons b x ih =>
      rw [Cob.revTerm, Cob.eval_bRec_cons, ← Cob.revTerm, ih]
      have hstep : ∀ c : Bool, (Cob.revStep c).eval (x :: x.reverse :: rest)
          = x.reverse ++ [c] := by
        intro c
        simp [Cob.revStep]
      have hlen : (x.reverse ++ [b]).length
          ≤ ((Cob.comp .smash [.proj 0, Cob.trueC]).eval ((b :: x) :: rest)).length := by
        simp
      cases b
      · simp [hstep false]
      · simp [hstep true]

/-! ### Transducers -/

/-- The state reached by the transducer `δ` after scanning the word `x` **from the right**,
starting in the state `s`. -/
def rst (δ : ℕ → Bool → ℕ) (s : ℕ) : Word → ℕ
  | [] => s
  | b :: x => δ (rst δ s x) b

/-- The output of the transducer `(δ, out)` on the word `x`, scanned **from the right** starting
in the state `s`.  Output blocks are emitted in the order of the positions of `x`. -/
def rrun (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) : Word → Word
  | [] => []
  | b :: x => out (rst δ s x) b ++ rrun δ out s x

/-- The state reached by the transducer `δ` after scanning the word `x` **from the left**,
starting in the state `s`. -/
def lst (δ : ℕ → Bool → ℕ) : ℕ → Word → ℕ
  | s, [] => s
  | s, b :: x => lst δ (δ s b) x

/-- The output of the transducer `(δ, out)` on the word `x`, scanned **from the left** starting in
the state `s`. -/
def lrun (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) : ℕ → Word → Word
  | _, [] => []
  | s, b :: x => out s b ++ lrun δ out (δ s b) x

theorem rst_lt {δ : ℕ → Bool → ℕ} {m : ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (x : Word) :
    rst δ 0 x < m := by
  induction x with
  | nil => exact hm
  | cons b x _ => exact hδ _ _

theorem length_rrun (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) {K : ℕ}
    (hK : ∀ t b, (out t b).length ≤ K) (x : Word) : (rrun δ out s x).length ≤ x.length * K := by
  induction x with
  | nil => simp [rrun]
  | cons b x ih =>
      have := hK (rst δ s x) b
      simp only [rrun, List.length_append, List.length_cons]
      calc (out (rst δ s x) b).length + (rrun δ out s x).length
          ≤ K + x.length * K := Nat.add_le_add this ih
        _ = (x.length + 1) * K := by ring

/-! ### The state term -/

/-- The step of the recursion computing the state, for the bit `b`: a table lookup on the state
carried over from the suffix. -/
def fstStep (m : ℕ) (δ : ℕ → Bool → ℕ) (b : Bool) : Cob :=
  Cob.tableSel ((List.range m).map fun s => Cob.pre (List.replicate (δ s b) true) .empty)
    (.proj 1)

/-- The Cobham term computing `1^{rst δ 0 x}` from `x`. -/
def fstStTerm (m : ℕ) (δ : ℕ → Bool → ℕ) : Cob :=
  .bRec .empty (fstStep m δ false) (fstStep m δ true) (Cob.pre (List.replicate m true) .empty)

theorem eval_fstStep {m : ℕ} {δ : ℕ → Bool → ℕ} (b : Bool) {s : ℕ} (hs : s < m) (x : Word)
    (rest : List Word) :
    (fstStep m δ b).eval (x :: List.replicate s true :: rest)
      = List.replicate (δ s b) true := by
  have hst : (Cob.proj 1).eval (x :: List.replicate s true :: rest) = List.replicate s true := by
    simp
  rw [fstStep, Cob.eval_tableSel _ _ _ s hst]
  have hget : (((List.range m).map fun t => Cob.pre (List.replicate (δ t b) true) Cob.empty).getD
      s .empty) = Cob.pre (List.replicate (δ s b) true) .empty := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs]
    rfl
  rw [hget]
  simp

theorem eval_fstStTerm {m : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    (x : Word) (rest : List Word) :
    (fstStTerm m δ).eval (x :: rest) = List.replicate (rst δ 0 x) true := by
  induction x with
  | nil => simp [fstStTerm, rst]
  | cons b x ih =>
      have hlt : rst δ 0 x < m := rst_lt hm hδ x
      rw [fstStTerm, Cob.eval_bRec_cons, ← fstStTerm, ih]
      have hbd : ((Cob.pre (List.replicate m true) Cob.empty).eval ((b :: x) :: rest)).length
          = m := by simp
      have hstep : ∀ c : Bool,
          (fstStep m δ c).eval (x :: List.replicate (rst δ 0 x) true :: rest)
            = List.replicate (δ (rst δ 0 x) c) true :=
        fun c => eval_fstStep c hlt x rest
      have hle : (List.replicate (δ (rst δ 0 x) b) true).length
          ≤ ((Cob.pre (List.replicate m true) Cob.empty).eval ((b :: x) :: rest)).length := by
        rw [hbd]
        simpa using (hδ (rst δ 0 x) b).le
      cases b
      · simpa [rst, hstep false] using List.take_of_length_le hle
      · simpa [rst, hstep true] using List.take_of_length_le hle

/-! ### The output term -/

/-- The output block emitted for the bit `b`, selected by the state of the suffix. -/
def fstOutSel (m : ℕ) (δ : ℕ → Bool → ℕ) (outT : ℕ → Bool → Cob) (b : Bool) : Cob :=
  Cob.tableSel ((List.range m).map fun s => .comp (outT s b) [.proj 2])
    (.comp (fstStTerm m δ) [.proj 0])

/-- The step of the recursion computing the output of the transducer. -/
def fstRunStep (m : ℕ) (δ : ℕ → Bool → ℕ) (outT : ℕ → Bool → Cob) (b : Bool) : Cob :=
  .comp Cob.concat [fstOutSel m δ outT b, .proj 1]

/-- The Cobham term computing the right-to-left transduction, with a parameter word as second
argument. -/
def fstRunTerm (m : ℕ) (δ : ℕ → Bool → ℕ) (outT : ℕ → Bool → Cob) (K : ℕ) : Cob :=
  .bRec .empty (fstRunStep m δ outT false) (fstRunStep m δ outT true)
    (.comp .smash [.proj 0, Cob.pre (List.replicate K true) (.proj 1)])

theorem eval_fstOutSel {m : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    (outT : ℕ → Bool → Cob) (b : Bool) (x r p : Word) :
    (fstOutSel m δ outT b).eval [x, r, p] = (outT (rst δ 0 x) b).eval [p] := by
  have hst : ((Cob.comp (fstStTerm m δ) [Cob.proj 0]).eval [x, r, p])
      = List.replicate (rst δ 0 x) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
    exact eval_fstStTerm hm hδ x []
  rw [fstOutSel, Cob.eval_tableSel _ _ _ (rst δ 0 x) hst]
  have hget : (((List.range m).map fun s => Cob.comp (outT s b) [Cob.proj 2]).getD
      (rst δ 0 x) .empty) = Cob.comp (outT (rst δ 0 x) b) [Cob.proj 2] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (rst_lt hm hδ x)]
    rfl
  rw [hget]
  simp

/-- **A right-to-left finite-state transduction is a Cobham function.** -/
theorem eval_fstRunTerm {m K : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    (outT : ℕ → Bool → Cob) (p : Word)
    (hK : ∀ s b, ((outT s b).eval [p]).length ≤ K + p.length) (x : Word) :
    (fstRunTerm m δ outT K).eval [x, p] = rrun δ (fun s b => (outT s b).eval [p]) 0 x := by
  induction x with
  | nil => simp [fstRunTerm, rrun]
  | cons b x ih =>
      rw [fstRunTerm, Cob.eval_bRec_cons, ← fstRunTerm]
      rw [ih]
      set out : ℕ → Bool → Word := fun s c => (outT s c).eval [p] with hout
      have hstep : ∀ c : Bool, (fstRunStep m δ outT c).eval [x, rrun δ out 0 x, p]
          = out (rst δ 0 x) c ++ rrun δ out 0 x := by
        intro c
        rw [fstRunStep]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_proj,
          List.getD_cons_succ, List.getD_cons_zero]
        rw [eval_fstOutSel hm hδ outT c x (rrun δ out 0 x) p]
      have hbdlen : ((Cob.comp .smash
          [Cob.proj 0, Cob.pre (List.replicate K true) (Cob.proj 1)]).eval
          ((b :: x) :: [p])).length = (x.length + 1) * (K + p.length) := by
        simp
      have hle : (out (rst δ 0 x) b ++ rrun δ out 0 x).length
          ≤ ((Cob.comp .smash [Cob.proj 0,
              Cob.pre (List.replicate K true) (Cob.proj 1)]).eval ((b :: x) :: [p])).length := by
        rw [hbdlen, List.length_append]
        have h₁ : (out (rst δ 0 x) b).length ≤ K + p.length := hK _ _
        have h₂ : (rrun δ out 0 x).length ≤ x.length * (K + p.length) :=
          length_rrun δ out 0 (fun t c => hK t c) x
        calc (out (rst δ 0 x) b).length + (rrun δ out 0 x).length
            ≤ (K + p.length) + x.length * (K + p.length) := Nat.add_le_add h₁ h₂
          _ = (x.length + 1) * (K + p.length) := by ring
      cases b
      · rw [if_neg (by simp), hstep false, List.take_of_length_le hle]
        rfl
      · rw [if_pos rfl, hstep true, List.take_of_length_le hle]
        rfl

/-! ### Scanning from the left -/

/-- The state after scanning a concatenation from the right: the right factor is scanned first. -/
theorem rst_append (δ : ℕ → Bool → ℕ) (s : ℕ) (y z : Word) :
    rst δ s (y ++ z) = rst δ (rst δ s z) y := by
  induction y with
  | nil => rfl
  | cons c y ih => rw [List.cons_append, rst, rst, ih]

/-- The output on a concatenation: the right factor is scanned first, and its output comes
last. -/
theorem rrun_append (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) (y z : Word) :
    rrun δ out s (y ++ z) = rrun δ out (rst δ s z) y ++ rrun δ out s z := by
  induction y with
  | nil => simp [rrun]
  | cons c y ih =>
      rw [List.cons_append, rrun, rrun, ih, rst_append, List.append_assoc]

theorem rst_append_singleton (δ : ℕ → Bool → ℕ) (s : ℕ) (b : Bool) (y : Word) :
    rst δ s (y ++ [b]) = rst δ (δ s b) y := by
  rw [rst_append]
  rfl

theorem rrun_append_singleton (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) (b : Bool)
    (y : Word) : rrun δ out s (y ++ [b]) = rrun δ out (δ s b) y ++ out s b := by
  rw [rrun_append]
  simp [rrun, rst]

theorem rrun_reverse (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) (x : Word) :
    rrun δ (fun t b => (out t b).reverse) s x.reverse = (lrun δ out s x).reverse := by
  induction x generalizing s with
  | nil => simp [rrun, lrun]
  | cons b x ih =>
      rw [List.reverse_cons, rrun_append_singleton, ih, lrun, List.reverse_append]

/-- The Cobham term computing the left-to-right transduction, with a parameter word as second
argument. -/
def lrunTerm (m : ℕ) (δ : ℕ → Bool → ℕ) (outT : ℕ → Bool → Cob) (K : ℕ) : Cob :=
  .comp Cob.revTerm
    [.comp (fstRunTerm m δ (fun s b => .comp Cob.revTerm [outT s b]) K)
      [.comp Cob.revTerm [.proj 0], .proj 1]]

/-- **A left-to-right finite-state transduction is a Cobham function.** -/
theorem eval_lrunTerm {m K : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    (outT : ℕ → Bool → Cob) (p : Word)
    (hK : ∀ s b, ((outT s b).eval [p]).length ≤ K + p.length) (x : Word) :
    (lrunTerm m δ outT K).eval [x, p] = lrun δ (fun s b => (outT s b).eval [p]) 0 x := by
  have hK' : ∀ s b, (((Cob.comp Cob.revTerm [outT s b])).eval [p]).length ≤ K + p.length := by
    intro s b
    have := hK s b
    simpa using this
  have hmain := eval_fstRunTerm (m := m) (K := K) hm hδ
    (fun s b => .comp Cob.revTerm [outT s b]) p hK' x.reverse
  have hrev : ∀ s b, ((Cob.comp Cob.revTerm [outT s b]).eval [p]) = ((outT s b).eval [p]).reverse :=
    by intro s b; simp
  rw [lrunTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    List.getD_cons_succ, Cob.eval_revTerm]
  rw [hmain]
  simp only [hrev]
  rw [rrun_reverse δ (fun s b => (outT s b).eval [p]) 0 x, List.reverse_reverse]

end Complexity
