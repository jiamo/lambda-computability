/-
SAT: conjunctive normal forms encoded as binary words, and the proof that the resulting
language is in `NP`.

A CNF is a list of clauses, a clause is a list of literals, and a literal is a pair
`(sign, index)`.  Words encode CNFs by a prefix-free token code that is read **from the right**,
which is the direction in which Cobham's bounded recursion on notation consumes its argument:

* `1`     — a *tick*, incrementing the variable index of the literal being read;
* `0 1`   — a negative literal, whose variable is the current tick count;
* `0 0 1` — a positive literal;
* `0 0 0` — a clause separator.

`encLit`, `encClause` and `encCnf` write the code out, and `decode : Word → Cnf` reads any word
back — junk is decoded to the CNF of the tokens that could be recognized, so `decode` is total and
surjective, and `decode (encCnf F) = F`.

Main definitions:

* `Complexity.Sat.cnfVal` — the truth value of a CNF under an assignment;
* `Complexity.Sat.encCnf`, `Complexity.Sat.decode` — the encoding of CNFs as binary words;
* `Complexity.Sat.SAT` — the language of words whose CNF is satisfiable;
* `Complexity.Sat.satMachine`, `Complexity.Sat.satVerifier` — the Cobham (polynomial-time)
  evaluator and NP-verifier for that encoding.

Main results:

* `Complexity.Sat.decode_encCnf` — decoding inverts the encoding;
* `Complexity.Sat.eval_satMachine` — the Cobham term `satMachine` really runs the evaluator;
* `Complexity.Sat.inNP_SAT` — **SAT is in NP**;
* `Complexity.Sat.SAT_encCnf` — a word encoding a CNF is in `SAT` exactly when that CNF is
  satisfiable.
-/

import Mathlib
import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Small Cobham gadgets -/

/-- The word representing a Boolean value: `[true]` for `true` and the empty word for `false`.
This is the "accept = nonempty output" convention of `Start/ComplexityClasses.lean`. -/
def bw (b : Bool) : Word := if b then [true] else []

@[simp] theorem bw_true : bw true = [true] := rfl

@[simp] theorem bw_false : bw false = [] := rfl

@[simp] theorem bw_eq_nil_iff (b : Bool) : bw b = [] ↔ b = false := by
  cases b <;> simp [bw]

/-- The three-argument conditional `if c ≠ [] then a else b`. -/
def Cob.iteC : Cob := .bRec (.proj 1) (.proj 2) (.proj 2) (.proj 1)

@[simp] theorem Cob.eval_iteC (c a b : Word) :
    Cob.iteC.eval [c, a, b] = if c = [] then b else a := by
  cases c with
  | nil => simp [Cob.iteC]
  | cons x c => cases x <;> simp [Cob.iteC, List.take_of_length_le]

/-- Dropping `|u|` bits from the second argument. -/
def Cob.dropU : Cob := .bRec (.proj 0) (.comp .tailC [.proj 1]) (.comp .tailC [.proj 1]) (.proj 1)

@[simp] theorem Cob.eval_dropU (u σ : Word) : Cob.dropU.eval [u, σ] = σ.drop u.length := by
  induction u with
  | nil => simp [Cob.dropU]
  | cons b u ih =>
      rw [Cob.dropU, Cob.eval_bRec_cons, ← Cob.dropU, ih]
      have hlen : (σ.drop u.length).tail.length ≤ σ.length := by
        simp only [List.length_tail, List.length_drop]; omega
      cases b <;>
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
          List.getD_cons_zero, List.getD_cons_succ, Cob.eval_tailC, Bool.false_eq_true,
          if_true, if_false, List.length_cons] <;>
        rw [List.take_of_length_le hlen, List.tail_drop]

/-- Iterated tail. -/
def Cob.tailN : ℕ → Cob → Cob
  | 0, t => t
  | n + 1, t => .comp .tailC [Cob.tailN n t]

theorem Cob.eval_tailN (n : ℕ) (t : Cob) (args : List Word) :
    (Cob.tailN n t).eval args = (t.eval args).drop n := by
  induction n with
  | zero => simp [Cob.tailN]
  | succ n ih => simp [Cob.tailN, ih, List.tail_drop]

theorem headD_drop (l : Word) (n : ℕ) : (l.drop n).headD false = l.getD n false := by
  induction n generalizing l with
  | zero => cases l <;> simp
  | succ n ih =>
      cases l with
      | nil => simp
      | cons a l => simp

/-- Bit `i` of the word computed by `t`, as a Boolean word. -/
def Cob.nthBit (i : ℕ) (t : Cob) : Cob := .comp .headTrue [Cob.tailN i t]

theorem Cob.eval_nthBit (i : ℕ) (t : Cob) (args : List Word) :
    (Cob.nthBit i t).eval args = bw ((t.eval args).getD i false) := by
  simp only [Cob.nthBit, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_headTrue,
    Cob.eval_tailN, headD_drop]
  simp [bw]

/-- Conjunction of two Boolean-valued terms. -/
def Cob.andT (s t : Cob) : Cob := .comp .andC [s, t]

/-- Disjunction of two Boolean-valued terms. -/
def Cob.orT (s t : Cob) : Cob := .comp .orC [s, t]

/-- Negation of a Boolean-valued term. -/
def Cob.notT (s : Cob) : Cob := .comp .notC [s]

/-- Conditional on a Boolean-valued term. -/
def Cob.iteT (c s t : Cob) : Cob := .comp Cob.iteC [c, s, t]

/-- Prepend the bit computed by the Boolean-valued term `c` to the word computed by `t`. -/
def Cob.consT (c t : Cob) : Cob :=
  Cob.iteT c (.comp (.app true) [t]) (.comp (.app false) [t])

theorem Cob.eval_andT {s t : Cob} {args : List Word} {p q : Bool}
    (hs : s.eval args = bw p) (ht : t.eval args = bw q) :
    (Cob.andT s t).eval args = bw (p && q) := by
  cases p <;> cases q <;> simp [Cob.andT, hs, ht, bw]

theorem Cob.eval_orT {s t : Cob} {args : List Word} {p q : Bool}
    (hs : s.eval args = bw p) (ht : t.eval args = bw q) :
    (Cob.orT s t).eval args = bw (p || q) := by
  cases p <;> cases q <;> simp [Cob.orT, hs, ht, bw]

theorem Cob.eval_notT {s : Cob} {args : List Word} {p : Bool} (hs : s.eval args = bw p) :
    (Cob.notT s).eval args = bw (!p) := by
  cases p <;> simp [Cob.notT, hs, bw]

/-- A word-valued conditional. -/
theorem Cob.eval_iteW {c s t : Cob} {args : List Word} {p : Bool} {a b : Word}
    (hc : c.eval args = bw p) (hs : s.eval args = a) (ht : t.eval args = b) :
    (Cob.iteT c s t).eval args = if p then a else b := by
  cases p <;> simp [Cob.iteT, hc, hs, ht, bw]

/-- A Boolean-valued conditional. -/
theorem Cob.eval_iteB {c s t : Cob} {args : List Word} {p x y : Bool}
    (hc : c.eval args = bw p) (hs : s.eval args = bw x) (ht : t.eval args = bw y) :
    (Cob.iteT c s t).eval args = bw (if p then x else y) := by
  cases p <;> simp [Cob.iteT, hc, hs, ht, bw]

theorem Cob.eval_consT {c t : Cob} {args : List Word} {p : Bool} {a : Word}
    (hc : c.eval args = bw p) (ht : t.eval args = a) :
    (Cob.consT c t).eval args = p :: a := by
  cases p <;> simp [Cob.consT, Cob.iteT, hc, ht, bw]

namespace Sat

/-! ### Conjunctive normal forms -/

/-- A literal: `(true, k)` is the variable `k`, `(false, k)` its negation. -/
abbrev Lit := Bool × ℕ

/-- A clause: a disjunction of literals. -/
abbrev Clause := List Lit

/-- A formula in conjunctive normal form: a conjunction of clauses. -/
abbrev Cnf := List Clause

/-- The value of a literal under an assignment; bits beyond the end of `σ` count as `false`. -/
def litVal (σ : Word) (l : Lit) : Bool :=
  if l.1 then σ.getD l.2 false else !(σ.getD l.2 false)

/-- The value of a clause: the disjunction of its literals. -/
def clauseVal (σ : Word) (C : Clause) : Bool := C.any (litVal σ)

/-- The value of a CNF: the conjunction of its clauses. -/
def cnfVal (σ : Word) (F : Cnf) : Bool := F.all (clauseVal σ)

@[simp] theorem clauseVal_nil (σ : Word) : clauseVal σ [] = false := rfl

@[simp] theorem clauseVal_cons (σ : Word) (l : Lit) (C : Clause) :
    clauseVal σ (l :: C) = (litVal σ l || clauseVal σ C) := rfl

@[simp] theorem cnfVal_nil (σ : Word) : cnfVal σ [] = true := rfl

@[simp] theorem cnfVal_cons (σ : Word) (C : Clause) (F : Cnf) :
    cnfVal σ (C :: F) = (clauseVal σ C && cnfVal σ F) := rfl

/-! ### The token code -/

/-- The phase of the token reader: reading ticks, after one escape bit, after two. -/
inductive Phase where
  /-- Reading ticks. -/
  | main : Phase
  /-- One escape bit `0` has been read. -/
  | esc : Phase
  /-- Two escape bits `0 0` have been read. -/
  | esc2 : Phase
  deriving DecidableEq, Inhabited

/-- The state of the decoder. -/
structure DSt where
  /-- The clauses decoded so far. -/
  done : Cnf
  /-- The literals of the clause currently being read. -/
  cur : Clause
  /-- The number of ticks read since the last token. -/
  ticks : ℕ
  /-- The reader phase. -/
  phase : Phase
  deriving Inhabited

/-- One step of the decoder, reading the bit `b`. -/
def dstep (b : Bool) (d : DSt) : DSt :=
  match d.phase, b with
  | .main, true => { d with ticks := d.ticks + 1 }
  | .main, false => { d with phase := .esc }
  | .esc, true => { d with cur := (false, d.ticks) :: d.cur, ticks := 0, phase := .main }
  | .esc, false => { d with phase := .esc2 }
  | .esc2, true => { d with cur := (true, d.ticks) :: d.cur, ticks := 0, phase := .main }
  | .esc2, false => ⟨d.cur :: d.done, [], 0, .main⟩

/-- The decoder run on `u` starting from the state `d`; the word is read from the right. -/
def drunFrom (d : DSt) (u : Word) : DSt := u.foldr dstep d

/-- The initial decoder state. -/
def dinit : DSt := ⟨[], [], 0, .main⟩

/-- The decoder run on `u`. -/
def drun (u : Word) : DSt := drunFrom dinit u

/-- The CNF encoded by a word. -/
def decode (u : Word) : Cnf := (drun u).done

theorem drunFrom_append (d : DSt) (u v : Word) :
    drunFrom d (u ++ v) = drunFrom (drunFrom d v) u := by
  simp [drunFrom, List.foldr_append]

@[simp] theorem drunFrom_nil (d : DSt) : drunFrom d [] = d := rfl

@[simp] theorem drunFrom_cons (d : DSt) (b : Bool) (u : Word) :
    drunFrom d (b :: u) = dstep b (drunFrom d u) := rfl

/-! ### The encoder -/

/-- The code of a literal: the command bits followed (to the right) by the unary index. -/
def encLit (l : Lit) : Word :=
  (if l.1 then [true, false, false] else [true, false]) ++ List.replicate l.2 true

/-- The code of a clause: the separator followed by the codes of its literals. -/
def encClause (C : Clause) : Word := [false, false, false] ++ C.flatMap encLit

/-- The code of a CNF. -/
def encCnf (F : Cnf) : Word := F.flatMap encClause

theorem drunFrom_replicate (d : DSt) (hp : d.phase = .main) (k : ℕ) :
    drunFrom d (List.replicate k true) = { d with ticks := d.ticks + k } := by
  induction k with
  | zero => cases d; simp
  | succ k ih =>
      rw [List.replicate_succ, drunFrom_cons, ih]
      cases d
      simp_all [dstep]
      omega

theorem drunFrom_encLit (d : DSt) (hp : d.phase = .main) (ht : d.ticks = 0) (l : Lit) :
    drunFrom d (encLit l) = { d with cur := l :: d.cur, ticks := 0, phase := .main } := by
  obtain ⟨s, k⟩ := l
  rw [encLit, drunFrom_append, drunFrom_replicate d hp k, ht]
  cases s <;> cases d <;> simp_all [drunFrom, dstep]

theorem drunFrom_lits (d : DSt) (hp : d.phase = .main) (ht : d.ticks = 0) (ls : List Lit) :
    drunFrom d (ls.flatMap encLit) =
      { d with cur := ls ++ d.cur, ticks := 0, phase := .main } := by
  induction ls with
  | nil => cases d; simp_all
  | cons l ls ih =>
      rw [List.flatMap_cons, drunFrom_append, ih, drunFrom_encLit _ rfl rfl l]
      simp

theorem drunFrom_encClause (d : DSt) (hp : d.phase = .main) (ht : d.ticks = 0)
    (hc : d.cur = []) (C : Clause) :
    drunFrom d (encClause C) = ⟨C :: d.done, [], 0, .main⟩ := by
  rw [encClause, drunFrom_append, drunFrom_lits d hp ht C]
  simp [drunFrom, dstep, hc]

theorem drun_encCnf (F : Cnf) : drun (encCnf F) = ⟨F, [], 0, .main⟩ := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      rw [encCnf, List.flatMap_cons, ← encCnf, drun, drunFrom_append, ← drun, ih,
        drunFrom_encClause _ rfl rfl rfl]

/-- **Decoding inverts the encoding**: every CNF is the value of the decoder on its code. -/
@[simp] theorem decode_encCnf (F : Cnf) : decode (encCnf F) = F := by
  rw [decode, drun_encCnf]

/-! ### The language SAT -/

/-- **SAT**: the words whose decoded CNF is satisfiable. -/
def SAT : Language := fun u => ∃ σ : Word, cnfVal σ (decode u) = true

/-! ### The evaluator -/

/-- The state of the evaluator: the truth of the clauses already read, the truth of the clause
being read, the remaining assignment bits, and the reader phase. -/
structure MSt where
  /-- Whether every clause read so far is satisfied. -/
  allSat : Bool
  /-- Whether the clause currently being read is already satisfied. -/
  curSat : Bool
  /-- The assignment from the current variable index on. -/
  ptr : Word
  /-- The reader phase. -/
  phase : Phase

/-- One step of the evaluator against the assignment `σ`. -/
def mstep (σ : Word) (b : Bool) (m : MSt) : MSt :=
  match m.phase, b with
  | .main, true => { m with ptr := m.ptr.tail }
  | .main, false => { m with phase := .esc }
  | .esc, true =>
      { m with curSat := m.curSat || !(m.ptr.headD false), ptr := σ, phase := .main }
  | .esc, false => { m with phase := .esc2 }
  | .esc2, true => { m with curSat := m.curSat || m.ptr.headD false, ptr := σ, phase := .main }
  | .esc2, false => ⟨m.allSat && m.curSat, false, σ, .main⟩

/-- The evaluator run on the word `u` against the assignment `σ`. -/
def mrun (σ u : Word) : MSt := u.foldr (mstep σ) ⟨true, false, σ, .main⟩

@[simp] theorem mrun_nil (σ : Word) : mrun σ [] = ⟨true, false, σ, .main⟩ := rfl

@[simp] theorem mrun_cons (σ : Word) (b : Bool) (u : Word) :
    mrun σ (b :: u) = mstep σ b (mrun σ u) := rfl

/-- **The evaluator simulates the decoder**: its state is the truth value of the decoded data. -/
theorem mrun_eq (σ u : Word) :
    mrun σ u = ⟨cnfVal σ (drun u).done, clauseVal σ (drun u).cur, σ.drop (drun u).ticks,
      (drun u).phase⟩ := by
  induction u with
  | nil => simp [drun, dinit]
  | cons b u ih =>
      rw [mrun_cons, ih]
      have hd : drun (b :: u) = dstep b (drun u) := rfl
      rw [hd]
      cases hp : (drun u).phase <;> cases b <;>
        simp [mstep, dstep, hp, litVal, List.tail_drop, Bool.or_comm, Bool.and_comm]

/-! ### The evaluator as a Cobham term -/

/-- The high bit of the two-bit code of a phase. -/
def phaseBit1 : Phase → Bool
  | .main => false
  | .esc => false
  | .esc2 => true

/-- The low bit of the two-bit code of a phase. -/
def phaseBit0 : Phase → Bool
  | .main => false
  | .esc => true
  | .esc2 => false

/-- The evaluator state as a word: four control bits followed by the remaining assignment. -/
def encMSt (m : MSt) : Word :=
  m.allSat :: m.curSat :: phaseBit1 m.phase :: phaseBit0 m.phase :: m.ptr

/-- The state read by the step terms. -/
def stT : Cob := .proj 1

/-- The assignment read by the step terms. -/
def sgT : Cob := .proj 2

/-- The `allSat` bit. -/
def aT : Cob := Cob.nthBit 0 stT

/-- The `curSat` bit. -/
def cT : Cob := Cob.nthBit 1 stT

/-- The high phase bit. -/
def p1T : Cob := Cob.nthBit 2 stT

/-- The low phase bit. -/
def p0T : Cob := Cob.nthBit 3 stT

/-- The current assignment bit. -/
def hlT : Cob := Cob.nthBit 4 stT

/-- The remaining assignment. -/
def lT : Cob := Cob.tailN 4 stT

/-- The remaining assignment, with one more bit consumed. -/
def ltT : Cob := Cob.tailN 5 stT

/-- The step term for the bit `true`. -/
def stepTrue : Cob :=
  Cob.consT aT
    (Cob.consT (Cob.iteT p0T (Cob.orT cT (Cob.notT hlT)) (Cob.iteT p1T (Cob.orT cT hlT) cT))
      (Cob.consT .empty (Cob.consT .empty (Cob.iteT (Cob.orT p0T p1T) sgT ltT))))

/-- The step term for the bit `false`. -/
def stepFalse : Cob :=
  Cob.consT (Cob.iteT p1T (Cob.andT aT cT) aT)
    (Cob.consT (Cob.iteT p1T .empty cT)
      (Cob.consT p0T (Cob.consT (Cob.andT (Cob.notT p1T) (Cob.notT p0T))
        (Cob.iteT p1T sgT lT))))

/-- The initial state term. -/
def initT : Cob :=
  .comp (.app true) [.comp (.app false) [.comp (.app false) [.comp (.app false) [.proj 0]]]]

/-- The bound term for the recursion. -/
def boundT : Cob :=
  .comp (.app true) [.comp (.app true) [.comp (.app true) [.comp (.app true) [.proj 1]]]]

/-- **The evaluator as a Cobham (polynomial-time) function**. -/
def satMachine : Cob := .bRec initT stepFalse stepTrue boundT

section StepEval

variable (m : MSt) (u σ : Word)

theorem eval_stT : stT.eval [u, encMSt m, σ] = encMSt m := by simp [stT]

theorem eval_sgT : sgT.eval [u, encMSt m, σ] = σ := by simp [sgT]

theorem eval_aT : aT.eval [u, encMSt m, σ] = bw m.allSat := by
  rw [aT, Cob.eval_nthBit, eval_stT]; rfl

theorem eval_cT : cT.eval [u, encMSt m, σ] = bw m.curSat := by
  rw [cT, Cob.eval_nthBit, eval_stT]; rfl

theorem eval_p1T : p1T.eval [u, encMSt m, σ] = bw (phaseBit1 m.phase) := by
  rw [p1T, Cob.eval_nthBit, eval_stT]; rfl

theorem eval_p0T : p0T.eval [u, encMSt m, σ] = bw (phaseBit0 m.phase) := by
  rw [p0T, Cob.eval_nthBit, eval_stT]; rfl

theorem eval_hlT : hlT.eval [u, encMSt m, σ] = bw (m.ptr.headD false) := by
  rw [hlT, Cob.eval_nthBit, eval_stT]
  rcases m with ⟨a, c, ptr, ph⟩
  cases ptr <;> simp [encMSt]

theorem eval_lT : lT.eval [u, encMSt m, σ] = m.ptr := by
  rw [lT, Cob.eval_tailN, eval_stT]
  rcases m with ⟨a, c, ptr, ph⟩
  simp [encMSt]

theorem eval_ltT : ltT.eval [u, encMSt m, σ] = m.ptr.tail := by
  rw [ltT, Cob.eval_tailN, eval_stT]
  rcases m with ⟨a, c, ptr, ph⟩
  cases ptr <;> simp [encMSt]

theorem eval_emptyT : (Cob.empty : Cob).eval [u, encMSt m, σ] = bw false := by simp

end StepEval

theorem eval_stepTrue (m : MSt) (u σ : Word) :
    stepTrue.eval [u, encMSt m, σ] = encMSt (mstep σ true m) := by
  have e1 : (Cob.orT cT (Cob.notT hlT)).eval [u, encMSt m, σ]
      = bw (m.curSat || !(m.ptr.headD false)) :=
    Cob.eval_orT (eval_cT m u σ) (Cob.eval_notT (eval_hlT m u σ))
  have e2 : (Cob.orT cT hlT).eval [u, encMSt m, σ] = bw (m.curSat || m.ptr.headD false) :=
    Cob.eval_orT (eval_cT m u σ) (eval_hlT m u σ)
  have e3 : (Cob.iteT p1T (Cob.orT cT hlT) cT).eval [u, encMSt m, σ]
      = bw (if phaseBit1 m.phase then (m.curSat || m.ptr.headD false) else m.curSat) :=
    Cob.eval_iteB (eval_p1T m u σ) e2 (eval_cT m u σ)
  have e4 : (Cob.iteT p0T (Cob.orT cT (Cob.notT hlT))
        (Cob.iteT p1T (Cob.orT cT hlT) cT)).eval [u, encMSt m, σ]
      = bw (if phaseBit0 m.phase then (m.curSat || !(m.ptr.headD false))
          else (if phaseBit1 m.phase then (m.curSat || m.ptr.headD false) else m.curSat)) :=
    Cob.eval_iteB (eval_p0T m u σ) e1 e3
  have e5 : (Cob.orT p0T p1T).eval [u, encMSt m, σ]
      = bw (phaseBit0 m.phase || phaseBit1 m.phase) :=
    Cob.eval_orT (eval_p0T m u σ) (eval_p1T m u σ)
  have e6 : (Cob.iteT (Cob.orT p0T p1T) sgT ltT).eval [u, encMSt m, σ]
      = if phaseBit0 m.phase || phaseBit1 m.phase then σ else m.ptr.tail :=
    Cob.eval_iteW e5 (eval_sgT m u σ) (eval_ltT m u σ)
  have e7 : (Cob.consT .empty (Cob.iteT (Cob.orT p0T p1T) sgT ltT)).eval [u, encMSt m, σ]
      = false :: (if phaseBit0 m.phase || phaseBit1 m.phase then σ else m.ptr.tail) :=
    Cob.eval_consT (eval_emptyT m u σ) e6
  have e8 : (Cob.consT .empty (Cob.consT .empty
        (Cob.iteT (Cob.orT p0T p1T) sgT ltT))).eval [u, encMSt m, σ]
      = false :: false :: (if phaseBit0 m.phase || phaseBit1 m.phase then σ else m.ptr.tail) :=
    Cob.eval_consT (eval_emptyT m u σ) e7
  rw [stepTrue, Cob.eval_consT (eval_aT m u σ) (Cob.eval_consT e4 e8)]
  rcases m with ⟨a, c, ptr, ph⟩
  cases ph <;> simp [mstep, encMSt, phaseBit0, phaseBit1]

theorem eval_stepFalse (m : MSt) (u σ : Word) :
    stepFalse.eval [u, encMSt m, σ] = encMSt (mstep σ false m) := by
  have e1 : (Cob.andT aT cT).eval [u, encMSt m, σ] = bw (m.allSat && m.curSat) :=
    Cob.eval_andT (eval_aT m u σ) (eval_cT m u σ)
  have e2 : (Cob.iteT p1T (Cob.andT aT cT) aT).eval [u, encMSt m, σ]
      = bw (if phaseBit1 m.phase then (m.allSat && m.curSat) else m.allSat) :=
    Cob.eval_iteB (eval_p1T m u σ) e1 (eval_aT m u σ)
  have e3 : (Cob.iteT p1T .empty cT).eval [u, encMSt m, σ]
      = bw (if phaseBit1 m.phase then false else m.curSat) :=
    Cob.eval_iteB (eval_p1T m u σ) (eval_emptyT m u σ) (eval_cT m u σ)
  have e4 : (Cob.andT (Cob.notT p1T) (Cob.notT p0T)).eval [u, encMSt m, σ]
      = bw (!phaseBit1 m.phase && !phaseBit0 m.phase) :=
    Cob.eval_andT (Cob.eval_notT (eval_p1T m u σ)) (Cob.eval_notT (eval_p0T m u σ))
  have e5 : (Cob.iteT p1T sgT lT).eval [u, encMSt m, σ]
      = if phaseBit1 m.phase then σ else m.ptr :=
    Cob.eval_iteW (eval_p1T m u σ) (eval_sgT m u σ) (eval_lT m u σ)
  have e6 : (Cob.consT (Cob.andT (Cob.notT p1T) (Cob.notT p0T))
        (Cob.iteT p1T sgT lT)).eval [u, encMSt m, σ]
      = (!phaseBit1 m.phase && !phaseBit0 m.phase) ::
          (if phaseBit1 m.phase then σ else m.ptr) :=
    Cob.eval_consT e4 e5
  have e7 : (Cob.consT p0T (Cob.consT (Cob.andT (Cob.notT p1T) (Cob.notT p0T))
        (Cob.iteT p1T sgT lT))).eval [u, encMSt m, σ]
      = phaseBit0 m.phase :: (!phaseBit1 m.phase && !phaseBit0 m.phase) ::
          (if phaseBit1 m.phase then σ else m.ptr) :=
    Cob.eval_consT (eval_p0T m u σ) e6
  rw [stepFalse, Cob.eval_consT e2 (Cob.eval_consT e3 e7)]
  rcases m with ⟨a, c, ptr, ph⟩
  cases ph <;> simp [mstep, encMSt, phaseBit0, phaseBit1]

theorem mrun_ptr_length (σ u : Word) : (mrun σ u).ptr.length ≤ σ.length := by
  rw [mrun_eq]
  simp only [List.length_drop]
  omega

theorem encMSt_length (m : MSt) : (encMSt m).length = m.ptr.length + 4 := by
  simp only [encMSt, List.length_cons]

theorem length_boundT (b : Bool) (u σ : Word) :
    (boundT.eval [b :: u, σ]).length = σ.length + 4 := by
  simp only [boundT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero, Cob.eval_app, List.length_cons]

/-- **The Cobham term `satMachine` computes the evaluator.** -/
theorem eval_satMachine (u σ : Word) : satMachine.eval [u, σ] = encMSt (mrun σ u) := by
  induction u with
  | nil => simp [satMachine, initT, encMSt, phaseBit0, phaseBit1]
  | cons b u ih =>
      have hlen : (encMSt (mrun σ (b :: u))).length ≤ (boundT.eval [b :: u, σ]).length := by
        rw [length_boundT, encMSt_length]
        have := mrun_ptr_length σ (b :: u)
        omega
      rw [satMachine, Cob.eval_bRec_cons, ← satMachine, ih]
      cases b
      · rw [if_neg (by simp), eval_stepFalse, ← mrun_cons]
        exact List.take_of_length_le hlen
      · rw [if_pos rfl, eval_stepTrue, ← mrun_cons]
        exact List.take_of_length_le hlen

/-! ### SAT is in NP -/

/-- The NP-verifier for SAT: check that the witness is not longer than the input, then run the
evaluator and read its `allSat` bit. -/
def satVerifier : Cob :=
  .comp .andC
    [ .comp .notC [.comp Cob.dropU [.proj 0, .proj 1]],
      .comp .headTrue [.comp satMachine [.proj 0, .proj 1]] ]

theorem eval_satVerifier (u w : Word) :
    satVerifier.eval [u, w] ≠ [] ↔ w.length ≤ u.length ∧ (mrun w u).allSat = true := by
  have h2 : (satMachine.eval [u, w]) = encMSt (mrun w u) := eval_satMachine u w
  simp only [satVerifier, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_dropU, h2, Cob.eval_notC,
    Cob.eval_headTrue, Cob.eval_andC, encMSt, List.headD_cons]
  by_cases hd : w.drop u.length = []
  · have hle : w.length ≤ u.length := by
      have h := List.length_drop (l := w) (i := u.length)
      rw [hd] at h
      simp only [List.length_nil] at h
      omega
    by_cases ha : (mrun w u).allSat <;> simp [hd, ha, hle]
  · have hlt : ¬ (w.length ≤ u.length) := fun hle => hd (List.drop_eq_nil_of_le hle)
    simp [hd, hlt]

/-! ### The witness may be taken no longer than the input -/

/-- Bounds on the variable indices produced by the decoder. -/
def DSt.Bounded (n : ℕ) (d : DSt) : Prop :=
  d.ticks ≤ n ∧ (∀ l ∈ d.cur, l.2 < n) ∧ (∀ C ∈ d.done, ∀ l ∈ C, l.2 < n)

theorem DSt.Bounded.mono {n m : ℕ} {d : DSt} (h : DSt.Bounded n d) (hnm : n ≤ m) :
    DSt.Bounded m d :=
  ⟨le_trans h.1 hnm, fun l hl => lt_of_lt_of_le (h.2.1 l hl) hnm,
    fun C hC l hl => lt_of_lt_of_le (h.2.2 C hC l hl) hnm⟩

theorem dstep_bounded {d : DSt} {n : ℕ} (b : Bool) (h : DSt.Bounded n d) :
    DSt.Bounded (n + 1) (dstep b d) := by
  obtain ⟨h1, h2, h3⟩ := h
  have h2' : ∀ l ∈ d.cur, l.2 < n + 1 := fun l hl => Nat.lt_succ_of_lt (h2 l hl)
  have h3' : ∀ C ∈ d.done, ∀ l ∈ C, l.2 < n + 1 := fun C hC l hl =>
    Nat.lt_succ_of_lt (h3 C hC l hl)
  have ht : d.ticks < n + 1 := Nat.lt_succ_of_le h1
  have hcurF : ∀ l ∈ (false, d.ticks) :: d.cur, l.2 < n + 1 := by
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact ht
    · exact h2' l hl
  have hcurT : ∀ l ∈ (true, d.ticks) :: d.cur, l.2 < n + 1 := by
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact ht
    · exact h2' l hl
  have hdone : ∀ C ∈ d.cur :: d.done, ∀ l ∈ C, l.2 < n + 1 := by
    intro C hC
    rcases List.mem_cons.1 hC with rfl | hC
    · exact h2'
    · exact h3' C hC
  cases hp : d.phase <;> cases b <;> simp only [DSt.Bounded, dstep, hp]
  · exact ⟨Nat.le_succ_of_le h1, h2', h3'⟩
  · exact ⟨Nat.succ_le_succ h1, h2', h3'⟩
  · exact ⟨Nat.le_succ_of_le h1, h2', h3'⟩
  · exact ⟨Nat.zero_le _, hcurF, h3'⟩
  · exact ⟨Nat.zero_le _, by simp, hdone⟩
  · exact ⟨Nat.zero_le _, hcurT, h3'⟩

theorem drun_bounded (u : Word) : DSt.Bounded u.length (drun u) := by
  induction u with
  | nil => exact ⟨le_refl 0, by simp [drun, dinit], by simp [drun, dinit]⟩
  | cons b u ih =>
      have hd : drun (b :: u) = dstep b (drun u) := rfl
      rw [hd]
      simpa using dstep_bounded b ih

theorem decode_bounded (u : Word) (C : Clause) (hC : C ∈ decode u) (l : Lit) (hl : l ∈ C) :
    l.2 < u.length := (drun_bounded u).2.2 C hC l hl

theorem litVal_take {σ : Word} {n : ℕ} {l : Lit} (h : l.2 < n) :
    litVal (σ.take n) l = litVal σ l := by
  simp only [litVal, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]

theorem clauseVal_take {σ : Word} {n : ℕ} {C : Clause} (h : ∀ l ∈ C, l.2 < n) :
    clauseVal (σ.take n) C = clauseVal σ C := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      rw [clauseVal_cons, clauseVal_cons, litVal_take (h l (by simp)),
        ih (fun l hl => h l (by simp [hl]))]

theorem cnfVal_take {σ : Word} {n : ℕ} {F : Cnf} (h : ∀ C ∈ F, ∀ l ∈ C, l.2 < n) :
    cnfVal (σ.take n) F = cnfVal σ F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      rw [cnfVal_cons, cnfVal_cons, clauseVal_take (h C (by simp)),
        ih (fun C hC => h C (by simp [hC]))]

/-- **SAT is in NP.** -/
theorem inNP_SAT : InNP SAT := by
  refine ⟨satVerifier, fun n => n, ⟨1, 1, by intro n; simp⟩, monotone_id, ?_, ?_⟩
  · intro x w hacc
    exact ((eval_satVerifier x w).1 hacc).1
  · intro u
    constructor
    · rintro ⟨σ, hσ⟩
      refine ⟨σ.take u.length, (eval_satVerifier u (σ.take u.length)).2 ⟨by simp, ?_⟩⟩
      rw [mrun_eq]
      change cnfVal (σ.take u.length) (decode u) = true
      rw [cnfVal_take (fun C hC l hl => decode_bounded u C hC l hl)]
      exact hσ
    · rintro ⟨w, hw⟩
      obtain ⟨-, hacc⟩ := (eval_satVerifier u w).1 hw
      rw [mrun_eq] at hacc
      exact ⟨w, hacc⟩

/-- A word encoding a CNF lies in `SAT` exactly when that CNF is satisfiable. -/
theorem SAT_encCnf (F : Cnf) : SAT (encCnf F) ↔ ∃ σ : Word, cnfVal σ F = true := by
  simp [SAT]

/-- `SAT` is not vacuous: the code of the empty CNF is in it. -/
theorem SAT_encCnf_nil : SAT (encCnf []) := by
  rw [SAT_encCnf]; exact ⟨[], rfl⟩

/-- The code of the CNF consisting of the empty clause is not in `SAT`. -/
theorem not_SAT_encCnf_empty_clause : ¬ SAT (encCnf [[]]) := by
  rw [SAT_encCnf]
  rintro ⟨σ, hσ⟩
  simp at hσ

end Sat

end Complexity
