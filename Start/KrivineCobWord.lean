/-
**Reading and writing the encoded states of the Krivine machine with Cobham terms.**

`Start/KrivineHeapCost.lean` writes an implementation state as a word (`Krivine.Impl.encState`)
and counts the cost of a transition in *passes* over that word.  What was missing there is a term
of one of the machine models of the library performing such a pass.  This module supplies the
tools: every field of the encoding — a unary number, a pointer, a cell of the heap, a node of the
code table — is read, skipped or rebuilt by a **Cobham term**, and so is the walk down the heap
that dereferences an address.

Main definitions:

* `Krivine.Impl.encNode`, `Krivine.Impl.encTab` — the code table as a word;
* `Krivine.Impl.leadUT`, `Krivine.Impl.takeUT`, `Krivine.Impl.dropUT` — reading and skipping a
  unary field;
* `Krivine.Impl.takePtrT`, `Krivine.Impl.dropPtrT`, `Krivine.Impl.dropCellT`,
  `Krivine.Impl.dropNodeT` — the same for a pointer, a cell and a node;
* `Krivine.Impl.iterT` — iterating a term a number of times given in unary, and the instances
  `Krivine.Impl.dropCellsT`, `Krivine.Impl.dropNodesT`, `Krivine.Impl.dropUsT`;
* `Krivine.Impl.countCellsT` — counting the cells of a heap, a finite-state transduction.

Main results: the `eval` lemma of each of those terms, in particular

* `Krivine.Impl.eval_dropCellsT` — **dereferencing an address is a Cobham function**: dropping the
  first `k` cells of an encoded heap;
* `Krivine.Impl.eval_countCellsT` — **the number of cells of an encoded heap is a Cobham
  function**.
-/

import Start.CobhamBlock
import Start.KrivineHeapCost

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

open Complexity

/-! ### The code table as a word -/

/-- A node of the code table as a word: a variable is a tag bit and its index, an application two
tag bits and the addresses of its two children, an abstraction two tag bits and the address of its
body.  Like `Krivine.Impl.encCell`, the encoding is self-delimiting. -/
def encNode : Node → Word
  | Node.var n => false :: unary n
  | Node.app f a => true :: false :: (unary f ++ unary a)
  | Node.lam b => true :: true :: unary b

/-- The code table, node after node. -/
def encTab (tab : Tab) : Word := (tab.map encNode).flatten

@[simp] theorem encTab_nil : encTab [] = [] := rfl

theorem encTab_cons (nd : Node) (tab : Tab) :
    encTab (nd :: tab) = encNode nd ++ encTab tab := by
  simp [encTab]

theorem encHeap_cons (c : Cell) (hp : Heap) :
    encHeap (c :: hp) = encCell c ++ encHeap hp := by
  simp [encHeap]

/-! ### Unary fields are self-delimiting -/

theorem lead1_unary_append (n : ℕ) (w : Word) : lead1 (unary n ++ w) = n := by
  induction n with
  | zero => simp [unary, lead1]
  | succ n ih => rw [unary_succ]; simpa [lead1] using ih

theorem drop1_unary_append (n : ℕ) (w : Word) : drop1 (unary n ++ w) = false :: w := by
  induction n with
  | zero => simp [unary, drop1]
  | succ n ih => rw [unary_succ]; simpa [drop1] using ih

/-! ### Reading a unary field -/

/-- The unary field at the front of the value of `t`, as a word of ones. -/
def leadUT (t : Cob) : Cob := .comp Cob.leadOnes [t]

theorem eval_leadUT {t : Cob} {args : List Word} {n : ℕ} {w : Word}
    (h : t.eval args = unary n ++ w) :
    (leadUT t).eval args = List.replicate n true := by
  simp [leadUT, h, lead1_unary_append]

/-- The unary field at the front of the value of `t`, terminator included. -/
def takeUT (t : Cob) : Cob := .comp Cob.concat [leadUT t, Cob.pre [false] .empty]

theorem eval_takeUT {t : Cob} {args : List Word} {n : ℕ} {w : Word}
    (h : t.eval args = unary n ++ w) : (takeUT t).eval args = unary n := by
  simp [takeUT, eval_leadUT h, unary]

/-- The value of `t` with its first unary field removed. -/
def dropUT (t : Cob) : Cob := .comp Cob.tailC [.comp Cob.dropOnes [t]]

theorem eval_dropUT {t : Cob} {args : List Word} {n : ℕ} {w : Word}
    (h : t.eval args = unary n ++ w) : (dropUT t).eval args = w := by
  simp [dropUT, h, drop1_unary_append]

/-! ### Reading a pointer -/

/-- The pointer at the front of the value of `t`. -/
def takePtrT (t : Cob) : Cob :=
  Cob.iteT (Cob.nthBit 0 t) (Cob.pre [true] (takeUT (Cob.tailN 1 t))) (Cob.pre [false] .empty)

/-- The value of `t` with its first pointer removed. -/
def dropPtrT (t : Cob) : Cob :=
  Cob.iteT (Cob.nthBit 0 t) (dropUT (Cob.tailN 1 t)) (Cob.tailN 1 t)

theorem eval_takePtrT {t : Cob} {args : List Word} {e : Option ℕ} {w : Word}
    (h : t.eval args = encPtr e ++ w) : (takePtrT t).eval args = encPtr e := by
  cases e with
  | none =>
      have hc : (Cob.nthBit 0 t).eval args = bw false := by
        rw [Cob.eval_nthBit, h]; simp [encPtr]
      rw [takePtrT, Cob.eval_iteW hc rfl rfl]
      simp [encPtr]
  | some p =>
      have hc : (Cob.nthBit 0 t).eval args = bw true := by
        rw [Cob.eval_nthBit, h]; simp [encPtr]
      have ht : (Cob.tailN 1 t).eval args = unary p ++ w := by
        rw [Cob.eval_tailN, h]; simp [encPtr]
      rw [takePtrT, Cob.eval_iteW hc rfl rfl]
      simp [Cob.eval_pre, eval_takeUT ht, encPtr]

theorem eval_dropPtrT {t : Cob} {args : List Word} {e : Option ℕ} {w : Word}
    (h : t.eval args = encPtr e ++ w) : (dropPtrT t).eval args = w := by
  cases e with
  | none =>
      have hc : (Cob.nthBit 0 t).eval args = bw false := by
        rw [Cob.eval_nthBit, h]; simp [encPtr]
      rw [dropPtrT, Cob.eval_iteW hc rfl rfl, Cob.eval_tailN, h]
      simp [encPtr]
  | some p =>
      have hc : (Cob.nthBit 0 t).eval args = bw true := by
        rw [Cob.eval_nthBit, h]; simp [encPtr]
      have ht : (Cob.tailN 1 t).eval args = unary p ++ w := by
        rw [Cob.eval_tailN, h]; simp [encPtr]
      rw [dropPtrT, Cob.eval_iteW hc rfl rfl]
      exact eval_dropUT ht

/-! ### Reading a cell and a node -/

/-- The value of `t` with its first cell removed. -/
def dropCellT (t : Cob) : Cob := dropPtrT (dropUT (Cob.tailN 1 t))

theorem eval_dropCellT {t : Cob} {args : List Word} {c : Cell} {w : Word}
    (h : t.eval args = encCell c ++ w) : (dropCellT t).eval args = w := by
  cases c with
  | clos a e =>
      have h1 : (Cob.tailN 1 t).eval args = unary a ++ (encPtr e ++ w) := by
        rw [Cob.eval_tailN, h]; simp [encCell]
      exact eval_dropPtrT (eval_dropUT h1)
  | cons a e =>
      have h1 : (Cob.tailN 1 t).eval args = unary a ++ (encPtr e ++ w) := by
        rw [Cob.eval_tailN, h]; simp [encCell]
      exact eval_dropPtrT (eval_dropUT h1)

/-- The value of `t` with its first node removed. -/
def dropNodeT (t : Cob) : Cob :=
  Cob.iteT (Cob.nthBit 0 t)
    (Cob.iteT (Cob.nthBit 1 t) (dropUT (Cob.tailN 2 t)) (dropUT (dropUT (Cob.tailN 2 t))))
    (dropUT (Cob.tailN 1 t))

theorem eval_dropNodeT {t : Cob} {args : List Word} {nd : Node} {w : Word}
    (h : t.eval args = encNode nd ++ w) : (dropNodeT t).eval args = w := by
  cases nd with
  | var n =>
      have hc : (Cob.nthBit 0 t).eval args = bw false := by
        rw [Cob.eval_nthBit, h]; simp [encNode]
      have h1 : (Cob.tailN 1 t).eval args = unary n ++ w := by
        rw [Cob.eval_tailN, h]; simp [encNode]
      rw [dropNodeT, Cob.eval_iteW hc rfl rfl]
      exact eval_dropUT h1
  | app f a =>
      have hc : (Cob.nthBit 0 t).eval args = bw true := by
        rw [Cob.eval_nthBit, h]; simp [encNode]
      have hc2 : (Cob.nthBit 1 t).eval args = bw false := by
        rw [Cob.eval_nthBit, h]; simp [encNode]
      have h1 : (Cob.tailN 2 t).eval args = unary f ++ (unary a ++ w) := by
        rw [Cob.eval_tailN, h]; simp [encNode]
      rw [dropNodeT, Cob.eval_iteW hc rfl rfl, Cob.eval_iteW hc2 rfl rfl]
      exact eval_dropUT (eval_dropUT h1)
  | lam b =>
      have hc : (Cob.nthBit 0 t).eval args = bw true := by
        rw [Cob.eval_nthBit, h]; simp [encNode]
      have hc2 : (Cob.nthBit 1 t).eval args = bw true := by
        rw [Cob.eval_nthBit, h]; simp [encNode]
      have h1 : (Cob.tailN 2 t).eval args = unary b ++ w := by
        rw [Cob.eval_tailN, h]; simp [encNode]
      rw [dropNodeT, Cob.eval_iteW hc rfl rfl, Cob.eval_iteW hc2 rfl rfl]
      exact eval_dropUT h1

/-! ### Iterating a term a number of times given in unary -/

/-- `iterT f` applies `f`, a term of two arguments, to the second argument as many times as the
first argument has bits.  The value is truncated to the length of the second argument at every
step, which is harmless whenever the iterates stay no longer than it. -/
def iterT (f : Cob) : Cob :=
  .bRec (.proj 0) (.comp f [.proj 1, .proj 2]) (.comp f [.proj 1, .proj 2]) (.proj 1)

theorem eval_iterT_zero (f : Cob) (v : Word) : (iterT f).eval [[], v] = v := by
  simp [iterT]

theorem eval_iterT_succ (f : Cob) (v : Word) (k : ℕ) :
    (iterT f).eval [List.replicate (k + 1) true, v] =
      (f.eval [(iterT f).eval [List.replicate k true, v], v]).take v.length := by
  rw [List.replicate_succ, iterT, Cob.eval_bRec_cons]
  simp

/-- Dropping cells from an encoded heap. -/
def dropCellsT : Cob := iterT (dropCellT (.proj 0))

/-- Dropping nodes from an encoded code table. -/
def dropNodesT : Cob := iterT (dropNodeT (.proj 0))

/-- Dropping unary fields from a word. -/
def dropUsT : Cob := iterT (dropUT (.proj 0))

theorem flatten_map_drop_le {α : Type} (f : α → Word) (l : List α) (k : ℕ) :
    (((l.drop k).map f).flatten).length ≤ ((l.map f).flatten).length := by
  have h : (l.map f).flatten = ((l.take k).map f).flatten ++ ((l.drop k).map f).flatten := by
    rw [← List.flatten_append, ← List.map_append, List.take_append_drop]
  rw [h, List.length_append]
  omega

theorem encHeap_drop_suffix (hp : Heap) (k : ℕ) :
    (encHeap (hp.drop k)).length ≤ (encHeap hp).length :=
  flatten_map_drop_le encCell hp k

theorem encTab_drop_suffix (tab : Tab) (k : ℕ) :
    (encTab (tab.drop k)).length ≤ (encTab tab).length :=
  flatten_map_drop_le encNode tab k

/-- **Dereferencing an address is a Cobham function**: dropping the first `k` cells of an encoded
heap. -/
theorem eval_dropCellsT (hp : Heap) : ∀ k ≤ hp.length,
    dropCellsT.eval [List.replicate k true, encHeap hp] = encHeap (hp.drop k) := by
  intro k
  induction k with
  | zero => intro _; simpa [dropCellsT] using eval_iterT_zero _ _
  | succ k ih =>
      intro hk
      have hk' : k ≤ hp.length := Nat.le_of_succ_le hk
      have hrec := ih hk'
      rw [dropCellsT, eval_iterT_succ]
      rw [show (iterT (dropCellT (.proj 0))).eval [List.replicate k true, encHeap hp] =
        encHeap (hp.drop k) from hrec]
      have hlt : k < hp.length := hk
      have hsplit : encHeap (hp.drop k) = encCell (hp[k]'hlt) ++ encHeap (hp.drop (k + 1)) := by
        have : hp.drop k = (hp[k]'hlt) :: hp.drop (k + 1) := by
          rw [List.drop_eq_getElem_cons hlt]
        rw [this, encHeap_cons]
      have hev : (dropCellT (Cob.proj 0)).eval [encHeap (hp.drop k), encHeap hp] =
          encHeap (hp.drop (k + 1)) :=
        eval_dropCellT (by simpa using hsplit)
      rw [hev, List.take_of_length_le (encHeap_drop_suffix hp (k + 1))]

/-- Dropping the first `k` nodes of an encoded table is a Cobham function. -/
theorem eval_dropNodesT (tab : Tab) : ∀ k ≤ tab.length,
    dropNodesT.eval [List.replicate k true, encTab tab] = encTab (tab.drop k) := by
  intro k
  induction k with
  | zero => intro _; simpa [dropNodesT] using eval_iterT_zero _ _
  | succ k ih =>
      intro hk
      have hk' : k ≤ tab.length := Nat.le_of_succ_le hk
      have hrec := ih hk'
      rw [dropNodesT, eval_iterT_succ]
      rw [show (iterT (dropNodeT (.proj 0))).eval [List.replicate k true, encTab tab] =
        encTab (tab.drop k) from hrec]
      have hlt : k < tab.length := hk
      have hsplit : encTab (tab.drop k) = encNode (tab[k]'hlt) ++ encTab (tab.drop (k + 1)) := by
        have : tab.drop k = (tab[k]'hlt) :: tab.drop (k + 1) := by
          rw [List.drop_eq_getElem_cons hlt]
        rw [this, encTab_cons]
      have hev : (dropNodeT (Cob.proj 0)).eval [encTab (tab.drop k), encTab tab] =
          encTab (tab.drop (k + 1)) :=
        eval_dropNodeT (by simpa using hsplit)
      rw [hev, List.take_of_length_le (encTab_drop_suffix tab (k + 1))]

/-- Dropping the first `k` unary fields of a word is a Cobham function. -/
theorem eval_dropUsT (st : List ℕ) (w : Word) : ∀ k ≤ st.length,
    dropUsT.eval [List.replicate k true, (st.map unary).flatten ++ w] =
      ((st.drop k).map unary).flatten ++ w := by
  intro k
  induction k with
  | zero => intro _; simpa [dropUsT] using eval_iterT_zero _ _
  | succ k ih =>
      intro hk
      have hk' : k ≤ st.length := Nat.le_of_succ_le hk
      have hrec := ih hk'
      have hlt : k < st.length := hk
      have hsplit : ((st.drop k).map unary).flatten ++ w =
          unary (st[k]'hlt) ++ (((st.drop (k + 1)).map unary).flatten ++ w) := by
        have hd : st.drop k = (st[k]'hlt) :: st.drop (k + 1) := List.drop_eq_getElem_cons hlt
        rw [hd, List.map_cons, List.flatten_cons, List.append_assoc]
      have hlen : (((st.drop (k + 1)).map unary).flatten ++ w).length ≤
          ((st.map unary).flatten ++ w).length := by
        have hsub : ((st.drop (k+1)).map unary).flatten.length ≤
            (st.map unary).flatten.length := flatten_map_drop_le unary st (k + 1)
        simp only [List.length_append]
        omega
      rw [dropUsT, eval_iterT_succ]
      rw [show (iterT (dropUT (.proj 0))).eval
        [List.replicate k true, (st.map unary).flatten ++ w] =
          ((st.drop k).map unary).flatten ++ w from hrec]
      have hev : (dropUT (Cob.proj 0)).eval
          [((st.drop k).map unary).flatten ++ w, (st.map unary).flatten ++ w] =
            ((st.drop (k + 1)).map unary).flatten ++ w :=
        eval_dropUT (by simpa using hsplit)
      rw [hev, List.take_of_length_le hlen]

/-! ### Counting the cells of a heap -/

/-- The control of the transducer counting cells: it reads a tag bit, then the unary address,
then the pointer, and starts again. -/
def cellDelta : ℕ → Bool → ℕ
  | 0, _ => 1
  | 1, b => if b then 1 else 2
  | 2, b => if b then 3 else 0
  | _, b => if b then 3 else 0

theorem cellDelta_lt (s : ℕ) (b : Bool) : cellDelta s b < 4 := by
  match s, b with
  | 0, b => simp [cellDelta]
  | 1, b => cases b <;> simp [cellDelta]
  | 2, b => cases b <;> simp [cellDelta]
  | (_ + 3), b => cases b <;> simp [cellDelta]

/-- The output of the transducer counting cells: one tick per tag bit read. -/
def cellOut : ℕ → Bool → Word := fun s _ => if s = 0 then [true] else []

/-- The output blocks of the counting transducer, as Cobham terms. -/
def cellOutT : ℕ → Bool → Cob := fun s _ => if s = 0 then Cob.pre [true] .empty else .empty

theorem eval_cellOutT (s : ℕ) (b : Bool) : (cellOutT s b).eval [[]] = cellOut s b := by
  by_cases h : s = 0 <;> simp [cellOutT, cellOut, h]

/-- The Cobham term counting the cells of an encoded heap. -/
def countCellsT : Cob := lrunTerm 4 cellDelta cellOutT 1

theorem lst_append (delta : ℕ → Bool → ℕ) (s : ℕ) (x y : Word) :
    lst delta s (x ++ y) = lst delta (lst delta s x) y := by
  induction x generalizing s with
  | nil => simp [lst]
  | cons b x ih => simp [lst, ih]

theorem lrun_append (delta : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) (x y : Word) :
    lrun delta out s (x ++ y) = lrun delta out s x ++ lrun delta out (lst delta s x) y := by
  induction x generalizing s with
  | nil => simp [lrun, lst]
  | cons b x ih => simp [lrun, lst, ih, List.append_assoc]

theorem lst_replicate_true : ∀ (n s : ℕ), s = 1 ∨ s = 3 →
    lst cellDelta s (List.replicate n true) = s := by
  intro n
  induction n with
  | zero => intro s _; simp [lst]
  | succ n ih =>
      intro s hs
      rcases hs with h | h
      · subst h
        rw [List.replicate_succ, lst, show cellDelta 1 true = 1 from rfl]
        exact ih 1 (Or.inl rfl)
      · subst h
        rw [List.replicate_succ, lst, show cellDelta 3 true = 3 from rfl]
        exact ih 3 (Or.inr rfl)

theorem lrun_replicate_true : ∀ (n s : ℕ), s = 1 ∨ s = 3 →
    lrun cellDelta cellOut s (List.replicate n true) = [] := by
  intro n
  induction n with
  | zero => intro s _; simp [lrun]
  | succ n ih =>
      intro s hs
      rcases hs with h | h
      · subst h
        rw [List.replicate_succ, lrun, show cellDelta 1 true = 1 from rfl, ih 1 (Or.inl rfl)]
        simp [cellOut]
      · subst h
        rw [List.replicate_succ, lrun, show cellDelta 3 true = 3 from rfl, ih 3 (Or.inr rfl)]
        simp [cellOut]

theorem lst_unary (s n : ℕ) (hs : s = 1 ∨ s = 3) :
    lst cellDelta s (unary n) = cellDelta s false := by
  rw [unary, lst_append, lst_replicate_true n s hs, lst]
  simp [lst]

theorem lrun_unary (s n : ℕ) (hs : s = 1 ∨ s = 3) :
    lrun cellDelta cellOut s (unary n) = [] := by
  rw [unary, lrun_append, lrun_replicate_true n s hs, lst_replicate_true n s hs, lrun]
  rcases hs with h | h <;> subst h <;> simp [cellOut, lrun]

theorem lst_encPtr (e : Option ℕ) : lst cellDelta 2 (encPtr e) = 0 := by
  cases e with
  | none => simp [encPtr, lst, cellDelta]
  | some p =>
      rw [encPtr, lst, show cellDelta 2 true = 3 from rfl, lst_unary 3 p (Or.inr rfl)]
      simp [cellDelta]

theorem lrun_encPtr (e : Option ℕ) : lrun cellDelta cellOut 2 (encPtr e) = [] := by
  cases e with
  | none => simp [encPtr, lrun, cellOut]
  | some p =>
      rw [encPtr, lrun, show cellDelta 2 true = 3 from rfl, lrun_unary 3 p (Or.inr rfl)]
      simp [cellOut]

theorem lst_encCell (c : Cell) : lst cellDelta 0 (encCell c) = 0 := by
  cases c with
  | clos a e =>
      rw [encCell, lst, show cellDelta 0 false = 1 from rfl, lst_append,
        lst_unary 1 a (Or.inl rfl), show cellDelta 1 false = 2 from rfl, lst_encPtr]
  | cons a e =>
      rw [encCell, lst, show cellDelta 0 true = 1 from rfl, lst_append,
        lst_unary 1 a (Or.inl rfl), show cellDelta 1 false = 2 from rfl, lst_encPtr]

theorem lrun_encCell (c : Cell) : lrun cellDelta cellOut 0 (encCell c) = [true] := by
  cases c with
  | clos a e =>
      rw [encCell, lrun, show cellDelta 0 false = 1 from rfl, lrun_append,
        lrun_unary 1 a (Or.inl rfl), lst_unary 1 a (Or.inl rfl),
        show cellDelta 1 false = 2 from rfl, lrun_encPtr]
      simp [cellOut]
  | cons a e =>
      rw [encCell, lrun, show cellDelta 0 true = 1 from rfl, lrun_append,
        lrun_unary 1 a (Or.inl rfl), lst_unary 1 a (Or.inl rfl),
        show cellDelta 1 false = 2 from rfl, lrun_encPtr]
      simp [cellOut]

theorem lrun_encHeap (hp : Heap) :
    lrun cellDelta cellOut 0 (encHeap hp) = List.replicate hp.length true := by
  induction hp with
  | nil => simp [encHeap, lrun]
  | cons c hp ih =>
      rw [encHeap_cons, lrun_append, lrun_encCell, lst_encCell, ih]
      simp [List.replicate_succ]

/-- **The number of cells of an encoded heap is a Cobham function.** -/
theorem eval_countCellsT (hp : Heap) :
    countCellsT.eval [encHeap hp, []] = List.replicate hp.length true := by
  have hK : ∀ s b, ((cellOutT s b).eval [([] : Word)]).length ≤ 1 + ([] : Word).length := by
    intro s b
    by_cases h : s = 0 <;> simp [cellOutT, h]
  rw [countCellsT, eval_lrunTerm (by norm_num) cellDelta_lt cellOutT [] hK (encHeap hp)]
  simp only [eval_cellOutT]
  exact lrun_encHeap hp

end Impl

end Krivine
