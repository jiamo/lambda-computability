/-
**One transition of the Krivine machine, as a Cobham term.**

`Start/KrivineHeapCost.lean` bounds the cost of a transition of the implementation in *passes*
over the encoded state, and left open the last half of the invariance statement: exhibiting a term
of one of the machine models of the library that performs such a transition.  This module closes
that gap for the model `Complexity.Cob` — Cobham's class of polynomial-time functions on words,
the model in which the uniformity of the Cook–Levin reduction is stated in this library.

The term is `Krivine.Impl.stepT`.  It reads the encoded state (`Krivine.Impl.encState`) and the
encoded code table (`Krivine.Impl.encTab`) and writes the encoding of the successor state, the
empty word standing for a stuck state.  Its three branches follow the three cases of
`Krivine.Impl.hstep`: an application pushes the closure of its argument, an abstraction pops the
stack and allocates a cons cell, and a variable walks down the environment — the walk being an
iteration whose length is the variable index, each step dereferencing one address in the heap.

Main definitions:

* `Krivine.Impl.walkT` — the walk down an environment, as a Cobham term;
* `Krivine.Impl.stepT` — **one transition, as a Cobham term**.

Main results:

* `Krivine.Impl.eval_walkT` — the walk computes `Krivine.Impl.envDrop`;
* `Krivine.Impl.eval_stepT` — **the term computes the transition**: on the encoding of a valid
  state it evaluates to the encoding of the successor, and to the empty word when the machine is
  stuck;
* `Krivine.Impl.stepT_compiles` — the term compiles into a family of Boolean circuits of size
  polynomial in the length of its input, so a transition costs polynomial time in this model.
-/

import Start.CobhamBRec
import Start.KrivineCobWord

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

open Complexity

/-! ### Concatenating the values of two terms -/

/-- The concatenation of the values of two terms. -/
def catT (a b : Cob) : Cob := .comp Cob.concat [a, b]

@[simp] theorem eval_catT (a b : Cob) (args : List Word) :
    (catT a b).eval args = a.eval args ++ b.eval args := by
  simp [catT]

/-! ### The fields of an encoded state

The two arguments of all the terms below are the encoded state and the encoded code table. -/

/-- The encoded state without its code and environment fields: the stack length, the stack and
the heap. -/
def restT : Cob := dropPtrT (dropUT (.proj 0))

/-- The environment pointer of the encoded state. -/
def envT : Cob := takePtrT (dropUT (.proj 0))

/-- The stack and the heap of the encoded state. -/
def swhT : Cob := dropUT restT

/-- The heap of the encoded state. -/
def heapT : Cob := .comp dropUsT [leadUT restT, swhT]

/-- The number of cells of the heap, in unary. -/
def hcountT : Cob := .comp countCellsT [heapT, .empty]

/-- The code table from the node the state points at on. -/
def nodeT : Cob := .comp dropNodesT [leadUT (.proj 0), .proj 1]

/-! ### The walk down an environment

The walk iterates on a word `encPtr e ++ encHeap hp`: the pointer moves to the tail of the cons
cell it points at, and the heap is carried along unchanged. -/

/-- The heap carried by the value of the first argument. -/
def curHeapT : Cob := dropPtrT (.proj 0)

/-- The cell the current pointer points at, and the heap after it. -/
def cellAtCurT : Cob := .comp dropCellsT [leadUT (Cob.tailN 1 (.proj 0)), curHeapT]

/-- One step of the walk: the pointer moves to the tail of the cons cell it points at.  The empty
environment is a fixed point. -/
def walkStepT : Cob :=
  Cob.iteT (Cob.nthBit 0 (.proj 0))
    (catT (takePtrT (dropUT (Cob.tailN 1 cellAtCurT))) curHeapT)
    (Cob.pre [false] curHeapT)

/-- **The walk down an environment**, iterated as many times as the first argument has bits. -/
def walkT : Cob := iterT walkStepT

/-- Walking `n` cons cells down the environment at `e`, returning the pointer reached. -/
def envDrop (hp : Heap) : Option ℕ → ℕ → Option ℕ
  | e, 0 => e
  | none, _ + 1 => none
  | some p, n + 1 =>
      match hp[p]? with
      | some (Cell.cons _ t) => envDrop hp t n
      | _ => none

@[simp] theorem envDrop_none (hp : Heap) : ∀ n, envDrop hp none n = none
  | 0 => rfl
  | _ + 1 => rfl

/-- Looking a variable up is walking down the environment and reading the head of the cell
reached. -/
theorem envNth_eq_envDrop (hp : Heap) : ∀ (n : ℕ) (e : Option ℕ),
    envNth hp e n =
      match envDrop hp e n with
      | none => none
      | some p => match hp[p]? with
          | some (Cell.cons a _) => some a
          | _ => none := by
  intro n
  induction n with
  | zero =>
      intro e
      cases e with
      | none => simp
      | some p => rfl
  | succ n ih =>
      intro e
      cases e with
      | none => simp
      | some p =>
          rcases hc : hp[p]? with _ | c
          · simp only [envNth, envDrop, hc]
          · cases c with
            | clos c e' => simp only [envNth, envDrop, hc]
            | cons a t =>
                have hL : envNth hp (some p) (n + 1) = envNth hp t n := by
                  simp only [envNth, hc]
                have hR : envDrop hp (some p) (n + 1) = envDrop hp t n := by
                  simp only [envDrop, hc]
                rw [hL, hR, ih t]

/-- Walking one more cons cell at the end of a walk. -/
theorem envDrop_succ (hp : Heap) : ∀ (n : ℕ) (e : Option ℕ),
    envDrop hp e (n + 1) = envDrop hp (envDrop hp e n) 1 := by
  intro n
  induction n with
  | zero => intro e; rfl
  | succ n ih =>
      intro e
      cases e with
      | none => simp
      | some p =>
          rcases hc : hp[p]? with _ | c
          · simp only [envDrop, hc, envDrop_none]
          · cases c with
            | clos c e' => simp only [envDrop, hc, envDrop_none]
            | cons a t =>
                have hR : envDrop hp (some p) (n + 1 + 1) = envDrop hp t (n + 1) := by
                  simp only [envDrop, hc]
                have hR' : envDrop hp (some p) (n + 1) = envDrop hp t n := by
                  simp only [envDrop, hc]
                rw [hR, hR', ih t]

/-- The walk stays inside the heap. -/
theorem envDrop_le (hp : Heap) (hwf : HeapWF hp) : ∀ (n p : ℕ),
    ∀ q ∈ envDrop hp (some p) n, q ≤ p := by
  intro n
  induction n with
  | zero => intro p q hq; simp only [envDrop, Option.mem_def, Option.some.injEq] at hq; omega
  | succ n ih =>
      intro p q hq
      rcases hc : hp[p]? with _ | c
      · rw [envDrop, hc] at hq; simp at hq
      · cases c with
        | clos c e => rw [envDrop, hc] at hq; simp at hq
        | cons a t =>
            simp only [envDrop, hc] at hq
            have hplt : p < hp.length := lt_length_of_getElem? hc
            have href : (hp[p]'hplt).refsLt p := hwf p hplt
            have hcell : (hp[p]'hplt) = Cell.cons a t := by
              have hg := List.getElem?_eq_getElem hplt
              rw [hg] at hc
              exact Option.some.inj hc
            rw [hcell] at href
            cases t with
            | none => simp at hq
            | some t' =>
                have hlt : t' < p := href.2 t' rfl
                have := ih t' q hq
                omega

/-- The walk stays on cons cells. -/
theorem envDrop_isEnvPtr (tab : Tab) (hp : Heap) (hty : HeapTyped tab hp) :
    ∀ (n : ℕ) (e : Option ℕ), IsEnvPtr hp e → IsEnvPtr hp (envDrop hp e n) := by
  intro n
  induction n with
  | zero => intro e he; exact he
  | succ n ih =>
      intro e he
      cases e with
      | none => rw [envDrop_none]; intro q hq; simp at hq
      | some p =>
          rcases hc : hp[p]? with _ | c
          · rw [envDrop, hc]; intro q hq; simp at hq
          · cases c with
            | clos c e' => rw [envDrop, hc]; intro q hq; simp at hq
            | cons a t =>
                rw [envDrop, hc]
                refine ih t ?_
                have hplt : p < hp.length := lt_length_of_getElem? hc
                have hcell : (hp[p]'hplt) = Cell.cons a t := by
                  have hg := List.getElem?_eq_getElem hplt
                  rw [hg] at hc
                  exact Option.some.inj hc
                have hct := hty p hplt
                rw [hcell] at hct
                exact hct.2

/-- The pointer reached by a walk is no longer to write down than the pointer it started from. -/
theorem encPtr_length_envDrop (hp : Heap) (hwf : HeapWF hp) (e : Option ℕ) (n : ℕ) :
    (encPtr (envDrop hp e n)).length ≤ (encPtr e).length := by
  cases e with
  | none => rw [envDrop_none]
  | some p =>
      rcases hq : envDrop hp (some p) n with _ | q
      · simp [encPtr]
      · have hle : q ≤ p := envDrop_le hp hwf n p q hq
        simp only [encPtr, List.length_cons, unary_length]
        omega

/-! ### The walk, step by step -/

theorem eval_walkStepT (hp : Heap) (e : Option ℕ) (he : IsEnvPtr hp e) (w : Word) :
    walkStepT.eval [encPtr e ++ encHeap hp, w] =
      encPtr (envDrop hp e 1) ++ encHeap hp := by
  cases e with
  | none =>
      have hc : (Cob.nthBit 0 (Cob.proj 0)).eval [encPtr none ++ encHeap hp, w] = bw false := by
        rw [Cob.eval_nthBit]; simp [encPtr]
      have hcur : curHeapT.eval [encPtr none ++ encHeap hp, w] = encHeap hp :=
        eval_dropPtrT (e := none) (by simp)
      rw [walkStepT, Cob.eval_iteW hc rfl rfl]
      simp only [Cob.eval_pre, hcur, envDrop_none]
      simp [encPtr]
  | some p =>
      obtain ⟨a, t, hcell⟩ := he p rfl
      have hplt : p < hp.length := lt_length_of_getElem? hcell
      have hv : (Cob.proj 0).eval [encPtr (some p) ++ encHeap hp, w] =
          encPtr (some p) ++ encHeap hp := by simp
      have hc : (Cob.nthBit 0 (Cob.proj 0)).eval [encPtr (some p) ++ encHeap hp, w] = bw true := by
        rw [Cob.eval_nthBit]; simp [encPtr]
      have hcur : curHeapT.eval [encPtr (some p) ++ encHeap hp, w] = encHeap hp :=
        eval_dropPtrT (e := some p) hv
      have hlead : (leadUT (Cob.tailN 1 (Cob.proj 0))).eval
          [encPtr (some p) ++ encHeap hp, w] = List.replicate p true := by
        refine eval_leadUT (w := encHeap hp) ?_
        rw [Cob.eval_tailN, hv]
        simp [encPtr]
      have hdropk : encHeap (hp.drop p) = encCell (Cell.cons a t) ++ encHeap (hp.drop (p + 1)) := by
        have hd : hp.drop p = (hp[p]'hplt) :: hp.drop (p + 1) := List.drop_eq_getElem_cons hplt
        have hg : (hp[p]'hplt) = Cell.cons a t := by
          have hgg := List.getElem?_eq_getElem hplt
          rw [hgg] at hcell
          exact Option.some.inj hcell
        rw [hd, hg, encHeap_cons]
      have hcellAt : cellAtCurT.eval [encPtr (some p) ++ encHeap hp, w] =
          encCell (Cell.cons a t) ++ encHeap (hp.drop (p + 1)) := by
        rw [cellAtCurT]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil]
        rw [hlead, hcur, eval_dropCellsT hp p (le_of_lt hplt), hdropk]
      have htl : (takePtrT (dropUT (Cob.tailN 1 cellAtCurT))).eval
          [encPtr (some p) ++ encHeap hp, w] = encPtr t := by
        refine eval_takePtrT (w := encHeap (hp.drop (p + 1))) (eval_dropUT (n := a) ?_)
        rw [Cob.eval_tailN, hcellAt]
        simp [encCell, List.append_assoc]
      have hdrop1 : envDrop hp (some p) 1 = t := by simp only [envDrop, hcell]
      rw [walkStepT, Cob.eval_iteW hc rfl rfl]
      simp only [if_true, eval_catT, htl, hcur, hdrop1]

/-- **The walk of the term is the walk on pointers.** -/
theorem eval_walkT (tab : Tab) (hp : Heap) (hwf : HeapWF hp) (hty : HeapTyped tab hp)
    (e : Option ℕ) (he : IsEnvPtr hp e) : ∀ n : ℕ,
    walkT.eval [List.replicate n true, encPtr e ++ encHeap hp] =
      encPtr (envDrop hp e n) ++ encHeap hp := by
  intro n
  induction n with
  | zero =>
      have h0 : envDrop hp e 0 = e := rfl
      rw [h0, walkT, List.replicate_zero]
      exact eval_iterT_zero walkStepT (encPtr e ++ encHeap hp)
  | succ n ih =>
      rw [walkT, eval_iterT_succ]
      rw [show (iterT walkStepT).eval [List.replicate n true, encPtr e ++ encHeap hp] =
        encPtr (envDrop hp e n) ++ encHeap hp from ih]
      rw [eval_walkStepT hp (envDrop hp e n) (envDrop_isEnvPtr tab hp hty n e he), ← envDrop_succ]
      refine List.take_of_length_le ?_
      simp only [List.length_append]
      have := encPtr_length_envDrop hp hwf e (n + 1)
      omega

/-! ### The three branches -/

/-- The successor of a state whose code is an application. -/
def appOutT : Cob :=
  catT (takeUT (Cob.tailN 2 nodeT))
    (catT envT
      (Cob.pre [true]
        (catT (takeUT restT)
          (catT (catT hcountT (Cob.pre [false] .empty))
            (catT swhT
              (Cob.pre [false] (catT (takeUT (dropUT (Cob.tailN 2 nodeT))) envT)))))))

/-- The successor of a state whose code is an abstraction and whose stack is not empty. -/
def betaOutT : Cob :=
  catT (takeUT (Cob.tailN 2 nodeT))
    (catT (Cob.pre [true] (catT hcountT (Cob.pre [false] .empty)))
      (catT (takeUT (Cob.tailN 1 restT))
        (catT (dropUT swhT)
          (Cob.pre [true] (catT (takeUT swhT) envT)))))

/-- The pointer reached by the walk, followed by the heap. -/
def walkResT : Cob := .comp walkT [leadUT (Cob.tailN 1 nodeT), catT envT heapT]

/-- The cell the walk ends on, and the heap after it. -/
def cellPT : Cob := .comp dropCellsT [leadUT (Cob.tailN 1 walkResT), heapT]

/-- The closure cell the variable denotes, and the heap after it. -/
def cellQT : Cob := .comp dropCellsT [leadUT (Cob.tailN 1 cellPT), heapT]

/-- The successor of a state whose code is a variable bound in the environment. -/
def varOutT : Cob :=
  catT (takeUT (Cob.tailN 1 cellQT))
    (catT (takePtrT (dropUT (Cob.tailN 1 cellQT))) restT)

/-- **One transition of the Krivine machine, as a Cobham term.**  The first argument is the
encoded state, the second the encoded code table; the empty word means that the machine is
stuck. -/
def stepT : Cob :=
  Cob.iteT (Cob.nthBit 0 nodeT)
    (Cob.iteT (Cob.nthBit 1 nodeT)
      (Cob.iteT (Cob.nthBit 0 restT) betaOutT .empty)
      appOutT)
    (Cob.iteT (Cob.nthBit 0 walkResT) varOutT .empty)

/-! ### Splitting an encoded heap at an address -/

theorem encHeap_drop_cons {hp : Heap} {p : ℕ} {c : Cell} (hc : hp[p]? = some c) :
    encHeap (hp.drop p) = encCell c ++ encHeap (hp.drop (p + 1)) := by
  have hplt : p < hp.length := lt_length_of_getElem? hc
  have hg : (hp[p]'hplt) = c := by
    have hgg := List.getElem?_eq_getElem hplt
    rw [hgg] at hc
    exact Option.some.inj hc
  rw [List.drop_eq_getElem_cons hplt, hg, encHeap_cons]

theorem encHeap_append_cell (hp : Heap) (c : Cell) :
    encHeap (hp ++ [c]) = encHeap hp ++ encCell c := by
  simp [encHeap]

/-- **The term computes the transition**: on the encoding of a valid state it evaluates to the
encoding of the successor state, and to the empty word when the machine is stuck. -/
theorem eval_stepT {tab : Tab} {s : HState} (h : Valid tab s) :
    stepT.eval [encState s, encTab tab] =
      match hstep tab s with
      | some (_, s') => encState s'
      | none => [] := by
  set args : List Word := [encState s, encTab tab] with hargs
  have hS : (Cob.proj 0).eval args = unary s.code ++ (encPtr s.env ++
      (unary s.stack.length ++ ((s.stack.map unary).flatten ++ encHeap s.heap))) := by
    rw [hargs]
    simp [encState, List.append_assoc]
  have hT : (Cob.proj 1).eval args = encTab tab := by rw [hargs]; simp
  have h1 : (dropUT (Cob.proj 0)).eval args =
      encPtr s.env ++ (unary s.stack.length ++ ((s.stack.map unary).flatten ++ encHeap s.heap)) :=
    eval_dropUT hS
  have hrest : restT.eval args =
      unary s.stack.length ++ ((s.stack.map unary).flatten ++ encHeap s.heap) :=
    eval_dropPtrT h1
  have henv : envT.eval args = encPtr s.env := eval_takePtrT h1
  have hswh : swhT.eval args = (s.stack.map unary).flatten ++ encHeap s.heap := eval_dropUT hrest
  have hlenO : (leadUT restT).eval args = List.replicate s.stack.length true := eval_leadUT hrest
  have hLu : (takeUT restT).eval args = unary s.stack.length := eval_takeUT hrest
  have hheap : heapT.eval args = encHeap s.heap := by
    rw [heapT]
    simp only [Cob.eval_comp, List.map_cons, List.map_nil]
    rw [hlenO, hswh]
    simpa using eval_dropUsT s.stack (encHeap s.heap) s.stack.length le_rfl
  have hcount : hcountT.eval args = List.replicate s.heap.length true := by
    rw [hcountT]
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_empty]
    rw [hheap]
    exact eval_countCellsT s.heap
  have hcodeO : (leadUT (Cob.proj 0)).eval args = List.replicate s.code true := eval_leadUT hS
  obtain ⟨nd, hnd⟩ : ∃ nd, tab[s.code]? = some nd := ⟨_, List.getElem?_eq_getElem h.code_lt⟩
  have hnode : nodeT.eval args = encNode nd ++ encTab (tab.drop (s.code + 1)) := by
    rw [nodeT]
    simp only [Cob.eval_comp, List.map_cons, List.map_nil]
    rw [hcodeO, hT, eval_dropNodesT tab s.code (le_of_lt h.code_lt)]
    have hg : (tab[s.code]'h.code_lt) = nd := by
      have hgg := List.getElem?_eq_getElem h.code_lt
      rw [hgg] at hnd
      exact Option.some.inj hnd
    rw [List.drop_eq_getElem_cons h.code_lt, hg, encTab_cons]
  cases nd with
  | app f a =>
      have hb0 : (Cob.nthBit 0 nodeT).eval args = bw true := by
        rw [Cob.eval_nthBit, hnode]; simp [encNode]
      have hb1 : (Cob.nthBit 1 nodeT).eval args = bw false := by
        rw [Cob.eval_nthBit, hnode]; simp [encNode]
      have hn2 : (Cob.tailN 2 nodeT).eval args =
          unary f ++ (unary a ++ encTab (tab.drop (s.code + 1))) := by
        rw [Cob.eval_tailN, hnode]; simp [encNode, List.append_assoc]
      have hf : (takeUT (Cob.tailN 2 nodeT)).eval args = unary f := eval_takeUT hn2
      have ha : (takeUT (dropUT (Cob.tailN 2 nodeT))).eval args = unary a :=
        eval_takeUT (eval_dropUT hn2)
      rw [hstep_app_eq hnd]
      rw [stepT, Cob.eval_iteW hb0 rfl rfl]
      simp only [if_true]
      rw [Cob.eval_iteW hb1 rfl rfl]
      rw [appOutT]
      simp only [eval_catT, Cob.eval_pre, Cob.eval_empty, hf, ha, henv, hLu, hcount, hswh]
      simp [encState, encHeap_append_cell, encCell, unary, List.replicate_succ,
        List.append_assoc]
  | lam b =>
      have hb0 : (Cob.nthBit 0 nodeT).eval args = bw true := by
        rw [Cob.eval_nthBit, hnode]; simp [encNode]
      have hb1 : (Cob.nthBit 1 nodeT).eval args = bw true := by
        rw [Cob.eval_nthBit, hnode]; simp [encNode]
      have hn2 : (Cob.tailN 2 nodeT).eval args = unary b ++ encTab (tab.drop (s.code + 1)) := by
        rw [Cob.eval_tailN, hnode]; simp [encNode]
      have hbb : (takeUT (Cob.tailN 2 nodeT)).eval args = unary b := eval_takeUT hn2
      cases hst : s.stack with
      | nil =>
          have hcst : (Cob.nthBit 0 restT).eval args = bw false := by
            rw [Cob.eval_nthBit, hrest, hst]; simp [unary]
          rw [hstep_lam_nil_eq hnd hst]
          rw [stepT, Cob.eval_iteW hb0 rfl rfl]
          simp only [if_true]
          rw [Cob.eval_iteW hb1 rfl rfl]
          simp only [if_true]
          rw [Cob.eval_iteW hcst rfl rfl]
          simp
      | cons p pi =>
          have hrest' : restT.eval args = unary (pi.length + 1) ++
              (unary p ++ ((pi.map unary).flatten ++ encHeap s.heap)) := by
            rw [hrest, hst]; simp [List.append_assoc]
          have hswh' : swhT.eval args = unary p ++ ((pi.map unary).flatten ++ encHeap s.heap) := by
            rw [hswh, hst]; simp [List.append_assoc]
          have hcst : (Cob.nthBit 0 restT).eval args = bw true := by
            rw [Cob.eval_nthBit, hrest']; simp [unary_succ]
          have hr1 : (Cob.tailN 1 restT).eval args =
              unary pi.length ++ (unary p ++ ((pi.map unary).flatten ++ encHeap s.heap)) := by
            rw [Cob.eval_tailN, hrest', unary_succ]; simp
          have hLu' : (takeUT (Cob.tailN 1 restT)).eval args = unary pi.length := eval_takeUT hr1
          have hp1 : (takeUT swhT).eval args = unary p := eval_takeUT hswh'
          have hd1 : (dropUT swhT).eval args = (pi.map unary).flatten ++ encHeap s.heap :=
            eval_dropUT hswh'
          rw [hstep_lam_cons_eq hnd hst]
          rw [stepT, Cob.eval_iteW hb0 rfl rfl]
          simp only [if_true]
          rw [Cob.eval_iteW hb1 rfl rfl]
          simp only [if_true]
          rw [Cob.eval_iteW hcst rfl rfl]
          simp only [if_true]
          rw [betaOutT]
          simp only [eval_catT, Cob.eval_pre, Cob.eval_empty, hbb, hcount, hLu', hd1, hp1, henv]
          simp [encState, encHeap_append_cell, encCell, encPtr, unary, List.append_assoc]
  | var n =>
      have hb0 : (Cob.nthBit 0 nodeT).eval args = bw false := by
        rw [Cob.eval_nthBit, hnode]; simp [encNode]
      have hn1 : (Cob.tailN 1 nodeT).eval args = unary n ++ encTab (tab.drop (s.code + 1)) := by
        rw [Cob.eval_tailN, hnode]; simp [encNode]
      have hnO : (leadUT (Cob.tailN 1 nodeT)).eval args = List.replicate n true := eval_leadUT hn1
      have hcatEH : (catT envT heapT).eval args = encPtr s.env ++ encHeap s.heap := by
        rw [eval_catT, henv, hheap]
      have hwalk : walkResT.eval args = encPtr (envDrop s.heap s.env n) ++ encHeap s.heap := by
        rw [walkResT]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil]
        rw [hnO, hcatEH]
        exact eval_walkT tab s.heap h.heapWF h.heapTyped s.env h.env_ty n
      rcases hed : envDrop s.heap s.env n with _ | p
      · have hnth : envNth s.heap s.env n = none := by rw [envNth_eq_envDrop, hed]
        have hcw : (Cob.nthBit 0 walkResT).eval args = bw false := by
          rw [Cob.eval_nthBit, hwalk, hed]; simp [encPtr]
        rw [hstep_var_none_eq hnd hnth]
        rw [stepT, Cob.eval_iteW hb0 rfl rfl]
        rw [Cob.eval_iteW hcw rfl rfl]
        simp
      · have hEnv : IsEnvPtr s.heap (envDrop s.heap s.env n) :=
          envDrop_isEnvPtr tab s.heap h.heapTyped n s.env h.env_ty
        rw [hed] at hEnv
        obtain ⟨a, t, hcell⟩ := hEnv p rfl
        have hplt : p < s.heap.length := lt_length_of_getElem? hcell
        have hnth : envNth s.heap s.env n = some a := by
          rw [envNth_eq_envDrop, hed]; simp only [hcell]
        have hclos : IsClosPtr s.heap a := by
          have hg : (s.heap[p]'hplt) = Cell.cons a t := by
            have hgg := List.getElem?_eq_getElem hplt
            rw [hgg] at hcell
            exact Option.some.inj hcell
          have hct := h.heapTyped p hplt
          rw [hg] at hct
          exact hct.1
        obtain ⟨c, e', hcellQ⟩ := hclos
        have halt : a < s.heap.length := lt_length_of_getElem? hcellQ
        have hcw : (Cob.nthBit 0 walkResT).eval args = bw true := by
          rw [Cob.eval_nthBit, hwalk, hed]; simp [encPtr]
        have hpO : (leadUT (Cob.tailN 1 walkResT)).eval args = List.replicate p true := by
          refine eval_leadUT (w := encHeap s.heap) ?_
          rw [Cob.eval_tailN, hwalk, hed]; simp [encPtr]
        have hcellP : cellPT.eval args =
            encCell (Cell.cons a t) ++ encHeap (s.heap.drop (p + 1)) := by
          rw [cellPT]
          simp only [Cob.eval_comp, List.map_cons, List.map_nil]
          rw [hpO, hheap, eval_dropCellsT s.heap p (le_of_lt hplt), encHeap_drop_cons hcell]
        have haO : (leadUT (Cob.tailN 1 cellPT)).eval args = List.replicate a true := by
          refine eval_leadUT (w := encPtr t ++ encHeap (s.heap.drop (p + 1))) ?_
          rw [Cob.eval_tailN, hcellP]
          simp [encCell, List.append_assoc]
        have hcellQE : cellQT.eval args =
            encCell (Cell.clos c e') ++ encHeap (s.heap.drop (a + 1)) := by
          rw [cellQT]
          simp only [Cob.eval_comp, List.map_cons, List.map_nil]
          rw [haO, hheap, eval_dropCellsT s.heap a (le_of_lt halt), encHeap_drop_cons hcellQ]
        have hq1 : (Cob.tailN 1 cellQT).eval args =
            unary c ++ (encPtr e' ++ encHeap (s.heap.drop (a + 1))) := by
          rw [Cob.eval_tailN, hcellQE]
          simp [encCell, List.append_assoc]
        have hc1 : (takeUT (Cob.tailN 1 cellQT)).eval args = unary c := eval_takeUT hq1
        have he1 : (takePtrT (dropUT (Cob.tailN 1 cellQT))).eval args = encPtr e' :=
          eval_takePtrT (eval_dropUT hq1)
        rw [hstep_var_eq hnd hnth hcellQ]
        rw [stepT, Cob.eval_iteW hb0 rfl rfl]
        rw [Cob.eval_iteW hcw rfl rfl]
        simp only [if_true]
        rw [varOutT]
        simp only [eval_catT, hc1, he1, hrest]
        simp [encState, List.append_assoc]

/-! ### The cost of the term, and the whole run -/

/-- **A transition costs polynomial time in this model**: the term compiles into a family of
Boolean circuits whose size is bounded by a monotone polynomial in the width of its arguments.
This is `Complexity.Tseitin.cobCompiles` applied to `Krivine.Impl.stepT`; the cost measure of the
model is the size of the compiled circuit. -/
theorem stepT_compiles : Tseitin.CobCompiles stepT := Tseitin.cobCompiles stepT

/-- The invariant is preserved along a run. -/
theorem valid_hrun {tab : Tab} : ∀ (n : ℕ) {s u : HState}, Valid tab s →
    hrun tab n s = some u → Valid tab u := by
  intro n
  induction n with
  | zero =>
      intro s u hv hr
      rw [hrun] at hr
      cases hr
      exact hv
  | succ n ih =>
      intro s u hv hr
      rw [hrun] at hr
      rcases hs : hstep tab s with _ | ⟨l, s'⟩
      · rw [hs] at hr; exact absurd hr (by simp)
      · rw [hs] at hr
        exact ih (hv.hstep hs) hr

/-- **Every state of a run is transformed by the term into its successor.** -/
theorem eval_stepT_hrun {tab : Tab} {s u : HState} (hv : Valid tab s) {n : ℕ}
    (hr : hrun tab n s = some u) :
    stepT.eval [encState u, encTab tab] =
      match hstep tab u with
      | some (_, u') => encState u'
      | none => [] :=
  eval_stepT (valid_hrun n hv hr)

/-- **The missing half of invariance, on a machine model of the library.**  A term the weak head
strategy normalises in `k` steps is evaluated by the implementation in `n` transitions, `n`
polynomial in the size of the term and in the number of β-steps, and *every one of those
transitions is performed by the single Cobham term* `Krivine.Impl.stepT`, whose cost — the size of
the circuits it compiles into — is polynomial in the length of its input. -/
theorem eval_impl_cob_cost {t : Lambda} {k : ℕ} (h : Lambda.WHNIn k t) :
    ∃ (n b : ℕ) (s : HState),
      hrun (tabOf t) n (initState t) = some s ∧
      hstep (tabOf t) s = none ∧
      b ≤ k ∧ n ≤ b + Lambda.size t * (1 + b * (b + 1)) ∧
      Lambda.reducesIn b t (decState (tabOf t) s).decode ∧
      Lambda.IsWhnf (decState (tabOf t) s).decode ∧
      hrunCost (tabOf t) n (initState t) ≤ n * ((n + 2) * (encBound t.nodes n + 1)) ∧
      ∀ m : ℕ, ∀ u : HState, hrun (tabOf t) m (initState t) = some u →
        stepT.eval [encState u, encTab (tabOf t)] =
          match hstep (tabOf t) u with
          | some (_, u') => encState u'
          | none => [] := by
  obtain ⟨n, b, s, hrun0, hfin, hbk, hnle, hred, hwhnf, hcost⟩ := eval_impl_cost h
  exact ⟨n, b, s, hrun0, hfin, hbk, hnle, hred, hwhnf, hcost,
    fun m u hu => eval_stepT_hrun (valid_initState t) hu⟩

end Impl

end Krivine
