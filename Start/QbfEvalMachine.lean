/-
**A word machine evaluating quantified Boolean formulas from their codes.**

The evaluator of `Start/Qbf.lean` holds subformulas in its states.  To run it on a tape, its
states have to be words, and this module gives such a machine, working directly on the code of
`Start/QbfWord.lean`.  A state (`Complexity.Qbf.EvalW.QS`) has six components:

* `P` — the code still to be read (a suffix of the input);
* `S` — the stack of activation records, a list of naturals read seven at a time
  (`kind, op, v₁, i, ptr, σ_old, D_old`), written on the tape as unary fields;
* `M` — the mode: `[]` while evaluating, `[v]` while returning the value `v`;
* `Sg`, `D` — the assignment and the "bound" flags, one bit per variable;
* `H` — `[]` once the machine has halted.

Evaluation consumes the code: after a subformula has been evaluated, `P` points just behind it,
which is where the next operand starts.  A quantifier record remembers where its body starts
(`ptr`, the number of bits read before it), so that the body can be run a second time with the
variable set to `true`, and the old value and binding of the variable, which are restored on
exit.  A variable that is not bound, a malformed code and a stack that grows beyond
`Complexity.Qbf.EvalW.bound` all stop the machine with a rejection.

The step (`Complexity.Qbf.EvalW.qstep`) is a case distinction on a number
(`Complexity.Qbf.EvalW.caseNum`) so that it can be written as a selection among Cobham terms.

Main results:

* `Complexity.Qbf.EvalW.run_enc` — **on the code of a formula whose free variables are bound the
  machine returns its value** and ends behind its code with the stack and the assignment it
  started with;
* `Complexity.Qbf.EvalW.rej_of_noPrefix` — on a word that does not start with the code of a
  formula the machine rejects;
* `Complexity.Qbf.EvalW.halts` and `Complexity.Qbf.EvalW.accepts_iff` — **from the initial state
  the machine halts on every word, and accepts exactly the words of
  `Complexity.Qbf.tqbfLang`**;
* `Complexity.Qbf.EvalW.inv_steps` — every reachable state satisfies the invariant
  `Complexity.Qbf.EvalW.Inv`, which bounds all six components polynomially in the length of the
  input.
-/

import Mathlib
import Start.QbfCodeSpace
import Start.CobhamFields
import Start.Sat

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace EvalW

open Complexity

/-! ### States and the step -/

/-- A state of the word evaluator. -/
structure QS where
  /-- The code still to be read. -/
  P : List Bool
  /-- The activation records, seven numbers each, innermost first. -/
  S : List ℕ
  /-- `[]` while evaluating, `[v]` while returning `v`. -/
  M : List Bool
  /-- The assignment. -/
  Sg : List Bool
  /-- The bound variables. -/
  D : List Bool
  /-- `[]` once halted. -/
  H : List Bool

/-- The bound on the length of the stack word beyond which no record is pushed. -/
def bound (n : ℕ) : ℕ := (2 * n + 10) * (2 * n + 10)

/-- The stack has reached its bound. -/
def isLong (x : List Bool) (s : QS) : Bool := decide (bound x.length ≤ (fieldsWord s.S).length)

/-- A bit as a number. -/
def bitN (b : Bool) : ℕ := if b then 1 else 0

/-- Combining two values: `and` for `op = 0`, `or` otherwise. -/
def comb (op v₁ : ℕ) (v : Bool) : Bool :=
  if op = 0 then (decide (v₁ ≠ 0) && v) else (decide (v₁ ≠ 0) || v)

/-- The case of the step. `0` rejects; `1`–`4` read a variable, a negation, a binary connective
and a quantifier; `5` halts; `6`–`10` return into a record of kind `0`–`4`. -/
def caseNum (x : List Bool) (s : QS) : ℕ :=
  match s.M with
  | [] =>
    match s.P with
    | false :: false :: r =>
        if drop1 r = [] then 0 else if s.D.getD (lead1 r) false then 1 else 0
    | false :: true :: _ => if isLong x s then 0 else 2
    | true :: false :: _ :: _ => if isLong x s then 0 else 3
    | true :: true :: _ :: r => if drop1 r = [] then 0 else if isLong x s then 0 else 4
    | _ => 0
  | _ :: _ =>
    match s.S with
    | [] => 5
    | k :: _ => if k < 5 then k + 6 else 0

/-- The step in a given case. -/
def stepAt (x : List Bool) (s : QS) : ℕ → QS
  | 1 => ⟨(drop1 (s.P.drop 2)).tail, s.S, [s.Sg.getD (lead1 (s.P.drop 2)) false], s.Sg, s.D, s.H⟩
  | 2 => ⟨s.P.drop 2, [0, 0, 0, 0, 0, 0, 0] ++ s.S, s.M, s.Sg, s.D, s.H⟩
  | 3 => ⟨s.P.drop 3, [1, bitN (s.P.getD 2 false), 0, 0, 0, 0, 0] ++ s.S, s.M, s.Sg, s.D, s.H⟩
  | 4 => ⟨(drop1 (s.P.drop 3)).tail,
      [3, bitN (s.P.getD 2 false), 0, lead1 (s.P.drop 3),
        x.length - (drop1 (s.P.drop 3)).tail.length,
        bitN (s.Sg.getD (lead1 (s.P.drop 3)) false),
        bitN (s.D.getD (lead1 (s.P.drop 3)) false)] ++ s.S,
      s.M, s.Sg.set (lead1 (s.P.drop 3)) false, s.D.set (lead1 (s.P.drop 3)) true, s.H⟩
  | 5 => ⟨s.P, s.S, bw (s.M.headD false && s.P.isEmpty), s.Sg, s.D, []⟩
  | 6 => ⟨s.P, s.S.drop 7, [!s.M.headD false], s.Sg, s.D, s.H⟩
  | 7 => ⟨s.P, [2, s.S.getD 1 0, bitN (s.M.headD false), 0, 0, 0, 0] ++ s.S.drop 7, [], s.Sg,
      s.D, s.H⟩
  | 8 => ⟨s.P, s.S.drop 7, [comb (s.S.getD 1 0) (s.S.getD 2 0) (s.M.headD false)], s.Sg, s.D,
      s.H⟩
  | 9 => ⟨x.drop (s.S.getD 4 0),
      [4, s.S.getD 1 0, bitN (s.M.headD false), s.S.getD 3 0, s.S.getD 4 0, s.S.getD 5 0,
        s.S.getD 6 0] ++ s.S.drop 7,
      [], s.Sg.set (s.S.getD 3 0) true, s.D, s.H⟩
  | 10 => ⟨s.P, s.S.drop 7, [comb (s.S.getD 1 0) (s.S.getD 2 0) (s.M.headD false)],
      s.Sg.set (s.S.getD 3 0) (decide (s.S.getD 5 0 ≠ 0)),
      s.D.set (s.S.getD 3 0) (decide (s.S.getD 6 0 ≠ 0)), s.H⟩
  | _ => ⟨s.P, s.S, [], s.Sg, s.D, []⟩

/-- **One step of the evaluator.** -/
def qstep (x : List Bool) (s : QS) : QS := stepAt x s (caseNum x s)

theorem qstep_eq {x : List Bool} {s : QS} {c : ℕ} (h : caseNum x s = c) :
    qstep x s = stepAt x s c := by
  rw [qstep, h]

/-- The initial state on the input `x`. -/
def start (x : List Bool) : QS :=
  ⟨x, [], [], List.replicate (x.length + 1) false, List.replicate (x.length + 1) false, [true]⟩

/-! ### Runs -/

/-- `Steps x s t`: iterating the step from `s` gives `t`, through states that have not halted. -/
def Steps (x : List Bool) (s t : QS) : Prop :=
  ∃ k, (∀ j < k, ((qstep x)^[j] s).H ≠ []) ∧ (qstep x)^[k] s = t

/-- The machine rejects from `s`: it halts with `M = []`. -/
def Rej (x : List Bool) (s : QS) : Prop := ∃ t, Steps x s t ∧ t.H = [] ∧ t.M = []

variable {x : List Bool}

theorem Steps.refl (s : QS) : Steps x s s := ⟨0, fun j hj => absurd hj (by omega), rfl⟩

theorem Steps.head {s t : QS} (hs : s.H ≠ []) (h : Steps x (qstep x s) t) : Steps x s t := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨k + 1, fun j hj => ?_, by rw [Function.iterate_succ_apply]⟩
  rcases j with _ | j
  · exact hs
  · rw [Function.iterate_succ_apply]; exact hk j (by omega)

theorem Steps.trans {s t u : QS} (h₁ : Steps x s t) (h₂ : Steps x t u) : Steps x s u := by
  obtain ⟨k, hk, rfl⟩ := h₁
  obtain ⟨m, hm, rfl⟩ := h₂
  refine ⟨m + k, fun j hj => ?_, by rw [Function.iterate_add_apply]⟩
  by_cases hjk : j < k
  · exact hk j hjk
  · obtain ⟨l, rfl⟩ : ∃ l, j = l + k := ⟨j - k, by omega⟩
    rw [Function.iterate_add_apply]
    exact hm l (by omega)

theorem Steps.rej {s t : QS} (h : Steps x s t) (ht : Rej x t) : Rej x s := by
  obtain ⟨u, hu, huH, huM⟩ := ht
  exact ⟨u, h.trans hu, huH, huM⟩

theorem Rej.head {s : QS} (hs : s.H ≠ []) (h : Rej x (qstep x s)) : Rej x s :=
  (Steps.head hs (Steps.refl _)).rej h

theorem rej_of_case0 {s : QS} (hs : s.H ≠ []) (h : caseNum x s = 0) : Rej x s := by
  refine Rej.head hs ⟨_, Steps.refl _, ?_, ?_⟩ <;> rw [qstep_eq h] <;> rfl

/-- Halting states are reached only once. -/
theorem Steps.halt_unique {s t t' : QS} (h : Steps x s t) (h' : Steps x s t') (ht : t.H = [])
    (ht' : t'.H = []) : t = t' := by
  obtain ⟨k, hk, rfl⟩ := h
  obtain ⟨k', hk', rfl⟩ := h'
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · exact absurd ht (hk' k hlt)
  · rfl
  · exact absurd ht' (hk k' hlt)

/-! ### Words and codes -/

theorem getD_set_eq (l : List Bool) (i j : ℕ) (b : Bool) (hi : i < l.length) :
    (l.set i b).getD j false = Function.update (fun k => l.getD k false) i b j := by
  by_cases hji : j = i
  · subst hji; simp [List.getD_eq_getElem?_getD, hi]
  · rw [Function.update_of_ne hji]
    simp [List.getD_eq_getElem?_getD, Ne.symm hji]

theorem set_getD_self (l : List Bool) (i : ℕ) (hi : i < l.length) :
    l.set i (l.getD i false) = l := by
  rw [List.getD_eq_getElem _ _ hi, List.set_getElem_self]

theorem fieldsWord_append (l₁ l₂ : List ℕ) :
    fieldsWord (l₁ ++ l₂) = fieldsWord l₁ ++ fieldsWord l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a l ih => simp [fieldsWord, ih]

theorem length_fieldsWord (l : List ℕ) : (fieldsWord l).length = l.sum + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [fieldsWord, ih]; omega

theorem lead1_unary (i : ℕ) (X : List Bool) : lead1 (QBF.unary i ++ X) = i := by
  simp [QBF.unary]

theorem drop1_unary (i : ℕ) (X : List Bool) : drop1 (QBF.unary i ++ X) = false :: X := by
  simp [QBF.unary]

theorem unary_split : ∀ {r : List Bool}, drop1 r ≠ [] → r = QBF.unary (lead1 r) ++ (drop1 r).tail
  | [], h => absurd rfl h
  | false :: r, _ => by simp [QBF.unary, lead1, drop1]
  | true :: r, h => by
      have ih := unary_split (r := r) (by simpa [drop1] using h)
      simp only [lead1, drop1]
      conv_lhs => rw [ih]
      simp [QBF.unary, List.replicate_succ]

/-- A word that starts with the code of a formula. -/
def HasPre (P : List Bool) : Prop := ∃ (p : QBF) (r : List Bool), P = QBF.enc p ++ r

theorem enc_prefix_unique {p q : QBF} {r r' : List Bool} (h : QBF.enc p ++ r = QBF.enc q ++ r') :
    p = q ∧ r = r' := by
  have hp := QBF.dec_enc_append p (max p.size q.size) (le_max_left _ _) r
  have hq := QBF.dec_enc_append q (max p.size q.size) (le_max_right _ _) r'
  rw [h, hq] at hp
  simp only [Option.some.injEq, Prod.mk.injEq] at hp
  exact ⟨hp.1.symm, hp.2.symm⟩

/-! ### The run on the code of a formula -/

/-- The width allowed for one record in the depth budget. -/
def frameW (n : ℕ) : ℕ := 2 * n + 16

/-- What the run on the code of `p` does from any stack, assignment and binding: it returns the
value of `p` when the free variables are bound and the stack has room, it returns or rejects in
any case, and it rejects when a free variable is unbound. -/
def Good (x : List Bool) (p : QBF) : Prop :=
  ∀ (rest : List Bool) (S : List ℕ) (Sg D H : List Bool), H ≠ [] →
    (QBF.enc p ++ rest) <:+ x → Sg.length = x.length + 1 → D.length = x.length + 1 →
    ((∀ i ∈ p.free, D.getD i false = true) →
      (fieldsWord S).length + p.height * frameW x.length ≤ bound x.length →
      Steps x ⟨QBF.enc p ++ rest, S, [], Sg, D, H⟩
        ⟨rest, S, [QBF.eval (fun j => Sg.getD j false) p], Sg, D, H⟩) ∧
    (Steps x ⟨QBF.enc p ++ rest, S, [], Sg, D, H⟩
        ⟨rest, S, [QBF.eval (fun j => Sg.getD j false) p], Sg, D, H⟩ ∨
      Rej x ⟨QBF.enc p ++ rest, S, [], Sg, D, H⟩) ∧
    ((∃ i ∈ p.free, D.getD i false = false) → Rej x ⟨QBF.enc p ++ rest, S, [], Sg, D, H⟩)

theorem good_var (i : ℕ) : Good x (.var i) := by
  intro rest S Sg D H hH _ _ _
  have hP : QBF.enc (.var i) ++ rest = false :: false :: (QBF.unary i ++ rest) := by
    simp [QBF.enc]
  rw [hP]
  cases hDi : D.getD i false
  · have hrej : Rej x ⟨false :: false :: (QBF.unary i ++ rest), S, [], Sg, D, H⟩ :=
      rej_of_case0 hH
        (by simp [-List.getD_eq_getElem?_getD, caseNum, drop1_unary, lead1_unary, hDi])
    refine ⟨fun h _ => absurd (h i (by simp [QBF.free]))
      (by simp [-List.getD_eq_getElem?_getD, hDi]), Or.inr hrej,
      fun _ => hrej⟩
  · have hstep : Steps x ⟨false :: false :: (QBF.unary i ++ rest), S, [], Sg, D, H⟩
        ⟨rest, S, [QBF.eval (fun j => Sg.getD j false) (.var i)], Sg, D, H⟩ := by
      refine Steps.head hH ?_
      rw [qstep_eq (c := 1)
        (by simp [-List.getD_eq_getElem?_getD, caseNum, drop1_unary, lead1_unary, hDi])]
      simp only [stepAt, List.drop_succ_cons, List.drop_zero, drop1_unary, List.tail_cons,
        lead1_unary, QBF.eval]
      exact Steps.refl _
    refine ⟨fun _ _ => hstep, Or.inl hstep, fun ⟨j, hj, hjD⟩ => ?_⟩
    simp only [QBF.free, List.mem_singleton] at hj
    subst hj
    simp [-List.getD_eq_getElem?_getD, hDi] at hjD

theorem good_neg {p : QBF} (ih : Good x p) : Good x (.neg p) := by
  intro rest S Sg D H hH hsuf hSg hD
  have hP : QBF.enc (.neg p) ++ rest = false :: true :: (QBF.enc p ++ rest) := by
    simp [QBF.enc]
  rw [hP]
  rw [hP] at hsuf
  have hsuf' : (QBF.enc p ++ rest) <:+ x :=
    List.IsSuffix.trans (List.suffix_cons _ _ |>.trans (List.suffix_cons _ _)) hsuf
  by_cases hl : isLong x ⟨false :: true :: (QBF.enc p ++ rest), S, [], Sg, D, H⟩ = true
  · have hrej : Rej x ⟨false :: true :: (QBF.enc p ++ rest), S, [], Sg, D, H⟩ :=
      rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])
    refine ⟨fun _ hb => ?_, Or.inr hrej, fun _ => hrej⟩
    simp only [isLong, decide_eq_true_eq] at hl
    simp only [QBF.height_neg, frameW] at hb
    nlinarith
  · have hstep : qstep x ⟨false :: true :: (QBF.enc p ++ rest), S, [], Sg, D, H⟩ =
        ⟨QBF.enc p ++ rest, [0, 0, 0, 0, 0, 0, 0] ++ S, [], Sg, D, H⟩ := by
      rw [qstep_eq (c := 2) (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])]
      rfl
    have hret : ∀ v, Steps x ⟨rest, [0, 0, 0, 0, 0, 0, 0] ++ S, [v], Sg, D, H⟩
        ⟨rest, S, [!v], Sg, D, H⟩ := by
      intro v
      refine Steps.head hH ?_
      rw [qstep_eq (c := 6) (by simp [-List.getD_eq_getElem?_getD, caseNum])]
      exact Steps.refl _
    obtain ⟨hA, hB, hC⟩ := ih rest ([0, 0, 0, 0, 0, 0, 0] ++ S) Sg D H hH hsuf' hSg hD
    refine ⟨fun hfree hb => ?_, ?_, fun hex => ?_⟩
    · refine Steps.head hH ?_
      rw [hstep]
      refine (hA (fun i hi => hfree i (by simpa [QBF.free] using hi)) ?_).trans (hret _)
      rw [fieldsWord_append]
      simp only [QBF.height_neg, frameW] at hb
      simp only [List.length_append, frameW]
      have : (fieldsWord [0, 0, 0, 0, 0, 0, 0]).length = 7 := rfl
      nlinarith
    · rcases hB with h | h
      · exact Or.inl (Steps.head hH (by rw [hstep]; exact h.trans (hret _)))
      · exact Or.inr (Rej.head hH (by rw [hstep]; exact h))
    · exact Rej.head hH (by rw [hstep]; exact hC (by simpa [QBF.free] using hex))

/-- A binary connective: conjunction for `false`, disjunction for `true`. -/
def binQ : Bool → QBF → QBF → QBF
  | false, p, q => .conj p q
  | true, p, q => .disj p q

/-- A quantifier: universal for `false`, existential for `true`. -/
def quantQ : Bool → ℕ → QBF → QBF
  | false, i, p => .all i p
  | true, i, p => .ex i p

theorem bitN_le (b : Bool) : bitN b ≤ 1 := by cases b <;> simp [bitN]

theorem decide_bitN (b : Bool) : decide (bitN b ≠ 0) = b := by cases b <;> simp [bitN]

theorem comb_bitN (b v₁ v : Bool) :
    comb (bitN b) (bitN v₁) v = if b then (v₁ || v) else (v₁ && v) := by
  cases b <;> cases v₁ <;> simp [comb, bitN]

theorem drop_of_suffix {X x : List Bool} (h : X <:+ x) : x.drop (x.length - X.length) = X := by
  obtain ⟨u, rfl⟩ := h
  simp

theorem good_bin (b : Bool) {p q : QBF} (ihp : Good x p) (ihq : Good x q) :
    Good x (binQ b p q) := by
  intro rest S Sg D H hH hsuf hSg hD
  have hP : QBF.enc (binQ b p q) ++ rest =
      true :: false :: b :: (QBF.enc p ++ (QBF.enc q ++ rest)) := by
    cases b <;> simp [binQ, QBF.enc]
  have hfree : (binQ b p q).free = p.free ++ q.free := by cases b <;> rfl
  have hheight : (binQ b p q).height = max p.height q.height + 1 := by cases b <;> rfl
  have heval : ∀ σ : ℕ → Bool, QBF.eval σ (binQ b p q) =
      comb (bitN b) (bitN (QBF.eval σ p)) (QBF.eval σ q) := by
    intro σ; rw [comb_bitN]; cases b <;> rfl
  rw [hP]
  rw [hP] at hsuf
  have hsufp : (QBF.enc p ++ (QBF.enc q ++ rest)) <:+ x :=
    List.IsSuffix.trans ((List.suffix_cons _ _).trans ((List.suffix_cons _ _).trans
      (List.suffix_cons _ _))) hsuf
  have hsufq : (QBF.enc q ++ rest) <:+ x := (List.suffix_append _ _).trans hsufp
  set F1 : List ℕ := [1, bitN b, 0, 0, 0, 0, 0] with hF1
  set F2 : Bool → List ℕ := fun v => [2, bitN b, bitN v, 0, 0, 0, 0] with hF2
  have hF1l : (fieldsWord F1).length ≤ 9 := by
    rw [length_fieldsWord]; simp [hF1]; have := bitN_le b; omega
  have hF2l : ∀ v, (fieldsWord (F2 v)).length ≤ 11 := by
    intro v; rw [length_fieldsWord]; simp [hF2]; have := bitN_le b; have := bitN_le v; omega
  by_cases hl : isLong x ⟨true :: false :: b :: (QBF.enc p ++ (QBF.enc q ++ rest)), S, [], Sg, D,
      H⟩ = true
  · have hrej : Rej x ⟨true :: false :: b :: (QBF.enc p ++ (QBF.enc q ++ rest)), S, [], Sg, D, H⟩ :=
      rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])
    refine ⟨fun _ hb => ?_, Or.inr hrej, fun _ => hrej⟩
    simp only [isLong, decide_eq_true_eq] at hl
    rw [hheight] at hb
    simp only [frameW] at hb
    have : 0 < (max p.height q.height + 1) * (2 * x.length + 16) := by positivity
    omega
  · have hstep : qstep x ⟨true :: false :: b :: (QBF.enc p ++ (QBF.enc q ++ rest)), S, [], Sg, D,
        H⟩ = ⟨QBF.enc p ++ (QBF.enc q ++ rest), F1 ++ S, [], Sg, D, H⟩ := by
      rw [qstep_eq (c := 3) (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])]
      rfl
    have hmid : ∀ v, Steps x ⟨QBF.enc q ++ rest, F1 ++ S, [v], Sg, D, H⟩
        ⟨QBF.enc q ++ rest, F2 v ++ S, [], Sg, D, H⟩ := by
      intro v
      refine Steps.head hH ?_
      rw [qstep_eq (c := 7) (by simp [-List.getD_eq_getElem?_getD, caseNum, hF1])]
      exact Steps.refl _
    have hfin : ∀ v w, Steps x ⟨rest, F2 v ++ S, [w], Sg, D, H⟩
        ⟨rest, S, [comb (bitN b) (bitN v) w], Sg, D, H⟩ := by
      intro v w
      refine Steps.head hH ?_
      rw [qstep_eq (c := 8) (by simp [-List.getD_eq_getElem?_getD, caseNum, hF2])]
      exact Steps.refl _
    obtain ⟨hAp, hBp, hCp⟩ := ihp (QBF.enc q ++ rest) (F1 ++ S) Sg D H hH hsufp hSg hD
    have hq := fun v => ihq rest (F2 v ++ S) Sg D H hH hsufq hSg hD
    refine ⟨fun hfr hb => ?_, ?_, fun hex => ?_⟩
    · rw [hheight] at hb
      simp only [frameW] at hb
      have h1 := hAp (fun i hi => hfr i (by rw [hfree]; exact List.mem_append_left _ hi)) (by
        rw [fieldsWord_append, List.length_append]
        simp only [frameW]
        have := le_max_left p.height q.height
        nlinarith)
      have h2 := (hq (QBF.eval (fun j => Sg.getD j false) p)).1
        (fun i hi => hfr i (by rw [hfree]; exact List.mem_append_right _ hi)) (by
        rw [fieldsWord_append, List.length_append]
        simp only [frameW]
        have := le_max_right p.height q.height
        have := hF2l (QBF.eval (fun j => Sg.getD j false) p)
        nlinarith)
      refine Steps.head hH ?_
      rw [hstep, heval]
      exact h1.trans ((hmid _).trans (h2.trans (hfin _ _)))
    · rcases hBp with h1 | h1
      · rcases (hq (QBF.eval (fun j => Sg.getD j false) p)).2.1 with h2 | h2
        · refine Or.inl (Steps.head hH ?_)
          rw [hstep, heval]
          exact h1.trans ((hmid _).trans (h2.trans (hfin _ _)))
        · exact Or.inr (Rej.head hH (by rw [hstep]; exact h1.rej ((hmid _).rej h2)))
      · exact Or.inr (Rej.head hH (by rw [hstep]; exact h1))
    · obtain ⟨i, hi, hiD⟩ := hex
      rw [hfree, List.mem_append] at hi
      rcases hi with hi | hi
      · exact Rej.head hH (by rw [hstep]; exact hCp ⟨i, hi, hiD⟩)
      · rcases hBp with h1 | h1
        · exact Rej.head hH (by
            rw [hstep]
            exact h1.rej ((hmid _).rej ((hq _).2.2 ⟨i, hi, hiD⟩)))
        · exact Rej.head hH (by rw [hstep]; exact h1)

theorem good_quant (b : Bool) (i : ℕ) {p : QBF} (ih : Good x p) : Good x (quantQ b i p) := by
  intro rest S Sg D H hH hsuf hSg hD
  set X := QBF.enc p ++ rest with hX
  have hP : QBF.enc (quantQ b i p) ++ rest = true :: true :: b :: (QBF.unary i ++ X) := by
    cases b <;> simp [quantQ, QBF.enc, hX]
  have hfree : (quantQ b i p).free = p.free.filter (fun j => j ≠ i) := by cases b <;> rfl
  have hheight : (quantQ b i p).height = p.height + 1 := by cases b <;> rfl
  have heval : ∀ σ : ℕ → Bool, QBF.eval σ (quantQ b i p) =
      comb (bitN b) (bitN (QBF.eval (Function.update σ i false) p))
        (QBF.eval (Function.update σ i true) p) := by
    intro σ; rw [comb_bitN]; cases b <;> rfl
  rw [hP]
  rw [hP] at hsuf
  have hsufX : X <:+ x :=
    List.IsSuffix.trans ((List.suffix_append _ _).trans ((List.suffix_cons _ _).trans
      ((List.suffix_cons _ _).trans (List.suffix_cons _ _)))) hsuf
  have hlen := hsuf.length_le
  simp only [List.length_cons, List.length_append, QBF.length_unary] at hlen
  have hi : i < Sg.length := by omega
  have hiD : i < D.length := by omega
  set n := x.length with hn
  set σ : ℕ → Bool := fun j => Sg.getD j false with hσ
  set F1 : List ℕ := [3, bitN b, 0, i, n - X.length, bitN (Sg.getD i false),
    bitN (D.getD i false)] with hF1
  set F2 : Bool → List ℕ := fun v => [4, bitN b, bitN v, i, n - X.length,
    bitN (Sg.getD i false), bitN (D.getD i false)] with hF2
  have hF1l : (fieldsWord F1).length + frameW n ≤ 2 * frameW n := by
    rw [length_fieldsWord]; simp only [hF1, frameW, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    have := bitN_le b; have := bitN_le (Sg.getD i false); have := bitN_le (D.getD i false)
    omega
  have hF2l : ∀ v, (fieldsWord (F2 v)).length ≤ frameW n := by
    intro v
    rw [length_fieldsWord]; simp only [hF2, frameW, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    have := bitN_le b; have := bitN_le v; have := bitN_le (Sg.getD i false)
    have := bitN_le (D.getD i false)
    omega
  have hF1l' : (fieldsWord F1).length ≤ frameW n := by
    have := hF1l; simp only [frameW] at this ⊢; omega
  by_cases hl : isLong x ⟨true :: true :: b :: (QBF.unary i ++ X), S, [], Sg, D, H⟩ = true
  · have hrej : Rej x ⟨true :: true :: b :: (QBF.unary i ++ X), S, [], Sg, D, H⟩ :=
      rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hl, drop1_unary])
    refine ⟨fun _ hb => ?_, Or.inr hrej, fun _ => hrej⟩
    simp only [isLong, decide_eq_true_eq, ← hn] at hl
    rw [hheight] at hb
    simp only [frameW] at hb
    have : 0 < (p.height + 1) * (2 * n + 16) := by positivity
    omega
  · have hstep : qstep x ⟨true :: true :: b :: (QBF.unary i ++ X), S, [], Sg, D, H⟩ =
        ⟨X, F1 ++ S, [], Sg.set i false, D.set i true, H⟩ := by
      rw [qstep_eq (c := 4) (by simp [-List.getD_eq_getElem?_getD, caseNum, hl, drop1_unary])]
      simp only [stepAt, List.drop_succ_cons, List.drop_zero, drop1_unary, lead1_unary,
        List.tail_cons, List.getD_cons_succ, List.getD_cons_zero, hF1]
      rfl
    have hmid : ∀ v, Steps x ⟨rest, F1 ++ S, [v], Sg.set i false, D.set i true, H⟩
        ⟨X, F2 v ++ S, [], Sg.set i true, D.set i true, H⟩ := by
      intro v
      refine Steps.head hH ?_
      rw [qstep_eq (c := 9) (by simp [-List.getD_eq_getElem?_getD, caseNum, hF1])]
      simp only [stepAt, hF1, hF2, List.cons_append, List.getD_cons_succ, List.getD_cons_zero,
        List.drop_succ_cons, List.drop_zero, List.nil_append, List.set_set, List.headD_cons]
      rw [show List.drop (n - X.length) x = X from drop_of_suffix hsufX]
      exact Steps.refl _
    have hfin : ∀ v w, Steps x ⟨rest, F2 v ++ S, [w], Sg.set i true, D.set i true, H⟩
        ⟨rest, S, [comb (bitN b) (bitN v) w], Sg, D, H⟩ := by
      intro v w
      refine Steps.head hH ?_
      rw [qstep_eq (c := 10) (by simp [-List.getD_eq_getElem?_getD, caseNum, hF2])]
      simp only [stepAt, hF2, List.cons_append, List.getD_cons_succ, List.getD_cons_zero,
        List.drop_succ_cons, List.drop_zero, List.nil_append, List.set_set, decide_bitN,
        set_getD_self Sg i hi, set_getD_self D i hiD, List.headD_cons]
      exact Steps.refl _
    have hSg1 : (Sg.set i false).length = n + 1 := by rw [List.length_set]; exact hSg
    have hSg2 : (Sg.set i true).length = n + 1 := by rw [List.length_set]; exact hSg
    have hD1 : (D.set i true).length = n + 1 := by rw [List.length_set]; exact hD
    have hσ1 : (fun j => (Sg.set i false).getD j false) = Function.update σ i false := by
      funext j; exact getD_set_eq Sg i j false hi
    have hσ2 : (fun j => (Sg.set i true).getD j false) = Function.update σ i true := by
      funext j; exact getD_set_eq Sg i j true hi
    have hDj : ∀ j, j ≠ i → (D.set i true).getD j false = D.getD j false := by
      intro j hj; rw [getD_set_eq D i j true hiD, Function.update_of_ne hj]
    have hDi : (D.set i true).getD i false = true := by
      rw [getD_set_eq D i i true hiD, Function.update_self]
    obtain ⟨hA1, hB1, hC1⟩ := ih rest (F1 ++ S) (Sg.set i false) (D.set i true) H hH hsufX hSg1 hD1
    have h2 := fun v => ih rest (F2 v ++ S) (Sg.set i true) (D.set i true) H hH hsufX hSg2 hD1
    rw [hσ1] at hA1 hB1
    have hfree' : (∀ j ∈ (quantQ b i p).free, D.getD j false = true) →
        ∀ j ∈ p.free, (D.set i true).getD j false = true := by
      intro hfr j hj
      by_cases hji : j = i
      · subst hji; exact hDi
      · rw [hDj j hji]; exact hfr j (by rw [hfree]; simp [hj, hji])
    refine ⟨fun hfr hb => ?_, ?_, fun hex => ?_⟩
    · rw [hheight] at hb
      have e1 := hA1 (hfree' hfr) (by
        rw [fieldsWord_append, List.length_append]
        nlinarith)
      have e2 := (h2 (QBF.eval (Function.update σ i false) p)).1 (hfree' hfr) (by
        rw [fieldsWord_append, List.length_append]
        have := hF2l (QBF.eval (Function.update σ i false) p)
        nlinarith)
      rw [hσ2] at e2
      refine Steps.head hH ?_
      rw [hstep, heval]
      exact e1.trans ((hmid _).trans (e2.trans (hfin _ _)))
    · rcases hB1 with e1 | e1
      · rcases (h2 (QBF.eval (Function.update σ i false) p)).2.1 with e2 | e2
        · rw [hσ2] at e2
          refine Or.inl (Steps.head hH ?_)
          rw [hstep, heval]
          exact e1.trans ((hmid _).trans (e2.trans (hfin _ _)))
        · exact Or.inr (Rej.head hH (by rw [hstep]; exact e1.rej ((hmid _).rej e2)))
      · exact Or.inr (Rej.head hH (by rw [hstep]; exact e1))
    · obtain ⟨j, hj, hjD⟩ := hex
      rw [hfree, List.mem_filter] at hj
      have hji : j ≠ i := by simpa using hj.2
      exact Rej.head hH (by rw [hstep]; exact hC1 ⟨j, hj.1, by rw [hDj j hji]; exact hjD⟩)

/-- **The run on the code of a formula.** -/
theorem good : ∀ p : QBF, Good x p
  | .var i => good_var i
  | .neg p => good_neg (good p)
  | .conj p q => good_bin false (good p) (good q)
  | .disj p q => good_bin true (good p) (good q)
  | .all i p => good_quant false i (good p)
  | .ex i p => good_quant true i (good p)

/-! ### Words that are not codes -/

/-- **On a word that does not start with the code of a formula the machine rejects.** -/
theorem rej_noPre : ∀ (m : ℕ) (P : List Bool), P.length ≤ m → ¬ HasPre P →
    ∀ (S : List ℕ) (Sg D H : List Bool), H ≠ [] → P <:+ x → Sg.length = x.length + 1 →
    D.length = x.length + 1 → Rej x ⟨P, S, [], Sg, D, H⟩ := by
  intro m
  induction m with
  | zero =>
      intro P hP _ S Sg D H hH _ _ _
      rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hP)]
      exact rej_of_case0 hH (by simp [caseNum])
  | succ m ih =>
      intro P hP hnp S Sg D H hH hsuf hSg hD
      rcases P with _ | ⟨b0, _ | ⟨b1, r⟩⟩
      · exact rej_of_case0 hH (by simp [caseNum])
      · exact rej_of_case0 hH (by cases b0 <;> simp [caseNum])
      have hsufr : r <:+ x := ((List.suffix_cons _ _).trans (List.suffix_cons _ _)).trans hsuf
      have hrm : r.length ≤ m := by simp at hP; omega
      cases b0 <;> cases b1
      · -- a variable
        by_cases hd : drop1 r = []
        · exact rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hd])
        · exact absurd ⟨.var (lead1 r), (drop1 r).tail, by
            conv_lhs => rw [unary_split hd]
            simp [QBF.enc]⟩ hnp
      · -- a negation
        by_cases hl : isLong x ⟨false :: true :: r, S, [], Sg, D, H⟩ = true
        · exact rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])
        · refine Rej.head hH ?_
          rw [qstep_eq (c := 2) (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])]
          refine ih r hrm (fun ⟨p, t, hr⟩ => hnp ⟨.neg p, t, by rw [hr]; simp [QBF.enc]⟩) _ _ _ _
            hH hsufr hSg hD
      · -- a binary connective
        rcases r with _ | ⟨b, r⟩
        · exact rej_of_case0 hH (by simp [caseNum])
        have hsufr' : r <:+ x := (List.suffix_cons _ _).trans hsufr
        have hrm' : r.length ≤ m := by simp at hrm; omega
        by_cases hl : isLong x ⟨true :: false :: b :: r, S, [], Sg, D, H⟩ = true
        · exact rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])
        refine Rej.head hH ?_
        rw [qstep_eq (c := 3) (by simp [-List.getD_eq_getElem?_getD, caseNum, hl])]
        by_cases hpre : HasPre r
        · obtain ⟨p, t, rfl⟩ := hpre
          have hsuft : t <:+ x := (List.suffix_append _ _).trans hsufr'
          have htm : t.length < m + 1 := by simp at hrm'; omega
          rcases ((good p) t _ Sg D H hH hsufr' hSg hD).2.1 with h1 | h1
          · refine h1.rej (Rej.head hH ?_)
            rw [qstep_eq (c := 7) (by simp [-List.getD_eq_getElem?_getD, caseNum])]
            refine ih t (by omega) (fun ⟨q, t', ht⟩ => hnp ⟨binQ b p q, t', ?_⟩) _ _ _ _ hH hsuft
              hSg hD
            rw [ht]
            cases b <;> simp [binQ, QBF.enc]
          · exact h1
        · exact ih r hrm' hpre _ _ _ _ hH hsufr' hSg hD
      · -- a quantifier
        rcases r with _ | ⟨b, r⟩
        · exact rej_of_case0 hH (by simp [caseNum])
        have hsufr' : r <:+ x := (List.suffix_cons _ _).trans hsufr
        by_cases hd : drop1 r = []
        · exact rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hd])
        obtain ⟨i, r', rfl⟩ : ∃ i r', r = QBF.unary i ++ r' := ⟨_, _, unary_split hd⟩
        have hsufr'' : r' <:+ x := (List.suffix_append _ _).trans hsufr'
        have hrm' : r'.length ≤ m := by simp at hrm; omega
        by_cases hl : isLong x ⟨true :: true :: b :: (QBF.unary i ++ r'), S, [], Sg, D, H⟩ = true
        · exact rej_of_case0 hH (by simp [-List.getD_eq_getElem?_getD, caseNum, hl, drop1_unary])
        refine Rej.head hH ?_
        rw [qstep_eq (c := 4) (by simp [-List.getD_eq_getElem?_getD, caseNum, hl, drop1_unary])]
        simp only [stepAt, List.drop_succ_cons, List.drop_zero, drop1_unary, lead1_unary,
          List.tail_cons]
        refine ih r' hrm' (fun ⟨p, t, ht⟩ => hnp ⟨quantQ b i p, t, ?_⟩) _ _ _ _ hH hsufr''
          (by rw [List.length_set]; exact hSg) (by rw [List.length_set]; exact hD)
        rw [ht]
        cases b <;> simp [quantQ, QBF.enc]

/-! ### From the initial state -/

theorem getD_replicate_false (n j : ℕ) : (List.replicate n false).getD j false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> rfl

/-- The last step: returning with an empty stack halts, accepting exactly on a true value with
the whole input read. -/
theorem steps_halt (P Sg D H : List Bool) (v : Bool) (hH : H ≠ []) :
    Steps x ⟨P, [], [v], Sg, D, H⟩ ⟨P, [], bw (v && P.isEmpty), Sg, D, []⟩ := by
  refine Steps.head hH ?_
  rw [qstep_eq (c := 5) (by simp [caseNum])]
  exact Steps.refl _

/-- **From the initial state the machine halts on every word.** -/
theorem halts (x : List Bool) : ∃ t, Steps x (start x) t ∧ t.H = [] := by
  have hRl : (List.replicate (x.length + 1) false).length = x.length + 1 :=
    List.length_replicate ..
  have hT : ([true] : List Bool) ≠ [] := List.cons_ne_nil _ _
  by_cases hpre : HasPre x
  · obtain ⟨p, rest, hx⟩ := hpre
    have hsuf : (QBF.enc p ++ rest) <:+ x := by rw [← hx]
    obtain ⟨_, hB, _⟩ := (good (x := x) p) rest [] (List.replicate (x.length + 1) false)
      (List.replicate (x.length + 1) false) [true] hT hsuf hRl hRl
    have hs : start x = ⟨QBF.enc p ++ rest, [], [], List.replicate (x.length + 1) false,
        List.replicate (x.length + 1) false, [true]⟩ := by rw [start, ← hx]
    rw [hs]
    rcases hB with h | ⟨t, ht, htH, _⟩
    · exact ⟨_, h.trans (steps_halt _ _ _ _ _ hT), rfl⟩
    · exact ⟨t, ht, htH⟩
  · obtain ⟨t, ht, htH, _⟩ := rej_noPre (x := x) x.length x le_rfl hpre [] _ _ [true] hT
      List.suffix_rfl hRl hRl
    exact ⟨t, ht, htH⟩

/-- **From the initial state the machine accepts exactly the codes of true closed formulas.** -/
theorem accepts_iff (x : List Bool) :
    (∃ t, Steps x (start x) t ∧ t.H = [] ∧ t.M ≠ []) ↔ tqbfLang x := by
  set R := List.replicate (x.length + 1) false with hR
  have hRl : R.length = x.length + 1 := List.length_replicate ..
  have hT : ([true] : List Bool) ≠ [] := List.cons_ne_nil _ _
  have hRg : (fun j => R.getD j false) = fun _ => false := by
    funext j; exact getD_replicate_false _ _
  constructor
  · rintro ⟨t, ht, htH, htM⟩
    by_cases hpre : HasPre x
    · obtain ⟨p, rest, hx⟩ := hpre
      have hsuf : (QBF.enc p ++ rest) <:+ x := by rw [← hx]
      obtain ⟨_, hB, hC⟩ := (good (x := x) p) rest [] R R [true] hT hsuf hRl hRl
      have hs : start x = ⟨QBF.enc p ++ rest, [], [], R, R, [true]⟩ := by rw [start, ← hx]
      rw [hs] at ht
      have hnrej : ¬ Rej x ⟨QBF.enc p ++ rest, [], [], R, R, [true]⟩ := by
        rintro ⟨u, hu, huH, huM⟩
        rw [ht.halt_unique hu htH huH] at htM
        exact htM huM
      rcases hB with h | h
      · have h' := h.trans (steps_halt _ _ _ _ _ hT)
        have he := ht.halt_unique h' htH rfl
        rw [he, hRg] at htM
        have hv : QBF.eval (fun _ => false) p = true := by
          by_contra hne
          simp only [Bool.not_eq_true] at hne
          simp [hne, bw] at htM
        have hr : rest = [] := by
          by_contra hne
          have : rest.isEmpty = false := by simpa [List.isEmpty_iff] using hne
          simp [this, bw] at htM
        refine ⟨p, by rw [hx, hr, List.append_nil], ?_, hv⟩
        by_contra hcl
        obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hcl
        exact hnrej (hC ⟨i, hi, getD_replicate_false _ _⟩)
      · exact absurd h hnrej
    · obtain ⟨u, hu, huH, huM⟩ := rej_noPre (x := x) x.length x le_rfl hpre [] _ _ [true]
        hT List.suffix_rfl hRl hRl
      rw [ht.halt_unique hu htH huH] at htM
      exact absurd huM htM
  · rintro ⟨p, hx, hcl, hv⟩
    have hsuf : (QBF.enc p ++ []) <:+ x := by rw [List.append_nil, hx]
    obtain ⟨hA, _, _⟩ := (good (x := x) p) [] [] R R [true] hT hsuf hRl hRl
    have hfr : ∀ i ∈ p.free, R.getD i false = true := by
      intro i hi; rw [hcl] at hi; simp at hi
    have hh := QBF.height_lt_length_enc p
    rw [hx] at hh
    have h := hA hfr (by simp only [fieldsWord, List.length_nil, frameW, bound]; nlinarith)
    have hs : start x = ⟨QBF.enc p ++ [], [], [], R, R, [true]⟩ := by
      rw [start, List.append_nil, hx]
    refine ⟨⟨[], [], bw (QBF.eval (fun j => R.getD j false) p && ([] : List Bool).isEmpty), R, R,
      []⟩, ?_, rfl, ?_⟩
    · rw [hs]
      exact h.trans (steps_halt _ _ _ _ _ hT)
    · rw [hRg, hv]; simp [bw]

/-! ### The invariant -/

/-- What every reachable state satisfies; it bounds every component. -/
def Inv (x : List Bool) (s : QS) : Prop :=
  s.P <:+ x ∧ 7 ∣ s.S.length ∧ s.S.length ≤ bound x.length + 7 ∧
    (∀ a ∈ s.S, a ≤ x.length + 4) ∧ s.M.length ≤ 1 ∧ s.Sg.length = x.length + 1 ∧
    s.D.length = x.length + 1 ∧ s.H.length ≤ 1

theorem drop1_suffix : ∀ r : List Bool, drop1 r <:+ r
  | [] => List.suffix_rfl
  | false :: _ => List.suffix_rfl
  | true :: r => (drop1_suffix r).trans (List.suffix_cons _ _)

theorem tail_suffix (r : List Bool) : r.tail <:+ r := by
  cases r with
  | nil => exact List.suffix_rfl
  | cons b r => exact List.suffix_cons _ _

theorem length_le_length_fieldsWord (l : List ℕ) : l.length ≤ (fieldsWord l).length := by
  rw [length_fieldsWord]; omega

theorem not_long_of_case {s : QS} (h : caseNum x s = 2 ∨ caseNum x s = 3 ∨ caseNum x s = 4) :
    isLong x s = false := by
  rcases s with ⟨P, S, M, Sg, D, H⟩
  rcases M with _ | ⟨m, M⟩
  · unfold caseNum at h
    simp only at h
    split at h <;> (try split_ifs at h) <;> simp_all
  · rcases S with _ | ⟨k, S⟩
    · simp [caseNum] at h
    · simp only [caseNum] at h
      split_ifs at h <;> simp_all

theorem caseNum_ret {s : QS} (h : 6 ≤ caseNum x s) : s.S ≠ [] := by
  rcases s with ⟨P, S, M, Sg, D, H⟩
  rcases M with _ | ⟨m, M⟩
  · exfalso
    simp only [caseNum] at h
    split at h <;> (try split_ifs at h) <;> omega
  · rcases S with _ | ⟨k, S⟩
    · simp [caseNum] at h
    · simp

theorem caseNum_le (s : QS) : caseNum x s ≤ 10 := by
  rcases s with ⟨P, S, M, Sg, D, H⟩
  simp only [caseNum]
  split <;> (try split) <;> (try split_ifs) <;> omega

theorem getD_le_of_forall {S : List ℕ} {c : ℕ} (h : ∀ a ∈ S, a ≤ c) (j : ℕ) : S.getD j 0 ≤ c := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : S[j]? with
  | none => simp
  | some a => exact h a (List.mem_of_getElem? hj)

/-- **The invariant is preserved by the step.** -/
theorem inv_qstep {s : QS} (hs : Inv x s) : Inv x (qstep x s) := by
  obtain ⟨hP, hdiv, hlen, hent, hM, hSg, hD, hH⟩ := hs
  have hPn := hP.length_le
  have hc := caseNum_le (x := x) s
  have hpush : caseNum x s = 2 ∨ caseNum x s = 3 ∨ caseNum x s = 4 →
      s.S.length + 7 ≤ bound x.length + 7 := by
    intro h
    have hl := not_long_of_case h
    simp only [isLong, decide_eq_false_iff_not, not_le] at hl
    have := length_le_length_fieldsWord s.S
    omega
  have hret : 6 ≤ caseNum x s → 7 ≤ s.S.length := by
    intro h
    have hne := caseNum_ret h
    obtain ⟨k, hk⟩ := hdiv
    have : s.S.length ≠ 0 := by simpa using hne
    omega
  have hentj : ∀ j, s.S.getD j 0 ≤ x.length + 4 := getD_le_of_forall hent
  have hmem_drop : ∀ a ∈ s.S.drop 7, a ≤ x.length + 4 :=
    fun a ha => hent a (List.mem_of_mem_drop ha)
  rw [qstep_eq rfl]
  generalize hcn : caseNum x s = c at hc hpush hret
  interval_cases c <;> dsimp only [stepAt]
  · exact ⟨hP, hdiv, hlen, hent, by simp, hSg, hD, by simp⟩
  · refine ⟨((tail_suffix _).trans ((drop1_suffix _).trans (List.drop_suffix _ _))).trans hP,
      hdiv, hlen, hent, by simp, hSg, hD, hH⟩
  · refine ⟨(List.drop_suffix _ _).trans hP, ?_, ?_, ?_, hM, hSg, hD, hH⟩
    · simpa using Nat.dvd_add hdiv (dvd_refl 7)
    · simpa using hpush (by omega)
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha <;>
        first | omega | exact hent a ha
  · refine ⟨(List.drop_suffix _ _).trans hP, ?_, ?_, ?_, hM, hSg, hD, hH⟩
    · simpa using Nat.dvd_add hdiv (dvd_refl 7)
    · simpa using hpush (by omega)
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
      have := bitN_le (s.P.getD 2 false)
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha <;>
        first | omega | exact hent a ha
  · have hl1 : lead1 (s.P.drop 3) ≤ x.length :=
      le_trans (lead1_le _) (le_trans (by simp) hPn)
    refine ⟨((tail_suffix _).trans ((drop1_suffix _).trans (List.drop_suffix _ _))).trans hP,
      ?_, ?_, ?_, hM, by simpa using hSg, by simpa using hD, hH⟩
    · simpa using Nat.dvd_add hdiv (dvd_refl 7)
    · simpa using hpush (by omega)
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
      have := bitN_le (s.P.getD 2 false)
      have := bitN_le (s.Sg.getD (lead1 (s.P.drop 3)) false)
      have := bitN_le (s.D.getD (lead1 (s.P.drop 3)) false)
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha <;>
        first | omega | exact hent a ha
  · exact ⟨hP, hdiv, hlen, hent, by unfold bw; split_ifs <;> simp, hSg, hD, by simp⟩
  · refine ⟨hP, ?_, ?_, hmem_drop, by simp, hSg, hD, hH⟩
    · have := hret (by omega); simp only [List.length_drop]; exact Nat.dvd_sub hdiv (dvd_refl 7)
    · simp only [List.length_drop]; omega
  · have h7 := hret (by omega)
    refine ⟨hP, ?_, ?_, ?_, by simp, hSg, hD, hH⟩
    · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_drop]
      rw [show s.S.length - 7 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = s.S.length by omega]; exact hdiv
    · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_drop]; omega
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
      have := bitN_le (s.M.headD false)
      have := hentj 1
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha <;>
        first | omega | exact hmem_drop a ha
  · refine ⟨hP, ?_, ?_, hmem_drop, by simp, hSg, hD, hH⟩
    · have := hret (by omega); simp only [List.length_drop]; exact Nat.dvd_sub hdiv (dvd_refl 7)
    · simp only [List.length_drop]; omega
  · have h7 := hret (by omega)
    refine ⟨List.drop_suffix _ _, ?_, ?_, ?_, by simp, by simpa using hSg, hD, hH⟩
    · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_drop]
      rw [show s.S.length - 7 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = s.S.length by omega]; exact hdiv
    · simp only [List.cons_append, List.nil_append, List.length_cons, List.length_drop]; omega
    · intro a ha
      simp only [List.cons_append, List.nil_append, List.mem_cons] at ha
      have := bitN_le (s.M.headD false)
      have := hentj 1; have := hentj 3; have := hentj 4; have := hentj 5; have := hentj 6
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | ha <;>
        first | omega | exact hmem_drop a ha
  · refine ⟨hP, ?_, ?_, hmem_drop, by simp, by simpa using hSg,
      by simpa using hD, hH⟩
    · have := hret (by omega); simp only [List.length_drop]; exact Nat.dvd_sub hdiv (dvd_refl 7)
    · simp only [List.length_drop]; omega

theorem inv_start (x : List Bool) : Inv x (start x) := by
  refine ⟨List.suffix_rfl, by simp [start], by simp [start], by simp [start], by simp [start],
    by simp [start], by simp [start], by simp [start]⟩

theorem inv_iterate (x : List Bool) (k : ℕ) : Inv x ((qstep x)^[k] (start x)) := by
  induction k with
  | zero => exact inv_start x
  | succ k ih => rw [Function.iterate_succ_apply']; exact inv_qstep ih

/-- A bound on every component of a state satisfying the invariant. -/
def regBound (n : ℕ) : ℕ := (bound n + 7) * (n + 5) + n + 1

theorem length_fieldsWord_le {s : QS} (hs : Inv x s) :
    (fieldsWord s.S).length ≤ (bound x.length + 7) * (x.length + 5) := by
  obtain ⟨_, _, hlen, hent, _⟩ := hs
  rw [length_fieldsWord]
  have : s.S.sum ≤ s.S.length * (x.length + 4) := by
    have := List.sum_le_card_nsmul s.S (x.length + 4) hent
    simpa using this
  nlinarith

end EvalW

end Complexity.Qbf
