/-
**`NP` is closed under intersection.**

`Start/ComplexityClasses.lean` proves that `NP` is closed under union — the witness carries a tag
bit saying which of the two verifiers to run — and `Start/ThreeSat.lean` that it is closed under
intersection with `P`.  Intersection of two `NP` languages needs a witness that carries *both*
witnesses, so it needs a pairing of words which a Cobham term can undo.

The pairing used here is the classical self-delimiting one: the first component is written with
every bit doubled, the marker `10` ends it, and the second component follows verbatim.  Both
projections are then finite-state transductions of the pairing word, so
`Start/CobhamTransducer.lean` turns them into Cobham terms.  On an arbitrary word — the verifier
must be total — the projections read whatever they can, and the length of the word is bounded by
`2 * |fst| + 3 + |snd|`, which is what keeps the witness bound polynomial.

Main definitions:

* `Complexity.pairDelta` — the four-state automaton reading a pairing word;
* `Complexity.pairW` — the pairing of two words;
* `Complexity.fstOf`, `Complexity.sndOf` — the two projections, and `Complexity.fstTerm`,
  `Complexity.sndTerm` — the Cobham terms computing them.

Main results:

* `Complexity.fstOf_pairW`, `Complexity.sndOf_pairW` — the projections undo the pairing;
* `Complexity.length_le_of_proj` — a word is no longer than `2 * |fst| + 3 + |snd|`;
* `Complexity.eval_fstTerm`, `Complexity.eval_sndTerm` — the projections are Cobham functions;
* `Complexity.InNP.inter` — **`NP` is closed under intersection**.
-/

import Start.CobhamTransducer
import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Scanning from the left, on a concatenation -/

theorem lst_append (δ : ℕ → Bool → ℕ) (s : ℕ) (y z : Word) :
    lst δ s (y ++ z) = lst δ (lst δ s y) z := by
  induction y generalizing s with
  | nil => rfl
  | cons c y ih => rw [List.cons_append, lst, lst, ih]

theorem lrun_append (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) (y z : Word) :
    lrun δ out s (y ++ z) = lrun δ out s y ++ lrun δ out (lst δ s y) z := by
  induction y generalizing s with
  | nil => simp [lrun, lst]
  | cons c y ih => rw [List.cons_append, lrun, lrun, ih, lst, List.append_assoc]

/-! ### The pairing of two words -/

/-- The automaton reading a pairing word: state `0` expects the first bit of a doubled pair,
states `1` and `2` remember that bit, and state `3` — reached at the first mismatched pair, the
marker — is the tail, where the second component is read. -/
def pairDelta (s : ℕ) (b : Bool) : ℕ :=
  match s, b with
  | 0, false => 1
  | 0, true => 2
  | 1, false => 0
  | 2, true => 0
  | _, _ => 3

theorem pairDelta_lt (s : ℕ) (b : Bool) : pairDelta s b < 4 := by
  match s, b with
  | 0, false => simp [pairDelta]
  | 0, true => simp [pairDelta]
  | 1, false => simp [pairDelta]
  | 1, true => simp [pairDelta]
  | 2, false => simp [pairDelta]
  | 2, true => simp [pairDelta]
  | (n + 3), b => cases b <;> simp [pairDelta]

/-- The output of the first projection: a bit is emitted when a doubled pair is completed. -/
def pairOutFst (s : ℕ) (b : Bool) : Word :=
  match s, b with
  | 1, false => [false]
  | 2, true => [true]
  | _, _ => []

/-- The output of the second projection: after the marker, every bit is emitted. -/
def pairOutSnd : ℕ → Bool → Word
  | 3, b => [b]
  | _, _ => []

/-- The first component read off a word. -/
def fstOf (x : Word) : Word := lrun pairDelta pairOutFst 0 x

/-- The second component read off a word. -/
def sndOf (x : Word) : Word := lrun pairDelta pairOutSnd 0 x

/-- **The pairing of two words**: the first with every bit doubled, the marker `10`, then the
second. -/
def pairW (u v : Word) : Word := (u.flatMap fun b => [b, b]) ++ [true, false] ++ v

/-! ### The projections undo the pairing -/

theorem lst_tail (v : Word) : lst pairDelta 3 v = 3 := by
  induction v with
  | nil => rfl
  | cons b v ih => rw [lst, show pairDelta 3 b = 3 by cases b <;> rfl, ih]

theorem lrun_fst_tail (v : Word) : lrun pairDelta pairOutFst 3 v = [] := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [lrun, show pairDelta 3 b = 3 by cases b <;> rfl, ih,
        show pairOutFst 3 b = [] by cases b <;> rfl]
      rfl

theorem lrun_snd_tail (v : Word) : lrun pairDelta pairOutSnd 3 v = v := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [lrun, show pairDelta 3 b = 3 by cases b <;> rfl, ih]
      rfl

theorem lst_dbl (u : Word) : lst pairDelta 0 (u.flatMap fun b => [b, b]) = 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [List.flatMap_cons, lst_append, show lst pairDelta 0 [b, b] = 0 by cases b <;> rfl, ih]

theorem lrun_fst_dbl (u : Word) : lrun pairDelta pairOutFst 0 (u.flatMap fun b => [b, b]) = u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [List.flatMap_cons, lrun_append, show lst pairDelta 0 [b, b] = 0 by cases b <;> rfl, ih]
      cases b <;> rfl

theorem lrun_snd_dbl (u : Word) :
    lrun pairDelta pairOutSnd 0 (u.flatMap fun b => [b, b]) = [] := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [List.flatMap_cons, lrun_append, show lst pairDelta 0 [b, b] = 0 by cases b <;> rfl, ih]
      cases b <;> rfl

/-- **The first projection undoes the pairing.** -/
theorem fstOf_pairW (u v : Word) : fstOf (pairW u v) = u := by
  rw [fstOf, pairW, lrun_append, lrun_append, lst_dbl, lrun_fst_dbl, lst_append, lst_dbl,
    show lst pairDelta 0 [true, false] = 3 from rfl, lrun_fst_tail,
    show lrun pairDelta pairOutFst 0 [true, false] = [] from rfl]
  simp

/-- **The second projection undoes the pairing.** -/
theorem sndOf_pairW (u v : Word) : sndOf (pairW u v) = v := by
  rw [sndOf, pairW, lrun_append, lrun_append, lst_dbl, lrun_snd_dbl, lst_append, lst_dbl,
    show lst pairDelta 0 [true, false] = 3 from rfl, lrun_snd_tail,
    show lrun pairDelta pairOutSnd 0 [true, false] = [] from rfl]
  simp

/-! ### Every word is short in terms of its projections -/

/-- The slack of a state in the length bound. -/
def pairSlack : ℕ → ℕ
  | 0 => 3
  | 3 => 0
  | _ => 2

theorem length_le_of_proj_aux : ∀ (x : Word) (s : ℕ), s < 4 →
    x.length ≤ 2 * (lrun pairDelta pairOutFst s x).length + pairSlack s
      + (lrun pairDelta pairOutSnd s x).length := by
  intro x
  induction x with
  | nil => intro s _; simp [lrun, pairSlack]
  | cons b x ih =>
      intro s hs
      have hrec := ih (pairDelta s b) (pairDelta_lt s b)
      rw [lrun, lrun, List.length_cons, List.length_append, List.length_append]
      interval_cases s <;> cases b <;>
        (try simp only [pairDelta, pairOutFst, pairOutSnd, pairSlack, List.length_nil,
          List.length_cons] at hrec ⊢) <;> omega

/-- **A word is no longer than `2 * |fst| + 3 + |snd|`**: the pairing is essentially the only way
a word can look to the two projections. -/
theorem length_le_of_proj (x : Word) :
    x.length ≤ 2 * (fstOf x).length + 3 + (sndOf x).length := by
  have := length_le_of_proj_aux x 0 (by norm_num)
  simpa [fstOf, sndOf, pairSlack] using this

/-! ### The projections are Cobham functions -/

/-- The output block of the first projection as a Cobham term. -/
def pairOutFstT (s : ℕ) (b : Bool) : Cob := Cob.pre (pairOutFst s b) .empty

/-- The output block of the second projection as a Cobham term. -/
def pairOutSndT (s : ℕ) (b : Bool) : Cob := Cob.pre (pairOutSnd s b) .empty

/-- The Cobham term computing the first projection. -/
def fstTerm : Cob := lrunTerm 4 pairDelta pairOutFstT 1

/-- The Cobham term computing the second projection. -/
def sndTerm : Cob := lrunTerm 4 pairDelta pairOutSndT 1

theorem eval_fstTerm (x : Word) : fstTerm.eval [x, []] = fstOf x := by
  have hK : ∀ s b, ((pairOutFstT s b).eval [([] : Word)]).length ≤ 1 + ([] : Word).length := by
    intro s b
    match s, b with
    | 1, false => simp [pairOutFstT, pairOutFst]
    | 2, true => simp [pairOutFstT, pairOutFst]
    | 0, false => simp [pairOutFstT, pairOutFst]
    | 0, true => simp [pairOutFstT, pairOutFst]
    | 1, true => simp [pairOutFstT, pairOutFst]
    | 2, false => simp [pairOutFstT, pairOutFst]
    | (n + 3), b => cases b <;> simp [pairOutFstT, pairOutFst]
  have h := eval_lrunTerm (m := 4) (K := 1) (by norm_num) pairDelta_lt pairOutFstT [] hK x
  rw [fstTerm, h, fstOf]
  congr 1
  funext s b
  simp [pairOutFstT]

theorem eval_sndTerm (x : Word) : sndTerm.eval [x, []] = sndOf x := by
  have hK : ∀ s b, ((pairOutSndT s b).eval [([] : Word)]).length ≤ 1 + ([] : Word).length := by
    intro s b
    by_cases h : s = 3 <;> simp [pairOutSndT, pairOutSnd, h]
  have h := eval_lrunTerm (m := 4) (K := 1) (by norm_num) pairDelta_lt pairOutSndT [] hK x
  rw [sndTerm, h, sndOf]
  congr 1
  funext s b
  simp [pairOutSndT]

/-! ### `NP` is closed under intersection -/

/-- **`NP` is closed under intersection**: the witness is the pairing of the two witnesses, and
the verifier runs each verifier on the corresponding projection. -/
theorem InNP.inter {L₁ L₂ : Language} (h₁ : InNP L₁) (h₂ : InNP L₂) :
    InNP (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨v₁, p₁, hpoly₁, hmono₁, hbound₁, hchar₁⟩ := h₁
  obtain ⟨v₂, p₂, hpoly₂, hmono₂, hbound₂, hchar₂⟩ := h₂
  set wfst : Cob := .comp fstTerm [.proj 1, .empty] with hwfst
  set wsnd : Cob := .comp sndTerm [.proj 1, .empty] with hwsnd
  set v : Cob := .comp .andC [.comp v₁ [.proj 0, wfst], .comp v₂ [.proj 0, wsnd]] with hv
  have hfst : ∀ x w : Word, wfst.eval [x, w] = fstOf w := by
    intro x w
    simp only [hwfst, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero, Cob.eval_empty]
    exact eval_fstTerm w
  have hsnd : ∀ x w : Word, wsnd.eval [x, w] = sndOf w := by
    intro x w
    simp only [hwsnd, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero, Cob.eval_empty]
    exact eval_sndTerm w
  have hacc : ∀ x w : Word,
      (v.eval [x, w] ≠ []) ↔ (v₁.eval [x, fstOf w] ≠ [] ∧ v₂.eval [x, sndOf w] ≠ []) := by
    intro x w
    simp only [hv, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, Cob.eval_andC, hfst x w, hsnd x w]
    by_cases h : v₁.eval [x, fstOf w] = []
    · simp [h]
    · simp [h]
  refine ⟨v, fun n => 2 * p₁ n + 3 + p₂ n, ?_, ?_, ?_, ?_⟩
  · have hsum : PolyBound (fun n => p₁ n + p₁ n + 3 + p₂ n) :=
      ((hpoly₁.add hpoly₁).add (polyBound_const 3)).add hpoly₂
    exact hsum.mono (fun n => by omega)
  · intro m n hmn
    have hm₁ := hmono₁ hmn
    have hm₂ := hmono₂ hmn
    change 2 * p₁ m + 3 + p₂ m ≤ 2 * p₁ n + 3 + p₂ n
    omega
  · intro x w hw
    obtain ⟨ha₁, ha₂⟩ := (hacc x w).1 hw
    have h₁ := hbound₁ x _ ha₁
    have h₂ := hbound₂ x _ ha₂
    have hlen := length_le_of_proj w
    change w.length ≤ 2 * p₁ x.length + 3 + p₂ x.length
    omega
  · intro x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      obtain ⟨w₁, hw₁⟩ := (hchar₁ x).1 hx₁
      obtain ⟨w₂, hw₂⟩ := (hchar₂ x).1 hx₂
      refine ⟨pairW w₁ w₂, (hacc x _).2 ?_⟩
      rw [fstOf_pairW, sndOf_pairW]
      exact ⟨hw₁, hw₂⟩
    · rintro ⟨w, hw⟩
      obtain ⟨ha₁, ha₂⟩ := (hacc x w).1 hw
      exact ⟨(hchar₁ x).2 ⟨_, ha₁⟩, (hchar₂ x).2 ⟨_, ha₂⟩⟩

end Complexity
