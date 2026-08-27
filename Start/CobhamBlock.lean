/-
**Block-emitting recursions are Cobham functions.**

`Start/CobhamTransducer.lean` shows that a finite-state transducer — one that emits a block of
bounded size at every position — is a Cobham function.  Writing a *formula* out of a description
needs more: the block emitted at a position may be as long as the input (it contains unary variable
indices), and it depends on the whole token that starts there and on how many tokens have been
passed already.

This module provides that scheme.  A **block-emitting recursion** is given by a finite-state
control `δ`, a counter increment `inc` and, for every state and bit, a Cobham term computing the
block from the suffix, from the counter in unary and from a parameter.  The emitted blocks may grow
linearly with the suffix, so the whole output is quadratic — still polynomial, which is all that is
needed.

Main definitions:

* `Complexity.rcnt`, `Complexity.brun` — the counter and the output of a block-emitting recursion;
* `Complexity.cntTerm`, `Complexity.blkRunTerm` — the Cobham terms;
* `Complexity.Cob.leadOnes`, `Complexity.Cob.dropOnes` — reading a unary field off the front of a
  word.

Main results:

* `Complexity.eval_cntTerm` — the counter is a Cobham function;
* `Complexity.eval_blkRunTerm` — **a block-emitting recursion is a Cobham function**;
* `Complexity.Cob.eval_leadOnes`, `Complexity.Cob.eval_dropOnes` — reading a unary field is a
  Cobham function.
-/

import Start.CobhamTransducer

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Reading a unary field off the front of a word -/

/-- The number of leading ones of a word. -/
def lead1 : Word → ℕ
  | true :: x => lead1 x + 1
  | _ => 0

theorem lead1_le (x : Word) : lead1 x ≤ x.length := by
  induction x with
  | nil => simp [lead1]
  | cons b x ih =>
      cases b
      · simp [lead1]
      · simp only [lead1, List.length_cons]; omega

/-- `1^n`, where `n` is the number of leading ones of the argument. -/
def Cob.leadOnes : Cob :=
  .bRec .empty .empty (.comp (.app true) [.proj 1]) (.comp .smash [.proj 0, Cob.trueC])

@[simp] theorem Cob.eval_leadOnes (x : Word) (rest : List Word) :
    Cob.leadOnes.eval (x :: rest) = List.replicate (lead1 x) true := by
  induction x with
  | nil => simp [Cob.leadOnes, lead1]
  | cons b x ih =>
      rw [Cob.leadOnes, Cob.eval_bRec_cons, ← Cob.leadOnes, ih]
      cases b
      · simp [lead1]
      · have hle : (true :: List.replicate (lead1 x) true).length ≤ (x.length + 1) * 1 := by
          simpa using Nat.succ_le_succ (lead1_le x)
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app,
          Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, Cob.eval_smash,
          Cob.eval_trueC, List.length_replicate, List.length_cons, List.length_nil]
        rw [List.take_of_length_le (by simpa using hle), lead1, List.replicate_succ]
        simp

/-- A word with its leading ones removed. -/
def drop1 : Word → Word
  | true :: x => drop1 x
  | x => x

theorem length_drop1 (x : Word) : (drop1 x).length ≤ x.length := by
  induction x with
  | nil => simp [drop1]
  | cons b x ih =>
      cases b
      · simp [drop1]
      · simp only [drop1, List.length_cons]; omega

/-- The argument with its leading ones removed. -/
def Cob.dropOnes : Cob :=
  .bRec .empty (.comp (.app false) [.proj 0]) (.proj 1) (.comp .smash [.proj 0, Cob.trueC])

@[simp] theorem Cob.eval_dropOnes (x : Word) (rest : List Word) :
    Cob.dropOnes.eval (x :: rest) = drop1 x := by
  induction x with
  | nil => simp [Cob.dropOnes, drop1]
  | cons b x ih =>
      rw [Cob.dropOnes, Cob.eval_bRec_cons, ← Cob.dropOnes, ih]
      cases b
      · simp only [Bool.false_eq_true, if_false, Cob.eval_comp, List.map_cons, List.map_nil,
          Cob.eval_app, Cob.eval_proj, List.getD_cons_zero, Cob.eval_smash, Cob.eval_trueC,
          List.length_replicate, List.length_cons]
        rw [List.take_of_length_le (by simp)]
        rfl
      · simp only [Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero,
          Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_trueC,
          List.length_replicate, List.length_cons]
        rw [List.take_of_length_le (by simpa using le_trans (length_drop1 x) (Nat.le_succ _))]
        rfl

/-- The argument with its first bit removed. -/
def Cob.tail : Cob := .bRec .empty (.proj 0) (.proj 0) (.proj 0)

@[simp] theorem Cob.eval_tail (x : Word) (rest : List Word) :
    Cob.tail.eval (x :: rest) = x.tail := by
  cases x with
  | nil => simp [Cob.tail]
  | cons b x =>
      rw [Cob.tail, Cob.eval_bRec_cons]
      cases b <;> simp

/-! ### The counter -/

/-- The counter of a block-emitting recursion: the increments accumulated over the word, each
increment depending on the state of the suffix and on the current bit. -/
def rcnt (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) : Word → ℕ
  | [] => 0
  | b :: x => inc (rst δ 0 x) b + rcnt δ inc x

theorem rcnt_le (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) {Ki : ℕ} (hi : ∀ s b, inc s b ≤ Ki)
    (x : Word) : rcnt δ inc x ≤ x.length * Ki := by
  induction x with
  | nil => simp [rcnt]
  | cons b x ih =>
      have := hi (rst δ 0 x) b
      simp only [rcnt, List.length_cons]
      calc inc (rst δ 0 x) b + rcnt δ inc x ≤ Ki + x.length * Ki := Nat.add_le_add this ih
        _ = (x.length + 1) * Ki := by ring

/-- The step of the recursion computing the counter. -/
def cntStep (m : ℕ) (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (b : Bool) : Cob :=
  Cob.tableSel ((List.range m).map fun s => Cob.pre (List.replicate (inc s b) true) (.proj 1))
    (.comp (fstStTerm m δ) [.proj 0])

/-- The Cobham term computing `1^{rcnt δ inc x}`. -/
def cntTerm (m : ℕ) (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (Ki : ℕ) : Cob :=
  .bRec .empty (cntStep m δ inc false) (cntStep m δ inc true)
    (.comp .smash [.proj 0, Cob.pre (List.replicate Ki true) .empty])

theorem eval_cntStep {m : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    (inc : ℕ → Bool → ℕ) (b : Bool) (x r : Word) (rest : List Word) :
    (cntStep m δ inc b).eval (x :: r :: rest)
      = List.replicate (inc (rst δ 0 x) b) true ++ r := by
  have hst : ((Cob.comp (fstStTerm m δ) [Cob.proj 0]).eval (x :: r :: rest))
      = List.replicate (rst δ 0 x) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
    exact eval_fstStTerm hm hδ x _
  rw [cntStep, Cob.eval_tableSel _ _ _ (rst δ 0 x) hst]
  have hget : (((List.range m).map fun s =>
      Cob.pre (List.replicate (inc s b) true) (Cob.proj 1)).getD (rst δ 0 x) .empty)
      = Cob.pre (List.replicate (inc (rst δ 0 x) b) true) (.proj 1) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (rst_lt hm hδ x)]
    rfl
  rw [hget]
  simp

/-- **The counter of a block-emitting recursion is a Cobham function.** -/
theorem eval_cntTerm {m Ki : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    {inc : ℕ → Bool → ℕ} (hi : ∀ s b, inc s b ≤ Ki) (x : Word) (rest : List Word) :
    (cntTerm m δ inc Ki).eval (x :: rest) = List.replicate (rcnt δ inc x) true := by
  induction x with
  | nil => simp [cntTerm, rcnt]
  | cons b x ih =>
      rw [cntTerm, Cob.eval_bRec_cons, ← cntTerm, ih]
      have hstep : ∀ c : Bool,
          (cntStep m δ inc c).eval (x :: List.replicate (rcnt δ inc x) true :: rest)
            = List.replicate (inc (rst δ 0 x) c + rcnt δ inc x) true := by
        intro c
        rw [eval_cntStep hm hδ inc c x _ rest, ← List.replicate_add]
      have hbd : ((Cob.comp .smash [Cob.proj 0,
          Cob.pre (List.replicate Ki true) Cob.empty]).eval ((b :: x) :: rest)).length
          = (x.length + 1) * Ki := by
        simp
      have hle : (List.replicate (inc (rst δ 0 x) b + rcnt δ inc x) true).length
          ≤ ((Cob.comp .smash [Cob.proj 0,
              Cob.pre (List.replicate Ki true) Cob.empty]).eval ((b :: x) :: rest)).length := by
        rw [hbd]
        have h₁ := hi (rst δ 0 x) b
        have h₂ := rcnt_le δ inc hi x
        simp only [List.length_replicate]
        calc inc (rst δ 0 x) b + rcnt δ inc x ≤ Ki + x.length * Ki := Nat.add_le_add h₁ h₂
          _ = (x.length + 1) * Ki := by ring
      cases b
      · rw [if_neg (by simp), hstep false, List.take_of_length_le hle]
        rfl
      · rw [if_pos rfl, hstep true, List.take_of_length_le hle]
        rfl

/-! ### The block-emitting recursion -/

/-- The output of a block-emitting recursion: at every position the block determined by the state
of the suffix, the current bit, the suffix itself and the counter of the suffix. -/
def brun (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (blk : ℕ → Bool → Word → ℕ → Word) :
    Word → Word
  | [] => []
  | b :: x => blk (rst δ 0 x) b x (rcnt δ inc x) ++ brun δ inc blk x

theorem length_brun (δ : ℕ → Bool → ℕ) {inc : ℕ → Bool → ℕ}
    (blk : ℕ → Bool → Word → ℕ → Word) {K L Ki : ℕ} (hi : ∀ s b, inc s b ≤ Ki)
    (hb : ∀ s b y c, c ≤ y.length * Ki → (blk s b y c).length ≤ K * (y.length + L + 1))
    (x : Word) :
    (brun δ inc blk x).length ≤ x.length * (K * (x.length + L + 1)) := by
  induction x with
  | nil => simp [brun]
  | cons b x ih =>
      have h₁ := hb (rst δ 0 x) b x (rcnt δ inc x) (rcnt_le δ inc hi x)
      have hmono : K * (x.length + L + 1) ≤ K * ((b :: x).length + L + 1) := by
        apply Nat.mul_le_mul_left
        simp
      have h₂ : x.length * (K * (x.length + L + 1))
          ≤ x.length * (K * ((b :: x).length + L + 1)) := Nat.mul_le_mul_left _ hmono
      simp only [brun, List.length_append, List.length_cons]
      calc (blk (rst δ 0 x) b x (rcnt δ inc x)).length + (brun δ inc blk x).length
          ≤ K * ((b :: x).length + L + 1) + x.length * (K * ((b :: x).length + L + 1)) :=
            Nat.add_le_add (le_trans h₁ hmono) (le_trans ih h₂)
        _ = (x.length + 1) * (K * ((b :: x).length + L + 1)) := by
            simp only [List.length_cons]; ring

/-- The block emitted at a position, selected by the state of the suffix. -/
def blkSel (m : ℕ) (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (blkT : ℕ → Bool → Cob) (Ki : ℕ)
    (b : Bool) : Cob :=
  Cob.tableSel
    ((List.range m).map fun s =>
      .comp (blkT s b) [.proj 0, .comp (cntTerm m δ inc Ki) [.proj 0], .proj 2])
    (.comp (fstStTerm m δ) [.proj 0])

/-- The step of a block-emitting recursion. -/
def blkStep (m : ℕ) (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (blkT : ℕ → Bool → Cob) (Ki : ℕ)
    (b : Bool) : Cob :=
  .comp Cob.concat [blkSel m δ inc blkT Ki b, .proj 1]

/-- The Cobham term of a block-emitting recursion, with a parameter word as second argument. -/
def blkRunTerm (m : ℕ) (δ : ℕ → Bool → ℕ) (inc : ℕ → Bool → ℕ) (blkT : ℕ → Bool → Cob)
    (Ki K : ℕ) : Cob :=
  .bRec .empty (blkStep m δ inc blkT Ki false) (blkStep m δ inc blkT Ki true)
    (.comp .smash
      [.comp .smash [.proj 0, Cob.pre (List.replicate K true) .empty],
        .comp Cob.concat [.comp (.app true) [.proj 0], .proj 1]])

theorem eval_blkSel {m Ki : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    {inc : ℕ → Bool → ℕ} (hi : ∀ s b, inc s b ≤ Ki) (blkT : ℕ → Bool → Cob) (b : Bool)
    (x r p : Word) :
    (blkSel m δ inc blkT Ki b).eval [x, r, p]
      = (blkT (rst δ 0 x) b).eval [x, List.replicate (rcnt δ inc x) true, p] := by
  have hst : ((Cob.comp (fstStTerm m δ) [Cob.proj 0]).eval [x, r, p])
      = List.replicate (rst δ 0 x) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
    exact eval_fstStTerm hm hδ x []
  rw [blkSel, Cob.eval_tableSel _ _ _ (rst δ 0 x) hst]
  have hget : (((List.range m).map fun s =>
      Cob.comp (blkT s b) [Cob.proj 0, Cob.comp (cntTerm m δ inc Ki) [Cob.proj 0], Cob.proj 2]).getD
      (rst δ 0 x) .empty)
      = Cob.comp (blkT (rst δ 0 x) b)
          [.proj 0, .comp (cntTerm m δ inc Ki) [.proj 0], .proj 2] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (rst_lt hm hδ x)]
    rfl
  rw [hget]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    List.getD_cons_succ]
  rw [eval_cntTerm hm hδ hi x []]

/-- **A block-emitting recursion is a Cobham function.** -/
theorem eval_blkRunTerm {m Ki K : ℕ} {δ : ℕ → Bool → ℕ} (hm : 0 < m) (hδ : ∀ s b, δ s b < m)
    {inc : ℕ → Bool → ℕ} (hi : ∀ s b, inc s b ≤ Ki) (blkT : ℕ → Bool → Cob)
    {blk : ℕ → Bool → Word → ℕ → Word} (p : Word)
    (hblk : ∀ s b y c, (blkT s b).eval [y, List.replicate c true, p] = blk s b y c)
    (hb : ∀ s b y c, c ≤ y.length * Ki → (blk s b y c).length ≤ K * (y.length + p.length + 1))
    (x : Word) :
    (blkRunTerm m δ inc blkT Ki K).eval [x, p] = brun δ inc blk x := by
  induction x with
  | nil => simp [blkRunTerm, brun]
  | cons b x ih =>
      rw [blkRunTerm, Cob.eval_bRec_cons, ← blkRunTerm, ih]
      have hstep : ∀ c : Bool, (blkStep m δ inc blkT Ki c).eval [x, brun δ inc blk x, p]
          = blk (rst δ 0 x) c x (rcnt δ inc x) ++ brun δ inc blk x := by
        intro c
        rw [blkStep]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_proj,
          List.getD_cons_succ, List.getD_cons_zero]
        rw [eval_blkSel hm hδ hi blkT c x (brun δ inc blk x) p, hblk]
      have hbd : ((Cob.comp .smash
          [Cob.comp .smash [Cob.proj 0, Cob.pre (List.replicate K true) Cob.empty],
            Cob.comp Cob.concat [Cob.comp (.app true) [Cob.proj 0], Cob.proj 1]]).eval
          ((b :: x) :: [p])).length = ((x.length + 1) * K) * (x.length + 2 + p.length) := by
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
          List.getD_cons_zero, List.getD_cons_succ, Cob.eval_pre, Cob.eval_empty, Cob.eval_concat,
          Cob.eval_app, List.append_nil, List.length_replicate, List.length_append,
          List.length_cons]
      have hle : (blk (rst δ 0 x) b x (rcnt δ inc x) ++ brun δ inc blk x).length
          ≤ ((Cob.comp .smash
              [Cob.comp .smash [Cob.proj 0, Cob.pre (List.replicate K true) Cob.empty],
                Cob.comp Cob.concat [Cob.comp (.app true) [Cob.proj 0], Cob.proj 1]]).eval
              ((b :: x) :: [p])).length := by
        rw [hbd, List.length_append]
        have h₁ : (blk (rst δ 0 x) b x (rcnt δ inc x)).length ≤ K * (x.length + p.length + 1) :=
          hb _ _ _ _ (rcnt_le δ inc hi x)
        have h₂ : (brun δ inc blk x).length ≤ x.length * (K * (x.length + p.length + 1)) :=
          length_brun δ blk hi hb x
        calc (blk (rst δ 0 x) b x (rcnt δ inc x)).length + (brun δ inc blk x).length
            ≤ K * (x.length + p.length + 1) + x.length * (K * (x.length + p.length + 1)) :=
              Nat.add_le_add h₁ h₂
          _ = ((x.length + 1) * K) * (x.length + p.length + 1) := by ring
          _ ≤ ((x.length + 1) * K) * (x.length + 2 + p.length) :=
              Nat.mul_le_mul_left _ (by omega)
      cases b
      · rw [if_neg (by simp), hstep false, List.take_of_length_le hle]
        rfl
      · rw [if_pos rfl, hstep true, List.take_of_length_le hle]
        rfl

end Complexity
