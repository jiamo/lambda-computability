/-
**The verifier of Shamir's protocol as a machine on words.**

The verdict of the sum-check protocol of `Start/SumCheck.lean` on the linearized operator tree
`Complexity.Qbf.QBF.toOp N q` of a formula is computed here by a small-step machine whose state is
eight binary words, and which reads the formula from its code `Complexity.Qbf.QBF.enc q` and the
messages of the prover and the random points from a transcript of records
(`Complexity.encMsg`).

The state (`Complexity.Shamir.St`) consists of

* `C` — the rest of the code (the current node is at its front);
* `J` — at a quantifier, the number of linearizations already performed, in unary;
* `A` — the current point, as a word of unary fields;
* `V` — the current claimed value, in unary;
* `S` — the stack of pending claims `(point, value)` for the right children of conjunctions and
  disjunctions, as a sequence of records;
* `B` — the rejection flag, `H` — the halting flag;
* `T` — the rest of the transcript: alternately a message and a point.

One step (`Complexity.Shamir.stepW`) processes one node of the operator tree: a variable (check the
claim and pop the stack), a negation, a conjunction or a disjunction (check the two values sent
and push the claim of the right child), one of the `N` linearizations generated at a quantifier,
or the quantifier itself.  All arithmetic is modulo `p` on naturals below `p`.

Main definitions:

* `Complexity.Shamir.St`, `Complexity.Shamir.stepW` — the machine;
* `Complexity.Shamir.tr` — a transcript of messages and points as a word of records;
* `Complexity.Shamir.idxStrat` — the strategy that answers the `k`-th message of the transcript
  at the `k`-th turn.

Main results:

* `Complexity.Shamir.stepW_halted` — halted states are fixed points;
* `Complexity.Shamir.sim` — **the machine replays the protocol**: started on the code of a formula,
  after `size (toOp N q)` steps it has either rejected (if the protocol run rejects) or popped its
  stack / halted without rejecting (if it accepts).
-/

import Start.SumCheckReplay
import Start.FieldCob
import Start.ShamirWords

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### The machine -/

/-- The state of the verifier. -/
structure St where
  /-- The rest of the code of the formula. -/
  C : Word
  /-- The number of linearizations already done at the current quantifier, in unary. -/
  J : Word
  /-- The current point, as unary fields. -/
  A : Word
  /-- The current claimed value, in unary. -/
  V : Word
  /-- The stack of pending claims, as records. -/
  S : Word
  /-- The rejection flag. -/
  B : Word
  /-- The rest of the transcript. -/
  T : Word
  /-- The halting flag. -/
  H : Word

/-- The bit at position `k` (false beyond the end). -/
def bit (k : ℕ) (C : Word) : Bool := (C.drop k).headD false

/-- Addition modulo `p`. -/
def fadd (p a b : ℕ) : ℕ := (a + b) % p

/-- Multiplication modulo `p`. -/
def fmul (p a b : ℕ) : ℕ := (a * b) % p

/-- Subtraction modulo `p` (for `b ≤ p`). -/
def fsub (p a b : ℕ) : ℕ := (a + (p - b)) % p

/-- The combination of two values at a conjunction or universal quantifier (`dis = false`) and at a
disjunction or existential quantifier (`dis = true`). -/
def comb (p : ℕ) (dis : Bool) (b c : ℕ) : ℕ :=
  if dis then fsub p 1 (fmul p (fsub p 1 b) (fsub p 1 c)) else fmul p b c

/-- Reject and halt. -/
def rej (s : St) : St := { s with B := [true], H := [true] }

/-- Pop the next pending claim, or halt if there is none. -/
def pop (s : St) : St :=
  if s.S = [] then { s with H := [true] }
  else { s with A := recGet s.S, V := recGet (recSkip s.S), S := recSkip (recSkip s.S) }

/-- **One step of the verifier**, with modulus `p`, `N` linearized variables and degree bound
`d`. -/
def stepW (p N d : ℕ) (s : St) : St :=
  if s.H ≠ [] then s else
  if bit 0 s.C = false then
    if bit 1 s.C = false then
      if fieldAt (lead1 (s.C.drop 2)) s.A = s.V.length then
        pop { s with C := (drop1 (s.C.drop 2)).tail }
      else rej s
    else { s with V := un (fsub p 1 s.V.length), C := s.C.drop 2 }
  else
    if bit 1 s.C = false then
      if dropFs 2 (trimW (recGet s.T)) = [] ∧ dropFs 1 (trimW (recGet s.T)) ≠ [] ∧
          comb p (bit 2 s.C) (fieldAt 0 (trimW (recGet s.T)) % p)
            (fieldAt 1 (trimW (recGet s.T)) % p) = s.V.length then
        { s with
          C := s.C.drop 3
          V := un (fieldAt 0 (trimW (recGet s.T)) % p)
          S := encMsg s.A ++ encMsg (un (fieldAt 1 (trimW (recGet s.T)) % p)) ++ s.S
          T := recSkip (recSkip s.T) }
      else rej s
    else
      if dropFs (d + 1) (trimW (recGet s.T)) ≠ [] then rej s else
      if s.J.length < N then
        if fadd p (fmul p (fieldAt s.J.length s.A) (hornerN 1 p (decF (recGet s.T))))
            (fmul p (fsub p 1 (fieldAt s.J.length s.A)) (hornerN 0 p (decF (recGet s.T)))) =
            s.V.length then
          { s with
            J := true :: s.J
            A := setField s.J.length ((recGet (recSkip s.T)).length % p) s.A
            V := un (hornerN ((recGet (recSkip s.T)).length % p) p (decF (recGet s.T)))
            T := recSkip (recSkip s.T) }
        else rej s
      else
        if comb p (bit 2 s.C) (hornerN 0 p (decF (recGet s.T)))
            (hornerN 1 p (decF (recGet s.T))) = s.V.length then
          { s with
            C := (drop1 (s.C.drop 3)).tail
            J := []
            A := setField (lead1 (s.C.drop 3)) ((recGet (recSkip s.T)).length % p) s.A
            V := un (hornerN ((recGet (recSkip s.T)).length % p) p (decF (recGet s.T)))
            T := recSkip (recSkip s.T) }
        else rej s

/-! ### Halting -/

theorem stepW_halted {p N d : ℕ} {s : St} (h : s.H ≠ []) : stepW p N d s = s := by
  rw [stepW, if_pos h]

theorem iterate_halted {p N d : ℕ} {s : St} (h : s.H ≠ []) :
    ∀ K, (stepW p N d)^[K] s = s
  | 0 => rfl
  | K + 1 => by rw [Function.iterate_succ_apply, stepW_halted h, iterate_halted h K]

@[simp] theorem rej_B (s : St) : (rej s).B = [true] := rfl
@[simp] theorem rej_H (s : St) : (rej s).H = [true] := rfl

/-- Once rejected, rejected for ever. -/
theorem iterate_rej {p N d : ℕ} (s : St) (K : ℕ) : ((stepW p N d)^[K] (rej s)).B ≠ [] := by
  rw [iterate_halted (by simp)]; simp

/-- A rejection reached within `K₀` steps persists. -/
theorem B_of_le {p N d : ℕ} {s : St} {K₀ : ℕ} (h : ((stepW p N d)^[K₀] s).B ≠ [])
    (hH : ((stepW p N d)^[K₀] s).H ≠ []) {K : ℕ} (hK : K₀ ≤ K) :
    ((stepW p N d)^[K] s).B ≠ [] := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_halted hH]
  exact h

/-! ### The step on each kind of node -/

section Steps

variable {p N d : ℕ}

theorem stepW_var {s : St} (hH : s.H = []) {i : ℕ} {r : Word}
    (hC : s.C = false :: false :: (QBF.unary i ++ r)) :
    stepW p N d s = if fieldAt i s.A = s.V.length then pop { s with C := r } else rej s := by
  simp [stepW, hH, hC, bit, EvalW.lead1_unary, EvalW.drop1_unary]

theorem stepW_neg {s : St} (hH : s.H = []) {X : Word} (hC : s.C = false :: true :: X) :
    stepW p N d s = { s with V := un (fsub p 1 s.V.length), C := X } := by
  simp [stepW, hH, hC, bit]

theorem stepW_bin {s : St} (hH : s.H = []) {b : Bool} {X : Word} (hC : s.C = true :: false :: b :: X)
    {w z T' : Word} (hT : s.T = encMsg w ++ (encMsg z ++ T')) :
    stepW p N d s =
      if dropFs 2 (trimW w) = [] ∧ dropFs 1 (trimW w) ≠ [] ∧
          comb p b (fieldAt 0 (trimW w) % p) (fieldAt 1 (trimW w) % p) = s.V.length then
        { s with
          C := X
          V := un (fieldAt 0 (trimW w) % p)
          S := encMsg s.A ++ encMsg (un (fieldAt 1 (trimW w) % p)) ++ s.S
          T := T' }
      else rej s := by
  simp only [stepW, hH, hC, hT, bit, ne_eq, not_true_eq_false, if_false, List.drop_zero,
    List.headD_cons, List.drop_succ_cons, recGet_encMsg, recSkip_encMsg]
  simp

theorem stepW_lin {s : St} (hH : s.H = []) {b : Bool} {X : Word}
    (hC : s.C = true :: true :: b :: X) {w z T' : Word} (hT : s.T = encMsg w ++ (encMsg z ++ T'))
    (hJ : s.J.length < N) :
    stepW p N d s =
      if dropFs (d + 1) (trimW w) = [] ∧
          fadd p (fmul p (fieldAt s.J.length s.A) (hornerN 1 p (decF w)))
            (fmul p (fsub p 1 (fieldAt s.J.length s.A)) (hornerN 0 p (decF w))) = s.V.length then
        { s with
          J := true :: s.J
          A := setField s.J.length (z.length % p) s.A
          V := un (hornerN (z.length % p) p (decF w))
          T := T' }
      else rej s := by
  simp only [stepW, hH, hC, hT, bit, ne_eq, not_true_eq_false, if_false, List.drop_zero,
    List.headD_cons, List.drop_succ_cons, recGet_encMsg, recSkip_encMsg, hJ, if_true,
    Bool.true_eq_false]
  by_cases h1 : dropFs (d + 1) (trimW w) = [] <;> simp [h1]

theorem stepW_quant {s : St} (hH : s.H = []) {b : Bool} {i : ℕ} {X : Word}
    (hC : s.C = true :: true :: b :: (QBF.unary i ++ X)) {w z T' : Word}
    (hT : s.T = encMsg w ++ (encMsg z ++ T')) (hJ : ¬ s.J.length < N) :
    stepW p N d s =
      if dropFs (d + 1) (trimW w) = [] ∧
          comb p b (hornerN 0 p (decF w)) (hornerN 1 p (decF w)) = s.V.length then
        { s with
          C := X
          J := []
          A := setField i (z.length % p) s.A
          V := un (hornerN (z.length % p) p (decF w))
          T := T' }
      else rej s := by
  simp only [stepW, hH, hC, hT, bit, ne_eq, not_true_eq_false, if_false, List.drop_zero,
    List.headD_cons, List.drop_succ_cons, recGet_encMsg, recSkip_encMsg, hJ,
    Bool.true_eq_false, EvalW.lead1_unary, EvalW.drop1_unary, List.tail_cons]
  by_cases h1 : dropFs (d + 1) (trimW w) = [] <;> simp [h1]

end Steps

end Complexity.Shamir
