/-
**The verifier machine replays the sum-check protocol.**

`Start/ShamirMachine.lean` defines a machine on words that walks the code of a formula and reads
messages and points from a transcript.  This module proves that it computes the verdict of the
sum-check protocol `Complexity.Qbf.run` of `Start/SumCheck.lean` on the linearized operator tree
`Complexity.Qbf.QBF.toOp N q`, over the field `ZMod p`, for the prover that sends the `k`-th
message of the transcript at its `k`-th turn (`Complexity.Shamir.idxStrat`).

Main definitions:

* `Complexity.Shamir.tr` — the transcript of messages `msgW k` and points `ptN k`, as records;
* `Complexity.Shamir.pts` — the random points of the protocol, as field elements;
* `Complexity.Shamir.idxStrat` — the prover reading its messages off the transcript;
* `Complexity.Shamir.Replays` — the statement that the machine replays a node of the tree.

Main results:

Main result proved downstream:

* `Complexity.Shamir.sim` (in `Start/ShamirReplay.lean`) — the machine replays the protocol on
  every formula; this file contains the transcript, the points, the reading prover and the
  field-arithmetic facts that proof uses.
-/

import Start.ShamirMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### Arithmetic modulo a prime -/

section Arith

variable {p : ℕ} [hp : Fact p.Prime]

theorem p_pos : 0 < p := hp.out.pos

theorem cast_eq_iff {x y : ℕ} (hx : x < p) (hy : y < p) : ((x : ZMod p) = y) ↔ x = y := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem fadd_lt (a b : ℕ) : fadd p a b < p := Nat.mod_lt _ p_pos
theorem fmul_lt (a b : ℕ) : fmul p a b < p := Nat.mod_lt _ p_pos
theorem fsub_lt (a b : ℕ) : fsub p a b < p := Nat.mod_lt _ p_pos

theorem comb_lt (dis : Bool) (b c : ℕ) : comb p dis b c < p := by
  cases dis
  · exact fmul_lt _ _
  · exact fsub_lt _ _

theorem cast_fadd (a b : ℕ) : ((fadd p a b : ℕ) : ZMod p) = a + b := zmod_fAdd p a b
theorem cast_fmul (a b : ℕ) : ((fmul p a b : ℕ) : ZMod p) = a * b := zmod_fMul p a b
theorem cast_fsub (a : ℕ) {b : ℕ} (hb : b ≤ p) : ((fsub p a b : ℕ) : ZMod p) = a - b :=
  zmod_fSub a hb

theorem cast_comb (dis : Bool) {b c : ℕ} (hb : b ≤ p) (hc : c ≤ p) :
    ((comb p dis b c : ℕ) : ZMod p) =
      if dis then 1 - (1 - (b : ZMod p)) * (1 - (c : ZMod p)) else (b : ZMod p) * c := by
  cases dis
  · simp [comb, cast_fmul]
  · simp only [comb, if_true]
    rw [cast_fsub _ (fmul_lt _ _).le, cast_fmul, cast_fsub _ hb, cast_fsub _ hc]
    simp only [Nat.cast_one]

theorem cast_hornerN (x : ℕ) (cs : List ℕ) :
    ((hornerN x p cs : ℕ) : ZMod p) = evalL (cs.map fun c => (c : ZMod p)) (x : ZMod p) :=
  zmod_hornerN x p cs

theorem hornerN_lt (x : ℕ) : ∀ cs : List ℕ, hornerN x p cs < p
  | [] => p_pos
  | _ :: _ => Nat.mod_lt _ p_pos

end Arith

/-! ### Transcripts, points, the replaying prover -/

/-- The transcript of `n` messages and points from index `k` on: the records of `msgW k`, of
`ptN k` in unary, of `msgW (k + 1)`, … -/
def tr (msgW : ℕ → Word) (ptN : ℕ → ℕ) : ℕ → ℕ → Word
  | _, 0 => []
  | k, n + 1 => encMsg (msgW k) ++ (encMsg (un (ptN k)) ++ tr msgW ptN (k + 1) n)

/-- The random points of indices `k, …, k + r - 1`, as field elements. -/
def pts (p : ℕ) (ptN : ℕ → ℕ) (k r : ℕ) : List (ZMod p) :=
  (List.range' k r).map fun j => (ptN j : ZMod p)

/-- The prover that answers the `k`-th message of the transcript at its `k`-th turn (when the
history has length `2k`). -/
def idxStrat (p : ℕ) (msgW : ℕ → Word) : Strat (ZMod p) :=
  fun H _ _ => (decF (msgW (H.length / 2))).map fun c => (c : ZMod p)

/-- A list of naturals as a point of `ZMod p`. -/
def toF (p : ℕ) (a : List ℕ) : ℕ → ZMod p := fun j => ((a.getD j 0 : ℕ) : ZMod p)

section Lists

variable {p : ℕ} (ptN : ℕ → ℕ)

@[simp] theorem length_pts (k r : ℕ) : (pts p ptN k r).length = r := by simp [pts]

theorem pts_succ (k r : ℕ) : pts p ptN k (r + 1) = (ptN k : ZMod p) :: pts p ptN (k + 1) r := by
  simp [pts, List.range'_succ]

theorem pts_add (k a b : ℕ) : pts p ptN k (a + b) = pts p ptN k a ++ pts p ptN (k + a) b := by
  simp only [pts]; rw [← List.map_append, List.range'_append_1]

theorem toF_set {a : List ℕ} {i : ℕ} (hi : i < a.length) (x : ℕ) :
    toF p (a.set i x) = Function.update (toF p a) i (x : ZMod p) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [toF, List.getD_eq_getElem?_getD, hi]
  · simp [toF, Function.update_of_ne hj, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hj)]

end Lists

end Complexity.Shamir
