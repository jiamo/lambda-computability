/-
**The verifier of Shamir's protocol plays the sum-check protocol** (towards task-board row
`M21-TQBF-IN-IP`).

On the code `x = enc q` of a closed formula, the transcript of the interaction of
`Complexity.Shamir.shamirV` with any prover, without its first record, is a transcript of the
form read by the machine of `Start/ShamirMachine.lean` (`Complexity.Shamir.foldl_stepT_eq`), so
by `Complexity.Shamir.sim` the verdict of the verifier is the verdict of a run of sum-check
(`Complexity.Shamir.accepts_eq_run`).

Main results:

* `Complexity.Shamir.accepts_eq_run` — the verdict of the verifier on coins `r` is the verdict of
  the sum-check run against the prover that reads the messages of the transcript, on the points
  decoded from the coin blocks `1, 2, …`.
-/

import Start.ShamirAsk
import Start.SumCheckReplay

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### The shape of the transcript -/

/-- The `k`-th message of the prover in the interaction whose questions are `vs`. -/
def mW (P : Prover) (M : ℕ) (vs : List ℕ) (k : ℕ) : Word :=
  (P ((vs.take k).foldl (stepT P M) [] ++ encMsg (un (vs.getD k 0)))).take M

theorem foldl_take_stepT (P : Prover) (M : ℕ) (vs : List ℕ) :
    ∀ k, k < vs.length →
      (vs.take (k + 1)).foldl (stepT P M) [] =
        encMsg (un (vs.getD 0 0)) ++ tr (mW P M vs) (fun j => vs.getD (j + 1) 0) 0 k ++
          encMsg (mW P M vs k)
  | 0, h => by
      obtain ⟨v, vs', rfl⟩ : ∃ v vs', vs = v :: vs' := List.exists_cons_of_length_pos h
      simp [stepT, mW, tr]
  | k + 1, h => by
      rw [List.take_add_one, List.foldl_append, foldl_take_stepT P M vs k (by omega),
        List.getElem?_eq_getElem h]
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, stepT]
      rw [tr_add]
      have hg : vs[k + 1] = vs.getD (k + 1) 0 := by simp [List.getD_eq_getElem?_getD, h]
      have hm : mW P M vs (k + 1) = (P ((vs.take (k + 1)).foldl (stepT P M) [] ++
          encMsg (un (vs.getD (k + 1) 0)))).take M := rfl
      rw [hm, foldl_take_stepT P M vs k (by omega), hg]
      simp [tr, List.append_assoc]

/-- **The transcript without its first record** is the transcript read by the machine: the
messages of the prover interleaved with the questions `vs₁, vs₂, …`. -/
theorem recSkip_foldl_stepT (P : Prover) (M : ℕ) (vs : List ℕ) {R : ℕ} (hR : R < vs.length) :
    recSkip (vs.foldl (stepT P M) []) =
      tr (mW P M vs) (fun j => vs.getD (j + 1) 0) 0 R ++
        (tr (mW P M vs) (fun j => vs.getD (j + 1) 0) R (vs.length - 1 - R) ++
          encMsg (mW P M vs (vs.length - 1))) := by
  have h := foldl_take_stepT P M vs (vs.length - 1) (by omega)
  rw [show vs.length - 1 + 1 = vs.length by omega, List.take_length] at h
  have ht := tr_add (mW P M vs) (fun j => vs.getD (j + 1) 0) 0 R (vs.length - 1 - R)
  rw [Nat.zero_add, show R + (vs.length - 1 - R) = vs.length - 1 by omega] at ht
  rw [h, List.append_assoc, recSkip_encMsg, ht, List.append_assoc]

/-! ### The verdict as a sum-check run -/

section Run

variable (q : QBF)

/-- The number of rounds of the sum-check run on `q`. -/
abbrev rdsOf : ℕ := (QBF.toOp (QBF.enc q).length q).rounds

theorem size_toOp_le :
    (QBF.toOp (QBF.enc q).length q).size ≤ ((QBF.enc q).length + 1) ^ 2 := by
  have h1 := QBF.size_toOp (QBF.enc q).length q
  have h2 := QBF.size_le_length_enc q
  calc _ ≤ ((QBF.enc q).length + 1) * q.size := h1
    _ ≤ ((QBF.enc q).length + 1) * ((QBF.enc q).length + 1) := by gcongr; omega
    _ = _ := by ring

theorem rdsOf_le : rdsOf q ≤ ((QBF.enc q).length + 1) ^ 2 :=
  (Op.rounds_le_size _).trans (size_toOp_le q)

/-- **The verdict of the verifier is the verdict of a sum-check run.** -/
theorem accepts_eq_run [Fact (primeOf (QBF.enc q)).Prime] (P : Prover) (r : Word) :
    shamirV.accepts P (QBF.enc q) r =
      (run (2 * (QBF.enc q).length)
        (idxStrat (primeOf (QBF.enc q)) (mW P (shamirV.maxMsg (QBF.enc q))
          (bvs (primeOf (QBF.enc q)) (8 * ((QBF.enc q).length + 1)) r
            (((QBF.enc q).length + 1) ^ 2 + 1))))
        (QBF.toOp (QBF.enc q).length q) (fun _ => 0) 1 []
        (pts (primeOf (QBF.enc q))
          (fun j => (bvs (primeOf (QBF.enc q)) (8 * ((QBF.enc q).length + 1)) r
            (((QBF.enc q).length + 1) ^ 2 + 1)).getD (j + 1) 0) 0 (rdsOf q))).1 := by
  have hlen : (bvs (primeOf (QBF.enc q)) (8 * ((QBF.enc q).length + 1)) r
      (((QBF.enc q).length + 1) ^ 2 + 1)).length = ((QBF.enc q).length + 1) ^ 2 + 1 := by
    simp [bvs]
  rw [accepts_shamirV, transcript_shamirV,
    recSkip_foldl_stepT _ _ _ (R := rdsOf q) (by rw [hlen]; have := rdsOf_le q; omega)]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact sim _ _ _ _ _ (QBF.varBound_le_length_enc q) (size_toOp_le q) _

end Run

end Complexity.Shamir
