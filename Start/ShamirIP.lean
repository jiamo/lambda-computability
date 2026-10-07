/-
**`PSPACE ⊆ IP` and `TQBF ∈ IP`** (task-board rows `M21-TQBF-IN-IP` and `M21-PSPACE-SUBSET-IP`).

The verifier `Complexity.Shamir.shamirV` decides `TQBF` on codes of closed formulas
(`Complexity.Shamir.shamirV_promise`, from `Start/ShamirSoundness.lean` and
`Start/ShamirComplete.lean`).  The reduction of a polynomial-space language to `TQBF`
(`Start/QbfCobReduction.lean`) always writes the code of a closed formula
(`Complexity.Qbf.QBF.closed_machineFk`), so running `shamirV` on the output of the reduction
(`Complexity.Verifier.precomp`) is an interactive proof for the language
(`Complexity.Shamir.pspace_subset_ip`); in particular for `TQBF` itself
(`Complexity.Shamir.tqbf_in_ip`).
-/

import Start.ShamirComplete
import Start.QbfEvalCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf Complexity.Space

/-- **Shamir's verifier decides `TQBF` on closed formulas**: on a true closed formula some prover
is accepted with probability `1 ≥ 2/3`, on a false one every prover with probability `≤ 1/3`. -/
theorem shamirV_promise (q : QBF) (hc : q.Closed) :
    (TQBF q → ∃ P : Prover, (2 : ℚ) / 3 ≤ shamirV.accProb P (QBF.enc q)) ∧
    (¬ TQBF q → ∀ P : Prover, shamirV.accProb P (QBF.enc q) ≤ 1 / 3) := by
  refine ⟨fun ht => ?_, fun hf P => accProb_shamirV_le q hc hf P⟩
  obtain ⟨P, hP⟩ := accProb_shamirV_complete q hc ht
  exact ⟨P, by rw [hP]; norm_num⟩

/-- **`PSPACE ⊆ IP`**: every language decidable in polynomial space has an interactive proof. -/
theorem pspace_subset_ip {L : Language} (h : Space.PSPACE L) : IP L := by
  obtain ⟨s, hs, M, hwf, hsp, hL⟩ := Space.npspace_of_pspace h
  obtain ⟨a, d, ha⟩ := hs
  refine ⟨shamirV.precomp (QBF.redTerm M a d), fun x => ?_⟩
  have hspx : M.SpaceBoundedOn x (QBF.spaceOf a d x.length) := by
    intro n c hc
    have := hsp x n c hc
    have hb := ha x.length
    simp only [QBF.spaceOf]
    omega
  have hk : savitchDepth M x (QBF.spaceOf a d x.length)
      ≤ QBF.kBound M (QBF.spaceOf a d) x.length :=
    QBF.savitchDepth_le_kBound M (QBF.spaceOf a d) x
  have hiff : L x ↔ TQBF (QBF.machineFk M x (QBF.spaceOf a d x.length)
      (QBF.kBound M (QBF.spaceOf a d) x.length)) := by
    rw [QBF.tqbf_machineFk_iff hwf hspx (QBF.spaceOf_pos a d x.length) hk]
    exact hL x
  have hpro := shamirV_promise _ (QBF.closed_machineFk M x (QBF.spaceOf a d x.length)
    (QBF.kBound M (QBF.spaceOf a d) x.length))
  simp only [Verifier.accProb_precomp, QBF.eval_redTerm M a d hwf.1 x]
  exact ⟨fun hx => hpro.1 (hiff.1 hx), fun hx => hpro.2 (fun h => hx (hiff.2 h))⟩

/-- **`TQBF` has an interactive proof.** -/
theorem tqbf_in_ip : IP tqbfLang := pspace_subset_ip tqbf_pspace

end Complexity.Shamir
