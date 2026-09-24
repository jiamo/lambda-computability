/-
**The reduction with the depth of the recursion as a parameter.**

`Complexity.Qbf.QBF.machineF` runs the midpoint recursion to the depth
`Complexity.Space.savitchDepth`, a `Nat.clog` of the number of configurations.  That depth is
awkward for a machine that has to *write* the formula: a polynomial-time transducer would have to
compute a logarithm of an exponential.  It is also more than is needed: running the recursion
*deeper* than necessary changes nothing, because reachability within `2 ^ k` steps only grows
with `k`, and the reduction never uses the bound in the direction that would break.

This module therefore parameterises the reduction by the depth, `Complexity.Qbf.QBF.machineFk`,
and proves it correct for every depth at or above `savitchDepth`.  The reduction can then be
instantiated at a depth that is a plain polynomial in the length of the input.

Main definitions:

* `Complexity.Qbf.QBF.machineFk` — the reduction at a given depth.

Main results:

* `Complexity.Qbf.QBF.eval_machineFk` — **the reduction is correct at any depth at or above
  `savitchDepth`**;
* `Complexity.Qbf.QBF.closed_machineFk` — it is closed;
* `Complexity.Qbf.QBF.tqbf_machineFk_iff` — **it is a true closed formula exactly when the machine
  accepts the input.**
-/

import Mathlib
import Start.QbfClosed

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity.Space Complexity.Reach

variable {M : Machine} {x : List Bool} {s : ℕ}

/-! ### Reachability bounds only grow -/

theorem reachLe_mono {C : Type} {r : C → C → Prop} {k k' : ℕ} (hk : k ≤ k') {a b : C}
    (h : Reach.reachLe r k a b) : Reach.reachLe r k' a b := by
  obtain ⟨n, hn, hsteps⟩ := h
  exact ⟨n, le_trans hn (Nat.pow_le_pow_right (by norm_num) hk), hsteps⟩

/-- **Acceptance is reachability in the padded graph within `2 ^ k` steps**, for any `k` at or
above `savitchDepth`. -/
theorem accepts_iff_reachLe_padStep_le (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) {k : ℕ}
    (hk : savitchDepth M x s ≤ k) :
    M.Accepts x ↔ ∃ e : Config, M.accept e.state = true ∧
      Reach.reachLe (padStep M x s) k (pad s init) e := by
  constructor
  · intro h
    obtain ⟨e, hacc, hr⟩ := (accepts_iff_reachLe_padStep hwf hsp).1 h
    exact ⟨e, hacc, reachLe_mono hk hr⟩
  · rintro ⟨e, hacc, n, -, hn⟩
    exact (accepts_iff_padStep hwf hsp).2 ⟨n, e, hn, hacc⟩

/-! ### The reduction at a given depth -/

/-- **The formula of the reduction, with the depth of the midpoint recursion as a parameter.** -/
def machineFk (M : Machine) (x : List Bool) (s k : ℕ) : QBF :=
  exBits 0 (cfgWidth M x s) (exBits (cfgWidth M x s) (cfgWidth M x s)
    (QBF.conj (QBF.conj (initF M x s 0) (accF M x s 1))
      (reachF (stepF M x s) (cfgWidth M x s) k 0 1 2)))

theorem machineFk_savitchDepth (M : Machine) (x : List Bool) (s : ℕ) :
    machineFk M x s (savitchDepth M x s) = machineF M x s := rfl

/-- **The reduction is correct at any depth at or above `savitchDepth`.** -/
theorem eval_machineFk (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) (hs : 0 < s) {k : ℕ}
    (hk : savitchDepth M x s ≤ k) (σ : ℕ → Bool) :
    (machineFk M x s k).eval σ = true ↔ M.Accepts x := by
  have hinit : Fits M x s (pad s init) := ⟨hwf.1, Nat.zero_le _, by simp, hs⟩
  have hblocks : ∀ w0 w1 : List Bool, w0.length = cfgWidth M x s →
      w1.length = cfgWidth M x s →
      blockVal (cfgWidth M x s)
          (setBits (setBits σ 0 w0) (cfgWidth M x s) w1) 0 = w0 ∧
        blockVal (cfgWidth M x s)
          (setBits (setBits σ 0 w0) (cfgWidth M x s) w1) 1 = w1 := by
    intro w0 w1 h0 h1
    have k1 : blockVal (cfgWidth M x s)
        (setBits (setBits σ 0 w0) (1 * cfgWidth M x s) w1) 1 = w1 :=
      blockVal_setBits_self _ _ 1 w1 h1
    have k0 : blockVal (cfgWidth M x s)
        (setBits (setBits σ 0 w0) (1 * cfgWidth M x s) w1) 0 =
          blockVal (cfgWidth M x s) (setBits σ 0 w0) 0 :=
      blockVal_setBits_of_ne _ _ 1 0 w1 h1 (by omega)
    have k00 : blockVal (cfgWidth M x s) (setBits σ (0 * cfgWidth M x s) w0) 0 = w0 :=
      blockVal_setBits_self _ _ 0 w0 h0
    rw [one_mul] at k1 k0
    rw [zero_mul] at k00
    exact ⟨by rw [k0, k00], k1⟩
  rw [machineFk, eval_exBits]
  constructor
  · rintro ⟨w0, hw0, h⟩
    rw [eval_exBits] at h
    obtain ⟨w1, hw1, h⟩ := h
    obtain ⟨hb0, hb1⟩ := hblocks w0 w1 hw0 hw1
    simp only [eval, Bool.and_eq_true] at h
    obtain ⟨⟨hi, ha⟩, hr⟩ := h
    rw [eval_initF, hb0] at hi
    rw [eval_accF, hb1] at ha
    obtain ⟨c, hfits, hacc, hcw⟩ := ha
    rw [eval_reachF (R := WordStep M x s) (fun τ u v => eval_stepF τ u v)
      (fun u v huv _ => (wordStep_length huv).2) _ _ _ _ _ (by omega) (by omega),
      hb0, hb1, hi, hcw, reachLe_wordStep_iff hinit hfits] at hr
    exact (accepts_iff_reachLe_padStep_le hwf hsp hk).2 ⟨c, hacc, hr⟩
  · intro hacc
    obtain ⟨c, haccc, hr⟩ := (accepts_iff_reachLe_padStep_le hwf hsp hk).1 hacc
    have hfits : Fits M x s c := by
      obtain ⟨n, -, hn⟩ := hr
      exact fits_of_steps_padStep hinit n hn
    refine ⟨cfgWord M x s (pad s init), by simp, ?_⟩
    rw [eval_exBits]
    refine ⟨cfgWord M x s c, by simp, ?_⟩
    obtain ⟨hb0, hb1⟩ := hblocks (cfgWord M x s (pad s init)) (cfgWord M x s c)
      (by simp) (by simp)
    simp only [eval, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [eval_initF, hb0]
    · rw [eval_accF, hb1]
      exact ⟨c, hfits, haccc, rfl⟩
    · rw [eval_reachF (R := WordStep M x s) (fun τ u v => eval_stepF τ u v)
        (fun u v huv _ => (wordStep_length huv).2) _ _ _ _ _ (by omega) (by omega),
        hb0, hb1, reachLe_wordStep_iff hinit hfits]
      exact hr

/-- **The reduction is closed at every depth.** -/
theorem closed_machineFk (M : Machine) (x : List Bool) (s k : ℕ) :
    (machineFk M x s k).Closed := by
  have hw := cfgWidth_pos M x s
  refine List.eq_nil_iff_forall_not_mem.2 fun i hi => ?_
  rw [machineFk] at hi
  obtain ⟨hi, h0⟩ := mem_free_exBits hi
  obtain ⟨hi, h1⟩ := mem_free_exBits hi
  have hbound : i < 2 * cfgWidth M x s := by
    simp only [free, List.mem_append] at hi
    have h2 : (0 + 1) * cfgWidth M x s = cfgWidth M x s := by ring
    have h3 : (1 + 1) * cfgWidth M x s = 2 * cfgWidth M x s := by ring
    rcases hi with (hi | hi) | hi
    · rcases mem_free_initF 0 i hi with h | h
      · omega
      · obtain ⟨-, h⟩ := h
        omega
    · rcases mem_free_accF 1 i hi with h | h
      · omega
      · obtain ⟨-, h⟩ := h
        omega
    · rcases mem_free_reachF (m := cfgWidth M x s) (stepF := stepF M x s)
        (fun u v j hj => mem_free_stepF u v j hj) k 0 1 2
        (by omega) (by omega) i hi with h | h | h
      · omega
      · obtain ⟨-, h⟩ := h
        omega
      · obtain ⟨-, h⟩ := h
        omega
  omega

/-- **The reduction is a true closed quantified Boolean formula exactly when the machine accepts
the input**, at every depth at or above `savitchDepth`. -/
theorem tqbf_machineFk_iff (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) (hs : 0 < s)
    {k : ℕ} (hk : savitchDepth M x s ≤ k) :
    TQBF (machineFk M x s k) ↔ M.Accepts x := by
  constructor
  · rintro ⟨-, h⟩
    exact (eval_machineFk hwf hsp hs hk _).1 h
  · intro h
    exact ⟨closed_machineFk M x s k, (eval_machineFk hwf hsp hs hk _).2 h⟩

end QBF

end Complexity.Qbf
