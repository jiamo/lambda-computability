/-
# An instance of the Turing machine rule: the scanning machine

`Start/UniformTM.lean` proves that the language of a one-tape deterministic Turing machine, run
on a Cobham-computable tape for a Cobham-computable number of steps, is decided by a P-uniform
circuit family.  This module exercises that rule on a concrete machine, so that the rule is
visibly not vacuous: the machine that walks to the right and accepts as soon as it reads a `1`.

Main definitions:

* `Complexity.scanTM` — the scanning machine;
* `Complexity.scanW`, `Complexity.scanH` — the width of the tape and the deadline.

Main results:

* `Complexity.tmAccBy_scanTM` — **the scanning machine accepts exactly the words with a `true`
  bit**;
* `Complexity.tmLang_scanTM_eq_someOne` — its language is `Complexity.SomeOne`;
* `Complexity.pUniformDecidable_someOne_of_tm` — a third proof, through a Turing machine, that
  `Complexity.SomeOne` is decided by a P-uniform circuit family.
-/
import Start.UniformTM

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- **The scanning machine**: two states, the initial one `0` and the accepting one `1`; it never
changes the tape, always walks to the right, and enters the accepting state as soon as it reads
a `true`. -/
def scanTM : TuringMachine where
  Q := 2
  st := fun _ b => if b then 1 else 0
  wr := fun _ b => b
  mv := fun _ _ => true
  acc := fun s => decide (s = 1)
  Qpos := by omega
  st_lt := by intro _ b; cases b <;> simp

/-- The width of the tape: one more than the length of the input, so that the tape is never
empty. -/
def scanW (n : ℕ) : ℕ := n + 1

/-- The deadline: enough time for the machine to reach the last bit and for the accept signal to
travel back to the first cell. -/
def scanH (n : ℕ) : ℕ := 2 * n + 3

/-- The initial tape of the machine. -/
def scanTape (n : ℕ) (bit : ℕ → Bool) : ℕ → Bool := fun j => if j < n then bit j else false

theorem tmConf_scanTM_zero (W n : ℕ) (bit : ℕ → Bool) :
    tmConf scanTM W n bit 0 = (scanTape n bit, (if 0 < n then 0 else W), 0) := rfl

/-- **As long as it has read only `false` bits, the machine is in its initial state and its head
is at the position given by the elapsed time.** -/
theorem tmConf_scanTM (W n : ℕ) (bit : ℕ → Bool) (hn : 0 < n) :
    ∀ t, (∀ i, i < t → scanTape n bit i = false) → t ≤ W →
      tmConf scanTM W n bit t = (scanTape n bit, t, 0) := by
  intro t
  induction t with
  | zero =>
      intro _ _
      rw [tmConf_scanTM_zero, if_pos hn]
  | succ t ih =>
      intro hfalse hle
      have h1 := ih (fun i hi => hfalse i (by omega)) (by omega)
      have hbt : scanTape n bit t = false := hfalse t (by omega)
      have hhead : (tmConf scanTM W n bit t).2.1 < W := by
        rw [h1]
        change t < W
        omega
      have haccF : scanTM.acc (tmConf scanTM W n bit t).2.2 = false := by
        rw [h1]
        simp [scanTM]
      rw [tmConf_succ_of_step hhead haccF, h1]
      have htape : (fun j => if j = t then scanTM.wr 0 (scanTape n bit t)
          else scanTape n bit j) = scanTape n bit := by
        funext j
        by_cases hj : j = t
        · rw [if_pos hj, hj]
          rfl
        · rw [if_neg hj]
      exact Prod.ext htape (Prod.ext (by simp [scanTM]) (by simp [scanTM, hbt]))

/-- **On an all-`false` input the machine never leaves its initial state**, so it never
accepts. -/
theorem tmConf_scanTM_of_false (W n : ℕ) (bit : ℕ → Bool) (hb : ∀ i, i < n → bit i = false) :
    ∀ t, (tmConf scanTM W n bit t).2.2 = 0 ∧ ∀ j, (tmConf scanTM W n bit t).1 j = false := by
  intro t
  induction t with
  | zero =>
      refine ⟨rfl, fun j => ?_⟩
      rw [tmConf_scanTM_zero]
      by_cases hj : j < n
      · simpa [scanTape, hj] using hb j hj
      · simp [scanTape, hj]
  | succ t ih =>
      by_cases hstop : ¬ ((tmConf scanTM W n bit t).2.1 < W ∧
          scanTM.acc (tmConf scanTM W n bit t).2.2 = false)
      · rw [tmConf_succ_of_stop hstop]
        exact ih
      · rw [not_not] at hstop
        rw [tmConf_succ_of_step hstop.1 hstop.2]
        refine ⟨?_, fun j => ?_⟩
        · change scanTM.st (tmConf scanTM W n bit t).2.2
              ((tmConf scanTM W n bit t).1 (tmConf scanTM W n bit t).2.1) = 0
          rw [ih.2 ((tmConf scanTM W n bit t).2.1)]
          simp [scanTM]
        · change (if j = (tmConf scanTM W n bit t).2.1 then
              scanTM.wr (tmConf scanTM W n bit t).2.2
                ((tmConf scanTM W n bit t).1 (tmConf scanTM W n bit t).2.1)
            else (tmConf scanTM W n bit t).1 j) = false
          by_cases hj : j = (tmConf scanTM W n bit t).2.1
          · rw [if_pos hj]
            exact ih.2 _
          · rw [if_neg hj]
            exact ih.2 j

theorem not_tmAccAt_scanTM (W n : ℕ) (bit : ℕ → Bool) (hb : ∀ i, i < n → bit i = false) (t : ℕ) :
    ¬ tmAccAt scanTM W n bit t := by
  intro hacc
  have := hacc.2
  rw [(tmConf_scanTM_of_false W n bit hb t).1] at this
  simp [scanTM] at this

/-- **The scanning machine accepts within the deadline exactly the inputs with a `true` bit.** -/
theorem tmAccBy_scanTM (n : ℕ) (bit : ℕ → Bool) :
    tmAccBy scanTM (scanW n) n bit (scanH n) ↔ ∃ i, i < n ∧ bit i = true := by
  constructor
  · intro h
    by_contra hcon
    have hb : ∀ i, i < n → bit i = false := by
      intro i hi
      cases hbi : bit i with
      | false => rfl
      | true => exact absurd ⟨i, hi, hbi⟩ hcon
    obtain ⟨t, hat, -⟩ := h
    exact not_tmAccAt_scanTM _ n bit hb t hat
  · intro h
    classical
    have hi := Nat.find_spec h
    set i := Nat.find h with hidef
    have hmin : ∀ k, k < i → ¬ (k < n ∧ bit k = true) := fun k hk => Nat.find_min h hk
    have hfalse : ∀ k, k < i → scanTape n bit k = false := by
      intro k hk
      by_cases hkn : k < n
      · have := hmin k hk
        simp only [not_and, hkn, true_implies, Bool.not_eq_true] at this
        simp [scanTape, hkn, this]
      · simp [scanTape, hkn]
    have hconf := tmConf_scanTM (scanW n) n bit (by omega) i hfalse (by rw [scanW]; omega)
    have hhead : (tmConf scanTM (scanW n) n bit i).2.1 < scanW n := by
      rw [hconf, scanW]
      exact Nat.lt_succ_of_lt hi.1
    have haccF : scanTM.acc (tmConf scanTM (scanW n) n bit i).2.2 = false := by
      rw [hconf]
      simp [scanTM]
    have hstep := tmConf_succ_of_step hhead haccF
    rw [hconf] at hstep
    have hbi : scanTape n bit i = true := by simp [scanTape, hi.1, hi.2]
    refine ⟨i + 1, ⟨?_, ?_⟩, ?_⟩
    · rw [tmAlive, hstep, scanW]
      simp [scanTM]
      omega
    · rw [hstep]
      simp [scanTM, hbi]
    · rw [hstep]
      simp only [scanTM]
      rw [scanH]
      have : i < n := hi.1
      simp
      omega

/-- The width of the tape and the deadline are computed in unary by Cobham terms. -/
theorem caUniform_scanW : CAUniform scanW scanH := by
  refine ⟨Cob.pre [true] (Cob.unary (.proj 0)),
    Cob.pre (List.replicate 3 true) (.comp .smash [Cob.unary (.proj 0),
      Cob.constT (List.replicate 2 true)]),
    fun n => by rw [scanW]; omega, ?_, ?_⟩
  · intro x
    rw [Cob.eval_pre, Cob.eval_unary, scanW, List.replicate_succ]
    simp
  · intro x
    rw [Cob.eval_pre, Cob.eval_comp]
    simp only [List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_unary, Cob.eval_constT,
      List.getD_cons_zero, List.getD_cons_succ, List.length_replicate, Cob.eval_proj]
    rw [← List.replicate_add, scanH]
    congr 1
    omega

/-- The language of the scanning machine is exactly the language of the words with a `true`
bit. -/
theorem tmLang_scanTM_eq_someOne : TMLang scanTM scanW scanH = SomeOne := by
  funext x
  rw [TMLang, SomeOne]
  apply propext
  rw [tmAccBy_scanTM]
  constructor
  · rintro ⟨i, hi, hbi⟩
    rw [List.any_eq_true]
    exact ⟨x.getD i false, by rw [List.getD_eq_getElem x false hi]; exact List.getElem_mem hi, hbi⟩
  · intro hx
    rw [List.any_eq_true] at hx
    obtain ⟨b, hb, hbt⟩ := hx
    obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem hb
    exact ⟨k, hk, by rw [List.getD_eq_getElem x false hk, hkb]; exact hbt⟩

/-- **A third proof, through a Turing machine, that `Complexity.SomeOne` is decided by a
P-uniform circuit family.** -/
theorem pUniformDecidable_someOne_of_tm : PUniformDecidable SomeOne := by
  rw [← tmLang_scanTM_eq_someOne]
  exact pUniformDecidable_tmLang caUniform_scanW

end Complexity
