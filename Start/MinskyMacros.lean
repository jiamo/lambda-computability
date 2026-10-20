/-
**Register-machine macros for the compilation of partial recursive codes** — task
`M25-KCM-UNIVERSAL` (round 8, part B), building on `Start/Minsky.lean`.

Shepherdson–Sturgis style macros for `k`-counter machines (`Minsky.KM`), each with its
correctness lemma stated *in place*: the instructions of the macro sit at given labels of an
arbitrary program `M`, and the lemma gives the run from the entry label to the exit label.
Lemmas therefore compose by concatenating runs.

* `Minsky.Macro.clear_run` — `r i := 0` (one instruction);
* `Minsky.Macro.transfer_run` — `r j += r i; r i := 0` (two instructions);
* `Minsky.Macro.transfer2_run` — `r j += r i; r t += r i; r i := 0` (three instructions);
* `Minsky.Macro.copy_run` — `r j += r i`, `r i` preserved, through a scratch register `t`
  that is zero before and after (five instructions);
* `Minsky.Macro.mul_run` — `r k += r i * r j`, `r i := 0`, `r j` preserved, through a scratch
  register (seven instructions): the first arithmetic loop of the pairing function.

Open: the pairing macro (`Nat.pair`, which needs a comparison loop) and its inverse
(`Nat.unpair`, an integer square root loop), and then the compilation of the constructors of
`Nat.Partrec.Code` with a stack of frames stored as one register through `Nat.pair`.
-/

import Start.Minsky

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Macro

open Function

/-- Runs of a `k`-counter machine. -/
abbrev Run (M : KM) : KConf → KConf → Prop := Relation.ReflTransGen (KM.Step M)

/-- Registers agree outside a list of registers. -/
def AgreeOff (r r' : ℕ → ℕ) (xs : List ℕ) : Prop := ∀ x, x ∉ xs → r' x = r x

/-! ### Clearing a register -/

/-- **`clear i`**: `test i e o` at label `o` empties register `i` and exits at `e`. -/
theorem clear_run {M : KM} {o e i : ℕ} (h : M[o]? = some (.test i e o)) :
    ∀ (r : ℕ → ℕ), Run M ⟨o, r⟩ ⟨e, update r i 0⟩ := by
  intro r
  induction hn : r i generalizing r with
  | zero =>
      have : update r i 0 = r := by rw [← hn, update_eq_self]
      rw [this]
      exact .single (KM.Step.zero h hn)
  | succ n ih =>
      have hs : KM.Step M ⟨o, r⟩ ⟨o, update r i n⟩ := KM.Step.dec h hn
      have := ih (update r i n) (by simp)
      rw [update_idem] at this
      exact .head hs this

/-! ### Transferring a register -/

/-- **`transfer i j`**: `test i e (o+1); inc j o` adds register `i` to register `j` and empties
register `i`. -/
theorem transfer_run {M : KM} {o e i j : ℕ} (hij : i ≠ j) (h₀ : M[o]? = some (.test i e (o + 1)))
    (h₁ : M[o + 1]? = some (.inc j o)) :
    ∀ (r : ℕ → ℕ), ∃ r', Run M ⟨o, r⟩ ⟨e, r'⟩ ∧ r' i = 0 ∧ r' j = r j + r i ∧
      AgreeOff r r' [i, j] := by
  intro r
  induction hn : r i generalizing r with
  | zero =>
      exact ⟨r, .single (KM.Step.zero h₀ hn), hn, by simp, fun _ _ => rfl⟩
  | succ n ih =>
      have hs₁ : KM.Step M ⟨o, r⟩ ⟨o + 1, update r i n⟩ := KM.Step.dec h₀ hn
      have hs₂ : KM.Step M ⟨o + 1, update r i n⟩
          ⟨o, update (update r i n) j (update r i n j + 1)⟩ := KM.Step.inc h₁
      obtain ⟨r', hrun, hi, hj, hag⟩ :=
        ih (update (update r i n) j (update r i n j + 1)) (by simp [hij])
      refine ⟨r', .head hs₁ (.head hs₂ hrun), hi, ?_, ?_⟩
      · rw [hj]; simp [Ne.symm hij]; omega
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [hag x (by simp [hx.1, hx.2])]
        simp [hx.1, hx.2]

/-- **`transfer2 i j t`**: `test i e (o+1); inc j (o+2); inc t o` adds register `i` to the
registers `j` and `t` and empties register `i`. -/
theorem transfer2_run {M : KM} {o e i j t : ℕ} (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (h₀ : M[o]? = some (.test i e (o + 1))) (h₁ : M[o + 1]? = some (.inc j (o + 2)))
    (h₂ : M[o + 2]? = some (.inc t o)) :
    ∀ (r : ℕ → ℕ), ∃ r', Run M ⟨o, r⟩ ⟨e, r'⟩ ∧ r' i = 0 ∧ r' j = r j + r i ∧
      r' t = r t + r i ∧ AgreeOff r r' [i, j, t] := by
  intro r
  induction hn : r i generalizing r with
  | zero =>
      exact ⟨r, .single (KM.Step.zero h₀ hn), hn, by simp, by simp, fun _ _ => rfl⟩
  | succ n ih =>
      have hs₁ : KM.Step M ⟨o, r⟩ ⟨o + 1, update r i n⟩ := KM.Step.dec h₀ hn
      have hs₂ : KM.Step M ⟨o + 1, update r i n⟩
          ⟨o + 2, update (update r i n) j (update r i n j + 1)⟩ := KM.Step.inc h₁
      have hs₃ : KM.Step M ⟨o + 2, update (update r i n) j (update r i n j + 1)⟩
          ⟨o, update (update (update r i n) j (update r i n j + 1)) t
            (update (update r i n) j (update r i n j + 1) t + 1)⟩ := KM.Step.inc h₂
      obtain ⟨r', hrun, hi, hj, ht, hag⟩ :=
        ih (update (update (update r i n) j (update r i n j + 1)) t
          (update (update r i n) j (update r i n j + 1) t + 1))
          (by rw [update_of_ne hit, update_of_ne hij, update_self])
      refine ⟨r', .head hs₁ (.head hs₂ (.head hs₃ hrun)), hi, ?_, ?_, ?_⟩
      · rw [hj]; simp [Ne.symm hij, hjt]; omega
      · rw [ht]; simp [Ne.symm hit, Ne.symm hjt]; omega
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [hag x (by simp [hx.1, hx.2.1, hx.2.2])]
        simp [hx.1, hx.2.1, hx.2.2]

/-! ### Copying a register -/

/-- **`copy i j` through the scratch register `t`**: `transfer2 i j t` at `o`, then
`transfer t i` at `o + 3`; register `j` receives register `i`, which is restored, and the
scratch register is zero again. -/
theorem copy_run {M : KM} {o e i j t : ℕ} (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t)
    (h₀ : M[o]? = some (.test i (o + 3) (o + 1))) (h₁ : M[o + 1]? = some (.inc j (o + 2)))
    (h₂ : M[o + 2]? = some (.inc t o)) (h₃ : M[o + 3]? = some (.test t e (o + 4)))
    (h₄ : M[o + 4]? = some (.inc i (o + 3))) (r : ℕ → ℕ) (hr : r t = 0) :
    ∃ r', Run M ⟨o, r⟩ ⟨e, r'⟩ ∧ r' i = r i ∧ r' j = r j + r i ∧ r' t = 0 ∧
      AgreeOff r r' [i, j, t] := by
  obtain ⟨r₁, hrun₁, hi₁, hj₁, ht₁, hag₁⟩ := transfer2_run hij hit hjt h₀ h₁ h₂ r
  obtain ⟨r₂, hrun₂, ht₂, hi₂, hag₂⟩ := transfer_run (Ne.symm hit) h₃ h₄ r₁
  refine ⟨r₂, hrun₁.trans hrun₂, by rw [hi₂, hi₁, ht₁, hr]; simp, ?_, ht₂, ?_⟩
  · rw [hag₂ j (by simp [Ne.symm hij, hjt]), hj₁]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [hag₂ x (by simp [hx.1, hx.2.2]), hag₁ x (by simp [hx.1, hx.2.1, hx.2.2])]

/-! ### Multiplication -/

/-- **`mul i j k` through the scratch register `t`**: a loop on register `i` adding register `j`
to register `k` once per unit of `i` (a copy of `j` into `k` through `t`):

* `o`: `test i e (o+1)`;
* `o+1 … o+5`: `copy j k` through `t`, exiting to `o`.

Register `k` receives `r i * r j`, register `i` is emptied, `j` is preserved, `t` stays zero. -/
theorem mul_run {M : KM} {o e i j k t : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hit : i ≠ t)
    (hjk : j ≠ k) (hjt : j ≠ t) (hkt : k ≠ t)
    (h₀ : M[o]? = some (.test i e (o + 1)))
    (h₁ : M[o + 1]? = some (.test j (o + 1 + 3) (o + 1 + 1)))
    (h₂ : M[o + 1 + 1]? = some (.inc k (o + 1 + 2)))
    (h₃ : M[o + 1 + 2]? = some (.inc t (o + 1)))
    (h₄ : M[o + 1 + 3]? = some (.test t o (o + 1 + 4)))
    (h₅ : M[o + 1 + 4]? = some (.inc j (o + 1 + 3))) :
    ∀ (r : ℕ → ℕ), r t = 0 → ∃ r', Run M ⟨o, r⟩ ⟨e, r'⟩ ∧ r' i = 0 ∧ r' j = r j ∧
      r' k = r k + r i * r j ∧ r' t = 0 ∧ AgreeOff r r' [i, j, k, t] := by
  intro r hr
  induction hn : r i generalizing r with
  | zero =>
      exact ⟨r, .single (KM.Step.zero h₀ hn), hn, rfl, by simp, hr, fun _ _ => rfl⟩
  | succ n ih =>
      have hs : KM.Step M ⟨o, r⟩ ⟨o + 1, update r i n⟩ := KM.Step.dec h₀ hn
      obtain ⟨r₁, hrun₁, hj₁, hk₁, ht₁, hag₁⟩ :=
        copy_run hjk hjt hkt h₁ h₂ h₃ h₄ h₅ (update r i n) (by simp [Ne.symm hit, hr])
      have hi₁ : r₁ i = n := by rw [hag₁ i (by simp [hij, hik, hit])]; simp
      obtain ⟨r₂, hrun₂, hi₂, hj₂, hk₂, ht₂, hag₂⟩ := ih r₁ ht₁ hi₁
      refine ⟨r₂, .head hs (hrun₁.trans hrun₂), hi₂, ?_, ?_, ht₂, ?_⟩
      · rw [hj₂, hj₁]; simp [Ne.symm hij]
      · rw [hk₂, hk₁, hj₁]; simp [Ne.symm hik, Ne.symm hij]; ring
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
        rw [hag₂ x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2]),
          hag₁ x (by simp [hx.2.1, hx.2.2.1, hx.2.2.2])]
        simp [hx.1]

end Macro

end Minsky
