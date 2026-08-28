/-
Levin's time-bounded complexity `Kt`.

`Kt(s)` is the least value of `|p| + log₂ t` over closed lambda terms `p` that reduce to the
Church numeral of `s` in `t` beta steps: a program is charged for its length *and* for the
logarithm of its running time.  It is the measure underlying Levin's universal search, and it is
the instance of `Complexity.DescSystem` in which the size of a program takes time into account —
the step counter comes from `Start/ReducesIn.lean`, the syntactic size from `Start/TermSize.lean`.

* `Lambda.ktSystem`, `Lambda.kt` — the description system and the measure;
* `Lambda.kt_le_of_isTimedProgramFor`, `Lambda.exists_timedProgram_of_kt` — `Kt` is a minimum;
* `Lambda.kolm_le_kt`, `Lambda.kt_le_kolm_add_log` — `K ≤ Kt`, and `Kt` exceeds `K` by at most the
  logarithm of the running time of a shortest program;
* `Lambda.ktWithSystem`, `Lambda.ktWith` — the same measure relative to a fixed interpreter `U`;
* `Lambda.kt_le_ktWith` — **the invariance theorem for `Kt`**: an interpreter changes `Kt` by at
  most the additive constant `size U + 1`, because interpreting costs no extra beta steps.  It is
  an instance of the generic invariance estimate `Complexity.DescSystem.K_le_add_cost`;
* `Lambda.ktWith_I_le_kt_succ` — conversely the identity interpreter loses at most `1`, the
  logarithmic cost of the single administrative step.
-/

import Start.KolmogorovMachines
import Start.ReducesIn
import Mathlib.Data.Nat.Log

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complexity Complexity.DescSystem

namespace Lambda

/-! ### Timed programs -/

/-- `t` is a *timed program* for `s` running in `n` steps: a closed term reducing to the Church
numeral of `s` in exactly `n` beta steps. -/
def IsTimedProgramFor (t : Lambda) (n : ℕ) (s : ℕ) : Prop :=
  Lambda.IsClosed t ∧ reducesIn n t (Lambda.church s)

theorem isProgramFor_of_isTimedProgramFor {t : Lambda} {n s : ℕ}
    (h : IsTimedProgramFor t n s) : IsProgramFor t s :=
  ⟨h.1, reduces_of_reducesIn h.2⟩

theorem isTimedProgramFor_church (s : ℕ) : IsTimedProgramFor (Lambda.church s) 0 s :=
  ⟨Lambda.church_closed s, reducesIn.refl _⟩

/-- Every program runs for some number of steps. -/
theorem exists_isTimedProgramFor {t : Lambda} {s : ℕ} (h : IsProgramFor t s) :
    ∃ n : ℕ, IsTimedProgramFor t n s := by
  obtain ⟨n, hn⟩ := exists_reducesIn_of_reduces h.2
  exact ⟨n, h.1, hn⟩

/-! ### The measure -/

/-- **Levin complexity** as a description system: a program is a pair `(p, n)` of a term and a
step count, and it costs `size p + log₂ n`. -/
def ktSystem : DescSystem (Lambda × ℕ) ℕ where
  size := fun p => size p.1 + Nat.log 2 p.2
  Outputs := fun p s => IsTimedProgramFor p.1 p.2 s

/-- **Levin's time-bounded complexity** `Kt(s) = min {|p| + log₂ t}`, over closed terms `p`
reducing to `church s` in `t` steps. -/
def kt (s : ℕ) : ℕ := ktSystem.K s

theorem kt_le_of_isTimedProgramFor {t : Lambda} {n s : ℕ} (h : IsTimedProgramFor t n s) :
    kt s ≤ size t + Nat.log 2 n :=
  K_le_of_outputs (M := ktSystem) (p := (t, n)) h

theorem describes_ktSystem (s : ℕ) : ktSystem.Describes s :=
  ⟨(Lambda.church s, 0), isTimedProgramFor_church s⟩

theorem exists_timedProgram_of_kt (s : ℕ) :
    ∃ (t : Lambda) (n : ℕ), IsTimedProgramFor t n s ∧ size t + Nat.log 2 n = kt s := by
  obtain ⟨⟨t, n⟩, h, hsize⟩ := exists_outputs_size_eq_K (describes_ktSystem s)
  exact ⟨t, n, h, hsize⟩

/-- Writing the numeral itself is a timed program running in no steps. -/
theorem kt_le_church (s : ℕ) : kt s ≤ 3 * s + 3 := by
  have := kt_le_of_isTimedProgramFor (isTimedProgramFor_church s)
  simpa [size_church] using this

/-! ### Comparison with plain complexity -/

/-- **`K ≤ Kt`**: charging for time can only increase the cost. -/
theorem kolm_le_kt (s : ℕ) : kolm s ≤ kt s := by
  obtain ⟨t, n, h, hsize⟩ := exists_timedProgram_of_kt s
  have := kolm_le_of_isProgramFor (isProgramFor_of_isTimedProgramFor h)
  omega

/-- Conversely `Kt` exceeds `K` by at most the logarithm of the running time of a shortest
program. -/
theorem kt_le_kolm_add_log (s : ℕ) :
    ∃ n : ℕ, kt s ≤ kolm s + Nat.log 2 n := by
  obtain ⟨t, ht, hsize⟩ := exists_program_of_kolm s
  obtain ⟨n, hn⟩ := exists_isTimedProgramFor ht
  refine ⟨n, ?_⟩
  have := kt_le_of_isTimedProgramFor hn
  omega

/-! ### Invariance -/

/-- Levin complexity relative to a fixed interpreter `U`: a program is a closed term `p` together
with a step count `n` such that `U p` reduces to `church s` in `n` steps. -/
def ktWithSystem (U : Lambda) : DescSystem (Lambda × ℕ) ℕ where
  size := fun p => size p.1 + Nat.log 2 p.2
  Outputs := fun p s =>
    Lambda.IsClosed p.1 ∧ reducesIn p.2 (Lambda.app U p.1) (Lambda.church s)

/-- Levin complexity relative to the interpreter `U`. -/
def ktWith (U : Lambda) (s : ℕ) : ℕ := (ktWithSystem U).K s

theorem ktWith_le {U p : Lambda} {n s : ℕ} (hp : Lambda.IsClosed p)
    (h : reducesIn n (Lambda.app U p) (Lambda.church s)) :
    ktWith U s ≤ size p + Nat.log 2 n :=
  K_le_of_outputs (M := ktWithSystem U) (p := (p, n)) ⟨hp, h⟩

/-- Feeding a program to a fixed closed interpreter is a translation of the interpreted system
into the plain one: it costs `size U + 1` symbols and *no extra beta steps*, which is what makes
`Kt` invariant. -/
def ktWithTranslation {U : Lambda} (hU : Lambda.IsClosed U) :
    Translation (ktWithSystem U) ktSystem where
  map := fun p => (Lambda.app U p.1, p.2)
  cost := size U + 1
  outputs := fun {p} {_} h => ⟨Lambda.IsClosed_app hU h.1, h.2⟩
  size_le := fun p => by simp [ktSystem, ktWithSystem]; omega

/-- **Invariance theorem for `Kt`.**  Reading programs through a fixed closed interpreter `U`
lowers Levin complexity by at most the constant `size U + 1`. -/
theorem kt_le_ktWith {U : Lambda} (hU : Lambda.IsClosed U) (s : ℕ)
    (h : ∃ (p : Lambda) (n : ℕ), Lambda.IsClosed p ∧
      reducesIn n (Lambda.app U p) (Lambda.church s)) :
    kt s ≤ ktWith U s + size U + 1 := by
  have hd : (ktWithSystem U).Describes s := by
    obtain ⟨p, n, hp, hn⟩ := h
    exact ⟨(p, n), hp, hn⟩
  have := K_le_add_cost (ktWithTranslation hU) (x := s) hd
  simpa [kt, ktWith, ktWithTranslation, Nat.add_assoc] using this

/-- One extra beta step costs at most one extra bit. -/
theorem log_succ_le (n : ℕ) : Nat.log 2 (n + 1) ≤ Nat.log 2 n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : n + 1 ≤ n * 2 := by omega
    calc Nat.log 2 (n + 1) ≤ Nat.log 2 (n * 2) := Nat.log_mono_right h1
      _ = Nat.log 2 n + 1 := Nat.log_mul_base (by omega) (by omega)

/-- Conversely, the identity interpreter costs at most one bit: it adds a single beta step and no
symbols to the program. -/
theorem ktWith_I_le_kt_succ (s : ℕ) : ktWith Lambda.I s ≤ kt s + 1 := by
  obtain ⟨t, n, ht, hsize⟩ := exists_timedProgram_of_kt s
  have hstep : Lambda.step (Lambda.app Lambda.I t) t := by
    have h := Lambda.step.beta (Lambda.var 0) t
    simpa [Lambda.I, Lambda.subst] using h
  have hred : reducesIn (n + 1) (Lambda.app Lambda.I t) (Lambda.church s) :=
    reducesIn.step hstep ht.2
  have hle := ktWith_le (U := Lambda.I) (n := n + 1) ht.1 hred
  have := log_succ_le n
  omega

end Lambda

end
