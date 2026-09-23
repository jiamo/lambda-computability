/-
Time-bounded Kolmogorov complexity `K^t`.

`K^T(s)` is the least size of a closed lambda term that reduces to the Church numeral of `s` in
**at most `T`** beta steps.  It is the measure that appears in time-bounded descriptive
complexity — as opposed to Levin's `Kt` of `Start/LevinKt.lean`, which charges `log₂` of the
running time instead of imposing a bound on it — and, like every complexity measure in this
library, it is an instance of `Complexity.DescSystem` (`Start/DescriptionSystem.lean`).

* `Lambda.IsProgramForWithin`, `Lambda.ktimeSystem`, `Lambda.ktime` — the timed programs, the
  description system they form, and the measure `K^T`;
* `Lambda.ktime_le_of_isProgramForWithin`, `Lambda.exists_program_of_ktime`,
  `Lambda.ktime_le_iff` — `K^T` is a minimum, and the membership test for it is the existence of
  a *bounded* witness: a program of size at most `k` together with a run of at most `T` steps;
* `Lambda.ktime_antitone` — `K^T` decreases as the time bound `T` grows;
* `Lambda.kolm_le_ktime`, `Lambda.ktime_le_church` — it sits above plain Kolmogorov complexity
  and below the size of the numeral itself;
* `Lambda.exists_bound_ktime_eq_kolm`, `Lambda.ktime_eq_kolm_of_le` — for every `s` there is a
  bound from which on the two agree: the time-bounded measure converges to `K`;
* `Lambda.finite_setOf_ktime_le`, `Lambda.exists_incompressible_ktime` — the counting bound and
  incompressibility, inherited from plain complexity;
* `Lambda.kt_le_ktime_add_log`, `Lambda.ktime_le_of_kt` — the comparison with Levin's `Kt`;
* `Lambda.ktimeWithSystem`, `Lambda.ktimeWith`, `Lambda.ktime_le_ktimeWith`,
  `Lambda.ktimeWith_I_le_ktime` — **invariance**: changing the interpreter changes `K^T` by at
  most an additive constant, at the price of at most one extra step in the bound.

The remaining exit criterion of the task (the language `{(x, k) : K^T(x) ≤ k}` lies in `NP`) is
*not* proved here; `Lambda.ktime_le_iff` isolates its combinatorial half — the existence of a
bounded certificate — and the missing half is that the certificate is checkable in polynomial
time in the time model of `Start/ComplexityClasses.lean`.
-/

import Start.LevinKt
import Start.Kolmogorov

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complexity Complexity.DescSystem

namespace Lambda

/-! ### Programs with a time bound -/

/-- `p` is a program for `s` running **within** `T` beta steps: a closed term that reduces to the
Church numeral of `s` in at most `T` steps. -/
def IsProgramForWithin (p : Lambda) (T s : ℕ) : Prop :=
  Lambda.IsClosed p ∧ ∃ n ≤ T, reducesIn n p (Lambda.church s)

theorem isProgramForWithin_of_isTimedProgramFor {p : Lambda} {n T s : ℕ} (hn : n ≤ T)
    (h : IsTimedProgramFor p n s) : IsProgramForWithin p T s :=
  ⟨h.1, n, hn, h.2⟩

theorem isProgramFor_of_isProgramForWithin {p : Lambda} {T s : ℕ}
    (h : IsProgramForWithin p T s) : IsProgramFor p s := by
  obtain ⟨hc, n, -, hn⟩ := h
  exact ⟨hc, reduces_of_reducesIn hn⟩

/-- Relaxing the time bound preserves timed programs. -/
theorem isProgramForWithin_mono {p : Lambda} {T T' s : ℕ} (hT : T ≤ T')
    (h : IsProgramForWithin p T s) : IsProgramForWithin p T' s := by
  obtain ⟨hc, n, hn, hred⟩ := h
  exact ⟨hc, n, hn.trans hT, hred⟩

/-- The numeral is a program for itself, running in no steps at all. -/
theorem isProgramForWithin_church (T s : ℕ) : IsProgramForWithin (Lambda.church s) T s :=
  ⟨Lambda.church_closed s, 0, Nat.zero_le _, reducesIn.refl _⟩

/-! ### The measure -/

/-- **Time-bounded Kolmogorov complexity** as a description system: the programs are the closed
terms reducing to the numeral within `T` steps, with their syntactic size. -/
def ktimeSystem (T : ℕ) : DescSystem Lambda ℕ where
  size := size
  Outputs := fun p s => IsProgramForWithin p T s

/-- **`K^T(s)`**: the least size of a closed term reducing to `church s` in at most `T` steps. -/
def ktime (T s : ℕ) : ℕ := (ktimeSystem T).K s

theorem ktime_le_of_isProgramForWithin {p : Lambda} {T s : ℕ} (h : IsProgramForWithin p T s) :
    ktime T s ≤ size p :=
  K_le_of_outputs (M := ktimeSystem T) h

theorem describes_ktimeSystem (T s : ℕ) : (ktimeSystem T).Describes s :=
  ⟨Lambda.church s, isProgramForWithin_church T s⟩

theorem exists_program_of_ktime (T s : ℕ) :
    ∃ p : Lambda, IsProgramForWithin p T s ∧ size p = ktime T s := by
  obtain ⟨p, hp, hsize⟩ := exists_outputs_size_eq_K (describes_ktimeSystem T s)
  exact ⟨p, hp, hsize⟩

/-- The membership test for `K^T`: `K^T(s) ≤ k` exactly when `s` has a *certificate* — a program
of size at most `k` and a run of at most `T` steps.  This is the combinatorial content of the
claim that the time-bounded measure is verifiable by a bounded witness. -/
theorem ktime_le_iff {T s k : ℕ} :
    ktime T s ≤ k ↔ ∃ p : Lambda, size p ≤ k ∧ IsProgramForWithin p T s := by
  constructor
  · intro h
    obtain ⟨p, hp, hsize⟩ := exists_program_of_ktime T s
    exact ⟨p, by omega, hp⟩
  · rintro ⟨p, hsize, hp⟩
    exact le_trans (ktime_le_of_isProgramForWithin hp) hsize

/-- Writing the numeral out is always allowed, so `K^T` never exceeds the size of the numeral. -/
theorem ktime_le_church (T s : ℕ) : ktime T s ≤ 3 * s + 3 := by
  simpa [size_church] using ktime_le_of_isProgramForWithin (isProgramForWithin_church T s)

/-- **`K^T` decreases in `T`**: more time can only help. -/
theorem ktime_antitone {T T' : ℕ} (hT : T ≤ T') (s : ℕ) : ktime T' s ≤ ktime T s := by
  obtain ⟨p, hp, hsize⟩ := exists_program_of_ktime T s
  have := ktime_le_of_isProgramForWithin (isProgramForWithin_mono hT hp)
  omega

/-- **`K ≤ K^T`**: a time bound can only increase the cost. -/
theorem kolm_le_ktime (T s : ℕ) : kolm s ≤ ktime T s := by
  obtain ⟨p, hp, hsize⟩ := exists_program_of_ktime T s
  have := kolm_le_of_isProgramFor (isProgramFor_of_isProgramForWithin hp)
  omega

/-! ### Convergence to plain complexity -/

/-- For every `s` some time bound already achieves the unbounded optimum. -/
theorem exists_bound_ktime_eq_kolm (s : ℕ) : ∃ T : ℕ, ktime T s = kolm s := by
  obtain ⟨p, hp, hsize⟩ := exists_program_of_kolm s
  obtain ⟨n, hn⟩ := exists_reducesIn_of_reduces hp.2
  refine ⟨n, le_antisymm ?_ (kolm_le_ktime n s)⟩
  have := ktime_le_of_isProgramForWithin (p := p) (T := n) (s := s) ⟨hp.1, n, le_rfl, hn⟩
  omega

/-- Beyond that bound the two measures agree. -/
theorem ktime_eq_kolm_of_le {T T' s : ℕ} (h : ktime T s = kolm s) (hT : T ≤ T') :
    ktime T' s = kolm s :=
  le_antisymm (h ▸ ktime_antitone hT s) (kolm_le_ktime T' s)

/-! ### Counting -/

/-- Only finitely many numbers have a time-bounded description of a given size: the measure
inherits the counting bound of plain complexity. -/
theorem finite_setOf_ktime_le (T n : ℕ) : {s : ℕ | ktime T s ≤ n}.Finite :=
  (finite_setOf_kolm_le n).subset fun s hs => le_trans (kolm_le_ktime T s) hs

/-- **Incompressibility** for the time-bounded measure: for every bound `n` some number needs a
description of size at least `n`, whatever the time allowance. -/
theorem exists_incompressible_ktime (T n : ℕ) : ∃ s : ℕ, n ≤ ktime T s := by
  obtain ⟨s, hs⟩ := exists_incompressible n
  exact ⟨s, le_trans hs (kolm_le_ktime T s)⟩

/-! ### Comparison with Levin's `Kt` -/

/-- Levin's measure is bounded by the time-bounded one plus the logarithm of the bound. -/
theorem kt_le_ktime_add_log (T s : ℕ) : kt s ≤ ktime T s + Nat.log 2 T := by
  obtain ⟨p, hp, hsize⟩ := exists_program_of_ktime T s
  obtain ⟨hc, n, hn, hred⟩ := hp
  have h1 : kt s ≤ size p + Nat.log 2 n := kt_le_of_isTimedProgramFor ⟨hc, hred⟩
  have h2 : Nat.log 2 n ≤ Nat.log 2 T := Nat.log_mono_right hn
  omega

/-- Conversely, a Levin-optimal program is a time-bounded program for the bound it runs in. -/
theorem ktime_le_of_kt (s : ℕ) : ∃ T : ℕ, ktime T s ≤ kt s := by
  obtain ⟨p, n, hp, hsize⟩ := exists_timedProgram_of_kt s
  exact ⟨n, le_trans (ktime_le_of_isProgramForWithin ⟨hp.1, n, le_rfl, hp.2⟩) (by omega)⟩

/-! ### Invariance under a change of interpreter -/

/-- `K^T` measured through a fixed interpreter `U`: a program is a closed term `p` such that
`U p` reduces to the numeral within `T` steps. -/
def ktimeWithSystem (U : Lambda) (T : ℕ) : DescSystem Lambda ℕ where
  size := size
  Outputs := fun p s =>
    Lambda.IsClosed p ∧ ∃ n ≤ T, reducesIn n (Lambda.app U p) (Lambda.church s)

/-- Time-bounded complexity relative to the interpreter `U`. -/
def ktimeWith (U : Lambda) (T s : ℕ) : ℕ := (ktimeWithSystem U T).K s

theorem ktimeWith_le {U p : Lambda} {T n s : ℕ} (hp : Lambda.IsClosed p) (hn : n ≤ T)
    (h : reducesIn n (Lambda.app U p) (Lambda.church s)) :
    ktimeWith U T s ≤ size p :=
  K_le_of_outputs (M := ktimeWithSystem U T) (p := p) ⟨hp, n, hn, h⟩

/-- Feeding a program to a fixed closed interpreter is a translation of the interpreted system
into the plain one: it costs `size U + 1` symbols and no extra beta steps. -/
def ktimeWithTranslation {U : Lambda} (hU : Lambda.IsClosed U) (T : ℕ) :
    Translation (ktimeWithSystem U T) (ktimeSystem T) where
  map := fun p => Lambda.app U p
  cost := size U + 1
  outputs := fun {p} {_} h => ⟨Lambda.IsClosed_app hU h.1, h.2⟩
  size_le := fun p => by simp [ktimeSystem, ktimeWithSystem]; omega

/-- **Invariance theorem for `K^T`.**  Reading programs through a fixed closed interpreter `U`
lowers the time-bounded complexity by at most the constant `size U + 1`, with the *same* time
bound. -/
theorem ktime_le_ktimeWith {U : Lambda} (hU : Lambda.IsClosed U) (T s : ℕ)
    (h : ∃ p : Lambda, Lambda.IsClosed p ∧
      ∃ n ≤ T, reducesIn n (Lambda.app U p) (Lambda.church s)) :
    ktime T s ≤ ktimeWith U T s + (size U + 1) := by
  have hd : (ktimeWithSystem U T).Describes s := by
    obtain ⟨p, hp, hn⟩ := h
    exact ⟨p, hp, hn⟩
  exact K_le_add_cost (ktimeWithTranslation hU T) (x := s) hd

/-- Conversely the identity interpreter costs no symbols and exactly one extra step, so it only
shifts the bound by one. -/
theorem ktimeWith_I_le_ktime (T s : ℕ) : ktimeWith Lambda.I (T + 1) s ≤ ktime T s := by
  obtain ⟨p, hp, hsize⟩ := exists_program_of_ktime T s
  obtain ⟨hc, n, hn, hred⟩ := hp
  have hstep : Lambda.step (Lambda.app Lambda.I p) p := by
    have h := Lambda.step.beta (Lambda.var 0) p
    simpa [Lambda.I, Lambda.subst] using h
  have := ktimeWith_le (U := Lambda.I) (n := n + 1) (T := T + 1) hc (by omega)
    (reducesIn.step hstep hred)
  omega

end Lambda

end
