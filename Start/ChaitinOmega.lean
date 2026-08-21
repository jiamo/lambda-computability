/-
A self-delimiting (prefix free) binary coding of lambda terms, prefix complexity, and Chaitin's
halting probability `Ω`.

The coding is the classical "binary lambda calculus" one:

* `var i  ↦  1^(i+1) 0`
* `lam t  ↦  00 ++ bits t`
* `app a b ↦ 01 ++ bits a ++ bits b`

`Lambda.bits_append_inj` is the standard self-delimiting statement — `bits s ++ u = bits t ++ v`
forces `s = t` and `u = v` — from which `Lambda.bits_prefixFree` follows: no code word is a prefix
of another one.  This is exactly the hypothesis of Kraft's inequality (`Start/Kraft.lean`).

Two consequences are recorded.

* Prefix complexity `Lambda.kolmP s`: the least *bit length* of a closed program for `s`.  Choosing
  a shortest program for each `s` gives a prefix free coding of ℕ, so
  `Lambda.kraft_kolmP : ∑' s, 2 ^ (-kolmP s) ≤ 1`.
* Chaitin's constant `Lambda.chaitinOmega`, the total weight of the halting programs, i.e. of the
  closed terms that have a normal form.  It is a convergent sum (`Lambda.summable_haltingWeight`)
  and satisfies `0 < Ω < 1` (`Lambda.chaitinOmega_pos`, `Lambda.chaitinOmega_lt_one`): positivity
  because `I` halts, and the strict upper bound because `omega` does not halt, and its own weight
  is therefore left over in Kraft's inequality.
-/

import Start.Kolmogorov
import Start.Kraft
import Start.NormalizationUndecidable
import Start.Solvability

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

open scoped BigOperators

------------------------------------------------------------------------
-- A self-delimiting binary coding of terms
------------------------------------------------------------------------

/-- Binary lambda calculus coding of a term as a bit string:
`var i ↦ 1^(i+1) 0`, `lam t ↦ 00 t`, `app a b ↦ 01 a b`. -/
def bits : Lambda → List Bool
  | Lambda.var i => List.replicate (i + 1) Bool.true ++ [Bool.false]
  | Lambda.lam t => Bool.false :: Bool.false :: bits t
  | Lambda.app a b => Bool.false :: Bool.true :: (bits a ++ bits b)

@[simp] theorem bits_var (i : ℕ) :
    bits (Lambda.var i) = List.replicate (i + 1) Bool.true ++ [Bool.false] := rfl

@[simp] theorem bits_lam (t : Lambda) :
    bits (Lambda.lam t) = Bool.false :: Bool.false :: bits t := rfl

@[simp] theorem bits_app (a b : Lambda) :
    bits (Lambda.app a b) = Bool.false :: Bool.true :: (bits a ++ bits b) := rfl

/-- The code of a variable is self-delimiting: the block of `true` bits determines the index. -/
theorem replicate_true_append_inj :
    ∀ (i j : ℕ) (u v : List Bool),
      List.replicate i Bool.true ++ (Bool.false :: u)
          = List.replicate j Bool.true ++ (Bool.false :: v) → i = j ∧ u = v := by
  intro i
  induction i with
  | zero =>
      intro j u v h
      cases j with
      | zero => simpa using h
      | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
      intro j u v h
      cases j with
      | zero => simp [List.replicate_succ] at h
      | succ j =>
          simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hi, hu⟩ := ih j u v h
          exact ⟨by omega, hu⟩

/-- The coding is self-delimiting: a code word can be read off from any string that begins with
it, together with the remainder. -/
theorem bits_append_inj :
    ∀ (s t : Lambda) (u v : List Bool), bits s ++ u = bits t ++ v → s = t ∧ u = v := by
  intro s
  induction s with
  | var i =>
      intro t u v h
      cases t with
      | var j =>
          simp only [bits_var, List.append_assoc, List.cons_append, List.nil_append] at h
          obtain ⟨hij, huv⟩ := replicate_true_append_inj (i + 1) (j + 1) u v h
          exact ⟨by simp [Nat.succ_injective hij], huv⟩
      | lam t => simp [bits_var, List.replicate_succ] at h
      | app a b => simp [bits_var, List.replicate_succ] at h
  | lam s ih =>
      intro t u v h
      cases t with
      | var j => simp [bits_var, List.replicate_succ] at h
      | lam t =>
          simp only [bits_lam, List.cons_append, List.cons.injEq, true_and] at h
          obtain ⟨hst, huv⟩ := ih t u v h
          exact ⟨by rw [hst], huv⟩
      | app a b => simp [bits_lam, bits_app] at h
  | app a b iha ihb =>
      intro t u v h
      cases t with
      | var j => simp [bits_var, List.replicate_succ] at h
      | lam t => simp [bits_lam, bits_app] at h
      | app c d =>
          simp only [bits_app, List.cons_append, List.cons.injEq, true_and,
            List.append_assoc] at h
          obtain ⟨hac, hbd⟩ := iha c (bits b ++ u) (bits d ++ v) h
          obtain ⟨hbd', huv⟩ := ihb d u v hbd
          exact ⟨by rw [hac, hbd'], huv⟩

/-- The coding is injective. -/
theorem bits_injective : Function.Injective bits := by
  intro s t h
  exact (bits_append_inj s t [] [] (by simp [h])).1

/-- The coding is prefix free: no code word is a prefix of another one. -/
theorem bits_prefixFree {s t : Lambda} (h : bits s <+: bits t) : s = t := by
  obtain ⟨w, hw⟩ := h
  exact (bits_append_inj s t w [] (by simp [hw])).1

theorem bits_prefixFreeCoding : Kraft.PrefixFreeCoding bits := fun _ _ h => bits_prefixFree h

/-- Prefix free codings restrict to subtypes. -/
theorem bits_prefixFreeCoding_subtype (P : Lambda → Prop) :
    Kraft.PrefixFreeCoding (fun t : {t : Lambda // P t} => bits ↑t) :=
  fun _ _ h => Subtype.ext (bits_prefixFree h)

------------------------------------------------------------------------
-- Prefix complexity
------------------------------------------------------------------------

/-- **Prefix complexity**: the least number of bits of a (self-delimiting) closed program for `s`.
-/
noncomputable def kolmP (s : ℕ) : ℕ :=
  sInf {n | ∃ t : Lambda, IsProgramFor t s ∧ (bits t).length = n}

theorem kolmP_le_of_isProgramFor {t : Lambda} {s : ℕ} (h : IsProgramFor t s) :
    kolmP s ≤ (bits t).length :=
  Nat.sInf_le ⟨t, h, rfl⟩

theorem exists_program_of_kolmP (s : ℕ) :
    ∃ t : Lambda, IsProgramFor t s ∧ (bits t).length = kolmP s :=
  Nat.sInf_mem (s := {n | ∃ t : Lambda, IsProgramFor t s ∧ (bits t).length = n})
    ⟨(bits (Lambda.church s)).length, Lambda.church s, isProgramFor_church s, rfl⟩

/-- A code word is at most twice as long as the syntactic size of the term it encodes. -/
theorem bits_length_le_two_mul_size : ∀ t : Lambda, (bits t).length ≤ 2 * size t := by
  intro t
  induction t with
  | var i => simp [size]
  | lam t ih => simp [size]; omega
  | app a b iha ihb => simp [size]; omega

/-- Prefix complexity is bounded by twice the plain complexity. -/
theorem kolmP_le_two_mul_kolm (s : ℕ) : kolmP s ≤ 2 * kolm s := by
  obtain ⟨t, ht, hsize⟩ := exists_program_of_kolm s
  calc kolmP s ≤ (bits t).length := kolmP_le_of_isProgramFor ht
    _ ≤ 2 * size t := bits_length_le_two_mul_size t
    _ = 2 * kolm s := by rw [hsize]

/-- A shortest self-delimiting program for `s`. -/
noncomputable def shortestProgram (s : ℕ) : Lambda := (exists_program_of_kolmP s).choose

theorem shortestProgram_spec (s : ℕ) :
    IsProgramFor (shortestProgram s) s ∧ (bits (shortestProgram s)).length = kolmP s :=
  (exists_program_of_kolmP s).choose_spec

/-- Shortest programs for different numbers are incomparable, so `s ↦ bits (shortestProgram s)` is
a prefix free coding of ℕ. -/
theorem shortestProgram_prefixFreeCoding :
    Kraft.PrefixFreeCoding (fun s : ℕ => bits (shortestProgram s)) := by
  intro s s' h
  have hterm : shortestProgram s = shortestProgram s' := bits_prefixFree h
  have h1 := (shortestProgram_spec s).1.2
  have h2 := (shortestProgram_spec s').1.2
  rw [hterm] at h1
  exact Lambda.unique_church_reduct h1 h2

/-- **Kraft's inequality for prefix complexity**: `∑ 2 ^ (-K(s)) ≤ 1`. -/
theorem kraft_kolmP : ∑' s : ℕ, ((2 : ℝ)⁻¹) ^ kolmP s ≤ 1 := by
  have h := Kraft.tsum_wt_le_one shortestProgram_prefixFreeCoding
  have hrw : ∀ s : ℕ, Kraft.wt (bits (shortestProgram s)) = ((2 : ℝ)⁻¹) ^ kolmP s := by
    intro s
    rw [Kraft.wt, (shortestProgram_spec s).2]
  simpa [hrw] using h

------------------------------------------------------------------------
-- Chaitin's Omega
------------------------------------------------------------------------

/-- A *halting program*: a closed term that reduces to a normal form. -/
def Halts (t : Lambda) : Prop := Lambda.IsClosed t ∧ HasNormalForm t

theorem halts_I : Halts Lambda.I :=
  ⟨Lambda.I_closed, ⟨Lambda.I, Lambda.reduces.refl _, Lambda.is_normal_I⟩⟩

theorem not_halts_omega : ¬ Halts Lambda.omega := fun h => not_hasNormalForm_omega h.2

/-- The weights `2 ^ (-|bits t|)` of the halting programs are summable: this is Kraft's
inequality. -/
theorem summable_haltingWeight :
    Summable (fun t : {t : Lambda // Halts t} => Kraft.wt (bits ↑t)) :=
  Kraft.summable_wt (bits_prefixFreeCoding_subtype Halts)

/-- **Chaitin's constant**: the halting probability, i.e. the total weight of the halting
programs in the self-delimiting coding `bits`. -/
noncomputable def chaitinOmega : ℝ := ∑' t : {t : Lambda // Halts t}, Kraft.wt (bits ↑t)

/-- **Kraft's inequality for the halting set**: `Ω ≤ 1`. -/
theorem chaitinOmega_le_one : chaitinOmega ≤ 1 :=
  Kraft.tsum_wt_le_one (bits_prefixFreeCoding_subtype Halts)

theorem chaitinOmega_pos : 0 < chaitinOmega := by
  have hI : (⟨Lambda.I, halts_I⟩ : {t : Lambda // Halts t}) ∈ Set.univ := Set.mem_univ _
  have hle : Kraft.wt (bits Lambda.I) ≤ chaitinOmega := by
    refine summable_haltingWeight.le_tsum ⟨Lambda.I, halts_I⟩ ?_
    intro b _
    exact Kraft.wt_nonneg _
  exact lt_of_lt_of_le (Kraft.wt_pos _) (by simpa using hle)

theorem chaitinOmega_add_omega_weight_le_one :
    chaitinOmega + Kraft.wt (bits Lambda.omega) ≤ 1 :=
  Kraft.tsum_wt_add_le_one bits_prefixFreeCoding (P := Halts) not_halts_omega

theorem chaitinOmega_lt_one : chaitinOmega < 1 := by
  have h := chaitinOmega_add_omega_weight_le_one
  have hpos := Kraft.wt_pos (bits Lambda.omega)
  linarith

/-- Chaitin's `Ω` is a genuine probability: `0 < Ω < 1`. -/
theorem chaitinOmega_mem_Ioo : chaitinOmega ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨chaitinOmega_pos, chaitinOmega_lt_one⟩

end Lambda
