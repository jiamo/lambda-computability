/-
**An oracle that separates: `P^B ≠ NP^B`.**

The second half of Baker–Gill–Solovay.  The language is the standard one,

  `L_B = { x : some word of length |x| lies in B }`,

which is in `NP^B` — guess a word of the right length and ask the oracle — and the oracle `B` is
built in stages against the enumeration `Start/OracleEnum.lean` of the polynomial-time oracle
machines, so that the `e`-th machine fails to decide `L_B` at one input.

The construction uses exactly the two facts of `Start/OracleCob.lean` and
`Start/OracleDiag.lean`: a polynomial-time oracle machine asks about fewer than `2 ^ n` words, so
on the input `1^n` it leaves a word of length `n` unasked
(`Complexity.CobQ.exists_word_not_queried_unary`), and a run does not change if the oracle is
changed only away from the words it asked about (`Complexity.CobQ.run_congr`).

* `Complexity.BGS.stage` — the stages: a finite oracle and a length threshold;
* `Complexity.BGS.oracleB`, `Complexity.BGS.langB` — the oracle and its language;
* `Complexity.BGS.inNP_rel_langB` — `L_B ∈ NP^B`;
* `Complexity.BGS.not_inP_rel_langB` — `L_B ∉ P^B`;
* `Complexity.bgs_different` — **`P^B ≠ NP^B` for that oracle.**
-/

import Mathlib
import Start.OracleClasses
import Start.OracleDiag
import Start.OracleEnum
import Start.CobhamRange

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace BGS

open CobQ

/-! ### The language of an oracle -/

/-- The characteristic function of a finite list of words. -/
def oracleOf (S : List Word) : Oracle := fun w => decide (w ∈ S)

@[simp] theorem oracleOf_apply (S : List Word) (w : Word) :
    oracleOf S w = true ↔ w ∈ S := by simp [oracleOf]

/-- The unary word `1^n`, the input the construction diagonalizes at. -/
def unary (n : ℕ) : Word := List.replicate n Bool.true

@[simp] theorem length_unary (n : ℕ) : (unary n).length = n := by simp [unary]

/-! ### The data attached to a machine -/

/-- The length from which on the machine `t` leaves a word of that length unasked. -/
noncomputable def startLen (t : CobQ) : ℕ := (exists_word_not_queried_unary t).choose

theorem startLen_spec (t : CobQ) (A : Oracle) (n : ℕ) (hn : startLen t ≤ n) :
    ∃ w : Word, w.length = n ∧ w ∉ queries A t [unary n] :=
  (exists_word_not_queried_unary t).choose_spec A n hn

/-- A monotone polynomial bound on the length of the words `t` asks about. -/
noncomputable def qlen (t : CobQ) : ℕ → ℕ := (polyQueryLen t).choose

theorem qlen_spec (t : CobQ) (A : Oracle) (args : List Word) :
    ∀ w ∈ queries A t args, w.length ≤ qlen t (maxLen args) :=
  (polyQueryLen t).choose_spec.2 A args

theorem qlen_unary (t : CobQ) (A : Oracle) (n : ℕ) :
    ∀ w ∈ queries A t [unary n], w.length ≤ qlen t n := by
  intro w hw
  have := qlen_spec t A [unary n] w hw
  simpa [maxLen, unary] using this

open Classical in
/-- The word of length `n` that `t` does not ask about, when there is one. -/
noncomputable def witness (t : CobQ) (A : Oracle) (n : ℕ) : Word :=
  if h : ∃ w : Word, w.length = n ∧ w ∉ queries A t [unary n] then h.choose else []

theorem witness_spec (t : CobQ) (A : Oracle) (n : ℕ) (hn : startLen t ≤ n) :
    (witness t A n).length = n ∧ witness t A n ∉ queries A t [unary n] := by
  have h : ∃ w : Word, w.length = n ∧ w ∉ queries A t [unary n] := startLen_spec t A n hn
  rw [witness, dif_pos h]
  exact h.choose_spec

/-! ### The stages -/

variable (f : ℕ → CobQ)

/-- The stage of the construction: the finite oracle built so far, and a length threshold above
which everything added later lies. -/
noncomputable def stage : ℕ → List Word × ℕ
  | 0 => ([], 0)
  | e + 1 =>
      let S := (stage e).1
      let m := (stage e).2
      let t := f e
      let n := max (startLen t) (m + 1)
      let A := oracleOf S
      let m' := max n (qlen t n)
      if eval A t [unary n] ≠ [] then (S, m') else (S ++ [witness t A n], m')

/-- The length at which the `e`-th machine is diagonalized. -/
noncomputable def diagLen (e : ℕ) : ℕ := max (startLen (f e)) ((stage f e).2 + 1)

theorem stage_succ_def (e : ℕ) :
    stage f (e + 1) =
      (if eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ [] then
        ((stage f e).1, max (diagLen f e) (qlen (f e) (diagLen f e)))
      else
        ((stage f e).1 ++ [witness (f e) (oracleOf (stage f e).1) (diagLen f e)],
          max (diagLen f e) (qlen (f e) (diagLen f e)))) := by
  rw [stage, diagLen]

theorem stage_succ_snd (e : ℕ) :
    (stage f (e + 1)).2 = max (diagLen f e) (qlen (f e) (diagLen f e)) := by
  rw [stage_succ_def]
  split <;> rfl

theorem stage_succ_fst_pos {e : ℕ}
    (h : eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ []) :
    (stage f (e + 1)).1 = (stage f e).1 := by
  rw [stage_succ_def, if_pos h]

theorem stage_succ_fst_neg {e : ℕ}
    (h : ¬ (eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ [])) :
    (stage f (e + 1)).1
      = (stage f e).1 ++ [witness (f e) (oracleOf (stage f e).1) (diagLen f e)] := by
  rw [stage_succ_def, if_neg h]

theorem lt_diagLen (e : ℕ) : (stage f e).2 < diagLen f e := by
  have : (stage f e).2 + 1 ≤ diagLen f e := le_max_right _ _
  omega

theorem startLen_le_diagLen (e : ℕ) : startLen (f e) ≤ diagLen f e := le_max_left _ _

theorem diagLen_le_stage_succ (e : ℕ) : diagLen f e ≤ (stage f (e + 1)).2 := by
  rw [stage_succ_snd]
  exact le_max_left _ _

theorem qlen_le_stage_succ (e : ℕ) : qlen (f e) (diagLen f e) ≤ (stage f (e + 1)).2 := by
  rw [stage_succ_snd]
  exact le_max_right _ _

theorem stage_subset_succ (e : ℕ) : (stage f e).1 ⊆ (stage f (e + 1)).1 := by
  by_cases h : eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ []
  · rw [stage_succ_fst_pos f h]
    exact fun w hw => hw
  · rw [stage_succ_fst_neg f h]
    intro w hw
    simp [hw]

theorem stage_snd_le_succ (e : ℕ) : (stage f e).2 ≤ (stage f (e + 1)).2 :=
  le_trans (le_of_lt (lt_diagLen f e)) (diagLen_le_stage_succ f e)

theorem stage_snd_mono {e e' : ℕ} (h : e ≤ e') : (stage f e).2 ≤ (stage f e').2 := by
  induction e' with
  | zero =>
      have he : e = 0 := by omega
      subst he
      exact le_rfl
  | succ e' ih =>
      rcases Nat.lt_or_ge e (e' + 1) with h' | h'
      · exact le_trans (ih (by omega)) (stage_snd_le_succ f e')
      · have he : e = e' + 1 := by omega
        subst he
        exact le_rfl

theorem stage_subset_mono {e e' : ℕ} (h : e ≤ e') : (stage f e).1 ⊆ (stage f e').1 := by
  induction e' with
  | zero =>
      have he : e = 0 := by omega
      subst he
      exact fun w hw => hw
  | succ e' ih =>
      rcases Nat.lt_or_ge e (e' + 1) with h' | h'
      · exact fun w hw => stage_subset_succ f e' (ih (by omega) hw)
      · have he : e = e' + 1 := by omega
        subst he
        exact fun w hw => hw

/-- Every word of a stage is no longer than its threshold. -/
theorem length_le_of_mem_stage : ∀ (e : ℕ) (w : Word), w ∈ (stage f e).1 → w.length ≤ (stage f e).2
  | 0, w, hw => by simp [stage] at hw
  | e + 1, w, hw => by
      have hprev : ∀ u ∈ (stage f e).1, u.length ≤ (stage f (e + 1)).2 := by
        intro u hu
        exact le_trans (length_le_of_mem_stage e u hu)
          (le_trans (le_of_lt (lt_diagLen f e)) (diagLen_le_stage_succ f e))
      by_cases h : eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ []
      · rw [stage_succ_fst_pos f h] at hw
        exact hprev w hw
      · rw [stage_succ_fst_neg f h] at hw
        rcases List.mem_append.1 hw with hw' | hw'
        · exact hprev w hw'
        · have hwit := witness_spec (f e) (oracleOf (stage f e).1) (diagLen f e)
            (startLen_le_diagLen f e)
          have hweq : w = witness (f e) (oracleOf (stage f e).1) (diagLen f e) := by
            simpa using hw'
          rw [hweq, hwit.1]
          exact diagLen_le_stage_succ f e

/-- A word appearing at a later stage but short enough was already there. -/
theorem mem_stage_of_length_le : ∀ (e e' : ℕ), e ≤ e' → ∀ w : Word, w ∈ (stage f e').1 →
    w.length ≤ (stage f e).2 → w ∈ (stage f e).1 := by
  intro e e' he
  induction e' with
  | zero =>
      intro w hw _
      have h0 : e = 0 := by omega
      subst h0
      exact hw
  | succ e' ih =>
      intro w hw hlen
      rcases Nat.lt_or_ge e (e' + 1) with h' | h'
      · have he' : e ≤ e' := by omega
        refine ih he' w ?_ hlen
        by_cases h : eval (oracleOf (stage f e').1) (f e') [unary (diagLen f e')] ≠ []
        · rw [stage_succ_fst_pos f h] at hw
          exact hw
        · rw [stage_succ_fst_neg f h] at hw
          rcases List.mem_append.1 hw with hw' | hw'
          · exact hw'
          · exfalso
            have hwit := witness_spec (f e') (oracleOf (stage f e').1) (diagLen f e')
              (startLen_le_diagLen f e')
            have hweq : w = witness (f e') (oracleOf (stage f e').1) (diagLen f e') := by
              simpa using hw'
            have hlen' : w.length = diagLen f e' := by rw [hweq, hwit.1]
            have h1 : (stage f e).2 ≤ (stage f e').2 := stage_snd_mono f he'
            have h2 : (stage f e').2 < diagLen f e' := lt_diagLen f e'
            omega
      · have he : e = e' + 1 := by omega
        subst he
        exact hw

/-! ### The oracle -/

open Classical in
/-- The oracle built by the construction. -/
noncomputable def oracleB : Oracle := fun w => decide (∃ e, w ∈ (stage f e).1)

theorem oracleB_true_iff (w : Word) : oracleB f w = true ↔ ∃ e, w ∈ (stage f e).1 := by
  classical
  simp [oracleB]

theorem oracleB_of_mem {e : ℕ} {w : Word} (h : w ∈ (stage f e).1) : oracleB f w = true :=
  (oracleB_true_iff f w).2 ⟨e, h⟩

/-- Below the threshold of a stage the oracle is the finite oracle of that stage. -/
theorem oracleB_eq_stage (e : ℕ) (w : Word) (hw : w.length ≤ (stage f e).2) :
    oracleB f w = oracleOf (stage f e).1 w := by
  by_cases h : w ∈ (stage f e).1
  · simp [oracleB_of_mem f h, oracleOf, h]
  · have hB : oracleB f w = false := by
      by_contra hcon
      have : oracleB f w = true := by
        cases hval : oracleB f w with
        | false => exact absurd hval hcon
        | true => rfl
      obtain ⟨e', he'⟩ := (oracleB_true_iff f w).1 this
      rcases Nat.le_total e e' with hle | hle
      · exact h (mem_stage_of_length_le f e e' hle w he' hw)
      · exact h (stage_subset_mono f hle he')
    simp [hB, oracleOf, h]

/-! ### The language -/

/-- The language of the oracle: the inputs whose length is the length of some word of `B`. -/
def langB : Language := fun x => ∃ w : Word, w.length = x.length ∧ oracleB f w = true

/-! ### The language is in `NP^B` -/

/-- `1` exactly when the second argument is no longer than the first. -/
def lenGeC : Cob := .comp .notC [.comp Cob.dropN [.proj 0, .proj 1]]

@[simp] theorem eval_lenGeC (x w : Word) :
    lenGeC.eval [x, w] = if w.length ≤ x.length then [Bool.true] else [] := by
  simp only [lenGeC, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_dropN, Cob.eval_notC]
  by_cases h : w.length ≤ x.length
  · simp [h, List.drop_eq_nil_iff.2 h]
  · have : ¬ (w.drop x.length = []) := by
      intro hdrop
      exact h (List.drop_eq_nil_iff.1 hdrop)
    simp [h, this]

/-- `1` exactly when the two arguments have the same length. -/
def eqLenC : Cob := .comp .andC [lenGeC, .comp lenGeC [.proj 1, .proj 0]]

@[simp] theorem eval_eqLenC (x w : Word) :
    eqLenC.eval [x, w] = if w.length = x.length then [Bool.true] else [] := by
  simp only [eqLenC, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, eval_lenGeC, Cob.eval_andC]
  by_cases h1 : w.length ≤ x.length <;> by_cases h2 : x.length ≤ w.length <;>
    simp [h1, h2] <;> omega

/-- The verifier of the language: the witness has the length of the input and belongs to the
oracle. -/
def verifier : CobQ := .comp CobQ.andQ [ofCob eqLenC, .comp .query [.proj 1]]

theorem eval_verifier (A : Oracle) (x w : Word) :
    eval A verifier [x, w] ≠ [] ↔ w.length = x.length ∧ A w = true := by
  simp only [verifier, CobQ.eval_comp, List.map_cons, List.map_nil, CobQ.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, CobQ.eval_andQ, CobQ.eval_query, eval_ofCob,
    eval_eqLenC]
  by_cases h1 : w.length = x.length
  · by_cases h2 : A w
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

/-- **The language is in `NP^B`.** -/
theorem inNP_rel_langB : InNP_rel (oracleB f) (langB f) := by
  refine ⟨verifier, fun n => n, ⟨1, 1, fun n => by simp⟩, fun _ _ h => h, ?_, ?_⟩
  · intro x w hacc
    exact le_of_eq ((eval_verifier (oracleB f) x w).1 hacc).1
  · intro x
    constructor
    · rintro ⟨w, hw, hB⟩
      exact ⟨w, (eval_verifier (oracleB f) x w).2 ⟨hw, hB⟩⟩
    · rintro ⟨w, hw⟩
      obtain ⟨h1, h2⟩ := (eval_verifier (oracleB f) x w).1 hw
      exact ⟨w, h1, h2⟩

/-! ### The language is not in `P^B` -/

/-- At the stage of the machine `t = f e`, the run of `t` on `1^n` with the finite oracle of the
stage is the run with the oracle `B`. -/
theorem run_stage_eq (e : ℕ) :
    run (oracleB f) (f e) [unary (diagLen f e)]
      = run (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] := by
  refine (run_congr (f e) (oracleOf (stage f e).1) (oracleB f) _ ?_).symm
  intro q hq
  have hqlen : q.length ≤ qlen (f e) (diagLen f e) :=
    qlen_unary (f e) (oracleOf (stage f e).1) (diagLen f e) q hq
  have hq1 : q.length ≤ (stage f (e + 1)).2 := le_trans hqlen (qlen_le_stage_succ f e)
  by_cases hmem : q ∈ (stage f e).1
  · have h1 : oracleOf (stage f e).1 q = true := by simp [oracleOf, hmem]
    have h2 : oracleB f q = true := oracleB_of_mem f hmem
    rw [h1, h2]
  · have hnot : q ∉ (stage f (e + 1)).1 := by
      by_cases h : eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ []
      · rw [stage_succ_fst_pos f h]
        exact hmem
      · rw [stage_succ_fst_neg f h]
        intro hcon
        rcases List.mem_append.1 hcon with hc | hc
        · exact hmem hc
        · have hwit := witness_spec (f e) (oracleOf (stage f e).1) (diagLen f e)
            (startLen_le_diagLen f e)
          have : q = witness (f e) (oracleOf (stage f e).1) (diagLen f e) := by simpa using hc
          rw [this] at hq
          exact hwit.2 hq
    have h1 : oracleOf (stage f e).1 q = false := by simp [oracleOf, hmem]
    have h2 : oracleB f q = false := by
      rw [oracleB_eq_stage f (e + 1) q hq1]
      simp [oracleOf, hnot]
    rw [h1, h2]

/-- In the accepting branch no word of the diagonal length enters the oracle. -/
theorem no_word_of_diagLen (e : ℕ)
    (h : eval (oracleOf (stage f e).1) (f e) [unary (diagLen f e)] ≠ []) :
    ∀ w : Word, w.length = diagLen f e → oracleB f w = false := by
  intro w hw
  by_cases hB : oracleB f w = true
  · exfalso
    obtain ⟨e', he'⟩ := (oracleB_true_iff f w).1 hB
    have hmem : w ∈ (stage f (e + 1)).1 := by
      rcases Nat.le_total (e + 1) e' with hle | hle
      · refine mem_stage_of_length_le f (e + 1) e' hle w he' ?_
        rw [hw]
        exact diagLen_le_stage_succ f e
      · exact stage_subset_mono f hle he'
    have hmem' : w ∈ (stage f e).1 := by
      rw [stage_succ_fst_pos f h] at hmem
      exact hmem
    have := length_le_of_mem_stage f e w hmem'
    have h2 := lt_diagLen f e
    omega
  · cases hval : oracleB f w with
    | false => rfl
    | true => exact absurd hval hB

/-- **The language is not in `P^B`.** -/
theorem not_inP_rel_langB (hf : Function.Surjective f) : ¬ InP_rel (oracleB f) (langB f) := by
  rintro ⟨t, ht⟩
  obtain ⟨e, rfl⟩ := hf t
  set n := diagLen f e with hn
  have hrun : eval (oracleB f) (f e) [unary n]
      = eval (oracleOf (stage f e).1) (f e) [unary n] := by
    unfold eval
    rw [run_stage_eq f e]
  by_cases h : eval (oracleOf (stage f e).1) (f e) [unary n] ≠ []
  · -- the machine accepts, but no word of that length is in the oracle
    have hacc : langB f (unary n) := (ht (unary n)).2 (by rw [hrun]; exact h)
    obtain ⟨w, hw, hB⟩ := hacc
    have := no_word_of_diagLen f e h w (by simpa using hw)
    rw [this] at hB
    exact Bool.false_ne_true hB
  · -- the machine rejects, but the witness of that length is in the oracle
    have hwit := witness_spec (f e) (oracleOf (stage f e).1) n (startLen_le_diagLen f e)
    have hmem : witness (f e) (oracleOf (stage f e).1) n ∈ (stage f (e + 1)).1 := by
      rw [stage_succ_fst_neg f h, hn]
      simp
    have hin : langB f (unary n) :=
      ⟨witness (f e) (oracleOf (stage f e).1) n, by rw [hwit.1, length_unary],
        oracleB_of_mem f hmem⟩
    have hacc := (ht (unary n)).1 hin
    rw [hrun] at hacc
    exact h hacc

end BGS

/-- **Baker–Gill–Solovay, the separating half: there is an oracle with `P^B ≠ NP^B`.** -/
theorem bgs_different : ∃ B : Oracle, ¬ PeqNP_rel B := by
  obtain ⟨f, hf⟩ := CobQ.exists_enumeration
  refine ⟨BGS.oracleB f, fun hcon => ?_⟩
  exact BGS.not_inP_rel_langB f hf (hcon _ (BGS.inNP_rel_langB f))

end Complexity
