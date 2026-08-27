/-
**The remaining Cook–Levin hypothesis, in its non-vacuous form.**

`Start/CookLevin.lean`, `Start/CookLevinUniform.lean` and `Start/CookLevinCode.lean` derive
NP-hardness of SAT from hypotheses of the shape

  *every* well-formed family of acceptance circuits of polynomial size is P-uniform

(`Complexity.npHard_SAT_of_uniform`, `Complexity.npHard_SAT_of_lengthUniform`,
`Complexity.npHard_SAT_of_codeUniform`).  Those antecedents are **false**, so the implications,
while true, say nothing: a family of circuits may be padded with pairs of negations in a way that
no polynomial-time term can describe.  This module proves that, and replaces the antecedent by the
statement that is actually wanted and actually open here — that *some* such family is P-uniform.

The counterexample is the constantly false circuit `Complexity.Tseitin.falseC j`, a chain of `j`
double negations over the constant `false`: it is well formed, its output is `false` whatever the
input, and it has `2 * j + 1` gates.  Padding it by one double negation or none, as dictated by a
diagonal against the (countable, `Start/CobCountable.lean`) list of Cobham terms, gives a family of
circuits of at most three gates whose description no Cobham term produces.

Main definitions:

* `Complexity.Tseitin.falseC` — the constantly false circuits, of unbounded size;
* `Complexity.Tseitin.diagFam` — the diagonal family;
* `Complexity.PUniformAcceptFamilies` — **the hypothesis that remains open**: every Cobham verifier
  admits *some* P-uniform family of acceptance circuits.

Main results:

* `Complexity.not_forall_uniformlyGenerated`, `Complexity.not_forall_lengthUniform`,
  `Complexity.not_forall_codeUniform` — the antecedents of the earlier conditional forms of
  Cook–Levin are false, hence those implications are vacuous;
* `Complexity.npHard_SAT_of_pUniform`, `Complexity.npComplete_SAT_of_pUniform` — **SAT is NP-hard,
  hence NP-complete, as soon as some acceptance family is P-uniform**: the same conclusions from a
  hypothesis that is not vacuous.
-/

import Start.CookLevinCode
import Start.CobCountable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Sat

namespace Tseitin

/-! ### Constantly false circuits of unbounded size -/

/-- Negating the output of a circuit. -/
theorem out_neg_head (x : Word) (g : Gate) (C : Circuit) :
    out x (Gate.neg C.length :: g :: C) = !(out x (g :: C)) := by
  rw [out, gateVal, vals_cons_getD_length, out]

/-- The constant `false`, under `j` double negations: a well-formed circuit with `2 * j + 1`
gates whose output is `false` on every input. -/
def falseC : ℕ → Circuit
  | 0 => [.cst false]
  | j + 1 => .neg (2 * j + 1) :: .neg (2 * j) :: falseC j

@[simp] theorem length_falseC (j : ℕ) : (falseC j).length = 2 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [falseC, List.length_cons, ih]; omega

theorem wf_falseC (j : ℕ) : wf (falseC j) := by
  induction j with
  | zero => exact ⟨trivial, trivial⟩
  | succ j ih =>
      refine ⟨?_, ?_, ih⟩
      · simp only [gateWf, List.length_cons, length_falseC]; omega
      · simp only [gateWf, length_falseC]; omega

theorem out_falseC (x : Word) (j : ℕ) : out x (falseC j) = false := by
  induction j with
  | zero => rfl
  | succ j ih =>
      obtain ⟨g, C, hgc⟩ : ∃ g C, falseC j = g :: C := by
        cases j with
        | zero => exact ⟨_, _, rfl⟩
        | succ k => exact ⟨_, _, rfl⟩
      have hC : C.length = 2 * j := by
        have h := length_falseC j
        rw [hgc] at h
        simp only [List.length_cons] at h
        omega
      have h₁ : out x (Gate.neg (2 * j) :: falseC j) = !(out x (falseC j)) := by
        rw [hgc, ← hC]
        exact out_neg_head x g C
      have h₂ : out x (falseC (j + 1)) = !(out x (Gate.neg (2 * j) :: falseC j)) := by
        change out x (Gate.neg (2 * j + 1) :: Gate.neg (2 * j) :: falseC j) = _
        rw [← length_falseC j]
        exact out_neg_head x (Gate.neg (2 * j)) (falseC j)
      rw [h₂, h₁, ih]
      rfl

theorem not_csat_falseC (j : ℕ) : ¬ csat (falseC j) := by
  rintro ⟨x, hx⟩
  rw [out_falseC] at hx
  exact Bool.false_ne_true hx

/-! ### The diagonal family -/

/-- The padding of the diagonal family: one double negation exactly when the `n`-th Cobham term
already writes the description of the unpadded circuit. -/
def diagPad (enc : Circuit → Word) (φ : ℕ → Cob) (n : ℕ) : ℕ :=
  if (φ n).eval [List.replicate n true] = enc (falseC 0) then 1 else 0

/-- The diagonal family: constantly false circuits of at most three gates, padded against every
Cobham term in turn. -/
def diagFam (enc : Circuit → Word) (φ : ℕ → Cob) (n : ℕ) : Circuit :=
  falseC (diagPad enc φ n)

theorem wf_diagFam (enc : Circuit → Word) (φ : ℕ → Cob) (n : ℕ) : wf (diagFam enc φ n) :=
  wf_falseC _

theorem out_diagFam (enc : Circuit → Word) (φ : ℕ → Cob) (n : ℕ) (x : Word) :
    out x (diagFam enc φ n) = false := out_falseC _ _

theorem length_diagFam_le (enc : Circuit → Word) (φ : ℕ → Cob) (n : ℕ) :
    (diagFam enc φ n).length ≤ 3 := by
  have : diagPad enc φ n ≤ 1 := by rw [diagPad]; split <;> omega
  rw [diagFam, length_falseC]
  omega

/-- **No Cobham term describes the diagonal family**, for any encoding of circuits that tells the
unpadded circuit from the once-padded one. -/
theorem not_uniform_diagFam (enc : Circuit → Word) {φ : ℕ → Cob} (hφ : Function.Surjective φ)
    (hne : enc (falseC 0) ≠ enc (falseC 1)) :
    ¬ ∃ gen : Cob, ∀ x : Word, gen.eval [x] = enc (diagFam enc φ x.length) := by
  rintro ⟨gen, hgen⟩
  obtain ⟨n, rfl⟩ := hφ gen
  have hx : (List.replicate n true).length = n := List.length_replicate ..
  have h := hgen (List.replicate n true)
  rw [hx, diagFam, diagPad] at h
  by_cases hc : (φ n).eval [List.replicate n true] = enc (falseC 0)
  · rw [if_pos hc] at h
    exact hne (hc.symm.trans h)
  · rw [if_neg hc] at h
    exact hc h

end Tseitin

/-! ### The antecedents of the earlier conditional forms are false -/

theorem encCirc_falseC_ne : CircCode.encCirc (Tseitin.falseC 0) ≠ CircCode.encCirc
    (Tseitin.falseC 1) := by decide

theorem encCnf_toCnf_falseC_ne :
    Sat.encCnf (Tseitin.toCnf (Tseitin.falseC 0)) ≠
      Sat.encCnf (Tseitin.toCnf (Tseitin.falseC 1)) := by decide

/-- **The antecedent of `Complexity.npHard_SAT_of_uniform` is false.**  A family of circuits that
is well formed and unsatisfiable — as it must be for the verifier that accepts nothing — may still
be padded so that no Cobham term writes its Tseitin translation. -/
theorem not_forall_uniformlyGenerated :
    ¬ ∀ (v : Cob) (cc : Word → Tseitin.Circuit), (∀ x, Tseitin.wf (cc x)) →
      (∀ x, Tseitin.csat (cc x) ↔ ∃ w : Word, v.eval [x, w] ≠ []) → UniformlyGenerated cc := by
  intro H
  obtain ⟨φ, hφ⟩ := exists_surjective_cob
  set enc : Tseitin.Circuit → Word := fun C => Sat.encCnf (Tseitin.toCnf C) with henc
  refine Tseitin.not_uniform_diagFam enc hφ encCnf_toCnf_falseC_ne ?_
  exact H .empty (fun x => Tseitin.diagFam enc φ x.length)
    (fun x => Tseitin.wf_diagFam enc φ x.length)
    (fun x => by
      simp only [Cob.eval_empty, ne_eq, not_true_eq_false, exists_const, iff_false]
      exact Tseitin.not_csat_falseC _)

/-- **The antecedent of `Complexity.npHard_SAT_of_lengthUniform` is false.** -/
theorem not_forall_lengthUniform :
    ¬ ∀ (v : Cob) (p : ℕ → ℕ) (cf : ℕ → Tseitin.Circuit),
      (∀ n, Tseitin.wf (cf n)) →
      (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
        decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) →
      (∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ n, (cf n).length ≤ sz n) →
      LengthUniform cf := by
  intro H
  obtain ⟨φ, hφ⟩ := exists_surjective_cob
  set enc : Tseitin.Circuit → Word := fun C => Sat.encCnf (Tseitin.toCnf C) with henc
  refine Tseitin.not_uniform_diagFam enc hφ encCnf_toCnf_falseC_ne ?_
  exact H .empty (fun _ => 0) (Tseitin.diagFam enc φ)
    (Tseitin.wf_diagFam enc φ)
    (fun n x => by rw [Tseitin.out_diagFam]; simp)
    ⟨fun _ => 3, MonoPoly.const 3, Tseitin.length_diagFam_le enc φ⟩

/-- **The antecedent of `Complexity.npHard_SAT_of_codeUniform` is false.** -/
theorem not_forall_codeUniform :
    ¬ ∀ (v : Cob) (p : ℕ → ℕ) (cf : ℕ → Tseitin.Circuit),
      (∀ n, Tseitin.wf (cf n)) →
      (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
        decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) →
      (∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ n, (cf n).length ≤ sz n) →
      CodeUniform cf := by
  intro H
  obtain ⟨φ, hφ⟩ := exists_surjective_cob
  refine Tseitin.not_uniform_diagFam CircCode.encCirc hφ encCirc_falseC_ne ?_
  exact H .empty (fun _ => 0) (Tseitin.diagFam CircCode.encCirc φ)
    (Tseitin.wf_diagFam CircCode.encCirc φ)
    (fun n x => by rw [Tseitin.out_diagFam]; simp)
    ⟨fun _ => 3, MonoPoly.const 3, Tseitin.length_diagFam_le CircCode.encCirc φ⟩

/-! ### The hypothesis that is actually open -/

/-- **The compilation step of Cook–Levin, in its non-vacuous form**: every Cobham verifier `v`
admits, for every witness bound `p`, *some* family of acceptance circuits — well formed, of
polynomial size, reading the instance and the witness off their own input — whose descriptions are
produced by a Cobham term from `1^n`.

Unlike the antecedents refuted above, this is exactly the statement of the P-uniform compilation
of polynomial-time verifiers into circuits, and it is what `Start/CobhamCircuit.lean` and
`Start/CobhamBRec.lean` prove for the circuits alone, without the uniformity. -/
def PUniformAcceptFamilies : Prop :=
  ∀ (v : Cob) (p : ℕ → ℕ), ∃ cf : ℕ → Tseitin.Circuit,
    (∀ n, Tseitin.wf (cf n)) ∧
    (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
      decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) ∧
    CodeUniform cf

/-- The reduction attached to one P-uniform acceptance family: the formula produced from `x` is
the Tseitin translation of the `|x|`-th circuit, with the instance pinned into it by unit
clauses. -/
theorem polyManyOne_SAT_of_acceptFamily {L : Language} {v : Cob} {p : ℕ → ℕ}
    {cf : ℕ → Tseitin.Circuit} (hwf : ∀ n, Tseitin.wf (cf n))
    (hout : ∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
      decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ []))
    (huni : LengthUniform cf)
    (hwit : ∀ x w, v.eval [x, w] ≠ [] → w.length ≤ p x.length)
    (hacc : ∀ x, L x ↔ ∃ w, v.eval [x, w] ≠ []) : L ≤ₘᵖ Sat.SAT := by
  obtain ⟨gen, hgen⟩ := huni
  refine ⟨.comp Cob.concat [gen, Tseitin.pinTerm], fun x => ?_⟩
  have heval : (Cob.comp Cob.concat [gen, Tseitin.pinTerm]).eval [x]
      = Sat.encCnf (Tseitin.toCnf (cf x.length) ++ Tseitin.pinCnfW x) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hgen x,
      Tseitin.eval_pinTerm x, Sat.encCnf_append]
  rw [heval, Sat.SAT_encCnf, Tseitin.sat_append_pinCnfW _ (hwf x.length) x, hacc x]
  constructor
  · rintro ⟨w, hw⟩
    have hwlen : w.length ≤ p x.length := hwit x w hw
    set pre : Word := (List.range (2 * x.length)).map
      (fun i => if i % 2 = 0 then true else x.getD (i / 2) false) with hpre
    have hprelen : pre.length = 2 * x.length := by simp [hpre]
    obtain ⟨y, hytake, hyw⟩ :=
      Tseitin.exists_inWordAt (2 * x.length) (p x.length) w hwlen pre hprelen
    have hyget : ∀ i, i < 2 * x.length → y.getD i false = pre.getD i false :=
      fun i hi => getD_of_take_eq hytake hi
    have hpin : ∀ m, m < x.length → y.getD (2 * m) false = true ∧
        y.getD (2 * m + 1) false = x.getD m false := by
      intro m hm
      have h₁ : 2 * m < 2 * x.length := by omega
      have h₂ : 2 * m + 1 < 2 * x.length := by omega
      have hget : ∀ i, i < 2 * x.length →
          pre.getD i false = if i % 2 = 0 then true else x.getD (i / 2) false := by
        intro i hi
        rw [hpre]
        exact Tseitin.getD_range_map
          (f := fun i => if i % 2 = 0 then true else x.getD (i / 2) false) hi
      refine ⟨?_, ?_⟩
      · rw [hyget _ h₁, hget _ h₁]
        simp [Nat.mul_mod_right]
      · rw [hyget _ h₂, hget _ h₂, if_neg (by omega)]
        congr 1
        omega
    refine ⟨y, ?_, hpin⟩
    rw [hout x.length y, Tseitin.inWord_eq_of_pinned x y hpin, hyw]
    simpa using hw
  · rintro ⟨y, hy, hpin⟩
    have hx : Tseitin.inWord x.length y = x := Tseitin.inWord_eq_of_pinned x y hpin
    rw [hout x.length y, hx] at hy
    exact ⟨_, by simpa using hy⟩

/-- **SAT is NP-hard as soon as some acceptance family is P-uniform.**

This is `Complexity.npHard_SAT_of_codeUniform` with the antecedent put in the form that
`Complexity.not_forall_codeUniform` shows to be necessary: the family is now *chosen* by the
hypothesis rather than quantified over. -/
theorem npHard_SAT_of_pUniform (H : PUniformAcceptFamilies) : NPHard Sat.SAT := by
  intro L hL
  obtain ⟨v, p, -, -, hwit, hacc⟩ := hL
  obtain ⟨cf, hwf, hout, hcode⟩ := H v p
  exact polyManyOne_SAT_of_acceptFamily hwf hout (lengthUniform_of_codeUniform hcode) hwit hacc

/-- **Cook–Levin, modulo P-uniform compilation**: SAT is NP-complete as soon as some acceptance
family is P-uniform.  The `InNP` half is unconditional. -/
theorem npComplete_SAT_of_pUniform (H : PUniformAcceptFamilies) : NPComplete Sat.SAT :=
  ⟨Sat.inNP_SAT, npHard_SAT_of_pUniform H⟩

/-- Under the same hypothesis, `P = NP` is equivalent to `SAT ∈ P`. -/
theorem peqNP_iff_inP_SAT_of_pUniform (H : PUniformAcceptFamilies) : PeqNP ↔ InP Sat.SAT :=
  ⟨fun h => h _ Sat.inNP_SAT,
    fun h => peqNP_of_npComplete_of_inP (npComplete_SAT_of_pUniform H) h⟩

end Complexity
