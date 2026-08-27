/-
**Languages decided by P-uniform circuit families, and their unconditional reduction to SAT.**

`Start/CookLevinExists.lean` shows that the antecedents of the earlier conditional forms of
Cook–Levin are false, and isolates the hypothesis that is actually open
(`Complexity.PUniformAcceptFamilies`): *every* Cobham verifier admits *some* P-uniform family of
acceptance circuits.  This module extracts from that discussion the part that can be proved
outright.

A language is `Complexity.PUniformDecidable` when some P-uniform family of well-formed circuits
decides it: the `n`-th circuit, fed an input that presents a word of length `n` in the paired
format of `Complexity.Tseitin.inWord`, outputs `true` exactly on the members of the language.  No
verifier, no witness, no size bound is involved — the size bound is implied by uniformity, since a
Cobham term writes the whole description.

For such a language the Cook–Levin reduction goes through unconditionally: the formula attached to
`x` is the Tseitin translation of the `|x|`-th circuit with `x` pinned into its input by unit
clauses, and it is satisfiable exactly when `x` is in the language.  The class is also closed
under the Boolean operations, by the circuit algebra of `Start/UniformBool.lean`, and it is not
empty: the language of all-ones words is decided by the conjunction circuits of
`Start/UniformAnd.lean`, so it reduces to SAT.

Main definitions:

* `Complexity.Tseitin.Pinned` — the inputs that present a word of length `n`;
* `Complexity.PUniformDecidable` — decidability by a P-uniform circuit family;
* `Complexity.AllOnes`, `Complexity.SomeOne` — the languages of words all of whose bits are
  `true`, and of words with at least one bit `true`;
* `Complexity.allOnesC`, `Complexity.someOneC` — the families of circuits deciding them.

Main results:

* `Complexity.polyManyOne_SAT_of_pUniformDecidable` — **every P-uniformly decidable language
  reduces to SAT in polynomial time**, unconditionally;
* `Complexity.PUniformDecidable.not`, `Complexity.PUniformDecidable.and`,
  `Complexity.PUniformDecidable.or` — the class is closed under the Boolean operations, and
  `Complexity.pUniformDecidable_true`, `Complexity.pUniformDecidable_false` are its two constants;
* `Complexity.pUniformDecidable_allOnes`, `Complexity.pUniformDecidable_someOne` — **the class is
  inhabited by nontrivial languages**, one built from the conjunction circuits of
  `Start/UniformAnd.lean` and one from the block loop rule of `Start/UniformLoop.lean`;
* `Complexity.polyManyOne_SAT_allOnes`, `Complexity.polyManyOne_SAT_someOne` — hence those
  languages reduce to SAT;
* `Complexity.npHard_SAT_of_pUniformDecidable`, `Complexity.npComplete_SAT_of_pUniformDecidable` —
  SAT is NP-hard, hence NP-complete, as soon as every language in NP is decided by a P-uniform
  family.
-/

import Start.UniformBool
import Start.UniformAnd
import Start.CookLevinExists

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Sat

namespace Tseitin

/-- The circuit inputs that present a word of length `n`: the flag positions `0, 2, …, 2 * n - 2`
are set, so that `Complexity.Tseitin.inWord n` reads off the `n` bits sitting at the odd
positions below `2 * n`. -/
def Pinned (n : ℕ) (y : Word) : Prop := ∀ m, m < n → y.getD (2 * m) false = true

/-- On a pinned input the word read off the input is exactly the list of its odd bits. -/
theorem inWord_of_pinned (n : ℕ) (y : Word) (h : Pinned n y) :
    inWord n y = (List.range n).map (fun i => y.getD (2 * i + 1) false) := by
  set u : Word := (List.range n).map (fun i => y.getD (2 * i + 1) false) with hu
  have hlen : u.length = n := by simp [hu]
  have hget : ∀ i, i < n → u.getD i false = y.getD (2 * i + 1) false := by
    intro i hi
    rw [hu, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have := inWord_eq_of_pinned u y (fun i hi => by
    rw [hlen] at hi
    exact ⟨h i hi, (hget i hi).symm⟩)
  rwa [hlen] at this

end Tseitin

/-! ### Decidability by a P-uniform family -/

/-- **A language is decided by a P-uniform circuit family**: there are well-formed, nonempty
circuits `cf n`, whose descriptions are written from `1^n` by a single Cobham term, such that on
every input presenting a word of length `n` the circuit `cf n` outputs `true` exactly on the
members of the language. -/
def PUniformDecidable (L : Language) : Prop :=
  ∃ cf : ℕ → Tseitin.Circuit,
    (∀ n, cf n ≠ []) ∧
    (∀ n, Tseitin.wf (cf n)) ∧
    (∀ (n : ℕ) (y : Word), Tseitin.Pinned n y →
      (Tseitin.out y (cf n) = true ↔ L (Tseitin.inWord n y))) ∧
    CodeUniform cf

/-- **Every P-uniformly decidable language reduces to SAT in polynomial time.**

This is the Cook–Levin reduction with no hypothesis left over: the reduction sends `x` to the
Tseitin translation of the `|x|`-th circuit together with the unit clauses pinning `x` into its
input, and `Complexity.Tseitin.sat_append_pinCnfW` identifies the satisfying assignments of the
result with the pinned inputs accepted by the circuit. -/
theorem polyManyOne_SAT_of_pUniformDecidable {L : Language} (h : PUniformDecidable L) :
    L ≤ₘᵖ Sat.SAT := by
  obtain ⟨cf, -, hwf, hdec, hcode⟩ := h
  obtain ⟨gen, hgen⟩ := lengthUniform_of_codeUniform hcode
  refine ⟨.comp Cob.concat [gen, Tseitin.pinTerm], fun x => ?_⟩
  have heval : (Cob.comp Cob.concat [gen, Tseitin.pinTerm]).eval [x]
      = Sat.encCnf (Tseitin.toCnf (cf x.length) ++ Tseitin.pinCnfW x) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hgen x,
      Tseitin.eval_pinTerm x, Sat.encCnf_append]
  rw [heval, Sat.SAT_encCnf, Tseitin.sat_append_pinCnfW _ (hwf x.length) x]
  constructor
  · intro hx
    set pre : Word := (List.range (2 * x.length)).map
      (fun i => if i % 2 = 0 then true else x.getD (i / 2) false) with hpre
    have hget : ∀ i, i < 2 * x.length →
        pre.getD i false = if i % 2 = 0 then true else x.getD (i / 2) false := by
      intro i hi
      rw [hpre]
      exact Tseitin.getD_range_map
        (f := fun i => if i % 2 = 0 then true else x.getD (i / 2) false) hi
    have hpin : ∀ m, m < x.length → pre.getD (2 * m) false = true ∧
        pre.getD (2 * m + 1) false = x.getD m false := by
      intro m hm
      refine ⟨?_, ?_⟩
      · rw [hget _ (by omega)]
        simp [Nat.mul_mod_right]
      · rw [hget _ (by omega), if_neg (by omega)]
        congr 1
        omega
    refine ⟨pre, ?_, hpin⟩
    have hw : Tseitin.inWord x.length pre = x := Tseitin.inWord_eq_of_pinned x pre hpin
    exact (hdec x.length pre (fun m hm => (hpin m hm).1)).2 (by rw [hw]; exact hx)
  · rintro ⟨y, hy, hpin⟩
    have hw : Tseitin.inWord x.length y = x := Tseitin.inWord_eq_of_pinned x y hpin
    have := (hdec x.length y (fun m hm => (hpin m hm).1)).1 hy
    rwa [hw] at this

/-! ### Closure under the Boolean operations -/

/-- Deciding a language depends only on its extension. -/
theorem PUniformDecidable.congr {L₁ L₂ : Language} (h : PUniformDecidable L₁)
    (he : ∀ x, L₁ x ↔ L₂ x) : PUniformDecidable L₂ := by
  obtain ⟨cf, hne, hwf, hdec, hcode⟩ := h
  exact ⟨cf, hne, hwf, fun n y hy => (hdec n y hy).trans (he _), hcode⟩

/-- **The everywhere-true language is decided by a P-uniform family.** -/
theorem pUniformDecidable_true : PUniformDecidable (fun _ => True) :=
  ⟨fun _ => [.cst true], fun _ => by simp, fun _ => ⟨trivial, trivial⟩,
    fun _ _ _ => by simp [Tseitin.out, Tseitin.gateVal],
    codeUniform_const [Tseitin.Gate.cst true]⟩

/-- **The empty language is decided by a P-uniform family.** -/
theorem pUniformDecidable_false : PUniformDecidable (fun _ => False) :=
  ⟨fun _ => [.cst false], fun _ => by simp, fun _ => ⟨trivial, trivial⟩,
    fun _ _ _ => by simp [Tseitin.out, Tseitin.gateVal],
    codeUniform_const [Tseitin.Gate.cst false]⟩

/-- **The complement of a P-uniformly decidable language is P-uniformly decidable.** -/
theorem PUniformDecidable.not {L : Language} (h : PUniformDecidable L) :
    PUniformDecidable (fun x => ¬ L x) := by
  obtain ⟨cf, hne, hwf, hdec, hcode⟩ := h
  refine ⟨fun n => Tseitin.negC (cf n), fun n => by simp [Tseitin.negC], fun n =>
    Tseitin.wf_negC (hwf n) (hne n), fun n y hy => ?_, codeUniform_negC hcode⟩
  rw [Tseitin.out_negC y (hne n)]
  rw [Bool.not_eq_true']
  constructor
  · intro hout hL
    exact absurd ((hdec n y hy).2 hL) (by rw [hout]; exact Bool.false_ne_true)
  · intro hL
    cases hb : Tseitin.out y (cf n) with
    | false => rfl
    | true => exact absurd ((hdec n y hy).1 hb) hL

/-- **The intersection of two P-uniformly decidable languages is P-uniformly decidable.** -/
theorem PUniformDecidable.and {L₁ L₂ : Language} (h₁ : PUniformDecidable L₁)
    (h₂ : PUniformDecidable L₂) : PUniformDecidable (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨cf, hne, hwf, hdec, hcode⟩ := h₁
  obtain ⟨cg, hne', hwf', hdec', hcode'⟩ := h₂
  refine ⟨fun n => Tseitin.conjC (cf n) (cg n), fun n => by simp [Tseitin.conjC], fun n =>
    Tseitin.wf_conjC (hwf n) (hwf' n) (hne n) (hne' n), fun n y hy => ?_,
    codeUniform_conjC hcode hcode'⟩
  rw [Tseitin.out_conjC y (hwf n) (hne n) (hne' n), Bool.and_eq_true]
  exact and_congr (hdec n y hy) (hdec' n y hy)

/-- **The union of two P-uniformly decidable languages is P-uniformly decidable.** -/
theorem PUniformDecidable.or {L₁ L₂ : Language} (h₁ : PUniformDecidable L₁)
    (h₂ : PUniformDecidable L₂) : PUniformDecidable (fun x => L₁ x ∨ L₂ x) := by
  obtain ⟨cf, hne, hwf, hdec, hcode⟩ := h₁
  obtain ⟨cg, hne', hwf', hdec', hcode'⟩ := h₂
  refine ⟨fun n => Tseitin.disjC (cf n) (cg n), fun n => by simp [Tseitin.disjC], fun n =>
    Tseitin.wf_disjC (hwf n) (hwf' n) (hne n) (hne' n), fun n y hy => ?_,
    codeUniform_disjC hcode hcode'⟩
  rw [Tseitin.out_disjC y (hwf n) (hne n) (hne' n), Bool.or_eq_true]
  exact or_congr (hdec n y hy) (hdec' n y hy)

/-! ### A nontrivial member of the class -/

/-- The language of words all of whose bits are `true`. -/
def AllOnes : Language := fun x => x.all (fun b => b) = true

/-- The circuits deciding `Complexity.AllOnes`: the conjunction of the first `2 * n` bits of the
circuit input, with a constant gate underneath so that the circuit is never empty. -/
def allOnesC (n : ℕ) : Tseitin.Circuit :=
  Tseitin.stackC (CircCode.andCirc (2 * n)) [.cst true]

theorem allOnesC_zero : allOnesC 0 = [Tseitin.Gate.cst true] := rfl

@[simp] theorem length_allOnesC (n : ℕ) : (allOnesC n).length = 2 * n + 2 * n + 1 := by
  simp [allOnesC]

theorem allOnesC_ne_nil (n : ℕ) : allOnesC n ≠ [] := by
  intro h
  have := length_allOnesC n
  rw [h] at this
  simp at this

theorem wf_andCirc_two_mul (n : ℕ) : Tseitin.wf (CircCode.andCirc (2 * n)) := by
  cases n with
  | zero => exact trivial
  | succ m => exact CircCode.wf_andCirc _ (by omega)

theorem wf_allOnesC (n : ℕ) : Tseitin.wf (allOnesC n) :=
  Tseitin.wf_stackC (wf_andCirc_two_mul n) ⟨trivial, trivial⟩

/-- The running conjunction of a word, as a check over an initial segment. -/
theorem andPrefix_eq_all (y : Word) : ∀ k : ℕ,
    CircCode.andPrefix y k = (List.range (k + 1)).all (fun j => y.getD j false)
  | 0 => by simp [CircCode.andPrefix]
  | k + 1 => by
      rw [CircCode.andPrefix, andPrefix_eq_all y k, List.range_succ (n := k + 1)]
      simp

theorem out_allOnesC (n : ℕ) (y : Word) :
    Tseitin.out y (allOnesC n) = true ↔ ∀ j, j < 2 * n → y.getD j false = true := by
  cases n with
  | zero => simp [allOnesC_zero, Tseitin.out, Tseitin.gateVal]
  | succ m =>
      have hne : CircCode.andCirc (2 * (m + 1)) ≠ [] := by
        intro h
        have := CircCode.length_andCirc (2 * (m + 1))
        rw [h] at this
        simp only [List.length_nil] at this
        omega
      rw [allOnesC, Tseitin.out_stackC y _ (wf_andCirc_two_mul (m + 1)) hne,
        CircCode.out_andCirc y (2 * (m + 1)) (by omega)]
      have h2 : 2 * (m + 1) - 1 + 1 = 2 * (m + 1) := by omega
      rw [andPrefix_eq_all y (2 * (m + 1) - 1), h2]
      simp [List.all_eq_true]

/-- **The all-ones language is decided by a P-uniform circuit family.** -/
theorem pUniformDecidable_allOnes : PUniformDecidable AllOnes := by
  refine ⟨allOnesC, allOnesC_ne_nil, wf_allOnesC, fun n y hy => ?_, ?_⟩
  · rw [out_allOnesC n y, AllOnes, Tseitin.inWord_of_pinned n y hy]
    simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_def]
    constructor
    · intro h i hi
      exact h (2 * i + 1) (by omega)
    · intro h j hj
      rcases Nat.even_or_odd j with he | ho
      · obtain ⟨i, hi⟩ := he
        have : 2 * i = j := by omega
        rw [← this]
        exact hy i (by omega)
      · obtain ⟨i, hi⟩ := ho
        have : 2 * i + 1 = j := by omega
        rw [← this]
        exact h i (by omega)
  · obtain ⟨g, hg⟩ := codeUniform_andCirc
    have hdbl : CodeUniform (fun n => CircCode.andCirc (2 * n)) := by
      refine ⟨.comp g [.comp Cob.concat [.proj 0, .proj 0]], fun x => ?_⟩
      have : (Cob.comp Cob.concat [Cob.proj 0, Cob.proj 0]).eval [x] = x ++ x := by
        simp
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, this, hg (x ++ x),
        List.length_append]
      congr 2
      omega
    exact codeUniform_stack hdbl (codeUniform_const [Tseitin.Gate.cst true])

/-- **A nontrivial language that reduces to SAT**, with no hypothesis: the all-ones language is
decided by a P-uniform family, so the reduction of
`Complexity.polyManyOne_SAT_of_pUniformDecidable` applies to it. -/
theorem polyManyOne_SAT_allOnes : AllOnes ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable pUniformDecidable_allOnes

/-! ### A second member, from the loop rule -/

/-- The language of words with at least one bit `true`. -/
def SomeOne : Language := fun x => x.any (fun b => b) = true

/-- The circuits deciding `Complexity.SomeOne`: the disjunction over the pairs of the circuit
input computed by `Complexity.CircCode.pairCirc`, with a constant gate underneath so that the
circuit is never empty.  On a pinned input the first component of every pair is the flag, which is
`true`, so the disjunction runs over the bits of the word. -/
def someOneC (n : ℕ) : Tseitin.Circuit :=
  Tseitin.stackC (CircCode.pairCirc n) [.cst false]

theorem someOneC_zero : someOneC 0 = [Tseitin.Gate.cst false] := rfl

@[simp] theorem length_someOneC (n : ℕ) : (someOneC n).length = 4 * n + 1 := by
  simp [someOneC]

theorem someOneC_ne_nil (n : ℕ) : someOneC n ≠ [] := by
  intro h
  have := length_someOneC n
  rw [h] at this
  simp at this

theorem wf_someOneC (n : ℕ) : Tseitin.wf (someOneC n) :=
  Tseitin.wf_stackC (CircCode.wf_pairCirc n) ⟨trivial, trivial⟩

theorem out_someOneC (n : ℕ) (y : Word) (hy : Tseitin.Pinned n y) :
    Tseitin.out y (someOneC n) = true ↔ ∃ i, i < n ∧ y.getD (2 * i + 1) false = true := by
  cases n with
  | zero => simp [someOneC_zero, Tseitin.out, Tseitin.gateVal]
  | succ m =>
      have hne : CircCode.pairCirc (m + 1) ≠ [] := by
        intro h
        have := CircCode.length_pairCirc (m + 1)
        rw [h] at this
        simp at this
      rw [someOneC, Tseitin.out_stackC y _ (CircCode.wf_pairCirc (m + 1)) hne,
        CircCode.out_pairCirc_iff y m]
      constructor
      · rintro ⟨i, hi, -, h⟩
        exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, h⟩
        exact ⟨i, by omega, hy i hi, h⟩

/-- **The all-ones language's dual is also decided by a P-uniform circuit family**, this time by
the family produced by the block loop rule of `Start/UniformLoop.lean`. -/
theorem pUniformDecidable_someOne : PUniformDecidable SomeOne := by
  refine ⟨someOneC, someOneC_ne_nil, wf_someOneC, fun n y hy => ?_, ?_⟩
  · rw [out_someOneC n y hy, SomeOne, Tseitin.inWord_of_pinned n y hy]
    simp only [List.any_map, List.any_eq_true, List.mem_range, Function.comp_def]
  · exact codeUniform_stack codeUniform_pairCirc (codeUniform_const [Tseitin.Gate.cst false])

theorem polyManyOne_SAT_someOne : SomeOne ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable pUniformDecidable_someOne

/-! ### NP-hardness, in one more non-vacuous form -/

/-- **SAT is NP-hard as soon as every language in NP is decided by a P-uniform circuit family.**

This is the same conclusion as `Complexity.npHard_SAT_of_pUniform`, from a hypothesis stated
directly about languages rather than about verifiers and witness bounds; like that one, and unlike
the universally quantified antecedents refuted in `Start/CookLevinExists.lean`, it is not vacuous —
`Complexity.pUniformDecidable_allOnes` and `Complexity.pUniformDecidable_someOne` exhibit languages
satisfying its conclusion. -/
theorem npHard_SAT_of_pUniformDecidable (H : ∀ L : Language, InNP L → PUniformDecidable L) :
    NPHard Sat.SAT := fun L hL => polyManyOne_SAT_of_pUniformDecidable (H L hL)

/-- **Cook–Levin, from P-uniform decidability of every NP language.** -/
theorem npComplete_SAT_of_pUniformDecidable (H : ∀ L : Language, InNP L → PUniformDecidable L) :
    NPComplete Sat.SAT :=
  ⟨Sat.inNP_SAT, npHard_SAT_of_pUniformDecidable H⟩

end Complexity
