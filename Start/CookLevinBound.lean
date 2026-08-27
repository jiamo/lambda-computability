/-
**The witness bound must be part of the uniformity hypothesis.**

`Start/CookLevinExists.lean` isolates `Complexity.PUniformAcceptFamilies` as "the hypothesis that
remains open" for Cook–Levin: *every* Cobham verifier `v` and *every* witness bound `p : ℕ → ℕ`
admit a P-uniform family of acceptance circuits.  This module shows that, as stated, the
hypothesis is **false**, and that it stays false when `p` is required to be monotone and
polynomially bounded — exactly the two conditions that `Complexity.InNP` puts on the witness bound.

The reason is that `p` itself is an arbitrary function.  The `n`-th acceptance circuit reads `p n`
witness bits, so its behaviour on the all-ones input records the parity of `p n`; a P-uniform
description of the family would therefore compute a bit sequence that can be chosen, by
diagonalization against the countably many Cobham terms, to be described by none of them.  The bit
sequence is carried by `p n = 2 * n + b n`, which is monotone and bounded by `2 * n + 1`.

What survives — and what the reduction actually needs — is the same statement with a *standard*
polynomial bound `n ↦ a * (n + 1) ^ k`.  Passing from an arbitrary polynomially bounded `p` to such
a bound is harmless: enlarging the witness field only adds inputs that the verifier rejects.  So
`Complexity.StdUniformAcceptFamilies` still gives NP-hardness of SAT
(`Complexity.npHard_SAT_of_stdUniform`), and it is not refutable by the argument above.

Main definitions:

* `Complexity.CircCode.circOf` — the circuit read back from its code;
* `Complexity.Cob.pariC` — a Cobham term testing the parity of the length of its argument;
* `Complexity.parityVerifier` — the verifier accepting `(x, w)` exactly when `|w|` is odd;
* `Complexity.StdUniformAcceptFamilies` — the corrected uniformity hypothesis, with the witness
  bound a standard polynomial.

Main results:

* `Complexity.CircCode.encCirc_injective` — the code of a circuit determines the circuit;
* `Complexity.not_pUniformAcceptFamilies`, `Complexity.not_pUniformAcceptFamilies_mono` —
  **the open hypothesis of `Start/CookLevinExists.lean` is false**, even for monotone,
  polynomially bounded witness bounds;
* `Complexity.npHard_SAT_of_stdUniform`, `Complexity.npComplete_SAT_of_stdUniform` — **SAT is
  NP-hard, hence NP-complete, under the corrected hypothesis.**
-/

import Start.CookLevinExists

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Sat

/-! ### The code of a circuit determines the circuit -/

namespace CircCode

open Tseitin

theorem encCirc_cons_ne_nil (g : Gate) (C : Circuit) : encCirc (g :: C) ≠ [] := by
  rw [encCirc, encGate_append]
  exact List.cons_ne_nil _ _

theorem lead1_tokS1 (g : Gate) (w : Word) : lead1 (tokS1 g w) = 0 := rfl

/-- The tag of a gate is read off the token it opens. -/
theorem lead1_tokT (g : Gate) (w : Word) : lead1 (tokT g w) = tag g := by
  rw [tokT, lead1_replicate_append, lead1_tokS1, Nat.add_zero]

/-- **The code of a circuit determines the circuit.** -/
theorem encCirc_injective : Function.Injective encCirc := by
  intro C
  induction C with
  | nil =>
      intro D h
      cases D with
      | nil => rfl
      | cons g D => exact absurd h.symm (encCirc_cons_ne_nil g D)
  | cons g C ih =>
      intro D h
      cases D with
      | nil => exact absurd h (encCirc_cons_ne_nil g C)
      | cons hg D =>
          rw [encCirc, encCirc, encGate_append, encGate_append] at h
          have htok : tokT g (encCirc C) = tokT hg (encCirc D) := by
            simpa using h
          have htag : tag g = tag hg := by
            rw [← lead1_tokT g (encCirc C), ← lead1_tokT hg (encCirc D), htok]
          have hgh : g = hg := by
            have h₁ := readGate_tokT g (lead1_encCirc C)
            have h₂ := readGate_tokT hg (lead1_encCirc D)
            rw [← h₁, ← h₂, htag, htok]
          subst hgh
          have hrest : encCirc C = encCirc D := by
            have : encGate g ++ encCirc C = encGate g ++ encCirc D := by
              rw [encGate_append, encGate_append, htok]
            exact List.append_cancel_left this
          rw [ih hrest]

open Classical in
/-- The circuit read back from its code (any word that is not a code decodes to the empty
circuit). -/
noncomputable def circOf (w : Word) : Circuit :=
  if h : ∃ C : Circuit, encCirc C = w then h.choose else []

theorem circOf_encCirc (C : Circuit) : circOf (encCirc C) = C := by
  have hex : ∃ D : Circuit, encCirc D = encCirc C := ⟨C, rfl⟩
  rw [circOf, dif_pos hex]
  exact encCirc_injective hex.choose_spec

end CircCode

/-! ### A verifier testing the parity of the witness length -/

/-- Parity of the length of the first argument, as a Boolean word. -/
def Cob.pariC : Cob :=
  .bRec .empty (Cob.notT (.proj 1)) (Cob.notT (.proj 1)) (.comp (.app true) [.empty])

theorem Cob.eval_pariC (w : Word) (rest : List Word) :
    Cob.pariC.eval (w :: rest) = bw (decide (w.length % 2 = 1)) := by
  induction w with
  | nil => simp [Cob.pariC, bw]
  | cons b w ih =>
      have hbd : ((Cob.comp (.app true) [.empty]).eval ((b :: w) :: rest)).length = 1 := by
        simp
      have hstep : (Cob.notT (Cob.proj 1)).eval
          (w :: Cob.pariC.eval (w :: rest) :: rest) = bw (!decide (w.length % 2 = 1)) := by
        refine Cob.eval_notT ?_
        simpa using ih
      rw [Cob.pariC, Cob.eval_bRec_cons, ← Cob.pariC]
      have hlen : (bw (!decide (w.length % 2 = 1))).length ≤ 1 := by
        cases (decide (w.length % 2 = 1)) <;> simp [bw]
      cases b <;>
        · simp only [if_pos, Bool.false_eq_true, hbd, hstep]
          rw [List.take_of_length_le (by simpa using hlen)]
          rcases Nat.even_or_odd w.length with he | ho
          · have h0 : w.length % 2 = 0 := Nat.even_iff.mp he
            simp [h0, Nat.succ_mod_two_eq_one_iff, bw]
          · have h1 : w.length % 2 = 1 := Nat.odd_iff.mp ho
            simp [h1, Nat.succ_mod_two_eq_zero_iff, bw]

/-- **The verifier that accepts `(x, w)` exactly when the witness has odd length.** -/
def parityVerifier : Cob := .comp Cob.pariC [.proj 1]

theorem eval_parityVerifier (x w : Word) :
    parityVerifier.eval [x, w] = bw (decide (w.length % 2 = 1)) := by
  simp only [parityVerifier, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero]
  exact Cob.eval_pariC w []

theorem parityVerifier_accepts (x w : Word) :
    (parityVerifier.eval [x, w] ≠ []) ↔ w.length % 2 = 1 := by
  rw [eval_parityVerifier]
  by_cases h : w.length % 2 = 1 <;> simp [h, bw]

/-! ### The all-ones input, and the length it presents -/

namespace Tseitin

/-- On an input all of whose first `2 * N` bits are set, the word read off the input has full
length `N`. -/
theorem length_inWord_of_all_true (N : ℕ) (x : Word) (h : ∀ i, i < 2 * N → x.getD i false = true) :
    (inWord N x).length = N := by
  cases N with
  | zero => simp [inWord]
  | succ N =>
      have hle := length_inWord_le (N + 1) x
      have hpres := inWord_pres (N + 1) N x (by omega)
      have hall : (List.range (N + 1)).all (fun j => x.getD (2 * j) false) = true := by
        refine List.all_eq_true.mpr ?_
        intro j hj
        exact h (2 * j) (by have := List.mem_range.mp hj; omega)
      rw [hall] at hpres
      have : N < (inWord (N + 1) x).length := by simpa using hpres
      omega

/-- The all-ones input long enough to present `N` witness bits after the offset `off`. -/
theorem length_inWordAt_replicate (off N M : ℕ) (h : off + 2 * N ≤ M) :
    (inWordAt off N (List.replicate M true)).length = N := by
  rw [inWordAt]
  refine length_inWord_of_all_true N _ (fun i hi => ?_)
  rw [getD_drop_add]
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  rw [if_pos (by omega)]
  rfl

end Tseitin

/-! ### The open hypothesis is false -/

/-- The all-ones input used to probe the `n`-th circuit of a family. -/
def probeInput (n : ℕ) : Word := List.replicate (6 * n + 6) true

/-- **The hypothesis `Complexity.PUniformAcceptFamilies` is false even for monotone, polynomially
bounded witness bounds.**

For the verifier that accepts an odd-length witness, the `n`-th acceptance circuit outputs, on the
all-ones input, the parity of the witness bound `p n`.  Choosing `p n = 2 * n + b n` with `b`
diagonal against the countably many Cobham terms therefore prevents any Cobham term from writing
the descriptions of the family. -/
theorem not_pUniformAcceptFamilies_mono :
    ¬ ∀ (v : Cob) (p : ℕ → ℕ), Monotone p → PolyBound p →
      ∃ cf : ℕ → Tseitin.Circuit,
        (∀ n, Tseitin.wf (cf n)) ∧
        (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
          decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) ∧
        CodeUniform cf := by
  intro H
  obtain ⟨φ, hφ⟩ := exists_surjective_cob
  classical
  set b : ℕ → Bool := fun n =>
    !Tseitin.out (probeInput n) (CircCode.circOf ((φ n).eval [List.replicate n true])) with hb
  set p : ℕ → ℕ := fun n => 2 * n + (if b n then 1 else 0) with hp
  have hmono : Monotone p := by
    intro m n hmn
    have h₁ : (if b m then 1 else 0) ≤ 1 := by split <;> omega
    have h₂ : 0 ≤ (if b n then 1 else 0) := Nat.zero_le _
    have : 2 * m + 1 ≤ 2 * n ∨ m = n := by omega
    rcases this with h | h
    · simp only [hp]; omega
    · subst h; exact le_rfl
  have hpoly : PolyBound p := by
    refine ⟨3, 1, fun n => ?_⟩
    have h₁ : (if b n then 1 else 0) ≤ 1 := by split <;> omega
    simp only [hp]
    nlinarith [Nat.zero_le n]
  obtain ⟨cf, -, hout, gen, hgen⟩ := H parityVerifier p hmono hpoly
  obtain ⟨k, rfl⟩ := hφ gen
  -- the circuit's value on the probe input is the parity of `p k`
  have hlen : (Tseitin.inWordAt (2 * k) (p k) (probeInput k)).length = p k := by
    refine Tseitin.length_inWordAt_replicate _ _ _ ?_
    have h₁ : (if b k then 1 else 0) ≤ 1 := by split <;> omega
    simp only [hp]
    omega
  have hvalue : Tseitin.out (probeInput k) (cf k) = b k := by
    rw [hout k (probeInput k)]
    have hpar : p k % 2 = if b k then 1 else 0 := by
      simp only [hp]
      split <;> omega
    have hacc := parityVerifier_accepts (Tseitin.inWord k (probeInput k))
      (Tseitin.inWordAt (2 * k) (p k) (probeInput k))
    rw [hlen] at hacc
    cases hbk : b k with
    | false =>
        refine decide_eq_false ?_
        rw [hacc, hpar, hbk]
        simp
    | true =>
        refine decide_eq_true ?_
        rw [hacc, hpar, hbk]
        simp
  -- but the diagonal bit was chosen to differ from it
  have hcode : (φ k).eval [List.replicate k true] = CircCode.encCirc (cf k) := by
    have := hgen (List.replicate k true)
    rwa [List.length_replicate] at this
  have hdiag : b k = !Tseitin.out (probeInput k) (cf k) := by
    rw [hb]
    simp only
    rw [hcode, CircCode.circOf_encCirc]
  rw [hvalue] at hdiag
  exact (Bool.eq_not_self (b k)).mp hdiag

/-- **The hypothesis isolated in `Start/CookLevinExists.lean` is false.** -/
theorem not_pUniformAcceptFamilies : ¬ PUniformAcceptFamilies := by
  intro H
  exact not_pUniformAcceptFamilies_mono fun v p _ _ => H v p

/-! ### The corrected hypothesis -/

/-- **P-uniform compilation of verifiers, with a standard polynomial witness bound.**

This is `Complexity.PUniformAcceptFamilies` with the arbitrary bound `p` replaced by
`n ↦ a * (n + 1) ^ k`.  The replacement costs nothing — a language in NP has a polynomially
bounded witness bound, and enlarging the witness field only adds inputs the verifier rejects —
and it removes the information smuggled in by an arbitrary `p`, which
`Complexity.not_pUniformAcceptFamilies_mono` shows makes the hypothesis false. -/
def StdUniformAcceptFamilies : Prop :=
  ∀ (v : Cob) (a k : ℕ), ∃ cf : ℕ → Tseitin.Circuit,
    (∀ n, Tseitin.wf (cf n)) ∧
    (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
      decide (v.eval [Tseitin.inWord n x,
        Tseitin.inWordAt (2 * n) (a * (n + 1) ^ k) x] ≠ [])) ∧
    CodeUniform cf

/-- **SAT is NP-hard under the corrected uniformity hypothesis.** -/
theorem npHard_SAT_of_stdUniform (H : StdUniformAcceptFamilies) : NPHard Sat.SAT := by
  intro L hL
  obtain ⟨v, p, ⟨a, k, hak⟩, -, hwit, hacc⟩ := hL
  obtain ⟨cf, hwf, hout, hcode⟩ := H v a k
  exact polyManyOne_SAT_of_acceptFamily hwf hout (lengthUniform_of_codeUniform hcode)
    (fun x w hxw => le_trans (hwit x w hxw) (hak x.length)) hacc

/-- **Cook–Levin under the corrected uniformity hypothesis**: SAT is NP-complete. -/
theorem npComplete_SAT_of_stdUniform (H : StdUniformAcceptFamilies) : NPComplete Sat.SAT :=
  ⟨Sat.inNP_SAT, npHard_SAT_of_stdUniform H⟩

/-- Under the corrected hypothesis, `P = NP` is equivalent to `SAT ∈ P`. -/
theorem peqNP_iff_inP_SAT_of_stdUniform (H : StdUniformAcceptFamilies) :
    PeqNP ↔ InP Sat.SAT :=
  ⟨fun h => h _ Sat.inNP_SAT,
    fun h => peqNP_of_npComplete_of_inP (npComplete_SAT_of_stdUniform H) h⟩

end Complexity
