/-
# The reversal loop

`Start/UniformSigGadget.lean` realizes the two halves of *moving one bit* from a word being
consumed to a word being built: `Complexity.Tseitin.selBit`-layers computing `u.tail` and
`Complexity.consHeadW`.  This module runs them together in the loop rule
`Complexity.sigListUniformB_iter`: on a state of two words `(z, b)` the stage takes the head bit
off `z` and puts it in front of `b`, so after `j` rounds the state is
`(x.drop j, (x.take j).reverse)`, and after `k n` rounds — `k n` being the promise the arguments
obey — it is `([], x.reverse)`.

The result is the first *loop over an argument* that this development compiles: the reversal of a
word is a P-uniform family of circuits.  It is also what a bounded recursion on notation needs,
since that recursion consumes the **head** of its argument, so the argument has to be presented
back to front.

Main definitions:

* `Complexity.revStep` — the transition of the loop, on states of two words.

Main results:

* `Complexity.iterate_revStep` — after `j` rounds the state is `(x.drop j, (x.take j).reverse)`;
* `Complexity.sigListUniformB_revStep` — the stage is realized;
* `Complexity.sigUniformB_reverse` — **the reversal of a word is realized**.
-/

import Start.UniformSigGadget
import Start.UniformSigIter

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### The transition -/

/-- The first entry of a nonempty tuple is one of its entries. -/
theorem getD_zero_mem {args : List Word} {r : ℕ} (hlen : args.length = r) (hr : 0 < r) :
    args.getD 0 [] ∈ args := by
  have h0 : 0 < args.length := by omega
  rw [List.getD_eq_getElem _ _ h0]
  exact List.getElem_mem h0


/-- The transition of the reversal loop: the head bit of the first word moves to the front of the
second. -/
def revStep : List (List Word → Word) :=
  [fun st => (st.getD 0 []).tail, fun st => consHeadW (st.getD 0 []) (st.getD 1 [])]

@[simp] theorem length_revStep : revStep.length = 2 := rfl

theorem stepW_revStep (a b : Word) : stepW revStep [a, b] = [a.tail, consHeadW a b] := rfl

/-- `consHeadW` on a suffix of `x` and the reverse of the matching prefix extends the prefix. -/
theorem consHeadW_drop_reverse_take (x : Word) (j : ℕ) :
    consHeadW (x.drop j) ((x.take j).reverse) = (x.take (j + 1)).reverse := by
  by_cases hj : j < x.length
  · have hdrop : x.drop j = x.getD j false :: x.drop (j + 1) := by
      rw [List.getD_eq_getElem _ _ hj, List.drop_eq_getElem_cons hj]
    have htake : x.take (j + 1) = x.take j ++ [x.getD j false] := by
      rw [List.getD_eq_getElem _ _ hj, List.take_add_one, List.getElem?_eq_getElem hj]
      rfl
    rw [hdrop, htake, consHeadW, List.reverse_append]
    rfl
  · have hdrop : x.drop j = [] := List.drop_eq_nil_of_le (by omega)
    have htake : x.take (j + 1) = x.take j := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    rw [hdrop, htake, consHeadW]

/-- **After `j` rounds the loop has moved `j` bits.** -/
theorem iterate_revStep (x : Word) :
    ∀ j : ℕ, (stepW revStep)^[j] [x, []] = [x.drop j, (x.take j).reverse] := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, stepW_revStep, List.tail_drop,
        consHeadW_drop_reverse_take]

/-! ### The stage -/

/-- **The stage of the reversal loop is realized.** -/
theorem sigListUniformB_revStep {m k : ℕ → ℕ} (hkm : ∀ n, k n ≤ m n) {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigListUniformB revStep.length m k revStep := by
  have h0 : SigUniformB 2 m k (fun st : List Word => (st.getD 0 []).tail) :=
    sigUniformB_of_sigUniform (sigUniform_tail (r := 2) (by omega) hm) hkm
  have h1 : SigUniformB 2 m k
      (fun st : List Word => consHeadW (st.getD 0 []) (st.getD 1 [])) :=
    sigUniformB_of_sigUniform (sigUniform_consHead (r := 2) le_rfl hm) hkm
  exact sigListUniformB_cons h0 (sigListUniformB_cons h1 sigListUniformB_nil hm) hm

/-! ### The loop -/

/-- **The reversal of a word is realized**: run the stage for `k n` rounds over the state whose
first entry is the argument and whose second entry is empty. -/
theorem sigUniformB_reverse {r : ℕ} {m k : ℕ → ℕ} (hr : 0 < r) (hkm : ∀ n, k n ≤ m n)
    (hm0 : ∀ n, 0 < m n) {mT kT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true) :
    SigUniformB r m k (fun args => (args.getD 0 []).reverse) := by
  set Ds : List (List Word → Word) :=
    [fun args : List Word => args.getD 0 [], fun _ : List Word => []] with hDs
  set Es : List (List Word → Word) :=
    [fun _ : List Word => [], fun args : List Word => (args.getD 0 []).reverse] with hEs
  have hbase : ∀ args : List Word, Ds.map (fun D => D args) = [args.getD 0 [], []] := by
    intro args; rfl
  have hD : SigListUniformB r m k Ds := by
    refine sigListUniformB_cons
      (sigUniformB_of_sigUniform (sigUniform_proj hr hm) hkm)
      (sigListUniformB_cons (sigUniformB_of_sigUniform (sigUniform_empty hm) hkm)
        sigListUniformB_nil hm) hm
  have hE : SigListUniformB r m k Es := by
    refine sigListUniformB_iter (Ts := revStep) (Ds := Ds) (Es := Es) (K := k) (k' := k)
      (sigListUniformB_revStep hkm hm) hD rfl rfl (by simp [revStep]) hm0 ?_ ?_ (kT := kT) hk hm
    · intro n args hlen hle j _ u hu
      rw [hbase args, iterate_revStep] at hu
      have hx : (args.getD 0 []).length ≤ k n := hle _ (getD_zero_mem hlen hr)
      rcases List.mem_cons.1 hu with rfl | hu
      · exact le_trans (by simp) hx
      · rcases List.mem_cons.1 hu with rfl | hu
        · refine le_trans ?_ hx
          simp
        · simp at hu
    · intro n args hlen hle
      rw [hbase args, iterate_revStep]
      have hx : (args.getD 0 []).length ≤ k n := hle _ (getD_zero_mem hlen hr)
      have hnil : (args.getD 0 []).drop (k n) = [] := List.drop_eq_nil_of_le hx
      have htake : (args.getD 0 []).take (k n) = args.getD 0 [] :=
        List.take_of_length_le hx
      rw [hnil, htake]
      rfl
  have hproj := sigUniformB_getD_of_sigListUniformB (i := 1) (Es := Es) (by simp [hEs]) hE hm
    (k' := k) hkm ?_
  · exact hproj
  · intro n args hlen hle E hE'
    have hx : (args.getD 0 []).length ≤ k n := hle _ (getD_zero_mem hlen hr)
    rcases List.mem_cons.1 hE' with rfl | hE'
    · simp
    · rcases List.mem_cons.1 hE' with rfl | hE'
      · simpa using hx
      · simp at hE'

end Complexity
