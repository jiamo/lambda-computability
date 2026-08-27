/-
# The loop rule at the level of signals

`Start/UniformIterate.lean` stacks copies of a circuit over a base and proves the stack P-uniform;
`Start/UniformSigBound.lean` says what it means for a family of circuits to *realize a word
function* on wires.  This module joins the two: it reads the stack as a loop on **tuples of
words**.

A *state* is a tuple of `s` words, presented on the wires as the signals of its entries laid side
by side (`Complexity.Tseitin.encArgs`).  A *stage* is a P-uniform family realizing a list of `s`
word functions of `s` arguments — that is, a transition on states — and a *base* is a P-uniform
family realizing a list of `s` word functions of the `r` real arguments, the initial state.  The
rule `Complexity.sigListUniformB_iter` then says: stacking `K n` copies of the stage over the base
realizes the `K n`-th iterate of the transition, provided the entries of the intermediate states
stay inside the promise the stage was given, and provided the iterate settles on a list of
functions that does not depend on `n`.

`Complexity.sigUniformB_getD_of_sigListUniformB` reads a single entry off a realized tuple, which
is how a loop is used: run it, then project out the component that carries the answer.

Main definitions:

* `Complexity.stepW` — the transition on states denoted by a list of word functions.

Main results:

* `Complexity.stepC_encArgs` — one copy of the stage performs one transition;
* `Complexity.iterate_stepC_encArgs` — `j` copies perform `j` transitions;
* `Complexity.sigListUniformB_iter` — **the loop is realized**;
* `Complexity.sigUniformB_getD_of_sigListUniformB` — an entry of a realized tuple is realized.
-/

import Start.UniformIterate
import Start.UniformSigBound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### The transition on states -/

/-- The transition on tuples of words denoted by a list of word functions: the new state is the
tuple of their values at the old one. -/
def stepW (Ts : List (List Word → Word)) (st : List Word) : List Word := Ts.map (fun T => T st)

@[simp] theorem length_stepW (Ts : List (List Word → Word)) (st : List Word) :
    (stepW Ts st).length = Ts.length := by simp [stepW]

theorem length_iterate_stepW (Ts : List (List Word → Word)) {st : List Word}
    (h : st.length = Ts.length) : ∀ j, ((stepW Ts)^[j] st).length = Ts.length := by
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih => rw [Function.iterate_succ_apply', length_stepW]

/-! ### One copy of the stage is one transition -/

/-- **A stage performs one transition**: its step function, read on the signals of a state, is the
transition the stage denotes. -/
theorem stepC_encArgs {m k' : ℕ → ℕ} {Ts : List (List Word → Word)} {cT : ℕ → Tseitin.Circuit}
    (hT : Tseitin.SigListFamB Ts.length m k' Ts cT) (n : ℕ) {st : List Word}
    (hlen : st.length = Ts.length) (hle : ∀ u ∈ st, u.length ≤ k' n) :
    Tseitin.stepC (cT n) (Ts.length * (2 * m n)) (encArgs (m n) st)
      = encArgs (m n) (stepW Ts st) := by
  rw [Tseitin.stepC]
  exact hT.outC n st hlen hle

/-- **`j` copies of the stage perform `j` transitions.** -/
theorem iterate_stepC_encArgs {m k' : ℕ → ℕ} {Ts : List (List Word → Word)}
    {cT : ℕ → Tseitin.Circuit} (hT : Tseitin.SigListFamB Ts.length m k' Ts cT) (n : ℕ)
    {st : List Word} (hlen : st.length = Ts.length) :
    ∀ J : ℕ, (∀ j < J, ∀ u ∈ (stepW Ts)^[j] st, u.length ≤ k' n) →
      (Tseitin.stepC (cT n) (Ts.length * (2 * m n)))^[J] (encArgs (m n) st)
        = encArgs (m n) ((stepW Ts)^[J] st) := by
  intro J
  induction J with
  | zero => intro _; simp
  | succ J ih =>
      intro hinv
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih (fun j hj => hinv j (by omega))]
      exact stepC_encArgs hT n (length_iterate_stepW Ts hlen J)
        (hinv J (by omega))

/-! ### The loop -/

/-- **The loop is realized.**  Stacking `K n` copies of a stage — a P-uniform family realizing a
transition on states of `s` words — over a base realizing the initial state gives a P-uniform
family realizing the `K n`-th iterate of the transition, provided the entries of the intermediate
states obey the promise made to the stage (`hinv`) and the iterate settles on a fixed list of
functions (`hstab`). -/
theorem sigListUniformB_iter {r : ℕ} {m k k' K : ℕ → ℕ}
    {Ts Ds Es : List (List Word → Word)}
    (hT : SigListUniformB Ts.length m k' Ts) (hD : SigListUniformB r m k Ds)
    (hDlen : Ds.length = Ts.length) (hElen : Es.length = Ts.length)
    (hTne : Ts ≠ []) (hm0 : ∀ n, 0 < m n)
    (hinv : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      ∀ j < K n, ∀ u ∈ (stepW Ts)^[j] (Ds.map (fun D => D args)), u.length ≤ k' n)
    (hstab : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      (stepW Ts)^[K n] (Ds.map (fun D => D args)) = Es.map (fun E => E args))
    {kT mT : Cob}
    (hK : ∀ x : Word, kT.eval [x] = List.replicate (K x.length) true)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigListUniformB r m k Es := by
  obtain ⟨cT, hT⟩ := hT
  obtain ⟨cD, hD⟩ := hD
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  obtain ⟨wT, hwT⟩ := exists_mulConstT (k := fun n => 2 * m n) Ts.length htwo
  set w : ℕ → ℕ := fun n => Ts.length * (2 * m n) with hw
  have hTpos : 0 < Ts.length := List.length_pos_iff.2 hTne
  have hwpos : ∀ n, 0 < w n := by
    intro n
    have := hm0 n
    simp only [hw]
    exact Nat.mul_pos hTpos (by omega)
  have hwD : ∀ n, w n ≤ (cD n).length := by
    intro n
    have := hD.widthC n
    rw [hDlen] at this
    exact this
  have hwB : ∀ n, w n ≤ (cT n).length := hT.widthC
  have hinpB : ∀ n, Tseitin.inpsLt (w n) (cT n) := hT.inpC
  refine ⟨fun n => Tseitin.iterC (cT n) (cD n) (w n) (K n), ?_⟩
  refine ⟨fun n => Tseitin.wf_iterC (hT.wfC n) (hD.wfC n) (hinpB n) (hwD n) (K n), ?_, ?_, ?_, ?_⟩
  · -- only the wires of the argument signals are read
    intro n
    induction K n with
    | zero => exact hD.inpC n
    | succ j ih =>
        rw [Tseitin.iterC_succ]
        intro g hg
        rcases List.mem_append.1 hg with hg' | hg'
        · exact Tseitin.inpsLt_reroute _ _ _ _ g hg'
        · exact ih g hg'
  · -- there is room for the output
    intro n
    rw [Tseitin.length_iterC, hElen]
    have := hwD n
    simp only [hw] at *
    omega
  · -- the descriptions
    exact codeUniform_iterC hT.codeC hD.codeC hT.wfC hinpB hwB
      (fun n => lt_of_lt_of_le (hwpos n) (hwB n)) hK hwT
  · -- the value
    intro n args hlen hle
    have hstate := Tseitin.state_iterC (hT.wfC n) (hinpB n) (hwD n) (hwB n)
      (encArgs (m n) args) (K n)
    have hbase : Tseitin.topVals (w n) (vals (encArgs (m n) args) (cD n))
        = encArgs (m n) (Ds.map (fun D => D args)) := by
      have := hD.outC n args hlen hle
      rw [hDlen] at this
      exact this
    have hlen0 : (Ds.map (fun D => D args)).length = Ts.length := by simp [hDlen]
    have hit := iterate_stepC_encArgs hT n hlen0 (K n) (hinv n args hlen hle)
    have hgoal : Tseitin.topVals (w n)
        (vals (encArgs (m n) args) (Tseitin.iterC (cT n) (cD n) (w n) (K n)))
        = encArgs (m n) (Es.map (fun E => E args)) := by
      have hst : Tseitin.topVals (w n)
          (vals (encArgs (m n) args) (Tseitin.iterC (cT n) (cD n) (w n) (K n)))
          = Tseitin.stateC (encArgs (m n) args) (cT n) (cD n) (w n) (K n) := rfl
      rw [hst, hstate, hbase, hit, hstab n args hlen hle]
    rw [hElen]
    exact hgoal

/-! ### Reading an entry off a realized tuple -/

/-- **An entry of a realized tuple is realized**: put the projection family on top of the family
realizing the tuple. -/
theorem sigUniformB_getD_of_sigListUniformB {r i : ℕ} {m k : ℕ → ℕ}
    {Es : List (List Word → Word)} (hi : i < Es.length) (hE : SigListUniformB r m k Es)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    {k' : ℕ → ℕ} (hk'm : ∀ n, k' n ≤ m n)
    (hbnd : ∀ (n : ℕ) (args : List Word), args.length = r →
      (∀ u ∈ args, u.length ≤ k n) → ∀ E ∈ Es, (E args).length ≤ k' n) :
    SigUniformB r m k (fun args => (Es.map (fun E => E args)).getD i []) := by
  have hproj : SigUniformB Es.length m k' (fun st => st.getD i []) :=
    sigUniformB_of_sigUniform (sigUniform_proj hi hm) hk'm
  exact sigUniformB_comp (k' := k') hproj hE hbnd hm

/-! ### An example -/

/-- A loop of `n + 1` rounds on a state of one word: it starts at the argument, and its stage
erases the state, so after any positive number of rounds the state is the empty word.  The point of
the example is that the hypotheses of the loop rule are satisfiable. -/
example : SigListUniformB 1 (fun n => n + 1) (fun n => n) [fun _ : List Word => []] := by
  set lenT : Cob := .comp .smash [Cob.proj 0, Cob.constT [true]] with hlenT
  have hlenTn : ∀ x : Word, lenT.eval [x] = List.replicate x.length true := by
    intro x; simp [hlenT]
  set mT : Cob := .comp (.app true) [lenT] with hmT
  have hm : ∀ x : Word, mT.eval [x] = List.replicate (x.length + 1) true := by
    intro x
    simp [hmT, hlenTn x, List.replicate_succ]
  refine sigListUniformB_iter (Ts := [fun _ : List Word => []])
    (Ds := [fun args : List Word => args.getD 0 []]) (K := fun n => n + 1) (k' := fun n => n)
    ?_ ?_ rfl rfl (by simp) (fun n => Nat.succ_pos n) ?_ ?_ (kT := mT) hm hm
  · exact sigListUniformB_cons
      (sigUniformB_of_sigUniform (sigUniform_empty hm) (fun n => by omega))
      sigListUniformB_nil hm
  · exact sigListUniformB_cons
      (sigUniformB_of_sigUniform (sigUniform_proj Nat.one_pos hm) (fun n => by omega))
      sigListUniformB_nil hm
  · intro n args hlen hle j _ u hu
    cases j with
    | zero =>
        simp only [Function.iterate_zero, id_eq, List.map_cons, List.map_nil,
          List.mem_singleton] at hu
        subst hu
        rcases args with _ | ⟨a, rest⟩
        · simp at hlen
        · rcases rest with _ | ⟨b, rest⟩
          · simpa using hle a (by simp)
          · simp at hlen
    | succ j =>
        rw [Function.iterate_succ_apply'] at hu
        simp only [stepW, List.map_cons, List.map_nil, List.mem_singleton] at hu
        simp [hu]
  · intro n args _ _
    rw [Function.iterate_succ_apply']
    simp [stepW]

end Complexity
