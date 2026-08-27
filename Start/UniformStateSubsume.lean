/-
# The poly-state rule subsumes the finite automata and the uniform symmetric languages

`Start/UniformStateCode.lean` proves that the language of an automaton with polynomially many
states, whose data is computed in unary by Cobham terms, is decided by a P-uniform circuit family.
This module checks that the two earlier families of examples are instances of that rule:

* a **finite automaton** with `m` states is a poly-state automaton whose number of states does not
  depend on the length of the input; its transition function and its accepting set are finite
  tables, hence Cobham-computable by `Cob.tableSel`;
* a **symmetric language** with a Cobham-decidable count predicate is the language of the counting
  automaton, whose state is the number of `true` bits read so far, capped at the length of the
  input, so that it has `n + 1` states.

Main results:

* `Complexity.pUniformDecidable_autoLang_of_state` — a second proof of
  `Complexity.pUniformDecidable_autoLang`, through the poly-state rule;
* `Complexity.pUniformDecidable_symLang_of_state` — a second proof of
  `Complexity.pUniformDecidable_symLang`, through the poly-state rule.
-/
import Start.UniformStateCode
import Start.CobhamTransducer

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Selecting from a finite table -/

/-- A finite table of unary values, selected by the first argument in unary. -/
def tabU (m : ℕ) (f : ℕ → ℕ) : Cob :=
  Cob.tableSel ((List.range m).map fun t => Cob.constT (List.replicate (f t) true)) (.proj 0)

/-- A finite table of Boolean values, selected by the first argument in unary. -/
def tabB (m : ℕ) (g : ℕ → Bool) : Cob :=
  Cob.tableSel ((List.range m).map fun t => Cob.constT (bw (g t))) (.proj 0)

theorem eval_tabU (m : ℕ) (f : ℕ → ℕ) (s p : ℕ) :
    (tabU m f).eval [List.replicate s true, List.replicate p true]
      = List.replicate (if s < m then f s else 0) true := by
  rw [tabU, Cob.eval_tableSel _ _ _ s (by simp)]
  by_cases hs : s < m
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, if_pos hs]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hs), if_neg hs]
    simp

theorem eval_tabB (m : ℕ) (g : ℕ → Bool) (s p : ℕ) :
    (tabB m g).eval [List.replicate s true, List.replicate p true]
      = bw (if s < m then g s else false) := by
  rw [tabB, Cob.eval_tableSel _ _ _ s (by simp)]
  by_cases hs : s < m
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, if_pos hs]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hs), if_neg hs]
    simp

/-! ### Finite automata -/

section Auto

variable {m : ℕ} {δ : ℕ → Bool → ℕ} {ac : ℕ → Bool}

/-- The transition function of a finite automaton, read as a poly-state one: outside the states of
the automaton it is sent to the initial state. -/
def autoDelta (m : ℕ) (δ : ℕ → Bool → ℕ) : ℕ → ℕ → Bool → ℕ :=
  fun _ s b => if s < m then δ s b else 0

/-- The accepting states of a finite automaton, read as a poly-state one. -/
def autoAc (m : ℕ) (ac : ℕ → Bool) : ℕ → ℕ → Bool := fun _ s => if s < m then ac s else false

theorem autoDelta_lt (hm : 0 < m) (hδ : ∀ s b, δ s b < m) (n s : ℕ) (b : Bool) :
    autoDelta m δ n s b < m := by
  rw [autoDelta]
  split_ifs with h
  · exact hδ s b
  · exact hm

/-- On the states of the automaton the two transition functions agree, and the run stays inside
the states. -/
theorem foldl_autoDelta (hδ : ∀ s b, δ s b < m) (n : ℕ) : ∀ (p : Word) (k : ℕ), k < m →
    p.foldl (fun s b => autoDelta m δ n s b) k = p.foldl (fun s b => δ s b) k
      ∧ p.foldl (fun s b => δ s b) k < m := by
  intro p
  induction p with
  | nil => intro k hk; exact ⟨rfl, hk⟩
  | cons b t ih =>
      intro k hk
      have h1 : autoDelta m δ n k b = δ k b := by rw [autoDelta, if_pos hk]
      rw [List.foldl_cons, List.foldl_cons, h1]
      exact ih (δ k b) (hδ k b)

/-- **A finite automaton is a poly-state automaton.** -/
theorem stateLang_autoDelta (hm : 0 < m) (hδ : ∀ s b, δ s b < m) :
    StateLang (autoDelta m δ) (autoAc m ac) = AutoLang δ ac := by
  funext x
  obtain ⟨h1, h2⟩ := foldl_autoDelta hδ x.length x 0 hm
  simp only [StateLang, AutoLang, h1, autoAc, if_pos h2]

/-- Its data is Cobham-computable in unary: the tables are finite. -/
theorem stateUniform_auto (hm : 0 < m) (hδ : ∀ s b, δ s b < m) :
    StateUniform (autoDelta m δ) (autoAc m ac) := by
  refine ⟨fun _ => m, Cob.constT (List.replicate m true), tabU m (fun s => δ s false),
    tabU m (fun s => δ s true), tabB m ac, fun _ => hm, autoDelta_lt hm hδ,
    fun x => by simp, fun s p => ?_, fun s p => ?_, fun s p => ?_⟩
  · rw [eval_tabU, autoDelta]
  · rw [eval_tabU, autoDelta]
  · rw [eval_tabB, autoAc]

/-- **The language of a finite automaton is decided by a P-uniform circuit family**, as an
instance of the poly-state rule. -/
theorem pUniformDecidable_autoLang_of_state (hm : 0 < m) (hδ : ∀ s b, δ s b < m) :
    PUniformDecidable (AutoLang δ ac) := by
  rw [← stateLang_autoDelta (ac := ac) hm hδ]
  exact pUniformDecidable_stateLang (stateUniform_auto hm hδ)

end Auto

/-! ### Symmetric languages -/

section Sym

/-- The counting automaton: the state is the number of `true` bits read so far, capped at the
length of the input so that it really has `n + 1` states. -/
def countDelta : ℕ → ℕ → Bool → ℕ := fun n s b => if b then min (s + 1) n else min s n

/-- On a word short enough for the cap never to bite, the counting automaton counts. -/
theorem foldl_countDelta (n : ℕ) : ∀ (p : Word) (k : ℕ), k + p.length ≤ n →
    p.foldl (fun s b => countDelta n s b) k = k + p.count true := by
  intro p
  induction p with
  | nil => intro k _; simp
  | cons b t ih =>
      intro k hk
      have hlen : k + 1 + t.length ≤ n := by simp at hk; omega
      cases b with
      | true =>
          have hstep : countDelta n k true = k + 1 := by
            rw [countDelta, if_pos rfl, Nat.min_eq_left (by omega)]
          rw [List.foldl_cons, hstep, ih (k + 1) hlen, List.count_cons]
          simp
          omega
      | false =>
          have hstep : countDelta n k false = k := by
            rw [countDelta, if_neg (by simp), Nat.min_eq_left (by omega)]
          rw [List.foldl_cons, hstep, ih k (by omega), List.count_cons]
          simp

/-- **A symmetric language is the language of the counting automaton.** -/
theorem stateLang_countDelta (acc : ℕ → ℕ → Bool) :
    StateLang countDelta (fun n s => acc n s) = SymLang acc := by
  funext x
  rw [StateLang, SymLang, foldl_countDelta x.length x 0 (by simp), Nat.zero_add]

/-- The unary minimum of two terms. -/
def minU (a b : Cob) : Cob := .comp Cob.dropU [.comp Cob.dropU [b, a], a]

theorem eval_minU {a b : Cob} {args : List Word} {u v : ℕ}
    (ha : a.eval args = List.replicate u true) (hb : b.eval args = List.replicate v true) :
    (minU a b).eval args = List.replicate (min u v) true := by
  simp only [minU, Cob.eval_comp, List.map_cons, List.map_nil, ha, hb, Cob.eval_dropU,
    List.length_replicate, List.drop_replicate]
  congr 1
  omega

/-- The data of the counting automaton is Cobham-computable in unary, given a Cobham term for the
count predicate. -/
theorem stateUniform_count {acc : ℕ → ℕ → Bool} (h : CountUniform acc) :
    StateUniform countDelta (fun n s => acc n s) := by
  obtain ⟨accT, hacc⟩ := h
  refine ⟨fun n => n + 1, .comp (.app true) [.comp .smash [.proj 0, Cob.constT [true]]],
    minU (.proj 0) (.proj 1), minU (.comp (.app true) [.proj 0]) (.proj 1), accT,
    fun n => Nat.succ_pos n, ?_, ?_, fun s p => ?_, fun s p => ?_, fun s p => hacc s p⟩
  · intro n s b
    change countDelta n s b < n + 1
    rw [countDelta]
    split_ifs <;> omega
  · intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, Cob.eval_smash,
      Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
      List.length_cons, List.length_nil, List.replicate_succ]
    norm_num
  · have h0 : (Cob.proj 0).eval [List.replicate s true, List.replicate p true]
        = List.replicate s true := by simp
    have h1 : (Cob.proj 1).eval [List.replicate s true, List.replicate p true]
        = List.replicate p true := by simp
    rw [eval_minU h0 h1, countDelta, if_neg (by simp)]
  · have h0 : (Cob.comp (Cob.app true) [Cob.proj 0]).eval
        [List.replicate s true, List.replicate p true] = List.replicate (s + 1) true := by
      simp [List.replicate_succ]
    have h1 : (Cob.proj 1).eval [List.replicate s true, List.replicate p true]
        = List.replicate p true := by simp
    rw [eval_minU h0 h1, countDelta, if_pos rfl]

/-- **Every symmetric language with a Cobham-decidable count predicate is decided by a P-uniform
circuit family**, as an instance of the poly-state rule. -/
theorem pUniformDecidable_symLang_of_state {acc : ℕ → ℕ → Bool} (h : CountUniform acc) :
    PUniformDecidable (SymLang acc) := by
  rw [← stateLang_countDelta acc]
  exact pUniformDecidable_stateLang (stateUniform_count h)

end Sym

end Complexity
