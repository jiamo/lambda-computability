/-
Kolmogorov complexity does not depend on the representation of λ-terms.

This library carries three interchangeable representations of the untyped λ-calculus (see
`Start/Representation.lean`): de Bruijn terms (`Lambda`), the locally nameless terms of `cslib`
(`Lambda.LNTerm`), and the binary λ-calculus bit strings (`Lambda.bits`).  Kolmogorov complexity
is defined against the first (`Lambda.kolm`, the least *syntactic size* of a closed program) and
against the third (`Lambda.kolmP`, the least *number of bits* of a closed program).  This module
adds the missing measure and settles how the three compare.

* `Lambda.kolmLN` — the least size of a closed **locally nameless** program;
  `Lambda.kolmLN_eq_kolm` proves it *equal* to `Lambda.kolm`, with no constant at all.  Changing
  the term syntax does not change the complexity function: the bijection of
  `Start/Representation.lean` preserves size (`Lambda.sizeLN_toLN`), closedness, and reduction in
  both directions.
* `Lambda.bits_length_eq_size_add_nodes` — the BLC code length of a term is exactly its size plus
  its number of nodes.  This sharpens the two inequalities of `Start/PlainVsPrefix.lean`, which
  give `kolm s ≤ kolmP s ≤ 2 * kolm s`.
* `Lambda.not_exists_const_kolmP_le_kolm_add` — that factor `2` cannot be traded for an additive
  constant: for every `c` there is an `s` with `kolm s + c < kolmP s`.  So invariance "up to an
  additive constant" is a statement about changing the *syntax*; changing the *cost measure*
  genuinely costs a factor.  The proof is a counting argument: only finitely many closed terms
  have at most `c` nodes (`Lambda.finite_closed_nodes_le`), so some `s` has no program with few
  nodes, and every program for it pays `nodes > c` extra bits.
-/

import Start.Kolmogorov
import Start.PlainVsPrefix
import Start.Representation

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Cslib.LambdaCalculus.LocallyNameless.Untyped
open scoped Cslib.LambdaCalculus.LocallyNameless.Untyped.Term

namespace Lambda

/-! ### Size in the locally nameless representation -/

/-- Syntactic size of a locally nameless term, counted exactly as `Lambda.size` counts it for de
Bruijn terms: a bound variable `i` costs `i + 1`, an atom `a` costs `a + 1`, and application and
abstraction cost one node each. -/
def sizeLN : LNTerm → ℕ
  | Term.bvar i => i + 1
  | Term.fvar a => a + 1
  | Term.app l r => sizeLN l + sizeLN r + 1
  | Term.abs m => sizeLN m + 1

@[simp] theorem sizeLN_bvar (i : ℕ) : sizeLN (Term.bvar i : LNTerm) = i + 1 := rfl

@[simp] theorem sizeLN_fvar (a : ℕ) : sizeLN (Term.fvar a : LNTerm) = a + 1 := rfl

@[simp] theorem sizeLN_app (l r : LNTerm) : sizeLN (Term.app l r) = sizeLN l + sizeLN r + 1 := rfl

@[simp] theorem sizeLN_abs (m : LNTerm) : sizeLN (Term.abs m) = sizeLN m + 1 := rfl

/-- **The translation to locally nameless terms preserves size**, as long as every variable of the
source term is bound. -/
theorem sizeLN_toLN (D : ℕ) : ∀ (d : ℕ) (t : Lambda), freeMax t ≤ d →
    sizeLN (toLN D d t) = size t := by
  intro d t
  induction t generalizing d with
  | var i =>
      intro h
      simp only [freeMax_var] at h
      have hi : i < d := by omega
      simp [hi]
  | app a b iha ihb =>
      intro h
      simp only [freeMax_app, max_le_iff] at h
      simp [iha d h.1, ihb d h.2, size]
  | lam u ihu =>
      intro h
      simp only [freeMax_lam] at h
      have hu : freeMax u ≤ d + 1 := by omega
      simp [ihu (d + 1) hu, size]

/-! ### Complexity in the locally nameless representation -/

/-- A *locally nameless program* for `s`: a locally closed term without free atoms that
`cslib`-β-reduces to the (translated) Church numeral of `s`. -/
def IsProgramForLN (M : LNTerm) (s : ℕ) : Prop :=
  M.LC ∧ M.fv = ∅ ∧ M ↠βᶠ toLN 0 0 (church s)

/-- **Kolmogorov complexity in the locally nameless representation**: the least size of a closed
locally nameless program. -/
noncomputable def kolmLN (s : ℕ) : ℕ := sInf {n | ∃ M : LNTerm, IsProgramForLN M s ∧ sizeLN M = n}

theorem isProgramForLN_toLN {t : Lambda} {s : ℕ} (h : IsProgramFor t s) :
    IsProgramForLN (toLN 0 0 t) s := by
  obtain ⟨hclosed, hred⟩ := h
  have hfree : freeMax t = 0 := (isClosed_iff_freeMax_eq_zero t).1 hclosed
  exact ⟨lc_toLN 0 t, fv_toLN_closed t hfree, reduces_toLN hred 0 (by omega)⟩

theorem fv_lt_zero_of_eq_empty {M : LNTerm} (h : M.fv = ∅) : ∀ a ∈ M.fv, a < 0 := by
  intro a ha
  rw [h] at ha
  simp at ha

theorem toLN_ofLN_closed {M : LNTerm} (hlc : M.LC) (hfv : M.fv = ∅) :
    toLN 0 0 (ofLN 0 0 M) = M :=
  toLN_ofLN 0 0 M ((Term.lcAt_iff_LC M).2 hlc) (fv_lt_zero_of_eq_empty hfv)

theorem freeMax_ofLN_closed {M : LNTerm} (hlc : M.LC) (hfv : M.fv = ∅) :
    freeMax (ofLN 0 0 M) = 0 := by
  have := freeMax_ofLN 0 0 M ((Term.lcAt_iff_LC M).2 hlc) (fv_lt_zero_of_eq_empty hfv)
  omega

theorem isProgramFor_ofLN {M : LNTerm} {s : ℕ} (h : IsProgramForLN M s) :
    IsProgramFor (ofLN 0 0 M) s := by
  obtain ⟨hlc, hfv, hred⟩ := h
  have hM : toLN 0 0 (ofLN 0 0 M) = M := toLN_ofLN_closed hlc hfv
  have hfree : freeMax (ofLN 0 0 M) = 0 := freeMax_ofLN_closed hlc hfv
  refine ⟨(isClosed_iff_freeMax_eq_zero _).2 hfree, ?_⟩
  have hred' : toLN 0 0 (ofLN 0 0 M) ↠βᶠ toLN 0 0 (church s) := by rw [hM]; exact hred
  obtain ⟨t', ht', hredt⟩ := reflect_reduces 0 (ofLN 0 0 M) _ (by omega) hred'
  have hchurch : t' = church s := by
    have h1 : ofLN 0 0 (toLN 0 0 t') = t' := by
      refine ofLN_toLN 0 0 t' ?_
      have := freeMax_reduces_le hredt
      omega
    have h2 : ofLN 0 0 (toLN 0 0 (church s)) = church s := by
      refine ofLN_toLN 0 0 (church s) ?_
      have : freeMax (church s) = 0 := (isClosed_iff_freeMax_eq_zero _).1 (church_closed s)
      omega
    rw [← h1, ht', h2]
  rw [← hchurch]
  exact hredt

/-- **Kolmogorov complexity is the same in the de Bruijn and in the locally nameless
representation** — not merely up to an additive constant, but on the nose. -/
theorem kolmLN_eq_kolm (s : ℕ) : kolmLN s = kolm s := by
  apply le_antisymm
  · obtain ⟨t, ht, hsize⟩ := exists_program_of_kolm s
    have hfree : freeMax t = 0 := (isClosed_iff_freeMax_eq_zero t).1 ht.1
    refine Nat.sInf_le ⟨toLN 0 0 t, isProgramForLN_toLN ht, ?_⟩
    rw [sizeLN_toLN 0 0 t (by omega), hsize]
  · have hne : {n | ∃ M : LNTerm, IsProgramForLN M s ∧ sizeLN M = n}.Nonempty :=
      ⟨sizeLN (toLN 0 0 (church s)), toLN 0 0 (church s),
        isProgramForLN_toLN (isProgramFor_church s), rfl⟩
    obtain ⟨M, hM, hsize⟩ := Nat.sInf_mem hne
    have hprog := isProgramFor_ofLN hM
    have hfree : freeMax (ofLN 0 0 M) = 0 := (isClosed_iff_freeMax_eq_zero _).1 hprog.1
    calc kolm s ≤ size (ofLN 0 0 M) := kolm_le_of_isProgramFor hprog
      _ = sizeLN (toLN 0 0 (ofLN 0 0 M)) := (sizeLN_toLN 0 0 _ (by omega)).symm
      _ = sizeLN M := by rw [toLN_ofLN_closed hM.1 hM.2.1]
      _ = kolmLN s := hsize

/-- The bit measure, read in the locally nameless representation, is the bit measure. -/
theorem kolmLN_le_kolmP (s : ℕ) : kolmLN s ≤ kolmP s := by
  rw [kolmLN_eq_kolm]; exact kolm_le_kolmP s

/-- **All three representations give the same complexity function up to a factor two**, and the
two term syntaxes give it exactly. -/
theorem kolmLN_eq_kolm_and_kolmP_bounds (s : ℕ) :
    kolmLN s = kolm s ∧ kolm s ≤ kolmP s ∧ kolmP s ≤ 2 * kolm s :=
  ⟨kolmLN_eq_kolm s, kolm_le_kolmP s, kolmP_le_two_mul_kolm s⟩

/-! ### The bit measure against the size measure -/

/-- The number of syntax nodes of a term (a de Bruijn index counts as one node, however large). -/
def nodes : Lambda → ℕ
  | Lambda.var _ => 1
  | Lambda.app a b => nodes a + nodes b + 1
  | Lambda.lam t => nodes t + 1

@[simp] theorem nodes_var (i : ℕ) : nodes (Lambda.var i) = 1 := rfl

@[simp] theorem nodes_app (a b : Lambda) : nodes (Lambda.app a b) = nodes a + nodes b + 1 := rfl

@[simp] theorem nodes_lam (t : Lambda) : nodes (Lambda.lam t) = nodes t + 1 := rfl

theorem nodes_pos (t : Lambda) : 0 < nodes t := by cases t <;> simp

/-- **The BLC code length of a term is its size plus its number of nodes.**  This is the exact
form of the comparison between the two cost measures. -/
theorem bits_length_eq_size_add_nodes : ∀ t : Lambda, (bits t).length = size t + nodes t := by
  intro t
  induction t with
  | var i => simp [bits, size]
  | app a b iha ihb =>
      simp only [bits, size, nodes_app, List.length_append, List.length_cons, iha, ihb]
      omega
  | lam u ihu =>
      simp only [bits, size, nodes_lam, List.length_cons, ihu]
      omega

/-! ### The factor cannot be replaced by an additive constant -/

/-- A term all of whose free indices are below `d` has size at most quadratic in its number of
nodes. -/
theorem size_le_nodes_mul (d : ℕ) : ∀ t : Lambda, freeMax t ≤ d → size t ≤ nodes t * (d + nodes t)
  | Lambda.var i, h => by
      simp only [freeMax_var] at h
      simp only [size_var, nodes_var, one_mul]
      omega
  | Lambda.app a b, h => by
      simp only [freeMax_app, max_le_iff] at h
      have iha := size_le_nodes_mul d a h.1
      have ihb := size_le_nodes_mul d b h.2
      simp only [size, nodes_app]
      nlinarith [nodes_pos a, nodes_pos b]
  | Lambda.lam u, h => by
      simp only [freeMax_lam] at h
      have ihu := size_le_nodes_mul (d + 1) u (by omega)
      simp only [size, nodes_lam]
      nlinarith [nodes_pos u]

/-- Only finitely many closed terms have at most `c` nodes. -/
theorem finite_closed_nodes_le (c : ℕ) :
    {t : Lambda | freeMax t = 0 ∧ nodes t ≤ c}.Finite := by
  refine Set.Finite.subset (finite_setOf_size_le (c * c)) ?_
  rintro t ⟨hfree, hnodes⟩
  have h := size_le_nodes_mul 0 t (by omega)
  simp only [Nat.zero_add] at h
  exact le_trans h (Nat.mul_le_mul hnodes hnodes)

/-- For every `c` there is a number all of whose programs have more than `c` nodes. -/
theorem exists_nodes_gt (c : ℕ) : ∃ s : ℕ, ∀ t : Lambda, IsProgramFor t s → c < nodes t := by
  have hfin : {s : ℕ | ∃ t : Lambda, IsProgramFor t s ∧ nodes t ≤ c}.Finite := by
    refine Set.Finite.subset ((finite_closed_nodes_le c).image valOf) ?_
    rintro s ⟨t, ht, hn⟩
    exact ⟨t, ⟨(isClosed_iff_freeMax_eq_zero t).1 ht.1, hn⟩, valOf_eq ht.2⟩
  obtain ⟨s, hs⟩ := hfin.infinite_compl.nonempty
  refine ⟨s, fun t ht => ?_⟩
  by_contra hle
  exact hs ⟨t, ht, by omega⟩

/-- For every `c` some number's prefix complexity exceeds its plain complexity by more than
`c`. -/
theorem exists_kolm_add_lt_kolmP (c : ℕ) : ∃ s : ℕ, kolm s + c < kolmP s := by
  obtain ⟨s, hs⟩ := exists_nodes_gt c
  obtain ⟨t, ht, hlen⟩ := exists_program_of_kolmP s
  have h1 : kolm s ≤ size t := kolm_le_of_isProgramFor ht
  have h2 : c < nodes t := hs t ht
  have h3 : (bits t).length = size t + nodes t := bits_length_eq_size_add_nodes t
  exact ⟨s, by omega⟩

/-- **The prefix (BLC) measure is not the plain (size) measure up to an additive constant**: the
factor two of `Lambda.kolmP_le_two_mul_kolm` is essential. -/
theorem not_exists_const_kolmP_le_kolm_add : ¬ ∃ c : ℕ, ∀ s : ℕ, kolmP s ≤ kolm s + c := by
  rintro ⟨c, hc⟩
  obtain ⟨s, hs⟩ := exists_kolm_add_lt_kolmP c
  exact absurd (hc s) (by omega)

end Lambda
