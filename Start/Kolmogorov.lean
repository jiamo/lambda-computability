/-
Kolmogorov complexity for the lambda calculus.

A *program* for a natural number `s` is a closed lambda term that reduces to the Church numeral
`church s`; the length of a program is its syntactic size (`Lambda.size`, the number of syntax
nodes, with a de Bruijn index `i` costing `i + 1`).  The Kolmogorov complexity of `s` is the least
length of a program for it:

  `kolm s = sInf { size t | t closed and t ↠ church s }`.

The definition is well founded because `church s` is itself such a program, so the set is never
empty.

This module proves, from theory already in the repository:

* `Lambda.exists_incompressible` — for every `n` there is an `s` with `n ≤ kolm s`.  Counting: only
  finitely many terms have size at most `n` (`Lambda.finite_setOf_size_le`), and distinct numbers
  need distinct programs, because a term reduces to at most one Church numeral (confluence, via
  `Lambda.unique_church_reduct`).
* `Lambda.not_computablePred_kolm_le` — the relation `kolm s ≤ n` is not decidable, and hence
  `Lambda.not_computable_kolm` — `K` is not a computable function.  This is Berry's paradox, run
  through Kleene's second recursion theorem (`Lambda.exists_code_fixed_point_closed`): if the
  relation were decidable one could compute, from a number `c`, some `s` whose complexity exceeds
  `2 * c + 1`; a self-referential term `X` computing that value from its own code `c = encode X`
  would then be a program for `s` of size `≤ 2 * encode X + 1 < kolm s`.
* Invariance.  Complexity relative to a closed "interpreter" term is treated in
  `Start/KolmogorovMachines.lean` (`Lambda.kolm_le_kolmWith`), as an instance of the generic
  invariance estimate for description systems.
  `Lambda.exists_const_kolm_le_of_partrec` — for every partial recursive
  "description system" `V` there is a constant `c` with `kolm s ≤ 3 * p + c` whenever `V p = s`; the
  factor `3` is the size cost of the *unary* Church numeral for `p` (a compact numeral encoding is
  what an additive-only statement would need, see `Start/KolmogorovBinary.lean` for the logarithmic
  refinement).  Via `TM2Partrec.tm2Computable_iff_partrec` the same holds for Turing machines, so
  the lambda-calculus complexity measure is optimal for machine-generated descriptions as well.
-/

import Start.SecondRecursion
import Start.KolmogorovDef
import Start.KolmogorovMachines
import Start.TM2Capstone
import Mathlib.Computability.Halting

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Only finitely many terms have size at most `n`. -/
theorem finite_setOf_size_le (n : ℕ) : {t : Lambda | size t ≤ n}.Finite := by
  induction n with
  | zero =>
      have hempty : {t : Lambda | size t ≤ 0} = ∅ := by
        ext t
        simpa using (size_pos t).ne'
      rw [hempty]
      exact Set.finite_empty
  | succ m ih =>
      have hsub : {t : Lambda | size t ≤ m + 1} ⊆
          (Lambda.var '' Set.Iic m ∪ Lambda.lam '' {t : Lambda | size t ≤ m}) ∪
            ((fun p : Lambda × Lambda => Lambda.app p.1 p.2) ''
              ({t : Lambda | size t ≤ m} ×ˢ {t : Lambda | size t ≤ m})) := by
        intro t ht
        simp only [Set.mem_ofPred_eq] at ht
        cases t with
        | var i =>
            exact Or.inl (Or.inl ⟨i, by simpa [size] using ht, rfl⟩)
        | lam u =>
            exact Or.inl (Or.inr ⟨u, by simpa [size] using ht, rfl⟩)
        | app a b =>
            refine Or.inr ⟨(a, b), ⟨?_, ?_⟩, rfl⟩
            · have := size_pos b
              simp only [size] at ht
              simp only [Set.mem_ofPred_eq]
              omega
            · have := size_pos a
              simp only [size] at ht
              simp only [Set.mem_ofPred_eq]
              omega
      exact Set.Finite.subset
        (((Set.finite_Iic m).image _ |>.union (ih.image _)).union ((ih.prod ih).image _)) hsub

------------------------------------------------------------------------
-- Incompressible numbers exist
------------------------------------------------------------------------

/-- The value a term reduces to, when it reduces to a Church numeral (junk value `0` otherwise).
Well defined by confluence. -/
def valOf (t : Lambda) : ℕ :=
  open Classical in
  if h : ∃ s : ℕ, Lambda.reduces t (Lambda.church s) then h.choose else 0

theorem valOf_eq {t : Lambda} {s : ℕ} (h : Lambda.reduces t (Lambda.church s)) : valOf t = s := by
  classical
  have hex : ∃ s : ℕ, Lambda.reduces t (Lambda.church s) := ⟨s, h⟩
  rw [valOf, dif_pos hex]
  exact Lambda.unique_church_reduct hex.choose_spec h

/-- Only finitely many numbers have complexity at most `n`. -/
theorem finite_setOf_kolm_le (n : ℕ) : {s : ℕ | kolm s ≤ n}.Finite := by
  refine ((finite_setOf_size_le n).image valOf).subset ?_
  intro s hs
  obtain ⟨t, ht, hsize⟩ := exists_program_of_kolm s
  refine ⟨t, ?_, valOf_eq ht.2⟩
  simp only [Set.mem_ofPred_eq, hsize]
  exact hs

/-- **Incompressible numbers exist**: for every `n` there is an `s` whose shortest program has
size at least `n`. -/
theorem exists_incompressible (n : ℕ) : ∃ s : ℕ, n ≤ kolm s := by
  by_contra hcon
  push Not at hcon
  exact Set.infinite_univ
    ((finite_setOf_kolm_le n).subset (fun s _ => le_of_lt (hcon s)))

------------------------------------------------------------------------
-- Size versus code
------------------------------------------------------------------------

theorem add_le_pair (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs <;> nlinarith

/-- A term's size is bounded by (twice) its code.  This is all the "size accounting" the Berry
argument below needs. -/
theorem size_le_encode (t : Lambda) : size t ≤ 2 * Lambda.encode t + 1 := by
  induction t with
  | var i =>
      have h := add_le_pair 0 i
      simp only [size, Lambda.encode]
      omega
  | app a b iha ihb =>
      have h1 := add_le_pair 1 (Nat.pair (Lambda.encode a) (Lambda.encode b))
      have h2 := add_le_pair (Lambda.encode a) (Lambda.encode b)
      simp only [size, Lambda.encode]
      omega
  | lam u ih =>
      have h := add_le_pair 2 (Lambda.encode u)
      simp only [size, Lambda.encode]
      omega

------------------------------------------------------------------------
-- Berry's paradox: K is not computable
------------------------------------------------------------------------

/-- **The relation `kolm s ≤ n` is undecidable.**  (For each *fixed* `n` the set
`{s | kolm s ≤ n}` is finite, hence decidable; it is the uniform, two-argument relation that is
not.) -/
theorem not_computablePred_kolm_le : ¬ ComputablePred (fun p : ℕ × ℕ => kolm p.1 ≤ p.2) := by
  intro hdec
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp hdec.not
  have hfe' : ∀ s n : ℕ, (¬ kolm s ≤ n) ↔ f (s, n) = Bool.true := by
    intro s n
    exact iff_of_eq (congrFun hfe (s, n))
  -- the search: from `c`, look for a number whose complexity exceeds `2 * c + 1`
  set pr : ℕ → ℕ →. Bool := fun c s => (Part.some (f (s, 2 * c + 1)) : Part Bool)
  have hprPartrec : Partrec₂ pr := by
    have hcomp : Computable fun x : ℕ × ℕ => f (x.2, 2 * x.1 + 1) :=
      hf.comp (Computable.pair Computable.snd
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)).to_comp)
    exact hcomp.partrec
  have hsearch : Partrec fun c => Nat.rfind (pr c) := Partrec.rfind hprPartrec
  have hdom : ∀ c : ℕ, (Nat.rfind (pr c)).Dom := by
    intro c
    obtain ⟨s, hs⟩ := exists_incompressible (2 * c + 2)
    refine Nat.rfind_dom.mpr ⟨s, ?_, fun {_} _ => trivial⟩
    have hne : ¬ kolm s ≤ 2 * c + 1 := by omega
    have hval : pr c s = Part.some (f (s, 2 * c + 1)) := rfl
    rw [hval, (hfe' s (2 * c + 1)).mp hne]
    exact Part.mem_some _
  obtain ⟨G, hGc, hG⟩ := lambdaComputable_of_partrec_closed hsearch
  obtain ⟨X, hXc, hX⟩ := exists_code_fixed_point_closed hGc
  set c : ℕ := Lambda.encode X
  set m : ℕ := (Nat.rfind (pr c)).get (hdom c)
  have hmem : Nat.rfind (pr c) = Part.some m := Part.get_eq_iff_eq_some.mp rfl
  have hbig : ¬ kolm m ≤ 2 * c + 1 := by
    have hspec : Bool.true ∈ pr c m := Nat.rfind_spec (hmem ▸ Part.mem_some m)
    have hval : pr c m = Part.some (f (m, 2 * c + 1)) := rfl
    rw [hval] at hspec
    exact (hfe' m (2 * c + 1)).mpr (Part.mem_some_iff.mp hspec).symm
  have hred : Lambda.reduces (Lambda.app G (Lambda.church c)) (Lambda.church m) :=
    (hG c m).1 hmem
  have hprog : IsProgramFor X m := ⟨hXc, Lambda.reduces_trans hX hred⟩
  have h1 : kolm m ≤ size X := kolm_le_of_isProgramFor hprog
  have h2 : size X ≤ 2 * c + 1 := size_le_encode X
  exact hbig (le_trans h1 h2)

/-- **Kolmogorov complexity is not computable.** -/
theorem not_computable_kolm : ¬ Computable kolm := by
  intro hK
  obtain ⟨_, hprim⟩ := Primrec.nat_le
  have hle : Computable fun q : ℕ × ℕ => decide (q.1 ≤ q.2) :=
    hprim.to_comp.of_eq (fun q => by simp)
  refine not_computablePred_kolm_le (ComputablePred.computable_iff.mpr
    ⟨fun p : ℕ × ℕ => decide (kolm p.1 ≤ p.2), ?_,
      by funext p; exact propext decide_eq_true_iff.symm⟩)
  exact (hle.comp (Computable.pair (hK.comp Computable.fst) Computable.snd)).of_eq
    (fun _ => decide_eq_decide.mpr Iff.rfl)

------------------------------------------------------------------------
-- Invariance
------------------------------------------------------------------------

/-- **Invariance for arbitrary computable description systems.**  If `V` is partial recursive,
thought of as decoding a description `p` into the number `V p`, then lambda-calculus complexity is
below the description length up to a constant factor and an additive constant.  The factor comes
from the unary Church numeral for `p`. -/
theorem exists_const_kolm_le_of_partrec {V : ℕ →. ℕ} (hV : Partrec V) :
    ∃ c : ℕ, ∀ p s : ℕ, V p = Part.some s → kolm s ≤ 3 * p + c := by
  obtain ⟨F, hFc, hF⟩ := lambdaComputable_of_partrec_closed hV
  refine ⟨size F + 4, fun p s hps => ?_⟩
  have hprog : IsProgramFor (Lambda.app F (Lambda.church p)) s :=
    ⟨Lambda.IsClosed_app hFc (Lambda.church_closed p), (hF p s).1 hps⟩
  have := kolm_le_of_isProgramFor hprog
  simp only [size_app, size_church] at this
  omega

/-- The same statement for Turing machines, through the model equivalence. -/
theorem exists_const_kolm_le_of_tm2 {V : ℕ →. ℕ} (hV : TM2Partrec.TM2ComputableNat V) :
    ∃ c : ℕ, ∀ p s : ℕ, V p = Part.some s → kolm s ≤ 3 * p + c :=
  exists_const_kolm_le_of_partrec (TM2Partrec.tm2Computable_iff_partrec.mp hV)

end Lambda
