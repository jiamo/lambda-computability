/-
**Creative code sets of the lambda calculus.**

`Start/RiceCreative.lean` shows that a convertibility-invariant class of lambda terms which
contains a term and only solvable terms has a code set that is many-one *above* the halting
problem, and that such a code set is *creative* as soon as it is recursively enumerable.  This
file supplies the missing enumerability half for the concrete classes of the library and reads off
the exact recursion-theoretic classification.

* `Lambda.reduces_of_conv_normal` — convertibility with a normal term is reduction to it;
* `Lambda.conv_church_iff_exists_nstep` — hence convertibility with a Church numeral is exactly
  the leftmost run reaching that numeral, which is the semi-decision procedure;
* `Lambda.rePred_codeSet_conv_church` — the codes of the terms convertible with `church m` form a
  recursively enumerable set;
* `Lambda.creative_codeSet_conv_church`, `Lambda.manyOneEquiv_codeSet_conv_church_haltK` — that
  set is creative, hence many-one equivalent to Kleene's `K` and not simple;
* `Lambda.creative_codeHasNormalForm`, `Lambda.creative_codeConverges` — the lambda-calculus
  halting set and the set of codes converging to a numeral are creative as well.
-/

import Start.RiceCreative
import Start.ScottCurry
import Start.HaltingComplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

------------------------------------------------------------------------
-- Convertibility with a normal term
------------------------------------------------------------------------

/-- A term convertible with a *normal* term already reduces to it. -/
theorem reduces_of_conv_normal {t u : Lambda} (h : Conv t u) (hu : Lambda.is_normal u) :
    Lambda.reduces t u := by
  obtain ⟨v, htv, huv⟩ := h
  rwa [← Lambda.reduces_normal_eq hu huv] at htv

/-- Convertibility with a Church numeral is decided in the limit by the leftmost run. -/
theorem conv_church_iff_exists_nstep (t : Lambda) (m : ℕ) :
    Conv t (Lambda.church m) ↔ ∃ k, nstep^[k] t = Lambda.church m := by
  constructor
  · intro h
    refine ⟨haltTime t, ?_⟩
    exact nf_eq_of_reduces_normal (reduces_of_conv_normal h (Lambda.church_normal m))
      (Lambda.church_normal m)
  · rintro ⟨k, hk⟩
    exact conv_of_reduces (hk ▸ reduces_nstep_iterate t k)

------------------------------------------------------------------------
-- The code set of the terms convertible with a Church numeral is r.e.
------------------------------------------------------------------------

/-- The stage test: after `k` leftmost steps, has the code `c` become the code of `church m`? -/
noncomputable def convChurchTest (m c k : ℕ) : Bool :=
  decide (nstep_code^[k] c = Lambda.church_code m)

theorem convChurchTest_primrec (m : ℕ) : Primrec₂ (convChurchTest m) := by
  have h : PrimrecPred fun p : ℕ × ℕ => nstep_code^[p.2] p.1 = Lambda.church_code m :=
    PrimrecRel.comp (Primrec.eq (α := ℕ))
      (nstep_code_iterate_primrec.comp Primrec.fst Primrec.snd) (Primrec.const _)
  obtain ⟨_inst, h⟩ := h
  exact h.of_eq fun p => by simp [convChurchTest]

theorem codeSet_conv_church_iff_valid_and_test (m c : ℕ) :
    CodeSet (fun t => Conv t (Lambda.church m)) c ↔
      is_valid_code c = Bool.true ∧ ∃ k, convChurchTest m c k = Bool.true := by
  constructor
  · rintro ⟨t, hd, hconv⟩
    have hc : Lambda.encode t = c := encode_of_decode c t hd
    subst hc
    obtain ⟨k, hk⟩ := (conv_church_iff_exists_nstep t m).1 hconv
    refine ⟨is_valid_code_encode t, k, ?_⟩
    simp only [convChurchTest, decide_eq_true_eq, nstep_code_iterate, hk,
      encode_church_eq_church_code]
  · rintro ⟨hv, k, hk⟩
    obtain ⟨t, rfl⟩ := (is_valid_code_iff c).1 hv
    simp only [convChurchTest, decide_eq_true_eq, nstep_code_iterate,
      ← encode_church_eq_church_code] at hk
    exact (codeSet_encode _ t).2
      ((conv_church_iff_exists_nstep t m).2 ⟨k, Lambda.encode_injective hk⟩)

/-- **The codes of the terms convertible with a Church numeral form an r.e. set.** -/
theorem rePred_codeSet_conv_church (m : ℕ) :
    REPred (CodeSet fun t => Conv t (Lambda.church m)) :=
  rePred_of_valid_test (convChurchTest m) (convChurchTest_primrec m)
    (codeSet_conv_church_iff_valid_and_test m)

------------------------------------------------------------------------
-- Creativity
------------------------------------------------------------------------

/-- **The codes of the terms convertible with `church m` form a creative set.** -/
theorem creative_codeSet_conv_church (m : ℕ) :
    Post.Creative (CodeSet fun t => Conv t (Lambda.church m)) :=
  creative_codeSet (convInvariant_conv_church m) (conv_refl _)
    (fun _ h => Solvable.of_conv h.symm (solvable_church m)) (rePred_codeSet_conv_church m)

/-- Hence that set is many-one equivalent to Kleene's halting set. -/
theorem manyOneEquiv_codeSet_conv_church_haltK (m : ℕ) :
    ManyOneEquiv (CodeSet fun t => Conv t (Lambda.church m)) HaltK :=
  (creative_codeSet_conv_church m).manyOneEquiv_haltK

/-- And it is not simple. -/
theorem not_simple_codeSet_conv_church (m : ℕ) :
    ¬ Post.Simple (CodeSet fun t => Conv t (Lambda.church m)) :=
  (creative_codeSet_conv_church m).not_simple

/-- **The lambda-calculus halting set is creative.** -/
theorem creative_codeHasNormalForm : Post.Creative CodeHasNormalForm :=
  Post.creative_of_manyOneComplete rePred_codeHasNormalForm
    fun _ hq => rePred_le_codeHasNormalForm hq

/-- **The set of codes converging to a Church numeral is creative.** -/
theorem creative_codeConverges : Post.Creative CodeConverges :=
  Post.creative_of_manyOneComplete rePred_codeConverges fun _ hq => rePred_le_codeConverges hq

/-- The lambda-calculus halting set is many-one equivalent to Kleene's `K`. -/
theorem manyOneEquiv_codeHasNormalForm_haltK : ManyOneEquiv CodeHasNormalForm HaltK :=
  creative_codeHasNormalForm.manyOneEquiv_haltK

/-- So is the set of codes converging to a Church numeral. -/
theorem manyOneEquiv_codeConverges_haltK : ManyOneEquiv CodeConverges HaltK :=
  creative_codeConverges.manyOneEquiv_haltK

/-- Normalization and convergence to a numeral are many-one equivalent problems. -/
theorem manyOneEquiv_codeHasNormalForm_codeConverges :
    ManyOneEquiv CodeHasNormalForm CodeConverges :=
  creative_codeHasNormalForm.manyOneEquiv creative_codeConverges

end Lambda
