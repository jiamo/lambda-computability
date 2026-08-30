/-
The Scott–Curry theorem: two disjoint, convertibility-invariant sets of lambda terms have
recursively inseparable code sets.

`Start/Scott.lean` proves Scott's theorem — a non-trivial convertibility-invariant set of terms
has a non-computable code set — by running the supposed decider on a fixed point of the term
`λc. if F c then N else M`.  The same diagonal term proves more: it does not even matter whether
the computable predicate we are testing *is* the code set; it is enough that it separates the
codes of the terms of one invariant set from the codes of the terms of another.  That is the
Scott–Curry theorem, and it has Scott's theorem (hence Rice's theorem for the lambda calculus,
`Lambda.not_computablePred_codeSet`) as the special case `B = fun t => ¬ A t`.

* `Lambda.RecursivelyInseparable` — no computable predicate contains the first set and avoids the
  second one;
* `Lambda.scott_curry` — the theorem in its term form: no computable predicate on codes can
  answer "true" on every term of `A` and "false" on every term of `B`, as soon as `A` and `B` are
  convertibility-invariant and each contains a closed term;
* `Lambda.scott_curry_codeSet` — the same statement phrased as recursive inseparability of the two
  code sets;
* `Lambda.recursivelyInseparable_conv_church` — the concrete instance: the codes of the terms
  convertible with `church m` and the codes of the terms convertible with `church n` are
  recursively inseparable for `m ≠ n`.

Disjointness of `A` and `B` is not needed as a hypothesis: if the two sets meet, no separating
predicate exists for trivial reasons, and the statement below is still exactly "there is no
separating computable predicate".
-/

import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Recursive inseparability
------------------------------------------------------------------------

/-- Two sets of numbers are *recursively inseparable* when no computable predicate contains the
first and is disjoint from the second. -/
def RecursivelyInseparable (A B : ℕ → Prop) : Prop :=
  ¬ ∃ C : ℕ → Prop, ComputablePred C ∧ (∀ n, A n → C n) ∧ (∀ n, B n → ¬ C n)

/-- `C` *separates the codes of* `A` *from the codes of* `B`. -/
def SeparatesCodes (C : ℕ → Prop) (A B : Lambda → Prop) : Prop :=
  (∀ X : Lambda, A X → C (Lambda.encode X)) ∧ (∀ X : Lambda, B X → ¬ C (Lambda.encode X))

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

/-- **The Scott–Curry theorem.**  Let `A` and `B` be sets of lambda terms that are invariant
under convertibility, `A` containing a closed term `M` and `B` a closed term `N`.  Then no
computable predicate on codes separates the codes of the terms of `A` from the codes of the
terms of `B`.

The proof is Curry's diagonal argument.  A closed term `F` deciding the separating predicate is
plugged into `λc. if F c then N else M`, and the second recursion theorem produces a term `X`
that reduces to that term applied to its own code.  If the predicate holds of `⌜X⌝` then `X`
reduces to `N`, so `X ∈ B` and the predicate must fail of `⌜X⌝`; if it fails then `X` reduces to
`M`, so `X ∈ A` and the predicate must hold. -/
theorem scott_curry {A B : Lambda → Prop} (hA : ConvInvariant A) (hB : ConvInvariant B)
    {M N : Lambda} (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N) (hAM : A M) (hBN : B N)
    {C : ℕ → Prop} (hC : ComputablePred C) : ¬ SeparatesCodes C A B := by
  rintro ⟨hCA, hCB⟩
  obtain ⟨F, hF, hFdec⟩ := exists_code_decider_of_computablePred hC
  obtain ⟨X, hX⟩ := exists_code_fixed_point (scottTerm_closed hF hN hM)
  have hstep := scottTerm_app_reduces hF hN hM (Lambda.encode X)
  by_cases hCX : C (Lambda.encode X)
  · have htrue := (hFdec (Lambda.encode X)).1 hCX
    have hite : Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
          (Lambda.app F (Lambda.church (Lambda.encode X)))) N) M) N :=
      Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_left
          (Lambda.reduces_app_right htrue))) (Lambda.ifThenElse_true N M)
    have hXN : Lambda.reduces X N := Lambda.reduces_trans hX (Lambda.reduces_trans hstep hite)
    exact hCB X (hB N X (conv_of_reduces hXN).symm hBN) hCX
  · have hfalse := (hFdec (Lambda.encode X)).2 hCX
    have hite : Lambda.reduces
        (Lambda.app (Lambda.app (Lambda.app Lambda.ifThenElse
          (Lambda.app F (Lambda.church (Lambda.encode X)))) N) M) M :=
      Lambda.reduces_trans
        (Lambda.reduces_app_left (Lambda.reduces_app_left
          (Lambda.reduces_app_right hfalse))) (Lambda.ifThenElse_false N M)
    have hXM : Lambda.reduces X M := Lambda.reduces_trans hX (Lambda.reduces_trans hstep hite)
    exact hCX (hCA X (hA M X (conv_of_reduces hXM).symm hAM))

/-- **The Scott–Curry theorem, phrased for code sets.**  The code sets of two convertibility-
invariant sets of lambda terms, each with a closed member, are recursively inseparable. -/
theorem scott_curry_codeSet {A B : Lambda → Prop} (hA : ConvInvariant A) (hB : ConvInvariant B)
    {M N : Lambda} (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N) (hAM : A M) (hBN : B N) :
    RecursivelyInseparable (CodeSet A) (CodeSet B) := by
  rintro ⟨C, hC, hCA, hCB⟩
  refine scott_curry hA hB hM hN hAM hBN hC ⟨fun X hAX => hCA _ ?_, fun X hBX => hCB _ ?_⟩
  · exact (codeSet_encode A X).2 hAX
  · exact (codeSet_encode B X).2 hBX

/-- Scott's theorem is the special case `B = fun t => ¬ A t` of the Scott–Curry theorem: a
separating predicate for `A` and its complement is precisely a decision procedure for `CodeSet A`
on the codes of terms. -/
theorem not_computablePred_codeSet_of_scott_curry {A : Lambda → Prop} (hA : ConvInvariant A)
    {M N : Lambda} (hM : Lambda.IsClosed M) (hN : Lambda.IsClosed N) (hAM : A M) (hAN : ¬ A N) :
    ¬ ComputablePred (CodeSet A) := by
  intro hC
  have hB : ConvInvariant (fun t => ¬ A t) := by
    intro s t hst hs ht
    exact hs (hA t s hst.symm ht)
  refine scott_curry hA hB hM hN hAM hAN hC ⟨fun X hAX => ?_, fun X hBX hcx => ?_⟩
  · exact (codeSet_encode A X).2 hAX
  · exact hBX ((codeSet_encode A X).1 hcx)

------------------------------------------------------------------------
-- A concrete pair of recursively inseparable sets
------------------------------------------------------------------------

theorem not_conv_church_of_ne {m n : ℕ} (h : m ≠ n) :
    ¬ Conv (Lambda.church m) (Lambda.church n) := by
  rintro ⟨u, hm, hn⟩
  have h1 : Lambda.church m = u := Lambda.reduces_normal_eq (Lambda.church_normal m) hm
  have h2 : Lambda.church n = u := Lambda.reduces_normal_eq (Lambda.church_normal n) hn
  exact h (Lambda.church_injective (h1.trans h2.symm))

theorem convInvariant_conv_church (n : ℕ) : ConvInvariant (fun t => Conv t (Lambda.church n)) :=
  fun _ _ hst hs => hst.symm.trans hs

/-- **A concrete instance of the Scott–Curry theorem.**  For `m ≠ n`, the set of codes of the
terms convertible with `church m` and the set of codes of the terms convertible with `church n`
are disjoint and recursively inseparable: no computable predicate on codes can answer "yes" on
all of the first and "no" on all of the second. -/
theorem recursivelyInseparable_conv_church {m n : ℕ} :
    RecursivelyInseparable (CodeSet (fun t => Conv t (Lambda.church m)))
      (CodeSet (fun t => Conv t (Lambda.church n))) :=
  scott_curry_codeSet (convInvariant_conv_church m) (convInvariant_conv_church n)
    (Lambda.church_closed m) (Lambda.church_closed n) (conv_refl _) (conv_refl _)

/-- The two sets above really are disjoint when `m ≠ n`. -/
theorem disjoint_conv_church {m n : ℕ} (h : m ≠ n) (t : Lambda)
    (hm : Conv t (Lambda.church m)) (hn : Conv t (Lambda.church n)) : False :=
  not_conv_church_of_ne h (hm.symm.trans hn)

end Lambda
