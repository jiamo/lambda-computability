# M20-TLCA4-BM-FIXPOINT — no fixed-point combinator from B and ω (TLCA open problem 4)

Module: `Start/TLCA4BMFixpoint.lean` (namespace `TLCA4.Tm`, imports only Mathlib).
Status: **DONE_STRONG** (series V, round 1). Axioms: `M20-TLCA4-BM-FIXPOINT-axioms.txt`
(`propext, Classical.choice, Quot.sound`; no `sorry`, no `native_decide`, no `Lean.ofReduceBool`).

## What is proved

Terms `Tm` (`B`, `M`, `I`, `var n`, `app`), `occ x u` (= |u|ₓ), `iterX x r u` (= xʳ u), one-step
weak reduction `WStep` (the three contractions closed under both sides of application) and weak
equivalence `WEq` (its equivalence closure, an inductive with `step`, `refl`, `symm`, `trans`).

```lean
theorem not_weq_iterate (Y : Tm) (x : ℕ) (hY : occ x Y = 0) (r : ℕ) (hr : 1 ≤ r) :
    ¬ WEq (.app Y (.var x)) (iterX x r (.app Y (.var x)))
theorem no_fixedPoint (Y : Tm) (x : ℕ) (hY : occ x Y = 0) :
    ¬ WEq (.app Y (.var x)) (.app (.var x) (.app Y (.var x)))
def IsFixedPointCombinator (Y : Tm) : Prop := ∀ F : Tm, WEq (app Y F) (app F (app Y F))
theorem no_BMI_fixedPointCombinator (Y : Tm) (hY : IsBMI Y) : ¬ IsFixedPointCombinator Y
theorem no_BM_fixedPointCombinator (Y : Tm) (hY : IsBM Y) : ¬ IsFixedPointCombinator Y
```

`IsBM`/`IsBMI` are the applicative combinations of `B, M` (resp. `B, M, I`). The last theorem is
the TLCA formulation for weak equivalence. The statements are the targets of the instruction,
not weakened.

## How the argument of v3 was formalized

* `li` (leftmost-innermost step, `Option Tm`), `ann x` (its annotation: `some (p, q)` at an
  `M`-contraction, `none` otherwise), `seq t n` (the `li`-sequence, normal terms fixed) and
  `str x t n` (the **raw annotation stream**, one entry per step — the second design suggestion).
* `Term t` — the `li`-sequence itself terminates (first design suggestion: no weak-normal-form
  notion and no uniform-normalization lemma are used).
* The invariant is a relation, not a quotient: `Agree x u v` ⇔ both sequences reach the same
  normal term, or both diverge with tail-equivalent raw streams. The operation `⋆` is never
  defined; Theorems 2.9 and 2.10 are proved directly as congruence and contraction lemmas:
  * Lemma 2.5: `agree_seq`;
  * Theorem 2.9: `agree_congr_left`, `agree_congr_right` (cases: head diverges; head reaches a
    normal `U` and the argument diverges, stream shifted by `|U|ₓ`; both terminate);
  * Theorem 2.10: `agree_B`, `agree_M`, `agree_I` (the arguments are normalized one by one through
    the congruence; the three-normal-terms case is one `li`-step);
  * Theorem 2.11: `agree_of_weq` — from 2.9 and 2.10 alone.
* Lemma 2.1: `exists_ann_of_not_term` (B- and I-steps lower the number of leaves, `li_size`).
  This is what makes raw streams work in Lemma 3.5 and in the first case of Theorem 3.1: after
  any position there is a later `some`-entry. Checked, as the instruction asked.
* Lemma 3.6: `seq_iterX`, `str_iterX` (`xʳ u` steps inside `u`, every `p` shifted by `r`).
* Lemma 3.2/3.3 in factor form `F W L = List.foldr app W L` (`step_cases`, `good_step`,
  `inv_step`), Corollary 3.4 `q_strictMono`, Lemma 3.5 `not_tailEq_shift`, Theorem 3.1
  `not_weq_iterate` with the three cases of the paper.

## What the formalization says about the reviewer's doubt

The doubted step (Lemma 3.3) **holds**, and the formal proof shows why the doubt does not apply.
After an `M`-contraction `M A ⇒ A A` the term is `U₁(…(Uₖ (V A)))` with every factor normal, `V`
the left copy and `A` the right copy. The invariant `Inv x q t` that is carried to the next
`M`-contraction is

```lean
∃ L V A, t = F (app V A) L ∧ (∀ U ∈ L, li U = none) ∧ li V = none ∧ li A = none ∧
  rl V = var x ∧ rl A = var x ∧ q ≤ occ x A
```

(`rl` = rightmost leaf). The only step that can touch the boundary between the last leaf of the
left copy and the right copy is a B-contraction at `V A` itself, i.e. `V = B a b`; since
`rl (B a b) = rl b = x`, the step `B a b A ⇒ a (b A)` moves `a` into the factor list and keeps
`b` — which still ends in `x` — glued to `A` (`inv_step`, last case). Because the strategy is
innermost, `A` is normal when duplicated and stays untouched; every other step happens at a
factor in `L`, to the left of `V A`. So a B-contraction can split off a *prefix* of the left copy,
never its last leaf; the next `M`-contraction is at some factor of `L`, and its argument contains
`V A`, whence `q' ≥ |V|ₓ + |A|ₓ ≥ 1 + q`.

Two remarks on the statement of v3:
* Lemma 3.2 as stated ("every redex contains the rightmost leaf") is true only because the
  strategy is innermost: the argument of an `M`-contraction is normal, so the left copy contains
  no redex. The formal version is the factor form with normal factors (`Good`, `state_seq`).
* Lemma 3.3 needs no hypothesis on `x` in `P`; `occ x Y = 0` is used only in the first case of
  Theorem 3.1 (`ann_le_occ`, `occ_seq`: every `p` of a reduct of `Y` is `0`).

No lemma of the paper was found false; no counterexample search was needed.
