# M20-TLCA4-BETAETA — TLCA problem 4 under βη (Imamura's Problem 5.1)

Series V, round 1, run 2.  Depends on M20-TLCA4-BM-FIXPOINT (`Start/TLCA4BMFixpoint.lean`).

**The problem.**  Is there an applicative combination `Y` of `B := λxyz.x(yz)`, `M := λx.xx` and
`I := λx.x` such that `Y x =βη x (Y x)`?  It is open.  This run neither answers it nor claims
progress on the answer; it supplies the formal bridge, a bounded search (no hit), and the first
place where the weak-equivalence invariant breaks under β and η.

## B1. The formal bridge (`Start/TLCA4BetaEta.lean`, proved)

* `TLCA4.lamB`, `lamM`, `lamI` — closed de Bruijn λ-terms for `B`, `M`, `I`;
  `TLCA4.toLam : TLCA4.Tm → Lambda` sends the variable `var n` to the free de Bruijn variable `n`.
* `TLCA4.reduces_B2` (`B u v ⟶β* λz. u (v z)`), `reduces_B`, `reduces_M`, `reduces_I`, and
  **`TLCA4.toLam_wstep : WStep u v → Lambda.reduces (toLam u) (toLam v)`** — every weak step is a
  β-reduction of the translations.
* **`TLCA4.toLam_weq : WEq u v → Lambda.betaEtaConv (toLam u) (toLam v)`** — soundness.
* **The incompatibility.**  `TLCA4.BII_betaReduces_I : Lambda.reduces (toLam (B I I)) (toLam I)`,
  `TLCA4.not_weq_BII_I : ¬ WEq (B I I) I`, packaged as `TLCA4.BII_incompatible`.
* `TLCA4.ProblemFiveOne : Prop` — Problem 5.1 stated over the bridge (with `x` the de Bruijn
  variable `0`).  Stated only.

Axioms: `docs/goal/evidence/M20-TLCA4-BETAETA-axioms.txt` (standard axioms only).

## B2. Bounded search for a positive answer (Python, `wip/b2_search.py`, not committed)

Everything in this section is an unverified computation; nothing in it is Lean-checked.

Method.  λ-terms in de Bruijn form, hashed as tuples.  For each candidate `Y`:
1. discard `Y` if `Y x` reaches a β-normal form by leftmost-outermost reduction within 200 steps
   and size 400 (a βη-normalizing `Y x` cannot satisfy the equation: the βη-normal forms of `Y x`
   and of `x (Y x)` would differ in size);
2. compute the *Böhm x-spine depth* `d`: head-reduce `Y x` to `x R₁`, `R₁` to `x R₂`, … (head
   normal forms with head `x`, one argument, no abstraction; at most 300 head steps and size 3000
   per level, cap `d ≤ 6`); `Y` with `d < 2` is not BFS-tested and is recorded as a miss (a
   heuristic filter: it would also discard a solution whose head normal forms are η-expanded);
3. for `d ≥ 2`, breadth-first βη-reduction of both `Y x` and `x (Y x)` to depth 8 with term size
   ≤ 80, and test for a common reduct.

| family | bound | tried | not normalized within the bounds | spine ≥ 2 (BFS-tested) | spine ≥ 6 | hits |
|---|---|---|---|---|---|---|
| all closed BMI-terms | ≤ 7 leaves | 323175 | 116060 | 301 | 301 | 0 |
| Statman-style polynomials `m₁ ∘ … ∘ m_k`, `t ∘ u := B t u`, monomials `Bⁿ B, Bⁿ M, Bⁿ I` | n ≤ 3, k ≤ 5 | 271452 | 25166 | 55 | 51 | 0 |

(An earlier run with ≤ 8 leaves was stopped by its time limit inside the 8-leaf layer and is not
counted.)

Closest misses: among BMI-terms every `Y` with spine depth `≥ 2` reached the cap `d = 6`, among
polynomials 51 of 55 did (the x-spine of the Böhm tree of `Y x` agrees with that of `x (Y x)` to
depth 6); none had a common βη-reduct in the BFS bounds.  The
smallest are the 5-leaf terms `B (M (B M)) B` and `M (B (B M)) B`; among polynomials,
`M ∘ (B M) ∘ B` (that is `B M (B (B M) B)`, the term `T` below) and its variants padded with `I`.

The term `T := B M (B (B M) B)`.  `T x` head-reduces to `x R₁` with `|R₁| = 78`; both `T x` and
`R₁` have x-spine depth ≥ 8 (the cap).  BFS to depth 6 and size 120: 466 reducts of `R₁`, 185 of
`T x`, **no common reduct**.  So `T x` and `x (T x)` agree as Böhm trees to depth 8 but no
βη-common reduct was found within the bounds — consistent with the problem being open (Böhm-tree
agreement does not give βη-conversion).

## B3. Research: a βη-compatible invariant

**Stop rule — the first identity that fails (Lean-checked).**  Theorem 2.11 (`agree_of_weq`:
`WEq ⊆ Agree x`) does not extend to β-conversion of the translations:
* `TLCA4.not_agree_BII_I x : ¬ Agree x (B I I) I`, while `TLCA4.BII_betaReduces_I` shows
  `toLam (B I I) ⟶β* toLam I`.  Both sides are weak normal forms with different values, so the
  normal-form clause of `Agree` separates them.
* the η-instance: `TLCA4.BxI_betaEtaReduces_x x : betaEtaReduces (toLam (B x I)) (toLam x)` (two
  β-steps, one η-step), while `TLCA4.not_agree_BxI_x x : ¬ Agree x (B x I) x` and
  `TLCA4.not_weq_BxI_x`.

So the first identity of the trace algebra that fails under βη is the soundness identity itself,
at the concrete pair `B I I = I` (β) and `B x I = x` (η); Theorems 2.9 (congruence) and 2.10
(validity of the three contractions) are not the obstruction — they concern only weak steps.

**The proposed variant (analysis on paper, not formalized).**  Replace the normal-form values of
`Agree` by βη-normal forms of the λ-interpretation and the leftmost-innermost trace by the head
reduction trace.  Then the analogue of 2.11 holds for the value clause (βη-normal forms are
unique, `Lambda.betaEtaNf_unique`), and for diverging terms the head trace of `toLam u` determines
its Böhm tree, which is βη-invariant up to η-expansion.  The variant therefore collapses to Böhm
trees modulo η, and the search data above show where it fails: the analogue of
`not_tailEq_shift` / Corollary 3.4 (the strictly increasing duplicated sizes that separate
`Y x` from `x (Y x)`) has no counterpart, since `B (M (B M)) B x` and `x (B (M (B M)) B x)` have the
same Böhm tree to depth 6 (computation, not Lean-checked).  A βη-invariant that separates them must
be finer than Böhm trees and coarser than weak equivalence; none was found.

## Exit criteria status

Neither criterion is met: no closed BMI-term `Y` with
`betaEtaConv (toLam (Y x)) (toLam (x (Y x)))` was found, and the negative statement
`∀ Y, occ x Y = 0 → ¬ betaEtaConv (toLam (.app Y (.var x))) (toLam (.app (.var x) (.app Y (.var x))))`
is not proved.  First missing lemma (the negative direction):
```lean
theorem TLCA4.no_fixedPoint_betaEta (Y : Tm) (x : ℕ) (hY : occ x Y = 0) :
    ¬ Lambda.betaEtaConv (toLam (.app Y (.var x))) (toLam (.app (.var x) (.app Y (.var x))))
```

## Series V, round 2, run 1

Module `Start/TLCA4Polynomial.lean` (row M20-TLCA4-POLYNOMIAL; axioms
`M20-TLCA4-POLYNOMIAL-axioms.txt`).

**B1 (Statman's valid step).**
* Monomials `Mono` (`Bⁿ B`, `Bⁿ M`, `Bⁿ I`, via `bpow`), composition `comp t u := B t u`, and
  polynomials `polyTm m [m₂, …, m_k] = m ∘ (m₂ ∘ (… ∘ m_k))`; `polyTm_isBMI`.
* `polyTm_action`: `(m₁ ∘ … ∘ m_k) x` is weakly equal to `m₁ (… (m_k x))`, hence βη-equal
  (`polyTm_action_betaEta`); `bpow_action`: `Bⁿ f g z₁ … zₙ = f (g z₁ … zₙ)` (and the βη form).
* `statmanT_eq`: `T = B M (B (B M) B)` is the polynomial `M ∘ ((B M) ∘ B)`.
* The reduction: `problemFiveOne_of_poly : PolyFiveOne → ProblemFiveOne` (unconditional) and
  `problemFiveOne_iff_poly (hS : StatmanStepOne) : ProblemFiveOne ↔ PolyFiveOne`.
* The version of the normal-form theorem the reduction needs is exactly `StatmanStepOne`: every
  closed BMI-term `Y` with `Y x =βη x (Y x)` is βη-equivalent to a polynomial.  It is stated as a
  `Prop` and **not proved**; it is the first missing lemma of B1:
```lean
theorem statmanStepOne : TLCA4.StatmanStepOne
```
  The first case of its induction that does not close was not reached: the argument (as reported
  in Imamura's introduction) goes through the Böhm-tree/head-normal-form shape of a fixed-point
  combinator, for which this library has no βη-normal-form theory of BMI-terms yet (the first
  piece needed is a head-normal-form lemma for `toLam (Y x)` with `Y` a BMI-term).

**B2 (polynomial algebra; extensional laws, proved in the weak calculus, hence βη).**
* `bpowI_action`: `Bⁿ I` is the identity on `n + 1` arguments; `comp_I_left`, `comp_I_right`
  (unit), `comp_assoc` (associativity, on one argument).
* `bpowM_action`: `Bⁿ M g z₁ … zₙ = (g z₁ … zₙ) (g z₁ … zₙ)` (duplication at depth `n`);
  `bpowB_action`: `Bⁿ B h z₁ … zₙ a b w⃗ = h z₁ … zₙ (a b) w⃗` (composition at depth `n`).
* Commutation law `comm_bpowB`: for `k ≥ n + 1`, `(Bⁿ B) ∘ (Bᵏ X)` and `(Bᵏ⁺¹ X) ∘ (Bⁿ B)` act
  identically on `k + 1` arguments.  A normal form modulo these laws (move every `Bⁿ B` to the
  right past deeper monomials, delete `Bⁿ I`) is suggested by them but not proved complete.
* Search `wip/b2_poly.py`: head normal forms of `p x` for I-free polynomials.
  - bounds: monomials `Bⁿ B`, `Bⁿ M` with `n ≤ 3`, length ≤ 5, 300 head steps per term;
  - run: 37448 polynomials; 19 have head normal form `x Q`; 6 also have `Q` with head normal form `x Q'`;
  - result: at length ≤ 4 only `T = M ∘ (B M) ∘ B` passes two head levels; at length 5 the six
    are `T`-like (listed in `wip/b2_poly.log`).  Not Lean-checked.
* No invariant separating `p x` from `x (p x)` was found.  The naive weight (number of
  `M`-monomials) is preserved by the proved laws (`Bⁿ I`-deletion, `comm_bpowB`), but its
  βη-invariance was neither tested nor proved, so it is not offered as a candidate.

**B3.** Not attempted (no candidate invariant from B2).
