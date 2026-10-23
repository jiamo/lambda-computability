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

## Series V, round 2, run 2

### B1: Statman's first step, the `B`-fragment (`Start/TLCA4PolyClosure.lean`, proved)

**The argument, reconstructed.**  Under βη, two closed terms are equal as soon as they agree on
fresh arguments (η).  So it suffices to compare actions:
* `B u v` acts as `λz. u (v z)`, i.e. it is the composite `u ∘ v`; if `u`, `v` are polynomials,
  `(u ∘ v) x = u (v x)` is the action of the concatenated monomial list;
* `B u` acts on two arguments as `λz w. u (z w)`; if `u = m₁ ∘ … ∘ m_k`, then
  `(B m₁) ∘ … ∘ (B m_k)` applied to `z w` gives `m₁ (… (m_k (z w)))` too, since
  `B mᵢ X w = mᵢ (X w)`; so `B` distributes over composition and raises `Bⁿ X` to `Bⁿ⁺¹ X`;
* `I u` is `u`; `B`, `M`, `I` are monomials (`n = 0`).
Hence every term of the grammar `Y ::= B | M | I | B Y | B Y Z | I Y` is βη-equal to a polynomial,
by induction on `Y`, with no use of the fixed-point hypothesis.  What remains are the terms whose
head has more arguments than its arity allows to stay a polynomial: `M Y` (acting as `Y Y`),
`B Y Z W` (`Y (Z W)`), `I Y Z` (`Y Z`).  For them the fixed-point hypothesis must be used: e.g. `M M`
has no head normal form, and is not a polynomial action.

**Proved (standard axioms only, `M20-TLCA4-STATMAN-STEP-ONE-axioms.txt`).**
* `lift_toLam_of_isBMI` (translations of closed terms are closed), `betaEtaConv_lam`;
* `ext1_of_weq`, `ext2_of_weq`: if `t x =w s x` (resp. `t x y =w s x y`) for fresh variables and
  `t`, `s` are closed `B`,`M`,`I`-terms, then `toLam t =βη toLam s`;
* `comp_poly`: `comp (polyTm m ps) (polyTm m' qs) =βη polyTm m (ps ++ m' :: qs)`;
* `B_poly`: `B (polyTm m ps) =βη polyTm m.raise (ps.map Mono.raise)`;
* `PolyGen`, `polyGen_betaEta_poly`: Statman's first step on the fragment above.

**Stop rule (first case of the induction that does not close).**  `Y = M Y'`: the IH gives
`Y' =βη p` for a polynomial `p`, and `M Y'` acts as `p p`, which is not a polynomial action in
general.  First missing lemma (as a Lean statement):
`theorem statmanStepOne_M (Y : Tm) (hY : IsBMI Y) (hfix : Lambda.betaEtaConv (toLam (app (app M Y) (var 0))) (toLam (app (var 0) (app (app M Y) (var 0))))) : ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam (app M Y)) (toLam (polyTm m ps))`
— it needs a head-normal-form theory of `toLam (Y x)`, which the library does not have.

### B2: the x-spine of `p x` (Python, `wip/b2_depth.py`, not Lean-checked)

The x-spine depth of `p x` is the largest `d` with `hnf(p x) = x Q₁`, `hnf(Q₁) = x Q₂`, …,
`d` levels (each level one argument, no λ), computed by fuel-bounded head reduction.
* Run 1: monomials `Bⁿ B`, `Bⁿ M`, `n ≤ 2`, length ≤ 6, depth cap 4, 400 head steps per level:
  55986 polynomials; depth histogram 0: 55967, 1: 13, 2: 3, ≥4: 3.
* Run 2: `n ≤ 3`, length ≤ 6, depth cap 5: 299592 polynomials; histogram 0: 299573, 1: 13,
  2: 3, 4: 1, ≥5: 2.
* Conjectured structural properties, no violation in either run: (i) depth ≥ 1 implies that the
  first monomial is `M` (`n = 0`); (ii) depth ≥ 2 implies that the last monomial is `B` (`n = 0`).
  Property (i) has a direct explanation: if `m₁ = Bⁿ⁺¹ X` or `m₁ = B`, then `p x` head-reduces to a
  λ-abstraction; if `m₁ = M`, `p x = (q x) (q x)`.  It is not formalized.
* Depth ≥ 4 occurs only for `T = M ∘ (B M) ∘ B`, `M ∘ M ∘ (B M) ∘ B ∘ B` and
  `p₄ = M ∘ (B M) ∘ (B M) ∘ (B B) ∘ B` (all `T`-like).  With cap 5, `T` and the second reach the
  cap, but `p₄` has depth exactly 4; rechecked with 3000 head steps per level and cap 8
  (`wip/b2_depth4.py`): the fifth head normal form is `x Q R`, with two arguments, so not fuel.
* No invariant separating `p x` from `x (p x)` was found; the spine depth is not βη-invariant in
  any proved sense.  Stop rule: the first conjectured property that fails is this run's
  conjecture "x-spine depth ≥ 3 implies an infinite x-spine", refuted (in the bounded,
  not Lean-checked sense above) by the concrete polynomial `p₄ = M ∘ (B M) ∘ (B M) ∘ (B B) ∘ B`
  (monomials `(0,M) (1,M) (1,M) (1,B) (0,B)`).

### B3

Not reached: B1 did not close, so M20-TLCA4-POLYNOMIAL stays DONE_WEAK and
M20-TLCA4-STATMAN-STEP-ONE stays open (IN_PROGRESS).

## Series V, round 3, run 1

Source read first: R. Statman, "To Type a Mockingbird" (2011), Lemma 0.1 and Corollary 0.1 (the
valid first step).  All results below are Lean-checked, standard axioms only (see the axioms
files of M20-TLCA4-STATMAN-STEP-ONE, M20-TLCA4-POLYNOMIAL, M20-TLCA4-T-NOT-FIXPOINT).

### A1: Corollary 0.1 (`Start/TLCA4StatmanStep.lean`)

* `WNF t := li t = none` (no weak redex; the library's leftmost-innermost strategy is stuck) and
  `WN t := ∃ N, ReflTransGen WStep t N ∧ WNF N`.
* `isBMI_wnf_polyGen`: a weakly normal closed `B`,`M`,`I`-term is `B`, `M`, `I`, `B U` or `B U V`
  with `U`, `V` weakly normal, hence in `PolyGen`; `wnf_betaEta_poly` (Corollary 0.1) and
  `wn_betaEta_poly` (for weakly normalizable terms) via `polyGen_betaEta_poly`.

### A3: the fixed-point bridge (`Start/TLCA4FixBridge.lean`)

* `hd` (free head variable of a λ-term), `HnfHead x t` (some head normal form of `t` has free head
  `x`).
* `hnf_betaEtaStep`: a βη-step keeps a head normal form a head normal form with the same free head
  (the root η-step `λz. P z → P` included: `hd_lift`, `Neutral.of_lift`).
* `hasHnf_of_betaEtaConv` (through `D∞`: `ddenot_convBE`, `exists_ddenot_ne_botDinf_of_hasHnf`,
  `hasHnf_of_ddenot_ne_botDinf`), then Church–Rosser: `hnfHead_of_betaEtaConv`, and
  `fixHeadBridge : FixHeadBridge`.  η-postponement was not needed.

### A2: Lemma 0.1 (`Start/TLCA4StatmanLemma.lean`, `Start/TLCA4StatmanInduction.lean`,
`Start/TLCA4StatmanProof.lean`)

* Form proved (`statmanLemmaGen : StatmanLemmaGen`): for a closed BMI-term `X` and variables
  `x, y₁, …, y_m`, if `toLam (X x y₁ … y_m)` reduces to a head normal form whose free head is among
  `x, y⃗`, then the head is `x` and `WN X`.  λs in the head normal form are allowed.
* Induction (`good_all`) on `n` with `HNIn n (toLam (X x y⃗))`, in the equivalent form "every head
  normal form with a free head has head `x`" (`Good n X`), over the spine `X = c z₁ … z_j`:
  - weak head redex (`I U …`, `M U …`, `B U V W …`): 1 or 3 head steps (`good_of_wstep`,
    `hnIn_hsteps`), IH on the contractum, `wn_of_wstep`;
  - `B`, `M`, `I`: `statmanGen_B/M/I` (head normal forms computed, `hd_unique`);
  - `B U` (`k = 1`: two head steps to `λz. U (x z)`, then under the λ; `k ≥ 2`: three head steps
    to `U (x y) …`) and `B U V` (three head steps to `U (V x) y⃗`): Statman's simulation by `U y …`
    with `y` fresh, realized as de Bruijn index 0 of a lifted term,
    `subst Q 0 (… lift 1 0 t … var 0 …)`, so no free-variable bookkeeping;
    `hnIn_split_subst` is `hasHeadEval_of_subst` refined to keep the step count and to split the
    run at the head normal form of the simulating term; `hnf_subst_ne`, `hnf_subst_head` transport
    head normal forms and heads through the substitution;
  - when `V x` reaches the head under the abstractions (`good_vpart`), `V x P₁ … P_m` is simulated
    by `V x' y₁ … y_m`, one argument at a time from the right (`good_peel`).
* `statmanLemmaOne` (one argument), and `statmanStepOne : StatmanStepOne`
  (`statmanStepOne_of_lemmaOne`: Lemma 0.1 + bridge + Corollary 0.1).

### A4

* `theorem statmanStepOne : TLCA4.StatmanStepOne` and
  `theorem problemFiveOne_iff_polyFiveOne : TLCA4.ProblemFiveOne ↔ TLCA4.PolyFiveOne`
  (`Start/TLCA4StatmanProof.lean`).  M20-TLCA4-STATMAN-STEP-ONE: exit criterion met (DONE_STRONG).
  M20-TLCA4-POLYNOMIAL: the reduction is unconditional, exit criteria met (DONE_STRONG).

### A5: the polynomial side (`Start/TLCA4TUnfold.lean`)

* Proved: `tT = B M (B (B M) B)` (`tT_eq_poly`), with `A₀ = B M (B x)`, `Aₙ₊₁ = B x Aₙ`:
  `T_unfold : T x →w M A₀`, `MtA_step : M Aₙ →w xⁿ (M Aₙ₊₁)` (`iterX`), `tA_app`.  (Imamura's
  indexing of `A` is shifted by one.)
* Stated only: `TNotFixedPoint` (`¬ toLam (T x) =βη toLam (x (T x))`), new row
  M20-TLCA4-T-NOT-FIXPOINT at the head of the M20-TLCA4 queue.
* Not done: the structural fact "a polynomial βη fixed-point combinator has first monomial `M`" is
  not formalized (the head normal form of `B R`-headed `p x` is an abstraction, but η can remove
  abstractions, so the shape argument needs an η-aware head comparison); no candidate invariant for
  `T` was formalized or tested.  Stop rule: no invariant property was tested in this run, so none is
  reported as failing; first missing lemma `T_not_fixedPoint`.
* Searches: none in this run.

## Series V, round 3, run 2

### B1: structure of a polynomial fixed-point combinator (`Start/TLCA4PolyHead.lean`)

Proved: `TLCA4.mono_app_reduces_lam` and `TLCA4.polyApp_reduces_lam (m : Mono) (hm : m.base = .B ∨
0 < m.n) (ps : List Mono) : ∃ t, Lambda.reduces (toLam (app (polyTm m ps) (var 0))) (.lam t)` — if
the first monomial is `B` or `Bⁿ⁺¹ X`, `p x` reduces (in at most five head steps) to an abstraction.

First structural claim that does not close: the η-aware comparison.  From the fixed-point equation
and `fixHeadBridge`, `p x` has a head normal form with head `x`; when it is an abstraction `λz. H`,
βη-equality with `x (p x)` forces `H` to η-contract against its last argument `z`, and comparing
`H` with `x (p x) z` needs the head of `r x z` (`r` the rest of the polynomial).  This was not
formalized; "the first monomial is `M`" remains open, and no constraint on the second or last
monomial was proved.

### B2: `T_not_fixedPoint` — experiment (`wip/b2_treducts.py`, not Lean-checked)

Reducts of `toLam (T x)`: the leftmost-outermost path (≤ 120, resp. ≤ 400 steps) and a breadth-first
neighbourhood of every path point (depth ≤ 3, resp. ≤ 2; size ≤ 160, resp. ≤ 260): 4000, resp. 6042
reducts, `k` up to 6, resp. 21.  Every reduct is written `xᵏ R`.
* No residual `R` occurs with two different `k` (in particular never with `k` and `k + 1`).
* First candidate `φ(i, j) = i(i+1)/2 + (j − i)` (indices of the β-normal forms `a_i`, `a_j` of the
  two components of `R = P Q`, `a_n = λz. xⁿ⁺¹ (z (λw. x (z w)))`) fails: `R = (B x Y)(B x Y)`
  with `Y = B (B M) B x`, `k = 0`, `φ = 1` (both components normalize to `a₁`).
* Second candidate `φ(i, j) = j(j+1)/2 − i` holds on every explored reduct where it is defined
  (3737 of 4000, 5798 of 6042); it is undefined on the reducts before the `M a₀` stage.  Along head
  reduction the pairs `(i, j)` run through `0 ≤ i < j` in the order `(0,1), (1,2), (0,2), (2,3), …`
  and `k = φ(i, j)` takes each value once: `k` is a Cantor pairing of the residual's indices.  If
  every reduct satisfies `k = φ(R)`, the common reduct of `T x` and `x (T x)` would need
  `φ(R) = φ(R) + 1`.
First missing lemma for the formalization: the shape predicate for all βη-reducts of `toLam (T x)`
(including partial reducts of the components and the pre-`M a₀` reducts) and its closure under one
β- or η-step at any position.

### B3: `Q = M ∘ M ∘ (B M) ∘ B ∘ B` — experiment (`wip/b3_QvsT.py`, not Lean-checked)

Head reduction of `toLam (Q x)` (≤ 3000 steps, size ≤ 4000) reaches `k = 0, 1, …, 24` with step
gaps `24, 16, 9, 16, 9, 9, 16, 9, 9, 9, …`, the same triangular pattern as `T` (gaps
`14, 10, 3, 10, 3, 3, 10, 3, 3, 3, …`), but the residual components of `Q x` are not the `a_n`.
βη-equality of `Q` and `T` was not decided; no theorem reducing `PolyFiveOne` to `T` and `Q` was
proved.  Conjecture (evidence above only): `Q x` and `T x` have the same x-spine growth.

## Series V, round 4, run 1

**Part A: `T` is not a βη fixed-point combinator (row M20-TLCA4-T-NOT-FIXPOINT, DONE_STRONG).**

```
theorem TLCA4.T_not_fixedPoint : TLCA4.TNotFixedPoint
theorem TLCA4.T_not_fixedPoint' :
    ¬ Lambda.betaEtaConv (toLam (app tT (var 0))) (toLam (app (var 0) (app tT (var 0))))
```

(`Start/TLCA4TNotFixpoint.lean`; standard axioms only.)  The proof follows the plan of the round,
with two changes.

* A1 (`Start/TLCA4TComponents.lean`).  `tAnf x n = aₙ = λz. xⁿ⁺¹ (z (λw. x (z w)))`, βη-normal
  (`tAnf_nf`) and injective in `n` (`tAnf_injective`).  `TComp x n` is the least family with
  `toLam A₀` at `0`, `B x P` at `n + 1` for `P` at `n`, closed under βη-reduction; every member
  reduces to `aₙ` (`TComp.reduces_tAnf`), so the index is unique (`TComp.index_unique`), and no
  member is `x`-headed (`TComp.not_xHeaded`).
* A2 (`Start/TLCA4TGrammar.lean`).  The circularity is avoided as suggested, by an explicit
  grammar `TGram x i` stated about components only, with the bound variable `q` of an abstraction
  in place of the argument: the abstractions have the bodies `xᵐ (R q)` (`R` of index `i'`,
  `m + i' = i`), `xᵐ (q R)` (`R` a reduct of `B x q`, `m = i + 1`), `xᵐ (M R)` and `xᵐ (R₁ R₂)`
  (`R`, `R₁`, `R₂` reducts of `B x q`, `m = i`); the non-abstractions are `B M R`,
  `(λab. M (a b)) R`, `(λab. (a b) (a b)) R` (`R` a reduct of `B x`) at index `0`, and `B x P`,
  `(λab. x (a b)) P` at index `i + 1`.  `TGram.step`: the grammar is closed under one β- or η-step
  at any position.  `TComp.tGram` and the abstraction lemma `TComp.abstraction` follow.
* A3 (`Start/TLCA4TNotFixpoint.lean`).  First change: the pre-stage reducts are not needed.  The
  argument starts from `N₀ = M A₀` (`T x →β N₀`, `T_unfold`), which has shape `(k, j) = (0, 0)`.
  `TShape x N`: `N = xᵏ (P Q)` with `P`, `Q` in the grammar at `i`, `j` and `k + i = tri j`, or
  `N = xᵏ (M Q)` with `Q` at `j` and `k + j = tri j` (`tri j = j (j + 1) / 2`, `two_mul_tri`).
  `TShape.step`, `TShape.reduces`: closed under βη-reduction (the four bodies give the pairs
  `(i', j)`, `(j, j + 1)`, the M stage at `j + 1`, and `(j + 1, j + 1)`).
* A4.  Second change: the index uniqueness is proved for the grammar directly
  (`TGram.reduces_tAnf`, `TGram.index_unique`), as `TGram ⊆ TComp` is not needed.  If
  `T x =βη x (T x)`, Church–Rosser twice gives `C'` with `N₀ →βη C'` and `N₀ →βη x C'`; both have
  shape; the `x`-prefix decomposition is unique (grammar members are not variables, and `M` is not a
  grammar member, `TGram.ne_lamM`), so `k + 1 + i = k + i` or `k + 1 + j = k + j`
  (`TShape.not_xPrefix`).

Experiment (wip/a_grammar.py, wip/a_grammar.log; Python, under `timeout 600`; before the Lean
proof, not used by it): `F n` = all βη-reducts of `toLam Aₙ` for `n ≤ 4` (21, 78, 270, 924, 3156
members, one normal form each, sizes ≤ 70, index unique on all of them); every abstraction
member's body with a fresh `q` falls in one of the four classes with offset `0` (for `i = 4`:
1782, 15, 15, 45 members), no other shape; the non-abstractions are the generator forms
(6 at index `0`, 2586 of the form `B x P` / `(λab. x (a b)) P`).

A5, first claim that does not close (experiment only, wip/a5_q.py, wip/a5_q.log, under
`timeout 300`): the method of A1 indexes a component by its βη-normal form, but the residual
components of `Q = M∘M∘(BM)∘B∘B` have none in the explored range.  Along 260 leftmost steps of
`toLam (Q x)` the x-prefix takes the values `k = 0, …, 22`; at each change of `k` the residual is
an application `P' Q'`, and `P'` (and, from `k = 1`, `Q'`) has no β-normal form within 400
leftmost steps (within 3000 steps for `k = 0, 1`).  Whether they normalize at all was not decided.
So Q needs an index that is not a normal form (for instance a grammar indexed by stages), and the
invariant for Q was not found.  The η-aware head comparison was not attempted.  Row
M20-TLCA4-BETAETA stays open; first missing lemma unchanged (`TLCA4.no_fixedPoint_betaEta`,
equivalently `¬ PolyFiveOne`).

## Series V, round 4, run 2

Lean: `Start/TLCA4QUnfold.lean`, standard axioms only.

```
theorem TLCA4.Q_unfold (x : ℕ) :
    Relation.ReflTransGen WStep (app tQ (var x)) (qK x) ∧
      Relation.ReflTransGen WStep (app M (app tT (app B (var x)))) (qK x)
theorem TLCA4.Q_weq_MT (x : ℕ) : WEq (app tQ (var x)) (app M (app tT (app B (var x))))
theorem TLCA4.Q_betaEta_MT (x : ℕ) :
    Lambda.betaEtaConv (toLam (app tQ (var x))) (toLam (app M (app tT (app B (var x)))))
```

with `tQ = M ∘ (M ∘ (BM ∘ (B ∘ B)))` (`tQ_eq_poly`) and the common reduct
`qK x = M (M (B M (B (B x))))`.  Everything else below is experiment only (Python, under
`timeout`, in `wip/`), not checked by Lean.

**A1, the candidates (wip/a1_spine.py, wip/a1_spine.log, `timeout 1500`).**  Polynomials
`p = m₁ ∘ ⋯ ∘ m_L` over the monomials `Bⁿ B`, `Bⁿ M` (`n ≤ 3`); the `Bⁿ I` monomials removed first
(units up to βη); `m₁ = M` fixed, since every other first monomial makes `p x` an abstraction
(`polyApp_reduces_lam`).  x-spine depth of `p x` (levels `hnf = x Q`, no λ, one argument) with cap
10 and 300 head steps per level; every cap hit rechecked with 3000 steps per level (all again at the
cap); no run was fuel-limited.

| L | polynomials | depth histogram | cap hits |
|---|---|---|---|
| 1 | 1 | {1: 1} | 0 |
| 2 | 8 | {0: 8} | 0 |
| 3 | 64 | {0: 62, 1: 1, 10: 1} | 1 |
| 4 | 512 | {0: 512} | 0 |
| 5 | 4096 | {0: 4080, 1: 11, 2: 3, 4: 1, 10: 1} | 1 |
| 6 | 32768 | {0: 32768} | 0 |
| 7 | 262144 | {0: 261872, 1: 208, 2: 44, 4: 8, 10: 12} | 12 |

Length 8 (2097152 polynomials) was started and not finished within the run.  The 14 cap hits:

* L = 3: `T = M ∘ BM ∘ B`;
* L = 5: `Q = M ∘ M ∘ BM ∘ B ∘ B`;
* L = 7: `M∘M∘B∘M∘BM∘B∘B`, `M∘M∘M∘BM∘B∘B∘B` (= `Q₂`), `M∘M∘BM∘B∘BM∘B¹B∘B`,
  `M∘M∘BM∘B∘B²M∘B¹B∘B`, `M∘M∘BM∘B¹B∘BM∘B∘B`, `M∘M∘BM∘B²M∘B∘B¹B∘B`, `M∘M∘BM∘B²M∘B²B∘B∘B`,
  `M∘M∘BM∘B³M∘B∘B¹B∘B`, `M∘M∘BM∘B³M∘B²B∘B∘B`, `M∘M∘B²M∘B¹B∘BM∘B∘B`, `M∘BM∘B∘M∘BM∘B∘B`
  (= `T∘T∘B`), `M∘BM∘M∘BM∘B∘B∘B`.

Pattern.  (1) Every cap hit has odd length `2m+1` with `m+1` monomials of the form `BⁿM` and `m`
of the form `BⁿB`; no polynomial of even length has depth `> 0`.  (2) The depths found are
`0, 1, 2, 4` or the cap: no depth in `5..9`.  (3) The family `Q_k = M ∘ Mᵏ ∘ BM ∘ Bᵏ⁺¹`
(`Q₀ = T`, `Q₁ = Q`) satisfies `Q_k = M ∘ Q_{k-1} ∘ B` (associativity of `∘`); its members for
`k ≤ 4` reach the cap 12 (wip/a1_family.py, recheck with 10× fuel).  In particular
`Q = M ∘ (T ∘ B)`, and in Lean `Q x =βη M (T (B x))` (`Q_betaEta_MT`).
But the family is not the whole list: at `L = 7` it contributes one of 12 cap hits, and `T∘T∘B` is another composite of `T`.  No
βη-equalities among the 14 were established (all have infinite Böhm trees, so no normal-form test
applies).

Conjecture (bounded).  Over `{BⁿB, BⁿM : n ≤ 3}`, `L ≤ 7`: a polynomial whose x-spine reaches depth
5 reaches every depth (it has the Böhm tree of a fixed-point combinator), and the polynomials with
this property are exactly the 14 above.

**A2, Q (wip/a2_q.py, wip/a2_q_stages.py, logs in the session).**  (i) The residual components do
not normalize: `R = M ∘ BM ∘ B ∘ B = T ∘ B` and the `P'` of the first residual of `Q x` is `R x`;
its Böhm tree is `λe. x (x (x ⋯))`: 40 levels computed (300 and 3000 head steps per level).  Proof
sketch of divergence: `W = BM (B (B x)) →β λc e. x (c (λd e'. x (c d e')) e)` is normal, and
`R x = W W` has the head reduct `λe. x (W W' e)` with `W' = λd e'. x (W d e')`, and `W` re-applied
to a growing argument at every level; so the Böhm tree is infinite and `R x` has no β-normal form.
Hence the normal-form index of the T proof (`TComp.reduces_tAnf`) cannot apply to Q.
(ii) Stage structure.  Along 700 leftmost-outermost steps, `Q x` reaches `k = 67` and `T x`
reaches `k = 187`; the gaps between the increments of `k` take two values only (Q: 9 and 16; T: 3
and 10), and the long gaps end exactly at `k = 1 + tri j` (`2, 4, 7, 11, …, 67`) for both, with
`j` short gaps in stage `j`.  So the stage index of `T` (`k + i = tri j`) is the candidate for `Q`,
with the M stage replaced by the long gap.
(iii) Stop.  The first step that does not close: the grammar of the components of `Q x` (the
analogue of `TGram` and of `TGram.step`) is not found, because the components are not indexed by
normal forms; the candidate index "number of `B x` layers" was not tested on the reducts.  No row
M20-TLCA4-Q-NOT-FIXPOINT was opened (no Lean statement proved).

(iv) Structure for the next attempt (Lean, `Q_unfold`): `qK x = M (M A₀[B x])`, where
`A₀[y] = B M (B y)` is the first component of the `T` proof (`T y →w M A₀[y]`, `T_unfold`).  So
`Q x` is `M` applied to the `T`-configuration `M A₀` for the argument `y = B x`; the `T`
invariant of the reducts of `M A₀[y]` is stated with `y`-prefixes, and `y = B x` is not a variable,
which is where the transfer from `T` to `Q` has to be done.

**A3.**  The family `Q_k` exists (`Q_k = M ∘ Q_{k-1} ∘ B`), but the first member whose invariant is
unclear is `Q₁ = Q` itself (A2 (iii)).

Row M20-TLCA4-BETAETA stays open; first missing lemma unchanged (`TLCA4.no_fixedPoint_betaEta`,
equivalently `¬ PolyFiveOne`), next claim `TLCA4.Q_not_fixedPoint`.

## Series V, big round, run 1

**A1, `Q_not_fixedPoint` (row M20-TLCA4-Q-NOT-FIXPOINT, opened on the board in this run).**
Lean, `Start/TLCA4QStages.lean`, axioms in `docs/goal/evidence/M20-TLCA4-Q-NOT-FIXPOINT-axioms.txt`:

* `tAy y n` — the components `A₀[y] = B M (B y)`, `Aₙ₊₁[y] = B y Aₙ[y]` for an arbitrary term
  `y` (`tAy_var`: for `y = x` they are the `tA x n` of the `T` proof);
* `tAy_app` — `Aₙ[y] Z →w yⁿ (M (B y Z))`; `MtAy_step` — `M Aₙ[y] →w yⁿ (M Aₙ₊₁[y])`;
* `iterT_Bx_app` — `(B x)ⁿ W R →w xⁿ (W R)`;
* `MtAy_tail_step` — `M Aₙ[B x] R →w xⁿ (M Aₙ₊₁[B x] R)`;
* `tT_Bx_reduces_qTail` — the tail `R = M A₀[B x]` is a weak reduct of `T (B x)`;
* **`Q_stage`** — `Q x →w x^{tri n} (M Aₙ₊₁[B x] R)` for all `n`; `Q_stage_betaEta` (β-form).

and `Start/TLCA4QComponents.lean`: `tAnfQ x n = ãₙ = λz c. xⁿ⁺¹ (z (λw d. x (z w d)) c)`,
**`tAnfQ_nf`** (βη-normal), **`tAnfQ_injective`**, `Bx_tAnfQ_reduces` (`B (B x) ãₙ →β ãₙ₊₁`),
`tAy0_reducesQ` and **`tAy_Bx_reduces_tAnfQ`** (`Aₙ[B x] →β ãₙ`): the components of `Q x` normalize,
so their index is well defined (the analogue of `tAnf`, `TComp.reduces_tAnf` for `T`); only the
tail has an infinite Böhm tree.

Reading: `Q x →w M (M A₀[B x]) → R R` with `R = M A₀[B x]`; the left copy runs the `T`-stages for
the argument `y = B x`, and each `y` that reaches the head of the application to `R` fires one `x`
(`B x U R → x (U R)`), while `R` itself is never touched by head reduction.  So the x-prefix at
the `M`-stages is exactly `tri n`, the triangular pattern of `T` (the experimental "long gaps end at
`k = 1 + j(j+1)/2`" of round 4 run 2 is the `+1` of `M A_{n+1}` firing).  The invariant to prove is
the `T` invariant with pending `y`'s counted as `x`'s: `k + m + i = tri j`.

Stop (for this run): the first missing lemma is the βη-closure of a shape for the reducts of
`Q x`, `TLCA4.QShape.step` (statement on the board row).  Its difficulty: under βη the `y = B x`
occurrences inside the components reduce (`B x U → λc. x (U c)`), so the grammar `TGram` must be
generalized from a variable `y` to the reducts of `B x` and their partial applications, with the
bound `c` standing for the tail; the tail itself is an arbitrary reduct of `T (B x)` and, as far as
the analysis goes (not Lean-checked), only ever occurs as the last argument.

Experiment (`wip/br1_qwalk.py`, not Lean-checked): 250 random βη-reduction walks from `toLam (Q x)`
(400 steps each, 60% leftmost-outermost β-steps, otherwise a uniformly random β/η redex, size ≤ 3000)
visit 98464 distinct residuals `R` (writing each term `x^k R`), with 1936 repeated visits and no
residual met with two different `k` (x-prefix up to 382): consistent with an invariant `k = φ(R)`.

## Series V, big round, run 2

Item A1 (row M20-TLCA4-Q-NOT-FIXPOINT), step (1) of the design.  Lean, `Start/TLCA4XChain.lean`,
axioms in `docs/goal/evidence/M20-TLCA4-Q-NOT-FIXPOINT-axioms.txt`:

* `XC base x i P` — the `x`-level constructors of `TGram` (`B x P`, `bxPre x P`,
  `λc. xᵐ (P c)` with `m + i' = i`) over an arbitrary indexed base family `base`;
* `XCBase base x` — the base is closed under one βη-step into chains, and a base abstraction
  `λc. b` of height `i` gives the chain `λc. xᵐ b` of height `m + i`;
* `XC.lam_xPow`, **`XC.step`**, **`XC.reduces`** — chains are closed under βη-steps and
  βη-reduction whenever `XCBase` holds (the `bx`, `bx1`, `rq` cases of `TGram.step`, generalized);
* `XCBase.of_closed` (a step-closed base without abstractions), `XC.mono`, and the sanity check
  `TGram.xcBase` (the `T` grammar is an instance).

Not closed.  First missing lemma (unchanged): `TLCA4.QShape.step`; the remaining steps of the
design are (2) the `y`-level grammar of the components `Aₙ[B x]` and their reducts (the `TGram`
of `T y` with `y` replaced by reducts of `B x`, each `y`-application becoming an `x`-chain over it),
(3) `QShape` as an `XC` chain over that base with the tail as last argument, and `QShape.step`
from `XC.step`, (4) `QShape.not_xPrefix` and Church–Rosser as in `T_not_fixedPoint`.

## Series V, big round, run 3

Item A1 closed: **`TLCA4.Q_not_fixedPoint`** — `Q = M∘M∘(BM)∘B∘B` is not a βη fixed-point
combinator (row M20-TLCA4-Q-NOT-FIXPOINT, DONE_STRONG; standard axioms only, see
`M20-TLCA4-Q-NOT-FIXPOINT-axioms.txt`).

New modules (all registered in `Start.lean` and `Start/Capstones.lean`):

- `Start/TLCA4YComponents.lean`: the five reducts of `B (B x)` (`ByR`) and the eight reducts of
  `B (B x) q` (`ByqR`), closed under βη (`ByR.step`, `ByqR.step`).
- `Start/TLCA4YGrammar.lean`: the component grammar of `Q x`, a mutual inductive `YG` / `YC` /
  `YBase`. It is `TGram` with each prefix `xᵐ (·)` replaced by an `x`-chain of height `m` (the
  `XC` constructors), with `BxR`/`BxqR` replaced by `ByR`/`ByqR`, and with the cores `q R`,
  `M R`, `R₁ R₂` and `R q`. The component index equals the chain height minus 1. The grammar is
  closed under βη by a mutual structural induction (`YG.step`, `YC.step`, `YBase.step`). It
  contains `Aᵢ[B x]` at index `i` (`YG.of_tAy`).
- `Start/TLCA4YIndex.lean`: every member reduces to `ãᵢ` (`YG.reduces_tAnfQ`, through the chain
  normal forms `chainNf`), so the index is unique (`YG.index_unique`).
- `Start/TLCA4QNotFixpoint.lean`: the shape is `xᵏ (H ρ)`. Here `ρ` is a reduct of the tail
  `M A₀[B x]`, and `H` is an `x`-chain over a core `P Q` / `M Q`. The conservation law is
  `k + d + i = tri j`, where `d` is the depth of the core below the top of `H`.

  When a core fires, `P Q → C[Q/q]` inserts `i + 1 − b` new `x`'s above the new core. As a
  result, chains with exact natural-number heights cannot carry the law. The chains therefore
  have integer heights (`ZC`), and the base stores `K = k + h`: `QBase x K n Z` means `Z` is a
  core of indices `(i, j)` with `K + i = tri j + n`.

  Results: `YC.subst` (substitution into a chain shifts its heights and preserves the law),
  `QBase.zcBase`, `QShape.step`, and `ZC.unique` (`K − h` is determined by the chain, from
  `QCore.unique` and syntactic separation of the cores from the chain constructors).
  `QShape.not_xPrefix` follows, and Church–Rosser starting from `M A₁[B x] R` gives
  `Q_not_fixedPoint`.

Item A2 (`Start/TLCA4Candidates.lean`) was blocked by its stop rule after about 10 minutes.

- The twelve length-7 hits of the run-1 spine search are encoded as monomial lists `hit1` …
  `hit12`.
- `factor_T`: `(C ∘ T ∘ F) x =w C (T (F x))`.
- Six hits factor through `T`:
  - `hit1 = M∘M∘B∘T∘B`
  - `hit2 = M∘Q∘B`, i.e. `hit2 x =w M (Q (B x))` (`hit2_weq_Q`; this is `Q₂`)
  - `hit3 = M∘T∘BM∘BB∘B`
  - `hit4 = M∘T∘B²M∘BB∘B`
  - `hit11 = T∘T∘B`, i.e. `hit11 x =w T (T (B x))` (`hit11_weq_TT`)
  - `hit12 = M∘BM∘T∘B∘B`
- Stop: `hit5 = M∘M∘BM∘BB∘BM∘B∘B`, which unfolds to `M (M (BM (BB (BM (B (B x))))))`. It has no
  factor `T`, and neither do `hit6`–`hit10` (`M∘M∘BM∘B²M∘…`, `M∘M∘BM∘B³M∘…`, `M∘M∘B²M∘…`). No
  class for them was found.
- Not done: the length-8 and length-9 searches (the length-7 search took 243 s, so length 8 is
  estimated at about 30 min).

## Series V, big round, run 4 (item A3: toward ¬ PolyFiveOne)

New file `Start/TLCA4PolyIdentity.lean`. Everything below is proved in Lean and uses only the
standard axioms; the axioms file is `M20-TLCA4-BETAETA-axioms.txt`.

* **`Bⁿ I` is a βη-unit.**
  * `comp_I_left_betaEta`, `comp_I_right_betaEta`: `I ∘ u` βη-reduces to `u`, and `t ∘ I` to `t`.
    Each takes two β-steps and one η-step, and holds for the terms themselves, not only for their
    action on an argument.
  * `BI_betaEta`: `B I` βη-reduces to `I`.
  * `bpowI_betaEta`: `Bⁿ I` is βη-convertible to `I`.
  * `polyTm_headI_betaEta`, `polyTm_lastI_betaEta`: a monomial `Bⁿ I` can be dropped from the
    front or the back of a polynomial, up to βη.
  * `polyL_filter_noI`: dropping every monomial of base `I` preserves βη-convertibility. Here
    `polyL` reads the empty list as `I`.
* **`x` and `x x` are not βη-convertible** (`var_not_betaEtaConv_selfApp`).
* **`polyFiveOne_noI`.** If `PolyFiveOne` holds, it has a witness with no monomial of base `I`.
  If every monomial had base `I`, the fixed-point equation would collapse to `x =βη x x`.
* **`not_fixedPoint_of_normal`** and `poly_not_fixedPoint_of_normal`, with the predicate
  `BENormal`. If `Y x` βη-reduces to a βη-normal term `N`, then `Y` is not a βη fixed-point
  combinator. The argument: `N =βη x N`, and both sides are normal, so Church–Rosser gives
  `N = x N`, which is impossible by size. So in a fixed-point polynomial `p`, the term `p x` has no
  βη-normal form.

**Still missing (A3).** First missing lemma, the η-aware head comparison:
`theorem TLCA4.polyFiveOne_head_M : PolyFiveOne → ∃ ps, (∀ q ∈ ps, q.base ≠ .I) ∧ <the
fixed-point equation for polyTm ⟨0, .M⟩ ps>`, i.e. the first monomial of a fixed-point polynomial
without `I` is `M`.

`polyApp_reduces_lam` already gives `p x ↠ λt` when the first monomial is `B` or `Bⁿ⁺¹X`. To
exclude `λt =βη x (p x)`, the proof needs the βη head-normal-form arity invariant. It goes as
follows: if two terms are βη-convertible and both have head normal forms `λy₁…y_k. h M₁…M_l` and
`λz₁…z_{k'}. h' N₁…N_{l'}`, then `h` and `h'` agree after the binder shift, and
`l - k = l' - k'`. This invariant is not in the project. Applied here, `λt` with `t` headed by `x`
would need `l - k = 1`, and that has to be compared with the head normal forms that the
`B`-monomial actually produces.

## Series V, big round, run 5 (item A3: toward ¬ PolyFiveOne)

New files `Start/TLCA4HeadArity.lean`, `Start/TLCA4HeadArgs.lean`, `Start/TLCA4FirstMono.lean`,
`Start/TLCA4HeadM.lean` and `Start/TLCA4SecondMono.lean`.
Everything below is proved in Lean and uses only the standard axioms; the axioms file is
`M20-TLCA4-BETAETA-axioms.txt`.

* **The βη head-arity invariant** (`Start/TLCA4HeadArity.lean`). `NSp t h n`: `t` is `var h`
  applied to `n` arguments; `HSp t h d`: `t = λ^k. y a₁ … a_n` with free head `y` (denoting `h`
  outside the binders) and `d = n - k`.
  * `HSp.step`, `HSp.etaStep`, `HSp.betaEtaReduces`: βη-reduction preserves `h` and `d` (β-steps
    can only happen inside arguments; an η-step removes the innermost binder together with the last
    argument, `NSp.of_lift`).
  * `HSp.unique`, **`HSp.betaEtaConv`**: βη-convertible terms with such head normal forms have the
    same head and the same arity difference (Church–Rosser for βη).
  * **`fixedPoint_hsp`**, `not_fixedPoint_of_hsp`: a head normal form of `Y x`, for a βη
    fixed-point combinator `Y`, has head `x` and arity difference `1`.
* **Arguments** (`Start/TLCA4HeadArgs.lean`). `spn y [a_l, …, a_1] = y a_1 … a_l`, `lamK k t = λ^k. t`.
  * `RForm`, `RForm.betaEtaReduces`: every βη-reduct of `λ^k. y a⃗` is `λ^{k-j}. (y-j) c⃗` where the
    last `j` arguments reduce to the bound variables `0, …, j-1` and every other argument reduces to
    the `j`-fold lifting of the corresponding `c`.
  * **`lamK_spn_betaEtaConv`**: `λ^k. y a⃗ =βη λ^k. y' b⃗` implies `y = y'` and `a⃗`, `b⃗` pointwise
    βη-convertible (same length).
  * `spn_betaEtaConv_eta`, `app_betaEtaConv_etaArgs`: η-expansion `x a =βη λz₁ … z_k. x a↑ z₁ … z_k`.
  * **`fixedPoint_args`**: if `Y x =βη x (Y x)` and `Y x =βη λ^k. y a⃗`, then `y = k` and `a⃗` is
    pointwise βη-convertible to `(Y x)↑ᵏ, z₁, …, z_k`.
  * **`fixedPoint_firstArg_hsp`**: the first argument, if it has a free-headed head normal form, has
    head `x` and arity difference `1` (it is again `(Y x)↑ᵏ`).
  * `bM_not_fixedPoint`: `B M x ↠ λz. x z (x z)`, whose first argument is `z`; not a fixed point.
* **Monomials and the first monomial** (`Start/TLCA4FirstMono.lean`).
  * `bpow_app_reduces`: `Bⁿ X u ↠ λz₁ … z_n. X (u z₁ … z_n)` for closed `X`.
  * **`mono_not_fixedPoint`**: no monomial `Bⁿ X`, `X ∈ {B, M, I}`, is a βη fixed-point combinator
    (`Bⁿ B x` has arity difference `-1`; `Bⁿ M x ↠ λz⃗. x z⃗ (x z⃗)` has the variable `z₁` (or `x`
    itself when `n = 0`) as first argument; `Bⁿ I x =βη x`).
  * **`polyFiveOne_two`**: `PolyFiveOne` has a witness with at least two monomials, none of base `I`.

  * `GY a b t`: every occurrence of the variable `b` in `t` is inside the subterm `a b`.
    `GY.lift`, `GY.subst`, `GY.of_lift`, `GY.step`, `GY.etaStep`, `GY.betaEtaReduces`: preserved by
    βη-reduction (a β-step substitutes whole `a b` pairs; an η-step cannot separate `b` from `a`).
  * **`headB_not_fixedPoint`**: no polynomial `Bⁿ B ∘ R` (`R` a nonempty polynomial) is a βη
    fixed-point combinator. Apply the fixed-point equation to fresh `z₁ … zₙ g y`: by
    `bpowB_action` the left side is `R x z⃗ (g y)`, in which `y` occurs only inside `g y`; every
    βη-reduct of the right side `x (P x) z⃗ g y` is `x c⃗ y` (`RForm` with `k = 0`), which violates
    `GY`. Church–Rosser gives the contradiction.
  * **`polyFiveOne_head_baseM`**: `PolyFiveOne` has a witness `Bⁿ M ∘ m₂ ∘ … ∘ m_k` with `k ≥ 2`
    and no monomial of base `I`. So the first monomial of a βη fixed-point polynomial has base `M`
    (the plan's "first monomial is `M`", up to the exponent `n`).

* **The exponent of the first monomial** (`Start/TLCA4HeadM.lean`).
  * `occL y t`: the number of free occurrences of `y`; `occL_lift_lt`, `occL_lift_ge`,
    `occL_lift_eq`, **`occL_subst`**: `occL y (subst s x M) = occL y' M + occL x M * occL y s`.
  * `LamI t`: every abstraction binds a variable that occurs; `lamI_toLam`: the translation of any
    `B`,`M`,`I`-term with variables is a λI-term.
  * **`LamI.betaEtaReduces`**: βη-reduction preserves `LamI` and never decreases `occL y`;
    `occL_zero_betaEtaReduces`: a variable that does not occur never appears.
  * **`headBM_not_fixedPoint`**: no polynomial `Bⁿ⁺¹ M ∘ R` is a βη fixed-point combinator. Applied
    to fresh `z₁ … z_{n+1}` (`bpowM_action`) the fixed-point equation gives
    `U U =βη x (P x) z⃗` with `U = R x z⃗`. In every reduct of the left side `z_{n+1}` occurs at
    least twice; every reduct of the right side is `x c⃗ z_{n+1}` with `z_{n+1}` not in `c⃗`.
  * **`polyFiveOne_head_M`**: `PolyFiveOne` has a witness `M ∘ m₂ ∘ … ∘ m_k`, `k ≥ 2`, with no
    monomial of base `I`. This is the plan's first missing lemma of run 4.

* **The second monomial** (`Start/TLCA4SecondMono.lean`). For `P = M ∘ m₂ ∘ …`, apply the
  fixed-point equation to fresh variables after `P x =w (R x) (R x)`, `R = m₂ ∘ …`
  (`gy_contra`, `occ_contra`: the two contradictions above for an arbitrary left side; `poly_tail`).
  * **`secondBB_not_fixedPoint`**: `m₂ = Bᵃ⁺¹ B` is impossible (`R x (R x) z⃗ g y =w u (R x) z⃗ (g y)`,
    `GY`).
  * **`secondBM_not_fixedPoint`**: `m₂ = Bᵃ⁺² M` is impossible (`R x (R x) z₁ … z_{a+1} =w W W`,
    `W = u (R x) z⃗`, occurrence counting).
  * **`polyFiveOne_second`**: `PolyFiveOne` has a witness `M ∘ m₂ ∘ …` without base-`I` monomials
    and `m₂ ∈ {B, M, B M}` (consistent with T = M∘BM∘B, Q = M∘M∘BM∘B∘B and the length-7 hits).

**Still missing (A3).** The remaining second monomials `B`, `M`, `B M` and the later monomials.
For `m₂ = B` the pairing is `R' x ((R x) y)`, with `R x` not a variable; for `m₂ ∈ {M, B M}` the
duplicated term contains no fresh variable. A generalisation of `GY` to "`y` occurs only as the
last argument of a fixed term up to βη" or an induction along the polynomial is the next step.
First missing lemma (a statement): `theorem TLCA4.polyFiveOne_third : PolyFiveOne → ∃ m₂ m₃ ps, <m₂ ∈ {B, M, BM}> ∧ <constraint on m₃> ∧ <fixed-point equation for polyTm ⟨0, .M⟩ (m₂ :: m₃ :: ps)>`,
or a proof that `m₂ = B` is impossible. The final target remains
`theorem TLCA4.no_fixedPoint_betaEta : ¬ TLCA4.ProblemFiveOne`.

## Series V, big round, run 6 (item A3: toward ¬ PolyFiveOne)

**The third monomial** (`Start/TLCA4ThirdMono.lean`; all theorems use only propext,
Classical.choice and Quot.sound).

* **`arity_contra`**: if `P x z⃗ =w x a₁ … a_l` with `l ≠ |z⃗| + 1`, then `P` is not a βη
  fixed-point combinator (the head-arity invariant `HSp.betaEtaConv` against `x (P x) z⃗`);
  `hsp_toLam_apps_var`.
* **Two monomials**: `polyMB_not_fixedPoint` (`M∘B x z =w x (B x z)`), `polyMM_not_fixedPoint`
  (`(x x)(x x)`), `polyMBM_not_fixedPoint` (`x (BMx) (x (BMx))`) — all by `arity_contra`; so a
  fixed-point polynomial has at least three monomials.
* **`m₂ = B`** (`secondB_unfold`: `P x z₁ r⃗ =w m₃ u (B U z₁) r⃗`, `U = (m₃ ∘ …) x`):
  `thirdB_B_not_fixedPoint` (`u (U (z₁ z₂))`, pairing), `thirdB_BB_not_fixedPoint` (`m₃ = Bᵃ⁺¹ B`,
  pairing), `thirdB_BM_not_fixedPoint` (`m₃ = Bᵃ⁺¹ M`, occurrence counting). So `m₃ = M`.
* **`m₂ ∈ {M, B M}`** (`secondM_unfold`: `P x z⃗ =w m₃ u g h z⃗` with `g, h` free of the fresh
  variables: `(g, h) = (U, U U)` resp. `(B M U, U (B M U))`): `thirdM_BB_not_fixedPoint`
  (`m₃ = Bᵃ⁺² B`, pairing), `thirdM_BM_not_fixedPoint` (`m₃ = Bᵃ⁺³ M`, occurrence counting).
* **`polyFiveOne_third`**: `PolyFiveOne` has a witness `M ∘ m₂ ∘ m₃ ∘ …` without base-`I`
  monomials with `(m₂, m₃) = (B, M)`, or `m₂ ∈ {M, B M}` and `m₃ ∈ {B, B B, M, B M, B² M}`.
  Consistent with T = M∘BM∘B, Q = M∘M∘BM∘B∘B and the length-7 hits.
* **The branch `M ∘ B ∘ M`** (`thirdBM_unfold`: `P x z₁ r⃗ =w m₄ w u' (B U z₁) r⃗`):
  `polyMBM'_not_fixedPoint` (`M∘B∘M x z₁ =w x x (B (M x) z₁)`; the first argument `x` would have to
  be βη-equal to `P x =βη x (P x)`, against `HSp`), `fourthBM_B1_not_fixedPoint`,
  `fourthBM_BB_not_fixedPoint` (pairing), `fourthBM_BM_not_fixedPoint` (occurrence counting),
  hence `fixedPoint_BM_fourth`: `m₄ ∈ {B, M, B M}`, and **`polyFiveOne_fourth`**.

**A uniform prefix bound** (`Start/TLCA4PrefixBound.lean`).

* `prefix_BB_contra`, `prefix_BM_contra`, **`prefix_bound`**: if `P x z⃗ =w m w a⃗ z⃗` for every
  list `z⃗`, where `w` and `a⃗` contain no fresh variable, and `P` is a βη fixed-point combinator,
  then `m = Bⁿ B` with `n < |a⃗|`, or `m = Bⁿ M` with `n ≤ |a⃗|` (or `m` has base `I`). This is the
  common core of all pairing/occurrence exclusions above.
* `secondM_unfold_cons`, **`fixedPoint_M_fourth`**: for `M ∘ m₂ ∘ m₃ ∘ m₄ ∘ …` with
  `m₂ ∈ {M, B M}` the unfolding is `m₃ u g h z⃗` (`u = (m₄ ∘ …) x`), and for
  `m₃ = B, M, B M, B² M` it continues to `u a⃗ z⃗` with `a⃗ = [g h]`, `[u, g, h]`, `[g, u g, h]`,
  `[g, h, u g h]`. So `m₄ ∈ {B, M, B M}` after `m₃ = B`, and `m₄ ∈ {B, B B, B² B, M, …, B³ M}` after
  `m₃ ∈ {M, B M, B² M}`.

**What remains (A3).** The case tree does not close by these local arguments: T = M∘BM∘B and
Q = M∘M∘BM∘B∘B pass every local test and needed the global stage/grammar arguments
(`T_not_fixedPoint`, `Q_not_fixedPoint`). Open sub-branches after run 6:
* `M ∘ B ∘ M ∘ m₄ ∘ …`, `m₄ ∈ {B, M, B M}`;
* `M ∘ m₂ ∘ B B ∘ …`, `m₂ ∈ {M, B M}` (the unfolding `u g (h z₁) z⃗` puts a fresh variable inside
  an argument, so `prefix_bound` does not apply directly);
* `M ∘ m₂ ∘ m₃ ∘ m₄ ∘ …` with `m₂ ∈ {M, B M}`, `m₃ ∈ {B, M, B M, B² M}` and `m₄` as in
  `fixedPoint_M_fourth`; also the three-monomial ends `M ∘ m₂ ∘ m₃` of these branches, which need
  a first-argument comparison (as in `polyMBM'_not_fixedPoint`).
Named conjecture (unchanged in substance): `TLCA4.no_fixedPoint_betaEta : ¬ TLCA4.ProblemFiveOne`;
evidence: the exclusions above, T and Q, and the spine search of round 4 (length ≤ 7, n ≤ 3,
x-spine cap 10; not Lean-checked).
First missing lemma (a statement): `theorem TLCA4.fixedPoint_BM_fifth (m₄ : Mono) (ps : List Mono) (hm : m₄ = ⟨0, .B⟩ ∨ m₄ = ⟨0, .M⟩ ∨ m₄ = ⟨1, .M⟩) : FP (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: m₄ :: ps)) → <constraint on the fifth monomial>`, or a first-argument version of
`prefix_bound` (arguments containing fresh variables only as `g z` with `g` fixed).

## Series V, big round, run 7 (item A3: toward ¬ PolyFiveOne)

**The argument-count automaton** (`Start/TLCA4Automaton.lean`; standard axioms only, see the
axioms file). `prefix_bound` (run 6) is turned into an invariant carried along the whole
polynomial.

* `Unf P m ps a⃗`: for every `z⃗`, `P x z⃗ =w (m ∘ ps) x a⃗ z⃗`, with every argument in `a⃗` free of
  the fresh variables (`GY`). Write `L = |a⃗|`.
* `actM_args`, `actB_args`: the weak actions `Bⁿ M w a⃗ z⃗ =w w a₁…aₙ (w a₁…aₙ) aₙ₊₁ … z⃗` and
  `Bⁿ B w a⃗ z⃗ =w w a₁…aₙ (aₙ₊₁ aₙ₊₂) aₙ₊₃ … z⃗`.
* **`unf_step`**: in a state of a βη fixed-point polynomial, the head monomial is `Bⁿ M` with
  `n ≤ L` (new state with `L + 1` arguments), or `Bⁿ B` with `n + 2 ≤ L` (new state with `L − 1`
  arguments), or `Bⁿ B` with `n + 1 = L` (the *escape*: a fresh variable enters an argument), or
  has base `I`.
* **`unf_end`**: if the polynomial ends (`ps = []`, so the head is `x` itself) in a state with
  `L ≥ 1`, then the last monomial is `B` or `B B` and `L = 2` (`arity_contra` on each of the other
  cases; for the escape a single fresh argument is supplied).
* `Adm L m ps`: the admissibility predicate of this automaton; **`unf_adm`**: every reachable state
  is admissible; **`polyFiveOne_adm`**: if `PolyFiveOne` holds, it has a witness
  `M ∘ m₂ ∘ … ∘ m_k`, without base-`I` monomials, with `Adm 1 m₂ [m₃, …, m_k]` (the initial state
  after `M` is `u u z⃗`, `u = (m₂ ∘ …) x`, so `L = 1`).
* `adm_T`, `adm_Q`: T and Q are admissible. Python (`wip/a3_adm.py`, not Lean-checked): all 14
  spine hits of length ≤ 7 are admissible; admissible tails over `n ≤ 3`: 0, 12, 80, 736, 5952,
  49248, 398720 for tail lengths 1–7 (most of them through the escape).

This subsumes the pairing/occurrence parts of `polyFiveOne_second`/`third`/`fourth` and
`fixedPoint_M_fourth` in one statement; without escape, the admissible paths are Dyck-like
(`M`-steps up, `B`-steps down, end at `L = 2` with `B` or `B B`), which matches T, Q and all hits.

**What remains (A3).** (1) The escape states `u a₁ … a_{L−1} (a_L z₁) z⃗`: a fresh variable occurs
inside an argument, so neither `GY` nor `prefix_bound` applies as stated; a version of `Unf` with
arguments of the form `g z` (`g` fixed) is needed. (2) The end at `L = 2`: `x (a₁ a₂) z⃗` resp.
`x a₁ (a₂ z₁) z⃗`, where the head-arity invariant is satisfied and a first-argument comparison
(`a₁ a₂ =βη P x`) is needed — this is where T and Q needed the global stage/grammar arguments.
Named conjecture (unchanged): `TLCA4.no_fixedPoint_betaEta : ¬ TLCA4.ProblemFiveOne`.
First missing lemma (a statement):
`theorem TLCA4.unf_escape (P : Tm) (m : Mono) (ps : List Mono) (args : List Tm) (h : Unf P m ps args) (hm : m = ⟨args.length - 1, .B⟩) (hY : <P is a βη fixed point>) : <admissibility of ps from an escape state>`.

**One step past the escape** (`Start/TLCA4Escape.lean`; standard axioms only).
* `wrap_BB_contra`, `wrap_BM_contra`, **`wrap_bound`**: if `P x z₁ z⃗ =w m w a⃗ (f z₁) z⃗` for every
  `z⃗` (`w`, `f`, `a⃗` free of the fresh variables), then `m = Bⁿ B` or `m = Bⁿ M` with `n ≤ |a⃗|`
  (or base `I`): pairing of two later fresh variables, resp. two occurrences of a fresh variable
  (for `n = |a⃗|` the duplicated variable is `z₁` inside `f z₁`).
* **`unf_escape_next`**: after an escape at argument count `L` (head `B^(L−1) B`), the next
  monomial is `Bⁿ B` or `Bⁿ M` with `n ≤ L − 1`.
Updated first missing lemma: an automaton for the escape states, i.e. a state predicate with one
argument `f z₁` carried along (after `Bⁿ B` with `n = L − 1` it becomes `(f z₁) z₂`, after
`Bⁿ M` it is duplicated), with its step lemma `TLCA4.unfW_step`, and the end case at `L = 2`.

## Series V, big round, run 8 (item A3, plan 4.4: the candidates themselves)

Plan 4.4: the monomial case tree is not extended further (T and Q pass all local tests); A3 works
on the length-7 hits without a factor `T` directly. All new theorems: standard axioms only
(`docs/goal/evidence/M20-TLCA4-BETAETA-axioms.txt`).

**hit5 = M∘M∘BM∘BB∘BM∘B∘B: stages** (`Start/TLCA4Hit5Stages.lean`). With `u = B (B x)`,
`v = BM u`, `w = BB v`, `s = BM w`, `hit5 x = M (M s)` syntactically (`hit5_act`), and
* `h5w_app`: `w A Z W →w x (A (u A) (Z W))`; `h5s_app`: `s A W →w x (A (u A) (w A W))`;
* `h5A_app`: `uⁿ s Z W →w xⁿ (s Z W)`;
* **`h5_stage_step`**: `s (uⁿ s) W →w x^{n+1} (s (uⁿ⁺¹ s) (w (uⁿ s) W))`;
* **`hit5_stage`**, `hit5_stage_weq`, `hit5_stage_betaEta`: `hit5 x →w x^{tri n} (s (uⁿ s) Wₙ)`
  for every `n` (`W₀ = M s`, `Wₙ₊₁ = w (uⁿ s) Wₙ`).
So hit5 has exactly the stage pattern of T and Q (x-prefix at the triangular numbers), with a
tail `Wₙ` that is only passed along linearly.

**hit5: components and their index** (`Start/TLCA4Hit5Components.lean`). The components `uⁿ s`
have the βη-normal forms `bₙ = λac. xⁿ⁺¹ (a U (λd. x (a U (c d))))`, `U = λzw. x (a z w)`:
* `h5nf_nf`, `h5nf_injective`, `Bx_h5nf_reduces` (`B (B x) bₙ →β bₙ₊₁`);
* `bm_red`, `h5v_reduces`, `h5w_reduces`, **`h5s_reduces`** (`s →βη b₀`);
* **`h5A_reduces`** (`uⁿ s →βη bₙ`) and **`h5A_index_unique`** (`uⁿ s =βη uᵐ s → n = m`).

**Python (`wip/a3_hits.py`, not Lean-checked).** Random βη-walks from `p x` (hit5–hit10): the map
residual ↦ x-prefix has no conflict (hit6–hit10: 30 walks each, 3000–6300 visits; hit5: 60 walks
× 400 steps, 23765 residuals, 0 conflicts). On the leftmost-outermost
reduction of hit5 x, every reduct of the form `x^k (P Q W…)` with `P`, `Q` reducing to `b_i`, `b_j`
satisfies `k + i = tri j` (the invariant of the T proof), checked on the first 120 steps.

**Four classes, not six** (`Start/TLCA4HitClasses.lean`). `wip/a3_hitg.py` (not Lean-checked)
printed the normal forms of the tails; in Lean:
* `f6_red`, `f7_red`: `B ∘ BB ∘ B` and `B²B ∘ B ∘ B`, applied to `x`, both βη-reduce to
  `λpqbc. x (p q (b c))`;
* `polyOf_conv_of_tails`: `C ∘ F` and `C ∘ F'` are βη-equal at `x` when the tails reduce to a
  common term;
* **`hit6_conv_hit7`**: `hit6 x =βη hit7 x`; **`hit8_conv_hit9`**: `hit8 x =βη hit9 x`.
So the six hits without a factor `T` form at most four βη-classes: hit5, hit6 ≡ hit7,
hit8 ≡ hit9, hit10 (hit5 and hit10 share the tail `BB ∘ BM ∘ B ∘ B` and differ in the third
monomial, `BM` vs `B²M`).

**A generic stage lemma** (`Start/TLCA4StageGen.lean`; plan 4.4 step 3, first part). For
combinatory terms `s`, `g` with `StageS`: `s A W →w x (A (g A) W')` and `StageG`:
`g A Z W →w x (A Z W')` (some `W'`), `iterT_g_app`, `stage_step_gen` and **`stage_gen`** give
`M (M s) →w x^{tri n} (s (gⁿ s) W)` for every `n`. Instances (all Lean-checked):
* Q (`g = u = B (B x)`, `s = v = BM u`): `Q_stageS`, **`Q_stage_gen`**;
* hit5 (`g = u`, `s = BM (BB v)`): `hit5_stageS`, `hit5_stageG`;
* hit6 (`F = B (BB (B x))`, `g = B²M F`, `s = BM g`; `g A Z W →w x (A Z (F A Z W))`): **`hit6_stage`**;
* hit8 (`g = B³M F`, `s = BM g`; `g A Z W →w x (A Z (W (F A Z W)))`): **`hit8_stage`**.
So Q and the classes hit5, hit6 ≡ hit7, hit8 ≡ hit9 all have the triangular stage pattern with a
component family `gⁿ s`; hit10 (third monomial `B²M`) is not of this form. Working conjecture (evidence:
Q proved, `Q_not_fixedPoint`; the hit5 invariant tested in Python only; not a theorem): every `M (M s)` with `StageS`/`StageG` and
normalizing components `gⁿ s` of pairwise distinct normal forms is not a βη fixed point.

**What remains (A3).** `hit5_not_fixedPoint` needs the analogue of `QShape`: a grammar of the
βη-reducts of `hit5 x` (x-chains over cores `P Q W` with components `P`, `Q` of indices `i`, `j`,
`k + i = tri j`, plus the partial unfoldings of `s A W` through `M (w A) W`, `w A (w A) W`, …),
closed under one βη-step. First missing lemma:
`theorem TLCA4.H5Shape.step {x : ℕ} {N N' : Lambda} (h : H5Shape x N) (hs : betaEtaStep N N') : H5Shape x N'`
(with `H5Shape` the shape predicate, to be defined as `QShape` was). Structural remark: the
components of `Q x` are `Aₙ[B x] = uⁿ v` (`tAy`: `A₀[B x] = B M (B (B x)) = v`), and those of
`hit5 x` are `uⁿ s` with `s = B M (B B v)`, so the `ByR`/`YG` machinery should adapt with a new
base. Then the same for the classes hit6, hit8, hit10.

## Series V, big round, run 9

**The generic shape argument with arbitrary tails** (`Start/TLCA4TailShape.lean`; item A3,
plan 4.4 step 3). The stages of hit5 update the tail (`Wₙ₊₁ = w (uⁿ s) Wₙ`), so the `QShape`
argument (tail = a reduct of a fixed term, chains pass their bound variable unchanged) does not
apply as it stands. The module abstracts the pattern of `T_not_fixedPoint`/`Q_not_fixedPoint`:
* `TC base x` — integer-height `x`-chains `B x C`, `(λab. x (a b)) C` and `λc. xᵐ (C T)` with an
  **arbitrary** tail transformer `T` (in which `c` may occur), over a base family;
* `TailCores base x` — hypotheses on a `K`-indexed core family: a βη-step of a core gives a chain
  at the same height; no core is an abstraction, a variable or a chain head; a core determines
  `K − n`;
* **`TC.step`** (via `TC.beta_lift`: an abstraction chain applied to any tail stays a chain),
  `TC.reduces`; `AShape` (`xᵏ (H ρ)`, any `ρ`, `H ∈ TC (base (k + h)) h`), **`AShape.step`**,
  `AShape.reduces`; **`TC.unique`**, **`AShape.not_xPrefix`**;
* **`not_fixedPoint_of_ashape`** — if `L →βη N₀` with `AShape base x N₀`, then `¬ L =βη x L`.
* Non-vacuity: `ZC.toTC`, **`QBase.tailCores`** (the cores of Q satisfy `TailCores`), and
  **`Q_not_fixedPoint_of_ashape`** re-derives `Q_not_fixedPoint` from the generic theorem.

**Two-argument chains** (`Start/TLCA4TailW.lean`): the tail update of hit5 goes through
`w Z →w B (v Z)` with `v Z` a chain, and `B C Y ρ →w C (Y ρ)`. Generically over a base family
(with the hypotheses of `TC.step`), `TW` collects the reducts of `B C` for a chain `C`: `B C`,
`λbc. xᵐ (C' T)` (`C'` = `C` lifted under `b, c`; `T` arbitrary) and `λb. C`. **`TW.step`**,
`TW.reduces`: closed under βη (inner β-steps of `C (b c)` included, via `lift2_beta`; η of
`λc. C' c` gives `λb. C`); **`TW.fire`**: a member `λb. c` applied to any `Y` gives a chain
`c[Y/b]` of the same height. These are the forms `wB`, `wP`, `wK` of the design below.

**Restricting the base** (`Start/TLCA4TailRestrict.lean`). A hit5 core `W Y` has a head `W ∈ TW`
over the *same* core family; Lean's kernel rejects this as a nested inductive (the parameters of
`TW` would contain the local variables `x`, `K`; checked). Plan: define the core family without
nesting (one inductive with tags, or the chains' data unfolded) and prove its βη-closure by strong
induction on `Lambda.nodes` of the core, applying `TC.step`/`TW.step` to the base restricted to
smaller terms. Generic facts for this: `TC.mono`, `TW.mono` (monotone in the base),
**`TC.restrict`** (base members used in a chain have at most its size) and **`TW.restrict`**
(strictly smaller for `TW`), `nodes_xPow_le`; `TC.exists_level`, `TW.exists_level` (a chain over a
union of bases uses one of them, for a family defined by levels `E (k+1) = E k ∪ {M W, W Y : W ∈
TW (E k)}`); **`TC.step2`**, **`TW.step2`** (closure with two bases `base ⊆ base'`: a step may
enlarge base members, so the restricted base only needs its steps to be chains over the full one).

**The extension by two-argument heads** (`Start/TLCA4TailExt.lean`). For any core family `core`,
`ExtL core x 0 = core`, `ExtL core x (k+1) = ExtL core x k ∪ {M W, W Y : W ∈ TW (ExtL core x k)}`,
`Ext core x K n P = ∃ k, ExtL core x k K n P`. **`Ext.step`**: if every βη-step of a core is a
chain over `Ext core x K`, then every βη-step of a member of `Ext core x K` is (strong induction
on `Lambda.nodes` with `TW.step2`, `TW.restrict`, `TW.exists_level`; root steps by `TW.fire` and
`M W → W W`); `Ext.not_lam`; **`TW.unique`** (for a family with `TailCores`, a two-argument chain
determines `K − n`; caveat for hit5: the forms `W Y` overlap syntactically with inner cores `P Q`,
so the uniqueness field of the extension needs a disjointness argument specific to the family). So for hit5 the forms `M Wz`, `Wz Y` come for free: what is left is
the inner core family (cores `P Q`, `M Q` and the forms of `v Z`) and its firing into chains over
the extension.
All standard axioms only (`M20-TLCA4-BETAETA-axioms.txt`).

**What remains for hit5** (design, not Lean-checked). A core family `H5Base x K n` with
`TailCores`: cores `P Q` (components of indices `i`, `j`, `K + i = tri j + n`) plus the partial
unfoldings of `s Z ρ →w M (w Z) ρ →w w Z (w Z) ρ →w v Z (w Z ρ) →w x (Z (u Z) (w Z ρ))`, i.e.
`M Wq`, `Wq Y` (`Wq` a reduct of `w Z`, `Y` arbitrary; offset one `x` before the core `Z (u Z)`)
and the forms of `v Z` (`B M R Z`, `(λab. M (a b)) R Z`, …, index `(j+1, j+1)`). The component
grammar (the analogue of `YG`/`YC`/`YBase`) needs `x`-chains under the parameter `q` *and* under
the extra binder `b` of `B (v q) = λbc. v q (b c)` (inner β-steps of `v q` there), so it should be
indexed by the de Bruijn positions of both `x` and `q`, with a lifting lemma for components.
First missing lemma (with `Ext` from `Start/TLCA4TailExt.lean`):
`theorem TLCA4.H5Core.step {x : ℕ} {K n : ℤ} {P P' : Lambda} (h : H5Core x K n P) (hs : betaEtaStep P P') : TC (Ext (H5Core x) x K) x n P'`
for the inner core family `H5Core` (then `Ext.step` gives the `step` field of
`TailCores (Ext (H5Core x) x) x`; uniqueness and the non-chain-head fields remain); then `hit5_not_fixedPoint` follows from
`not_fixedPoint_of_ashape` and `hit5_stage_betaEta`.

## Series V, big round, run 10

Item A3 (plan 4.4, step 2 for hit5): βη-closed grammars for the next two layers of hit5
(`u = B (B x)`, `v = B M u`, `w = B B v`, `s = B M w`). All standard axioms only
(`M20-TLCA4-BETAETA-axioms.txt`).

**The `w`-layer** (`Start/TLCA4Hit5W.lean`). `YB x` is `YBase x` with integer heights; `LiftB base`
lifts a base family under one more binder. **`TC.lift`**: chains with arbitrary tails are stable
under `lift 1 0` (the tail becomes `lift 1 1 T`); `TC.step_liftB`: lifted chains are closed under
βη when the base is; `YC.toTC`: the chains of `Q` are chains with arbitrary tails. The grammar:
`WqR x` (bodies under `q`): `B Vq` with `Vq ∈ TC (YB x) (x+1) 1`, and `λb. C` with
`C ∈ TC (LiftB (YB x)) (x+2) 1` — the arbitrary tail absorbs `b c` and its descendants, so the
inner β-steps of `v q` under the extra binder need no new grammar; `WR x`: `B B V`,
`(λbc. B (b c)) V`, `(λbcyz. b c (y z)) V` (`V ∈ YG x 0`) and `λq. W` (`W ∈ WqR x`).
**`WqR.step`**, **`WR.step`**, `WR.reduces`, **`WR.of_h5w`**, `WR.of_reduces`.

**The `s`-layer** (`Start/TLCA4Hit5S.lean`). **`TC.subst_liftB`**: substituting any `Y` for the
extra binder of a lifted chain gives a chain over the base (the firing `(λb. C) Y`). `WqF x`: the
reducts of `W q` (`W ∈ WR x`): `W q` itself and `WqR x` (via `subst (var k) k (lift 1 (k+1) W) = W`).
`SqR x`: `M Wq`, `Wq Y` (`Y` arbitrary) and chains of height `1` over `YB x`. `SR x`: `B M W`,
`(λab. M (a b)) W`, `(λab. a b (a b)) W` (`W ∈ WR x`), `λq. S` (`S ∈ SqR x`) and the two
η-contracta (`V ∈ YG x 0` from `λq. V q`, and `f` with `f q ∈ WqF x`). **`WqF.step`**,
**`SqR.step`**, **`SR.step`**, `SR.reduces`, **`SR.of_h5s`**, `SR.of_reduces`.

**What remains for hit5.** The components are `uⁿ s`: the analogue of `YG`/`YC`/`YBase` with `SR x`
as an extra base at index `0`, whose q-level chains need arbitrary tails (the β-contractum of
`(λq. S) q` is an `SqR` body, which contains `TC` chains with arbitrary tails, while `YC` only has
the tail `q`). A direct definition nests `TC` inside the mutual family, which the kernel rejected
in run 9; the level-wise construction of `Start/TLCA4TailExt.lean` is the template. First missing
lemma unchanged: `TLCA4.H5Core.step` (the inner core family over the component grammar); then the
`TailCores` fields and `hit5_not_fixedPoint` via `not_fixedPoint_of_ashape` and
`hit5_stage_betaEta`.

## Big round 2, run 1

Item A1 (hit5 is not a βη fixed-point combinator).  The former first missing lemma,
`TLCA4.H5Core.step`, is proved.

* `Start/TLCA4Hit5TW.lean` — the `w`- and `s`-layers again, with the bodies of the `w`-reducts
  taken in `TW (YB x) (x + 1) 1` (the family `Ext` uses), so that substitution lands in `TW`:
  `WT.step`, `WqT.step`, `SqT.step`, `ST.step`, `ST.of_h5s`; generic substitution of a term for
  `q` in a chain or a two-argument chain under `q`: `TC.subst_gen`, `TW.subst_gen`.
* `Start/TLCA4Hit5Grammar.lean` — the components `uⁿ s`: `HG x i` (YG components, `s`-reducts at
  index 0, `R P` with `R` a reduct of `B (B x)`, abstractions over chains), `HC x n` (chains of
  integer height under `q`, **arbitrary tails**), `HB x n` (cores `q R`, `M R`, `R₁ R₂`, `P q`,
  `M Wq`, `Wq Y`).  `HG.step`/`HC.step`/`HB.step` (mutual), `HC.eta_inv`, `HG.fire_q`,
  `HG.of_h5A` (`uⁿ s` has index `n`).
* `Start/TLCA4Hit5Core.lean` — `H5Core x K n`: `P Q` (indices `i, j`, `K + i = tri j + n`),
  `M Q` (`K + j = tri j + n`), `M (W Q)` and `(W Q) Y` with `W ∈ WT x`
  (`K + j = tri (j + 1) + n - 1`).  `ByqR.substH`, `HC.toTC`, `HB.substH`, `HC.substH`;
  **`H5Core.step`**: every βη-step of a core is a chain over `Ext (H5Core x) x K`;
  **`H5Ext.step`** (by `Ext.step`); `hit5_reduces_shape` (stage 0, core `s s`, `K = 0`);
  **`hit5_not_fixedPoint_of_tailCores`**: `TailCores (Ext (H5Core x) x) x` implies that
  `hit5 x` is not βη-convertible to `x (hit5 x)`.

First missing lemma: `theorem TLCA4.H5Ext.tailCores (x : ℕ) : TailCores (Ext (H5Core x) x) x`.
Its fields `step` (`H5Ext.step`) and `not_lam` (`Ext.not_lam H5Core.not_lam`) are proved; `ne_var`,
`ne_bx`, `ne_bx1` are syntactic; `unique` is the substantial one.  Route for `unique`:

1. *Index uniqueness of `HG`.*  The chains have arbitrary tails, so components need not normalize
   and the normal-form argument of `YG.index_unique` does not apply.  Replacement (a βη-invariant
   of head normal forms): `XDepth x a k N :⇔ N =βη xᵏ M` with `M` neutral with head `a`; for
   `a ≠ x` it is unique (proved in a scratch file this run: `conv_app_var_inj`,
   `xPow_conv_unique`, `XDepth.unique`, from `HSp.betaEtaConv`).  To prove: a component `P` of
   index `i` has `XDepth x a (i + 1) (P a b)` for `a ≠ x` and any `b` — by mutual induction over
   `HG`/`HC`/`HB`, uniformly in the tail (each chain layer contributes its height in `x`'s; the
   cores `q R`, `M R`, `R₁ R₂`, `P' q`, `M Wq`, `Wq Y` end in an `a`-headed term after
   `0, 1, 1, i' + 1, 1, 1` further `x`'s).
2. *`q`-freeness.*  Every member of `HC`, `TC (YB x) (x + 1)`, `TW (YB x) (x + 1)`, `WqT x`, `SqT x`
   has the variable `0` free; a lifted term does not.  This separates `TW.wP`/`TW.wK` heads and
   `B C` heads (with `C` a top-level chain) from components.
3. *Separation*: `lamM` is not a component; a component is not of the form `W Q` with `W ∈ WT x`;
   `TW` members over any base are not components.
4. A version of `TC.unique`/`TW.unique` that needs only the syntactic fields (no `step`), used by
   strong induction on `Lambda.nodes` for the extension levels.

## Big round 2, run 3

Item A1, step 1 of the route above is done: `Start/TLCA4Hit5Index.lean`.

* `XDepth x a k N` (`N =βη xᵏ M`, `M` neutral with head `a`) with `XDepth.unique` for `a ≠ x`
  (moved from the scratch file); `XDz` is its integer-height form.
* Head-reduction laws of the combinators (`law_B`, `law_M`, `law_bxPre`, `law_bmPre1`,
  `law_bmPre2`, `law_bbPre`, `law_bbPre2`, `law_byl1`–`law_byl3`); `ByR.conv`:
  `R P z w =βη x (P z w)` for every reduct `R` of `B (B x)`; `ByqR.conv` likewise for the reducts
  of `B (B x) q` after `q := a`.
* Depth lemmas, uniformly in the arbitrary tails: `YG.xd`/`YC.xd`/`YBase.xd` (the `v`-components),
  `TC.xd`, `TW.xd` (generic in the base), `WT.xd`, `WqT.xd`, `SqT.xd`, `ST.xd`, and the mutual
  **`HG.xd`**/`HC.xd`/`HB.xd`: a component `P` of index `i` has `P a b =βη x^{i+1} (a …)` for
  every variable `a` and term `b`.
* **`HG.index_unique`**: `HG x i P → HG x j P → i = j`.

First missing lemma unchanged: `theorem TLCA4.H5Ext.tailCores (x : ℕ) : TailCores (Ext (H5Core x) x) x`.
Remaining steps for its `unique` field: (2) `q`-freeness (every member of `HC`, `TC (YB x) (x+1)`,
`TW (YB x) (x+1)`, `WqT`, `SqT` has variable `0` free; lifted terms do not); (3) separation —
`lamM` is not a component (now immediate from `HG.xd`: `M a b` has depth `0`), a component is
not `W Q` with `W ∈ WT x` (syntactic: `WT` heads are none of `lamB`, `B M`, `bmPre1`, `bmPre2`,
`ByR`), `TW` members over any base are not components (by (2)); (4) a version of
`TC.unique`/`TW.unique` needing only the syntactic fields, by strong induction on `Lambda.nodes`
for the levels of `Ext`.

Also in run 3: `HG.not_lamM` (`M` is not a component: `M a b =βη a a b` has depth `0`, the first
separation fact of step 3), and step 2: `Start/TLCA4Hit5QFree.lean` — `FreeIn k t`,
`not_freeIn_lift` (a lifted term never has its cut-off variable free), and `q`-freeness of every
chain under `q`: `TC.freeIn0`/`TW.freeIn0` (generic in the base), `ByqR.freeIn0`,
`YBase.freeIn0`, `WqT.freeIn0`, `HB.freeIn0`, `SqT.freeIn0`, **`HC.freeIn0`**.  Remaining for
`unique`: step 3 (a component is not `W Q` with `W ∈ WT x`; `TW` members over any base are not
components, using step 2) and step 4 (`TC.unique`/`TW.unique` from the syntactic fields only, by
strong induction on `Lambda.nodes` over the levels of `Ext`).

Step 3, first half: `Start/TLCA4Hit5Sep.lean` — no `w`-reduct is `B`, `B M`, `bmPre1`, `bmPre2`
or a reduct of `B (B x)` (`WT.ne_lamB`, `WT.ne_bm`, `WT.ne_bmPre1`, `WT.ne_bmPre2`,
**`WT.not_byR`**; the `λ`-shaped cases use `q`-freeness and `not_freeIn_lift`), hence
**`WT.not_HG_app`**: no component of `hit5` is `W Q` with `W ∈ WT x` (this separates the cores
`(W Q) Y` from `P Q'` and `M (W Q)` from `M Q'`).  Still open in step 3: `TW` members over the
levels of `Ext` are not components (cores `M W'` and `W' Y` of the extension against `M Q`, `P Q`).

Step 3, second half (same module): `WqT.not_lift` — the constructor `ST.seta` is vacuous (a
`WqT` member has `q` free, a lifted term does not); **`TW.not_HG`** — a two-argument chain over any
base of non-variables (e.g. a level of `Ext`) is not a component of `hit5` (`wB` heads are `B`,
which is no component head; `wP`/`wK` heads would force a chain under `q` to equal a lifted term,
contradicting `HC.freeIn0`).  With these, the cores `P Q`, `M Q`, `M (W Q)`, `(W Q) Y`, `M W'`, `W' Y` overlap only within
the same form, up to one more easy fact: a `TW` member is not `W Q` with `W ∈ WT x` (its `wB`
head would make `W = B`, excluded by `WT.ne_lamB`; the other forms are abstractions).  Remaining: step 4, the assembly of
`H5Ext.tailCores` (fields `ne_var`, `ne_bx`, `ne_bx1`, and `unique` by strong induction on
`Lambda.nodes` over the levels of `Ext`, using `HG.index_unique`, `WT`-uniqueness of `W` in
`W Q`, and a syntactic-fields-only version of `TW.unique`).

`Start/TLCA4Hit5Fields.lean`: the syntactic fields of `TailCores (Ext (H5Core x) x) x` —
**`H5Ext.ne_var`**, **`H5Ext.ne_bx`** (via `HG.not_lamB_app`), **`H5Ext.ne_bx1`** (via
`HG.not_bxPre`: `λab. x (a b)` is not a component) — and `TW.not_WT_app` (the easy fact above).
Five of the six fields are now proved (`step`, `not_lam`, `ne_var`, `ne_bx`, `ne_bx1`); the
first missing lemma is the last field:
`theorem TLCA4.H5Ext.unique {x : ℕ} {K i K' i' : ℤ} {P : Lambda} (h : Ext (H5Core x) x K i P) (h' : Ext (H5Core x) x K' i' P) : K - i = K' - i'`.
Plan: strong induction on `Lambda.nodes P`; same-form cases by `HG.index_unique` (and injectivity
of the `W Q` decomposition), the extension forms by a version of `TW.unique` whose base
uniqueness is only required for strictly smaller terms (`TW.restrict`); cross-form cases by
`HG.not_lamM`, `WT.not_HG_app`, `TW.not_HG`, `TW.not_WT_app`.

## Big round 2, run 3 (A1 closed): `hit5_not_fixedPoint`

`Start/TLCA4Hit5NotFixpoint.lean` proves the last `TailCores` field, `H5Ext.unique`: the syntactic
fields alone (`TailSyn`) make `K − h` a function of a tail chain (`TC.uniqueS`, `TW.uniqueS`);
a core of `Ext (H5Core x) x` is either a core of `H5Core x` (index determined by
`HG.index_unique`) or an extension (`H5Ext.cases`), and the two forms are separated
(`H5Core.not_extM`, `H5Core.not_extWY`); induction on size (`H5Ext.unique_aux`) closes it.
Hence `H5Ext.tailCores` and **`hit5_not_fixedPoint`** (new row M20-TLCA4-HIT5-NOT-FIXPOINT,
DONE_STRONG). Standard axioms only. Next: A2, `hit6_not_fixedPoint`, `hit8_not_fixedPoint`.

## Big round 2, run 5 (A2, A3 closed; A5 theorem): normalized stage components

The grammars for `Q` and `hit5` follow the combinators through every intermediate form.  Run 5
starts instead from a partly normalized reduct: every candidate seen so far has `p x = M (M s)`
with `s` βη-reducing to

    nfStage x T T' = λa w. x (a G_a T),   G_a = λz w'. x (a z T')   (T, T' arbitrary).

`Start/TLCA4NfGrammar.lean`: the grammar `NG x i` (components of index `i`: `λq. C`, `C` a chain
of height `i + 1` under `q`), `NC` (chains with arbitrary tails), `NB` (cores `q G_q`, height 0,
and `R q` with `R` a component of index `i'`, height `i' + 1`); **`NG.step`** — closed under βη.
`Start/TLCA4NfCores.lean`: **`NG.index_unique`** (index determined by the term), `NB.substQ`
(substituting a component of index `j` for `q`: `q G_q ↦ Q G_Q`, a core `P Q` of indices
`(j, j + 1)`; `R q ↦ R Q`), **`NCore.tailCores`** (top-level cores `P Q`, `K + i = tri j + n`,
satisfy `TailCores`; no `Ext` needed), **`not_fixedPoint_of_nf`**: if `L →βη S S ρ` with `S` a
component of index 0, then `¬ L =βη x L`.

`Start/TLCA4Hit6NotFixpoint.lean`: `F a z →βη λbc. x (a z (b c))` (`f6_red`), so
`g a →βη G_a` for `hit6` (`h6g_qG`: `B M (F a) → λz. Ψ Ψ → λz c. x (a z (Ψ c))`) and for `hit8`
(`h8g_qG`: `G_a = λz w. x (a z (w Ψ))`); `sComp_of_qG`: then `B M g` reduces to a component of
index 0.  **`hit6_not_fixedPoint`**, **`hit8_not_fixedPoint`**, and through `hit6_conv_hit7`,
`hit8_conv_hit9`, **`hit7_not_fixedPoint`**, **`hit9_not_fixedPoint`** (row
M20-TLCA4-HIT6-HIT9-NOT-FIXPOINT).  `Start/TLCA4StageIndex.lean`: for any stage pattern, the
components `gⁿ s` are pairwise βη-distinct (`stage_index_unique`; instances for hit5, hit6, hit8,
Q), and `hit6_stage_betaEta`, `hit8_stage_betaEta`.

`Start/TLCA4Hit10NotFixpoint.lean` (A3): `hit10 x = M (M s)`, `s = B²M w` with `w` the `w`-term of
`hit5`; `s →βη λa w. x (a U_a (w (λc. x (a U_a (w c)))))` (`h10s_red`), `U_a = G_a` with tail
`w`; **`hit10_not_fixedPoint`** (row M20-TLCA4-HIT10-NOT-FIXPOINT).  So none of the six length-7
spine hits without a `T` factor is a βη fixed-point combinator.

`Start/TLCA4StageNf.lean` (A5): **`not_fixedPoint_of_MM_nfStage`** — if `L →βη M (M s)` and
`s →βη nfStage x T T'`, then `¬ L =βη x L` (row M20-TLCA4-NFSTAGE); `hit5_not_fixedPoint_nf`
recovers `hit5` from it.  Named conjecture (A5, evidence: Q, hit5–hit10): every polynomial
satisfying `PolyFiveOne` has a step term of this shape; first missing lemma
`theorem TLCA4.polyFiveOne_nfStage {C : List Mono} (h : PolyFiveOne C) (x : ℕ) : ∃ s T T', Lambda.betaEtaReduces (toLam (actList C (Tm.var x))) (.app lamM (.app lamM s)) ∧ Lambda.betaEtaReduces s (nfStage x T T')`.
Together with `statmanStepOne` and `not_fixedPoint_of_MM_nfStage` it would give
`¬ ProblemFiveOne`.

## Big round 2, run 6 (A2, A3, A5 rebuilt after the move to a new project)

The six modules of run 5 above were lost with the old project; run 6 rebuilt them from the design
note above and the fragments of run 5's command log, and they build again with
`lake build --wfail` (standard axioms only; `*-axioms.txt`, section "Big round 2, run 6"):

* `Start/TLCA4NfGrammar.lean`: `qG x T = λz w'. x (q z T)` under `q`; `NG`, `NC`, `NB`; `qG_step`
  (a step of `G_q` happens in its tail); **`NG.step`**, `NG.reduces`, `NG.fire_q`, `NC.eta_inv`.
  The definition `nfStage` and **`nfStage_NG`** now live here (run 5 had them in
  `Start/TLCA4StageNf.lean`), so that `sComp_of_qG` can name the component it produces.
* `Start/TLCA4NfCores.lean`: **`NG.index_unique`** (with `NC.height_unique`, `NB.height_unique`),
  `NC.toTC`, `qG_subst`, `NB.substQ`, **`NCore.step`**, **`NCore.tailCores`**,
  **`not_fixedPoint_of_nf`** — as in run 5.
* `Start/TLCA4Hit6NotFixpoint.lean`: `sComp_of_qG` (if `g a →βη G_a` then `B M g →βη
  nfStage x T₁ T`, explicitly), `bmF_qG`, `h6g_qG`, `h8g_qG`, **`hit6_not_fixedPoint`** …
  **`hit9_not_fixedPoint`**.
* `Start/TLCA4Hit10NotFixpoint.lean`: as in run 5 (**`hit10_not_fixedPoint`**).
* `Start/TLCA4StageNf.lean`: **`not_fixedPoint_of_MM_nfStage`**, `hit5_not_fixedPoint_nf`.
* `Start/TLCA4StageIndex.lean`: `toLam_iterX`, `iterT_stage_app` (`gⁿ s Z W →w x^{n+1} (Z (g Z) W')`),
  **`stage_index_unique`** through the βη-invariant `x`-depth (`XDepth.unique`), instances
  `hit5_comp_index_unique`, `hit6_comp_index_unique`, `hit8_comp_index_unique`.  Run 5's
  `hit6_stage_betaEta`, `hit8_stage_betaEta` (the stages restated under βη) were not rebuilt.

A5 is unchanged: first missing lemma `theorem TLCA4.polyFiveOne_nfStage {C : List Mono}
(h : PolyFiveOne C) (x : ℕ) : ∃ s T T', Lambda.betaEtaReduces (toLam (actList C (Tm.var x)))
(.app lamM (.app lamM s)) ∧ Lambda.betaEtaReduces s (nfStage x T T')`.  The A4 searches of run 5
(lengths 8 and 9) were never recorded and are lost; they are the first step of A5 (plan 0.8).

## Big round 2, run 7 (A4 rerun; A5 step 2, the nfStage test) — Python only, not Lean-checked

Scripts (rewritten in run 7, big round 1's are lost): `wip/a1_spine.py` (x-spine depth by head
reduction of `p x`, cap 10, 300 head steps per level), `wip/a3_adm.py` (`TLCA4.Adm` of
`Start/TLCA4Automaton.lean`), `wip/b2/a4_search.py` (after run 5's `a4_len8.py`; Adm filter; cap hits
rechecked with 10x fuel), `wip/b2/a5_nfstage.py`, `wip/b2/a5_hits.py`.

**Check against big round 1.** Lengths 1–7 reproduce the table of Series V, round 4, run 2 exactly
(histograms {1:1}, {0:8}, {0:62,1:1,10:1}, {0:512}, {0:4080,1:11,2:3,4:1,10:1}; length 7 restricted to
Adm: 49,248 polynomials, {0:48976, 1:208, 2:44, 4:8, 10:12}, the same 12 hits), and the Adm tail counts
0, 12, 80, 736, 5952 (then 49,248, 398,720, 3,233,920 for tails of length 6, 7, 8). Every polynomial with
depth > 0 at length ≤ 7 is admissible.

**A4, length 8** (monomials `BⁿB`, `BⁿM`, `n ≤ 3`, `m₁ = M`): 2,097,152 polynomials, 398,720 pass Adm,
all of x-spine depth 0; no hit, no fuel-limited run. (Even lengths again have no depth > 0.)

**A4, length 9, partial**: 16,777,216 polynomials, 3,233,920 pass Adm; the run was stopped by its
`timeout 2400` after 2,560,000 of them (≈79%, in `itertools.product` order of the tail, so the last
part of the enumeration — tails beginning with the late monomials — is not covered). 88 cap hits,
all again at the cap with 10x fuel; all have second monomial `M`. Classes: 40 contain the factor
`T = M∘BM∘B` contiguously, 48 do not.

**A5 step 2, the nfStage test.** For each hit: search a weak reduct `M (M s)` of `p x` (combinatory
weak reduction, ≤ 200 steps: reduce the argument of the top `M` by weak head steps, fire the top `M`
when it is stuck), then test `s →βη nfStage x T T' = λc e. x (c (λz w. x (c z T')) T)` by head normal
forms (2000 head steps each; η only for variables). Results:

* length ≤ 7, 14 hits: 9 pass (Q, hit3, hit4, hit5–hit10); 5 exceptions:
  - second monomial `BM`, no weak reduct `M (M s)` found: `T = M∘BM∘B`, `M∘BM∘B∘M∘BM∘B∘B` (= `T∘T∘B`, hit11),
    `M∘BM∘M∘BM∘B∘B∘B` (hit12);
  - `x`-prefixed stage (`s →β λc e. x R` with `R` headed by `x`, not by `c`): `M∘M∘B∘M∘BM∘B∘B` (hit1),
    `M∘M∘M∘BM∘B∘B∘B` (hit2 = Q₂).
* length 8: no hits, nothing to test.
* length 9 (partial): 88 hits, 26 pass, 62 exceptions: 59 `x`-prefixed stages (third monomial `M`: 42,
  `B`: 12, `BM`: 5) and 3 where the inner component's first argument is not `z` (third monomial `BM`).

So the conjecture fails as stated: the class without exceptions in the data is not simply
"second monomial `M`". Exceptional classes: (i) second monomial `BM` (all with a factor `T`; `T`,
`T∘T∘B`, hit12); (ii) the `x`-prefixed stages `λc e. xᵏ (c Q T)`, `k ≥ 2`, which contain `Q₂` and all
polynomials `M∘M∘M∘…` tested. Next step (A5 step 4): generalize `nfStage` to an `x`-prefix
`nfStageK x k T T' = λc e. xᵏ⁺¹ (c (qG x T') T)` (test it in Python first), and prove the restricted
`polyFiveOne_nfStage` for the class that passes. Every exception, with the test's reason:

```

('M∘M∘B∘M∘B∘M∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘M∘BM∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘BB∘BM∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘B²M∘B∘BB∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘B²M∘B²B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘B²M∘BB∘BM∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘BM∘B∘M∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘BM∘M∘BM∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘B∘BM∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘B∘B²M∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘B³M∘B∘BB∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘B∘M∘BM∘B³M∘B²B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘B∘B∘M∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘B∘M∘BM∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BB∘B∘M∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BB∘M∘BM∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BB∘BM∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BB∘B²M∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘M∘BM∘B∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B²M∘B∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘BM∘B∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘BM∘BB∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘BM∘B²B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘BB∘B∘BM∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B∘BM∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B∘B²M∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘BB∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘BB∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘BB∘B²M∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²B∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²B∘B²M∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B²M∘BB∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B²M∘B²B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²M∘B∘B∘BB∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²M∘B∘BB∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²M∘B∘B²B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²M∘B²B∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²M∘B³B∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²B∘B∘B∘BM∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²B∘B∘BM∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²B∘B∘B²M∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B³M∘B³B∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B²B∘B³M∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘B²M∘BB∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘B²M∘B²B∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘B³M∘BB∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘B³M∘B²B∘BM∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B³M∘B∘B∘BB∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B³M∘B∘BB∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B³M∘B∘B²B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B³M∘B²B∘B∘B∘B', 'no-T/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B³M∘B∘BB∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B³M∘BB∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘M∘BM∘B∘B³M∘B²B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘BM∘B∘B∘M∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘BM∘B∘M∘BM∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘BM∘BB∘B∘M∘BM∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘BM∘BB∘M∘BM∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘BM∘M∘BM∘B∘B∘B∘B', 'T-factor/MM', "body: 0 λ, head ('x',), 1 args")
('M∘M∘BM∘BM∘B²M∘BB∘B∘BB∘B', 'no-T/MM', 'Q: first argument of c is not z')
('M∘M∘BM∘BM∘B²M∘BB∘B²B∘B∘B', 'no-T/MM', 'Q: first argument of c is not z')
('M∘M∘BM∘BM∘B²M∘B³B∘BB∘B∘B', 'no-T/MM', 'Q: first argument of c is not z')
```
