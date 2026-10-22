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
