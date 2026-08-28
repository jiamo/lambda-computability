# M9-COMPLEXITY-CLASSES

**Status:** DONE_STRONG

Module `Start/ComplexityClasses.lean`, imported by `Start.lean`.  It builds without `sorry` and
without linter warnings.

The module introduces the basic apparatus of complexity theory over binary words (`List Bool`):
the polynomial-time functions, the classes `P` and `NP`, polynomial-time many-one reductions and
NP-completeness, together with the structural theorems that relate them.

## Polynomial-time functions (first exit criterion)

Polynomial time for *functions* is defined à la **Cobham (1965)**, as a syntactic class `Cob`
with semantics `Cob.eval : Cob → List Word → Word`:

* base functions: the empty word, the projections `proj i`, the successors `x ↦ b :: x`, and the
  smash function `x # y = 1^{|x|·|y|}`;
* closure under composition (`comp`) and under **bounded recursion on notation** (`bRec`), where
  the value at each step is truncated to the length of a previously defined bounding function.

Defining the class syntactically is what makes closure under composition a *constructor* rather
than a theorem, which is exactly what the results below need.

`Cob.polyLen` proves the basic size property: for every `c : Cob` there are `a, k` with
`|c.eval args| ≤ a · (maxLen args + 1)^k`.  The proof is by strong induction on the size of the
syntax tree; the `comp` case uses the arithmetic lemma `bound_comp_le` (substituting a
polynomially bounded quantity into a polynomial bound stays polynomial), and the `bRec` case is
immediate from the truncation, which is precisely the point of *bounded* recursion.

Small gadgets `Cob.trueC`, `Cob.notC`, `Cob.andC`, `Cob.orC` implement the Boolean connectives on
the convention "accept = nonempty output", and `Cob.tailC`, `Cob.headTrue` read a word's first
bit.  `Cob.eval_concat` shows that concatenation `x ++ y` is definable in the class, by bounded
recursion on notation with the bound `1^{(|x|+1)(|y|+1)}` built from the smash function — a
nontrivial check that the class is usable and not just formally defined.

## The classes (second and third exit criteria)

* `InP L` — some `c : Cob` decides `L`: `L x ↔ c.eval [x] ≠ []`.
* `InNP L` — some verifier `v : Cob` and polynomially bounded, monotone `p` satisfy
  `v.eval [x, w] ≠ [] → |w| ≤ p |x|` and `L x ↔ ∃ w, v.eval [x, w] ≠ []`.  The first clause (the
  verifier itself rejects overlong witnesses) is the standard normalization that makes the class
  robust; without it `NP` would not be closed under reductions.
* `L₁ ≤ₘᵖ L₂` (`PolyManyOne`) — some `r : Cob` with `L₁ x ↔ L₂ (r.eval [x])`.
* `NPHard`, `NPComplete`, and `PeqNP` (`∀ L, InNP L → InP L`).

## Structural results (fourth exit criterion)

* `inNP_of_inP` — **`P ⊆ NP`**; the verifier is `andC (decider x) (notC w)`, which accepts only
  the empty witness, so the witness bound is the constant `0`.
* `polyManyOne_refl`, `polyManyOne_trans` — `≤ₘᵖ` is a preorder.
* `InP.of_reduction`, `InNP.of_reduction` — `P` and `NP` are closed downwards under `≤ₘᵖ`.  The
  `NP` case is where `Cob.polyLen` is used: the new witness bound is `p ∘ q` where `q` bounds the
  length of the reduction's output, and `PolyBound.comp` keeps it polynomial.
* `NPHard.of_reduction` — NP-hardness moves along reductions.
* `peqNP_of_npComplete_of_inP` and `inP_of_peqNP` — an NP-complete language is in `P` exactly when
  `P = NP`.
* `InP.compl`, `InP.inter`, `InP.union` — `P` is a Boolean algebra of languages.
* `InNP.union` — `NP` is closed under union; the witness carries a tag bit selecting which of the
  two verifiers to run.  (Closure of `NP` under intersection would need a polynomial-time pairing
  of witnesses and is not formalized; closure under complement is of course not expected.)
* `bruteForce_decides` — an `NP` language is decided by the explicit exhaustive search
  `bruteForce v p` over all words of length at most `p |x|` (`wordsUpTo`, `wordsOfLen`).
* Non-vacuity: `inP_univ`, `inP_empty`, `inP_nonempty`.

## Boundary

* Cook–Levin is **not** part of this module: it is `M9-COOK-LEVIN`, and it is proved there
  (`Complexity.npHard_SAT`, `Complexity.npComplete_SAT` in `Start/CookLevinNPHard.lean`), so
  `NPHard` *is* inhabited and `Complexity.peqNP_iff_inP_SAT` holds.  What this module contributes
  is the structural theory that proof plugs into; on its own it proves no language NP-complete,
  and `PeqNP` is of course neither proved nor refuted anywhere here.
* **Cobham's theorem is not formalized**: `Cob` is *defined* by the Cobham axioms, and its
  coincidence with polynomial-time Turing machine computability is not proved.  Nothing in the
  module depends on that coincidence.
* No connection is made to `Mathlib`'s `Computable`/`Partrec`, nor to `Start/TM2PolyTime.lean`'s
  machine-level polynomial-time predicate.
* Statements of the shape "languages in `P` are decidable" are deliberately avoided: in Lean
  `Nonempty (DecidablePred L)` holds classically for every `L`, so such a statement would carry no
  content.  `bruteForce` is given as an explicit function instead.
