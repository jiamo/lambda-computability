# M7-SYSTEM-T

**Status:** DONE_STRONG

Modules `Start/SystemTSyntax.lean`, `Start/SystemT.lean` and `Start/SystemTCanon.lean`, all
imported by `Start.lean`.  This is Gödel's System T: the simply typed lambda calculus extended
with the natural numbers and a primitive recursor, which is the standard proof-theoretic
companion of the untyped computability development.

## Definitions

* `GodelT.Tm` — de Bruijn terms with `zero`, `succ` and `natrec` as genuine constructors, plus
  `GodelT.lift` and `GodelT.subst` and the full suite of substitution lemmas
  (`lift_lift`, `lift_subst`, `subst_lift`, `subst_subst`, `subst_subst_zero`, …).
* `GodelT.Ty`, `GodelT.Typing` — the types `nat` and `A → B`, and the typing relation.
* `GodelT.step` — β-reduction together with the two ι-rules `natrec z f 0 ↝ z` and
  `natrec z f (succ n) ↝ f n (natrec z f n)`, closed under all congruences.
* `GodelT.SN`, `GodelT.Neutral`, `GodelT.RedNat`, `GodelT.Red` — Tait's reducibility machinery.
  The candidate at type `nat` is the inductively generated family `RedNat`, which is what makes
  the recursor case go through.
* `GodelT.num`, `GodelT.addTm` — the numerals and a term for addition.

## Theorems

* `GodelT.red_natrec` — the recursor is reducible; this is the case that distinguishes System T
  from the simply typed calculus.
* `GodelT.red_substEnv` — the fundamental lemma.
* `GodelT.sn_of_typing` — **strong normalization for System T**.
* `GodelT.hasNormalForm_of_typing` — every typable term has a normal form.
* `GodelT.typing_weaken`, `GodelT.typing_weaken_list`, `GodelT.typing_subst`,
  `GodelT.typing_subst_zero` — weakening and substitution for the typing relation.
* `GodelT.typing_step`, `GodelT.typing_reduces` — **subject reduction**: reduction preserves
  types.
* `GodelT.eq_num_of_closed_normal`, `GodelT.eq_lam_of_closed_normal` — closed normal forms are
  canonical: a numeral at type `nat`, an abstraction at a function type.
* `GodelT.exists_reduces_num` — **canonicity**: every closed term of type `nat` reduces to a
  numeral; and `GodelT.exists_reduces_num_app`, so every closed term of type `nat → nat`
  computes a total function on numerals.
* `GodelT.reduces_addTm : reduces (addTm ⌜m⌝ ⌜n⌝) ⌜m + n⌝` — non-vacuity: the reduction relation
  really computes, and `addTm` represents addition.

Gates: `lake build` succeeds; no `sorry`; `#print axioms` on `GodelT.sn_of_typing` and
`GodelT.exists_reduces_num` reports only `propext, Classical.choice, Quot.sound`.

## Boundary

The characterization of the System T definable functions as exactly the provably total functions
of Peano arithmetic is **not** formalized: that needs a formalization of PA and of its
proof-theoretic ordinal, which this development does not have.
