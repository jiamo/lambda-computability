/-
Kleene's diagonal halting set `K`, and its equivalence with the lambda-calculus halting set.

`Start/HaltingComplete.lean` shows that the lambda halting set is Σ₁-complete, indeed one-one
complete.  This file does the same for the *standard* halting problem — the diagonal set
`K = {n | the n-th partial recursive code halts on input n}` of mathlib's `Nat.Partrec.Code` —
and then deduces that the two sets are one-one equivalent.  So the halting problem of the lambda
calculus and the halting problem of the classical model are the same problem, not merely two
undecidable problems.

* `Lambda.HaltK` — the diagonal halting set as a predicate on `ℕ`;
* `Lambda.rePred_haltK` — it is r.e.;
* `Lambda.rePred_le_one_haltK` — every r.e. predicate reduces to it injectively (via the s-m-n
  theorem, in the form of `Nat.Partrec.Code.curry`);
* `Lambda.haltK_one_complete` — hence `K` is one-one complete;
* `Lambda.oneOneEquiv_haltK_codeHasNormalForm`, `Lambda.oneOneEquiv_haltK_codeConverges` — the
  bridge: `K`, "this lambda code has a normal form", and "this lambda code converges to a Church
  numeral" are pairwise one-one equivalent.
-/

import Start.HaltingComplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

open Nat.Partrec (Code)
open Encodable Denumerable

/-- **Kleene's diagonal halting set**: the `n`-th partial recursive code, run on the input `n`,
halts. -/
def HaltK (n : ℕ) : Prop := (Code.eval (ofNat Code n) n).Dom

/-- `K` is recursively enumerable. -/
theorem rePred_haltK : REPred HaltK := by
  have h : Partrec fun n : ℕ => Code.eval (ofNat Code n) n :=
    Code.eval_part.comp (Computable.ofNat Code) Computable.id
  exact h.dom_re

/-- From an r.e. predicate on `ℕ`, a partial recursive function whose domain it is. -/
theorem exists_partrec_dom_iff {p : ℕ → Prop} (hp : REPred p) :
    ∃ f : ℕ →. ℕ, Partrec f ∧ ∀ a, (f a).Dom ↔ p a := by
  refine ⟨fun a => (Part.assert (p a) fun _ => Part.some ()).map fun _ => 0,
    hp.map (Computable.const (0 : ℕ)).to₂, fun a => ?_⟩
  simp [Part.dom_iff_mem]

/-- **One-one hardness of `K`.**  Every r.e. predicate reduces to the diagonal halting set by an
injective computable function; the reduction is built with the s-m-n theorem. -/
theorem rePred_le_one_haltK {p : ℕ → Prop} (hp : REPred p) : p ≤₁ HaltK := by
  obtain ⟨f, hf, hdom⟩ := exists_partrec_dom_iff hp
  have hF : Partrec fun n : ℕ => f n.unpair.1 :=
    hf.comp (Primrec.fst.comp Primrec.unpair).to_comp
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hF)
  refine ⟨fun a => Encodable.encode (Code.curry c a), Computable.encode.comp
    (Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.id), ?_, ?_⟩
  · intro a b hab
    exact (Code.curry_inj (Encodable.encode_injective hab)).2
  · intro a
    have hval : Code.eval (Code.curry c a) (Encodable.encode (Code.curry c a)) = f a := by
      rw [Code.eval_curry, hc]
      simp
    rw [HaltK, Denumerable.ofNat_encode, hval]
    exact (hdom a).symm

/-- Σ₁-hardness of `K`. -/
theorem rePred_le_haltK {p : ℕ → Prop} (hp : REPred p) : p ≤₀ HaltK :=
  (rePred_le_one_haltK hp).to_many_one

/-- **`K` is one-one complete**: it is r.e., and every r.e. predicate reduces to it injectively. -/
theorem haltK_one_complete : REPred HaltK ∧ ∀ p : ℕ → Prop, REPred p → p ≤₁ HaltK :=
  ⟨rePred_haltK, fun _ hp => rePred_le_one_haltK hp⟩

/-- **`K` is Σ₁-complete.** -/
theorem haltK_sigma1_complete : REPred HaltK ∧ ∀ p : ℕ → Prop, REPred p → p ≤₀ HaltK :=
  ⟨rePred_haltK, fun _ hp => rePred_le_haltK hp⟩

/-- **The bridge.**  Kleene's halting problem and the lambda-calculus halting problem are one-one
equivalent. -/
theorem oneOneEquiv_haltK_codeHasNormalForm : OneOneEquiv HaltK CodeHasNormalForm :=
  ⟨rePred_le_one_codeHasNormalForm rePred_haltK, rePred_le_one_haltK rePred_codeHasNormalForm⟩

/-- Kleene's halting problem and convergence of a lambda code to a Church numeral are one-one
equivalent. -/
theorem oneOneEquiv_haltK_codeConverges : OneOneEquiv HaltK CodeConverges :=
  ⟨rePred_le_one_codeConverges rePred_haltK, rePred_le_one_haltK rePred_codeConverges⟩

/-- The many-one form of the bridge. -/
theorem manyOneEquiv_haltK_codeHasNormalForm : ManyOneEquiv HaltK CodeHasNormalForm :=
  oneOneEquiv_haltK_codeHasNormalForm.to_many_one

/-- `K` is not co-r.e. -/
theorem not_rePred_not_haltK : ¬ REPred fun n => ¬ HaltK n := by
  intro h
  have hcomp : ComputablePred HaltK :=
    ComputablePred.computable_iff_re_compl_re'.2 ⟨rePred_haltK, h⟩
  exact not_computablePred_codeHasNormalForm
    (ComputablePred.computable_of_manyOneReducible
      (rePred_le_haltK rePred_codeHasNormalForm) hcomp)

end Lambda
