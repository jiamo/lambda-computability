/-
**The index set of the total functions, and its exact place in the hierarchy.**

`Start/ArithComplete.lean` makes completeness available at every level of the arithmetical
hierarchy but exhibits a concrete complete predicate only at level one, where it is the halting
problem.  This module does the same job at level two, with the classical example: the set of
indices `e` such that the `e`-th partial recursive function is total.

* `Lambda.Arith.Tot` — the index set of the total functions, `∀ x, x ∈ W e`.
* `Lambda.Arith.piAt_two_tot` — it is `Π⁰₂`: "for every argument there is a halting stage".
* `Lambda.Arith.piAt_two_le_one_tot` — it is **hard** for `Π⁰₂` already under *one-one*
  reducibility.  Given `P x ↔ ∀ y, Q (⟨x, y⟩)` with `Q` recursively enumerable, take a partial
  recursive `f` whose domain is `Q` and a code `c` for it; the s-m-n theorem turns `c` into the
  index `⌜curry c x⌝`, whose function is total exactly when every `⟨x, y⟩` lies in the domain of
  `f`, that is, exactly when `P x`.
* `Lambda.Arith.tot_piComplete` — hence **totality is `Π⁰₂`-complete**, and its complement is
  `Σ⁰₂`-complete (`Lambda.Arith.notTot_sigmaComplete`).
* The consequences: totality is not `Σ⁰₂`, not `Δ⁰₂`, neither recursively enumerable nor
  co-recursively-enumerable, and not computable.
* `Lambda.Arith.haltK_le_tot`, `Lambda.Arith.not_manyOne_tot_haltK` — the halting problem reduces
  to totality but not conversely, so totality is strictly harder.

One level down, the same s-m-n construction places the emptiness of the `e`-th r.e. set exactly at
the bottom of the `Π` side:

* `Lambda.Arith.Emp` — the index set of the nowhere-defined functions;
* `Lambda.Arith.emp_piComplete` — it is `Π⁰₁`-complete, so it is co-recursively-enumerable but
  not recursively enumerable, and its complement — "the `e`-th function is defined somewhere" —
  is `Σ⁰₁`-complete.
-/

import Start.ArithComplete
import Start.KleeneK

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Arith

open Encodable Denumerable
open Nat.Partrec (Code)

/-! ## The index set -/

/-- `Tot e`: the `e`-th partial recursive function is total, i.e. every number lies in the `e`-th
recursively enumerable set. -/
def Tot (e : ℕ) : Prop := ∀ x, Post.Wset e x

theorem tot_iff_forall_dom (e : ℕ) :
    Tot e ↔ ∀ x, (Code.eval (ofNat Code e) x).Dom := Iff.rfl

/-! ## Totality is `Π⁰₂` -/

/-- **Totality is `Π⁰₂`.**  Membership in the `e`-th r.e. set is a universal `Σ⁰₁` predicate of the
pair `⟨e, x⟩`, and a universal quantifier over `x` in front of a `Σ⁰₁` matrix is exactly `Π⁰₂`. -/
theorem piAt_two_tot : PiAt 2 Tot := by
  have h2 : PiAt 2 univOne := PiAt.of_sigmaAt univSigma_one.1
  refine h2.forall.of_iff fun e => forall_congr' fun x => ?_
  simp [univOne]

/-! ## Totality is `Π⁰₂`-hard -/

/-- **Totality is hard for `Π⁰₂` under one-one reducibility.**  The reduction is the s-m-n
function `x ↦ ⌜curry c x⌝` for a code `c` of a partial recursive function whose domain is the
`Σ⁰₁` matrix. -/
theorem piAt_two_le_one_tot {P : ℕ → Prop} (hP : PiAt 2 P) : P ≤₁ Tot := by
  obtain ⟨Q, hQ, hPQ⟩ := piAt_succ_iff.1 hP
  obtain ⟨f, hf, hdom⟩ := exists_partrec_dom_iff (sigmaAt_one_iff.1 hQ)
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hf)
  refine ⟨fun a => Encodable.encode (Code.curry c a), Computable.encode.comp
    (Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.id), ?_, ?_⟩
  · intro a b hab
    exact (Code.curry_inj (Encodable.encode_injective hab)).2
  · intro a
    rw [hPQ a]
    refine forall_congr' fun x => ?_
    have hval : Code.eval (ofNat Code (Encodable.encode (Code.curry c a))) x
        = f (Nat.pair a x) := by
      rw [Denumerable.ofNat_encode, Code.eval_curry, hc]
    exact (hdom (Nat.pair a x)).symm.trans (by rw [Post.Wset, hval])

/-- **Totality is `Π⁰₂`-complete.** -/
theorem tot_piComplete : PiComplete 2 Tot :=
  ⟨piAt_two_tot, fun _ hQ => (piAt_two_le_one_tot hQ).to_many_one⟩

/-- The complement of the index set of total functions is `Σ⁰₂`-complete. -/
theorem notTot_sigmaComplete : SigmaComplete 2 fun e => ¬ Tot e :=
  tot_piComplete.compl

/-! ## Where totality is not -/

/-- Totality is not `Σ⁰₂`. -/
theorem not_sigmaAt_two_tot : ¬ SigmaAt 2 Tot := tot_piComplete.not_sigmaAt

/-- Totality is not `Δ⁰₂`, so it is not decidable even from the halting oracle. -/
theorem not_deltaAt_two_tot : ¬ DeltaAt 2 Tot := tot_piComplete.not_deltaAt

/-- Totality is not `Π⁰₁`, that is, not co-recursively-enumerable. -/
theorem not_piAt_one_tot : ¬ PiAt 1 Tot := tot_piComplete.not_piAt_lower

/-- Totality is not `Σ⁰₁`, that is, not recursively enumerable. -/
theorem not_sigmaAt_one_tot : ¬ SigmaAt 1 Tot := fun h => not_sigmaAt_two_tot h.succ

theorem not_rePred_tot : ¬ REPred Tot := fun h => not_sigmaAt_one_tot (sigmaAt_one_iff.2 h)

theorem not_rePred_compl_tot : ¬ REPred fun e => ¬ Tot e := fun h =>
  not_piAt_one_tot (piAt_one_iff.2 h)

/-- Totality is undecidable. -/
theorem not_computablePred_tot : ¬ ComputablePred Tot := tot_piComplete.not_computablePred

/-! ## Totality is strictly harder than halting -/

/-- The halting problem many-one reduces to totality, because it is `Σ⁰₁` and hence `Π⁰₂`. -/
theorem haltK_le_tot : HaltK ≤₀ Tot :=
  tot_piComplete.2 HaltK (PiAt.of_sigmaAt (sigmaAt_one_iff.2 rePred_haltK))

/-- **Totality does not reduce to the halting problem**: it is strictly harder.  A reduction would
make totality recursively enumerable, since every level is closed downwards under many-one
reducibility. -/
theorem not_manyOne_tot_haltK : ¬ Tot ≤₀ HaltK := fun h =>
  not_sigmaAt_one_tot ((sigmaAt_one_iff.2 rePred_haltK).of_manyOne h)

/-! ## One level down: the empty index set -/

/-- `Emp e`: the `e`-th recursively enumerable set is empty, i.e. the `e`-th partial recursive
function is nowhere defined. -/
def Emp (e : ℕ) : Prop := ∀ x, ¬ Post.Wset e x

/-- "The `e`-th function is defined somewhere" is `Σ⁰₁`. -/
theorem sigmaAt_one_exists_wset : SigmaAt 1 fun e => ∃ x, Post.Wset e x := by
  refine (SigmaAt.exists univSigma_one.1).of_iff fun e => exists_congr fun x => ?_
  simp [univOne]

/-- **Emptiness is `Π⁰₁`.** -/
theorem piAt_one_emp : PiAt 1 Emp := by
  classical
  exact piAt_iff_sigmaAt_not.2 (sigmaAt_one_exists_wset.of_iff fun e => by
    simp [Emp, not_forall])

/-- **Emptiness is hard for `Π⁰₁` under one-one reducibility.**  For a code `c` of a partial
recursive function that ignores its second argument, the `e`-th set of the index `⌜curry c a⌝` is
empty exactly when the first argument `a` is outside the domain. -/
theorem piAt_one_le_one_emp {P : ℕ → Prop} (hP : PiAt 1 P) : P ≤₁ Emp := by
  classical
  obtain ⟨f, hf, hdom⟩ := exists_partrec_dom_iff (piAt_one_iff.1 hP)
  have hF : Partrec fun w : ℕ => f w.unpair.1 :=
    hf.comp (Primrec.fst.comp Primrec.unpair).to_comp
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hF)
  refine ⟨fun a => Encodable.encode (Code.curry c a), Computable.encode.comp
    (Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.id), ?_, ?_⟩
  · intro a b hab
    exact (Code.curry_inj (Encodable.encode_injective hab)).2
  · intro a
    have hval : ∀ x : ℕ,
        Code.eval (ofNat Code (Encodable.encode (Code.curry c a))) x = f a := by
      intro x
      rw [Denumerable.ofNat_encode, Code.eval_curry, hc]
      simp
    constructor
    · intro hPa x hx
      exact (hdom a).1 (by rw [← hval x]; exact hx) hPa
    · intro hEmp
      by_contra hPa
      exact hEmp 0 (by rw [Post.Wset, hval 0]; exact (hdom a).2 hPa)

/-- **Emptiness of the `e`-th recursively enumerable set is `Π⁰₁`-complete.** -/
theorem emp_piComplete : PiComplete 1 Emp :=
  ⟨piAt_one_emp, fun _ hQ => (piAt_one_le_one_emp hQ).to_many_one⟩

/-- "The `e`-th function is defined somewhere" is `Σ⁰₁`-complete. -/
theorem notEmp_sigmaComplete : SigmaComplete 1 fun e => ¬ Emp e :=
  emp_piComplete.compl

/-- Emptiness is not recursively enumerable. -/
theorem not_sigmaAt_one_emp : ¬ SigmaAt 1 Emp := emp_piComplete.not_sigmaAt

theorem not_rePred_emp : ¬ REPred Emp := fun h => not_sigmaAt_one_emp (sigmaAt_one_iff.2 h)

/-- Emptiness is undecidable. -/
theorem not_computablePred_emp : ¬ ComputablePred Emp := emp_piComplete.not_computablePred

end Arith
end Lambda
