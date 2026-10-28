/-
**Bridge: counter machines and F<: over the λ-calculus** — milestone M31 (`M31-BRIDGE-MINSKY`).

The undecidability results of `Start/MinskyUndecidable.lean` and `Start/FsubComputable.lean`
are stated with Mathlib's `ComputablePred`.  Through `lambdaDecidable_iff_computablePred`
(`Start/BridgeComputability.lean`) they become statements about the λ-calculus.

* `ComputablePred.of_lambdaDecidable_encode` — a predicate on a `Primcodable` type whose coded
  version is λ-decidable is computable;
* `Minsky.Universal.cm_halts_not_lambdaDecidable` — **the halting problem of the fixed counter
  machine `M_u` is not λ-decidable** (on paired inputs);
* `FsubCode.sub_not_lambdaDecidable` — **subtyping in full F<: is not λ-decidable** (on the codes
  of goals).
-/

import Start.BridgeComputability
import Start.FsubComputable

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Encodable

/-- A predicate whose coded version is λ-decidable is computable. -/
theorem ComputablePred.of_lambdaDecidable_encode {α : Type} [Primcodable α] {p : α → Prop}
    {q : ℕ → Prop} (hq : LambdaDecidable q) (h : ∀ a, p a ↔ q (encode a)) : ComputablePred p := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp (lambdaDecidable_iff_computablePred.mp hq)
  refine ComputablePred.computable_iff.mpr ⟨fun a => f (encode a), hf.comp Computable.encode, ?_⟩
  funext a
  exact propext (h a)

/-- **The halting problem of the counter machine `M_u` is not λ-decidable.** -/
theorem Minsky.Universal.cm_halts_not_lambdaDecidable :
    ¬ LambdaDecidable (fun n => FsubGhelli.CM.Halts M_u n.unpair.1 n.unpair.2) := by
  intro h
  refine cm_halts_undecidable (ComputablePred.of_lambdaDecidable_encode h fun ab => ?_)
  show _ ↔ FsubGhelli.CM.Halts M_u (Nat.pair ab.1 ab.2).unpair.1 (Nat.pair ab.1 ab.2).unpair.2
  rw [Nat.unpair_pair]

/-- **Subtyping in full F<: is not λ-decidable** (on the codes of goals). -/
theorem FsubCode.sub_not_lambdaDecidable :
    ¬ LambdaDecidable (fun n => ∃ g : FsubGhelli.Goal, encode g = n ∧ FsubGhelli.Sub g) := by
  intro h
  refine sub_not_computable (ComputablePred.of_lambdaDecidable_encode h fun g => ?_)
  constructor
  · intro hs
    exact ⟨g, rfl, hs⟩
  · rintro ⟨g', e, hs⟩
    rwa [← encode_injective e]
