import Start.RigiditySigmaCollection

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/Syntax/SigmaTransitiveWitness.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace SigmaFormula

theorem transitive_upward (φ : SigmaFormula) {d D : ZFSet.{u}} (hd : Transitive d) (hD : Transitive D)
    (hsub : d ⊆ D) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ d) :
    φ.Realize d e → φ.Realize D e := by
  induction φ generalizing e with
  | bounded φ =>
    intro h
    exact (φ.absolute D hD e (fun i => hsub (he i))).mpr ((φ.absolute d hd e he).mp h)
  | existsSet φ ih =>
    rintro ⟨x,hx,hφ⟩
    exact ⟨x,hsub hx,ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx]) hφ⟩

theorem internal_transitive_witness (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) {t : ZFSet.{u}} (ht : t ∈ M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ t) (φ : SigmaFormula) (hφ : φ.Realize M e) :
    ∃ d ∈ M, Transitive d ∧ t ⊆ d ∧ φ.Realize d e := by
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix M e).mp hφ
  have hω := omega_mem M hM hS hI
  have h0 := hM _ hω _ ZFSet.omega_zero
  let s := t ∪ FiniteTuple.elements xs
  have hs : s ∈ M := binary_union_mem M hM hP hU ht (FiniteTuple.elements_mem M hM hP hU h0 xs hxs)
  obtain ⟨d,hdM,hd,hsd⟩ := internal_transitive_container M hM hP hU hS hR hI hs
  have hsD : s ⊆ d := fun y hy => hd s hsd y hy
  have htD : t ⊆ d := fun y hy => hsD (ZFSet.mem_union.mpr (Or.inl hy))
  have hxsD : ∀ y ∈ xs, y ∈ d := fun y hy =>
    hsD (ZFSet.mem_union.mpr (Or.inr ((FiniteTuple.mem_elements y xs).mpr hy)))
  have heM := fun i => hM t ht _ (he i)
  have heD := fun i => htD (he i)
  refine ⟨d,hdM,hd,htD,(φ.realize_iff_prefix d e).mpr ⟨xs,hlen,hxsD,?_⟩⟩
  exact (φ.matrix.absolute d hd _ (feed_mem xs e d hxsD heD)).mpr
    ((φ.matrix.absolute M hM _ (feed_mem xs e M hxs heM)).mp hmat)
end SigmaFormula

end TuringRigidity.BoundedSetTheory

