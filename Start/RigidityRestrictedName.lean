import Start.RigidityNameUnionCode

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/SetModels/RestrictedName.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.RecursiveNames
open Set CountableForcing
universe u
variable {P : Type u} [Preorder P]

abbrev Name.Entry (a : Name P) := Σ i : a.arity, {q : P // q ≤ a.tag i}

noncomputable def Name.entryCode (l : P → ZFSet.{u}) (a : Name P) (s : a.Entry) : ZFSet.{u} :=
  ZFSet.pair ((a.child s.1).encode l) (l s.2.val)

noncomputable def Name.support (l : P → ZFSet.{u}) (a : Name P) : ZFSet.{u} :=
  ZFSet.range (a.entryCode l)

noncomputable def Name.restrict (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u}) : Name P :=
  .mk {s : a.Entry // a.entryCode l s ∈ B} (fun s => a.child s.val.1) (fun s => s.val.2.val)

theorem Name.encode_restrict (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u})
    (hB : B ⊆ a.support l) : (a.restrict l B).encode l = B := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩
    exact hs ▸ s.property
  · intro hz
    obtain ⟨s,hs⟩ := ZFSet.mem_range.mp (hB hz)
    exact ⟨⟨s,hs ▸ hz⟩,hs⟩

theorem Name.mem_val_restrict (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u})
    (G : Set P) (x : ZFSet.{u}) : x ∈ (a.restrict l B).val G ↔
      ∃ i, ∃ q, q ≤ a.tag i ∧ ZFSet.pair ((a.child i).encode l) (l q) ∈ B ∧
        q ∈ G ∧ (a.child i).val G = x := by
  rw [Name.restrict,Name.mem_val]
  constructor
  · rintro ⟨⟨⟨i,q,hq⟩,hB⟩,hG,hx⟩
    exact ⟨i,q,hq,hB,hG,hx⟩
  · rintro ⟨i,q,hq,hB,hG,hx⟩
    exact ⟨⟨⟨i,⟨q,hq⟩⟩,hB⟩,hG,hx⟩

theorem Name.val_restrict_subset (l : P → ZFSet.{u}) (a : Name P) (B : ZFSet.{u})
    (G : GenericFilter P) : (a.restrict l B).val G.carrier ⊆ a.val G.carrier := by
  intro x hx
  obtain ⟨i,q,hq,_,hqG,hx⟩ := (a.mem_val_restrict l B G.carrier x).mp hx
  exact (a.mem_val_children G.carrier x).mpr ⟨i,G.upper hq hqG,hx⟩

end TuringRigidity.RecursiveNames

