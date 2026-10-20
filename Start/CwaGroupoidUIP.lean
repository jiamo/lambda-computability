/-
**The independence of UIP** — task `M23-UIP-INDEPENDENT`.

* `GrpdModel.grpdIdStruct_not_UIP` — **UIP fails in the groupoid model** of
  `Start/CwaGroupoidId.lean`: over the terminal groupoid, the one-object groupoid `LoopG` whose automorphism group is `ℤ/2`
  has two distinct loops, and the identity type between them is empty.
* `GrpdModel.uip_independent` — **UIP is independent of the identity-type rules**: the set model
  `CwaType.idStruct` satisfies UIP and the groupoid model refutes it.
-/

import Start.CwaGroupoidId

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Cwa

namespace GrpdModel

/-- The one-object groupoid whose automorphism group is `ℤ/2` (`Bool` under `xor`). -/
def LoopG : Type u := PUnit.{u + 1}

instance : Groupoid.{u} LoopG.{u} where
  Hom _ _ := ULift.{u} Bool
  id _ := ⟨false⟩
  comp f g := ⟨xor f.down g.down⟩
  id_comp f := by obtain ⟨b⟩ := f; cases b <;> rfl
  comp_id f := by obtain ⟨b⟩ := f; cases b <;> rfl
  assoc f g h := by
    obtain ⟨a⟩ := f; obtain ⟨b⟩ := g; obtain ⟨c⟩ := h
    cases a <;> cases b <;> cases c <;> rfl
  inv f := f
  inv_comp f := by obtain ⟨b⟩ := f; cases b <;> rfl
  comp_inv f := by obtain ⟨b⟩ := f; cases b <;> rfl

/-- The terminal groupoid. -/
def unitG : Grpd.{u, u} := Grpd.of (Discrete PUnit.{u + 1})

/-- The type with a nontrivial loop: the constant family `LoopG` over the terminal groupoid. -/
def loopTy : grpdCwa.Ty unitG.{u} := (Functor.const _).obj (Grpd.of LoopG.{u})

/-- **UIP fails in the groupoid model.** -/
theorem grpdIdStruct_not_UIP : ¬ grpdIdStruct.{u}.UIP := by
  intro h
  obtain ⟨s⟩ := h (Γ := unitG) loopTy
  let P : GObj (disp loopTy ⋙ loopTy) := ⟨⟨⟨PUnit.unit⟩, PUnit.unit⟩, PUnit.unit⟩
  let x0 : GObj (disp (IdC loopTy) ⋙ IdC loopTy) :=
    ⟨⟨P, Discrete.mk (⟨true⟩ : ULift.{u} Bool)⟩, Discrete.mk (⟨false⟩ : ULift.{u} Bool)⟩
  have key : ∀ y : GObj (disp (IdC loopTy) ⋙ IdC loopTy), y = x0 →
      (y.base.fib ⟶ y.fib) → False := by
    rintro y rfl ⟨⟨h⟩⟩
    cases h
  exact key _ (Functor.congr_obj s.2 x0) (s.1.obj x0).fib.as

/-- **UIP is independent of the identity-type rules.**  The rules of `Cwa.IdStruct` (formation,
reflexivity, `J` with its computation rule, and stability under substitution) are satisfied by
the set model `CwaType.idStruct`, which validates UIP, and by the groupoid model `grpdIdStruct`,
which refutes it.  So neither UIP nor its negation follows from these rules. -/
theorem uip_independent :
    CwaType.idStruct.{u}.UIP ∧ ¬ grpdIdStruct.{u}.UIP ∧
    (∃ (C : Type (u + 1)) (_ : Category.{u} C) (T : Cwa.{u + 1, u, u + 1} C) (I : IdStruct T),
      I.UIP) ∧
    (∃ (C : Type (u + 1)) (_ : Category.{u} C) (T : Cwa.{u + 1, u, u + 1} C) (I : IdStruct T),
      ¬ I.UIP) :=
  ⟨CwaType.idStruct_UIP, grpdIdStruct_not_UIP, ⟨_, _, _, _, CwaType.idStruct_UIP⟩,
    ⟨_, _, _, _, grpdIdStruct_not_UIP⟩⟩

end GrpdModel
