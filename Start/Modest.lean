/-
Modest sets: the cartesian closed structure of `Asm(A)` restricts to them.

An assembly is *modest* when its realizers determine its elements; modest sets are, up to
isomorphism, exactly the partial equivalence relations of `Start/PER.lean`
(`Realizability.PER.modest_toAsm` and `Realizability.Assembly.toPER` are the two directions of
that correspondence at the level of objects).

This file records that modesty is stable under the whole cartesian closed structure built in
`Start/Assembly.lean` and `Start/AssemblyCcc.lean`:

* `Realizability.Assembly.modest_unitAsm` — the terminal assembly is modest;
* `Realizability.Assembly.Modest.prod` — a product of modest assemblies is modest;
* `Realizability.Assembly.Modest.exp` — an exponential with modest codomain is modest;
* `Realizability.Assembly.toPER` — the PER of a modest assembly.

So the full subcategory of modest assemblies — equivalently, the PERs — is closed under the
terminal object, binary products and exponentials of `Asm(A)`: it is a cartesian closed full
subcategory, which is what makes the PER interpretation of System F
(`Start/PERSystemF.lean`) possible.
-/

import Start.PER
import Start.AssemblyCcc

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

namespace Assembly

variable {A : Type u} [PCA A]

/-- The terminal assembly is modest. -/
theorem modest_unitAsm : (unitAsm.{u, v} A).Modest := by
  intro _ x y _ _
  rfl

/-- Church pairing is injective on the realizers it produces: the first projection recovers the
first component. -/
theorem pairEl_inj {a b a' b' : A} (h : PCA.pairEl a b = PCA.pairEl a' b') : a = a' ∧ b = b' := by
  constructor
  · have h₁ := PCA.fstComb_pairEl (A := A) a b
    rw [h, PCA.fstComb_pairEl] at h₁
    exact (Part.some_inj.1 h₁).symm
  · have h₂ := PCA.sndComb_pairEl (A := A) a b
    rw [h, PCA.sndComb_pairEl] at h₂
    exact (Part.some_inj.1 h₂).symm

/-- A product of modest assemblies is modest. -/
theorem Modest.prod {X Y : Assembly.{u, v} A} (hX : X.Modest) (hY : Y.Modest) :
    (prodAsm X Y).Modest := by
  rintro p ⟨x, y⟩ ⟨x', y'⟩ ⟨a, b, ha, hb, rfl⟩ ⟨a', b', ha', hb', hp⟩
  obtain ⟨rfl, rfl⟩ := pairEl_inj hp
  exact Prod.ext (hX a x x' ha ha') (hY b y y' hb hb')

/-- An exponential with modest codomain is modest. -/
theorem Modest.exp {X Y : Assembly.{u, v} A} (hY : Y.Modest) : (expAsm X Y).Modest := by
  intro r f g hf hg
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨a, ha⟩ := X.exists_realizer x
  obtain ⟨v, hv, hvf⟩ := hf a x ha
  obtain ⟨w, hw, hwg⟩ := hg a x ha
  rw [← Part.mem_unique hv hw] at hwg
  exact hY v _ _ hvf hwg

/-- The partial equivalence relation of a modest assembly: two elements of the algebra are
related when they realize the same element. -/
def toPER {X : Assembly.{u, u} A} (hX : X.Modest) : PER A where
  rel a b := ∃ x, X.realizes a x ∧ X.realizes b x
  symm := fun ⟨x, ha, hb⟩ => ⟨x, hb, ha⟩
  trans := fun ⟨x, ha, hbx⟩ ⟨y, hby, hc⟩ => by
    obtain rfl : x = y := hX _ _ _ hbx hby
    exact ⟨x, ha, hc⟩

theorem dom_toPER {X : Assembly.{u, u} A} (hX : X.Modest) (a : A) :
    (toPER hX).dom a ↔ ∃ x, X.realizes a x :=
  ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx, hx⟩⟩

end Assembly

end Realizability
