/-
**Projective objects in the category of assemblies.**

`Start/AssemblyRegular.lean` identifies the strong (equivalently, regular) epimorphisms of
`Asm(A)` as the morphisms that *lift realizers*: a single element of the algebra turns a realizer
of a point of the codomain into a realizer of one of its preimages.  This module identifies the
objects that are projective with respect to those covers.

An assembly is **partitioned** when every point has exactly one realizer, so that the assembly is
the graph of a function `C → A`.  Such an assembly is projective for the covers: a map out of it
is lifted by composing its tracker with the lifting combinator of the cover, which is precisely
the point where realizability makes choice constructive.  Every assembly is covered by a
partitioned one — take the pairs `(a, x)` with `a` a realizer of `x`, realized by `a` alone — and
conversely a regular projective is a retract of its cover, hence isomorphic to a partitioned
assembly.  So:

* `Realizability.Assembly.Partitioned.regularProjective` — partitioned assemblies are projective
  for the covers;
* `Realizability.Assembly.exists_partitioned_cover` — **`Asm(A)` has enough regular
  projectives**;
* `Realizability.Assembly.regularProjective_iff` — **the regular projectives of `Asm(A)` are
  exactly the assemblies isomorphic to partitioned ones**.

Projectivity for *all* epimorphisms is a strictly stronger demand, and it fails.  Over Kleene's
first algebra the standard numbers assembly is partitioned, hence regular projective, but the
identity function onto the indiscrete assembly on the same set is an epimorphism along which the
non-computable diagonal function does not lift:

* `Realizability.Kleene.regularProjective_natK1` — the numbers are regular projective;
* `Realizability.Kleene.not_projective_natK1` — the numbers are **not** projective;
* `Realizability.Kleene.not_liftsRealizers_natToNabla` — the epimorphism responsible does not
  lift realizers, so it is not a strong epimorphism: in `Asm(K₁)` the epimorphisms and the strong
  epimorphisms differ.
-/

import Start.AssemblyRegular
import Start.AssemblyKleene
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace Assembly

variable {A : Type u} [PCA A]

/-! ### Partitioned assemblies -/

/-- The assembly on a set with one chosen realizer for each element. -/
def partAsm (A : Type u) [PCA A] {C : Type v} (e : C → A) : Assembly.{u, v} A where
  carrier := C
  realizes a x := a = e x
  exists_realizer x := ⟨e x, rfl⟩

@[simp] theorem partAsm_realizes {C : Type v} (e : C → A) (a : A) (x : C) :
    (partAsm A e).realizes a x ↔ a = e x := Iff.rfl

/-- An assembly is **partitioned** when every point has exactly one realizer. -/
def Partitioned (X : Assembly.{u, v} A) : Prop :=
  ∃ e : X.carrier → A, ∀ (a : A) (x : X.carrier), X.realizes a x ↔ a = e x

theorem partitioned_partAsm {C : Type v} (e : C → A) : Partitioned (partAsm A e) :=
  ⟨e, fun _ _ => Iff.rfl⟩

/-- Partitioned assemblies are closed under binary products: the Church pair of the two chosen
realizers is the chosen realizer of a pair. -/
theorem Partitioned.prod {X Y : Assembly.{u, v} A} (hX : Partitioned X) (hY : Partitioned Y) :
    Partitioned (prodAsm X Y) := by
  obtain ⟨e, he⟩ := hX
  obtain ⟨d, hd⟩ := hY
  refine ⟨fun z => PCA.pairEl (e z.1) (d z.2), fun p z => ⟨?_, ?_⟩⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [(he a z.1).1 ha, (hd b z.2).1 hb]
  · rintro rfl
    exact ⟨e z.1, d z.2, (he _ _).2 rfl, (hd _ _).2 rfl, rfl⟩

/-- Two isomorphisms induce an isomorphism of the product assemblies. -/
noncomputable def prodMapIso {X Y P Q : Assembly.{u, v} A} (i : X ≅ P) (j : Y ≅ Q) :
    prodAsm X Y ≅ prodAsm P Q where
  hom := prodLift (prodFst X Y ≫ i.hom) (prodSnd X Y ≫ j.hom)
  inv := prodLift (prodFst P Q ≫ i.inv) (prodSnd P Q ≫ j.inv)
  hom_inv_id := hom_ext fun z => Prod.ext
    (congrArg (fun k : X ⟶ X => k.toFun z.1) i.hom_inv_id)
    (congrArg (fun k : Y ⟶ Y => k.toFun z.2) j.hom_inv_id)
  inv_hom_id := hom_ext fun z => Prod.ext
    (congrArg (fun k : P ⟶ P => k.toFun z.1) i.inv_hom_id)
    (congrArg (fun k : Q ⟶ Q => k.toFun z.2) j.inv_hom_id)

/-! ### Projectivity with respect to the covers -/

/-- An assembly is **regular projective** when every map out of it lifts along every morphism
that lifts realizers, i.e. along every strong epimorphism. -/
def RegularProjective (P : Assembly.{u, v} A) : Prop :=
  ∀ {X Y : Assembly.{u, v} A} (g : X ⟶ Y), LiftsRealizers g → ∀ f : P ⟶ Y,
    ∃ h : P ⟶ X, h ≫ g = f

/-- **Partitioned assemblies are regular projective**: the lift is computed by composing the
tracker of the map with the lifting combinator of the cover. -/
theorem Partitioned.regularProjective {P : Assembly.{u, v} A} (hP : Partitioned P) :
    RegularProjective P := by
  classical
  obtain ⟨e, he⟩ := hP
  intro X Y g hg f
  obtain ⟨t, ht⟩ := f.tracked
  obtain ⟨l, hl⟩ := hg
  have key : ∀ p : P.carrier, ∃ x : X.carrier, g.toFun x = f.toFun p ∧
      ∃ w, w ∈ PCA.app (PCA.comp l t) (e p) ∧ X.realizes w x := by
    intro p
    obtain ⟨v, hv, hvf⟩ := ht (e p) p ((he (e p) p).2 rfl)
    obtain ⟨w, hw, x, hx, hwx⟩ := hl v (f.toFun p) hvf
    refine ⟨x, hx, w, ?_, hwx⟩
    have hmem : w ∈ Part.some l ⬝ (Part.some t ⬝ Part.some (e p)) := by
      rw [papp_some_some, papp_some_left]
      exact Part.mem_bind_iff.2 ⟨v, hv, hw⟩
    have h2 := PCA.comp_app l t (e p) w hmem
    rwa [papp_some_some] at h2
  choose x hgx hw using key
  refine ⟨⟨x, ⟨PCA.comp l t, fun a p ha => ?_⟩⟩, hom_ext fun p => hgx p⟩
  obtain ⟨w, hwmem, hwx⟩ := hw p
  exact ⟨w, ((he a p).1 ha) ▸ hwmem, hwx⟩

/-- Regular projectivity is invariant under isomorphism. -/
theorem RegularProjective.of_iso {P Q : Assembly.{u, v} A} (hP : RegularProjective P)
    (i : Q ≅ P) : RegularProjective Q := by
  intro X Y g hg f
  obtain ⟨h, hh⟩ := hP g hg (i.inv ≫ f)
  refine ⟨i.hom ≫ h, ?_⟩
  rw [Category.assoc, hh, ← Category.assoc, i.hom_inv_id, Category.id_comp]

/-! ### Enough regular projectives -/

variable (X : Assembly.{u, max u v} A)

/-- The canonical partitioned cover of an assembly: the pairs `(a, x)` with `a` a realizer of
`x`, where `(a, x)` is realized by `a` alone. -/
def coverAsm : Assembly.{u, max u v} A :=
  partAsm A (fun p : {p : A × X.carrier // X.realizes p.1 p.2} => p.1.1)

/-- The canonical cover is partitioned. -/
theorem partitioned_coverAsm : Partitioned (coverAsm X) := partitioned_partAsm _

/-- The covering map, forgetting the realizer. -/
noncomputable def coverHom : coverAsm X ⟶ X where
  toFun p := p.1.2
  tracked := ⟨PCA.i A, fun a p ha => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, by
    have hp : a = p.1.1 := ha
    exact hp ▸ p.2⟩⟩

/-- The covering map lifts realizers: a realizer of a point is a realizer of the pair it forms
with that point. -/
theorem liftsRealizers_coverHom : LiftsRealizers (coverHom X) :=
  ⟨PCA.i A, fun a y ha =>
    ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, ⟨⟨(a, y), ha⟩, rfl, rfl⟩⟩⟩

/-- **The assemblies have enough regular projectives.** -/
theorem exists_partitioned_cover :
    ∃ (P : Assembly.{u, max u v} A) (p : P ⟶ X), Partitioned P ∧ LiftsRealizers p :=
  ⟨coverAsm X, coverHom X, partitioned_coverAsm X, liftsRealizers_coverHom X⟩

/-- A regular projective assembly is isomorphic to a partitioned one: it is a retract of its
canonical cover, and the realizers picked out by the retraction partition it. -/
theorem exists_partitioned_iso_of_regularProjective (h : RegularProjective X) :
    ∃ P : Assembly.{u, max u v} A, Partitioned P ∧ Nonempty (X ≅ P) := by
  obtain ⟨s, hs⟩ := h (coverHom X) (liftsRealizers_coverHom X) (𝟙 X)
  have hsx : ∀ x : X.carrier, (s.toFun x).1.2 = x := fun x =>
    congrArg (fun k : X ⟶ X => k.toFun x) hs
  refine ⟨partAsm A fun x : X.carrier => (s.toFun x).1.1, partitioned_partAsm _,
    ⟨⟨⟨_root_.id, ?_⟩, ⟨_root_.id, ?_⟩, hom_ext fun _ => rfl, hom_ext fun _ => rfl⟩⟩⟩
  · obtain ⟨t, ht⟩ := s.tracked
    refine ⟨t, fun a x hax => ?_⟩
    obtain ⟨v, hv, hvx⟩ := ht a x hax
    exact ⟨v, hv, hvx⟩
  · refine ⟨PCA.i A, fun a x hax => ⟨a, by rw [PCA.i_app]; exact Part.mem_some _, ?_⟩⟩
    have ha : a = (s.toFun x).1.1 := hax
    have hreal := (s.toFun x).2
    rw [hsx x] at hreal
    exact ha ▸ hreal

/-- **The regular projectives of `Asm(A)` are exactly the assemblies isomorphic to partitioned
assemblies.** -/
theorem regularProjective_iff :
    RegularProjective X ↔ ∃ P : Assembly.{u, max u v} A, Partitioned P ∧ Nonempty (X ≅ P) := by
  refine ⟨exists_partitioned_iso_of_regularProjective X, ?_⟩
  rintro ⟨P, hP, ⟨i⟩⟩
  exact RegularProjective.of_iso (Partitioned.regularProjective hP) i

/-- Regular projectives are closed under binary products. -/
theorem RegularProjective.prod {W Z : Assembly.{u, max u v} A} (hW : RegularProjective W)
    (hZ : RegularProjective Z) : RegularProjective (prodAsm W Z) := by
  obtain ⟨P, hP, ⟨i⟩⟩ := exists_partitioned_iso_of_regularProjective W hW
  obtain ⟨Q, hQ, ⟨j⟩⟩ := exists_partitioned_iso_of_regularProjective Z hZ
  exact RegularProjective.of_iso (Partitioned.regularProjective (hP.prod hQ)) (prodMapIso i j)

end Assembly

/-! ### Kleene's first algebra: regular projective but not projective -/

namespace Kleene

open Realizability.Assembly

/-- The standard numbers assembly is partitioned: a number is realized by itself alone. -/
theorem partitioned_natK1 : Partitioned natK1 := ⟨_root_.id, fun _ _ => Iff.rfl⟩

/-- The standard numbers assembly is regular projective. -/
theorem regularProjective_natK1 : RegularProjective natK1 :=
  Partitioned.regularProjective partitioned_natK1

/-- The identity function, seen as a morphism onto the indiscrete assembly on the numbers. -/
noncomputable def natToNabla : natK1 ⟶ nablaAsm ℕ ℕ := toNabla _root_.id

instance epi_natToNabla : Epi natToNabla :=
  epi_of_surjective (f := natToNabla) fun n => ⟨n, rfl⟩

/-- **The standard numbers assembly is not projective**: the diagonal function does not lift
along the epimorphism onto the indiscrete assembly. -/
theorem not_projective_natK1 : ¬ Projective natK1 := by
  intro h
  obtain ⟨lift, hlift⟩ := h.factors (toNabla diag) natToNabla
  have hfun : lift.toFun = diag :=
    funext fun n => congrArg (fun k : natK1 ⟶ nablaAsm ℕ ℕ => k.toFun n) hlift
  exact not_tracked_diag (hfun ▸ lift.tracked)

/-- The epimorphism onto the indiscrete assembly does not lift realizers: a single element of the
algebra would have to produce a realizer of every number from one and the same argument. -/
theorem not_liftsRealizers_natToNabla : ¬ LiftsRealizers natToNabla := by
  rintro ⟨r, hr⟩
  have key : ∀ n : ℕ, n ∈ PCA.app r 0 := by
    intro n
    obtain ⟨v, hv, m, hm, hvm⟩ := hr 0 n trivial
    have h1 : v = m := hvm
    have h2 : m = n := hm
    rw [← h2, ← h1]
    exact hv
  have hcon : (0 : ℕ) = 1 := Part.mem_unique (key 0) (key 1)
  exact absurd hcon (by decide)

end Kleene

end Realizability
