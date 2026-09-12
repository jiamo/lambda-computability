/-
**Probes with a projective base for the exact completion of the assemblies.**

`Start/AsmExRegNotExact.lean` shows that the completion `ExReg(A)` of `Start/AsmExReg.lean` is not
exact, the obstruction being uniformity: a morphism into an object must pick one point per point
of the source *and* compute a realizer of the chosen point from a realizer of the source point.
The obstruction disappears when the source has a **partitioned** base — a regular projective of
`Asm(A)`, `Start/AssemblyProjective.lean` — because a point of a partitioned assembly has exactly
one realizer, so reading the choice off the realizer is a function.

This module builds the objects with which that is exploited in `Start/AsmExRegEffective.lean`.
All of them have the same shape: a set of tuples, each realized by the tuple itself, carrying two
points of a fixed object `R` together with whatever data the tuple is supposed to witness.  Such
an object is called a **probe** here; its base is partitioned by construction, so it is a legal
test object for the universal properties of the full subcategory on the projective bases, and the
data it carries is available to every tracker out of it.

Main definitions:

* `Realizability.ExReg.ProjBase`, `Realizability.ExReg.ExRegP` — the objects of the completion
  whose base is partitioned, and the full subcategory they span;
* `Realizability.ExReg.PairData`, `Realizability.ExReg.pairERel` — a probe: a set of tuples with
  a realizer and two points of `R`, related when the two points are related in `R`, with the
  realizers of the endpoints carried by every proof;
* `Realizability.ExReg.JMTracker`, `Realizability.ExReg.jmData` — joint monicity of a parallel
  pair read on realizers, and the probe that produces it;
* `Realizability.ExReg.compData` — the probe of **composable pairs**: two points of `R` and a
  proof that the second endpoint of the first is related to the first endpoint of the second;
* `Realizability.ExReg.EqvDataP` — the computational data of an internal equivalence relation of
  the full subcategory: a diagonal, a swap, and composites of maps out of objects with
  partitioned base.

Main results:

* `Realizability.ExReg.partitioned_pairERel` — a probe has a partitioned base;
* `Realizability.ExReg.homotopic_pair` — two maps out of a probe are homotopic as soon as the
  proof relating their values is computable from the tuple;
* `Realizability.ExReg.jmTracker_of_jointlyMono` — **joint monicity against objects with
  partitioned base yields the tracker**: a single element of the algebra produces a proof that
  two points of `R` are related from their realizers and from proofs that their images agree;
* `Realizability.ExReg.eqvDataP_of_isInternalEquiv` — an internal equivalence relation of the
  full subcategory carries the data above.
-/

import Start.AsmExRegCoeq
import Start.AssemblyProjective

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

open NotExact Coeq

variable {A : Type u} [PCA A]

/-! ### The objects with a projective base -/

/-- The objects of the completion whose base is a partitioned assembly, i.e. a regular projective
of `Asm(A)` (`Realizability.Assembly.regularProjective_iff`). -/
def ProjBase (A : Type u) [PCA A] : ObjectProperty (ERel.{u, v} A) :=
  fun E => Assembly.Partitioned E.base

/-- **The completion restricted to the regular projective bases**: the full subcategory of
`ExReg(A)` spanned by the objects whose base is partitioned. -/
abbrev ExRegP (A : Type u) [PCA A] :=
  ObjectProperty.FullSubcategory (ProjBase.{u, v} A)

/-! ### Probes -/

/-- The data of a **probe** over an object `R`: a set of tuples, a realizer of each tuple, and two
points of `R` read off a tuple, each with a realizer computable from the tuple. -/
structure PairData (R : ERel.{u, v} A) (P : Type v) where
  /-- The realizer of a tuple. -/
  rz : P → A
  /-- The first point carried by a tuple. -/
  fst : P → R.base.carrier
  /-- The second point carried by a tuple. -/
  snd : P → R.base.carrier
  /-- A realizer of the first point is computable from the tuple. -/
  fst_tracked : ∃ t : A, ∀ z : P, ∃ a ∈ PCA.app t (rz z), R.base.realizes a (fst z)
  /-- A realizer of the second point is computable from the tuple. -/
  snd_tracked : ∃ t : A, ∀ z : P, ∃ a ∈ PCA.app t (rz z), R.base.realizes a (snd z)

variable {R : ERel.{u, v} A} {P : Type v}

/-- The probe attached to such data: the tuples, each realized by itself, two of them related when
their two points are related in `R`, a proof carrying in addition the realizers of its two
endpoints, which is what keeps those endpoints computable. -/
noncomputable def pairERel (D : PairData R P) : ERel.{u, v} A where
  base := Assembly.partAsm A D.rz
  Prf w z z' := ∃ s t : A, R.Prf s (D.fst z) (D.fst z') ∧ R.Prf t (D.snd z) (D.snd z') ∧
    w = PCA.pairEl (PCA.pairEl s t) (PCA.pairEl (D.rz z) (D.rz z'))
  ends := by
    obtain ⟨g, hg⟩ := exists_sThen (PCA.i A)
    refine ⟨g, ?_⟩
    rintro w z z' ⟨s, t, -, -, rfl⟩
    exact ⟨_, hg _ _ _ (mem_i _), D.rz z, D.rz z', rfl, rfl, rfl⟩
  refl' := by
    obtain ⟨rr, hrr⟩ := R.refl'
    obtain ⟨tf, htf⟩ := D.fst_tracked
    obtain ⟨ts, hts⟩ := D.snd_tracked
    obtain ⟨c₁, hc₁⟩ := exists_pairOf (PCA.comp rr tf) (PCA.comp rr ts)
    obtain ⟨c₂, hc₂⟩ := exists_pairOf (PCA.i A) (PCA.i A)
    obtain ⟨t, ht⟩ := exists_pairOf c₁ c₂
    refine ⟨t, ?_⟩
    intro a z ha
    have hrz : a = D.rz z := ha
    subst hrz
    obtain ⟨b₁, hb₁, hb₁r⟩ := htf z
    obtain ⟨b₂, hb₂, hb₂r⟩ := hts z
    obtain ⟨v₁, hv₁, hv₁p⟩ := hrr b₁ (D.fst z) hb₁r
    obtain ⟨v₂, hv₂, hv₂p⟩ := hrr b₂ (D.snd z) hb₂r
    exact ⟨_, ht _ _ _ (hc₁ _ _ _ (mem_comp hb₁ hv₁) (mem_comp hb₂ hv₂))
      (hc₂ _ _ _ (mem_i _) (mem_i _)), v₁, v₂, hv₁p, hv₂p, rfl⟩
  symm' := by
    obtain ⟨sr, hsr⟩ := R.symm'
    obtain ⟨a₁, ha₁⟩ := exists_ffThen sr
    obtain ⟨a₂, ha₂⟩ := exists_fsThen sr
    obtain ⟨a₃, ha₃⟩ := exists_ssThen (PCA.i A)
    obtain ⟨a₄, ha₄⟩ := exists_sfThen (PCA.i A)
    obtain ⟨c₁, hc₁⟩ := exists_pairOf a₁ a₂
    obtain ⟨c₂, hc₂⟩ := exists_pairOf a₃ a₄
    obtain ⟨t, ht⟩ := exists_pairOf c₁ c₂
    refine ⟨t, ?_⟩
    rintro w z z' ⟨s, tt, hs, htt, rfl⟩
    obtain ⟨v₁, hv₁, hv₁p⟩ := hsr s (D.fst z) (D.fst z') hs
    obtain ⟨v₂, hv₂, hv₂p⟩ := hsr tt (D.snd z) (D.snd z') htt
    exact ⟨_, ht _ _ _ (hc₁ _ _ _ (ha₁ s tt _ v₁ hv₁) (ha₂ s tt _ v₂ hv₂))
      (hc₂ _ _ _ (ha₃ _ _ _ _ (mem_i _)) (ha₄ _ _ _ _ (mem_i _))), v₁, v₂, hv₁p, hv₂p, rfl⟩
  trans' := by
    obtain ⟨tr, htr⟩ := R.trans'
    obtain ⟨gs, hgs⟩ := exists_ffThen (PCA.i A)
    obtain ⟨gt, hgt⟩ := exists_fsThen (PCA.i A)
    obtain ⟨grz, hgrz⟩ := exists_sfThen (PCA.i A)
    obtain ⟨grz', hgrz'⟩ := exists_ssThen (PCA.i A)
    obtain ⟨x₁, hx₁⟩ := exists_binLeft gs
    obtain ⟨y₁, hy₁⟩ := exists_binRight gs
    obtain ⟨c₁, hc₁⟩ := exists_binApply tr x₁ y₁
    obtain ⟨x₂, hx₂⟩ := exists_binLeft gt
    obtain ⟨y₂, hy₂⟩ := exists_binRight gt
    obtain ⟨c₂, hc₂⟩ := exists_binApply tr x₂ y₂
    obtain ⟨c₃, hc₃⟩ := exists_binLeft grz
    obtain ⟨c₄, hc₄⟩ := exists_binRight grz'
    obtain ⟨e₁, he₁⟩ := exists_binPairOf c₁ c₂
    obtain ⟨e₂, he₂⟩ := exists_binPairOf c₃ c₄
    obtain ⟨t, ht⟩ := exists_binPairOf e₁ e₂
    refine ⟨t, ?_⟩
    rintro w w' z z' z'' ⟨s, tt, hs, htt, rfl⟩ ⟨s', tt', hs', htt', rfl⟩
    obtain ⟨v₁, hv₁, hv₁p⟩ := htr s s' (D.fst z) (D.fst z') (D.fst z'') hs hs'
    obtain ⟨v₂, hv₂, hv₂p⟩ := htr tt tt' (D.snd z) (D.snd z') (D.snd z'') htt htt'
    refine ⟨_, ht _ _ _ _
      (he₁ _ _ _ _
        (hc₁ _ _ s s' v₁ (hx₁ _ _ s (hgs s tt _ s (mem_i s)))
          (hy₁ _ _ s' (hgs s' tt' _ s' (mem_i s'))) hv₁)
        (hc₂ _ _ tt tt' v₂ (hx₂ _ _ tt (hgt s tt _ tt (mem_i tt)))
          (hy₂ _ _ tt' (hgt s' tt' _ tt' (mem_i tt'))) hv₂))
      (he₂ _ _ _ _ (hc₃ _ _ _ (hgrz _ _ _ _ (mem_i _)))
        (hc₄ _ _ _ (hgrz' _ _ _ _ (mem_i _)))), v₁, v₂, hv₁p, hv₂p, rfl⟩

/-- **A probe has a partitioned base**: a tuple is realized by itself alone. -/
theorem partitioned_pairERel (D : PairData R P) :
    Assembly.Partitioned (pairERel D).base :=
  Assembly.partitioned_partAsm _

@[simp] theorem pairERel_realizes (D : PairData R P) (a : A) (z : P) :
    (pairERel D).base.realizes a z ↔ a = D.rz z := Iff.rfl

/-- The first projection of a probe. -/
noncomputable def pairFst (D : PairData R P) : Pre (pairERel D) R where
  toFun := D.fst
  tracked := by
    obtain ⟨g, hg⟩ := exists_ffThen (PCA.i A)
    refine ⟨g, ?_⟩
    rintro w z z' ⟨s, t, hs, -, rfl⟩
    exact ⟨s, hg s t _ s (mem_i s), hs⟩

/-- The second projection of a probe. -/
noncomputable def pairSnd (D : PairData R P) : Pre (pairERel D) R where
  toFun := D.snd
  tracked := by
    obtain ⟨g, hg⟩ := exists_fsThen (PCA.i A)
    refine ⟨g, ?_⟩
    rintro w z z' ⟨s, t, -, ht, rfl⟩
    exact ⟨t, hg s t _ t (mem_i t), ht⟩

@[simp] theorem pairFst_toFun (D : PairData R P) : (pairFst D).toFun = D.fst := rfl

@[simp] theorem pairSnd_toFun (D : PairData R P) : (pairSnd D).toFun = D.snd := rfl

/-- **Two maps out of a probe are homotopic** as soon as a proof relating their values at a tuple
is computable from that tuple.  This is the whole point of a probe: its realizers are its
points. -/
theorem homotopic_pair {F : ERel.{u, v} A} (D : PairData R P) (f g : Pre R F)
    (h : ∃ t : A, ∀ z : P, ∃ w ∈ PCA.app t (D.rz z),
      F.Prf w (f.toFun (D.fst z)) (g.toFun (D.snd z))) :
    Homotopic ((pairFst D).comp f) ((pairSnd D).comp g) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, fun a z ha => ?_⟩
  have hrz : a = D.rz z := ha
  subst hrz
  exact ht z

/-! ### The probe for joint monicity -/

variable {E : ERel.{u, max u v} A}

/-- A tuple of the joint monicity probe: two points of `R`, realizers of them, and proofs that
their images under the two legs are related. -/
structure JMPt {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) : Type (max u v) where
  /-- The first point. -/
  x : R.base.carrier
  /-- The second point. -/
  y : R.base.carrier
  /-- A realizer of the first point. -/
  ra : A
  /-- A realizer of the second point. -/
  rb : A
  /-- A proof that the images under the first leg are related. -/
  pf₁ : A
  /-- A proof that the images under the second leg are related. -/
  pf₂ : A
  /-- `ra` realizes `x`. -/
  hra : R.base.realizes ra x
  /-- `rb` realizes `y`. -/
  hrb : R.base.realizes rb y
  /-- `pf₁` proves that the images under the first leg are related. -/
  hpf₁ : E.Prf pf₁ (f₁.toFun x) (f₁.toFun y)
  /-- `pf₂` proves that the images under the second leg are related. -/
  hpf₂ : E.Prf pf₂ (f₂.toFun x) (f₂.toFun y)

/-- The realizer of such a tuple: the tuple itself. -/
noncomputable def jmRz {R : ERel.{u, max u v} A} {f₁ f₂ : Pre R E} (z : JMPt f₁ f₂) : A :=
  PCA.pairEl (PCA.pairEl z.ra z.rb) (PCA.pairEl z.pf₁ z.pf₂)

/-- The joint monicity probe. -/
noncomputable def jmData {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) :
    PairData R (JMPt f₁ f₂) where
  rz := jmRz
  fst z := z.x
  snd z := z.y
  fst_tracked := by
    obtain ⟨g, hg⟩ := exists_ffThen (PCA.i A)
    exact ⟨g, fun z => ⟨z.ra, hg _ _ _ _ (mem_i _), z.hra⟩⟩
  snd_tracked := by
    obtain ⟨g, hg⟩ := exists_fsThen (PCA.i A)
    exact ⟨g, fun z => ⟨z.rb, hg _ _ _ _ (mem_i _), z.hrb⟩⟩

/-- Joint monicity of a parallel pair `f₁, f₂ : R ⟶ E`, read on realizers: a single element of
the algebra turns realizers of two points of `R`, together with proofs that their images under
`f₁` and under `f₂` are related, into a proof that the two points are related.  This is the
computational content of the pair being jointly monic. -/
def JMTracker {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) : Prop :=
  ∃ t : A, ∀ (x y : R.base.carrier) (a b p q : A), R.base.realizes a x → R.base.realizes b y →
    E.Prf p (f₁.toFun x) (f₁.toFun y) → E.Prf q (f₂.toFun x) (f₂.toFun y) →
    ∃ w ∈ PCA.app t (PCA.pairEl (PCA.pairEl a b) (PCA.pairEl p q)), R.Prf w x y

/-- After the first leg, the two projections of the joint monicity probe are homotopic: the proof
is part of the tuple. -/
theorem jm_homotopic_fst {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) :
    Homotopic ((pairFst (jmData f₁ f₂)).comp f₁) ((pairSnd (jmData f₁ f₂)).comp f₁) := by
  refine homotopic_pair _ _ _ ⟨?_, ?_⟩
  · exact PCA.comp (PCA.fstComb A) (PCA.sndComb A)
  · exact fun z => ⟨z.pf₁, mem_comp (mem_sndComb _ _) (mem_fstComb _ _), z.hpf₁⟩

/-- After the second leg, the two projections of the joint monicity probe are homotopic. -/
theorem jm_homotopic_snd {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) :
    Homotopic ((pairFst (jmData f₁ f₂)).comp f₂) ((pairSnd (jmData f₁ f₂)).comp f₂) := by
  refine homotopic_pair _ _ _ ⟨?_, ?_⟩
  · exact PCA.comp (PCA.sndComb A) (PCA.sndComb A)
  · exact fun z => ⟨z.pf₂, mem_comp (mem_sndComb _ _) (mem_sndComb _ _), z.hpf₂⟩

/-- **Joint monicity against the objects with partitioned base yields the tracker.** -/
theorem jmTracker_of_jointlyMono {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E)
    (hjm : ∀ (T : ERel.{u, max u v} A), Assembly.Partitioned T.base →
      ∀ g k : T ⟶ R, g ≫ homOf f₁ = k ≫ homOf f₁ → g ≫ homOf f₂ = k ≫ homOf f₂ → g = k) :
    JMTracker f₁ f₂ := by
  have heq : homOf (pairFst (jmData f₁ f₂)) = homOf (pairSnd (jmData f₁ f₂)) :=
    hjm _ (partitioned_pairERel _) _ _
      (by rw [homOf_comp, homOf_comp]; exact homOf_eq_iff.2 (jm_homotopic_fst f₁ f₂))
      (by rw [homOf_comp, homOf_comp]; exact homOf_eq_iff.2 (jm_homotopic_snd f₁ f₂))
  obtain ⟨t, ht⟩ := homOf_eq_iff.1 heq
  refine ⟨t, fun x y a b p q ha hb hp hq => ?_⟩
  exact ht _ ⟨x, y, a, b, p, q, ha, hb, hp, hq⟩ rfl

/-! ### The probe of composable pairs -/

/-- A tuple of the probe of composable pairs: two points of `R`, realizers of them, and a proof
that the second endpoint of the first is related to the first endpoint of the second. -/
structure CompPt {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) : Type (max u v) where
  /-- The first point. -/
  x : R.base.carrier
  /-- The second point. -/
  y : R.base.carrier
  /-- A realizer of the first point. -/
  ra : A
  /-- A realizer of the second point. -/
  rb : A
  /-- The middle proof. -/
  pm : A
  /-- `ra` realizes `x`. -/
  hra : R.base.realizes ra x
  /-- `rb` realizes `y`. -/
  hrb : R.base.realizes rb y
  /-- `pm` proves that the two points are composable. -/
  hpm : E.Prf pm (f₂.toFun x) (f₁.toFun y)

/-- The realizer of such a tuple: the tuple itself. -/
noncomputable def compRz {R : ERel.{u, max u v} A} {f₁ f₂ : Pre R E} (z : CompPt f₁ f₂) : A :=
  PCA.pairEl (PCA.pairEl z.ra z.rb) z.pm

/-- The probe of composable pairs. -/
noncomputable def compData {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) :
    PairData R (CompPt f₁ f₂) where
  rz := compRz
  fst z := z.x
  snd z := z.y
  fst_tracked := by
    obtain ⟨g, hg⟩ := exists_ffThen (PCA.i A)
    exact ⟨g, fun z => ⟨z.ra, hg _ _ _ _ (mem_i _), z.hra⟩⟩
  snd_tracked := by
    obtain ⟨g, hg⟩ := exists_fsThen (PCA.i A)
    exact ⟨g, fun z => ⟨z.rb, hg _ _ _ _ (mem_i _), z.hrb⟩⟩

/-- The two projections of the probe of composable pairs are composable: the middle proof is part
of every tuple. -/
theorem comp_homotopic {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) :
    Homotopic ((pairFst (compData f₁ f₂)).comp f₂) ((pairSnd (compData f₁ f₂)).comp f₁) :=
  homotopic_pair _ _ _ ⟨PCA.sndComb A, fun z => ⟨z.pm, mem_sndComb _ _, z.hpm⟩⟩

/-! ### The data of an internal equivalence relation with projective bases -/

/-- The computational data of an internal equivalence relation `f₁, f₂ : R ⟶ E` of the full
subcategory on the projective bases: a diagonal, a swap, and a composite for every pair of maps
out of an object *with partitioned base* whose middle endpoints agree.  Compared with
`Realizability.ExReg.Coeq.EqvData` only the last clause is weaker, and it is all that the
construction of the quotient needs, because the composable pairs can be probed. -/
structure EqvDataP {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E) where
  /-- The diagonal. -/
  diag : Pre E R
  /-- The first leg of the diagonal is the identity. -/
  diag_fst : Homotopic (diag.comp f₁) (Pre.id E)
  /-- The second leg of the diagonal is the identity. -/
  diag_snd : Homotopic (diag.comp f₂) (Pre.id E)
  /-- The swap. -/
  swap : Pre R R
  /-- The swap exchanges the two legs. -/
  swap_fst : Homotopic (swap.comp f₁) f₂
  /-- The swap exchanges the two legs. -/
  swap_snd : Homotopic (swap.comp f₂) f₁
  /-- Two maps into `R` out of an object with partitioned base, with matching middle endpoints,
  have a composite. -/
  comp' : ∀ {T : ERel.{u, max u v} A}, Assembly.Partitioned T.base → ∀ g h : Pre T R,
    Homotopic (g.comp f₂) (h.comp f₁) →
    ∃ k : Pre T R, Homotopic (k.comp f₁) (g.comp f₁) ∧ Homotopic (k.comp f₂) (h.comp f₂)

/-- **An internal equivalence relation of the full subcategory carries that data.** -/
theorem eqvDataP_of_isInternalEquiv {R : ERel.{u, max u v} A} (f₁ f₂ : Pre R E)
    (hrefl : ∃ d : E ⟶ R, d ≫ homOf f₁ = 𝟙 E ∧ d ≫ homOf f₂ = 𝟙 E)
    (hsymm : ∃ s : R ⟶ R, s ≫ homOf f₁ = homOf f₂ ∧ s ≫ homOf f₂ = homOf f₁)
    (htrans : ∀ (T : ERel.{u, max u v} A), Assembly.Partitioned T.base → ∀ g h : T ⟶ R,
      g ≫ homOf f₂ = h ≫ homOf f₁ →
      ∃ k : T ⟶ R, k ≫ homOf f₁ = g ≫ homOf f₁ ∧ k ≫ homOf f₂ = h ≫ homOf f₂) :
    Nonempty (EqvDataP f₁ f₂) := by
  obtain ⟨d, hd₁, hd₂⟩ := hrefl
  obtain ⟨s, hs₁, hs₂⟩ := hsymm
  refine ⟨{ diag := rep d
            diag_fst := ?_
            diag_snd := ?_
            swap := rep s
            swap_fst := ?_
            swap_snd := ?_
            comp' := ?_ }⟩
  · exact homOf_eq_iff.1 (by rw [← homOf_comp, homOf_rep, hd₁, id_eq])
  · exact homOf_eq_iff.1 (by rw [← homOf_comp, homOf_rep, hd₂, id_eq])
  · exact homOf_eq_iff.1 (by rw [← homOf_comp, homOf_rep, hs₁])
  · exact homOf_eq_iff.1 (by rw [← homOf_comp, homOf_rep, hs₂])
  · intro T hT g k hgk
    have hgk' : homOf g ≫ homOf f₂ = homOf k ≫ homOf f₁ := by
      rw [homOf_comp, homOf_comp]; exact homOf_eq_iff.2 hgk
    obtain ⟨m, hm₁, hm₂⟩ := htrans T hT (homOf g) (homOf k) hgk'
    refine ⟨rep m, homOf_eq_iff.1 ?_, homOf_eq_iff.1 ?_⟩
    · rw [← homOf_comp, ← homOf_comp, homOf_rep]; exact hm₁
    · rw [← homOf_comp, ← homOf_comp, homOf_rep]; exact hm₂

/-- The composite of the two projections of the probe of composable pairs. -/
noncomputable def compPtP {R : ERel.{u, max u v} A} {f₁ f₂ : Pre R E} (d : EqvDataP f₁ f₂) :
    Pre (pairERel (compData f₁ f₂)) R :=
  (d.comp' (partitioned_pairERel _) (pairFst (compData f₁ f₂)) (pairSnd (compData f₁ f₂))
    (comp_homotopic f₁ f₂)).choose

theorem compPtP_fst {R : ERel.{u, max u v} A} {f₁ f₂ : Pre R E} (d : EqvDataP f₁ f₂) :
    Homotopic ((compPtP d).comp f₁) ((pairFst (compData f₁ f₂)).comp f₁) :=
  (d.comp' (partitioned_pairERel _) (pairFst (compData f₁ f₂)) (pairSnd (compData f₁ f₂))
    (comp_homotopic f₁ f₂)).choose_spec.1

theorem compPtP_snd {R : ERel.{u, max u v} A} {f₁ f₂ : Pre R E} (d : EqvDataP f₁ f₂) :
    Homotopic ((compPtP d).comp f₂) ((pairSnd (compData f₁ f₂)).comp f₂) :=
  (d.comp' (partitioned_pairERel _) (pairFst (compData f₁ f₂)) (pairSnd (compData f₁ f₂))
    (comp_homotopic f₁ f₂)).choose_spec.2

end ExReg

end Realizability
