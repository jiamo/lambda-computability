/-
**Equalizers in the exact completion of the assemblies, and hence finite limits.**

Let `f, g : E ⟶ F` be two morphisms of pseudo-equivalence relations, presented by pre-morphisms.
Their equalizer is the relation whose points are the points `x` of the base of `E` for which
`f x` and `g x` are related, and whose *proofs* carry, besides a proof `x ~ y` in `E`, a proof of
`f x ~ g x` and a proof of `f y ~ g y`.  Carrying the two witnesses is what makes the endpoints
of a proof computable: the realizer of a point of the equalizer is the pair of a realizer of `x`
and of a proof that `f x ~ g x`, and neither is recoverable from the other.

With the binary products of `Start/AsmExRegProd.lean` and the terminal object of
`Start/AsmExReg.lean`, this gives **all finite limits** in the completion.

Main results:

* `Realizability.ExReg.eqObj` — the equalizer relation, and `Realizability.ExReg.eqForkIsLimit`
  — **it is an equalizer**;
* `Realizability.ExReg.instHasEqualizers`, `.instHasFiniteLimits` — the completion has
  equalizers, hence finite limits.
-/

import Start.AsmExRegProd
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A]

/-! ### One more combinator -/

/-- The combinator `λxy. pair (r x) (s y)`. -/
theorem exists_binOf (r s : A) : ∃ t : A, ∀ x y u w : A, u ∈ PCA.app r x → w ∈ PCA.app s y →
    PCA.pairEl u w ∈ (Part.some t ⬝ Part.some x) ⬝ Part.some y := by
  refine ⟨PCA.lam2 (Expr.app (Expr.app (Expr.const (PCA.pairComb A))
      (Expr.app (Expr.const r) (Expr.var 0))) (Expr.app (Expr.const s) (Expr.var 1))),
    fun x y u w hu hw => ?_⟩
  refine PCA.lam2_app_app _ x y _ ?_
  have hu' : Part.some u ≤ Part.some r ⬝ Part.some x := by
    rw [papp_some_some]; exact some_le_of_mem hu
  have hw' : Part.some w ≤ Part.some s ⬝ Part.some y := by
    rw [papp_some_some]; exact some_le_of_mem hw
  have hmono : (Part.some (PCA.pairComb A) ⬝ Part.some u) ⬝ Part.some w
      ≤ (Part.some (PCA.pairComb A) ⬝ (Part.some r ⬝ Part.some x))
        ⬝ (Part.some s ⬝ Part.some y) :=
    papp_mono (papp_mono le_rfl hu') hw'
  have hmem : PCA.pairEl u w ∈
      (Part.some (PCA.pairComb A) ⬝ (Part.some r ⬝ Part.some x)) ⬝ (Part.some s ⬝ Part.some y) := by
    refine hmono _ ?_
    rw [PCA.pairComb_app]
    exact Part.mem_some _
  simpa [Expr.eval, Function.update_of_ne] using hmem

/-! ### The equalizer relation -/

variable {E F G : ERel.{u, v} A}

/-- The base of the equalizer: the points where the two maps are related, a realizer being the
pair of a realizer of the point and of a proof that they are. -/
def eqBaseAsm (f g : Pre E F) : Assembly.{u, v} A where
  carrier := {x : E.base.carrier // ∃ b, F.Prf b (f.toFun x) (g.toFun x)}
  realizes c x := ∃ a b, E.base.realizes a x.1 ∧ F.Prf b (f.toFun x.1) (g.toFun x.1) ∧
    c = PCA.pairEl a b
  exists_realizer x := by
    obtain ⟨a, ha⟩ := E.base.exists_realizer x.1
    obtain ⟨b, hb⟩ := x.2
    exact ⟨PCA.pairEl a b, a, b, ha, hb, rfl⟩

/-- The **equalizer** of two pre-morphisms: the relation inherited from `E`, its proofs carrying
in addition a witness at each endpoint that the two maps agree there. -/
def eqObj (f g : Pre E F) : ERel.{u, v} A where
  base := eqBaseAsm f g
  Prf w x y := ∃ u b c, E.Prf u x.1 y.1 ∧ F.Prf b (f.toFun x.1) (g.toFun x.1) ∧
    F.Prf c (f.toFun y.1) (g.toFun y.1) ∧ w = PCA.pairEl u (PCA.pairEl b c)
  ends := by
    obtain ⟨tE, htE⟩ := E.ends
    obtain ⟨q₁, hq₁⟩ := exists_pairOf (PCA.comp (PCA.fstComb A) (PCA.comp tE (PCA.fstComb A)))
      (PCA.comp (PCA.fstComb A) (PCA.sndComb A))
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.comp (PCA.sndComb A) (PCA.comp tE (PCA.fstComb A)))
      (PCA.comp (PCA.sndComb A) (PCA.sndComb A))
    obtain ⟨qq, hqq⟩ := exists_pairOf q₁ q₂
    refine ⟨qq, fun w x y h => ?_⟩
    obtain ⟨u, b, c, hu, hb, hc, rfl⟩ := h
    obtain ⟨vE, hvE, a₁, a₂, ha₁, ha₂, rfl⟩ := htE u x.1 y.1 hu
    have hE : PCA.pairEl a₁ a₂ ∈
        PCA.app (PCA.comp tE (PCA.fstComb A)) (PCA.pairEl u (PCA.pairEl b c)) :=
      mem_comp (mem_fstComb _ _) hvE
    have hbc : PCA.pairEl b c ∈ PCA.app (PCA.sndComb A) (PCA.pairEl u (PCA.pairEl b c)) :=
      mem_sndComb _ _
    exact ⟨PCA.pairEl (PCA.pairEl a₁ b) (PCA.pairEl a₂ c),
      hqq _ _ _
        (hq₁ _ _ _ (mem_comp hE (mem_fstComb a₁ a₂)) (mem_comp hbc (mem_fstComb b c)))
        (hq₂ _ _ _ (mem_comp hE (mem_sndComb a₁ a₂)) (mem_comp hbc (mem_sndComb b c))),
      _, _, ⟨a₁, b, ha₁, hb, rfl⟩, ⟨a₂, c, ha₂, hc, rfl⟩, rfl⟩
  refl' := by
    obtain ⟨rE, hrE⟩ := E.refl'
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.sndComb A) (PCA.sndComb A)
    obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.comp rE (PCA.fstComb A)) q₂
    refine ⟨qq, fun c x hc => ?_⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := hc
    obtain ⟨u, hu, hux⟩ := hrE a x.1 ha
    exact ⟨PCA.pairEl u (PCA.pairEl b b),
      hqq _ _ _ (mem_comp (mem_fstComb a b) hu)
        (hq₂ _ _ _ (mem_sndComb a b) (mem_sndComb a b)),
      u, b, b, hux, hb, hb, rfl⟩
  symm' := by
    obtain ⟨sE, hsE⟩ := E.symm'
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.comp (PCA.sndComb A) (PCA.sndComb A))
      (PCA.comp (PCA.fstComb A) (PCA.sndComb A))
    obtain ⟨qq, hqq⟩ := exists_pairOf (PCA.comp sE (PCA.fstComb A)) q₂
    refine ⟨qq, fun w x y h => ?_⟩
    obtain ⟨u, b, c, hu, hb, hc, rfl⟩ := h
    obtain ⟨u', hu', hux⟩ := hsE u x.1 y.1 hu
    exact ⟨PCA.pairEl u' (PCA.pairEl c b),
      hqq _ _ _ (mem_comp (mem_fstComb _ _) hu')
        (hq₂ _ _ _ (mem_comp (mem_sndComb _ _) (mem_sndComb b c))
          (mem_comp (mem_sndComb _ _) (mem_fstComb b c))),
      u', c, b, hux, hc, hb, rfl⟩
  trans' := by
    obtain ⟨tE, htE⟩ := E.trans'
    obtain ⟨t₂, ht₂⟩ := exists_binOf (PCA.fstComb A) (PCA.sndComb A)
    obtain ⟨qq, hqq⟩ := exists_binPair tE t₂
    refine ⟨qq, fun w w' x y z hw hw' => ?_⟩
    obtain ⟨u, b, c, hu, hb, _, rfl⟩ := hw
    obtain ⟨u', b', c', hu', _, hc', rfl⟩ := hw'
    obtain ⟨v, hv, hvx⟩ := htE u u' x.1 y.1 z.1 hu hu'
    exact ⟨PCA.pairEl v (PCA.pairEl b c'),
      hqq u (PCA.pairEl b c) u' (PCA.pairEl b' c') v (PCA.pairEl b c') hv
        (ht₂ _ _ _ _ (mem_fstComb b c) (mem_sndComb b' c')),
      v, b, c', hvx, hb, hc', rfl⟩

/-! ### The fork -/

/-- The inclusion of the equalizer, as a pre-morphism. -/
def eqInclPre (f g : Pre E F) : Pre (eqObj f g) E where
  toFun x := x.1
  tracked := ⟨PCA.fstComb A, fun w x y h => by
    obtain ⟨u, b, c, hu, _, _, rfl⟩ := h
    exact ⟨u, mem_fstComb _ _, hu⟩⟩

/-- On the equalizer the two maps become homotopic: the second component of a realizer is a
proof that they agree. -/
theorem eqIncl_homotopic (f g : Pre E F) :
    Homotopic ((eqInclPre f g).comp f) ((eqInclPre f g).comp g) :=
  ⟨PCA.sndComb A, fun c x hc => by
    obtain ⟨a, b, _, hb, rfl⟩ := hc
    exact ⟨b, mem_sndComb _ _, hb⟩⟩

/-- The map into the equalizer induced by a pre-morphism on which the two maps are homotopic. -/
noncomputable def eqLiftPre {f g : Pre E F} {r : Pre G E} (h : Homotopic (r.comp f) (r.comp g)) :
    Pre G (eqObj f g) where
  toFun z := ⟨r.toFun z, by
    obtain ⟨t, ht⟩ := h
    obtain ⟨a, ha⟩ := G.base.exists_realizer z
    obtain ⟨v, _, hv⟩ := ht a z ha
    exact ⟨v, hv⟩⟩
  tracked := by
    obtain ⟨t, ht⟩ := h
    obtain ⟨cr, hcr⟩ := r.tracked
    obtain ⟨pF, hpF⟩ := G.exists_fstTracker
    obtain ⟨pS, hpS⟩ := G.exists_sndTracker
    obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.comp t pF) (PCA.comp t pS)
    obtain ⟨qq, hqq⟩ := exists_pairOf cr q₂
    refine ⟨qq, fun a z z' hz => ?_⟩
    obtain ⟨u, hu, hux⟩ := hcr a z z' hz
    obtain ⟨e₁, he₁, hz₁⟩ := hpF a z z' hz
    obtain ⟨e₂, he₂, hz₂⟩ := hpS a z z' hz
    obtain ⟨b, hb, hbx⟩ := ht e₁ z hz₁
    obtain ⟨c, hc, hcx⟩ := ht e₂ z' hz₂
    exact ⟨PCA.pairEl u (PCA.pairEl b c),
      hqq _ _ _ hu (hq₂ _ _ _ (mem_comp he₁ hb) (mem_comp he₂ hc)),
      u, b, c, hux, hbx, hcx, rfl⟩

theorem eqLiftPre_comp {f g : Pre E F} {r : Pre G E} (h : Homotopic (r.comp f) (r.comp g)) :
    (eqLiftPre h).comp (eqInclPre f g) = r := Pre.ext rfl

/-- A map into the equalizer is determined, up to homotopy, by its composite with the
inclusion. -/
theorem eqLift_uniq {f g : Pre E F} {r : Pre G E} (h : Homotopic (r.comp f) (r.comp g))
    (m : Pre G (eqObj f g)) (hm : Homotopic (m.comp (eqInclPre f g)) r) :
    Homotopic m (eqLiftPre h) := by
  obtain ⟨t', ht'⟩ := hm
  obtain ⟨t, ht⟩ := h
  obtain ⟨rm, hrm⟩ := m.trackedBase
  obtain ⟨q₂, hq₂⟩ := exists_pairOf (PCA.comp (PCA.sndComb A) rm) t
  obtain ⟨qq, hqq⟩ := exists_pairOf t' q₂
  refine ⟨qq, fun a z ha => ?_⟩
  obtain ⟨u, hu, hux⟩ := ht' a z ha
  obtain ⟨v, hv, hvx⟩ := hrm a z ha
  obtain ⟨a', b, _, hb, rfl⟩ := hvx
  obtain ⟨c, hc, hcx⟩ := ht a z ha
  exact ⟨PCA.pairEl u (PCA.pairEl b c),
    hqq _ _ _ hu (hq₂ _ _ _ (mem_comp hv (mem_sndComb a' b)) hc),
    u, b, c, hux, hb, hcx, rfl⟩

/-! ### The equalizer in the completion -/

/-- A representative of a morphism of the completion. -/
noncomputable def repr (h : E ⟶ F) : Pre E F := Quotient.out h

@[simp] theorem homOf_repr (h : E ⟶ F) : homOf (repr h) = h := Quotient.out_eq h

/-- The fork given by the equalizer relation. -/
noncomputable def eqFork (f g : Pre E F) : Fork (homOf f) (homOf g) :=
  Fork.ofι (homOf (eqInclPre f g)) (homOf_eq_iff.2 (eqIncl_homotopic f g))

@[simp] theorem eqFork_ι (f g : Pre E F) :
    Fork.ι (eqFork f g) = homOf (eqInclPre f g) := rfl

/-- The condition of a fork, read on a representative of its leg. -/
theorem homotopic_of_fork (f g : Pre E F) (s : Fork (homOf f) (homOf g)) :
    Homotopic ((repr (Fork.ι s)).comp f) ((repr (Fork.ι s)).comp g) := by
  have h : homOf (repr (Fork.ι s)) ≫ homOf f = homOf (repr (Fork.ι s)) ≫ homOf g := by
    rw [homOf_repr]
    exact s.condition
  exact homOf_eq_iff.1 h

/-- **The equalizer relation really is an equalizer.** -/
noncomputable def eqForkIsLimit (f g : Pre E F) : IsLimit (eqFork f g) :=
  Fork.IsLimit.mk _
    (fun s => homOf (eqLiftPre (homotopic_of_fork f g s)))
    (fun s => by
      have h : homOf ((eqLiftPre (homotopic_of_fork f g s)).comp (eqInclPre f g))
          = homOf (repr (Fork.ι s)) :=
        congrArg homOf (eqLiftPre_comp _)
      rw [homOf_repr] at h
      exact h)
    (fun s m hm => by
      obtain ⟨r', rfl⟩ := homOf_surjective m
      have hm' : Homotopic (r'.comp (eqInclPre f g)) (repr (Fork.ι s)) := by
        refine homOf_eq_iff.1 ?_
        rw [homOf_repr]
        exact hm
      exact homOf_eq_iff.2 (eqLift_uniq _ r' hm'))

instance hasEqualizer_homOf (f g : Pre E F) : HasEqualizer (homOf f) (homOf g) :=
  ⟨⟨⟨eqFork f g, eqForkIsLimit f g⟩⟩⟩

instance hasEqualizer' (f g : E ⟶ F) : HasEqualizer f g := by
  obtain ⟨p, rfl⟩ := homOf_surjective f
  obtain ⟨q, rfl⟩ := homOf_surjective g
  infer_instance

instance instHasEqualizers : HasEqualizers (ERel.{u, v} A) :=
  hasEqualizers_of_hasLimit_parallelPair _

/-- **The exact completion of the assemblies has all finite limits.** -/
instance instHasFiniteLimits : HasFiniteLimits (ERel.{u, v} A) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end ExReg

end Realizability
