/-
**Measures for the product premise of route (iii)** (M29-EP-IMPREDICATIVE, round 5).

Round 4 reduced expansion postponement in every corner of the cube to `HSubstPi (cubeSpec f)`
(`Start/PTSExpansionHSubstSN.lean`).  This module records what is proved about the three
candidate measures for that hypothesis.

* `HSubstSort P` — hereditary substitution, at depth, into a canonical judgement whose type is a
  **sort** (the first stage of the level-stratified measure (c)).
* `hsubstPi_of_hsubstSort` and `hsubstSort_of_hsubstPi`: **`HSubstPi ↔ HSubstSort`** in every
  corner (`hsubstPi_iff_hsubstSort`).  So the first stage of (c) is not a weakening of the
  target: it is the target, and `cube_expansionPostponement_of_hsubstSort` follows.
* `HasTypeNW.not_lam_of_sort`: a canonical judgement whose type is a sort never has an
  abstraction as subject (the top of every sort-typed premise is a product, a sort or a neutral
  term).
* Measure (b), unrestricted: `UpDown P Γ` is "a one-step reduct, an immediate subterm, or a type
  (in `HasType`) of".  `lambdaP2_upDown_not_acc`: in λP2 the variable `t : P` in the context
  `P : ∗, t : P` is **not accessible** — `t` has the type `(λu:P. P) t` (by conversion), and `t`
  is an immediate subterm of that type.  So the order of (b) is only a candidate when "is the type
  of" is restricted to *canonical* (normal) types; with conversion it has a 2-cycle.
-/

import Start.PTSExpansionHSubstSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- **Hereditary substitution into sort-typed premises** (stage 1 of measure (c)): substituting a
canonical `N : A` at depth `Δ` into a canonical judgement `M : s` (`s` a sort), into a canonically
valid target context, gives after reduction a canonical judgement of the same sort. -/
def HSubstSort (P : Specification Srt) : Prop :=
  ∀ {Γ : List (Expr Srt)} {N A : Expr Srt} {Δ Δ' : List (Expr Srt)} {M : Expr Srt} {s : Srt},
    HasTypeNW P Γ N A → CtxSubstRed N Δ Δ' → ValidContextNW P (Δ' ++ Γ) →
    HasTypeNW P (Δ ++ A :: Γ) M (.sort s) →
    ∃ M', Reduces (M.subst (Expr.substAt N Δ.length)) M' ∧ HasTypeNW P (Δ' ++ Γ) M' (.sort s)

/-- `HSubstSort` gives `HSubstPi`: a product premise is a sort-typed premise, and reducts of a
product are products. -/
theorem hsubstPi_of_hsubstSort {P : Specification Srt} (h : HSubstSort P) : HSubstPi P := by
  intro Γ N A Δ Δ' C E s hN hc hv hP
  obtain ⟨M', hr, hM'⟩ := h hN hc hv hP
  simp only [Expr.subst] at hr
  obtain ⟨C', E', rfl, hC, hE⟩ := Reduces.pi_inv hr
  refine ⟨C', E', hC, ?_, hM'⟩
  first | exact hE | (rw [Expr.substAt_succ]; exact hE)

/-- Conversely, in every corner of the cube, `HSubstPi` gives `HSubstSort`, by route (iii) at the
root `M[N]` (which is typed, hence strongly normalizing). -/
theorem hsubstSort_of_hsubstPi (f : CubeFeatures) (hpi : HSubstPi (cubeSpec f)) :
    HSubstSort (cubeSpec f) := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  have hT := HasType.subst_at (Δ := Δ) hN.toHasType hM.toHasType
  have hsn : StronglyNormalizing (M.subst (Expr.substAt N Δ.length)) :=
    cube_stronglyNormalizing f _ hT.valid _ ⟨_, .inl hT⟩
  have hb : Expr.Below (M.subst (Expr.substAt N Δ.length))
      (M.subst (Expr.substAt N Δ.length)) := ⟨id, by rw [Expr.rename_id]⟩
  obtain ⟨M', B', h1, h2, h3⟩ :=
    hsubst_route3_aux f hpi _ (Expr.acc_desc_of_sn hsn) hN hM Δ Δ' rfl hc hv hb
  simp only [Expr.subst] at h2
  rw [Reduces.sort_eq h2] at h3
  exact ⟨M', h1, h3⟩

/-- **The first stage of the level-stratified measure is the whole problem**: in every corner of
the cube, hereditary substitution into product premises is equivalent to hereditary substitution
into all sort-typed premises. -/
theorem hsubstPi_iff_hsubstSort (f : CubeFeatures) :
    HSubstPi (cubeSpec f) ↔ HSubstSort (cubeSpec f) :=
  ⟨hsubstSort_of_hsubstPi f, hsubstPi_of_hsubstSort⟩

/-- Expansion postponement in every corner of the cube, from stage 1 of measure (c). -/
theorem cube_expansionPostponement_of_hsubstSort (f : CubeFeatures)
    (h : HSubstSort (cubeSpec f)) :
    ProductNormalizationR (cubeSpec f) ∧ ExpansionPostponement (cubeSpec f) :=
  cube_expansionPostponement_of_hsubstPi f (hsubstPi_of_hsubstSort h)

/-- A canonical judgement whose type is a sort never has an abstraction as subject. -/
theorem HasTypeNW.not_lam_of_sort {P : Specification Srt} {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : HasTypeNW P Γ M T) {s : Srt} (hT : T = .sort s) : ∀ C b, M ≠ .lam C b := by
  induction h with
  | ax _ => intro C b hc; cases hc
  | var _ _ => intro C b hc; cases hc
  | @weaken Θ₀ M₀ B₀ A₀ s₀ hM hA ihM ihA =>
      intro C b hc
      have hB₀ : B₀ = .sort s := by
        cases B₀ <;> simp_all [Expr.rename]
      cases M₀ with
      | lam C₀ b₀ => exact ihM hB₀ C₀ b₀ rfl
      | _ => simp [Expr.rename] at hc
  | product _ _ _ _ _ => intro C b hc; cases hc
  | abstraction _ _ _ _ => cases hT
  | application _ _ _ _ _ _ _ => intro C b hc; cases hc

/-! ### Measure (b) without canonical types has a cycle -/

/-- One step of measure (b): `x` is a one-step reduct of `y`, an immediate subterm of `y`, or a
type of `y` in context `Γ` (in the full system `HasType`, with conversion). -/
def UpDown (P : Specification Srt) (Γ : List (Expr Srt)) (x y : Expr Srt) : Prop :=
  Expr.DescStep x y ∨ HasType P Γ y x

/-- An accessible element is not related to itself. -/
theorem acc_irrefl {α : Type} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hxx => ih x hxx hxx

/-- The context `P : ∗, t : P` (de Bruijn: `t` is `var 0`, `P` is `var 1`). -/
def cycleCtx : List (Expr Srt) := [.var 0, .sort .star]

/-- The type `(λu:P. P) t`, convertible to `P`, which contains `t`. -/
def cycleType : Expr Srt := .app (.lam (.var 1) (.var 2)) (.var 0)

theorem cycleType_hasType :
    HasType (cubeSpec lambdaP2) cycleCtx cycleType (.sort .star) := by
  have hstar : HasType (cubeSpec lambdaP2) ([]) (.sort .star) (.sort .box) := .ax ⟨rfl, rfl⟩
  -- `P : ∗ ⊢ P : ∗`
  have hP : HasType (cubeSpec lambdaP2) ([Expr.sort Srt.star] : List (Expr Srt)) (.var 0) (.sort .star) := hstar.var
  -- `P : ∗, t : P ⊢ P : ∗`
  have hP1 : HasType (cubeSpec lambdaP2) cycleCtx (.var 1) (.sort .star) := hP.weaken hP
  -- `P : ∗, t : P, u : P ⊢ P : ∗`
  have hP2 : HasType (cubeSpec lambdaP2) (.var 1 :: cycleCtx) (.var 2) (.sort .star) :=
    hP1.weaken hP1
  have hstar1 : HasType (cubeSpec lambdaP2) ([Expr.sort Srt.star] : List (Expr Srt)) (.sort .star) (.sort .box) :=
    hstar.weaken hstar
  have hstar2 : HasType (cubeSpec lambdaP2) cycleCtx (.sort .star) (.sort .box) :=
    hstar1.weaken hP
  have hstar3 : HasType (cubeSpec lambdaP2) (.var 1 :: cycleCtx) (.sort .star) (.sort .box) :=
    hstar2.weaken hP1
  have hpi : HasType (cubeSpec lambdaP2) cycleCtx (.pi (.var 1) (.sort .star)) (.sort .box) :=
    .product hP1 hstar3 ⟨rfl, rfl⟩
  have hlam : HasType (cubeSpec lambdaP2) cycleCtx (.lam (.var 1) (.var 2))
      (.pi (.var 1) (.sort .star)) := .abstraction hP2 hpi
  have ht : HasType (cubeSpec lambdaP2) cycleCtx (.var 0) (.var 1) := hP.var
  exact .application hlam ht

/-- `t : (λu:P. P) t` in λP2, by conversion. -/
theorem cycle_var_hasType : HasType (cubeSpec lambdaP2) cycleCtx (.var 0) cycleType := by
  have hstar : HasType (cubeSpec lambdaP2) ([]) (.sort .star) (.sort .box) := .ax ⟨rfl, rfl⟩
  have hP : HasType (cubeSpec lambdaP2) ([Expr.sort Srt.star] : List (Expr Srt)) (.var 0) (.sort .star) := hstar.var
  have ht : HasType (cubeSpec lambdaP2) cycleCtx (.var 0) (.var 1) := hP.var
  refine .conversion ht cycleType_hasType ?_
  exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (Beta.head _ _ _))

/-- **Measure (b) needs canonical types**: in λP2, with "is a type of" read in the full system
(with conversion), the order "reduct, immediate subterm or type of" has the 2-cycle
`t ⟶ (λu:P. P) t ⟶ t`, so `t` is not accessible. -/
theorem lambdaP2_upDown_not_acc :
    ¬ Acc (Relation.TransGen (UpDown (cubeSpec lambdaP2) cycleCtx)) (.var 0) := by
  intro h
  refine acc_irrefl h ?_
  refine Relation.TransGen.head (b := cycleType) ?_ (.single ?_)
  · exact .inl (.inr (.app_right _ _))
  · exact .inr cycle_var_hasType

end PureTypeSystem
