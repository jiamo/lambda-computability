import Start.PTSExpansionCoC
import Start.PTSExpansionPoll
import Start.PTSRestriction
import Start.PTSExpansionLevels
import Start.PTSExpansionSNGeneric

/-!
# Series V, round 1, part C: specifications with a morphism into coc (row M29-EP-COC-MORPHISM)

* `CoCMorphism P` — a map `φ` from the sorts of `P` to the sorts of `cubeSpec coc` sending axioms
  to axioms and rules to rules (so `φ s₃ = φ s₂` for every rule, `CoCMorphism.rule_eq`);
* `CoCMorphism.hasType`, `CoCMorphism.validContext` — transport of derivations along `φ`
  (through `HasType.mapSort`);
* `CoCMorphism.stronglyNormalizing` — every such `P` is strongly normalizing (pulled back from
  `coc_stronglyNormalizing` by `StronglyNormalizing.of_mapSort`);
* `CoCMorphism.expansionPostponement_iff_productNormalizationR` — so for every such `P`,
  expansion postponement is equivalent to `ProductNormalizationR P`;
* instances: `CoCMorphism.cube f` (the eight corners, `φ = id`) and `cocBox2_cocMorphism` for
  `cocBox2`, the calculus of constructions with a second kind sort `□'` (`∗ : □`, `∗ : □'`, all
  rules `(s₁, s₂, s₂)`), which is not functional (`cocBox2_not_functional`), not stratified
  (`cocBox2_not_stratified`) and strongly normalizing (`cocBox2_in_class`).

* `CoCMorphism.expansionPostponement_of_sortFundamental` — for every such `P`, expansion
  postponement follows from the sort-typed fundamental lemma of route (ii) alone (routes (iii) and
  the product-normalization step are generic, `Start/PTSExpansionSNGeneric.lean`).

The target `expansionPostponement_of_cocMorphism` is **not** proved here; its first missing lemma
is the route (ii) fundamental lemma for `P`,
`sortFundamental_of_cocMorphism (m : CoCMorphism P) : SNGeneric.SortFundamental P`
(see `docs/goal/evidence/M29-EP.md`, "Series V, round 1").
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- **A morphism of specifications into the calculus of constructions.** -/
structure CoCMorphism {S : Type} (P : Specification S) where
  φ : S → Srt
  axiom_map : ∀ s t, P.axioms s t → (cubeSpec coc).axioms (φ s) (φ t)
  rule_map : ∀ a b c, P.rule a b c → (cubeSpec coc).rule (φ a) (φ b) (φ c)

namespace CoCMorphism

variable {S : Type} {P : Specification S} (m : CoCMorphism P)
include m

/-- Rules are sent to rules of coc, whose third sort is the second. -/
theorem rule_eq {a b c : S} (h : P.rule a b c) : m.φ c = m.φ b := (m.rule_map a b c h).1

/-- Axioms are sent to `∗ : □`. -/
theorem axiom_eq {s t : S} (h : P.axioms s t) : m.φ s = Srt.star ∧ m.φ t = Srt.box :=
  m.axiom_map s t h

/-- Transport of derivations along the morphism. -/
theorem hasType {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    HasType (cubeSpec coc) (Γ.map (Expr.mapSort m.φ)) (M.mapSort m.φ) (A.mapSort m.φ) :=
  h.mapSort m.φ m.axiom_map m.rule_map

theorem validContext {Γ : List (Expr S)} (h : ValidContext P Γ) :
    ValidContext (cubeSpec coc) (Γ.map (Expr.mapSort m.φ)) := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih (m.hasType hA)

/-- **Every specification with a morphism into coc is strongly normalizing.** -/
theorem stronglyNormalizing : SystemStronglyNormalizing P := by
  intro Γ hΓ M hM
  obtain ⟨A, hA⟩ := hM
  apply StronglyNormalizing.of_mapSort m.φ
  apply coc_stronglyNormalizing _ (m.validContext hΓ)
  rcases hA with h | h
  · exact ⟨_, .inl (m.hasType h)⟩
  · exact ⟨_, .inr (m.hasType h)⟩

/-- For a specification with a morphism into coc, expansion postponement reduces to product
normalization of the reduction-only system. -/
theorem expansionPostponement_of_productNormalizationR (hpn : ProductNormalizationR P) :
    ExpansionPostponement P :=
  expansionPostponement_of_productNormalizationR_sn m.stronglyNormalizing hpn

/-- **Expansion postponement is equivalent to `ProductNormalizationR`** for every specification
with a morphism into coc. -/
theorem expansionPostponement_iff_productNormalizationR :
    ExpansionPostponement P ↔ ProductNormalizationR P :=
  ⟨productNormalizationR_of_expansionPostponement, m.expansionPostponement_of_productNormalizationR⟩

/-- **Expansion postponement from route (ii) alone**: for a specification with a morphism into
coc, the sort-typed fundamental lemma (`SNGeneric.SortFundamental`) is the only missing input;
routes (iii) and the reduction to product normalization hold for every strongly normalizing
specification (`SNGeneric.expansionPostponement_of_sortFundamental`). -/
theorem expansionPostponement_of_sortFundamental (h : SNGeneric.SortFundamental P) :
    ExpansionPostponement P :=
  SNGeneric.expansionPostponement_of_sortFundamental m.stronglyNormalizing h

end CoCMorphism

/-- The eight corners of the cube have a morphism (the identity) into coc. -/
def CoCMorphism.cube (f : CubeFeatures) : CoCMorphism (cubeSpec f) where
  φ := id
  axiom_map _ _ h := h
  rule_map a b c h := ⟨h.1, by cases a <;> cases b <;> trivial⟩

/-- For every corner of the cube, expansion postponement is equivalent to product normalization
through the morphism `CoCMorphism.cube` (both sides hold, by `cube_expansionPostponement_all`). -/
theorem cube_in_cocMorphism_class (f : CubeFeatures) :
    Nonempty (CoCMorphism (cubeSpec f)) ∧ ExpansionPostponement (cubeSpec f) ∧
      ProductNormalizationR (cubeSpec f) :=
  ⟨⟨CoCMorphism.cube f⟩, cube_expansionPostponement_all f,
    productNormalizationR_of_expansionPostponement (cube_expansionPostponement_all f)⟩

/-! ### A non-functional specification outside the cube -/

/-- Sorts of coc with a second kind sort. -/
inductive Srt2 where
  | star : Srt2
  | box : Srt2
  | box' : Srt2
  deriving DecidableEq, Repr

/-- The calculus of constructions with a second kind sort `□'`: axioms `∗ : □`, `∗ : □'`, and the
rules `(s₁, s₂, s₂)` for all sorts `s₁, s₂`. -/
def cocBox2 : Specification Srt2 where
  axioms s t := s = .star ∧ (t = .box ∨ t = .box')
  rule _ s₂ s₃ := s₃ = s₂

/-- The collapse `□' ↦ □`. -/
def collapse2 : Srt2 → Srt
  | .star => .star
  | .box => .box
  | .box' => .box

/-- `cocBox2` has a morphism into coc. -/
def cocBox2_cocMorphism : CoCMorphism cocBox2 where
  φ := collapse2
  axiom_map s t h := by
    obtain ⟨rfl, rfl | rfl⟩ := h <;> exact ⟨rfl, rfl⟩
  rule_map a b c h := ⟨by rw [show c = b from h], by cases a <;> cases b <;> trivial⟩

/-- `cocBox2` is not functional: `∗ : □` and `∗ : □'`. -/
theorem cocBox2_not_functional :
    ¬ ∀ s a b, cocBox2.axioms s a → cocBox2.axioms s b → a = b := by
  intro h
  have := h .star .box .box' ⟨rfl, Or.inl rfl⟩ ⟨rfl, Or.inr rfl⟩
  cases this

/-- `cocBox2` is not stratified (it has the dependent rule `(∗, □, □)`). -/
theorem cocBox2_not_stratified (L : Stratification cocBox2) : False :=
  not_stratified_of_dependent_rule (P := cocBox2) (s := .star) (t := .box) (r := .box)
    ⟨rfl, Or.inl rfl⟩ rfl L

/-- **`cocBox2` is in the class**: it has a morphism into coc, is not functional (hence outside
Barthe's injective class), is not stratified (outside Stage B), and is strongly normalizing. -/
theorem cocBox2_in_class : Nonempty (CoCMorphism cocBox2) ∧
    ¬ (∀ s a b, cocBox2.axioms s a → cocBox2.axioms s b → a = b) ∧
    ¬ Nonempty (Stratification cocBox2) ∧ SystemStronglyNormalizing cocBox2 :=
  ⟨⟨cocBox2_cocMorphism⟩, cocBox2_not_functional, fun ⟨L⟩ => cocBox2_not_stratified L,
    cocBox2_cocMorphism.stronglyNormalizing⟩

/-- For `cocBox2`, expansion postponement is equivalent to product normalization. -/
theorem cocBox2_expansionPostponement_iff :
    ExpansionPostponement cocBox2 ↔ ProductNormalizationR cocBox2 :=
  cocBox2_cocMorphism.expansionPostponement_iff_productNormalizationR

end PureTypeSystem
