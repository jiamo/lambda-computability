import Start.PTSLambdaPi

/-!
# The lambda cube as one parameterized family of pure type systems

This module is this library's own (task `M23-PTS`).  It instantiates the pure type system
framework absorbed from github.com/openai/math (`Start/PTSBasic.lean`, `Start/PTSTyping.lean`;
see `NOTICE`) with Barendregt's lambda cube.

* `PureTypeSystem.CubeFeatures` — which of the three optional product rules `(□,∗)`
  (polymorphism), `(□,□)` (type operators) and `(∗,□)` (dependent types) are present; the rule
  `(∗,∗)` is always present.
* `PureTypeSystem.cubeSpec f` — the specification over the sorts `∗ : □` (reusing the sorts
  `LambdaPi.Srt` of the library's `λΠ`) with product rules `(s₁,s₂,s₂)` for the enabled pairs.
* The eight corners `lambdaArrow`, `systemF`, `lambdaOmegaBar`, `systemFOmega`, `lambdaP`,
  `lambdaP2`, `lambdaPOmegaBar`, `coc` as values of `CubeFeatures`.
* `PureTypeSystem.HasType.mono` — a generic simulation of derivations along an inclusion of
  specifications, and `cube_inclusion` — **adding product rules is an inclusion of typing
  derivations**; strong normalization is inherited downwards (`cube_sn_mono`).
* Instance facts: the cube is functional (`cube_axioms_functional`, `cube_rule_functional`),
  `□` has no type (`not_hasType_box`), the sort `∗` is not a type of itself
  (`not_hasType_star_star`).
* `lambdaPiSpec_eq_cube` — the existing `λΠ` system is literally the `λP` corner, so every
  `λP`-corner derivation translates to a `LambdaPi.Typing` derivation (`cube_lambdaP_toTyping`)
  and the `λP` and `λ→` corners are strongly normalizing (`cube_lambdaP_sn`, `cube_lambdaArrow_sn`)
  by the independent proof `Start/LambdaPiSN.lean`.
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- Which optional product rules of the lambda cube are present. -/
@[ext] structure CubeFeatures where
  /-- `(□,∗)`: terms depending on types (polymorphism, System F). -/
  poly : Bool
  /-- `(□,□)`: types depending on types (type operators). -/
  ops : Bool
  /-- `(∗,□)`: types depending on terms (dependent types). -/
  dep : Bool
  deriving DecidableEq

namespace CubeFeatures

/-- Whether the product rule `(s₁, s₂)` is enabled. -/
def allows (f : CubeFeatures) : Srt → Srt → Prop
  | .star, .star => True
  | .box, .star => f.poly = true
  | .box, .box => f.ops = true
  | .star, .box => f.dep = true

/-- Feature inclusion: every rule enabled in `f` is enabled in `g`. -/
def Le (f g : CubeFeatures) : Prop :=
  (f.poly = true → g.poly = true) ∧ (f.ops = true → g.ops = true) ∧
    (f.dep = true → g.dep = true)

instance : LE CubeFeatures := ⟨Le⟩

theorem allows_mono {f g : CubeFeatures} (h : f ≤ g) {s₁ s₂ : Srt} (hs : f.allows s₁ s₂) :
    g.allows s₁ s₂ := by
  obtain ⟨hp, ho, hd⟩ := h
  cases s₁ <;> cases s₂ <;> simp_all [allows]

theorem le_refl (f : CubeFeatures) : f ≤ f := ⟨id, id, id⟩

theorem le_trans {f g h : CubeFeatures} (h₁ : f ≤ g) (h₂ : g ≤ h) : f ≤ h :=
  ⟨fun x => h₂.1 (h₁.1 x), fun x => h₂.2.1 (h₁.2.1 x), fun x => h₂.2.2 (h₁.2.2 x)⟩

end CubeFeatures

/-- The eight corners of the lambda cube. -/
def lambdaArrow : CubeFeatures := ⟨false, false, false⟩
def systemF : CubeFeatures := ⟨true, false, false⟩
def lambdaOmegaBar : CubeFeatures := ⟨false, true, false⟩
def systemFOmega : CubeFeatures := ⟨true, true, false⟩
def lambdaP : CubeFeatures := ⟨false, false, true⟩
def lambdaP2 : CubeFeatures := ⟨true, false, true⟩
def lambdaPOmegaBar : CubeFeatures := ⟨false, true, true⟩
/-- The Calculus of Constructions. -/
def coc : CubeFeatures := ⟨true, true, true⟩

/-- Every corner lies below the Calculus of Constructions, and above `λ→`. -/
theorem le_coc (f : CubeFeatures) : f ≤ coc := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

theorem lambdaArrow_le (f : CubeFeatures) : lambdaArrow ≤ f :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-- The cube specification: axiom `∗ : □` and product rules `(s₁, s₂, s₂)` for the enabled
pairs. -/
def cubeSpec (f : CubeFeatures) : Specification Srt where
  axioms s t := s = Srt.star ∧ t = Srt.box
  rule s₁ s₂ s₃ := s₃ = s₂ ∧ f.allows s₁ s₂

/-! ### Simulation of derivations along an inclusion of specifications -/

section Mono

universe u

variable {S : Type u}

/-- An inclusion of specifications: every axiom and rule of `P` is one of `Q`. -/
def Specification.Le (P Q : Specification S) : Prop :=
  (∀ s t, P.axioms s t → Q.axioms s t) ∧ (∀ s₁ s₂ s₃, P.rule s₁ s₂ s₃ → Q.rule s₁ s₂ s₃)

/-- Derivations are simulated along an inclusion of specifications (same terms, same types). -/
theorem HasType.mono {P Q : Specification S} (hPQ : P.Le Q) {Γ : List (Expr S)}
    {M A : Expr S} (h : HasType P Γ M A) : HasType Q Γ M A := by
  induction h with
  | ax h => exact .ax (hPQ.1 _ _ h)
  | var _ ih => exact .var ih
  | weaken _ _ ih₁ ih₂ => exact .weaken ih₁ ih₂
  | product _ _ hr ih₁ ih₂ => exact .product ih₁ ih₂ (hPQ.2 _ _ _ hr)
  | abstraction _ _ ih₁ ih₂ => exact .abstraction ih₁ ih₂
  | application _ _ ih₁ ih₂ => exact .application ih₁ ih₂
  | conversion _ _ hc ih₁ ih₂ => exact .conversion ih₁ ih₂ hc

theorem ValidContext.mono {P Q : Specification S} (hPQ : P.Le Q) {Γ : List (Expr S)}
    (h : ValidContext P Γ) : ValidContext Q Γ := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih (hA.mono hPQ)

theorem Legal.mono {P Q : Specification S} (hPQ : P.Le Q) {Γ : List (Expr S)} {M : Expr S}
    (h : Legal P Γ M) : Legal Q Γ M := by
  obtain ⟨A, h | h⟩ := h
  · exact ⟨A, .inl (h.mono hPQ)⟩
  · exact ⟨A, .inr (h.mono hPQ)⟩

/-- Strong normalization is inherited by subsystems. -/
theorem SystemStronglyNormalizing.mono {P Q : Specification S} (hPQ : P.Le Q)
    (h : SystemStronglyNormalizing Q) : SystemStronglyNormalizing P :=
  fun Γ hΓ M hM => h Γ (hΓ.mono hPQ) M (hM.mono hPQ)

/-- Weak normalization is inherited by subsystems. -/
theorem SystemWeaklyNormalizing.mono {P Q : Specification S} (hPQ : P.Le Q)
    (h : SystemWeaklyNormalizing Q) : SystemWeaklyNormalizing P :=
  fun Γ hΓ M hM => h Γ (hΓ.mono hPQ) M (hM.mono hPQ)

end Mono

/-- Adding product rules is an inclusion of specifications. -/
theorem cubeSpec_le {f g : CubeFeatures} (h : f ≤ g) : (cubeSpec f).Le (cubeSpec g) :=
  ⟨fun _ _ h => h, fun _ _ _ ⟨h₁, h₂⟩ => ⟨h₁, CubeFeatures.allows_mono h h₂⟩⟩

/-- **The inclusions of the cube**: a derivation in a corner is a derivation in every corner
with more product rules. -/
theorem cube_inclusion {f g : CubeFeatures} (h : f ≤ g) {Γ : List (Expr Srt)} {M A : Expr Srt}
    (hM : HasType (cubeSpec f) Γ M A) : HasType (cubeSpec g) Γ M A :=
  hM.mono (cubeSpec_le h)

/-- Strong normalization descends along the cube's inclusions. -/
theorem cube_sn_mono {f g : CubeFeatures} (h : f ≤ g)
    (hg : SystemStronglyNormalizing (cubeSpec g)) : SystemStronglyNormalizing (cubeSpec f) :=
  hg.mono (cubeSpec_le h)

/-! ### Facts about the cube instances -/

theorem cube_axioms_functional (f : CubeFeatures) {s t t' : Srt}
    (h : (cubeSpec f).axioms s t) (h' : (cubeSpec f).axioms s t') : t = t' :=
  h.2.trans h'.2.symm

theorem cube_rule_functional (f : CubeFeatures) {s₁ s₂ s₃ s₃' : Srt}
    (h : (cubeSpec f).rule s₁ s₂ s₃) (h' : (cubeSpec f).rule s₁ s₂ s₃') : s₃ = s₃' :=
  h.1.trans h'.1.symm

/-- The sort `□` has no type in any corner. -/
theorem not_hasType_box (f : CubeFeatures) {Γ : List (Expr Srt)} {T : Expr Srt} :
    ¬ HasType (cubeSpec f) Γ (.sort .box) T := by
  intro h
  have := HasType.generation h
  obtain ⟨t, ⟨h₁, _⟩, _⟩ := this
  cases h₁

/-- The sort `∗` is not of type `∗` (as it is in the inconsistent system `∗ : ∗`). -/
theorem not_hasType_star_star (f : CubeFeatures) {Γ : List (Expr Srt)} :
    ¬ HasType (cubeSpec f) Γ (.sort .star) (.sort .star) := by
  intro h
  obtain ⟨t, ⟨_, rfl⟩, hc⟩ := HasType.generation h
  exact absurd (Converts.sort_inj hc) (by decide)

/-- In every valid context, `∗ : □`. -/
theorem cube_star_box (f : CubeFeatures) {Γ : List (Expr Srt)}
    (hΓ : ValidContext (cubeSpec f) Γ) : HasType (cubeSpec f) Γ (.sort .star) (.sort .box) :=
  HasType.sort_of_valid hΓ ⟨rfl, rfl⟩

/-! ### The `λP` corner is the library's `λΠ` -/

/-- **`λΠ` is the `λP` corner of the cube**: the two specifications are equal. -/
theorem lambdaPiSpec_eq_cube : lambdaPiSpec = cubeSpec lambdaP := by
  unfold lambdaPiSpec cubeSpec
  congr
  funext s₁ s₂ s₃
  apply propext
  cases s₁ <;> cases s₂ <;>
    simp [lambdaP, CubeFeatures.allows, and_comm]

/-- Every derivation of the `λP` corner is a derivation of the library's `λΠ`
(`Start/LambdaPiTyping.lean`). -/
theorem cube_lambdaP_toTyping {Γ : List (Expr Srt)} {M A : Expr Srt}
    (h : HasType (cubeSpec lambdaP) Γ M A) :
    LambdaPi.Typing (Γ.map toTm) (toTm M) (toTm A) := by
  rw [← lambdaPiSpec_eq_cube] at h
  exact h.toTyping

/-- The `λP` corner is strongly normalizing (from the independent `Start/LambdaPiSN.lean`). -/
theorem cube_lambdaP_sn : SystemStronglyNormalizing (cubeSpec lambdaP) := by
  rw [← lambdaPiSpec_eq_cube]
  exact lambdaPi_systemStronglyNormalizing

/-- The simply typed corner `λ→` is strongly normalizing, as a subsystem of `λP`. -/
theorem cube_lambdaArrow_sn : SystemStronglyNormalizing (cubeSpec lambdaArrow) :=
  cube_sn_mono (lambdaArrow_le lambdaP) cube_lambdaP_sn

end PureTypeSystem
