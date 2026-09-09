/-
**Kleene's second algebra does not map back to the first.**

`Start/PCAMorphism.lean` builds the applicative morphism `Realizability.KleeneTwo.kOneToTwo`
from Kleene's first algebra `K₁` to Kleene's second algebra `K₂`: number realizability sits
inside function realizability.  This module shows that the inclusion cannot be reversed.

The unqualified statement — "there is no applicative morphism `K₂ → K₁`" — is *false*, and the
counterexample is recorded here: `Realizability.AppMorphism.trivialMor` is an applicative morphism
between any two partial combinatory algebras, obtained by letting *every* element of the target
represent *every* element of the source and taking a constant realizer.  A morphism is only
informative if the target can read something back off a representative, so the theorem has to
assume that much:

* `Realizability.KleeneTwo.SeparatesBits` — a morphism `K₂ → K₁` *separates bits* if a single
  partial recursive code tells the representatives of the constant function `0` from those of
  the constant function `1`;
* `Realizability.KleeneTwo.no_separatesBits_morphism` — **no applicative morphism `K₂ → K₁`
  separates bits.**  The projections `β ↦ β n` are continuous, hence are elements of `K₂`
  (`Realizability.KleeneTwo.projAssoc`), so a representative of `β` together with the realizer
  computes, for each `n`, a representative of the constant function `β n`; separating bits then
  reads `β n` back off it.  A representative of a `0/1`-valued `β` therefore determines `β`, and
  a set of naturals would be determined by a natural number, which Cantor's theorem forbids.
* `Realizability.KleeneTwo.no_readsNumerals_morphism` — the same for a morphism that reads back
  every numeral, and `Realizability.KleeneTwo.kOneToTwo_not_invertible`, the conclusion in the
  form the inclusion suggests.
-/

import Start.PCAMorphism

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Realizability

/-! ### The trivial morphism -/

/-- **The trivial applicative morphism** between any two partial combinatory algebras: every
element of the target represents every element of the source, and the realizer is the constant
function `λ x y. k`.  Its existence is the reason the theorems below have to assume that the
target can tell some representatives apart. -/
noncomputable def AppMorphism.trivialMor (A B : Type u) [PCA A] [PCA B] : AppMorphism A B where
  map _ _ := True
  map_nonempty _ := ⟨PCA.k, trivial⟩
  realizer := PCA.lam2 (Expr.const (PCA.k : B))
  realizer_dom b := by
    have h := PCA.lam2_app_dom (Expr.const (PCA.k : B)) b
    rwa [papp_some_some] at h
  realizer_app _ _ b b' _ _ _ _ := by
    refine ⟨PCA.k, trivial, ?_⟩
    exact PCA.lam2_app_app (Expr.const (PCA.k : B)) b b' _ (Part.mem_some _)

namespace KleeneTwo

open scoped Realizability.Kleene

/-! ### The projections, as elements of `K₂` -/

/-- The operation `β ↦ (the constant function `β n`)` on Baire space. -/
def projEl (n : ℕ) : (ℕ → ℕ) → ℕ → ℕ := fun β _ => β n

theorem cont_projEl (n : ℕ) : Cont (projEl n) := by
  intro β _
  refine ⟨n + 1, fun β' h => ?_⟩
  simp only [projEl, h n (by omega)]

/-- The element of `K₂` that returns the constant function with value `β n`. -/
noncomputable def projAssoc (n : ℕ) : ℕ → ℕ := detAssoc (projEl n)

theorem appK_projAssoc (n : ℕ) (β : ℕ → ℕ) :
    appK (projAssoc n) β = Part.some (natEl (β n)) :=
  appK_detAssoc (cont_projEl n) β

/-! ### Morphisms `K₂ → K₁` that read something back -/

/-- A morphism `K₂ → K₁` **separates bits** if one partial recursive code recovers `b` from
every representative of the constant function with value `b`, for `b = 0` and `b = 1`. -/
def SeparatesBits (δ : AppMorphism (ℕ → ℕ) ℕ) : Prop :=
  ∃ q : ℕ, ∀ b m : ℕ, b ≤ 1 → δ.map (natEl b) m → b ∈ Kleene.natApp q m

/-- A morphism `K₂ → K₁` **reads back the numerals** if one partial recursive code recovers `n`
from every representative of the constant function with value `n`. -/
def ReadsNumerals (δ : AppMorphism (ℕ → ℕ) ℕ) : Prop :=
  ∃ q : ℕ, ∀ n m : ℕ, δ.map (natEl n) m → n ∈ Kleene.natApp q m

theorem SeparatesBits.of_readsNumerals {δ : AppMorphism (ℕ → ℕ) ℕ} (h : ReadsNumerals δ) :
    SeparatesBits δ := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, fun b m _ hm => hq b m hm⟩

/-- The values of a represented element are represented: if `m` represents `β` in a morphism
`K₂ → K₁`, then for each `n` the realizer computes from `m` a representative of the constant
function `β n`. -/
theorem exists_map_natEl (δ : AppMorphism (ℕ → ℕ) ℕ) {β : ℕ → ℕ} {m p : ℕ}
    (hm : δ.map β m) {n : ℕ} (hp : δ.map (projAssoc n) p) :
    ∃ d, δ.map (natEl (β n)) d ∧
      d ∈ (Part.some δ.realizer ⬝ Part.some p) ⬝ Part.some m := by
  refine δ.realizer_app (projAssoc n) β p m hp hm (natEl (β n)) ?_
  rw [pca_app_eq, appK_projAssoc]
  exact Part.mem_some _

/-- **No applicative morphism `K₂ → K₁` separates bits.**  Kleene's second algebra does not map
back to Kleene's first in any way that lets `K₁` read a single bit off a representative. -/
theorem no_separatesBits_morphism (δ : AppMorphism (ℕ → ℕ) ℕ) : ¬ SeparatesBits δ := by
  classical
  rintro ⟨q, hq⟩
  -- a representative of the `n`-th projection, and of the characteristic function of a set
  set p : ℕ → ℕ := fun n => (δ.map_nonempty (projAssoc n)).choose with hpdef
  have hp : ∀ n, δ.map (projAssoc n) (p n) := fun n =>
    (δ.map_nonempty (projAssoc n)).choose_spec
  set chi : Set ℕ → ℕ → ℕ := fun S n => if n ∈ S then 1 else 0 with hchi
  set code : Set ℕ → ℕ := fun S => (δ.map_nonempty (chi S)).choose with hcode
  have hcodeSpec : ∀ S, δ.map (chi S) (code S) := fun S =>
    (δ.map_nonempty (chi S)).choose_spec
  have hle : ∀ (S : Set ℕ) (n : ℕ), chi S n ≤ 1 := by
    intro S n
    by_cases h : n ∈ S <;> simp [hchi, h]
  -- a representative determines the `0/1`-valued function it represents
  have hinj : Function.Injective code := by
    intro S T hST
    have hval : ∀ n, chi S n = chi T n := by
      intro n
      obtain ⟨d, hd, hdmem⟩ := exists_map_natEl δ (hcodeSpec S) (hp n)
      obtain ⟨d', hd', hd'mem⟩ := exists_map_natEl δ (hcodeSpec T) (hp n)
      rw [← hST] at hd'mem
      have hdd : d = d' := Part.mem_unique hdmem hd'mem
      subst hdd
      exact Part.mem_unique (hq _ d (hle S n) hd) (hq _ d (hle T n) hd')
    ext n
    have := hval n
    by_cases hS : n ∈ S <;> by_cases hT : n ∈ T <;>
      simp only [hchi, hS, hT, if_true, if_false] at this ⊢ <;> simp_all
  exact Function.cantor_injective code hinj

/-- **No applicative morphism `K₂ → K₁` reads back the numerals.** -/
theorem no_readsNumerals_morphism (δ : AppMorphism (ℕ → ℕ) ℕ) : ¬ ReadsNumerals δ := fun h =>
  no_separatesBits_morphism δ (SeparatesBits.of_readsNumerals h)

/-- The morphism `K₁ → K₂` of `Start/PCAMorphism.lean` is not reversible: there is no
applicative morphism back that recovers a numeral from a representative of the constant function
naming it. -/
theorem kOneToTwo_not_invertible :
    ¬ ∃ δ : AppMorphism (ℕ → ℕ) ℕ, ReadsNumerals δ := by
  rintro ⟨δ, hδ⟩
  exact no_readsNumerals_morphism δ hδ

/-- Applicative morphisms `K₂ → K₁` do exist — the trivial one — so the hypothesis of
`Realizability.KleeneTwo.no_separatesBits_morphism` cannot be dropped. -/
theorem nonempty_appMorphism_kleeneTwo_kleeneOne : Nonempty (AppMorphism (ℕ → ℕ) ℕ) :=
  ⟨AppMorphism.trivialMor (ℕ → ℕ) ℕ⟩

end KleeneTwo

end Realizability
