import Start.PTSRouteIICoCFundamental
import Start.PTSExpansionLambdaP
import Start.PTSExpansionLambdaPOmegaBarEP

/-!
# Round 11, part A4–A5: expansion postponement for coc, and for every corner of the cube

* `RouteIICoC.SubstOK.ids` — the identity substitution with the canonical valuation is
  reducible in every canonically valid coc context;
* `RouteIICoC.substOK_substAt`, `RouteIICoC.sortFundamental_coc : SortFundamental (cubeSpec coc)`;
* `hsubstSort_coc`, **`hsubstPi_coc : HSubstPi (cubeSpec coc)`** (through
  `hsubstPi_iff_hsubstSort`), `coc_productNormalizationR`, and
  **`coc_expansionPostponement : ExpansionPostponement (cubeSpec coc)`** (through
  `cube_expansionPostponement_of_hsubstPi`);
* **`cube_expansionPostponement_all : ∀ f : CubeFeatures, ExpansionPostponement (cubeSpec f)`** —
  the four non-dependent corners by `cube_expansionPostponement`, and λP, λP2, λPω̲ and coc by
  their theorems.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace RouteIICoC

open LambdaPi (Srt)
open RouteII (Cand NormNW scons forall₂_reduces_refl SortFundamental)
open ErasureCoC (canonK ValK)

theorem HasTypeNW.lookup' {Δ : List (Expr Srt)} (hv : ValidContextNW PC Δ) :
    ∀ {n : ℕ} {A : Expr Srt}, Lookup Δ n A → HasTypeNW PC Δ (.var n) A := by
  induction hv with
  | nil => intro n A hn; cases hn
  | cons _ hB ih =>
      intro n A hn
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

/-- The canonical valuation. -/
def canonValC : ValK Cand := fun _ k => canonK candAlg k

theorem goodVal_canon (Δ : Nat → CoC.Cls) : GoodVal Δ canonValC := fun _ k _ => candC_canon k

theorem ncons_canonValC : CoC.ncons (canonK candAlg) canonValC = canonValC := by
  funext n; cases n <;> rfl

/-- **The identity substitution is reducible** in every canonically valid coc context. -/
theorem SubstOK.ids {Γ : List (Expr Srt)} (hv : ValidContextNW PC Γ) :
    SubstOK Γ Γ Expr.var canonValC where
  good := goodVal_canon _
  ctx := ⟨Γ, forall₂_reduces_refl Γ, hv⟩
  tys n A hn := tyOK_of_typed (HasTypeNW.lookup' hv hn).toHasType (goodVal_canon _)
  var n A hn := by
    unfold Sem
    simp only [Expr.subst_var]
    exact SemC.var (tyOK_of_typed (HasTypeNW.lookup' hv hn).toHasType (goodVal_canon _))
      ⟨Γ, _, _, forall₂_reduces_refl Γ, .refl, .refl, HasTypeNW.lookup' hv hn⟩

/-- **The substitution of a canonical `N : A` at depth `Δ` is reducible.** -/
theorem substOK_substAt {Γ : List (Expr Srt)} {N A : Expr Srt} (hN : HasTypeNW PC Γ N A)
    {Δ Δ' : List (Expr Srt)} (hc : CtxSubstRed N Δ Δ') (hv : ValidContextNW PC (Δ' ++ Γ))
    (hsrc : ValidContext PC (Δ ++ A :: Γ)) :
    SubstOK (Δ ++ A :: Γ) (Δ' ++ Γ) (Expr.substAt N Δ.length) canonValC := by
  induction hc with
  | nil =>
      have hid := SubstOK.ids hN.valid
      have hNsem : SemC Γ canonValC Γ A N (A.subst Expr.var) := by
        have := fundamental hN.toHasType hid
        unfold Sem at this
        simp only [Expr.subst_var] at this ⊢
        exact this
      have := hid.cons ((goodVal_canon _).ncons_canon _)
        (tyOK_of_typed hN.toHasType (goodVal_canon _)) hNsem
      rw [ncons_canonValC, RouteII.scons_var] at this
      exact this
  | @cons Δ Δ' D D' _ hr ih =>
      cases hv with
      | cons hv' hD' =>
          cases hsrc with
          | cons hsrc' hD =>
              have := (ih hv' hsrc').lift ((goodVal_canon _).ncons_canon _)
                (tyOK_of_sorted hD (goodVal_canon _))
                ⟨_, D', _, forall₂_reduces_refl _, .refl, .refl, hD'⟩ hr
              rw [ncons_canonValC, ← Expr.substAt_succ] at this
              exact this

/-- **The sort-typed fundamental lemma for coc.** -/
theorem sortFundamental_coc : SortFundamental PC := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  have := fundamental hM.toHasType (substOK_substAt hN hc hv hM.toHasType.valid)
  unfold Sem at this
  exact SemC_sort.1 this

end RouteIICoC

/-- **Hereditary substitution into sort-typed premises holds in coc.** -/
theorem hsubstSort_coc : HSubstSort (cubeSpec coc) :=
  RouteII.hsubstSort_of_sortFundamental RouteIICoC.sortFundamental_coc

/-- **Hereditary substitution into product premises holds in coc** (the board's target
`HSubstPi (cubeSpec coc)`, through `hsubstPi_iff_hsubstSort`). -/
theorem hsubstPi_coc : HSubstPi (cubeSpec coc) :=
  (hsubstPi_iff_hsubstSort coc).2 hsubstSort_coc

/-- **Product normalization for the reduction-only judgement of coc.** -/
theorem coc_productNormalizationR : ProductNormalizationR (cubeSpec coc) :=
  (cube_expansionPostponement_of_hsubstPi coc hsubstPi_coc).1

/-- **Expansion postponement for the Calculus of Constructions** (TLCA open problem 23 for the
corner coc), through `cube_expansionPostponement_of_hsubstPi`. -/
theorem coc_expansionPostponement : ExpansionPostponement (cubeSpec coc) :=
  (cube_expansionPostponement_of_hsubstPi coc hsubstPi_coc).2

/-- **Expansion postponement in every corner of the λ-cube.** -/
theorem cube_expansionPostponement_all (f : CubeFeatures) :
    ExpansionPostponement (cubeSpec f) := by
  obtain ⟨poly, ops, dep⟩ := f
  cases dep with
  | false => exact cube_expansionPostponement _ rfl
  | true =>
      cases poly <;> cases ops
      · exact lambdaP_expansionPostponement
      · exact lambdaPOmegaBar_expansionPostponement
      · exact lambdaP2_expansionPostponement
      · exact coc_expansionPostponement

end PureTypeSystem
