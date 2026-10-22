import Start.PTSExpansionTop

/-!
# Series V, round 2, run 1, part A: strong normalization of coc with a top sort
(row M29-EP-TOP-MORPHISM)

Route (ii) of the task: SN by reduction to coc.

* `TopSN.kf_coc` — a `cocTop` judgement in a *kind-free* context (no declaration `K : □`) whose
  type is not `Δ` is a coc judgement after the collapse `Δ ↦ □` (`TopSN.cut`); the conversion
  case with target `□` uses that `□` is untypable in coc;
* `TopSN.kindSubst` — every valid `cocTop` context is sent to a valid kind-free context by a
  typed substitution (each kind variable `K : □` is replaced by `∗`);
* **`TopSN.cocTop_stronglyNormalizing : SystemStronglyNormalizing cocTop`** (pulled back along the
  substitution by `StronglyNormalizing.of_subst` and along the collapse by
  `StronglyNormalizing.of_mapSort`);
* **`TopMorphism.stronglyNormalizing`** for every top-morphism specification,
  `lambdaHOL_stronglyNormalizing`, and
  **`TopMorphism.expansionPostponement_of_sortFundamental`**: for every such `P`, expansion
  postponement follows from the sort-typed fundamental lemma alone;
* **`lambdaHOL_expansionPostponement`** — `λHOL` is stratified (`∗ ↦ 0`, `□ ↦ 1`, `Δ ↦ 2`), so
  Stage B applies; `cocTop_not_stratified` — `cocTop` is not.

The first missing lemma towards `expansionPostponement_of_topMorphism` is
`SNGeneric.SortFundamental P` for a top-morphism `P` (the route (ii) fundamental lemma of
`Start/PTSRouteIIMorphismFundamental.lean` generalized to `cocTop`).
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace TopSN

open LambdaPi (Srt)

/-- The collapse `Δ ↦ □` (used only on judgements that never mention `Δ`). -/
def cut : Srt3 → Srt
  | .star => .star
  | .box => .box
  | .top => .box

abbrev PC : Specification Srt := cubeSpec coc

theorem sort_typed_top {Γ : List (Expr Srt3)} {A : Expr Srt3}
    (h : HasType cocTop Γ A (.sort .top)) : A = .sort .box := by
  obtain ⟨s, rfl⟩ := cocTop_topMorphism.top_typed_sort h .top rfl rfl
  obtain ⟨t, hst, hc⟩ := h.generation
  have := hc.sort_inj
  subst this
  rcases hst with ⟨_, h2⟩ | ⟨h1, _⟩
  · cases h2
  · rw [h1]

theorem box_typed {Γ : List (Expr Srt3)} {s : Srt3}
    (h : HasType cocTop Γ (.sort .box) (.sort s)) : s = .top := by
  obtain ⟨t, hst, hc⟩ := h.generation
  have := hc.sort_inj
  subst this
  rcases hst with ⟨h1, _⟩ | ⟨_, h2⟩
  · cases h1
  · exact h2

theorem not_top_of_ne_box {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hA : A ≠ .sort .box) : s ≠ .top := by
  rintro rfl
  exact hA (sort_typed_top h)

theorem ne_box_of_rule {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) : A ≠ .sort .box := by
  rintro rfl
  exact hs (box_typed h)

theorem typed_ne_top {Γ : List (Expr Srt3)} {A T : Expr Srt3} (h : HasType cocTop Γ A T) :
    A ≠ .sort .top := fun e => cocTop_topMorphism.sort_untypable h .top e rfl

theorem rename_ne_top {B : Expr Srt3} (hB : B.rename Nat.succ ≠ .sort .top) :
    B ≠ .sort .top := by
  rintro rfl
  exact hB rfl

/-- **A kind-free `cocTop` judgement whose type is not `Δ` is a coc judgement.** -/
theorem kf_coc {Γ : List (Expr Srt3)} {M A : Expr Srt3} (h : HasType cocTop Γ M A) :
    (∀ C ∈ Γ, C ≠ .sort .box) → A ≠ .sort .top →
    HasType PC (Γ.map (Expr.mapSort cut)) (M.mapSort cut) (A.mapSort cut) := by
  induction h with
  | ax hst =>
      intro _ hA
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact .ax ⟨rfl, rfl⟩
      · exact absurd rfl hA
  | @var Γ A s hA ih =>
      intro hKF _
      have hAb : A ≠ .sort .box := hKF A (by simp)
      have hs := not_top_of_ne_box hA hAb
      have := ih (fun C hC => hKF C (by simp [hC])) (by rintro ⟨⟩; exact hs rfl)
      simpa [Expr.mapSort] using HasType.var this
  | @weaken Γ M B C s hM hC ihM ihC =>
      intro hKF hB
      have hCb : C ≠ .sort .box := hKF C (by simp)
      have hs := not_top_of_ne_box hC hCb
      have hKF' : ∀ D ∈ Γ, D ≠ .sort .box := fun D hD => hKF D (by simp [hD])
      have h1 := ihM hKF' (rename_ne_top hB)
      have h2 := ihC hKF' (by rintro ⟨⟩; exact hs rfl)
      simpa using HasType.weaken h1 h2
  | @product Γ A B s₁ s₂ s₃ hA hB hr ihA ihB =>
      intro hKF _
      obtain ⟨e3, h1, h2⟩ := hr
      have hAb := ne_box_of_rule hA h1
      have hKF' : ∀ D ∈ A :: Γ, D ≠ .sort .box := by
        intro D hD
        rcases List.mem_cons.1 hD with rfl | hD
        · exact hAb
        · exact hKF D hD
      have iA := ihA hKF (by rintro ⟨⟩; exact h1 rfl)
      have iB := ihB hKF' (by rintro ⟨⟩; exact h2 rfl)
      subst e3
      refine HasType.product iA iB ⟨rfl, ?_⟩
      cases s₁ <;> cases s₃ <;> first | exact absurd rfl h1 | exact absurd rfl h2 | trivial
  | @abstraction Γ A b B s hb hPi ihb ihPi =>
      intro hKF _
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, _⟩ := hPi.generation_pi
      have hAb := ne_box_of_rule hA hr.2.1
      have hKF' : ∀ D ∈ A :: Γ, D ≠ .sort .box := by
        intro D hD
        rcases List.mem_cons.1 hD with rfl | hD
        · exact hAb
        · exact hKF D hD
      have hs : s ≠ .top := by
        rintro rfl
        obtain ⟨_, e⟩ := cocTop_topMorphism.top_typed_sort hPi .top rfl rfl
        cases e
      have i1 := ihb hKF' (typed_ne_top hB)
      have i2 := ihPi hKF (by rintro ⟨⟩; exact hs rfl)
      exact HasType.abstraction i1 i2
  | @application Γ f a A B hf ha ihf iha =>
      intro hKF _
      have hAt : A ≠ .sort .top := by
        rcases hf.regularity with ⟨_, he⟩ | ⟨_, hPi⟩
        · cases he
        · obtain ⟨_, _, _, hA, _, _, _⟩ := hPi.generation_pi
          exact typed_ne_top hA
      have i1 := ihf hKF (by rintro ⟨⟩)
      have i2 := iha hKF hAt
      simpa [Expr.mapSort] using HasType.application i1 i2
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      intro hKF hBt
      by_cases hs : s = .top
      · subst hs
        have eB := sort_typed_top hB
        subst eB
        have hAt : A ≠ .sort .top := by
          rintro rfl
          cases hc.sort_inj
        have i1 := ihM hKF hAt
        have hc' : Converts (A.mapSort cut) (.sort .box) := by
          simpa [Expr.mapSort, cut] using hc.mapSort cut
        show HasType PC _ _ (.sort .box)
        rcases i1.regularity with ⟨t, ht⟩ | ⟨t, hAt'⟩
        · rw [ht] at hc' i1
          rw [← hc'.sort_inj]
          exact i1
        · exfalso
          obtain ⟨N, hN, hs⟩ := hc'.join
          have heq := (Normal.sort (Srt.box)).reduces_eq hs
          subst heq
          have hbox := hAt'.subject_reduces hN
          obtain ⟨t', hst, _⟩ := hbox.generation
          cases hst.1
      · have hAt : A ≠ .sort .top := by
          rintro rfl
          obtain ⟨N, hN, hs'⟩ := hc.join
          have heq := (Normal.sort (Srt3.top)).reduces_eq hN
          subst heq
          exact typed_ne_top (hB.subject_reduces hs') rfl
        have i1 := ihM hKF hAt
        have i2 := ihB hKF (by rintro ⟨⟩; exact hs rfl)
        exact HasType.conversion i1 i2 (hc.mapSort cut)

theorem kf_valid {Γ : List (Expr Srt3)} (hΓ : ValidContext cocTop Γ)
    (hKF : ∀ C ∈ Γ, C ≠ .sort .box) : ValidContext PC (Γ.map (Expr.mapSort cut)) := by
  induction hΓ with
  | nil => exact .nil
  | @cons Γ A s _ hA ih =>
      have hAb : A ≠ .sort .box := hKF A (by simp)
      have hs := not_top_of_ne_box hA hAb
      have hKF' : ∀ D ∈ Γ, D ≠ .sort .box := fun D hD => hKF D (by simp [hD])
      exact .cons (ih hKF') (kf_coc hA hKF' (by rintro ⟨⟩; exact hs rfl))

/-- The substitution sending each kind variable (`K : □`) to `∗`. -/
def consStar (σ : Nat → Expr Srt3) : Nat → Expr Srt3
  | 0 => .sort .star
  | n + 1 => σ n

/-- **Kind substitution**: every valid `cocTop` context maps, by a typed substitution, to a valid
kind-free context. -/
theorem kindSubst {Γ : List (Expr Srt3)} (hΓ : ValidContext cocTop Γ) :
    ∃ Γ' σ, ValidContext cocTop Γ' ∧ (∀ C ∈ Γ', C ≠ .sort .box) ∧
      TypedSubstitution cocTop Γ Γ' σ := by
  induction hΓ with
  | nil => exact ⟨[], Expr.var, .nil, by simp, fun n A h => by cases h⟩
  | @cons Γ A s _ hA ih =>
      obtain ⟨Γ', σ, hΓ', hKF, hσ⟩ := ih
      have hA' := hA.subst hΓ' σ hσ
      by_cases hb : A.subst σ = .sort .box
      · refine ⟨Γ', consStar σ, hΓ', hKF, ?_⟩
        intro n B hn
        cases hn with
        | zero =>
            rw [Expr.subst_rename]
            have : consStar σ ∘ Nat.succ = σ := rfl
            rw [this, hb]
            exact HasType.sort_of_valid hΓ' (Or.inl ⟨rfl, rfl⟩)
        | succ _ hn =>
            rw [Expr.subst_rename]
            exact hσ _ _ hn
      · refine ⟨A.subst σ :: Γ', Expr.liftSub σ, .cons hΓ' hA', ?_, hσ.lift hA'⟩
        intro C hC
        rcases List.mem_cons.1 hC with rfl | hC
        · exact hb
        · exact hKF C hC

theorem sn_sort (s : Srt3) : StronglyNormalizing (Expr.sort s : Expr Srt3) :=
  Acc.intro _ fun N h => absurd h (Normal.sort s N)

/-- **Strong normalization of coc with a top sort.** -/
theorem cocTop_stronglyNormalizing : SystemStronglyNormalizing cocTop := by
  intro Γ hΓ M hM
  obtain ⟨A, hA⟩ := hM
  obtain ⟨Γ', σ, hΓ', hKF, hσ⟩ := kindSubst hΓ
  apply StronglyNormalizing.of_subst σ
  have hc := kf_valid hΓ' hKF
  rcases hA with h | h
  · have h' := h.subst hΓ' σ hσ
    by_cases ht : A.subst σ = .sort .top
    · obtain ⟨s, e⟩ := cocTop_topMorphism.top_typed_sort h' .top ht rfl
      rw [e]; exact sn_sort s
    · apply StronglyNormalizing.of_mapSort cut
      exact coc_stronglyNormalizing _ hc _ ⟨_, .inl (kf_coc h' hKF ht)⟩
  · have h' := h.subst hΓ' σ hσ
    by_cases ht : M.subst σ = .sort .top
    · rw [ht]; exact sn_sort _
    · apply StronglyNormalizing.of_mapSort cut
      exact coc_stronglyNormalizing _ hc _ ⟨_, .inr (kf_coc h' hKF ht)⟩

end TopSN

/-- **Every specification with a morphism into `cocTop` is strongly normalizing.** -/
theorem TopMorphism.stronglyNormalizing {S : Type} {P : Specification S} (m : TopMorphism P) :
    SystemStronglyNormalizing P :=
  m.stronglyNormalizing_of_cocTop TopSN.cocTop_stronglyNormalizing

/-- `λHOL` is strongly normalizing. -/
theorem lambdaHOL_stronglyNormalizing : SystemStronglyNormalizing lambdaHOL :=
  lambdaHOL_topMorphism.stronglyNormalizing

/-- **Expansion postponement from the sort-typed fundamental lemma alone**, for every
specification with a morphism into `cocTop`. -/
theorem TopMorphism.expansionPostponement_of_sortFundamental {S : Type} {P : Specification S}
    (m : TopMorphism P) (h : SNGeneric.SortFundamental P) : ExpansionPostponement P :=
  SNGeneric.expansionPostponement_of_sortFundamental m.stronglyNormalizing h

/-- `λHOL` is stratified: levels `∗ ↦ 0`, `□ ↦ 1`, `Δ ↦ 2`. -/
def lambdaHOL_stratification : Stratification lambdaHOL where
  level
    | .star => 0
    | .box => 1
    | .top => 2
  bound := 2
  level_le s := by cases s <;> decide
  axiom_level s t h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rule_level a b c h := by
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide

/-- **Expansion postponement for `λHOL`** (through its stratification, Stage B). -/
theorem lambdaHOL_expansionPostponement : ExpansionPostponement lambdaHOL :=
  expansionPostponement_of_stratification lambdaHOL_stratification

/-- `cocTop` is not stratified (it has the dependent rule `(∗, □, □)`). -/
theorem cocTop_not_stratified (L : Stratification cocTop) : False :=
  not_stratified_of_dependent_rule (P := cocTop) (s := .star) (t := .box) (r := .box)
    (Or.inl ⟨rfl, rfl⟩) ⟨rfl, by decide, by decide⟩ L

end PureTypeSystem
