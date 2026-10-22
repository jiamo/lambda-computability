import Start.PTSRouteIIMorphismFundamental

/-!
# Series V, round 2, run 1, part A: coc with a top sort, `λHOL`, and `CC^ω`
(rows M29-EP-TOP-MORPHISM, M29-EP-CCOMEGA)

* `Srt3` (sorts `∗, □, Δ`), `cocTop` (axioms `∗ : □`, `□ : Δ`, the four coc rules) and
  `lambdaHOL` (Barendregt's `λHOL`: the same axioms, rules `(∗,∗)`, `(□,∗)`, `(□,□)`);
* **`lambdaHOL_not_cocMorphism : CoCMorphism lambdaHOL → False`** — the class is new;
* `TopMorphism P` — sorts to `∗, □, Δ`, axioms to axioms, rules to rules of `cocTop`; instances
  `lambdaHOL_topMorphism`, `cocTop_topMorphism`, and `CoCMorphism.toTop` (every coc-morphism is a
  top-morphism);
* `TopMorphism.hasType` (transport), `TopMorphism.sort_untypable` (a sort sent to `Δ` is never a
  typable subject), `TopMorphism.stronglyNormalizing_of_cocTop` (SN pulls back from `cocTop`) and
  `TopMorphism.expansionPostponement_of_sn_sortFundamental`;
* `ccOmega` (`CC^ω`) with the morphisms `coc → CC^ω`, `λHOL → CC^ω`, `cocTop → CC^ω` and
  `TopMorphism.toCCOmega`.

The target `expansionPostponement_of_topMorphism` is **not** proved here.  Its first missing lemma
is `SystemStronglyNormalizing cocTop` (see `docs/goal/evidence/M29-EP.md`,
"Series V, round 2, run 1").
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

/-- Sorts of coc with a top sort: `∗`, `□`, `Δ`. -/
inductive Srt3 where
  | star : Srt3
  | box : Srt3
  | top : Srt3
  deriving DecidableEq, Repr

/-- coc with a top sort: axioms `∗ : □` and `□ : Δ`; rules `(s₁, s₂, s₂)` for `s₁, s₂ ∈ {∗, □}`;
no rule mentions `Δ`. -/
def cocTop : Specification Srt3 where
  axioms s t := (s = .star ∧ t = .box) ∨ (s = .box ∧ t = .top)
  rule s₁ s₂ s₃ := s₃ = s₂ ∧ s₁ ≠ .top ∧ s₂ ≠ .top

/-- Barendregt's `λHOL`: axioms `∗ : □`, `□ : Δ`; rules `(∗,∗,∗)`, `(□,∗,∗)`, `(□,□,□)`. -/
def lambdaHOL : Specification Srt3 where
  axioms s t := (s = .star ∧ t = .box) ∨ (s = .box ∧ t = .top)
  rule s₁ s₂ s₃ := (s₁ = .star ∧ s₂ = .star ∧ s₃ = .star) ∨
    (s₁ = .box ∧ s₂ = .star ∧ s₃ = .star) ∨ (s₁ = .box ∧ s₂ = .box ∧ s₃ = .box)

/-- **`λHOL` has no morphism into coc**: the axiom `□ : Δ` has no image, since the only axiom of
coc is `∗ : □` and `∗ : □` would force `φ □ = ∗` and `φ □ = □`. -/
theorem lambdaHOL_not_cocMorphism (m : CoCMorphism lambdaHOL) : False := by
  have h1 := m.axiom_map .star .box (Or.inl ⟨rfl, rfl⟩)
  have h2 := m.axiom_map .box .top (Or.inr ⟨rfl, rfl⟩)
  have e : Srt.box = Srt.star := h1.2.symm.trans h2.1
  cases e

/-- **A morphism of specifications into coc with a top sort.** -/
structure TopMorphism {S : Type} (P : Specification S) where
  φ : S → Srt3
  axiom_map : ∀ s t, P.axioms s t → cocTop.axioms (φ s) (φ t)
  rule_map : ∀ a b c, P.rule a b c → cocTop.rule (φ a) (φ b) (φ c)

/-- `λHOL → cocTop` (the identity on sorts). -/
def lambdaHOL_topMorphism : TopMorphism lambdaHOL where
  φ := id
  axiom_map _ _ h := h
  rule_map a b c h := by
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      exact ⟨rfl, by decide, by decide⟩

/-- `cocTop → cocTop` (the identity). -/
def cocTop_topMorphism : TopMorphism cocTop where
  φ := id
  axiom_map _ _ h := h
  rule_map _ _ _ h := h

/-- The embedding of the sorts of coc into `Srt3`. -/
def srtToSrt3 : Srt → Srt3
  | .star => .star
  | .box => .box

/-- Every specification with a morphism into coc has a morphism into `cocTop`. -/
def CoCMorphism.toTop {S : Type} {P : Specification S} (m : CoCMorphism P) : TopMorphism P where
  φ := srtToSrt3 ∘ m.φ
  axiom_map s t h := by
    obtain ⟨h1, h2⟩ := m.axiom_map s t h
    exact Or.inl ⟨by simp [Function.comp, h1, srtToSrt3], by simp [Function.comp, h2, srtToSrt3]⟩
  rule_map a b c h := by
    have e := (m.rule_map a b c h).1
    refine ⟨by simp [Function.comp, e], ?_, ?_⟩ <;>
      simp only [Function.comp] <;> cases m.φ _ <;> decide

/-- `λHOL` lies in the top-morphism class but not in the coc-morphism class. -/
theorem lambdaHOL_in_top_class :
    Nonempty (TopMorphism lambdaHOL) ∧ ¬ Nonempty (CoCMorphism lambdaHOL) :=
  ⟨⟨lambdaHOL_topMorphism⟩, fun ⟨m⟩ => lambdaHOL_not_cocMorphism m⟩

namespace TopMorphism

variable {S : Type} {P : Specification S} (m : TopMorphism P)
include m

/-- Transport of derivations along the morphism. -/
theorem hasType {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    HasType cocTop (Γ.map (Expr.mapSort m.φ)) (M.mapSort m.φ) (A.mapSort m.φ) :=
  h.mapSort m.φ m.axiom_map m.rule_map

theorem validContext {Γ : List (Expr S)} (h : ValidContext P Γ) :
    ValidContext cocTop (Γ.map (Expr.mapSort m.φ)) := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih (m.hasType hA)

/-- Axioms are sent to `∗ : □` or `□ : Δ`, so the first sort of an axiom is never sent to `Δ`. -/
theorem axiom_fst_ne_top {s t : S} (h : P.axioms s t) : m.φ s ≠ .top := by
  rcases m.axiom_map s t h with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> decide

/-- **A sort sent to `Δ` is never a typable subject.** -/
theorem sort_untypable {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    ∀ s, M = .sort s → m.φ s ≠ .top := by
  induction h with
  | ax hst => intro s e; cases e; exact m.axiom_fst_ne_top hst
  | var _ _ => intro s e; cases e
  | @weaken _ M₀ _ _ _ _ _ ihM _ =>
      intro s e
      cases M₀ <;> simp [Expr.rename] at e
      subst e
      exact ihM _ rfl
  | product _ _ _ _ _ => intro s e; cases e
  | abstraction _ _ _ _ => intro s e; cases e
  | application _ _ _ _ => intro s e; cases e
  | conversion _ _ _ ihM _ => exact ihM

/-- **Only sorts are typed by a sort sent to `Δ`** (in `cocTop`: only `□ : Δ`). -/
theorem top_typed_sort {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    ∀ t, A = .sort t → m.φ t = .top → ∃ s, M = .sort s := by
  induction h with
  | ax _ => intro t _ _; exact ⟨_, rfl⟩
  | @var Γ A s hA _ =>
      intro t e ht
      cases A <;> simp [Expr.rename] at e
      subst e
      exact absurd ht (m.sort_untypable hA _ rfl)
  | @weaken Γ M B C s hM hC ihM _ =>
      intro t e ht
      cases B <;> simp [Expr.rename] at e
      subst e
      obtain ⟨s', rfl⟩ := ihM _ rfl ht
      exact ⟨s', rfl⟩
  | @product Γ A B s₁ s₂ s₃ _ _ hr _ _ =>
      intro t e ht
      cases e
      obtain ⟨e3, _, h2⟩ := m.rule_map _ _ _ hr
      exact absurd (e3.symm.trans ht) h2
  | abstraction _ _ _ _ => intro t e; cases e
  | @application Γ f a A B hf ha _ _ =>
      intro t e ht
      cases B with
      | sort u =>
          simp [Expr.instantiate, Expr.subst] at e
          subst e
          rcases hf.regularity with ⟨_, he⟩ | ⟨_, hPi⟩
          · cases he
          · obtain ⟨_, _, _, _, hB, _, _⟩ := hPi.generation_pi
            exact absurd ht (m.sort_untypable hB _ rfl)
      | var n =>
          cases n with
          | zero =>
              simp [Expr.instantiate, Expr.subst, Expr.single] at e
              exact absurd ht (m.sort_untypable ha _ e)
          | succ n => simp [Expr.instantiate, Expr.subst, Expr.single] at e
      | app _ _ => simp [Expr.instantiate, Expr.subst] at e
      | lam _ _ => simp [Expr.instantiate, Expr.subst] at e
      | pi _ _ => simp [Expr.instantiate, Expr.subst] at e
  | conversion _ hB _ _ _ =>
      intro t e ht
      subst e
      exact absurd ht (m.sort_untypable hB _ rfl)

/-- **Strong normalization pulls back from `cocTop`.** -/
theorem stronglyNormalizing_of_cocTop (hsn : SystemStronglyNormalizing cocTop) :
    SystemStronglyNormalizing P := by
  intro Γ hΓ M hM
  obtain ⟨A, hA⟩ := hM
  apply StronglyNormalizing.of_mapSort m.φ
  apply hsn _ (m.validContext hΓ)
  rcases hA with h | h
  · exact ⟨_, .inl (m.hasType h)⟩
  · exact ⟨_, .inr (m.hasType h)⟩

/-- Expansion postponement for a top-morphism specification from strong normalization of
`cocTop` and the sort-typed fundamental lemma (routes (iii) and product normalization are generic). -/
theorem expansionPostponement_of_sn_sortFundamental (hsn : SystemStronglyNormalizing cocTop)
    (h : SNGeneric.SortFundamental P) : ExpansionPostponement P :=
  SNGeneric.expansionPostponement_of_sortFundamental (m.stronglyNormalizing_of_cocTop hsn) h

end TopMorphism

/-! ### `CC^ω` -/

/-- Sorts of `CC^ω`: `Prop` and `Type n`. -/
inductive CSrt where
  | prop : CSrt
  | type : ℕ → CSrt
  deriving DecidableEq, Repr

/-- `CC^ω`: axioms `Prop : Type 0`, `Type n : Type (n+1)`; rules `(s, Prop, Prop)`,
`(Prop, Type n, Type n)`, `(Type i, Type j, Type (max i j))`. -/
def ccOmega : Specification CSrt where
  axioms s t := (s = .prop ∧ t = .type 0) ∨ ∃ n, s = .type n ∧ t = .type (n + 1)
  rule s₁ s₂ s₃ := (s₂ = .prop ∧ s₃ = .prop) ∨ (∃ n, s₁ = .prop ∧ s₂ = .type n ∧ s₃ = .type n) ∨
    ∃ i j, s₁ = .type i ∧ s₂ = .type j ∧ s₃ = .type (max i j)

/-- A morphism of specifications into `CC^ω`. -/
structure CCOmegaMorphism {S : Type} (P : Specification S) where
  φ : S → CSrt
  axiom_map : ∀ s t, P.axioms s t → ccOmega.axioms (φ s) (φ t)
  rule_map : ∀ a b c, P.rule a b c → ccOmega.rule (φ a) (φ b) (φ c)

/-- `∗ ↦ Prop`, `□ ↦ Type 0`, `Δ ↦ Type 1`. -/
def srt3ToCSrt : Srt3 → CSrt
  | .star => .prop
  | .box => .type 0
  | .top => .type 1

/-- `cocTop → CC^ω`. -/
def cocTop_ccOmegaMorphism : CCOmegaMorphism cocTop where
  φ := srt3ToCSrt
  axiom_map s t h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨0, rfl, rfl⟩
  rule_map a b c h := by
    obtain ⟨e, ha, hb⟩ := h
    subst e
    cases a <;> cases c <;> simp_all [srt3ToCSrt, ccOmega]

/-- Every top-morphism specification has a morphism into `CC^ω`. -/
def TopMorphism.toCCOmega {S : Type} {P : Specification S} (m : TopMorphism P) :
    CCOmegaMorphism P where
  φ := srt3ToCSrt ∘ m.φ
  axiom_map s t h := cocTop_ccOmegaMorphism.axiom_map _ _ (m.axiom_map s t h)
  rule_map a b c h := cocTop_ccOmegaMorphism.rule_map _ _ _ (m.rule_map a b c h)

/-- `λHOL → CC^ω`. -/
def lambdaHOL_ccOmegaMorphism : CCOmegaMorphism lambdaHOL := lambdaHOL_topMorphism.toCCOmega

/-- `coc → CC^ω` (`∗ ↦ Prop`, `□ ↦ Type 0`). -/
def coc_ccOmegaMorphism : CCOmegaMorphism (cubeSpec coc) :=
  (CoCMorphism.cube coc).toTop.toCCOmega

/-- `CC^ω` has no morphism into `cocTop`: the chain `Prop : Type 0 : Type 1 : Type 2` of axioms
would need four distinct levels. -/
theorem ccOmega_not_topMorphism (m : TopMorphism ccOmega) : False := by
  have h1 := m.axiom_map .prop (.type 0) (Or.inl ⟨rfl, rfl⟩)
  have h2 := m.axiom_map (.type 0) (.type 1) (Or.inr ⟨0, rfl, rfl⟩)
  have h3 := m.axiom_map (.type 1) (.type 2) (Or.inr ⟨1, rfl, rfl⟩)
  simp only [cocTop] at h1 h2 h3
  rcases h1 with ⟨_, e1⟩ | ⟨_, e1⟩ <;> rcases h2 with ⟨f2, e2⟩ | ⟨f2, e2⟩ <;>
    rcases h3 with ⟨f3, _⟩ | ⟨f3, _⟩ <;> simp_all

end PureTypeSystem
