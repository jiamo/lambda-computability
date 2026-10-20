/-
**Route (ii), round 9: CR3 at neutral applications does not need hereditary substitution, and
the two-level (type/term) relation for λP2** — task `M29-EP-IMPREDICATIVE`, round 9, part A.

Round 8 recorded as the first failing step of the route (ii) fundamental lemma the equation

  `NormNW (cubeSpec lambdaP2) Γ (.app (.var x) N) (B.instantiate N)`

for `x : Π A B` and a normalizable `N : A`, and claimed that it needs `HSubstSort` at `B`.  That
diagnosis is **wrong**: the application rule of the canonical judgement `HasTypeNW` asks for the
normal form `B'` of `B[N]` and for `Normal B'`, *not* for a canonical derivation of `B' : s`.
The normal form exists by strong normalization of the cube (`HasTypeNW.app_type_exists`), and
the contexts and domains of the two premises are matched by uniqueness of normal forms.  This
module proves it:

* `RouteII.NeNW` — the judgement normalizes to a canonical judgement whose subject is a
  **neutral** (a variable applied to arguments);
* `RouteII.normal_app_of_neutral` — a normal neutral applied to a normal argument is normal;
* `RouteII.NeNW.app` — **CR3 at neutral applications**, in every corner of the cube:
  `NeNW Γ F (Π A B) → NormNW Γ N A → NeNW Γ (F N) (B[N])`;
* `RouteII.cr3_var_app` — the round-8 equation itself, closed, with no hereditary substitution:
  `NormNW P Γ (.var x) (.pi A B) → NormNW P Γ N A → NormNW P Γ (.app (.var x) N) (B.instantiate N)`;
* `RouteII.NormNW.convType` — the base predicate is closed under **conversion** of the type
  (the canonical type is normal), so the term-level candidates need not carry the
  reduction-only judgement `HasTypeR`, whose closure under expansion of the type is the open
  problem itself.

The two-level relation (types first, as in Abel–Öhman–Vezzosi):

* `RouteII.IsCandN` — candidates: normalizable judgements, closed under conversion of the type
  and under expansion of the subject, containing the neutral judgements (CR3);
* `RouteII.TRed Cs` — **type reducibility** of a constructor at a λP2 kind, relative to the
  *semantic kind* `Cs` (the list of candidates interpreting the domains `A₁ … Aₙ` of the kind
  `Π x₁:A₁ … Π xₙ:Aₙ. ∗`): at `∗` the constructor normalizes; at a product, applied to every
  argument of the domain candidate in every context extension, it is reducible at the codomain.
  It is environment free, because the domains are given as candidates;
* `RouteII.TRed.escape` (CR1), `RouteII.TRed.reflect` (CR3: neutral constructors are type
  reducible, by `NeNW.app`), `RouteII.TRed.var`, `RouteII.TRed.app` (the family-application case,
  supplied by the clause of `TRed`), `RouteII.TRed.reduceKind`, `RouteII.TRed.expand`;
* `RouteII.SkP` / `RouteII.KSkP` — λP2 skeletons whose quantifier `(□,∗)` records the kind
  skeleton of the bound constructor variable;
* `RouteII.GoodP` — **term reducibility** relative to type reducibility: at the quantifier, closure
  under application to every *type-reducible* constructor, for every candidate interpreting the
  bound variable;
* `RouteII.GoodP.isCandN` — **CR1–CR3** for term reducibility (with closure under conversion of
  the type and expansion of the subject); `RouteII.GoodP.var` (variables are reducible),
  `RouteII.GoodP.app`, `RouteII.GoodP.tyApp`, `RouteII.GoodP.lam_arr` (the application,
  type-application and abstraction cases of the fundamental lemma at the level of the relation);
* `RouteII.GoodP_subst` / `RouteII.GoodP_inst` — the interpretation commutes with substitution of
  skeletons, and `RouteII.GoodP.tyApp_subst`.

What is not built: the erasure of λP2 types into `SkP` (recording at `(□,∗)` the kind skeleton of
the bound variable) with its commutation lemmas, and the fundamental lemma itself; see
`docs/goal/evidence/M29-EP.md`, round 9, for the exact first missing lemma.
-/

import Start.PTSRouteIIErased

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PureTypeSystem

namespace RouteII

open LambdaPi (Srt)

/-! ### Neutral normalization and CR3 at neutral applications -/

/-- The judgement `Γ ⊢ M : T` normalizes to a canonical judgement with a neutral subject. -/
def NeNW (P : Specification Srt) (Γ : List (Expr Srt)) (M T : Expr Srt) : Prop :=
  ∃ Γ' M' T', List.Forall₂ Reduces Γ Γ' ∧ Reduces M M' ∧ Reduces T T' ∧
    HasTypeNW P Γ' M' T' ∧ Neutral M'

theorem NeNW.toNormNW {P : Specification Srt} {Γ : List (Expr Srt)} {M T : Expr Srt}
    (h : NeNW P Γ M T) : NormNW P Γ M T := by
  obtain ⟨Γ', M', T', hc, hM, hT, hNW, -⟩ := h
  exact ⟨Γ', M', T', hc, hM, hT, hNW⟩

/-- A variable which normalizes is a neutral which normalizes. -/
theorem NeNW.of_var {P : Specification Srt} {Γ : List (Expr Srt)} {x : ℕ} {T : Expr Srt}
    (h : NormNW P Γ (.var x) T) : NeNW P Γ (.var x) T := by
  obtain ⟨Γ', M', T', hc, hM, hT, hNW⟩ := h
  have hv : M' = .var x := ((Normal.var x).reduces_eq hM).symm
  subst hv
  exact ⟨Γ', _, T', hc, hM, hT, hNW, .var x⟩

/-- A neutral is never an abstraction. -/
theorem neutral_not_lam {M : Expr Srt} (h : Neutral M) (A b : Expr Srt) : M ≠ .lam A b := by
  cases h <;> intro heq <;> cases heq

/-- A normal neutral applied to a normal argument is normal. -/
theorem normal_app_of_neutral {F a : Expr Srt} (hF : Neutral F) (hFn : Normal F)
    (ha : Normal a) : Normal (.app F a) := by
  intro N hb
  cases hb with
  | head A b a => exact neutral_not_lam hF A b rfl
  | app_left h => exact hFn _ h
  | app_right h => exact ha _ h

/-- **CR3 at neutral applications**, in every corner of the cube.  Only strong normalization
(for the normal form of `B[N]`) and uniqueness of normal forms are used; no canonical
derivation of the instantiated codomain is needed, because the application rule of
`HasTypeNW` does not ask for one. -/
theorem NeNW.app (f : CubeFeatures) {Γ : List (Expr Srt)} {F N A B : Expr Srt}
    (hF : NeNW (cubeSpec f) Γ F (.pi A B)) (hN : NormNW (cubeSpec f) Γ N A) :
    NeNW (cubeSpec f) Γ (.app F N) (B.instantiate N) := by
  obtain ⟨Γ₁, F', T₁, hc₁, hF', hT₁, hNW₁, hne⟩ := hF
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hT₁
  obtain ⟨Γ₂, N', A₂, hc₂, hN', hA₂, hNW₂⟩ := hN
  have hΓ : Γ₂ = Γ₁ :=
    forall₂_reduces_unique hc₂ hc₁ hNW₂.normal.2.2 hNW₁.normal.2.2
  subst hΓ
  have hnP := normal_pi_inv hNW₁.normal.2.1
  have hA : A₂ = A₁ := Reduces.normal_unique hA₂ hA₁ hNW₂.normal.2.1 hnP.1
  subst hA
  obtain ⟨B', hB', hB'n⟩ := HasTypeNW.app_type_exists f hNW₁ hNW₂
  refine ⟨Γ₂, .app F' N', B', hc₂, Reduces.app hF' hN',
    (Reduces.instantiate hB₁ hN').trans hB', ?_, .app hne⟩
  exact .application hNW₁ hNW₂ hB' hB'n
    (normal_app_of_neutral hne hNW₁.normal.1 hNW₂.normal.1)

/-- **The round-8 equation, closed.**  For a variable `x : Π A B` and a normalizable argument
`N : A`, the neutral application normalizes, in every corner of the cube (in particular
λP2), without hereditary substitution. -/
theorem cr3_var_app (f : CubeFeatures) {Γ : List (Expr Srt)} {x : ℕ} {N A B : Expr Srt}
    (hx : NormNW (cubeSpec f) Γ (.var x) (.pi A B)) (hN : NormNW (cubeSpec f) Γ N A) :
    NormNW (cubeSpec f) Γ (.app (.var x) N) (B.instantiate N) :=
  (NeNW.app f (NeNW.of_var hx) hN).toNormNW

/-- The round-8 equation for λP2. -/
theorem cr3_var_app_lambdaP2 {Γ : List (Expr Srt)} {x : ℕ} {N A B : Expr Srt}
    (hx : NormNW P2 Γ (.var x) (.pi A B)) (hN : NormNW P2 Γ N A) :
    NormNW P2 Γ (.app (.var x) N) (B.instantiate N) :=
  cr3_var_app lambdaP2 hx hN

/-! ### Closure under conversion of the type -/

/-- The base predicate is closed under conversion of the type. -/
theorem NormNW.convType {P : Specification Srt} {Γ : List (Expr Srt)} {M T T₂ : Expr Srt}
    (h : NormNW P Γ M T) (hc : Converts T T₂) : NormNW P Γ M T₂ := by
  obtain ⟨Γ', M', T', hcx, hM, hT, hNW⟩ := h
  obtain ⟨J, hTJ, hT₂J⟩ := Converts.join hc
  obtain ⟨K, hT'K, hJK⟩ := Reduces.confluent hT hTJ
  have hK : T' = K := hNW.normal.2.1.reduces_eq hT'K
  subst hK
  exact ⟨Γ', M', T', hcx, hM, hT₂J.trans hJK, hNW⟩

theorem NeNW.convType {P : Specification Srt} {Γ : List (Expr Srt)} {M T T₂ : Expr Srt}
    (h : NeNW P Γ M T) (hc : Converts T T₂) : NeNW P Γ M T₂ := by
  obtain ⟨Γ', M', T', hcx, hM, hT, hNW, hne⟩ := h
  obtain ⟨Γ'', M'', T'', h1, h2, h3, h4⟩ :=
    NormNW.convType (P := P) ⟨Γ', M', T', hcx, hM, hT, hNW⟩ hc
  have hM'' : M' = M'' := Reduces.normal_unique hM h2 hNW.normal.1 h4.normal.1
  subst hM''
  exact ⟨Γ'', M', T'', h1, h2, h3, h4, hne⟩

/-! ### Weakening of neutral normalization along a context prefix -/

theorem neutral_rename {M : Expr Srt} (h : Neutral M) (ρ : ℕ → ℕ) : Neutral (M.rename ρ) := by
  induction h with
  | var n => exact .var _
  | app _ ih => exact .app ih

theorem wk_nil : wk ([] : List (Expr Srt)) = id := by funext n; simp [wk]

/-- The weakening renaming along a prefix is a declaration renaming. -/
theorem declRenaming_wk (Γ : List (Expr Srt)) :
    ∀ (Γ₀ : List (Expr Srt)), TypingTree.DeclRenaming Γ (Γ₀ ++ Γ) (wk Γ₀)
  | [] => by
      intro n A hn
      rw [wk_nil, Expr.rename_id]
      exact hn
  | B :: Γ₀ => by
      intro n A hn
      have h := Lookup.succ B (declRenaming_wk Γ Γ₀ n A hn)
      have he : wk (B :: Γ₀) = Nat.succ ∘ wk Γ₀ := by
        funext n; simp [wk, Function.comp]; omega
      rw [Expr.rename_comp, ← he] at h
      have hn' : wk Γ₀ n + 1 = wk (B :: Γ₀) n := by simp [wk]; omega
      rw [hn'] at h
      exact h

/-- Splitting a pointwise reduction of an appended context. -/
theorem forall₂_reduces_append_split :
    ∀ (Γ₀ Γ Δ : List (Expr Srt)), List.Forall₂ Reduces (Γ₀ ++ Γ) Δ →
      ∃ Γ₀' Γ', Δ = Γ₀' ++ Γ' ∧ Γ₀'.length = Γ₀.length ∧ List.Forall₂ Reduces Γ Γ'
  | [], _, Δ, h => ⟨[], Δ, rfl, rfl, h⟩
  | _ :: Γ₀, Γ, _, h => by
      cases h with
      | @cons _ A' _ Δ' _ h =>
          obtain ⟨Γ₀', Γ', rfl, hl, h'⟩ := forall₂_reduces_append_split Γ₀ Γ Δ' h
          exact ⟨A' :: Γ₀', Γ', rfl, by simp [hl], h'⟩

/-- **Weakening of neutral normalization** along a context prefix whose extension normalizes to
a canonical context. -/
theorem NeNW.weaken {P : Specification Srt} {Γ : List (Expr Srt)} {F T : Expr Srt}
    (h : NeNW P Γ F T) (Γ₀ : List (Expr Srt)) {Δ : List (Expr Srt)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Γ) Δ) (hv : ValidContextNW P Δ) :
    NeNW P (Γ₀ ++ Γ) (F.rename (wk Γ₀)) (T.rename (wk Γ₀)) := by
  obtain ⟨Γ', F', T', hc', hF, hT, hNW, hne⟩ := h
  obtain ⟨Γ₀', Γ₃, rfl, hl, h₃⟩ := forall₂_reduces_append_split Γ₀ Γ Δ hc
  have hΓ : Γ₃ = Γ' := forall₂_reduces_unique h₃ hc'
    (fun X hX => hv.normal_entries X (List.mem_append_right _ hX)) hNW.normal.2.2
  subst hΓ
  have hwk : wk Γ₀ = wk Γ₀' := by funext n; simp [wk, hl]
  refine ⟨Γ₀' ++ Γ₃, F'.rename (wk Γ₀), T'.rename (wk Γ₀), hc, hF.rename _, hT.rename _, ?_,
    neutral_rename hne _⟩
  rw [hwk]
  exact hNW.rename hv _ (declRenaming_wk Γ₃ Γ₀')

/-- **CR3 at neutral applications in a context extension** (the Kripke form used by the
reflection lemmas). -/
theorem NeNW.app_wk (f : CubeFeatures) {Γ : List (Expr Srt)} {F T N A B : Expr Srt}
    (hF : NeNW (cubeSpec f) Γ F T) (Γ₀ : List (Expr Srt))
    (hT : Reduces (T.rename (wk Γ₀)) (.pi A B)) (hN : NormNW (cubeSpec f) (Γ₀ ++ Γ) N A) :
    NeNW (cubeSpec f) (Γ₀ ++ Γ) (.app (F.rename (wk Γ₀)) N) (B.instantiate N) := by
  obtain ⟨Δ, N', A', hc, hN', hA', hNW⟩ := hN
  have hw := hF.weaken Γ₀ hc hNW.valid
  exact NeNW.app f (hw.convType (Reduces.converts hT)) ⟨Δ, N', A', hc, hN', hA', hNW⟩

/-! ### The two-level relation: candidates with CR3, and type reducibility -/

/-- **Candidates of the two-level relation** (for λP2): normalizable judgements, closed under
conversion of the type, containing every neutral normalizable judgement (CR3). -/
structure IsCandN (C : Cand) : Prop where
  norm : ∀ {Γ M T}, C Γ M T → NormNW P2 Γ M T
  conv : ∀ {Γ M T T'}, C Γ M T → Converts T T' → C Γ M T'
  neutral : ∀ {Γ M T}, NeNW P2 Γ M T → C Γ M T
  expand : ∀ {Γ M M' T}, Reduces M M' → C Γ M' T → C Γ M T

/-- The base candidate: normalizable judgements. -/
theorem isCandN_normNW : IsCandN (NormNW P2) where
  norm h := h
  conv h hc := h.convType hc
  neutral h := h.toNormNW
  expand hr h := NormNW.expand hr h

/-- **Type reducibility** of a constructor `U` at a λP2 kind `K` (the judgement `Γ ⊢ U : K`),
relative to the **semantic kind** `Cs`: the candidates interpreting the domains `A₁ … Aₙ` of
`K = Π x₁:A₁ … Π xₙ:Aₙ. ∗`.  At `∗` the constructor normalizes; at a product, applied to every
argument in the candidate of the domain, in every context extension, it is reducible at the
codomain.  Environment free. -/
def TRed : List Cand → Cand
  | [], Γ, U, K => NormNW P2 Γ U K
  | C :: Cs, Γ, U, K => NormNW P2 Γ U K ∧
      ∀ (Γ₀ : List (Expr Srt)) (N A K' : Expr Srt),
        Reduces (K.rename (wk Γ₀)) (.pi A K') → C (Γ₀ ++ Γ) N A →
        TRed Cs (Γ₀ ++ Γ) (.app (U.rename (wk Γ₀)) N) (K'.instantiate N)

/-- **CR1 for type reducibility.** -/
theorem TRed.escape : ∀ {Cs : List Cand} {Γ : List (Expr Srt)} {U K : Expr Srt},
    TRed Cs Γ U K → NormNW P2 Γ U K
  | [], _, _, _, h => h
  | _ :: _, _, _, _, h => h.1

/-- **CR3 for type reducibility**: a neutral normalizable constructor is type reducible at every
semantic kind whose candidates are candidates. -/
theorem TRed.reflect : ∀ {Cs : List Cand}, (∀ C ∈ Cs, IsCandN C) →
    ∀ {Γ : List (Expr Srt)} {U K : Expr Srt}, NeNW P2 Γ U K → TRed Cs Γ U K
  | [], _, _, _, _, h => h.toNormNW
  | C :: Cs, hCs, _, _, _, h => by
      refine ⟨h.toNormNW, fun Γ₀ N A K' hK hN => ?_⟩
      have hC := hCs C (List.mem_cons_self ..)
      exact TRed.reflect (fun C' hC' => hCs C' (List.mem_cons_of_mem _ hC'))
        (NeNW.app_wk lambdaP2 h Γ₀ hK (hC.norm hN))

/-- Type reducibility is closed under reduction of the kind. -/
theorem TRed.reduceKind : ∀ {Cs : List Cand} {Γ : List (Expr Srt)} {U K K₂ : Expr Srt},
    TRed Cs Γ U K → Reduces K K₂ → TRed Cs Γ U K₂
  | [], _, _, _, _, h, hr => h.reduceType hr
  | _ :: _, _, _, _, _, h, hr => ⟨h.1.reduceType hr, fun Γ₀ N A K' hK hN =>
      h.2 Γ₀ N A K' ((hr.rename _).trans hK) hN⟩

/-- **The family-application case at the type level**: a type-reducible family applied to an
argument in the candidate of its domain is type reducible at the instantiated codomain; the
clause of `TRed` supplies it, with no hereditary substitution. -/
theorem TRed.app {C : Cand} {Cs : List Cand} {Γ : List (Expr Srt)} {U A K' N : Expr Srt}
    (h : TRed (C :: Cs) Γ U (.pi A K')) (hN : C Γ N A) :
    TRed Cs Γ (.app U N) (K'.instantiate N) := by
  have := h.2 [] N A K' (by rw [wk_nil, Expr.rename_id]) hN
  simpa [wk_nil, Expr.rename_id] using this

/-- **Constructor variables are type reducible**: a constructor variable whose judgement
normalizes is type reducible at every semantic kind (CR3 at variables; the step used by the
identity substitution). -/
theorem TRed.var {Cs : List Cand} (hCs : ∀ C ∈ Cs, IsCandN C) {Γ : List (Expr Srt)} {x : ℕ}
    {K : Expr Srt} (h : NormNW P2 Γ (.var x) K) : TRed Cs Γ (.var x) K :=
  TRed.reflect hCs (NeNW.of_var h)

/-! ### The term level: skeletons whose quantifier records the semantic kind -/

mutual
/-- **λP2 skeletons of types**: type variables, arrows (object quantification `(∗,∗)`), and the
impredicative quantifier `(□,∗)` over a constructor variable whose kind has the kind skeleton
`κ` (the skeletons of the domains `A₁ … Aₙ` of `Π x₁:A₁ … Π xₙ:Aₙ. ∗`). -/
inductive SkP where
  | base : ℕ → SkP
  | arr : SkP → SkP → SkP
  | all : KSkP → SkP → SkP

/-- Kind skeletons: the list of domain skeletons of a λP2 kind. -/
inductive KSkP where
  | star : KSkP
  | pi : SkP → KSkP → KSkP
end

mutual
/-- **Term reducibility** relative to an assignment `ξ` of candidates to the type variables:
at an arrow, Kripke closure under application to reducible arguments; at the quantifier over a
constructor variable of kind skeleton `κ`, closure under application to every **type-reducible**
constructor (at the semantic kind `⟦κ⟧ξ`), for every candidate interpreting the bound variable. -/
def GoodP : SkP → (ℕ → Cand) → Cand
  | .base i, ξ => ξ i
  | .arr σ τ, ξ => fun Γ M T => NormNW P2 Γ M T ∧
      ∀ (Γ₀ : List (Expr Srt)) (N A B : Expr Srt),
        Reduces (T.rename (wk Γ₀)) (.pi A B) → GoodP σ ξ (Γ₀ ++ Γ) N A →
        GoodP τ ξ (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) N) (B.instantiate N)
  | .all κ τ, ξ => fun Γ M T => NormNW P2 Γ M T ∧
      ∀ (Γ₀ : List (Expr Srt)) (U K B : Expr Srt) (C : Cand), IsCandN C →
        Reduces (T.rename (wk Γ₀)) (.pi K B) → TRed (KSem κ ξ) (Γ₀ ++ Γ) U K →
        GoodP τ (consC C ξ) (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) U) (B.instantiate U)

/-- The semantic kind of a kind skeleton: the candidates of its domains. -/
def KSem : KSkP → (ℕ → Cand) → List Cand
  | .star, _ => []
  | .pi σ κ, ξ => GoodP σ ξ :: KSem κ ξ
end

theorem consC_isCandN {C : Cand} {ξ : ℕ → Cand} (hC : IsCandN C) (hξ : ∀ i, IsCandN (ξ i)) :
    ∀ i, IsCandN (consC C ξ i)
  | 0 => hC
  | i + 1 => hξ i

/-- A conversion `T ≡ Π A B` is a reduction `T ↠ Π A₂ B₂` with `A ↠ A₂` and `B ↠ B₂`. -/
theorem converts_pi_reduces {T A B : Expr Srt} (h : Converts T (.pi A B)) :
    ∃ A₂ B₂, Reduces T (.pi A₂ B₂) ∧ Reduces A A₂ ∧ Reduces B B₂ := by
  obtain ⟨J, hTJ, hPJ⟩ := Converts.join h
  obtain ⟨A₂, B₂, rfl, hA, hB⟩ := Reduces.pi_inv hPJ
  exact ⟨A₂, B₂, hTJ, hA, hB⟩

theorem converts_symm {M N : Expr Srt} (h : Converts M N) : Converts N M :=
  Relation.EqvGen.symm _ _ h

theorem converts_trans {M N K : Expr Srt} (h₁ : Converts M N) (h₂ : Converts N K) :
    Converts M K :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem converts_rename {M N : Expr Srt} (h : Converts M N) (ρ : ℕ → ℕ) :
    Converts (M.rename ρ) (N.rename ρ) :=
  Converts.rename h ρ

mutual
/-- **CR1–CR3 for term reducibility**: every `GoodP s ξ` is a candidate, given candidates for
the type variables. -/
theorem GoodP.isCandN : ∀ (s : SkP) (ξ : ℕ → Cand), (∀ i, IsCandN (ξ i)) → IsCandN (GoodP s ξ)
  | .base i, _, hξ => hξ i
  | .arr σ τ, ξ, hξ => by
      have hσ := GoodP.isCandN σ ξ hξ
      have hτ := GoodP.isCandN τ ξ hξ
      refine ⟨fun h => h.1, fun {Γ M T T'} h hc => ⟨h.1.convType hc, ?_⟩, fun {Γ M T} h => ?_,
        fun {Γ M M' T} hr h => ⟨NormNW.expand hr h.1, fun Γ₀ N A B hT hN =>
          hτ.expand (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ N A B hT hN)⟩⟩
      · intro Γ₀ N A B hT' hN
        have hc' : Converts (T.rename (wk Γ₀)) (.pi A B) :=
          converts_trans (converts_rename hc _) (Reduces.converts hT')
        obtain ⟨A₂, B₂, hT₂, hA₂, hB₂⟩ := converts_pi_reduces hc'
        have := h.2 Γ₀ N A₂ B₂ hT₂ (hσ.conv hN (Reduces.converts hA₂))
        exact hτ.conv this (converts_symm (Reduces.converts (Reduces.instantiate hB₂ .refl)))
      · refine ⟨h.toNormNW, fun Γ₀ N A B hT hN => ?_⟩
        exact hτ.neutral (NeNW.app_wk lambdaP2 h Γ₀ hT (hσ.norm hN))
  | .all κ τ, ξ, hξ => by
      refine ⟨fun h => h.1, fun {Γ M T T'} h hc => ⟨h.1.convType hc, ?_⟩, fun {Γ M T} h => ?_,
        fun {Γ M M' T} hr h => ⟨NormNW.expand hr h.1, fun Γ₀ U K B C hC hT hU =>
          (GoodP.isCandN τ (consC C ξ) (consC_isCandN hC hξ)).expand
            (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ U K B C hC hT hU)⟩⟩
      · intro Γ₀ U K B C hC hT' hU
        have hτ := GoodP.isCandN τ (consC C ξ) (consC_isCandN hC hξ)
        have hc' : Converts (T.rename (wk Γ₀)) (.pi K B) :=
          converts_trans (converts_rename hc _) (Reduces.converts hT')
        obtain ⟨K₂, B₂, hT₂, hK₂, hB₂⟩ := converts_pi_reduces hc'
        have := h.2 Γ₀ U K₂ B₂ C hC hT₂ (hU.reduceKind hK₂)
        exact hτ.conv this (converts_symm (Reduces.converts (Reduces.instantiate hB₂ .refl)))
      · refine ⟨h.toNormNW, fun Γ₀ U K B C hC hT hU => ?_⟩
        have hτ := GoodP.isCandN τ (consC C ξ) (consC_isCandN hC hξ)
        exact hτ.neutral (NeNW.app_wk lambdaP2 h Γ₀ hT hU.escape)

/-- The domains of a semantic kind are candidates. -/
theorem KSem.isCandN : ∀ (κ : KSkP) (ξ : ℕ → Cand), (∀ i, IsCandN (ξ i)) →
    ∀ C ∈ KSem κ ξ, IsCandN C
  | .star, _, _ => by intro C hC; simp [KSem] at hC
  | .pi σ κ, ξ, hξ => by
      intro C hC
      simp only [KSem, List.mem_cons] at hC
      rcases hC with rfl | hC
      · exact GoodP.isCandN σ ξ hξ
      · exact KSem.isCandN κ ξ hξ C hC
end

/-- **CR3 for term reducibility at variables**: a variable whose judgement normalizes is
reducible at every skeleton.  With `TRed.var`, this makes the identity substitution reducible
in every context whose declarations normalize. -/
theorem GoodP.var {s : SkP} {ξ : ℕ → Cand} (hξ : ∀ i, IsCandN (ξ i)) {Γ : List (Expr Srt)}
    {x : ℕ} {T : Expr Srt} (h : NormNW P2 Γ (.var x) T) : GoodP s ξ Γ (.var x) T :=
  (GoodP.isCandN s ξ hξ).neutral (NeNW.of_var h)

/-- **The type-application case `(□,∗)`** of the fundamental lemma, at the term level: a
reducible judgement at `∀κ. τ` applied to a type-reducible constructor `U` is reducible at `τ`
with the bound variable interpreted by any candidate `C`. -/
theorem GoodP.tyApp {κ : KSkP} {τ : SkP} {ξ : ℕ → Cand} {Γ : List (Expr Srt)}
    {M K B U : Expr Srt} {C : Cand} (hC : IsCandN C) (h : GoodP (.all κ τ) ξ Γ M (.pi K B))
    (hU : TRed (KSem κ ξ) Γ U K) :
    GoodP τ (consC C ξ) Γ (.app M U) (B.instantiate U) := by
  have := h.2 [] U K B C hC (by rw [wk_nil, Expr.rename_id]) (by simpa using hU)
  simpa [wk_nil, Expr.rename_id] using this

/-- **The object-application case `(∗,∗)`** at the term level. -/
theorem GoodP.app {σ τ : SkP} {ξ : ℕ → Cand} {Γ : List (Expr Srt)} {M A B N : Expr Srt}
    (h : GoodP (.arr σ τ) ξ Γ M (.pi A B)) (hN : GoodP σ ξ Γ N A) :
    GoodP τ ξ Γ (.app M N) (B.instantiate N) := by
  have := h.2 [] N A B (by rw [wk_nil, Expr.rename_id]) (by simpa using hN)
  simpa [wk_nil, Expr.rename_id] using this

/-- **Type reducibility is closed under expansion of the constructor.** -/
theorem TRed.expand : ∀ {Cs : List Cand} {Γ : List (Expr Srt)} {U U' K : Expr Srt},
    Reduces U U' → TRed Cs Γ U' K → TRed Cs Γ U K
  | [], _, _, _, _, hr, h => NormNW.expand hr h
  | _ :: _, _, _, _, _, hr, h => ⟨NormNW.expand hr h.1, fun Γ₀ N A K' hK hN =>
      TRed.expand (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ N A K' hK hN)⟩

/-- **The abstraction case at an arrow skeleton**: an abstraction whose instantiated bodies are
reducible at every reducible argument is reducible (closure under β-expansion). -/
theorem GoodP.lam_arr {σ τ : SkP} {ξ : ℕ → Cand} (hξ : ∀ i, IsCandN (ξ i))
    {Γ : List (Expr Srt)} {D b T : Expr Srt} (hn : NormNW P2 Γ (.lam D b) T)
    (hb : ∀ (Γ₀ : List (Expr Srt)) (N A B : Expr Srt),
      Reduces (T.rename (wk Γ₀)) (.pi A B) → GoodP σ ξ (Γ₀ ++ Γ) N A →
      GoodP τ ξ (Γ₀ ++ Γ) ((b.rename (Expr.liftRen (wk Γ₀))).instantiate N) (B.instantiate N)) :
    GoodP (.arr σ τ) ξ Γ (.lam D b) T :=
  ⟨hn, fun Γ₀ N A B hT hN => (GoodP.isCandN τ ξ hξ).expand
    (.single (Beta.head _ _ _)) (hb Γ₀ N A B hT hN)⟩

/-! ### The interpretation commutes with renaming and substitution of `SkP` skeletons -/

mutual
def SkP.rename (r : ℕ → ℕ) : SkP → SkP
  | .base i => .base (r i)
  | .arr σ τ => .arr (σ.rename r) (τ.rename r)
  | .all κ τ => .all (κ.rename r) (τ.rename (upR r))

def KSkP.rename (r : ℕ → ℕ) : KSkP → KSkP
  | .star => .star
  | .pi σ κ => .pi (σ.rename r) (κ.rename r)
end

/-- Lifting a substitution of `SkP` skeletons under a binder. -/
def upSP (σ : ℕ → SkP) : ℕ → SkP
  | 0 => .base 0
  | i + 1 => (σ i).rename Nat.succ

mutual
def SkP.subst (σ : ℕ → SkP) : SkP → SkP
  | .base i => σ i
  | .arr s t => .arr (s.subst σ) (t.subst σ)
  | .all κ t => .all (κ.subst σ) (t.subst (upSP σ))

def KSkP.subst (σ : ℕ → SkP) : KSkP → KSkP
  | .star => .star
  | .pi s κ => .pi (s.subst σ) (κ.subst σ)
end

/-- The substitution of `t` for the variable `0`. -/
def singleP (t : SkP) : ℕ → SkP
  | 0 => t
  | i + 1 => .base i

mutual
theorem GoodP_rename : ∀ (s : SkP) (r : ℕ → ℕ) (ξ : ℕ → Cand),
    GoodP (s.rename r) ξ = GoodP s (fun i => ξ (r i))
  | .base _, _, _ => by simp only [SkP.rename, GoodP]
  | .arr σ τ, r, ξ => by
      simp only [SkP.rename, GoodP, GoodP_rename σ r ξ, GoodP_rename τ r ξ]
  | .all κ τ, r, ξ => by
      simp only [SkP.rename, GoodP, KSem_rename κ r ξ]
      funext Γ M T
      congr 1
      apply propext
      refine forall_congr' fun Γ₀ => forall_congr' fun U => forall_congr' fun K =>
        forall_congr' fun B => forall_congr' fun C => ?_
      rw [GoodP_rename τ (upR r) (consC C ξ), consC_comp_upR]

theorem KSem_rename : ∀ (κ : KSkP) (r : ℕ → ℕ) (ξ : ℕ → Cand),
    KSem (κ.rename r) ξ = KSem κ (fun i => ξ (r i))
  | .star, _, _ => by simp only [KSkP.rename, KSem]
  | .pi σ κ, r, ξ => by
      simp only [KSkP.rename, KSem, GoodP_rename σ r ξ, KSem_rename κ r ξ]
end

theorem consC_upSP (C : Cand) (ξ : ℕ → Cand) (σ : ℕ → SkP) :
    (fun i => GoodP (upSP σ i) (consC C ξ)) = consC C (fun i => GoodP (σ i) ξ) := by
  funext i
  cases i with
  | zero => simp only [upSP, GoodP]; rfl
  | succ i => simp only [upSP, GoodP_rename]; rfl

mutual
/-- **The interpretation commutes with substitution of skeletons**:
`⟦s[σ]⟧ξ = ⟦s⟧(i ↦ ⟦σ i⟧ξ)`, for the two-level skeletons. -/
theorem GoodP_subst : ∀ (s : SkP) (σ : ℕ → SkP) (ξ : ℕ → Cand),
    GoodP (s.subst σ) ξ = GoodP s (fun i => GoodP (σ i) ξ)
  | .base _, _, _ => by simp only [SkP.subst, GoodP]
  | .arr s t, σ, ξ => by
      simp only [SkP.subst, GoodP, GoodP_subst s σ ξ, GoodP_subst t σ ξ]
  | .all κ τ, σ, ξ => by
      simp only [SkP.subst, GoodP, KSem_subst κ σ ξ]
      funext Γ M T
      congr 1
      apply propext
      refine forall_congr' fun Γ₀ => forall_congr' fun U => forall_congr' fun K =>
        forall_congr' fun B => forall_congr' fun C => ?_
      rw [GoodP_subst τ (upSP σ) (consC C ξ), consC_upSP]

theorem KSem_subst : ∀ (κ : KSkP) (σ : ℕ → SkP) (ξ : ℕ → Cand),
    KSem (κ.subst σ) ξ = KSem κ (fun i => GoodP (σ i) ξ)
  | .star, _, _ => by simp only [KSkP.subst, KSem]
  | .pi s κ, σ, ξ => by
      simp only [KSkP.subst, KSem, GoodP_subst s σ ξ, KSem_subst κ σ ξ]
end

/-- The instance used at `(□,∗)`: `⟦τ[t/X]⟧ξ = ⟦τ⟧(ξ, X ↦ ⟦t⟧ξ)`. -/
theorem GoodP_inst (τ t : SkP) (ξ : ℕ → Cand) :
    GoodP (τ.subst (singleP t)) ξ = GoodP τ (consC (GoodP t ξ) ξ) := by
  rw [GoodP_subst]
  congr 1
  funext i
  cases i <;> rfl

/-- **The type-application case `(□,∗)` with the substituted skeleton**: a reducible judgement
at `∀κ. τ` applied to a constructor `U` type-reducible at `⟦κ⟧ξ` is reducible at `τ[t/X]` for
every skeleton `t` (in the fundamental lemma, the skeleton of `U`). -/
theorem GoodP.tyApp_subst {κ : KSkP} {τ : SkP} {ξ : ℕ → Cand} (hξ : ∀ i, IsCandN (ξ i))
    {Γ : List (Expr Srt)} {M K B U : Expr Srt} (t : SkP)
    (h : GoodP (.all κ τ) ξ Γ M (.pi K B)) (hU : TRed (KSem κ ξ) Γ U K) :
    GoodP (τ.subst (singleP t)) ξ Γ (.app M U) (B.instantiate U) := by
  rw [GoodP_inst]
  exact GoodP.tyApp (GoodP.isCandN t ξ hξ) h hU

end RouteII

end PureTypeSystem
