import Start.PTSExpansionTopClassify
import Start.PTSSyntaxDirected

/-!
# Series V, round 3, run 1, part B1: `TopSkel.classifyV` (row M29-EP-TOP-SORT-FUNDAMENTAL)

The classification of `cocTop` judgements with skeleton variables, the `cocTop` analogue of
`CoC.classify`: kinds are classified as kinds (`kindV_cl`; a kind variable `K : □` has the
skeleton variable of its level), expressions with a sorted type are never kinds (`notKindV`),
kinds keep their class under conversion (`kindV_conv`: a kind variable is convertible only to
itself), every typed expression is classified by its type (`classifyFull`) and is
well-classified (`wcv_of_hasType`), and finally:

* **`classifyV`** — `WCV (ctxClV Γ) M ∧ ∀ k, clV (ctxClV Γ) M = .constr k → clV (ctxClV Γ) T = .kind k`;
* `clV_beta`, `clV_reduces` — the classification is stable under reduction (`CoC.cl_beta`).

The interpretation over `VV θ` (`interpK` with skeleton variables) and the generalized fundamental
lemma are **not** done here; the first missing lemma is `TopSkel.interpV_beta`, the analogue of
`CoC.interp_beta` for the interpretation relative to a skeleton valuation `θ` (see
`docs/goal/evidence/M29-EP.md`, "Series V, round 3, run 1").
-/

set_option autoImplicit false

namespace PureTypeSystem.TopSkel

open CoC (ncons)

theorem rename_eq_sort {A : Expr Srt3} {ρ : Nat → Nat} {s : Srt3} (h : A.rename ρ = .sort s) :
    A = .sort s := by
  cases A with
  | sort t => exact h
  | var _ => cases h
  | app _ _ => cases h
  | lam _ _ => cases h
  | pi _ _ => cases h

theorem cocTop_functional : Functional cocTop := by
  refine ⟨fun s t t' h1 h2 => ?_, fun s₁ s₂ s₃ s₃' h1 h2 => h1.1.trans h2.1.symm⟩
  simp only [cocTop] at h1 h2
  rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨h, rfl⟩ | ⟨h, rfl⟩ <;>
    first | rfl | cases h

theorem sort_unique_conv {Γ : List (Expr Srt3)} {A B : Expr Srt3} {s t : Srt3}
    (hA : HasType cocTop Γ A (.sort s)) (hB : HasType cocTop Γ B (.sort t))
    (hc : Converts A B) : s = t := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  exact Converts.sort_inj (HasType.type_unique_of_functional cocTop_functional
    (hA.subject_reduces hAC) (hB.subject_reduces hBC))

theorem box_typed {Γ : List (Expr Srt3)} {T : Expr Srt3} (h : HasType cocTop Γ (.sort .box) T) :
    Converts T (.sort .top) := by
  obtain ⟨t, ht, hc⟩ := h.generation
  simp only [cocTop] at ht
  rcases ht with ⟨h1, _⟩ | ⟨_, rfl⟩
  · cases h1
  · exact hc

theorem box_sort {Γ : List (Expr Srt3)} {s : Srt3} (h : HasType cocTop Γ (.sort .box) (.sort s)) :
    s = .top :=
  Converts.sort_inj (box_typed h)

theorem star_typed {Γ : List (Expr Srt3)} {T : Expr Srt3} (h : HasType cocTop Γ (.sort .star) T) :
    Converts T (.sort .box) := by
  obtain ⟨t, ht, hc⟩ := h.generation
  simp only [cocTop] at ht
  rcases ht with ⟨_, rfl⟩ | ⟨h1, _⟩
  · exact hc
  · cases h1

theorem ne_box_of_sorted {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) : A ≠ .sort .box := by
  rintro rfl; exact hs (box_sort h)

theorem star_box {Γ : List (Expr Srt3)} (hΓ : ValidContext cocTop Γ) :
    HasType cocTop Γ (.sort .star) (.sort .box) :=
  HasType.sort_of_valid hΓ (.inl ⟨rfl, rfl⟩)

/-- A sorted type of sort other than `Δ` is not `□`, hence not convertible to `□`. -/
theorem not_conv_box_of_sorted {Γ : List (Expr Srt3)} {T : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ T (.sort s)) (hs : s ≠ .top) (hc : Converts T (.sort .box)) : False :=
  ne_box_of_sorted h hs (eq_box_of_conv h hc)

theorem bindV_ne_kind (c : ClsV) (a : SkV) : bindV c ≠ .kind a := by
  cases c <;> simp [bindV]

theorem appV_ne_kind (c : ClsV) (a : SkV) : appV c ≠ .kind a := by
  unfold appV; split <;> simp

theorem lamV_ne_kind (c d : ClsV) (a : SkV) : lamV c d ≠ .kind a := by
  cases d <;> simp [lamV]

theorem ctxClV_kind_lookup : ∀ {Γ : List (Expr Srt3)} {n : Nat} {D : Expr Srt3}, Lookup Γ n D →
    ∀ {k : SkV}, ctxClV Γ n = .kind k → D = .sort .box
  | _, _, _, .zero A Γ, k, h => by
      by_cases hA : A = .sort .box
      · subst hA; rfl
      · simp only [ctxClV, hA, if_false] at h
        exact (bindV_ne_kind _ _ h).elim
  | _, _, _, .succ B hD, k, h => by
      rw [ctxClV_kind_lookup hD h]; rfl

theorem ctxClV_of_lookup_box : ∀ {Γ : List (Expr Srt3)} {n : Nat} {D : Expr Srt3}, Lookup Γ n D →
    D = .sort .box → ∃ ℓ, ctxClV Γ n = .kind (.svar ℓ)
  | _, _, _, .zero A Γ, e => by
      have hA := rename_eq_sort e
      subst hA
      exact ⟨Γ.length, by simp [ctxClV]⟩
  | _, _, _, .succ B hD, e => by
      obtain ⟨ℓ, h⟩ := ctxClV_of_lookup_box hD (rename_eq_sort e)
      exact ⟨ℓ, h⟩

theorem rule_dom {s₁ s₂ s₃ : Srt3} (h : cocTop.rule s₁ s₂ s₃) : s₁ ≠ .top := h.2.1

theorem rule_cod {s₁ s₂ s₃ : Srt3} (h : cocTop.rule s₁ s₂ s₃) : s₂ ≠ .top := h.2.2

/-! ### Kinds -/

/-- **Kinds are classified as kinds.** -/
theorem kindV_cl {Γ : List (Expr Srt3)} {M : Expr Srt3}
    (h : HasType cocTop Γ M (.sort .box)) : ∃ k, clV (ctxClV Γ) M = .kind k := by
  induction M generalizing Γ with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      obtain ⟨s, hs⟩ := HasType.lookup_sorted h.valid hD
      have hDb := eq_box_of_conv hs (.symm _ _ hc)
      obtain ⟨ℓ, hℓ⟩ := ctxClV_of_lookup_box hD hDb
      exact ⟨_, hℓ⟩
  | sort s =>
      cases s with
      | star => exact ⟨.star, rfl⟩
      | box => exact absurd (Converts.sort_inj (box_typed h)) (by simp)
      | top => exact (top_untypable h).elim
  | app F a _ _ =>
      obtain ⟨A, B, hF, ha, hc⟩ := h.generation_app
      obtain ⟨s, hPi⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, _⟩ := hPi.generation_pi
      have hBa := hB.instantiate ha
      simp only [Expr.instantiate, Expr.subst] at hBa
      have e := eq_box_of_conv hBa (.symm _ _ hc)
      exact absurd (box_sort (e ▸ hBa)) (rule_cod hr)
  | lam A b _ _ =>
      obtain ⟨B, s, _, _, hc⟩ := h.generation_lam
      exact (Converts.pi_not_sort (.symm _ _ hc)).elim
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      have h₃ : s₃ = .box := (Converts.sort_inj hc).symm
      have h₂ : s₂ = .box := hr.1 ▸ h₃
      subst h₂
      obtain ⟨k, hk⟩ := ihB hB
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at hk
      exact ⟨domV (clV (ctxClV Γ) A) k, by simp only [clV, hk, piV]⟩

/-- **Expressions whose type is sorted (below `Δ`) are never kinds.** -/
theorem notKindV {Γ : List (Expr Srt3)} {M T : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ M T) (hT : HasType cocTop Γ T (.sort s)) (hs : s ≠ .top) :
    ∀ k, clV (ctxClV Γ) M ≠ .kind k := by
  induction M generalizing Γ T s with
  | var n =>
      intro k hk
      obtain ⟨D, hD, hc⟩ := h.generation
      have hDb := ctxClV_kind_lookup hD hk
      subst hDb
      exact not_conv_box_of_sorted hT hs hc
  | sort s' =>
      cases s' with
      | star => exact fun _ _ => not_conv_box_of_sorted hT hs (star_typed h)
      | box => intro k; simp [clV]
      | top => exact (top_untypable h).elim
  | app F a _ _ => exact appV_ne_kind _
  | lam A b _ _ => exact lamV_ne_kind _ _
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      cases s₃ with
      | box => exact (not_conv_box_of_sorted hT hs hc).elim
      | top => exact (rule_cod hr (hr.1 ▸ rfl)).elim
      | star =>
          have h₂ : s₂ = .star := hr.1.symm
          subst h₂
          have hnk := ihB hB (star_box hB.valid) (by simp)
          rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at hnk
          intro k
          simp only [clV]
          generalize clV (ncons (bindV (clV (ctxClV Γ) A)) (ctxClV Γ)) B = c at hnk
          cases c with
          | kind a => exact absurd rfl (hnk a)
          | constr _ => simp [piV]
          | obj => simp [piV]

theorem bindV_eq_of_not_kind {c c' : ClsV} (h : ∀ k, c ≠ .kind k) (h' : ∀ k, c' ≠ .kind k) :
    bindV c = bindV c' := by
  cases c with
  | kind a => exact absurd rfl (h a)
  | constr _ => cases c' with
    | kind a => exact absurd rfl (h' a)
    | _ => rfl
  | obj => cases c' with
    | kind a => exact absurd rfl (h' a)
    | _ => rfl

theorem domV_eq_of_not_kind {c c' : ClsV} (h : ∀ k, c ≠ .kind k) (h' : ∀ k, c' ≠ .kind k)
    (k : SkV) : domV c k = domV c' k := by
  cases c with
  | kind a => exact absurd rfl (h a)
  | constr _ => cases c' with
    | kind a => exact absurd rfl (h' a)
    | _ => rfl
  | obj => cases c' with
    | kind a => exact absurd rfl (h' a)
    | _ => rfl

theorem piV_eq_of_not_kind {c c' : ClsV} (h : ∀ k, c ≠ .kind k) (h' : ∀ k, c' ≠ .kind k)
    (d : ClsV) : piV c d = piV c' d := by
  cases d <;> simp [piV, domV_eq_of_not_kind h h']

/-- The class of a kind is invariant under one β-step. -/
theorem kindV_beta {Γ : List (Expr Srt3)} {K K' : Expr Srt3}
    (h : HasType cocTop Γ K (.sort .box)) (hr : Beta K K') :
    clV (ctxClV Γ) K = clV (ctxClV Γ) K' := by
  induction hr generalizing Γ with
  | head A b a =>
      obtain ⟨k, hk⟩ := kindV_cl h
      exact absurd hk (appV_ne_kind _ _)
  | app_left _ _ =>
      obtain ⟨k, hk⟩ := kindV_cl h
      exact absurd hk (appV_ne_kind _ _)
  | app_right _ _ =>
      obtain ⟨k, hk⟩ := kindV_cl h
      exact absurd hk (appV_ne_kind _ _)
  | lam_domain _ _ =>
      obtain ⟨k, hk⟩ := kindV_cl h
      exact absurd hk (lamV_ne_kind _ _ _)
  | lam_body _ _ =>
      obtain ⟨k, hk⟩ := kindV_cl h
      exact absurd hk (lamV_ne_kind _ _ _)
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, hc⟩ := h.generation_pi
      cases s₁ with
      | box => simp only [clV, ih hA]
      | top => exact (rule_dom hrl rfl).elim
      | star =>
          have hA' := hA.subject_reduction hr
          have hn := notKindV hA (star_box hA.valid) (by simp)
          have hn' := notKindV hA' (star_box hA.valid) (by simp)
          simp only [clV, bindV_eq_of_not_kind hn hn', piV_eq_of_not_kind hn hn']
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, hc⟩ := h.generation_pi
      have h₃ : s₃ = .box := (Converts.sort_inj hc).symm
      have h₂ : s₂ = .box := hrl.1 ▸ h₃
      subst h₂
      have := ih hB
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hrl))] at this
      simp only [clV, this]

theorem kindV_reduces {Γ : List (Expr Srt3)} {K K' : Expr Srt3}
    (h : HasType cocTop Γ K (.sort .box)) (hr : Reduces K K') :
    clV (ctxClV Γ) K = clV (ctxClV Γ) K' := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih => exact ih.trans (kindV_beta (h.subject_reduces hr₁) hr₂)

/-- **Convertible kinds have the same class** (a kind variable is convertible only to itself). -/
theorem kindV_conv {Γ : List (Expr Srt3)} {K K' : Expr Srt3}
    (h : HasType cocTop Γ K (.sort .box)) (h' : HasType cocTop Γ K' (.sort .box))
    (hc : Converts K K') : clV (ctxClV Γ) K = clV (ctxClV Γ) K' := by
  obtain ⟨C, hKC, hK'C⟩ := hc.join
  exact (kindV_reduces h hKC).trans (kindV_reduces h' hK'C).symm

/-! ### The classification -/

theorem lamV_bindV (cA c : ClsV) : lamV cA (bindV c) = bindV (piV cA c) := by
  cases c <;> rfl

theorem appV_bindV_piV (cA c : ClsV) : appV (bindV (piV cA c)) = bindV c := by
  cases c with
  | kind k => cases cA <;> rfl
  | constr => rfl
  | obj => rfl

theorem not_top_typed {Γ : List (Expr Srt3)} {M T : Expr Srt3} (h : HasType cocTop Γ M T) :
    T ≠ .sort .top ∨ M = .sort .box := by
  by_cases hT : T = .sort .top
  · subst hT
    obtain ⟨s, hs⟩ := cocTop_topMorphism.top_typed_sort h .top rfl rfl
    subst hs
    cases s with
    | box => exact .inr rfl
    | star => exact absurd (Converts.sort_inj (star_typed h)) (by simp)
    | top => exact (top_untypable h).elim
  · exact .inl hT

/-- **The classification**: a typed expression whose type is neither `□` nor `Δ` is classified
by its type. -/
theorem classifyFull {Γ : List (Expr Srt3)} {M T : Expr Srt3} (h : HasType cocTop Γ M T)
    (hT : T ≠ .sort .box) (hT' : T ≠ .sort .top) :
    clV (ctxClV Γ) M = bindV (clV (ctxClV Γ) T) := by
  induction h with
  | @ax s t h =>
      simp only [cocTop] at h
      rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact absurd rfl hT
      · exact absurd rfl hT'
  | @var Γ A s hA _ =>
      by_cases hAb : A = .sort .box
      · subst hAb; exact absurd rfl hT
      · show ctxClV (A :: Γ) 0 = _
        rw [clV_rename, ctxClV_comp_succ]
        simp [ctxClV, hAb]
  | @weaken Γ M B A s hM hA ihM _ =>
      rw [clV_rename, clV_rename, ctxClV_comp_succ]
      exact ihM (fun e => hT (by rw [e]; rfl)) (fun e => hT' (by rw [e]; rfl))
  | @product Γ A B s₁ s₂ s₃ hA hB hr _ _ =>
      cases s₃ with
      | box => exact absurd rfl hT
      | top => exact absurd rfl hT'
      | star =>
          have h₂ : s₂ = .star := hr.1.symm
          subst h₂
          have hnk := notKindV hB (star_box hB.valid) (by simp)
          rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at hnk
          simp only [clV]
          generalize clV (ncons (bindV (clV (ctxClV Γ) A)) (ctxClV Γ)) B = c at hnk
          cases c with
          | kind a => exact absurd rfl (hnk a)
          | constr _ => rfl
          | obj => rfl
  | @abstraction Γ A b B s hb hPi ihb _ =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPi.generation_pi
      have := ihb (ne_box_of_sorted hB (rule_cod hr))
        (fun e => top_untypable (e ▸ hB))
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at this
      simp only [clV, this, lamV_bindV]
  | @application Γ F a A B hF ha ihF iha =>
      obtain ⟨s, hPi⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPi.generation_pi
      have hF' := ihF (by intro h; cases h) (by intro h; cases h)
      have ha' := iha (ne_box_of_sorted hA (rule_dom hr)) (fun e => top_untypable (e ▸ hA))
      simp only [clV] at hF' ⊢
      rw [hF', clV_instantiate, ha', appV_bindV_piV]
  | @conversion Γ M A B s hM hB hc ihM _ =>
      have hA : A ≠ .sort .box := by
        rintro rfl
        exact hT (eq_box_of_conv hB (.symm _ _ hc))
      have hA' : A ≠ .sort .top := by
        rintro rfl
        exact not_conv_top hB (.symm _ _ hc)
      rw [ihM hA hA']
      have hs : s ≠ .top := by
        rintro rfl
        rcases not_top_typed hB with h | h
        · exact h rfl
        · exact hT h
      rcases HasType.regularity hM with ⟨t, rfl⟩ | ⟨s', hA''⟩
      · cases t with
        | box => exact absurd rfl hA
        | top => exact absurd rfl hA'
        | star =>
            have hsb : s = .box := (sort_unique_conv (star_box hB.valid) hB hc).symm
            subst hsb
            rw [kindV_conv (star_box hB.valid) hB hc]
      · have hss := sort_unique_conv hA'' hB hc
        subst hss
        cases s' with
        | box => rw [kindV_conv hA'' hB hc]
        | top => exact absurd rfl hs
        | star =>
            exact bindV_eq_of_not_kind (notKindV hA'' (star_box hA''.valid) (by simp))
              (notKindV hB (star_box hB.valid) (by simp))

/-- Every typed expression is well-classified. -/
theorem wcv_of_hasType {Γ : List (Expr Srt3)} {M T : Expr Srt3} (h : HasType cocTop Γ M T) :
    WCV (ctxClV Γ) M := by
  induction h with
  | ax _ => trivial
  | var _ _ => trivial
  | @weaken Γ M B A s hM hA ihM _ =>
      rw [WCV_rename, ctxClV_comp_succ]; exact ihM
  | @product Γ A B s₁ s₂ s₃ hA hB hr ihA ihB =>
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at ihB
      exact ⟨ihA, ihB⟩
  | @abstraction Γ A b B s hb hPi ihb ihPi =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPi.generation_pi
      rw [ctxClV_cons_of_ne (ne_box_of_sorted hA (rule_dom hr))] at ihb
      exact ⟨ihPi.1, ihb⟩
  | @application Γ F a A B hF ha ihF iha =>
      refine ⟨fun i e => ?_, ihF, iha⟩
      have hF' := classifyFull hF (by intro h; cases h) (by intro h; cases h)
      rw [e] at hF'
      simp only [clV] at hF'
      generalize clV (ncons (bindV (clV (ctxClV Γ) A)) (ctxClV Γ)) B = c at hF'
      cases c with
      | kind k =>
          simp only [piV, bindV] at hF'
          cases hF'' : clV (ctxClV Γ) A <;> rw [hF''] at hF' <;> simp [domV] at hF'
      | constr _ => simp [piV, bindV] at hF'
      | obj => simp [piV, bindV] at hF'
  | conversion _ _ _ ihM _ => exact ihM

/-- **`classifyV`**: the `cocTop` analogue of `CoC.classify` with skeleton variables. -/
theorem classifyV {Γ : List (Expr Srt3)} {M T : Expr Srt3} (h : HasType cocTop Γ M T) :
    WCV (ctxClV Γ) M ∧ ∀ k, clV (ctxClV Γ) M = .constr k → clV (ctxClV Γ) T = .kind k := by
  refine ⟨wcv_of_hasType h, fun k hk => ?_⟩
  by_cases hTb : T = .sort .box
  · subst hTb
    obtain ⟨k', hk'⟩ := kindV_cl h
    rw [hk] at hk'; cases hk'
  rcases not_top_typed h with hTt | rfl
  · have := classifyFull h hTb hTt
    rw [hk] at this
    generalize clV (ctxClV Γ) T = c at this
    cases c with
    | kind a => simp only [bindV] at this; cases this; rfl
    | constr _ => simp [bindV] at this
    | obj => simp [bindV] at this
  · simp [clV] at hk

/-- **The classification is stable under reduction** (`CoC.cl_beta` for `cocTop`). -/
theorem clV_beta {Γ : List (Expr Srt3)} {U U' T : Expr Srt3} (h : HasType cocTop Γ U T)
    (hr : Beta U U') : clV (ctxClV Γ) U = clV (ctxClV Γ) U' := by
  by_cases hTb : T = .sort .box
  · subst hTb; exact kindV_beta h hr
  rcases not_top_typed h with hTt | rfl
  · rw [classifyFull h hTb hTt, classifyFull (h.subject_reduction hr) hTb hTt]
  · cases hr

theorem clV_reduces {Γ : List (Expr Srt3)} {U U' T : Expr Srt3} (h : HasType cocTop Γ U T)
    (hr : Reduces U U') : clV (ctxClV Γ) U = clV (ctxClV Γ) U' := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih => exact ih.trans (clV_beta (h.subject_reduces hr₁) hr₂)

end PureTypeSystem.TopSkel
