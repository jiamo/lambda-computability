import Start.CoCModel
import Start.PTSFOmegaKinds
import Start.PTSHurkens

/-!
# Strong normalization of the calculus of constructions

This library's own module (task `M23-COC-SN`).  Route: Geuvers' saturated-set model ("A short
and flexible proof of strong normalization for the calculus of constructions"), with the
syntactic model of `Start/CoCModel.lean`.  Kinds are interpreted through their skeletons
(`CoC.Sk`), constructors ignore object arguments, and kinds, types and `□` are all interpreted by
saturated sets, so that the fundamental lemma covers kinds and constructors as well as objects.

* `CoC.type_unique` — uniqueness of types up to conversion in every corner of the cube.
* `CoC.classify` — every legal expression is a kind (`CoC.kind_cl`), a constructor or an object,
  and the syntactic classifier `CoC.cl` computes which: `Γ ⊢ M : T`, `T ≠ □` gives
  `cl M = bindC (cl T)`.  The classification is stable under reduction (`CoC.cl_beta`) and under
  substitution (`CoC.cl_subst`, purely syntactic).
* `CoC.interp_beta`, `CoC.interp_conv` — the interpretation of legal kinds and constructors is
  invariant under reduction and conversion.
* `CoC.fundamental` — the fundamental lemma.
* `coc_stronglyNormalizing` — **`SystemStronglyNormalizing (cubeSpec coc)`**, with no hypothesis;
  `cube_stronglyNormalizing` — every corner, by `cube_sn_mono`; `coc_consistent` — no closed
  expression of type `Π α:∗. α`, from strong normalization and `no_normal_closed_bot`.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace CoC

open LambdaPi (Srt)

variable {f : CubeFeatures}

/-! ### Uniqueness of types -/

theorem lookup_unique {Γ : List (Expr Srt)} {n : Nat} {A B : Expr Srt} (hA : Lookup Γ n A)
    (hB : Lookup Γ n B) : A = B := by
  induction hA generalizing B with
  | zero => cases hB; rfl
  | succ C _ ih =>
      cases hB with
      | succ _ hB => exact congrArg (Expr.rename Nat.succ) (ih hB)

/-- **Uniqueness of types** in every corner of the cube. -/
theorem type_unique {Γ : List (Expr Srt)} {M A B : Expr Srt}
    (hA : HasType (cubeSpec f) Γ M A) (hB : HasType (cubeSpec f) Γ M B) : Converts A B := by
  induction M generalizing Γ A B with
  | var n =>
      obtain ⟨D, hD, hcD⟩ := hA.generation
      obtain ⟨E, hE, hcE⟩ := hB.generation
      rw [lookup_unique hD hE] at hcD
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | sort s =>
      obtain ⟨t, ht, hc⟩ := hA.generation
      obtain ⟨t', ht', hc'⟩ := hB.generation
      rw [cube_axioms_functional f ht ht'] at hc
      exact .trans _ _ _ hc (.symm _ _ hc')
  | app F a ihF iha =>
      obtain ⟨D, E, hf, ha, hc⟩ := hA.generation_app
      obtain ⟨D', E', hf', ha', hc'⟩ := hB.generation_app
      have he := (ihF hf hf').product_compatibility.2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))
  | lam D b ihD ihb =>
      obtain ⟨B₁, s, hb, -, hc⟩ := hA.generation_lam
      obtain ⟨B₂, s', hb', -, hc'⟩ := hB.generation_lam
      exact .trans _ _ _ hc (.trans _ _ _ (Converts.pi (.refl _) (ihb hb hb')) (.symm _ _ hc'))
  | pi D E ihD ihE =>
      obtain ⟨s₁, s₂, s₃, -, hE, hr, hc⟩ := hA.generation_pi
      obtain ⟨s₁', s₂', s₃', -, hE', hr', hc'⟩ := hB.generation_pi
      have h₂ : s₂ = s₂' := Converts.sort_inj (ihE hE hE')
      have h₃ : s₃ = s₃' := by rw [hr.1, hr'.1, h₂]
      rw [h₃] at hc
      exact .trans _ _ _ hc (.symm _ _ hc')

/-- Convertible sorted expressions have the same sort. -/
theorem sort_unique_conv {Γ : List (Expr Srt)} {A B : Expr Srt} {s t : Srt}
    (hA : HasType (cubeSpec f) Γ A (.sort s)) (hB : HasType (cubeSpec f) Γ B (.sort t))
    (hc : Converts A B) : s = t := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  exact Converts.sort_inj (type_unique (hA.subject_reduces hAC) (hB.subject_reduces hBC))

/-- No typed expression is convertible to `□`. -/
theorem not_conv_box {Γ : List (Expr Srt)} {A X : Expr Srt}
    (hA : HasType (cubeSpec f) Γ A X) (hc : Converts A (.sort .box)) : False := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  have hC : (Expr.sort Srt.box : Expr Srt) = C := (Normal.sort _).reduces_eq hBC
  subst hC
  exact not_hasType_box f (hA.subject_reduces hAC)

theorem ne_box_of_hasType {Γ : List (Expr Srt)} {A X : Expr Srt}
    (hA : HasType (cubeSpec f) Γ A X) : A ≠ .sort .box := by
  rintro rfl
  exact not_hasType_box f hA

/-- The type of a typed expression is `□` or is sorted. -/
theorem type_sorted {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    T = .sort .box ∨ ∃ s, HasType (cubeSpec f) Γ T (.sort s) := by
  obtain ⟨s, rfl⟩ | hs := h.regularity
  · cases s with
    | box => exact .inl rfl
    | star => exact .inr ⟨.box, cube_star_box f h.valid⟩
  · exact .inr hs

/-! ### Classes of variables of a context -/

/-- The classes of the variables of a context. -/
def ctxCl : List (Expr Srt) → Nat → Cls
  | [] => fun _ => .obj
  | A :: Γ => ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)

theorem bindC_ne_kind (c : Cls) (a : Sk) : bindC c ≠ .kind a := by
  cases c <;> simp [bindC]

theorem ctxCl_ne_kind : ∀ (Γ : List (Expr Srt)) (n : Nat) (a : Sk), ctxCl Γ n ≠ .kind a
  | [], _, _ => by simp [ctxCl]
  | A :: Γ, 0, a => bindC_ne_kind _ a
  | _ :: Γ, n + 1, a => ctxCl_ne_kind Γ n a

@[simp] theorem ctxCl_cons_comp_succ (A : Expr Srt) (Γ : List (Expr Srt)) :
    ctxCl (A :: Γ) ∘ Nat.succ = ctxCl Γ := rfl

/-! ### Kinds -/

theorem piCls_of_not_kind {cA c : Cls} (h : ∀ k, c ≠ .kind k) : piCls cA c = .constr .star := by
  cases c with
  | kind k => exact absurd rfl (h k)
  | constr => rfl
  | obj => rfl

/-- Every expression of type `□` is classified as a kind. -/
theorem kind_cl {Γ : List (Expr Srt)} {M : Expr Srt} (h : HasType (cubeSpec f) Γ M (.sort .box)) :
    ∃ k, cl (ctxCl Γ) M = .kind k := by
  induction M generalizing Γ with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      obtain ⟨s, hs⟩ := lookup_sorted h.valid hD
      exact (not_conv_box hs (.symm _ _ hc)).elim
  | sort s =>
      cases s with
      | star => exact ⟨.star, rfl⟩
      | box =>
          obtain ⟨t, ⟨h₁, _⟩, _⟩ := h.generation
          cases h₁
  | app F a _ _ =>
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box f hs).elim
  | lam A b _ _ =>
      obtain ⟨s, hs⟩ := h.abstraction_type_sorted
      exact (not_hasType_box f hs).elim
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      have h₃ : s₃ = .box := (Converts.sort_inj hc).symm
      rw [hr.1] at h₃
      subst h₃
      obtain ⟨k, hk⟩ := ihB hB
      refine ⟨domSk (cl (ctxCl Γ) A) k, ?_⟩
      have hk' : cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) B = .kind k := hk
      simp only [cl, hk', piCls]

/-- Expressions whose type is sorted are never classified as kinds. -/
theorem not_kind {Γ : List (Expr Srt)} {M T : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ M T) (hT : HasType (cubeSpec f) Γ T (.sort s)) :
    ∀ k, cl (ctxCl Γ) M ≠ .kind k := by
  induction M generalizing Γ T s with
  | var n => exact ctxCl_ne_kind Γ n
  | sort s' =>
      cases s' with
      | star =>
          obtain ⟨t, ⟨_, rfl⟩, hc⟩ := h.generation
          exact (not_conv_box hT hc).elim
      | box => intro k; simp [cl]
  | app F a _ _ => exact appCls_ne_kind _
  | lam A b _ _ => exact lamCls_ne_kind _ _
  | pi A B _ ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := h.generation_pi
      cases s₃ with
      | box => exact (not_conv_box hT hc).elim
      | star =>
          have h₂ : s₂ = .star := hr.1.symm
          subst h₂
          have hnk := ihB hB (cube_star_box f hB.valid)
          simp only [ctxCl] at hnk
          intro k
          simp only [cl]
          rw [piCls_of_not_kind hnk]
          simp

theorem bindC_eq_of_not_kind {c c' : Cls} (h : ∀ k, c ≠ .kind k) (h' : ∀ k, c' ≠ .kind k) :
    bindC c = bindC c' := by
  rw [bindC_of_not_kind h, bindC_of_not_kind h']

theorem piCls_eq_of_not_kind {c c' : Cls} (h : ∀ k, c ≠ .kind k) (h' : ∀ k, c' ≠ .kind k)
    (d : Cls) : piCls c d = piCls c' d := by
  cases d <;> simp [piCls, domSk_of_not_kind h, domSk_of_not_kind h']

/-- The skeleton of a kind is invariant under reduction. -/
theorem kind_beta {Γ : List (Expr Srt)} {K K' : Expr Srt}
    (h : HasType (cubeSpec f) Γ K (.sort .box)) (hr : Beta K K') :
    cl (ctxCl Γ) K = cl (ctxCl Γ) K' := by
  induction hr generalizing Γ with
  | head A b a =>
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box f hs).elim
  | app_left _ _ =>
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box f hs).elim
  | app_right _ _ =>
      obtain ⟨s, hs⟩ := h.application_type_sorted
      exact (not_hasType_box f hs).elim
  | lam_domain _ _ =>
      obtain ⟨s, hs⟩ := h.abstraction_type_sorted
      exact (not_hasType_box f hs).elim
  | lam_body _ _ =>
      obtain ⟨s, hs⟩ := h.abstraction_type_sorted
      exact (not_hasType_box f hs).elim
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, hc⟩ := h.generation_pi
      cases s₁ with
      | box =>
          simp only [cl, ih hA]
      | star =>
          have hA' := hA.subject_reduction hr
          have hn := not_kind hA (cube_star_box f hA.valid)
          have hn' := not_kind hA' (cube_star_box f hA.valid)
          simp only [cl, bindC_eq_of_not_kind hn hn', piCls_eq_of_not_kind hn hn']
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrl, hc⟩ := h.generation_pi
      have h₃ : s₃ = .box := (Converts.sort_inj hc).symm
      rw [hrl.1] at h₃
      subst h₃
      have := ih hB
      simp only [ctxCl] at this
      simp only [cl, this]

theorem kind_reduces {Γ : List (Expr Srt)} {K K' : Expr Srt}
    (h : HasType (cubeSpec f) Γ K (.sort .box)) (hr : Reduces K K') :
    cl (ctxCl Γ) K = cl (ctxCl Γ) K' := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih => exact ih.trans (kind_beta (h.subject_reduces hr₁) hr₂)

theorem kind_conv {Γ : List (Expr Srt)} {K K' : Expr Srt}
    (h : HasType (cubeSpec f) Γ K (.sort .box)) (h' : HasType (cubeSpec f) Γ K' (.sort .box))
    (hc : Converts K K') : cl (ctxCl Γ) K = cl (ctxCl Γ) K' := by
  obtain ⟨C, hKC, hK'C⟩ := hc.join
  exact (kind_reduces h hKC).trans (kind_reduces h' hK'C).symm

/-! ### The classification -/

theorem lamCls_bindC (cA c : Cls) : lamCls cA (bindC c) = bindC (piCls cA c) := by
  cases c <;> rfl

theorem appCls_bindC_piCls (cA c : Cls) : appCls (bindC (piCls cA c)) = bindC c := by
  cases c with
  | kind k => cases cA <;> rfl
  | constr => rfl
  | obj => rfl

/-- **The classification**: in a legal judgement `Γ ⊢ M : T` with `T ≠ □`, `M` is a constructor
of skeleton `k` if `T` is a kind of skeleton `k`, and an object if `T` is a type. -/
theorem classify {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T)
    (hT : T ≠ .sort .box) : cl (ctxCl Γ) M = bindC (cl (ctxCl Γ) T) := by
  induction h with
  | ax h => exact absurd (congrArg Expr.sort h.2) hT
  | @var Γ A s hA _ =>
      show bindC (cl (ctxCl Γ) A) = _
      rw [cl_rename]
      rfl
  | @weaken Γ M B A s hM hA ihM _ =>
      rw [cl_rename, cl_rename]
      have hB : B ≠ .sort .box := by
        rintro rfl
        exact hT rfl
      exact ihM hB
  | @product Γ A B s₁ s₂ s₃ hA hB hr _ _ =>
      cases s₃ with
      | box => exact absurd rfl hT
      | star =>
          have h₂ : s₂ = .star := hr.1.symm
          subst h₂
          have hnk := not_kind hB (cube_star_box f hB.valid)
          simp only [ctxCl] at hnk
          simp only [cl]
          rw [piCls_of_not_kind hnk]
          rfl
  | @abstraction Γ A b B s hb hPi ihb _ =>
      obtain ⟨s₁, s₂, s₃, -, hB, -, -⟩ := hPi.generation_pi
      have := ihb (ne_box_of_hasType hB)
      simp only [ctxCl] at this
      simp only [cl, this, lamCls_bindC]
  | @application Γ F a A B hF ha ihF iha =>
      obtain ⟨s, hPi⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := hPi.generation_pi
      have hF' := ihF (by intro h; cases h)
      have ha' := iha (ne_box_of_hasType hA)
      simp only [cl] at hF' ⊢
      rw [hF', cl_instantiate, ha', appCls_bindC_piCls]
  | @conversion Γ M A B s hM hB hc ihM _ =>
      have hA : A ≠ .sort .box := by
        rintro rfl
        exact not_conv_box hB (.symm _ _ hc)
      rw [ihM hA]
      rcases type_sorted hM with h | ⟨s', hA'⟩
      · exact absurd h hA
      have hss := sort_unique_conv hA' hB hc
      subst hss
      cases s' with
      | box => rw [kind_conv hA' hB hc]
      | star =>
          exact bindC_eq_of_not_kind (not_kind hA' (cube_star_box f hA'.valid))
            (not_kind hB (cube_star_box f hB.valid))

/-- Kinds and types are products' admissible domains. -/
theorem piOK_of_sorted {Γ : List (Expr Srt)} {A : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ A (.sort s)) : PiOK (cl (ctxCl Γ) A) := by
  cases s with
  | box => exact .inr (kind_cl h)
  | star =>
      left
      rw [classify h (by intro h; cases h)]
      rfl

theorem relC_of_sorted {Γ : List (Expr Srt)} {A : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ A (.sort s)) : RelC (cl (ctxCl Γ) A) .star :=
  .of_piOK (piOK_of_sorted h)

theorem appOK_bindC (cA cB : Cls) : AppOK (bindC (piCls cA cB)) (bindC cA) := by
  cases cB with
  | kind k => cases cA <;> rfl
  | constr => trivial
  | obj => trivial

/-- Every legal expression is well classified. -/
theorem wc_of_hasType {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    WC (ctxCl Γ) M := by
  induction M generalizing Γ T with
  | var n => trivial
  | sort s => trivial
  | app F U ihF ihU =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      obtain ⟨s, hPi⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := hPi.generation_pi
      refine ⟨ihF hF, ihU hU, ?_⟩
      rw [classify hF (by intro h; cases h), classify hU (ne_box_of_hasType hA)]
      exact appOK_bindC _ _
  | lam A b ihA ihb =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, hA⟩ := hPi.product_domain A B rfl
      exact ⟨ihA hA, ihb hb⟩
  | pi A B ihA ihB =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      exact ⟨ihA hA, ihB hB, piOK_of_sorted hA, piOK_of_sorted hB⟩

/-- **The classification is stable under reduction.** -/
theorem cl_beta {Γ : List (Expr Srt)} {U U' T : Expr Srt} (h : HasType (cubeSpec f) Γ U T)
    (hr : Beta U U') : cl (ctxCl Γ) U = cl (ctxCl Γ) U' := by
  rcases type_sorted h with rfl | ⟨s, hT⟩
  · exact kind_beta h hr
  · have hT' := ne_box_of_hasType hT
    rw [classify h hT', classify (h.subject_reduction hr) hT']

/-! ### Invariance of the interpretation -/

/-- **The interpretation of legal kinds and constructors is invariant under reduction.** -/
theorem interp_beta {Γ : List (Expr Srt)} {M M' X : Expr Srt} (h : HasType (cubeSpec f) Γ M X)
    (hr : Beta M M') {k : Sk} (hk : RelC (cl (ctxCl Γ) M) k) (ξ : Val) :
    interp (ctxCl Γ) M k ξ = interp (ctxCl Γ) M' k ξ := by
  induction hr generalizing Γ X k ξ with
  | head A b U =>
      have hwc := wc_of_hasType h
      obtain ⟨⟨_, hb⟩, _, hok⟩ := hwc
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .constr a := hok
        obtain ⟨k₀, hb₀, hk₀⟩ := lamCls_eq_constr ha
        obtain ⟨hcA, rfl⟩ := domSk_eq_arr hk₀.symm
        rw [interp_instantiate, hcU]
        simp only [interp, hcU]
        rw [hcA] at hb hb₀ ⊢
        apply interp_agree b hb _ (.inl hb₀)
        intro n k' hk'
        cases n with
        | zero =>
            have := RelC.constr_eq hk'
            subst this
            simp
        | succ n => rfl
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .obj := hok
        obtain ⟨k₀, hb₀, hk₀⟩ := lamCls_eq_constr ha
        obtain ⟨hcA, rfl⟩ := domSk_eq_arrO hk₀.symm
        rw [interp_instantiate, hcU]
        simp only [interp, hcU]
        rw [bindC_of_not_kind hcA] at hb hb₀ ⊢
        apply interp_agree b hb _ (.inl hb₀)
        intro n k' hk'
        cases n with
        | zero => exact hk'.not_obj.elim
        | succ n => rfl
  | @app_left F F' U hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      obtain ⟨_, _, hok⟩ := wc_of_hasType h
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .constr a := hok
        simp only [interp, hcU]
        rw [ih hF (.inl ha)]
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .obj := hok
        simp only [interp, hcU]
        rw [ih hF (.inl ha)]
  | @app_right F U U' hr ih =>
      obtain ⟨A, B, hF, hU, -⟩ := h.generation_app
      obtain ⟨_, _, hok⟩ := wc_of_hasType h
      have hcl := cl_beta hU hr
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .constr a := hok
        have hcU' : cl (ctxCl Γ) U' = .constr a := hcl ▸ hcU
        simp only [interp, hcU, hcU']
        rw [ih hU (.inl hcU)]
      · rw [ha] at hok
        have hcU : cl (ctxCl Γ) U = .obj := hok
        have hcU' : cl (ctxCl Γ) U' = .obj := hcl ▸ hcU
        simp only [interp, hcU, hcU']
        rfl
  | @lam_domain A A' b hr _ =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨s₁, hA⟩ := hPi.product_domain A B rfl
      have hcl := cl_beta hA hr
      cases k <;> simp only [interp, hcl] <;> rfl
  | @lam_body A b b' hr ih =>
      obtain ⟨B, s, hb, hPi, -⟩ := h.generation_lam
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      have ih' := fun ξ => ih hb (.inl hb₀) ξ
      simp only [ctxCl] at ih'
      rcases hcA : cl (ctxCl Γ) A with a | a | _
      · simp only [domSk, interp]
        funext v
        exact ih' _
      · simp only [domSk, interp]
        exact ih' _
      · simp only [domSk, interp]
        exact ih' _
  | @pi_domain A A' B hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      have := hk.pi
      subst this
      have hcl := cl_beta hA hr
      have hA' := ih hA (relC_of_sorted hA) ξ
      simp only [interp]
      rw [← hcl, hA']
  | @pi_body A B B' hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := h.generation_pi
      have := hk.pi
      subst this
      have ih' := fun ξ => ih hB (relC_of_sorted hB) ξ
      simp only [ctxCl] at ih'
      simp only [interp]
      rcases hcA : cl (ctxCl Γ) A with a | a | _ <;>
        (rw [hcA] at ih'; simp only [bindC] at ih'; simp only [ih']) <;> rfl

theorem interp_reduces {Γ : List (Expr Srt)} {A C : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ A (.sort s)) (hr : Reduces A C) (ξ : Val) :
    interp (ctxCl Γ) A .star ξ = interp (ctxCl Γ) C .star ξ := by
  induction hr with
  | refl => rfl
  | tail hr₁ hr₂ ih =>
      have hB := h.subject_reduces hr₁
      exact ih.trans (interp_beta hB hr₂ (relC_of_sorted hB) ξ)

/-- **The interpretation of kinds and types is invariant under conversion.** -/
theorem interp_conv {Γ : List (Expr Srt)} {A B : Expr Srt} {s t : Srt}
    (hA : HasType (cubeSpec f) Γ A (.sort s)) (hB : HasType (cubeSpec f) Γ B (.sort t))
    (hc : Converts A B) (ξ : Val) :
    interp (ctxCl Γ) A .star ξ = interp (ctxCl Γ) B .star ξ := by
  obtain ⟨C, hAC, hBC⟩ := hc.join
  exact (interp_reduces hA hAC ξ).trans (interp_reduces hB hBC ξ).symm

/-! ### The fundamental lemma -/

/-- Semantic validity of a substitution and a valuation for a context. -/
def SemCtx : List (Expr Srt) → (Nat → Expr Srt) → Val → Prop
  | [], _, _ => True
  | A :: Γ, σ, ξ => σ 0 ∈ interp (ctxCl Γ) A .star (ξ ∘ Nat.succ) ∧
      (∀ k, RelC (bindC (cl (ctxCl Γ) A)) k → Cand k (ξ 0 k)) ∧
      SemCtx Γ (σ ∘ Nat.succ) (ξ ∘ Nat.succ)

theorem SemCtx.good : ∀ {Γ : List (Expr Srt)} {σ : Nat → Expr Srt} {ξ : Val},
    SemCtx Γ σ ξ → Good (ctxCl Γ) ξ
  | [], _, _, _ => fun _ k hk => by
      rcases hk with h | ⟨_, _, h⟩ <;> cases h
  | _ :: _, _, _, ⟨_, h0, hΓ⟩ => fun n k hk => by
      cases n with
      | zero => exact h0 k hk
      | succ n => exact hΓ.good n k hk

theorem interp_sort (Δ : Nat → Cls) (s : Srt) (ξ : Val) : interp Δ (.sort s) .star ξ = snSet := by
  cases s <;> rfl

theorem subst_ncons (B N : Expr Srt) (σ : Nat → Expr Srt) :
    B.subst (ncons N σ) = (B.subst (Expr.liftSub σ)).instantiate N := by
  rw [Expr.instantiate, Expr.subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [ncons_succ, Expr.liftSub_succ, Expr.subst_rename]
      exact (Expr.subst_var (σ n)).symm

theorem sat_of_sorted {Γ : List (Expr Srt)} {A : Expr Srt} {s : Srt} {ξ : Val}
    (h : HasType (cubeSpec f) Γ A (.sort s)) (hξ : Good (ctxCl Γ) ξ) :
    Sat (interp (ctxCl Γ) A .star ξ) :=
  interp_cand A (wc_of_hasType h) hξ (relC_of_sorted h)

/-- **The fundamental lemma.** -/
theorem fundamental {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    ∀ σ ξ, SemCtx Γ σ ξ → M.subst σ ∈ interp (ctxCl Γ) T .star ξ := by
  induction h with
  | ax hax =>
      intro σ ξ _
      obtain ⟨rfl, rfl⟩ := hax
      exact (Normal.sort _).stronglyNormalizing
  | @var Γ A s hA _ =>
      intro σ ξ hσ
      show σ 0 ∈ _
      rw [interp_rename]
      exact hσ.1
  | @weaken Γ M B A s hM hA ihM _ =>
      intro σ ξ hσ
      rw [Expr.subst_rename, interp_rename]
      exact ihM _ _ hσ.2.2
  | @product Γ A B s₁ s₂ s₃ hA hB _ ihA ihB =>
      intro σ ξ hσ
      rw [interp_sort]
      have hA' : StronglyNormalizing (A.subst σ) := by
        have := ihA σ ξ hσ
        rwa [interp_sort] at this
      have hσ' : SemCtx (A :: Γ) (ncons (.var 0) σ) (ncons canon ξ) :=
        ⟨(sat_of_sorted hA hσ.good).var_mem 0, fun k _ => cand_canon k, hσ⟩
      have hB' := ihB _ _ hσ'
      rw [interp_sort, subst_ncons] at hB'
      exact StronglyNormalizing.pi hA' (StronglyNormalizing.of_subst _ hB')
  | @abstraction Γ A b B s hb hPi ihb ihPi =>
      intro σ ξ hσ
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := hPi.generation_pi
      have hAσ : StronglyNormalizing (A.subst σ) := by
        have := ihPi σ ξ hσ
        rw [interp_sort] at this
        exact StronglyNormalizing.pi_domain this
      have hXA := sat_of_sorted hA hσ.good
      have hwcB := wc_of_hasType hB
      have hrB := relC_of_sorted hB
      simp only [ctxCl] at hwcB hrB
      show Expr.lam (A.subst σ) (b.subst (Expr.liftSub σ)) ∈ _
      simp only [interp]
      rcases hcA : cl (ctxCl Γ) A with a | a | _
      · rw [hcA] at hwcB hrB
        intro N hN v hv
        have hY : Sat (interp (ncons (.constr a) (ctxCl Γ)) B .star (ncons (ext a v) ξ)) :=
          interp_cand B hwcB (hσ.good.ncons_ext hv) hrB
        apply hY.head_mem hAσ (hXA.sn N hN)
        rw [← subst_ncons]
        have hσ' : SemCtx (A :: Γ) (ncons N σ) (ncons (ext a v) ξ) := by
          refine ⟨hN, ?_, hσ⟩
          intro k hk
          rw [hcA] at hk
          have := RelC.constr_eq hk
          subst this
          simpa using hv
        have := ihb _ _ hσ'
        simp only [ctxCl, hcA] at this
        exact this
      all_goals
        rw [hcA] at hwcB hrB
        intro N hN _ _
        have hY : Sat (interp (ncons .obj (ctxCl Γ)) B .star (ncons canon ξ)) :=
          interp_cand B hwcB (hσ.good.ncons_obj _) hrB
        apply hY.head_mem hAσ (hXA.sn N hN)
        rw [← subst_ncons]
        have hσ' : SemCtx (A :: Γ) (ncons N σ) (ncons canon ξ) :=
          ⟨hN, fun k _ => cand_canon k, hσ⟩
        have := ihb _ _ hσ'
        simp only [ctxCl, hcA, bindC] at this
        exact this
  | @application Γ F a A B hF ha ihF iha =>
      intro σ ξ hσ
      obtain ⟨s, hPi⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, -, -⟩ := hPi.generation_pi
      have hcl := classify ha (ne_box_of_hasType hA)
      have hwcB := wc_of_hasType hB
      have hrB := relC_of_sorted hB
      simp only [ctxCl] at hwcB hrB
      have hFσ := ihF σ ξ hσ
      have haσ := iha σ ξ hσ
      show Expr.app (F.subst σ) (a.subst σ) ∈ _
      rw [interp_instantiate, hcl]
      simp only [interp] at hFσ
      rcases hcA : cl (ctxCl Γ) A with a₀ | a₀ | _
      · rw [hcA] at hFσ hwcB hrB
        simp only [bindC] at hwcB hrB ⊢
        dsimp only at hFσ
        have hv : Cand a₀ (interp (ctxCl Γ) a a₀ ξ) :=
          interp_cand a (wc_of_hasType ha) hσ.good (.inl (by rw [hcl, hcA]; rfl))
        have hmem : Expr.app (F.subst σ) (a.subst σ) ∈ interp (ncons (.constr a₀) (ctxCl Γ)) B
            .star (ncons (ext a₀ (interp (ctxCl Γ) a a₀ ξ)) ξ) := hFσ _ haσ _ hv
        have heq : interp (ncons (.constr a₀) (ctxCl Γ)) B .star
            (ncons (ext a₀ (interp (ctxCl Γ) a a₀ ξ)) ξ) =
            interp (ncons (.constr a₀) (ctxCl Γ)) B .star
            (ncons (fun k => interp (ctxCl Γ) a k ξ) ξ) := by
          apply interp_agree B hwcB _ hrB
          intro n k hk
          cases n with
          | zero =>
              have := RelC.constr_eq hk
              subst this
              simp
          | succ n => rfl
        rw [heq] at hmem
        exact hmem
      all_goals
        rw [hcA] at hFσ hwcB hrB
        simp only [bindC] at hwcB hrB ⊢
        dsimp only at hFσ
        have hmem : Expr.app (F.subst σ) (a.subst σ) ∈ interp (ncons .obj (ctxCl Γ)) B
            .star (ncons canon ξ) := hFσ _ haσ () trivial
        have heq : interp (ncons .obj (ctxCl Γ)) B .star (ncons canon ξ) =
            interp (ncons .obj (ctxCl Γ)) B .star
            (ncons (fun k => interp (ctxCl Γ) a k ξ) ξ) := by
          apply interp_agree B hwcB _ hrB
          intro n k hk
          cases n with
          | zero => exact hk.not_obj.elim
          | succ n => rfl
        rw [heq] at hmem
        exact hmem
  | @conversion Γ M A B s hM hB hc ihM _ =>
      intro σ ξ hσ
      have := ihM σ ξ hσ
      rcases type_sorted hM with rfl | ⟨s', hA⟩
      · exact (not_conv_box hB (.symm _ _ hc)).elim
      rwa [interp_conv hA hB hc] at this

/-- Variables form a semantically valid substitution for every valid context. -/
theorem semCtx_vars {Γ : List (Expr Srt)} (hΓ : ValidContext (cubeSpec f) Γ) :
    ∀ j, SemCtx Γ (fun n => .var (n + j)) canonVal := by
  induction hΓ with
  | nil => intro j; trivial
  | @cons Γ A s hΓ hA ih =>
      intro j
      refine ⟨(sat_of_sorted hA (good_canonVal _)).var_mem _, fun k _ => cand_canon k, ?_⟩
      have := ih (j + 1)
      have heq : ((fun n => Expr.var (n + j)) ∘ Nat.succ : Nat → Expr Srt) =
          fun n => .var (n + (j + 1)) := by
        funext n
        simp only [Function.comp_apply, Nat.succ_eq_add_one]
        congr 1
        omega
      rw [heq]
      exact this

/-- Every typed expression is strongly normalizing. -/
theorem sn_of_hasType {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    StronglyNormalizing M := by
  have hM := fundamental h _ _ (semCtx_vars h.valid 0)
  have hid : (fun n => (Expr.var (n + 0) : Expr Srt)) = Expr.var := by
    funext n
    rfl
  rw [hid, Expr.subst_var] at hM
  rcases type_sorted h with rfl | ⟨s, hT⟩
  · exact hM
  · exact (sat_of_sorted hT (good_canonVal _)).sn _ hM

/-- Strong normalization in every corner of the cube (the general form of the fundamental
lemma's consequence). -/
theorem systemStronglyNormalizing (f : CubeFeatures) :
    SystemStronglyNormalizing (cubeSpec f) := by
  intro Γ _ M hM
  obtain ⟨A, h | h⟩ := hM
  · exact sn_of_hasType h
  · rcases h.regularity with ⟨s, rfl⟩ | ⟨s, hM⟩
    · exact (Normal.sort s).stronglyNormalizing
    · exact sn_of_hasType hM

end CoC

/-- **Strong normalization of the calculus of constructions.** -/
theorem coc_stronglyNormalizing : SystemStronglyNormalizing (cubeSpec coc) :=
  CoC.systemStronglyNormalizing coc

/-- **Every corner of the cube is strongly normalizing**, by `cube_sn_mono`. -/
theorem cube_stronglyNormalizing (f : CubeFeatures) : SystemStronglyNormalizing (cubeSpec f) :=
  cube_sn_mono (le_coc f) coc_stronglyNormalizing

/-- **System `F^ω` is strongly normalizing** (task `M23-FOMEGA`), as a corner below `coc`. -/
theorem systemFOmega_stronglyNormalizing : SystemStronglyNormalizing (cubeSpec systemFOmega) :=
  cube_stronglyNormalizing systemFOmega

/-- Strong normalization gives a normal form. -/
theorem StronglyNormalizing.weaklyNormalizing {S : Type*} {M : Expr S}
    (h : StronglyNormalizing M) : WeaklyNormalizing M := by
  induction h with
  | intro M _ ih =>
      by_cases hn : Normal M
      · exact ⟨M, .refl, hn⟩
      · simp only [Normal, not_forall, not_not] at hn
        obtain ⟨N, hN⟩ := hn
        obtain ⟨K, hK, hKn⟩ := ih N hN
        exact ⟨K, Relation.ReflTransGen.head hN hK, hKn⟩

/-- **Consistency of the calculus of constructions**: no closed expression has type
`Π α:∗. α`. -/
theorem coc_consistent :
    ¬ ∃ M, HasType (cubeSpec coc) ([]) M (.pi (.sort .star) (.var 0)) := by
  rintro ⟨M, hM⟩
  obtain ⟨N, hr, hn⟩ :=
    (coc_stronglyNormalizing List.nil .nil M ⟨_, .inl hM⟩).weaklyNormalizing
  exact no_normal_closed_bot (hM.subject_reduces hr) hn

end PureTypeSystem
