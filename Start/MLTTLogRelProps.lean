/-
**Martin-Löf type theory: the logical relation is a PER, and stable under type equality** —
milestone M30 (`M30-MLTT-LR`).

For a reducible type `A` with interpretation `I` (`TyR E l Γ A I`), one induction on the
derivation (and on the level, for the universes) proves at once (`TyR.good`):

* `symm`, `trans` — reducible term equality at `A` is a partial equivalence relation;
* `conv` — **conversion**: if `B` is reducible with interpretation `J` and reducibly equal to
  `A`, then `I` and `J` relate the same terms;
* `tySymm`, `tyTrans` — reducible type equality is symmetric and transitive.

They depend on each other (symmetry at a product converts along the codomain, conversion at a
product needs the reflexivity of related arguments), which is why they are proved together.
Consequences: `TyR.irrel` (**irrelevance**: two reducibility proofs of the same type have the
same interpretation), `TyR.tmRefl` (related terms are reducible).
-/

import Start.MLTTLogRel

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Natural numbers, the empty type, neutral types -/

/-- Two typed reductions of a term to weak head normal forms end at the same term. -/
theorem TRedsT_whnf {Γ : Ctx} {t u v A B : Tm} (hu : TRedsT Γ t u A) (hv : TRedsT Γ t v B)
    (hnu : Whnf u) (hnv : Whnf v) : u = v :=
  hu.red.whnf_unique hv.red hnu hnv

theorem NatR.symm {E : GenEq} {Γ : Ctx} {t u : Tm} (h : NatR E Γ t u) : NatR E Γ u t := by
  induction h with
  | zero ht hu => exact NatR.zero hu ht
  | succ ht hu hsm _ ih => exact NatR.succ hu ht (E.tm_symm hsm) ih
  | ne ht hu hn hm hnm => exact NatR.ne hu ht hm hn (E.ne_symm hnm)

theorem NatR.trans {E : GenEq} {Γ : Ctx} {t u v : Tm} (h₁ : NatR E Γ t u) (h₂ : NatR E Γ u v) :
    NatR E Γ t v := by
  induction h₁ generalizing v with
  | zero ht hu =>
      cases h₂ with
      | zero hu' hv => exact NatR.zero ht hv
      | succ hu' hv _ _ =>
          exact absurd (TRedsT_whnf hu hu' Whnf.zero (Whnf.succ _)) (by simp)
      | ne hu' hv hn _ _ =>
          have e := TRedsT_whnf hu hu' Whnf.zero (Whnf.ne hn)
          subst e; cases hn
  | succ ht hu hsm _ ih =>
      cases h₂ with
      | zero hu' hv =>
          exact absurd (TRedsT_whnf hu hu' (Whnf.succ _) Whnf.zero) (by simp)
      | succ hu' hv hsm' hr' =>
          have e := TRedsT_whnf hu hu' (Whnf.succ _) (Whnf.succ _)
          simp only [succ.injEq] at e
          subst e
          exact NatR.succ ht hv (E.tm_trans hsm hsm') (ih hr')
      | ne hu' hv hn _ _ =>
          have e := TRedsT_whnf hu hu' (Whnf.succ _) (Whnf.ne hn)
          subst e; cases hn
  | ne ht hu hn hm hnm =>
      cases h₂ with
      | zero hu' hv =>
          have e := TRedsT_whnf hu hu' (Whnf.ne hm) Whnf.zero
          subst e; cases hm
      | succ hu' hv _ _ =>
          have e := TRedsT_whnf hu hu' (Whnf.ne hm) (Whnf.succ _)
          subst e; cases hm
      | ne hu' hv hm' hk hmk =>
          have e := TRedsT_whnf hu hu' (Whnf.ne hm) (Whnf.ne hm')
          subst e
          exact NatR.ne ht hv hn hk (E.ne_trans hnm hmk)

theorem EmptyR.symm {E : GenEq} {Γ : Ctx} {t u : Tm} (h : EmptyR E Γ t u) : EmptyR E Γ u t := by
  obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := h
  exact ⟨m, n, hu, ht, hm, hn, E.ne_symm hnm⟩

theorem EmptyR.trans {E : GenEq} {Γ : Ctx} {t u v : Tm} (h₁ : EmptyR E Γ t u)
    (h₂ : EmptyR E Γ u v) : EmptyR E Γ t v := by
  obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := h₁
  obtain ⟨m', k, hu', hv, hm', hk, hmk⟩ := h₂
  have e := TRedsT_whnf hu hu' (Whnf.ne hm) (Whnf.ne hm')
  subst e
  exact ⟨n, k, ht, hv, hn, hk, E.ne_trans hnm hmk⟩

theorem NeR.symm {E : GenEq} {Γ : Ctx} {N t u : Tm} (h : NeR E Γ N t u) : NeR E Γ N u t := by
  obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := h
  exact ⟨m, n, hu, ht, hm, hn, E.ne_symm hnm⟩

theorem NeR.trans {E : GenEq} {Γ : Ctx} {N t u v : Tm} (h₁ : NeR E Γ N t u)
    (h₂ : NeR E Γ N u v) : NeR E Γ N t v := by
  obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := h₁
  obtain ⟨m', k, hu', hv, hm', hk, hmk⟩ := h₂
  have e := TRedsT_whnf hu hu' (Whnf.ne hm) (Whnf.ne hm')
  subst e
  exact ⟨n, k, ht, hv, hn, hk, E.ne_trans hnm hmk⟩

theorem NeR.conv {E : GenEq} {Γ : Ctx} {N M t u : Tm} (h : NeR E Γ N t u) (hNM : TyEq Γ N M) :
    NeR E Γ M t u := by
  obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := h
  exact ⟨n, m, ht.conv hNM, hu.conv hNM, hn, hm, E.ne_conv hnm hNM⟩

/-! ### The properties -/

/-- The properties of a reducible type proved by one induction. -/
structure Good (E : GenEq) (Γ : Ctx) (A : Tm) (I : Interp) : Prop where
  symm : ∀ {t u : Tm}, I.tmEq t u → I.tmEq u t
  trans : ∀ {t u v : Tm}, I.tmEq t u → I.tmEq u v → I.tmEq t v
  conv : ∀ {l₂ : ℕ} {B : Tm} {J : Interp}, TyR E l₂ Γ B J → I.tyEq B →
    ∀ t u, (I.tmEq t u ↔ J.tmEq t u)
  tySymm : ∀ {l₂ : ℕ} {B : Tm} {J : Interp}, TyR E l₂ Γ B J → I.tyEq B → J.tyEq A
  tyTrans : ∀ {l₂ : ℕ} {B : Tm} {J : Interp} {C : Tm}, TyR E l₂ Γ B J → I.tyEq B → J.tyEq C →
    I.tyEq C

theorem Good.left {E : GenEq} {Γ : Ctx} {A : Tm} {I : Interp} (g : Good E Γ A I) {t u : Tm}
    (h : I.tmEq t u) : I.tmEq t t :=
  g.trans h (g.symm h)

theorem Good.right {E : GenEq} {Γ : Ctx} {A : Tm} {I : Interp} (g : Good E Γ A I) {t u : Tm}
    (h : I.tmEq t u) : I.tmEq u u :=
  g.trans (g.symm h) h

theorem TyRAt.toTyR {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp}
    (h : TyRAt E l (fun l' _ => TyR E l') Γ A I) : TyR E l Γ A I := by
  rw [TyR.unfold]; exact h

/-- **The logical relation is a PER, stable under reducible type equality.** -/
theorem TyR.good {E : GenEq} : ∀ (l : ℕ) {Γ : Ctx} {A : Tm} {I : Interp}, TyR E l Γ A I →
    Good E Γ A I := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ihl =>
  intro Γ A I h
  rw [TyR.unfold] at h
  induction h with
  | @univ Γ A l' hl D =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rintro t u ⟨t', u', ht, hu, hnt, hnu, htu, ⟨It, hIt, hItu⟩, ⟨Ju, hJu⟩⟩
        exact ⟨u', t', hu, ht, hnu, hnt, E.tm_symm htu,
          ⟨Ju, hJu, (ihl l' hl hIt).tySymm hJu hItu⟩, ⟨It, hIt⟩⟩
      · rintro t u v ⟨t', u', ht, hu, hnt, hnu, htu, ⟨It, hIt, hItu⟩, ⟨Ju, hJu⟩⟩
          ⟨u'', v', hu', hv, hnu', hnv, huv, ⟨Iu, hIu, hIuv⟩, ⟨Jv, hJv⟩⟩
        have e := TRedsT_whnf hu hu' hnu hnu'
        subst e
        exact ⟨t', v', ht, hv, hnt, hnv, E.tm_trans htu huv,
          ⟨It, hIt, (ihl l' hl hIt).tyTrans hIu hItu hIuv⟩, ⟨Jv, hJv⟩⟩
      · intro l₂ B J hJ hB t u
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            have e := TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.univ _)
            simp only [univ.injEq] at e
            subst e
            exact Iff.rfl
        | nat DB => exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) Whnf.nat) (by simp)
        | empty DB => exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.pi _ _)) (by simp)
      · intro l₂ B J hJ hB
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            have e := TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.univ _)
            simp only [univ.injEq] at e
            subst e
            exact D
        | nat DB => exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) Whnf.nat) (by simp)
        | empty DB => exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.pi _ _)) (by simp)
      · intro l₂ B J C hJ hB hC
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            have e := TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.univ _)
            simp only [univ.injEq] at e
            subst e
            exact hC
        | nat DB => exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) Whnf.nat) (by simp)
        | empty DB => exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB (Whnf.univ _) (Whnf.pi _ _)) (by simp)
  | @nat Γ A D =>
      refine ⟨fun h => NatR.symm h, fun h h' => NatR.trans h h', ?_, ?_, ?_⟩
      · intro l₂ B J hJ hB t u
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.univ _)) (by simp)
        | nat DB => exact Iff.rfl
        | empty DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.pi _ _)) (by simp)
      · intro l₂ B J hJ hB
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.univ _)) (by simp)
        | nat DB => exact D
        | empty DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.pi _ _)) (by simp)
      · intro l₂ B J C hJ hB hC
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.univ _)) (by simp)
        | nat DB => exact hC
        | empty DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.nat (Whnf.pi _ _)) (by simp)
  | @empty Γ A D =>
      refine ⟨fun h => EmptyR.symm h, fun h h' => EmptyR.trans h h', ?_, ?_, ?_⟩
      · intro l₂ B J hJ hB t u
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.univ _)) (by simp)
        | nat DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty Whnf.nat) (by simp)
        | empty DB => exact Iff.rfl
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.pi _ _)) (by simp)
      · intro l₂ B J hJ hB
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.univ _)) (by simp)
        | nat DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty Whnf.nat) (by simp)
        | empty DB => exact D
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.pi _ _)) (by simp)
      · intro l₂ B J C hJ hB hC
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.univ _)) (by simp)
        | nat DB => exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty Whnf.nat) (by simp)
        | empty DB => exact hC
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.ne hN)
            subst e; cases hN
        | pi _ _ DB _ _ _ _ _ _ =>
            exact absurd (TyRedsT.whnf_unique hB DB Whnf.empty (Whnf.pi _ _)) (by simp)
  | @ne Γ A N k D hN hNN =>
      refine ⟨fun h => NeR.symm h, fun h h' => NeR.trans h h', ?_, ?_, ?_⟩
      · rintro l₂ B J hJ ⟨M, hBM, hM, hNM⟩ t u
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.univ _)
            subst e; cases hM
        | nat DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) Whnf.nat
            subst e; cases hM
        | empty DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) Whnf.empty
            subst e; cases hM
        | ne DB hM' _ =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.ne hM')
            subst e
            have hTE := E.ty_eq hNM
            exact ⟨fun h => h.conv hTE, fun h => h.conv (Der.symmT hTE)⟩
        | pi _ _ DB _ _ _ _ _ _ =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.pi _ _)
            subst e; cases hM
      · rintro l₂ B J hJ ⟨M, hBM, hM, hNM⟩
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.univ _)
            subst e; cases hM
        | nat DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) Whnf.nat
            subst e; cases hM
        | empty DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) Whnf.empty
            subst e; cases hM
        | ne DB hM' _ =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.ne hM')
            subst e
            exact ⟨N, D, hN, E.ty_symm hNM⟩
        | pi _ _ DB _ _ _ _ _ _ =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.pi _ _)
            subst e; cases hM
      · rintro l₂ B J C hJ ⟨M, hBM, hM, hNM⟩ hC
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.univ _)
            subst e; cases hM
        | nat DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) Whnf.nat
            subst e; cases hM
        | empty DB =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) Whnf.empty
            subst e; cases hM
        | ne DB hM' _ =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.ne hM')
            subst e
            obtain ⟨P, hCP, hP, hMP⟩ := hC
            exact ⟨P, hCP, hP, E.ty_trans hNM hMP⟩
        | pi _ _ DB _ _ _ _ _ _ =>
            have e := TyRedsT.whnf_unique hBM DB (Whnf.ne hM) (Whnf.pi _ _)
            subst e; cases hM
  | @pi Γ A F G IF IG D hF hG hPi rF rG extG ihF ihG =>
      -- the domain and codomain are good
      have gF : ∀ Δ ρ, Wk Γ Δ ρ → Good E Δ (rename ρ F) (IF Δ ρ) := ihF
      have gG : ∀ Δ ρ a, Wk Γ Δ ρ → (IF Δ ρ).tmEq a a →
          Good E Δ ((rename (upr ρ) G)[a]) (IG Δ ρ a) := ihG
      -- converting the codomain along related arguments
      have cG : ∀ Δ ρ a b, (hρ : Wk Γ Δ ρ) → (IF Δ ρ).tmEq a b → ∀ t u,
          ((IG Δ ρ a).tmEq t u ↔ (IG Δ ρ b).tmEq t u) := by
        intro Δ ρ a b hρ hab t u
        have ha := (gF Δ ρ hρ).left hab
        have hb := (gF Δ ρ hρ).right hab
        exact (gG Δ ρ a hρ ha).conv (rG Δ ρ b hρ hb).toTyR (extG Δ ρ a b hρ ha hb hab) t u
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- symmetry
        rintro t u ⟨f, g, ht, hu, hnf, hng, hfg, happ⟩
        refine ⟨g, f, hu, ht, hng, hnf, E.tm_symm hfg, fun Δ ρ a b hρ hab => ?_⟩
        have hba := (gF Δ ρ hρ).symm hab
        have h₁ := happ Δ ρ b a hρ hba
        have hb := (gF Δ ρ hρ).right hab
        have h₂ := (gG Δ ρ b hρ hb).symm h₁
        exact (cG Δ ρ b a hρ hba _ _).mp h₂
      · -- transitivity
        rintro t u v ⟨f, g, ht, hu, hnf, hng, hfg, happ⟩ ⟨g', k, hu', hv, hng', hnk, hgk, happ'⟩
        have e := TRedsT_whnf hu hu' hng hng'
        subst e
        refine ⟨f, k, ht, hv, hnf, hnk, E.tm_trans hfg hgk, fun Δ ρ a b hρ hab => ?_⟩
        have ha := (gF Δ ρ hρ).left hab
        have hb := (gF Δ ρ hρ).right hab
        have h₁ := happ Δ ρ a b hρ hab
        have h₂ := happ' Δ ρ b b hρ hb
        have h₂' := (cG Δ ρ a b hρ hab _ _).mpr h₂
        exact (gG Δ ρ a hρ ha).trans h₁ h₂'
      · -- conversion
        rintro l₂ B J hJ ⟨F', G', DB', hE, hdom, hcod⟩ t u
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.univ _)) (by simp)
        | nat DB => exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) Whnf.nat) (by simp)
        | empty DB => exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.ne hN)
            rw [← e] at hN; cases hN
        | pi JF JG DB _ _ _ rF' rG' _ =>
            have e := TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.pi _ _)
            simp only [pi.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            have dom : ∀ Δ ρ, (hρ : Wk Γ Δ ρ) → ∀ a b,
                ((IF Δ ρ).tmEq a b ↔ (JF Δ ρ).tmEq a b) := fun Δ ρ hρ =>
              (gF Δ ρ hρ).conv (rF' Δ ρ hρ).toTyR (hdom Δ ρ hρ)
            have cod : ∀ Δ ρ a, (hρ : Wk Γ Δ ρ) → (ha : (IF Δ ρ).tmEq a a) → ∀ t u,
                ((IG Δ ρ a).tmEq t u ↔ (JG Δ ρ a).tmEq t u) := fun Δ ρ a hρ ha =>
              (gG Δ ρ a hρ ha).conv (rG' Δ ρ a hρ ((dom Δ ρ hρ a a).mp ha)).toTyR
                (hcod Δ ρ a hρ ha)
            have hTE := E.ty_eq hE
            constructor
            · rintro ⟨f, g, ht, hu, hnf, hng, hfg, happ⟩
              refine ⟨f, g, ht.conv hTE, hu.conv hTE, hnf, hng, E.tm_conv hfg hTE,
                fun Δ ρ a b hρ hab => ?_⟩
              have hab' := (dom Δ ρ hρ a b).mpr hab
              exact (cod Δ ρ a hρ ((gF Δ ρ hρ).left hab') _ _).mp (happ Δ ρ a b hρ hab')
            · rintro ⟨f, g, ht, hu, hnf, hng, hfg, happ⟩
              refine ⟨f, g, ht.conv (Der.symmT hTE), hu.conv (Der.symmT hTE), hnf, hng,
                E.tm_conv hfg (Der.symmT hTE), fun Δ ρ a b hρ hab => ?_⟩
              have hab' := (dom Δ ρ hρ a b).mp hab
              exact (cod Δ ρ a hρ ((gF Δ ρ hρ).left hab) _ _).mpr (happ Δ ρ a b hρ hab')
      · -- symmetry of type equality
        rintro l₂ B J hJ ⟨F', G', DB', hE, hdom, hcod⟩
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.univ _)) (by simp)
        | nat DB => exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) Whnf.nat) (by simp)
        | empty DB => exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.ne hN)
            rw [← e] at hN; cases hN
        | pi JF JG DB _ _ _ rF' rG' _ =>
            have e := TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.pi _ _)
            simp only [pi.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            refine ⟨F, G, D, E.ty_symm hE, fun Δ ρ hρ => ?_, fun Δ ρ a hρ ha => ?_⟩
            · exact (gF Δ ρ hρ).tySymm (rF' Δ ρ hρ).toTyR (hdom Δ ρ hρ)
            · have ha' := ((gF Δ ρ hρ).conv (rF' Δ ρ hρ).toTyR (hdom Δ ρ hρ) a a).mpr ha
              exact (gG Δ ρ a hρ ha').tySymm (rG' Δ ρ a hρ ha).toTyR (hcod Δ ρ a hρ ha')
      · -- transitivity of type equality
        rintro l₂ B J C hJ ⟨F', G', DB', hE, hdom, hcod⟩ hC
        rw [TyR.unfold] at hJ
        cases hJ with
        | univ hl₂ DB =>
            exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.univ _)) (by simp)
        | nat DB => exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) Whnf.nat) (by simp)
        | empty DB => exact absurd (TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) Whnf.empty) (by simp)
        | ne DB hN _ =>
            have e := TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.ne hN)
            rw [← e] at hN; cases hN
        | pi JF JG DB _ _ _ rF' rG' _ =>
            have e := TyRedsT.whnf_unique DB' DB (Whnf.pi _ _) (Whnf.pi _ _)
            simp only [pi.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            obtain ⟨F'', G'', DC, hE', hdom', hcod'⟩ := hC
            refine ⟨F'', G'', DC, E.ty_trans hE hE', fun Δ ρ hρ => ?_, fun Δ ρ a hρ ha => ?_⟩
            · exact (gF Δ ρ hρ).tyTrans (rF' Δ ρ hρ).toTyR (hdom Δ ρ hρ) (hdom' Δ ρ hρ)
            · have ha' := ((gF Δ ρ hρ).conv (rF' Δ ρ hρ).toTyR (hdom Δ ρ hρ) a a).mp ha
              exact (gG Δ ρ a hρ ha).tyTrans (rG' Δ ρ a hρ ha').toTyR (hcod Δ ρ a hρ ha)
                (hcod' Δ ρ a hρ ha')

/-! ### Consequences -/

/-- **Irrelevance**: two reducibility proofs of a type have the same interpretation. -/
theorem TyR.irrel {E : GenEq} {l l₂ : ℕ} {Γ : Ctx} {A : Tm} {I J : Interp} (h : TyR E l Γ A I)
    (h₂ : TyR E l₂ Γ A J) : (∀ B, I.tyEq B ↔ J.tyEq B) ∧ (∀ t u, I.tmEq t u ↔ J.tmEq t u) := by
  have g := TyR.good l h
  have g₂ := TyR.good l₂ h₂
  have hJA : J.tyEq A := g.tySymm h₂ h.refl
  exact ⟨fun B => ⟨fun hB => g₂.tyTrans h hJA hB, fun hB => g.tyTrans h₂ h.refl hB⟩,
    g.conv h₂ h.refl⟩

/-- Related terms are reducible. -/
theorem TyR.tmLeft {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t u : Tm} (htu : I.tmEq t u) : I.tmEq t t :=
  (TyR.good l h).left htu

theorem TyR.tmRight {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t u : Tm} (htu : I.tmEq t u) : I.tmEq u u :=
  (TyR.good l h).right htu

end MLTT
