/-
**Martin-Löf type theory: weakening, expansion and neutral terms in the logical relation** —
milestone M30 (`M30-MLTT-LR`).

* `TyR.wk` — **weakening** (Kripke monotonicity): a reducible type stays reducible under a
  renaming into a well-formed context, and its reducible equalities are carried along;
* `TyR.expand`, `TyR.expandTm` — **closure under weak head expansion**: a type reducing to a
  reducible type is reducible (with the same interpretation), and a term reducing to a term
  related to `u` is related to `u`;
* `TyR.neutral` — **reflection of neutral terms**: two neutral terms that are generically equal
  are reducibly equal; in particular variables are reducible (`TyR.var`).
-/

import Start.MLTTLogRelProps

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Auxiliary facts -/

theorem Wk.comp {Γ Δ Θ : Ctx} {ρ ρ' : ℕ → ℕ} (h : Wk Γ Δ ρ) (h' : Wk Δ Θ ρ') :
    Wk Γ Θ (fun n => ρ' (ρ n)) :=
  ⟨h.1.comp h'.1, h'.2⟩

theorem rename_upr_comp (ρ ρ' : ℕ → ℕ) (G : Tm) :
    rename (upr ρ') (rename (upr ρ) G) = rename (upr (fun n => ρ' (ρ n))) G := by
  rw [rename_rename]
  exact rename_congr (upr_comp ρ' ρ) G

theorem TRedsT.trans {Γ : Ctx} {t u v A : Tm} (h₁ : TRedsT Γ t u A) (h₂ : TRedsT Γ u v A) :
    TRedsT Γ t v A :=
  ⟨h₁.tyL, h₂.tyR, h₁.red.trans h₂.red⟩

theorem TReds.toTyReds {Γ : Ctx} {A B T : Tm} (h : TReds Γ A B T) :
    ∀ l, T = univ l → TyReds Γ A B := by
  induction h with
  | refl hA => intro l e; subst e; exact TyReds.refl (Der.el hA)
  | step hs _ ih => intro l e; subst e; exact TyReds.step hs (ih l rfl)

theorem TRedsT.toTy {Γ : Ctx} {A B : Tm} {l : ℕ} (h : TRedsT Γ A B (univ l)) : TyRedsT Γ A B :=
  ⟨Der.el h.tyL, Der.el h.tyR, h.red.toTyReds l rfl⟩

theorem TyRedsT.trans {Γ : Ctx} {A B C : Tm} (h₁ : TyRedsT Γ A B) (h₂ : TyRedsT Γ B C) :
    TyRedsT Γ A C :=
  ⟨h₁.wfL, h₂.wfR, h₁.red.trans h₂.red⟩

theorem NatR.rename {E : GenEq} {Γ Δ : Ctx} {ρ : ℕ → ℕ} (hρ : Wk Γ Δ ρ) {t u : Tm}
    (h : NatR E Γ t u) : NatR E Δ (MLTT.rename ρ t) (MLTT.rename ρ u) := by
  induction h with
  | zero ht hu => exact NatR.zero (ht.rename hρ.1 hρ.2) (hu.rename hρ.1 hρ.2)
  | succ ht hu hsm _ ih =>
      exact NatR.succ (ht.rename hρ.1 hρ.2) (hu.rename hρ.1 hρ.2) (E.tm_wk hρ.1 hρ.2 hsm) ih
  | ne ht hu hn hm hnm =>
      exact NatR.ne (ht.rename hρ.1 hρ.2) (hu.rename hρ.1 hρ.2) (hn.rename ρ) (hm.rename ρ)
        (E.ne_wk hρ.1 hρ.2 hnm)

/-! ### Weakening -/

/-- **Weakening of the logical relation.** -/
theorem TyR.wk {E : GenEq} : ∀ (l : ℕ) {Γ : Ctx} {A : Tm} {I : Interp}, TyR E l Γ A I →
    ∀ {Δ : Ctx} {ρ : ℕ → ℕ}, Wk Γ Δ ρ → ∃ J, TyR E l Δ (rename ρ A) J ∧
      (∀ B, I.tyEq B → J.tyEq (rename ρ B)) ∧
      (∀ t u, I.tmEq t u → J.tmEq (rename ρ t) (rename ρ u)) := by
  intro l
  induction l using Nat.strong_induction_on with
  | _ l ihl =>
  intro Γ A I h
  rw [TyR.unfold] at h
  induction h with
  | @univ Γ A l' hl D =>
      intro Δ ρ hρ
      refine ⟨_, (TyRAt.univ (lo := fun l' _ => TyR E l') hl (D.rename hρ.1 hρ.2)).toTyR,
        fun B hB => hB.rename hρ.1 hρ.2, ?_⟩
      rintro t u ⟨t', u', ht, hu, hnt, hnu, htu, ⟨It, hIt, hItu⟩, ⟨Ju, hJu⟩⟩
      obtain ⟨Jt, hJt, hJt₁, -⟩ := ihl l' hl hIt hρ
      obtain ⟨Ju', hJu', -, -⟩ := ihl l' hl hJu hρ
      exact ⟨_, _, ht.rename hρ.1 hρ.2, hu.rename hρ.1 hρ.2, hnt.rename ρ, hnu.rename ρ,
        E.tm_wk hρ.1 hρ.2 htu, ⟨Jt, hJt, hJt₁ u hItu⟩, ⟨Ju', hJu'⟩⟩
  | @nat Γ A D =>
      intro Δ ρ hρ
      exact ⟨_, (TyRAt.nat (lo := fun l' _ => TyR E l') (D.rename hρ.1 hρ.2)).toTyR,
        fun B hB => hB.rename hρ.1 hρ.2, fun t u h => h.rename hρ⟩
  | @empty Γ A D =>
      intro Δ ρ hρ
      refine ⟨_, (TyRAt.empty (lo := fun l' _ => TyR E l') (D.rename hρ.1 hρ.2)).toTyR,
        fun B hB => hB.rename hρ.1 hρ.2, ?_⟩
      rintro t u ⟨n, m, ht, hu, hn, hm, hnm⟩
      exact ⟨_, _, ht.rename hρ.1 hρ.2, hu.rename hρ.1 hρ.2, hn.rename ρ, hm.rename ρ,
        E.ne_wk hρ.1 hρ.2 hnm⟩
  | @ne Γ A N k D hN hNN =>
      intro Δ ρ hρ
      refine ⟨_, (TyRAt.ne (lo := fun l' _ => TyR E l') (D.rename hρ.1 hρ.2) (hN.rename ρ)
        (E.ne_wk hρ.1 hρ.2 hNN)).toTyR, ?_, ?_⟩
      · rintro B ⟨M, hBM, hM, hNM⟩
        exact ⟨_, hBM.rename hρ.1 hρ.2, hM.rename ρ, E.ty_wk hρ.1 hρ.2 hNM⟩
      · rintro t u ⟨n, m, ht, hu, hn, hm, hnm⟩
        exact ⟨_, _, ht.rename hρ.1 hρ.2, hu.rename hρ.1 hρ.2, hn.rename ρ, hm.rename ρ,
          E.ne_wk hρ.1 hρ.2 hnm⟩
  | @pi Γ A F G IF IG D hF hG hPi rF rG extG _ _ =>
      intro Δ ρ hρ
      have hF' : WfTy Δ (rename ρ F) := hF.rename hρ.1 hρ.2
      have hG' : WfTy (rename ρ F :: Δ) (rename (upr ρ) G) :=
        hG.rename (hρ.1.up F) (Der.cons hρ.2 hF')
      have D' : TyRedsT Δ (rename ρ A) (pi (rename ρ F) (rename (upr ρ) G)) := by
        simpa using D.rename hρ.1 hρ.2
      have hPi' : E.ty Δ (pi (rename ρ F) (rename (upr ρ) G)) (pi (rename ρ F) (rename (upr ρ) G)) := by
        simpa using E.ty_wk hρ.1 hρ.2 hPi
      let IF' : Ctx → (ℕ → ℕ) → Interp := fun Δ' ρ' => IF Δ' (fun n => ρ' (ρ n))
      let IG' : Ctx → (ℕ → ℕ) → Tm → Interp := fun Δ' ρ' a => IG Δ' (fun n => ρ' (ρ n)) a
      have rF' : ∀ Δ' ρ', Wk Δ Δ' ρ' →
          TyRAt E l (fun l' _ => TyR E l') Δ' (rename ρ' (rename ρ F)) (IF' Δ' ρ') := by
        intro Δ' ρ' hρ'
        rw [rename_rename]
        exact rF Δ' _ (hρ.comp hρ')
      have rG' : ∀ Δ' ρ' a, Wk Δ Δ' ρ' → (IF' Δ' ρ').tmEq a a →
          TyRAt E l (fun l' _ => TyR E l') Δ' ((rename (upr ρ') (rename (upr ρ) G))[a])
            (IG' Δ' ρ' a) := by
        intro Δ' ρ' a hρ' ha
        rw [rename_upr_comp]
        exact rG Δ' _ a (hρ.comp hρ') ha
      have extG' : ∀ Δ' ρ' a b, Wk Δ Δ' ρ' → (IF' Δ' ρ').tmEq a a → (IF' Δ' ρ').tmEq b b →
          (IF' Δ' ρ').tmEq a b → (IG' Δ' ρ' a).tyEq ((rename (upr ρ') (rename (upr ρ) G))[b]) := by
        intro Δ' ρ' a b hρ' ha hb hab
        rw [rename_upr_comp]
        exact extG Δ' _ a b (hρ.comp hρ') ha hb hab
      refine ⟨_, (TyRAt.pi IF' IG' D' hF' hG' hPi' rF' rG' extG').toTyR, ?_, ?_⟩
      · rintro B ⟨F₁, G₁, DB, hE, hdom, hcod⟩
        refine ⟨rename ρ F₁, rename (upr ρ) G₁, by simpa using DB.rename hρ.1 hρ.2,
          by simpa using E.ty_wk hρ.1 hρ.2 hE, fun Δ' ρ' hρ' => ?_, fun Δ' ρ' a hρ' ha => ?_⟩
        · rw [rename_rename]; exact hdom Δ' _ (hρ.comp hρ')
        · rw [rename_upr_comp]; exact hcod Δ' _ a (hρ.comp hρ') ha
      · rintro t u ⟨f, g, ht, hu, hnf, hng, hfg, happ⟩
        refine ⟨rename ρ f, rename ρ g, by simpa using ht.rename hρ.1 hρ.2,
          by simpa using hu.rename hρ.1 hρ.2, hnf.rename ρ, hng.rename ρ,
          by simpa using E.tm_wk hρ.1 hρ.2 hfg, fun Δ' ρ' a b hρ' hab => ?_⟩
        rw [rename_rename, rename_rename]
        exact happ Δ' _ a b (hρ.comp hρ') hab

/-! ### Expansion -/

/-- **A type reducing to a reducible type is reducible**, with the same interpretation. -/
theorem TyR.expand {E : GenEq} {l : ℕ} {Γ : Ctx} {A A' : Tm} {I : Interp}
    (hA : TyRedsT Γ A A') (h : TyR E l Γ A' I) : TyR E l Γ A I := by
  rw [TyR.unfold] at h ⊢
  cases h with
  | univ hl D => exact TyRAt.univ hl (hA.trans D)
  | nat D => exact TyRAt.nat (hA.trans D)
  | empty D => exact TyRAt.empty (hA.trans D)
  | ne D hN hNN => exact TyRAt.ne (hA.trans D) hN hNN
  | pi IF IG D hF hG hPi rF rG extG => exact TyRAt.pi IF IG (hA.trans D) hF hG hPi rF rG extG

theorem NatR.expand {E : GenEq} {Γ : Ctx} {t t' u : Tm} (ht : TRedsT Γ t t' Tm.nat)
    (h : NatR E Γ t' u) : NatR E Γ t u := by
  cases h with
  | zero ht' hu => exact NatR.zero (ht.trans ht') hu
  | succ ht' hu hsm hr => exact NatR.succ (ht.trans ht') hu hsm hr
  | ne ht' hu hn hm hnm => exact NatR.ne (ht.trans ht') hu hn hm hnm

/-- **A term reducing to a term related to `u` is related to `u`.** -/
theorem TyR.expandTm {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t t' u : Tm} (ht : TRedsT Γ t t' A) (htu : I.tmEq t' u) : I.tmEq t u := by
  rw [TyR.unfold] at h
  cases h with
  | univ hl D =>
      obtain ⟨t'', u', ht', hu, hnt, hnu, htu', ⟨It, hIt, hItu⟩, hJu⟩ := htu
      have htU := ht.conv D.tyEq
      exact ⟨t'', u', htU.trans ht', hu, hnt, hnu, htu', ⟨It, hIt.expand htU.toTy, hItu⟩, hJu⟩
  | nat D => exact NatR.expand (ht.conv D.tyEq) htu
  | empty D =>
      obtain ⟨n, m, ht', hu, hn, hm, hnm⟩ := htu
      exact ⟨n, m, (ht.conv D.tyEq).trans ht', hu, hn, hm, hnm⟩
  | ne D hN _ =>
      obtain ⟨n, m, ht', hu, hn, hm, hnm⟩ := htu
      exact ⟨n, m, (ht.conv D.tyEq).trans ht', hu, hn, hm, hnm⟩
  | pi IF IG D _ _ _ _ _ _ =>
      obtain ⟨f, g, ht', hu, hnf, hng, hfg, happ⟩ := htu
      exact ⟨f, g, (ht.conv D.tyEq).trans ht', hu, hnf, hng, hfg, happ⟩

/-- Expansion on the right. -/
theorem TyR.expandTm' {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t u u' : Tm} (hu : TRedsT Γ u u' A) (htu : I.tmEq t u') : I.tmEq t u :=
  (TyR.good l h).symm (h.expandTm hu ((TyR.good l h).symm htu))

/-! ### Escape for type equality -/

/-- **Escape for type equality**: reducibly equal types are generically equal. -/
theorem TyRAt.escapeTyEq {E : GenEq} {l : ℕ} {lo : (l' : ℕ) → l' < l → Ctx → Tm → Interp → Prop}
    {Γ : Ctx} {A : Tm} {I : Interp} (h : TyRAt E l lo Γ A I) {B : Tm} (hB : I.tyEq B) :
    E.ty Γ A B := by
  cases h with
  | univ hl D => exact E.ty_red D hB (Whnf.univ _) (Whnf.univ _) (E.univ_refl _ D.wfL.wf)
  | nat D => exact E.ty_red D hB Whnf.nat Whnf.nat (E.nat_refl D.wfL.wf)
  | empty D => exact E.ty_red D hB Whnf.empty Whnf.empty (E.empty_refl D.wfL.wf)
  | ne D hN _ =>
      obtain ⟨M, hBM, hM, hNM⟩ := hB
      exact E.ty_red D hBM (Whnf.ne hN) (Whnf.ne hM) hNM
  | pi IF IG D _ _ _ _ _ _ =>
      obtain ⟨F', G', DB, hE, -, -⟩ := hB
      exact E.ty_red D DB (Whnf.pi _ _) (Whnf.pi _ _) hE

theorem TyR.escapeTyEq {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {B : Tm} (hB : I.tyEq B) : E.ty Γ A B := by
  rw [TyR.unfold] at h
  exact h.escapeTyEq hB

/-! ### Neutral terms -/

theorem E_ne_refl {E : GenEq} {Γ : Ctx} {n m A : Tm} (h : E.ne Γ n m A) : E.ne Γ n n A :=
  E.ne_trans h (E.ne_symm h)

/-- **Reflection of neutral terms**: generically equal neutral terms are reducibly equal. -/
theorem TyR.neutral {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I) :
    ∀ {n m : Tm}, Neutral n → Neutral m → HasTy Γ n A → HasTy Γ m A → E.ne Γ n m A →
      I.tmEq n m := by
  rw [TyR.unfold] at h
  induction h with
  | @univ Γ A l' hl D =>
      intro n m hn hm htn htm hnm
      have hTE := D.tyEq
      have hnmU := E.ne_conv hnm hTE
      have hnU := Der.conv htn hTE
      have hmU := Der.conv htm hTE
      refine ⟨n, m, TRedsT.refl hnU, TRedsT.refl hmU, Whnf.ne hn, Whnf.ne hm, E.ne_tm hnmU,
        ⟨_, (TyRAt.ne (lo := fun l'' _ => TyR E l'') (TyRedsT.refl (Der.el hnU)) hn
          (E_ne_refl hnmU)).toTyR, ⟨m, TyRedsT.refl (Der.el hmU), hm, E.univ (E.ne_tm hnmU)⟩⟩,
        ⟨_, (TyRAt.ne (lo := fun l'' _ => TyR E l'') (TyRedsT.refl (Der.el hmU)) hm
          (E_ne_refl (E.ne_symm hnmU))).toTyR⟩⟩
  | @nat Γ A D =>
      intro n m hn hm htn htm hnm
      have hTE := D.tyEq
      exact NatR.ne (TRedsT.refl (Der.conv htn hTE)) (TRedsT.refl (Der.conv htm hTE)) hn hm
        (E.ne_conv hnm hTE)
  | @empty Γ A D =>
      intro n m hn hm htn htm hnm
      have hTE := D.tyEq
      exact ⟨n, m, TRedsT.refl (Der.conv htn hTE), TRedsT.refl (Der.conv htm hTE), hn, hm,
        E.ne_conv hnm hTE⟩
  | @ne Γ A N k D hN _ =>
      intro n m hn hm htn htm hnm
      have hTE := D.tyEq
      exact ⟨n, m, TRedsT.refl (Der.conv htn hTE), TRedsT.refl (Der.conv htm hTE), hn, hm,
        E.ne_conv hnm hTE⟩
  | @pi Γ A F G IF IG D hF hG hPi rF rG extG ihF ihG =>
      intro n m hn hm htn htm hnm
      have hTE := D.tyEq
      have htn' := Der.conv htn hTE
      have htm' := Der.conv htm hTE
      have hnm' := E.ne_conv hnm hTE
      refine ⟨n, m, TRedsT.refl htn', TRedsT.refl htm', Whnf.ne hn, Whnf.ne hm, E.ne_tm hnm',
        fun Δ ρ a b hρ hab => ?_⟩
      have hF' := (rF Δ ρ hρ).toTyR
      have ha := hF'.tmLeft hab
      obtain ⟨hta, htb, hab'⟩ := hF'.escapeTm hab
      have hnmρ : E.ne Δ (rename ρ n) (rename ρ m) (pi (rename ρ F) (rename (upr ρ) G)) := by
        simpa using E.ne_wk hρ.1 hρ.2 hnm'
      have htnρ : HasTy Δ (rename ρ n) (pi (rename ρ F) (rename (upr ρ) G)) := by
        simpa using HasTy.rename htn' hρ.1 hρ.2
      have htmρ : HasTy Δ (rename ρ m) (pi (rename ρ F) (rename (upr ρ) G)) := by
        simpa using HasTy.rename htm' hρ.1 hρ.2
      have hGa := (rG Δ ρ a hρ ha).toTyR
      have hGab : (IG Δ ρ a).tyEq ((rename (upr ρ) G)[b]) :=
        extG Δ ρ a b hρ ha (hF'.tmRight hab) hab
      -- the type of `m b` is `G[b]`, equal to `G[a]`
      have hTyEq : TyEq Δ ((rename (upr ρ) G)[b]) ((rename (upr ρ) G)[a]) :=
        Der.symmT (E.ty_eq (TyR.escapeTyEq hGa hGab))
      exact ihG Δ ρ a hρ ha (Neutral.app a (hn.rename ρ)) (Neutral.app b (hm.rename ρ))
        (Der.app htnρ hta) (Der.conv (Der.app htmρ htb) hTyEq) (E.app_cong hnmρ hab')

/-- Variables are reducible. -/
theorem TyR.var {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I) {n : ℕ}
    (hn : HasTy Γ (var n) A) : I.tmEq (var n) (var n) :=
  h.neutral (Neutral.var n) (Neutral.var n) hn hn (E.var_refl hn)

end MLTT
