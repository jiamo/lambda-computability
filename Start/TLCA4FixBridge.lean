import Start.TLCA4StatmanStep
import Start.DinfAdequacy
import Start.ScottDinfOmega

/-!
# TLCA open problem 4 under βη: the fixed-point bridge (row M20-TLCA4-STATMAN-STEP-ONE;
series V, round 3, run 1, part A3)

If `toLam (Y x) =βη toLam (x (Y x))` then `toLam (Y x)` has a head normal form whose head is the
free variable `x`.

* `hd_lift`, `Neutral.of_lift` — the free head variable and neutrality under lifting;
* `hnf_betaEtaStep`, `hnf_betaEtaReduces` — βη-reduction keeps a head normal form a head normal
  form with the same free head variable (an η-step at the root `λz. P z → P` included);
* `hasHnf_of_betaEtaConv` — head normalizability is βη-invariant (through `D∞`: `ddenot_convBE`,
  `exists_ddenot_ne_botDinf_of_hasHnf`, `hasHnf_of_ddenot_ne_botDinf`);
* **`hnfHead_of_betaEtaConv`** — a term βη-convertible to a head normal form with free head `x`
  has a (β) head normal form with free head `x`;
* **`fixHeadBridge`** — the proposition `FixHeadBridge` holds;
* `statmanStepOne_of_lemmaOne` — `StatmanStepOne` follows from Lemma 0.1 (`StatmanLemmaOne`).
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

theorem hd_lift (n : ℕ) : ∀ (t : Lambda) (k : ℕ),
    hd (Lambda.lift n k t) = (hd t).map (fun y => if y < k then y else y + n)
  | .var y, k => by
      simp only [Lambda.lift]
      split_ifs with h <;> simp [hd, h]
  | .app f _, k => by simp only [Lambda.lift, hd]; exact hd_lift n f k
  | .lam t, k => by
      simp only [Lambda.lift, hd, hd_lift n t (k + 1)]
      rcases hd t with _ | y
      · rfl
      · by_cases h0 : y = 0
        · subst h0; simp
        · simp only [Option.map_some, Option.bind_some, h0, if_false]
          by_cases hk : y < k + 1
          · have : y - 1 < k := by omega
            simp [hk, this, h0]
          · have h1 : ¬ y - 1 < k := by omega
            have h2 : y + n ≠ 0 := by omega
            simp only [hk, if_false, h2, h1, Option.some.injEq]
            omega

theorem Neutral.of_lift {n k : ℕ} : ∀ {t : Lambda}, Neutral (Lambda.lift n k t) → Neutral t
  | .var y, _ => Neutral.var y
  | .app f a, h => by
      simp only [Lambda.lift] at h
      cases h with
      | app _ hf => exact Neutral.app a (Neutral.of_lift hf)
  | .lam _, h => by simp only [Lambda.lift] at h; cases h

theorem neutral_step_hd {u u' : Lambda} (hn : Neutral u) (hs : Lambda.step u u') :
    hd u' = hd u := by
  induction hs with
  | beta t₁ t₂ => cases hn with | app _ h => cases h
  | app_left t₁ t₁' t₂ _ ih => cases hn with | app _ h => simp only [hd]; exact ih h
  | app_right t₁ t₂ t₂' _ _ => rfl
  | lam t t' _ _ => cases hn

theorem neutral_etaStep {u u' : Lambda} (hn : Neutral u) (hs : etaStep u u') :
    Neutral u' ∧ hd u' = hd u := by
  induction hs with
  | eta t => cases hn
  | app_left a _ ih =>
      cases hn with
      | app _ h => obtain ⟨h1, h2⟩ := ih h; exact ⟨Neutral.app a h1, by simp only [hd]; exact h2⟩
  | app_right f _ _ => cases hn with | app _ h => exact ⟨Neutral.app _ h, rfl⟩
  | lam _ _ => cases hn

theorem isHnf_app_neutral {f a : Lambda} (h : IsHnf (Lambda.app f a)) : Neutral (Lambda.app f a) := by
  cases h with
  | neutral h => exact h

/-- One βη-step keeps a head normal form and its free head variable. -/
theorem hnf_betaEtaStep : ∀ {u u' : Lambda}, IsHnf u → betaEtaStep u u' →
    IsHnf u' ∧ hd u' = hd u
  | _, _, .neutral hn, .beta hs => ⟨.neutral (hn.step hs), neutral_step_hd hn hs⟩
  | _, _, .neutral hn, .eta hs => by
      obtain ⟨h1, h2⟩ := neutral_etaStep hn hs
      exact ⟨.neutral h1, h2⟩
  | _, _, .lam hP, .beta hs => by
      cases hs with
      | lam _ P' hs' =>
          obtain ⟨h1, h2⟩ := hnf_betaEtaStep hP (.beta hs')
          exact ⟨.lam h1, by simp only [hd, h2]⟩
  | _, _, .lam hP, .eta hs => by
      cases hs with
      | eta t =>
          have hn := isHnf_app_neutral hP
          cases hn with
          | app _ hl =>
            refine ⟨.neutral (Neutral.of_lift hl), ?_⟩
            simp only [hd, hd_lift]
            generalize hd _ = o
            cases o <;> simp
      | lam hs' =>
          obtain ⟨h1, h2⟩ := hnf_betaEtaStep hP (.eta hs')
          exact ⟨.lam h1, by simp only [hd, h2]⟩

theorem hnf_betaEtaReduces {u w : Lambda} (hu : IsHnf u) (h : betaEtaReduces u w) :
    IsHnf w ∧ hd w = hd u := by
  induction h with
  | refl => exact ⟨hu, rfl⟩
  | tail _ hs ih =>
      obtain ⟨h1, h2⟩ := ih
      obtain ⟨h3, h4⟩ := hnf_betaEtaStep h1 hs
      exact ⟨h3, h4.trans h2⟩

theorem convBE_of_etaStep {t u : Lambda} (h : etaStep t u) : ScottDinf.ConvBE t u := by
  induction h with
  | eta t => exact .eta t
  | app_left a _ ih => exact .appLeft a ih
  | app_right f _ ih => exact .appRight f ih
  | lam _ ih => exact .lam ih

theorem convBE_of_betaEtaStep {t u : Lambda} (h : betaEtaStep t u) : ScottDinf.ConvBE t u := by
  cases h with
  | beta h => exact .beta h
  | eta h => exact convBE_of_etaStep h

theorem convBE_of_betaEtaConv {t u : Lambda} (h : betaEtaConv t u) : ScottDinf.ConvBE t u := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih => exact .trans ih (convBE_of_betaEtaStep hs)
  | symm_step _ hs ih => exact .trans ih (.symm (convBE_of_betaEtaStep hs))

/-- Head normalizability is βη-invariant (through `D∞`). -/
theorem hasHnf_of_betaEtaConv {t u : Lambda} (h : betaEtaConv t u) (hu : HasHnf u) :
    HasHnf t := by
  obtain ⟨ρ, hρ⟩ := ScottDinf.exists_ddenot_ne_botDinf_of_hasHnf hu
  refine ScottDinf.hasHnf_of_ddenot_ne_botDinf (ρ := ρ) ?_
  rw [ScottDinf.ddenot_convBE (convBE_of_betaEtaConv h) ρ]
  exact hρ

theorem betaEtaConv_of_lreduces {t u : Lambda} (h : Lambda.reduces t u) : betaEtaConv t u :=
  betaEtaConv.of_reduces (betaEtaReduces.of_reduces h)

/-- **A term βη-convertible to a head normal form with free head `x` has a head normal form with
free head `x`.** -/
theorem hnfHead_of_betaEtaConv {t v : Lambda} {x : ℕ} (h : betaEtaConv t v) (hv : IsHnf v)
    (hx : hd v = some x) : HnfHead x t := by
  obtain ⟨u, hr, hu⟩ := hasHnf_of_betaEtaConv h (hasHnf_of_isHnf hv)
  have huv : betaEtaConv u v := (betaEtaConv_symm (betaEtaConv_of_lreduces hr)).trans h
  obtain ⟨w, hw₁, hw₂⟩ := huv.common_reduct
  have e1 := (hnf_betaEtaReduces hu hw₁).2
  have e2 := (hnf_betaEtaReduces hv hw₂).2
  exact ⟨u, hr, hu, e1.symm.trans (e2.trans hx)⟩

/-- **The fixed-point bridge** (A3). -/
theorem fixHeadBridge : FixHeadBridge := fun _ _ hfix =>
  hnfHead_of_betaEtaConv hfix (.neutral (Neutral.app _ (Neutral.var 0))) rfl

/-- `StatmanStepOne` now rests on Lemma 0.1 alone. -/
theorem statmanStepOne_of_lemmaOne (hL : StatmanLemmaOne) : StatmanStepOne :=
  statmanStepOne_of_lemma_bridge hL fixHeadBridge

end TLCA4
