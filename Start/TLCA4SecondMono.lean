import Start.TLCA4HeadM

/-!
# Series V, big round, run 5, item A3: the second monomial of a βη fixed-point polynomial
(row M20-TLCA4-BETAETA)

The two arguments that fixed the first monomial (`GY` pairing, `Start/TLCA4FirstMono.lean`, and
occurrence counting in the λI-calculus, `Start/TLCA4HeadM.lean`) apply to the second monomial of
`P = M ∘ m₂ ∘ …` after applying the fixed-point equation to enough fresh variables.

* `gy_contra`, `occ_contra` — the two contradictions, for an arbitrary left-hand side;
* `poly_tail` — `(m ∘ ps) x = m u` with `u` free of the fresh variables;
* **`secondBB_not_fixedPoint`** — `M ∘ Bᵃ⁺¹ B ∘ …` is not a βη fixed-point combinator;
* **`secondBM_not_fixedPoint`** — `M ∘ Bᵃ⁺² M ∘ …` is not a βη fixed-point combinator;
* **`polyFiveOne_second`** — `PolyFiveOne` has a witness `M ∘ m₂ ∘ …` without base-`I` monomials
  and with `m₂ ∈ {B, M, B M}`.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

/-- The `GY` contradiction behind `headB_not_fixedPoint`, for any left-hand side. -/
theorem gy_contra (n : ℕ) (Y : Tm) (zs : List Tm) (t : Tm)
    (hGY : GY (n + 1) (n + 2) (toLam t))
    (hc : betaEtaConv (toLam t)
      (toLam (apps (Tm.app (Tm.var 0) (Tm.app Y (Tm.var 0)))
        (zs ++ [Tm.var (n + 1), Tm.var (n + 2)])))) :
    False := by
  obtain ⟨cs', hcs'⟩ := toLam_apps_spn (y := 0) (cs := [toLam (Tm.app Y (Tm.var 0))])
    (f := Tm.app (Tm.var 0) (Tm.app Y (Tm.var 0))) (zs ++ [Tm.var (n + 1)]) rfl
  have hR : toLam (apps (Tm.app (Tm.var 0) (Tm.app Y (Tm.var 0)))
      (zs ++ [Tm.var (n + 1), Tm.var (n + 2)])) = lamK 0 (spn 0 (.var (n + 2) :: cs')) := by
    rw [show zs ++ [Tm.var (n + 1), Tm.var (n + 2)] =
        (zs ++ [Tm.var (n + 1)]) ++ [Tm.var (n + 2)] by simp, apps_append]
    simp only [apps, toLam, hcs', lamK, spn]
  rw [hR] at hc
  obtain ⟨w, h1, h2⟩ := hc.common_reduct
  have hw := hGY.betaEtaReduces h1
  obtain ⟨j, z, pre, post, cs, hj, hy, hl, rfl, hpre, hpost⟩ := RForm.betaEtaReduces h2
  obtain rfl : j = 0 := by omega
  cases hpre
  simp only [List.nil_append] at hl
  subst hl
  cases hpost with
  | cons hc0 _ =>
    rename_i c cs2
    rw [Lambda.lift_zero] at hc0
    have := var_betaEtaReduces hc0
    subst this
    simp only [Nat.sub_zero, lamK, spn] at hw
    rcases hw.app_inv with ⟨h3, _⟩ | ⟨_, h4⟩
    · cases cs2 with
      | nil => simp [spn] at h3; omega
      | cons _ _ => simp [spn] at h3
    · exact h4.var_inv rfl

/-- The tail `u` of a polynomial `m ∘ ps` applied to `x`: `(m ∘ ps) x = m u`. -/
theorem poly_tail (m : Mono) (ps : List Mono) :
    ∃ u : Tm, Tm.WEq (Tm.app (polyTm m ps) (Tm.var 0)) (Tm.app m.tm u) ∧
      ∀ a b : ℕ, 0 < b → GY a b (toLam u) := by
  cases ps with
  | nil => exact ⟨Tm.var 0, .refl _, fun a b hb => .var (by omega)⟩
  | cons m3 ps =>
    refine ⟨Tm.app (polyTm m3 ps) (Tm.var 0), comp_action _ _ _, fun a b hb => ?_⟩
    exact .app (GY.toLam_closed (polyTm_isBMI m3 ps)) (.var (by omega))

/-- **The second monomial of a βη fixed-point polynomial `M ∘ m₂ ∘ …` is not `Bᵃ⁺¹ B`.** -/
theorem secondBB_not_fixedPoint (a : ℕ) (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨a + 1, .B⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (⟨a + 1, .B⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨a + 1, .B⟩ :: ps)
  set R := polyTm ⟨a + 1, .B⟩ ps
  obtain ⟨u, hu, hGYu⟩ := poly_tail ⟨a + 1, .B⟩ ps
  set zs : List Tm := (List.range a).map (fun i => Tm.var (i + 1)) with hzs
  have hzl : (Tm.app R (Tm.var 0) :: zs).length = a + 1 := by simp [hzs]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (zs ++ [Tm.var (a + 1), Tm.var (a + 2)]))
      (apps u ((Tm.app R (Tm.var 0) :: zs) ++ [Tm.app (Tm.var (a + 1)) (Tm.var (a + 2))])) := by
    refine (comp_action_apps Tm.M R (Tm.var 0) _).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) _).trans ?_
    refine (Tm.WEq.apps (Tm.WEq.appL hu _) _).trans ?_
    exact bpowB_action (a + 1) u (Tm.app R (Tm.var 0) :: zs) hzl (Tm.var (a + 1))
      (Tm.var (a + 2)) []
  refine gy_contra a P zs _ ?_ ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  refine GY.toLam_apps (hGYu _ _ (by omega)) ?_
  intro z hz
  simp only [List.cons_append, List.mem_cons, List.mem_append, hzs, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | ⟨i, hi, rfl⟩ | rfl
  · exact .app (GY.toLam_closed (polyTm_isBMI _ _)) (.var (by omega))
  · exact .var (by omega)
  · exact .pair

/-- The occurrence contradiction behind `headBM_not_fixedPoint`, for any left-hand side. -/
theorem occ_contra (n : ℕ) (Y : Tm) (hYc : Tm.IsBMI Y) (t : Tm)
    (h2 : 2 ≤ occL (n + 1) (toLam t))
    (hc : betaEtaConv (toLam t) (toLam (apps (Tm.app (Tm.var 0) (Tm.app Y (Tm.var 0)))
      ((List.range n).map (fun i => Tm.var (i + 1)) ++ [Tm.var (n + 1)])))) : False := by
  set pre : List Tm := (List.range n).map (fun i => Tm.var (i + 1)) with hpre
  obtain ⟨cs', hcs'⟩ := toLam_apps_spn (y := 0) (cs := [toLam (Tm.app Y (Tm.var 0))])
    (f := Tm.app (Tm.var 0) (Tm.app Y (Tm.var 0))) pre rfl
  have hocc' : occL (n + 1) (spn 0 cs') = 0 := by
    rw [← hcs', occL_toLam_apps]
    simp only [toLam, occL, occL_toLam_closed hYc, hpre, List.map_map]
    rw [List.sum_eq_zero]
    · simp
    · intro a ha
      simp only [List.mem_map, List.mem_range, Function.comp] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp [toLam, occL]; omega
  have hR : toLam (apps (Tm.app (Tm.var 0) (Tm.app Y (Tm.var 0))) (pre ++ [Tm.var (n + 1)])) =
      lamK 0 (spn 0 (.var (n + 1) :: cs')) := by
    rw [apps_append]
    simp only [apps, toLam, hcs', lamK, spn]
  rw [hR] at hc
  obtain ⟨w, h1, h2'⟩ := hc.common_reduct
  have hw1 : 2 ≤ occL (n + 1) w :=
    h2.trans (((lamI_toLam t).betaEtaReduces h1).2 (n + 1))
  obtain ⟨j, z, pre', post, cs, hj, hy, hl, rfl, hpre', hpost⟩ := RForm.betaEtaReduces h2'
  obtain rfl : j = 0 := by omega
  obtain rfl : z = 0 := by omega
  cases hpre'
  simp only [List.nil_append] at hl
  subst hl
  cases hpost with
  | cons hc0 hrest =>
    rename_i c cs2
    rw [Lambda.lift_zero] at hc0
    have := var_betaEtaReduces hc0
    subst this
    have hrest' : List.Forall₂ betaEtaReduces cs' cs2 :=
      hrest.imp (fun a b hab => by rwa [Lambda.lift_zero] at hab)
    have h0 := occL_zero_betaEtaReduces (spn_betaEtaReduces (z := 0) hrest') (n + 1) hocc'
    simp only [Nat.sub_zero, lamK, spn, occL, ↓reduceIte, h0] at hw1
    omega

/-- **The second monomial of a βη fixed-point polynomial `M ∘ m₂ ∘ …` is not `Bᵃ⁺² M`.** -/
theorem secondBM_not_fixedPoint (a : ℕ) (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨a + 2, .M⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (⟨a + 2, .M⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨a + 2, .M⟩ :: ps)
  set R := polyTm ⟨a + 2, .M⟩ ps
  obtain ⟨u, hu, -⟩ := poly_tail ⟨a + 2, .M⟩ ps
  set zs : List Tm := (List.range a).map (fun i => Tm.var (i + 1)) ++ [Tm.var (a + 1)] with hzs
  set W : Tm := apps u (Tm.app R (Tm.var 0) :: zs)
  have hzl : (Tm.app R (Tm.var 0) :: zs).length = a + 2 := by simp [hzs]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) zs) (Tm.app W W) := by
    refine (comp_action_apps Tm.M R (Tm.var 0) _).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) _).trans ?_
    refine (Tm.WEq.apps (Tm.WEq.appL hu _) _).trans ?_
    exact bpowM_action (a + 2) u (Tm.app R (Tm.var 0) :: zs) hzl
  refine occ_contra a P (polyTm_isBMI _ _) (Tm.app W W) ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  have hW : 1 ≤ occL (a + 1) (toLam W) := by
    simp only [W, occL_toLam_apps, hzs, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, toLam, occL, ↓reduceIte]
    omega
  simp only [toLam, occL]
  omega

/-- **The first two monomials of a βη fixed-point polynomial**: `PolyFiveOne` has a witness
`M ∘ m₂ ∘ m₃ ∘ … ∘ m_k` with no monomial of base `I` and `m₂ ∈ {B, M, B M}`. -/
theorem polyFiveOne_second (h : PolyFiveOne) :
    ∃ (m₂ : Mono) (ps : List Mono),
      (m₂ = ⟨0, .B⟩ ∨ m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩) ∧
      (∀ q ∈ (⟨0, .M⟩ : Mono) :: m₂ :: ps, q.base ≠ .I) ∧
      betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: ps)) (Tm.var 0)))
        (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: ps)) (Tm.var 0)))) := by
  obtain ⟨⟨k, b⟩, ps, hI, hfix⟩ := polyFiveOne_head_M h
  cases b with
  | I => exact (hI ⟨k, .I⟩ (by simp) rfl).elim
  | B =>
    cases k with
    | zero => exact ⟨_, ps, .inl rfl, hI, hfix⟩
    | succ a => exact (secondBB_not_fixedPoint a ps hfix).elim
  | M =>
    match k with
    | 0 => exact ⟨_, ps, .inr (.inl rfl), hI, hfix⟩
    | 1 => exact ⟨_, ps, .inr (.inr rfl), hI, hfix⟩
    | a + 2 => exact (secondBM_not_fixedPoint a ps hfix).elim

end TLCA4
