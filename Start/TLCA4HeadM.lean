import Start.TLCA4FirstMono

/-!
# Series V, big round, run 5, item A3: the first monomial of a βη fixed-point polynomial is `M`
(row M20-TLCA4-BETAETA)

Occurrence counting in the λI-calculus excludes a first monomial `Bⁿ⁺¹ M`.

* `occL y t` — the number of free occurrences of the variable `y`; `occL_lift_*`, **`occL_subst`**;
* `LamI t` — every abstraction binds a variable that occurs; `lamI_toLam`: every
  `B`,`M`,`I`-term with variables translates to a λI-term;
* **`LamI.betaEtaReduces`** — βη-reduction of a λI-term preserves `LamI` and never decreases the
  number of occurrences of a free variable; `occL_zero_betaEtaReduces` — no variable appears;
* **`headBM_not_fixedPoint`** — no polynomial `Bⁿ⁺¹ M ∘ R` is a βη fixed-point combinator: applied
  to fresh `z₁ … z_{n+1}`, the fixed-point equation gives `U U =βη x (P x) z⃗` with `U = R x z⃗`;
  `z_{n+1}` occurs at least twice on the left and in all its reducts, and exactly once in every
  reduct of the right-hand side;
* **`polyFiveOne_head_M`** — `PolyFiveOne` has a witness `M ∘ m₂ ∘ … ∘ m_k`, `k ≥ 2`, without
  monomials of base `I`.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

/-- Number of free occurrences of the variable `y`. -/
def occL (y : ℕ) : Lambda → ℕ
  | .var n => if n = y then 1 else 0
  | .app f a => occL y f + occL y a
  | .lam t => occL (y + 1) t

theorem occL_lift_lt : ∀ (s : Lambda) (k y : ℕ), y < k → occL y (Lambda.lift 1 k s) = occL y s
  | .var n, k, y, h => by
    simp only [Lambda.lift]
    split_ifs
    · rfl
    · simp only [occL]; split_ifs <;> omega
  | .app f a, k, y, h => by
    simp only [Lambda.lift, occL, occL_lift_lt f k y h, occL_lift_lt a k y h]
  | .lam t, k, y, h => by simp only [Lambda.lift, occL, occL_lift_lt t (k + 1) (y + 1) (by omega)]

theorem occL_lift_ge : ∀ (s : Lambda) (k y : ℕ), k ≤ y → occL (y + 1) (Lambda.lift 1 k s) = occL y s
  | .var n, k, y, h => by
    simp only [Lambda.lift]; split_ifs <;> simp only [occL] <;> split_ifs <;> omega
  | .app f a, k, y, h => by simp only [Lambda.lift, occL, occL_lift_ge f k y h, occL_lift_ge a k y h]
  | .lam t, k, y, h => by simp only [Lambda.lift, occL, occL_lift_ge t (k + 1) (y + 1) (by omega)]

theorem occL_lift_eq : ∀ (s : Lambda) (k : ℕ), occL k (Lambda.lift 1 k s) = 0
  | .var n, k => by
    simp only [Lambda.lift]; split_ifs <;> simp only [occL] <;> split_ifs <;> omega
  | .app f a, k => by simp only [Lambda.lift, occL, occL_lift_eq f k, occL_lift_eq a k]
  | .lam t, k => by simp only [Lambda.lift, occL, occL_lift_eq t (k + 1)]

theorem occL_subst : ∀ (M s : Lambda) (x y : ℕ),
    occL y (Lambda.subst s x M) = occL (if y < x then y else y + 1) M + occL x M * occL y s
  | .var n, s, x, y => by
    simp only [Lambda.subst, occL]
    split_ifs <;> simp_all [occL] <;> omega
  | .app f a, s, x, y => by
    simp only [Lambda.subst, occL, occL_subst f s x y, occL_subst a s x y]; ring
  | .lam t, s, x, y => by
    simp only [Lambda.subst, occL, occL_subst t _ (x + 1) (y + 1),
      occL_lift_ge s 0 y (Nat.zero_le _)]
    by_cases h : y < x
    · simp [h, show y + 1 < x + 1 by omega]
    · simp [h, show ¬ y + 1 < x + 1 by omega]

/-- λI-terms: every abstraction binds a variable that occurs. -/
inductive LamI : Lambda → Prop
  | var (n : ℕ) : LamI (.var n)
  | app {f a : Lambda} : LamI f → LamI a → LamI (.app f a)
  | lam {t : Lambda} : LamI t → 0 < occL 0 t → LamI (.lam t)

theorem LamI.lift {s : Lambda} (h : LamI s) : ∀ k, LamI (Lambda.lift 1 k s) := by
  induction h with
  | var n => intro k; simp only [Lambda.lift]; split_ifs <;> exact .var _
  | app _ _ ih1 ih2 => intro k; exact .app (ih1 k) (ih2 k)
  | lam _ hpos ih =>
    intro k
    exact .lam (ih (k + 1)) (by rw [occL_lift_lt _ _ _ (by omega)]; exact hpos)

theorem LamI.subst {M : Lambda} (hM : LamI M) : ∀ (s : Lambda) (x : ℕ), LamI s →
    LamI (Lambda.subst s x M) := by
  induction hM with
  | var n =>
    intro s x hs
    simp only [Lambda.subst]; split_ifs
    · exact hs
    · exact .var _
    · exact .var _
  | app _ _ ih1 ih2 => intro s x hs; exact .app (ih1 s x hs) (ih2 s x hs)
  | @lam t _ hpos ih =>
    intro s x hs
    refine .lam (ih _ _ (hs.lift 0)) ?_
    rw [occL_subst]
    simp only [show (0 : ℕ) < x + 1 from Nat.succ_pos _, ↓reduceIte]
    omega

theorem LamI.of_lift : ∀ (t : Lambda) (k : ℕ), LamI (Lambda.lift 1 k t) → LamI t
  | .var n, _, _ => .var n
  | .app f a, k, h => by
    simp only [Lambda.lift] at h
    cases h with
    | app h1 h2 => exact .app (LamI.of_lift f k h1) (LamI.of_lift a k h2)
  | .lam t, k, h => by
    simp only [Lambda.lift] at h
    cases h with
    | lam h1 hpos =>
      exact .lam (LamI.of_lift t (k + 1) h1) (by rwa [occL_lift_lt _ _ _ (by omega)] at hpos)

theorem LamI.step {t t' : Lambda} (h : LamI t) (hs : Lambda.step t t') : LamI t' ∧
    ∀ y, occL y t ≤ occL y t' := by
  induction hs with
  | beta M N =>
    cases h with
    | app hl hN =>
      cases hl with
      | lam hM hpos =>
        refine ⟨hM.subst N 0 hN, fun y => ?_⟩
        simp only [occL, occL_subst, show ¬ y < 0 from Nat.not_lt_zero _, ↓reduceIte]
        nlinarith
  | app_left _ _ a _ ih =>
    cases h with
    | app h1 h2 =>
      obtain ⟨h1', hle⟩ := ih h1
      exact ⟨.app h1' h2, fun y => by simp only [occL]; have := hle y; omega⟩
  | app_right f _ _ _ ih =>
    cases h with
    | app h1 h2 =>
      obtain ⟨h2', hle⟩ := ih h2
      exact ⟨.app h1 h2', fun y => by simp only [occL]; have := hle y; omega⟩
  | lam _ _ _ ih =>
    cases h with
    | lam h1 hpos =>
      obtain ⟨h1', hle⟩ := ih h1
      exact ⟨.lam h1' (lt_of_lt_of_le hpos (hle 0)), fun y => hle (y + 1)⟩

theorem LamI.etaStep {t t' : Lambda} (h : LamI t) (hs : etaStep t t') : LamI t' ∧
    ∀ y, occL y t ≤ occL y t' := by
  induction hs with
  | eta u =>
    cases h with
    | lam h1 _ =>
      cases h1 with
      | app h2 _ =>
        refine ⟨LamI.of_lift u 0 h2, fun y => ?_⟩
        show occL (y + 1) (Lambda.lift 1 0 u) + occL (y + 1) (.var 0) ≤ occL y u
        rw [occL_lift_ge u 0 y (Nat.zero_le _)]
        simp [occL]
  | app_left a _ ih =>
    cases h with
    | app h1 h2 =>
      obtain ⟨h1', hle⟩ := ih h1
      exact ⟨.app h1' h2, fun y => by simp only [occL]; have := hle y; omega⟩
  | app_right f _ ih =>
    cases h with
    | app h1 h2 =>
      obtain ⟨h2', hle⟩ := ih h2
      exact ⟨.app h1 h2', fun y => by simp only [occL]; have := hle y; omega⟩
  | lam _ ih =>
    cases h with
    | lam h1 hpos =>
      obtain ⟨h1', hle⟩ := ih h1
      exact ⟨.lam h1' (lt_of_lt_of_le hpos (hle 0)), fun y => hle (y + 1)⟩

/-- **In the λI-calculus, βη-reduction never decreases the number of occurrences of a free
variable.** -/
theorem LamI.betaEtaReduces {t t' : Lambda} (h : LamI t) (hr : betaEtaReduces t t') :
    LamI t' ∧ ∀ y, occL y t ≤ occL y t' := by
  induction hr with
  | refl => exact ⟨h, fun _ => le_refl _⟩
  | tail _ hs ih =>
    obtain ⟨h1, hle⟩ := ih
    rcases hs with hs | hs
    · obtain ⟨h2, hle2⟩ := h1.step hs
      exact ⟨h2, fun y => (hle y).trans (hle2 y)⟩
    · obtain ⟨h2, hle2⟩ := h1.etaStep hs
      exact ⟨h2, fun y => (hle y).trans (hle2 y)⟩

theorem occL_zero_step {t t' : Lambda} (hs : Lambda.step t t') :
    ∀ y, occL y t = 0 → occL y t' = 0 := by
  induction hs with
  | beta M N =>
    intro y h
    simp only [occL] at h
    simp only [occL_subst, show ¬ y < 0 from Nat.not_lt_zero _, ↓reduceIte]
    rw [show occL (y + 1) M = 0 by omega, show occL y N = 0 by omega]; simp
  | app_left _ _ a _ ih => intro y h; simp only [occL] at h ⊢; rw [ih y (by omega)]; omega
  | app_right f _ _ _ ih => intro y h; simp only [occL] at h ⊢; rw [ih y (by omega)]; omega
  | lam _ _ _ ih => intro y h; exact ih (y + 1) h

theorem occL_zero_etaStep {t t' : Lambda} (hs : etaStep t t') :
    ∀ y, occL y t = 0 → occL y t' = 0 := by
  induction hs with
  | eta u =>
    intro y h
    simp only [occL, occL_lift_ge u 0 y (Nat.zero_le _)] at h
    omega
  | app_left a _ ih => intro y h; simp only [occL] at h ⊢; rw [ih y (by omega)]; omega
  | app_right f _ ih => intro y h; simp only [occL] at h ⊢; rw [ih y (by omega)]; omega
  | lam _ ih => intro y h; exact ih (y + 1) h

theorem occL_zero_betaEtaReduces {t t' : Lambda} (hr : betaEtaReduces t t') (y : ℕ)
    (h : occL y t = 0) : occL y t' = 0 := by
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    rcases hs with hs | hs
    · exact occL_zero_step hs y ih
    · exact occL_zero_etaStep hs y ih

theorem lamI_toLam : ∀ t : Tm, LamI (toLam t)
  | .B => .lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))) (by simp [occL]))
      (by simp [occL])) (by simp [occL])
  | .M => .lam (.app (.var 0) (.var 0)) (by simp [occL])
  | .I => .lam (.var 0) (by simp [occL])
  | .var n => .var n
  | .app u v => .app (lamI_toLam u) (lamI_toLam v)

theorem occL_toLam_closed {t : Tm} (ht : Tm.IsBMI t) (y : ℕ) : occL y (toLam t) = 0 := by
  induction ht generalizing y with
  | B => simp [toLam, lamB, occL]
  | M => simp [toLam, lamM, occL]
  | I => simp [toLam, lamI, occL]
  | app _ _ ih1 ih2 => simp [toLam, occL, ih1, ih2]

theorem occL_toLam_apps (y : ℕ) : ∀ (f : Tm) (l : List Tm),
    occL y (toLam (apps f l)) = occL y (toLam f) + (l.map fun z => occL y (toLam z)).sum
  | f, [] => by simp [apps]
  | f, z :: l => by
    simp only [apps, occL_toLam_apps y (Tm.app f z) l, toLam, occL, List.map_cons, List.sum_cons]
    ring

theorem spn_betaEtaReduces {z : ℕ} : ∀ {cs cs' : List Lambda},
    List.Forall₂ betaEtaReduces cs cs' → betaEtaReduces (spn z cs) (spn z cs')
  | _, _, .nil => .refl _
  | _, _, .cons h hs => betaEtaReduces_app (spn_betaEtaReduces hs) h

/-- **No polynomial `Bⁿ⁺¹ M ∘ R` is a βη fixed-point combinator.**  Applied to fresh
`z₁ … z_{n+1}`, the fixed-point equation gives `U U =βη x (P x) z⃗` with `U = R x z⃗`.  All terms
are λI-terms, so βη-reduction does not decrease the number of occurrences of `z_{n+1}`: at least two
on the left, exactly one in every reduct of the right. -/
theorem headBM_not_fixedPoint (n : ℕ) (m' : Mono) (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨n + 1, .M⟩ (m' :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨n + 1, .M⟩ (m' :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨n + 1, .M⟩ (m' :: ps) with hP
  set R := polyTm m' ps
  set pre : List Tm := (List.range n).map (fun i => Tm.var (i + 1)) with hpre
  set zs : List Tm := pre ++ [Tm.var (n + 1)] with hzs
  have hzl : zs.length = n + 1 := by simp [hzs, hpre]
  set U := apps (Tm.app R (Tm.var 0)) zs
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) zs) (Tm.app U U) :=
    (comp_action_apps (bpow (n + 1) Tm.M) R (Tm.var 0) zs).trans
      (bpowM_action (n + 1) (Tm.app R (Tm.var 0)) zs hzl)
  have hc : betaEtaConv (toLam (Tm.app U U))
      (toLam (apps (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))) zs)) :=
    (betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY zs)
  obtain ⟨cs', hcs'⟩ := toLam_apps_spn (y := 0) (cs := [toLam (Tm.app P (Tm.var 0))])
    (f := Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))) pre rfl
  have hocc' : occL (n + 1) (spn 0 cs') = 0 := by
    rw [← hcs', occL_toLam_apps]
    simp only [toLam, occL, occL_toLam_closed (t := P) (polyTm_isBMI _ _), hpre, List.map_map]
    rw [List.sum_eq_zero]
    · simp
    · intro a ha
      simp only [List.mem_map, List.mem_range, Function.comp] at ha
      obtain ⟨i, hi, rfl⟩ := ha
      simp [toLam, occL]; omega
  have hR : toLam (apps (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))) zs) =
      lamK 0 (spn 0 (.var (n + 1) :: cs')) := by
    rw [hzs, apps_append]
    simp only [apps, toLam, hcs', lamK, spn]
  rw [hR] at hc
  obtain ⟨w, h1, h2⟩ := hc.common_reduct
  have hU : 1 ≤ occL (n + 1) (toLam U) := by
    simp only [U, occL_toLam_apps, hzs, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, toLam, occL, ↓reduceIte]
    omega
  have hw1 : 2 ≤ occL (n + 1) w := by
    have := ((lamI_toLam (Tm.app U U)).betaEtaReduces h1).2 (n + 1)
    simp only [toLam, occL] at this
    omega
  obtain ⟨j, z, pre', post, cs, hj, hy, hl, rfl, hpre', hpost⟩ := RForm.betaEtaReduces h2
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

/-- **The first monomial of a βη fixed-point polynomial is `M`**: `PolyFiveOne` has a witness
`M ∘ m₂ ∘ … ∘ m_k` with `k ≥ 2` and no monomial of base `I`. -/
theorem polyFiveOne_head_M (h : PolyFiveOne) :
    ∃ (m' : Mono) (ps : List Mono), (∀ q ∈ (⟨0, .M⟩ : Mono) :: m' :: ps, q.base ≠ .I) ∧
      betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m' :: ps)) (Tm.var 0)))
        (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (m' :: ps)) (Tm.var 0)))) := by
  obtain ⟨n, m', ps, hI, hfix⟩ := polyFiveOne_head_baseM h
  cases n with
  | zero => exact ⟨m', ps, hI, hfix⟩
  | succ n => exact (headBM_not_fixedPoint n m' ps hfix).elim

end TLCA4
