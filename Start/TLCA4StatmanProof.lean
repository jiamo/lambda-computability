import Start.TLCA4StatmanInduction

/-!
# TLCA open problem 4 under βη: Statman's Lemma 0.1 and first step (rows
M20-TLCA4-STATMAN-STEP-ONE, M20-TLCA4-POLYNOMIAL; series V, round 3, run 1, parts A2 and A4)

Statman's induction on the number `n` of head steps (`Good n X`), case by case after his proof:
a weak head redex (`I U …`, `M U …`, `B U V W …`) is one or three head β-steps
(`good_of_wstep`); `B`, `M`, `I` are the base cases; `B U` and `B U V` simulate `U (V x) …` by
`U y …` with `y` fresh (`hnIn_split_subst`), and then `V x P₁ … P_m` by `V x y₁ … y_m`
(`good_peel`, one argument at a time, and `good_vpart` under the abstractions).

* **`statmanLemmaGen`** — Lemma 0.1 (`StatmanLemmaGen`);
* **`statmanLemmaOne`** — its one-argument form;
* **`statmanStepOne`** — Statman's first step (`StatmanStepOne`);
* **`problemFiveOne_iff_polyFiveOne`** — Problem 5.1 holds iff it holds for a polynomial.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda Tm

/-- Statman's induction hypothesis at `n` head steps. -/
def Good (n : ℕ) (X : Tm) : Prop :=
  ∀ (x : ℕ) (ys : List ℕ), HNIn n (lapps (toLam X) (.var x :: ys.map Lambda.var)) →
    ∀ (u : Lambda) (w : ℕ), Lambda.reduces (lapps (toLam X) (.var x :: ys.map Lambda.var)) u →
      IsHnf u → hd u = some w → w = x ∧ WN X

theorem lift_toLam {t : Tm} (h : IsBMI t) : Lambda.lift 1 0 (toLam t) = toLam t :=
  lift_toLam_of_isBMI h 1 0

/-- A weak head redex: `c` head steps lead to the contractum. -/
theorem good_of_wstep {n c : ℕ} {X X' : Tm} (hs : WStep X X') (hX' : IsBMI X')
    (hst : ∀ as, hsteps c (lapps (toLam X) as) (lapps (toLam X') as)) (hc : 1 ≤ c)
    (ih : ∀ m < n, ∀ Y, IsBMI Y → Good m Y) : Good n X := by
  intro x ys hT u w hr hu hw
  obtain ⟨hcn, hT'⟩ := hnIn_hsteps hT (hst _)
  obtain ⟨u', hr', hu'⟩ := exists_hnf_of_hnIn _ hT'
  have e : hd u = hd u' :=
    hd_unique hr hu (Lambda.reduces_trans (hsteps_reduces (hst _)) hr') hu'
  obtain ⟨h1, h2⟩ := ih (n - c) (by omega) X' hX' x ys hT' u' w hr' hu' (e ▸ hw)
  exact ⟨h1, wn_of_wstep hs h2⟩

/-- The peeling of arguments: `V x A₁ … A_m y⃗` is simulated by `V x' y⃗'` with variables. -/
theorem good_peel {V : Tm} (hV : IsBMI V) : ∀ (A : List Lambda) (s : ℕ), (∀ m ≤ s, Good m V) →
    ∀ (B : List ℕ) (x : ℕ), HNIn s (lapps (toLam V) (.var x :: (A ++ B.map Lambda.var))) →
    ∀ (u : Lambda) (w : ℕ),
      Lambda.reduces (lapps (toLam V) (.var x :: (A ++ B.map Lambda.var))) u →
      IsHnf u → hd u = some w → w = x ∧ WN V := by
  suffices H : ∀ (k : ℕ) (A : List Lambda), A.length = k → ∀ (s : ℕ), (∀ m ≤ s, Good m V) →
      ∀ (B : List ℕ) (x : ℕ), HNIn s (lapps (toLam V) (.var x :: (A ++ B.map Lambda.var))) →
      ∀ (u : Lambda) (w : ℕ),
        Lambda.reduces (lapps (toLam V) (.var x :: (A ++ B.map Lambda.var))) u →
        IsHnf u → hd u = some w → w = x ∧ WN V from fun A => H _ A rfl
  intro k
  induction k with
  | zero =>
      intro A hA s ih B x hT u w hr hu hw
      rw [List.length_eq_zero_iff] at hA
      subst hA
      exact ih s le_rfl x B hT u w hr hu hw
  | succ k ihA =>
      intro A hA s ih B x hT u w hr hu hw
      rcases List.eq_nil_or_concat A with rfl | ⟨A', a, rfl⟩
      · simp at hA
      simp only [List.concat_eq_append] at hA hT hr
      have hlen : (A'.map (Lambda.lift 1 0)).length = k := by simp at hA ⊢; omega
      set T₁ := lapps (toLam V) (.var (x + 1) ::
        (A'.map (Lambda.lift 1 0) ++ (0 :: B.map (· + 1)).map Lambda.var)) with hT₁
      have eT : Lambda.subst a 0 T₁ =
          lapps (toLam V) (.var x :: (A' ++ [a] ++ B.map Lambda.var)) := by
        rw [hT₁, subst_lapps, subst_toLam_of_isBMI hV]
        simp [Lambda.subst, Function.comp_def, Lambda.subst_lift]
      rw [← eT] at hT hr
      obtain ⟨h, r, hrs, hsh, hh, _⟩ := hnIn_split_subst s hT
      rw [hT₁] at hsh
      have hred : Lambda.reduces (Lambda.subst a 0 T₁) (Lambda.subst a 0 h) :=
        hsteps_reduces (hsteps_subst hsh a 0)
      obtain ⟨hn1, hn2⟩ := hnf_subst_ne hh a 0
      rcases e : hd h with _ | w'
      · obtain ⟨h1, h2⟩ := hn1 e
        have := hd_unique hr hu hred h1
        rw [hw, h2] at this; cases this
      · obtain ⟨hw', hWN⟩ := ihA _ hlen r (fun m hm => ih m (le_trans hm hrs)) (0 :: B.map (· + 1))
          (x + 1) (hnIn_of_hsteps hsh hh) h w' (hsteps_reduces hsh) hh e
        subst hw'
        obtain ⟨h1, h2⟩ := hn2 (x + 1) e (by omega)
        have := hd_unique hr hu hred h1
        rw [hw, h2] at this
        simp only [Option.some.injEq] at this
        exact ⟨by split_ifs at this <;> omega, hWN⟩

/-- The `V`-part of the case `B U V`, under the abstractions of the head normal form of `U y …`. -/
theorem good_vpart {V : Tm} (hV : IsBMI V) : ∀ {h : Lambda}, IsHnf h → ∀ (z x s : ℕ),
    hd h = some z → (∀ m ≤ s, Good m V) →
    HNIn s (Lambda.subst (.app (toLam V) (.var x)) z h) →
    ∀ (u : Lambda) (w : ℕ), Lambda.reduces (Lambda.subst (.app (toLam V) (.var x)) z h) u →
      IsHnf u → hd u = some w → w = x ∧ WN V
  | _, .lam (t := t) ht, z, x, s, hz, ih, hT, u, w, hr, hu, hw => by
      have hz' := hd_lam_some hz
      have eQ : Lambda.lift 1 0 (.app (toLam V) (.var x)) = .app (toLam V) (.var (x + 1)) := by
        simp [Lambda.lift, lift_toLam hV]
      simp only [Lambda.subst, eQ] at hT hr
      obtain ⟨u', rfl, hr'⟩ := reduces_lam_shape hr
      obtain ⟨h1, h2⟩ := good_vpart hV ht (z + 1) (x + 1) s hz' ih (hnIn_lam_inv hT) u' (w + 1)
        hr' hu.of_lam (hd_lam_some hw)
      exact ⟨by omega, h2⟩
  | _, .neutral hn, z, x, s, hz, ih, hT, u, w, hr, hu, hw => by
      obtain ⟨w0, as, rfl⟩ := neutral_decomp hn
      have hw0 : w0 = z := by
        have := (neutral_lapps as (Neutral.var w0)).2
        rw [hz] at this; simp [hd] at this; omega
      subst hw0
      have e : Lambda.subst (.app (toLam V) (.var x)) w0 (lapps (.var w0) as) =
          lapps (toLam V) (.var x :: (as.map (Lambda.subst (.app (toLam V) (.var x)) w0) ++
            ([] : List ℕ).map Lambda.var)) := by
        rw [subst_lapps]; simp [Lambda.subst, lapps]
      rw [e] at hT hr
      exact good_peel hV _ s ih [] x hT u w hr hu hw

/-- **Statman's induction.** -/
theorem good_all : ∀ (n : ℕ) (X : Tm), IsBMI X → Good n X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X hX
  obtain ⟨c, zs, rfl, hc, hz⟩ := isBMI_spine hX
  rcases hc with rfl | rfl | rfl
  · -- `B`
    match zs, hz with
    | [], _ =>
        intro x ys _ u w hr hu hw
        obtain ⟨h1, h2⟩ := statmanGen_B x ys u hr hu
        rw [hw] at h1; cases h1; exact ⟨rfl, h2⟩
    | [U], hz =>
        have hU : IsBMI U := hz U (by simp)
        intro x ys hT u w hr hu hw
        match ys with
        | [] =>
            have hst := hsteps_B2 (toLam U) (.var x)
            simp only [lift_toLam hU] at hst
            have eT : lapps (toLam (apps .B [U])) (.var x :: ([] : List ℕ).map Lambda.var) =
                .app (.app lamB (toLam U)) (.var x) := rfl
            rw [eT] at hT hr
            obtain ⟨hcn, hT2⟩ := hnIn_hsteps hT hst
            have eP : Lambda.subst (.app (.var (x + 1)) (.var 0)) 0 (.app (toLam U) (.var 0)) =
                .app (toLam U) (.app (Lambda.lift 1 0 (.var x)) (.var 0)) := by
              simp [Lambda.subst, subst_toLam_of_isBMI hU, Lambda.lift]
            rw [← eP] at hT2 hst
            obtain ⟨h, r, hrs, hsh, hh, _⟩ := hnIn_split_subst _ (hnIn_lam_inv hT2)
            have hred := Lambda.reduces_trans (hsteps_reduces hst)
              (Lambda.reduces_lam (hsteps_reduces (hsteps_subst hsh (.app (.var (x + 1)) (.var 0)) 0)))
            obtain ⟨hn1, _⟩ := hnf_subst_ne hh (.app (.var (x + 1)) (.var 0)) 0
            rcases e : hd h with _ | w'
            · obtain ⟨h1, h2⟩ := hn1 e
              have := hd_unique hr hu hred (.lam h1)
              rw [hw, hd_lam_none h2] at this; cases this
            · obtain ⟨hw', hWN⟩ := ih r (by omega) U hU 0 [] (hnIn_of_hsteps hsh hh) h w'
                (hsteps_reduces hsh) hh e
              subst hw'
              obtain ⟨h1, h2⟩ := hnf_subst_head hh (Neutral.app _ (Neutral.var (x + 1))) rfl e
              have := hd_unique hr hu hred (.lam h1)
              rw [hw, hd_lam_succ h2] at this
              cases this
              exact ⟨rfl, wn_BU hWN⟩
        | y :: rest =>
            have hst := hsteps_B3 (toLam U) (.var x) (.var y) (rest.map Lambda.var)
            have eT : lapps (toLam (apps .B [U])) (.var x :: (y :: rest).map Lambda.var) =
                lapps (.app (.app (.app lamB (toLam U)) (.var x)) (.var y)) (rest.map Lambda.var) :=
              rfl
            rw [eT] at hT hr
            obtain ⟨hcn, hT2⟩ := hnIn_hsteps hT hst
            have eP : Lambda.subst (.app (.var x) (.var y)) 0
                (lapps (toLam U) (.var 0 :: (rest.map (· + 1)).map Lambda.var)) =
                lapps (.app (toLam U) (.app (.var x) (.var y))) (rest.map Lambda.var) := by
              rw [subst_lapps, subst_toLam_of_isBMI hU]
              simp only [List.map_cons, List.map_map]
              simp only [lapps, Lambda.subst, if_true]
              congr 1
            rw [← eP] at hT2 hst
            obtain ⟨h, r, hrs, hsh, hh, _⟩ := hnIn_split_subst _ hT2
            have hred := Lambda.reduces_trans (hsteps_reduces hst)
              (hsteps_reduces (hsteps_subst hsh (.app (.var x) (.var y)) 0))
            obtain ⟨hn1, _⟩ := hnf_subst_ne hh (.app (.var x) (.var y)) 0
            rcases e : hd h with _ | w'
            · obtain ⟨h1, h2⟩ := hn1 e
              have := hd_unique hr hu hred h1
              rw [hw, h2] at this; cases this
            · obtain ⟨hw', hWN⟩ := ih r (by omega) U hU 0 (rest.map (· + 1))
                (hnIn_of_hsteps hsh hh) h w' (hsteps_reduces hsh) hh e
              subst hw'
              obtain ⟨h1, h2⟩ := hnf_subst_head hh (Neutral.app _ (Neutral.var x)) rfl e
              have := hd_unique hr hu hred h1
              rw [hw, h2] at this
              cases this
              exact ⟨rfl, wn_BU hWN⟩
    | [U, V], hz =>
        have hU : IsBMI U := hz U (by simp)
        have hV : IsBMI V := hz V (by simp)
        intro x ys hT u w hr hu hw
        have hst := hsteps_B3 (toLam U) (toLam V) (.var x) (ys.map Lambda.var)
        have eT : lapps (toLam (apps .B [U, V])) (.var x :: ys.map Lambda.var) =
            lapps (.app (.app (.app lamB (toLam U)) (toLam V)) (.var x)) (ys.map Lambda.var) :=
          rfl
        rw [eT] at hT hr
        obtain ⟨hcn, hT2⟩ := hnIn_hsteps hT hst
        have eP : Lambda.subst (.app (toLam V) (.var x)) 0
            (lapps (toLam U) (.var 0 :: (ys.map (· + 1)).map Lambda.var)) =
            lapps (.app (toLam U) (.app (toLam V) (.var x))) (ys.map Lambda.var) := by
          rw [subst_lapps, subst_toLam_of_isBMI hU]
          simp only [List.map_cons, List.map_map]
          simp only [lapps, Lambda.subst, if_true]
          congr 1
        rw [← eP] at hT2 hst
        obtain ⟨h, r, hrs, hsh, hh, hT3⟩ := hnIn_split_subst _ hT2
        have hred := Lambda.reduces_trans (hsteps_reduces hst)
          (hsteps_reduces (hsteps_subst hsh (.app (toLam V) (.var x)) 0))
        obtain ⟨hn1, _⟩ := hnf_subst_ne hh (.app (toLam V) (.var x)) 0
        rcases e : hd h with _ | w'
        · obtain ⟨h1, h2⟩ := hn1 e
          have := hd_unique hr hu hred h1
          rw [hw, h2] at this; cases this
        · obtain ⟨hw', hWNU⟩ := ih r (by omega) U hU 0 (ys.map (· + 1))
            (hnIn_of_hsteps hsh hh) h w' (hsteps_reduces hsh) hh e
          subst hw'
          obtain ⟨u'', hr'', hu''⟩ := exists_hnf_of_hnIn _ hT3
          have e2 := hd_unique hr hu (Lambda.reduces_trans hred hr'') hu''
          rw [hw] at e2
          obtain ⟨h1, hWNV⟩ := good_vpart hV hh 0 x _ e
            (fun m hm => ih m (by omega) V hV) hT3 u'' w hr'' hu'' e2.symm
          exact ⟨h1, wn_BUV hWNU hWNV⟩
    | U :: V :: W :: rest, hz =>
        have hU : IsBMI U := hz U (by simp)
        have hV : IsBMI V := hz V (by simp)
        have hW : IsBMI W := hz W (by simp)
        have hR : ∀ r ∈ rest, IsBMI r := fun r hr => hz r (by simp [hr])
        refine good_of_wstep (X' := apps (.app U (.app V W)) rest)
          (wstep_apps rest (WStep.b U V W)) ?_ (c := 3) ?_ (by omega) ih
        · exact isBMI_wstep (wstep_apps rest (WStep.b U V W)) hX
        · intro as
          have := hsteps_B3 (toLam U) (toLam V) (toLam W) (rest.map toLam ++ as)
          simpa [toLam_apps, lapps_append, toLam, lapps] using this
  · -- `M`
    match zs, hz with
    | [], _ =>
        intro x ys _ u w hr hu hw
        obtain ⟨h1, h2⟩ := statmanGen_M x ys u hr hu
        rw [hw] at h1; cases h1; exact ⟨rfl, h2⟩
    | U :: rest, hz =>
        have hU : IsBMI U := hz U (by simp)
        have hR : ∀ r ∈ rest, IsBMI r := fun r hr => hz r (by simp [hr])
        refine good_of_wstep (X' := apps (.app U U) rest)
          (wstep_apps rest (WStep.m U)) ?_ (c := 1) ?_ le_rfl ih
        · exact isBMI_wstep (wstep_apps rest (WStep.m U)) hX
        · intro as
          have := hsteps_one (.weak (wstep_lapps (rest.map toLam ++ as) (wstep_M (toLam U))))
          simpa [toLam_apps, lapps_append, toLam, lapps] using this
  · -- `I`
    match zs, hz with
    | [], _ =>
        intro x ys _ u w hr hu hw
        obtain ⟨h1, h2⟩ := statmanGen_I x ys u hr hu
        rw [hw] at h1; cases h1; exact ⟨rfl, h2⟩
    | U :: rest, hz =>
        have hU : IsBMI U := hz U (by simp)
        have hR : ∀ r ∈ rest, IsBMI r := fun r hr => hz r (by simp [hr])
        refine good_of_wstep (X' := apps U rest)
          (wstep_apps rest (WStep.i U)) ?_ (c := 1) ?_ le_rfl ih
        · exact isBMI_wstep (wstep_apps rest (WStep.i U)) hX
        · intro as
          have := hsteps_one (.weak (wstep_lapps (rest.map toLam ++ as) (wstep_I (toLam U))))
          simpa [toLam_apps, lapps_append, toLam, lapps] using this

/-- **Statman's Lemma 0.1.** -/
theorem statmanLemmaGen : StatmanLemmaGen := by
  intro X hX x ys u hr hu hhead
  obtain ⟨n, hn⟩ := hasHeadEval_of_hasHnf ⟨u, hr, hu⟩
  obtain ⟨w, hw⟩ : ∃ w, hd u = some w := by
    rcases hhead with h | ⟨y, _, h⟩ <;> exact ⟨_, h⟩
  obtain ⟨h1, h2⟩ := good_all n X hX x ys hn u w hr hu hw
  exact ⟨h1 ▸ hw, h2⟩

/-- **Statman's Lemma 0.1, one argument.** -/
theorem statmanLemmaOne : StatmanLemmaOne := statmanLemmaOne_of_gen statmanLemmaGen

/-- **Statman's first step**: a closed `B`,`M`,`I`-term that is a βη fixed-point combinator is
βη-equal to a polynomial. -/
theorem statmanStepOne : StatmanStepOne := statmanStepOne_of_lemmaOne statmanLemmaOne

/-- **Problem 5.1 holds iff it holds for some polynomial.** -/
theorem problemFiveOne_iff_polyFiveOne : ProblemFiveOne ↔ PolyFiveOne :=
  problemFiveOne_iff_poly statmanStepOne

end TLCA4
