import Start.TLCA4StatmanLemma

/-!
# TLCA open problem 4 under βη: Statman's Lemma 0.1 (row M20-TLCA4-STATMAN-STEP-ONE;
series V, round 3, run 1, part A2)

Statman's induction on the number of head steps, in the form `Good n X`: for every variable `x` and
list of variables `ys`, if `toLam (X x ys)` reaches a head normal form in at most `n` head steps,
then every head normal form of it whose head is a free variable has head `x`, and `X` weakly
reduces to a weakly normal term.

The fresh variable of Statman's simulation is de Bruijn index `0` of a lifted term:
`subst Q 0 (… lift 1 0 t … var 0 …) = … t … Q …`, so no free-variable bookkeeping is needed.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda Tm

/-! ## Substitution into head normal forms -/

theorem hd_lam_some {t : Lambda} {w : ℕ} (h : hd (.lam t) = some w) : hd t = some (w + 1) := by
  simp only [hd] at h
  rcases e : hd t with _ | v
  · rw [e] at h; cases h
  · rw [e] at h
    simp only [Option.bind_some] at h
    split_ifs at h with h0
    cases h; congr 1; omega

theorem hd_lam_none {t : Lambda} (h : hd t = none) : hd (.lam t) = none := by
  simp [hd, h]

theorem hd_lam_succ {t : Lambda} {w : ℕ} (h : hd t = some (w + 1)) : hd (.lam t) = some w := by
  simp [hd, h]

theorem neutral_subst_ne {h : Lambda} (hn : Neutral h) {z w : ℕ} (hh : hd h = some w) (hw : w ≠ z)
    (Q : Lambda) : Neutral (Lambda.subst Q z h) ∧
      hd (Lambda.subst Q z h) = some (if w > z then w - 1 else w) := by
  induction hn with
  | var n =>
      simp only [hd, Option.some.injEq] at hh
      subst hh
      simp only [Lambda.subst, hw, ite_false]
      split_ifs <;> exact ⟨Neutral.var _, rfl⟩
  | app N _ ih =>
      obtain ⟨h1, h2⟩ := ih hh
      exact ⟨Neutral.app _ h1, h2⟩

theorem neutral_subst_none {h : Lambda} (hn : Neutral h) (hh : hd h = none) : False := by
  induction hn with
  | var n => simp [hd] at hh
  | app N _ ih => exact ih hh

/-- Substituting for a variable that is not the head keeps a head normal form. -/
theorem hnf_subst_ne : ∀ {h : Lambda}, IsHnf h → ∀ (Q : Lambda) (z : ℕ),
    (hd h = none → IsHnf (Lambda.subst Q z h) ∧ hd (Lambda.subst Q z h) = none) ∧
    (∀ w, hd h = some w → w ≠ z →
      IsHnf (Lambda.subst Q z h) ∧ hd (Lambda.subst Q z h) = some (if w > z then w - 1 else w))
  | _, .neutral hn, Q, z => by
      refine ⟨fun hh => (neutral_subst_none hn hh).elim, fun w hh hw => ?_⟩
      obtain ⟨h1, h2⟩ := neutral_subst_ne hn hh hw Q
      exact ⟨.neutral h1, h2⟩
  | _, .lam (t := t) ht, Q, z => by
      obtain ⟨ih1, ih2⟩ := hnf_subst_ne ht (Lambda.lift 1 0 Q) (z + 1)
      simp only [Lambda.subst]
      refine ⟨fun hh => ?_, fun w hh hw => ?_⟩
      · rcases e : hd t with _ | v
        · obtain ⟨h1, h2⟩ := ih1 e
          exact ⟨.lam h1, hd_lam_none h2⟩
        · have hv0 : v = 0 := by
            simp only [hd, e, Option.bind_some] at hh
            split_ifs at hh with h0
            exact h0
          subst hv0
          obtain ⟨h1, h2⟩ := ih2 0 e (by omega)
          refine ⟨.lam h1, ?_⟩
          simp only [hd, h2]
          simp
      · have e := hd_lam_some hh
        obtain ⟨h1, h2⟩ := ih2 (w + 1) e (by omega)
        refine ⟨.lam h1, ?_⟩
        apply hd_lam_succ
        rw [h2]
        congr 1
        split_ifs <;> omega

theorem neutral_subst_head {h : Lambda} (hn : Neutral h) {Q : Lambda} {z q : ℕ} (hQ : Neutral Q)
    (hq : hd Q = some q) (hh : hd h = some z) :
    Neutral (Lambda.subst Q z h) ∧ hd (Lambda.subst Q z h) = some q := by
  induction hn with
  | var n =>
      simp only [hd, Option.some.injEq] at hh
      subst hh
      simp only [Lambda.subst, ite_true]
      exact ⟨hQ, hq⟩
  | app N _ ih =>
      obtain ⟨h1, h2⟩ := ih hh
      exact ⟨Neutral.app _ h1, h2⟩

/-- Substituting a neutral term for the head variable keeps a head normal form, with the head of
the substituted term. -/
theorem hnf_subst_head : ∀ {h : Lambda}, IsHnf h → ∀ {Q : Lambda} {z q : ℕ}, Neutral Q →
    hd Q = some q → hd h = some z → IsHnf (Lambda.subst Q z h) ∧
      hd (Lambda.subst Q z h) = some q
  | _, .neutral hn, Q, z, q, hQ, hq, hh => by
      obtain ⟨h1, h2⟩ := neutral_subst_head hn hQ hq hh
      exact ⟨.neutral h1, h2⟩
  | _, .lam ht, Q, z, q, hQ, hq, hh => by
      have e := hd_lam_some hh
      have hq' : hd (Lambda.lift 1 0 Q) = some (q + 1) := by simp [hd_lift, hq]
      obtain ⟨h1, h2⟩ := hnf_subst_head ht (hQ.lift 1 0) hq' e
      exact ⟨.lam h1, hd_lam_succ h2⟩

/-! ## Counted head reduction, continued -/

theorem hnIn_lam_inv : ∀ {n : ℕ} {t : Lambda}, HNIn n (.lam t) → HNIn n t
  | 0, _, h => h.of_lam
  | _ + 1, _, .inl h => .inl h.of_lam
  | _ + 1, _, .inr ⟨_, hs, hn⟩ => by
      cases hs with
      | weak hw => cases hw
      | lam hs' => exact .inr ⟨_, hs', hnIn_lam_inv hn⟩

theorem hnIn_hsteps : ∀ {c n : ℕ} {t t' : Lambda}, HNIn n t → hsteps c t t' →
    c ≤ n ∧ HNIn (n - c) t'
  | 0, n, _, _, h, e => by cases e; exact ⟨Nat.zero_le _, h⟩
  | c + 1, 0, _, _, h, ⟨_, hs, _⟩ => absurd hs (not_hstep_of_isHnf h _)
  | c + 1, n + 1, _, _, h, ⟨_, hs, hr⟩ => by
      obtain ⟨h1, h2⟩ := hnIn_hsteps (hnIn_hstep h hs) hr
      refine ⟨by omega, ?_⟩
      have e : n + 1 - (c + 1) = n - c := by omega
      rw [e]; exact h2

theorem hsteps_reduces : ∀ {c : ℕ} {t t' : Lambda}, hsteps c t t' → Lambda.reduces t t'
  | 0, _, _, e => by cases e; exact .refl _
  | _ + 1, _, _, ⟨_, hs, hr⟩ => Lambda.reduces.step _ _ _ (hstep_imp_step hs) (hsteps_reduces hr)

theorem wstep_lapps : ∀ {f f' : Lambda} (as : List Lambda), wstep f f' →
    wstep (lapps f as) (lapps f' as)
  | _, _, [], h => h
  | _, _, a :: as, h => wstep_lapps as (wstep.app a h)

theorem hsteps_one {t t' : Lambda} (h : hstep t t') : hsteps 1 t t' := ⟨t', h, rfl⟩

theorem hsteps_three {t₀ t₁ t₂ t₃ : Lambda} (h₁ : hstep t₀ t₁) (h₂ : hstep t₁ t₂)
    (h₃ : hstep t₂ t₃) : hsteps 3 t₀ t₃ := ⟨t₁, h₁, t₂, h₂, t₃, h₃, rfl⟩

theorem hsteps_two {t₀ t₁ t₂ : Lambda} (h₁ : hstep t₀ t₁) (h₂ : hstep t₁ t₂) :
    hsteps 2 t₀ t₂ := ⟨t₁, h₁, t₂, h₂, rfl⟩

/-! ## The translation -/

theorem subst_toLam_of_isBMI {t : Tm} (h : IsBMI t) (Q : Lambda) (z : ℕ) :
    Lambda.subst Q z (toLam t) = toLam t := by
  induction h generalizing Q z with
  | B => simp only [toLam, lamB, Lambda.subst]; split_ifs <;> first | rfl | (exfalso; omega)
  | M => simp only [toLam, lamM, Lambda.subst]; split_ifs <;> first | rfl | (exfalso; omega)
  | I => simp only [toLam, lamI, Lambda.subst]; split_ifs <;> first | rfl | (exfalso; omega)
  | app _ _ ihu ihv => simp only [toLam, Lambda.subst, ihu, ihv]

theorem subst_lapps (Q : Lambda) (z : ℕ) : ∀ (f : Lambda) (as : List Lambda),
    Lambda.subst Q z (lapps f as) = lapps (Lambda.subst Q z f) (as.map (Lambda.subst Q z))
  | _, [] => rfl
  | f, a :: as => subst_lapps Q z (.app f a) as

theorem lift_lapps (n k : ℕ) : ∀ (f : Lambda) (as : List Lambda),
    Lambda.lift n k (lapps f as) = lapps (Lambda.lift n k f) (as.map (Lambda.lift n k))
  | _, [] => rfl
  | f, a :: as => lift_lapps n k (.app f a) as

theorem lapps_append : ∀ (f : Lambda) (as bs : List Lambda),
    lapps f (as ++ bs) = lapps (lapps f as) bs
  | _, [], _ => rfl
  | f, a :: as, bs => lapps_append (.app f a) as bs

theorem toLam_apps : ∀ (f : Tm) (zs : List Tm),
    toLam (apps f zs) = lapps (toLam f) (zs.map toLam)
  | _, [] => rfl
  | f, z :: zs => toLam_apps (.app f z) zs

theorem wstep_apps : ∀ {f f' : Tm} (zs : List Tm), WStep f f' → WStep (apps f zs) (apps f' zs)
  | _, _, [], h => h
  | _, _, z :: zs, h => wstep_apps zs (WStep.appL z h)

theorem neutral_decomp : ∀ {h : Lambda}, Neutral h → ∃ w as, h = lapps (.var w) as
  | _, .var w => ⟨w, [], rfl⟩
  | _, .app N hn => by
      obtain ⟨w, as, e⟩ := neutral_decomp hn
      exact ⟨w, as ++ [N], by rw [e, lapps_append]; rfl⟩

/-- The spine of a closed `B`,`M`,`I`-term. -/
theorem isBMI_spine {X : Tm} (h : IsBMI X) :
    ∃ c zs, X = apps c zs ∧ (c = .B ∨ c = .M ∨ c = .I) ∧ ∀ z ∈ zs, IsBMI z := by
  induction h with
  | B => exact ⟨.B, [], rfl, .inl rfl, by simp⟩
  | M => exact ⟨.M, [], rfl, .inr (.inl rfl), by simp⟩
  | I => exact ⟨.I, [], rfl, .inr (.inr rfl), by simp⟩
  | @app u v _ hv ihu _ =>
      obtain ⟨c, zs, e, hc, hz⟩ := ihu
      refine ⟨c, zs ++ [v], by rw [apps_append, e]; rfl, hc, ?_⟩
      intro z hz'
      rcases List.mem_append.1 hz' with h' | h'
      · exact hz z h'
      · simp at h'; subst h'; exact hv

/-! ## The `B`, `M`, `I` head steps -/

theorem wstep_I (U : Lambda) : wstep (.app lamI U) U := by
  have := wstep.beta (.var 0) U
  simpa [Lambda.subst, lamI] using this

theorem wstep_M (U : Lambda) : wstep (.app lamM U) (.app U U) := by
  have := wstep.beta (.app (.var 0) (.var 0)) U
  simpa [Lambda.subst, lamM] using this

theorem wstep_B1 (u : Lambda) : wstep (.app lamB u)
    (.lam (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0))))) := by
  have := wstep.beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) u
  simp only [Lambda.subst, lift_lift_zero_one] at this
  simpa [lamB] using this

theorem wstep_B2 (u v : Lambda) : wstep
    (.app (.lam (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0))))) v)
    (.lam (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0)))) := by
  have := wstep.beta (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0)))) v
  simpa [Lambda.subst, Lambda.subst_lift] using this

theorem wstep_B3 (u v w : Lambda) : wstep
    (.app (.lam (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0)))) w)
    (.app u (.app v w)) := by
  have := wstep.beta (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0))) w
  simpa [Lambda.subst, Lambda.subst_lift] using this

theorem hsteps_B3 (u v w : Lambda) (as : List Lambda) :
    hsteps 3 (lapps (.app (.app (.app lamB u) v) w) as) (lapps (.app u (.app v w)) as) :=
  hsteps_three (.weak (wstep_lapps as (wstep.app w (wstep.app v (wstep_B1 u)))))
    (.weak (wstep_lapps as (wstep.app w (wstep_B2 u v))))
    (.weak (wstep_lapps as (wstep_B3 u v w)))

theorem hsteps_B2 (u v : Lambda) :
    hsteps 2 (.app (.app lamB u) v)
      (.lam (.app (Lambda.lift 1 0 u) (.app (Lambda.lift 1 0 v) (.var 0)))) :=
  hsteps_two (.weak (wstep.app v (wstep_B1 u))) (.weak (wstep_B2 u v))

end TLCA4
