import Start.TLCA4FixBridge

/-!
# TLCA open problem 4 under βη: towards Statman's Lemma 0.1 (row M20-TLCA4-STATMAN-STEP-ONE;
series V, round 3, run 1, part A2)

Statman's Lemma 0.1, in the form the induction needs (`StatmanLemmaGen`): for a closed
`B`,`M`,`I`-term `X` and variables `x, y₁, …, y_m`, if `toLam (X x y₁ … y_m)` has a head normal form
whose free head is among `x, y₁, …, y_m`, then the head is `x` and `X` weakly reduces to a weakly
normal term.  This module proves the infrastructure of Statman's induction on the number of head
steps and the base cases; the induction itself is in `Start/TLCA4StatmanProof.lean`
(`statmanLemmaGen`).

* `hd_unique` — all head normal forms of a term have the same free head variable;
* `hsteps`, `hnIn_of_hsteps`, `hnIn_hstep` — counted head reduction;
* **`hnIn_split_subst`** — the counted simulation: if `subst Q y P` reaches a head normal form in
  `n` head steps, then `P` reaches a head normal form `h` in `r ≤ n` steps and `subst Q y h`
  reaches it in `n - r` further steps (`hasHeadEval_of_subst`, refined to keep the step count);
* `hnIn_of_subst` — `HNIn n (subst Q y P) → HNIn n P`;
* `lapps`, `StatmanLemmaGen`; `statmanLemmaOne_of_gen` (one argument);
* `statmanGen_I`, `statmanGen_M`, `statmanGen_B` — the cases `X = I, M, B` (Statman's Case 1);
* `wn_of_wstep`, `wn_BUV`, `wn_BU` — weak normalizability through a weak head step, and of `B U V`
  and `B U` from that of `U` and `V`.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda Tm

/-- All head normal forms of a term have the same free head variable. -/
theorem hd_unique {t u v : Lambda} (hu : Lambda.reduces t u) (hu' : IsHnf u)
    (hv : Lambda.reduces t v) (hv' : IsHnf v) : hd u = hd v := by
  obtain ⟨w, h1, h2⟩ := betaEta_church_rosser (betaEtaReduces.of_reduces hu)
    (betaEtaReduces.of_reduces hv)
  exact (hnf_betaEtaReduces hu' h1).2.symm.trans (hnf_betaEtaReduces hv' h2).2

/-! ## Counted head reduction -/

/-- Exactly `r` head steps. -/
def hsteps : ℕ → Lambda → Lambda → Prop
  | 0, t, u => t = u
  | r + 1, t, u => ∃ t', hstep t t' ∧ hsteps r t' u

theorem hnIn_of_hsteps : ∀ {r : ℕ} {t h : Lambda}, hsteps r t h → IsHnf h → HNIn r t
  | 0, _, _, e, hh => by cases e; exact hh
  | _ + 1, _, _, ⟨_, hs, hr⟩, hh => Or.inr ⟨_, hs, hnIn_of_hsteps hr hh⟩

theorem hnIn_hstep {n : ℕ} {t t' : Lambda} (h : HNIn (n + 1) t) (hs : hstep t t') : HNIn n t' := by
  rcases h with h | ⟨w, hw, hn⟩
  · exact absurd hs (not_hstep_of_isHnf h _)
  · rwa [hstep_deterministic hs hw]

theorem hsteps_subst : ∀ {r : ℕ} {P h : Lambda}, hsteps r P h → ∀ (Q : Lambda) (y : ℕ),
    hsteps r (Lambda.subst Q y P) (Lambda.subst Q y h)
  | 0, _, _, e, _, _ => by cases e; rfl
  | _ + 1, _, _, ⟨_, hs, hr⟩, Q, y => ⟨_, hstep_subst hs Q y, hsteps_subst hr Q y⟩

/-- **Counted simulation through a substitution.** -/
theorem hnIn_split_subst : ∀ (n : ℕ) {P Q : Lambda} {y : ℕ}, HNIn n (Lambda.subst Q y P) →
    ∃ h r, r ≤ n ∧ hsteps r P h ∧ IsHnf h ∧ HNIn (n - r) (Lambda.subst Q y h) := by
  intro n
  induction n with
  | zero =>
      intro P Q y h
      by_cases hP : IsHnf P
      · exact ⟨P, 0, le_rfl, rfl, hP, h⟩
      obtain ⟨P', hP'⟩ := exists_hstep_of_not_isHnf hP
      exact absurd (hstep_subst hP' Q y) (not_hstep_of_isHnf h _)
  | succ n ih =>
      intro P Q y h
      by_cases hP : IsHnf P
      · exact ⟨P, 0, Nat.zero_le _, rfl, hP, h⟩
      obtain ⟨P', hP'⟩ := exists_hstep_of_not_isHnf hP
      have h' := hnIn_hstep h (hstep_subst hP' Q y)
      obtain ⟨hh, r, hr, hs, hhh, hn⟩ := ih h'
      refine ⟨hh, r + 1, by omega, ⟨P', hP', hs⟩, hhh, ?_⟩
      have e : n + 1 - (r + 1) = n - r := by omega
      rw [e]; exact hn

theorem hnIn_of_subst {n : ℕ} {P Q : Lambda} {y : ℕ} (h : HNIn n (Lambda.subst Q y P)) :
    HNIn n P := by
  obtain ⟨hh, r, hr, hs, hhh, _⟩ := hnIn_split_subst n h
  exact hnIn_mono hr (hnIn_of_hsteps hs hhh)

/-! ## Applications to lists of arguments -/

/-- `f a₁ … a_k`. -/
def lapps (f : Lambda) : List Lambda → Lambda
  | [] => f
  | a :: as => lapps (.app f a) as

theorem neutral_lapps : ∀ {f : Lambda} (as : List Lambda), Neutral f →
    Neutral (lapps f as) ∧ hd (lapps f as) = hd f
  | _, [], h => ⟨h, rfl⟩
  | f, a :: as, h => by
      obtain ⟨h1, h2⟩ := neutral_lapps as (Neutral.app a h)
      exact ⟨h1, h2.trans rfl⟩

theorem reduces_lapps : ∀ {f f' : Lambda} (as : List Lambda), Lambda.reduces f f' →
    Lambda.reduces (lapps f as) (lapps f' as)
  | _, _, [], h => h
  | _, _, _ :: as, h => reduces_lapps as (Lambda.reduces_app_left h)

/-- Statman's Lemma 0.1, in the form its induction needs. -/
def StatmanLemmaGen : Prop :=
  ∀ X : Tm, IsBMI X → ∀ (x : ℕ) (ys : List ℕ) (u : Lambda),
    Lambda.reduces (lapps (toLam X) (.var x :: ys.map Lambda.var)) u → IsHnf u →
    (hd u = some x ∨ ∃ y ∈ ys, hd u = some y) → hd u = some x ∧ WN X

theorem statmanLemmaOne_of_gen (h : StatmanLemmaGen) : StatmanLemmaOne := by
  intro X hX ⟨u, hr, hu, hx⟩
  exact (h X hX 0 [] u hr hu (Or.inl hx)).2

theorem wn_normal {t : Tm} (h : WNF t) : WN t := ⟨t, .refl, h⟩

/-- A neutral term with free head `x` decides the head of every head normal form. -/
theorem hd_of_reduces_neutral {t v u : Lambda} (hv : Lambda.reduces t v) (hn : Neutral v)
    (hu : Lambda.reduces t u) (hu' : IsHnf u) : hd u = hd v :=
  hd_unique hu hu' hv (.neutral hn)

theorem statmanGen_I (x : ℕ) (ys : List ℕ) (u : Lambda)
    (hr : Lambda.reduces (lapps (toLam .I) (.var x :: ys.map Lambda.var)) u) (hu : IsHnf u) :
    hd u = some x ∧ WN .I := by
  refine ⟨?_, wn_normal rfl⟩
  have h1 := reduces_lapps (ys.map Lambda.var) (reduces_I (.var x))
  obtain ⟨hn, hh⟩ := neutral_lapps (ys.map Lambda.var) (Neutral.var x)
  exact (hd_of_reduces_neutral h1 hn hr hu).trans hh

theorem statmanGen_M (x : ℕ) (ys : List ℕ) (u : Lambda)
    (hr : Lambda.reduces (lapps (toLam .M) (.var x :: ys.map Lambda.var)) u) (hu : IsHnf u) :
    hd u = some x ∧ WN .M := by
  refine ⟨?_, wn_normal rfl⟩
  have h1 := reduces_lapps (ys.map Lambda.var) (reduces_M (.var x))
  obtain ⟨hn, hh⟩ := neutral_lapps (ys.map Lambda.var) (Neutral.app (.var x) (Neutral.var x))
  exact (hd_of_reduces_neutral h1 hn hr hu).trans hh

theorem reduces_B1 (u : Lambda) :
    Lambda.reduces (.app lamB u)
      (.lam (.lam (.app (Lambda.lift 1 1 (Lambda.lift 1 0 u)) (.app (.var 1) (.var 0))))) := by
  have := Lambda.step.beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) u
  simp only [Lambda.subst, lift_lift_zero_one] at this
  exact Lambda.reduces.step _ _ _ (by simpa [lamB] using this) (.refl _)

theorem statmanGen_B (x : ℕ) (ys : List ℕ) (u : Lambda)
    (hr : Lambda.reduces (lapps (toLam .B) (.var x :: ys.map Lambda.var)) u) (hu : IsHnf u) :
    hd u = some x ∧ WN .B := by
  refine ⟨?_, wn_normal rfl⟩
  match ys with
  | [] =>
      have h1 := reduces_B1 (.var x)
      have e := hd_unique hr hu h1
        (.lam (.lam (.neutral (Neutral.app _ (by simp [Lambda.lift]; exact Neutral.var _)))))
      rw [e]; simp [Lambda.lift, hd]
  | [y] =>
      have h1 := reduces_B2 (.var x) (.var y)
      have e := hd_unique hr hu h1
        (.lam (.neutral (Neutral.app _ (by simp [Lambda.lift]; exact Neutral.var _))))
      rw [e]; simp [Lambda.lift, hd]
  | y :: z :: zs =>
      have h1 := reduces_lapps (zs.map Lambda.var) (reduces_B (.var x) (.var y) (.var z))
      obtain ⟨hn, hh⟩ := neutral_lapps (zs.map Lambda.var)
        (Neutral.app (.app (.var y) (.var z)) (Neutral.var x))
      exact (hd_of_reduces_neutral h1 hn hr hu).trans hh

/-! ## Weak normalizability -/

theorem wn_of_wstep {t t' : Tm} (hs : WStep t t') (h : WN t') : WN t := by
  obtain ⟨N, hr, hN⟩ := h
  exact ⟨N, Relation.ReflTransGen.head hs hr, hN⟩

theorem rtg_appL {u u' : Tm} (h : Relation.ReflTransGen WStep u u') (v : Tm) :
    Relation.ReflTransGen WStep (.app u v) (.app u' v) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (WStep.appL v hs)

theorem rtg_appR (u : Tm) {v v' : Tm} (h : Relation.ReflTransGen WStep v v') :
    Relation.ReflTransGen WStep (.app u v) (.app u v') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (WStep.appR u hs)

theorem wn_BU {U : Tm} (h : WN U) : WN (.app .B U) := by
  obtain ⟨U', hr, hU⟩ := h
  exact ⟨_, rtg_appR _ hr, li_app_B hU⟩

theorem wn_BUV {U V : Tm} (hU : WN U) (hV : WN V) : WN (.app (.app .B U) V) := by
  obtain ⟨U', hr, hU'⟩ := hU
  obtain ⟨V', hr', hV'⟩ := hV
  exact ⟨_, (rtg_appL (rtg_appR _ hr) V).trans (rtg_appR _ hr'), li_app_app_B hU' hV'⟩

end TLCA4
