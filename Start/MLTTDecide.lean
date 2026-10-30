/-
**Martin-Löf type theory: decidability of conversion** — milestone M30 (`M30-MLTT-CONV`).

* `MLTT.Alg.terminates` — **termination**: if the left-hand side of a comparison has an
  algorithmic derivation (with any partner) and so has the right-hand side, in an equal context
  and at an equal type, the run answers for all large fuels; the answers on neutral terms are
  eventually constant.  Typed terms have such derivations (`DEq.alg` of reflexivity).
* **`MLTT.TyEq.decide_spec`**, **`MLTT.DEq.decide_spec`** — on well-formed types, and on terms
  typable at a type, the run answers for all large fuels, and answers `true` exactly when the
  types (terms) are judgementally equal;
* **`MLTT.TyEq.decidable`**, **`MLTT.DEq.decidable`** — judgemental equality of well-formed
  types and of typed terms is decidable, by the search for the least fuel at which the run
  answers (`decideTyEq`, `decideDEq`).
-/

import Start.MLTTDecideCorrect

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Shapes of the steps -/

theorem natStep_ne_left {R : CFns} {Γ : Ctx} {k u : Tm} (hk : Neutral k) :
    natStep R Γ k u = neCmp R Γ k u (fun r => decide (r = some Tm.nat)) := by
  cases hk <;> rfl

theorem tyDownStep_ne_left {R : CFns} {Γ : Ctx} {K B : Tm} (hK : Neutral K) :
    tyDownStep R Γ K B = neCmp R Γ K B isUnivOpt := by
  cases hK <;> rfl

theorem tmDownStep_neTy {R : CFns} {Γ : Ctx} {t u A : Tm} (hA : Neutral A) :
    tmDownStep R Γ t u A = neCmp R Γ t u Option.isSome := by
  have h := isNe_iff.mpr hA
  have key : tmDownStep R Γ t u A =
      if isNe A = true then neCmp R Γ t u Option.isSome else some false := by
    cases hA <;> rfl
  rw [key, ite_eq_left h]

theorem neCmp_left_not_ne {R : CFns} {Γ : Ctx} {t u : Tm} {f : Option Tm → Bool}
    (ht : isNe t = false) : neCmp R Γ t u f = some false := by
  simp [neCmp, ht]

theorem neCmp_right_not_ne {R : CFns} {Γ : Ctx} {t u : Tm} {f : Option Tm → Bool}
    (hu : isNe u = false) : neCmp R Γ t u f = some false := by
  simp [neCmp, hu]

theorem neCmp_ne {R : CFns} {Γ : Ctx} {t u : Tm} {f : Option Tm → Bool} (ht : Neutral t)
    (hu : Neutral u) : neCmp R Γ t u f = (R.neDn Γ t u).map f := by
  simp [neCmp, isNe_iff.mpr ht, isNe_iff.mpr hu]

/-- A neutral comparison answers once the neutral comparison of the run does. -/
theorem neCmp_ne_none {R : CFns} {Γ : Ctx} {t u : Tm} {f : Option Tm → Bool}
    (h : Neutral t → Neutral u → R.neDn Γ t u ≠ none) : neCmp R Γ t u f ≠ none := by
  unfold neCmp
  split
  · next hne =>
      simp only [Bool.and_eq_true, isNe_iff] at hne
      intro e
      exact h hne.1 hne.2 (Option.map_eq_none_iff.mp e)
  · simp

theorem andThen_true {k : Unit → Option Bool} : andThen (some true) k = k () := rfl
theorem andThen_false {k : Unit → Option Bool} : andThen (some false) k = some false := rfl
theorem andThenNe_true {k : Unit → Option (Option Tm)} : andThenNe (some true) k = k () := rfl
theorem andThenNe_false {k : Unit → Option (Option Tm)} : andThenNe (some false) k = some none :=
  rfl

/-! ### Answers are eventually constant -/

open Classical in
theorem tyUp_eq_decide {n : ℕ} {Γ : Ctx} {A B : Tm} (hA : WfTy Γ A) (hB : WfTy Γ B)
    (hne : (cRun n).tyUp Γ A B ≠ none) : (cRun n).tyUp Γ A B = some (decide (TyUp Γ A B)) := by
  cases e : (cRun n).tyUp Γ A B with
  | none => exact absurd e hne
  | some b =>
      have c := (cRun_correct n).2.1 hA hB e
      congr 1
      by_cases hT : TyUp Γ A B
      · rw [decide_eq_true hT]; exact c.mpr hT
      · rw [decide_eq_false hT]
        cases b with
        | false => rfl
        | true => exact absurd (c.mp rfl) hT

open Classical in
theorem tmUp_eq_decide {n : ℕ} {Γ : Ctx} {t u A : Tm} (ht : HasTy Γ t A) (hu : HasTy Γ u A)
    (hne : (cRun n).tmUp Γ t u A ≠ none) :
    (cRun n).tmUp Γ t u A = some (decide (TmUp Γ t u A)) := by
  cases e : (cRun n).tmUp Γ t u A with
  | none => exact absurd e hne
  | some b =>
      have c := (cRun_correct n).2.2 ht hu e
      congr 1
      by_cases hT : TmUp Γ t u A
      · rw [decide_eq_true hT]; exact c.mpr hT
      · rw [decide_eq_false hT]
        cases b with
        | false => rfl
        | true => exact absurd (c.mp rfl) hT

/-! ### Termination -/

/-- The termination statement of each algorithmic judgement, for its left-hand side. -/
def AJd.Term : AJd → Prop
  | .neUp Γ k _ _ => ∀ {Δ : Ctx} {l l' B : Tm}, CtxEq Γ Δ → NeUp Δ l l' B →
      ∃ r n₀, ∀ n, n₀ ≤ n → neUpStep (cRun n) Δ k l = some r
  | .neDown Γ k _ _ => ∀ {Δ : Ctx} {l l' B : Tm}, CtxEq Γ Δ → NeDown Δ l l' B →
      ∃ r n₀, ∀ n, n₀ ≤ n → (cRun n).neDn Δ k l = some r
  | .tyUp Γ A _ => ∀ {Δ : Ctx} {B B' : Tm}, CtxEq Γ Δ → TyUp Δ B B' →
      ∃ n₀, ∀ n, n₀ ≤ n → (cRun n).tyUp Δ A B ≠ none
  | .tyDown Γ A _ => ∀ {Δ : Ctx} {B B' : Tm}, CtxEq Γ Δ → TyDown Δ B B' →
      ∃ n₀, ∀ n, n₀ ≤ n → tyDownStep (cRun n) Δ A B ≠ none
  | .tmUp Γ t _ A => ∀ {Δ : Ctx} {u u' A' : Tm}, CtxEq Γ Δ → TyEq Γ A A' → TmUp Δ u u' A' →
      ∃ n₀, ∀ n, n₀ ≤ n → (cRun n).tmUp Δ t u A' ≠ none
  | .tmDown Γ t _ A => ∀ {Δ : Ctx} {u u' A' : Tm}, CtxEq Γ Δ → TyEq Γ A A' → Whnf A' →
      TmDown Δ u u' A' → ∃ n₀, ∀ n, n₀ ≤ n → tmDownStep (cRun n) Δ t u A' ≠ none

open Classical in
/-- **Termination of the run.** -/
theorem Alg.terminates {J : AJd} (h : Alg J) : J.Term := by
  induction h with
  | varRefl _ =>
      intro Δ l l' B hc h2
      cases h2 <;> exact ⟨_, 0, fun n _ => rfl⟩
  | @appCong Γ k k' a a' F G hk _ ihk iha =>
      intro Δ l l' B hc h2
      cases h2 with
      | varRefl _ => exact ⟨_, 0, fun n _ => rfl⟩
      | natrecCong _ _ _ _ => exact ⟨_, 0, fun n _ => rfl⟩
      | emptyrecCong _ _ => exact ⟨_, 0, fun n _ => rfl⟩
      | @appCong _ l₁ m b c F₂ G₂ hd2 hb2 =>
          obtain ⟨r₁, n₁, hr₁⟩ := ihk hc hd2
          have hkΔ := (NeDown.sound (hk.stab hc)).tyL
          have hl₁ := (NeDown.sound hd2).tyL
          cases r₁ with
          | none =>
              refine ⟨none, n₁, fun n hn => ?_⟩
              show (cRun n).neDn Δ k l₁ >>= appTy (cRun n) Δ a b = some none
              rw [hr₁ n hn]; rfl
          | some T₁ =>
              cases T₁
              case pi F₃ G₃ =>
                have hd3 := ((cRun_correct n₁).1 hkΔ hl₁ (hr₁ n₁ le_rfl)).1 _ rfl
                have hFF₃ : TyEq Γ F F₃ :=
                  ((TyEq.pi_inj ((hk.stab hc).ty_eq hd3)).1).stab hc.symm
                have hl₁P := (NeDown.sound hd3).tyR
                have hF₂₃ : TyEq Δ F₂ F₃ :=
                  (TyEq.pi_inj ((NeDown.neutral hd2).1.tyUnique hl₁ hl₁P)).1
                obtain ⟨n₂, hn₂⟩ := iha hc hFF₃ (hb2.conv hF₂₃)
                have haF₃ := (TmUp.sound ((Alg.stab ‹TmUp Γ a a' F› hc).conv (hFF₃.stab hc))).tyL
                have hbF₃ := Der.conv (TmUp.sound hb2).tyL hF₂₃
                refine ⟨if decide (TmUp Δ a b F₃) = true then some (G₃[a]) else none, max n₁ n₂,
                  fun n hn => ?_⟩
                show (cRun n).neDn Δ k l₁ >>= appTy (cRun n) Δ a b = _
                rw [hr₁ n (le_of_max_le_left hn)]
                show ((cRun n).tmUp Δ a b F₃).map _ = _
                rw [tmUp_eq_decide haF₃ hbF₃ (hn₂ n (le_of_max_le_right hn))]
                rfl
              all_goals
                refine ⟨none, n₁, fun n hn => ?_⟩
                show (cRun n).neDn Δ k l₁ >>= appTy (cRun n) Δ a b = some none
                rw [hr₁ n hn]; rfl
  | @natrecCong Γ P P' z z' s s' m m' hP hz hs hm ihP ihz ihs ihm =>
      intro Δ l l' B hc h2
      cases h2 with
      | varRefl _ => exact ⟨_, 0, fun n _ => rfl⟩
      | appCong _ _ => exact ⟨_, 0, fun n _ => rfl⟩
      | emptyrecCong _ _ => exact ⟨_, 0, fun n _ => rfl⟩
      | @natrecCong _ Q Q₂ y y₂ w w₂ q q₂ hQ hy hw hq =>
          have hΔ := hc.wfR
          have hPe := TyUp.sound hP
          have hPΔ := hPe.wfL.stab hc.upNat
          have hQΔ := (TyUp.sound hQ).wfL
          obtain ⟨n₁, hn₁⟩ := ihP hc.upNat hQ
          by_cases hPQ : TyUp (Tm.nat :: Δ) P Q
          · have hPQe := TyUp.sound hPQ
            have hzΔ := (TmUp.sound (hz.stab hc)).tyL
            have hyP := Der.conv (TmUp.sound hy).tyL (Der.symmT (hPQe.inst (Der.zero hΔ)))
            obtain ⟨n₂, hn₂⟩ := ihz hc (Der.reflT (TmUp.sound hz).tyL.wfTy)
              (hy.conv (Der.symmT (hPQe.inst (Der.zero hΔ))))
            by_cases hzy : TmUp Δ z y (P[Tm.zero])
            · have hctxQP : CtxEq (Q :: Tm.nat :: Δ) (P :: Tm.nat :: Δ) :=
                (CtxEq.refl (Der.cons hΔ (Der.natT hΔ))).cons' (Der.symmT hPQe)
              have hsΔ := (TmUp.sound (hs.stab (hc.upNat.up hPe.wfL))).tyL
              have hw' : TmUp (P :: Tm.nat :: Δ) w w₂ (stepTy P) :=
                (hw.stab hctxQP).conv (Der.symmT hPQe.stepTy)
              have hwP := (TmUp.sound hw').tyL
              obtain ⟨n₃, hn₃⟩ := ihs (hc.upNat.up hPe.wfL)
                (Der.reflT (TmUp.sound hs).tyL.wfTy) hw'
              by_cases hsw : TmUp (P :: Tm.nat :: Δ) s w (stepTy P)
              · obtain ⟨r₄, n₄, hn₄⟩ := ihm hc hq
                refine ⟨if r₄ = some Tm.nat then some (P[m]) else none,
                  max (max n₁ n₂) (max n₃ n₄), fun n hn => ?_⟩
                have h1 : n₁ ≤ n := le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hn)
                have h2 : n₂ ≤ n := le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hn)
                have h3 : n₃ ≤ n := le_trans (le_max_left _ _) (le_max_right _ _ |>.trans hn)
                have h4 : n₄ ≤ n := le_trans (le_max_right _ _) (le_max_right _ _ |>.trans hn)
                simp only [neUpStep]
                rw [tyUp_eq_decide hPΔ hQΔ (hn₁ n h1), decide_eq_true hPQ, andThenNe_true]
                rw [tmUp_eq_decide hzΔ hyP (hn₂ n h2), decide_eq_true hzy, andThenNe_true]
                rw [tmUp_eq_decide hsΔ hwP (hn₃ n h3), decide_eq_true hsw, andThenNe_true]
                rw [hn₄ n h4]
                rfl
              · refine ⟨none, max (max n₁ n₂) n₃, fun n hn => ?_⟩
                have h1 : n₁ ≤ n := le_trans (le_max_left _ _) (le_max_left _ _ |>.trans hn)
                have h2 : n₂ ≤ n := le_trans (le_max_right _ _) (le_max_left _ _ |>.trans hn)
                have h3 : n₃ ≤ n := le_trans (le_max_right _ _) hn
                simp only [neUpStep]
                rw [tyUp_eq_decide hPΔ hQΔ (hn₁ n h1), decide_eq_true hPQ, andThenNe_true]
                rw [tmUp_eq_decide hzΔ hyP (hn₂ n h2), decide_eq_true hzy, andThenNe_true]
                rw [tmUp_eq_decide hsΔ hwP (hn₃ n h3), decide_eq_false hsw, andThenNe_false]
            · refine ⟨none, max n₁ n₂, fun n hn => ?_⟩
              simp only [neUpStep]
              rw [tyUp_eq_decide hPΔ hQΔ (hn₁ n (le_of_max_le_left hn)), decide_eq_true hPQ, andThenNe_true]
              rw [tmUp_eq_decide hzΔ hyP (hn₂ n (le_of_max_le_right hn)), decide_eq_false hzy, andThenNe_false]
          · refine ⟨none, n₁, fun n hn => ?_⟩
            simp only [neUpStep]
            rw [tyUp_eq_decide hPΔ hQΔ (hn₁ n hn), decide_eq_false hPQ, andThenNe_false]
  | @emptyrecCong Γ P P' e e' hP he ihP ihe =>
      intro Δ l l' B hc h2
      cases h2 with
      | varRefl _ => exact ⟨_, 0, fun n _ => rfl⟩
      | appCong _ _ => exact ⟨_, 0, fun n _ => rfl⟩
      | natrecCong _ _ _ _ => exact ⟨_, 0, fun n _ => rfl⟩
      | @emptyrecCong _ _ Q₂ q q₂ hQ hq =>
          have hPΔ := (TyUp.sound hP).wfL.stab hc
          have hQΔ := (TyUp.sound hQ).wfL
          obtain ⟨n₁, hn₁⟩ := ihP hc hQ
          by_cases hPQ : TyUp Δ P B
          · obtain ⟨r₂, n₂, hn₂⟩ := ihe hc hq
            refine ⟨if r₂ = some Tm.empty then some P else none, max n₁ n₂, fun n hn => ?_⟩
            simp only [neUpStep]
            rw [tyUp_eq_decide hPΔ hQΔ (hn₁ n (le_of_max_le_left hn)), decide_eq_true hPQ, andThenNe_true]
            rw [hn₂ n (le_of_max_le_right hn)]
            rfl
          · refine ⟨none, n₁, fun n hn => ?_⟩
            simp only [neUpStep]
            rw [tyUp_eq_decide hPΔ hQΔ (hn₁ n hn), decide_eq_false hPQ, andThenNe_false]
  | @down Γ k k' A A' hk _ _ ih =>
      intro Δ l l' B hc h2
      obtain ⟨B₀, hl₀, -, -⟩ := h2.inv
      obtain ⟨r₀, n₁, hr₀⟩ := ih hc hl₀
      have hkΔ := (NeUp.sound (hk.stab hc)).tyL
      have hlΔ := (NeUp.sound hl₀).tyL
      cases r₀ with
      | none =>
          refine ⟨none, n₁ + 1, fun n hn => ?_⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show downStep m (neUpStep (cRun m) Δ k l) = _
          rw [hr₀ m (by omega)]
          rfl
      | some T =>
          have hT := (neUpStep_correct (cRun_correct n₁) hkΔ hlΔ (hr₀ n₁ le_rfl)).1 _ rfl
          obtain ⟨T', hTT', hT'⟩ := (NeUp.sound hT).tyL.wfTy.whnf
          obtain ⟨n₂, hn₂⟩ := whnfF_of_tyReds hTT' hT'
          refine ⟨some T', n₁ + n₂ + 1, fun n hn => ?_⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show downStep m (neUpStep (cRun m) Δ k l) = _
          rw [hr₀ m (by omega)]
          show (whnfF m T).map some = _
          rw [hn₂ m (by omega)]
          rfl
  | @tyRed Γ A A₁ A' A₁' hA _ hA₁ _ _ ih =>
      intro Δ B B' hc h2
      obtain ⟨B₁, B₁', hB, -, hB₁, -, hd2⟩ := h2.inv
      obtain ⟨n₁, hn₁⟩ := whnfF_of_tyReds hA hA₁
      obtain ⟨n₂, hn₂⟩ := whnfF_of_tyReds hB hB₁
      obtain ⟨n₃, hn₃⟩ := ih hc hd2
      refine ⟨n₁ + n₂ + n₃ + 1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      show (match whnfF m A, whnfF m B with
        | some A', some B' => tyDownStep (cRun m) Δ A' B'
        | _, _ => none) ≠ none
      rw [hn₁ m (by omega), hn₂ m (by omega)]
      exact hn₃ m (by omega)
  | univRefl _ =>
      intro Δ B B' hc h2
      refine ⟨0, fun n _ => ?_⟩
      cases h2
      case neTy hd => cases (NeDown.neutral hd).1 <;> simp [tyDownStep, neCmp, isNe]
      all_goals simp [tyDownStep, neCmp, isNe]
  | natRefl _ =>
      intro Δ B B' hc h2
      refine ⟨0, fun n _ => ?_⟩
      cases h2
      case neTy hd => cases (NeDown.neutral hd).1 <;> simp [tyDownStep, neCmp, isNe]
      all_goals simp [tyDownStep, neCmp, isNe]
  | emptyRefl _ =>
      intro Δ B B' hc h2
      refine ⟨0, fun n _ => ?_⟩
      cases h2
      case neTy hd => cases (NeDown.neutral hd).1 <;> simp [tyDownStep, neCmp, isNe]
      all_goals simp [tyDownStep, neCmp, isNe]
  | @neTy Γ K M l hd ih =>
      intro Δ B B' hc h2
      have hK := (NeDown.neutral hd).1
      by_cases hB : Neutral B
      · obtain ⟨l', hd2⟩ := h2.inv_ne hB
        obtain ⟨r, n₁, hr⟩ := ih hc hd2
        refine ⟨n₁, fun n hn => ?_⟩
        rw [tyDownStep_ne_left hK]
        exact neCmp_ne_none (fun _ _ => by rw [hr n hn]; simp)
      · refine ⟨0, fun n _ => ?_⟩
        rw [tyDownStep_ne_left hK]
        exact neCmp_ne_none (fun _ h => absurd h hB)
  | @piCong Γ F H G E hF hG ihF ihG =>
      intro Δ B B' hc h2
      cases h2 with
      | univRefl _ => exact ⟨0, fun n _ => by simp [tyDownStep, neCmp, isNe]⟩
      | natRefl _ => exact ⟨0, fun n _ => by simp [tyDownStep, neCmp, isNe]⟩
      | emptyRefl _ => exact ⟨0, fun n _ => by simp [tyDownStep, neCmp, isNe]⟩
      | neTy hd2 =>
          have hnB := (NeDown.neutral hd2).1
          refine ⟨0, fun n _ => ?_⟩
          cases hnB <;> simp [tyDownStep, neCmp, isNe]
      | @piCong _ H₂ K E₂ M hH hE =>
          have hFΔ := (TyUp.sound hF).wfL.stab hc
          have hH₂ := (TyUp.sound hH).wfL
          obtain ⟨n₁, hn₁⟩ := ihF hc hH
          by_cases hFH : TyUp Δ F H₂
          · have hctx : CtxEq (H₂ :: Δ) (F :: Δ) :=
              (CtxEq.refl hc.wfR).cons' (Der.symmT (TyUp.sound hFH))
            obtain ⟨n₂, hn₂⟩ := ihG (hc.up (TyUp.sound hF).wfL) (hE.stab hctx)
            refine ⟨max n₁ n₂, fun n hn => ?_⟩
            show andThen ((cRun n).tyUp Δ F H₂) (fun _ => (cRun n).tyUp (F :: Δ) G E₂) ≠ none
            rw [tyUp_eq_decide hFΔ hH₂ (hn₁ n (le_of_max_le_left hn)), decide_eq_true hFH,
              andThen_true]
            exact hn₂ n (le_of_max_le_right hn)
          · refine ⟨n₁, fun n hn => ?_⟩
            show andThen ((cRun n).tyUp Δ F H₂) (fun _ => (cRun n).tyUp (F :: Δ) G E₂) ≠ none
            rw [tyUp_eq_decide hFΔ hH₂ (hn₁ n hn), decide_eq_false hFH, andThen_false]
            simp
  | @tmRed Γ t t₁ t' t₁' A B hAB ht _ hB ht₁ _ _ ih =>
      intro Δ u u' A' hc hAA' h2
      obtain ⟨B₂, u₂, u₂', hAB₂, hu, -, hB₂, hu₂, -, hd2⟩ := h2.inv
      obtain ⟨n₁, hn₁⟩ := whnfF_of_tyReds hAB₂ hB₂
      obtain ⟨n₂, hn₂⟩ := whnfF_of_treds ht ht₁
      obtain ⟨n₃, hn₃⟩ := whnfF_of_treds hu hu₂
      have hBB₂ : TyEq Γ B B₂ :=
        Der.transT (Der.symmT hAB.tyEq) (Der.transT hAA' (hAB₂.tyEq.stab hc.symm))
      obtain ⟨n₄, hn₄⟩ := ih hc hBB₂ hB₂ hd2
      refine ⟨n₁ + n₂ + n₃ + n₄ + 1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      show (match whnfF m A', whnfF m t, whnfF m u with
        | some A', some t', some u' => tmDownStep (cRun m) Δ t' u' A'
        | _, _, _ => none) ≠ none
      rw [hn₁ m (by omega), hn₂ m (by omega), hn₃ m (by omega)]
      exact hn₄ m (by omega)
  | @neNat Γ k k' hd ih =>
      intro Δ u u' A' hc hAA' hA' h2
      rw [TyEq.nat_whnf hAA' hA'] at h2 ⊢
      have hk := (NeDown.neutral hd).1
      refine (?_ : ∃ n₀, ∀ n, n₀ ≤ n → natStep (cRun n) Δ k u ≠ none)
      cases h2 with
      | neNat hd2 =>
          obtain ⟨r, n₁, hr⟩ := ih hc hd2
          refine ⟨n₁, fun n hn => ?_⟩
          rw [natStep_ne_left hk]
          exact neCmp_ne_none (fun _ _ => by rw [hr n hn]; simp)
      | neNe _ _ hN _ => cases hN
      | zeroRefl _ =>
          refine ⟨0, fun n _ => ?_⟩
          rw [natStep_ne_left hk, neCmp_right_not_ne rfl]
          simp
      | succCong _ =>
          refine ⟨0, fun n _ => ?_⟩
          rw [natStep_ne_left hk, neCmp_right_not_ne rfl]
          simp
  | @neEmpty Γ k k' hd ih =>
      intro Δ u u' A' hc hAA' hA' h2
      rw [TyEq.empty_whnf hAA' hA'] at h2 ⊢
      have hd2 := h2.inv_empty
      obtain ⟨r, n₁, hr⟩ := ih hc hd2
      refine ⟨n₁, fun n hn => ?_⟩
      exact neCmp_ne_none (fun _ _ => by rw [hr n hn]; simp)
  | @neNe Γ k k' A B' _ _ hA hd ih =>
      intro Δ u u' A' hc hAA' hA' h2
      have hNA' := hAA'.ne_whnf hA hA'
      obtain ⟨_, -, hd2⟩ := h2.inv_neTy hNA'
      obtain ⟨r, n₁, hr⟩ := ih hc hd2
      refine ⟨n₁, fun n hn => ?_⟩
      rw [tmDownStep_neTy hNA']
      exact neCmp_ne_none (fun _ _ => by rw [hr n hn]; simp)
  | @univTm Γ A₁ A₂ l _ _ _ ih =>
      intro Δ u u' A' hc hAA' hA' h2
      rw [TyEq.univ_whnf hAA' hA'] at h2 ⊢
      obtain ⟨-, hd2⟩ := h2.inv_univ
      exact ih hc hd2
  | zeroRefl _ =>
      intro Δ u u' A' hc hAA' hA' h2
      rw [TyEq.nat_whnf hAA' hA'] at h2 ⊢
      refine ⟨0, fun n _ => ?_⟩
      show natStep (cRun n) Δ Tm.zero u ≠ none
      cases u <;> simp [natStep, neCmp, isNe]
  | @succCong Γ m m' _ ih =>
      intro Δ u u' A' hc hAA' hA' h2
      rw [TyEq.nat_whnf hAA' hA'] at h2 ⊢
      show ∃ n₀, ∀ n, n₀ ≤ n → natStep (cRun n) Δ (succ m) u ≠ none
      cases h2 with
      | succCong hd2 =>
          obtain ⟨n₁, hn₁⟩ := ih hc (Der.reflT (Der.natT hc.wfL)) hd2
          exact ⟨n₁, fun n hn => hn₁ n hn⟩
      | zeroRefl _ => exact ⟨0, fun n _ => by simp [natStep, neCmp, isNe]⟩
      | neNat hd2 =>
          refine ⟨0, fun n _ => ?_⟩
          have key : natStep (cRun n) Δ (succ m) u =
              neCmp (cRun n) Δ (succ m) u (fun r => decide (r = some Tm.nat)) := by
            cases (NeDown.neutral hd2).1 <;> rfl
          rw [key, neCmp_left_not_ne rfl]
          simp
      | neNe _ _ hN _ => cases hN
  | @eta Γ f g F G hf _ _ _ _ ih =>
      intro Δ u u' A' hc hAA' hA' h2
      obtain ⟨F₂, G₂, rfl, hFF, hGG⟩ := hAA'.pi_whnf hA'
      obtain ⟨-, -, hd2⟩ := h2.inv_pi
      exact ih (hc.cons' hFF) hGG hd2

/-! ### Decidability -/

/-- **The run decides the judgemental equality of well-formed types.** -/
theorem TyEq.decide_spec {Γ : Ctx} {A B : Tm} (hA : WfTy Γ A) (hB : WfTy Γ B) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ b, (cRun n).tyUp Γ A B = some b ∧ (b = true ↔ TyEq Γ A B) := by
  obtain ⟨n₀, hn₀⟩ := Alg.terminates (TyEq.alg (Der.reflT hA)) (CtxEq.refl hA.wf)
    (TyEq.alg (Der.reflT hB))
  refine ⟨n₀, fun n hn => ?_⟩
  cases e : (cRun n).tyUp Γ A B with
  | none => exact absurd e (hn₀ n hn)
  | some b => exact ⟨b, rfl, ((cRun_correct n).2.1 hA hB e).trans TyEq.iff_alg.symm⟩

/-- **The run decides the judgemental equality of terms of a type.** -/
theorem DEq.decide_spec {Γ : Ctx} {t u A : Tm} (ht : HasTy Γ t A) (hu : HasTy Γ u A) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ b, (cRun n).tmUp Γ t u A = some b ∧ (b = true ↔ DEq Γ t u A) := by
  obtain ⟨n₀, hn₀⟩ := Alg.terminates (DEq.alg (Der.refl ht)) (CtxEq.refl ht.wf)
    (Der.reflT ht.wfTy) (DEq.alg (Der.refl hu))
  refine ⟨n₀, fun n hn => ?_⟩
  cases e : (cRun n).tmUp Γ t u A with
  | none => exact absurd e (hn₀ n hn)
  | some b => exact ⟨b, rfl, ((cRun_correct n).2.2 ht hu e).trans DEq.iff_alg.symm⟩

theorem TyEq.run_answers {Γ : Ctx} {A B : Tm} (hA : WfTy Γ A) (hB : WfTy Γ B) :
    ∃ n, (cRun n).tyUp Γ A B ≠ none := by
  obtain ⟨n₀, hn₀⟩ := TyEq.decide_spec hA hB
  obtain ⟨b, hb, -⟩ := hn₀ n₀ le_rfl
  exact ⟨n₀, by rw [hb]; simp⟩

theorem DEq.run_answers {Γ : Ctx} {t u A : Tm} (ht : HasTy Γ t A) (hu : HasTy Γ u A) :
    ∃ n, (cRun n).tmUp Γ t u A ≠ none := by
  obtain ⟨n₀, hn₀⟩ := DEq.decide_spec ht hu
  obtain ⟨b, hb, -⟩ := hn₀ n₀ le_rfl
  exact ⟨n₀, by rw [hb]; simp⟩

/-- **The decision procedure for types**: run at the least fuel at which the run answers. -/
def decideTyEq (Γ : Ctx) (A B : Tm) (h : ∃ n, (cRun n).tyUp Γ A B ≠ none) : Bool :=
  ((cRun (Nat.find h)).tyUp Γ A B).getD false

/-- **The decision procedure for terms.** -/
def decideDEq (Γ : Ctx) (t u A : Tm) (h : ∃ n, (cRun n).tmUp Γ t u A ≠ none) : Bool :=
  ((cRun (Nat.find h)).tmUp Γ t u A).getD false

theorem decideTyEq_spec {Γ : Ctx} {A B : Tm} (hA : WfTy Γ A) (hB : WfTy Γ B) :
    decideTyEq Γ A B (TyEq.run_answers hA hB) = true ↔ TyEq Γ A B := by
  have hfind := Nat.find_spec (TyEq.run_answers hA hB)
  unfold decideTyEq
  cases e : (cRun (Nat.find (TyEq.run_answers hA hB))).tyUp Γ A B with
  | none => exact absurd e hfind
  | some b =>
      simp only [Option.getD_some]
      exact ((cRun_correct _).2.1 hA hB e).trans TyEq.iff_alg.symm

theorem decideDEq_spec {Γ : Ctx} {t u A : Tm} (ht : HasTy Γ t A) (hu : HasTy Γ u A) :
    decideDEq Γ t u A (DEq.run_answers ht hu) = true ↔ DEq Γ t u A := by
  have hfind := Nat.find_spec (DEq.run_answers ht hu)
  unfold decideDEq
  cases e : (cRun (Nat.find (DEq.run_answers ht hu))).tmUp Γ t u A with
  | none => exact absurd e hfind
  | some b =>
      simp only [Option.getD_some]
      exact ((cRun_correct _).2.2 ht hu e).trans DEq.iff_alg.symm

/-- **Judgemental equality of well-formed types is decidable.** -/
def TyEq.decidable {Γ : Ctx} {A B : Tm} (hA : WfTy Γ A) (hB : WfTy Γ B) :
    Decidable (TyEq Γ A B) :=
  decidable_of_iff _ (decideTyEq_spec hA hB)

/-- **Judgemental equality of terms of a type is decidable.** -/
def DEq.decidable {Γ : Ctx} {t u A : Tm} (ht : HasTy Γ t A) (hu : HasTy Γ u A) :
    Decidable (DEq Γ t u A) :=
  decidable_of_iff _ (decideDEq_spec ht hu)

end MLTT
