import Start.TLCA4TComponents

/-!
# Series V, round 4, run 1, part A2: an explicit grammar for the components of `T x`
(row M20-TLCA4-T-NOT-FIXPOINT)

`TLCA4.TGram x i P` is an explicit grammar for the components of index `i` (the βη-reducts of
`Aᵢ`, `TLCA4.TComp`).  Its abstractions `λq. b` have one of four bodies, with `x` at index `x + 1`
under the binder and `q` the bound variable:

* `xᵐ (R q)` with `R` a component of index `i'` and `m + i' = i`;
* `xᵐ (q R)` with `R` a reduct of `B x q` and `m = i + 1`;
* `xᵐ (M R)` with `R` a reduct of `B x q` and `m = i`;
* `xᵐ (R₁ R₂)` with `R₁`, `R₂` reducts of `B x q` and `m = i`.

* **`TGram.step`** — the grammar is closed under one βη-step (no `Q` involved);
* **`TComp.tGram`** — every component is in the grammar;
* **`TComp.abstraction`** — the abstraction lemma: the body of a component abstraction of index `i`
  has one of the four shapes above.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep etaStep betaEta_church_rosser)

/-! ### Step inversion -/

theorem betaEtaStep_app_cases {f a u : Lambda} (h : betaEtaStep (.app f a) u) :
    (∃ c, f = .lam c ∧ u = Lambda.subst a 0 c) ∨ (∃ f', betaEtaStep f f' ∧ u = .app f' a) ∨
      (∃ a', betaEtaStep a a' ∧ u = .app f a') := by
  rcases h with hb | he
  · cases hb with
    | beta c _ => exact .inl ⟨c, rfl, rfl⟩
    | app_left _ f' _ h' => exact .inr (.inl ⟨f', .beta h', rfl⟩)
    | app_right _ _ a' h' => exact .inr (.inr ⟨a', .beta h', rfl⟩)
  · cases he with
    | app_left _ h' => exact .inr (.inl ⟨_, .eta h', rfl⟩)
    | app_right _ h' => exact .inr (.inr ⟨_, .eta h', rfl⟩)

theorem betaEtaStep_lam_cases {b u : Lambda} (h : betaEtaStep (.lam b) u) :
    (∃ b', betaEtaStep b b' ∧ u = .lam b') ∨ (∃ f, b = .app (Lambda.lift 1 0 f) (.var 0) ∧ u = f) := by
  rcases h with hb | he
  · cases hb with
    | lam _ b' h' => exact .inl ⟨b', .beta h', rfl⟩
  · cases he with
    | eta _ => exact .inr ⟨_, rfl, rfl⟩
    | lam h' => exact .inl ⟨_, .eta h', rfl⟩

theorem betaEtaStep_var {i : ℕ} {u : Lambda} (h : betaEtaStep (.var i) u) : False :=
  betaEtaNf_var i u h

theorem betaEtaStep_xPow {y m : ℕ} {H u : Lambda} (h : betaEtaStep (xPow (.var y) m H) u) :
    ∃ H', betaEtaStep H H' ∧ u = xPow (.var y) m H' := by
  induction m generalizing u with
  | zero => exact ⟨u, h, rfl⟩
  | succ m ih =>
    rcases betaEtaStep_app_cases h with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · exact (betaEtaStep_var hf).elim
    · obtain ⟨H', h1, rfl⟩ := ih ha
      exact ⟨H', h1, rfl⟩

theorem xPow_add (f : Lambda) : ∀ (m n : ℕ) (t : Lambda), xPow f m (xPow f n t) = xPow f (m + n) t
  | 0, n, t => by simp [xPow]
  | m + 1, n, t => by
    rw [show m + 1 + n = (m + n) + 1 by omega]
    simp [xPow, xPow_add f m n t]

theorem xPow_app_self (f t : Lambda) (m : ℕ) : xPow f m (.app f t) = xPow f (m + 1) t := by
  have := xPow_add f m 1 t
  simpa [xPow] using this

/-! ### The concrete pieces -/

/-- `λab. x (a b)`, the reduct of `B x` (with `x` at index `y`). -/
def bxPre (y : ℕ) : Lambda := .lam (.lam (.app (.var (y + 2)) (.app (.var 1) (.var 0))))

/-- `λab. M (a b)`, the reduct of `B M`. -/
def bmPre1 : Lambda := .lam (.lam (.app lamM (.app (.var 1) (.var 0))))

/-- `λab. (a b) (a b)`. -/
def bmPre2 : Lambda := .lam (.lam (.app (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0))))

/-- `λw. x (q w)` (with `x` at index `y` and `q` at index `0`). -/
def lamXq (y : ℕ) : Lambda := .lam (.app (.var (y + 1)) (.app (.var 1) (.var 0)))

theorem nf_app_app_var {i j k : ℕ} : BetaEtaNf (.app (.var i) (.app (.var j) (.var k))) :=
  betaEtaNf_app_var (betaEtaNf_app_var (betaEtaNf_var _))

theorem nf_lamB : BetaEtaNf lamB := by
  unfold lamB
  refine betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_lam nf_app_app_var ?_) ?_) ?_ <;>
    intro f h <;> simp at h

theorem nf_lamM : BetaEtaNf lamM := by
  unfold lamM
  refine betaEtaNf_lam (betaEtaNf_app_var (betaEtaNf_var 0)) ?_
  intro f h
  simp only [Lambda.app.injEq] at h
  obtain ⟨h1, -⟩ := h
  cases f with
  | var n => simp [Lambda.lift] at h1
  | app _ _ => simp [Lambda.lift] at h1
  | lam _ => simp [Lambda.lift] at h1

theorem nf_bxPre (y : ℕ) : BetaEtaNf (bxPre y) := by
  unfold bxPre
  refine betaEtaNf_lam (betaEtaNf_lam nf_app_app_var ?_) ?_ <;> intro f h <;> simp at h

theorem nf_lamXq (y : ℕ) : BetaEtaNf (lamXq y) := by
  unfold lamXq
  refine betaEtaNf_lam nf_app_app_var ?_
  intro f h; simp at h

theorem nf_app_var_var {i j : ℕ} : BetaEtaNf (.app (.var i) (.var j)) :=
  betaEtaNf_app_var (betaEtaNf_var _)

theorem nf_bmPre2 : BetaEtaNf bmPre2 := by
  unfold bmPre2
  refine betaEtaNf_lam (betaEtaNf_lam ?_ ?_) ?_
  · intro u hu
    rcases betaEtaStep_app_cases hu with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
    · cases hc
    · exact nf_app_var_var _ hf
    · exact nf_app_var_var _ ha
  · intro f h; simp at h
  · intro f h; simp at h

theorem step_bmPre1 {u : Lambda} (h : betaEtaStep bmPre1 u) : u = bmPre2 := by
  unfold bmPre1 at h
  rcases betaEtaStep_lam_cases h with ⟨b', hb, rfl⟩ | ⟨f, hf, _⟩
  · rcases betaEtaStep_lam_cases hb with ⟨b'', hb', rfl⟩ | ⟨f, hf, _⟩
    · rcases betaEtaStep_app_cases hb' with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
      · simp only [lamM, Lambda.lam.injEq] at hc
        subst hc
        simp [Lambda.subst, bmPre2]
      · exact (nf_lamM _ hf).elim
      · exact (nf_app_var_var _ ha).elim
    · simp at hf
  · simp at hf

theorem step_lamB_var (y : ℕ) :
    Lambda.subst (.var y) 0 (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) = bxPre y := by
  simp [Lambda.subst, Lambda.lift, bxPre]

theorem step_lamB_M :
    Lambda.subst lamM 0 (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) = bmPre1 := by
  simp [Lambda.subst, Lambda.lift, bmPre1, lamM]

/-! ### Reducts of `B x` and of `B x q` -/

/-- The reducts of `B x` (`x` at index `y`). -/
inductive BxR (y : ℕ) : Lambda → Prop
  | b : BxR y (.app lamB (.var y))
  | pre : BxR y (bxPre y)

/-- The reducts of `B x q` (`x` at index `y`, `q` at index `0`). -/
inductive BxqR (y : ℕ) : Lambda → Prop
  | b : BxqR y (.app (.app lamB (.var y)) (.var 0))
  | pre : BxqR y (.app (bxPre y) (.var 0))
  | lam : BxqR y (lamXq y)

theorem BxR.step {y : ℕ} {R R' : Lambda} (h : BxR y R) (hs : betaEtaStep R R') : BxR y R' := by
  cases h with
  | b =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
    · simp only [lamB, Lambda.lam.injEq] at hc
      subst hc
      rw [step_lamB_var]; exact .pre
    · exact (nf_lamB _ hf).elim
    · exact (betaEtaStep_var ha).elim
  | pre => exact (nf_bxPre y _ hs).elim

theorem BxqR.step {y : ℕ} {R R' : Lambda} (h : BxqR y R) (hs : betaEtaStep R R') :
    BxqR y R' := by
  cases h with
  | b =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .pre
      · exact (nf_lamB _ hf').elim
      · exact (betaEtaStep_var ha).elim
    · exact (betaEtaStep_var ha).elim
  | pre =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
    · simp only [bxPre, Lambda.lam.injEq] at hc
      subst hc
      have : Lambda.subst (.var 0) 0 (.lam (.app (.var (y + 2)) (.app (.var 1) (.var 0)))) =
          lamXq y := by simp [Lambda.subst, Lambda.lift, lamXq]
      rw [this]; exact .lam
    · exact (nf_bxPre y _ hf).elim
    · exact (betaEtaStep_var ha).elim
  | lam => exact (nf_lamXq y _ hs).elim

theorem BxqR.ne_var {y j : ℕ} {R : Lambda} (h : BxqR y R) : R ≠ .var j := by
  cases h <;> simp [lamXq]

theorem BxR.lift {y : ℕ} {R : Lambda} (h : BxR y R) :
    BxqR (y + 1) (.app (Lambda.lift 1 0 R) (.var 0)) := by
  cases h with
  | b => exact .b
  | pre =>
    have : Lambda.lift 1 0 (bxPre y) = bxPre (y + 1) := by simp [bxPre, Lambda.lift]
    rw [this]; exact .pre

/-! ### The grammar -/

/-- **The explicit grammar of the components of index `i`** (`x` at index `x`). -/
inductive TGram (x : ℕ) : ℕ → Lambda → Prop
  | bm {R : Lambda} : BxR x R → TGram x 0 (.app (.app lamB lamM) R)
  | bm1 {R : Lambda} : BxR x R → TGram x 0 (.app bmPre1 R)
  | bm2 {R : Lambda} : BxR x R → TGram x 0 (.app bmPre2 R)
  | bx {i : ℕ} {P : Lambda} : TGram x i P → TGram x (i + 1) (.app (.app lamB (.var x)) P)
  | bx1 {i : ℕ} {P : Lambda} : TGram x i P → TGram x (i + 1) (.app (bxPre x) P)
  | rq {i i' m : ℕ} {R : Lambda} : TGram x i' R → m + i' = i →
      TGram x i (.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) (.var 0))))
  | qr {i m : ℕ} {R : Lambda} : BxqR (x + 1) R → m = i + 1 →
      TGram x i (.lam (xPow (.var (x + 1)) m (.app (.var 0) R)))
  | mr {i m : ℕ} {R : Lambda} : BxqR (x + 1) R → m = i →
      TGram x i (.lam (xPow (.var (x + 1)) m (.app lamM R)))
  | rr {i m : ℕ} {R₁ R₂ : Lambda} : BxqR (x + 1) R₁ → BxqR (x + 1) R₂ → m = i →
      TGram x i (.lam (xPow (.var (x + 1)) m (.app R₁ R₂)))

/-- The bodies of the abstractions of the grammar (the four shapes). -/
inductive TBody (x i : ℕ) : Lambda → Prop
  | rq {i' m : ℕ} {R : Lambda} : TGram x i' R → m + i' = i →
      TBody x i (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) (.var 0)))
  | qr {m : ℕ} {R : Lambda} : BxqR (x + 1) R → m = i + 1 →
      TBody x i (xPow (.var (x + 1)) m (.app (.var 0) R))
  | mr {m : ℕ} {R : Lambda} : BxqR (x + 1) R → m = i →
      TBody x i (xPow (.var (x + 1)) m (.app lamM R))
  | rr {m : ℕ} {R₁ R₂ : Lambda} : BxqR (x + 1) R₁ → BxqR (x + 1) R₂ → m = i →
      TBody x i (xPow (.var (x + 1)) m (.app R₁ R₂))

theorem TGram.lam_inv {x i : ℕ} {b : Lambda} (h : TGram x i (.lam b)) : TBody x i b := by
  cases h with
  | rq h hm => exact .rq h hm
  | qr h hm => exact .qr h hm
  | mr h hm => exact .mr h hm
  | rr h1 h2 hm => exact .rr h1 h2 hm

theorem TBody.toGram {x i : ℕ} {b : Lambda} (h : TBody x i b) : TGram x i (.lam b) := by
  cases h with
  | rq h hm => exact .rq h hm
  | qr h hm => exact .qr h hm
  | mr h hm => exact .mr h hm
  | rr h1 h2 hm => exact .rr h1 h2 hm

/-- Prefixing a body by more `x`'s. -/
theorem TBody.xPow {x i : ℕ} {b : Lambda} (h : TBody x i b) (m : ℕ) :
    TBody x (m + i) (TLCA4.xPow (.var (x + 1)) m b) := by
  cases h with
  | rq h hm => rw [xPow_add]; exact .rq h (by omega)
  | qr h hm => rw [xPow_add]; exact .qr h (by omega)
  | mr h hm => rw [xPow_add]; exact .mr h (by omega)
  | rr h1 h2 hm => rw [xPow_add]; exact .rr h1 h2 (by omega)

theorem xPow_eta_inv {y m : ℕ} {a c f : Lambda}
    (h : xPow (.var y) m (.app a c) = .app (Lambda.lift 1 0 f) (.var 0)) :
    m = 0 ∧ a = Lambda.lift 1 0 f ∧ c = .var 0 := by
  cases m with
  | zero => simp only [xPow, Lambda.app.injEq] at h; exact ⟨rfl, h⟩
  | succ m =>
    simp only [xPow, Lambda.app.injEq] at h
    exact absurd h.2 (xPow_app_ne_var _ _ _ m 0)

theorem betaEtaStep_lift_inv {R u : Lambda} (h : betaEtaStep (Lambda.lift 1 0 R) u) :
    ∃ R', u = Lambda.lift 1 0 R' ∧ betaEtaStep R R' := by
  rcases h with hb | he
  · obtain ⟨R', rfl, h'⟩ := Lambda.step_lift_inv hb
    exact ⟨R', rfl, .beta h'⟩
  · obtain ⟨R', rfl, h'⟩ := Lambda.etaStep_lift_inv he
    exact ⟨R', rfl, .eta h'⟩

/-- **The grammar is closed under one βη-step.** -/
theorem TGram.step {x i : ℕ} {P P' : Lambda} (h : TGram x i P) (hs : betaEtaStep P P') :
    TGram x i P' := by
  induction h generalizing P' with
  | bm hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_M]; exact .bm1 hR
      · exact (nf_lamB _ hf').elim
      · exact (nf_lamM _ ha).elim
    · exact .bm (hR.step ha)
  | bm1 hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre1, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ R : Lambda, Lambda.subst R 0 (.lam (.app lamM (.app (.var 1) (.var 0)))) =
          .lam (.app lamM (.app (Lambda.lift 1 0 R) (.var 0))) := by
        intro R; simp [Lambda.subst, lamM]
      rw [e]; exact TGram.mr (m := 0) hR.lift rfl
    · rw [step_bmPre1 hf]; exact .bm2 hR
    · exact .bm1 (hR.step ha)
  | bm2 hR =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre2, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ R : Lambda, Lambda.subst R 0
          (.lam (.app (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0)))) =
          .lam (.app (.app (Lambda.lift 1 0 R) (.var 0)) (.app (Lambda.lift 1 0 R) (.var 0))) := by
        intro R; simp [Lambda.subst]
      rw [e]; exact TGram.rr (m := 0) hR.lift hR.lift rfl
    · exact (nf_bmPre2 _ hf).elim
    · exact .bm2 (hR.step ha)
  | bx h ih =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bx1 h
      · exact (nf_lamB _ hf').elim
      · exact (betaEtaStep_var ha).elim
    · exact .bx (ih ha)
  | bx1 h ih =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bxPre, Lambda.lam.injEq] at hc
      subst hc
      have e : ∀ P : Lambda, Lambda.subst P 0 (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0)))) =
          .lam (.app (.var (x + 1)) (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst]
      rw [e]; exact TGram.rq (m := 1) h (by omega)
    · exact (nf_bxPre x _ hf).elim
    · exact .bx1 (ih ha)
  | @rq i₀ i' m R h hm ih =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        rw [Lambda.subst_var_lift_succ c0 0]
        have := (h.lam_inv.xPow m).toGram
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (ih hR') hm
      · exact (betaEtaStep_var ha).elim
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by omega
      subst e
      exact h
  | qr hR hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb
      rcases betaEtaStep_app_cases hH with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
      · cases hc
      · exact (betaEtaStep_var hf).elim
      · exact .qr (hR.step ha) hm
    · obtain ⟨-, -, h2⟩ := xPow_eta_inv hf
      exact (hR.ne_var h2).elim
  | mr hR hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamM, Lambda.lam.injEq] at hc
        subst hc
        simp only [Lambda.subst, ite_eq_left]
        exact .rr hR hR hm
      · exact (nf_lamM _ hf).elim
      · exact .mr (hR.step ha) hm
    · obtain ⟨-, -, h2⟩ := xPow_eta_inv hf
      exact (hR.ne_var h2).elim
  | rr h1 h2 hm =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · cases h1 with
        | b => cases hc
        | pre => cases hc
        | lam =>
          simp only [lamXq, Lambda.lam.injEq] at hc
          subst hc
          have e : ∀ R : Lambda, Lambda.subst R 0 (.app (.var (x + 1 + 1)) (.app (.var 1) (.var 0)))
              = .app (.var (x + 1)) (.app (.var 0) R) := by
            intro R; simp [Lambda.subst]
          rw [e, xPow_app_self]
          exact .qr h2 (by omega)
      · exact .rr (h1.step hf) h2 hm
      · exact .rr h1 (h2.step ha) hm
    · obtain ⟨-, -, h3⟩ := xPow_eta_inv hf
      exact (h2.ne_var h3).elim

theorem TGram.reduces {x i : ℕ} {P Q : Lambda} (h : TGram x i P) (hr : betaEtaReduces P Q) :
    TGram x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **Every component is in the grammar.** -/
theorem TComp.tGram {x i : ℕ} {P : Lambda} (h : TComp x i P) : TGram x i P := by
  induction h with
  | base => exact .bm .b
  | bx _ ih => exact .bx ih
  | red _ hr ih => exact ih.reduces hr

/-- **The abstraction lemma** (open form): the body of a component abstraction of index `i`
has one of the four shapes of `TBody`. -/
theorem TComp.abstraction {x i : ℕ} {b : Lambda} (h : TComp x i (.lam b)) : TBody x i b :=
  h.tGram.lam_inv

end TLCA4
