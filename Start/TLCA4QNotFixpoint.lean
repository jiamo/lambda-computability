import Start.TLCA4YIndex

/-!
# TLCA open problem 4: `Q = M ∘ M ∘ (B M) ∘ B ∘ B` is not a βη fixed-point combinator
(row M20-TLCA4-Q-NOT-FIXPOINT; series V, big round, run 3, item A1)

`Q x →w x^{tri n} (M Aₙ₊₁[B x] R)` with the tail `R = M A₀[B x]` (`Q_stage`).  The reducts of
`Q x` keep the *shape* `xᵏ (H ρ)`: `ρ` is a reduct of the tail, and `H` is an `x`-chain over a
*core* — `P Q` with components `P`, `Q` of indices `i`, `j` (grammar `YG`, unique index by
`YG.index_unique`) or `M Q` (`i = j`) — whose depth `d` below the top satisfies the conservation
law `k + d + i = tri j` (the triangular pattern of the `T` proof, with every `y = B x` counted as
one `x`).

The depth changes when a core fires (`P Q → C[Q/q]` inserts new `x`'s above the new core), so
the chains carry **integer** heights (`ZC`, the constructors of `XC` over `ℤ`) and the conserved
quantity `K = k + h` is stored in the base family (`QBase x K`: a core of indices `(i, j)` at
height `n` has `K + i = tri j + n`).

* `ByqR.subst` — `R[Q/q]` for `R ∈ ByqR`, `Q` of index `j`, is a component of index `j + 1`;
* `ZC`, `ZC.step`, `ZC.reduces` — integer-height chains are closed under βη given their base;
* `QCore`, `QBase`, **`YC.subst`** — substituting a component into a chain under `q` gives an
  integer-height chain over cores, shifted, with the conservation law;
* `QBase.zcBase` — the base is closed under βη-steps (a firing core becomes a chain);
* `QShape`, **`QShape.step`**, `QShape.reduces` — the shape is closed under βη-reduction;
* `QCore.unique`, **`ZC.unique`** — `K − h` is determined by the chain;
* `QShape.not_xPrefix` — a term and its `x`-prefix cannot both have the shape;
* **`Q_not_fixedPoint`** — `¬ Q x =βη x (Q x)`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- **Substituting a component for `q` in a reduct of `B y q`** gives a component of the next
index. -/
theorem ByqR.subst {x j : ℕ} {R Q : Lambda} (hR : ByqR (x + 1) R) (hQ : YG x j Q) :
    YG x (j + 1) (Lambda.subst Q 0 R) := by
  cases hR with
  | bb =>
    have : Lambda.subst Q 0 (.app (bbx (x + 1)) (.var 0)) = .app (bbx x) Q := by
      simp [Lambda.subst, bbx, lamB]
    rw [this]; exact .byApp .bb hQ
  | bpre =>
    have : Lambda.subst Q 0 (.app (bbpre (x + 1)) (.var 0)) = .app (bbpre x) Q := by
      simp [Lambda.subst, bbpre, bxPre, lamB]
    rw [this]; exact .byApp .bpre hQ
  | l1 =>
    have : Lambda.subst Q 0 (.app (byl1 (x + 1)) (.var 0)) = .app (byl1 x) Q := by
      simp [Lambda.subst, byl1, lamB]
    rw [this]; exact .byApp .l1 hQ
  | l2 =>
    have : Lambda.subst Q 0 (.app (byl2 (x + 1)) (.var 0)) = .app (byl2 x) Q := by
      simp [Lambda.subst, byl2, bxPre]
    rw [this]; exact .byApp .l2 hQ
  | l3 =>
    have : Lambda.subst Q 0 (.app (byl3 (x + 1)) (.var 0)) = .app (byl3 x) Q := by
      simp [Lambda.subst, byl3]
    rw [this]; exact .byApp .l3 hQ
  | m1 =>
    have : Lambda.subst Q 0 (bym1 (x + 1)) =
        .lam (.app (.app lamB (.var (x + 1))) (.app (Lambda.lift 1 0 Q) (.var 0))) := by
      simp [Lambda.subst, bym1, lamB]
    rw [this]; exact .lam (.bx (.base (.comp hQ)))
  | m2 =>
    have : Lambda.subst Q 0 (bym2 (x + 1)) =
        .lam (.app (bxPre (x + 1)) (.app (Lambda.lift 1 0 Q) (.var 0))) := by
      simp [Lambda.subst, bym2, bxPre]
    rw [this]; exact .lam (.bx1 (.base (.comp hQ)))
  | m3 =>
    have : Lambda.subst Q 0 (bym3 (x + 1)) =
        .lam (.lam (xPow (.var (x + 2)) 1
          (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 Q) (.var 0))) (.var 0)))) := by
      simp [Lambda.subst, bym3, xPow, Lambda.lift, lift_lift_zero_one]
    rw [this]; exact .lam (.rq (m := 1) (.base (.comp hQ)) (by omega))


/-- `x`-chains with **integer** heights over an indexed base family (the constructors of `XC`). -/
inductive ZC (base : ℤ → Lambda → Prop) (x : ℕ) : ℤ → Lambda → Prop
  | base {i : ℤ} {P : Lambda} : base i P → ZC base x i P
  | bx {i : ℤ} {P : Lambda} : ZC base x i P → ZC base x (i + 1) (.app (.app lamB (.var x)) P)
  | bx1 {i : ℤ} {P : Lambda} : ZC base x i P → ZC base x (i + 1) (.app (bxPre x) P)
  | rq {i i' : ℤ} {m : ℕ} {R : Lambda} : ZC base x i' R → (m : ℤ) + i' = i →
      ZC base x i (.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) (.var 0))))

/-- Closure hypotheses on the base of integer-height chains. -/
structure ZCBase (base : ℤ → Lambda → Prop) (x : ℕ) : Prop where
  step : ∀ {i : ℤ} {P P' : Lambda}, base i P → betaEtaStep P P' → ZC base x i P'
  lam : ∀ {i : ℤ} {m : ℕ} {c : Lambda}, base i (.lam c) →
    ZC base x ((m : ℤ) + i) (.lam (xPow (.var (x + 1)) m c))

theorem ZC.lam_xPow {base : ℤ → Lambda → Prop} {x : ℕ} (hb : ZCBase base x) :
    ∀ {i : ℤ} {c : Lambda}, ZC base x i (.lam c) → ∀ (m : ℕ),
      ZC base x ((m : ℤ) + i) (.lam (xPow (.var (x + 1)) m c)) := by
  intro i c h m
  generalize e : Lambda.lam c = t at h
  cases h with
  | base hP => subst e; exact hb.lam hP
  | bx _ => cases e
  | bx1 _ => cases e
  | rq hR hm =>
    simp only [Lambda.lam.injEq] at e
    subst e
    rw [xPow_add]
    exact .rq hR (by push_cast; omega)

/-- Integer-height chains are closed under one βη-step, given closure of the base. -/
theorem ZC.step {base : ℤ → Lambda → Prop} {x : ℕ} (hb : ZCBase base x) {i : ℤ}
    {P P' : Lambda} (h : ZC base x i P) (hs : betaEtaStep P P') : ZC base x i P' := by
  induction h generalizing P' with
  | base hP => exact hb.step hP hs
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
          .lam (xPow (.var (x + 1)) 1 (.app (Lambda.lift 1 0 P) (.var 0))) := by
        intro P; simp [Lambda.subst, xPow]
      rw [e]; exact ZC.rq (m := 1) h (by push_cast; omega)
    · exact (nf_bxPre x _ hf).elim
    · exact .bx1 (ih ha)
  | @rq i₀ i' m R h hm ih =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb', rfl⟩ | ⟨f, hf, rfl⟩
    · obtain ⟨H', hH, rfl⟩ := betaEtaStep_xPow hb'
      rcases betaEtaStep_app_cases hH with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
      · obtain ⟨c0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
        rw [Lambda.subst_var_lift_succ c0 0]
        have := ZC.lam_xPow hb h m
        rwa [hm] at this
      · obtain ⟨R', rfl, hR'⟩ := betaEtaStep_lift_inv hf
        exact .rq (ih hR') hm
      · exact (betaEtaStep_var ha).elim
    · obtain ⟨rfl, h1, -⟩ := xPow_eta_inv hf
      rw [Lambda.lift_one_injective 0 h1] at h
      have e : i' = i₀ := by push_cast at hm; omega
      subst e
      exact h

theorem ZC.reduces {base : ℤ → Lambda → Prop} {x : ℕ} (hb : ZCBase base x) {i : ℤ}
    {P Q : Lambda} (h : ZC base x i P) (hr : betaEtaReduces P Q) : ZC base x i Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hb hs


/-- The cores of the reducts of `Q x`: `P Q` with components of indices `i`, `j`, or `M Q`
(`i = j`). -/
inductive QCore (x : ℕ) : ℕ → ℕ → Lambda → Prop
  | pq {i j : ℕ} {P Q : Lambda} : YG x i P → YG x j Q → QCore x i j (.app P Q)
  | mq {j : ℕ} {Q : Lambda} : YG x j Q → QCore x j j (.app lamM Q)

/-- Base family of the chains in the shape, with the conserved quantity `K`: a core of indices
`(i, j)` sits at height `n` with `K + i = tri j + n`. -/
def QBase (x : ℕ) (K : ℤ) (n : ℤ) (Z : Lambda) : Prop :=
  ∃ i j : ℕ, QCore x i j Z ∧ K + i = (tri j : ℤ) + n

theorem lift_subst_zero (R Q : Lambda) :
    Lambda.subst (Lambda.lift 1 0 Q) 1 (Lambda.lift 1 0 R) = Lambda.lift 1 0 (Lambda.subst Q 0 R) :=
  (Lambda.lift_subst R Q 1 0 0 (le_refl 0)).symm

/-- **Substituting a component `Q` of index `j` for `q` in a chain under `q`** gives an
integer-height chain over the cores, shifted by `s`, provided `K + j = tri (j + 1) + s`. -/
theorem YC.subst {x : ℕ} {c : ℕ} {C : Lambda} (h : YC x c C) {j : ℕ} {Q : Lambda} {K s : ℤ}
    (hQ : YG x j Q) (hK : K + j = (tri (j + 1) : ℤ) + s) :
    ZC (QBase x K) x ((c : ℤ) + s) (Lambda.subst Q 0 C) := by
  match h with
  | .base hb =>
    cases hb with
    | q hR =>
      simp only [Lambda.subst, if_pos]
      refine .base ⟨j, j + 1, .pq hQ (hR.subst hQ), ?_⟩
      push_cast at hK ⊢; omega
    | m hR =>
      have e : Lambda.subst Q 0 lamM = lamM := by simp [Lambda.subst, lamM]
      simp only [Lambda.subst, e]
      refine .base ⟨j + 1, j + 1, .mq (hR.subst hQ), ?_⟩
      push_cast at hK ⊢; omega
    | rr h1 h2 =>
      simp only [Lambda.subst]
      refine .base ⟨j + 1, j + 1, .pq (h1.subst hQ) (h2.subst hQ), ?_⟩
      push_cast at hK ⊢; omega
    | @comp i' R hR =>
      simp only [Lambda.subst, Lambda.subst_lift, if_pos]
      refine .base ⟨i', j, .pq hR hQ, ?_⟩
      simp only [tri] at hK
      push_cast at hK ⊢; omega
  | @YC.bx _ n P h =>
    have e : Lambda.subst Q 0 (.app (.app lamB (.var (x + 1))) P) =
        .app (.app lamB (.var x)) (Lambda.subst Q 0 P) := by simp [Lambda.subst, lamB]
    rw [e]
    have := ZC.bx (YC.subst h hQ hK)
    convert this using 1
    push_cast; ring
  | @YC.bx1 _ n P h =>
    have e : Lambda.subst Q 0 (.app (bxPre (x + 1)) P) =
        .app (bxPre x) (Lambda.subst Q 0 P) := by simp [Lambda.subst, bxPre]
    rw [e]
    have := ZC.bx1 (YC.subst h hQ hK)
    convert this using 1
    push_cast; ring
  | @YC.rq _ n n' m R h hm =>
    rw [show Lambda.subst Q 0 (.lam (xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) (.var 0)))) =
      .lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 (Lambda.subst Q 0 R)) (.var 0))) by
        simp only [Lambda.subst, subst_xPow, ← lift_subst_zero]
        simp]
    exact .rq (YC.subst h hQ hK) (by omega)


theorem QBase.zcBase (x : ℕ) (K : ℤ) : ZCBase (QBase x K) x where
  step := by
    rintro n Z Z' ⟨i, j, hc, hK⟩ hs
    cases hc with
    | pq hP hQ =>
      rcases betaEtaStep_app_cases hs with ⟨c, rfl, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · cases hP with
        | lam hc =>
          have h1 : K + j = (tri (j + 1) : ℤ) + (n - (i + 1)) := by
            simp only [tri]; push_cast; omega
          have := YC.subst hc hQ h1
          convert this using 1
          push_cast; ring
      · exact .base ⟨i, j, .pq (hP.step hf) hQ, hK⟩
      · exact .base ⟨i, j, .pq hP (hQ.step ha), hK⟩
    | mq hQ =>
      rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamM, Lambda.lam.injEq] at hc
        subst hc
        simp only [Lambda.subst, if_pos]
        exact .base ⟨_, _, .pq hQ hQ, hK⟩
      · exact (nf_lamM _ hf).elim
      · exact .base ⟨_, _, .mq (hQ.step ha), hK⟩
  lam := by
    rintro n m c ⟨i, j, hc, -⟩
    cases hc

/-- The tail `R = M A₀[B x]` of the reducts of `Q x`. -/
def qTailLam (x : ℕ) : Lambda := toLam (qTail x)

/-- **The shape of the reducts of `Q x`**: `xᵏ (H ρ)` with `ρ` a reduct of the tail and `H` an
integer-height chain over the cores with conserved quantity `k + h`. -/
def QShape (x : ℕ) (N : Lambda) : Prop :=
  ∃ (k : ℕ) (h : ℤ) (H ρ : Lambda), N = xPow (.var x) k (.app H ρ) ∧
    betaEtaReduces (qTailLam x) ρ ∧ ZC (QBase x ((k : ℤ) + h)) x h H

/-- **The shape is closed under one βη-step.** -/
theorem QShape.step {x : ℕ} {N N' : Lambda} (h : QShape x N) (hs : betaEtaStep N N') :
    QShape x N' := by
  obtain ⟨k, hh, H, ρ, rfl, hρ, hH⟩ := h
  obtain ⟨T', hT, rfl⟩ := betaEtaStep_xPow hs
  rcases betaEtaStep_app_cases hT with ⟨c, rfl, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
  · generalize e : Lambda.lam c = t at hH
    cases hH with
    | base hb => subst e; obtain ⟨i, j, hc, -⟩ := hb; cases hc
    | bx _ => cases e
    | bx1 _ => cases e
    | @rq _ i' m R hR hm =>
      simp only [Lambda.lam.injEq] at e
      subst e
      rw [subst_xPow_var]
      simp only [Lambda.subst, Lambda.subst_lift, if_pos]
      rw [xPow_add]
      refine ⟨k + m, i', R, ρ, rfl, hρ, ?_⟩
      have : ((k + m : ℕ) : ℤ) + i' = (k : ℤ) + hh := by push_cast; omega
      rw [this]; exact hR
  · exact ⟨k, hh, f', ρ, rfl, hρ, hH.step (QBase.zcBase x _) hf⟩
  · exact ⟨k, hh, H, a', rfl, hρ.tail ha, hH⟩

theorem QShape.reduces {x : ℕ} {N N' : Lambda} (h : QShape x N) (hr : betaEtaReduces N N') :
    QShape x N' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs


theorem YG.ne_var {x i n : ℕ} {P : Lambda} (h : YG x i P) : P ≠ .var n := by
  cases h <;> simp

theorem ByR.ne_lamB {y : ℕ} {R : Lambda} (h : ByR y R) : R ≠ lamB := by
  cases h <;> simp [bbx, bbpre, byl1, byl2, byl3, lamB]

theorem ByR.ne_var {y n : ℕ} {R : Lambda} (h : ByR y R) : R ≠ .var n := by
  cases h <;> simp [bbx, bbpre, byl1, byl2, byl3]

theorem YG.ne_lamB_var {x i : ℕ} {P : Lambda} (h : YG x i P) : P ≠ .app lamB (.var x) := by
  intro e
  cases h with
  | bm _ => simp [lamB] at e
  | bm1 hR => simp only [Lambda.app.injEq] at e; exact hR.ne_var e.2
  | bm2 hR => simp only [Lambda.app.injEq] at e; exact hR.ne_var e.2
  | byApp hR _ => simp only [Lambda.app.injEq] at e; exact hR.ne_lamB e.1
  | lam _ => simp at e

theorem YG.ne_bxPre {x i : ℕ} {P : Lambda} (h : YG x i P) : P ≠ bxPre x := by
  intro e
  cases h with
  | bm _ => simp [bxPre] at e
  | bm1 _ => simp [bxPre] at e
  | bm2 _ => simp [bxPre] at e
  | byApp _ _ => simp [bxPre] at e
  | lam hc =>
    simp only [bxPre, Lambda.lam.injEq] at e
    subst e
    generalize e2 : Lambda.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0))) = t at hc
    cases hc with
    | base hb => subst e2; cases hb
    | bx _ => cases e2
    | bx1 _ => cases e2
    | @rq _ _ m R hR _ =>
      simp only [Lambda.lam.injEq] at e2
      match m, e2 with
      | 0, e2 => simp [xPow] at e2
      | 1, e2 =>
        simp only [xPow, Lambda.app.injEq, true_and] at e2
        obtain ⟨e3, -⟩ := e2
        cases R <;> simp [Lambda.lift] at e3
        exact hR.ne_var rfl
      | m + 2, e2 => simp [xPow] at e2

theorem YG.ne_lamM {x i : ℕ} {P : Lambda} (h : YG x i P) : P ≠ lamM := by
  intro e
  cases h with
  | bm _ => simp [lamM] at e
  | bm1 _ => simp [lamM, bmPre1] at e
  | bm2 _ => simp [lamM, bmPre2] at e
  | byApp _ _ => simp [lamM] at e
  | lam hc =>
    simp only [lamM, Lambda.lam.injEq] at e
    subst e
    generalize e2 : Lambda.app (.var 0) (.var 0) = t at hc
    cases hc with
    | base hb =>
      subst e2
      generalize e3 : Lambda.app (.var 0) (.var 0) = t at hb
      cases hb with
      | m hR => simp [lamM] at e3
      | rr h1 _ => simp only [Lambda.app.injEq] at e3; exact h1.ne_var e3.1.symm
      | comp _ =>
        simp only [Lambda.app.injEq] at e3
        obtain ⟨e4, -⟩ := e3
        rename_i R _
        cases R <;> simp [Lambda.lift] at e4
    | bx _ => simp [lamB] at e2
    | bx1 _ => simp [bxPre] at e2
    | rq _ _ => simp at e2

theorem QCore.unique {x i j i' j' : ℕ} {Z : Lambda} (h : QCore x i j Z) (h' : QCore x i' j' Z) :
    i = i' ∧ j = j' := by
  cases h with
  | pq hP hQ =>
    generalize e : Lambda.app _ _ = t at h'
    cases h' with
    | pq hP' hQ' =>
      simp only [Lambda.app.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨hP.index_unique hP', hQ.index_unique hQ'⟩
    | mq hQ' =>
      simp only [Lambda.app.injEq] at e
      exact (hP.ne_lamM e.1).elim
  | mq hQ =>
    generalize e : Lambda.app lamM _ = t at h'
    cases h' with
    | pq hP' hQ' =>
      simp only [Lambda.app.injEq] at e
      exact (hP'.ne_lamM e.1.symm).elim
    | mq hQ' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      obtain rfl := hQ.index_unique hQ'
      exact ⟨rfl, rfl⟩

theorem QCore.ne_bx {x i j : ℕ} {Z P : Lambda} (h : QCore x i j Z) :
    Z ≠ .app (.app lamB (.var x)) P := by
  intro e
  cases h with
  | pq hP _ => simp only [Lambda.app.injEq] at e; exact hP.ne_lamB_var e.1
  | mq _ => simp [lamM, lamB] at e

theorem QCore.ne_bx1 {x i j : ℕ} {Z P : Lambda} (h : QCore x i j Z) :
    Z ≠ .app (bxPre x) P := by
  intro e
  cases h with
  | pq hP _ => simp only [Lambda.app.injEq] at e; exact hP.ne_bxPre e.1
  | mq _ => simp [lamM, bxPre] at e

theorem QCore.ne_lam {x i j : ℕ} {Z c : Lambda} (h : QCore x i j Z) : Z ≠ .lam c := by
  cases h <;> simp

theorem ZC.ne_var {x : ℕ} {K h : ℤ} {H : Lambda} (hH : ZC (QBase x K) x h H) (n : ℕ) :
    H ≠ .var n := by
  cases hH with
  | base hb => obtain ⟨i, j, hc, -⟩ := hb; cases hc <;> simp
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

/-- **The conserved quantity `K − h` is determined by the chain.** -/
theorem ZC.unique {x : ℕ} {K h : ℤ} {H : Lambda} (hH : ZC (QBase x K) x h H) :
    ∀ {K' h' : ℤ}, ZC (QBase x K') x h' H → K - h = K' - h' := by
  induction hH with
  | base hb =>
    intro K' h' hH'
    obtain ⟨i, j, hc, hK⟩ := hb
    cases hH' with
    | base hb' =>
      obtain ⟨i', j', hc', hK'⟩ := hb'
      obtain ⟨rfl, rfl⟩ := hc.unique hc'
      omega
    | bx _ => exact (hc.ne_bx rfl).elim
    | bx1 _ => exact (hc.ne_bx1 rfl).elim
    | rq _ _ => exact (hc.ne_lam rfl).elim
  | bx hP ih =>
    intro K' h' hH'
    generalize e : Lambda.app (.app lamB (.var x)) _ = t at hH'
    cases hH' with
    | base hb' => subst e; obtain ⟨i, j, hc, -⟩ := hb'; exact (hc.ne_bx rfl).elim
    | bx hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := ih hP'
      omega
    | bx1 _ => simp [lamB, bxPre] at e
    | rq _ _ => simp at e
  | bx1 hP ih =>
    intro K' h' hH'
    generalize e : Lambda.app (bxPre x) _ = t at hH'
    cases hH' with
    | base hb' => subst e; obtain ⟨i, j, hc, -⟩ := hb'; exact (hc.ne_bx1 rfl).elim
    | bx _ => simp [lamB, bxPre] at e
    | bx1 hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := ih hP'
      omega
    | rq _ _ => simp at e
  | @rq i₀ i' m R hR hm ih =>
    intro K' h' hH'
    generalize e : Lambda.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) (.var 0))) = t at hH'
    cases hH' with
    | base hb' => subst e; obtain ⟨i, j, hc, -⟩ := hb'; exact (hc.ne_lam rfl).elim
    | bx _ => simp at e
    | bx1 _ => simp at e
    | @rq _ i'' m' R' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      have hA : Lambda.lift 1 0 R ≠ .var (x + 1) := by
        intro e'; cases R <;> simp [Lambda.lift] at e'; exact hR.ne_var x (by rw [e'])
      have hA' : Lambda.lift 1 0 R' ≠ .var (x + 1) := by
        intro e'; cases R' <;> simp [Lambda.lift] at e'; exact hR'.ne_var x (by rw [e'])
      obtain ⟨rfl, e1, -⟩ := xPow_app_unique hA hA' e
      obtain rfl := Lambda.lift_one_injective 0 e1
      have := ih hR'
      omega

/-- **A term and its `x`-prefix cannot both have the shape.** -/
theorem QShape.not_xPrefix {x : ℕ} {N : Lambda} (h : QShape x N)
    (h' : QShape x (.app (.var x) N)) : False := by
  obtain ⟨k, hh, H, ρ, rfl, -, hH⟩ := h
  obtain ⟨k', hh', H', ρ', e, -, hH'⟩ := h'
  have e' : xPow (.var x) (k + 1) (.app H ρ) = xPow (.var x) k' (.app H' ρ') := e
  obtain ⟨rfl, rfl, rfl⟩ := xPow_app_unique (hH.ne_var x) (hH'.ne_var x) e'
  have := hH.unique hH'
  push_cast at this
  omega

/-- **`Q = M ∘ M ∘ (B M) ∘ B ∘ B` is not a βη fixed-point combinator.** -/
theorem Q_not_fixedPoint :
    ¬ Lambda.betaEtaConv (toLam (app tQ (var 0))) (toLam (app (var 0) (app tQ (var 0)))) := by
  intro hconv
  set N₀ : Lambda := .app (.app lamM (toLam (tAy (app B (var 0)) 1))) (qTailLam 0) with hN₀
  have hQ : betaEtaReduces (toLam (app tQ (var 0))) N₀ := .of_reduces (Q_stage_betaEta 0 0)
  have hS : QShape 0 N₀ :=
    ⟨0, 0, _, _, rfl, .refl _, .base ⟨1, 1, .mq (YG.of_tAy 0 1), by simp [tri]⟩⟩
  obtain ⟨w, hw₁, hw₂⟩ := hconv.common_reduct
  obtain ⟨w', rfl, hw'⟩ := betaEtaReduces_app_var' hw₂
  obtain ⟨D, hD₁, hD₂⟩ := Lambda.betaEta_church_rosser hQ hw'
  obtain ⟨E, hE₁, hE₂⟩ := Lambda.betaEta_church_rosser hQ
    (hw₁.trans (betaEtaReduces_app_right (.var 0) hD₂))
  obtain ⟨D', rfl, hD'⟩ := betaEtaReduces_app_var' hE₂
  exact (hS.reduces (hD₁.trans hD')).not_xPrefix (hS.reduces hE₁)

end TLCA4
