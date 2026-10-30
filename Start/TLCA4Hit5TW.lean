import Start.TLCA4Hit5S
import Start.TLCA4TailExt

/-!
# TLCA open problem 4: the `s`-layer of `hit5` with two-argument-chain bodies
(row M20-TLCA4-BETAETA; big round 2, run 1, item A1)

The extension `Ext` of `Start/TLCA4TailExt.lean` adds the cores `M W` and `W Y` with `W` a
two-argument chain in the sense of `TW` (`Start/TLCA4TailW.lean`).  The `w`-layer of
`Start/TLCA4Hit5W.lean` describes the bodies of the `w`-reducts by `WqR`, whose second
constructor allows arbitrary lifted chains; after substituting a component for `q` those are
not `TW` members in general.  This module redoes the `w`- and `s`-layers with the bodies taken
in `TW (YB x) (x + 1) 1` itself, so that substitution lands in `TW`:

* `WT x` — the reducts of `w = B B V` (`V ∈ YG x 0`) with `TW` bodies; **`WT.step`**;
* `WqT x` — the reducts of `W q`; `SqT x` — the bodies under `q` of the `s`-reducts
  (`M Wq`, `Wq Y`, chains of height `1` over `YB x`); `ST x` — the reducts of `s = B M W`;
* **`WqT.step`**, **`SqT.step`**, **`ST.step`**, `ST.reduces`, **`ST.of_h5s`** — the grammar is
  closed under βη and contains `s`;
* **`TC.subst_gen`**, **`TW.subst_gen`** — substituting any term `Q` for `q` in a chain (or a
  two-argument chain) under `q` gives a chain at top level over any family that receives the
  substituted cores, with the height shifted by a constant.  This is the substitution step of
  `H5Core.step`: firing `λq. C` on a component of index `j`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-! ### Generic substitution into chains under `q` -/

/-- **Substituting for `q` in a chain under `q`**: if every substituted core lands in `core`
with its height shifted by `s`, the substituted chain is a top-level chain over `core`. -/
theorem TC.subst_gen {base core : ℤ → Lambda → Prop} {x : ℕ} {Q : Lambda} {s : ℤ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → core (i + s) (Lambda.subst Q 0 P))
    {c : ℤ} {C : Lambda} (h : TC base (x + 1) c C) : TC core x (c + s) (Lambda.subst Q 0 C) := by
  generalize ex : x + 1 = x' at h
  induction h with
  | base hP => exact .base (hb hP)
  | @bx i P _ ih =>
    subst ex
    have e : Lambda.subst Q 0 (.app (.app lamB (.var (x + 1))) P) =
        .app (.app lamB (.var x)) (Lambda.subst Q 0 P) := by
      simp [Lambda.subst, subst_lamB]
    rw [e, show i + 1 + s = (i + s) + 1 by ring]; exact .bx ih
  | @bx1 i P _ ih =>
    subst ex
    have e : Lambda.subst Q 0 (.app (bxPre (x + 1)) P) = .app (bxPre x) (Lambda.subst Q 0 P) := by
      simp only [Lambda.subst, subst_bxPre]
    rw [e, show i + 1 + s = (i + s) + 1 by ring]; exact .bx1 ih
  | @rq i i' m R T _ hm ih =>
    subst ex
    have e : Lambda.subst Q 0 (.lam (xPow (.var (x + 1 + 1)) m (.app (Lambda.lift 1 0 R) T))) =
        .lam (xPow (.var (x + 1)) m
          (.app (Lambda.lift 1 0 (Lambda.subst Q 0 R)) (Lambda.subst (Lambda.lift 1 0 Q) 1 T))) := by
      simp only [Lambda.subst, subst_xPow]
      rw [Lambda.lift_subst R Q 1 0 0 (le_refl 0)]
      simp
    rw [e]; exact .rq ih (by omega)

/-- **Substituting for `q` in a two-argument chain under `q`.** -/
theorem TW.subst_gen {base core : ℤ → Lambda → Prop} {x : ℕ} {Q : Lambda} {s : ℤ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → core (i + s) (Lambda.subst Q 0 P))
    {c : ℤ} {W : Lambda} (h : TW base (x + 1) c W) : TW core x (c + s) (Lambda.subst Q 0 W) := by
  cases h with
  | wB hR =>
    simp only [Lambda.subst, subst_lamB]
    exact .wB (hR.subst_gen hb)
  | @wK R hR =>
    have e : Lambda.subst Q 0 (.lam (Lambda.lift 1 0 R)) =
        .lam (Lambda.lift 1 0 (Lambda.subst Q 0 R)) := by
      simp only [Lambda.subst]
      rw [Lambda.lift_subst R Q 1 0 0 (le_refl 0)]
    rw [e]; exact .wK (hR.subst_gen hb)
  | @wP i' m R T hR hm =>
    have e1 : Lambda.subst (Lambda.lift 1 0 Q) 1 (Lambda.lift 1 0 R) =
        Lambda.lift 1 0 (Lambda.subst Q 0 R) := by
      rw [Lambda.lift_subst R Q 1 0 0 (le_refl 0)]
    have e2 : Lambda.subst (Lambda.lift 1 0 (Lambda.lift 1 0 Q)) 2
        (Lambda.lift 1 0 (Lambda.lift 1 0 R)) =
        Lambda.lift 1 0 (Lambda.lift 1 0 (Lambda.subst Q 0 R)) := by
      rw [← e1, Lambda.lift_subst (Lambda.lift 1 0 R) (Lambda.lift 1 0 Q) 1 0 1 (Nat.zero_le 1)]
    have e : Lambda.subst Q 0 (.lam (.lam (xPow (.var (x + 1 + 2)) m
        (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)))) =
        .lam (.lam (xPow (.var (x + 2)) m
          (.app (Lambda.lift 1 0 (Lambda.lift 1 0 (Lambda.subst Q 0 R)))
            (Lambda.subst (Lambda.lift 1 0 (Lambda.lift 1 0 Q)) 2 T)))) := by
      simp only [Lambda.subst, subst_xPow]
      rw [e2]
      simp
    rw [e]; exact .wP (hR.subst_gen hb) (by omega)

/-! ### The `w`-layer with `TW` bodies -/

/-- The reducts of `w = B B V` (`V` a reduct of `v`) with bodies in `TW (YB x) (x + 1) 1`. -/
inductive WT (x : ℕ) : Lambda → Prop
  | wbb {V : Lambda} : YG x 0 V → WT x (.app (.app lamB lamB) V)
  | wpre {V : Lambda} : YG x 0 V → WT x (.app bbPre V)
  | wpre2 {V : Lambda} : YG x 0 V → WT x (.app bbPre2 V)
  | wlam {W : Lambda} : TW (YB x) (x + 1) 1 W → WT x (.lam W)

theorem TW.step_YB {x : ℕ} {i : ℤ} {W W' : Lambda} (h : TW (YB x) (x + 1) i W)
    (hs : betaEtaStep W W') : TW (YB x) (x + 1) i W' :=
  h.step YB.step YB.not_lam hs

theorem TW.ne_var_YB {x : ℕ} {i : ℤ} {W : Lambda} (h : TW (YB x) (x + 1) i W) (n : ℕ) :
    W ≠ .var n := by
  cases h <;> simp

/-- The comp core `(lift V) q` of a `v`-reduct `V`, as a chain of height `1`. -/
theorem compYB {x : ℕ} {V : Lambda} (hV : YG x 0 V) :
    TC (YB x) (x + 1) 1 (.app (Lambda.lift 1 0 V) (.var 0)) :=
  .base ⟨1, rfl, .comp hV⟩

/-- **The `w`-reducts with `TW` bodies are closed under one βη-step.** -/
theorem WT.step {x : ℕ} {P P' : Lambda} (h : WT x P) (hs : betaEtaStep P P') : WT x P' := by
  cases h with
  | wbb hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        have e : Lambda.subst lamB 0 (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) =
            bbPre := by
          simp [Lambda.subst, Lambda.lift, bbPre, lamB]
        rw [e]; exact .wpre hV
      · exact (nf_lamB _ hf').elim
      · exact (nf_lamB _ ha).elim
    · exact .wbb (hV.step ha)
  | @wpre V hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bbPre, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst V 0 (.lam (.app lamB (.app (.var 1) (.var 0)))) =
          .lam (.app lamB (.app (Lambda.lift 1 0 V) (.var 0))) := by
        simp [Lambda.subst, lamB]
      rw [e]; exact .wlam (.wB (compYB hV))
    · rw [step_bbPre hf]; exact .wpre2 hV
    · exact .wpre (hV.step ha)
  | @wpre2 V hV =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bbPre2, Lambda.lam.injEq] at hc
      subst hc
      refine .wlam ?_
      have := TW.wP (base := YB x) (x := x + 1) (i := 1) (i' := 1) (m := 0)
        (T := .app (.var 1) (.var 0)) (compYB hV) (by simp)
      convert this using 3
      simp [Lambda.subst, Lambda.lift, lift_lift_zero_one, xPow]
    · exact (nf_bbPre2 _ hf).elim
    · exact .wpre2 (hV.step ha)
  | wlam hW =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .wlam (hW.step_YB hb)
    · exfalso
      cases hW with
      | wB hV =>
        simp only [Lambda.app.injEq] at hf
        exact hV.ne_var_of YB.ne_var 0 hf.2
      | wP _ _ => simp at hf
      | wK _ => simp at hf

theorem WT.reduces {x : ℕ} {P Q : Lambda} (h : WT x P) (hr : betaEtaReduces P Q) : WT x Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- The reducts of `W q` (`W ∈ WT x`). -/
inductive WqT (x : ℕ) : Lambda → Prop
  | ap {W : Lambda} : WT x W → WqT x (.app (Lambda.lift 1 0 W) (.var 0))
  | body {W : Lambda} : TW (YB x) (x + 1) 1 W → WqT x W

theorem WqT.step {x : ℕ} {P P' : Lambda} (h : WqT x P) (hs : betaEtaStep P P') : WqT x P' := by
  cases h with
  | @ap W hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · obtain ⟨W0, rfl, rfl⟩ := Lambda.lift_eq_lam hc
      rw [subst_var_lift_succ W0 0]
      cases hW with
      | wlam hq => exact .body hq
    · obtain ⟨W', rfl, hW'⟩ := betaEtaStep_lift_inv hf
      exact .ap (hW.step hW')
    · exact (betaEtaStep_var ha).elim
  | body hW => exact .body (hW.step_YB hs)

theorem WqT.reduces {x : ℕ} {P Q : Lambda} (h : WqT x P) (hr : betaEtaReduces P Q) :
    WqT x Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem WqT.ne_var {x : ℕ} {P : Lambda} {n : ℕ} (h : WqT x P) : P ≠ .var n := by
  cases h with
  | ap _ => simp
  | body hW => exact hW.ne_var_YB n

/-- The bodies under `q` of the `s`-reducts. -/
inductive SqT (x : ℕ) : Lambda → Prop
  | mw {W : Lambda} : WqT x W → SqT x (.app lamM W)
  | ww {W Y : Lambda} : WqT x W → SqT x (.app W Y)
  | core {P : Lambda} : TC (YB x) (x + 1) 1 P → SqT x P

theorem SqT.step {x : ℕ} {P P' : Lambda} (h : SqT x P) (hs : betaEtaStep P P') : SqT x P' := by
  cases h with
  | mw hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, ite_eq_left]
      exact .ww hW
    · exact (nf_lamM _ hf).elim
    · exact .mw (hW.step ha)
  | @ww W Y hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hW with
      | ap _ => cases hc
      | body hq => exact .core (hq.fire hc Y)
    · exact .ww (hW.step hf)
    · exact .ww hW
  | core hP => exact .core (hP.step_YB hs)

/-- The reducts of `s = B M W` (`W ∈ WT x`), `x` at index `x`. -/
inductive ST (x : ℕ) : Lambda → Prop
  | sbm {W : Lambda} : WT x W → ST x (.app (.app lamB lamM) W)
  | sbm1 {W : Lambda} : WT x W → ST x (.app bmPre1 W)
  | sbm2 {W : Lambda} : WT x W → ST x (.app bmPre2 W)
  | slam {S : Lambda} : SqT x S → ST x (.lam S)
  | sv {V : Lambda} : YG x 0 V → ST x V
  | seta {f : Lambda} : WqT x (Lambda.lift 1 0 f) → ST x f

/-- **The `s`-reducts are closed under one βη-step.** -/
theorem ST.step {x : ℕ} {P P' : Lambda} (h : ST x P) (hs : betaEtaStep P P') : ST x P' := by
  cases h with
  | sbm hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_M]; exact .sbm1 hW
      · exact (nf_lamB _ hf').elim
      · exact (nf_lamM _ ha).elim
    · exact .sbm (hW.step ha)
  | @sbm1 W hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre1, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst W 0 (.lam (.app lamM (.app (.var 1) (.var 0)))) =
          .lam (.app lamM (.app (Lambda.lift 1 0 W) (.var 0))) := by
        simp [Lambda.subst, lamM]
      rw [e]; exact .slam (.mw (.ap hW))
    · rw [step_bmPre1 hf]; exact .sbm2 hW
    · exact .sbm1 (hW.step ha)
  | @sbm2 W hW =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [bmPre2, Lambda.lam.injEq] at hc
      subst hc
      have e : Lambda.subst W 0
          (.lam (.app (.app (.var 1) (.var 0)) (.app (.var 1) (.var 0)))) =
          .lam (.app (.app (Lambda.lift 1 0 W) (.var 0)) (.app (Lambda.lift 1 0 W) (.var 0))) := by
        simp [Lambda.subst]
      rw [e]; exact .slam (.ww (.ap hW))
    · exact (nf_bmPre2 _ hf).elim
    · exact .sbm2 (hW.step ha)
  | slam hS =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, rfl⟩
    · exact .slam (hS.step hb)
    · cases hS with
      | mw hW =>
        simp only [Lambda.app.injEq] at hf
        exact (hW.ne_var hf.2).elim
      | ww hW =>
        simp only [Lambda.app.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact .seta hW
      | core hP =>
        generalize hone : (1 : ℤ) = one at hP
        cases hP with
        | base hb =>
          obtain ⟨n, rfl, hb⟩ := hb
          cases hb with
          | q hR => simp only [Lambda.app.injEq] at hf; cases hR <;> simp [bym1, bym2, bym3] at hf
          | m hR => simp only [Lambda.app.injEq] at hf; cases hR <;> simp [bym1, bym2, bym3] at hf
          | rr _ hR => simp only [Lambda.app.injEq] at hf; cases hR <;> simp [bym1, bym2, bym3] at hf
          | @comp i' R hR =>
            simp only [Lambda.app.injEq] at hf
            obtain rfl := Lambda.lift_one_injective 0 hf.1
            have : i' = 0 := by omega
            subst this
            exact .sv hR
        | bx hP =>
          simp only [Lambda.app.injEq] at hf
          exact (hP.ne_var_of YB.ne_var 0 hf.2).elim
        | bx1 hP =>
          simp only [Lambda.app.injEq] at hf
          exact (hP.ne_var_of YB.ne_var 0 hf.2).elim
        | rq _ _ => simp at hf
  | sv hV => exact .sv (hV.step hs)
  | seta hW => exact .seta (hW.reduces (betaEtaStep_lift_reduces hs))

theorem ST.reduces {x : ℕ} {P Q : Lambda} (h : ST x P) (hr : betaEtaReduces P Q) : ST x Q := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

/-- **`s = B M w` is in the grammar.** -/
theorem ST.of_h5s (x : ℕ) : ST x (toLam (h5s x)) :=
  .sbm (.wbb (.bm .bb))

/-- Every βη-reduct of `s` is in the grammar. -/
theorem ST.of_reduces {x : ℕ} {P : Lambda} (hr : betaEtaReduces (toLam (h5s x)) P) : ST x P :=
  (ST.of_h5s x).reduces hr

end TLCA4
