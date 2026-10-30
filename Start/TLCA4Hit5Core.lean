import Start.TLCA4Hit5Grammar

/-!
# TLCA open problem 4: the cores of `hit5` and their closure under βη
(row M20-TLCA4-BETAETA; big round 2, run 1, item A1)

The stage `x^{tri n} (s (uⁿ s) Wₙ)` of `hit5 x` has the core `s (uⁿ s)` (components of indices
`0` and `n`) and the tail `Wₙ`.  This module defines the core family `H5Core x K` with the
conserved quantity `K`, and proves the step lemma that the plan names as the first missing
lemma of item A1:

* `H5Core x K n` — `P Q` (components of indices `i`, `j`, `K + i = tri j + n`), `M Q`
  (`K + j = tri j + n`), and the two forms that the `w`-layer creates, `M (W Q)` and `(W Q) Y`
  with `W` a `w`-reduct (`K + j = tri (j + 1) + n - 1`);
* `ByqR.substH` — substituting a component of index `j` into a reduct of `B y q` gives a
  component of index `j + 1`;
* `HC.toTC` — the chains of the grammar are chains with arbitrary tails over its cores;
* `YBase.substH`, `HB.substH`, **`HC.substH`** — substituting a component for `q` in a chain
  under `q` gives a top-level chain over `Ext (H5Core x) x K`, with the height shifted;
* **`H5Core.step`** — every βη-step of a core is a chain over `Ext (H5Core x) x K`;
* `H5Core.not_lam`, **`H5Ext.step`** — hence (`Ext.step`) the extension is closed under βη;
* `hit5_reduces_shape` — `hit5 x` βη-reduces to a term of the shape `AShape` over the extension.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- **Substituting a component for `q` in a reduct of `B y q`** gives a component of the next
index. -/
theorem ByqR.substH {x j : ℕ} {R Q : Lambda} (hR : ByqR (x + 1) R) (hQ : HG x j Q) :
    HG x (j + 1) (Lambda.subst Q 0 R) := by
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
    rw [this]; exact .lam (.bx (.base (.comp hQ rfl))) (by push_cast; ring)
  | m2 =>
    have : Lambda.subst Q 0 (bym2 (x + 1)) =
        .lam (.app (bxPre (x + 1)) (.app (Lambda.lift 1 0 Q) (.var 0))) := by
      simp [Lambda.subst, bym2, bxPre]
    rw [this]; exact .lam (.bx1 (.base (.comp hQ rfl))) (by push_cast; ring)
  | m3 =>
    have : Lambda.subst Q 0 (bym3 (x + 1)) =
        .lam (.lam (xPow (.var (x + 2)) 1
          (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 Q) (.var 0))) (.var 0)))) := by
      simp [Lambda.subst, bym3, xPow, Lambda.lift, lift_lift_zero_one]
    rw [this]; exact .lam (.rq (m := 1) (.base (.comp hQ rfl)) rfl) (by push_cast; ring)

/-- The chains of the grammar are chains with arbitrary tails over its cores. -/
theorem HC.toTC {x : ℕ} {n : ℤ} {C : Lambda} (h : HC x n C) : TC (HB x) (x + 1) n C :=
  match h with
  | .base hb => .base hb
  | .bx h' => .bx (HC.toTC h')
  | .bx1 h' => .bx1 (HC.toTC h')
  | .rq h' hm => .rq (HC.toTC h') hm

/-- The cores of the components of `hit5 x`, with the conserved quantity `K`. -/
inductive H5Core (x : ℕ) (K : ℤ) : ℤ → Lambda → Prop
  | pq {i j : ℕ} {n : ℤ} {P Q : Lambda} : HG x i P → HG x j Q →
      K + i = (tri j : ℤ) + n → H5Core x K n (.app P Q)
  | mq {j : ℕ} {n : ℤ} {Q : Lambda} : HG x j Q → K + j = (tri j : ℤ) + n →
      H5Core x K n (.app lamM Q)
  | mwq {j : ℕ} {n : ℤ} {W Q : Lambda} : WT x W → HG x j Q →
      K + j = (tri (j + 1) : ℤ) + n - 1 → H5Core x K n (.app lamM (.app W Q))
  | wqy {j : ℕ} {n : ℤ} {W Q Y : Lambda} : WT x W → HG x j Q →
      K + j = (tri (j + 1) : ℤ) + n - 1 → H5Core x K n (.app (.app W Q) Y)

theorem tri_succ_int (j : ℕ) : (tri (j + 1) : ℤ) = tri j + j + 1 := by
  simp only [tri]; push_cast; ring

theorem subst_zero_var0 (Q : Lambda) : Lambda.subst Q 0 (.var 0) = Q := by
  simp [Lambda.subst]

theorem subst_lamM (Q : Lambda) (k : ℕ) : Lambda.subst Q k lamM = lamM := by
  simp [Lambda.subst, lamM]

/-- Substituting a component for `q` in a core of `YBase` (the cores of `v`-chains). -/
theorem YBase.substH {x : ℕ} {K s : ℤ} {j : ℕ} {Q : Lambda} (hQ : HG x j Q)
    (hK : K + j = (tri (j + 1) : ℤ) + s) {k : ℕ} {P : Lambda} (h : YBase x k P) :
    H5Core x K ((k : ℤ) + s) (Lambda.subst Q 0 P) := by
  cases h with
  | q hR =>
    simp only [Lambda.subst, ite_eq_left]
    exact .pq hQ (hR.substH hQ) (by push_cast at hK ⊢; omega)
  | m hR =>
    simp only [Lambda.subst, subst_lamM]
    exact .mq (hR.substH hQ) (by push_cast at hK ⊢; omega)
  | rr h1 h2 =>
    simp only [Lambda.subst]
    exact .pq (h1.substH hQ) (h2.substH hQ) (by push_cast at hK ⊢; omega)
  | comp hR =>
    simp only [Lambda.subst, Lambda.subst_lift, ite_eq_left]
    refine .pq (.yg hR) hQ ?_
    rw [tri_succ_int] at hK
    push_cast; omega

theorem YB.substH {x : ℕ} {K s : ℤ} {j : ℕ} {Q : Lambda} (hQ : HG x j Q)
    (hK : K + j = (tri (j + 1) : ℤ) + s) {i : ℤ} {P : Lambda} (h : YB x i P) :
    H5Core x K (i + s) (Lambda.subst Q 0 P) := by
  obtain ⟨k, rfl, hb⟩ := h
  exact hb.substH hQ hK

/-- Substituting a component for `q` in a core of the grammar. -/
theorem HB.substH {x : ℕ} {K s : ℤ} {j : ℕ} {Q : Lambda} (hQ : HG x j Q)
    (hK : K + j = (tri (j + 1) : ℤ) + s) {i : ℤ} {P : Lambda} (h : HB x i P) :
    Ext (H5Core x) x K (i + s) (Lambda.subst Q 0 P) := by
  cases h with
  | q hR =>
    simp only [Lambda.subst, ite_eq_left]
    exact ⟨0, .pq hQ (hR.substH hQ) (by omega)⟩
  | m hR =>
    simp only [Lambda.subst, subst_lamM]
    exact ⟨0, .mq (hR.substH hQ) (by push_cast at hK ⊢; omega)⟩
  | rr h1 h2 =>
    simp only [Lambda.subst]
    exact ⟨0, .pq (h1.substH hQ) (h2.substH hQ) (by push_cast at hK ⊢; omega)⟩
  | comp hR hn =>
    simp only [Lambda.subst, Lambda.subst_lift, ite_eq_left]
    refine ⟨0, .pq hR hQ ?_⟩
    rw [tri_succ_int] at hK
    subst hn
    omega
  | mw hW =>
    cases hW with
    | @ap W hW =>
      simp only [Lambda.subst, subst_lamM, Lambda.subst_lift, ite_eq_left]
      exact ⟨0, .mwq hW hQ (by omega)⟩
    | body hT =>
      simp only [Lambda.subst, subst_lamM]
      exact ⟨1, .inr (.inl ⟨_, rfl, hT.subst_gen (fun hb => hb.substH hQ hK)⟩)⟩
  | ww hW =>
    cases hW with
    | @ap W hW =>
      simp only [Lambda.subst, Lambda.subst_lift, ite_eq_left]
      exact ⟨0, .wqy hW hQ (by omega)⟩
    | body hT =>
      simp only [Lambda.subst]
      exact ⟨1, .inr (.inr ⟨_, _, rfl, hT.subst_gen (fun hb => hb.substH hQ hK)⟩)⟩

/-- **Substituting a component for `q` in a chain under `q`** gives a top-level chain over the
extended cores. -/
theorem HC.substH {x : ℕ} {K s : ℤ} {j : ℕ} {Q : Lambda} (hQ : HG x j Q)
    (hK : K + j = (tri (j + 1) : ℤ) + s) {c : ℤ} {C : Lambda} (h : HC x c C) :
    TC (Ext (H5Core x) x K) x (c + s) (Lambda.subst Q 0 C) :=
  h.toTC.subst_gen (fun hb => hb.substH hQ hK)

theorem H5Core.not_lam {x : ℕ} {K n : ℤ} {c : Lambda} (h : H5Core x K n (.lam c)) : False := by
  cases h

/-- Firing a `w`-reduct on a component: `W Q` with `W = λq. Wq` gives a two-argument chain. -/
theorem WT.fire_subst {x : ℕ} {K s : ℤ} {j : ℕ} {W c Q : Lambda} (hW : WT x W) (e : W = .lam c)
    (hQ : HG x j Q) (hK : K + j = (tri (j + 1) : ℤ) + s) :
    TW (H5Core x K) x (1 + s) (Lambda.subst Q 0 c) := by
  cases hW with
  | wlam hT =>
    simp only [Lambda.lam.injEq] at e
    subst e
    exact hT.subst_gen (fun hb => hb.substH hQ hK)
  | wbb _ => cases e
  | wpre _ => cases e
  | wpre2 _ => cases e

/-- **Every βη-step of a core of `hit5` is a chain over the extended cores.** -/
theorem H5Core.step {x : ℕ} {K n : ℤ} {P P' : Lambda} (h : H5Core x K n P)
    (hs : betaEtaStep P P') : TC (Ext (H5Core x) x K) x n P' := by
  cases h with
  | @pq i j _ P Q hP hQ hK =>
    rcases betaEtaStep_app_cases hs with ⟨c, rfl, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · have hc := hP.fire_q
      have := hc.substH (K := K) (s := K + j - tri (j + 1)) hQ (by ring)
      rwa [show (i : ℤ) + 1 + (K + j - tri (j + 1)) = n by rw [tri_succ_int]; omega] at this
    · exact .base ⟨0, .pq (hP.step hf) hQ hK⟩
    · exact .base ⟨0, .pq hP (hQ.step ha) hK⟩
  | mq hQ hK =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, ite_eq_left]
      exact .base ⟨0, .pq hQ hQ hK⟩
    · exact (nf_lamM _ hf).elim
    · exact .base ⟨0, .mq (hQ.step ha) hK⟩
  | @mwq j _ W Q hW hQ hK =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · simp only [lamM, Lambda.lam.injEq] at hc
      subst hc
      simp only [Lambda.subst, ite_eq_left]
      exact .base ⟨0, .wqy hW hQ hK⟩
    · exact (nf_lamM _ hf).elim
    · rcases betaEtaStep_app_cases ha with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha', rfl⟩
      · have := hW.fire_subst hc hQ (K := K) (s := n - 1) (by omega)
        rw [show 1 + (n - 1) = n by ring] at this
        exact .base ⟨1, .inr (.inl ⟨_, rfl, this⟩)⟩
      · exact .base ⟨0, .mwq (hW.step hf) hQ hK⟩
      · exact .base ⟨0, .mwq hW (hQ.step ha') hK⟩
  | @wqy j _ W Q Y hW hQ hK =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · cases hc
    · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', rfl⟩ | ⟨a', ha', rfl⟩
      · have := hW.fire_subst hc hQ (K := K) (s := n - 1) (by omega)
        rw [show 1 + (n - 1) = n by ring] at this
        exact .base ⟨1, .inr (.inr ⟨_, _, rfl, this⟩)⟩
      · exact .base ⟨0, .wqy (hW.step hf') hQ hK⟩
      · exact .base ⟨0, .wqy hW (hQ.step ha') hK⟩
    · exact .base ⟨0, .wqy hW hQ hK⟩

/-- **The extended cores of `hit5` are closed under one βη-step.** -/
theorem H5Ext.step {x : ℕ} {K n : ℤ} {P P' : Lambda} (h : Ext (H5Core x) x K n P)
    (hs : betaEtaStep P P') : TC (Ext (H5Core x) x K) x n P' :=
  Ext.step H5Core.step H5Core.not_lam h hs

/-- **`hit5 x` reduces to a term of the shape** over the extended cores: its stage `0`,
`s s (M s)`, with the core `s s` (indices `0, 0`, `K = 0`) and the tail `M s`. -/
theorem hit5_reduces_shape (x : ℕ) :
    ∃ N, betaEtaReduces (toLam (actList hit5 (var x))) N ∧ AShape (Ext (H5Core x) x) x N :=
  ⟨_, .of_reduces (hit5_stage_betaEta x 0),
    ⟨0, 0, _, _, rfl, .base ⟨0, .pq (.st (ST.of_h5s x)) (HG.of_h5A x 0) (by simp [tri])⟩⟩⟩

/-- **`hit5` is not a βη fixed point, given the hypotheses of the shape argument for its
extended cores** (`TailCores`: closure under βη, which `H5Ext.step` proves, and the syntactic
fields, of which `unique` is the open one). -/
theorem hit5_not_fixedPoint_of_tailCores (x : ℕ) (hc : TailCores (Ext (H5Core x) x) x) :
    ¬ Lambda.betaEtaConv (toLam (actList hit5 (var x)))
      (.app (.var x) (toLam (actList hit5 (var x)))) := by
  obtain ⟨N, hN, hS⟩ := hit5_reduces_shape x
  exact not_fixedPoint_of_ashape hc hN hS

end TLCA4
