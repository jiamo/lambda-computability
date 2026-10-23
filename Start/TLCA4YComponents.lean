import Start.TLCA4XChain
import Start.TLCA4QComponents

/-!
# TLCA open problem 4: the reducts of `B y` and `B y q` for `y = B x`
(row M20-TLCA4-Q-NOT-FIXPOINT; series V, big round, run 3, item A1)

In the grammar `TLCA4.TGram` of the components of `T x`, the variable `x` occurs through the
reducts of `B x` (`TLCA4.BxR`) and of `B x q` (`TLCA4.BxqR`).  The components of `Q x` are those of
`T y` at `y = B x`, so the corresponding families are the reducts of `B y` and of `B y q` with
`y = B x`.  This module gives them explicitly (with `x` at de Bruijn index `y`):

* `ByR y` — the five reducts of `B (B x)`: `B (B x)`, `B (λab. x (a b))`, `λgz. B x (g z)`,
  `λgz. (λab. x (a b)) (g z)` and the normal form `λgzw. x (g z w)`;
* `ByqR y` — the eight reducts of `B (B x) q` (`q` the variable `0`);
* **`ByR.step`**, **`ByqR.step`** — both families are closed under one βη-step;
* `ByR.reduces`, `ByqR.reduces` — and under βη-reduction;
* `ByR.lift` — `R ∈ ByR y` gives `R q ∈ ByqR (y + 1)`; `ByqR.ne_var` — no member is a variable;
* `ByR.of_toLam` — `B (B x)` itself is a member.

This is the first part of step (2) of the design for `Q_not_fixedPoint` (the `y`-level grammar):
the analogues of `BxR` and `BxqR`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- `B (B x)`. -/
def bbx (y : ℕ) : Lambda := .app lamB (.app lamB (.var y))

/-- `B (λab. x (a b))`. -/
def bbpre (y : ℕ) : Lambda := .app lamB (bxPre y)

/-- `λgz. B x (g z)`. -/
def byl1 (y : ℕ) : Lambda := .lam (.lam (.app (.app lamB (.var (y + 2))) (.app (.var 1) (.var 0))))

/-- `λgz. (λab. x (a b)) (g z)`. -/
def byl2 (y : ℕ) : Lambda := .lam (.lam (.app (bxPre (y + 2)) (.app (.var 1) (.var 0))))

/-- `λgzw. x (g z w)`, the normal form of `B (B x)`. -/
def byl3 (y : ℕ) : Lambda :=
  .lam (.lam (.lam (.app (.var (y + 3)) (.app (.app (.var 2) (.var 1)) (.var 0)))))

/-- `λz. B x (q z)`. -/
def bym1 (y : ℕ) : Lambda := .lam (.app (.app lamB (.var (y + 1))) (.app (.var 1) (.var 0)))

/-- `λz. (λab. x (a b)) (q z)`. -/
def bym2 (y : ℕ) : Lambda := .lam (.app (bxPre (y + 1)) (.app (.var 1) (.var 0)))

/-- `λzw. x (q z w)`, the normal form of `B (B x) q`. -/
def bym3 (y : ℕ) : Lambda :=
  .lam (.lam (.app (.var (y + 2)) (.app (.app (.var 2) (.var 1)) (.var 0))))

/-- The reducts of `B y` for `y = B x` (`x` at index `y`). -/
inductive ByR (y : ℕ) : Lambda → Prop
  | bb : ByR y (bbx y)
  | bpre : ByR y (bbpre y)
  | l1 : ByR y (byl1 y)
  | l2 : ByR y (byl2 y)
  | l3 : ByR y (byl3 y)

/-- The reducts of `B y q` for `y = B x` (`x` at index `y`, `q` at index `0`). -/
inductive ByqR (y : ℕ) : Lambda → Prop
  | bb : ByqR y (.app (bbx y) (.var 0))
  | bpre : ByqR y (.app (bbpre y) (.var 0))
  | l1 : ByqR y (.app (byl1 y) (.var 0))
  | l2 : ByqR y (.app (byl2 y) (.var 0))
  | l3 : ByqR y (.app (byl3 y) (.var 0))
  | m1 : ByqR y (bym1 y)
  | m2 : ByqR y (bym2 y)
  | m3 : ByqR y (bym3 y)

/-! ### Normal forms -/

theorem nf_app_app2_var {i j k l : ℕ} :
    BetaEtaNf (.app (.var i) (.app (.app (.var j) (.var k)) (.var l))) :=
  betaEtaNf_app_var (betaEtaNf_app_of (betaEtaNf_app_var (betaEtaNf_var _)) (betaEtaNf_var _)
    (by intro c h; simp at h))

theorem nf_byl3 (y : ℕ) : BetaEtaNf (byl3 y) := by
  unfold byl3
  refine betaEtaNf_lam (betaEtaNf_lam (betaEtaNf_lam nf_app_app2_var ?_) ?_) ?_ <;>
    intro f h <;> simp at h

theorem nf_bym3 (y : ℕ) : BetaEtaNf (bym3 y) := by
  unfold bym3
  refine betaEtaNf_lam (betaEtaNf_lam nf_app_app2_var ?_) ?_ <;> intro f h <;> simp at h

/-! ### Closure under steps -/

theorem nf_app_var_var' {i j : ℕ} {u : Lambda} (h : betaEtaStep (.app (.var i) (.var j)) u) :
    False := nf_app_var_var _ h

theorem ByR.step {y : ℕ} {R R' : Lambda} (h : ByR y R) (hs : betaEtaStep R R') : ByR y R' := by
  cases h with
  | bb =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, rfl⟩
    · simp only [lamB, Lambda.lam.injEq] at hc
      subst hc
      have : Lambda.subst (.app lamB (.var y)) 0
          (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) = byl1 y := by
        simp [Lambda.subst, Lambda.lift, byl1, lamB]
      rw [this]; exact .l1
    · exact (nf_lamB _ hf).elim
    · rcases betaEtaStep_app_cases ha with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha', _⟩
      · simp only [lamB, Lambda.lam.injEq] at hc
        subst hc
        rw [step_lamB_var]; exact .bpre
      · exact (nf_lamB _ hf).elim
      · exact (betaEtaStep_var ha').elim
  | bpre =>
    rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
    · simp only [lamB, Lambda.lam.injEq] at hc
      subst hc
      have : Lambda.subst (bxPre y) 0
          (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) = byl2 y := by
        simp [Lambda.subst, Lambda.lift, byl2, bxPre]
      rw [this]; exact .l2
    · exact (nf_lamB _ hf).elim
    · exact (nf_bxPre y _ ha).elim
  | l1 =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, _⟩
    · rcases betaEtaStep_lam_cases hb with ⟨b'', hb', rfl⟩ | ⟨f, hf, _⟩
      · rcases betaEtaStep_app_cases hb' with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
        · cases hc
        · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
          · simp only [lamB, Lambda.lam.injEq] at hc
            subst hc
            rw [step_lamB_var]; exact .l2
          · exact (nf_lamB _ hf').elim
          · exact (betaEtaStep_var ha).elim
        · exact (nf_app_var_var' ha).elim
      · simp at hf
    · simp at hf
  | l2 =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, _⟩
    · rcases betaEtaStep_lam_cases hb with ⟨b'', hb', rfl⟩ | ⟨f, hf, _⟩
      · rcases betaEtaStep_app_cases hb' with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
        · simp only [bxPre, Lambda.lam.injEq] at hc
          subst hc
          have : Lambda.subst (.app (.var 1) (.var 0)) 0
              (.lam (.app (.var (y + 2 + 2)) (.app (.var 1) (.var 0)))) =
              .lam (.app (.var (y + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))) := by
            simp [Lambda.subst, Lambda.lift]
          rw [this]; exact .l3
        · exact (nf_bxPre _ _ hf).elim
        · exact (nf_app_var_var' ha).elim
      · simp at hf
    · simp at hf
  | l3 => exact (nf_byl3 y _ hs).elim

theorem ByR.app_q {y : ℕ} {R : Lambda} (h : ByR y R) : ByqR y (.app R (.var 0)) := by
  cases h with
  | bb => exact .bb
  | bpre => exact .bpre
  | l1 => exact .l1
  | l2 => exact .l2
  | l3 => exact .l3

/-- A β-step at the root of `R q` with `R ∈ ByR y`. -/
theorem ByR.beta_q {y : ℕ} {R c : Lambda} (h : ByR y R) (hc : R = .lam c) :
    ByqR y (Lambda.subst (.var 0) 0 c) := by
  cases h with
  | bb => simp [bbx] at hc
  | bpre => simp [bbpre] at hc
  | l1 =>
    simp only [byl1, Lambda.lam.injEq] at hc
    subst hc
    have : Lambda.subst (.var 0) 0
        (.lam (.app (.app lamB (.var (y + 2))) (.app (.var 1) (.var 0)))) = bym1 y := by
      simp [Lambda.subst, Lambda.lift, bym1, lamB]
    rw [this]; exact .m1
  | l2 =>
    simp only [byl2, Lambda.lam.injEq] at hc
    subst hc
    have : Lambda.subst (.var 0) 0
        (.lam (.app (bxPre (y + 2)) (.app (.var 1) (.var 0)))) = bym2 y := by
      simp [Lambda.subst, Lambda.lift, bym2, bxPre]
    rw [this]; exact .m2
  | l3 =>
    simp only [byl3, Lambda.lam.injEq] at hc
    subst hc
    have : Lambda.subst (.var 0) 0
        (.lam (.lam (.app (.var (y + 3)) (.app (.app (.var 2) (.var 1)) (.var 0))))) =
        bym3 y := by
      simp [Lambda.subst, Lambda.lift, bym3]
    rw [this]; exact .m3

theorem ByR.step_q {y : ℕ} {R u : Lambda} (h : ByR y R) (hs : betaEtaStep (.app R (.var 0)) u) :
    ByqR y u := by
  rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
  · exact h.beta_q hc
  · exact (h.step hf).app_q
  · exact (betaEtaStep_var ha).elim

/-- **The reducts of `B y q` are closed under one βη-step.** -/
theorem ByqR.step {y : ℕ} {R R' : Lambda} (h : ByqR y R) (hs : betaEtaStep R R') :
    ByqR y R' := by
  cases h with
  | bb => exact ByR.bb.step_q hs
  | bpre => exact ByR.bpre.step_q hs
  | l1 => exact ByR.l1.step_q hs
  | l2 => exact ByR.l2.step_q hs
  | l3 => exact ByR.l3.step_q hs
  | m1 =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, _⟩
    · rcases betaEtaStep_app_cases hb with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, _⟩
      · cases hc
      · rcases betaEtaStep_app_cases hf with ⟨c, hc, rfl⟩ | ⟨f'', hf', _⟩ | ⟨a', ha, _⟩
        · simp only [lamB, Lambda.lam.injEq] at hc
          subst hc
          rw [step_lamB_var]; exact .m2
        · exact (nf_lamB _ hf').elim
        · exact (betaEtaStep_var ha).elim
      · exact (nf_app_var_var' ha).elim
    · simp at hf
  | m2 =>
    rcases betaEtaStep_lam_cases hs with ⟨b', hb, rfl⟩ | ⟨f, hf, _⟩
    · rcases betaEtaStep_app_cases hb with ⟨c, hc, rfl⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
      · simp only [bxPre, Lambda.lam.injEq] at hc
        subst hc
        have : Lambda.subst (.app (.var 1) (.var 0)) 0
            (.lam (.app (.var (y + 1 + 2)) (.app (.var 1) (.var 0)))) =
            .lam (.app (.var (y + 2)) (.app (.app (.var 2) (.var 1)) (.var 0))) := by
          simp [Lambda.subst, Lambda.lift]
        rw [this]; exact .m3
      · exact (nf_bxPre _ _ hf).elim
      · exact (nf_app_var_var' ha).elim
    · simp at hf
  | m3 => exact (nf_bym3 y _ hs).elim

theorem ByR.reduces {y : ℕ} {R R' : Lambda} (h : ByR y R) (hr : betaEtaReduces R R') :
    ByR y R' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem ByqR.reduces {y : ℕ} {R R' : Lambda} (h : ByqR y R) (hr : betaEtaReduces R R') :
    ByqR y R' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem ByqR.ne_var {y j : ℕ} {R : Lambda} (h : ByqR y R) : R ≠ .var j := by
  cases h <;> simp [bym1, bym2, bym3]

/-- Applying a reduct of `B y` to the fresh variable `q`. -/
theorem ByR.lift {y : ℕ} {R : Lambda} (h : ByR y R) :
    ByqR (y + 1) (.app (Lambda.lift 1 0 R) (.var 0)) := by
  cases h with
  | bb =>
    have : Lambda.lift 1 0 (bbx y) = bbx (y + 1) := by simp [bbx, Lambda.lift, lamB]
    rw [this]; exact .bb
  | bpre =>
    have : Lambda.lift 1 0 (bbpre y) = bbpre (y + 1) := by simp [bbpre, bxPre, Lambda.lift, lamB]
    rw [this]; exact .bpre
  | l1 =>
    have : Lambda.lift 1 0 (byl1 y) = byl1 (y + 1) := by simp [byl1, Lambda.lift, lamB]
    rw [this]; exact .l1
  | l2 =>
    have : Lambda.lift 1 0 (byl2 y) = byl2 (y + 1) := by simp [byl2, bxPre, Lambda.lift]
    rw [this]; exact .l2
  | l3 =>
    have : Lambda.lift 1 0 (byl3 y) = byl3 (y + 1) := by simp [byl3, Lambda.lift]
    rw [this]; exact .l3

/-- `B (B x)`, the translation of the combinatory term `B (B x)`, is a member. -/
theorem ByR.of_toLam (x : ℕ) : ByR x (toLam (app B (app B (var x)))) := .bb

/-- Every reduct of `B (B x)` is in `ByR`. -/
theorem ByR.of_reduces {x : ℕ} {R : Lambda}
    (hr : betaEtaReduces (toLam (app B (app B (var x)))) R) : ByR x R :=
  (ByR.of_toLam x).reduces hr

end TLCA4
