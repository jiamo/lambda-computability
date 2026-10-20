/-
**The unpairing macro for structured counter programs** — task `M25-KCM-UNIVERSAL`
(round 10, part B1).

`Nat.unpair (k + 1)` is obtained from `Nat.unpair k` by two comparisons (`unpair_succ`): the
enumeration of `Nat.pair` walks `(0,m), …, (m-1,m)` and then `(m,0), …, (m,m)`.  The macro
`unpairM n a b s` counts up to `r n` along this enumeration, using the comparison loop
`ltFlag` at each step:

* `Minsky.Prog.unpair_succ` — the successor rule;
* `Minsky.Prog.exec_unpairStep` — one step of the walk;
* `Minsky.Prog.exec_unpairM` — **correctness of the unpairing macro**:
  `r a, r b := Nat.unpair (r n)`, scratch registers zero before and after.
-/

import Start.MinskyProgMacros

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Prog

open Function

/-- The successor of a pair in the enumeration of `Nat.pair`. -/
def unpairNext (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.1 < p.2 then (if p.1 + 1 < p.2 then (p.1 + 1, p.2) else (p.2, 0))
  else (if p.2 < p.1 then (p.1, p.2 + 1) else (0, p.1 + 1))

/-- **The successor rule of `Nat.unpair`.** -/
theorem unpair_succ (k : ℕ) : Nat.unpair (k + 1) = unpairNext (Nat.unpair k) := by
  rcases h : Nat.unpair k with ⟨a, b⟩
  have hk : Nat.pair a b = k := by
    have := Nat.pair_unpair k; rw [h] at this; exact this
  suffices Nat.pair (unpairNext (a, b)).1 (unpairNext (a, b)).2 = k + 1 by
    rw [← this, Nat.unpair_pair]
  subst hk
  unfold unpairNext
  simp only
  split_ifs with h₁ h₂ h₃
  · simp only [Nat.pair, if_pos h₂, if_pos h₁]; ring
  · have : a + 1 = b := by omega
    subst this
    simp only [Nat.pair, if_pos h₁, Nat.not_lt_zero, if_false]; ring
  · simp only [Nat.pair, if_neg h₁, if_neg (show ¬ a < b + 1 by omega)]; ring
  · have : a = b := by omega
    subst this
    simp only [Nat.pair, if_neg h₁, if_pos (show 0 < a + 1 by omega)]; ring

/-- The branch `r a < r b` of a step. -/
def unpairLT (a b s : ℕ) : Prog :=
  .seq (copy a (s + 5) s) (.seq (.inc (s + 5)) (.seq (ltFlag (s + 5) b (s + 6) (s + 2) (s + 3) s)
    (.seq (clear (s + 5)) (ite (s + 6) (s + 7) (.inc a) (.seq (clear a) (addTo b a))))))

/-- The branch `r b ≤ r a` of a step. -/
def unpairGE (a b s : ℕ) : Prog :=
  .seq (ltFlag b a (s + 8) (s + 2) (s + 3) s)
    (ite (s + 8) (s + 9) (.inc b) (.seq (clear b) (.seq (addTo a b) (.inc b))))

/-- One step of the walk: `(r a, r b) := unpairNext (r a, r b)`. -/
def unpairStep (a b s : ℕ) : Prog :=
  .seq (ltFlag a b (s + 1) (s + 2) (s + 3) s) (ite (s + 1) (s + 4) (unpairLT a b s) (unpairGE a b s))

theorem exec_unpairLT {a b s : ℕ} (hab : a ≠ b) (ha : a < s) (hb : b < s) (r : ℕ → ℕ)
    (hr : ∀ j, s ≤ j → r j = 0) (hlt : r a < r b) :
    Exec (unpairLT a b s) r
      (update (update r a (unpairNext (r a, r b)).1) b (unpairNext (r a, r b)).2) := by
  have h0 := hr s le_rfl
  have h2 := hr (s + 2) (by omega)
  have h3 := hr (s + 3) (by omega)
  have h5 := hr (s + 5) (by omega)
  have h6 := hr (s + 6) (by omega)
  have h7 := hr (s + 7) (by omega)
  have e₁ := exec_copy (i := a) (j := s + 5) (t := s) (by omega) (by omega) (by omega) r h0
  set r₁ := update r (s + 5) (r (s + 5) + r a) with hr₁
  have e₂ : Exec (.inc (s + 5)) r₁ (update r₁ (s + 5) (r₁ (s + 5) + 1)) := .inc
  set r₂ := update r₁ (s + 5) (r₁ (s + 5) + 1) with hr₂
  have e₃ := exec_ltFlag (a := s + 5) (b := b) (f := s + 6) (s₁ := s + 2) (s₂ := s + 3) (t := s)
    (by simp; omega) r₂ (by simp only [hr₂, hr₁]; upd_val) (by simp only [hr₂, hr₁]; upd_val)
    (by simp only [hr₂, hr₁]; upd_val)
  set r₃ := update r₂ (s + 6) (r₂ (s + 6) + if r₂ (s + 5) < r₂ b then 1 else 0) with hr₃
  have e₄ := exec_clear (s + 5) r₃
  set r₄ := update r₃ (s + 5) 0 with hr₄
  have v5 : r₂ (s + 5) = r a + 1 := by simp only [hr₂, hr₁]; upd_val
  have vb : r₂ b = r b := by simp only [hr₂, hr₁]; upd_val
  have v62 : r₂ (s + 6) = 0 := by simp only [hr₂, hr₁]; upd_val
  refine .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ ?_)))
  by_cases h₂ : r a + 1 < r b
  · have v6 : r₄ (s + 6) = 1 := by
      simp only [hr₄, hr₃, v5, vb, v62, if_pos h₂]; upd_val
    have e₅ : Exec (.inc a) (update r₄ (s + 6) 0)
        (update (update r₄ (s + 6) 0) a (update r₄ (s + 6) 0 a + 1)) := .inc
    refine (exec_ite_pos (by omega) (by omega) (by simp only [hr₄, hr₃, hr₂, hr₁]; upd_val) e₅
      (by upd_val) (by simp only [hr₄, hr₃, hr₂, hr₁]; upd_val)).congr rfl ?_
    simp only [unpairNext, if_pos hlt, if_pos h₂, hr₄, hr₃, hr₂, hr₁]
    upd_tac
  · have v6 : r₄ (s + 6) = 0 := by
      simp only [hr₄, hr₃, v5, vb, v62, if_neg h₂]; upd_val
    have e₅ := exec_clear a r₄
    have e₆ := exec_addTo (i := b) (j := a) (Ne.symm hab) (update r₄ a 0)
    refine (exec_ite_neg (by omega) v6 (by simp only [hr₄, hr₃, hr₂, hr₁]; upd_val) (.seq e₅ e₆)
      (by simp only [hr₄, hr₃, hr₂, hr₁]; upd_val)).congr rfl ?_
    simp only [unpairNext, if_pos hlt, if_neg h₂, hr₄, hr₃, hr₂, hr₁]
    upd_tac

theorem exec_unpairGE {a b s : ℕ} (hab : a ≠ b) (ha : a < s) (hb : b < s) (r : ℕ → ℕ)
    (hr : ∀ j, s ≤ j → r j = 0) (hge : ¬ r a < r b) :
    Exec (unpairGE a b s) r
      (update (update r a (unpairNext (r a, r b)).1) b (unpairNext (r a, r b)).2) := by
  have h0 := hr s le_rfl
  have h2 := hr (s + 2) (by omega)
  have h3 := hr (s + 3) (by omega)
  have h8 := hr (s + 8) (by omega)
  have h9 := hr (s + 9) (by omega)
  have e₁ := exec_ltFlag (a := b) (b := a) (f := s + 8) (s₁ := s + 2) (s₂ := s + 3) (t := s)
    (by simp; omega) r h2 h3 h0
  refine .seq e₁ ?_
  by_cases h₂ : r b < r a
  · rw [if_pos h₂]
    have e₅ : Exec (.inc b) (update (update r (s + 8) (r (s + 8) + 1)) (s + 8) 0)
        (update (update (update r (s + 8) (r (s + 8) + 1)) (s + 8) 0) b (r b + 1)) := by
      refine Exec.congr .inc rfl ?_
      congr 1; simp only [update_apply]; split_ifs <;> omega
    refine (exec_ite_pos (by omega) (by simp) (by upd_val) e₅ (by upd_val) (by upd_val)).congr
      rfl ?_
    simp only [unpairNext, if_neg hge, if_pos h₂]
    upd_tac
  · rw [if_neg h₂]
    have e₅ := exec_clear b (update r (s + 8) (r (s + 8) + 0))
    have e₆ := exec_addTo (i := a) (j := b) hab (update (update r (s + 8) (r (s + 8) + 0)) b 0)
    have e₇ : Exec (.inc b) (update (update (update (update r (s + 8) (r (s + 8) + 0)) b 0) b
        (r a)) a 0) (update (update (update (update (update r (s + 8) (r (s + 8) + 0)) b 0) b
        (r a)) a 0) b (r a + 1)) := by
      refine Exec.congr .inc rfl ?_
      congr 1; simp only [update_apply]; split_ifs <;> omega
    refine (exec_ite_neg (by omega) (by upd_val) (by upd_val)
      (.seq e₅ (.seq (e₆.congr rfl ?_) e₇)) (by upd_val)).congr rfl ?_
    · upd_tac
    · simp only [unpairNext, if_neg hge, if_neg h₂]
      upd_tac

theorem exec_unpairStep {a b s : ℕ} (hab : a ≠ b) (ha : a < s) (hb : b < s) (r : ℕ → ℕ)
    (hr : ∀ j, s ≤ j → r j = 0) :
    Exec (unpairStep a b s) r
      (update (update r a (unpairNext (r a, r b)).1) b (unpairNext (r a, r b)).2) := by
  have h0 := hr s le_rfl
  have h1 := hr (s + 1) (by omega)
  have h2 := hr (s + 2) (by omega)
  have h3 := hr (s + 3) (by omega)
  have h4 := hr (s + 4) (by omega)
  have e₁ := exec_ltFlag (a := a) (b := b) (f := s + 1) (s₁ := s + 2) (s₂ := s + 3) (t := s)
    (by simp; omega) r h2 h3 h0
  refine .seq e₁ ?_
  by_cases hlt : r a < r b
  · rw [if_pos hlt]
    have e := exec_unpairLT hab ha hb (update (update r (s + 1) (r (s + 1) + 1)) (s + 1) 0)
      (by intro j hj; simp only [update_apply]; split_ifs <;> simp [hr j hj]) (by upd_val)
    refine (exec_ite_pos (by omega) (by simp) (by upd_val) e (by upd_val) (by upd_val)).congr
      rfl ?_
    have ea : update (update r (s + 1) (r (s + 1) + 1)) (s + 1) 0 a = r a := by upd_val
    have eb : update (update r (s + 1) (r (s + 1) + 1)) (s + 1) 0 b = r b := by upd_val
    rw [ea, eb]
    upd_tac
  · rw [if_neg hlt]
    have e := exec_unpairGE hab ha hb (update r (s + 1) (r (s + 1) + 0))
      (by intro j hj; simp only [update_apply]; split_ifs <;> simp [hr j hj, h1]) (by upd_val)
    refine (exec_ite_neg (by omega) (by upd_val) (by upd_val) e (by upd_val)).congr rfl ?_
    have ea : update r (s + 1) (r (s + 1) + 0) a = r a := by upd_val
    have eb : update r (s + 1) (r (s + 1) + 0) b = r b := by upd_val
    rw [ea, eb]
    upd_tac

/-- The walk: `r s` steps of `unpairStep`. -/
theorem exec_unpairLoop {a b s : ℕ} (hab : a ≠ b) (ha : a < s) (hb : b < s) (k : ℕ) :
    ∀ (v : ℕ) (r : ℕ → ℕ), r s = v → (∀ j, s < j → r j = 0) → (r a, r b) = Nat.unpair k →
    Exec (.loop s (unpairStep a b (s + 1))) r
      (update (update (update r a (Nat.unpair (k + v)).1) b (Nat.unpair (k + v)).2) s 0) := by
  intro v
  induction v generalizing k with
  | zero =>
    intro r hv _ hk
    refine (Exec.loop0 hv).congr rfl ?_
    rw [Nat.add_zero, ← hk]
    upd_tac
  | succ v ih =>
    intro r hv hr hk
    have e := exec_unpairStep (s := s + 1) hab (by omega) (by omega) (update r s v)
      (by intro j hj; simp only [update_apply]; split_ifs <;> first | omega | exact hr j (by omega))
    have ea : update r s v a = r a := by upd_val
    have eb : update r s v b = r b := by upd_val
    rw [ea, eb, hk, ← unpair_succ] at e
    refine .loopS hv e ?_
    have e' := ih (k + 1)
      (update (update (update r s v) a (Nat.unpair (k + 1)).1) b (Nat.unpair (k + 1)).2)
      (by upd_val)
      (by intro j hj; simp only [update_apply]; split_ifs <;> first | omega | exact hr j hj)
      (by simp only [update_apply]; split_ifs <;> first | omega | rfl)
    refine e'.congr rfl ?_
    rw [show k + 1 + v = k + (v + 1) by omega]
    upd_tac

/-- **The unpairing macro**: `r a, r b := Nat.unpair (r n)`, scratch registers from `s`. -/
def unpairM (n a b s : ℕ) : Prog := .seq (copy n s (s + 1)) (.loop s (unpairStep a b (s + 1)))

/-- **Correctness of the unpairing macro.** -/
theorem exec_unpairM {n a b s : ℕ} (hab : a ≠ b) (hna : n ≠ a) (hnb : n ≠ b) (hn : n < s)
    (ha : a < s) (hb : b < s) (r : ℕ → ℕ) (hra : r a = 0) (hrb : r b = 0)
    (hr : ∀ j, s ≤ j → r j = 0) :
    Exec (unpairM n a b s) r
      (update (update r a (Nat.unpair (r n)).1) b (Nat.unpair (r n)).2) := by
  have e₁ := exec_copy (i := n) (j := s) (t := s + 1) (by omega) (by omega) (by omega) r
    (hr _ (by omega))
  have e₂ := exec_unpairLoop hab ha hb 0 (r n) (update r s (r s + r n)) (by simp [hr s le_rfl])
    (by intro j hj; simp only [update_apply]; split_ifs <;> first | omega | exact hr j (by omega))
    (by simp only [update_apply]; split_ifs <;> first | omega | simp [hra, hrb])
  refine (Exec.seq e₁ e₂).congr rfl ?_
  rw [Nat.zero_add]
  have := hr s le_rfl
  upd_tac

end Prog

end Minsky
