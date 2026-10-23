import Start.TLCA4Hit5Index

/-!
# TLCA open problem 4: the chains of `hit5` under `q` depend on `q`
(row M20-TLCA4-BETAETA; big round 2, run 3, item A1)

Step 2 of the route to the `unique` field of `TailCores (Ext (H5Core x) x) x`: the variable `q`
(index `0`) occurs free in every chain under `q`, while a lifted term never has its cut-off
variable free.  This separates the heads `TW.wP`, `TW.wK` (built from lifted top-level chains) from
the abstractions among the components.

* `FreeIn k t` — the variable `k` occurs free in `t`; `freeIn_lift_iff`, **`not_freeIn_lift`**;
* `TC.freeIn0`, `TW.freeIn0` — generically in the base; `ByqR.freeIn0`, `YBase.freeIn0`,
  `YB.freeIn0`, `WqT.freeIn0`, `HB.freeIn0`, `SqT.freeIn0` and **`HC.freeIn0`**.
-/

set_option autoImplicit false

namespace TLCA4

/-- The variable `k` occurs free in a term. -/
def FreeIn : ℕ → Lambda → Prop
  | k, .var n => n = k
  | k, .app f a => FreeIn k f ∨ FreeIn k a
  | k, .lam b => FreeIn (k + 1) b

theorem freeIn_lift_iff (t : Lambda) : ∀ (c k : ℕ),
    FreeIn (if k < c then k else k + 1) (Lambda.lift 1 c t) ↔ FreeIn k t := by
  induction t with
  | var n =>
    intro c k
    simp only [Lambda.lift, FreeIn]
    split_ifs <;> simp [FreeIn] <;> omega
  | app f a ihf iha => intro c k; simp only [Lambda.lift, FreeIn, ihf, iha]
  | lam b ih =>
    intro c k
    simp only [Lambda.lift, FreeIn]
    have := ih (c + 1) (k + 1)
    split_ifs at this ⊢ <;> omega

theorem not_freeIn_lift (t : Lambda) : ∀ c : ℕ, ¬ FreeIn c (Lambda.lift 1 c t) := by
  induction t with
  | var n =>
    intro c
    simp only [Lambda.lift]
    split_ifs <;> simp [FreeIn] <;> omega
  | app f a ihf iha => intro c h; rcases h with h | h; exacts [ihf c h, iha c h]
  | lam b ih => intro c h; exact ih (c + 1) h

theorem freeIn_app_l {k : ℕ} {f : Lambda} (a : Lambda) (h : FreeIn k f) : FreeIn k (.app f a) :=
  Or.inl h

theorem freeIn_xPow {k : ℕ} {f t : Lambda} (h : FreeIn k t) : ∀ m, FreeIn k (xPow f m t)
  | 0 => h
  | m + 1 => Or.inr (freeIn_xPow h m)

theorem freeIn_lift_succ {t : Lambda} {k : ℕ} (h : FreeIn k t) :
    FreeIn (k + 1) (Lambda.lift 1 0 t) := by
  have := (freeIn_lift_iff t 0 k).2 h
  simpa using this

/-- Chains under `q` over a base whose members have `q` free have `q` free. -/
theorem TC.freeIn0 {base : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → FreeIn 0 P) {n : ℤ} {C : Lambda}
    (h : TC base x n C) : FreeIn 0 C := by
  induction h with
  | base hP => exact hb hP
  | bx _ ih => exact Or.inr ih
  | bx1 _ ih => exact Or.inr ih
  | rq _ _ ih => exact show FreeIn 1 _ from freeIn_xPow (freeIn_app_l _ (freeIn_lift_succ ih)) _

theorem TW.freeIn0 {base : ℤ → Lambda → Prop} {x : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → FreeIn 0 P) {n : ℤ} {W : Lambda}
    (h : TW base x n W) : FreeIn 0 W := by
  cases h with
  | wB hR => exact Or.inr (hR.freeIn0 hb)
  | wP hR _ =>
    exact show FreeIn 2 _ from
      freeIn_xPow (freeIn_app_l _ (freeIn_lift_succ (freeIn_lift_succ (hR.freeIn0 hb)))) _
  | wK hR => exact show FreeIn 1 _ from freeIn_lift_succ (hR.freeIn0 hb)

theorem ByqR.freeIn0 {y : ℕ} {R : Lambda} (h : ByqR y R) : FreeIn 0 R := by
  cases h <;> simp [FreeIn, bym1, bym2, bym3, bxPre]

theorem YBase.freeIn0 {x n : ℕ} {P : Lambda} (h : YBase x n P) : FreeIn 0 P := by
  cases h with
  | q _ => exact Or.inl rfl
  | m hR => exact Or.inr hR.freeIn0
  | rr _ h2 => exact Or.inr h2.freeIn0
  | comp _ => exact Or.inr rfl

theorem YB.freeIn0 {x : ℕ} {i : ℤ} {P : Lambda} (h : YB x i P) : FreeIn 0 P := by
  obtain ⟨n, -, hP⟩ := h
  exact hP.freeIn0

theorem WqT.freeIn0 {x : ℕ} {W : Lambda} (h : WqT x W) : FreeIn 0 W := by
  cases h with
  | ap _ => exact Or.inr rfl
  | body hW => exact hW.freeIn0 YB.freeIn0

theorem HB.freeIn0 {x : ℕ} {n : ℤ} {P : Lambda} (h : HB x n P) : FreeIn 0 P := by
  cases h with
  | q _ => exact Or.inl rfl
  | m hR => exact Or.inr hR.freeIn0
  | rr _ h2 => exact Or.inr h2.freeIn0
  | comp _ _ => exact Or.inr rfl
  | mw hW => exact Or.inr hW.freeIn0
  | ww hW => exact Or.inl hW.freeIn0

/-- **Every chain under `q` of the `hit5` grammar has `q` free.** -/
theorem HC.freeIn0 {x : ℕ} {n : ℤ} {C : Lambda} (h : HC x n C) : FreeIn 0 C :=
  h.toTC.freeIn0 HB.freeIn0

theorem SqT.freeIn0 {x : ℕ} {S : Lambda} (h : SqT x S) : FreeIn 0 S := by
  cases h with
  | mw hW => exact Or.inr hW.freeIn0
  | ww hW => exact Or.inl hW.freeIn0
  | core hP => exact hP.freeIn0 YB.freeIn0

end TLCA4
