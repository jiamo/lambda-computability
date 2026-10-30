import Start.TLCA4Hit5Core
import Start.TLCA4HeadArity

/-!
# TLCA open problem 4: the index of a component of `hit5` is unique
(row M20-TLCA4-BETAETA; big round 2, run 3, item A1)

The components of `hit5` (`HG x i`, `Start/TLCA4Hit5Grammar.lean`) contain chains with arbitrary
tails, so they need not normalize, and the normal-form argument that gives index uniqueness for
the components of `Q` (`YG.index_unique`) does not apply.  The replacement is a βη-invariant read
off a head normal form:

* `XDepth x a k N` — `N =βη xᵏ M` with `M` neutral with head `a`; **`XDepth.unique`** — for
  `a ≠ x`, the depth `k` is unique (confluence);
* `law_B`, `law_M`, `law_bxPre`, … — the head-reduction laws of the combinators involved;
  `ByR.conv`, `ByqR.conv` — the reducts `R` of `B (B x)` satisfy `R P z w =βη x (P z w)`;
* `YG.xd`, `YC.xd`, `YBase.xd` (the `v`-components), `TC.xd`, `TW.xd` (chains with arbitrary
  tails, generically in the base), `WT.xd`, `WqT.xd`, `SqT.xd`, `ST.xd` (the `w`- and `s`-layers)
  and **`HG.xd`**, `HC.xd`, `HB.xd` — a component `P` of index `i` satisfies
  `P a b =βη x^{i+1} (a …)` for every variable `a` and every term `b`;
* **`HG.index_unique`** — hence a term is a component of at most one index;
* `HG.not_lamM` — `M` is not a component (depth `0`).

This is the first ingredient of the uniqueness field of `TailCores (Ext (H5Core x) x) x`.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda (betaEtaReduces betaEtaStep)

/-- `N =βη xᵏ M` with `M` a neutral term with head variable `a`. -/
def XDepth (x a k : ℕ) (N : Lambda) : Prop :=
  ∃ M n, Lambda.betaEtaConv N (xPow (.var x) k M) ∧ NSp M a n

/-- Integer-height version: `0 ≤ n` and `XDepth` at `n.toNat`. -/
def XDz (x a : ℕ) (n : ℤ) (N : Lambda) : Prop := 0 ≤ n ∧ XDepth x a n.toNat N

theorem XDepth.of_conv {x a k : ℕ} {N N' : Lambda} (h : Lambda.betaEtaConv N N')
    (h' : XDepth x a k N') : XDepth x a k N := by
  obtain ⟨M, n, hc, hM⟩ := h'
  exact ⟨M, n, h.trans hc, hM⟩

theorem XDepth.x_app {x a k : ℕ} {N : Lambda} (h : XDepth x a k N) :
    XDepth x a (k + 1) (.app (.var x) N) := by
  obtain ⟨M, n, hc, hM⟩ := h
  exact ⟨M, n, betaEtaConv_app_right _ hc, hM⟩

theorem XDepth.neutral {x a n : ℕ} {M : Lambda} (h : NSp M a n) : XDepth x a 0 M :=
  ⟨M, n, .refl _, h⟩

theorem XDz.of_conv {x a : ℕ} {k : ℤ} {N N' : Lambda} (h : Lambda.betaEtaConv N N')
    (h' : XDz x a k N') : XDz x a k N := ⟨h'.1, h'.2.of_conv h⟩

theorem XDz.x_app {x a : ℕ} {k : ℤ} {N : Lambda} (h : XDz x a k N) :
    XDz x a (k + 1) (.app (.var x) N) := by
  refine ⟨by have := h.1; omega, ?_⟩
  have e : (k + 1).toNat = k.toNat + 1 := by have := h.1; omega
  rw [e]; exact h.2.x_app

theorem XDz.xPow {x a : ℕ} {k : ℤ} {N : Lambda} (h : XDz x a k N) :
    ∀ m : ℕ, XDz x a ((m : ℤ) + k) (xPow (.var x) m N)
  | 0 => by simpa [TLCA4.xPow] using h
  | m + 1 => by
    have := (XDz.xPow h m).x_app
    simp only [TLCA4.xPow]
    rwa [show ((m + 1 : ℕ) : ℤ) + k = (m : ℤ) + k + 1 by push_cast; ring]

theorem XDz.neutral {x a n : ℕ} {M : Lambda} (h : NSp M a n) : XDz x a 0 M :=
  ⟨le_rfl, XDepth.neutral h⟩

theorem XDz.ofNat {x a k : ℕ} {N : Lambda} (h : XDepth x a k N) : XDz x a k N :=
  ⟨by omega, by simpa using h⟩

theorem XDz.toNat {x a k : ℕ} {N : Lambda} (h : XDz x a k N) : XDepth x a k N := by
  simpa using h.2

theorem conv_beta (c t : Lambda) :
    Lambda.betaEtaConv (.app (.lam c) t) (Lambda.subst t 0 c) :=
  Lambda.betaEtaConv.of_reduces (.tail (.refl _) (.beta (Lambda.step.beta c t)))

theorem XDz.beta0 {x a : ℕ} {k : ℤ} {c t : Lambda} (h : XDz x a k (Lambda.subst t 0 c)) :
    XDz x a k (.app (.lam c) t) := h.of_conv (conv_beta c t)

theorem XDz.beta1 {x a : ℕ} {k : ℤ} {c t u : Lambda}
    (h : XDz x a k (.app (Lambda.subst t 0 c) u)) :
    XDz x a k (.app (.app (.lam c) t) u) := h.of_conv (betaEtaConv_app_left (conv_beta c t) u)

theorem XDz.beta2 {x a : ℕ} {k : ℤ} {c t u v : Lambda}
    (h : XDz x a k (.app (.app (Lambda.subst t 0 c) u) v)) :
    XDz x a k (.app (.app (.app (.lam c) t) u) v) :=
  h.of_conv (betaEtaConv_app_left (betaEtaConv_app_left (conv_beta c t) u) v)

theorem XDz.beta3 {x a : ℕ} {k : ℤ} {c t u v w : Lambda}
    (h : XDz x a k (.app (.app (.app (Lambda.subst t 0 c) u) v) w)) :
    XDz x a k (.app (.app (.app (.app (.lam c) t) u) v) w) :=
  h.of_conv (betaEtaConv_app_left (betaEtaConv_app_left (betaEtaConv_app_left
    (conv_beta c t) u) v) w)

theorem XDz.beta4 {x a : ℕ} {k : ℤ} {c t u v w y : Lambda}
    (h : XDz x a k (.app (.app (.app (.app (Lambda.subst t 0 c) u) v) w) y)) :
    XDz x a k (.app (.app (.app (.app (.app (.lam c) t) u) v) w) y) :=
  h.of_conv (betaEtaConv_app_left (betaEtaConv_app_left (betaEtaConv_app_left
    (betaEtaConv_app_left (conv_beta c t) u) v) w) y)

theorem subst_liftN (s X : Lambda) {k n : ℕ} (hk : k ≤ n) :
    ∀ c : ℕ, Lambda.subst s (c + k) (Lambda.lift (n + 1) c X) = Lambda.lift n c X := by
  induction X generalizing s with
  | var y =>
    intro c
    by_cases hy : y < c
    · have h1 : y ≠ c + k := by omega
      have h2 : ¬ y > c + k := by omega
      simp [Lambda.lift, Lambda.subst, hy, h1, h2]
    · have h1 : y + (n + 1) ≠ c + k := by omega
      have h2 : y + (n + 1) > c + k := by omega
      simp only [Lambda.lift, Lambda.subst, ite_eq_right hy, ite_eq_right h1, ite_eq_left h2]
      congr 1
  | app f g ihf ihg => intro c; simp [Lambda.lift, Lambda.subst, ihf, ihg]
  | lam b ih =>
    intro c
    simp only [Lambda.lift, Lambda.subst]
    rw [show c + k + 1 = (c + 1) + k by omega, ih]

theorem subst_liftN0 (s X : Lambda) {k n : ℕ} (hk : k ≤ n) :
    Lambda.subst s k (Lambda.lift (n + 1) 0 X) = Lambda.lift n 0 X := by
  simpa using subst_liftN s X hk 0

theorem lift_one_lift (n : ℕ) (X : Lambda) :
    Lambda.lift 1 0 (Lambda.lift n 0 X) = Lambda.lift (n + 1) 0 X := by
  rw [Lambda.lift_add 1 n 0 X |>.symm, Nat.add_comm]

macro "tlca4_csimp" : tactic =>
  `(tactic| simp only [Lambda.subst, Lambda.lift, Lambda.subst_lift, lift_one_lift,
    Lambda.lift_zero, subst_liftN0, subst_lamB, subst_lamM, lift_lamB, Nat.lt_irrefl, ite_true, ite_false, Nat.zero_add,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceGT,
    Nat.lt_add_one, Nat.not_lt_zero, reduceIte, gt_iff_lt, Nat.succ_ne_zero,
    Nat.add_one_ne_zero, Nat.reduceLeDiff, Nat.le_refl, Nat.zero_le, Nat.one_le_ofNat])

macro "tlca4_cbeta" : tactic =>
  `(tactic| (first
    | refine (conv_beta _ _).trans ?_
    | refine (betaEtaConv_app_left (conv_beta _ _) _).trans ?_
    | refine (betaEtaConv_app_left (betaEtaConv_app_left (conv_beta _ _) _) _).trans ?_
    | refine (betaEtaConv_app_left (betaEtaConv_app_left (betaEtaConv_app_left
        (conv_beta _ _) _) _) _).trans ?_) <;> tlca4_csimp)

theorem law_B (f g y : Lambda) :
    Lambda.betaEtaConv (.app (.app (.app lamB f) g) y) (.app f (.app g y)) := by
  unfold lamB
  tlca4_cbeta; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_M (f : Lambda) : Lambda.betaEtaConv (.app lamM f) (.app f f) := by
  unfold lamM; tlca4_cbeta; exact .refl _

theorem law_bxPre (y : ℕ) (f z : Lambda) :
    Lambda.betaEtaConv (.app (.app (bxPre y) f) z) (.app (.var y) (.app f z)) := by
  unfold bxPre; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_bmPre1 (f z : Lambda) :
    Lambda.betaEtaConv (.app (.app bmPre1 f) z) (.app lamM (.app f z)) := by
  unfold bmPre1 lamM; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_bmPre2 (f z : Lambda) :
    Lambda.betaEtaConv (.app (.app bmPre2 f) z) (.app (.app f z) (.app f z)) := by
  unfold bmPre2; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_bbPre (V c Y : Lambda) :
    Lambda.betaEtaConv (.app (.app (.app bbPre V) c) Y) (.app (.app lamB (.app V c)) Y) := by
  unfold bbPre lamB; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_bbPre2 (V c Y z : Lambda) :
    Lambda.betaEtaConv (.app (.app (.app (.app bbPre2 V) c) Y) z) (.app (.app V c) (.app Y z)) := by
  unfold bbPre2; tlca4_cbeta; tlca4_cbeta; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_byl1 (y : ℕ) (g z : Lambda) :
    Lambda.betaEtaConv (.app (.app (byl1 y) g) z) (.app (.app lamB (.var y)) (.app g z)) := by
  unfold byl1 lamB; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_byl2 (y : ℕ) (g z : Lambda) :
    Lambda.betaEtaConv (.app (.app (byl2 y) g) z) (.app (bxPre y) (.app g z)) := by
  unfold byl2 bxPre; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem law_byl3 (y : ℕ) (g z w : Lambda) :
    Lambda.betaEtaConv (.app (.app (.app (byl3 y) g) z) w) (.app (.var y) (.app (.app g z) w)) := by
  unfold byl3; tlca4_cbeta; tlca4_cbeta; tlca4_cbeta; exact .refl _

theorem conv_app_var_inj {x : ℕ} {A B : Lambda}
    (h : Lambda.betaEtaConv (.app (.var x) A) (.app (.var x) B)) : Lambda.betaEtaConv A B := by
  obtain ⟨w, h1, h2⟩ := h.common_reduct
  obtain ⟨A', rfl, hA⟩ := betaEtaReduces_app_var' h1
  obtain ⟨B', e, hB⟩ := betaEtaReduces_app_var' h2
  simp only [Lambda.app.injEq, true_and] at e
  subst e
  exact (Lambda.betaEtaConv.of_reduces hA).trans (betaEtaConv_symm (Lambda.betaEtaConv.of_reduces hB))

theorem nsp_xPow_succ (x k : ℕ) (M : Lambda) : NSp (xPow (.var x) (k + 1) M) x 1 := by
  exact .app _ (.var x)

theorem xPow_conv_unique {x a : ℕ} (hax : a ≠ x) :
    ∀ (k k' : ℕ) {M M' : Lambda} {n n' : ℕ}, NSp M a n → NSp M' a n' →
      Lambda.betaEtaConv (xPow (.var x) k M) (xPow (.var x) k' M') → k = k'
  | 0, 0, _, _, _, _, _, _, _ => rfl
  | 0, k' + 1, _, _, _, _, hM, _, hc => by
    have := (HSp.neu hM).betaEtaConv (HSp.neu (nsp_xPow_succ x k' _)) hc
    exact (hax this.1).elim
  | k + 1, 0, _, _, _, _, _, hM', hc => by
    have := (HSp.neu (nsp_xPow_succ x k _)).betaEtaConv (HSp.neu hM') hc
    exact (hax this.1.symm).elim
  | k + 1, k' + 1, _, _, _, _, hM, hM', hc => by
    rw [xPow_conv_unique hax k k' hM hM' (conv_app_var_inj hc)]

/-- **The `x`-depth is unique.** -/
theorem XDepth.unique {x a k k' : ℕ} {N : Lambda} (hax : a ≠ x) (h : XDepth x a k N)
    (h' : XDepth x a k' N) : k = k' := by
  obtain ⟨M, n, hc, hM⟩ := h
  obtain ⟨M', n', hc', hM'⟩ := h'
  exact xPow_conv_unique hax k k' hM hM' ((betaEtaConv_symm hc).trans hc')


/-! ### Reducts of `B y`: `R P z w =βη x (P z w)` -/

theorem conv_app2 {t t' : Lambda} (h : Lambda.betaEtaConv t t') (u v : Lambda) :
    Lambda.betaEtaConv (.app (.app t u) v) (.app (.app t' u) v) :=
  betaEtaConv_app_left (betaEtaConv_app_left h u) v

theorem ByR.conv {y : ℕ} {R : Lambda} (hR : ByR y R) (P z w : Lambda) :
    Lambda.betaEtaConv (.app (.app (.app R P) z) w) (.app (.var y) (.app (.app P z) w)) := by
  cases hR with
  | bb =>
    unfold bbx
    exact (betaEtaConv_app_left (law_B _ _ _) w).trans (law_B _ _ _)
  | bpre =>
    unfold bbpre
    exact (betaEtaConv_app_left (law_B _ _ _) w).trans (law_bxPre _ _ _)
  | l1 => exact (betaEtaConv_app_left (law_byl1 _ _ _) w).trans (law_B _ _ _)
  | l2 => exact (betaEtaConv_app_left (law_byl2 _ _ _) w).trans (law_bxPre _ _ _)
  | l3 => exact law_byl3 _ _ _ _

theorem ByqR.conv {x a : ℕ} {R : Lambda} (hR : ByqR (x + 1) R) (z w : Lambda) :
    Lambda.betaEtaConv (.app (.app (Lambda.subst (.var a) 0 R) z) w)
      (.app (.var x) (.app (.app (.var a) z) w)) := by
  cases hR with
  | bb =>
    have : Lambda.subst (.var a) 0 (.app (bbx (x + 1)) (.var 0)) = .app (bbx x) (.var a) := by
      simp [bbx, lamB, Lambda.subst]
    rw [this]; exact (ByR.bb).conv _ _ _
  | bpre =>
    have : Lambda.subst (.var a) 0 (.app (bbpre (x + 1)) (.var 0)) = .app (bbpre x) (.var a) := by
      simp [bbpre, bxPre, lamB, Lambda.subst]
    rw [this]; exact (ByR.bpre).conv _ _ _
  | l1 =>
    have : Lambda.subst (.var a) 0 (.app (byl1 (x + 1)) (.var 0)) = .app (byl1 x) (.var a) := by
      simp [byl1, lamB, Lambda.subst]
    rw [this]; exact (ByR.l1).conv _ _ _
  | l2 =>
    have : Lambda.subst (.var a) 0 (.app (byl2 (x + 1)) (.var 0)) = .app (byl2 x) (.var a) := by
      simp [byl2, bxPre, Lambda.subst]
    rw [this]; exact (ByR.l2).conv _ _ _
  | l3 =>
    have : Lambda.subst (.var a) 0 (.app (byl3 (x + 1)) (.var 0)) = .app (byl3 x) (.var a) := by
      simp [byl3, Lambda.subst]
    rw [this]; exact (ByR.l3).conv _ _ _
  | m1 =>
    simp only [bym1, Lambda.subst, Lambda.lift, subst_lamB]
    tlca4_cbeta
    exact law_B _ _ _
  | m2 =>
    simp only [bym2, bxPre, Lambda.subst, Lambda.lift]
    tlca4_cbeta
    tlca4_cbeta; tlca4_cbeta; exact .refl _
  | m3 =>
    simp only [bym3, Lambda.subst, Lambda.lift]
    tlca4_cbeta; tlca4_cbeta; exact .refl _

/-! ### Chain steps -/

theorem XDz.neutral_app2 {x a n : ℕ} {M : Lambda} (h : NSp M a n) (u v : Lambda) :
    XDz x a 0 (.app (.app M u) v) := XDz.neutral (.app _ (.app _ h))

theorem xd_bx {x a : ℕ} {n : ℤ} {P : Lambda}
    (h : ∀ b, XDz x a n (.app (Lambda.subst (.var a) 0 P) b)) (b : Lambda) :
    XDz x a (n + 1) (.app (Lambda.subst (.var a) 0 (.app (.app lamB (.var (x + 1))) P)) b) := by
  simp only [Lambda.subst, subst_lamB]
  simp only [show x + 1 ≠ 0 by omega, ite_false, show x + 1 > 0 by omega, ite_true,
    Nat.add_sub_cancel]
  exact (h b).x_app.of_conv (law_B _ _ _)

theorem xd_bx1 {x a : ℕ} {n : ℤ} {P : Lambda}
    (h : ∀ b, XDz x a n (.app (Lambda.subst (.var a) 0 P) b)) (b : Lambda) :
    XDz x a (n + 1) (.app (Lambda.subst (.var a) 0 (.app (bxPre (x + 1)) P)) b) := by
  simp only [Lambda.subst, subst_bxPre]
  exact (h b).x_app.of_conv (law_bxPre _ _ _)

theorem xd_rq {x a : ℕ} {n n' : ℤ} {m : ℕ} {R T : Lambda}
    (h : ∀ b, XDz x a n' (.app (Lambda.subst (.var a) 0 R) b)) (hm : (m : ℤ) + n' = n)
    (b : Lambda) :
    XDz x a n (.app (Lambda.subst (.var a) 0
      (.lam (xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) T)))) b) := by
  have e : Lambda.subst (.var a) 0 (.lam (xPow (.var (x + 1 + 1)) m (.app (Lambda.lift 1 0 R) T))) =
      .lam (xPow (.var (x + 1)) m
        (.app (Lambda.lift 1 0 (Lambda.subst (.var a) 0 R))
          (Lambda.subst (Lambda.lift 1 0 (.var a)) 1 T))) := by
    simp only [Lambda.subst, subst_xPow]
    rw [Lambda.lift_subst R (.var a) 1 0 0 (le_refl 0)]
    simp
  rw [show x + 2 = x + 1 + 1 by rfl, e]
  refine XDz.beta0 ?_
  simp only [subst_xPow, Lambda.subst, Lambda.subst_lift]
  simp only [show x + 1 ≠ 0 by omega, ite_false, show x + 1 > 0 by omega, ite_true,
    Nat.add_sub_cancel]
  rw [← hm]
  exact (h _).xPow m

/-! ### The components of `Q`-type grammars -/

/-- `M (R a) b` for a reduct `R` of `B y`: depth one. -/
theorem xd_mR {x a : ℕ} {R : Lambda} (hR : ByR x R) (b : Lambda) :
    XDz x a 1 (.app (.app lamM (.app R (.var a))) b) := by
  refine XDz.of_conv (betaEtaConv_app_left (law_M _) b) ?_
  refine XDz.of_conv (hR.conv _ _ _) ?_
  simpa using (XDz.neutral_app2 (x := x) (NSp.var a) (.app R (.var a)) b).x_app

theorem xd_qR {x a : ℕ} {R : Lambda} (hR : ByqR (x + 1) R) (z b : Lambda) :
    XDz x a 1 (.app (.app (Lambda.subst (.var a) 0 R) z) b) := by
  refine XDz.of_conv (hR.conv _ _) ?_
  simpa using (XDz.neutral_app2 (x := x) (NSp.var a) z b).x_app

mutual
theorem YG.xd {x a i : ℕ} {P : Lambda} (h : YG x i P) (b : Lambda) :
    XDz x a ((i : ℤ) + 1) (.app (.app P (.var a)) b) := by
  match h with
  | .bm hR =>
    simpa using (xd_mR hR b).of_conv (betaEtaConv_app_left (law_B _ _ _) b)
  | .bm1 hR =>
    simpa using (xd_mR hR b).of_conv (betaEtaConv_app_left (law_bmPre1 _ _) b)
  | .bm2 hR =>
    refine XDz.of_conv (betaEtaConv_app_left (law_bmPre2 _ _) b) ?_
    refine XDz.of_conv (hR.conv _ _ _) ?_
    simpa using (XDz.neutral_app2 (x := x) (NSp.var a) (.app _ (.var a)) b).x_app
  | .byApp hR hP =>
    refine XDz.of_conv (hR.conv _ _ _) ?_
    have := (YG.xd (a := a) hP b).x_app
    push_cast; exact this
  | .lam hc =>
    refine XDz.beta1 ?_
    have := YC.xd (a := a) hc b
    push_cast at this; exact this
theorem YC.xd {x a n : ℕ} {C : Lambda} (h : YC x n C) (b : Lambda) :
    XDz x a n (.app (Lambda.subst (.var a) 0 C) b) := by
  match h with
  | .base hb => exact YBase.xd (a := a) hb b
  | .bx hP => push_cast; exact xd_bx (fun b => YC.xd (a := a) hP b) b
  | .bx1 hP => push_cast; exact xd_bx1 (fun b => YC.xd (a := a) hP b) b
  | .rq hR hm => exact xd_rq (fun b => YC.xd (a := a) hR b) (by rw [← hm]; push_cast; rfl) b
theorem YBase.xd {x a n : ℕ} {P : Lambda} (h : YBase x n P) (b : Lambda) :
    XDz x a n (.app (Lambda.subst (.var a) 0 P) b) := by
  match h with
  | .q hR =>
    simp only [Lambda.subst, ite_true]
    exact XDz.neutral (.app _ (.app _ (.var a)))
  | .m hR =>
    simp only [Lambda.subst, subst_lamM]
    exact (xd_qR hR _ b).of_conv (betaEtaConv_app_left (law_M _) b)
  | .rr h1 h2 =>
    simp only [Lambda.subst]
    exact xd_qR h1 _ b
  | .comp hR =>
    simp only [Lambda.subst, Lambda.subst_lift, ite_true]
    push_cast; exact YG.xd (a := a) hR b
end

/-! ### Generic chains and two-argument chains under `q` -/

theorem TC.xd {base : ℤ → Lambda → Prop} {x a : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → ∀ b, XDz x a i (.app (Lambda.subst (.var a) 0 P) b))
    {n : ℤ} {C : Lambda} (h : TC base (x + 1) n C) :
    ∀ b, XDz x a n (.app (Lambda.subst (.var a) 0 C) b) := by
  generalize ex : x + 1 = x' at h
  induction h with
  | base hP => exact hb hP
  | bx _ ih => subst ex; exact xd_bx ih
  | bx1 _ ih => subst ex; exact xd_bx1 ih
  | rq _ hm ih => subst ex; exact xd_rq ih hm

theorem TW.xd {base : ℤ → Lambda → Prop} {x a : ℕ}
    (hb : ∀ {i : ℤ} {P : Lambda}, base i P → ∀ b, XDz x a i (.app (Lambda.subst (.var a) 0 P) b))
    {n : ℤ} {W : Lambda} (h : TW base (x + 1) n W) (Y b : Lambda) :
    XDz x a n (.app (.app (Lambda.subst (.var a) 0 W) Y) b) := by
  cases h with
  | wB hR =>
    simp only [Lambda.subst, subst_lamB]
    exact (TC.xd hb hR (.app Y b)).of_conv (law_B _ _ _)
  | @wK R hR =>
    have e : Lambda.subst (.var a) 0 (.lam (Lambda.lift 1 0 R)) =
        .lam (Lambda.lift 1 0 (Lambda.subst (.var a) 0 R)) := by
      simp only [Lambda.subst]
      rw [Lambda.lift_subst R (.var a) 1 0 0 (le_refl 0)]
    rw [e]
    refine XDz.beta1 ?_
    rw [Lambda.subst_lift]
    exact TC.xd hb hR b
  | @wP i' m R T hR hm =>
    have e1 : Lambda.subst (Lambda.lift 1 0 (.var a)) 1 (Lambda.lift 1 0 R) =
        Lambda.lift 1 0 (Lambda.subst (.var a) 0 R) := by
      rw [Lambda.lift_subst R (.var a) 1 0 0 (le_refl 0)]
    have e2 : Lambda.subst (Lambda.lift 1 0 (Lambda.lift 1 0 (.var a))) 2
        (Lambda.lift 1 0 (Lambda.lift 1 0 R)) =
        Lambda.lift 1 0 (Lambda.lift 1 0 (Lambda.subst (.var a) 0 R)) := by
      rw [← e1, Lambda.lift_subst (Lambda.lift 1 0 R) (Lambda.lift 1 0 (.var a)) 1 0 1 (Nat.zero_le 1)]
    have e : Lambda.subst (.var a) 0 (.lam (.lam (xPow (.var (x + 1 + 2)) m
        (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T)))) =
        .lam (.lam (xPow (.var (x + 2)) m
          (.app (Lambda.lift 1 0 (Lambda.lift 1 0 (Lambda.subst (.var a) 0 R)))
            (Lambda.subst (Lambda.lift 1 0 (Lambda.lift 1 0 (.var a))) 2 T)))) := by
      simp only [Lambda.subst, subst_xPow]
      rw [e2]
      simp
    rw [e]
    refine XDz.beta1 ?_
    simp only [Lambda.subst, subst_xPow, Nat.zero_add, subst_lift_lift_one1,
      show x + 2 ≠ 1 by omega, show x + 2 > 1 by omega, ite_true, ite_false,
      show x + 2 - 1 = x + 1 by omega]
    refine XDz.beta0 ?_
    simp only [Lambda.subst, subst_xPow, Lambda.subst_lift,
      show x + 1 ≠ 0 by omega, show x + 1 > 0 by omega, ite_true, ite_false, Nat.add_sub_cancel]
    rw [← hm]
    exact (TC.xd hb hR _).xPow m

theorem YB.xd {x a : ℕ} {i : ℤ} {P : Lambda} (h : YB x i P) (b : Lambda) :
    XDz x a i (.app (Lambda.subst (.var a) 0 P) b) := by
  obtain ⟨n, rfl, hP⟩ := h
  exact YBase.xd hP b

/-! ### The `w`- and `s`-layers of `hit5` -/

theorem WT.xd {x a : ℕ} {W : Lambda} (h : WT x W) (Y b : Lambda) :
    XDz x a 1 (.app (.app (.app W (.var a)) Y) b) := by
  cases h with
  | wbb hV =>
    refine XDz.of_conv (conv_app2 (law_B _ _ _) Y b) ?_
    refine XDz.of_conv (law_B _ _ _) ?_
    simpa using YG.xd (a := a) hV (.app Y b)
  | wpre hV =>
    refine XDz.of_conv (betaEtaConv_app_left (law_bbPre _ _ _) b) ?_
    refine XDz.of_conv (law_B _ _ _) ?_
    simpa using YG.xd (a := a) hV (.app Y b)
  | wpre2 hV =>
    refine XDz.of_conv (law_bbPre2 _ _ _ _) ?_
    simpa using YG.xd (a := a) hV (.app Y b)
  | wlam hW =>
    refine XDz.beta2 ?_
    exact TW.xd (fun hP b => YB.xd hP b) hW Y b

theorem WqT.xd {x a : ℕ} {W : Lambda} (h : WqT x W) (Y b : Lambda) :
    XDz x a 1 (.app (.app (Lambda.subst (.var a) 0 W) Y) b) := by
  cases h with
  | ap hW =>
    simp only [Lambda.subst, Lambda.subst_lift, ite_true]
    exact WT.xd hW Y b
  | body hW => exact TW.xd (fun hP b => YB.xd hP b) hW Y b

theorem SqT.xd {x a : ℕ} {S : Lambda} (h : SqT x S) (b : Lambda) :
    XDz x a 1 (.app (Lambda.subst (.var a) 0 S) b) := by
  cases h with
  | mw hW =>
    simp only [Lambda.subst, subst_lamM]
    exact (WqT.xd hW _ b).of_conv (betaEtaConv_app_left (law_M _) b)
  | ww hW =>
    simp only [Lambda.subst]
    exact WqT.xd hW _ b
  | core hP => exact TC.xd (fun hP b => YB.xd hP b) hP b

theorem ST.xd {x a : ℕ} {P : Lambda} (h : ST x P) (b : Lambda) :
    XDz x a 1 (.app (.app P (.var a)) b) := by
  cases h with
  | sbm hW =>
    refine XDz.of_conv (betaEtaConv_app_left (law_B _ _ _) b) ?_
    exact (WT.xd hW _ b).of_conv (betaEtaConv_app_left (law_M _) b)
  | sbm1 hW =>
    refine XDz.of_conv (betaEtaConv_app_left (law_bmPre1 _ _) b) ?_
    exact (WT.xd hW _ b).of_conv (betaEtaConv_app_left (law_M _) b)
  | sbm2 hW =>
    refine XDz.of_conv (betaEtaConv_app_left (law_bmPre2 _ _) b) ?_
    exact WT.xd hW _ b
  | slam hS =>
    refine XDz.beta1 ?_
    exact SqT.xd hS b
  | sv hV => simpa using YG.xd (a := a) hV b
  | @seta f hW =>
    have := WqT.xd (a := a) hW (.var a) b
    rwa [Lambda.subst_lift] at this

/-! ### The components of `hit5` -/

mutual
theorem HG.xd {x a i : ℕ} {P : Lambda} (h : HG x i P) (b : Lambda) :
    XDz x a ((i : ℤ) + 1) (.app (.app P (.var a)) b) := by
  match h with
  | .yg hY => exact YG.xd hY b
  | .st hS => simpa using ST.xd (a := a) hS b
  | .byApp hR hP =>
    refine XDz.of_conv (hR.conv _ _ _) ?_
    have := (HG.xd (a := a) hP b).x_app
    push_cast; exact this
  | .lam hc hn =>
    refine XDz.beta1 ?_
    rw [← hn]; exact HC.xd (a := a) hc b
theorem HC.xd {x a : ℕ} {n : ℤ} {C : Lambda} (h : HC x n C) (b : Lambda) :
    XDz x a n (.app (Lambda.subst (.var a) 0 C) b) := by
  match h with
  | .base hb => exact HB.xd (a := a) hb b
  | .bx hP => exact xd_bx (fun b => HC.xd (a := a) hP b) b
  | .bx1 hP => exact xd_bx1 (fun b => HC.xd (a := a) hP b) b
  | .rq hR hm => exact xd_rq (fun b => HC.xd (a := a) hR b) hm b
theorem HB.xd {x a : ℕ} {n : ℤ} {P : Lambda} (h : HB x n P) (b : Lambda) :
    XDz x a n (.app (Lambda.subst (.var a) 0 P) b) := by
  match h with
  | .q hR =>
    simp only [Lambda.subst, ite_true]
    exact XDz.neutral (.app _ (.app _ (.var a)))
  | .m hR =>
    simp only [Lambda.subst, subst_lamM]
    exact (xd_qR hR _ b).of_conv (betaEtaConv_app_left (law_M _) b)
  | .rr h1 h2 =>
    simp only [Lambda.subst]
    exact xd_qR h1 _ b
  | .comp hR hn =>
    simp only [Lambda.subst, Lambda.subst_lift, ite_true]
    rw [hn]; exact HG.xd (a := a) hR b
  | .mw hW =>
    simp only [Lambda.subst, subst_lamM]
    exact (WqT.xd hW _ b).of_conv (betaEtaConv_app_left (law_M _) b)
  | .ww hW =>
    simp only [Lambda.subst]
    exact WqT.xd hW _ b
end

/-- **The index of a component of `hit5` is unique.** -/
theorem HG.index_unique {x i j : ℕ} {P : Lambda} (hi : HG x i P) (hj : HG x j P) : i = j := by
  have h1 : XDz x (x + 1) ((i + 1 : ℕ) : ℤ) (.app (.app P (.var (x + 1))) (.var 0)) := by
    push_cast; exact HG.xd (a := x + 1) hi (.var 0)
  have h2 : XDz x (x + 1) ((j + 1 : ℕ) : ℤ) (.app (.app P (.var (x + 1))) (.var 0)) := by
    push_cast; exact HG.xd (a := x + 1) hj (.var 0)
  have := XDepth.unique (by omega) h1.toNat h2.toNat
  omega

/-- **`M` is not a component of `hit5`**: `M a b =βη a a b` has `x`-depth `0`. -/
theorem HG.not_lamM {x i : ℕ} (h : HG x i lamM) : False := by
  have h1 : XDz x (x + 1) ((i + 1 : ℕ) : ℤ) (.app (.app lamM (.var (x + 1))) (.var 0)) := by
    push_cast; exact HG.xd (a := x + 1) h (.var 0)
  have h2 : XDz x (x + 1) ((0 : ℕ) : ℤ) (.app (.app lamM (.var (x + 1))) (.var 0)) :=
    (XDz.neutral_app2 (x := x) (NSp.var (x + 1)) (.var (x + 1)) (.var 0)).of_conv
      (betaEtaConv_app_left (law_M _) _)
  have := XDepth.unique (by omega) h1.toNat h2.toNat
  omega

end TLCA4
