import Start.TLCA4HeadArgs

/-!
# Series V, big round, run 5, item A3: the first monomial of a βη fixed-point polynomial
(row M20-TLCA4-BETAETA)

Applications of the head-and-arguments invariant of `Start/TLCA4HeadArgs.lean` to polynomials.

* `bpow_app_reduces` — `Bⁿ X u ↠ λz₁ … z_n. X (u z₁ … z_n)` for a closed `B`,`M`,`I`-term `X`;
* **`mono_not_fixedPoint`** — no monomial `Bⁿ X` (`X ∈ {B, M, I}`) is a βη fixed-point
  combinator: `Bⁿ B x` has arity difference `-1`, `Bⁿ M x ↠ λz⃗. x z⃗ (x z⃗)` has a variable as
  first argument, and `Bⁿ I x =βη x`;
* **`polyFiveOne_two`** — a witness of `PolyFiveOne` without monomials of base `I` has at least two
  monomials;
* `GY a b t` — every occurrence of the variable `b` in `t` is inside the subterm `a b`;
  `GY.betaEtaReduces`: preserved by βη-reduction;
* **`headB_not_fixedPoint`** — no polynomial `Bⁿ B ∘ R` is a βη fixed-point combinator: applied to
  fresh `z₁ … zₙ g y` the fixed-point equation gives `R x z⃗ (g y) =βη x (P x) z⃗ g y`, where `y`
  occurs only inside `g y` on the left, while every reduct of the right ends with the argument `y`;
* **`polyFiveOne_head_baseM`** — `PolyFiveOne` has a witness `Bⁿ M ∘ m₂ ∘ … ∘ m_k`, `k ≥ 2`, with
  no monomial of base `I`: the first monomial of a βη fixed-point polynomial has base `M`.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda Tm

/-- `apl f [a_l, …, a_1] = f a_1 … a_l` (the list starts with the last argument). -/
def apl (f : Lambda) : List Lambda → Lambda
  | [] => f
  | a :: as => .app (apl f as) a

theorem apl_var (y : ℕ) : ∀ as : List Lambda, apl (.var y) as = spn y as
  | [] => rfl
  | a :: as => by simp only [apl, spn, apl_var y as]

theorem apl_append (f a : Lambda) : ∀ l : List Lambda, apl f (l ++ [a]) = apl (.app f a) l
  | [] => rfl
  | b :: l => by simp only [List.cons_append, apl, apl_append f a l]

/-- **`Bⁿ X u ↠ λz₁ … z_n. X (u z₁ … z_n)`** for a closed `X`. -/
theorem bpow_app_reduces {X : Tm} (hX : IsBMI X) : ∀ (n : ℕ) (u : Lambda),
    Lambda.reduces (.app (toLam (bpow n X)) u)
      (lamK n (.app (toLam X) (apl (Lambda.lift n 0 u) ((List.range n).map Lambda.var))))
  | 0, u => by
    simp only [bpow, lamK, Lambda.lift_zero, List.range_zero, List.map_nil, apl]
    exact .refl _
  | n + 1, u => by
    have h1 := hsteps_reduces (hsteps_B2 (toLam (bpow n X)) u)
    rw [lift_toLam_of_isBMI (bpow_isBMI hX n)] at h1
    refine Lambda.reduces_trans h1 (Lambda.reduces_lam ?_)
    have h2 := bpow_app_reduces hX n (.app (Lambda.lift 1 0 u) (.var 0))
    have e : apl (Lambda.lift n 0 (.app (Lambda.lift 1 0 u) (.var 0))) ((List.range n).map .var) =
        apl (Lambda.lift (n + 1) 0 u) ((List.range (n + 1)).map .var) := by
      rw [List.range_succ, List.map_append, List.map_singleton, apl_append]
      simp [Lambda.lift, Lambda.lift_add]
    rw [e] at h2
    exact h2

theorem reduces_lamK (k : ℕ) {t t' : Lambda} (h : Lambda.reduces t t') :
    Lambda.reduces (lamK k t) (lamK k t') := by
  induction k with
  | zero => exact h
  | succ k ih => exact Lambda.reduces_lam ih

theorem nsp_spn (z : ℕ) : ∀ as : List Lambda, NSp (spn z as) z as.length
  | [] => .var z
  | a :: as => .app a (nsp_spn z as)

theorem hsp_lamK_spn (y : ℕ) (as : List Lambda) : ∀ k : ℕ,
    HSp (lamK k (spn (y + k) as)) y ((as.length : ℤ) - k)
  | 0 => by simpa [lamK] using HSp.neu (nsp_spn y as)
  | k + 1 => by
    have := HSp.lam (hsp_lamK_spn (y + 1) as k)
    rw [show y + 1 + k = y + (k + 1) by omega] at this
    have e : (as.length : ℤ) - k - 1 = (as.length : ℤ) - ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e] at this
    exact this

/-- **No monomial is a βη fixed-point combinator.** -/
theorem mono_not_fixedPoint (m : Mono) :
    ¬ betaEtaConv (toLam (app m.tm (var 0))) (toLam (app (var 0) (app m.tm (var 0)))) := by
  intro hY
  obtain ⟨n, b⟩ := m
  have hR := bpow_app_reduces b.tm_isBMI n (.var 0)
  have hv : Lambda.lift n 0 (Lambda.var 0) = .var n := by simp [Lambda.lift]
  rw [hv, apl_var] at hR
  cases b with
  | I =>
    have hc : betaEtaConv (toLam (app (Mono.tm ⟨n, .I⟩) (var 0))) (.var 0) :=
      (betaEtaConv_app_left (bpowI_betaEta n) _).trans
        (betaEtaConv.of_reduces (betaEtaReduces.of_reduces (reduces_I _)))
    have := fixedPoint_hsp hY (HSp.neu (NSp.var 0)) hc
    omega
  | M =>
    have h2 : Lambda.reduces (toLam (app (Mono.tm ⟨n, .M⟩) (var 0)))
        (lamK n (spn n (spn n ((List.range n).map .var) :: (List.range n).map .var))) :=
      Lambda.reduces_trans hR (reduces_lamK n (reduces_M _))
    have hc := betaEtaConv.of_reduces (betaEtaReduces.of_reduces h2)
    cases n with
    | zero =>
      have := fixedPoint_firstArg_hsp (as := []) hY hc (HSp.neu (NSp.var 0))
      omega
    | succ j =>
      rw [List.range_succ, List.map_append, List.map_singleton, ← List.cons_append] at hc
      have := fixedPoint_firstArg_hsp hY hc (HSp.neu (NSp.var j))
      omega
  | B =>
    set R := (List.range n).map Lambda.var
    have h2 : Lambda.reduces (toLam (app (Mono.tm ⟨n, .B⟩) (var 0)))
        (lamK (n + 2) (spn (0 + (n + 2))
          (.app (.var 1) (.var 0) :: (R.map (Lambda.lift 1 0)).map (Lambda.lift 1 0)))) := by
      rw [lamK_add]
      refine Lambda.reduces_trans hR (reduces_lamK n ?_)
      have h3 := hsteps_reduces (hsteps_one (.weak (wstep_B1 (spn n R))))
      rw [← lift_lift_zero_one, spn_lift, spn_lift] at h3
      simpa [lamK, spn, Base.tm, toLam] using h3
    have ht := hsp_lamK_spn 0
      (.app (.var 1) (.var 0) :: (R.map (Lambda.lift 1 0)).map (Lambda.lift 1 0)) (n + 2)
    refine not_fixedPoint_of_hsp ht (betaEtaReduces.of_reduces h2) (Or.inr ?_) hY
    simp [R]

/-- **A fixed-point polynomial has at least two monomials**: a witness of `PolyFiveOne` can be
chosen without monomials of base `I`, and then it has length at least two. -/
theorem polyFiveOne_two (h : PolyFiveOne) :
    ∃ (m m' : Mono) (ps : List Mono), (∀ q ∈ m :: m' :: ps, q.base ≠ .I) ∧
      betaEtaConv (toLam (app (polyTm m (m' :: ps)) (var 0)))
        (toLam (app (var 0) (app (polyTm m (m' :: ps)) (var 0)))) := by
  obtain ⟨m, ps, hI, hfix⟩ := polyFiveOne_noI h
  cases ps with
  | nil => exact (mono_not_fixedPoint m hfix).elim
  | cons m' ps => exact ⟨m, m', ps, hI, hfix⟩

/-! ### First monomial `Bⁿ B`: the variable `y` occurs only in `g y` -/

/-- `GY a b t`: every occurrence of the variable `b` in `t` is as the argument of the variable `a`,
in the subterm `a b` (indices shift under binders). -/
inductive GY : ℕ → ℕ → Lambda → Prop
  | var {a b n : ℕ} : n ≠ b → GY a b (.var n)
  | pair {a b : ℕ} : GY a b (.app (.var a) (.var b))
  | app {a b : ℕ} {f u : Lambda} : GY a b f → GY a b u → GY a b (.app f u)
  | lam {a b : ℕ} {t : Lambda} : GY (a + 1) (b + 1) t → GY a b (.lam t)

theorem GY.var_inv {a b n : ℕ} (h : GY a b (.var n)) : n ≠ b := by
  cases h with
  | var hn => exact hn

theorem GY.app_inv {a b : ℕ} {f u : Lambda} (h : GY a b (.app f u)) :
    (f = .var a ∧ u = .var b) ∨ (GY a b f ∧ GY a b u) := by
  cases h with
  | pair => exact .inl ⟨rfl, rfl⟩
  | app hf hu => exact .inr ⟨hf, hu⟩

theorem GY.lam_inv {a b : ℕ} {t : Lambda} (h : GY a b (.lam t)) : GY (a + 1) (b + 1) t := by
  cases h with
  | lam ht => exact ht

theorem GY.lift {a b : ℕ} {s : Lambda} (h : GY a b s) :
    ∀ k, k ≤ a → k ≤ b → GY (a + 1) (b + 1) (Lambda.lift 1 k s) := by
  induction h with
  | @var a b n hn =>
    intro k _ _
    simp only [Lambda.lift]
    split_ifs <;> exact .var (by omega)
  | @pair a b =>
    intro k ha hb
    simp only [Lambda.lift, show ¬ a < k by omega, show ¬ b < k by omega, ↓reduceIte]
    exact .pair
  | app _ _ ih1 ih2 => intro k ha hb; exact .app (ih1 k ha hb) (ih2 k ha hb)
  | lam _ ih => intro k ha hb; exact .lam (ih (k + 1) (by omega) (by omega))

theorem GY.subst {A B : ℕ} {M : Lambda} (hM : GY A B M) :
    ∀ (a b x : ℕ) (s : Lambda), A = a + 1 → B = b + 1 → x ≤ a → x ≤ b → GY a b s →
      GY a b (Lambda.subst s x M) := by
  induction hM with
  | @var A B n hn =>
    intro a b x s hA hB hxa hxb hs
    simp only [Lambda.subst]
    split_ifs with h1 h2
    · exact hs
    · exact .var (by omega)
    · exact .var (by omega)
  | @pair A B =>
    intro a b x s hA hB hxa hxb hs
    subst hA hB
    simp only [Lambda.subst, show a + 1 ≠ x by omega, show a + 1 > x by omega,
      show b + 1 ≠ x by omega, show b + 1 > x by omega, ↓reduceIte, Nat.add_sub_cancel]
    exact .pair
  | app _ _ ih1 ih2 =>
    intro a b x s hA hB hxa hxb hs
    exact .app (ih1 a b x s hA hB hxa hxb hs) (ih2 a b x s hA hB hxa hxb hs)
  | lam _ ih =>
    intro a b x s hA hB hxa hxb hs
    exact .lam (ih (a + 1) (b + 1) (x + 1) _ (by omega) (by omega) (by omega) (by omega)
      (hs.lift 0 (Nat.zero_le _) (Nat.zero_le _)))

theorem GY.of_lift : ∀ (t : Lambda) (k a b : ℕ), GY (a + 1) (b + 1) (Lambda.lift 1 k t) →
    k ≤ a → k ≤ b → GY a b t
  | .var n, k, a, b, h, _, _ => by
    simp only [Lambda.lift] at h
    split_ifs at h <;> exact .var (by have := h.var_inv; omega)
  | .app t1 t2, k, a, b, h, ha, hb => by
    simp only [Lambda.lift] at h
    rcases h.app_inv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · cases t1 with
      | var n1 =>
        cases t2 with
        | var n2 =>
          simp only [Lambda.lift] at h1 h2
          split_ifs at h1 h2 <;> simp only [Lambda.var.injEq] at h1 h2 <;>
            first | omega | (obtain rfl : n1 = a := by omega
                             obtain rfl : n2 = b := by omega
                             exact .pair)
        | app _ _ => simp [Lambda.lift] at h2
        | lam _ => simp [Lambda.lift] at h2
      | app _ _ => simp [Lambda.lift] at h1
      | lam _ => simp [Lambda.lift] at h1
    · exact .app (GY.of_lift t1 k a b h1 ha hb) (GY.of_lift t2 k a b h2 ha hb)
  | .lam t, k, a, b, h, ha, hb => by
    simp only [Lambda.lift] at h
    exact .lam (GY.of_lift t (k + 1) (a + 1) (b + 1) h.lam_inv (by omega) (by omega))

theorem GY.step {a b : ℕ} {t t' : Lambda} (h : GY a b t) (hs : Lambda.step t t') :
    GY a b t' := by
  induction hs generalizing a b with
  | beta t1 t2 =>
    rcases h.app_inv with ⟨h1, _⟩ | ⟨h1, h2⟩
    · cases h1
    · exact h1.lam_inv.subst a b 0 t2 rfl rfl (Nat.zero_le _) (Nat.zero_le _) h2
  | app_left _ _ _ _ ih =>
    rcases h.app_inv with ⟨rfl, _⟩ | ⟨h1, h2⟩
    · rename_i hst; exact (Lambda.step.var_inv hst).elim
    · exact .app (ih h1) h2
  | app_right _ _ _ _ ih =>
    rcases h.app_inv with ⟨_, rfl⟩ | ⟨h1, h2⟩
    · rename_i hst; exact (Lambda.step.var_inv hst).elim
    · exact .app h1 (ih h2)
  | lam _ _ _ ih => exact .lam (ih h.lam_inv)

theorem GY.etaStep {a b : ℕ} {t t' : Lambda} (h : GY a b t) (hs : etaStep t t') : GY a b t' := by
  induction hs generalizing a b with
  | eta u =>
    rcases h.lam_inv.app_inv with ⟨_, h2⟩ | ⟨h1, _⟩
    · simp at h2
    · exact GY.of_lift u 0 a b h1 (Nat.zero_le _) (Nat.zero_le _)
  | app_left _ hst ih =>
    rcases h.app_inv with ⟨rfl, _⟩ | ⟨h1, h2⟩
    · cases hst
    · exact .app (ih h1) h2
  | app_right _ hst ih =>
    rcases h.app_inv with ⟨_, rfl⟩ | ⟨h1, h2⟩
    · cases hst
    · exact .app h1 (ih h2)
  | lam _ ih => exact .lam (ih h.lam_inv)

theorem GY.betaEtaReduces {a b : ℕ} {t t' : Lambda} (h : GY a b t)
    (hr : Lambda.betaEtaReduces t t') : GY a b t' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    rcases hs with hs | hs
    · exact ih.step hs
    · exact ih.etaStep hs

theorem GY.toLam_closed {a b : ℕ} {t : Tm} (ht : IsBMI t) : GY a b (toLam t) := by
  induction ht generalizing a b with
  | B =>
    exact .lam (.lam (.lam (.app (.var (by omega)) (.app (.var (by omega)) (.var (by omega))))))
  | M => exact .lam (.app (.var (by omega)) (.var (by omega)))
  | I => exact .lam (.var (by omega))
  | app _ _ ih1 ih2 => exact .app ih1 ih2

theorem GY.toLam_apps {a b : ℕ} : ∀ {f : Tm} {l : List Tm}, GY a b (toLam f) →
    (∀ z ∈ l, GY a b (toLam z)) → GY a b (toLam (apps f l))
  | _, [], hf, _ => hf
  | _, z :: l, hf, hl => GY.toLam_apps (l := l) (.app hf (hl z (by simp)))
      (fun w hw => hl w (by simp [hw]))

theorem var_betaEtaReduces {n : ℕ} {u : Lambda} (h : Lambda.betaEtaReduces (.var n) u) :
    u = .var n := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    subst ih
    rcases hs with hs | hs
    · exact (Lambda.step.var_inv hs).elim
    · cases hs

theorem toLam_apps_spn {y : ℕ} : ∀ {f : Tm} {cs : List Lambda} (l : List Tm), toLam f = spn y cs →
    ∃ cs', toLam (apps f l) = spn y cs'
  | _, cs, [], h => ⟨cs, h⟩
  | f, cs, z :: l, h => toLam_apps_spn (cs := toLam z :: cs) l (by simp [toLam, h, spn])

theorem conv_apps {f f' : Tm} (h : betaEtaConv (toLam f) (toLam f')) :
    ∀ l : List Tm, betaEtaConv (toLam (apps f l)) (toLam (apps f' l))
  | [] => h
  | z :: l => conv_apps (f := app f z) (f' := app f' z) (betaEtaConv_app_left h _) l

/-- **No polynomial whose first monomial has base `B` is a βη fixed-point combinator.**  With
`P = Bⁿ B ∘ R`, applying the fixed-point equation to fresh `z₁ … zₙ g y` gives
`R x z⃗ (g y) =βη x (P x) z⃗ g y`; on the left `y` only occurs in `g y` (`GY`, preserved by
βη-reduction), while every reduct of the right-hand side ends with the argument `y`. -/
theorem headB_not_fixedPoint (n : ℕ) (m' : Mono) (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨n, .B⟩ (m' :: ps)) (var 0)))
      (toLam (Tm.app (var 0) (Tm.app (polyTm ⟨n, .B⟩ (m' :: ps)) (var 0)))) := by
  intro hY
  set P := polyTm ⟨n, .B⟩ (m' :: ps) with hP
  set R := polyTm m' ps
  set zs : List Tm := (List.range n).map (fun i => Tm.var (i + 1)) with hzs
  have hzl : zs.length = n := by simp [hzs]
  have hL : WEq (apps (Tm.app P (var 0)) (zs ++ [Tm.var (n + 1), Tm.var (n + 2)]))
      (apps (Tm.app R (var 0)) (zs ++ [Tm.app (Tm.var (n + 1)) (Tm.var (n + 2))])) :=
    (comp_action_apps (bpow n B) R (var 0) _).trans
      (bpowB_action n (Tm.app R (var 0)) zs hzl (Tm.var (n + 1)) (Tm.var (n + 2)) [])
  have hc : betaEtaConv
      (toLam (apps (Tm.app R (var 0)) (zs ++ [Tm.app (Tm.var (n + 1)) (Tm.var (n + 2))])))
      (toLam (apps (Tm.app (var 0) (Tm.app P (var 0))) (zs ++ [Tm.var (n + 1), Tm.var (n + 2)]))) :=
    (betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _)
  obtain ⟨cs', hcs'⟩ := toLam_apps_spn (y := 0) (cs := [toLam (Tm.app P (var 0))])
    (f := Tm.app (var 0) (Tm.app P (var 0))) (zs ++ [Tm.var (n + 1)]) rfl
  have hR :
      toLam (apps (Tm.app (var 0) (Tm.app P (var 0))) (zs ++ [Tm.var (n + 1), Tm.var (n + 2)])) =
      lamK 0 (spn 0 (.var (n + 2) :: cs')) := by
    rw [show zs ++ [Tm.var (n + 1), Tm.var (n + 2)] =
        (zs ++ [Tm.var (n + 1)]) ++ [Tm.var (n + 2)] by simp,
      apps_append]
    simp only [apps, toLam, hcs', lamK, spn]
  rw [hR] at hc
  have hGY : GY (n + 1) (n + 2)
      (toLam (apps (Tm.app R (var 0)) (zs ++ [Tm.app (Tm.var (n + 1)) (Tm.var (n + 2))]))) := by
    refine GY.toLam_apps (.app (GY.toLam_closed (polyTm_isBMI m' ps)) (.var (by omega))) ?_
    intro z hz
    simp only [List.mem_append, List.mem_singleton, hzs, List.mem_map, List.mem_range] at hz
    rcases hz with ⟨i, hi, rfl⟩ | rfl
    · exact .var (by omega)
    · exact .pair
  obtain ⟨w, h1, h2⟩ := hc.common_reduct
  have hw := hGY.betaEtaReduces h1
  obtain ⟨j, z, pre, post, cs, hj, hy, hl, rfl, hpre, hpost⟩ := RForm.betaEtaReduces h2
  obtain rfl : j = 0 := by omega
  cases hpre
  simp only [List.nil_append] at hl
  subst hl
  cases hpost with
  | cons hc0 _ =>
    rename_i c cs2
    rw [Lambda.lift_zero] at hc0
    have := var_betaEtaReduces hc0
    subst this
    simp only [Nat.sub_zero, lamK, spn] at hw
    rcases hw.app_inv with ⟨h3, _⟩ | ⟨_, h4⟩
    · cases cs2 with
      | nil => simp [spn] at h3; omega
      | cons _ _ => simp [spn] at h3
    · exact h4.var_inv rfl

/-- **The first monomial of a βη fixed-point polynomial has base `M`**: `PolyFiveOne` has a
witness `Bⁿ M ∘ m₂ ∘ … ∘ m_k` with `k ≥ 2` and no monomial of base `I`. -/
theorem polyFiveOne_head_baseM (h : PolyFiveOne) :
    ∃ (n : ℕ) (m' : Mono) (ps : List Mono), (∀ q ∈ (⟨n, .M⟩ : Mono) :: m' :: ps, q.base ≠ .I) ∧
      betaEtaConv (toLam (app (polyTm ⟨n, .M⟩ (m' :: ps)) (var 0)))
        (toLam (app (var 0) (app (polyTm ⟨n, .M⟩ (m' :: ps)) (var 0)))) := by
  obtain ⟨⟨n, b⟩, m', ps, hI, hfix⟩ := polyFiveOne_two h
  cases b with
  | B => exact (headB_not_fixedPoint n m' ps hfix).elim
  | M => exact ⟨n, m', ps, hI, hfix⟩
  | I => exact (hI ⟨n, .I⟩ (by simp) rfl).elim

end TLCA4
