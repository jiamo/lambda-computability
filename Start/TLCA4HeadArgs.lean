import Start.TLCA4HeadArity

/-!
# Series V, big round, run 5, item A3: βη-convertible head normal forms have convertible
arguments (row M20-TLCA4-BETAETA)

The refinement of `Start/TLCA4HeadArity.lean` that also compares arguments.  Write
`spn y [a_l, …, a_1] = y a_1 … a_l` (the list starts with the *last* argument) and
`lamK k t = λ^k. t`.

* `RForm` — the shape of every βη-reduct of `λ^k. y a⃗`: the innermost `j` binders and the last
  `j` arguments have been η-removed (those arguments reduce to the bound variables), the head is
  `y - j`, and every remaining argument reduces to the `j`-fold lifting of the new argument;
* `RForm.betaEtaReduces` — `RForm` is preserved by βη-reduction;
* **`lamK_spn_betaEtaConv`** — if `λ^k. y a⃗ =βη λ^k. y' b⃗` (same number of binders), then
  `y = y'` and the argument lists are pointwise βη-convertible;
* `spn_betaEtaConv_eta` — η-expansion `λ^k. y a⃗ =βη λ^{k+1}. (y+1) (a⃗↑) 0`;
* **`fixedPoint_args`** — if `Y` is a βη fixed-point combinator and `Y x =βη λ^k. y a⃗`, then
  `y = k` (the head is `x`), and `a⃗` is pointwise βη-convertible to `x`'s argument `Y x` (lifted
  by `k`) followed by the bound variables, in order: `λ^k. x (Y x)↑ z₁ … z_k`.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

/-- `λ^k. t`. -/
def lamK : ℕ → Lambda → Lambda
  | 0, t => t
  | n + 1, t => .lam (lamK n t)

/-- `spn y [a_l, …, a_1] = y a_1 … a_l`: the list starts with the last argument. -/
def spn (y : ℕ) : List Lambda → Lambda
  | [] => .var y
  | a :: as => .app (spn y as) a

theorem spn_ne_lam (y : ℕ) (as : List Lambda) (c : Lambda) : spn y as ≠ .lam c := by
  cases as <;> simp [spn]

theorem lamK_succ' (m : ℕ) (t : Lambda) : lamK (m + 1) t = lamK m (.lam t) := by
  induction m with
  | zero => rfl
  | succ m ih => show Lambda.lam (lamK (m + 1) t) = Lambda.lam (lamK m (.lam t)); rw [ih]

theorem lamK_add (m n : ℕ) (t : Lambda) : lamK (m + n) t = lamK m (lamK n t) := by
  induction m with
  | zero => simp [lamK]
  | succ m ih => rw [Nat.add_right_comm]; show Lambda.lam _ = Lambda.lam _; rw [ih]

theorem lamK_spn_inj : ∀ {m m' z z' : ℕ} {cs cs' : List Lambda},
    lamK m (spn z cs) = lamK m' (spn z' cs') → m = m' ∧ z = z' ∧ cs = cs'
  | 0, 0, z, z', cs, cs', h => by
    simp only [lamK] at h
    induction cs generalizing cs' with
    | nil => cases cs' <;> simp_all [spn]
    | cons a as ih =>
      cases cs' with
      | nil => simp [spn] at h
      | cons b bs =>
        simp only [spn, Lambda.app.injEq] at h
        obtain ⟨h1, rfl⟩ := h
        obtain ⟨_, rfl, rfl⟩ := ih _ h1
        exact ⟨rfl, rfl, rfl⟩
  | m + 1, 0, z, z', cs, cs', h => by
    simp only [lamK] at h; exact absurd h.symm (spn_ne_lam _ _ _)
  | 0, m' + 1, z, z', cs, cs', h => by
    simp only [lamK] at h; exact absurd h (spn_ne_lam _ _ _)
  | m + 1, m' + 1, z, z', cs, cs', h => by
    simp only [lamK, Lambda.lam.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := lamK_spn_inj h
    exact ⟨rfl, rfl, rfl⟩

/-! ### βη-reduction under liftings -/

theorem betaEtaStep_lift {t t' : Lambda} (h : betaEtaStep t t') (n k : ℕ) :
    betaEtaReduces (Lambda.lift n k t) (Lambda.lift n k t') := by
  rcases h with h | h
  · exact betaEtaReduces.of_reduces (Lambda.reduces_lift (Lambda.reduces.step _ _ _ h
      (Lambda.reduces.refl _)) n k)
  · exact betaEtaReduces.single (.eta (etaStep_lift h n k))

theorem betaEtaReduces_liftNK {t t' : Lambda} (h : betaEtaReduces t t') (n k : ℕ) :
    betaEtaReduces (Lambda.lift n k t) (Lambda.lift n k t') := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih => exact ih.trans (betaEtaStep_lift hs n k)

theorem betaEtaReduces_app {f f' a a' : Lambda} (hf : betaEtaReduces f f')
    (ha : betaEtaReduces a a') : betaEtaReduces (.app f a) (.app f' a') := by
  have h1 : betaEtaReduces (.app f a) (.app f' a) := by
    induction hf with
    | refl => exact .refl _
    | tail _ hs ih =>
      refine ih.tail ?_
      rcases hs with hs | hs
      · exact .beta (.app_left _ _ _ hs)
      · exact .eta (.app_left _ hs)
  refine h1.trans ?_
  induction ha with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine ih.tail ?_
    rcases hs with hs | hs
    · exact .beta (.app_right _ _ _ hs)
    · exact .eta (.app_right _ hs)

theorem betaEtaReduces_underLam {t t' : Lambda} (h : betaEtaReduces t t') :
    betaEtaReduces (.lam t) (.lam t') := by
  induction h with
  | refl => exact .refl _
  | tail _ hs ih =>
    refine ih.tail ?_
    rcases hs with hs | hs
    · exact .beta (.lam _ _ hs)
    · exact .eta (.lam hs)

theorem betaEtaReduces_lamK (m : ℕ) {t t' : Lambda} (h : betaEtaReduces t t') :
    betaEtaReduces (lamK m t) (lamK m t') := by
  induction m with
  | zero => exact h
  | succ m ih => exact betaEtaReduces_underLam ih

/-! ### One step out of `λ^m. z c⃗` -/

theorem spn_step {z : ℕ} : ∀ {cs : List Lambda} {w : Lambda}, betaEtaStep (spn z cs) w →
    ∃ cs', w = spn z cs' ∧ List.Forall₂ betaEtaReduces cs cs'
  | [], w, h => by
    rcases h with h | h
    · exact (Lambda.step.var_inv h).elim
    · cases h
  | a :: as, w, h => by
    rcases h with h | h
    · rcases Lambda.step_app_inv h with ⟨c, hc, _⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · exact absurd hc (spn_ne_lam _ _ _)
      · obtain ⟨cs', rfl, hcs⟩ := spn_step (.beta hf)
        exact ⟨a :: cs', rfl, .cons (.refl _) hcs⟩
      · exact ⟨a' :: as, rfl, .cons (betaEtaReduces.single (.beta ha))
          (List.forall₂_same.2 fun _ _ => .refl _)⟩
    · cases h with
      | app_left _ hf =>
        obtain ⟨cs', rfl, hcs⟩ := spn_step (.eta hf)
        exact ⟨a :: cs', rfl, .cons (.refl _) hcs⟩
      | app_right _ ha =>
        exact ⟨_ :: as, rfl, .cons (betaEtaReduces.single (.eta ha))
          (List.forall₂_same.2 fun _ _ => .refl _)⟩

theorem spn_eq_lift {z : ℕ} : ∀ {cs : List Lambda} {u : Lambda}, spn z cs = Lambda.lift 1 0 u →
    ∃ z' cs0, z = z' + 1 ∧ cs = cs0.map (Lambda.lift 1 0) ∧ u = spn z' cs0
  | [], u, h => by
    cases u with
    | var y => simp only [spn, Lambda.lift] at h; cases h; exact ⟨y, [], by simp, rfl, rfl⟩
    | app _ _ => simp [spn, Lambda.lift] at h
    | lam _ => simp [spn, Lambda.lift] at h
  | a :: as, u, h => by
    cases u with
    | var y => simp [spn, Lambda.lift] at h
    | lam _ => simp [spn, Lambda.lift] at h
    | app u1 u2 =>
      simp only [spn, Lambda.lift, Lambda.app.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      obtain ⟨z', cs0, rfl, rfl, rfl⟩ := spn_eq_lift h1
      exact ⟨z', u2 :: cs0, rfl, rfl, rfl⟩

theorem etaStep_lam_inv {b w : Lambda} (h : etaStep (.lam b) w) :
    (∃ b', etaStep b b' ∧ w = .lam b') ∨ b = .app (Lambda.lift 1 0 w) (.var 0) := by
  cases h with
  | lam hb => exact .inl ⟨_, hb, rfl⟩
  | eta => exact .inr rfl

theorem lamK_spn_step {z : ℕ} {cs : List Lambda} : ∀ {m : ℕ} {w : Lambda},
    betaEtaStep (lamK m (spn z cs)) w →
    (∃ cs', w = lamK m (spn z cs') ∧ List.Forall₂ betaEtaReduces cs cs') ∨
    (∃ m' z' cs0, m = m' + 1 ∧ z = z' + 1 ∧ cs = .var 0 :: cs0.map (Lambda.lift 1 0) ∧
      w = lamK m' (spn z' cs0))
  | 0, w, h => .inl (spn_step h)
  | m + 1, w, h => by
    rcases h with h | h
    · cases h with
      | lam _ w' hb =>
        rcases lamK_spn_step (.beta hb) with ⟨cs', rfl, h⟩ | ⟨m', z', cs0, rfl, rfl, rfl, rfl⟩
        · exact .inl ⟨cs', rfl, h⟩
        · exact .inr ⟨m' + 1, z', cs0, rfl, rfl, rfl, rfl⟩
    · rcases etaStep_lam_inv h with ⟨b', hb, rfl⟩ | hb0
      · rcases lamK_spn_step (.eta hb) with ⟨cs', rfl, hcs⟩ | ⟨m', z', cs0, rfl, rfl, rfl, rfl⟩
        · exact .inl ⟨cs', rfl, hcs⟩
        · exact .inr ⟨m' + 1, z', cs0, rfl, rfl, rfl, rfl⟩
      · cases m with
        | succ m => simp [lamK] at hb0
        | zero =>
          simp only [lamK] at hb0
          cases cs with
          | nil => simp [spn] at hb0
          | cons c cs1 =>
            simp only [spn, Lambda.app.injEq] at hb0
            obtain ⟨h1, rfl⟩ := hb0
            obtain ⟨z', cs0, rfl, rfl, rfl⟩ := spn_eq_lift h1
            exact .inr ⟨0, z', cs0, rfl, rfl, rfl, rfl⟩

theorem forall₂_append' {R : Lambda → Lambda → Prop} :
    ∀ {a b c d : List Lambda}, List.Forall₂ R a b → List.Forall₂ R c d →
      List.Forall₂ R (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons hx hs, h => .cons hx (forall₂_append' hs h)

/-! ### The shape of the reducts -/

/-- The shape of a βη-reduct `w` of `λ^k. y a⃗` (see the module docstring). -/
def RForm (k y : ℕ) (as : List Lambda) (w : Lambda) : Prop :=
  ∃ j z pre post cs, j ≤ k ∧ y = z + j ∧ as = pre ++ post ∧ w = lamK (k - j) (spn z cs) ∧
    List.Forall₂ betaEtaReduces pre ((List.range j).map Lambda.var) ∧
    List.Forall₂ (fun a c => betaEtaReduces a (Lambda.lift j 0 c)) post cs

theorem RForm.init (k y : ℕ) (as : List Lambda) : RForm k y as (lamK k (spn y as)) :=
  ⟨0, y, [], as, as, Nat.zero_le _, rfl, rfl, rfl, .nil,
    List.forall₂_same.2 fun a _ => by rw [Lambda.lift_zero]; exact .refl _⟩

theorem RForm.step {k y : ℕ} {as : List Lambda} {w w' : Lambda} (hf : RForm k y as w)
    (hs : betaEtaStep w w') : RForm k y as w' := by
  obtain ⟨j, z, pre, post, cs, hj, rfl, rfl, rfl, hpre, hpost⟩ := hf
  rcases lamK_spn_step hs with ⟨cs', rfl, hcs⟩ | ⟨m', z', cs0, hm, rfl, rfl, rfl⟩
  · refine ⟨j, z, pre, post, cs', hj, rfl, rfl, rfl, hpre, ?_⟩
    clear hpre hs
    induction hpost generalizing cs' with
    | nil => cases hcs; exact .nil
    | cons hab _ ih =>
      cases hcs with
      | cons hc hrest => exact .cons (hab.trans (betaEtaReduces_liftNK hc j 0)) (ih _ hrest)
  · cases hpost with
    | @cons a c post' cs0' ha hpost' =>
      refine ⟨j + 1, z', pre ++ [a], post', cs0, by omega, by omega, by simp, by
        rw [show k - (j + 1) = m' by omega], ?_, ?_⟩
      · rw [List.range_succ, List.map_append]
        exact forall₂_append' hpre (.cons (by simpa [Lambda.lift] using ha) .nil)
      · clear hpre ha hs
        induction cs0 generalizing post' with
        | nil => cases hpost'; exact .nil
        | cons c cs ih =>
          cases hpost' with
          | cons hb hrest =>
            refine .cons ?_ (ih hrest)
            rw [Lambda.lift_add]; exact hb

/-- **`RForm` is preserved by βη-reduction**: every βη-reduct of `λ^k. y a⃗` has this shape. -/
theorem RForm.betaEtaReduces {k y : ℕ} {as : List Lambda} {w : Lambda}
    (hr : betaEtaReduces (lamK k (spn y as)) w) : RForm k y as w := by
  induction hr with
  | refl => exact RForm.init k y as
  | tail _ hs ih => exact ih.step hs

theorem forall₂_conv_of_common {f : Lambda → Lambda} {R : Lambda → Lambda → Prop}
    (hR : ∀ a c, R a c ↔ betaEtaReduces a (f c)) :
    ∀ {as bs cs : List Lambda}, List.Forall₂ R as cs → List.Forall₂ R bs cs →
      List.Forall₂ betaEtaConv as bs
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons ha hs, .cons hb hs' =>
    .cons ((betaEtaConv.of_reduces ((hR _ _).1 ha)).trans
      (betaEtaConv_symm (betaEtaConv.of_reduces ((hR _ _).1 hb))))
      (forall₂_conv_of_common hR hs hs')

/-- **βη-convertible head normal forms with the same number of binders have the same head and
pointwise βη-convertible arguments.** -/
theorem lamK_spn_betaEtaConv {k y y' : ℕ} {as bs : List Lambda}
    (hc : betaEtaConv (lamK k (spn y as)) (lamK k (spn y' bs))) :
    y = y' ∧ List.Forall₂ betaEtaConv as bs := by
  obtain ⟨w, h1, h2⟩ := hc.common_reduct
  obtain ⟨j, z, pre, post, cs, hj, rfl, rfl, rfl, hpre, hpost⟩ := RForm.betaEtaReduces h1
  obtain ⟨j', z', pre', post', cs', hj', hy, rfl, he, hpre', hpost'⟩ := RForm.betaEtaReduces h2
  obtain ⟨hm, rfl, rfl⟩ := lamK_spn_inj he
  obtain rfl : j = j' := by omega
  exact ⟨hy.symm, forall₂_append'
    (forall₂_conv_of_common (f := id) (fun _ _ => Iff.rfl) hpre hpre')
    (forall₂_conv_of_common (f := Lambda.lift j 0) (fun _ _ => Iff.rfl) hpost hpost')⟩

/-! ### η-expansion and fixed points -/

theorem spn_lift (y : ℕ) : ∀ cs : List Lambda,
    Lambda.lift 1 0 (spn y cs) = spn (y + 1) (cs.map (Lambda.lift 1 0))
  | [] => by simp [spn]
  | c :: cs => by simp only [spn, Lambda.lift, List.map_cons, spn_lift y cs]

/-- One η-expansion inside `k` binders. -/
theorem spn_betaEtaConv_eta (k y : ℕ) (cs : List Lambda) :
    betaEtaConv (lamK k (spn y cs))
      (lamK (k + 1) (spn (y + 1) (.var 0 :: cs.map (Lambda.lift 1 0)))) := by
  refine betaEtaConv_symm (betaEtaConv.of_reduces ?_)
  rw [lamK_succ']
  refine betaEtaReduces_lamK k (betaEtaReduces.single (.eta ?_))
  show etaStep (.lam (.app (spn (y + 1) (cs.map (Lambda.lift 1 0))) (.var 0))) _
  rw [← spn_lift]
  exact .eta _

/-- The arguments of `x a` after `k` η-expansions, last argument first:
`λ^k. x a↑ z₁ … z_k`. -/
def etaArgs (k : ℕ) (a : Lambda) : List Lambda :=
  (List.range k).map Lambda.var ++ [Lambda.lift k 0 a]

theorem etaArgs_succ (k : ℕ) (a : Lambda) :
    etaArgs (k + 1) a = .var 0 :: (etaArgs k a).map (Lambda.lift 1 0) := by
  simp only [etaArgs, List.range_succ_eq_map, List.map_cons, List.cons_append, List.map_append,
    List.map_map, List.cons.injEq, true_and]
  congr 1
  rw [List.map_nil, ← Lambda.lift_add, Nat.add_comm]

theorem app_betaEtaConv_etaArgs (a : Lambda) : ∀ k : ℕ,
    betaEtaConv (.app (.var 0) a) (lamK k (spn k (etaArgs k a)))
  | 0 => by simp [etaArgs, lamK, spn, Lambda.lift_zero]; exact .refl _
  | k + 1 => by
    rw [etaArgs_succ]
    exact (app_betaEtaConv_etaArgs a k).trans (spn_betaEtaConv_eta k k _)

open Tm in
/-- **The arguments of a βη fixed-point combinator.**  If `Y x =βη x (Y x)` and
`Y x =βη λ^k. y a⃗`, then the head is `x` (`y = k`) and the arguments are, in order, `(Y x)↑ᵏ`
followed by the bound variables: `λ^k. x (Y x)↑ z₁ … z_k`. -/
theorem fixedPoint_args {Y : Tm}
    (hY : betaEtaConv (toLam (app Y (var 0))) (toLam (app (var 0) (app Y (var 0)))))
    {k y : ℕ} {as : List Lambda} (hc : betaEtaConv (toLam (app Y (var 0))) (lamK k (spn y as))) :
    y = k ∧ List.Forall₂ betaEtaConv as (etaArgs k (toLam (app Y (var 0)))) :=
  lamK_spn_betaEtaConv ((betaEtaConv_symm hc).trans
    (hY.trans (app_betaEtaConv_etaArgs (toLam (app Y (var 0))) k)))

theorem betaEtaConv_lift {t u : Lambda} (h : betaEtaConv t u) (n k : ℕ) :
    betaEtaConv (Lambda.lift n k t) (Lambda.lift n k u) := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih => exact ih.trans (betaEtaConv.of_reduces (betaEtaStep_lift hs n k))
  | symm_step _ hs ih =>
    exact ih.trans (betaEtaConv_symm (betaEtaConv.of_reduces (betaEtaStep_lift hs n k)))

theorem forall₂_last {R : Lambda → Lambda → Prop} : ∀ {as bs : List Lambda} {a b : Lambda},
    as.length = bs.length → List.Forall₂ R (as ++ [a]) (bs ++ [b]) → R a b
  | [], [], _, _, _, .cons h _ => h
  | _ :: _, _ :: _, _, _, hl, .cons _ h => forall₂_last (by simpa using hl) h
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

open Tm in
/-- **The first argument of a βη fixed-point combinator is again headed by `x`**: if
`Y x =βη λ^k. y a₁ … a_l` with `a₁` a free-headed head normal form, then `a₁` has head `x`
(the variable `k` under the `k` binders) and arity difference `1`. -/
theorem fixedPoint_firstArg_hsp {Y : Tm}
    (hY : betaEtaConv (toLam (app Y (var 0))) (toLam (app (var 0) (app Y (var 0)))))
    {k y : ℕ} {as : List Lambda} {a : Lambda}
    (hc : betaEtaConv (toLam (app Y (var 0))) (lamK k (spn y (as ++ [a]))))
    {h : ℕ} {d : ℤ} (ha : HSp a h d) : h = k ∧ d = 1 := by
  obtain ⟨_, hf⟩ := fixedPoint_args hY hc
  have hl := hf.length_eq
  simp only [List.length_append, List.length_singleton, etaArgs, List.length_map,
    List.length_range] at hl
  have hlast : betaEtaConv a (Lambda.lift k 0 (toLam (app Y (var 0)))) :=
    forall₂_last (by simp; omega) hf
  have hx : HSp (Lambda.lift k 0 (toLam (app (var 0) (app Y (var 0))))) k 1 := by
    show HSp (.app (Lambda.lift k 0 (.var 0)) _) k ((0 + 1 : ℕ) : ℤ)
    simp only [Lambda.lift, Nat.zero_add]
    exact .neu (.app _ (.var k))
  obtain ⟨h1, h2⟩ := ha.betaEtaConv hx (hlast.trans (betaEtaConv_lift hY k 0))
  exact ⟨h1, h2⟩

open Tm in
/-- Non-vacuity of `fixedPoint_firstArg_hsp`: `B M` is not a βη fixed-point combinator, since
`B M x` reduces to `λz. x z (x z)`, whose first argument `z` is not headed by `x`. -/
theorem bM_not_fixedPoint :
    ¬ betaEtaConv (toLam (app (app B M) (var 0))) (toLam (app (var 0) (app (app B M) (var 0)))) := by
  intro hY
  have hr : Lambda.reduces (toLam (app (app B M) (var 0)))
      (lamK 1 (spn 1 ([.app (.var 1) (.var 0)] ++ [.var 0]))) := by
    have h1 := hsteps_reduces (hsteps_B2 lamM (.var 0))
    have hM : Lambda.lift 1 0 lamM = lamM := by simp [lamM, Lambda.lift]
    rw [hM] at h1
    refine Lambda.reduces_trans h1 (Lambda.reduces_lam ?_)
    simpa [Lambda.lift, spn, lamK] using reduces_M (.app (.var 1) (.var 0))
  have := fixedPoint_firstArg_hsp hY (betaEtaConv.of_reduces (betaEtaReduces.of_reduces hr))
    (HSp.neu (NSp.var 0))
  omega

end TLCA4
