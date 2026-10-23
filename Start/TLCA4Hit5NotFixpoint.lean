import Start.TLCA4Hit5Fields

/-!
# TLCA open problem 4: `hit5` is not a βη fixed-point combinator
(row M20-TLCA4-BETAETA; big round 2, run 3, item A1)

The last field `unique` of `TailCores (Ext (H5Core x) x) x` (**`H5Ext.unique`**: the conserved
quantity `K − i` is determined by the core), hence **`H5Ext.tailCores`**, and the terminal
theorem **`hit5_not_fixedPoint`**: `hit5 x` is not βη-convertible to `x (hit5 x)`.
-/

set_option autoImplicit false

namespace TLCA4

/-- The syntactic hypotheses of `TailCores` (no closure under βη). -/
structure TailSyn (base : ℤ → ℤ → Lambda → Prop) (x : ℕ) : Prop where
  not_lam : ∀ {K i : ℤ} {c : Lambda}, base K i (.lam c) → False
  ne_var : ∀ {K i : ℤ} {P : Lambda} {n : ℕ}, base K i P → P ≠ .var n
  ne_bx : ∀ {K i : ℤ} {P Q : Lambda}, base K i P → P ≠ .app (.app lamB (.var x)) Q
  ne_bx1 : ∀ {K i : ℤ} {P Q : Lambda}, base K i P → P ≠ .app (bxPre x) Q
  unique : ∀ {K i K' i' : ℤ} {P : Lambda}, base K i P → base K' i' P → K - i = K' - i'

theorem TC.ne_varS {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailSyn base x) {K h : ℤ}
    {H : Lambda} (hH : TC (base K) x h H) (n : ℕ) : H ≠ .var n := by
  cases hH with
  | base hb => exact hc.ne_var hb
  | bx _ => simp
  | bx1 _ => simp
  | rq _ _ => simp

/-- **The conserved quantity `K − h` is determined by the chain.** -/
theorem TC.uniqueS {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailSyn base x) {K h : ℤ}
    {H : Lambda} (hH : TC (base K) x h H) :
    ∀ {K' h' : ℤ}, TC (base K') x h' H → K - h = K' - h' := by
  induction hH with
  | base hb =>
    intro K' h' hH'
    cases hH' with
    | base hb' => exact hc.unique hb hb'
    | bx _ => exact (hc.ne_bx hb rfl).elim
    | bx1 _ => exact (hc.ne_bx1 hb rfl).elim
    | rq _ _ => exact (hc.not_lam hb).elim
  | bx hP ih =>
    intro K' h' hH'
    generalize e : Lambda.app (.app lamB (.var x)) _ = t at hH'
    cases hH' with
    | base hb' => subst e; exact (hc.ne_bx hb' rfl).elim
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
    | base hb' => subst e; exact (hc.ne_bx1 hb' rfl).elim
    | bx _ => simp [lamB, bxPre] at e
    | bx1 hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := ih hP'
      omega
    | rq _ _ => simp at e
  | @rq i₀ i' m R T hR hm ih =>
    intro K' h' hH'
    generalize e : Lambda.lam (xPow (.var (x + 1)) m (.app (Lambda.lift 1 0 R) T)) = t at hH'
    cases hH' with
    | base hb' => subst e; exact (hc.not_lam hb').elim
    | bx _ => simp at e
    | bx1 _ => simp at e
    | @rq _ i'' m' R' T' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      have hA : Lambda.lift 1 0 R ≠ .var (x + 1) := by
        intro e'; cases R <;> simp [Lambda.lift] at e'; exact TC.ne_varS hc hR x (by rw [e'])
      have hA' : Lambda.lift 1 0 R' ≠ .var (x + 1) := by
        intro e'; cases R' <;> simp [Lambda.lift] at e'; exact TC.ne_varS hc hR' x (by rw [e'])
      obtain ⟨rfl, e1, -⟩ := xPow_app_unique hA hA' e
      obtain rfl := Lambda.lift_one_injective 0 e1
      have := ih hR'
      omega

/-- **The conserved quantity is determined through a two-argument chain.** -/
theorem TW.uniqueS {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailSyn base x) {K n : ℤ}
    {W : Lambda} (hW : TW (base K) x n W) {K' n' : ℤ} (hW' : TW (base K') x n' W) :
    K - n = K' - n' := by
  cases hW with
  | wB hR =>
    generalize e : Lambda.app lamB _ = t at hW'
    cases hW' with
    | wB hR' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      exact TC.uniqueS hc hR hR'
    | wP _ _ => cases e
    | wK _ => cases e
  | @wP i' m R T hR hm =>
    generalize e : Lambda.lam (.lam (xPow (.var (x + 2)) m
      (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))) = t at hW'
    cases hW' with
    | wB _ => cases e
    | @wP i'' m' R' T' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      obtain ⟨rfl, e1, -⟩ := xPow_app_unique (lift2_ne_var (TC.ne_varS hc hR x))
        (lift2_ne_var (TC.ne_varS hc hR' x)) e
      obtain rfl := Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 e1)
      have := TC.uniqueS hc hR hR'
      omega
    | @wK R' hR' =>
      simp only [Lambda.lam.injEq] at e
      obtain ⟨c0, rfl, e2⟩ := Lambda.lift_eq_lam e.symm
      cases hR' with
      | base hb => exact (hc.not_lam hb).elim
      | @rq _ i'' m'' R'' T'' hR'' hm'' =>
        rw [lift_xPow] at e2
        simp only [Lambda.lift] at e2
        rw [if_neg (by omega)] at e2
        have hA : Lambda.lift 1 1 (Lambda.lift 1 0 R'') ≠ .var (x + 1 + 1) := by
          rw [← lift_lift_zero_one]; exact lift2_ne_var (TC.ne_varS hc hR'' x)
        obtain ⟨rfl, e3, -⟩ := xPow_app_unique (lift2_ne_var (TC.ne_varS hc hR x)) hA e2
        rw [← lift_lift_zero_one] at e3
        obtain rfl := Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 e3)
        have := TC.uniqueS hc hR hR''
        omega
  | @wK R hR =>
    generalize e : Lambda.lam (Lambda.lift 1 0 R) = t at hW'
    cases hW' with
    | wB _ => cases e
    | @wP i'' m' R' T' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      obtain ⟨c0, rfl, e2⟩ := Lambda.lift_eq_lam e
      cases hR with
      | base hb => exact (hc.not_lam hb).elim
      | @rq _ i₂ m₂ R₂ T₂ hR₂ hm₂ =>
        rw [lift_xPow] at e2
        simp only [Lambda.lift] at e2
        rw [if_neg (by omega)] at e2
        have hA : Lambda.lift 1 1 (Lambda.lift 1 0 R₂) ≠ .var (x + 1 + 1) := by
          rw [← lift_lift_zero_one]; exact lift2_ne_var (TC.ne_varS hc hR₂ x)
        obtain ⟨rfl, e3, -⟩ := xPow_app_unique (lift2_ne_var (TC.ne_varS hc hR' x)) hA e2
        rw [← lift_lift_zero_one] at e3
        obtain rfl := Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 e3)
        have := TC.uniqueS hc hR₂ hR'
        omega
    | wK hR' =>
      simp only [Lambda.lam.injEq] at e
      obtain rfl := Lambda.lift_one_injective 0 e
      exact TC.uniqueS hc hR hR'


/-! ### Uniqueness of the conserved quantity for the extended cores of `hit5` -/

theorem TW.ne_lamM {base : ℤ → Lambda → Prop} {x : ℕ} {n : ℤ} (h : TW base x n lamM) : False := by
  generalize e : lamM = t at h
  cases h with
  | wB _ => simp [lamM] at e
  | wP _ _ => simp [lamM] at e
  | @wK R _ =>
    simp only [lamM, Lambda.lam.injEq] at e
    exact not_freeIn_lift_eq e.symm (Or.inl rfl)

/-- The three forms of a core of the extension. -/
theorem H5Ext.cases {x : ℕ} {K : ℤ} :
    ∀ (l : ℕ) {i : ℤ} {P : Lambda}, ExtL (H5Core x) x l K i P →
      H5Core x K i P ∨
      (∃ k W, P = .app lamM W ∧ TW (ExtL (H5Core x) x k K) x i W) ∨
      (∃ k W Y, P = .app W Y ∧ TW (ExtL (H5Core x) x k K) x i W)
  | 0, _, _, hl => .inl hl
  | l + 1, _, _, hl => by
    rcases hl with hl | ⟨W, rfl, hW⟩ | ⟨W, Y, rfl, hW⟩
    · exact H5Ext.cases l hl
    · exact .inr (.inl ⟨l, W, rfl, hW⟩)
    · exact .inr (.inr ⟨l, W, Y, rfl, hW⟩)

/-- Two cores of `H5Core` that are the same term have the same `K − n`. -/
theorem H5Core.unique {x : ℕ} {K i K' i' : ℤ} {P : Lambda} (h : H5Core x K i P)
    (h' : H5Core x K' i' P) : K - i = K' - i' := by
  cases h with
  | pq hP hQ hK =>
    cases h' with
    | pq hP' hQ' hK' =>
      have h1 := hP.index_unique hP'
      have h2 := hQ.index_unique hQ'
      subst h1 h2; omega
    | mq _ _ => exact hP.not_lamM.elim
    | mwq _ _ _ => exact hP.not_lamM.elim
    | wqy hW' _ _ => exact (hW'.not_HG_app hP).elim
  | mq hQ hK =>
    cases h' with
    | pq hP' _ _ => exact hP'.not_lamM.elim
    | mq hQ' hK' =>
      have h2 := hQ.index_unique hQ'
      subst h2; omega
    | mwq hW' _ _ => exact (hW'.not_HG_app hQ).elim
  | mwq hW hQ hK =>
    cases h' with
    | pq hP' _ _ => exact hP'.not_lamM.elim
    | mq hQ' _ => exact (hW.not_HG_app hQ').elim
    | mwq hW' hQ' hK' =>
      have h2 := hQ.index_unique hQ'
      subst h2; omega
  | wqy hW hQ hK =>
    cases h' with
    | pq hP' _ _ => exact (hW.not_HG_app hP').elim
    | wqy hW' hQ' hK' =>
      have h2 := hQ.index_unique hQ'
      subst h2; omega

theorem H5Core.not_extM {x : ℕ} {K i K' i' : ℤ} {k : ℕ} {W : Lambda}
    (h : H5Core x K i (.app lamM W)) (hW : TW (ExtL (H5Core x) x k K') x i' W) : False := by
  have hbv : ∀ {j : ℤ} {Q : Lambda} {n : ℕ}, ExtL (H5Core x) x k K' j Q → Q ≠ .var n :=
    fun hQ => H5ExtL.ne_var k hQ
  generalize e : Lambda.app lamM W = t at h
  cases h with
  | pq hP _ _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hP.not_lamM
  | mq hQ _ => simp only [Lambda.app.injEq, true_and] at e; subst e; exact hW.not_HG hbv hQ
  | mwq hW' _ _ =>
    simp only [Lambda.app.injEq, true_and] at e; subst e; exact hW.not_WT_app hW'
  | wqy _ _ _ => simp only [Lambda.app.injEq] at e; obtain ⟨e1, -⟩ := e; simp [lamM] at e1

theorem H5Core.not_extWY {x : ℕ} {K i K' i' : ℤ} {k : ℕ} {W Y : Lambda}
    (h : H5Core x K i (.app W Y)) (hW : TW (ExtL (H5Core x) x k K') x i' W) : False := by
  have hbv : ∀ {j : ℤ} {Q : Lambda} {n : ℕ}, ExtL (H5Core x) x k K' j Q → Q ≠ .var n :=
    fun hQ => H5ExtL.ne_var k hQ
  generalize e : Lambda.app W Y = t at h
  cases h with
  | pq hP _ _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hW.not_HG hbv hP
  | mq _ _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hW.ne_lamM
  | mwq _ _ _ => simp only [Lambda.app.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hW.ne_lamM
  | wqy hW' _ _ =>
    simp only [Lambda.app.injEq] at e; obtain ⟨rfl, rfl⟩ := e; exact hW.not_WT_app hW'

theorem H5Ext.unique_aux {x : ℕ} : ∀ (N : ℕ) {K i K' i' : ℤ} {P : Lambda},
    Lambda.nodes P ≤ N → Ext (H5Core x) x K i P → Ext (H5Core x) x K' i' P → K - i = K' - i' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro K i K' i' P hN h h'
  have hS : TailSyn (fun K j Q => Ext (H5Core x) x K j Q ∧ Lambda.nodes Q < Lambda.nodes P) x :=
    { not_lam := fun hb => Ext.not_lam H5Core.not_lam hb.1
      ne_var := fun hb => H5Ext.ne_var hb.1
      ne_bx := fun hb => H5Ext.ne_bx hb.1
      ne_bx1 := fun hb => H5Ext.ne_bx1 hb.1
      unique := fun hb hb' => ih _ (by have := hb.2; omega) le_rfl hb.1 hb'.1 }
  have toS : ∀ {k : ℕ} {K j : ℤ} {W : Lambda}, TW (ExtL (H5Core x) x k K) x j W →
      Lambda.nodes W < Lambda.nodes P →
      TW (fun j Q => Ext (H5Core x) x K j Q ∧ Lambda.nodes Q < Lambda.nodes P) x j W :=
    fun hW hlt => hW.restrict.mono (fun hQ => ⟨⟨_, hQ.1⟩, by have := hQ.2; omega⟩)
  obtain ⟨l, hl⟩ := h
  obtain ⟨l', hl'⟩ := h'
  rcases H5Ext.cases l hl with hc | ⟨k, W, rfl, hW⟩ | ⟨k, W, Y, rfl, hW⟩ <;>
    rcases H5Ext.cases l' hl' with hc' | ⟨k', W', e', hW'⟩ | ⟨k', W', Y', e', hW'⟩
  · exact hc.unique hc'
  · subst e'; exact (hc.not_extM hW').elim
  · subst e'; exact (hc.not_extWY hW').elim
  · exact (hc'.not_extM hW).elim
  · simp only [Lambda.app.injEq, true_and] at e'
    subst e'
    exact TW.uniqueS hS (toS hW (by simp only [Lambda.nodes_app]; omega))
      (toS hW' (by simp only [Lambda.nodes_app]; omega))
  · simp only [Lambda.app.injEq] at e'
    obtain ⟨rfl, -⟩ := e'
    exact hW'.ne_lamM.elim
  · exact (hc'.not_extWY hW).elim
  · simp only [Lambda.app.injEq] at e'
    obtain ⟨rfl, -⟩ := e'
    exact hW.ne_lamM.elim
  · simp only [Lambda.app.injEq] at e'
    obtain ⟨rfl, -⟩ := e'
    exact TW.uniqueS hS (toS hW (by simp only [Lambda.nodes_app]; omega))
      (toS hW' (by simp only [Lambda.nodes_app]; omega))

/-- **The conserved quantity of an extended core of `hit5` is unique.** -/
theorem H5Ext.unique {x : ℕ} {K i K' i' : ℤ} {P : Lambda} (h : Ext (H5Core x) x K i P)
    (h' : Ext (H5Core x) x K' i' P) : K - i = K' - i' :=
  H5Ext.unique_aux _ le_rfl h h'

/-- **The extended cores of `hit5` satisfy the hypotheses of the shape argument.** -/
theorem H5Ext.tailCores (x : ℕ) : TailCores (Ext (H5Core x) x) x where
  step := H5Ext.step
  not_lam := Ext.not_lam H5Core.not_lam
  ne_var := H5Ext.ne_var
  ne_bx := H5Ext.ne_bx
  ne_bx1 := H5Ext.ne_bx1
  unique := H5Ext.unique

/-- **`hit5` is not a βη fixed-point combinator**: `hit5 x` is not βη-convertible to
`x (hit5 x)`. -/
theorem hit5_not_fixedPoint (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit5 (Tm.var x)))
      (.app (.var x) (toLam (actList hit5 (Tm.var x)))) :=
  hit5_not_fixedPoint_of_tailCores x (H5Ext.tailCores x)

end TLCA4
