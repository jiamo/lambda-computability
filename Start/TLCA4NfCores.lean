import Start.TLCA4NfGrammar

/-!
# TLCA open problem 4: the cores of normalized stages satisfy `TailCores`
(row M20-TLCA4-BETAETA; big round 2, item A2, rebuilt in run 6 after the move to a new project)

* **`NG.index_unique`**, `NC.height_unique`, `NB.height_unique` — the index of a component (the
  height of a chain, of a core) is determined by the term;
* `qG_subst`, `NB.substQ` — substituting a component `Q` of index `j` for `q`: `q G_q ↦ Q G_Q`, a
  core `P Q` of indices `(j, j + 1)`; `R q ↦ R Q`;
* `NCore x K n` — the top-level cores `P Q` (indices `i`, `j`, `K + i = tri j + n`);
  **`NCore.step`**, **`NCore.tailCores`** (no extension `Ext` needed);
* **`not_fixedPoint_of_nf`** — if `L →βη S S ρ` with `S` a component of index `0`, then
  `¬ L =βη x L`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

theorem lift_eq_var_succ {R : Lambda} {k : ℕ} (h : Lambda.lift 1 0 R = .var (k + 1)) :
    R = .var k := by
  cases R <;> simp [Lambda.lift] at h; simp [h]

theorem qG_ne_var (x : ℕ) (T : Lambda) (j : ℕ) : qG x T ≠ .var j := by
  simp [qG]

theorem NB.cases_app {x : ℕ} {n : ℤ} {P : Lambda} (h : NB x n P) :
    (∃ T, P = .app (.var 0) (qG x T)) ∨ (∃ R, P = .app (Lambda.lift 1 0 R) (.var 0)) := by
  cases h with
  | q => exact .inl ⟨_, rfl⟩
  | comp _ _ => exact .inr ⟨_, rfl⟩

mutual
theorem NG.index_unique {x i i' : ℕ} {P : Lambda} (h : NG x i P) (h' : NG x i' P) : i = i' := by
  match h with
  | .lam hc hn =>
    cases h' with
    | lam hc' hn' =>
      have := NC.height_unique hc hc'
      omega
theorem NB.height_unique {x : ℕ} {n n' : ℤ} {P : Lambda} (h : NB x n P) (h' : NB x n' P) :
    n = n' := by
  match h with
  | @NB.q _ T =>
    generalize e : Lambda.app (.var 0) (qG x T) = t at h'
    cases h' with
    | q => rfl
    | comp _ _ =>
      simp only [Lambda.app.injEq] at e
      exact (qG_ne_var _ _ 0 e.2).elim
  | .comp hR hn =>
    generalize e : Lambda.app (Lambda.lift 1 0 _) (.var 0) = t at h'
    cases h' with
    | q =>
      simp only [Lambda.app.injEq] at e
      exact absurd e.2 (qG_ne_var _ _ 0).symm
    | comp hR' hn' =>
      simp only [Lambda.app.injEq, and_true] at e
      obtain rfl := Lambda.lift_one_injective 0 e
      have := NG.index_unique hR hR'
      subst hn hn'
      rw [this]
theorem NC.height_unique {x : ℕ} {n n' : ℤ} {P : Lambda} (h : NC x n P) (h' : NC x n' P) :
    n = n' := by
  match h with
  | .base hb =>
    cases h' with
    | base hb' => exact NB.height_unique hb hb'
    | bx hP' =>
      rcases hb.cases_app with ⟨T, e⟩ | ⟨R, e⟩
      · simp [lamB] at e
      · simp only [Lambda.app.injEq] at e
        exact (hP'.ne_var e.2).elim
    | bx1 hP' =>
      rcases hb.cases_app with ⟨T, e⟩ | ⟨R, e⟩
      · simp [bxPre] at e
      · simp only [Lambda.app.injEq] at e
        exact (hP'.ne_var e.2).elim
    | rq _ _ => exact hb.not_lam.elim
  | .bx hP =>
    generalize e : Lambda.app (.app lamB (.var (x + 1))) _ = t at h'
    cases h' with
    | base hb' =>
      rcases hb'.cases_app with ⟨T, e'⟩ | ⟨R, e'⟩
      · rw [← e] at e'; simp [lamB] at e'
      · rw [← e] at e'
        simp only [Lambda.app.injEq] at e'
        exact (hP.ne_var e'.2).elim
    | bx hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := NC.height_unique hP hP'
      omega
    | bx1 _ => simp [lamB, bxPre] at e
    | rq _ _ => cases e
  | .bx1 hP =>
    generalize e : Lambda.app (bxPre (x + 1)) _ = t at h'
    cases h' with
    | base hb' =>
      rcases hb'.cases_app with ⟨T, e'⟩ | ⟨R, e'⟩
      · rw [← e] at e'; simp [bxPre] at e'
      · rw [← e] at e'
        simp only [Lambda.app.injEq] at e'
        exact (hP.ne_var e'.2).elim
    | bx _ => simp [lamB, bxPre] at e
    | bx1 hP' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      have := NC.height_unique hP hP'
      omega
    | rq _ _ => cases e
  | @NC.rq _ _ i₁ m R T hR hm =>
    generalize e : Lambda.lam (xPow (.var (x + 2)) m (.app (Lambda.lift 1 0 R) T)) = t at h'
    cases h' with
    | base hb' => subst e; exact hb'.not_lam.elim
    | bx _ => cases e
    | bx1 _ => cases e
    | @rq _ i₂ m' R' T' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      have hA : Lambda.lift 1 0 R ≠ .var (x + 2) := by
        intro e'; exact hR.ne_var (lift_eq_var_succ e')
      have hA' : Lambda.lift 1 0 R' ≠ .var (x + 2) := by
        intro e'; exact hR'.ne_var (lift_eq_var_succ e')
      obtain ⟨rfl, e1, -⟩ := xPow_app_unique hA hA' e
      obtain rfl := Lambda.lift_one_injective 0 e1
      have := NC.height_unique hR hR'
      omega
end

/-- Chains under `q` are `TC` chains over the cores `NB`. -/
theorem NC.toTC {x : ℕ} {n : ℤ} {P : Lambda} (h : NC x n P) : TC (NB x) (x + 1) n P :=
  match h with
  | .base hb => .base hb
  | .bx h' => .bx (NC.toTC h')
  | .bx1 h' => .bx1 (NC.toTC h')
  | .rq h' hm => .rq (NC.toTC h') hm

/-! ### Top-level cores -/

/-- The top-level cores `P Q` (components of indices `i`, `j`), with the conserved quantity `K`. -/
inductive NCore (x : ℕ) (K : ℤ) : ℤ → Lambda → Prop
  | pq {i j : ℕ} {n : ℤ} {P Q : Lambda} : NG x i P → NG x j Q →
      K + i = (tri j : ℤ) + n → NCore x K n (.app P Q)

/-- `G_q` with a component `Q` substituted for `q` is a component of the next index. -/
theorem qG_subst {x j : ℕ} {Q : Lambda} (hQ : NG x j Q) (T : Lambda) :
    NG x (j + 1) (Lambda.subst Q 0 (qG x T)) := by
  have e : Lambda.subst Q 0 (qG x T) = .lam (.lam (xPow (.var (x + 2)) 1
      (.app (Lambda.lift 1 0 (.app (Lambda.lift 1 0 Q) (.var 0)))
        (Lambda.subst (Lambda.lift 1 0 (Lambda.lift 1 0 Q)) 2 T)))) := by
    simp [qG, Lambda.subst, xPow, Lambda.lift, lift_lift_zero_one]
  rw [e]
  exact .lam (.rq (m := 1) (.base (.comp hQ rfl)) rfl) (by push_cast; ring)

/-- Substituting a component for `q` in a core under `q`. -/
theorem NB.substQ {x j : ℕ} {K : ℤ} {Q : Lambda} (hQ : NG x j Q) {h : ℤ} {P : Lambda}
    (hP : NB x h P) : NCore x K (h + (K - tri j - 1)) (Lambda.subst Q 0 P) := by
  cases hP with
  | @q T =>
    simp only [Lambda.subst, if_pos]
    refine .pq hQ (qG_subst hQ T) ?_
    rw [tri_succ_int]; ring
  | @comp i' _ R hR hn =>
    simp only [Lambda.subst, Lambda.subst_lift, if_pos]
    refine .pq hR hQ ?_
    subst hn; ring

/-- **Every βη-step of a top-level core is a chain over the cores.** -/
theorem NCore.step {x : ℕ} {K n : ℤ} {P P' : Lambda} (h : NCore x K n P)
    (hs : betaEtaStep P P') : TC (NCore x K) x n P' := by
  cases h with
  | @pq i j _ P Q hP hQ hK =>
    rcases betaEtaStep_app_cases hs with ⟨c, rfl, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
    · have hc := hP.fire_q
      have := hc.toTC.subst_gen (core := NCore x K) (Q := Q) (s := K - tri j - 1)
        (fun hb => hb.substQ hQ)
      rwa [show (i : ℤ) + 1 + (K - tri j - 1) = n by omega] at this
    · exact .base (.pq (hP.step hf) hQ hK)
    · exact .base (.pq hP (hQ.step ha) hK)

/-- The body of `bxPre` is not a chain. -/
theorem NC.ne_bxPreBody {x : ℕ} {n : ℤ}
    (h : NC x n (.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0))))) : False := by
  generalize e : Lambda.lam (.app (.var (x + 2)) (.app (.var 1) (.var 0))) = t at h
  cases h with
  | base hb => subst e; exact hb.not_lam
  | bx _ => cases e
  | bx1 _ => cases e
  | @rq _ _ m R T hR _ =>
    simp only [Lambda.lam.injEq] at e
    match m, e with
    | 0, e =>
      simp only [xPow, Lambda.app.injEq] at e
      exact hR.ne_var (lift_eq_var_succ e.1.symm)
    | 1, e =>
      simp only [xPow, Lambda.app.injEq, true_and] at e
      exact hR.ne_var (lift_eq_var_succ (k := 0) e.1.symm)
    | k + 2, e =>
      simp only [xPow, Lambda.app.injEq, true_and] at e
      cases k <;> simp [xPow] at e

/-- **The top-level cores satisfy the hypotheses of the shape argument.** -/
theorem NCore.tailCores (x : ℕ) : TailCores (NCore x) x where
  step := NCore.step
  not_lam := by intro K i c h; cases h
  ne_var := by intro K i P n h; cases h; simp
  ne_bx := by
    intro K i P Q h e
    cases h with
    | pq hP _ _ =>
      obtain ⟨c, rfl⟩ := hP.exists_lam
      simp at e
  ne_bx1 := by
    intro K i P Q h e
    cases h with
    | pq hP _ _ =>
      simp only [bxPre, Lambda.app.injEq] at e
      obtain ⟨rfl, -⟩ := e
      exact (hP.fire_q).ne_bxPreBody
  unique := by
    intro K i K' i' P h h'
    cases h with
    | pq hP hQ hK =>
      generalize e : Lambda.app _ _ = t at h'
      cases h' with
      | pq hP' hQ' hK' =>
        simp only [Lambda.app.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        have h1 := hP.index_unique hP'
        have h2 := hQ.index_unique hQ'
        subst h1 h2
        omega

/-- **The generic non-fixed-point theorem for normalized stages**: if `L` βη-reduces to
`S S ρ` with `S` a component of index `0`, then `L` is not βη-convertible to `x L`. -/
theorem not_fixedPoint_of_nf {x : ℕ} {L S ρ : Lambda} (hS : NG x 0 S)
    (hL : betaEtaReduces L (.app (.app S S) ρ)) : ¬ Lambda.betaEtaConv L (.app (.var x) L) :=
  not_fixedPoint_of_ashape (NCore.tailCores x) hL
    ⟨0, 0, _, ρ, rfl, .base (.pq hS hS (by simp [tri]))⟩

end TLCA4
