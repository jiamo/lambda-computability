import Start.TLCA4TailRestrict

/-!
# TLCA open problem 4: extending a core family by two-argument heads
(row M20-TLCA4-BETAETA; series V, big round, run 9, item A3)

The cores of hit5 include `M W` and `W Y` with `W` a two-argument chain (`TW`) over the core
family itself (`s Z ρ →w M (w Z) ρ →w w Z (w Z) ρ`, `w Z →w B (v Z)`).  Since this cannot be a
nested inductive, the extension is defined by levels:

* `ExtL core x 0 = core`, `ExtL core x (k+1) = ExtL core x k ∪ {M W, W Y : W ∈ TW (ExtL core x k)}`;
* `Ext core x K n P = ∃ k, ExtL core x k K n P`;
* `ExtL.not_lam` — no member is an abstraction (if no core is);
* **`Ext.step`** — if every βη-step of a core is a chain over `Ext core x K`, then so is every
  βη-step of a member of `Ext core x K` (strong induction on `Lambda.nodes`, with `TW.step2` on the
  base restricted to smaller terms and `TW.fire` for the root steps);
* **`TW.unique`** — for a core family with `TailCores`, a two-argument chain determines `K − n`
  (towards the uniqueness field for the cores `M W`, `W Y` of the extension).
-/

set_option autoImplicit false

namespace TLCA4

open Lambda (betaEtaReduces betaEtaStep)

/-- The levels of the extension of a core family by the heads `M W` and `W Y`, `W ∈ TW`. -/
def ExtL (core : ℤ → ℤ → Lambda → Prop) (x : ℕ) : ℕ → ℤ → ℤ → Lambda → Prop
  | 0 => core
  | k + 1 => fun K n P => ExtL core x k K n P ∨
      (∃ W, P = .app lamM W ∧ TW (ExtL core x k K) x n W) ∨
      (∃ W Y, P = .app W Y ∧ TW (ExtL core x k K) x n W)

/-- The extension of a core family by the heads `M W` and `W Y`, `W ∈ TW`. -/
def Ext (core : ℤ → ℤ → Lambda → Prop) (x : ℕ) (K n : ℤ) (P : Lambda) : Prop :=
  ∃ k, ExtL core x k K n P

theorem ExtL.not_lam {core : ℤ → ℤ → Lambda → Prop} {x : ℕ}
    (hcl : ∀ {K n : ℤ} {c : Lambda}, core K n (.lam c) → False) :
    ∀ {k : ℕ} {K n : ℤ} {c : Lambda}, ExtL core x k K n (.lam c) → False
  | 0, _, _, _, h => hcl h
  | k + 1, _, _, _, h => by
    rcases h with h | ⟨W, e, -⟩ | ⟨W, Y, e, -⟩
    · exact ExtL.not_lam hcl h
    · cases e
    · cases e

theorem ExtL.to_ext {core : ℤ → ℤ → Lambda → Prop} {x : ℕ} {k : ℕ} {K : ℤ} :
    ∀ {n : ℤ} {P : Lambda}, ExtL core x k K n P → Ext core x K n P :=
  fun h => ⟨_, h⟩

/-- **The extension is closed under βη-steps, given closure of the cores.** -/
theorem ExtL.step {core : ℤ → ℤ → Lambda → Prop} {x : ℕ}
    (hcore : ∀ {K n : ℤ} {P P' : Lambda}, core K n P → betaEtaStep P P' →
      TC (Ext core x K) x n P')
    (hcl : ∀ {K n : ℤ} {c : Lambda}, core K n (.lam c) → False) :
    ∀ (N k : ℕ) {K n : ℤ} {P P' : Lambda}, Lambda.nodes P ≤ N → ExtL core x k K n P →
      betaEtaStep P P' → TC (Ext core x K) x n P' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ihN =>
  intro k
  induction k with
  | zero => intro K n P P' _ h hs; exact hcore h hs
  | succ k ihk =>
    intro K n P P' hN h hs
    -- steps of a head `W ∈ TW (ExtL k K)` of fewer nodes than `P`
    have hW : ∀ {W W' : Lambda}, Lambda.nodes W < Lambda.nodes P →
        TW (ExtL core x k K) x n W → betaEtaStep W W' → ∃ k', TW (ExtL core x k' K) x n W' := by
      intro W W' hlt hW hsW
      have h2 := TW.step2 (base := fun j Q => ExtL core x k K j Q ∧ Lambda.nodes Q < Lambda.nodes W)
        (base' := Ext core x K) (fun hQ => ⟨k, hQ.1⟩)
        (fun hQ hsQ => ihN (Lambda.nodes _) (by omega) k le_rfl hQ.1 hsQ)
        (fun hQ => ExtL.not_lam hcl hQ.1) hW.restrict hsW
      exact TW.exists_level (F := fun k' => ExtL core x k' K) h2
    rcases h with h | ⟨W, rfl, hWk⟩ | ⟨W, Y, rfl, hWk⟩
    · exact ihk hN h hs
    · rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · simp only [lamM, Lambda.lam.injEq] at hc
        subst hc
        simp only [Lambda.subst, if_pos]
        exact .base ⟨k + 1, .inr (.inr ⟨W, W, rfl, hWk⟩)⟩
      · exact (nf_lamM _ hf).elim
      · obtain ⟨k', hk'⟩ := hW (by simp only [Lambda.nodes_app]; omega) hWk ha
        exact .base ⟨k' + 1, .inr (.inl ⟨a', rfl, hk'⟩)⟩
    · rcases betaEtaStep_app_cases hs with ⟨c, hc, rfl⟩ | ⟨f', hf, rfl⟩ | ⟨a', ha, rfl⟩
      · exact (hWk.fire hc Y).mono (fun hQ => ⟨k, hQ⟩)
      · obtain ⟨k', hk'⟩ := hW (by simp only [Lambda.nodes_app]; omega) hWk hf
        exact .base ⟨k' + 1, .inr (.inr ⟨f', Y, rfl, hk'⟩)⟩
      · exact .base ⟨k + 1, .inr (.inr ⟨W, a', rfl, hWk⟩)⟩

/-- **Closure of the extension under one βη-step.** -/
theorem Ext.step {core : ℤ → ℤ → Lambda → Prop} {x : ℕ}
    (hcore : ∀ {K n : ℤ} {P P' : Lambda}, core K n P → betaEtaStep P P' →
      TC (Ext core x K) x n P')
    (hcl : ∀ {K n : ℤ} {c : Lambda}, core K n (.lam c) → False)
    {K n : ℤ} {P P' : Lambda} (h : Ext core x K n P) (hs : betaEtaStep P P') :
    TC (Ext core x K) x n P' := by
  obtain ⟨k, hk⟩ := h
  exact ExtL.step hcore hcl _ k le_rfl hk hs

theorem Ext.not_lam {core : ℤ → ℤ → Lambda → Prop} {x : ℕ}
    (hcl : ∀ {K n : ℤ} {c : Lambda}, core K n (.lam c) → False)
    {K n : ℤ} {c : Lambda} (h : Ext core x K n (.lam c)) : False := by
  obtain ⟨k, hk⟩ := h
  exact ExtL.not_lam hcl hk


/-! ### Uniqueness through two-argument chains -/

theorem lift2_ne_var {R : Lambda} {x : ℕ} (h : R ≠ .var x) :
    Lambda.lift 1 0 (Lambda.lift 1 0 R) ≠ .var (x + 2) := by
  intro e
  cases R with
  | var n =>
    simp only [Lambda.lift] at e
    split at e <;> simp at e
    · omega
    · exact h (by congr 1)
  | app _ _ => simp [Lambda.lift] at e
  | lam _ => simp [Lambda.lift] at e

/-- **The conserved quantity is determined through a two-argument chain.** -/
theorem TW.unique {base : ℤ → ℤ → Lambda → Prop} {x : ℕ} (hc : TailCores base x) {K n : ℤ}
    {W : Lambda} (hW : TW (base K) x n W) {K' n' : ℤ} (hW' : TW (base K') x n' W) :
    K - n = K' - n' := by
  cases hW with
  | wB hR =>
    generalize e : Lambda.app lamB _ = t at hW'
    cases hW' with
    | wB hR' =>
      simp only [Lambda.app.injEq, true_and] at e
      subst e
      exact hR.unique hc hR'
    | wP _ _ => cases e
    | wK _ => cases e
  | @wP i' m R T hR hm =>
    generalize e : Lambda.lam (.lam (xPow (.var (x + 2)) m
      (.app (Lambda.lift 1 0 (Lambda.lift 1 0 R)) T))) = t at hW'
    cases hW' with
    | wB _ => cases e
    | @wP i'' m' R' T' hR' hm' =>
      simp only [Lambda.lam.injEq] at e
      obtain ⟨rfl, e1, -⟩ := xPow_app_unique (lift2_ne_var (hR.ne_var hc x))
        (lift2_ne_var (hR'.ne_var hc x)) e
      obtain rfl := Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 e1)
      have := hR.unique hc hR'
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
          rw [← lift_lift_zero_one]; exact lift2_ne_var (hR''.ne_var hc x)
        obtain ⟨rfl, e3, -⟩ := xPow_app_unique (lift2_ne_var (hR.ne_var hc x)) hA e2
        rw [← lift_lift_zero_one] at e3
        obtain rfl := Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 e3)
        have := hR.unique hc hR''
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
          rw [← lift_lift_zero_one]; exact lift2_ne_var (hR₂.ne_var hc x)
        obtain ⟨rfl, e3, -⟩ := xPow_app_unique (lift2_ne_var (hR'.ne_var hc x)) hA e2
        rw [← lift_lift_zero_one] at e3
        obtain rfl := Lambda.lift_one_injective 0 (Lambda.lift_one_injective 0 e3)
        have := hR₂.unique hc hR'
        omega
    | wK hR' =>
      simp only [Lambda.lam.injEq] at e
      obtain rfl := Lambda.lift_one_injective 0 e
      exact hR.unique hc hR'

end TLCA4
