/-
# The infinite η-expansion of the identity in `D∞`

`Start/DinfWadsworthSharp.lean` isolates the one semantic principle that is still missing for full
abstraction of Scott's `D∞`, and explains why no *finite* inductive witness relation can decide the
`D∞` order: the model identifies a term with its infinite η-expansion.  This file makes that
phenomenon precise and proves it.

Let `J` be the closed term obtained from Turing's fixed-point combinator by

  `J = Θ (λj x y. x (j y))`,   so that   `J →* λx y. x (J y)`.

Unfolding the recursion, `J x = λy. x (J y) = λy. x (λy'. y (J y'))= …`, so `J` is the *infinite*
η-expansion of the identity: it is β-convertible to no η-expansion of `λx. x` of any finite depth,
yet in `D∞` the two are equal.

The proof is organised around a purely semantic statement about `D∞` which is of independent
interest:

* `ScottDinf.eq_dId_of_eta_fixpoint` — if `x : D∞` satisfies the two equations
  `x · y · z = y · (x · z)` and `x · ⊥ = ⊥`, then `x` is the identity.

The engine behind it is a family of general lemmas about the finite approximations `theta n`:

* `ScottDinf.theta_le_iff` — `theta n x ≤ v` is decided at level `n` alone;
* `ScottDinf.theta_succ_le_of_forall_psi`, `ScottDinf.le_of_forall_psi` — criteria for
  `theta (n+1) x ≤ v` and for `x ≤ v` which only ever apply `x` and `v` to elements of the image
  of `psiFun n`;
* `ScottDinf.Phi_psi_succ_app` — a function coming from level `n+1` computes at level `n` exactly
  as its level-`(n+1)` component says;
* `ScottDinf.Phi_bot_app_zero` — the base level of application.

The two equations cannot be replaced by finitely many η-expansions: the proof proceeds by two
simultaneous inductions over the levels of the inverse limit (`ScottDinf.psi_le_Phi_of_eta_fixpoint`
and `ScottDinf.theta_Phi_le_psi_of_eta_fixpoint`), and the limit step is exactly the point where a
finite witness would be needed.

Main syntactic results:

* `ScottDinf.Jterm_reduces` — `J →* λx y. x (J y)`;
* `ScottDinf.ddenot_Jterm_eq_ddenot_id` — **`⟦J⟧ = ⟦I⟧` in `D∞`**;
* `ScottDinf.obsEqHnf_Jterm_id` — hence `J` and the identity are observationally equivalent;
* `ScottDinf.ddenot_app_Jterm`, `ScottDinf.obsEqHnf_app_Jterm` — `J M` is indistinguishable
  from `M` for every term `M`;
* `ScottDinf.not_conv_Jterm_I` — the identification is not a β-conversion: the graph model, which
  is sound for β but not extensional, separates `J` from the identity.
-/

import Start.DinfApprox
import Start.FixedPoint
import Start.FreeVars

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

noncomputable section

/-! ## General facts about the finite approximations -/

/-- The embedding of the least element of any level is the least element of `D∞`. -/
theorem psiFun_botD (n : ℕ) : psiFun n (botD n) = Dinf.botDinf :=
  le_antisymm (psi_le_iff.mpr (botD_le _ _)) (Dinf.botDinf_le _)

/-- `theta n x ≤ v` only depends on level `n`. -/
theorem theta_le_iff {n : ℕ} {x v : Dinf} : theta n x ≤ v ↔ x.app n ≤ v.app n := by
  constructor
  · intro h
    have h' := Dinf.le_def.mp h n
    rwa [← psi_theta, psiFun_app_self] at h'
  · intro h
    rw [← psi_theta, psi_le_iff]
    exact h

/-- Elements coming from level `n` are their own level-`n` approximation. -/
theorem theta_psiFun (n : ℕ) (z : D n) : theta n (psiFun n z) = psiFun n z := by
  rw [← psi_theta, psiFun_app_self]

/-- An element is the supremum of its finite approximations. -/
theorem le_of_forall_theta_le {x v : Dinf} (h : ∀ n, theta n x ≤ v) : x ≤ v := by
  rw [← ωSup_thetaChain x]
  exact ωSup_le _ _ h

/-- **The engine.**  To prove `theta (n+1) x ≤ v` it suffices to compare `x` and `v` on the
image of `psiFun n`, and only up to level `n`. -/
theorem theta_succ_le_of_forall_psi {n : ℕ} {x v : Dinf}
    (h : ∀ z : D n, theta n (Phi x (psiFun n z)) ≤ Phi v (psiFun n z)) :
    theta (n + 1) x ≤ v := by
  rw [← psi_theta, psi_le_iff, toFn_le_iff]
  intro z
  have h1 := theta_le_iff.mp (h z)
  rwa [Phi_app_psi, Phi_app_psi] at h1

/-- **Extensionality at the finite levels.**  To prove `x ≤ v` it suffices to compare `x` and `v`
on the image of each `psiFun n`, and only up to level `n`. -/
theorem le_of_forall_psi {x v : Dinf}
    (h : ∀ (n : ℕ) (z : D n), theta n (Phi x (psiFun n z)) ≤ Phi v (psiFun n z)) : x ≤ v := by
  refine le_of_forall_theta_le fun n => ?_
  exact le_trans (theta_mono (Nat.le_succ n) x) (theta_succ_le_of_forall_psi (h n))

/-! ## Application of an element coming from a finite level -/

/-- Above level `n`, the approximating chain of `psiFun (n+1) z` has constant `n`-th component. -/
theorem appChain_psi_succ_app (n : ℕ) (z : D (n + 1)) (u : Dinf) :
    ∀ m, n ≤ m → (appChain (psiFun (n + 1) z) m u).app n = toFn z (u.app n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp only [appChain_apply, psiFun_app_self]
  | succ m hm ih =>
      rw [appChain_apply, psi_succ_app_of_le _ hm]
      have hx : (psiFun (n + 1) z).app (m + 1 + 1)
          = emb (m + 1) ((psiFun (n + 1) z).app (m + 1)) := by
        rw [psiFun_app, psiFun_app, psiSeq_of_gt z (by omega)]
      rw [hx, emb_succ_apply, prj_emb, u.coherent]
      exact ih

/-- **An element coming from level `n+1` computes at level `n` by its own component.** -/
theorem Phi_psi_succ_app (n : ℕ) (z : D (n + 1)) (u : Dinf) :
    (Phi (psiFun (n + 1) z) u).app n = toFn z (u.app n) := by
  rw [Phi_apply, Dinf.ωSup_app]
  refine le_antisymm (ωSup_le _ _ ?_) ?_
  · intro m
    change (appChain (psiFun (n + 1) z) m u).app n ≤ toFn z (u.app n)
    rcases Nat.le_total n m with hm | hm
    · exact le_of_eq (appChain_psi_succ_app n z u m hm)
    · have hle : appChain (psiFun (n + 1) z) m u ≤ appChain (psiFun (n + 1) z) n u :=
        (appChain (psiFun (n + 1) z)).monotone hm _
      refine le_trans (Dinf.le_def.mp hle n) ?_
      exact le_of_eq (appChain_psi_succ_app n z u n (le_refl n))
  · exact le_ωSup_of_le n (le_of_eq (appChain_psi_succ_app n z u n (le_refl n)).symm)

/-! ## Application at the base level -/

theorem appChain_bot_app_zero (x : Dinf) :
    ∀ m, (appChain x m Dinf.botDinf).app 0 = x.app 0 := by
  intro m
  induction m with
  | zero =>
      rw [appChain_apply, psiFun_app_self, Dinf.botDinf_app, ← prj_zero_apply, x.coherent 0]
  | succ m ih =>
      rw [appChain_apply, psi_succ_app_of_le _ (Nat.zero_le m)]
      have hb : Dinf.botDinf.app (m + 1) = emb m (botD m) := by
        rw [Dinf.botDinf_app, emb_botD]
      rw [hb, ← prj_succ_apply m (x.app (m + 1 + 1)) (botD m), x.coherent (m + 1),
        ← Dinf.botDinf_app m]
      exact ih

/-- Applying to `⊥` does not change the base level. -/
theorem Phi_bot_app_zero (x : Dinf) : (Phi x Dinf.botDinf).app 0 = x.app 0 := by
  rw [Phi_apply, Dinf.ωSup_app]
  refine le_antisymm (ωSup_le _ _ ?_) ?_
  · intro m
    exact le_of_eq (appChain_bot_app_zero x m)
  · exact le_ωSup_of_le 0 (le_of_eq (appChain_bot_app_zero x 0).symm)

/-! ## The identity of `D∞` -/

/-- The identity element of `D∞`. -/
def dId : Dinf := dlamAny (fun y => y)

theorem Phi_dId (y : Dinf) : Phi dId y = y := Phi_dlamAny ωScottContinuous.id y

theorem ddenot_id (ρ : DEnv) : ddenot Lambda.I ρ = dId := by
  rw [Lambda.I, ddenot_lam]
  exact dlamAny_congr fun _ => rfl

/-! ## Elements satisfying the η-limit equations -/

section EtaFixpoint

variable {x : Dinf}

/-- Under the two equations, applying `x` never changes the base level. -/
theorem Phi_app_zero_of_eta_fixpoint
    (hA : ∀ y z : Dinf, Phi (Phi x y) z = Phi y (Phi x z))
    (hB : Phi x Dinf.botDinf = Dinf.botDinf) (w : Dinf) :
    (Phi x w).app 0 = w.app 0 := by
  calc (Phi x w).app 0 = (Phi (Phi x w) Dinf.botDinf).app 0 := (Phi_bot_app_zero _).symm
    _ = (Phi w (Phi x Dinf.botDinf)).app 0 := by rw [hA]
    _ = (Phi w Dinf.botDinf).app 0 := by rw [hB]
    _ = w.app 0 := Phi_bot_app_zero w

/-- **First induction**: `x` is above the identity on every finite level. -/
theorem psi_le_Phi_of_eta_fixpoint
    (hA : ∀ y z : Dinf, Phi (Phi x y) z = Phi y (Phi x z))
    (hB : Phi x Dinf.botDinf = Dinf.botDinf) :
    ∀ (n : ℕ) (z : D n), psiFun n z ≤ Phi x (psiFun n z) := by
  intro n
  induction n with
  | zero =>
      intro z
      refine psi_le_iff.mpr ?_
      rw [Phi_app_zero_of_eta_fixpoint hA hB, psiFun_app_self]
  | succ n ih =>
      intro z
      have hmain : theta (n + 1) (psiFun (n + 1) z) ≤ Phi x (psiFun (n + 1) z) := by
        refine theta_succ_le_of_forall_psi ?_
        intro u
        rw [hA]
        exact le_trans (theta_le _ _)
          ((Phi (psiFun (n + 1) z)).monotone (ih u))
      rwa [theta_psiFun] at hmain

/-- **Second induction**: `x` is below the identity on every finite level. -/
theorem theta_Phi_le_psi_of_eta_fixpoint
    (hA : ∀ y z : Dinf, Phi (Phi x y) z = Phi y (Phi x z))
    (hB : Phi x Dinf.botDinf = Dinf.botDinf) :
    ∀ (n : ℕ) (z : D n), theta n (Phi x (psiFun n z)) ≤ psiFun n z := by
  intro n
  induction n with
  | zero =>
      intro z
      refine theta_le_iff.mpr ?_
      rw [Phi_app_zero_of_eta_fixpoint hA hB]
  | succ n ih =>
      intro z
      refine theta_succ_le_of_forall_psi ?_
      intro u
      rw [hA, theta_le_iff, Phi_psi_succ_app, Phi_psi_succ_app]
      exact (toFn z).monotone (theta_le_iff.mp (ih u))

/-- **The η-limit equations characterise the identity of `D∞`.**

If `x · y · z = y · (x · z)` for all `y, z` and `x · ⊥ = ⊥`, then `x` is the identity.  The
hypotheses say exactly that `x` behaves like the infinite η-expansion of the identity; no finite
amount of η-expansion is assumed. -/
theorem eq_dId_of_eta_fixpoint
    (hA : ∀ y z : Dinf, Phi (Phi x y) z = Phi y (Phi x z))
    (hB : Phi x Dinf.botDinf = Dinf.botDinf) : x = dId := by
  have hup : dId ≤ x := by
    refine le_of_forall_psi fun n z => ?_
    rw [Phi_dId, theta_psiFun]
    exact psi_le_Phi_of_eta_fixpoint hA hB n z
  have hdown : x ≤ dId := by
    refine le_of_forall_psi fun n z => ?_
    rw [Phi_dId]
    exact theta_Phi_le_psi_of_eta_fixpoint hA hB n z
  exact le_antisymm hdown hup

end EtaFixpoint

/-! ## The denotation of a closed term does not depend on the environment -/

theorem ddenot_congr_freeBelow :
    ∀ (t : Lambda) (k : ℕ) (ρ ρ' : DEnv), Lambda.freeBelow k t → (∀ i, i < k → ρ i = ρ' i) →
      ddenot t ρ = ddenot t ρ' := by
  intro t
  induction t with
  | var i => intro k ρ ρ' hf hρ; exact hρ i hf
  | app s u ihs ihu =>
      intro k ρ ρ' hf hρ
      rw [ddenot_app, ddenot_app, ihs k ρ ρ' hf.1 hρ, ihu k ρ ρ' hf.2 hρ]
  | lam s ih =>
      intro k ρ ρ' hf hρ
      rw [ddenot_lam, ddenot_lam]
      refine dlamAny_congr fun X => ?_
      refine ih (k + 1) _ _ hf ?_
      intro i hi
      cases i with
      | zero => rfl
      | succ j => exact hρ j (by omega)

theorem ddenot_of_closed {t : Lambda} (h : Lambda.freeBelow 0 t) (ρ ρ' : DEnv) :
    ddenot t ρ = ddenot t ρ' :=
  ddenot_congr_freeBelow t 0 ρ ρ' h (fun _ hi => absurd hi (Nat.not_lt_zero _))

/-! ## The infinite η-expansion of the identity -/

/-- The body of the recursion: `λ j x y. x (j y)`. -/
def Jbody : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.lam
    (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.var 2) (Lambda.var 0)))))

/-- **The infinite η-expansion of the identity**, `J = Θ (λ j x y. x (j y))`. -/
def Jterm : Lambda := Lambda.app Lambda.Theta Jbody

theorem Jbody_freeBelow : Lambda.freeBelow 0 Jbody := by
  refine ⟨?_, ?_, ?_⟩
  · change (1 : ℕ) < 3
    omega
  · change (2 : ℕ) < 3
    omega
  · change (0 : ℕ) < 3
    omega

theorem Jbody_closed : Lambda.IsClosed Jbody :=
  Lambda.isClosed_of_freeBelow_zero Jbody_freeBelow

theorem Jterm_closed : Lambda.IsClosed Jterm :=
  Lambda.IsClosed_app Lambda.Theta_closed Jbody_closed

theorem Jterm_freeBelow : Lambda.freeBelow 0 Jterm :=
  (Lambda.freeBelow_zero_iff_isClosed Jterm).2 Jterm_closed

/-- **The defining reduction**: `J →* λx y. x (J y)`. -/
theorem Jterm_reduces :
    Lambda.reduces Jterm (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 1) (Lambda.app Jterm (Lambda.var 0))))) := by
  have hL : Lambda.lift 1 0 Jterm = Jterm := Lambda.lift_closed Jterm_closed 1 0
  refine Lambda.reduces_trans (Lambda.Theta_reduces Jbody) ?_
  refine Lambda.reduces.step _ _ _
    (Lambda.step.beta (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.var 2) (Lambda.var 0))))) Jterm) ?_
  have hs : Lambda.subst Jterm 0 (Lambda.lam (Lambda.lam
      (Lambda.app (Lambda.var 1) (Lambda.app (Lambda.var 2) (Lambda.var 0)))))
      = Lambda.lam (Lambda.lam (Lambda.app (Lambda.var 1)
          (Lambda.app Jterm (Lambda.var 0)))) := by
    simp [Lambda.subst, hL]
  rw [hs]
  exact Lambda.reduces.refl _

/-- The denotation of `J`. -/
def Jval : Dinf := ddenot Jterm (fun _ => Dinf.botDinf)

theorem ddenot_Jterm (ρ : DEnv) : ddenot Jterm ρ = Jval :=
  ddenot_of_closed Jterm_freeBelow ρ _

theorem Phi_Jval (ρ : DEnv) (y : Dinf) :
    Phi Jval y =
      ddenot (Lambda.lam (Lambda.app (Lambda.var 1) (Lambda.app Jterm (Lambda.var 0))))
        (dcons y ρ) := by
  rw [← ddenot_Jterm ρ, ddenot_reduces Jterm_reduces ρ, ddenot_lam_apply]

/-- The first η-limit equation for `J`: `J · y · z = y · (J · z)`. -/
theorem Phi_Phi_Jval (y z : Dinf) : Phi (Phi Jval y) z = Phi y (Phi Jval z) := by
  rw [Phi_Jval (fun _ => Dinf.botDinf) y, ddenot_lam_apply]
  simp only [ddenot_app, ddenot_var, dcons_zero, dcons_succ, ddenot_Jterm]

/-- The second η-limit equation for `J`: `J · ⊥ = ⊥`. -/
theorem Phi_Jval_bot : Phi Jval Dinf.botDinf = Dinf.botDinf := by
  rw [Phi_Jval (fun _ => Dinf.botDinf) Dinf.botDinf, ddenot_lam]
  have h1 : ∀ X : Dinf,
      ddenot (Lambda.app (Lambda.var 1) (Lambda.app Jterm (Lambda.var 0)))
        (dcons X (dcons Dinf.botDinf (fun _ => Dinf.botDinf)))
      = Phi Dinf.botDinf X := by
    intro X
    simp only [ddenot_app, ddenot_var, dcons_zero, dcons_succ, ddenot_Jterm]
    rw [Phi_botDinf, Phi_botDinf]
  rw [dlamAny_congr h1, dlamAny_Phi]

/-- **`J` denotes the identity in `D∞`.** -/
theorem ddenot_Jterm_eq_ddenot_id (ρ : DEnv) : ddenot Jterm ρ = ddenot Lambda.I ρ := by
  rw [ddenot_Jterm, ddenot_id]
  exact eq_dId_of_eta_fixpoint Phi_Phi_Jval Phi_Jval_bot

/-- **`J` is observationally equivalent to the identity.** -/
theorem obsEqHnf_Jterm_id : Lambda.ObsEqHnf Jterm Lambda.I :=
  obsEqHnf_of_ddenot_eq ddenot_Jterm_eq_ddenot_id

/-- `J` acts as the identity on `D∞`. -/
theorem Phi_Jval_eq (y : Dinf) : Phi Jval y = y := by
  rw [eq_dId_of_eta_fixpoint Phi_Phi_Jval Phi_Jval_bot]
  exact Phi_dId y

/-- Applying `J` to a term is semantically invisible: `⟦J M⟧ = ⟦M⟧`. -/
theorem ddenot_app_Jterm (M : Lambda) (ρ : DEnv) :
    ddenot (Lambda.app Jterm M) ρ = ddenot M ρ := by
  rw [ddenot_app, ddenot_Jterm, Phi_Jval_eq]

/-- Hence `J M` is observationally equivalent to `M`, for every term `M`. -/
theorem obsEqHnf_app_Jterm (M : Lambda) : Lambda.ObsEqHnf (Lambda.app Jterm M) M :=
  obsEqHnf_of_ddenot_eq (ddenot_app_Jterm M)

/-! ## The identification is not a β-conversion

The graph model is not extensional, and it separates `J` from the identity for exactly the reason
it separates `λx. x` from `λx y. x y` (`Start/GraphNotFullyAbstract.lean`): every token of `⟦J⟧` is
a step function producing a step function.  Since the graph model is sound for β-conversion, `J`
and the identity are not β-convertible, so the `D∞` identification above is a genuine one. -/

/-- The token `[atom 0] ⇒ atom 0` belongs to the graph-model denotation of the identity. -/
theorem tok_mem_denot_I (ρ : GraphModel.Env) :
    GraphModel.Tok.arrow [GraphModel.Tok.atom 0] (GraphModel.Tok.atom 0)
      ∈ GraphModel.denot Lambda.I ρ := by
  simp only [Lambda.I, GraphModel.denot_lam, GraphModel.denot_var]
  exact GraphModel.mem_graph.2 (by simp [GraphModel.lset])

/-- It does not belong to the graph-model denotation of `J`. -/
theorem tok_notMem_denot_Jterm (ρ : GraphModel.Env) :
    GraphModel.Tok.arrow [GraphModel.Tok.atom 0] (GraphModel.Tok.atom 0)
      ∉ GraphModel.denot Jterm ρ := by
  rw [GraphModel.denot_reduces Jterm_reduces ρ, GraphModel.denot_lam]
  intro h
  have h' := GraphModel.mem_graph.1 h
  rw [GraphModel.denot_lam] at h'
  exact GraphModel.atom_notMem_graph h'

/-- **`J` is not β-convertible to the identity**, although `D∞` identifies the two. -/
theorem not_conv_Jterm_I : ¬ Lambda.Conv Jterm Lambda.I := by
  intro h
  have hd := GraphModel.denot_conv h (fun _ => (∅ : GraphModel.D))
  exact tok_notMem_denot_Jterm _ (hd ▸ tok_mem_denot_I (fun _ => (∅ : GraphModel.D)))

end

end ScottDinf
