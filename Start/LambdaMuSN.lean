/-
**Towards strong normalisation of typed λμ** — task `M23-LAMBDA-MU-SN` (partial).

The reducibility framework of Parigot's proof, on the calculus of `Start/LambdaMu.lean`:

* `LambdaMu.SN` — strong normalisation, `Acc` of the reverse of `Step` (as in
  `Start/SimpleTypes.lean`), with its closure properties (`sn_lam`, `sn_app_left`, …);
* `LambdaMu.VarHead` — the variable-headed spines `x u₁ ⋯ uₙ`, which never create a redex;
  `LambdaMu.sn_app_varHead`: such a spine is SN when its parts are;
* `LambdaMu.Red` — the reducibility candidates (`Red (atom k) = SN`,
  `Red (A → B) = {t | ∀ u ∈ Red A, t u ∈ Red B}`), with `LambdaMu.red_cr` (CR1, CR2, and
  variable-headed SN spines are reducible);
* `LambdaMu.Stk` / `LambdaMu.red_iff_stk` — the stack form of the candidates:
  `t ∈ Red A ↔ ∀ π ∈ Stk A, t π ∈ SN`, the form in which the μ-case of the fundamental lemma is
  stated;
* `LambdaMu.sn_lam` — SN is closed under λ-abstraction.

What remains open is recorded in `docs/goal/evidence/M23-LAMBDA-MU-SN.md`: the first missing
lemma is the stability of reduction under (name-respecting) substitution, which the β- and the
μ-expansion lemmas, and hence the λ- and μ-cases of the fundamental lemma, need.
-/

import Start.LambdaMu

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

open Tm

/-! ### Strong normalisation -/

/-- **Strong normalisation**: `Acc` of the reverse of `Step`. -/
def SN (t : Tm) : Prop := Acc (fun a b => Step b a) t

theorem SN.step {t t' : Tm} (h : SN t) (hs : Step t t') : SN t' := h.inv hs

theorem SN.intro {t : Tm} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

theorem sn_of_map (f : Tm → Tm) (hf : ∀ a b, Step a b → Step (f a) (f b)) :
    ∀ {t : Tm}, SN (f t) → SN t := by
  intro t h
  generalize hft : f t = s at h
  induction h generalizing t with
  | intro s _ ih =>
      subst hft
      exact SN.intro fun t' ht' => ih (f t') (hf _ _ ht') rfl

theorem sn_app_left {t u : Tm} (h : SN (app t u)) : SN t :=
  sn_of_map (fun t => app t u) (fun _ _ h => Step.appL u h) h

theorem sn_app_right {t u : Tm} (h : SN (app t u)) : SN u :=
  sn_of_map (fun u => app t u) (fun _ _ h => Step.appR t h) h

theorem sn_lam_inv {t : Tm} (h : SN (lam t)) : SN t :=
  sn_of_map lam (fun _ _ h => Step.lam h) h

theorem sn_mu_inv {β : ℕ} {t : Tm} (h : SN (mu β t)) : SN t :=
  sn_of_map (mu β) (fun _ _ h => Step.mu β h) h

theorem not_step_var {i : ℕ} {t : Tm} : ¬ Step (var i) t := by
  intro h; cases h

theorem sn_var (i : ℕ) : SN (var i) := SN.intro fun _ h => absurd h not_step_var

theorem sn_lam {t : Tm} (h : SN t) : SN (lam t) := by
  induction h with
  | intro t _ ih =>
      refine SN.intro fun s hs => ?_
      cases hs with
      | lam h => exact ih _ h

/-! ### Variable-headed spines -/

/-- Variable-headed spines `x u₁ ⋯ uₙ`. -/
inductive VarHead : Tm → Prop
  | var (i : ℕ) : VarHead (var i)
  | app {h : Tm} (u : Tm) : VarHead h → VarHead (app h u)

theorem VarHead.step {h h' : Tm} (hv : VarHead h) (hs : Step h h') : VarHead h' := by
  induction hv generalizing h' with
  | var i => exact absurd hs not_step_var
  | app u hv ih =>
      cases hs with
      | beta => cases hv
      | struct => cases hv
      | appL _ hs => exact .app u (ih hs)
      | appR _ _ => exact .app _ hv

/-- **A variable-headed spine is SN when its head and its argument are.** -/
theorem sn_app_varHead {h u : Tm} (hv : VarHead h) (hh : SN h) (hu : SN u) : SN (app h u) := by
  induction hh generalizing u with
  | intro h _ ihh =>
      induction hu with
      | intro u hu' ihu =>
          refine SN.intro fun s hs => ?_
          cases hs with
          | beta => cases hv
          | struct => cases hv
          | appL _ hs' => exact ihh _ hs' (hv.step hs') (Acc.intro u hu')
          | appR _ hs' => exact ihu _ hs'

/-! ### Reducibility candidates -/

/-- **The reducibility candidates.** -/
def Red : Ty → Tm → Prop
  | .atom _, t => SN t
  | .arr A B, t => ∀ u, Red A u → Red B (app t u)

/-- **The candidate properties**: reducible terms are SN (CR1), reducibility is closed under
reduction (CR2), and SN variable-headed spines are reducible. -/
theorem red_cr (A : Ty) :
    (∀ t, Red A t → SN t) ∧ (∀ t t', Red A t → Step t t' → Red A t') ∧
      (∀ h, VarHead h → SN h → Red A h) := by
  induction A with
  | atom k => exact ⟨fun _ h => h, fun _ _ h hs => h.step hs, fun _ _ h => h⟩
  | arr A B ihA ihB =>
      obtain ⟨cr1A, _, cr3A⟩ := ihA
      obtain ⟨cr1B, cr2B, cr3B⟩ := ihB
      refine ⟨fun t ht => ?_, fun t t' ht hs u hu => cr2B _ _ (ht u hu) (Step.appL u hs),
        fun h hv hh u hu => cr3B _ (.app u hv) (sn_app_varHead hv hh (cr1A u hu))⟩
      have := ht (var 0) (cr3A _ (.var 0) (sn_var 0))
      exact sn_app_left (cr1B _ this)

theorem red_sn {A : Ty} {t : Tm} (h : Red A t) : SN t := (red_cr A).1 t h

theorem red_step {A : Ty} {t t' : Tm} (h : Red A t) (hs : Step t t') : Red A t' :=
  (red_cr A).2.1 t t' h hs

theorem red_var (A : Ty) (i : ℕ) : Red A (var i) := (red_cr A).2.2 _ (.var i) (sn_var i)

/-! ### The stack form of the candidates -/

/-- `apps t π` applies `t` to the arguments `π`, outermost first. -/
def apps : Tm → List Tm → Tm
  | t, [] => t
  | t, u :: π => apps (app t u) π

/-- The reducible stacks of a type `A₁ → ⋯ → Aₙ → o`: lists `u₁, …, uₙ` with `uᵢ ∈ Red Aᵢ`. -/
def Stk : Ty → List Tm → Prop
  | .atom _, π => π = []
  | .arr A B, π => ∃ u π', π = u :: π' ∧ Red A u ∧ Stk B π'

/-- **The stack form of the candidates**: `t ∈ Red A ↔ ∀ π ∈ Stk A, t π ∈ SN`. -/
theorem red_iff_stk (A : Ty) : ∀ t, Red A t ↔ ∀ π, Stk A π → SN (apps t π) := by
  induction A with
  | atom k =>
      intro t
      exact ⟨fun h π hπ => by subst hπ; exact h, fun h => h [] rfl⟩
  | arr A B _ ihB =>
      intro t
      constructor
      · rintro h π ⟨u, π', rfl, hu, hπ'⟩
        exact (ihB _).1 (h u hu) π' hπ'
      · intro h u hu
        exact (ihB _).2 fun π' hπ' => h (u :: π') ⟨u, π', rfl, hu, hπ'⟩

end LambdaMu
