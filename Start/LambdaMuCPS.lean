/-
**A CPS translation of λμ into the simply typed λ-calculus (M23-LAMBDA-MU).**

Call-by-name translation in Plotkin's style, with answer type `o` (`Lambda.Ty.base`) and
`¬X := X ⇒ o`.  Types: `atom* = o`, `(A → B)* = ¬¬A* ⇒ ¬¬B*`; a term of type `A` becomes a term of
type `¬¬A*`, a term variable of type `A` gets type `¬¬A*`, a name of type `A` gets type `¬A*`.

The translation is environment-passing (`cpsE ρ t`, where `ρ i` is the image of the free index
`i`):

* `⟦x⟧ = ρ x`,
* `⟦λx.t⟧ = λk. k (λx. ⟦t⟧)`,
* `⟦t u⟧ = λk. ⟦t⟧ (λm. m ⟦u⟧ k)`,
* `⟦μα.[β]t⟧ = λα. ⟦t⟧ β`,

and `cps t := cpsE etaV t` with the η-expanded identity environment `etaV i = λk. i k`.

* `typing_cps`: **the translation preserves typing** (with double negation of types).
* `cps_step`: **simulation**: one λμ step becomes a β-conversion of the images; precisely, the two
  images have a common β-reduct (`Join`).  For β and renaming steps the image of the redex even
  reduces to the image of the reduct; a structural step is simulated only up to a common reduct.
  Strict simulation (one step ↦ at least one β-step) and strong normalization of typed λμ are
  *not* proved here (open boundary).
-/

import Start.LambdaMu
import Start.SimpleTypes

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

open Tm

/-! ### Types -/

/-- `¬X = X ⇒ o`. -/
def neg (X : Lambda.Ty) : Lambda.Ty := .arrow X .base

/-- `A*`. -/
def tyS : Ty → Lambda.Ty
  | .atom _ => .base
  | .arr A B => .arrow (neg (neg (tyS A))) (neg (neg (tyS B)))

/-- `¬¬A*`, the type of the image of a term of type `A`. -/
def tyN (A : Ty) : Lambda.Ty := neg (neg (tyS A))

/-- Context entries: term variables get `¬¬A*`, names get `¬A*`. -/
def entS : Entry → Lambda.Ty
  | .tm A => tyN A
  | .nm A => neg (tyS A)

/-! ### The translation -/

/-- The η-expanded variable `λk. i k`. -/
def etaV (i : ℕ) : Lambda := .lam (.app (.var (i + 1)) (.var 0))

/-- Environment under a λ (the bound term variable is `etaV 0`). -/
def consT (ρ : ℕ → Lambda) : ℕ → Lambda
  | 0 => etaV 0
  | i + 1 => Lambda.lift 1 0 (ρ i)

/-- Environment under a μ (the bound name is the continuation variable `0`). -/
def consN (ρ : ℕ → Lambda) : ℕ → Lambda
  | 0 => .var 0
  | i + 1 => Lambda.lift 1 0 (ρ i)

/-- Lifting an environment. -/
def liftE (ρ : ℕ → Lambda) : ℕ → Lambda := fun i => Lambda.lift 1 0 (ρ i)

/-- The CPS translation relative to an environment. -/
def cpsE : (ℕ → Lambda) → Tm → Lambda
  | ρ, .var i => ρ i
  | ρ, .lam t => .lam (.app (.var 0) (.lam (cpsE (consT (liftE ρ)) t)))
  | ρ, .app t u => .lam (.app (cpsE (liftE ρ) t)
      (.lam (.app (.app (.var 0) (cpsE (liftE (liftE ρ)) u)) (.var 1))))
  | ρ, .mu β t => .lam (.app (cpsE (consN ρ) t) (consN ρ β))

/-- The CPS translation. -/
def cps (t : Tm) : Lambda := cpsE etaV t

/-! ### Typing -/

theorem typing_lift {Δ : List Lambda.Ty} {t : Lambda} {T : Lambda.Ty} (h : Lambda.Typing Δ t T)
    (X : Lambda.Ty) : ∀ k, Lambda.Typing (Δ.take k ++ X :: Δ.drop k) (Lambda.lift 1 k t) T := by
  induction h with
  | @var Δ i A hi =>
      intro k
      have hlt : i < Δ.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
      by_cases hik : i < k
      · simp only [Lambda.lift, hik, if_true]
        refine .var ?_
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hik]
        exact hi
      · simp only [Lambda.lift, hik, if_false]
        refine .var ?_
        have hk : (Δ.take k).length = k := by simp; omega
        rw [List.getElem?_append_right (by omega), hk]
        rw [show i + 1 - k = (i - k) + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop,
          show k + (i - k) = i by omega]
        exact hi
  | app _ _ iha ihb => intro k; exact .app (iha k) (ihb k)
  | @lam Δ t A B _ ih =>
      intro k
      have := ih (k + 1)
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append] at this
      exact .lam this

theorem typing_weaken {Δ : List Lambda.Ty} {t : Lambda} {T : Lambda.Ty}
    (h : Lambda.Typing Δ t T) (X : Lambda.Ty) : Lambda.Typing (X :: Δ) (Lambda.lift 1 0 t) T := by
  simpa using typing_lift h X 0

/-- Environments typed by the translated context. -/
def EnvTyped (Γ : List Entry) (Δ : List Lambda.Ty) (ρ : ℕ → Lambda) : Prop :=
  ∀ i e, Γ[i]? = some e → Lambda.Typing Δ (ρ i) (entS e)

theorem entS_arrow (e : Entry) : ∃ P, entS e = .arrow P .base := by
  cases e with
  | tm A => exact ⟨_, rfl⟩
  | nm A => exact ⟨_, rfl⟩

theorem typing_etaV0 {Δ : List Lambda.Ty} {P : Lambda.Ty} :
    Lambda.Typing (.arrow P .base :: Δ) (etaV 0) (.arrow P .base) :=
  .lam (.app (.var rfl) (.var rfl))

theorem EnvTyped.liftE {Γ : List Entry} {Δ : List Lambda.Ty} {ρ : ℕ → Lambda}
    (h : EnvTyped Γ Δ ρ) (X : Lambda.Ty) : EnvTyped Γ (X :: Δ) (liftE ρ) :=
  fun i e hi => typing_weaken (h i e hi) X

theorem EnvTyped.consT {Γ : List Entry} {Δ : List Lambda.Ty} {ρ : ℕ → Lambda}
    (h : EnvTyped Γ Δ ρ) (A : Ty) : EnvTyped (.tm A :: Γ) (tyN A :: Δ) (consT ρ) := by
  intro i e hi
  cases i with
  | zero => simp at hi; subst hi; exact typing_etaV0
  | succ i => exact typing_weaken (h i e (by simpa using hi)) _

theorem EnvTyped.consN {Γ : List Entry} {Δ : List Lambda.Ty} {ρ : ℕ → Lambda}
    (h : EnvTyped Γ Δ ρ) (A : Ty) : EnvTyped (.nm A :: Γ) (neg (tyS A) :: Δ) (consN ρ) := by
  intro i e hi
  cases i with
  | zero => simp at hi; subst hi; exact .var rfl
  | succ i => exact typing_weaken (h i e (by simpa using hi)) _

theorem typing_cpsE {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {Δ : List Lambda.Ty} {ρ : ℕ → Lambda}, EnvTyped Γ Δ ρ →
      Lambda.Typing Δ (cpsE ρ t) (tyN A) := by
  induction h with
  | var hi => intro Δ ρ hρ; exact hρ _ _ hi
  | @lam Γ t A B _ ih =>
      intro Δ ρ hρ
      exact .lam (.app (.var rfl) (.lam (ih ((hρ.liftE (neg (tyS (.arr A B)))).consT A))))
  | @app Γ t u A B _ _ iht ihu =>
      intro Δ ρ hρ
      refine .lam (.app (iht (hρ.liftE (neg (tyS B)))) (.lam (.app (.app (.var rfl)
        (ihu ((hρ.liftE _).liftE _))) (.var rfl))))
  | @mu Γ β t A B _ hβ ih =>
      intro Δ ρ hρ
      exact .lam (.app (ih (hρ.consN A)) ((hρ.consN A) β _ hβ))

/-- **The CPS translation preserves typing**: `Γ ⊢ t : A | Δ` gives `Γ*, Δ* ⊢ ⟦t⟧ : ¬¬A*`. -/
theorem typing_cps {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    Lambda.Typing (Γ.map entS) (cps t) (tyN A) := by
  refine typing_cpsE h ?_
  intro i e hi
  obtain ⟨P, hP⟩ := entS_arrow e
  rw [hP]
  refine .lam (.app (.var ?_) (.var rfl))
  simp [hi, hP]

/-! ### Commutation of the translation with lifting, substitution and renaming -/

theorem lift_etaV0 (n j : ℕ) : Lambda.lift n (j + 1) (etaV 0) = etaV 0 := by
  simp [etaV, Lambda.lift]

theorem lift_liftE (n j : ℕ) (ρ : ℕ → Lambda) :
    (fun i => Lambda.lift n (j + 1) (liftE ρ i)) = liftE (fun i => Lambda.lift n j (ρ i)) := by
  funext i
  exact (Lambda.lift_lift (ρ i) 1 n 0 j (Nat.zero_le j)).symm

theorem lift_consT (n j : ℕ) (σ : ℕ → Lambda) :
    (fun i => Lambda.lift n (j + 1) (consT σ i)) = consT (fun i => Lambda.lift n j (σ i)) := by
  funext i
  cases i with
  | zero => exact lift_etaV0 n j
  | succ i => exact (Lambda.lift_lift (σ i) 1 n 0 j (Nat.zero_le j)).symm

theorem lift_consN (n j : ℕ) (σ : ℕ → Lambda) :
    (fun i => Lambda.lift n (j + 1) (consN σ i)) = consN (fun i => Lambda.lift n j (σ i)) := by
  funext i
  cases i with
  | zero => simp [consN, Lambda.lift]
  | succ i => exact (Lambda.lift_lift (σ i) 1 n 0 j (Nat.zero_le j)).symm

/-- Lifting commutes with the translation. -/
theorem cpsE_lift (n : ℕ) : ∀ (t : Tm) (ρ : ℕ → Lambda) (j : ℕ),
    Lambda.lift n j (cpsE ρ t) = cpsE (fun i => Lambda.lift n j (ρ i)) t := by
  intro t
  induction t with
  | var i => intro ρ j; rfl
  | lam t ih =>
      intro ρ j
      simp only [cpsE, Lambda.lift, ih, lift_consT, lift_liftE]
      simp
  | app t u iht ihu =>
      intro ρ j
      simp only [cpsE, Lambda.lift, iht, ihu, lift_liftE]
      simp
  | mu β t ih =>
      intro ρ j
      have hc := congrFun (lift_consN n j ρ) β
      simp only [cpsE, Lambda.lift, ih, lift_consN]
      rw [hc]

theorem subst_etaV0 (s : Lambda) (j : ℕ) : Lambda.subst s (j + 1) (etaV 0) = etaV 0 := by
  simp only [etaV, Lambda.subst]
  have h2 : ¬ (1 : ℕ) > j + 1 + 1 := by omega
  have h4 : ¬ (0 : ℕ) > j + 1 + 1 := by omega
  simp [h2, h4]

theorem subst_liftE (s : Lambda) (j : ℕ) (ρ : ℕ → Lambda) :
    (fun i => Lambda.subst (Lambda.lift 1 0 s) (j + 1) (liftE ρ i)) =
      liftE (fun i => Lambda.subst s j (ρ i)) := by
  funext i
  exact (Lambda.lift_subst (ρ i) s 1 0 j (Nat.zero_le j)).symm

theorem subst_consT (s : Lambda) (j : ℕ) (σ : ℕ → Lambda) :
    (fun i => Lambda.subst (Lambda.lift 1 0 s) (j + 1) (consT σ i)) =
      consT (fun i => Lambda.subst s j (σ i)) := by
  funext i
  cases i with
  | zero => exact subst_etaV0 _ j
  | succ i => exact (Lambda.lift_subst (σ i) s 1 0 j (Nat.zero_le j)).symm

theorem subst_consN (s : Lambda) (j : ℕ) (σ : ℕ → Lambda) :
    (fun i => Lambda.subst (Lambda.lift 1 0 s) (j + 1) (consN σ i)) =
      consN (fun i => Lambda.subst s j (σ i)) := by
  funext i
  cases i with
  | zero =>
      have h4 : ¬ (0 : ℕ) > j + 1 := by omega
      simp [consN, Lambda.subst, h4]
  | succ i => exact (Lambda.lift_subst (σ i) s 1 0 j (Nat.zero_le j)).symm

/-- Substitution commutes with the translation. -/
theorem cpsE_subst : ∀ (t : Tm) (ρ : ℕ → Lambda) (s : Lambda) (j : ℕ),
    Lambda.subst s j (cpsE ρ t) = cpsE (fun i => Lambda.subst s j (ρ i)) t := by
  intro t
  induction t with
  | var i => intro ρ s j; rfl
  | lam t ih =>
      intro ρ s j
      simp only [cpsE, Lambda.subst, ih, subst_consT, subst_liftE]
      have h4 : ¬ (0 : ℕ) > j + 1 := by omega
      simp [h4]
  | app t u iht ihu =>
      intro ρ s j
      simp only [cpsE, Lambda.subst, iht, ihu, subst_liftE]
      have h4 : ¬ (0 : ℕ) > j + 1 + 1 := by omega
      have h5 : ¬ (1 : ℕ) > j + 1 + 1 := by omega
      simp [h4, h5]
  | mu β t ih =>
      intro ρ s j
      have hc := congrFun (subst_consN s j ρ) β
      simp only [cpsE, Lambda.subst, ih, subst_consN]
      rw [hc]

/-- Renaming the source is renaming the environment. -/
theorem cpsE_ren : ∀ (t : Tm) (ρ : ℕ → Lambda) (r : ℕ → ℕ),
    cpsE ρ (Tm.ren r t) = cpsE (fun i => ρ (r i)) t := by
  intro t
  induction t with
  | var i => intro ρ r; rfl
  | lam t ih =>
      intro ρ r
      have he : (fun i => consT (liftE ρ) (Tm.up r i)) = consT (liftE (fun i => ρ (r i))) := by
        funext i; cases i <;> rfl
      simp only [cpsE, Tm.ren, ih, he]
  | app t u iht ihu =>
      intro ρ r
      simp only [cpsE, Tm.ren, iht, ihu]
      rfl
  | mu β t ih =>
      intro ρ r
      have he : (fun i => consN ρ (Tm.up r i)) = consN (fun i => ρ (r i)) := by
        funext i; cases i <;> rfl
      have hc := congrFun he β
      simp only [cpsE, Tm.ren, ih, he]
      rw [hc]

/-- Names of `t` are sent to variables by `σ`. -/
def NamesVar : (ℕ → Tm) → Tm → Prop
  | _, .var _ => True
  | σ, .lam t => NamesVar (Tm.upS σ) t
  | σ, .app t u => NamesVar σ t ∧ NamesVar σ u
  | σ, .mu β t => (∃ j, Tm.upS σ β = .var j) ∧ NamesVar (Tm.upS σ) t

theorem cpsE_liftE_eq (ρ : ℕ → Lambda) (t : Tm) : cpsE (liftE ρ) t = Lambda.lift 1 0 (cpsE ρ t) :=
  (cpsE_lift 1 t ρ 0).symm

/-- **Substitution lemma for the translation.** -/
theorem cpsE_substTm : ∀ (t : Tm) (σ : ℕ → Tm) (ρ : ℕ → Lambda), NamesVar σ t →
    cpsE ρ (Tm.subst σ t) = cpsE (fun i => cpsE ρ (σ i)) t := by
  intro t
  induction t with
  | var i => intro σ ρ _; rfl
  | lam t ih =>
      intro σ ρ hn
      have he : (fun i => cpsE (consT (liftE ρ)) (Tm.upS σ i)) =
          consT (liftE (fun i => cpsE ρ (σ i))) := by
        funext i
        cases i with
        | zero => rfl
        | succ i =>
            simp only [Tm.upS, cpsE_ren, consT, liftE]
            show cpsE (liftE (liftE ρ)) (σ i) = _
            rw [cpsE_liftE_eq, cpsE_liftE_eq]
      simp only [cpsE, Tm.subst, ih _ _ hn, he]
  | app t u iht ihu =>
      intro σ ρ hn
      have h1 : (fun i => cpsE (liftE ρ) (σ i)) = liftE (fun i => cpsE ρ (σ i)) := by
        funext i; exact cpsE_liftE_eq ρ (σ i)
      have h2 : (fun i => cpsE (liftE (liftE ρ)) (σ i)) =
          liftE (liftE (fun i => cpsE ρ (σ i))) := by
        funext i; rw [cpsE_liftE_eq, cpsE_liftE_eq]; rfl
      simp only [cpsE, Tm.subst, iht _ _ hn.1, ihu _ _ hn.2, h1, h2]
  | mu β t ih =>
      intro σ ρ hn
      have he : (fun i => cpsE (consN ρ) (Tm.upS σ i)) = consN (fun i => cpsE ρ (σ i)) := by
        funext i
        cases i with
        | zero => rfl
        | succ i =>
            simp only [Tm.upS, cpsE_ren, consN]
            show cpsE (liftE ρ) (σ i) = _
            rw [cpsE_liftE_eq]
      obtain ⟨j, hj⟩ := hn.1
      have hname : consN ρ (Tm.nameOf (Tm.upS σ β)) = consN (fun i => cpsE ρ (σ i)) β := by
        rw [← congrFun he β, hj]; rfl
      simp only [cpsE, Tm.subst, ih _ _ hn.2, he, hname]

/-- Pointwise reduction of the environment. -/
theorem cpsE_reduces_env : ∀ (t : Tm) (ρ ρ' : ℕ → Lambda), (∀ i, Lambda.reduces (ρ i) (ρ' i)) →
    Lambda.reduces (cpsE ρ t) (cpsE ρ' t) := by
  intro t
  induction t with
  | var i => intro ρ ρ' h; exact h i
  | lam t ih =>
      intro ρ ρ' h
      refine Lambda.reduces_lam (Lambda.reduces_app (.refl _) (Lambda.reduces_lam (ih _ _ ?_)))
      intro i
      cases i with
      | zero => exact .refl _
      | succ i => exact Lambda.reduces_lift (Lambda.reduces_lift (h i) 1 0) 1 0
  | app t u iht ihu =>
      intro ρ ρ' h
      refine Lambda.reduces_lam (Lambda.reduces_app (iht _ _ ?_) (Lambda.reduces_lam
        (Lambda.reduces_app (Lambda.reduces_app (.refl _) (ihu _ _ ?_)) (.refl _))))
      · intro i; exact Lambda.reduces_lift (h i) 1 0
      · intro i; exact Lambda.reduces_lift (Lambda.reduces_lift (h i) 1 0) 1 0
  | mu β t ih =>
      intro ρ ρ' h
      have h' : ∀ i, Lambda.reduces (consN ρ i) (consN ρ' i) := by
        intro i
        cases i with
        | zero => exact .refl _
        | succ i => exact Lambda.reduces_lift (h i) 1 0
      exact Lambda.reduces_lam (Lambda.reduces_app (ih _ _ h') (h' β))

/-! ### Simulation -/

/-- Two terms have a common β-reduct (so they are β-convertible). -/
def Join (a b : Lambda) : Prop := ∃ c, Lambda.reduces a c ∧ Lambda.reduces b c

theorem reduces_single {a b : Lambda} (h : Lambda.step a b) : Lambda.reduces a b :=
  .step _ _ _ h (.refl _)

namespace Join

theorem refl (a : Lambda) : Join a a := ⟨a, .refl _, .refl _⟩

theorem of_eq {a b : Lambda} (h : a = b) : Join a b := h ▸ refl a

theorem app {a a' b b' : Lambda} (h1 : Join a a') (h2 : Join b b') :
    Join (.app a b) (.app a' b') := by
  obtain ⟨c, h1, h1'⟩ := h1
  obtain ⟨d, h2, h2'⟩ := h2
  exact ⟨_, Lambda.reduces_app h1 h2, Lambda.reduces_app h1' h2'⟩

theorem lam {a a' : Lambda} (h : Join a a') : Join (.lam a) (.lam a') := by
  obtain ⟨c, h1, h1'⟩ := h
  exact ⟨_, Lambda.reduces_lam h1, Lambda.reduces_lam h1'⟩

theorem red_left {a a' b : Lambda} (h : Lambda.reduces a a') (j : Join a' b) : Join a b := by
  obtain ⟨c, h1, h2⟩ := j
  exact ⟨c, Lambda.reduces_trans h h1, h2⟩

theorem red_right {a b b' : Lambda} (h : Lambda.reduces b b') (j : Join a b') : Join a b := by
  obtain ⟨c, h1, h2⟩ := j
  exact ⟨c, h1, Lambda.reduces_trans h h2⟩

theorem of_reduces {a b : Lambda} (h : Lambda.reduces a b) : Join a b := ⟨b, h, .refl _⟩

theorem symm {a b : Lambda} (h : Join a b) : Join b a := by
  obtain ⟨c, h1, h2⟩ := h
  exact ⟨c, h2, h1⟩

end Join

theorem subst_var_lift (C : Lambda) : ∀ k, Lambda.subst (.var k) k (Lambda.lift 1 (k + 1) C) = C := by
  induction C with
  | var y =>
      intro k
      by_cases hy : y < k + 1
      · by_cases hyk : y = k
        · subst hyk; simp [Lambda.lift, Lambda.subst]
        · have h1 : ¬ y > k := by omega
          simp [Lambda.lift, Lambda.subst, hy, hyk, h1]
      · have h1 : y + 1 ≠ k := by omega
        have h2 : y + 1 > k := by omega
        simp [Lambda.lift, Lambda.subst, hy, h1, h2]
  | app a b iha ihb => intro k; simp [Lambda.lift, Lambda.subst, iha, ihb]
  | lam C ih =>
      intro k
      have := ih (k + 1)
      simp only [Lambda.lift, Lambda.subst]
      simp [this]

/-- `λk. (λx. C) k → λx. C` (a β-step that undoes an η-expansion of an abstraction). -/
theorem step_eta_lam (C : Lambda) :
    Lambda.step (.lam (.app (Lambda.lift 1 0 (.lam C)) (.var 0))) (.lam C) := by
  have h := Lambda.step.lam _ _ (Lambda.step.beta (Lambda.lift 1 1 C) (.var 0))
  have e : Lambda.subst (.var 0) 0 (Lambda.lift 1 1 C) = C := subst_var_lift C 0
  rw [e] at h
  simpa [Lambda.lift] using h

/-- The continuation `λm. m V L`. -/
def KontT (L V : Lambda) : Lambda :=
  .lam (.app (.app (.var 0) (Lambda.lift 1 0 V)) (Lambda.lift 1 0 L))

theorem lift_lift00 (X : Lambda) : Lambda.lift 1 1 (Lambda.lift 1 0 X) =
    Lambda.lift 1 0 (Lambda.lift 1 0 X) :=
  (Lambda.lift_lift X 1 1 0 0 le_rfl).symm

theorem lift_KontT (L V : Lambda) :
    Lambda.lift 1 0 (KontT L V) = KontT (Lambda.lift 1 0 L) (Lambda.lift 1 0 V) := by
  simp [KontT, Lambda.lift, lift_lift00]

theorem subst_lift_lift1 (s X : Lambda) :
    Lambda.subst (Lambda.lift 1 0 s) 1 (Lambda.lift 1 0 (Lambda.lift 1 0 X)) = Lambda.lift 1 0 X := by
  rw [← lift_lift00, Lambda.subst_lift]

/-- Applying the image of an application to a continuation. -/
theorem step_app_cont (σ : ℕ → Lambda) (w v : Tm) (L : Lambda) :
    Lambda.step (.app (cpsE σ (.app w v)) L) (.app (cpsE σ w) (KontT L (cpsE σ v))) := by
  have h := Lambda.step.beta (.app (cpsE (liftE σ) w)
      (.lam (.app (.app (.var 0) (cpsE (liftE (liftE σ)) v)) (.var 1)))) L
  have e : Lambda.subst L 0 (.app (cpsE (liftE σ) w)
      (.lam (.app (.app (.var 0) (cpsE (liftE (liftE σ)) v)) (.var 1)))) =
      .app (cpsE σ w) (KontT L (cpsE σ v)) := by
    simp only [Lambda.subst, cpsE_liftE_eq, Lambda.subst_lift, KontT]
    simp [subst_lift_lift1]
  rw [e] at h
  exact h

/-- `a` is not used as a term variable in `t`. -/
def TermFree : ℕ → Tm → Prop
  | a, .var i => i ≠ a
  | a, .lam t => TermFree (a + 1) t
  | a, .app t u => TermFree a t ∧ TermFree a u
  | a, .mu _ t => TermFree (a + 1) t

theorem termFree_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {a : ℕ} {B : Ty}, Γ[a]? = some (.nm B) → TermFree a t := by
  induction h with
  | var hi =>
      intro a B ha
      simp only [TermFree]
      rintro rfl
      rw [ha] at hi; cases hi
  | lam _ ih => intro a B ha; exact ih (a := a + 1) (by simpa using ha)
  | app _ _ iht ihu => intro a B ha; exact ⟨iht ha, ihu ha⟩
  | mu _ _ ih => intro a B ha; exact ih (a := a + 1) (by simpa using ha)

theorem namesVar_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {σ : ℕ → Tm}, (∀ i B, Γ[i]? = some (.nm B) → ∃ j, σ i = .var j) → NamesVar σ t := by
  induction h with
  | var _ => intro σ _; trivial
  | @lam Γ t A B _ ih =>
      intro σ hσ
      refine ih ?_
      intro i C hi
      cases i with
      | zero => simp at hi
      | succ i =>
          obtain ⟨j, hj⟩ := hσ i C (by simpa using hi)
          exact ⟨j + 1, by simp [Tm.upS, hj, Tm.ren]⟩
  | app _ _ iht ihu => intro σ hσ; exact ⟨iht hσ, ihu hσ⟩
  | @mu Γ β t A B _ hβ ih =>
      intro σ hσ
      have hσ' : ∀ i C, (Entry.nm A :: Γ)[i]? = some (.nm C) → ∃ j, Tm.upS σ i = .var j := by
        intro i C hi
        cases i with
        | zero => exact ⟨0, rfl⟩
        | succ i =>
            obtain ⟨j, hj⟩ := hσ i C (by simpa using hi)
            exact ⟨j + 1, by simp [Tm.upS, hj, Tm.ren]⟩
      exact ⟨hσ' β B hβ, ih hσ'⟩

theorem namesVar_of_allVar : ∀ (t : Tm) (σ : ℕ → Tm), (∀ i, ∃ j, σ i = .var j) → NamesVar σ t := by
  have hup : ∀ σ : ℕ → Tm, (∀ i, ∃ j, σ i = .var j) → ∀ i, ∃ j, Tm.upS σ i = .var j := by
    intro σ hσ i
    cases i with
    | zero => exact ⟨0, rfl⟩
    | succ i =>
        obtain ⟨j, hj⟩ := hσ i
        exact ⟨j + 1, by simp [Tm.upS, hj, Tm.ren]⟩
  intro t
  induction t with
  | var _ => intro σ _; trivial
  | lam t ih => intro σ hσ; exact ih _ (hup σ hσ)
  | app t u iht ihu => intro σ hσ; exact ⟨iht σ hσ, ihu σ hσ⟩
  | mu β t ih => intro σ hσ; exact ⟨hup σ hσ β, ih _ (hup σ hσ)⟩

/-- Environment update. -/
def upd (ρ : ℕ → Lambda) (a : ℕ) (X : Lambda) : ℕ → Lambda := fun i => if i = a then X else ρ i

theorem liftE_upd (ρ : ℕ → Lambda) (a : ℕ) (X : Lambda) :
    liftE (upd ρ a X) = upd (liftE ρ) a (Lambda.lift 1 0 X) := by
  funext i
  by_cases h : i = a <;> simp [liftE, upd, h]

theorem consT_upd (ρ : ℕ → Lambda) (a : ℕ) (X : Lambda) :
    consT (upd ρ a X) = upd (consT ρ) (a + 1) (Lambda.lift 1 0 X) := by
  funext i
  cases i with
  | zero => simp [consT, upd]
  | succ i => by_cases h : i = a <;> simp [consT, upd, h]

theorem consN_upd (ρ : ℕ → Lambda) (a : ℕ) (X : Lambda) :
    consN (upd ρ a X) = upd (consN ρ) (a + 1) (Lambda.lift 1 0 X) := by
  funext i
  cases i with
  | zero => simp [consN, upd]
  | succ i => by_cases h : i = a <;> simp [consN, upd, h]

theorem cpsE_ren_succ_consT (ρ : ℕ → Lambda) (v : Tm) :
    cpsE (consT (liftE ρ)) (Tm.ren Nat.succ v) = Lambda.lift 1 0 (Lambda.lift 1 0 (cpsE ρ v)) := by
  rw [cpsE_ren]
  show cpsE (liftE (liftE ρ)) v = _
  rw [cpsE_liftE_eq, cpsE_liftE_eq]

theorem cpsE_ren_succ_consN (ρ : ℕ → Lambda) (v : Tm) :
    cpsE (consN ρ) (Tm.ren Nat.succ v) = Lambda.lift 1 0 (cpsE ρ v) := by
  rw [cpsE_ren]
  show cpsE (liftE ρ) v = _
  rw [cpsE_liftE_eq]

/-- **Structural substitution in the image**: the image of `t[[a](w v)/[a]w]` and the image of
`t` with the continuation `a` replaced by `λm. m ⟦v⟧ a` have a common reduct. -/
theorem cpsE_sstr : ∀ (t : Tm) (a : ℕ) (v : Tm) (ρ : ℕ → Lambda), TermFree a t →
    Join (cpsE ρ (Tm.sstr a v t)) (cpsE (upd ρ a (KontT (ρ a) (cpsE ρ v))) t) := by
  intro t
  induction t with
  | var i =>
      intro a v ρ ht
      exact Join.of_eq (by simp [Tm.sstr, cpsE, upd, show i ≠ a from ht])
  | lam t ih =>
      intro a v ρ ht
      have IH := ih (a + 1) (Tm.ren Nat.succ v) (consT (liftE ρ)) ht
      have he : consT (liftE (upd ρ a (KontT (ρ a) (cpsE ρ v)))) =
          upd (consT (liftE ρ)) (a + 1) (KontT (consT (liftE ρ) (a + 1))
            (cpsE (consT (liftE ρ)) (Tm.ren Nat.succ v))) := by
        rw [liftE_upd, consT_upd, cpsE_ren_succ_consT, lift_KontT, lift_KontT]
        rfl
      simp only [Tm.sstr, cpsE]
      rw [he]
      exact Join.lam (Join.app (Join.refl _) (Join.lam IH))
  | app t u iht ihu =>
      intro a v ρ ht
      have IHt := iht a v (liftE ρ) ht.1
      have IHu := ihu a v (liftE (liftE ρ)) ht.2
      have he1 : liftE (upd ρ a (KontT (ρ a) (cpsE ρ v))) =
          upd (liftE ρ) a (KontT (liftE ρ a) (cpsE (liftE ρ) v)) := by
        rw [liftE_upd, lift_KontT, cpsE_liftE_eq]; rfl
      have he2 : liftE (upd (liftE ρ) a (KontT (liftE ρ a) (cpsE (liftE ρ) v))) =
          upd (liftE (liftE ρ)) a (KontT (liftE (liftE ρ) a) (cpsE (liftE (liftE ρ)) v)) := by
        rw [liftE_upd, lift_KontT, cpsE_liftE_eq (liftE ρ)]; rfl
      simp only [Tm.sstr, cpsE]
      rw [he1, he2]
      exact Join.lam (Join.app IHt (Join.lam (Join.app (Join.app (Join.refl _) IHu) (Join.refl _))))
  | mu β t ih =>
      intro a v ρ ht
      have IH := ih (a + 1) (Tm.ren Nat.succ v) (consN ρ) ht
      have he : consN (upd ρ a (KontT (ρ a) (cpsE ρ v))) =
          upd (consN ρ) (a + 1) (KontT (consN ρ (a + 1)) (cpsE (consN ρ) (Tm.ren Nat.succ v))) := by
        rw [consN_upd, cpsE_ren_succ_consN, lift_KontT]
        rfl
      simp only [Tm.sstr, cpsE]
      rw [he]
      split_ifs with hβ
      · subst hβ
        refine Join.red_left (Lambda.reduces_lam (reduces_single (step_app_cont _ _ _ _))) ?_
        refine Join.lam (Join.app IH (Join.of_eq ?_))
        simp [upd]
      · refine Join.lam (Join.app IH (Join.of_eq ?_))
        simp [upd, hβ]

/-- Environments that send term variables to abstractions. -/
def EnvLam (Γ : List Entry) (ρ : ℕ → Lambda) : Prop :=
  ∀ i A, Γ[i]? = some (.tm A) → ∃ C, ρ i = .lam C

theorem EnvLam.liftE {Γ : List Entry} {ρ : ℕ → Lambda} (h : EnvLam Γ ρ) : EnvLam Γ (liftE ρ) := by
  intro i A hi
  obtain ⟨C, hC⟩ := h i A hi
  exact ⟨Lambda.lift 1 1 C, by simp [LambdaMu.liftE, hC, Lambda.lift]⟩

theorem EnvLam.consT {Γ : List Entry} {ρ : ℕ → Lambda} (h : EnvLam Γ ρ) (A : Ty) :
    EnvLam (.tm A :: Γ) (consT ρ) := by
  intro i B hi
  cases i with
  | zero => exact ⟨_, rfl⟩
  | succ i =>
      obtain ⟨C, hC⟩ := h i B (by simpa using hi)
      exact ⟨Lambda.lift 1 1 C, by simp [LambdaMu.consT, hC, Lambda.lift]⟩

theorem EnvLam.consN {Γ : List Entry} {ρ : ℕ → Lambda} (h : EnvLam Γ ρ) (A : Ty) :
    EnvLam (.nm A :: Γ) (consN ρ) := by
  intro i B hi
  cases i with
  | zero => simp at hi
  | succ i =>
      obtain ⟨C, hC⟩ := h i B (by simpa using hi)
      exact ⟨Lambda.lift 1 1 C, by simp [LambdaMu.consN, hC, Lambda.lift]⟩

theorem cpsE_isLam {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) {ρ : ℕ → Lambda}
    (hρ : EnvLam Γ ρ) : ∃ C, cpsE ρ t = .lam C := by
  cases h with
  | var hi => exact hρ _ _ hi
  | lam _ => exact ⟨_, rfl⟩
  | app _ _ => exact ⟨_, rfl⟩
  | mu _ _ => exact ⟨_, rfl⟩

/-- Simulation of a β-step: the image of the redex reduces to the image of the reduct. -/
theorem cpsE_beta (M N : Tm) (ρ : ℕ → Lambda) (hnv : NamesVar (Tm.single N) M)
    (hR : ∃ C, cpsE ρ (Tm.subst (Tm.single N) M) = .lam C) (hN : ∃ C, cpsE ρ N = .lam C) :
    Lambda.reduces (cpsE ρ (.app (.lam M) N)) (cpsE ρ (Tm.subst (Tm.single N) M)) := by
  obtain ⟨C, hC⟩ := hR
  obtain ⟨D, hD⟩ := hN
  set K : Lambda := .lam (.app (.app (.var 0) (cpsE (liftE (liftE ρ)) N)) (.var 1)) with hK
  set B : Lambda := cpsE (consT (liftE (liftE ρ))) M with hB
  set B' : Lambda := cpsE (consT (liftE ρ)) M with hB'
  set Nn : Lambda := cpsE (liftE ρ) N with hNn
  set ρη : ℕ → Lambda := fun i => Lambda.subst Nn 0 (consT (liftE ρ) i) with hρη
  -- step 1
  have s1 : Lambda.step (.app (.lam (.app (.var 0) (.lam B))) K) (.app K (.lam B')) := by
    have h := Lambda.step.beta (.app (.var 0) (.lam B)) K
    have e : Lambda.subst K 0 (.app (.var 0) (.lam B)) = .app K (.lam B') := by
      have e1 : (fun i => Lambda.subst (Lambda.lift 1 0 K) (0 + 1) (consT (liftE (liftE ρ)) i)) =
          consT (liftE ρ) := by
        rw [subst_consT]
        congr 1
        funext i
        exact Lambda.subst_lift _ _ 0
      simp only [Lambda.subst, hB, cpsE_subst, e1]
      simp
      exact hB'.symm
    rw [e] at h; exact h
  -- step 2
  have s2 : Lambda.step (.app K (.lam B')) (.app (.app (.lam B') Nn) (.var 0)) := by
    have h := Lambda.step.beta (.app (.app (.var 0) (cpsE (liftE (liftE ρ)) N)) (.var 1)) (.lam B')
    have e : Lambda.subst (.lam B') 0 (.app (.app (.var 0) (cpsE (liftE (liftE ρ)) N)) (.var 1)) =
        .app (.app (.lam B') Nn) (.var 0) := by
      rw [cpsE_liftE_eq (liftE ρ)]
      simp only [Lambda.subst, Lambda.subst_lift]
      simp
      exact hNn.symm
    rw [e] at h; exact h
  -- step 3
  have s3 : Lambda.step (.app (.app (.lam B') Nn) (.var 0)) (.app (cpsE ρη M) (.var 0)) := by
    have h := Lambda.step.app_left _ _ (.var 0) (Lambda.step.beta B' Nn)
    rw [hB', cpsE_subst] at h
    exact h
  -- step 4: the environment
  have s4 : Lambda.reduces (cpsE ρη M) (Lambda.lift 1 0 (.lam C)) := by
    rw [← hC, cpsE_substTm M _ ρ hnv, ← cpsE_liftE_eq]
    refine cpsE_reduces_env M _ _ ?_
    intro i
    cases i with
    | zero =>
        have hNl : Nn = Lambda.lift 1 0 (.lam D) := by rw [hNn, cpsE_liftE_eq, hD]
        have e0 : ρη 0 = .lam (.app (Lambda.lift 1 0 Nn) (.var 0)) := by
          simp only [hρη, consT, etaV, Lambda.subst]
          simp
        rw [e0]
        have hl : Nn = .lam (Lambda.lift 1 1 D) := by rw [hNl]; rfl
        rw [hl]
        refine reduces_single ?_
        have := step_eta_lam (Lambda.lift 1 1 D)
        simpa [liftE, Tm.single, hD, Lambda.lift] using this
    | succ i =>
        have e : ρη (i + 1) = Lambda.lift 1 0 (ρ i) := by
          simp only [hρη, consT, liftE]
          exact Lambda.subst_lift _ _ 0
        rw [e]
        exact .refl _
  -- assemble
  have hstart : cpsE ρ (.app (.lam M) N) = .lam (.app (.lam (.app (.var 0) (.lam B))) K) := by
    simp only [cpsE, hB, hK]
  rw [hstart, hC]
  refine Lambda.reduces_trans (Lambda.reduces_lam (reduces_single s1)) ?_
  refine Lambda.reduces_trans (Lambda.reduces_lam (reduces_single s2)) ?_
  refine Lambda.reduces_trans (Lambda.reduces_lam (reduces_single s3)) ?_
  refine Lambda.reduces_trans (Lambda.reduces_lam (Lambda.reduces_app s4 (.refl _))) ?_
  exact reduces_single (step_eta_lam C)

/-- Simulation of a renaming step: one β-step. -/
theorem cpsE_renameStep (β γ : ℕ) (t : Tm) (ρ : ℕ → Lambda) :
    Lambda.reduces (cpsE ρ (.mu β (.mu γ t)))
      (cpsE ρ (.mu (Tm.nameOf (Tm.single (.var β) γ)) (Tm.subst (Tm.single (.var β)) t))) := by
  set L := consN ρ β
  have he : (fun i => Lambda.subst L 0 (consN (consN ρ) i)) =
      (fun i => cpsE (consN ρ) (Tm.single (.var β) i)) := by
    funext i
    cases i with
    | zero => simp [consN, Lambda.subst, L, Tm.single, cpsE]
    | succ i => simp only [consN, Tm.single, cpsE]; exact Lambda.subst_lift _ _ 0
  have hname : consN ρ (Tm.nameOf (Tm.single (.var β) γ)) =
      Lambda.subst L 0 (consN (consN ρ) γ) := by
    rw [congrFun he γ]
    cases γ <;> rfl
  have h := Lambda.step.beta (.app (cpsE (consN (consN ρ)) t) (consN (consN ρ) γ)) L
  simp only [Lambda.subst, cpsE_subst, he] at h
  refine reduces_single ?_
  simp only [cpsE, cpsE_substTm t (Tm.single (.var β)) _ (namesVar_of_allVar t _ (fun i => by
    cases i with
    | zero => exact ⟨β, rfl⟩
    | succ i => exact ⟨i, rfl⟩)), hname]
  exact Lambda.step.lam _ _ h

/-- Simulation of a structural step: a common reduct. -/
theorem cpsE_struct (β : ℕ) (t u : Tm) (ρ : ℕ → Lambda) (ht : TermFree 0 t) :
    Join (cpsE ρ (.app (.mu β t) u))
      (cpsE ρ (.mu β (if β = 0 then .app (Tm.sstr 0 (Tm.ren Nat.succ u) t) (Tm.ren Nat.succ u)
        else Tm.sstr 0 (Tm.ren Nat.succ u) t))) := by
  set v := Tm.ren Nat.succ u
  set Kn := KontT (consN ρ 0) (cpsE (consN ρ) v)
  set K₀ : Lambda := .lam (.app (.app (.var 0) (cpsE (liftE (liftE ρ)) u)) (.var 1))
  have hK : K₀ = Kn := by
    simp only [K₀, Kn, KontT, v, cpsE_ren_succ_consN, cpsE_liftE_eq]
    simp [consN, Lambda.lift]
  have henv : (fun i => Lambda.subst K₀ 0 (consN (liftE ρ) i)) = upd (consN ρ) 0 Kn := by
    funext i
    cases i with
    | zero => simp [consN, upd, Lambda.subst, hK]
    | succ i =>
        simp only [consN, upd, liftE, if_neg (Nat.succ_ne_zero i)]
        exact Lambda.subst_lift _ _ 0
  have hstep : Lambda.step (cpsE ρ (.app (.mu β t) u))
      (.lam (.app (cpsE (upd (consN ρ) 0 Kn) t) (upd (consN ρ) 0 Kn β))) := by
    have h := Lambda.step.beta (.app (cpsE (consN (liftE ρ)) t) (consN (liftE ρ) β)) K₀
    simp only [Lambda.subst, cpsE_subst, henv] at h
    have h2 := Lambda.step.lam _ _ h
    rw [← congrFun henv β]
    exact h2
  refine Join.red_left (reduces_single hstep) ?_
  have IH := cpsE_sstr t 0 v (consN ρ) ht
  simp only [cpsE]
  split_ifs with hβ
  · subst hβ
    refine Join.red_right (Lambda.reduces_lam (reduces_single (step_app_cont _ _ _ _))) ?_
    exact Join.lam (Join.app (by simpa [Kn] using IH.symm) (Join.of_eq (by simp [upd, Kn])))
  · exact Join.lam (Join.app (by simpa [Kn] using IH.symm) (Join.of_eq (by simp [upd, hβ])))

theorem namesVar_single_of_typ {Γ : List Entry} {M : Tm} {A B : Ty} (hM : Typ (.tm A :: Γ) M B)
    (N : Tm) : NamesVar (Tm.single N) M := by
  refine namesVar_of_typ hM ?_
  intro i C hi
  cases i with
  | zero => simp at hi
  | succ i => exact ⟨i, rfl⟩

/-- Simulation relative to an environment. -/
theorem cpsE_step {t t' : Tm} (hs : Step t t') :
    ∀ {Γ : List Entry} {A : Ty} {ρ : ℕ → Lambda}, Typ Γ t A → EnvLam Γ ρ →
      Join (cpsE ρ t) (cpsE ρ t') := by
  induction hs with
  | beta M N =>
      intro Γ A ρ h hρ
      have hred := Typ.step (.beta M N) h
      cases h with
      | app hM hN =>
          cases hM with
          | lam hM =>
              exact Join.of_reduces (cpsE_beta M N ρ (namesVar_single_of_typ hM N)
                (cpsE_isLam hred hρ) (cpsE_isLam hN hρ))
  | struct β t u =>
      intro Γ A ρ h hρ
      cases h with
      | app ht hu =>
          cases ht with
          | mu ht hβ => exact cpsE_struct β t u ρ (termFree_of_typ ht (a := 0) rfl)
  | rename β γ t => intro Γ A ρ h hρ; exact Join.of_reduces (cpsE_renameStep β γ t ρ)
  | lam _ ih =>
      intro Γ A ρ h hρ
      cases h with
      | lam h => exact Join.lam (Join.app (Join.refl _) (Join.lam (ih h (hρ.liftE.consT _))))
  | appL u _ ih =>
      intro Γ A ρ h hρ
      cases h with
      | app ht hu => exact Join.lam (Join.app (ih ht hρ.liftE) (Join.refl _))
  | appR t _ ih =>
      intro Γ A ρ h hρ
      cases h with
      | app ht hu =>
          exact Join.lam (Join.app (Join.refl _) (Join.lam (Join.app
            (Join.app (Join.refl _) (ih hu hρ.liftE.liftE)) (Join.refl _))))
  | mu β _ ih =>
      intro Γ A ρ h hρ
      cases h with
      | mu h hβ => exact Join.lam (Join.app (ih h (hρ.consN _)) (Join.refl _))

theorem envLam_etaV (Γ : List Entry) : EnvLam Γ etaV := fun _ _ _ => ⟨_, rfl⟩

/-- **Simulation**: one λμ step becomes a β-conversion of the CPS images (the images of a
well-typed term and of its reduct have a common β-reduct). -/
theorem cps_step {Γ : List Entry} {t t' : Tm} {A : Ty} (h : Typ Γ t A) (hs : Step t t') :
    ∃ c, Lambda.reduces (cps t) c ∧ Lambda.reduces (cps t') c :=
  cpsE_step hs h (envLam_etaV Γ)

/-- For a β-step the image of the redex reduces to the image of the reduct. -/
theorem cps_beta {Γ : List Entry} {M N : Tm} {A : Ty} (h : Typ Γ (.app (.lam M) N) A) :
    Lambda.reduces (cps (.app (.lam M) N)) (cps (Tm.subst (Tm.single N) M)) := by
  have hred := Typ.step (.beta M N) h
  cases h with
  | app hM hN =>
      cases hM with
      | lam hM =>
          exact cpsE_beta M N etaV (namesVar_single_of_typ hM N)
            (cpsE_isLam hred (envLam_etaV Γ)) (cpsE_isLam hN (envLam_etaV Γ))

/-- For a renaming step the image of the redex reduces to the image of the reduct. -/
theorem cps_rename (β γ : ℕ) (t : Tm) :
    Lambda.reduces (cps (.mu β (.mu γ t)))
      (cps (.mu (Tm.nameOf (Tm.single (.var β) γ)) (Tm.subst (Tm.single (.var β)) t))) :=
  cpsE_renameStep β γ t etaV

end LambdaMu
