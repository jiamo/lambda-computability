import Start.PTSTyping

/-!
# A verified type inference procedure for functional pure type systems

This module is this library's own (used by task `M23-HURKENS`).  It gives an executable,
fuel-bounded type inference function `PureTypeSystem.Check.infer` for pure type systems whose
axioms and rules are presented by partial functions, and proves it **sound** for the absorbed
typing relation `PureTypeSystem.HasType` (`Start/PTSBasic.lean`): whenever it returns a type,
there is a derivation.  It is incomplete (it may give up), which is harmless: it is used only to
certify concrete derivations, such as the typing of Hurkens' paradox.

* `step1` — one leftmost-outermost β-step, sound for `Beta`;
* `nf` — fuel-bounded normalization, sound for `Reduces`;
* `HasType.to_sort`, `HasType.to_pi` — moving a typing along a reduction of its type to a sort
  or a product (by regularity and subject reduction);
* `infer_sound` — **soundness of inference**.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace Check

universe u

variable {S : Type u}

/-- The application case of `step1`, given the steps of the two components. -/
def appStep (f a : Expr S) (sf sa : Option (Expr S)) : Option (Expr S) :=
  match f with
  | .lam _ b => some (b.instantiate a)
  | _ =>
      match sf with
      | some f' => some (.app f' a)
      | none => sa.map (.app f)

/-- The binder cases of `step1`. -/
def binStep (mk : Expr S → Expr S → Expr S) (A b : Expr S) (sA sb : Option (Expr S)) :
    Option (Expr S) :=
  match sA with
  | some A' => some (mk A' b)
  | none => sb.map (mk A)

/-- One leftmost-outermost β-step. -/
def step1 : Expr S → Option (Expr S)
  | .app f a => appStep f a (step1 f) (step1 a)
  | .lam A b => binStep .lam A b (step1 A) (step1 b)
  | .pi A B => binStep .pi A B (step1 A) (step1 B)
  | _ => none

theorem step1_sound {M : Expr S} : ∀ {N : Expr S}, step1 M = some N → Beta M N := by
  induction M with
  | var _ => intro N h; simp [step1] at h
  | sort _ => intro N h; simp [step1] at h
  | app f a ihf iha =>
      intro N h
      simp only [step1, appStep] at h
      cases f with
      | lam A b =>
          simp only [Option.some.injEq] at h
          subst h
          exact .head A b a
      | _ =>
          revert h ihf
          rcases step1 _ with _ | f' <;> intro ihf h
          all_goals first
            | (simp only [Option.some.injEq] at h; subst h; exact .app_left (ihf rfl))
            | (obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h; exact .app_right (iha ha))
  | lam A b ihA ihb =>
      intro N h
      simp only [step1, binStep] at h
      revert h ihA
      rcases step1 A with _ | A' <;> intro ihA h
      · obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .lam_body (ihb hb)
      · simp only [Option.some.injEq] at h
        subst h
        exact .lam_domain (ihA rfl)
  | pi A B ihA ihB =>
      intro N h
      simp only [step1, binStep] at h
      revert h ihA
      rcases step1 A with _ | A' <;> intro ihA h
      · obtain ⟨B', hB, rfl⟩ := Option.map_eq_some_iff.mp h
        exact .pi_body (ihB hB)
      · simp only [Option.some.injEq] at h
        subst h
        exact .pi_domain (ihA rfl)

/-- Fuel-bounded normalization by repeated leftmost-outermost steps. -/
def nf : ℕ → Expr S → Expr S
  | 0, M => M
  | k + 1, M =>
      match step1 M with
      | some N => nf k N
      | none => M

theorem nf_sound : ∀ (k : ℕ) (M : Expr S), Reduces M (nf k M)
  | 0, _ => .refl
  | k + 1, M => by
      simp only [nf]
      rcases h : step1 M with _ | N
      · exact .refl
      · exact Relation.ReflTransGen.head (step1_sound h) (nf_sound k N)

/-- Fuel-bounded convertibility test: equal normal forms. -/
def conv [DecidableEq S] (k : ℕ) (A B : Expr S) : Bool := decide (nf k A = nf k B)

theorem conv_sound [DecidableEq S] {k : ℕ} {A B : Expr S} (h : conv k A B = true) :
    Converts A B := by
  have he : nf k A = nf k B := of_decide_eq_true h
  exact .trans _ _ _ (nf_sound k A).converts (he ▸ .symm _ _ (nf_sound k B).converts)

/-- The type of a variable in a newest-first context. -/
def lookupTy : List (Expr S) → ℕ → Option (Expr S)
  | [], _ => none
  | A :: _, 0 => some (A.rename Nat.succ)
  | _ :: Γ, n + 1 => (lookupTy Γ n).map (Expr.rename Nat.succ)

theorem lookupTy_sound : ∀ {Γ : List (Expr S)} {n : ℕ} {T : Expr S},
    lookupTy Γ n = some T → Lookup Γ n T
  | [], _, _, h => by simp [lookupTy] at h
  | A :: Γ, 0, T, h => by
      simp only [lookupTy, Option.some.injEq] at h
      subst h
      exact .zero A Γ
  | A :: Γ, n + 1, T, h => by
      simp only [lookupTy] at h
      obtain ⟨T', hT', rfl⟩ := Option.map_eq_some_iff.mp h
      exact .succ A (lookupTy_sound hT')

def asSort : Expr S → Option S
  | .sort s => some s
  | _ => none

theorem asSort_eq {M : Expr S} {s : S} (h : asSort M = some s) : M = .sort s := by
  cases M <;> simp_all [asSort]

def asPi : Expr S → Option (Expr S × Expr S)
  | .pi A B => some (A, B)
  | _ => none

theorem asPi_eq {M A B : Expr S} (h : asPi M = some (A, B)) : M = .pi A B := by
  cases M <;> simp_all [asPi]

variable {P : Specification S}

/-- A typing may be moved along a reduction of its type to a sort. -/
theorem _root_.PureTypeSystem.HasType.to_sort {Γ : List (Expr S)} {M T : Expr S} {s : S} (h : HasType P Γ M T)
    (hr : Reduces T (.sort s)) : HasType P Γ M (.sort s) := by
  rcases h.regularity with ⟨t, rfl⟩ | ⟨u, hu⟩
  · cases (Normal.sort t).reduces_eq hr
    exact h
  · exact .conversion h (hu.subject_reduces hr) hr.converts

/-- A typing may be moved along a reduction of its type to a product. -/
theorem _root_.PureTypeSystem.HasType.to_pi {Γ : List (Expr S)} {M T A B : Expr S} (h : HasType P Γ M T)
    (hr : Reduces T (.pi A B)) : HasType P Γ M (.pi A B) := by
  rcases h.regularity with ⟨t, rfl⟩ | ⟨u, hu⟩
  · cases (Normal.sort t).reduces_eq hr
  · exact .conversion h (hu.subject_reduces hr) hr.converts

/-- Fuel-bounded type inference, for axioms and rules given by partial functions `ax`, `rl`;
`k` is the normalization fuel and `d` the recursion depth. -/
def infer [DecidableEq S] (ax : S → Option S) (rl : S → S → Option S) (k : ℕ) :
    ℕ → List (Expr S) → Expr S → Option (Expr S)
  | 0, _, _ => none
  | _ + 1, Γ, .var n => lookupTy Γ n
  | _ + 1, _, .sort s => (ax s).map Expr.sort
  | d + 1, Γ, .pi A B => do
      let s₁ ← asSort (nf k (← infer ax rl k d Γ A))
      let s₂ ← asSort (nf k (← infer ax rl k d (A :: Γ) B))
      let s₃ ← rl s₁ s₂
      pure (.sort s₃)
  | d + 1, Γ, .lam A b => do
      let s₁ ← asSort (nf k (← infer ax rl k d Γ A))
      let B ← infer ax rl k d (A :: Γ) b
      let s₂ ← asSort (nf k (← infer ax rl k d (A :: Γ) B))
      let _ ← rl s₁ s₂
      pure (.pi A B)
  | d + 1, Γ, .app f a => do
      let (A, B) ← asPi (nf k (← infer ax rl k d Γ f))
      let A' ← infer ax rl k d Γ a
      if conv k A' A then pure (B.instantiate a) else none

/-- **Soundness of type inference**: in a valid context, every type returned by `infer` is
derivable. -/
theorem infer_sound [DecidableEq S] {ax : S → Option S} {rl : S → S → Option S}
    (hax : ∀ s t, ax s = some t → P.axioms s t)
    (hrl : ∀ s₁ s₂ s₃, rl s₁ s₂ = some s₃ → P.rule s₁ s₂ s₃) (k : ℕ) :
    ∀ (d : ℕ) {Γ : List (Expr S)} {M T : Expr S}, ValidContext P Γ →
      infer ax rl k d Γ M = some T → HasType P Γ M T := by
  intro d
  induction d with
  | zero => intro Γ M T _ h; simp [infer] at h
  | succ d ih =>
      intro Γ M T hΓ h
      cases M with
      | var n =>
          simp only [infer] at h
          exact HasType.lookup hΓ (lookupTy_sound h)
      | sort s =>
          simp only [infer] at h
          obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          exact HasType.sort_of_valid hΓ (hax _ _ ht)
      | pi A B =>
          simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨TA, hTA, s₁, hs₁, TB, hTB, s₂, hs₂, s₃, hs₃, rfl⟩ := h
          have hA := (ih hΓ hTA).to_sort ((asSort_eq hs₁) ▸ nf_sound k TA)
          have hB := (ih (.cons hΓ hA) hTB).to_sort ((asSort_eq hs₂) ▸ nf_sound k TB)
          exact .product hA hB (hrl _ _ _ hs₃)
      | lam A b =>
          simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
            Option.some.injEq] at h
          obtain ⟨TA, hTA, s₁, hs₁, B, hB, TB, hTB, s₂, hs₂, s₃, hs₃, rfl⟩ := h
          have hA := (ih hΓ hTA).to_sort ((asSort_eq hs₁) ▸ nf_sound k TA)
          have hb := ih (.cons hΓ hA) hB
          have hBs := (ih (.cons hΓ hA) hTB).to_sort ((asSort_eq hs₂) ▸ nf_sound k TB)
          exact .abstraction hb (.product hA hBs (hrl _ _ _ hs₃))
      | app f a =>
          simp only [infer, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨F, hF, ⟨A, B⟩, hAB, A', hA', h⟩ := h
          split_ifs at h with hc
          simp only [Option.pure_def, Option.some.injEq] at h
          subst h
          have hf := (ih hΓ hF).to_pi ((asPi_eq hAB) ▸ nf_sound k F)
          obtain ⟨u, hu⟩ := hf.regularity.resolve_left (by rintro ⟨_, h⟩; cases h)
          obtain ⟨s, hAs⟩ := hu.product_domain _ _ rfl
          exact .application hf (.conversion (ih hΓ hA') hAs (conv_sound hc))

end Check

end PureTypeSystem
