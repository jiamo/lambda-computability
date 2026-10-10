import Start.PTSCube
import Start.PTSTyping

/-!
# The library's `λΠ` embeds in the `λP` corner of the cube

This library's own module (task `M23-LAMBDAPI-EMBED`).  `Start/PTSLambdaPi.lean` and
`Start/PTSCube.lean` translate derivations of the `λP` corner into the library's `λΠ`
(`cube_lambdaP_toTyping`).  This module gives the other direction:

* `PureTypeSystem.ofTm : LambdaPi.Tm → Expr Srt`, inverse to `toTm` (`toTm_ofTm`, `ofTm_toTm`),
  compatible with renaming (`ofTm_rename`), substitution (`ofTm_subst`), instantiation
  (`ofTm_inst`), β-steps (`step_ofTm`) and conversion (`conv_ofTm`; conversely
  `converts_iff_conv`);
* `PureTypeSystem.typing_ofTm` — **every `λΠ` derivation `Γ ⊢ t : A` in a well-formed context
  translates to a `HasType (cubeSpec lambdaP)` derivation** of `Γ.map ofTm ⊢ ofTm t : ofTm A`;
* `PureTypeSystem.wf_ofTm` — well-formed `λΠ` contexts translate to valid contexts.

The well-formedness hypothesis is needed: the `λΠ` rules for sorts and variables have no
context premise, while the framework's axiom rule holds in the empty context only and is carried
into longer contexts by weakening, which asks for the context to be valid.
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt Tm)

/-- The `λΠ` syntax as framework syntax. -/
def ofTm : Tm → Expr Srt
  | .var n => .var n
  | .sort s => .sort s
  | .app f a => .app (ofTm f) (ofTm a)
  | .lam A b => .lam (ofTm A) (ofTm b)
  | .pi A B => .pi (ofTm A) (ofTm B)

@[simp] theorem toTm_ofTm (t : Tm) : toTm (ofTm t) = t := by
  induction t with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [ofTm, toTm, ihf, iha]
  | lam A b ihA ihb => simp only [ofTm, toTm, ihA, ihb]
  | pi A B ihA ihB => simp only [ofTm, toTm, ihA, ihB]

@[simp] theorem ofTm_toTm (M : Expr Srt) : ofTm (toTm M) = M := by
  induction M with
  | var n => rfl
  | sort s => rfl
  | app f a ihf iha => simp only [ofTm, toTm, ihf, iha]
  | lam A b ihA ihb => simp only [ofTm, toTm, ihA, ihb]
  | pi A B ihA ihB => simp only [ofTm, toTm, ihA, ihB]

theorem toTm_injective : Function.Injective toTm := fun M N h => by
  rw [← ofTm_toTm M, h, ofTm_toTm]

theorem ofTm_rename (t : Tm) (ρ : ℕ → ℕ) :
    ofTm (LambdaPi.rename ρ t) = (ofTm t).rename ρ := by
  apply toTm_injective
  rw [toTm_ofTm, toTm_rename, toTm_ofTm]

theorem ofTm_subst (t : Tm) (σ : ℕ → Tm) :
    ofTm (LambdaPi.subst σ t) = (ofTm t).subst (fun n => ofTm (σ n)) := by
  apply toTm_injective
  rw [toTm_ofTm, toTm_subst, toTm_ofTm]
  simp only [toTm_ofTm]

theorem ofTm_inst (b a : Tm) : ofTm (LambdaPi.inst a b) = (ofTm b).instantiate (ofTm a) := by
  apply toTm_injective
  rw [toTm_ofTm, toTm_instantiate, toTm_ofTm, toTm_ofTm]

theorem ofTm_shift (t : Tm) : ofTm (LambdaPi.shift t) = (ofTm t).rename Nat.succ :=
  ofTm_rename t Nat.succ

/-- A `λΠ` β-step is a framework β-step. -/
theorem step_ofTm {t u : Tm} (h : LambdaPi.Step t u) : Beta (ofTm t) (ofTm u) := by
  induction h with
  | beta A b a => rw [ofTm_inst]; exact Beta.head _ _ _
  | appL _ _ ih => exact Beta.app_left ih
  | appR _ _ ih => exact Beta.app_right ih
  | lamL _ _ ih => exact Beta.lam_domain ih
  | lamR _ _ ih => exact Beta.lam_body ih
  | piL _ _ ih => exact Beta.pi_domain ih
  | piR _ _ ih => exact Beta.pi_body ih

/-- `λΠ` conversion is framework conversion. -/
theorem conv_ofTm {t u : Tm} (h : LambdaPi.Conv t u) : Converts (ofTm t) (ofTm u) := by
  induction h with
  | refl => exact Relation.EqvGen.refl _
  | step _ hs ih => exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ (step_ofTm hs))
  | stepInv _ hs ih =>
      exact Relation.EqvGen.trans _ _ _ ih
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ (step_ofTm hs)))

/-- The two conversions agree under the translation. -/
theorem converts_iff_conv (M N : Expr Srt) : Converts M N ↔ LambdaPi.Conv (toTm M) (toTm N) :=
  ⟨converts_toTm, fun h => by simpa using conv_ofTm h⟩

/-- A `λΠ` lookup is a framework lookup. -/
theorem lookup_ofTm {Γ : LambdaPi.Ctx} {n : ℕ} {A : Tm} (h : LambdaPi.Lookup Γ n A) :
    Lookup (Γ.map ofTm) n (ofTm A) := by
  induction h with
  | zero Γ A => rw [ofTm_shift]; exact Lookup.zero _ _
  | succ B _ ih => rw [ofTm_shift]; exact Lookup.succ _ ih

/-- The translation of derivations, in any valid framework context translating the `λΠ`
context. -/
theorem typing_ofTm_aux {Γ : LambdaPi.Ctx} {t A : Tm} (h : LambdaPi.Typing Γ t A) :
    ∀ Δ : List (Expr Srt), ValidContext lambdaPiSpec Δ → Δ = Γ.map ofTm →
      HasType lambdaPiSpec Δ (ofTm t) (ofTm A) := by
  induction h with
  | ax Γ =>
      intro Δ hΔ _
      exact HasType.sort_of_valid hΔ ⟨rfl, rfl⟩
  | var hl =>
      intro Δ hΔ hΔe
      subst hΔe
      exact HasType.lookup hΔ (lookup_ofTm hl)
  | @pi Γ A B s t hr _ _ ihA ihB =>
      intro Δ hΔ hΔe
      have hA := ihA Δ hΔ hΔe
      have hB := ihB (ofTm A :: Δ) (.cons hΔ hA) (by rw [hΔe]; rfl)
      exact HasType.product hA hB ⟨hr, rfl⟩
  | @lam Γ A B b s _ _ ihP ihb =>
      intro Δ hΔ hΔe
      have hP := ihP Δ hΔ hΔe
      obtain ⟨s₁, hA⟩ := HasType.product_domain hP _ _ rfl
      have hb := ihb (ofTm A :: Δ) (.cons hΔ hA) (by rw [hΔe]; rfl)
      exact HasType.abstraction hb hP
  | @app Γ f a A B _ _ ihf iha =>
      intro Δ hΔ hΔe
      rw [ofTm_inst]
      exact HasType.application (ihf Δ hΔ hΔe) (iha Δ hΔ hΔe)
  | conv _ _ hc iht ihB =>
      intro Δ hΔ hΔe
      exact HasType.conversion (iht Δ hΔ hΔe) (ihB Δ hΔ hΔe) (conv_ofTm hc)

/-- Well-formed `λΠ` contexts translate to valid framework contexts. -/
theorem wf_ofTm_lambdaPi {Γ : LambdaPi.Ctx} (h : LambdaPi.Wf Γ) :
    ValidContext lambdaPiSpec (Γ.map ofTm) := by
  induction h with
  | nil => exact .nil
  | cons _ hA ih => exact .cons ih (typing_ofTm_aux hA _ ih rfl)

/-- Well-formed `λΠ` contexts translate to valid contexts of the `λP` corner. -/
theorem wf_ofTm {Γ : LambdaPi.Ctx} (h : LambdaPi.Wf Γ) :
    ValidContext (cubeSpec lambdaP) (Γ.map ofTm) := by
  rw [← lambdaPiSpec_eq_cube]
  exact wf_ofTm_lambdaPi h

/-- **The library's `λΠ` embeds in the `λP` corner**: every derivation `Γ ⊢ t : A` of
`Start/LambdaPiTyping.lean` in a well-formed context translates to a derivation of the `λP`
corner of the cube. -/
theorem typing_ofTm {Γ : LambdaPi.Ctx} {t A : Tm} (h : LambdaPi.Typing Γ t A)
    (hΓ : LambdaPi.Wf Γ) :
    HasType (cubeSpec lambdaP) (Γ.map ofTm) (ofTm t) (ofTm A) := by
  rw [← lambdaPiSpec_eq_cube]
  exact typing_ofTm_aux h _ (wf_ofTm_lambdaPi hΓ) rfl

/-- Round trip: a `λP`-corner judgement is derivable iff its `λΠ` image is (in a valid context). -/
theorem hasType_iff_typing {Γ : List (Expr Srt)} {M A : Expr Srt}
    (hΓ : ValidContext (cubeSpec lambdaP) Γ) :
    HasType (cubeSpec lambdaP) Γ M A ↔
      LambdaPi.Typing (Γ.map toTm) (toTm M) (toTm A) := by
  refine ⟨cube_lambdaP_toTyping, fun h => ?_⟩
  have hwf : LambdaPi.Wf (Γ.map toTm) := by
    rw [← lambdaPiSpec_eq_cube] at hΓ
    exact hΓ.toWf
  have := typing_ofTm h hwf
  simpa [List.map_map, Function.comp_def] using this

end PureTypeSystem
