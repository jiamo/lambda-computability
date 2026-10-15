/-
**Completeness of Pollack's syntax-directed type checking for stratified functional PTSs.**

* `WhBeta`, `WhReduces`: weak-head β-reduction.
* `Functional P`: functional specifications (axioms and rules are partial functions).
* `HasTypeSD P Γ M A`: Pollack's syntax-directed system (Pollack 1992; Poll 1998, Definition 14),
  in de Bruijn form.  `HasTypeSD.toHasType`: soundness (Poll 1998, Theorem 15).
* `StdRed`, `Reduces.stdRed`: a standardization theorem (every reduction is a standard
  reduction, in the inductive form of Kashima / Loader), and from it
  `Converts.whReduces_pi`: a term convertible to a product weak-head reduces to a product.
* `HasType.type_unique_of_functional`: uniqueness of types up to conversion for functional
  specifications.
* `sd_complete_of_stratification`: for every functional specification with a `Stratification`,
  every judgement `Γ ⊢ M : A` has a syntax-directed derivation `Γ ⊢sd M : A'` with `A' =β A`.
  No normalization hypothesis.
* Corollaries: System U⁻ (`Hurkens.uMinus_sd_complete`), the four cube corners without
  dependent types (`cube_sd_complete`), and `W₀` (`BeyondPoll.W0_sd_complete`), a functional
  stratified specification with a well-typed type that has no normal form.
-/

import Start.PTSExpansionBeyondPoll

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

universe u

/-- Weak-head β-step: contracts the head redex of an application spine. -/
inductive WhBeta {S : Type u} : Expr S → Expr S → Prop
  | head (A b a : Expr S) : WhBeta (.app (.lam A b) a) (b.instantiate a)
  | app_left {f f' a : Expr S} : WhBeta f f' → WhBeta (.app f a) (.app f' a)

def WhReduces {S : Type u} : Expr S → Expr S → Prop := Relation.ReflTransGen WhBeta

def Functional {S : Type u} (P : Specification S) : Prop :=
  (∀ s t t', P.axioms s t → P.axioms s t' → t = t') ∧
  (∀ s₁ s₂ s₃ s₃', P.rule s₁ s₂ s₃ → P.rule s₁ s₂ s₃' → s₃ = s₃')

/-- Pollack's syntax-directed system (Pollack 1992; Poll 1998, Definition 14). -/
inductive HasTypeSD {S : Type u} (P : Specification S) :
    List (Expr S) → Expr S → Expr S → Prop
  | ax {s t} : P.axioms s t → HasTypeSD P ([]) (.sort s) (.sort t)
  | var {Γ A T s} : HasTypeSD P Γ A T → Reduces T (.sort s) →
      HasTypeSD P (A :: Γ) (.var 0) (A.rename Nat.succ)
  | weaken_var {Γ n B A T s} : HasTypeSD P Γ (.var n) B → HasTypeSD P Γ A T →
      Reduces T (.sort s) → HasTypeSD P (A :: Γ) (.var (n + 1)) (B.rename Nat.succ)
  | weaken_sort {Γ t B A T s} : HasTypeSD P Γ (.sort t) B → HasTypeSD P Γ A T →
      Reduces T (.sort s) → HasTypeSD P (A :: Γ) (.sort t) (B.rename Nat.succ)
  | product {Γ A B TA TB s₁ s₂ s₃} : HasTypeSD P Γ A TA → Reduces TA (.sort s₁) →
      HasTypeSD P (A :: Γ) B TB → Reduces TB (.sort s₂) → P.rule s₁ s₂ s₃ →
      HasTypeSD P Γ (.pi A B) (.sort s₃)
  | abstraction {Γ A b B T s} : HasTypeSD P (A :: Γ) b B →
      HasTypeSD P Γ (.pi A B) T → Reduces T (.sort s) →
      HasTypeSD P Γ (.lam A b) (.pi A B)
  | application {Γ f a F A' B A} : HasTypeSD P Γ f F → WhReduces F (.pi A' B) →
      HasTypeSD P Γ a A → Converts A A' → HasTypeSD P Γ (.app f a) (B.instantiate a)

/-! ### Weak-head reduction -/

namespace WhBeta

variable {S : Type u} {M N : Expr S}

theorem toBeta (h : WhBeta M N) : Beta M N := by
  induction h with
  | head A b a => exact .head A b a
  | app_left _ ih => exact .app_left ih

theorem subst (h : WhBeta M N) (σ : Nat → Expr S) : WhBeta (M.subst σ) (N.subst σ) := by
  induction h with
  | head A b a =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (WhBeta.head (A.subst σ) (b.subst (Expr.liftSub σ)) (a.subst σ))
  | app_left _ ih => exact .app_left ih

theorem rename (h : WhBeta M N) (ρ : Nat → Nat) : WhBeta (M.rename ρ) (N.rename ρ) := by
  induction h with
  | head A b a =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (WhBeta.head (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left _ ih => exact .app_left ih

end WhBeta

namespace WhReduces

variable {S : Type u} {M N : Expr S}

theorem refl (M : Expr S) : WhReduces M M := Relation.ReflTransGen.refl

theorem trans {M N K : Expr S} (h₁ : WhReduces M N) (h₂ : WhReduces N K) : WhReduces M K :=
  Relation.ReflTransGen.trans h₁ h₂

theorem tail {M N K : Expr S} (h₁ : WhReduces M N) (h₂ : WhBeta N K) : WhReduces M K :=
  Relation.ReflTransGen.tail h₁ h₂

theorem toReduces (h : WhReduces M N) : Reduces M N := by
  unfold WhReduces at h
  exact Relation.ReflTransGen.mono (fun _ _ h => WhBeta.toBeta h) _ _ h

theorem app_left (h : WhReduces M N) (a : Expr S) : WhReduces (.app M a) (.app N a) := by
  unfold WhReduces at *
  exact h.lift (fun x => Expr.app x a) (fun _ _ h => WhBeta.app_left h)

theorem subst (h : WhReduces M N) (σ : Nat → Expr S) : WhReduces (M.subst σ) (N.subst σ) := by
  unfold WhReduces at *
  exact h.lift (Expr.subst σ) (fun _ _ h => WhBeta.subst h σ)

theorem rename (h : WhReduces M N) (ρ : Nat → Nat) : WhReduces (M.rename ρ) (N.rename ρ) := by
  unfold WhReduces at *
  exact h.lift (Expr.rename ρ) (fun _ _ h => WhBeta.rename h ρ)

end WhReduces

/-! ### Standardization -/

/-- Standard reduction, in inductive form: weak-head reduce to a head shape, then reduce the
components standardly. -/
inductive StdRed {S : Type u} : Expr S → Expr S → Prop
  | var {M n} : WhReduces M (.var n) → StdRed M (.var n)
  | sort {M s} : WhReduces M (.sort s) → StdRed M (.sort s)
  | app {M P Q P' Q'} : WhReduces M (.app P Q) → StdRed P P' → StdRed Q Q' →
      StdRed M (.app P' Q')
  | lam {M A b A' b'} : WhReduces M (.lam A b) → StdRed A A' → StdRed b b' →
      StdRed M (.lam A' b')
  | pi {M A B A' B'} : WhReduces M (.pi A B) → StdRed A A' → StdRed B B' →
      StdRed M (.pi A' B')

namespace StdRed

variable {S : Type u}

theorem refl : ∀ M : Expr S, StdRed M M
  | .var _ => .var (WhReduces.refl _)
  | .sort _ => .sort (WhReduces.refl _)
  | .app f a => .app (WhReduces.refl _) (refl f) (refl a)
  | .lam A b => .lam (WhReduces.refl _) (refl A) (refl b)
  | .pi A B => .pi (WhReduces.refl _) (refl A) (refl B)

theorem wh_prefix {M M' N : Expr S} (hw : WhReduces M M') (h : StdRed M' N) : StdRed M N := by
  cases h with
  | var h => exact .var (hw.trans h)
  | sort h => exact .sort (hw.trans h)
  | app h hP hQ => exact .app (hw.trans h) hP hQ
  | lam h hA hb => exact .lam (hw.trans h) hA hb
  | pi h hA hB => exact .pi (hw.trans h) hA hB

theorem toReduces {M N : Expr S} (h : StdRed M N) : Reduces M N := by
  induction h with
  | var h => exact h.toReduces
  | sort h => exact h.toReduces
  | app h _ _ ihP ihQ => exact h.toReduces.trans (Reduces.app ihP ihQ)
  | lam h _ _ ihA ihb => exact h.toReduces.trans (Reduces.lam ihA ihb)
  | pi h _ _ ihA ihB => exact h.toReduces.trans (Reduces.pi ihA ihB)

theorem rename {M N : Expr S} (h : StdRed M N) (ρ : Nat → Nat) :
    StdRed (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | var h => exact .var (h.rename ρ)
  | sort h => exact .sort (h.rename ρ)
  | app h _ _ ihP ihQ => exact .app (h.rename ρ) (ihP ρ) (ihQ ρ)
  | lam h _ _ ihA ihb => exact .lam (h.rename ρ) (ihA ρ) (ihb _)
  | pi h _ _ ihA ihB => exact .pi (h.rename ρ) (ihA ρ) (ihB _)

theorem subst {M N : Expr S} (h : StdRed M N) (σ τ : Nat → Expr S)
    (hστ : ∀ n, StdRed (σ n) (τ n)) : StdRed (M.subst σ) (N.subst τ) := by
  have hlift : ∀ σ τ : Nat → Expr S, (∀ n, StdRed (σ n) (τ n)) →
      ∀ n, StdRed (Expr.liftSub σ n) (Expr.liftSub τ n) := by
    intro σ τ h n
    cases n with
    | zero => exact refl _
    | succ n => exact (h n).rename Nat.succ
  induction h generalizing σ τ with
  | @var M n h => exact wh_prefix (h.subst σ) (hστ n)
  | sort h => exact .sort (h.subst σ)
  | app h _ _ ihP ihQ => exact .app (h.subst σ) (ihP σ τ hστ) (ihQ σ τ hστ)
  | lam h _ _ ihA ihb =>
      exact .lam (h.subst σ) (ihA σ τ hστ) (ihb _ _ (hlift σ τ hστ))
  | pi h _ _ ihA ihB =>
      exact .pi (h.subst σ) (ihA σ τ hστ) (ihB _ _ (hlift σ τ hστ))

theorem instantiate {b b' a a' : Expr S} (hb : StdRed b b') (ha : StdRed a a') :
    StdRed (b.instantiate a) (b'.instantiate a') := by
  refine hb.subst _ _ (fun n => ?_)
  cases n with
  | zero => exact ha
  | succ n => exact refl _

/-- A standard reduction followed by one β-step is a standard reduction. -/
theorem beta {M N N' : Expr S} (h : StdRed M N) (hN : Beta N N') : StdRed M N' := by
  induction h generalizing N' with
  | var _ => cases hN
  | sort _ => cases hN
  | @app M P Q P' Q' hM hP hQ ihP ihQ =>
      cases hN with
      | head A' b' _ =>
          cases hP with
          | @lam _ A b _ _ hw hA hb =>
              have h1 : WhReduces M (.app (.lam A b) Q) := hM.trans (hw.app_left Q)
              have h2 : WhReduces M (b.instantiate Q) := h1.tail (WhBeta.head A b Q)
              exact wh_prefix h2 (instantiate hb hQ)
      | app_left h => exact .app hM (ihP h) hQ
      | app_right h => exact .app hM hP (ihQ h)
  | lam hM _ _ ihA ihb =>
      cases hN with
      | lam_domain h => exact .lam hM (ihA h) ‹_›
      | lam_body h => exact .lam hM ‹_› (ihb h)
  | pi hM _ _ ihA ihB =>
      cases hN with
      | pi_domain h => exact .pi hM (ihA h) ‹_›
      | pi_body h => exact .pi hM ‹_› (ihB h)

end StdRed

/-- **Standardization.** Every reduction is a standard reduction. -/
theorem Reduces.stdRed {S : Type u} {M N : Expr S} (h : Reduces M N) : StdRed M N := by
  induction h with
  | refl => exact StdRed.refl _
  | tail _ hs ih => exact ih.beta hs

/-- A term that reduces to a product weak-head reduces to a product whose components reduce to
the given ones. -/
theorem Reduces.whReduces_pi {S : Type u} {F A B : Expr S} (h : Reduces F (.pi A B)) :
    ∃ A' B', WhReduces F (.pi A' B') ∧ Reduces A' A ∧ Reduces B' B := by
  cases h.stdRed with
  | pi hw hA hB => exact ⟨_, _, hw, hA.toReduces, hB.toReduces⟩

/-- **Weak-head standardization to a product.** A term convertible to a product weak-head
reduces to a product with convertible components. -/
theorem Converts.whReduces_pi {S : Type u} {F A B : Expr S} (h : Converts F (.pi A B)) :
    ∃ A' B', WhReduces F (.pi A' B') ∧ Converts A' A ∧ Converts B' B := by
  obtain ⟨K, hF, hK⟩ := h.join
  obtain ⟨A₁, B₁, rfl, hA₁, hB₁⟩ := Reduces.pi_inv hK
  obtain ⟨A', B', hw, hA', hB'⟩ := hF.whReduces_pi
  exact ⟨A', B', hw, .trans _ _ _ hA'.converts (.symm _ _ hA₁.converts),
    .trans _ _ _ hB'.converts (.symm _ _ hB₁.converts)⟩

/-! ### Soundness -/

namespace HasType

variable {S : Type u} {P : Specification S}

/-- A typing judgement survives reduction of the type. -/
theorem reduces_type {Γ : List (Expr S)} {M T T' : Expr S} (h : HasType P Γ M T)
    (hr : Reduces T T') : HasType P Γ M T' := by
  rcases h.regularity with ⟨s, rfl⟩ | ⟨s, hT⟩
  · rw [HasTypeR.sort_reduces hr]
    exact h
  · exact .conversion h (hT.subject_reduces hr) hr.converts

end HasType

/-- **Soundness of the syntax-directed system** (Poll 1998, Theorem 15). -/
theorem HasTypeSD.toHasType {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {M A : Expr S} (h : HasTypeSD P Γ M A) : HasType P Γ M A := by
  induction h with
  | ax h => exact .ax h
  | var _ hT ih => exact .var (ih.reduces_type hT)
  | weaken_var _ _ hT ihM ihA => exact HasType.weaken ihM (ihA.reduces_type hT)
  | weaken_sort _ _ hT ihM ihA => exact HasType.weaken ihM (ihA.reduces_type hT)
  | product _ hTA _ hTB hr ihA ihB =>
      exact .product (ihA.reduces_type hTA) (ihB.reduces_type hTB) hr
  | abstraction _ _ hT ihb ihP => exact .abstraction ihb (ihP.reduces_type hT)
  | application _ hw _ hc ihf iha =>
      have hf := ihf.reduces_type hw.toReduces
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, hA'⟩ := hPi.product_domain _ _ rfl
      exact .application hf (.conversion iha hA' hc)

/-! ### Uniqueness of types for functional specifications -/

/-- **Uniqueness of types** up to conversion, for functional specifications. -/
theorem HasType.type_unique_of_functional {S : Type u} {P : Specification S}
    (hf : Functional P) {Γ : List (Expr S)} {M T T' : Expr S}
    (hT : HasType P Γ M T) (hT' : HasType P Γ M T') : Converts T T' := by
  induction M generalizing Γ T T' with
  | var n =>
      obtain ⟨D, hD, hcD⟩ := hT.generation
      obtain ⟨E, hE, hcE⟩ := hT'.generation
      rw [hD.unique hE] at hcD
      exact .trans _ _ _ hcD (.symm _ _ hcE)
  | sort s =>
      obtain ⟨t, ht, hc⟩ := hT.generation
      obtain ⟨t', ht', hc'⟩ := hT'.generation
      rw [hf.1 _ _ _ ht ht'] at hc
      exact .trans _ _ _ hc (.symm _ _ hc')
  | app F a ihF _ =>
      obtain ⟨D, E, hF, -, hc⟩ := hT.generation_app
      obtain ⟨D', E', hF', -, hc'⟩ := hT'.generation_app
      have he := (ihF hF hF').product_compatibility.2
      exact .trans _ _ _ hc (.trans _ _ _ (he.subst (Expr.single a)) (.symm _ _ hc'))
  | lam D b _ ihb =>
      obtain ⟨B₁, s, hb, -, hc⟩ := hT.generation_lam
      obtain ⟨B₂, s', hb', -, hc'⟩ := hT'.generation_lam
      exact .trans _ _ _ hc (.trans _ _ _ (Converts.pi (.refl _) (ihb hb hb')) (.symm _ _ hc'))
  | pi D E ihD ihE =>
      obtain ⟨s₁, s₂, s₃, hD, hE, hr, hc⟩ := hT.generation_pi
      obtain ⟨s₁', s₂', s₃', hD', hE', hr', hc'⟩ := hT'.generation_pi
      obtain rfl : s₁ = s₁' := Converts.sort_inj (ihD hD hD')
      obtain rfl : s₂ = s₂' := Converts.sort_inj (ihE hE hE')
      rw [hf.2 _ _ _ _ hr hr'] at hc
      exact .trans _ _ _ hc (.symm _ _ hc')

/-! ### Contexts for the syntax-directed system -/

/-- Contexts whose declarations are syntax-directed typed by a type reducing to a sort. -/
inductive ValidContextSD {S : Type u} (P : Specification S) : List (Expr S) → Prop
  | nil : ValidContextSD P ([])
  | cons {Γ A T s} : ValidContextSD P Γ → HasTypeSD P Γ A T → Reduces T (.sort s) →
      ValidContextSD P (A :: Γ)

namespace ValidContextSD

variable {S : Type u} {P : Specification S}

theorem lookup {Γ : List (Expr S)} (hΓ : ValidContextSD P Γ) {n : Nat} {A : Expr S}
    (hn : Lookup Γ n A) : HasTypeSD P Γ (.var n) A := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons _ hB hT ih =>
      cases hn with
      | zero => exact .var hB hT
      | succ _ hn => exact .weaken_var (ih hn) hB hT

theorem sort {Γ : List (Expr S)} (hΓ : ValidContextSD P Γ) {s t : S} (hst : P.axioms s t) :
    HasTypeSD P Γ (.sort s) (.sort t) := by
  induction hΓ with
  | nil => exact .ax hst
  | cons _ hB hT ih => exact .weaken_sort ih hB hT

end ValidContextSD

/-! ### The core lemma -/

namespace Stratification

variable {S : Type u} {P : Specification S} {L : Stratification P}

theorem sd_core_aux (hf : Functional P) (n : ℕ) : ∀ (M : Expr S) (Γ : List (Expr S))
    (T : Expr S) (k : ℕ), L.bound + 2 - k ≤ n → ValidContextSD P Γ → HasType P Γ M T →
    L.TypeLevel Γ T k → ∃ T', HasTypeSD P Γ M T' ∧ Converts T' T := by
  induction n with
  | zero =>
      intro M Γ T k hn _ _ hT
      have := hT.le
      omega
  | succ n ihn =>
      intro M
      induction M with
      | var m =>
          intro Γ T k _ hΓ ht _
          obtain ⟨A, hA, hc⟩ := ht.generation
          exact ⟨A, hΓ.lookup hA, .symm _ _ hc⟩
      | sort t =>
          intro Γ T k _ hΓ ht _
          obtain ⟨r, hr, hc⟩ := ht.generation
          exact ⟨_, hΓ.sort hr, .symm _ _ hc⟩
      | pi A B ihA ihB =>
          intro Γ T k hn hΓ ht hT
          obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := ht.generation_pi
          have l := L.rule_level _ _ _ hr
          have hk := conv_level hc hT (TypeLevel.sort L Γ s₃)
          obtain ⟨TA, hA', hTA⟩ := ihA Γ _ _ (by omega) hΓ hA (TypeLevel.sort L Γ s₁)
          have hTA' := Converts.reduces_sort hTA
          obtain ⟨TB, hB', hTB⟩ := ihB (A :: Γ) _ _ (by omega) (.cons hΓ hA' hTA') hB
            (TypeLevel.sort L _ s₂)
          exact ⟨_, .product hA' hTA' hB' (Converts.reduces_sort hTB) hr, .symm _ _ hc⟩
      | app f a ihf iha =>
          intro Γ T k hn hΓ ht hT
          obtain ⟨D, E, hf, ha, hc⟩ := ht.generation_app
          obtain ⟨r, hPi⟩ := hf.product_type_sorted
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hrc⟩ := hPi.generation_pi
          obtain rfl := hrc.sort_inj
          have l := L.rule_level _ _ _ hr
          have hEa : HasType P Γ (E.instantiate a) (.sort r₂) := hE.instantiate ha
          have hk := conv_level hc hT (.inr ⟨r₂, hEa, rfl⟩)
          obtain ⟨F, hF, hFc⟩ := ihf Γ _ _ (by omega) hΓ hf (.inr ⟨_, hPi, rfl⟩)
          obtain ⟨Da, ha', hDa⟩ := iha Γ _ _ (by omega) hΓ ha (.inr ⟨r₁, hD, rfl⟩)
          obtain ⟨A', B', hw, hA', hB'⟩ := hFc.whReduces_pi
          exact ⟨_, .application hF hw ha' (.trans _ _ _ hDa (.symm _ _ hA')),
            .trans _ _ _ (hB'.subst (Expr.single a)) (.symm _ _ hc)⟩
      | lam A b ihA ihb =>
          intro Γ T k hn hΓ ht hT
          obtain ⟨B, s, hb, hPi, hc⟩ := ht.generation_lam
          obtain ⟨s₁, s₂, s₃, hA, hB, hr, hsc⟩ := hPi.generation_pi
          obtain rfl := hsc.sort_inj
          have l := L.rule_level _ _ _ hr
          have hk := conv_level hc hT (.inr ⟨_, hPi, rfl⟩)
          have hs := L.level_le s
          obtain ⟨TA, hA', hTA⟩ := ihA Γ _ _ (by omega) hΓ hA (TypeLevel.sort L Γ s₁)
          have hTA' := Converts.reduces_sort hTA
          obtain ⟨Bsd, hb', hBc⟩ := ihb (A :: Γ) _ _ (by omega) (.cons hΓ hA' hTA') hb
            (.inr ⟨s₂, hB, rfl⟩)
          -- The syntax-directed type of the body is typed by `s₂`.  This is the only place
          -- where functionality is used (through uniqueness of types).
          have hBsd : HasType P (A :: Γ) Bsd (.sort s₂) := by
            obtain ⟨t, rfl⟩ | ⟨t, hBt⟩ := hb'.toHasType.regularity
            · exact hB.subject_reduces (Converts.reduces_sort (.symm _ _ hBc))
            · obtain ⟨C, h1, h2⟩ := hBc.join
              have e := HasType.type_unique_of_functional hf (hBt.subject_reduces h1)
                (hB.subject_reduces h2)
              obtain rfl := e.sort_inj
              exact hBt
          have hPi' : HasType P Γ (.pi A Bsd) (.sort s) := .product hA hBsd hr
          obtain ⟨U, hPiSD, hU⟩ := ihn _ Γ _ _ (by omega) hΓ hPi' (TypeLevel.sort L Γ s)
          exact ⟨_, .abstraction hb' hPiSD (Converts.reduces_sort hU),
            .trans _ _ _ (Converts.pi (.refl _) hBc) (.symm _ _ hc)⟩

/-- **Core lemma.** In a context valid for the syntax-directed system, every typing judgement
has a syntax-directed derivation at a convertible type. -/
theorem sd_core (hf : Functional P) (L : Stratification P) {Γ : List (Expr S)} {M T : Expr S}
    (hΓ : ValidContextSD P Γ) (h : HasType P Γ M T) :
    ∃ T', HasTypeSD P Γ M T' ∧ Converts T' T := by
  obtain ⟨t, rfl⟩ | ⟨s, hs⟩ := h.regularity
  · exact sd_core_aux (L := L) hf (L.bound + 2) M Γ _ _ (by omega) hΓ h (TypeLevel.sort L Γ t)
  · exact sd_core_aux (L := L) hf (L.bound + 2) M Γ _ _ (by omega) hΓ h (.inr ⟨s, hs, rfl⟩)

theorem validContextSD (hf : Functional P) (L : Stratification P) {Γ : List (Expr S)}
    (hΓ : ValidContext P Γ) : ValidContextSD P Γ := by
  induction hΓ with
  | nil => exact .nil
  | cons _ hA ih =>
      obtain ⟨T, hT, hc⟩ := sd_core hf L ih hA
      exact .cons ih hT (Converts.reduces_sort hc)

end Stratification

/-- **Completeness of Pollack's syntax-directed system for stratified functional PTSs.**
No normalization hypothesis. -/
theorem sd_complete_of_stratification {S : Type u} {P : Specification S}
    (hf : Functional P) (L : Stratification P) {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) : ∃ A', HasTypeSD P Γ M A' ∧ Converts A' A :=
  Stratification.sd_core hf L (Stratification.validContextSD hf L h.valid) h

/-! ### Corollaries -/

namespace Hurkens

theorem uMinus_functional : Functional uMinus := by
  refine ⟨fun s t t' h h' => ?_, fun s₁ s₂ s₃ s₃' h h' => h.1.trans h'.1.symm⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
    first | rfl | cases h1

/-- **Syntax-directed completeness for System U⁻.** -/
theorem uMinus_sd_complete {Γ : List (Expr USort)} {M A : Expr USort}
    (h : HasType uMinus Γ M A) : ∃ A', HasTypeSD uMinus Γ M A' ∧ Converts A' A :=
  sd_complete_of_stratification uMinus_functional uMinus_stratified h

end Hurkens

theorem cube_functional (f : CubeFeatures) : Functional (cubeSpec f) :=
  ⟨fun _ _ _ h h' => cube_axioms_functional f h h', fun _ _ _ _ h h' => h.1.trans h'.1.symm⟩

/-- **Syntax-directed completeness for the cube corners without dependent types**
(`λ→`, `λ2`, `λω̲`, `λω`). -/
theorem cube_sd_complete (f : CubeFeatures) (hd : f.dep = false)
    {Γ : List (Expr LambdaPi.Srt)} {M A : Expr LambdaPi.Srt} (h : HasType (cubeSpec f) Γ M A) :
    ∃ A', HasTypeSD (cubeSpec f) Γ M A' ∧ Converts A' A :=
  sd_complete_of_stratification (cube_functional f) (cube_stratified f hd) h

namespace BeyondPoll

open Hurkens

/-- The sorts of `W₀`. -/
inductive W0Sort | o | t | k | u
  deriving DecidableEq, Repr

/-- `W₀`: `W` without the sort `t'`.  Axioms `o : t`, `t : k`, `k : u`; rules `(o,o,o)`,
`(t,t,t)`, `(k,t,t)`, `(k,k,k)`, `(u,k,k)`. -/
def W0 : Specification W0Sort where
  axioms a b := (a = .o ∧ b = .t) ∨ (a = .t ∧ b = .k) ∨ (a = .k ∧ b = .u)
  rule s₁ s₂ s₃ := s₃ = s₂ ∧
    ((s₁ = .o ∧ s₂ = .o) ∨ (s₁ = .t ∧ s₂ = .t) ∨ (s₁ = .k ∧ s₂ = .t) ∨
      (s₁ = .k ∧ s₂ = .k) ∨ (s₁ = .u ∧ s₂ = .k))

/-- Levels `o ↦ 0`, `t ↦ 1`, `k ↦ 2`, `u ↦ 3`. -/
def W0_stratified : Stratification W0 where
  level
    | .o => 0
    | .t => 1
    | .k => 2
    | .u => 3
  bound := 3
  level_le s := by cases s <;> decide
  axiom_level a b h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  rule_level s₁ s₂ s₃ h := by
    obtain ⟨rfl, h⟩ := h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- `W₀` is functional. -/
theorem W0_functional : Functional W0 := by
  refine ⟨fun s a b h h' => ?_, fun s₁ s₂ s₃ s₃' h h' => h.1.trans h'.1.symm⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases h' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;> first | rfl | cases h1

/-- The embedding of U⁻ into `W₀`: `∗ ↦ t`, `□ ↦ k`, `△ ↦ u`. -/
def shift0 : USort → W0Sort
  | .star => .t
  | .box => .k
  | .tri => .u

/-- Hurkens' term moved up one level, in `W₀`. -/
def hurkensW0 : Expr W0Sort := hurkens.mapSort shift0

theorem W0_hurkens_typed : HasType W0 ([]) hurkensW0 (.pi (.sort .t) (.var 0)) := by
  have h := hurkens_typed.mapSort shift0 (Q := W0)
    (by
      intro a b h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩))
    (by
      intro a b c h
      obtain ⟨rfl, h⟩ := h
      refine ⟨rfl, ?_⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
  exact h

/-- `W₀` is not weakly normalizing. -/
theorem W0_not_wn : ¬ SystemWeaklyNormalizing W0 := fun h =>
  not_wn_of_closed_bot W0_hurkens_typed
    (h ([]) .nil hurkensW0 ⟨_, .inl W0_hurkens_typed⟩)

/-- The closed type `L o`, with `L` Hurkens' term in `W₀`. -/
def typeA0 : Expr W0Sort := .app hurkensW0 (.sort .o)

theorem typeA0_typed : HasType W0 ([]) typeA0 (.sort .o) :=
  HasType.application W0_hurkens_typed (.ax (Or.inl ⟨rfl, rfl⟩))

/-- No closed normal term has type `o` in `W₀`. -/
theorem W0_closed_normal_not_o {N : Expr W0Sort} (h : HasType W0 ([]) N (.sort .o))
    (hn : Normal N) : False := by
  induction N with
  | var n => exact neutral_nil_untyped (.var n) h
  | sort s =>
      obtain ⟨r, hr, hc⟩ := h.generation
      obtain rfl := hc.sort_inj
      rcases hr with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> cases h
  | app f a _ _ =>
      obtain ⟨s, h'⟩ | hne | ⟨A, B, h'⟩ | ⟨A, b, h'⟩ := h.normal_shape hn
      · cases h'
      · exact neutral_nil_untyped hne h
      · cases h'
      · cases h'
  | lam A b _ _ => exact h.lambda_cannot_have_sort_type
  | pi A B ihA _ =>
      obtain ⟨s₁, s₂, s₃, hA, -, hr, hc⟩ := h.generation_pi
      obtain rfl := hc.sort_inj
      obtain ⟨rfl, hr⟩ := hr
      rcases hr with ⟨rfl, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · exact ihA hA hn.pi_domain
      all_goals cases h

/-- **A well-typed closed type with no normal form in `W₀`.** -/
theorem W0_type_not_wn : HasType W0 ([]) typeA0 (.sort .o) ∧ ¬ WeaklyNormalizing typeA0 := by
  refine ⟨typeA0_typed, ?_⟩
  rintro ⟨N, hr, hn⟩
  exact W0_closed_normal_not_o (typeA0_typed.subject_reduces hr) hn

/-- **Syntax-directed completeness for `W₀`**, a functional stratified specification that has a
well-typed type with no normal form. -/
theorem W0_sd_complete {Γ : List (Expr W0Sort)} {M A : Expr W0Sort} (h : HasType W0 Γ M A) :
    ∃ A', HasTypeSD W0 Γ M A' ∧ Converts A' A :=
  sd_complete_of_stratification W0_functional W0_stratified h

/-- `W₀` is functional and stratified, and has a well-typed type without a normal form. -/
theorem W0_in_class : Functional W0 ∧ Nonempty (Stratification W0) ∧
    ∃ T s, HasType W0 ([]) T (.sort s) ∧ ¬ WeaklyNormalizing T :=
  ⟨W0_functional, ⟨W0_stratified⟩, typeA0, .o, W0_type_not_wn⟩

end BeyondPoll

end PureTypeSystem
