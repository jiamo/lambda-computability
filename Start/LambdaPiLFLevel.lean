/-
**Levels and the erasure of `λΠ` types** — task `M23-LF-EQUIV-COMPLETE`.

Harper and Pfenning's algorithm is indexed by the *erasure* of a type to a simple type, which
forgets the objects a type depends on.  For the algorithm to be complete, two equal types must
have the same erasure.  Proving that with typed reduction needs subject reduction for η, hence
strengthening; this module avoids both with a purely syntactic invariant.

* `LambdaPi.Lvl L t k` — the **level** of a raw term: `0` for objects, `1` for types and type
  families, `2` for kinds.  The variables of the context have the levels recorded in `L`
  (`true` for a type variable), binders bind objects, arguments are objects, and the annotation
  of an abstraction is not looked at.  The level is unique (`Lvl.det`) and is preserved by raw
  β-steps (`Lvl.step`), raw η-steps (`Lvl.etaStep`) and the erasure of annotations
  (`Lvl.eraseAnn`).
* `LambdaPi.er` — the **erasure**: a product becomes an arrow, an abstraction and an
  application are transparent, every variable and every sort is the base type.  It is
  context-free, stable under renaming (`er_rename`), and under any substitution of terms of erasure
  `base` (`er_subst`); objects have erasure `base` (`er_of_lvl_zero`).  Hence it is invariant
  under raw β-steps of terms that have a level (`er_step`), under raw η-steps (`er_etaStep`), and
  under βη-conversion of terms with a level (`Lvl.betaEtaConv`, through Church–Rosser modulo
  annotations, `betaEtaConv_iff_join`).
* `TypingE.lvl` — **a typable term has a level**, one below the level of its type (`TyLvl`), in a
  context whose entries have levels (`CtxLvl`, which holds for every well-formed context,
  `WfE.ctxLvl`).
* Consequences: `TypingE.er_object` (an object has erasure `base`) and `TypingE.er_conv` (two
  βη-convertible terms typable by sorts have the same erasure, and the same sort).
-/

import Start.LambdaPiTypingE

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Levels -/

/-- The level of a variable of a context of levels: `1` for a type variable, `0` otherwise. -/
def varLvl (L : List Bool) (n : ℕ) : ℕ := if L.getD n false then 1 else 0

@[simp] theorem varLvl_cons_zero (b : Bool) (L : List Bool) :
    varLvl (b :: L) 0 = if b then 1 else 0 := rfl

@[simp] theorem varLvl_cons_succ (b : Bool) (L : List Bool) (n : ℕ) :
    varLvl (b :: L) (n + 1) = varLvl L n := by
  simp [varLvl]

theorem varLvl_le (L : List Bool) (n : ℕ) : varLvl L n ≤ 1 := by
  unfold varLvl; split <;> omega

/-- **The level of a raw term**: `0` objects, `1` types and type families, `2` kinds. -/
inductive Lvl : List Bool → Tm → ℕ → Prop
  | star (L : List Bool) : Lvl L (sort Srt.star) 2
  | var (L : List Bool) (n : ℕ) : Lvl L (var n) (varLvl L n)
  | pi {L : List Bool} {A B : Tm} {k : ℕ} : Lvl L A 1 → Lvl (false :: L) B k → 1 ≤ k →
      Lvl L (pi A B) k
  | lam {L : List Bool} {A b : Tm} {k : ℕ} : Lvl (false :: L) b k → k ≤ 1 → Lvl L (lam A b) k
  | app {L : List Bool} {f a : Tm} {k : ℕ} : Lvl L f k → Lvl L a 0 → k ≤ 1 → Lvl L (app f a) k

/-- The level is unique. -/
theorem Lvl.det {L : List Bool} {t : Tm} {k k' : ℕ} (h : Lvl L t k) (h' : Lvl L t k') :
    k = k' := by
  induction h generalizing k' with
  | star => cases h'; rfl
  | var L n => cases h'; rfl
  | pi _ _ _ _ ihB => cases h' with | pi _ hB' _ => exact ihB hB'
  | lam _ _ ih => cases h' with | lam hb' _ => exact ih hb'
  | app _ _ _ ihf _ => cases h' with | app hf' _ _ => exact ihf hf'

theorem Lvl.le_two {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) : k ≤ 2 := by
  induction h with
  | star => exact le_refl _
  | var L n => exact (varLvl_le L n).trans (by norm_num)
  | pi _ _ _ _ ihB => exact ihB
  | lam _ hk _ => omega
  | app _ _ hk _ _ => omega

/-- The top sort has no level. -/
theorem Lvl.not_box {L : List Bool} {k : ℕ} (h : Lvl L (sort Srt.box) k) : False := by
  cases h

theorem lvl_upr {L L' : List Bool} {ρ : ℕ → ℕ} (b : Bool)
    (h : ∀ n, L'.getD (ρ n) false = L.getD n false) :
    ∀ n, (b :: L').getD (upr ρ n) false = (b :: L).getD n false
  | 0 => rfl
  | n + 1 => by simpa [upr] using h n

theorem Lvl.rename {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) :
    ∀ {L' : List Bool} {ρ : ℕ → ℕ}, (∀ n, L'.getD (ρ n) false = L.getD n false) →
      Lvl L' (LambdaPi.rename ρ t) k := by
  induction h with
  | star L => intro L' ρ _; exact Lvl.star _
  | var L n =>
      intro L' ρ hρ
      have := Lvl.var L' (ρ n)
      simp only [varLvl, hρ n] at this
      exact this
  | pi _ _ hk ihA ihB => intro L' ρ hρ; exact Lvl.pi (ihA hρ) (ihB (lvl_upr false hρ)) hk
  | lam _ hk ih => intro L' ρ hρ; exact Lvl.lam (ih (lvl_upr false hρ)) hk
  | app _ _ hk ihf iha => intro L' ρ hρ; exact Lvl.app (ihf hρ) (iha hρ) hk

theorem Lvl.shift {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) (b : Bool) :
    Lvl (b :: L) (LambdaPi.shift t) k :=
  h.rename (fun _ => rfl)

theorem Lvl.of_rename {t : Tm} : ∀ {L L' : List Bool} {ρ : ℕ → ℕ} {k : ℕ},
    (∀ n, L'.getD (ρ n) false = L.getD n false) → Lvl L' (LambdaPi.rename ρ t) k → Lvl L t k := by
  induction t with
  | var n =>
      intro L L' ρ k hρ h
      cases h
      have := Lvl.var L n
      simp only [varLvl, ← hρ n] at this
      exact this
  | sort s =>
      intro L L' ρ k hρ h
      cases h
      exact Lvl.star _
  | app f a ihf iha =>
      intro L L' ρ k hρ h
      cases h with
      | app hf ha hk => exact Lvl.app (ihf hρ hf) (iha hρ ha) hk
  | lam A b _ ihb =>
      intro L L' ρ k hρ h
      cases h with
      | lam hb hk => exact Lvl.lam (ihb (lvl_upr false hρ) hb) hk
  | pi A B ihA ihB =>
      intro L L' ρ k hρ h
      cases h with
      | pi hA hB hk => exact Lvl.pi (ihA hρ hA) (ihB (lvl_upr false hρ) hB) hk

theorem Lvl.subst {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) :
    ∀ {L' : List Bool} {σ : ℕ → Tm}, (∀ n, Lvl L' (σ n) (varLvl L n)) →
      Lvl L' (LambdaPi.subst σ t) k := by
  have hup : ∀ {L L' : List Bool} {σ : ℕ → Tm}, (∀ n, Lvl L' (σ n) (varLvl L n)) →
      ∀ n, Lvl (false :: L') (up σ n) (varLvl (false :: L) n) := by
    intro L L' σ hσ n
    cases n with
    | zero => exact Lvl.var _ 0
    | succ n =>
        simp only [up_succ, varLvl_cons_succ]
        exact (hσ n).shift false
  induction h with
  | star L => intro L' σ _; exact Lvl.star _
  | var L n => intro L' σ hσ; exact hσ n
  | pi _ _ hk ihA ihB => intro L' σ hσ; exact Lvl.pi (ihA hσ) (ihB (hup hσ)) hk
  | lam _ hk ih => intro L' σ hσ; exact Lvl.lam (ih (hup hσ)) hk
  | app _ _ hk ihf iha => intro L' σ hσ; exact Lvl.app (ihf hσ) (iha hσ) hk

/-- Substituting an object for the variable `0`. -/
theorem Lvl.inst {L : List Bool} {b a : Tm} {k : ℕ} (hb : Lvl (false :: L) b k) (ha : Lvl L a 0) :
    Lvl L (b[a]) k := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact Lvl.var L n

/-- Raw β-steps preserve the level. -/
theorem Lvl.step {t u : Tm} (hs : Step t u) : ∀ {L : List Bool} {k : ℕ}, Lvl L t k → Lvl L u k := by
  induction hs with
  | beta A b a =>
      intro L k h
      cases h with
      | app hf ha _ =>
          cases hf with
          | lam hb _ => exact hb.inst ha
  | appL a _ ih =>
      intro L k h
      cases h with
      | app hf ha hk => exact Lvl.app (ih hf) ha hk
  | appR f _ ih =>
      intro L k h
      cases h with
      | app hf ha hk => exact Lvl.app hf (ih ha) hk
  | lamL b _ _ =>
      intro L k h
      cases h with
      | lam hb hk => exact Lvl.lam hb hk
  | lamR A _ ih =>
      intro L k h
      cases h with
      | lam hb hk => exact Lvl.lam (ih hb) hk
  | piL B _ ih =>
      intro L k h
      cases h with
      | pi hA hB hk => exact Lvl.pi (ih hA) hB hk
  | piR A _ ih =>
      intro L k h
      cases h with
      | pi hA hB hk => exact Lvl.pi hA (ih hB) hk

/-- Raw η-steps preserve the level. -/
theorem Lvl.etaStep {t u : Tm} (hs : EtaStep t u) :
    ∀ {L : List Bool} {k : ℕ}, Lvl L t k → Lvl L u k := by
  induction hs with
  | eta A f =>
      intro L k h
      cases h with
      | lam hb _ =>
          cases hb with
          | app hf _ _ => exact Lvl.of_rename (L' := false :: L) (ρ := Nat.succ) (fun _ => rfl) hf
  | appL a _ ih =>
      intro L k h
      cases h with
      | app hf ha hk => exact Lvl.app (ih hf) ha hk
  | appR f _ ih =>
      intro L k h
      cases h with
      | app hf ha hk => exact Lvl.app hf (ih ha) hk
  | lamL b _ _ =>
      intro L k h
      cases h with
      | lam hb hk => exact Lvl.lam hb hk
  | lamR A _ ih =>
      intro L k h
      cases h with
      | lam hb hk => exact Lvl.lam (ih hb) hk
  | piL B _ ih =>
      intro L k h
      cases h with
      | pi hA hB hk => exact Lvl.pi (ih hA) hB hk
  | piR A _ ih =>
      intro L k h
      cases h with
      | pi hA hB hk => exact Lvl.pi hA (ih hB) hk

theorem Lvl.betaEtaRed {L : List Bool} {t u : Tm} {k : ℕ} (h : Lvl L t k) (hr : BetaEtaRed t u) :
    Lvl L u k := by
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
      rcases hs with hb | he
      · exact Lvl.step hb ih
      · exact Lvl.etaStep he ih

theorem Lvl.eraseAnn {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) :
    Lvl L (LambdaPi.eraseAnn t) k := by
  induction h with
  | star L => exact Lvl.star _
  | var L n => exact Lvl.var L n
  | pi _ _ hk ihA ihB => exact Lvl.pi ihA ihB hk
  | lam _ hk ih => exact Lvl.lam ih hk
  | app _ _ hk ihf iha => exact Lvl.app ihf iha hk

/-! ### Kinds and levels -/

/-- The syntactic shape of a kind, as a boolean. -/
def isKindShape : Tm → Bool
  | Tm.sort Srt.star => true
  | Tm.pi _ B => isKindShape B
  | _ => false

/-- A term of level `2` is a kind. -/
theorem Lvl.isKindShape_two {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) (hk : k = 2) :
    isKindShape t = true := by
  induction h with
  | star => rfl
  | var L n => have := varLvl_le L n; omega
  | pi _ _ _ _ ihB => exact ihB hk
  | lam _ hk' _ => omega
  | app _ _ hk' _ _ => omega

/-- A kind has level `2`. -/
theorem Lvl.eq_two_of_isKindShape {t : Tm} : ∀ {L : List Bool} {k : ℕ}, Lvl L t k →
    isKindShape t = true → k = 2 := by
  induction t with
  | var n => intro L k _ hs; simp [isKindShape] at hs
  | sort s =>
      intro L k h _
      cases h
      rfl
  | app f a _ _ => intro L k _ hs; simp [isKindShape] at hs
  | lam A b _ _ => intro L k _ hs; simp [isKindShape] at hs
  | pi A B _ ihB =>
      intro L k h hs
      cases h with
      | pi _ hB _ => exact ihB hB hs

theorem Lvl.isKindShape_eq {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) :
    isKindShape t = decide (k = 2) := by
  by_cases hk : k = 2
  · simp [hk, h.isKindShape_two hk]
  · simp only [hk, decide_false]
    cases hs : isKindShape t
    · rfl
    · exact absurd (h.eq_two_of_isKindShape hs) hk

/-! ### The erasure -/

/-- **The erasure of a term to a simple type**: products become arrows, abstractions and
applications are transparent, variables and sorts become the base type. -/
def er : Tm → STy
  | Tm.sort _ => STy.base
  | Tm.var _ => STy.base
  | Tm.pi A B => STy.arrow (er A) (er B)
  | Tm.lam _ b => er b
  | Tm.app f _ => er f

@[simp] theorem er_sort (s : Srt) : er (Tm.sort s) = STy.base := rfl
@[simp] theorem er_var (n : ℕ) : er (Tm.var n) = STy.base := rfl
@[simp] theorem er_pi (A B : Tm) : er (Tm.pi A B) = STy.arrow (er A) (er B) := rfl
@[simp] theorem er_lam (A b : Tm) : er (Tm.lam A b) = er b := rfl
@[simp] theorem er_app (f a : Tm) : er (Tm.app f a) = er f := rfl

@[simp] theorem er_rename (ρ : ℕ → ℕ) (t : Tm) : er (LambdaPi.rename ρ t) = er t := by
  induction t generalizing ρ with
  | var n => rfl
  | sort s => rfl
  | app f a ihf _ => simp [ihf]
  | lam A b _ ihb => simp [ihb]
  | pi A B ihA ihB => simp [ihA, ihB]

@[simp] theorem er_shift (t : Tm) : er (LambdaPi.shift t) = er t := er_rename _ t

/-- The erasure is stable under substitutions of terms of erasure `base`. -/
theorem er_subst {σ : ℕ → Tm} (hσ : ∀ n, er (σ n) = STy.base) (t : Tm) :
    er (LambdaPi.subst σ t) = er t := by
  induction t generalizing σ with
  | var n => exact hσ n
  | sort s => rfl
  | app f a ihf _ => simp [ihf hσ]
  | lam A b _ ihb =>
      have hup : ∀ n, er (up σ n) = STy.base := by
        intro n; cases n with
        | zero => rfl
        | succ n => simpa using hσ n
      simp [ihb hup]
  | pi A B ihA ihB =>
      have hup : ∀ n, er (up σ n) = STy.base := by
        intro n; cases n with
        | zero => rfl
        | succ n => simpa using hσ n
      simp [ihA hσ, ihB hup]

theorem er_inst {a : Tm} (ha : er a = STy.base) (t : Tm) : er (t[a]) = er t := by
  apply er_subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => rfl

@[simp] theorem er_eraseAnn (t : Tm) : er (LambdaPi.eraseAnn t) = er t := by
  induction t with
  | var n => rfl
  | sort s => rfl
  | app f a ihf _ => simp [ihf]
  | lam A b _ ihb => simp [ihb]
  | pi A B ihA ihB => simp [ihA, ihB]

/-- **Objects have erasure `base`.** -/
theorem er_of_lvl_zero {L : List Bool} {t : Tm} {k : ℕ} (h : Lvl L t k) (hk : k = 0) :
    er t = STy.base := by
  induction h with
  | star => omega
  | var => rfl
  | pi _ _ hk' _ _ => omega
  | lam _ _ ih => exact ih hk
  | app _ _ _ ihf _ => exact ihf hk

/-- The erasure is invariant under raw β-steps of terms with a level. -/
theorem er_step {t u : Tm} (hs : Step t u) : ∀ {L : List Bool} {k : ℕ}, Lvl L t k → er t = er u := by
  induction hs with
  | beta A b a =>
      intro L k h
      cases h with
      | app hf ha _ =>
          simp only [er_app, er_lam]
          exact (er_inst (er_of_lvl_zero ha rfl) b).symm
  | appL a _ ih =>
      intro L k h
      cases h with
      | app hf _ _ => simpa using ih hf
  | appR f _ _ => intro L k _; rfl
  | lamL b _ _ => intro L k _; rfl
  | lamR A _ ih =>
      intro L k h
      cases h with
      | lam hb _ => simpa using ih hb
  | piL B _ ih =>
      intro L k h
      cases h with
      | pi hA _ _ => simp [ih hA]
  | piR A _ ih =>
      intro L k h
      cases h with
      | pi _ hB _ => simp [ih hB]

/-- The erasure is invariant under raw η-steps. -/
theorem er_etaStep {t u : Tm} (hs : EtaStep t u) : er t = er u := by
  induction hs with
  | eta A f => simp
  | appL a _ ih => simp [ih]
  | appR f _ _ => rfl
  | lamL b _ _ => rfl
  | lamR A _ ih => simp [ih]
  | piL B _ ih => simp [ih]
  | piR A _ ih => simp [ih]

theorem er_betaEtaRed {L : List Bool} {t u : Tm} {k : ℕ} (h : Lvl L t k) (hr : BetaEtaRed t u) :
    er t = er u := by
  induction hr with
  | refl => rfl
  | tail hr' hs ih =>
      have hl := h.betaEtaRed hr'
      rcases hs with hb | he
      · exact ih.trans (er_step hb hl)
      · exact ih.trans (er_etaStep he)

/-- **Two βη-convertible terms with levels have the same level and the same erasure.** -/
theorem Lvl.betaEtaConv {L : List Bool} {t u : Tm} {k k' : ℕ} (ht : Lvl L t k) (hu : Lvl L u k')
    (h : BetaEtaConv t u) : k = k' ∧ er t = er u := by
  obtain ⟨w, hw₁, hw₂⟩ := betaEtaConv_iff_join.mp h
  have h₁ := ht.eraseAnn.betaEtaRed hw₁
  have h₂ := hu.eraseAnn.betaEtaRed hw₂
  refine ⟨h₁.det h₂, ?_⟩
  rw [← er_eraseAnn t, ← er_eraseAnn u, er_betaEtaRed ht.eraseAnn hw₁,
    er_betaEtaRed hu.eraseAnn hw₂]

/-- A term with a level is not βη-convertible to the top sort. -/
theorem Lvl.not_conv_box {L : List Bool} {u : Tm} {k : ℕ} (hu : Lvl L u k)
    (h : BetaEtaConv (sort Srt.box) u) : False := by
  obtain ⟨w, hw₁, hw₂⟩ := betaEtaConv_iff_join.mp h
  rw [eraseAnn_sort] at hw₁
  have hw := betaEtaRed_sort_inv hw₁
  subst hw
  exact (hu.eraseAnn.betaEtaRed hw₂).not_box

/-! ### Typable terms have levels -/

/-- The levels of the entries of a context. -/
def lvlCtx : Ctx → List Bool
  | [] => []
  | A :: Γ => isKindShape A :: lvlCtx Γ

@[simp] theorem lvlCtx_nil : lvlCtx [] = [] := rfl
@[simp] theorem lvlCtx_cons (A : Tm) (Γ : Ctx) : lvlCtx (A :: Γ) = isKindShape A :: lvlCtx Γ := rfl

/-- The type `A` of a term of level `k`: the top sort for a kind, a term of level `k + 1`
otherwise. -/
def TyLvl (L : List Bool) (A : Tm) (k : ℕ) : Prop :=
  (A = Tm.sort Srt.box ∧ k = 2) ∨ (k ≤ 1 ∧ Lvl L A (k + 1))

theorem TyLvl.shift {L : List Bool} {A : Tm} {k : ℕ} (h : TyLvl L A k) (b : Bool) :
    TyLvl (b :: L) (LambdaPi.shift A) k := by
  rcases h with ⟨rfl, hk⟩ | ⟨hk, hA⟩
  · exact Or.inl ⟨rfl, hk⟩
  · exact Or.inr ⟨hk, hA.shift b⟩

/-- The declared types of a context have the levels the context records. -/
def CtxLvl (Γ : Ctx) : Prop :=
  ∀ n A, Lookup Γ n A → TyLvl (lvlCtx Γ) A (varLvl (lvlCtx Γ) n)

theorem CtxLvl.nil : CtxLvl [] := fun _ _ h => by cases h

theorem CtxLvl.cons {Γ : Ctx} (h : CtxLvl Γ) {A : Tm} {j : ℕ} (hA : Lvl (lvlCtx Γ) A j)
    (hj : j = 1 ∨ j = 2) : CtxLvl (A :: Γ) := by
  intro n B hB
  cases hB with
  | zero =>
      rw [lvlCtx_cons, varLvl_cons_zero, hA.isKindShape_eq]
      rcases hj with rfl | rfl
      · have h0 : TyLvl (false :: lvlCtx Γ) (LambdaPi.shift A) 0 :=
          Or.inr ⟨by norm_num, hA.shift _⟩
        simpa using h0
      · have h1 : TyLvl (true :: lvlCtx Γ) (LambdaPi.shift A) 1 := Or.inr ⟨le_rfl, hA.shift _⟩
        simpa using h1
  | @succ Γ' n' A' B' hB' =>
      rw [lvlCtx_cons, varLvl_cons_succ]
      exact (h _ _ hB').shift _

/-- A context of levels where every declaration is an object. -/
theorem lvlCtx_cons_type {Γ : Ctx} {A : Tm} (hA : Lvl (lvlCtx Γ) A 1) :
    lvlCtx (A :: Γ) = false :: lvlCtx Γ := by
  rw [lvlCtx_cons, hA.isKindShape_eq]
  rfl

theorem TyLvl.sort_star {L : List Bool} {k : ℕ} (h : TyLvl L (sort Srt.star) k) : k = 1 := by
  rcases h with ⟨he, _⟩ | ⟨_, h⟩
  · exact absurd he (by simp)
  · have := h.det (Lvl.star L); omega

theorem TyLvl.sort_box {L : List Bool} {k : ℕ} (h : TyLvl L (sort Srt.box) k) : k = 2 := by
  rcases h with ⟨_, hk⟩ | ⟨_, h⟩
  · exact hk
  · exact h.not_box.elim

theorem TyLvl.sort {L : List Bool} {s : Srt} {k : ℕ} (h : TyLvl L (sort s) k) : k = 1 ∨ k = 2 := by
  cases s with
  | star => exact Or.inl h.sort_star
  | box => exact Or.inr h.sort_box

/-- **A typable term has a level**, one below the level of its type. -/
theorem TypingE.lvl {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) :
    CtxLvl Γ → ∃ k, Lvl (lvlCtx Γ) t k ∧ TyLvl (lvlCtx Γ) A k := by
  induction h with
  | ax Γ => intro _; exact ⟨2, Lvl.star _, Or.inl ⟨rfl, rfl⟩⟩
  | @var Γ n A hA => intro hctx; exact ⟨_, Lvl.var _ n, hctx _ _ hA⟩
  | @pi Γ A B s t hr _ _ ihA ihB =>
      intro hctx
      cases hr
      obtain ⟨kA, hlA, htA⟩ := ihA hctx
      have hkA := htA.sort_star
      subst hkA
      have hctx' := hctx.cons hlA (Or.inl rfl)
      obtain ⟨kB, hlB, htB⟩ := ihB hctx'
      rw [lvlCtx_cons_type hlA] at hlB htB
      cases t with
      | star =>
          have hkB := htB.sort_star
          subst hkB
          exact ⟨1, Lvl.pi hlA hlB le_rfl, Or.inr ⟨le_rfl, Lvl.star _⟩⟩
      | box =>
          have hkB := htB.sort_box
          subst hkB
          exact ⟨2, Lvl.pi hlA hlB (by norm_num), Or.inl ⟨rfl, rfl⟩⟩
  | @lam Γ A B b s _ _ ihP ihb =>
      intro hctx
      obtain ⟨kP, hlP, _⟩ := ihP hctx
      cases hlP with
      | pi hlA hlB hkP =>
          have hctx' := hctx.cons hlA (Or.inl rfl)
          obtain ⟨kb, hlb, htb⟩ := ihb hctx'
          rw [lvlCtx_cons_type hlA] at hlb htb
          rcases htb with ⟨rfl, _⟩ | ⟨hkb, hlB'⟩
          · exact hlB.not_box.elim
          · have he := hlB.det hlB'
            subst he
            exact ⟨kb, Lvl.lam hlb hkb, Or.inr ⟨hkb, Lvl.pi hlA hlB hkP⟩⟩
  | @app Γ f a A B _ _ ihf iha =>
      intro hctx
      obtain ⟨kf, hlf, htf⟩ := ihf hctx
      rcases htf with ⟨he, _⟩ | ⟨hkf, hlP⟩
      · exact absurd he (by simp)
      · cases hlP with
        | pi hlA hlB _ =>
            obtain ⟨ka, hla, hta⟩ := iha hctx
            rcases hta with ⟨rfl, _⟩ | ⟨_, hlA'⟩
            · exact hlA.not_box.elim
            · have he := hlA.det hlA'
              have hka : ka = 0 := by omega
              subst hka
              exact ⟨kf, Lvl.app hlf hla hkf, Or.inr ⟨hkf, hlB.inst hla⟩⟩
  | @conv Γ t A B s _ hB hc iht ihB =>
      intro hctx
      obtain ⟨k, hlt, htA⟩ := iht hctx
      obtain ⟨kB, hlB, htB⟩ := ihB hctx
      rcases htA with ⟨rfl, _⟩ | ⟨hk, hlA⟩
      · exact (hlB.not_conv_box hc).elim
      · have he := (hlA.betaEtaConv hlB hc).1
        subst he
        exact ⟨k, hlt, Or.inr ⟨hk, hlB⟩⟩

/-- **Every well-formed context records the levels of its declarations.** -/
theorem WfE.ctxLvl {Γ : Ctx} (h : WfE Γ) : CtxLvl Γ := by
  induction h with
  | nil => exact CtxLvl.nil
  | cons _ hA ih =>
      obtain ⟨k, hl, ht⟩ := hA.lvl ih
      exact ih.cons hl ht.sort

theorem TypingE.lvl' {Γ : Ctx} {t A : Tm} (h : TypingE Γ t A) (hΓ : WfE Γ) :
    ∃ k, Lvl (lvlCtx Γ) t k ∧ TyLvl (lvlCtx Γ) A k :=
  h.lvl hΓ.ctxLvl

/-- A term typable by `∗` has level `1`, by `□` level `2`. -/
theorem TypingE.lvl_star {Γ : Ctx} {A : Tm} (h : TypingE Γ A (sort Srt.star)) (hΓ : WfE Γ) :
    Lvl (lvlCtx Γ) A 1 := by
  obtain ⟨k, hl, ht⟩ := h.lvl' hΓ
  have := ht.sort_star
  subst this
  exact hl

theorem TypingE.lvl_sort {Γ : Ctx} {A : Tm} {s : Srt} (h : TypingE Γ A (sort s)) (hΓ : WfE Γ) :
    ∃ k, Lvl (lvlCtx Γ) A k ∧ (k = 1 ∨ k = 2) := by
  obtain ⟨k, hl, ht⟩ := h.lvl' hΓ
  exact ⟨k, hl, ht.sort⟩

/-- **An object has erasure `base`.** -/
theorem TypingE.er_object {Γ : Ctx} {a A : Tm} (h : TypingE Γ a A)
    (hA : TypingE Γ A (sort Srt.star)) (hΓ : WfE Γ) : er a = STy.base := by
  obtain ⟨k, hl, ht⟩ := h.lvl' hΓ
  have hA1 := hA.lvl_star hΓ
  rcases ht with ⟨rfl, _⟩ | ⟨_, hA'⟩
  · exact (not_typingE_box hA).elim
  · have := hA1.det hA'
    exact er_of_lvl_zero hl (by omega)

/-- **Two βη-convertible types (or kinds) have the same erasure and the same sort.** -/
theorem TypingE.er_conv {Γ : Ctx} {A B : Tm} {s s' : Srt} (hA : TypingE Γ A (sort s))
    (hB : TypingE Γ B (sort s')) (h : BetaEtaConv A B) (hΓ : WfE Γ) : er A = er B ∧ s = s' := by
  obtain ⟨k, hlA, htA⟩ := hA.lvl' hΓ
  obtain ⟨k', hlB, htB⟩ := hB.lvl' hΓ
  obtain ⟨hk, her⟩ := hlA.betaEtaConv hlB h
  refine ⟨her, ?_⟩
  subst hk
  cases s <;> cases s'
  · rfl
  · have := htA.sort_star; have := htB.sort_box; omega
  · have := htA.sort_box; have := htB.sort_star; omega
  · rfl

end LambdaPi
