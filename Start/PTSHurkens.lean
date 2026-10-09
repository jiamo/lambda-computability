import Start.PTSCheck
import Start.PTSCube

/-!
# Hurkens' paradox in System U⁻

This module is this library's own (task `M23-HURKENS`).  It is an **object-theory**
inconsistency theorem about a pure type system of the absorbed framework
(`Start/PTSBasic.lean`); nothing here proves `False` in Lean.

* `PureTypeSystem.Hurkens.USort`, `uMinus` — System U⁻: sorts `∗, □, △`, axioms `∗ : □`,
  `□ : △`, product rules `(∗,∗)`, `(□,∗)`, `(□,□)`, `(△,□)` (all with target the second sort).
* `PureTypeSystem.Hurkens.hurkens` — Hurkens' term (A. J. C. Hurkens, "A simplification of
  Girard's paradox", TLCA 1995), written with named binders and compiled to de Bruijn syntax.
* `PureTypeSystem.Hurkens.hurkens_typed` — **`⊢ hurkens : ΠA:∗. A` in System U⁻**, certified by
  the verified inference procedure of `Start/PTSCheck.lean`; the target type is not assumed.
* Consequences: every well-formed closed type is inhabited (`uMinus_inconsistent`); there is no
  closed *normal* term of type `ΠA:∗. A` in **any** pure type system (`no_normal_closed_bot`);
  hence Hurkens' term has no normal form (`hurkens_not_weaklyNormalizing`) and System U⁻ is
  neither weakly nor strongly normalizing (`uMinus_not_wn`, `uMinus_not_sn`).
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace Hurkens

/-- The sorts of System U⁻. -/
inductive USort where
  | star
  | box
  | tri
  deriving DecidableEq, Repr

/-- Axioms of U⁻ as a partial function: `∗ : □`, `□ : △`. -/
def uAx : USort → Option USort
  | .star => some .box
  | .box => some .tri
  | .tri => none

/-- Product rules of U⁻ as a partial function: `(∗,∗)`, `(□,∗)`, `(□,□)`, `(△,□)`. -/
def uRl : USort → USort → Option USort
  | .star, .star => some .star
  | .box, .star => some .star
  | .box, .box => some .box
  | .tri, .box => some .box
  | _, _ => none

/-- **System U⁻.** -/
def uMinus : Specification USort where
  axioms s t := (s = .star ∧ t = .box) ∨ (s = .box ∧ t = .tri)
  rule s₁ s₂ s₃ := s₃ = s₂ ∧
    ((s₁ = .star ∧ s₂ = .star) ∨ (s₁ = .box ∧ s₂ = .star) ∨ (s₁ = .box ∧ s₂ = .box) ∨
      (s₁ = .tri ∧ s₂ = .box))

theorem uAx_sound : ∀ s t, uAx s = some t → uMinus.axioms s t := by
  intro s t h; cases s <;> simp_all [uAx, uMinus]

theorem uRl_sound : ∀ s₁ s₂ s₃, uRl s₁ s₂ = some s₃ → uMinus.rule s₁ s₂ s₃ := by
  intro s₁ s₂ s₃ h; cases s₁ <;> cases s₂ <;> simp_all [uRl, uMinus]

/-! ### Named syntax -/

/-- Terms with named binders, compiled to de Bruijn syntax by `Nm.toExpr`. -/
inductive Nm where
  | v (x : String)
  | s (σ : USort)
  | ap (f a : Nm)
  | lm (x : String) (A b : Nm)
  | pi (x : String) (A B : Nm)

/-- Compilation to de Bruijn indices (`ctx` lists the bound names, innermost first). -/
def Nm.toExpr (ctx : List String) : Nm → Expr USort
  | .v x => .var (ctx.idxOf x)
  | .s σ => .sort σ
  | .ap f a => .app (f.toExpr ctx) (a.toExpr ctx)
  | .lm x A b => .lam (A.toExpr ctx) (b.toExpr (x :: ctx))
  | .pi x A B => .pi (A.toExpr ctx) (B.toExpr (x :: ctx))

open Nm

/-- Non-dependent product (the bound name `_` is never referenced). -/
def arr (A B : Nm) : Nm := pi "_" A B
def star : Nm := s .star
def box : Nm := s .box
def ap2 (f a b : Nm) : Nm := ap (ap f a) b
def ap3 (f a b c : Nm) : Nm := ap (ap (ap f a) b) c

/-- `⊥ := ΠA:∗. A`. -/
def bot : Nm := pi "A" star (v "A")
/-- `¬φ := φ → ⊥`. -/
def neg (φ : Nm) : Nm := arr φ bot
/-- `℘S := S → ∗`. -/
def pow (S : Nm) : Nm := arr S star
/-- `U := ΠX:□. ((℘℘X → X) → ℘℘X)`. -/
def U : Nm := pi "X" box (arr (arr (pow (pow (v "X"))) (v "X")) (pow (pow (v "X"))))
/-- `τ := λt:℘℘U. λX:□. λf:℘℘X → X. λp:℘X. t (λx:U. p (f (x X f)))`. -/
def tau : Nm :=
  lm "t" (pow (pow U)) (lm "X" box (lm "f" (arr (pow (pow (v "X"))) (v "X"))
    (lm "p" (pow (v "X"))
      (ap (v "t") (lm "x" U (ap (v "p") (ap (v "f") (ap2 (v "x") (v "X") (v "f")))))))))
/-- `σ := λs:U. s U (λt:℘℘U. τ t)`. -/
def sigma : Nm := lm "s" U (ap2 (v "s") U (lm "t" (pow (pow U)) (ap tau (v "t"))))
/-- `τσ x`. -/
def ts (x : Nm) : Nm := ap tau (ap sigma x)
/-- `Δ := λy:U. ¬(Πp:℘U. σ y p → p (τσ y))`. -/
def Delta : Nm :=
  lm "y" U (neg (pi "p" (pow U) (arr (ap2 sigma (v "y") (v "p")) (ap (v "p") (ts (v "y"))))))
/-- `Ω := τ (λp:℘U. Πx:U. σ x p → p x)`. -/
def Omega : Nm :=
  ap tau (lm "p" (pow U) (pi "x" U (arr (ap2 sigma (v "x") (v "p")) (ap (v "p") (v "x")))))

/-- `Πp:℘U. (Πx:U. σ x p → p x) → p Ω`. -/
def lemTy : Nm :=
  pi "p" (pow U) (arr (pi "x" U (arr (ap2 sigma (v "x") (v "p")) (ap (v "p") (v "x"))))
    (ap (v "p") Omega))

/-- `λp:℘U. λh:(Πx:U. σ x p → p x). h Ω (λx:U. h (τσ x))`. -/
def lem : Nm :=
  lm "p" (pow U) (lm "h" (pi "x" U (arr (ap2 sigma (v "x") (v "p")) (ap (v "p") (v "x"))))
    (ap2 (v "h") Omega (lm "x" U (ap (v "h") (ts (v "x"))))))

/-- The body using the lemma `k : lemTy`. -/
def body : Nm :=
  ap (ap2 (v "k") Delta
      (lm "x" U (lm "h2" (ap2 sigma (v "x") Delta)
        (lm "h3" (pi "p" (pow U) (arr (ap2 sigma (v "x") (v "p")) (ap (v "p") (ts (v "x")))))
          (ap (ap2 (v "h3") Delta (v "h2"))
            (lm "p" (pow U) (ap (v "h3") (lm "y" U (ap (v "p") (ts (v "y")))))))))))
    (lm "p" (pow U) (ap (v "k") (lm "y" U (ap (v "p") (ts (v "y"))))))

/-- **Hurkens' term**, in named form. -/
def hurkensNm : Nm := ap (lm "k" lemTy body) lem

/-- **Hurkens' term** in the de Bruijn syntax of the framework. -/
def hurkens : Expr USort := hurkensNm.toExpr []

/-- The internal falsity `ΠA:∗. A`. -/
def botE : Expr USort := .pi (.sort .star) (.var 0)

end Hurkens

end PureTypeSystem

namespace PureTypeSystem

/-! ### No closed normal proof of falsity, in any pure type system -/

section NoNormal

universe u

variable {S : Type u} {P : Specification S}

theorem not_converts_var_sort {n : ℕ} {s : S} : ¬ Converts (Expr.var n) (.sort s) := by
  intro h
  cases Normal.eq_of_converts (Normal.var n) (Normal.sort s) h

theorem not_converts_pi_var {A B : Expr S} {n : ℕ} : ¬ Converts (.pi A B) (.var n) := by
  intro h
  obtain ⟨K, hK, hK'⟩ := h.join
  obtain ⟨A', B', rfl, -, -⟩ := hK.pi_inv
  cases (Normal.var n).reduces_eq hK'

theorem neutral_nil_untyped {M T : Expr S} (hn : Neutral M) (h : HasType P ([]) M T) : False := by
  induction hn generalizing T with
  | var n =>
      obtain ⟨A, hA, -⟩ := h.generation
      cases hA
  | app _ ih =>
      obtain ⟨D, E, hf, -, -⟩ := h.generation_app
      exact ih hf

theorem neutral_single_sort {M T : Expr S} {s : S} (hn : Neutral M)
    (h : HasType P ([.sort s]) M T) : Converts T (.sort s) := by
  induction hn generalizing T with
  | var n =>
      obtain ⟨A, hA, hc⟩ := h.generation
      cases hA with
      | zero => exact hc
      | succ _ hA => cases hA
  | app _ ih =>
      obtain ⟨D, E, hf, -, -⟩ := h.generation_app
      exact absurd (ih hf) Converts.pi_not_sort

/-- **In every pure type system there is no closed normal term of type `ΠA:s. A`.** -/
theorem no_normal_closed_bot {N : Expr S} {s : S}
    (h : HasType P ([]) N (.pi (.sort s) (.var 0))) (hn : Normal N) : False := by
  obtain ⟨_, hT⟩ | ⟨u, hT⟩ := h.regularity
  · cases hT
  obtain ⟨s₁, -, -, hss, -, -, -⟩ := hT.generation_pi
  obtain ⟨t, rfl⟩ | hne | ⟨A, B, rfl⟩ | ⟨A, b, rfl⟩ := h.normal_shape hn
  · obtain ⟨_, -, hc⟩ := h.generation
    exact Converts.pi_not_sort hc
  · exact neutral_nil_untyped hne h
  · obtain ⟨_, _, _, -, -, -, hc⟩ := h.generation_pi
    exact Converts.pi_not_sort hc
  · obtain ⟨B, r, hb, hPi, hc⟩ := h.generation_lam
    obtain ⟨hcA, hcB⟩ := hc.product_compatibility
    obtain ⟨r', hA⟩ := hPi.product_domain _ _ rfl
    have hb' := hb.context_head_conversion hA hss (.symm _ _ hcA)
    have hv : HasType P ([.sort s]) (.var 0) (.sort s) := by
      simpa only [Expr.rename] using HasType.var hss
    have hb'' : HasType P ([.sort s]) b (.var 0) := .conversion hb' hv (.symm _ _ hcB)
    obtain ⟨t, rfl⟩ | hne | ⟨A', B', rfl⟩ | ⟨A', b', rfl⟩ := hb''.normal_shape hn.lam_body
    · obtain ⟨_, -, hc⟩ := hb''.generation
      exact not_converts_var_sort hc
    · exact not_converts_var_sort (neutral_single_sort hne hb'')
    · obtain ⟨_, _, _, -, -, -, hc⟩ := hb''.generation_pi
      exact not_converts_var_sort hc
    · obtain ⟨_, _, -, -, hc⟩ := hb''.generation_lam
      exact not_converts_pi_var (.symm _ _ hc)

/-- A system with a closed proof of `ΠA:s. A` is not weakly normalizing. -/
theorem not_wn_of_closed_bot {M : Expr S} {s : S}
    (h : HasType P ([]) M (.pi (.sort s) (.var 0))) : ¬ WeaklyNormalizing M := by
  rintro ⟨N, hr, hn⟩
  exact no_normal_closed_bot (h.subject_reduces hr) hn

end NoNormal

namespace Hurkens

set_option maxRecDepth 100000 in
/-- **Hurkens' paradox**: `⊢ hurkens : ΠA:∗. A` in System U⁻.  The derivation is certified by the
verified inference procedure `Check.infer` (soundness: `Check.infer_sound`); the kernel evaluates
the inference. -/
theorem hurkens_typed : HasType uMinus ([]) hurkens botE :=
  Check.infer_sound uAx_sound uRl_sound 2000 200 .nil (by decide +kernel)

/-- **System U⁻ is inconsistent**: every closed type of sort `∗` is inhabited by a closed term. -/
theorem uMinus_inconsistent {T : Expr USort} (hT : HasType uMinus ([]) T (.sort .star)) :
    HasType uMinus ([]) (.app hurkens T) T :=
  HasType.application hurkens_typed hT

/-- Hurkens' term has no normal form. -/
theorem hurkens_not_weaklyNormalizing : ¬ WeaklyNormalizing hurkens :=
  not_wn_of_closed_bot hurkens_typed

/-- **System U⁻ is not weakly normalizing.** -/
theorem uMinus_not_wn : ¬ SystemWeaklyNormalizing uMinus := fun h =>
  hurkens_not_weaklyNormalizing (h ([]) .nil hurkens ⟨botE, .inl hurkens_typed⟩)

/-- **System U⁻ is not strongly normalizing.** -/
theorem uMinus_not_sn : ¬ SystemStronglyNormalizing uMinus := fun h =>
  hurkens_not_weaklyNormalizing
    (weaklyNormalizing_of_stronglyNormalizing (h ([]) .nil hurkens ⟨botE, .inl hurkens_typed⟩))

end Hurkens

end PureTypeSystem
