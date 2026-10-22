import Start.TLCA4BetaEta

/-!
# TLCA open problem 4 under βη: polynomials in `B`, `M`, `I` (row M20-TLCA4-POLYNOMIAL)

Statman's valid first step (as reported in the introduction of Imamura's paper): a fixed-point
combinator built from `B` and `M` is βη-equivalent to a *polynomial*, a composition
`m₁ ∘ … ∘ m_k` (with `t ∘ u := B t u`) of monomials `Bⁿ B`, `Bⁿ M`, `Bⁿ I`.

* `Mono`, `Mono.tm`, `polyTm` — monomials and polynomials as combinatory terms
  (`polyTm m [m₂, …, m_k] = m ∘ (m₂ ∘ (… ∘ m_k))`), `polyTm_isBMI`;
* **`polyTm_action`** — `(m₁ ∘ … ∘ m_k) x` is weakly (hence βη-) equal to `m₁ (… (m_k x))`;
* **`bpow_action`** — `Bⁿ f g z₁ … zₙ` is weakly equal to `f (g z₁ … zₙ)`;
  `bpowI_action` — `Bⁿ I` acts as the identity on `n + 1` arguments;
* `statmanT_eq` — Imamura's counterexample `T = B M (B (B M) B)` is the polynomial
  `M ∘ ((B M) ∘ B)`;
* `PolyFiveOne` (Problem 5.1 for polynomials), `problemFiveOne_of_poly`, and the reduction
  **`problemFiveOne_iff_poly`** of Problem 5.1 to polynomials, conditional on Statman's step
  `StatmanStepOne`, which is stated (as a `Prop`) and **not** proved here.
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- `bpow n X = B (B (… (B X)))` with `n` copies of `B`. -/
def bpow : ℕ → Tm → Tm
  | 0, X => X
  | n + 1, X => app B (bpow n X)

/-- The three monomial bases. -/
inductive Base where
  | B : Base
  | M : Base
  | I : Base
  deriving DecidableEq, Repr

def Base.tm : Base → Tm
  | .B => Tm.B
  | .M => Tm.M
  | .I => Tm.I

/-- A monomial `Bⁿ X` with `X ∈ {B, M, I}`. -/
structure Mono where
  n : ℕ
  base : Base
  deriving DecidableEq, Repr

def Mono.tm (m : Mono) : Tm := bpow m.n m.base.tm

/-- Composition `t ∘ u := B t u`. -/
def comp (t u : Tm) : Tm := app (app B t) u

/-- The polynomial `m ∘ (m₂ ∘ (… ∘ m_k))` for the nonempty list `m :: [m₂, …, m_k]`. -/
def polyTm : Mono → List Mono → Tm
  | m, [] => m.tm
  | m, m' :: ps => comp m.tm (polyTm m' ps)

/-- The λ-action `m₁ (m₂ (… (m_k x)))`. -/
def actList : List Mono → Tm → Tm
  | [], x => x
  | m :: ps, x => app m.tm (actList ps x)

/-- Iterated application `f z₁ … zₙ`. -/
def apps : Tm → List Tm → Tm
  | f, [] => f
  | f, z :: zs => apps (app f z) zs

/-! ### Congruence of weak equivalence -/

theorem Tm.WEq.appL {u u' : Tm} (h : WEq u u') (v : Tm) : WEq (app u v) (app u' v) := by
  induction h with
  | step hs => exact .step (.appL v hs)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Tm.WEq.appR (u : Tm) {v v' : Tm} (h : WEq v v') : WEq (app u v) (app u v') := by
  induction h with
  | step hs => exact .step (.appR u hs)
  | refl => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem Tm.WEq.apps {u u' : Tm} (h : WEq u u') (zs : List Tm) : WEq (apps u zs) (apps u' zs) := by
  induction zs generalizing u u' with
  | nil => exact h
  | cons z zs ih => exact ih (h.appL z)

/-! ### Closedness -/

theorem bpow_isBMI {X : Tm} (hX : IsBMI X) : ∀ n, IsBMI (bpow n X)
  | 0 => hX
  | n + 1 => .app .B (bpow_isBMI hX n)

theorem Base.tm_isBMI : ∀ b : Base, IsBMI b.tm
  | .B => .B
  | .M => .M
  | .I => .I

theorem Mono.tm_isBMI (m : Mono) : IsBMI m.tm := bpow_isBMI m.base.tm_isBMI m.n

theorem polyTm_isBMI : ∀ (m : Mono) (ps : List Mono), IsBMI (polyTm m ps)
  | m, [] => m.tm_isBMI
  | m, m' :: ps => .app (.app .B m.tm_isBMI) (polyTm_isBMI m' ps)

/-! ### The λ-action of polynomials and monomials -/

/-- `(t ∘ u) x = t (u x)`. -/
theorem comp_action (t u x : Tm) : WEq (app (comp t u) x) (app t (app u x)) :=
  .step (.b t u x)

/-- **The action of a polynomial**: `(m₁ ∘ … ∘ m_k) x = m₁ (… (m_k x))`. -/
theorem polyTm_action : ∀ (m : Mono) (ps : List Mono) (x : Tm),
    WEq (app (polyTm m ps) x) (actList (m :: ps) x)
  | _, [], _ => .refl _
  | _, m' :: ps, x =>
      (comp_action _ _ x).trans (WEq.appR _ (polyTm_action m' ps x))

/-- **The action of `Bⁿ f`**: `Bⁿ f g z₁ … zₙ = f (g z₁ … zₙ)`. -/
theorem bpow_action (f : Tm) : ∀ (n : ℕ) (g : Tm) (zs : List Tm), zs.length = n →
    WEq (apps (app (bpow n f) g) zs) (app f (apps g zs))
  | 0, g, [], _ => .refl _
  | n + 1, g, z :: zs, hl => by
      have h1 : WEq (app (app (bpow (n + 1) f) g) z) (app (bpow n f) (app g z)) :=
        .step (.b _ _ _)
      exact (WEq.apps h1 zs).trans (bpow_action f n (app g z) zs (by simpa using hl))

/-- **`Bⁿ I` is the identity** on `n + 1` arguments: `Bⁿ I g z₁ … zₙ = g z₁ … zₙ`. -/
theorem bpowI_action (n : ℕ) (g : Tm) (zs : List Tm) (hl : zs.length = n) :
    WEq (apps (app (bpow n I) g) zs) (apps g zs) :=
  (bpow_action I n g zs hl).trans (.step (.i _))

/-- The βη-form of `polyTm_action`. -/
theorem polyTm_action_betaEta (m : Mono) (ps : List Mono) (x : Tm) :
    Lambda.betaEtaConv (toLam (app (polyTm m ps) x)) (toLam (actList (m :: ps) x)) :=
  toLam_weq (polyTm_action m ps x)

/-- The βη-form of `bpow_action`. -/
theorem bpow_action_betaEta (f : Tm) (n : ℕ) (g : Tm) (zs : List Tm) (hl : zs.length = n) :
    Lambda.betaEtaConv (toLam (apps (app (bpow n f) g) zs)) (toLam (app f (apps g zs))) :=
  toLam_weq (bpow_action f n g zs hl)

/-- Imamura's counterexample to Statman's second step, `T = B M (B (B M) B)`, is the polynomial
`M ∘ ((B M) ∘ B)`. -/
theorem statmanT_eq :
    polyTm ⟨0, .M⟩ [⟨1, .M⟩, ⟨0, .B⟩] = app (app B M) (app (app B (app B M)) B) := rfl

/-! ### The polynomial algebra (extensional laws, Series V round 2 part B2) -/

theorem apps_append (f : Tm) (zs ws : List Tm) : apps f (zs ++ ws) = apps (apps f zs) ws := by
  induction zs generalizing f with
  | nil => rfl
  | cons z zs ih => exact ih (app f z)

/-- `Bⁿ M` duplicates at depth `n`: `Bⁿ M g z₁ … zₙ = (g z₁ … zₙ) (g z₁ … zₙ)`. -/
theorem bpowM_action (n : ℕ) (g : Tm) (zs : List Tm) (hl : zs.length = n) :
    WEq (apps (app (bpow n M) g) zs) (app (apps g zs) (apps g zs)) :=
  (bpow_action M n g zs hl).trans (.step (.m _))

/-- `Bⁿ B` composes the arguments `n + 1` and `n + 2`:
`Bⁿ B h z₁ … zₙ a b w⃗ = h z₁ … zₙ (a b) w⃗`. -/
theorem bpowB_action (n : ℕ) (h : Tm) (zs : List Tm) (hl : zs.length = n) (a b : Tm)
    (ws : List Tm) :
    WEq (apps (app (bpow n B) h) (zs ++ a :: b :: ws)) (apps h (zs ++ app a b :: ws)) := by
  rw [apps_append, apps_append]
  have h1 := WEq.apps (bpow_action B n h zs hl) (a :: b :: ws)
  refine h1.trans ?_
  exact WEq.apps (.step (.b _ _ _)) ws

/-- `(t ∘ u) g = t (u g)` under further arguments. -/
theorem comp_action_apps (t u g : Tm) (zs : List Tm) :
    WEq (apps (app (comp t u) g) zs) (apps (app t (app u g)) zs) :=
  WEq.apps (comp_action t u g) zs

/-- **Commutation law**: for `k ≥ n + 1`, `(Bⁿ B) ∘ (Bᵏ X)` and `(Bᵏ⁺¹ X) ∘ (Bⁿ B)` act
identically on `k + 1` arguments after `g`
(both give `X (g z₁ … zₙ (a b) w₁ … w_{k-n-1})`). -/
theorem comm_bpowB (n k : ℕ) (X g : Tm) (zs : List Tm) (hl : zs.length = n) (a b : Tm)
    (ws : List Tm) (hw : n + 1 + ws.length = k) :
    WEq (apps (app (comp (bpow n B) (bpow k X)) g) (zs ++ a :: b :: ws))
      (apps (app (comp (bpow (k + 1) X) (bpow n B)) g) (zs ++ a :: b :: ws)) := by
  have hL : WEq (apps (app (comp (bpow n B) (bpow k X)) g) (zs ++ a :: b :: ws))
      (app X (apps g (zs ++ app a b :: ws))) := by
    refine (comp_action_apps _ _ _ _).trans ((bpowB_action n _ zs hl a b ws).trans ?_)
    exact bpow_action X k g _ (by simp; omega)
  have hR : WEq (apps (app (comp (bpow (k + 1) X) (bpow n B)) g) (zs ++ a :: b :: ws))
      (app X (apps g (zs ++ app a b :: ws))) := by
    refine (comp_action_apps _ _ _ _).trans ((bpow_action X (k + 1) _ _ (by simp; omega)).trans ?_)
    exact WEq.appR X (bpowB_action n g zs hl a b ws)
  exact hL.trans hR.symm

/-- `I` is a two-sided unit for `∘` (acting on one argument). -/
theorem comp_I_left (t x : Tm) : WEq (app (comp I t) x) (app t x) :=
  (comp_action I t x).trans (.step (.i _))

theorem comp_I_right (t x : Tm) : WEq (app (comp t I) x) (app t x) :=
  (comp_action t I x).trans (WEq.appR t (.step (.i _)))

/-- `∘` is associative (acting on one argument). -/
theorem comp_assoc (t u v x : Tm) :
    WEq (app (comp (comp t u) v) x) (app (comp t (comp u v)) x) := by
  have h1 : WEq (app (comp (comp t u) v) x) (app t (app u (app v x))) :=
    (comp_action _ v x).trans (comp_action t u _)
  have h2 : WEq (app (comp t (comp u v)) x) (app t (app u (app v x))) :=
    (comp_action t _ x).trans (WEq.appR t (comp_action u v x))
  exact h1.trans h2.symm

/-! ### Reduction of Problem 5.1 to polynomials -/

theorem betaEtaStep_app_left {t t' : Lambda} (h : Lambda.betaEtaStep t t') (a : Lambda) :
    Lambda.betaEtaStep (.app t a) (.app t' a) := by
  cases h with
  | beta h => exact .beta (Lambda.step.app_left _ _ _ h)
  | eta h => exact .eta (Lambda.etaStep.app_left _ h)

theorem betaEtaStep_app_right (f : Lambda) {a a' : Lambda} (h : Lambda.betaEtaStep a a') :
    Lambda.betaEtaStep (.app f a) (.app f a') := by
  cases h with
  | beta h => exact .beta (Lambda.step.app_right _ _ _ h)
  | eta h => exact .eta (Lambda.etaStep.app_right _ h)

theorem betaEtaConv_app_left {t t' : Lambda} (h : Lambda.betaEtaConv t t') (a : Lambda) :
    Lambda.betaEtaConv (.app t a) (.app t' a) := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih => exact .step ih (betaEtaStep_app_left hs a)
  | symm_step _ hs ih => exact .symm_step ih (betaEtaStep_app_left hs a)

theorem betaEtaConv_app_right (f : Lambda) {a a' : Lambda} (h : Lambda.betaEtaConv a a') :
    Lambda.betaEtaConv (.app f a) (.app f a') := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih => exact .step ih (betaEtaStep_app_right f hs)
  | symm_step _ hs ih => exact .symm_step ih (betaEtaStep_app_right f hs)

/-- Problem 5.1 restricted to polynomials. -/
def PolyFiveOne : Prop :=
  ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam (app (polyTm m ps) (var 0)))
    (toLam (app (var 0) (app (polyTm m ps) (var 0))))

/-- Statman's (valid) first step, in the form the reduction needs: every closed `B`,`M`,`I`-term
`Y` with `Y x =βη x (Y x)` is βη-equivalent to a polynomial.  Stated only; **not** proved here. -/
def StatmanStepOne : Prop :=
  ∀ Y : Tm, IsBMI Y → Lambda.betaEtaConv (toLam (app Y (var 0)))
      (toLam (app (var 0) (app Y (var 0)))) →
    ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam Y) (toLam (polyTm m ps))

/-- A polynomial solution is a solution of Problem 5.1. -/
theorem problemFiveOne_of_poly (h : PolyFiveOne) : ProblemFiveOne := by
  obtain ⟨m, ps, h⟩ := h
  exact ⟨polyTm m ps, polyTm_isBMI m ps, h⟩

/-- **Problem 5.1 holds iff it holds for some polynomial**, given Statman's first step. -/
theorem problemFiveOne_iff_poly (hS : StatmanStepOne) : ProblemFiveOne ↔ PolyFiveOne := by
  refine ⟨fun ⟨Y, hY, hfix⟩ => ?_, problemFiveOne_of_poly⟩
  obtain ⟨m, ps, hp⟩ := hS Y hY hfix
  refine ⟨m, ps, ?_⟩
  have h1 : Lambda.betaEtaConv (toLam (app (polyTm m ps) (var 0))) (toLam (app Y (var 0))) :=
    betaEtaConv_app_left (betaEtaConv_symm hp) _
  have h2 : Lambda.betaEtaConv (toLam (app (var 0) (app Y (var 0))))
      (toLam (app (var 0) (app (polyTm m ps) (var 0)))) :=
    betaEtaConv_app_right _ (betaEtaConv_app_left hp _)
  exact (h1.trans hfix).trans h2

end TLCA4
