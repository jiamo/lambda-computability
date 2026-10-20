/-
**Route (ii) re-indexed by the erasure** — task `M29-EP-IMPREDICATIVE`, round 8, part A2/A3.

The route (ii) predicate `RouteII.Good` of `Start/PTSExpansionRouteII.lean` is defined by
recursion on a λ2 skeleton.  With the erasure `ErasureP2.er` of `Start/PTSErasureP2.lean`, a
λP2 judgement `Γ ⊢ M : T` is assigned the skeleton `er (ctxCl Γ) ρ T` of its type:

* `RouteII.GoodE ξ ρ Γ M T` — **the predicate indexed by the erased skeleton of the type**;
* `RouteII.GoodE.reduceType` — invariance under reduction of a well-typed type (the erasure is
  invariant, `ErasureP2.er_reduces`, and the candidates are closed under type reduction);
* `RouteII.GoodE.isCand` / `RouteII.GoodE.escape` — CR1: good judgements normalize;
* `RouteII.GoodE.app` — **the object-application case** `(∗,∗)`/`(∗,□)` of the fundamental lemma
  in erased form: the skeleton of `B[N]` for an object `N` is that of `B`
  (`ErasureP2.er_instantiate_obj`);
* `RouteII.GoodE.tyApp` — **the type-application case `(□,∗)`** in erased form: the skeleton of
  `B[U]` for a constructor `U` is `(er B)[er U]` (`ErasureP2.er_instantiate`), and the typed
  Kripke candidate chosen for the bound variable is `⟦er U⟧ξ` (`RouteII.Good_inst`);
* `RouteII.NormNW.expand` — CR3 in its head-expansion form for the base predicate: the base
  predicate is closed under expansion of the subject.

What is not built (A3): the fundamental lemma.  Its first failing step is CR3 at neutral
applications: `NormNW Γ (app x N) (B[N])` for a variable `x : Π A B` needs the canonical form of
the type `B[N]`, which is the instance `HSubstSort` (equivalently `SortFundamental`) for the
sort-typed judgement `B : s`; see `docs/goal/evidence/M29-EP.md`, round 8.
-/

import Start.PTSErasureP2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PureTypeSystem

namespace RouteII

open LambdaPi (Srt)
open ErasureP2
open CoC (Cls cl ncons bindC ctxCl)

/-- λP2. -/
abbrev P2 : Specification Srt := cubeSpec lambdaP2

/-- **The route (ii) predicate indexed by the erased skeleton of the type.** -/
def GoodE (ξ : ℕ → Cand) (ρ : ℕ → Sk) (Γ : List (Expr Srt)) (M T : Expr Srt) : Prop :=
  Good P2 (er (ctxCl Γ) ρ T) ξ Γ M T

/-- CR1 in erased form. -/
theorem GoodE.escape {ξ : ℕ → Cand} (hξ : ∀ i, IsCand P2 (ξ i)) {ρ : ℕ → Sk}
    {Γ : List (Expr Srt)} {M T : Expr Srt} (h : GoodE ξ ρ Γ M T) : NormNW P2 Γ M T :=
  Good.escape hξ h

theorem GoodE.typed {ξ : ℕ → Cand} (hξ : ∀ i, IsCand P2 (ξ i)) {ρ : ℕ → Sk}
    {Γ : List (Expr Srt)} {M T : Expr Srt} (h : GoodE ξ ρ Γ M T) : HasTypeR P2 Γ M T :=
  (Good.isCand P2 _ ξ hξ).typed h

/-- **Invariance under reduction of a well-typed type.** -/
theorem GoodE.reduceType {ξ : ℕ → Cand} (hξ : ∀ i, IsCand P2 (ξ i)) {ρ : ℕ → Sk}
    {Γ : List (Expr Srt)} {M T T' X : Expr Srt} (hT : HasType P2 Γ T X) (hr : Reduces T T')
    (h : GoodE ξ ρ Γ M T) : GoodE ξ ρ Γ M T' := by
  unfold GoodE at h ⊢
  rw [← er_reduces hT hr ρ]
  exact (Good.isCand P2 _ ξ hξ).red h hr

/-- **The object-application case in erased form.**  If the syntactic type `Π A B` of `M` has a
domain which is not a kind, and the argument `N` is an object, a good `M` applied to an argument
good at the skeleton of `A` is good at the skeleton of `B[N]`. -/
theorem GoodE.app {ξ : ℕ → Cand} {ρ : ℕ → Sk} {Γ : List (Expr Srt)} {M T A B A' B' N : Expr Srt}
    (hA : ∀ a, cl (ctxCl Γ) A ≠ .kind a) (hPiC : IsC (cl (ctxCl Γ) (.pi A B)))
    (hN : cl (ctxCl Γ) N = .obj)
    (h : Good P2 (er (ctxCl Γ) ρ (.pi A B)) ξ Γ M T) (hT : Reduces T (.pi A' B'))
    (hNg : Good P2 (er (ctxCl Γ) ρ A) ξ Γ N A') :
    Good P2 (er (ctxCl Γ) ρ (B.instantiate N)) ξ Γ (.app M N) (B'.instantiate N) := by
  rw [er_pi_type hPiC hA] at h
  rw [er_instantiate_obj B N (ctxCl Γ) ρ junk (by rw [hN]; exact id), hN]
  exact Good.app h hT hNg

/-- **The type-application case `(□,∗)` in erased form.**  If the syntactic type `Π K B` of `M`
quantifies over a kind `K` of skeleton `a` and `U` is a constructor of that skeleton, a good `M`
applied to `U` is good at the skeleton of `B[U]`, which is `(er B)[er U]`; the typed Kripke
candidate interpreting the bound variable is `⟦er U⟧ξ`. -/
theorem GoodE.tyApp {ξ : ℕ → Cand} (hξ : ∀ i, IsCand P2 (ξ i)) {ρ : ℕ → Sk}
    {Γ : List (Expr Srt)} {M T K B K' B' U : Expr Srt} {a : CoC.Sk}
    (hK : cl (ctxCl Γ) K = .kind a) (hU : cl (ctxCl Γ) U = .constr a)
    (hPiC : IsC (cl (ctxCl Γ) (.pi K B)))
    (h : Good P2 (er (ctxCl Γ) ρ (.pi K B)) ξ Γ M T) (hT : Reduces T (.pi K' B'))
    (hUt : HasTypeR P2 Γ U K') :
    Good P2 (er (ctxCl Γ) ρ (B.instantiate U)) ξ Γ (.app M U) (B'.instantiate U) := by
  rw [er_pi_kind hPiC hK] at h
  rw [er_instantiate, hU]
  exact Good.tyApp hξ _ h hT hUt

/-- **CR3, head-expansion form, for the base predicate**: normalizability of a judgement is
closed under expansion of the subject. -/
theorem NormNW.expand {P : Specification Srt} {Γ : List (Expr Srt)} {M M' T : Expr Srt}
    (hr : Reduces M M') (h : NormNW P Γ M' T) : NormNW P Γ M T := by
  obtain ⟨Γ', M'', T', hc, hM, hT, hNW⟩ := h
  exact ⟨Γ', M'', T', hc, hr.trans hM, hT, hNW⟩

end RouteII

end PureTypeSystem
