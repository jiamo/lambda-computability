/-
**The type-directed equivalence algorithm indexed by the erasure** — task
`M23-LF-EQUIV-COMPLETE`.

The algorithm of `Start/LambdaPiLFEquiv.lean` is indexed by the skeleton `skel Δ A`, which reads
the skeletons of the type variables from the context and changes under type-level β-steps of
untypable terms (`skel_beta_raw_counterexample`).  Here it is indexed by the context-free erasure
`LambdaPi.er` of `Start/LambdaPiLFLevel.lean`, as in Harper and Pfenning, where a type family
applied to objects erases to the base type.  Everything else is unchanged:

* `LambdaPi.EqvE` — the algorithm: η-expansion at arrows; at the base, weak head
  normalization and comparison of two sorts, two products (domains of the same erasure, the
  codomains in the context extended by that erasure), or two paths; paths compared
  structurally with their simple type synthesised from the context;
* `EqvE.sound` (algorithmically equivalent terms are βη-convertible), `EqvE.rename`
  (weakening), `EqvE.symm`, `EqvE.trans` (a PER);
* `LambdaPi.LRE` — the Kripke logical relation, whose arrow case quantifies over related
  arguments of erasure `base` (the objects); `LRE.escape`, `LRE.reflect`, `LRE.rename`,
  `LRE.whExpand_left`, `LRE.whExpand_right`, `LRE.symm`, `LRE.trans`.
-/

import Start.LambdaPiLFLevel
import Start.LambdaPiLFEquivPER

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### The algorithm -/

/-- **The type-directed equivalence algorithm**, indexed by erasures. -/
inductive EqvE : EqvKind → List STy → Tm → Tm → STy → Prop
  /-- Extensionality at an arrow. -/
  | arrow {Δ : List STy} {M N : Tm} {σ τ : STy} :
      EqvE .alg (σ :: Δ) (app (shift M) (var 0)) (app (shift N) (var 0)) τ →
      EqvE .alg Δ M N (STy.arrow σ τ)
  /-- At the base: weak head normalize to two equivalent paths. -/
  | basePath {Δ : List STy} {M N M' N' : Tm} : WhRed M M' → WhRed N N' →
      EqvE .path Δ M' N' STy.base → EqvE .alg Δ M N STy.base
  /-- At the base: weak head normalize to the same sort. -/
  | baseSort {Δ : List STy} {M N : Tm} {s : Srt} : WhRed M (sort s) → WhRed N (sort s) →
      EqvE .alg Δ M N STy.base
  /-- At the base: weak head normalize to two products whose domains are equivalent and have
  the same erasure, and whose codomains are equivalent. -/
  | basePi {Δ : List STy} {M N A B A' B' : Tm} : WhRed M (pi A B) → WhRed N (pi A' B') →
      EqvE .alg Δ A A' STy.base → er A = er A' →
      EqvE .alg (er A :: Δ) B B' STy.base → EqvE .alg Δ M N STy.base
  /-- A variable, with the simple type the context gives it. -/
  | var {Δ : List STy} (n : ℕ) : EqvE .path Δ (var n) (var n) (Δ.getD n STy.base)
  /-- An application of paths to algorithmically equivalent arguments. -/
  | app {Δ : List STy} {p q a b : Tm} {σ τ : STy} : EqvE .path Δ p q (STy.arrow σ τ) →
      EqvE .alg Δ a b σ → EqvE .path Δ (app p a) (app q b) τ

/-- Algorithmic equivalence `Δ ⊢ M ⇔ N : τ`. -/
abbrev AlgEqE (Δ : List STy) (M N : Tm) (τ : STy) : Prop := EqvE .alg Δ M N τ

/-- Structural equivalence `Δ ⊢ p ↔ q : τ`. -/
abbrev PathEqE (Δ : List STy) (p q : Tm) (τ : STy) : Prop := EqvE .path Δ p q τ

/-- **Soundness of the algorithm for βη-conversion.** -/
theorem EqvE.sound {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : EqvE k Δ M N τ) :
    BetaEtaConv M N := by
  induction h with
  | arrow _ ih =>
      exact ((betaEtaConv_eta (sort Srt.star) _).symm.trans
        (BetaEtaConv.lamR _ ih)).trans (betaEtaConv_eta _ _)
  | basePath hM hN _ ih => exact (hM.betaEtaConv.trans ih).trans hN.betaEtaConv.symm
  | baseSort hM hN => exact hM.betaEtaConv.trans hN.betaEtaConv.symm
  | basePi hM hN _ _ _ ihA ihB =>
      exact (hM.betaEtaConv.trans ((BetaEtaConv.piL _ ihA).trans (BetaEtaConv.piR _ ihB))).trans
        hN.betaEtaConv.symm
  | var n => exact BetaEtaConv.refl _
  | app _ _ ihp iha => exact (BetaEtaConv.appL _ ihp).trans (BetaEtaConv.appR _ iha)

/-- **The algorithm is stable under renamings respecting the simple types.** -/
theorem EqvE.rename {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : EqvE k Δ M N τ) :
    ∀ {ρ : ℕ → ℕ} {Δ' : List STy}, RenS ρ Δ Δ' →
      EqvE k Δ' (LambdaPi.rename ρ M) (LambdaPi.rename ρ N) τ := by
  induction h with
  | @arrow Δ M N σ τ _ ih =>
      intro ρ Δ' hρ
      have := ih (hρ.up σ)
      simp only [rename_app, rename_upr_shift] at this
      exact EqvE.arrow this
  | basePath hM hN _ ih =>
      intro ρ Δ' hρ
      exact EqvE.basePath (hM.rename ρ) (hN.rename ρ) (ih hρ)
  | baseSort hM hN =>
      intro ρ Δ' hρ
      exact EqvE.baseSort (by simpa using hM.rename ρ) (by simpa using hN.rename ρ)
  | @basePi Δ M N A B A' B' hM hN _ hsk _ ihA ihB =>
      intro ρ Δ' hρ
      have hρ' : RenS (upr ρ) (er A :: Δ) (er (LambdaPi.rename ρ A) :: Δ') := by
        rw [er_rename]; exact hρ.up _
      exact EqvE.basePi (by simpa using hM.rename ρ) (by simpa using hN.rename ρ) (ihA hρ)
        (by rw [er_rename, er_rename, hsk]) (ihB hρ')
  | var n =>
      intro ρ Δ' hρ
      have := EqvE.var (Δ := Δ') (ρ n)
      rw [hρ n] at this
      simpa using this
  | app _ _ ihp iha =>
      intro ρ Δ' hρ
      exact EqvE.app (ihp hρ) (iha hρ)

/-! ### Paths -/

theorem EqvE.path_isPath {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : EqvE k Δ M N τ) :
    k = .path → IsPath M ∧ IsPath N := by
  induction h with
  | arrow => intro h; cases h
  | basePath => intro h; cases h
  | baseSort => intro h; cases h
  | basePi => intro h; cases h
  | var n => intro _; exact ⟨.var n, .var n⟩
  | app _ _ ihp _ =>
      intro _
      obtain ⟨hp, hq⟩ := ihp rfl
      exact ⟨.app _ hp, .app _ hq⟩

theorem PathEqE.isPath {Δ : List STy} {M N : Tm} {τ : STy} (h : PathEqE Δ M N τ) :
    IsPath M ∧ IsPath N :=
  EqvE.path_isPath h rfl

/-! ### Symmetry and transitivity -/

/-- **Symmetry of the algorithm.** -/
theorem EqvE.symm {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : EqvE k Δ M N τ) :
    EqvE k Δ N M τ := by
  induction h with
  | arrow _ ih => exact EqvE.arrow ih
  | basePath hM hN _ ih => exact EqvE.basePath hN hM ih
  | baseSort hM hN => exact EqvE.baseSort hN hM
  | basePi hM hN _ hsk _ ihA ihB =>
      refine EqvE.basePi hN hM ihA hsk.symm ?_
      rw [← hsk]; exact ihB
  | var n => exact EqvE.var n
  | app _ _ ihp iha => exact EqvE.app ihp iha

theorem EqvE.trans_aux {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : EqvE k Δ M N τ) :
    ∀ {P : Tm} {τ' : STy}, EqvE k Δ N P τ' → (k = .alg → τ = τ') →
      τ = τ' ∧ EqvE k Δ M P τ := by
  induction h with
  | @arrow Δ M N σ τ _ ih =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      cases h2 with
      | arrow h2 =>
          refine ⟨rfl, EqvE.arrow (ih h2 (fun _ => rfl)).2⟩
  | @basePath Δ M N M' N' hM hN hp ih =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      have hN'p := (PathEqE.isPath hp).2
      refine ⟨rfl, ?_⟩
      cases h2 with
      | basePath hN₂ hP hp₂ =>
          have e := WhRed.whnf_unique hN hN₂ hN'p.whnf (PathEqE.isPath hp₂).1.whnf
          subst e
          exact EqvE.basePath hM hP (ih hp₂ (fun h => by cases h)).2
      | baseSort hN₂ hP =>
          have e := WhRed.whnf_unique hN hN₂ hN'p.whnf (whnf_sort _)
          exact absurd e hN'p.ne_sort
      | basePi hN₂ hP _ _ _ =>
          have e := WhRed.whnf_unique hN hN₂ hN'p.whnf (whnf_pi _ _)
          exact absurd e hN'p.ne_pi
  | @baseSort Δ M N s hM hN =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      refine ⟨rfl, ?_⟩
      cases h2 with
      | basePath hN₂ hP hp₂ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_sort _) (PathEqE.isPath hp₂).1.whnf
          exact absurd e.symm (PathEqE.isPath hp₂).1.ne_sort
      | baseSort hN₂ hP =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_sort _) (whnf_sort _)
          cases e
          exact EqvE.baseSort hM hP
      | basePi hN₂ hP _ _ _ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_sort _) (whnf_pi _ _)
          cases e
  | @basePi Δ M N A B A' B' hM hN _ hsk _ ihA ihB =>
      intro P τ' h2 hτ
      obtain rfl := hτ rfl
      refine ⟨rfl, ?_⟩
      cases h2 with
      | basePath hN₂ hP hp₂ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_pi _ _) (PathEqE.isPath hp₂).1.whnf
          exact absurd e.symm (PathEqE.isPath hp₂).1.ne_pi
      | baseSort hN₂ hP =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_pi _ _) (whnf_sort _)
          cases e
      | basePi hN₂ hP hA₂ hsk₂ hB₂ =>
          have e := WhRed.whnf_unique hN hN₂ (whnf_pi _ _) (whnf_pi _ _)
          cases e
          refine EqvE.basePi hM hP (ihA hA₂ (fun _ => rfl)).2 (hsk.trans hsk₂) ?_
          rw [← hsk] at hB₂
          exact (ihB hB₂ (fun _ => rfl)).2
  | var n =>
      intro P τ' h2 _
      cases h2 with
      | var => exact ⟨rfl, EqvE.var n⟩
  | @app Δ p q a b σ τ _ _ ihp iha =>
      intro P τ' h2 _
      cases h2 with
      | app hq hb =>
          obtain ⟨e, hpr⟩ := ihp hq (fun h => by cases h)
          cases e
          exact ⟨rfl, EqvE.app hpr (iha hb (fun _ => rfl)).2⟩

/-- **Transitivity of the algorithm.** -/
theorem EqvE.trans {k : EqvKind} {Δ : List STy} {M N P : Tm} {τ : STy} (h : EqvE k Δ M N τ)
    (h' : EqvE k Δ N P τ) : EqvE k Δ M P τ :=
  (h.trans_aux h' (fun _ => rfl)).2

/-- The simple type synthesised for a path is unique. -/
theorem EqvE.path_ty_unique {Δ : List STy} {p q r : Tm} {τ τ' : STy} (h : PathEqE Δ p q τ)
    (h' : PathEqE Δ q r τ') : τ = τ' :=
  (EqvE.trans_aux h h' (fun h => by cases h)).1

/-! ### The Kripke logical relation -/

/-- **The Kripke logical relation**: algorithmic equivalence at the base; at an arrow, related
arguments of erasure `base`, in every extension of the context, give related applications. -/
def LRE : STy → List STy → Tm → Tm → Prop
  | .base, Δ, M, N => AlgEqE Δ M N STy.base
  | .arrow σ τ, Δ, M, N => ∀ (Δ' : List STy) (ρ : ℕ → ℕ), RenS ρ Δ Δ' → ∀ a b,
      er a = STy.base → er b = STy.base → LRE σ Δ' a b →
      LRE τ Δ' (app (LambdaPi.rename ρ M) a) (app (LambdaPi.rename ρ N) b)

/-- **Escape and reflection**, by simultaneous induction on the simple type. -/
theorem LRE.escape_reflect : ∀ τ : STy,
    (∀ {Δ M N}, LRE τ Δ M N → AlgEqE Δ M N τ) ∧ (∀ {Δ p q}, PathEqE Δ p q τ → LRE τ Δ p q)
  | .base => ⟨fun h => h, fun h => EqvE.basePath .refl .refl h⟩
  | .arrow σ τ => by
      obtain ⟨escσ, refσ⟩ := LRE.escape_reflect σ
      obtain ⟨escτ, refτ⟩ := LRE.escape_reflect τ
      refine ⟨fun {Δ M N} h => ?_, fun {Δ p q} h => ?_⟩
      · have h0 : LRE σ (σ :: Δ) (var 0) (var 0) := refσ (EqvE.var (Δ := σ :: Δ) 0)
        exact EqvE.arrow (escτ (h (σ :: Δ) Nat.succ (RenS.succ Δ σ) _ _ rfl rfl h0))
      · intro Δ' ρ hρ a b _ _ hab
        exact refτ (EqvE.app (h.rename hρ) (escσ hab))

/-- **Escape**: related terms are algorithmically equivalent. -/
theorem LRE.escape {τ : STy} {Δ : List STy} {M N : Tm} (h : LRE τ Δ M N) : AlgEqE Δ M N τ :=
  (LRE.escape_reflect τ).1 h

/-- **Reflection**: structurally equivalent paths are related. -/
theorem LRE.reflect {τ : STy} {Δ : List STy} {p q : Tm} (h : PathEqE Δ p q τ) : LRE τ Δ p q :=
  (LRE.escape_reflect τ).2 h

/-- Variables are related to themselves. -/
theorem LRE.var (Δ : List STy) (n : ℕ) : LRE (Δ.getD n STy.base) Δ (var n) (var n) :=
  LRE.reflect (EqvE.var n)

/-- **Monotonicity** under renamings respecting the simple types. -/
theorem LRE.rename : ∀ {τ : STy} {Δ Δ' : List STy} {M N : Tm} {ρ : ℕ → ℕ}, RenS ρ Δ Δ' →
    LRE τ Δ M N → LRE τ Δ' (LambdaPi.rename ρ M) (LambdaPi.rename ρ N)
  | .base, _, _, _, _, _, hρ, h => EqvE.rename h hρ
  | .arrow _ _, _, _, M, N, ρ, hρ, h => by
      intro Δ'' ρ' hρ' a b ha hb hab
      have := h Δ'' (fun n => ρ' (ρ n)) (hρ.comp hρ') a b ha hb hab
      simpa [rename_rename] using this

theorem EqvE.whExpand_left {Δ : List STy} {M M' N : Tm} (hs : WhStep M M')
    (h : AlgEqE Δ M' N STy.base) : AlgEqE Δ M N STy.base := by
  cases h with
  | basePath hM hN hp => exact EqvE.basePath (.head hs hM) hN hp
  | baseSort hM hN => exact EqvE.baseSort (.head hs hM) hN
  | basePi hM hN hA hsk hB => exact EqvE.basePi (.head hs hM) hN hA hsk hB

theorem EqvE.whExpand_right {Δ : List STy} {M N N' : Tm} (hs : WhStep N N')
    (h : AlgEqE Δ M N' STy.base) : AlgEqE Δ M N STy.base := by
  cases h with
  | basePath hM hN hp => exact EqvE.basePath hM (.head hs hN) hp
  | baseSort hM hN => exact EqvE.baseSort hM (.head hs hN)
  | basePi hM hN hA hsk hB => exact EqvE.basePi hM (.head hs hN) hA hsk hB

/-- **Closure under weak head expansion** (left). -/
theorem LRE.whExpand_left : ∀ {τ : STy} {Δ : List STy} {M M' N : Tm}, WhStep M M' →
    LRE τ Δ M' N → LRE τ Δ M N
  | .base, _, _, _, _, hs, h => EqvE.whExpand_left hs h
  | .arrow _ _, _, _, _, _, hs, h => fun Δ' ρ hρ a b ha hb hab =>
      LRE.whExpand_left (WhStep.appL a (hs.rename ρ)) (h Δ' ρ hρ a b ha hb hab)

/-- **Closure under weak head expansion** (right). -/
theorem LRE.whExpand_right : ∀ {τ : STy} {Δ : List STy} {M N N' : Tm}, WhStep N N' →
    LRE τ Δ M N' → LRE τ Δ M N
  | .base, _, _, _, _, hs, h => EqvE.whExpand_right hs h
  | .arrow _ _, _, _, _, _, hs, h => fun Δ' ρ hρ a b ha hb hab =>
      LRE.whExpand_right (WhStep.appL b (hs.rename ρ)) (h Δ' ρ hρ a b ha hb hab)

theorem LRE.whRedExpand_left {τ : STy} {Δ : List STy} {M M' N : Tm} (hs : WhRed M M')
    (h : LRE τ Δ M' N) : LRE τ Δ M N := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hs _ ih => exact LRE.whExpand_left hs ih

theorem LRE.whRedExpand_right {τ : STy} {Δ : List STy} {M N N' : Tm} (hs : WhRed N N')
    (h : LRE τ Δ M N') : LRE τ Δ M N := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hs _ ih => exact LRE.whExpand_right hs ih

/-- **Symmetry of the logical relation.** -/
theorem LRE.symm : ∀ {τ : STy} {Δ : List STy} {M N : Tm}, LRE τ Δ M N → LRE τ Δ N M
  | .base, _, _, _, h => EqvE.symm h
  | .arrow _ _, _, _, _, h => fun Δ' ρ hρ a b ha hb hab =>
      LRE.symm (h Δ' ρ hρ b a hb ha (LRE.symm hab))

/-- **Transitivity of the logical relation.** -/
theorem LRE.trans : ∀ {τ : STy} {Δ : List STy} {M N P : Tm}, LRE τ Δ M N → LRE τ Δ N P →
    LRE τ Δ M P
  | .base, _, _, _, _, h, h' => EqvE.trans h h'
  | .arrow _ _, _, _, _, _, h, h' => fun Δ' ρ hρ a b ha hb hab =>
      LRE.trans (h Δ' ρ hρ a b ha hb hab) (h' Δ' ρ hρ b b hb hb (LRE.trans (LRE.symm hab) hab))

/-- The right component of a related pair is related to itself. -/
theorem LRE.right {τ : STy} {Δ : List STy} {M N : Tm} (h : LRE τ Δ M N) : LRE τ Δ N N :=
  LRE.trans (LRE.symm h) h

/-- The left component of a related pair is related to itself. -/
theorem LRE.left {τ : STy} {Δ : List STy} {M N : Tm} (h : LRE τ Δ M N) : LRE τ Δ M M :=
  LRE.trans h (LRE.symm h)

end LambdaPi
