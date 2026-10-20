/-
**Type-directed βη-equivalence for LF (`λΠ`)** — task `M23-LF-EQUIV` (round 7, partial), after
Harper and Pfenning, *On equivalence and canonical forms in the LF type theory* (TOCL 2005).

The algorithm is indexed by the simple skeletons of `λΠ` types (`LambdaPi.STy`,
`Start/LambdaPiSkeleton.lean`), as in Harper and Pfenning's erasure to simple types.  It
η-expands at arrow skeletons and compares weak head normal forms structurally at the base:

* `LambdaPi.WhStep` / `LambdaPi.WhRed` — weak head reduction (a β-step at the head);
* `LambdaPi.AlgEq Δ M N τ` — **algorithmic equivalence** at the skeleton `τ`, in a context `Δ`
  of skeletons: at `σ ⇒ τ` compare `M 0` and `N 0` in `σ :: Δ` (extensionality); at the base,
  weak head normalize and compare the heads: two sorts, two products (domains at the base,
  codomains in the extended context), or two paths;
* `LambdaPi.PathEq Δ p q τ` — **structural equivalence** of paths (a variable applied to
  arguments), whose skeleton is synthesised;
* `LambdaPi.Eqv.sound` — **soundness of the algorithm for βη-conversion**: algorithmically
  equivalent terms are βη-convertible;
* `LambdaPi.Eqv.rename` — the algorithm is stable under renamings respecting the skeletons
  (weakening);
* `LambdaPi.LR` — the **Kripke logical relation** on skeleton types: algorithmic equivalence at
  the base, and at `σ ⇒ τ` related arguments in every extension of the context give related
  applications;
* `LambdaPi.LR.escape` / `LambdaPi.LR.reflect` — **escape** (related terms are algorithmically
  equivalent) and **reflection** (structurally equivalent paths are related), by simultaneous
  induction on the skeleton;
* `LambdaPi.LR.rename` (monotonicity) and `LambdaPi.LR.whExpand_left` / `whExpand_right`
  (closure under weak head expansion), the two closure properties the fundamental lemma uses;
* `LambdaPi.TEq` — the **declarative typed equality judgement** `Γ ⊢ M ≡ N : A` of `λΠ` with
  typed β and typed η, and `LambdaPi.TEq.betaEtaConv`: declaratively equal terms are
  βη-convertible.

Open (the gap row `M23-LF-EQUIV-COMPLETE`): soundness of the algorithm for the declarative typed
judgement, the fundamental lemma of the logical relation (completeness), and termination on
well-typed terms.
-/

import Start.LambdaPiEtaConfluent
import Start.LambdaPiSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Weak head reduction -/

/-- One step of weak head reduction. -/
inductive WhStep : Tm → Tm → Prop
  | beta (A b a : Tm) : WhStep (app (lam A b) a) (b[a])
  | appL {f f' : Tm} (a : Tm) : WhStep f f' → WhStep (app f a) (app f' a)

/-- Many-step weak head reduction. -/
abbrev WhRed : Tm → Tm → Prop := Relation.ReflTransGen WhStep

theorem WhStep.step {t u : Tm} (h : WhStep t u) : Step t u := by
  induction h with
  | beta A b a => exact Step.beta A b a
  | appL a _ ih => exact Step.appL a ih

theorem WhRed.betaEtaConv {t u : Tm} (h : WhRed t u) : BetaEtaConv t u := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | tail _ hs ih => exact ih.step (Or.inl hs.step)

theorem WhStep.rename {t t' : Tm} (h : WhStep t t') (ρ : ℕ → ℕ) :
    WhStep (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h with
  | beta A b a =>
      have hb := WhStep.beta (LambdaPi.rename ρ A) (LambdaPi.rename (upr ρ) b)
        (LambdaPi.rename ρ a)
      simpa [inst_rename] using hb
  | appL a _ ih => exact WhStep.appL _ ih

theorem WhRed.rename {t t' : Tm} (h : WhRed t t') (ρ : ℕ → ℕ) :
    WhRed (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (hs.rename ρ)

/-! ### The algorithm -/

/-- The two judgements of the algorithm. -/
inductive EqvKind where
  /-- Type-directed algorithmic equivalence. -/
  | alg
  /-- Structural equivalence of paths. -/
  | path

/-- **The type-directed equivalence algorithm**, indexed by skeletons. -/
inductive Eqv : EqvKind → List STy → Tm → Tm → STy → Prop
  /-- Extensionality at an arrow skeleton. -/
  | arrow {Δ : List STy} {M N : Tm} {σ τ : STy} :
      Eqv .alg (σ :: Δ) (app (shift M) (var 0)) (app (shift N) (var 0)) τ →
      Eqv .alg Δ M N (STy.arrow σ τ)
  /-- At the base: weak head normalize to two equivalent paths. -/
  | basePath {Δ : List STy} {M N M' N' : Tm} : WhRed M M' → WhRed N N' →
      Eqv .path Δ M' N' STy.base → Eqv .alg Δ M N STy.base
  /-- At the base: weak head normalize to the same sort. -/
  | baseSort {Δ : List STy} {M N : Tm} {s : Srt} : WhRed M (sort s) → WhRed N (sort s) →
      Eqv .alg Δ M N STy.base
  /-- At the base: weak head normalize to two products with equivalent domains and codomains. -/
  | basePi {Δ : List STy} {M N A B A' B' : Tm} : WhRed M (pi A B) → WhRed N (pi A' B') →
      Eqv .alg Δ A A' STy.base → Eqv .alg (skel Δ A :: Δ) B B' STy.base →
      Eqv .alg Δ M N STy.base
  /-- A variable, with its skeleton. -/
  | var {Δ : List STy} (n : ℕ) : Eqv .path Δ (var n) (var n) (Δ.getD n STy.base)
  /-- An application of paths to algorithmically equivalent arguments. -/
  | app {Δ : List STy} {p q a b : Tm} {σ τ : STy} : Eqv .path Δ p q (STy.arrow σ τ) →
      Eqv .alg Δ a b σ → Eqv .path Δ (app p a) (app q b) τ

/-- Algorithmic equivalence `Δ ⊢ M ⇔ N : τ`. -/
abbrev AlgEq (Δ : List STy) (M N : Tm) (τ : STy) : Prop := Eqv .alg Δ M N τ

/-- Structural equivalence `Δ ⊢ p ↔ q : τ`. -/
abbrev PathEq (Δ : List STy) (p q : Tm) (τ : STy) : Prop := Eqv .path Δ p q τ

/-- η-expansion is a βη-conversion: `f` and `λ(x : A). f x` are convertible. -/
theorem betaEtaConv_eta (A f : Tm) : BetaEtaConv (lam A (app (shift f) (var 0))) f :=
  (BetaEtaConv.refl _).step (Or.inr (EtaStep.eta A f))

/-- **Soundness of the algorithm for βη-conversion.** -/
theorem Eqv.sound {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : Eqv k Δ M N τ) :
    BetaEtaConv M N := by
  induction h with
  | arrow _ ih =>
      exact ((betaEtaConv_eta (sort Srt.star) _).symm.trans
        (BetaEtaConv.lamR _ ih)).trans (betaEtaConv_eta _ _)
  | basePath hM hN _ ih => exact (hM.betaEtaConv.trans ih).trans hN.betaEtaConv.symm
  | baseSort hM hN => exact hM.betaEtaConv.trans hN.betaEtaConv.symm
  | basePi hM hN _ _ ihA ihB =>
      exact (hM.betaEtaConv.trans ((BetaEtaConv.piL _ ihA).trans (BetaEtaConv.piR _ ihB))).trans
        hN.betaEtaConv.symm
  | var n => exact BetaEtaConv.refl _
  | app _ _ ihp iha => exact (BetaEtaConv.appL _ ihp).trans (BetaEtaConv.appR _ iha)

/-! ### Weakening -/

/-- A renaming respecting the skeletons of the variables. -/
def RenS (ρ : ℕ → ℕ) (Δ Δ' : List STy) : Prop :=
  ∀ n, Δ'.getD (ρ n) STy.base = Δ.getD n STy.base

theorem RenS.up {ρ : ℕ → ℕ} {Δ Δ' : List STy} (h : RenS ρ Δ Δ') (σ : STy) :
    RenS (upr ρ) (σ :: Δ) (σ :: Δ') := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simpa [upr] using h n

theorem RenS.succ (Δ : List STy) (σ : STy) : RenS Nat.succ Δ (σ :: Δ) := fun _ => rfl

theorem RenS.comp {ρ ρ' : ℕ → ℕ} {Δ Δ' Δ'' : List STy} (h : RenS ρ Δ Δ') (h' : RenS ρ' Δ' Δ'') :
    RenS (fun n => ρ' (ρ n)) Δ Δ'' := fun n => (h' (ρ n)).trans (h n)

/-- **The algorithm is stable under renamings respecting the skeletons.** -/
theorem Eqv.rename {k : EqvKind} {Δ : List STy} {M N : Tm} {τ : STy} (h : Eqv k Δ M N τ) :
    ∀ {ρ : ℕ → ℕ} {Δ' : List STy}, RenS ρ Δ Δ' →
      Eqv k Δ' (LambdaPi.rename ρ M) (LambdaPi.rename ρ N) τ := by
  induction h with
  | @arrow Δ M N σ τ _ ih =>
      intro ρ Δ' hρ
      have := ih (hρ.up σ)
      simp only [rename_app, rename_upr_shift] at this
      exact Eqv.arrow this
  | basePath hM hN _ ih =>
      intro ρ Δ' hρ
      exact Eqv.basePath (hM.rename ρ) (hN.rename ρ) (ih hρ)
  | baseSort hM hN =>
      intro ρ Δ' hρ
      exact Eqv.baseSort (by simpa using hM.rename ρ) (by simpa using hN.rename ρ)
  | @basePi Δ M N A B A' B' hM hN _ _ ihA ihB =>
      intro ρ Δ' hρ
      have hs : skel Δ' (LambdaPi.rename ρ A) = skel Δ A := skel_rename hρ A
      have hρ' : RenS (upr ρ) (skel Δ A :: Δ) (skel Δ' (LambdaPi.rename ρ A) :: Δ') := by
        rw [hs]; exact hρ.up _
      exact Eqv.basePi (by simpa using hM.rename ρ) (by simpa using hN.rename ρ) (ihA hρ)
        (ihB hρ')
  | var n =>
      intro ρ Δ' hρ
      have := Eqv.var (Δ := Δ') (ρ n)
      rw [hρ n] at this
      simpa using this
  | app _ _ ihp iha =>
      intro ρ Δ' hρ
      exact Eqv.app (ihp hρ) (iha hρ)

/-! ### The Kripke logical relation -/

/-- **The Kripke logical relation** on skeleton types. -/
def LR : STy → List STy → Tm → Tm → Prop
  | .base, Δ, M, N => AlgEq Δ M N STy.base
  | .arrow σ τ, Δ, M, N => ∀ (Δ' : List STy) (ρ : ℕ → ℕ), RenS ρ Δ Δ' → ∀ a b, LR σ Δ' a b →
      LR τ Δ' (app (LambdaPi.rename ρ M) a) (app (LambdaPi.rename ρ N) b)

/-- **Escape and reflection**, by simultaneous induction on the skeleton. -/
theorem LR.escape_reflect : ∀ τ : STy,
    (∀ {Δ M N}, LR τ Δ M N → AlgEq Δ M N τ) ∧ (∀ {Δ p q}, PathEq Δ p q τ → LR τ Δ p q)
  | .base => ⟨fun h => h, fun h => Eqv.basePath .refl .refl h⟩
  | .arrow σ τ => by
      obtain ⟨escσ, refσ⟩ := LR.escape_reflect σ
      obtain ⟨escτ, refτ⟩ := LR.escape_reflect τ
      refine ⟨fun {Δ M N} h => ?_, fun {Δ p q} h => ?_⟩
      · have h0 : LR σ (σ :: Δ) (var 0) (var 0) := refσ (Eqv.var (Δ := σ :: Δ) 0)
        exact Eqv.arrow (escτ (h (σ :: Δ) Nat.succ (RenS.succ Δ σ) _ _ h0))
      · intro Δ' ρ hρ a b hab
        exact refτ (Eqv.app (h.rename hρ) (escσ hab))

/-- **Escape**: related terms are algorithmically equivalent. -/
theorem LR.escape {τ : STy} {Δ : List STy} {M N : Tm} (h : LR τ Δ M N) : AlgEq Δ M N τ :=
  (LR.escape_reflect τ).1 h

/-- **Reflection**: structurally equivalent paths are related. -/
theorem LR.reflect {τ : STy} {Δ : List STy} {p q : Tm} (h : PathEq Δ p q τ) : LR τ Δ p q :=
  (LR.escape_reflect τ).2 h

/-- Variables are related to themselves. -/
theorem LR.var (Δ : List STy) (n : ℕ) : LR (Δ.getD n STy.base) Δ (var n) (var n) :=
  LR.reflect (Eqv.var n)

/-- **Monotonicity** of the logical relation under renamings respecting the skeletons. -/
theorem LR.rename : ∀ {τ : STy} {Δ Δ' : List STy} {M N : Tm} {ρ : ℕ → ℕ}, RenS ρ Δ Δ' →
    LR τ Δ M N → LR τ Δ' (LambdaPi.rename ρ M) (LambdaPi.rename ρ N)
  | .base, _, _, _, _, _, hρ, h => Eqv.rename h hρ
  | .arrow _ _, _, _, M, N, ρ, hρ, h => by
      intro Δ'' ρ' hρ' a b hab
      have := h Δ'' (fun n => ρ' (ρ n)) (hρ.comp hρ') a b hab
      simpa [rename_rename] using this

theorem Eqv.whExpand_left {Δ : List STy} {M M' N : Tm} (hs : WhStep M M')
    (h : AlgEq Δ M' N STy.base) : AlgEq Δ M N STy.base := by
  cases h with
  | basePath hM hN hp => exact Eqv.basePath (.head hs hM) hN hp
  | baseSort hM hN => exact Eqv.baseSort (.head hs hM) hN
  | basePi hM hN hA hB => exact Eqv.basePi (.head hs hM) hN hA hB

theorem Eqv.whExpand_right {Δ : List STy} {M N N' : Tm} (hs : WhStep N N')
    (h : AlgEq Δ M N' STy.base) : AlgEq Δ M N STy.base := by
  cases h with
  | basePath hM hN hp => exact Eqv.basePath hM (.head hs hN) hp
  | baseSort hM hN => exact Eqv.baseSort hM (.head hs hN)
  | basePi hM hN hA hB => exact Eqv.basePi hM (.head hs hN) hA hB

/-- **Closure of the logical relation under weak head expansion** (on the left). -/
theorem LR.whExpand_left : ∀ {τ : STy} {Δ : List STy} {M M' N : Tm}, WhStep M M' →
    LR τ Δ M' N → LR τ Δ M N
  | .base, _, _, _, _, hs, h => Eqv.whExpand_left hs h
  | .arrow _ _, _, _, _, _, hs, h => fun Δ' ρ hρ a b hab =>
      LR.whExpand_left (WhStep.appL a (hs.rename ρ)) (h Δ' ρ hρ a b hab)

/-- **Closure of the logical relation under weak head expansion** (on the right). -/
theorem LR.whExpand_right : ∀ {τ : STy} {Δ : List STy} {M N N' : Tm}, WhStep N N' →
    LR τ Δ M N' → LR τ Δ M N
  | .base, _, _, _, _, hs, h => Eqv.whExpand_right hs h
  | .arrow _ _, _, _, _, _, hs, h => fun Δ' ρ hρ a b hab =>
      LR.whExpand_right (WhStep.appL b (hs.rename ρ)) (h Δ' ρ hρ a b hab)

/-! ### The declarative typed equality judgement -/

/-- **Declarative typed equality** `Γ ⊢ M ≡ N : A` of `λΠ`: an equivalence relation containing
typed β and typed η, closed under the term formers, and under conversion of the type (with the
conversion of `λΠ`'s own typing rule). -/
inductive TEq : Ctx → Tm → Tm → Tm → Prop
  | refl {Γ : Ctx} {M A : Tm} : Typing Γ M A → TEq Γ M M A
  | symm {Γ : Ctx} {M N A : Tm} : TEq Γ M N A → TEq Γ N M A
  | trans {Γ : Ctx} {M N P A : Tm} : TEq Γ M N A → TEq Γ N P A → TEq Γ M P A
  | beta {Γ : Ctx} {A b a B : Tm} : Typing (A :: Γ) b B → Typing Γ a A →
      TEq Γ (app (lam A b) a) (b[a]) (B[a])
  | eta {Γ : Ctx} {f A B : Tm} : Typing Γ f (pi A B) →
      TEq Γ (lam A (app (shift f) (var 0))) f (pi A B)
  | app {Γ : Ctx} {f f' a a' A B : Tm} : TEq Γ f f' (pi A B) → TEq Γ a a' A →
      TEq Γ (app f a) (app f' a') (B[a])
  | lam {Γ : Ctx} {A A' b b' B : Tm} : TEq Γ A A' (sort Srt.star) → TEq (A :: Γ) b b' B →
      TEq Γ (lam A b) (lam A' b') (pi A B)
  | pi {Γ : Ctx} {A A' B B' : Tm} {s t : Srt} : Rule s t → TEq Γ A A' (sort s) →
      TEq (A :: Γ) B B' (sort t) → TEq Γ (pi A B) (pi A' B') (sort t)
  | conv {Γ : Ctx} {M N A B : Tm} {s : Srt} : TEq Γ M N A → Typing Γ B (sort s) → Conv A B →
      TEq Γ M N B

/-- Declaratively equal terms are βη-convertible. -/
theorem TEq.betaEtaConv {Γ : Ctx} {M N A : Tm} (h : TEq Γ M N A) : BetaEtaConv M N := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | beta => exact (BetaEtaConv.refl _).step (Or.inl (Step.beta _ _ _))
  | eta => exact betaEtaConv_eta _ _
  | app _ _ ihf iha => exact (BetaEtaConv.appL _ ihf).trans (BetaEtaConv.appR _ iha)
  | lam _ _ _ ihb => exact (BetaEtaConv.lamR _ ihb).trans (betaEtaConv_lam_annot _ _ _)
  | pi _ _ _ ihA ihB => exact (BetaEtaConv.piL _ ihA).trans (BetaEtaConv.piR _ ihB)
  | conv _ _ _ ih => exact ih

end LambdaPi
