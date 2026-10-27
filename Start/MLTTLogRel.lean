/-
**Martin-Löf type theory: the Kripke logical relation** — milestone M30 (`M30-MLTT-LR`).

Abel, Öhman and Vezzosi define the reducibility of a type by induction-recursion: the
reducibility of a type is inductive, and the reducible equalities of its terms are defined by
recursion on that proof.  Here the recursion is moved into an index: `TyR E l Γ A I` says that
`A` is reducible at universe level `l` with **interpretation** `I`, a pair of predicates `I.tyEq`
(the types reducibly equal to `A`) and `I.tmEq` (the pairs of terms reducibly equal at `A`).
The universe levels are handled by well-founded recursion: the logical relation at level `l` is
an inductive family `TyRAt` whose universe case refers to the relations at the levels below.

* `MLTT.NatR`, `MLTT.EmptyR`, `MLTT.NeR` — reducible equality at `ℕ`, `⊥` and neutral types;
* `MLTT.TyRAt`, `MLTT.TyR` — the logical relation, for any generic equality `E`: universes
  `U l'` with `l' < l`, `ℕ`, `⊥`, neutral types, and dependent products, whose domain and
  codomain are reducible in every weakening (Kripke);
* `TyR.wfTy` — escape for types: a reducible type is well formed;
* `TyR.refl` — reflexivity of reducible type equality;
* `TyR.lift` — **cumulativity**: a type reducible at level `l` is reducible at every level above,
  with the same interpretation (so the logical relation needs no embedding constructor);
* `TyR.escapeTm` — escape for terms: reducibly equal terms are typable and generically equal.
-/

import Start.MLTTGenEq

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-- The interpretation of a reducible type. -/
structure Interp where
  /-- The types reducibly equal to the type. -/
  tyEq : Tm → Prop
  /-- The pairs of terms reducibly equal at the type. -/
  tmEq : Tm → Tm → Prop

/-- Valid weakenings of `Γ`: renamings into a well-formed context. -/
def Wk (Γ Δ : Ctx) (ρ : ℕ → ℕ) : Prop := RenOk ρ Γ Δ ∧ WfCtx Δ

/-- Reducible equality of natural numbers. -/
inductive NatR (E : GenEq) (Γ : Ctx) : Tm → Tm → Prop
  | zero {t u : Tm} : TRedsT Γ t Tm.zero Tm.nat → TRedsT Γ u Tm.zero Tm.nat → NatR E Γ t u
  | succ {t u n m : Tm} : TRedsT Γ t (succ n) Tm.nat → TRedsT Γ u (succ m) Tm.nat →
      E.tm Γ (succ n) (succ m) Tm.nat → NatR E Γ n m → NatR E Γ t u
  | ne {t u n m : Tm} : TRedsT Γ t n Tm.nat → TRedsT Γ u m Tm.nat → Neutral n → Neutral m →
      E.ne Γ n m Tm.nat → NatR E Γ t u

/-- Reducible equality at the empty type: two neutral terms. -/
def EmptyR (E : GenEq) (Γ : Ctx) (t u : Tm) : Prop :=
  ∃ n m, TRedsT Γ t n Tm.empty ∧ TRedsT Γ u m Tm.empty ∧ Neutral n ∧ Neutral m ∧
    E.ne Γ n m Tm.empty

/-- Reducible equality at a neutral type `N`: two neutral terms. -/
def NeR (E : GenEq) (Γ : Ctx) (N t u : Tm) : Prop :=
  ∃ n m, TRedsT Γ t n N ∧ TRedsT Γ u m N ∧ Neutral n ∧ Neutral m ∧ E.ne Γ n m N

/-- **The logical relation at level `l`**, given the logical relations at the levels below. -/
inductive TyRAt (E : GenEq) (l : ℕ) (lo : (l' : ℕ) → l' < l → Ctx → Tm → Interp → Prop) :
    Ctx → Tm → Interp → Prop
  | univ {Γ : Ctx} {A : Tm} {l' : ℕ} (hl : l' < l) : TyRedsT Γ A (Tm.univ l') →
      TyRAt E l lo Γ A
        { tyEq := fun B => TyRedsT Γ B (Tm.univ l')
          tmEq := fun t u => ∃ t' u', TRedsT Γ t t' (Tm.univ l') ∧ TRedsT Γ u u' (Tm.univ l') ∧
            Whnf t' ∧ Whnf u' ∧ E.tm Γ t' u' (Tm.univ l') ∧
            (∃ I, lo l' hl Γ t I ∧ I.tyEq u) ∧ (∃ J, lo l' hl Γ u J) }
  | nat {Γ : Ctx} {A : Tm} : TyRedsT Γ A Tm.nat →
      TyRAt E l lo Γ A { tyEq := fun B => TyRedsT Γ B Tm.nat, tmEq := NatR E Γ }
  | empty {Γ : Ctx} {A : Tm} : TyRedsT Γ A Tm.empty →
      TyRAt E l lo Γ A { tyEq := fun B => TyRedsT Γ B Tm.empty, tmEq := EmptyR E Γ }
  | ne {Γ : Ctx} {A N : Tm} {k : ℕ} : TyRedsT Γ A N → Neutral N → E.ne Γ N N (Tm.univ k) →
      TyRAt E l lo Γ A
        { tyEq := fun B => ∃ M, TyRedsT Γ B M ∧ Neutral M ∧ E.ty Γ N M
          tmEq := NeR E Γ N }
  | pi {Γ : Ctx} {A F G : Tm} (IF : Ctx → (ℕ → ℕ) → Interp) (IG : Ctx → (ℕ → ℕ) → Tm → Interp) :
      TyRedsT Γ A (pi F G) → WfTy Γ F → WfTy (F :: Γ) G → E.ty Γ (pi F G) (pi F G) →
      (∀ Δ ρ, Wk Γ Δ ρ → TyRAt E l lo Δ (rename ρ F) (IF Δ ρ)) →
      (∀ Δ ρ a, Wk Γ Δ ρ → (IF Δ ρ).tmEq a a →
        TyRAt E l lo Δ ((rename (upr ρ) G)[a]) (IG Δ ρ a)) →
      (∀ Δ ρ a b, Wk Γ Δ ρ → (IF Δ ρ).tmEq a a → (IF Δ ρ).tmEq b b → (IF Δ ρ).tmEq a b →
        (IG Δ ρ a).tyEq ((rename (upr ρ) G)[b])) →
      TyRAt E l lo Γ A
        { tyEq := fun B => ∃ F' G', TyRedsT Γ B (pi F' G') ∧ E.ty Γ (pi F G) (pi F' G') ∧
            (∀ Δ ρ, Wk Γ Δ ρ → (IF Δ ρ).tyEq (rename ρ F')) ∧
            (∀ Δ ρ a, Wk Γ Δ ρ → (IF Δ ρ).tmEq a a →
              (IG Δ ρ a).tyEq ((rename (upr ρ) G')[a]))
          tmEq := fun t u => ∃ f g, TRedsT Γ t f (pi F G) ∧ TRedsT Γ u g (pi F G) ∧
            Whnf f ∧ Whnf g ∧ E.tm Γ f g (pi F G) ∧
            (∀ Δ ρ a b, Wk Γ Δ ρ → (IF Δ ρ).tmEq a b →
              (IG Δ ρ a).tmEq (app (rename ρ f) a) (app (rename ρ g) b)) }

/-- **The logical relation**: `TyR E l Γ A I` — `A` is reducible at level `l` in `Γ`, with
interpretation `I`. -/
def TyR (E : GenEq) (l : ℕ) : Ctx → Tm → Interp → Prop :=
  TyRAt E l (fun l' _ => TyR E l')
termination_by l
decreasing_by all_goals omega

theorem TyR.unfold (E : GenEq) (l : ℕ) : TyR E l = TyRAt E l (fun l' _ => TyR E l') := by
  rw [TyR]

/-! ### Escape for types and reflexivity -/

/-- **Escape**: a reducible type is well formed. -/
theorem TyRAt.wfTy {E : GenEq} {l : ℕ} {lo : (l' : ℕ) → l' < l → Ctx → Tm → Interp → Prop}
    {Γ : Ctx} {A : Tm} {I : Interp} (h : TyRAt E l lo Γ A I) : WfTy Γ A := by
  cases h with
  | univ _ D => exact D.wfL
  | nat D => exact D.wfL
  | empty D => exact D.wfL
  | ne D _ _ => exact D.wfL
  | pi _ _ D _ _ _ _ _ _ => exact D.wfL

theorem TyR.wfTy {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I) :
    WfTy Γ A := by
  rw [TyR.unfold] at h
  exact h.wfTy

/-- **Reflexivity** of reducible type equality. -/
theorem TyRAt.refl {E : GenEq} {l : ℕ} {lo : (l' : ℕ) → l' < l → Ctx → Tm → Interp → Prop}
    {Γ : Ctx} {A : Tm} {I : Interp} (h : TyRAt E l lo Γ A I) : I.tyEq A := by
  induction h with
  | univ _ D => exact D
  | nat D => exact D
  | empty D => exact D
  | ne D hN hNN => exact ⟨_, D, hN, E.univ (E.ne_tm hNN)⟩
  | pi IF IG D _ _ hPi _ _ _ ihF ihG =>
      exact ⟨_, _, D, hPi, fun Δ ρ hρ => ihF Δ ρ hρ, fun Δ ρ a hρ ha => ihG Δ ρ a hρ ha⟩

theorem TyR.refl {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I) :
    I.tyEq A := by
  rw [TyR.unfold] at h
  exact h.refl

/-! ### Cumulativity -/

/-- **Cumulativity of the logical relation.** -/
theorem TyR.lift {E : GenEq} {l l₂ : ℕ} (hl : l ≤ l₂) {Γ : Ctx} {A : Tm} {I : Interp}
    (h : TyR E l Γ A I) : TyR E l₂ Γ A I := by
  rw [TyR.unfold] at h ⊢
  induction h with
  | univ hl' D => exact TyRAt.univ (lt_of_lt_of_le hl' hl) D
  | nat D => exact TyRAt.nat D
  | empty D => exact TyRAt.empty D
  | ne D hN hNN => exact TyRAt.ne D hN hNN
  | pi IF IG D hF hG hPi _ _ hext ihF ihG =>
      exact TyRAt.pi IF IG D hF hG hPi (fun Δ ρ hρ => ihF Δ ρ hρ)
        (fun Δ ρ a hρ ha => ihG Δ ρ a hρ ha) hext

/-! ### Escape for terms -/

theorem NatR.escape {E : GenEq} {Γ : Ctx} {t u : Tm} (h : NatR E Γ t u) :
    HasTy Γ t Tm.nat ∧ HasTy Γ u Tm.nat ∧ E.tm Γ t u Tm.nat := by
  have hN : ∀ {Γ : Ctx}, WfCtx Γ → TyRedsT Γ Tm.nat Tm.nat := fun hΓ =>
    TyRedsT.refl (Der.natT hΓ)
  induction h with
  | zero ht hu =>
      exact ⟨ht.tyL, hu.tyL, E.tm_red (hN ht.tyL.wf) ht hu Whnf.nat Whnf.zero Whnf.zero
        (E.zero_refl ht.tyL.wf)⟩
  | succ ht hu hsm _ _ =>
      exact ⟨ht.tyL, hu.tyL, E.tm_red (hN ht.tyL.wf) ht hu Whnf.nat (Whnf.succ _) (Whnf.succ _)
        hsm⟩
  | ne ht hu hn hm hnm =>
      exact ⟨ht.tyL, hu.tyL, E.tm_red (hN ht.tyL.wf) ht hu Whnf.nat (Whnf.ne hn) (Whnf.ne hm)
        (E.ne_tm hnm)⟩

/-- **Escape for terms**: reducibly equal terms are typable and generically equal. -/
theorem TyRAt.escapeTm {E : GenEq} {l : ℕ} {lo : (l' : ℕ) → l' < l → Ctx → Tm → Interp → Prop}
    {Γ : Ctx} {A : Tm} {I : Interp} (h : TyRAt E l lo Γ A I) {t u : Tm} (htu : I.tmEq t u) :
    HasTy Γ t A ∧ HasTy Γ u A ∧ E.tm Γ t u A := by
  cases h with
  | univ hl D =>
      obtain ⟨t', u', ht, hu, hnt, hnu, htu', -, -⟩ := htu
      have hc := Der.symmT D.tyEq
      exact ⟨Der.conv ht.tyL hc, Der.conv hu.tyL hc,
        E.tm_red D ht hu (Whnf.univ _) hnt hnu htu'⟩
  | nat D =>
      obtain ⟨ht, hu, he⟩ := NatR.escape htu
      have hc := Der.symmT D.tyEq
      exact ⟨Der.conv ht hc, Der.conv hu hc, E.tm_conv he hc⟩
  | empty D =>
      obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := htu
      have hc := Der.symmT D.tyEq
      exact ⟨Der.conv ht.tyL hc, Der.conv hu.tyL hc,
        E.tm_red D ht hu Whnf.empty (Whnf.ne hn) (Whnf.ne hm) (E.ne_tm hnm)⟩
  | ne D hN _ =>
      obtain ⟨n, m, ht, hu, hn, hm, hnm⟩ := htu
      have hc := Der.symmT D.tyEq
      exact ⟨Der.conv ht.tyL hc, Der.conv hu.tyL hc,
        E.tm_red D ht hu (Whnf.ne hN) (Whnf.ne hn) (Whnf.ne hm) (E.ne_tm hnm)⟩
  | pi IF IG D _ _ _ _ _ _ =>
      obtain ⟨f, g, ht, hu, hnf, hng, hfg, -⟩ := htu
      have hc := Der.symmT D.tyEq
      exact ⟨Der.conv ht.tyL hc, Der.conv hu.tyL hc,
        E.tm_red D ht hu (Whnf.pi _ _) hnf hng hfg⟩

theorem TyR.escapeTm {E : GenEq} {l : ℕ} {Γ : Ctx} {A : Tm} {I : Interp} (h : TyR E l Γ A I)
    {t u : Tm} (htu : I.tmEq t u) : HasTy Γ t A ∧ HasTy Γ u A ∧ E.tm Γ t u A := by
  rw [TyR.unfold] at h
  exact h.escapeTm htu

end MLTT
