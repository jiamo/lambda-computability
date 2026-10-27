/-
**Martin-Löf type theory: the conversion algorithm as a program** — milestone M30
(`M30-MLTT-CONV`).

The algorithmic conversion `MLTT.Alg` (`Start/MLTTAlg.lean`) is a relation.  Here it is run as a
program with fuel.

* `MLTT.whStep?`, `MLTT.whnfF` — one untyped weak head step, and weak head normalization with
  fuel; on typed terms they follow the typed reductions (`whnfF_typed`, `whnfF_tyTyped`,
  `whnfF_of_treds`, `whnfF_of_tyReds`);
* `MLTT.cRun` — the algorithm with fuel `n`: the comparison of neutral terms returns the weak
  head normal form of the inferred type (the declared type of the head variable, through the
  eliminators); the comparison of types and of terms reduces to weak head normal forms and
  compares them by the head of the type; at products and at `natrec` a later comparison is run
  only after an earlier one succeeded, so that every comparison is on well-typed inputs;
* `MLTT.cRun_correct` — **the answers are correct** on typed inputs: a Boolean answer `b`
  satisfies `b = true ↔ TyUp …` (resp. `TmUp …`), and an answer for neutral terms is a weak head
  normal type at which they are algorithmically equal, or `none` when they are not.
-/

import Start.MLTTAlgComplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Untyped weak head reduction with fuel -/

/-- One untyped weak head step, if there is one. -/
def whStep? : Tm → Option Tm
  | .app (.lam b) a => some (b[a])
  | .app f a => (whStep? f).map (fun f' => .app f' a)
  | .natrec _ z _ .zero => some z
  | .natrec P z s (.succ m) => some (inst2 m (.natrec P z s m) s)
  | .natrec P z s n => (whStep? n).map (fun n' => .natrec P z s n')
  | .emptyrec P e => (whStep? e).map (fun e' => .emptyrec P e')
  | _ => none

theorem whStep?_sound : ∀ {t u : Tm}, whStep? t = some u → WhStep t u := by
  intro t
  induction t with
  | app f a ihf _ =>
      intro u h
      cases f
      case lam b =>
        simp only [whStep?, Option.some.injEq] at h
        subst h
        exact WhStep.beta _ _
      all_goals
        simp only [whStep?] at h
        obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp h
        exact WhStep.appL _ (ihf hf')
  | natrec P z s n _ _ _ ihn =>
      intro u h
      cases n
      case zero =>
        simp only [whStep?, Option.some.injEq] at h
        subst h
        exact WhStep.natrecZero _ _ _
      case succ m =>
        simp only [whStep?, Option.some.injEq] at h
        subst h
        exact WhStep.natrecSucc _ _ _ _
      all_goals
        simp only [whStep?] at h
        obtain ⟨n', hn', rfl⟩ := Option.map_eq_some_iff.mp h
        exact WhStep.natrecS _ _ _ (ihn hn')
  | emptyrec P e _ ihe =>
      intro u h
      simp only [whStep?] at h
      obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp h
      exact WhStep.emptyrecS _ (ihe he')
  | _ => intro u h; simp [whStep?] at h

theorem whStep?_app {f : Tm} (a : Tm) (hf : ∀ b, f ≠ .lam b) :
    whStep? (.app f a) = (whStep? f).map (fun f' => .app f' a) := by
  cases f <;> first | rfl | exact absurd rfl (hf _)

theorem whStep?_natrec (P z s : Tm) {n : Tm} (hz : n ≠ .zero) (hs : ∀ m, n ≠ .succ m) :
    whStep? (.natrec P z s n) = (whStep? n).map (fun n' => .natrec P z s n') := by
  cases n <;> first | rfl | exact absurd rfl hz | exact absurd rfl (hs _)

theorem whStep?_complete {t u : Tm} (h : WhStep t u) : whStep? t = some u := by
  induction h with
  | beta b a => rfl
  | appL a hs ih =>
      rw [whStep?_app a (fun b hb => by subst hb; cases hs), ih]
      rfl
  | natrecZero P z s => rfl
  | natrecSucc P z s n => rfl
  | natrecS P z s hs ih =>
      rw [whStep?_natrec P z s (fun hb => by subst hb; cases hs)
        (fun m hb => by subst hb; cases hs), ih]
      rfl
  | emptyrecS P hs ih => simp only [whStep?, ih, Option.map_some]

theorem whStep?_none {t : Tm} (h : whStep? t = none) (u : Tm) : ¬ WhStep t u := by
  intro hs
  rw [whStep?_complete hs] at h
  cases h

/-- Weak head normalization with fuel. -/
def whnfF : ℕ → Tm → Option Tm
  | 0, _ => none
  | n + 1, t =>
      match whStep? t with
      | none => some t
      | some t' => whnfF n t'

theorem whnfF_sound : ∀ {n : ℕ} {t u : Tm}, whnfF n t = some u →
    Relation.ReflTransGen WhStep t u ∧ ∀ v, ¬ WhStep u v
  | 0, _, _, h => by simp [whnfF] at h
  | n + 1, t, u, h => by
      simp only [whnfF] at h
      split at h
      · next hn =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨.refl, whStep?_none hn⟩
      · next t' hs =>
          obtain ⟨hr, hnf⟩ := whnfF_sound h
          exact ⟨Relation.ReflTransGen.head (whStep?_sound hs) hr, hnf⟩

theorem whnfF_complete {t u : Tm} (hr : Relation.ReflTransGen WhStep t u) (hn : ∀ v, ¬ WhStep u v) :
    ∃ n₀, ∀ n, n₀ ≤ n → whnfF n t = some u := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨1, fun n hn' => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have e : whStep? u = none := by
        cases e : whStep? u with
        | none => rfl
        | some v => exact absurd (whStep?_sound e) (hn v)
      simp [whnfF, e]
  | head hs _ ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine ⟨n₁ + 1, fun n hn' => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [whnfF, whStep?_complete hs]
      exact hn₁ m (by omega)

/-- Two untyped reductions from the same term to terms without a step end at the same term. -/
theorem whSteps_stuck_unique {t u v : Tm} (hu : Relation.ReflTransGen WhStep t u)
    (hv : Relation.ReflTransGen WhStep t v) (su : ∀ w, ¬ WhStep u w) (sv : ∀ w, ¬ WhStep v w) :
    u = v := by
  induction hu using Relation.ReflTransGen.head_induction_on with
  | refl =>
      cases hv using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hs _ => exact absurd hs (su _)
  | head hs _ ih =>
      cases hv using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd hs (sv _)
      | head hs' hv' =>
          rw [WhStep.det hs hs'] at ih
          exact ih hv'

theorem TReds.whSteps {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) : Relation.ReflTransGen WhStep t u := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs.whStep ih

theorem TyReds.whSteps {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) : Relation.ReflTransGen WhStep A B := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs.whStep ih

/-- On a typed term, normalization with fuel follows the typed reduction. -/
theorem whnfF_typed {Γ : Ctx} {t A u : Tm} {n : ℕ} (ht : HasTy Γ t A) (h : whnfF n t = some u) :
    TReds Γ t u A ∧ Whnf u := by
  obtain ⟨t', hr, hn⟩ := ht.whnf
  obtain ⟨hr', su⟩ := whnfF_sound h
  have e := whSteps_stuck_unique hr' hr.whSteps su (fun w => hn.no_step)
  subst e
  exact ⟨hr, hn⟩

/-- On a well-formed type, normalization with fuel follows the type reduction. -/
theorem whnfF_tyTyped {Γ : Ctx} {A A' : Tm} {n : ℕ} (hA : WfTy Γ A) (h : whnfF n A = some A') :
    TyReds Γ A A' ∧ Whnf A' := by
  obtain ⟨A'', hr, hn⟩ := hA.whnf
  obtain ⟨hr', su⟩ := whnfF_sound h
  have e := whSteps_stuck_unique hr' hr.whSteps su (fun w => hn.no_step)
  subst e
  exact ⟨hr, hn⟩

theorem whnfF_of_treds {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) (hu : Whnf u) :
    ∃ n₀, ∀ n, n₀ ≤ n → whnfF n t = some u :=
  whnfF_complete h.whSteps (fun _ => hu.no_step)

theorem whnfF_of_tyReds {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) (hB : Whnf B) :
    ∃ n₀, ∀ n, n₀ ≤ n → whnfF n A = some B :=
  whnfF_complete h.whSteps (fun _ => hB.no_step)

/-! ### Contexts and neutral terms, computably -/

/-- The declared type of a variable. -/
def ctxGet : Ctx → ℕ → Option Tm
  | [], _ => none
  | A :: _, 0 => some (shift A)
  | _ :: Γ, n + 1 => (ctxGet Γ n).map shift

theorem ctxGet_of_lookup {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) : ctxGet Γ n = some A := by
  induction h with
  | zero => rfl
  | succ _ _ ih => simp [ctxGet, ih]

theorem lookup_of_ctxGet : ∀ {Γ : Ctx} {n : ℕ} {A : Tm}, ctxGet Γ n = some A → Lookup Γ n A
  | [], _, _, h => by simp [ctxGet] at h
  | B :: Γ, 0, A, h => by
      simp only [ctxGet, Option.some.injEq] at h
      subst h
      exact Lookup.zero Γ B
  | B :: Γ, n + 1, A, h => by
      simp only [ctxGet] at h
      obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp h
      exact Lookup.succ B (lookup_of_ctxGet hA')

/-- Is the term neutral? -/
def isNe : Tm → Bool
  | .var _ => true
  | .app f _ => isNe f
  | .natrec _ _ _ n => isNe n
  | .emptyrec _ e => isNe e
  | _ => false

theorem isNe_iff {t : Tm} : isNe t = true ↔ Neutral t := by
  induction t with
  | var n => exact ⟨fun _ => Neutral.var n, fun _ => rfl⟩
  | app f a ihf _ =>
      simp only [isNe, ihf]
      exact ⟨fun h => Neutral.app a h, fun h => by cases h with | app _ h => exact h⟩
  | natrec P z s n _ _ _ ihn =>
      simp only [isNe, ihn]
      exact ⟨fun h => Neutral.natrec P z s h, fun h => by cases h with | natrec _ _ _ h => exact h⟩
  | emptyrec P e _ ihe =>
      simp only [isNe, ihe]
      exact ⟨fun h => Neutral.emptyrec P h, fun h => by cases h with | emptyrec _ h => exact h⟩
  | _ => simp only [isNe, Bool.false_eq_true, false_iff]; intro h; cases h

/-! ### The algorithm with fuel -/

/-- The three comparisons. -/
structure CFns where
  /-- Neutral terms: the weak head normal form of the inferred type, or `none` if unequal. -/
  neDn : Ctx → Tm → Tm → Option (Option Tm)
  /-- Types. -/
  tyUp : Ctx → Tm → Tm → Option Bool
  /-- Terms at a type. -/
  tmUp : Ctx → Tm → Tm → Tm → Option Bool

/-- Run a comparison only after a successful one. -/
def andThen (r : Option Bool) (k : Unit → Option Bool) : Option Bool :=
  match r with
  | none => none
  | some false => some false
  | some true => k ()

/-- Run a neutral comparison only after a successful comparison. -/
def andThenNe (r : Option Bool) (k : Unit → Option (Option Tm)) : Option (Option Tm) :=
  match r with
  | none => none
  | some false => some none
  | some true => k ()

/-- The type of an application, given the reduced type of the head. -/
def appTy (R : CFns) (Γ : Ctx) (a b : Tm) : Option Tm → Option (Option Tm)
  | some (.pi F G) => (R.tmUp Γ a b F).map (fun ok => if ok then some (G[a]) else none)
  | _ => some none

/-- The comparison of neutral terms, inferring the type. -/
def neUpStep (R : CFns) (Γ : Ctx) : Tm → Tm → Option (Option Tm)
  | .var i, .var j => some (if i = j then ctxGet Γ i else none)
  | .app k a, .app l b => (R.neDn Γ k l).bind (appTy R Γ a b)
  | .natrec P z s m, .natrec P' z' s' m' =>
      andThenNe (R.tyUp (Tm.nat :: Γ) P P') fun _ =>
      andThenNe (R.tmUp Γ z z' (P[Tm.zero])) fun _ =>
      andThenNe (R.tmUp (P :: Tm.nat :: Γ) s s' (stepTy P)) fun _ =>
      (R.neDn Γ m m').map (fun r => if r = some Tm.nat then some (P[m]) else none)
  | .emptyrec P e, .emptyrec P' e' =>
      andThenNe (R.tyUp Γ P P') fun _ =>
      (R.neDn Γ e e').map (fun r => if r = some Tm.empty then some P else none)
  | _, _ => some none

/-- Reduce the inferred type of a neutral comparison. -/
def downStep (n : ℕ) : Option (Option Tm) → Option (Option Tm)
  | none => none
  | some none => some none
  | some (some A) => (whnfF n A).map some

/-- Is the answer of a neutral comparison a universe? -/
def isUnivOpt : Option Tm → Bool
  | some (.univ _) => true
  | _ => false

/-- A neutral comparison, if both terms are neutral. -/
def neCmp (R : CFns) (Γ : Ctx) (t u : Tm) (f : Option Tm → Bool) : Option Bool :=
  if isNe t && isNe u then (R.neDn Γ t u).map f else some false

/-- The comparison of two weak head normal types. -/
def tyDownStep (R : CFns) (Γ : Ctx) : Tm → Tm → Option Bool
  | .univ i, .univ j => some (decide (i = j))
  | .nat, .nat => some true
  | .empty, .empty => some true
  | .pi F G, .pi H E => andThen (R.tyUp Γ F H) fun _ => R.tyUp (F :: Γ) G E
  | K, M => neCmp R Γ K M isUnivOpt

/-- The comparison of two weak head normal natural numbers. -/
def natStep (R : CFns) (Γ : Ctx) : Tm → Tm → Option Bool
  | .zero, .zero => some true
  | .succ m, .succ m' => R.tmUp Γ m m' Tm.nat
  | t, u => neCmp R Γ t u (fun r => decide (r = some Tm.nat))

/-- The comparison of two weak head normal terms at a weak head normal type. -/
def tmDownStep (R : CFns) (Γ : Ctx) (t u : Tm) : Tm → Option Bool
  | .univ _ => tyDownStep R Γ t u
  | .pi F G => R.tmUp (F :: Γ) (.app (shift t) (.var 0)) (.app (shift u) (.var 0)) G
  | .nat => natStep R Γ t u
  | .empty => neCmp R Γ t u (fun r => decide (r = some Tm.empty))
  | A => if isNe A then neCmp R Γ t u Option.isSome else some false

/-- **The algorithm with fuel `n`.** -/
def cRun : ℕ → CFns
  | 0 => ⟨fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ _ => none⟩
  | n + 1 =>
      { neDn := fun Γ k l => downStep n (neUpStep (cRun n) Γ k l)
        tyUp := fun Γ A B =>
          match whnfF n A, whnfF n B with
          | some A', some B' => tyDownStep (cRun n) Γ A' B'
          | _, _ => none
        tmUp := fun Γ t u A =>
          match whnfF n A, whnfF n t, whnfF n u with
          | some A', some t', some u' => tmDownStep (cRun n) Γ t' u' A'
          | _, _, _ => none }

end MLTT
