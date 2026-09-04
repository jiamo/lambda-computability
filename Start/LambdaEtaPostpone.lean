/-
η-postponement for the untyped λ-calculus.

`Start/LambdaBetaEta.lean` proves that βη-reduction of untyped terms is confluent.  This module
proves the sharper structural fact: **η can always be postponed**.  If `t` βη-reduces to `u`, then
the reduction can be rearranged so that all β-steps come first and all η-steps last,

```
t  ⟶β*  m  ⟶η*  u,
```

which is `Lambda.betaEtaReduces_iff` — the βη-reduction relation is exactly the composite
`β* ∘ η*`, the relation that `Start/LambdaBetaEta.lean` had to close under transitivity in order
to run the Hindley–Rosen argument.  One consequence is recorded: a term that β-reduces only to
itself cannot acquire a β-reduct through η, so all of its βη-reducts are η-reducts
(`Lambda.etaReduces_of_betaEtaReduces_of_betaNf`).

The proof goes through a *parallel* η-reduction `Lambda.etaPar`, which contracts a whole family
of η-redexes at once.  The point is the local diagram: a parallel η-step followed by one β-step
can be replaced by β-steps followed by a single parallel η-step
(`Lambda.etaPar_postpone_step`) — this is what fails for the plain one-step η, because a β-redex
may be created by a *tower* of η-expansions.

* `Lambda.etaPar` — parallel η-reduction, with `Lambda.etaPar.refl`,
  `Lambda.etaStep.toEtaPar`, `Lambda.etaPar.toEtaReduces`;
* `Lambda.etaPar_lift`, `Lambda.etaPar_subst` — it is stable under lifting and substitution;
* `Lambda.etaPar_lam_app_reduces` — if `f` parallel-η-reduces to an abstraction `lam c`, then
  `app f a` β-reduces to a substitution instance of a term that parallel-η-reduces to `c`;
* `Lambda.etaPar_postpone_step`, `Lambda.etaPar_postpone_reduces`, `Lambda.etaReduces_postpone` —
  the postponement diagrams;
* `Lambda.betaEtaReduces_iff` — **βη-reduction is `β*` followed by `η*`**.
-/

import Start.LambdaBetaEta

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-! ### Parallel η-reduction -/

/-- Parallel η-reduction: contract any family of η-redexes in one step.  The last rule is the
η-rule itself, allowing a further parallel contraction inside the function part. -/
inductive etaPar : Lambda → Lambda → Prop
  | var (n : ℕ) : etaPar (Lambda.var n) (Lambda.var n)
  | app {f f' a a' : Lambda} : etaPar f f' → etaPar a a' →
      etaPar (Lambda.app f a) (Lambda.app f' a')
  | lam {b b' : Lambda} : etaPar b b' → etaPar (Lambda.lam b) (Lambda.lam b')
  | eta {f f' : Lambda} : etaPar f f' →
      etaPar (Lambda.lam (Lambda.app (Lambda.lift 1 0 f) (Lambda.var 0))) f'

theorem etaPar.refl (t : Lambda) : etaPar t t := by
  induction t with
  | var n => exact etaPar.var n
  | app f a ihf iha => exact etaPar.app ihf iha
  | lam b ihb => exact etaPar.lam ihb

/-- One η-step is a parallel η-step. -/
theorem etaStep.toEtaPar {t u : Lambda} (h : etaStep t u) : etaPar t u := by
  induction h with
  | eta s => exact etaPar.eta (etaPar.refl s)
  | app_left a _ ih => exact etaPar.app ih (etaPar.refl a)
  | app_right f _ ih => exact etaPar.app (etaPar.refl f) ih
  | lam _ ih => exact etaPar.lam ih

/-- A parallel η-step is a sequence of η-steps. -/
theorem etaPar.toEtaReduces {t u : Lambda} (h : etaPar t u) : etaReduces t u := by
  induction h with
  | var n => exact etaReduces.refl _
  | app _ _ ihf iha => exact etaReduces.app ihf iha
  | lam _ ihb => exact etaReduces.lam ihb
  | @eta f f' _ ih =>
      exact (etaReduces.lam (etaReduces.app_left _ (etaReduces_lift ih 1 0))).tail
        (etaStep.eta f')

/-! ### Stability under lifting and substitution -/

/-- Parallel η-reduction is stable under lifting. -/
theorem etaPar_lift {t t' : Lambda} (h : etaPar t t') (n k : ℕ) :
    etaPar (Lambda.lift n k t) (Lambda.lift n k t') := by
  induction h generalizing k with
  | var m => exact etaPar.refl _
  | app _ _ ihf iha => exact etaPar.app (ihf k) (iha k)
  | lam _ ihb => exact etaPar.lam (ihb (k + 1))
  | @eta f f' _ ih =>
      have hkey : Lambda.lift n (k + 1) (Lambda.lift 1 0 f)
          = Lambda.lift 1 0 (Lambda.lift n k f) := lift_succ_lift_zero n k f
      have h0 : Lambda.lift n (k + 1) (Lambda.var 0) = Lambda.var 0 := by simp
      change etaPar (Lambda.lam (Lambda.app _ _)) _
      rw [hkey, h0]
      exact etaPar.eta (ih k)

/-- Parallel η-reduction is stable under substitution, on both sides. -/
theorem etaPar_subst : ∀ {b b' : Lambda}, etaPar b b' → ∀ {a a' : Lambda} (x : ℕ), etaPar a a' →
    etaPar (Lambda.subst a x b) (Lambda.subst a' x b') := by
  intro b b' h
  induction h with
  | var m =>
      intro a a' x ha
      simp only [Lambda.subst]
      split_ifs
      · exact ha
      · exact etaPar.refl _
      · exact etaPar.refl _
  | app _ _ ihf iha =>
      intro a a' x ha
      exact etaPar.app (ihf x ha) (iha x ha)
  | lam _ ihb =>
      intro a a' x ha
      exact etaPar.lam (ihb (x + 1) (etaPar_lift ha 1 0))
  | @eta f f' _ ih =>
      intro a a' x ha
      have hkey : Lambda.subst (Lambda.lift 1 0 a) (x + 1) (Lambda.lift 1 0 f)
          = Lambda.lift 1 0 (Lambda.subst a x f) :=
        (Lambda.lift_subst f a 1 0 x (Nat.zero_le x)).symm
      have h0 : Lambda.subst (Lambda.lift 1 0 a) (x + 1) (Lambda.var 0) = Lambda.var 0 := by
        simp [Lambda.subst]
      change etaPar (Lambda.lam (Lambda.app _ _)) _
      rw [hkey, h0]
      exact etaPar.eta (ih x ha)

/-! ### β-redexes created by η -/

/-- If `f` parallel-η-reduces to an abstraction, then applying `f` to an argument β-reduces to a
substitution instance: the β-redex that η created was already there, behind a tower of
η-expansions. -/
theorem etaPar_lam_app_reduces_aux : ∀ {f g : Lambda}, etaPar f g → ∀ {c : Lambda},
    g = Lambda.lam c → ∀ a : Lambda,
      ∃ b, Lambda.reduces (Lambda.app f a) (Lambda.subst a 0 b) ∧ etaPar b c := by
  intro f g h
  induction h with
  | var n => intro c hc; exact absurd hc (by simp)
  | app _ _ _ _ => intro c hc; exact absurd hc (by simp)
  | @lam b b' hb _ =>
      intro c hc a
      simp only [Lambda.lam.injEq] at hc
      subst hc
      exact ⟨b, Lambda.reduces.step _ _ _ (Lambda.step.beta b a) (Lambda.reduces.refl _), hb⟩
  | @eta f₀ g₀ _ ih =>
      intro c hc a
      obtain ⟨b, hb₁, hb₂⟩ := ih hc a
      refine ⟨b, ?_, hb₂⟩
      refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ a) ?_
      have hred : Lambda.subst a 0 (Lambda.app (Lambda.lift 1 0 f₀) (Lambda.var 0))
          = Lambda.app f₀ a := by
        simp [Lambda.subst, Lambda.subst_lift]
      rw [hred]
      exact hb₁

theorem etaPar_lam_app_reduces {f c : Lambda} (h : etaPar f (Lambda.lam c)) (a : Lambda) :
    ∃ b, Lambda.reduces (Lambda.app f a) (Lambda.subst a 0 b) ∧ etaPar b c :=
  etaPar_lam_app_reduces_aux h rfl a

/-! ### Postponement -/

/-- Inversion for a β-step out of an abstraction. -/
theorem step_lam_inv {b w : Lambda} (h : Lambda.step (Lambda.lam b) w) :
    ∃ b', Lambda.step b b' ∧ w = Lambda.lam b' := by
  cases h with
  | lam _ b' hb => exact ⟨b', hb, rfl⟩

/-- **Local postponement**: a parallel η-step followed by a β-step is β-steps followed by a
parallel η-step. -/
theorem etaPar_postpone_step : ∀ {t v : Lambda}, etaPar t v → ∀ {w : Lambda}, Lambda.step v w →
    ∃ m, Lambda.reduces t m ∧ etaPar m w := by
  intro t v h
  induction h with
  | var n => intro w hw; exact absurd hw step.var_inv
  | @app f f' a a' hf ha ihf iha =>
      intro w hw
      rcases step_app_inv hw with ⟨c, hc, hwc⟩ | ⟨g, hg, hwg⟩ | ⟨a₂, ha₂, hwa⟩
      · subst hc
        obtain ⟨b, hb₁, hb₂⟩ := etaPar_lam_app_reduces hf a
        subst hwc
        exact ⟨Lambda.subst a 0 b, hb₁, etaPar_subst hb₂ 0 ha⟩
      · obtain ⟨m₁, hm₁, hm₂⟩ := ihf hg
        subst hwg
        exact ⟨Lambda.app m₁ a, Lambda.reduces_app_left hm₁, etaPar.app hm₂ ha⟩
      · obtain ⟨m₁, hm₁, hm₂⟩ := iha ha₂
        subst hwa
        exact ⟨Lambda.app f m₁, Lambda.reduces_app_right hm₁, etaPar.app hf hm₂⟩
  | @lam b b' _ ihb =>
      intro w hw
      obtain ⟨c, hc, rfl⟩ := step_lam_inv hw
      obtain ⟨m₁, hm₁, hm₂⟩ := ihb hc
      exact ⟨Lambda.lam m₁, Lambda.reduces_lam hm₁, etaPar.lam hm₂⟩
  | @eta f f' _ ih =>
      intro w hw
      obtain ⟨m₁, hm₁, hm₂⟩ := ih hw
      refine ⟨Lambda.lam (Lambda.app (Lambda.lift 1 0 m₁) (Lambda.var 0)), ?_, etaPar.eta hm₂⟩
      exact Lambda.reduces_lam (Lambda.reduces_app_left (Lambda.reduces_lift hm₁ 1 0))

/-- **Bridge to the abstract rewriting interface** (`Start/Rewriting.lean`): η-reduction is the
reflexive–transitive closure of an η-step. -/
theorem etaReduces_iff_star {t u : Lambda} :
    etaReduces t u ↔ Rewriting.Star etaStep t u := by
  constructor
  · intro h
    induction h with
    | refl => exact Rewriting.Star.refl t
    | tail _ hs ih => exact ih.tail hs
  · intro h
    induction h with
    | refl => exact etaReduces.refl t
    | tail _ hs ih => exact ih.tail hs

/-- A parallel η-step followed by a β-reduction is a β-reduction followed by a parallel η-step;
an instance of `Rewriting.postpone_par_star`. -/
theorem etaPar_postpone_reduces : ∀ {v w : Lambda}, Lambda.reduces v w → ∀ {t : Lambda},
    etaPar t v → ∃ m, Lambda.reduces t m ∧ etaPar m w := by
  intro v w h t ht
  obtain ⟨m, hm, hmw⟩ :=
    Rewriting.postpone_par_star
      (fun k₁ k₂ => by
        obtain ⟨m, hm, hmw⟩ := etaPar_postpone_step k₁ k₂
        exact ⟨m, Lambda.reduces_iff_star.1 hm, hmw⟩)
      (Lambda.reduces_iff_star.1 h) ht
  exact ⟨m, Lambda.reduces_iff_star.2 hm, hmw⟩

/-- **η-postponement**: an η-reduction followed by a β-reduction can be rearranged into a
β-reduction followed by an η-reduction.  An instance of `Rewriting.postpones_of_par`, with
parallel η-reduction as the parallel relation. -/
theorem etaReduces_postpone : ∀ {t v : Lambda}, etaReduces t v → ∀ {w : Lambda},
    Lambda.reduces v w → ∃ m, Lambda.reduces t m ∧ etaReduces m w := by
  have hpost : Rewriting.Postpones etaStep Lambda.step :=
    Rewriting.postpones_of_par (p := etaPar) etaStep.toEtaPar
      (fun h => etaReduces_iff_star.1 h.toEtaReduces)
      (fun k₁ k₂ => by
        obtain ⟨m, hm, hmw⟩ := etaPar_postpone_step k₁ k₂
        exact ⟨m, Lambda.reduces_iff_star.1 hm, hmw⟩)
  intro t v h w hw
  obtain ⟨m, hm, hmw⟩ :=
    Rewriting.postpone_par_star (p := Rewriting.Star etaStep)
      (fun k₁ k₂ => hpost k₁ k₂)
      (Lambda.reduces_iff_star.1 hw) (etaReduces_iff_star.1 h)
  exact ⟨m, Lambda.reduces_iff_star.2 hm, etaReduces_iff_star.2 hmw⟩

/-! ### βη-reduction factors as β then η -/

/-- **βη-reduction is `β*` followed by `η*`.** -/
theorem betaEtaReduces_iff {t u : Lambda} :
    betaEtaReduces t u ↔ ∃ m, Lambda.reduces t m ∧ etaReduces m u := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨t, Lambda.reduces.refl t, etaReduces.refl t⟩
    | @tail u₀ v _ hs ih =>
        obtain ⟨m, hm, he⟩ := ih
        cases hs with
        | beta hb =>
            obtain ⟨m', hm', he'⟩ :=
              etaReduces_postpone he (Lambda.reduces.step _ _ _ hb (Lambda.reduces.refl v))
            exact ⟨m', Lambda.reduces_trans hm hm', he'⟩
        | eta he' => exact ⟨m, hm, he.tail he'⟩
  · rintro ⟨m, hm, he⟩
    exact (betaEtaReduces.of_reduces hm).trans (betaEtaReduces.of_etaReduces he)

/-- A term with no β-reduct beyond itself cannot acquire one through η: if `t` βη-reduces to `u`
and `t` is β-normal in the strong sense that it β-reduces only to itself, then `t` η-reduces to
`u`. -/
theorem etaReduces_of_betaEtaReduces_of_betaNf {t u : Lambda}
    (hnf : ∀ m, Lambda.reduces t m → m = t) (h : betaEtaReduces t u) : etaReduces t u := by
  obtain ⟨m, hm, he⟩ := betaEtaReduces_iff.mp h
  rwa [hnf m hm] at he

end Lambda
