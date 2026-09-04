/-
η-postponement for `λΠ`, and strong normalization of `βη`.

`Start/LambdaPiEta.lean` adds η-reduction to the dependently typed calculus and shows that the raw
rewriting system `β ∪ η` is *not* confluent (Nederpelt's counterexample, which turns on the domain
annotation of an abstraction).  This module proves the structural fact that survives the
counterexample: **η can always be postponed**.  If `t` βη-reduces to `u`, then the reduction can be
rearranged so that every β-step comes before every η-step,

```
t  ⟶β*  m  ⟶η*  u,
```

which is `LambdaPi.betaEtaRed_iff`.  The proof is the parallel-η argument of
`Start/LambdaEtaPostpone.lean`, transported to `λΠ`: the local diagram fails for the plain
one-step η, because a β-redex may be created by a whole tower of η-expansions, and a *parallel*
η-step contracts such a tower in one go.

The payoff is at the typing layer.  β-strong normalization of `λΠ` is
`LambdaPi.Typing.sn`; η-reduction decreases the size of a term; and postponement is exactly what
glues the two together, so that a typable term admits no infinite βη-reduction at all
(`LambdaPi.Typing.betaEta_sn`) and has a βη-normal form (`LambdaPi.Typing.hasBetaEtaNormalForm`).

* `LambdaPi.SRed` — a reduction with at least one β-step, and its congruences;
* `LambdaPi.EtaPar` — parallel η-reduction, with `EtaPar.refl`, `EtaStep.toEtaPar`,
  `EtaPar.toEtaRed`, and stability under renaming and substitution (`EtaPar.rename`,
  `EtaPar.substs`);
* `LambdaPi.EtaPar.lam_app_sred` — if `f` parallel-η-reduces to an abstraction `lam A c`, then
  `app f a` β-reduces, in at least one step, to a substitution instance of a term that
  parallel-η-reduces to `c`;
* `LambdaPi.EtaPar.postpone_step`, `LambdaPi.EtaRed.postpone`, `LambdaPi.betaEta_postpone` — the
  postponement diagrams, and `LambdaPi.betaEtaRed_iff`: **βη-reduction is `β*` then `η*`**;
* `LambdaPi.SNBetaEta`, `LambdaPi.snBetaEta_of_sn` — a β-strongly normalizing term is βη-strongly
  normalizing, and `LambdaPi.Typing.betaEta_sn`, `LambdaPi.Typing.hasBetaEtaNormalForm`.
-/

import Start.LambdaPiEta
import Start.LambdaPiSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Reductions with at least one step -/

/-- `SRed t u` is a β-reduction from `t` to `u` using at least one step. -/
def SRed (t u : Tm) : Prop := ∃ m, Step t m ∧ Red m u

/-- A nonempty β-reduction can be split off at the head. -/
theorem Red.head_split : ∀ {t u : Tm}, Red t u → ∀ {v : Tm}, Step u v →
    ∃ t₁, Step t t₁ ∧ Red t₁ v := by
  intro t u h
  induction h with
  | refl => intro v hv; exact ⟨v, hv, Red.refl v⟩
  | tail _ hs ih =>
      intro v hv
      obtain ⟨t₁, ht₁, ht₁u⟩ := ih hs
      exact ⟨t₁, ht₁, ht₁u.tail hv⟩

theorem SRed.ofStep {t u : Tm} (h : Step t u) : SRed t u := ⟨u, h, Red.refl u⟩

theorem SRed.red {t u : Tm} (h : SRed t u) : Red t u := Red.head h.choose_spec.1 h.choose_spec.2

theorem SRed.trans_right {t u v : Tm} (h : SRed t u) (h' : Red u v) : SRed t v := by
  obtain ⟨m, hm, hmu⟩ := h
  exact ⟨m, hm, hmu.trans h'⟩

theorem SRed.trans_left {t u v : Tm} (h : Red t u) (h' : SRed u v) : SRed t v := by
  obtain ⟨m, hm, hmv⟩ := h'
  obtain ⟨t₁, ht₁, ht₁m⟩ := Red.head_split h hm
  exact ⟨t₁, ht₁, ht₁m.trans hmv⟩

theorem SRed.appL {f f' : Tm} (a : Tm) (h : SRed f f') : SRed (app f a) (app f' a) := by
  obtain ⟨m, hm, hmf⟩ := h
  exact ⟨app m a, Step.appL a hm, Red.appL a hmf⟩

theorem SRed.appR (f : Tm) {a a' : Tm} (h : SRed a a') : SRed (app f a) (app f a') := by
  obtain ⟨m, hm, hma⟩ := h
  exact ⟨app f m, Step.appR f hm, Red.appR f hma⟩

theorem SRed.lamL {A A' : Tm} (b : Tm) (h : SRed A A') : SRed (lam A b) (lam A' b) := by
  obtain ⟨m, hm, hmA⟩ := h
  exact ⟨lam m b, Step.lamL b hm, Red.lamL b hmA⟩

theorem SRed.lamR (A : Tm) {b b' : Tm} (h : SRed b b') : SRed (lam A b) (lam A b') := by
  obtain ⟨m, hm, hmb⟩ := h
  exact ⟨lam A m, Step.lamR A hm, Red.lamR A hmb⟩

theorem SRed.piL {A A' : Tm} (B : Tm) (h : SRed A A') : SRed (pi A B) (pi A' B) := by
  obtain ⟨m, hm, hmA⟩ := h
  exact ⟨pi m B, Step.piL B hm, Red.piL B hmA⟩

theorem SRed.piR (A : Tm) {B B' : Tm} (h : SRed B B') : SRed (pi A B) (pi A B') := by
  obtain ⟨m, hm, hmB⟩ := h
  exact ⟨pi A m, Step.piR A hm, Red.piR A hmB⟩

theorem SRed.rename {t t' : Tm} (h : SRed t t') (ρ : ℕ → ℕ) :
    SRed (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  obtain ⟨m, hm, hmt⟩ := h
  exact ⟨LambdaPi.rename ρ m, hm.rename ρ, hmt.rename ρ⟩

/-! ### Congruences for η-reduction -/

namespace EtaRed

theorem appL {f f' : Tm} (a : Tm) (h : EtaRed f f') : EtaRed (app f a) (app f' a) := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (EtaStep.appL a hs)

theorem appR (f : Tm) {a a' : Tm} (h : EtaRed a a') : EtaRed (app f a) (app f a') := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (EtaStep.appR f hs)

theorem lamL {A A' : Tm} (b : Tm) (h : EtaRed A A') : EtaRed (lam A b) (lam A' b) := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (EtaStep.lamL b hs)

theorem lamR (A : Tm) {b b' : Tm} (h : EtaRed b b') : EtaRed (lam A b) (lam A b') := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (EtaStep.lamR A hs)

theorem piL {A A' : Tm} (B : Tm) (h : EtaRed A A') : EtaRed (pi A B) (pi A' B) := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (EtaStep.piL B hs)

theorem piR (A : Tm) {B B' : Tm} (h : EtaRed B B') : EtaRed (pi A B) (pi A B') := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (EtaStep.piR A hs)

theorem app {f f' a a' : Tm} (hf : EtaRed f f') (ha : EtaRed a a') :
    EtaRed (Tm.app f a) (Tm.app f' a') := (appL a hf).trans (appR f' ha)

theorem lam {A A' b b' : Tm} (hA : EtaRed A A') (hb : EtaRed b b') :
    EtaRed (Tm.lam A b) (Tm.lam A' b') := (lamL b hA).trans (lamR A' hb)

theorem pi {A A' B B' : Tm} (hA : EtaRed A A') (hB : EtaRed B B') :
    EtaRed (Tm.pi A B) (Tm.pi A' B') := (piL B hA).trans (piR A' hB)

theorem rename {t t' : Tm} (h : EtaRed t t') (ρ : ℕ → ℕ) :
    EtaRed (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h with
  | refl => exact EtaRed.refl _
  | tail _ hs ih => exact ih.tail (hs.rename ρ)

end EtaRed

/-! ### Parallel η-reduction -/

/-- Parallel η-reduction: contract a whole family of η-redexes at once.  The last rule is the
η-rule itself, which allows a further parallel contraction inside the function part; as in the
one-step rule, the domain annotation of the contracted abstraction is discarded. -/
inductive EtaPar : Tm → Tm → Prop
  | var (n : ℕ) : EtaPar (Tm.var n) (Tm.var n)
  | sort (s : Srt) : EtaPar (Tm.sort s) (Tm.sort s)
  | app {f f' a a' : Tm} : EtaPar f f' → EtaPar a a' → EtaPar (Tm.app f a) (Tm.app f' a')
  | lam {A A' b b' : Tm} : EtaPar A A' → EtaPar b b' → EtaPar (Tm.lam A b) (Tm.lam A' b')
  | pi {A A' B B' : Tm} : EtaPar A A' → EtaPar B B' → EtaPar (Tm.pi A B) (Tm.pi A' B')
  | eta (A : Tm) {f f' : Tm} : EtaPar f f' →
      EtaPar (Tm.lam A (Tm.app (shift f) (Tm.var 0))) f'

theorem EtaPar.refl (t : Tm) : EtaPar t t := by
  induction t with
  | var n => exact EtaPar.var n
  | sort s => exact EtaPar.sort s
  | app f a ihf iha => exact EtaPar.app ihf iha
  | lam A b ihA ihb => exact EtaPar.lam ihA ihb
  | pi A B ihA ihB => exact EtaPar.pi ihA ihB

/-- One η-step is a parallel η-step. -/
theorem EtaStep.toEtaPar {t u : Tm} (h : EtaStep t u) : EtaPar t u := by
  induction h with
  | eta A t => exact EtaPar.eta A (EtaPar.refl t)
  | appL a _ ih => exact EtaPar.app ih (EtaPar.refl _)
  | appR f _ ih => exact EtaPar.app (EtaPar.refl f) ih
  | lamL b _ ih => exact EtaPar.lam ih (EtaPar.refl b)
  | lamR A _ ih => exact EtaPar.lam (EtaPar.refl A) ih
  | piL B _ ih => exact EtaPar.pi ih (EtaPar.refl B)
  | piR A _ ih => exact EtaPar.pi (EtaPar.refl A) ih

/-- A parallel η-step is a sequence of η-steps. -/
theorem EtaPar.toEtaRed {t u : Tm} (h : EtaPar t u) : EtaRed t u := by
  induction h with
  | var n => exact EtaRed.refl _
  | sort s => exact EtaRed.refl _
  | app _ _ ihf iha => exact EtaRed.app ihf iha
  | lam _ _ ihA ihb => exact EtaRed.lam ihA ihb
  | pi _ _ ihA ihB => exact EtaRed.pi ihA ihB
  | @eta A f f' _ ih =>
      exact (EtaRed.lamR A (EtaRed.appL _ (ih.rename Nat.succ))).tail (EtaStep.eta A f')

/-- Parallel η-reduction is stable under renaming. -/
theorem EtaPar.rename {t t' : Tm} (h : EtaPar t t') (ρ : ℕ → ℕ) :
    EtaPar (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h generalizing ρ with
  | var n => exact EtaPar.refl _
  | sort s => exact EtaPar.refl _
  | app _ _ ihf iha => exact EtaPar.app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact EtaPar.lam (ihA ρ) (ihb (LambdaPi.upr ρ))
  | pi _ _ ihA ihB => exact EtaPar.pi (ihA ρ) (ihB (LambdaPi.upr ρ))
  | @eta A f f' _ ih =>
      have hkey : LambdaPi.rename (LambdaPi.upr ρ) (shift f) = shift (LambdaPi.rename ρ f) := by
        simp [shift, rename_rename, LambdaPi.upr]
      have h0 : LambdaPi.rename (LambdaPi.upr ρ) (Tm.var 0) = Tm.var 0 := rfl
      change EtaPar (Tm.lam _ (Tm.app _ _)) _
      rw [hkey, h0]
      exact EtaPar.eta _ (ih ρ)

/-- A parallel substitution whose components are related by parallel η-reduction. -/
def EtaParSub (σ σ' : ℕ → Tm) : Prop := ∀ n, EtaPar (σ n) (σ' n)

theorem EtaParSub.up {σ σ' : ℕ → Tm} (h : EtaParSub σ σ') :
    EtaParSub (LambdaPi.up σ) (LambdaPi.up σ') := by
  intro n
  cases n with
  | zero => exact EtaPar.var 0
  | succ n => exact (h n).rename Nat.succ

/-- Parallel η-reduction is stable under substitution, on both sides. -/
theorem EtaPar.substs {t t' : Tm} (h : EtaPar t t') :
    ∀ {σ σ' : ℕ → Tm}, EtaParSub σ σ' → EtaPar (subst σ t) (subst σ' t') := by
  induction h with
  | var n => intro σ σ' hσ; exact hσ n
  | sort s => intro σ σ' _; exact EtaPar.refl _
  | app _ _ ihf iha => intro σ σ' hσ; exact EtaPar.app (ihf hσ) (iha hσ)
  | lam _ _ ihA ihb => intro σ σ' hσ; exact EtaPar.lam (ihA hσ) (ihb hσ.up)
  | pi _ _ ihA ihB => intro σ σ' hσ; exact EtaPar.pi (ihA hσ) (ihB hσ.up)
  | @eta A f f' _ ih =>
      intro σ σ' hσ
      have hkey : subst (LambdaPi.up σ) (shift f) = shift (subst σ f) := subst_up_shift σ f
      have h0 : subst (LambdaPi.up σ) (Tm.var 0) = Tm.var 0 := rfl
      change EtaPar (Tm.lam _ (Tm.app _ _)) _
      rw [hkey, h0]
      exact EtaPar.eta _ (ih hσ)

theorem EtaParSub.scons {a a' : Tm} (h : EtaPar a a') {σ σ' : ℕ → Tm} (hσ : EtaParSub σ σ') :
    EtaParSub (LambdaPi.scons a σ) (LambdaPi.scons a' σ') := by
  intro n
  cases n with
  | zero => exact h
  | succ n => exact hσ n

theorem EtaParSub.ids : EtaParSub LambdaPi.ids LambdaPi.ids := fun n => EtaPar.var n

theorem EtaPar.inst {b b' a a' : Tm} (hb : EtaPar b b') (ha : EtaPar a a') :
    EtaPar (b[a]) (b'[a']) := hb.substs (EtaParSub.ids.scons ha)

/-! ### β-redexes created by η -/

/-- If `f` parallel-η-reduces to an abstraction, then applying `f` to an argument β-reduces, in at
least one step, to a substitution instance: the β-redex that η created was already there, behind a
tower of η-expansions. -/
theorem EtaPar.lam_app_sred_aux : ∀ {f g : Tm}, EtaPar f g → ∀ {A c : Tm}, g = Tm.lam A c →
    ∀ a : Tm, ∃ b, SRed (Tm.app f a) (b[a]) ∧ EtaPar b c := by
  intro f g h
  induction h with
  | var n => intro A c hc; exact absurd hc (by simp)
  | sort s => intro A c hc; exact absurd hc (by simp)
  | app _ _ _ _ => intro A c hc; exact absurd hc (by simp)
  | pi _ _ _ _ => intro A c hc; exact absurd hc (by simp)
  | @lam A₀ A' b₀ b' _ hb _ _ =>
      intro A c hc a
      simp only [Tm.lam.injEq] at hc
      obtain ⟨-, hb'⟩ := hc
      subst hb'
      exact ⟨b₀, SRed.ofStep (Step.beta A₀ b₀ a), hb⟩
  | @eta A₀ f₀ g₀ _ ih =>
      intro A c hc a
      obtain ⟨b, hb₁, hb₂⟩ := ih hc a
      refine ⟨b, ?_, hb₂⟩
      refine ⟨Tm.app f₀ a, ?_, hb₁.red⟩
      have hstep : Step (Tm.app (Tm.lam A₀ (Tm.app (shift f₀) (Tm.var 0))) a)
          ((Tm.app (shift f₀) (Tm.var 0))[a]) := Step.beta _ _ a
      have hred : (Tm.app (shift f₀) (Tm.var 0))[a] = Tm.app f₀ a := by
        change Tm.app ((shift f₀)[a]) a = Tm.app f₀ a
        rw [inst_shift]
      rwa [hred] at hstep

theorem EtaPar.lam_app_sred {f A c : Tm} (h : EtaPar f (Tm.lam A c)) (a : Tm) :
    ∃ b, SRed (Tm.app f a) (b[a]) ∧ EtaPar b c :=
  EtaPar.lam_app_sred_aux h rfl a

/-! ### Postponement -/

theorem BetaEtaRed.of_red {t u : Tm} (h : Red t u) : BetaEtaRed t u := by
  induction h with
  | refl => exact BetaEtaRed.refl t
  | tail _ hs ih => exact ih.tail (Or.inl hs)

theorem BetaEtaRed.of_etaRed {t u : Tm} (h : EtaRed t u) : BetaEtaRed t u := by
  induction h with
  | refl => exact BetaEtaRed.refl t
  | tail _ hs ih => exact ih.tail (Or.inr hs)

/-- **Local postponement**: a parallel η-step followed by a β-step is at least one β-step followed
by a parallel η-step. -/
theorem EtaPar.postpone_step : ∀ {t v : Tm}, EtaPar t v → ∀ {w : Tm}, Step v w →
    ∃ m, SRed t m ∧ EtaPar m w := by
  intro t v h
  induction h with
  | var n => intro w hw; cases hw
  | sort s => intro w hw; cases hw
  | @app f f' a a' hf ha ihf iha =>
      intro w hw
      cases hw with
      | beta A b a₀ =>
          obtain ⟨b₀, hb₁, hb₂⟩ := EtaPar.lam_app_sred hf a
          exact ⟨b₀[a], hb₁, hb₂.inst ha⟩
      | appL a₀ hs =>
          obtain ⟨m₁, hm₁, hm₂⟩ := ihf hs
          exact ⟨Tm.app m₁ a, SRed.appL a hm₁, EtaPar.app hm₂ ha⟩
      | appR f₀ hs =>
          obtain ⟨m₁, hm₁, hm₂⟩ := iha hs
          exact ⟨Tm.app f m₁, SRed.appR f hm₁, EtaPar.app hf hm₂⟩
  | @lam A A' b b' hA hb ihA ihb =>
      intro w hw
      cases hw with
      | lamL b₀ hs =>
          obtain ⟨m₁, hm₁, hm₂⟩ := ihA hs
          exact ⟨Tm.lam m₁ b, SRed.lamL b hm₁, EtaPar.lam hm₂ hb⟩
      | lamR A₀ hs =>
          obtain ⟨m₁, hm₁, hm₂⟩ := ihb hs
          exact ⟨Tm.lam A m₁, SRed.lamR A hm₁, EtaPar.lam hA hm₂⟩
  | @pi A A' B B' hA hB ihA ihB =>
      intro w hw
      cases hw with
      | piL B₀ hs =>
          obtain ⟨m₁, hm₁, hm₂⟩ := ihA hs
          exact ⟨Tm.pi m₁ B, SRed.piL B hm₁, EtaPar.pi hm₂ hB⟩
      | piR A₀ hs =>
          obtain ⟨m₁, hm₁, hm₂⟩ := ihB hs
          exact ⟨Tm.pi A m₁, SRed.piR A hm₁, EtaPar.pi hA hm₂⟩
  | @eta A f f' _ ih =>
      intro w hw
      obtain ⟨m₁, hm₁, hm₂⟩ := ih hw
      refine ⟨Tm.lam A (Tm.app (shift m₁) (Tm.var 0)), ?_, EtaPar.eta A hm₂⟩
      exact SRed.lamR A (SRed.appL _ (hm₁.rename Nat.succ))

/-- **Bridges to the abstract rewriting interface** (`Start/Rewriting.lean`): η-reduction is the
closure of an η-step, a nonempty β-reduction is the transitive closure of a β-step, and
βη-reduction is the closure of the union. -/
theorem EtaRed.iff_star {t u : Tm} : EtaRed t u ↔ Rewriting.Star EtaStep t u := by
  constructor
  · intro h
    induction h with
    | refl => exact Rewriting.Star.refl t
    | tail _ hs ih => exact ih.tail hs
  · intro h
    induction h with
    | refl => exact EtaRed.refl t
    | tail _ hs ih => exact ih.tail hs

theorem SRed.iff_plus {t u : Tm} : SRed t u ↔ Rewriting.Plus Step t u := by
  constructor
  · rintro ⟨v, hv, hvu⟩
    exact Rewriting.Plus.trans_star (Rewriting.Plus.single hv) (Red.iff_star.1 hvu)
  · intro h
    obtain ⟨v, hv, hvu⟩ := h.head_split
    exact ⟨v, hv, Red.iff_star.2 hvu⟩

theorem BetaEtaRed.iff_star {t u : Tm} :
    BetaEtaRed t u ↔ Rewriting.Star (Rewriting.Alt Step EtaStep) t u := by
  constructor
  · intro h
    induction h with
    | refl => exact Rewriting.Star.refl t
    | tail _ hs ih => exact ih.tail hs
  · intro h
    induction h with
    | refl => exact BetaEtaRed.refl t
    | tail _ hs ih => exact ih.tail hs

/-- A parallel η-step followed by a β-reduction is a β-reduction followed by a parallel η-step;
an instance of `Rewriting.postpone_par_star`. -/
theorem EtaPar.postpone_red : ∀ {v w : Tm}, Red v w → ∀ {t : Tm}, EtaPar t v →
    ∃ m, Red t m ∧ EtaPar m w := by
  intro v w h t ht
  obtain ⟨m, hm, hmw⟩ :=
    Rewriting.postpone_par_star
      (fun k₁ k₂ => by
        obtain ⟨m, hm, hmw⟩ := EtaPar.postpone_step k₁ k₂
        exact ⟨m, Red.iff_star.1 hm.red, hmw⟩)
      (Red.iff_star.1 h) ht
  exact ⟨m, Red.iff_star.2 hm, hmw⟩

/-- A parallel η-step followed by a nonempty β-reduction is a nonempty β-reduction followed by a
parallel η-step. -/
theorem EtaPar.postpone_sred {t v w : Tm} (h : EtaPar t v) (hs : SRed v w) :
    ∃ m, SRed t m ∧ EtaPar m w := by
  obtain ⟨v₁, hv₁, hv₁w⟩ := hs
  obtain ⟨m₁, hm₁, hm₂⟩ := EtaPar.postpone_step h hv₁
  obtain ⟨m, hm, hmw⟩ := EtaPar.postpone_red hv₁w hm₂
  exact ⟨m, hm₁.trans_right hm, hmw⟩

/-- η postpones after β, in the vocabulary of `Start/Rewriting.lean`, in the sharp form: the
rearranged β-reduction is nonempty.  Parallel η-reduction is the parallel relation. -/
theorem postponesPlus_etaStep : Rewriting.PostponesPlus EtaStep Step :=
  Rewriting.postponesPlus_of_par (p := EtaPar) EtaStep.toEtaPar
    (fun h => EtaRed.iff_star.1 h.toEtaRed)
    (fun k₁ k₂ => by
      obtain ⟨m, hm, hmw⟩ := EtaPar.postpone_step k₁ k₂
      exact ⟨m, SRed.iff_plus.1 hm, hmw⟩)

/-- An η-reduction followed by a nonempty β-reduction is a nonempty β-reduction followed by an
η-reduction; an instance of `Rewriting.postponesPlus_of_par`. -/
theorem EtaRed.postpone_sred : ∀ {t v : Tm}, EtaRed t v → ∀ {w : Tm}, SRed v w →
    ∃ m, SRed t m ∧ EtaRed m w := by
  intro t v h w hw
  obtain ⟨v₁, hv₁, hv₁w⟩ := hw
  obtain ⟨m₁, hm₁, hm₂⟩ := postponesPlus_etaStep (EtaRed.iff_star.1 h) hv₁
  obtain ⟨m, hm, hmw⟩ :=
    Rewriting.postpone_par_star (p := Rewriting.Star EtaStep)
      (fun k₁ k₂ => postponesPlus_etaStep.toPostpones k₁ k₂)
      (Red.iff_star.1 hv₁w) hm₂
  exact ⟨m, SRed.iff_plus.2 (hm₁.trans_star hm), EtaRed.iff_star.2 hmw⟩

/-- **η-postponement**: an η-reduction followed by a β-reduction can be rearranged into a
β-reduction followed by an η-reduction.  An instance of the interface. -/
theorem EtaRed.postpone : ∀ {t v : Tm}, EtaRed t v → ∀ {w : Tm}, Red v w →
    ∃ m, Red t m ∧ EtaRed m w := by
  intro t v h w hw
  obtain ⟨m, hm, hmw⟩ :=
    Rewriting.postpone_par_star (p := Rewriting.Star EtaStep)
      (fun k₁ k₂ => postponesPlus_etaStep.toPostpones k₁ k₂)
      (Red.iff_star.1 hw) (EtaRed.iff_star.1 h)
  exact ⟨m, Red.iff_star.2 hm, EtaRed.iff_star.2 hmw⟩

/-- **βη-reduction is `β*` followed by `η*`**, an instance of
`Rewriting.star_alt_iff_of_postpones`. -/
theorem betaEtaRed_iff {t u : Tm} : BetaEtaRed t u ↔ ∃ m, Red t m ∧ EtaRed m u := by
  rw [BetaEtaRed.iff_star,
    Rewriting.star_alt_iff_of_postpones postponesPlus_etaStep.toPostpones]
  exact ⟨fun ⟨m, hm, he⟩ => ⟨m, Red.iff_star.2 hm, EtaRed.iff_star.2 he⟩,
    fun ⟨m, hm, he⟩ => ⟨m, Red.iff_star.1 hm, EtaRed.iff_star.1 he⟩⟩

/-- η-postponement in the form the name advertises: `βη` factors through `β` then `η`. -/
theorem betaEta_postpone {t u : Tm} (h : BetaEtaRed t u) : ∃ m, Red t m ∧ EtaRed m u :=
  betaEtaRed_iff.mp h

/-! ### Strong normalization of βη -/

/-- A term is **βη-strongly normalizing** when βη-reduction is well founded above it. -/
def SNBetaEta (t : Tm) : Prop := Acc (fun a b => BetaEtaStep b a) t

theorem SNBetaEta.intro {t : Tm} (h : ∀ t', BetaEtaStep t t' → SNBetaEta t') : SNBetaEta t :=
  Acc.intro t h

/-- The engine of βη-strong normalization: from a β-strongly normalizing term, every term reached
by β-steps and then η-steps is βη-strongly normalizing.  The outer induction is on the
β-accessibility of `t`, which absorbs the β-steps by postponement; the inner one is on the size,
which the η-steps decrease. -/
theorem snBetaEta_aux : ∀ {t : Tm}, SN t → ∀ (n : ℕ) {m u : Tm}, Red t m → EtaRed m u →
    size u ≤ n → SNBetaEta u := by
  intro t ht n m u hm hu hsize
  exact Rewriting.sn_alt_aux size (fun h => h.size_lt) postponesPlus_etaStep ht n
    (Red.iff_star.1 hm) (EtaRed.iff_star.1 hu) hsize

/-- A β-strongly normalizing term is βη-strongly normalizing. -/
theorem snBetaEta_of_sn {t : Tm} (h : SN t) : SNBetaEta t :=
  snBetaEta_aux h (size t) (Red.refl t) (EtaRed.refl t) le_rfl

/-- **Strong normalization of `βη` for `λΠ`**: no typable term admits an infinite βη-reduction. -/
theorem Typing.betaEta_sn {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) : SNBetaEta t :=
  snBetaEta_of_sn (h.sn hΓ)

/-- A term is **βη-normal** when no βη-step applies to it. -/
def BetaEtaNormal (t : Tm) : Prop := ∀ t', ¬ BetaEtaStep t t'

theorem hasBetaEtaNormalForm_of_snBetaEta {t : Tm} (h : SNBetaEta t) :
    ∃ u, BetaEtaRed t u ∧ BetaEtaNormal u := by
  induction h with
  | intro t _ ih =>
      by_cases hn : ∀ t', ¬ BetaEtaStep t t'
      · exact ⟨t, BetaEtaRed.refl t, hn⟩
      · obtain ⟨t', ht'⟩ := not_forall.1 hn
        replace ht' : BetaEtaStep t t' := not_not.1 ht'
        obtain ⟨u, hu, hnu⟩ := ih t' ht'
        exact ⟨u, (BetaEtaRed.single ht').trans hu, hnu⟩

/-- Every typable term of `λΠ` has a βη-normal form. -/
theorem Typing.hasBetaEtaNormalForm {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    ∃ u, BetaEtaRed t u ∧ BetaEtaNormal u :=
  hasBetaEtaNormalForm_of_snBetaEta (h.betaEta_sn hΓ)

end LambdaPi
