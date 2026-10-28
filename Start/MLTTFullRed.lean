/-
**Martin-Löf type theory: full reduction and normal forms** — milestone M30
(`M30-MLTT-WN`).

* `MLTT.FStep`, `MLTT.FSteps` — full reduction: `β` and the two computation rules of `natrec`,
  under every term former (also under binders and inside types);
* `MLTT.NfB` — normal forms (`Nf`) and neutral normal forms (`NeNf`), inductively;
* `FStep.rename`, `FStep.subst`, `FSteps.substArg` — reduction commutes with renaming and
  substitution, and substituting reducing terms reduces;
* `FStep.unrename`, `NfB.unrename` — **anti-renaming**: a step of a renamed term is the renaming
  of a step, and a renamed term is normal only if the term is;
* `MLTT.DEq.lam_cong` — congruence of abstraction, from the η rule;
* **`MLTT.FStep.deq`** — **subject reduction for full reduction**: a step of a typed term is a
  judgemental equality at its type (`FStep.tyEq` for types, `FSteps.deq`, `FSteps.tyEq`);
* `MLTT.Whnf.pi_canon` — a weak head normal term of a product type is an abstraction or neutral.
-/

import Start.MLTTInversion

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Full reduction -/

/-- **Full reduction**, one step. -/
inductive FStep : Tm → Tm → Prop
  | beta (b a : Tm) : FStep (app (lam b) a) (b[a])
  | natrecZero (P z s : Tm) : FStep (natrec P z s zero) z
  | natrecSucc (P z s n : Tm) : FStep (natrec P z s (succ n)) (inst2 n (natrec P z s n) s)
  | piL {F F' : Tm} (G : Tm) : FStep F F' → FStep (pi F G) (pi F' G)
  | piR (F : Tm) {G G' : Tm} : FStep G G' → FStep (pi F G) (pi F G')
  | lam {b b' : Tm} : FStep b b' → FStep (lam b) (lam b')
  | appL {f f' : Tm} (a : Tm) : FStep f f' → FStep (app f a) (app f' a)
  | appR (f : Tm) {a a' : Tm} : FStep a a' → FStep (app f a) (app f a')
  | succ {n n' : Tm} : FStep n n' → FStep (succ n) (succ n')
  | natrecP {P P' : Tm} (z s n : Tm) : FStep P P' → FStep (natrec P z s n) (natrec P' z s n)
  | natrecZ (P : Tm) {z z' : Tm} (s n : Tm) : FStep z z' → FStep (natrec P z s n) (natrec P z' s n)
  | natrecS (P z : Tm) {s s' : Tm} (n : Tm) : FStep s s' →
      FStep (natrec P z s n) (natrec P z s' n)
  | natrecN (P z s : Tm) {n n' : Tm} : FStep n n' → FStep (natrec P z s n) (natrec P z s n')
  | emptyrecP {P P' : Tm} (e : Tm) : FStep P P' → FStep (emptyrec P e) (emptyrec P' e)
  | emptyrecE (P : Tm) {e e' : Tm} : FStep e e' → FStep (emptyrec P e) (emptyrec P e')

/-- Full reduction, many steps. -/
abbrev FSteps : Tm → Tm → Prop := Relation.ReflTransGen FStep

theorem WhStep.fstep {t u : Tm} (h : WhStep t u) : FStep t u := by
  induction h with
  | beta b a => exact FStep.beta b a
  | appL a _ ih => exact FStep.appL a ih
  | natrecZero P z s => exact FStep.natrecZero P z s
  | natrecSucc P z s n => exact FStep.natrecSucc P z s n
  | natrecS P z s _ ih => exact FStep.natrecN P z s ih
  | emptyrecS P _ ih => exact FStep.emptyrecE P ih

theorem TReds.fsteps {Γ : Ctx} {t u A : Tm} (h : TReds Γ t u A) : FSteps t u := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs.whStep.fstep ih

theorem TyReds.fsteps {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) : FSteps A B := by
  induction h with
  | refl => exact .refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs.whStep.fstep ih

/-! ### Congruence of many-step reduction -/

namespace FSteps

theorem pi {F F' G G' : Tm} (hF : FSteps F F') (hG : FSteps G G') : FSteps (Tm.pi F G) (Tm.pi F' G') :=
  (hF.lift (fun x => Tm.pi x G) (fun _ _ h => FStep.piL G h)).trans
    (hG.lift (fun y => Tm.pi F' y) (fun _ _ h => FStep.piR F' h))

theorem lam {b b' : Tm} (h : FSteps b b') : FSteps (Tm.lam b) (Tm.lam b') :=
  h.lift Tm.lam (fun _ _ h => FStep.lam h)

theorem app {f f' a a' : Tm} (hf : FSteps f f') (ha : FSteps a a') :
    FSteps (Tm.app f a) (Tm.app f' a') :=
  (hf.lift (fun x => Tm.app x a) (fun _ _ h => FStep.appL a h)).trans
    (ha.lift (fun y => Tm.app f' y) (fun _ _ h => FStep.appR f' h))

theorem succ {n n' : Tm} (h : FSteps n n') : FSteps (Tm.succ n) (Tm.succ n') :=
  h.lift Tm.succ (fun _ _ h => FStep.succ h)

theorem natrec {P P' z z' s s' n n' : Tm} (hP : FSteps P P') (hz : FSteps z z') (hs : FSteps s s')
    (hn : FSteps n n') : FSteps (Tm.natrec P z s n) (Tm.natrec P' z' s' n') :=
  ((hP.lift (fun x => Tm.natrec x z s n) (fun _ _ h => FStep.natrecP z s n h)).trans
    (hz.lift (fun x => Tm.natrec P' x s n) (fun _ _ h => FStep.natrecZ P' s n h))).trans
    ((hs.lift (fun x => Tm.natrec P' z' x n) (fun _ _ h => FStep.natrecS P' z' n h)).trans
    (hn.lift (fun x => Tm.natrec P' z' s' x) (fun _ _ h => FStep.natrecN P' z' s' h)))

theorem emptyrec {P P' e e' : Tm} (hP : FSteps P P') (he : FSteps e e') :
    FSteps (Tm.emptyrec P e) (Tm.emptyrec P' e') :=
  (hP.lift (fun x => Tm.emptyrec x e) (fun _ _ h => FStep.emptyrecP e h)).trans
    (he.lift (fun y => Tm.emptyrec P' y) (fun _ _ h => FStep.emptyrecE P' h))

end FSteps

/-! ### Renaming and substitution -/

theorem FStep.subst {t u : Tm} (h : FStep t u) : ∀ σ : ℕ → Tm, FStep (MLTT.subst σ t) (MLTT.subst σ u) := by
  induction h with
  | beta b a =>
      intro σ
      rw [subst_inst]
      exact FStep.beta _ _
  | natrecZero P z s => intro σ; exact FStep.natrecZero _ _ _
  | natrecSucc P z s n =>
      intro σ
      rw [subst_inst2]
      exact FStep.natrecSucc _ _ _ _
  | piL G _ ih => intro σ; exact FStep.piL _ (ih σ)
  | piR F _ ih => intro σ; exact FStep.piR _ (ih (up σ))
  | lam _ ih => intro σ; exact FStep.lam (ih (up σ))
  | appL a _ ih => intro σ; exact FStep.appL _ (ih σ)
  | appR f _ ih => intro σ; exact FStep.appR _ (ih σ)
  | succ _ ih => intro σ; exact FStep.succ (ih σ)
  | natrecP z s n _ ih => intro σ; exact FStep.natrecP _ _ _ (ih (up σ))
  | natrecZ P s n _ ih => intro σ; exact FStep.natrecZ _ _ _ (ih σ)
  | natrecS P z n _ ih => intro σ; exact FStep.natrecS _ _ _ (ih (up (up σ)))
  | natrecN P z s _ ih => intro σ; exact FStep.natrecN _ _ _ (ih σ)
  | emptyrecP e _ ih => intro σ; exact FStep.emptyrecP _ (ih σ)
  | emptyrecE P _ ih => intro σ; exact FStep.emptyrecE _ (ih σ)

theorem FStep.rename {t u : Tm} (h : FStep t u) (ρ : ℕ → ℕ) :
    FStep (MLTT.rename ρ t) (MLTT.rename ρ u) := by
  rw [rename_eq_subst, rename_eq_subst]
  exact h.subst _

theorem FSteps.rename {t u : Tm} (h : FSteps t u) (ρ : ℕ → ℕ) :
    FSteps (MLTT.rename ρ t) (MLTT.rename ρ u) :=
  h.lift (MLTT.rename ρ) (fun _ _ h => h.rename ρ)

theorem FSteps.subst {t u : Tm} (h : FSteps t u) (σ : ℕ → Tm) :
    FSteps (MLTT.subst σ t) (MLTT.subst σ u) :=
  h.lift (MLTT.subst σ) (fun _ _ h => h.subst σ)

/-- Lifting pointwise reduction under a binder. -/
theorem FSteps.upArg {σ τ : ℕ → Tm} (h : ∀ i, FSteps (σ i) (τ i)) :
    ∀ i, FSteps (MLTT.up σ i) (MLTT.up τ i)
  | 0 => .refl
  | i + 1 => (h i).rename Nat.succ

/-- Substituting reducing terms reduces. -/
theorem FSteps.substArg : ∀ (t : Tm) {σ τ : ℕ → Tm}, (∀ i, FSteps (σ i) (τ i)) →
    FSteps (MLTT.subst σ t) (MLTT.subst τ t) := by
  intro t
  induction t with
  | var i => intro σ τ h; exact h i
  | univ l => intro σ τ _; exact .refl
  | nat => intro σ τ _; exact .refl
  | zero => intro σ τ _; exact .refl
  | empty => intro σ τ _; exact .refl
  | pi F G ihF ihG =>
      intro σ τ h
      exact FSteps.pi (ihF h) (ihG (FSteps.upArg h))
  | lam b ih => intro σ τ h; exact FSteps.lam (ih (FSteps.upArg h))
  | app f a ihf iha => intro σ τ h; exact FSteps.app (ihf h) (iha h)
  | succ n ih => intro σ τ h; exact FSteps.succ (ih h)
  | natrec P z s n ihP ihz ihs ihn =>
      intro σ τ h
      exact FSteps.natrec (ihP (FSteps.upArg h)) (ihz h) (ihs (FSteps.upArg (FSteps.upArg h))) (ihn h)
  | emptyrec P e ihP ihe => intro σ τ h; exact FSteps.emptyrec (ihP h) (ihe h)

theorem FSteps.inst_arg (t : Tm) {a a' : Tm} (h : FSteps a a') : FSteps (t[a]) (t[a']) :=
  FSteps.substArg t (fun i => by cases i <;> first | exact h | exact .refl)

/-! ### Anti-renaming -/

theorem rename_eq_app {ρ : ℕ → ℕ} {t x y : Tm} (h : MLTT.rename ρ t = app x y) :
    ∃ f a, t = app f a ∧ MLTT.rename ρ f = x ∧ MLTT.rename ρ a = y := by
  cases t <;> simp at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rename_eq_lam {ρ : ℕ → ℕ} {t x : Tm} (h : MLTT.rename ρ t = lam x) :
    ∃ b, t = lam b ∧ MLTT.rename (upr ρ) b = x := by
  cases t <;> simp at h
  exact ⟨_, rfl, h⟩

theorem rename_eq_pi {ρ : ℕ → ℕ} {t x y : Tm} (h : MLTT.rename ρ t = pi x y) :
    ∃ F G, t = pi F G ∧ MLTT.rename ρ F = x ∧ MLTT.rename (upr ρ) G = y := by
  cases t <;> simp at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem rename_eq_succ {ρ : ℕ → ℕ} {t x : Tm} (h : MLTT.rename ρ t = succ x) :
    ∃ n, t = succ n ∧ MLTT.rename ρ n = x := by
  cases t <;> simp at h
  exact ⟨_, rfl, h⟩

theorem rename_eq_zero {ρ : ℕ → ℕ} {t : Tm} (h : MLTT.rename ρ t = zero) : t = zero := by
  cases t <;> simp at h
  rfl

theorem rename_eq_natrec {ρ : ℕ → ℕ} {t P z s n : Tm} (h : MLTT.rename ρ t = natrec P z s n) :
    ∃ P₀ z₀ s₀ n₀, t = natrec P₀ z₀ s₀ n₀ ∧ MLTT.rename (upr ρ) P₀ = P ∧ MLTT.rename ρ z₀ = z ∧
      MLTT.rename (upr (upr ρ)) s₀ = s ∧ MLTT.rename ρ n₀ = n := by
  cases t <;> simp at h
  exact ⟨_, _, _, _, rfl, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem rename_eq_emptyrec {ρ : ℕ → ℕ} {t P e : Tm} (h : MLTT.rename ρ t = emptyrec P e) :
    ∃ P₀ e₀, t = emptyrec P₀ e₀ ∧ MLTT.rename ρ P₀ = P ∧ MLTT.rename ρ e₀ = e := by
  cases t <;> simp at h
  exact ⟨_, _, rfl, h.1, h.2⟩

/-- **Anti-renaming**: a step of a renamed term is the renaming of a step. -/
theorem FStep.unrename {x u : Tm} (h : FStep x u) :
    ∀ {ρ : ℕ → ℕ} {t : Tm}, MLTT.rename ρ t = x → ∃ t', FStep t t' ∧ u = MLTT.rename ρ t' := by
  induction h with
  | beta b a =>
      intro ρ t e
      obtain ⟨f, a₀, rfl, ef, rfl⟩ := rename_eq_app e
      obtain ⟨c, rfl, rfl⟩ := rename_eq_lam ef
      exact ⟨_, FStep.beta c a₀, (rename_inst ρ a₀ c).symm⟩
  | natrecZero P z s =>
      intro ρ t e
      obtain ⟨P₀, z₀, s₀, n₀, rfl, -, rfl, -, en⟩ := rename_eq_natrec e
      rw [rename_eq_zero en]
      exact ⟨_, FStep.natrecZero _ _ _, rfl⟩
  | natrecSucc P z s n =>
      intro ρ t e
      obtain ⟨P₀, z₀, s₀, n₀, rfl, rfl, rfl, rfl, en⟩ := rename_eq_natrec e
      obtain ⟨m, rfl, rfl⟩ := rename_eq_succ en
      exact ⟨_, FStep.natrecSucc _ _ _ _, (rename_inst2 ρ m (natrec P₀ z₀ s₀ m) s₀).symm⟩
  | piL G _ ih =>
      intro ρ t e
      obtain ⟨F₀, G₀, rfl, rfl, rfl⟩ := rename_eq_pi e
      obtain ⟨F', hF, rfl⟩ := ih rfl
      exact ⟨_, FStep.piL _ hF, rfl⟩
  | piR F _ ih =>
      intro ρ t e
      obtain ⟨F₀, G₀, rfl, rfl, rfl⟩ := rename_eq_pi e
      obtain ⟨G', hG, rfl⟩ := ih rfl
      exact ⟨_, FStep.piR _ hG, rfl⟩
  | lam _ ih =>
      intro ρ t e
      obtain ⟨b₀, rfl, rfl⟩ := rename_eq_lam e
      obtain ⟨b', hb, rfl⟩ := ih rfl
      exact ⟨_, FStep.lam hb, rfl⟩
  | appL a _ ih =>
      intro ρ t e
      obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := rename_eq_app e
      obtain ⟨f', hf, rfl⟩ := ih rfl
      exact ⟨_, FStep.appL _ hf, rfl⟩
  | appR f _ ih =>
      intro ρ t e
      obtain ⟨f₀, a₀, rfl, rfl, rfl⟩ := rename_eq_app e
      obtain ⟨a', ha, rfl⟩ := ih rfl
      exact ⟨_, FStep.appR _ ha, rfl⟩
  | succ _ ih =>
      intro ρ t e
      obtain ⟨n₀, rfl, rfl⟩ := rename_eq_succ e
      obtain ⟨n', hn, rfl⟩ := ih rfl
      exact ⟨_, FStep.succ hn, rfl⟩
  | natrecP z s n _ ih =>
      intro ρ t e
      obtain ⟨P₀, z₀, s₀, n₀, rfl, rfl, rfl, rfl, rfl⟩ := rename_eq_natrec e
      obtain ⟨P', hP, rfl⟩ := ih rfl
      exact ⟨_, FStep.natrecP _ _ _ hP, rfl⟩
  | natrecZ P s n _ ih =>
      intro ρ t e
      obtain ⟨P₀, z₀, s₀, n₀, rfl, rfl, rfl, rfl, rfl⟩ := rename_eq_natrec e
      obtain ⟨z', hz, rfl⟩ := ih rfl
      exact ⟨_, FStep.natrecZ _ _ _ hz, rfl⟩
  | natrecS P z n _ ih =>
      intro ρ t e
      obtain ⟨P₀, z₀, s₀, n₀, rfl, rfl, rfl, rfl, rfl⟩ := rename_eq_natrec e
      obtain ⟨s', hs, rfl⟩ := ih rfl
      exact ⟨_, FStep.natrecS _ _ _ hs, rfl⟩
  | natrecN P z s _ ih =>
      intro ρ t e
      obtain ⟨P₀, z₀, s₀, n₀, rfl, rfl, rfl, rfl, rfl⟩ := rename_eq_natrec e
      obtain ⟨n', hn, rfl⟩ := ih rfl
      exact ⟨_, FStep.natrecN _ _ _ hn, rfl⟩
  | emptyrecP e₁ _ ih =>
      intro ρ t e
      obtain ⟨P₀, e₀, rfl, rfl, rfl⟩ := rename_eq_emptyrec e
      obtain ⟨P', hP, rfl⟩ := ih rfl
      exact ⟨_, FStep.emptyrecP _ hP, rfl⟩
  | emptyrecE P _ ih =>
      intro ρ t e
      obtain ⟨P₀, e₀, rfl, rfl, rfl⟩ := rename_eq_emptyrec e
      obtain ⟨e', he, rfl⟩ := ih rfl
      exact ⟨_, FStep.emptyrecE _ he, rfl⟩

theorem FSteps.unrename {ρ : ℕ → ℕ} {t u : Tm} (h : FSteps (MLTT.rename ρ t) u) :
    ∃ t', FSteps t t' ∧ u = MLTT.rename ρ t' := by
  generalize e : MLTT.rename ρ t = x at h
  induction h with
  | refl => exact ⟨t, .refl, e.symm⟩
  | tail _ hs ih =>
      obtain ⟨t₁, h₁, rfl⟩ := ih
      obtain ⟨t₂, h₂, rfl⟩ := hs.unrename rfl
      exact ⟨t₂, h₁.tail h₂, rfl⟩

/-! ### Normal forms -/

/-- **Normal forms**: `NfB true` — neutral normal forms, `NfB false` — normal forms. -/
inductive NfB : Bool → Tm → Prop
  | var (i : ℕ) : NfB true (var i)
  | app {f a : Tm} : NfB true f → NfB false a → NfB true (app f a)
  | natrec {P z s n : Tm} : NfB false P → NfB false z → NfB false s → NfB true n →
      NfB true (natrec P z s n)
  | emptyrec {P e : Tm} : NfB false P → NfB true e → NfB true (emptyrec P e)
  | ne {t : Tm} : NfB true t → NfB false t
  | univ (l : ℕ) : NfB false (Tm.univ l)
  | pi {F G : Tm} : NfB false F → NfB false G → NfB false (pi F G)
  | lam {b : Tm} : NfB false b → NfB false (lam b)
  | nat : NfB false Tm.nat
  | zero : NfB false Tm.zero
  | succ {n : Tm} : NfB false n → NfB false (succ n)
  | empty : NfB false Tm.empty

/-- Normal forms. -/
abbrev Nf (t : Tm) : Prop := NfB false t

/-- Neutral normal forms. -/
abbrev NeNf (t : Tm) : Prop := NfB true t

theorem NfB.rename {c : Bool} {t : Tm} (h : NfB c t) (ρ : ℕ → ℕ) : NfB c (MLTT.rename ρ t) := by
  induction h generalizing ρ with
  | var i => exact NfB.var _
  | app _ _ ihf iha => exact NfB.app (ihf ρ) (iha ρ)
  | natrec _ _ _ _ ihP ihz ihs ihn =>
      exact NfB.natrec (ihP (upr ρ)) (ihz ρ) (ihs (upr (upr ρ))) (ihn ρ)
  | emptyrec _ _ ihP ihe => exact NfB.emptyrec (ihP ρ) (ihe ρ)
  | ne _ ih => exact NfB.ne (ih ρ)
  | univ l => exact NfB.univ l
  | pi _ _ ihF ihG => exact NfB.pi (ihF ρ) (ihG (upr ρ))
  | lam _ ih => exact NfB.lam (ih (upr ρ))
  | nat => exact NfB.nat
  | zero => exact NfB.zero
  | succ _ ih => exact NfB.succ (ih ρ)
  | empty => exact NfB.empty

theorem NeNf.neutral {t : Tm} (h : NeNf t) : Neutral t := by
  suffices H : ∀ {c : Bool} {t : Tm}, NfB c t → c = true → Neutral t from H h rfl
  intro c t h
  induction h with
  | var i => intro _; exact Neutral.var i
  | app _ _ ih _ => intro _; exact Neutral.app _ (ih rfl)
  | natrec _ _ _ _ _ _ _ ih => intro _; exact Neutral.natrec _ _ _ (ih rfl)
  | emptyrec _ _ _ ih => intro _; exact Neutral.emptyrec _ (ih rfl)
  | _ => intro e; cases e

/-- **Anti-renaming of normal forms.** -/
theorem NfB.unrename : ∀ (t : Tm) {c : Bool} {ρ : ℕ → ℕ}, NfB c (MLTT.rename ρ t) → NfB c t := by
  intro t
  induction t with
  | var i =>
      intro c ρ h
      cases c
      · exact NfB.ne (NfB.var i)
      · exact NfB.var i
  | univ l =>
      intro c ρ h
      cases h with
      | univ => exact NfB.univ l
      | ne h => cases h
  | nat =>
      intro c ρ h
      cases h with
      | nat => exact NfB.nat
      | ne h => cases h
  | zero =>
      intro c ρ h
      cases h with
      | zero => exact NfB.zero
      | ne h => cases h
  | empty =>
      intro c ρ h
      cases h with
      | empty => exact NfB.empty
      | ne h => cases h
  | pi F G ihF ihG =>
      intro c ρ h
      cases h with
      | pi hF hG => exact NfB.pi (ihF hF) (ihG hG)
      | ne h => cases h
  | lam b ih =>
      intro c ρ h
      cases h with
      | lam hb => exact NfB.lam (ih hb)
      | ne h => cases h
  | succ n ih =>
      intro c ρ h
      cases h with
      | succ hn => exact NfB.succ (ih hn)
      | ne h => cases h
  | app f a ihf iha =>
      intro c ρ h
      have key : NfB true (MLTT.rename ρ (Tm.app f a)) → NfB true (Tm.app f a) := by
        intro h'
        cases h' with
        | app hf ha => exact NfB.app (ihf hf) (iha ha)
      cases c
      · cases h with
        | ne h => exact NfB.ne (key h)
      · exact key h
  | natrec P z s n ihP ihz ihs ihn =>
      intro c ρ h
      have key : NfB true (MLTT.rename ρ (Tm.natrec P z s n)) → NfB true (Tm.natrec P z s n) := by
        intro h'
        cases h' with
        | natrec hP hz hs hn => exact NfB.natrec (ihP hP) (ihz hz) (ihs hs) (ihn hn)
      cases c
      · cases h with
        | ne h => exact NfB.ne (key h)
      · exact key h
  | emptyrec P e ihP ihe =>
      intro c ρ h
      have key : NfB true (MLTT.rename ρ (Tm.emptyrec P e)) → NfB true (Tm.emptyrec P e) := by
        intro h'
        cases h' with
        | emptyrec hP he => exact NfB.emptyrec (ihP hP) (ihe he)
      cases c
      · cases h with
        | ne h => exact NfB.ne (key h)
      · exact key h

/-- Neutral terms reduce to neutral terms. -/
theorem Neutral.fstep {x y : Tm} (hx : Neutral x) (h : FStep x y) : Neutral y := by
  induction hx generalizing y with
  | var n => cases h
  | app a hf ih =>
      cases h with
      | beta => cases hf
      | appL _ h => exact Neutral.app _ (ih h)
      | appR _ _ => exact Neutral.app _ hf
  | natrec P z s hn ih =>
      cases h with
      | natrecZero => cases hn
      | natrecSucc => cases hn
      | natrecP _ _ _ _ => exact Neutral.natrec _ _ _ hn
      | natrecZ _ _ _ _ => exact Neutral.natrec _ _ _ hn
      | natrecS _ _ _ _ => exact Neutral.natrec _ _ _ hn
      | natrecN _ _ _ h => exact Neutral.natrec _ _ _ (ih h)
  | emptyrec P he ih =>
      cases h with
      | emptyrecP _ _ => exact Neutral.emptyrec _ he
      | emptyrecE _ h => exact Neutral.emptyrec _ (ih h)

/-! ### Subject reduction for full reduction -/

/-- **Congruence of abstraction**, from the η rule. -/
theorem DEq.lam_cong {Γ : Ctx} {F G b b' : Tm} (hF : WfTy Γ F) (h : DEq (F :: Γ) b b' G) :
    DEq Γ (lam b) (lam b') (pi F G) := by
  have hwf : WfCtx (F :: Γ) := Der.cons hF.wf hF
  have key : ∀ c, HasTy (F :: Γ) c G → DEq (F :: Γ) (app (shift (lam c)) (Tm.var 0)) c G := by
    intro c hc
    have hv : HasTy (F :: Γ) (Tm.var 0) (shift F) := Der.var hwf (Lookup.zero Γ F)
    have hc' := hc.rename ((RenOk.shift Γ F).up F) (Der.cons hwf (hF.weaken hwf))
    have := Der.beta (hF.weaken hwf) hc' hv
    rw [shift_inst_rename, shift_inst_rename] at this
    exact this
  exact Der.eta hF (Der.lam hF h.tyL) (Der.lam hF h.tyR)
    (Der.trans (key b h.tyL) (Der.trans h (Der.symm (key b' h.tyR))))

/-- **Subject reduction for full reduction**: a step of a typed term is a judgemental equality
at its type. -/
theorem FStep.deq {t u : Tm} (h : FStep t u) : ∀ {Γ : Ctx} {T : Tm}, HasTy Γ t T → DEq Γ t u T := by
  induction h with
  | beta b a =>
      intro Γ T ht
      obtain ⟨F, G, hf, ha, hT⟩ := ht.inv_app
      obtain ⟨F₀, G₀, hF₀, hb, hP⟩ := hf.inv_lam
      obtain ⟨hFF, hGG⟩ := TyEq.pi_inj hP
      have hβ := Der.beta hF₀ hb (Der.conv ha hFF)
      exact Der.eqConv hβ (Der.transT (Der.symmT (hGG.inst ha)) (Der.symmT hT))
  | natrecZero P z s =>
      intro Γ T ht
      obtain ⟨hP, hz, hs, -, hT⟩ := ht.inv_natrec
      exact Der.eqConv (Der.natrecZero hP hz hs) (Der.symmT hT)
  | natrecSucc P z s n =>
      intro Γ T ht
      obtain ⟨hP, hz, hs, hn, hT⟩ := ht.inv_natrec
      exact Der.eqConv (Der.natrecSucc hP hz hs hn.inv_succ.1) (Der.symmT hT)
  | piL G _ ih =>
      intro Γ T ht
      obtain ⟨i, j, hF, hG, hT⟩ := ht.inv_pi
      exact Der.eqConv (Der.piCongU hF (ih hF) (Der.refl hG)) (Der.symmT hT)
  | piR F _ ih =>
      intro Γ T ht
      obtain ⟨i, j, hF, hG, hT⟩ := ht.inv_pi
      exact Der.eqConv (Der.piCongU hF (Der.refl hF) (ih hG)) (Der.symmT hT)
  | lam _ ih =>
      intro Γ T ht
      obtain ⟨F₀, G₀, hF₀, hb, hT⟩ := ht.inv_lam
      exact Der.eqConv (DEq.lam_cong hF₀ (ih hb)) (Der.symmT hT)
  | appL a _ ih =>
      intro Γ T ht
      obtain ⟨F, G, hf, ha, hT⟩ := ht.inv_app
      exact Der.eqConv (Der.appCong (ih hf) (Der.refl ha)) (Der.symmT hT)
  | appR f _ ih =>
      intro Γ T ht
      obtain ⟨F, G, hf, ha, hT⟩ := ht.inv_app
      exact Der.eqConv (Der.appCong (Der.refl hf) (ih ha)) (Der.symmT hT)
  | succ _ ih =>
      intro Γ T ht
      obtain ⟨hn, hT⟩ := ht.inv_succ
      exact Der.eqConv (Der.succCong (ih hn)) (Der.symmT hT)
  | natrecP z s n _ ih =>
      intro Γ T ht
      obtain ⟨hP, hz, hs, hn, hT⟩ := ht.inv_natrec
      obtain ⟨l, hPl⟩ := WfTy.univ hP
      exact Der.eqConv (Der.natrecCong hP (Der.elEq (ih hPl)) (Der.refl hz) (Der.refl hs)
        (Der.refl hn)) (Der.symmT hT)
  | natrecZ P s n _ ih =>
      intro Γ T ht
      obtain ⟨hP, hz, hs, hn, hT⟩ := ht.inv_natrec
      exact Der.eqConv (Der.natrecCong hP (Der.reflT hP) (ih hz) (Der.refl hs) (Der.refl hn))
        (Der.symmT hT)
  | natrecS P z n _ ih =>
      intro Γ T ht
      obtain ⟨hP, hz, hs, hn, hT⟩ := ht.inv_natrec
      exact Der.eqConv (Der.natrecCong hP (Der.reflT hP) (Der.refl hz) (ih hs) (Der.refl hn))
        (Der.symmT hT)
  | natrecN P z s _ ih =>
      intro Γ T ht
      obtain ⟨hP, hz, hs, hn, hT⟩ := ht.inv_natrec
      exact Der.eqConv (Der.natrecCong hP (Der.reflT hP) (Der.refl hz) (Der.refl hs) (ih hn))
        (Der.symmT hT)
  | emptyrecP e _ ih =>
      intro Γ T ht
      obtain ⟨hP, he, hT⟩ := ht.inv_emptyrec
      obtain ⟨l, hPl⟩ := WfTy.univ hP
      exact Der.eqConv (Der.emptyrecCong (Der.elEq (ih hPl)) (Der.refl he)) (Der.symmT hT)
  | emptyrecE P _ ih =>
      intro Γ T ht
      obtain ⟨hP, he, hT⟩ := ht.inv_emptyrec
      exact Der.eqConv (Der.emptyrecCong (Der.reflT hP) (ih he)) (Der.symmT hT)

theorem FStep.tyEq {Γ : Ctx} {A B : Tm} (h : FStep A B) (hA : WfTy Γ A) : TyEq Γ A B := by
  obtain ⟨l, hl⟩ := WfTy.univ hA
  exact Der.elEq (h.deq hl)

theorem FSteps.deq {Γ : Ctx} {t u T : Tm} (h : FSteps t u) (ht : HasTy Γ t T) : DEq Γ t u T := by
  induction h with
  | refl => exact Der.refl ht
  | tail _ hs ih => exact Der.trans ih (hs.deq ih.tyR)

theorem FSteps.tyEq {Γ : Ctx} {A B : Tm} (h : FSteps A B) (hA : WfTy Γ A) : TyEq Γ A B := by
  induction h with
  | refl => exact Der.reflT hA
  | tail _ hs ih => exact Der.transT ih (hs.tyEq ih.wfR)

/-! ### Canonical forms at a product -/

/-- A weak head normal term of a product type is an abstraction or neutral. -/
theorem Whnf.pi_canon {Γ : Ctx} {f F G : Tm} (hf : HasTy Γ f (Tm.pi F G)) (hw : Whnf f) :
    (∃ b, f = Tm.lam b) ∨ Neutral f := by
  cases hw with
  | univ l =>
      have := TyEq.univ_whnf (Der.symmT hf.inv_univ) (Whnf.pi _ _)
      cases this
  | pi A B =>
      obtain ⟨i, j, -, -, h⟩ := hf.inv_pi
      have := TyEq.univ_whnf (Der.symmT h) (Whnf.pi _ _)
      cases this
  | lam b => exact Or.inl ⟨b, rfl⟩
  | nat =>
      have := TyEq.univ_whnf (Der.symmT hf.inv_nat) (Whnf.pi _ _)
      cases this
  | zero =>
      have := TyEq.nat_whnf (Der.symmT hf.inv_zero) (Whnf.pi _ _)
      cases this
  | succ n =>
      have := TyEq.nat_whnf (Der.symmT hf.inv_succ.2) (Whnf.pi _ _)
      cases this
  | empty =>
      have := TyEq.univ_whnf (Der.symmT hf.inv_empty) (Whnf.pi _ _)
      cases this
  | ne hn => exact Or.inr hn

end MLTT
