/-
**Completeness of normalization by evaluation for the simply typed λ-calculus** — task
`M23-NBE-STLC` (round 6, part F).

* `StlcNbE.EqS` — the Kripke partial equivalence on semantic values: equality at the base type,
  and at function types extensional equality together with **uniformity** (naturality of the
  function in the renaming);
* `StlcNbE.EqS.symm`, `StlcNbE.EqS.trans`, `StlcNbE.EqS.ren` — it is a PER, stable under
  renaming;
* `StlcNbE.reflect_reify_eq` — reflection is uniform and natural, reification identifies related
  values and commutes with renaming;
* `StlcNbE.eval_resp` — evaluation respects related environments and is natural in renamings;
* `StlcNbE.eval_ren`, `StlcNbE.eval_sub` — evaluation of renamed and substituted terms;
* `StlcNbE.eval_conv` — convertible terms evaluate to related values;
* `StlcNbE.nf_complete` — **completeness**: `Γ ⊢ t ≡βη u : A → nf t = nf u`;
* `StlcNbE.conv_iff_nf_eq`, `StlcNbE.decidableConv` — βη-conversion of well-typed terms is
  decided by comparing normal forms (with `DecidableEq` derived for `Stlc.Var` and `Stlc.Tm`).
-/

import Start.StlcNbE

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Stlc

deriving instance DecidableEq for Var
deriving instance DecidableEq for Tm

end Stlc

namespace StlcNbE

open Stlc

/-! ### The presheaf laws -/

theorem Sem.ren_ren : ∀ {A : Ty} {Γ Δ Θ : Ctx} (r' : Ren Δ Θ) (r : Ren Γ Δ) (a : Sem A Γ),
    Sem.ren r' (Sem.ren r a) = Sem.ren (r'.comp r) a
  | .base, _, _, _, r', r, a => Stlc.ren_ren r' r a
  | .unit, _, _, _, _, _, _ => rfl
  | .prod _ _, _, _, _, r', r, a => by
      show (Sem.ren r' (Sem.ren r a.1), Sem.ren r' (Sem.ren r a.2)) = _
      rw [Sem.ren_ren r' r a.1, Sem.ren_ren r' r a.2]
      rfl
  | .arrow _ _, _, _, _, _, _, _ => rfl

theorem Sem.ren_id : ∀ {A : Ty} {Γ : Ctx} (a : Sem A Γ), Sem.ren (Ren.id Γ) a = a
  | .base, _, a => Stlc.ren_id a
  | .unit, _, _ => rfl
  | .prod _ _, _, a => by
      show (Sem.ren (Ren.id _) a.1, Sem.ren (Ren.id _) a.2) = _
      rw [Sem.ren_id a.1, Sem.ren_id a.2]
      rfl
  | .arrow _ _, _, _ => rfl

/-! ### The Kripke PER -/

/-- **The Kripke partial equivalence on semantic values.** -/
def EqS : ∀ (A : Ty) {Γ : Ctx}, Sem A Γ → Sem A Γ → Prop
  | .base, _, a, b => a = b
  | .unit, _, _, _ => True
  | .prod A B, _, p, q => EqS A p.1 q.1 ∧ EqS B p.2 q.2
  | .arrow A B, Γ, f, g =>
      (∀ (Δ : Ctx) (r : Ren Γ Δ) (a b : Sem A Δ), EqS A a b → EqS B (f Δ r a) (g Δ r b)) ∧
      (∀ (Δ Θ : Ctx) (r : Ren Γ Δ) (r' : Ren Δ Θ) (a : Sem A Δ), EqS A a a →
        EqS B (Sem.ren r' (f Δ r a)) (f Θ (r'.comp r) (Sem.ren r' a))) ∧
      (∀ (Δ Θ : Ctx) (r : Ren Γ Δ) (r' : Ren Δ Θ) (a : Sem A Δ), EqS A a a →
        EqS B (Sem.ren r' (g Δ r a)) (g Θ (r'.comp r) (Sem.ren r' a)))

theorem EqS.per : ∀ (A : Ty),
    (∀ {Γ : Ctx} {a b : Sem A Γ}, EqS A a b → EqS A b a) ∧
      ∀ {Γ : Ctx} {a b c : Sem A Γ}, EqS A a b → EqS A b c → EqS A a c
  | .base => ⟨fun h => h.symm, fun h h' => h.trans h'⟩
  | .unit => ⟨fun _ => trivial, fun _ _ => trivial⟩
  | .prod A B => ⟨fun h => ⟨(EqS.per A).1 h.1, (EqS.per B).1 h.2⟩,
      fun h h' => ⟨(EqS.per A).2 h.1 h'.1, (EqS.per B).2 h.2 h'.2⟩⟩
  | .arrow A B =>
      ⟨fun h => ⟨fun Δ r a b hab => (EqS.per B).1 (h.1 Δ r b a ((EqS.per A).1 hab)), h.2.2, h.2.1⟩,
        fun h h' => ⟨fun Δ r a b hab =>
          (EqS.per B).2 (h.1 Δ r a b hab)
            (h'.1 Δ r b b ((EqS.per A).2 ((EqS.per A).1 hab) hab)), h.2.1, h'.2.2⟩⟩

theorem EqS.symm {A : Ty} {Γ : Ctx} {a b : Sem A Γ} (h : EqS A a b) : EqS A b a :=
  (EqS.per A).1 h

theorem EqS.trans {A : Ty} {Γ : Ctx} {a b c : Sem A Γ} (h : EqS A a b) (h' : EqS A b c) :
    EqS A a c :=
  (EqS.per A).2 h h'

theorem EqS.left {A : Ty} {Γ : Ctx} {a b : Sem A Γ} (h : EqS A a b) : EqS A a a :=
  h.trans h.symm

theorem EqS.right {A : Ty} {Γ : Ctx} {a b : Sem A Γ} (h : EqS A a b) : EqS A b b :=
  h.symm.trans h

/-- The PER is stable under renaming. -/
theorem EqS.ren : ∀ (A : Ty) {Γ Δ : Ctx} (r : Ren Γ Δ) {a b : Sem A Γ}, EqS A a b →
    EqS A (Sem.ren r a) (Sem.ren r b)
  | .base, _, _, r, _, _, h => by
      show Stlc.ren r _ = Stlc.ren r _
      rw [show _ = _ from h]
  | .unit, _, _, _, _, _, _ => trivial
  | .prod A B, _, _, r, _, _, h => ⟨EqS.ren A r h.1, EqS.ren B r h.2⟩
  | .arrow _ _, _, _, r, _, _, h =>
      ⟨fun Δ r' a b hab => h.1 Δ (r'.comp r) a b hab,
        fun Δ Θ r' r'' a ha => h.2.1 Δ Θ (r'.comp r) r'' a ha,
        fun Δ Θ r' r'' a ha => h.2.2 Δ Θ (r'.comp r) r'' a ha⟩

/-! ### Reflection and reification -/

/-- **Reflection is uniform and natural; reification identifies related values and commutes with
renaming.** -/
theorem reflect_reify_eq : ∀ (A : Ty),
    (∀ {Γ : Ctx} (t : Tm Γ A), EqS A (reflect A t) (reflect A t)) ∧
    (∀ {Γ Δ : Ctx} (r : Ren Γ Δ) (t : Tm Γ A),
      EqS A (Sem.ren r (reflect A t)) (reflect A (Stlc.ren r t))) ∧
    (∀ {Γ : Ctx} {a b : Sem A Γ}, EqS A a b → reify A a = reify A b) ∧
    (∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {a : Sem A Γ}, EqS A a a →
      Stlc.ren r (reify A a) = reify A (Sem.ren r a))
  | .base => ⟨fun _ => rfl, fun _ _ => rfl, fun h => h, fun _ _ _ => rfl⟩
  | .unit => ⟨fun _ => trivial, fun _ _ => trivial, fun _ => rfl, fun _ _ _ => rfl⟩
  | .prod A B =>
      ⟨fun t => ⟨(reflect_reify_eq A).1 (Tm.fst t), (reflect_reify_eq B).1 (Tm.snd t)⟩,
        fun r t => ⟨(reflect_reify_eq A).2.1 r (Tm.fst t), (reflect_reify_eq B).2.1 r (Tm.snd t)⟩,
        fun {_} {a b} h => by
          show Tm.pair (reify A a.1) (reify B a.2) = Tm.pair (reify A b.1) (reify B b.2)
          rw [(reflect_reify_eq A).2.2.1 h.1, (reflect_reify_eq B).2.2.1 h.2],
        fun {_ _} r {a} h => by
          show Tm.pair (Stlc.ren r (reify A a.1)) (Stlc.ren r (reify B a.2)) =
            Tm.pair (reify A (Sem.ren r a.1)) (reify B (Sem.ren r a.2))
          rw [(reflect_reify_eq A).2.2.2 r h.1, (reflect_reify_eq B).2.2.2 r h.2]⟩
  | .arrow A B => by
      obtain ⟨hAa, hAb, hAc, hAd⟩ := reflect_reify_eq A
      obtain ⟨hBa, hBb, hBc, hBd⟩ := reflect_reify_eq B
      have nat : ∀ {Γ : Ctx} (t : Tm Γ (.arrow A B)) (Δ Θ : Ctx) (r : Ren Γ Δ) (r' : Ren Δ Θ)
          (a : Sem A Δ), EqS A a a →
          EqS B (Sem.ren r' (reflect B (Tm.app (Stlc.ren r t) (reify A a))))
            (reflect B (Tm.app (Stlc.ren (r'.comp r) t) (reify A (Sem.ren r' a)))) := by
        intro Γ t Δ Θ r r' a ha
        have h := hBb r' (Tm.app (Stlc.ren r t) (reify A a))
        have e : Stlc.ren r' (Tm.app (Stlc.ren r t) (reify A a)) =
            Tm.app (Stlc.ren (r'.comp r) t) (reify A (Sem.ren r' a)) := by
          show Tm.app (Stlc.ren r' (Stlc.ren r t)) (Stlc.ren r' (reify A a)) = _
          rw [ren_ren, hAd r' ha]
        rw [e] at h
        exact h
      have ha : ∀ {Γ : Ctx} (t : Tm Γ (.arrow A B)),
          EqS (.arrow A B) (reflect (.arrow A B) t) (reflect (.arrow A B) t) := by
        intro Γ t
        refine ⟨fun Δ r a b hab => ?_, nat t, nat t⟩
        show EqS B (reflect B (Tm.app (Stlc.ren r t) (reify A a)))
          (reflect B (Tm.app (Stlc.ren r t) (reify A b)))
        rw [hAc hab]
        exact hBa _
      refine ⟨ha, fun {Γ Δ} r t => ?_, fun {Γ} {f g} h => ?_, fun {Γ Δ} r {f} h => ?_⟩
      · have e : Sem.ren r (reflect (.arrow A B) t) = reflect (.arrow A B) (Stlc.ren r t) := by
          funext Θ r' a
          show reflect B (Tm.app (Stlc.ren (r'.comp r) t) (reify A a)) =
            reflect B (Tm.app (Stlc.ren r' (Stlc.ren r t)) (reify A a))
          rw [ren_ren]
        rw [e]
        exact ha _
      · show Tm.lam (reify B (f (A :: Γ) (Ren.wk A) (reflect A (Tm.var Var.zero)))) =
          Tm.lam (reify B (g (A :: Γ) (Ren.wk A) (reflect A (Tm.var Var.zero))))
        rw [hBc (h.1 _ (Ren.wk A) _ _ (hAa _))]
      · have x0 := hAa (Γ := A :: Γ) (Tm.var Var.zero)
        have hf0 := h.1 (A :: Γ) (Ren.wk A) _ _ x0
        show Tm.lam (Stlc.ren (r.lift A)
            (reify B (f (A :: Γ) (Ren.wk A) (reflect A (Tm.var Var.zero))))) =
          Tm.lam (reify B (f (A :: Δ) ((Ren.wk A).comp r) (reflect A (Tm.var Var.zero))))
        rw [hBd (r.lift A) hf0.left]
        congr 1
        apply hBc
        refine (h.2.1 (A :: Γ) (A :: Δ) (Ren.wk A) (r.lift A) _ x0).trans ?_
        exact h.1 _ _ _ _ (hAb (r.lift A) (Tm.var Var.zero))

/-! ### Evaluation respects the PER -/

/-- Pointwise related environments. -/
def EqEnv {Γ Δ : Ctx} (ρ ρ' : Env Γ Δ) : Prop := ∀ (B : Ty) (v : Var Γ B), EqS B (ρ B v) (ρ' B v)

theorem Env.ren_ren {Γ Δ Θ Ξ : Ctx} (r' : Ren Θ Ξ) (r : Ren Δ Θ) (ρ : Env Γ Δ) :
    Env.ren r' (Env.ren r ρ) = Env.ren (r'.comp r) ρ := by
  funext B v
  exact Sem.ren_ren r' r (ρ B v)

theorem Env.ren_id {Γ Δ : Ctx} (ρ : Env Γ Δ) : Env.ren (Ren.id Δ) ρ = ρ := by
  funext B v
  exact Sem.ren_id (ρ B v)

theorem Env.ren_cons {Γ Δ Θ : Ctx} {A : Ty} (r : Ren Δ Θ) (a : Sem A Δ) (ρ : Env Γ Δ) :
    Env.ren r (Env.cons a ρ) = Env.cons (Sem.ren r a) (Env.ren r ρ) := by
  funext B v
  cases v <;> rfl

theorem EqEnv.ren {Γ Δ Θ : Ctx} (r : Ren Δ Θ) {ρ ρ' : Env Γ Δ} (h : EqEnv ρ ρ') :
    EqEnv (Env.ren r ρ) (Env.ren r ρ') := fun B v => EqS.ren B r (h B v)

theorem EqEnv.cons {Γ Δ : Ctx} {A : Ty} {a b : Sem A Δ} {ρ ρ' : Env Γ Δ} (hab : EqS A a b)
    (h : EqEnv ρ ρ') : EqEnv (Env.cons a ρ) (Env.cons b ρ') := by
  intro B v
  cases v with
  | zero => exact hab
  | succ v => exact h B v

theorem EqEnv.left {Γ Δ : Ctx} {ρ ρ' : Env Γ Δ} (h : EqEnv ρ ρ') : EqEnv ρ ρ :=
  fun B v => (h B v).left

theorem EqEnv.right {Γ Δ : Ctx} {ρ ρ' : Env Γ Δ} (h : EqEnv ρ ρ') : EqEnv ρ' ρ' :=
  fun B v => (h B v).right

theorem EqEnv.symm {Γ Δ : Ctx} {ρ ρ' : Env Γ Δ} (h : EqEnv ρ ρ') : EqEnv ρ' ρ :=
  fun B v => (h B v).symm

/-- **Evaluation respects related environments and is natural in renamings.** -/
theorem eval_resp : ∀ {Γ : Ctx} {A : Ty} (t : Tm Γ A),
    (∀ {Δ : Ctx} {ρ ρ' : Env Γ Δ}, EqEnv ρ ρ' → EqS A (eval t ρ) (eval t ρ')) ∧
    (∀ {Δ Θ : Ctx} (r : Ren Δ Θ) {ρ : Env Γ Δ}, EqEnv ρ ρ →
      EqS A (Sem.ren r (eval t ρ)) (eval t (Env.ren r ρ)))
  | _, _, Tm.var v => ⟨fun h => h _ v, fun r _ h => EqS.ren _ r (h _ v)⟩
  | _, _, Tm.app f a => by
      obtain ⟨hf1, hf2⟩ := eval_resp f
      obtain ⟨ha1, ha2⟩ := eval_resp a
      refine ⟨fun {Δ _ _} h => (hf1 h).1 Δ (Ren.id Δ) _ _ (ha1 h), fun {Δ Θ} r {ρ} h => ?_⟩
      have e1 := (hf1 h).2.1 Δ Θ (Ren.id Δ) r (eval a ρ) (ha1 h)
      have e2 := (hf2 r h).1 Θ (Ren.id Θ) _ _ (ha2 r h)
      exact e1.trans e2
  | _, .arrow A B, Tm.lam t => by
      obtain ⟨ht1, ht2⟩ := eval_resp t
      have key : ∀ {Δ : Ctx} {ρ ρ' : Env _ Δ}, EqEnv ρ ρ' →
          EqS (.arrow A B) (eval (Tm.lam t) ρ) (eval (Tm.lam t) ρ') := by
        intro Δ ρ ρ' h
        have nat : ∀ (σ : Env _ Δ), EqEnv σ σ → ∀ (Θ Ξ : Ctx) (r : Ren Δ Θ) (r' : Ren Θ Ξ)
            (a : Sem A Θ), EqS A a a →
            EqS B (Sem.ren r' (eval t (Env.cons a (Env.ren r σ))))
              (eval t (Env.cons (Sem.ren r' a) (Env.ren (r'.comp r) σ))) := by
          intro σ hσ Θ Ξ r r' a ha
          have := ht2 r' (EqEnv.cons ha (hσ.ren r))
          rw [Env.ren_cons, Env.ren_ren] at this
          exact this
        exact ⟨fun Θ r a b hab => ht1 (EqEnv.cons hab (h.ren r)), nat ρ h.left, nat ρ' h.right⟩
      refine ⟨key, fun {Δ Θ} r {ρ} h => ?_⟩
      have e : Sem.ren r (eval (Tm.lam t) ρ) = eval (Tm.lam t) (Env.ren r ρ) := by
        funext Ξ r' a
        show eval t (Env.cons a (Env.ren (r'.comp r) ρ)) = eval t (Env.cons a (Env.ren r' (Env.ren r ρ)))
        rw [Env.ren_ren]
      rw [e]
      exact key (h.ren r)
  | _, _, Tm.star => ⟨fun _ => trivial, fun _ _ _ => trivial⟩
  | _, _, Tm.pair a b =>
      ⟨fun h => ⟨(eval_resp a).1 h, (eval_resp b).1 h⟩,
        fun r _ h => ⟨(eval_resp a).2 r h, (eval_resp b).2 r h⟩⟩
  | _, _, Tm.fst t => ⟨fun h => ((eval_resp t).1 h).1, fun r _ h => ((eval_resp t).2 r h).1⟩
  | _, _, Tm.snd t => ⟨fun h => ((eval_resp t).1 h).2, fun r _ h => ((eval_resp t).2 r h).2⟩

/-! ### Renaming and substitution -/

/-- Evaluation of a renamed term. -/
theorem eval_ren : ∀ {Γ Γ' : Ctx} {A : Ty} (r : Ren Γ Γ') (t : Tm Γ A) {Δ : Ctx} (ρ : Env Γ' Δ),
    eval (Stlc.ren r t) ρ = eval t (fun B v => ρ B (r B v))
  | _, _, _, _, Tm.var _, _, _ => rfl
  | _, _, _, r, Tm.app f a, Δ, ρ => by
      show eval (Stlc.ren r f) ρ Δ (Ren.id Δ) (eval (Stlc.ren r a) ρ) = _
      rw [eval_ren r f, eval_ren r a]
      rfl
  | _, _, _, r, Tm.lam t, _, ρ => by
      funext Θ r' a
      show eval (Stlc.ren (r.lift _) t) (Env.cons a (Env.ren r' ρ)) = _
      rw [eval_ren]
      congr 1
      funext B v
      cases v <;> rfl
  | _, _, _, _, Tm.star, _, _ => rfl
  | _, _, _, r, Tm.pair a b, _, ρ => by
      show (eval (Stlc.ren r a) ρ, eval (Stlc.ren r b) ρ) = _
      rw [eval_ren r a, eval_ren r b]
      rfl
  | _, _, _, r, Tm.fst t, _, ρ => by
      show (eval (Stlc.ren r t) ρ).1 = _
      rw [eval_ren r t]
      rfl
  | _, _, _, r, Tm.snd t, _, ρ => by
      show (eval (Stlc.ren r t) ρ).2 = _
      rw [eval_ren r t]
      rfl

/-- **Evaluation of a substituted term.** -/
theorem eval_sub : ∀ {Γ Γ' : Ctx} {A : Ty} (σ : Sub Γ Γ') (t : Tm Γ A) {Δ : Ctx}
    {ρ : Env Γ' Δ}, EqEnv ρ ρ → EqS A (eval (sub σ t) ρ) (eval t (fun B v => eval (σ B v) ρ))
  | _, _, _, σ, Tm.var v, _, _, h => (eval_resp (σ _ v)).1 h
  | _, _, _, σ, Tm.app f a, Δ, _, h => (eval_sub σ f h).1 Δ (Ren.id Δ) _ _ (eval_sub σ a h)
  | _, _, .arrow A B, σ, Tm.lam t, _, ρ, h => by
      have hσ : EqEnv (fun C v => eval (σ C v) ρ) (fun C v => eval (σ C v) ρ) :=
        fun C v => (eval_resp (σ C v)).1 h
      have selfL := (eval_resp (sub σ (Tm.lam t))).1 h
      have selfR := (eval_resp (Tm.lam t)).1 hσ
      refine ⟨fun Θ r a b hab => ?_, selfL.2.1, selfR.2.2⟩
      show EqS B (eval (sub (σ.lift A) t) (Env.cons a (Env.ren r ρ)))
        (eval t (Env.cons b (Env.ren r fun C v => eval (σ C v) ρ)))
      refine (eval_sub (σ.lift A) t (EqEnv.cons hab.left (h.ren r))).trans ?_
      refine (eval_resp t).1 fun C v => ?_
      cases v with
      | zero => exact hab
      | succ v =>
          show EqS C (eval (Stlc.ren (Ren.wk A) (σ C v)) (Env.cons a (Env.ren r ρ)))
            (Sem.ren r (eval (σ C v) ρ))
          rw [eval_ren]
          exact ((eval_resp (σ C v)).2 r h).symm
  | _, _, _, _, Tm.star, _, _, _ => trivial
  | _, _, _, σ, Tm.pair a b, _, _, h => ⟨eval_sub σ a h, eval_sub σ b h⟩
  | _, _, _, σ, Tm.fst t, _, _, h => (eval_sub σ t h).1
  | _, _, _, σ, Tm.snd t, _, _, h => (eval_sub σ t h).2

/-! ### Completeness -/

/-- **Convertible terms evaluate to related values.** -/
theorem eval_conv {Γ : Ctx} {A : Ty} {t u : Tm Γ A} (hc : Conv t u) :
    ∀ {Δ : Ctx} {ρ ρ' : Env Γ Δ}, EqEnv ρ ρ' → EqS A (eval t ρ) (eval u ρ') := by
  induction hc with
  | refl t => exact fun h => (eval_resp t).1 h
  | symm _ ih => exact fun h => (ih h.symm).symm
  | trans _ _ ih1 ih2 => exact fun h => (ih1 h).trans (ih2 h.right)
  | app _ _ ihf iha => exact fun {Δ _ _} h => (ihf h).1 Δ (Ren.id Δ) _ _ (iha h)
  | @lam Γ A B t t' _ ih =>
      intro Δ ρ ρ' h
      exact ⟨fun Θ r a b hab => ih (EqEnv.cons hab (h.ren r)),
        ((eval_resp (Tm.lam t)).1 h.left).2.1, ((eval_resp (Tm.lam t')).1 h.right).2.2⟩
  | pair _ _ iha ihb => exact fun h => ⟨iha h, ihb h⟩
  | fst _ ih => exact fun h => (ih h).1
  | snd _ ih => exact fun h => (ih h).2
  | @beta Γ A B t s =>
      intro Δ ρ ρ' h
      show EqS B (eval t (Env.cons (eval s ρ) (Env.ren (Ren.id Δ) ρ))) (eval (sub (Sub.single s) t) ρ')
      rw [Env.ren_id]
      refine EqS.trans ?_ (eval_sub (Sub.single s) t h.right).symm
      refine (eval_resp t).1 fun C v => ?_
      cases v with
      | zero => exact (eval_resp s).1 h
      | succ v => exact h C v
  | @eta Γ A B t =>
      intro Δ ρ ρ' h
      refine ⟨fun Θ r a b hab => ?_, ((eval_resp t).1 h.left).2.1,
        ((eval_resp (Tm.lam (Tm.app (wk A t) (Tm.var Var.zero)))).1 h.right).2.2⟩
      show EqS B (eval t ρ Θ r a)
        (eval (Stlc.ren (Ren.wk A) t) (Env.cons b (Env.ren r ρ')) Θ (Ren.id Θ) b)
      rw [eval_ren]
      exact (((eval_resp t).1 h).1 Θ r a a hab.left).trans
        (((eval_resp t).2 r h.right).1 Θ (Ren.id Θ) a b hab)
  | fst_pair a b => exact fun h => (eval_resp a).1 h
  | snd_pair a b => exact fun h => (eval_resp b).1 h
  | pair_eta t => exact fun h => ⟨((eval_resp t).1 h).1, ((eval_resp t).1 h).2⟩
  | unit_eta t => exact fun _ => trivial

/-- The identity environment is related to itself. -/
theorem idEnv_eq (Γ : Ctx) : EqEnv (idEnv Γ) (idEnv Γ) :=
  fun B v => (reflect_reify_eq B).1 (Tm.var v)

/-- **Completeness of normalization by evaluation**: convertible terms have equal normal
forms. -/
theorem nf_complete {Γ : Ctx} {A : Ty} {t u : Tm Γ A} (h : Conv t u) : nf t = nf u :=
  (reflect_reify_eq A).2.2.1 (eval_conv h (idEnv_eq Γ))

/-- **βη-conversion is equality of normal forms.** -/
theorem conv_iff_nf_eq {Γ : Ctx} {A : Ty} (t u : Tm Γ A) : Conv t u ↔ nf t = nf u :=
  ⟨nf_complete, fun h => Conv.trans (nf_sound t) (h ▸ Conv.symm (nf_sound u))⟩

/-- **βη-conversion of well-typed terms is decidable**, by comparing normal forms. -/
instance decidableConv {Γ : Ctx} {A : Ty} (t u : Tm Γ A) : Decidable (Conv t u) :=
  decidable_of_iff _ (conv_iff_nf_eq t u).symm

end StlcNbE
