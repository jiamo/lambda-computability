/-
**Normalization by evaluation for the simply typed λ-calculus** — task `M23-NBE-STLC` (round 6,
part F).

For the intrinsically typed calculus of `Start/Stlc.lean` (a base type, unit, products and
functions, with typed βη-conversion `Stlc.Conv`):

* `StlcNbE.Sem A Γ` — the **Kripke model of presheaves on context renamings**: at the base type the
  terms of base type, at `unit` a point, at products pairs, and at `A ⇒ B` the Kripke function
  space `∀ Δ, Ren Γ Δ → Sem A Δ → Sem B Δ`; `StlcNbE.Sem.ren` is the presheaf action;
* `StlcNbE.eval` — evaluation of a term in a semantic environment;
* `StlcNbE.reflect`, `StlcNbE.reify` — reflection of terms and reification of semantic values
  (η-expanding at function, product and unit types);
* `StlcNbE.nf` — the normalization function, `reify (eval t id)`;
* `StlcNbE.R` — the Kripke logical relation between terms and semantic values;
* `StlcNbE.reflect_reify` — reflection is related, and reification of a related value is
  convertible to the term;
* `StlcNbE.fundamental` — every substitution instance of a term is related to its evaluation in a
  related environment;
* `StlcNbE.nf_sound` — **soundness**: `Γ ⊢ t ≡βη nf t : A`.

Completeness (`Γ ⊢ t ≡βη u : A → nf t = nf u`) and the decidability corollary are proved in
`Start/StlcNbEComplete.lean`.
-/

import Start.Stlc

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace StlcNbE

open Stlc

/-! ### The Kripke model -/

/-- **Semantic values**, a presheaf on renamings for each type. -/
def Sem : Ty → Ctx → Type
  | .base, Γ => Tm Γ .base
  | .unit, _ => PUnit
  | .prod A B, Γ => Sem A Γ × Sem B Γ
  | .arrow A B, Γ => ∀ Δ : Ctx, Ren Γ Δ → Sem A Δ → Sem B Δ

/-- The presheaf action of a renaming on semantic values. -/
def Sem.ren : ∀ {A : Ty} {Γ Δ : Ctx}, Ren Γ Δ → Sem A Γ → Sem A Δ
  | .base, _, _, r, t => Stlc.ren r t
  | .unit, _, _, _, _ => PUnit.unit
  | .prod _ _, _, _, r, p => (Sem.ren r p.1, Sem.ren r p.2)
  | .arrow _ _, _, _, r, f => fun Θ r' a => f Θ (r'.comp r) a

mutual
/-- **Reflection** of a term as a semantic value (η-expanding). -/
def reflect : ∀ (A : Ty) {Γ : Ctx}, Tm Γ A → Sem A Γ
  | .base, _, t => t
  | .unit, _, _ => PUnit.unit
  | .prod A B, _, t => (reflect A (Tm.fst t), reflect B (Tm.snd t))
  | .arrow A B, _, t => fun _ r a => reflect B (Tm.app (Stlc.ren r t) (reify A a))

/-- **Reification** of a semantic value as a term (η-long). -/
def reify : ∀ (A : Ty) {Γ : Ctx}, Sem A Γ → Tm Γ A
  | .base, _, v => v
  | .unit, _, _ => Tm.star
  | .prod A B, _, p => Tm.pair (reify A p.1) (reify B p.2)
  | .arrow A B, Γ, f => Tm.lam (reify B (f (A :: Γ) (Ren.wk A) (reflect A (Tm.var Var.zero))))
end

/-- Semantic environments. -/
def Env (Γ Δ : Ctx) : Type := ∀ A : Ty, Var Γ A → Sem A Δ

/-- The action of a renaming on environments. -/
def Env.ren {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (ρ : Env Γ Δ) : Env Γ Θ := fun _ v => Sem.ren r (ρ _ v)

/-- Extending an environment. -/
def Env.cons {Γ Δ : Ctx} {A : Ty} (a : Sem A Δ) (ρ : Env Γ Δ) : Env (A :: Γ) Δ := fun _ v =>
  match v with
  | Var.zero => a
  | Var.succ v => ρ _ v

/-- **Evaluation.** -/
def eval : ∀ {Γ : Ctx} {A : Ty}, Tm Γ A → ∀ {Δ : Ctx}, Env Γ Δ → Sem A Δ
  | _, _, Tm.var v, _, ρ => ρ _ v
  | _, _, Tm.app f a, Δ, ρ => eval f ρ Δ (Ren.id Δ) (eval a ρ)
  | _, _, Tm.lam t, _, ρ => fun _ r a => eval t (Env.cons a (Env.ren r ρ))
  | _, _, Tm.star, _, _ => PUnit.unit
  | _, _, Tm.pair a b, _, ρ => (eval a ρ, eval b ρ)
  | _, _, Tm.fst t, _, ρ => (eval t ρ).1
  | _, _, Tm.snd t, _, ρ => (eval t ρ).2

/-- The identity environment: every variable reflected. -/
def idEnv (Γ : Ctx) : Env Γ Γ := fun A v => reflect A (Tm.var v)

/-- **The normalization function.** -/
def nf {Γ : Ctx} {A : Ty} (t : Tm Γ A) : Tm Γ A := reify A (eval t (idEnv Γ))

/-! ### The logical relation -/

/-- **The Kripke logical relation** between terms and semantic values. -/
def R : ∀ (A : Ty) {Γ : Ctx}, Tm Γ A → Sem A Γ → Prop
  | .base, _, t, v => Conv t v
  | .unit, _, _, _ => True
  | .prod A B, _, t, p => R A (Tm.fst t) p.1 ∧ R B (Tm.snd t) p.2
  | .arrow A B, Γ, t, f => ∀ (Δ : Ctx) (r : Ren Γ Δ) (s : Tm Δ A) (a : Sem A Δ),
      R A s a → R B (Tm.app (Stlc.ren r t) s) (f Δ r a)

/-- The relation is closed under conversion of the term. -/
theorem R.conv : ∀ (A : Ty) {Γ : Ctx} {t t' : Tm Γ A} {v : Sem A Γ}, Conv t t' → R A t v →
    R A t' v
  | .base, _, _, _, _, h, hv => Conv.trans (Conv.symm h) hv
  | .unit, _, _, _, _, _, _ => trivial
  | .prod A B, _, _, _, _, h, hv => ⟨R.conv A (Conv.fst h) hv.1, R.conv B (Conv.snd h) hv.2⟩
  | .arrow _ B, _, _, _, _, h, hv => fun Δ r s a ha =>
      R.conv B (Conv.app (h.ren r) (Conv.refl s)) (hv Δ r s a ha)

/-- The relation is stable under renaming. -/
theorem R.ren : ∀ (A : Ty) {Γ Δ : Ctx} (r : Ren Γ Δ) {t : Tm Γ A} {v : Sem A Γ}, R A t v →
    R A (Stlc.ren r t) (Sem.ren r v)
  | .base, _, _, r, _, _, hv => Conv.ren hv r
  | .unit, _, _, _, _, _, _ => trivial
  | .prod A B, _, _, r, _, _, hv => ⟨R.ren A r hv.1, R.ren B r hv.2⟩
  | .arrow _ _, _, _, r, t, _, hv => fun Θ r' s a ha => by
      have h := hv Θ (r'.comp r) s a ha
      rw [← ren_ren] at h
      exact h

/-- **Reflection and reification**: reflected terms are related, and a related value reifies to
a term convertible to the original. -/
theorem reflect_reify : ∀ (A : Ty),
    (∀ {Γ : Ctx} (t : Tm Γ A), R A t (reflect A t)) ∧
      ∀ {Γ : Ctx} (t : Tm Γ A) (a : Sem A Γ), R A t a → Conv t (reify A a)
  | .base => ⟨fun t => Conv.refl t, fun _ _ h => h⟩
  | .unit => ⟨fun _ => trivial, fun t _ _ => Conv.unit_eta t⟩
  | .prod A B =>
      ⟨fun t => ⟨(reflect_reify A).1 (Tm.fst t), (reflect_reify B).1 (Tm.snd t)⟩,
        fun t a h => Conv.trans (Conv.symm (Conv.pair_eta t))
          (Conv.pair ((reflect_reify A).2 _ _ h.1) ((reflect_reify B).2 _ _ h.2))⟩
  | .arrow A B =>
      ⟨fun t Δ r s a ha =>
          R.conv B (Conv.app (Conv.refl _) (Conv.symm ((reflect_reify A).2 s a ha)))
            ((reflect_reify B).1 _),
        fun {Γ} t f h => by
          have h1 := h (A :: Γ) (Ren.wk A) (Tm.var Var.zero) (reflect A (Tm.var Var.zero))
            ((reflect_reify A).1 _)
          exact Conv.trans (Conv.eta t) (Conv.lam ((reflect_reify B).2 _ _ h1))⟩

/-- The substitution behind the β-step of an evaluated abstraction. -/
theorem inst_ren_lift_sub_lift {Γ Δ Θ : Ctx} {A B : Ty} (σ : Sub Γ Δ) (r : Ren Δ Θ)
    (t : Tm (A :: Γ) B) (s : Tm Θ A) :
    inst (Stlc.ren (r.lift A) (sub (σ.lift A) t)) s = sub (Sub.cons s (Sub.renComp r σ)) t := by
  unfold inst
  rw [ren_sub, sub_sub]
  congr 1
  funext C v
  cases v with
  | zero => rfl
  | succ v =>
      change sub (Sub.single s) (Stlc.ren (r.lift A) (Stlc.ren (Ren.wk A) (σ C v))) =
        Stlc.ren r (σ C v)
      rw [ren_ren, sub_ren, ren_eq_sub]
      rfl

/-- **The fundamental lemma.** -/
theorem fundamental : ∀ {Γ : Ctx} {A : Ty} (t : Tm Γ A) {Δ : Ctx} (σ : Sub Γ Δ) (ρ : Env Γ Δ),
    (∀ (B : Ty) (v : Var Γ B), R B (σ B v) (ρ B v)) → R A (sub σ t) (eval t ρ)
  | _, _, Tm.var v, _, _, _, h => h _ v
  | _, _, Tm.app f a, Δ, σ, ρ, h => by
      have h1 := fundamental f σ ρ h Δ (Ren.id Δ) (sub σ a) (eval a ρ) (fundamental a σ ρ h)
      rw [ren_id] at h1
      exact h1
  | _, .arrow _ B, Tm.lam t, _, σ, ρ, h => by
      intro Θ r s a ha
      refine R.conv B (Conv.symm (Conv.beta _ s)) ?_
      rw [inst_ren_lift_sub_lift]
      refine fundamental t _ _ fun C v => ?_
      cases v with
      | zero => exact ha
      | succ v => exact R.ren C r (h C v)
  | _, _, Tm.star, _, _, _, _ => trivial
  | _, _, @Tm.pair _ A B a b, _, σ, ρ, h =>
      ⟨R.conv A (Conv.symm (Conv.fst_pair _ _)) (fundamental a σ ρ h),
        R.conv B (Conv.symm (Conv.snd_pair _ _)) (fundamental b σ ρ h)⟩
  | _, _, Tm.fst t, _, σ, ρ, h => (fundamental t σ ρ h).1
  | _, _, Tm.snd t, _, σ, ρ, h => (fundamental t σ ρ h).2

/-- **Soundness of normalization by evaluation**: every term is βη-convertible to its normal
form. -/
theorem nf_sound {Γ : Ctx} {A : Ty} (t : Tm Γ A) : Conv t (nf t) := by
  have h := fundamental t (Sub.id Γ) (idEnv Γ) fun B v => (reflect_reify B).1 (Tm.var v)
  rw [sub_id] at h
  exact (reflect_reify A).2 _ _ h

end StlcNbE
