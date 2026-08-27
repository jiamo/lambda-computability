/-
**Parametricity for System F** (Reynolds' abstraction theorem) and a free theorem.

`Start/SystemF.lean` interprets a type by a *unary* predicate on terms — a reducibility candidate —
and gets strong normalization.  Here the same type structure is interpreted by a *binary relation*
on terms, and the fundamental lemma becomes the abstraction theorem: a term of type `A` relates to
itself in the relational interpretation of `A`, for **every** choice of relations for the free type
variables.  Since the quantifier is interpreted by quantifying over all admissible relations, a
polymorphic term cannot inspect the type it is instantiated at, and equations about it follow from
its type alone.

The admissible relations here are those closed under β-conversion (`Lambda.Conv` of
`Start/Scott.lean`, joinability, which is β-conversion by the Church-Rosser theorem) in each
argument.  That is all the abstraction theorem needs — no normalization is used — and it is what
makes the β-rule invisible to the interpretation.

* `SystemF.Rel` — an admissible relation, `SystemF.rinterp` — the relational interpretation of a
  type, `SystemF.rinterp_conv` — it is again conversion-closed, and `SystemF.relOf` — packaged;
* `SystemF.rinterp_tyShift`, `SystemF.rinterp_tyInst` — the semantic weakening and substitution
  lemmas;
* **`SystemF.parametricity`** — the abstraction theorem, for open terms and parallel
  substitutions;
* **`SystemF.conv_app_of_typing_idTy`** — the free theorem for `∀ α. α → α`: a closed term of that
  type applied to any term `v` is β-convertible to `v`, so all closed terms of the polymorphic
  identity type behave like the identity (`SystemF.conv_app_of_typing_idTy'`).
-/

import Start.SystemFChurch
import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemF

open Lambda

/-! ### Admissible relations -/

/-- An **admissible relation**: a binary relation on terms closed under β-conversion in each
argument. -/
structure Rel where
  /-- The underlying relation. -/
  rel : Lambda → Lambda → Prop
  /-- Conversion-closure, in both arguments at once. -/
  conv : ∀ {a a' b b' : Lambda}, Lambda.Conv a a' → Lambda.Conv b b' → rel a b → rel a' b'

@[ext] theorem Rel.ext' {X Y : Rel} (h : X.rel = Y.rel) : X = Y := by
  cases X; cases Y; cases h; rfl

/-- Convertibility is a congruence for application. -/
theorem conv_app {a a' b b' : Lambda} (ha : Lambda.Conv a a') (hb : Lambda.Conv b b') :
    Lambda.Conv (Lambda.app a b) (Lambda.app a' b') := by
  obtain ⟨u, h1, h2⟩ := ha
  obtain ⟨v, h3, h4⟩ := hb
  exact ⟨Lambda.app u v, Lambda.reduces_app h1 h3, Lambda.reduces_app h2 h4⟩

/-- Extending a valuation of type variables by a relation. -/
def relScons (R : Rel) (rho : ℕ → Rel) : ℕ → Rel
  | 0 => R
  | n + 1 => rho n

/-! ### The relational interpretation of a type -/

/-- The relational interpretation of a type in a valuation of its free type variables by
admissible relations.  The quantifier ranges over *all* admissible relations: this is
parametricity. -/
def rinterp : FTy → (ℕ → Rel) → Lambda → Lambda → Prop
  | FTy.var i, rho => (rho i).rel
  | FTy.arrow A B, rho => fun t t' =>
      ∀ u u' : Lambda, rinterp A rho u u' → rinterp B rho (Lambda.app t u) (Lambda.app t' u')
  | FTy.all A, rho => fun t t' => ∀ R : Rel, rinterp A (relScons R rho) t t'

@[simp] theorem rinterp_var (i : ℕ) (rho : ℕ → Rel) : rinterp (FTy.var i) rho = (rho i).rel := rfl

@[simp] theorem rinterp_arrow (A B : FTy) (rho : ℕ → Rel) (t t' : Lambda) :
    rinterp (FTy.arrow A B) rho t t' ↔
      ∀ u u', rinterp A rho u u' → rinterp B rho (Lambda.app t u) (Lambda.app t' u') := Iff.rfl

@[simp] theorem rinterp_all (A : FTy) (rho : ℕ → Rel) (t t' : Lambda) :
    rinterp (FTy.all A) rho t t' ↔ ∀ R : Rel, rinterp A (relScons R rho) t t' := Iff.rfl

/-- The relational interpretation of a type is again closed under conversion. -/
theorem rinterp_conv (A : FTy) :
    ∀ (rho : ℕ → Rel) {a a' b b' : Lambda}, Lambda.Conv a a' → Lambda.Conv b b' →
      rinterp A rho a b → rinterp A rho a' b' := by
  induction A with
  | var i => intro rho a a' b b' ha hb h; exact (rho i).conv ha hb h
  | arrow A B ihA ihB =>
      intro rho a a' b b' ha hb h u u' hu
      exact ihB rho (conv_app ha (Lambda.conv_refl u)) (conv_app hb (Lambda.conv_refl u'))
        (h u u' hu)
  | all A ihA =>
      intro rho a a' b b' ha hb h R
      exact ihA (relScons R rho) ha hb (h R)

/-- The relational interpretation of a type, packaged as an admissible relation. -/
def relOf (A : FTy) (rho : ℕ → Rel) : Rel where
  rel := rinterp A rho
  conv ha hb h := rinterp_conv A rho ha hb h

@[simp] theorem relOf_rel (A : FTy) (rho : ℕ → Rel) : (relOf A rho).rel = rinterp A rho := rfl

/-! ### Semantic weakening and substitution -/

theorem rinterp_tyRename (A : FTy) :
    ∀ (r : ℕ → ℕ) (rho : ℕ → Rel) (t t' : Lambda),
      rinterp (tyRename r A) rho t t' ↔ rinterp A (fun i => rho (r i)) t t' := by
  induction A with
  | var i => intro r rho t t'; exact Iff.rfl
  | arrow A B ihA ihB =>
      intro r rho t t'
      constructor
      · intro h u u' hu
        exact (ihB r rho _ _).1 (h u u' ((ihA r rho u u').2 hu))
      · intro h u u' hu
        exact (ihB r rho _ _).2 (h u u' ((ihA r rho u u').1 hu))
  | all A ihA =>
      intro r rho t t'
      have hval : ∀ R : Rel,
          (fun i => relScons R rho (upr r i)) = relScons R (fun i => rho (r i)) :=
        fun R => by
          funext i
          cases i with
          | zero => rfl
          | succ i => rfl
      constructor
      · intro h R
        have hR := (ihA (upr r) (relScons R rho) t t').1 (h R)
        rwa [hval R] at hR
      · intro h R
        refine (ihA (upr r) (relScons R rho) t t').2 ?_
        rw [hval R]
        exact h R

/-- **Semantic weakening**: a type not mentioning the fresh type variable is interpreted the same
way whatever relation is given to it. -/
theorem rinterp_tyShift (A : FTy) (R : Rel) (rho : ℕ → Rel) (t t' : Lambda) :
    rinterp (tyShift A) (relScons R rho) t t' ↔ rinterp A rho t t' := by
  rw [tyShift, rinterp_tyRename A Nat.succ (relScons R rho) t t']
  have hval : (fun i => relScons R rho (Nat.succ i)) = rho := funext fun _ => rfl
  rw [hval]

/-- **Semantic substitution**. -/
theorem rinterp_tySubst (A : FTy) :
    ∀ (s : ℕ → FTy) (rho : ℕ → Rel) (t t' : Lambda),
      rinterp (tySubst s A) rho t t' ↔ rinterp A (fun i => relOf (s i) rho) t t' := by
  induction A with
  | var i => intro s rho t t'; exact Iff.rfl
  | arrow A B ihA ihB =>
      intro s rho t t'
      constructor
      · intro h u u' hu
        exact (ihB s rho _ _).1 (h u u' ((ihA s rho u u').2 hu))
      · intro h u u' hu
        exact (ihB s rho _ _).2 (h u u' ((ihA s rho u u').1 hu))
  | all A ihA =>
      intro s rho t t'
      have hval : ∀ R : Rel, (fun i => relOf (ups s i) (relScons R rho))
          = relScons R (fun i => relOf (s i) rho) := by
        intro R
        funext i
        cases i with
        | zero => exact Rel.ext' rfl
        | succ i =>
            refine Rel.ext' ?_
            funext a b
            exact propext (rinterp_tyShift (s i) R rho a b)
      constructor
      · intro h R
        have hR := (ihA (ups s) (relScons R rho) t t').1 (h R)
        rwa [hval R] at hR
      · intro h R
        refine (ihA (ups s) (relScons R rho) t t').2 ?_
        rw [hval R]
        exact h R

/-- Instantiating a quantifier semantically. -/
theorem rinterp_tyInst (A B : FTy) (rho : ℕ → Rel) (t t' : Lambda) :
    rinterp (tyInst B A) rho t t' ↔ rinterp A (relScons (relOf B rho) rho) t t' := by
  rw [tyInst, rinterp_tySubst A (tyScons B) rho t t']
  have hval : (fun i => relOf (tyScons B i) rho) = relScons (relOf B rho) rho := by
    funext i
    cases i with
    | zero => exact Rel.ext' rfl
    | succ i => exact Rel.ext' rfl
  rw [hval]

/-! ### The abstraction theorem -/

/-- **Parametricity (Reynolds' abstraction theorem) for System F.**  A typable term relates to
itself in the relational interpretation of its type, under any pair of related substitutions and
any valuation of the free type variables by admissible relations. -/
theorem parametricity {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    ∀ (rho : ℕ → Rel) (u u' : ℕ → Lambda),
      (∀ i A', Γ[i]? = some A' → rinterp A' rho (u i) (u' i)) →
      rinterp A rho (substEnv u t) (substEnv u' t) := by
  induction h with
  | var hi => intro rho u u' hu; exact hu _ _ hi
  | app _ _ iha ihb =>
      intro rho u u' hu
      exact iha rho u u' hu _ _ (ihb rho u u' hu)
  | @lam Γ t A B _ ih =>
      intro rho u u' hu v v' hv
      have hsu : substEnv u (Lambda.lam t) = Lambda.lam (substEnv (envCons u) t) := rfl
      have hsu' : substEnv u' (Lambda.lam t) = Lambda.lam (substEnv (envCons u') t) := rfl
      rw [hsu, hsu']
      have hbody : rinterp B rho (substEnv (envScons v u) t) (substEnv (envScons v' u') t) := by
        refine ih rho (envScons v u) (envScons v' u') fun i A' hi => ?_
        cases i with
        | zero =>
            have hA : A = A' := by simpa using hi
            subst hA
            exact hv
        | succ i => exact hu i A' (by simpa using hi)
      rw [← subst_zero_substEnv, ← subst_zero_substEnv] at hbody
      exact rinterp_conv B rho (Lambda.conv_of_reduces Lambda.beta_reduces).symm
        (Lambda.conv_of_reduces Lambda.beta_reduces).symm hbody
  | @tlam Γ t A _ ih =>
      intro rho u u' hu R
      refine ih (relScons R rho) u u' fun i A' hi => ?_
      rw [List.getElem?_map] at hi
      match hΓ : Γ[i]? with
      | none => rw [hΓ] at hi; exact absurd hi (by simp)
      | some A₀ =>
          rw [hΓ] at hi
          have hA' : tyShift A₀ = A' := by simpa using hi
          subst hA'
          exact (rinterp_tyShift A₀ R rho (u i) (u' i)).2 (hu i A₀ hΓ)
  | @tapp Γ t A B _ ih =>
      intro rho u u' hu
      refine (rinterp_tyInst A B rho (substEnv u t) (substEnv u' t)).2 ?_
      exact ih rho u u' hu (relOf B rho)

/-- The abstraction theorem for a closed term. -/
theorem parametricity_closed {t : Lambda} {A : FTy} (h : Typing [] t A) (rho : ℕ → Rel) :
    rinterp A rho t t := by
  have hpar := parametricity h rho (fun k => Lambda.var k) (fun k => Lambda.var k)
    (by intro i A' hi; exact absurd hi (by simp))
  rwa [substEnv_var_id] at hpar

/-! ### A free theorem -/

/-- The relation "both sides are convertible to `v`", which is admissible. -/
def convRel (v : Lambda) : Rel where
  rel a b := Lambda.Conv a v ∧ Lambda.Conv b v
  conv ha hb h := ⟨ha.symm.trans h.1, hb.symm.trans h.2⟩

/-- **A free theorem.**  Every closed term of the polymorphic identity type `∀ α. α → α` acts as
the identity: applied to any term `v` it is β-convertible to `v`.  Nothing but the type of the term
is used. -/
theorem conv_app_of_typing_idTy {t : Lambda} (h : Typing [] t idTy) (v : Lambda) :
    Lambda.Conv (Lambda.app t v) v := by
  have hpar := parametricity_closed h (fun _ => convRel v) (convRel v)
  have hv : (convRel v).rel v v := ⟨Lambda.conv_refl v, Lambda.conv_refl v⟩
  exact (hpar v v hv).1

/-- Consequently any two closed terms of the polymorphic identity type are convertible at every
argument. -/
theorem conv_app_of_typing_idTy' {t s : Lambda} (ht : Typing [] t idTy) (hs : Typing [] s idTy)
    (v : Lambda) : Lambda.Conv (Lambda.app t v) (Lambda.app s v) :=
  (conv_app_of_typing_idTy ht v).trans (conv_app_of_typing_idTy hs v).symm

/-- The graph of a term `h`, as an admissible relation: `a` is related to `b` when `b` is
convertible to `h a`. -/
def graphRel (h : Lambda) : Rel where
  rel a b := Lambda.Conv b (Lambda.app h a)
  conv ha hb hr := hb.symm.trans (hr.trans (conv_app (Lambda.conv_refl h) ha))

/-- **The free theorem for the polymorphic numerals.**  A closed term of type
`∀ α. (α → α) → α → α` can only iterate its first argument, so it commutes with any `h`
intertwining `f` and `g`: if `h (f a)` is convertible to `g (h a)` for every `a`, then `h` maps the
result of iterating `f` from `x` to the result of iterating `g` from `h x`.  Only the type of `t`
is used. -/
theorem conv_iterate_of_typing_natTy {t : Lambda} (ht : Typing [] t natTy)
    (h f g x : Lambda) (hcomm : ∀ a : Lambda,
      Lambda.Conv (Lambda.app g (Lambda.app h a)) (Lambda.app h (Lambda.app f a))) :
    Lambda.Conv (Lambda.app (Lambda.app t g) (Lambda.app h x))
      (Lambda.app h (Lambda.app (Lambda.app t f) x)) := by
  have hpar := parametricity_closed ht (fun _ => graphRel h) (graphRel h)
  have hfg : ∀ u u' : Lambda, (graphRel h).rel u u' →
      (graphRel h).rel (Lambda.app f u) (Lambda.app g u') := by
    intro u u' hu
    change Lambda.Conv (Lambda.app g u') (Lambda.app h (Lambda.app f u))
    exact (conv_app (Lambda.conv_refl g) hu).trans (hcomm u)
  have hx : (graphRel h).rel x (Lambda.app h x) := Lambda.conv_refl _
  exact hpar f g hfg x (Lambda.app h x) hx

/-- Non-vacuity of the first free theorem: the identity is a closed term of the polymorphic
identity type. -/
theorem conv_app_I (v : Lambda) : Lambda.Conv (Lambda.app Lambda.I v) v :=
  conv_app_of_typing_idTy (typing_I []) v

/-- Non-vacuity of the second free theorem: it applies to every Church numeral. -/
theorem conv_iterate_church (n : ℕ) (h f g x : Lambda) (hcomm : ∀ a : Lambda,
    Lambda.Conv (Lambda.app g (Lambda.app h a)) (Lambda.app h (Lambda.app f a))) :
    Lambda.Conv (Lambda.app (Lambda.app (Lambda.church n) g) (Lambda.app h x))
      (Lambda.app h (Lambda.app (Lambda.app (Lambda.church n) f) x)) :=
  conv_iterate_of_typing_natTy (typing_church n) h f g x hcomm

end SystemF
