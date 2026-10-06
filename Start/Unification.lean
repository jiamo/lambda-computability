/-
**First-order unification**: Robinson's algorithm, the most general unifier, and correct failure.

The terms are the monotypes of Hindley–Milner (`Start/HindleyMilner.lean`): type variables, type
constants, and the binary arrow.  This is first-order term unification over the signature with one
binary symbol and countably many constants; it is exactly the unification problem that type
inference has to solve.

* `HM.Ty` — terms (monotypes), with `HM.Ty.subst`, `HM.Ty.vars`, `HM.Ty.size`;
* `HM.unify` — the algorithm on a list of equations, by well-founded recursion on the number of
  variables and the size of the problem (it terminates on every input, so it is a total function);
* `HM.unify_sound` — a returned substitution unifies every equation;
* `HM.unify_mgu` — and it is **most general**: every unifier `s'` factors through it, in the strong
  form `s' = s' ∘ u` (so `s'` is `u` followed by `s'` itself);
* `HM.unify_none` — **correct failure**: if the algorithm fails, no substitution unifies the
  equations (a clash of constructors, or the occurs check);
* `HM.unify_vars` — the unifier introduces no new variables: every variable of `u v` is `v` or a
  variable of the problem.  Type inference needs this to keep its supply of fresh variables fresh;
* `HM.mgu` — the two-term interface, with `HM.mgu_sound`, `HM.mgu_most_general`, `HM.mgu_none`,
  and `HM.mgu_iff` (the algorithm succeeds exactly when a unifier exists).
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace HM

/-- Monotypes, which are also the first-order terms of the unification problem: variables,
constants, and the arrow. -/
inductive Ty where
  /-- A type variable. -/
  | var : ℕ → Ty
  /-- A type constant (a base type). -/
  | con : ℕ → Ty
  /-- A function type. -/
  | arrow : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Applying a substitution (a map from variables to types). -/
def subst (s : ℕ → Ty) : Ty → Ty
  | var v => s v
  | con c => con c
  | arrow a b => arrow (subst s a) (subst s b)

/-- The variables of a type. -/
def vars : Ty → Finset ℕ
  | var v => {v}
  | con _ => ∅
  | arrow a b => vars a ∪ vars b

/-- The size of a type. -/
def size : Ty → ℕ
  | var _ => 1
  | con _ => 1
  | arrow a b => size a + size b + 1

@[simp] theorem subst_var' (s : ℕ → Ty) (v : ℕ) : (var v).subst s = s v := rfl
@[simp] theorem subst_con (s : ℕ → Ty) (c : ℕ) : (con c).subst s = con c := rfl
@[simp] theorem subst_arrow (s : ℕ → Ty) (a b : Ty) :
    (arrow a b).subst s = arrow (a.subst s) (b.subst s) := rfl
@[simp] theorem vars_var (v : ℕ) : (var v).vars = {v} := rfl
@[simp] theorem vars_con (c : ℕ) : (con c).vars = ∅ := rfl
@[simp] theorem vars_arrow (a b : Ty) : (arrow a b).vars = a.vars ∪ b.vars := rfl

@[simp] theorem subst_id (t : Ty) : t.subst var = t := by
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [iha, ihb]

theorem subst_subst (s s' : ℕ → Ty) (t : Ty) :
    (t.subst s).subst s' = t.subst (fun v => (s v).subst s') := by
  induction t with
  | var v => rfl
  | con c => rfl
  | arrow a b iha ihb => simp [iha, ihb]

theorem subst_congr {s s' : ℕ → Ty} {t : Ty} (h : ∀ v ∈ t.vars, s v = s' v) :
    t.subst s = t.subst s' := by
  induction t with
  | var v => simpa using h v (by simp)
  | con c => rfl
  | arrow a b iha ihb =>
    simp only [subst_arrow, arrow.injEq]
    exact ⟨iha fun v hv => h v (by simp [hv]), ihb fun v hv => h v (by simp [hv])⟩

theorem mem_vars_subst {s : ℕ → Ty} {t : Ty} {w : ℕ} :
    w ∈ (t.subst s).vars ↔ ∃ v ∈ t.vars, w ∈ (s v).vars := by
  induction t with
  | var v => simp
  | con c => simp
  | arrow a b iha ihb =>
    simp only [subst_arrow, vars_arrow, Finset.mem_union, iha, ihb]
    constructor
    · rintro (⟨v, hv, h⟩ | ⟨v, hv, h⟩)
      · exact ⟨v, Or.inl hv, h⟩
      · exact ⟨v, Or.inr hv, h⟩
    · rintro ⟨v, hv | hv, h⟩
      · exact Or.inl ⟨v, hv, h⟩
      · exact Or.inr ⟨v, hv, h⟩

theorem size_pos (t : Ty) : 0 < t.size := by
  cases t <;> simp [size]

theorem size_le_subst {a : ℕ} {t : Ty} (s : ℕ → Ty) (ha : a ∈ t.vars) :
    (s a).size ≤ (t.subst s).size := by
  induction t with
  | var v => rw [vars_var, Finset.mem_singleton] at ha; subst ha; exact le_rfl
  | con c => simp at ha
  | arrow x y ihx ihy =>
    simp only [vars_arrow, Finset.mem_union] at ha
    simp only [subst_arrow, size]
    rcases ha with h | h
    · have := ihx h; omega
    · have := ihy h; omega

/-- The size argument behind the occurs check: a variable occurring properly inside `t` is mapped
by any substitution to something strictly smaller than the image of `t`. -/
theorem size_lt_subst {a : ℕ} {t : Ty} (s : ℕ → Ty) (ha : a ∈ t.vars) (hne : t ≠ var a) :
    (s a).size < (t.subst s).size := by
  cases t with
  | var v => rw [vars_var, Finset.mem_singleton] at ha; exact absurd (by rw [ha]) hne
  | con c => simp at ha
  | arrow x y =>
    simp only [vars_arrow, Finset.mem_union] at ha
    simp only [subst_arrow, size]
    rcases ha with h | h
    · have := size_le_subst s h; omega
    · have := size_le_subst s h; omega

end Ty

open Ty

/-- The substitution replacing the variable `a` by `t`. -/
def single (a : ℕ) (t : Ty) : ℕ → Ty := fun v => if v = a then t else var v

theorem subst_single_of_not_mem {a : ℕ} {t x : Ty} (ha : a ∉ x.vars) :
    x.subst (single a t) = x := by
  conv_rhs => rw [← subst_id x]
  apply subst_congr
  intro v hv
  have : v ≠ a := fun h => ha (h ▸ hv)
  simp [single, this]

theorem vars_subst_single {a : ℕ} {t x : Ty} (ha : a ∉ t.vars) :
    (x.subst (single a t)).vars ⊆ (x.vars ∪ t.vars).erase a := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := mem_vars_subst.1 hw
  by_cases hva : v = a
  · subst hva
    simp only [single, if_true] at hw
    exact Finset.mem_erase.2 ⟨fun h => ha (h ▸ hw), Finset.mem_union_right _ hw⟩
  · simp only [single, hva, if_false, vars_var, Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_erase.2 ⟨hva, Finset.mem_union_left _ hv⟩

/-- A unification problem: a list of equations. -/
abbrev Eqs := List (Ty × Ty)

/-- The variables of a unification problem. -/
def eqsVars : Eqs → Finset ℕ
  | [] => ∅
  | (a, b) :: E => a.vars ∪ b.vars ∪ eqsVars E

/-- The size of a unification problem. -/
def eqsSize : Eqs → ℕ
  | [] => 0
  | (a, b) :: E => a.size + b.size + eqsSize E

/-- Applying a substitution to both sides of every equation. -/
def substEqs (s : ℕ → Ty) (E : Eqs) : Eqs := E.map fun p => (p.1.subst s, p.2.subst s)

/-- `s` unifies every equation of `E`. -/
def Unifies (s : ℕ → Ty) (E : Eqs) : Prop := ∀ p ∈ E, p.1.subst s = p.2.subst s

@[simp] theorem eqsVars_nil : eqsVars [] = ∅ := rfl
@[simp] theorem eqsVars_cons (a b : Ty) (E : Eqs) :
    eqsVars ((a, b) :: E) = a.vars ∪ b.vars ∪ eqsVars E := rfl

theorem eqsVars_substEqs_single {a : ℕ} {t : Ty} (ha : a ∉ t.vars) (E : Eqs) :
    eqsVars (substEqs (single a t) E) ⊆ (eqsVars E ∪ t.vars).erase a := by
  induction E with
  | nil => simp [substEqs]
  | cons p E ih =>
    obtain ⟨x, y⟩ := p
    have ih' : eqsVars (substEqs (single a t) E) ⊆ (eqsVars E ∪ t.vars).erase a := ih
    change (x.subst (single a t)).vars ∪ (y.subst (single a t)).vars ∪
      eqsVars (substEqs (single a t) E) ⊆ _
    have hx := vars_subst_single (x := x) ha
    have hy := vars_subst_single (x := y) ha
    intro w hw
    simp only [Finset.mem_union] at hw
    rcases hw with (hw | hw) | hw
    · have := hx hw; simp only [Finset.mem_erase, Finset.mem_union] at this ⊢
      simp only [eqsVars_cons, Finset.mem_union]; tauto
    · have := hy hw; simp only [Finset.mem_erase, Finset.mem_union] at this ⊢
      simp only [eqsVars_cons, Finset.mem_union]; tauto
    · have := ih' hw; simp only [Finset.mem_erase, Finset.mem_union] at this ⊢
      simp only [eqsVars_cons, Finset.mem_union]; tauto

theorem card_elim_lt {a : ℕ} {t : Ty} (ha : a ∉ t.vars) (E : Eqs) (S : Finset ℕ)
    (haS : a ∈ S) (hS : eqsVars E ∪ t.vars ⊆ S) :
    (eqsVars (substEqs (single a t) E)).card < S.card := by
  calc (eqsVars (substEqs (single a t) E)).card ≤ ((eqsVars E ∪ t.vars).erase a).card :=
        Finset.card_le_card (eqsVars_substEqs_single ha E)
    _ ≤ (S.erase a).card := Finset.card_le_card (Finset.erase_subset_erase _ hS)
    _ < S.card := Finset.card_erase_lt_of_mem haS

/-- The lexicographic measure of a unification problem. -/
def eqsMeasure (E : Eqs) : ℕ ×ₗ ℕ := toLex ((eqsVars E).card, eqsSize E)

/-- **Robinson's unification algorithm** on a list of equations.  It returns a unifier or fails;
termination is by the number of variables, then the size of the problem. -/
def unify : Eqs → Option (ℕ → Ty)
  | [] => some var
  | (var a, t) :: E =>
      if t = var a then unify E
      else if a ∈ t.vars then none
      else (unify (substEqs (single a t) E)).map fun u v => (single a t v).subst u
  | (con c, var a) :: E =>
      (unify (substEqs (single a (con c)) E)).map fun u v => (single a (con c) v).subst u
  | (arrow x y, var a) :: E =>
      if a ∈ (arrow x y).vars then none
      else (unify (substEqs (single a (arrow x y)) E)).map
        fun u v => (single a (arrow x y) v).subst u
  | (con c, con d) :: E => if c = d then unify E else none
  | (con _, arrow _ _) :: _ => none
  | (arrow _ _, con _) :: _ => none
  | (arrow x y, arrow x' y') :: E => unify ((x, x') :: (y, y') :: E)
termination_by E => eqsMeasure E
decreasing_by
  all_goals simp only [eqsMeasure]
  · -- `t = var a`: the variables do not increase and the size drops
    subst_vars
    rcases (Finset.card_le_card (show eqsVars E ⊆ eqsVars ((var a, var a) :: E) from
      Finset.subset_union_right)).lt_or_eq with h | h
    · rw [Prod.Lex.toLex_lt_toLex]; left; exact h
    · rw [Prod.Lex.toLex_lt_toLex]; right; refine ⟨h, ?_⟩
      simp [eqsSize, size]
  · rw [Prod.Lex.toLex_lt_toLex]; left
    apply card_elim_lt (by assumption) E
    · simp
    · intro w hw; simp only [Finset.mem_union] at hw ⊢; simp only [eqsVars_cons,
        Finset.mem_union]; tauto
  · rw [Prod.Lex.toLex_lt_toLex]; left
    apply card_elim_lt (by simp) E
    · simp
    · intro w hw; simp only [Finset.mem_union] at hw ⊢; simp only [eqsVars_cons,
        Finset.mem_union]; tauto
  · rw [Prod.Lex.toLex_lt_toLex]; left
    apply card_elim_lt (by assumption) E
    · simp
    · intro w hw; simp only [Finset.mem_union] at hw ⊢; simp only [eqsVars_cons,
        Finset.mem_union]; tauto
  · rcases (Finset.card_le_card (show eqsVars E ⊆ eqsVars ((con c, con c) :: E) from
      Finset.subset_union_right)).lt_or_eq with h | h
    · rw [Prod.Lex.toLex_lt_toLex]; left; exact h
    · rw [Prod.Lex.toLex_lt_toLex]; right; refine ⟨h, ?_⟩
      simp [eqsSize, size]
  · rw [Prod.Lex.toLex_lt_toLex]; right
    refine ⟨?_, ?_⟩
    · simp only [eqsVars_cons, vars_arrow]
      congr 1
      ext w; simp only [Finset.mem_union]; tauto
    · simp [eqsSize, size]; omega

theorem unifies_cons {s : ℕ → Ty} {x y : Ty} {E : Eqs} :
    Unifies s ((x, y) :: E) ↔ x.subst s = y.subst s ∧ Unifies s E := by
  simp [Unifies]

theorem eqsVars_mem_of_mem {p : Ty × Ty} {E : Eqs} (hp : p ∈ E) :
    p.1.vars ∪ p.2.vars ⊆ eqsVars E := by
  induction E with
  | nil => simp at hp
  | cons q E ih =>
    obtain ⟨x, y⟩ := q
    rcases List.mem_cons.1 hp with rfl | hp
    · intro w hw; simp only [eqsVars_cons, Finset.mem_union] at hw ⊢; tauto
    · exact (ih hp).trans Finset.subset_union_right

/-- What the algorithm guarantees on a problem: a returned substitution is a unifier, is most
general, and introduces no new variables; failure means there is no unifier. -/
def UnifySpec (E : Eqs) : Prop :=
  (∀ u, unify E = some u →
      Unifies u E ∧ (∀ s', Unifies s' E → ∀ v, (u v).subst s' = s' v) ∧
        ∀ v, (u v).vars ⊆ insert v (eqsVars E)) ∧
    (unify E = none → ∀ s, ¬ Unifies s E)

theorem subst_single_subst {a : ℕ} {t : Ty} {s' : ℕ → Ty} (h : s' a = t.subst s') (v : ℕ) :
    (single a t v).subst s' = s' v := by
  by_cases hv : v = a
  · subst hv; simp [single, h]
  · simp [single, hv]

/-- The elimination step `a ↦ t` of the algorithm preserves the specification. -/
theorem unifySpec_elim {a : ℕ} {t : Ty} {E E₀ : Eqs} (ha : a ∉ t.vars)
    (hspec : UnifySpec (substEqs (single a t) E))
    (hU : ∀ s, Unifies s E₀ ↔ Unifies s ((var a, t) :: E))
    (hV : eqsVars E₀ = eqsVars ((var a, t) :: E))
    (hrun : unify E₀ = (unify (substEqs (single a t) E)).map fun u v => (single a t v).subst u) :
    UnifySpec E₀ := by
  -- a unifier of the whole problem unifies the reduced problem
  have hred : ∀ s', Unifies s' ((var a, t) :: E) → Unifies s' (substEqs (single a t) E) := by
    intro s' hs' p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hst := (unifies_cons.1 hs').1
    have hfun : (fun v => (single a t v).subst s') = s' :=
      funext (subst_single_subst (by simpa using hst))
    simp only [subst_subst, hfun]
    exact (unifies_cons.1 hs').2 q hq
  refine ⟨fun w hw => ?_, fun hw s hs => ?_⟩
  · rw [hrun] at hw
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hw
    obtain ⟨hu1, hu2, hu3⟩ := hspec.1 u hu
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, unifies_cons]
      refine ⟨?_, ?_⟩
      · rw [subst_var', ← subst_subst, subst_single_of_not_mem ha]
        simp [single]
      · intro p hp
        have := hu1 _ (List.mem_map_of_mem (f := fun p => (p.1.subst (single a t),
          p.2.subst (single a t))) hp)
        simpa [subst_subst] using this
    · intro s' hs' v
      rw [hU] at hs'
      have hst : s' a = t.subst s' := by simpa using (unifies_cons.1 hs').1
      have h2 := hu2 s' (hred s' hs')
      rw [subst_subst, show (fun x => (u x).subst s') = s' from funext h2]
      exact subst_single_subst hst v
    · intro v x hx
      rw [hV]
      have hsub := eqsVars_substEqs_single ha E
      by_cases hva : v = a
      · subst hva
        simp only [single, if_true] at hx
        obtain ⟨y, hy, hxy⟩ := mem_vars_subst.1 hx
        have := hu3 y hxy
        rcases Finset.mem_insert.1 this with rfl | h
        · simp [hy]
        · have := hsub h
          simp only [Finset.mem_erase, Finset.mem_union] at this
          simp only [Finset.mem_insert, eqsVars_cons, vars_var, Finset.mem_union,
            Finset.mem_singleton]; tauto
      · simp only [single, hva, if_false, subst_var'] at hx
        have := hu3 v hx
        rcases Finset.mem_insert.1 this with rfl | h
        · simp
        · have := hsub h
          simp only [Finset.mem_erase, Finset.mem_union] at this
          simp only [Finset.mem_insert, eqsVars_cons, vars_var, Finset.mem_union,
            Finset.mem_singleton]; tauto
  · rw [hrun, Option.map_eq_none_iff] at hw
    exact hspec.2 hw s (hred s ((hU s).1 hs))

theorem unifySpec (E : Eqs) : UnifySpec E := by
  induction E using unify.induct with
  | case1 =>
    refine ⟨fun u hu => ?_, fun h => by simp [unify] at h⟩
    simp only [unify, Option.some.injEq] at hu; subst hu
    exact ⟨fun p hp => by simp at hp, fun s' _ v => rfl, fun v => by simp⟩
  | case2 a E ih =>
    have hrun : unify ((var a, var a) :: E) = unify E := by simp [unify]
    refine ⟨fun u hu => ?_, fun h s hs => ?_⟩
    · rw [hrun] at hu
      obtain ⟨h1, h2, h3⟩ := ih.1 u hu
      refine ⟨unifies_cons.2 ⟨rfl, h1⟩, fun s' hs' => h2 s' (unifies_cons.1 hs').2,
        fun v => (h3 v).trans (Finset.insert_subset_insert _ Finset.subset_union_right)⟩
    · rw [hrun] at h
      exact ih.2 h s (unifies_cons.1 hs).2
  | case3 a t E hne hocc =>
    refine ⟨fun u hu => by simp [unify, hne, hocc] at hu, fun _ s hs => ?_⟩
    have h := (unifies_cons.1 hs).1
    simp only [subst_var'] at h
    have := Ty.size_lt_subst s hocc hne
    rw [h] at this; exact lt_irrefl _ this
  | case4 a t E hne hocc ih =>
    exact unifySpec_elim hocc ih (fun _ => Iff.rfl) rfl (by simp [unify, hne, hocc])
  | case5 c a E ih =>
    refine unifySpec_elim (by simp) ih (fun s => ?_) ?_ (by simp [unify])
    · simp only [unifies_cons]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩
    · simp only [eqsVars_cons]; ext w; simp only [Finset.mem_union]; tauto
  | case6 x y a E hocc =>
    refine ⟨fun u hu => ?_, fun _ s hs => ?_⟩
    · simp only [unify, hocc, if_true] at hu
      cases hu
    have h := (unifies_cons.1 hs).1
    simp only [subst_var'] at h
    have := Ty.size_lt_subst s hocc (by simp)
    rw [← h] at this; exact lt_irrefl _ this
  | case7 x y a E hocc ih =>
    refine unifySpec_elim hocc ih (fun s => ?_) ?_ (by simp only [unify, hocc, if_false])
    · simp only [unifies_cons]; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2⟩
    · simp only [eqsVars_cons]; ext w; simp only [Finset.mem_union]; tauto
  | case8 d E ih =>
    have hrun : unify ((con d, con d) :: E) = unify E := by simp [unify]
    refine ⟨fun u hu => ?_, fun h s hs => ?_⟩
    · rw [hrun] at hu
      obtain ⟨h1, h2, h3⟩ := ih.1 u hu
      refine ⟨unifies_cons.2 ⟨rfl, h1⟩, fun s' hs' => h2 s' (unifies_cons.1 hs').2,
        fun v => (h3 v).trans (Finset.insert_subset_insert _ Finset.subset_union_right)⟩
    · rw [hrun] at h
      exact ih.2 h s (unifies_cons.1 hs).2
  | case9 c d E hne =>
    refine ⟨fun u hu => by simp [unify, hne] at hu, fun _ s hs => ?_⟩
    have h := (unifies_cons.1 hs).1
    simp only [subst_con, con.injEq] at h; exact hne h
  | case10 c x y E =>
    refine ⟨fun u hu => by simp [unify] at hu, fun _ s hs => ?_⟩
    have h := (unifies_cons.1 hs).1
    simp at h
  | case11 x y c E =>
    refine ⟨fun u hu => by simp [unify] at hu, fun _ s hs => ?_⟩
    have h := (unifies_cons.1 hs).1
    simp at h
  | case12 x y x' y' E ih =>
    have hrun : unify ((arrow x y, arrow x' y') :: E) = unify ((x, x') :: (y, y') :: E) := by
      simp [unify]
    have hU : ∀ s, Unifies s ((arrow x y, arrow x' y') :: E) ↔
        Unifies s ((x, x') :: (y, y') :: E) := by
      intro s; simp only [unifies_cons, subst_arrow, arrow.injEq, and_assoc]
    have hV : eqsVars ((arrow x y, arrow x' y') :: E) = eqsVars ((x, x') :: (y, y') :: E) := by
      simp only [eqsVars_cons, vars_arrow]; ext w; simp only [Finset.mem_union]; tauto
    refine ⟨fun u hu => ?_, fun h s hs => ?_⟩
    · rw [hrun] at hu
      obtain ⟨h1, h2, h3⟩ := ih.1 u hu
      exact ⟨(hU u).2 h1, fun s' hs' => h2 s' ((hU s').1 hs'), fun v => hV ▸ h3 v⟩
    · rw [hrun] at h
      exact ih.2 h s ((hU s).1 hs)

/-- **Soundness**: a substitution returned by `unify` unifies every equation. -/
theorem unify_sound {E : Eqs} {u : ℕ → Ty} (h : unify E = some u) : Unifies u E :=
  ((unifySpec E).1 u h).1

/-- **Most generality**: every unifier `s'` of `E` factors through the computed unifier `u`, as
`s' = s' ∘ u`. -/
theorem unify_mgu {E : Eqs} {u : ℕ → Ty} (h : unify E = some u) {s' : ℕ → Ty}
    (hs' : Unifies s' E) (v : ℕ) : (u v).subst s' = s' v :=
  ((unifySpec E).1 u h).2.1 s' hs' v

/-- The computed unifier introduces no new variables. -/
theorem unify_vars {E : Eqs} {u : ℕ → Ty} (h : unify E = some u) (v : ℕ) :
    (u v).vars ⊆ insert v (eqsVars E) :=
  ((unifySpec E).1 u h).2.2 v

/-- **Correct failure**: if `unify` fails, there is no unifier at all. -/
theorem unify_none {E : Eqs} (h : unify E = none) (s : ℕ → Ty) : ¬ Unifies s E :=
  (unifySpec E).2 h s

/-- `unify` succeeds exactly on the unifiable problems. -/
theorem unify_isSome_iff (E : Eqs) : (unify E).isSome ↔ ∃ s, Unifies s E := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h
    exact ⟨u, unify_sound hu⟩
  · rintro ⟨s, hs⟩
    cases h : unify E with
    | none => exact absurd hs (unify_none h s)
    | some u => rfl

/-! ### Two terms -/

/-- The most general unifier of two types, if they are unifiable. -/
def mgu (t₁ t₂ : Ty) : Option (ℕ → Ty) := unify [(t₁, t₂)]

theorem mgu_sound {t₁ t₂ : Ty} {u : ℕ → Ty} (h : mgu t₁ t₂ = some u) :
    t₁.subst u = t₂.subst u :=
  unify_sound h _ (List.mem_singleton_self _)

theorem mgu_most_general {t₁ t₂ : Ty} {u : ℕ → Ty} (h : mgu t₁ t₂ = some u) {s' : ℕ → Ty}
    (hs' : t₁.subst s' = t₂.subst s') (v : ℕ) : (u v).subst s' = s' v :=
  unify_mgu h (by simpa [Unifies] using hs') v

theorem mgu_vars {t₁ t₂ : Ty} {u : ℕ → Ty} (h : mgu t₁ t₂ = some u) (v : ℕ) :
    (u v).vars ⊆ insert v (t₁.vars ∪ t₂.vars) := by
  have := unify_vars h v
  simpa [eqsVars] using this

theorem mgu_none {t₁ t₂ : Ty} (h : mgu t₁ t₂ = none) (s : ℕ → Ty) :
    t₁.subst s ≠ t₂.subst s := fun hs =>
  unify_none h s (by simpa [Unifies] using hs)

/-- **Unification is decided by `mgu`**: it succeeds exactly when the two types have a unifier,
and then it returns a most general one. -/
theorem mgu_iff (t₁ t₂ : Ty) :
    (∃ s, t₁.subst s = t₂.subst s) ↔
      ∃ u, mgu t₁ t₂ = some u ∧ t₁.subst u = t₂.subst u ∧
        ∀ s', t₁.subst s' = t₂.subst s' → ∀ v, (u v).subst s' = s' v := by
  constructor
  · rintro ⟨s, hs⟩
    cases h : mgu t₁ t₂ with
    | none => exact absurd hs (mgu_none h s)
    | some u => exact ⟨u, rfl, mgu_sound h, fun s' hs' => mgu_most_general h hs'⟩
  · rintro ⟨u, -, hu, -⟩
    exact ⟨u, hu⟩

/-! ### Sanity checks -/

/-- The occurs check: `α ≐ α → β` has no unifier. -/
theorem not_unifiable_occurs (s : ℕ → Ty) :
    (var 0).subst s ≠ (arrow (var 0) (var 1)).subst s := by
  intro h
  have := Ty.size_lt_subst s (a := 0) (t := arrow (var 0) (var 1)) (by simp) (by simp)
  rw [← h] at this; exact lt_irrefl _ this

example : (mgu (arrow (var 0) (con 0)) (arrow (con 1) (var 1))).isSome = true :=
  (unify_isSome_iff _).2 ⟨fun v => if v = 0 then con 1 else con 0, fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; simp⟩

example : mgu (var 0) (arrow (var 0) (var 1)) = none := by
  cases h : mgu (var 0) (arrow (var 0) (var 1)) with
  | none => rfl
  | some u => exact absurd (mgu_sound h) (not_unifiable_occurs u)

end HM
