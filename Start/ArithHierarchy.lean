/-
**The arithmetical hierarchy.**

A predicate on the natural numbers is `Σ⁰ₙ` when it can be written with `n` alternating number
quantifiers, the outermost existential, in front of a computable matrix; it is `Π⁰ₙ` when the
outermost quantifier is universal instead.  This file defines the two families and develops their
structural theory:

* `Lambda.Arith.qAlt` — the alternating quantifier prefix, as a predicate transformer:
  `qAlt Bool.true n R` is `∃y₁ ∀y₂ ∃y₃ … R`, and `qAlt Bool.false n R` its dual.  The `n`
  witnesses are accumulated by pairing, so the matrix `R` is a predicate on a single number.
* `Lambda.Arith.SigmaAt`, `Lambda.Arith.PiAt`, `Lambda.Arith.DeltaAt` — the classes `Σ⁰ₙ`, `Π⁰ₙ`
  and `Δ⁰ₙ`.
* `Lambda.Arith.qAlt_not` — the prefix dualises: negating a prefix swaps every quantifier and the
  matrix; hence `Lambda.Arith.piAt_iff_sigmaAt_not`, `Lambda.Arith.sigmaAt_iff_piAt_not`.
* `Lambda.Arith.qAlt_shift` — substituting a computable function into the *base* argument of a
  prefix is again a prefix, over a shifted matrix.  This is the workhorse behind
  `Lambda.Arith.SigmaAt.subst` and `Lambda.Arith.PiAt.subst`, and behind the padding lemmas.
* `Lambda.Arith.SigmaAt.succ`, `Lambda.Arith.PiAt.succ`, `Lambda.Arith.SigmaAt.of_piAt`,
  `Lambda.Arith.PiAt.of_sigmaAt` — the inclusions `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁`.
* `Lambda.Arith.sigmaAt_succ_iff`, `Lambda.Arith.piAt_succ_iff` — peeling the outermost
  quantifier, the form in which the hierarchy is usually presented.
* `Lambda.Arith.SigmaAt.and`, `.or`, `.exists`, and the `Π` duals — the closure properties.
* `Lambda.Arith.sigmaAt_zero_iff`, `Lambda.Arith.piAt_zero_iff` — level `0` is the computable
  predicates, and `Lambda.Arith.sigmaAt_one_iff` — level `Σ⁰₁` is the recursively enumerable
  predicates.
-/

import Start.PostSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Arith

open Encodable Denumerable
open Nat.Partrec (Code)

/-! ## The alternating quantifier prefix -/

/-- `qAlt b n R x`: the `n`-fold alternating quantifier prefix applied to the matrix `R`, at the
base point `x`.  The outermost quantifier is existential when `b = true` and universal when
`b = false`, and each witness is appended to the running argument by `Nat.pair`. -/
def qAlt : Bool → ℕ → (ℕ → Prop) → ℕ → Prop
  | _, 0, R, x => R x
  | Bool.true, (n + 1), R, x => ∃ y, qAlt Bool.false n R (Nat.pair x y)
  | Bool.false, (n + 1), R, x => ∀ y, qAlt Bool.true n R (Nat.pair x y)

@[simp] theorem qAlt_zero (b : Bool) (R : ℕ → Prop) (x : ℕ) : qAlt b 0 R x ↔ R x := Iff.rfl

@[simp] theorem qAlt_true_succ (n : ℕ) (R : ℕ → Prop) (x : ℕ) :
    qAlt Bool.true (n + 1) R x ↔ ∃ y, qAlt Bool.false n R (Nat.pair x y) := Iff.rfl

@[simp] theorem qAlt_false_succ (n : ℕ) (R : ℕ → Prop) (x : ℕ) :
    qAlt Bool.false (n + 1) R x ↔ ∀ y, qAlt Bool.true n R (Nat.pair x y) := Iff.rfl

/-- **The prefix dualises.**  The negation of an alternating prefix is the opposite prefix over
the negated matrix. -/
theorem qAlt_not : ∀ (n : ℕ) (b : Bool) (R : ℕ → Prop) (x : ℕ),
    (¬ qAlt b n R x ↔ qAlt (!b) n (fun z => ¬ R z) x) := by
  classical
  intro n
  induction n with
  | zero => intro b R x; exact Iff.rfl
  | succ n ih =>
      intro b R x
      cases b with
      | true =>
          simp only [qAlt_true_succ, Bool.not_true, qAlt_false_succ, not_exists]
          exact forall_congr' fun y => ih Bool.false R (Nat.pair x y)
      | false =>
          simp only [qAlt_false_succ, Bool.not_false, qAlt_true_succ, not_forall]
          exact exists_congr fun y => ih Bool.true R (Nat.pair x y)

/-! ## The classes -/

/-- `P` is `Σ⁰ₙ`: it is an `n`-fold alternating prefix, outermost quantifier existential, over a
computable matrix. -/
def SigmaAt (n : ℕ) (P : ℕ → Prop) : Prop :=
  ∃ R : ℕ → Prop, ComputablePred R ∧ ∀ x, P x ↔ qAlt Bool.true n R x

/-- `P` is `Π⁰ₙ`: it is an `n`-fold alternating prefix, outermost quantifier universal, over a
computable matrix. -/
def PiAt (n : ℕ) (P : ℕ → Prop) : Prop :=
  ∃ R : ℕ → Prop, ComputablePred R ∧ ∀ x, P x ↔ qAlt Bool.false n R x

/-- `P` is `Δ⁰ₙ`: both `Σ⁰ₙ` and `Π⁰ₙ`. -/
def DeltaAt (n : ℕ) (P : ℕ → Prop) : Prop := SigmaAt n P ∧ PiAt n P

theorem SigmaAt.of_iff {n : ℕ} {P Q : ℕ → Prop} (h : SigmaAt n P) (hPQ : ∀ x, Q x ↔ P x) :
    SigmaAt n Q := by
  obtain ⟨R, hR, hP⟩ := h
  exact ⟨R, hR, fun x => (hPQ x).trans (hP x)⟩

theorem PiAt.of_iff {n : ℕ} {P Q : ℕ → Prop} (h : PiAt n P) (hPQ : ∀ x, Q x ↔ P x) : PiAt n Q := by
  obtain ⟨R, hR, hP⟩ := h
  exact ⟨R, hR, fun x => (hPQ x).trans (hP x)⟩

/-! ## Duality -/

theorem piAt_iff_sigmaAt_not {n : ℕ} {P : ℕ → Prop} :
    PiAt n P ↔ SigmaAt n fun x => ¬ P x := by
  classical
  constructor
  · rintro ⟨R, hR, hP⟩
    refine ⟨fun z => ¬ R z, hR.not, fun x => ?_⟩
    have h := qAlt_not n Bool.false R x
    simp only [Bool.not_false] at h
    rw [← h]
    exact not_congr (hP x)
  · rintro ⟨R, hR, hP⟩
    refine ⟨fun z => ¬ R z, hR.not, fun x => ?_⟩
    have h := qAlt_not n Bool.true R x
    simp only [Bool.not_true] at h
    rw [← h, ← hP x, not_not]

theorem sigmaAt_iff_piAt_not {n : ℕ} {P : ℕ → Prop} :
    SigmaAt n P ↔ PiAt n fun x => ¬ P x := by
  classical
  constructor
  · rintro ⟨R, hR, hP⟩
    refine ⟨fun z => ¬ R z, hR.not, fun x => ?_⟩
    have h := qAlt_not n Bool.true R x
    simp only [Bool.not_true] at h
    rw [← h]
    exact not_congr (hP x)
  · rintro ⟨R, hR, hP⟩
    refine ⟨fun z => ¬ R z, hR.not, fun x => ?_⟩
    have h := qAlt_not n Bool.false R x
    simp only [Bool.not_false] at h
    rw [← h, ← hP x, not_not]

/-! ## Substituting into the base argument -/

/-- Shifting a base substitution `f` past `i` appended witnesses. -/
def shiftAt (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => f
  | (i + 1) => fun w => Nat.pair (shiftAt f i w.unpair.1) w.unpair.2

@[simp] theorem shiftAt_zero (f : ℕ → ℕ) : shiftAt f 0 = f := rfl

theorem shiftAt_succ_pair (f : ℕ → ℕ) (i w y : ℕ) :
    shiftAt f (i + 1) (Nat.pair w y) = Nat.pair (shiftAt f i w) y := by
  simp [shiftAt]

theorem shiftAt_succ_eq (f : ℕ → ℕ) : ∀ i : ℕ, shiftAt f (i + 1) = shiftAt (shiftAt f 1) i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      funext w
      have hl : shiftAt f (i + 1 + 1) w
          = Nat.pair (shiftAt f (i + 1) w.unpair.1) w.unpair.2 := rfl
      have hr : shiftAt (shiftAt f 1) (i + 1) w
          = Nat.pair (shiftAt (shiftAt f 1) i w.unpair.1) w.unpair.2 := rfl
      rw [hl, hr, ih]

theorem computable_shiftAt {f : ℕ → ℕ} (hf : Computable f) :
    ∀ i : ℕ, Computable (shiftAt f i) := by
  intro i
  induction i with
  | zero => exact hf
  | succ i ih =>
      have hl : Computable fun w : ℕ => shiftAt f i w.unpair.1 :=
        ih.comp (Primrec.fst.comp Primrec.unpair).to_comp
      have hr : Computable fun w : ℕ => w.unpair.2 :=
        (Primrec.snd.comp Primrec.unpair).to_comp
      exact Primrec₂.natPair.to_comp.comp hl hr

/-- **Base substitution.**  A prefix over a matrix shifted by `f` is the prefix over the original
matrix, evaluated at `f x`. -/
theorem qAlt_shift : ∀ (n : ℕ) (R : ℕ → Prop) (f : ℕ → ℕ) (b : Bool) (x : ℕ),
    (qAlt b n (fun w => R (shiftAt f n w)) x ↔ qAlt b n R (f x)) := by
  intro n
  induction n with
  | zero => intro R f b x; exact Iff.rfl
  | succ n ih =>
      intro R f b x
      have h1 : (fun w => R (shiftAt f (n + 1) w)) = fun w => R (shiftAt (shiftAt f 1) n w) := by
        funext w; rw [shiftAt_succ_eq]
      have h2 : ∀ y : ℕ, shiftAt f 1 (Nat.pair x y) = Nat.pair (f x) y := by
        intro y; simp [shiftAt]
      cases b with
      | true =>
          simp only [qAlt_true_succ, h1]
          exact exists_congr fun y => by
            rw [ih R (shiftAt f 1) Bool.false (Nat.pair x y), h2 y]
      | false =>
          simp only [qAlt_false_succ, h1]
          exact forall_congr' fun y => by
            rw [ih R (shiftAt f 1) Bool.true (Nat.pair x y), h2 y]

/-- A computable predicate composed with a computable function is computable. -/
theorem computablePred_comp {P : ℕ → Prop} (hP : ComputablePred P) {f : ℕ → ℕ}
    (hf : Computable f) : ComputablePred fun x => P (f x) := by
  obtain ⟨g, hg, hPg⟩ := ComputablePred.computable_iff.1 hP
  subst hPg
  exact ComputablePred.computable_iff.2 ⟨fun x => g (f x), hg.comp hf, rfl⟩

theorem SigmaAt.subst {n : ℕ} {P : ℕ → Prop} (h : SigmaAt n P) {f : ℕ → ℕ} (hf : Computable f) :
    SigmaAt n fun x => P (f x) := by
  obtain ⟨R, hR, hP⟩ := h
  refine ⟨fun w => R (shiftAt f n w), computablePred_comp hR (computable_shiftAt hf n),
    fun x => ?_⟩
  exact (hP (f x)).trans (qAlt_shift n R f Bool.true x).symm

theorem PiAt.subst {n : ℕ} {P : ℕ → Prop} (h : PiAt n P) {f : ℕ → ℕ} (hf : Computable f) :
    PiAt n fun x => P (f x) := by
  obtain ⟨R, hR, hP⟩ := h
  refine ⟨fun w => R (shiftAt f n w), computablePred_comp hR (computable_shiftAt hf n),
    fun x => ?_⟩
  exact (hP (f x)).trans (qAlt_shift n R f Bool.false x).symm

/-! ## Padding: the inclusions `Σ⁰ₙ ∪ Π⁰ₙ ⊆ Δ⁰ₙ₊₁` -/

/-- Appending one innermost quantifier over a matrix that ignores the new witness changes
nothing. -/
theorem qAlt_dummy : ∀ (n : ℕ) (R : ℕ → Prop) (b : Bool) (x : ℕ),
    (qAlt b (n + 1) (fun w => R w.unpair.1) x ↔ qAlt b n R x) := by
  intro n
  induction n with
  | zero =>
      intro R b x
      cases b with
      | true => simp
      | false => simp
  | succ n ih =>
      intro R b x
      cases b with
      | true => exact exists_congr fun y => ih R Bool.false (Nat.pair x y)
      | false => exact forall_congr' fun y => ih R Bool.true (Nat.pair x y)

theorem SigmaAt.succ {n : ℕ} {P : ℕ → Prop} (h : SigmaAt n P) : SigmaAt (n + 1) P := by
  obtain ⟨R, hR, hP⟩ := h
  refine ⟨fun w => R w.unpair.1,
    computablePred_comp hR (Primrec.fst.comp Primrec.unpair).to_comp, fun x => ?_⟩
  rw [hP x]
  exact (qAlt_dummy n R Bool.true x).symm

theorem PiAt.succ {n : ℕ} {P : ℕ → Prop} (h : PiAt n P) : PiAt (n + 1) P :=
  piAt_iff_sigmaAt_not.2 (SigmaAt.succ (piAt_iff_sigmaAt_not.1 h))

theorem SigmaAt.of_piAt {n : ℕ} {P : ℕ → Prop} (h : PiAt n P) : SigmaAt (n + 1) P := by
  obtain ⟨R, hR, hP⟩ := h
  have hfst : Computable fun w : ℕ => w.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
  refine ⟨fun w => R (shiftAt (fun w : ℕ => w.unpair.1) n w),
    computablePred_comp hR (computable_shiftAt hfst n), fun x => ?_⟩
  simp only [qAlt_true_succ]
  have key : ∀ y : ℕ,
      qAlt Bool.false n (fun w => R (shiftAt (fun w : ℕ => w.unpair.1) n w)) (Nat.pair x y) ↔
        qAlt Bool.false n R x := by
    intro y
    rw [qAlt_shift n R (fun w : ℕ => w.unpair.1) Bool.false (Nat.pair x y)]
    simp
  constructor
  · intro hx
    exact ⟨0, (key 0).2 ((hP x).1 hx)⟩
  · rintro ⟨y, hy⟩
    exact (hP x).2 ((key y).1 hy)

theorem PiAt.of_sigmaAt {n : ℕ} {P : ℕ → Prop} (h : SigmaAt n P) : PiAt (n + 1) P :=
  piAt_iff_sigmaAt_not.2 (SigmaAt.of_piAt (sigmaAt_iff_piAt_not.1 h))

theorem DeltaAt.of_sigmaAt {n : ℕ} {P : ℕ → Prop} (h : SigmaAt n P) : DeltaAt (n + 1) P :=
  ⟨h.succ, PiAt.of_sigmaAt h⟩

theorem DeltaAt.of_piAt {n : ℕ} {P : ℕ → Prop} (h : PiAt n P) : DeltaAt (n + 1) P :=
  ⟨SigmaAt.of_piAt h, h.succ⟩

/-! ## Peeling the outermost quantifier -/

theorem sigmaAt_succ_iff {n : ℕ} {P : ℕ → Prop} :
    SigmaAt (n + 1) P ↔ ∃ Q : ℕ → Prop, PiAt n Q ∧ ∀ x, P x ↔ ∃ y, Q (Nat.pair x y) := by
  constructor
  · rintro ⟨R, hR, hP⟩
    exact ⟨qAlt Bool.false n R, ⟨R, hR, fun _ => Iff.rfl⟩, hP⟩
  · rintro ⟨Q, ⟨R, hR, hQ⟩, hPQ⟩
    exact ⟨R, hR, fun x => (hPQ x).trans (exists_congr fun y => hQ (Nat.pair x y))⟩

theorem piAt_succ_iff {n : ℕ} {P : ℕ → Prop} :
    PiAt (n + 1) P ↔ ∃ Q : ℕ → Prop, SigmaAt n Q ∧ ∀ x, P x ↔ ∀ y, Q (Nat.pair x y) := by
  constructor
  · rintro ⟨R, hR, hP⟩
    exact ⟨qAlt Bool.true n R, ⟨R, hR, fun _ => Iff.rfl⟩, hP⟩
  · rintro ⟨Q, ⟨R, hR, hQ⟩, hPQ⟩
    exact ⟨R, hR, fun x => (hPQ x).trans (forall_congr' fun y => hQ (Nat.pair x y))⟩

/-! ## The bottom levels -/

theorem sigmaAt_zero_iff {P : ℕ → Prop} : SigmaAt 0 P ↔ ComputablePred P := by
  constructor
  · rintro ⟨R, hR, hP⟩
    exact hR.of_eq fun x => (hP x).symm
  · intro h
    exact ⟨P, h, fun _ => Iff.rfl⟩

theorem piAt_zero_iff {P : ℕ → Prop} : PiAt 0 P ↔ ComputablePred P := by
  constructor
  · rintro ⟨R, hR, hP⟩
    exact hR.of_eq fun x => (hP x).symm
  · intro h
    exact ⟨P, h, fun _ => Iff.rfl⟩

/-- A predicate is r.e. as soon as it is "some stage of a computable test succeeds". -/
theorem rePred_of_exists_computable {P : ℕ → Prop} {R : ℕ → Prop} (hR : ComputablePred R)
    (h : ∀ x, P x ↔ ∃ y, R (Nat.pair x y)) : REPred P := by
  obtain ⟨f, hf, hRf⟩ := ComputablePred.computable_iff.1 hR
  subst hRf
  have hg : Computable₂ fun x k : ℕ => f (Nat.pair x k) :=
    hf.comp (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)
  have hr : Partrec fun x : ℕ => Nat.rfind fun k => Part.some (f (Nat.pair x k)) :=
    Partrec.rfind (Computable₂.partrec₂ hg)
  refine hr.dom_re.of_eq fun x => ?_
  rw [h x]
  constructor
  · intro hdom
    obtain ⟨k, hk, -⟩ := Nat.rfind_dom.1 hdom
    exact ⟨k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact Nat.rfind_dom.2 ⟨k, by simp [hk], fun {_} _ => trivial⟩

/-- **`Σ⁰₁` is exactly the class of recursively enumerable predicates.** -/
theorem sigmaAt_one_iff {P : ℕ → Prop} : SigmaAt 1 P ↔ REPred P := by
  constructor
  · rintro ⟨R, hR, hP⟩
    exact rePred_of_exists_computable hR fun x => by simpa using hP x
  · intro hP
    obtain ⟨g, hg, hgP⟩ := Post.exists_test_of_rePred hP
    have hcomp : Computable fun z : ℕ => g z.unpair.1 z.unpair.2 :=
      (hg.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
    refine ⟨fun z => g z.unpair.1 z.unpair.2 = Bool.true,
      ComputablePred.computable_iff.2 ⟨_, hcomp, rfl⟩, fun x => ?_⟩
    simpa using hgP x

/-- **`Π⁰₁` is exactly the class of co-r.e. predicates.** -/
theorem piAt_one_iff {P : ℕ → Prop} : PiAt 1 P ↔ REPred fun x => ¬ P x :=
  piAt_iff_sigmaAt_not.trans sigmaAt_one_iff

/-- **`Δ⁰₁` is exactly the class of computable predicates**: Post's theorem at the bottom of the
hierarchy. -/
theorem deltaAt_one_iff {P : ℕ → Prop} : DeltaAt 1 P ↔ ComputablePred P := by
  constructor
  · rintro ⟨hs, hp⟩
    exact ComputablePred.computable_iff_re_compl_re'.2 ⟨sigmaAt_one_iff.1 hs, piAt_one_iff.1 hp⟩
  · intro h
    exact ⟨(sigmaAt_zero_iff.2 h).succ, (piAt_zero_iff.2 h).succ⟩

/-! ## Closure properties -/

theorem computablePred_and {P Q : ℕ → Prop} (hP : ComputablePred P) (hQ : ComputablePred Q) :
    ComputablePred fun x => P x ∧ Q x := by
  obtain ⟨f, hf, hPf⟩ := ComputablePred.computable_iff.1 hP
  obtain ⟨g, hg, hQg⟩ := ComputablePred.computable_iff.1 hQ
  subst hPf
  subst hQg
  exact ComputablePred.computable_iff.2
    ⟨fun x => f x && g x, (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp hf hg,
      by funext x; simp⟩

theorem computablePred_or {P Q : ℕ → Prop} (hP : ComputablePred P) (hQ : ComputablePred Q) :
    ComputablePred fun x => P x ∨ Q x := by
  obtain ⟨f, hf, hPf⟩ := ComputablePred.computable_iff.1 hP
  obtain ⟨g, hg, hQg⟩ := ComputablePred.computable_iff.1 hQ
  subst hPf
  subst hQg
  exact ComputablePred.computable_iff.2
    ⟨fun x => f x || g x, (Primrec.dom_bool₂ (fun a b => a || b)).to_comp.comp hf hg,
      by funext x; simp⟩

/-- Closure of `Π⁰ₙ` under conjunction follows, by duality, from closure of `Σ⁰ₙ` under
disjunction. -/
theorem piAt_and_of_sigmaAt_or {n : ℕ}
    (h : ∀ P Q : ℕ → Prop, SigmaAt n P → SigmaAt n Q → SigmaAt n fun x => P x ∨ Q x)
    (P Q : ℕ → Prop) (hP : PiAt n P) (hQ : PiAt n Q) : PiAt n fun x => P x ∧ Q x := by
  classical
  have h1 := h _ _ (piAt_iff_sigmaAt_not.1 hP) (piAt_iff_sigmaAt_not.1 hQ)
  exact piAt_iff_sigmaAt_not.2 (h1.of_iff fun _ => not_and_or)

/-- Closure of `Π⁰ₙ` under disjunction follows, by duality, from closure of `Σ⁰ₙ` under
conjunction. -/
theorem piAt_or_of_sigmaAt_and {n : ℕ}
    (h : ∀ P Q : ℕ → Prop, SigmaAt n P → SigmaAt n Q → SigmaAt n fun x => P x ∧ Q x)
    (P Q : ℕ → Prop) (hP : PiAt n P) (hQ : PiAt n Q) : PiAt n fun x => P x ∨ Q x := by
  classical
  have h1 := h _ _ (piAt_iff_sigmaAt_not.1 hP) (piAt_iff_sigmaAt_not.1 hQ)
  exact piAt_iff_sigmaAt_not.2 (h1.of_iff fun _ => not_or)

/-- The two closure properties, proved together by induction on the level. -/
theorem sigmaAt_closure : ∀ n : ℕ,
    (∀ P Q : ℕ → Prop, SigmaAt n P → SigmaAt n Q → SigmaAt n fun x => P x ∧ Q x) ∧
      (∀ P Q : ℕ → Prop, SigmaAt n P → SigmaAt n Q → SigmaAt n fun x => P x ∨ Q x) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun P Q hP hQ => ?_, fun P Q hP hQ => ?_⟩
      · exact sigmaAt_zero_iff.2
          (computablePred_and (sigmaAt_zero_iff.1 hP) (sigmaAt_zero_iff.1 hQ))
      · exact sigmaAt_zero_iff.2
          (computablePred_or (sigmaAt_zero_iff.1 hP) (sigmaAt_zero_iff.1 hQ))
  | succ n ih =>
      obtain ⟨ihand, ihor⟩ := ih
      have hpiand : ∀ P Q : ℕ → Prop, PiAt n P → PiAt n Q → PiAt n fun x => P x ∧ Q x :=
        piAt_and_of_sigmaAt_or ihor
      have hpior : ∀ P Q : ℕ → Prop, PiAt n P → PiAt n Q → PiAt n fun x => P x ∨ Q x :=
        piAt_or_of_sigmaAt_and ihand
      constructor
      · intro P Q hP hQ
        obtain ⟨P', hP', hPP'⟩ := sigmaAt_succ_iff.1 hP
        obtain ⟨Q', hQ', hQQ'⟩ := sigmaAt_succ_iff.1 hQ
        have hf1 : Computable fun u : ℕ => Nat.pair u.unpair.1 u.unpair.2.unpair.1 :=
          (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
            (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
        have hf2 : Computable fun u : ℕ => Nat.pair u.unpair.1 u.unpair.2.unpair.2 :=
          (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
            (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
        have h1 : PiAt n fun u : ℕ => P' (Nat.pair u.unpair.1 u.unpair.2.unpair.1) :=
          hP'.subst hf1
        have h2 : PiAt n fun u : ℕ => Q' (Nat.pair u.unpair.1 u.unpair.2.unpair.2) :=
          hQ'.subst hf2
        refine sigmaAt_succ_iff.2 ⟨_, hpiand _ _ h1 h2, fun x => ?_⟩
        constructor
        · rintro ⟨hx1, hx2⟩
          obtain ⟨y, hy⟩ := (hPP' x).1 hx1
          obtain ⟨z, hz⟩ := (hQQ' x).1 hx2
          refine ⟨Nat.pair y z, ?_, ?_⟩
          · simpa using hy
          · simpa using hz
        · rintro ⟨u, hu1, hu2⟩
          simp only [Nat.unpair_pair] at hu1 hu2
          exact ⟨(hPP' x).2 ⟨u.unpair.1, hu1⟩, (hQQ' x).2 ⟨u.unpair.2, hu2⟩⟩
      · intro P Q hP hQ
        obtain ⟨P', hP', hPP'⟩ := sigmaAt_succ_iff.1 hP
        obtain ⟨Q', hQ', hQQ'⟩ := sigmaAt_succ_iff.1 hQ
        refine sigmaAt_succ_iff.2 ⟨fun u => P' u ∨ Q' u, hpior _ _ hP' hQ', fun x => ?_⟩
        constructor
        · rintro (hx | hx)
          · obtain ⟨y, hy⟩ := (hPP' x).1 hx
            exact ⟨y, Or.inl hy⟩
          · obtain ⟨y, hy⟩ := (hQQ' x).1 hx
            exact ⟨y, Or.inr hy⟩
        · rintro ⟨y, hy | hy⟩
          · exact Or.inl ((hPP' x).2 ⟨y, hy⟩)
          · exact Or.inr ((hQQ' x).2 ⟨y, hy⟩)

theorem SigmaAt.and {n : ℕ} {P Q : ℕ → Prop} (hP : SigmaAt n P) (hQ : SigmaAt n Q) :
    SigmaAt n fun x => P x ∧ Q x := (sigmaAt_closure n).1 P Q hP hQ

theorem SigmaAt.or {n : ℕ} {P Q : ℕ → Prop} (hP : SigmaAt n P) (hQ : SigmaAt n Q) :
    SigmaAt n fun x => P x ∨ Q x := (sigmaAt_closure n).2 P Q hP hQ

theorem PiAt.and {n : ℕ} {P Q : ℕ → Prop} (hP : PiAt n P) (hQ : PiAt n Q) :
    PiAt n fun x => P x ∧ Q x := piAt_and_of_sigmaAt_or (sigmaAt_closure n).2 P Q hP hQ

theorem PiAt.or {n : ℕ} {P Q : ℕ → Prop} (hP : PiAt n P) (hQ : PiAt n Q) :
    PiAt n fun x => P x ∨ Q x := piAt_or_of_sigmaAt_and (sigmaAt_closure n).1 P Q hP hQ

/-- **`Σ⁰ₙ₊₁` is closed under existential quantification.** -/
theorem SigmaAt.exists {n : ℕ} {Q : ℕ → Prop} (hQ : SigmaAt (n + 1) Q) :
    SigmaAt (n + 1) fun x => ∃ y, Q (Nat.pair x y) := by
  obtain ⟨Q', hQ', hQQ'⟩ := sigmaAt_succ_iff.1 hQ
  have hf : Computable fun v : ℕ =>
      Nat.pair (Nat.pair v.unpair.1 v.unpair.2.unpair.1) v.unpair.2.unpair.2 :=
    (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).to_comp
  have hS : PiAt n fun v : ℕ =>
      Q' (Nat.pair (Nat.pair v.unpair.1 v.unpair.2.unpair.1) v.unpair.2.unpair.2) :=
    hQ'.subst hf
  refine sigmaAt_succ_iff.2 ⟨_, hS, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨w, hw⟩ := (hQQ' (Nat.pair x y)).1 hy
    exact ⟨Nat.pair y w, by simpa using hw⟩
  · rintro ⟨u, hu⟩
    simp only [Nat.unpair_pair] at hu
    exact ⟨u.unpair.1, (hQQ' (Nat.pair x u.unpair.1)).2 ⟨u.unpair.2, hu⟩⟩

/-- **`Π⁰ₙ₊₁` is closed under universal quantification.** -/
theorem PiAt.forall {n : ℕ} {Q : ℕ → Prop} (hQ : PiAt (n + 1) Q) :
    PiAt (n + 1) fun x => ∀ y, Q (Nat.pair x y) := by
  classical
  have h2 := SigmaAt.exists (piAt_iff_sigmaAt_not.1 hQ)
  exact piAt_iff_sigmaAt_not.2 (h2.of_iff fun _ => not_forall)

end Arith
end Lambda
