/-
**Degree reduction for Shamir's protocol: Shen's linearization operators.**

The arithmetization of `Start/QbfArith.lean` is correct but unusable as it stands for an
interactive proof: every quantifier squares the polynomial it acts on, so after `k` nested
quantifiers the degree in a variable can be `2^k`, and the prover's messages — univariate
restrictions — would be exponentially long.  Shen's remedy is the **linearization operator**

  `L_j f = x_j · f[x_j := 1] + (1 - x_j) · f[x_j := 0]`,

which agrees with `f` on `0/1` points and has degree at most one in `x_j`.  Inserting a
linearization of every variable after every quantifier keeps every intermediate function
multilinear in the variables, so the degrees stay bounded by the size of the formula.

The route taken here does not need a prenex normal form: the operators are inserted directly into
the formula tree (`Complexity.Qbf.QBF.toOp`), and the protocol of `Start/SumCheck.lean` walks
the tree.  Degrees are expressed semantically: `Complexity.Qbf.UniDeg f j d` says that every
restriction of `f` to a line in direction `j` is a polynomial of degree at most `d`, which is
exactly what the honest prover has to send and what the soundness estimate needs.

Main definitions:

* `Complexity.Qbf.linOp` — the linearization operator on functions `(ℕ → R) → R`;
* `Complexity.Qbf.UniDeg` — degree at most `d` in the variable `j`;
* `Complexity.Qbf.Op`, `.eval` — formulas with explicit linearization nodes, and their value;
* `Complexity.Qbf.Op.linAll`, `Complexity.Qbf.QBF.toOp` — the linearized operator tree of a
  formula: after every quantifier, a linearization of every variable below `N`;
* `Complexity.Qbf.Op.RoundDeg` — every quantifier and linearization node acts on a function of
  degree at most `d` in its variable.

Main results:

* `Complexity.Qbf.linOp_eq_of_bool`, `Complexity.Qbf.uniDeg_linOp_self` — `L_j f` agrees with
  `f` when `x_j ∈ {0, 1}`, and has degree at most one in `x_j`;
* `Complexity.Qbf.QBF.eval_toOp_bool` — on `0/1` points the operator tree has the value of the
  arithmetization;
* `Complexity.Qbf.QBF.tqbf_iff_toOp` — a closed formula is true iff its operator tree evaluates
  to `1` (in any nontrivial commutative ring);
* `Complexity.Qbf.QBF.uniDeg_toOp` — the value of the operator tree has degree at most `size p`
  in every variable;
* `Complexity.Qbf.QBF.roundDeg_toOp` — **every univariate restriction met in the protocol has
  degree at most `2 · size p`**.
-/

import Start.QbfArith

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Polynomial

namespace Complexity.Qbf

variable {R : Type*} [CommRing R]

/-! ### Degree in one variable -/

/-- `f` has degree at most `d` in the variable `j`: on every line in direction `j` it is a
polynomial of degree at most `d`. -/
def UniDeg (f : (ℕ → R) → R) (j d : ℕ) : Prop :=
  ∀ a : ℕ → R, ∃ q : R[X], q.natDegree ≤ d ∧ ∀ x, q.eval x = f (Function.update a j x)

/-- `f` does not depend on the variable `j`. -/
def Indep (f : (ℕ → R) → R) (j : ℕ) : Prop := ∀ (a : ℕ → R) (x : R), f (Function.update a j x) = f a

theorem UniDeg.mono {f : (ℕ → R) → R} {j d e : ℕ} (h : UniDeg f j d) (hde : d ≤ e) :
    UniDeg f j e := fun a => by
  obtain ⟨q, hq, hx⟩ := h a
  exact ⟨q, hq.trans hde, hx⟩

theorem Indep.uniDeg {f : (ℕ → R) → R} {j : ℕ} (h : Indep f j) : UniDeg f j 0 := fun a =>
  ⟨C (f a), by simp, fun x => by simp [h a x]⟩

theorem uniDeg_const (c : R) (j : ℕ) : UniDeg (fun _ => c) j 0 :=
  Indep.uniDeg (fun _ _ => rfl)

theorem uniDeg_var (i j : ℕ) : UniDeg (fun a : ℕ → R => a i) j 1 := by
  intro a
  by_cases h : i = j
  · subst h
    exact ⟨X, natDegree_X_le, fun x => by simp⟩
  · exact ⟨C (a i), by simp, fun x => by simp [Function.update_of_ne h]⟩

theorem uniDeg_var_ne {i j : ℕ} (h : i ≠ j) : UniDeg (fun a : ℕ → R => a i) j 0 :=
  Indep.uniDeg (fun a x => by simp [Function.update_of_ne h])

theorem UniDeg.add {f g : (ℕ → R) → R} {j d e : ℕ} (hf : UniDeg f j d) (hg : UniDeg g j e) :
    UniDeg (fun a => f a + g a) j (max d e) := fun a => by
  obtain ⟨q, hq, hqx⟩ := hf a
  obtain ⟨r, hr, hrx⟩ := hg a
  refine ⟨q + r, (natDegree_add_le _ _).trans (max_le_max hq hr), fun x => by simp [hqx, hrx]⟩

theorem UniDeg.mul {f g : (ℕ → R) → R} {j d e : ℕ} (hf : UniDeg f j d) (hg : UniDeg g j e) :
    UniDeg (fun a => f a * g a) j (d + e) := fun a => by
  obtain ⟨q, hq, hqx⟩ := hf a
  obtain ⟨r, hr, hrx⟩ := hg a
  refine ⟨q * r, (natDegree_mul_le).trans (add_le_add hq hr), fun x => by simp [hqx, hrx]⟩

theorem UniDeg.one_sub {f : (ℕ → R) → R} {j d : ℕ} (hf : UniDeg f j d) :
    UniDeg (fun a => 1 - f a) j d := fun a => by
  obtain ⟨q, hq, hqx⟩ := hf a
  refine ⟨1 - q, (natDegree_sub_le _ _).trans ?_, fun x => by simp [hqx]⟩
  simpa using hq

/-- Fixing a *different* variable does not raise the degree in `j`. -/
theorem UniDeg.update_ne {f : (ℕ → R) → R} {j d k : ℕ} (hf : UniDeg f j d) (hk : k ≠ j) (c : R) :
    UniDeg (fun a => f (Function.update a k c)) j d := fun a => by
  obtain ⟨q, hq, hqx⟩ := hf (Function.update a k c)
  refine ⟨q, hq, fun x => ?_⟩
  rw [hqx]
  change _ = f (Function.update (Function.update a j x) k c)
  rw [Function.update_comm hk]

omit [CommRing R] in
/-- After fixing `j` itself the function no longer depends on `j`. -/
theorem indep_update_self (f : (ℕ → R) → R) (j : ℕ) (c : R) :
    Indep (fun a => f (Function.update a j c)) j := fun a x => by
  simp

/-- Fixing some variable, whichever, keeps the degree in `j` at most `d`. -/
theorem UniDeg.update {f : (ℕ → R) → R} {j d : ℕ} (hf : UniDeg f j d) (k : ℕ) (c : R) :
    UniDeg (fun a => f (Function.update a k c)) j d := by
  by_cases hk : k = j
  · subst hk
    exact ((indep_update_self f k c).uniDeg).mono (Nat.zero_le _)
  · exact hf.update_ne hk c

/-! ### The linearization operator -/

/-- **Shen's linearization operator** `L_j f = x_j f[x_j := 1] + (1 - x_j) f[x_j := 0]`. -/
def linOp (j : ℕ) (f : (ℕ → R) → R) (a : ℕ → R) : R :=
  a j * f (Function.update a j 1) + (1 - a j) * f (Function.update a j 0)

/-- On `0/1` values of `x_j` the linearization agrees with `f`. -/
theorem linOp_eq_of_bool (j : ℕ) (f : (ℕ → R) → R) (a : ℕ → R) (h : a j = 0 ∨ a j = 1) :
    linOp j f a = f a := by
  rcases h with h | h
  · have : Function.update a j 0 = a := by rw [← h]; exact Function.update_eq_self j a
    simp [linOp, h, this]
  · have : Function.update a j 1 = a := by rw [← h]; exact Function.update_eq_self j a
    simp [linOp, h, this]

/-- `L_j f` has degree at most one in `x_j`, whatever `f` is. -/
theorem uniDeg_linOp_self (j : ℕ) (f : (ℕ → R) → R) : UniDeg (linOp j f) j 1 := by
  have h := ((uniDeg_var j j).mul ((indep_update_self f j 1).uniDeg)).add
    (((uniDeg_var j j).one_sub).mul ((indep_update_self f j 0).uniDeg))
  exact h

/-- A linearization does not raise the degree in any variable above `max d 1`. -/
theorem UniDeg.linOp {f : (ℕ → R) → R} {j d : ℕ} (hf : UniDeg f j d) (k : ℕ) :
    UniDeg (linOp k f) j (max d 1) := by
  by_cases hk : k = j
  · subst hk; exact (uniDeg_linOp_self k f).mono (le_max_right _ _)
  · have h := ((uniDeg_var_ne hk).mul (hf.update_ne hk 1)).add
      (((uniDeg_var_ne hk).one_sub).mul (hf.update_ne hk 0))
    simp only [zero_add, max_self] at h
    exact h.mono (le_max_left _ _)

/-- A linearization of another variable keeps independence of `j`. -/
theorem Indep.linOp {f : (ℕ → R) → R} {j k : ℕ} (hf : Indep f j) (hk : k ≠ j) :
    Indep (Qbf.linOp k f) j := fun a x => by
  simp only [Qbf.linOp, Function.update_of_ne hk]
  rw [← Function.update_comm hk, ← Function.update_comm hk, hf, hf]

/-! ### Operator trees -/

/-- Formulas with explicit linearization nodes: the operator expressions of Shen's protocol. -/
inductive Op where
  /-- A variable. -/
  | var (i : ℕ)
  /-- Negation, `1 - f`. -/
  | neg (p : Op)
  /-- Conjunction, `f · g`. -/
  | conj (p q : Op)
  /-- Disjunction, `1 - (1 - f)(1 - g)`. -/
  | disj (p q : Op)
  /-- Universal quantifier, `f[x_i := 0] · f[x_i := 1]`. -/
  | all (i : ℕ) (p : Op)
  /-- Existential quantifier, `1 - (1 - f[x_i := 0])(1 - f[x_i := 1])`. -/
  | ex (i : ℕ) (p : Op)
  /-- Linearization in the variable `j`. -/
  | lin (j : ℕ) (p : Op)
  deriving DecidableEq, Repr, Inhabited

namespace Op

/-- The value of an operator expression at a point. -/
def eval (a : ℕ → R) : Op → R
  | .var i => a i
  | .neg p => 1 - eval a p
  | .conj p q => eval a p * eval a q
  | .disj p q => 1 - (1 - eval a p) * (1 - eval a q)
  | .all i p => eval (Function.update a i 0) p * eval (Function.update a i 1) p
  | .ex i p => 1 - (1 - eval (Function.update a i 0) p) * (1 - eval (Function.update a i 1) p)
  | .lin j p => a j * eval (Function.update a j 1) p + (1 - a j) * eval (Function.update a j 0) p

theorem eval_lin (a : ℕ → R) (j : ℕ) (p : Op) :
    eval a (.lin j p) = Qbf.linOp j (fun b => eval b p) a := rfl

/-- Linearize every variable of a list, the head outermost. -/
def linAll : List ℕ → Op → Op
  | [], t => t
  | j :: js, t => .lin j (linAll js t)

/-- The number of nodes. -/
def size : Op → ℕ
  | .var _ => 1
  | .neg p => p.size + 1
  | .conj p q => p.size + q.size + 1
  | .disj p q => p.size + q.size + 1
  | .all _ p => p.size + 1
  | .ex _ p => p.size + 1
  | .lin _ p => p.size + 1

/-- The rounds of the protocol: the nodes at which the prover sends a message and the verifier
then draws a random point — the quantifier and linearization nodes, where the message is a
univariate polynomial, and the conjunction and disjunction nodes, where it is the pair of values of
the two children (the point drawn there is not used, but drawing it keeps the protocol in strict
alternation, one message and one point per round). -/
def rounds : Op → ℕ
  | .var _ => 0
  | .neg p => p.rounds
  | .conj p q => p.rounds + q.rounds + 1
  | .disj p q => p.rounds + q.rounds + 1
  | .all _ p => p.rounds + 1
  | .ex _ p => p.rounds + 1
  | .lin _ p => p.rounds + 1

theorem rounds_le_size : ∀ t : Op, t.rounds ≤ t.size
  | .var _ => by simp [rounds, size]
  | .neg p => by have := rounds_le_size p; simp [rounds, size]; omega
  | .conj p q => by
      have := rounds_le_size p; have := rounds_le_size q; simp [rounds, size]; omega
  | .disj p q => by
      have := rounds_le_size p; have := rounds_le_size q; simp [rounds, size]; omega
  | .all _ p => by have := rounds_le_size p; simp [rounds, size]; omega
  | .ex _ p => by have := rounds_le_size p; simp [rounds, size]; omega
  | .lin _ p => by have := rounds_le_size p; simp [rounds, size]; omega

theorem size_linAll (js : List ℕ) (t : Op) : (linAll js t).size = t.size + js.length := by
  induction js with
  | nil => rfl
  | cons j js ih => simp [linAll, size, ih]; omega

variable (R) in
/-- Every quantifier and linearization node of the expression acts on a function of degree at most
`d` in its variable: the bound on the prover's messages in the protocol. -/
def RoundDeg (d : ℕ) : Op → Prop
  | .var _ => True
  | .neg p => RoundDeg d p
  | .conj p q => RoundDeg d p ∧ RoundDeg d q
  | .disj p q => RoundDeg d p ∧ RoundDeg d q
  | .all i p => UniDeg (fun a : ℕ → R => eval a p) i d ∧ RoundDeg d p
  | .ex i p => UniDeg (fun a : ℕ → R => eval a p) i d ∧ RoundDeg d p
  | .lin j p => UniDeg (fun a : ℕ → R => eval a p) j d ∧ RoundDeg d p

theorem RoundDeg.mono {d e : ℕ} (hde : d ≤ e) {t : Op} (h : RoundDeg R d t) : RoundDeg R e t := by
  induction t with
  | var _ => trivial
  | neg _ ih => exact ih h
  | conj _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | disj _ _ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | all _ _ ih => exact ⟨h.1.mono hde, ih h.2⟩
  | ex _ _ ih => exact ⟨h.1.mono hde, ih h.2⟩
  | lin _ _ ih => exact ⟨h.1.mono hde, ih h.2⟩

/-- A point with every coordinate `0` or `1`. -/
def IsBool (a : ℕ → R) : Prop := ∀ j, a j = 0 ∨ a j = 1

theorem IsBool.update {a : ℕ → R} (ha : IsBool a) (j : ℕ) {c : R} (hc : c = 0 ∨ c = 1) :
    IsBool (Function.update a j c) := fun k => by
  by_cases h : k = j
  · subst h; simpa using hc
  · simpa [Function.update_of_ne h] using ha k

/-- Linearizations do not change the value at `0/1` points. -/
theorem eval_linAll_bool (js : List ℕ) (t : Op) :
    ∀ a : ℕ → R, IsBool a → eval a (linAll js t) = eval a t := by
  induction js with
  | nil => intro a _; rfl
  | cons j js ih =>
      intro a ha
      rw [linAll, eval_lin]
      rw [linOp_eq_of_bool j _ a (ha j)]
      exact ih a ha

/-- Linearizations keep the degree in every variable at most `max d 1`. -/
theorem uniDeg_linAll {t : Op} {j d : ℕ} (h : UniDeg (fun a : ℕ → R => eval a t) j d) :
    ∀ js : List ℕ, UniDeg (fun a : ℕ → R => eval a (linAll js t)) j (max d 1)
  | [] => h.mono (le_max_left _ _)
  | k :: js => by
      have := (uniDeg_linAll h js).linOp k
      simp only [max_assoc, max_self] at this
      exact this

/-- After linearizing `j`, the degree in `j` is at most one. -/
theorem uniDeg_linAll_mem (t : Op) {j : ℕ} :
    ∀ {js : List ℕ}, j ∈ js → UniDeg (fun a : ℕ → R => eval a (linAll js t)) j 1
  | k :: js, hj => by
      by_cases hk : k = j
      · subst hk; exact uniDeg_linOp_self (R := R) k (fun a => eval a (linAll js t))
      · have hj' : j ∈ js := by
          rcases List.mem_cons.1 hj with h | h
          · exact absurd h.symm hk
          · exact h
        have := (uniDeg_linAll_mem t hj').linOp k
        exact this

/-- Linearizations of other variables keep independence. -/
theorem indep_linAll {t : Op} {j : ℕ} (h : Indep (fun a : ℕ → R => eval a t) j) :
    ∀ {js : List ℕ}, j ∉ js → Indep (fun a : ℕ → R => eval a (linAll js t)) j
  | [], _ => h
  | k :: js, hj => by
      have hk : k ≠ j := fun e => hj (e ▸ List.mem_cons_self ..)
      have hj' : j ∉ js := fun e => hj (List.mem_cons_of_mem _ e)
      exact (indep_linAll h hj').linOp hk

/-- Linearizations preserve the round-degree bound, given the degree bound on the expression
they act on. -/
theorem roundDeg_linAll {t : Op} {d : ℕ} (hd : 1 ≤ d)
    (hdeg : ∀ j, UniDeg (fun a : ℕ → R => eval a t) j d) (ht : RoundDeg R d t) :
    ∀ js : List ℕ, RoundDeg R d (linAll js t)
  | [] => ht
  | k :: js => by
      refine ⟨?_, roundDeg_linAll hd hdeg ht js⟩
      have := uniDeg_linAll (hdeg k) js
      rwa [max_eq_left hd] at this

end Op

/-! ### The linearized operator tree of a formula -/

namespace QBF

open Op

/-- The operator tree of a formula: the arithmetization with, after every quantifier, a
linearization of every variable below `N`. -/
def toOp (N : ℕ) : QBF → Op
  | .var i => .var i
  | .neg p => .neg (toOp N p)
  | .conj p q => .conj (toOp N p) (toOp N q)
  | .disj p q => .disj (toOp N p) (toOp N q)
  | .all i p => linAll (List.range N) (.all i (toOp N p))
  | .ex i p => linAll (List.range N) (.ex i (toOp N p))

/-- The operator tree is polynomially large: at most `(N + 1) · size p` nodes. -/
theorem size_toOp (N : ℕ) : ∀ p : QBF, (toOp N p).size ≤ (N + 1) * p.size
  | .var _ => by simp [toOp, Op.size, QBF.size]
  | .neg p => by
      have := size_toOp N p; simp only [toOp, Op.size, QBF.size]; nlinarith
  | .conj p q => by
      have := size_toOp N p; have := size_toOp N q
      simp only [toOp, Op.size, QBF.size]; nlinarith
  | .disj p q => by
      have := size_toOp N p; have := size_toOp N q
      simp only [toOp, Op.size, QBF.size]; nlinarith
  | .all _ p => by
      have := size_toOp N p
      simp only [toOp, size_linAll, Op.size, QBF.size, List.length_range]; nlinarith
  | .ex _ p => by
      have := size_toOp N p
      simp only [toOp, size_linAll, Op.size, QBF.size, List.length_range]; nlinarith

/-- **On `0/1` points the operator tree has the value of the arithmetization.** -/
theorem eval_toOp_bool (N : ℕ) (p : QBF) :
    ∀ a : ℕ → R, IsBool a → Op.eval a (toOp N p) = arith a p := by
  induction p with
  | var i => intro a _; rfl
  | neg p ih => intro a ha; simp [toOp, Op.eval, arith, ih a ha]
  | conj p q ihp ihq => intro a ha; simp [toOp, Op.eval, arith, ihp a ha, ihq a ha]
  | disj p q ihp ihq => intro a ha; simp [toOp, Op.eval, arith, ihp a ha, ihq a ha]
  | all i p ih =>
      intro a ha
      rw [toOp, eval_linAll_bool _ _ a ha, Op.eval, arith,
        ih _ (ha.update i (Or.inl rfl)), ih _ (ha.update i (Or.inr rfl))]
  | ex i p ih =>
      intro a ha
      rw [toOp, eval_linAll_bool _ _ a ha, Op.eval, arith,
        ih _ (ha.update i (Or.inl rfl)), ih _ (ha.update i (Or.inr rfl))]

/-- **A closed formula is true iff its operator tree evaluates to `1`**, in any nontrivial
commutative ring. -/
theorem tqbf_iff_toOp [Nontrivial R] (N : ℕ) {p : QBF} (hp : p.Closed) :
    TQBF p ↔ Op.eval (fun _ => (0 : R)) (toOp N p) = 1 := by
  rw [eval_toOp_bool N p _ (fun _ => Or.inl rfl)]
  exact tqbf_iff_arith hp

/-- The operator tree does not depend on the variables at or above `N` (for `varBound p ≤ N`). -/
theorem indep_toOp {N : ℕ} {j : ℕ} (hj : N ≤ j) :
    ∀ p : QBF, p.varBound ≤ N → Indep (fun a : ℕ → R => Op.eval a (toOp N p)) j
  | .var i, h => fun a x => by
      have : i ≠ j := by simp [varBound] at h; omega
      simp [toOp, Op.eval, Function.update_of_ne this]
  | .neg p, h => fun a x => by
      have := indep_toOp hj p (by simpa [varBound] using h) a x
      simp only [toOp, Op.eval] at this ⊢; rw [this]
  | .conj p q, h => fun a x => by
      have h1 := indep_toOp hj p (le_trans (le_max_left _ _) h) a x
      have h2 := indep_toOp hj q (le_trans (le_max_right _ _) h) a x
      simp only [toOp, Op.eval] at h1 h2 ⊢; rw [h1, h2]
  | .disj p q, h => fun a x => by
      have h1 := indep_toOp hj p (le_trans (le_max_left _ _) h) a x
      have h2 := indep_toOp hj q (le_trans (le_max_right _ _) h) a x
      simp only [toOp, Op.eval] at h1 h2 ⊢; rw [h1, h2]
  | .all i p, h => by
      have hp : p.varBound ≤ N := le_trans (le_max_right _ _) h
      have hi : i ≠ j := by have := le_trans (le_max_left _ _) h; omega
      refine indep_linAll (fun a x => ?_) (by simp; omega)
      have h0 := indep_toOp hj p hp (Function.update a i 0) x
      have h1 := indep_toOp hj p hp (Function.update a i 1) x
      simp only at h0 h1
      simp only [Op.eval]
      rw [Function.update_comm hi.symm, Function.update_comm hi.symm, h0, h1]
  | .ex i p, h => by
      have hp : p.varBound ≤ N := le_trans (le_max_right _ _) h
      have hi : i ≠ j := by have := le_trans (le_max_left _ _) h; omega
      refine indep_linAll (fun a x => ?_) (by simp; omega)
      have h0 := indep_toOp hj p hp (Function.update a i 0) x
      have h1 := indep_toOp hj p hp (Function.update a i 1) x
      simp only at h0 h1
      simp only [Op.eval]
      rw [Function.update_comm hi.symm, Function.update_comm hi.symm, h0, h1]

/-- A quantifier at most doubles the degree in every variable (and kills its own). -/
theorem uniDeg_quant {f : (ℕ → R) → R} {d : ℕ} (hf : ∀ j, UniDeg f j d) (i j : ℕ) :
    UniDeg (fun a => f (Function.update a i 0) * f (Function.update a i 1)) j (2 * d) ∧
    UniDeg (fun a => 1 - (1 - f (Function.update a i 0)) * (1 - f (Function.update a i 1)))
      j (2 * d) := by
  have h := ((hf j).update i 0).mul ((hf j).update i 1)
  rw [← two_mul] at h
  exact ⟨h, (((hf j).update i 0).one_sub.mul ((hf j).update i 1).one_sub).one_sub.mono
    (by omega)⟩

/-- **The value of the operator tree has degree at most `size p` in every variable.** -/
theorem uniDeg_toOp {N : ℕ} :
    ∀ p : QBF, p.varBound ≤ N → ∀ j, UniDeg (fun a : ℕ → R => Op.eval a (toOp N p)) j p.size
  | .var i, _ => fun j => uniDeg_var i j
  | .neg p, h => fun j =>
      ((uniDeg_toOp p (by simpa [varBound] using h) j).one_sub).mono (by simp [QBF.size])
  | .conj p q, h => fun j =>
      ((uniDeg_toOp p (le_trans (le_max_left _ _) h) j).mul
        (uniDeg_toOp q (le_trans (le_max_right _ _) h) j)).mono (by simp [QBF.size])
  | .disj p q, h => fun j =>
      (((uniDeg_toOp p (le_trans (le_max_left _ _) h) j).one_sub.mul
        (uniDeg_toOp q (le_trans (le_max_right _ _) h) j).one_sub).one_sub).mono
        (by simp [QBF.size])
  | .all i p, h => fun j => by
      by_cases hj : j < N
      · exact (uniDeg_linAll_mem _ (by simpa using hj)).mono (by simp [QBF.size])
      · exact ((indep_toOp (by omega) (.all i p) h).uniDeg).mono (Nat.zero_le _)
  | .ex i p, h => fun j => by
      by_cases hj : j < N
      · exact (uniDeg_linAll_mem _ (by simpa using hj)).mono (by simp [QBF.size])
      · exact ((indep_toOp (by omega) (.ex i p) h).uniDeg).mono (Nat.zero_le _)

/-- **Degree reduction works: every univariate restriction met in the protocol on the operator
tree has degree at most `2 · size p`.** -/
theorem roundDeg_toOp {N : ℕ} :
    ∀ p : QBF, p.varBound ≤ N → RoundDeg R (2 * p.size) (toOp N p)
  | .var _, _ => trivial
  | .neg p, h =>
      (roundDeg_toOp p (by simpa [varBound] using h)).mono (by simp [QBF.size])
  | .conj p q, h =>
      ⟨(roundDeg_toOp p (le_trans (le_max_left _ _) h)).mono (by simp [QBF.size]; omega),
        (roundDeg_toOp q (le_trans (le_max_right _ _) h)).mono (by simp [QBF.size]; omega)⟩
  | .disj p q, h =>
      ⟨(roundDeg_toOp p (le_trans (le_max_left _ _) h)).mono (by simp [QBF.size]; omega),
        (roundDeg_toOp q (le_trans (le_max_right _ _) h)).mono (by simp [QBF.size]; omega)⟩
  | .all i p, h => by
      have hp : p.varBound ≤ N := le_trans (le_max_right _ _) h
      have hs : 1 ≤ 2 * (QBF.all i p).size := by simp [QBF.size]; omega
      refine roundDeg_linAll (t := Op.all i (toOp N p)) hs (fun j => ?_) (And.intro ?_ ?_) _
      · exact ((uniDeg_quant (uniDeg_toOp p hp) i j).1).mono (by simp [QBF.size])
      · exact (uniDeg_toOp p hp i).mono (by simp [QBF.size]; omega)
      · exact (roundDeg_toOp p hp).mono (by simp [QBF.size])
  | .ex i p, h => by
      have hp : p.varBound ≤ N := le_trans (le_max_right _ _) h
      have hs : 1 ≤ 2 * (QBF.ex i p).size := by simp [QBF.size]; omega
      refine roundDeg_linAll (t := Op.ex i (toOp N p)) hs (fun j => ?_) (And.intro ?_ ?_) _
      · exact ((uniDeg_quant (uniDeg_toOp p hp) i j).2).mono (by simp [QBF.size])
      · exact (uniDeg_toOp p hp i).mono (by simp [QBF.size]; omega)
      · exact (roundDeg_toOp p hp).mono (by simp [QBF.size])

end QBF

end Complexity.Qbf
