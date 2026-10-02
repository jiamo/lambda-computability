/-
**The arithmetization of quantified Boolean formulas** — the first algebraic step of Shamir's
proof of `IP = PSPACE` — and the one-round soundness estimate of the sum-check protocol.

Note that the Cobham-term modules `Start/QbfCob*.lean` are *not* an arithmetization: they build
the reduction formula of `PSPACE`-hardness by polynomial-time word operations.  The arithmetization
proper starts here.

A formula `p` is sent to an element of an arbitrary commutative ring, given values of the variables:
negation becomes `1 - a`, conjunction a product, disjunction `1 - (1 - a)(1 - b)`, and the two
quantifiers combine the values at `0` and at `1` in the same way (product for `∀`, the dual
product for `∃`).  On `0/1` values this computes the truth value (`QBF.arith_bool`), so a closed
formula is true exactly when its arithmetization is `1` (`QBF.tqbf_iff_arith`).  The same map
lands in multivariate polynomials (`QBF.arithPoly`), evaluating to `arith`
(`QBF.eval_arithPoly`).

The probabilistic heart of the sum-check protocol is the estimate that two *different* univariate
polynomials of degree at most `d` over a finite field agree on at most `d` points
(`Polynomial.card_eval_eq_le`), so a verifier who checks a false claim at a uniformly random point
is fooled with probability at most `d / |F|` (`Polynomial.card_eval_eq_le_div`).

What is *not* here, and is recorded on the task board: the degree reduction (linearization) that
keeps the degrees of the intermediate polynomials polynomial — without it the quantifiers
double the degree — and the interactive-proof framework itself.
-/

import Start.Qbf

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

variable {R : Type*} [CommRing R]

/-- **Shamir's arithmetization** of a formula, given ring values `a` of the variables. -/
def arith (a : ℕ → R) : QBF → R
  | .var i => a i
  | .neg p => 1 - arith a p
  | .conj p q => arith a p * arith a q
  | .disj p q => 1 - (1 - arith a p) * (1 - arith a q)
  | .all i p => arith (Function.update a i 0) p * arith (Function.update a i 1) p
  | .ex i p => 1 - (1 - arith (Function.update a i 0) p) * (1 - arith (Function.update a i 1) p)

/-- A truth value as an element of the ring: `1` or `0`. -/
def boolVal (R : Type*) [CommRing R] (b : Bool) : R := if b then 1 else 0

@[simp] theorem boolVal_true : boolVal R true = 1 := rfl
@[simp] theorem boolVal_false : boolVal R false = 0 := rfl

theorem boolVal_not (b : Bool) : boolVal R (!b) = 1 - boolVal R b := by
  cases b <;> simp [boolVal]

theorem boolVal_and (b c : Bool) : boolVal R (b && c) = boolVal R b * boolVal R c := by
  cases b <;> cases c <;> simp [boolVal]

theorem boolVal_or (b c : Bool) :
    boolVal R (b || c) = 1 - (1 - boolVal R b) * (1 - boolVal R c) := by
  cases b <;> cases c <;> simp [boolVal]

theorem boolVal_comp_update (σ : ℕ → Bool) (i : ℕ) (b : Bool) :
    (fun j => boolVal R (Function.update σ i b j)) =
      Function.update (fun j => boolVal R (σ j)) i (boolVal R b) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **Arithmetization is correct on `0/1` values**: it computes the truth value. -/
theorem arith_bool (p : QBF) : ∀ σ : ℕ → Bool,
    arith (fun i => boolVal R (σ i)) p = boolVal R (eval σ p) := by
  induction p with
  | var i => intro σ; rfl
  | neg p ih => intro σ; simp only [arith, eval, ih, boolVal_not]
  | conj p q ihp ihq => intro σ; simp only [arith, eval, ihp, ihq, boolVal_and]
  | disj p q ihp ihq => intro σ; simp only [arith, eval, ihp, ihq, boolVal_or]
  | all i p ih =>
    intro σ
    have h0 := boolVal_comp_update (R := R) σ i false
    have h1 := boolVal_comp_update (R := R) σ i true
    simp only [boolVal_false, boolVal_true] at h0 h1
    simp only [arith, eval, ← h0, ← h1, ih, boolVal_and]
  | ex i p ih =>
    intro σ
    have h0 := boolVal_comp_update (R := R) σ i false
    have h1 := boolVal_comp_update (R := R) σ i true
    simp only [boolVal_false, boolVal_true] at h0 h1
    simp only [arith, eval, ← h0, ← h1, ih, boolVal_or]

/-- **A closed formula is true iff its arithmetization is `1`**, in any nontrivial commutative
ring (the variables being set to `0`, which does not matter for a closed formula). -/
theorem tqbf_iff_arith [Nontrivial R] {p : QBF} (hp : p.Closed) :
    TQBF p ↔ arith (fun _ => (0 : R)) p = 1 := by
  have h := arith_bool (R := R) p (fun _ => false)
  simp only [boolVal_false] at h
  rw [h, TQBF]
  cases eval (fun _ => false) p <;> simp [boolVal, hp]

/-- The arithmetization as a multivariate polynomial over the variables of the formula. -/
noncomputable def arithPoly : QBF → MvPolynomial ℕ R
  | .var i => MvPolynomial.X i
  | .neg p => 1 - arithPoly p
  | .conj p q => arithPoly p * arithPoly q
  | .disj p q => 1 - (1 - arithPoly p) * (1 - arithPoly q)
  | .all i p =>
      MvPolynomial.bind₁ (Function.update MvPolynomial.X i 0) (arithPoly p) *
        MvPolynomial.bind₁ (Function.update MvPolynomial.X i 1) (arithPoly p)
  | .ex i p =>
      1 - (1 - MvPolynomial.bind₁ (Function.update MvPolynomial.X i 0) (arithPoly p)) *
        (1 - MvPolynomial.bind₁ (Function.update MvPolynomial.X i 1) (arithPoly p))

theorem eval_bind₁_update (a : ℕ → R) (i : ℕ) (c : R) (P : MvPolynomial ℕ R) :
    MvPolynomial.eval a
        (MvPolynomial.bind₁ (Function.update MvPolynomial.X i (MvPolynomial.C c)) P) =
      MvPolynomial.eval (Function.update a i c) P := by
  change MvPolynomial.eval₂Hom (RingHom.id R) a _ =
    MvPolynomial.eval₂Hom (RingHom.id R) (Function.update a i c) P
  rw [MvPolynomial.eval₂Hom_bind₁]
  congr 2
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- The polynomial evaluates to the arithmetization. -/
theorem eval_arithPoly (p : QBF) : ∀ a : ℕ → R, MvPolynomial.eval a (arithPoly p) = arith a p := by
  induction p with
  | var i => intro a; simp [arithPoly, arith]
  | neg p ih => intro a; simp [arithPoly, arith, ih]
  | conj p q ihp ihq => intro a; simp [arithPoly, arith, ihp, ihq]
  | disj p q ihp ihq => intro a; simp [arithPoly, arith, ihp, ihq]
  | all i p ih =>
    intro a
    have h0 := eval_bind₁_update a i 0 (arithPoly p)
    have h1 := eval_bind₁_update a i 1 (arithPoly p)
    simp only [map_zero, map_one] at h0 h1
    simp only [arithPoly, arith, map_mul, h0, h1, ih]
  | ex i p ih =>
    intro a
    have h0 := eval_bind₁_update a i 0 (arithPoly p)
    have h1 := eval_bind₁_update a i 1 (arithPoly p)
    simp only [map_zero, map_one] at h0 h1
    simp only [arithPoly, arith, map_sub, map_mul, map_one, h0, h1, ih]

end QBF

end Complexity.Qbf

namespace Polynomial

/-- **The one-round soundness of sum-check**: two different polynomials of degree at most `d`
over a finite field agree on at most `d` points. -/
theorem card_eval_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] {g h : F[X]} {d : ℕ}
    (hne : g ≠ h) (hg : g.natDegree ≤ d) (hh : h.natDegree ≤ d) :
    (Finset.univ.filter fun r => g.eval r = h.eval r).card ≤ d := by
  have hsub : g - h ≠ 0 := sub_ne_zero.mpr hne
  calc (Finset.univ.filter fun r => g.eval r = h.eval r).card
      ≤ (g - h).roots.toFinset.card := by
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        simp [Multiset.mem_toFinset, mem_roots hsub, IsRoot, hr]
    _ ≤ (g - h).roots.card := Multiset.toFinset_card_le _
    _ ≤ (g - h).natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le g h).trans (max_le hg hh)

/-- The same estimate as a probability: a verifier that checks a claimed polynomial `g` against
the true one `h` at a uniformly random point of `F` is fooled with probability at most `d / |F|`. -/
theorem card_eval_eq_le_div {F : Type*} [Field F] [Fintype F] [DecidableEq F] {g h : F[X]}
    {d : ℕ} (hne : g ≠ h) (hg : g.natDegree ≤ d) (hh : h.natDegree ≤ d) :
    ((Finset.univ.filter fun r => g.eval r = h.eval r).card : ℚ) / Fintype.card F ≤
      d / Fintype.card F := by
  gcongr
  exact_mod_cast card_eval_eq_le hne hg hh

end Polynomial
