import Start.TLCA4PolyIdentity

/-!
# Series V, big round, run 5, item A3: the βη head-arity invariant (row M20-TLCA4-BETAETA)

A head normal form `λx₁ … x_k. y a₁ … a_l` whose head `y` is free has two quantities that
βη-reduction cannot change: the head variable `y` (read outside the binders) and the difference
`l - k` (an η-step removes one binder and one argument; β-steps happen inside the arguments).  By
Church–Rosser for βη this makes them invariants of βη-*conversion* between head normal forms.

* `NSp t h n` — `t` is `var h` applied to `n` arguments; `HSp t h d` — `t` is `λ^k. NSp` with
  free head `h` (outside the binders) and `d = n - k`;
* `HSp.betaEtaStep`, `HSp.betaEtaReduces` — the data are preserved by βη-reduction;
* `HSp.unique` — the data of a term are unique;
* **`HSp.betaEtaConv`** — βη-convertible terms with free-headed head normal forms have the same
  head and the same arity difference;
* **`fixedPoint_hsp`** — if `Y` is a βη fixed-point combinator, every free-headed head normal form
  βη-convertible to `Y x` has head `x` and arity difference `1`;
* `not_fixedPoint_of_hsp` — the contrapositive, as a test that excludes candidates.
-/

set_option autoImplicit false

namespace TLCA4

/-- `t` is the variable `h` applied to `n` arguments. -/
inductive NSp : Lambda → ℕ → ℕ → Prop
  | var (h : ℕ) : NSp (.var h) h 0
  | app {f : Lambda} {h n : ℕ} (a : Lambda) : NSp f h n → NSp (.app f a) h (n + 1)

/-- `t = λ^k. y a₁ … a_n` where the head `y` is free and denotes the variable `h` outside the
binders; `d = n - k`. -/
inductive HSp : Lambda → ℕ → ℤ → Prop
  | neu {t : Lambda} {h n : ℕ} : NSp t h n → HSp t h n
  | lam {t : Lambda} {h : ℕ} {d : ℤ} : HSp t (h + 1) d → HSp (.lam t) h (d - 1)

theorem NSp.not_lam {t : Lambda} {h n : ℕ} (hs : NSp (.lam t) h n) : False := by cases hs

theorem NSp.unique {t : Lambda} {h n h' n' : ℕ} (hs : NSp t h n) (hs' : NSp t h' n') :
    h = h' ∧ n = n' := by
  induction hs generalizing n' with
  | var => cases hs'; exact ⟨rfl, rfl⟩
  | app a _ ih =>
    cases hs' with
    | app _ hf => obtain ⟨rfl, rfl⟩ := ih hf; exact ⟨rfl, rfl⟩

theorem HSp.unique {t : Lambda} {h h' : ℕ} {d d' : ℤ} (hs : HSp t h d) (hs' : HSp t h' d') :
    h = h' ∧ d = d' := by
  induction hs generalizing h' d' with
  | neu hn =>
    cases hs' with
    | neu hn' => obtain ⟨rfl, rfl⟩ := hn.unique hn'; exact ⟨rfl, rfl⟩
    | lam _ => exact hn.not_lam.elim
  | lam _ ih =>
    cases hs' with
    | neu hn' => exact hn'.not_lam.elim
    | lam hb =>
      obtain ⟨h1, h2⟩ := ih hb
      exact ⟨by omega, by rw [h2]⟩

theorem NSp.step {t t' : Lambda} {h n : ℕ} (hs : NSp t h n) (hst : Lambda.step t t') :
    NSp t' h n := by
  induction hs generalizing t' with
  | var => exact (Lambda.step.var_inv hst).elim
  | app a hf ih =>
    rcases Lambda.step_app_inv hst with ⟨c, rfl, _⟩ | ⟨f', hf', rfl⟩ | ⟨a', _, rfl⟩
    · exact hf.not_lam.elim
    · exact .app a (ih hf')
    · exact .app a' hf

theorem NSp.etaStep {t t' : Lambda} {h n : ℕ} (hs : NSp t h n) (hst : Lambda.etaStep t t') :
    NSp t' h n := by
  induction hs generalizing t' with
  | var => cases hst
  | app a hf ih =>
    cases hst with
    | app_left _ hf' => exact .app a (ih hf')
    | app_right _ _ => exact .app _ hf

/-- Lowering a lifted spine. -/
theorem NSp.of_lift : ∀ {u : Lambda} {h n : ℕ}, NSp (Lambda.lift 1 0 u) (h + 1) n → NSp u h n
  | .var y, h, n, hs => by
    simp only [Lambda.lift] at hs
    cases hs
    exact .var _
  | .app f a, h, n, hs => by
    simp only [Lambda.lift] at hs
    cases hs with
    | app _ hf => exact .app a (NSp.of_lift hf)
  | .lam b, h, n, hs => by
    simp only [Lambda.lift] at hs
    exact hs.not_lam.elim

theorem HSp.step {t t' : Lambda} {h : ℕ} {d : ℤ} (hs : HSp t h d) (hst : Lambda.step t t') :
    HSp t' h d := by
  induction hs generalizing t' with
  | neu hn => exact .neu (hn.step hst)
  | lam _ ih =>
    cases hst with
    | lam _ _ hb => exact .lam (ih hb)

theorem HSp.etaStep {t t' : Lambda} {h : ℕ} {d : ℤ} (hs : HSp t h d)
    (hst : Lambda.etaStep t t') : HSp t' h d := by
  induction hs generalizing t' with
  | neu hn => exact .neu (hn.etaStep hst)
  | @lam b h d hb ih =>
    cases hst with
    | lam hb' => exact .lam (ih hb')
    | eta u =>
      cases hb with
      | @neu _ _ n hn =>
        cases hn with
        | @app _ _ m _ hf =>
          have := NSp.of_lift hf
          have e : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
          rw [e]
          exact .neu this

theorem HSp.betaEtaReduces {t t' : Lambda} {h : ℕ} {d : ℤ} (hs : HSp t h d)
    (hr : Lambda.betaEtaReduces t t') : HSp t' h d := by
  induction hr with
  | refl => exact hs
  | tail _ hst ih =>
    rcases hst with hst | hst
    · exact ih.step hst
    · exact ih.etaStep hst

/-- **The βη head-arity invariant**: βη-convertible terms with free-headed head normal forms have
the same head variable and the same difference between argument count and binder count. -/
theorem HSp.betaEtaConv {t u : Lambda} {h h' : ℕ} {d d' : ℤ} (hs : HSp t h d) (hu : HSp u h' d')
    (hc : Lambda.betaEtaConv t u) : h = h' ∧ d = d' := by
  obtain ⟨w, h1, h2⟩ := hc.common_reduct
  exact (hs.betaEtaReduces h1).unique (hu.betaEtaReduces h2)

open Tm in
/-- **Head and arity of a βη fixed-point combinator**: if `Y x =βη x (Y x)`, then every
free-headed head normal form βη-convertible to `Y x` has head `x` and arity difference `1`. -/
theorem fixedPoint_hsp {Y : Tm}
    (hY : Lambda.betaEtaConv (toLam (app Y (var 0))) (toLam (app (var 0) (app Y (var 0)))))
    {t : Lambda} {h : ℕ} {d : ℤ} (ht : HSp t h d)
    (hc : Lambda.betaEtaConv (toLam (app Y (var 0))) t) : h = 0 ∧ d = 1 := by
  have hx : HSp (toLam (app (var 0) (app Y (var 0)))) 0 1 := by
    show HSp (.app (.var 0) _) 0 ((0 + 1 : ℕ) : ℤ)
    exact .neu (.app _ (.var 0))
  obtain ⟨h1, h2⟩ := hx.betaEtaConv ht ((betaEtaConv_symm hY).trans hc)
  exact ⟨h1.symm, h2.symm⟩

open Tm in
/-- A term `Y` such that `Y x` βη-reduces to a free-headed head normal form with head other than
`x` or arity difference other than `1` is not a βη fixed-point combinator. -/
theorem not_fixedPoint_of_hsp {Y : Tm} {t : Lambda} {h : ℕ} {d : ℤ} (ht : HSp t h d)
    (hr : Lambda.betaEtaReduces (toLam (app Y (var 0))) t) (hne : h ≠ 0 ∨ d ≠ 1) :
    ¬ Lambda.betaEtaConv (toLam (app Y (var 0))) (toLam (app (var 0) (app Y (var 0)))) := by
  intro hY
  obtain ⟨h1, h2⟩ := fixedPoint_hsp hY ht (Lambda.betaEtaConv.of_reduces hr)
  omega

end TLCA4
