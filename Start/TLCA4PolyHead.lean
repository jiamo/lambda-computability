import Start.TLCA4StatmanProof

/-!
# Series V, round 3, run 2, part B1: the head of `p x` for a polynomial whose first monomial is
not `M` (row M20-TLCA4-BETAETA)

The η-aware head comparison of B1 starts from the shape of the head normal form of `p x`.  If the
first monomial of the polynomial `p` is `B` or `Bⁿ⁺¹ X`, then `p x` head-reduces in at most five
steps to an abstraction:

* **`polyApp_reduces_lam`** — for `m = Bⁿ⁺¹ X` or `m = B`, the λ-translation of
  `(m ∘ m₂ ∘ … ∘ m_k) x` reduces to a λ-abstraction.

Not proved (first missing claim of B1): an abstraction can be βη-equal to `x (p x)` only through
an η-step removing its binder, so the head normal form of `p x` must be `λz. x (p x)' z` up to η;
comparing with the head normal form of `x (p x)` would exclude these first monomials.  See
`docs/goal/evidence/M20-TLCA4-BETAETA.md`, "Series V, round 3, run 2".
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- `Bⁿ⁺¹ X` and `B` applied to one argument head-reduce to an abstraction. -/
theorem mono_app_reduces_lam (m : Mono) (hm : m.base = .B ∨ 0 < m.n) (u : Lambda) :
    ∃ t, Lambda.reduces (.app (toLam m.tm) u) (.lam t) := by
  obtain ⟨n, base⟩ := m
  cases n with
  | succ n =>
      exact ⟨_, hsteps_reduces (hsteps_B2 (toLam (bpow n base.tm)) u)⟩
  | zero =>
      rcases hm with hb | hn
      · simp only at hb
        subst hb
        exact ⟨_, hsteps_reduces (hsteps_one (.weak (wstep_B1 u)))⟩
      · exact absurd hn (Nat.lt_irrefl 0)

/-- **The head of `p x` is an abstraction when the first monomial of `p` is `B` or `Bⁿ⁺¹ X`.** -/
theorem polyApp_reduces_lam (m : Mono) (hm : m.base = .B ∨ 0 < m.n) (ps : List Mono) :
    ∃ t, Lambda.reduces (toLam (app (polyTm m ps) (var 0))) (.lam t) := by
  cases ps with
  | nil => exact mono_app_reduces_lam m hm _
  | cons m' ps =>
      obtain ⟨t, ht⟩ := mono_app_reduces_lam m hm (.app (toLam (polyTm m' ps)) (.var 0))
      refine ⟨t, Lambda.reduces_trans ?_ ht⟩
      exact hsteps_reduces (hsteps_B3 (toLam m.tm) (toLam (polyTm m' ps)) (.var 0) [])

end TLCA4
