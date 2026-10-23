import Start.TLCA4PolyHead

/-!
# Series V, big round, run 4, item A3: the monomials `Bⁿ I` are βη-units
(row M20-TLCA4-BETAETA)

A first constraint toward `¬ PolyFiveOne`: under βη the monomials `Bⁿ I` are the identity, and
they are units for `∘` (as terms, not only in their action).  So the monomials with base `I` can be
removed from a polynomial up to βη-conversion.

* `comp_I_left_betaEta`, `comp_I_right_betaEta` — `I ∘ u` and `t ∘ I` βη-reduce to `u` and `t`;
* `bpowI_betaEta` — `Bⁿ I` is βη-convertible to `I`;
* **`polyTm_headI_betaEta`** — a polynomial whose first monomial is `Bⁿ I`, followed by at least
  one more monomial, is βη-convertible to the polynomial without it;
* **`polyTm_lastI_betaEta`** — likewise for a last monomial `Bⁿ I`;
* `polyL_filter_noI` — removing all monomials of base `I` preserves βη-convertibility;
* `var_not_betaEtaConv_selfApp` — `x ≠βη x x`;
* **`polyFiveOne_noI`** — if some polynomial is a βη fixed-point combinator, then so is one with
  no monomial of base `I` (the all-`I` case is excluded since `x ≠βη x x`);
* `BENormal`, **`not_fixedPoint_of_normal`**, `poly_not_fixedPoint_of_normal` — if `Y x` has a
  βη-normal form, `Y` is not a βη fixed-point combinator.
-/

set_option autoImplicit false

namespace TLCA4

open Tm

theorem lift_lamI (k : ℕ) : Lambda.lift 1 k lamI = lamI := by simp [lamI, Lambda.lift]

/-- `I ∘ u` βη-reduces to `u`. -/
theorem comp_I_left_betaEta (u : Lambda) :
    Lambda.betaEtaReduces (.app (.app lamB lamI) u) u := by
  have h1 := reduces_B2 lamI u
  rw [lift_lamI] at h1
  have h2 : Lambda.reduces
      (.lam (.app lamI (.app (Lambda.lift 1 0 u) (.var 0))))
      (.lam (.app (Lambda.lift 1 0 u) (.var 0))) :=
    Lambda.reduces_lam (reduces_I _)
  refine (Lambda.betaEtaReduces.of_reduces (Lambda.reduces_trans h1 h2)).trans ?_
  exact Lambda.betaEtaReduces.single (.eta (.eta u))

/-- `t ∘ I` βη-reduces to `t`. -/
theorem comp_I_right_betaEta (t : Lambda) :
    Lambda.betaEtaReduces (.app (.app lamB t) lamI) t := by
  have h1 := reduces_B2 t lamI
  rw [lift_lamI] at h1
  have h2 : Lambda.reduces
      (.lam (.app (Lambda.lift 1 0 t) (.app lamI (.var 0))))
      (.lam (.app (Lambda.lift 1 0 t) (.var 0))) :=
    Lambda.reduces_lam (Lambda.reduces_app_right (reduces_I _))
  refine (Lambda.betaEtaReduces.of_reduces (Lambda.reduces_trans h1 h2)).trans ?_
  exact Lambda.betaEtaReduces.single (.eta (.eta t))

/-- `B I` βη-reduces to `I`. -/
theorem BI_betaEta : Lambda.betaEtaReduces (.app lamB lamI) lamI := by
  have h1 : Lambda.step (.app lamB lamI)
      (.lam (.lam (.app lamI (.app (.var 1) (.var 0))))) := by
    have := Lambda.step.beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) lamI
    simpa [lamB, Lambda.subst, lift_lamI] using this
  have h2 : Lambda.reduces (.lam (.lam (.app lamI (.app (.var 1) (.var 0)))))
      (.lam (.lam (.app (.var 1) (.var 0)))) :=
    Lambda.reduces_lam (Lambda.reduces_lam (reduces_I _))
  refine (Lambda.betaEtaReduces.of_reduces
    (Lambda.reduces.step _ _ _ h1 h2)).trans ?_
  exact Lambda.betaEtaReduces.single (.eta (.lam (.eta (.var 0))))

/-- **`Bⁿ I` is βη-convertible to `I`.** -/
theorem bpowI_betaEta : ∀ n : ℕ, Lambda.betaEtaConv (toLam (bpow n I)) lamI
  | 0 => .refl _
  | n + 1 => by
    have h := betaEtaConv_app_right lamB (bpowI_betaEta n)
    exact h.trans (Lambda.betaEtaConv.of_reduces BI_betaEta)

/-- **A leading monomial `Bⁿ I` can be dropped** up to βη. -/
theorem polyTm_headI_betaEta (n : ℕ) (m : Mono) (ps : List Mono) :
    Lambda.betaEtaConv (toLam (polyTm ⟨n, .I⟩ (m :: ps))) (toLam (polyTm m ps)) := by
  show Lambda.betaEtaConv (.app (.app lamB (toLam (bpow n I))) (toLam (polyTm m ps))) _
  have h := betaEtaConv_app_left (betaEtaConv_app_right lamB (bpowI_betaEta n))
    (toLam (polyTm m ps))
  exact h.trans (Lambda.betaEtaConv.of_reduces (comp_I_left_betaEta _))

/-- **A trailing monomial `Bⁿ I` can be dropped** up to βη. -/
theorem polyTm_lastI_betaEta (n : ℕ) (m : Mono) :
    Lambda.betaEtaConv (toLam (polyTm m [⟨n, .I⟩])) (toLam (polyTm m [])) := by
  show Lambda.betaEtaConv (.app (.app lamB (toLam m.tm)) (toLam (bpow n I))) _
  have h := betaEtaConv_app_right (.app lamB (toLam m.tm)) (bpowI_betaEta n)
  exact h.trans (Lambda.betaEtaConv.of_reduces (comp_I_right_betaEta _))

/-- The λ-term of a list of monomials read as a polynomial, with the empty list read as `I`. -/
def polyL : List Mono → Lambda
  | [] => lamI
  | m :: ps => toLam (polyTm m ps)

theorem polyL_cons (m : Mono) (L : List Mono) :
    Lambda.betaEtaConv (polyL (m :: L)) (.app (.app lamB (toLam m.tm)) (polyL L)) := by
  cases L with
  | nil => exact betaEtaConv_symm (Lambda.betaEtaConv.of_reduces (comp_I_right_betaEta _))
  | cons m' ps => exact .refl _

/-- **Removing the monomials with base `I`** does not change a polynomial up to βη. -/
theorem polyL_filter_noI : ∀ L : List Mono,
    Lambda.betaEtaConv (polyL L) (polyL (L.filter fun q => q.base ≠ .I))
  | [] => .refl _
  | m :: L => by
    have ih := polyL_filter_noI L
    have h1 := (polyL_cons m L).trans (betaEtaConv_app_right _ ih)
    by_cases hm : m.base = .I
    · obtain ⟨n, b⟩ := m
      simp only at hm
      subst hm
      have hf : (⟨n, .I⟩ :: L : List Mono).filter (fun q => q.base ≠ .I) =
          L.filter (fun q => q.base ≠ .I) := by simp
      rw [hf]
      refine h1.trans ((betaEtaConv_app_left (betaEtaConv_app_right lamB (bpowI_betaEta n))
        _).trans (Lambda.betaEtaConv.of_reduces (comp_I_left_betaEta _)))
    · have hf : (m :: L).filter (fun q => q.base ≠ .I) =
          m :: L.filter (fun q => q.base ≠ .I) := by simp [hm]
      rw [hf]
      exact h1.trans (betaEtaConv_symm (polyL_cons _ _))

/-- The βη-normal forms `x` and `x x` are distinct. -/
theorem var_not_betaEtaConv_selfApp (x : ℕ) :
    ¬ Lambda.betaEtaConv (.var x) (.app (.var x) (.var x)) := by
  intro h
  obtain ⟨w, h1, h2⟩ := h.common_reduct
  have hv : ∀ u, Lambda.betaEtaReduces (.var x) u → u = .var x := by
    intro u hu
    induction hu with
    | refl => rfl
    | tail _ hs ih =>
      subst ih
      rcases hs with hs | hs
      · exact (Lambda.step.var_inv hs).elim
      · cases hs
  have ha : ∀ u, Lambda.betaEtaReduces (.app (.var x) (.var x)) u →
      u = .app (.var x) (.var x) := by
    intro u hu
    induction hu with
    | refl => rfl
    | tail _ hs ih =>
      subst ih
      rcases hs with hs | hs
      · rcases Lambda.step_app_inv hs with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
        · cases hc
        · exact (Lambda.step.var_inv hf).elim
        · exact (Lambda.step.var_inv ha).elim
      · rcases hs with _ | ⟨_, hs⟩ | ⟨_, hs⟩ <;> cases hs
  rw [hv w h1] at h2
  exact absurd (ha _ h2) (by simp)

/-- **A βη fixed-point polynomial can be chosen without monomials of base `I`.** -/
theorem polyFiveOne_noI (h : PolyFiveOne) :
    ∃ (m : Mono) (ps : List Mono), (∀ q ∈ m :: ps, q.base ≠ .I) ∧
      Lambda.betaEtaConv (toLam (app (polyTm m ps) (var 0)))
        (toLam (app (var 0) (app (polyTm m ps) (var 0)))) := by
  obtain ⟨m, ps, hfix⟩ := h
  have hc : Lambda.betaEtaConv (toLam (polyTm m ps))
      (polyL ((m :: ps).filter fun q => q.base ≠ .I)) := polyL_filter_noI (m :: ps)
  -- transport the fixed-point equation along `hc`
  have tr : ∀ t : Lambda, Lambda.betaEtaConv (toLam (polyTm m ps)) t →
      Lambda.betaEtaConv (.app t (.var 0)) (.app (.var 0) (.app t (.var 0))) := by
    intro t ht
    have e1 := betaEtaConv_app_left ht (.var 0)
    have e2 := betaEtaConv_app_right (.var 0) e1
    exact (betaEtaConv_symm e1).trans (hfix.trans e2)
  generalize hF : (m :: ps).filter (fun q => q.base ≠ .I) = F at hc
  cases F with
  | nil =>
    have e := tr _ hc
    have hI : Lambda.betaEtaConv (.app lamI (.var 0)) (.var 0) :=
      Lambda.betaEtaConv.of_reduces (Lambda.betaEtaReduces.of_reduces (reduces_I _))
    have e' := (betaEtaConv_symm hI).trans (e.trans (betaEtaConv_app_right _ hI))
    exact (var_not_betaEtaConv_selfApp 0 e').elim
  | cons m' ps' =>
    refine ⟨m', ps', fun q hq => ?_, tr _ hc⟩
    have : q ∈ (m :: ps).filter (fun q => q.base ≠ .I) := by rw [hF]; exact hq
    simpa using (List.mem_filter.mp this).2

/-- A λ-term is βη-normal when it has no βη-step. -/
def BENormal (t : Lambda) : Prop := ∀ u, ¬ Lambda.betaEtaStep t u

theorem BENormal.reduces_eq {t u : Lambda} (ht : BENormal t) (h : Lambda.betaEtaReduces t u) :
    u = t := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact (ht _ hs).elim

/-- `x N` is βη-normal when `N` is. -/
theorem BENormal.app_var (x : ℕ) {t : Lambda} (ht : BENormal t) :
    BENormal (.app (.var x) t) := by
  intro u hs
  rcases hs with hs | hs
  · rcases Lambda.step_app_inv hs with ⟨c, hc, _⟩ | ⟨f', hf, _⟩ | ⟨a', ha, _⟩
    · cases hc
    · exact Lambda.step.var_inv hf
    · exact ht _ (.beta ha)
  · rcases hs with _ | ⟨_, hs⟩ | ⟨_, hs⟩
    · cases hs
    · exact ht _ (.eta hs)

/-- **A fixed-point combinator has no βη-normal form on a variable**: if `Y x` βη-reduces to a
βη-normal term, then `Y x ≠βη x (Y x)`. -/
theorem not_fixedPoint_of_normal (t : Lambda) (x : ℕ) {N : Lambda}
    (hN : Lambda.betaEtaReduces t N) (hn : BENormal N) :
    ¬ Lambda.betaEtaConv t (.app (.var x) t) := by
  intro h
  have h1 : Lambda.betaEtaConv N (.app (.var x) N) :=
    (betaEtaConv_symm (Lambda.betaEtaConv.of_reduces hN)).trans
      (h.trans (betaEtaConv_app_right _ (Lambda.betaEtaConv.of_reduces hN)))
  obtain ⟨w, hw1, hw2⟩ := h1.common_reduct
  have e1 := hn.reduces_eq hw1
  have e2 := (hn.app_var x).reduces_eq hw2
  have hsz := congrArg sizeOf (e1.symm.trans e2)
  simp at hsz

/-- The polynomial form: a polynomial `p` with `p x` βη-normalizing is not a βη fixed-point
combinator. -/
theorem poly_not_fixedPoint_of_normal (m : Mono) (ps : List Mono) {N : Lambda}
    (hN : Lambda.betaEtaReduces (toLam (app (polyTm m ps) (var 0))) N) (hn : BENormal N) :
    ¬ Lambda.betaEtaConv (toLam (app (polyTm m ps) (var 0)))
      (toLam (app (var 0) (app (polyTm m ps) (var 0)))) :=
  not_fixedPoint_of_normal _ 0 hN hn

end TLCA4
