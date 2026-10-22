import Start.TLCA4Polynomial

/-!
# TLCA open problem 4 under βη: the `B`-fragment of Statman's first step
(rows M20-TLCA4-STATMAN-STEP-ONE, M20-TLCA4-POLYNOMIAL; series V, round 2, run 2)

Statman's first step says that a fixed-point combinator built from `B`, `M`, `I` is βη-equal to a
polynomial.  This module proves the part of it that concerns composition and `B`:

* `lift_toLam_of_isBMI` — the translation of a closed `B`,`M`,`I`-term is closed;
* `betaEtaConv_lam` — βη-conversion is a congruence under `λ`;
* **`ext1_of_weq`**, **`ext2_of_weq`** — extensionality for closed terms: if `t x =w s x`
  (resp. `t x y =w s x y`) for fresh variables, then `t =βη s`;
* **`comp_poly`** — the composite of two polynomials is βη-equal to a polynomial
  (concatenation of the monomial lists);
* **`B_poly`** — `B p` is βη-equal to the polynomial obtained from `p` by raising every
  monomial `Bⁿ X` to `Bⁿ⁺¹ X` (`B` distributes over composition);
* `PolyGen` — the grammar `Y ::= B | M | I | B Y | B Y Z | I Y`;
* **`polyGen_betaEta_poly`** — every term of the grammar is βη-equal to a polynomial
  (Statman's first step on this fragment; the fixed-point hypothesis is not needed there).

The full `StatmanStepOne` is **not** proved: the first missing case is a term headed by `M` with an
argument, `M Y` (acting as `Y Y`), where the fixed-point hypothesis must be used; applications with
more arguments (`B Y Z W`, `I Y Z`) are outside the fragment as well (see
`docs/goal/evidence/M20-TLCA4-BETAETA.md`, "Series V, round 2, run 2").
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- The translation of a closed `B`,`M`,`I`-term is invariant under lifting. -/
theorem lift_toLam_of_isBMI {t : Tm} (h : IsBMI t) (n k : ℕ) :
    Lambda.lift n k (toLam t) = toLam t := by
  induction h generalizing k with
  | B => simp only [toLam, lamB, Lambda.lift]; split_ifs <;> first | rfl | omega
  | M => simp only [toLam, lamM, Lambda.lift]; split_ifs <;> first | rfl | omega
  | I => simp only [toLam, lamI, Lambda.lift]; split_ifs <;> first | rfl | omega
  | app _ _ ihu ihv => simp only [toLam, Lambda.lift, ihu, ihv]

theorem betaEtaStep_lam {t t' : Lambda} (h : Lambda.betaEtaStep t t') :
    Lambda.betaEtaStep (.lam t) (.lam t') := by
  cases h with
  | beta h => exact .beta (.lam _ _ h)
  | eta h => exact .eta (.lam h)

/-- βη-conversion is a congruence under `λ`. -/
theorem betaEtaConv_lam {t t' : Lambda} (h : Lambda.betaEtaConv t t') :
    Lambda.betaEtaConv (.lam t) (.lam t') := by
  induction h with
  | refl => exact .refl _
  | step _ hs ih => exact ih.step (betaEtaStep_lam hs)
  | symm_step _ hs ih => exact ih.symm_step (betaEtaStep_lam hs)

/-- `λx. t x →η t` for a closed `t`. -/
theorem eta1 {t : Tm} (ht : IsBMI t) :
    Lambda.betaEtaConv (.lam (toLam (app t (var 0)))) (toLam t) := by
  have e := Lambda.etaStep.eta (toLam t)
  rw [lift_toLam_of_isBMI ht] at e
  exact (Lambda.betaEtaConv.refl _).step (.eta e)

/-- `λxy. t x y →η t` for a closed `t`. -/
theorem eta2 {t : Tm} (ht : IsBMI t) :
    Lambda.betaEtaConv (.lam (.lam (toLam (app (app t (var 1)) (var 0))))) (toLam t) := by
  have e := Lambda.etaStep.eta (toLam (app t (var 0)))
  have hl : Lambda.lift 1 0 (toLam (app t (var 0))) = toLam (app t (var 1)) := by
    simp only [toLam, Lambda.lift, lift_toLam_of_isBMI ht]; rfl
  rw [hl] at e
  exact ((Lambda.betaEtaConv.refl _).step (.eta (.lam e))).trans (eta1 ht)

/-- **Extensionality, one argument.** -/
theorem ext1_of_weq {t s : Tm} (ht : IsBMI t) (hs : IsBMI s)
    (h : WEq (app t (var 0)) (app s (var 0))) : Lambda.betaEtaConv (toLam t) (toLam s) :=
  (betaEtaConv_symm (eta1 ht)).trans ((betaEtaConv_lam (toLam_weq h)).trans (eta1 hs))

/-- **Extensionality, two arguments.** -/
theorem ext2_of_weq {t s : Tm} (ht : IsBMI t) (hs : IsBMI s)
    (h : WEq (app (app t (var 1)) (var 0)) (app (app s (var 1)) (var 0))) :
    Lambda.betaEtaConv (toLam t) (toLam s) :=
  (betaEtaConv_symm (eta2 ht)).trans
    ((betaEtaConv_lam (betaEtaConv_lam (toLam_weq h))).trans (eta2 hs))

theorem actList_append (ps qs : List Mono) (x : Tm) :
    actList (ps ++ qs) x = actList ps (actList qs x) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.cons_append, actList, ih]

theorem actList_weq (ps : List Mono) {x y : Tm} (h : WEq x y) :
    WEq (actList ps x) (actList ps y) := by
  induction ps with
  | nil => exact h
  | cons p ps ih => exact Tm.WEq.appR _ ih

/-- **Composition of polynomials.** -/
theorem comp_poly (m : Mono) (ps : List Mono) (m' : Mono) (qs : List Mono) :
    Lambda.betaEtaConv (toLam (comp (polyTm m ps) (polyTm m' qs)))
      (toLam (polyTm m (ps ++ m' :: qs))) := by
  refine ext1_of_weq (.app (.app .B (polyTm_isBMI _ _)) (polyTm_isBMI _ _)) (polyTm_isBMI _ _) ?_
  have h1 := comp_action (polyTm m ps) (polyTm m' qs) (var 0)
  have h2 := polyTm_action m ps (app (polyTm m' qs) (var 0))
  have h3 := actList_weq (m :: ps) (polyTm_action m' qs (var 0))
  have h4 := polyTm_action m (ps ++ m' :: qs) (var 0)
  have e : actList (m :: (ps ++ m' :: qs)) (var 0) =
      actList (m :: ps) (actList (m' :: qs) (var 0)) := by
    rw [← List.cons_append, actList_append]
  rw [e] at h4
  exact ((h1.trans h2).trans h3).trans h4.symm

/-- Raise a monomial: `Bⁿ X ↦ Bⁿ⁺¹ X`. -/
def Mono.raise (m : Mono) : Mono := ⟨m.n + 1, m.base⟩

theorem Mono.raise_tm (m : Mono) : m.raise.tm = app B m.tm := rfl

/-- `(B m₁) ((B m₂) (… ((B m_k) z))) w =w m₁ (m₂ (… (m_k (z w))))`. -/
theorem actList_raise (ps : List Mono) (z w : Tm) :
    WEq (app (actList (ps.map Mono.raise) z) w) (actList ps (app z w)) := by
  induction ps with
  | nil => exact WEq.refl _
  | cons p ps ih =>
      simp only [List.map_cons, actList, Mono.raise_tm]
      exact (WEq.step (WStep.b _ _ _)).trans (Tm.WEq.appR _ ih)

/-- **`B` distributes over composition**: `B p` is βη-equal to the raised polynomial. -/
theorem B_poly (m : Mono) (ps : List Mono) :
    Lambda.betaEtaConv (toLam (app B (polyTm m ps)))
      (toLam (polyTm m.raise (ps.map Mono.raise))) := by
  refine ext2_of_weq (.app .B (polyTm_isBMI _ _)) (polyTm_isBMI _ _) ?_
  have h1 : WEq (app (app (app B (polyTm m ps)) (var 1)) (var 0))
      (app (polyTm m ps) (app (var 1) (var 0))) := WEq.step (WStep.b _ _ _)
  have h2 := polyTm_action m ps (app (var 1) (var 0))
  have h3 := Tm.WEq.appL (polyTm_action m.raise (ps.map Mono.raise) (var 1)) (var 0)
  have h4 := actList_raise (m :: ps) (var 1) (var 0)
  rw [← List.map_cons] at h3
  exact (h1.trans h2).trans (h3.trans h4).symm

/-- The grammar `Y ::= B | M | I | B Y | B Y Z | I Y`. -/
inductive PolyGen : Tm → Prop
  | B : PolyGen Tm.B
  | M : PolyGen Tm.M
  | I : PolyGen Tm.I
  | B1 {y : Tm} : PolyGen y → PolyGen (app Tm.B y)
  | B2 {y z : Tm} : PolyGen y → PolyGen z → PolyGen (app (app Tm.B y) z)
  | I1 {y : Tm} : PolyGen y → PolyGen (app Tm.I y)

/-- **Every term of the `B`-fragment is βη-equal to a polynomial.** -/
theorem polyGen_betaEta_poly {Y : Tm} (h : PolyGen Y) :
    ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam Y) (toLam (polyTm m ps)) := by
  induction h with
  | B => exact ⟨⟨0, .B⟩, [], .refl _⟩
  | M => exact ⟨⟨0, .M⟩, [], .refl _⟩
  | I => exact ⟨⟨0, .I⟩, [], .refl _⟩
  | B1 _ ih =>
      obtain ⟨m, ps, hp⟩ := ih
      refine ⟨m.raise, ps.map Mono.raise, ?_⟩
      exact (betaEtaConv_app_right lamB hp).trans (B_poly m ps)
  | @B2 y z _ _ ihy ihz =>
      obtain ⟨m, ps, hp⟩ := ihy
      obtain ⟨m', qs, hq⟩ := ihz
      refine ⟨m, ps ++ m' :: qs, ?_⟩
      have e1 := betaEtaConv_app_left (betaEtaConv_app_right lamB hp) (toLam z)
      have e2 := betaEtaConv_app_right (.app lamB (toLam (polyTm m ps))) hq
      exact (e1.trans e2).trans (comp_poly m ps m' qs)
  | @I1 y _ ih =>
      obtain ⟨m, ps, hp⟩ := ih
      exact ⟨m, ps, (Lambda.betaEtaConv.of_reduces
        (Lambda.betaEtaReduces.of_reduces (reduces_I (toLam y)))).trans hp⟩

end TLCA4
