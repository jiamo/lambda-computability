/-
Realizers: closed lambda terms that compute total numeric functions on Church
numerals, and a compiler that turns every primitive recursive construction into
such a term.

This file is the lambda-calculus side of the reverse direction
`recursive → lambda-definable`.
-/

import Start.Recursion

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- `F` realizes the total function `f` when `F` is closed and `F (church n)`
reduces to `church (f n)` for every `n`. -/
def Realizes (F : Lambda) (f : ℕ → ℕ) : Prop :=
  Lambda.IsClosed F ∧ ∀ n, Lambda.reduces (Lambda.app F (Lambda.church n)) (Lambda.church (f n))

theorem Realizes.of_eq {F : Lambda} {f g : ℕ → ℕ} (h : Realizes F f) (he : ∀ n, f n = g n) :
    Realizes F g := by
  refine ⟨h.1, fun n => ?_⟩
  rw [← he n]
  exact h.2 n

------------------------------------------------------------------------
-- Closedness of the basic arithmetic combinators
------------------------------------------------------------------------

theorem add_closed : Lambda.IsClosed Lambda.add := by
  unfold Lambda.IsClosed
  aesop

theorem sub_closed : Lambda.IsClosed Lambda.sub := by
  intro s x
  simp [Lambda.sub, Lambda.subst, Lambda.IsClosed_imp_subst_eq Lambda.pred_closed]

theorem natPair'_closed : Lambda.IsClosed Lambda.natPair' := by
  intro s x
  simp [Lambda.natPair', Lambda.subst,
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.lt'_closed,
    Lambda.IsClosed_imp_subst_eq add_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.mult_closed]

theorem sqrt_v2_closed : Lambda.IsClosed Lambda.sqrt_v2 := by
  intro s x
  simp [Lambda.sqrt_v2, Lambda.subst,
    Lambda.IsClosed_imp_subst_eq Lambda.fix_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.sqrt_iter_v2_closed,
    Lambda.IsClosed_imp_subst_eq (Lambda.church_closed 0)]

theorem unpairLeft_impl_closed : Lambda.IsClosed Lambda.unpairLeft_impl := by
  intro s x
  simp [Lambda.unpairLeft_impl, Lambda.subst,
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.lt'_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.mult_closed,
    Lambda.IsClosed_imp_subst_eq sub_closed,
    Lambda.IsClosed_imp_subst_eq sqrt_v2_closed]

theorem unpairRight_impl_closed : Lambda.IsClosed Lambda.unpairRight_impl := by
  intro s x
  simp [Lambda.unpairRight_impl, Lambda.subst,
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.lt'_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.mult_closed,
    Lambda.IsClosed_imp_subst_eq sub_closed,
    Lambda.IsClosed_imp_subst_eq sqrt_v2_closed]

------------------------------------------------------------------------
-- Combinators on realizers
------------------------------------------------------------------------

/-- `mkApp1 G F` is `fun x => G (F x)`. -/
def mkApp1 (G F : Lambda) : Lambda :=
  Lambda.lam (Lambda.app G (Lambda.app F (Lambda.var 0)))

/-- `mkApp2 G F₁ F₂` is `fun x => G (F₁ x) (F₂ x)`. -/
def mkApp2 (G F₁ F₂ : Lambda) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app G (Lambda.app F₁ (Lambda.var 0)))
    (Lambda.app F₂ (Lambda.var 0)))

/-- `mkConst c` is the constant function `fun _ => church c`. -/
def mkConst (c : ℕ) : Lambda := Lambda.lam (Lambda.church c)

/-- `mkIter N S I` is `fun x => (N x) S (I x)`: it applies the Church numeral
produced by `N` to the step term `S` and the initial value `I x`. -/
def mkIter (N S I : Lambda) : Lambda :=
  Lambda.lam (Lambda.app (Lambda.app (Lambda.app N (Lambda.var 0)) S)
    (Lambda.app I (Lambda.var 0)))

theorem mkApp1_closed {G F : Lambda} (hG : Lambda.IsClosed G) (hF : Lambda.IsClosed F) :
    Lambda.IsClosed (mkApp1 G F) := by
  intro s x
  simp [mkApp1, Lambda.subst, Lambda.IsClosed_imp_subst_eq hG, Lambda.IsClosed_imp_subst_eq hF]

theorem mkApp2_closed {G F₁ F₂ : Lambda} (hG : Lambda.IsClosed G) (h₁ : Lambda.IsClosed F₁)
    (h₂ : Lambda.IsClosed F₂) : Lambda.IsClosed (mkApp2 G F₁ F₂) := by
  intro s x
  simp [mkApp2, Lambda.subst, Lambda.IsClosed_imp_subst_eq hG, Lambda.IsClosed_imp_subst_eq h₁,
    Lambda.IsClosed_imp_subst_eq h₂]

theorem mkConst_closed (c : ℕ) : Lambda.IsClosed (mkConst c) := by
  intro s x
  simp [mkConst, Lambda.subst, Lambda.IsClosed_imp_subst_eq (Lambda.church_closed c)]

theorem mkIter_closed {N S I : Lambda} (hN : Lambda.IsClosed N) (hS : Lambda.IsClosed S)
    (hI : Lambda.IsClosed I) : Lambda.IsClosed (mkIter N S I) := by
  intro s x
  simp [mkIter, Lambda.subst, Lambda.IsClosed_imp_subst_eq hN, Lambda.IsClosed_imp_subst_eq hS,
    Lambda.IsClosed_imp_subst_eq hI]

theorem Realizes.const (c : ℕ) : Realizes (mkConst c) (fun _ => c) := by
  refine ⟨mkConst_closed c, fun n => ?_⟩
  have h := @Lambda.beta_reduces (Lambda.church c) (Lambda.church n)
  simpa [mkConst, Lambda.IsClosed_imp_subst_eq (Lambda.church_closed c)] using h

theorem Realizes.comp1 {G F : Lambda} {g f : ℕ → ℕ}
    (hG : Realizes G g) (hF : Realizes F f) : Realizes (mkApp1 G F) (fun n => g (f n)) := by
  obtain ⟨hGc, hGr⟩ := hG
  obtain ⟨hFc, hFr⟩ := hF
  refine ⟨mkApp1_closed hGc hFc, fun n => ?_⟩
  have h1 : Lambda.reduces (Lambda.app (mkApp1 G F) (Lambda.church n))
      (Lambda.app G (Lambda.app F (Lambda.church n))) := by
    have h := @Lambda.beta_reduces (Lambda.app G (Lambda.app F (Lambda.var 0))) (Lambda.church n)
    simpa [mkApp1, Lambda.subst, Lambda.IsClosed_imp_subst_eq hGc,
      Lambda.IsClosed_imp_subst_eq hFc] using h
  exact Lambda.reduces_trans h1
    (Lambda.reduces_trans (Lambda.reduces_app_right (hFr n)) (hGr (f n)))

/-- A binary closed term `G` that computes `op` on Church numerals lifts to a
realizer combinator. -/
theorem Realizes.binop {G F₁ F₂ : Lambda} {op : ℕ → ℕ → ℕ} {f₁ f₂ : ℕ → ℕ}
    (hGc : Lambda.IsClosed G)
    (hG : ∀ a b, Lambda.reduces (Lambda.app (Lambda.app G (Lambda.church a)) (Lambda.church b))
      (Lambda.church (op a b)))
    (h₁ : Realizes F₁ f₁) (h₂ : Realizes F₂ f₂) :
    Realizes (mkApp2 G F₁ F₂) (fun n => op (f₁ n) (f₂ n)) := by
  obtain ⟨h₁c, h₁r⟩ := h₁
  obtain ⟨h₂c, h₂r⟩ := h₂
  refine ⟨mkApp2_closed hGc h₁c h₂c, fun n => ?_⟩
  have h1 : Lambda.reduces (Lambda.app (mkApp2 G F₁ F₂) (Lambda.church n))
      (Lambda.app (Lambda.app G (Lambda.app F₁ (Lambda.church n)))
        (Lambda.app F₂ (Lambda.church n))) := by
    have h := @Lambda.beta_reduces
      (Lambda.app (Lambda.app G (Lambda.app F₁ (Lambda.var 0))) (Lambda.app F₂ (Lambda.var 0)))
      (Lambda.church n)
    simpa [mkApp2, Lambda.subst, Lambda.IsClosed_imp_subst_eq hGc,
      Lambda.IsClosed_imp_subst_eq h₁c, Lambda.IsClosed_imp_subst_eq h₂c] using h
  refine Lambda.reduces_trans h1 (Lambda.reduces_trans ?_ (hG (f₁ n) (f₂ n)))
  exact Lambda.reduces_app (Lambda.reduces_app_right (h₁r n)) (h₂r n)

/-- Iterating a realizer along a Church numeral. -/
theorem Realizes.iterate_church {S : Lambda} {sigma : ℕ → ℕ} (hS : Realizes S sigma) (a n : ℕ) :
    Lambda.reduces (Lambda.iterate S (Lambda.church a) n) (Lambda.church (sigma^[n] a)) := by
  induction n with
  | zero => simpa [Lambda.iterate_zero] using Lambda.reduces.refl (Lambda.church a)
  | succ n ih =>
      rw [Lambda.iterate_succ, Function.iterate_succ_apply']
      exact Lambda.reduces_trans (Lambda.reduces_app_right ih) (hS.2 (sigma^[n] a))

theorem Realizes.iter {N S I : Lambda} {nu sigma iota : ℕ → ℕ}
    (hN : Realizes N nu) (hS : Realizes S sigma) (hI : Realizes I iota) :
    Realizes (mkIter N S I) (fun x => sigma^[nu x] (iota x)) := by
  refine ⟨mkIter_closed hN.1 hS.1 hI.1, fun n => ?_⟩
  have h1 : Lambda.reduces (Lambda.app (mkIter N S I) (Lambda.church n))
      (Lambda.app (Lambda.app (Lambda.app N (Lambda.church n)) S)
        (Lambda.app I (Lambda.church n))) := by
    have h := @Lambda.beta_reduces
      (Lambda.app (Lambda.app (Lambda.app N (Lambda.var 0)) S) (Lambda.app I (Lambda.var 0)))
      (Lambda.church n)
    simpa [mkIter, Lambda.subst, Lambda.IsClosed_imp_subst_eq hN.1,
      Lambda.IsClosed_imp_subst_eq hS.1, Lambda.IsClosed_imp_subst_eq hI.1] using h
  have h2 : Lambda.reduces
      (Lambda.app (Lambda.app (Lambda.app N (Lambda.church n)) S) (Lambda.app I (Lambda.church n)))
      (Lambda.app (Lambda.app (Lambda.church (nu n)) S) (Lambda.church (iota n))) :=
    Lambda.reduces_app (Lambda.reduces_app_left (hN.2 n)) (hI.2 n)
  refine Lambda.reduces_trans h1 (Lambda.reduces_trans h2 ?_)
  exact Lambda.reduces_trans (Lambda.church_reduces_iterate (nu n) S (Lambda.church (iota n)))
    (Realizes.iterate_church hS (iota n) (nu n))

------------------------------------------------------------------------
-- The base realizers
------------------------------------------------------------------------

theorem Realizes.zero : Realizes (mkConst 0) (fun _ => 0) := Realizes.const 0

theorem Realizes.succ : Realizes Lambda.succ Nat.succ :=
  ⟨Lambda.succ_closed, fun n => Lambda.succ_works n⟩

theorem Realizes.left : Realizes Lambda.unpairLeft_impl (fun n => (Nat.unpair n).1) :=
  ⟨unpairLeft_impl_closed, fun n => Lambda.unpairLeft_works n⟩

theorem Realizes.right : Realizes Lambda.unpairRight_impl (fun n => (Nat.unpair n).2) :=
  ⟨unpairRight_impl_closed, fun n => Lambda.unpairRight_works n⟩

theorem Realizes.natPair {F₁ F₂ : Lambda} {f₁ f₂ : ℕ → ℕ}
    (h₁ : Realizes F₁ f₁) (h₂ : Realizes F₂ f₂) :
    Realizes (mkApp2 Lambda.natPair' F₁ F₂) (fun n => Nat.pair (f₁ n) (f₂ n)) :=
  Realizes.binop natPair'_closed Lambda.natPair'_works h₁ h₂

------------------------------------------------------------------------
-- Primitive recursion
------------------------------------------------------------------------

/-- The state transformer of the primitive-recursion loop: on a state
`⟨z, y, v⟩` (coded as `pair z (pair y v)`) it produces `⟨z, y+1, g ⟨z,y,v⟩⟩`. -/
def precStep (F₂ : Lambda) : Lambda :=
  mkApp2 Lambda.natPair' Lambda.unpairLeft_impl
    (mkApp2 Lambda.natPair'
      (mkApp1 Lambda.succ (mkApp1 Lambda.unpairLeft_impl Lambda.unpairRight_impl))
      F₂)

/-- The initial state of the primitive-recursion loop: `⟨z, 0, f z⟩`. -/
def precInit (F₁ : Lambda) : Lambda :=
  mkApp2 Lambda.natPair' Lambda.unpairLeft_impl
    (mkApp2 Lambda.natPair' (mkConst 0) (mkApp1 F₁ Lambda.unpairLeft_impl))

/-- The realizer for the `prec` constructor. -/
def precRealizer (F₁ F₂ : Lambda) : Lambda :=
  mkApp1 Lambda.unpairRight_impl
    (mkApp1 Lambda.unpairRight_impl
      (mkIter Lambda.unpairRight_impl (precStep F₂) (precInit F₁)))

/-- The numeric state transformer matching `precStep`. -/
def precStepNum (g : ℕ → ℕ) (s : ℕ) : ℕ :=
  Nat.pair (Nat.unpair s).1 (Nat.pair ((Nat.unpair (Nat.unpair s).2).1 + 1) (g s))

theorem precStepNum_iterate (f g : ℕ → ℕ) (z n : ℕ) :
    (precStepNum g)^[n] (Nat.pair z (Nat.pair 0 (f z)))
      = Nat.pair z (Nat.pair n (Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp [precStepNum, Nat.unpair_pair]

theorem Realizes.precStep_spec {F₂ : Lambda} {g : ℕ → ℕ} (h₂ : Realizes F₂ g) :
    Realizes (precStep F₂) (precStepNum g) := by
  have h := Realizes.natPair Realizes.left
    (Realizes.natPair (Realizes.comp1 Realizes.succ (Realizes.comp1 Realizes.left Realizes.right))
      h₂)
  exact h.of_eq (fun n => rfl)

theorem Realizes.precInit_spec {F₁ : Lambda} {f : ℕ → ℕ} (h₁ : Realizes F₁ f) :
    Realizes (precInit F₁)
      (fun x => Nat.pair (Nat.unpair x).1 (Nat.pair 0 (f (Nat.unpair x).1))) := by
  have h := Realizes.natPair Realizes.left
    (Realizes.natPair (Realizes.const 0) (Realizes.comp1 h₁ Realizes.left))
  exact h.of_eq (fun n => rfl)

theorem Realizes.prec {F₁ F₂ : Lambda} {f g : ℕ → ℕ}
    (h₁ : Realizes F₁ f) (h₂ : Realizes F₂ g) :
    Realizes (precRealizer F₁ F₂)
      (Nat.unpaired fun z n => Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n) := by
  have hiter := Realizes.iter Realizes.right (Realizes.precStep_spec h₂)
    (Realizes.precInit_spec h₁)
  have h := Realizes.comp1 Realizes.right (Realizes.comp1 Realizes.right hiter)
  refine h.of_eq (fun x => ?_)
  simp only [precStepNum_iterate f g (Nat.unpair x).1 (Nat.unpair x).2, Nat.unpair_pair,
    Nat.unpaired]

------------------------------------------------------------------------
-- The compiler
------------------------------------------------------------------------

/-- **Every primitive recursive function has a lambda realizer.** -/
theorem exists_realizer_of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ F : Lambda, Realizes F f := by
  induction hf with
  | zero => exact ⟨mkConst 0, Realizes.zero⟩
  | succ => exact ⟨Lambda.succ, Realizes.succ⟩
  | left => exact ⟨Lambda.unpairLeft_impl, Realizes.left⟩
  | right => exact ⟨Lambda.unpairRight_impl, Realizes.right⟩
  | pair _ _ ih₁ ih₂ =>
      obtain ⟨F₁, hF₁⟩ := ih₁
      obtain ⟨F₂, hF₂⟩ := ih₂
      exact ⟨mkApp2 Lambda.natPair' F₁ F₂, Realizes.natPair hF₁ hF₂⟩
  | comp _ _ ih₁ ih₂ =>
      obtain ⟨F₁, hF₁⟩ := ih₁
      obtain ⟨F₂, hF₂⟩ := ih₂
      exact ⟨mkApp1 F₁ F₂, Realizes.comp1 hF₁ hF₂⟩
  | prec _ _ ih₁ ih₂ =>
      obtain ⟨F₁, hF₁⟩ := ih₁
      obtain ⟨F₂, hF₂⟩ := ih₂
      exact ⟨precRealizer F₁ F₂, Realizes.prec hF₁ hF₂⟩

/-- A realizer for a total function witnesses lambda-computability. -/
theorem lambdaComputable_of_realizes {F : Lambda} {f : ℕ → ℕ} (hF : Realizes F f) :
    LambdaComputable (fun n => Part.some (f n)) := by
  refine ⟨F, fun n m => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact Part.some_inj.mp h ▸ hF.2 n
  · exact congrArg Part.some (Lambda.unique_church_reduct (hF.2 n) h)

/-- **Primitive recursive functions are lambda-computable.** -/
theorem lambdaComputable_of_primrec {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    LambdaComputable (fun n => Part.some (f n)) := by
  obtain ⟨F, hF⟩ := exists_realizer_of_primrec hf
  exact lambdaComputable_of_realizes hF

end Lambda

end
