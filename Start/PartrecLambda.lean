/-
The reverse direction of the Church–Turing correspondence for the lambda calculus:
every (total) computable function has a closed lambda realizer, hence is
lambda-computable.

The primitive recursive constructors are compiled in `Start/Realizer.lean`; here
they are combined with the minimisation combinator (`Start/Minimization.lean`)
through Kleene's normal form: a computable `f` is `g (n, μ k. h (n, k) = 0)` for
primitive recursive `g` and `h`, and on a total `f` the search always succeeds.
-/

import Start.Minimization
import Start.EvalGK

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- The identity realizer and closedness of `Lambda.mu`
------------------------------------------------------------------------

theorem I_closed : Lambda.IsClosed Lambda.I := by
  intro s x
  simp [Lambda.I, Lambda.subst]

theorem Realizes.identity : Realizes Lambda.I id := by
  refine ⟨I_closed, fun n => ?_⟩
  have h := @Lambda.beta_reduces (Lambda.var 0) (Lambda.church n)
  simpa [Lambda.I, Lambda.subst] using h

theorem mu_closed : Lambda.IsClosed Lambda.mu := by
  intro s x
  simp [Lambda.mu, Lambda.mu_body, Lambda.subst,
    Lambda.IsClosed_imp_subst_eq Lambda.fix_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.ifThenElse_closed,
    Lambda.IsClosed_imp_subst_eq isZero_closed,
    Lambda.IsClosed_imp_subst_eq Lambda.succ_closed,
    Lambda.IsClosed_imp_subst_eq (Lambda.church_closed 0)]

------------------------------------------------------------------------
-- Parameterised minimisation
------------------------------------------------------------------------

/-- The tested function of the parameterised search at parameter `n`:
`fun y => H (pair n y)`. -/
def muFiber (H : Lambda) (n : ℕ) : Lambda :=
  Lambda.lam (Lambda.app H (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
    (Lambda.var 0)))

/-- Parameterised minimisation: `fun n => mu (fun y => H (pair n y))`. -/
def muParam (H : Lambda) : Lambda :=
  Lambda.lam (Lambda.app Lambda.mu
    (Lambda.lam (Lambda.app H (Lambda.app (Lambda.app Lambda.natPair' (Lambda.var 1))
      (Lambda.var 0)))))

theorem muFiber_closed {H : Lambda} (hH : Lambda.IsClosed H) (n : ℕ) :
    Lambda.IsClosed (muFiber H n) := by
  intro s x
  simp [muFiber, Lambda.subst, Lambda.IsClosed_imp_subst_eq hH,
    Lambda.IsClosed_imp_subst_eq natPair'_closed,
    Lambda.IsClosed_imp_subst_eq (Lambda.church_closed n)]

theorem muParam_closed {H : Lambda} (hH : Lambda.IsClosed H) :
    Lambda.IsClosed (muParam H) := by
  intro s x
  simp [muParam, Lambda.subst, Lambda.IsClosed_imp_subst_eq hH,
    Lambda.IsClosed_imp_subst_eq natPair'_closed,
    Lambda.IsClosed_imp_subst_eq mu_closed]

theorem muParam_app_reduces {H : Lambda} (hH : Lambda.IsClosed H) (n : ℕ) :
    Lambda.reduces (Lambda.app (muParam H) (Lambda.church n))
      (Lambda.app Lambda.mu (muFiber H n)) := by
  have h := @Lambda.beta_reduces
    (Lambda.app Lambda.mu
      (Lambda.lam (Lambda.app H (Lambda.app (Lambda.app Lambda.natPair' (Lambda.var 1))
        (Lambda.var 0))))) (Lambda.church n)
  simpa [muParam, muFiber, Lambda.subst, Lambda.IsClosed_imp_subst_eq hH,
    Lambda.IsClosed_imp_subst_eq natPair'_closed, Lambda.IsClosed_imp_subst_eq mu_closed,
    Lambda.lift_closed (Lambda.church_closed n)] using h

theorem muFiber_works {H : Lambda} {h : ℕ → ℕ} (hH : Realizes H h) (n y : ℕ) :
    Lambda.reduces (Lambda.app (muFiber H n) (Lambda.church y))
      (Lambda.church (h (Nat.pair n y))) := by
  have h1 : Lambda.reduces (Lambda.app (muFiber H n) (Lambda.church y))
      (Lambda.app H (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
        (Lambda.church y))) := by
    have hb := @Lambda.beta_reduces
      (Lambda.app H (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
        (Lambda.var 0))) (Lambda.church y)
    simpa [muFiber, Lambda.subst, Lambda.IsClosed_imp_subst_eq hH.1,
      Lambda.IsClosed_imp_subst_eq natPair'_closed,
      Lambda.IsClosed_imp_subst_eq (Lambda.church_closed n)] using hb
  exact Lambda.reduces_trans h1
    (Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.natPair'_works n y))
      (hH.2 (Nat.pair n y)))

/-- **Parameterised minimisation realizes the least-witness function.**  If `H`
realizes `h` and `m n` is the least `y` with `h (pair n y) = 0`, then `muParam H`
realizes `m`. -/
theorem Realizes.muParam {H : Lambda} {h : ℕ → ℕ} (hH : Realizes H h) (m : ℕ → ℕ)
    (hm0 : ∀ n, h (Nat.pair n (m n)) = 0)
    (hmlt : ∀ n y, y < m n → h (Nat.pair n y) ≠ 0) :
    Realizes (Lambda.muParam H) m := by
  refine ⟨muParam_closed hH.1, fun n => ?_⟩
  refine Lambda.reduces_trans (muParam_app_reduces hH.1 n) ?_
  exact muCorrectness (fun y => h (Nat.pair n y)) (muFiber H n) (muFiber_closed hH.1 n)
    (muFiber_works hH n) (m n) (fun y hy => hmlt n y hy) (hm0 n)

end Lambda

------------------------------------------------------------------------
-- Kleene normal form and the compiler for computable functions
------------------------------------------------------------------------

open Nat.Partrec (Code)

/-- The step-indexed evaluation predicate of a code, arithmetised: `0` marks a
successful evaluation of `c` on `(unpair p).1` within `(unpair p).2` steps. -/
def Lambda.kleeneTest (c : Nat.Partrec.Code) (p : ℕ) : ℕ :=
  ((Nat.Partrec.Code.evaln (Nat.unpair p).2 c (Nat.unpair p).1).map fun _ => 0).getD 1

/-- The step-indexed value extractor of a code, arithmetised. -/
def Lambda.kleeneValue (c : Nat.Partrec.Code) (p : ℕ) : ℕ :=
  (Nat.Partrec.Code.evaln (Nat.unpair p).2 c (Nat.unpair p).1).getD 0

theorem Lambda.kleeneEvaln_primrec (c : Nat.Partrec.Code) :
    Primrec fun p : ℕ => Nat.Partrec.Code.evaln (Nat.unpair p).2 c (Nat.unpair p).1 := by
  have h := Nat.Partrec.Code.primrec_evaln
  exact h.comp (((Primrec.snd.comp Primrec.unpair).pair (Primrec.const c)).pair
    (Primrec.fst.comp Primrec.unpair))

theorem Lambda.kleeneTest_primrec (c : Nat.Partrec.Code) : Nat.Primrec (Lambda.kleeneTest c) := by
  refine Primrec.nat_iff.1 ?_
  have hmap : Primrec fun p : ℕ =>
      (Nat.Partrec.Code.evaln (Nat.unpair p).2 c (Nat.unpair p).1).map fun _ => (0 : ℕ) :=
    (Lambda.kleeneEvaln_primrec c).option_map (Primrec.const 0).to₂
  exact Primrec.option_getD.comp hmap (Primrec.const 1)

theorem Lambda.kleeneValue_primrec (c : Nat.Partrec.Code) : Nat.Primrec (Lambda.kleeneValue c) := by
  refine Primrec.nat_iff.1 ?_
  exact Primrec.option_getD.comp (Lambda.kleeneEvaln_primrec c) (Primrec.const 0)

theorem Lambda.kleeneTest_eq_zero_iff (c : Nat.Partrec.Code) (p : ℕ) :
    Lambda.kleeneTest c p = 0 ↔
      (Nat.Partrec.Code.evaln (Nat.unpair p).2 c (Nat.unpair p).1).isSome := by
  unfold Lambda.kleeneTest
  cases Nat.Partrec.Code.evaln (Nat.unpair p).2 c (Nat.unpair p).1 <;> simp

/-- Kleene's normal form for a total computable function: the step-indexed search
always succeeds. -/
theorem Lambda.kleene_exists_witness {f : ℕ → ℕ} {c : Nat.Partrec.Code}
    (hc : c.eval = fun n => Part.some (f n)) (n : ℕ) :
    ∃ k, Lambda.kleeneTest c (Nat.pair n k) = 0 := by
  have hmem : f n ∈ Nat.rfindOpt fun k => Nat.Partrec.Code.evaln k c n := by
    rw [← Nat.Partrec.Code.eval_eq_rfindOpt, hc]
    exact Part.mem_some _
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hmem
  refine ⟨k, ?_⟩
  rw [Lambda.kleeneTest_eq_zero_iff]
  simp only [Nat.unpair_pair]
  rw [Option.mem_def] at hk
  simp [hk]

/-- On a successful step-indexed search the extracted value is the value of `f`. -/
theorem Lambda.kleene_value_eq {f : ℕ → ℕ} {c : Nat.Partrec.Code}
    (hc : c.eval = fun n => Part.some (f n)) (n k : ℕ)
    (h : Lambda.kleeneTest c (Nat.pair n k) = 0) :
    Lambda.kleeneValue c (Nat.pair n k) = f n := by
  rw [Lambda.kleeneTest_eq_zero_iff] at h
  simp only [Nat.unpair_pair] at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  have hsound : v ∈ c.eval n := Nat.Partrec.Code.evaln_sound hv
  rw [hc] at hsound
  have hvf : v = f n := Part.mem_some_iff.1 hsound
  simp [Lambda.kleeneValue, hv, hvf]

/-- **Every total computable function has a closed lambda realizer.** -/
theorem Lambda.exists_realizer_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ F : Lambda, Lambda.Realizes F f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf)
  have hex : ∀ n, ∃ k, Lambda.kleeneTest c (Nat.pair n k) = 0 :=
    Lambda.kleene_exists_witness hc
  obtain ⟨H, hH⟩ := Lambda.exists_realizer_of_primrec (Lambda.kleeneTest_primrec c)
  obtain ⟨G, hG⟩ := Lambda.exists_realizer_of_primrec (Lambda.kleeneValue_primrec c)
  set m : ℕ → ℕ := fun n => Nat.find (hex n) with hm
  have hm0 : ∀ n, Lambda.kleeneTest c (Nat.pair n (m n)) = 0 := fun n => Nat.find_spec (hex n)
  have hmlt : ∀ n y, y < m n → Lambda.kleeneTest c (Nat.pair n y) ≠ 0 :=
    fun n y hy => Nat.find_min (hex n) hy
  refine ⟨Lambda.mkApp1 G (Lambda.mkApp2 Lambda.natPair' Lambda.I (Lambda.muParam H)), ?_⟩
  have hR := Lambda.Realizes.comp1 hG
    (Lambda.Realizes.natPair Lambda.Realizes.identity (Lambda.Realizes.muParam hH m hm0 hmlt))
  exact hR.of_eq fun n => Lambda.kleene_value_eq hc n (m n) (hm0 n)

/-- **Total computable functions are lambda-computable.** -/
theorem lambdaComputable_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    LambdaComputable (fun n => Part.some (f n)) := by
  obtain ⟨F, hF⟩ := Lambda.exists_realizer_of_computable hf
  exact Lambda.lambdaComputable_of_realizes hF

/-- **Church–Turing for the lambda calculus, total case:** a total function is
computable exactly when it is lambda-computable. -/
theorem lambdaComputable_iff_computable {f : ℕ → ℕ} :
    LambdaComputable (fun n => Part.some (f n)) ↔ Computable f := by
  constructor
  · intro h
    exact LambdaComputable_imp_Partrec_unconditional h
  · exact lambdaComputable_of_computable

end
