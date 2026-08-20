/-
Church–Turing for the lambda calculus, for *partial* functions.

`Start/PartrecLambda.lean` compiles every total computable function into a
lambda term.  With the divergence half of minimisation available
(`Start/Divergence.lean`) the same construction works for arbitrary partial
recursive functions, provided the value is computed *strictly*: the search
result is placed in head position, so that when the search diverges the whole
term has no weak head normal form and hence no normal form either.

The capstone is `lambdaComputable_iff_partrec`.
-/

import Start.PartrecLambda
import Start.Divergence

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Forcing a Church numeral
------------------------------------------------------------------------

theorem reduces_I (x : Lambda) : Lambda.reduces (Lambda.app Lambda.I x) x := by
  have h := @Lambda.beta_reduces (Lambda.var 0) x
  simpa [Lambda.I, Lambda.subst] using h

theorem reduces_iterate_I (x : Lambda) : ∀ n : ℕ,
    Lambda.reduces (Lambda.iterate Lambda.I x n) x := by
  intro n
  induction n with
  | zero => simpa [Lambda.iterate_zero] using Lambda.reduces.refl x
  | succ n ih =>
      rw [Lambda.iterate_succ]
      exact Lambda.reduces_trans (Lambda.reduces_app_right ih) (reduces_I x)

/-- Applying a Church numeral to the identity forces the numeral and returns the
second argument. -/
theorem church_force (k : ℕ) (x : Lambda) :
    Lambda.reduces (Lambda.app (Lambda.app (Lambda.church k) Lambda.I) x) x :=
  Lambda.reduces_trans (Lambda.church_reduces_iterate k Lambda.I x) (reduces_iterate_I x k)

------------------------------------------------------------------------
-- Parameterised minimisation, pointwise
------------------------------------------------------------------------

/-- If the parameterised search has a least witness at `n`, it reduces to it. -/
theorem muParam_reduces_church {H : Lambda} {h : ℕ → ℕ} (hH : Realizes H h) (n k : ℕ)
    (hlt : ∀ y, y < k → h (Nat.pair n y) ≠ 0) (hk : h (Nat.pair n k) = 0) :
    Lambda.reduces (Lambda.app (muParam H) (Lambda.church n)) (Lambda.church k) :=
  Lambda.reduces_trans (muParam_app_reduces hH.1 n)
    (muCorrectness (fun y => h (Nat.pair n y)) (muFiber H n) (muFiber_closed hH.1 n)
      (muFiber_works hH n) k hlt hk)

/-- If the parameterised search has no witness at `n`, the weak head strategy diverges
on it. -/
theorem muParam_not_hasWhnfEval {H : Lambda} {h : ℕ → ℕ} (hH : Realizes H h) (n : ℕ)
    (hno : ∀ y, h (Nat.pair n y) ≠ 0) :
    ¬ HasWhnfEval (Lambda.app (muParam H) (Lambda.church n)) := by
  intro hev
  obtain ⟨u, hu1, hu2⟩ := exists_whnf_of_hasWhnfEval hev
  obtain ⟨w, hw1, hw2⟩ := Lambda.confluence_theorem hu1 (muParam_app_reduces hH.1 n)
  exact mu_not_reduces_whnf (muFiber H n) (muFiber_closed hH.1 n) (fun y => h (Nat.pair n y))
    (muFiber_works hH n) hno (isWhnf_of_reduces hu2 hw1) hw2

------------------------------------------------------------------------
-- The strict realizer of a partial function
------------------------------------------------------------------------

/-- The lambda term computing a partial function from a realizer `H` of its
step-indexed test and a realizer `G` of its step-indexed value: search for the least
witness, *force* it, and then read off the value.  Forcing is what makes the term
diverge when the search does. -/
def partialTerm (H G : Lambda) : Lambda :=
  Lambda.lam (Lambda.app
    (Lambda.app (Lambda.app (muParam H) (Lambda.var 0)) Lambda.I)
    (Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.var 0))
      (Lambda.app (muParam H) (Lambda.var 0)))))

theorem partialTerm_app_reduces {H G : Lambda} (hH : Lambda.IsClosed H)
    (hG : Lambda.IsClosed G) (n : ℕ) :
    Lambda.reduces (Lambda.app (partialTerm H G) (Lambda.church n))
      (Lambda.app
        (Lambda.app (Lambda.app (muParam H) (Lambda.church n)) Lambda.I)
        (Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
          (Lambda.app (muParam H) (Lambda.church n))))) := by
  have h := @Lambda.beta_reduces
    (Lambda.app
      (Lambda.app (Lambda.app (muParam H) (Lambda.var 0)) Lambda.I)
      (Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.var 0))
        (Lambda.app (muParam H) (Lambda.var 0))))) (Lambda.church n)
  simpa [partialTerm, Lambda.subst, Lambda.IsClosed_imp_subst_eq hG,
    Lambda.IsClosed_imp_subst_eq (muParam_closed hH),
    Lambda.IsClosed_imp_subst_eq natPair'_closed,
    Lambda.IsClosed_imp_subst_eq I_closed] using h

/-- On a converging search the strict realizer produces the value. -/
theorem partialTerm_reduces_church {H G : Lambda} {h v : ℕ → ℕ}
    (hH : Realizes H h) (hG : Realizes G v) (n k : ℕ)
    (hlt : ∀ y, y < k → h (Nat.pair n y) ≠ 0) (hk : h (Nat.pair n k) = 0) :
    Lambda.reduces (Lambda.app (partialTerm H G) (Lambda.church n))
      (Lambda.church (v (Nat.pair n k))) := by
  have hsearch : Lambda.reduces (Lambda.app (muParam H) (Lambda.church n)) (Lambda.church k) :=
    muParam_reduces_church hH n k hlt hk
  refine Lambda.reduces_trans (partialTerm_app_reduces hH.1 hG.1 n) ?_
  -- reduce the value part
  have hvalue : Lambda.reduces
      (Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
        (Lambda.app (muParam H) (Lambda.church n))))
      (Lambda.church (v (Nat.pair n k))) := by
    refine Lambda.reduces_trans
      (Lambda.reduces_app_right (Lambda.reduces_app_right hsearch)) ?_
    exact Lambda.reduces_trans (Lambda.reduces_app_right (Lambda.natPair'_works n k))
      (hG.2 (Nat.pair n k))
  -- force the search result
  refine Lambda.reduces_trans (Lambda.reduces_app_left
    (Lambda.reduces_app_left hsearch)) ?_
  exact Lambda.reduces_trans (church_force k _) hvalue

/-- On a diverging search the strict realizer has no weak head normal form. -/
theorem partialTerm_not_hasWhnfEval {H G : Lambda} {h : ℕ → ℕ} (hH : Realizes H h)
    (hG : Lambda.IsClosed G) (n : ℕ) (hno : ∀ y, h (Nat.pair n y) ≠ 0) :
    ¬ HasWhnfEval (Lambda.app (partialTerm H G) (Lambda.church n)) := by
  intro hev
  obtain ⟨u, hu1, hu2⟩ := exists_whnf_of_hasWhnfEval hev
  obtain ⟨w, hw1, hw2⟩ := Lambda.confluence_theorem hu1 (partialTerm_app_reduces hH.1 hG n)
  have hwhnf : IsWhnf w := isWhnf_of_reduces hu2 hw1
  have h1 := hasWhnfEval_of_reduces_whnf hw2 hwhnf
  exact muParam_not_hasWhnfEval hH n hno (hasWhnfEval_of_app (hasWhnfEval_of_app h1))

/-- On a diverging search the strict realizer reduces to no Church numeral. -/
theorem partialTerm_not_reduces_church {H G : Lambda} {h : ℕ → ℕ} (hH : Realizes H h)
    (hG : Lambda.IsClosed G) (n : ℕ) (hno : ∀ y, h (Nat.pair n y) ≠ 0) (m : ℕ) :
    ¬ Lambda.reduces (Lambda.app (partialTerm H G) (Lambda.church n)) (Lambda.church m) := by
  intro hred
  exact partialTerm_not_hasWhnfEval hH hG n hno
    (hasWhnfEval_of_reduces_whnf hred (isWhnf_church m))

end Lambda

------------------------------------------------------------------------
-- Kleene normal form for partial functions
------------------------------------------------------------------------

open Nat.Partrec (Code)

theorem Lambda.kleeneTest_pair_eq_zero_iff (c : Nat.Partrec.Code) (n k : ℕ) :
    Lambda.kleeneTest c (Nat.pair n k) = 0 ↔ (Nat.Partrec.Code.evaln k c n).isSome := by
  rw [Lambda.kleeneTest_eq_zero_iff]
  simp

/-- A converging computation is found by the step-indexed search. -/
theorem Lambda.exists_kleene_witness {f : ℕ →. ℕ} {c : Nat.Partrec.Code} (hc : c.eval = f)
    {n m : ℕ} (hm : m ∈ f n) : ∃ k, Lambda.kleeneTest c (Nat.pair n k) = 0 := by
  have hmem : m ∈ Nat.rfindOpt fun k => Nat.Partrec.Code.evaln k c n := by
    rw [← Nat.Partrec.Code.eval_eq_rfindOpt, hc]
    exact hm
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec hmem
  refine ⟨k, ?_⟩
  rw [Lambda.kleeneTest_pair_eq_zero_iff]
  rw [Option.mem_def] at hk
  simp [hk]

/-- The value extracted from a successful step-indexed search is the value of the
function. -/
theorem Lambda.kleeneValue_mem {f : ℕ →. ℕ} {c : Nat.Partrec.Code} (hc : c.eval = f) {n k : ℕ}
    (h : Lambda.kleeneTest c (Nat.pair n k) = 0) : Lambda.kleeneValue c (Nat.pair n k) ∈ f n := by
  rw [Lambda.kleeneTest_pair_eq_zero_iff] at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  have hsound : v ∈ c.eval n := Nat.Partrec.Code.evaln_sound hv
  rw [hc] at hsound
  have : Lambda.kleeneValue c (Nat.pair n k) = v := by
    simp [Lambda.kleeneValue, hv]
  rw [this]
  exact hsound

/-- A diverging computation is never found by the step-indexed search. -/
theorem Lambda.kleene_no_witness {f : ℕ →. ℕ} {c : Nat.Partrec.Code} (hc : c.eval = f) {n : ℕ}
    (hn : ∀ m, m ∉ f n) (k : ℕ) : Lambda.kleeneTest c (Nat.pair n k) ≠ 0 := by
  intro h
  exact hn _ (Lambda.kleeneValue_mem hc h)

------------------------------------------------------------------------
-- The capstone
------------------------------------------------------------------------

/-- **Every partial recursive function is lambda-computable.** -/
theorem lambdaComputable_of_partrec {f : ℕ →. ℕ} (hf : Partrec f) : LambdaComputable f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf)
  obtain ⟨H, hH⟩ := Lambda.exists_realizer_of_primrec (Lambda.kleeneTest_primrec c)
  obtain ⟨G, hG⟩ := Lambda.exists_realizer_of_primrec (Lambda.kleeneValue_primrec c)
  refine ⟨Lambda.partialTerm H G, fun n m => ⟨fun hfn => ?_, fun hred => ?_⟩⟩
  · -- convergence
    have hm : m ∈ f n := by rw [hfn]; exact Part.mem_some m
    obtain ⟨k, hk⟩ := Lambda.exists_kleene_witness hc hm
    have hex : ∃ k, Lambda.kleeneTest c (Nat.pair n k) = 0 := ⟨k, hk⟩
    have hk0 : Lambda.kleeneTest c (Nat.pair n (Nat.find hex)) = 0 := Nat.find_spec hex
    have hlt : ∀ y, y < Nat.find hex → Lambda.kleeneTest c (Nat.pair n y) ≠ 0 :=
      fun y hy => Nat.find_min hex hy
    have hval : Lambda.kleeneValue c (Nat.pair n (Nat.find hex)) ∈ f n :=
      Lambda.kleeneValue_mem hc hk0
    have hveq : Lambda.kleeneValue c (Nat.pair n (Nat.find hex)) = m := by
      have : m ∈ f n := hm
      exact Part.mem_unique hval this
    have := Lambda.partialTerm_reduces_church hH hG n (Nat.find hex) hlt hk0
    rwa [hveq] at this
  · -- the reduction determines the value
    rcases Classical.em (∃ m', m' ∈ f n) with ⟨m', hm'⟩ | hnone
    · obtain ⟨k, hk⟩ := Lambda.exists_kleene_witness hc hm'
      have hex : ∃ k, Lambda.kleeneTest c (Nat.pair n k) = 0 := ⟨k, hk⟩
      have hk0 : Lambda.kleeneTest c (Nat.pair n (Nat.find hex)) = 0 := Nat.find_spec hex
      have hlt : ∀ y, y < Nat.find hex → Lambda.kleeneTest c (Nat.pair n y) ≠ 0 :=
        fun y hy => Nat.find_min hex hy
      have hred' := Lambda.partialTerm_reduces_church hH hG n (Nat.find hex) hlt hk0
      have heq : Lambda.kleeneValue c (Nat.pair n (Nat.find hex)) = m :=
        Lambda.unique_church_reduct hred' hred
      have hval : Lambda.kleeneValue c (Nat.pair n (Nat.find hex)) ∈ f n :=
        Lambda.kleeneValue_mem hc hk0
      rw [heq] at hval
      exact Part.eq_some_iff.2 hval
    · exact absurd hred (Lambda.partialTerm_not_reduces_church hH hG.1 n
        (Lambda.kleene_no_witness hc (fun m' hm' => hnone ⟨m', hm'⟩)) m)

/-- **Church–Turing for the lambda calculus.**  A partial function on the naturals is
lambda-definable exactly when it is partial recursive. -/
theorem lambdaComputable_iff_partrec {f : ℕ →. ℕ} : LambdaComputable f ↔ Partrec f :=
  ⟨LambdaComputable_imp_Partrec_unconditional, lambdaComputable_of_partrec⟩

end
