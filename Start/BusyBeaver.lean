/-
# A busy beaver for the lambda calculus

`Start/LeftmostRun.lean` gives every normalizing term a *halting time* `Lambda.haltTime t`: the
number of leftmost-outermost steps it takes to reach its normal form.  The busy beaver function
collects the largest halting time available at a given description length:

* `Lambda.bbTime n` — the maximum of `haltTime t` over the (finitely many) normalizing terms with
  code at most `n`;
* `Lambda.bbSize n` — the same maximum over the normalizing terms of syntactic *size* at most `n`.

Both are well defined because only finitely many terms have a bounded code (resp. size).

The point of the busy beaver is that it converts the halting problem into a bounded computation:
`Lambda.hasNormalForm_iff_haltsBy_code` says that once you know a bound on the halting time of a
term, running the term for that many steps decides whether it normalizes.  Consequently no
computable function can bound the halting times (`Lambda.not_computable_of_halting_bound`), so:

* `Lambda.not_computable_bbTime`, `Lambda.not_computable_bbSize` — the busy beaver functions are
  not computable;
* `Lambda.no_computable_bound_bbTime`, `Lambda.bbTime_exceeds_computable` — no computable function
  bounds `bbTime` everywhere, and every computable function is exceeded by `bbTime` at arbitrarily
  large arguments.

In the other direction the busy beaver frontier admits *certificates*: exhibiting a single term of
code at most `n` that halts in exactly `k` steps proves the lower bound `k ≤ bbTime n`
(`Lambda.bbTime_ge_of_cert`).  A certificate is a finite, checkable object — that is what makes
lower bounds on a busy beaver frontier accessible even though the function itself is not
computable.
-/

import Start.LeftmostRun

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Finitely many terms have a bounded code
------------------------------------------------------------------------

theorem finite_setOf_encode_le (n : ℕ) : {t : Lambda | Lambda.encode t ≤ n}.Finite := by
  have hsub : {t : Lambda | Lambda.encode t ≤ n} ⊆ Lambda.encode ⁻¹' (Set.Iic n) := fun _ ht => ht
  exact (Set.Finite.preimage (Lambda.encode_injective.injOn) (Set.finite_Iic n)).subset hsub

------------------------------------------------------------------------
-- The busy beaver functions
------------------------------------------------------------------------

open Classical in
/-- **The busy beaver of the lambda calculus**, indexed by code: the largest number of
leftmost-outermost steps that a normalizing term with code at most `n` needs to reach its normal
form. -/
def bbTime (n : ℕ) : ℕ :=
  (finite_setOf_encode_le n).toFinset.sup (fun t => if HasNormalForm t then haltTime t else 0)

theorem haltTime_le_bbTime {t : Lambda} {n : ℕ} (hn : Lambda.encode t ≤ n)
    (ht : HasNormalForm t) : haltTime t ≤ bbTime n := by
  classical
  have hmem : t ∈ (finite_setOf_encode_le n).toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact hn
  have hle := Finset.le_sup (f := fun t => if HasNormalForm t then haltTime t else 0) hmem
  simp only [if_pos ht] at hle
  exact hle

theorem bbTime_mono : Monotone bbTime := by
  intro m n hmn
  refine Finset.sup_mono ?_
  intro t ht
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ht ⊢
  omega

/-- The busy beaver indexed by syntactic size. -/
def bbSize (n : ℕ) : ℕ := bbTime (encBound n)

theorem haltTime_le_bbSize {t : Lambda} {n : ℕ} (hn : size t ≤ n) (ht : HasNormalForm t) :
    haltTime t ≤ bbSize n :=
  haltTime_le_bbTime (encode_le_encBound t n hn) ht

------------------------------------------------------------------------
-- A halting-time bound decides normalization
------------------------------------------------------------------------

/-- **Knowing a bound on the halting time decides the halting problem.**  If `m` bounds the
halting time of `t` (whenever `t` normalizes at all), then running `t` for `m` leftmost steps
answers whether `t` normalizes. -/
theorem hasNormalForm_iff_haltsBy_code {t : Lambda} {m : ℕ}
    (h : HasNormalForm t → haltTime t ≤ m) :
    HasNormalForm t ↔ haltsBy_code (Lambda.encode t) m = Bool.true := by
  rw [haltsBy_code_correct]
  constructor
  · intro hnf
    rw [nstep_iterate_stable (is_normal_nstep_haltTime hnf) (h hnf)]
    exact is_normal_nstep_haltTime hnf
  · intro hk
    exact (hasNormalForm_iff_exists_normal_iterate t).2 ⟨m, hk⟩

------------------------------------------------------------------------
-- No computable function bounds the halting time
------------------------------------------------------------------------

/-- **The halting times are not computably bounded.**  There is no computable `f` such that
`f (encode t)` bounds the number of leftmost steps that a normalizing term `t` needs. -/
theorem not_computable_of_halting_bound {f : ℕ → ℕ} (hf : Computable f)
    (hb : ∀ t : Lambda, HasNormalForm t → haltTime t ≤ f (Lambda.encode t)) : False := by
  have hcode : Computable (fun k : ℕ => strictHaltCode k) := strictHaltCode_primrec.to_comp
  have hdec : Computable (fun k : ℕ =>
      haltsBy_code (strictHaltCode k) (f (strictHaltCode k))) :=
    (Primrec₂.to_comp haltsBy_code_primrec).comp hcode (hf.comp hcode)
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr
    ⟨fun c : Nat.Partrec.Code =>
      haltsBy_code (strictHaltCode (Encodable.encode c)) (f (strictHaltCode (Encodable.encode c))),
      hdec.comp (Primrec.encode.to_comp.comp Computable.id), ?_⟩)
  funext c
  set k : ℕ := Encodable.encode c with hkdef
  have hT : strictHaltCode k = Lambda.encode (Lambda.app strictHaltTerm (Lambda.church k)) :=
    strictHaltCode_eq k
  have hiff : (univHalt k).Dom ↔
      haltsBy_code (strictHaltCode k) (f (strictHaltCode k)) = Bool.true := by
    rw [univHalt_dom_iff_hasNormalForm, hT]
    exact hasNormalForm_iff_haltsBy_code
      (fun hnf => hb (Lambda.app strictHaltTerm (Lambda.church k)) hnf)
  have hk : univHalt k = Nat.Partrec.Code.eval c 0 := by
    simp only [univHalt, hkdef, Denumerable.ofNat_encode]
  rw [eq_iff_iff, ← hk]
  exact hiff

/-- **No computable function bounds the busy beaver.** -/
theorem no_computable_bound_bbTime {f : ℕ → ℕ} (hf : Computable f) :
    ¬ (∀ n, bbTime n ≤ f n) := by
  intro hb
  refine not_computable_of_halting_bound hf (fun t ht => ?_)
  exact le_trans (haltTime_le_bbTime (le_refl _) ht) (hb (Lambda.encode t))

/-- **The busy beaver is not computable.** -/
theorem not_computable_bbTime : ¬ Computable bbTime :=
  fun h => no_computable_bound_bbTime h (fun _ => le_refl _)

/-- The size-indexed busy beaver is not computable either. -/
theorem not_computable_bbSize : ¬ Computable bbSize := by
  intro h
  refine not_computable_of_halting_bound (f := fun c => bbSize (size_code c))
    (h.comp size_code_primrec.to_comp) (fun t ht => ?_)
  simp only [size_code_correct]
  exact haltTime_le_bbSize (le_refl _) ht

/-- **The busy beaver outgrows every computable function**: for every computable `f` and every
`N` there is an `n ≥ N` with `f n < bbTime n`. -/
theorem bbTime_exceeds_computable {f : ℕ → ℕ} (hf : Computable f) (N : ℕ) :
    ∃ n, N ≤ n ∧ f n < bbTime n := by
  classical
  set table : List ℕ := (List.range N).map bbTime with htable
  set g : ℕ → ℕ := fun n => cond (decide (n < N)) (table.getD n 0) (f n) with hg
  have hgc : Computable g := by
    have hcond : Computable (fun n : ℕ => decide (n < N)) := by
      have h : PrimrecPred (fun n : ℕ => n < N) :=
        Primrec.nat_lt.comp Primrec.id (Primrec.const N)
      obtain ⟨_inst, h⟩ := h
      exact (h.of_eq (fun n => by simp)).to_comp
    exact Computable.cond hcond
      ((Primrec.list_getD 0).comp (Primrec.const table) Primrec.id).to_comp hf
  have hnb := no_computable_bound_bbTime hgc
  push Not at hnb
  obtain ⟨n, hn⟩ := hnb
  have hnN : N ≤ n := by
    by_contra hcon
    push Not at hcon
    have : g n = bbTime n := by
      simp only [hg, hcon, decide_true, cond_true, htable]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hcon]
      rfl
    omega
  refine ⟨n, hnN, ?_⟩
  have : g n = f n := by simp [hg, Nat.not_lt.mpr hnN, decide_eq_false]
  omega

------------------------------------------------------------------------
-- Certificates for lower bounds
------------------------------------------------------------------------

/-- A *halting certificate*: the term `t` reaches a normal form after exactly `k` leftmost steps
and not before.  This is a finite, checkable object. -/
structure HaltCert (t : Lambda) (k : ℕ) : Prop where
  halts : Lambda.is_normal (nstep^[k] t)
  minimal : ∀ j, j < k → ¬ Lambda.is_normal (nstep^[j] t)

theorem HaltCert.haltTime_eq {t : Lambda} {k : ℕ} (h : HaltCert t k) : haltTime t = k :=
  le_antisymm (haltTime_le h.halts)
    (le_of_not_gt fun hlt => h.minimal _ hlt
      (is_normal_nstep_haltTime ((hasNormalForm_iff_exists_normal_iterate t).2 ⟨k, h.halts⟩)))

theorem HaltCert.hasNormalForm {t : Lambda} {k : ℕ} (h : HaltCert t k) : HasNormalForm t :=
  (hasNormalForm_iff_exists_normal_iterate t).2 ⟨k, h.halts⟩

/-- **Certificates give lower bounds on the busy beaver frontier.** -/
theorem bbTime_ge_of_cert {t : Lambda} {k n : ℕ} (hcode : Lambda.encode t ≤ n)
    (h : HaltCert t k) : k ≤ bbTime n := by
  rw [← h.haltTime_eq]
  exact haltTime_le_bbTime hcode h.hasNormalForm

theorem bbSize_ge_of_cert {t : Lambda} {k n : ℕ} (hsize : size t ≤ n) (h : HaltCert t k) :
    k ≤ bbSize n := by
  rw [← h.haltTime_eq]
  exact haltTime_le_bbSize hsize h.hasNormalForm

/-- A first certificate: `I I` needs exactly one step. -/
theorem haltCert_I_I : HaltCert (Lambda.app Lambda.I Lambda.I) 1 := by
  constructor
  · have h : nstep^[1] (Lambda.app Lambda.I Lambda.I) = Lambda.I := by
      simp only [Function.iterate_one, nstep, Lambda.I]
      rfl
    rw [h]
    exact Lambda.lam_normal (Lambda.var_normal 0)
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [Function.iterate_zero_apply]
    intro hnormal
    exact hnormal (Lambda.subst Lambda.I 0 (Lambda.var 0)) (Lambda.step.beta _ _)

theorem one_le_bbSize_five : 1 ≤ bbSize 5 :=
  bbSize_ge_of_cert (by decide) haltCert_I_I

end Lambda

end
