/-
# The bridge between the halting problem and the uncomputability of `K`

Two uncomputability results were proved independently in this repository:

* `Lambda.not_computablePred_codeHasNormalForm` — whether a lambda term has a normal form is
  undecidable (a reduction from Turing's halting problem);
* `Lambda.not_computable_kolm` — Kolmogorov complexity is not computable (Berry's paradox, run
  through Kleene's second recursion theorem).

This file connects them.  The mathematical content is the reduction

  `Lambda.computable_kolm_of_decidable_halting :
      ComputablePred CodeHasNormalForm → Computable Lambda.kolm`,

i.e. **a halting oracle computes `K`**.  The construction is the classical one:

* with a halting decider, the leftmost-outermost run of `Start/LeftmostRun.lean` can be turned
  into a *total* computable normal-form function (`Lambda.progTest`: "is the code `c` a closed
  program for `s`?");
* only finitely many codes need to be inspected, because a term of size at most `n` has code at
  most `Lambda.encBound n` (`Start/CodeArith.lean`), and the Church numeral `church s` is always
  a program for `s` of size `3 * s + 3`;
* so `K s` is the minimum of a computable function over a computably bounded range
  (`Lambda.minProg`), hence computable.

Contraposing the bridge derives the undecidability of normalization from Berry's paradox alone
(`Lambda.not_computablePred_codeHasNormalForm_of_berry`), a proof completely different from the
reduction in `Start/NormalizationUndecidable.lean`; and `Lambda.kolm_uncomputable_iff` records
the resulting equivalence of the two "negative" statements.
-/

import Start.LeftmostRun

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Decoding is inverse to encoding
------------------------------------------------------------------------

/-- Unfolding lemma for `Lambda.decode`. -/
theorem decode_eq (n : ℕ) :
    Lambda.decode n =
      (match _h : n.unpair with
       | (0, m) => some (Lambda.var m)
       | (1, m) =>
         match _hm : m.unpair with
         | (c₁, c₂) =>
           match Lambda.decode c₁, Lambda.decode c₂ with
           | some t₁, some t₂ => some (Lambda.app t₁ t₂)
           | _, _ => none
       | (2, m) =>
         match Lambda.decode m with
         | some t => some (Lambda.lam t)
         | _ => none
       | _ => none) := by
  conv_lhs => rw [Lambda.decode, Nat.strongRecOn_eq]
  congr! 2

/-- A code that decodes at all is the code of the term it decodes to. -/
theorem encode_of_decode : ∀ (c : ℕ) (t : Lambda),
    Lambda.decode c = some t → Lambda.encode t = c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
      intro t ht
      rw [decode_eq] at ht
      split at ht
      · next m hu =>
          have : t = Lambda.var m := by simpa using ht.symm
          subst this
          rw [Lambda.encode, ← Nat.pair_unpair c, hu]
      · next m hu =>
          split at ht
          next c₁ c₂ hm =>
            have h1 : c₁ < c := Lambda.decode_lt_1 hu hm
            have h2 : c₂ < c := Lambda.decode_lt_2 hu hm
            rcases hd1 : Lambda.decode c₁ with _ | t₁ <;>
              rcases hd2 : Lambda.decode c₂ with _ | t₂ <;>
              rw [hd1, hd2] at ht <;> simp only [reduceCtorEq, Option.some.injEq] at ht
            subst ht
            have hm' : Nat.pair c₁ c₂ = m := by rw [← Nat.pair_unpair m, hm]
            have hu' : Nat.pair 1 m = c := by rw [← Nat.pair_unpair c, hu]
            rw [Lambda.encode, ih c₁ h1 t₁ hd1, ih c₂ h2 t₂ hd2, hm', hu']
      · next m hu =>
          have h1 : m < c := Lambda.decode_lt_3 hu
          rcases hd : Lambda.decode m with _ | u <;> rw [hd] at ht <;>
            simp only [reduceCtorEq, Option.some.injEq] at ht
          subst ht
          rw [Lambda.encode, ih m h1 u hd, ← Nat.pair_unpair c, hu]
      · simp at ht

/-- The normalization predicate on codes, in terms of `Lambda.encode`. -/
theorem codeHasNormalForm_iff (c : ℕ) :
    CodeHasNormalForm c ↔ ∃ t : Lambda, Lambda.encode t = c ∧ HasNormalForm t := by
  constructor
  · rintro ⟨t, hd, hnf⟩
    exact ⟨t, encode_of_decode c t hd, hnf⟩
  · rintro ⟨t, rfl, hnf⟩
    exact ⟨t, decode_encode t, hnf⟩

------------------------------------------------------------------------
-- A halting decider computes the program test
------------------------------------------------------------------------

section Bridge

variable (f : ℕ → Bool)

/-- Driven by a halting decider `f`, the leftmost run decides whether the code `p.1` is a closed
program for the number `p.2`.  When `f` says "no", the search stops immediately at `0`. -/
def progRun (p : ℕ × ℕ) : Part Bool :=
  (Nat.rfind fun k => Part.some (cond (f p.1) (haltsBy_code p.1 k) Bool.true)).map
    (fun k => cond (f p.1)
      (cond (isClosed_code p.1) (decide (nstep_code^[k] p.1 = Lambda.church_code p.2)) Bool.false)
      Bool.false)

set_option maxHeartbeats 1000000 in
-- The compositional `Computable`/`Primrec` bookkeeping below unfolds many `Primcodable`
-- instances, which exceeds the default heartbeat budget.
theorem progRun_partrec (hf : Computable f) : Partrec (progRun f) := by
  have hf1 : Computable (fun p : ℕ × ℕ => f p.1) := hf.comp Computable.fst
  have hstop : Computable₂ (fun (p : ℕ × ℕ) (k : ℕ) =>
      cond (f p.1) (haltsBy_code p.1 k) Bool.true) := by
    refine Computable.cond (hf1.comp Computable.fst) ?_ (Computable.const Bool.true)
    exact (Primrec₂.to_comp haltsBy_code_primrec).comp
      (Computable.fst.comp Computable.fst) Computable.snd
  have hval : Computable₂ (fun (p : ℕ × ℕ) (k : ℕ) =>
      cond (f p.1)
        (cond (isClosed_code p.1)
          (decide (nstep_code^[k] p.1 = Lambda.church_code p.2)) Bool.false)
        Bool.false) := by
    refine Computable.cond (hf1.comp Computable.fst) ?_ (Computable.const Bool.false)
    refine Computable.cond
      (isClosed_code_primrec.to_comp.comp (Computable.fst.comp Computable.fst)) ?_
      (Computable.const Bool.false)
    have h1 : Computable (fun q : (ℕ × ℕ) × ℕ => nstep_code^[q.2] q.1.1) :=
      (Primrec₂.to_comp nstep_code_iterate_primrec).comp
        (Computable.fst.comp Computable.fst) Computable.snd
    have h2 : Computable (fun q : (ℕ × ℕ) × ℕ => Lambda.church_code q.1.2) :=
      Lambda.church_code_primrec.to_comp.comp (Computable.snd.comp Computable.fst)
    have h : PrimrecPred (fun q : ℕ × ℕ => q.1 = q.2) := Primrec.eq
    obtain ⟨_inst, h⟩ := h
    exact ((h.to_comp).comp (Computable.pair h1 h2)).of_eq (fun _ => by congr)
  have hsearch : Partrec (fun p : ℕ × ℕ =>
      Nat.rfind fun k => Part.some (cond (f p.1) (haltsBy_code p.1 k) Bool.true)) :=
    Partrec.rfind hstop
  exact Partrec.map hsearch hval

theorem progRun_of_false {c s : ℕ} (h : f c = Bool.false) :
    progRun f (c, s) = Part.some Bool.false := by
  have hrf : (Nat.rfind fun _ : ℕ => (Part.some Bool.true : Part Bool)) = Part.some 0 :=
    Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨Part.mem_some _, fun {m} hm => absurd hm (by omega)⟩)
  simp only [progRun, h, cond_false, hrf, Part.map_some]

theorem progRun_of_true {t : Lambda} {s : ℕ} (h : f (Lambda.encode t) = Bool.true)
    (hnf : HasNormalForm t) :
    progRun f (Lambda.encode t, s) =
      Part.some (cond (isClosed_code (Lambda.encode t))
        (decide (Lambda.encode (nf t) = Lambda.church_code s)) Bool.false) := by
  have hmem : haltTime t ∈
      Nat.rfind (fun k => Part.some (haltsBy_code (Lambda.encode t) k)) := by
    refine Nat.mem_rfind.2 ⟨?_, ?_⟩
    · simp only [Part.mem_some_iff]
      exact ((haltsBy_code_correct t (haltTime t)).2 (is_normal_nstep_haltTime hnf)).symm
    · intro m hm
      simp only [Part.mem_some_iff]
      have hns : ¬ Lambda.is_normal (nstep^[m] t) := by
        intro hcon
        exact absurd (haltTime_le hcon) (by omega)
      rcases hb : haltsBy_code (Lambda.encode t) m with _ | _
      · rfl
      · exact absurd ((haltsBy_code_correct t m).1 hb) hns
  have hrf : Nat.rfind (fun k => Part.some (haltsBy_code (Lambda.encode t) k)) =
      Part.some (haltTime t) :=
    Part.eq_some_iff.2 hmem
  have hiter : nstep_code^[haltTime t] (Lambda.encode t) = Lambda.encode (nf t) := by
    rw [nstep_code_iterate]; rfl
  simp only [progRun, h, cond_true, hrf, Part.map_some, hiter]

open Classical in
/-- The total program test extracted from `Lambda.progRun`. -/
def progTest (p : ℕ × ℕ) : Bool :=
  if h : (progRun f p).Dom then (progRun f p).get h else Bool.false

variable {f}

theorem progRun_dom (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) (p : ℕ × ℕ) :
    ∃ b, progRun f p = Part.some b := by
  obtain ⟨c, s⟩ := p
  rcases hb : f c with _ | _
  · exact ⟨Bool.false, progRun_of_false f hb⟩
  · obtain ⟨t, hte, hnf⟩ := (codeHasNormalForm_iff c).1 ((hfe c).2 hb)
    subst hte
    exact ⟨_, progRun_of_true f hb hnf⟩

theorem progRun_eq_progTest (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) (p : ℕ × ℕ) :
    progRun f p = Part.some (progTest f p) := by
  classical
  obtain ⟨b, hb⟩ := progRun_dom hfe p
  have hdom : (progRun f p).Dom := by rw [hb]; trivial
  rw [hb, progTest, dif_pos hdom]
  congr 1
  exact (Part.get_eq_iff_eq_some.2 hb).symm

theorem computable_progTest (hf : Computable f)
    (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) : Computable (progTest f) :=
  Partrec.of_eq (progRun_partrec f hf) (progRun_eq_progTest hfe)

/-- **Correctness of the program test.** -/
theorem progTest_encode (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) (t : Lambda) (s : ℕ) :
    progTest f (Lambda.encode t, s) = Bool.true ↔ IsProgramFor t s := by
  classical
  rcases hb : f (Lambda.encode t) with _ | _
  · have hnf : ¬ HasNormalForm t := by
      intro hcon
      have hc : CodeHasNormalForm (Lambda.encode t) := (codeHasNormalForm_encode t).2 hcon
      rw [hfe] at hc
      rw [hc] at hb
      exact Bool.noConfusion hb
    have hprog : ¬ IsProgramFor t s := by
      rintro ⟨-, hred⟩
      exact hnf ⟨Lambda.church s, hred, Lambda.church_normal s⟩
    have hrun := progRun_of_false f (s := s) hb
    rw [progRun_eq_progTest hfe] at hrun
    simp only [Part.some_inj] at hrun
    rw [hrun]
    simp [hprog]
  · have hnf : HasNormalForm t := by
      have hc : CodeHasNormalForm (Lambda.encode t) := by rw [hfe]; exact hb
      exact (codeHasNormalForm_encode t).1 hc
    have hrun := progRun_of_true f hb hnf (s := s)
    rw [progRun_eq_progTest hfe] at hrun
    simp only [Part.some_inj] at hrun
    rw [hrun]
    rcases hcl : isClosed_code (Lambda.encode t) with _ | _
    · have hncl : ¬ IsClosed t := by
        intro hcon
        rw [← isClosed_code_correct t, hcl] at hcon
        exact Bool.noConfusion hcon
      simp only [cond_false]
      constructor
      · intro hcon; exact Bool.noConfusion hcon
      · rintro ⟨hclosed, -⟩; exact absurd hclosed hncl
    · have hcl' : IsClosed t := (isClosed_code_correct t).1 hcl
      have hchurch : Lambda.church_code s = Lambda.encode (Lambda.church s) :=
        (Lambda.encode_church_eq_church_code s).symm
      simp only [cond_true, decide_eq_true_eq, hchurch]
      constructor
      · intro hc
        exact ⟨hcl', (Lambda.encode_injective hc) ▸ reduces_nf t⟩
      · rintro ⟨-, hred⟩
        exact congrArg Lambda.encode (nf_eq_of_reduces_normal hred (Lambda.church_normal s))

theorem progTest_true_iff (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) {c s : ℕ}
    (h : progTest f (c, s) = Bool.true) : ∃ t : Lambda, Lambda.encode t = c ∧ IsProgramFor t s := by
  classical
  rcases hb : f c with _ | _
  · have hrun := progRun_of_false f (s := s) hb
    rw [progRun_eq_progTest hfe] at hrun
    simp only [Part.some_inj] at hrun
    rw [hrun] at h
    exact absurd h (by simp)
  · obtain ⟨t, hte, hnf⟩ := (codeHasNormalForm_iff c).1 ((hfe c).2 hb)
    subst hte
    exact ⟨t, rfl, (progTest_encode hfe t s).1 h⟩

------------------------------------------------------------------------
-- The bounded minimisation
------------------------------------------------------------------------

/-- The least size of a program for `s` among the terms with code `< k`, defaulting to the size
`3 * s + 3` of the Church numeral. -/
def minProg (g : ℕ → Bool) (s k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (3 * s + 3)
    (fun c acc => cond (progTest g (c, s)) (min (size_code c) acc) acc) k

theorem minProg_eq_rec (g : ℕ → Bool) (s k : ℕ) :
    Nat.rec (motive := fun _ => ℕ) (3 * s + 3)
      (fun c acc => cond (progTest g (c, s)) (min (size_code c) acc) acc) k = minProg g s k :=
  rfl

theorem kolm_le_minProg (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) (s k : ℕ) :
    kolm s ≤ minProg f s k := by
  induction k with
  | zero => simpa [minProg] using kolm_le_church s
  | succ c ih =>
      rcases hb : progTest f (c, s) with _ | _
      · simpa [minProg, hb] using ih
      · obtain ⟨t, hte, hprog⟩ := progTest_true_iff hfe hb
        have : kolm s ≤ size_code c := by
          rw [← hte, size_code_correct]
          exact kolm_le_of_isProgramFor hprog
        simp only [minProg, hb, cond_true, le_min_iff]
        exact ⟨this, ih⟩

theorem minProg_le_of_isProgramFor (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true)
    {t : Lambda} {s : ℕ} (hprog : IsProgramFor t s) {k : ℕ} (hk : Lambda.encode t < k) :
    minProg f s k ≤ size t := by
  induction k with
  | zero => omega
  | succ c ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hlt | heq
      · have := ih hlt
        rcases hb : progTest f (c, s) with _ | _
        · simpa [minProg, hb] using this
        · simp only [minProg, hb, cond_true, min_le_iff]
          exact Or.inr this
      · subst heq
        have hb : progTest f (Lambda.encode t, s) = Bool.true := by
          rw [progTest_encode hfe t s]
          simpa using hprog
        simp only [minProg, hb, cond_true, min_le_iff]
        left
        rw [size_code_correct]

/-- The bounded minimisation computes `K`. -/
theorem kolm_eq_minProg (hfe : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true) (s : ℕ) :
    kolm s = minProg f s (encBound (3 * s + 3) + 1) := by
  refine le_antisymm (kolm_le_minProg hfe s _) ?_
  obtain ⟨t, hprog, hsize⟩ := exists_program_of_kolm s
  have hsz : size t ≤ 3 * s + 3 := by
    rw [hsize]
    exact kolm_le_church s
  have hcode : Lambda.encode t < encBound (3 * s + 3) + 1 :=
    Nat.lt_succ_of_le (encode_le_encBound t _ hsz)
  rw [← hsize]
  exact minProg_le_of_isProgramFor hfe hprog hcode

end Bridge

------------------------------------------------------------------------
-- The bridge
------------------------------------------------------------------------

set_option maxHeartbeats 1000000 in
-- Assembling the primitive recursion for the bounded minimisation is elaboration heavy.
/-- **A halting oracle computes Kolmogorov complexity.**  If normalization of lambda terms were
decidable, `K` would be a computable function. -/
theorem computable_kolm_of_decidable_halting (h : ComputablePred CodeHasNormalForm) :
    Computable kolm := by
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  have hfe' : ∀ c, CodeHasNormalForm c ↔ f c = Bool.true := fun c => iff_of_eq (congrFun hfe c)
  have hbound : Computable (fun s : ℕ => encBound (3 * s + 3) + 1) :=
    (Primrec.succ.comp (encBound_primrec.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
        (Primrec.const 3)))).to_comp
  have hbase : Computable (fun s : ℕ => 3 * s + 3) :=
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.id)
      (Primrec.const 3)).to_comp
  have hstep : Computable₂ (fun (s : ℕ) (q : ℕ × ℕ) =>
      cond (progTest f (q.1, s)) (min (size_code q.1) q.2) q.2) := by
    refine Computable.cond ?_ ?_ (Computable.snd.comp Computable.snd)
    · exact (computable_progTest hf hfe').comp
        (Computable.pair (Computable.fst.comp Computable.snd) Computable.fst)
    · exact (Primrec.nat_min.to_comp).comp
        (size_code_primrec.to_comp.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd)
  have hrec := Computable.nat_rec (f := fun s : ℕ => encBound (3 * s + 3) + 1)
    (g := fun s : ℕ => 3 * s + 3)
    (h := fun (s : ℕ) (q : ℕ × ℕ) => cond (progTest f (q.1, s)) (min (size_code q.1) q.2) q.2)
    hbound hbase hstep
  refine hrec.of_eq (fun s => ?_)
  simp only []
  rw [minProg_eq_rec]
  exact (kolm_eq_minProg hfe' s).symm

/-- **Berry's paradox proves the halting problem undecidable.**  Contraposing the bridge, the
uncomputability of `K` gives a second, completely different proof of
`Lambda.not_computablePred_codeHasNormalForm`. -/
theorem not_computablePred_codeHasNormalForm_of_berry : ¬ ComputablePred CodeHasNormalForm :=
  fun h => not_computable_kolm (computable_kolm_of_decidable_halting h)

/-- The two negative results of the theory are equivalent statements about the same oracle: `K`
is uncomputable *because* the halting problem is undecidable. -/
theorem kolm_uncomputable_iff :
    (¬ Computable kolm) ↔ (¬ ComputablePred CodeHasNormalForm) :=
  ⟨fun _ => not_computablePred_codeHasNormalForm_of_berry,
   fun _ => not_computable_kolm⟩

end Lambda

end
