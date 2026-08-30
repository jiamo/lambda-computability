/-
**Kolmogorov complexity is upper semicomputable.**

`Start/KolmogorovHalting.lean` computes `K` from a halting oracle, by minimising the size of a
program over a computably bounded range of codes — using the oracle to know which of them
terminate.  Without the oracle one can still run each candidate for a bounded number of steps;
what is lost is only that a candidate may not have been *seen* to converge yet.  That gives the
classical *one-sided* effectivity of `K`:

* `Lambda.progBy` — the primitive recursive test "the code `c` is a closed term whose
  leftmost-outermost run reaches `church s` within `k` steps", with its correctness lemmas
  (`Lambda.progBy_encode_iff`, `Lambda.exists_isProgramFor_of_progBy`,
  `Lambda.exists_progBy_of_isProgramFor`) and its stability in the number of steps
  (`Lambda.progBy_mono`);
* `Lambda.rePred_kolm_le` — **`K s ≤ n` is recursively enumerable**, so `K` is upper
  semicomputable, while `Lambda.not_computablePred_kolm_le` says it is not decidable and
  `Lambda.not_rePred_lt_kolm` says the complementary relation `n < K s` is not even r.e.;
* `Lambda.kolmAt` — the stage-`k` approximation: the least size of a program for `s` found within
  `k` steps, among the codes below the bound of `Start/CodeArith.lean`, defaulting to the size of
  the Church numeral;
* `Lambda.kolm_le_kolmAt`, `Lambda.kolmAt_antitone`, `Lambda.exists_kolmAt_eq_kolm` — the
  approximation is above `K`, non-increasing in the stage, and reaches `K` — indeed it is exact
  from some stage on (`Lambda.kolmAt_eventually_eq_kolm`); hence
  `Lambda.kolm_eq_iInf_kolmAt` — **`K` is the pointwise infimum of a computable, non-increasing
  family** (`Lambda.primrec_kolmAt`).
-/

import Start.ChaitinIncompleteness
import Start.OmegaUncomputable
import Start.PostSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ### The time-bounded program test -/

/-- The **time-bounded program test**: the code `c` is a closed term whose leftmost-outermost run
reaches `church s` within `k` steps. -/
def progBy (s k c : ℕ) : Bool :=
  is_valid_code c && isClosed_code c && decide (nstep_code^[k] c = Lambda.church_code s)

theorem progBy_primrec : Primrec fun p : (ℕ × ℕ) × ℕ => progBy p.1.1 p.1.2 p.2 := by
  have hband : ∀ {f g : (ℕ × ℕ) × ℕ → Bool}, Primrec f → Primrec g → Primrec fun p => f p && g p :=
    fun hf hg => (Primrec.dom_bool₂ (fun a b => a && b)).comp hf hg
  have h1 : Primrec fun p : (ℕ × ℕ) × ℕ => is_valid_code p.2 :=
    is_valid_code_primrec.comp Primrec.snd
  have h2 : Primrec fun p : (ℕ × ℕ) × ℕ => isClosed_code p.2 :=
    isClosed_code_primrec.comp Primrec.snd
  have h3 : Primrec fun p : (ℕ × ℕ) × ℕ => nstep_code^[p.1.2] p.2 :=
    nstep_code_iterate_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)
  have h4 : Primrec fun p : (ℕ × ℕ) × ℕ => Lambda.church_code p.1.1 :=
    church_code_primrec.comp (Primrec.fst.comp Primrec.fst)
  have h5 : Primrec fun p : (ℕ × ℕ) × ℕ =>
      decide (nstep_code^[p.1.2] p.2 = Lambda.church_code p.1.1) := by
    obtain ⟨_, h'⟩ := Primrec.eq.comp h3 h4
    exact h'.of_eq fun a => by congr 1
  exact hband (hband h1 h2) h5

theorem progBy_encode_iff (t : Lambda) (s k : ℕ) :
    progBy s k (Lambda.encode t) = Bool.true ↔ IsClosed t ∧ nstep^[k] t = Lambda.church s := by
  have hcode : Lambda.encode (nstep^[k] t) = Lambda.church_code s ↔
      nstep^[k] t = Lambda.church s := by
    rw [← encode_church_eq_church_code]
    constructor
    · intro h
      have := congrArg Lambda.decode h
      simpa [Lambda.decode_encode] using this
    · exact congrArg _
  simp [progBy, nstep_code_iterate, hcode, is_valid_code_encode]

theorem exists_isProgramFor_of_progBy {s k c : ℕ} (h : progBy s k c = Bool.true) :
    ∃ t : Lambda, Lambda.encode t = c ∧ IsProgramFor t s := by
  have hvalid : is_valid_code c = Bool.true := by
    simp only [progBy, Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨t, rfl⟩ := exists_encode_of_is_valid_code c hvalid
  obtain ⟨hcl, hrun⟩ := (progBy_encode_iff t s k).1 h
  exact ⟨t, rfl, hcl, hrun ▸ reduces_nstep_iterate t k⟩

theorem exists_progBy_of_isProgramFor {t : Lambda} {s : ℕ} (h : IsProgramFor t s) :
    ∃ k, progBy s k (Lambda.encode t) = Bool.true := by
  refine ⟨haltTime t, (progBy_encode_iff t s _).2 ⟨h.1, ?_⟩⟩
  exact nf_eq_of_reduces_normal h.2 (church_normal s)

/-- Once the run has been seen to converge it stays converged. -/
theorem progBy_mono {s k k' c : ℕ} (hk : k ≤ k') (h : progBy s k c = Bool.true) :
    progBy s k' c = Bool.true := by
  have hvalid : is_valid_code c = Bool.true := by
    simp only [progBy, Bool.and_eq_true] at h
    exact h.1.1
  obtain ⟨t, rfl⟩ := exists_encode_of_is_valid_code c hvalid
  obtain ⟨hcl, hrun⟩ := (progBy_encode_iff t s k).1 h
  refine (progBy_encode_iff t s k').2 ⟨hcl, ?_⟩
  rw [nstep_iterate_stable (by rw [hrun]; exact church_normal s) hk, hrun]

/-! ### One-sided effectivity -/

/-- **Kolmogorov complexity is upper semicomputable**: the relation `K s ≤ n` is recursively
enumerable.  (By `Lambda.not_computablePred_kolm_le` it is not decidable.) -/
theorem rePred_kolm_le : REPred fun q : ℕ × ℕ => kolm q.1 ≤ q.2 := by
  refine Post.rePred_of_exists_test
    (fun q j => progBy q.1 (Nat.unpair j).2 (Nat.unpair j).1 &&
      decide (size_code (Nat.unpair j).1 ≤ q.2)) ?_ ?_
  · have hprog : Primrec fun r : (ℕ × ℕ) × ℕ =>
        progBy r.1.1 (Nat.unpair r.2).2 (Nat.unpair r.2).1 :=
      progBy_primrec.comp
        (((Primrec.fst.comp (Primrec.fst : Primrec fun r : (ℕ × ℕ) × ℕ => r.1))).pair
          (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)) |>.pair
          (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    have hsize : Primrec fun r : (ℕ × ℕ) × ℕ =>
        decide (size_code (Nat.unpair r.2).1 ≤ r.1.2) := by
      obtain ⟨_, h'⟩ := Primrec.nat_le.comp
        (size_code_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp
          (Primrec.snd : Primrec fun r : (ℕ × ℕ) × ℕ => r.2))))
        (Primrec.snd.comp (Primrec.fst : Primrec fun r : (ℕ × ℕ) × ℕ => r.1))
      exact h'.of_eq fun a => by congr 1
    exact (Primrec.dom_bool₂ (fun a b => a && b)).comp hprog hsize
  · rintro ⟨s, n⟩
    dsimp only
    constructor
    · intro hle
      obtain ⟨t, hprog, hsize⟩ := exists_program_of_kolm s
      obtain ⟨k, hk⟩ := exists_progBy_of_isProgramFor hprog
      refine ⟨Nat.pair (Lambda.encode t) k, ?_⟩
      simp only [Nat.unpair_pair, hk, Bool.and_eq_true, decide_eq_true_eq, true_and,
        size_code_correct]
      omega
    · rintro ⟨j, hj⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
      obtain ⟨t, hte, hprog⟩ := exists_isProgramFor_of_progBy hj.1
      have hkolm := kolm_le_of_isProgramFor hprog
      have hsz : size_code (Nat.unpair j).1 = size t := by rw [← hte, size_code_correct]
      have hj2 := hj.2
      omega

/-- The other half of `Lambda.rePred_kolm_le` fails: **`n < K s` is not recursively enumerable**.
Indeed an enumeration of it would be a sound r.e. system of lower bounds proving *all* true ones,
contradicting `Lambda.chaitin_incompleteness`. -/
theorem not_rePred_lt_kolm : ¬ REPred fun q : ℕ × ℕ => q.2 < kolm q.1 := by
  intro h
  obtain ⟨c, hc⟩ := chaitin_incompleteness (S := fun x n => n < kolm x) h fun _ _ hx => hx
  obtain ⟨s, hs⟩ := exists_incompressible (c + 1)
  exact absurd (hc s c (lt_of_lt_of_le (Nat.lt_succ_self c) hs)) (lt_irrefl c)

/-! ### The stage-by-stage approximation -/

/-- The least size of a program for `s` found within `k` steps among the codes below `b`,
defaulting to the size `3 * s + 3` of the Church numeral. -/
def minAt (s k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ) (3 * s + 3)
    (fun c acc => cond (progBy s k c) (min (size_code c) acc) acc)

/-- The **stage-`k` approximation** of Kolmogorov complexity. -/
def kolmAt (s k : ℕ) : ℕ := minAt s k (encBound (3 * s + 3) + 1)

theorem minAt_eq_rec (s k b : ℕ) :
    minAt s k b = Nat.rec (motive := fun _ => ℕ) (3 * s + 3)
      (fun c acc => cond (progBy s k c) (min (size_code c) acc) acc) b := rfl

theorem kolm_le_minAt (s k b : ℕ) : kolm s ≤ minAt s k b := by
  induction b with
  | zero => simpa [minAt] using kolm_le_church s
  | succ c ih =>
      rcases hb : progBy s k c with _ | _
      · simpa [minAt, hb] using ih
      · obtain ⟨t, hte, hprog⟩ := exists_isProgramFor_of_progBy hb
        have hsz : kolm s ≤ size_code c := by
          rw [← hte, size_code_correct]
          exact kolm_le_of_isProgramFor hprog
        simp only [minAt, hb, cond_true, le_min_iff]
        exact ⟨hsz, ih⟩

theorem minAt_le_of_progBy {s k b c : ℕ} (h : progBy s k c = Bool.true) (hc : c < b) :
    minAt s k b ≤ size_code c := by
  induction b with
  | zero => omega
  | succ d ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | heq
      · have hle := ih hlt
        rcases hb : progBy s k d with _ | _
        · simpa [minAt, hb] using hle
        · simp only [minAt, hb, cond_true, min_le_iff]
          exact Or.inr hle
      · subst heq
        simp only [minAt, h, cond_true, min_le_iff]
        exact Or.inl le_rfl

theorem minAt_antitone {s k k' : ℕ} (hk : k ≤ k') (b : ℕ) : minAt s k' b ≤ minAt s k b := by
  induction b with
  | zero => simp [minAt]
  | succ c ih =>
      rcases hb : progBy s k c with _ | _
      · rcases hb' : progBy s k' c with _ | _
        · simpa [minAt, hb, hb'] using ih
        · simp only [minAt, hb, hb', cond_true, cond_false, min_le_iff]
          exact Or.inr ih
      · have hb' : progBy s k' c = Bool.true := progBy_mono hk hb
        simp only [minAt, hb, hb', cond_true, le_min_iff, min_le_iff]
        exact ⟨Or.inl le_rfl, Or.inr ih⟩

theorem kolm_le_kolmAt (s k : ℕ) : kolm s ≤ kolmAt s k := kolm_le_minAt s k _

theorem kolmAt_antitone {s k k' : ℕ} (hk : k ≤ k') : kolmAt s k' ≤ kolmAt s k :=
  minAt_antitone hk _

/-- The approximation is exact from some stage on. -/
theorem exists_kolmAt_eq_kolm (s : ℕ) : ∃ k, kolmAt s k = kolm s := by
  obtain ⟨t, hprog, hsize⟩ := exists_program_of_kolm s
  obtain ⟨k, hk⟩ := exists_progBy_of_isProgramFor hprog
  refine ⟨k, le_antisymm ?_ (kolm_le_kolmAt s k)⟩
  have hsz : size t ≤ 3 * s + 3 := by
    rw [hsize]
    exact kolm_le_church s
  have hcode : Lambda.encode t < encBound (3 * s + 3) + 1 :=
    Nat.lt_succ_of_le (encode_le_encBound t _ hsz)
  have hmin := minAt_le_of_progBy hk hcode
  rw [size_code_correct, hsize] at hmin
  exact hmin

/-- **`K` is limit computable**: the approximation is not merely exact at one stage, it is exact
from that stage on. -/
theorem kolmAt_eventually_eq_kolm (s : ℕ) : ∃ k₀, ∀ k, k₀ ≤ k → kolmAt s k = kolm s := by
  obtain ⟨k₀, hk₀⟩ := exists_kolmAt_eq_kolm s
  exact ⟨k₀, fun k hk => le_antisymm (hk₀ ▸ kolmAt_antitone hk) (kolm_le_kolmAt s k)⟩

/-- **`K` is the infimum of its computable approximations.** -/
theorem kolm_eq_iInf_kolmAt (s : ℕ) : kolm s = ⨅ k, kolmAt s k := by
  obtain ⟨k, hk⟩ := exists_kolmAt_eq_kolm s
  refine le_antisymm (le_ciInf fun j => kolm_le_kolmAt s j) ?_
  calc ⨅ j, kolmAt s j ≤ kolmAt s k := ciInf_le (OrderBot.bddBelow _) k
    _ = kolm s := hk

-- Assembling the primitive recursion for the bounded minimisation is elaboration heavy.
private theorem hbase_primrec : Primrec fun q : ℕ × ℕ => 3 * q.1 + 3 :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst) (Primrec.const 3)

private theorem hstep_primrec : Primrec₂ fun (q : ℕ × ℕ) (r : ℕ × ℕ) =>
    cond (progBy q.1 q.2 r.1) (min (size_code r.1) r.2) r.2 := by
  refine Primrec.cond ?_ ?_ (Primrec.snd.comp Primrec.snd)
  · exact progBy_primrec.comp (((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd))
  · exact Primrec.nat_min.comp (size_code_primrec.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)

/-- The bounded minimisation is primitive recursive in all three arguments. -/
theorem primrec_minAt : Primrec fun p : (ℕ × ℕ) × ℕ => minAt p.1.1 p.1.2 p.2 :=
  Primrec.of_eq (Primrec.nat_rec hbase_primrec hstep_primrec) fun _ => rfl

/-- The approximation is primitive recursive. -/
theorem primrec_kolmAt : Primrec₂ kolmAt := by
  have hbound : Primrec fun q : ℕ × ℕ => encBound (3 * q.1 + 3) + 1 :=
    Primrec.succ.comp (encBound_primrec.comp hbase_primrec)
  exact (primrec_minAt.comp (Primrec.id.pair hbound)).of_eq fun q => rfl

end Lambda

end
