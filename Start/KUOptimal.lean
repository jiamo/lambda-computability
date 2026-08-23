/-
# The universal prefix machine is optimal for the lambda prefix machine

`Start/KCMachine.lean` builds a universal prefix machine `KC.U` by Kraft–Chaitin allocation and
`Start/ChaitinOmega.lean` defines the prefix complexity `Lambda.kolmP` of the *lambda* prefix
machine, whose programs are the self-delimiting bit codes `Lambda.bits t` of closed lambda terms.
Until now the two complexities lived side by side without any comparison.  This file connects
them:

* `KC.lamReq` is a total computable stream of Kraft–Chaitin requests which, for every closed
  lambda term `t` reducing to the Church numeral of `m`, contains the request
  `(|bits t|, m)` — exactly once, at the first step of the leftmost run at which `t` reaches
  `church m`.
* `KC.sum_wtOpt_lamReq_le` bounds the total weight of that stream by one; this is Kraft's
  inequality for the prefix free coding `Lambda.bits`.
* `KC.exists_const_KU_le_kolmP` — **optimality**: `∃ c, ∀ s, KU s ≤ Lambda.kolmP s + c`.

Only this direction holds with these definitions: a `U`-program is an arbitrary bit string, while
a lambda program has to spend two bits per node of its syntax tree, so `kolmP` can exceed `KU` by
more than an additive constant.
-/

import Start.LevinSchnorr

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace KC

------------------------------------------------------------------------
-- The request stream of the lambda prefix machine
------------------------------------------------------------------------

/-- `lamHit e m i` says that the code `e` is a valid code of a closed term whose leftmost run
reaches the Church numeral of `m` after `i` steps. -/
def lamHit (e m i : ℕ) : Bool :=
  Lambda.is_valid_code e && decide (Lambda.freeMax_code e = 0) &&
    decide (Lambda.nstep_code^[i] e = Lambda.church_code m)

/-- `lamFirst e m i` restricts `KC.lamHit` to the *first* step at which the run arrives. -/
def lamFirst (e m i : ℕ) : Bool :=
  lamHit e m i && (decide (i = 0) || !lamHit e m (i - 1))

/-- The request stream of the lambda prefix machine: the index `n` is read as a triple
`(e, m, i)`, and the request `(|bits t|, m)` is issued when `e` codes a closed term `t` whose
leftmost run first reaches `church m` at step `i`. -/
def lamReq (n : ℕ) : Option (ℕ × ℕ) :=
  cond (lamFirst n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2)
    (some (Lambda.bitsLen_code n.unpair.1, n.unpair.2.unpair.1)) none

theorem lamHit_iff {e m i : ℕ} :
    lamHit e m i = true ↔ Lambda.is_valid_code e = true ∧ Lambda.freeMax_code e = 0 ∧
      Lambda.nstep_code^[i] e = Lambda.church_code m := by
  simp [lamHit, and_assoc]

theorem lamFirst_iff {e m i : ℕ} :
    lamFirst e m i = true ↔ lamHit e m i = true ∧ (i = 0 ∨ lamHit e m (i - 1) = false) := by
  simp [lamFirst]

------------------------------------------------------------------------
-- Computability
------------------------------------------------------------------------

theorem primrec_lamHit : Primrec fun q : ℕ × ℕ × ℕ => lamHit q.1 q.2.1 q.2.2 := by
  have he : Primrec fun q : ℕ × ℕ × ℕ => q.1 := Primrec.fst
  have hm : Primrec fun q : ℕ × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hi : Primrec fun q : ℕ × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
  have hA : Primrec fun q : ℕ × ℕ × ℕ => Lambda.is_valid_code q.1 :=
    Lambda.is_valid_code_primrec.comp he
  have hB : Primrec fun q : ℕ × ℕ × ℕ => decide (Lambda.freeMax_code q.1 = 0) :=
    (PrimrecRel.comp (Primrec.eq (α := ℕ)) (Lambda.freeMax_code_primrec.comp he)
      (Primrec.const 0)).decide
  have hC : Primrec fun q : ℕ × ℕ × ℕ =>
      decide (Lambda.nstep_code^[q.2.2] q.1 = Lambda.church_code q.2.1) :=
    (PrimrecRel.comp (Primrec.eq (α := ℕ)) (Lambda.nstep_code_iterate_primrec.comp he hi)
      (Lambda.church_code_primrec.comp hm)).decide
  exact (Primrec₂.comp Primrec.and (Primrec₂.comp Primrec.and hA hB) hC).of_eq fun _ => rfl

theorem primrec_lamFirst : Primrec fun q : ℕ × ℕ × ℕ => lamFirst q.1 q.2.1 q.2.2 := by
  have he : Primrec fun q : ℕ × ℕ × ℕ => q.1 := Primrec.fst
  have hm : Primrec fun q : ℕ × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
  have hi : Primrec fun q : ℕ × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
  have h2 : Primrec fun q : ℕ × ℕ × ℕ => lamHit q.1 q.2.1 (q.2.2 - 1) :=
    primrec_lamHit.comp (Primrec.pair he
      (Primrec.pair hm (Primrec.nat_sub.comp hi (Primrec.const 1))))
  have h3 : Primrec fun q : ℕ × ℕ × ℕ => decide (q.2.2 = 0) :=
    (PrimrecRel.comp (Primrec.eq (α := ℕ)) hi (Primrec.const 0)).decide
  exact (Primrec₂.comp Primrec.and primrec_lamHit
    (Primrec₂.comp Primrec.or h3 (Primrec.not.comp h2))).of_eq fun _ => rfl

theorem computable_lamReq : Computable lamReq := by
  have he : Primrec fun n : ℕ => n.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hm : Primrec fun n : ℕ => n.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hi : Primrec fun n : ℕ => n.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  have hcond : Primrec fun n : ℕ => lamFirst n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 :=
    primrec_lamFirst.comp (Primrec.pair he (Primrec.pair hm hi))
  have hsome : Primrec fun n : ℕ => (some (Lambda.bitsLen_code n.unpair.1, n.unpair.2.unpair.1) :
      Option (ℕ × ℕ)) :=
    Primrec.option_some.comp (Primrec.pair (Lambda.bitsLen_code_primrec.comp he) hm)
  exact (Primrec.cond hcond hsome (Primrec.const none)).to_comp

------------------------------------------------------------------------
-- The leftmost run stays at a Church numeral
------------------------------------------------------------------------

theorem nstep_code_church (m : ℕ) :
    Lambda.nstep_code (Lambda.church_code m) = Lambda.church_code m := by
  rw [← Lambda.encode_church_eq_church_code, Lambda.nstep_code_correct,
    Lambda.nstep_of_is_normal (Lambda.church_normal m)]

theorem lamHit_mono {e m i : ℕ} (h : lamHit e m i = true) {j : ℕ} (hj : i ≤ j) :
    lamHit e m j = true := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + i := ⟨j - i, by omega⟩
  obtain ⟨h1, h2, h3⟩ := lamHit_iff.1 h
  refine lamHit_iff.2 ⟨h1, h2, ?_⟩
  rw [Function.iterate_add_apply, h3, Function.iterate_fixed (nstep_code_church m)]

theorem church_code_inj {m m' : ℕ} (h : Lambda.church_code m = Lambda.church_code m') : m = m' := by
  refine Lambda.church_injective (Lambda.encode_injective ?_)
  rw [Lambda.encode_church_eq_church_code, Lambda.encode_church_eq_church_code, h]

/-- Each code emits at most one request: both the target and the arrival time are determined. -/
theorem lamFirst_unique {e m i m' i' : ℕ} (h : lamFirst e m i = true)
    (h' : lamFirst e m' i' = true) : m = m' ∧ i = i' := by
  obtain ⟨hh, hmin⟩ := lamFirst_iff.1 h
  obtain ⟨hh', hmin'⟩ := lamFirst_iff.1 h'
  obtain ⟨-, -, h3⟩ := lamHit_iff.1 hh
  obtain ⟨-, -, h3'⟩ := lamHit_iff.1 hh'
  have hm : m = m' := by
    rcases le_total i i' with hle | hle
    · obtain ⟨-, -, h4⟩ := lamHit_iff.1 (lamHit_mono hh hle)
      exact church_code_inj (h4.symm.trans h3')
    · obtain ⟨-, -, h4⟩ := lamHit_iff.1 (lamHit_mono hh' hle)
      exact church_code_inj (h3.symm.trans h4)
  subst hm
  refine ⟨rfl, ?_⟩
  by_contra hne
  rcases Nat.lt_or_ge i i' with hlt | hge
  · have hprev : lamHit e m (i' - 1) = true := lamHit_mono hh (by omega)
    rcases hmin' with h0 | hfalse
    · omega
    · rw [hprev] at hfalse; exact Bool.noConfusion hfalse
  · have hlt : i' < i := by omega
    have hprev : lamHit e m (i - 1) = true := lamHit_mono hh' (by omega)
    rcases hmin with h0 | hfalse
    · omega
    · rw [hprev] at hfalse; exact Bool.noConfusion hfalse

------------------------------------------------------------------------
-- The total weight of the stream
------------------------------------------------------------------------

theorem lamReq_eq_none {n : ℕ}
    (h : lamFirst n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 = false) :
    lamReq n = none := by
  simp [lamReq, h]

theorem lamFirst_of_lamReq {n : ℕ} (h : lamReq n ≠ none) :
    lamFirst n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 = true := by
  rcases hb : lamFirst n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 with _ | _
  · exact absurd (lamReq_eq_none hb) h
  · rfl

theorem lamReq_valid {n : ℕ} (h : lamReq n ≠ none) :
    Lambda.is_valid_code n.unpair.1 = true :=
  (lamHit_iff.1 (lamFirst_iff.1 (lamFirst_of_lamReq h)).1).1

theorem wtOpt_lamReq {n : ℕ} (h : lamReq n ≠ none) :
    wtOpt (lamReq n) = Kraft.wt (Lambda.bits (Lambda.decodeD n.unpair.1)) := by
  have hb := lamFirst_of_lamReq h
  have hcode : Lambda.encode (Lambda.decodeD n.unpair.1) = n.unpair.1 :=
    Lambda.encode_decodeD (lamReq_valid h)
  have hlen : Lambda.bitsLen_code n.unpair.1
      = (Lambda.bits (Lambda.decodeD n.unpair.1)).length := by
    conv_lhs => rw [← hcode]
    rw [Lambda.bitsLen_code_correct]
  simp [lamReq, hb, wtOpt, wt, Kraft.wt, hlen]

/-- **The requests of the lambda machine have total weight at most one.**  This is Kraft's
inequality for the prefix free coding `Lambda.bits`. -/
theorem sum_wtOpt_lamReq_le (F : Finset ℕ) : ∑ n ∈ F, wtOpt (lamReq n) ≤ 1 := by
  classical
  set F' := F.filter (fun n => lamReq n ≠ none)
  have hmem : ∀ n ∈ F', lamReq n ≠ none := fun n hn => (Finset.mem_filter.1 hn).2
  have hsum : ∑ n ∈ F, wtOpt (lamReq n) = ∑ n ∈ F', wtOpt (lamReq n) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hn'
    simp only [Finset.mem_filter, not_and, not_not] at hn'
    rw [hn' hn]
    rfl
  set f : ℕ → Lambda := fun n => Lambda.decodeD n.unpair.1
  have hinj : ∀ n ∈ F', ∀ n' ∈ F', f n = f n' → n = n' := by
    intro n hn n' hn' heq
    have he : n.unpair.1 = n'.unpair.1 := by
      rw [← Lambda.encode_decodeD (lamReq_valid (hmem n hn)),
        ← Lambda.encode_decodeD (lamReq_valid (hmem n' hn'))]
      exact congrArg Lambda.encode heq
    have hb : lamFirst n'.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 = true := by
      rw [← he]; exact lamFirst_of_lamReq (hmem n hn)
    obtain ⟨hm, hi⟩ := lamFirst_unique hb (lamFirst_of_lamReq (hmem n' hn'))
    have h2 : n.unpair.2 = n'.unpair.2 := by
      rw [← Nat.pair_unpair n.unpair.2, ← Nat.pair_unpair n'.unpair.2, hm, hi]
    rw [← Nat.pair_unpair n, ← Nat.pair_unpair n', he, h2]
  calc ∑ n ∈ F, wtOpt (lamReq n) = ∑ n ∈ F', wtOpt (lamReq n) := hsum
    _ = ∑ n ∈ F', Kraft.wt (Lambda.bits (f n)) :=
        Finset.sum_congr rfl fun n hn => wtOpt_lamReq (hmem n hn)
    _ = ∑ t ∈ F'.image f, Kraft.wt (Lambda.bits t) := by rw [Finset.sum_image hinj]
    _ ≤ 1 := Kraft.sum_wt_le_one Lambda.bits_prefixFreeCoding _

------------------------------------------------------------------------
-- Every lambda program is requested
------------------------------------------------------------------------

theorem exists_lamReq_of_isProgramFor {t : Lambda} {m : ℕ} (h : Lambda.IsProgramFor t m) :
    ∃ n : ℕ, lamReq n = some ((Lambda.bits t).length, m) := by
  classical
  obtain ⟨i, hi⟩ := Lambda.exists_iterate_eq_church_of_isProgramFor h
  have hhit : lamHit (Lambda.encode t) m i = true := by
    refine lamHit_iff.2 ⟨Lambda.is_valid_code_encode t, ?_, ?_⟩
    · rw [Lambda.freeMax_code_correct]
      exact (Lambda.isClosed_iff_freeMax_eq_zero t).1 h.1
    · rw [Lambda.nstep_code_iterate, hi, Lambda.encode_church_eq_church_code]
  have hex : ∃ k, lamHit (Lambda.encode t) m k = true := ⟨i, hhit⟩
  have hfind : lamHit (Lambda.encode t) m (Nat.find hex) = true := Nat.find_spec hex
  have hfirst : lamFirst (Lambda.encode t) m (Nat.find hex) = true := by
    refine lamFirst_iff.2 ⟨hfind, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases hb : lamHit (Lambda.encode t) m (Nat.find hex - 1) with _ | _
      · rfl
      · exfalso
        have hle : Nat.find hex ≤ Nat.find hex - 1 := Nat.find_le hb
        omega
  refine ⟨Nat.pair (Lambda.encode t) (Nat.pair m (Nat.find hex)), ?_⟩
  simp only [lamReq, Nat.unpair_pair, hfirst, cond_true, Lambda.bitsLen_code_correct]

------------------------------------------------------------------------
-- Optimality
------------------------------------------------------------------------

/-- **The Kraft–Chaitin universal machine is optimal for the lambda prefix machine**: its
complexity `KC.KU` is below the lambda prefix complexity `Lambda.kolmP` up to an additive
constant. -/
theorem exists_const_KU_le_kolmP : ∃ c : ℕ, ∀ s : ℕ, KU s ≤ Lambda.kolmP s + c := by
  obtain ⟨c, hc⟩ := exists_const_KU_le computable_lamReq sum_wtOpt_lamReq_le
  refine ⟨c, fun s => ?_⟩
  obtain ⟨t, hprog, hbits⟩ := Lambda.exists_program_of_kolmP s
  obtain ⟨n, hn⟩ := exists_lamReq_of_isProgramFor hprog
  have hle := hc n _ _ hn
  rwa [hbits] at hle

/-- Incompressibility of the prefixes of `X` for the universal machine `KC.U` transfers to the
lambda prefix complexity. -/
theorem exists_const_le_kolmP_prefix_of_exists_const_le_KU {X : ℕ → Bool}
    (h : ∃ c : ℕ, ∀ n : ℕ, n ≤ KU (Encodable.encode (Lambda.prefixList X n)) + c) :
    ∃ c : ℕ, ∀ n : ℕ, n ≤ Lambda.kolmP (Encodable.encode (Lambda.prefixList X n)) + c := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := exists_const_KU_le_kolmP
  refine ⟨c + d, fun n => ?_⟩
  have h1 := hc n
  have h2 := hd (Encodable.encode (Lambda.prefixList X n))
  omega

end KC

end
