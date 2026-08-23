/-
# Martin-Löf randomness of Chaitin's `Ω`

`Start/KCMachine.lean` builds a universal prefix machine `KC.U` by Kraft–Chaitin allocation and
its halting probability `KC.Omega`; `Start/OmegaUIncompressible.lean` defines the binary
expansion `KC.omegaSeq` of `KC.Omega` and proves Chaitin incompressibility for it.  This file
proves that `KC.omegaSeq` is Martin-Löf random, in the sense of `Lambda.MLRandom`
(`Start/MartinLof.lean`).

The missing half is the converse of Levin–Schnorr: a Martin-Löf test is turned into a computably
enumerated stream of requests of finite total weight, and the Kraft–Chaitin theorem
`KC.exists_const_KU_le` then compresses a prefix of every sequence caught by the test.

* Level `c` of the test enumerates strings: `KC.discovered T c j` is the string discovered at
  step `j`, read off the pair coded by `j`.
* The `j`-th discovery is cut into cylinders of the common length `KC.cutLength T c j` (the
  largest length discovered so far, and at least `c`), minus everything already covered by an
  earlier discovery.  The resulting strings `KC.piece T c j m` have pairwise disjoint cylinders
  inside level `c`, so their weights add up to at most `2 ^ (-c)`.
* `KC.testReq` compresses the pieces of level `2 * k + 2` by `k` bits; the total weight of all
  requests is then at most `∑ₖ 2 ^ (-k-2) ≤ 1`, so Kraft–Chaitin applies.

Together with `KC.exists_const_le_KU_omegaPrefix` this gives
`KC.mlRandom_omegaSeq : Lambda.MLRandom KC.omegaSeq`.
-/

import Start.OmegaUIncompressible

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace KC

open MeasureTheory Lambda

------------------------------------------------------------------------
-- From a Martin-Löf test to requests
------------------------------------------------------------------------

/-- The string discovered at step `j` of level `c` of the test `T`: the step `j` codes a pair
`(σ, s)`, and `σ` is discovered when it has entered level `c` by stage `s`. -/
def discovered (T : MLTest) (c j : ℕ) : Option (List Bool) :=
  if T.enter c ((Encodable.decode (α := List Bool) j.unpair.1).getD []) j.unpair.2 = Bool.true
  then some ((Encodable.decode (α := List Bool) j.unpair.1).getD []) else none

/-- The length of the string discovered at step `j`, or `0`. -/
def discLen (T : MLTest) (c j : ℕ) : ℕ := ((discovered T c j).map List.length).getD 0

/-- One step of the running maximum `KC.cutLength`. -/
def cutStep (T : MLTest) (c : ℕ) (q : ℕ × ℕ) : ℕ := max q.2 (discLen T c (q.1 + 1))

/-- The common length at which the `j`-th discovery of level `c` is cut into cylinders: the
largest length discovered so far, and at least `c`. -/
def cutLength (T : MLTest) (c j : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (max c (discLen T c 0)) (fun k IH => cutStep T c (k, IH)) j

/-- One step of `KC.covered`. -/
def coveredStep (T : MLTest) (c : ℕ) (τ : List Bool) (q : ℕ × Bool) : Bool :=
  q.2 || ((discovered T c q.1).map fun σ => BitStr.isPrefixB σ τ).getD Bool.false

/-- Whether the string `τ` already extends a string discovered before step `j`. -/
def covered (T : MLTest) (c : ℕ) (τ : List Bool) (j : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) Bool.false (fun k IH => coveredStep T c τ (k, IH)) j

/-- The condition under which the string of length `cutLength T c j` and value `m` is a piece of
the discovery `σ` at step `j` of level `c`. -/
def pieceCond (T : MLTest) (c j m : ℕ) (σ : List Bool) : Bool :=
  (decide (m < 2 ^ cutLength T c j) &&
      BitStr.isPrefixB σ (BitStr.ofNat (cutLength T c j) m)) &&
    !covered T c (BitStr.ofNat (cutLength T c j) m) j

/-- The `m`-th piece of the `j`-th discovery of level `c`: the extension of the discovered
string of the common length `cutLength T c j` with numerical value `m`, provided it is not
already covered by an earlier discovery. -/
def piece (T : MLTest) (c j m : ℕ) : Option (List Bool) :=
  (discovered T c j).bind fun σ =>
    bif pieceCond T c j m σ then some (BitStr.ofNat (cutLength T c j) m) else none

/-- The piece named by the index `i`, which codes a triple `(k, j, m)`: the `m`-th piece of the
`j`-th discovery of level `2 * k + 2`. -/
def pieceOf (T : MLTest) (i : ℕ) : Option (List Bool) :=
  piece T (2 * i.unpair.1 + 2) i.unpair.2.unpair.1 i.unpair.2.unpair.2

/-- The request stream attached to a Martin-Löf test: the piece named by `i` is compressed by
`k = i.unpair.1` bits. -/
def testReq (T : MLTest) (i : ℕ) : Option (ℕ × ℕ) :=
  (pieceOf T i).map fun τ => (τ.length - i.unpair.1, Encodable.encode τ)

------------------------------------------------------------------------
-- Basic properties of the cut
------------------------------------------------------------------------

theorem cutLength_succ (T : MLTest) (c j : ℕ) :
    cutLength T c (j + 1) = max (cutLength T c j) (discLen T c (j + 1)) := rfl

theorem le_cutLength (T : MLTest) (c j : ℕ) : c ≤ cutLength T c j := by
  induction j with
  | zero => exact le_max_left _ _
  | succ j ih => exact le_trans ih (by rw [cutLength_succ]; exact le_max_left _ _)

theorem cutLength_mono (T : MLTest) (c : ℕ) : Monotone (cutLength T c) := by
  refine monotone_nat_of_le_succ fun j => ?_
  rw [cutLength_succ]
  exact le_max_left _ _

theorem discLen_le_cutLength (T : MLTest) (c j : ℕ) : discLen T c j ≤ cutLength T c j := by
  cases j with
  | zero => exact le_max_right _ _
  | succ j => rw [cutLength_succ]; exact le_max_right _ _

theorem length_le_cutLength {T : MLTest} {c j j' : ℕ} {σ : List Bool}
    (h : discovered T c j = some σ) (hj : j ≤ j') : σ.length ≤ cutLength T c j' := by
  have h1 : σ.length = discLen T c j := by rw [discLen, h]; rfl
  exact h1 ▸ le_trans (discLen_le_cutLength T c j) (cutLength_mono T c hj)

theorem covered_iff (T : MLTest) (c : ℕ) (τ : List Bool) (j : ℕ) :
    covered T c τ j = Bool.true ↔ ∃ j' < j, ∃ σ, discovered T c j' = some σ ∧ σ <+: τ := by
  induction j with
  | zero => simp [covered]
  | succ j ih =>
      have hstep : covered T c τ (j + 1) = coveredStep T c τ (j, covered T c τ j) := rfl
      rw [hstep, coveredStep]
      simp only [Bool.or_eq_true, ih]
      constructor
      · rintro (⟨j', hj', hσ⟩ | hlast)
        · exact ⟨j', by omega, hσ⟩
        · revert hlast
          cases hd : discovered T c j with
          | none => simp
          | some σ =>
              intro h
              exact ⟨j, by omega, σ, hd, by simpa using h⟩
      · rintro ⟨j', hj', σ, hd, hpre⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h | rfl
        · exact Or.inl ⟨j', h, σ, hd, hpre⟩
        · exact Or.inr (by rw [hd]; simpa using hpre)

theorem discovered_mem_strings {T : MLTest} {c j : ℕ} {σ : List Bool}
    (h : discovered T c j = some σ) : σ ∈ T.strings c := by
  unfold discovered at h
  by_cases hen : T.enter c ((Encodable.decode (α := List Bool) j.unpair.1).getD []) j.unpair.2
      = Bool.true
  · rw [if_pos hen] at h
    have hσ : (Encodable.decode (α := List Bool) j.unpair.1).getD [] = σ := by
      simpa using h
    refine Set.mem_setOf.2 ⟨j.unpair.2, ?_⟩
    rw [← hσ]
    exact hen
  · rw [if_neg hen] at h
    exact absurd h (by simp)

theorem pieceCond_iff {T : MLTest} {c j m : ℕ} {σ : List Bool} :
    pieceCond T c j m σ = Bool.true ↔ m < 2 ^ cutLength T c j ∧
      σ <+: BitStr.ofNat (cutLength T c j) m ∧
      covered T c (BitStr.ofNat (cutLength T c j) m) j = Bool.false := by
  simp [pieceCond, and_assoc]

theorem piece_eq_some {T : MLTest} {c j m : ℕ} {τ : List Bool} (h : piece T c j m = some τ) :
    τ = BitStr.ofNat (cutLength T c j) m ∧ m < 2 ^ cutLength T c j ∧
      covered T c τ j = Bool.false ∧ ∃ σ, discovered T c j = some σ ∧ σ <+: τ := by
  unfold piece at h
  cases hd : discovered T c j with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some σ =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      cases hcond : pieceCond T c j m σ with
      | false => rw [hcond] at h; exact absurd h (by simp)
      | true =>
          rw [hcond] at h
          obtain ⟨h1, h2, h3⟩ := pieceCond_iff.1 hcond
          have hτ : τ = BitStr.ofNat (cutLength T c j) m := by simpa using h.symm
          exact ⟨hτ, h1, hτ ▸ h3, σ, rfl, hτ ▸ h2⟩

theorem piece_length {T : MLTest} {c j m : ℕ} {τ : List Bool} (h : piece T c j m = some τ) :
    τ.length = cutLength T c j := by
  rw [(piece_eq_some h).1, BitStr.length_ofNat]

theorem cylinder_piece_subset_level {T : MLTest} {c j m : ℕ} {τ : List Bool}
    (h : piece T c j m = some τ) : cylinder τ ⊆ T.level c := by
  obtain ⟨-, -, -, σ, hd, hpre⟩ := piece_eq_some h
  intro X hX
  exact mem_openOf.2 ⟨σ, discovered_mem_strings hd, cylinder_mono hpre hX⟩

/-- Pieces of the same level attached to different indices are incomparable strings. -/
theorem piece_not_prefix {T : MLTest} {c j m j' m' : ℕ} {τ τ' : List Bool}
    (h : piece T c j m = some τ) (h' : piece T c j' m' = some τ')
    (hne : (j, m) ≠ (j', m')) (hjj : j ≤ j') : ¬ τ <+: τ' := by
  obtain ⟨hτ, hm, -, σ, hd, hpre⟩ := piece_eq_some h
  obtain ⟨hτ', hm', hcov', σ', hd', hpre'⟩ := piece_eq_some h'
  rcases eq_or_lt_of_le hjj with rfl | hlt
  · -- same discovery, different value: strings of the same length, and distinct
    have hmm : m ≠ m' := by
      intro hmm; exact hne (by rw [hmm])
    intro hp
    have hlen : τ.length = τ'.length := by rw [piece_length h, piece_length h']
    have : τ = τ' := hp.eq_of_length hlen
    exact hmm (BitStr.ofNat_inj hm hm' (by rw [← hτ, ← hτ', this]))
  · -- a later piece avoids every earlier discovery
    intro hp
    have hcov : covered T c τ' j' = Bool.true :=
      (covered_iff T c τ' j').2 ⟨j, hlt, σ, hd, hpre.trans hp⟩
    rw [hcov'] at hcov
    exact absurd hcov (by simp)

theorem piece_ne {T : MLTest} {c j m j' m' : ℕ} {τ τ' : List Bool}
    (h : piece T c j m = some τ) (h' : piece T c j' m' = some τ')
    (hne : (j, m) ≠ (j', m')) : τ ≠ τ' := by
  rcases le_total j j' with hjj | hjj
  · intro hEq
    exact piece_not_prefix h h' hne hjj (hEq ▸ List.prefix_refl τ')
  · intro hEq
    exact piece_not_prefix h' h (Ne.symm hne) hjj (hEq ▸ List.prefix_refl τ)

theorem disjoint_cylinder_piece {T : MLTest} {c j m j' m' : ℕ} {τ τ' : List Bool}
    (h : piece T c j m = some τ) (h' : piece T c j' m' = some τ') (hne : τ ≠ τ') :
    Disjoint (cylinder τ) (cylinder τ') := by
  have hidx : (j, m) ≠ (j', m') := by
    intro hEq
    apply hne
    rw [Prod.mk.injEq] at hEq
    obtain ⟨rfl, rfl⟩ := hEq
    rw [h] at h'
    simpa using h'
  rcases le_total j j' with hjj | hjj
  · exact disjoint_cylinder (by rw [piece_length h, piece_length h']; exact cutLength_mono T c hjj)
      (piece_not_prefix h h' hidx hjj)
  · exact (disjoint_cylinder
      (by rw [piece_length h, piece_length h']; exact cutLength_mono T c hjj)
      (piece_not_prefix h' h (Ne.symm hidx) hjj)).symm

------------------------------------------------------------------------
-- The total weight of the requests
------------------------------------------------------------------------

/-- The weights of finitely many pieces of level `c` add up to at most `2 ^ (-c)`. -/
theorem sum_wt_pieces_le (T : MLTest) (c : ℕ) {S : Finset (List Bool)}
    (hS : ∀ τ ∈ S, ∃ j m, piece T c j m = some τ) :
    ∑ τ ∈ S, wt τ.length ≤ wt c := by
  have hdisj : ∀ τ ∈ S, ∀ τ' ∈ S, τ ≠ τ' → Disjoint (cylinder τ) (cylinder τ') := by
    intro τ hτ τ' hτ' hne
    obtain ⟨j, m, h⟩ := hS τ hτ
    obtain ⟨j', m', h'⟩ := hS τ' hτ'
    exact disjoint_cylinder_piece h h' hne
  have hsub : ∀ τ ∈ S, cylinder τ ⊆ T.level c := by
    intro τ hτ
    obtain ⟨j, m, h⟩ := hS τ hτ
    exact cylinder_piece_subset_level h
  have hmain : ∑ τ ∈ S, (2 : ENNReal)⁻¹ ^ τ.length ≤ (2 : ENNReal)⁻¹ ^ c :=
    le_trans (sum_two_inv_pow_length_le hdisj hsub) (T.measure_level_le c)
  have hL : ∑ τ ∈ S, (2 : ENNReal)⁻¹ ^ τ.length = ENNReal.ofReal (∑ τ ∈ S, wt τ.length) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun τ _ => le_of_lt (wt_pos _)]
    exact Finset.sum_congr rfl fun τ _ => by rw [ennreal_two_inv_pow]; rfl
  rw [hL, ennreal_two_inv_pow] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (le_of_lt (wt_pos c))).1 hmain

theorem wtOpt_testReq_eq {T : MLTest} {i : ℕ} {τ : List Bool} (h : pieceOf T i = some τ) :
    wtOpt (testReq T i) = wt (τ.length - i.unpair.1) := by
  rw [testReq, h]
  rfl

theorem testReq_eq_none {T : MLTest} {i : ℕ} (h : pieceOf T i = none) : testReq T i = none := by
  rw [testReq, h]
  rfl

/-- Pieces attached to different indices of the same level are different strings. -/
theorem pieceOf_inj {T : MLTest} {i i' : ℕ} {τ : List Bool} (hk : i.unpair.1 = i'.unpair.1)
    (h : pieceOf T i = some τ) (h' : pieceOf T i' = some τ) : i = i' := by
  by_contra hne
  have hidx : (i.unpair.2.unpair.1, i.unpair.2.unpair.2)
      ≠ (i'.unpair.2.unpair.1, i'.unpair.2.unpair.2) := by
    intro hEq
    rw [Prod.mk.injEq] at hEq
    apply hne
    have h2 : i.unpair.2 = i'.unpair.2 := by
      rw [← Nat.pair_unpair i.unpair.2, ← Nat.pair_unpair i'.unpair.2, hEq.1, hEq.2]
    rw [← Nat.pair_unpair i, ← Nat.pair_unpair i', hk, h2]
  have hp : piece T (2 * i.unpair.1 + 2) i.unpair.2.unpair.1 i.unpair.2.unpair.2 = some τ := h
  have hp' : piece T (2 * i'.unpair.1 + 2) i'.unpair.2.unpair.1 i'.unpair.2.unpair.2 = some τ := h'
  rw [← hk] at hp'
  exact piece_ne hp hp' hidx rfl

theorem sum_wtOpt_testReq_level_le (T : MLTest) (k : ℕ) {G : Finset ℕ}
    (hG : ∀ i ∈ G, i.unpair.1 = k) : ∑ i ∈ G, wtOpt (testReq T i) ≤ wt (k + 2) := by
  classical
  set G' := G.filter (fun i => pieceOf T i ≠ none) with hG'
  have hsum : ∑ i ∈ G, wtOpt (testReq T i) = ∑ i ∈ G', wtOpt (testReq T i) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i hi hi'
    simp only [Finset.mem_filter, not_and, not_not] at hi'
    rw [testReq_eq_none (hi' hi)]
    rfl
  set f : ℕ → List Bool := fun i => (pieceOf T i).getD [] with hf
  have hpiece : ∀ i ∈ G', pieceOf T i = some (f i) := by
    intro i hi
    simp only [hG', Finset.mem_filter] at hi
    obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.1 hi.2
    rw [hτ, hf]
    simp [hτ]
  have hinj : ∀ i ∈ G', ∀ i' ∈ G', f i = f i' → i = i' := by
    intro i hi i' hi' heq
    have h1 := hpiece i hi
    have h2 := hpiece i' hi'
    rw [heq] at h1
    exact pieceOf_inj
      (by rw [hG i (Finset.mem_filter.1 hi).1, hG i' (Finset.mem_filter.1 hi').1]) h1 h2
  have hlen : ∀ i ∈ G', 2 * k + 2 ≤ (f i).length := by
    intro i hi
    have h1 := hpiece i hi
    have hk := hG i (Finset.mem_filter.1 hi).1
    rw [pieceOf, hk] at h1
    rw [piece_length h1]
    exact le_cutLength T (2 * k + 2) _
  have himg : ∀ τ ∈ G'.image f, ∃ j m, piece T (2 * k + 2) j m = some τ := by
    intro τ hτ
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hτ
    have h1 := hpiece i hi
    have hk := hG i (Finset.mem_filter.1 hi).1
    rw [pieceOf, hk] at h1
    exact ⟨_, _, h1⟩
  have hstep : ∀ i ∈ G', wtOpt (testReq T i) = (2 : ℝ) ^ k * wt (f i).length := by
    intro i hi
    have hk := hG i (Finset.mem_filter.1 hi).1
    rw [wtOpt_testReq_eq (hpiece i hi), hk]
    have h2 : k ≤ (f i).length := le_trans (by omega) (hlen i hi)
    unfold wt
    have hsplit : ((2 : ℝ)⁻¹) ^ (f i).length
        = ((2 : ℝ)⁻¹) ^ k * ((2 : ℝ)⁻¹) ^ ((f i).length - k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit, ← mul_assoc, show (2 : ℝ) ^ k * ((2 : ℝ)⁻¹) ^ k = 1 by
      rw [← mul_pow]; norm_num, one_mul]
  calc ∑ i ∈ G, wtOpt (testReq T i) = ∑ i ∈ G', wtOpt (testReq T i) := hsum
    _ = ∑ i ∈ G', (2 : ℝ) ^ k * wt (f i).length := Finset.sum_congr rfl hstep
    _ = (2 : ℝ) ^ k * ∑ i ∈ G', wt (f i).length := by rw [Finset.mul_sum]
    _ = (2 : ℝ) ^ k * ∑ τ ∈ G'.image f, wt τ.length := by rw [Finset.sum_image hinj]
    _ ≤ (2 : ℝ) ^ k * wt (2 * k + 2) := by
        have := sum_wt_pieces_le T (2 * k + 2) himg
        have hpos : (0 : ℝ) < 2 ^ k := by positivity
        exact mul_le_mul_of_nonneg_left this (le_of_lt hpos)
    _ = wt (k + 2) := by
        unfold wt
        rw [show 2 * k + 2 = k + (k + 2) by ring, pow_add, ← mul_assoc,
          show (2 : ℝ) ^ k * ((2 : ℝ)⁻¹) ^ k = 1 by rw [← mul_pow]; norm_num, one_mul]

/-- The requests of a test have total weight at most one. -/
theorem sum_wtOpt_testReq_le (T : MLTest) (F : Finset ℕ) :
    ∑ i ∈ F, wtOpt (testReq T i) ≤ 1 := by
  classical
  set K := F.image (fun i => i.unpair.1) with hK
  have hfib : ∑ k ∈ K, ∑ i ∈ F.filter (fun i => i.unpair.1 = k), wtOpt (testReq T i)
      = ∑ i ∈ F, wtOpt (testReq T i) :=
    Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
  rw [← hfib]
  have hbound : ∀ k ∈ K,
      ∑ i ∈ F.filter (fun i => i.unpair.1 = k), wtOpt (testReq T i) ≤ wt (k + 2) :=
    fun k _ => sum_wtOpt_testReq_level_le T k fun i hi => (Finset.mem_filter.1 hi).2
  refine le_trans (Finset.sum_le_sum hbound) ?_
  obtain ⟨N, hN⟩ := K.exists_nat_subset_range
  have hmono : ∑ k ∈ K, wt (k + 2) ≤ ∑ k ∈ Finset.range N, wt (k + 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg hN fun i _ _ => le_of_lt (wt_pos _)
  exact le_trans hmono (le_trans (sum_wt_succ_succ_le N) (by norm_num))

------------------------------------------------------------------------
-- Computability of the request stream
------------------------------------------------------------------------

theorem computable₂_and : Computable₂ fun a b : Bool => a && b := Primrec₂.to_comp Primrec.and

theorem computable₂_or : Computable₂ fun a b : Bool => a || b := Primrec₂.to_comp Primrec.or

theorem computable₂_natMax : Computable₂ fun a b : ℕ => max a b :=
  Primrec₂.to_comp Primrec.nat_max

theorem computable₂_natLt : Computable₂ fun a b : ℕ => decide (a < b) :=
  Primrec₂.to_comp Primrec.nat_lt.decide

theorem computable₂_natPow : Computable₂ fun a b : ℕ => a ^ b :=
  Primrec₂.to_comp (Primrec₂.unpaired'.1 Nat.Primrec.pow)

theorem computable₂_isPrefixB : Computable₂ BitStr.isPrefixB :=
  Primrec₂.to_comp BitStr.primrec_isPrefixB

theorem computable₂_ofNat : Computable₂ BitStr.ofNat := Primrec₂.to_comp BitStr.primrec_ofNat

/-!
The next few lemmas are the *applied* forms of the basic operations.  Composing with
`Computable₂.comp` directly at a use site forces the elaborator to unfold the arguments, which is
prohibitively expensive for the recursively defined `KC.cutLength` and `KC.covered`; stating the
composition once for an abstract computable argument avoids that.
-/

section Apply

variable {α : Type} [Primcodable α]

theorem comp_and {f g : α → Bool} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f a && g a := Computable₂.comp computable₂_and hf hg

theorem comp_or {f g : α → Bool} (hf : Computable f) (hg : Computable g) :
    Computable fun a => f a || g a := Computable₂.comp computable₂_or hf hg

theorem comp_not {f : α → Bool} (hf : Computable f) : Computable fun a => !f a :=
  (Primrec.to_comp Primrec.not).comp hf

theorem comp_max {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => max (f a) (g a) := Computable₂.comp computable₂_natMax hf hg

theorem comp_ltB {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => decide (f a < g a) := Computable₂.comp computable₂_natLt hf hg

theorem comp_pow2 {f : α → ℕ} (hf : Computable f) : Computable fun a => 2 ^ f a :=
  Computable₂.comp computable₂_natPow (Computable.const 2) hf

theorem comp_isPrefixB {f g : α → List Bool} (hf : Computable f) (hg : Computable g) :
    Computable fun a => BitStr.isPrefixB (f a) (g a) :=
  Computable₂.comp computable₂_isPrefixB hf hg

theorem comp_ofNat {f g : α → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable fun a => BitStr.ofNat (f a) (g a) := Computable₂.comp computable₂_ofNat hf hg

end Apply

theorem computable_discovered (T : MLTest) : Computable₂ (discovered T) := by
  have hσ : Computable fun p : ℕ × ℕ =>
      (Encodable.decode (α := List Bool) p.2.unpair.1).getD [] :=
    Primrec.to_comp (Primrec.option_getD.comp
      (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
      (Primrec.const []))
  have hs : Computable fun p : ℕ × ℕ => p.2.unpair.2 :=
    Primrec.to_comp (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have harg : Computable fun p : ℕ × ℕ =>
      ((p.1, (Encodable.decode (α := List Bool) p.2.unpair.1).getD [], p.2.unpair.2) :
        ℕ × List Bool × ℕ) :=
    Computable.fst.pair (hσ.pair hs)
  have hen : Computable fun p : ℕ × ℕ =>
      T.enter p.1 ((Encodable.decode (α := List Bool) p.2.unpair.1).getD []) p.2.unpair.2 :=
    T.enter_computable.comp harg
  refine (Computable.cond hen (Computable.option_some.comp hσ) (Computable.const none)).of_eq
    fun p => ?_
  unfold discovered
  cases h : T.enter p.1 ((Encodable.decode (α := List Bool) p.2.unpair.1).getD []) p.2.unpair.2 <;>
    simp

theorem computable_discLen (T : MLTest) : Computable₂ (discLen T) :=
  Computable.option_getD
    (Computable.option_map (computable_discovered T)
      (Primrec.to_comp (Primrec.list_length.comp Primrec.snd)))
    (Computable.const 0)

theorem computable_cutLength (T : MLTest) : Computable₂ (cutLength T) := by
  have hc : Computable fun p : ℕ × ℕ => p.1 := Computable.fst
  have hzero : Computable fun _ : ℕ × ℕ => (0 : ℕ) := Computable.const 0
  have hbase : Computable fun p : ℕ × ℕ => max p.1 (discLen T p.1 0) :=
    comp_max hc (Computable₂.comp (computable_discLen T) hc hzero)
  have hstep : Computable₂ fun (p : ℕ × ℕ) (q : ℕ × ℕ) => cutStep T p.1 q := by
    have h1 : Computable fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.2 :=
      Computable.snd.comp Computable.snd
    have hc' : Computable fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.1.1 :=
      Computable.fst.comp Computable.fst
    have hsucc : Computable fun x : (ℕ × ℕ) × (ℕ × ℕ) => x.2.1 + 1 :=
      Primrec.to_comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
    have h2 : Computable fun x : (ℕ × ℕ) × (ℕ × ℕ) => discLen T x.1.1 (x.2.1 + 1) :=
      Computable₂.comp (computable_discLen T) hc' hsucc
    have hmax : Computable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
        max x.2.2 (discLen T x.1.1 (x.2.1 + 1)) :=
      comp_max h1 h2
    exact hmax.of_eq fun x => rfl
  exact (Computable.nat_rec Computable.snd hbase hstep).of_eq fun p => rfl

theorem computable_covered (T : MLTest) :
    Computable₂ fun (p : ℕ × List Bool) (j : ℕ) => covered T p.1 p.2 j := by
  have hstep : Computable₂ fun (p : (ℕ × List Bool) × ℕ) (q : ℕ × Bool) =>
      coveredStep T p.1.1 p.1.2 q := by
    have hprev : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.2.2 :=
      Computable.snd.comp Computable.snd
    have hc : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.1.1.1 :=
      Computable.fst.comp (Computable.fst.comp Computable.fst)
    have hτ : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.1.1.2 :=
      Computable.snd.comp (Computable.fst.comp Computable.fst)
    have hk : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) => x.2.1 :=
      Computable.fst.comp Computable.snd
    have hdisc : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
        discovered T x.1.1.1 x.2.1 :=
      Computable₂.comp (computable_discovered T) hc hk
    have hpre : Computable₂ fun (x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool)) (σ : List Bool) =>
        BitStr.isPrefixB σ x.1.1.2 := by
      have hs : Computable fun y : (((ℕ × List Bool) × ℕ) × (ℕ × Bool)) × List Bool => y.2 :=
        Computable.snd
      have ht : Computable fun y : (((ℕ × List Bool) × ℕ) × (ℕ × Bool)) × List Bool =>
          y.1.1.1.2 := hτ.comp Computable.fst
      exact Computable₂.comp computable₂_isPrefixB hs ht
    have hmap : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
        (discovered T x.1.1.1 x.2.1).map (fun σ => BitStr.isPrefixB σ x.1.1.2) :=
      Computable.option_map hdisc hpre
    have hgetD : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
        ((discovered T x.1.1.1 x.2.1).map (fun σ => BitStr.isPrefixB σ x.1.1.2)).getD Bool.false :=
      Computable.option_getD hmap (Computable.const Bool.false)
    have hor : Computable fun x : ((ℕ × List Bool) × ℕ) × (ℕ × Bool) =>
        x.2.2 || ((discovered T x.1.1.1 x.2.1).map
          (fun σ => BitStr.isPrefixB σ x.1.1.2)).getD Bool.false :=
      comp_or hprev hgetD
    exact hor.of_eq fun x => rfl
  exact (Computable.nat_rec Computable.snd (Computable.const Bool.false) hstep).of_eq
    fun p => rfl

theorem comp_cutLength {α : Type} [Primcodable α] (T : MLTest) {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable fun a => cutLength T (f a) (g a) :=
  Computable₂.comp (computable_cutLength T) hf hg

theorem comp_covered {α : Type} [Primcodable α] (T : MLTest) {f : α → ℕ} {g : α → List Bool}
    {h : α → ℕ} (hf : Computable f) (hg : Computable g) (hh : Computable h) :
    Computable fun a => covered T (f a) (g a) (h a) :=
  (Computable₂.comp (computable_covered T) (hf.pair hg) hh).of_eq fun _ => rfl

theorem computable_piece (T : MLTest) :
    Computable₂ fun (p : ℕ × ℕ) (m : ℕ) => piece T p.1 p.2 m := by
  have hc : Computable fun x : (ℕ × ℕ) × ℕ => x.1.1 := Computable.fst.comp Computable.fst
  have hj : Computable fun x : (ℕ × ℕ) × ℕ => x.1.2 := Computable.snd.comp Computable.fst
  have hm : Computable fun x : (ℕ × ℕ) × ℕ => x.2 := Computable.snd
  have hdisc : Computable fun x : (ℕ × ℕ) × ℕ => discovered T x.1.1 x.1.2 :=
    Computable₂.comp (computable_discovered T) hc hj
  have hbody : Computable₂ fun (x : (ℕ × ℕ) × ℕ) (σ : List Bool) =>
      (bif pieceCond T x.1.1 x.1.2 x.2 σ then some (BitStr.ofNat (cutLength T x.1.1 x.1.2) x.2)
        else none) := by
    have hc' : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool => y.1.1.1 := hc.comp Computable.fst
    have hj' : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool => y.1.1.2 := hj.comp Computable.fst
    have hm' : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool => y.1.2 := hm.comp Computable.fst
    have hs : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool => y.2 := Computable.snd
    have hN : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool => cutLength T y.1.1.1 y.1.1.2 :=
      comp_cutLength T hc' hj'
    have hτ : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool =>
        BitStr.ofNat (cutLength T y.1.1.1 y.1.1.2) y.1.2 := comp_ofNat hN hm'
    have hA : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool =>
        decide (y.1.2 < 2 ^ cutLength T y.1.1.1 y.1.1.2) := comp_ltB hm' (comp_pow2 hN)
    have hB : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool =>
        BitStr.isPrefixB y.2 (BitStr.ofNat (cutLength T y.1.1.1 y.1.1.2) y.1.2) :=
      comp_isPrefixB hs hτ
    have hcov : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool =>
        covered T y.1.1.1 (BitStr.ofNat (cutLength T y.1.1.1 y.1.1.2) y.1.2) y.1.1.2 :=
      comp_covered T hc' hτ hj'
    have hcond : Computable fun y : ((ℕ × ℕ) × ℕ) × List Bool =>
        pieceCond T y.1.1.1 y.1.1.2 y.1.2 y.2 :=
      (comp_and (comp_and hA hB) (comp_not hcov)).of_eq fun y => rfl
    exact Computable.cond hcond (Computable.option_some.comp hτ) (Computable.const none)
  exact (Computable.option_bind hdisc hbody).of_eq fun x => rfl

theorem computable_pieceOf (T : MLTest) : Computable (pieceOf T) := by
  have harg : Computable fun i : ℕ =>
      (((2 * i.unpair.1 + 2, i.unpair.2.unpair.1), i.unpair.2.unpair.2) : (ℕ × ℕ) × ℕ) := by
    have hk : Primrec fun i : ℕ => 2 * i.unpair.1 + 2 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.unpair))
        (Primrec.const 2)
    have hj : Primrec fun i : ℕ => i.unpair.2.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    have hm : Primrec fun i : ℕ => i.unpair.2.unpair.2 :=
      Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
    exact Primrec.to_comp ((hk.pair hj).pair hm)
  have hcomp : Computable fun i : ℕ =>
      piece T (2 * i.unpair.1 + 2) i.unpair.2.unpair.1 i.unpair.2.unpair.2 :=
    Computable.comp (computable_piece T) harg
  exact hcomp.of_eq fun i => rfl

theorem computable_testReq (T : MLTest) : Computable (testReq T) := by
  have hmap : Computable₂ fun (i : ℕ) (τ : List Bool) =>
      ((τ.length - i.unpair.1, Encodable.encode τ) : ℕ × ℕ) :=
    Primrec₂.to_comp ((Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))).pair
      (Primrec.encode.comp Primrec.snd))
  exact Computable.option_map (computable_pieceOf T) hmap


------------------------------------------------------------------------
-- Every caught sequence has a compressed prefix
------------------------------------------------------------------------

/-- Every sequence caught by level `2 * k + 2` of a test has a prefix which is requested with a
saving of `k` bits. -/
theorem exists_piece_prefix {T : MLTest} {X : ℕ → Bool} {k : ℕ}
    (h : X ∈ T.level (2 * k + 2)) :
    ∃ i N, testReq T i = some (N - k, Encodable.encode (prefixList X N)) ∧ k ≤ N := by
  classical
  set c := 2 * k + 2 with hc
  obtain ⟨σ, hσ, hXσ⟩ := mem_openOf.1 h
  obtain ⟨s, hs⟩ := Set.mem_setOf.1 hσ
  have hdisc₀ : discovered T c (Nat.pair (Encodable.encode σ) s) = some σ := by
    unfold discovered
    rw [Nat.unpair_pair]
    simp only [Encodable.encodek, Option.getD_some]
    rw [if_pos hs]
  have hP : ∃ j, ∃ σ' : List Bool, discovered T c j = some σ' ∧ X ∈ cylinder σ' :=
    ⟨_, σ, hdisc₀, hXσ⟩
  obtain ⟨σ₁, hd₁, hX₁⟩ := Nat.find_spec hP
  set j := Nat.find hP with hj
  set N := cutLength T c j with hN
  have hlenσ₁ : σ₁.length ≤ N := length_le_cutLength hd₁ le_rfl
  have hpre : σ₁ <+: prefixList X N := by
    have hseg := prefixList_eq_of_mem_cylinder hX₁
    exact hseg ▸ prefixList_prefix (X := X) hlenσ₁
  have hcov : covered T c (prefixList X N) j = Bool.false := by
    rcases Bool.eq_false_or_eq_true (covered T c (prefixList X N) j) with h1 | h0
    · exfalso
      obtain ⟨j', hj', σ', hd', hpre'⟩ := (covered_iff T c (prefixList X N) j).1 h1
      exact Nat.find_min hP hj' ⟨σ', hd', cylinder_mono hpre' (mem_cylinder_prefixList X N)⟩
    · exact h0
  have hlenτ : (prefixList X N).length = N := prefixList_length X N
  have hofNat : BitStr.ofNat N (BitStr.toNat (prefixList X N)) = prefixList X N := by
    have hb := BitStr.ofNat_toNat (prefixList X N)
    rwa [hlenτ] at hb
  have hm : BitStr.toNat (prefixList X N) < 2 ^ N := by
    have hb := BitStr.toNat_lt (prefixList X N)
    rwa [hlenτ] at hb
  have hpiece : piece T c j (BitStr.toNat (prefixList X N)) = some (prefixList X N) := by
    have hcond : pieceCond T c j (BitStr.toNat (prefixList X N)) σ₁ = Bool.true :=
      pieceCond_iff.2 (by rw [← hN, hofNat]; exact ⟨hm, hpre, hcov⟩)
    unfold piece
    rw [hd₁, Option.bind_some, hcond, cond_true, ← hN, hofNat]
  refine ⟨Nat.pair k (Nat.pair j (BitStr.toNat (prefixList X N))), N, ?_, ?_⟩
  · have hpo : pieceOf T (Nat.pair k (Nat.pair j (BitStr.toNat (prefixList X N))))
        = some (prefixList X N) := by
      unfold pieceOf
      rw [Nat.unpair_pair, Nat.unpair_pair]
      exact hpiece
    rw [testReq, hpo, Nat.unpair_pair]
    simp [hlenτ]
  · have hcN : c ≤ N := le_cutLength T c j
    omega

------------------------------------------------------------------------
-- The theorem
------------------------------------------------------------------------

/-- **Chaitin's `Ω` is Martin-Löf random.** -/
theorem mlRandom_omegaSeq : MLRandom omegaSeq := by
  obtain ⟨c₀, hc₀⟩ := exists_const_le_KU_omegaPrefix
  intro T
  obtain ⟨c₁, hc₁⟩ := exists_const_KU_le (computable_testReq T) (sum_wtOpt_testReq_le T)
  refine ⟨2 * (c₀ + c₁ + 1) + 2, fun hmem => ?_⟩
  obtain ⟨i, N, hreq, hkN⟩ := exists_piece_prefix (k := c₀ + c₁ + 1) hmem
  have h1 := hc₁ i (N - (c₀ + c₁ + 1)) _ hreq
  have h2 := hc₀ N
  omega

end KC
