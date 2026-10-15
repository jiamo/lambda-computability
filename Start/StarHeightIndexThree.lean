import Start.StarHeightResetCount
import Start.StarHeightGroups

/-!
# Generalized star height at most two for groups with an abelian normal subgroup of index 3

* `bmod_height`: for a prefix code `E` whose star has height at most one and a subcode `L ⊆ E`
  of height at most one, the words of `E∗` whose factorization has a number of `L`-blocks
  congruent to `r` modulo `m` form a language of height at most two.  The second star counts
  blocks.
* `kstar_firstReturn_group`, `mem_remainder_group`: for a morphism into a group, `(firstReturn ψ)∗`
  is the fiber over `1`, and the remainder of `firstReturn ψ` is the set of words none of whose
  nonempty prefixes maps to `1`.
* `height_two_of_abelian_index_three`: if `G` has an abelian normal subgroup `N` of index 3, every
  language recognized by a morphism into `G` has generalized star height at most two.
  The blocks are the first returns to `N`; inside a block the walk in `G ⧸ N ≅ Z/3` is driven by a
  reset automaton (`Start/StarHeightResetCount.lean`), and the value of a block in the abelian `N`
  depends only on how often each letter is read in each state, modulo `|N|`.
* `height_two_alternatingGroup_four`: the corollary for `A₄` and its Klein four subgroup.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

variable {Alphabet : Type u}

/-! ### Counting blocks of a prefix code -/

section BlockCount

open Classical

variable (E L : Language Alphabet)

/-- The number of blocks of `es` lying in `L`. -/
noncomputable def bcount (es : List (List Alphabet)) : ℕ := es.countP (fun e => e ∈ L)

/-- Words of `E∗` with exactly `k` blocks in `L`. -/
def bwords (k : ℕ) : Language Alphabet :=
  {x | ∃ es, AllIn E es ∧ es.flatten = x ∧ bcount L es = k}

/-- Words of `E∗` whose number of blocks in `L` is `r` modulo `m`. -/
def bmod (m r : ℕ) : Language Alphabet :=
  {x | ∃ es, AllIn E es ∧ es.flatten = x ∧ bcount L es % m = r}

/-- Words of `E∗` with no block in `L`, followed by a block in `L`. -/
def bfirst : Language Alphabet := bwords E L 0 * L

lemma countP_split {β : Type*} (p : β → Bool) :
    ∀ (l : List β) (k : ℕ), l.countP p = k + 1 →
      ∃ l₁ x l₂, l = l₁ ++ x :: l₂ ∧ l₁.countP p = 0 ∧ p x ∧ l₂.countP p = k
  | [], k, h => by simp at h
  | b :: l, k, h => by
      by_cases hb : p b
      · refine ⟨[], b, l, rfl, rfl, hb, ?_⟩
        rw [List.countP_cons_of_pos hb] at h
        omega
      · rw [List.countP_cons_of_neg hb] at h
        obtain ⟨l₁, x, l₂, rfl, h1, hx, h2⟩ := countP_split p l k h
        exact ⟨b :: l₁, x, l₂, rfl, by rw [List.countP_cons_of_neg hb]; exact h1, hx, h2⟩

variable {E L}

theorem bwords_succ (hL : L ≤ E) (k : ℕ) : bwords E L (k + 1) = bfirst E L * bwords E L k := by
  ext x
  constructor
  · rintro ⟨es, hes, rfl, hk⟩
    obtain ⟨es₁, e, es₂, rfl, h1, he, h2⟩ := countP_split _ es k hk
    refine Language.mem_mul.mpr ⟨es₁.flatten ++ e, Language.mem_mul.mpr
      ⟨es₁.flatten, ⟨es₁, fun f hf => hes f (by simp [hf]), rfl, h1⟩, e,
        by simpa using he, rfl⟩, es₂.flatten, ⟨es₂, fun f hf => hes f (by simp [hf]), rfl, h2⟩,
      by simp⟩
  · intro hx
    obtain ⟨yl, hyl, z, ⟨es₂, hes₂, rfl, h2⟩, rfl⟩ := Language.mem_mul.mp hx
    obtain ⟨y, ⟨es₁, hes₁, rfl, h1⟩, l, hl, rfl⟩ := Language.mem_mul.mp hyl
    refine ⟨es₁ ++ l :: es₂, ?_, by simp, ?_⟩
    · intro f hf
      rcases List.mem_append.1 hf with hf | hf
      · exact hes₁ f hf
      · rcases List.mem_cons.1 hf with rfl | hf
        · exact hL hl
        · exact hes₂ f hf
    · unfold bcount at h1 h2 ⊢
      rw [List.countP_append, List.countP_cons_of_pos (by simpa using hl), h1, h2]
      omega

theorem bwords_eq_pow (hL : L ≤ E) (k : ℕ) : bwords E L k = bfirst E L ^ k * bwords E L 0 := by
  induction k with
  | zero => rw [pow_zero, one_mul]
  | succ k ih => rw [bwords_succ hL, ih, pow_succ', mul_assoc]

theorem bmod_eq (hL : L ≤ E) {m r : ℕ} (hr : r < m) :
    bmod E L m r = (bfirst E L ^ m)∗ * (bfirst E L ^ r * bwords E L 0) := by
  ext x
  constructor
  · rintro ⟨es, hes, rfl, hk⟩
    have hmem : es.flatten ∈ bwords E L (m * (bcount L es / m) + r) :=
      ⟨es, hes, rfl, by rw [← hk]; exact (Nat.div_add_mod _ _).symm⟩
    rw [bwords_eq_pow hL, pow_add, pow_mul, mul_assoc] at hmem
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp hmem
    refine Language.mem_mul.mpr ⟨x, ?_, y, hy, hxy⟩
    rw [Language.kstar_eq_iSup_pow]
    exact Language.mem_iSup.mpr ⟨_, hx⟩
  · intro hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hu
    rw [Language.kstar_eq_iSup_pow] at hx
    obtain ⟨j, hj⟩ := Language.mem_iSup.mp hx
    have hmem : x ++ y ∈ (bfirst E L ^ m) ^ j * (bfirst E L ^ r * bwords E L 0) :=
      Language.mem_mul.mpr ⟨x, hj, y, hy, rfl⟩
    rw [← mul_assoc, ← pow_mul, ← pow_add, ← bwords_eq_pow hL] at hmem
    obtain ⟨es, hes, hflat, hk⟩ := hmem
    exact ⟨es, hes, hflat, by rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]⟩

theorem bwords_zero_eq (hE : PrefixCode E) (hL : L ≤ E) :
    bwords E L 0 = E∗ ⊓ (E∗ * L * ⊤)ᶜ := by
  ext x
  constructor
  · rintro ⟨es, hes, rfl, h0⟩
    refine ⟨Language.mem_kstar.mpr ⟨es, rfl, hes⟩, ?_⟩
    intro hm
    obtain ⟨yl, hyl, z, _, hxz⟩ := Language.mem_mul.mp hm
    obtain ⟨y, hy, l, hl, rfl⟩ := Language.mem_mul.mp hyl
    obtain ⟨fs, rfl, hfs⟩ := Language.mem_kstar.mp hy
    have hp := flatten_prefix hE hfs hes ⟨l ++ z, by rw [← hxz]; simp⟩
    obtain ⟨gs, rfl⟩ := hp
    have hgs : gs.flatten = l ++ z := by
      apply List.append_cancel_left (as := fs.flatten)
      rw [← List.flatten_append, ← hxz, List.append_assoc]
    cases gs with
    | nil =>
        obtain ⟨hl0, -⟩ : l = [] ∧ z = [] := by simpa using hgs.symm
        exact hE.1 (hl0 ▸ hL hl)
    | cons g gs =>
        have hg : g ∈ E := hes g (by simp)
        have hgl : g = l := by
          have h1 : g <+: l ++ z := ⟨gs.flatten, by rw [← hgs]; simp⟩
          have h2 : l <+: l ++ z := List.prefix_append _ _
          rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
          · exact hE.2 g hg l (hL hl) h
          · exact (hE.2 l (hL hl) g hg h).symm
        have : bcount L (fs ++ g :: gs) ≠ 0 := by
          unfold bcount
          rw [List.countP_append, List.countP_cons_of_pos (by simpa [hgl] using hl)]
          omega
        exact this h0
  · rintro ⟨hx, hn⟩
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hx
    refine ⟨es, hes, rfl, ?_⟩
    unfold bcount
    rw [List.countP_eq_zero]
    intro e he hL'
    obtain ⟨es₁, es₂, rfl⟩ := List.append_of_mem he
    apply hn
    refine Language.mem_mul.mpr ⟨es₁.flatten ++ e, Language.mem_mul.mpr
      ⟨es₁.flatten, Language.mem_kstar.mpr ⟨es₁, rfl, fun f hf => hes f (by simp [hf])⟩,
        e, by simpa using hL', rfl⟩, es₂.flatten, trivial, by simp⟩

/-- **Counting blocks modulo `m` at height two.** -/
theorem bmod_height (hE : PrefixCode E) (hL : L ≤ E) (hEs : HasHeightAtMost E∗ 1)
    (hLh : HasHeightAtMost L 1) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (bmod E L m r) 2 := by
  rw [bmod_eq hL hr]
  have h0 : HasHeightAtMost (bwords E L 0) 1 := by
    rw [bwords_zero_eq hE hL]
    exact hEs.inter ((hEs.concat hLh).concat (HasHeightAtMost.top 1)).compl
  have hY : HasHeightAtMost (bfirst E L) 1 := h0.concat hLh
  exact (pow_height hY m).star.concat ((pow_height hY r).concat h0 |>.mono (by omega))

end BlockCount

/-! ### First returns in a group -/

section FirstReturnGroup

variable {H : Type} [Group H] (ψ : FreeMonoid Alphabet →* H)

theorem kstar_firstReturn_group :
    (firstReturn ψ)∗ = ({w | ψ (FreeMonoid.ofList w) = 1} : Language Alphabet) := by
  ext w
  constructor
  · intro hw
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hw
    exact firstReturn_T es hes
  · intro hw
    change ψ (FreeMonoid.ofList w) = 1 at hw
    induction hlen : w.length using Nat.strong_induction_on generalizing w with
    | _ n ih =>
    classical
    rcases w.eq_nil_or_concat' with rfl | ⟨_, _, _⟩
    · exact Language.nil_mem_kstar _
    have hex : ∃ k, 0 < k ∧ k ≤ w.length ∧ ψ (FreeMonoid.ofList (w.take k)) = 1 := by
      refine ⟨w.length, ?_, le_rfl, by rw [List.take_length]; exact hw⟩
      rename_i v b hv
      rw [hv]; simp
    obtain ⟨k, ⟨hk0, hkl, hk1⟩, hmin⟩ : ∃ k, (0 < k ∧ k ≤ w.length ∧
        ψ (FreeMonoid.ofList (w.take k)) = 1) ∧
        ∀ j, 0 < j → j < k → ψ (FreeMonoid.ofList (w.take j)) ≠ 1 :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj0 hjk hj1 => Nat.find_min hex hjk
        ⟨hj0, by have := (Nat.find_spec hex).2.1; omega, hj1⟩⟩
    have hfr : w.take k ∈ firstReturn ψ := by
      refine ⟨?_, hk1, ?_⟩
      · intro h
        have := congrArg List.length h
        rw [List.length_take, List.length_nil] at this
        omega
      · intro p hp hpne hpw
        have hle : p.length ≤ k := hp.length_le.trans (List.length_take_le _ _)
        have hpk : p = w.take p.length := by
          have h := List.prefix_iff_eq_take.1 hp
          rw [List.take_take, Nat.min_eq_left hle] at h
          exact h
        have hlt : p.length < k := lt_of_le_of_ne hle (fun h => hpw (by rw [hpk, h]))
        rw [hpk]
        exact hmin _ (List.length_pos_of_ne_nil hpne) hlt
    have hrest : ψ (FreeMonoid.ofList (w.drop k)) = 1 := by
      have h := hw
      rw [← List.take_append_drop k w, FreeMonoid.ofList_append, map_mul, hk1, one_mul] at h
      exact h
    have hlt : (w.drop k).length < n := by simp; omega
    have hr := ih _ hlt (w.drop k) hrest rfl
    rw [← List.take_append_drop k w]
    obtain ⟨es, hes, hes'⟩ := Language.mem_kstar.mp hr
    exact Language.mem_kstar.mpr ⟨w.take k :: es, by simp [hes], by
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hfr
      · exact hes' e he⟩

theorem mem_remainder_group (w : List Alphabet) :
    w ∈ remainder (firstReturn ψ) ↔
      ∀ p, p <+: w → p ≠ [] → ψ (FreeMonoid.ofList p) ≠ 1 := by
  constructor
  · intro hw p hp hpne hp1
    have hk : p ∈ (firstReturn ψ)∗ := by rw [kstar_firstReturn_group]; exact hp1
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hk
    cases es with
    | nil => exact hpne rfl
    | cons e es =>
        exact hw e (hes e (by simp)) ((List.prefix_append e es.flatten).trans
          (by simpa using hp))
  · intro h e he hew
    exact h e hew he.1 he.2.1

end FirstReturnGroup

/-! ### Groups of order three -/

section Order3

variable {Q : Type} [Group Q]

lemma q3_cube (h3 : Nat.card Q = 3) (q : Q) : q ^ 3 = 1 := by
  rw [← h3]; exact pow_card_eq_one'

lemma q3_sq (h3 : Nat.card Q = 3) (q : Q) : q * q = q⁻¹ := by
  rw [eq_inv_iff_mul_eq_one]
  have := q3_cube h3 q
  rwa [pow_succ, pow_two] at this

lemma q3_inv_ne (h3 : Nat.card Q = 3) {q : Q} (hq : q ≠ 1) : q⁻¹ ≠ q := by
  intro h
  apply hq
  have h2 := q3_sq h3 q
  rw [h] at h2
  exact mul_eq_left.mp h2

lemma q3_cases (h3 : Nat.card Q = 3) {q : Q} (hq : q ≠ 1) (x : Q) :
    x = 1 ∨ x = q ∨ x = q⁻¹ := by
  classical
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [h3]; norm_num)
  have := Fintype.ofFinite Q
  by_contra hx
  simp only [not_or] at hx
  obtain ⟨h1, h2, h3'⟩ := hx
  have a1 : (1 : Q) ≠ q := Ne.symm hq
  have a2 : (1 : Q) ≠ q⁻¹ := Ne.symm (inv_ne_one.mpr hq)
  have a3 : (1 : Q) ≠ x := Ne.symm h1
  have a4 : q ≠ q⁻¹ := Ne.symm (q3_inv_ne h3 hq)
  have a5 : q ≠ x := Ne.symm h2
  have a6 : q⁻¹ ≠ x := Ne.symm h3'
  have hc : ({1, q, q⁻¹, x} : Finset Q).card = 4 := by
    simp [Finset.card_insert_of_notMem, a1, a2, a3, a4, a5, a6]
  have hle := Finset.card_le_univ ({1, q, q⁻¹, x} : Finset Q)
  rw [Fintype.card_eq_nat_card, h3, hc] at hle
  omega

lemma q3_comm (h3 : Nat.card Q = 3) (x y : Q) : x * y = y * x := by
  by_cases hx : x = 1
  · rw [hx, one_mul, mul_one]
  · rcases q3_cases h3 hx y with rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · rfl
    · rw [mul_inv_cancel, inv_mul_cancel]

end Order3

/-! ### The walk in `G ⧸ N` -/

section Walk

open Classical

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (T : FreeMonoid Alphabet →* G)

/-- The morphism to the quotient. -/
noncomputable def psi : FreeMonoid Alphabet →* G ⧸ N := (QuotientGroup.mk' N).comp T

/-- Coset representatives, with `rep 1 = 1`. -/
noncomputable def rep (q : G ⧸ N) : G := if q = 1 then 1 else q.out

lemma rep_one : rep N 1 = 1 := if_pos rfl

lemma mk_rep (q : G ⧸ N) : ((rep N q : G) : G ⧸ N) = q := by
  unfold rep
  split_ifs with h
  · rw [h]; rfl
  · exact QuotientGroup.out_eq' q

lemma psi_apply (w : FreeMonoid Alphabet) : psi N T w = ((T w : G) : G ⧸ N) := rfl

/-- The value of reading `a` in the state `q`. -/
noncomputable def cv (q : G ⧸ N) (a : Alphabet) : G :=
  rep N q * T (FreeMonoid.of a) * (rep N (q * psi N T (FreeMonoid.of a)))⁻¹

lemma cv_mem (q : G ⧸ N) (a : Alphabet) : cv N T q a ∈ N := by
  rw [← QuotientGroup.eq_one_iff]
  simp only [cv, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep, psi_apply]
  exact mul_inv_cancel _

/-- The pairs (state, letter) of the walk in `G ⧸ N`. -/
noncomputable def tpairs (q : G ⧸ N) : List Alphabet → List ((G ⧸ N) × Alphabet)
  | [] => []
  | b :: u => (q, b) :: tpairs (q * psi N T (FreeMonoid.of b)) u

lemma tpairs_append (q : G ⧸ N) (u w : List Alphabet) :
    tpairs N T q (u ++ w) = tpairs N T q u ++
      tpairs N T (q * psi N T (FreeMonoid.ofList u)) w := by
  induction u generalizing q with
  | nil => simp [tpairs]
  | cons b u ih =>
      simp only [List.cons_append, tpairs, ih, FreeMonoid.ofList_cons, map_mul, mul_assoc]

/-- Telescoping along the walk. -/
lemma telescope (q : G ⧸ N) (u : List Alphabet) :
    rep N q * T (FreeMonoid.ofList u) * (rep N (q * psi N T (FreeMonoid.ofList u)))⁻¹ =
      ((tpairs N T q u).map (fun p => cv N T p.1 p.2)).prod := by
  induction u generalizing q with
  | nil => simp [tpairs]
  | cons b u ih =>
      rw [tpairs, List.map_cons, List.prod_cons, ← ih]
      simp only [cv, FreeMonoid.ofList_cons, map_mul, mul_assoc, inv_mul_cancel_left]

/-- The reset automaton of the walk: letters mapping to `1` keep the state, any other letter `b`
resets it to `(ψ b)⁻¹`. -/
def KK (b : Alphabet) : Prop := psi N T (FreeMonoid.of b) = 1

noncomputable def RR (b : Alphabet) : G ⧸ N := (psi N T (FreeMonoid.of b))⁻¹

noncomputable def rpairs (q : G ⧸ N) : List Alphabet → List ((G ⧸ N) × Alphabet)
  | [] => []
  | b :: u => (q, b) :: rpairs (rstep (KK N T) (RR N T) q b) u

lemma rcount_eq_count (qs : G ⧸ N) (a : Alphabet) (q : G ⧸ N) (u : List Alphabet) :
    rcount (KK N T) (RR N T) qs a q u = (rpairs N T q u).count (qs, a) := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih =>
      simp only [rcount, rpairs, List.count_cons, ih]
      by_cases h : b = a ∧ q = qs
      · obtain ⟨rfl, rfl⟩ := h; simp; omega
      · rw [if_neg h]
        have : ¬ ((q, b) == (qs, a)) = true := by
          simp only [beq_iff_eq, Prod.mk.injEq]
          exact fun h' => h ⟨h'.2, h'.1⟩
        simp [this]

/-- While the walk avoids `1`, it is the reset automaton. -/
lemma walk_reset (h3 : Nat.card (G ⧸ N) = 3) :
    ∀ (u : List Alphabet) (q : G ⧸ N), q ≠ 1 →
      (∀ p, p <+: u → q * psi N T (FreeMonoid.ofList p) ≠ 1) →
        tpairs N T q u = rpairs N T q u ∧
          q * psi N T (FreeMonoid.ofList u) = rstate (KK N T) (RR N T) q u := by
  intro u
  induction u with
  | nil => intro q _ _; simp [tpairs, rpairs, rstate]
  | cons b u ih =>
      intro q hq hu
      have hqb : q * psi N T (FreeMonoid.of b) ≠ 1 := by
        have := hu [b] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
        simpa using this
      have hstep : rstep (KK N T) (RR N T) q b = q * psi N T (FreeMonoid.of b) := by
        unfold rstep
        split_ifs with hK
        · rw [show psi N T (FreeMonoid.of b) = 1 from hK, mul_one]
        · unfold RR
          rcases q3_cases h3 hq (psi N T (FreeMonoid.of b)) with h | h | h
          · exact absurd h hK
          · rw [h, q3_sq h3]
          · rw [h, mul_inv_cancel] at hqb; exact absurd rfl hqb
      have hu' : ∀ p, p <+: u →
          q * psi N T (FreeMonoid.of b) * psi N T (FreeMonoid.ofList p) ≠ 1 := by
        intro p hp
        have := hu (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        simpa [FreeMonoid.ofList_cons, mul_assoc] using this
      obtain ⟨h1, h2⟩ := ih _ hqb hu'
      refine ⟨?_, ?_⟩
      · simp only [tpairs, rpairs, hstep, h1]
      · rw [rstate, hstep, ← h2, FreeMonoid.ofList_cons, map_mul, mul_assoc]

/-- The subgroup `N`, commutative. -/
@[reducible] def nComm (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) : CommGroup N :=
  { (inferInstance : Group N) with
    mul_comm := fun a b => Subtype.ext (hab _ a.2 _ b.2) }

/-- `cv` as an element of `N`. -/
noncomputable def cvN (q : G ⧸ N) (a : Alphabet) : N := ⟨cv N T q a, cv_mem N T q a⟩

variable [Fintype Alphabet] [Fintype (G ⧸ N)]

/-- The value attached to residues of the counts of (state, letter) pairs. -/
noncomputable def valN (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (res : (G ⧸ N) × Alphabet → ℕ) : N :=
  letI := nComm N hab
  ∏ p : (G ⧸ N) × Alphabet, cvN N T p.1 p.2 ^ res p

omit [N.Normal] [Fintype Alphabet] [Fintype (G ⧸ N)] in
lemma pow_mod_card_N (g : N) (k : ℕ) : g ^ k = g ^ (k % Nat.card N) := by
  conv_lhs => rw [← Nat.div_add_mod k (Nat.card N), pow_add, pow_mul, pow_card_eq_one',
    one_pow, one_mul]

lemma list_prod_cv (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (l : List ((G ⧸ N) × Alphabet)) :
    (l.map (fun p => cv N T p.1 p.2)).prod =
      (valN N T hab (fun p => l.count p % Nat.card N) : G) := by
  let := nComm N hab
  have h1 : (l.map (fun p => cv N T p.1 p.2)).prod =
      ((l.map (fun p => cvN N T p.1 p.2)).prod : G) := by
    induction l with
    | nil => simp
    | cons p l ih => simp [ih, cvN]
  rw [h1, Finset.prod_list_map_count]
  unfold valN
  congr 1
  rw [Finset.prod_subset (Finset.subset_univ _)]
  · refine Finset.prod_congr rfl (fun p _ => ?_)
    convert pow_mod_card_N N (cvN N T p.1 p.2) (List.count p l) using 3
    exact lawful_beq_subsingleton _ _
  · intro p _ hp
    convert pow_zero (cvN N T p.1 p.2)
    convert List.count_eq_zero_of_not_mem (fun h => hp (List.mem_toFinset.mpr h))

end Walk

/-! ### Assembling the split -/

/-- Height two from height two of the fibers of `E∗` and height one of the fibers of the
remainder of `E`. -/
theorem height_two_of_split {M : Type} [Monoid M] [Finite M] (T : FreeMonoid Alphabet →* M)
    (E : Language Alphabet) (hE : [] ∉ E)
    (hA : ∀ d, HasHeightAtMost {w | w ∈ E∗ ∧ T (FreeMonoid.ofList w) = d} 2)
    (hB : ∀ f, HasHeightAtMost {w | w ∈ remainder E ∧ T (FreeMonoid.ofList w) = f} 1)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 := by
  classical
  let A : M → Language Alphabet := fun d => {w | w ∈ E∗ ∧ T (FreeMonoid.ofList w) = d}
  let B : M → Language Alphabet := fun f => {w | w ∈ remainder E ∧ T (FreeMonoid.ofList w) = f}
  let I := {p : M × M // p.1 * p.2 ∈ F}
  have hU : HasHeightAtMost (⨆ p : I, A p.1.1 * B p.1.2) 2 :=
    HasHeightAtMost.iSup _ (fun p => (hA p.1.1).concat ((hB p.1.2).mono (by decide)))
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      ⨆ p : I, A p.1.1 * B p.1.2 := by
    ext w
    constructor
    · intro hw
      obtain ⟨es, r, hes, hr, hwr⟩ := factor_remainder hE w
      have hdf : T (FreeMonoid.ofList es.flatten) * T (FreeMonoid.ofList r) ∈ F := by
        rw [← map_mul]
        change T (FreeMonoid.ofList (es.flatten ++ r)) ∈ F
        rw [← hwr]
        exact hw
      apply Language.mem_iSup.mpr
      refine ⟨⟨(_, _), hdf⟩, Language.mem_mul.mpr ⟨es.flatten, ?_, r, ?_, hwr.symm⟩⟩
      · exact ⟨Language.join_mem_kstar hes, rfl⟩
      · exact ⟨hr, rfl⟩
    · intro hw
      obtain ⟨p, hp⟩ := Language.mem_iSup.mp hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Language.mem_mul.mp hp
      change T (FreeMonoid.ofList a * FreeMonoid.ofList b) ∈ F
      rw [map_mul, ha.2, hb.2]
      exact p.2
  exact heq.symm ▸ hU

section Values

open Classical

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (T : FreeMonoid Alphabet →* G)

lemma T_mem_of_firstReturn {e : List Alphabet} (he : e ∈ firstReturn (psi N T)) :
    T (FreeMonoid.ofList e) ∈ N :=
  (QuotientGroup.eq_one_iff _).mp he.2.1

variable [Fintype Alphabet] [Fintype (G ⧸ N)]

/-- The residues of the counts of the reset automaton. -/
noncomputable def rres (q : G ⧸ N) (v : List Alphabet) : (G ⧸ N) × Alphabet → ℕ :=
  fun p => rcount (KK N T) (RR N T) p.1 p.2 q v % Nat.card N

lemma rpairs_prod (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (q : G ⧸ N) (v : List Alphabet) :
    ((rpairs N T q v).map (fun p => cv N T p.1 p.2)).prod = (valN N T hab (rres N T q v) : G) := by
  rw [list_prod_cv N T hab]
  congr 2
  funext p
  rw [rres, rcount_eq_count]

/-- **The value of a block.** -/
lemma block_value (h3 : Nat.card (G ⧸ N) = 3) (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    {x y : Alphabet} {v : List Alphabet} (he : x :: (v ++ [y]) ∈ firstReturn (psi N T))
    (hx : psi N T (FreeMonoid.of x) ≠ 1) :
    T (FreeMonoid.ofList (x :: (v ++ [y]))) =
      cv N T 1 x * (valN N T hab (rres N T (psi N T (FreeMonoid.of x)) v) : G) *
        cv N T (psi N T (FreeMonoid.of y))⁻¹ y := by
  have ht := telescope N T 1 (x :: (v ++ [y]))
  rw [one_mul (psi N T _), he.2.1, rep_one, inv_one, mul_one, one_mul] at ht
  rw [ht]
  have hpre : ∀ p, p <+: v → psi N T (FreeMonoid.of x) * psi N T (FreeMonoid.ofList p) ≠ 1 := by
    intro p hp
    have hne : x :: p ≠ x :: (v ++ [y]) := by
      intro h
      have := congrArg List.length h
      have := hp.length_le
      simp at *
      omega
    have := he.2.2 (x :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp.trans (List.prefix_append _ _)⟩)
      (List.cons_ne_nil _ _) hne
    simpa [FreeMonoid.ofList_cons] using this
  obtain ⟨h1, h2⟩ := walk_reset N T h3 v _ hx hpre
  have hlast : psi N T (FreeMonoid.of x) * psi N T (FreeMonoid.ofList v) =
      (psi N T (FreeMonoid.of y))⁻¹ := by
    have := he.2.1
    simp only [FreeMonoid.ofList_cons, FreeMonoid.ofList_append, FreeMonoid.ofList_nil,
      map_mul, mul_one] at this
    rw [eq_inv_iff_mul_eq_one, ← this, mul_assoc]
  rw [tpairs, tpairs_append, one_mul, h1, hlast]
  simp only [tpairs, List.map_cons, List.map_append, List.map_nil, List.prod_cons,
    List.prod_append, List.prod_nil, mul_one, rpairs_prod N T hab, mul_assoc]

/-- **The value of a remainder.** -/
lemma rem_value (h3 : Nat.card (G ⧸ N) = 3) (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    {x : Alphabet} {v : List Alphabet} (hr : x :: v ∈ remainder (firstReturn (psi N T))) :
    psi N T (FreeMonoid.of x) ≠ 1 ∧
    T (FreeMonoid.ofList (x :: v)) =
      cv N T 1 x * (valN N T hab (rres N T (psi N T (FreeMonoid.of x)) v) : G) *
        rep N (rstate (KK N T) (RR N T) (psi N T (FreeMonoid.of x)) v) := by
  rw [mem_remainder_group] at hr
  have hx : psi N T (FreeMonoid.of x) ≠ 1 := by
    have := hr [x] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (List.cons_ne_nil _ _)
    simpa using this
  refine ⟨hx, ?_⟩
  have hpre : ∀ p, p <+: v → psi N T (FreeMonoid.of x) * psi N T (FreeMonoid.ofList p) ≠ 1 := by
    intro p hp
    have := hr (x :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩) (List.cons_ne_nil _ _)
    simpa [FreeMonoid.ofList_cons] using this
  obtain ⟨h1, h2⟩ := walk_reset N T h3 v _ hx hpre
  have ht := telescope N T 1 (x :: v)
  rw [rep_one, one_mul, one_mul, mul_inv_eq_iff_eq_mul] at ht
  rw [ht, tpairs, one_mul, h1]
  have h2' : psi N T (FreeMonoid.ofList (x :: v)) =
      rstate (KK N T) (RR N T) (psi N T (FreeMonoid.of x)) v := by
    rw [← h2, FreeMonoid.ofList_cons, map_mul]
  rw [h2']
  simp only [List.map_cons, List.prod_cons, rpairs_prod N T hab, mul_assoc]

end Values


section Languages

open Classical

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (T : FreeMonoid Alphabet →* G)
  [Fintype Alphabet] [Fintype (G ⧸ N)]

/-- Blocks with a given value. -/
def Bv (g : G) : Language Alphabet :=
  {e | e ∈ firstReturn (psi N T) ∧ T (FreeMonoid.ofList e) = g}

/-- Remainders with a given value. -/
def Rv (f : G) : Language Alphabet :=
  {w | w ∈ remainder (firstReturn (psi N T)) ∧ T (FreeMonoid.ofList w) = f}

/-- Words read from `q` with the given residues of all the counts. -/
def resLang (q : G ⧸ N) (res : (G ⧸ N) × Alphabet → Fin (Nat.card N)) : Language Alphabet :=
  ⨅ p : (G ⧸ N) × Alphabet, rmod (KK N T) (RR N T) p.1 p.2 q (Nat.card N) (res p)

omit [Fintype Alphabet] [Fintype (G ⧸ N)] in
lemma mem_resLang {q : G ⧸ N} {res : (G ⧸ N) × Alphabet → Fin (Nat.card N)}
    {v : List Alphabet} : v ∈ resLang N T q res ↔ rres N T q v = fun p => (res p : ℕ) := by
  rw [resLang, HasHeightAtMost.mem_iInf_lang, funext_iff]
  rfl

lemma resLang_height [Finite N] (q : G ⧸ N) (res : (G ⧸ N) × Alphabet → Fin (Nat.card N)) :
    HasHeightAtMost (resLang N T q res) 1 :=
  HasHeightAtMost.iInf _ (fun p => rcountMod_height Nat.card_pos (res p).2 q)

/-- Index data of the blocks of length at least two with value `g`. -/
abbrev BIdx (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (g : G) :=
  {t : Alphabet × Alphabet × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    psi N T (FreeMonoid.of t.1) ≠ 1 ∧
    cv N T 1 t.1 * (valN N T hab (fun p => (t.2.2 p : ℕ)) : G) *
      cv N T (psi N T (FreeMonoid.of t.2.1))⁻¹ t.2.1 = g}

/-- Index data of the nonempty remainders with value `f`. -/
abbrev RIdx (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (f : G) :=
  {t : Alphabet × (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    cv N T 1 t.1 * (valN N T hab (fun p => (t.2.2 p : ℕ)) : G) * rep N t.2.1 = f}

lemma Bv_eq [Finite N] (h3 : Nat.card (G ⧸ N) = 3) (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (g : G) :
    Bv N T g = (⨆ x : {x : Alphabet // psi N T (FreeMonoid.of x) = 1 ∧ T (FreeMonoid.of x) = g},
        firstReturn (psi N T) ⊓ ({[x.1]} : Language Alphabet)) ⊔
      ⨆ t : BIdx N T hab g, firstReturn (psi N T) ⊓
        ({[t.1.1]} * resLang N T (psi N T (FreeMonoid.of t.1.1)) t.1.2.2 * {[t.1.2.1]}) := by
  ext w
  constructor
  · rintro ⟨he, hTe⟩
    cases w with
    | nil => exact absurd rfl he.1
    | cons x rest =>
    by_cases hx : psi N T (FreeMonoid.of x) = 1
    · have hrest : rest = [] := by
        by_contra hrest
        apply he.2.2 [x] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩)
          (List.cons_ne_nil _ _) (by simpa using Ne.symm hrest)
        simpa using hx
      subst hrest
      refine Or.inl (Language.mem_iSup.mpr ⟨⟨x, hx, by simpa using hTe⟩, he, rfl⟩)
    · have hrest : rest ≠ [] := by
        rintro rfl
        exact hx (by simpa using he.2.1)
      obtain ⟨v, y, rfl⟩ := (List.eq_nil_or_concat' rest).resolve_left hrest
      refine Or.inr (Language.mem_iSup.mpr ⟨⟨(x, y, fun p =>
        ⟨rres N T (psi N T (FreeMonoid.of x)) v p, Nat.mod_lt _ Nat.card_pos⟩), hx, ?_⟩, he, ?_⟩)
      · rw [← hTe, block_value N T h3 hab he hx]
      · refine Language.mem_mul.mpr ⟨[x] ++ v, Language.mem_mul.mpr ⟨[x], rfl, v,
          (mem_resLang N T).mpr rfl, rfl⟩, [y], rfl, by simp⟩
  · intro hw
    rcases hw with hw | hw
    · obtain ⟨x, he, hx⟩ := Language.mem_iSup.mp hw
      refine ⟨he, ?_⟩
      have hx' : w = [x.1] := hx
      rw [hx']
      simpa using x.2.2
    · obtain ⟨t, he, hm⟩ := Language.mem_iSup.mp hw
      refine ⟨he, ?_⟩
      obtain ⟨xv, hxv, yy, hyy, rfl⟩ := Language.mem_mul.mp hm
      obtain ⟨xx, hxx, v, hv, rfl⟩ := Language.mem_mul.mp hxv
      have hxx' : xx = [t.1.1] := hxx
      have hyy' : yy = [t.1.2.1] := hyy
      subst hxx' hyy'
      have heq : [t.1.1] ++ v ++ [t.1.2.1] = t.1.1 :: (v ++ [t.1.2.1]) := by simp
      rw [heq] at he ⊢
      rw [block_value N T h3 hab he t.2.1, (mem_resLang N T).mp hv]
      exact t.2.2

lemma Bv_height [Finite N] (h3 : Nat.card (G ⧸ N) = 3)
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hE1 : HasHeightAtMost (firstReturn (psi N T)) 1) (g : G) :
    HasHeightAtMost (Bv N T g) 1 := by
  rw [Bv_eq N T h3 hab g]
  refine HasHeightAtMost.union (HasHeightAtMost.iSup _ fun x =>
    hE1.inter (HasHeightAtMost.singleton _ _)) (HasHeightAtMost.iSup _ fun t =>
    hE1.inter (((HasHeightAtMost.singleton _ _).concat (resLang_height N T _ _)).concat
      (HasHeightAtMost.singleton _ _)))

omit [Fintype Alphabet] in
lemma nil_mem_remainder (E : Language Alphabet) (hE : [] ∉ E) : [] ∈ remainder E := by
  intro e he hp
  rw [List.prefix_nil] at hp
  exact hE (hp ▸ he)

lemma Rv_eq [Finite N] (h3 : Nat.card (G ⧸ N) = 3) (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (f : G) :
    Rv N T f = (if f = 1 then (1 : Language Alphabet) else 0) ⊔
      ⨆ t : RIdx N T hab f, remainder (firstReturn (psi N T)) ⊓
        ({[t.1.1]} * (resLang N T (psi N T (FreeMonoid.of t.1.1)) t.1.2.2 ⊓
          stateIs (KK N T) (RR N T) (psi N T (FreeMonoid.of t.1.1)) t.1.2.1)) := by
  ext w
  constructor
  · rintro ⟨hr, hTw⟩
    cases w with
    | nil =>
        refine Or.inl ?_
        have hf : f = 1 := by rw [← hTw]; simp
        rw [if_pos hf]
        exact (Language.mem_one _).mpr rfl
    | cons x v =>
        obtain ⟨hx, hT⟩ := rem_value N T h3 hab hr
        refine Or.inr (Language.mem_iSup.mpr ⟨⟨(x, rstate (KK N T) (RR N T)
          (psi N T (FreeMonoid.of x)) v, fun p =>
          ⟨rres N T (psi N T (FreeMonoid.of x)) v p, Nat.mod_lt _ Nat.card_pos⟩), ?_⟩, hr, ?_⟩)
        · rw [← hTw, hT]
        · exact Language.mem_mul.mpr ⟨[x], rfl, v, ⟨(mem_resLang N T).mpr rfl, rfl⟩, rfl⟩
  · intro hw
    rcases hw with hw | hw
    · split_ifs at hw with hf
      · have hw' : w = [] := (Language.mem_one _).mp hw
        subst hw'
        exact ⟨nil_mem_remainder _ (firstReturn_prefixCode _).1, by rw [hf]; simp⟩
      · exact absurd hw (Language.notMem_zero _)
    · obtain ⟨t, hr, hm⟩ := Language.mem_iSup.mp hw
      refine ⟨hr, ?_⟩
      obtain ⟨xx, hxx, v, ⟨hv, hs⟩, rfl⟩ := Language.mem_mul.mp hm
      have hxx' : xx = [t.1.1] := hxx
      subst hxx'
      change t.1.1 :: v ∈ _ at hr
      change T (FreeMonoid.ofList (t.1.1 :: v)) = f
      rw [(rem_value N T h3 hab hr).2, (mem_resLang N T).mp hv]
      have hs' : rstate (KK N T) (RR N T) (psi N T (FreeMonoid.of t.1.1)) v = t.1.2.1 := hs
      rw [hs']
      exact t.2

lemma Rv_height [Finite N] (h3 : Nat.card (G ⧸ N) = 3)
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hE1 : HasHeightAtMost (firstReturn (psi N T)) 1) (f : G) :
    HasHeightAtMost (Rv N T f) 1 := by
  rw [Rv_eq N T h3 hab f]
  have hrem : HasHeightAtMost (remainder (firstReturn (psi N T))) 1 := by
    rw [remainder_eq]
    exact (hE1.concat (HasHeightAtMost.top 1)).compl
  refine HasHeightAtMost.union ?_ (HasHeightAtMost.iSup _ fun t =>
    hrem.inter ((HasHeightAtMost.singleton _ _).concat
      ((resLang_height N T _ _).inter (stateIs_height _ _ 1))))
  split_ifs
  · exact HasHeightAtMost.one 1
  · exact HasHeightAtMost.zero 1

end Languages


section Blocks

open Classical

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] (T : FreeMonoid Alphabet →* G)
  [Fintype N]

/-- The product `∏ g ^ c g` in the commutative group `N`. -/
noncomputable def prodN (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (c : N → ℕ) : N :=
  letI := nComm N hab
  ∏ g : N, g ^ c g

omit [N.Normal] in
lemma prodN_mod (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (c : N → ℕ) :
    prodN N hab (fun g => c g % Nat.card N) = prodN N hab c := by
  let := nComm N hab
  exact Finset.prod_congr rfl (fun g _ => (pow_mod_card_N N g (c g)).symm)

lemma T_flatten (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) :
    ∀ es : List (List Alphabet), AllIn (firstReturn (psi N T)) es →
      T (FreeMonoid.ofList es.flatten) = (prodN N hab (fun g => bcount (Bv N T g) es) : G)
  | [], _ => by
      let := nComm N hab
      simp [prodN, bcount]
  | e :: es, hes => by
      let := nComm N hab
      have he : e ∈ firstReturn (psi N T) := hes e (by simp)
      have ih := T_flatten hab es (fun f hf => hes f (by simp [hf]))
      let ge : N := ⟨T (FreeMonoid.ofList e), T_mem_of_firstReturn N T he⟩
      have hb : ∀ g : N, e ∈ Bv N T g ↔ g = ge :=
        fun g => ⟨fun h => Subtype.ext h.2.symm, fun h => ⟨he, by rw [h]⟩⟩
      rw [List.flatten_cons, FreeMonoid.ofList_append, map_mul, ih]
      change (ge : G) * _ = _
      rw [← Subgroup.coe_mul]
      congr 1
      simp only [prodN, bcount, List.countP_cons, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [Finset.prod_eq_single ge]
      · simp [hb]
      · intro g _ hg
        simp [hb, hg]
      · simp

variable [Fintype Alphabet] [Fintype (G ⧸ N)]

omit [Fintype Alphabet] [Fintype (G ⧸ N)] in
lemma Av_eq (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (d : G) :
    ({w | w ∈ (firstReturn (psi N T))∗ ∧ T (FreeMonoid.ofList w) = d} : Language Alphabet) =
      ⨆ res : {res : N → Fin (Nat.card N) // (prodN N hab (fun g => (res g : ℕ)) : G) = d},
        ⨅ g : N, bmod (firstReturn (psi N T)) (Bv N T g) (Nat.card N) (res.1 g) := by
  ext w
  constructor
  · rintro ⟨hw, hT⟩
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hw
    refine Language.mem_iSup.mpr ⟨⟨fun g => ⟨bcount (Bv N T g) es % Nat.card N,
      Nat.mod_lt _ Nat.card_pos⟩, ?_⟩, HasHeightAtMost.mem_iInf_lang.mpr fun g =>
        ⟨es, hes, rfl, rfl⟩⟩
    rw [← hT, T_flatten N T hab es hes]
    exact congrArg Subtype.val (prodN_mod N hab (fun g : N => bcount (Bv N T g) es))
  · intro hw
    obtain ⟨res, hm⟩ := Language.mem_iSup.mp hw
    have hall := HasHeightAtMost.mem_iInf_lang.mp hm
    obtain ⟨es, hes, rfl, -⟩ := hall 1
    refine ⟨Language.mem_kstar.mpr ⟨es, rfl, hes⟩, ?_⟩
    have hc : (fun g : N => bcount (Bv N T g) es % Nat.card N) = fun g => (res.1 g : ℕ) := by
      funext g
      obtain ⟨fs, hfs, hflat, hk⟩ := hall g
      rw [← flatten_injective (firstReturn_prefixCode _) hfs hes hflat]
      exact hk
    change T (FreeMonoid.ofList es.flatten) = d
    rw [T_flatten N T hab es hes, ← prodN_mod, hc]
    exact res.2

lemma Av_height (h3 : Nat.card (G ⧸ N) = 3) (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hE1 : HasHeightAtMost (firstReturn (psi N T)) 1)
    (hEs : HasHeightAtMost (firstReturn (psi N T))∗ 1) (d : G) :
    HasHeightAtMost
      ({w | w ∈ (firstReturn (psi N T))∗ ∧ T (FreeMonoid.ofList w) = d} : Language Alphabet) 2 := by
  rw [Av_eq N T hab d]
  exact HasHeightAtMost.iSup _ fun res => HasHeightAtMost.iInf _ fun g =>
    bmod_height (firstReturn_prefixCode _) (fun e he => he.1) hEs
      (Bv_height N T h3 hab hE1 g) (res.1 g).2

end Blocks

/-- **Generalized star height at most two for groups with an abelian normal subgroup of index
three.** -/
theorem height_two_of_abelian_index_three [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 3)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 := by
  classical
  have := Fintype.ofFinite Alphabet
  have h3 : Nat.card (G ⧸ N) = 3 := hidx
  have hQ : ∀ x y : G ⧸ N, x * y = y * x := q3_comm h3
  have hfib : HasHeightAtMost
      ({w | psi N T (FreeMonoid.ofList w) = 1} : Language Alphabet) 1 := by
    simpa using height_one_of_comm hQ (psi N T) {1}
  have hE1 := firstReturn_height_of_fiber_one (psi N T) hfib
  have hEs : HasHeightAtMost (firstReturn (psi N T))∗ 1 := by
    rw [kstar_firstReturn_group]
    exact hfib
  exact height_two_of_split T (firstReturn (psi N T)) (firstReturn_prefixCode _).1
    (Av_height N T h3 hab hE1 hEs) (Rv_height N T h3 hab hE1) F

/-- **The corollary for `A₄`**, through its Klein four subgroup. -/
theorem height_two_alternatingGroup_four [Finite Alphabet]
    (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4)) (F : Set (alternatingGroup (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have := alternatingGroup.normal_kleinFour h4
  have hK := alternatingGroup.kleinFour_isKleinFour h4
  have hab : ∀ x ∈ alternatingGroup.kleinFour (Fin 4), ∀ y ∈ alternatingGroup.kleinFour (Fin 4),
      x * y = y * x := by
    intro x hx y hy
    have := hK.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hidx : (alternatingGroup.kleinFour (Fin 4)).index = 3 := by
    have h := (alternatingGroup.kleinFour (Fin 4)).index_mul_card
    rw [hK.card_four, nat_card_alternatingGroup, h4] at h
    norm_num [Nat.factorial] at h
    omega
  exact height_two_of_abelian_index_three _ hab hidx T F

end GeneralizedStarHeight
