import Start.StarHeightPrimeIndex

/-!
# An abelian normal subgroup adds at most one to generalized star height

* `height_succ_of_abelian_normal`: if `N` is an abelian normal subgroup of a finite group `G` and
  every language recognized by a morphism into `G ⧸ N` has height at most `k`, then every language
  recognized by a morphism into `G` has height at most `k + 1` (the wreath product principle).
* `height_two_of_commutator_abelian`: every language recognized by a finite group with abelian
  commutator subgroup (a metabelian group) has height at most two.

The proof: the telescoping of `Start/StarHeightIndexThree.lean` writes `T w` as a product, in the
abelian `N`, of values of the pairs (state, letter), times a representative of the final state.
The number of positions reading `a` in state `q` is counted by factoring the word at those
positions: after each of them the state is `q·ψ(a)`, so the segments in between are languages of
`G ⧸ N` (height at most `k`), and the count condition is `U₀ a (U a)^r ((U a)^m)∗ Z`, one more star.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

namespace HasHeightAtMost

variable {α : Type u} {L : Language α} {n : ℕ}

lemma pow (h : HasHeightAtMost L n) : ∀ c : ℕ, HasHeightAtMost (L ^ c) n
  | 0 => by rw [_root_.pow_zero]; exact HasHeightAtMost.one n
  | c + 1 => by rw [pow_succ]; exact (pow h c).concat h

end HasHeightAtMost

section Count

open Classical

variable {Alphabet : Type u} {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (T : FreeMonoid Alphabet →* G) (q : G ⧸ N) (a : Alphabet)

/-- The number of positions reading `a` in state `q`, starting in state `s`. -/
noncomputable def qcount : G ⧸ N → List Alphabet → ℕ
  | _, [] => 0
  | s, b :: w => (if b = a ∧ s = q then 1 else 0) + qcount (s * psi N T (FreeMonoid.of b)) w

lemma tpairs_count_eq_qcount : ∀ (w : List Alphabet) (s : G ⧸ N),
    (tpairs N T s w).count (q, a) = qcount N T q a s w
  | [], _ => rfl
  | b :: w, s => by
      rw [tpairs, qcount, List.count_cons, tpairs_count_eq_qcount w, add_comm]
      congr 1
      by_cases h : b = a ∧ s = q
      · obtain ⟨rfl, rfl⟩ := h; simp
      · rw [if_neg h]
        have : ¬ ((s, b) == (q, a)) = true := by
          simp only [beq_iff_eq, Prod.mk.injEq]
          exact fun h' => h ⟨h'.2, h'.1⟩
        simp [this]

lemma qcount_append (s : G ⧸ N) (u v : List Alphabet) :
    qcount N T q a s (u ++ v) =
      qcount N T q a s u + qcount N T q a (s * psi N T (FreeMonoid.ofList u)) v := by
  induction u generalizing s with
  | nil => simp [qcount]
  | cons b u ih =>
      simp only [List.cons_append, qcount, ih, FreeMonoid.ofList_cons, map_mul, mul_assoc,
        add_assoc]

/-- Words starting in state `s` that end in state `t`. -/
def fib (s t : G ⧸ N) : Language Alphabet := {u | s * psi N T (FreeMonoid.ofList u) = t}

/-- Words with no position reading `a` in state `q`, starting in state `s`. -/
def zfree (s : G ⧸ N) : Language Alphabet := {w | qcount N T q a s w = 0}

lemma qcount_eq_zero_iff : ∀ (w : List Alphabet) (s : G ⧸ N), qcount N T q a s w = 0 ↔
    ∀ u v, w = u ++ a :: v → s * psi N T (FreeMonoid.ofList u) ≠ q
  | [], s => by simp [qcount]
  | b :: w, s => by
      rw [qcount, Nat.add_eq_zero_iff, qcount_eq_zero_iff w]
      constructor
      · rintro ⟨h1, h2⟩ u v huv
        rcases u with _ | ⟨c, u⟩
        · simp only [List.nil_append, List.cons.injEq] at huv
          obtain ⟨rfl, rfl⟩ := huv
          intro hs
          simp only [FreeMonoid.ofList_nil, map_one, mul_one] at hs
          simp [hs] at h1
        · simp only [List.cons_append, List.cons.injEq] at huv
          obtain ⟨rfl, rfl⟩ := huv
          have := h2 u v rfl
          simpa [FreeMonoid.ofList_cons, mul_assoc] using this
      · intro h
        refine ⟨?_, fun u v huv => ?_⟩
        · split_ifs with hb
          · obtain ⟨rfl, rfl⟩ := hb
            exact absurd (by simp) (h [] w rfl)
          · rfl
        · have := h (b :: u) v (by rw [huv]; rfl)
          simpa [FreeMonoid.ofList_cons, mul_assoc] using this

lemma zfree_eq (s : G ⧸ N) :
    zfree N T q a s = (fib N T s q * {[a]} * ⊤)ᶜ := by
  ext w
  constructor
  · intro hw hm
    obtain ⟨ua, hua, v, -, rfl⟩ := Language.mem_mul.mp hm
    obtain ⟨u, hu, aa, haa, rfl⟩ := Language.mem_mul.mp hua
    have haa' : aa = [a] := haa
    subst haa'
    exact (qcount_eq_zero_iff N T q a _ s).mp hw u v (by simp) hu
  · intro hw
    refine (qcount_eq_zero_iff N T q a w s).mpr fun u v huv hs => hw ?_
    exact Language.mem_mul.mpr ⟨u ++ [a], Language.mem_mul.mpr ⟨u, hs, [a], rfl, rfl⟩, v,
      trivial, by simp [huv]⟩

lemma qcount_succ_iff (c : ℕ) : ∀ (w : List Alphabet) (s : G ⧸ N),
    qcount N T q a s w = c + 1 ↔ ∃ u v, w = u ++ a :: v ∧ qcount N T q a s u = 0 ∧
      s * psi N T (FreeMonoid.ofList u) = q ∧
        qcount N T q a (q * psi N T (FreeMonoid.of a)) v = c
  | [], s => by simp [qcount]
  | b :: w, s => by
      constructor
      · intro h
        rw [qcount] at h
        by_cases hb : b = a ∧ s = q
        · obtain ⟨rfl, rfl⟩ := hb
          rw [if_pos ⟨rfl, rfl⟩] at h
          exact ⟨[], w, rfl, rfl, by simp, by omega⟩
        · rw [if_neg hb, zero_add] at h
          obtain ⟨u, v, rfl, h1, h2, h3⟩ := (qcount_succ_iff c w _).mp h
          refine ⟨b :: u, v, rfl, ?_, ?_, h3⟩
          · rw [qcount, if_neg hb, h1]
          · simpa [FreeMonoid.ofList_cons, mul_assoc] using h2
      · rintro ⟨u, v, huv, h1, h2, h3⟩
        rw [huv, qcount_append, h1, h2, qcount, if_pos ⟨rfl, rfl⟩, h3]
        omega

/-- The blocks: a segment from state `q·ψ(a)` back to `q` with no counted position, then `a`. -/
def qblock : Language Alphabet :=
  (zfree N T q a (q * psi N T (FreeMonoid.of a)) ⊓ fib N T (q * psi N T (FreeMonoid.of a)) q) *
    {[a]}

/-- Words with exactly `c` counted positions from state `s`. -/
def qeq (s : G ⧸ N) (c : ℕ) : Language Alphabet := {w | qcount N T q a s w = c}

/-- Words with `r` counted positions modulo `m` from state `s`. -/
def qmod (s : G ⧸ N) (m r : ℕ) : Language Alphabet := {w | qcount N T q a s w % m = r}

lemma qcount_eq_lang (s : G ⧸ N) (c : ℕ) :
    qeq N T q a s (c + 1) =
      (zfree N T q a s ⊓ fib N T s q) * {[a]} * qeq N T q a (q * psi N T (FreeMonoid.of a)) c := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, v, rfl, h1, h2, h3⟩ := (qcount_succ_iff N T q a c w s).mp hw
    exact Language.mem_mul.mpr ⟨u ++ [a], Language.mem_mul.mpr ⟨u, ⟨h1, h2⟩, [a], rfl, rfl⟩, v,
      h3, by simp⟩
  · intro hw
    obtain ⟨ua, hua, v, hv, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨u, ⟨h1, h2⟩, aa, haa, rfl⟩ := Language.mem_mul.mp hua
    have haa' : aa = [a] := haa
    subst haa'
    exact (qcount_succ_iff N T q a c _ s).mpr ⟨u, v, by simp, h1, h2, hv⟩

lemma qcount_after_eq (c : ℕ) :
    qeq N T q a (q * psi N T (FreeMonoid.of a)) c =
      qblock N T q a ^ c * zfree N T q a (q * psi N T (FreeMonoid.of a)) := by
  induction c with
  | zero => rw [_root_.pow_zero, one_mul]; rfl
  | succ c ih =>
      rw [qcount_eq_lang, ih, pow_succ']
      simp only [qblock, mul_assoc]

lemma qcount_after_mod {m r : ℕ} (hr : r < m) :
    qmod N T q a (q * psi N T (FreeMonoid.of a)) m r =
      qblock N T q a ^ r * (qblock N T q a ^ m)∗ *
        zfree N T q a (q * psi N T (FreeMonoid.of a)) := by
  rw [Language.kstar_eq_iSup_pow, Language.mul_iSup, Language.iSup_mul]
  ext w
  rw [Language.mem_iSup]
  constructor
  · intro hw
    have hw' : qcount N T q a (q * psi N T (FreeMonoid.of a)) w % m = r := hw
    refine ⟨qcount N T q a (q * psi N T (FreeMonoid.of a)) w / m, ?_⟩
    rw [← pow_mul, ← pow_add, ← qcount_after_eq]
    show _ = _
    have := Nat.div_add_mod (qcount N T q a (q * psi N T (FreeMonoid.of a)) w) m
    rw [hw'] at this
    omega
  · rintro ⟨j, hj⟩
    rw [← pow_mul, ← pow_add, ← qcount_after_eq] at hj
    have hj' : qcount N T q a (q * psi N T (FreeMonoid.of a)) w = r + m * j := hj
    show _ % m = r
    rw [hj', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The count condition from state `s`. -/
lemma qcount_mod_eq (s : G ⧸ N) {m r : ℕ} (hm : 0 < m) (hr : r < m) :
    qmod N T q a s m r =
      (if r = 0 then zfree N T q a s else 0) + (zfree N T q a s ⊓ fib N T s q) * {[a]} *
        qmod N T q a (q * psi N T (FreeMonoid.of a)) m ((r + m - 1 % m) % m) := by
  ext w
  rw [Language.mem_add]
  constructor
  · intro hw
    have hw' : qcount N T q a s w % m = r := hw
    rcases hc : qcount N T q a s w with _ | c
    · left
      rw [hc, Nat.zero_mod] at hw'
      subst hw'
      simp only [if_true]
      exact hc
    · right
      rw [hc] at hw'
      have hc' : w ∈ qeq N T q a s (c + 1) := hc
      rw [qcount_eq_lang] at hc'
      obtain ⟨ua, hua, v, hv, rfl⟩ := Language.mem_mul.mp hc'
      have hv' : qcount N T q a (q * psi N T (FreeMonoid.of a)) v = c := hv
      refine Language.mem_mul.mpr ⟨ua, hua, v, ?_, rfl⟩
      show qcount N T q a (q * psi N T (FreeMonoid.of a)) v % m = _
      rw [hv']
      exact mod_arith_sub hm hw'
  · rintro (hw | hw)
    · split_ifs at hw with h0
      · subst h0
        show _ % m = 0
        rw [show qcount N T q a s w = 0 from hw, Nat.zero_mod]
      · exact absurd hw (by simp)
    · obtain ⟨ua, hua, v, hv, rfl⟩ := Language.mem_mul.mp hw
      have hv' : qcount N T q a (q * psi N T (FreeMonoid.of a)) v % m = (r + m - 1 % m) % m := hv
      have hc : ua ++ v ∈ qeq N T q a s
          (qcount N T q a (q * psi N T (FreeMonoid.of a)) v + 1) := by
        rw [qcount_eq_lang]
        exact Language.mem_mul.mpr ⟨ua, hua, v, rfl, rfl⟩
      show _ % m = r
      rw [show qcount N T q a s (ua ++ v) = _ from hc]
      exact mod_arith_add hm hr hv'

/-- **Every count condition has height at most `k + 1`.** -/
theorem qcount_height {k : ℕ}
    (hk : ∀ F : Set (G ⧸ N), HasHeightAtMost {w | psi N T (FreeMonoid.ofList w) ∈ F} k)
    (s : G ⧸ N) {m r : ℕ} (hm : 0 < m) (hr : r < m) :
    HasHeightAtMost (qmod N T q a s m r) (k + 1) := by
  have hfib : ∀ s t : G ⧸ N, HasHeightAtMost (fib N T s t) k := by
    intro s t
    have : fib N T s t = {w | psi N T (FreeMonoid.ofList w) ∈ ({s⁻¹ * t} : Set (G ⧸ N))} := by
      ext w
      show _ = _ ↔ _ = _
      constructor
      · intro h; rw [← h]; group
      · intro h; rw [h]; group
    rw [this]; exact hk _
  have hz : ∀ s, HasHeightAtMost (zfree N T q a s) k := by
    intro s
    rw [zfree_eq]
    exact (((hfib s q).concat (HasHeightAtMost.letter a k)).concat
      (HasHeightAtMost.top k)).compl
  have hblock : HasHeightAtMost (qblock N T q a) k :=
    ((hz _).inter (hfib _ _)).concat (HasHeightAtMost.letter a k)
  have hafter : ∀ r', r' < m →
      HasHeightAtMost (qmod N T q a (q * psi N T (FreeMonoid.of a)) m r') (k + 1) := by
    intro r' hr'
    rw [qcount_after_mod N T q a hr']
    refine ((HasHeightAtMost.pow hblock r').mono (by omega)).concat ?_ |>.concat
      ((hz _).mono (by omega))
    have := (HasHeightAtMost.pow hblock m).star
    rwa [add_comm] at this
  rw [qcount_mod_eq N T q a s hm hr]
  refine HasHeightAtMost.union ?_ ?_
  · split_ifs
    · exact (hz s).mono (by omega)
    · exact HasHeightAtMost.zero _
  · exact ((((hz s).inter (hfib s q)).concat (HasHeightAtMost.letter a k)).mono
      (by omega)).concat (hafter _ (Nat.mod_lt _ hm))

end Count

/-! ### Assembly -/

/-- **The wreath product step**: an abelian normal subgroup adds at most one to generalized star
height. -/
theorem height_succ_of_abelian_normal {Alphabet : Type u} [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) {k : ℕ}
    (hk : ∀ (T' : FreeMonoid Alphabet →* G ⧸ N) (F : Set (G ⧸ N)),
      HasHeightAtMost {w | T' (FreeMonoid.ofList w) ∈ F} k)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} (k + 1) := by
  classical
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % Nat.card N) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul] at ht
    exact ht
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          qmod N T pr.1 pr.2 1 (Nat.card N) (z.1.2 pr)) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % Nat.card N, Nat.mod_lt _ Nat.card_pos⟩), ?_⟩, rfl, ?_⟩
      · show _ ∈ F
        rw [← hval]; exact hw
      · refine HasHeightAtMost.mem_iInf_lang.mpr fun pr => ?_
        show _ = _
        simp only
        rw [tpairs_count_eq_qcount]
    · intro hw
      obtain ⟨z, hz1, hz2⟩ := Language.mem_iSup.mp hw
      have hz2' := HasHeightAtMost.mem_iInf_lang.mp hz2
      show T (FreeMonoid.ofList w) ∈ F
      rw [hval]
      have hres : (fun pr => (tpairs N T 1 w).count pr % Nat.card N) =
          fun pr => (z.1.2 pr : ℕ) := by
        funext pr
        rw [tpairs_count_eq_qcount]; exact hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  refine HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter ?_ ?_
  · exact (hk (psi N T) {z.1.1}).mono (by omega)
  · exact HasHeightAtMost.iInf _ fun pr =>
      qcount_height N T pr.1 pr.2 (hk (psi N T)) 1 Nat.card_pos (z.1.2 pr).2

/-- **Metabelian groups**: every language recognized by a finite group with abelian commutator
subgroup has height at most two. -/
theorem height_two_of_commutator_abelian {Alphabet : Type u} [Finite Alphabet] {G : Type}
    [Group G] [Fintype G]
    (hab : ∀ x ∈ commutator G, ∀ y ∈ commutator G, x * y = y * x)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 := by
  have : Fintype (G ⧸ commutator G) := Fintype.ofFinite _
  have hQ : ∀ x y : G ⧸ commutator G, x * y = y * x :=
    fun x y => @mul_comm (Abelianization G) _ x y
  exact height_succ_of_abelian_normal (commutator G) hab (k := 1)
    (fun T' F' => height_one_of_comm hQ T' F') T F

end GeneralizedStarHeight
