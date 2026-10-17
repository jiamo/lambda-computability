import Start.StarHeightZ4Classes

/-!
# Case (m) of `Z4CorePM1`: the moving counted letter

Letters `0` (`a`, counted, `+1`), `1` (`b`, `+1`), `2` (`d`, `-1`): displacements `σm`.
`zc σm 0 u` counts the letters `a` read in state `0`.

* `Z2 u`: the letters `a` at even positions (equivalently, read in an even state).
* `ad2 u`: the factors `ad` whose `a` is read in state `2`; `ad0 u`: the same in state `0`.
  `ad2 u = ad0 (b b u)` (`ad2_eq`), and `ad0 u` is the number of blocks `ad` of the factorization
  of `u` (`ad0_eq_Nad`).
* `Ncl c u`: the number of blocks of class `c` (`C⁺` for `c = 1`, `C⁻` for `c = 2`).
* **The identity** (`pm1_identity`): for `u` in state `0`,
  `2·zc σm 0 u = Z2 u + #C⁺(u) − #C⁻(u) − ad2 u`.
  It is an invariant of a scanning automaton (walk state, first and last letter of the current
  block, and the potential), checked on its reachable states (`id4_check`).
* `zcM_height`: counting `a` in state `0` modulo `n` has height at most one.  Every term of the
  identity, counted modulo `2n`, has height at most one: `Z2` by `pcount_height_one` (`p = 2`),
  the class counts by the Transfer Lemma (`bmodC_height`), and `ad2` by the Transfer Lemma for the
  block `ad` (`{ad}∗` is star-free) and two left quotients.
-/

namespace GeneralizedStarHeight

open EpisodeAlgebra
open scoped Computability

/-! ### The counts -/

/-- The letters `a` at even positions. -/
def Z2 (u : List (Fin 3)) : ℕ := pcount (fun _ : Fin 3 => true) 2 0 0 0 u

lemma Z2_snoc (u : List (Fin 3)) (a : Fin 3) :
    Z2 (u ++ [a]) = Z2 u + if a = 0 ∧ u.length % 2 = 0 then 1 else 0 := by
  unfold Z2
  rw [pcount_append]
  simp [pcount, List.countP_true]

lemma σm_parity : ∀ (z : ZMod 4) (b : Fin 3), (σm b + z).val % 2 = (z.val + 1) % 2 := by
  decide

lemma dsum4_parity : ∀ u : List (Fin 3), (dsum4 σm u).val % 2 = u.length % 2
  | [] => rfl
  | b :: w => by
      rw [dsum4_cons, σm_parity, List.length_cons, Nat.add_mod, dsum4_parity w, ← Nat.add_mod]

/-- Factors `ad` whose `d` is read in state `g`; `s` is the current state, `p` the previous
letter. -/
def adC (g : ZMod 4) : ZMod 4 → Option (Fin 3) → List (Fin 3) → ℕ
  | _, _, [] => 0
  | s, p, b :: w => (if p = some 0 ∧ b = 2 ∧ s = g then 1 else 0) + adC g (s + σm b) (some b) w

/-- **The factor `ad` with `a` read in state `2`.** -/
def ad2 (u : List (Fin 3)) : ℕ := adC 3 0 none u

/-- The factor `ad` with `a` read in state `0`. -/
def ad0 (u : List (Fin 3)) : ℕ := adC 1 0 none u

lemma adC_snoc (g : ZMod 4) (a : Fin 3) :
    ∀ (u : List (Fin 3)) (s : ZMod 4) (p : Option (Fin 3)), adC g s p (u ++ [a]) =
      adC g s p u + if (u.getLast?.or p) = some 0 ∧ a = 2 ∧ s + dsum4 σm u = g then 1 else 0
  | [], s, p => by simp [adC]
  | b :: u, s, p => by
      have e : (b :: u).getLast?.or p = u.getLast?.or (some b) := by
        rw [List.getLast?_cons]
        cases u.getLast? <;> rfl
      rw [List.cons_append, adC, adC, adC_snoc g a u, dsum4_cons, e]
      simp only [add_assoc]

lemma adC_shift (g c : ZMod 4) :
    ∀ (w : List (Fin 3)) (s : ZMod 4) (p : Option (Fin 3)), adC g s p w = adC (g + c) (s + c) p w
  | [], _, _ => rfl
  | b :: w, s, p => by
      rw [adC, adC, adC_shift g c w, show s + σm b + c = s + c + σm b by ring]
      congr 2
      simp only [add_left_inj]

lemma adC_prev (g s : ZMod 4) {p p' : Option (Fin 3)} (hp : p ≠ some 0) (hp' : p' ≠ some 0) :
    ∀ w : List (Fin 3), adC g s p w = adC g s p' w
  | [] => rfl
  | b :: w => by simp [adC, hp, hp']

lemma ad2_eq (u : List (Fin 3)) : ad2 u = ad0 (1 :: 1 :: u) := by
  unfold ad2 ad0
  rw [adC, adC, if_neg (by simp), if_neg (by decide), zero_add, zero_add,
    show (0 : ZMod 4) + σm 1 + σm 1 = 2 from rfl, adC_shift 1 2 u 2 (some 1),
    show (1 : ZMod 4) + 2 = 3 from rfl, show (2 : ZMod 4) + 2 = 0 from rfl]
  exact adC_prev _ _ (by simp) (by simp) u

/-! ### Block counts -/

/-- The number of blocks of class `c`. -/
noncomputable def Ncl (c : Fin 3) (u : List (Fin 3)) : ℕ := bcount (Ccl c) (splitW σm u).1

/-- The number of blocks `ad`. -/
noncomputable def Nad (u : List (Fin 3)) : ℕ := bcount ({[0, 2]} : Language (Fin 3)) (splitW σm u).1

lemma Ncl_snoc (c : Fin 3) (u : List (Fin 3)) (a : Fin 3) :
    Ncl c (u ++ [a]) = Ncl c u + if dsum4 σm ((splitW σm u).2 ++ [a]) = 0 ∧
      clsB (splitW σm u).2.head? (splitW σm u).2.getLast? a = c then 1 else 0 := by
  unfold Ncl
  rw [splitW_snoc]
  unfold splitWStep
  split_ifs with h1 h2 h3
  · rw [bcount_snoc, if_pos (show _ ∈ Ccl c from
      ⟨mem_Xc_snoc σm (splitW_spec σm u).2.2 h1, (bcls_snoc (tail_ne_nil_of_ret h1) a).trans h2.2⟩)]
  · rw [bcount_snoc, if_neg]
    rintro ⟨-, h⟩
    exact h2 ⟨h1, (bcls_snoc (tail_ne_nil_of_ret h1) a).symm.trans h⟩
  · exact absurd h3.1 h1
  · rfl

lemma getLast_of_dsum4_ne_zero {u : List (Fin 3)} (h : dsum4 σm u ≠ 0) :
    u.getLast? = (splitW σm u).2.getLast? := by
  have ht : (splitW σm u).2 ≠ [] := by
    intro h'
    rw [dsum4_splitW, h'] at h
    exact h rfl
  conv_lhs => rw [← (splitW_spec σm u).1]
  exact List.getLast?_append_of_ne_nil _ ht

lemma NR_last0 {t : List (Fin 3)} (ht : t ∈ NR σm) (hl : t.getLast? = some 0)
    (hs : dsum4 σm t = 1) : t = [0] := by
  obtain ⟨t', b, rfl⟩ := (List.eq_nil_or_concat t).resolve_left (by rintro rfl; simp at hl)
  simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at hl
  subst hl
  simp only [List.concat_eq_append] at ht hs ⊢
  rw [dsum4_append, dsum4_single] at hs
  have h0 : dsum4 σm t' = 0 := by
    have : dsum4 σm t' = 1 - σm 0 := eq_sub_of_add_eq hs
    rw [this]; decide
  by_cases h : t' = []
  · rw [h]; rfl
  · exact absurd h0 (ht t' (List.prefix_append _ _) h)

open Classical in
lemma ad0_eq_Nad (u : List (Fin 3)) : ad0 u = Nad u := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton u a ih =>
      unfold ad0 at ih ⊢
      unfold Nad at ih ⊢
      rw [adC_snoc, ih, splitW_snoc]
      simp only [Option.or_none, zero_add]
      have ht := (splitW_spec σm u).2.2
      have key : (u.getLast? = some 0 ∧ a = 2 ∧ dsum4 σm u = 1) ↔
          (dsum4 σm ((splitW σm u).2 ++ [a]) = 0 ∧ (splitW σm u).2 ++ [a] = [0, 2]) := by
        constructor
        · rintro ⟨hl, rfl, hd⟩
          have hne : dsum4 σm u ≠ 0 := by rw [hd]; decide
          rw [getLast_of_dsum4_ne_zero hne] at hl
          rw [NR_last0 ht hl (by rw [← dsum4_splitW]; exact hd)]
          exact ⟨by decide, rfl⟩
        · rintro ⟨-, hm⟩
          obtain ⟨h0, h2⟩ :=
            List.append_inj' (show (splitW σm u).2 ++ [a] = [0] ++ [2] from hm) rfl
          have ha : a = 2 := by simpa using h2
          have hd : dsum4 σm u = 1 := by rw [dsum4_splitW, h0]; rfl
          refine ⟨?_, ha, hd⟩
          rw [getLast_of_dsum4_ne_zero (by rw [hd]; decide), h0]
          rfl
      unfold splitWStep
      by_cases h0 : dsum4 σm ((splitW σm u).2 ++ [a]) = 0
      · rw [if_pos h0]
        show _ = bcount _ ((splitW σm u).1 ++ [(splitW σm u).2 ++ [a]])
        rw [bcount_snoc]
        by_cases hm : (splitW σm u).2 ++ [a] = [0, 2]
        · rw [if_pos (key.mpr ⟨h0, hm⟩),
            if_pos (show _ ∈ ({[0, 2]} : Language (Fin 3)) from hm)]
        · rw [if_neg (fun h => hm (key.mp h).2),
            if_neg (show _ ∉ ({[0, 2]} : Language (Fin 3)) from hm)]
      · rw [if_neg h0, if_neg (fun h => h0 (key.mp h).1)]
        rfl

/-! ### The identity -/

/-- The potential `2·zc − Z2 − #C⁺ + #C⁻ + ad2`. -/
noncomputable def Phi4 (u : List (Fin 3)) : ℤ :=
  2 * (zc σm 0 u : ℤ) - (Z2 u : ℤ) - (Ncl 1 u : ℤ) + (Ncl 2 u : ℤ) + (ad2 u : ℤ)

/-- The scanning automaton with the potential. -/
def idSt4 (q : ZMod 4 × Option (Fin 3) × Option (Fin 3) × ℤ) (a : Fin 3) :
    ZMod 4 × Option (Fin 3) × Option (Fin 3) × ℤ :=
  (q.1 + σm a, if q.1 + σm a = 0 then none else q.2.1.or (some a),
    if q.1 + σm a = 0 then none else some a,
    q.2.2.2 + (if a = 0 ∧ q.1 = 0 then 2 else 0) - (if a = 0 ∧ q.1.val % 2 = 0 then 1 else 0) -
      (if q.1 + σm a = 0 ∧ clsB q.2.1 q.2.2.1 a = 1 then 1 else 0) +
      (if q.1 + σm a = 0 ∧ clsB q.2.1 q.2.2.1 a = 2 then 1 else 0) +
      (if a = 2 ∧ q.2.2.1 = some 0 ∧ q.1 = 3 then 1 else 0))

/-- The state of the scanning automaton after `u`. -/
noncomputable def idState4 (u : List (Fin 3)) : ZMod 4 × Option (Fin 3) × Option (Fin 3) × ℤ :=
  (dsum4 σm (splitW σm u).2, (splitW σm u).2.head?, (splitW σm u).2.getLast?, Phi4 u)

lemma idState4_snoc (u : List (Fin 3)) (a : Fin 3) :
    idState4 (u ++ [a]) = idSt4 (idState4 u) a := by
  have hs : dsum4 σm ((splitW σm u).2 ++ [a]) = dsum4 σm (splitW σm u).2 + σm a := by
    rw [dsum4_append, dsum4_single]
  unfold idState4 idSt4
  simp only
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only
    rw [splitW_snoc]
    unfold splitWStep
    split_ifs with h
    · rw [← hs, h]; rfl
    · exact hs
  · simp only
    rw [splitW_snoc]
    unfold splitWStep
    by_cases h : dsum4 σm ((splitW σm u).2 ++ [a]) = 0
    · simp only [if_pos h]
      rw [if_pos (by rw [← hs]; exact h)]
      rfl
    · simp only [if_neg h]
      rw [if_neg (by rw [← hs]; exact h)]
      exact head?_snoc _ _
  · simp only
    rw [splitW_snoc]
    unfold splitWStep
    by_cases h : dsum4 σm ((splitW σm u).2 ++ [a]) = 0
    · simp only [if_pos h]
      rw [if_pos (by rw [← hs]; exact h)]
      rfl
    · simp only [if_neg h]
      rw [if_neg (by rw [← hs]; exact h)]
      simp
  · simp only [Phi4]
    rw [zc_snoc, Z2_snoc, Ncl_snoc, Ncl_snoc, ad2, adC_snoc, ← ad2]
    have hpar : (u.length % 2 = 0) ↔ ((dsum4 σm (splitW σm u).2).val % 2 = 0) := by
      rw [← dsum4_splitW, dsum4_parity]
    have hlast : ((u.getLast?.or none) = some 0 ∧ a = 2 ∧ 0 + dsum4 σm u = 3) ↔
        (a = 2 ∧ (splitW σm u).2.getLast? = some 0 ∧ dsum4 σm (splitW σm u).2 = 3) := by
      rw [Option.or_none, zero_add, ← dsum4_splitW]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rw [getLast_of_dsum4_ne_zero (by rw [h3]; decide)] at h1
        exact ⟨h2, h1, h3⟩
      · rintro ⟨h2, h1, h3⟩
        rw [getLast_of_dsum4_ne_zero (by rw [h3]; decide)]
        exact ⟨h1, h2, h3⟩
    rw [if_congr (and_congr_right' hpar) rfl rfl, if_congr hlast rfl rfl, hs, dsum4_splitW σm u]
    split_ifs <;> push_cast <;> ring

lemma idState4_eq_foldl (u : List (Fin 3)) : idState4 u = u.foldl idSt4 (0, none, none, 0) := by
  induction u using List.reverseRecOn with
  | nil => simp [idState4, Phi4, Ncl, splitW, zc, Z2, pcount, ad2, adC, bcount]
  | append_singleton u a ih => rw [idState4_snoc, ih, List.foldl_append]; rfl

/-- The predicate checked on the reachable states: the potential vanishes in state `0`. -/
def idGood4 (q : ZMod 4 × Option (Fin 3) × Option (Fin 3) × ℤ) : Bool :=
  if q.1 = 0 then decide (q.2.2.2 = 0) else true

lemma id4_check : checkInv [0, 1, 2] idSt4 (0, none, none, 0) idGood4
    (explore [0, 1, 2] idSt4 30 [(0, none, none, 0)] [(0, none, none, 0)]) = true := by
  decide +kernel

/-- **The identity.** For `u` in state `0`: `2·zc σm 0 u = Z2 u + #C⁺(u) − #C⁻(u) − ad2 u`. -/
theorem pm1_identity {u : List (Fin 3)} (h : dsum4 σm u = 0) :
    2 * (zc σm 0 u : ℤ) = (Z2 u : ℤ) + (Ncl 1 u : ℤ) - (Ncl 2 u : ℤ) - (ad2 u : ℤ) := by
  have hg := checkInv_spec letters3' id4_check u
  rw [← idState4_eq_foldl] at hg
  have ht : dsum4 σm (splitW σm u).2 = 0 := by rw [← dsum4_splitW]; exact h
  have : Phi4 u = 0 := by
    simp only [idGood4, idState4, ht, if_true, decide_eq_true_eq] at hg
    exact hg
  unfold Phi4 at this
  linarith

/-! ### Heights of the terms -/

theorem Z2_height {m r : ℕ} (hm : 0 < m) (hr : r < m) :
    HasHeightAtMost {u : List (Fin 3) | Z2 u % m = r} 1 :=
  pcount_height_one (fun _ : Fin 3 => true) Nat.prime_two (by norm_num) 0 hm hr

lemma ad_mem_Xc : [0, 2] ∈ Xc σm := by
  refine ⟨by simp, by decide, fun p hp hne hpe => ?_⟩
  rcases List.prefix_cons_iff.mp hp with h | ⟨p', rfl, hp'⟩
  · exact absurd h hne
  · rcases List.prefix_cons_iff.mp hp' with h | ⟨p'', rfl, hp''⟩
    · subst h; decide
    · rw [List.prefix_nil.mp hp''] at hpe; exact absurd rfl hpe

/-- The blocks other than `ad`. -/
def XcAd1 : Language (Fin 3) := Xc σm ⊓ ({[0, 2]} : Language (Fin 3))ᶜ

lemma XcAd_split : ({[0, 2]} : Language (Fin 3)) + XcAd1 = Xc σm := by
  ext e
  rw [Language.mem_add]
  constructor
  · rintro (h | h)
    · rw [show e = [0, 2] from h]; exact ad_mem_Xc
    · exact h.1
  · intro h
    by_cases h0 : e = [0, 2]
    · exact Or.inl h0
    · exact Or.inr ⟨h, h0⟩

theorem bmodAd_height {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (bmod (Xc σm) {[0, 2]} m r) 1 := by
  have hpc : PrefixCode (({[0, 2]} : Language (Fin 3)) + XcAd1) := by
    rw [XcAd_split]; exact Xc_prefixCode σm
  have hdis : Disjoint ({[0, 2]} : Language (Fin 3)) XcAd1 :=
    Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1
  have h1 : HasHeightAtMost XcAd1 0 :=
    Xc_starFree_m.inter (HasHeightAtMost.singleton _ 0).compl
  have hs : HasHeightAtMost ({[0, 2]} : Language (Fin 3))∗ 0 :=
    kstar_singleton_starFree [0, 2] (by simp) (fun j hj hj' => by
      simp at hj'; interval_cases j; decide)
  have h := transfer_height_one hpc hdis (HasHeightAtMost.singleton _ 0) h1 hs hr
  rwa [XcAd_split] at h

lemma ad0_lang (m r : ℕ) :
    ({v : List (Fin 3) | ad0 v % m = r} : Language (Fin 3)) =
      bmod (Xc σm) {[0, 2]} m r * NR σm := by
  ext v
  constructor
  · intro hv
    change ad0 v % m = r at hv
    refine Language.mem_mul.mpr ⟨(splitW σm v).1.flatten, ⟨(splitW σm v).1,
      (splitW_spec σm v).2.1, rfl, ?_⟩, (splitW σm v).2, (splitW_spec σm v).2.2,
      (splitW_spec σm v).1⟩
    rw [ad0_eq_Nad] at hv
    exact hv
  · intro hv
    obtain ⟨x, ⟨es, hes, rfl, hk⟩, t, ht, rfl⟩ := Language.mem_mul.mp hv
    show ad0 _ % m = r
    rw [ad0_eq_Nad, Nad, splitW_flatten σm hes ht]
    exact hk

theorem ad2_height {m r : ℕ} (hr : r < m) :
    HasHeightAtMost {u : List (Fin 3) | ad2 u % m = r} 1 := by
  have : ({u : List (Fin 3) | ad2 u % m = r} : Language (Fin 3)) =
      leftQuot 1 (leftQuot 1 {v : List (Fin 3) | ad0 v % m = r}) := by
    ext u
    show ad2 u % m = r ↔ ad0 (1 :: 1 :: u) % m = r
    rw [ad2_eq]
  rw [this, ad0_lang]
  exact (((bmodAd_height hr).concat (NR_starFree_m.mono (by omega))).leftQuot 1).leftQuot 1

/-! ### Assembly -/

/-- The residue condition. -/
def resM (k n : ℕ) (r : Fin (2 * n) × Fin (2 * n) × Fin (2 * n) × Fin (2 * n)) : Prop :=
  ((r.1 : ℤ) + (r.2.2.1 : ℤ) - (r.2.2.2 : ℤ) - (r.2.1 : ℤ) - 2 * k : ZMod (2 * n)) = 0

lemma zcK_m_eq (k n : ℕ) (hk : k < n) : zcK σm n k =
    ⨆ r : {r : Fin (2 * n) × Fin (2 * n) × Fin (2 * n) × Fin (2 * n) // resM k n r},
      ((({u | Z2 u % (2 * n) = r.1.1} : Language (Fin 3)) ⊓
        {u | ad2 u % (2 * n) = r.1.2.1}) ⊓
        (bmod (Xc σm) (Ccl 1) (2 * n) r.1.2.2.1 ⊓ bmod (Xc σm) (Ccl 2) (2 * n) r.1.2.2.2)) := by
  have hM : 0 < 2 * n := by omega
  have key : ∀ u : List (Fin 3), dsum4 σm u = 0 →
      (((Z2 u % (2 * n) : ℕ) : ℤ) + ((Ncl 1 u % (2 * n) : ℕ) : ℤ) -
        ((Ncl 2 u % (2 * n) : ℕ) : ℤ) - ((ad2 u % (2 * n) : ℕ) : ℤ) - 2 * k : ZMod (2 * n)) =
        ((2 * ((zc σm 0 u : ℤ) - k) : ℤ) : ZMod (2 * n)) := by
    intro u hu
    have := congrArg (fun z : ℤ => (z : ZMod (2 * n))) (pm1_identity hu)
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      Int.cast_ofNat] at this ⊢
    simp only [ZMod.natCast_mod]
    rw [mul_sub, this]
  have hdvd : ∀ c : ℕ, (((2 * ((c : ℤ) - k) : ℤ) : ZMod (2 * n)) = 0 ↔ c % n = k) := by
    intro c
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), ← Nat.modEq_iff_dvd]
    constructor
    · intro h
      have := h.symm
      unfold Nat.ModEq at this
      rw [this, Nat.mod_eq_of_lt hk]
    · intro h
      unfold Nat.ModEq
      rw [h, Nat.mod_eq_of_lt hk]
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    refine Language.mem_iSup.mpr ⟨⟨(⟨Z2 u % (2 * n), Nat.mod_lt _ hM⟩,
      ⟨ad2 u % (2 * n), Nat.mod_lt _ hM⟩, ⟨Ncl 1 u % (2 * n), Nat.mod_lt _ hM⟩,
      ⟨Ncl 2 u % (2 * n), Nat.mod_lt _ hM⟩), ?_⟩, ?_⟩
    · show (_ : ZMod (2 * n)) = 0
      rw [key u hu]
      exact (hdvd _).mpr hc
    · exact ⟨⟨rfl, rfl⟩, (mem_bmod_Xc σm _ _ _ u).mpr ⟨hu, rfl⟩,
        (mem_bmod_Xc σm _ _ _ u).mpr ⟨hu, rfl⟩⟩
  · intro h
    obtain ⟨r, ⟨h0, h1⟩, h2, h3⟩ := Language.mem_iSup.mp h
    obtain ⟨hu, e2⟩ := (mem_bmod_Xc σm _ _ _ u).mp h2
    obtain ⟨-, e3⟩ := (mem_bmod_Xc σm _ _ _ u).mp h3
    refine ⟨hu, (hdvd _).mp ?_⟩
    rw [← key u hu]
    have hr := r.2
    unfold resM at hr
    have e0 : Z2 u % (2 * n) = r.1.1 := h0
    have e1 : ad2 u % (2 * n) = r.1.2.1 := h1
    have e2' : Ncl 1 u % (2 * n) = r.1.2.2.1 := e2
    have e3' : Ncl 2 u % (2 * n) = r.1.2.2.2 := e3
    rw [e0, e1, e2', e3']
    exact hr

theorem zcK_m_height {k n : ℕ} (hk : k < n) : HasHeightAtMost (zcK σm n k) 1 := by
  have hM : 0 < 2 * n := by omega
  rw [zcK_m_eq k n hk]
  refine HasHeightAtMost.iSup _ fun r => ?_
  refine HasHeightAtMost.inter (HasHeightAtMost.inter ?_ ?_) (HasHeightAtMost.inter ?_ ?_)
  · exact Z2_height hM r.1.1.2
  · exact ad2_height r.1.2.1.2
  · exact bmodC_height (Or.inl rfl) r.1.2.2.1.2
  · exact bmodC_height (Or.inr rfl) r.1.2.2.2.2

/-- **Case (m).** With the counted letter moving, counting it in state `0` modulo `n` has height
at most one. -/
theorem zcM_height {n k : ℕ} (hk : k < n) :
    HasHeightAtMost {u : List (Fin 3) | zc σm 0 u % n = k} 1 :=
  zc_height_of_zcK σm rfl (zcK_m_height hk)

end GeneralizedStarHeight
