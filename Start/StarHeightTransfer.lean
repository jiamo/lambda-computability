import Start.StarHeightIndexThree

/-!
# The Transfer Lemma and star-free stars of primitive words

Pin, Straubing and Thérien (1992):

* `bmod_height_one_of_star_free`: counting `L`-blocks of a prefix code `E` modulo `m` has height at
  most one when the blocks outside `L` have a star-free star.
* `transfer_height_one` (PST Lemma 6.1): if `L₀`, `L₁` are star-free and disjoint, `L₀ ∪ L₁` is a
  prefix code and `L₀∗` is star-free, then the words of `(L₀ ∪ L₁)∗` whose factorization has
  `≡ r (mod m)` blocks in `L₀` form a language of height at most one.  `L₁∗` need not be
  star-free.
* `kstar_singleton_starFree`: if `t` is primitive (no nontrivial rotation of `t` equals `t`),
  then `t∗` is star-free.
* `primitive_of_prime_length`: every non-constant word of prime length is primitive.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

variable {α : Type u}

section Transfer

open Classical

variable {E L : Language α}

/-- Counting `L`-blocks at height one when the words of `E∗` without `L`-blocks are star-free. -/
theorem bmod_height_one_of_star_free (hL : L ≤ E) (h0 : HasHeightAtMost (bwords E L 0) 0)
    (hLh : HasHeightAtMost L 0) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (bmod E L m r) 1 := by
  rw [bmod_eq hL hr]
  have hY : HasHeightAtMost (bfirst E L) 0 := h0.concat hLh
  exact (pow_height hY m).star.concat ((pow_height hY r).concat h0 |>.mono (by omega))

lemma bcount_partition {L₀ L₁ : Language α} (hdisj : Disjoint L₀ L₁) :
    ∀ es : List (List α), AllIn (L₀ + L₁) es →
      bcount L₀ es + bcount L₁ es = bcount (L₀ + L₁) es
  | [], _ => by simp [bcount]
  | e :: es, hes => by
      have ih := bcount_partition hdisj es (fun f hf => hes f (by simp [hf]))
      have he : e ∈ L₀ + L₁ := hes e (by simp)
      unfold bcount at ih ⊢
      simp only [List.countP_cons, decide_eq_true_eq]
      rw [if_pos he]
      rcases (Language.mem_add _ _ _).mp he with h | h
      · have h' : e ∉ L₁ := fun h1 => Set.disjoint_left.mp hdisj h h1
        rw [if_pos h, if_neg h']
        omega
      · have h' : e ∉ L₀ := fun h0 => Set.disjoint_left.mp hdisj h0 h
        rw [if_pos h, if_neg h']
        omega

lemma bwords_compl_zero {L₀ L₁ : Language α} (hdisj : Disjoint L₀ L₁) :
    bwords (L₀ + L₁) L₁ 0 = L₀∗ := by
  ext x
  constructor
  · rintro ⟨es, hes, rfl, h0⟩
    refine Language.mem_kstar.mpr ⟨es, rfl, fun e he => ?_⟩
    unfold bcount at h0
    rw [List.countP_eq_zero] at h0
    rcases (Language.mem_add _ _ _).mp (hes e he) with h | h
    · exact h
    · exact absurd (decide_eq_true h) (h0 e he)
  · intro hx
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hx
    refine ⟨es, fun e he => (Language.mem_add _ _ _).mpr (Or.inl (hes e he)), rfl, ?_⟩
    unfold bcount
    rw [List.countP_eq_zero]
    intro e he h1
    exact Set.disjoint_left.mp hdisj (hes e he) (of_decide_eq_true h1)

lemma bwords_self_zero : bwords E E 0 = 1 := by
  ext x
  constructor
  · rintro ⟨es, hes, rfl, h0⟩
    unfold bcount at h0
    rw [List.countP_eq_zero] at h0
    cases es with
    | nil => exact (Language.mem_one _).mpr rfl
    | cons e es => exact absurd (by simpa using hes e (by simp)) (h0 e (by simp))
  · intro hx
    rw [Language.mem_one] at hx
    subst hx
    exact ⟨[], fun e he => by simp at he, rfl, by simp [bcount]⟩

lemma mod_sub_aux {a b c m r : ℕ} (hr : r < m) (habc : a + b = c) (ha : a % m = r) :
    b % m = (c % m + m - r) % m := by
  have h1 : b + r ≡ (c % m + m - r) + r [MOD m] := by
    have e1 : (c % m + m - r) + r = c % m + m := by omega
    rw [e1]
    calc b + r ≡ b + a [MOD m] := Nat.ModEq.add_left _ (by rw [Nat.ModEq, ha, Nat.mod_eq_of_lt hr])
      _ = c := by omega
      _ ≡ c % m [MOD m] := (Nat.mod_modEq c m).symm
      _ ≡ c % m + m [MOD m] := by simp [Nat.ModEq]
  exact Nat.ModEq.add_right_cancel' _ h1

lemma mod_sub_aux' {a b c m r : ℕ} (hr : r < m) (habc : a + b = c)
    (hb : b % m = (c % m + m - r) % m) : a % m = r := by
  have h1 : a + (c % m + m - r) ≡ r + (c % m + m - r) [MOD m] := by
    have e1 : r + (c % m + m - r) = c % m + m := by omega
    rw [e1]
    calc a + (c % m + m - r) ≡ a + b [MOD m] := Nat.ModEq.add_left _ hb.symm
      _ = c := habc
      _ ≡ c % m [MOD m] := (Nat.mod_modEq c m).symm
      _ ≡ c % m + m [MOD m] := by simp [Nat.ModEq]
  have := Nat.ModEq.add_right_cancel' _ h1
  rw [Nat.ModEq, Nat.mod_eq_of_lt hr] at this
  exact this

lemma bmod_eq_iSup {L₀ L₁ : Language α} (hE : PrefixCode (L₀ + L₁)) (hdisj : Disjoint L₀ L₁)
    {m r : ℕ} (hr : r < m) :
    bmod (L₀ + L₁) L₀ m r = ⨆ s : Fin m,
      (bmod (L₀ + L₁) (L₀ + L₁) m s ⊓ bmod (L₀ + L₁) L₁ m ((s + m - r) % m)) := by
  ext x
  constructor
  · rintro ⟨es, hes, rfl, hk⟩
    refine Language.mem_iSup.mpr ⟨⟨bcount (L₀ + L₁) es % m, Nat.mod_lt _ (by omega)⟩,
      ⟨es, hes, rfl, rfl⟩, es, hes, rfl, ?_⟩
    exact mod_sub_aux hr (bcount_partition hdisj es hes) hk
  · intro hx
    obtain ⟨s, ⟨es, hes, rfl, hs⟩, fs, hfs, hflat, ht⟩ := Language.mem_iSup.mp hx
    have := flatten_injective hE hfs hes hflat
    subst this
    refine ⟨fs, hes, rfl, mod_sub_aux' hr (bcount_partition hdisj fs hes) ?_⟩
    rw [hs]; exact ht

/-- **The Transfer Lemma** (PST Lemma 6.1). -/
theorem transfer_height_one {L₀ L₁ : Language α} (hE : PrefixCode (L₀ + L₁))
    (hdisj : Disjoint L₀ L₁) (h0 : HasHeightAtMost L₀ 0) (h1 : HasHeightAtMost L₁ 0)
    (h0s : HasHeightAtMost L₀∗ 0) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (bmod (L₀ + L₁) L₀ m r) 1 := by
  rw [bmod_eq_iSup hE hdisj hr]
  refine HasHeightAtMost.iSup _ fun s => ?_
  refine HasHeightAtMost.inter ?_ ?_
  · refine bmod_height_one_of_star_free le_rfl ?_ (h0.union h1) s.2
    rw [bwords_self_zero]; exact HasHeightAtMost.one 0
  · refine bmod_height_one_of_star_free (fun x hx => (Language.mem_add _ _ _).mpr (Or.inr hx))
      ?_ h1 (Nat.mod_lt _ (by omega))
    rw [bwords_compl_zero hdisj]; exact h0s

end Transfer

/-! ### Stars of primitive words -/

section Primitive

/-- The `n`-th power of a word. -/
def wpow (t : List α) (n : ℕ) : List α := (List.replicate n t).flatten

lemma wpow_length (t : List α) (n : ℕ) : (wpow t n).length = n * t.length := by
  induction n with
  | zero => simp [wpow]
  | succ n ih =>
      simp only [wpow, List.replicate_succ, List.flatten_cons, List.length_append] at ih ⊢
      rw [ih]; ring

lemma wpow_succ (t : List α) (n : ℕ) : wpow t (n + 1) = t ++ wpow t n := by
  simp [wpow, List.replicate_succ]

lemma wpow_succ' (t : List α) (n : ℕ) : wpow t (n + 1) = wpow t n ++ t := by
  simp [wpow, List.replicate_succ']

lemma wpow_getElem (t : List α) (ht : 0 < t.length) :
    ∀ (n i : ℕ) (h : i < (wpow t n).length), (wpow t n)[i] = t[i % t.length]'(Nat.mod_lt _ ht)
  | 0, i, h => by simp [wpow] at h
  | n + 1, i, h => by
      simp only [wpow_succ]
      by_cases hi : i < t.length
      · rw [List.getElem_append_left hi]
        simp [Nat.mod_eq_of_lt hi]
      · push Not at hi
        rw [List.getElem_append_right hi]
        rw [wpow_getElem t ht n]
        congr 1
        conv_rhs => rw [← Nat.sub_add_cancel hi]
        simp

lemma mem_kstar_singleton {t : List α} {u : List α} :
    u ∈ ({t} : Language α)∗ ↔ ∃ n, u = wpow t n := by
  constructor
  · intro h
    obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.mp h
    refine ⟨S.length, ?_⟩
    unfold wpow
    congr 1
    exact List.eq_replicate_iff.mpr ⟨rfl, fun b hb => hS b hb⟩
  · rintro ⟨n, rfl⟩
    exact Language.mem_kstar.mpr ⟨_, rfl, fun y hy => (List.eq_of_mem_replicate hy :)⟩

/-- Words of length `t.length` that are not rotations of `t`. -/
def badFactors (t : List α) : Language α := {x | x.length = t.length ∧ ∀ j, x ≠ t.rotate j}

/-- The star-free expression for `t∗`. -/
def primStarExpr (t : List α) : Language α :=
  1 + ({t} * ⊤ ⊓ ⊤ * {t} ⊓ (⊤ * badFactors t * ⊤)ᶜ)

lemma primStarExpr_height [Finite α] (t : List α) : HasHeightAtMost (primStarExpr t) 0 := by
  unfold primStarExpr
  have hbad : HasHeightAtMost (badFactors t) 0 :=
    HasHeightAtMost.finite _ ((List.finite_length_eq α t.length).subset fun x hx => hx.1) 0
  refine (HasHeightAtMost.one 0).union (HasHeightAtMost.inter (HasHeightAtMost.inter ?_ ?_) ?_)
  · exact (HasHeightAtMost.singleton t 0).concat (HasHeightAtMost.top 0)
  · exact (HasHeightAtMost.top 0).concat (HasHeightAtMost.singleton t 0)
  · exact (((HasHeightAtMost.top 0).concat hbad).concat (HasHeightAtMost.top 0)).compl

/-- A factor of `u` in `X` puts `u` in `⊤ X ⊤`. -/
lemma factor_mem {u : List α} {i k : ℕ} {X : Language α} (hX : (u.drop i).take k ∈ X) :
    u ∈ (⊤ : Language α) * X * ⊤ := by
  refine Language.mem_mul.mpr ⟨u.take i ++ (u.drop i).take k, Language.mem_mul.mpr
    ⟨u.take i, trivial, _, hX, rfl⟩, (u.drop i).drop k, trivial, ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

lemma drop_last_eq {x : List α} {n : ℕ} (hn : n + 1 = x.length) :
    x.drop n = [x[n]'(by omega)] := by
  rw [List.drop_eq_getElem_cons (by omega)]
  simp [List.drop_eq_nil_of_le (show x.length ≤ n + 1 by omega)]

lemma rotation_agree [DecidableEq α] {t x y : List α} (hx : x.Perm t) (hy : y.Perm t)
    {n : ℕ} (hxn : n + 1 = x.length) (hyn : n + 1 = y.length)
    (hagree : ∀ l (h : l < n), x[l]'(by omega) = y[l]'(by omega)) :
    x[n]'(by omega) = y[n]'(by omega) := by
  have hxy : x.Perm y := hx.trans hy.symm
  have htake : x.take n = y.take n := by
    apply List.ext_getElem (by simp; omega)
    intro l h1 h2
    simp only [List.getElem_take]
    exact hagree l (by simp at h1; omega)
  have hc := (List.perm_iff_count.mp hxy) (x[n]'(by omega))
  have e1 : ∀ (c : α) (z : List α), z.count c = (z.take n).count c + (z.drop n).count c := by
    intro c z; rw [← List.count_append, List.take_append_drop]
  rw [e1 _ x, e1 _ y, htake, drop_last_eq hxn, drop_last_eq hyn] at hc
  by_contra hne
  have : List.count (x[n]'(by omega)) [y[n]'(by omega)] = 0 := by
    simp only [List.count_singleton]
    simp [Ne.symm hne]
  simp [this] at hc

lemma mod_add_comm' (a l k : ℕ) : (a + l) % k = (l + a % k) % k := by
  rw [Nat.add_mod_mod, Nat.add_comm]

/-- **Stars of primitive words are star-free.** -/
theorem kstar_singleton_eq [DecidableEq α] (t : List α) (ht : t ≠ [])
    (hprim : ∀ j, 0 < j → j < t.length → t.rotate j ≠ t) :
    ({t} : Language α)∗ = primStarExpr t := by
  have hk : 0 < t.length := List.length_pos_iff.mpr ht
  ext u
  rw [mem_kstar_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    rcases n with _ | n
    · exact (Language.mem_add _ _ _).mpr (Or.inl ((Language.mem_one _).mpr rfl))
    refine (Language.mem_add _ _ _).mpr (Or.inr ⟨⟨?_, ?_⟩, ?_⟩)
    · exact Language.mem_mul.mpr ⟨t, rfl, _, trivial, (wpow_succ t n).symm⟩
    · exact Language.mem_mul.mpr ⟨_, trivial, t, rfl, (wpow_succ' t n).symm⟩
    · intro hm
      obtain ⟨ax, hax, b, -, hxb⟩ := Language.mem_mul.mp hm
      obtain ⟨a, -, x, ⟨hxl, hxr⟩, rfl⟩ := Language.mem_mul.mp hax
      apply hxr (a.length % t.length)
      apply List.ext_getElem (by simp [hxl])
      intro l h1 h2
      have hlen := congrArg List.length hxb
      simp only [List.length_append] at hlen
      have hw := wpow_getElem t hk (n + 1) (a.length + l) (by rw [← hxb]; simp; omega)
      simp only [← hxb] at hw
      rw [List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by omega)] at hw
      simp only [Nat.add_sub_cancel_left] at hw
      rw [hw, List.getElem_rotate]
      congr 1
      rw [mod_add_comm']
  · intro hu
    rcases (Language.mem_add _ _ _).mp hu with hu | ⟨⟨hpre, hsuf⟩, hbad⟩
    · exact ⟨0, by simpa [wpow, Language.mem_one] using hu⟩
    obtain ⟨t', ht', v, -, hpre⟩ := Language.mem_mul.mp hpre
    obtain ⟨v', -, t'', ht'', hsuf⟩ := Language.mem_mul.mp hsuf
    have e1 : t' = t := ht'
    have e2 : t'' = t := ht''
    rw [e1] at hpre
    rw [e2] at hsuf
    -- periodicity
    have hper : ∀ i (h : i < u.length), u[i] = t[i % t.length]'(Nat.mod_lt _ hk) := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro hi
        by_cases hik : i < t.length
        · subst hpre
          rw [List.getElem_append_left hik]
          simp [Nat.mod_eq_of_lt hik]
        · push Not at hik
          set k := t.length with hkdef
          set x := (u.drop (i + 1 - k)).take k with hxdef
          have hxlen : x.length = k := by simp [hxdef]; omega
          have hnb : x ∉ badFactors t := fun hb => hbad (factor_mem hb)
          have hj' : ∃ j, x = t.rotate j := by
            by_contra hne
            push Not at hne
            exact hnb ⟨hxlen, hne⟩
          obtain ⟨j, hj⟩ := hj'
          have hxget : ∀ l (h : l < x.length), x[l] = u[i + 1 - k + l]'(by omega) := by
            intro l h
            simp [hxdef]
          have hlast := rotation_agree (t := t) (x := x) (y := t.rotate ((i + 1 - k) % k)) (n := k - 1)
            (by rw [hj]; exact List.rotate_perm _ _) (List.rotate_perm _ _)
            (by omega) (by simp; omega) (by
              intro l hl
              rw [hxget l (by omega), ih _ (by omega) (by omega), List.getElem_rotate]
              congr 1
              rw [mod_add_comm'])
          rw [hxget _ (by omega)] at hlast
          have e : i + 1 - k + (k - 1) = i := by omega
          simp only [e] at hlast
          rw [hlast, List.getElem_rotate]
          congr 1
          rw [Nat.add_mod_mod]
          congr 1
          omega
    -- the suffix forces a multiple of `k`
    have hlen : t.length ≤ u.length := by subst hpre; simp
    set k := t.length with hkdef
    set n := u.length with hn
    have hrot : t.rotate ((n - k) % k) = t := by
      apply List.ext_getElem (by simp)
      intro l h1 h2
      rw [List.getElem_rotate]
      have := hper (n - k + l) (by simp at h1; omega)
      have hu' : u[n - k + l]'(by simp at h1; omega) = t[l] := by
        subst hsuf
        have hn' := hn
        simp only [List.length_append] at hn'
        rw [List.getElem_append_right (by omega)]
        congr 1
        omega
      rw [← hu', this]
      congr 1
      simp only [hkdef]
      rw [Nat.add_mod_mod, Nat.add_comm]
    have hmod : (n - k) % k = 0 := by
      by_contra hne
      exact hprim _ (Nat.pos_of_ne_zero hne) (Nat.mod_lt _ hk) hrot
    have hdvd : k ∣ n := by
      have : k ∣ n - k := Nat.dvd_of_mod_eq_zero hmod
      have := Nat.dvd_add this (dvd_refl k)
      rwa [Nat.sub_add_cancel hlen] at this
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, List.ext_getElem (by rw [wpow_length, ← hn, hc]; ring) ?_⟩
    intro i h1 h2
    rw [hper i h1, wpow_getElem t hk]

theorem kstar_singleton_starFree [Finite α] [DecidableEq α] (t : List α) (ht : t ≠ [])
    (hprim : ∀ j, 0 < j → j < t.length → t.rotate j ≠ t) :
    HasHeightAtMost ({t} : Language α)∗ 0 := by
  rw [kstar_singleton_eq t ht hprim]
  exact primStarExpr_height t

/-- **Non-constant words of prime length are primitive.** -/
theorem primitive_of_prime_length {t : List α} (hp : t.length.Prime)
    (hnc : ∀ a, t ≠ List.replicate t.length a) :
    ∀ j, 0 < j → j < t.length → t.rotate j ≠ t := by
  intro j hj0 hjp hrot
  set p := t.length with hpdef
  have hp0 : 0 < p := hp.pos
  have hstep : ∀ l (h : l < p), t[(l + j) % p]'(Nat.mod_lt _ hp0) = t[l] := by
    intro l h
    have := List.getElem_rotate t j l (by simpa using h)
    simp only [hrot] at this
    exact this.symm
  have hiter : ∀ c l (h : l < p), t[(l + j * c) % p]'(Nat.mod_lt _ hp0) = t[l] := by
    intro c
    induction c with
    | zero => intro l h; simp [Nat.mod_eq_of_lt h]
    | succ c ih =>
        intro l h
        have e : (l + j * (c + 1)) % p = ((l + j * c) % p + j) % p := by
          rw [Nat.mod_add_mod, mul_add, mul_one, add_assoc]
        simp only [e]
        rw [hstep _ (Nat.mod_lt _ hp0), ih l h]
  obtain ⟨jinv, hjinv⟩ : ∃ m, j * m % p = 1 := by
    have h1 : (j : ZMod p) ≠ 0 := by
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd hj0 h) (by omega)
    have : Fact p.Prime := ⟨hp⟩
    refine ⟨((j : ZMod p)⁻¹).val, ?_⟩
    have : ((j * ((j : ZMod p)⁻¹).val : ℕ) : ZMod p) = 1 := by
      push_cast; rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ h1]
    rw [← ZMod.val_natCast, this, ZMod.val_one]
  apply hnc (t[0]'hp0)
  apply List.ext_getElem (by simp [p])
  intro i h1 h2
  rw [List.getElem_replicate]
  have := hiter (jinv * i) 0 hp0
  rw [← this]
  congr 1
  rw [zero_add, ← mul_assoc, Nat.mul_mod, hjinv, one_mul, Nat.mod_mod, Nat.mod_eq_of_lt h1]

end Primitive

end GeneralizedStarHeight
