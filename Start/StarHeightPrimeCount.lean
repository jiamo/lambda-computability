import Start.StarHeightClosure
import Start.StarHeightTransfer

/-!
# Counting letters read in a given state of a cyclic counter, at height one

The state of a prefix is the number of its *moving* letters modulo a prime `p`.
`pcount mv p h x s w` is the number of positions of `w` that read the letter `x` in state `h`,
when the walk starts in state `s`.

* `pcount_height_one`: for every prime `p`, `h < p`, letter `x` and `r < m`, the words with
  `pcount mv p h x 0 w ≡ r (mod m)` form a language of generalized star height at most one.

The proof follows Pin, Straubing and Thérien (1992): an inverse alphabetic morphism reduces to a
two-letter alphabet (`HasHeightAtMost.invAlph`).

* If `x` moves, every letter of the reduced alphabet moves.  The word splits into `p`-blocks;
  `p · cnt = |v|ₐ + Σₜ cₜ nₜ`, where `nₜ` is the number of blocks equal to `t` and `cₜ = 0` for the
  two constant blocks.  For non-constant `t`, `t∗` is star-free (`t` has prime length, so it is
  primitive) and the Transfer Lemma counts the `t`-blocks at height one.
* If `x` does not move, the first returns to state `0` that do not read `x` in state `0` form a
  star-free code `P`, and the Transfer Lemma counts the `x`-blocks of `({x} ∪ P)∗`
  (PST Proposition 6.6).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

section PCount

variable {α : Type u} [DecidableEq α]

/-- The number of positions of `w` reading `x` in state `h`, starting in state `s`; the state is
the number of moving letters read so far (plus `s`) modulo `p`. -/
def pcount (mv : α → Bool) (p h : ℕ) (x : α) : ℕ → List α → ℕ
  | _, [] => 0
  | s, b :: w => (if b = x ∧ s % p = h then 1 else 0) + pcount mv p h x (if mv b then s + 1 else s) w

variable (mv : α → Bool) (p h : ℕ) (x : α)

lemma pcount_append (s : ℕ) (u w : List α) :
    pcount mv p h x s (u ++ w) = pcount mv p h x s u + pcount mv p h x (s + u.countP mv) w := by
  induction u generalizing s with
  | nil => simp [pcount]
  | cons b u ih =>
      simp only [List.cons_append, pcount, ih, List.countP_cons]
      by_cases hb : mv b <;> simp [hb] <;> ring_nf

lemma pcount_mod_eq {s s' : ℕ} (hs : s % p = s' % p) (w : List α) :
    pcount mv p h x s w = pcount mv p h x s' w := by
  induction w generalizing s s' with
  | nil => rfl
  | cons b w ih =>
      simp only [pcount, hs]
      congr 1
      apply ih
      split_ifs
      · rw [Nat.add_mod, hs, ← Nat.add_mod]
      · exact hs

lemma pcount_shift (hh : h < p) (s d : ℕ) (w : List α) :
    pcount mv p h x s w = pcount mv p ((h + d) % p) x (s + d) w := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
      simp only [pcount]
      congr 1
      · have : s % p = h ↔ (s + d) % p = (h + d) % p := by
          constructor
          · intro e; rw [Nat.add_mod, e, Nat.add_mod h d p, Nat.mod_eq_of_lt hh]
          · intro e
            have h1 : (s + d) % p = (h + d) % p := e
            have := Nat.ModEq.add_right_cancel' d h1
            rw [Nat.ModEq, Nat.mod_eq_of_lt hh] at this
            exact this
        simp only [this]
      · rw [ih]
        split_ifs <;> ring_nf

/-- An alphabetic morphism compatible with the moving letters and the counted letter preserves
the count. -/
lemma pcount_filterMap {β : Type*} [DecidableEq β] (φ : α → Option β) (mvB : β → Bool) (xB : β)
    (h0 : ∀ y, φ y = none → mv y = false ∧ y ≠ x)
    (h1 : ∀ y c, φ y = some c → mv y = mvB c ∧ (y = x ↔ c = xB)) (s : ℕ) (w : List α) :
    pcount mv p h x s w = pcount mvB p h xB s (w.filterMap φ) := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
      cases hb : φ b with
      | none =>
          obtain ⟨hm, hx⟩ := h0 b hb
          rw [List.filterMap_cons, hb, pcount, ite_eq_right (fun h => hx h.1), hm, ih]
          simp
      | some c =>
          obtain ⟨hm, hx⟩ := h1 b c hb
          rw [List.filterMap_cons, hb, pcount, pcount, hm, ih]
          simp only [hx]

lemma pcount_zero_of_avoid :
    ∀ (w : List α) (s : ℕ), (∀ i, s ≤ i → i ≤ s + w.countP mv → i % p ≠ h) →
      pcount mv p h x s w = 0
  | [], _, _ => rfl
  | b :: w, s, hs => by
      rw [pcount]
      have hs0 : s % p ≠ h := hs s le_rfl (by omega)
      rw [ite_eq_right (fun h' => hs0 h'.2), zero_add]
      apply pcount_zero_of_avoid w
      intro i hi1 hi2
      apply hs i
      · split_ifs at hi1 <;> omega
      · rw [List.countP_cons]; split_ifs at hi2 ⊢ <;> omega

lemma pcount_zero_of_avoid_len (hmv : ∀ b, mv b = true) :
    ∀ (w : List α) (s : ℕ), (∀ i, s ≤ i → i < s + w.length → i % p ≠ h) →
      pcount mv p h x s w = 0
  | [], _, _ => rfl
  | b :: w, s, hs => by
      rw [pcount]
      have hs0 : s % p ≠ h := hs s le_rfl (by simp)
      rw [ite_eq_right (fun h' => hs0 h'.2), zero_add, ite_eq_left (hmv b)]
      apply pcount_zero_of_avoid_len hmv w
      intro i hi1 hi2
      exact hs i (by omega) (by simp; omega)

end PCount

lemma mod_arith_sub {a b m r : ℕ} (hm : 0 < m) (h : (a + b) % m = r) :
    a % m = (r + m - b % m) % m := by
  have hb : b % m < m := Nat.mod_lt _ hm
  have h1 : a + b % m ≡ (r + m - b % m) + b % m [MOD m] := by
    have e1 : (r + m - b % m) + b % m = r + m := by
      have : r < m := h ▸ Nat.mod_lt _ hm
      omega
    rw [e1]
    calc a + b % m ≡ a + b [MOD m] := Nat.ModEq.add_left _ (Nat.mod_modEq b m)
      _ ≡ r [MOD m] := by rw [Nat.ModEq, h, Nat.mod_eq_of_lt (h ▸ Nat.mod_lt _ hm)]
      _ ≡ r + m [MOD m] := by simp [Nat.ModEq]
  exact Nat.ModEq.add_right_cancel' _ h1

lemma mod_arith_add {a b m r : ℕ} (hm : 0 < m) (hr : r < m) (h : a % m = (r + m - b % m) % m) :
    (a + b) % m = r := by
  have hb : b % m < m := Nat.mod_lt _ hm
  rw [Nat.add_mod, h, Nat.mod_add_mod, show r + m - b % m + b % m = r + m by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt hr]

/-! ### Height one for the reduced alphabets -/

section Reduced

open Classical

variable {p : ℕ}

/-! #### Every letter moves -/

/-- Blocks of length `p`. -/
def pblocks (p : ℕ) : Language Bool := {e | e.length = p}

lemma pblocks_prefixCode (hp : 0 < p) : PrefixCode (pblocks p) := by
  refine ⟨fun h => by
    have h' : ([] : List Bool).length = p := h
    simp at h'; omega, fun e he f hf hef => ?_⟩
  exact hef.eq_of_length (by rw [he, hf])

lemma pblocks_height (n : ℕ) : HasHeightAtMost (pblocks p) n :=
  HasHeightAtMost.finite _ (List.finite_length_eq Bool p) n

lemma mem_pblocks_kstar : ∀ (c : ℕ) (v : List Bool), v.length = p * c → v ∈ (pblocks p)∗
  | 0, v, h => by
      rw [mul_zero, List.length_eq_zero_iff] at h
      subst h; exact Language.nil_mem_kstar _
  | c + 1, v, h => by
      have h1 := mem_pblocks_kstar c (v.drop p) (by rw [List.length_drop, h, Nat.mul_succ,
        Nat.add_sub_cancel])
      obtain ⟨S, hS, hS'⟩ := Language.mem_kstar.mp h1
      refine Language.mem_kstar.mpr ⟨v.take p :: S, ?_, ?_⟩
      · rw [List.flatten_cons, ← hS, List.take_append_drop]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · show (v.take p).length = p
          rw [List.length_take, h]
          exact min_eq_left (Nat.le_mul_of_pos_right p (Nat.succ_pos c))
        · exact hS' y hy

/-- All letters move. -/
abbrev allMv : Bool → Bool := fun _ => true

lemma pcount_flatten_blocks (h : ℕ) :
    ∀ es : List (List Bool), AllIn (pblocks p) es →
      pcount allMv p h true 0 es.flatten = (es.map (pcount allMv p h true 0)).sum
  | [], _ => rfl
  | e :: es, hes => by
      have he : e.length = p := hes e (by simp)
      rw [List.flatten_cons, pcount_append, List.map_cons, List.sum_cons,
        pcount_mod_eq allMv p h true (s := 0 + List.countP allMv e) (s' := 0) (by simp [he])
          es.flatten, pcount_flatten_blocks h es (fun f hf => hes f (by simp [hf]))]

lemma count_flatten (es : List (List Bool)) :
    es.flatten.count true = (es.map (List.count true)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [List.count_append, ih]

lemma pcount_block {h : ℕ} (hh : h < p) (e : List Bool) (he : e.length = p) :
    pcount allMv p h true 0 e = if e[h]'(by omega) = true then 1 else 0 := by
  have hsplit : e = e.take h ++ (e[h]'(by omega) :: e.drop (h + 1)) := by
    conv_lhs => rw [← List.take_append_drop h e]
    rw [List.drop_eq_getElem_cons (by omega)]
  have hlt : (e.take h).length = h := by simp; omega
  conv_lhs => rw [hsplit]
  rw [pcount_append, pcount_zero_of_avoid_len allMv p h true (fun _ => rfl) (e.take h) 0 (by
      intro i _ hi; rw [hlt] at hi; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
  have hc : List.countP allMv (e.take h) = h := by rw [List.countP_true, hlt]
  rw [hc, pcount]
  simp only [Nat.zero_add, Nat.mod_eq_of_lt hh, and_true, ↓reduceIte]
  rw [pcount_zero_of_avoid_len allMv p h true (fun _ => rfl) (e.drop (h + 1)) (h + 1) (by
      intro i hi1 hi2; rw [List.length_drop, he] at hi2; rw [Nat.mod_eq_of_lt (by omega)]; omega)]
  simp

/-- The constant blocks. -/
def ConstBlock (t : List.Vector Bool p) : Prop := ∃ a, t.toList = List.replicate p a

/-- The coefficient `cₜ = p·[t_h = true] − |t|_true`. -/
def coef (p h : ℕ) (e : List Bool) : ℤ :=
  (p : ℤ) * pcount allMv p h true 0 e - (e.count true : ℤ)

lemma coef_const {h : ℕ} (hh : h < p) {t : List.Vector Bool p} (ht : ConstBlock t) :
    coef p h t.toList = 0 := by
  obtain ⟨a, ha⟩ := ht
  unfold coef
  rw [ha, pcount_block hh _ (by simp)]
  cases a <;> simp [List.count_replicate]

lemma sum_blocks (f : List Bool → ℤ) :
    ∀ es : List (List Bool), AllIn (pblocks p) es →
      (es.map f).sum = ∑ t : List.Vector Bool p, f t.toList * (bcount {t.toList} es : ℤ)
  | [], _ => by simp [bcount]
  | e :: es, hes => by
      have he : e.length = p := hes e (by simp)
      rw [List.map_cons, List.sum_cons, sum_blocks f es (fun g hg => hes g (by simp [hg]))]
      let t0 : List.Vector Bool p := ⟨e, he⟩
      have hsplit : ∀ t : List.Vector Bool p, f t.toList * (bcount {t.toList} (e :: es) : ℤ) =
          (if t = t0 then f e else 0) + f t.toList * (bcount {t.toList} es : ℤ) := by
        intro t
        unfold bcount
        rw [List.countP_cons]
        by_cases h : t = t0
        · subst h
          have hm : e ∈ ({t0.toList} : Language Bool) := rfl
          simp only [hm, decide_true, ite_true]
          have : t0.toList = e := rfl
          rw [this]
          push_cast; ring
        · have hne : ¬ e ∈ ({t.toList} : Language Bool) := fun h' => h (Subtype.ext h'.symm)
          rw [ite_eq_right (fun hc => hne (of_decide_eq_true hc)), ite_eq_right h]
          simp
      rw [Finset.sum_congr rfl (fun t _ => hsplit t), Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ]
      simp

lemma block_identity_aux {h : ℕ} :
    ∀ es : List (List Bool), AllIn (pblocks p) es →
      (p : ℤ) * pcount allMv p h true 0 es.flatten =
        (es.flatten.count true : ℤ) + (es.map (coef p h)).sum
  | [], _ => by simp [pcount]
  | e :: es, hes => by
      have he : e.length = p := hes e (by simp)
      have ih := block_identity_aux (h := h) es (fun f hf => hes f (by simp [hf]))
      have hpc : pcount allMv p h true 0 (e ++ es.flatten) =
          pcount allMv p h true 0 e + pcount allMv p h true 0 es.flatten := by
        rw [pcount_append]
        congr 1
        apply pcount_mod_eq
        simp [he]
      have hce : coef p h e = (p : ℤ) * pcount allMv p h true 0 e - (e.count true : ℤ) := rfl
      rw [List.flatten_cons, hpc, List.count_append, List.map_cons, List.sum_cons, hce]
      push_cast
      linarith

lemma block_identity {h : ℕ} (es : List (List Bool)) (hes : AllIn (pblocks p) es) :
    (p : ℤ) * pcount allMv p h true 0 es.flatten =
      (es.flatten.count true : ℤ) +
        ∑ t : List.Vector Bool p, coef p h t.toList * (bcount {t.toList} es : ℤ) := by
  rw [← sum_blocks _ es hes]
  exact block_identity_aux (h := h) es hes

lemma zmod_mul_iff {p m k n : ℕ} (hp : 0 < p) (hk : k < m) :
    ((p * n : ℕ) : ZMod (p * m)) = ((p * k : ℕ) : ZMod (p * m)) ↔ n % m = k := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
    Nat.mod_eq_of_lt hk]
  constructor
  · intro h; exact Nat.eq_of_mul_eq_mul_left hp h
  · intro h; rw [h]

/-- Words of `(Aᵖ)∗` whose count is `k` modulo `m`. -/
def Vlang (p h m k : ℕ) : Language Bool :=
  {v | v ∈ (pblocks p)∗ ∧ pcount allMv p h true 0 v % m = k}

/-- Admissible residues of the letter count and of the block counts. -/
def VIdx (p h m k : ℕ) :=
  {z : (List.Vector Bool p → Fin (p * m)) × Fin (p * m) //
    ((z.2 : ℕ) : ZMod (p * m)) +
      ∑ t : List.Vector Bool p, ((coef p h t.toList : ℤ) : ZMod (p * m)) * ((z.1 t : ℕ) : ZMod (p * m))
      = ((p * k : ℕ) : ZMod (p * m))}

instance (p h m k : ℕ) : Finite (VIdx p h m k) := by unfold VIdx; infer_instance

lemma cast_identity {h : ℕ} (es : List (List Bool)) (hes : AllIn (pblocks p) es) (n : ℕ) :
    ((p * pcount allMv p h true 0 es.flatten : ℕ) : ZMod n) =
      ((es.flatten.count true : ℕ) : ZMod n) +
        ∑ t : List.Vector Bool p, ((coef p h t.toList : ℤ) : ZMod n) *
          ((bcount {t.toList} es : ℕ) : ZMod n) := by
  have := congrArg (fun z : ℤ => (z : ZMod n)) (block_identity (h := h) es hes)
  push_cast at this ⊢
  exact this

lemma Vlang_eq {h m k : ℕ} (hp : 0 < p) (hh : h < p) (hk : k < m) :
    Vlang p h m k = ⨆ z : VIdx p h m k,
      ((pblocks p)∗ ⊓ {v | v.count true % (p * m) = z.1.2} ⊓
        ⨅ t : {t : List.Vector Bool p // ¬ ConstBlock t},
          bmod (pblocks p) {t.1.toList} (p * m) (z.1.1 t.1)) := by
  have hpm : 0 < p * m := Nat.mul_pos hp (by omega)
  ext v
  constructor
  · rintro ⟨hv, hk'⟩
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hv
    let z1 : List.Vector Bool p → Fin (p * m) :=
      fun t => ⟨bcount {t.toList} es % (p * m), Nat.mod_lt _ hpm⟩
    let z2 : Fin (p * m) := ⟨es.flatten.count true % (p * m), Nat.mod_lt _ hpm⟩
    have hz : ((z2 : ℕ) : ZMod (p * m)) +
        ∑ t : List.Vector Bool p, ((coef p h t.toList : ℤ) : ZMod (p * m)) *
          ((z1 t : ℕ) : ZMod (p * m)) = ((p * k : ℕ) : ZMod (p * m)) := by
      simp only [z1, z2, ZMod.natCast_mod]
      rw [← cast_identity es hes, zmod_mul_iff hp hk]
      exact hk'
    refine Language.mem_iSup.mpr ⟨⟨(z1, z2), hz⟩, ⟨⟨hv, rfl⟩, ?_⟩⟩
    exact HasHeightAtMost.mem_iInf_lang.mpr fun t => ⟨es, hes, rfl, rfl⟩
  · intro hv
    obtain ⟨⟨⟨z1, z2⟩, hz⟩, ⟨hstar, hcount⟩, hb⟩ := Language.mem_iSup.mp hv
    have hb' := HasHeightAtMost.mem_iInf_lang.mp hb
    refine ⟨hstar, ?_⟩
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hstar
    rw [← zmod_mul_iff hp hk, cast_identity es hes, ← hz]
    simp only at hcount ⊢
    rw [← hcount, ZMod.natCast_mod]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : ConstBlock t
    · rw [coef_const hh ht]; simp
    · obtain ⟨fs, hfs, hflat, hcnt⟩ := hb' ⟨t, ht⟩
      have := flatten_injective (pblocks_prefixCode hp) hfs hes hflat
      subst this
      simp only at hcnt
      rw [← hcnt, ZMod.natCast_mod]

lemma pblocks_split (t : List.Vector Bool p) :
    pblocks p = {t.toList} + (pblocks p ⊓ ({t.toList} : Language Bool)ᶜ) := by
  ext e
  simp only [Language.mem_add]
  constructor
  · intro he
    by_cases h : e = t.toList
    · left; exact h
    · right; exact ⟨he, h⟩
  · rintro (h | h)
    · have h' : e = t.toList := h
      show e.length = p
      rw [h']; simp
    · exact h.1

lemma bmod_block_height (hp : p.Prime) (t : List.Vector Bool p) (ht : ¬ ConstBlock t)
    {n k : ℕ} (hk : k < n) : HasHeightAtMost (bmod (pblocks p) {t.toList} n k) 1 := by
  have hp0 : 0 < p := hp.pos
  rw [pblocks_split t]
  have hlen : t.toList.length = p := by simp
  refine transfer_height_one ?_ ?_ (HasHeightAtMost.singleton _ 0)
    (HasHeightAtMost.finite _ ((List.finite_length_eq Bool p).subset fun x hx => hx.1) 0) ?_ hk
  · rw [← pblocks_split t]; exact pblocks_prefixCode hp0
  · exact Set.disjoint_left.mpr (fun e h1 h2 => h2.2 h1)
  · refine kstar_singleton_starFree _ (by intro h; rw [h] at hlen; simp at hlen; omega) ?_
    refine primitive_of_prime_length (by rw [hlen]; exact hp) ?_
    intro a ha
    exact ht ⟨a, by rw [ha, hlen]⟩

theorem Vlang_height {h m k : ℕ} (hp : p.Prime) (hh : h < p) (hk : k < m) :
    HasHeightAtMost (Vlang p h m k) 1 := by
  have hp0 : 0 < p := hp.pos
  rw [Vlang_eq hp0 hh hk]
  refine HasHeightAtMost.iSup _ fun z => ?_
  refine HasHeightAtMost.inter (HasHeightAtMost.inter ?_ ?_) ?_
  · exact (pblocks_height 0).star
  · exact countMod_height true (Nat.mul_pos hp0 (by omega)) _ z.1.2.2
  · exact HasHeightAtMost.iInf _ fun t => bmod_block_height hp t.1 t.2 (z.1.1 t.1).2

/-- **Case (a)**: every letter moves. -/
def Alang (p h m r : ℕ) : Language Bool := {u | pcount allMv p h true 0 u % m = r}

lemma Alang_eq {h m r : ℕ} (hp : 0 < p) (hm : 0 < m) (hr : r < m) :
    Alang p h m r = ⨆ y : Fin p × List.Vector Bool p,
      Vlang p h m ((r + m - pcount allMv p h true 0 (y.2.toList.take y.1) % m) % m) *
        {y.2.toList.take y.1} := by
  ext u
  constructor
  · intro hu
    set c := u.length / p
    set v := u.take (p * c)
    set y := u.drop (p * c)
    have hvlen : v.length = p * c := by
      simp only [v, List.length_take]
      exact min_eq_left (Nat.mul_div_le _ _)
    have hylen : y.length < p := by
      simp only [y, List.length_drop, c]
      have := Nat.div_add_mod u.length p
      have := Nat.mod_lt u.length hp
      omega
    let yv : List.Vector Bool p := ⟨y ++ List.replicate (p - y.length) false, by simp; omega⟩
    have hyv : yv.toList.take y.length = y := by simp [yv]
    have hsplit : pcount allMv p h true 0 u =
        pcount allMv p h true 0 v + pcount allMv p h true 0 y := by
      conv_lhs => rw [← List.take_append_drop (p * c) u]
      rw [pcount_append]
      congr 1
      apply pcount_mod_eq
      rw [List.countP_true]
      change (0 + v.length) % p = 0 % p
      rw [hvlen]; simp
    refine Language.mem_iSup.mpr ⟨(⟨y.length, hylen⟩, yv), ?_⟩
    simp only [hyv]
    refine Language.mem_mul.mpr ⟨v, ⟨mem_pblocks_kstar c v hvlen, ?_⟩, y, rfl,
      List.take_append_drop _ _⟩
    apply mod_arith_sub hm
    rw [← hsplit]; exact hu
  · intro hu
    obtain ⟨y, hy⟩ := Language.mem_iSup.mp hu
    obtain ⟨v, ⟨hv, hvk⟩, y', hy', rfl⟩ := Language.mem_mul.mp hy
    have hy'' : y' = y.2.toList.take y.1 := hy'
    subst hy''
    show pcount allMv p h true 0 (v ++ _) % m = r
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hv
    rw [pcount_append]
    have : pcount allMv p h true (0 + List.countP allMv es.flatten)
        (y.2.toList.take y.1) = pcount allMv p h true 0 (y.2.toList.take y.1) := by
      apply pcount_mod_eq
      simp only [List.countP_true, zero_add, Nat.zero_mod]
      obtain ⟨c, hc⟩ : p ∣ es.flatten.length := by
        rw [List.length_flatten]
        apply List.dvd_sum
        intro n hn
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
        rw [hes e he]
      rw [hc, Nat.mul_mod_right]
    rw [this]
    exact mod_arith_add hm hr hvk

theorem Alang_height {h m r : ℕ} (hp : p.Prime) (hh : h < p) (hm : 0 < m) (hr : r < m) :
    HasHeightAtMost (Alang p h m r) 1 := by
  rw [Alang_eq hp.pos hm hr]
  exact HasHeightAtMost.iSup _ fun y =>
    (Vlang_height hp hh (Nat.mod_lt _ hm)).concat (HasHeightAtMost.singleton _ 1)

/-! #### Only `false` moves, and `true` is counted -/

/-- `false` moves, `true` does not. -/
abbrev nmv : Bool → Bool := fun c => !c

lemma countP_nmv (w : List Bool) : w.countP nmv = w.count false := by
  rw [List.count_eq_countP]
  congr 1
  funext c
  cases c <;> rfl

lemma pcount_cons_ne {mv : Bool → Bool} {q h : ℕ} {x b : Bool} (hb : b ≠ x) (s : ℕ)
    (w : List Bool) :
    pcount mv q h x s (b :: w) = pcount mv q h x (if mv b then s + 1 else s) w := by
  rw [pcount, ite_eq_right (fun h' => hb h'.1), zero_add]

/-- First returns to state `0` that read no `true` in state `0`. -/
def Pblk (p : ℕ) : Language Bool := {[false]} * countIs false (p - 2) * {[false]}

/-- The code `{true} ∪ P`. -/
def Eb (p : ℕ) : Language Bool := {[true]} + Pblk p

/-- Proper prefixes of `P`-blocks. -/
def Pref (p : ℕ) : Language Bool := 1 + {[false]} * ⨆ k : Fin (p - 1), countIs false k

lemma mem_Pblk {e : List Bool} :
    e ∈ Pblk p ↔ ∃ z, z.count false = p - 2 ∧ e = false :: (z ++ [false]) := by
  constructor
  · intro he
    obtain ⟨xz, hxz, f, hf, rfl⟩ := Language.mem_mul.mp he
    obtain ⟨x, hx, z, hz, rfl⟩ := Language.mem_mul.mp hxz
    have hx' : x = [false] := hx
    have hf' : f = [false] := hf
    subst hx' hf'
    exact ⟨z, hz, by simp⟩
  · rintro ⟨z, hz, rfl⟩
    exact Language.mem_mul.mpr ⟨[false] ++ z, Language.mem_mul.mpr ⟨[false], rfl, z, hz, rfl⟩,
      [false], rfl, by simp⟩

lemma Pblk_count (hp : 2 ≤ p) {e : List Bool} (he : e ∈ Pblk p) : e.count false = p := by
  obtain ⟨z, hz, rfl⟩ := mem_Pblk.mp he
  simp [List.count_append, hz]; omega

lemma Pblk_pcount (hp : 2 ≤ p) {e : List Bool} (he : e ∈ Pblk p) {s : ℕ} (hs : s % p = 0) :
    pcount nmv p 0 true s e = 0 := by
  obtain ⟨z, hz, rfl⟩ := mem_Pblk.mp he
  rw [pcount_cons_ne (by decide), pcount_append, pcount_cons_ne (by decide)]
  simp only [nmv, Bool.not_false, ite_true]
  rw [pcount_zero_of_avoid]
  · rfl
  · intro i hi1 hi2
    rw [countP_nmv, hz] at hi2
    intro hi
    have h1 : p ∣ i := Nat.dvd_of_mod_eq_zero hi
    have h2 : p ∣ s := Nat.dvd_of_mod_eq_zero hs
    obtain ⟨a, ha⟩ := h1
    obtain ⟨b, hb⟩ := h2
    have : b < a := by
      by_contra hab; push Not at hab
      have := Nat.mul_le_mul_left p hab; omega
    have : p * (b + 1) ≤ p * a := Nat.mul_le_mul_left p this
    rw [mul_add] at this; omega

lemma Eb_prefixCode (hp : 2 ≤ p) : PrefixCode (Eb p) := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases (Language.mem_add _ _ _).mp h with h | h
    · have h' : ([] : List Bool) = [true] := h
      cases h'
    · obtain ⟨z, -, hz⟩ := mem_Pblk.mp h
      simp at hz
  · intro e he f hf hef
    rcases (Language.mem_add _ _ _).mp he with he | he <;>
      rcases (Language.mem_add _ _ _).mp hf with hf | hf
    · exact (he : e = [true]).trans (hf : f = [true]).symm
    · have he' : e = [true] := he
      obtain ⟨z, -, rfl⟩ := mem_Pblk.mp hf
      subst he'
      simp at hef
    · have hf' : f = [true] := hf
      obtain ⟨z, -, rfl⟩ := mem_Pblk.mp he
      subst hf'
      simp at hef
    · obtain ⟨rest, rfl⟩ := hef
      have hc := Pblk_count hp hf
      rw [List.count_append, Pblk_count hp he] at hc
      rcases List.eq_nil_or_concat rest with h | ⟨L, b, rfl⟩
      · subst h; simp
      · obtain ⟨z', -, hz'⟩ := mem_Pblk.mp hf
        have hz'' : (e ++ L) ++ [b] = (false :: z') ++ [false] := by simpa using hz'
        have := List.append_inj' hz'' rfl
        have hb : b = false := by simpa using this.2
        subst hb
        simp [List.count_append] at hc

lemma pcount_flatten_Eb (hp : 2 ≤ p) :
    ∀ es : List (List Bool), AllIn (Eb p) es → ∀ s, s % p = 0 →
      pcount nmv p 0 true s es.flatten = bcount {[true]} es ∧
        (s + es.flatten.countP nmv) % p = 0
  | [], _, s, hs => by simp [pcount, bcount, hs]
  | e :: es, hes, s, hs => by
      have ih := pcount_flatten_Eb hp es (fun f hf => hes f (by simp [hf]))
      rw [List.flatten_cons, pcount_append]
      rcases (Language.mem_add _ _ _).mp (hes e (by simp)) with he | he
      · have he' : e = [true] := he
        subst he'
        have hcp : List.countP nmv [true] = 0 := rfl
        obtain ⟨h1, h2⟩ := ih (s + 0) (by simpa using hs)
        rw [hcp, h1]
        refine ⟨?_, ?_⟩
        · have hp1 : pcount nmv p 0 true s [true] = 1 := by simp [pcount, hs]
          rw [hp1]
          unfold bcount
          rw [List.countP_cons]
          simp only [show ([true] : List Bool) ∈ ({[true]} : Language Bool) from rfl,
            decide_true, ite_true]
          omega
        · rw [List.countP_append, hcp]; simpa using h2
      · have hcp : e.countP nmv = p := by rw [countP_nmv]; exact Pblk_count hp he
        obtain ⟨h1, h2⟩ := ih (s + p) (by simp [hs])
        rw [hcp, h1, Pblk_pcount hp he hs]
        have hne : e ∉ ({[true]} : Language Bool) := by
          intro h
          obtain ⟨z, -, hz⟩ := mem_Pblk.mp he
          have h' : e = [true] := h
          rw [hz] at h'
          simp at h'
        refine ⟨?_, ?_⟩
        · unfold bcount
          rw [List.countP_cons, ite_eq_right (fun hc => hne (of_decide_eq_true hc))]
          omega
        · rw [List.countP_append, hcp, ← add_assoc]; exact h2

lemma Pref_pcount (hp : 2 ≤ p) {y : List Bool} (hy : y ∈ Pref p) {s : ℕ} (hs : s % p = 0) :
    pcount nmv p 0 true s y = 0 := by
  rcases (Language.mem_add _ _ _).mp hy with hy | hy
  · rw [(Language.mem_one _).mp hy]; rfl
  obtain ⟨f, hf, z, hz, rfl⟩ := Language.mem_mul.mp hy
  have hf' : f = [false] := hf
  subst hf'
  obtain ⟨k, hk⟩ := Language.mem_iSup.mp hz
  have hk' : z.count false = k := hk
  rw [List.singleton_append, pcount_cons_ne (by decide)]
  simp only [nmv, Bool.not_false, ite_true]
  apply pcount_zero_of_avoid
  intro i hi1 hi2 hi
  rw [countP_nmv, hk'] at hi2
  have := k.2
  obtain ⟨a, ha⟩ := Nat.dvd_of_mod_eq_zero hi
  obtain ⟨b, hb⟩ := Nat.dvd_of_mod_eq_zero hs
  have : b < a := by
    by_contra hab; push Not at hab
    have := Nat.mul_le_mul_left p hab; omega
  have : p * (b + 1) ≤ p * a := Nat.mul_le_mul_left p this
  rw [mul_add] at this; omega

lemma decomp_Eb (hp : 2 ≤ p) : ∀ (n : ℕ) (w : List Bool), w.length ≤ n →
    ∃ es y, AllIn (Eb p) es ∧ y ∈ Pref p ∧ w = es.flatten ++ y
  | _, [], _ => ⟨[], [], by simp [AllIn], (Language.mem_add _ _ _).mpr
      (Or.inl ((Language.mem_one _).mpr rfl)), rfl⟩
  | 0, b :: w, h => by simp at h
  | n + 1, true :: w, h => by
      obtain ⟨es, y, hes, hy, rfl⟩ := decomp_Eb hp n w (by simpa using h)
      refine ⟨[true] :: es, y, ?_, hy, rfl⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact (Language.mem_add _ _ _).mpr (Or.inl rfl)
      · exact hes e he
  | n + 1, false :: w, h => by
      by_cases hc : w.count false < p - 1
      · refine ⟨[], false :: w, by simp [AllIn], (Language.mem_add _ _ _).mpr (Or.inr ?_), rfl⟩
        exact Language.mem_mul.mpr ⟨[false], rfl, w,
          Language.mem_iSup.mpr ⟨⟨w.count false, hc⟩, rfl⟩, rfl⟩
      · push Not at hc
        obtain ⟨y₁, z, rfl, hy₁, v, rfl⟩ := exists_split_count false w (p - 1) (by omega) hc
        obtain ⟨es, y, hes, hy, hz⟩ := decomp_Eb hp n z (by simp at h; omega)
        refine ⟨(false :: (v ++ [false])) :: es, y, ?_, hy, by simp [hz]⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · refine (Language.mem_add _ _ _).mpr (Or.inr (mem_Pblk.mpr ⟨v, ?_, rfl⟩))
          simp [List.count_append] at hy₁; omega
        · exact hes e he

/-- **Case (b)** in state `0`. -/
def B0lang (p m r : ℕ) : Language Bool := {w | pcount nmv p 0 true 0 w % m = r}

lemma B0lang_eq (hp : 2 ≤ p) (m r : ℕ) :
    B0lang p m r = bmod (Eb p) {[true]} m r * Pref p := by
  ext w
  constructor
  · intro hw
    obtain ⟨es, y, hes, hy, rfl⟩ := decomp_Eb hp _ w le_rfl
    obtain ⟨h1, h2⟩ := pcount_flatten_Eb hp es hes 0 rfl
    have hw' : pcount nmv p 0 true 0 (es.flatten ++ y) % m = r := hw
    rw [pcount_append, h1, Pref_pcount hp hy h2, add_zero] at hw'
    exact Language.mem_mul.mpr ⟨_, ⟨es, hes, rfl, hw'⟩, y, hy, rfl⟩
  · intro hw
    obtain ⟨v, ⟨es, hes, rfl, hk⟩, y, hy, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨h1, h2⟩ := pcount_flatten_Eb hp es hes 0 rfl
    show pcount nmv p 0 true 0 (es.flatten ++ y) % m = r
    rw [pcount_append, h1, Pref_pcount hp hy h2, add_zero]
    exact hk

theorem B0lang_height (hp : 2 ≤ p) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (B0lang p m r) 1 := by
  rw [B0lang_eq hp]
  refine HasHeightAtMost.concat ?_ ?_
  · refine transfer_height_one (Eb_prefixCode hp) ?_ (HasHeightAtMost.singleton _ 0) ?_ ?_ hr
    · refine Set.disjoint_left.mpr (fun e h1 h2 => ?_)
      obtain ⟨z, -, hz⟩ := mem_Pblk.mp h2
      have h1' : e = [true] := h1
      rw [hz] at h1'
      simp at h1'
    · exact ((HasHeightAtMost.singleton _ 0).concat (countIs_height false _)).concat
        (HasHeightAtMost.singleton _ 0)
    · exact kstar_singleton_starFree [true] (by simp) (fun j hj hj' => by simp at hj'; omega)
  · exact ((HasHeightAtMost.one 0).union ((HasHeightAtMost.singleton _ 0).concat
      (HasHeightAtMost.iSup _ fun k : Fin (p - 1) => countIs_height false (k : ℕ)))).mono
      (by omega)

/-- **Case (b)** in state `h`. -/
def Blang (p h m r : ℕ) : Language Bool := {w | pcount nmv p h true 0 w % m = r}

lemma Blang_eq {h : ℕ} (h0 : 0 < h) (hh : h < p) {m r : ℕ} (hr : r < m) :
    Blang p h m r = (if r = 0 then ⨆ k : Fin h, countIs false k else 0) +
      countBlock false h * B0lang p m r := by
  have hshift : ∀ z : List Bool, pcount nmv p h true h z = pcount nmv p 0 true 0 z := by
    intro z
    rw [pcount_shift nmv p h true hh h (p - h), show h + (p - h) = p by omega, Nat.mod_self]
    exact pcount_mod_eq _ _ _ _ (by simp) z
  ext w
  simp only [Language.mem_add]
  constructor
  · intro hw
    have hw' : pcount nmv p h true 0 w % m = r := hw
    by_cases hc : w.count false < h
    · left
      have hz : pcount nmv p h true 0 w = 0 := by
        apply pcount_zero_of_avoid
        intro i _ hi2
        rw [countP_nmv] at hi2
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hz, Nat.zero_mod] at hw'
      subst hw'
      rw [ite_eq_left rfl]
      exact Language.mem_iSup.mpr ⟨⟨_, hc⟩, rfl⟩
    · right
      push Not at hc
      obtain ⟨y, z, rfl, hy, v, rfl⟩ := exists_split_count false w h h0 hc
      refine Language.mem_mul.mpr ⟨v ++ [false], ⟨hy, v, rfl⟩, z, ?_, rfl⟩
      show pcount nmv p 0 true 0 z % m = r
      rw [pcount_append, pcount_append, countP_nmv, countP_nmv] at hw'
      have hv : v.count false + 1 = h := by simp [List.count_append] at hy; omega
      rw [pcount_zero_of_avoid nmv p h true v 0 (by
          intro i _ hi2; rw [countP_nmv] at hi2
          rw [Nat.mod_eq_of_lt (by omega)]; omega),
        pcount_cons_ne (by decide), show pcount nmv p h true _ [] = 0 from rfl,
        List.count_append, show [false].count false = 1 from rfl, zero_add, hv] at hw'
      simp only [Nat.zero_add, hshift] at hw'
      exact hw'
  · rintro (hw | hw)
    · split_ifs at hw with hr0
      · subst hr0
        obtain ⟨k, hk⟩ := Language.mem_iSup.mp hw
        have hk' : w.count false = k := hk
        show pcount nmv p h true 0 w % m = 0
        rw [pcount_zero_of_avoid]
        · simp
        · intro i _ hi2
          rw [countP_nmv, hk'] at hi2
          have := k.2
          rw [Nat.mod_eq_of_lt (by omega)]; omega
      · exact absurd hw (Language.notMem_zero _)
    · obtain ⟨y, ⟨hy, v, rfl⟩, z, hz, rfl⟩ := Language.mem_mul.mp hw
      show pcount nmv p h true 0 (v ++ [false] ++ z) % m = r
      have hv : v.count false + 1 = h := by simp [List.count_append] at hy; omega
      rw [pcount_append, pcount_append, countP_nmv, countP_nmv,
        pcount_zero_of_avoid nmv p h true v 0 (by
          intro i _ hi2; rw [countP_nmv] at hi2
          rw [Nat.mod_eq_of_lt (by omega)]; omega),
        pcount_cons_ne (by decide), show pcount nmv p h true _ [] = 0 from rfl,
        List.count_append, show [false].count false = 1 from rfl, zero_add, hv]
      simp only [Nat.zero_add, hshift]
      exact hz

theorem Blang_height (hp : 2 ≤ p) {h : ℕ} (hh : h < p) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (Blang p h m r) 1 := by
  rcases Nat.eq_zero_or_pos h with h0 | h0
  · subst h0; exact B0lang_height hp hr
  rw [Blang_eq h0 hh hr]
  refine HasHeightAtMost.union ?_
    (((countBlock_height false h).mono (Nat.zero_le 1)).concat (B0lang_height hp hr))
  split_ifs
  · exact HasHeightAtMost.iSup _ fun k : Fin h => (countIs_height false (k : ℕ)).mono (by omega)
  · exact HasHeightAtMost.zero 1

end Reduced

/-! ### The general alphabet -/

/-- **Counting the letters read in a given state has height one.** -/
theorem pcount_height_one {α : Type u} [Finite α] [DecidableEq α] (mv : α → Bool) {p : ℕ}
    (hp : p.Prime) {h : ℕ} (hh : h < p) (x : α) {m r : ℕ} (hm : 0 < m) (hr : r < m) :
    HasHeightAtMost {w : List α | pcount mv p h x 0 w % m = r} 1 := by
  let φ : α → Option Bool := fun y => if y = x then some true else if mv y then some false else none
  by_cases hx : mv x = true
  · have heq : {w : List α | pcount mv p h x 0 w % m = r} = invAlph φ (Alang p h m r) := by
      ext w
      show _ % m = r ↔ pcount allMv p h true 0 (w.filterMap φ) % m = r
      rw [pcount_filterMap mv p h x φ allMv true]
      · intro y hy
        simp only [φ] at hy
        split_ifs at hy with h1 h2
        exact ⟨by simpa using h2, h1⟩
      · intro y c hy
        simp only [φ] at hy
        split_ifs at hy with h1 h2 <;> simp at hy <;> subst hy
        · subst h1; exact ⟨hx, by simp⟩
        · exact ⟨h2, by simp [h1]⟩
    rw [heq]
    exact (Alang_height hp hh hm hr).invAlph φ
  · have heq : {w : List α | pcount mv p h x 0 w % m = r} = invAlph φ (Blang p h m r) := by
      ext w
      show _ % m = r ↔ pcount nmv p h true 0 (w.filterMap φ) % m = r
      rw [pcount_filterMap mv p h x φ nmv true]
      · intro y hy
        simp only [φ] at hy
        split_ifs at hy with h1 h2
        exact ⟨by simpa using h2, h1⟩
      · intro y c hy
        simp only [φ] at hy
        split_ifs at hy with h1 h2 <;> simp at hy <;> subst hy
        · subst h1; exact ⟨by simpa using hx, by simp⟩
        · exact ⟨h2, by simp [h1]⟩
    rw [heq]
    exact (Blang_height hp.two_le hh hr).invAlph φ

end GeneralizedStarHeight
