import Start.StarHeightIndexFour

/-!
# The `Z₄` core: the cases without a letter of rotation `2` against rotation `1`

`Z4CoreHeightOne` asks for height one of `{w | vcount δ 0 x w ≡ k (mod n)}` for every
`δ : α → ZMod 4`.  This file proves the cases in which the displacements `δ` take at most one
nonzero value:

* `z4core_rot01`: every letter has `δ ∈ {0, 1}` (the counted letter fixed or moving);
* `z4core_rot03`: every letter has `δ ∈ {0, 3}` (the automorphism `q ↦ -q`);
* `z4core_rot02`: every letter has `δ ∈ {0, 2}` (the `Z₂` case).

Each reduces to `pcount` (a cyclic counter driven by one set of moving letters).

* Fixed counted letter: PST Proposition 6.6 for `p = 4` (`Blang_height` needs only `2 ≤ p`).
* Moving counted letter, `p = 4` (`Alang_height_four`): on words cut into `4`-blocks,
  `2·cnt₄(h) = cnt₂(h mod 2) + Σₜ cₜ·nₜ` with `cₜ = [t_h] − [t_{h+2}]`
  (`two_mul_pcount_four_eq`).  The `Z₂` count has height one (`Alang_height`, `p = 2` prime), and
  `cₜ ≠ 0` forces `t_h ≠ t_{h+2}`, so `t` has no period `1` or `2` and is primitive
  (`primitive_of_coef4_ne`); its blocks are counted with the Transfer Lemma.

The remaining cases are named as propositions: `Z4CoreRot2` (a letter of displacement `2` together
with a letter of odd displacement; smallest instance `Z4Rot2Abc`) and `Z4CorePM1` (displacements `1`
and `3`, no `2`).  `z4core_of_rot2_pm1` derives `Z4CoreHeightOne` from them, and
`height_one_F20_of_rot2_pm1` gives the Frobenius group of order `20`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-! ### The moving counted letter for `p = 4` -/

section Four

/-- The coefficient `[t_h] − [t_{h+2}]` of a block. -/
def coef4 (h : ℕ) (e : List Bool) : ℤ :=
  (pcount allMv 4 h true 0 e : ℤ) - (pcount allMv 4 ((h + 2) % 4) true 0 e : ℤ)

/-- The `Z₂` count splits into two `Z₄` counts, from every start state. -/
lemma pcount_two_eq_four {h : ℕ} (hh : h < 4) :
    ∀ (u : List Bool) (s : ℕ), pcount allMv 2 (h % 2) true s u =
      pcount allMv 4 h true s u + pcount allMv 4 ((h + 2) % 4) true s u
  | [], _ => rfl
  | b :: u, s => by
      simp only [pcount, ite_true]
      rw [pcount_two_eq_four hh u (s + 1)]
      have : (if b = true ∧ s % 2 = h % 2 then 1 else 0) =
          (if b = true ∧ s % 4 = h then 1 else 0) +
            (if b = true ∧ s % 4 = (h + 2) % 4 then 1 else 0) := by
        by_cases hb : b = true
        · simp only [hb, true_and]
          split_ifs <;> omega
        · simp [hb]
      omega

lemma sum_map_sub_int (f g : List Bool → ℕ) (es : List (List Bool)) :
    (es.map (fun e => (f e : ℤ) - g e)).sum = ((es.map f).sum : ℤ) - (es.map g).sum := by
  induction es with
  | nil => simp
  | cons e es ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring

/-- **The block identity for `p = 4`.** -/
lemma two_mul_pcount_four_eq {h : ℕ} (hh : h < 4) (es : List (List Bool))
    (hes : AllIn (pblocks 4) es) :
    (2 * pcount allMv 4 h true 0 es.flatten : ℤ) =
      (pcount allMv 2 (h % 2) true 0 es.flatten : ℤ) +
        ∑ t : List.Vector Bool 4, coef4 h t.toList * (bcount {t.toList} es : ℤ) := by
  rw [← sum_blocks _ es hes, pcount_two_eq_four hh, pcount_flatten_blocks h es hes,
    pcount_flatten_blocks ((h + 2) % 4) es hes]
  unfold coef4
  rw [sum_map_sub_int]
  push_cast
  ring

lemma coef4_eq {h : ℕ} (hh : h < 4) (e : List Bool) (he : e.length = 4) :
    coef4 h e = (if e[h]'(by omega) = true then 1 else 0) -
      (if e[(h + 2) % 4]'(by omega) = true then 1 else 0) := by
  unfold coef4
  rw [pcount_block hh e he, pcount_block (Nat.mod_lt _ (by norm_num)) e he]
  push_cast
  rfl

/-- Blocks of length `4` with `t_h ≠ t_{h+2}` are primitive. -/
lemma primitive_of_coef4_ne {h : ℕ} (hh : h < 4) (t : List.Vector Bool 4)
    (ht : coef4 h t.toList ≠ 0) :
    ∀ j, 0 < j → j < t.toList.length → t.toList.rotate j ≠ t.toList := by
  obtain ⟨l, hl⟩ := t
  change coef4 h l ≠ 0 at ht
  show ∀ j, 0 < j → j < l.length → l.rotate j ≠ l
  rw [coef4_eq hh l hl] at ht
  match l, hl with
  | [a0, a1, a2, a3], _ =>
    intro j hj0 hj4
    have hj : j = 1 ∨ j = 2 ∨ j = 3 := by simp at hj4; omega
    interval_cases h <;> rcases hj with rfl | rfl | rfl <;>
      cases a0 <;> cases a1 <;> cases a2 <;> cases a3 <;> simp_all

/-- Admissible residues for `p = 4`. -/
def VIdx4 (h m k : ℕ) :=
  {z : (List.Vector Bool 4 → Fin (2 * m)) × Fin (2 * m) //
    ((z.2 : ℕ) : ZMod (2 * m)) +
      ∑ t : List.Vector Bool 4, ((coef4 h t.toList : ℤ) : ZMod (2 * m)) *
        ((z.1 t : ℕ) : ZMod (2 * m)) = ((2 * k : ℕ) : ZMod (2 * m))}

instance (h m k : ℕ) : Finite (VIdx4 h m k) := by unfold VIdx4; infer_instance

lemma cast_identity4 {h : ℕ} (hh : h < 4) (es : List (List Bool)) (hes : AllIn (pblocks 4) es)
    (n : ℕ) :
    ((2 * pcount allMv 4 h true 0 es.flatten : ℕ) : ZMod n) =
      ((pcount allMv 2 (h % 2) true 0 es.flatten : ℕ) : ZMod n) +
        ∑ t : List.Vector Bool 4, ((coef4 h t.toList : ℤ) : ZMod n) *
          ((bcount {t.toList} es : ℕ) : ZMod n) := by
  have := congrArg (fun z : ℤ => (z : ZMod n)) (two_mul_pcount_four_eq hh es hes)
  push_cast at this ⊢
  exact this

lemma Vlang_four_eq {h m k : ℕ} (hh : h < 4) (hk : k < m) :
    Vlang 4 h m k = ⨆ z : VIdx4 h m k,
      ((pblocks 4)∗ ⊓ {v | pcount allMv 2 (h % 2) true 0 v % (2 * m) = z.1.2} ⊓
        ⨅ t : {t : List.Vector Bool 4 // coef4 h t.toList ≠ 0},
          bmod (pblocks 4) {t.1.toList} (2 * m) (z.1.1 t.1)) := by
  have hpm : 0 < 2 * m := by omega
  ext v
  constructor
  · rintro ⟨hv, hk'⟩
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hv
    let z1 : List.Vector Bool 4 → Fin (2 * m) :=
      fun t => ⟨bcount {t.toList} es % (2 * m), Nat.mod_lt _ hpm⟩
    let z2 : Fin (2 * m) :=
      ⟨pcount allMv 2 (h % 2) true 0 es.flatten % (2 * m), Nat.mod_lt _ hpm⟩
    have hz : ((z2 : ℕ) : ZMod (2 * m)) +
        ∑ t : List.Vector Bool 4, ((coef4 h t.toList : ℤ) : ZMod (2 * m)) *
          ((z1 t : ℕ) : ZMod (2 * m)) = ((2 * k : ℕ) : ZMod (2 * m)) := by
      simp only [z1, z2, ZMod.natCast_mod]
      rw [← cast_identity4 hh es hes, zmod_mul_iff (by norm_num) hk]
      exact hk'
    refine Language.mem_iSup.mpr ⟨⟨(z1, z2), hz⟩, ⟨⟨hv, rfl⟩, ?_⟩⟩
    exact HasHeightAtMost.mem_iInf_lang.mpr fun t => ⟨es, hes, rfl, rfl⟩
  · intro hv
    obtain ⟨⟨⟨z1, z2⟩, hz⟩, ⟨hstar, hcount⟩, hb⟩ := Language.mem_iSup.mp hv
    have hb' := HasHeightAtMost.mem_iInf_lang.mp hb
    refine ⟨hstar, ?_⟩
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hstar
    rw [← zmod_mul_iff (show 0 < 2 by norm_num) hk, cast_identity4 hh es hes, ← hz]
    simp only at hcount ⊢
    rw [← hcount, ZMod.natCast_mod]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : coef4 h t.toList = 0
    · rw [ht]; simp
    · obtain ⟨fs, hfs, hflat, hcnt⟩ := hb' ⟨t, ht⟩
      have := flatten_injective (pblocks_prefixCode (by norm_num)) hfs hes hflat
      subst this
      simp only at hcnt
      rw [← hcnt, ZMod.natCast_mod]

lemma bmod_block_height_four {h : ℕ} (hh : h < 4) (t : List.Vector Bool 4)
    (ht : coef4 h t.toList ≠ 0) {n k : ℕ} (hk : k < n) :
    HasHeightAtMost (bmod (pblocks 4) {t.toList} n k) 1 := by
  rw [pblocks_split t]
  have hlen : t.toList.length = 4 := by simp
  refine transfer_height_one ?_ ?_ (HasHeightAtMost.singleton _ 0)
    (HasHeightAtMost.finite _ ((List.finite_length_eq Bool 4).subset fun x hx => hx.1) 0) ?_ hk
  · rw [← pblocks_split t]; exact pblocks_prefixCode (by norm_num)
  · exact Set.disjoint_left.mpr (fun e h1 h2 => h2.2 h1)
  · exact kstar_singleton_starFree _ (by intro h; rw [h] at hlen; simp at hlen)
      (primitive_of_coef4_ne hh t ht)

theorem Vlang_height_four {h m k : ℕ} (hh : h < 4) (hk : k < m) :
    HasHeightAtMost (Vlang 4 h m k) 1 := by
  rw [Vlang_four_eq hh hk]
  refine HasHeightAtMost.iSup _ fun z => ?_
  refine HasHeightAtMost.inter (HasHeightAtMost.inter ?_ ?_) ?_
  · exact (pblocks_height 0).star
  · exact Alang_height Nat.prime_two (Nat.mod_lt _ (by norm_num)) (by omega) z.1.2.2
  · exact HasHeightAtMost.iInf _ fun t => bmod_block_height_four hh t.1 t.2 (z.1.1 t.1).2

/-- **Every letter moves, `p = 4`.** -/
theorem Alang_height_four {h m r : ℕ} (hh : h < 4) (hm : 0 < m) (hr : r < m) :
    HasHeightAtMost (Alang 4 h m r) 1 := by
  rw [Alang_eq (by norm_num) hm hr]
  exact HasHeightAtMost.iSup _ fun y =>
    (Vlang_height_four hh (Nat.mod_lt _ hm)).concat (HasHeightAtMost.singleton _ 1)

end Four

/-! ### `pcount` on a general alphabet -/

/-- A fixed counted letter, any `p ≥ 2` (PST Proposition 6.6). -/
theorem pcount_fixed_height_one {α : Type u} [Finite α] [DecidableEq α] (mv : α → Bool) {p : ℕ}
    (hp : 2 ≤ p) {h : ℕ} (hh : h < p) (x : α) (hx : mv x = false) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost {w : List α | pcount mv p h x 0 w % m = r} 1 := by
  let φ : α → Option Bool := fun y => if y = x then some true else if mv y then some false else none
  have heq : {w : List α | pcount mv p h x 0 w % m = r} = invAlph φ (Blang p h m r) := by
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
  exact (Blang_height hp hh hr).invAlph φ

/-- A moving counted letter, `p = 4`. -/
theorem pcount_moving_height_four {α : Type u} [Finite α] [DecidableEq α] (mv : α → Bool)
    {h : ℕ} (hh : h < 4) (x : α) (hx : mv x = true) {m r : ℕ} (hm : 0 < m) (hr : r < m) :
    HasHeightAtMost {w : List α | pcount mv 4 h x 0 w % m = r} 1 := by
  let φ : α → Option Bool := fun y => if y = x then some true else if mv y then some false else none
  have heq : {w : List α | pcount mv 4 h x 0 w % m = r} = invAlph φ (Alang 4 h m r) := by
    ext w
    show _ % m = r ↔ pcount allMv 4 h true 0 (w.filterMap φ) % m = r
    rw [pcount_filterMap mv 4 h x φ allMv true]
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
  exact (Alang_height_four hh hm hr).invAlph φ

/-! ### From `vcount` on `ZMod 4` to `pcount` -/

section Bridge

variable {α : Type u} [DecidableEq α]

lemma vcountFrom_eq_pcount (δ : α → ZMod 4) (mv : α → Bool) (d : ZMod 4) (p : ℕ)
    (hδ : ∀ y, δ y = if mv y then d else 0) (hd : ∀ s : ℕ, d * (s : ZMod 4) = 0 ↔ s % p = 0)
    (x : α) : ∀ (w : List α) (s : ℕ), vcountFrom δ 0 x (d * s) w = pcount mv p 0 x s w
  | [], _ => by simp [vcountFrom_nil, pcount]
  | b :: w, s => by
      rw [vcountFrom_cons, pcount]
      have hs : d * (s : ZMod 4) + δ b = d * ((if mv b then s + 1 else s : ℕ) : ZMod 4) := by
        rw [hδ b]
        split_ifs <;> push_cast <;> ring
      rw [hs, vcountFrom_eq_pcount δ mv d p hδ hd x w]
      congr 1
      by_cases hb : b = x
      · simp only [hb, true_and]
        by_cases h0 : s % p = 0
        · rw [ite_eq_left ((hd s).mpr h0), ite_eq_left h0]
        · rw [ite_eq_right (fun h => h0 ((hd s).mp h)), ite_eq_right h0]
      · simp [hb]

lemma vcount_eq_pcount (δ : α → ZMod 4) (mv : α → Bool) (d : ZMod 4) (p : ℕ)
    (hδ : ∀ y, δ y = if mv y then d else 0) (hd : ∀ s : ℕ, d * (s : ZMod 4) = 0 ↔ s % p = 0)
    (x : α) (w : List α) : vcount δ 0 x w = pcount mv p 0 x 0 w := by
  rw [vcount_eq_vcountFrom, ← vcountFrom_eq_pcount δ mv d p hδ hd x w 0]
  simp

end Bridge

/-! ### The cases of `Z4CoreHeightOne` -/

/-- **Rotations `0` and `1` only.** -/
theorem z4core_rot01 {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 4)
    (hδ : ∀ y, δ y = 0 ∨ δ y = 1) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1 := by
  let mv : α → Bool := fun y => decide (δ y = 1)
  have hδ' : ∀ y, δ y = if mv y then 1 else 0 := by
    intro y
    rcases hδ y with h | h <;> simp [mv, h]
  have hd : ∀ s : ℕ, (1 : ZMod 4) * (s : ZMod 4) = 0 ↔ s % 4 = 0 := by
    intro s
    rw [one_mul, show (0 : ZMod 4) = ((0 : ℕ) : ZMod 4) by simp, ZMod.natCast_eq_natCast_iff']
  have heq : {w : List α | vcount δ 0 x w % n = k} = {w | pcount mv 4 0 x 0 w % n = k} := by
    ext w
    show _ % n = k ↔ _ % n = k
    rw [vcount_eq_pcount δ mv 1 4 hδ' hd]
  rw [heq]
  by_cases hx : mv x = true
  · exact pcount_moving_height_four mv (by norm_num) x hx (by omega) hk
  · exact pcount_fixed_height_one mv (by norm_num) (by norm_num) x (by simpa using hx) hk

/-- **Rotations `0` and `3` only** (the automorphism `q ↦ -q`). -/
theorem z4core_rot03 {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 4)
    (hδ : ∀ y, δ y = 0 ∨ δ y = 3) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1 := by
  have heq : ∀ w, vcount δ 0 x w = vcount (fun a => -δ a) 0 x w := by
    intro w
    rw [vcount_eq_vcountFrom, vcount_eq_vcountFrom,
      ← vcountFrom_hom (negAddMonoidHom : ZMod 4 →+ ZMod 4) neg_injective δ 0 x 0 w]
    simp
  have : {w : List α | vcount δ 0 x w % n = k} =
      {w : List α | vcount (fun a => -δ a) 0 x w % n = k} := by
    ext w; show _ % n = k ↔ _ % n = k; rw [heq]
  rw [this]
  refine z4core_rot01 _ (fun y => ?_) x n k hk
  rcases hδ y with h | h
  · left; rw [h, neg_zero]
  · right; rw [h]; decide

/-- **Rotations `0` and `2` only** (the `Z₂` case). -/
theorem z4core_rot02 {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 4)
    (hδ : ∀ y, δ y = 0 ∨ δ y = 2) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1 := by
  let mv : α → Bool := fun y => decide (δ y = 2)
  have hδ' : ∀ y, δ y = if mv y then 2 else 0 := by
    intro y
    rcases hδ y with h | h <;> simp [mv, h]
  have hd : ∀ s : ℕ, (2 : ZMod 4) * (s : ZMod 4) = 0 ↔ s % 2 = 0 := by
    intro s
    rw [show (2 : ZMod 4) * (s : ZMod 4) = ((2 * s : ℕ) : ZMod 4) by push_cast; ring,
      show (0 : ZMod 4) = ((0 : ℕ) : ZMod 4) by simp, ZMod.natCast_eq_natCast_iff']
    omega
  have heq : {w : List α | vcount δ 0 x w % n = k} = {w | pcount mv 2 0 x 0 w % n = k} := by
    ext w
    show _ % n = k ↔ _ % n = k
    rw [vcount_eq_pcount δ mv 2 2 hδ' hd]
  rw [heq]
  exact pcount_height_one mv Nat.prime_two (by norm_num) x (by omega) hk

/-! ### The open cases, and the conditional theorems -/

/-- **Open (rotation `2` together with an odd rotation).** The core for alphabets with a letter of
displacement `2` and a letter of odd displacement. -/
def Z4CoreRot2 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α) (n k : ℕ), k < n →
    (∃ y, δ y = 2) → (∃ y, δ y = 1 ∨ δ y = 3) →
      HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1

/-- **Open (rotations `1` and `3`, no rotation `2`).** -/
def Z4CorePM1 : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 4) (x : α) (n k : ℕ), k < n →
    (∀ y, δ y ≠ 2) → (∃ y, δ y = 1) → (∃ y, δ y = 3) →
      HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1

/-- The smallest instance of `Z4CoreRot2`: letters `0, 1, 2` of `Fin 3` with displacements
`0, 1, 2`, counting the letter `0` read in state `0`. -/
def Z4Rot2Abc : Prop :=
  ∀ n k : ℕ, k < n →
    HasHeightAtMost {w : List (Fin 3) | vcount (![0, 1, 2] : Fin 3 → ZMod 4) 0 0 w % n = k} 1

lemma z4Rot2Abc_of_rot2 (h : Z4CoreRot2) : Z4Rot2Abc :=
  fun n k hk => h (Fin 3) _ 0 n k hk ⟨2, rfl⟩ ⟨1, Or.inl rfl⟩

lemma zmod4_cases : ∀ z : ZMod 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by decide

/-- **The core from its two open cases.** -/
theorem z4core_of_rot2_pm1 (h2 : Z4CoreRot2) (h1 : Z4CorePM1) : Z4CoreHeightOne := by
  intro α _ _ δ x n k hk
  by_cases hc : ∃ y, δ y = 2
  · by_cases ho : ∃ y, δ y = 1 ∨ δ y = 3
    · exact h2 α δ x n k hk hc ho
    · refine z4core_rot02 δ (fun y => ?_) x n k hk
      push Not at ho
      rcases zmod4_cases (δ y) with e | e | e | e
      · exact Or.inl e
      · exact absurd e (ho y).1
      · exact Or.inr e
      · exact absurd e (ho y).2
  · push Not at hc
    by_cases hb : ∃ y, δ y = 1
    · by_cases hd : ∃ y, δ y = 3
      · exact h1 α δ x n k hk hc hb hd
      · push Not at hd
        refine z4core_rot01 δ (fun y => ?_) x n k hk
        rcases zmod4_cases (δ y) with e | e | e | e
        · exact Or.inl e
        · exact Or.inr e
        · exact absurd e (hc y)
        · exact absurd e (hd y)
    · push Not at hb
      refine z4core_rot03 δ (fun y => ?_) x n k hk
      rcases zmod4_cases (δ y) with e | e | e | e
      · exact Or.inl e
      · exact absurd e (hb y)
      · exact absurd e (hc y)
      · exact Or.inr e

/-- **`F₂₀`, conditional on the two open cases of the core.** -/
theorem height_one_F20_of_rot2_pm1 (h2 : Z4CoreRot2) (h1 : Z4CorePM1) {Alphabet : Type u}
    [Finite Alphabet] (T : FreeMonoid Alphabet →* F20) (F : Set F20) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_F20_of_core (z4core_of_rot2_pm1 h2 h1) T F

end GeneralizedStarHeight
