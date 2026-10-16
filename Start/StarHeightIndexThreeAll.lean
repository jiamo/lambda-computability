import Start.StarHeightCoreHeight

/-!
# Generalized star height one for abelian-by-`Z₃` groups

`height_one_of_abelian_index_three`: if `N` is an abelian normal subgroup of index `3` in a finite
group `G`, every language recognized by `G` has generalized star height at most one (Bourne's
Conjecture 4.11, for groups).

The proof follows `height_one_of_index_three_exponent_two_of_core`, with every state count taken
modulo `|N|` instead of `2`.  Each count "letter `x` read in state `h`" modulo `m` reduces to
`coreLang k m` (`zcount_height_one_mod`), which has height at most one for every `m`
(`coreLang_height_one_all`).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-- Height one of all state counts modulo `m` from height one in state `0`. -/
lemma height_of_state_zero_mod {δ : Fin 3 → ZMod 3}
    (hδ : ∀ h : ZMod 3, h ≠ 0 → ∃ z, z ≠ 0 ∧ δ z = -h) {m r : ℕ}
    (h0 : HasHeightAtMost {u | zcount δ 0 0 0 u % m = r} 1) (h : ZMod 3) :
    HasHeightAtMost {u | zcount δ h 0 0 u % m = r} 1 := by
  by_cases hh : h = 0
  · subst hh; exact h0
  obtain ⟨z, hz, hzh⟩ := hδ h hh
  have : {u : List (Fin 3) | zcount δ h 0 0 u % m = r} =
      leftQuot z {u | zcount δ 0 0 0 u % m = r} := by
    ext u
    show _ % m = r ↔ zcount δ 0 0 0 (z :: u) % m = r
    rw [zcount_state_quot z hz hzh]
  rw [this]
  exact h0.leftQuot z

theorem coreState_height_mod {m r : ℕ} (hr : r < m) (h : ZMod 3) :
    HasHeightAtMost {u | zcount step3 h 0 0 u % m = r} 1 :=
  height_of_state_zero_mod step3_quot (coreLang_height_one_all m r hr) h

/-- **Letters outside `N`**, modulo `m`. -/
theorem moving_count_height_mod {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 3) (x : α)
    (hx : δ x ≠ 0) (h : ZMod 3) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost {w : List α | zcount δ h x 0 w % m = r} 1 := by
  set ε := δ x with hεdef
  have hε : ε * ε = 1 := by
    rcases zmod3_cases ε with e | e | e
    · exact absurd e hx
    · rw [e]; decide
    · rw [e]; decide
  let φ : α → Option (Fin 3) := fun y =>
    if y = x then some 0 else if δ y = ε then some 1 else if δ y = -ε then some 2 else none
  have heq : {w : List α | zcount δ h x 0 w % m = r} =
      invAlph φ {u | zcount step3 (ε * h) 0 0 u % m = r} := by
    ext w
    show _ % m = r ↔ zcount step3 (ε * h) 0 0 (w.filterMap φ) % m = r
    rw [zcount_transfer δ h x φ step3 0 ε hε _ _ 0 w, mul_zero]
    · intro y hy
      simp only [φ] at hy
      split_ifs at hy with h1 h2 h3
      refine ⟨?_, h1⟩
      rcases zmod3_cases (δ y) with e | e | e
      · exact e
      · rcases zmod3_cases ε with e' | e' | e'
        · exact absurd e' hx
        · exact absurd (e.trans e'.symm) h2
        · exact absurd (by rw [e, e']; decide) h3
      · rcases zmod3_cases ε with e' | e' | e'
        · exact absurd e' hx
        · exact absurd (by rw [e, e']; decide) h3
        · exact absurd (e.trans e'.symm) h2
    · intro y c hy
      simp only [φ] at hy
      split_ifs at hy with h1 h2 h3 <;> simp only [Option.some.injEq] at hy <;> subst hy
      · subst h1; exact ⟨by rw [← hεdef, hε]; rfl, by simp⟩
      · refine ⟨by rw [h2, hε]; rfl, by simp [h1]⟩
      · refine ⟨?_, by simp [h1]⟩
        rw [h3]
        show (2 : ZMod 3) = ε * -ε
        rw [mul_neg, hε]; decide
  rw [heq]
  exact (coreState_height_mod hr (ε * h)).invAlph φ

/-- **Letters inside `N`**, modulo `m`. -/
theorem fixed_count_height_mod {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 3) (x : α)
    (hx : δ x = 0) (h : ZMod 3) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost {w : List α | zcount δ h x 0 w % m = r} 1 := by
  let φ : α → Option (Fin 3) := fun y =>
    if y = x then some 0 else if δ y = 1 then some 1 else if δ y = 2 then some 2 else none
  have heq : {w : List α | zcount δ h x 0 w % m = r} =
      invAlph φ {u | zcount vstep h 0 0 u % m = r} := by
    ext w
    show _ % m = r ↔ zcount vstep h 0 0 (w.filterMap φ) % m = r
    rw [zcount_transfer δ h x φ vstep 0 1 (by decide) _ _ 0 w, one_mul, mul_zero]
    · intro y hy
      simp only [φ] at hy
      split_ifs at hy with h1 h2 h3
      refine ⟨?_, h1⟩
      rcases zmod3_cases (δ y) with e | e | e
      · exact e
      · exact absurd e h2
      · exact absurd e h3
    · intro y c hy
      simp only [φ] at hy
      split_ifs at hy with h1 h2 h3 <;> simp only [Option.some.injEq] at hy <;> subst hy
      · subst h1; exact ⟨by rw [hx]; rfl, by simp⟩
      · exact ⟨by rw [h2]; rfl, by simp [h1]⟩
      · exact ⟨by rw [h3]; rfl, by simp [h1]⟩
  rw [heq]
  exact (height_of_state_zero_mod vstep_quot (V0lang_height hr) h).invAlph φ

/-- **All state counts, modulo every `m`.** -/
theorem zcount_height_one_mod {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 3) (x : α)
    (h : ZMod 3) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost {w : List α | zcount δ h x 0 w % m = r} 1 := by
  by_cases hx : δ x = 0
  · exact fixed_count_height_mod δ x hx h hr
  · exact moving_count_height_mod δ x hx h hr

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Bourne's Conjecture 4.11, for groups.** If `N` is an abelian normal subgroup of index `3`
in a finite group `G`, every language recognized by `G` has generalized star height at most
one. -/
theorem height_one_of_abelian_index_three [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hidx : N.index = 3)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcardN : 0 < Nat.card N := Nat.card_pos
  have hcard : Nat.card (G ⧸ N) = 3 := hidx
  have hcyc : IsCyclic (G ⧸ N) := isCyclic_of_prime_card (p := 3) (hp := ⟨Nat.prime_three⟩) hcard
  obtain ⟨γ, hγ⟩ := hcyc.exists_generator
  have hord : orderOf γ = 3 := by
    rw [← hcard, orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card]
  let e : ZMod 3 → G ⧸ N := fun s => γ ^ s.val
  have hpow : ∀ a b : ℕ, γ ^ a = γ ^ b ↔ a % 3 = b % 3 := by
    intro a b
    rw [pow_eq_pow_iff_modEq, hord]; rfl
  have he : ∀ s t, e (s + t) = e s * e t := by
    intro s t
    simp only [e, ← pow_add]
    rw [hpow, ZMod.val_add]
    simp
  have hinj : Function.Injective e := by
    intro s t hst
    have := (hpow _ _).mp hst
    rw [Nat.mod_eq_of_lt (ZMod.val_lt s), Nat.mod_eq_of_lt (ZMod.val_lt t)] at this
    exact ZMod.val_injective 3 this
  have hsurj : ∀ q : G ⧸ N, ∃ s, e s = q := by
    intro q
    obtain ⟨k, hk⟩ := hγ q
    refine ⟨(k : ZMod 3), ?_⟩
    simp only [e, ← hk]
    rw [← zpow_natCast, ZMod.val_intCast, ← hord, zpow_mod_orderOf]
  choose hix hixeq using hsurj
  let δ : Alphabet → ZMod 3 := fun a => hix (psi N T (FreeMonoid.of a))
  have hδ : ∀ a, psi N T (FreeMonoid.of a) = e (δ a) := fun a => (hixeq _).symm
  have he0 : e 0 = 1 := by simp [e]
  have hcount : ∀ (w : List Alphabet) (pr : (G ⧸ N) × Alphabet),
      (tpairs N T 1 w).count pr = zcount δ (hix pr.1) pr.2 0 w := by
    intro w pr
    have := tpairs_count_eq_zcount N T e he hinj δ hδ (hix pr.1) pr.2 w 0
    rw [he0, hixeq] at this
    exact this
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % Nat.card N) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul] at ht
    exact ht
  have hQ : ∀ x y : G ⧸ N, x * y = y * x :=
    fun x y => (IsCyclic.commGroup (α := G ⧸ N)).mul_comm x y
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          {w | zcount δ (hix pr.1) pr.2 0 w % Nat.card N = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % Nat.card N, Nat.mod_lt _ hcardN⟩), ?_⟩, rfl, ?_⟩
      · show _ ∈ F
        rw [← hval]; exact hw
      · refine HasHeightAtMost.mem_iInf_lang.mpr fun pr => ?_
        show _ = _
        simp only
        rw [hcount]
    · intro hw
      obtain ⟨z, hz1, hz2⟩ := Language.mem_iSup.mp hw
      have hz2' := HasHeightAtMost.mem_iInf_lang.mp hz2
      show T (FreeMonoid.ofList w) ∈ F
      rw [hval]
      have hres : (fun pr => (tpairs N T 1 w).count pr % Nat.card N) =
          fun pr => (z.1.2 pr : ℕ) := by
        funext pr
        rw [hcount]; exact hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  refine HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter ?_ ?_
  · simpa using height_one_of_comm hQ (psi N T) {z.1.1}
  · exact HasHeightAtMost.iInf _ fun pr =>
      zcount_height_one_mod δ pr.2 (hix pr.1) (z.1.2 pr).2

end Assembly

end GeneralizedStarHeight
