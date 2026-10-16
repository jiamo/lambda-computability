import Start.StarHeightPrimeIndex

/-!
# Reducing generalized star height one for `A₄` to one three-letter language

The state of a prefix is an element of `ZMod 3`; letter `b` adds `δ b`.  `zcount δ h x s w` is the
number of positions of `w` that read `x` in state `h`, starting in state `s`.

* `coreLang k n` (alphabet `Fin 3`; letters `0` and `1` add `1`, letter `2` adds `2`): the words in
  which the number of positions reading `0` in state `0` is `k` modulo `n`.
* `zcount_height_one_of_core`: if `coreLang k 2` has height at most one for `k < 2`, then for every
  `δ`, `h`, `x` the words with `zcount δ h x 0 w ≡ r (mod 2)` have height at most one.
  - Letters with `δ x ≠ 0`: an inverse alphabetic morphism (with the automorphism `q ↦ -q` of
    `ZMod 3` when `δ x = 2`) and a left quotient for the state.
  - Letters with `δ x = 0`: the first returns to `0` starting with a moving letter form a star-free
    code `P` (while the walk avoids `0` it is a reset automaton), and the Transfer Lemma counts the
    `x`-blocks of `({x} ∪ P)∗`.
* `height_one_alternatingGroup_four_of_core`: if `coreLang k 2` has height at most one for `k < 2`,
  every language recognized by `A₄` has height at most one.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

section ZCount

variable {α : Type u} [DecidableEq α]

/-- Positions of `w` reading `x` in state `h`, starting in state `s`. -/
def zcount (δ : α → ZMod 3) (h : ZMod 3) (x : α) : ZMod 3 → List α → ℕ
  | _, [] => 0
  | s, b :: w => (if b = x ∧ s = h then 1 else 0) + zcount δ h x (s + δ b) w

/-- The total displacement of a word. -/
def dsum (δ : α → ZMod 3) (w : List α) : ZMod 3 := (w.map δ).sum

variable (δ : α → ZMod 3) (h : ZMod 3) (x : α)

omit [DecidableEq α] in
lemma dsum_append (u w : List α) : dsum δ (u ++ w) = dsum δ u + dsum δ w := by
  simp [dsum]

omit [DecidableEq α] in
lemma dsum_cons (b : α) (w : List α) : dsum δ (b :: w) = δ b + dsum δ w := by
  simp [dsum]

lemma zcount_append (s : ZMod 3) (u w : List α) :
    zcount δ h x s (u ++ w) = zcount δ h x s u + zcount δ h x (s + dsum δ u) w := by
  induction u generalizing s with
  | nil => simp [zcount, dsum]
  | cons b u ih =>
      simp only [List.cons_append, zcount, ih, dsum_cons, add_assoc]

lemma zcount_shift (c s : ZMod 3) (w : List α) :
    zcount δ h x s w = zcount δ (h + c) x (s + c) w := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
      simp only [zcount]
      rw [ih (s + δ b), show s + δ b + c = s + c + δ b by ring]
      congr 2
      simp only [add_left_inj]

lemma zcount_transfer {β : Type*} [DecidableEq β] (φ : α → Option β) (δ' : β → ZMod 3) (x' : β)
    (ε : ZMod 3) (hε : ε * ε = 1)
    (h0 : ∀ y, φ y = none → δ y = 0 ∧ y ≠ x)
    (h1 : ∀ y c, φ y = some c → δ' c = ε * δ y ∧ (y = x ↔ c = x')) (s : ZMod 3) (w : List α) :
    zcount δ h x s w = zcount δ' (ε * h) x' (ε * s) (w.filterMap φ) := by
  induction w generalizing s with
  | nil => rfl
  | cons b w ih =>
      have hinj : (ε * s = ε * h) ↔ s = h := by
        constructor
        · intro e
          have := congrArg (ε * ·) e
          simp only [← mul_assoc, hε, one_mul] at this
          exact this
        · intro e; rw [e]
      cases hb : φ b with
      | none =>
          obtain ⟨hd, hx⟩ := h0 b hb
          rw [List.filterMap_cons, hb, zcount, if_neg (fun h' => hx h'.1), hd, add_zero, ih]
          simp
      | some c =>
          obtain ⟨hd, hx⟩ := h1 b c hb
          rw [List.filterMap_cons, hb, zcount, zcount, ih, hd, mul_add]
          simp only [hx, hinj]

lemma zcount_zero_of_avoid :
    ∀ (w : List α) (s : ZMod 3), (∀ v₁ v₂, w = v₁ ++ x :: v₂ → s + dsum δ v₁ ≠ h) →
      zcount δ h x s w = 0
  | [], _, _ => rfl
  | b :: w, s, hs => by
      rw [zcount]
      have h1 : ¬ (b = x ∧ s = h) := by
        rintro ⟨rfl, rfl⟩
        exact hs [] w rfl (by simp [dsum])
      rw [if_neg h1, zero_add]
      apply zcount_zero_of_avoid w
      intro v₁ v₂ hv
      have := hs (b :: v₁) v₂ (by rw [hv]; rfl)
      rwa [dsum_cons, ← add_assoc] at this

end ZCount

/-! ### The core language -/

/-- Letters `0` and `1` add `1`, letter `2` adds `2`. -/
def step3 : Fin 3 → ZMod 3 := ![1, 1, 2]

/-- The number of positions reading `0` in state `0`. -/
def coreCount (u : List (Fin 3)) : ℕ := zcount step3 0 0 0 u

/-- **The core language.** -/
def coreLang (k n : ℕ) : Language (Fin 3) := {u | coreCount u % n = k}

/-! ### Letters outside `N` -/

lemma zcount_state_quot {δ : Fin 3 → ZMod 3} {h : ZMod 3} (z : Fin 3) (hz : z ≠ 0)
    (hzh : δ z = -h) (u : List (Fin 3)) :
    zcount δ h 0 0 u = zcount δ 0 0 0 (z :: u) := by
  rw [zcount, if_neg (fun h' => hz h'.1), zero_add, zcount_shift δ h 0 (-h) 0 u, hzh]
  simp

/-- Height one of all state counts from height one in state `0`, by left quotients. -/
lemma height_of_state_zero {δ : Fin 3 → ZMod 3} (hδ : ∀ h : ZMod 3, h ≠ 0 → ∃ z, z ≠ 0 ∧ δ z = -h)
    {r : ℕ} (h0 : HasHeightAtMost {u | zcount δ 0 0 0 u % 2 = r} 1) (h : ZMod 3) :
    HasHeightAtMost {u | zcount δ h 0 0 u % 2 = r} 1 := by
  by_cases hh : h = 0
  · subst hh; exact h0
  obtain ⟨z, hz, hzh⟩ := hδ h hh
  have : {u : List (Fin 3) | zcount δ h 0 0 u % 2 = r} =
      leftQuot z {u | zcount δ 0 0 0 u % 2 = r} := by
    ext u
    show _ % 2 = r ↔ zcount δ 0 0 0 (z :: u) % 2 = r
    rw [zcount_state_quot z hz hzh]
  rw [this]
  exact h0.leftQuot z

lemma step3_quot : ∀ h : ZMod 3, h ≠ 0 → ∃ z, z ≠ 0 ∧ step3 z = -h := by decide

theorem coreState_height (hcore : ∀ k < 2, HasHeightAtMost (coreLang k 2) 1) {r : ℕ} (hr : r < 2)
    (h : ZMod 3) : HasHeightAtMost {u | zcount step3 h 0 0 u % 2 = r} 1 :=
  height_of_state_zero step3_quot (hcore r hr) h

lemma zmod3_cases : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide

/-- **Letters outside `N`.** -/
theorem moving_count_height {α : Type u} [Finite α] [DecidableEq α]
    (hcore : ∀ k < 2, HasHeightAtMost (coreLang k 2) 1) (δ : α → ZMod 3) (x : α) (hx : δ x ≠ 0)
    (h : ZMod 3) {r : ℕ} (hr : r < 2) :
    HasHeightAtMost {w : List α | zcount δ h x 0 w % 2 = r} 1 := by
  set ε := δ x with hεdef
  have hε : ε * ε = 1 := by
    rcases zmod3_cases ε with e | e | e
    · exact absurd e hx
    · rw [e]; decide
    · rw [e]; decide
  let φ : α → Option (Fin 3) := fun y =>
    if y = x then some 0 else if δ y = ε then some 1 else if δ y = -ε then some 2 else none
  have heq : {w : List α | zcount δ h x 0 w % 2 = r} =
      invAlph φ {u | zcount step3 (ε * h) 0 0 u % 2 = r} := by
    ext w
    show _ % 2 = r ↔ zcount step3 (ε * h) 0 0 (w.filterMap φ) % 2 = r
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
  exact (coreState_height hcore hr (ε * h)).invAlph φ

/-! ### Letters in `N`: the first-return code -/

/-- Displacements on `Fin 3` for the letters in `N`: `0` stays, `1` adds `1`, `2` adds `2`. -/
def vstep : Fin 3 → ZMod 3 := ![0, 1, 2]

/-- The walk from `q` avoids `0` after every letter of `v`. -/
def Avoid (q : ZMod 3) : Language (Fin 3) :=
  {v | ∀ v₁ b v₂, v = v₁ ++ b :: v₂ → q + dsum vstep (v₁ ++ [b]) ≠ 0}

/-- The reset automaton: `0` keeps the state, any other letter `b` resets it to `-vstep b`. -/
def vK (b : Fin 3) : Prop := vstep b = 0

instance : DecidablePred vK := fun b => inferInstanceAs (Decidable (vstep b = 0))

def vρ (b : Fin 3) : ZMod 3 := -vstep b

lemma reset_step : ∀ q d : ZMod 3, q ≠ 0 → d ≠ 0 → q + d ≠ 0 → q + d = -d := by decide

lemma walk_eq_reset : ∀ (v : List (Fin 3)) (q : ZMod 3), q ≠ 0 → v ∈ Avoid q →
    q + dsum vstep v = rstate vK vρ q v
  | [], q, _, _ => by simp [dsum, rstate]
  | b :: v, q, hq, hv => by
      have hb : q + vstep b ≠ 0 := by
        have := hv [] b v rfl
        simpa [dsum] using this
      have hstep : rstep vK vρ q b = q + vstep b := by
        unfold rstep
        split_ifs with hK
        · rw [show vstep b = 0 from hK, add_zero]
        · exact (reset_step q (vstep b) hq hK hb).symm
      have hv' : v ∈ Avoid (q + vstep b) := by
        intro v₁ c v₂ he
        have := hv (b :: v₁) c v₂ (by rw [he]; rfl)
        rwa [List.cons_append, dsum_cons, ← add_assoc] at this
      rw [rstate, hstep, ← walk_eq_reset v _ hb hv', dsum_cons, add_assoc]

lemma nil_mem_avoid (q : ZMod 3) : [] ∈ Avoid q := by
  intro v₁ b v₂ he
  exact absurd he.symm (by simp)

lemma avoid_cons {q : ZMod 3} {b : Fin 3} (hb : q + vstep b ≠ 0) (v : List (Fin 3)) :
    b :: v ∈ Avoid q ↔ v ∈ Avoid (q + vstep b) := by
  constructor
  · intro hv v₁ c v₂ he
    have := hv (b :: v₁) c v₂ (by rw [he]; rfl)
    rwa [List.cons_append, dsum_cons, ← add_assoc] at this
  · intro hv v₁ c v₂ he
    rcases v₁ with _ | ⟨b', v₁⟩
    · simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      simpa [dsum] using hb
    · simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have := hv v₁ c v₂ he
      rwa [List.cons_append, dsum_cons, ← add_assoc]

/-- The first return to `0`, if any. -/
lemma first_return : ∀ (v : List (Fin 3)) (q : ZMod 3), v ∈ Avoid q ∨
    ∃ v₁ b v₂, v = v₁ ++ b :: v₂ ∧ v₁ ∈ Avoid q ∧ q + dsum vstep (v₁ ++ [b]) = 0
  | [], q => Or.inl (nil_mem_avoid q)
  | b :: v, q => by
      by_cases hb : q + vstep b = 0
      · exact Or.inr ⟨[], b, v, rfl, nil_mem_avoid q, by simpa [dsum] using hb⟩
      rcases first_return v (q + vstep b) with h | ⟨v₁, c, v₂, rfl, h1, h2⟩
      · exact Or.inl ((avoid_cons hb v).mpr h)
      · refine Or.inr ⟨b :: v₁, c, v₂, rfl, (avoid_cons hb v₁).mpr h1, ?_⟩
        rwa [List.cons_append, dsum_cons, ← add_assoc]

/-- Pairs (state, letter) at which the walk returns to `0`. -/
abbrev RetIdx := {z : ZMod 3 × Fin 3 // z.1 + vstep z.2 = 0}

lemma avoid_eq {q : ZMod 3} (hq : q ≠ 0) :
    Avoid q = (⨆ z : RetIdx, stateIs vK vρ q z.1.1 * {[z.1.2]} * ⊤)ᶜ := by
  ext v
  constructor
  · intro hv hm
    obtain ⟨z, hz⟩ := Language.mem_iSup.mp hm
    obtain ⟨ab, hab, c, -, rfl⟩ := Language.mem_mul.mp hz
    obtain ⟨a, ha, bb, hbb, rfl⟩ := Language.mem_mul.mp hab
    have hbb' : bb = [z.1.2] := hbb
    subst hbb'
    have ha' : rstate vK vρ q a = z.1.1 := ha
    -- the prefix `a` avoids `0`
    have hav : a ∈ Avoid q := by
      intro v₁ b v₂ he
      exact hv v₁ b (v₂ ++ [z.1.2] ++ c) (by rw [he]; simp)
    have := hv a z.1.2 c (by simp)
    rw [dsum_append, ← add_assoc, walk_eq_reset a q hq hav, ha'] at this
    exact this (by simpa [dsum] using z.2)
  · intro hv
    by_contra hna
    rcases first_return v q with h | ⟨v₁, b, v₂, rfl, h1, h2⟩
    · exact hna h
    apply hv
    refine Language.mem_iSup.mpr ⟨⟨(rstate vK vρ q v₁, b), ?_⟩, ?_⟩
    · show rstate vK vρ q v₁ + vstep b = 0
      rw [← walk_eq_reset v₁ q hq h1]
      simpa [dsum_append, dsum, add_assoc] using h2
    · exact Language.mem_mul.mpr ⟨v₁ ++ [b], Language.mem_mul.mpr ⟨v₁, rfl, [b], rfl, rfl⟩,
        v₂, trivial, by simp⟩

lemma avoid_height {q : ZMod 3} (hq : q ≠ 0) (n : ℕ) : HasHeightAtMost (Avoid q) n := by
  rw [avoid_eq hq]
  exact (HasHeightAtMost.iSup _ fun z : RetIdx =>
    ((stateIs_height q z.1.1 n).concat (HasHeightAtMost.singleton _ n)).concat
      (HasHeightAtMost.top n)).compl

/-- First returns to `0` that start with a moving letter. -/
def Pblock : Language (Fin 3) :=
  {e | ∃ m v b, e = m :: (v ++ [b]) ∧ m ≠ 0 ∧ v ∈ Avoid (vstep m) ∧
    vstep m + dsum vstep v + vstep b = 0}

/-- Proper prefixes of `P`-blocks. -/
def PrefV : Language (Fin 3) :=
  {y | y = [] ∨ ∃ m v, y = m :: v ∧ m ≠ 0 ∧ v ∈ Avoid (vstep m)}

lemma vstep_ne_zero {m : Fin 3} (hm : m ≠ 0) : vstep m ≠ 0 := by
  revert m; decide

/-- Index data of the `P`-blocks. -/
abbrev PIdx := {m : Fin 3 // m ≠ 0} × RetIdx

lemma Pblock_eq : Pblock = ⨆ z : PIdx,
    {[z.1.1]} * (Avoid (vstep z.1.1) ⊓ stateIs vK vρ (vstep z.1.1) z.2.1.1) * {[z.2.1.2]} := by
  ext e
  constructor
  · rintro ⟨m, v, b, rfl, hm, hv, hret⟩
    have hw := walk_eq_reset v _ (vstep_ne_zero hm) hv
    refine Language.mem_iSup.mpr ⟨(⟨m, hm⟩, ⟨(rstate vK vρ (vstep m) v, b), ?_⟩), ?_⟩
    · show rstate vK vρ (vstep m) v + vstep b = 0
      rw [← hw]; exact hret
    · exact Language.mem_mul.mpr ⟨[m] ++ v, Language.mem_mul.mpr ⟨[m], rfl, v, ⟨hv, rfl⟩, rfl⟩,
        [b], rfl, by simp⟩
  · intro he
    obtain ⟨⟨⟨m, hm⟩, ⟨⟨q', b⟩, hret⟩⟩, hz⟩ := Language.mem_iSup.mp he
    obtain ⟨mv, hmv, bb, hbb, rfl⟩ := Language.mem_mul.mp hz
    obtain ⟨mm, hmm, v, ⟨hv, hst⟩, rfl⟩ := Language.mem_mul.mp hmv
    have hmm' : mm = [m] := hmm
    have hbb' : bb = [b] := hbb
    subst hmm' hbb'
    have hst' : rstate vK vρ (vstep m) v = q' := hst
    refine ⟨m, v, b, by simp, hm, hv, ?_⟩
    rw [walk_eq_reset v _ (vstep_ne_zero hm) hv, hst']
    exact hret

lemma PrefV_eq : PrefV = 1 + ⨆ m : {m : Fin 3 // m ≠ 0}, {[m.1]} * Avoid (vstep m.1) := by
  ext y
  rw [Language.mem_add]
  constructor
  · rintro (rfl | ⟨m, v, rfl, hm, hv⟩)
    · exact Or.inl ((Language.mem_one _).mpr rfl)
    · exact Or.inr (Language.mem_iSup.mpr ⟨⟨m, hm⟩, Language.mem_mul.mpr ⟨[m], rfl, v, hv, rfl⟩⟩)
  · rintro (h | h)
    · exact Or.inl ((Language.mem_one _).mp h)
    · obtain ⟨⟨m, hm⟩, hz⟩ := Language.mem_iSup.mp h
      obtain ⟨mm, hmm, v, hv, rfl⟩ := Language.mem_mul.mp hz
      have hmm' : mm = [m] := hmm
      subst hmm'
      exact Or.inr ⟨m, v, rfl, hm, hv⟩

lemma Pblock_height : HasHeightAtMost Pblock 0 := by
  rw [Pblock_eq]
  exact HasHeightAtMost.iSup _ fun z =>
    ((HasHeightAtMost.singleton _ 0).concat ((avoid_height (vstep_ne_zero z.1.2) 0).inter
      (stateIs_height _ _ 0))).concat (HasHeightAtMost.singleton _ 0)

lemma PrefV_height : HasHeightAtMost PrefV 0 := by
  rw [PrefV_eq]
  exact (HasHeightAtMost.one 0).union (HasHeightAtMost.iSup _ fun m =>
    (HasHeightAtMost.singleton _ 0).concat (avoid_height (vstep_ne_zero m.2) 0))

/-- The code `{0} ∪ P`. -/
def EV : Language (Fin 3) := {[0]} + Pblock

lemma Pblock_ne_zero_head {e : List (Fin 3)} (he : e ∈ Pblock) : e ≠ [0] ∧ ∀ w, e ≠ 0 :: w := by
  obtain ⟨m, v, b, rfl, hm, -, -⟩ := he
  refine ⟨?_, ?_⟩
  · intro h; simp [hm] at h
  · intro w h; simp [hm] at h

lemma EV_prefixCode : PrefixCode EV := by
  refine ⟨?_, ?_⟩
  · intro h
    rcases (Language.mem_add _ _ _).mp h with h | ⟨m, v, b, he, -⟩
    · have h' : ([] : List (Fin 3)) = [0] := h
      simp at h'
    · simp at he
  · intro e he f hf hef
    rcases (Language.mem_add _ _ _).mp he with he | he <;>
      rcases (Language.mem_add _ _ _).mp hf with hf | hf
    · exact (he : e = [0]).trans (hf : f = [0]).symm
    · have he' : e = [0] := he
      subst he'
      obtain ⟨w, hw⟩ := hef
      exact absurd hw.symm ((Pblock_ne_zero_head hf).2 w)
    · have hf' : f = [0] := hf
      subst hf'
      obtain ⟨m, v, b, rfl, hm, -, -⟩ := he
      obtain ⟨w, hw⟩ := hef
      simp [hm] at hw
    · obtain ⟨m, v, b, rfl, hm, hv, hret⟩ := he
      obtain ⟨m', v', b', rfl, hm', hv', hret'⟩ := hf
      obtain ⟨w, hw⟩ := hef
      simp only [List.cons_append, List.cons.injEq, List.append_assoc] at hw
      obtain ⟨rfl, hw⟩ := hw
      rcases List.eq_nil_or_concat w with hw0 | ⟨w', c, rfl⟩
      · subst hw0
        simp only [List.append_nil] at hw
        rw [hw]
      · exfalso
        -- `v ++ [b]` is a proper prefix of `v' ++ [b']`, so `v ++ [b]` is a prefix of `v'`
        have hw2 : (v ++ b :: w') ++ [c] = v' ++ [b'] := by simpa using hw
        have hlen : v ++ b :: w' = v' := (List.append_inj' hw2 rfl).1
        have := hv' v b w' hlen.symm
        exact this (by rw [dsum_append]; simpa [dsum, add_assoc] using hret)

lemma avoid_prefix_state {q : ZMod 3} (hq : q ≠ 0) {v v₁ : List (Fin 3)} (hv : v ∈ Avoid q)
    (hp : v₁ <+: v) : q + dsum vstep v₁ ≠ 0 := by
  rcases List.eq_nil_or_concat v₁ with rfl | ⟨v₁', d, rfl⟩
  · simpa [dsum] using hq
  · obtain ⟨r, hr⟩ := hp
    rw [List.concat_eq_append]
    exact hv v₁' d r (by rw [← hr]; simp)

lemma zcount_avoid {q : ZMod 3} (hq : q ≠ 0) {v : List (Fin 3)} (hv : v ∈ Avoid q) (t : List (Fin 3))
    (ht : t.length ≤ 1) : zcount vstep 0 0 q (v ++ t) = 0 := by
  apply zcount_zero_of_avoid
  intro v₁ v₂ he
  apply avoid_prefix_state hq hv
  have h1 : v₁ <+: v ++ t := ⟨0 :: v₂, he.symm⟩
  refine List.prefix_of_prefix_length_le h1 (List.prefix_append v t) ?_
  have := congrArg List.length he
  simp at this
  omega

lemma Pblock_zcount {e : List (Fin 3)} (he : e ∈ Pblock) :
    zcount vstep 0 0 0 e = 0 ∧ dsum vstep e = 0 := by
  obtain ⟨m, v, b, rfl, hm, hv, hret⟩ := he
  refine ⟨?_, ?_⟩
  · rw [zcount, if_neg (fun h => hm h.1), zero_add, zero_add]
    exact zcount_avoid (vstep_ne_zero hm) hv [b] (by simp)
  · rw [dsum_cons, dsum_append, ← add_assoc, ← hret]
    simp [dsum]

lemma PrefV_zcount {y : List (Fin 3)} (hy : y ∈ PrefV) : zcount vstep 0 0 0 y = 0 := by
  rcases hy with rfl | ⟨m, v, rfl, hm, hv⟩
  · rfl
  · rw [zcount, if_neg (fun h => hm h.1), zero_add, zero_add]
    simpa using zcount_avoid (vstep_ne_zero hm) hv [] (by simp)

open Classical in
lemma zcount_flatten_EV : ∀ es : List (List (Fin 3)), AllIn EV es →
    zcount vstep 0 0 0 es.flatten = bcount {[0]} es ∧ dsum vstep es.flatten = 0
  | [], _ => by simp [zcount, bcount, dsum]
  | e :: es, hes => by
      obtain ⟨ih1, ih2⟩ := zcount_flatten_EV es (fun f hf => hes f (by simp [hf]))
      rw [List.flatten_cons, zcount_append, dsum_append]
      rcases (Language.mem_add _ _ _).mp (hes e (by simp)) with he | he
      · have he' : e = [0] := he
        subst he'
        have hd : dsum vstep [0] = 0 := by decide
        rw [hd, zero_add, ih1, ih2]
        refine ⟨?_, rfl⟩
        have hz : zcount vstep 0 0 0 [0] = 1 := by decide
        rw [hz]
        unfold bcount
        rw [List.countP_cons]
        simp only [show ([0] : List (Fin 3)) ∈ ({[0]} : Language (Fin 3)) from rfl,
          decide_true, if_true]
        omega
      · obtain ⟨hz, hd⟩ := Pblock_zcount he
        simp only [hz, hd, add_zero, zero_add]
        rw [ih1, ih2]
        refine ⟨?_, rfl⟩
        have hne : e ∉ ({[0]} : Language (Fin 3)) := fun h => (Pblock_ne_zero_head he).1 h
        unfold bcount
        rw [List.countP_cons, if_neg (fun hc => hne (of_decide_eq_true hc))]
        omega

lemma decomp_EV : ∀ (n : ℕ) (w : List (Fin 3)), w.length ≤ n →
    ∃ es y, AllIn EV es ∧ y ∈ PrefV ∧ w = es.flatten ++ y
  | _, [], _ => ⟨[], [], by simp [AllIn], Or.inl rfl, rfl⟩
  | 0, b :: w, h => by simp at h
  | n + 1, m :: w, h => by
      by_cases hm : m = 0
      · subst hm
        obtain ⟨es, y, hes, hy, rfl⟩ := decomp_EV n w (by simpa using h)
        refine ⟨[0] :: es, y, ?_, hy, rfl⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact (Language.mem_add _ _ _).mpr (Or.inl rfl)
        · exact hes e he
      rcases first_return w (vstep m) with hw | ⟨v₁, b, v₂, rfl, h1, h2⟩
      · exact ⟨[], m :: w, by simp [AllIn], Or.inr ⟨m, w, rfl, hm, hw⟩, rfl⟩
      · obtain ⟨es, y, hes, hy, hz⟩ := decomp_EV n v₂ (by simp at h; omega)
        refine ⟨(m :: (v₁ ++ [b])) :: es, y, ?_, hy, by simp [hz]⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · refine (Language.mem_add _ _ _).mpr (Or.inr ⟨m, v₁, b, rfl, hm, h1, ?_⟩)
          rw [dsum_append] at h2
          simpa [dsum, add_assoc] using h2
        · exact hes e he

/-- Positions reading `0` in state `0`, over the letters of `N`. -/
def V0lang (m r : ℕ) : Language (Fin 3) := {w | zcount vstep 0 0 0 w % m = r}

lemma V0lang_eq (m r : ℕ) : V0lang m r = bmod EV {[0]} m r * PrefV := by
  ext w
  constructor
  · intro hw
    obtain ⟨es, y, hes, hy, rfl⟩ := decomp_EV _ w le_rfl
    obtain ⟨h1, h2⟩ := zcount_flatten_EV es hes
    have hw' : zcount vstep 0 0 0 (es.flatten ++ y) % m = r := hw
    rw [zcount_append, h1, h2, add_zero, PrefV_zcount hy, add_zero] at hw'
    exact Language.mem_mul.mpr ⟨_, ⟨es, hes, rfl, hw'⟩, y, hy, rfl⟩
  · intro hw
    obtain ⟨v, ⟨es, hes, rfl, hk⟩, y, hy, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨h1, h2⟩ := zcount_flatten_EV es hes
    show zcount vstep 0 0 0 (es.flatten ++ y) % m = r
    rw [zcount_append, h1, h2, add_zero, PrefV_zcount hy, add_zero]
    exact hk

theorem V0lang_height {m r : ℕ} (hr : r < m) : HasHeightAtMost (V0lang m r) 1 := by
  rw [V0lang_eq]
  refine HasHeightAtMost.concat ?_ (PrefV_height.mono (by omega))
  refine transfer_height_one EV_prefixCode ?_ (HasHeightAtMost.singleton _ 0) Pblock_height ?_ hr
  · exact Set.disjoint_left.mpr (fun e h1 h2 => (Pblock_ne_zero_head h2).1 h1)
  · exact kstar_singleton_starFree [0] (by simp) (fun j hj hj' => by simp at hj'; omega)

lemma vstep_quot : ∀ h : ZMod 3, h ≠ 0 → ∃ z, z ≠ 0 ∧ vstep z = -h := by decide

/-- **Letters inside `N`.** -/
theorem fixed_count_height {α : Type u} [Finite α] [DecidableEq α] (δ : α → ZMod 3) (x : α)
    (hx : δ x = 0) (h : ZMod 3) {r : ℕ} (hr : r < 2) :
    HasHeightAtMost {w : List α | zcount δ h x 0 w % 2 = r} 1 := by
  let φ : α → Option (Fin 3) := fun y =>
    if y = x then some 0 else if δ y = 1 then some 1 else if δ y = 2 then some 2 else none
  have heq : {w : List α | zcount δ h x 0 w % 2 = r} =
      invAlph φ {u | zcount vstep h 0 0 u % 2 = r} := by
    ext w
    show _ % 2 = r ↔ zcount vstep h 0 0 (w.filterMap φ) % 2 = r
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
  exact (height_of_state_zero vstep_quot (V0lang_height hr) h).invAlph φ

/-- **All state counts**, from the core language. -/
theorem zcount_height_one_of_core {α : Type u} [Finite α] [DecidableEq α]
    (hcore : ∀ k < 2, HasHeightAtMost (coreLang k 2) 1) (δ : α → ZMod 3) (x : α) (h : ZMod 3)
    {r : ℕ} (hr : r < 2) : HasHeightAtMost {w : List α | zcount δ h x 0 w % 2 = r} 1 := by
  by_cases hx : δ x = 0
  · exact fixed_count_height δ x hx h hr
  · exact moving_count_height hcore δ x hx h hr

/-! ### Assembly -/

section Assembly

open Classical

variable {Alphabet : Type u} {G : Type} [Group G] (N : Subgroup G) [N.Normal]
  (T : FreeMonoid Alphabet →* G)

lemma tpairs_count_eq_zcount (e : ZMod 3 → G ⧸ N) (he : ∀ s t, e (s + t) = e s * e t)
    (hinj : Function.Injective e) (δ : Alphabet → ZMod 3)
    (hδ : ∀ a, psi N T (FreeMonoid.of a) = e (δ a)) (h : ZMod 3) (a : Alphabet) :
    ∀ (w : List Alphabet) (s : ZMod 3), (tpairs N T (e s) w).count (e h, a) = zcount δ h a s w
  | [], _ => rfl
  | b :: w, s => by
      rw [tpairs, zcount, List.count_cons, hδ b, ← he, tpairs_count_eq_zcount e he hinj δ hδ h a w,
        add_comm]
      congr 1
      by_cases hb : b = a
      · subst hb
        by_cases hs : s = h
        · simp [hs]
        · have : ¬ e s = e h := fun e' => hs (hinj e')
          simp [hs, this]
      · simp [hb]

lemma valN_mod_two [Fintype Alphabet] [Fintype (G ⧸ N)] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x ∈ N, x * x = 1) (res : (G ⧸ N) × Alphabet → ℕ) :
    valN N T hab res = valN N T hab (fun pr => res pr % 2) := by
  let := nComm N hab
  unfold valN
  refine Finset.prod_congr rfl fun pr _ => ?_
  have h2 : cvN N T pr.1 pr.2 ^ 2 = 1 := Subtype.ext (by
    simp only [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact hexp _ (cv_mem N T pr.1 pr.2))
  conv_lhs => rw [← Nat.div_add_mod (res pr) 2, pow_add, pow_mul, h2, one_pow, one_mul]

lemma valN_mod_card [Fintype Alphabet] [Fintype (G ⧸ N)] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (res : (G ⧸ N) × Alphabet → ℕ) :
    valN N T hab (fun pr => res pr % Nat.card N) = valN N T hab res := by
  let := nComm N hab
  unfold valN
  exact Finset.prod_congr rfl fun pr _ => (pow_mod_card_N N _ _).symm

/-- **Index three, exponent two.** If `N` is a normal subgroup of index three in which every
element has order at most two, then every language recognized by `G` has height at most one,
provided `coreLang k 2` does. -/
theorem height_one_of_index_three_exponent_two_of_core
    (hcore : ∀ k < 2, HasHeightAtMost (coreLang k 2) 1) [Finite Alphabet] [Fintype G]
    (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hexp : ∀ x ∈ N, x * x = 1) (hidx : N.index = 3)
    (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
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
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % 2) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul,
      valN_mod_card N T hab (fun pr => (tpairs N T 1 w).count pr),
      valN_mod_two N T hab hexp] at ht
    exact ht
  have hQ : ∀ x y : G ⧸ N, x * y = y * x :=
    fun x y => (IsCyclic.commGroup (α := G ⧸ N)).mul_comm x y
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin 2) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          {w | zcount δ (hix pr.1) pr.2 0 w % 2 = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % 2, Nat.mod_lt _ (by norm_num)⟩), ?_⟩, rfl, ?_⟩
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
      have hres : (fun pr => (tpairs N T 1 w).count pr % 2) = fun pr => (z.1.2 pr : ℕ) := by
        funext pr
        rw [hcount]; exact hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  refine HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter ?_ ?_
  · simpa using height_one_of_comm hQ (psi N T) {z.1.1}
  · exact HasHeightAtMost.iInf _ fun pr =>
      zcount_height_one_of_core hcore δ pr.2 (hix pr.1) (z.1.2 pr).2

end Assembly

/-- **Reduction of `A₄` to the core language.** -/
theorem height_one_alternatingGroup_four_of_core
    (hcore : ∀ k < 2, HasHeightAtMost (coreLang k 2) 1) {Alphabet : Type u} [Finite Alphabet]
    (T : FreeMonoid Alphabet →* alternatingGroup (Fin 4)) (F : Set (alternatingGroup (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  have := alternatingGroup.normal_kleinFour h4
  have hK := alternatingGroup.kleinFour_isKleinFour h4
  have hab : ∀ x ∈ alternatingGroup.kleinFour (Fin 4), ∀ y ∈ alternatingGroup.kleinFour (Fin 4),
      x * y = y * x := by
    intro x hx y hy
    have := hK.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hexp : ∀ x ∈ alternatingGroup.kleinFour (Fin 4), x * x = 1 := by
    intro x hx
    have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : alternatingGroup.kleinFour (Fin 4))
    rw [hK.exponent_two, pow_two] at h
    exact congrArg Subtype.val h
  have hidx : (alternatingGroup.kleinFour (Fin 4)).index = 3 := by
    have h := (alternatingGroup.kleinFour (Fin 4)).index_mul_card
    rw [hK.card_four, nat_card_alternatingGroup, h4] at h
    norm_num [Nat.factorial] at h
    omega
  exact height_one_of_index_three_exponent_two_of_core _ T hcore hab hexp hidx F

end GeneralizedStarHeight
