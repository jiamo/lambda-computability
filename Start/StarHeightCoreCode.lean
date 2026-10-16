import Start.StarHeightLocalDFA

/-!
# The first-return code to state `0` of the core automaton

Alphabet `Fin 3`; letters `0` and `1` add `1` to the state in `ZMod 3`, letter `2` adds `2`
(`step3`).  Words are read from state `0`.

* `coreX`: the nonempty words returning to state `0` for the first time at their end.
* `NoRet`: the words none of whose nonempty prefixes returns to state `0`.
* `split u`: the factorization `u = e₁ ⋯ e_r · t` with `eᵢ ∈ coreX` and `t ∈ NoRet`
  (`split_spec`); it is the only one (`split_flatten`).
* `coreX_prefixCode`, `coreX_height` and `NoRet_height`: `coreX` is a star-free prefix code and
  `NoRet` is star-free.  The proof writes the middle parts of the blocks as strictly locally
  testable languages (`((0|1)2)*`, `((0|1)2)*(0|1)`, `(2(0|1))*` and `(2(0|1))*2`), checked on
  finite automata.
-/

namespace GeneralizedStarHeight

open EpisodeAlgebra
open scoped Computability

/-- Words over `Fin 3`. -/
abbrev W3 := List (Fin 3)

/-- **The first-return code** to state `0`. -/
def coreX : Language (Fin 3) :=
  {w | w ≠ [] ∧ dsum step3 w = 0 ∧ ∀ p, p <+: w → p ≠ [] → p ≠ w → dsum step3 p ≠ 0}

/-- Words with no nonempty prefix in state `0`. -/
def NoRet : Language (Fin 3) := {t | ∀ p, p <+: t → p ≠ [] → dsum step3 p ≠ 0}

lemma step3_ne_zero (a : Fin 3) : step3 a ≠ 0 := by fin_cases a <;> decide

lemma nil_mem_NoRet : ([] : W3) ∈ NoRet := fun _ hp hne => absurd (List.prefix_nil.mp hp) hne

lemma NoRet_eq_nil {t : W3} (ht : t ∈ NoRet) (h0 : dsum step3 t = 0) : t = [] := by
  by_contra hne
  exact ht t List.prefix_rfl hne h0

/-! ### The factorization -/

/-- One step of the factorization. -/
def splitStep (x : List W3 × W3) (a : Fin 3) : List W3 × W3 :=
  if dsum step3 (x.2 ++ [a]) = 0 then (x.1 ++ [x.2 ++ [a]], []) else (x.1, x.2 ++ [a])

/-- The factorization into first returns and a tail. -/
def split (u : W3) : List W3 × W3 := u.foldl splitStep ([], [])

lemma split_snoc (u : W3) (a : Fin 3) : split (u ++ [a]) = splitStep (split u) a := by
  rw [split, List.foldl_append]; rfl

lemma split_spec (u : W3) : (split u).1.flatten ++ (split u).2 = u ∧ AllIn coreX (split u).1 ∧
    (split u).2 ∈ NoRet := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨rfl, fun e he => by simp [split] at he, nil_mem_NoRet⟩
  | append_singleton u a ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [split_snoc]
      unfold splitStep
      split_ifs with h0
      · refine ⟨?_, ?_, nil_mem_NoRet⟩
        · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
          rw [← List.append_assoc, h1]
        · refine AllIn.append h2 ?_
          intro e he
          simp only [List.mem_singleton] at he
          subst he
          refine ⟨by simp, h0, fun p hp hne hpe => ?_⟩
          rcases List.prefix_concat_iff.mp hp with h | h
          · exact absurd h hpe
          · exact h3 p h hne
      · refine ⟨?_, h2, ?_⟩
        · simp only; rw [← List.append_assoc, h1]
        · intro p hp hne
          rcases List.prefix_concat_iff.mp hp with h | h
          · rw [h]; exact h0
          · exact h3 p h hne

lemma foldl_splitStep_noRet (es₀ : List W3) :
    ∀ (v t₀ : W3), (∀ p, p <+: v → p ≠ [] → dsum step3 (t₀ ++ p) ≠ 0) →
      v.foldl splitStep (es₀, t₀) = (es₀, t₀ ++ v)
  | [], t₀, _ => by simp
  | b :: v, t₀, h => by
      rw [List.foldl_cons]
      have hb : dsum step3 (t₀ ++ [b]) ≠ 0 := h [b] (by simp) (by simp)
      rw [show splitStep (es₀, t₀) b = (es₀, t₀ ++ [b]) by simp [splitStep, hb]]
      rw [foldl_splitStep_noRet es₀ v (t₀ ++ [b])]
      · simp
      · intro p hp hne
        have := h (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩) (by simp)
        simpa using this

lemma foldl_splitStep_coreX (es₀ : List W3) {e : W3} (he : e ∈ coreX) :
    e.foldl splitStep (es₀, []) = (es₀ ++ [e], []) := by
  obtain ⟨hne, h0, hpre⟩ := he
  rcases List.eq_nil_or_concat e with rfl | ⟨e', a, rfl⟩
  · exact absurd rfl hne
  simp only [List.concat_eq_append] at h0 hpre ⊢
  rw [List.foldl_append, foldl_splitStep_noRet es₀ e' []]
  · simp [splitStep, h0]
  · intro p hp hpne
    simp only [List.nil_append]
    refine hpre p (hp.trans (List.prefix_append _ _)) hpne ?_
    intro hpe
    have := hp.length_le
    rw [hpe] at this
    simp at this

lemma foldl_splitStep_flatten (t : W3) (ht : t ∈ NoRet) :
    ∀ (es es₀ : List W3), AllIn coreX es →
      (es.flatten ++ t).foldl splitStep (es₀, []) = (es₀ ++ es, t)
  | [], es₀, _ => by
      simp only [List.flatten_nil, List.nil_append, List.append_nil]
      rw [foldl_splitStep_noRet es₀ t []]
      · simp
      · intro p hp hne; simpa using ht p hp hne
  | e :: es, es₀, hes => by
      rw [List.flatten_cons, List.append_assoc, List.foldl_append,
        foldl_splitStep_coreX es₀ (hes e (by simp)),
        foldl_splitStep_flatten t ht es _ (fun f hf => hes f (by simp [hf]))]
      simp

/-- **Uniqueness of the factorization.** -/
lemma split_flatten {es : List W3} (hes : AllIn coreX es) {t : W3} (ht : t ∈ NoRet) :
    split (es.flatten ++ t) = (es, t) := by
  have := foldl_splitStep_flatten t ht es [] hes
  simpa [split] using this

lemma coreX_prefixCode : PrefixCode coreX := by
  refine ⟨fun h => h.1 rfl, fun e he f hf hef => ?_⟩
  by_contra hne
  exact hf.2.2 e hef he.1 hne he.2.1

lemma dsum_flatten_coreX : ∀ {es : List W3}, AllIn coreX es → dsum step3 es.flatten = 0
  | [], _ => by simp [dsum]
  | e :: es, hes => by
      rw [List.flatten_cons, dsum_append, (hes e (by simp)).2.1,
        dsum_flatten_coreX (fun f hf => hes f (by simp [hf]))]
      simp

lemma dsum_split (u : W3) : dsum step3 u = dsum step3 (split u).2 := by
  conv_lhs => rw [← (split_spec u).1]
  rw [dsum_append, dsum_flatten_coreX (split_spec u).2.1, zero_add]

lemma split_of_dsum_zero {u : W3} (h : dsum step3 u = 0) :
    (split u).2 = [] ∧ (split u).1.flatten = u := by
  have ht : (split u).2 = [] := NoRet_eq_nil (split_spec u).2.2 (by rw [← dsum_split]; exact h)
  refine ⟨ht, ?_⟩
  have := (split_spec u).1
  rw [ht, List.append_nil] at this
  exact this

lemma mem_bmod_coreX (L : Language (Fin 3)) (m r : ℕ) (u : W3) :
    u ∈ bmod coreX L m r ↔ dsum step3 u = 0 ∧ bcount L (split u).1 % m = r := by
  constructor
  · rintro ⟨es, hes, rfl, hk⟩
    refine ⟨dsum_flatten_coreX hes, ?_⟩
    have := split_flatten hes nil_mem_NoRet
    rw [List.append_nil] at this
    rw [this]; exact hk
  · rintro ⟨h0, hk⟩
    exact ⟨(split u).1, (split_spec u).2.1, (split_of_dsum_zero h0).2, hk⟩

/-! ### Star-freeness -/

/-- The walk avoiding state `0`; `none` once it has hit `0`. -/
def walkStep : Option (ZMod 3) → Fin 3 → Option (ZMod 3)
  | none, _ => none
  | some s, a => if s + step3 a = 0 then none else some (s + step3 a)

open Classical in
/-- The state of the walk after `v`, started in `q`. -/
noncomputable def walkState (q : ZMod 3) (v : W3) : Option (ZMod 3) :=
  if ∀ p, p <+: v → q + dsum step3 p ≠ 0 then some (q + dsum step3 v) else none

lemma walkState_eq_foldl {q : ZMod 3} (hq : q ≠ 0) (v : W3) :
    walkState q v = v.foldl walkStep (some q) := by
  induction v using List.reverseRecOn with
  | nil =>
      unfold walkState
      rw [if_pos]
      · simp [dsum]
      · intro p hp; rw [List.prefix_nil.mp hp]; simpa [dsum] using hq
  | append_singleton v a ih =>
      rw [List.foldl_append, ← ih]
      unfold walkState
      by_cases hv : ∀ p, p <+: v → q + dsum step3 p ≠ 0
      · rw [if_pos hv]
        simp only [List.foldl_cons, List.foldl_nil, walkStep]
        by_cases ha : q + dsum step3 v + step3 a = 0
        · rw [if_pos ha, if_neg]
          intro h
          have := h (v ++ [a]) List.prefix_rfl
          rw [dsum_append, ← add_assoc] at this
          exact this (by simpa [dsum] using ha)
        · rw [if_neg ha, if_pos]
          · rw [dsum_append, ← add_assoc]; simp [dsum]
          · intro p hp
            rcases List.prefix_concat_iff.mp hp with h | h
            · rw [h, dsum_append, ← add_assoc]; simpa [dsum] using ha
            · exact hv p h
      · rw [if_neg hv, if_neg]
        · rfl
        · intro h
          exact hv fun p hp => h p (hp.trans (List.prefix_append _ _))

/-- The middle parts of the blocks beginning with `b` and ending with `c`. -/
def Mid (b c : Fin 3) : Language (Fin 3) := {v | b :: v ++ [c] ∈ coreX}

/-- The words `v` with `b :: v ∈ NoRet`. -/
def AvoidL (b : Fin 3) : Language (Fin 3) := {v | b :: v ∈ NoRet}

/-- Acceptance for `Mid b c`. -/
def midAcc (c : Fin 3) : Option (ZMod 3) → Bool
  | none => false
  | some s => decide (s + step3 c = 0)

lemma mem_Mid_iff (b c : Fin 3) (v : W3) :
    v ∈ Mid b c ↔ midAcc c (walkState (step3 b) v) = true := by
  unfold walkState
  show b :: v ++ [c] ∈ coreX ↔ _
  constructor
  · rintro ⟨-, h0, hpre⟩
    rw [if_pos]
    · simp only [midAcc, decide_eq_true_eq]
      rw [List.cons_append, dsum_cons, dsum_append, ← add_assoc] at h0
      simpa [dsum] using h0
    · intro p hp
      have := hpre (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp.trans (List.prefix_append _ _)⟩)
        (by simp) (by
          intro h
          have := congrArg List.length h
          have := hp.length_le
          simp at *; omega)
      rwa [dsum_cons] at this
  · intro h
    by_cases hw : ∀ p, p <+: v → step3 b + dsum step3 p ≠ 0
    · rw [if_pos hw] at h
      simp only [midAcc, decide_eq_true_eq] at h
      refine ⟨by simp, ?_, fun p hp hne hpw => ?_⟩
      · rw [List.cons_append, dsum_cons, dsum_append, ← add_assoc]; simpa [dsum] using h
      · rw [List.cons_append] at hp hpw
        rcases List.prefix_cons_iff.mp hp with h' | ⟨p', rfl, hp'⟩
        · exact absurd h' hne
        rcases List.prefix_concat_iff.mp hp' with h'' | h''
        · exact absurd (by rw [h'']) hpw
        · rw [dsum_cons]; exact hw p' h''
    · rw [if_neg hw] at h
      exact absurd h (by simp [midAcc])

lemma mem_AvoidL_iff (b : Fin 3) (v : W3) :
    v ∈ AvoidL b ↔ (walkState (step3 b) v).isSome = true := by
  unfold walkState
  show b :: v ∈ NoRet ↔ _
  constructor
  · intro h
    rw [if_pos]
    · rfl
    · intro p hp
      have := h (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩) (by simp)
      rwa [dsum_cons] at this
  · intro h p hp hne
    by_cases hw : ∀ p, p <+: v → step3 b + dsum step3 p ≠ 0
    · rcases List.prefix_cons_iff.mp hp with h' | ⟨p', rfl, hp'⟩
      · exact absurd h' hne
      · rw [dsum_cons]; exact hw p' hp'
    · rw [if_neg hw] at h
      exact absurd h (by simp)

lemma coreX_eq : coreX = ⨆ bc : Fin 3 × Fin 3, {[bc.1]} * Mid bc.1 bc.2 * {[bc.2]} := by
  ext w
  rw [Language.mem_iSup]
  constructor
  · intro hw
    obtain ⟨hne, h0, -⟩ := id hw
    obtain ⟨b, w', rfl⟩ := List.exists_cons_of_ne_nil hne
    rcases List.eq_nil_or_concat w' with rfl | ⟨v, c, rfl⟩
    · exact absurd (by simpa [dsum] using h0) (step3_ne_zero b)
    refine ⟨(b, c), Language.mem_mul.mpr ⟨[b] ++ v, Language.mem_mul.mpr
      ⟨[b], rfl, v, ?_, rfl⟩, [c], rfl, by simp⟩⟩
    show b :: v ++ [c] ∈ coreX
    simpa using hw
  · rintro ⟨⟨b, c⟩, h⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp h
    obtain ⟨z, hz, v, hv, rfl⟩ := Language.mem_mul.mp hx
    rw [show z = [b] from hz, show y = [c] from hy]
    simpa using (show b :: v ++ [c] ∈ coreX from hv)

lemma NoRet_eq : NoRet = 1 + ⨆ b : Fin 3, {[b]} * AvoidL b := by
  ext t
  rw [Language.mem_add, Language.mem_one, Language.mem_iSup]
  constructor
  · intro ht
    rcases t with _ | ⟨b, v⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨b, Language.mem_mul.mpr ⟨[b], rfl, v, ht, rfl⟩⟩
  · rintro (rfl | ⟨b, h⟩)
    · exact nil_mem_NoRet
    · obtain ⟨x, hx, v, hv, rfl⟩ := Language.mem_mul.mp h
      rw [show x = [b] from hx]
      exact hv

/-- The forbidden factors of the loop languages. -/
def loopG : List W3 := [[0, 0], [0, 1], [1, 0], [1, 1], [2, 2]]

/-- Strictly locally testable data for `Mid b c`. -/
def midData (b c : Fin 3) : Bool × List W3 × List W3 :=
  if b = 2 then (if c = 2 then (false, [[2]], [[2]]) else (true, [[2]], [[0], [1]]))
  else (if c = 2 then (true, [[0], [1]], [[2]]) else (false, [[0], [1]], [[0], [1]]))

/-- Strictly locally testable data for `AvoidL b`. -/
def avoidData (b : Fin 3) : List W3 := if b = 2 then [[2]] else [[0], [1]]

lemma letters3 : ∀ a : Fin 3, a ∈ ([0, 1, 2] : List (Fin 3)) := by decide

lemma mid_check : ∀ b c : Fin 3, pairCheck [0, 1, 2] walkStep (sltStep loopG) (some (step3 b))
    (some ([], [])) (midAcc c) (sltAcc (midData b c).1 (midData b c).2.1 (midData b c).2.2)
    20 = true := by
  decide +kernel

lemma avoid_check : ∀ b : Fin 3, pairCheck [0, 1, 2] walkStep (sltStep loopG) (some (step3 b))
    (some ([], [])) Option.isSome (sltAcc true (avoidData b) [[0], [1], [2]]) 20 = true := by
  decide +kernel

lemma loopG_ok : ∀ g ∈ loopG, g ≠ [] ∧ g.length ≤ 4 := by decide

lemma Mid_eq (b c : Fin 3) :
    Mid b c = sltLang (midData b c).1 (midData b c).2.1 (midData b c).2.2 loopG := by
  ext v
  rw [mem_Mid_iff, mem_sltLang_iff (by revert b c; decide) (by revert b c; decide) loopG_ok,
    sltState_eq_foldl loopG_ok, walkState_eq_foldl (step3_ne_zero b)]
  rw [pairCheck_spec letters3 (mid_check b c) v]

lemma AvoidL_eq (b : Fin 3) : AvoidL b = sltLang true (avoidData b) [[0], [1], [2]] loopG := by
  ext v
  rw [mem_AvoidL_iff, mem_sltLang_iff (by revert b; decide) (by decide) loopG_ok,
    sltState_eq_foldl loopG_ok, walkState_eq_foldl (step3_ne_zero b)]
  rw [pairCheck_spec letters3 (avoid_check b) v]

/-- **`coreX` is star-free.** -/
theorem coreX_height : HasHeightAtMost coreX 0 := by
  rw [coreX_eq]
  refine HasHeightAtMost.iSup _ fun bc => ?_
  rw [Mid_eq]
  exact ((HasHeightAtMost.singleton _ 0).concat (sltLang_height _ _ _ _)).concat
    (HasHeightAtMost.singleton _ 0)

/-- **`NoRet` is star-free.** -/
theorem NoRet_height : HasHeightAtMost NoRet 0 := by
  rw [NoRet_eq]
  refine (HasHeightAtMost.one 0).union (HasHeightAtMost.iSup _ fun b => ?_)
  rw [AvoidL_eq]
  exact (HasHeightAtMost.singleton _ 0).concat (sltLang_height _ _ _ _)

end GeneralizedStarHeight
