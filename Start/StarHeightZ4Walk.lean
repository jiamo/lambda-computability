import Start.StarHeightZ4Core
import Start.StarHeightAperiodic

/-!
# Walks on `ZMod 4` with steps `0, ±1`: the first-return code

Alphabet `Fin 3`; letter `i` moves the state in `ZMod 4` by `σ i`.  Words are read from state `0`.
Two displacement maps are used: `σm = ![1, 1, 3]` (all letters move; the counted letter `0` moves)
and `σa = ![0, 1, 3]` (the counted letter `0` is fixed).

* `zc σ s w`: the positions of `w` reading the letter `0` in state `0`, starting in state `s`
  (`zc_eq_vcountFrom`).
* `Xc σ`: the nonempty words returning to `0` for the first time at their end; `NR σ`: the words
  none of whose nonempty prefixes is in state `0`.  `splitW σ u` is the factorization
  `u = e₁ ⋯ e_r · t` with `eᵢ ∈ Xc σ`, `t ∈ NR σ` (`splitW_spec`, unique: `splitW_flatten`).
* `walk4St σ`: a six-state automaton (start, the states `1, 2, 3`, returned, dead) recognizing both
  (`Xc_eq_walk`, `NR_eq_walk`).  Its transition monoid is aperiodic, so `Xc σ` and `NR σ` are
  star-free for `σ ∈ {σm, σa}` (`starFree_of_dfa`, one kernel check each).
* `zcK_quot`: counting modulo `n` on all words reduces to the words in state `0`, by right
  quotients by the letter `2` (which moves by `-1` and is not counted).
* **Case (a)**, `zcA_height`: with `σa`, the counted letter is fixed, and the count of a word in
  state `0` is the number of blocks `[0]` of its factorization; the Transfer Lemma applies with
  `L₀ = {[0]}` and `L₁ = Xc σa ∖ {[0]}`.
-/

namespace GeneralizedStarHeight

open EpisodeAlgebra
open scoped Computability

/-! ### Displacements and counts -/

/-- All letters move: `0` and `1` by `+1`, `2` by `-1`. -/
def σm : Fin 3 → ZMod 4 := ![1, 1, 3]

/-- The counted letter `0` is fixed; `1` moves by `+1`, `2` by `-1`. -/
def σa : Fin 3 → ZMod 4 := ![0, 1, 3]

section Walk

variable (σ : Fin 3 → ZMod 4)

/-- The total displacement. -/
def dsum4 (w : List (Fin 3)) : ZMod 4 := (w.map σ).sum

lemma dsum4_append (u w : List (Fin 3)) : dsum4 σ (u ++ w) = dsum4 σ u + dsum4 σ w := by
  simp [dsum4]

lemma dsum4_cons (b : Fin 3) (w : List (Fin 3)) : dsum4 σ (b :: w) = σ b + dsum4 σ w := by
  simp [dsum4]

@[simp] lemma dsum4_nil : dsum4 σ [] = 0 := rfl

lemma dsum4_single (b : Fin 3) : dsum4 σ [b] = σ b := by simp [dsum4]

/-- Positions reading `0` in state `0`, from the state `s`. -/
def zc : ZMod 4 → List (Fin 3) → ℕ
  | _, [] => 0
  | s, b :: w => (if b = 0 ∧ s = 0 then 1 else 0) + zc (s + σ b) w

lemma zc_eq_vcountFrom : ∀ (s : ZMod 4) (w : List (Fin 3)), zc σ s w = vcountFrom σ 0 0 s w
  | _, [] => by simp [zc, vcountFrom_nil]
  | s, b :: w => by
      rw [zc, vcountFrom_cons, zc_eq_vcountFrom _ w]
      by_cases h : b = 0 ∧ s = 0
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]

lemma zc_append (s : ZMod 4) (u w : List (Fin 3)) :
    zc σ s (u ++ w) = zc σ s u + zc σ (s + dsum4 σ u) w := by
  induction u generalizing s with
  | nil => simp [zc]
  | cons b u ih => simp only [List.cons_append, zc, ih, dsum4_cons, add_assoc]

lemma zc_snoc (u : List (Fin 3)) (a : Fin 3) :
    zc σ 0 (u ++ [a]) = zc σ 0 u + if a = 0 ∧ dsum4 σ u = 0 then 1 else 0 := by
  rw [zc_append]; simp [zc]

/-! ### The first-return code -/

/-- **The first-return code** to state `0`. -/
def Xc : Language (Fin 3) :=
  {w | w ≠ [] ∧ dsum4 σ w = 0 ∧ ∀ p, p <+: w → p ≠ [] → p ≠ w → dsum4 σ p ≠ 0}

/-- Words with no nonempty prefix in state `0`. -/
def NR : Language (Fin 3) := {t | ∀ p, p <+: t → p ≠ [] → dsum4 σ p ≠ 0}

lemma nil_mem_NR : ([] : List (Fin 3)) ∈ NR σ :=
  fun _ hp hne => absurd (List.prefix_nil.mp hp) hne

lemma NR_eq_nil {t : List (Fin 3)} (ht : t ∈ NR σ) (h0 : dsum4 σ t = 0) : t = [] := by
  by_contra hne
  exact ht t List.prefix_rfl hne h0

/-- One step of the factorization. -/
def splitWStep (x : List (List (Fin 3)) × List (Fin 3)) (a : Fin 3) :
    List (List (Fin 3)) × List (Fin 3) :=
  if dsum4 σ (x.2 ++ [a]) = 0 then (x.1 ++ [x.2 ++ [a]], []) else (x.1, x.2 ++ [a])

/-- The factorization into first returns and a tail. -/
def splitW (u : List (Fin 3)) : List (List (Fin 3)) × List (Fin 3) :=
  u.foldl (splitWStep σ) ([], [])

lemma splitW_snoc (u : List (Fin 3)) (a : Fin 3) :
    splitW σ (u ++ [a]) = splitWStep σ (splitW σ u) a := by
  rw [splitW, List.foldl_append]; rfl

lemma mem_Xc_snoc {t : List (Fin 3)} (ht : t ∈ NR σ) {a : Fin 3} (h0 : dsum4 σ (t ++ [a]) = 0) :
    t ++ [a] ∈ Xc σ := by
  refine ⟨by simp, h0, fun p hp hne hpe => ?_⟩
  rcases List.prefix_concat_iff.mp hp with h | h
  · exact absurd h hpe
  · exact ht p h hne

lemma splitW_spec (u : List (Fin 3)) : (splitW σ u).1.flatten ++ (splitW σ u).2 = u ∧
    AllIn (Xc σ) (splitW σ u).1 ∧ (splitW σ u).2 ∈ NR σ := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨rfl, fun e he => by simp [splitW] at he, nil_mem_NR σ⟩
  | append_singleton u a ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [splitW_snoc]
      unfold splitWStep
      split_ifs with h0
      · refine ⟨?_, ?_, nil_mem_NR σ⟩
        · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
          rw [← List.append_assoc, h1]
        · refine AllIn.append h2 ?_
          intro e he
          simp only [List.mem_singleton] at he
          subst he
          exact mem_Xc_snoc σ h3 h0
      · refine ⟨?_, h2, ?_⟩
        · simp only; rw [← List.append_assoc, h1]
        · intro p hp hne
          rcases List.prefix_concat_iff.mp hp with h | h
          · rw [h]; exact h0
          · exact h3 p h hne

lemma foldl_splitWStep_noRet (es₀ : List (List (Fin 3))) :
    ∀ (v t₀ : List (Fin 3)), (∀ p, p <+: v → p ≠ [] → dsum4 σ (t₀ ++ p) ≠ 0) →
      v.foldl (splitWStep σ) (es₀, t₀) = (es₀, t₀ ++ v)
  | [], t₀, _ => by simp
  | b :: v, t₀, h => by
      rw [List.foldl_cons]
      have hb : dsum4 σ (t₀ ++ [b]) ≠ 0 := h [b] (by simp) (by simp)
      rw [show splitWStep σ (es₀, t₀) b = (es₀, t₀ ++ [b]) by simp [splitWStep, hb]]
      rw [foldl_splitWStep_noRet es₀ v (t₀ ++ [b])]
      · simp
      · intro p hp hne
        have := h (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩) (by simp)
        simpa using this

lemma foldl_splitWStep_Xc (es₀ : List (List (Fin 3))) {e : List (Fin 3)} (he : e ∈ Xc σ) :
    e.foldl (splitWStep σ) (es₀, []) = (es₀ ++ [e], []) := by
  obtain ⟨hne, h0, hpre⟩ := he
  rcases List.eq_nil_or_concat e with rfl | ⟨e', a, rfl⟩
  · exact absurd rfl hne
  simp only [List.concat_eq_append] at h0 hpre ⊢
  rw [List.foldl_append, foldl_splitWStep_noRet σ es₀ e' []]
  · simp [splitWStep, h0]
  · intro p hp hpne
    simp only [List.nil_append]
    refine hpre p (hp.trans (List.prefix_append _ _)) hpne ?_
    intro hpe
    have := hp.length_le
    rw [hpe] at this
    simp at this

lemma foldl_splitWStep_flatten (t : List (Fin 3)) (ht : t ∈ NR σ) :
    ∀ (es es₀ : List (List (Fin 3))), AllIn (Xc σ) es →
      (es.flatten ++ t).foldl (splitWStep σ) (es₀, []) = (es₀ ++ es, t)
  | [], es₀, _ => by
      simp only [List.flatten_nil, List.nil_append, List.append_nil]
      rw [foldl_splitWStep_noRet σ es₀ t []]
      · simp
      · intro p hp hne; simpa using ht p hp hne
  | e :: es, es₀, hes => by
      rw [List.flatten_cons, List.append_assoc, List.foldl_append,
        foldl_splitWStep_Xc σ es₀ (hes e (by simp)),
        foldl_splitWStep_flatten t ht es _ (fun f hf => hes f (by simp [hf]))]
      simp

/-- **Uniqueness of the factorization.** -/
lemma splitW_flatten {es : List (List (Fin 3))} (hes : AllIn (Xc σ) es) {t : List (Fin 3)}
    (ht : t ∈ NR σ) : splitW σ (es.flatten ++ t) = (es, t) := by
  have := foldl_splitWStep_flatten σ t ht es [] hes
  simpa [splitW] using this

lemma Xc_prefixCode : PrefixCode (Xc σ) := by
  refine ⟨fun h => h.1 rfl, fun e he f hf hef => ?_⟩
  by_contra hne
  exact hf.2.2 e hef he.1 hne he.2.1

lemma dsum4_flatten_Xc : ∀ {es : List (List (Fin 3))}, AllIn (Xc σ) es → dsum4 σ es.flatten = 0
  | [], _ => by simp [dsum4]
  | e :: es, hes => by
      rw [List.flatten_cons, dsum4_append, (hes e (by simp)).2.1,
        dsum4_flatten_Xc (fun f hf => hes f (by simp [hf]))]
      simp

lemma dsum4_splitW (u : List (Fin 3)) : dsum4 σ u = dsum4 σ (splitW σ u).2 := by
  conv_lhs => rw [← (splitW_spec σ u).1]
  rw [dsum4_append, dsum4_flatten_Xc σ (splitW_spec σ u).2.1, zero_add]

lemma splitW_of_dsum_zero {u : List (Fin 3)} (h : dsum4 σ u = 0) :
    (splitW σ u).2 = [] ∧ (splitW σ u).1.flatten = u := by
  have ht : (splitW σ u).2 = [] :=
    NR_eq_nil σ (splitW_spec σ u).2.2 (by rw [← dsum4_splitW]; exact h)
  refine ⟨ht, ?_⟩
  have := (splitW_spec σ u).1
  rw [ht, List.append_nil] at this
  exact this

lemma mem_bmod_Xc (L : Language (Fin 3)) (m r : ℕ) (u : List (Fin 3)) :
    u ∈ bmod (Xc σ) L m r ↔ dsum4 σ u = 0 ∧ bcount L (splitW σ u).1 % m = r := by
  constructor
  · rintro ⟨es, hes, rfl, hk⟩
    refine ⟨dsum4_flatten_Xc σ hes, ?_⟩
    have := splitW_flatten σ hes (nil_mem_NR σ)
    rw [List.append_nil] at this
    rw [this]; exact hk
  · rintro ⟨h0, hk⟩
    exact ⟨(splitW σ u).1, (splitW_spec σ u).2.1, (splitW_of_dsum_zero σ h0).2, hk⟩

/-! ### Counting along the factorization -/

lemma zc_zero_of_avoid : ∀ (w : List (Fin 3)) (s : ZMod 4),
    (∀ p, p <+: w → p ≠ w → s + dsum4 σ p ≠ 0) → zc σ s w = 0
  | [], _, _ => rfl
  | b :: w, s, hs => by
      rw [zc]
      have h1 : ¬ (b = 0 ∧ s = 0) := by
        rintro ⟨-, rfl⟩
        exact hs [] (List.nil_prefix) (by simp) (by simp)
      rw [if_neg h1, zero_add]
      apply zc_zero_of_avoid w
      intro p hp hpw
      have := hs (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩) (by simpa using hpw)
      rwa [dsum4_cons, ← add_assoc] at this

/-- A block counts `1` iff it begins with `0`. -/
lemma zc_Xc {e : List (Fin 3)} (he : e ∈ Xc σ) :
    zc σ 0 e = if e.head? = some 0 then 1 else 0 := by
  obtain ⟨hne, -, hpre⟩ := he
  obtain ⟨b, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  rw [zc, zero_add, zc_zero_of_avoid σ w (σ b)]
  · by_cases hb : b = 0 <;> simp [hb]
  · intro p hp hpw
    have := hpre (b :: p) (List.cons_prefix_cons.mpr ⟨rfl, hp⟩) (by simp) (by simpa using hpw)
    rwa [dsum4_cons] at this

/-- The blocks beginning with `0`. -/
def Head0 : Language (Fin 3) := {e | e.head? = some 0}

open Classical in
lemma zc_flatten_Xc : ∀ {es : List (List (Fin 3))}, AllIn (Xc σ) es →
    zc σ 0 es.flatten = bcount Head0 es
  | [], _ => by simp [zc, bcount]
  | e :: es, hes => by
      have he := hes e (by simp)
      rw [List.flatten_cons, zc_append, he.2.1, zero_add,
        zc_flatten_Xc (fun f hf => hes f (by simp [hf])), zc_Xc σ he]
      unfold bcount
      rw [List.countP_cons]
      by_cases h : e.head? = some 0
      · have h' : e ∈ Head0 := h
        simp [h, h']
        omega
      · have h' : e ∉ Head0 := h
        simp [h, h']

/-- On words in state `0`, the count is the number of blocks beginning with `0`. -/
lemma zc_eq_bcount {u : List (Fin 3)} (h : dsum4 σ u = 0) :
    zc σ 0 u = bcount Head0 (splitW σ u).1 := by
  conv_lhs => rw [← (splitW_of_dsum_zero σ h).2]
  exact zc_flatten_Xc σ (splitW_spec σ u).2.1

/-! ### The walk automaton -/

/-- Code of a nonzero state. -/
def enc4 (s : ZMod 4) : Fin 6 := ⟨s.val, by have := ZMod.val_lt s; omega⟩

/-- The walk automaton: `0` start, `1, 2, 3` the current state, `4` returned, `5` dead. -/
def walk4St (q : Fin 6) (a : Fin 3) : Fin 6 :=
  if q.val < 4 then (if (q.val : ZMod 4) + σ a = 0 then 4 else enc4 ((q.val : ZMod 4) + σ a))
  else 5

open Classical in
/-- The state of `walk4St` after a word, described directly. -/
noncomputable def walk4State (u : List (Fin 3)) : Fin 6 :=
  if u = [] then 0
  else if ∀ p, p <+: u → p ≠ [] → p ≠ u → dsum4 σ p ≠ 0 then
    (if dsum4 σ u = 0 then 4 else enc4 (dsum4 σ u))
  else 5

lemma encS_val (s : ZMod 4) : ((enc4 s).val : ZMod 4) = s := by
  simp [enc4]

lemma encS_lt (s : ZMod 4) : (enc4 s).val < 4 := ZMod.val_lt s

lemma encS_ne_four (s : ZMod 4) : enc4 s ≠ 4 := by
  intro h
  have := encS_lt s
  rw [h] at this
  exact absurd this (by decide)

lemma encS_ne_five (s : ZMod 4) : enc4 s ≠ 5 := by
  intro h
  have := encS_lt s
  rw [h] at this
  exact absurd this (by decide)

lemma walk4State_snoc (u : List (Fin 3)) (a : Fin 3) :
    walk4State σ (u ++ [a]) = walk4St σ (walk4State σ u) a := by
  have hs : dsum4 σ (u ++ [a]) = dsum4 σ u + σ a := by rw [dsum4_append, dsum4_single]
  unfold walk4State
  rw [if_neg (by simp)]
  by_cases hu : u = []
  · subst hu
    rw [if_pos rfl, if_pos]
    · simp [walk4St, dsum4_single]
    · intro p hp hne hpe
      rcases List.prefix_concat_iff.mp hp with h | h
      · exact absurd h hpe
      · exact absurd (List.prefix_nil.mp h) hne
  rw [if_neg hu]
  by_cases hc : ∀ p, p <+: u → p ≠ [] → p ≠ u → dsum4 σ p ≠ 0
  · rw [if_pos hc]
    by_cases h0 : dsum4 σ u = 0
    · rw [if_pos h0, if_neg]
      · simp [walk4St]
      · intro h
        exact h u (List.prefix_append _ _) hu (by simp) h0
    · rw [if_neg h0, if_pos]
      · simp only [walk4St, encS_lt, if_true, encS_val, hs]
      · intro p hp hne hpe
        rcases List.prefix_concat_iff.mp hp with h | h
        · exact absurd h hpe
        · by_cases hpu : p = u
          · rw [hpu]; exact h0
          · exact hc p h hne hpu
  · rw [if_neg hc, if_neg]
    · simp [walk4St]
    · intro h
      apply hc
      intro p hp hne hpe
      refine h p (hp.trans (List.prefix_append _ _)) hne ?_
      intro hpe'
      have := hp.length_le
      rw [hpe'] at this
      simp at this

lemma walk4State_eq_foldl (u : List (Fin 3)) : walk4State σ u = u.foldl (walk4St σ) 0 := by
  induction u using List.reverseRecOn with
  | nil => simp [walk4State]
  | append_singleton u a ih => rw [walk4State_snoc, ih, List.foldl_append]; rfl

lemma Xc_eq_walk : Xc σ = {u | u.foldl (walk4St σ) 0 = 4} := by
  ext u
  show u ∈ Xc σ ↔ u.foldl (walk4St σ) 0 = 4
  rw [← walk4State_eq_foldl]
  unfold walk4State
  constructor
  · rintro ⟨hne, h0, hpre⟩
    rw [if_neg hne, if_pos hpre, if_pos h0]
  · intro h
    by_cases hne : u = []
    · rw [if_pos hne] at h; exact absurd h (by decide)
    rw [if_neg hne] at h
    by_cases hc : ∀ p, p <+: u → p ≠ [] → p ≠ u → dsum4 σ p ≠ 0
    · rw [if_pos hc] at h
      by_cases h0 : dsum4 σ u = 0
      · exact ⟨hne, h0, hc⟩
      · rw [if_neg h0] at h; exact absurd h (encS_ne_four _)
    · rw [if_neg hc] at h; exact absurd h (by decide)

lemma NR_eq_walk : NR σ = {u | (u.foldl (walk4St σ) 0).val < 4} := by
  ext u
  show u ∈ NR σ ↔ (u.foldl (walk4St σ) 0).val < 4
  rw [← walk4State_eq_foldl]
  unfold walk4State
  constructor
  · intro h
    by_cases hne : u = []
    · rw [if_pos hne]; decide
    rw [if_neg hne, if_pos (fun p hp hne' _ => h p hp hne'),
      if_neg (h u List.prefix_rfl hne)]
    exact encS_lt _
  · intro h p hp hne
    by_cases hu : u = []
    · subst hu; exact absurd (List.prefix_nil.mp hp) hne
    rw [if_neg hu] at h
    by_cases hc : ∀ p, p <+: u → p ≠ [] → p ≠ u → dsum4 σ p ≠ 0
    · rw [if_pos hc] at h
      by_cases h0 : dsum4 σ u = 0
      · rw [if_pos h0] at h; exact absurd h (by decide)
      · by_cases hpu : p = u
        · rw [hpu]; exact h0
        · exact hc p hp hne hpu
    · rw [if_neg hc] at h; exact absurd h (by decide)

lemma letters3' : ∀ a : Fin 3, a ∈ ([0, 1, 2] : List (Fin 3)) := by decide

end Walk

/-! ### Star-freeness for the two displacement maps -/

lemma walk_cert_m : Aperiodic.certOK (List.finRange 6) [0, 1, 2] (walk4St σm)
    (Aperiodic.dfaCert (List.finRange 6) [0, 1, 2] (walk4St σm) 100) 6 = true := by
  decide +kernel

lemma walk_cert_a : Aperiodic.certOK (List.finRange 6) [0, 1, 2] (walk4St σa)
    (Aperiodic.dfaCert (List.finRange 6) [0, 1, 2] (walk4St σa) 100) 6 = true := by
  decide +kernel

lemma walkLang_starFree_m (P : Fin 6 → Prop) :
    HasHeightAtMost {u : List (Fin 3) | P (u.foldl (walk4St σm) 0)} 0 :=
  Aperiodic.starFree_of_dfa _ (List.mem_finRange) _ letters3' _ _ _ walk_cert_m 0 P

lemma walkLang_starFree_a (P : Fin 6 → Prop) :
    HasHeightAtMost {u : List (Fin 3) | P (u.foldl (walk4St σa) 0)} 0 :=
  Aperiodic.starFree_of_dfa _ (List.mem_finRange) _ letters3' _ _ _ walk_cert_a 0 P

theorem Xc_starFree_m : HasHeightAtMost (Xc σm) 0 := by
  rw [Xc_eq_walk]; exact walkLang_starFree_m (fun q => q = 4)

theorem NR_starFree_m : HasHeightAtMost (NR σm) 0 := by
  rw [NR_eq_walk]; exact walkLang_starFree_m (fun q => q.val < 4)

theorem Xc_starFree_a : HasHeightAtMost (Xc σa) 0 := by
  rw [Xc_eq_walk]; exact walkLang_starFree_a (fun q => q = 4)

/-! ### Reduction to the words in state `0` -/

/-- The words in state `0` whose count is `k` modulo `n`. -/
def zcK (σ : Fin 3 → ZMod 4) (n k : ℕ) : Language (Fin 3) :=
  {u | dsum4 σ u = 0 ∧ zc σ 0 u % n = k}

lemma zmod4_cases' : ∀ z : ZMod 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by decide

/-- Appending the letter `2` (displacement `3 = -1`, not counted) brings every word to state `0`
without changing the count. -/
lemma zcK_quot (σ : Fin 3 → ZMod 4) (hσ : σ 2 = 3) (n k : ℕ) :
    ({u : List (Fin 3) | zc σ 0 u % n = k} : Language (Fin 3)) =
      zcK σ n k + rightQuot 2 (zcK σ n k) +
      rightQuot 2 (rightQuot 2 (zcK σ n k)) +
        rightQuot 2 (rightQuot 2 (rightQuot 2 (zcK σ n k))) := by
  have hz : ∀ u : List (Fin 3), zc σ 0 (u ++ [2]) = zc σ 0 u := by
    intro u; rw [zc_snoc]; simp
  have hd : ∀ u : List (Fin 3), dsum4 σ (u ++ [2]) = dsum4 σ u + 3 := by
    intro u; rw [dsum4_append, dsum4_single, hσ]
  apply Language.ext
  intro u
  rw [Language.mem_add, Language.mem_add, Language.mem_add]
  show zc σ 0 u % n = k ↔ (((dsum4 σ u = 0 ∧ zc σ 0 u % n = k) ∨
    (dsum4 σ (u ++ [2]) = 0 ∧ zc σ 0 (u ++ [2]) % n = k)) ∨
    (dsum4 σ ((u ++ [2]) ++ [2]) = 0 ∧ zc σ 0 ((u ++ [2]) ++ [2]) % n = k)) ∨
    (dsum4 σ (((u ++ [2]) ++ [2]) ++ [2]) = 0 ∧ zc σ 0 (((u ++ [2]) ++ [2]) ++ [2]) % n = k)
  simp only [hz, hd]
  constructor
  · intro hc
    rcases zmod4_cases' (dsum4 σ u) with h | h | h | h <;> rw [h]
    · exact Or.inl (Or.inl (Or.inl ⟨rfl, hc⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨by decide, hc⟩))
    · exact Or.inl (Or.inr ⟨by decide, hc⟩)
    · exact Or.inr ⟨by decide, hc⟩
  · rintro (((⟨-, hc⟩ | ⟨-, hc⟩) | ⟨-, hc⟩) | ⟨-, hc⟩) <;> exact hc

/-- If the words in state `0` with count `k` modulo `n` have height one, so do all the words with
count `k` modulo `n`. -/
lemma zc_height_of_zcK (σ : Fin 3 → ZMod 4) (hσ : σ 2 = 3) {n k : ℕ}
    (h : HasHeightAtMost (zcK σ n k) 1) :
    HasHeightAtMost {u : List (Fin 3) | zc σ 0 u % n = k} 1 := by
  rw [zcK_quot σ hσ]
  exact ((h.union (h.rightQuot 2)).union ((h.rightQuot 2).rightQuot 2)).union
    (((h.rightQuot 2).rightQuot 2).rightQuot 2)

/-! ### Case (a): the counted letter is fixed -/

lemma Xc_a_head0 {e : List (Fin 3)} (he : e ∈ Xc σa) (h : e.head? = some 0) : e = [0] := by
  obtain ⟨hne, -, hpre⟩ := he
  obtain ⟨b, w, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.head?_cons, Option.some.injEq] at h
  subst h
  by_contra hw
  exact hpre [0] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (by simp)
    (fun h => hw h.symm) (by decide)

lemma zero_mem_Xc_a : [0] ∈ Xc σa := by
  refine ⟨by simp, by decide, fun p hp hne hpe => ?_⟩
  rcases List.prefix_cons_iff.mp hp with h | ⟨p', rfl, hp'⟩
  · exact absurd h hne
  · rw [List.prefix_nil.mp hp'] at hpe; exact absurd rfl hpe

/-- The blocks other than `[0]`. -/
def XcA1 : Language (Fin 3) := Xc σa ⊓ ({[0]} : Language (Fin 3))ᶜ

lemma XcA_split : ({[0]} : Language (Fin 3)) + XcA1 = Xc σa := by
  ext e
  rw [Language.mem_add]
  constructor
  · rintro (h | h)
    · rw [show e = [0] from h]; exact zero_mem_Xc_a
    · exact h.1
  · intro h
    by_cases h0 : e = [0]
    · exact Or.inl h0
    · exact Or.inr ⟨h, h0⟩

open Classical in
lemma bcount_head0_a : ∀ {es : List (List (Fin 3))}, AllIn (Xc σa) es →
    bcount Head0 es = bcount ({[0]} : Language (Fin 3)) es
  | [], _ => rfl
  | e :: es, hes => by
      have ih := bcount_head0_a (es := es) (fun f hf => hes f (by simp [hf]))
      unfold bcount at ih ⊢
      rw [List.countP_cons, List.countP_cons, ih]
      congr 1
      have : e ∈ Head0 ↔ e ∈ ({[0]} : Language (Fin 3)) := by
        constructor
        · intro h; exact Xc_a_head0 (hes e (by simp)) h
        · intro h; rw [show e = [0] from h]; rfl
      simp only [this]

lemma zcK_a_eq (n k : ℕ) : zcK σa n k = bmod (Xc σa) {[0]} n k := by
  ext u
  rw [mem_bmod_Xc]
  constructor
  · rintro ⟨h0, hk⟩
    refine ⟨h0, ?_⟩
    rw [← bcount_head0_a (splitW_spec σa u).2.1, ← zc_eq_bcount σa h0]
    exact hk
  · rintro ⟨h0, hk⟩
    refine ⟨h0, ?_⟩
    rw [zc_eq_bcount σa h0, bcount_head0_a (splitW_spec σa u).2.1]
    exact hk

/-- **Case (a).** With the counted letter fixed, counting it in state `0` modulo `n` has height
at most one. -/
theorem zcA_height {n k : ℕ} (hk : k < n) :
    HasHeightAtMost {u : List (Fin 3) | zc σa 0 u % n = k} 1 := by
  refine zc_height_of_zcK σa rfl ?_
  rw [zcK_a_eq]
  have hpc : PrefixCode (({[0]} : Language (Fin 3)) + XcA1) := by
    rw [XcA_split]; exact Xc_prefixCode σa
  have hdis : Disjoint ({[0]} : Language (Fin 3)) XcA1 :=
    Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1
  have h1 : HasHeightAtMost XcA1 0 := Xc_starFree_a.inter (HasHeightAtMost.singleton _ 0).compl
  have hs : HasHeightAtMost ({[0]} : Language (Fin 3))∗ 0 :=
    kstar_singleton_starFree [0] (by simp) (fun j hj hj' => by simp at hj'; omega)
  have h := transfer_height_one hpc hdis (HasHeightAtMost.singleton _ 0) h1 hs hk
  rwa [XcA_split] at h

end GeneralizedStarHeight
