import Start.StarHeightA4Core

/-!
# Finite-state checks and strictly locally testable languages

* `checkInv`: a finite list of states containing the start state, closed under the transitions,
  on which a Boolean predicate holds.  `checkInv_spec`: the predicate then holds after reading any
  word.  The list is produced by `explore` (breadth-first search with fuel) and the check is closed
  by `decide`.
* `sltLang e P S G`: the words (other than `[]`, which is included iff `e`) with a prefix in `P`,
  a suffix in `S` and no factor in `G` (a strictly locally testable language).
  `sltLang_height`: these languages are star-free.  `mem_sltLang_iff`: when the words of `P` and
  `S` have length at most `3` and those of `G` length between `1` and `4`, membership is computed
  by the automaton `sltStep` (which remembers the first three and the last three letters).
-/

namespace GeneralizedStarHeight

universe u

open scoped Computability

variable {α : Type u}

section Check

variable {Q : Type*} [DecidableEq Q]

/-- Breadth-first exploration of the states reachable from `todo`, with fuel. -/
def explore (letters : List α) (δ : Q → α → Q) : ℕ → List Q → List Q → List Q
  | 0, _, seen => seen
  | n + 1, todo, seen =>
    let fresh := todo.foldl (fun acc q => letters.foldl (fun acc a =>
      let x := δ q a; if seen.contains x || acc.contains x then acc else x :: acc) acc) []
    if fresh = [] then seen else explore letters δ n fresh (seen ++ fresh)

/-- `R` contains `q₀`, is closed under `δ`, and satisfies `P`. -/
def checkInv (letters : List α) (δ : Q → α → Q) (q₀ : Q) (P : Q → Bool) (R : List Q) : Bool :=
  R.contains q₀ && R.all (fun q => P q && letters.all fun a => R.contains (δ q a))

lemma checkInv_spec {letters : List α} (hl : ∀ a, a ∈ letters) {δ : Q → α → Q} {q₀ : Q}
    {P : Q → Bool} {R : List Q} (h : checkInv letters δ q₀ P R = true) (w : List α) :
    P (w.foldl δ q₀) = true := by
  simp only [checkInv, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at h
  obtain ⟨h0, hR⟩ := h
  have key : ∀ (w : List α) (q : Q), q ∈ R → w.foldl δ q ∈ R := by
    intro w
    induction w with
    | nil => intro q hq; exact hq
    | cons a w ih =>
        intro q hq
        exact ih _ ((hR q hq).2 a (hl a))
  exact (hR _ (key w q₀ h0)).1

variable {Q₁ Q₂ : Type*} [DecidableEq Q₁] [DecidableEq Q₂]

/-- Two automata agree on every word: checked on the reachable part of their product. -/
def pairCheck (letters : List α) (δ₁ : Q₁ → α → Q₁) (δ₂ : Q₂ → α → Q₂) (q₁ : Q₁) (q₂ : Q₂)
    (acc₁ : Q₁ → Bool) (acc₂ : Q₂ → Bool) (fuel : ℕ) : Bool :=
  checkInv letters (fun q a => (δ₁ q.1 a, δ₂ q.2 a)) (q₁, q₂) (fun q => acc₁ q.1 == acc₂ q.2)
    (explore letters (fun q a => (δ₁ q.1 a, δ₂ q.2 a)) fuel [(q₁, q₂)] [(q₁, q₂)])

omit [DecidableEq Q₁] [DecidableEq Q₂] in
lemma foldl_prod (δ₁ : Q₁ → α → Q₁) (δ₂ : Q₂ → α → Q₂) :
    ∀ (w : List α) (q : Q₁ × Q₂),
      w.foldl (fun q a => (δ₁ q.1 a, δ₂ q.2 a)) q = (w.foldl δ₁ q.1, w.foldl δ₂ q.2)
  | [], _ => rfl
  | _ :: w, _ => foldl_prod δ₁ δ₂ w _

lemma pairCheck_spec {letters : List α} (hl : ∀ a, a ∈ letters) {δ₁ : Q₁ → α → Q₁}
    {δ₂ : Q₂ → α → Q₂} {q₁ : Q₁} {q₂ : Q₂} {acc₁ : Q₁ → Bool} {acc₂ : Q₂ → Bool} {fuel : ℕ}
    (h : pairCheck letters δ₁ δ₂ q₁ q₂ acc₁ acc₂ fuel = true) (w : List α) :
    acc₁ (w.foldl δ₁ q₁) = acc₂ (w.foldl δ₂ q₂) := by
  have := checkInv_spec hl h w
  rw [foldl_prod] at this
  simpa using this

end Check

/-! ### Strictly locally testable languages -/

section SLT

/-- The last three letters. -/
def last3 (w : List α) : List α := w.drop (w.length - 3)

/-- The strictly locally testable language with prefixes `P`, suffixes `S`, forbidden factors
`G`; it contains `[]` iff `e`. -/
def sltLang (e : Bool) (P S G : List (List α)) : Language α :=
  {u | (u = [] ∧ e = true) ∨
    (u ≠ [] ∧ (∃ p ∈ P, p <+: u) ∧ (∃ s ∈ S, s <:+ u) ∧ ∀ g ∈ G, ¬ g <:+: u)}

lemma last3_suffix (u : List α) : last3 u <:+ u := List.drop_suffix _ _

lemma last3_length (u : List α) : (last3 u).length = min u.length 3 := by
  simp only [last3, List.length_drop]; omega

lemma last3_snoc (u : List α) (a : α) : last3 (u ++ [a]) = last3 (last3 u ++ [a]) := by
  have h1 : last3 u ++ [a] = (u ++ [a]).drop (u.length - 3) := by
    rw [last3, List.drop_append_of_le_length (by omega)]
  rw [h1]
  unfold last3
  rw [List.drop_drop]
  congr 1
  simp only [List.length_append, List.length_singleton, List.length_drop]
  omega

lemma take3_snoc (u : List α) (a : α) :
    (u ++ [a]).take 3 = if (u.take 3).length < 3 then u.take 3 ++ [a] else u.take 3 := by
  split_ifs with h
  · simp only [List.length_take] at h
    rw [List.take_append, List.take_of_length_le (by omega : u.length ≤ 3)]
    rw [List.take_of_length_le (by simp; omega : [a].length ≤ 3 - u.length)]
  · simp only [List.length_take] at h
    rw [List.take_append_of_le_length (by omega)]

lemma suffix_iff_last3 {s u : List α} (hs : s.length ≤ 3) : s <:+ u ↔ s <:+ last3 u := by
  constructor
  · intro h
    refine List.suffix_of_suffix_length_le h (last3_suffix u) ?_
    rw [last3_length]
    have := h.length_le
    omega
  · intro h; exact h.trans (last3_suffix u)

lemma prefix_iff_take3 {p u : List α} (hp : p.length ≤ 3) : p <+: u ↔ p <+: u.take 3 := by
  constructor
  · intro h
    refine List.prefix_of_prefix_length_le h (List.take_prefix _ _) ?_
    have := h.length_le
    simp; omega
  · intro h; exact h.trans (List.take_prefix _ _)

lemma infix_snoc_iff {g u : List α} {a : α} (hg4 : g.length ≤ 4) :
    g <:+: u ++ [a] ↔ g <:+: u ∨ g <:+ last3 u ++ [a] := by
  constructor
  · rintro ⟨s, t, hst⟩
    rcases List.eq_nil_or_concat t with rfl | ⟨t', b, rfl⟩
    · right
      have hsuf : g <:+ u ++ [a] := ⟨s, by simpa using hst⟩
      have hsuf2 : last3 u ++ [a] <:+ u ++ [a] := by
        obtain ⟨t, ht⟩ := last3_suffix u
        exact ⟨t, by rw [← List.append_assoc, ht]⟩
      refine List.suffix_of_suffix_length_le hsuf hsuf2 ?_
      have := hsuf.length_le
      simp only [List.length_append, List.length_singleton] at this ⊢
      rw [last3_length]
      omega
    · left
      simp only [List.concat_eq_append, ← List.append_assoc] at hst
      have := List.append_inj_left' hst rfl
      exact ⟨s, t', this⟩
  · rintro (h | h)
    · exact h.trans (List.infix_append [] u [a])
    · obtain ⟨t, ht⟩ := last3_suffix u
      exact (h.trans ⟨t, by rw [← List.append_assoc, ht]⟩).isInfix

section Automaton

variable [DecidableEq α]

open Classical in
/-- The state of the recognizing automaton after reading `u`. -/
noncomputable def sltState (G : List (List α)) (u : List α) : Option (List α × List α) :=
  if ∃ g ∈ G, g <:+: u then none else some (u.take 3, last3 u)

/-- One transition of the recognizing automaton. -/
def sltStep (G : List (List α)) : Option (List α × List α) → α → Option (List α × List α)
  | none, _ => none
  | some (p, s), a =>
    if G.any (fun g => g.isSuffixOf (s ++ [a])) then none
    else some (if p.length < 3 then p ++ [a] else p, last3 (s ++ [a]))

/-- Acceptance. -/
def sltAcc (e : Bool) (P S : List (List α)) : Option (List α × List α) → Bool
  | none => false
  | some (p, s) =>
    if p = [] then e else P.any (fun x => x.isPrefixOf p) && S.any (fun x => x.isSuffixOf s)

lemma sltState_nil {G : List (List α)} (hG : ∀ g ∈ G, g ≠ []) :
    sltState G ([] : List α) = some ([], []) := by
  unfold sltState
  rw [if_neg]
  · rfl
  · rintro ⟨g, hg, hinf⟩
    exact hG g hg (List.eq_nil_of_infix_nil hinf)

lemma sltState_snoc {G : List (List α)} (hG : ∀ g ∈ G, g ≠ [] ∧ g.length ≤ 4) (u : List α)
    (a : α) : sltState G (u ++ [a]) = sltStep G (sltState G u) a := by
  unfold sltState
  by_cases hu : ∃ g ∈ G, g <:+: u
  · rw [if_pos hu, if_pos]
    · rfl
    · obtain ⟨g, hg, h⟩ := hu
      exact ⟨g, hg, h.trans (List.infix_append [] u [a])⟩
  · rw [if_neg hu, sltStep]
    by_cases hb : G.any (fun g => g.isSuffixOf (last3 u ++ [a])) = true
    · rw [if_pos hb, if_pos]
      obtain ⟨g, hg, h⟩ := List.any_eq_true.mp hb
      exact ⟨g, hg, (infix_snoc_iff (hG g hg).2).mpr
        (Or.inr (List.isSuffixOf_iff_suffix.mp h))⟩
    · rw [if_neg hb, if_neg, take3_snoc, last3_snoc]
      rintro ⟨g, hg, h⟩
      rcases (infix_snoc_iff (hG g hg).2).mp h with h | h
      · exact hu ⟨g, hg, h⟩
      · exact hb (List.any_eq_true.mpr ⟨g, hg, List.isSuffixOf_iff_suffix.mpr h⟩)

lemma sltState_eq_foldl {G : List (List α)} (hG : ∀ g ∈ G, g ≠ [] ∧ g.length ≤ 4)
    (u : List α) : sltState G u = u.foldl (sltStep G) (some ([], [])) := by
  induction u using List.reverseRecOn with
  | nil => exact sltState_nil fun g hg => (hG g hg).1
  | append_singleton u a ih => rw [sltState_snoc hG, ih, List.foldl_append]; rfl

lemma mem_sltLang_iff {e : Bool} {P S G : List (List α)} (hP : ∀ p ∈ P, p.length ≤ 3)
    (hS : ∀ s ∈ S, s.length ≤ 3) (hG : ∀ g ∈ G, g ≠ [] ∧ g.length ≤ 4) (u : List α) :
    u ∈ sltLang e P S G ↔ sltAcc e P S (sltState G u) = true := by
  unfold sltState
  show (u = [] ∧ e = true) ∨ _ ↔ _
  by_cases hu : ∃ g ∈ G, g <:+: u
  · rw [if_pos hu]
    obtain ⟨g, hg, h⟩ := hu
    simp only [sltAcc, Bool.false_eq_true, iff_false, not_or, not_and]
    refine ⟨fun hn _ => ?_, fun _ _ _ hall => hall g hg h⟩
    subst hn
    exact (hG g hg).1 (List.eq_nil_of_infix_nil h)
  · rw [if_neg hu]
    simp only [not_exists, not_and] at hu
    simp only [sltAcc]
    by_cases hn : u = []
    · subst hn; simp
    · have ht : u.take 3 ≠ [] := by
        intro h
        simp only [List.take_eq_nil_iff, OfNat.ofNat_ne_zero, false_or] at h
        exact hn h
      rw [if_neg ht]
      simp only [hn, false_and, false_or, ne_eq, not_false_eq_true, true_and, Bool.and_eq_true,
        List.any_eq_true, List.isPrefixOf_iff_prefix, List.isSuffixOf_iff_suffix]
      constructor
      · rintro ⟨⟨p, hp, h1⟩, ⟨s, hs, h2⟩, -⟩
        exact ⟨⟨p, hp, (prefix_iff_take3 (hP p hp)).mp h1⟩,
          ⟨s, hs, (suffix_iff_last3 (hS s hs)).mp h2⟩⟩
      · rintro ⟨⟨p, hp, h1⟩, ⟨s, hs, h2⟩⟩
        exact ⟨⟨p, hp, (prefix_iff_take3 (hP p hp)).mpr h1⟩,
          ⟨s, hs, (suffix_iff_last3 (hS s hs)).mpr h2⟩, hu⟩

end Automaton

lemma mem_preLang_iff (P : List (List α)) (u : List α) :
    u ∈ (⨆ i : Fin P.length, ({P[i]} : Language α) * ⊤) ↔ ∃ p ∈ P, p <+: u := by
  rw [Language.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨x, hx, t, -, rfl⟩ := Language.mem_mul.mp hi
    exact ⟨P[i], List.getElem_mem _, ⟨t, by rw [show x = P[i] from hx]⟩⟩
  · rintro ⟨p, hp, h⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨t, ht⟩ := h
    exact ⟨⟨i, hi⟩, Language.mem_mul.mpr ⟨_, rfl, t, trivial, ht⟩⟩

lemma mem_sufLang_iff (S : List (List α)) (u : List α) :
    u ∈ (⨆ i : Fin S.length, (⊤ : Language α) * {S[i]}) ↔ ∃ s ∈ S, s <:+ u := by
  rw [Language.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨t, -, x, hx, rfl⟩ := Language.mem_mul.mp hi
    exact ⟨S[i], List.getElem_mem _, ⟨t, by rw [show x = S[i] from hx]⟩⟩
  · rintro ⟨s, hs, h⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    obtain ⟨t, ht⟩ := h
    exact ⟨⟨i, hi⟩, Language.mem_mul.mpr ⟨t, trivial, _, rfl, ht⟩⟩

lemma mem_noFacLang_iff (G : List (List α)) (u : List α) :
    u ∈ (⨅ i : Fin G.length, ((⊤ : Language α) * {G[i]} * ⊤)ᶜ) ↔ ∀ g ∈ G, ¬ g <:+: u := by
  rw [HasHeightAtMost.mem_iInf_lang]
  constructor
  · intro h g hg hinf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨s, t, hst⟩ := hinf
    exact h ⟨i, hi⟩ (Language.mem_mul.mpr ⟨s ++ G[i], Language.mem_mul.mpr
      ⟨s, trivial, _, rfl, rfl⟩, t, trivial, hst⟩)
  · intro h i hi
    obtain ⟨y, hy, t, -, rfl⟩ := Language.mem_mul.mp hi
    obtain ⟨s, -, x, hx, rfl⟩ := Language.mem_mul.mp hy
    exact h G[i] (List.getElem_mem _) ⟨s, t, by rw [show x = G[i] from hx]⟩

/-- **Strictly locally testable languages are star-free.** -/
theorem sltLang_height (e : Bool) (P S G : List (List α)) :
    HasHeightAtMost (sltLang e P S G) 0 := by
  have heq : sltLang e P S G = (if e then 1 else 0) + ((1 : Language α)ᶜ ⊓
      (⨆ i : Fin P.length, {P[i]} * ⊤) ⊓ (⨆ i : Fin S.length, ⊤ * {S[i]}) ⊓
      ⨅ i : Fin G.length, (⊤ * {G[i]} * ⊤)ᶜ) := by
    ext u
    have e1 : (u ∈ (if e then (1 : Language α) else 0)) ↔ (u = [] ∧ e = true) := by
      cases e
      · simp only [Bool.false_eq_true, if_false, and_false, iff_false]
        exact Language.notMem_zero u
      · simp [Language.mem_one]
    have h1 : u ∈ (1 : Language α)ᶜ ↔ u ≠ [] := by
      show ¬ u ∈ (1 : Language α) ↔ _
      rw [Language.mem_one]
    show (u = [] ∧ e = true) ∨ _ ↔ _
    rw [Language.mem_add, e1, Language.mem_inf, Language.mem_inf, Language.mem_inf, h1,
      mem_preLang_iff, mem_sufLang_iff, mem_noFacLang_iff]
    simp only [and_assoc]
  rw [heq]
  refine HasHeightAtMost.union ?_ ?_
  · split_ifs
    · exact HasHeightAtMost.one 0
    · exact HasHeightAtMost.zero 0
  · refine HasHeightAtMost.inter (HasHeightAtMost.inter (HasHeightAtMost.inter
      (HasHeightAtMost.one 0).compl ?_) ?_) ?_
    · exact HasHeightAtMost.iSup _ fun i =>
        (HasHeightAtMost.singleton _ 0).concat (HasHeightAtMost.top 0)
    · exact HasHeightAtMost.iSup _ fun i =>
        (HasHeightAtMost.top 0).concat (HasHeightAtMost.singleton _ 0)
    · exact HasHeightAtMost.iInf _ fun i =>
        (((HasHeightAtMost.top 0).concat (HasHeightAtMost.singleton _ 0)).concat
          (HasHeightAtMost.top 0)).compl

end SLT

end GeneralizedStarHeight
