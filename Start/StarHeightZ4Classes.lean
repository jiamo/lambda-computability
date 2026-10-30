import Start.StarHeightZ4Walk

/-!
# The block classes `C⁺`, `C⁻` of the moving case and their stars

Moving case: letters `0` (the counted letter `a`, `+1`), `1` (`b`, `+1`), `2` (`d`, `-1`), i.e. the
displacements `σm`.  The blocks of the first-return code `Xc σm` are classified by their first
letter and their last two letters (`bcls`):

* `C⁺` (`bcls = 1`): the blocks beginning with `a` whose last two letters are not `a` followed by
  an up letter (`a` or `b`);
* `C⁻` (`bcls = 2`): the blocks beginning with `b` or `d` whose last two letters are `a` followed by
  an up letter.

* `Ccl_starFree`, `Cco_starFree`: each class and its complement in `Xc σm` are star-free.
* `Ccl_kstar_starFree`: `C⁺∗` and `C⁻∗` are star-free.  A scanning automaton `fSt4` (walk state,
  first and last letter of the current block, rejection of a completed block outside the class)
  recognizes `C∗` (`mem_kstar_Ccl_iff`); it is compared with a six-state automaton on the reachable
  part of the product (`pairCheck`), whose transition monoid is aperiodic (`certOK`).
-/

namespace GeneralizedStarHeight

open EpisodeAlgebra
open scoped Computability

/-! ### The classes -/

/-- The class of a block with first letter `f`, penultimate letter `p` and last letter `a`. -/
def clsB (f p : Option (Fin 3)) (a : Fin 3) : Fin 3 :=
  if f = some 0 ∧ ¬ (p = some 0 ∧ a ≠ 2) then 1
  else if (f = some 1 ∨ f = some 2) ∧ p = some 0 ∧ a ≠ 2 then 2 else 0

/-- The class of a block, from its first letter and its last two letters. -/
def bcls (e : List (Fin 3)) : Fin 3 :=
  match e.reverse with
  | a :: p :: _ => clsB e.head? (some p) a
  | _ => 0

lemma bcls_snoc {t : List (Fin 3)} (ht : t ≠ []) (a : Fin 3) :
    bcls (t ++ [a]) = clsB t.head? t.getLast? a := by
  obtain ⟨t', p, rfl⟩ := (List.eq_nil_or_concat t).resolve_left ht
  simp only [List.concat_eq_append, bcls, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.getLast?_append, List.getLast?_singleton]
  simp [List.head?_append]

lemma bcls_comp (e : W3) : bcls (comp e) = bcls e := by
  by_cases h : e.length ≤ 4
  · rw [comp_short h]
  · obtain ⟨x, m, y, hm, hy, rfl⟩ := exists_long (by omega : 5 ≤ e.length)
    rw [comp_long x hm hy]
    match y, hy with
    | [y₁, y₂, y₃], _ => simp [bcls]

/-- The blocks of class `c`. -/
def Ccl (c : Fin 3) : Language (Fin 3) := Xc σm ⊓ {e | bcls e = c}

/-- The blocks outside class `c`. -/
def Cco (c : Fin 3) : Language (Fin 3) := Xc σm ⊓ {e | bcls e ≠ c}

lemma bclsPred_starFree (Pr : Fin 3 → Prop) : HasHeightAtMost {e : W3 | Pr (bcls e)} 0 := by
  have h := compPred_height (fun c => Pr (bcls c))
  have heq : ({e : W3 | Pr (bcls (comp e))} : Language (Fin 3)) = {e | Pr (bcls e)} := by
    ext e
    show Pr (bcls (comp e)) ↔ Pr (bcls e)
    rw [bcls_comp]
  rwa [heq] at h

theorem Ccl_starFree (c : Fin 3) : HasHeightAtMost (Ccl c) 0 :=
  Xc_starFree_m.inter (bclsPred_starFree fun x => x = c)

theorem Cco_starFree (c : Fin 3) : HasHeightAtMost (Cco c) 0 :=
  Xc_starFree_m.inter (bclsPred_starFree fun x => x ≠ c)

lemma Ccl_add_Cco (c : Fin 3) : Ccl c + Cco c = Xc σm := by
  ext e
  rw [Language.mem_add]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro h
    by_cases hc : bcls e = c
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, hc⟩

lemma Ccl_disjoint (c : Fin 3) : Disjoint (Ccl c) (Cco c) :=
  Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2

/-! ### The scanning automaton for `C∗` -/

lemma σm_ne_zero (a : Fin 3) : σm a ≠ 0 := by fin_cases a <;> decide

/-- Reads a word block by block: the walk state and the first and last letter of the current
block; `none` once a completed block lies outside the class `c`. -/
def fSt4 (c : Fin 3) : Option (ZMod 4 × Option (Fin 3) × Option (Fin 3)) → Fin 3 →
    Option (ZMod 4 × Option (Fin 3) × Option (Fin 3))
  | none, _ => none
  | some (s, f, p), a =>
    if s + σm a = 0 then (if clsB f p a = c then some (0, none, none) else none)
    else some (s + σm a, f.or (some a), some a)

/-- Acceptance: no incomplete block. -/
def fAcc4 : Option (ZMod 4 × Option (Fin 3) × Option (Fin 3)) → Bool
  | none => false
  | some (s, _, _) => decide (s = 0)

open Classical in
/-- The state of `fSt4 c` after a word, described directly. -/
noncomputable def fState4 (c : Fin 3) (u : List (Fin 3)) :
    Option (ZMod 4 × Option (Fin 3) × Option (Fin 3)) :=
  if ∀ e ∈ (splitW σm u).1, bcls e = c then
    some (dsum4 σm (splitW σm u).2, (splitW σm u).2.head?, (splitW σm u).2.getLast?) else none

lemma tail_ne_nil_of_ret {t : List (Fin 3)} {a : Fin 3} (h0 : dsum4 σm (t ++ [a]) = 0) :
    t ≠ [] := by
  rintro rfl
  exact σm_ne_zero a (by simpa [dsum4_single] using h0)

lemma head?_snoc (t : List (Fin 3)) (a : Fin 3) : (t ++ [a]).head? = t.head?.or (some a) := by
  cases t <;> simp

lemma fState4_snoc (c : Fin 3) (u : List (Fin 3)) (a : Fin 3) :
    fState4 c (u ++ [a]) = fSt4 c (fState4 c u) a := by
  have hs : dsum4 σm ((splitW σm u).2 ++ [a]) = dsum4 σm (splitW σm u).2 + σm a := by
    rw [dsum4_append, dsum4_single]
  unfold fState4
  rw [splitW_snoc]
  unfold splitWStep
  by_cases h0 : dsum4 σm ((splitW σm u).2 ++ [a]) = 0
  · have hs0 : dsum4 σm (splitW σm u).2 + σm a = 0 := by rw [← hs]; exact h0
    have hcl := bcls_snoc (tail_ne_nil_of_ret h0) a
    simp only [ite_eq_left h0]
    by_cases hall : ∀ e ∈ (splitW σm u).1, bcls e = c
    · simp only [ite_eq_left hall, fSt4, ite_eq_left hs0]
      by_cases hc : clsB (splitW σm u).2.head? (splitW σm u).2.getLast? a = c
      · rw [ite_eq_left hc, ite_eq_left]
        · rfl
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hall e he
          · rw [hcl]; exact hc
      · rw [ite_eq_right hc, ite_eq_right]
        intro h
        exact hc (hcl ▸ h _ (by simp))
    · rw [ite_eq_right hall, ite_eq_right]
      · rfl
      · intro h
        exact hall fun e he => h e (List.mem_append_left _ he)
  · have hs0 : ¬ (dsum4 σm (splitW σm u).2 + σm a = 0) := by rw [← hs]; exact h0
    simp only [ite_eq_right h0]
    by_cases hall : ∀ e ∈ (splitW σm u).1, bcls e = c
    · simp only [ite_eq_left hall, fSt4, ite_eq_right hs0]
      rw [hs, head?_snoc, List.getLast?_append, List.getLast?_singleton]
      rfl
    · simp only [ite_eq_right hall]
      rfl

lemma fState4_eq_foldl (c : Fin 3) (u : List (Fin 3)) :
    fState4 c u = u.foldl (fSt4 c) (some (0, none, none)) := by
  induction u using List.reverseRecOn with
  | nil => simp [fState4, splitW]
  | append_singleton u a ih => rw [fState4_snoc, ih, List.foldl_append]; rfl

lemma mem_kstar_Ccl_iff (c : Fin 3) (u : List (Fin 3)) :
    u ∈ (Ccl c)∗ ↔ fAcc4 (fState4 c u) = true := by
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨es, rfl, hes⟩
    have hsp := splitW_flatten σm (fun e he => (hes e he).1) (nil_mem_NR σm)
    rw [List.append_nil] at hsp
    unfold fState4
    rw [hsp]
    dsimp only
    have hall : ∀ e ∈ es, bcls e = c := fun e he => (hes e he).2
    rw [ite_eq_left hall]
    simp [fAcc4]
  · intro h
    unfold fState4 at h
    by_cases hall : ∀ e ∈ (splitW σm u).1, bcls e = c
    · rw [ite_eq_left hall] at h
      simp only [fAcc4, decide_eq_true_eq] at h
      have ht := NR_eq_nil σm (splitW_spec σm u).2.2 h
      refine ⟨(splitW σm u).1, ?_, fun e he => ⟨(splitW_spec σm u).2.1 e he, hall e he⟩⟩
      have := (splitW_spec σm u).1
      rw [ht, List.append_nil] at this
      exact this.symm
    · rw [ite_eq_right hall] at h
      exact absurd h (by simp [fAcc4])

/-! ### Six-state automata for `C⁺∗` and `C⁻∗` -/

/-- A six-state automaton for `C⁺∗` (start and accepting state `0`). -/
def cPlusDFA : Fin 6 → Fin 3 → Fin 6 :=
  ![![1, 2, 2], ![3, 3, 0], ![2, 2, 2], ![4, 5, 1], ![2, 2, 3], ![0, 0, 3]]

/-- A six-state automaton for `C⁻∗` (start and accepting state `0`). -/
def cMinusDFA : Fin 6 → Fin 3 → Fin 6 :=
  ![![1, 2, 5], ![1, 1, 1], ![3, 3, 1], ![4, 5, 2], ![0, 0, 3], ![1, 1, 3]]

/-- The six-state automaton of class `c ∈ {1, 2}`. -/
def cDFA (c : Fin 3) : Fin 6 → Fin 3 → Fin 6 := if c = 1 then cPlusDFA else cMinusDFA

set_option Elab.async false

lemma cPlus_agree_check : pairCheck [0, 1, 2] (fSt4 1) cPlusDFA (some (0, none, none)) 0 fAcc4
    (fun q => decide (q = 0)) 40 = true := by
  decide +kernel

lemma cMinus_agree_check : pairCheck [0, 1, 2] (fSt4 2) cMinusDFA (some (0, none, none)) 0 fAcc4
    (fun q => decide (q = 0)) 40 = true := by
  decide +kernel

lemma cPlus_cert : Aperiodic.certOK (List.finRange 6) [0, 1, 2] cPlusDFA
    (Aperiodic.dfaCert (List.finRange 6) [0, 1, 2] cPlusDFA 100) 6 = true := by
  decide +kernel

lemma cMinus_cert : Aperiodic.certOK (List.finRange 6) [0, 1, 2] cMinusDFA
    (Aperiodic.dfaCert (List.finRange 6) [0, 1, 2] cMinusDFA 100) 6 = true := by
  decide +kernel

lemma Ccl_kstar_eq {c : Fin 3} (hc : c = 1 ∨ c = 2) :
    (Ccl c)∗ = {u | u.foldl (cDFA c) 0 = 0} := by
  ext u
  show u ∈ (Ccl c)∗ ↔ u.foldl (cDFA c) 0 = 0
  rw [mem_kstar_Ccl_iff, fState4_eq_foldl]
  rcases hc with rfl | rfl
  · rw [pairCheck_spec letters3' cPlus_agree_check u]
    simp [cDFA]
  · rw [pairCheck_spec letters3' cMinus_agree_check u]
    simp [cDFA]

/-- **`C⁺∗` and `C⁻∗` are star-free.** -/
theorem Ccl_kstar_starFree {c : Fin 3} (hc : c = 1 ∨ c = 2) : HasHeightAtMost (Ccl c)∗ 0 := by
  rw [Ccl_kstar_eq hc]
  rcases hc with rfl | rfl
  · exact Aperiodic.starFree_of_dfa _ List.mem_finRange _ letters3' _ _ _ cPlus_cert 0
      (fun q => q = 0)
  · exact Aperiodic.starFree_of_dfa _ List.mem_finRange _ letters3' _ _ _ cMinus_cert 0
      (fun q => q = 0)

/-- **Counting the blocks of `C⁺` or `C⁻`**, by the Transfer Lemma. -/
theorem bmodC_height {c : Fin 3} (hc : c = 1 ∨ c = 2) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (bmod (Xc σm) (Ccl c) m r) 1 := by
  have h := transfer_height_one (L₀ := Ccl c) (L₁ := Cco c)
    (by rw [Ccl_add_Cco]; exact Xc_prefixCode σm) (Ccl_disjoint c) (Ccl_starFree c)
    (Cco_starFree c) (Ccl_kstar_starFree hc) hr
  rwa [Ccl_add_Cco] at h

end GeneralizedStarHeight
