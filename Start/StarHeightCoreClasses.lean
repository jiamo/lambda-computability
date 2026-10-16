import Start.StarHeightCoreClassCheck

/-!
# The twelve classes: star-freeness and their stars

* `Fcls_height`, `Fco_height`: each class `Fᵢ` and its complement in `coreX` are star-free.
* `Fcls_kstar_eq`: each `Fᵢ∗` is the strictly locally testable language with the data `fData i`
  (prefixes, suffixes, forbidden factors), checked on the product of two finite automata
  (`f_agree`).
  Hence `Fᵢ∗` is star-free (`Fcls_kstar_height`).
* `bmodF_height`: counting the blocks in `Fᵢ` modulo `m` has height at most one (Transfer Lemma).
* `acCount_height`: the words with `acCount u ≡ r (mod m)` have height at most one.
-/

namespace GeneralizedStarHeight

open EpisodeAlgebra
open scoped Computability

/-! ### Languages defined through `comp` -/

lemma comp_length_long {e : W3} (h : 5 ≤ e.length) : (comp e).length = 4 := by
  obtain ⟨x, m, y, hm, hy, rfl⟩ := exists_long h
  rw [comp_long x hm hy]; simp [hy]

lemma comp_length_le (e : W3) : (comp e).length ≤ 4 := by
  by_cases h : e.length ≤ 4
  · rw [comp_short h]; exact h
  · rw [comp_length_long (by omega)]

lemma compEq_height (c : W3) : HasHeightAtMost {e | comp e = c} 0 := by
  by_cases h3 : c.length ≤ 3
  · have : ({e | comp e = c} : Language (Fin 3)) = {c} := by
      ext e
      show comp e = c ↔ e = c
      constructor
      · intro he
        by_cases hl : e.length ≤ 4
        · rw [comp_short hl] at he; exact he
        · have := comp_length_long (by omega : 5 ≤ e.length)
          rw [he] at this; omega
      · intro he
        rw [show e = c from he, comp_short (by omega)]
    rw [this]; exact HasHeightAtMost.singleton _ 0
  by_cases h4 : c.length = 4
  · obtain ⟨x, y, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (l := c)
      (by omega))
    have hy : y.length = 3 := by simp at h4; omega
    have : ({e | comp e = x :: y} : Language (Fin 3)) =
        {x :: y} + {[x]} * (1 : Language (Fin 3))ᶜ * {y} := by
      ext e
      show comp e = x :: y ↔ e ∈ ({x :: y} : Language (Fin 3)) +
        {[x]} * (1 : Language (Fin 3))ᶜ * {y}
      rw [Language.mem_add]
      constructor
      · intro he
        by_cases hl : e.length ≤ 4
        · rw [comp_short hl] at he; exact Or.inl he
        · obtain ⟨x', m, y', hm, hy', rfl⟩ := exists_long (by omega : 5 ≤ e.length)
          rw [comp_long x' hm hy'] at he
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          refine Or.inr (Language.mem_mul.mpr ⟨[x'] ++ m, Language.mem_mul.mpr
            ⟨[x'], rfl, m, ?_, rfl⟩, y', rfl, by simp⟩)
          show ¬ m ∈ (1 : Language (Fin 3))
          rw [Language.mem_one]; exact hm
      · rintro (he | he)
        · rw [show e = x :: y from he, comp_short (by simp; omega)]
        · obtain ⟨z, hz, w, hw, rfl⟩ := Language.mem_mul.mp he
          obtain ⟨v, hv, m, hm, rfl⟩ := Language.mem_mul.mp hz
          rw [show v = [x] from hv, show w = y from hw]
          have hm' : m ≠ [] := by
            intro h
            exact hm (by rw [h]; exact (Language.mem_one _).mpr rfl)
          simpa using comp_long x hm' hy
    rw [this]
    exact (HasHeightAtMost.singleton _ 0).union (((HasHeightAtMost.singleton _ 0).concat
      (HasHeightAtMost.one 0).compl).concat (HasHeightAtMost.singleton _ 0))
  · have : ({e | comp e = c} : Language (Fin 3)) = (0 : Language (Fin 3)) := by
      ext e
      show comp e = c ↔ e ∈ (0 : Language (Fin 3))
      constructor
      · intro he
        have := comp_length_le e
        rw [he] at this; omega
      · intro he; exact absurd he (Language.notMem_zero e)
    rw [this]; exact HasHeightAtMost.zero 0

/-- Every language defined by a condition on `comp` is star-free. -/
lemma compPred_height (Pr : W3 → Prop) : HasHeightAtMost {e | Pr (comp e)} 0 := by
  have hfin : Set.Finite {c : W3 | c.length ≤ 4 ∧ Pr c} :=
    (List.finite_length_le (Fin 3) 4).subset fun c hc => hc.1
  have := hfin.to_subtype
  have heq : ({e | Pr (comp e)} : Language (Fin 3)) =
      ⨆ c : {c : W3 | c.length ≤ 4 ∧ Pr c}, ({e | comp e = c.1} : Language (Fin 3)) := by
    ext e
    show Pr (comp e) ↔ e ∈ (⨆ c : {c : W3 | c.length ≤ 4 ∧ Pr c},
      ({e | comp e = c.1} : Language (Fin 3)))
    constructor
    · intro h
      exact Language.mem_iSup.mpr ⟨⟨comp e, comp_length_le e, h⟩, rfl⟩
    · intro h
      obtain ⟨c, hc⟩ := Language.mem_iSup.mp h
      show Pr (comp e)
      rw [show comp e = c.1 from hc]
      exact c.2.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun c => compEq_height c.1

/-- **Each class is star-free.** -/
theorem Fcls_height (i : Fin 12) : HasHeightAtMost (Fcls i) 0 :=
  coreX_height.inter (compPred_height fun c => cls c = i.succ)

theorem Fco_height (i : Fin 12) : HasHeightAtMost (Fco i) 0 :=
  coreX_height.inter (compPred_height fun c => cls c ≠ i.succ)

lemma Fcls_add_Fco (i : Fin 12) : Fcls i + Fco i = coreX := by
  ext e
  rw [Language.mem_add]
  constructor
  · rintro (h | h)
    · exact h.1
    · exact h.1
  · intro h
    by_cases hc : cls (comp e) = i.succ
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, hc⟩

lemma Fcls_disjoint (i : Fin 12) : Disjoint (Fcls i) (Fco i) :=
  Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2

/-! ### The stars of the classes -/

open Classical in
/-- The state of `fStep` after reading `u`. -/
noncomputable def fState (i : Fin 12) (u : W3) : Option (ZMod 3 × W3) :=
  if ∀ e ∈ (split u).1, cls (comp e) = i.succ then
    some (dsum step3 (split u).2, comp (split u).2) else none

lemma fState_snoc (i : Fin 12) (u : W3) (a : Fin 3) :
    fState i (u ++ [a]) = fStep i (fState i u) a := by
  have hs : dsum step3 ((split u).2 ++ [a]) = dsum step3 (split u).2 + step3 a := by
    rw [dsum_append]; simp [dsum]
  unfold fState
  rw [split_snoc]
  unfold splitStep
  by_cases h0 : dsum step3 ((split u).2 ++ [a]) = 0
  · have hs0 : dsum step3 (split u).2 + step3 a = 0 := by rw [← hs]; exact h0
    simp only [if_pos h0]
    by_cases hall : ∀ e ∈ (split u).1, cls (comp e) = i.succ
    · simp only [if_pos hall, fStep, if_pos hs0, ← comp_snoc]
      by_cases hc : cls (comp ((split u).2 ++ [a])) = i.succ
      · rw [if_pos hc, if_pos]
        · rfl
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with he | rfl
          · exact hall e he
          · exact hc
      · rw [if_neg hc, if_neg]
        intro h
        exact hc (h _ (by simp))
    · rw [if_neg hall, if_neg]
      · rfl
      · intro h
        exact hall fun e he => h e (List.mem_append_left _ he)
  · have hs0 : ¬ (dsum step3 (split u).2 + step3 a = 0) := by rw [← hs]; exact h0
    simp only [if_neg h0]
    by_cases hall : ∀ e ∈ (split u).1, cls (comp e) = i.succ
    · simp only [if_pos hall, fStep, if_neg hs0]
      rw [hs, comp_snoc]
    · simp only [if_neg hall]
      rfl

lemma fState_eq_foldl (i : Fin 12) (u : W3) : fState i u = u.foldl (fStep i) (some (0, [])) := by
  induction u using List.reverseRecOn with
  | nil => simp [fState, split, dsum, comp]
  | append_singleton u a ih => rw [fState_snoc, ih, List.foldl_append]; rfl

lemma mem_kstar_Fcls_iff (i : Fin 12) (u : W3) :
    u ∈ (Fcls i)∗ ↔ fAcc (fState i u) = true := by
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨es, rfl, hes⟩
    have hsp := split_flatten (fun e he => (hes e he).1) nil_mem_NoRet
    rw [List.append_nil] at hsp
    unfold fState
    rw [hsp]
    dsimp only
    have hall : ∀ e ∈ es, cls (comp e) = i.succ := fun e he => (hes e he).2
    rw [if_pos hall]
    simp [fAcc, dsum]
  · intro h
    unfold fState at h
    by_cases hall : ∀ e ∈ (split u).1, cls (comp e) = i.succ
    · rw [if_pos hall] at h
      simp only [fAcc, decide_eq_true_eq] at h
      have ht := NoRet_eq_nil (split_spec u).2.2 h
      refine ⟨(split u).1, ?_, fun e he => ⟨(split_spec u).2.1 e he, hall e he⟩⟩
      have := (split_spec u).1
      rw [ht, List.append_nil] at this
      exact this.symm
    · rw [if_neg hall] at h
      exact absurd h (by simp [fAcc])

/-- **The twelve strictly locally testable descriptions.** -/
theorem Fcls_kstar_eq (i : Fin 12) :
    (Fcls i)∗ = sltLang true (fData i).1 (fData i).2.1 (fData i).2.2 := by
  ext u
  obtain ⟨hP, hS, hG⟩ := fData_ok i
  rw [mem_kstar_Fcls_iff, mem_sltLang_iff hP hS hG, sltState_eq_foldl hG, fState_eq_foldl,
    f_agree i u]

theorem Fcls_kstar_height (i : Fin 12) : HasHeightAtMost (Fcls i)∗ 0 := by
  rw [Fcls_kstar_eq]; exact sltLang_height _ _ _ _

/-! ### Heights of the counting languages -/

/-- **Counting the blocks of a class**, by the Transfer Lemma. -/
theorem bmodF_height (i : Fin 12) {m r : ℕ} (hr : r < m) :
    HasHeightAtMost (bmod coreX (Fcls i) m r) 1 := by
  have h := transfer_height_one (L₀ := Fcls i) (L₁ := Fco i)
    (by rw [Fcls_add_Fco]; exact coreX_prefixCode) (Fcls_disjoint i) (Fcls_height i)
    (Fco_height i) (Fcls_kstar_height i) hr
  rwa [Fcls_add_Fco] at h

lemma acCount0_lang (m r : ℕ) :
    {v : W3 | acCount0 v % m = r} = bmod coreX (Fcls 0) m r * NoRet := by
  ext v
  constructor
  · intro hv
    change acCount0 v % m = r at hv
    refine Language.mem_mul.mpr ⟨(split v).1.flatten, ⟨(split v).1, (split_spec v).2.1, rfl, ?_⟩,
      (split v).2, (split_spec v).2.2, (split_spec v).1⟩
    rw [acCount0_eq] at hv
    exact hv
  · intro hv
    obtain ⟨x, ⟨es, hes, rfl, hk⟩, t, ht, rfl⟩ := Language.mem_mul.mp hv
    show acCount0 _ % m = r
    rw [acCount0_eq, Ncnt, split_flatten hes ht]
    exact hk

/-- **The factor `02` read from state `1`, counted modulo `m`.** -/
theorem acCount_height {m r : ℕ} (hr : r < m) :
    HasHeightAtMost {u : W3 | acCount u % m = r} 1 := by
  have : {u : W3 | acCount u % m = r} = leftQuot 2 {v : W3 | acCount0 v % m = r} := by
    ext u
    show acCount u % m = r ↔ acCount0 (2 :: u) % m = r
    rw [acCount_eq_cons]
  rw [this, acCount0_lang]
  exact ((bmodF_height 0 hr).concat (NoRet_height.mono (by omega))).leftQuot 2

end GeneralizedStarHeight
