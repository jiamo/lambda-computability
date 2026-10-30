import Start.StarHeightZpWalk

/-!
# Walks on `ZMod p`: first returns ending with a given pair, and their stars

Alphabet `β`, displacements `σ : β → ZMod p`, a relation `P` on letters.

* `PairEnd P`: the words ending with two letters `a c` with `P a c` (star-free, `pairEnd_starFree`).
* `pcls σ P = zpX σ ⊓ PairEnd P`: the first returns to `0` whose last two letters form a `P`-pair.
* `pcls_kstar_starFree`: for `p` prime, `(pcls σ P)∗` is star-free provided no letter `y` is
  `P`-related "in a cycle", i.e. `P a c → a = y ∧ c ≠ y` for all `a c`, or
  `P a c → a ≠ y ∧ c = y` for all `a c`.

The proof of the last point: `(pcls σ P)∗` is recognized by the automaton `pkStep` (states: the
boundary, `(state, last letter)`, dead).  It satisfies `w^(p+2) ≡ w^(p+1)`.  If `σ(w) = 0` then
already `w³ ≡ w²`.  If `σ(w) ≠ 0`, some cyclic pair `(ℓ, c)` of `w` is not a `P`-pair; reading the
rotation of `w` starting with `c` repeatedly, the state just before some copy of `c` is `-σ c`
(as `σ(w)` generates `ZMod p`), and that copy lands on `0` through the non-pair `(ℓ, c)`, which
kills the run.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

section Pairs

variable {β : Type} {p : ℕ} (σ : β → ZMod p) (P : β → β → Prop)

open Classical

/-- The words ending with a `P`-pair. -/
def PairEnd : Language β := {w | ∃ v a c, w = v ++ [a, c] ∧ P a c}

lemma pairEnd_eq : PairEnd P =
    (⊤ : Language β) * ⨆ ac : {ac : β × β // P ac.1 ac.2}, ({[ac.1.1, ac.1.2]} : Language β) := by
  ext w
  constructor
  · rintro ⟨v, a, c, rfl, h⟩
    exact Language.mem_mul.mpr ⟨v, trivial, [a, c], Language.mem_iSup.mpr ⟨⟨(a, c), h⟩, rfl⟩, rfl⟩
  · intro hw
    obtain ⟨v, -, y, hy, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨⟨⟨a, c⟩, h⟩, hy⟩ := Language.mem_iSup.mp hy
    have hy' : y = [a, c] := hy
    exact ⟨v, a, c, by rw [hy'], h⟩

lemma pairEnd_starFree [Finite β] : HasHeightAtMost (PairEnd P) 0 := by
  rw [pairEnd_eq]
  exact Aperiodic.sf_top.concat (HasHeightAtMost.iSup _ fun _ => HasHeightAtMost.singleton _ 0)

/-- First returns ending with a `P`-pair. -/
def pcls : Language β := zpX σ ⊓ PairEnd P

lemma pcls_le : pcls σ P ≤ zpX σ := fun _ h => h.1

lemma pcls_starFree [Fact p.Prime] [Finite β] : HasHeightAtMost (pcls σ P) 0 :=
  (zpX_starFree σ).inter (pairEnd_starFree P)

/-! ### The automaton of `(pcls σ P)∗` -/

/-- `some none`: on a block boundary; `some (some (s, ℓ))`: in state `s` after the letter `ℓ`;
`none`: dead. -/
noncomputable def pkStep : Option (Option (ZMod p × β)) → β → Option (Option (ZMod p × β))
  | some none, c => if σ c = 0 then none else some (some (σ c, c))
  | some (some (s, ℓ)), c =>
      if s + σ c = 0 then (if P ℓ c then some none else none) else some (some (s + σ c, c))
  | none, _ => none

lemma pk_dead : ∀ u : List β, u.foldl (pkStep σ P) none = none
  | [] => rfl
  | _ :: u => by rw [List.foldl_cons]; exact pk_dead u

lemma pk_nr : ∀ (t : List β) (a : β), t ++ [a] ∈ zpNR σ →
    (t ++ [a]).foldl (pkStep σ P) (some none) = some (some (zpSum σ (t ++ [a]), a)) := by
  intro t
  induction t using List.reverseRecOn with
  | nil =>
      intro a ha
      have h := ha [a] List.prefix_rfl (by simp)
      rw [zpSum_single] at h
      simp [pkStep, h, zpSum_single]
  | append_singleton t b ih =>
      intro a ha
      have hb : t ++ [b] ∈ zpNR σ := fun q hq hne =>
        ha q (hq.trans (List.prefix_append _ _)) hne
      have h := ha _ List.prefix_rfl (by simp)
      rw [List.foldl_append, ih b hb]
      simp only [List.foldl_cons, List.foldl_nil, pkStep]
      rw [zpSum_append (u := t ++ [b]), zpSum_single] at h ⊢
      rw [ite_eq_right h]

lemma pk_block {e : List β} (he : e ∈ zpX σ) :
    e.foldl (pkStep σ P) (some none) = if e ∈ PairEnd P then some none else none := by
  obtain ⟨hne, h0, hpre⟩ := he
  rcases List.eq_nil_or_concat e with rfl | ⟨e', c, rfl⟩
  · exact absurd rfl hne
  simp only [List.concat_eq_append] at h0 hpre ⊢
  rcases List.eq_nil_or_concat e' with rfl | ⟨t, a, rfl⟩
  · simp only [List.nil_append] at h0 ⊢
    rw [zpSum_single] at h0
    have hn : [c] ∉ PairEnd P := by
      rintro ⟨v, a, c', hv, -⟩
      have := congrArg List.length hv
      simp at this
    simp [pkStep, h0, hn]
  · simp only [List.concat_eq_append] at h0 hpre ⊢
    have hnr : t ++ [a] ∈ zpNR σ := fun q hq hqne => hpre q (hq.trans (List.prefix_append _ _))
      hqne (fun h => by have := hq.length_le; rw [h] at this; simp at this)
    rw [List.foldl_append, pk_nr σ P t a hnr]
    rw [zpSum_append] at h0
    simp only [List.foldl_cons, List.foldl_nil, pkStep]
    rw [zpSum_single] at h0
    rw [ite_eq_left h0]
    have hiff : t ++ [a] ++ [c] ∈ PairEnd P ↔ P a c := by
      constructor
      · rintro ⟨v, a', c', hv, hP⟩
        rw [List.append_assoc, show [a] ++ [c] = [a, c] from rfl] at hv
        have h2 := List.append_inj' hv rfl
        simp only [List.cons.injEq, and_true] at h2
        rw [h2.2.1, h2.2.2]
        exact hP
      · intro h
        exact ⟨t, a, c, by simp, h⟩
    by_cases hP : P a c
    · rw [ite_eq_left hP, ite_eq_left (hiff.mpr hP)]
    · rw [ite_eq_right hP, ite_eq_right (fun h => hP (hiff.mp h))]

lemma pk_flatten : ∀ {es : List (List β)}, AllIn (zpX σ) es →
    es.flatten.foldl (pkStep σ P) (some none) =
      if AllIn (PairEnd P) es then some none else none
  | [], _ => by rw [ite_eq_left (show AllIn (PairEnd P) [] from fun e he => by simp at he)]; rfl
  | e :: es, hes => by
      rw [List.flatten_cons, List.foldl_append, pk_block σ P (hes e (by simp))]
      have ih := pk_flatten (es := es) (fun f hf => hes f (by simp [hf]))
      have hall : AllIn (PairEnd P) (e :: es) ↔ e ∈ PairEnd P ∧ AllIn (PairEnd P) es := by
        simp [AllIn]
      by_cases he : e ∈ PairEnd P
      · rw [ite_eq_left he, ih]
        by_cases h : AllIn (PairEnd P) es
        · rw [ite_eq_left h, ite_eq_left (hall.mpr ⟨he, h⟩)]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h (hall.mp h').2)]
      · rw [ite_eq_right he, pk_dead, ite_eq_right (fun h' => he (hall.mp h').1)]

lemma pk_tail : ∀ (t : List β) (q : Option (Option (ZMod p × β))), t ∈ zpNR σ → t ≠ [] →
    (q = none ∨ q = some none) → t.foldl (pkStep σ P) q ≠ some none := by
  intro t q ht htne hq
  rcases List.eq_nil_or_concat t with rfl | ⟨t', a, rfl⟩
  · exact absurd rfl htne
  simp only [List.concat_eq_append] at ht ⊢
  rcases hq with rfl | rfl
  · rw [pk_dead]; simp
  · rw [pk_nr σ P t' a ht]; simp

/-- **The automaton recognizes `(pcls σ P)∗`.** -/
lemma pcls_kstar_eq :
    (pcls σ P)∗ = {u : List β | u.foldl (pkStep σ P) (some none) = some none} := by
  ext u
  constructor
  · intro hu
    obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hu
    show es.flatten.foldl (pkStep σ P) (some none) = some none
    rw [pk_flatten σ P (fun e he => (hes e he).1), ite_eq_left (show AllIn (PairEnd P) es from fun e he => (hes e he).2)]
  · intro hu
    change u.foldl (pkStep σ P) (some none) = some none at hu
    obtain ⟨h1, h2, h3⟩ := zpSplit_spec σ u
    set es := (zpSplit σ u).1
    set t := (zpSplit σ u).2
    rw [← h1, List.foldl_append, pk_flatten σ P h2] at hu
    by_cases ht : t = []
    · have hall : AllIn (PairEnd P) es := by
        by_contra h
        rw [ite_eq_right h, ht] at hu
        simp at hu
      refine Language.mem_kstar.mpr ⟨es, ?_, fun e he => ⟨h2 e he, hall e he⟩⟩
      rw [← h1, ht, List.append_nil]
    · exfalso
      refine pk_tail σ P t _ h3 ht ?_ hu
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

/-! ### Stable powers -/

/-- The state value: `0` on the boundary. -/
def pkVal : Option (Option (ZMod p × β)) → ZMod p
  | some (some (s, _)) => s
  | _ => 0

lemma pkStep_cases (q : Option (Option (ZMod p × β))) (c : β) :
    pkStep σ P q c = none ∨ pkStep σ P q c = some none ∨
      ∃ s, s ≠ 0 ∧ pkStep σ P q c = some (some (s, c)) := by
  rcases q with _ | _ | ⟨s, ℓ⟩
  · exact Or.inl rfl
  · simp only [pkStep]
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨_, h, rfl⟩)
  · simp only [pkStep]
    split_ifs with h h'
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨_, h, rfl⟩)

lemma pk_val : ∀ (u : List β) (q : Option (Option (ZMod p × β))),
    u.foldl (pkStep σ P) q ≠ none → pkVal (u.foldl (pkStep σ P) q) = pkVal q + zpSum σ u
  | [], q, _ => by simp
  | c :: u, q, h => by
      rw [List.foldl_cons] at h ⊢
      rw [pk_val u _ h, zpSum_cons, ← add_assoc]
      congr 1
      have hq : pkStep σ P q c ≠ none := by
        intro h'; rw [h', pk_dead] at h; exact h rfl
      rcases q with _ | _ | ⟨s, ℓ⟩
      · exact absurd rfl hq
      · simp only [pkStep] at hq ⊢
        split_ifs at hq ⊢ with h0
        · exact absurd rfl hq
        · simp [pkVal]
      · simp only [pkStep] at hq ⊢
        split_ifs at hq ⊢ with h0 h1
        · simp [pkVal, h0]
        · exact absurd rfl hq
        · simp [pkVal]

/-- The last letter read, if recorded, is `ℓ`. -/
def pkCompat (ℓ : β) (q : Option (Option (ZMod p × β))) : Prop :=
  ∀ s ℓ', q = some (some (s, ℓ')) → ℓ' = ℓ

lemma pk_compat_snoc (u : List β) (a : β) (q : Option (Option (ZMod p × β))) :
    pkCompat a ((u ++ [a]).foldl (pkStep σ P) q) := by
  intro s ℓ' h
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
  rcases pkStep_cases σ P (u.foldl (pkStep σ P) q) a with h' | h' | ⟨s', -, h'⟩ <;>
    rw [h'] at h <;> simp_all

lemma pk_kill {ℓ c : β} {q : Option (Option (ZMod p × β))} (hq : pkCompat ℓ q) (hP : ¬ P ℓ c)
    (h0 : pkVal q + σ c = 0) : pkStep σ P q c = none := by
  rcases q with _ | _ | ⟨s, ℓ'⟩
  · rfl
  · simp only [pkVal, zero_add] at h0
    simp [pkStep, h0]
  · have hℓ := hq s ℓ' rfl
    subst hℓ
    simp only [pkVal] at h0
    simp [pkStep, h0, hP]

lemma pk_wpow_add (w : List β) (a b : ℕ) : wpow w (a + b) = wpow w a ++ wpow w b := by
  unfold wpow; rw [List.replicate_add, List.flatten_append]

/-- **The kill lemma.** Reading `p` copies of a word starting with `c` and ending with `ℓ`, where
`(ℓ, c)` is not a `P`-pair and the word moves the state, from a state compatible with `ℓ`. -/
lemma pk_wpow_kill [Fact p.Prime] {w v rest : List β} {ℓ c : β} (hv : w = v ++ [ℓ])
    (hc : w = c :: rest) (hP : ¬ P ℓ c) (hr : zpSum σ w ≠ 0)
    {q : Option (Option (ZMod p × β))} (hq : pkCompat ℓ q) :
    (wpow w p).foldl (pkStep σ P) q = none := by
  have hcomp : ∀ k, pkCompat ℓ ((wpow w k).foldl (pkStep σ P) q) := by
    intro k
    cases k with
    | zero => exact hq
    | succ k =>
        rw [wpow_succ', List.foldl_append, hv]
        exact pk_compat_snoc σ P v ℓ _
  rcases q with _ | q
  · exact pk_dead σ P _
  obtain ⟨k, hk1, hkp, hk⟩ := exists_land (pkVal (some q) + σ c - zpSum σ w) (zpSum σ w) hr
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hsplit : wpow w p = wpow w j ++ (c :: rest) ++ wpow w (p - 1 - j) := by
    rw [← hc, ← wpow_succ', ← pk_wpow_add]
    congr 1
    omega
  rw [hsplit, List.foldl_append, List.foldl_append, List.foldl_cons]
  by_cases hq2 : (wpow w j).foldl (pkStep σ P) (some q) = none
  · rw [hq2, show pkStep σ P none c = none from rfl, pk_dead, pk_dead]
  · have hval := pk_val σ P (wpow w j) (some q) hq2
    rw [pk_kill σ P (hcomp j) hP, pk_dead, pk_dead]
    rw [hval, zpSum_wpow]
    push_cast at hk
    linear_combination hk

/-- A word of displacement `0`: `w³ ≡ w²`. -/
lemma pk_rot0 {w : List β} (hw : w ≠ []) (hr : zpSum σ w = 0)
    (q : Option (Option (ZMod p × β))) :
    (w ++ w ++ w).foldl (pkStep σ P) q = (w ++ w).foldl (pkStep σ P) q := by
  simp only [List.foldl_append]
  set q1 := w.foldl (pkStep σ P) q
  suffices h : w.foldl (pkStep σ P) q1 = q1 ∨ w.foldl (pkStep σ P) q1 = none by
    rcases h with h | h
    · rw [h, h]
    · rw [h, pk_dead]
  obtain ⟨w', a, rfl⟩ : ∃ w' a, w = w' ++ [a] := by
    rcases List.eq_nil_or_concat w with h | ⟨w', a, h⟩
    · exact absurd h hw
    · exact ⟨w', a, by simpa using h⟩
  have hres : ∀ q', (w' ++ [a]).foldl (pkStep σ P) q' = none ∨
      (w' ++ [a]).foldl (pkStep σ P) q' = some none ∨
      ∃ s, s ≠ 0 ∧ (w' ++ [a]).foldl (pkStep σ P) q' = some (some (s, a)) := by
    intro q'
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact pkStep_cases σ P _ a
  by_cases h2 : (w' ++ [a]).foldl (pkStep σ P) q1 = none
  · exact Or.inr h2
  left
  have hval := pk_val σ P _ q1 h2
  rw [hr, add_zero] at hval
  rcases hres q with h1 | h1 | ⟨s, hs, h1⟩
  · exfalso; apply h2; show _ = none; rw [show q1 = none from h1, pk_dead]
  · rw [show q1 = some none from h1] at hval h2 ⊢
    rcases hres (some none) with h | h | ⟨s', hs', h⟩
    · exact absurd h h2
    · exact h
    · rw [h] at hval; exact absurd hval hs'
  · rw [show q1 = some (some (s, a)) from h1] at hval h2 ⊢
    rcases hres (some (some (s, a))) with h | h | ⟨s', hs', h⟩
    · exact absurd h h2
    · rw [h] at hval; exact absurd hval.symm hs
    · rw [h] at hval ⊢; simp only [pkVal] at hval; rw [hval]

lemma pk_wpow_iter (w : List β) (q : Option (Option (ZMod p × β))) :
    ∀ n, (wpow w n).foldl (pkStep σ P) q = (fun q' => w.foldl (pkStep σ P) q')^[n] q
  | 0 => rfl
  | n + 1 => by
      rw [wpow_succ', List.foldl_append, pk_wpow_iter w q n, Function.iterate_succ_apply']

lemma wpow_rotate (a : β) (u : List β) :
    ∀ n, wpow (a :: u) (n + 1) = a :: (wpow (u ++ [a]) n ++ u)
  | 0 => by simp [wpow]
  | n + 1 => by
      rw [wpow_succ, wpow_rotate a u n, wpow_succ]
      simp

/-- **Stable powers** of the `(pcls σ P)∗` automaton. -/
lemma pk_pow_stable [Fact p.Prime] {y : β}
    (hP : (∀ a c, P a c → a = y ∧ c ≠ y) ∨ (∀ a c, P a c → a ≠ y ∧ c = y))
    (w : List β) (q : Option (Option (ZMod p × β))) :
    (wpow w (p + 2)).foldl (pkStep σ P) q = (wpow w (p + 1)).foldl (pkStep σ P) q := by
  rcases w with _ | ⟨a0, w₁⟩
  · have : ∀ n, wpow ([] : List β) n = [] := fun n => by simp [wpow]
    rw [this, this]
  set w := a0 :: w₁ with hwdef
  have hw : w ≠ [] := List.cons_ne_nil a0 w₁
  by_cases hr : zpSum σ w = 0
  · set F := fun q' => w.foldl (pkStep σ P) q'
    have h3 : ∀ q', F (F (F q')) = F (F q') := by
      intro q'
      have := pk_rot0 σ P hw hr q'
      simpa [List.foldl_append, F] using this
    have h2 : ∀ n q', F^[n + 2] q' = F^[2] q' := by
      intro n
      induction n with
      | zero => intro q'; rfl
      | succ n ih =>
          intro q'
          rw [show n + 1 + 2 = (n + 2) + 1 by omega, Function.iterate_succ_apply, ih]
          exact h3 q'
    rw [pk_wpow_iter, pk_wpow_iter]
    show F^[p + 2] q = F^[p + 1] q
    rw [h2, show p + 1 = (p - 1) + 2 by have := (Fact.out : p.Prime).one_lt; omega, h2 (p - 1)]
  · have hkill : ∀ q', (wpow w (p + 1)).foldl (pkStep σ P) q' = none := by
      intro q'
      obtain ⟨v, ℓ, hv⟩ : ∃ v ℓ, w = v ++ [ℓ] := by
        rcases List.eq_nil_or_concat w with h | ⟨v, ℓ, h⟩
        · exact absurd h hw
        · exact ⟨v, ℓ, by simpa using h⟩
      obtain ⟨c, rest, hc⟩ : ∃ c rest, w₁ ++ [a0] = c :: rest :=
        List.exists_cons_of_ne_nil (by simp)
      by_cases hA : P ℓ a0
      · by_cases hB : P a0 c
        · exfalso
          rcases hP with h | h
          · exact (h _ _ hA).2 (h _ _ hB).1
          · exact (h _ _ hB).1 (h _ _ hA).2
        · rw [hwdef, wpow_rotate, List.foldl_cons, List.foldl_append]
          have hr' : zpSum σ (w₁ ++ [a0]) ≠ 0 := by
            rwa [zpSum_append, add_comm, ← zpSum_append]
          have hcomp : pkCompat a0 (pkStep σ P q' a0) := by
            have := pk_compat_snoc σ P [] a0 q'
            simpa using this
          rw [pk_wpow_kill σ P (v := w₁) rfl hc hB hr' hcomp, pk_dead]
      · rw [wpow_succ, List.foldl_append]
        have hcomp : pkCompat ℓ (w.foldl (pkStep σ P) q') := by
          rw [hv]; exact pk_compat_snoc σ P v ℓ q'
        exact pk_wpow_kill σ P hv hwdef hA hr hcomp
    rw [show p + 2 = (p + 1) + 1 by omega, wpow_succ', List.foldl_append, hkill, pk_dead]

/-- **`(pcls σ P)∗` is star-free** for `p` prime and `P` without cyclic pairs. -/
theorem pcls_kstar_starFree [Fact p.Prime] [Finite β] {y : β}
    (hP : (∀ a c, P a c → a = y ∧ c ≠ y) ∨ (∀ a c, P a c → a ≠ y ∧ c = y)) :
    HasHeightAtMost (pcls σ P)∗ 0 := by
  have : Finite (ZMod p) := by
    have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    infer_instance
  rw [pcls_kstar_eq]
  exact starFree_of_pow_stable (pkStep σ P) (p + 1) (fun w q => pk_pow_stable σ P hP w q) _
    (fun q => q = some none)

end Pairs

end GeneralizedStarHeight
