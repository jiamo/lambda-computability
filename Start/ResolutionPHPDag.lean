/-
**Haken's theorem for DAG-like resolution, by Beame–Pitassi.**

Task `M22-HAKEN-PHP-DAG`.  The monotone width bound of `Start/ResolutionPHPWidth.lean` is relativized
to a partial matching `m` (pigeons outside `P` sit in holes outside `H`), and a greedy restriction
kills all wide clauses.

* `muR n m P H C`: the complexity of `C` measured on the critical assignments of `(P, H)` extended
  by `m`.  It is subadditive (`muR_resolvent`), at most one on the clauses of `PHP(n+1, n)`
  (`muR_php_le_one`), `|P|` on the empty clause (`muR_nil`), and zero on every clause whose
  monotone translation contains a pair matched by `m` (`muR_killed`).
* `muR_mul_le_monoVars`: `μ(C) · (|P| - μ(C)) ≤ |monoVarsOn n P H C|`.
* `exists_heavy_pair`: averaging; some pair lies in many wide clauses.
* `stage`: after `s` greedy rounds the wide clauses that are not killed number at most
  `|R| · (D - w)^s / D^s`, `D = n(n+1)`.
* **`php_dag_size`**: every DAG-like refutation of `PHP(n+1, n)` has at least `2^(n/32)` clauses.
-/

import Start.ResolutionPHPWidth

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Sat.PHP

open Classical

/-! ### Critical assignments extended by a partial matching -/

/-- `g` on `P`, `m` outside. -/
def ext (P : Finset ℕ) (m g : ℕ → Option ℕ) (a : ℕ) : Option ℕ := if a ∈ P then g a else m a

/-- Every `i`-critical assignment of `(P, H)` with `i ∉ S`, extended by `m`, satisfies `C`. -/
def WitnessR (n : ℕ) (m : ℕ → Option ℕ) (P H S : Finset ℕ) (C : Clause) : Prop :=
  ∀ i g, IsCrit P H i g → i ∉ S → EvalC (critAsg n (ext P m g)) C

theorem exists_witnessR (n : ℕ) (m : ℕ → Option ℕ) (P H : Finset ℕ) (C : Clause) :
    ∃ k, ∃ S ⊆ P, S.card = k ∧ WitnessR n m P H S C :=
  ⟨P.card, P, subset_rfl, rfl, fun _ _ hg hi => absurd hg.mem hi⟩

/-- The relative complexity `μ(C)`. -/
noncomputable def muR (n : ℕ) (m : ℕ → Option ℕ) (P H : Finset ℕ) (C : Clause) : ℕ :=
  Nat.find (exists_witnessR n m P H C)

variable {n : ℕ} {m : ℕ → Option ℕ} {P H : Finset ℕ}

theorem muR_spec (C : Clause) : ∃ S ⊆ P, S.card = muR n m P H C ∧ WitnessR n m P H S C :=
  Nat.find_spec (exists_witnessR n m P H C)

theorem muR_le {C : Clause} {S : Finset ℕ} (hS : S ⊆ P) (hw : WitnessR n m P H S C) :
    muR n m P H C ≤ S.card :=
  Nat.find_min' (exists_witnessR n m P H C) ⟨S, hS, rfl, hw⟩

theorem muR_resolvent (k : ℕ) (C₁ C₂ : Clause) :
    muR n m P H (resolvent k C₁ C₂) ≤ muR n m P H C₁ + muR n m P H C₂ := by
  obtain ⟨S₁, hS₁, hc₁, hw₁⟩ := muR_spec (n := n) (m := m) (P := P) (H := H) C₁
  obtain ⟨S₂, hS₂, hc₂, hw₂⟩ := muR_spec (n := n) (m := m) (P := P) (H := H) C₂
  calc muR n m P H (resolvent k C₁ C₂) ≤ (S₁ ∪ S₂).card := by
        refine muR_le (Finset.union_subset hS₁ hS₂) fun i g hg hi => ?_
        rw [Finset.mem_union, not_or] at hi
        exact evalC_resolvent (hw₁ i g hg hi.1) (hw₂ i g hg hi.2)
    _ ≤ S₁.card + S₂.card := Finset.card_union_le _ _
    _ = _ := by rw [hc₁, hc₂]

theorem muR_nil (hcard : P.card = H.card + 1) : muR n m P H [] = P.card := by
  refine le_antisymm (muR_le subset_rfl fun _ _ hg hi => absurd hg.mem hi) ?_
  obtain ⟨S, hS, hc, hw⟩ := muR_spec (n := n) (m := m) (P := P) (H := H) []
  rw [← hc]
  refine Finset.card_le_card fun i hi => ?_
  by_contra hiS
  obtain ⟨g, hg⟩ := crit_exists hcard hi
  obtain ⟨l, hl, -⟩ := hw i g hg hiS
  simp at hl

theorem exists_mid_muR {F : Cnf} (hF : ∀ C ∈ F, muR n m P H C ≤ 1) {t : ℕ} (ht : 1 ≤ t) :
    ∀ {L : List Clause}, DagDeriv F L → (∃ C ∈ L, t < muR n m P H C) →
      ∃ C ∈ L, t < muR n m P H C ∧ muR n m P H C ≤ 2 * t
  | _, .nil, h => by simp at h
  | _, .snoc (L := L) (C := C) hL hC, h => by
      by_cases hex : ∃ D ∈ L, t < muR n m P H D
      · obtain ⟨D, hD, h1, h2⟩ := exists_mid_muR hF ht hL hex
        exact ⟨D, List.mem_append_left _ hD, h1, h2⟩
      · push Not at hex
        obtain ⟨D, hD, hDt⟩ := h
        rcases List.mem_append.1 hD with hD | hD
        · exact absurd (hex D hD) (by omega)
        · simp only [List.mem_singleton] at hD
          subst hD
          refine ⟨D, by simp, hDt, ?_⟩
          rcases hC with hC | ⟨k, C₁, C₂, h₁, h₂, -, -, rfl⟩
          · have := hF _ hC; omega
          · have := muR_resolvent (n := n) (m := m) (P := P) (H := H) k C₁ C₂
            have := hex C₁ h₁
            have := hex C₂ h₂
            omega

/-! ### Relative monotone width -/

theorem mem_monoVars_of_flip' {i j l : ℕ} {g : ℕ → Option ℕ} (hi : i ∈ P) (hlH : l ∈ H)
    (hgi : g i = none) (hj : j ∈ P) (hji : j ≠ i) (hl : g j = some l) {C : Clause}
    (hf : ¬ EvalC (critAsg n g) C) (ht : EvalC (critAsg n (moveHole g i j l)) C) :
    (i, l) ∈ monoVarsOn n P H C := by
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi, hlH⟩, ?_⟩
  obtain ⟨⟨b, k⟩, hlit, hv⟩ := ht
  have hfl : (if b then critAsg n g k else !critAsg n g k) = false := by
    by_contra h
    exact hf ⟨(b, k), hlit, by simpa using h⟩
  have hk : k = var n (k / n) (k % n) := by unfold var; exact (Nat.div_add_mod k n).symm
  have hupd : ∀ a, moveHole g i j l a = if a = j then none else if a = i then some l else g a := by
    intro a
    simp only [moveHole, Function.update_apply]
  by_cases hkj : k / n = j
  · have h1 : critAsg n (moveHole g i j l) k = false := by
      simp [critAsg, hupd, hkj]
    rw [h1] at hv
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hv hfl
      have h2 : critAsg n g k = true := by simpa using hfl
      simp only [critAsg, hkj, hl, decide_eq_true_eq, Option.some.injEq] at h2
      right
      refine ⟨j, hj, hji, ?_⟩
      rw [hk, hkj, ← h2] at hlit
      exact hlit
    · simp at hv
  · by_cases hki : k / n = i
    · have h1 : critAsg n g k = false := by simp [critAsg, hki, hgi]
      rw [h1] at hfl
      cases b
      · simp at hfl
      · simp only [ite_true] at hv
        have hv' : l = k % n := by
          simp [critAsg, hupd, hki] at hv
          exact hv.2
        left
        rw [hk, hki, ← hv'] at hlit
        exact hlit
    · have h1 : critAsg n (moveHole g i j l) k = critAsg n g k := by
        simp [critAsg, hupd, hkj, hki]
      rw [h1] at hv
      rw [hv] at hfl
      exact absurd hfl (by simp)

theorem ext_moveHole {g : ℕ → Option ℕ} {i j l : ℕ} (hi : i ∈ P) (hj : j ∈ P) :
    ext P m (moveHole g i j l) = moveHole (ext P m g) i j l := by
  funext a
  simp only [ext, moveHole, Function.update_apply]
  by_cases haj : a = j
  · simp [haj, hj]
  · by_cases hai : a = i
    · simp [hai, hi]
    · simp [haj, hai]

theorem muR_mul_le_monoVars (C : Clause) :
    muR n m P H C * (P.card - muR n m P H C) ≤ (monoVarsOn n P H C).card := by
  obtain ⟨S, hS, hc, hw⟩ := muR_spec (n := n) (m := m) (P := P) (H := H) C
  have hfals : ∀ i ∈ S, ∃ g, IsCrit P H i g ∧ ¬ EvalC (critAsg n (ext P m g)) C := by
    intro i hi
    by_contra hno
    push Not at hno
    have hw' : WitnessR n m P H (S.erase i) C := by
      intro i' g hg hi'
      by_cases e : i' = i
      · subst e; exact hno g hg
      · exact hw i' g hg (fun h => hi' (Finset.mem_erase.2 ⟨e, h⟩))
    have := muR_le ((Finset.erase_subset i S).trans hS) hw'
    rw [Finset.card_erase_of_mem hi] at this
    have : 0 < S.card := Finset.card_pos.2 ⟨i, hi⟩
    omega
  choose! G hG hGf using hfals
  have hhole : ∀ i ∈ S, ∀ j ∈ P \ S, G i j = some ((G i j).getD 0) := by
    intro i hi j hj
    obtain ⟨hjP, hjS⟩ := Finset.mem_sdiff.1 hj
    obtain ⟨b, -, hb⟩ := (hG i hi).maps j hjP (fun e => hjS (e ▸ hi))
    rw [hb]; rfl
  have hmaps : Set.MapsTo (fun ij : ℕ × ℕ => (ij.1, (G ij.1 ij.2).getD 0)) ↑(S ×ˢ (P \ S))
      ↑(monoVarsOn n P H C) := by
    rintro ⟨i, j⟩ hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
    obtain ⟨hjP, hjS⟩ := Finset.mem_sdiff.1 hj
    have hji : j ≠ i := fun e => hjS (e ▸ hi)
    have hl := hhole i hi j hj
    have hiP := hS hi
    have htrue := hw j _ (isCrit_moveHole (hG i hi) hjP hji hl) hjS
    rw [ext_moveHole hiP hjP] at htrue
    refine mem_monoVars_of_flip' hiP ((hG i hi).range _ _ hl) ?_ hjP hji ?_ (hGf i hi) htrue
    · show (if i ∈ P then G i i else m i) = none
      rw [ite_eq_left hiP]; exact (hG i hi).self
    · show (if j ∈ P then G i j else m j) = _
      rw [ite_eq_left hjP]; exact hl
  have hinj : Set.InjOn (fun ij : ℕ × ℕ => (ij.1, (G ij.1 ij.2).getD 0)) ↑(S ×ˢ (P \ S)) := by
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, he⟩ := he
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
    obtain ⟨-, hj'⟩ := Finset.mem_product.1 hij'
    have h1 := hhole i hi j hj
    have h2 := hhole i hi j' hj'
    rw [he] at h1
    rw [(hG i hi).inj _ _ _ h1 h2]
  have := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_sdiff_of_subset hS, hc] at this
  exact this

theorem monoVarsOn_mono {P' H' : Finset ℕ} (hP : P' ⊆ P) (hH : H' ⊆ H) (C : Clause) :
    monoVarsOn n P' H' C ⊆ monoVarsOn n P H C := by
  intro ab hab
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.1 hab
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hmem
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hP h1, hH h2⟩, ?_⟩
  rcases hc with hc | ⟨a', ha', hne, hc⟩
  · exact Or.inl hc
  · exact Or.inr ⟨a', hP ha', hne, hc⟩

/-! ### Partial matchings -/

/-- `m` matches the pigeons of `P₀ ∖ P` injectively to holes of `H₀ ∖ H`. -/
structure Base (P₀ H₀ P H : Finset ℕ) (m : ℕ → Option ℕ) : Prop where
  subP : P ⊆ P₀
  subH : H ⊆ H₀
  none_in : ∀ a ∈ P, m a = none
  none_out : ∀ a, a ∉ P₀ → m a = none
  maps : ∀ a ∈ P₀, a ∉ P → ∃ b, m a = some b
  range : ∀ a b, m a = some b → b ∈ H₀ ∧ b ∉ H
  inj : ∀ a a' b, m a = some b → m a' = some b → a = a'

theorem base_init (P₀ H₀ : Finset ℕ) : Base P₀ H₀ P₀ H₀ (fun _ => none) :=
  ⟨subset_rfl, subset_rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ h h' => absurd h h',
    fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩

theorem base_step {P₀ H₀ : Finset ℕ} (hB : Base P₀ H₀ P H m) {i j : ℕ} (hi : i ∈ P) (hj : j ∈ H) :
    Base P₀ H₀ (P.erase i) (H.erase j) (Function.update m i (some j)) := by
  have upd : ∀ a, Function.update m i (some j) a = if a = i then some j else m a := by
    intro a; simp only [Function.update_apply]
  refine ⟨(Finset.erase_subset _ _).trans hB.subP, (Finset.erase_subset _ _).trans hB.subH,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨hai, haP⟩ := Finset.mem_erase.1 ha
    simp [hai, hB.none_in a haP]
  · intro a ha
    have hai : a ≠ i := fun e => ha (hB.subP (e ▸ hi))
    simp [hai, hB.none_out a ha]
  · intro a ha haP
    by_cases hai : a = i
    · exact ⟨j, by simp [hai]⟩
    · obtain ⟨b, hb⟩ := hB.maps a ha (fun h => haP (Finset.mem_erase.2 ⟨hai, h⟩))
      exact ⟨b, by simp [hai, hb]⟩
  · intro a b hab
    rw [upd] at hab
    split_ifs at hab with hai
    · simp only [Option.some.injEq] at hab
      subst hab
      exact ⟨hB.subH hj, by simp⟩
    · obtain ⟨h1, h2⟩ := hB.range a b hab
      exact ⟨h1, fun h => h2 (Finset.mem_of_mem_erase h)⟩
  · intro a a' b h1 h2
    rw [upd] at h1 h2
    have hmi : m i = none := hB.none_in i hi
    split_ifs at h1 h2 with e1 e2 e2
    · rw [e1, e2]
    · simp only [Option.some.injEq] at h1
      subst h1
      exact absurd hj (hB.range a' j h2).2
    · simp only [Option.some.injEq] at h2
      subst h2
      exact absurd hj (hB.range a j h1).2
    · exact hB.inj _ _ _ h1 h2

theorem ext_inj {P₀ H₀ : Finset ℕ} (hB : Base P₀ H₀ P H m) {i : ℕ} {g : ℕ → Option ℕ}
    (hg : IsCrit P H i g) : ∀ a a' b, ext P m g a = some b → ext P m g a' = some b → a = a' := by
  intro a a' b h1 h2
  simp only [ext] at h1 h2
  split_ifs at h1 h2 with ha ha'
  · exact hg.inj _ _ _ h1 h2
  · exact absurd (hg.range _ _ h1) (hB.range a' b h2).2
  · exact absurd (hg.range _ _ h2) (hB.range a b h1).2
  · exact hB.inj _ _ _ h1 h2

theorem muR_php_le_one (hB : Base (Finset.range (n + 1)) (Finset.range n) P H m) {C : Clause}
    (hC : C ∈ php n) : muR n m P H C ≤ 1 := by
  rcases mem_php hC with ⟨i, hi, rfl⟩ | ⟨i, k, j, hik, hk, hj, rfl⟩
  · by_cases hiP : i ∈ P
    · refine (muR_le (S := {i}) (by simpa using hiP) fun i' g hg hi' => ?_).trans (by simp)
      have hii' : i ≠ i' := fun e => hi' (by simp [e])
      obtain ⟨b, hb, hgb⟩ := hg.maps i hiP hii'
      have hbn : b < n := by simpa using hB.subH hb
      refine ⟨(true, var n i b), List.mem_map.2 ⟨b, List.mem_range.2 hbn, rfl⟩, ?_⟩
      simp [critAsg_var _ hbn, ext, hiP, hgb]
    · refine (muR_le (S := ∅) (by simp) fun i' g hg _ => ?_).trans (by simp)
      obtain ⟨b, hb⟩ := hB.maps i (by simp; omega) hiP
      have hbn : b < n := by simpa using (hB.range i b hb).1
      refine ⟨(true, var n i b), List.mem_map.2 ⟨b, List.mem_range.2 hbn, rfl⟩, ?_⟩
      simp [critAsg_var _ hbn, ext, hiP, hb]
  · refine (muR_le (S := ∅) (by simp) fun i' g hg _ => ?_).trans (by simp)
    by_cases hgi : ext P m g i = some j
    · refine ⟨(false, var n k j), by simp [holeClause], ?_⟩
      have : ext P m g k ≠ some j := fun h => by
        have := ext_inj hB hg _ _ _ hgi h; omega
      simp [critAsg_var _ hj, this]
    · exact ⟨(false, var n i j), by simp [holeClause], by simp [critAsg_var _ hj, hgi]⟩

/-- A clause killed by the matching: its monotone translation contains a matched pair. -/
def Killed (n : ℕ) (P₀ H₀ : Finset ℕ) (m : ℕ → Option ℕ) (C : Clause) : Prop :=
  ∃ i j, m i = some j ∧ (i, j) ∈ monoVarsOn n P₀ H₀ C

theorem muR_killed {P₀ H₀ : Finset ℕ} (hH₀ : ∀ b ∈ H₀, b < n) (hB : Base P₀ H₀ P H m)
    {C : Clause} (hK : Killed n P₀ H₀ m C) : muR n m P H C = 0 := by
  obtain ⟨i₀, j₀, hm, hmono⟩ := hK
  obtain ⟨hmem, hc⟩ := Finset.mem_filter.1 hmono
  have hj₀ : j₀ < n := hH₀ _ (Finset.mem_product.1 hmem).2
  have hi₀ : i₀ ∉ P := fun h => by rw [hB.none_in i₀ h] at hm; exact absurd hm (by simp)
  refine Nat.le_zero.1 ((muR_le (S := ∅) (by simp) fun i g hg _ => ?_).trans (by simp))
  rcases hc with hc | ⟨a', ha', hne, hc⟩
  · exact ⟨_, hc, by simp [critAsg_var _ hj₀, ext, hi₀, hm]⟩
  · refine ⟨_, hc, ?_⟩
    have : ext P m g a' ≠ some j₀ := by
      intro h
      simp only [ext] at h
      split_ifs at h with ha
      · exact (hB.range i₀ j₀ hm).2 (hg.range _ _ h)
      · exact hne (hB.inj _ _ _ h hm)
    simp [critAsg_var _ hj₀, this]

theorem killed_step {P₀ H₀ : Finset ℕ} (hB : Base P₀ H₀ P H m) {i j : ℕ} (hi : i ∈ P)
    {C : Clause} (hK : Killed n P₀ H₀ m C) : Killed n P₀ H₀ (Function.update m i (some j)) C := by
  obtain ⟨a, b, hab, hmono⟩ := hK
  have hai : a ≠ i := fun e => by rw [e, hB.none_in i hi] at hab; exact absurd hab (by simp)
  exact ⟨a, b, by simp [hai, hab], hmono⟩

/-! ### Averaging -/

theorem exists_heavy_pair {ι : Type*} (W : Finset ι) (M : ι → Finset (ℕ × ℕ))
    (Q : Finset (ℕ × ℕ)) (hQ : ∀ C ∈ W, M C ⊆ Q) (hQne : Q.Nonempty) (w : ℕ)
    (hw : ∀ C ∈ W, w ≤ (M C).card) :
    ∃ p ∈ Q, W.card * w ≤ (W.filter fun C => p ∈ M C).card * Q.card := by
  have hsum : ∑ p ∈ Q, (W.filter fun C => p ∈ M C).card = ∑ C ∈ W, (M C).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C hC => ?_
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hQ C hC)]
  have hge : W.card * w ≤ ∑ p ∈ Q, (W.filter fun C => p ∈ M C).card := by
    rw [hsum]
    simpa [smul_eq_mul] using Finset.card_nsmul_le_sum W (fun C => (M C).card) w hw
  by_contra hno
  push Not at hno
  have hlt : ∑ p ∈ Q, (W.filter fun C => p ∈ M C).card * Q.card < ∑ _p ∈ Q, W.card * w :=
    Finset.sum_lt_sum_of_nonempty hQne hno
  rw [← Finset.sum_mul, Finset.sum_const, smul_eq_mul] at hlt
  have := Nat.mul_le_mul_right Q.card hge
  nlinarith

/-! ### Greedy restriction -/

section Greedy

variable (n : ℕ) (R : DagRefutation (php n)) (w : ℕ)

/-- The wide clauses of `R` (monotone width at least `w` relative to `(P, H)`) not killed by `m`. -/
noncomputable def wideAlive (P H : Finset ℕ) (m : ℕ → Option ℕ) : Finset Clause :=
  R.lines.toFinset.filter fun C =>
    ¬ Killed n (Finset.range (n + 1)) (Finset.range n) m C ∧ w ≤ (monoVarsOn n P H C).card

theorem stage (hwD : w ≤ n * (n + 1)) :
    ∀ s, s ≤ n → ∃ P H m, Base (Finset.range (n + 1)) (Finset.range n) P H m ∧
      P.card = n + 1 - s ∧ H.card = n - s ∧
      (wideAlive n R w P H m).card * (n * (n + 1)) ^ s ≤
        R.lines.toFinset.card * (n * (n + 1) - w) ^ s
  | 0, _ => ⟨Finset.range (n + 1), Finset.range n, fun _ => none, base_init _ _, by simp, by simp,
      by simp only [pow_zero, mul_one]; exact Finset.card_le_card (Finset.filter_subset _ _)⟩
  | s + 1, hs => by
      obtain ⟨P, H, m, hB, hP, hH, hW⟩ := stage hwD s (by omega)
      have hHne : H.Nonempty := Finset.card_pos.1 (by omega)
      have hPne : P.Nonempty := Finset.card_pos.1 (by omega)
      set D := n * (n + 1)
      set W := wideAlive n R w P H m
      -- choose the pair
      obtain ⟨⟨i, j⟩, hij, hheavy⟩ : ∃ p ∈ P ×ˢ H,
          W.card * w ≤ (W.filter fun C => p ∈ monoVarsOn n P H C).card * (P ×ˢ H).card := by
        refine exists_heavy_pair W (fun C => monoVarsOn n P H C) (P ×ˢ H)
          (fun C _ => Finset.filter_subset _ _) (hPne.product hHne) w (fun C hC => ?_)
        exact (Finset.mem_filter.1 hC).2.2
      obtain ⟨hi, hj⟩ := Finset.mem_product.1 hij
      refine ⟨P.erase i, H.erase j, Function.update m i (some j), base_step hB hi hj,
        by rw [Finset.card_erase_of_mem hi, hP]; omega,
        by rw [Finset.card_erase_of_mem hj, hH]; omega, ?_⟩
      set W' := wideAlive n R w (P.erase i) (H.erase j) (Function.update m i (some j))
      set Fk := W.filter fun C => (i, j) ∈ monoVarsOn n P H C
      have hsub : W' ⊆ W \ Fk := by
        intro C hC
        obtain ⟨hCl, hnK, hwide⟩ := Finset.mem_filter.1 hC
        have hnK0 : ¬ Killed n (Finset.range (n + 1)) (Finset.range n) m C :=
          fun hK => hnK (killed_step hB hi hK)
        refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hCl, hnK0, hwide.trans
          (Finset.card_le_card (monoVarsOn_mono (Finset.erase_subset _ _)
            (Finset.erase_subset _ _) C))⟩, fun hF => hnK ?_⟩
        refine ⟨i, j, by simp, monoVarsOn_mono hB.subP hB.subH C (Finset.mem_filter.1 hF).2⟩
      have hFk : Fk ⊆ W := Finset.filter_subset _ _
      have hcardW' : W'.card + Fk.card ≤ W.card := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_sdiff_of_subset hFk] at h1
        have h2 : Fk.card ≤ W.card := Finset.card_le_card hFk
        omega
      have hPH : (P ×ˢ H).card ≤ D := by
        calc (P ×ˢ H).card = (n + 1 - s) * (n - s) := by rw [Finset.card_product, hP, hH]
          _ ≤ (n + 1) * n := Nat.mul_le_mul (by omega) (by omega)
          _ = D := mul_comm _ _
      have hstep : W'.card * D ≤ W.card * (D - w) := by
        have h1 : W.card * w ≤ Fk.card * D := hheavy.trans (Nat.mul_le_mul_left _ hPH)
        have h2 : (W'.card + Fk.card) * D ≤ W.card * D := Nat.mul_le_mul_right _ hcardW'
        rw [Nat.mul_sub]
        rw [add_mul] at h2
        omega
      calc W'.card * D ^ (s + 1) = (W'.card * D) * D ^ s := by ring
        _ ≤ (W.card * (D - w)) * D ^ s := Nat.mul_le_mul_right _ hstep
        _ = (W.card * D ^ s) * (D - w) := by ring
        _ ≤ (R.lines.toFinset.card * (D - w) ^ s) * (D - w) := Nat.mul_le_mul_right _ hW
        _ = R.lines.toFinset.card * (D - w) ^ (s + 1) := by ring

end Greedy

/-- At the last stage some clause is wide and alive. -/
theorem final_alive (R : DagRefutation (php n)) {w : ℕ} {P H : Finset ℕ} {m : ℕ → Option ℕ}
    (hB : Base (Finset.range (n + 1)) (Finset.range n) P H m) (hcard : P.card = H.card + 1)
    (h3 : 3 ≤ P.card) (hw : 9 * w ≤ 2 * (P.card - 1) ^ 2) :
    (wideAlive n R w P H m).Nonempty := by
  have hlast : [] ∈ R.lines := List.mem_of_getLast? R.last
  obtain ⟨C, hC, h1, h2⟩ := exists_mid_muR (n := n) (m := m) (P := P) (H := H)
    (fun C hC => muR_php_le_one hB hC) (t := P.card / 3) (by omega) R.valid
    ⟨[], hlast, by rw [muR_nil hcard]; omega⟩
  refine ⟨C, Finset.mem_filter.2 ⟨List.mem_toFinset.2 hC, fun hK => ?_, ?_⟩⟩
  · rw [muR_killed (fun b hb => by simpa using hb) hB hK] at h1
    omega
  · have hwidth := muR_mul_le_monoVars (n := n) (m := m) (P := P) (H := H) C
    have ha := width_arith (N := P.card) (s := muR n m P H C) h1 h2
    omega

theorem final_arith {n : ℕ} (hn : 32 ≤ n) :
    9 * ((n * (n + 1) + 7) / 8) ≤ 2 * (n + 1 - 6 * (n / 32) - 1) ^ 2 := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 32 ∧ n = 32 * q + r :=
    ⟨n / 32, n % 32, Nat.mod_lt _ (by omega), (Nat.div_add_mod n 32).symm⟩
  have hq : (32 * q + r) / 32 = q := by omega
  rw [hq]
  have e : 32 * q + r + 1 - 6 * q - 1 = 26 * q + r := by omega
  rw [e]
  have hq1 : 1 ≤ q := by omega
  have h8 : 8 * ((( 32 * q + r) * (32 * q + r + 1) + 7) / 8) ≤
      (32 * q + r) * (32 * q + r + 1) + 7 := Nat.mul_div_le _ _
  nlinarith

/-- **Haken's theorem for DAG-like resolution** (Beame–Pitassi): every DAG-like refutation of
`PHP(n+1, n)` has at least `2^(n/32)` clauses. -/
theorem php_dag_size (n : ℕ) (R : DagRefutation (php n)) : 2 ^ (n / 32) ≤ R.size := by
  have hlast : [] ∈ R.lines := List.mem_of_getLast? R.last
  have hsize : R.lines.toFinset.card ≤ R.size := List.toFinset_card_le _
  by_cases hn : n < 32
  · rw [Nat.div_eq_of_lt hn, pow_zero]
    exact (Finset.card_pos.2 ⟨[], List.mem_toFinset.2 hlast⟩).trans_le hsize
  push Not at hn
  set k := n / 32
  set r := 6 * k
  set D := n * (n + 1)
  set w := (D + 7) / 8
  have hwD : w ≤ D := by
    have : 1 ≤ D := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hr : r ≤ n := by omega
  obtain ⟨P, H, m, hB, hP, hH, hW⟩ := stage n R w hwD r hr
  have hne := final_alive R hB (by rw [hP, hH]; omega) (by rw [hP]; omega)
    (by rw [hP]; exact final_arith hn)
  have h1 : 1 ≤ (wideAlive n R w P H m).card := Finset.card_pos.2 hne
  have hDpos : 0 < D := by positivity
  have hW1 : D ^ r ≤ R.lines.toFinset.card * (D - w) ^ r := by
    calc D ^ r = 1 * D ^ r := (one_mul _).symm
      _ ≤ (wideAlive n R w P H m).card * D ^ r := Nat.mul_le_mul_right _ h1
      _ ≤ _ := hW
  have h87 : 8 * (D - w) ≤ 7 * D := by omega
  have hkey : 8 ^ r * D ^ r ≤ R.lines.toFinset.card * 7 ^ r * D ^ r := by
    calc 8 ^ r * D ^ r ≤ 8 ^ r * (R.lines.toFinset.card * (D - w) ^ r) :=
          Nat.mul_le_mul_left _ hW1
      _ = R.lines.toFinset.card * (8 * (D - w)) ^ r := by ring
      _ ≤ R.lines.toFinset.card * (7 * D) ^ r :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h87 r)
      _ = R.lines.toFinset.card * 7 ^ r * D ^ r := by rw [mul_pow, mul_assoc]
  have h87r : 8 ^ r ≤ R.lines.toFinset.card * 7 ^ r :=
    Nat.le_of_mul_le_mul_right hkey (by positivity)
  have h2 : 2 ^ k * 7 ^ r ≤ 8 ^ r := by
    have : 2 * 7 ^ 6 ≤ 8 ^ 6 := by norm_num
    calc 2 ^ k * 7 ^ r = (2 * 7 ^ 6) ^ k := by rw [mul_pow, ← pow_mul]
      _ ≤ (8 ^ 6) ^ k := Nat.pow_le_pow_left this k
      _ = 8 ^ r := by rw [← pow_mul]
  have : 2 ^ k * 7 ^ r ≤ R.lines.toFinset.card * 7 ^ r := h2.trans h87r
  exact (Nat.le_of_mul_le_mul_right this (by positivity)).trans hsize

end Complexity.Sat.PHP
