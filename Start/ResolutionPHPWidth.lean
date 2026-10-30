/-
**Beame–Pitassi: a DAG-like refutation of the pigeonhole principle contains a clause of large
monotone width.**

Task `M22-HAKEN-PHP-DAG`, steps 1–4 of the Beame–Pitassi argument ("Simplified and improved
resolution lower bounds", 1996).

* Pigeons form a finite set `P`, holes a finite set `H` with `P.card = H.card + 1`; the variable
  "pigeon `a` in hole `b`" is `var n a b` (holes below `n`).
* `IsCrit P H i g`: `g` is an `i`-critical assignment, a bijection from `P ∖ {i}` onto `H`
  (`g a = some b` means pigeon `a` sits in hole `b`); `critAsg n g` is the corresponding assignment
  of the variables.
* `mu n P H C`: the least `|S|`, `S ⊆ P`, such that every `i`-critical assignment with `i ∉ S`
  satisfies `C` (`Witness`).  `mu_resolvent`: `μ` is subadditive under resolution;
  `mu_nil`: `μ [] = |P|`.
* `exists_mid_mu`: a DAG-like derivation from clauses of complexity at most one that contains a
  clause of complexity above `t ≥ 1` contains one of complexity in `(t, 2t]`.
* `mu_mul_le_monoVars`: `μ(C) · (|P| - μ(C)) ≤ |monoVars C|`, where `monoVars C` is the set of
  pairs `(a, b)` such that `x_{a,b}` occurs in the monotone translation of `C` (a positive
  `x_{a,b}`, or a negative `x_{a',b}` with `a' ≠ a`).
* **`dag_exists_wide_monotone`**: every DAG-like refutation of `PHP(n+1, n)`, `n ≥ 2`, contains a
  clause `C` with `2 n² ≤ 9 |monoVars C|`.
-/

import Start.ResolutionDag
import Start.ResolutionPHP

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Sat.PHP

open Classical

/-! ### Total assignments -/

/-- A clause is true under a total assignment of the variables. -/
def EvalC (τ : ℕ → Bool) (C : Clause) : Prop := ∃ l ∈ C, (if l.1 then τ l.2 else !τ l.2) = true

theorem evalC_resolvent {τ : ℕ → Bool} {k : ℕ} {C₁ C₂ : Clause} (h₁ : EvalC τ C₁)
    (h₂ : EvalC τ C₂) : EvalC τ (resolvent k C₁ C₂) := by
  obtain ⟨l, hl, hlv⟩ := h₁
  obtain ⟨l', hl', hl'v⟩ := h₂
  by_cases e1 : l = (true, k)
  · by_cases e2 : l' = (false, k)
    · subst e1; subst e2
      simp only [ite_true] at hlv
      simp [hlv] at hl'v
    · exact ⟨l', List.mem_append_right _ (List.mem_filter.2 ⟨hl', by simpa using e2⟩), hl'v⟩
  · exact ⟨l, List.mem_append_left _ (List.mem_filter.2 ⟨hl, by simpa using e1⟩), hlv⟩

/-- The assignment of a partial map from pigeons to holes. -/
def critAsg (n : ℕ) (g : ℕ → Option ℕ) (k : ℕ) : Bool := decide (g (k / n) = some (k % n))

theorem var_div {n a b : ℕ} (hb : b < n) : var n a b / n = a := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]

theorem var_mod {n a b : ℕ} (hb : b < n) : var n a b % n = b := by
  unfold var
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem critAsg_var {n a b : ℕ} (g : ℕ → Option ℕ) (hb : b < n) :
    critAsg n g (var n a b) = decide (g a = some b) := by
  rw [critAsg, var_div hb, var_mod hb]

/-! ### Critical assignments -/

/-- `g` is an `i`-critical assignment: a bijection from `P ∖ {i}` onto `H`. -/
structure IsCrit (P H : Finset ℕ) (i : ℕ) (g : ℕ → Option ℕ) : Prop where
  mem : i ∈ P
  self : g i = none
  outside : ∀ a, a ∉ P → g a = none
  maps : ∀ a ∈ P, a ≠ i → ∃ b ∈ H, g a = some b
  range : ∀ a b, g a = some b → b ∈ H
  inj : ∀ a a' b, g a = some b → g a' = some b → a = a'
  surj : ∀ b ∈ H, ∃ a, g a = some b

theorem crit_exists {P H : Finset ℕ} (hcard : P.card = H.card + 1) {i : ℕ} (hi : i ∈ P) :
    ∃ g, IsCrit P H i g := by
  have hc : (P.erase i).card = H.card := by rw [Finset.card_erase_of_mem hi, hcard]; rfl
  let e : P.erase i ≃ H := Finset.equivOfCardEq hc
  let g : ℕ → Option ℕ := fun a => if h : a ∈ P.erase i then some (e ⟨a, h⟩ : ℕ) else none
  refine ⟨g, hi, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [g]
  · intro a ha; simp [g, ha]
  · intro a ha hai
    have h : a ∈ P.erase i := Finset.mem_erase.2 ⟨hai, ha⟩
    exact ⟨_, (e ⟨a, h⟩).2, by simp [g, hai, ha]⟩
  · intro a b hab
    simp only [g] at hab
    split_ifs at hab with h
    · simp only [Option.some.injEq] at hab
      rw [← hab]; exact (e ⟨a, h⟩).2
  · intro a a' b h1 h2
    simp only [g] at h1 h2
    split_ifs at h1 h2 with ha ha'
    simp only [Option.some.injEq] at h1 h2
    have : e ⟨a, ha⟩ = e ⟨a', ha'⟩ := Subtype.ext (h1.trans h2.symm)
    exact congrArg Subtype.val (e.injective this)
  · intro b hb
    obtain ⟨⟨a, ha⟩, hab⟩ := e.surjective ⟨b, hb⟩
    have ha' := Finset.mem_erase.1 ha
    exact ⟨a, by simp [g, ha'.1, ha'.2, hab]⟩

/-! ### The complexity measure -/

/-- Every `i`-critical assignment with `i ∉ S` satisfies `C`. -/
def Witness (n : ℕ) (P H S : Finset ℕ) (C : Clause) : Prop :=
  ∀ i g, IsCrit P H i g → i ∉ S → EvalC (critAsg n g) C

theorem witness_self (n : ℕ) (P H : Finset ℕ) (C : Clause) : Witness n P H P C :=
  fun _ _ hg hi => absurd hg.mem hi

theorem exists_witness (n : ℕ) (P H : Finset ℕ) (C : Clause) :
    ∃ k, ∃ S ⊆ P, S.card = k ∧ Witness n P H S C :=
  ⟨P.card, P, subset_rfl, rfl, witness_self n P H C⟩

/-- The complexity `μ(C)`. -/
noncomputable def mu (n : ℕ) (P H : Finset ℕ) (C : Clause) : ℕ := Nat.find (exists_witness n P H C)

variable {n : ℕ} {P H : Finset ℕ}

theorem mu_spec (C : Clause) : ∃ S ⊆ P, S.card = mu n P H C ∧ Witness n P H S C :=
  Nat.find_spec (exists_witness n P H C)

theorem mu_le {C : Clause} {S : Finset ℕ} (hS : S ⊆ P) (hw : Witness n P H S C) :
    mu n P H C ≤ S.card :=
  Nat.find_min' (exists_witness n P H C) ⟨S, hS, rfl, hw⟩

theorem mu_le_card (C : Clause) : mu n P H C ≤ P.card := mu_le subset_rfl (witness_self n P H C)

theorem mu_resolvent (k : ℕ) (C₁ C₂ : Clause) :
    mu n P H (resolvent k C₁ C₂) ≤ mu n P H C₁ + mu n P H C₂ := by
  obtain ⟨S₁, hS₁, hc₁, hw₁⟩ := mu_spec (n := n) (P := P) (H := H) C₁
  obtain ⟨S₂, hS₂, hc₂, hw₂⟩ := mu_spec (n := n) (P := P) (H := H) C₂
  calc mu n P H (resolvent k C₁ C₂) ≤ (S₁ ∪ S₂).card := by
        refine mu_le (Finset.union_subset hS₁ hS₂) fun i g hg hi => ?_
        rw [Finset.mem_union, not_or] at hi
        exact evalC_resolvent (hw₁ i g hg hi.1) (hw₂ i g hg hi.2)
    _ ≤ S₁.card + S₂.card := Finset.card_union_le _ _
    _ = _ := by rw [hc₁, hc₂]

theorem mu_nil (hcard : P.card = H.card + 1) : mu n P H [] = P.card := by
  refine le_antisymm (mu_le_card _) ?_
  obtain ⟨S, hS, hc, hw⟩ := mu_spec (n := n) (P := P) (H := H) []
  rw [← hc]
  refine Finset.card_le_card fun i hi => ?_
  by_contra hiS
  obtain ⟨g, hg⟩ := crit_exists hcard hi
  obtain ⟨l, hl, -⟩ := hw i g hg hiS
  simp at hl

/-! ### A clause of middle complexity -/

theorem exists_mid_mu {F : Cnf} (hF : ∀ C ∈ F, mu n P H C ≤ 1) {t : ℕ} (ht : 1 ≤ t) :
    ∀ {L : List Clause}, DagDeriv F L → (∃ C ∈ L, t < mu n P H C) →
      ∃ C ∈ L, t < mu n P H C ∧ mu n P H C ≤ 2 * t
  | _, .nil, h => by simp at h
  | _, .snoc (L := L) (C := C) hL hC, h => by
      by_cases hex : ∃ D ∈ L, t < mu n P H D
      · obtain ⟨D, hD, h1, h2⟩ := exists_mid_mu hF ht hL hex
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
          · have := mu_resolvent (n := n) (P := P) (H := H) k C₁ C₂
            have := hex C₁ h₁
            have := hex C₂ h₂
            omega

/-! ### Monotone width -/

/-- The pairs `(a, b)` such that `x_{a,b}` occurs in the monotone translation of `C`. -/
noncomputable def monoVarsOn (n : ℕ) (P H : Finset ℕ) (C : Clause) : Finset (ℕ × ℕ) :=
  (P ×ˢ H).filter fun ab =>
    (true, var n ab.1 ab.2) ∈ C ∨ ∃ a' ∈ P, a' ≠ ab.1 ∧ (false, var n a' ab.2) ∈ C

/-- Moving the hole of pigeon `j` to pigeon `i`. -/
def moveHole (g : ℕ → Option ℕ) (i j l : ℕ) : ℕ → Option ℕ :=
  Function.update (Function.update g i (some l)) j none

theorem isCrit_moveHole {i j l : ℕ} {g : ℕ → Option ℕ} (hg : IsCrit P H i g) (hj : j ∈ P)
    (hji : j ≠ i) (hl : g j = some l) : IsCrit P H j (moveHole g i j l) := by
  have hlH : l ∈ H := hg.range _ _ hl
  have upd : ∀ a, moveHole g i j l a = if a = j then none else if a = i then some l else g a := by
    intro a
    simp only [moveHole, Function.update_apply]
  refine ⟨hj, by simp [upd], ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have h1 : a ≠ j := fun e => ha (e ▸ hj)
    have h2 : a ≠ i := fun e => ha (e ▸ hg.mem)
    simp [upd, h1, h2, hg.outside a ha]
  · intro a ha haj
    by_cases hai : a = i
    · exact ⟨l, hlH, by subst hai; simp [upd, Ne.symm hji]⟩
    · obtain ⟨b, hb, hgb⟩ := hg.maps a ha hai
      exact ⟨b, hb, by simp [upd, haj, hai, hgb]⟩
  · intro a b hab
    rw [upd] at hab
    split_ifs at hab with h1 h2
    · simp only [Option.some.injEq] at hab; exact hab ▸ hlH
    · exact hg.range _ _ hab
  · intro a a' b h1 h2
    rw [upd] at h1 h2
    by_cases e1 : a = j
    · simp [e1] at h1
    by_cases e3 : a' = j
    · simp [e3] at h2
    simp only [e1, e3, ite_false] at h1 h2
    by_cases e2 : a = i <;> by_cases e4 : a' = i
    · rw [e2, e4]
    · simp only [e2, ite_true, Option.some.injEq, e4, ite_false] at h1 h2
      subst h1; exact absurd (hg.inj _ _ _ h2 hl) e3
    · simp only [e2, ite_false, e4, ite_true, Option.some.injEq] at h1 h2
      subst h2; exact absurd (hg.inj _ _ _ h1 hl) e1
    · simp only [e2, e4, ite_false] at h1 h2; exact hg.inj _ _ _ h1 h2
  · intro b hb
    obtain ⟨a, ha⟩ := hg.surj b hb
    by_cases haj : a = j
    · subst haj
      rw [hl] at ha
      simp only [Option.some.injEq] at ha
      subst ha
      exact ⟨i, by simp [upd, Ne.symm hji]⟩
    · have hai : a ≠ i := fun e => by rw [e, hg.self] at ha; exact absurd ha (by simp)
      exact ⟨a, by simp [upd, haj, hai, ha]⟩

/-- The key step: `C` false at `g` and true at `moveHole g i j l` puts `(i, l)` into the monotone
translation of `C`. -/
theorem mem_monoVars_of_flip {i j l : ℕ} {g : ℕ → Option ℕ} (hg : IsCrit P H i g) (hj : j ∈ P)
    (hji : j ≠ i) (hl : g j = some l) {C : Clause}
    (hf : ¬ EvalC (critAsg n g) C) (ht : EvalC (critAsg n (moveHole g i j l)) C) :
    (i, l) ∈ monoVarsOn n P H C := by
  have hlH : l ∈ H := hg.range _ _ hl
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hg.mem, hlH⟩, ?_⟩
  obtain ⟨⟨b, k⟩, hlit, hv⟩ := ht
  have hfl : (if b then critAsg n g k else !critAsg n g k) = false := by
    by_contra h
    exact hf ⟨(b, k), hlit, by simpa using h⟩
  have hk : k = var n (k / n) (k % n) := by unfold var; exact (Nat.div_add_mod k n).symm
  have hupd : ∀ a, moveHole g i j l a = if a = j then none else if a = i then some l else g a := by
    intro a
    simp only [moveHole, Function.update_apply]
  by_cases hkj : k / n = j
  · -- the variable of pigeon `j`
    have h1 : critAsg n (moveHole g i j l) k = false := by
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
    · have h1 : critAsg n g k = false := by simp [critAsg, hki, hg.self]
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

theorem mu_mul_le_monoVars (C : Clause) :
    mu n P H C * (P.card - mu n P H C) ≤ (monoVarsOn n P H C).card := by
  obtain ⟨S, hS, hc, hw⟩ := mu_spec (n := n) (P := P) (H := H) C
  -- for each `i ∈ S`, an `i`-critical assignment falsifying `C`
  have hfals : ∀ i ∈ S, ∃ g, IsCrit P H i g ∧ ¬ EvalC (critAsg n g) C := by
    intro i hi
    by_contra hno
    push Not at hno
    have hw' : Witness n P H (S.erase i) C := by
      intro i' g hg hi'
      by_cases e : i' = i
      · subst e; exact hno g hg
      · exact hw i' g hg (fun h => hi' (Finset.mem_erase.2 ⟨e, h⟩))
    have := mu_le ((Finset.erase_subset i S).trans hS) hw'
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
    exact mem_monoVars_of_flip (hG i hi) hjP hji hl (hGf i hi)
      (hw j _ (isCrit_moveHole (hG i hi) hjP hji hl) hjS)
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

/-! ### The pigeonhole formula -/

/-- The monotone width of a clause of `PHP(n+1, n)`. -/
noncomputable def monoVars (n : ℕ) (C : Clause) : Finset (ℕ × ℕ) :=
  monoVarsOn n (Finset.range (n + 1)) (Finset.range n) C

theorem mu_php_le_one (n : ℕ) {C : Clause} (hC : C ∈ php n) :
    mu n (Finset.range (n + 1)) (Finset.range n) C ≤ 1 := by
  rcases mem_php hC with ⟨i, hi, rfl⟩ | ⟨i, k, j, hik, hk, hj, rfl⟩
  · refine (mu_le (S := {i}) (by simp; omega) fun i' g hg hi' => ?_).trans (by simp)
    have hii' : i ≠ i' := fun e => hi' (by simp [e])
    obtain ⟨b, hb, hgb⟩ := hg.maps i (by simp; omega) hii'
    have hbn : b < n := by simpa using hb
    refine ⟨(true, var n i b), ?_, ?_⟩
    · exact List.mem_map.2 ⟨b, List.mem_range.2 hbn, rfl⟩
    · simp [critAsg_var g hbn, hgb]
  · refine (mu_le (S := ∅) (by simp) fun i' g hg _ => ?_).trans (by simp)
    by_cases hgi : g i = some j
    · refine ⟨(false, var n k j), by simp [holeClause], ?_⟩
      have : g k ≠ some j := fun h => by
        have := hg.inj _ _ _ hgi h; omega
      simp [critAsg_var g hj, this]
    · exact ⟨(false, var n i j), by simp [holeClause], by simp [critAsg_var g hj, hgi]⟩

theorem width_arith {N s : ℕ} (h1 : N / 3 < s) (h2 : s ≤ 2 * (N / 3)) :
    2 * (N - 1) ^ 2 ≤ 9 * (s * (N - s)) := by
  obtain ⟨d, hd⟩ : ∃ d, N = s + d := ⟨N - s, by omega⟩
  have e1 : N - s = d := by omega
  have h3 : N < 3 * s := by omega
  have h4 : N ≤ 3 * d := by omega
  have h5 : (N - 1) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left (Nat.sub_le N 1) 2
  rw [e1]
  have h6 : 2 * N ^ 2 ≤ 9 * (s * d) := by
    zify at h3 h4 hd ⊢
    nlinarith [mul_nonneg (sub_nonneg.2 h3.le) (sub_nonneg.2 h4)]
  omega

/-- **Beame–Pitassi monotone width bound.** Every DAG-like refutation of `PHP(n+1, n)`, `n ≥ 2`,
contains a clause whose monotone translation mentions at least `2n²/9` variables. -/
theorem dag_exists_wide_monotone (n : ℕ) (hn : 2 ≤ n) (R : DagRefutation (php n)) :
    ∃ C ∈ R.lines, 2 * n ^ 2 ≤ 9 * (monoVars n C).card := by
  set P := Finset.range (n + 1)
  set H := Finset.range n
  have hcard : P.card = H.card + 1 := by simp [P, H]
  have hlast : [] ∈ R.lines := List.mem_of_getLast? R.last
  have hP : P.card = n + 1 := by simp [P]
  obtain ⟨C, hC, h1, h2⟩ := exists_mid_mu (n := n) (P := P) (H := H)
    (fun C hC => mu_php_le_one n hC) (t := P.card / 3) (by omega) R.valid
    ⟨[], hlast, by rw [mu_nil hcard]; omega⟩
  refine ⟨C, hC, ?_⟩
  have hw := mu_mul_le_monoVars (n := n) (P := P) (H := H) C
  have ha := width_arith (N := P.card) (s := mu n P H C) h1 h2
  rw [hP, Nat.add_sub_cancel] at ha
  calc 2 * n ^ 2 ≤ 9 * (mu n P H C * (n + 1 - mu n P H C)) := ha
    _ ≤ 9 * (monoVars n C).card := by
        rw [← hP]; exact Nat.mul_le_mul_left 9 hw

end Complexity.Sat.PHP
