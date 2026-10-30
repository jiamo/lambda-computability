/-
**Parity is not in `AC⁰`.**

The proof follows Håstad: random restrictions, counted with Razborov's encoding
(`Start/SwitchingLemma.lean`), switch the bottom layers of a constant-depth circuit to decision
trees of small depth, one layer at a time, while many variables stay free; a small-width DNF cannot
compute parity on more free variables than its width.

* `Switching.RR ρ₀ ℓ`: the refinements of `ρ₀` with exactly `ℓ` free variables;
  `Switching.card_RR`: there are as many as restrictions with `ℓ` free variables on
  `|freeSet ρ₀|` variables.
* `Switching.switching_rel`: the switching lemma relative to `ρ₀`.
* `Parity.toDNF`: the DNF of the accepting paths of a decision tree.
* `Parity.round`: one switching round on a circuit in negation normal form.
* `Complexity.parity_circuit_bound`: a depth-`d` circuit (`d ≥ 2`) that computes parity on `n`
  inputs has `n < (32 (log₂ S + 2))^(d-1)`, `S` its size; `parity_log_size_lower_bound` and
  `parity_size_lower_bound` restate it as `S > 2^(n^(1/(d-1))/32 - 2)`, i.e.
  `S = 2^(Ω(n^(1/(d-1))))`; `parity_depth_le_one`: depth `≤ 1` circuits handle `n ≤ 1` only.
* `Complexity.parity_not_AC0 : ¬ InAC0 Parity`.
-/

import Start.SwitchingLemma
import Start.AC0

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Switching

open Finset

variable {n : ℕ}

/-! ### The switching lemma relative to a restriction -/

instance (ρ₀ ρ : Restriction n) : Decidable (Refines ρ₀ ρ) := by
  unfold Refines; infer_instance

/-- The refinements of `ρ₀` with exactly `ℓ` free variables. -/
def RR (ρ₀ : Restriction n) (ℓ : ℕ) : Finset (Restriction n) :=
  univ.filter (fun ρ => Refines ρ₀ ρ ∧ (freeSet ρ).card = ℓ)

theorem Refines.trans {ρ₁ ρ₂ ρ₃ : Restriction n} (h₁ : Refines ρ₁ ρ₂) (h₂ : Refines ρ₂ ρ₃) :
    Refines ρ₁ ρ₃ := fun i b h => h₂ i b (h₁ i b h)

theorem Refines.refl (ρ : Restriction n) : Refines ρ ρ := fun _ _ h => h

theorem Refines.freeSet_subset {ρ₀ ρ : Restriction n} (h : Refines ρ₀ ρ) :
    freeSet ρ ⊆ freeSet ρ₀ := by
  intro i hi
  simp only [freeSet, mem_filter, mem_univ, true_and] at hi ⊢
  cases h0 : ρ₀ i with
  | none => rfl
  | some b => rw [h i b h0] at hi; cases hi

theorem Refines.extends {ρ₀ ρ : Restriction n} (h : Refines ρ₀ ρ) {x : Fin n → Bool}
    (hx : Extends ρ x) : Extends ρ₀ x := fun i b hb => hx i b (h i b hb)

theorem card_fiber_rel (ρ₀ : Restriction n) (S : Finset (Fin n)) (hS : S ⊆ freeSet ρ₀) :
    (univ.filter (fun ρ : Restriction n => Refines ρ₀ ρ ∧ freeSet ρ = S)).card =
      2 ^ ((freeSet ρ₀).card - S.card) := by
  classical
  have h : univ.filter (fun ρ : Restriction n => Refines ρ₀ ρ ∧ freeSet ρ = S) =
      Fintype.piFinset (fun i => if i ∈ S then ({none} : Finset (Option Bool))
        else if i ∈ freeSet ρ₀ then {some false, some true} else {ρ₀ i}) := by
    ext ρ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hr, rfl⟩ i
      by_cases hi : ρ i = none
      · simp [freeSet, hi]
      · have : i ∉ freeSet ρ := by simp [freeSet, hi]
        rw [ite_eq_right this]
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hi
        split_ifs with h0
        · cases b <;> simp [hb]
        · have : ρ₀ i ≠ none := by simpa [freeSet] using h0
          obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 this
          have := hr i c hc
          simp [hc, this]
    · intro h
      refine ⟨fun i b hb => ?_, ?_⟩
      · have hi := h i
        have hiS : i ∉ S := fun hiS => by
          have := hS hiS
          simp [freeSet, hb] at this
        have hif : i ∉ freeSet ρ₀ := by simp [freeSet, hb]
        rw [ite_eq_right hiS, ite_eq_right hif, mem_singleton] at hi
        rw [hi, hb]
      · ext i
        have hi := h i
        simp only [freeSet, mem_filter, mem_univ, true_and]
        by_cases his : i ∈ S
        · rw [ite_eq_left his] at hi
          simpa [his] using hi
        · rw [ite_eq_right his] at hi
          split_ifs at hi with hif
          · simp only [mem_insert, mem_singleton] at hi
            rcases hi with hi | hi <;> simp [hi, his]
          · rw [mem_singleton] at hi
            have : ρ₀ i ≠ none := by simpa [freeSet] using hif
            simp only [his, iff_false]
            rw [hi]; exact this
  rw [h, Fintype.card_piFinset]
  have hc : ∀ i, (if i ∈ S then ({none} : Finset (Option Bool))
      else if i ∈ freeSet ρ₀ then {some false, some true} else {ρ₀ i}).card =
      if i ∈ freeSet ρ₀ \ S then 2 else 1 := by
    intro i
    by_cases h1 : i ∈ S
    · have : i ∉ freeSet ρ₀ \ S := by simp [h1]
      rw [ite_eq_left h1, ite_eq_right this]; rfl
    · by_cases h2 : i ∈ freeSet ρ₀
      · have : i ∈ freeSet ρ₀ \ S := by simp [h1, h2]
        rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left this]; rfl
      · have : i ∉ freeSet ρ₀ \ S := by simp [h2]
        rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right this]; rfl
  simp only [hc]
  rw [Fintype.prod_ite_mem, prod_const, card_sdiff_of_subset hS]

theorem mem_RR {ρ₀ ρ : Restriction n} {ℓ : ℕ} :
    ρ ∈ RR ρ₀ ℓ ↔ Refines ρ₀ ρ ∧ (freeSet ρ).card = ℓ := by
  simp [RR]

/-- There are as many refinements of `ρ₀` with `ℓ` free variables as restrictions with `ℓ` free
variables on `|freeSet ρ₀|` variables. -/
theorem card_RR (ρ₀ : Restriction n) (ℓ : ℕ) :
    (RR ρ₀ ℓ).card = (R (freeSet ρ₀).card ℓ).card := by
  classical
  rw [card_R]
  rw [card_eq_sum_card_fiberwise (f := freeSet) (t := powersetCard ℓ (freeSet ρ₀))]
  · have : ∀ S ∈ powersetCard ℓ (freeSet ρ₀),
        ((RR ρ₀ ℓ).filter (fun ρ => freeSet ρ = S)).card = 2 ^ ((freeSet ρ₀).card - ℓ) := by
      intro S hS
      rw [mem_powersetCard] at hS
      rw [← hS.2, ← card_fiber_rel ρ₀ S hS.1]
      congr 1
      ext ρ
      simp only [RR, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, rfl⟩; exact ⟨⟨h1, rfl⟩, rfl⟩
    rw [sum_congr rfl this, sum_const, card_powersetCard, smul_eq_mul]
  · intro ρ hρ
    rw [mem_coe, mem_RR] at hρ
    simp [mem_powersetCard, hρ.2, hρ.1.freeSet_subset]

/-- The refinements of `ρ₀` with `ℓ` free variables under which the canonical decision tree of
`F` has depth at least `s`. -/
def BadRel (F : DNF n) (ρ₀ : Restriction n) (ℓ s : ℕ) : Finset (Restriction n) :=
  (RR ρ₀ ℓ).filter (fun ρ => s ≤ (cdt F ρ).depth)

theorem card_badRel_le {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (ρ₀ : Restriction n) (ℓ s : ℕ) :
    (BadRel F ρ₀ ℓ s).card ≤ (RR ρ₀ (ℓ - s)).card * (4 * k) ^ s := by
  calc (BadRel F ρ₀ ℓ s).card ≤ (RR ρ₀ (ℓ - s) ×ˢ codes k s).card := by
        refine card_le_card_of_injOn (encode F s) (fun ρ hρ => ?_) ?_
        · have hρ' := mem_filter.1 hρ
          have hR := (mem_RR.1 hρ'.1)
          obtain ⟨h1, -, h3, -⟩ := encode_spec F hF s ρ hρ'.2
          have hm := encode_mem F hF s ℓ ρ (by simp [R, hR.2]) hρ'.2
          refine mem_product.2 ⟨mem_RR.2 ⟨hR.1.trans h1, by omega⟩, (mem_product.1 hm.2).2⟩
        · intro ρ₁ h₁ ρ₂ h₂ he
          exact encode_injOn F hF s (mem_filter.1 (mem_coe.1 h₁)).2
            (mem_filter.1 (mem_coe.1 h₂)).2 he
    _ = (RR ρ₀ (ℓ - s)).card * (codes k s).card := card_product _ _
    _ ≤ (RR ρ₀ (ℓ - s)).card * (4 * k) ^ s := Nat.mul_le_mul_left _ (card_codes_le k s)

/-- **The switching lemma relative to `ρ₀`**, in integers: if `ρ₀` has `m` free variables and
`2ℓ ≤ m`, then `|BadRel| · m^s ≤ |RR ρ₀ ℓ| · (16 k ℓ)^s`. -/
theorem switching_rel {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (ρ₀ : Restriction n) (ℓ s : ℕ)
    (hℓ : 2 * ℓ ≤ (freeSet ρ₀).card) :
    (BadRel F ρ₀ ℓ s).card * (freeSet ρ₀).card ^ s ≤ (RR ρ₀ ℓ).card * (16 * k * ℓ) ^ s := by
  by_cases hs : ℓ < s
  · have : BadRel F ρ₀ ℓ s = ∅ := by
      apply eq_empty_of_forall_notMem
      intro ρ hρ
      have hρ' := mem_filter.1 hρ
      have := (encode_mem F hF s ℓ ρ (by simp [R, (mem_RR.1 hρ'.1).2]) hρ'.2).1
      omega
    rw [this]; simp
  replace hs := Nat.le_of_not_lt hs
  calc (BadRel F ρ₀ ℓ s).card * (freeSet ρ₀).card ^ s
      ≤ (RR ρ₀ (ℓ - s)).card * (4 * k) ^ s * (freeSet ρ₀).card ^ s :=
        Nat.mul_le_mul_right _ (card_badRel_le F hF ρ₀ ℓ s)
    _ = ((R (freeSet ρ₀).card (ℓ - s)).card * (freeSet ρ₀).card ^ s) * (4 * k) ^ s := by
        rw [card_RR]; ring
    _ ≤ ((R (freeSet ρ₀).card ℓ).card * (4 * ℓ) ^ s) * (4 * k) ^ s :=
        Nat.mul_le_mul_right _ (card_R_iter hℓ s hs)
    _ = (RR ρ₀ ℓ).card * (16 * k * ℓ) ^ s := by
        rw [card_RR, mul_assoc, ← mul_pow, show 4 * ℓ * (4 * k) = 16 * k * ℓ by ring]

theorem badRel_eq_empty {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (ρ₀ : Restriction n) {ℓ s : ℕ}
    (hs : ℓ < s) : BadRel F ρ₀ ℓ s = ∅ := by
  apply eq_empty_of_forall_notMem
  intro ρ hρ
  have hρ' := mem_filter.1 hρ
  have := (encode_mem F hF s ℓ ρ (by simp [R, (mem_RR.1 hρ'.1).2]) hρ'.2).1
  omega

/-- The relative switching lemma with `ℓ = ⌊m / (32 k)⌋`: at most a `2^(-s)` fraction of the
refinements is bad. -/
theorem switching_rel_half {k : ℕ} (hk : 1 ≤ k) (F : DNF n) (hF : IsKDNF k F)
    (ρ₀ : Restriction n) {s : ℕ} (hs : 1 ≤ s) :
    (BadRel F ρ₀ ((freeSet ρ₀).card / (32 * k)) s).card * 2 ^ s ≤
      (RR ρ₀ ((freeSet ρ₀).card / (32 * k))).card := by
  set m := (freeSet ρ₀).card with hm
  set ℓ := m / (32 * k) with hℓ
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · have : ℓ = 0 := by rw [hℓ, h0, Nat.zero_div]
    rw [badRel_eq_empty F hF ρ₀ (by omega : ℓ < s)]
    simp
  have h32 : 32 * k * ℓ ≤ m := by
    rw [hℓ, mul_comm]; exact Nat.div_mul_le_self m (32 * k)
  have h2 : 2 * ℓ ≤ m := le_trans (by nlinarith) h32
  have key := switching_rel F hF ρ₀ ℓ s h2
  have hmp : 0 < m ^ s := pow_pos hpos s
  refine Nat.le_of_mul_le_mul_right ?_ hmp
  calc (BadRel F ρ₀ ℓ s).card * 2 ^ s * m ^ s = ((BadRel F ρ₀ ℓ s).card * m ^ s) * 2 ^ s := by
        ring
    _ ≤ ((RR ρ₀ ℓ).card * (16 * k * ℓ) ^ s) * 2 ^ s := Nat.mul_le_mul_right _ key
    _ = (RR ρ₀ ℓ).card * (32 * k * ℓ) ^ s := by
        rw [mul_assoc, ← mul_pow]; ring_nf
    _ ≤ (RR ρ₀ ℓ).card * m ^ s := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h32 s)

theorem card_RR_pos (ρ₀ : Restriction n) {ℓ : ℕ} (h : ℓ ≤ (freeSet ρ₀).card) :
    0 < (RR ρ₀ ℓ).card := by
  rw [card_RR, card_R]
  exact Nat.mul_pos (Nat.choose_pos h) (by positivity)

end Complexity.Switching

namespace Complexity.Parity

open Switching Finset

variable {n : ℕ}

/-! ### Decision trees and DNFs -/

/-- Flip the leaves of a decision tree. -/
def neg : DTree n → DTree n
  | .leaf b => .leaf (!b)
  | .node i t₀ t₁ => .node i (neg t₀) (neg t₁)

theorem eval_neg (x : Fin n → Bool) : ∀ T : DTree n, (neg T).eval x = !T.eval x
  | .leaf b => rfl
  | .node i t₀ t₁ => by
      simp only [neg, DTree.eval]
      rw [eval_neg x t₀, eval_neg x t₁]
      split_ifs <;> rfl

theorem depth_neg : ∀ T : DTree n, (neg T).depth = T.depth
  | .leaf _ => rfl
  | .node i t₀ t₁ => by simp only [neg, DTree.depth, depth_neg t₀, depth_neg t₁]

/-- The DNF of the accepting paths of a decision tree, below the path `acc`; a variable already
on the path is not queried again. -/
def toDNF : DTree n → Term n → DNF n
  | .leaf b, acc => if b then [acc] else []
  | .node i t₀ t₁, acc =>
      if (i, false) ∈ acc then toDNF t₀ acc
      else if (i, true) ∈ acc then toDNF t₁ acc
      else toDNF t₀ ((i, false) :: acc) ++ toDNF t₁ ((i, true) :: acc)

theorem DNF.eval_append (F G : DNF n) (x : Fin n → Bool) :
    DNF.eval (F ++ G) x = (DNF.eval F x || DNF.eval G x) := by
  simp [DNF.eval, List.any_append]

theorem term_eval_cons (l : Lit n) (C : Term n) (x : Fin n → Bool) :
    Term.eval (l :: C) x = ((x l.1 == l.2) && Term.eval C x) := by
  simp [Term.eval]

theorem term_eval_mem {C : Term n} {x : Fin n → Bool} (h : Term.eval C x = true) {l : Lit n}
    (hl : l ∈ C) : x l.1 = l.2 := by
  simp only [Term.eval, List.all_eq_true, beq_iff_eq] at h
  exact h l hl

theorem eval_toDNF (x : Fin n → Bool) :
    ∀ (T : DTree n) (acc : Term n), DNF.eval (toDNF T acc) x = (Term.eval acc x && T.eval x)
  | .leaf b, acc => by
      cases b <;> simp [toDNF, DNF.eval, DTree.eval]
  | .node i t₀ t₁, acc => by
      simp only [toDNF]
      split_ifs with h0 h1
      · rw [eval_toDNF x t₀ acc]
        cases ha : Term.eval acc x
        · rfl
        · have := term_eval_mem ha h0
          simp [DTree.eval, this]
      · rw [eval_toDNF x t₁ acc]
        cases ha : Term.eval acc x
        · rfl
        · have := term_eval_mem ha h1
          simp [DTree.eval, this]
      · rw [DNF.eval_append, eval_toDNF x t₀, eval_toDNF x t₁, term_eval_cons, term_eval_cons]
        simp only [DTree.eval]
        cases x i <;> simp

theorem isKDNF_mono {k k' : ℕ} {F : DNF n} (h : IsKDNF k F) (hk : k ≤ k') : IsKDNF k' F :=
  fun C hC => ⟨le_trans (h C hC).1 hk, (h C hC).2⟩

theorem isKDNF_append {k : ℕ} {F G : DNF n} (hF : IsKDNF k F) (hG : IsKDNF k G) :
    IsKDNF k (F ++ G) := by
  intro C hC
  rcases List.mem_append.1 hC with h | h
  · exact hF C h
  · exact hG C h

theorem isKDNF_toDNF :
    ∀ (T : DTree n) (acc : Term n), acc.WellFormed → IsKDNF (acc.length + T.depth) (toDNF T acc)
  | .leaf b, acc, hacc => by
      intro C hC
      cases b
      · simp [toDNF] at hC
      · simp only [toDNF, ite_true, List.mem_singleton] at hC
        subst hC
        exact ⟨by simp, hacc⟩
  | .node i t₀ t₁, acc, hacc => by
      simp only [toDNF]
      have hd₀ : t₀.depth ≤ (DTree.node i t₀ t₁).depth := by simp only [DTree.depth]; omega
      have hd₁ : t₁.depth ≤ (DTree.node i t₀ t₁).depth := by simp only [DTree.depth]; omega
      split_ifs with h0 h1
      · exact isKDNF_mono (isKDNF_toDNF t₀ acc hacc) (by omega)
      · exact isKDNF_mono (isKDNF_toDNF t₁ acc hacc) (by omega)
      · have hi : i ∉ acc.map Prod.fst := by
          intro hi
          obtain ⟨⟨j, b⟩, hm, hj⟩ := List.mem_map.1 hi
          simp only at hj
          subst hj
          cases b
          · exact h0 hm
          · exact h1 hm
        have hw : ∀ b, Term.WellFormed ((i, b) :: acc) := fun b => by
          simp only [Term.WellFormed, List.map_cons, List.nodup_cons]
          exact ⟨hi, hacc⟩
        have hdn : (DTree.node i t₀ t₁).depth = max t₀.depth t₁.depth + 1 := rfl
        refine isKDNF_append (isKDNF_mono (isKDNF_toDNF t₀ _ (hw false)) ?_)
          (isKDNF_mono (isKDNF_toDNF t₁ _ (hw true)) ?_)
        · simp only [List.length_cons]; omega
        · simp only [List.length_cons]; omega

/-- A function with a decision tree of depth `≤ t` under `ρ`. -/
def HasDT (f : (Fin n → Bool) → Bool) (ρ : Restriction n) (t : ℕ) : Prop :=
  ∃ T : DTree n, T.depth ≤ t ∧ ∀ x, Extends ρ x → T.eval x = f x

theorem HasDT.mono {f : (Fin n → Bool) → Bool} {ρ ρ' : Restriction n} {t t' : ℕ}
    (h : HasDT f ρ t) (hr : Refines ρ ρ') (ht : t ≤ t') : HasDT f ρ' t' := by
  obtain ⟨T, hT, hc⟩ := h
  exact ⟨T, le_trans hT ht, fun x hx => hc x (hr.extends hx)⟩

theorem HasDT.not {f : (Fin n → Bool) → Bool} {ρ : Restriction n} {t : ℕ} (h : HasDT f ρ t) :
    HasDT (fun x => !f x) ρ t := by
  obtain ⟨T, hT, hc⟩ := h
  exact ⟨neg T, by rw [depth_neg]; exact hT, fun x hx => by rw [eval_neg, hc x hx]⟩

/-- A function with a decision tree of depth `≤ t` is a `t`-DNF. -/
theorem HasDT.dnf {f : (Fin n → Bool) → Bool} {ρ : Restriction n} {t : ℕ} (h : HasDT f ρ t) :
    ∃ F : DNF n, IsKDNF t F ∧ ∀ x, Extends ρ x → DNF.eval F x = f x := by
  obtain ⟨T, hT, hc⟩ := h
  refine ⟨toDNF T [], isKDNF_mono (isKDNF_toDNF T [] List.nodup_nil) (by simpa using hT),
    fun x hx => ?_⟩
  rw [eval_toDNF, hc x hx]
  simp [Term.eval]

/-- An `OR` of functions with decision trees of depth `≤ t` is a `t`-DNF. -/
theorem dnf_of_any {ρ : Restriction n} {t : ℕ} :
    ∀ fs : List ((Fin n → Bool) → Bool), (∀ f ∈ fs, HasDT f ρ t) →
      ∃ F : DNF n, IsKDNF t F ∧ ∀ x, Extends ρ x → DNF.eval F x = fs.any (fun f => f x)
  | [], _ => ⟨[], fun C hC => by simp at hC, fun x _ => by simp [DNF.eval]⟩
  | f :: fs, h => by
      obtain ⟨F₁, hF₁, hc₁⟩ := (h f (by simp)).dnf
      obtain ⟨F₂, hF₂, hc₂⟩ := dnf_of_any fs (fun g hg => h g (by simp [hg]))
      refine ⟨F₁ ++ F₂, isKDNF_append hF₁ hF₂, fun x hx => ?_⟩
      rw [DNF.eval_append, hc₁ x hx, hc₂ x hx, List.any_cons]

/-! ### Circuits as functions of `n` variables -/

/-- The function of `n` variables computed by a circuit. -/
def toFun (n : ℕ) (c : ACCirc) (x : Fin n → Bool) : Bool := c.eval (List.ofFn x)

theorem hasDT_lit (ρ : Restriction n) (i : ℕ) (b : Bool) :
    HasDT (toFun n (.lit i b)) ρ 1 := by
  by_cases hi : i < n
  · refine ⟨.node ⟨i, hi⟩ (.leaf (false == b)) (.leaf (true == b)), by simp [DTree.depth],
      fun x _ => ?_⟩
    simp only [DTree.eval, toFun, ACCirc.eval_lit]
    have : (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    rw [this]
    cases x ⟨i, hi⟩ <;> rfl
  · refine ⟨.leaf (false == b), by simp [DTree.depth], fun x _ => ?_⟩
    simp only [DTree.eval, toFun, ACCirc.eval_lit]
    rw [List.getD_eq_default _ _ (by simpa using hi)]

theorem hasDT_const (ρ : Restriction n) (b : Bool) : HasDT (toFun n (.const b)) ρ 1 :=
  ⟨.leaf b, by simp [DTree.depth], fun x _ => by simp [DTree.eval, toFun]⟩

/-! ### Subcircuits -/

mutual
/-- All subcircuits of a circuit (with multiplicity), the circuit itself first. -/
def subs : ACCirc → List ACCirc
  | .lit i b => [.lit i b]
  | .const b => [.const b]
  | .not c => .not c :: subs c
  | .and cs => .and cs :: subsL cs
  | .or cs => .or cs :: subsL cs
/-- The subcircuits of a list of circuits. -/
def subsL : List ACCirc → List ACCirc
  | [] => []
  | c :: cs => subs c ++ subsL cs
end

theorem mem_subsL {c : ACCirc} : ∀ {cs : List ACCirc}, c ∈ subsL cs ↔ ∃ d ∈ cs, c ∈ subs d
  | [] => by simp [subsL]
  | d :: cs => by
      rw [subsL, List.mem_append, mem_subsL]
      simp

theorem length_subs : ∀ c : ACCirc, (subs c).length = c.size := by
  have hL : ∀ cs : List ACCirc, (∀ c ∈ cs, (subs c).length = c.size) →
      (subsL cs).length = (cs.map ACCirc.size).sum := by
    intro cs
    induction cs with
    | nil => intro _; simp [subsL]
    | cons c cs ih =>
        intro h
        rw [subsL, List.length_append, h c (by simp), ih fun d hd => h d (by simp [hd])]
        simp
  refine ACCirc.induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b; simp [subs]
  · intro b; simp [subs]
  · intro c ih; simp [subs, ih]
  · intro cs ih; simp only [subs, List.length_cons, hL cs ih, ACCirc.size_and]
  · intro cs ih; simp only [subs, List.length_cons, hL cs ih, ACCirc.size_or]

theorem mem_subs_self (c : ACCirc) : c ∈ subs c := by
  cases c <;> simp [subs]

theorem subs_trans : ∀ C : ACCirc, ∀ c ∈ subs C, ∀ d ∈ subs c, d ∈ subs C := by
  refine ACCirc.induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b c hc d hd
    simp only [subs, List.mem_singleton] at hc
    subst hc; exact hd
  · intro b c hc d hd
    simp only [subs, List.mem_singleton] at hc
    subst hc; exact hd
  · intro C ih c hc d hd
    simp only [subs, List.mem_cons] at hc ⊢
    rcases hc with rfl | hc
    · simpa [subs] using hd
    · exact Or.inr (ih c hc d hd)
  · intro cs ih c hc d hd
    simp only [subs, List.mem_cons] at hc ⊢
    rcases hc with rfl | hc
    · simpa [subs] using hd
    · obtain ⟨e, he, hce⟩ := mem_subsL.1 hc
      exact Or.inr (mem_subsL.2 ⟨e, he, ih e he c hce d hd⟩)
  · intro cs ih c hc d hd
    simp only [subs, List.mem_cons] at hc ⊢
    rcases hc with rfl | hc
    · simpa [subs] using hd
    · obtain ⟨e, he, hce⟩ := mem_subsL.1 hc
      exact Or.inr (mem_subsL.2 ⟨e, he, ih e he c hce d hd⟩)

theorem child_mem_subs_and {cs : List ACCirc} {d : ACCirc} (hd : d ∈ cs) :
    d ∈ subs (.and cs) := by
  simp only [subs, List.mem_cons]
  exact Or.inr (mem_subsL.2 ⟨d, hd, mem_subs_self d⟩)

theorem child_mem_subs_or {cs : List ACCirc} {d : ACCirc} (hd : d ∈ cs) :
    d ∈ subs (.or cs) := by
  simp only [subs, List.mem_cons]
  exact Or.inr (mem_subsL.2 ⟨d, hd, mem_subs_self d⟩)

theorem noNot_of_mem_subs : ∀ C : ACCirc, C.NoNot → ∀ c ∈ subs C, c.NoNot := by
  refine ACCirc.induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b _ c hc
    simp only [subs, List.mem_singleton] at hc
    subst hc; trivial
  · intro b _ c hc
    simp only [subs, List.mem_singleton] at hc
    subst hc; trivial
  · intro C _ hC
    exact absurd hC (by simp [ACCirc.NoNot])
  · intro cs ih hC c hc
    simp only [subs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hC
    · obtain ⟨e, he, hce⟩ := mem_subsL.1 hc
      simp only [ACCirc.NoNot] at hC
      exact ih e he (hC e he) c hce
  · intro cs ih hC c hc
    simp only [subs, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hC
    · obtain ⟨e, he, hce⟩ := mem_subsL.1 hc
      simp only [ACCirc.NoNot] at hC
      exact ih e he (hC e he) c hce

/-! ### The invariant of the switching rounds -/

/-- Every subcircuit of `C` of depth `≤ j` has a decision tree of depth `≤ t` under `ρ`. -/
def Good (C : ACCirc) (ρ : Restriction n) (j t : ℕ) : Prop :=
  ∀ c ∈ subs C, c.depth ≤ j → HasDT (toFun n c) ρ t

theorem good_zero (C : ACCirc) (hC : C.NoNot) (ρ : Restriction n) : Good C ρ 0 1 := by
  intro c hc hd
  have hn := noNot_of_mem_subs C hC c hc
  cases c with
  | lit i b => exact hasDT_lit ρ i b
  | const b => exact hasDT_const ρ b
  | not c => exact absurd hn (by simp [ACCirc.NoNot])
  | and cs => simp at hd
  | or cs => simp at hd

/-- A subcircuit of depth `≤ j + 1` is, under `ρ`, a `t`-DNF or the negation of one. -/
theorem exists_dnf_of_good {C : ACCirc} (hC : C.NoNot) {ρ : Restriction n} {j t : ℕ}
    (hg : Good C ρ j t) {c : ACCirc} (hc : c ∈ subs C) (hd : c.depth ≤ j + 1) :
    ∃ (F : DNF n) (b : Bool), IsKDNF t F ∧ ∀ x, Extends ρ x → toFun n c x = (DNF.eval F x != b) := by
  by_cases hj : c.depth ≤ j
  · obtain ⟨F, hF, hc'⟩ := (hg c hc hj).dnf
    exact ⟨F, false, hF, fun x hx => by rw [hc' x hx]; simp⟩
  have hn := noNot_of_mem_subs C hC c hc
  cases c with
  | lit i b => simp at hj
  | const b => simp at hj
  | not c => exact absurd hn (by simp [ACCirc.NoNot])
  | and cs =>
      have hch : ∀ d ∈ cs, HasDT (toFun n d) ρ t := fun d hdc =>
        hg d (subs_trans C _ hc d (child_mem_subs_and hdc))
          (by have := ACCirc.le_lmax ACCirc.depth hdc; simp at hd; omega)
      obtain ⟨F, hF, hcF⟩ := dnf_of_any (cs.map fun d x => !toFun n d x)
        (by
          intro f hf
          obtain ⟨d, hdc, rfl⟩ := List.mem_map.1 hf
          exact (hch d hdc).not)
      refine ⟨F, true, hF, fun x hx => ?_⟩
      rw [hcF x hx]
      simp only [toFun, ACCirc.eval_and, List.any_map, Function.comp_def]
      rw [ACCirc.any_not_eq]
      cases (cs.all fun c => c.eval (List.ofFn x)) <;> rfl
  | or cs =>
      have hch : ∀ d ∈ cs, HasDT (toFun n d) ρ t := fun d hdc =>
        hg d (subs_trans C _ hc d (child_mem_subs_or hdc))
          (by have := ACCirc.le_lmax ACCirc.depth hdc; simp at hd; omega)
      obtain ⟨F, hF, hcF⟩ := dnf_of_any (cs.map fun d x => toFun n d x)
        (by
          intro f hf
          obtain ⟨d, hdc, rfl⟩ := List.mem_map.1 hf
          exact hch d hdc)
      refine ⟨F, false, hF, fun x hx => ?_⟩
      rw [hcF x hx]
      simp [toFun, List.any_map, Function.comp_def]

/-- From a good refinement: the canonical decision tree (or its negation) of the DNF. -/
theorem hasDT_of_cdt {f : (Fin n → Bool) → Bool} {ρ ρ' : Restriction n} {F : DNF n} {b : Bool}
    {s : ℕ} (hf : ∀ x, Extends ρ x → f x = (DNF.eval F x != b)) (hr : Refines ρ ρ')
    (hd : (cdt F ρ').depth < s) : HasDT f ρ' s := by
  refine ⟨if b then neg (cdt F ρ') else cdt F ρ', ?_, fun x hx => ?_⟩
  · split_ifs
    · rw [depth_neg]; omega
    · omega
  · rw [hf x (hr.extends hx)]
    have hc := cdt_computes F ρ' x hx
    cases b
    · simp [hc]
    · simp [eval_neg, hc]

open Classical in
/-- **One switching round.**  If every subcircuit of depth `≤ j` has a decision tree of depth
`≤ t` under `ρ`, then some refinement `ρ'` of `ρ` with `⌊m / (32 t)⌋` free variables (`m` those of
`ρ`) gives every subcircuit of depth `≤ j + 1` a decision tree of depth `≤ s`, provided the
circuit has fewer than `2^s` nodes. -/
theorem round {C : ACCirc} (hC : C.NoNot) {s t j : ℕ} (ht : 1 ≤ t) (hts : t ≤ s)
    (hsize : C.size < 2 ^ s) {ρ : Restriction n} (hg : Good C ρ j t) :
    ∃ ρ', Refines ρ ρ' ∧ (freeSet ρ').card = (freeSet ρ).card / (32 * t) ∧
      Good C ρ' (j + 1) s := by
  set ℓ := (freeSet ρ).card / (32 * t) with hℓ
  have hs : 1 ≤ s := le_trans ht hts
  let B : ACCirc → Finset (Restriction n) := fun c =>
    (RR ρ ℓ).filter (fun ρ' => c.depth ≤ j + 1 ∧ ¬ HasDT (toFun n c) ρ' s)
  have hB : ∀ c ∈ subs C, (B c).card * 2 ^ s ≤ (RR ρ ℓ).card := by
    intro c hc
    by_cases hd : c.depth ≤ j + 1
    · obtain ⟨F, b, hF, hcF⟩ := exists_dnf_of_good hC hg hc hd
      have hsub : B c ⊆ BadRel F ρ ℓ s := by
        intro ρ' hρ'
        simp only [B, mem_filter] at hρ'
        refine mem_filter.2 ⟨hρ'.1, ?_⟩
        by_contra hlt
        exact hρ'.2.2 (hasDT_of_cdt hcF (mem_RR.1 hρ'.1).1 (Nat.lt_of_not_le hlt))
      exact le_trans (Nat.mul_le_mul_right _ (card_le_card hsub))
        (switching_rel_half ht F (isKDNF_mono hF le_rfl) ρ hs)
    · have : B c = ∅ := by
        apply eq_empty_of_forall_notMem
        intro ρ' hρ'
        simp only [B, mem_filter] at hρ'
        exact hd hρ'.2.1
      rw [this]; simp
  let Bad := (subs C).toFinset.biUnion B
  have hpos : 0 < (RR ρ ℓ).card :=
    card_RR_pos ρ (by rw [hℓ]; exact Nat.div_le_self _ _)
  have hcard : Bad.card < (RR ρ ℓ).card := by
    have h1 : Bad.card * 2 ^ s ≤ (subs C).toFinset.card * (RR ρ ℓ).card := by
      calc Bad.card * 2 ^ s ≤ (∑ c ∈ (subs C).toFinset, (B c).card) * 2 ^ s :=
            Nat.mul_le_mul_right _ card_biUnion_le
        _ = ∑ c ∈ (subs C).toFinset, (B c).card * 2 ^ s := by rw [sum_mul]
        _ ≤ ∑ c ∈ (subs C).toFinset, (RR ρ ℓ).card :=
            sum_le_sum fun c hc => hB c (List.mem_toFinset.1 hc)
        _ = (subs C).toFinset.card * (RR ρ ℓ).card := by rw [sum_const, smul_eq_mul]
    have h2 : (subs C).toFinset.card ≤ C.size := by
      rw [← length_subs C]; exact List.toFinset_card_le _
    have h3 : Bad.card * 2 ^ s < 2 ^ s * (RR ρ ℓ).card :=
      lt_of_le_of_lt (le_trans h1 (Nat.mul_le_mul_right _ h2))
        (Nat.mul_lt_mul_of_pos_right hsize hpos)
    rw [mul_comm (2 ^ s)] at h3
    exact Nat.lt_of_mul_lt_mul_right h3
  obtain ⟨ρ', hρ'R, hρ'B⟩ := exists_mem_notMem_of_card_lt_card hcard
  refine ⟨ρ', (mem_RR.1 hρ'R).1, (mem_RR.1 hρ'R).2, fun c hc hd => ?_⟩
  by_contra hno
  exact hρ'B (mem_biUnion.2 ⟨c, List.mem_toFinset.2 hc, mem_filter.2 ⟨hρ'R, hd, hno⟩⟩)

/-- The rounds: after `r` rounds, `n` (if `r = 0`) or `⌊n / (32 (32 s)^(r-1))⌋` variables are
free and every subcircuit of depth `≤ r` has a decision tree of depth `≤ 1` (if `r = 0`) or `≤ s`. -/
theorem rounds {C : ACCirc} (hC : C.NoNot) {s : ℕ} (hs : 1 ≤ s) (hsize : C.size < 2 ^ s) :
    ∀ r : ℕ, ∃ ρ : Restriction n, Good C ρ r (if r = 0 then 1 else s) ∧
      (freeSet ρ).card = if r = 0 then n else n / (32 * (32 * s) ^ (r - 1))
  | 0 => ⟨fun _ => none, good_zero C hC _, by simp [freeSet]⟩
  | r + 1 => by
      obtain ⟨ρ, hg, hcard⟩ := rounds hC hs hsize r
      have ht : 1 ≤ (if r = 0 then 1 else s) := by split_ifs <;> omega
      have hts : (if r = 0 then 1 else s) ≤ s := by split_ifs <;> omega
      obtain ⟨ρ', -, hc', hg'⟩ := round hC ht hts hsize hg
      refine ⟨ρ', by simpa using hg', ?_⟩
      rw [hc', hcard]
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, Nat.add_sub_cancel]
      split_ifs with hr
      · subst hr; simp
      · rw [Nat.div_div_eq_div_mul]
        congr 1
        obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring

/-! ### Small-width DNFs do not compute parity -/

/-- Parity of an assignment. -/
def par (x : Fin n → Bool) : Bool := decide ((univ.filter fun j => x j = true).card % 2 = 1)

theorem par_flip (x : Fin n → Bool) (i : Fin n) : par (Function.update x i (!x i)) = !par x := by
  unfold par
  cases hx : x i
  · have : (univ.filter fun j => Function.update x i (!false) j = true) =
        insert i (univ.filter fun j => x j = true) := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this, card_insert_of_notMem (by simp [hx])]
    by_cases h : (univ.filter fun j => x j = true).card % 2 = 1 <;> simp [h] <;> omega
  · have hmem : i ∈ univ.filter fun j => x j = true := by simp [hx]
    have : (univ.filter fun j => Function.update x i (!true) j = true) =
        (univ.filter fun j => x j = true).erase i := by
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [this, card_erase_of_mem hmem]
    have hpos := card_pos.2 ⟨i, hmem⟩
    by_cases h : (univ.filter fun j => x j = true).card % 2 = 1 <;> simp [h] <;> omega

theorem extends_update {ρ : Restriction n} {x : Fin n → Bool} (hx : Extends ρ x) {i : Fin n}
    (hi : i ∈ freeSet ρ) (v : Bool) : Extends ρ (Function.update x i v) := by
  intro j b hj
  by_cases hji : j = i
  · subst hji
    simp [freeSet] at hi
    rw [hi] at hj; cases hj
  · rw [Function.update_of_ne hji]; exact hx j b hj

/-- **A `t`-DNF, or its negation, does not compute parity on more than `t` free variables.** -/
theorem dnf_not_parity {F : DNF n} {t : ℕ} (hF : IsKDNF t F) {ρ : Restriction n}
    (hm : t < (freeSet ρ).card) (b : Bool)
    (h : ∀ x, Extends ρ x → (DNF.eval F x != b) = par x) : False := by
  classical
  have hx0 : Extends ρ (fun i => (ρ i).getD false) := by
    intro i c hc; simp [hc]
  obtain ⟨i0, hi0⟩ : (freeSet ρ).Nonempty := card_pos.1 (by omega)
  -- some extension accepted by `F`
  obtain ⟨x, hx, hFx⟩ : ∃ x, Extends ρ x ∧ DNF.eval F x = true := by
    set x0 : Fin n → Bool := fun i => (ρ i).getD false
    by_cases h0 : DNF.eval F x0 = true
    · exact ⟨x0, hx0, h0⟩
    · refine ⟨Function.update x0 i0 (!x0 i0), extends_update hx0 hi0 _, ?_⟩
      have e1 := h _ (extends_update hx0 hi0 (!x0 i0))
      have e0 := h x0 hx0
      rw [par_flip, ← e0] at e1
      simp only [Bool.not_eq_true] at h0
      rw [h0] at e1
      cases b <;> simpa using e1
  obtain ⟨C, hCF, hCx⟩ : ∃ C ∈ F, Term.eval C x = true := by
    simpa [DNF.eval] using hFx
  -- a free variable outside the term
  obtain ⟨i, hi, hiC⟩ : ∃ i ∈ freeSet ρ, i ∉ (C.map Prod.fst).toFinset := by
    by_contra hcon
    have hsub : freeSet ρ ⊆ (C.map Prod.fst).toFinset := fun i hi => by
      by_contra h; exact hcon ⟨i, hi, h⟩
    have := card_le_card hsub
    have h2 := List.toFinset_card_le (C.map Prod.fst)
    rw [List.length_map] at h2
    have h3 := (hF C hCF).1
    omega
  set x' := Function.update x i (!x i)
  have hx' : Extends ρ x' := extends_update hx hi _
  have hCx' : Term.eval C x' = true := by
    simp only [Term.eval, List.all_eq_true, beq_iff_eq] at hCx ⊢
    intro l hl
    have hne : l.1 ≠ i := by
      intro he; apply hiC; rw [← he]; simp only [List.mem_toFinset, List.mem_map]; exact ⟨l, hl, rfl⟩
    rw [show x' l.1 = x l.1 from Function.update_of_ne hne _ _]; exact hCx l hl
  have hFx' : DNF.eval F x' = true := by
    simp only [DNF.eval, List.any_eq_true]; exact ⟨C, hCF, hCx'⟩
  have e1 := h x' hx'
  have e0 := h x hx
  rw [par_flip, ← e0, hFx, hFx'] at e1
  cases b <;> simp at e1

end Complexity.Parity

namespace Complexity

open Parity Switching Finset

/-- **Parity**: the word has an odd number of ones. -/
def Parity : Language := fun x => x.count true % 2 = 1

namespace Parity

theorem count_ofFn_true :
    ∀ (n : ℕ) (x : Fin n → Bool), (List.ofFn x).count true = (univ.filter fun j => x j = true).card
  | 0, x => by simp
  | n + 1, x => by
      rw [List.ofFn_succ, List.count_cons, count_ofFn_true n, card_filter, card_filter,
        Fin.sum_univ_succ]
      cases x 0 <;> simp
      omega

theorem toFun_eq_par {C : ACCirc} {n : ℕ}
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) (x : Fin n → Bool) :
    toFun n C x = par x := by
  have h := hpar (List.ofFn x) (List.length_ofFn)
  unfold toFun par
  simp only [Complexity.Parity, count_ofFn_true] at h
  by_cases hc : (univ.filter fun j => x j = true).card % 2 = 1
  · rw [decide_eq_true hc]; exact h.1 hc
  · rw [decide_eq_false hc]
    cases he : C.eval (List.ofFn x)
    · rfl
    · exact absurd (h.2 he) hc

theorem log2_mono {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]; exact Nat.log_mono_right h

/-- The final step: after `d - 1` rounds the circuit is a DNF of small width, so few variables
can be free. -/
theorem final_bound {C : ACCirc} (hC : C.NoNot) {n d : ℕ} (hd : C.depth ≤ d)
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) {s : ℕ} (hs : 1 ≤ s)
    (hsize : C.size < 2 ^ s) :
    (if d - 1 = 0 then n else n / (32 * (32 * s) ^ (d - 1 - 1))) ≤
      if d - 1 = 0 then 1 else s := by
  obtain ⟨ρ, hg, hcard⟩ := rounds (n := n) hC hs hsize (d - 1)
  obtain ⟨F, b, hF, hcF⟩ := exists_dnf_of_good hC hg (mem_subs_self C) (by omega)
  rw [← hcard]
  by_contra hlt
  exact dnf_not_parity hF (Nat.lt_of_not_le hlt) b
    (fun x hx => by rw [← hcF x hx, toFun_eq_par hpar])

/-- Negation normal form of a circuit computing parity. -/
theorem nnf_spec {C : ACCirc} {n : ℕ}
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) :
    (ACCirc.nnf true C).NoNot ∧ (ACCirc.nnf true C).depth = C.depth ∧
      (ACCirc.nnf true C).size ≤ C.size ∧
      ∀ x : Word, x.length = n → (Parity x ↔ (ACCirc.nnf true C).eval x = true) := by
  refine ⟨ACCirc.noNot_nnf C true, ACCirc.depth_nnf C true, ACCirc.size_nnf C true,
    fun x hx => ?_⟩
  rw [hpar x hx, ACCirc.eval_nnf]
  cases C.eval x <;> simp

end Parity

/-- Circuits of depth at most one compute parity on at most one input. -/
theorem parity_depth_le_one {C : ACCirc} {n : ℕ} (hd : C.depth ≤ 1)
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) : n ≤ 1 := by
  obtain ⟨hC, hdep, -, hpar'⟩ := Parity.nnf_spec hpar
  have h := Parity.final_bound hC (d := 1) (by omega) hpar' (Nat.succ_pos _) Nat.lt_log2_self
  simpa using h

/-- **Håstad's bound.**  A circuit of depth `d ≥ 2` and size `S` that computes parity on `n`
inputs has `n < (32 (log₂ S + 2))^(d-1)`; equivalently `S ≥ 2^(n^(1/(d-1))/32 - 2)`. -/
theorem parity_circuit_bound {C : ACCirc} {n d : ℕ} (hd : C.depth ≤ d) (h2 : 2 ≤ d)
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) :
    n < (32 * (Nat.log2 C.size + 2)) ^ (d - 1) := by
  obtain ⟨hC, hdep, hsz, hpar'⟩ := Parity.nnf_spec hpar
  set C' := ACCirc.nnf true C
  set s := Nat.log2 C'.size + 1 with hsdef
  have h := Parity.final_bound hC (d := d) (s := s) (by omega) hpar' (by omega)
    (by rw [hsdef]; exact Nat.lt_log2_self)
  rw [ite_eq_right (by omega), ite_eq_right (by omega)] at h
  have hK : 0 < 32 * (32 * s) ^ (d - 1 - 1) := by positivity
  have h1 : n < (s + 1) * (32 * (32 * s) ^ (d - 1 - 1)) :=
    (Nat.div_lt_iff_lt_mul hK).1 (Nat.lt_succ_of_le h)
  have hs' : s + 1 ≤ Nat.log2 C.size + 2 := by
    have := Parity.log2_mono hsz; omega
  calc n < (s + 1) * (32 * (32 * s) ^ (d - 1 - 1)) := h1
    _ = 32 * (s + 1) * (32 * s) ^ (d - 1 - 1) := by ring
    _ ≤ 32 * (s + 1) * (32 * (s + 1)) ^ (d - 1 - 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = (32 * (s + 1)) ^ (d - 1) := by
        rw [← pow_succ']; congr 1; omega
    _ ≤ (32 * (Nat.log2 C.size + 2)) ^ (d - 1) := Nat.pow_le_pow_left (by omega) _

theorem ACCirc.size_pos (C : ACCirc) : 0 < C.size := by
  cases C <;> simp

/-- **Håstad's bound, real form**: `log₂ S > n^(1/(d-1)) / 32 - 2`. -/
theorem parity_log_size_lower_bound {C : ACCirc} {n d : ℕ} (hd : C.depth ≤ d) (h2 : 2 ≤ d)
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) :
    (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 32 - 2 < Nat.log2 C.size := by
  have h := parity_circuit_bound hd h2 hpar
  set X : ℝ := 32 * ((Nat.log2 C.size : ℝ) + 2)
  have hX : 0 ≤ X := by positivity
  have hd1 : d - 1 ≠ 0 := by omega
  have hlt : (n : ℝ) < X ^ (d - 1) := by
    have : ((n : ℕ) : ℝ) < (((32 * (Nat.log2 C.size + 2)) ^ (d - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    simpa [X] using this
  have hroot : (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) < X := by
    have := Real.rpow_lt_rpow (by positivity) hlt (by positivity : (0:ℝ) < ((d - 1 : ℕ) : ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast hX hd1] at this
  simp only [X] at hroot
  linarith

/-- **Håstad's bound, exponential form**: `S > 2^(n^(1/(d-1)) / 32 - 2)`. -/
theorem parity_size_lower_bound {C : ACCirc} {n d : ℕ} (hd : C.depth ≤ d) (h2 : 2 ≤ d)
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 32 - 2) < C.size := by
  have h := parity_log_size_lower_bound hd h2 hpar
  calc (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 32 - 2) < (2 : ℝ) ^ ((Nat.log2 C.size : ℕ) : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h
    _ = ((2 ^ Nat.log2 C.size : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; rfl
    _ ≤ C.size := by
        exact_mod_cast Nat.log2_self_le (Nat.pos_iff_ne_zero.1 (ACCirc.size_pos C))

/-- Polynomials grow more slowly than `2^N`. -/
theorem exists_poly_lt_two_pow (c e : ℕ) : ∃ N : ℕ, 1 ≤ N ∧ (c * N) ^ e + 1 < 2 ^ N := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt e (r := (2 : ℝ)) (by norm_num)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / ((c : ℝ) ^ e + 1) by positivity))
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 ht
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  set N := max N0 1
  have h := hN0 N (le_max_left _ _)
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  have hc : (0 : ℝ) < (c : ℝ) ^ e + 1 := by positivity
  rw [div_lt_div_iff₀ h2 hc, one_mul] at h
  have hreal : (((c ^ e + 1) * N ^ e : ℕ) : ℝ) < ((2 ^ N : ℕ) : ℝ) := by
    push_cast; linarith
  have hnat : (c ^ e + 1) * N ^ e < 2 ^ N := by exact_mod_cast hreal
  have hN1 : 1 ≤ N ^ e := Nat.one_le_pow _ _ (by omega)
  calc (c * N) ^ e + 1 ≤ c ^ e * N ^ e + N ^ e := by rw [mul_pow]; omega
    _ = (c ^ e + 1) * N ^ e := by ring
    _ < 2 ^ N := hnat

/-- **Parity is not in `AC⁰`.** -/
theorem parity_not_AC0 : ¬ InAC0 Parity := by
  intro h
  obtain ⟨d, p, ⟨a, k, hp⟩, hC⟩ := h.exists_noNot
  set D := max d 2
  have key : ∀ n, n < (32 * (Nat.log2 (p n) + 2)) ^ (D - 1) := by
    intro n
    obtain ⟨C, -, hd, hs, hx⟩ := hC n
    exact lt_of_lt_of_le (parity_circuit_bound (le_trans hd (le_max_left _ _))
      (le_max_right _ _) hx) (Nat.pow_le_pow_left (by have := Parity.log2_mono hs; omega) _)
  set A := Nat.log2 a + 1
  obtain ⟨N, hN1, hN⟩ := exists_poly_lt_two_pow (32 * (A + k + 2)) (D - 1)
  have hn1 : 2 ^ N - 1 + 1 = 2 ^ N := Nat.sub_add_cancel (Nat.one_le_two_pow)
  have hpn : p (2 ^ N - 1) < 2 ^ (A + N * k) := by
    calc p (2 ^ N - 1) ≤ a * (2 ^ N - 1 + 1) ^ k := hp _
      _ = a * 2 ^ (N * k) := by rw [hn1, pow_mul]
      _ < 2 ^ A * 2 ^ (N * k) :=
          Nat.mul_lt_mul_of_pos_right Nat.lt_log2_self (by positivity)
      _ = 2 ^ (A + N * k) := (pow_add _ _ _).symm
  have hlog : Nat.log2 (p (2 ^ N - 1)) < A + N * k := by
    by_cases h0 : p (2 ^ N - 1) = 0
    · rw [h0]; simp [Nat.log2]; omega
    · rw [Nat.log2_eq_log_two]; exact Nat.log_lt_of_lt_pow h0 hpn
  have hle : 32 * (Nat.log2 (p (2 ^ N - 1)) + 2) ≤ 32 * (A + k + 2) * N := by
    have : A + N * k + 2 ≤ (A + k + 2) * N := by nlinarith
    nlinarith
  have := key (2 ^ N - 1)
  have := lt_of_lt_of_le this (Nat.pow_le_pow_left hle _)
  omega

end Complexity
