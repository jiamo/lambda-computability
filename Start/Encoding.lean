/-
Encoding/decoding of Lambda terms to/from natural numbers.
Core definitions extracted from Start/Basic.lean.
The primrec proof machinery remains in Basic.lean.
-/

import Start.Syntax
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Sqrt
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

------------------------------------------------------------------------
-- Encoding Lambda terms to ℕ
------------------------------------------------------------------------

/-- Encoding of Lambda terms to Nat using `Nat.pair`. -/
def Lambda.encode : Lambda → ℕ
  | Lambda.var n => Nat.pair 0 n
  | Lambda.app t₁ t₂ => Nat.pair 1 (Nat.pair (Lambda.encode t₁) (Lambda.encode t₂))
  | Lambda.lam t => Nat.pair 2 (Lambda.encode t)

------------------------------------------------------------------------
-- Termination lemmas for decode
------------------------------------------------------------------------

/-- A number is strictly smaller than any code `Nat.pair a x` built from it with a positive tag. -/
theorem Lambda.lt_pair_of_pos {a : ℕ} (ha : 0 < a) (x : ℕ) : x < Nat.pair a x := by
  unfold Nat.pair
  split_ifs <;> nlinarith

/-- A number is strictly smaller than the code `Nat.pair 1 x` built from it. -/
theorem Lambda.lt_pair_one (x : ℕ) : x < Nat.pair 1 x :=
  Lambda.lt_pair_of_pos one_pos x

/-- The left component of an application code is strictly smaller than the code itself. -/
theorem Lambda.left_lt_app_code (a b : ℕ) : a < Nat.pair 1 (Nat.pair a b) :=
  lt_of_le_of_lt (Nat.left_le_pair a b) (Lambda.lt_pair_one _)

/-- The right component of an application code is strictly smaller than the code itself. -/
theorem Lambda.right_lt_app_code (a b : ℕ) : b < Nat.pair 1 (Nat.pair a b) :=
  lt_of_le_of_lt (Nat.right_le_pair a b) (Lambda.lt_pair_one _)

theorem Lambda.decode_lt_1 {n m c₁ c₂ : ℕ} (h : n.unpair = (1, m)) (hm : m.unpair = (c₁, c₂)) :
    c₁ < n := by
  unfold Nat.unpair at h hm
  dsimp only at h hm
  split_ifs at h with h1
  · simp only [Prod.mk.injEq] at h
    obtain ⟨hn, hm_eq⟩ := h
    subst hm_eq
    rw [hn] at h1
    split_ifs at hm with h2 <;> simp only [Prod.mk.injEq] at hm <;>
      obtain ⟨hc, -⟩ := hm <;> subst hc
    · nlinarith [Nat.sub_add_cancel (Nat.sqrt_le n), Nat.sub_add_cancel (Nat.sqrt_le (Nat.sqrt n)),
        Nat.sqrt_le n, Nat.sqrt_le (Nat.sqrt n)]
    · exact lt_of_le_of_lt (Nat.sqrt_le_self _)
        (by nlinarith [Nat.sub_add_cancel (Nat.sqrt_le n)])
  · simp only [Prod.mk.injEq] at h
    obtain ⟨hs, hm_eq⟩ := h
    subst hm_eq
    rw [hs] at h1 hm
    simp only [Nat.mul_one] at h1 hm
    split_ifs at hm with h2 <;> simp only [Prod.mk.injEq] at hm <;>
      obtain ⟨hc, -⟩ := hm <;> subst hc
    · grind
    · rcases n with (_ | _ | _ | n) <;> simp_all +arith +decide [Nat.sqrt_lt]
      nlinarith

theorem Lambda.decode_lt_2 {n m c₁ c₂ : ℕ} (h : n.unpair = (1, m)) (hm : m.unpair = (c₁, c₂)) :
    c₂ < n := by
  unfold Nat.unpair at h hm
  dsimp only at h hm
  split_ifs at h with h1
  · simp only [Prod.mk.injEq] at h
    obtain ⟨hn, hm_eq⟩ := h
    subst hm_eq
    rw [hn] at h1
    split_ifs at hm with h2 <;> simp only [Prod.mk.injEq] at hm <;>
      obtain ⟨-, hc⟩ := hm <;> subst hc
    · nlinarith [Nat.sub_add_cancel (Nat.sqrt_le' n),
        Nat.sub_add_cancel (Nat.sqrt_le' (Nat.sqrt n))]
    · rw [tsub_tsub, tsub_lt_iff_left]
      · nlinarith only [Nat.sqrt_le n, Nat.sqrt_le (Nat.sqrt n), h1]
      · nlinarith [Nat.sub_add_cancel
          (show n.sqrt.sqrt * n.sqrt.sqrt ≤ n.sqrt from
            by nlinarith [Nat.sqrt_le n.sqrt])]
  · simp only [Prod.mk.injEq] at h
    obtain ⟨hs, hm_eq⟩ := h
    subst hm_eq
    rw [hs] at h1 hm
    simp only [Nat.mul_one] at h1 hm
    split_ifs at hm with h2 <;> simp only [Prod.mk.injEq] at hm <;>
      obtain ⟨-, hc⟩ := hm <;> subst hc
    · exact lt_of_le_of_lt (Nat.sqrt_le_self _) (by omega)
    · omega

theorem Lambda.decode_lt_3 {n m : ℕ} (h : n.unpair = (2, m)) : m < n := by
  unfold Nat.unpair at h
  dsimp only at h
  split_ifs at h with h1 <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨hl, hr⟩ := h <;> subst hr
  · rw [hl] at h1
    nlinarith [Nat.sub_add_cancel (Nat.sqrt_le' n)]
  · rw [hl] at h1 ⊢
    omega

------------------------------------------------------------------------
-- Decoding ℕ to Lambda terms
------------------------------------------------------------------------

/-- Decoding of Nat to Lambda terms using strong recursion. -/
def Lambda.decode (n : ℕ) : Option Lambda :=
  Nat.strongRecOn n (fun n ih =>
    match h : n.unpair with
    | (0, m) => some (Lambda.var m)
    | (1, m) =>
      match hm : m.unpair with
      | (c₁, c₂) =>
        have h₁ : c₁ < n := Lambda.decode_lt_1 h hm
        have h₂ : c₂ < n := Lambda.decode_lt_2 h hm
        match ih c₁ h₁, ih c₂ h₂ with
        | some t₁, some t₂ => some (Lambda.app t₁ t₂)
        | _, _ => none
    | (2, m) =>
      have h' : m < n := Lambda.decode_lt_3 h
      match ih m h' with
      | some t => some (Lambda.lam t)
      | _ => none
    | _ => none)

------------------------------------------------------------------------
-- Encodable instance
------------------------------------------------------------------------

instance : Encodable Lambda where
  encode := Lambda.encode
  decode := Lambda.decode
  encodek := by
    intro a
    induction a with
    | var n =>
        simp only [Lambda.encode]
        unfold Lambda.decode
        rw [Nat.strongRecOn_eq]
        aesop
    | app a a_1 ih ha =>
        unfold Lambda.encode
        unfold Lambda.decode
        dsimp only
        rw [Nat.strongRecOn_eq]
        simp +decide only [Nat.unpair_pair, Prod.mk.injEq, false_and, imp_self, implies_true]
        rw [Nat.unpair_pair]
        simp +decide only [Nat.unpair_pair]
        rw [show Nat.strongRecOn a.encode _ = Option.some a from ih,
          show Nat.strongRecOn a_1.encode _ = Option.some a_1 from ha]
    | lam t ih =>
        simp only [Lambda.decode, Lambda.encode] at *
        rw [Nat.strongRecOn_eq]
        simp +decide only [Nat.unpair_pair, Prod.mk.injEq, false_and, imp_self, implies_true]
        rw [Nat.unpair_pair]
        simp +decide [*]
