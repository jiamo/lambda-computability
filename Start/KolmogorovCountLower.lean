import Start.KolmogorovCount
import Start.KolmogorovPair

/-!
# Exponential lower bounds on the number of terms and of simple numbers

Task `M19-TERM-COUNT-LOWER`.

`Start/KolmogorovCount.lean` proves the upper bounds: at most `4^m` terms have size `≤ m`
(`Lambda.card_size_le`) and at most `4^m` numbers have complexity `≤ m` (`Lambda.card_kolm_le`).
This module proves matching exponential lower bounds with explicit bases.

* `Lambda.termCount` — a computable recursion for the number of terms of each exact size,
  `c(n+1) = 1 + c(n) + Σ_{a ≤ n} c(a) c(n-a)`, with `Lambda.termCount_le_card` showing that at
  least `termCount n` terms have size exactly `n`.
* `Lambda.card_size_eq_pow_le` — supermultiplicativity: `(#size = s)^j ≤ #(size ≤ (s+1) j + 1)`,
  through the injective chain `a₁ (a₂ (… (aⱼ 0)…))`.
* `Lambda.three_pow_le_card_size_le` — **at least `3^m` terms have size `≤ m`** for every
  `m ≥ 3400` (base `3`, against the upper base `4`).
* `Lambda.two_pow_le_card_kolm_le` — **at least `2^j` numbers have complexity `≤ 3 + 55 j`**
  (binary expansion with the realizers of `n ↦ 2n` and `n ↦ 2n + 1`, of sizes `36` and `54`), and
  its form `Lambda.two_pow_le_card_kolm_le_pow`: `2^m ≤ (#{s | kolm s ≤ m})^110` for every
  `m ≥ 114`, i.e. base `2^(1/110)`.
-/

set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Counting terms of each exact size
------------------------------------------------------------------------

/-- The table `[c 0, …, c n]` of the recursion `c 0 = 0`,
`c (n+1) = 1 + c n + Σ_{a ≤ n} c a · c (n - a)` (variable, abstraction, application). -/
def termTable : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
      let L := termTable n
      L ++ [1 + L.getD n 0 + ((List.range (n + 1)).map fun a => L.getD a 0 * L.getD (n - a) 0).sum]

/-- The number of lambda terms of size exactly `n` (proved below to be a lower bound for it). -/
def termCount (n : ℕ) : ℕ := (termTable n).getD n 0

theorem length_termTable (n : ℕ) : (termTable n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [termTable, ih]

theorem getD_termTable {n k : ℕ} (hk : k ≤ n) : (termTable n).getD k 0 = termCount k := by
  induction n with
  | zero => obtain rfl : k = 0 := by omega
            rfl
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 1) with h | h
      · rw [termTable]
        rw [List.getD_append _ _ _ _ (by rw [length_termTable]; exact h)]
        exact ih (by omega)
      · obtain rfl : k = n + 1 := by omega
        rfl

theorem sum_map_range_eq_finset_sum (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

theorem termCount_zero : termCount 0 = 0 := rfl

theorem termCount_succ (n : ℕ) :
    termCount (n + 1) =
      1 + termCount n + ∑ a ∈ Finset.range (n + 1), termCount a * termCount (n - a) := by
  have h : termCount (n + 1) = 1 + (termTable n).getD n 0 +
      ((List.range (n + 1)).map fun a =>
        (termTable n).getD a 0 * (termTable n).getD (n - a) 0).sum := by
    rw [termCount, termTable]
    rw [List.getD_append_right _ _ _ _ (by rw [length_termTable])]
    simp [length_termTable]
  rw [h, getD_termTable le_rfl, sum_map_range_eq_finset_sum]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := Finset.mem_range.1 ha
  rw [getD_termTable (by omega), getD_termTable (by omega)]

/-- The terms of size exactly `n`. -/
abbrev SizeEq (n : ℕ) := {t : Lambda // size t = n}

instance finite_sizeEq (n : ℕ) : Finite (SizeEq n) :=
  Finite.of_injective (fun t : SizeEq n => (⟨t.1, t.2.le⟩ : {t : Lambda // size t ≤ n}))
    (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- The three ways of building a term of size `n + 1`. -/
def buildSucc (n : ℕ) :
    Unit ⊕ SizeEq n ⊕ (Σ a : Fin (n + 1), SizeEq a × SizeEq (n - a)) → SizeEq (n + 1)
  | Sum.inl _ => ⟨var n, by simp⟩
  | Sum.inr (Sum.inl t) => ⟨lam t.1, by simp [t.2]⟩
  | Sum.inr (Sum.inr ⟨a, x, y⟩) => ⟨app x.1 y.1, by simp [x.2, y.2]; omega⟩

theorem buildSucc_injective (n : ℕ) : Function.Injective (buildSucc n) := by
  rintro (u | t | ⟨a, x, y⟩) (u' | t' | ⟨a', x', y'⟩) h <;>
    have h' := congrArg Subtype.val h <;>
    simp only [buildSucc, lam.injEq, app.injEq, reduceCtorEq] at h'
  · rfl
  · rw [Subtype.ext h']
  · obtain ⟨hx, hy⟩ := h'
    have ha : a = a' := Fin.ext (by rw [← x.2, ← x'.2, hx])
    subst ha
    obtain rfl : x = x' := Subtype.ext hx
    obtain rfl : y = y' := Subtype.ext hy
    rfl

/-- **At least `termCount n` terms have size exactly `n`.** -/
theorem termCount_le_card (n : ℕ) : termCount n ≤ Nat.card (SizeEq n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [termCount_zero]
    | succ n =>
      have hinj := Nat.card_le_card_of_injective _ (buildSucc_injective n)
      rw [Nat.card_sum, Nat.card_sum, Nat.card_sigma] at hinj
      simp only [Nat.card_unique, Nat.card_prod] at hinj
      rw [termCount_succ]
      have hA := ih n (by omega)
      have hB : ∑ a ∈ Finset.range (n + 1), termCount a * termCount (n - a) ≤
          ∑ a : Fin (n + 1), Nat.card (SizeEq a) * Nat.card (SizeEq (n - a)) := by
        rw [Fin.sum_univ_eq_sum_range (fun a => Nat.card (SizeEq a) * Nat.card (SizeEq (n - a)))]
        refine Finset.sum_le_sum fun a ha => ?_
        have ha' := Finset.mem_range.1 ha
        exact Nat.mul_le_mul (ih a (by omega)) (ih (n - a) (by omega))
      omega

------------------------------------------------------------------------
-- Supermultiplicativity: chains of terms
------------------------------------------------------------------------

/-- The chain `a₁ (a₂ (… (aⱼ 0)…))`. -/
def chain : List Lambda → Lambda
  | [] => var 0
  | a :: l => app a (chain l)

theorem chain_injective : Function.Injective chain := by
  intro l
  induction l with
  | nil => intro l' h; cases l' with
    | nil => rfl
    | cons a l' => simp [chain] at h
  | cons a l ih => intro l' h; cases l' with
    | nil => simp [chain] at h
    | cons a' l' =>
      obtain ⟨h1, h2⟩ := Lambda.app.inj h
      rw [h1, ih h2]

theorem size_chain (s : ℕ) (l : List Lambda) (hl : ∀ a ∈ l, size a = s) :
    size (chain l) = (s + 1) * l.length + 1 := by
  induction l with
  | nil => simp [chain]
  | cons a l ih =>
    simp only [chain, size_app, List.length_cons]
    rw [hl a (by simp), ih (fun b hb => hl b (by simp [hb]))]
    ring

/-- The chain of a `j`-tuple of terms of size `s`. -/
def chainOf (s j : ℕ) (v : Fin j → SizeEq s) : {t : Lambda // size t ≤ (s + 1) * j + 1} :=
  ⟨chain (List.ofFn fun i => (v i).1), by
    rw [size_chain s _ (by
      intro b hb
      simp only [List.mem_ofFn] at hb
      obtain ⟨i, rfl⟩ := hb
      exact (v i).2)]
    simp⟩

theorem chainOf_injective (s j : ℕ) : Function.Injective (chainOf s j) := by
  intro v w h
  have h1 := chain_injective (congrArg Subtype.val h)
  have h2 := List.ofFn_injective h1
  funext i
  exact Subtype.ext (congrFun h2 i)

/-- **Supermultiplicativity**: `(#size = s)^j ≤ #(size ≤ (s+1) j + 1)`. -/
theorem card_size_eq_pow_le (s j : ℕ) :
    Nat.card (SizeEq s) ^ j ≤ Nat.card {t : Lambda // size t ≤ (s + 1) * j + 1} := by
  have := Nat.card_le_card_of_injective _ (chainOf_injective s j)
  rwa [Nat.card_fun, Nat.card_fin] at this

theorem card_size_le_mono {a b : ℕ} (hab : a ≤ b) :
    Nat.card {t : Lambda // size t ≤ a} ≤ Nat.card {t : Lambda // size t ≤ b} :=
  Nat.card_le_card_of_injective (fun t => ⟨t.1, t.2.trans hab⟩)
    (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))

theorem termCount_hundred : 3 ^ 101 * 30 ≤ termCount 100 := by decide +kernel

/-- **At least `3^m` lambda terms have size at most `m`**, for every `m ≥ 3334`.  Together with
`Lambda.card_size_le` the number of terms of size `≤ m` lies between `3^m` and `4^m`. -/
theorem three_pow_le_card_size_le {m : ℕ} (hm : 3334 ≤ m) :
    3 ^ m ≤ Nat.card {t : Lambda // size t ≤ m} := by
  set j := (m - 1) / 101 with hj
  have hj33 : 33 ≤ j := by omega
  have hmj : m ≤ 101 * j + 101 := by omega
  have h1 : 3 ^ m ≤ 3 ^ 101 * (3 ^ 101) ^ j := by
    rw [← pow_mul, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 3 ^ 101 ≤ 30 ^ j :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hj33)
  have h3 : (3 ^ 101 * 30) ^ j ≤ termCount 100 ^ j := Nat.pow_le_pow_left termCount_hundred j
  have h4 : termCount 100 ^ j ≤ Nat.card {t : Lambda // size t ≤ m} :=
    ((Nat.pow_le_pow_left (termCount_le_card 100) j).trans (card_size_eq_pow_le 100 j)).trans
      (card_size_le_mono (by omega))
  calc 3 ^ m ≤ 3 ^ 101 * (3 ^ 101) ^ j := h1
    _ ≤ 30 ^ j * (3 ^ 101) ^ j := Nat.mul_le_mul_right _ h2
    _ = (3 ^ 101 * 30) ^ j := by rw [mul_pow, mul_comm]
    _ ≤ termCount 100 ^ j := h3
    _ ≤ _ := h4

------------------------------------------------------------------------
-- Numbers of small complexity: binary expansions
------------------------------------------------------------------------

theorem realizes_I : Realizes Lambda.I id := by
  refine ⟨fun s x => by simp [Lambda.I, Lambda.subst], fun n => ?_⟩
  have h := @Lambda.beta_reduces (Lambda.var 0) (Lambda.church n)
  simpa [Lambda.I, Lambda.subst] using h

/-- A doubling realizer, `n ↦ 2 n`. -/
def dblTerm : Lambda := mkApp2 Lambda.mult (mkConst 2) Lambda.I

/-- `n ↦ 2 n + 1`. -/
def dblOneTerm : Lambda := mkApp1 Lambda.succ dblTerm

theorem realizes_dblTerm : Realizes dblTerm (fun n => 2 * n) :=
  (Realizes.binop (op := (· * ·)) Lambda.mult_closed Lambda.mult_works (Realizes.const 2)
    realizes_I).of_eq fun _ => rfl

theorem realizes_dblOneTerm : Realizes dblOneTerm (fun n => 2 * n + 1) :=
  Realizes.comp1 Realizes.succ realizes_dblTerm

theorem size_dblTerm : size dblTerm = 36 := by decide

theorem size_dblOneTerm : size dblOneTerm = 54 := by decide

/-- Every number below `2^j` has complexity at most `3 + 55 j`. -/
theorem kolm_le_of_lt_two_pow (j : ℕ) : ∀ n < 2 ^ j, kolm n ≤ 3 + 55 * j := by
  induction j with
  | zero =>
      intro n hn
      obtain rfl : n = 0 := by simpa using hn
      simpa using kolm_le_church 0
  | succ j ih =>
      intro n hn
      have hq : n / 2 < 2 ^ j := by rw [pow_succ] at hn; omega
      have hq' := ih _ hq
      rcases Nat.even_or_odd' n with ⟨q, rfl | rfl⟩
      · have h := kolm_apply_le realizes_dblTerm q
        have : 2 * q / 2 = q := by omega
        rw [this] at hq'
        rw [size_dblTerm] at h
        omega
      · have h := kolm_apply_le realizes_dblOneTerm q
        have : (2 * q + 1) / 2 = q := by omega
        rw [this] at hq'
        rw [size_dblOneTerm] at h
        omega

/-- **At least `2^j` numbers have complexity at most `3 + 55 j`.** -/
theorem two_pow_le_card_kolm_le (j : ℕ) : 2 ^ j ≤ Nat.card {s : ℕ // kolm s ≤ 3 + 55 * j} := by
  have := Nat.card_le_card_of_injective
    (fun i : Fin (2 ^ j) =>
      (⟨i.1, kolm_le_of_lt_two_pow j i.1 i.2⟩ : {s : ℕ // kolm s ≤ 3 + 55 * j}))
    (fun a b h => Fin.ext (by simpa using congrArg Subtype.val h))
  simpa using this

theorem card_kolm_le_mono {a b : ℕ} (hab : a ≤ b) :
    Nat.card {s : ℕ // kolm s ≤ a} ≤ Nat.card {s : ℕ // kolm s ≤ b} :=
  Nat.card_le_card_of_injective (fun t => ⟨t.1, t.2.trans hab⟩)
    (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))

/-- **Exponentially many numbers of complexity `≤ m`, base `2^(1/110)`**: for every `m ≥ 114`,
`2^m ≤ (#{s | kolm s ≤ m})^110`.  Against the upper bound `Lambda.card_kolm_le` (base `4`). -/
theorem two_pow_le_card_kolm_le_pow {m : ℕ} (hm : 114 ≤ m) :
    2 ^ m ≤ Nat.card {s : ℕ // kolm s ≤ m} ^ 110 := by
  set j := (m - 3) / 55 with hj
  have hjm : 3 + 55 * j ≤ m := by omega
  have h1 : 2 ^ j ≤ Nat.card {s : ℕ // kolm s ≤ m} :=
    (two_pow_le_card_kolm_le j).trans (card_kolm_le_mono hjm)
  calc 2 ^ m ≤ 2 ^ (j * 110) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ j) ^ 110 := pow_mul _ _ _
    _ ≤ _ := Nat.pow_le_pow_left h1 110

end Lambda
