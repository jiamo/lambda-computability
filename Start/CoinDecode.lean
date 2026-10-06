/-
**Field elements from coin flips.**

The verifier of an interactive proof (`Start/InteractiveProof.lean`) has random *bits*; the
sum-check protocol (`Start/SumCheck.lean`) needs random elements of a field `ZMod p`.  The verifier
reads a block of `K` bits as a number in binary (least significant bit first) and reduces it modulo
`p` (`Complexity.decP`).  This is not exactly uniform, but every residue has at most
`2 ^ K / p + 1` preimages (`Complexity.fiber_le`), so counting over the coin words loses at most a
factor `(2 ^ K / p + 1) · p / 2 ^ K ≤ 1 + p / 2 ^ K` per block against counting over field elements
(`Complexity.sumL_blocks_le`), and over `n` blocks at most a factor `2` once `2 · n · p ≤ 2 ^ K`
(`Complexity.cntL_blocks_le`).

Main definitions:

* `Complexity.binV`, `Complexity.decP` — a block of bits as a number, and as a residue;
* `Complexity.blocks` — a coin word cut into blocks, each read as a field element.

Main results:

* `Complexity.fiber_le` — each residue is hit by at most `2 ^ K / p + 1` blocks of length `K`;
* `Complexity.sumL_blocks_le` — the transfer of a count over field elements to a count over coin
  words, with the factor `(2 ^ K / p + 1) ^ n`;
* `Complexity.cntL_blocks_le` — **the probability of an event over decoded coin words is at most
  twice its probability over field elements**, once `2 · n · p ≤ 2 ^ K`.
-/

import Start.CountProb

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- A bit as a number. -/
def bitV (b : Bool) : ℕ := if b then 1 else 0

theorem bitV_le (b : Bool) : bitV b ≤ 1 := by cases b <;> simp [bitV]

/-- A word as a number in binary, least significant bit first. -/
def binV : List Bool → ℕ
  | [] => 0
  | b :: w => bitV b + 2 * binV w

/-- A word as a residue modulo `p`, computed bit by bit from the most significant end — the shape
of a bounded recursion on notation. -/
def decP (p : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: w => (bitV b + 2 * decP p w) % p

theorem decP_eq (p : ℕ) : ∀ w : List Bool, decP p w = binV w % p
  | [] => by simp [decP, binV]
  | b :: w => by
      rw [decP, binV, decP_eq p w, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        ← Nat.add_mod]

theorem decP_lt {p : ℕ} (hp : 0 < p) (w : List Bool) : decP p w < p := by
  rw [decP_eq]; exact Nat.mod_lt _ hp

/-! ### Sums over blocks -/

theorem sum_range_two_mul (g : ℕ → ℕ) (m : ℕ) :
    ∑ n ∈ Finset.range (2 * m), g n = ∑ n ∈ Finset.range m, (g (2 * n) + g (1 + 2 * n)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ]
      ring_nf

/-- A sum over the words of length `K` of a function of their binary value is a sum over the
numbers below `2 ^ K`. -/
theorem sumL_binV (K : ℕ) : ∀ g : ℕ → ℕ,
    sumL K (fun w => g (binV w)) = ∑ n ∈ Finset.range (2 ^ K), g n := by
  induction K with
  | zero => intro g; simp [binV]
  | succ K ih =>
      intro g
      rw [sumL_succ]
      simp only [binV]
      rw [Fintype.sum_bool, ih (fun n => g (bitV true + 2 * n)),
        ih (fun n => g (bitV false + 2 * n)), pow_succ', sum_range_two_mul,
        Finset.sum_add_distrib]
      simp [bitV, add_comm]

/-- **The fibres of the decoding**: at most `2 ^ K / p + 1` words of length `K` decode to a given
residue. -/
theorem fiber_le (p K y : ℕ) :
    sumL K (fun w => if decP p w = y then 1 else 0) ≤ 2 ^ K / p + 1 := by
  simp only [decP_eq]
  rw [sumL_binV K (fun n => if n % p = y then 1 else 0), Finset.sum_boole]
  simp only [Nat.cast_id]
  calc ((Finset.range (2 ^ K)).filter (fun n => n % p = y)).card
      ≤ (Finset.range (2 ^ K / p + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun n => n / p) ?_ ?_
        · intro n hn
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.le)
        · intro n hn m hm hnm
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hn hm
          simp only at hnm
          rw [← Nat.div_add_mod n p, ← Nat.div_add_mod m p, hnm, hn.2, hm.2]
    _ = 2 ^ K / p + 1 := Finset.card_range _

/-! ### Transfer from field elements to coin words -/

/-- A word cut into `n` blocks of `K` bits, each decoded to a residue modulo `p`. -/
def blocks (p K : ℕ) : ℕ → List Bool → List ℕ
  | 0, _ => []
  | n + 1, r => decP p (r.take K) :: blocks p K n (r.drop K)

@[simp] theorem length_blocks (p K n : ℕ) (r : List Bool) : (blocks p K n r).length = n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => simp [blocks, ih]

theorem sumL_finset_sum {α ι : Type*} [Fintype α] (s : Finset ι) (n : ℕ) (f : ι → List α → ℕ) :
    sumL n (fun ρ => ∑ i ∈ s, f i ρ) = ∑ i ∈ s, sumL n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sumL_const (α := α) n 0
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [sumL_add, ih]

/-- A sum of `h (f w)` over the words of length `K` is a sum over the values, weighted by the
sizes of the fibres. -/
theorem sumL_comp_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (K : ℕ)
    (f : List α → β) (h : β → ℕ) :
    sumL K (fun w => h (f w)) = ∑ y : β, h y * sumL K (fun w => if f w = y then 1 else 0) := by
  have : (fun w => h (f w)) = fun w => ∑ y : β, h y * (if f w = y then 1 else 0) := by
    funext w
    rw [Finset.sum_eq_single (f w)]
    · simp
    · intro y _ hy; simp [Ne.symm hy]
    · simp
  rw [this, sumL_finset_sum]
  exact Finset.sum_congr rfl fun y _ => sumL_mul_left _ _ _

/-- **Transfer**: a sum over coin words of a function of their decoded blocks is at most
`c ^ n` times the corresponding sum over lists of `n` field elements, `c` the bound on the fibres
of the decoding of a block. -/
theorem sumL_blocks_le {p : ℕ} [NeZero p] (hp : 0 < p) (K : ℕ) :
    ∀ (n : ℕ) (g : List (ZMod p) → ℕ),
      sumL (n * K) (fun r => g ((blocks p K n r).map (fun k => (k : ZMod p)))) ≤
        (2 ^ K / p + 1) ^ n * sumL n g := by
  intro n
  induction n with
  | zero => intro g; simp [blocks]
  | succ n ih =>
      intro g
      rw [show (n + 1) * K = K + n * K by ring, sumL_append]
      have step : ∀ w : List Bool, w.length = K →
          sumL (n * K) (fun r => g ((blocks p K (n + 1) (w ++ r)).map (fun k => (k : ZMod p)))) ≤
            (2 ^ K / p + 1) ^ n * sumL n (fun ρ => g ((decP p w : ZMod p) :: ρ)) := by
        intro w hw
        have := ih (fun ρ => g ((decP p w : ZMod p) :: ρ))
        simp only [blocks, List.take_left' hw, List.drop_left' hw]
        exact this
      calc sumL K (fun w => sumL (n * K)
              (fun r => g ((blocks p K (n + 1) (w ++ r)).map (fun k => (k : ZMod p)))))
          ≤ sumL K (fun w => (2 ^ K / p + 1) ^ n *
              sumL n (fun ρ => g ((decP p w : ZMod p) :: ρ))) := sumL_le_of_length step
        _ = (2 ^ K / p + 1) ^ n * sumL K (fun w => sumL n (fun ρ => g ((decP p w : ZMod p) :: ρ))) :=
            sumL_mul_left _ _ _
        _ ≤ (2 ^ K / p + 1) ^ n * ((2 ^ K / p + 1) * sumL (n + 1) g) := by
            refine Nat.mul_le_mul_left _ ?_
            rw [sumL_comp_fiber K (fun w => (decP p w : ZMod p))
              (fun y => sumL n (fun ρ => g (y :: ρ))), sumL_succ, Finset.mul_sum]
            refine Finset.sum_le_sum fun y _ => ?_
            rw [mul_comm]
            refine Nat.mul_le_mul_right _ ?_
            calc sumL K (fun w => if (decP p w : ZMod p) = y then 1 else 0)
                = sumL K (fun w => if decP p w = y.val then 1 else 0) := by
                  refine sumL_congr fun w _ => ?_
                  congr 1
                  apply propext
                  constructor
                  · intro h; rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt (decP_lt hp w)]
                  · intro h; rw [h, ZMod.natCast_zmod_val]
              _ ≤ 2 ^ K / p + 1 := fiber_le p K y.val
        _ = (2 ^ K / p + 1) ^ (n + 1) * sumL (n + 1) g := by ring

/-! ### The bias -/

theorem one_add_pow_le (x : ℚ) (hx : 0 ≤ x) : ∀ n : ℕ, n * x < 1 → (1 + x) ^ n * (1 - n * x) ≤ 1
  | 0, _ => by simp
  | n + 1, h => by
      have ih := one_add_pow_le x hx n (by push_cast at h; nlinarith)
      push_cast at h ⊢
      have h1 : 0 ≤ 1 - n * x := by nlinarith
      have h2 : (1 + x) * (1 - (n + 1) * x) ≤ 1 - n * x := by nlinarith [sq_nonneg x]
      calc (1 + x) ^ (n + 1) * (1 - (n + 1) * x) = (1 + x) ^ n * ((1 + x) * (1 - (n + 1) * x)) := by
            ring
        _ ≤ (1 + x) ^ n * (1 - n * x) := by gcongr
        _ ≤ 1 := ih

/-- `(1 + x) ^ n ≤ 2` when `n · x ≤ 1 / 2`. -/
theorem one_add_pow_le_two (x : ℚ) (hx : 0 ≤ x) (n : ℕ) (h : n * x ≤ 1 / 2) : (1 + x) ^ n ≤ 2 := by
  have := one_add_pow_le x hx n (by linarith)
  have hp : 0 < (1 + x) ^ n := by positivity
  nlinarith

/-- **Coins against field elements**: the probability of an event of `n` field elements, when the
elements are decoded from `n` blocks of `K` coin flips, is at most twice its probability under the
uniform distribution on the field, as soon as `2 · n · p ≤ 2 ^ K`. -/
theorem cntL_blocks_le {p : ℕ} [NeZero p] (hp : 0 < p) (K n : ℕ) (hK : 2 * n * p ≤ 2 ^ K)
    (E : List (ZMod p) → Bool) :
    (cntL (n * K) (fun r => E ((blocks p K n r).map (fun k => (k : ZMod p)))) : ℚ) / 2 ^ (n * K) ≤
      2 * ((cntL n E : ℚ) / (p : ℚ) ^ n) := by
  have h := sumL_blocks_le hp K n (fun ρ => if E ρ then 1 else 0)
  have hcnt : (cntL (n * K) (fun r => E ((blocks p K n r).map (fun k => (k : ZMod p)))) : ℚ) ≤
      ((2 ^ K / p + 1 : ℕ) : ℚ) ^ n * cntL n E := by
    unfold cntL
    have : sumL (n * K) (fun r => if E ((blocks p K n r).map (fun k => (k : ZMod p))) = true
        then 1 else 0) ≤ (2 ^ K / p + 1) ^ n * sumL n (fun ρ => if E ρ = true then 1 else 0) := h
    exact_mod_cast this
  have hc : ((2 ^ K / p + 1 : ℕ) : ℚ) * p ≤ 2 ^ K + p := by
    have : (2 ^ K / p) * p ≤ 2 ^ K := Nat.div_mul_le_self _ _
    have : ((2 ^ K / p : ℕ) : ℚ) * p ≤ 2 ^ K := by exact_mod_cast this
    push_cast; nlinarith
  have hpq : (0 : ℚ) < p := by exact_mod_cast hp
  have h2K : (0 : ℚ) < 2 ^ K := by positivity
  have hbias : (((2 ^ K / p + 1 : ℕ) : ℚ) * p / 2 ^ K) ^ n ≤ 2 := by
    calc (((2 ^ K / p + 1 : ℕ) : ℚ) * p / 2 ^ K) ^ n ≤ (1 + p / 2 ^ K) ^ n := by
          gcongr
          rw [div_le_iff₀ h2K]
          calc _ ≤ (2 : ℚ) ^ K + p := hc
            _ = _ := by field_simp
      _ ≤ 2 := by
          apply one_add_pow_le_two _ (by positivity)
          rw [mul_div_assoc', div_le_iff₀ h2K]
          have : ((2 * n * p : ℕ) : ℚ) ≤ ((2 ^ K : ℕ) : ℚ) := by exact_mod_cast hK
          push_cast at this
          linarith
  have hE : (0 : ℚ) ≤ cntL n E := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc (cntL (n * K) (fun r => E ((blocks p K n r).map (fun k => (k : ZMod p)))) : ℚ)
      ≤ ((2 ^ K / p + 1 : ℕ) : ℚ) ^ n * cntL n E := hcnt
    _ = (((2 ^ K / p + 1 : ℕ) : ℚ) * p / 2 ^ K) ^ n * ((cntL n E : ℚ) / (p : ℚ) ^ n) *
          2 ^ (n * K) := by
        rw [mul_comm n K, pow_mul, div_pow, mul_pow]
        field_simp
    _ ≤ 2 * ((cntL n E : ℚ) / (p : ℚ) ^ n) * 2 ^ (n * K) := by gcongr

end Complexity
