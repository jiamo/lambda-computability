/-
# Fixed length binary strings

A small dictionary between bit strings (`List Bool`, most significant bit first) and pairs
`(length, value)` of natural numbers.  It is used to run the interval arithmetic of the
Kraft–Chaitin machine construction (`Start/KCMachine.lean`) on natural numbers while the machine
itself is a partial function on bit strings.

* `BitStr.ofNat n m` — the `n`-bit binary representation of `m` (of `m % 2 ^ n`, if `m` is too
  big);
* `BitStr.toNat σ` — the value of the bit string `σ`;
* `BitStr.prefix_iff` — `σ` is a prefix of `τ` exactly when `|σ| ≤ |τ|` and the value of `σ` is
  the value of `τ` shifted right by `|τ| - |σ|` bits.  This turns the (dis)comparability of
  programs into arithmetic on dyadic intervals.
-/

import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BitStr

/-- The `n`-bit binary representation of `m`, most significant bit first. -/
def ofNat : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, m => ofNat n (m / 2) ++ [decide (m % 2 = 1)]

/-- The value of a bit string, read most significant bit first. -/
def toNat (σ : List Bool) : ℕ := σ.foldl (fun a b => 2 * a + (if b then 1 else 0)) 0

@[simp] theorem ofNat_zero (m : ℕ) : ofNat 0 m = [] := rfl

theorem ofNat_succ (n m : ℕ) : ofNat (n + 1) m = ofNat n (m / 2) ++ [decide (m % 2 = 1)] := rfl

@[simp] theorem length_ofNat (n m : ℕ) : (ofNat n m).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih => simp [ofNat_succ, ih]

@[simp] theorem toNat_nil : toNat [] = 0 := rfl

theorem toNat_foldl (σ : List Bool) (a : ℕ) :
    σ.foldl (fun a b => 2 * a + (if b then 1 else 0)) a = a * 2 ^ σ.length + toNat σ := by
  induction σ generalizing a with
  | nil => simp [toNat]
  | cons b σ ih =>
      simp only [List.foldl_cons, List.length_cons, toNat] at *
      rw [ih, ih (0 * 2 + (if b then 1 else 0))]
      ring

theorem toNat_append (σ u : List Bool) :
    toNat (σ ++ u) = toNat σ * 2 ^ u.length + toNat u := by
  simp only [toNat, List.foldl_append]
  exact toNat_foldl u _

@[simp] theorem toNat_singleton (b : Bool) : toNat [b] = if b then 1 else 0 := by
  cases b <;> rfl

theorem toNat_lt (σ : List Bool) : toNat σ < 2 ^ σ.length := by
  induction σ using List.reverseRecOn with
  | nil => simp
  | append_singleton σ b ih =>
      rw [toNat_append]
      simp only [List.length_append, List.length_singleton, toNat_singleton]
      have : (if b then 1 else 0) ≤ 1 := by cases b <;> simp
      have h2 : toNat σ + 1 ≤ 2 ^ σ.length := ih
      calc toNat σ * 2 ^ 1 + (if b then 1 else 0) ≤ toNat σ * 2 + 1 := by omega
        _ < 2 ^ σ.length * 2 := by omega
        _ = 2 ^ (σ.length + 1) := by ring

theorem toNat_ofNat (n m : ℕ) : toNat (ofNat n m) = m % 2 ^ n := by
  induction n generalizing m with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
      rw [ofNat_succ, toNat_append, ih]
      simp only [List.length_singleton, toNat_singleton, pow_one]
      have hm : m % 2 ^ (n + 1) = (m / 2) % 2 ^ n * 2 + m % 2 := by
        conv_lhs => rw [show (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n from by ring]
        rw [Nat.mod_mul]
        omega
      rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h, hm]

theorem ofNat_toNat (σ : List Bool) : ofNat σ.length (toNat σ) = σ := by
  induction σ using List.reverseRecOn with
  | nil => rfl
  | append_singleton σ b ih =>
      have hb : toNat σ * 2 ^ 1 + (if b then 1 else 0) = toNat σ * 2 + (if b then 1 else 0) := by
        ring
      simp only [List.length_append, List.length_singleton, ofNat_succ, toNat_append,
        toNat_singleton, hb]
      have hdiv : (toNat σ * 2 + (if b then 1 else 0)) / 2 = toNat σ := by
        cases b
        · simp
        · simp; omega
      rw [hdiv, ih]
      congr 1
      cases b <;> simp

theorem ofNat_inj {n a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) (h : ofNat n a = ofNat n b) :
    a = b := by
  have := congrArg toNat h
  rw [toNat_ofNat, toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem toNat_of_prefix {σ τ : List Bool} (h : σ <+: τ) :
    toNat σ = toNat τ / 2 ^ (τ.length - σ.length) := by
  obtain ⟨u, rfl⟩ := h
  have hlt := toNat_lt u
  simp only [List.length_append, toNat_append]
  rw [show σ.length + u.length - σ.length = u.length by omega,
    show toNat σ * 2 ^ u.length + toNat u = toNat u + 2 ^ u.length * toNat σ from by ring,
    Nat.add_mul_div_left _ _ (by positivity : 0 < 2 ^ u.length), Nat.div_eq_of_lt hlt]
  omega

theorem prefix_of_toNat {σ τ : List Bool} (hlen : σ.length ≤ τ.length)
    (h : toNat σ = toNat τ / 2 ^ (τ.length - σ.length)) : σ <+: τ := by
  refine ⟨τ.drop σ.length, ?_⟩
  have hsplit : τ.take σ.length ++ τ.drop σ.length = τ := List.take_append_drop _ _
  have hlen' : (τ.take σ.length).length = σ.length := by
    simp [Nat.min_eq_left hlen]
  have hval : toNat (τ.take σ.length) = toNat τ / 2 ^ (τ.length - σ.length) := by
    have := toNat_of_prefix (List.take_prefix σ.length τ)
    rwa [hlen'] at this
  have hpre : σ = τ.take σ.length := by
    calc σ = ofNat σ.length (toNat σ) := (ofNat_toNat σ).symm
      _ = ofNat (τ.take σ.length).length (toNat (τ.take σ.length)) := by
          rw [hlen', h, hval]
      _ = τ.take σ.length := ofNat_toNat _
  calc σ ++ τ.drop σ.length = τ.take σ.length ++ τ.drop σ.length := by rw [← hpre]
    _ = τ := hsplit

theorem length_le_of_prefix {σ τ : List Bool} (h : σ <+: τ) : σ.length ≤ τ.length :=
  h.length_le

/-- Prefixes, arithmetically: `σ` is a prefix of `τ` exactly when it is not longer and its value
is the value of `τ` shifted right. -/
theorem prefix_iff {σ τ : List Bool} :
    σ <+: τ ↔ σ.length ≤ τ.length ∧ toNat σ = toNat τ / 2 ^ (τ.length - σ.length) :=
  ⟨fun h => ⟨h.length_le, toNat_of_prefix h⟩, fun h => prefix_of_toNat h.1 h.2⟩

/-- The interval reading of prefixes: if `σ` is a prefix of `τ` then the dyadic interval of `τ`
is contained in that of `σ`. -/
theorem interval_subset_of_prefix {σ τ : List Bool} (h : σ <+: τ) :
    toNat σ * 2 ^ (τ.length - σ.length) ≤ toNat τ ∧
      toNat τ < (toNat σ + 1) * 2 ^ (τ.length - σ.length) := by
  have hval := toNat_of_prefix h
  have hpos : 0 < 2 ^ (τ.length - σ.length) := by positivity
  constructor
  · rw [hval]; exact Nat.div_mul_le_self _ _
  · rw [hval, add_mul, one_mul]
    have := Nat.div_add_mod (toNat τ) (2 ^ (τ.length - σ.length))
    have hmod : toNat τ % 2 ^ (τ.length - σ.length) < 2 ^ (τ.length - σ.length) :=
      Nat.mod_lt _ hpos
    nlinarith [this, hmod]

/-- Two bit strings whose dyadic intervals are disjoint (the interval of `σ` lies strictly to the
left of the interval of `τ`) are incomparable. -/
theorem not_prefix_of_lt {σ τ : List Bool}
    (h : (toNat σ + 1) * 2 ^ τ.length ≤ toNat τ * 2 ^ σ.length) :
    ¬ σ <+: τ := by
  intro hpre
  have hlen := hpre.length_le
  obtain ⟨-, hub⟩ := interval_subset_of_prefix hpre
  have hpow : 2 ^ σ.length * 2 ^ (τ.length - σ.length) = 2 ^ τ.length := by
    rw [← pow_add]; congr 1; omega
  have h1 : toNat τ * 2 ^ σ.length <
      (toNat σ + 1) * 2 ^ (τ.length - σ.length) * 2 ^ σ.length :=
    Nat.mul_lt_mul_of_lt_of_le hub (le_refl _) (by positivity)
  have h2 : (toNat σ + 1) * 2 ^ (τ.length - σ.length) * 2 ^ σ.length
      = (toNat σ + 1) * 2 ^ τ.length := by
    rw [mul_assoc, mul_comm (2 ^ (τ.length - σ.length)), hpow]
  omega

/-- The same conclusion for the reverse order of the two intervals. -/
theorem not_prefix_of_lt' {σ τ : List Bool}
    (h : (toNat σ + 1) * 2 ^ τ.length ≤ toNat τ * 2 ^ σ.length) :
    ¬ τ <+: σ := by
  intro hpre
  have hlen := hpre.length_le
  obtain ⟨hlb, -⟩ := interval_subset_of_prefix hpre
  have hpow : 2 ^ τ.length * 2 ^ (σ.length - τ.length) = 2 ^ σ.length := by
    rw [← pow_add]; congr 1; omega
  have h1 : toNat τ * 2 ^ (σ.length - τ.length) * 2 ^ τ.length ≤ toNat σ * 2 ^ τ.length :=
    Nat.mul_le_mul_right _ hlb
  have h2 : toNat τ * 2 ^ (σ.length - τ.length) * 2 ^ τ.length = toNat τ * 2 ^ σ.length := by
    rw [mul_assoc, mul_comm (2 ^ (σ.length - τ.length)), hpow]
  have h3 : 0 < 2 ^ τ.length := by positivity
  nlinarith [h, h1, h2, h3]

/-- `toNat` is primitive recursive. -/
theorem primrec_toNat : Primrec toNat := by
  have h2 : Primrec fun p : (List Bool) × (ℕ × Bool) => 2 * p.2.1 :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd)
  have h3 : Primrec fun p : (List Bool) × (ℕ × Bool) => (if p.2.2 then 1 else 0 : ℕ) :=
    (Primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.const 1)
      (Primrec.const 0)).of_eq fun p => by cases p.2.2 <;> simp
  exact Primrec.list_foldl (f := fun σ : List Bool => σ) (g := fun _ => (0 : ℕ))
    (h := fun (_ : List Bool) (p : ℕ × Bool) => 2 * p.1 + (if p.2 then 1 else 0))
    Primrec.id (Primrec.const 0) (Primrec.nat_add.comp h2 h3)

/-- Peeling the top bit off the `n + 1`-bit representation. -/
theorem ofNat_succ' (n m : ℕ) : ofNat (n + 1) m = decide ((m / 2 ^ n) % 2 = 1) :: ofNat n m := by
  induction n generalizing m with
  | zero => simp [ofNat_succ]
  | succ n ih =>
      rw [ofNat_succ (n + 1) m, ih (m / 2), ofNat_succ n m]
      simp [Nat.div_div_eq_div_mul, pow_succ, mul_comm]

/-- A tail-recursive reading of `BitStr.ofNat`, used to see that it is primitive recursive. -/
def ofNatAux : ℕ → ℕ → List Bool × ℕ
  | 0, m => ([], m)
  | n + 1, m =>
    (decide ((ofNatAux n m).2 % 2 = 1) :: (ofNatAux n m).1, (ofNatAux n m).2 / 2)

theorem ofNatAux_spec (n m : ℕ) : ofNatAux n m = (ofNat n m, m / 2 ^ n) := by
  induction n with
  | zero => simp [ofNatAux]
  | succ n ih =>
      rw [ofNatAux, ih]
      simp only []
      rw [ofNat_succ' n m, Nat.div_div_eq_div_mul, ← pow_succ]

theorem primrec_ofNatAux : Primrec₂ fun (m n : ℕ) => ofNatAux n m := by
  have hstep : Primrec₂ fun (_ : ℕ) (p : ℕ × (List Bool × ℕ)) =>
      ((decide (p.2.2 % 2 = 1) :: p.2.1, p.2.2 / 2) : List Bool × ℕ) := by
    have hrem : Primrec fun p : ℕ × (ℕ × (List Bool × ℕ)) => p.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hbits : Primrec fun p : ℕ × (ℕ × (List Bool × ℕ)) => p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hbit : Primrec fun p : ℕ × (ℕ × (List Bool × ℕ)) => decide (p.2.2.2 % 2 = 1) :=
      (Primrec.eq.comp (Primrec.nat_mod.comp hrem (Primrec.const 2)) (Primrec.const 1)).decide
    exact (Primrec.list_cons.comp hbit hbits).pair
      (Primrec.nat_div.comp hrem (Primrec.const 2))
  have hbase : Primrec fun m : ℕ => (([], m) : List Bool × ℕ) :=
    (Primrec.const []).pair Primrec.id
  refine (Primrec.nat_rec hbase hstep).of_eq fun m n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [ofNatAux, ← ih]

/-- `ofNat` is primitive recursive. -/
theorem primrec_ofNat : Primrec₂ ofNat :=
  (Primrec.fst.comp (primrec_ofNatAux.comp Primrec.snd Primrec.fst)).of_eq fun p => by
    rw [ofNatAux_spec]

/-- The prefix test as a `Bool`-valued arithmetic function: by `BitStr.prefix_iff` being a
prefix is a condition on lengths and values.  Unlike `decide (σ <+: τ)` this carries no list
recursion in its decidability instance, which keeps it cheap for the computability API. -/
def isPrefixB (σ τ : List Bool) : Bool :=
  decide (σ.length ≤ τ.length) && decide (toNat σ = toNat τ / 2 ^ (τ.length - σ.length))

@[simp] theorem isPrefixB_iff {σ τ : List Bool} : isPrefixB σ τ = true ↔ σ <+: τ := by
  rw [isPrefixB, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, ← prefix_iff]

/-- `BitStr.isPrefixB` is primitive recursive. -/
theorem primrec_isPrefixB : Primrec₂ isPrefixB := by
  have hlen1 : Primrec fun p : List Bool × List Bool => p.1.length :=
    Primrec.list_length.comp Primrec.fst
  have hlen2 : Primrec fun p : List Bool × List Bool => p.2.length :=
    Primrec.list_length.comp Primrec.snd
  have hA : Primrec fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length) :=
    (PrimrecRel.comp Primrec.nat_le hlen1 hlen2).decide
  have hB : Primrec fun p : List Bool × List Bool =>
      decide (toNat p.1 = toNat p.2 / 2 ^ (p.2.length - p.1.length)) :=
    (PrimrecRel.comp (Primrec.eq (α := ℕ)) (primrec_toNat.comp Primrec.fst)
      (Primrec.nat_div.comp (primrec_toNat.comp Primrec.snd)
        ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
          (Primrec.nat_sub.comp hlen2 hlen1)))).decide
  exact (Primrec.and.comp hA hB).of_eq fun p => rfl

/-- Testing whether one bit string is a prefix of another is primitive recursive: by
`BitStr.prefix_iff` it is an arithmetic condition on lengths and values. -/
theorem primrec_isPrefix : PrimrecPred fun p : List Bool × List Bool => p.1 <+: p.2 := by
  have hlen1 : Primrec fun p : List Bool × List Bool => p.1.length :=
    Primrec.list_length.comp Primrec.fst
  have hlen2 : Primrec fun p : List Bool × List Bool => p.2.length :=
    Primrec.list_length.comp Primrec.snd
  have hA : PrimrecPred fun p : List Bool × List Bool => p.1.length ≤ p.2.length :=
    PrimrecRel.comp Primrec.nat_le hlen1 hlen2
  have hB : PrimrecPred fun p : List Bool × List Bool =>
      toNat p.1 = toNat p.2 / 2 ^ (p.2.length - p.1.length) :=
    PrimrecRel.comp (Primrec.eq (α := ℕ)) (primrec_toNat.comp Primrec.fst)
      (Primrec.nat_div.comp (primrec_toNat.comp Primrec.snd)
        ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2)
          (Primrec.nat_sub.comp hlen2 hlen1)))
  exact (hA.and hB).of_eq fun p => by rw [prefix_iff]

end BitStr
