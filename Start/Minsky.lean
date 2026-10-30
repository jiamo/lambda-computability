/-
**Minsky's reduction of `k`-counter machines to two-counter machines** — task
`M25-COUNTER-MACHINE-UNDECIDABLE` (round 7, step B1).

A `k`-counter machine (`Minsky.KM`) has registers `r : ℕ → ℕ` and instructions
`inc i l` and `test i l₁ l₂` (if `r i = 0` go to `l₁`, else decrement `r i` and go to `l₂`).
It is compiled into a two-counter machine (`FsubGhelli.CM`) whose first counter holds the Gödel
number `godel k r = ∏_{i<k} pᵢ^{rᵢ}` and whose second counter is a scratch counter, zero between
simulated steps.  The bases are the Fermat numbers `pᵢ = 2^(2^i) + 1`, which are pairwise coprime
(Goldbach), so that `pᵢ ∣ godel k r ↔ 0 < rᵢ`.

* an increment of `rᵢ` multiplies the first counter by `pᵢ` (a loop moving it to the second
  counter `pᵢ` at a time, then a loop moving it back) — `Minsky.incF`;
* a test of `rᵢ` divides the first counter by `pᵢ` (a loop taking `pᵢ` from the first counter for
  each unit of the second); if the remainder is zero the quotient is moved back (decrement branch),
  otherwise the remainder and `pᵢ` times the quotient are restored (zero branch) — `Minsky.testF`.

* `Minsky.compile` — the two-counter program (blocks laid out at the offsets `Minsky.off`);
* `Minsky.sim_step` — **the step-correctness lemma**: one step of the `k`-counter machine is a
  non-empty run of the two-counter machine between the encoded configurations
  `(off pc, godel k r, 0)`;
* `Minsky.halts_iff` — **Minsky's theorem**: for a program using only registers `< k`,
  `KM.Halts M r ↔ CM.Halts (compile M) (godel k r) 0`;
* `Minsky.halts_iff_sub` — with `Start/FsubPierce.lean`, counter-machine halting reduces to
  subtyping in full F<:.
-/

import Start.FsubPierce
import Mathlib.NumberTheory.Fermat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

open FsubGhelli

/-! ### `k`-counter machines -/

/-- Instructions of a counter machine with registers indexed by `ℕ`. -/
inductive KInstr where
  /-- `inc i; goto l`. -/
  | inc : ℕ → ℕ → KInstr
  /-- `if r i = 0 then goto l₁ else (dec r i; goto l₂)`. -/
  | test : ℕ → ℕ → ℕ → KInstr

/-- The register of an instruction. -/
def KInstr.reg : KInstr → ℕ
  | .inc i _ => i
  | .test i _ _ => i

/-- A counter machine: a program; a label outside the program halts. -/
abbrev KM := List KInstr

/-- A configuration: label and registers. -/
structure KConf where
  /-- The label. -/
  pc : ℕ
  /-- The registers. -/
  r : ℕ → ℕ

/-- One step of a counter machine. -/
inductive KM.Step (M : KM) : KConf → KConf → Prop
  | inc {c : KConf} {i l : ℕ} : M[c.pc]? = some (.inc i l) →
      KM.Step M c ⟨l, Function.update c.r i (c.r i + 1)⟩
  | zero {c : KConf} {i l₁ l₂ : ℕ} : M[c.pc]? = some (.test i l₁ l₂) → c.r i = 0 →
      KM.Step M c ⟨l₁, c.r⟩
  | dec {c : KConf} {i l₁ l₂ v : ℕ} : M[c.pc]? = some (.test i l₁ l₂) → c.r i = v + 1 →
      KM.Step M c ⟨l₂, Function.update c.r i v⟩

/-- The machine halts from the configuration `c`. -/
def KM.HaltsFrom (M : KM) (c : KConf) : Prop :=
  ∃ c', Relation.ReflTransGen (KM.Step M) c c' ∧ M.length ≤ c'.pc

/-- The machine halts from label `0` with registers `r`. -/
def KM.Halts (M : KM) (r : ℕ → ℕ) : Prop := KM.HaltsFrom M ⟨0, r⟩

theorem KM.progress {M : KM} {c : KConf} (h : c.pc < M.length) : ∃ c', KM.Step M c c' := by
  obtain ⟨i, hi⟩ : ∃ i, M[c.pc]? = some i := ⟨M[c.pc], List.getElem?_eq_getElem h⟩
  cases i with
  | inc i l => exact ⟨_, KM.Step.inc hi⟩
  | test i l₁ l₂ =>
      rcases Nat.eq_zero_or_eq_succ_pred (c.r i) with h0 | h0
      · exact ⟨_, KM.Step.zero hi h0⟩
      · exact ⟨_, KM.Step.dec hi h0⟩

/-! ### Gödel numbering -/

/-- The base of register `i`: the Fermat number `2^(2^i) + 1`. -/
def base (i : ℕ) : ℕ := Nat.fermatNumber i

theorem three_le_base (i : ℕ) : 3 ≤ base i := Nat.three_le_fermatNumber i

/-- The Gödel number of the registers below `k`. -/
def godel (k : ℕ) (r : ℕ → ℕ) : ℕ := ∏ i ∈ Finset.range k, base i ^ r i

theorem godel_update (k : ℕ) (r : ℕ → ℕ) {i : ℕ} (hi : i < k) (v : ℕ) :
    godel k (Function.update r i v) * base i ^ r i = godel k r * base i ^ v := by
  unfold godel
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi),
    ← Finset.mul_prod_erase _ _ (Finset.mem_range.2 hi)]
  rw [Function.update_self]
  have : ∏ x ∈ (Finset.range k).erase i, base x ^ Function.update r i v x =
      ∏ x ∈ (Finset.range k).erase i, base x ^ r x := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]
  ring

/-- Increment: the Gödel number is multiplied by the base. -/
theorem godel_inc (k : ℕ) (r : ℕ → ℕ) {i : ℕ} (hi : i < k) :
    godel k (Function.update r i (r i + 1)) = base i * godel k r := by
  have h := godel_update k r hi (r i + 1)
  have hp : 0 < base i ^ r i := pow_pos (by have := three_le_base i; omega) _
  rw [pow_succ] at h
  have : godel k (Function.update r i (r i + 1)) * base i ^ r i =
      (base i * godel k r) * base i ^ r i := by rw [h]; ring
  exact Nat.eq_of_mul_eq_mul_right hp this

/-- Decrement: the Gödel number is the base times the decremented one. -/
theorem godel_dec (k : ℕ) (r : ℕ → ℕ) {i v : ℕ} (hi : i < k) (hv : r i = v + 1) :
    godel k r = base i * godel k (Function.update r i v) := by
  have h := godel_inc k (Function.update r i v) hi
  rw [Function.update_self, Function.update_idem] at h
  rw [← h, ← hv, Function.update_eq_self]

/-- Zero test: the base does not divide the Gödel number when the register is zero. -/
theorem godel_not_dvd (k : ℕ) (r : ℕ → ℕ) {i : ℕ} (h0 : r i = 0) : ¬ base i ∣ godel k r := by
  intro hd
  have hc : Nat.Coprime (base i) (godel k r) := by
    refine Nat.Coprime.prod_right fun j _ => ?_
    by_cases hj : j = i
    · subst hj; rw [h0, pow_zero]; exact Nat.coprime_one_right _
    · exact Nat.Coprime.pow_right _ (Nat.coprime_fermatNumber_fermatNumber (Ne.symm hj))
  have := Nat.Coprime.eq_one_of_dvd hc hd
  have := three_le_base i
  omega

/-! ### Running two-counter machines -/

section Run

variable {P : CM}

local notation "RT" => Relation.ReflTransGen (CM.Step P)
local notation "TG" => Relation.TransGen (CM.Step P)

theorem rt_incA {x l a b : ℕ} (h : P[x]? = some (.inc true l)) :
    Relation.TransGen (CM.Step P) ⟨x, a, b⟩ ⟨l, a + 1, b⟩ := .single (CM.Step.incA h)

/-- A chain of increments of the first counter, entered `j` instructions before its end. -/
theorem chainA {s n : ℕ} (h : ∀ m < n, P[s + m]? = some (.inc true (s + m + 1))) :
    ∀ j ≤ n, ∀ a b, RT ⟨s + (n - j), a, b⟩ ⟨s + n, a + j, b⟩
  | 0, _, a, b => by simpa using Relation.ReflTransGen.refl
  | j + 1, hj, a, b => by
      have hs := CM.Step.incA (c := ⟨s + (n - (j + 1)), a, b⟩) (h (n - (j + 1)) (by omega))
      have hr := chainA h j (by omega) (a + 1) b
      rw [show s + (n - (j + 1)) + 1 = s + (n - j) by omega] at hs
      rw [show a + (j + 1) = a + 1 + j by omega]
      exact .head hs hr

/-- A chain of increments of the second counter. -/
theorem chainB {s n : ℕ} (h : ∀ m < n, P[s + m]? = some (.inc false (s + m + 1))) :
    ∀ j ≤ n, ∀ a b, RT ⟨s + (n - j), a, b⟩ ⟨s + n, a, b + j⟩
  | 0, _, a, b => by simpa using Relation.ReflTransGen.refl
  | j + 1, hj, a, b => by
      have hs := CM.Step.incB (c := ⟨s + (n - (j + 1)), a, b⟩) (h (n - (j + 1)) (by omega))
      have hr := chainB h j (by omega) a (b + 1)
      rw [show s + (n - (j + 1)) + 1 = s + (n - j) by omega] at hs
      rw [show b + (j + 1) = b + 1 + j by omega]
      exact .head hs hr

/-- **Moving the second counter into the first.** -/
theorem moveBA {o z : ℕ} (h1 : P[o]? = some (.test false z (o + 1)))
    (h2 : P[o + 1]? = some (.inc true o)) : ∀ b a, TG ⟨o, a, b⟩ ⟨z, a + b, 0⟩
  | 0, a => .single (CM.Step.zeroB (c := ⟨o, a, 0⟩) h1 rfl)
  | b + 1, a => by
      have s1 := CM.Step.decB (c := ⟨o, a, b + 1⟩) h1 rfl
      have s2 := CM.Step.incA (c := ⟨o + 1, a, b⟩) h2
      have := moveBA h1 h2 b (a + 1)
      rw [show a + (b + 1) = a + 1 + b by omega]
      exact .head s1 (.head s2 this)

/-- **Multiplying the first counter into the second** (`p` increments per unit). -/
theorem mulAB {o z p : ℕ} (hp : 1 ≤ p) (h1 : P[o]? = some (.test true z (o + 1)))
    (h2 : ∀ m < p - 1, P[o + 1 + m]? = some (.inc false (o + 1 + m + 1)))
    (h3 : P[o + p]? = some (.inc false o)) : ∀ a b, TG ⟨o, a, b⟩ ⟨z, 0, b + p * a⟩
  | 0, b => .single (CM.Step.zeroA (c := ⟨o, 0, b⟩) h1 rfl)
  | a + 1, b => by
      have s1 := CM.Step.decA (c := ⟨o, a + 1, b⟩) h1 rfl
      have hc := chainB h2 (p - 1) le_rfl a b
      rw [Nat.sub_self, Nat.add_zero] at hc
      have s3 := CM.Step.incB (c := ⟨o + 1 + (p - 1), a, b + (p - 1)⟩)
        (by rw [show o + 1 + (p - 1) = o + p by omega]; exact h3)
      have := mulAB hp h1 h2 h3 a (b + (p - 1) + 1)
      rw [show b + (p - 1) + 1 + p * a = b + p * (a + 1) by rw [Nat.mul_succ]; omega] at this
      exact .head' s1 (hc.trans (.head s3 this.to_reflTransGen))

/-- **Multiplying the second counter into the first** (`p` increments per unit). -/
theorem mulBA {o z p : ℕ} (hp : 1 ≤ p) (h1 : P[o]? = some (.test false z (o + 1)))
    (h2 : ∀ m < p - 1, P[o + 1 + m]? = some (.inc true (o + 1 + m + 1)))
    (h3 : P[o + p]? = some (.inc true o)) : ∀ b a, TG ⟨o, a, b⟩ ⟨z, a + p * b, 0⟩
  | 0, a => .single (CM.Step.zeroB (c := ⟨o, a, 0⟩) h1 rfl)
  | b + 1, a => by
      have s1 := CM.Step.decB (c := ⟨o, a, b + 1⟩) h1 rfl
      have hc := chainA h2 (p - 1) le_rfl a b
      rw [Nat.sub_self, Nat.add_zero] at hc
      have s3 := CM.Step.incA (c := ⟨o + 1 + (p - 1), a + (p - 1), b⟩)
        (by rw [show o + 1 + (p - 1) = o + p by omega]; exact h3)
      have := mulBA hp h1 h2 h3 b (a + (p - 1) + 1)
      rw [show a + (p - 1) + 1 + p * b = a + p * (b + 1) by rw [Nat.mul_succ]; omega] at this
      exact .head' s1 (hc.trans (.head s3 this.to_reflTransGen))

/-- One round of division: `p` is taken from the first counter and the second is incremented. -/
theorem divRound {o p : ℕ} {ex : ℕ → ℕ}
    (h1 : ∀ j < p, P[o + j]? = some (.test true (ex j) (o + j + 1)))
    (h2 : P[o + p]? = some (.inc false o)) :
    ∀ d, 1 ≤ d → d ≤ p → ∀ x b, RT ⟨o + (p - d), x + d, b⟩ ⟨o, x, b + 1⟩
  | 0, hd, _, _, _ => absurd hd (by omega)
  | d + 1, _, hd, x, b => by
      have s1 := CM.Step.decA (c := ⟨o + (p - (d + 1)), x + (d + 1), b⟩) (n := x + d)
        (h1 _ (by omega)) rfl
      rw [show o + (p - (d + 1)) + 1 = o + (p - d) by omega] at s1
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · subst h0
        have s2 := CM.Step.incB (c := ⟨o + (p - 0), x, b⟩) (by simpa using h2)
        simp only [Nat.add_zero] at s1 s2 ⊢
        exact .head s1 (.single s2)
      · exact .head s1 (divRound h1 h2 d hpos (by omega) x b)

/-- The remainder phase of a division: the first counter runs out at position `j`. -/
theorem divRem {o p : ℕ} {ex : ℕ → ℕ}
    (h1 : ∀ j < p, P[o + j]? = some (.test true (ex j) (o + j + 1))) {j : ℕ} (hj : j < p) :
    ∀ m ≤ j, ∀ b, TG ⟨o + (j - m), m, b⟩ ⟨ex j, 0, b⟩
  | 0, _, b => by
      simpa using Relation.TransGen.single
        (CM.Step.zeroA (c := ⟨o + j, 0, b⟩) (h1 j hj) rfl)
  | m + 1, hm, b => by
      have s1 := CM.Step.decA (c := ⟨o + (j - (m + 1)), m + 1, b⟩) (n := m) (h1 _ (by omega)) rfl
      rw [show o + (j - (m + 1)) + 1 = o + (j - m) by omega] at s1
      exact .head s1 (divRem h1 hj m (by omega) b)

/-- **Division by `p`**: from `(o, p q + j, b)` the run reaches the exit of the remainder `j`
with the quotient added to the second counter. -/
theorem divide {o p : ℕ} {ex : ℕ → ℕ}
    (h1 : ∀ j < p, P[o + j]? = some (.test true (ex j) (o + j + 1)))
    (h2 : P[o + p]? = some (.inc false o)) (hp : 1 ≤ p) {j : ℕ} (hj : j < p) :
    ∀ q b, TG ⟨o, p * q + j, b⟩ ⟨ex j, 0, b + q⟩
  | 0, b => by simpa using divRem h1 hj j le_rfl b
  | q + 1, b => by
      have := divRound h1 h2 p hp le_rfl (p * q + j) b
      rw [Nat.sub_self, Nat.add_zero, show p * q + j + p = p * (q + 1) + j by
        rw [Nat.mul_succ]; omega] at this
      have h' := divide h1 h2 hp hj q (b + 1)
      rw [show b + 1 + q = b + (q + 1) by omega] at h'
      exact Relation.TransGen.trans_right this h'

end Run


/-- Close a goal `some (block j) = some instr` by unfolding the case split of the block. -/
macro "blk" : tactic => `(tactic| (split_ifs <;> first | rfl | (exfalso; omega) |
  (simp only [Option.some.injEq, CMInstr.inc.injEq, CMInstr.test.injEq, true_and]; omega)))

/-! ### The compiled program -/

/-- The block of an increment of a register with base `p`, at offset `o`, continuing at `t`:
multiply the first counter into the second, then move it back. -/
def incF (p o t : ℕ) (j : ℕ) : CMInstr :=
  if j = 0 then .test true (o + p + 1) (o + 1)
  else if j < p then .inc false (o + j + 1)
  else if j = p then .inc false o
  else if j = p + 1 then .test false t (o + p + 2)
  else .inc true (o + p + 1)

/-- The exit of the division loop for the remainder `j`. -/
def exitL (p o j : ℕ) : ℕ := if j = 0 then o + p + 1 else o + p + 3 + (p - 1 - j)

/-- The block of a test of a register with base `p`, at offset `o`, with zero branch `t₁` and
decrement branch `t₂`: divide the first counter by `p`; on remainder zero move the quotient back,
otherwise restore the remainder and `p` times the quotient. -/
def testF (p o t₁ t₂ : ℕ) (j : ℕ) : CMInstr :=
  if j < p then .test true (exitL p o j) (o + j + 1)
  else if j = p then .inc false o
  else if j = p + 1 then .test false t₂ (o + p + 2)
  else if j = p + 2 then .inc true (o + p + 1)
  else if j < 2 * p + 2 then .inc true (o + j + 1)
  else if j = 2 * p + 2 then .test false t₁ (o + 2 * p + 3)
  else if j < 3 * p + 2 then .inc true (o + j + 1)
  else .inc true (o + 2 * p + 2)

/-- The size of the block of an instruction. -/
def isize : KInstr → ℕ
  | .inc i _ => base i + 3
  | .test i _ _ => 3 * base i + 3

/-- The offset of the block of label `l` (labels from the length on are the end). -/
def off (M : KM) (l : ℕ) : ℕ := ((M.take l).map isize).sum

/-- The instructions of the block of an instruction at offset `o`. -/
def blockF (M : KM) (o : ℕ) : KInstr → ℕ → CMInstr
  | .inc i l => incF (base i) o (off M l)
  | .test i l₁ l₂ => testF (base i) o (off M l₁) (off M l₂)

/-- The blocks of the instructions of `L`, the first at label `s`. -/
def compileAux (M : KM) : List KInstr → ℕ → CM
  | [], _ => []
  | ins :: L, s => (List.range (isize ins)).map (blockF M (off M s) ins) ++ compileAux M L (s + 1)

/-- **The two-counter program simulating a counter machine.** -/
def compile (M : KM) : CM := compileAux M M 0

theorem compileAux_length (M : KM) : ∀ (L : List KInstr) (s : ℕ),
    (compileAux M L s).length = (L.map isize).sum
  | [], _ => rfl
  | ins :: L, s => by simp [compileAux, compileAux_length M L]

theorem compileAux_get (M : KM) : ∀ (L : List KInstr) (s l : ℕ) (hl : l < L.length) (j : ℕ),
    j < isize L[l] → (compileAux M L s)[((L.take l).map isize).sum + j]? =
      some (blockF M (off M (s + l)) L[l] j)
  | [], _, _, hl, _, _ => by simp at hl
  | ins :: L, s, 0, _, j, hj => by
      simp only [compileAux, List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add,
        Nat.add_zero, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map,
        List.getElem?_range (by simpa using hj)]
      rfl
  | ins :: L, s, l + 1, hl, j, hj => by
      simp only [compileAux, List.take_succ_cons, List.map_cons, List.sum_cons,
        List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      rw [show isize ins + ((L.take l).map isize).sum + j - isize ins =
        ((L.take l).map isize).sum + j by omega]
      rw [compileAux_get M L (s + 1) l (by simpa using hl) j hj]
      rw [show s + 1 + l = s + (l + 1) by omega]

theorem compile_get {M : KM} {l : ℕ} {ins : KInstr} (h : M[l]? = some ins) {j : ℕ}
    (hj : j < isize ins) : (compile M)[off M l + j]? = some (blockF M (off M l) ins j) := by
  obtain ⟨hl, rfl⟩ := List.getElem?_eq_some_iff.1 h
  have := compileAux_get M M 0 l hl j hj
  rw [Nat.zero_add] at this
  exact this

theorem compile_length (M : KM) : (compile M).length = off M M.length := by
  simp [compile, compileAux_length, off]

theorem isize_pos (ins : KInstr) : 0 < isize ins := by cases ins <;> simp [isize]

theorem off_lt {M : KM} {l : ℕ} (h : l < M.length) : off M l < off M M.length := by
  unfold off
  rw [List.take_of_length_le le_rfl]
  conv_rhs => rw [← List.take_append_drop l M]
  rw [List.map_append, List.sum_append]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (show M.drop l ≠ [] by simp; omega)
  rw [hx]
  simp only [List.map_cons, List.sum_cons]
  have := isize_pos x
  omega

theorem off_of_le {M : KM} {l : ℕ} (h : M.length ≤ l) : off M l = off M M.length := by
  simp [off, List.take_of_length_le h]

/-! ### Correctness of the blocks -/

section Blocks

variable {P : CM}

/-- The increment block multiplies the first counter by `p`. -/
theorem incBlock_run {p o t : ℕ} (hp : 2 ≤ p)
    (hP : ∀ j < p + 3, P[o + j]? = some (incF p o t j)) (N : ℕ) :
    Relation.TransGen (CM.Step P) ⟨o, N, 0⟩ ⟨t, p * N, 0⟩ := by
  have e : ∀ x j, x = o + j → j < p + 3 → P[x]? = some (incF p o t j) := by
    rintro x j rfl hj; exact hP j hj
  have h1 := mulAB (P := P) (o := o) (z := o + p + 1) (p := p) (by omega)
    (by rw [e o 0 (by omega) (by omega)]; simp [incF])
    (fun m hm => by
      rw [e (o + 1 + m) (1 + m) (by omega) (by omega)]
      simp only [incF]; blk)
    (by
      rw [e (o + p) p (by omega) (by omega)]
      simp only [incF]; blk)
    N 0
  have h2 := moveBA (P := P) (o := o + p + 1) (z := t)
    (by
      rw [e (o + p + 1) (p + 1) (by omega) (by omega)]
      simp only [incF]; blk)
    (by
      rw [e (o + p + 1 + 1) (p + 2) (by omega) (by omega)]
      simp only [incF]; blk)
    (0 + p * N) 0
  simp only [Nat.zero_add] at h1 h2
  exact h1.trans h2

theorem testF_at {p o t₁ t₂ : ℕ} (hP : ∀ j < 3 * p + 3, P[o + j]? = some (testF p o t₁ t₂ j))
    {x j : ℕ} (hx : x = o + j) (hj : j < 3 * p + 3) : P[x]? = some (testF p o t₁ t₂ j) := by
  subst hx; exact hP j hj

theorem testBlock_div {p o t₁ t₂ : ℕ} (hp : 2 ≤ p)
    (hP : ∀ j < 3 * p + 3, P[o + j]? = some (testF p o t₁ t₂ j)) :
    ∀ j < p, P[o + j]? = some (.test true (exitL p o j) (o + j + 1)) := fun j hj => by
  rw [hP j (by omega)]; simp only [testF]; blk

theorem testBlock_inc {p o t₁ t₂ : ℕ}
    (hP : ∀ j < 3 * p + 3, P[o + j]? = some (testF p o t₁ t₂ j)) :
    P[o + p]? = some (.inc false o) := by
  rw [hP p (by omega)]; simp only [testF]; blk

/-- The test block on a multiple of `p`: the quotient, decrement branch. -/
theorem testBlock_dvd {p o t₁ t₂ : ℕ} (hp : 2 ≤ p)
    (hP : ∀ j < 3 * p + 3, P[o + j]? = some (testF p o t₁ t₂ j)) (q : ℕ) :
    Relation.TransGen (CM.Step P) ⟨o, p * q, 0⟩ ⟨t₂, q, 0⟩ := by
  have h1 := divide (testBlock_div hp hP) (testBlock_inc hP) (by omega) (j := 0) (by omega) q 0
  have h2 := moveBA (P := P) (o := o + p + 1) (z := t₂)
    (by
      rw [testF_at hP (j := p + 1) (by omega) (by omega)]
      simp only [testF]; blk)
    (by
      rw [testF_at hP (j := p + 2) (by omega) (by omega)]
      simp only [testF]; blk)
    (0 + q) 0
  simp only [Nat.add_zero, Nat.zero_add, exitL, ite_eq_left] at h1 h2
  exact h1.trans h2

/-- The test block on a non-multiple of `p`: the number is restored, zero branch. -/
theorem testBlock_ndvd {p o t₁ t₂ : ℕ} (hp : 2 ≤ p)
    (hP : ∀ j < 3 * p + 3, P[o + j]? = some (testF p o t₁ t₂ j)) (q : ℕ) {j : ℕ}
    (hj0 : 0 < j) (hj : j < p) :
    Relation.TransGen (CM.Step P) ⟨o, p * q + j, 0⟩ ⟨t₁, p * q + j, 0⟩ := by
  have h1 := divide (testBlock_div hp hP) (testBlock_inc hP) (by omega) hj q 0
  have hex : exitL p o j = o + p + 3 + (p - 1 - j) := by simp [exitL, Nat.pos_iff_ne_zero.1 hj0]
  rw [hex, Nat.zero_add] at h1
  have h2 := chainA (P := P) (s := o + p + 3) (n := p - 1)
    (fun m hm => by
      rw [testF_at hP (j := p + 3 + m) (by omega) (by omega)]
      simp only [testF]; blk)
    j (by omega) 0 q
  have h3 := mulBA (P := P) (o := o + 2 * p + 2) (z := t₁) (p := p) (by omega)
    (by
      rw [testF_at hP (j := 2 * p + 2) (by omega) (by omega)]
      simp only [testF]; blk)
    (fun m hm => by
      rw [testF_at hP (j := 2 * p + 3 + m) (by omega) (by omega)]
      simp only [testF]; blk)
    (by
      rw [testF_at hP (j := 3 * p + 2) (by omega) (by omega)]
      simp only [testF]; blk)
    q j
  rw [show o + p + 3 + (p - 1) = o + 2 * p + 2 by omega, Nat.zero_add] at h2
  rw [show j + p * q = p * q + j by omega] at h3
  exact h1.trans_left (h2.trans h3.to_reflTransGen)

end Blocks


/-! ### The simulation -/

/-- The encoding of a configuration of the counter machine as a two-counter configuration. -/
def encC (M : KM) (k : ℕ) (c : KConf) : CMConf := ⟨off M c.pc, godel k c.r, 0⟩

/-- All registers used by the program are below `k`. -/
def RegsBelow (M : KM) (k : ℕ) : Prop := ∀ ins ∈ M, ins.reg < k

theorem two_le_base (i : ℕ) : 2 ≤ base i := by have := three_le_base i; omega

/-- **The step-correctness lemma of Minsky's construction**: one step of the counter machine is
a non-empty run of the compiled two-counter machine between the encoded configurations. -/
theorem sim_step {M : KM} {k : ℕ} (hk : RegsBelow M k) {c c' : KConf} (hs : KM.Step M c c') :
    Relation.TransGen (CM.Step (compile M)) (encC M k c) (encC M k c') := by
  cases hs with
  | @inc i l hi =>
      have hik : i < k := hk _ (List.mem_of_getElem? hi)
      have hP : ∀ j < base i + 3, (compile M)[off M c.pc + j]? =
          some (incF (base i) (off M c.pc) (off M l) j) := fun j hj =>
        compile_get hi (by simpa [isize] using hj)
      have := incBlock_run (two_le_base i) hP (godel k c.r)
      rw [← godel_inc k c.r hik] at this
      exact this
  | @zero i l₁ l₂ hi h0 =>
      have hP : ∀ j < 3 * base i + 3, (compile M)[off M c.pc + j]? =
          some (testF (base i) (off M c.pc) (off M l₁) (off M l₂) j) := fun j hj =>
        compile_get hi (by simpa [isize] using hj)
      have hnd := godel_not_dvd k c.r h0
      have hmod : 0 < godel k c.r % base i :=
        Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
      have := testBlock_ndvd (two_le_base i) hP (godel k c.r / base i) hmod
        (Nat.mod_lt _ (by have := three_le_base i; omega))
      rw [Nat.div_add_mod] at this
      exact this
  | @dec i l₁ l₂ v hi hv =>
      have hik : i < k := hk _ (List.mem_of_getElem? hi)
      have hP : ∀ j < 3 * base i + 3, (compile M)[off M c.pc + j]? =
          some (testF (base i) (off M c.pc) (off M l₁) (off M l₂) j) := fun j hj =>
        compile_get hi (by simpa [isize] using hj)
      have := testBlock_dvd (two_le_base i) hP (godel k (Function.update c.r i v))
      rw [← godel_dec k c.r hik hv] at this
      exact this

/-- Two-counter machines are deterministic. -/
theorem cm_step_det {P : CM} {c c₁ c₂ : CMConf} (h₁ : CM.Step P c c₁) (h₂ : CM.Step P c c₂) :
    c₁ = c₂ := by
  cases h₁ <;> cases h₂ <;> simp_all

theorem cm_no_step {P : CM} {c c' : CMConf} (h : P.length ≤ c.pc) : ¬ CM.Step P c c' := by
  intro hs
  cases hs <;> simp_all

/-- A halting run of the counter machine gives a halting run of the compiled machine. -/
theorem cm_halts_of_halts {M : KM} {k : ℕ} (hk : RegsBelow M k) {c : KConf}
    (h : KM.HaltsFrom M c) : ∃ c', Relation.ReflTransGen (CM.Step (compile M)) (encC M k c) c' ∧
      (compile M).length ≤ c'.pc := by
  obtain ⟨c', hr, hpc⟩ := h
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨_, .refl, by simp [encC, compile_length, off_of_le hpc]⟩
  | head hs _ ih =>
      obtain ⟨d, hd, hdp⟩ := ih
      exact ⟨d, (sim_step hk hs).to_reflTransGen.trans hd, hdp⟩

/-- A halting run of the compiled machine through an encoded configuration comes from a halting
run of the counter machine. -/
theorem halts_of_cm_run {M : KM} {k : ℕ} (hk : RegsBelow M k) {x y : CMConf}
    (hr : Relation.ReflTransGen (CM.Step (compile M)) x y) (hy : (compile M).length ≤ y.pc) :
    ∀ c, Relation.ReflTransGen (CM.Step (compile M)) x (encC M k c) → KM.HaltsFrom M c := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro c h
      rcases Relation.ReflTransGen.cases_head h with h | ⟨z, hz, _⟩
      · refine ⟨c, .refl, ?_⟩
        by_contra hlt
        have := off_lt (M := M) (Nat.lt_of_not_le hlt)
        rw [h] at hy
        simp only [encC, compile_length] at hy
        omega
      · exact absurd hz (cm_no_step hy)
  | head hs _ ih =>
      intro c h
      rcases Relation.ReflTransGen.cases_head h with he | ⟨z, hz, hzr⟩
      · by_cases hpc : M.length ≤ c.pc
        · exact ⟨c, .refl, hpc⟩
        · obtain ⟨c₁, hc₁⟩ := KM.progress (Nat.lt_of_not_le hpc)
          obtain ⟨z, hz, hzr⟩ := Relation.TransGen.head'_iff.1 (sim_step hk hc₁)
          rw [← he] at hz
          rw [cm_step_det hs hz] at *
          obtain ⟨d, h1, h2⟩ := ih c₁ hzr
          exact ⟨d, .head hc₁ h1, h2⟩
      · rw [cm_step_det hs hz] at *
        exact ih c hzr

/-- **Minsky's theorem**: a counter machine whose registers are below `k` halts from the
registers `r` exactly when the compiled two-counter machine halts from `(godel k r, 0)`. -/
theorem halts_iff {M : KM} {k : ℕ} (hk : RegsBelow M k) (r : ℕ → ℕ) :
    KM.Halts M r ↔ CM.Halts (compile M) (godel k r) 0 := by
  have he : encC M k ⟨0, r⟩ = ⟨0, godel k r, 0⟩ := by simp [encC, off]
  constructor
  · intro h
    obtain ⟨c', hr, hc'⟩ := cm_halts_of_halts hk h
    rw [he] at hr
    exact ⟨c', hr, hc'⟩
  · rintro ⟨c', hr, hc'⟩
    exact halts_of_cm_run hk hr hc' ⟨0, r⟩ (by rw [he])

/-- **Counter-machine halting reduces to subtyping in full F<:** (Minsky's construction followed
by the F<:^D simulation of `Start/FsubPierce.lean`). -/
theorem halts_iff_sub {M : KM} {k : ℕ} (hk : RegsBelow M k) (r : ℕ → ℕ) :
    KM.Halts M r ↔ Sub (FsubPierce.enc (compile M) (godel k r) 0) :=
  (halts_iff hk r).trans (FsubPierce.cm_halts_iff_sub _ _ _)

end Minsky
