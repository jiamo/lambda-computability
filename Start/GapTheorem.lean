/-
**The gap theorem of Borodin and Trakhtenbrot.**

`Start/StepComplexity.lean` counts the fuel a code needs on an input and proves the two Blum
axioms for that measure.  Complexity classes are then cut out by a computable bound `t`: the codes
converging on `x` within `t x` units of fuel.  One might expect that enlarging the bound — say
from `t` to `2 ^ t`, or to any computable `g ∘ t` with `g n ≥ n` — always enlarges the class.  It
does not: **for every computable `g` with `g n ≥ n` there is a computable bound `t` for which the
two classes coincide** (for every code, on all inputs beyond the code itself).  So the classes are
not indexed faithfully by their bounds, and a hierarchy theorem cannot be proved from the Blum
axioms alone: it must use a bound that is *honest* for the measure.

The construction is a search for a gap.  Iterating `g` from `0` gives a chain
`0 = chain 0 ≤ chain 1 ≤ ⋯`, and the interval `(chain i, chain (i+1)]` is *bad* for the input `x`
if some code below `x` needs a number of fuel units in it.  At most `x` of the `x + 1` intervals
with `i ≤ x` are bad, so a good one can be found by a bounded search, and `t x` is its lower end:
below `x` no code converges within `g (t x) = chain (i+1)` unless it already converges within
`t x = chain i`.

Main definitions:

* `Complexity.chain` — the iterates of `g` from `0`;
* `Complexity.badB`, `Complexity.goodB` — the decision that an interval of the chain is used by a
  code below `x`, and that none is;
* `Complexity.pick`, `Complexity.gapBound` — the bounded search for a good interval, and the
  resulting bound `t`.

Main results:

* `Complexity.exists_good_index` — the pigeonhole step: some interval with `i ≤ x` is good;
* `Complexity.goodB_pick`, `Complexity.pick_le` — the search finds one;
* `Complexity.computable_gapBound` — the bound is computable;
* `Complexity.gapBound_spec`, `Complexity.exists_gap` — **the gap theorem**.
-/

import Start.StepComplexity

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### The chain of iterates -/

/-- The iterates of `g` from `0`: `chain g i = g^[i] 0`.  Written with `Nat.rec` so that its
computability is immediate. -/
def chain (g : ℕ → ℕ) (i : ℕ) : ℕ := Nat.rec 0 (fun _ acc => g acc) i

@[simp] theorem chain_zero (g : ℕ → ℕ) : chain g 0 = 0 := rfl

@[simp] theorem chain_succ (g : ℕ → ℕ) (i : ℕ) : chain g (i + 1) = g (chain g i) := rfl

theorem chain_le_succ {g : ℕ → ℕ} (hle : ∀ n, n ≤ g n) (i : ℕ) : chain g i ≤ chain g (i + 1) :=
  hle _

theorem chain_mono {g : ℕ → ℕ} (hle : ∀ n, n ≤ g n) : Monotone (chain g) := by
  refine monotone_nat_of_le_succ ?_
  exact chain_le_succ hle

/-! ### Bad and good intervals -/

/-- The code with index `c` uses the interval `(chain g i, chain g (i+1)]` on the input `x`: it
converges there with the larger amount of fuel but not with the smaller. -/
def badB (g : ℕ → ℕ) (x i c : ℕ) : Bool :=
  (Code.evaln (chain g (i + 1)) (ofNat Code c) x).isSome &&
    !(Code.evaln (chain g i) (ofNat Code c) x).isSome

theorem badB_eq_true_iff (g : ℕ → ℕ) (x i c : ℕ) :
    badB g x i c = true ↔
      StepsLe (ofNat Code c) x (chain g (i + 1)) ∧ ¬ StepsLe (ofNat Code c) x (chain g i) := by
  simp [badB, StepsLe, Bool.and_eq_true]

/-- No code with index below `n` uses the interval `(chain g i, chain g (i+1)]` on the input `x`.
Written by `Nat.rec` over the bound, for computability. -/
def goodUpTo (g : ℕ → ℕ) (x i n : ℕ) : Bool :=
  Nat.rec true (fun k acc => acc && !badB g x i k) n

@[simp] theorem goodUpTo_zero (g : ℕ → ℕ) (x i : ℕ) : goodUpTo g x i 0 = true := rfl

@[simp] theorem goodUpTo_succ (g : ℕ → ℕ) (x i n : ℕ) :
    goodUpTo g x i (n + 1) = (goodUpTo g x i n && !badB g x i n) := rfl

/-- No code with index below `x` uses the interval `(chain g i, chain g (i+1)]` on the input `x`. -/
def goodB (g : ℕ → ℕ) (x i : ℕ) : Bool := goodUpTo g x i x

theorem goodUpTo_iff (g : ℕ → ℕ) (x i n : ℕ) :
    goodUpTo g x i n = true ↔ ∀ c < n, badB g x i c = false := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [goodUpTo_succ, Bool.and_eq_true, Bool.not_eq_true', ih]
      constructor
      · rintro ⟨h1, h2⟩ c hc
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc' | rfl
        · exact h1 c hc'
        · exact h2
      · intro h
        exact ⟨fun c hc => h c (Nat.lt_succ_of_lt hc), h n (Nat.lt_succ_self n)⟩

theorem goodB_iff (g : ℕ → ℕ) (x i : ℕ) :
    goodB g x i = true ↔ ∀ c < x, badB g x i c = false :=
  goodUpTo_iff g x i x

/-! ### The pigeonhole step -/

/-- **At most `x` of the `x + 1` intervals can be bad**, since a code uses at most one of them:
so some `i ≤ x` is good. -/
theorem exists_good_index {g : ℕ → ℕ} (hle : ∀ n, n ≤ g n) (x : ℕ) :
    ∃ i ≤ x, goodB g x i = true := by
  by_contra hcon
  push Not at hcon
  -- every `i ≤ x` has a code below `x` using its interval
  have hbad : ∀ i ∈ Finset.range (x + 1), ∃ c < x, badB g x i c = true := by
    intro i hi
    have hix : i ≤ x := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have : goodB g x i ≠ true := hcon i hix
    have := (goodB_iff g x i).not.1 this
    push Not at this
    obtain ⟨c, hc, hcb⟩ := this
    exact ⟨c, hc, by simpa using hcb⟩
  choose! wit hwit hwitb using hbad
  have hmaps : Set.MapsTo wit ↑(Finset.range (x + 1)) ↑(Finset.range x) := by
    intro i hi
    exact Finset.mem_coe.2 (Finset.mem_range.2 (hwit i (Finset.mem_coe.1 hi)))
  have hinj : Set.InjOn wit ↑(Finset.range (x + 1)) := by
    intro i hi j hj hij
    rw [Finset.mem_coe] at hi hj
    by_contra hne
    -- the two intervals are disjoint, so a single code cannot use both
    rcases Nat.lt_or_ge i j with h | h
    · have hb1 := (badB_eq_true_iff g x i (wit i)).1 (hwitb i hi)
      have hb2 := (badB_eq_true_iff g x j (wit j)).1 (hwitb j hj)
      rw [hij] at hb1
      exact absurd (stepsLe_mono (chain_mono hle h) hb1.1) hb2.2
    · have hji : j < i := lt_of_le_of_ne h (Ne.symm hne)
      have hb1 := (badB_eq_true_iff g x j (wit j)).1 (hwitb j hj)
      have hb2 := (badB_eq_true_iff g x i (wit i)).1 (hwitb i hi)
      rw [← hij] at hb1
      exact absurd (stepsLe_mono (chain_mono hle hji) hb1.1) hb2.2
  have hcard := Finset.card_le_card_of_injOn wit hmaps hinj
  simp at hcard

/-! ### The bounded search -/

/-- The bounded search for a good interval: `pick g x` is the least good `i ≤ x`, and `x + 1` if
there is none — which `Complexity.pick_le` rules out. -/
def pick (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  Nat.rec 0 (fun k acc => bif goodB g x acc then acc else k + 1) (x + 1)

/-- The value of the search after `n` steps, as an auxiliary for the induction. -/
def pickAux (g : ℕ → ℕ) (x n : ℕ) : ℕ :=
  Nat.rec 0 (fun k acc => bif goodB g x acc then acc else k + 1) n

@[simp] theorem pickAux_zero (g : ℕ → ℕ) (x : ℕ) : pickAux g x 0 = 0 := rfl

@[simp] theorem pickAux_succ (g : ℕ → ℕ) (x n : ℕ) :
    pickAux g x (n + 1) = bif goodB g x (pickAux g x n) then pickAux g x n else n + 1 := rfl

theorem pick_eq (g : ℕ → ℕ) (x : ℕ) : pick g x = pickAux g x (x + 1) := rfl

/-- The invariant of the search: after `n` steps either a good index has been found, or all the
indices below `n` are bad and the search stands at `n`. -/
theorem pickAux_spec (g : ℕ → ℕ) (x n : ℕ) :
    (goodB g x (pickAux g x n) = true ∧ pickAux g x n < n) ∨
      (pickAux g x n = n ∧ ∀ i < n, goodB g x i ≠ true) := by
  induction n with
  | zero => exact Or.inr ⟨rfl, by omega⟩
  | succ n ih =>
      rcases ih with ⟨hgood, hlt⟩ | ⟨heq, hbad⟩
      · refine Or.inl ⟨?_, ?_⟩
        · rw [pickAux_succ, hgood]; simpa using hgood
        · rw [pickAux_succ, hgood]; simpa using Nat.lt_succ_of_lt hlt
      · rcases hgn : goodB g x n with _ | _
        · refine Or.inr ⟨?_, ?_⟩
          · rw [pickAux_succ, heq, hgn]; rfl
          · intro i hi
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
            · exact hbad i hi'
            · rw [hgn]; exact Bool.noConfusion
        · refine Or.inl ⟨?_, ?_⟩
          · rw [pickAux_succ, heq, hgn]; simpa using hgn
          · rw [pickAux_succ, heq, hgn]; simp

/-- The search succeeds: it stops at a good index, which is at most `x`. -/
theorem goodB_pick {g : ℕ → ℕ} (hle : ∀ n, n ≤ g n) (x : ℕ) : goodB g x (pick g x) = true := by
  rcases pickAux_spec g x (x + 1) with ⟨hgood, _⟩ | ⟨heq, hbad⟩
  · exact hgood
  · obtain ⟨i, hix, hi⟩ := exists_good_index hle x
    exact absurd hi (hbad i (Nat.lt_succ_of_le hix))

theorem pick_le {g : ℕ → ℕ} (hle : ∀ n, n ≤ g n) (x : ℕ) : pick g x ≤ x := by
  rcases pickAux_spec g x (x + 1) with ⟨_, hlt⟩ | ⟨heq, hbad⟩
  · rw [pick_eq]; omega
  · obtain ⟨i, hix, hi⟩ := exists_good_index hle x
    exact absurd hi (hbad i (Nat.lt_succ_of_le hix))

/-! ### The bound and its computability -/

/-- **The bound of the gap theorem**: the lower end of a good interval for the input `x`. -/
def gapBound (g : ℕ → ℕ) (x : ℕ) : ℕ := chain g (pick g x)

theorem computable_chain {g : ℕ → ℕ} (hg : Computable g) : Computable (chain g) :=
  Computable.nat_rec Computable.id (Computable.const 0)
    (hg.comp (Computable.snd.comp Computable.snd)).to₂

theorem computable_badB {g : ℕ → ℕ} (hg : Computable g) :
    Computable fun a : (ℕ × ℕ) × ℕ => badB g a.1.1 a.1.2 a.2 := by
  have hchain := computable_chain hg
  have hx : Computable fun a : (ℕ × ℕ) × ℕ => a.1.1 := Computable.fst.comp Computable.fst
  have hi : Computable fun a : (ℕ × ℕ) × ℕ => a.1.2 := Computable.snd.comp Computable.fst
  have hc : Computable fun a : (ℕ × ℕ) × ℕ => a.2 := Computable.snd
  have hcode : Computable fun a : (ℕ × ℕ) × ℕ => ofNat Code a.2 :=
    (Computable.ofNat Code).comp hc
  have h1 : Computable fun a : (ℕ × ℕ) × ℕ =>
      Code.evaln (chain g (a.1.2 + 1)) (ofNat Code a.2) a.1.1 :=
    Code.primrec_evaln.to_comp.comp
      (((hchain.comp (Computable.succ.comp hi)).pair hcode).pair hx)
  have h2 : Computable fun a : (ℕ × ℕ) × ℕ =>
      Code.evaln (chain g a.1.2) (ofNat Code a.2) a.1.1 :=
    Code.primrec_evaln.to_comp.comp (((hchain.comp hi).pair hcode).pair hx)
  exact (Primrec.dom_bool₂ (fun b c => b && !c)).to_comp.comp
    (Primrec.option_isSome.to_comp.comp h1) (Primrec.option_isSome.to_comp.comp h2)

attribute [local irreducible] badB

/-- `goodB` written as the `Nat.rec` that `Computable.nat_rec` produces, with the motive spelled
out so that no unification is needed. -/
theorem goodB_natRec (g : ℕ → ℕ) (a : ℕ × ℕ) :
    Nat.rec (motive := fun _ => Bool) true (fun y IH => IH && !badB g a.1 a.2 y) a.1
      = goodB g a.1 a.2 := rfl

/-- Likewise for the bounded search. -/
theorem pick_natRec (g : ℕ → ℕ) (x : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0
        (fun y IH => bif goodB g x IH then IH else y + 1) (x + 1) = pick g x := rfl

set_option maxHeartbeats 4000000 in
-- The `Computable` combinators below unfold large `Primcodable` instances for the nested product
-- types, and elaborating the primitive-recursion step function exceeds the default budget.
theorem computable_goodB {g : ℕ → ℕ} (hg : Computable g) :
    Computable fun a : ℕ × ℕ => goodB g a.1 a.2 := by
  have hbad := computable_badB hg
  have hstep0 : Computable fun q : (ℕ × ℕ) × ℕ × Bool => q.2.2 && !badB g q.1.1 q.1.2 q.2.1 := by
    have h1 : Computable fun q : (ℕ × ℕ) × ℕ × Bool => q.2.2 :=
      Computable.snd.comp Computable.snd
    have hk : Computable fun q : (ℕ × ℕ) × ℕ × Bool => ((q.1, q.2.1) : (ℕ × ℕ) × ℕ) :=
      Computable.fst.pair (Computable.fst.comp Computable.snd)
    have h2 : Computable fun q : (ℕ × ℕ) × ℕ × Bool => badB g q.1.1 q.1.2 q.2.1 :=
      hbad.comp hk
    exact (Primrec.dom_bool₂ (fun b c => b && !c)).to_comp.comp h1 h2
  have hstep : Computable₂ fun (a : ℕ × ℕ) (p : ℕ × Bool) => p.2 && !badB g a.1 a.2 p.1 := hstep0
  exact (Computable.nat_rec (f := fun a : ℕ × ℕ => a.1) (g := fun _ : ℕ × ℕ => true)
    Computable.fst (Computable.const true) hstep).of_eq (goodB_natRec g)

attribute [local irreducible] goodB

set_option maxHeartbeats 1000000 in
-- Same reason as `computable_goodB`: the encodings of the nested products are large.
theorem computable_pick {g : ℕ → ℕ} (hg : Computable g) : Computable (pick g) := by
  have hgood := computable_goodB hg
  have hstep : Computable₂ fun (x : ℕ) (p : ℕ × ℕ) =>
      bif goodB g x p.2 then p.2 else p.1 + 1 := by
    have hk : Computable fun a : ℕ × ℕ × ℕ => ((a.1, a.2.2) : ℕ × ℕ) :=
      Computable.fst.pair (Computable.snd.comp Computable.snd)
    have hcond : Computable fun a : ℕ × ℕ × ℕ => goodB g a.1 a.2.2 :=
      hgood.comp hk
    have hthen : Computable fun a : ℕ × ℕ × ℕ => a.2.2 := Computable.snd.comp Computable.snd
    have helse : Computable fun a : ℕ × ℕ × ℕ => a.2.1 + 1 :=
      Computable.succ.comp (Computable.fst.comp Computable.snd)
    exact (Computable.cond hcond hthen helse).to₂
  exact (Computable.nat_rec (f := fun x : ℕ => x + 1) (g := fun _ : ℕ => 0)
    Computable.succ (Computable.const 0) hstep).of_eq (pick_natRec g)

theorem computable_gapBound {g : ℕ → ℕ} (hg : Computable g) : Computable (gapBound g) :=
  (computable_chain hg).comp (computable_pick hg)

/-! ### The gap -/

/-- **The gap theorem.**  Below the input, no code converges within `g (t x)` units of fuel
without already converging within `t x`. -/
theorem gapBound_spec {g : ℕ → ℕ} (hle : ∀ n, n ≤ g n) (c : Code) (x : ℕ) (hc : encode c < x) :
    StepsLe c x (g (gapBound g x)) ↔ StepsLe c x (gapBound g x) := by
  have hcode : ofNat Code (encode c) = c := Denumerable.ofNat_encode c
  constructor
  · intro h
    have hgood : badB g x (pick g x) (encode c) = false :=
      (goodB_iff g x (pick g x)).1 (goodB_pick hle x) (encode c) hc
    by_contra hB
    have hbad : badB g x (pick g x) (encode c) = true :=
      (badB_eq_true_iff g x (pick g x) (encode c)).2
        ⟨by rw [hcode]; exact h, by rw [hcode]; exact hB⟩
    rw [hgood] at hbad
    exact Bool.noConfusion hbad
  · intro h
    exact stepsLe_mono (hle _) h

/-- **The gap theorem**, packaged: for every computable `g` with `g n ≥ n` there is a computable
bound `t` such that the class of codes converging within `t` and the class of codes converging
within `g ∘ t` agree on every input above the code. -/
theorem exists_gap {g : ℕ → ℕ} (hg : Computable g) (hle : ∀ n, n ≤ g n) :
    ∃ t : ℕ → ℕ, Computable t ∧
      ∀ (c : Code) (x : ℕ), encode c < x → (StepsLe c x (g (t x)) ↔ StepsLe c x (t x)) :=
  ⟨gapBound g, computable_gapBound hg, fun c x hc => gapBound_spec hle c x hc⟩

end Complexity
