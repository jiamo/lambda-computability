/-
**The configuration graph of a space-bounded machine, as quantified Boolean formulas.**

`Start/QbfReach.lean` writes bounded reachability as a quantified Boolean formula, given a family
of *step formulas* expressing the edge relation on blocks of variables, and
`Start/QbfCfgWord.lean` writes a configuration of a space-bounded machine as a word of
`cfgWidth M x s = q + (n + 1) + 2 s` bits.  This module supplies the missing step formula and
assembles the whole reduction: for a machine `M` running in space `s` on the input `x` there is a
*closed* quantified Boolean formula `machineF M x s` which is true exactly when `M` accepts `x`,
and whose size is polynomial in `q`, `n`, `s` and the branching of the transition function.

The step formula is a disjunction over the *situations* of the machine — a control state, a
position of each head, and the bit read on the work tape — of the conjunction of the constraints
that one instruction imposes on the two blocks.  Because the heads are written in unary, every
constraint is a literal or a copy of a single variable, so one situation costs `O(width)` and the
whole formula `O(q · n · s · d · width)`.

Main definitions:

* `Complexity.Qbf.QBF.litF`, `.ff`, `.disjAny` — a literal, the false formula, and a disjunction
  over a list;
* `Complexity.Qbf.QBF.cfgF` — block `a` carries the word of the configuration with a given state
  and given head positions (and the tape block `a` itself carries);
* `Complexity.Qbf.QBF.tgtF`, `.stepCase`, `.caseList`, `.stepF` — the step formula;
* `Complexity.Qbf.QBF.initF`, `.accF`, `.machineF` — the formula of the whole reduction.

Main results:

* `Complexity.Qbf.QBF.eval_cfgF`, `.eval_tgtF` — the two families of block formulas are correct;
* `Complexity.Qbf.QBF.eval_stepF` — **the step formula expresses one step of the machine** on the
  words of `Start/QbfCfgWord.lean`;
* `Complexity.Qbf.QBF.size_stepF_le` — it is of size `O(q · (n+1) · s · d · width)`;
* `Complexity.Qbf.QBF.eval_machineF` — **the reduction is correct**: the closed formula is true
  exactly when the machine accepts the input;
* `Complexity.Qbf.QBF.size_machineF_le` — and its size is polynomial in `q`, `n`, `s` and `d`.

The honest boundary: what is *not* formalised here is that the map `x ↦ machineF M x s` is
computable in polynomial time.  That step — a syntactic transducer writing the formula — is what
would upgrade the reduction below into the statement that every language in `PSPACE` reduces to
`TQBF`, so `TQBF` is not claimed here to be `PSPACE`-hard.
-/

import Mathlib
import Start.QbfCfgWord

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity.Space Complexity.Reach

variable {M : Machine} {x : List Bool} {s : ℕ}

/-! ### Literals, disjunctions, and conjunctions over a range -/

/-- The literal demanding that the variable `i` carries the bit `b`. -/
def litF (i : ℕ) (b : Bool) : QBF := if b then QBF.var i else QBF.neg (QBF.var i)

@[simp] theorem eval_litF (σ : ℕ → Bool) (i : ℕ) (b : Bool) :
    (litF i b).eval σ = true ↔ σ i = b := by
  cases b <;> simp [litF, eval]

theorem size_litF_le (i : ℕ) (b : Bool) : (litF i b).size ≤ 2 := by
  cases b <;> simp [litF, size]

/-- The false formula. -/
def ff : QBF := QBF.conj (QBF.var 0) (QBF.neg (QBF.var 0))

@[simp] theorem eval_ff (σ : ℕ → Bool) : ff.eval σ = false := by
  simp only [ff, eval]
  cases σ 0 <;> simp

@[simp] theorem size_ff : ff.size = 4 := rfl

/-- The disjunction of a list of formulas. -/
def disjAny : List QBF → QBF
  | [] => ff
  | p :: ps => QBF.disj p (disjAny ps)

theorem eval_disjAny (σ : ℕ → Bool) : ∀ ps : List QBF,
    (disjAny ps).eval σ = true ↔ ∃ p ∈ ps, p.eval σ = true
  | [] => by simp [disjAny]
  | p :: ps => by
      simp only [disjAny, eval, Bool.or_eq_true, eval_disjAny σ ps, List.mem_cons]
      constructor
      · rintro (h | ⟨q, hq, hq'⟩)
        · exact ⟨p, Or.inl rfl, h⟩
        · exact ⟨q, Or.inr hq, hq'⟩
      · rintro ⟨q, rfl | hq, hq'⟩
        · exact Or.inl hq'
        · exact Or.inr ⟨q, hq, hq'⟩

theorem size_disjAny : ∀ ps : List QBF,
    (disjAny ps).size = (ps.map fun p => p.size + 1).sum + 4
  | [] => by simp [disjAny]
  | p :: ps => by
      simp only [disjAny, size, size_disjAny ps, List.map_cons, List.sum_cons]
      omega

theorem sum_le_of_forall_le {ps : List QBF} {K : ℕ} (h : ∀ p ∈ ps, p.size ≤ K) :
    (ps.map fun p => p.size + 1).sum ≤ ps.length * (K + 1) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have h₁ : p.size ≤ K := h p (List.mem_cons_self ..)
      have h₂ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have : (ps.length + 1) * (K + 1) = ps.length * (K + 1) + (K + 1) := by ring
      omega

theorem size_disjAny_le {ps : List QBF} {K : ℕ} (h : ∀ p ∈ ps, p.size ≤ K) :
    (disjAny ps).size ≤ ps.length * (K + 1) + 4 := by
  rw [size_disjAny]
  have := sum_le_of_forall_le h
  omega

theorem size_conjAll_le {ps : List QBF} {K : ℕ} (h : ∀ p ∈ ps, p.size ≤ K) :
    (conjAll ps).size ≤ ps.length * (K + 1) + 4 := by
  rw [size_conjAll]
  have := sum_le_of_forall_le h
  omega

theorem eval_conjAll_range (σ : ℕ → Bool) (m : ℕ) (f : ℕ → QBF) :
    (conjAll ((List.range m).map f)).eval σ = true ↔ ∀ l < m, (f l).eval σ = true := by
  rw [eval_conjAll]
  constructor
  · intro h l hl
    exact h _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩)
  · rintro h p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
    exact h l (List.mem_range.1 hl)

theorem eval_disjAny_map {α : Type} (σ : ℕ → Bool) (l : List α) (f : α → QBF) :
    (disjAny (l.map f)).eval σ = true ↔ ∃ z ∈ l, (f z).eval σ = true := by
  rw [eval_disjAny]
  constructor
  · rintro ⟨p, hp, hp'⟩
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
    exact ⟨z, hz, hp'⟩
  · rintro ⟨z, hz, hz'⟩
    exact ⟨f z, List.mem_map.2 ⟨z, hz, rfl⟩, hz'⟩

/-! ### The block of a configuration -/

/-- Block `a` carries the word of the configuration with control state `q`, input head `i` and
work head `j`; the work tape is left to the block itself. -/
def cfgF (M : Machine) (x : List Bool) (s : ℕ) (a q i j : ℕ) : QBF :=
  conjAll ((List.range (cfgWidth M x s)).map fun l =>
    if l < M.states then litF (a * cfgWidth M x s + l) (decide (l = q))
    else if l < M.states + (x.length + 1) then
      litF (a * cfgWidth M x s + l) (decide (l - M.states = i))
    else if l < M.states + (x.length + 1) + s then tt
    else litF (a * cfgWidth M x s + l) (decide (l - (M.states + (x.length + 1) + s) = j)))

/-- The formula for the target block of a transition: the new state, the new head positions, the
bit written under the old work head, and every other tape cell copied from block `a`. -/
def tgtF (M : Machine) (x : List Bool) (s : ℕ) (a b q' i' j' : ℕ) (w : Bool) (j : ℕ) : QBF :=
  conjAll ((List.range (cfgWidth M x s)).map fun l =>
    if l < M.states then litF (b * cfgWidth M x s + l) (decide (l = q'))
    else if l < M.states + (x.length + 1) then
      litF (b * cfgWidth M x s + l) (decide (l - M.states = i'))
    else if l < M.states + (x.length + 1) + s then
      (if l - (M.states + (x.length + 1)) = j then litF (b * cfgWidth M x s + l) w
        else iffVar (b * cfgWidth M x s + l) (a * cfgWidth M x s + l))
    else litF (b * cfgWidth M x s + l) (decide (l - (M.states + (x.length + 1) + s) = j')))

/-- The block formula is correct. -/
theorem eval_cfgF (σ : ℕ → Bool) (a q i j : ℕ) :
    (cfgF M x s a q i j).eval σ = true ↔
      blockVal (cfgWidth M x s) σ a =
        cfgWord M x s ⟨q, i, tapeOf M x s σ a, j⟩ := by
  rw [cfgF, eval_conjAll_range, blockVal_eq_cfgWord_iff]
  have key : ∀ l, l < cfgWidth M x s →
      (((if l < M.states then litF (a * cfgWidth M x s + l) (decide (l = q))
        else if l < M.states + (x.length + 1) then
          litF (a * cfgWidth M x s + l) (decide (l - M.states = i))
        else if l < M.states + (x.length + 1) + s then tt
        else litF (a * cfgWidth M x s + l)
          (decide (l - (M.states + (x.length + 1) + s) = j)))).eval σ = true ↔
        σ (a * cfgWidth M x s + l) =
          cfgBit M x s ⟨q, i, tapeOf M x s σ a, j⟩ l) := by
    intro l hl
    by_cases h1 : l < M.states
    · simp [h1, cfgBit]
    · by_cases h2 : l < M.states + (x.length + 1)
      · simp [h1, h2, cfgBit]
      · by_cases h3 : l < M.states + (x.length + 1) + s
        · have hls : l - (M.states + (x.length + 1)) < s := by omega
          have hbit : cfgBit M x s (⟨q, i, tapeOf M x s σ a, j⟩ : Config) l
              = σ (a * cfgWidth M x s + l) := by
            simp only [cfgBit, if_neg h1, if_neg h2, if_pos h3]
            rw [getD_tapeOf M x s σ a hls]
            congr 2
            omega
          simp [h1, h2, h3, hbit]
        · simp [h1, h2, h3, cfgBit]
  exact ⟨fun h l hl => (key l hl).1 (h l hl), fun h l hl => (key l hl).2 (h l hl)⟩

/-- The target formula is correct. -/
theorem eval_tgtF (σ : ℕ → Bool) (a b q' i' j' : ℕ) (w : Bool) (j : ℕ) :
    (tgtF M x s a b q' i' j' w j).eval σ = true ↔
      blockVal (cfgWidth M x s) σ b =
        cfgWord M x s ⟨q', i', writeAt (tapeOf M x s σ a) j w, j'⟩ := by
  rw [tgtF, eval_conjAll_range, blockVal_eq_cfgWord_iff]
  have key : ∀ l, l < cfgWidth M x s →
      (((if l < M.states then litF (b * cfgWidth M x s + l) (decide (l = q'))
        else if l < M.states + (x.length + 1) then
          litF (b * cfgWidth M x s + l) (decide (l - M.states = i'))
        else if l < M.states + (x.length + 1) + s then
          (if l - (M.states + (x.length + 1)) = j then litF (b * cfgWidth M x s + l) w
            else iffVar (b * cfgWidth M x s + l) (a * cfgWidth M x s + l))
        else litF (b * cfgWidth M x s + l)
          (decide (l - (M.states + (x.length + 1) + s) = j')))).eval σ = true ↔
        σ (b * cfgWidth M x s + l) =
          cfgBit M x s ⟨q', i', writeAt (tapeOf M x s σ a) j w, j'⟩ l) := by
    intro l hl
    by_cases h1 : l < M.states
    · simp [h1, cfgBit]
    · by_cases h2 : l < M.states + (x.length + 1)
      · simp [h1, h2, cfgBit]
      · by_cases h3 : l < M.states + (x.length + 1) + s
        · have hls : l - (M.states + (x.length + 1)) < s := by omega
          by_cases h4 : l - (M.states + (x.length + 1)) = j
          · have hbit : cfgBit M x s
                (⟨q', i', writeAt (tapeOf M x s σ a) j w, j'⟩ : Config) l = w := by
              simp only [cfgBit, if_neg h1, if_neg h2, if_pos h3]
              rw [h4, getD_writeAt_self]
            simp [h1, h2, h3, h4, hbit]
          · have hbit : cfgBit M x s
                (⟨q', i', writeAt (tapeOf M x s σ a) j w, j'⟩ : Config) l
                = σ (a * cfgWidth M x s + l) := by
              simp only [cfgBit, if_neg h1, if_neg h2, if_pos h3]
              rw [getD_writeAt_of_ne _ _ _ _ h4, getD_tapeOf M x s σ a hls]
              congr 2
              omega
            simp [h1, h2, h3, h4, hbit]
        · simp [h1, h2, h3, cfgBit]
  exact ⟨fun h l hl => (key l hl).1 (h l hl), fun h l hl => (key l hl).2 (h l hl)⟩

/-! ### The step formula -/

/-- One situation of the machine and one instruction available in it. -/
def stepCase (M : Machine) (x : List Bool) (s : ℕ) (a b q i j : ℕ) (bit : Bool)
    (t : ℕ × Bool × Dir × Dir) : QBF :=
  QBF.conj
    (QBF.conj (cfgF M x s a q i j)
      (litF (a * cfgWidth M x s + (M.states + (x.length + 1) + j)) bit))
    (tgtF M x s a b t.1 (moveIn x.length i t.2.2.1) (moveWork j t.2.2.2) t.2.1 j)

/-- All situations of the machine, with the instructions available in them that stay inside the
state set and inside the space bound. -/
theorem length_flatMap_le {α β : Type} (l : List α) (f : α → List β) (K : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ K) : (l.flatMap f).length ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have h₁ : (f a).length ≤ K := h a (List.mem_cons_self ..)
      have h₂ := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have : (l.length + 1) * K = l.length * K + K := by ring
      omega

def allDirs : List Dir := [Dir.left, Dir.right, Dir.stay]

theorem mem_allDirs (d : Dir) : d ∈ allDirs := by cases d <;> simp [allDirs]

@[simp] theorem length_allDirs : allDirs.length = 3 := rfl

/-- Every instruction whose new state is one of the machine's: the instructions a situation can
possibly offer.  Running over this list rather than over the transition function's own list makes
the count of cases independent of how the transition function is written. -/
def allInstr (q : ℕ) : List (ℕ × Bool × Dir × Dir) :=
  (List.range q).flatMap fun q' =>
    [false, true].flatMap fun w =>
      allDirs.flatMap fun d₁ =>
        allDirs.map fun d₂ => (q', w, d₁, d₂)

theorem mem_allInstr {q : ℕ} {t : ℕ × Bool × Dir × Dir} : t ∈ allInstr q ↔ t.1 < q := by
  obtain ⟨q', w, d₁, d₂⟩ := t
  simp only [allInstr, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false, Prod.mk.injEq]
  constructor
  · rintro ⟨r, hr, w', -, e₁, -, e₂, -, rfl, rfl, rfl, rfl⟩
    exact hr
  · intro h
    exact ⟨q', h, w, by cases w <;> simp, d₁, mem_allDirs d₁, d₂, mem_allDirs d₂,
      rfl, rfl, rfl, rfl⟩

theorem length_allInstr (q : ℕ) : (allInstr q).length ≤ q * 18 := by
  have h1 : ∀ q' : ℕ, (([false, true] : List Bool).flatMap fun w =>
      allDirs.flatMap fun d₁ => allDirs.map fun d₂ => (q', w, d₁, d₂)).length ≤ 2 * (3 * 3) := by
    intro q'
    simp [allDirs]
  have h0 := length_flatMap_le (List.range q) _ (2 * (3 * 3)) fun q' _ => h1 q'
  rw [List.length_range] at h0
  refine le_trans h0 (le_of_eq ?_)
  ring

def caseList (M : Machine) (x : List Bool) (s : ℕ) :
    List (ℕ × ℕ × ℕ × Bool × (ℕ × Bool × Dir × Dir)) :=
  (List.range M.states).flatMap fun q =>
    (List.range (x.length + 1)).flatMap fun i =>
      (List.range s).flatMap fun j =>
        [false, true].flatMap fun bit =>
          ((allInstr M.states).filter fun t =>
              decide (t ∈ M.delta q x[i]? bit) && decide (moveWork j t.2.2.2 < s)).map
            fun t => (q, i, j, bit, t)

/-- **The step formula**: the disjunction over all situations and instructions. -/
def stepF (M : Machine) (x : List Bool) (s : ℕ) (a b : ℕ) : QBF :=
  disjAny ((caseList M x s).map fun z =>
    stepCase M x s a b z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)

/-- Membership in the list of situations, unfolded. -/
theorem mem_caseList {q i j : ℕ} {bit : Bool} {t : ℕ × Bool × Dir × Dir} :
    (q, i, j, bit, t) ∈ caseList M x s ↔
      q < M.states ∧ i ≤ x.length ∧ j < s ∧ t ∈ M.delta q x[i]? bit ∧
        t.1 < M.states ∧ moveWork j t.2.2.2 < s := by
  simp only [caseList, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨q', hq', i', hi', j', hj', bit', -, t', ⟨ht', ht1, ht2⟩,
      ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    exact ⟨hq', by omega, hj', ht1, mem_allInstr.1 ht', ht2⟩
  · rintro ⟨hq, hi, hj, ht, ht1, ht2⟩
    exact ⟨q, hq, i, by omega, j, hj, bit, by cases bit <;> simp,
      t, ⟨mem_allInstr.2 ht1, ht, ht2⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- **The step formula expresses one step of the machine.** -/
theorem eval_stepF (σ : ℕ → Bool) (a b : ℕ) :
    (stepF M x s a b).eval σ = true ↔
      WordStep M x s (blockVal (cfgWidth M x s) σ a) (blockVal (cfgWidth M x s) σ b) := by
  rw [stepF, eval_disjAny_map]
  constructor
  · rintro ⟨⟨q, i, j, bit, t⟩, hz, hev⟩
    obtain ⟨hq, hi, hj, ht, ht1, ht2⟩ := mem_caseList.1 hz
    simp only [stepCase, eval, Bool.and_eq_true] at hev
    obtain ⟨⟨hcfg, hlit⟩, htgt⟩ := hev
    rw [eval_cfgF] at hcfg
    rw [eval_tgtF] at htgt
    rw [eval_litF] at hlit
    set c : Config := ⟨q, i, tapeOf M x s σ a, j⟩ with hc
    set c' : Config := ⟨t.1, moveIn x.length i t.2.2.1,
      writeAt (tapeOf M x s σ a) j t.2.1, moveWork j t.2.2.2⟩ with hc'
    have hread : c.tape.getD c.wHead false = bit := by
      rw [hc]
      simpa using (getD_tapeOf M x s σ a hj).trans hlit
    refine ⟨c, c', hcfg, htgt, ⟨⟨hq, hi, by simp [hc], hj⟩, ⟨ht1, ?_, ?_, ht2⟩, ?_⟩⟩
    · exact moveIn_le _ _ _ hi
    · simp only [hc', writeAt_length, tapeOf_length]
      omega
    · refine List.mem_map.2 ⟨t, ?_, rfl⟩
      rw [hread]
      exact ht
  · rintro ⟨c, c', hca, hcb, hfits, hfits', hstep⟩
    obtain ⟨t, ht, hmap⟩ := List.mem_map.1 hstep
    have htape : tapeOf M x s σ a = c.tape := tapeOf_eq_tape hca hfits.tape
    refine ⟨(c.state, c.inHead, c.wHead, c.tape.getD c.wHead false, t), ?_, ?_⟩
    · refine mem_caseList.2 ⟨hfits.state, hfits.inHead, hfits.wHead, ht, ?_, ?_⟩
      · have := hfits'.state
        rw [← hmap] at this
        exact this
      · have := hfits'.wHead
        rw [← hmap] at this
        exact this
    · simp only [stepCase, eval, Bool.and_eq_true]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [eval_cfgF, htape, hca]
      · rw [eval_litF, ← getD_tapeOf M x s σ a hfits.wHead, htape]
      · rw [eval_tgtF, htape, hcb, ← hmap]

/-! ### Size of the step formula -/

theorem size_cfgF_le (a q i j : ℕ) :
    (cfgF M x s a q i j).size ≤ cfgWidth M x s * 5 + 4 := by
  have h : ∀ p ∈ (List.range (cfgWidth M x s)).map (fun l =>
      if l < M.states then litF (a * cfgWidth M x s + l) (decide (l = q))
      else if l < M.states + (x.length + 1) then
        litF (a * cfgWidth M x s + l) (decide (l - M.states = i))
      else if l < M.states + (x.length + 1) + s then tt
      else litF (a * cfgWidth M x s + l)
        (decide (l - (M.states + (x.length + 1) + s) = j))), p.size ≤ 4 := by
    intro p hp
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hp
    by_cases h1 : l < M.states
    · simpa [h1] using le_trans (size_litF_le _ _) (by norm_num)
    · by_cases h2 : l < M.states + (x.length + 1)
      · simpa [h1, h2] using le_trans (size_litF_le _ _) (by norm_num)
      · by_cases h3 : l < M.states + (x.length + 1) + s
        · simp [h1, h2, h3]
        · simpa [h1, h2, h3] using le_trans (size_litF_le _ _) (by norm_num)
  have := size_conjAll_le h
  rw [List.length_map, List.length_range] at this
  simpa [cfgF] using this

theorem size_tgtF_le (a b q' i' j' : ℕ) (w : Bool) (j : ℕ) :
    (tgtF M x s a b q' i' j' w j).size ≤ cfgWidth M x s * 10 + 4 := by
  have h : ∀ p ∈ (List.range (cfgWidth M x s)).map (fun l =>
      if l < M.states then litF (b * cfgWidth M x s + l) (decide (l = q'))
      else if l < M.states + (x.length + 1) then
        litF (b * cfgWidth M x s + l) (decide (l - M.states = i'))
      else if l < M.states + (x.length + 1) + s then
        (if l - (M.states + (x.length + 1)) = j then litF (b * cfgWidth M x s + l) w
          else iffVar (b * cfgWidth M x s + l) (a * cfgWidth M x s + l))
      else litF (b * cfgWidth M x s + l)
        (decide (l - (M.states + (x.length + 1) + s) = j'))), p.size ≤ 9 := by
    intro p hp
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hp
    by_cases h1 : l < M.states
    · simpa [h1] using le_trans (size_litF_le _ _) (by norm_num)
    · by_cases h2 : l < M.states + (x.length + 1)
      · simpa [h1, h2] using le_trans (size_litF_le _ _) (by norm_num)
      · by_cases h3 : l < M.states + (x.length + 1) + s
        · by_cases h4 : l - (M.states + (x.length + 1)) = j
          · simpa [h1, h2, h3, h4] using le_trans (size_litF_le _ _) (by norm_num)
          · simp [h1, h2, h3, h4]
        · simpa [h1, h2, h3] using le_trans (size_litF_le _ _) (by norm_num)
  have := size_conjAll_le h
  rw [List.length_map, List.length_range] at this
  simpa [tgtF] using this

theorem size_stepCase_le (a b q i j : ℕ) (bit : Bool) (t : ℕ × Bool × Dir × Dir) :
    (stepCase M x s a b q i j bit t).size ≤ cfgWidth M x s * 15 + 12 := by
  have h₁ := size_cfgF_le (M := M) (x := x) (s := s) a q i j
  have h₂ := size_tgtF_le (M := M) (x := x) (s := s) a b t.1 (moveIn x.length i t.2.2.1)
    (moveWork j t.2.2.2) t.2.1 j
  have h₃ := size_litF_le (a * cfgWidth M x s + (M.states + (x.length + 1) + j)) bit
  simp only [stepCase, size]
  omega

theorem length_caseList_le :
    (caseList M x s).length ≤ M.states * (x.length + 1) * s * 2 * (M.states * 18) := by
  have h4 : ∀ (q i j : ℕ), ((([false, true] : List Bool)).flatMap fun bit =>
      ((allInstr M.states).filter fun t =>
        decide (t ∈ M.delta q x[i]? bit) && decide (moveWork j t.2.2.2 < s)).map
          fun t => (q, i, j, bit, t)).length ≤ 2 * (M.states * 18) := by
    intro q i j
    have := length_flatMap_le ([false, true] : List Bool) (fun bit =>
      ((allInstr M.states).filter fun t =>
        decide (t ∈ M.delta q x[i]? bit) && decide (moveWork j t.2.2.2 < s)).map
          fun t => (q, i, j, bit, t)) (M.states * 18) ?_
    · simpa using this
    · intro bit _
      refine le_trans ?_ (length_allInstr M.states)
      rw [List.length_map]
      exact List.length_filter_le _ _
  have h3 : ∀ (q i : ℕ), ((List.range s).flatMap fun j =>
      (([false, true] : List Bool)).flatMap fun bit =>
        ((allInstr M.states).filter fun t =>
          decide (t ∈ M.delta q x[i]? bit) && decide (moveWork j t.2.2.2 < s)).map
            fun t => (q, i, j, bit, t)).length ≤ s * (2 * (M.states * 18)) := by
    intro q i
    have := length_flatMap_le (List.range s) _ (2 * (M.states * 18)) fun j _ => h4 q i j
    simpa using this
  have h2 : ∀ q : ℕ, ((List.range (x.length + 1)).flatMap fun i =>
      (List.range s).flatMap fun j =>
        (([false, true] : List Bool)).flatMap fun bit =>
          ((allInstr M.states).filter fun t =>
            decide (t ∈ M.delta q x[i]? bit) && decide (moveWork j t.2.2.2 < s)).map
              fun t => (q, i, j, bit, t)).length
      ≤ (x.length + 1) * (s * (2 * (M.states * 18))) := by
    intro q
    have := length_flatMap_le (List.range (x.length + 1)) _ (s * (2 * (M.states * 18)))
      fun i _ => h3 q i
    simpa using this
  have h1 := length_flatMap_le (List.range M.states) _
    ((x.length + 1) * (s * (2 * (M.states * 18)))) fun q _ => h2 q
  rw [List.length_range] at h1
  refine le_trans h1 (le_of_eq ?_)
  ring

/-- **The step formula is small**: its size is a fixed multiple of the width of a configuration
word times the number of situations of the machine. -/
theorem size_stepF_le (a b : ℕ) :
    (stepF M x s a b).size ≤
      M.states * (x.length + 1) * s * 2 * (M.states * 18) * (cfgWidth M x s * 15 + 13) + 4 := by
  have hlen := length_caseList_le (M := M) (x := x) (s := s)
  have hall : ∀ p ∈ (caseList M x s).map (fun z =>
      stepCase M x s a b z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2),
      p.size ≤ cfgWidth M x s * 15 + 12 := by
    intro p hp
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hp
    exact size_stepCase_le a b z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2
  have h := size_disjAny_le hall
  rw [List.length_map] at h
  have key : cfgWidth M x s * 15 + 12 + 1 = cfgWidth M x s * 15 + 13 := by omega
  rw [key] at h
  exact le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 4)

/-! ### The whole reduction -/

/-- Block `a` carries the word of the padded initial configuration. -/
def initF (M : Machine) (x : List Bool) (s : ℕ) (a : ℕ) : QBF :=
  QBF.conj (cfgF M x s a 0 0 0)
    (conjAll ((List.range s).map fun l =>
      litF (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) false))

/-- The situations an accepting configuration can be in: an accepting control state and a
position of each head. -/
def accCases (M : Machine) (x : List Bool) (s : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((List.range M.states).filter fun q => M.accept q).flatMap fun q =>
    (List.range (x.length + 1)).flatMap fun i =>
      (List.range s).map fun j => (q, i, j)

theorem mem_accCases {q i j : ℕ} :
    (q, i, j) ∈ accCases M x s ↔
      q < M.states ∧ M.accept q = true ∧ i ≤ x.length ∧ j < s := by
  simp only [accCases, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
    Prod.mk.injEq]
  constructor
  · rintro ⟨q', ⟨hq', hacc⟩, i', hi', j', hj', rfl, rfl, rfl⟩
    exact ⟨hq', by simpa using hacc, by omega, hj'⟩
  · rintro ⟨hq, hacc, hi, hj⟩
    exact ⟨q, ⟨hq, by simpa using hacc⟩, i, by omega, j, hj, rfl, rfl, rfl⟩

theorem length_accCases_le :
    (accCases M x s).length ≤ M.states * (x.length + 1) * s := by
  have h2 : ∀ q : ℕ, ((List.range (x.length + 1)).flatMap fun i =>
      (List.range s).map fun j => (q, i, j)).length ≤ (x.length + 1) * s := by
    intro q
    simp
  have h1 := length_flatMap_le ((List.range M.states).filter fun q => M.accept q)
    _ ((x.length + 1) * s) fun q _ => h2 q
  refine le_trans h1 ?_
  have hfil : ((List.range M.states).filter fun q => M.accept q).length ≤ M.states := by
    have := List.length_filter_le (fun q => M.accept q) (List.range M.states)
    simpa using this
  calc ((List.range M.states).filter fun q => M.accept q).length * ((x.length + 1) * s)
      ≤ M.states * ((x.length + 1) * s) := Nat.mul_le_mul_right _ hfil
    _ = M.states * (x.length + 1) * s := by ring

/-- Block `b` carries the word of a configuration in an accepting state. -/
def accF (M : Machine) (x : List Bool) (s : ℕ) (b : ℕ) : QBF :=
  disjAny ((accCases M x s).map fun z => cfgF M x s b z.1 z.2.1 z.2.2)

/-- **The formula of the reduction**: a closed quantified Boolean formula, true exactly when the
machine accepts the input. -/
def machineF (M : Machine) (x : List Bool) (s : ℕ) : QBF :=
  exBits 0 (cfgWidth M x s) (exBits (cfgWidth M x s) (cfgWidth M x s)
    (QBF.conj (QBF.conj (initF M x s 0) (accF M x s 1))
      (reachF (stepF M x s) (cfgWidth M x s) (savitchDepth M x s) 0 1 2)))

theorem eval_initF (σ : ℕ → Bool) (a : ℕ) :
    (initF M x s a).eval σ = true ↔
      blockVal (cfgWidth M x s) σ a = cfgWord M x s (pad s init) := by
  have hpi : (pad s init).tape = padTape s ([] : List Bool) := rfl
  have hrec : (⟨0, 0, (pad s init).tape, 0⟩ : Config) = pad s init := rfl
  have hzero : ∀ i, i < s → (padTape s ([] : List Bool)).getD i false = false := by
    intro i hi
    rw [getD_padTape s [] hi]
    simp
  rw [initF]
  simp only [eval, Bool.and_eq_true]
  rw [eval_cfgF, eval_conjAll_range]
  constructor
  · rintro ⟨h1, h2⟩
    have ht : tapeOf M x s σ a = (pad s init).tape := by
      refine List.ext_getElem (by simp) ?_
      intro i hi1 hi2
      have hi : i < s := by simpa using hi1
      have h3 := h2 i hi
      rw [eval_litF] at h3
      have e1 : (tapeOf M x s σ a).getD i false = false := by
        rw [getD_tapeOf M x s σ a hi]; exact h3
      have e2 : ((pad s init).tape).getD i false = false := by
        rw [hpi]; exact hzero i hi
      rw [List.getD_eq_getElem _ _ hi1] at e1
      rw [List.getD_eq_getElem _ _ hi2] at e2
      rw [e1, e2]
    rw [h1, ht, hrec]
  · intro h
    have ht : tapeOf M x s σ a = (pad s init).tape :=
      tapeOf_eq_tape h (by simp)
    refine ⟨by rw [ht, hrec, h], ?_⟩
    intro l hl
    rw [eval_litF, ← getD_tapeOf M x s σ a hl, ht, hpi]
    exact hzero l hl

theorem eval_accF (σ : ℕ → Bool) (b : ℕ) :
    (accF M x s b).eval σ = true ↔
      ∃ c : Config, Fits M x s c ∧ M.accept c.state = true ∧
        blockVal (cfgWidth M x s) σ b = cfgWord M x s c := by
  rw [accF, eval_disjAny_map]
  constructor
  · rintro ⟨⟨q, i, j⟩, hz, hev⟩
    obtain ⟨hq, hacc, hi, hj⟩ := mem_accCases.1 hz
    rw [eval_cfgF] at hev
    exact ⟨⟨q, i, tapeOf M x s σ b, j⟩, ⟨hq, hi, by simp, hj⟩, hacc, hev⟩
  · rintro ⟨c, hfits, hacc, hval⟩
    refine ⟨(c.state, c.inHead, c.wHead),
      mem_accCases.2 ⟨hfits.state, hacc, hfits.inHead, hfits.wHead⟩, ?_⟩
    rw [eval_cfgF, tapeOf_eq_tape hval hfits.tape, hval]

/-- **The reduction is correct.** -/
theorem eval_machineF (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) (hs : 0 < s)
    (σ : ℕ → Bool) : (machineF M x s).eval σ = true ↔ M.Accepts x := by
  have hinit : Fits M x s (pad s init) := ⟨hwf.1, Nat.zero_le _, by simp, hs⟩
  have hblocks : ∀ w0 w1 : List Bool, w0.length = cfgWidth M x s →
      w1.length = cfgWidth M x s →
      blockVal (cfgWidth M x s)
          (setBits (setBits σ 0 w0) (cfgWidth M x s) w1) 0 = w0 ∧
        blockVal (cfgWidth M x s)
          (setBits (setBits σ 0 w0) (cfgWidth M x s) w1) 1 = w1 := by
    intro w0 w1 h0 h1
    have k1 : blockVal (cfgWidth M x s)
        (setBits (setBits σ 0 w0) (1 * cfgWidth M x s) w1) 1 = w1 :=
      blockVal_setBits_self _ _ 1 w1 h1
    have k0 : blockVal (cfgWidth M x s)
        (setBits (setBits σ 0 w0) (1 * cfgWidth M x s) w1) 0 =
          blockVal (cfgWidth M x s) (setBits σ 0 w0) 0 :=
      blockVal_setBits_of_ne _ _ 1 0 w1 h1 (by omega)
    have k00 : blockVal (cfgWidth M x s) (setBits σ (0 * cfgWidth M x s) w0) 0 = w0 :=
      blockVal_setBits_self _ _ 0 w0 h0
    rw [one_mul] at k1 k0
    rw [zero_mul] at k00
    exact ⟨by rw [k0, k00], k1⟩
  rw [machineF, eval_exBits]
  constructor
  · rintro ⟨w0, hw0, h⟩
    rw [eval_exBits] at h
    obtain ⟨w1, hw1, h⟩ := h
    obtain ⟨hb0, hb1⟩ := hblocks w0 w1 hw0 hw1
    simp only [eval, Bool.and_eq_true] at h
    obtain ⟨⟨hi, ha⟩, hr⟩ := h
    rw [eval_initF, hb0] at hi
    rw [eval_accF, hb1] at ha
    obtain ⟨c, hfits, hacc, hcw⟩ := ha
    rw [eval_reachF (R := WordStep M x s) (fun τ u v => eval_stepF τ u v)
      (fun u v huv _ => (wordStep_length huv).2) _ _ _ _ _ (by omega) (by omega),
      hb0, hb1, hi, hcw, reachLe_wordStep_iff hinit hfits] at hr
    exact (accepts_iff_reachLe_padStep hwf hsp).2 ⟨c, hacc, hr⟩
  · intro hacc
    obtain ⟨c, haccc, hr⟩ := (accepts_iff_reachLe_padStep hwf hsp).1 hacc
    have hfits : Fits M x s c := by
      obtain ⟨n, -, hn⟩ := hr
      exact fits_of_steps_padStep hinit n hn
    refine ⟨cfgWord M x s (pad s init), by simp, ?_⟩
    rw [eval_exBits]
    refine ⟨cfgWord M x s c, by simp, ?_⟩
    obtain ⟨hb0, hb1⟩ := hblocks (cfgWord M x s (pad s init)) (cfgWord M x s c)
      (by simp) (by simp)
    simp only [eval, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [eval_initF, hb0]
    · rw [eval_accF, hb1]
      exact ⟨c, hfits, haccc, rfl⟩
    · rw [eval_reachF (R := WordStep M x s) (fun τ u v => eval_stepF τ u v)
        (fun u v huv _ => (wordStep_length huv).2) _ _ _ _ _ (by omega) (by omega),
        hb0, hb1, reachLe_wordStep_iff hinit hfits]
      exact hr

theorem size_initF_le (a : ℕ) :
    (initF M x s a).size ≤ (cfgWidth M x s * 5 + 4) + (s * 3 + 4) + 1 := by
  have h1 := size_cfgF_le (M := M) (x := x) (s := s) a 0 0 0
  have h2 : (conjAll ((List.range s).map fun l =>
      litF (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) false)).size ≤ s * 3 + 4 := by
    have h : ∀ p ∈ (List.range s).map (fun l =>
        litF (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) false), p.size ≤ 2 := by
      intro p hp
      obtain ⟨l, -, rfl⟩ := List.mem_map.1 hp
      exact size_litF_le _ _
    have := size_conjAll_le h
    rw [List.length_map, List.length_range] at this
    omega
  simp only [initF, size]
  omega

theorem size_accF_le (b : ℕ) :
    (accF M x s b).size ≤ M.states * (x.length + 1) * s * (cfgWidth M x s * 5 + 5) + 4 := by
  have hall : ∀ p ∈ (accCases M x s).map (fun z => cfgF M x s b z.1 z.2.1 z.2.2),
      p.size ≤ cfgWidth M x s * 5 + 4 := by
    intro p hp
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hp
    exact size_cfgF_le _ _ _ _
  have h := size_disjAny_le hall
  rw [List.length_map] at h
  have key : cfgWidth M x s * 5 + 4 + 1 = cfgWidth M x s * 5 + 5 := by omega
  rw [key] at h
  exact le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right _ length_accCases_le) 4)

/-- **The formula of the reduction is small.** -/
theorem size_machineF_le :
    (machineF M x s).size ≤
      (M.states * (x.length + 1) * s * 2 * (M.states * 18) * (cfgWidth M x s * 15 + 13) + 4)
        + 10 * cfgWidth M x s + 5
        + savitchDepth M x s * (43 * cfgWidth M x s + 21)
        + (cfgWidth M x s * 5 + 4) + (s * 3 + 4) + 1
        + (M.states * (x.length + 1) * s * (cfgWidth M x s * 5 + 5) + 4)
        + 2 * cfgWidth M x s + 2 := by
  have hreach := size_reachF_le (stepF := stepF M x s) (m := cfgWidth M x s)
    (c := M.states * (x.length + 1) * s * 2 * (M.states * 18) * (cfgWidth M x s * 15 + 13) + 4)
    (fun a b => size_stepF_le a b) (savitchDepth M x s) 0 1 2
  have hi := size_initF_le (M := M) (x := x) (s := s) 0
  have ha := size_accF_le (M := M) (x := x) (s := s) 1
  simp only [machineF, size_exBits, size]
  set W := cfgWidth M x s with hW
  set A := M.states * (x.length + 1) * s * 2 * (M.states * 18) * (W * 15 + 13) with hA
  set B := M.states * (x.length + 1) * s * (W * 5 + 5) with hB
  set C := savitchDepth M x s * (43 * W + 21) with hC
  omega

end QBF

end Complexity.Qbf
