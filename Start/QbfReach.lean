/-
**Bounded reachability as a quantified Boolean formula.**

`Start/SavitchReach.lean` proves the midpoint identity — reachability within `2 ^ (k + 1)` steps
is reachability within `2 ^ k` steps to a midpoint and from it — and `Start/SavitchVM.lean` runs
that recursion on a machine.  The same identity is what makes `TQBF` hard for polynomial space:
written as a formula, the midpoint recursion costs only *one* new block of variables per level,
because the two legs are shared by a universal quantifier over a pair of endpoints instead of
being written twice.  This module performs that construction and proves it correct.

Vertices are words of `m` bits, read off an assignment in *blocks*: block `i` is the variables
`i * m, …, i * m + m - 1`.  The edge relation enters as a family of formulas `stepF a b`, one for
each pair of blocks, which is assumed to express the relation of the words in those blocks; the
construction and its correctness proof do not otherwise depend on it.

Main definitions:

* `Complexity.Qbf.blockVal`, `Complexity.Qbf.setBits` — reading a block of an assignment, and
  overwriting a block with a word;
* `Complexity.Qbf.QBF.allBits`, `Complexity.Qbf.QBF.exBits` — quantification over a block;
* `Complexity.Qbf.QBF.eqBlock` — two blocks carry the same word;
* `Complexity.Qbf.QBF.reachF` — **the formula**: `reachF stepF m k a b t` says that the word in
  block `a` reaches the word in block `b` within `2 ^ k` steps, using the blocks from `t` on as
  scratch space.

Main results:

* `Complexity.Qbf.QBF.eval_allBits`, `Complexity.Qbf.QBF.eval_exBits` — quantifying over a block
  is quantifying over a word of that width;
* `Complexity.Qbf.QBF.eval_eqBlock` — the equality formula is correct;
* `Complexity.Qbf.QBF.eval_reachF` — **the formula is correct**: it holds exactly when the two
  words are joined by a walk of at most `2 ^ k` edges, in the sense of
  `Complexity.Reach.reachLe`;
* `Complexity.Qbf.QBF.size_reachF_le` — **the formula is small**: its size is bounded by the size
  of one step formula plus `k * (43 * m + 21) + 10 * m + 5`, so it is polynomial in the width of
  a vertex and in the depth of the recursion.

Together these say that bounded reachability in a graph whose vertices are `m`-bit words and
whose edge relation is expressed by formulas of size `c` is expressed by a quantified Boolean
formula of size `O(c + k * m)`.  This is the half of the PSPACE-hardness of `TQBF` that is about
formulas; the other half — that the configuration graph of a space-bounded machine has such a
step formula, computed in polynomial time — is not formalised here.
-/

import Start.Qbf
import Start.SavitchReach

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

/-! ### Blocks of an assignment -/

/-- The word held by block `i` of width `m`: the bits at the variables `i * m, …, i * m + m - 1`,
in that order. -/
def blockVal (m : ℕ) (σ : ℕ → Bool) (i : ℕ) : List Bool :=
  (List.range m).map fun l => σ (i * m + l)

@[simp] theorem blockVal_length (m : ℕ) (σ : ℕ → Bool) (i : ℕ) :
    (blockVal m σ i).length = m := by simp [blockVal]

@[simp] theorem blockVal_getElem (m : ℕ) (σ : ℕ → Bool) (i l : ℕ)
    (h : l < (blockVal m σ i).length) : (blockVal m σ i)[l] = σ (i * m + l) := by
  simp [blockVal]

theorem blockVal_getD (m : ℕ) (σ : ℕ → Bool) (i l : ℕ) (hl : l < m) :
    (blockVal m σ i).getD l false = σ (i * m + l) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hl), blockVal_getElem]

/-- Two blocks are equal exactly when they agree bit by bit. -/
theorem blockVal_eq_iff (m : ℕ) (σ τ : ℕ → Bool) (i j : ℕ) :
    blockVal m σ i = blockVal m τ j ↔ ∀ l < m, σ (i * m + l) = τ (j * m + l) := by
  constructor
  · intro h l hl
    rw [← blockVal_getD m σ i l hl, ← blockVal_getD m τ j l hl, h]
  · intro h
    refine List.ext_getElem (by simp) ?_
    intro l h₁ h₂
    rw [blockVal_getElem, blockVal_getElem]
    exact h l (by simpa using h₁)

/-- Overwriting the variables `o, o + 1, …` with the bits of `w`. -/
def setBits (σ : ℕ → Bool) (o : ℕ) : List Bool → (ℕ → Bool)
  | [] => σ
  | b :: w => setBits (Function.update σ o b) (o + 1) w

@[simp] theorem setBits_nil (σ : ℕ → Bool) (o : ℕ) : setBits σ o [] = σ := rfl

theorem setBits_cons (σ : ℕ → Bool) (o : ℕ) (b : Bool) (w : List Bool) :
    setBits σ o (b :: w) = setBits (Function.update σ o b) (o + 1) w := rfl

theorem setBits_of_lt (σ : ℕ → Bool) (o : ℕ) (w : List Bool) (j : ℕ) (hj : j < o) :
    setBits σ o w j = σ j := by
  induction w generalizing σ o with
  | nil => rfl
  | cons b w ih =>
      rw [setBits_cons, ih _ _ (by omega)]
      exact Function.update_of_ne (by omega) _ _

theorem setBits_of_ge (σ : ℕ → Bool) (o : ℕ) (w : List Bool) (j : ℕ) (hj : o + w.length ≤ j) :
    setBits σ o w j = σ j := by
  induction w generalizing σ o with
  | nil => rfl
  | cons b w ih =>
      rw [setBits_cons, ih _ _ (by simp at hj ⊢; omega)]
      exact Function.update_of_ne (by simp at hj; omega) _ _

theorem setBits_getD (σ : ℕ → Bool) (o : ℕ) (w : List Bool) (l : ℕ) (hl : l < w.length) :
    setBits σ o w (o + l) = w.getD l false := by
  induction w generalizing σ o l with
  | nil => simp at hl
  | cons b w ih =>
      cases l with
      | zero =>
          rw [setBits_cons, setBits_of_lt _ _ _ _ (by omega)]
          simp
      | succ l =>
          have h : o + (l + 1) = o + 1 + l := by omega
          rw [setBits_cons, h, ih (Function.update σ o b) (o + 1) l (by simpa using hl)]
          simp

/-- Reading back the block that was just written. -/
theorem blockVal_setBits_self (m : ℕ) (σ : ℕ → Bool) (i : ℕ) (w : List Bool)
    (hw : w.length = m) : blockVal m (setBits σ (i * m) w) i = w := by
  refine List.ext_getElem (by simp [hw]) ?_
  intro l h₁ h₂
  have hl : l < m := by simpa using h₁
  rw [blockVal_getElem, setBits_getD _ _ _ _ (by omega), List.getD_eq_getElem _ _ h₂]

/-- Writing a block leaves the other blocks alone. -/
theorem blockVal_setBits_of_ne (m : ℕ) (σ : ℕ → Bool) (i j : ℕ) (w : List Bool)
    (hw : w.length = m) (hij : i ≠ j) : blockVal m (setBits σ (i * m) w) j = blockVal m σ j := by
  rw [blockVal_eq_iff]
  intro l hl
  rcases Nat.lt_or_ge j i with h | h
  · refine setBits_of_lt _ _ _ _ ?_
    have : (j + 1) * m ≤ i * m := Nat.mul_le_mul_right m (by omega)
    rw [Nat.succ_mul] at this
    omega
  · have hji : i < j := lt_of_le_of_ne h hij
    refine setBits_of_ge _ _ _ _ ?_
    have : (i + 1) * m ≤ j * m := Nat.mul_le_mul_right m (by omega)
    rw [Nat.succ_mul] at this
    rw [hw]
    omega

namespace QBF

/-! ### Quantifying over a block -/

/-- Universal quantification over the variables `o, …, o + n - 1`. -/
def allBits (o : ℕ) : ℕ → QBF → QBF
  | 0, p => p
  | n + 1, p => QBF.all o (allBits (o + 1) n p)

/-- Existential quantification over the variables `o, …, o + n - 1`. -/
def exBits (o : ℕ) : ℕ → QBF → QBF
  | 0, p => p
  | n + 1, p => QBF.ex o (exBits (o + 1) n p)

@[simp] theorem size_allBits (o n : ℕ) (p : QBF) : (allBits o n p).size = p.size + n := by
  induction n generalizing o with
  | zero => simp [allBits]
  | succ n ih => simp [allBits, size, ih]; omega

@[simp] theorem size_exBits (o n : ℕ) (p : QBF) : (exBits o n p).size = p.size + n := by
  induction n generalizing o with
  | zero => simp [exBits]
  | succ n ih => simp [exBits, size, ih]; omega

/-- Quantifying universally over a block is quantifying over a word of that width. -/
theorem eval_allBits (o n : ℕ) (p : QBF) (σ : ℕ → Bool) :
    (allBits o n p).eval σ = true ↔
      ∀ w : List Bool, w.length = n → p.eval (setBits σ o w) = true := by
  induction n generalizing o σ with
  | zero =>
      simp only [allBits]
      constructor
      · intro h w hw
        rw [List.length_eq_zero_iff.1 hw, setBits_nil]
        exact h
      · intro h
        simpa using h [] rfl
  | succ n ih =>
      simp only [allBits, eval, Bool.and_eq_true]
      constructor
      · rintro ⟨h₀, h₁⟩ w hw
        match w with
        | [] => simp at hw
        | b :: w =>
            rw [setBits_cons]
            cases b with
            | false => exact (ih (o + 1) _).1 h₀ w (by simpa using hw)
            | true => exact (ih (o + 1) _).1 h₁ w (by simpa using hw)
      · intro h
        constructor
        · refine (ih (o + 1) _).2 fun w hw => ?_
          simpa [setBits_cons] using h (false :: w) (by simp [hw])
        · refine (ih (o + 1) _).2 fun w hw => ?_
          simpa [setBits_cons] using h (true :: w) (by simp [hw])

/-- Quantifying existentially over a block is quantifying over a word of that width. -/
theorem eval_exBits (o n : ℕ) (p : QBF) (σ : ℕ → Bool) :
    (exBits o n p).eval σ = true ↔
      ∃ w : List Bool, w.length = n ∧ p.eval (setBits σ o w) = true := by
  induction n generalizing o σ with
  | zero =>
      simp only [exBits]
      constructor
      · intro h; exact ⟨[], rfl, h⟩
      · rintro ⟨w, hw, h⟩
        rwa [List.length_eq_zero_iff.1 hw, setBits_nil] at h
  | succ n ih =>
      simp only [exBits, eval, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · obtain ⟨w, hw, h⟩ := (ih (o + 1) _).1 h
          exact ⟨false :: w, by simp [hw], by rwa [setBits_cons]⟩
        · obtain ⟨w, hw, h⟩ := (ih (o + 1) _).1 h
          exact ⟨true :: w, by simp [hw], by rwa [setBits_cons]⟩
      · rintro ⟨w, hw, h⟩
        match w with
        | [] => simp at hw
        | b :: w =>
            rw [setBits_cons] at h
            cases b with
            | false => exact Or.inl ((ih (o + 1) _).2 ⟨w, by simpa using hw, h⟩)
            | true => exact Or.inr ((ih (o + 1) _).2 ⟨w, by simpa using hw, h⟩)

/-! ### Equality of blocks -/

/-- The formula that is always true. -/
def tt : QBF := QBF.disj (QBF.var 0) (QBF.neg (QBF.var 0))

@[simp] theorem eval_tt (σ : ℕ → Bool) : tt.eval σ = true := by
  simp only [tt, eval]
  cases σ 0 <;> rfl

@[simp] theorem size_tt : tt.size = 4 := rfl

/-- The conjunction of a list of formulas. -/
def conjAll : List QBF → QBF
  | [] => tt
  | p :: ps => QBF.conj p (conjAll ps)

theorem eval_conjAll (σ : ℕ → Bool) : ∀ ps : List QBF,
    (conjAll ps).eval σ = true ↔ ∀ p ∈ ps, p.eval σ = true
  | [] => by simp [conjAll]
  | p :: ps => by
      simp only [conjAll, eval, Bool.and_eq_true, eval_conjAll σ ps, List.mem_cons]
      constructor
      · rintro ⟨h₀, h₁⟩ q (rfl | hq)
        · exact h₀
        · exact h₁ q hq
      · intro h
        exact ⟨h p (Or.inl rfl), fun q hq => h q (Or.inr hq)⟩

/-- Two variables carry the same bit. -/
def iffVar (i j : ℕ) : QBF :=
  QBF.disj (QBF.conj (QBF.var i) (QBF.var j))
    (QBF.conj (QBF.neg (QBF.var i)) (QBF.neg (QBF.var j)))

@[simp] theorem eval_iffVar (σ : ℕ → Bool) (i j : ℕ) :
    (iffVar i j).eval σ = true ↔ σ i = σ j := by
  simp only [iffVar, eval]
  cases σ i <;> cases σ j <;> simp

@[simp] theorem size_iffVar (i j : ℕ) : (iffVar i j).size = 9 := rfl

/-- The blocks `i` and `j` of width `m` carry the same word. -/
def eqBlock (m i j : ℕ) : QBF :=
  conjAll ((List.range m).map fun l => iffVar (i * m + l) (j * m + l))

theorem eval_eqBlock (m i j : ℕ) (σ : ℕ → Bool) :
    (eqBlock m i j).eval σ = true ↔ blockVal m σ i = blockVal m σ j := by
  rw [eqBlock, eval_conjAll, blockVal_eq_iff]
  constructor
  · intro h l hl
    exact (eval_iffVar σ _ _).1 (h _ (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))
  · intro h q hq
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
    exact (eval_iffVar σ _ _).2 (h l (List.mem_range.1 hl))

/-- The size of a conjunction of a list of formulas. -/
theorem size_conjAll : ∀ ps : List QBF,
    (conjAll ps).size = (ps.map fun p => p.size + 1).sum + 4
  | [] => by simp [conjAll]
  | p :: ps => by
      simp only [conjAll, size, size_conjAll ps, List.map_cons, List.sum_cons]
      omega

theorem sum_map_const_range (c m : ℕ) : ((List.range m).map fun _ : ℕ => c).sum = c * m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      simp
      ring

theorem size_eqBlock (m i j : ℕ) : (eqBlock m i j).size = 10 * m + 4 := by
  rw [eqBlock, size_conjAll]
  have hmap : ((List.range m).map fun l => iffVar (i * m + l) (j * m + l)).map
      (fun p => p.size + 1) = (List.range m).map fun _ => 10 := by
    simp [List.map_map, Function.comp_def]
  rw [hmap, sum_map_const_range]

/-! ### The reachability formula -/

/-- Implication. -/
def imp (p q : QBF) : QBF := QBF.disj (QBF.neg p) q

@[simp] theorem eval_imp (σ : ℕ → Bool) (p q : QBF) :
    (imp p q).eval σ = true ↔ (p.eval σ = true → q.eval σ = true) := by
  simp only [imp, eval, Bool.or_eq_true, Bool.not_eq_true']
  cases p.eval σ <;> simp

@[simp] theorem size_imp (p q : QBF) : (imp p q).size = p.size + q.size + 2 := by
  simp only [imp, size]; omega

/-- **The formula**: `reachF stepF m k a b t` says that the `m`-bit word in block `a` reaches the
word in block `b` by a walk of at most `2 ^ k` edges.  The blocks `t, t + 1, t + 2, …` are the
scratch space of the recursion: `t` holds the midpoint, and `t + 1`, `t + 2` are the two
endpoints of the single recursive call that stands for both legs. -/
def reachF (stepF : ℕ → ℕ → QBF) (m : ℕ) : ℕ → ℕ → ℕ → ℕ → QBF
  | 0, a, b, _ => QBF.disj (eqBlock m a b) (stepF a b)
  | k + 1, a, b, t =>
      exBits (t * m) m (allBits ((t + 1) * m) m (allBits ((t + 2) * m) m
        (imp (QBF.disj (QBF.conj (eqBlock m (t + 1) a) (eqBlock m (t + 2) t))
                       (QBF.conj (eqBlock m (t + 1) t) (eqBlock m (t + 2) b)))
             (reachF stepF m k (t + 1) (t + 2) (t + 3)))))

theorem reachF_zero (stepF : ℕ → ℕ → QBF) (m a b t : ℕ) :
    reachF stepF m 0 a b t = QBF.disj (eqBlock m a b) (stepF a b) := rfl

theorem reachF_succ (stepF : ℕ → ℕ → QBF) (m k a b t : ℕ) :
    reachF stepF m (k + 1) a b t =
      exBits (t * m) m (allBits ((t + 1) * m) m (allBits ((t + 2) * m) m
        (imp (QBF.disj (QBF.conj (eqBlock m (t + 1) a) (eqBlock m (t + 2) t))
                       (QBF.conj (eqBlock m (t + 1) t) (eqBlock m (t + 2) b)))
             (reachF stepF m k (t + 1) (t + 2) (t + 3))))) := rfl

/-- Along a walk of the edge relation of `m`-bit words, every vertex is an `m`-bit word. -/
theorem length_of_reachLe {R : List Bool → List Bool → Prop} {m : ℕ}
    (hlen : ∀ u v, R u v → u.length = m → v.length = m) :
    ∀ (k : ℕ) (u v : List Bool), Reach.reachLe R k u v → u.length = m → v.length = m := by
  have hsteps : ∀ (n : ℕ) (u v : List Bool), Reach.steps R n u v → u.length = m →
      v.length = m := by
    intro n
    induction n with
    | zero => rintro u v rfl hu; exact hu
    | succ n ih =>
        rintro u v ⟨w, hw, hwv⟩ hu
        exact hlen _ _ hwv (ih _ _ hw hu)
  rintro k u v ⟨n, -, h⟩ hu
  exact hsteps n u v h hu

/-- **The formula is correct**: it holds exactly when the word in block `a` reaches the word in
block `b` within `2 ^ k` steps.  The only hypothesis on the family of step formulas is that
`stepF a b` expresses the edge relation between the words in blocks `a` and `b`; the scratch
blocks are those from `t` on, so the two endpoints must lie below `t`. -/
theorem eval_reachF {R : List Bool → List Bool → Prop} {stepF : ℕ → ℕ → QBF} {m : ℕ}
    (hstep : ∀ (σ : ℕ → Bool) (a b : ℕ),
      (stepF a b).eval σ = true ↔ R (blockVal m σ a) (blockVal m σ b))
    (hlen : ∀ u v, R u v → u.length = m → v.length = m) :
    ∀ (k a b t : ℕ) (σ : ℕ → Bool), a < t → b < t →
      ((reachF stepF m k a b t).eval σ = true ↔
        Reach.reachLe R k (blockVal m σ a) (blockVal m σ b)) := by
  intro k
  induction k with
  | zero =>
      intro a b t σ _ _
      rw [reachF_zero, Reach.reachLe_zero_iff]
      simp only [eval, Bool.or_eq_true, eval_eqBlock, hstep]
  | succ k ih =>
      intro a b t σ ha hb
      -- the values of the two endpoints, which the scratch blocks never touch
      set va := blockVal m σ a with hva
      set vb := blockVal m σ b with hvb
      -- the inner formula, for a fixed midpoint `wz`
      have key : ∀ wz : List Bool, wz.length = m →
          ((allBits ((t + 1) * m) m (allBits ((t + 2) * m) m
            (imp (QBF.disj (QBF.conj (eqBlock m (t + 1) a) (eqBlock m (t + 2) t))
                           (QBF.conj (eqBlock m (t + 1) t) (eqBlock m (t + 2) b)))
                 (reachF stepF m k (t + 1) (t + 2) (t + 3))))).eval
              (setBits σ (t * m) wz) = true ↔
            (Reach.reachLe R k va wz ∧ Reach.reachLe R k wz vb)) := by
        intro wz hwz
        -- abbreviations for the three nested writes
        have hσz : ∀ (i : ℕ), i < t → blockVal m (setBits σ (t * m) wz) i = blockVal m σ i :=
          fun i hi => blockVal_setBits_of_ne m σ t i wz hwz (by omega)
        rw [eval_allBits]
        constructor
        · intro h
          have hmain : ∀ wu wv : List Bool, wu.length = m → wv.length = m →
              ((blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) (t + 1) =
                 blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) a ∧
                blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) (t + 2) =
                 blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) t) ∨
               (blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) (t + 1) =
                 blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) t ∧
                blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) (t + 2) =
                 blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) b)) →
                Reach.reachLe R k wu wv := by
            intro wu wv hwu hwv hguard
            have h1 := (eval_allBits _ _ _ _).1 (h wu hwu) wv hwv
            rw [eval_imp] at h1
            have h2 : (QBF.disj (QBF.conj (eqBlock m (t + 1) a) (eqBlock m (t + 2) t))
                (QBF.conj (eqBlock m (t + 1) t) (eqBlock m (t + 2) b))).eval
                (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
                  ((t + 2) * m) wv) = true := by
              simp only [eval, Bool.or_eq_true, Bool.and_eq_true, eval_eqBlock]
              exact hguard
            have h3 := (ih (t + 1) (t + 2) (t + 3) _ (by omega) (by omega)).1 (h1 h2)
            rwa [blockVal_setBits_of_ne m _ (t + 2) (t + 1) wv hwv (by omega),
              blockVal_setBits_self m _ (t + 1) wu hwu,
              blockVal_setBits_self m _ (t + 2) wv hwv] at h3
          have hlva : va.length = m := by rw [hva]; simp
          have hlvb : vb.length = m := by rw [hvb]; simp
          constructor
          · refine hmain va wz hlva hwz (Or.inl ⟨?_, ?_⟩)
            · rw [blockVal_setBits_of_ne m _ (t + 2) (t + 1) _ hwz (by omega),
                blockVal_setBits_self m _ (t + 1) _ hlva,
                blockVal_setBits_of_ne m _ (t + 2) a _ hwz (by omega),
                blockVal_setBits_of_ne m _ (t + 1) a _ hlva (by omega), hσz a ha]
            · rw [blockVal_setBits_self m _ (t + 2) _ hwz,
                blockVal_setBits_of_ne m _ (t + 2) t _ hwz (by omega),
                blockVal_setBits_of_ne m _ (t + 1) t _ hlva (by omega),
                blockVal_setBits_self m σ t wz hwz]
          · refine hmain wz vb hwz hlvb (Or.inr ⟨?_, ?_⟩)
            · rw [blockVal_setBits_of_ne m _ (t + 2) (t + 1) _ hlvb (by omega),
                blockVal_setBits_self m _ (t + 1) _ hwz,
                blockVal_setBits_of_ne m _ (t + 2) t _ hlvb (by omega),
                blockVal_setBits_of_ne m _ (t + 1) t _ hwz (by omega),
                blockVal_setBits_self m σ t wz hwz]
            · rw [blockVal_setBits_self m _ (t + 2) _ hlvb,
                blockVal_setBits_of_ne m _ (t + 2) b _ hlvb (by omega),
                blockVal_setBits_of_ne m _ (t + 1) b _ hwz (by omega), hσz b hb]
        · rintro ⟨h₁, h₂⟩ wu hwu
          rw [eval_allBits]
          intro wv hwv
          rw [eval_imp]
          intro hg
          have hb1 : blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
              ((t + 2) * m) wv) (t + 1) = wu := by
            rw [blockVal_setBits_of_ne m _ (t + 2) (t + 1) wv hwv (by omega),
              blockVal_setBits_self m _ (t + 1) wu hwu]
          have hb2 : blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
              ((t + 2) * m) wv) (t + 2) = wv :=
            blockVal_setBits_self m _ (t + 2) wv hwv
          have hbz : blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
              ((t + 2) * m) wv) t = wz := by
            rw [blockVal_setBits_of_ne m _ (t + 2) t wv hwv (by omega),
              blockVal_setBits_of_ne m _ (t + 1) t wu hwu (by omega),
              blockVal_setBits_self m σ t wz hwz]
          have hba : blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
              ((t + 2) * m) wv) a = va := by
            rw [blockVal_setBits_of_ne m _ (t + 2) a wv hwv (by omega),
              blockVal_setBits_of_ne m _ (t + 1) a wu hwu (by omega), hσz a ha]
          have hbb : blockVal m (setBits (setBits (setBits σ (t * m) wz) ((t + 1) * m) wu)
              ((t + 2) * m) wv) b = vb := by
            rw [blockVal_setBits_of_ne m _ (t + 2) b wv hwv (by omega),
              blockVal_setBits_of_ne m _ (t + 1) b wu hwu (by omega), hσz b hb]
          simp only [eval, Bool.or_eq_true, Bool.and_eq_true, eval_eqBlock, hb1, hb2, hbz, hba,
            hbb] at hg
          refine (ih (t + 1) (t + 2) (t + 3) _ (by omega) (by omega)).2 ?_
          rw [hb1, hb2]
          rcases hg with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · rw [hu, hv]; exact h₁
          · rw [hu, hv]; exact h₂
      -- now assemble
      rw [reachF_succ, eval_exBits, Reach.reachLe_succ_iff]
      constructor
      · rintro ⟨wz, hwz, h⟩
        exact ⟨wz, (key wz hwz).1 h⟩
      · rintro ⟨z, h₁, h₂⟩
        have hz : z.length = m :=
          length_of_reachLe hlen k va z h₁ (by rw [hva]; simp)
        exact ⟨z, hz, (key z hz).2 ⟨h₁, h₂⟩⟩

/-- **The formula is small**: its size grows by a fixed multiple of the width of a vertex per
level of the recursion. -/
theorem size_reachF_le {stepF : ℕ → ℕ → QBF} {m c : ℕ} (hc : ∀ a b, (stepF a b).size ≤ c) :
    ∀ (k a b t : ℕ), (reachF stepF m k a b t).size ≤ c + 10 * m + 5 + k * (43 * m + 21) := by
  intro k
  induction k with
  | zero =>
      intro a b t
      have := hc a b
      simp only [reachF_zero, size, size_eqBlock]
      omega
  | succ k ih =>
      intro a b t
      have h := ih (t + 1) (t + 2) (t + 3)
      simp only [reachF_succ, size_exBits, size_allBits, size_imp, size, size_eqBlock]
      have : (k + 1) * (43 * m + 21) = k * (43 * m + 21) + (43 * m + 21) := by ring
      omega

/-! ### Non-vacuity -/

/-- The hypotheses of `Complexity.Qbf.QBF.eval_reachF` are satisfiable: the equality relation on
`m`-bit words is expressed by `Complexity.Qbf.QBF.eqBlock`, so the construction applies to it and
the correctness theorem is not vacuous. -/
example (m k a b t : ℕ) (σ : ℕ → Bool) (ha : a < t) (hb : b < t) :
    (reachF (fun i j => eqBlock m i j) m k a b t).eval σ = true ↔
      Reach.reachLe (fun u v : List Bool => u = v) k (blockVal m σ a) (blockVal m σ b) :=
  eval_reachF (fun σ i j => eval_eqBlock m i j σ) (fun _ _ huv hu => huv ▸ hu) k a b t σ ha hb

end QBF

end Complexity.Qbf
