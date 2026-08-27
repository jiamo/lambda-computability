/-
# Compiling a bounded recursion into a P-uniform family

`Start/UniformSigFlat.lean` compiles every term of the Cobham algebra **except** the bounded
recursion.  This module supplies the missing shape: a term `Cob.bRec g h₀ h₁ bd`, whose value is
defined by recursion on the *head* of its first argument, is realized by a P-uniform family of
circuits, provided its four subterms are.

The construction is a loop, run by `Complexity.sigListUniformB_iter`.  Its state is a tuple of
`p + 3` words `[z, y, v] ++ rest`: the bits of the recursion argument still to be consumed — held
back to front, as `Start/UniformSigRev.lean` produces them — the prefix already consumed, the value
of the recursion at that prefix, and the parameters.  One round moves one bit from `z` to the front
of `y` and updates `v` by the step term the bit selects, truncated to the length the bound term
prescribes; when `z` is empty the round is a no-op, so the loop settles.  After the promised number
of rounds the state is `[[], x, R (x :: rest)] ++ rest`, and the answer is read off the third
entry.

Main definitions:

* `Complexity.projsW` — a list of projections, as word functions;
* `Complexity.brecStep`, `Complexity.brecStage` — one round of the loop;
* `Complexity.brecBase`, `Complexity.brecFinal` — the initial and the final state.

Main results:

* `Complexity.iterate_brecStage` — after `j` rounds the state holds the recursion at the last `j`
  bits of the argument;
* `Complexity.length_eval_bRec_le` — the value of a bounded recursion is no longer than the bound
  term allows;
* `Complexity.sigUniformB_bRec` — **a bounded recursion is realized** whenever its subterms are.
-/

import Start.UniformSigRev

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### Small lemmas on words and tuples -/

/-- An entry of a tuple of short words is short, whether or not the index exists. -/
theorem length_getD_le_of_forall {st : List Word} {B : ℕ}
    (h : ∀ u ∈ st, u.length ≤ B) (i : ℕ) : (st.getD i []).length ≤ B := by
  by_cases hi : i < st.length
  · refine h _ ?_
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · have hnil : st.getD i [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    rw [hnil]
    simp

/-- The multiplexer returns one of its two branches. -/
theorem length_muxW_le (a b c : Word) : (muxW a b c).length ≤ max b.length c.length := by
  unfold muxW
  split_ifs <;> simp

/-- Reading a tuple by its indices returns the tuple. -/
theorem map_getD_range_self (l : List Word) (p : ℕ) (h : l.length = p) :
    (List.range p).map (fun i => l.getD i []) = l := by
  refine List.ext_getElem (by simp [h]) ?_
  intro i h1 h2
  have hi : i < p := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- Reading a window of a tuple by its indices. -/
theorem map_getD_range_add (l : List Word) (d p : ℕ) (h : l.length = d + p) :
    (List.range p).map (fun i => l.getD (i + d) []) = l.drop d := by
  refine List.ext_getElem (by simp; omega) ?_
  intro i h1 h2
  have hi : i < p := by simpa using h1
  have hcomm : i + d = d + i := Nat.add_comm i d
  simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp [hcomm]

/-! ### Lists of projections -/

/-- The list of projection functions named by `idx`. -/
def projsW (idx : List ℕ) : List (List Word → Word) :=
  idx.map (fun i => fun st : List Word => st.getD i [])

@[simp] theorem length_projsW (idx : List ℕ) : (projsW idx).length = idx.length := by
  simp [projsW]

@[simp] theorem map_projsW (idx : List ℕ) (st : List Word) :
    (projsW idx).map (fun F => F st) = idx.map (fun i => st.getD i []) := by
  simp [projsW, List.map_map, Function.comp_def]

/-- **A list of projections is realized.** -/
theorem sigListUniformB_projs {r : ℕ} {m k : ℕ → ℕ} (hkm : ∀ n, k n ≤ m n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (idx : List ℕ) (hidx : ∀ i ∈ idx, i < r) :
    SigListUniformB r m k (projsW idx) := by
  induction idx with
  | nil => simpa [projsW] using (sigListUniformB_nil (r := r) (m := m) (k := k))
  | cons i idx ih =>
      have h1 : SigUniformB r m k (fun st : List Word => st.getD i []) :=
        sigUniformB_of_sigUniform (sigUniform_proj (hidx i (by simp)) hm) hkm
      have h2 := sigListUniformB_cons h1 (ih (fun j hj => hidx j (by simp [hj]))) hm
      simpa [projsW] using h2

/-! ### Composing a realized function with realized arguments -/

/-- **A function of two realized arguments is realized.** -/
theorem sigUniformB_comp2 {r : ℕ} {m k k' : ℕ → ℕ} {f F1 F2 : List Word → Word}
    (hf : SigUniformB 2 m k' f) (h1 : SigUniformB r m k F1) (h2 : SigUniformB r m k F2)
    (hb1 : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      (F1 args).length ≤ k' n)
    (hb2 : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      (F2 args).length ≤ k' n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniformB r m k (fun args => f [F1 args, F2 args]) := by
  have hFs : SigListUniformB r m k [F1, F2] :=
    sigListUniformB_cons h1 (sigListUniformB_cons h2 sigListUniformB_nil hm) hm
  have hf' : SigUniformB ([F1, F2] : List (List Word → Word)).length m k' f := by simpa using hf
  have hbnd : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      ∀ F ∈ ([F1, F2] : List (List Word → Word)), (F args).length ≤ k' n := by
    intro n args hlen hle F hF
    rcases List.mem_cons.1 hF with rfl | hF
    · exact hb1 n args hlen hle
    · rcases List.mem_cons.1 hF with rfl | hF
      · exact hb2 n args hlen hle
      · simp at hF
  exact sigUniformB_comp hf' hFs hbnd hm

/-- **A function of three realized arguments is realized.** -/
theorem sigUniformB_comp3 {r : ℕ} {m k k' : ℕ → ℕ} {f F1 F2 F3 : List Word → Word}
    (hf : SigUniformB 3 m k' f) (h1 : SigUniformB r m k F1) (h2 : SigUniformB r m k F2)
    (h3 : SigUniformB r m k F3)
    (hb1 : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      (F1 args).length ≤ k' n)
    (hb2 : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      (F2 args).length ≤ k' n)
    (hb3 : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      (F3 args).length ≤ k' n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniformB r m k (fun args => f [F1 args, F2 args, F3 args]) := by
  have hFs : SigListUniformB r m k [F1, F2, F3] :=
    sigListUniformB_cons h1
      (sigListUniformB_cons h2 (sigListUniformB_cons h3 sigListUniformB_nil hm) hm) hm
  have hf' : SigUniformB ([F1, F2, F3] : List (List Word → Word)).length m k' f := by
    simpa using hf
  have hbnd : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      ∀ F ∈ ([F1, F2, F3] : List (List Word → Word)), (F args).length ≤ k' n := by
    intro n args hlen hle F hF
    rcases List.mem_cons.1 hF with rfl | hF
    · exact hb1 n args hlen hle
    · rcases List.mem_cons.1 hF with rfl | hF
      · exact hb2 n args hlen hle
      · rcases List.mem_cons.1 hF with rfl | hF
        · exact hb3 n args hlen hle
        · simp at hF
  exact sigUniformB_comp hf' hFs hbnd hm

/-- **A realized function applied to a window of the arguments is realized.** -/
theorem sigUniformB_appProjs {r : ℕ} {m k k' : ℕ → ℕ} {f : List Word → Word} (idx : List ℕ)
    (hf : SigUniformB idx.length m k' f) (hidx : ∀ i ∈ idx, i < r)
    (hkk' : ∀ n, k n ≤ k' n) (hkm : ∀ n, k n ≤ m n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniformB r m k (fun args => f (idx.map (fun i => args.getD i []))) := by
  have hFs : SigListUniformB r m k (projsW idx) := sigListUniformB_projs hkm hm idx hidx
  have hf' : SigUniformB (projsW idx).length m k' f := by
    rw [length_projsW]; exact hf
  have hbnd : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      ∀ F ∈ projsW idx, (F args).length ≤ k' n := by
    intro n args _ hle F hF
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hF
    exact le_trans (length_getD_le_of_forall hle i) (hkk' n)
  have hcomp := sigUniformB_comp hf' hFs hbnd hm
  simpa using hcomp

/-! ### The loop of a bounded recursion -/

/-- The arguments handed to the step terms at a state: the prefix consumed so far, the value of the
recursion at it, and the parameters. -/
def brecHArgs (p : ℕ) (st : List Word) : List Word :=
  (List.range (p + 2)).map (fun i => st.getD (i + 1) [])

/-- The arguments handed to the bound term at a state: the prefix after the current round, and the
parameters. -/
def brecBdArgs (p : ℕ) (st : List Word) : List Word :=
  consHeadW (st.getD 0 []) (st.getD 1 []) :: (List.range p).map (fun i => st.getD (i + 3) [])

/-- The new value of the recursion after one round: unchanged if there is no bit left to consume,
and otherwise the step term the bit selects, truncated to the length of the bound. -/
def brecStep (p : ℕ) (h₀ h₁ bd : Cob) (st : List Word) : Word :=
  muxW (st.getD 0 [])
    ((muxW (headBitW (st.getD 0 []))
        (h₁.eval (brecHArgs p st)) (h₀.eval (brecHArgs p st))).take
      (bd.eval (brecBdArgs p st)).length)
    (st.getD 2 [])

/-- One round of the loop, as a transition on states of `p + 3` words. -/
def brecStage (p : ℕ) (h₀ h₁ bd : Cob) : List (List Word → Word) :=
  [(fun st => (st.getD 0 []).tail), (fun st => consHeadW (st.getD 0 []) (st.getD 1 [])),
    brecStep p h₀ h₁ bd] ++ projsW ((List.range p).map (fun i => i + 3))

/-- The initial state: the recursion argument back to front, the empty prefix, the value of the
recursion at it, and the parameters. -/
def brecBase (p : ℕ) (g : Cob) : List (List Word → Word) :=
  [(fun args => (args.getD 0 []).reverse), (fun _ => []),
    (fun args => g.eval ((List.range p).map (fun i => args.getD (i + 1) [])))] ++
      projsW ((List.range p).map (fun i => i + 1))

/-- The final state: no bit left, the whole argument consumed, and the value of the recursion. -/
def brecFinal (p : ℕ) (g h₀ h₁ bd : Cob) : List (List Word → Word) :=
  [(fun _ => []), (fun args => args.getD 0 []), (Cob.bRec g h₀ h₁ bd).eval] ++
    projsW ((List.range p).map (fun i => i + 1))

@[simp] theorem length_brecStage (p : ℕ) (h₀ h₁ bd : Cob) :
    (brecStage p h₀ h₁ bd).length = p + 3 := by
  simp [brecStage]

@[simp] theorem length_brecBase (p : ℕ) (g : Cob) : (brecBase p g).length = p + 3 := by
  simp [brecBase]

@[simp] theorem length_brecFinal (p : ℕ) (g h₀ h₁ bd : Cob) :
    (brecFinal p g h₀ h₁ bd).length = p + 3 := by
  simp [brecFinal]

theorem brecStage_ne_nil (p : ℕ) (h₀ h₁ bd : Cob) : brecStage p h₀ h₁ bd ≠ [] := by
  simp [brecStage]

/-! ### What the loop computes -/

theorem brecHArgs_state {p : ℕ} (z y v : Word) {rest : List Word} (h : rest.length = p) :
    brecHArgs p ([z, y, v] ++ rest) = y :: v :: rest := by
  have := map_getD_range_add ([z, y, v] ++ rest) 1 (p + 2) (by simp; omega)
  simpa [brecHArgs] using this

theorem brecBdArgs_state {p : ℕ} (z y v : Word) {rest : List Word} (h : rest.length = p) :
    brecBdArgs p ([z, y, v] ++ rest) = consHeadW z y :: rest := by
  have := map_getD_range_add ([z, y, v] ++ rest) 3 p (by simp; omega)
  simpa [brecBdArgs] using this

theorem stepW_brecStage {p : ℕ} (h₀ h₁ bd : Cob) (z y v : Word) {rest : List Word}
    (h : rest.length = p) :
    stepW (brecStage p h₀ h₁ bd) ([z, y, v] ++ rest)
      = [z.tail, consHeadW z y, brecStep p h₀ h₁ bd ([z, y, v] ++ rest)] ++ rest := by
  simp only [stepW, brecStage, List.map_cons, map_projsW, List.map_map, Function.comp_def,
    List.nil_append, List.cons_append, List.getD_cons_zero, List.getD_cons_succ,
    map_getD_range_self rest p h]

theorem brecStep_nil {p : ℕ} (h₀ h₁ bd : Cob) (y v : Word) (rest : List Word) :
    brecStep p h₀ h₁ bd ([[], y, v] ++ rest) = v := by
  simp [brecStep, muxW]

theorem brecStep_cons {p : ℕ} (h₀ h₁ bd : Cob) (b : Bool) (z y v : Word) {rest : List Word}
    (h : rest.length = p) :
    brecStep p h₀ h₁ bd ([b :: z, y, v] ++ rest)
      = (if b then h₁.eval (y :: v :: rest) else h₀.eval (y :: v :: rest)).take
          (bd.eval ((b :: y) :: rest)).length := by
  have hH : brecHArgs p ([b :: z, y, v] ++ rest) = y :: v :: rest := brecHArgs_state _ _ _ h
  have hB : brecBdArgs p ([b :: z, y, v] ++ rest) = (b :: y) :: rest := by
    rw [brecBdArgs_state _ _ _ h]
    simp [consHeadW]
  simp only [brecStep, hH, hB]
  cases b <;> simp [muxW, headBitW]

/-- **After `j` rounds the loop holds the recursion at the last `j` bits of the argument.** -/
theorem iterate_brecStage {p : ℕ} (g h₀ h₁ bd : Cob) (x : Word) {rest : List Word}
    (h : rest.length = p) :
    ∀ j : ℕ, (stepW (brecStage p h₀ h₁ bd))^[j] ([x.reverse, [], g.eval rest] ++ rest)
      = [x.reverse.drop j, (x.reverse.take j).reverse,
          (Cob.bRec g h₀ h₁ bd).eval ((x.reverse.take j).reverse :: rest)] ++ rest := by
  intro j
  induction j with
  | zero =>
      simp only [Function.iterate_zero, id_eq, List.drop_zero, List.take_zero,
        List.reverse_nil]
      rw [Cob.eval_bRec_nil]
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, stepW_brecStage h₀ h₁ bd _ _ _ h,
        ← consHeadW_drop_reverse_take x.reverse j, List.tail_drop]
      congr 2
      rcases hz : x.reverse.drop j with _ | ⟨b, z⟩
      · rw [brecStep_nil]
        simp [consHeadW]
      · rw [brecStep_cons h₀ h₁ bd b z _ _ h]
        have hcons : consHeadW (b :: z) ((x.reverse.take j).reverse)
            = b :: (x.reverse.take j).reverse := by simp [consHeadW]
        rw [hcons, Cob.eval_bRec_cons]

/-! ### The value of a bounded recursion is short -/

/-- **The value of a bounded recursion is no longer than its base and its bound allow.** -/
theorem length_eval_bRec_le {n : ℕ} {k kS : ℕ → ℕ} {g h₀ h₁ bd : Cob}
    (hGb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ k n) →
      (g.eval args).length ≤ kS n)
    (hBDb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ k n) →
      (bd.eval args).length ≤ kS n)
    (y : Word) (rest : List Word) (hy : y.length ≤ k n)
    (hrest : ∀ u ∈ rest, u.length ≤ k n) :
    ((Cob.bRec g h₀ h₁ bd).eval (y :: rest)).length ≤ kS n := by
  rcases y with _ | ⟨b, y'⟩
  · rw [Cob.eval_bRec_nil]
    exact hGb n rest hrest
  · rw [Cob.eval_bRec_cons]
    refine le_trans (List.length_take_le _ _) ?_
    refine hBDb n ((b :: y') :: rest) ?_
    intro u hu
    rcases List.mem_cons.1 hu with rfl | hu
    · exact hy
    · exact hrest u hu

/-! ### The stage is realized -/

/-- Putting a bit in front of a word lengthens it by at most one. -/
theorem length_consHeadW_le (a b : Word) : (consHeadW a b).length ≤ b.length + 1 := by
  rw [consHeadW_eq]
  split_ifs <;> simp

/-- The head bit of a word is a word of at most one letter. -/
theorem length_headBitW_le (a : Word) : (headBitW a).length ≤ 1 := by
  unfold headBitW
  split_ifs <;> simp

/-- The arguments handed to the step terms at a short state are short. -/
theorem length_brecHArgs_le {p : ℕ} {st : List Word} {B : ℕ} (h : ∀ u ∈ st, u.length ≤ B) :
    ∀ u ∈ brecHArgs p st, u.length ≤ B := by
  intro u hu
  simp only [brecHArgs] at hu
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hu
  exact length_getD_le_of_forall h (i + 1)

/-- The arguments handed to the bound term at a short state are short. -/
theorem length_brecBdArgs_le {p : ℕ} {st : List Word} {B : ℕ} (h : ∀ u ∈ st, u.length ≤ B) :
    ∀ u ∈ brecBdArgs p st, u.length ≤ B + 1 := by
  intro u hu
  simp only [brecBdArgs] at hu
  rcases List.mem_cons.1 hu with rfl | hu
  · exact le_trans (length_consHeadW_le _ _)
      (Nat.add_le_add_right (length_getD_le_of_forall h 1) 1)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hu
    exact le_trans (length_getD_le_of_forall h (i + 3)) (by omega)

/-- **One round of the loop is realized.** -/
theorem sigListUniformB_brecStage {p : ℕ} {m kS kP kI : ℕ → ℕ} {h₀ h₁ bd : Cob}
    (hkP : ∀ n, kS n + 1 ≤ kP n) (hPI : ∀ n, kP n ≤ kI n) (hIm : ∀ n, kI n ≤ m n)
    (hH0 : SigUniformB (p + 2) m kP h₀.eval) (hH1 : SigUniformB (p + 2) m kP h₁.eval)
    (hBD : SigUniformB (p + 1) m kP bd.eval)
    (hH0b : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
      (h₀.eval args).length ≤ kI n)
    (hH1b : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
      (h₁.eval args).length ≤ kI n)
    (hBDb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
      (bd.eval args).length ≤ kI n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigListUniformB (p + 3) m kS (brecStage p h₀ h₁ bd) := by
  have hSP : ∀ n, kS n ≤ kP n := fun n => by have := hkP n; omega
  have hSm : ∀ n, kS n ≤ m n := fun n => le_trans (hSP n) (le_trans (hPI n) (hIm n))
  have hIpos : ∀ n, 1 ≤ kI n := fun n => by
    have := hkP n; have := hPI n; omega
  -- the indices of the parameters inside a state
  have hidx3 : ∀ i ∈ (List.range p).map (fun i => i + 3), i < p + 3 := by
    intro i hi
    simp only [List.mem_map, List.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    omega
  have hidx1 : ∀ i ∈ (List.range (p + 2)).map (fun i => i + 1), i < p + 3 := by
    intro i hi
    simp only [List.mem_map, List.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    omega
  -- the gadgets
  have hT0 : SigUniformB (p + 3) m kS (fun st : List Word => (st.getD 0 []).tail) :=
    sigUniformB_of_sigUniform (sigUniform_tail (r := p + 3) (by omega) hm) hSm
  have hT1 : SigUniformB (p + 3) m kS
      (fun st : List Word => consHeadW (st.getD 0 []) (st.getD 1 [])) :=
    sigUniformB_of_sigUniform (sigUniform_consHead (r := p + 3) (by omega) hm) hSm
  have hhead : SigUniformB (p + 3) m kS (fun st : List Word => headBitW (st.getD 0 [])) :=
    sigUniformB_of_sigUniform (sigUniform_headBit (r := p + 3) (by omega) hm) hSm
  have hproj0 : SigUniformB (p + 3) m kS (fun st : List Word => st.getD 0 []) :=
    sigUniformB_of_sigUniform (sigUniform_proj (by omega) hm) hSm
  have hproj2 : SigUniformB (p + 3) m kS (fun st : List Word => st.getD 2 []) :=
    sigUniformB_of_sigUniform (sigUniform_proj (by omega) hm) hSm
  have hmuxF : SigUniformB 3 m kI
      (fun args : List Word => muxW (args.getD 0 []) (args.getD 1 []) (args.getD 2 [])) :=
    sigUniformB_of_sigUniform (sigUniform_mux (r := 3) le_rfl hm) hIm
  have htakeF : SigUniformB 2 m kI
      (fun args : List Word => (args.getD 0 []).take (args.getD 1 []).length) :=
    sigUniformB_of_sigUniform (sigUniform_takeLen (r := 2) le_rfl hm) hIm
  -- the step terms, applied to the window of the state they read
  have hHwin : ∀ st : List Word,
      ((List.range (p + 2)).map (fun i => i + 1)).map (fun i => st.getD i [])
        = brecHArgs p st := by
    intro st
    simp [brecHArgs, List.map_map, Function.comp_def]
  have hA1 : SigUniformB (p + 3) m kS (fun st => h₁.eval (brecHArgs p st)) := by
    have hap := sigUniformB_appProjs (r := p + 3) (k := kS) (k' := kP)
      ((List.range (p + 2)).map (fun i => i + 1)) (by simpa using hH1) hidx1 hSP hSm hm
    have heq : (fun st : List Word =>
        h₁.eval (((List.range (p + 2)).map (fun i => i + 1)).map (fun i => st.getD i [])))
        = fun st : List Word => h₁.eval (brecHArgs p st) := by
      funext st
      rw [hHwin st]
    rw [heq] at hap
    exact hap
  have hA0 : SigUniformB (p + 3) m kS (fun st => h₀.eval (brecHArgs p st)) := by
    have hap := sigUniformB_appProjs (r := p + 3) (k := kS) (k' := kP)
      ((List.range (p + 2)).map (fun i => i + 1)) (by simpa using hH0) hidx1 hSP hSm hm
    have heq : (fun st : List Word =>
        h₀.eval (((List.range (p + 2)).map (fun i => i + 1)).map (fun i => st.getD i [])))
        = fun st : List Word => h₀.eval (brecHArgs p st) := by
      funext st
      rw [hHwin st]
    rw [heq] at hap
    exact hap
  -- the bound term, applied to the prefix after the round and the parameters
  have hBDapp : SigUniformB (p + 3) m kS (fun st => bd.eval (brecBdArgs p st)) := by
    set Fs : List (List Word → Word) :=
      (fun st : List Word => consHeadW (st.getD 0 []) (st.getD 1 [])) ::
        projsW ((List.range p).map (fun i => i + 3)) with hFsdef
    have hFs : SigListUniformB (p + 3) m kS Fs :=
      sigListUniformB_cons hT1 (sigListUniformB_projs hSm hm _ hidx3) hm
    have hf : SigUniformB Fs.length m kP bd.eval := by
      have hlen : Fs.length = p + 1 := by simp [hFsdef]
      rw [hlen]
      exact hBD
    have hbnd : ∀ (n : ℕ) (args : List Word), args.length = p + 3 →
        (∀ u ∈ args, u.length ≤ kS n) → ∀ F ∈ Fs, (F args).length ≤ kP n := by
      intro n args _ hle F hF
      rw [hFsdef] at hF
      rcases List.mem_cons.1 hF with rfl | hF
      · refine le_trans (length_consHeadW_le _ _) ?_
        have := length_getD_le_of_forall hle 1
        have := hkP n
        omega
      · obtain ⟨i, _, rfl⟩ := List.mem_map.1 hF
        exact le_trans (length_getD_le_of_forall hle i) (hSP n)
    have hcomp := sigUniformB_comp hf hFs hbnd hm
    have heq : (fun args : List Word => bd.eval (Fs.map (fun F => F args)))
        = fun st : List Word => bd.eval (brecBdArgs p st) := by
      funext st
      congr 1
      simp [hFsdef, brecBdArgs, List.map_map, Function.comp_def]
    rw [heq] at hcomp
    exact hcomp
  -- the value the round produces
  have hmux1 : SigUniformB (p + 3) m kS (fun st => muxW (headBitW (st.getD 0 []))
      (h₁.eval (brecHArgs p st)) (h₀.eval (brecHArgs p st))) := by
    refine sigUniformB_comp3 (k' := kI) hmuxF hhead hA1 hA0 ?_ ?_ ?_ hm
    · intro n args _ _
      exact le_trans (length_headBitW_le (args.getD 0 [])) (hIpos n)
    · intro n args _ hle
      exact hH1b n _ (length_brecHArgs_le (fun u hu => le_trans (hle u hu) (hSP n)))
    · intro n args _ hle
      exact hH0b n _ (length_brecHArgs_le (fun u hu => le_trans (hle u hu) (hSP n)))
  have hmux1b : ∀ (n : ℕ) (st : List Word), (∀ u ∈ st, u.length ≤ kS n) →
      (muxW (headBitW (st.getD 0 [])) (h₁.eval (brecHArgs p st))
        (h₀.eval (brecHArgs p st))).length ≤ kI n := by
    intro n st hle
    refine le_trans (length_muxW_le _ _ _) ?_
    have h1 := hH1b n _ (length_brecHArgs_le (p := p)
      (fun u hu => le_trans (hle u hu) (hSP n)))
    have h0 := hH0b n _ (length_brecHArgs_le (p := p)
      (fun u hu => le_trans (hle u hu) (hSP n)))
    omega
  have hBDappb : ∀ (n : ℕ) (st : List Word), (∀ u ∈ st, u.length ≤ kS n) →
      (bd.eval (brecBdArgs p st)).length ≤ kI n := by
    intro n st hle
    refine hBDb n _ (fun u hu => ?_)
    have := length_brecBdArgs_le (p := p) hle u hu
    have := hkP n
    omega
  have htake : SigUniformB (p + 3) m kS (fun st =>
      (muxW (headBitW (st.getD 0 [])) (h₁.eval (brecHArgs p st))
        (h₀.eval (brecHArgs p st))).take (bd.eval (brecBdArgs p st)).length) := by
    refine sigUniformB_comp2 (k' := kI) htakeF hmux1 hBDapp ?_ ?_ hm
    · intro n args _ hle
      exact hmux1b n args hle
    · intro n args _ hle
      exact hBDappb n args hle
  have hT2 : SigUniformB (p + 3) m kS (brecStep p h₀ h₁ bd) := by
    refine sigUniformB_comp3 (k' := kI) hmuxF hproj0 htake hproj2 ?_ ?_ ?_ hm
    · intro n args _ hle
      exact le_trans (length_getD_le_of_forall hle 0) (le_trans (hSP n) (hPI n))
    · intro n args _ hle
      exact le_trans (List.length_take_le _ _) (hBDappb n args hle)
    · intro n args _ hle
      exact le_trans (length_getD_le_of_forall hle 2) (le_trans (hSP n) (hPI n))
  have hprojs : SigListUniformB (p + 3) m kS (projsW ((List.range p).map (fun i => i + 3))) :=
    sigListUniformB_projs hSm hm _ hidx3
  exact sigListUniformB_cons hT0 (sigListUniformB_cons hT1
    (sigListUniformB_cons hT2 hprojs hm) hm) hm

/-! ### The initial state is realized -/

theorem map_brecBase {p : ℕ} (g : Cob) (x : Word) {rest : List Word} (h : rest.length = p) :
    (brecBase p g).map (fun D => D (x :: rest)) = [x.reverse, [], g.eval rest] ++ rest := by
  simp only [brecBase, List.map_cons, map_projsW, List.map_map, Function.comp_def,
    List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append,
    map_getD_range_self rest p h]

theorem map_brecFinal {p : ℕ} (g h₀ h₁ bd : Cob) (x : Word) {rest : List Word}
    (h : rest.length = p) :
    (brecFinal p g h₀ h₁ bd).map (fun E => E (x :: rest))
      = [[], x, (Cob.bRec g h₀ h₁ bd).eval (x :: rest)] ++ rest := by
  simp only [brecFinal, List.map_cons, map_projsW, List.map_map, Function.comp_def,
    List.getD_cons_zero, List.getD_cons_succ, List.nil_append, List.cons_append,
    map_getD_range_self rest p h]

/-- **The initial state is realized.** -/
theorem sigListUniformB_brecBase {p : ℕ} {m k kP : ℕ → ℕ} {g : Cob}
    (hkP : ∀ n, k n ≤ kP n) (hkm : ∀ n, k n ≤ m n) (hm0 : ∀ n, 0 < m n)
    (hG : SigUniformB p m kP g.eval)
    {mT kT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true) :
    SigListUniformB (p + 1) m k (brecBase p g) := by
  have hidx1 : ∀ i ∈ (List.range p).map (fun i => i + 1), i < p + 1 := by
    intro i hi
    simp only [List.mem_map, List.mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    omega
  have hD0 : SigUniformB (p + 1) m k (fun args : List Word => (args.getD 0 []).reverse) :=
    sigUniformB_reverse (r := p + 1) (by omega) hkm hm0 hm hk
  have hD1 : SigUniformB (p + 1) m k (fun _ : List Word => ([] : Word)) :=
    sigUniformB_of_sigUniform (sigUniform_empty hm) hkm
  have hD2 : SigUniformB (p + 1) m k
      (fun args : List Word => g.eval ((List.range p).map (fun i => args.getD (i + 1) []))) := by
    have hap := sigUniformB_appProjs (r := p + 1) (k := k) (k' := kP)
      ((List.range p).map (fun i => i + 1)) (by simpa using hG) hidx1 hkP hkm hm
    have heq : (fun args : List Word =>
        g.eval (((List.range p).map (fun i => i + 1)).map (fun i => args.getD i [])))
        = fun args : List Word => g.eval ((List.range p).map (fun i => args.getD (i + 1) [])) := by
      funext args
      congr 1
      simp [List.map_map, Function.comp_def]
    rw [heq] at hap
    exact hap
  exact sigListUniformB_cons hD0 (sigListUniformB_cons hD1
    (sigListUniformB_cons hD2 (sigListUniformB_projs hkm hm _ hidx1) hm) hm) hm

/-! ### The compiler for a bounded recursion -/

/-- **A bounded recursion is realized** by a P-uniform family of circuits, provided its four
subterms are: run the loop for as many rounds as the promise allows, and read the value off the
third entry of the state. -/
theorem sigUniformB_bRec {p : ℕ} {m k kS kP kI : ℕ → ℕ} {g h₀ h₁ bd : Cob}
    (hkS : ∀ n, k n ≤ kS n) (hkP : ∀ n, kS n + 1 ≤ kP n) (hPI : ∀ n, kP n ≤ kI n)
    (hIm : ∀ n, kI n ≤ m n) (hm0 : ∀ n, 0 < m n)
    (hG : SigUniformB p m kP g.eval)
    (hH0 : SigUniformB (p + 2) m kP h₀.eval) (hH1 : SigUniformB (p + 2) m kP h₁.eval)
    (hBD : SigUniformB (p + 1) m kP bd.eval)
    (hGb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ k n) →
      (g.eval args).length ≤ kS n)
    (hH0b : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
      (h₀.eval args).length ≤ kI n)
    (hH1b : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
      (h₁.eval args).length ≤ kI n)
    (hBDb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ k n) →
      (bd.eval args).length ≤ kS n)
    (hBDb' : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
      (bd.eval args).length ≤ kI n)
    {mT kT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true) :
    SigUniformB (p + 1) m k (Cob.bRec g h₀ h₁ bd).eval := by
  have hSP : ∀ n, kS n ≤ kP n := fun n => by have := hkP n; omega
  have hSm : ∀ n, kS n ≤ m n := fun n => le_trans (hSP n) (le_trans (hPI n) (hIm n))
  have hkm : ∀ n, k n ≤ m n := fun n => le_trans (hkS n) (hSm n)
  -- the value of the recursion is short
  have hRb : ∀ (n : ℕ) (y : Word) (rest : List Word), y.length ≤ k n →
      (∀ u ∈ rest, u.length ≤ k n) →
      ((Cob.bRec g h₀ h₁ bd).eval (y :: rest)).length ≤ kS n := by
    intro n y rest hy hrest
    exact length_eval_bRec_le hGb hBDb y rest hy hrest
  have hstage : SigListUniformB (p + 3) m kS (brecStage p h₀ h₁ bd) :=
    sigListUniformB_brecStage hkP hPI hIm hH0 hH1 hBD hH0b hH1b hBDb' hm
  have hbase : SigListUniformB (p + 1) m k (brecBase p g) :=
    sigListUniformB_brecBase (fun n => le_trans (hkS n) (hSP n)) hkm hm0 hG hm hk
  -- the loop
  have hfinal : SigListUniformB (p + 1) m k (brecFinal p g h₀ h₁ bd) := by
    refine sigListUniformB_iter (Ts := brecStage p h₀ h₁ bd) (Ds := brecBase p g)
      (Es := brecFinal p g h₀ h₁ bd) (K := k) (k' := kS) ?_ hbase (by simp) (by simp)
      (brecStage_ne_nil p h₀ h₁ bd) hm0 ?_ ?_ (kT := kT) hk hm
    · rw [length_brecStage]
      exact hstage
    · -- the intermediate states are short
      intro n args hlen hle j _ u hu
      rcases args with _ | ⟨x, rest⟩
      · simp at hlen
      · have hrest : rest.length = p := by simpa using hlen
        have hx : x.length ≤ k n := hle x (by simp)
        have hrestle : ∀ w ∈ rest, w.length ≤ kS n := fun w hw =>
          le_trans (hle w (by simp [hw])) (hkS n)
        rw [map_brecBase g x hrest, iterate_brecStage g h₀ h₁ bd x hrest j] at hu
        simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
        rcases hu with rfl | hu
        · have h1 : (x.reverse.drop j).length ≤ x.length := by simp
          have h2 := hkS n
          omega
        · rcases hu with rfl | hu
          · refine le_trans ?_ (le_trans hx (hkS n))
            simp
          · rcases hu with rfl | hu
            · refine hRb n _ rest ?_ (fun w hw => hle w (by simp [hw]))
              refine le_trans ?_ hx
              simp
            · exact hrestle u hu
    · -- after the promised number of rounds the state has settled
      intro n args hlen hle
      rcases args with _ | ⟨x, rest⟩
      · simp at hlen
      · have hrest : rest.length = p := by simpa using hlen
        have hx : x.length ≤ k n := hle x (by simp)
        rw [map_brecBase g x hrest, iterate_brecStage g h₀ h₁ bd x hrest (k n),
          map_brecFinal g h₀ h₁ bd x hrest]
        have hdrop : x.reverse.drop (k n) = [] := List.drop_eq_nil_of_le (by simpa using hx)
        have htake : (x.reverse.take (k n)).reverse = x := by
          rw [List.take_of_length_le (by simpa using hx), List.reverse_reverse]
        rw [hdrop, htake]
  -- read the answer off the third entry
  have hproj := sigUniformB_getD_of_sigListUniformB (i := 2) (Es := brecFinal p g h₀ h₁ bd)
    (by simp) hfinal hm (k' := kS) hSm ?_
  · have heq : (fun args : List Word =>
        ((brecFinal p g h₀ h₁ bd).map (fun E => E args)).getD 2 [])
        = (Cob.bRec g h₀ h₁ bd).eval := by
      funext args
      rfl
    rw [heq] at hproj
    exact hproj
  · intro n args hlen hle E hE
    rcases args with _ | ⟨x, rest⟩
    · simp at hlen
    · have hrest : rest.length = p := by simpa using hlen
      have hx : x.length ≤ k n := hle x (by simp)
      have hrestle : ∀ w ∈ rest, w.length ≤ kS n := fun w hw =>
        le_trans (hle w (by simp [hw])) (hkS n)
      simp only [brecFinal, List.cons_append, List.nil_append, List.mem_cons] at hE
      rcases hE with rfl | hE
      · simp
      · rcases hE with rfl | hE
        · simpa using le_trans hx (hkS n)
        · rcases hE with rfl | hE
          · exact hRb n x rest hx (fun w hw => hle w (by simp [hw]))
          · simp only [projsW, List.mem_map] at hE
            obtain ⟨i, _, rfl⟩ := hE
            exact length_getD_le_of_forall
              (fun w hw => le_trans (hle w hw) (hkS n)) i

end Complexity
