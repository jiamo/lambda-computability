/-
**The questions of the verifier and the verifier of Shamir's protocol** (task-board row
`M21-VERIFIER-POLY`).

The verifier `Complexity.Shamir.shamirV` (parameters and decision term in
`Start/ShamirVerifier.lean`) asks, in the round after `i` completed rounds, the residue modulo `p`
of the `i`-th block of `8 (n + 1)` coins, in unary.  The question term
`Complexity.Shamir.askT` finds the block by a bounded iteration that drops two records of the
transcript and one block of coins per step (`Complexity.Shamir.askStep`), then decodes the block
by a bounded recursion on notation (`Complexity.Shamir.decPT`).

Main results:

* `Complexity.Shamir.eval_askT` — on a transcript of `i` completed rounds the question is the
  residue of the `i`-th coin block;
* `Complexity.Shamir.transcript_shamirV` — the transcript of the interaction is the left fold of
  the round function `Complexity.Shamir.stepT` over the decoded coin blocks;
* `Complexity.Shamir.accepts_shamirV` — the verdict of the verifier is the verdict of the
  machine of `Start/ShamirMachine.lean` on the transcript without its first record.
-/

import Start.ShamirVerifier

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### Decoding a coin block -/

/-- One bit of the decoding: `(b + 2 · ih) mod p`, on `[x, ih, 1^p]`. -/
def decPH (b : Bool) : Cob :=
  Cob.modT (Cob.catT (if b then Cob.constT [true] else .empty)
    (Cob.catT (.proj 1) (.proj 1))) (.proj 2)

/-- The residue modulo `p` of a block, in unary, on `[w, 1^p]`. -/
def decPT : Cob := .bRec .empty (decPH false) (decPH true) (.proj 1)

theorem eval_decPT {p : ℕ} (hp : 0 < p) :
    ∀ w : Word, decPT.eval [w, un p] = un (decP p w)
  | [] => by simp only [decPT, Cob.eval_bRec_nil, Cob.eval_empty, decP]; rfl
  | b :: w => by
      rw [decPT, Cob.eval_bRec_cons, ← decPT, eval_decPT hp w]
      have hlt : (bitV b + 2 * decP p w) % p < p := Nat.mod_lt _ hp
      have hh : ∀ c : Bool, (decPH c).eval [w, un (decP p w), un p] =
          un ((bitV c + 2 * decP p w) % p) := by
        intro c
        rw [decPH]
        refine Cob.eval_modT hp ?_ (by simp [un])
        cases c
        · simp only [Bool.false_eq_true, if_false, Cob.eval_catT, Cob.eval_empty, Cob.eval_proj,
            List.getD_cons_succ, List.getD_cons_zero, List.nil_append, bitV, un,
            ← List.replicate_add]
          congr 1; omega
        · simp only [if_true, Cob.eval_catT, Cob.eval_constT, Cob.eval_proj,
            List.getD_cons_succ, List.getD_cons_zero, bitV, un, ← List.replicate_add]
          rw [← List.replicate_one, ← List.replicate_add]
          congr 1; omega
      have e : (if b then (decPH true).eval [w, un (decP p w), un p]
          else (decPH false).eval [w, un (decP p w), un p]) = (decPH b).eval [w, un (decP p w), un p] :=
        by cases b <;> rfl
      rw [e, hh, decP]
      simp only [Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, length_un]
      exact List.take_of_length_le (by simp [hlt.le])

/-! ### Finding the current block -/

/-- One step of the search for the current coin block: drop two records of the transcript and a
block of `kb` coins, unless the transcript is used up. -/
def askStep (kb : ℕ) (s : Word × Word) : Word × Word :=
  if s.1 = [] then s else (recSkip (recSkip s.1), s.2.drop kb)

/-- The step as a Cobham term, on `[s, x, r, t]` with `s` packing the pair. -/
def stepA : Cob :=
  Cob.iteT (unpackT 0 (.proj 0))
    (packT [Cob.recSkipT (Cob.recSkipT (unpackT 0 (.proj 0))),
      Cob.dropBy (.comp kbT [.proj 1]) (unpackT 1 (.proj 0))])
    (.proj 0)

/-- The initial pair `(t, r)`, packed, on `[x, r, t]`. -/
def initA : Cob := packT [.proj 2, .proj 1]

/-- `|t|` steps of the search, on `[w, x, r, t]`. -/
def countA : Cob := Cob.iterT initA stepA initA 3

/-- **The question of the verifier**, on `[x, r, t]`. -/
def askT : Cob :=
  .comp decPT
    [Cob.takeBy (.comp kbT [.proj 0]) (unpackT 1 (.comp countA [.proj 2, .proj 0, .proj 1, .proj 2])),
     .comp pT [.proj 0]]

/-- The packing of a pair. -/
def packP (s : Word × Word) : Word := packW [s.1, s.2]

theorem eval_stepA (s : Word × Word) (x r t : Word) :
    stepA.eval [packP s, x, r, t] = packP (askStep (8 * (x.length + 1)) s) := by
  have h0 : (unpackT 0 (.proj 0)).eval [packW [s.1, s.2], x, r, t] = s.1 :=
    eval_unpackT (ws := [s.1, s.2]) (by simp) (by simp)
  have h1 : (unpackT 1 (.proj 0)).eval [packW [s.1, s.2], x, r, t] = s.2 :=
    eval_unpackT (ws := [s.1, s.2]) (by simp) (by simp)
  simp only [packP]
  rw [stepA, Cob.eval_iteT_word, h0, askStep]
  by_cases hs : s.1 = []
  · simp [hs]
  · simp only [hs, if_false, eval_packT, List.map_cons, List.map_nil, Cob.eval_recSkipT, h0,
      Cob.eval_dropBy, h1, Cob.eval_comp, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ,
      eval_kbT, length_un, packP]

theorem iterate_stepA (s : Word × Word) (x r t : Word) (j : ℕ) :
    (fun w => stepA.eval (w :: [x, r, t]))^[j] (packP s) =
      packP ((askStep (8 * (x.length + 1)))^[j] s) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, eval_stepA, Function.iterate_succ_apply']

theorem askStep_le (kb A B : ℕ) (s : Word × Word) (h : s.1.length ≤ A ∧ s.2.length ≤ B) :
    (askStep kb s).1.length ≤ A ∧ (askStep kb s).2.length ≤ B := by
  unfold askStep
  split
  · exact h
  · exact ⟨(recSkip_length_le _).trans ((recSkip_length_le _).trans h.1),
      (by rw [List.length_drop]; omega)⟩

theorem iterate_askStep_le (kb : ℕ) (s : Word × Word) (j : ℕ) :
    ((askStep kb)^[j] s).1.length ≤ s.1.length ∧ ((askStep kb)^[j] s).2.length ≤ s.2.length := by
  induction j with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact askStep_le _ _ _ _ ih

theorem eval_countA (x r t : Word) :
    countA.eval [t, x, r, t] = packP ((askStep (8 * (x.length + 1)))^[t.length] (t, r)) := by
  have hinit : initA.eval [x, r, t] = packP (t, r) := by
    simp [initA, eval_packT, packP]
  rw [countA, show (3 : ℕ) = [x, r, t].length from rfl, Cob.eval_iterT, hinit, iterate_stepA]
  intro j _ _
  rw [hinit, iterate_stepA, packP, packP, length_packW, length_packW]
  have := iterate_askStep_le (8 * (x.length + 1)) (t, r) j
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at this ⊢
  omega

/-! ### Transcripts of completed rounds -/

/-- A word of completed rounds: the records of the two messages of each round. -/
def pairsW (L : List (Word × Word)) : Word := (L.map fun ab => encMsg ab.1 ++ encMsg ab.2).flatten

theorem iterate_askStep_pairsW (kb : ℕ) (r : Word) :
    ∀ (L : List (Word × Word)) (j : ℕ), L.length ≤ j →
      (askStep kb)^[j] (pairsW L, r) = ([], r.drop (kb * L.length))
  | [], j, _ => by
      have : ∀ j, (askStep kb)^[j] ([], r) = ([], r) := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih => rw [Function.iterate_succ_apply', ih]; simp [askStep]
      simpa [pairsW] using this j
  | ab :: L, j, hj => by
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by simp at hj; omega⟩
      have hne : pairsW (ab :: L) ≠ [] := by simp [pairsW, encMsg]
      rw [Function.iterate_succ_apply]
      have e : askStep kb (pairsW (ab :: L), r) = (pairsW L, r.drop kb) := by
        rw [askStep, if_neg hne]
        simp [pairsW, List.append_assoc]
      rw [e, iterate_askStep_pairsW kb (r.drop kb) L j (by simp at hj; omega), List.drop_drop]
      simp only [List.length_cons]
      congr 2
      ring

theorem length_pairsW_ge (L : List (Word × Word)) : L.length ≤ (pairsW L).length := by
  induction L with
  | nil => simp
  | cons ab L ih =>
      simp only [pairsW, List.map_cons, List.flatten_cons, List.length_append, length_encMsg,
        List.length_cons] at ih ⊢
      omega

/-- The residue of the `k`-th block of `kb` coins. -/
def bv (p kb : ℕ) (r : Word) (k : ℕ) : ℕ := decP p ((r.drop (kb * k)).take kb)

/-- **The question after `i` completed rounds is the `i`-th coin block.** -/
theorem eval_askT (x r : Word) (L : List (Word × Word)) :
    askT.eval [x, r, pairsW L] = un (bv (primeOf x) (8 * (x.length + 1)) r L.length) := by
  obtain ⟨hpT, hpr, -, -⟩ := primeOf_spec x
  have hc : (Cob.comp countA [.proj 2, .proj 0, .proj 1, .proj 2]).eval [x, r, pairsW L] =
      packP ([], r.drop (8 * (x.length + 1) * L.length)) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [eval_countA, iterate_askStep_pairsW _ _ _ _ (length_pairsW_ge L)]
  have hu : (unpackT 1 (Cob.comp countA [.proj 2, .proj 0, .proj 1, .proj 2])).eval
      [x, r, pairsW L] = r.drop (8 * (x.length + 1) * L.length) :=
    eval_unpackT (ws := [[], r.drop (8 * (x.length + 1) * L.length)]) hc (by simp)
  rw [askT, Cob.eval_comp]
  simp only [List.map_cons, List.map_nil, Cob.eval_takeBy, hu, Cob.eval_comp, Cob.eval_proj,
    List.getD_cons_zero, eval_kbT, length_un, eval_pT_cons, hpT]
  exact eval_decPT hpr.pos _

/-! ### The verifier -/

/-- **One round of the interaction**: the verifier asks `1^v`, the prover answers from the
transcript extended by the question, cut to `M` bits; both messages are recorded. -/
def stepT (P : Prover) (M : ℕ) (t : Word) (v : ℕ) : Word :=
  t ++ encMsg (un v) ++ encMsg ((P (t ++ encMsg (un v))).take M)

theorem foldl_stepT_pairsW (P : Prover) (M : ℕ) :
    ∀ (vs : List ℕ) (L0 : List (Word × Word)), ∃ L : List (Word × Word),
      L.length = L0.length + vs.length ∧ vs.foldl (stepT P M) (pairsW L0) = pairsW L
  | [], L0 => ⟨L0, by simp, rfl⟩
  | v :: vs, L0 => by
      obtain ⟨L, hL, he⟩ := foldl_stepT_pairsW P M vs
        (L0 ++ [(un v, (P (pairsW L0 ++ encMsg (un v))).take M)])
      refine ⟨L, by simp only [hL, List.length_append, List.length_cons, List.length_nil]; omega,
        ?_⟩
      rw [List.foldl_cons, ← he]
      congr 1
      simp [stepT, pairsW, List.append_assoc]

/-- **The verifier of Shamir's protocol for `TQBF`.** -/
def shamirV : Verifier where
  rounds := Cob.catT rcT (Cob.constT [true])
  coins := .comp .smash [Cob.catT rcT (Cob.constT [true]), kbT]
  msgLen := .comp .smash [Cob.catT dT (Cob.constT [true, true]), pT]
  ask := askT
  decide := decideT

theorem numRounds_shamirV (x : Word) : shamirV.numRounds x = (x.length + 1) ^ 2 + 1 := by
  simp [Verifier.numRounds, shamirV, eval_rcT]

theorem numCoins_shamirV (x : Word) :
    shamirV.numCoins x = ((x.length + 1) ^ 2 + 1) * (8 * (x.length + 1)) := by
  simp [Verifier.numCoins, shamirV, eval_rcT, eval_kbT]

theorem maxMsg_shamirV (x : Word) : shamirV.maxMsg x = (2 * x.length + 2) * primeOf x := by
  simp [Verifier.maxMsg, shamirV, eval_dT, (primeOf_spec x).1]

/-- The residues of the first `j` coin blocks. -/
def bvs (p kb : ℕ) (r : Word) (j : ℕ) : List ℕ := (List.range j).map (bv p kb r)

theorem bv_lt (x r : Word) (k : ℕ) : bv (primeOf x) (8 * (x.length + 1)) r k < primeOf x :=
  decP_lt (primeOf_spec x).2.1.pos _

theorem iterate_round_shamirV (P : Prover) (x r : Word) (j : ℕ) :
    (shamirV.round P x r)^[j] [] =
      (bvs (primeOf x) (8 * (x.length + 1)) r j).foldl (stepT P (shamirV.maxMsg x)) [] := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      obtain ⟨L, hL, he⟩ := foldl_stepT_pairsW P (shamirV.maxMsg x)
        (bvs (primeOf x) (8 * (x.length + 1)) r j) []
      have hL' : L.length = j := by simpa [bvs] using hL
      rw [show ([] : Word) = pairsW [] from rfl, he, bvs, List.range_succ, List.map_append,
        List.foldl_append, ← bvs, he]
      have hq : (shamirV.ask.eval [x, r, pairsW L]).take (shamirV.maxMsg x) =
          un (bv (primeOf x) (8 * (x.length + 1)) r j) := by
        rw [show shamirV.ask = askT from rfl, eval_askT, hL']
        refine List.take_of_length_le ?_
        rw [length_un, maxMsg_shamirV]
        have := bv_lt x r j
        nlinarith
      simp only [Verifier.round, hq, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
        stepT, List.append_assoc]

theorem transcript_shamirV (P : Prover) (x r : Word) :
    shamirV.transcript P x r =
      (bvs (primeOf x) (8 * (x.length + 1)) r ((x.length + 1) ^ 2 + 1)).foldl
        (stepT P (shamirV.maxMsg x)) [] := by
  rw [Verifier.transcript, numRounds_shamirV, iterate_round_shamirV]

/-- **The verdict of the verifier is the verdict of the machine** on the transcript without its
first record, after `(n + 1)²` steps. -/
theorem accepts_shamirV (P : Prover) (x r : Word) :
    shamirV.accepts P x r =
      decide (((stepW (primeOf x) x.length (2 * x.length))^[(x.length + 1) ^ 2]
        (initSt x.length x (recSkip (shamirV.transcript P x r)))).B = []) := by
  rw [Verifier.accepts, show shamirV.decide = decideT from rfl, eval_decideT]
  split <;> simp_all

end Complexity.Shamir
