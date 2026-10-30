/-
**`P^TQBF = NP^TQBF = PSPACE`** — task `M15-BGS-EQUAL`.

The classical collapsing oracle of Baker, Gill and Solovay is a `PSPACE`-complete language.  With
`A = TQBF`:

* `NP^A ⊆ PSPACE`: every witness is tried in turn, as in `Start/OracleNPSpace.lean`, but the
  verifier is compiled by `Complexity.Space.Elim.compileT` with the oracle replaced by the
  iteration that decides `TQBF` in polynomial space (`Start/QbfEvalCob.lean`), run as a subprogram
  on the scratch registers (`Complexity.Space.Elim.iterGadget`).  No oracle machine is left, so
  the language is in `PSPACE` outright.  (In Cobham's model the deterministic enumeration of the
  witnesses suffices; Savitch's theorem is not needed.)
* `PSPACE ⊆ P^A`: a `PSPACE` language reduces to `TQBF` by a Cobham term
  (`Complexity.Space.pspaceHard_tqbfLang'`), and one query decides it.
* `P^A ⊆ NP^A` (`Complexity.inNP_rel_of_inP_rel`) closes the circle.

Main results:

* `Complexity.Space.Elim.pspace_of_inNP_rel_gadget` — `NP^A ⊆ PSPACE` for every oracle `A` with a
  gadget of polynomial space;
* `Complexity.Space.Elim.tqbf_gadget` — `TQBF` has one;
* **`Complexity.bgs_equal_tqbf`** — `P^TQBF = NP^TQBF`, and both are `PSPACE`.
-/

import Mathlib
import Start.OracleElimGadget
import Start.OracleNPSpace
import Start.QbfEvalCob
import Start.QbfHard

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Qbf

/-- The facts behind `Complexity.Qbf.tqbf_pspace`: the evaluator of `TQBF`, as an iteration of
Cobham terms, halts through registers bounded by `EvalW.regBound` and answers in register `2`. -/
theorem tqbf_iter (x : List Bool) : ∃ T,
    (∀ k ≤ T, ∀ w ∈ Space.cobIter EvalW.initT EvalW.stepT x k,
      w.length ≤ EvalW.regBound x.length) ∧
    (∀ k < T, (Space.cobIter EvalW.initT EvalW.stepT x k).getD 5 [] ≠ []) ∧
    (Space.cobIter EvalW.initT EvalW.stepT x T).getD 5 [] = [] ∧
    ((Space.cobIter EvalW.initT EvalW.stepT x T).getD 2 [] ≠ [] ↔ tqbfLang x) := by
  obtain ⟨t, ⟨T, hTH, hTt⟩, htH⟩ := EvalW.halts x
  refine ⟨T, fun k _ w hw => ?_, fun k hk => ?_, ?_, ?_⟩
  · rw [EvalW.cobIter_eq] at hw
    exact EvalW.encS_bound (EvalW.inv_iterate x k) w hw
  · rw [EvalW.cobIter_eq]
    exact hTH k hk
  · rw [EvalW.cobIter_eq, hTt]
    exact htH
  · rw [EvalW.cobIter_eq, hTt, ← EvalW.accepts_iff]
    simp only [EvalW.encS, List.getD_cons_succ, List.getD_cons_zero]
    constructor
    · intro hM
      exact ⟨t, ⟨T, hTH, hTt⟩, htH, hM⟩
    · rintro ⟨t', ht', ht'H, ht'M⟩
      rwa [(EvalW.Steps.halt_unique ⟨T, hTH, hTt⟩ ht' htH ht'H)]

end Qbf

namespace Space

namespace Elim

open Prog Tracks NPW

/-! ### `NP^A ⊆ PSPACE` for an oracle with a gadget -/

/-- The body of the witness loop, with the gadget `G` for the queries. -/
def npBodyT (v : CobQ) (K : ℕ) (G : ℕ → ℕ → ℕ → Prog) : Prog :=
  .seq (compileT K G (tF v) [0, 1, 2] 4 6) (.seq (assign K 4 2) (.seq (clear K 4)
    (.seq (compileT K G tNA [1] 3 6) (.seq (compileT K G tInc [1] 4 6)
      (.seq (assign K 4 1) (clear K 4))))))

/-- The whole decider. -/
def npProgT (v : CobQ) (a k K : ℕ) (G : ℕ → ℕ → ℕ → Prog) : Prog :=
  .seq (write true) (.seq (copyInput K 0) (.seq (compileT K G (tZ a k) [0] 1 6)
    (.seq (compileT K G tT [] 3 6) (.seq (whileNE 3 (npBodyT v K G)) (mvR 5)))))

section Loop

variable {A : Oracle} {G : ℕ → ℕ → ℕ → Prog} {q : ℕ} {T : ℕ → ℕ} {K : ℕ} {x : List Bool}
  {B : ℕ} (hTm : Monotone T) (hTid : ∀ n, n ≤ T n) (hG : GadgetOK A G q T K x B)

include hTm hTid hG

theorem runs_npBodyT (v : CobQ) (N : ℕ) (u f c : Word)
    (i : ℕ) (hKF : 6 + (tF v).need + q ≤ K) (hKN : 6 + tNA.need + q ≤ K)
    (hKI : 6 + tInc.need + q ≤ K)
    (hx : x.length ≤ N) (hu : u.length ≤ N) (hf : f.length ≤ 1) (hc : c.length ≤ N)
    (hN1 : 1 ≤ N) (hBF : (T ((tF v).spaceW N) + 3) * wd K ≤ B)
    (hBN : (T (tNA.spaceW N) + 3) * wd K ≤ B) (hBI : (T (tInc.spaceW N) + 3) * wd K ≤ B) :
    Runs x B (npBodyT v K G) ⟨lay K (regs x u f c []), 0, i⟩
      ⟨lay K (regs x (incrW u) (if CobQ.eval A v [x, decodeW u] = [] then f else [true])
        (notAllW u) []), 0, i⟩ := by
  have hB : (N + 3) * wd K ≤ B := bT hTm hTid (CobQ.le_spaceW (tF v) N) hBF
  have hf'1 : (if CobQ.eval A v [x, decodeW u] = [] then f else [true]).length ≤ 1 := by
    split_ifs <;> simp [hf]
  have hna := length_notAllW_le u
  unfold npBodyT
  have h1 := compileTOK (A := A) (K := K) (x := x) (B := B) hTm hTid hG (tF v) [0, 1, 2] 4 6
    (regs x u f c []) N i (by simp) (by omega) (by simp) hKF
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N hx hu (by omega) hc (by simp)) hBF
  simp only [List.map_cons, List.map_nil, regs_zero, regs_one, regs_two, eval_tF,
    update_regs_four] at h1
  generalize (if CobQ.eval A v [x, decodeW u] = [] then f else [true]) = f' at h1 hf'1 ⊢
  refine h1.seq ?_
  refine Runs.seq ((runs_assign _ 4 2 (by omega) (by omega) (by omega) N (by simp; omega)
    (by simp; omega) hB i).of_eq rfl (by rw [regs_four, update_regs_two])) ?_
  refine Runs.seq ((runs_clear _ 4 (by omega) N (by simp; omega) hB i).of_eq rfl
    (by rw [update_regs_four])) ?_
  have h4 := compileTOK (A := A) (K := K) (x := x) (B := B) hTm hTid hG tNA [1] 3 6
    (regs x u f' c []) N i (by simp) (by omega) (by simp) hKN
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N hx hu (by omega) hc (by simp)) hBN
  simp only [List.map_cons, List.map_nil, regs_one, tNA, CobQ.eval_ofCob, eval_notAllC,
    update_regs_three] at h4
  refine Runs.seq h4 ?_
  have h5 := compileTOK (A := A) (K := K) (x := x) (B := B) hTm hTid hG tInc [1] 4 6
    (regs x u f' (notAllW u) []) N i (by simp) (by omega) (by simp) hKI
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N hx hu (by omega) (by omega) (by simp)) hBI
  simp only [List.map_cons, List.map_nil, regs_one, tInc, CobQ.eval_ofCob, eval_incrC,
    update_regs_four] at h5
  refine Runs.seq h5 ?_
  refine Runs.seq ((runs_assign _ 4 1 (by omega) (by omega) (by omega) N (by simp; omega)
    (by simp; omega) hB i).of_eq rfl (by rw [regs_four, update_regs_one])) ?_
  exact (runs_clear _ 4 (by omega) N (by simp; omega) hB i).of_eq rfl (by rw [update_regs_four])

end Loop

/-- The number of registers, with the scratch registers of the gadget. -/
def npKT (q : ℕ) (v : CobQ) (a k : ℕ) : ℕ := npK v a k + q

/-- The space bound. -/
def npBT (T : ℕ → ℕ) (q : ℕ) (v : CobQ) (a k n : ℕ) : ℕ :=
  (T (SW v a k (NW a k n)) + 3) * wd (npKT q v a k)

theorem runs_npProgT {A : Oracle} {G : ℕ → ℕ → ℕ → ℕ → Prog} {q : ℕ} {T : ℕ → ℕ}
    (hTm : Monotone T) (hTid : ∀ n, n ≤ T n) (hG : ∀ K x B, GadgetOK A (G K) q T K x B)
    (v : CobQ) (a k : ℕ) (x : List Bool) :
    Runs x (npBT T q v a k x.length) (npProgT v a k (npKT q v a k) (G (npKT q v a k)))
      ⟨fun _ => false, 0, 0⟩
      ⟨lay (npKT q v a k) (regs x (bits (mW a k x.length) (2 ^ mW a k x.length))
        (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)) [] []), 5, x.length⟩ := by
  set n := x.length with hn
  set m := mW a k n with hm
  set N := NW a k n with hN
  set K := npKT q v a k with hK
  set B := npBT T q v a k n with hB
  have hKv : 7 + (tF v).need + tNA.need + tInc.need + (tZ a k).need + tT.need + q = K := rfl
  have hB0 : (T (SW v a k N) + 3) * wd K ≤ B := le_rfl
  have hSv : SW v a k N =
      (tF v).spaceW N + tNA.spaceW N + tInc.spaceW N + (tZ a k).spaceW N + tT.spaceW N := rfl
  have hNv : N = n + m + 1 := rfl
  have hle := CobQ.le_spaceW (tF v) N
  have hBF : (T ((tF v).spaceW N) + 3) * wd K ≤ B := bTT hTm hTid (by omega) hB0
  have hBN : (T (tNA.spaceW N) + 3) * wd K ≤ B := bTT hTm hTid (by omega) hB0
  have hBI : (T (tInc.spaceW N) + 3) * wd K ≤ B := bTT hTm hTid (by omega) hB0
  have hBZ : (T ((tZ a k).spaceW N) + 3) * wd K ≤ B := bTT hTm hTid (by omega) hB0
  have hBT : (T (tT.spaceW N) + 3) * wd K ≤ B := bTT hTm hTid (by omega) hB0
  have hB3 : (N + 3) * wd K ≤ B := bT hTm hTid (by omega) hB0
  have hwd : 5 < wd K := by womega
  have hwdB : wd K < B := lt_of_lt_of_le (by nlinarith) hB3
  have hGK := hG K x B
  unfold npProgT
  refine (runs_write true _ 0 0).seq ?_
  rw [lay_empty K]
  refine (runs_copyInput (fun _ => []) 0 (by omega) rfl N (by omega) hB3).seq ?_
  rw [update_empty_zero]
  have hz := compileTOK (A := A) (K := K) (x := x) (B := B) hTm hTid hGK (tZ a k) [0] 1 6
    (regs x [] [] [] []) N n (by simp) (by omega) (by simp) (by omega)
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N (by omega) (by simp) (by simp) (by simp) (by simp)) hBZ
  simp only [List.map_cons, List.map_nil, regs_zero, eval_tZ, update_regs_one, ← hn] at hz
  rw [show a * (n + 1) ^ k + 1 = m from rfl, ← bits_zero] at hz
  refine Runs.seq hz ?_
  have ht := compileTOK (A := A) (K := K) (x := x) (B := B) hTm hTid hGK tT [] 3 6
    (regs x (bits m 0) [] [] []) N n (by simp) (by omega) (by simp) (by omega)
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N (by omega) (by simp; omega) (by simp) (by simp) (by simp)) hBT
  simp only [List.map_nil, tT, CobQ.eval_ofCob, Cob.eval_trueC, update_regs_three] at ht
  refine Runs.seq ht ?_
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hloop := runs_whileNE (x := x) (B := B)
    (fun j => regs x (bits m j) (foundW A v x m j) (contW m j) []) 3 (2 ^ m) (K := K)
    (by omega) (npBodyT v K (G K)) (fun j hj => by simp [contW, hj]) (by simp [contW]) hwdB n
    (fun j hj => by
      have := runs_npBodyT hTm hTid hGK v N (bits m j) (foundW A v x m j) (contW m j) n
        (by omega) (by omega) (by omega) (by omega) (by simp; omega) (length_foundW_le A v x m j)
        (by simp only [contW, hj, if_true, List.length_singleton]; omega) (by omega) hBF hBN hBI
      refine this.of_eq rfl ?_
      rw [incrW_bits, notAllW_bits m j hj]
      rfl)
  have h0 : regs x (bits m 0) [] [true] [] =
      regs x (bits m 0) (foundW A v x m 0) (contW m 0) [] := by
    simp [foundW, contW, hpos]
  rw [h0]
  refine Runs.seq hloop ?_
  simp only [contW, lt_irrefl, if_false]
  exact (runs_mvR 5 _ 0 n (by omega)).of_eq rfl (by simp)

/-- **`NP^A ⊆ PSPACE`** for every oracle `A` with a gadget of polynomial space: try every
witness, answering the queries with the gadget. -/
theorem pspace_of_inNP_rel_gadget {A : Oracle} {G : ℕ → ℕ → ℕ → ℕ → Prog} {q : ℕ}
    {T : ℕ → ℕ} (hTm : Monotone T) (hTid : ∀ n, n ≤ T n) (hTp : PolyBound T)
    (hG : ∀ K x B, GadgetOK A (G K) q T K x B) {L : Language} (hL : InNP_rel A L) :
    PSPACE L := by
  obtain ⟨v, p, ⟨a, k, ha⟩, -, hlen, hLv⟩ := hL
  have hid : PolyBound (fun n => n) := ⟨1, 1, fun n => by simp⟩
  have hak : PolyBound (fun n => a * (n + 1) ^ k) := ⟨a, k, fun _ => le_rfl⟩
  have hNW : PolyBound (NW a k) :=
    PolyBound.mono (((hid.add hak).add (polyBound_const 1)).add (polyBound_const 1))
      (fun _ => le_rfl)
  have hSW : PolyBound (SW v a k) :=
    PolyBound.mono (((((CobQ.spaceW_polyBound (tF v)).add (CobQ.spaceW_polyBound tNA)).add
      (CobQ.spaceW_polyBound tInc)).add (CobQ.spaceW_polyBound (tZ a k))).add
      (CobQ.spaceW_polyBound tT)) (fun _ => le_rfl)
  refine Prog.pspace_of_runs (npProgT v a k (npKT q v a k) (G (npKT q v a k))) L
    (fun x => npBT T q v a k x.length) (npBT T q v a k)
    (PolyBound.mono (PolyBound.mul_const' ((hTp.comp (hSW.comp hNW)).add (polyBound_const 3))
      (wd (npKT q v a k))) (fun _ => le_rfl)) _ (fun x => ?_) (fun x => le_rfl)
    (runs_npProgT hTm hTid hG v a k) (fun x => ?_)
  · have : 1 ≤ wd (npKT q v a k) := by womega
    unfold npBT
    nlinarith
  · dsimp only
    have := lay_pres (K := npKT q v a k) (regs x (bits (mW a k x.length) (2 ^ mW a k x.length))
      (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)) [] []) 2
      (by unfold npKT npK; omega) 0
    simp only [zero_mul, zero_add, regs_two] at this
    have h5 : lay (npKT q v a k) (regs x (bits (mW a k x.length) (2 ^ mW a k x.length))
        (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)) [] []) 5 = true ↔
        0 < (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)).length := by
      rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, this]
      exact decide_eq_true_iff
    rw [h5, hLv x, List.length_pos_iff, foundW_ne_nil_iff, mW]
    exact exists_witness_iff A v x _ (fun w hw => le_trans (hlen x w hw) (ha _))

/-! ### The oracle `TQBF` -/

open Classical in
/-- The oracle `TQBF`. -/
noncomputable def tqbfOracle : Oracle := fun w => decide (Qbf.tqbfLang w)

theorem tqbfOracle_iff (w : Word) : tqbfOracle w = true ↔ Qbf.tqbfLang w := by
  simp [tqbfOracle]

/-- **`TQBF` has a gadget of polynomial space**: the iteration of `Start/QbfEvalCob.lean`. -/
theorem tqbf_gadget : ∃ (G : ℕ → ℕ → ℕ → ℕ → Prog) (q : ℕ) (T : ℕ → ℕ), Monotone T ∧
    (∀ n, n ≤ T n) ∧ PolyBound T ∧ ∀ K x B, GadgetOK tqbfOracle (G K) q T K x B := by
  obtain ⟨c, e, hce⟩ := Qbf.EvalW.polyBound_regBound
  have hbm : Monotone (fun n => c * (n + 1) ^ e) := fun _ _ h =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  refine ⟨fun K => iterGadget K 6 5 2 Qbf.EvalW.initT Qbf.EvalW.stepT,
    2 * 6 + 1 + Cob.needs Qbf.EvalW.initT + Cob.needs Qbf.EvalW.stepT,
    gadgetT (fun n => c * (n + 1) ^ e) Qbf.EvalW.initT Qbf.EvalW.stepT, gadgetT_mono hbm _ _,
    le_gadgetT _ _ _, gadgetT_polyBound ⟨c, e, fun _ => le_rfl⟩ _ _, fun K x B => ?_⟩
  refine gadgetOK_iter _ _ 6 5 2 Qbf.tqbfLang tqbfOracle tqbfOracle_iff _ hbm rfl
    Qbf.EvalW.length_stepT (by norm_num) (by norm_num) (fun y => ?_)
  obtain ⟨T, h1, h2, h3, h4⟩ := Qbf.tqbf_iter y
  exact ⟨T, fun k hk w hw => le_trans (h1 k hk w hw) (hce _), h2, h3, h4⟩

/-- **`NP^TQBF ⊆ PSPACE`.** -/
theorem pspace_of_inNP_rel_tqbf {L : Language} (hL : InNP_rel tqbfOracle L) : PSPACE L := by
  obtain ⟨G, q, T, hTm, hTid, hTp, hG⟩ := tqbf_gadget
  exact pspace_of_inNP_rel_gadget hTm hTid hTp hG hL

/-- **`PSPACE ⊆ P^TQBF`**, by one query on the reduction to `TQBF`. -/
theorem inP_rel_tqbf_of_pspace {L : Language} (hL : PSPACE L) : InP_rel tqbfOracle L := by
  obtain ⟨r, hr⟩ := pspaceHard_tqbfLang' L hL
  refine ⟨.comp .query [CobQ.ofCob r], fun x => ?_⟩
  rw [hr x]
  simp only [CobQ.eval_comp, CobQ.eval_query, CobQ.eval_ofCob, List.map_cons, List.map_nil,
    List.getD_cons_zero]
  by_cases h : Qbf.tqbfLang (r.eval [x])
  · simp [(tqbfOracle_iff _).2 h, h]
  · have : tqbfOracle (r.eval [x]) = false := by
      cases e : tqbfOracle (r.eval [x])
      · rfl
      · exact absurd ((tqbfOracle_iff _).1 e) h
    simp [this, h]

end Elim

end Space

open Space.Elim in
/-- **`P^TQBF = NP^TQBF = PSPACE`** (Baker, Gill and Solovay's collapsing oracle): with the
oracle `TQBF`, a language is in `P` iff it is in `NP` iff it is in `PSPACE`. -/
theorem bgs_equal_tqbf (L : Language) :
    (InP_rel tqbfOracle L ↔ InNP_rel tqbfOracle L) ∧ (InNP_rel tqbfOracle L ↔ Space.PSPACE L) :=
  ⟨⟨inNP_rel_of_inP_rel, fun h => inP_rel_tqbf_of_pspace (pspace_of_inNP_rel_tqbf h)⟩,
    ⟨pspace_of_inNP_rel_tqbf, fun h => inNP_rel_of_inP_rel (inP_rel_tqbf_of_pspace h)⟩⟩

/-- `P^A = NP^A` for `A = TQBF`. -/
theorem peqNP_rel_tqbf : PeqNP_rel Space.Elim.tqbfOracle :=
  fun L hL => ((bgs_equal_tqbf L).1).2 hL

end Complexity
