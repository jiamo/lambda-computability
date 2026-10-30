/-
**A gadget for an oracle decided by an iteration of Cobham terms.**

`Start/CobhamIterate.lean` decides a language in polynomial space by iterating Cobham terms on
registers `0, …, 2m`.  This module runs the same iteration on the registers from `fr` on, as a
subprogram of a larger register file, on a word taken from another register: it is a gadget in
the sense of `Start/OracleElimSpace.lean` (`Complexity.Space.Elim.GadgetOK`).

* `Complexity.Space.Elim.regsAt` — a register file with a word and a state from register `b` on;
* `Complexity.Space.Elim.runs_iterBodyAt` — one round of the iteration there;
* `Complexity.Space.Elim.iterGadget` — copy the query into register `fr`, compute the initial
  state, iterate while register `fr + h + 1` is non-empty, write the answer, clear the scratch;
* **`Complexity.Space.Elim.gadgetOK_iter`** — it is a gadget for the language, with
  `2m + 1 + needs init + needs step` scratch registers and a polynomial space function
  (`Complexity.Space.Elim.gadgetT`).
-/

import Mathlib
import Start.OracleElimSpace
import Start.CobhamIterate

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace Elim

open Prog Tracks

/-! ### Iterations on the registers from `b` on -/

/-- The register file `R` with the word `y` in register `b` and the words `ws` after it, the
registers from `b + |ws| + 1` on being empty. -/
def regsAt (R : ℕ → List Bool) (b : ℕ) (y : List Bool) (ws : List (List Bool)) :
    ℕ → List Bool :=
  fun r => if b ≤ r then (y :: ws).getD (r - b) [] else R r

/-- One round of the iteration on the registers from `b` on. -/
def iterBodyAt (K b m : ℕ) (step : List Cob) : Prog :=
  .seq (compiles K step (List.range' b (m + 1)) (b + m + 1) (b + 2 * m + 1))
    (.seq (assignFrom K (b + m + 1) (b + 1) m) (clearFrom K (b + m + 1) m))

theorem map_range'_regsAt (R : ℕ → List Bool) (b : ℕ) (y : List Bool) (ws : List (List Bool)) :
    (List.range' b (ws.length + 1)).map (regsAt R b y ws) = y :: ws := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  rw [List.getElem_map, List.getElem_range']
  simp only [regsAt, one_mul]
  rw [if_pos (Nat.le_add_right b i), Nat.add_sub_cancel_left]
  exact List.getD_eq_getElem _ _ h₂

theorem regsAt_high {R : ℕ → List Bool} {b : ℕ} {y : List Bool} {ws : List (List Bool)} {r : ℕ}
    (hr : b + ws.length + 1 ≤ r) : regsAt R b y ws r = [] := by
  simp only [regsAt]
  rw [if_pos (by omega)]
  exact List.getD_eq_default _ _ (by simp; omega)

theorem regsAt_low {R : ℕ → List Bool} {b : ℕ} {y : List Bool} {ws : List (List Bool)} {r : ℕ}
    (hr : r < b) : regsAt R b y ws r = R r := by
  simp only [regsAt]
  rw [if_neg (by omega)]

theorem regsAt_len {R : ℕ → List Bool} {b : ℕ} {y : List Bool} {ws : List (List Bool)} {N : ℕ}
    (hR : ∀ r, (R r).length ≤ N) (hN : ∀ w ∈ y :: ws, w.length ≤ N) (r : ℕ) :
    (regsAt R b y ws r).length ≤ N := by
  simp only [regsAt]
  split_ifs
  · exact Cob.getD_length_le hN _
  · exact hR r

variable {K : ℕ} {x : List Bool} {B : ℕ}

theorem runs_iterBodyAt (step : List Cob) (b m : ℕ) (hK : b + 2 * m + 1 + Cob.needs step ≤ K)
    (hs : step.length = m) (R : ℕ → List Bool) (y : List Bool) (ws : List (List Bool))
    (hws : ws.length = m) (N N' : ℕ) (hR : ∀ r, (R r).length ≤ N)
    (hN : ∀ w ∈ y :: ws, w.length ≤ N) (hNN : N ≤ N')
    (hsp : ∀ g ∈ step, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B)
    (hB : (N' + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (iterBodyAt K b m step) ⟨lay K (regsAt R b y ws), 0, i⟩
      ⟨lay K (regsAt R b y (step.map fun g => g.eval (y :: ws))), 0, i⟩ := by
  set ws' := step.map fun g => g.eval (y :: ws) with hws'
  have hws'len : ws'.length = m := by simp [ws', hs]
  have hws'N : ∀ w ∈ ws', w.length ≤ N' := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
    exact le_trans (Cob.eval_length_le g _ N hN) (hsp g hg).1
  have hlen : ∀ r, (regsAt R b y ws r).length ≤ N := regsAt_len hR hN
  have hc := Space.runs_compiles (K := K) (x := x) (B := B) step (compilesOK step)
    (List.range' b (m + 1)) (b + 2 * m + 1) hK N N' i (b + m + 1) (regsAt R b y ws)
    (fun a ha => by rw [List.mem_range'_1] at ha; omega) (by omega)
    (fun r hr => regsAt_high (by omega))
    (fun a _ => hlen a)
    (fun r => le_trans (hlen r) hNN) hsp
  have hmap : (List.range' b (m + 1)).map (regsAt R b y ws) = y :: ws := by
    rw [← hws]; exact map_range'_regsAt R b y ws
  rw [hmap, ← hws'] at hc
  unfold iterBodyAt
  refine hc.seq ?_
  set R1 := setFrom (regsAt R b y ws) (b + m + 1) ws' with hR1
  have hR1N : ∀ r, (R1 r).length ≤ N' := by
    intro r
    simp only [R1, setFrom]
    split_ifs
    · exact Cob.getD_length_le hws'N _
    · exact le_trans (hlen r) hNN
  refine (runs_assignFrom m R1 (b + m + 1) (b + 1) (by omega) (by omega) N' hR1N hB i).seq ?_
  refine (runs_clearFrom m _ (b + m + 1) (by omega) N' (fun r => by
    split_ifs
    · exact hR1N _
    · exact hR1N r) hB i).of_eq rfl ?_
  congr 2
  funext r
  simp only [R1, setFrom, regsAt, hws'len]
  by_cases h1 : r < b
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  by_cases h2 : r = b
  · subst h2
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos le_rfl, if_pos le_rfl,
      Nat.sub_self]
    rfl
  by_cases h3 : r < b + 1 + m
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show r - b = (r - (b + 1)) + 1 by omega, List.getD_cons_succ]
    congr 1
    omega
  by_cases h4 : r < b + m + 1 + m
  · rw [if_pos (by omega), if_pos (by omega)]
    exact (List.getD_eq_default _ _ (by simp; omega)).symm
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
      if_pos (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

/-! ### The gadget -/

/-- **The gadget of an iteration**: copy the query (register `src`) into register `fr`, compute
the initial state into the registers `fr + 1, …, fr + m`, iterate while register `fr + h + 1` is
non-empty, set register `d` to `[true]` if register `fr + a + 1` is non-empty and to `[]`
otherwise, and clear the registers `fr, …, fr + m`. -/
def iterGadget (K m h a : ℕ) (init step : List Cob) (src d fr : ℕ) : Prog :=
  .seq (assign K src fr)
    (.seq (compiles K init [fr] (fr + 1) (fr + m + 1))
      (.seq (whileNE (fr + h + 1) (iterBodyAt K fr m step))
        (.seq (clear K d)
          (.seq (whileNE (fr + a + 1) (.seq (clear K (fr + a + 1)) (append K d true)))
            (clearFrom K fr (m + 1))))))

/-- The work space of one round of the terms. -/
def gadgetSW (init step : List Cob) (M : ℕ) : ℕ := Cob.spaceWs init M + Cob.spaceWs step M

/-- A bound on every register while the gadget runs, for registers of length at most `n`. -/
def gadgetN (bnd : ℕ → ℕ) (n : ℕ) : ℕ := bnd n + n + 1

/-- The space function of the gadget. -/
def gadgetT (bnd : ℕ → ℕ) (init step : List Cob) (n : ℕ) : ℕ :=
  gadgetN bnd n + gadgetSW init step (gadgetN bnd n) +
    gadgetSW init step (gadgetN bnd n + gadgetSW init step (gadgetN bnd n))

theorem gadgetSW_mono (init step : List Cob) : Monotone (gadgetSW init step) :=
  fun _ _ h => Nat.add_le_add (Cob.spaceWs_mono init h) (Cob.spaceWs_mono step h)

theorem gadgetT_mono {bnd : ℕ → ℕ} (hbm : Monotone bnd) (init step : List Cob) :
    Monotone (gadgetT bnd init step) := by
  intro n n' h
  have hN : gadgetN bnd n ≤ gadgetN bnd n' := by
    unfold gadgetN; have := hbm h; omega
  have h1 := gadgetSW_mono init step hN
  have h2 := gadgetSW_mono init step (Nat.add_le_add hN h1)
  unfold gadgetT
  omega

theorem le_gadgetT (bnd : ℕ → ℕ) (init step : List Cob) (n : ℕ) : n ≤ gadgetT bnd init step n := by
  unfold gadgetT gadgetN; omega

theorem gadgetT_polyBound {bnd : ℕ → ℕ} (hb : PolyBound bnd) (init step : List Cob) :
    PolyBound (gadgetT bnd init step) := by
  have hSW : PolyBound (gadgetSW init step) :=
    (Cob.spaceWs_polyBound init).add (Cob.spaceWs_polyBound step)
  have hN : PolyBound (gadgetN bnd) := (hb.add Cob.polyBound_id).add (polyBound_const 1)
  have hN' : PolyBound (fun n => gadgetN bnd n + gadgetSW init step (gadgetN bnd n)) :=
    hN.add (hSW.comp hN)
  exact hN'.add (hSW.comp hN')

/-- **The gadget of an iteration deciding `L`** is a gadget for every oracle `A` agreeing with
`L`, given the hypotheses of `Complexity.Space.pspace_of_cobIter` with a monotone bound. -/
theorem gadgetOK_iter (init step : List Cob) (m h a : ℕ) (L : Language) (A : Oracle)
    (hAL : ∀ w, A w = true ↔ L w) (bnd : ℕ → ℕ) (hbm : Monotone bnd) (hi : init.length = m)
    (hs : step.length = m) (hh : h < m) (ha : a < m)
    (hrun : ∀ y : List Bool, ∃ T, (∀ k ≤ T, ∀ w ∈ cobIter init step y k, w.length ≤ bnd y.length) ∧
      (∀ k < T, (cobIter init step y k).getD h [] ≠ []) ∧
      (cobIter init step y T).getD h [] = [] ∧
      ((cobIter init step y T).getD a [] ≠ [] ↔ L y)) :
    GadgetOK A (iterGadget K m h a init step) (2 * m + 1 + Cob.needs init + Cob.needs step)
      (gadgetT bnd init step) K x B := by
  intro src d fr R Nq i hsrc hd hq hfr hR hB
  set X := R src with hX
  obtain ⟨Tx, hTb, hTne, hTe, hTa⟩ := hrun X
  set N := gadgetN bnd Nq with hNdef
  set N' := N + gadgetSW init step N with hN'def
  have hBeq : gadgetT bnd init step Nq = N' + gadgetSW init step N' := rfl
  rw [hBeq] at hB
  clear_value N N'
  have hXN : X.length ≤ Nq := hR src
  have hbX : bnd X.length ≤ bnd Nq := hbm hXN
  have hNq : Nq + 1 ≤ N := by rw [hNdef, gadgetN]; omega
  have hbN : bnd Nq ≤ N := by rw [hNdef, gadgetN]; omega
  have hNN' : N ≤ N' := by omega
  have hwd : 1 ≤ wd K := by womega
  have hN'B : (N' + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  have hNB : (N + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hN'B
  have hwdB : wd K < B := by nlinarith
  have hSWN : gadgetSW init step N = Cob.spaceWs init N + Cob.spaceWs step N := rfl
  have hSWN' : gadgetSW init step N' = Cob.spaceWs init N' + Cob.spaceWs step N' := rfl
  have hspi : ∀ g ∈ init, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B := by
    intro g hg
    have h1 := Cob.spaceWs_le init N g hg
    have h2 := Cob.spaceWs_le init N' g hg
    exact ⟨by omega, le_trans (Nat.mul_le_mul_right _ (by omega)) hB⟩
  have hsps : ∀ g ∈ step, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B := by
    intro g hg
    have h1 := Cob.spaceWs_le step N g hg
    have h2 := Cob.spaceWs_le step N' g hg
    exact ⟨by omega, le_trans (Nat.mul_le_mul_right _ (by omega)) hB⟩
  have hRN : ∀ r, (R r).length ≤ N := fun r => by have := hR r; omega
  have hstN : ∀ k ≤ Tx, ∀ w ∈ X :: cobIter init step X k, w.length ≤ N := by
    intro k hk w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · omega
    · have := hTb k hk w hw; omega
  have hFN : ∀ k ≤ Tx, ∀ r, (regsAt R fr X (cobIter init step X k) r).length ≤ N :=
    fun k hk => regsAt_len hRN (hstN k hk)
  unfold iterGadget
  -- copy the query
  refine (runs_assign R src fr (by omega) (by omega) (by omega) N (hRN src) (hRN fr) hNB i).seq ?_
  -- the initial state
  have hc := Space.runs_compiles (K := K) (x := x) (B := B) init (compilesOK init) [fr] (fr + m + 1)
    (by omega) N N' i (fr + 1) (Function.update R fr X)
    (by simp) (by omega) (fun r hr => by rw [Function.update_of_ne (by omega)]; exact hfr r (by omega))
    (fun a ha => by
      rw [List.mem_singleton] at ha; subst ha; simp only [Function.update_self]; omega)
    (fun r => by
      rw [Function.update_apply]; split_ifs
      · omega
      · have := hRN r; omega)
    hspi
  have h0 : setFrom (Function.update R fr X) (fr + 1)
      (init.map fun g => g.eval ([fr].map (Function.update R fr X))) =
      regsAt R fr X (cobIter init step X 0) := by
    funext r
    simp only [setFrom, regsAt, List.map_cons, List.map_nil, Function.update_self, cobIter,
      List.length_map, hi]
    by_cases h1 : r < fr
    · rw [if_neg (by omega), if_neg (by omega), Function.update_of_ne (by omega)]
    by_cases h2 : r = fr
    · subst h2
      rw [if_neg (by omega), if_pos le_rfl, Nat.sub_self, Function.update_self]
      rfl
    by_cases h3 : r < fr + 1 + m
    · rw [if_pos (by omega), if_pos (by omega), show r - fr = (r - (fr + 1)) + 1 by omega,
        List.getD_cons_succ]
    · rw [if_neg (by omega), if_pos (by omega), Function.update_of_ne (by omega), hfr r (by omega),
        List.getD_eq_default _ _ (by simp [hi]; omega)]
  rw [h0] at hc
  refine hc.seq ?_
  -- the loop
  refine (runs_whileNE (fun k => regsAt R fr X (cobIter init step X k)) (fr + h + 1) Tx
    (by omega) _ (fun k hk => ?_) ?_ hwdB i (fun k hk => ?_)).seq ?_
  · simp only [regsAt, if_pos (show fr ≤ fr + h + 1 by omega),
      show fr + h + 1 - fr = h + 1 by omega, List.getD_cons_succ]
    exact hTne k hk
  · simp only [regsAt, if_pos (show fr ≤ fr + h + 1 by omega),
      show fr + h + 1 - fr = h + 1 by omega, List.getD_cons_succ]
    exact hTe
  · exact runs_iterBodyAt step fr m (by omega) hs R X (cobIter init step X k)
      (length_cobIter hi hs X k) N N' hRN (hstN k (by omega)) hNN' hsps hN'B i
  -- the answer
  set F := regsAt R fr X (cobIter init step X Tx) with hF
  set Y := (cobIter init step X Tx).getD a [] with hY
  have hFa : F (fr + a + 1) = Y := by
    simp only [F, regsAt, if_pos (show fr ≤ fr + a + 1 by omega),
      show fr + a + 1 - fr = a + 1 by omega, List.getD_cons_succ]
    exact hY.symm
  have hFN : ∀ r, (F r).length ≤ N := hFN Tx le_rfl
  refine (runs_clear F d (by omega) N (hFN d) hNB i).seq ?_
  have hF0N : ∀ r, (Function.update F d [] r).length ≤ N := fun r => by
    rw [Function.update_apply]; split_ifs
    · simp
    · exact hFN r
  -- the final register file before clearing
  obtain ⟨Rf, hRf, hRfN⟩ : ∃ Rf : ℕ → List Bool,
      Runs x B (whileNE (fr + a + 1) (.seq (clear K (fr + a + 1)) (append K d true)))
        ⟨lay K (Function.update F d []), 0, i⟩ ⟨lay K Rf, 0, i⟩ ∧
      (Rf d = if A X then [true] else []) ∧ (∀ r, r ≠ d → r < fr → Rf r = R r) ∧
      ∀ r, Rf r = [] ∨ Rf r = F r ∨ r = d := by
    by_cases hY0 : Y = []
    · refine ⟨Function.update F d [], runs_whileNE (fun _ => Function.update F d []) (fr + a + 1)
        0 (by omega) _ (fun k hk => absurd hk (by omega)) (by
          rw [Function.update_of_ne (by omega), hFa, hY0]) hwdB i
          (fun k hk => absurd hk (by omega)), ?_, ?_, ?_⟩
      · rw [Function.update_self]
        have : A X = false := by
          cases hAX : A X
          · rfl
          · exact absurd (hTa.2 ((hAL X).1 hAX)) (not_not.2 hY0)
        rw [this]; rfl
      · intro r hrd hr
        rw [Function.update_of_ne hrd, hF, regsAt_low hr]
      · intro r
        by_cases hrd : r = d
        · exact Or.inr (Or.inr hrd)
        · exact Or.inr (Or.inl (Function.update_of_ne hrd _ _))
    · let R2 := Function.update (Function.update (Function.update F d []) (fr + a + 1) []) d [true]
      refine ⟨R2, ?_, ?_, ?_, ?_⟩
      · refine (runs_whileNE (fun k => if k = 0 then Function.update F d [] else R2) (fr + a + 1)
          1 (by omega) _ (fun k hk => ?_) ?_ hwdB i (fun k hk => ?_)).of_eq (by simp) (by simp)
        · rw [if_pos (by omega), Function.update_of_ne (by omega), hFa]; exact hY0
        · simp only [one_ne_zero, if_false, R2]
          rw [Function.update_of_ne (by omega), Function.update_self]
        · rw [if_pos (by omega), if_neg (by omega)]
          refine (runs_clear _ (fr + a + 1) (by omega) N (hF0N _) hNB i).seq ?_
          refine (runs_append _ d (by omega) true N (by
            rw [Function.update_of_ne (by omega), Function.update_self]; simp; omega)
            hNB i).of_eq rfl ?_
          have e1 : (Function.update (Function.update F d []) (fr + a + 1) []) d = [] := by
            rw [Function.update_of_ne (by omega), Function.update_self]
          rw [e1, List.nil_append]
      · simp only [R2, Function.update_self]
        have : A X = true := (hAL X).2 (hTa.1 hY0)
        rw [this]; rfl
      · intro r hrd hr
        simp only [R2]
        rw [Function.update_of_ne hrd, Function.update_of_ne (by omega), Function.update_of_ne hrd,
          hF, regsAt_low hr]
      · intro r
        simp only [R2, Function.update_apply]
        split_ifs <;> simp_all
  refine hRf.seq ?_
  have hRfN' : ∀ r, (Rf r).length ≤ N := by
    intro r
    rcases hRfN.2.2 r with h1 | h1 | h1
    · rw [h1]; simp
    · rw [h1]; exact hFN r
    · subst h1; rw [hRfN.1]; split_ifs <;> simp; omega
  refine (runs_clearFrom (m + 1) Rf fr (by omega) N hRfN' hNB i).of_eq rfl ?_
  congr 2
  funext r
  by_cases hrd : r = d
  · subst hrd
    rw [if_neg (by omega), Function.update_self, hRfN.1]
  rw [Function.update_of_ne hrd]
  by_cases hr : r < fr
  · rw [if_neg (by omega), hRfN.2.1 r hrd hr]
  by_cases hr' : r < fr + (m + 1)
  · rw [if_pos (by omega), hfr r (by omega)]
  rw [if_neg (by omega), hfr r (by omega)]
  rcases hRfN.2.2 r with h1 | h1 | h1
  · exact h1
  · rw [h1, hF, regsAt_high (by rw [length_cobIter hi hs]; omega)]
  · exact absurd h1 hrd

end Elim

end Complexity.Space
