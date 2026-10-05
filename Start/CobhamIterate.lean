/-
**Iterating Cobham terms in polynomial space.**

`Start/CobhamPspace.lean` runs one Cobham term on a tape.  Many decision procedures in polynomial
space are not one polynomial-time function but a polynomial-time *step* iterated an exponential
number of times on a state of polynomial size.  This module runs such an iteration on a tape.

A state is a list of `m` words.  The initial state is computed from the input `x` by the terms
`init`, and each further state from `x` and the previous state by the terms `step`
(`Complexity.Space.cobIter`).  The tape program `Complexity.Space.iterDecider` copies the input
into register `0`, computes the initial state into registers `1, …, m`, and then, as long as
register `h + 1` is non-empty, computes the next state into the scratch registers
`m + 1, …, 2m` and copies it back.  At the end it looks at register `a + 1`.

Main results:

* `Complexity.Space.runs_iterBody` — one round of the loop replaces the state by the next one;
* `Complexity.Space.pspace_of_cobIter` — **a language decided by iterating Cobham terms, through
  states of polynomially bounded size, is in `PSPACE`**, however many rounds the iteration takes.
-/

import Mathlib
import Start.CobhamPspace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Prog Tracks

/-- The stages of the iteration: the initial state computed by `init` from `[x]`, then each
state computed by `step` from `x` followed by the previous state. -/
def cobIter (init step : List Cob) (x : List Bool) : ℕ → List (List Bool)
  | 0 => init.map fun g => g.eval [x]
  | k + 1 => step.map fun g => g.eval (x :: cobIter init step x k)

theorem length_cobIter {init step : List Cob} {m : ℕ} (hi : init.length = m)
    (hs : step.length = m) (x : List Bool) : ∀ k, (cobIter init step x k).length = m
  | 0 => by simp [cobIter, hi]
  | k + 1 => by simp [cobIter, hs]

/-- The register file holding `x` in register `0` and the words `ws` in the registers after it. -/
def regsOf (x : List Bool) (ws : List (List Bool)) : ℕ → List Bool := fun r => (x :: ws).getD r []

theorem regsOf_of_le {x : List Bool} {ws : List (List Bool)} {r : ℕ} (hr : ws.length + 1 ≤ r) :
    regsOf x ws r = [] := by
  simp only [regsOf]
  exact List.getD_eq_default _ _ (by simpa using hr)

theorem map_range_regsOf (x : List Bool) (ws : List (List Bool)) :
    (List.range (ws.length + 1)).map (regsOf x ws) = x :: ws := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_map, List.getElem_range, regsOf]
  exact List.getD_eq_getElem _ _ h₂

theorem regsOf_length_le {x : List Bool} {ws : List (List Bool)} {N : ℕ}
    (h : ∀ w ∈ x :: ws, w.length ≤ N) (r : ℕ) : (regsOf x ws r).length ≤ N :=
  Cob.getD_length_le h r

/-- `R (d + j) := R (s + j)` for `j < n`. -/
def assignFrom (K : ℕ) : ℕ → ℕ → ℕ → Prog
  | _, _, 0 => skip
  | s, d, n + 1 => .seq (assign K s d) (assignFrom K (s + 1) (d + 1) n)

variable {K : ℕ} {x : List Bool} {B : ℕ}

theorem runs_assignFrom (n : ℕ) : ∀ (R : ℕ → List Bool) (s d : ℕ), d + n ≤ s → s + n ≤ K →
    ∀ (N : ℕ), (∀ r, (R r).length ≤ N) → (N + 3) * wd K ≤ B → ∀ i,
    Runs x B (assignFrom K s d n) ⟨lay K R, 0, i⟩
      ⟨lay K (fun r => if d ≤ r ∧ r < d + n then R (r - d + s) else R r), 0, i⟩ := by
  induction n with
  | zero =>
      intro R s d _ _ N _ _ i
      refine (runs_skip _ 0 i).of_eq rfl ?_
      congr 2; funext r; simp
  | succ n ih =>
      intro R s d hds hsK N hN hB i
      refine (runs_assign R s d (by omega) (by omega) (by omega) N (hN s) (hN d) hB i).seq ?_
      refine (ih (Function.update R d (R s)) (s + 1) (d + 1) (by omega) (by omega) N (fun r => by
        rw [Function.update_apply]; split_ifs
        · exact hN s
        · exact hN r) hB i).of_eq rfl ?_
      congr 2; funext r
      simp only [Function.update_apply]
      by_cases h1 : r = d
      · subst h1; simp
      · by_cases h2 : d + 1 ≤ r ∧ r < d + 1 + n
        · rw [if_pos h2, if_neg (by omega), if_pos (by omega)]
          congr 1; omega
        · rw [if_neg h2, if_neg h1, if_neg (by omega)]

/-- One round of the loop: compute the next state into the scratch registers `m + 1, …, 2m`, copy
it back into the registers `1, …, m`, and clear the scratch registers. -/
def iterBody (K m : ℕ) (step : List Cob) : Prog :=
  .seq (compiles K step (List.range (m + 1)) (m + 1) (2 * m + 1))
    (.seq (assignFrom K (m + 1) 1 m) (clearFrom K (m + 1) m))

theorem runs_iterBody (step : List Cob) (m : ℕ) (hK : 2 * m + 1 + Cob.needs step ≤ K)
    (hs : step.length = m) (ws : List (List Bool)) (hws : ws.length = m) (N N' : ℕ)
    (hN : ∀ w ∈ x :: ws, w.length ≤ N) (hNN : N ≤ N')
    (hsp : ∀ g ∈ step, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B)
    (hB : (N' + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (iterBody K m step) ⟨lay K (regsOf x ws), 0, i⟩
      ⟨lay K (regsOf x (step.map fun g => g.eval (x :: ws))), 0, i⟩ := by
  set ws' := step.map fun g => g.eval (x :: ws) with hws'
  have hws'len : ws'.length = m := by simp [ws', hs]
  have hws'N : ∀ w ∈ ws', w.length ≤ N' := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
    exact le_trans (Cob.eval_length_le g _ N hN) (hsp g hg).1
  have hc := runs_compiles (K := K) (x := x) (B := B) step (compilesOK step)
    (List.range (m + 1)) (2 * m + 1) hK N N' i (m + 1) (regsOf x ws)
    (fun a ha => by simpa using ha) (by omega)
    (fun r hr => regsOf_of_le (by omega))
    (fun a _ => regsOf_length_le hN a)
    (fun r => le_trans (regsOf_length_le hN r) hNN) hsp
  have hmap : (List.range (m + 1)).map (regsOf x ws) = x :: ws := by
    rw [← hws]; exact map_range_regsOf x ws
  rw [hmap, ← hws'] at hc
  unfold iterBody
  refine hc.seq ?_
  set R1 := setFrom (regsOf x ws) (m + 1) ws' with hR1
  have hR1N : ∀ r, (R1 r).length ≤ N' := by
    intro r
    simp only [R1, setFrom]
    split_ifs
    · exact Cob.getD_length_le hws'N _
    · exact le_trans (regsOf_length_le hN r) hNN
  refine (runs_assignFrom m R1 (m + 1) 1 (by omega) (by omega) N' hR1N hB i).seq ?_
  refine (runs_clearFrom m _ (m + 1) (by omega) N' (fun r => by
    split_ifs
    · exact hR1N _
    · exact hR1N r) hB i).of_eq rfl ?_
  congr 2
  funext r
  simp only [R1, setFrom, regsOf, hws'len]
  rcases r with _ | r
  · simp
  · simp only [List.getD_cons_succ]
    by_cases h1 : r < m
    · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
      congr 1; omega
    · have e1 : ws'.getD r [] = [] := List.getD_eq_default _ _ (by omega)
      have e2 : ws.getD r [] = [] := List.getD_eq_default _ _ (by omega)
      rw [e1]
      split_ifs <;> first
        | rfl
        | exact e2
        | exact List.getD_eq_default _ _ (by omega)

/-- The decider of an iteration: set the ruler, copy the input into register `0`, compute the
initial state, run the loop while register `h + 1` is non-empty, and look at register `a + 1`. -/
def iterDecider (init step : List Cob) (m h a : ℕ) : Prog :=
  .seq (write true) (.seq (copyInput (2 * m + 1 + Cob.needs init + Cob.needs step) 0)
    (.seq (compiles (2 * m + 1 + Cob.needs init + Cob.needs step) init [0] 1 (m + 1))
      (.seq (whileNE (h + 1) (iterBody (2 * m + 1 + Cob.needs init + Cob.needs step) m step))
        (mvR (2 * (a + 1) + 1)))))

/-- **Iterating Cobham terms decides in polynomial space.**  If on every input the iteration of
`step` from the state computed by `init` reaches, through states whose words are polynomially
bounded, a stage at which word `h` is empty (and word `h` is non-empty before), and at that stage
word `a` is non-empty exactly for the inputs in `L`, then `L ∈ PSPACE`. -/
theorem pspace_of_cobIter (init step : List Cob) (m h a : ℕ) (L : Language) (bnd : ℕ → ℕ)
    (hbnd : PolyBound bnd) (hi : init.length = m) (hs : step.length = m) (hh : h < m)
    (ha : a < m)
    (hrun : ∀ x, ∃ T, (∀ k ≤ T, ∀ w ∈ cobIter init step x k, w.length ≤ bnd x.length) ∧
      (∀ k < T, (cobIter init step x k).getD h [] ≠ []) ∧
      (cobIter init step x T).getD h [] = [] ∧
      ((cobIter init step x T).getD a [] ≠ [] ↔ L x)) : PSPACE L := by
  choose T hT using hrun
  set K := 2 * m + 1 + Cob.needs init + Cob.needs step with hK
  let SW : ℕ → ℕ := fun N => Cob.spaceWs init N + Cob.spaceWs step N
  let Nf : ℕ → ℕ := fun n => bnd n + n
  let N'f : ℕ → ℕ := fun n => Nf n + SW (Nf n)
  let Bf : ℕ → ℕ := fun n => (N'f n + SW (N'f n) + 3) * wd K
  have hSWpoly : PolyBound SW := (Cob.spaceWs_polyBound init).add (Cob.spaceWs_polyBound step)
  have hNpoly : PolyBound Nf := hbnd.add Cob.polyBound_id
  have hN'poly : PolyBound N'f := hNpoly.add (hSWpoly.comp hNpoly)
  have hBpoly : PolyBound Bf :=
    PolyBound.mul_const' ((hN'poly.add (hSWpoly.comp hN'poly)).add (polyBound_const 3)) _
  refine pspace_of_runs (iterDecider init step m h a) L (fun x => Bf x.length) Bf hBpoly
    (fun x => ⟨lay K (regsOf x (cobIter init step x (T x))), 2 * (a + 1) + 1, x.length⟩)
    (fun x => by simp only [Bf]; have : 1 ≤ wd K := by womega
                 nlinarith) (fun x => le_rfl) (fun x => ?_) (fun x => ?_)
  · -- the run
    set n := x.length
    set N := Nf n with hNdef
    set N' := N'f n with hN'def
    set B := Bf n with hBdef
    obtain ⟨hTb, hTne, hTe, -⟩ := hT x
    have hNeq : N = bnd n + n := rfl
    have hN'eq : N' = N + (Cob.spaceWs init N + Cob.spaceWs step N) := rfl
    have hBeq : B = (N' + (Cob.spaceWs init N' + Cob.spaceWs step N') + 3) * wd K := rfl
    clear_value N N' B
    have hwd : 1 ≤ wd K := by womega
    have hN'B : (N' + 3) * wd K ≤ B := by rw [hBeq]; exact Nat.mul_le_mul_right _ (by omega)
    have hNN' : N ≤ N' := by omega
    have hspi : ∀ g ∈ init, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B := fun g hg =>
      ⟨by have := Cob.spaceWs_le init N g hg; omega,
       by rw [hBeq]; exact Nat.mul_le_mul_right _ (by have := Cob.spaceWs_le init N' g hg; omega)⟩
    have hsps : ∀ g ∈ step, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B := fun g hg =>
      ⟨by have := Cob.spaceWs_le step N g hg; omega,
       by rw [hBeq]; exact Nat.mul_le_mul_right _ (by have := Cob.spaceWs_le step N' g hg; omega)⟩
    have hstN : ∀ k ≤ T x, ∀ w ∈ x :: cobIter init step x k, w.length ≤ N := by
      intro k hk w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · omega
      · have := hTb k hk w hw
        have e : bnd x.length = bnd n := rfl
        omega
    unfold iterDecider
    refine (runs_write true _ 0 0).seq ?_
    rw [lay_empty K]
    refine (runs_copyInput (K := K) (fun _ => []) 0 (by omega) rfl N'
      (by omega) hN'B).seq ?_
    have hc := runs_compiles (K := K) (x := x) (B := B) init (compilesOK init) [0] (m + 1)
      (by omega) N N' x.length 1 (Function.update (fun _ => []) 0 x)
      (by simp) (by omega) (fun r hr => by rw [Function.update_of_ne (by omega)])
      (fun a ha => by
        rw [List.mem_singleton] at ha; subst ha; simp only [Function.update_self]; omega)
      (fun r => by
        rw [Function.update_apply]; split_ifs
        · omega
        · simp)
      hspi
    have h0 : setFrom (Function.update (fun _ => []) 0 x) 1
        (init.map fun g => g.eval ([0].map (Function.update (fun _ => []) 0 x))) =
        regsOf x (cobIter init step x 0) := by
      funext r
      simp only [setFrom, regsOf, List.map_cons, List.map_nil, Function.update_self, cobIter,
        List.length_map, hi]
      rcases r with _ | r
      · simp
      · rw [List.getD_cons_succ]
        split_ifs with h1
        · congr 1
        · rw [Function.update_of_ne (by omega), List.getD_eq_default _ _ (by simp [hi]; omega)]
    rw [h0] at hc
    refine hc.seq ?_
    refine Runs.seq ?_ ((runs_mvR (2 * (a + 1) + 1) (lay K (regsOf x (cobIter init step x (T x))))
      0 x.length ?_).of_eq rfl (by simp [n]))
    · refine runs_whileNE (fun k => regsOf x (cobIter init step x k)) (h + 1) (T x)
        (by omega) _ (fun k hk => by simpa [regsOf] using hTne k hk) (by simpa [regsOf] using hTe)
        (by rw [hBeq]; nlinarith) x.length (fun k hk => ?_)
      have := runs_iterBody (K := K) (x := x) (B := B) step m (by omega) hs
        (cobIter init step x k) (length_cobIter hi hs x k) N N' (hstN k (by omega)) hNN' hsps
        hN'B x.length
      exact this
    · have : 2 * (a + 1) + 1 < wd K := by womega
      have : wd K ≤ B := by rw [hBeq]; nlinarith
      omega
  · -- the answer
    obtain ⟨-, -, -, hTa⟩ := hT x
    dsimp only
    have := lay_pres (K := K) (regsOf x (cobIter init step x (T x))) (a + 1) (by omega) 0
    simp only [zero_mul, zero_add] at this
    rw [this, decide_eq_true_iff, List.length_pos_iff, ← hTa]
    simp [regsOf]

end Complexity.Space
