/-
**From a CNF to a circuit: the reduction of SAT to CIRCUIT-SAT, on the semantic side.**

`Start/Sat.lean` reads a word as a CNF by a right-to-left token scan (`Complexity.Sat.decode`) and
evaluates it against an assignment by the same scan (`Complexity.Sat.mrun`).  This module builds,
by the *same* scan, a Boolean circuit that computes what the scan computes: four gates per position
of the word, carrying the two accumulators of the evaluator — "every clause read so far is
satisfied" and "the clause being read is already satisfied" — as wires.

The construction is the mathematical half of the reduction `SAT ≤ₘᵖ CIRCUIT-SAT`; the half that
exhibits it as a Cobham (polynomial-time) term is `Start/SatToCircuitCob.lean`.

Main definitions:

* `Complexity.Sat.satBlk` — the four gates emitted at one position of the word;
* `Complexity.Sat.satC` — the circuit of a word: the blocks of its positions on top of the two
  constant gates that start the accumulators.

Main results:

* `Complexity.Sat.wf_satC` — the circuit is well formed;
* `Complexity.Sat.vals_satC` — its two top wires carry the two accumulators of the evaluator;
* `Complexity.Sat.out_satC` — its output is the truth value of the decoded CNF;
* `Complexity.Sat.csat_satC_iff` — **the circuit is satisfiable exactly when the word is in
  `SAT`**.
-/

import Start.CircuitSatLang

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Sat

open Complexity.Tseitin

/-! ### The circuit of a word -/

/-- The four gates emitted at one position of the scan.  With `n = 4 * |u| + 2` gates already
emitted by the suffix `u`, the gate `n - 1` carries the accumulator `allSat` and the gate `n - 2`
the accumulator `curSat`; the new block ends with the two new accumulators, `n + 3` carrying
`allSat` and `n + 2` carrying `curSat`.  The two gates in between compute the value of a literal. -/
def satBlk (b : Bool) (u : Word) : Circuit :=
  match (drun u).phase, b with
  | .esc, true =>
      -- a negative literal, of variable `(drun u).ticks`
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length + 3),
        .neg (4 * u.length + 2), .inp (drun u).ticks]
  | .esc2, true =>
      -- a positive literal, of variable `(drun u).ticks`
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length + 3),
        .disj (4 * u.length + 2) (4 * u.length + 2), .inp (drun u).ticks]
  | .esc2, false =>
      -- a clause separator: the clause just read is conjoined, the accumulator is reset
      [.conj (4 * u.length + 1) (4 * u.length), .disj (4 * u.length + 2) (4 * u.length + 2),
        .cst false, .cst false]
  | _, _ =>
      -- a tick or an escape bit: both accumulators are copied
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length),
        .cst false, .cst false]

/-- The circuit of a word: the blocks of its positions, on top of the initial accumulators
`allSat = true` (gate `1`) and `curSat = false` (gate `0`). -/
def satC : Word → Circuit
  | [] => [.cst true, .cst false]
  | b :: u => satBlk b u ++ satC u

theorem satC_cons (b : Bool) (u : Word) : satC (b :: u) = satBlk b u ++ satC u := rfl

/-! ### The block, case by case -/

theorem satBlk_main (u : Word) (h : (drun u).phase = .main) (b : Bool) :
    satBlk b u =
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length),
        .cst false, .cst false] := by
  cases b <;> simp only [satBlk, h]

theorem satBlk_esc_false (u : Word) (h : (drun u).phase = .esc) :
    satBlk false u =
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length),
        .cst false, .cst false] := by
  simp only [satBlk, h]

theorem satBlk_esc_true (u : Word) (h : (drun u).phase = .esc) :
    satBlk true u =
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length + 3),
        .neg (4 * u.length + 2), .inp (drun u).ticks] := by
  simp only [satBlk, h]

theorem satBlk_esc2_true (u : Word) (h : (drun u).phase = .esc2) :
    satBlk true u =
      [.disj (4 * u.length + 1) (4 * u.length + 1), .disj (4 * u.length) (4 * u.length + 3),
        .disj (4 * u.length + 2) (4 * u.length + 2), .inp (drun u).ticks] := by
  simp only [satBlk, h]

theorem satBlk_esc2_false (u : Word) (h : (drun u).phase = .esc2) :
    satBlk false u =
      [.conj (4 * u.length + 1) (4 * u.length), .disj (4 * u.length + 2) (4 * u.length + 2),
        .cst false, .cst false] := by
  simp only [satBlk, h]

theorem length_satBlk (b : Bool) (u : Word) : (satBlk b u).length = 4 := by
  rcases h : (drun u).phase with _ | _ | _
  · rw [satBlk_main u h]; rfl
  · cases b
    · rw [satBlk_esc_false u h]; rfl
    · rw [satBlk_esc_true u h]; rfl
  · cases b
    · rw [satBlk_esc2_false u h]; rfl
    · rw [satBlk_esc2_true u h]; rfl

@[simp] theorem length_satC (u : Word) : (satC u).length = 4 * u.length + 2 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      rw [satC_cons, List.length_append, length_satBlk, ih, List.length_cons]
      omega

/-! ### Well-formedness -/

theorem wf_block {g₃ g₂ g₁ g₀ : Gate} {C : Circuit} (hC : wf C)
    (h₃ : gateWf (C.length + 3) g₃) (h₂ : gateWf (C.length + 2) g₂)
    (h₁ : gateWf (C.length + 1) g₁) (h₀ : gateWf C.length g₀) :
    wf ([g₃, g₂, g₁, g₀] ++ C) := by
  exact ⟨h₃, h₂, h₁, h₀, hC⟩

theorem wf_satC (u : Word) : wf (satC u) := by
  induction u with
  | nil => exact ⟨trivial, trivial, trivial⟩
  | cons b u ih =>
      have hlen : (satC u).length = 4 * u.length + 2 := length_satC u
      rw [satC_cons]
      rcases h : (drun u).phase with _ | _ | _
      · rw [satBlk_main u h]
        exact wf_block ih (by simp only [gateWf, hlen]; omega) (by simp only [gateWf, hlen]; omega)
          trivial trivial
      · cases b
        · rw [satBlk_esc_false u h]
          exact wf_block ih (by simp only [gateWf, hlen]; omega)
            (by simp only [gateWf, hlen]; omega) trivial trivial
        · rw [satBlk_esc_true u h]
          exact wf_block ih (by simp only [gateWf, hlen]; omega)
            (by simp only [gateWf, hlen]; omega) (by simp only [gateWf, hlen]; omega) trivial
      · cases b
        · rw [satBlk_esc2_false u h]
          exact wf_block ih (by simp only [gateWf, hlen]; omega)
            (by simp only [gateWf, hlen]; omega) trivial trivial
        · rw [satBlk_esc2_true u h]
          exact wf_block ih (by simp only [gateWf, hlen]; omega)
            (by simp only [gateWf, hlen]; omega) (by simp only [gateWf, hlen]; omega) trivial

/-! ### The two accumulators -/

theorem getD_append_add (V l : List Bool) (i : ℕ) :
    (V ++ l).getD (V.length + i) false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    ← List.getD_eq_getElem?_getD]
  simp

theorem getD_append_lt (V l : List Bool) {i : ℕ} (hi : i < V.length) :
    (V ++ l).getD i false = V.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

/-- The values of a circuit whose top four gates are given explicitly. -/
theorem vals_block (x : Word) (g₃ g₂ g₁ g₀ : Gate) (C : Circuit) :
    vals x ([g₃, g₂, g₁, g₀] ++ C)
      = vals x C ++
          [gateVal x (vals x C) g₀,
            gateVal x (vals x C ++ [gateVal x (vals x C) g₀]) g₁,
            gateVal x (vals x C ++ [gateVal x (vals x C) g₀,
              gateVal x (vals x C ++ [gateVal x (vals x C) g₀]) g₁]) g₂,
            gateVal x (vals x C ++ [gateVal x (vals x C) g₀,
              gateVal x (vals x C ++ [gateVal x (vals x C) g₀]) g₁,
              gateVal x (vals x C ++ [gateVal x (vals x C) g₀,
                gateVal x (vals x C ++ [gateVal x (vals x C) g₀]) g₁]) g₂]) g₃] := by
  simp only [List.cons_append, List.nil_append, vals, List.append_assoc]

/-- **The two top wires of the circuit carry the two accumulators of the evaluator.** -/
theorem vals_satC (σ : Word) (u : Word) :
    (vals σ (satC u)).getD (4 * u.length + 1) false = (mrun σ u).allSat ∧
      (vals σ (satC u)).getD (4 * u.length) false = (mrun σ u).curSat := by
  induction u with
  | nil => exact ⟨rfl, rfl⟩
  | cons b u ih =>
      obtain ⟨ihA, ihS⟩ := ih
      have hVlen : (vals σ (satC u)).length = 4 * u.length + 2 := by
        rw [vals_length, length_satC]
      have hphase : (mrun σ u).phase = (drun u).phase := by rw [mrun_eq]
      have hptr : (mrun σ u).ptr.headD false = σ.getD (drun u).ticks false := by
        rw [mrun_eq]
        exact headD_drop σ _
      have hidxA : 4 * (b :: u).length + 1 = (vals σ (satC u)).length + 3 := by
        rw [hVlen, List.length_cons]; omega
      have hidxS : 4 * (b :: u).length = (vals σ (satC u)).length + 2 := by
        rw [hVlen, List.length_cons]; omega
      have hgetA : (vals σ (satC u)).getD (4 * u.length + 1) false = (mrun σ u).allSat := ihA
      have hgetS : (vals σ (satC u)).getD (4 * u.length) false = (mrun σ u).curSat := ihS
      have e1 : ∀ l : List Bool,
          (vals σ (satC u) ++ l).getD (4 * u.length + 1) false = (mrun σ u).allSat := by
        intro l
        rw [getD_append_lt _ _ (by omega), hgetA]
      have e2 : ∀ l : List Bool,
          (vals σ (satC u) ++ l).getD (4 * u.length) false = (mrun σ u).curSat := by
        intro l
        rw [getD_append_lt _ _ (by omega), hgetS]
      have f0 : ∀ (v : Bool) (l : List Bool),
          (vals σ (satC u) ++ v :: l).getD (4 * u.length + 2) false = v := by
        intro v l
        rw [show 4 * u.length + 2 = (vals σ (satC u)).length + 0 from by omega,
          getD_append_add _ _ _]
        rfl
      have f1 : ∀ (v w : Bool) (l : List Bool),
          (vals σ (satC u) ++ v :: w :: l).getD (4 * u.length + 3) false = w := by
        intro v w l
        rw [show 4 * u.length + 3 = (vals σ (satC u)).length + 1 from by omega,
          getD_append_add _ _ _]
        rfl
      have g3 : ∀ v₀ v₁ v₂ v₃ : Bool,
          (vals σ (satC u) ++ [v₀, v₁, v₂, v₃]).getD ((vals σ (satC u)).length + 3) false = v₃ := by
        intro v₀ v₁ v₂ v₃
        rw [getD_append_add _ _ _]
        rfl
      have g2 : ∀ v₀ v₁ v₂ v₃ : Bool,
          (vals σ (satC u) ++ [v₀, v₁, v₂, v₃]).getD ((vals σ (satC u)).length + 2) false = v₂ := by
        intro v₀ v₁ v₂ v₃
        rw [getD_append_add _ _ _]
        rfl
      rw [satC_cons, hidxA, hidxS, mrun_cons]
      rcases h : (drun u).phase with _ | _ | _
      · cases b <;>
          · rw [satBlk_main u h, vals_block]
            simp only [mstep, hphase, h]
            exact ⟨by rw [g3]; simp only [gateVal, e1, Bool.or_self],
            by rw [g2]; simp only [gateVal, e2, Bool.or_self]⟩
      · cases b
        · rw [satBlk_esc_false u h, vals_block]
          simp only [mstep, hphase, h]
          exact ⟨by rw [g3]; simp only [gateVal, e1, Bool.or_self],
            by rw [g2]; simp only [gateVal, e2, Bool.or_self]⟩
        · rw [satBlk_esc_true u h, vals_block]
          simp only [mstep, hphase, h]
          refine ⟨by rw [g3]; simp only [gateVal, e1, Bool.or_self], ?_⟩
          rw [g2]
          simp only [gateVal, e2, f0, f1, hptr]
      · cases b
        · rw [satBlk_esc2_false u h, vals_block]
          simp only [mstep, hphase, h]
          refine ⟨by rw [g3]; simp only [gateVal, e1, e2], ?_⟩
          rw [g2]
          simp only [gateVal, f0, Bool.or_self]
        · rw [satBlk_esc2_true u h, vals_block]
          simp only [mstep, hphase, h]
          refine ⟨by rw [g3]; simp only [gateVal, e1, Bool.or_self], ?_⟩
          rw [g2]
          simp only [gateVal, e2, f0, f1, hptr, Bool.or_self]

/-! ### The output -/

theorem out_eq_getD (x : Word) {C : Circuit} (h : C ≠ []) :
    out x C = (vals x C).getD (C.length - 1) false := by
  cases C with
  | nil => exact absurd rfl h
  | cons g C =>
      rw [out, ← vals_cons_getD_length x g C]
      simp

/-- **The output of the circuit is the truth value of the decoded CNF.** -/
theorem out_satC (σ : Word) (u : Word) : out σ (satC u) = cnfVal σ (decode u) := by
  have hne : satC u ≠ [] := by
    intro hc
    have := congrArg List.length hc
    rw [length_satC] at this
    simp at this
  rw [out_eq_getD σ hne, length_satC,
    show 4 * u.length + 2 - 1 = 4 * u.length + 1 from by omega, (vals_satC σ u).1, mrun_eq]
  rfl

/-- **The circuit of a word is satisfiable exactly when the word is in `SAT`.** -/
theorem csat_satC_iff (u : Word) : csat (satC u) ↔ SAT u := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, by rw [← out_satC σ u]; exact hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, by rw [out_satC σ u]; exact hσ⟩

/-- The code of the circuit of a word is in `CIRCUIT-SAT` exactly when the word is in `SAT`: the
semantic half of the reduction `SAT ≤ₘᵖ CIRCUIT-SAT`. -/
theorem CSAT_encCirc_satC (u : Word) : CSAT (CircCode.encCirc (satC u)) ↔ SAT u := by
  rw [CSAT_encCirc_wf (wf_satC u), csat_satC_iff]

end Sat

end Complexity
