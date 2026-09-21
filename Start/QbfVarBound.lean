/-
**The variables of the reduction formula lie in a polynomial range.**

`Start/QbfMachine.lean` builds, for a machine running in space `s` on an input `x`, a closed
quantified Boolean formula `machineF M x s`, and `Start/QbfClosed.lean` tracks which variables its
pieces leave *free*.  Writing that formula down as a word needs more: a bound on *every* variable
index it mentions, bound ones included, because an index is what an encoding has to spell out.
This module supplies it.  Every piece of the construction speaks about blocks of `cfgWidth M x s`
variables, and the whole formula only ever mentions the blocks below `3 k + 5`, where `k` is the
depth of the midpoint recursion; so all its indices are below `(3 k + 5) * cfgWidth M x s`.

Main results:

* `Complexity.Qbf.QBF.varBound_conjAll_le`, `.varBound_disjAny_le`, `.varBound_allBits_le`,
  `.varBound_exBits_le` — the bound for the generic constructions;
* `Complexity.Qbf.QBF.varBound_eqBlock_le`, `.varBound_reachF_le` — the reachability formula uses
  only its endpoint blocks and the scratch blocks above them;
* `Complexity.Qbf.QBF.varBound_stepF_le`, `.varBound_initF_le`, `.varBound_accF_le` — the formulas
  of the machine use only the blocks they name;
* `Complexity.Qbf.QBF.varBound_machineF_le` — **every variable of the reduction formula is below
  `(3 * savitchDepth M x s + 5) * cfgWidth M x s`**.
-/

import Mathlib
import Start.QbfClosed

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

open Complexity.Space

variable {M : Machine} {x : List Bool} {s : ℕ}

/-! ### The generic constructions -/

@[simp] theorem varBound_tt : tt.varBound = 1 := by simp [tt, varBound]

@[simp] theorem varBound_ff : ff.varBound = 1 := by simp [ff, varBound]

theorem varBound_litF (i : ℕ) (b : Bool) : (litF i b).varBound = i + 1 := by
  cases b <;> simp [litF, varBound]

theorem varBound_litF_le {i N : ℕ} {b : Bool} (h : i < N) : (litF i b).varBound ≤ N := by
  rw [varBound_litF]; omega

theorem varBound_iffVar_le {i j N : ℕ} (hi : i < N) (hj : j < N) :
    (iffVar i j).varBound ≤ N := by
  simp only [iffVar, varBound]
  omega

theorem varBound_imp_le {p q : QBF} {N : ℕ} (hp : p.varBound ≤ N) (hq : q.varBound ≤ N) :
    (imp p q).varBound ≤ N := by
  simp only [imp, varBound]
  omega

theorem varBound_conjAll_le {N : ℕ} (hN : 1 ≤ N) : ∀ {ps : List QBF},
    (∀ p ∈ ps, p.varBound ≤ N) → (conjAll ps).varBound ≤ N
  | [], _ => by simpa [conjAll] using hN
  | p :: ps, h => by
      have h₁ : p.varBound ≤ N := h p (List.mem_cons_self ..)
      have h₂ := varBound_conjAll_le hN fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [conjAll, varBound]
      omega

theorem varBound_disjAny_le {N : ℕ} (hN : 1 ≤ N) : ∀ {ps : List QBF},
    (∀ p ∈ ps, p.varBound ≤ N) → (disjAny ps).varBound ≤ N
  | [], _ => by simpa [disjAny] using hN
  | p :: ps, h => by
      have h₁ : p.varBound ≤ N := h p (List.mem_cons_self ..)
      have h₂ := varBound_disjAny_le hN fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [disjAny, varBound]
      omega

theorem varBound_allBits_le : ∀ (n o : ℕ) {p : QBF} {N : ℕ}, o + n ≤ N → p.varBound ≤ N →
    (allBits o n p).varBound ≤ N
  | 0, o, _, _, _, hp => by simpa [allBits] using hp
  | n + 1, o, p, N, ho, hp => by
      have ih := varBound_allBits_le n (o + 1) (p := p) (N := N) (by omega) hp
      simp only [allBits, varBound]
      omega

theorem varBound_exBits_le : ∀ (n o : ℕ) {p : QBF} {N : ℕ}, o + n ≤ N → p.varBound ≤ N →
    (exBits o n p).varBound ≤ N
  | 0, o, _, _, _, hp => by simpa [exBits] using hp
  | n + 1, o, p, N, ho, hp => by
      have ih := varBound_exBits_le n (o + 1) (p := p) (N := N) (by omega) hp
      simp only [exBits, varBound]
      omega

/-! ### Blocks -/

theorem varBound_eqBlock_le {m i j N : ℕ} (hm : 0 < m) (hi : i < N) (hj : j < N) :
    (eqBlock m i j).varBound ≤ N * m := by
  have hone : 1 ≤ N * m := Nat.mul_pos (by omega) hm
  refine varBound_conjAll_le hone ?_
  intro p hp
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
  have hl' : l < m := List.mem_range.1 hl
  refine varBound_iffVar_le ?_ ?_
  · calc i * m + l < i * m + m := by omega
      _ = (i + 1) * m := by ring
      _ ≤ N * m := Nat.mul_le_mul_right _ (by omega)
  · calc j * m + l < j * m + m := by omega
      _ = (j + 1) * m := by ring
      _ ≤ N * m := Nat.mul_le_mul_right _ (by omega)

theorem block_index_lt {m a l N : ℕ} (ha : a < N) (hl : l < m) : a * m + l < N * m := by
  calc a * m + l < a * m + m := by omega
    _ = (a + 1) * m := by ring
    _ ≤ N * m := Nat.mul_le_mul_right _ (by omega)

/-! ### The formulas of the machine -/

theorem varBound_cfgF_le {a q i j N : ℕ} (h : a < N) :
    (cfgF M x s a q i j).varBound ≤ N * cfgWidth M x s := by
  have hm := cfgWidth_pos M x s
  have hone : 1 ≤ N * cfgWidth M x s := Nat.mul_pos (by omega) hm
  refine varBound_conjAll_le hone ?_
  intro p hp
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
  have hl' : l < cfgWidth M x s := List.mem_range.1 hl
  have hidx : a * cfgWidth M x s + l < N * cfgWidth M x s := block_index_lt h hl'
  by_cases h1 : l < M.states
  · simpa [h1] using varBound_litF_le (b := decide (l = q)) hidx
  · by_cases h2 : l < M.states + (x.length + 1)
    · simpa [h1, h2] using varBound_litF_le (b := decide (l - M.states = i)) hidx
    · by_cases h3 : l < M.states + (x.length + 1) + s
      · simpa [h1, h2, h3] using hone
      · simpa [h1, h2, h3] using
          varBound_litF_le (b := decide (l - (M.states + (x.length + 1) + s) = j)) hidx

theorem varBound_tgtF_le {a b q' i' j' : ℕ} {w : Bool} {j N : ℕ} (ha : a < N) (hb : b < N) :
    (tgtF M x s a b q' i' j' w j).varBound ≤ N * cfgWidth M x s := by
  have hm := cfgWidth_pos M x s
  have hone : 1 ≤ N * cfgWidth M x s := Nat.mul_pos (by omega) hm
  refine varBound_conjAll_le hone ?_
  intro p hp
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
  have hl' : l < cfgWidth M x s := List.mem_range.1 hl
  have hidxa : a * cfgWidth M x s + l < N * cfgWidth M x s := block_index_lt ha hl'
  have hidxb : b * cfgWidth M x s + l < N * cfgWidth M x s := block_index_lt hb hl'
  by_cases h1 : l < M.states
  · simpa [h1] using varBound_litF_le (b := decide (l = q')) hidxb
  · by_cases h2 : l < M.states + (x.length + 1)
    · simpa [h1, h2] using varBound_litF_le (b := decide (l - M.states = i')) hidxb
    · by_cases h3 : l < M.states + (x.length + 1) + s
      · by_cases h4 : l - (M.states + (x.length + 1)) = j
        · simpa [h1, h2, h3, h4] using varBound_litF_le (b := w) hidxb
        · simpa [h1, h2, h3, h4] using varBound_iffVar_le hidxb hidxa
      · simpa [h1, h2, h3] using
          varBound_litF_le (b := decide (l - (M.states + (x.length + 1) + s) = j')) hidxb

theorem varBound_stepCase_le {a b q i j : ℕ} {bit : Bool} {t : ℕ × Bool × Dir × Dir} {N : ℕ}
    (ha : a < N) (hb : b < N) (hj : j < s) :
    (stepCase M x s a b q i j bit t).varBound ≤ N * cfgWidth M x s := by
  have hcfg : (cfgF M x s a q i j).varBound ≤ N * cfgWidth M x s := varBound_cfgF_le ha
  have hlit : (litF (a * cfgWidth M x s + (M.states + (x.length + 1) + j)) bit).varBound
      ≤ N * cfgWidth M x s := by
    refine varBound_litF_le (block_index_lt ha ?_)
    simp only [cfgWidth]
    omega
  have htgt : (tgtF M x s a b t.1 (moveIn x.length i t.2.2.1) (moveWork j t.2.2.2) t.2.1 j).varBound
      ≤ N * cfgWidth M x s := varBound_tgtF_le ha hb
  simp only [stepCase, varBound]
  omega

theorem varBound_stepF_le {a b N : ℕ} (ha : a < N) (hb : b < N) :
    (stepF M x s a b).varBound ≤ N * cfgWidth M x s := by
  have hm := cfgWidth_pos M x s
  have hone : 1 ≤ N * cfgWidth M x s := Nat.mul_pos (by omega) hm
  refine varBound_disjAny_le hone ?_
  intro p hp
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hp
  obtain ⟨q, i, j, bit, t⟩ := z
  obtain ⟨-, -, hj, -⟩ := mem_caseList.1 hz
  exact varBound_stepCase_le ha hb hj

theorem varBound_initF_le {a N : ℕ} (ha : a < N) :
    (initF M x s a).varBound ≤ N * cfgWidth M x s := by
  have hm := cfgWidth_pos M x s
  have hone : 1 ≤ N * cfgWidth M x s := Nat.mul_pos (by omega) hm
  have hcfg : (cfgF M x s a 0 0 0).varBound ≤ N * cfgWidth M x s := varBound_cfgF_le ha
  have hrest : (conjAll ((List.range s).map fun l =>
      litF (a * cfgWidth M x s + (M.states + (x.length + 1) + l)) false)).varBound
        ≤ N * cfgWidth M x s := by
    refine varBound_conjAll_le hone ?_
    intro p hp
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hp
    have hl' : l < s := List.mem_range.1 hl
    refine varBound_litF_le (block_index_lt ha ?_)
    simp only [cfgWidth]
    omega
  simp only [initF, varBound]
  omega

theorem varBound_accF_le {b N : ℕ} (hb : b < N) :
    (accF M x s b).varBound ≤ N * cfgWidth M x s := by
  have hm := cfgWidth_pos M x s
  have hone : 1 ≤ N * cfgWidth M x s := Nat.mul_pos (by omega) hm
  refine varBound_disjAny_le hone ?_
  intro p hp
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hp
  exact varBound_cfgF_le hb

/-! ### The reachability formula -/

/-- The reachability formula mentions its two endpoint blocks and the scratch blocks
`t, …, t + 3 k + 2`, so all its variables lie below `N * m` as soon as those blocks do. -/
theorem varBound_reachF_le {stepF' : ℕ → ℕ → QBF} {m : ℕ} (hm : 0 < m)
    (hstep : ∀ (u v N : ℕ), u < N → v < N → (stepF' u v).varBound ≤ N * m) :
    ∀ (k a b t N : ℕ), a < N → b < N → t + 3 * k + 3 ≤ N →
      (reachF stepF' m k a b t).varBound ≤ N * m := by
  intro k
  induction k with
  | zero =>
      intro a b t N ha hb _
      rw [reachF_zero]
      have h₁ : (eqBlock m a b).varBound ≤ N * m := varBound_eqBlock_le hm ha hb
      have h₂ : (stepF' a b).varBound ≤ N * m := hstep a b N ha hb
      simp only [varBound]
      omega
  | succ k ih =>
      intro a b t N ha hb ht
      rw [reachF_succ]
      have hrec : (reachF stepF' m k (t + 1) (t + 2) (t + 3)).varBound ≤ N * m :=
        ih (t + 1) (t + 2) (t + 3) N (by omega) (by omega) (by omega)
      have hq1 : (eqBlock m (t + 1) a).varBound ≤ N * m :=
        varBound_eqBlock_le hm (by omega) ha
      have hq2 : (eqBlock m (t + 2) t).varBound ≤ N * m :=
        varBound_eqBlock_le hm (by omega) (by omega)
      have hq3 : (eqBlock m (t + 1) t).varBound ≤ N * m :=
        varBound_eqBlock_le hm (by omega) (by omega)
      have hq4 : (eqBlock m (t + 2) b).varBound ≤ N * m :=
        varBound_eqBlock_le hm (by omega) hb
      have hguard : (QBF.disj (QBF.conj (eqBlock m (t + 1) a) (eqBlock m (t + 2) t))
            (QBF.conj (eqBlock m (t + 1) t) (eqBlock m (t + 2) b))).varBound ≤ N * m := by
        simp only [varBound]
        omega
      have hbody := varBound_imp_le hguard hrec
      have hle : ∀ c : ℕ, t + c + 1 ≤ N → (t + c) * m + m ≤ N * m := by
        intro c hc
        calc (t + c) * m + m = (t + c + 1) * m := by ring
          _ ≤ N * m := Nat.mul_le_mul_right _ (by omega)
      refine varBound_exBits_le m (t * m) ?_ (varBound_allBits_le m ((t + 1) * m) ?_
        (varBound_allBits_le m ((t + 2) * m) ?_ hbody))
      · have := hle 0 (by omega)
        simpa using this
      · exact hle 1 (by omega)
      · exact hle 2 (by omega)

/-! ### The whole formula -/

/-- **Every variable of the reduction formula is below `(3 k + 5) * cfgWidth M x s`**, where
`k = savitchDepth M x s` is the depth of the midpoint recursion. -/
theorem varBound_machineF_le (M : Machine) (x : List Bool) (s : ℕ) :
    (machineF M x s).varBound
      ≤ (3 * savitchDepth M x s + 5) * cfgWidth M x s := by
  have hm : 0 < cfgWidth M x s := cfgWidth_pos M x s
  have hreach := varBound_reachF_le (stepF' := stepF M x s) (m := cfgWidth M x s) hm
    (fun u v N' hu hv => varBound_stepF_le hu hv) (savitchDepth M x s) 0 1 2
    (3 * savitchDepth M x s + 5) (by omega) (by omega) (by omega)
  have hinit := varBound_initF_le (M := M) (x := x) (s := s) (a := 0)
    (N := 3 * savitchDepth M x s + 5) (by omega)
  have hacc := varBound_accF_le (M := M) (x := x) (s := s) (b := 1)
    (N := 3 * savitchDepth M x s + 5) (by omega)
  have hbody : (QBF.conj (QBF.conj (initF M x s 0) (accF M x s 1))
      (reachF (stepF M x s) (cfgWidth M x s) (savitchDepth M x s) 0 1 2)).varBound
        ≤ (3 * savitchDepth M x s + 5) * cfgWidth M x s := by
    simp only [varBound]
    omega
  rw [machineF]
  refine varBound_exBits_le (cfgWidth M x s) 0 ?_
    (varBound_exBits_le (cfgWidth M x s) (cfgWidth M x s) ?_ hbody)
  · calc 0 + cfgWidth M x s = 1 * cfgWidth M x s := by ring
      _ ≤ (3 * savitchDepth M x s + 5) * cfgWidth M x s :=
        Nat.mul_le_mul_right _ (by omega)
  · calc cfgWidth M x s + cfgWidth M x s = 2 * cfgWidth M x s := by ring
      _ ≤ (3 * savitchDepth M x s + 5) * cfgWidth M x s :=
        Nat.mul_le_mul_right _ (by omega)

end QBF

end Complexity.Qbf
