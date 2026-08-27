/-
**A circuit for a verifier that reads the instance off its own input.**

`Start/PolyCircuit.lean` builds, for a fixed instance `x₀`, a circuit deciding whether a Cobham
verifier accepts `x₀` together with the witness read off the circuit input.  That circuit depends
on the instance, so a family of them is not obviously uniform.

Here the instance is read off the circuit input as well: the positions `[0, 2 * n)` carry the
instance and the positions `[2 * n, 2 * n + 2 * N)` the witness.  The resulting circuit depends
only on the two *lengths* `n` and `N`.  Fixing the instance is then done outside the circuit, by
the unit clauses of `Start/PinnedCnf.lean`.

Main results:

* `Complexity.Tseitin.exists_pinAcceptWire`, `Complexity.Tseitin.exists_pinAcceptCircuit` — the
  length-indexed acceptance circuit.
-/

import Start.PolyCircuit
import Start.InputSegment

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-- **The acceptance wire of the length-indexed circuit.**  For a Cobham term `v` and two lengths
`n`, `N`, there is a well-formed circuit of size polynomial in `max n N` with a wire that is true
exactly when `v` accepts the pair consisting of the word read off the input positions `[0, 2 * n)`
and the word read off the input positions `[2 * n, 2 * n + 2 * N)`. -/
theorem exists_pinAcceptWire (v : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ (n N : ℕ),
      ∃ (C : Circuit) (w : ℕ), wf C ∧
        Holds C w (fun x => decide (v.eval [inWord n x, inWordAt (2 * n) N x] ≠ [])) ∧
        C.length ≤ sz (max n N) := by
  obtain ⟨bdv, hbdv, hvc⟩ := cobCompiles v
  obtain ⟨av, kv, hav⟩ := Cob.polyLen v
  refine ⟨fun m => 2 * m + m * (m + 2) + m + (2 * m + m * (m + 2) + m) +
    bdv (m + av * (m + 1) ^ kv + 1), ?_, ?_⟩
  · have hA : MonoPoly (fun m => 2 * m + m * (m + 2) + m) :=
      (((MonoPoly.const 2).mul MonoPoly.id').add
        (MonoPoly.id'.mul (MonoPoly.id'.add (MonoPoly.const 2)))).add MonoPoly.id'
    exact (hA.add hA).add
      (hbdv.comp ((MonoPoly.id'.add (MonoPoly.std av kv)).add (MonoPoly.const 1)))
  intro n N
  obtain ⟨m, hmdef⟩ : ∃ m, m = max n N := ⟨_, rfl⟩
  have hxm : n ≤ m := by rw [hmdef]; exact le_max_left _ _
  have hNm : N ≤ m := by rw [hmdef]; exact le_max_right _ _
  rw [← hmdef]
  have hwfnil : wf ([] : Circuit) := trivial
  obtain ⟨C₁, ps₀, bs₀, e₁, w₁, l₁, hc₀⟩ := exists_inputSigAt [] hwfnil 0 n
  obtain ⟨C₂, psw, bsw, e₂, w₂, l₂, hcw⟩ := exists_inputSigAt C₁ w₁ (2 * n) N
  have hc₀' : WHolds C₂ n ps₀ bs₀ (inWord n) :=
    ((hc₀.mono e₂).congr fun x => inWordAt_zero n x)
  have hbase : ArgSig C₂ m 0 (fun _ => ([], [])) (fun _ _ => []) :=
    ⟨fun _ _ _ => rfl, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
  have hA := (hbase.cons hcw hNm).cons hc₀' hxm
  have hargs : ∀ x, argsOf
      (consFun (inWord n) (consFun (inWordAt (2 * n) N) (fun _ _ => []))) (0 + 1 + 1) x
      = [inWord n x, inWordAt (2 * n) N x] := by
    intro x
    rw [argsOf_consFun, argsOf_consFun]
    simp [argsOf]
  have hbnd : ∀ x, (v.eval (argsOf
      (consFun (inWord n) (consFun (inWordAt (2 * n) N) (fun _ _ => []))) (0 + 1 + 1) x)).length
      ≤ av * (m + 1) ^ kv + 1 := by
    intro x
    have h₁ := hav (argsOf
      (consFun (inWord n) (consFun (inWordAt (2 * n) N) (fun _ _ => []))) (0 + 1 + 1) x)
    have h₂ : maxLen (argsOf
        (consFun (inWord n) (consFun (inWordAt (2 * n) N) (fun _ _ => []))) (0 + 1 + 1) x)
        ≤ m := hA.maxLen_le x
    have h₃ : av * (maxLen (argsOf
        (consFun (inWord n) (consFun (inWordAt (2 * n) N) (fun _ _ => []))) (0 + 1 + 1) x) + 1) ^ kv
        ≤ av * (m + 1) ^ kv :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  obtain ⟨C₃, ps, bs, e₃, w₃, hh, l₃⟩ :=
    hvc (m + av * (m + 1) ^ kv + 1) (0 + 1 + 1) (av * (m + 1) ^ kv + 1) C₂ _ _ w₂
      (hA.widen (by omega)) (by omega) hbnd
  refine ⟨C₃, ps.getD 0 0, w₃, (hh.pres 0 (by omega)).congr fun x => ?_, ?_⟩
  · rw [hargs x]
    simp [List.length_pos_iff]
  · change C₃.length ≤ 2 * m + m * (m + 2) + m + (2 * m + m * (m + 2) + m) +
      bdv (m + av * (m + 1) ^ kv + 1)
    have hsq₁ : n * (n + 2) ≤ m * (m + 2) := Nat.mul_le_mul hxm (by omega)
    have hsq₂ : N * (N + 2) ≤ m * (m + 2) := Nat.mul_le_mul hNm (by omega)
    have hnil : ([] : Circuit).length = 0 := rfl
    omega

/-- **The length-indexed acceptance circuit**: the same statement with the answer on the output
gate.  The circuit depends on the two lengths only. -/
theorem exists_pinAcceptCircuit (v : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ (n N : ℕ),
      ∃ C : Circuit, wf C ∧ C.length ≤ sz (max n N) ∧
        ∀ x, out x C = decide (v.eval [inWord n x, inWordAt (2 * n) N x] ≠ []) := by
  obtain ⟨sz, hsz, hw⟩ := exists_pinAcceptWire v
  refine ⟨fun n => sz n + 1, hsz.add (MonoPoly.const 1), fun n N => ?_⟩
  obtain ⟨C, w, hC, hh, hl⟩ := hw n N
  obtain ⟨C', _, hwf', hlen', hout⟩ := exists_outCircuit hC hh
  exact ⟨C', hwf', by change C'.length ≤ sz (max n N) + 1; omega, hout⟩

end Tseitin

end Complexity
