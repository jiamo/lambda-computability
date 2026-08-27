/-
**Polynomial-time computation by polynomial-size circuits.**

`Start/CobhamBRec.lean` compiles every Cobham term into a Boolean circuit of polynomial size, the
arguments arriving as word signals.  This module feeds the two kinds of argument that matter into
that compiler — a *constant* word (the instance) and the word *read off the circuit input* (the
witness) — and reads the answer off the presence wire of the output signal.

The two consequences are:

* every polynomial-time predicate on words of length at most `N` is computed by a circuit of size
  polynomial in `N` (that is, `P ⊆ P/poly`);
* for every Cobham verifier `v` and every instance `x`, there is a well-formed circuit of size
  polynomial in `|x|` which is satisfiable exactly when `v` accepts some short witness for `x`.

The second statement is the non-uniform half of the compilation step of the Cook–Levin theorem
(`Complexity.CircuitCompilable` in `Start/CookLevin.lean`); what it does *not* provide is
uniformity, i.e. that the description of the circuit — or of its Tseitin translation — is itself
produced from `x` by a Cobham term.

Main results:

* `Complexity.Tseitin.exists_acceptCircuit` — the circuit deciding acceptance of a fixed instance
  together with the witness read off the circuit input;
* `Complexity.Tseitin.exists_decideCircuit` — **`P ⊆ P/poly`**;
* `Complexity.Tseitin.exists_witnessCircuit` — the satisfiability version;
* `Complexity.Tseitin.exists_npCircuitFamily` — for every language in `NP`, a polynomial-size
  circuit family satisfiable exactly on the language.
-/

import Start.CobhamBRec

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Putting a wire on top of a circuit -/

/-- Turning a wire into the output of a circuit. -/
theorem exists_outCircuit {C : Circuit} (hC : wf C) {w : ℕ} {f : Word → Bool}
    (hw : Holds C w f) :
    ∃ C' : Circuit, Ext C C' ∧ wf C' ∧ C'.length = C.length + 1 ∧ ∀ x, out x C' = f x := by
  refine ⟨Gate.conj w w :: C, Ext.cons _ _, ⟨⟨hw.1, hw.1⟩, hC⟩, by simp, fun x => ?_⟩
  rw [out]
  simp only [gateVal]
  rw [show (vals x C).getD w false = wval C w x from rfl, hw.2 x, Bool.and_self]

theorem csat_iff_exists {C : Circuit} {f : Word → Bool} (h : ∀ x, out x C = f x) :
    csat C ↔ ∃ x, f x = true :=
  exists_congr fun x => by rw [h x]

/-! ### Deciding a Cobham verifier on a fixed instance -/

/-- **The acceptance wire.**  For a Cobham term `v`, a fixed word `x₀` and a bound `N`, there is a
well-formed circuit of size polynomial in `max |x₀| N` with a wire that is true exactly when `v`
accepts the pair consisting of `x₀` and the word of length at most `N` read off the circuit
input. -/
theorem exists_acceptWire (v : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ (x₀ : Word) (N : ℕ),
      ∃ (C : Circuit) (w : ℕ), wf C ∧
        Holds C w (fun x => decide (v.eval [x₀, inWord N x] ≠ [])) ∧
        C.length ≤ sz (max x₀.length N) := by
  obtain ⟨bdv, hbdv, hvc⟩ := cobCompiles v
  obtain ⟨av, kv, hav⟩ := Cob.polyLen v
  refine ⟨fun m => 3 + 2 * m + m * (m + 2) + m + bdv (m + av * (m + 1) ^ kv + 1), ?_, ?_⟩
  · exact ((((MonoPoly.const 3).add ((MonoPoly.const 2).mul MonoPoly.id')).add
      (MonoPoly.id'.mul (MonoPoly.id'.add (MonoPoly.const 2)))).add MonoPoly.id').add
      (hbdv.comp ((MonoPoly.id'.add (MonoPoly.std av kv)).add (MonoPoly.const 1)))
  intro x₀ N
  obtain ⟨m, hmdef⟩ : ∃ m, m = max x₀.length N := ⟨_, rfl⟩
  have hxm : x₀.length ≤ m := by rw [hmdef]; exact le_max_left _ _
  have hNm : N ≤ m := by rw [hmdef]; exact le_max_right _ _
  rw [← hmdef]
  have hwfnil : wf ([] : Circuit) := trivial
  obtain ⟨C₁, ps₀, bs₀, e₁, w₁, l₁, hc₀⟩ := exists_constSig [] hwfnil x₀ m hxm
  obtain ⟨C₂, psw, bsw, e₂, w₂, l₂, hcw⟩ := exists_inputSig C₁ w₁ N
  have hbase : ArgSig C₂ m 0 (fun _ => ([], [])) (fun _ _ => []) :=
    ⟨fun _ _ _ => rfl, fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩
  have hA := (hbase.cons hcw hNm).cons (hc₀.mono e₂) le_rfl
  have hargs : ∀ x, argsOf
      (consFun (fun _ : Word => x₀) (consFun (inWord N) (fun _ _ => []))) (0 + 1 + 1) x
      = [x₀, inWord N x] := by
    intro x
    rw [argsOf_consFun, argsOf_consFun]
    simp [argsOf]
  have hbnd : ∀ x, (v.eval (argsOf
      (consFun (fun _ : Word => x₀) (consFun (inWord N) (fun _ _ => []))) (0 + 1 + 1) x)).length
      ≤ av * (m + 1) ^ kv + 1 := by
    intro x
    have h₁ := hav (argsOf
      (consFun (fun _ : Word => x₀) (consFun (inWord N) (fun _ _ => []))) (0 + 1 + 1) x)
    have h₂ : maxLen (argsOf
        (consFun (fun _ : Word => x₀) (consFun (inWord N) (fun _ _ => []))) (0 + 1 + 1) x)
        ≤ m := hA.maxLen_le x
    have h₃ : av * (maxLen (argsOf
        (consFun (fun _ : Word => x₀) (consFun (inWord N) (fun _ _ => []))) (0 + 1 + 1) x) + 1) ^ kv
        ≤ av * (m + 1) ^ kv :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    omega
  obtain ⟨C₃, ps, bs, e₃, w₃, hh, l₃⟩ :=
    hvc (m + av * (m + 1) ^ kv + 1) (0 + 1 + 1) (av * (m + 1) ^ kv + 1) C₂ _ _ w₂
      (hA.widen (by omega)) (by omega) hbnd
  refine ⟨C₃, ps.getD 0 0, w₃, (hh.pres 0 (by omega)).congr fun x => ?_, ?_⟩
  · rw [hargs x]
    simp [List.length_pos_iff]
  · change C₃.length ≤ 3 + 2 * m + m * (m + 2) + m + bdv (m + av * (m + 1) ^ kv + 1)
    have hsq : N * (N + 2) ≤ m * (m + 2) := Nat.mul_le_mul hNm (by omega)
    have hnil : ([] : Circuit).length = 0 := rfl
    omega

/-- **The acceptance circuit**: the same statement with the answer on the output gate. -/
theorem exists_acceptCircuit (v : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ (x₀ : Word) (N : ℕ),
      ∃ C : Circuit, wf C ∧ C.length ≤ sz (max x₀.length N) ∧
        ∀ x, out x C = decide (v.eval [x₀, inWord N x] ≠ []) := by
  obtain ⟨sz, hsz, hw⟩ := exists_acceptWire v
  refine ⟨fun n => sz n + 1, hsz.add (MonoPoly.const 1), fun x₀ N => ?_⟩
  obtain ⟨C, w, hC, hh, hl⟩ := hw x₀ N
  obtain ⟨C', _, hwf', hlen', hout⟩ := exists_outCircuit hC hh
  exact ⟨C', hwf', by change C'.length ≤ sz (max x₀.length N) + 1; omega, hout⟩

/-! ### `P ⊆ P/poly` -/

/-- **Every polynomial-time predicate is computed by circuits of polynomial size.**  The circuit
for the bound `N` decides, on input `x`, whether the Cobham term `c` accepts the word of length at
most `N` read off `x`; by `Complexity.Tseitin.exists_inWord` every word of length at most `N` is
read off some circuit input. -/
theorem exists_decideCircuit (c : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ N : ℕ, ∃ C : Circuit, wf C ∧ C.length ≤ sz N ∧
      ∀ x : Word, out x C = decide (c.eval [inWord N x] ≠ []) := by
  obtain ⟨sz, hsz, hC⟩ := exists_acceptCircuit (.comp c [.proj 1])
  refine ⟨sz, hsz, fun N => ?_⟩
  obtain ⟨C, hwf, hlen, hout⟩ := hC [] N
  refine ⟨C, hwf, by simpa using hlen, fun x => ?_⟩
  rw [hout x]
  congr 2
  simp

/-- The same statement for a language in `P`. -/
theorem exists_decideCircuit_of_inP {L : Language} (h : InP L) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ N : ℕ, ∃ C : Circuit, wf C ∧ C.length ≤ sz N ∧
      ∀ x : Word, (out x C = true ↔ L (inWord N x)) := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨sz, hsz, hC⟩ := exists_decideCircuit c
  refine ⟨sz, hsz, fun N => ?_⟩
  obtain ⟨C, hwf, hlen, hout⟩ := hC N
  refine ⟨C, hwf, hlen, fun x => ?_⟩
  rw [hout x, hc (inWord N x)]
  simp

/-! ### The satisfiability version -/

/-- **The witness circuit**: a well-formed circuit of size polynomial in `max |x₀| N`, satisfiable
exactly when the Cobham verifier `v` accepts some witness of length at most `N` for `x₀`. -/
theorem exists_witnessCircuit (v : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ (x₀ : Word) (N : ℕ), ∃ C : Circuit, wf C ∧
      C.length ≤ sz (max x₀.length N) ∧
      (csat C ↔ ∃ u : Word, u.length ≤ N ∧ v.eval [x₀, u] ≠ []) := by
  obtain ⟨sz, hsz, hC⟩ := exists_acceptCircuit v
  refine ⟨sz, hsz, fun x₀ N => ?_⟩
  obtain ⟨C, hwf, hlen, hout⟩ := hC x₀ N
  refine ⟨C, hwf, hlen, ?_⟩
  rw [csat_iff_exists hout]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨inWord N x, length_inWord_le N x, by simpa using hx⟩
  · rintro ⟨u, hu, hne⟩
    obtain ⟨x, hx⟩ := exists_inWord N u hu
    exact ⟨x, by rw [hx]; simpa using hne⟩

/-- **For every language in `NP`, a polynomial-size circuit family satisfiable exactly on the
language.**  This is the non-uniform half of the compilation step of the Cook–Levin theorem: the
circuits exist and are small, but nothing here says that their descriptions are produced from the
instance by a polynomial-time function. -/
theorem exists_npCircuitFamily {L : Language} (h : InNP L) :
    ∃ (cc : Word → Circuit) (sz : ℕ → ℕ), MonoPoly sz ∧ (∀ x, wf (cc x)) ∧
      (∀ x, (cc x).length ≤ sz x.length) ∧ (∀ x, csat (cc x) ↔ L x) := by
  obtain ⟨v, p, hpb, hpm, hwit, hacc⟩ := h
  obtain ⟨sz, hsz, hC⟩ := exists_witnessCircuit v
  choose cc hwf hlen hcsat using fun x : Word => hC x (p x.length)
  refine ⟨cc, fun n => sz (n + p n), hsz.comp (MonoPoly.id'.add ⟨hpm, hpb⟩), hwf,
    fun x => ?_, fun x => ?_⟩
  · exact le_trans (hlen x) (hsz.mono (by simp))
  · rw [hcsat x, hacc x]
    constructor
    · rintro ⟨u, -, hne⟩
      exact ⟨u, hne⟩
    · rintro ⟨w, hne⟩
      exact ⟨w, hwit x w hne, hne⟩

end Tseitin

end Complexity
