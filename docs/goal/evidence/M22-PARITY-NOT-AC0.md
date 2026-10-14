# M22-PARITY-NOT-AC0 — Parity is not in AC0

**Status:** DONE_STRONG

Module: `Start/ParityNotAC0.lean` (namespaces `Complexity.Switching`, `Complexity.Parity`,
`Complexity`), new in this delivery; it imports `Start/SwitchingLemma.lean` and `Start/AC0.lean`.
No existing module was edited except `Start.lean` and `Start/Capstones.lean` (registration).
No `sorry`, no axiom; `#print axioms` reports `propext`, `Classical.choice`, `Quot.sound` only
(`docs/goal/evidence/M29-EP-axioms.txt`).

## Terminal statements

```lean
/-- Parity: the word has an odd number of ones. -/
def Complexity.Parity : Language := fun x => x.count true % 2 = 1

-- Exit criterion 1.
theorem Complexity.parity_not_AC0 : ¬ InAC0 Parity

-- Exit criterion 2 (quantitative form), for every circuit (NOT gates allowed):
theorem Complexity.parity_circuit_bound {C : ACCirc} {n d : ℕ} (hd : C.depth ≤ d) (h2 : 2 ≤ d)
    (hpar : ∀ x : Word, x.length = n → (Parity x ↔ C.eval x = true)) :
    n < (32 * (Nat.log2 C.size + 2)) ^ (d - 1)
theorem Complexity.parity_log_size_lower_bound ... :
    (n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 32 - 2 < Nat.log2 C.size
theorem Complexity.parity_size_lower_bound ... :
    (2 : ℝ) ^ ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ)⁻¹) / 32 - 2) < C.size
theorem Complexity.parity_depth_le_one {C : ACCirc} {n : ℕ} (hd : C.depth ≤ 1)
    (hpar : ...) : n ≤ 1
```

So a depth-`d` circuit for parity on `n` inputs has size `S > 2^(n^(1/(d-1))/32 - 2)`, i.e.
`S = 2^(Ω(n^(1/(d-1))))`, with explicit constants.

## Proof structure

1. **Relative switching lemma** (`Complexity.Switching`): `RR ρ₀ ℓ` = refinements of `ρ₀` with
   `ℓ` free variables; `card_RR : |RR ρ₀ ℓ| = |R m ℓ|` with `m = |freeSet ρ₀|`
   (counted by free sets, `card_fiber_rel`); Razborov's encoding maps bad refinements into
   `RR ρ₀ (ℓ-s) ×ˢ codes k s` (it refines its argument), so
   `switching_rel : |BadRel F ρ₀ ℓ s| · m^s ≤ |RR ρ₀ ℓ| · (16 k ℓ)^s` for `2ℓ ≤ m`, and with
   `ℓ = ⌊m/(32k)⌋`, `switching_rel_half : |BadRel| · 2^s ≤ |RR ρ₀ ℓ|`.
2. **Decision trees to DNFs** (`toDNF`, `eval_toDNF`, `isKDNF_toDNF`): the accepting paths of a
   tree of depth `t` (a variable already on the path is not queried again) form a well-formed
   `t`-DNF; `neg` flips leaves.  An OR of functions with depth-`t` trees is a `t`-DNF
   (`dnf_of_any`); an AND is the negation of one.
3. **Invariant** `Good C ρ j t`: every subcircuit (`subs C`, with `(subs C).length = C.size`) of
   depth `≤ j` has a decision tree of depth `≤ t` under `ρ`.  `good_zero`: literals and constants
   have depth-1 trees.
4. **One round** (`round`): if `Good C ρ j t`, `1 ≤ t ≤ s` and `C.size < 2^s`, then some
   refinement with `⌊m/(32t)⌋` free variables satisfies `Good C ρ' (j+1) s`: each gate of depth
   `j+1` is a `t`-DNF or a negated one, its bad refinements are at most a `2^-s` fraction, and
   there are fewer than `2^s` gates (union bound by cardinalities).
5. **Rounds** (`rounds`): first round with `t = 1`, then `t = s = log₂ S + 1`; after `r ≥ 1`
   rounds `⌊n/(32 (32 s)^(r-1))⌋` variables are free.
6. **End** (`final_bound`, `dnf_not_parity`): after `d-1` rounds the whole circuit is a `t`-DNF or
   a negated one; such a function cannot compute parity on more than `t` free variables (flip a
   free variable outside an accepting term).  Hence `n/(32(32s)^(d-2)) ≤ s`.
7. **Asymptotics** (`parity_not_AC0`): for `p n ≤ a (n+1)^k`, take `n = 2^N - 1`; then
   `log₂ p(n) < log₂ a + 1 + N k`, and `2^N - 1 < (c N)^(D-1)` for every `N ≥ 1` contradicts
   `exists_poly_lt_two_pow` (from `tendsto_pow_const_div_const_pow_of_one_lt`).

Circuits are the trees of `Start/AC0.lean`; NOT gates are removed with `ACCirc.nnf`, which keeps
depth and does not increase size.
