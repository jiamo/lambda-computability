# M22-SWITCHING-LEMMA — Håstad's switching lemma, by Razborov's counting argument

**Status:** DONE_STRONG

Module: `Start/SwitchingLemma.lean` (namespace `Complexity.Switching`), new in this delivery.
No existing module was edited except `Start.lean` and `Start/Capstones.lean` (import and `#check`
registration).  No `sorry`, no axiom; `#print axioms` reports `propext`, `Classical.choice`,
`Quot.sound` only (see `docs/goal/evidence/M29-EP-axioms.txt`, which lists all theorems of this
delivery).

## Definitions

```lean
abbrev Restriction (n : ℕ) := Fin n → Option Bool          -- none = free
abbrev Lit (n : ℕ) := Fin n × Bool                         -- (i, b) : the literal xᵢ = b
abbrev Term (n : ℕ) := List (Lit n)
abbrev DNF (n : ℕ) := List (Term n)
def freeSet (ρ : Restriction n) : Finset (Fin n)
def R (n ℓ : ℕ) : Finset (Restriction n)                   -- restrictions with exactly ℓ free variables
def IsKDNF (k : ℕ) (F : DNF n) : Prop                       -- terms of length ≤ k with distinct variables
inductive DTree (n : ℕ) | leaf (b : Bool) | node (i : Fin n) (t₀ t₁ : DTree n)
def Computes (T : DTree n) (F : DNF n) (ρ : Restriction n) : Prop   -- T = F on every extension of ρ
def cdt : DNF n → Restriction n → DTree n                   -- canonical decision tree
noncomputable def encode : DNF n → ℕ → Restriction n → Restriction n × List (ℕ × Bool × Bool)
def codes (k s : ℕ) : Finset (List (ℕ × Bool × Bool))      -- words of s letters (position < k, two bits)
noncomputable def Bad (F : DNF n) (ℓ s : ℕ) : Finset (Restriction n) :=
  (R n ℓ).filter (fun ρ => ¬ ∃ T : DTree n, T.depth < s ∧ Computes T F ρ)
```

## Results (exit criteria)

```lean
theorem cdt_computes (F : DNF n) (ρ : Restriction n) : Computes (cdt F ρ) F ρ
theorem encode_mem (hF : IsKDNF k F) (hρ : ρ ∈ R n ℓ) (hbad : s ≤ (cdt F ρ).depth) :
    s ≤ ℓ ∧ encode F s ρ ∈ R n (ℓ - s) ×ˢ codes k s
theorem encode_injOn (hF : IsKDNF k F) (s : ℕ) :
    Set.InjOn (encode F s) {ρ | s ≤ (cdt F ρ).depth}
theorem card_codes_le (k s : ℕ) : (codes k s).card ≤ (4 * k) ^ s
-- Exit criterion 1: restrictions are counted by an explicit injection (Razborov's encoding).
theorem card_bad_le (hF : IsKDNF k F) (ℓ s : ℕ) :
    (Bad F ℓ s).card ≤ (R n (ℓ - s)).card * (4 * k) ^ s
theorem card_R (n ℓ : ℕ) : (R n ℓ).card = n.choose ℓ * 2 ^ (n - ℓ)
-- Exit criterion 2: the bound (c p k)^s with p = ℓ / n and c = 16.
theorem switching_lemma (hF : IsKDNF k F) (ℓ s : ℕ) (hℓ : 2 * ℓ ≤ n) :
    ((Bad F ℓ s).card : ℚ) / (R n ℓ).card ≤ (16 * k * ℓ / n : ℚ) ^ s
```

## Proof outline

* `encode F s ρ`: walk down `F` to the first term `C` not falsified by `ρ`, with free literals
  `L`.  If `|L| ≥ s`, fix the first `s` of them to their *satisfying* values and stop.  Otherwise
  choose (`choosePath`) an extension `ρ'` on the variables of `L` that does not satisfy `C` and
  under which the canonical tree still has depth `≥ s - |L|`, recurse on `ρ'` with
  `s - |L|`, and in the result fix the variables of `L` to their satisfying values.  The code
  word of a block records, for each fixed variable, its position in `C` (`< k`), whether it is
  the last of the block, and its value on the path (`blockCode`).
* Decoding (`encode_inj_aux`): from the encoded restriction, the first term of `F` it does not
  falsify is `C` again (earlier terms are falsified by `ρ`, which the encoding refines, and `C` is
  satisfied), so the positions in the code identify the variables, and the bits give back the
  path's values; induction on `s`.
* Counting: `card_bad_le` is `card_le_card_of_injOn`; `card_R` counts restrictions by their free
  sets; `card_R_iter` gives `|R n (ℓ-s)| n^s ≤ |R n ℓ| (4ℓ)^s` for `2ℓ ≤ n`, whence the ratio bound.

No probability theory is used: the "fraction of bad restrictions" is a ratio of cardinalities of
finite sets.

## Used downstream

`Start/ParityNotAC0.lean` reuses `encode`, `encode_spec`, `encode_injOn`, `codes`, `card_R` and
`card_R_iter` to prove the relative version (refinements of a fixed restriction) needed for
`M22-PARITY-NOT-AC0`.
