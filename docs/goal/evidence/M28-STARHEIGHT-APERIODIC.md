# M28-STARHEIGHT-APERIODIC: Schützenberger's theorem (aperiodic ⇒ star-free)

Row: M28-STARHEIGHT-APERIODIC (DONE_STRONG).  Module: `Start/StarHeightAperiodic.lean`
(imports only `Start.StarHeightHeight`).  "Star-free" is `HasHeightAtMost _ 0`.

Gates: `lake build --wfail` (10645 jobs, no warnings), no `sorry`, no `native_decide`, no
`Lean.ofReduceBool`, no new axioms.  Axioms: `docs/goal/evidence/M28-STARHEIGHT-Z4-PM1-axioms.txt`
(all `[propext, Classical.choice, Quot.sound]`).

## Statements

```
theorem starFree_of_aperiodic {A : Type u} [Finite A] {M : Type u} [Monoid M] [Finite M]
    (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (φ : FreeMonoid A →* M) (m : M) :
    HasHeightAtMost {w : List A | φ (FreeMonoid.ofList w) = m} 0

def certOK [DecidableEq Q] (qs : List Q) (letters : List A) (δ : Q → A → Q) (R : List (Q → Q)) (N : ℕ) : Bool :=
  (R.any (tEq qs id) && R.all (fun f => letters.all fun a => R.any (tEq qs (tStep δ f a)))) &&
    R.all (fun f => tEq qs (f^[N + 1]) (f^[N]))

theorem starFree_of_dfa_closed [DecidableEq Q] (qs : List Q) (q₀ : Q) (hq₀ : q₀ ∈ qs)
    (letters : List A) (hl : ∀ a, a ∈ letters) (δ : Q → A → Q)
    (hcl : ∀ q ∈ qs, ∀ a, δ q a ∈ qs) (R : List (Q → Q)) (N : ℕ)
    (hR : certOK qs letters δ R N = true) (P : Q → Prop) :
    HasHeightAtMost {w : List A | P (w.foldl δ q₀)} 0

theorem starFree_of_dfa [DecidableEq Q] (qs : List Q) (hqs : ∀ q, q ∈ qs) (letters : List A)
    (hl : ∀ a, a ∈ letters) (δ : Q → A → Q) (R : List (Q → Q)) (N : ℕ)
    (hR : certOK qs letters δ R N = true) (q₀ : Q) (P : Q → Prop) :
    HasHeightAtMost {w : List A | P (w.foldl δ q₀)} 0
```

(all in namespace `GeneralizedStarHeight.Aperiodic`).  `tEq qs f g` compares on `qs`;
`tStep δ f a = fun q => δ (f q) a` (right composition with a letter).  `dfaCert qs letters δ fuel`
computes `R` by breadth-first closure from `id`, so an application is
`starFree_of_dfa _ List.mem_finRange _ hl _ _ _ (by decide +kernel) q₀ P` with
`R := dfaCert (List.finRange k) letters δ 100`.

## Proof (local divisors, Diekert–Kufleitner)

`fibL φ S m` = words over the letters `S` with value `m`.  `fibL_starFree_aux`: strong induction
on `Nat.card M`, inside on the finite set `S` of letters (`Finset.strongInduction`).

1. If `φ a = 1` for every `a ∈ S`: `fibL φ S 1 = overL S` (star-free, `overL_starFree`: the
   complement of `⊤ · (letters outside S) · ⊤`), other fibers empty (`fibL_trivial`).
2. Otherwise `S = insert c B`, `φ c ≠ 1`.  Words without `c` are handled by the inner induction.
   Words with `c` factor uniquely as `u₀ c u₁ c ⋯ c u_k`, `uᵢ ∈ B∗` (`decompose`, `cflat_inj`):
   `fibL_insert_eq` writes `fibL φ (insert c B) m` as `fibL φ B m` plus the union over
   `DIdx c m = {(p, n, q) | p · n · q = m}` of `fibL φ B p · {c} · subst φ B c (ψ⁻¹ n) · fibL φ B q`.
3. `LocalDiv c = {x | x ∈ M c ∩ c M}` with `(x c) ∘ (c y) = x c y`, identity `c`
   (`mul_val_of_left`, `mul_val_of_right`: well defined).  `LocalDiv.aperiodic`;
   `LocalDiv.one_not_mem` (if `1 = p c = c q` then `c` is a unit, hence `1` by aperiodicity) and
   `LocalDiv.card_lt`.
4. `psi c : FreeMonoid M →* LocalDiv c`, `t ↦ c t c` (`psi_val`).  The fibers of `psi` are
   star-free over the alphabet `M` by the outer induction.
5. `subst φ B c K = {cflat c us | us ∈ (B∗)^*, (φ uᵢ)ᵢ ∈ K}` (`cflat us = u₁ c ⋯ u_r c`).
   `subst_zero/one/letter/add/mul/compl/top` (prefix code `B∗c`, disjoint fibers;
   `subst (Kᶜ) = subst ⊤ ∖ subst K`, `subst ⊤ = ε ∪ (insert c B)∗ c`), and `subst_starFree` by induction on
   the star-free expression.

## Use (M28-STARHEIGHT-Z4-PM1)

Each automaton is one kernel `decide`:

| check | automaton | file |
|---|---|---|
| `walk_cert_m`, `walk_cert_a` | 6-state walk on `ZMod 4` (σm, σa) | `Start/StarHeightZ4Walk.lean` |
| `cPlus_cert`, `cMinus_cert` | 6-state DFAs of `C⁺∗`, `C⁻∗` | `Start/StarHeightZ4Classes.lean` |
| `cPlus_agree_check`, `cMinus_agree_check` | scanner vs. 6-state DFA (`pairCheck`) | `Start/StarHeightZ4Classes.lean` |
| `id4_check` | the PM1 identity as invariant (`checkInv`) | `Start/StarHeightZ4Moving.lean` |

## Memory (max RSS of `lake env lean <file>`, after `lake build`)

Measured with Python `resource.getrusage(RUSAGE_CHILDREN).ru_maxrss`; baseline is a file
containing only `import Mathlib` (imported `.olean` files are memory-mapped and counted).

| file | max RSS (KB) | above baseline | wall (s) |
|---|---|---|---|
| `import Mathlib` (baseline) | 8,067,052 | — | 9.9 |
| `Start/StarHeightAperiodic.lean` | 8,155,712 | +87 MB | 11.9 |
| `Start/StarHeightZ4Walk.lean` | 8,453,704 | +377 MB | 13.1 |
| `Start/StarHeightZ4Classes.lean` | 8,619,820 | +540 MB | 16.6 |
| `Start/StarHeightZ4Moving.lean` | 8,245,824 | +174 MB | 13.5 |
| `Start/StarHeightZ4PM1.lean` | 8,156,344 | +87 MB | 10.6 |
