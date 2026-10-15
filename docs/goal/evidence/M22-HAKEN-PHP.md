# M22-HAKEN-PHP — the pigeonhole principle needs exponential-size resolution refutations

**Status:** DONE_STRONG (for the resolution refutations of the library, which are tree-shaped;
see the caveat below).

Module: `Start/ResolutionPHP.lean` (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound` only).

## Statements

* `Complexity.Sat.PHP.php n : Cnf` — `PHP(n+1, n)` over the CNFs of `Start/Sat.lean`: the variable
  `var n i j = n·i + j` says that pigeon `i ≤ n` sits in hole `j < n`; one clause per pigeon
  (`pigeonClause`), one clause `¬p i j ∨ ¬p k j` per hole and pair `i < k` (`holeClauses`).
* `Complexity.Sat.PHP.php_unsat : ∀ σ, cnfVal σ (php n) = false` (first exit criterion).
* **`Complexity.Sat.PHP.php_refutation_size (n) (d : Refutation (php n)) : 2 ^ n ≤ d.size`**
  (second exit criterion, `c = 1`).  Packaged: `haken_php`.

## Proof

The Prover–Delayer argument (Pudlák–Impagliazzo), as an induction on the derivation
(`size_ge_of_falsifies`): if `d` derives a clause `C` and `ρ` is a partial assignment that
falsifies `C` and puts no two pigeons in one hole (`Inv`), then `2^(n - pot ρ) ≤ d.size`, where
`pot ρ` is the number of true entries plus the number of false entries whose pigeon and hole are
both free.

* Leaf: a falsified pigeon clause forces `pot ρ ≥ n` (`pot_ge_of_pigeon`: every hole is either
  taken, giving a true entry, or free, giving a free false entry in that pigeon's row); a hole
  clause is never falsified (`not_falsifies_hole`).
* Resolution on a variable `ρ` already assigns: follow the premise that `ρ` falsifies.
* Resolution on an unassigned grid variable `p i j` with pigeon `i` matched or hole `j` taken: set
  it false; `pot` does not grow (`pot_forced`).
* Unassigned with `i` and `j` both free: follow both premises, with `p i j` false and true; `pot`
  grows by at most one in each (`pot_free`), so the subtree sizes add up to `2^(n - pot ρ)`.
* Unassigned non-grid variable: set it false; `pot` is unchanged (`pot_outside`).

At the root `ρ` is empty, `pot = 0`, and the empty clause is falsified.

## Caveat: tree-like versus general resolution

`Complexity.Sat.Deriv` (`Start/Resolution.lean`) is an inductive *tree*: a resolution step takes
two subderivations, and `Deriv.size` counts the nodes of the tree, so a clause used twice is
derived (and counted) twice.  The exit criterion "every resolution refutation of `PHP(n+1, n)` has
size at least `2^(cn)`" is proved for exactly these refutations.  This is the lower bound for
tree-like resolution, which is easier than Haken's theorem for general (DAG-like) resolution:
Haken's bottleneck argument, or Beame–Pitassi's width argument, is needed when derived clauses
may be shared.  The library has no DAG-shaped resolution proofs, so that stronger statement is
not formulated here; it would need a line-based notion of refutation (a list of clauses, each an
axiom or a resolvent of two earlier ones) and is a natural follow-up row.

`#print axioms` output for the terminal theorems of this delivery: `docs/goal/evidence/M29-PART1-axioms.txt` (only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`).

## Correction (this delivery): M22-HAKEN-PHP is DONE_WEAK, gap M22-HAKEN-PHP-DAG

`Deriv` in `Start/Resolution.lean` is a tree, so `haken_php` is the tree-like bound.  Haken's
theorem concerns general resolution, where a derived clause is reused; a DAG-like refutation of
size `s` can unfold into a tree of size up to `2^s`, so the tree-like bound does not imply it.
M22-HAKEN-PHP is therefore `DONE_WEAK` (terminal statement unchanged) and depends on the new row
M22-HAKEN-PHP-DAG.

### M22-HAKEN-PHP-DAG: exit criterion 1 (`Start/ResolutionDag.lean`)

```lean
def DagStep (F : Cnf) (prev : List Clause) (C : Clause) : Prop   -- initial, or resolvent of two of prev
inductive DagDeriv (F : Cnf) : List Clause → Prop                -- nil, snoc
structure DagRefutation (F : Cnf) where
  lines : List Clause
  valid : DagDeriv F lines
  last : lines.getLast? = some []
def DagRefutation.size (R : DagRefutation F) : ℕ := R.lines.length

theorem DagRefutation.unsat (R : DagRefutation F) : ∀ σ, cnfVal σ F = false
theorem Refutation.toDag_size (d : Refutation F) : d.toDag.size = d.size
theorem Refutation.exists_dag_size_le (d : Refutation F) : ∃ R : DagRefutation F, R.size ≤ d.size
```

`Refutation.toDag` lists the clauses of the tree in postorder.

### Exit criterion 2: open.  First missing lemma (Beame–Pitassi monotone width bound)

```lean
theorem Complexity.Sat.PHP.dag_exists_wide_monotone (n : ℕ) (hn : 2 ≤ n) (R : DagRefutation (php n)) :
    ∃ C ∈ R.lines, 2 * n ^ 2 ≤ 9 * (monoVars n C).card
```

where `monoVars n C : Finset (ℕ × ℕ)` is the set of pairs `(i, j)` such that `x_(i,j)` occurs in
the monotone translation of `C` (a positive `x_(i,j)`, or a negative `x_(i',j)` with `i' ≠ i`).
The rest of the argument is the greedy restriction that kills the wide clauses.
