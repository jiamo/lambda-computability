# M10-COMPLEXITY-DESCSYSTEM

**Status:** DONE_STRONG

The library had six independent Kolmogorov-style complexity measures, each spelling out its own
`sInf {n | ∃ …}` and each re-proving its own invariance statement:

| measure      | location                                 |
| ------------ | ---------------------------------------- |
| `kolm`       | `Start/KolmogorovDef.lean`               |
| `kolmWith U` | `Start/Kolmogorov.lean`                  |
| `kolmP`      | `Start/ChaitinOmega.lean`                |
| `KU`         | `Start/KCMachine.lean`                   |
| `kolmCond`   | `Start/KolmogorovCond.lean`              |
| `kolmLN`     | `Start/KolmogorovRepresentation.lean`    |

## The abstraction — `Start/DescriptionSystem.lean`

`Complexity.DescSystem P α` is a *description system*: a type `P` of programs, a `size : P → ℕ`
and an output relation `Outputs : P → α → Prop`.  On top of it:

* `Complexity.DescSystem.K` — the complexity `sInf {n | ∃ p, size p = n ∧ Outputs p x}`;
* `Complexity.DescSystem.K_le_of_outputs`, `exists_outputs_size_eq_K` — the two directions of the
  infimum, once and for all;
* `Complexity.Translation` — a size-bounded compiler between two systems;
* **`Complexity.K_le_add_cost`** — the *generic invariance theorem*: a translation of cost `c`
  gives `K₂ x ≤ K₁ x + c`;
* `Complexity.Optimal`, `optimal_of_translation`, `optimal_refl`, `optimal_trans`;
* `Complexity.K_le_add_of_combine`, `K_le_add_of_apply` — generic subadditivity.

## The instances — `Start/KolmogorovMachines.lean`

`Lambda.kolmSystem`, `Lambda.kolmCondSystem y`, `Lambda.kolmWithSystem U` and `KC.kuSystem`, with
`Lambda.kolm_eq_kolmSystem_K`, `Lambda.kolmCond_eq_kolmCondSystem_K` and `KC.KU_eq_kuSystem_K`
identifying them with the existing measures.

The abstraction deletes code rather than adding it: `kolmWith` and its two invariance theorems
moved out of `Start/Kolmogorov.lean` into `Start/KolmogorovMachines.lean`, and
`Lambda.kolm_le_kolmWith` is now a one-line instance of `Complexity.K_le_add_cost`.

## The two remaining measures

`Lambda.kolmP` and `Lambda.kolmLN` are defined after `Start/KolmogorovMachines.lean` in the import
order, so their systems sit next to their definitions:

* `Lambda.kolmPSystem` (`Start/ChaitinOmega.lean`) — the programs and the output relation of
  `Lambda.kolmSystem`, sized by the length of the self-delimiting code, with
  `Lambda.kolmP_eq_kolmPSystem_K` and `Lambda.describes_kolmPSystem`;
* `Lambda.kolmLNSystem` (`Start/KolmogorovRepresentation.lean`) — locally nameless programs sized
  by `Lambda.sizeLN`, with `Lambda.kolmLN_eq_kolmLNSystem_K` and `Lambda.describes_kolmLNSystem`.
  `Lambda.toLNTranslation` is a cost-free translation of `kolmSystem` into it
  (`Lambda.sizeLN_toLN_le`: the translation never grows a term), which gives one half of
  `Lambda.kolmLN_eq_kolm` from the generic invariance theorem.  There is no translation back:
  `Lambda.ofLN 0 d` sends an atom to the de Bruijn index `d`, so it preserves the size only on
  closed terms, and the other half still goes through the shortest program — now obtained from
  the generic `Complexity.DescSystem.exists_outputs_size_eq_K`.

## Gates

* `python3 scripts/goal_state.py validate`
* `python3 scripts/check_closure.py`
* `lake build Start.DescriptionSystem Start.KolmogorovMachines`
