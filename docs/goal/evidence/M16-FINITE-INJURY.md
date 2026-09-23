# M16-FINITE-INJURY — the finite injury lemma

`Start/Priority.lean` proves the lemma in the abstract, over the frame of
`M16-REQUIREMENT-FRAMEWORK`.

## The data

`Lambda.Priority.Injury` collects what a finite injury construction supplies:

* `acts : ℕ → ℕ → Prop` — the `i`-th requirement acts at stage `s`.  Requirements are indexed by
  the naturals, which **linearly orders them by priority**, the smaller index having the higher
  priority.
* `Lambda.Priority.Injury.injured i s : ∃ j, j < i ∧ acts j s` — a requirement is injured exactly
  when a requirement of higher priority acts; in particular
  `Lambda.Priority.Injury.not_injured_zero`, the requirement of highest priority is never injured.
* `betweenInjury` — the one hypothesis: between two actions of a requirement, one of higher
  priority acts.  This is what the design of a construction has to establish by inspection.

## The lemma

* `Lambda.Priority.Injury.acts_finite : ∀ i, {s | acts i s}.Finite` — **each requirement acts only
  finitely often.**  By strong induction on the priority: the injuries of `i` are the actions of
  the finitely many requirements of higher priority, so they are finite, hence bounded by some
  `M`; above `M` the requirement cannot act twice, since that would need an injury in between.
* `Lambda.Priority.Injury.injured_finite` — hence each requirement is injured only finitely often.
* `Lambda.Priority.Injury.exists_final_stage` — hence from some stage on a requirement neither
  acts nor is injured.
* `Lambda.Priority.Injury.requirements_met` — the conclusion a construction draws: if a
  requirement is met as soon as it is left alone, every requirement is met.  The "as soon as it is
  left alone" step for the concrete notion of injury of `Lambda.Priority.Requirement` is
  `Lambda.Priority.Requirement.met_of_not_injured`.

## Boundary

The lemma is proved for an arbitrary `Injury`; no construction has been fed to it yet.  The
verification that a particular construction satisfies `betweenInjury` — and the strategies that
make it true — is the content of `M16-FRIEDBERG-MUCHNIK`, still open.

## Gates

`lake build` (whole tree, no errors and no new warnings), `python3 scripts/check_sorry.py`,
`python3 scripts/check_closure.py`, `python3 scripts/goal_state.py validate`,
`python3 scripts/check_manifest.py`.
