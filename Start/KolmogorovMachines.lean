/-
The complexity measures of the library as description systems.

`Start/DescriptionSystem.lean` isolates the construction `K x = inf {|p| : p describes x}`.  Here
the concrete measures are exhibited as instances of it, so that the invariance and subadditivity
estimates can be proved once and specialised, instead of being re-proved for each measure:

* `Lambda.kolmSystem` — closed lambda terms reducing to a Church numeral (`Lambda.kolm`);
* `Lambda.kolmCondSystem y` — closed terms mapping `church y` to a Church numeral
  (`Lambda.kolmCond`);
* `Lambda.kolmWithSystem U` — programs read through a fixed interpreter `U`; the measure
  `Lambda.kolmWith` is *defined* here as the complexity of this system, and the invariance
  theorem `Lambda.kolm_le_kolmWith` is an instance of `Complexity.DescSystem.K_le_add_cost`;
* `KC.kuSystem` — bit strings accepted by the universal prefix machine (`KC.KU`).

The two measures whose definitions come later in the import order are exhibited where they are
defined: `Lambda.kolmPSystem` in `Start/ChaitinOmega.lean` (the same programs and the same output
relation as `Lambda.kolmSystem`, sized by the length of the self-delimiting code) and
`Lambda.kolmLNSystem` in `Start/KolmogorovRepresentation.lean`, where the two representations are
related by a pair of cost-free translations (`Lambda.toLNTranslation`, `Lambda.ofLNTranslation`)
from which `Lambda.kolmLN_eq_kolm` follows.  `Lambda.kt` in `Start/LevinKt.lean` is the instance
where the size of a program includes the logarithm of its running time.
-/

import Start.DescriptionSystem
import Start.KolmogorovDef
import Start.KolmogorovCond
import Start.KCMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

open Complexity Complexity.DescSystem

namespace Lambda

/-! ### Plain complexity -/

/-- Plain Kolmogorov complexity as a description system: programs are closed lambda terms, their
size is the syntactic size, and a program describes `s` when it reduces to `church s`. -/
def kolmSystem : DescSystem Lambda ℕ where
  size := size
  Outputs := IsProgramFor

@[simp] theorem kolm_eq_kolmSystem_K (s : ℕ) : kolm s = kolmSystem.K s := rfl

theorem describes_kolmSystem (s : ℕ) : kolmSystem.Describes s :=
  ⟨Lambda.church s, isProgramFor_church s⟩

/-! ### Conditional complexity -/

/-- Conditional complexity `K(· | y)` as a description system. -/
def kolmCondSystem (y : ℕ) : DescSystem Lambda ℕ where
  size := size
  Outputs := fun t s => IsCondProgramFor t s y

@[simp] theorem kolmCond_eq_kolmCondSystem_K (s y : ℕ) : kolmCond s y = (kolmCondSystem y).K s :=
  rfl

theorem describes_kolmCondSystem (s y : ℕ) : (kolmCondSystem y).Describes s :=
  ⟨Lambda.lam (Lambda.church s), isCondProgramFor_lam_of_isProgramFor (isProgramFor_church s) y⟩

/-! ### Complexity relative to an interpreter -/

/-- Complexity relative to a closed "interpreter" term `U`: a program is a closed term `p`, and it
describes `s` when `U p ↠ church s`. -/
def kolmWithSystem (U : Lambda) : DescSystem Lambda ℕ where
  size := size
  Outputs := fun p s => Lambda.IsClosed p ∧ Lambda.reduces (Lambda.app U p) (Lambda.church s)

/-- Complexity relative to a fixed interpreter `U`: the least size of a closed term `p` with
`U p ↠ church s`. -/
def kolmWith (U : Lambda) (s : ℕ) : ℕ := (kolmWithSystem U).K s

theorem kolmWith_le {U p : Lambda} {s : ℕ} (hp : Lambda.IsClosed p)
    (h : Lambda.reduces (Lambda.app U p) (Lambda.church s)) : kolmWith U s ≤ size p :=
  K_le_of_outputs (M := kolmWithSystem U) ⟨hp, h⟩

/-- Reading programs through a fixed closed interpreter `U` is a translation into plain
complexity, at the cost of the interpreter itself. -/
def kolmWithTranslation {U : Lambda} (hU : Lambda.IsClosed U) :
    Translation (kolmWithSystem U) kolmSystem where
  map := fun p => Lambda.app U p
  cost := size U + 1
  outputs := fun {p} {_} h => ⟨Lambda.IsClosed_app hU h.1, h.2⟩
  size_le := fun p => by simp [kolmSystem, kolmWithSystem]; omega

/-- **Invariance theorem.**  Interpreting programs through a fixed closed term `U` can only lower
the complexity by at most the constant `size U + 1`. -/
theorem kolm_le_kolmWith {U : Lambda} (hU : Lambda.IsClosed U) (s : ℕ)
    (h : ∃ p : Lambda, Lambda.IsClosed p ∧ Lambda.reduces (Lambda.app U p) (Lambda.church s)) :
    kolm s ≤ kolmWith U s + size U + 1 := by
  have := K_le_add_cost (kolmWithTranslation hU) (x := s) h
  simpa [kolmWith, kolmWithTranslation, Nat.add_assoc] using this

/-- The identity interpreter gives back `K`, up to its own constant: `kolmWith I` is below `K`. -/
theorem kolmWith_I_le_kolm (s : ℕ) : kolmWith Lambda.I s ≤ kolm s := by
  obtain ⟨t, ht, hsize⟩ := exists_program_of_kolm s
  have : Lambda.reduces (Lambda.app Lambda.I t) (Lambda.church s) :=
    Lambda.reduces_trans (Lambda.I_works t) ht.2
  simpa [hsize] using kolmWith_le (U := Lambda.I) ht.1 this

/-- ... and `K` is below `kolmWith I` plus a constant, so the two measures agree up to `3`. -/
theorem kolm_le_kolmWith_I (s : ℕ) : kolm s ≤ kolmWith Lambda.I s + 3 := by
  have hI : size Lambda.I = 2 := rfl
  have hIc : Lambda.IsClosed Lambda.I := fun s x => by simp [Lambda.I, Lambda.subst]
  have := kolm_le_kolmWith (U := Lambda.I) hIc s
    ⟨Lambda.church s, Lambda.church_closed s, Lambda.I_works _⟩
  omega

end Lambda

namespace KC

/-- The universal prefix machine as a description system: programs are bit strings, their size is
their length, and a string describes the numbers the machine outputs on it. -/
def kuSystem : Complexity.DescSystem (List Bool) ℕ where
  size := List.length
  Outputs := fun σ x => x ∈ U σ

theorem KU_eq_kuSystem_K (x : ℕ) : KU x = kuSystem.K x := by
  unfold KU Complexity.DescSystem.K
  congr 1
  ext n
  exact ⟨fun ⟨σ, hlen, hmem⟩ => ⟨σ, hmem, hlen⟩, fun ⟨σ, hmem, hlen⟩ => ⟨σ, hlen, hmem⟩⟩

end KC

end
