/-
**The dependent product of the local-universe model of `Type u`.**

`Start/CwaPi.lean` builds a Π-structure on the category with attributes of local universes over any
locally cartesian closed category.  This module checks that the hypothesis is inhabited by the
motivating example: `Type u` is locally cartesian closed (`Start/LcccType.lean`), so its
local-universe model of dependent type theory has a dependent product satisfying both β and η.

Main results:

* `LcccType.instLcccPullbacksType` — `Type u` is locally cartesian closed relative to its own
  pullbacks;
* `LcccType.luPiStruct`, `LcccType.luSigmaStruct` — the Π- and Σ-structures of the local-universe
  model of `Type u`;
* `LcccType.luNaturalPiStruct` — that Π-structure is natural: abstraction commutes with
  substitution.
-/

import Start.CwaPiSub
import Start.LcccType

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace LcccType

/-- `Type u` has a chosen pullback along every morphism. -/
noncomputable instance instChosenPullbacksType : ChosenPullbacks (Type u) :=
  fun f => chosenPullbacksAlong f

/-- **`Type u` is locally cartesian closed relative to its own pullbacks**, so it models the
dependent product of `Start/CwaPi.lean`. -/
noncomputable instance instLcccPullbacksType : LcccPullbacks (Type u) :=
  LcccPullbacks.ofLocallyCartesianClosed (Type u)

/-- **The dependent product of the local-universe model of `Type u`**: a Π-structure, with η, on
the category with attributes whose types are local universes. -/
noncomputable def luPiStruct : Cwa.PiStruct (Cwa.ofPullbacks (Type u)) :=
  Cwa.piStructOfLccc (Type u)

/-- **The dependent product of the local-universe model of `Type u` is natural**: abstraction
commutes with substitution, so the model interprets a calculus with substitution. -/
noncomputable def luNaturalPiStruct : Cwa.NaturalPiStruct (Cwa.ofPullbacks (Type u)) :=
  Cwa.naturalPiStructOfLccc (Type u)

/-- **The dependent sum of the local-universe model of `Type u`.** -/
noncomputable def luSigmaStruct : Cwa.SigmaStruct (Cwa.ofPullbacks (Type u)) :=
  Cwa.sigmaStructOfLccc (Type u)

end LcccType
