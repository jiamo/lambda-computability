/-
**Hardness for polynomial space as a property of a language, and what it buys.**

`Start/QbfCobReduction.lean` proves the reduction: every language of (nondeterministic)
polynomial space is many-one reducible to `Complexity.Qbf.tqbfLang` by a single Cobham term.  This
module packages that as a property of a language — hardness — and draws the consequences that make
a hardness theorem worth proving: hardness travels along reductions, and an efficient algorithm for
a hard language is an efficient algorithm for the whole class.

Two cost models meet here, as everywhere in this library: polynomial *time* is Cobham's class
(`Start/ComplexityClasses.lean`) and *space* is the offline machine of `Start/SpaceMachine.lean`.
A hardness statement is exactly the bridge between them, since the reduction is a polynomial-time
map and the class reduced is a space class.

Main definitions:

* `Complexity.Space.PSPACEHard`, `.NPSPACEHard` — hardness for (nondeterministic) polynomial
  space, under polynomial-time many-one reducibility;
* `Complexity.Space.PSPACEComplete` — hardness together with membership.

Main results:

* `Complexity.Space.pspaceHard_tqbfLang'`, `.npspaceHard_tqbfLang'` — **`TQBF` is hard for
  polynomial space**, in that vocabulary;
* `Complexity.Space.PSPACEHard.of_reduction` — hardness travels along a reduction, so any language
  that `TQBF` reduces to is hard as well;
* `Complexity.Space.PSPACEHard.inP_of_inP`, `.inNP_of_inNP` — **a hard language in `P` (resp. in
  `NP`) puts the whole of `PSPACE` there**;
* `Complexity.Space.pspace_inP_of_tqbf_inP`, `.tqbf_not_inP` — the two directions of that for
  `TQBF`: a polynomial-time decision procedure for `TQBF` would decide every language of
  polynomial space in polynomial time, and conversely one language of polynomial space outside `P`
  keeps `TQBF` out of `P`.
-/

import Mathlib
import Start.QbfCobReduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Space

open Complexity (Language InP InNP PolyManyOne)

/-! ### Hardness -/

/-- `L` is hard for polynomial space: every language of polynomial space reduces to it by a
polynomial-time many-one reduction. -/
def PSPACEHard (L : Language) : Prop := ∀ L' : Language, PSPACE L' → PolyManyOne L' L

/-- `L` is hard for nondeterministic polynomial space. -/
def NPSPACEHard (L : Language) : Prop := ∀ L' : Language, NPSPACE L' → PolyManyOne L' L

/-- `L` is complete for polynomial space: it lies in the class and is hard for it. -/
def PSPACEComplete (L : Language) : Prop := PSPACE L ∧ PSPACEHard L

theorem PSPACEHard.of_npspaceHard {L : Language} (h : NPSPACEHard L) : PSPACEHard L :=
  fun L' hL' => h L' (npspace_of_pspace hL')

/-- Hardness travels along a reduction: if a hard language reduces to `L'`, then `L'` is hard. -/
theorem PSPACEHard.of_reduction {L L' : Language} (h : PSPACEHard L) (hred : PolyManyOne L L') :
    PSPACEHard L' :=
  fun L'' hL'' => polyManyOne_trans (h L'' hL'') hred

theorem NPSPACEHard.of_reduction {L L' : Language} (h : NPSPACEHard L) (hred : PolyManyOne L L') :
    NPSPACEHard L' :=
  fun L'' hL'' => polyManyOne_trans (h L'' hL'') hred

/-! ### `TQBF` is hard for polynomial space -/

/-- **`TQBF` is hard for polynomial space.** -/
theorem pspaceHard_tqbfLang' : PSPACEHard Complexity.Qbf.tqbfLang :=
  fun _ hL => Complexity.Qbf.QBF.pspaceHard_tqbfLang hL

/-- **`TQBF` is hard even for nondeterministic polynomial space.** -/
theorem npspaceHard_tqbfLang' : NPSPACEHard Complexity.Qbf.tqbfLang :=
  fun _ hL => Complexity.Qbf.QBF.npspaceHard_tqbfLang hL

/-! ### What hardness buys -/

/-- A hard language decided in polynomial time decides every language of polynomial space in
polynomial time. -/
theorem PSPACEHard.inP_of_inP {L : Language} (h : PSPACEHard L) (hL : InP L)
    {L' : Language} (hL' : PSPACE L') : InP L' :=
  InP.of_reduction (h L' hL') hL

/-- A hard language in `NP` puts the whole of polynomial space in `NP`. -/
theorem PSPACEHard.inNP_of_inNP {L : Language} (h : PSPACEHard L) (hL : InNP L)
    {L' : Language} (hL' : PSPACE L') : InNP L' :=
  InNP.of_reduction (h L' hL') hL

theorem NPSPACEHard.inP_of_inP {L : Language} (h : NPSPACEHard L) (hL : InP L)
    {L' : Language} (hL' : NPSPACE L') : InP L' :=
  InP.of_reduction (h L' hL') hL

/-- **If `TQBF` is decided in polynomial time then so is every language of polynomial space** —
the statement `P = PSPACE` would follow from a polynomial-time algorithm for `TQBF`, one half of
what makes `TQBF` the canonical hard problem of the class. -/
theorem pspace_inP_of_tqbf_inP (h : InP Complexity.Qbf.tqbfLang)
    {L : Language} (hL : PSPACE L) : InP L :=
  pspaceHard_tqbfLang'.inP_of_inP h hL

/-- The same for nondeterministic polynomial space, which by the hardness theorem is no harder. -/
theorem npspace_inP_of_tqbf_inP (h : InP Complexity.Qbf.tqbfLang)
    {L : Language} (hL : NPSPACE L) : InP L :=
  npspaceHard_tqbfLang'.inP_of_inP h hL

/-- The contrapositive: **one language of polynomial space outside `P` keeps `TQBF` outside
`P`.** -/
theorem tqbf_not_inP {L : Language} (hL : PSPACE L) (hnot : ¬ InP L) :
    ¬ InP Complexity.Qbf.tqbfLang :=
  fun h => hnot (pspace_inP_of_tqbf_inP h hL)

/-- If `TQBF` lies in `NP` then every language of polynomial space does. -/
theorem pspace_inNP_of_tqbf_inNP (h : InNP Complexity.Qbf.tqbfLang)
    {L : Language} (hL : PSPACE L) : InNP L :=
  pspaceHard_tqbfLang'.inNP_of_inNP h hL

/-- Hardness of `TQBF` transfers to every language it reduces to. -/
theorem pspaceHard_of_tqbf_reduction {L : Language} (h : PolyManyOne Complexity.Qbf.tqbfLang L) :
    PSPACEHard L :=
  pspaceHard_tqbfLang'.of_reduction h

end Space

end Complexity
