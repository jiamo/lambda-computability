/-
Rice's theorem in its effective form: the code set of a convertibility-invariant set of solvable
lambda terms is many-one hard for the halting problem.

`Start/Scott.lean` shows that a non-trivial convertibility-invariant set of terms has a
non-computable code set, and `Start/ScottCurry.lean` sharpens that to recursive inseparability.
Neither says *how* hard the code set is.  This module answers that for the sets that contain no
unsolvable term: they are many-one above Kleene's diagonal halting set `Lambda.HaltK`, hence
their complements are not recursively enumerable, and they are creative as soon as they are
recursively enumerable.

The reduction is the standard "wait for the machine, then produce `M`" construction, assembled
from the parameterised minimisation of `Start/PartialCapstone.lean`:

    riceTerm M n  =  (muParam H ⌜n⌝) I M

where `H` realizes the total test "does code `n` halt on input `n` within `k` steps".  If the
`n`-th machine halts, the search reduces to a Church numeral and `riceTerm M n` reduces to `M`;
if it does not, the search has no weak head normal form, so `riceTerm M n` has no head normal
form and is unsolvable.
-/

import Start.PostCreative
import Start.PartialCapstone
import Start.HeadSolvable
import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

open Nat.Partrec (Code)
open Encodable Denumerable

------------------------------------------------------------------------
-- The step-indexed halting test
------------------------------------------------------------------------

/-- The diagonal halting test: `haltTest (pair n k) = 0` exactly when the `n`-th code halts on
the input `n` within `k` steps. -/
def haltTest (p : ℕ) : ℕ :=
  ((Code.evaln (Nat.unpair p).2 (ofNat Code (Nat.unpair p).1)
    (Nat.unpair p).1).map fun _ => 0).getD 1

theorem haltTest_evaln_primrec :
    Primrec fun p : ℕ =>
      Code.evaln (Nat.unpair p).2 (ofNat Code (Nat.unpair p).1) (Nat.unpair p).1 :=
  Code.primrec_evaln.comp
    (((Primrec.snd.comp Primrec.unpair).pair
      ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair))).pair
      (Primrec.fst.comp Primrec.unpair))

theorem haltTest_computable : Computable haltTest := by
  have hmap : Primrec fun p : ℕ =>
      (Code.evaln (Nat.unpair p).2 (ofNat Code (Nat.unpair p).1)
        (Nat.unpair p).1).map fun _ => (0 : ℕ) :=
    haltTest_evaln_primrec.option_map (Primrec.const 0).to₂
  exact (Primrec.option_getD.comp hmap (Primrec.const 1)).to_comp

theorem haltTest_eq_zero_iff (n k : ℕ) :
    haltTest (Nat.pair n k) = 0 ↔ (Code.evaln k (ofNat Code n) n).isSome := by
  unfold haltTest
  simp only [Nat.unpair_pair]
  cases Code.evaln k (ofNat Code n) n <;> simp

theorem haltK_iff_exists_haltTest (n : ℕ) : HaltK n ↔ ∃ k, haltTest (Nat.pair n k) = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
    obtain ⟨k, hk⟩ := Code.evaln_complete.1 hx
    exact ⟨k, (haltTest_eq_zero_iff n k).2 (by rw [Option.mem_def] at hk; simp [hk])⟩
  · rintro ⟨k, hk⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 ((haltTest_eq_zero_iff n k).1 hk)
    exact Part.dom_iff_mem.2 ⟨x, Code.evaln_sound hx⟩

------------------------------------------------------------------------
-- The searching term
------------------------------------------------------------------------

/-- A closed lambda realizer of the halting test. -/
def haltH : Lambda := Classical.choose (Lambda.exists_realizer_of_computable haltTest_computable)

theorem haltH_realizes : Realizes haltH haltTest :=
  Classical.choose_spec (Lambda.exists_realizer_of_computable haltTest_computable)

/-- The search for a halting stage of the `n`-th machine on the input `n`. -/
def searchTerm (n : ℕ) : Lambda := Lambda.app (muParam haltH) (Lambda.church n)

theorem searchTerm_reduces_church {n : ℕ} (h : HaltK n) :
    ∃ k, Lambda.reduces (searchTerm n) (Lambda.church k) := by
  have hex : ∃ k, haltTest (Nat.pair n k) = 0 := (haltK_iff_exists_haltTest n).1 h
  refine ⟨Nat.find hex, muParam_reduces_church haltH_realizes n (Nat.find hex)
    (fun y hy => Nat.find_min hex hy) (Nat.find_spec hex)⟩

theorem searchTerm_not_hasHnf {n : ℕ} (h : ¬ HaltK n) : ¬ HasHnf (searchTerm n) := by
  intro hhnf
  obtain ⟨u, hu, hisHnf⟩ := hhnf
  have hno : ∀ y, haltTest (Nat.pair n y) ≠ 0 := by
    intro y hy
    exact h ((haltK_iff_exists_haltTest n).2 ⟨y, hy⟩)
  exact muParam_not_hasWhnfEval haltH_realizes n hno
    (hasWhnfEval_of_reduces_whnf hu (IsWhnf.of_isHnf hisHnf))

------------------------------------------------------------------------
-- The reduction
------------------------------------------------------------------------

/-- The term of the reduction: it reduces to `M` when the `n`-th machine halts on `n`, and is
unsolvable otherwise. -/
def riceTerm (M : Lambda) (n : ℕ) : Lambda :=
  Lambda.app (Lambda.app (searchTerm n) Lambda.I) M

theorem riceTerm_reduces {M : Lambda} {n : ℕ} (h : HaltK n) :
    Lambda.reduces (riceTerm M n) M := by
  obtain ⟨k, hk⟩ := searchTerm_reduces_church h
  exact Lambda.reduces_trans (Lambda.reduces_app_left (Lambda.reduces_app_left hk))
    (church_force k M)

theorem riceTerm_not_solvable {M : Lambda} {n : ℕ} (h : ¬ HaltK n) :
    ¬ Solvable (riceTerm M n) := by
  intro hs
  exact searchTerm_not_hasHnf h (hasHnf_of_solvable hs).app_left.app_left

theorem riceCode_eq (M : Lambda) (n : ℕ) :
    Lambda.encode (riceTerm M n) =
      Lambda.app_code (Lambda.app_code
        (Lambda.app_code (Lambda.encode (muParam haltH)) (Lambda.church_code n))
        (Lambda.encode Lambda.I)) (Lambda.encode M) := by
  simp [riceTerm, searchTerm, Lambda.encode_app, Lambda.encode_church_eq_church_code]

theorem riceCode_primrec (M : Lambda) : Primrec fun n => Lambda.encode (riceTerm M n) := by
  have h : Primrec fun n : ℕ =>
      Lambda.app_code (Lambda.app_code
        (Lambda.app_code (Lambda.encode (muParam haltH)) (Lambda.church_code n))
        (Lambda.encode Lambda.I)) (Lambda.encode M) :=
    Lambda.app_code_primrec.comp
      (Lambda.app_code_primrec.comp
        (Lambda.app_code_primrec.comp (Primrec.const _) Lambda.church_code_primrec)
        (Primrec.const _))
      (Primrec.const _)
  exact h.of_eq fun n => (riceCode_eq M n).symm

------------------------------------------------------------------------
-- Rice's theorem, effective form
------------------------------------------------------------------------

/-- **Rice's theorem, effective form.**  If `A` is invariant under convertibility, contains a
term `M`, and contains no unsolvable term, then the diagonal halting set reduces many-one to the
code set of `A`. -/
theorem manyOneReducible_haltK_codeSet {A : Lambda → Prop} (hA : ConvInvariant A) {M : Lambda}
    (hAM : A M) (hAsolv : ∀ t, A t → Solvable t) : HaltK ≤₀ CodeSet A := by
  refine ⟨fun n => Lambda.encode (riceTerm M n), (riceCode_primrec M).to_comp, fun n => ?_⟩
  rw [codeSet_encode]
  constructor
  · intro h
    exact hA M (riceTerm M n) (conv_of_reduces (riceTerm_reduces h)).symm hAM
  · intro h
    by_contra hn
    exact riceTerm_not_solvable hn (hAsolv _ h)

/-- Consequently the complement of such a code set is not recursively enumerable. -/
theorem not_rePred_compl_codeSet {A : Lambda → Prop} (hA : ConvInvariant A) {M : Lambda}
    (hAM : A M) (hAsolv : ∀ t, A t → Solvable t) :
    ¬ REPred fun c => ¬ CodeSet A c := by
  intro hre
  obtain ⟨f, hf, hfe⟩ := manyOneReducible_haltK_codeSet hA hAM hAsolv
  refine not_rePred_not_haltK ?_
  have heq : (fun n => ¬ HaltK n) = fun n => ¬ CodeSet A (f n) :=
    funext fun n => propext (not_congr (hfe n))
  rw [heq]
  exact hre.comp hf

/-- And such a code set is creative as soon as it is recursively enumerable. -/
theorem creative_codeSet {A : Lambda → Prop} (hA : ConvInvariant A) {M : Lambda}
    (hAM : A M) (hAsolv : ∀ t, A t → Solvable t) (hre : REPred (CodeSet A)) :
    Post.Creative (CodeSet A) :=
  Post.creative_of_manyOneComplete hre fun _ hq =>
    (rePred_le_haltK hq).trans (manyOneReducible_haltK_codeSet hA hAM hAsolv)

------------------------------------------------------------------------
-- Instances
------------------------------------------------------------------------

/-- Solvability of a lambda term is many-one hard for the halting problem. -/
theorem manyOneReducible_haltK_codeSet_solvable : HaltK ≤₀ CodeSet Solvable :=
  manyOneReducible_haltK_codeSet convInvariant_solvable solvable_I fun _ h => h

/-- Convertibility with a Church numeral is many-one hard for the halting problem. -/
theorem manyOneReducible_haltK_codeSet_conv_church (m : ℕ) :
    HaltK ≤₀ CodeSet fun t => Conv t (Lambda.church m) :=
  manyOneReducible_haltK_codeSet (fun _ _ hst hs => hst.symm.trans hs) (conv_refl _)
    fun _ h => Solvable.of_conv h.symm (solvable_church m)

/-- The set of codes of the *unsolvable* terms is not recursively enumerable. -/
theorem not_rePred_compl_codeSet_solvable : ¬ REPred fun c => ¬ CodeSet Solvable c :=
  not_rePred_compl_codeSet convInvariant_solvable solvable_I fun _ h => h

/-- The set of codes of the terms *not* convertible with a given Church numeral is not
recursively enumerable. -/
theorem not_rePred_compl_codeSet_conv_church (m : ℕ) :
    ¬ REPred fun c => ¬ CodeSet (fun t => Conv t (Lambda.church m)) c :=
  not_rePred_compl_codeSet (fun _ _ hst hs => hst.symm.trans hs) (conv_refl _)
    fun _ h => Solvable.of_conv h.symm (solvable_church m)

end Lambda
