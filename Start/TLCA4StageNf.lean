import Start.TLCA4Hit10NotFixpoint

/-!
# TLCA open problem 4: the parametric non-fixed-point theorem
(row M20-TLCA4-BETAETA; big round 2, item A5, rebuilt in run 6 after the move to a new project)

The step terms of `Q`, `hit5`, `hit6` (≡ `hit7`), `hit8` (≡ `hit9`) and `hit10` all βη-reduce to
terms of one explicit shape,

  `nfStage x T T' = λa w. x (a (λz w'. x (a z T')) T)`   (`T`, `T'` arbitrary),

which are components of index `0` of the grammar `NG`.  Hence one theorem covers all of them:

* `nfStage`, **`nfStage_NG`** (`Start/TLCA4NfGrammar.lean`);
* **`not_fixedPoint_of_MM_nfStage`** — if `L →βη M (M s)` and `s →βη nfStage x T T'`, then `L` is
  not βη-convertible to `x L`;
* `hit5_not_fixedPoint_nf` — `hit5` again, through the parametric theorem (`s →βη b₀`,
  `h5s_reduces`).
-/

set_option autoImplicit false

namespace TLCA4

open Tm
open Lambda (BetaEtaNf betaEtaReduces betaEtaStep)

/-- **The parametric non-fixed-point theorem**: if `L →βη M (M s)` and `s` βη-reduces to the
explicit stage shape, then `L` is not βη-convertible to `x L`. -/
theorem not_fixedPoint_of_MM_nfStage {x : ℕ} {L s T T' : Lambda}
    (hL : betaEtaReduces L (.app lamM (.app lamM s))) (hs : betaEtaReduces s (nfStage x T T')) :
    ¬ Lambda.betaEtaConv L (.app (.var x) L) :=
  not_fixedPoint_of_nf (ρ := .app lamM (nfStage x T T')) (nfStage_NG x T T')
    (hL.trans ((betaEtaReduces_app_right _ (betaEtaReduces_app_right _ hs)).trans (mm_red _)))

theorem h5nf_zero_eq (x : ℕ) : h5nf x 0 = nfStage x (h5V x) (.var 0) := by
  simp [h5nf, h5Body, h5U, nfStage, qG, xPow, Lambda.lift]

/-- `hit5` again, from the parametric theorem. -/
theorem hit5_not_fixedPoint_nf (x : ℕ) :
    ¬ Lambda.betaEtaConv (toLam (actList hit5 (var x)))
      (.app (.var x) (toLam (actList hit5 (var x)))) := by
  refine not_fixedPoint_of_MM_nfStage (s := toLam (h5s x)) ?_ (h5nf_zero_eq x ▸ h5s_reduces x)
  rw [hit5_act]
  exact .refl _

end TLCA4
