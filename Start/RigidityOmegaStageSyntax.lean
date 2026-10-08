import Start.RigidityOmegaPowerDefinability

/-
Absorbed from github.com/openai/math (commit adc7f1241, Apache-2.0),
file `lean/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaStageSyntax.lean`, family 241,
paper "Rigidity of the Turing degrees".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Rigidity*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.
-/

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

def omegaStageMatrix (s f r x A : ℕ) : Formula :=
  .conj (.subset s A)
    (.conj (.allMem A (.disj (.member 0 (s+1))
      (.existsMem (x+1) (.existsMem (r+2)
        (.conj (.pairMem 1 0 (f+3)) (.member 2 0))))))
      (.allMem x (.allMem (r+1)
        (.imp (.pairMem 1 0 (f+2)) (.subset 0 (A+2))))))

theorem omegaStageMatrix_eval (s f r x A : ℕ) (e : ℕ → ZFSet.{u}) :
    (omegaStageMatrix s f r x A).Eval e ↔ StageStep (e s) (e f) (e r) (e x) (e A) := by
  simp only [omegaStageMatrix,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_disj,Formula.eval_pairMem,Formula.eval_imp,cons_zero,cons_succ,StageStep]

def ordinalAllMem (i : ℕ) (p : SentenceForm) : SentenceForm :=
  .all (.imp (.member 0 (i+1)) p)

theorem ordinalAllMem_sat (M : ZFSet.{u}) (hM : Transitive M)
    (i : ℕ) (p : SentenceForm) (e : ℕ → ZFSet.{u}) (hi : e i ∈ M) :
    (ordinalAllMem i p).Sat (M : Set ZFSet) e ↔
      ∀ x ∈ e i, p.Sat (M : Set ZFSet) (cons x e) := by
  simp only [ordinalAllMem,SentenceForm.sat_all,SentenceForm.sat_imp,
    SentenceForm.Sat,cons_zero,cons_succ]
  exact ⟨fun h x hx => h x (hM _ hi x hx) hx,fun h x _ hx => h x hx⟩

noncomputable def ordinalProductAt (v a b : ℕ) : SentenceForm :=
  productSentence.rename (fun i => if i = 0 then v else if i = 1 then a else b)

theorem ordinalProductAt_sound (M : ZFSet.{u}) (hM : Transitive M)
    (v a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (ha : (e a).IsOrdinal) (hb : (e b).IsOrdinal) :
    (ordinalProductAt v a b).Sat (M : Set ZFSet) e →
      e v = ((e a).rank * (e b).rank).toZFSet := by
  rw [ordinalProductAt,SentenceForm.sat_rename]
  exact productSentence_sound M hM _ (fun i => he _) _ _
    ha.toZFSet_rank_eq.symm hb.toZFSet_rank_eq.symm

theorem ordinalProductAt_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (v a b : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (ha : (e a).IsOrdinal) (hb : (e b).IsOrdinal) :
    (ordinalProductAt v a b).Sat (M : Set ZFSet) e ↔
      e v = ((e a).rank * (e b).rank).toZFSet := by
  rw [ordinalProductAt,SentenceForm.sat_rename]
  exact productSentence_sourceT M hM hT _ (fun i => he _) _ _
    ha.toZFSet_rank_eq.symm hb.toZFSet_rank_eq.symm

end TuringRigidity.OrdinalArithmetic

