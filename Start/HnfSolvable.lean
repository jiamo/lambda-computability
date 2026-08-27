/-
Head normal forms and solvability.

`Start/GraphAdequacy.lean` proves one half of the classical characterization semantically, and
`Start/HeadSolvable.lean` proves it again syntactically: a solvable term has a head normal form.
This file proves the other half — a closed term with a head normal form is solvable — and puts
the two together.  The construction reuses
the substitution calculus of `Start/Bohm.lean`: an `n`-fold abstraction applied to `n` closed
arguments performs `Lambda.substDown`, and `λy₁ … y_m. I` returns the identity once it has
received its `m` arguments.

* `Lambda.exists_lamN_neutral`, `Lambda.exists_appList_var` — a head normal form is
  `λx₁ … xₙ. y M₁ … Mₘ`;
* `Lambda.solvable_of_isHnf` — a closed head normal form is solvable: apply it to `n` copies of
  `λy₁ … y_m. I`, which turns the head variable into a term that eats the `m` arguments and
  returns the identity;
* `Lambda.solvable_of_hasHnf`, `Lambda.solvable_iff_hasHnf` — hence, for closed terms,
  solvability and head normalizability coincide;
* `GraphModel.denot_ne_empty_iff_solvable` — and both coincide with having a nonempty denotation
  in Scott's graph model, so the least element of the model is exactly the unsolvable terms.
-/

import Start.GraphAdequacy
import Start.FreeVars
import Start.HeadSolvable

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- Every head normal form is an iterated abstraction over a neutral term. -/
theorem exists_lamN_neutral : ∀ {H : Lambda}, IsHnf H → ∃ (n : ℕ) (v : Lambda),
    H = lamN n v ∧ Neutral v := by
  intro H h
  induction h with
  | neutral hn => exact ⟨0, _, rfl, hn⟩
  | @lam u _ ih =>
      obtain ⟨n, v, rfl, hv⟩ := ih
      exact ⟨n + 1, v, rfl, hv⟩

/-- Every neutral term is a variable applied to a list of arguments. -/
theorem exists_appList_var : ∀ {v : Lambda}, Neutral v → ∃ (k : ℕ) (args : List Lambda),
    v = appList (Lambda.var k) args := by
  intro v h
  induction h with
  | var n => exact ⟨n, [], rfl⟩
  | @app M N _ ih =>
      obtain ⟨k, args, rfl⟩ := ih
      exact ⟨k, args ++ [N], (appList_concat (Lambda.var k) N args).symm⟩

/-- **A closed head normal form is solvable.** -/
theorem solvable_of_isHnf {H : Lambda} (hcl : Lambda.IsClosed H) (h : IsHnf H) : Solvable H := by
  obtain ⟨n, v, rfl, hv⟩ := exists_lamN_neutral h
  obtain ⟨k, args, rfl⟩ := exists_appList_var hv
  have hfb : freeBelow n (appList (Lambda.var k) args) := by
    have h0 : freeBelow 0 (lamN n (appList (Lambda.var k) args)) :=
      freeBelow_zero_of_isClosed hcl
    simpa only [Nat.zero_add] using (freeBelow_lamN_iff n).1 h0
  have hk : k < n := ((freeBelow_appList_iff args).1 hfb).1
  -- every binder receives the same closed term, which returns the identity after `m` arguments
  set m := args.length with hm
  set A : Lambda := lamN m Lambda.I with hA
  have hAcl : Lambda.IsClosed A := IsClosed_lamN Lambda.I_closed m
  set as : List Lambda := argsFor (fun _ => A) n with has
  have hascl : ∀ a ∈ as, Lambda.IsClosed a := by
    intro a ha
    obtain ⟨j, -, rfl⟩ := mem_argsFor ha
    exact hAcl
  have haslen : as.length = n := argsFor_length _ n
  refine ⟨as, hascl, ⟨Lambda.I, ?_, Lambda.reduces.refl _⟩⟩
  have h1 : Lambda.reduces (appList (lamN n (appList (Lambda.var k) args)) as)
      (substDown as (appList (Lambda.var k) args)) := by
    have := reduces_appList_lamN hascl (appList (Lambda.var k) args)
    rwa [haslen] at this
  refine Lambda.reduces_trans h1 ?_
  rw [substDown_appList, substDown_argsFor_var (fun _ => hAcl) (by omega)]
  have hlen : (args.map (substDown as)).length = m := by simp [hm]
  have h2 := reduces_appList_lamN_closed Lambda.I_closed (args.map (substDown as))
  rwa [hlen] at h2

/-- **A closed term with a head normal form is solvable.** -/
theorem solvable_of_hasHnf {t : Lambda} (hcl : Lambda.IsClosed t) (h : HasHnf t) : Solvable t := by
  obtain ⟨u, hu, hhnf⟩ := h
  have hcl' : Lambda.IsClosed u := hcl.reduces hu
  exact Solvable.of_conv ⟨u, Lambda.reduces.refl u, hu⟩ (solvable_of_isHnf hcl' hhnf)

/-- **Wadsworth's characterization** for closed terms: being solvable is the same as having a
head normal form. -/
theorem solvable_iff_hasHnf {t : Lambda} (hcl : Lambda.IsClosed t) : Solvable t ↔ HasHnf t :=
  ⟨hasHnf_of_solvable, solvable_of_hasHnf hcl⟩

end Lambda

namespace GraphModel

/-- **The least element of the graph model is exactly the unsolvable terms.**  For a closed term
the denotation is nonempty iff the term is solvable. -/
theorem denot_ne_empty_iff_solvable {t : Lambda} (hcl : Lambda.IsClosed t) (ρ : Env) :
    denot t ρ ≠ (∅ : D) ↔ Lambda.Solvable t :=
  (denot_ne_empty_iff_hasHnf hcl ρ).trans (Lambda.solvable_iff_hasHnf hcl).symm

end GraphModel
