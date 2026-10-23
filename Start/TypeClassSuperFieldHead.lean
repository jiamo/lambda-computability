import Start.TypeClassSuperFieldMeasure

/-!
# Series V, big round, run 3, item C1: head forms of dictionaries under `SuperField`
(row M25-TYPECLASS-SUPER-FIELD)

Under `SuperField` for every instance, every elaborated dictionary reduces, without increasing
its size, to a dictionary in **head form**: either a chain of superclass projections of a
hypothesis, or an instance applied to dictionaries for its context.  The superclass projection of
an instance dictionary is contracted with `DEnt.superMeasure_lt`, which strictly decreases the
size of the term, so the size is the termination measure.

* `DEntHyp` — superclass projections of a hypothesis;
* `DEntH` — head forms;
* **`DEnt.headForm`** — every dictionary reduces to a head form of no larger size;
* `DEntHyp.unique`, `DEntHyp.not_instHead` — in a `SuperInstFragment`, two projection chains for
  one constraint coincide, and no projection chain is for an instance head.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-- Superclass projections of a hypothesis. -/
inductive DEntHyp (E : Env) (P : List Cstr) (n : ℕ) : Cstr → Lambda → Prop
  | hyp {C : Cstr} {i : ℕ} : P[i]? = some C → DEntHyp E P n C (Lambda.var (n + i))
  | sup {c d : ℕ} {τ : Mty} {D : ClassDecl} {dd : Lambda} : E.classes[c]? = some D →
      D.super = some d → DEntHyp E P n ⟨c, τ⟩ dd →
      DEntHyp E P n ⟨d, τ⟩ (recProj (dictFields (dictTy E) D τ).length 0 dd)

/-- Head forms of dictionaries: a projection chain over a hypothesis, or an instance applied to
dictionaries for its context. -/
inductive DEntH (E : Env) (P : List Cstr) (n : ℕ) : Cstr → Lambda → Prop
  | ofHyp {C : Cstr} {d : Lambda} : DEntHyp E P n C d → DEntH E P n C d
  | inst {I : Inst} {s : ℕ → Mty} {ds : List Lambda} : I ∈ E.insts →
      ds.length = I.ctxt.length →
      (∀ (k : ℕ) (hk : k < ds.length) (hk' : k < I.ctxt.length),
        DEnt E P n ((I.ctxt[k]).subst s) (ds[k])) →
      DEntH E P n ⟨I.cls, msubst s I.head⟩
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)

theorem DEntHyp.toDEnt {E : Env} {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda}
    (h : DEntHyp E P n C d) : DEnt E P n C d := by
  induction h with
  | hyp hi => exact DEnt.hyp hi
  | sup hc hs _ ih => exact DEnt.sup hc hs ih

theorem DEntH.toDEnt {E : Env} {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda}
    (h : DEntH E P n C d) : DEnt E P n C d := by
  cases h with
  | ofHyp h => exact h.toDEnt
  | inst hI hds hall => exact DEnt.inst hI hds hall

/-- **Head forms under `SuperField`.**  If every instance is well formed for its superclass, every
elaborated dictionary reduces to a dictionary in head form, for the same constraint, of no larger
size. -/
theorem DEnt.headForm {E : Env} (hE : EnvGood E) (hSF : ∀ I ∈ E.insts, SuperField E I)
    {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda} (h : DEnt E P n C d) :
    ∃ e, DEntH E P n C e ∧ Lambda.reduces d e ∧ dsize e ≤ dsize d := by
  suffices H : ∀ N, ∀ C d, DEnt E P n C d → dsize d ≤ N →
      ∃ e, DEntH E P n C e ∧ Lambda.reduces d e ∧ dsize e ≤ dsize d from
    H _ C d h le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro C d h hle
  induction h with
  | hyp hi => exact ⟨_, .ofHyp (.hyp hi), Lambda.reduces.refl _, le_rfl⟩
  | inst hI hds hall => exact ⟨_, .inst hI hds hall, Lambda.reduces.refl _, le_rfl⟩
  | @sup c d' τ D dd hc hs hdd ih =>
    have hle' : dsize dd ≤ N := by
      simp only [recProj, dsize] at hle; omega
    obtain ⟨e, he, hred, hsz⟩ := ih hle'
    cases he with
    | ofHyp he =>
      refine ⟨_, .ofHyp (.sup hc hs he), reduces_recProj hred, ?_⟩
      simp only [recProj, dsize]; omega
    | @inst I s ds hI hds hall =>
      obtain ⟨sd, hsd, hred2, hlt⟩ := DEnt.superMeasure_lt hE (hSF I hI) hc hs hds hall
      have hlt' : dsize (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) < N := by
        simp only [recProj, dsize] at hlt hle ⊢; omega
      obtain ⟨g, hg, hred3, hsz3⟩ :=
        IHN _ hlt' _ _ hsd le_rfl
      refine ⟨g, hg, Lambda.reduces_trans (reduces_recProj hred)
        (Lambda.reduces_trans hred2 hred3), ?_⟩
      simp only [recProj, dsize] at hlt ⊢; omega

/-- Projection chains over hypotheses are normal derivations. -/
theorem DEntHyp.toDEntN {E : Env} {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda}
    (h : DEntHyp E P n C d) : DEntN E P n false C d := by
  induction h with
  | hyp hi => exact DEntN.hyp hi
  | sup hc hs _ ih => exact DEntN.sup hc hs ih

/-- **Two projection chains for one constraint coincide** in a `SuperInstFragment`. -/
theorem DEntHyp.unique {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperInstFragment E P)
    {C : Cstr} {d d' : Lambda} (h : DEntHyp E P n C d) (h' : DEntHyp E P n C d') : d = d' :=
  DEntN.unique hF h.toDEntN h'.toDEntN

/-- **A projection chain is never for an instance head** in a `SuperInstFragment`. -/
theorem DEntHyp.not_instHead {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperInstFragment E P)
    {I : Inst} (hI : I ∈ E.insts) {s : ℕ → Mty} {d : Lambda}
    (h : DEntHyp E P n ⟨I.cls, msubst s I.head⟩ d) : False := by
  obtain ⟨i, C₀, hi, hty, hr⟩ := h.toDEntN.source rfl
  have hmem : C₀ ∈ P := List.mem_of_getElem? hi
  exact hF.closure_rigid C₀ hmem I.cls hr I hI s (by rw [hty])

end TypeClass
