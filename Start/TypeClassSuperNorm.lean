/-
**Normal dictionary derivations and superclass instances** — task `M25-TYPECLASS-SUPER-INST`
(round 8, part E).

* `TypeClass.DEntN E P n b C d` — **normal dictionary derivations**: the `DEnt` rules where a
  superclass projection is never applied to an instance dictionary; the flag `b` records whether
  the root is an instance;
* `TypeClass.DEntN.toDEnt` — normal derivations are derivations;
* `TypeClass.NormalSuperFields E` — **the termination condition on the environment**: every
  instance of a class with a superclass carries its superclass field as a *closed normal*
  derivation (from no hypotheses, with no superclass projection of an instance dictionary);
* `TypeClass.NormalSuperFields.superField` — the condition implies the round-5 well-formedness
  `SuperField`;
* `TypeClass.DEntN.supInst_contract` — **the contraction of a superclass projection of a
  normal instance dictionary**: under `NormalSuperFields` it reduces to the type instance of the
  closed normal superclass field, itself a normal derivation (`DEntN.subst_closed`), so no new
  redex is created.

Open: `DEnt.normalize_super` itself.  Under `NormalSuperFields` the remaining step is the
instance case, where the dictionaries of the instance context are normalized and the instance
dictionary must reduce accordingly: the first missing lemma is the congruence of β-reduction for
parallel substitution, `Lambda.reduces (Lambda.substEnv u t) (Lambda.substEnv u' t)` when
`u k` reduces to `u' k` for every free variable `k` of `t`.  Without the closedness of the
superclass fields, substitution of instance dictionaries for hypotheses under a superclass
projection creates new redexes, and the termination order must combine Paterson's measure on
instance contexts with the size of instance dictionaries.
-/

import Start.TypeClassSuperCoh

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-- **Normal dictionary derivations**: no superclass projection of an instance dictionary.  The
flag records whether the root is an instance. -/
inductive DEntN (E : Env) (P : List Cstr) (n : ℕ) : Bool → Cstr → Lambda → Prop
  | hyp {C : Cstr} {i : ℕ} : P[i]? = some C → DEntN E P n false C (Lambda.var (n + i))
  | sup {c d : ℕ} {τ : Mty} {D : ClassDecl} {dd : Lambda} : E.classes[c]? = some D →
      D.super = some d → DEntN E P n false ⟨c, τ⟩ dd →
      DEntN E P n false ⟨d, τ⟩ (recProj (dictFields (dictTy E) D τ).length 0 dd)
  | inst {I : Inst} {s : ℕ → Mty} {ds : List Lambda} (bs : ℕ → Bool) : I ∈ E.insts →
      ds.length = I.ctxt.length →
      (∀ (k : ℕ) (hk : k < ds.length) (hk' : k < I.ctxt.length),
        DEntN E P n (bs k) ((I.ctxt[k]).subst s) (ds[k])) →
      DEntN E P n true ⟨I.cls, msubst s I.head⟩
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)

/-- Normal derivations are derivations. -/
theorem DEntN.toDEnt {E : Env} {P : List Cstr} {n : ℕ} {b : Bool} {C : Cstr} {d : Lambda}
    (h : DEntN E P n b C d) : DEnt E P n C d := by
  induction h with
  | hyp hi => exact .hyp hi
  | sup hc hs _ ih => exact .sup hc hs ih
  | inst bs hI hds _ ih => exact .inst hI hds fun k hk hk' => ih k hk hk'

/-- **Type instances of closed normal derivations are closed normal derivations**, with the
same dictionary term (no hypothesis is substituted, and dictionary terms do not mention types). -/
theorem DEntN.subst_closed {E : Env} {b : Bool} {C : Cstr} {d : Lambda} (s : ℕ → Mty)
    (h : DEntN E [] 0 b C d) (P : List Cstr) (n : ℕ) : DEntN E P n b (C.subst s) d := by
  induction h with
  | hyp hi => simp at hi
  | @sup c d' τ D dd hc hs _ ih =>
      have hlen := dictFields_length (dictTy E) D τ (msubst s τ)
      rw [hlen]
      exact DEntN.sup hc hs ih
  | @inst I s' ds bs hI hds _ ih =>
      have hC : (⟨I.cls, msubst s' I.head⟩ : Cstr).subst s
          = ⟨I.cls, msubst (fun i => msubst s (s' i)) I.head⟩ := by
        simp [Cstr.subst, msubst_msubst]
      rw [hC]
      refine DEntN.inst bs hI hds fun k hk hk' => ?_
      have := ih k hk hk'
      simp only [Cstr.subst, msubst_msubst] at this
      simpa [Cstr.subst] using this

/-- **The termination condition on the environment**: every instance of a class with a
superclass stores its superclass field as a closed normal derivation. -/
def NormalSuperFields (E : Env) : Prop :=
  ∀ I ∈ E.insts, ∀ (D : ClassDecl) (d : ℕ), E.classes[I.cls]? = some D → D.super = some d →
    ∃ sd ms, I.dict = recMk (sd :: ms) ∧
      (sd :: ms).length = (dictFields (dictTy E) D I.head).length ∧
      ∃ b, DEntN E [] 0 b ⟨d, I.head⟩ sd

/-- Normal derivations from no hypotheses, transported to any hypotheses (the dictionary term
does not mention hypotheses). -/
theorem DEntN.weaken_nil {E : Env} {b : Bool} {C : Cstr} {d : Lambda}
    (h : DEntN E [] 0 b C d) (P : List Cstr) (n : ℕ) : DEntN E P n b C d := by
  induction h with
  | hyp hi => simp at hi
  | sup hc hs _ ih => exact .sup hc hs ih
  | inst bs hI hds _ ih => exact .inst bs hI hds fun k hk hk' => ih k hk hk'

/-- `NormalSuperFields` implies the round-5 well-formedness `SuperField` of every instance. -/
theorem NormalSuperFields.superField {E : Env} (h : NormalSuperFields E) {I : Inst}
    (hI : I ∈ E.insts) : SuperField E I := by
  intro D d hc hs
  obtain ⟨sd, ms, hdict, hlen, b, hsd⟩ := h I hI D d hc hs
  exact ⟨sd, ms, hdict, hlen, (hsd.weaken_nil I.ctxt 0).toDEnt⟩

/-- The dictionary term of a closed derivation is closed. -/
theorem DEnt.substEnv_closed {E : Env} (hE : EnvGood E) {C : Cstr} {d : Lambda}
    (h : DEnt E [] 0 C d) (u : ℕ → Lambda) : Lambda.substEnv u d = d := by
  have ht := DEnt.typing hE [] h
  have hf : Lambda.freeBelow 0 d := by simpa using ht.freeBelow
  rw [Lambda.substEnv_congr _ 0 u (fun k => Lambda.var k) hf
    (fun _ h => absurd h (Nat.not_lt_zero _)), Lambda.substEnv_var_id]

/-- **Contraction of a superclass projection of an instance dictionary under
`NormalSuperFields`**: the projection reduces to a *normal* derivation of the superclass
constraint (the type instance of the closed normal superclass field), whatever the dictionaries
`ds` of the instance context. -/
theorem DEntN.supInst_contract {E : Env} (hE : EnvGood E) (hN : NormalSuperFields E)
    {P : List Cstr} {n : ℕ} {I : Inst} (hI : I ∈ E.insts) {D : ClassDecl} {d : ℕ}
    (hc : E.classes[I.cls]? = some D) (hs : D.super = some d) (s : ℕ → Mty) (ds : List Lambda) :
    ∃ b d', DEntN E P n b ⟨d, msubst s I.head⟩ d' ∧
      Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)) d' := by
  obtain ⟨sd, ms, hdict, hlen, b, hsd⟩ := hN I hI D d hc hs
  have hred' : Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict))
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) := by
    rw [hdict, Lambda.substEnv_recMk, ← dictFields_length (dictTy E) D I.head, ← hlen]
    have := recProj_recMk ((sd :: ms).map (Lambda.substEnv fun k => ds.getD k (Lambda.var 0))) 0
      (by simp)
    simpa using this
  rw [DEnt.substEnv_closed hE hsd.toDEnt] at hred'
  exact ⟨b, sd, by simpa [Cstr.subst] using hsd.subst_closed s P n, hred'⟩

end TypeClass
