/-
**Normalization of dictionary derivations with superclasses** — task `M25-TYPECLASS-SUPER-INST`
(round 9, part E), continuing `Start/TypeClassSuperNorm.lean`.

* `Lambda.substEnv_reduces` — **the congruence of β-reduction for parallel substitution**:
  `Lambda.reduces (Lambda.substEnv u t) (Lambda.substEnv u' t)` when `u k` reduces to `u' k` for
  every variable `k` (and `Lambda.substEnv_reduces_below`, for the free variables of `t` only);
* `TypeClass.DEntN.true_inv` — inversion: a normal derivation whose root is an instance is an
  instance application;
* `TypeClass.DEnt.normalize_super` — **every dictionary derivation reduces to a normal one**
  (no superclass projection of an instance dictionary), in an environment satisfying
  `NormalSuperFields`;
* `TypeClass.SuperInstFragment` — the round-6 `SuperFragment` without the restriction that
  instances are declared only for classes without a superclass;
* `TypeClass.DEntN.unique` — uniqueness of normal dictionaries in that fragment;
* `TypeClass.DEnt.conv_superInst`, `TypeClass.AElab.conv_superInst` and
  `TypeClass.coherence_unannotated_superInst` — **coherence up to β for unambiguous judgements
  in environments with instances of subclasses**, under `NormalSuperFields`.

Not proved: coherence under the weaker well-formedness `SuperField` alone (superclass fields that
are arbitrary, not closed normal, derivations); see `docs/goal/evidence/M25-TYPECLASS-COHERENCE.md`.
-/

import Start.TypeClassSuperNorm

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ### Congruence of reduction for parallel substitution -/

/-- **Congruence of β-reduction for parallel substitution**, for the free variables of `t`. -/
theorem Lambda.substEnv_reduces_below : ∀ (t : Lambda) (k : ℕ) (u u' : ℕ → Lambda),
    Lambda.freeBelow k t → (∀ j, j < k → Lambda.reduces (u j) (u' j)) →
    Lambda.reduces (Lambda.substEnv u t) (Lambda.substEnv u' t) := by
  intro t
  induction t with
  | var n => intro k u u' h huu; exact huu n h
  | app a b iha ihb =>
      intro k u u' h huu
      exact Lambda.reduces_app (iha k u u' h.1 huu) (ihb k u u' h.2 huu)
  | lam t ih =>
      intro k u u' h huu
      refine Lambda.reduces_lam (ih (k + 1) (Lambda.envCons u) (Lambda.envCons u') h ?_)
      intro j hj
      cases j with
      | zero => exact Lambda.reduces.refl _
      | succ j => exact Lambda.reduces_lift (huu j (by omega)) 1 0

/-- **Congruence of β-reduction for parallel substitution.** -/
theorem Lambda.substEnv_reduces : ∀ (t : Lambda) (u u' : ℕ → Lambda),
    (∀ j, Lambda.reduces (u j) (u' j)) →
    Lambda.reduces (Lambda.substEnv u t) (Lambda.substEnv u' t) := by
  intro t
  induction t with
  | var n => intro u u' huu; exact huu n
  | app a b iha ihb =>
      intro u u' huu
      exact Lambda.reduces_app (iha u u' huu) (ihb u u' huu)
  | lam t ih =>
      intro u u' huu
      refine Lambda.reduces_lam (ih (Lambda.envCons u) (Lambda.envCons u') ?_)
      intro j
      cases j with
      | zero => exact Lambda.reduces.refl _
      | succ j => exact Lambda.reduces_lift (huu j) 1 0

namespace TypeClass

open SystemF

/-- Inversion: a normal derivation whose root is an instance is an instance application. -/
theorem DEntN.true_inv {E : Env} {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda}
    (h : DEntN E P n true C d) :
    ∃ (I : Inst) (s : ℕ → Mty) (ds : List Lambda), I ∈ E.insts ∧
      C = ⟨I.cls, msubst s I.head⟩ ∧
      d = Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict := by
  generalize hb : true = b at h
  cases h with
  | hyp => cases hb
  | sup => cases hb
  | @inst I s ds bs hI _ _ => exact ⟨I, s, ds, hI, rfl, rfl⟩

theorem reduces_recProj {n j : ℕ} {d d' : Lambda} (h : Lambda.reduces d d') :
    Lambda.reduces (recProj n j d) (recProj n j d') :=
  Lambda.reduces_app h (Lambda.reduces.refl _)

/-- **Normalization of dictionary derivations with superclasses**: under `NormalSuperFields`,
every dictionary derivation reduces to a normal one, with no superclass projection of an
instance dictionary. -/
theorem DEnt.normalize_super {E : Env} (hE : EnvGood E) (hN : NormalSuperFields E)
    {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda} (h : DEnt E P n C d) :
    ∃ b d', DEntN E P n b C d' ∧ Lambda.reduces d d' := by
  induction h with
  | hyp hi => exact ⟨false, _, .hyp hi, Lambda.reduces.refl _⟩
  | @sup c d₀ τ D dd hc hs _ ih =>
      obtain ⟨b, d', hd', hr⟩ := ih
      cases b with
      | false => exact ⟨false, _, .sup hc hs hd', reduces_recProj hr⟩
      | true =>
          obtain ⟨I, s, ds, hI, hC, rfl⟩ := hd'.true_inv
          simp only [Cstr.mk.injEq] at hC
          obtain ⟨rfl, rfl⟩ := hC
          obtain ⟨b', d'', hd'', hr'⟩ := DEntN.supInst_contract hE hN hI hc hs s ds
          exact ⟨b', d'', hd'', Lambda.reduces_trans (reduces_recProj hr) hr'⟩
  | @inst I s ds hI hlen _ ih =>
      classical
      have hex : ∀ k : Fin ds.length, ∃ b d', DEntN E P n b ((I.ctxt[k.1]'(hlen ▸ k.2)).subst s)
          d' ∧ Lambda.reduces (ds[k.1]) d' := fun k => ih k.1 k.2 (hlen ▸ k.2)
      choose bf df hdf hrf using hex
      let ds' : List Lambda := List.ofFn df
      let bs : ℕ → Bool := fun k => if hk : k < ds.length then bf ⟨k, hk⟩ else false
      have hlen' : ds'.length = I.ctxt.length := by simp [ds', hlen]
      refine ⟨true, _, DEntN.inst (ds := ds') bs hI hlen' fun k hk hk' => ?_, ?_⟩
      · have hk0 : k < ds.length := by simpa [ds'] using hk
        have := hdf ⟨k, hk0⟩
        simpa [ds', bs, hk0] using this
      · refine Lambda.substEnv_reduces _ _ _ fun j => ?_
        by_cases hj : j < ds.length
        · have h1 : ds.getD j (Lambda.var 0) = ds[j] := by simp [hj]
          have h2 : ds'.getD j (Lambda.var 0) = df ⟨j, hj⟩ := by simp [ds', hj]
          rw [h1, h2]
          exact hrf ⟨j, hj⟩
        · have h1 : ds.getD j (Lambda.var 0) = Lambda.var 0 := by simp [hj]
          have h2 : ds'.getD j (Lambda.var 0) = Lambda.var 0 := by simp [ds', hj]
          rw [h1, h2]
          exact Lambda.reduces.refl _

/-! ### Coherence with instances of classes that have a superclass -/

/-- **The fragment with superclasses and instances of subclasses**: `SuperFragment` without the
restriction that instances are declared only for classes without a superclass. -/
structure SuperInstFragment (E : Env) (P : List Cstr) : Prop where
  /-- Superclasses come earlier. -/
  env_ok : EnvOK E
  /-- No overlapping instances; the head determines the instance context. -/
  no_overlap : ∀ I ∈ E.insts, ∀ I' ∈ E.insts, ∀ s s' : ℕ → Mty, I.cls = I'.cls →
    msubst s I.head = msubst s' I'.head → I = I' ∧ ∀ C ∈ I.ctxt, C.subst s = C.subst s'
  /-- No superclass of a hypothesis is an instance of an instance head. -/
  closure_rigid : ∀ C ∈ P, ∀ c, SupReach E C.cls c → ∀ I ∈ E.insts, ∀ s : ℕ → Mty,
    (⟨I.cls, msubst s I.head⟩ : Cstr) ≠ ⟨c, C.ty⟩
  /-- The superclass closures of distinct hypotheses are disjoint. -/
  closure_unique : ∀ (i j : ℕ) (Ci Cj : Cstr) (c : ℕ), P[i]? = some Ci → P[j]? = some Cj →
    Ci.ty = Cj.ty → SupReach E Ci.cls c → SupReach E Cj.cls c → i = j

/-- `SuperFragment` is a special case. -/
theorem SuperFragment.toSuperInst {E : Env} {P : List Cstr} (h : SuperFragment E P) :
    SuperInstFragment E P :=
  ⟨h.env_ok, h.no_overlap, h.closure_rigid, h.closure_unique⟩

/-- In `SuperFragment` (instances only for classes without a superclass) `NormalSuperFields`
holds vacuously, so the coherence below extends the round-6 coherence. -/
theorem SuperFragment.normalSuperFields {E : Env} {P : List Cstr} (h : SuperFragment E P) :
    NormalSuperFields E := by
  intro I hI D d hc hs
  have := h.inst_no_super I hI D hc
  rw [hs] at this
  cases this

/-- A normal derivation whose root is not an instance comes from a hypothesis, through
superclass projections. -/
theorem DEntN.source {E : Env} {P : List Cstr} {n : ℕ} {b : Bool} {C : Cstr} {d : Lambda}
    (h : DEntN E P n b C d) : b = false →
      ∃ (i : ℕ) (C₀ : Cstr), P[i]? = some C₀ ∧ C₀.ty = C.ty ∧ SupReach E C₀.cls C.cls := by
  induction h with
  | @hyp C i hi => intro _; exact ⟨i, C, hi, rfl, .refl⟩
  | @sup c d τ D dd hc hs _ ih =>
      intro _
      obtain ⟨i, C₀, hi, hty, hr⟩ := ih rfl
      exact ⟨i, C₀, hi, hty, hr.tail ⟨D, hc, hs⟩⟩
  | inst => intro h; cases h

/-- **Uniqueness of normal dictionaries** in the fragment with instances of subclasses. -/
theorem DEntN.unique {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperInstFragment E P)
    {b b' : Bool} {C : Cstr} {d d' : Lambda} (h : DEntN E P n b C d)
    (h' : DEntN E P n b' C d') : d = d' := by
  induction h generalizing b' d' with
  | @hyp C i hi =>
      cases h' with
      | @hyp _ i' hi' =>
          rw [hF.closure_unique i i' C C C.cls hi hi' rfl .refl .refl]
      | @sup c _ τ D dd hc hs h₀ =>
          obtain ⟨j, C₀, hj, hty, hr⟩ := h₀.source rfl
          have hr' : SupReach E C₀.cls _ := hr.tail ⟨D, hc, hs⟩
          have hij := hF.closure_unique j i C₀ ⟨_, τ⟩ _ hj hi hty hr' .refl
          subst hij
          rw [hj] at hi
          cases hi
          have h1 := hr.le hF.env_ok
          have h2 := SupStep.lt hF.env_ok ⟨D, hc, hs⟩
          simp only at h1 h2
          omega
      | @inst I s ds _ hI _ =>
          exact absurd rfl (hF.closure_rigid _ (List.mem_of_getElem? hi) _ .refl I hI s)
  | @sup c d τ D dd hc hs h₀ ih =>
      generalize hC0 : (⟨d, τ⟩ : Cstr) = C0 at h'
      cases h' with
      | @hyp _ i hi =>
          subst hC0
          obtain ⟨j, C₀, hj, hty, hr⟩ := h₀.source rfl
          have hr' : SupReach E C₀.cls d := hr.tail ⟨D, hc, hs⟩
          have hij := hF.closure_unique j i C₀ ⟨d, τ⟩ d hj hi hty hr' .refl
          subst hij
          rw [hj] at hi
          cases hi
          have h1 := hr.le hF.env_ok
          have h2 := SupStep.lt hF.env_ok ⟨D, hc, hs⟩
          simp only at h1 h2
          omega
      | @sup c' _ τ' D' dd' hc' hs' h₀' =>
          obtain ⟨rfl, rfl⟩ := Cstr.mk.inj hC0
          obtain ⟨j, C₀, hj, hty, hr⟩ := h₀.source rfl
          obtain ⟨j', C₀', hj', hty', hr'⟩ := h₀'.source rfl
          have hjj := hF.closure_unique j j' C₀ C₀' d hj hj' (hty.trans hty'.symm)
            (hr.tail ⟨D, hc, hs⟩) (hr'.tail ⟨D', hc', hs'⟩)
          subst hjj
          rw [hj] at hj'
          cases hj'
          have hcc : c = c' := by
            rcases SupReach.total hr hr' with h | h
            · rcases Relation.ReflTransGen.cases_head h with h | ⟨x, hx, hxc⟩
              · exact h
              · have := SupStep.det hx ⟨D, hc, hs⟩
                subst this
                have h1 := SupReach.le hF.env_ok hxc
                have h2 := SupStep.lt hF.env_ok ⟨D', hc', hs'⟩
                simp only at h1 h2
                omega
            · rcases Relation.ReflTransGen.cases_head h with h | ⟨x, hx, hxc⟩
              · exact h.symm
              · have := SupStep.det hx ⟨D', hc', hs'⟩
                subst this
                have h1 := SupReach.le hF.env_ok hxc
                have h2 := SupStep.lt hF.env_ok ⟨D, hc, hs⟩
                simp only at h1 h2
                omega
          subst hcc
          rw [hc] at hc'
          cases hc'
          rw [ih h₀']
      | @inst I s ds _ hI _ =>
          obtain ⟨j, C₀, hj, hty, hr⟩ := h₀.source rfl
          exact (hF.closure_rigid _ (List.mem_of_getElem? hj) _ (hr.tail ⟨D, hc, hs⟩) I hI s
            (by rw [← hC0]; simp only at hty; rw [hty])).elim
  | @inst I s ds bs hI hds _ ih =>
      generalize hC0 : (⟨I.cls, msubst s I.head⟩ : Cstr) = C0 at h'
      cases h' with
      | @hyp _ i' hi' =>
          subst hC0
          exact absurd rfl (hF.closure_rigid _ (List.mem_of_getElem? hi') _ .refl I hI s)
      | @sup c _ τ D dd hc hs h₀ =>
          obtain ⟨j, C₀, hj, hty, hr⟩ := h₀.source rfl
          exact (hF.closure_rigid _ (List.mem_of_getElem? hj) _ (hr.tail ⟨D, hc, hs⟩) I hI s
            (by rw [hC0]; simp only at hty; rw [hty])).elim
      | @inst I' s' ds' bs' hI' hds' hall' =>
          obtain ⟨hcls, hhead⟩ := Cstr.mk.inj hC0
          obtain ⟨rfl, hctx⟩ := hF.no_overlap I hI I' hI' s s' hcls hhead
          suffices hdd : ds = ds' by rw [hdd]
          refine List.ext_getElem (hds.trans hds'.symm) fun k hk hk' => ?_
          have hkc : k < I.ctxt.length := hds ▸ hk
          have h2 := hall' k hk' hkc
          rw [← hctx _ (List.getElem_mem hkc)] at h2
          exact ih k hk hkc h2

/-- **Coherence of dictionaries with instances of subclasses**: in the fragment, under
`NormalSuperFields`, any two dictionaries for one constraint are β-convertible. -/
theorem DEnt.conv_superInst {E : Env} {P : List Cstr} {n : ℕ} (hE : EnvGood E)
    (hN : NormalSuperFields E) (hF : SuperInstFragment E P) {C : Cstr} {d d' : Lambda}
    (h : DEnt E P n C d) (h' : DEnt E P n C d') : Lambda.Conv d d' := by
  obtain ⟨b, e, he, hr⟩ := DEnt.normalize_super hE hN h
  obtain ⟨b', e', he', hr'⟩ := DEnt.normalize_super hE hN h'
  rw [DEntN.unique hF he he'] at hr
  exact ⟨e', hr, hr'⟩

/-- **Coherence of annotated elaboration up to β** with instances of subclasses. -/
theorem AElab.conv_superInst {E : Env} {P : List Cstr} (hE : EnvGood E)
    (hN : NormalSuperFields E) (hF : SuperInstFragment E P)
    {Γ Γ' : List Mty} {e : ASexp} {τ τ' : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t)
    (h' : AElab E P Γ' e τ' t') (hlen : Γ.length = Γ'.length) : Lambda.Conv t t' := by
  induction h generalizing Γ' τ' t' with
  | var _ => cases h'; exact Lambda.conv_refl _
  | lam _ ih =>
      cases h' with
      | lam h' =>
          obtain ⟨u, h1, h2⟩ := ih h' (by simp [hlen])
          exact ⟨Lambda.lam u, Lambda.reduces_lam h1, Lambda.reduces_lam h2⟩
  | app _ _ ihf iha =>
      cases h' with
      | app hf' ha' =>
          obtain ⟨u, h1, h2⟩ := ihf hf' hlen
          obtain ⟨v, h3, h4⟩ := iha ha' hlen
          exact ⟨Lambda.app u v, Lambda.reduces_app h1 h3, Lambda.reduces_app h2 h4⟩
  | @method Γ c j D m τ d hc hj hd =>
      cases h' with
      | method hc' hj' hd' =>
          rw [hc] at hc'
          cases hc'
          rw [← hlen] at hd'
          obtain ⟨u, h1, h2⟩ := DEnt.conv_superInst hE hN hF hd hd'
          exact ⟨_, reduces_recProj h1, reduces_recProj h2⟩

/-- **Coherence for unambiguous judgements with instances of subclasses**: in the fragment,
under `NormalSuperFields`, an unambiguous derivable judgement has an elaboration, and any two
elaborations are β-convertible. -/
theorem coherence_unannotated_superInst {E : Env} {P : List Cstr} (hE : EnvGood E)
    (hN : NormalSuperFields E) (hF : SuperInstFragment E P)
    {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) (hS : STyping E P Γ e τ) :
    (∃ t, ElabS E P Γ e τ t) ∧
      ∀ t t', ElabS E P Γ e τ t → ElabS E P Γ e τ t' → Lambda.Conv t t' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, t, he, ha⟩ := hS.annotate
    exact ⟨t, a, he, ha⟩
  · rintro t t' ⟨a, he, ha⟩ ⟨a', he', ha'⟩
    obtain ⟨rfl, _⟩ := hB.annot_unique he he' ha ha' (fun _ => ⟨rfl, rfl⟩)
    exact AElab.conv_superInst hE hN hF ha ha' rfl

end TypeClass
