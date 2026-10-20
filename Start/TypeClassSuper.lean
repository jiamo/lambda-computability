/-
**Coherence: the superclass case** — task `M25-TYPECLASS-COHERENCE` (round 5).

* `Lambda.substEnv_substEnv` — composition of parallel substitutions;
* `SystemF.Typing.freeBelow` — a System F term typed in `Γ` has its free variables below `|Γ|`;
* `TypeClass.DEnt.subst` — **dictionary elaboration is stable under instantiation**: a
  dictionary elaborated from the hypotheses `Q`, with the hypotheses replaced by dictionaries for
  `Q[s]`, is a dictionary for the instantiated constraint;
* `TypeClass.SuperField` — an instance of a class with a superclass is *well formed for the
  superclass* when its dictionary is a record whose first field is a dictionary for the
  superclass at the instance head, elaborated from the instance context;
* `TypeClass.super_coherent` — **the superclass case of coherence**: the superclass projection
  of an instance dictionary (entailment through `Ent.sup` of `Ent.inst`) reduces to, hence is
  β-convertible to, a dictionary elaborated for the superclass constraint directly.
-/

import Start.TypeClassUnannotated

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-- Parallel substitution after a lifting skips the lifted index. -/
theorem substEnv_lift_skip : ∀ (t : Lambda) (j : ℕ) (w : ℕ → Lambda),
    substEnv w (Lambda.lift 1 j t) = substEnv (fun i => if i < j then w i else w (i + 1)) t := by
  intro t
  induction t with
  | var m =>
      intro j w
      by_cases h : m < j <;> simp [Lambda.lift, substEnv, h]
  | app a b iha ihb => intro j w; simp only [Lambda.lift, substEnv, iha, ihb]
  | lam t ih =>
      intro j w
      simp only [Lambda.lift, substEnv, ih]
      congr 2
      funext i
      cases i with
      | zero => simp
      | succ i => by_cases h : i < j <;> simp [h]

/-- Parallel substitution in the extended environment after a lifting. -/
theorem substEnv_envCons_lift (t : Lambda) (u : ℕ → Lambda) :
    substEnv (envCons u) (Lambda.lift 1 0 t) = Lambda.lift 1 0 (substEnv u t) := by
  rw [substEnv_lift_skip, lift_substEnv]
  rfl

/-- **Composition of parallel substitutions.** -/
theorem substEnv_substEnv : ∀ (t : Lambda) (u v : ℕ → Lambda),
    substEnv u (substEnv v t) = substEnv (fun i => substEnv u (v i)) t := by
  intro t
  induction t with
  | var m => intro u v; rfl
  | app a b iha ihb => intro u v; simp only [substEnv, iha, ihb]
  | lam t ih =>
      intro u v
      simp only [substEnv, ih]
      congr 2
      funext i
      cases i with
      | zero => rfl
      | succ i => exact substEnv_envCons_lift (v i) u

theorem freeBelow_lams : ∀ (n k : ℕ) (t : Lambda),
    freeBelow k (TypeClass.lams n t) ↔ freeBelow (k + n) t := by
  intro n
  induction n with
  | zero => intro k t; rfl
  | succ n ih =>
      intro k t
      simp only [TypeClass.lams, freeBelow]
      rw [ih]
      rw [show k + 1 + n = k + (n + 1) by omega]

/-- Selectors are closed. -/
theorem substEnv_sel (u : ℕ → Lambda) (n j : ℕ) (hj : j < n) :
    substEnv u (TypeClass.sel n j) = TypeClass.sel n j := by
  rw [substEnv_congr _ 0 u (fun k => Lambda.var k) ?_ (fun _ h => absurd h (Nat.not_lt_zero _)),
    substEnv_var_id]
  rw [TypeClass.sel, freeBelow_lams]
  simp only [freeBelow]
  omega

theorem substEnv_appsL (u : ℕ → Lambda) : ∀ (ts : List Lambda) (t : Lambda),
    substEnv u (TypeClass.appsL t ts) = TypeClass.appsL (substEnv u t) (ts.map (substEnv u)) := by
  intro ts
  induction ts with
  | nil => intro t; rfl
  | cons a ts ih => intro t; simp only [TypeClass.appsL, ih, substEnv, List.map_cons]

/-- Parallel substitution in a record. -/
theorem substEnv_recMk (u : ℕ → Lambda) (ds : List Lambda) :
    substEnv u (TypeClass.recMk ds) = TypeClass.recMk (ds.map (substEnv u)) := by
  simp only [TypeClass.recMk, substEnv, substEnv_appsL, List.map_map]
  congr 2
  refine List.map_congr_left fun d _ => ?_
  exact substEnv_envCons_lift d u

end Lambda

namespace SystemF

/-- The free variables of a typed term are below the length of its context. -/
theorem Typing.freeBelow {Γ : List FTy} {t : Lambda} {A : FTy} (h : Typing Γ t A) :
    Lambda.freeBelow Γ.length t := by
  induction h with
  | var hi => exact (List.getElem?_eq_some_iff.mp hi).1
  | app _ _ iha ihb => exact ⟨iha, ihb⟩
  | lam _ ih => simpa [Lambda.freeBelow] using ih
  | tlam _ ih => simpa using ih
  | tapp _ _ ih => exact ih

end SystemF

namespace TypeClass

open SystemF

theorem dictFields_length (rec : ℕ → Mty → FTy) (D : ClassDecl) (τ τ' : Mty) :
    (dictFields rec D τ).length = (dictFields rec D τ').length := by
  cases h : D.super <;> simp [dictFields, h]

theorem msubst_msubst (s s' : ℕ → Mty) (τ : Mty) :
    msubst s (msubst s' τ) = msubst (fun i => msubst s (s' i)) τ := by
  induction τ with
  | base => rfl
  | var i => rfl
  | arrow a b iha ihb => simp [msubst, iha, ihb]

theorem recProj_substEnv (u : ℕ → Lambda) (n j : ℕ) (hj : j < n) (d : Lambda) :
    Lambda.substEnv u (recProj n j d) = recProj n j (Lambda.substEnv u d) := by
  simp only [recProj, Lambda.substEnv, Lambda.substEnv_sel u n j hj]

/-- **Stability of dictionary elaboration under instantiation**: a dictionary elaborated from
the hypotheses `Q` becomes, once the hypotheses are replaced by dictionaries `u` for the
instantiated hypotheses `Q[s]`, a dictionary for the instantiated constraint. -/
theorem DEnt.subst {E : Env} (hE : EnvGood E) {Q P : List Cstr} {n : ℕ} {s : ℕ → Mty}
    {u : ℕ → Lambda} (hu : ∀ (i : ℕ) (C : Cstr), Q[i]? = some C → DEnt E P n (C.subst s) (u i))
    {C : Cstr} {d : Lambda} (h : DEnt E Q 0 C d) :
    DEnt E P n (C.subst s) (Lambda.substEnv u d) := by
  induction h with
  | @hyp C i hi => simpa [Lambda.substEnv] using hu i C hi
  | @sup c d' τ D dd hc hs _ ih =>
      have hlen := dictFields_length (dictTy E) D τ (msubst s τ)
      have hpos : 0 < (dictFields (dictTy E) D τ).length := by
        simp [dictFields, hs]
      rw [recProj_substEnv u _ 0 hpos, hlen]
      exact DEnt.sup hc hs ih
  | @inst I s' ds hI hds _ ih =>
      have hfree : Lambda.freeBelow I.ctxt.length I.dict := by
        simpa using (hE.insts_ok I hI).freeBelow
      have key : Lambda.substEnv u (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)
          = Lambda.substEnv (fun k => (ds.map (Lambda.substEnv u)).getD k (Lambda.var 0))
              I.dict := by
        rw [Lambda.substEnv_substEnv]
        refine Lambda.substEnv_congr _ _ _ _ hfree fun k hk => ?_
        have hk' : k < ds.length := hds ▸ hk
        simp [List.getD_eq_getElem?_getD, hk']
      rw [key]
      have hC : (⟨I.cls, msubst s' I.head⟩ : Cstr).subst s
          = ⟨I.cls, msubst (fun i => msubst s (s' i)) I.head⟩ := by
        simp [Cstr.subst, msubst_msubst]
      rw [hC]
      refine DEnt.inst hI (by simpa using hds) fun k hk hk' => ?_
      have hkd : k < ds.length := by simpa using hk
      have := ih k hkd hk'
      simp only [Cstr.subst, msubst_msubst] at this
      simpa [Cstr.subst] using this

/-- An instance is **well formed for its superclass** when, for a class with a superclass `d`,
its dictionary is a record whose first field is a dictionary for `d` at the instance head,
elaborated from the instance context. -/
def SuperField (E : Env) (I : Inst) : Prop :=
  ∀ (D : ClassDecl) (d : ℕ), E.classes[I.cls]? = some D → D.super = some d →
    ∃ sd ms, I.dict = recMk (sd :: ms) ∧
      (sd :: ms).length = (dictFields (dictTy E) D I.head).length ∧
      DEnt E I.ctxt 0 ⟨d, I.head⟩ sd

/-- **The superclass case of coherence.**  Let `I` be an instance of a class with superclass
`d`, well formed for its superclass.  The dictionary for `d` obtained by projecting the
superclass field out of an instance dictionary for `I` (entailment by `Ent.sup` of `Ent.inst`,
the first conjunct) reduces to a dictionary elaborated for `d` directly from the dictionaries of the instance
context; in particular the two are β-convertible. -/
theorem super_coherent {E : Env} (hE : EnvGood E) {P : List Cstr} {n : ℕ} {I : Inst}
    (hI : I ∈ E.insts) (hSF : SuperField E I) {D : ClassDecl} {d : ℕ}
    (hc : E.classes[I.cls]? = some D) (hs : D.super = some d) {s : ℕ → Mty} {ds : List Lambda}
    (hds : ds.length = I.ctxt.length)
    (hall : ∀ (k : ℕ) (hk : k < ds.length) (hk' : k < I.ctxt.length),
      DEnt E P n ((I.ctxt[k]).subst s) (ds[k])) :
    DEnt E P n ⟨d, msubst s I.head⟩ (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)) ∧
    ∃ dd, DEnt E P n ⟨d, msubst s I.head⟩ dd ∧
      Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)) dd ∧
      Lambda.Conv (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)) dd := by
  obtain ⟨sd, ms, hdict, hlen, hsd⟩ := hSF D d hc hs
  have hsub : DEnt E P n (Cstr.subst s ⟨d, I.head⟩)
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) := by
    refine DEnt.subst hE (fun i C hi => ?_) hsd
    have hi' : i < I.ctxt.length := (List.getElem?_eq_some_iff.mp hi).1
    have hCi : I.ctxt[i] = C := (List.getElem?_eq_some_iff.mp hi).2
    have hid : i < ds.length := hds ▸ hi'
    have := hall i hid hi'
    rw [hCi] at this
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hid] using this
  have hred : Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict))
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) := by
    rw [hdict, Lambda.substEnv_recMk, ← dictFields_length (dictTy E) D I.head, ← hlen]
    have := recProj_recMk ((sd :: ms).map (Lambda.substEnv fun k => ds.getD k (Lambda.var 0))) 0
      (by simp)
    simpa using this
  exact ⟨DEnt.sup hc hs (DEnt.inst hI hds hall), _, hsub, hred, _, hred,
    Lambda.reduces.refl _⟩

end TypeClass
