/-
**Coherence of the dictionary elaboration** — task `M25-TYPECLASS-COHERENCE` (partial).

On the calculus of `Start/TypeClassElab.lean`:

* `TypeClass.recProj_recMk` — **the β-law of records**: `recProj n j (recMk ds) ↠ ds[j]` for
  `n = |ds|`, `j < n` (`Lambda.reduces`);
* `TypeClass.DEnt` — **dictionary elaboration of entailment as a relation**: the dictionary built
  from a hypothesis, a superclass projection or an instance;
* `TypeClass.DEnt.typing` — every elaborated dictionary is typed at the dictionary type;
* `TypeClass.Fragment` — the coherent fragment: no superclasses, no overlapping instances (and
  instance contexts determined by the instance head), hypotheses not matched by any instance
  head, and no duplicate hypotheses;
* `TypeClass.DEnt.unique` — **in the fragment, the dictionary of a constraint is unique**; hence
  any two dictionaries for one constraint are β-convertible (`DEnt.conv`);
* `TypeClass.AElab` — elaboration of **annotated** source terms (application carries the argument
  type, method selection carries the instance type) as a relation;
* `TypeClass.AElab.coherent` — **in the fragment, any two elaborations of the same annotated
  source term are equal**, hence β-convertible (`AElab.conv`).

The remaining gap for unannotated source terms (`Sexp`) is ambiguity: a source typing judgement
does not determine the types at which methods are used (for instance when a method signature does
not mention the class variable, or inside a discarded argument), so two source derivations of one
judgement can elaborate to dictionaries at different types.
-/

import Start.TypeClassElab
import Start.Scott

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-! ### The β-law of records -/

theorem reduces_appsL {t t' : Lambda} (h : Lambda.reduces t t') :
    ∀ ts : List Lambda, Lambda.reduces (appsL t ts) (appsL t' ts)
  | [] => h
  | _ :: ts => reduces_appsL (Lambda.reduces_app_left h) ts

theorem subst_appsL (s : Lambda) (x : ℕ) :
    ∀ (h : Lambda) (ts : List Lambda),
      Lambda.subst s x (appsL h ts) = appsL (Lambda.subst s x h) (ts.map (Lambda.subst s x))
  | _, [] => rfl
  | h, u :: ts => by simp only [appsL, List.map_cons]; rw [subst_appsL s x]; rfl

theorem subst_lams (s : Lambda) (b : Lambda) :
    ∀ (k x : ℕ), Lambda.subst s x (lams k b) = lams k (Lambda.subst (Lambda.lift k 0 s) (x + k) b)
  | 0, x => by simp [lams, Lambda.lift_zero]
  | k + 1, x => by
      simp only [lams, Lambda.subst]
      rw [subst_lams (Lambda.lift 1 0 s) b k (x + 1), ← Lambda.lift_add]
      congr 3
      omega

/-- A single β-step at the head of a spine. -/
theorem reduces_appsL_beta (B t : Lambda) (ts : List Lambda) :
    Lambda.reduces (appsL (Lambda.app (Lambda.lam B) t) ts) (appsL (Lambda.subst t 0 B) ts) :=
  reduces_appsL (Lambda.reduces.step _ _ _ (Lambda.step.beta B t) (Lambda.reduces.refl _)) ts

theorem lift_succ_eq (k : ℕ) (t : Lambda) :
    Lambda.lift (k + 1) 0 t = Lambda.lift 1 k (Lambda.lift k 0 t) := by
  have h := Lambda.lift_lift t k 1 0 0 (le_refl 0)
  rw [Nat.zero_add] at h
  rw [← h, ← Lambda.lift_add]

/-- A constant function of `k` arguments returns its body. -/
theorem appsL_lams_const (t : Lambda) :
    ∀ (ts : List Lambda), Lambda.reduces (appsL (lams ts.length (Lambda.lift ts.length 0 t)) ts) t
  | [] => by simpa [lams, appsL, Lambda.lift_zero] using Lambda.reduces.refl t
  | u :: ts => by
      have h1 := reduces_appsL_beta (lams ts.length (Lambda.lift (ts.length + 1) 0 t)) u ts
      have e : Lambda.subst u 0 (lams ts.length (Lambda.lift (ts.length + 1) 0 t))
          = lams ts.length (Lambda.lift ts.length 0 t) := by
        rw [subst_lams, Nat.zero_add, lift_succ_eq, Lambda.subst_lift]
      rw [e] at h1
      show Lambda.reduces (appsL (Lambda.app (Lambda.lam
        (lams ts.length (Lambda.lift (ts.length + 1) 0 t))) u) ts) t
      exact Lambda.reduces_trans h1 (appsL_lams_const t ts)

/-- **Selection**: `(λx₁ ⋯ xₖ. xᵢ) t₁ ⋯ tₖ ↠ t_{k-1-i}` (de Bruijn index `i`). -/
theorem appsL_lams_var :
    ∀ (ts : List Lambda) (i : ℕ) (hi : i < ts.length),
      Lambda.reduces (appsL (lams ts.length (Lambda.var i)) ts) (ts[ts.length - 1 - i])
  | [], i, hi => by simp at hi
  | u :: ts, i, hi => by
      have h1 := reduces_appsL_beta (lams ts.length (Lambda.var i)) u ts
      rw [subst_lams, Nat.zero_add] at h1
      by_cases hik : i = ts.length
      · subst hik
        simp only [Lambda.subst, ite_true] at h1
        have h2 := appsL_lams_const u ts
        refine Lambda.reduces_trans h1 ?_
        simpa using h2
      · have hlt : i < ts.length := by simp at hi; omega
        have hne : ¬ i > ts.length := by omega
        simp only [Lambda.subst, hik, ite_false, hne] at h1
        refine Lambda.reduces_trans h1 ?_
        have h2 := appsL_lams_var ts i hlt
        have hidx : (u :: ts).length - 1 - i = (ts.length - 1 - i) + 1 := by simp; omega
        simp only [hidx, List.getElem_cons_succ]
        exact h2

/-- **The β-law of records**: projecting the `j`-th field of a record reduces to that field. -/
theorem recProj_recMk (ds : List Lambda) (j : ℕ) (hj : j < ds.length) :
    Lambda.reduces (recProj ds.length j (recMk ds)) (ds[j]) := by
  unfold recProj recMk
  have h1 : Lambda.reduces (Lambda.app (Lambda.lam (appsL (Lambda.var 0) (ds.map (Lambda.lift 1 0))))
      (sel ds.length j)) (appsL (sel ds.length j) ds) := by
    refine Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) ?_
    rw [subst_appsL, List.map_map]
    have : (Lambda.subst (sel ds.length j) 0 ∘ Lambda.lift 1 0) = id := by
      funext t; exact Lambda.subst_lift t _ 0
    rw [this, List.map_id]
    simpa [Lambda.subst] using Lambda.reduces.refl _
  refine Lambda.reduces_trans h1 ?_
  unfold sel
  have h2 := appsL_lams_var ds (ds.length - 1 - j) (by omega)
  have hidx : ds.length - 1 - (ds.length - 1 - j) = j := by omega
  simp only [hidx] at h2
  exact h2

/-! ### Dictionary elaboration of entailment, as a relation -/

/-- **Dictionary elaboration of entailment**: `DEnt E P n C d` says that `d` is a dictionary for
`C` built from the hypotheses `P` (the `i`-th hypothesis is the variable `n + i`), the superclass
projections and the instance dictionaries. -/
inductive DEnt (E : Env) (P : List Cstr) (n : ℕ) : Cstr → Lambda → Prop
  /-- A hypothesis. -/
  | hyp {C : Cstr} {i : ℕ} : P[i]? = some C → DEnt E P n C (Lambda.var (n + i))
  /-- A superclass projection. -/
  | sup {c d : ℕ} {τ : Mty} {D : ClassDecl} {dd : Lambda} : E.classes[c]? = some D →
      D.super = some d → DEnt E P n ⟨c, τ⟩ dd →
      DEnt E P n ⟨d, τ⟩ (recProj (dictFields (dictTy E) D τ).length 0 dd)
  /-- An instance, applied to dictionaries for its context. -/
  | inst {I : Inst} {s : ℕ → Mty} {ds : List Lambda} : I ∈ E.insts →
      ds.length = I.ctxt.length →
      (∀ (k : ℕ) (hk : k < ds.length) (hk' : k < I.ctxt.length),
        DEnt E P n ((I.ctxt[k]).subst s) (ds[k])) →
      DEnt E P n ⟨I.cls, msubst s I.head⟩ (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)

/-- Every elaborated dictionary is typed at the dictionary type of its constraint. -/
theorem DEnt.typing {E : Env} {P : List Cstr} {C : Cstr} {d : Lambda} (hE : EnvGood E)
    (Δ : List FTy) (h : DEnt E P Δ.length C d) :
    Typing (Δ ++ P.map (dictTyC E)) d (dictTyC E C) := by
  induction h with
  | @hyp C i hi =>
      refine Typing.var ?_
      rw [List.getElem?_append_right (by omega)]
      simpa [List.getElem?_map] using congrArg (Option.map (dictTyC E)) hi
  | @sup c d τ D dd hc hs _ ih =>
      have hdt : dictTyC E ⟨c, τ⟩ = recTy (dictFields (dictTy E) D τ) := dictTy_eq hE.toEnvOK hc τ
      rw [hdt] at ih
      exact typing_recProj ih (dictFields_super hs τ)
  | @inst I s ds hI hds _ ih =>
      have hdict := hE.insts_ok I hI
      have h1 := hdict.substTy (mtyS s)
      have hctx : (I.ctxt.map (dictTyC E)).map (tySubst (mtyS s))
          = I.ctxt.map (fun C => dictTyC E (C.subst s)) := by
        rw [List.map_map]
        exact List.map_congr_left fun C _ => (dictTyC_subst hE.toEnvOK s C).symm
      have hty : tySubst (mtyS s) (dictTy E I.cls I.head) = dictTyC E ⟨I.cls, msubst s I.head⟩ :=
        (dictTy_msubst hE.toEnvOK I.cls s I.head).symm
      rw [hctx, hty] at h1
      refine h1.substEnv _ _ ?_
      intro k A' hk
      rw [List.getElem?_map] at hk
      cases hC : I.ctxt[k]? with
      | none => rw [hC] at hk; cases hk
      | some C =>
          rw [hC] at hk
          simp only [Option.map_some, Option.some.injEq] at hk
          subst hk
          have hk' : k < I.ctxt.length := (List.getElem?_eq_some_iff.mp hC).1
          have hkd : k < ds.length := by rw [hds]; exact hk'
          have hCk : I.ctxt[k] = C := (List.getElem?_eq_some_iff.mp hC).2
          have := ih k hkd hk'
          rw [hCk] at this
          simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkd] using this

/-! ### The coherent fragment -/

/-- **The coherent fragment**: no superclasses; no overlapping instances, with instance contexts
determined by the instance head; no hypothesis matched by an instance head; no duplicate
hypotheses. -/
structure Fragment (E : Env) (P : List Cstr) : Prop where
  /-- No class has a superclass. -/
  no_super : ∀ (c : ℕ) (D : ClassDecl), E.classes[c]? = some D → D.super = none
  /-- No overlapping instances; the head determines the instance context. -/
  no_overlap : ∀ I ∈ E.insts, ∀ I' ∈ E.insts, ∀ s s' : ℕ → Mty, I.cls = I'.cls →
    msubst s I.head = msubst s' I'.head → I = I' ∧ ∀ C ∈ I.ctxt, C.subst s = C.subst s'
  /-- No hypothesis is an instance of an instance head. -/
  hyp_rigid : ∀ C ∈ P, ∀ I ∈ E.insts, ∀ s : ℕ → Mty, (⟨I.cls, msubst s I.head⟩ : Cstr) ≠ C
  /-- No duplicate hypotheses. -/
  nodup : P.Nodup

/-- **Uniqueness of dictionaries in the coherent fragment.** -/
theorem DEnt.unique {E : Env} {P : List Cstr} {n : ℕ} (hF : Fragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : d = d' := by
  induction h generalizing d' with
  | @hyp C i hi =>
      cases h' with
      | @hyp _ i' hi' =>
          have : i = i' := by
            have h1 := (List.getElem?_eq_some_iff.mp hi)
            have h2 := (List.getElem?_eq_some_iff.mp hi')
            exact (List.Nodup.getElem_inj_iff hF.nodup).mp (h1.2.trans h2.2.symm)
          rw [this]
      | sup hc hs _ => exact absurd (hF.no_super _ _ hc) (by rw [hs]; simp)
      | @inst I s ds hI _ =>
          exact absurd rfl (hF.hyp_rigid _ (List.mem_of_getElem? hi) I hI s)
  | sup hc hs _ _ => exact absurd (hF.no_super _ _ hc) (by rw [hs]; simp)
  | @inst I s ds hI hds _ ih =>
      generalize hC0 : (⟨I.cls, msubst s I.head⟩ : Cstr) = C0 at h'
      cases h' with
      | @hyp _ i' hi' =>
          subst hC0
          exact absurd rfl (hF.hyp_rigid _ (List.mem_of_getElem? hi') I hI s)
      | sup hc hs _ => exact absurd (hF.no_super _ _ hc) (by rw [hs]; simp)
      | @inst I' s' ds' hI' hds' hall' =>
          obtain ⟨hcls, hhead⟩ := Cstr.mk.inj hC0
          obtain ⟨rfl, hctx⟩ := hF.no_overlap I hI I' hI' s s' hcls hhead
          suffices hdd : ds = ds' by rw [hdd]
          refine List.ext_getElem (hds.trans hds'.symm) fun k hk hk' => ?_
          have hkc : k < I.ctxt.length := hds ▸ hk
          have h2 := hall' k hk' hkc
          rw [← hctx _ (List.getElem_mem hkc)] at h2
          exact ih k hk hkc h2

/-- In the coherent fragment, any two dictionaries for one constraint are β-convertible. -/
theorem DEnt.conv {E : Env} {P : List Cstr} {n : ℕ} (hF : Fragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : Lambda.Conv d d' := by
  rw [DEnt.unique hF h h']
  exact Lambda.conv_refl d'

/-! ### Elaboration of annotated source terms -/

/-- Source terms with type annotations: the argument type of an application and the instance
type of a method selection. -/
inductive ASexp where
  /-- A variable. -/
  | var : ℕ → ASexp
  /-- An abstraction. -/
  | lam : ASexp → ASexp
  /-- An application, annotated with the argument type. -/
  | app : Mty → ASexp → ASexp → ASexp
  /-- The `j`-th method of the class `c`, at the type `τ`. -/
  | method : ℕ → ℕ → Mty → ASexp

/-- **Elaboration of annotated source terms, as a relation**, with constraint context `P` and
term context `Γ`; the dictionaries of `P` sit after the term variables. -/
inductive AElab (E : Env) (P : List Cstr) : List Mty → ASexp → Mty → Lambda → Prop
  /-- A variable. -/
  | var {Γ : List Mty} {i : ℕ} {τ : Mty} : Γ[i]? = some τ → AElab E P Γ (.var i) τ (Lambda.var i)
  /-- An abstraction. -/
  | lam {Γ : List Mty} {e : ASexp} {A B : Mty} {t : Lambda} :
      AElab E P (A :: Γ) e B t → AElab E P Γ (.lam e) (.arrow A B) (Lambda.lam t)
  /-- An application. -/
  | app {Γ : List Mty} {f a : ASexp} {A B : Mty} {tf ta : Lambda} :
      AElab E P Γ f (.arrow A B) tf → AElab E P Γ a A ta →
      AElab E P Γ (.app A f a) B (Lambda.app tf ta)
  /-- A method, through the dictionary of its constraint. -/
  | method {Γ : List Mty} {c j : ℕ} {D : ClassDecl} {m τ : Mty} {d : Lambda} :
      E.classes[c]? = some D → D.methods[j]? = some m → DEnt E P Γ.length ⟨c, τ⟩ d →
      AElab E P Γ (.method c j τ) (inst0 τ m)
        (recProj (dictFields (dictTy E) D τ).length (methodIdx D j) d)

/-- Elaborations are well typed. -/
theorem AElab.typing {E : Env} {P : List Cstr} {Γ : List Mty} {e : ASexp} {τ : Mty} {t : Lambda}
    (hE : EnvGood E) (h : AElab E P Γ e τ t) : Typing (tctx E P Γ) t (mtyF τ) := by
  induction h with
  | @var Γ i τ hi =>
      refine Typing.var ?_
      have hlt : i < Γ.length := (List.getElem?_eq_some_iff.mp hi).1
      rw [tctx, List.getElem?_append_left (by simpa using hlt)]
      simpa [List.getElem?_map] using congrArg (Option.map mtyF) hi
  | lam _ ih => exact Typing.lam (by simpa [tctx] using ih)
  | app _ _ ihf iha => exact Typing.app ihf iha
  | @method Γ c j D m τ d hc hj hd =>
      have hd' := DEnt.typing hE (Γ.map mtyF) (by simpa using hd)
      have hdt : dictTyC E ⟨c, τ⟩ = recTy (dictFields (dictTy E) D τ) := dictTy_eq hE.toEnvOK hc τ
      rw [hdt] at hd'
      exact typing_recProj hd' (dictFields_method hj τ)

/-- **Coherence for annotated source terms**: in the coherent fragment, any two elaborations of
the same annotated source term, in term contexts of the same length, are equal. -/
theorem AElab.coherent {E : Env} {P : List Cstr} (hF : Fragment E P) {Γ Γ' : List Mty}
    {e : ASexp} {τ τ' : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t) (h' : AElab E P Γ' e τ' t')
    (hlen : Γ.length = Γ'.length) : t = t' := by
  induction h generalizing Γ' τ' t' with
  | var _ => cases h'; rfl
  | lam _ ih => cases h' with | lam h' => rw [ih h' (by simp [hlen])]
  | app _ _ ihf iha => cases h' with | app hf' ha' => rw [ihf hf' hlen, iha ha' hlen]
  | @method Γ c j D m τ d hc hj hd =>
      cases h' with
      | method hc' hj' hd' =>
          rw [hc] at hc'
          cases hc'
          rw [← hlen] at hd'
          rw [DEnt.unique hF hd hd']

/-- In the coherent fragment, any two elaborations of one annotated source term are
β-convertible. -/
theorem AElab.conv {E : Env} {P : List Cstr} (hF : Fragment E P) {Γ : List Mty} {e : ASexp}
    {τ : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t) (h' : AElab E P Γ e τ t') :
    Lambda.Conv t t' := by
  rw [AElab.coherent hF h h' rfl]
  exact Lambda.conv_refl t'

end TypeClass
