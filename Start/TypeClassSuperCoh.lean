/-
**Coherence with superclasses** — task `M25-TYPECLASS-COHERENCE-SUPER` (round 6, part E).

The lemma named as first missing in round 5,
`DEnt.conv_super : SuperFragment E P → DEnt E P n C d → DEnt E P n C d' → Lambda.Conv d d'`,
needs a condition on the *hypotheses* that the round-5 statement did not carry: two hypotheses
whose superclass closures meet give two dictionaries for the meeting point.

* `TypeClass.SupStep`, `TypeClass.SupReach` — the superclass relation on classes and its
  reflexive-transitive closure (a functional, strictly decreasing relation under `EnvOK`);
* `TypeClass.superClosure_not_coherent` — **the hypothesis condition is needed**: with classes
  `Eq`, `Ord <: Eq`, `Num <: Eq`, no instances, and hypotheses `Ord α, Num α`, the constraint
  `Eq α` has two dictionaries (through `Ord α` and through `Num α`) that are distinct normal forms,
  hence not β-convertible;
* `TypeClass.SuperFragment` — the fragment with superclasses: no overlap, instances only for
  classes without a superclass, the superclass closures of the hypotheses are disjoint and avoid
  instance heads;
* `TypeClass.DEnt.unique_super` — **uniqueness of dictionaries with superclasses**, hence
  `TypeClass.DEnt.conv_super` (β-convertibility);
* `TypeClass.AElab.coherent_super`, `TypeClass.coherence_unannotated_super`,
  `TypeClass.coherence_unannotated_super_conv` — **coherence for unambiguous judgements in the
  fragment with superclasses**.

Not covered: instances of classes that have a superclass (the `sup`-of-`inst` case of
`super_coherent`).  There the second dictionary is obtained by substituting the instance's
superclass field, which is not a sub-derivation; the next missing lemma is a normalisation of
dictionary derivations removing `sup`-of-`inst` (it needs a termination order on instance
contexts, e.g. Paterson's conditions, which `EnvGood` does not impose).
-/

import Start.TypeClassSuper

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-! ### The superclass relation -/

/-- `d` is the superclass of `c`. -/
def SupStep (E : Env) (c d : ℕ) : Prop := ∃ D, E.classes[c]? = some D ∧ D.super = some d

/-- The reflexive-transitive closure of the superclass relation. -/
def SupReach (E : Env) : ℕ → ℕ → Prop := Relation.ReflTransGen (SupStep E)

theorem SupStep.det {E : Env} {c d₁ d₂ : ℕ} (h₁ : SupStep E c d₁) (h₂ : SupStep E c d₂) :
    d₁ = d₂ := by
  obtain ⟨D, hD, hs⟩ := h₁
  obtain ⟨D', hD', hs'⟩ := h₂
  rw [hD] at hD'
  cases hD'
  rw [hs] at hs'
  cases hs'
  rfl

theorem SupStep.lt {E : Env} (hE : EnvOK E) {c d : ℕ} (h : SupStep E c d) : d < c :=
  let ⟨_, hD, hs⟩ := h
  hE.super_lt hD hs

theorem SupReach.le {E : Env} (hE : EnvOK E) {a b : ℕ} (h : SupReach E a b) : b ≤ a := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans (le_of_lt (hs.lt hE)) ih

/-- Two classes reachable from one class are comparable (the relation is functional). -/
theorem SupReach.total {E : Env} {x a b : ℕ} (ha : SupReach E x a) (hb : SupReach E x b) :
    SupReach E a b ∨ SupReach E b a := by
  induction ha with
  | refl => exact Or.inl hb
  | @tail a' a _ hs ih =>
      rcases ih with h | h
      · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, hc, hcb⟩
        · exact Or.inr (Relation.ReflTransGen.single hs)
        · rw [hs.det hc]
          exact Or.inl hcb
      · exact Or.inr (h.tail hs)

/-! ### The hypothesis condition is needed -/

/-- `Eq` (class `0`), `Ord <: Eq` (class `1`), `Num <: Eq` (class `2`), no methods, no
instances. -/
def supEnv : Env := ⟨[⟨none, []⟩, ⟨some 0, []⟩, ⟨some 0, []⟩], []⟩

/-- The hypotheses `Ord α, Num α`. -/
def supHyps : List Cstr := [⟨1, .var 0⟩, ⟨2, .var 0⟩]

theorem supEnv_ok : EnvGood supEnv where
  super_lt := by
    intro c D hc d hs
    match c, hc with
    | 0, hc => simp [supEnv] at hc; subst hc; simp at hs
    | 1, hc => simp [supEnv] at hc; subst hc; simp at hs; omega
    | 2, hc => simp [supEnv] at hc; subst hc; simp at hs; omega
    | n + 3, hc => simp [supEnv] at hc
  methods_mono := by
    intro c D hc m hm
    match c, hc with
    | 0, hc => simp [supEnv] at hc; subst hc; simp at hm
    | 1, hc => simp [supEnv] at hc; subst hc; simp at hm
    | 2, hc => simp [supEnv] at hc; subst hc; simp at hm
    | n + 3, hc => simp [supEnv] at hc
  insts_ok := by simp [supEnv]

theorem app_var_id_normal (i : ℕ) :
    Lambda.is_normal (Lambda.app (Lambda.var i) (Lambda.lam (Lambda.var 0))) := by
  intro t h
  cases h with
  | app_left _ _ _ h => cases h
  | app_right _ _ _ h =>
      cases h with
      | lam _ _ h => cases h

/-- **The hypothesis condition is needed.**  In a well-formed environment with superclasses and
no instances, under the hypotheses `Ord α, Num α`, the constraint `Eq α` has two dictionaries that
are not β-convertible. -/
theorem superClosure_not_coherent : EnvGood supEnv ∧
    ∃ d d', DEnt supEnv supHyps 0 ⟨0, .var 0⟩ d ∧ DEnt supEnv supHyps 0 ⟨0, .var 0⟩ d' ∧
      ¬ Lambda.Conv d d' := by
  refine ⟨supEnv_ok, _, _,
    DEnt.sup (c := 1) (D := ⟨some 0, []⟩) (by simp [supEnv]) rfl
      (DEnt.hyp (i := 0) (by simp [supHyps])),
    DEnt.sup (c := 2) (D := ⟨some 0, []⟩) (by simp [supEnv]) rfl
      (DEnt.hyp (i := 1) (by simp [supHyps])), ?_⟩
  rintro ⟨v, hv1, hv2⟩
  have n1 := app_var_id_normal 0
  have n2 := app_var_id_normal 1
  have e1 : recProj (dictFields (dictTy supEnv) ⟨some 0, []⟩ (.var 0)).length 0
      (Lambda.var (0 + 0)) = Lambda.app (Lambda.var 0) (Lambda.lam (Lambda.var 0)) := by
    simp [recProj, dictFields, sel, lams]
  have e2 : recProj (dictFields (dictTy supEnv) ⟨some 0, []⟩ (.var 0)).length 0
      (Lambda.var (0 + 1)) = Lambda.app (Lambda.var 1) (Lambda.lam (Lambda.var 0)) := by
    simp [recProj, dictFields, sel, lams]
  rw [e1] at hv1
  rw [e2] at hv2
  have := (Lambda.reduces_normal_eq n1 hv1).trans (Lambda.reduces_normal_eq n2 hv2).symm
  simp at this

/-! ### The fragment with superclasses -/

/-- **The coherent fragment with superclasses.** -/
structure SuperFragment (E : Env) (P : List Cstr) : Prop where
  /-- Superclasses come earlier. -/
  env_ok : EnvOK E
  /-- Instances are declared only for classes without a superclass. -/
  inst_no_super : ∀ I ∈ E.insts, ∀ D : ClassDecl, E.classes[I.cls]? = some D → D.super = none
  /-- No overlapping instances; the head determines the instance context. -/
  no_overlap : ∀ I ∈ E.insts, ∀ I' ∈ E.insts, ∀ s s' : ℕ → Mty, I.cls = I'.cls →
    msubst s I.head = msubst s' I'.head → I = I' ∧ ∀ C ∈ I.ctxt, C.subst s = C.subst s'
  /-- No superclass of a hypothesis is an instance of an instance head. -/
  closure_rigid : ∀ C ∈ P, ∀ c, SupReach E C.cls c → ∀ I ∈ E.insts, ∀ s : ℕ → Mty,
    (⟨I.cls, msubst s I.head⟩ : Cstr) ≠ ⟨c, C.ty⟩
  /-- The superclass closures of distinct hypotheses are disjoint. -/
  closure_unique : ∀ (i j : ℕ) (Ci Cj : Cstr) (c : ℕ), P[i]? = some Ci → P[j]? = some Cj →
    Ci.ty = Cj.ty → SupReach E Ci.cls c → SupReach E Cj.cls c → i = j

/-- Sanity check: the fragment contains environments with superclasses — `supEnv` under the single
hypothesis `Ord α` (whose superclass closure is `Ord α, Eq α`). -/
theorem superFragment_supEnv : SuperFragment supEnv [⟨1, .var 0⟩] where
  env_ok := supEnv_ok.toEnvOK
  inst_no_super := by simp [supEnv]
  no_overlap := by simp [supEnv]
  closure_rigid := by simp [supEnv]
  closure_unique := by
    intro i j Ci Cj c hi hj _ _ _
    have h1 := (List.getElem?_eq_some_iff.mp hi).1
    have h2 := (List.getElem?_eq_some_iff.mp hj).1
    simp at h1 h2
    omega

/-- A derivable constraint is an instance of an instance head, or in the superclass closure of a
hypothesis. -/
theorem DEnt.source {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperFragment E P) {C : Cstr}
    {d : Lambda} (h : DEnt E P n C d) :
    (∃ I ∈ E.insts, ∃ s : ℕ → Mty, C = ⟨I.cls, msubst s I.head⟩) ∨
      ∃ (i : ℕ) (C₀ : Cstr), P[i]? = some C₀ ∧ C₀.ty = C.ty ∧ SupReach E C₀.cls C.cls := by
  induction h with
  | @hyp C i hi => exact Or.inr ⟨i, C, hi, rfl, .refl⟩
  | @sup c d τ D dd hc hs _ ih =>
      rcases ih with ⟨I, hI, s, hC⟩ | ⟨i, C₀, hi, hty, hr⟩
      · obtain ⟨rfl, -⟩ := Cstr.mk.inj hC
        exact absurd (hF.inst_no_super I hI D hc) (by rw [hs]; simp)
      · exact Or.inr ⟨i, C₀, hi, hty, hr.tail ⟨D, hc, hs⟩⟩
  | @inst I s ds hI _ _ _ => exact Or.inl ⟨I, hI, s, rfl⟩

/-- A class with a superclass is not an instance class. -/
theorem SuperFragment.not_inst_of_super {E : Env} {P : List Cstr} (hF : SuperFragment E P)
    {c d : ℕ} {D : ClassDecl} (hc : E.classes[c]? = some D) (hs : D.super = some d) {τ : Mty}
    {I : Inst} (hI : I ∈ E.insts) {s : ℕ → Mty} (hC : (⟨c, τ⟩ : Cstr) = ⟨I.cls, msubst s I.head⟩) :
    False := by
  obtain ⟨rfl, -⟩ := Cstr.mk.inj hC
  exact absurd (hF.inst_no_super I hI D hc) (by rw [hs]; simp)

/-- **Uniqueness of dictionaries in the fragment with superclasses.** -/
theorem DEnt.unique_super {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperFragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : d = d' := by
  induction h generalizing d' with
  | @hyp C i hi =>
      cases h' with
      | @hyp _ i' hi' =>
          rw [hF.closure_unique i i' C C C.cls hi hi' rfl .refl .refl]
      | @sup c _ τ D dd hc hs h₀ =>
          rcases DEnt.source hF h₀ with ⟨I, hI, s, hC⟩ | ⟨j, C₀, hj, hty, hr⟩
          · exact (hF.not_inst_of_super hc hs hI hC).elim
          · have hr' : SupReach E C₀.cls _ := hr.tail ⟨D, hc, hs⟩
            have hij := hF.closure_unique j i C₀ ⟨_, τ⟩ _ hj hi hty hr' .refl
            subst hij
            rw [hj] at hi
            cases hi
            have h1 := hr.le hF.env_ok
            have h2 := SupStep.lt hF.env_ok ⟨D, hc, hs⟩
            simp only at h1 h2
            omega
      | @inst I s ds hI _ =>
          exact absurd rfl (hF.closure_rigid _ (List.mem_of_getElem? hi) _ .refl I hI s)
  | @sup c d τ D dd hc hs h₀ ih =>
      generalize hC0 : (⟨d, τ⟩ : Cstr) = C0 at h'
      cases h' with
      | @hyp _ i hi =>
          subst hC0
          rcases DEnt.source hF h₀ with ⟨I, hI, s, hC⟩ | ⟨j, C₀, hj, hty, hr⟩
          · exact (hF.not_inst_of_super hc hs hI hC).elim
          · have hr' : SupReach E C₀.cls d := hr.tail ⟨D, hc, hs⟩
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
          rcases DEnt.source hF h₀ with ⟨I, hI, s, hC⟩ | ⟨j, C₀, hj, hty, hr⟩
          · exact (hF.not_inst_of_super hc hs hI hC).elim
          rcases DEnt.source hF h₀' with ⟨I, hI, s, hC⟩ | ⟨j', C₀', hj', hty', hr'⟩
          · exact (hF.not_inst_of_super hc' hs' hI hC).elim
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
      | @inst I s ds hI _ =>
          rcases DEnt.source hF h₀ with ⟨I', hI', s', hC⟩ | ⟨j, C₀, hj, hty, hr⟩
          · exact (hF.not_inst_of_super hc hs hI' hC).elim
          · exact (hF.closure_rigid _ (List.mem_of_getElem? hj) _ (hr.tail ⟨D, hc, hs⟩) I hI s
              (by rw [← hC0]; simp only at hty; rw [hty])).elim
  | @inst I s ds hI hds _ ih =>
      generalize hC0 : (⟨I.cls, msubst s I.head⟩ : Cstr) = C0 at h'
      cases h' with
      | @hyp _ i' hi' =>
          subst hC0
          exact absurd rfl (hF.closure_rigid _ (List.mem_of_getElem? hi') _ .refl I hI s)
      | @sup c _ τ D dd hc hs h₀ =>
          rcases DEnt.source hF h₀ with ⟨I', hI', s', hC⟩ | ⟨j, C₀, hj, hty, hr⟩
          · exact (hF.not_inst_of_super hc hs hI' hC).elim
          · exact (hF.closure_rigid _ (List.mem_of_getElem? hj) _ (hr.tail ⟨D, hc, hs⟩) I hI s
              (by rw [hC0]; simp only at hty; rw [hty])).elim
      | @inst I' s' ds' hI' hds' hall' =>
          obtain ⟨hcls, hhead⟩ := Cstr.mk.inj hC0
          obtain ⟨rfl, hctx⟩ := hF.no_overlap I hI I' hI' s s' hcls hhead
          suffices hdd : ds = ds' by rw [hdd]
          refine List.ext_getElem (hds.trans hds'.symm) fun k hk hk' => ?_
          have hkc : k < I.ctxt.length := hds ▸ hk
          have h2 := hall' k hk' hkc
          rw [← hctx _ (List.getElem_mem hkc)] at h2
          exact ih k hk hkc h2

/-- **`DEnt.conv_super`**: in the fragment with superclasses, any two dictionaries for one
constraint are β-convertible. -/
theorem DEnt.conv_super {E : Env} {P : List Cstr} {n : ℕ} (hF : SuperFragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : Lambda.Conv d d' := by
  rw [DEnt.unique_super hF h h']
  exact Lambda.conv_refl d'

/-- Coherence of annotated elaboration in the fragment with superclasses. -/
theorem AElab.coherent_super {E : Env} {P : List Cstr} (hF : SuperFragment E P)
    {Γ Γ' : List Mty} {e : ASexp} {τ τ' : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t)
    (h' : AElab E P Γ' e τ' t') (hlen : Γ.length = Γ'.length) : t = t' := by
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
          rw [DEnt.unique_super hF hd hd']

/-- **Coherence for unambiguous judgements with superclasses**: in the fragment with
superclasses, an unambiguous derivable judgement has an elaboration, and any two are equal. -/
theorem coherence_unannotated_super {E : Env} {P : List Cstr} (hF : SuperFragment E P)
    {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) (hS : STyping E P Γ e τ) :
    (∃ t, ElabS E P Γ e τ t) ∧ ∀ t t', ElabS E P Γ e τ t → ElabS E P Γ e τ t' → t = t' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, t, he, ha⟩ := hS.annotate
    exact ⟨t, a, he, ha⟩
  · rintro t t' ⟨a, he, ha⟩ ⟨a', he', ha'⟩
    obtain ⟨rfl, _⟩ := hB.annot_unique he he' ha ha' (fun _ => ⟨rfl, rfl⟩)
    exact AElab.coherent_super hF ha ha' rfl

/-- Coherence with superclasses, up to β-conversion. -/
theorem coherence_unannotated_super_conv {E : Env} {P : List Cstr} (hF : SuperFragment E P)
    {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) {t t' : Lambda}
    (h : ElabS E P Γ e τ t) (h' : ElabS E P Γ e τ t') : Lambda.Conv t t' := by
  obtain ⟨a, he, ha⟩ := h
  rw [(coherence_unannotated_super hF hB (he ▸ ha.styping)).2 t t' ⟨a, he, ha⟩ h']
  exact Lambda.conv_refl t'

end TypeClass
