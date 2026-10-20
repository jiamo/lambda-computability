/-
**Coherence for unannotated source judgements** — task `M25-TYPECLASS-COHERENCE` (round 5).

On the calculus of `Start/TypeClassElab.lean` and `Start/TypeClassCoherence.lean`:

* `TypeClass.erase` — erasure of annotated source terms (`ASexp`) to source terms (`Sexp`);
* `TypeClass.DEnt.ent`, `TypeClass.Ent.dent` — dictionary entailment and entailment agree;
* `TypeClass.AElab.styping`, `TypeClass.STyping.annotate` — an annotated elaboration erases to
  a source typing derivation, and every source typing derivation is the erasure of an annotated
  elaboration.  So the elaborations of an unannotated judgement `Γ ⊢ e : τ` are exactly the
  `ElabS E P Γ e τ t`: elaborations of annotations of `e` at `τ`;
* `TypeClass.Bidi` — the **unambiguity condition**, a bidirectional discipline: applications
  synthesise the type of their function, and a method occurrence is only checked against a type
  `inst0 σ m`, with `m` mentioning the class variable (so the judgement determines `σ`, as in
  Haskell's ambiguity check);
* `TypeClass.Bidi.annot_unique` — under the condition, a judgement has at most one annotation;
* `TypeClass.coherence_unannotated` — **coherence for unambiguous unannotated judgements**: in
  the coherent fragment, an unambiguous derivable judgement has an elaboration, and any two
  elaborations are equal (`coherence_unannotated_conv`: β-convertible);
* `TypeClass.ambiguous_not_coherent` — the condition is needed: an environment and a judgement
  with two elaborations that are distinct normal forms, hence not β-convertible;
* `TypeClass.DEnt.subst` — dictionary elaboration is stable under instantiating the hypotheses
  of an instance context by dictionaries;
* `TypeClass.super_coherent` — **the superclass case**: for an instance whose dictionary is a
  record whose superclass field is a dictionary elaborated from the instance context, the
  superclass projection of an instance dictionary is β-convertible to a dictionary elaborated
  for the superclass constraint directly.
-/

import Start.TypeClassCoherence
import Start.ParallelSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-! ### Erasure and the correspondence with source typing -/

/-- Erasure of the annotations. -/
def erase : ASexp → Sexp
  | .var i => .var i
  | .lam e => .lam (erase e)
  | .app _ f a => .app (erase f) (erase a)
  | .method c j _ => .method c j

/-- Dictionary entailment is entailment. -/
theorem DEnt.ent {E : Env} {P : List Cstr} {n : ℕ} {C : Cstr} {d : Lambda}
    (h : DEnt E P n C d) : Ent E P C := by
  induction h with
  | hyp hi => exact Ent.hyp (List.mem_of_getElem? hi)
  | sup hc hs _ ih => exact Ent.sup hc hs ih
  | @inst I s ds hI hds _ ih =>
      refine Ent.inst hI fun C hC => ?_
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hC
      exact ih k (hds ▸ hk) hk

/-- Entailment is witnessed by a dictionary elaboration. -/
theorem Ent.dent {E : Env} {P : List Cstr} {C : Cstr} (h : Ent E P C) (n : ℕ) :
    ∃ d, DEnt E P n C d := by
  induction h with
  | @hyp C hC =>
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hC
      exact ⟨_, DEnt.hyp hi⟩
  | sup hc hs _ ih =>
      obtain ⟨dd, hdd⟩ := ih
      exact ⟨_, DEnt.sup hc hs hdd⟩
  | @inst I s hI _ ih =>
      classical
      let ds : List Lambda := I.ctxt.attach.map fun C => Classical.choose (ih C.1 C.2)
      refine ⟨_, DEnt.inst (s := s) (ds := ds) hI (by simp [ds]) fun k hk hk' => ?_⟩
      simp only [ds, List.getElem_map, List.getElem_attach]
      exact Classical.choose_spec (ih _ (List.getElem_mem hk'))

/-- An annotated elaboration erases to a source typing derivation. -/
theorem AElab.styping {E : Env} {P : List Cstr} {Γ : List Mty} {a : ASexp} {τ : Mty}
    {t : Lambda} (h : AElab E P Γ a τ t) : STyping E P Γ (erase a) τ := by
  induction h with
  | var hi => exact STyping.var hi
  | lam _ ih => exact STyping.lam ih
  | app _ _ ihf iha => exact STyping.app ihf iha
  | method hc hj hd => exact STyping.method hc hj hd.ent

/-- Every source typing derivation is the erasure of an annotated elaboration. -/
theorem STyping.annotate {E : Env} {P : List Cstr} {Γ : List Mty} {e : Sexp} {τ : Mty}
    (h : STyping E P Γ e τ) : ∃ a t, erase a = e ∧ AElab E P Γ a τ t := by
  induction h with
  | @var Γ i τ hi => exact ⟨.var i, _, rfl, AElab.var hi⟩
  | lam _ ih =>
      obtain ⟨a, t, rfl, ha⟩ := ih
      exact ⟨.lam a, _, rfl, AElab.lam ha⟩
  | @app Γ f a A B _ _ ihf iha =>
      obtain ⟨af, tf, rfl, hf⟩ := ihf
      obtain ⟨aa, ta, rfl, ha⟩ := iha
      exact ⟨.app A af aa, _, rfl, AElab.app hf ha⟩
  | @method Γ c j D m τ hc hj hent =>
      obtain ⟨d, hd⟩ := hent.dent Γ.length
      exact ⟨.method c j τ, _, rfl, AElab.method hc hj hd⟩

/-- **An elaboration of the unannotated judgement** `Γ ⊢ e : τ`: the elaboration of some
annotation of `e` at `τ` (equivalently, by `AElab.styping` and `STyping.annotate`, of some source
typing derivation of the judgement). -/
def ElabS (E : Env) (P : List Cstr) (Γ : List Mty) (e : Sexp) (τ : Mty) (t : Lambda) : Prop :=
  ∃ a, erase a = e ∧ AElab E P Γ a τ t

/-! ### The unambiguity condition -/

/-- The monotype mentions a type variable. -/
def HasVar : Mty → Prop
  | Mty.base => False
  | Mty.var _ => True
  | Mty.arrow a b => HasVar a ∨ HasVar b

/-- A signature mentioning the class variable determines the instance type. -/
theorem inst0_inj {m : Mty} (hm : HasVar m) {σ σ' : Mty} (h : inst0 σ m = inst0 σ' m) :
    σ = σ' := by
  induction m with
  | base => exact hm.elim
  | var i => simpa [inst0, msubst] using h
  | arrow a b iha ihb =>
      simp only [inst0, msubst, Mty.arrow.injEq] at h
      rcases hm with ha | hb
      · exact iha ha h.1
      · exact ihb hb h.2

/-- **The unambiguity condition**, as a bidirectional judgement (`true`: the type is
synthesised; `false`: it is checked).  Variables and applications synthesise; abstractions and
method occurrences are checked; a method is only checked against `inst0 σ m` with `m`
mentioning the class variable. -/
inductive Bidi (E : Env) : Bool → List Mty → Sexp → Mty → Prop
  /-- A variable synthesises its type. -/
  | var {Γ : List Mty} {i : ℕ} {τ : Mty} : Γ[i]? = some τ → Bidi E true Γ (.var i) τ
  /-- An application synthesises the result type of its function. -/
  | app {Γ : List Mty} {f a : Sexp} {A B : Mty} :
      Bidi E true Γ f (.arrow A B) → Bidi E false Γ a A → Bidi E true Γ (.app f a) B
  /-- An abstraction is checked against an arrow. -/
  | lam {Γ : List Mty} {e : Sexp} {A B : Mty} :
      Bidi E false (A :: Γ) e B → Bidi E false Γ (.lam e) (.arrow A B)
  /-- A method is checked, and its signature mentions the class variable. -/
  | method {Γ : List Mty} {c j : ℕ} {D : ClassDecl} {m σ : Mty} :
      E.classes[c]? = some D → D.methods[j]? = some m → HasVar m →
      Bidi E false Γ (.method c j) (inst0 σ m)
  /-- A synthesised type can be checked. -/
  | sub {Γ : List Mty} {e : Sexp} {τ : Mty} : Bidi E true Γ e τ → Bidi E false Γ e τ

/-- **Under the unambiguity condition the annotation is unique**: two annotations of `e` with
elaborations agree, and in synthesis mode their types are the synthesised type. -/
theorem Bidi.annot_unique {E : Env} {P : List Cstr} {b : Bool} {Γ : List Mty} {e : Sexp}
    {τ : Mty} (hB : Bidi E b Γ e τ) :
    ∀ {a a' : ASexp} {σ σ' : Mty} {t t' : Lambda}, erase a = e → erase a' = e →
      AElab E P Γ a σ t → AElab E P Γ a' σ' t' → (b = false → σ = τ ∧ σ' = τ) →
      a = a' ∧ (b = true → σ = τ ∧ σ' = τ) := by
  induction hB with
  | @var Γ i τ hi =>
      intro a a' σ σ' t t' he he' h h' _
      cases a <;> simp only [erase, Sexp.var.injEq, reduceCtorEq] at he
      cases a' <;> simp only [erase, Sexp.var.injEq, reduceCtorEq] at he'
      subst he he'
      cases h with
      | var hσ =>
          cases h' with
          | var hσ' =>
              rw [hi] at hσ hσ'
              exact ⟨rfl, fun _ => ⟨(Option.some.inj hσ).symm, (Option.some.inj hσ').symm⟩⟩
  | @app Γ f a A B _ _ ihf iha =>
      intro x x' σ σ' t t' he he' h h' _
      cases x <;> simp only [erase, Sexp.app.injEq, reduceCtorEq] at he
      cases x' <;> simp only [erase, Sexp.app.injEq, reduceCtorEq] at he'
      rename_i A1 f1 a1 A2 f2 a2
      cases h with
      | app hf ha =>
          cases h' with
          | app hf' ha' =>
              obtain ⟨rfl, hty⟩ := ihf he.1 he'.1 hf hf' (by simp)
              obtain ⟨h1, h2⟩ := hty rfl
              simp only [Mty.arrow.injEq] at h1 h2
              obtain ⟨rfl, rfl⟩ := h1
              obtain ⟨rfl, rfl⟩ := h2
              obtain ⟨rfl, _⟩ := iha he.2 he'.2 ha ha' (fun _ => ⟨rfl, rfl⟩)
              exact ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩
  | @lam Γ e A B _ ih =>
      intro x x' σ σ' t t' he he' h h' hty
      obtain ⟨rfl, rfl⟩ := hty rfl
      cases x <;> simp only [erase, Sexp.lam.injEq, reduceCtorEq] at he
      cases x' <;> simp only [erase, Sexp.lam.injEq, reduceCtorEq] at he'
      cases h with
      | lam hb =>
          cases h' with
          | lam hb' =>
              obtain ⟨rfl, _⟩ := ih he he' hb hb' (fun _ => ⟨rfl, rfl⟩)
              exact ⟨rfl, by simp⟩
  | @method Γ c j D m σ0 hc hj hm =>
      intro x x' σ σ' t t' he he' h h' hty
      obtain ⟨e1, e2⟩ := hty rfl
      cases x <;> simp only [erase, Sexp.method.injEq, reduceCtorEq] at he
      cases x' <;> simp only [erase, Sexp.method.injEq, reduceCtorEq] at he'
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨rfl, rfl⟩ := he'
      cases h with
      | method hc1 hj1 _ =>
          cases h' with
          | method hc2 hj2 _ =>
              rw [hc] at hc1 hc2
              cases hc1; cases hc2
              rw [hj] at hj1 hj2
              cases hj1; cases hj2
              have h1 := inst0_inj hm e1
              have h2 := inst0_inj hm e2
              subst h1 h2
              exact ⟨rfl, by simp⟩
  | sub _ ih =>
      intro x x' σ σ' t t' he he' h h' hty
      obtain ⟨h1, h2⟩ := ih he he' h h' (by simp)
      exact ⟨h1, by simp⟩

/-- **Coherence for unambiguous unannotated judgements.**  In the coherent fragment, a derivable
source judgement satisfying the unambiguity condition (in checking mode, which every synthesised
judgement also satisfies by `Bidi.sub`) has an elaboration, and any two of its elaborations are
equal. -/
theorem coherence_unannotated {E : Env} {P : List Cstr} (hF : Fragment E P) {Γ : List Mty}
    {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) (hS : STyping E P Γ e τ) :
    (∃ t, ElabS E P Γ e τ t) ∧ ∀ t t', ElabS E P Γ e τ t → ElabS E P Γ e τ t' → t = t' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, t, he, ha⟩ := hS.annotate
    exact ⟨t, a, he, ha⟩
  · rintro t t' ⟨a, he, ha⟩ ⟨a', he', ha'⟩
    obtain ⟨rfl, _⟩ := hB.annot_unique he he' ha ha' (fun _ => ⟨rfl, rfl⟩)
    exact AElab.coherent hF ha ha' rfl

/-- Coherence for unambiguous unannotated judgements, up to β-conversion. -/
theorem coherence_unannotated_conv {E : Env} {P : List Cstr} (hF : Fragment E P)
    {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) {t t' : Lambda}
    (h : ElabS E P Γ e τ t) (h' : ElabS E P Γ e τ t') : Lambda.Conv t t' := by
  obtain ⟨a, he, ha⟩ := h
  rw [(coherence_unannotated hF hB (he ▸ ha.styping)).2 t t' ⟨a, he, ha⟩ h']
  exact Lambda.conv_refl t'

/-! ### The ambiguity counterexample -/

/-- The method signature `base → base → base`, which does not mention the class variable. -/
def ambSig : Mty := .arrow .base (.arrow .base .base)

/-- The first projection `λx y. x`. -/
def ambK1 : Lambda := .lam (.lam (.var 1))

/-- The second projection `λx y. y`. -/
def ambK2 : Lambda := .lam (.lam (.var 0))

/-- One class with the single method `ambSig`, and two instances (at `base` and at
`base → base`) whose dictionaries hold `ambK1` and `ambK2`. -/
def ambEnv : Env :=
  ⟨[⟨none, [ambSig]⟩], [⟨0, .base, [], recMk [ambK1]⟩, ⟨0, .arrow .base .base, [], recMk [ambK2]⟩]⟩

theorem ambEnv_fragment : Fragment ambEnv [] where
  no_super := by
    intro c D h
    match c, h with
    | 0, h => simp [ambEnv] at h; subst h; rfl
  no_overlap := by
    intro I hI I' hI' s s' _ hh
    simp only [ambEnv, List.mem_cons, List.not_mem_nil, or_false] at hI hI'
    rcases hI with rfl | rfl <;> rcases hI' with rfl | rfl <;>
      simp_all [msubst]
  hyp_rigid := by simp
  nodup := List.nodup_nil

theorem ambEnv_elab (K : Lambda) (hd : DEnt ambEnv [] 0 ⟨0, .base⟩ (recMk [K]) ∨
    DEnt ambEnv [] 0 ⟨0, .arrow .base .base⟩ (recMk [K])) :
    ElabS ambEnv [] [] (.method 0 0) ambSig (recProj 1 0 (recMk [K])) := by
  rcases hd with hd | hd
  · exact ⟨.method 0 0 .base, rfl, AElab.method (D := ⟨none, [ambSig]⟩) (m := ambSig) rfl rfl hd⟩
  · exact ⟨.method 0 0 (.arrow .base .base), rfl,
      AElab.method (D := ⟨none, [ambSig]⟩) (m := ambSig) rfl rfl hd⟩

/-- **The unambiguity condition is needed.**  In an environment of the coherent fragment, the
unannotated judgement `⊢ m₀ : base → base → base` (the method's signature does not mention the
class variable) has two elaborations that are not β-convertible: they go through the dictionaries
of the instance at `base` and of the instance at `base → base`. -/
theorem ambiguous_not_coherent : Fragment ambEnv [] ∧
    STyping ambEnv [] [] (.method 0 0) ambSig ∧
    ∃ t t', ElabS ambEnv [] [] (.method 0 0) ambSig t ∧
      ElabS ambEnv [] [] (.method 0 0) ambSig t' ∧ ¬ Lambda.Conv t t' := by
  have h1 : DEnt ambEnv [] 0 ⟨0, .base⟩ (recMk [ambK1]) :=
    DEnt.inst (I := ⟨0, .base, [], recMk [ambK1]⟩) (s := fun _ => .base) (ds := [])
      (by simp [ambEnv]) rfl (fun k hk => by simp at hk)
  have h2 : DEnt ambEnv [] 0 ⟨0, .arrow .base .base⟩ (recMk [ambK2]) :=
    DEnt.inst (I := ⟨0, .arrow .base .base, [], recMk [ambK2]⟩) (s := fun _ => .base) (ds := [])
      (by simp [ambEnv]) rfl (fun k hk => by simp at hk)
  refine ⟨ambEnv_fragment, (ambEnv_elab _ (.inl h1)).elim fun a ⟨he, ha⟩ => he ▸ ha.styping,
    _, _, ambEnv_elab _ (.inl h1), ambEnv_elab _ (.inr h2), ?_⟩
  rintro ⟨v, hv1, hv2⟩
  have r1 := recProj_recMk [ambK1] 0 (by simp)
  have r2 := recProj_recMk [ambK2] 0 (by simp)
  simp only [List.length_singleton, List.getElem_singleton] at r1 r2
  have n1 : Lambda.is_normal ambK1 := Lambda.lam_normal (Lambda.lam_normal (Lambda.var_normal 1))
  have n2 : Lambda.is_normal ambK2 := Lambda.lam_normal (Lambda.lam_normal (Lambda.var_normal 0))
  obtain ⟨w1, hw1a, hw1b⟩ := Lambda.confluence_theorem r1 hv1
  obtain ⟨w2, hw2a, hw2b⟩ := Lambda.confluence_theorem r2 hv2
  rw [← Lambda.reduces_normal_eq n1 hw1a] at hw1b
  rw [← Lambda.reduces_normal_eq n2 hw2a] at hw2b
  obtain ⟨w, hwa, hwb⟩ := Lambda.confluence_theorem hw1b hw2b
  have := (Lambda.reduces_normal_eq n1 hwa).trans (Lambda.reduces_normal_eq n2 hwb).symm
  simp [ambK1, ambK2] at this

end TypeClass
