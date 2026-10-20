/-
**Type classes by dictionary passing: entailment, typing and elaboration** — task
`M25-TYPECLASS-DICT`.

On top of the dictionary types of `Start/TypeClassDict.lean`:

* `TypeClass.Ent E P C` — the **entailment judgement** for constraints: a hypothesis of the
  context `P`, a superclass of a derivable constraint, or an instance whose context is derivable;
* `TypeClass.STyping E P Γ e τ` — the **source typing judgement**: variables, abstraction,
  application, and the use of a method of a class at a type whose constraint is entailed;
* `TypeClass.EnvGood` — a well-formed environment: superclasses come earlier, method signatures
  mention only the class variable, and every instance declaration carries a dictionary typed, in
  the dictionary types of its instance context, at the dictionary type of its head;
* `TypeClass.ent_dict` — **(E2) entailment is witnessed**: every derivable constraint has a
  dictionary term, built from the instance dictionaries and the superclass projections, typed at
  its dictionary type;
* `TypeClass.elab_typing` — **(E1) elaboration preserves typing**: a source derivation yields a
  System F term of the translated type, in the context of the translated term variables followed
  by the dictionary variables of `P`;
* `TypeClass.elab_sn` — **(E3)** that term is strongly normalizing (`SystemF.sn_of_typing`);
* `TypeClass.elab_program` — a closed program with constraint context `P` elaborates to a term
  of the **qualified type** `∀ᾱ. C₁τ₁ → ⋯ → Cₙτₙ → ⟦τ⟧`.

Coherence (E4) is not proved; see `docs/goal/evidence/M25-TYPECLASS-DICT.md`.
-/

import Start.TypeClassDict
import Start.HMSystemF

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-! ### Entailment and source typing -/

/-- **Entailment of a class constraint** from a constraint context. -/
inductive Ent (E : Env) (P : List Cstr) : Cstr → Prop
  /-- A hypothesis. -/
  | hyp {C : Cstr} : C ∈ P → Ent E P C
  /-- A superclass of a derivable constraint. -/
  | sup {c d : ℕ} {τ : Mty} {D : ClassDecl} : E.classes[c]? = some D → D.super = some d →
      Ent E P ⟨c, τ⟩ → Ent E P ⟨d, τ⟩
  /-- An instance whose context is derivable. -/
  | inst {I : Inst} {s : ℕ → Mty} : I ∈ E.insts → (∀ C ∈ I.ctxt, Ent E P (C.subst s)) →
      Ent E P ⟨I.cls, msubst s I.head⟩

/-- Source expressions: variables, abstraction, application, and method selection. -/
inductive Sexp where
  /-- A variable. -/
  | var : ℕ → Sexp
  /-- An abstraction. -/
  | lam : Sexp → Sexp
  /-- An application. -/
  | app : Sexp → Sexp → Sexp
  /-- The `j`-th method of the class `c`. -/
  | method : ℕ → ℕ → Sexp

/-- **Source typing**, with a constraint context `P` and a context `Γ` of monotypes. -/
inductive STyping (E : Env) (P : List Cstr) : List Mty → Sexp → Mty → Prop
  /-- A variable. -/
  | var {Γ : List Mty} {i : ℕ} {τ : Mty} : Γ[i]? = some τ → STyping E P Γ (.var i) τ
  /-- An abstraction. -/
  | lam {Γ : List Mty} {e : Sexp} {A B : Mty} :
      STyping E P (A :: Γ) e B → STyping E P Γ (.lam e) (.arrow A B)
  /-- An application. -/
  | app {Γ : List Mty} {f a : Sexp} {A B : Mty} :
      STyping E P Γ f (.arrow A B) → STyping E P Γ a A → STyping E P Γ (.app f a) B
  /-- A method of a class, at a type whose class constraint is entailed. -/
  | method {Γ : List Mty} {c j : ℕ} {D : ClassDecl} {m τ : Mty} :
      E.classes[c]? = some D → D.methods[j]? = some m → Ent E P ⟨c, τ⟩ →
      STyping E P Γ (.method c j) (inst0 τ m)

/-- A **well-formed environment**: `EnvOK`, and every instance carries a well-typed
dictionary. -/
structure EnvGood (E : Env) : Prop extends EnvOK E where
  /-- The dictionary of an instance has the dictionary type of its head, in the context of the
  dictionaries of its instance context. -/
  insts_ok : ∀ I ∈ E.insts,
    Typing (I.ctxt.map (dictTyC E)) I.dict (dictTy E I.cls I.head)

/-! ### Dictionaries for entailed constraints -/

theorem exists_env {Δ : List FTy} {Cs : List Cstr} {f : Cstr → FTy}
    (h : ∀ C ∈ Cs, ∃ d, Typing Δ d (f C)) :
    ∃ u : ℕ → Lambda, ∀ i A', (Cs.map f)[i]? = some A' → Typing Δ (u i) A' := by
  induction Cs with
  | nil => exact ⟨fun _ => Lambda.var 0, by simp⟩
  | cons C Cs ih =>
      obtain ⟨d, hd⟩ := h C (List.mem_cons_self ..)
      obtain ⟨u, hu⟩ := ih fun C' hC' => h C' (List.mem_cons_of_mem _ hC')
      refine ⟨fun i => match i with | 0 => d | i + 1 => u i, ?_⟩
      intro i A' hi
      cases i with
      | zero => simpa using (by simpa using hi : f C = A') ▸ hd
      | succ i => exact hu i A' (by simpa using hi)

/-- The index of the `j`-th method among the fields of a dictionary. -/
def methodIdx (D : ClassDecl) (j : ℕ) : ℕ :=
  (match D.super with | none => 0 | some _ => 1) + j

theorem dictFields_super {E : Env} {D : ClassDecl} {d : ℕ} (hs : D.super = some d) (τ : Mty) :
    (dictFields (dictTy E) D τ)[0]? = some (dictTy E d τ) := by
  simp [dictFields, hs]

theorem dictFields_method {E : Env} {D : ClassDecl} {j : ℕ} {m : Mty}
    (hj : D.methods[j]? = some m) (τ : Mty) :
    (dictFields (dictTy E) D τ)[methodIdx D j]? = some (mtyF (inst0 τ m)) := by
  cases hs : D.super with
  | none =>
      simp only [dictFields, hs, methodIdx, Nat.zero_add, List.nil_append]
      simp [List.getElem?_map, hj]
  | some d =>
      simp only [dictFields, hs, methodIdx]
      rw [List.getElem?_append_right (by simp)]
      simp [List.getElem?_map, hj]

/-- **(E2) Entailment is witnessed by a dictionary term.** -/
theorem ent_dict {E : Env} {P : List Cstr} {C : Cstr} (hE : EnvGood E) (h : Ent E P C) :
    ∀ Δ : List FTy, ∃ d, Typing (Δ ++ P.map (dictTyC E)) d (dictTyC E C) := by
  induction h with
  | @hyp C hC =>
      intro Δ
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hC
      refine ⟨Lambda.var (Δ.length + i), Typing.var ?_⟩
      rw [List.getElem?_append_right (by omega)]
      simpa [List.getElem?_map] using congrArg (Option.map (dictTyC E)) hi
  | @sup c d τ D hc hs _ ih =>
      intro Δ
      obtain ⟨dd, hdd⟩ := ih Δ
      have hdt : dictTyC E ⟨c, τ⟩ = recTy (dictFields (dictTy E) D τ) := dictTy_eq hE.toEnvOK hc τ
      rw [hdt] at hdd
      refine ⟨recProj (dictFields (dictTy E) D τ).length 0 dd, ?_⟩
      exact typing_recProj hdd (dictFields_super hs τ)
  | @inst I s hI _ ih =>
      intro Δ
      have hdict := hE.insts_ok I hI
      have h1 := hdict.substTy (mtyS s)
      have hctx : (I.ctxt.map (dictTyC E)).map (tySubst (mtyS s))
          = I.ctxt.map (fun C => dictTyC E (C.subst s)) := by
        rw [List.map_map]
        exact List.map_congr_left fun C _ => (dictTyC_subst hE.toEnvOK s C).symm
      have hty : tySubst (mtyS s) (dictTy E I.cls I.head) = dictTyC E ⟨I.cls, msubst s I.head⟩ :=
        (dictTy_msubst hE.toEnvOK I.cls s I.head).symm
      rw [hctx, hty] at h1
      obtain ⟨u, hu⟩ := exists_env (Δ := Δ ++ P.map (dictTyC E))
        (f := fun C => dictTyC E (C.subst s)) fun C hC => ih C hC Δ
      exact ⟨Lambda.substEnv u I.dict, h1.substEnv _ u hu⟩

/-! ### Elaboration -/

/-- The System F context of a source judgement: the term variables, then the dictionaries. -/
def tctx (E : Env) (P : List Cstr) (Γ : List Mty) : List FTy :=
  Γ.map mtyF ++ P.map (dictTyC E)

/-- **(E1) Elaboration preserves typing.** -/
theorem elab_typing {E : Env} {P : List Cstr} {Γ : List Mty} {e : Sexp} {τ : Mty}
    (hE : EnvGood E) (h : STyping E P Γ e τ) : ∃ t, Typing (tctx E P Γ) t (mtyF τ) := by
  induction h with
  | @var Γ i τ hi =>
      refine ⟨Lambda.var i, Typing.var ?_⟩
      have hlt : i < Γ.length := by
        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hi
        exact hlt
      rw [tctx, List.getElem?_append_left (by simpa using hlt)]
      simpa [List.getElem?_map] using congrArg (Option.map mtyF) hi
  | @lam Γ e A B _ ih =>
      obtain ⟨t, ht⟩ := ih
      exact ⟨Lambda.lam t, Typing.lam (by simpa [tctx] using ht)⟩
  | app _ _ ihf iha =>
      obtain ⟨tf, htf⟩ := ihf
      obtain ⟨ta, hta⟩ := iha
      exact ⟨Lambda.app tf ta, Typing.app htf hta⟩
  | @method Γ c j D m τ hc hj hent =>
      obtain ⟨d, hd⟩ := ent_dict hE hent (Γ.map mtyF)
      have hdt : dictTyC E ⟨c, τ⟩ = recTy (dictFields (dictTy E) D τ) := dictTy_eq hE.toEnvOK hc τ
      rw [hdt] at hd
      exact ⟨recProj (dictFields (dictTy E) D τ).length (methodIdx D j) d,
        typing_recProj hd (dictFields_method hj τ)⟩

/-- **(E3) Every well-typed source expression elaborates to a strongly normalizing System F
term.** -/
theorem elab_sn {E : Env} {P : List Cstr} {Γ : List Mty} {e : Sexp} {τ : Mty}
    (hE : EnvGood E) (h : STyping E P Γ e τ) :
    ∃ t, Typing (tctx E P Γ) t (mtyF τ) ∧ Lambda.SN t := by
  obtain ⟨t, ht⟩ := elab_typing hE h
  exact ⟨t, ht, sn_of_typing ht⟩

/-! ### The qualified type of a program -/

theorem lams_lam (n : ℕ) (t : Lambda) : lams n (Lambda.lam t) = Lambda.lam (lams n t) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [lams, ih]

theorem typing_lams_ctx : ∀ (Δ : List FTy) {Γ : List FTy} {t : Lambda} {A : FTy},
    Typing (Δ ++ Γ) t A → Typing Γ (lams Δ.length t) (Δ.foldl (fun B X => FTy.arrow X B) A) := by
  intro Δ
  induction Δ with
  | nil => intro Γ t A h; exact h
  | cons X Δ ih =>
      intro Γ t A h
      have h' : Typing (X :: (Δ ++ Γ)) t A := by simpa using h
      have h2 := ih (Γ := Γ) (t := Lambda.lam t) (A := FTy.arrow X A) (Typing.lam h')
      simpa [lams_lam, List.length_cons, lams] using h2

/-- **A closed program elaborates to a term of its qualified type** `∀ᾱ. C₁τ₁ → ⋯ → Cₙτₙ → ⟦τ⟧`
(the constraints become dictionary arguments, and `K` type variables are quantified). -/
theorem elab_program {E : Env} {P : List Cstr} {e : Sexp} {τ : Mty}
    (hE : EnvGood E) (h : STyping E P [] e τ) (K : ℕ) :
    ∃ t, Typing [] t
      (HM.allN K ((P.map (dictTyC E)).foldl (fun B X => FTy.arrow X B) (mtyF τ))) ∧
      Lambda.SN t := by
  obtain ⟨t, ht⟩ := elab_typing hE h
  have ht' : Typing (P.map (dictTyC E) ++ []) t (mtyF τ) := by simpa [tctx] using ht
  have h1 := typing_lams_ctx (P.map (dictTyC E)) ht'
  have h2 := HM.typing_allN_gen (Γ := []) K (by simpa using h1)
  exact ⟨_, h2, sn_of_typing h2⟩

end TypeClass
