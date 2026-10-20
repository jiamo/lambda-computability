/-
**System FC with data types: preservation and progress** (task `M25-SYSTEM-FC-TYCON`).

System F with type-equality coercions (`Start/SystemFCoerce.lean`) extended, over the types and
coercions of `Start/SystemFCTyConTypes.lean`, by algebraic data types in the style of Sulzmann,
Chakravarty, Peyton Jones and Donnelly (2007):

* a **data signature** `D : List DataCon`; constructor `K` builds a value of `T σ₁ ⋯ σₙ`
  (`tycon`, `arity = n`) from one field of type `field[σ]` (a type over the `n` parameters).
  Constructors with one field keep the term language free of nested lists; a nullary constructor
  is a field of the closed type `∀α. α → α`;
* terms `dcon K σ e` (constructor application) and `case t K t₁ t₂` (if `t` is built by `K`, run
  `t₁` on its field, otherwise `t₂`);
* **axiom schemes** between types, in particular between constructor applications
  (`(n, F σ, τ)` for a type-family instance, `(n, N α, φ)` for a newtype);
* reduction: β, type-β, the cast rules of round 4, `case` on a constructor (`caseMatch`,
  `caseMiss`) and **the push rule for data constructors** `casePush`:
  `case (K σ e ▷ γ) K t₁ t₂ ⟶ t₁[e ▷ field[nth γ]]`, where `field[nth γ]` (`liftCo`) is the
  field type with its parameters replaced by the argument decompositions `nth j γ` of `γ`;
* `FCTyCon.Typing.preservation` — **subject reduction**, for a well-scoped signature and
  well-scoped axiom schemes;
* `FCTyCon.Consistent` — **consistency**: a derivable coercion never relates two types with
  different heads, where the heads are `→`, `∀` and the type constructors (so in particular two
  applications of distinct type constructors are never related, `Consistent.tapps_ne`);
  `consistent_nil` — the empty axiom set is consistent;
* `FCTyCon.Typing.progress` — **progress for closed terms, under consistency**, and
  `FCTyCon.Typing.safety`.
-/

import Start.SystemFCTyConTypes

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FCTyCon

/-! ### Data signatures and terms -/

/-- A data constructor: it builds a value of `tycon σ₁ ⋯ σ_arity` from one field of type
`field[σ]`. -/
structure DataCon where
  /-- The type constructor of the result. -/
  tycon : ℕ
  /-- The number of type parameters. -/
  arity : ℕ
  /-- The type of the field, over the parameters `0, …, arity - 1`. -/
  field : Ty

/-- A well-scoped signature: field types mention only the parameters. -/
def SigOK (D : List DataCon) : Prop := ∀ c ∈ D, Scoped c.arity c.field

/-- Terms of System FC with data types. -/
inductive Tm where
  | var : ℕ → Tm
  | app : Tm → Tm → Tm
  | lam : Ty → Tm → Tm
  | tlam : Tm → Tm
  | tapp : Tm → Ty → Tm
  | cast : Tm → Co → Tm
  /-- The constructor `K` at the types `σ` applied to its field. -/
  | dcon : ℕ → List Ty → Tm → Tm
  /-- `case t K t₁ t₂`: if `t` is built by `K`, run `t₁` on its field, otherwise `t₂`. -/
  | case : Tm → ℕ → Tm → Tm → Tm

/-- Substituting the type variables of a term. -/
def substTyTm (s : ℕ → Ty) : Tm → Tm
  | .var i => .var i
  | .app a b => .app (substTyTm s a) (substTyTm s b)
  | .lam A t => .lam (tySubst s A) (substTyTm s t)
  | .tlam t => .tlam (substTyTm (ups s) t)
  | .tapp t B => .tapp (substTyTm s t) (tySubst s B)
  | .cast t γ => .cast (substTyTm s t) (substTyCo s γ)
  | .dcon K σ e => .dcon K (σ.map (tySubst s)) (substTyTm s e)
  | .case t K t₁ t₂ => .case (substTyTm s t) K (substTyTm s t₁) (substTyTm s t₂)

/-- Weakening the type variables of a term. -/
def shiftTyTm (t : Tm) : Tm := substTyTm (fun i => Ty.var (i + 1)) t

/-- Lifting the term variables. -/
def lift (n k : ℕ) : Tm → Tm
  | .var y => if y < k then .var y else .var (y + n)
  | .app a b => .app (lift n k a) (lift n k b)
  | .lam A t => .lam A (lift n (k + 1) t)
  | .tlam t => .tlam (lift n k t)
  | .tapp t B => .tapp (lift n k t) B
  | .cast t γ => .cast (lift n k t) γ
  | .dcon K σ e => .dcon K σ (lift n k e)
  | .case t K t₁ t₂ => .case (lift n k t) K (lift n (k + 1) t₁) (lift n k t₂)

/-- Substituting a term variable. -/
def subst (u : Tm) (x : ℕ) : Tm → Tm
  | .var y => if y = x then u else if y > x then .var (y - 1) else .var y
  | .app a b => .app (subst u x a) (subst u x b)
  | .lam A t => .lam A (subst (lift 1 0 u) (x + 1) t)
  | .tlam t => .tlam (subst (shiftTyTm u) x t)
  | .tapp t B => .tapp (subst u x t) B
  | .cast t γ => .cast (subst u x t) γ
  | .dcon K σ e => .dcon K σ (subst u x e)
  | .case t K t₁ t₂ => .case (subst u x t) K (subst (lift 1 0 u) (x + 1) t₁) (subst u x t₂)

/-! ### Typing -/

/-- **Typing for System FC with data types**, relative to a signature and an axiom set. -/
inductive Typing (D : List DataCon) (Ax : AxSet) : List Ty → Tm → Ty → Prop
  | var {Γ : List Ty} {i : ℕ} {A : Ty} : Γ[i]? = some A → Typing D Ax Γ (.var i) A
  | app {Γ : List Ty} {a b : Tm} {A B : Ty} :
      Typing D Ax Γ a (.arrow A B) → Typing D Ax Γ b A → Typing D Ax Γ (.app a b) B
  | lam {Γ : List Ty} {t : Tm} {A B : Ty} :
      Typing D Ax (A :: Γ) t B → Typing D Ax Γ (.lam A t) (.arrow A B)
  | tlam {Γ : List Ty} {t : Tm} {A : Ty} :
      Typing D Ax (Γ.map tyShift) t A → Typing D Ax Γ (.tlam t) (.all A)
  | tapp {Γ : List Ty} {t : Tm} {A : Ty} (B : Ty) :
      Typing D Ax Γ t (.all A) → Typing D Ax Γ (.tapp t B) (tyInst B A)
  | cast {Γ : List Ty} {t : Tm} {γ : Co} {A B : Ty} :
      Typing D Ax Γ t A → CoTyping Ax γ A B → Typing D Ax Γ (.cast t γ) B
  | dcon {Γ : List Ty} {K : ℕ} {c : DataCon} {σ : List Ty} {e : Tm} :
      D[K]? = some c → σ.length = c.arity → Typing D Ax Γ e (tySubst (listSub σ) c.field) →
      Typing D Ax Γ (.dcon K σ e) (tapps c.tycon σ)
  | case {Γ : List Ty} {t : Tm} {K : ℕ} {c : DataCon} {σ : List Ty} {t₁ t₂ : Tm} {B : Ty} :
      D[K]? = some c → σ.length = c.arity → Typing D Ax Γ t (tapps c.tycon σ) →
      Typing D Ax (tySubst (listSub σ) c.field :: Γ) t₁ B → Typing D Ax Γ t₂ B →
      Typing D Ax Γ (.case t K t₁ t₂) B

/-! ### Reduction -/

/-- One step of reduction (the push rule for data constructors reads the field type off the
signature). -/
inductive Step (D : List DataCon) : Tm → Tm → Prop
  | beta (A : Ty) (t u : Tm) : Step D (.app (.lam A t) u) (subst u 0 t)
  | tbeta (t : Tm) (B : Ty) : Step D (.tapp (.tlam t) B) (substTyTm (tyCons B Ty.var) t)
  | castTrans (t : Tm) (γ δ : Co) : Step D (.cast (.cast t γ) δ) (.cast t (.trans γ δ))
  | pushApp (A : Ty) (t : Tm) (γ : Co) (u : Tm) :
      Step D (.app (.cast (.lam A t) γ) u)
        (.cast (.app (.lam A t) (.cast u (.sym (.left γ)))) (.right γ))
  | pushTApp (t : Tm) (γ : Co) (C : Ty) :
      Step D (.tapp (.cast (.tlam t) γ) C) (.cast (.tapp (.tlam t) C) (.inst γ C))
  /-- `case` on the matching constructor. -/
  | caseMatch (K : ℕ) (σ : List Ty) (e t₁ t₂ : Tm) :
      Step D (.case (.dcon K σ e) K t₁ t₂) (subst e 0 t₁)
  /-- `case` on another constructor. -/
  | caseMiss {K K' : ℕ} (h : K' ≠ K) (σ : List Ty) (e t₁ t₂ : Tm) :
      Step D (.case (.dcon K' σ e) K t₁ t₂) t₂
  /-- **The push rule for data constructors**: the cast moves onto the field, along the lifting of
  the field type to the decompositions of the coercion. -/
  | casePush {K : ℕ} {c : DataCon} (hK : D[K]? = some c) (σ : List Ty) (e : Tm) (γ : Co)
      (t₁ t₂ : Tm) :
      Step D (.case (.cast (.dcon K σ e) γ) K t₁ t₂)
        (subst (.cast e (liftCo c.field (nthCos γ c.arity))) 0 t₁)
  /-- `case` on another constructor under a cast. -/
  | casePushMiss {K K' : ℕ} (h : K' ≠ K) (σ : List Ty) (e : Tm) (γ : Co) (t₁ t₂ : Tm) :
      Step D (.case (.cast (.dcon K' σ e) γ) K t₁ t₂) t₂
  | appL {a a' : Tm} (b : Tm) : Step D a a' → Step D (.app a b) (.app a' b)
  | appR (a : Tm) {b b' : Tm} : Step D b b' → Step D (.app a b) (.app a b')
  | lam (A : Ty) {t t' : Tm} : Step D t t' → Step D (.lam A t) (.lam A t')
  | tlam {t t' : Tm} : Step D t t' → Step D (.tlam t) (.tlam t')
  | tapp {t t' : Tm} (B : Ty) : Step D t t' → Step D (.tapp t B) (.tapp t' B)
  | cast {t t' : Tm} (γ : Co) : Step D t t' → Step D (.cast t γ) (.cast t' γ)
  /-- Congruence in the scrutinee. -/
  | caseScrut {t t' : Tm} (K : ℕ) (t₁ t₂ : Tm) : Step D t t' →
      Step D (.case t K t₁ t₂) (.case t' K t₁ t₂)

variable {D : List DataCon} {Ax : AxSet}

/-! ### Weakening and substitution -/

theorem Typing.lift_gen {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing D Ax Γ t A) :
    ∀ (k : ℕ) (Δ : List Ty),
      (∀ i A', Γ[i]? = some A' → Δ[if i < k then i else i + 1]? = some A') →
      Typing D Ax Δ (lift 1 k t) A := by
  induction h with
  | @var Γ i A hi =>
      intro k Δ hk
      have hb := hk i A hi
      by_cases hik : i < k
      · rw [if_pos hik] at hb
        have hl : lift 1 k (Tm.var i) = Tm.var i := by simp [lift, hik]
        rw [hl]; exact Typing.var hb
      · rw [if_neg hik] at hb
        have hl : lift 1 k (Tm.var i) = Tm.var (i + 1) := by simp [lift, hik]
        rw [hl]; exact Typing.var hb
  | app _ _ iha ihb => intro k Δ hk; exact Typing.app (iha k Δ hk) (ihb k Δ hk)
  | @lam Γ t A B _ ih =>
      intro k Δ hk
      refine Typing.lam (ih (k + 1) (A :: Δ) ?_)
      intro i A' hi
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA; simp
      | succ j =>
          have hj : Γ[j]? = some A' := by simpa using hi
          have hb := hk j A' hj
          by_cases hjk : j < k
          · rw [if_pos hjk] at hb
            rw [if_pos (by omega : j + 1 < k + 1)]
            simpa using hb
          · rw [if_neg hjk] at hb
            rw [if_neg (by omega : ¬ (j + 1 < k + 1))]
            simpa using hb
  | @tlam Γ t A _ ih =>
      intro k Δ hk
      refine Typing.tlam (ih k (Δ.map tyShift) ?_)
      intro i A' hi
      rw [List.getElem?_map] at hi ⊢
      match hΓ : Γ[i]? with
      | none => rw [hΓ] at hi; exact absurd hi (by simp)
      | some A₀ =>
          rw [hΓ] at hi
          have hA' : tyShift A₀ = A' := by simpa using hi
          subst hA'
          rw [hk i A₀ hΓ]
          rfl
  | tapp B _ ih => intro k Δ hk; exact Typing.tapp B (ih k Δ hk)
  | cast _ hγ ih => intro k Δ hk; exact Typing.cast (ih k Δ hk) hγ
  | dcon hK hσ _ ih => intro k Δ hk; exact Typing.dcon hK hσ (ih k Δ hk)
  | @case Γ t K c σ t₁ t₂ B hK hσ _ _ _ ih ih₁ ih₂ =>
      intro k Δ hk
      refine Typing.case hK hσ (ih k Δ hk) (ih₁ (k + 1) _ ?_) (ih₂ k Δ hk)
      intro i A' hi
      cases i with
      | zero =>
          have hA : tySubst (listSub σ) c.field = A' := by simpa using hi
          subst hA; simp
      | succ j =>
          have hj : Γ[j]? = some A' := by simpa using hi
          have hb := hk j A' hj
          by_cases hjk : j < k
          · rw [if_pos hjk] at hb
            rw [if_pos (by omega : j + 1 < k + 1)]
            simpa using hb
          · rw [if_neg hjk] at hb
            rw [if_neg (by omega : ¬ (j + 1 < k + 1))]
            simpa using hb

theorem Typing.lift_one {Δ : List Ty} {u : Tm} {A : Ty} (h : Typing D Ax Δ u A) (B : Ty) :
    Typing D Ax (B :: Δ) (lift 1 0 u) A := by
  refine h.lift_gen 0 (B :: Δ) ?_
  intro i A' hi
  simpa using hi

/-- **A derivation may be substituted in its type variables**, for a well-scoped signature and
well-scoped axiom schemes. -/
theorem Typing.substTy (hD : SigOK D) (hAx : AxOK Ax) {Γ : List Ty} {t : Tm} {A : Ty}
    (h : Typing D Ax Γ t A) :
    ∀ s : ℕ → Ty, Typing D Ax (Γ.map (tySubst s)) (substTyTm s t) (tySubst s A) := by
  induction h with
  | @var Γ i A hi =>
      intro s
      refine Typing.var ?_
      rw [List.getElem?_map, hi]
      rfl
  | app _ _ iha ihb => intro s; exact Typing.app (iha s) (ihb s)
  | lam _ ih => intro s; exact Typing.lam (ih s)
  | @tlam Γ t A _ ih =>
      intro s
      refine Typing.tlam ?_
      have hmap : (Γ.map tyShift).map (tySubst (ups s)) = (Γ.map (tySubst s)).map tyShift := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_congr_left fun X _ => tySubst_tyShift s X
      have := ih (ups s)
      rwa [hmap] at this
  | @tapp Γ t A B _ ih =>
      intro s
      rw [tySubst_tyInst]
      exact Typing.tapp _ (ih s)
  | cast _ hγ ih => intro s; exact Typing.cast (ih s) (hγ.substTy hAx s)
  | @dcon Γ K c σ e hK hσ _ ih =>
      intro s
      have hsc := hD c (List.mem_of_getElem? hK)
      rw [tySubst_tapps]
      refine Typing.dcon hK (by simp [hσ]) ?_
      rw [← tySubst_listSub hsc σ hσ s]
      exact ih s
  | @case Γ t K c σ t₁ t₂ B hK hσ _ _ _ ih ih₁ ih₂ =>
      intro s
      have hsc := hD c (List.mem_of_getElem? hK)
      refine Typing.case hK (σ := σ.map (tySubst s)) (by simp [hσ]) ?_ ?_ (ih₂ s)
      · rw [← tySubst_tapps]; exact ih s
      · rw [← tySubst_listSub hsc σ hσ s]
        exact ih₁ s

theorem Typing.shiftTy (hD : SigOK D) (hAx : AxOK Ax) {Γ : List Ty} {t : Tm} {A : Ty}
    (h : Typing D Ax Γ t A) : Typing D Ax (Γ.map tyShift) (shiftTyTm t) (tyShift A) := by
  have hsub := h.substTy hD hAx (fun i => Ty.var (i + 1))
  have hA : tySubst (fun i => Ty.var (i + 1)) A = tyShift A := (tyShift_eq_tySubst A).symm
  have hΓ : Γ.map (tySubst (fun i => Ty.var (i + 1))) = Γ.map tyShift :=
    List.map_congr_left fun X _ => (tyShift_eq_tySubst X).symm
  rw [hA, hΓ] at hsub
  exact hsub

/-- **Substituting a term variable**, in the general form needed under binders. -/
theorem Typing.subst_gen (hD : SigOK D) (hAx : AxOK Ax) {Γ : List Ty} {t : Tm} {B : Ty}
    (h : Typing D Ax Γ t B) :
    ∀ (k : ℕ) (Δ : List Ty) (u : Tm) (A : Ty),
      Γ[k]? = some A → Typing D Ax Δ u A →
      (∀ i A', i < k → Γ[i]? = some A' → Δ[i]? = some A') →
      (∀ i A', k ≤ i → Γ[i + 1]? = some A' → Δ[i]? = some A') →
      Typing D Ax Δ (subst u k t) B := by
  induction h with
  | @var Γ i B hi =>
      intro k Δ u A hk hu hlt hge
      by_cases hik : i = k
      · subst hik
        have hAB : A = B := by rw [hk] at hi; simpa using hi
        subst hAB
        have hl : subst u i (Tm.var i) = u := by simp [subst]
        rw [hl]; exact hu
      · by_cases hgt : i > k
        · have hl : subst u k (Tm.var i) = Tm.var (i - 1) := by simp [subst, hik, hgt]
          rw [hl]
          refine Typing.var (hge (i - 1) B (by omega) ?_)
          have : i - 1 + 1 = i := by omega
          rw [this]; exact hi
        · have hl : subst u k (Tm.var i) = Tm.var i := by simp [subst, hik, hgt]
          rw [hl]
          exact Typing.var (hlt i B (by omega) hi)
  | app _ _ iha ihb =>
      intro k Δ u A hk hu hlt hge
      exact Typing.app (iha k Δ u A hk hu hlt hge) (ihb k Δ u A hk hu hlt hge)
  | @lam Γ t A₀ B₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      refine Typing.lam (ih (k + 1) (A₀ :: Δ) (lift 1 0 u) A (by simpa using hk)
        (hu.lift_one A₀) ?_ ?_)
      · intro i A' hi hget
        cases i with
        | zero => simpa using hget
        | succ j =>
            have hj : Γ[j]? = some A' := by simpa using hget
            simpa using hlt j A' (by omega) hj
      · intro i A' hi hget
        cases i with
        | zero => omega
        | succ j =>
            have hj : Γ[j + 1]? = some A' := by simpa using hget
            simpa using hge j A' (by omega) hj
  | @tlam Γ t A₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      refine Typing.tlam (ih k (Δ.map tyShift) (shiftTyTm u) (tyShift A) ?_
        (hu.shiftTy hD hAx) ?_ ?_)
      · rw [List.getElem?_map, hk]; rfl
      · intro i A' hi hget
        rw [List.getElem?_map] at hget ⊢
        match hΓ : Γ[i]? with
        | none => rw [hΓ] at hget; exact absurd hget (by simp)
        | some A₁ =>
            rw [hΓ] at hget
            have hA' : tyShift A₁ = A' := by simpa using hget
            subst hA'
            rw [hlt i A₁ hi hΓ]; rfl
      · intro i A' hi hget
        rw [List.getElem?_map] at hget ⊢
        match hΓ : Γ[i + 1]? with
        | none => rw [hΓ] at hget; exact absurd hget (by simp)
        | some A₁ =>
            rw [hΓ] at hget
            have hA' : tyShift A₁ = A' := by simpa using hget
            subst hA'
            rw [hge i A₁ hi hΓ]; rfl
  | tapp B₀ _ ih =>
      intro k Δ u A hk hu hlt hge
      exact Typing.tapp B₀ (ih k Δ u A hk hu hlt hge)
  | cast _ hγ ih =>
      intro k Δ u A hk hu hlt hge
      exact Typing.cast (ih k Δ u A hk hu hlt hge) hγ
  | dcon hK hσ _ ih =>
      intro k Δ u A hk hu hlt hge
      exact Typing.dcon hK hσ (ih k Δ u A hk hu hlt hge)
  | @case Γ t K c σ t₁ t₂ B₀ hK hσ _ _ _ ih ih₁ ih₂ =>
      intro k Δ u A hk hu hlt hge
      refine Typing.case hK hσ (ih k Δ u A hk hu hlt hge) ?_ (ih₂ k Δ u A hk hu hlt hge)
      refine ih₁ (k + 1) (_ :: Δ) (lift 1 0 u) A (by simpa using hk) (hu.lift_one _) ?_ ?_
      · intro i A' hi hget
        cases i with
        | zero => simpa using hget
        | succ j =>
            have hj : Γ[j]? = some A' := by simpa using hget
            simpa using hlt j A' (by omega) hj
      · intro i A' hi hget
        cases i with
        | zero => omega
        | succ j =>
            have hj : Γ[j + 1]? = some A' := by simpa using hget
            simpa using hge j A' (by omega) hj

theorem Typing.subst_zero (hD : SigOK D) (hAx : AxOK Ax) {Γ : List Ty} {t u : Tm} {A B : Ty}
    (ht : Typing D Ax (A :: Γ) t B) (hu : Typing D Ax Γ u A) : Typing D Ax Γ (subst u 0 t) B := by
  refine ht.subst_gen hD hAx 0 Γ u A (by simp) hu ?_ ?_
  · intro i A' hi _; omega
  · intro i A' _ hget; simpa using hget

/-! ### Inversion -/

theorem Typing.cast_inv {Γ : List Ty} {t : Tm} {γ : Co} {B : Ty}
    (h : Typing D Ax Γ (.cast t γ) B) : ∃ A, Typing D Ax Γ t A ∧ CoTyping Ax γ A B := by
  cases h with
  | cast ht hγ => exact ⟨_, ht, hγ⟩

theorem Typing.dcon_inv {Γ : List Ty} {K : ℕ} {σ : List Ty} {e : Tm} {A : Ty}
    (h : Typing D Ax Γ (.dcon K σ e) A) :
    ∃ c, D[K]? = some c ∧ σ.length = c.arity ∧
      Typing D Ax Γ e (tySubst (listSub σ) c.field) ∧ A = tapps c.tycon σ := by
  cases h with
  | dcon hK hσ he => exact ⟨_, hK, hσ, he, rfl⟩

theorem Typing.lam_inv {Γ : List Ty} {A₀ : Ty} {t : Tm} {A : Ty}
    (h : Typing D Ax Γ (.lam A₀ t) A) : ∃ B, A = .arrow A₀ B ∧ Typing D Ax (A₀ :: Γ) t B := by
  cases h with
  | lam ht => exact ⟨_, rfl, ht⟩

theorem Typing.tlam_inv {Γ : List Ty} {t : Tm} {A : Ty}
    (h : Typing D Ax Γ (.tlam t) A) : ∃ A', A = .all A' ∧ Typing D Ax (Γ.map tyShift) t A' := by
  cases h with
  | tlam ht => exact ⟨_, rfl, ht⟩

theorem tapps_ne_arrow (T : ℕ) (σ : List Ty) (A B : Ty) : tapps T σ ≠ .arrow A B := by
  cases σ <;> simp [tapps]

theorem tapps_ne_all (T : ℕ) (σ : List Ty) (A : Ty) : tapps T σ ≠ .all A := by
  cases σ <;> simp [tapps]

theorem tapps_inj {T T' : ℕ} : ∀ {σ ρ : List Ty}, tapps T σ = tapps T' ρ → T = T' ∧ σ = ρ
  | [], [], h => by simp only [tapps, Ty.con.injEq] at h; exact ⟨h, rfl⟩
  | [], _ :: _, h => by simp [tapps] at h
  | _ :: _, [], h => by simp [tapps] at h
  | A :: σ, B :: ρ, h => by
      simp only [tapps, Ty.app.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      obtain ⟨hT, rfl⟩ := tapps_inj h1
      exact ⟨hT, rfl⟩

/-! ### Preservation -/

/-- **Subject reduction for System FC with data types**, for a well-scoped signature and
well-scoped axiom schemes. -/
theorem Typing.preservation (hD : SigOK D) (hAx : AxOK Ax) {Γ : List Ty} {t : Tm} {A : Ty}
    (h : Typing D Ax Γ t A) : ∀ t' : Tm, Step D t t' → Typing D Ax Γ t' A := by
  induction h with
  | var _ => intro t' hs; cases hs
  | @app Γ a b A₀ B ha hb iha ihb =>
      intro t' hs
      cases hs with
      | beta A₁ s u =>
          obtain ⟨B', hB', hbody⟩ := ha.lam_inv
          cases hB'
          exact hbody.subst_zero hD hAx hb
      | pushApp A₁ s γ u =>
          obtain ⟨A', hlam, hγ⟩ := ha.cast_inv
          obtain ⟨B', rfl, hbody⟩ := hlam.lam_inv
          exact Typing.cast (Typing.app (Typing.lam hbody)
            (Typing.cast hb (CoTyping.sym (CoTyping.left hγ)))) (CoTyping.right hγ)
      | appL _ hstep => exact Typing.app (iha _ hstep) hb
      | appR _ hstep => exact Typing.app ha (ihb _ hstep)
  | @lam Γ t A₀ B _ ih =>
      intro t' hs
      cases hs with
      | lam _ hstep => exact Typing.lam (ih _ hstep)
  | @tlam Γ t A₀ _ ih =>
      intro t' hs
      cases hs with
      | tlam hstep => exact Typing.tlam (ih _ hstep)
  | @tapp Γ t A₀ B hall ih =>
      intro t' hs
      cases hs with
      | tbeta s _ =>
          obtain ⟨A', hA', hbody⟩ := hall.tlam_inv
          cases hA'
          have hsub := hbody.substTy hD hAx (tyCons B Ty.var)
          have hmap : (Γ.map tyShift).map (tySubst (tyCons B Ty.var)) = Γ := by
            simp only [List.map_map, Function.comp_def]
            refine (List.map_congr_left fun X _ => ?_).trans (List.map_id Γ)
            exact tyInst_tyShift B X
          rw [hmap] at hsub
          exact hsub
      | pushTApp s γ _ =>
          obtain ⟨A', htl, hγ⟩ := hall.cast_inv
          obtain ⟨A'', rfl, hbody⟩ := htl.tlam_inv
          exact Typing.cast (Typing.tapp B (Typing.tlam hbody)) (CoTyping.inst B hγ)
      | tapp _ hstep => exact Typing.tapp B (ih _ hstep)
  | @cast Γ t γ A₀ B ht hγ ih =>
      intro t' hs
      cases hs with
      | castTrans s γ₁ _ =>
          obtain ⟨A', hs', hγ₁⟩ := ht.cast_inv
          exact Typing.cast hs' (CoTyping.trans hγ₁ hγ)
      | cast _ hstep => exact Typing.cast (ih _ hstep) hγ
  | dcon _ _ _ _ => intro t' hs; cases hs
  | @case Γ t K c σ t₁ t₂ B hK hσ ht ht₁ ht₂ ih _ _ =>
      intro t' hs
      cases hs with
      | caseMatch _ σ' e _ _ =>
          obtain ⟨c', hK', hσ', he, heq⟩ := ht.dcon_inv
          rw [hK] at hK'
          cases hK'
          have hσσ : σ' = σ := (tapps_inj heq.symm).2
          subst hσσ
          exact ht₁.subst_zero hD hAx he
      | caseMiss _ _ _ _ _ => exact ht₂
      | @casePush _ c' hK' σ' e γ _ _ =>
          rw [hK] at hK'
          cases hK'
          obtain ⟨A', hdc, hγ⟩ := ht.cast_inv
          obtain ⟨c'', hK'', hσ', he, rfl⟩ := hdc.dcon_inv
          rw [hK] at hK''
          cases hK''
          have hlen : σ'.length = σ.length := by rw [hσ', hσ]
          have hcs := CoTyping.nthCos hγ hlen
          rw [hσ'] at hcs
          have hlift := CoTyping.liftCo hAx c.field (nthCos γ c.arity) (listSub σ') (listSub σ) hcs
          exact ht₁.subst_zero hD hAx (Typing.cast he hlift)
      | casePushMiss _ _ _ _ _ _ => exact ht₂
      | caseScrut _ _ _ hstep => exact Typing.case hK hσ (ih _ hstep) ht₁ ht₂

/-- Subject reduction along many steps. -/
theorem Typing.preservation_star (hD : SigOK D) (hAx : AxOK Ax) {Γ : List Ty} {t t' : Tm}
    {A : Ty} (h : Typing D Ax Γ t A) (hs : Relation.ReflTransGen (Step D) t t') :
    Typing D Ax Γ t' A := by
  induction hs with
  | refl => exact h
  | tail _ hstep ih => exact ih.preservation hD hAx _ hstep

/-! ### Consistency -/

/-- The heads of types that classify values: `→`, `∀` and the type constructors. -/
inductive Head where
  | arrow : Head
  | all : Head
  | con : ℕ → Head
  deriving DecidableEq

/-- The head of a type (`none` for a type variable or a variable-headed application). -/
def tyHead : Ty → Option Head
  | .var _ => none
  | .arrow _ _ => some .arrow
  | .all _ => some .all
  | .con T => some (.con T)
  | .app A _ => tyHead A

theorem tyHead_tapps (T : ℕ) (σ : List Ty) : tyHead (tapps T σ) = some (.con T) := by
  induction σ with
  | nil => rfl
  | cons A σ ih => simpa [tapps, tyHead] using ih

/-- **Consistency of the axiom set**: a derivable coercion never relates two types with different
heads (`→`, `∀`, or distinct type constructors). -/
def Consistent (Ax : AxSet) : Prop :=
  ∀ (γ : Co) (A B : Ty) (h₁ h₂ : Head), CoTyping Ax γ A B → tyHead A = some h₁ →
    tyHead B = some h₂ → h₁ = h₂

/-- Under consistency, applications of distinct type constructors are never related. -/
theorem Consistent.tapps_ne (hcon : Consistent Ax) {T T' : ℕ} (hT : T ≠ T') (σ ρ : List Ty)
    (γ : Co) : ¬ CoTyping Ax γ (tapps T σ) (tapps T' ρ) := by
  intro h
  have := hcon γ _ _ _ _ h (tyHead_tapps T σ) (tyHead_tapps T' ρ)
  exact hT (by cases this; rfl)

/-- Without axioms, a coercion relates a type only to itself. -/
theorem CoTyping.eq_of_nil {γ : Co} {A B : Ty} (h : CoTyping [] γ A B) : A = B := by
  induction h with
  | refl => rfl
  | sym _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | arr _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | all _ ih => rw [ih]
  | inst C _ ih => cases ih; rfl
  | ax hi => simp at hi
  | left _ ih => cases ih; rfl
  | right _ ih => cases ih; rfl
  | capp _ _ ih₁ ih₂ => rw [ih₁, ih₂]
  | appL _ ih => cases ih; rfl
  | appR _ ih => cases ih; rfl

/-- The empty axiom set is consistent (so the hypothesis of progress is satisfiable). -/
theorem consistent_nil : Consistent [] := by
  intro γ A B h₁ h₂ h ha hb
  rw [h.eq_of_nil] at ha
  rw [ha] at hb
  cases hb
  rfl

/-! ### Progress -/

/-- Plain values: abstractions, type abstractions and constructor applications. -/
inductive PlainValue : Tm → Prop
  | lam (A : Ty) (t : Tm) : PlainValue (.lam A t)
  | tlam (t : Tm) : PlainValue (.tlam t)
  | dcon (K : ℕ) (σ : List Ty) (e : Tm) : PlainValue (.dcon K σ e)

/-- Values: plain values, possibly under one cast. -/
inductive Value : Tm → Prop
  | plain {v : Tm} : PlainValue v → Value v
  | cast {v : Tm} (γ : Co) : PlainValue v → Value (.cast v γ)

/-- **Progress for System FC with data types**: under consistency, a closed well-typed term is a
value or takes a step. -/
theorem Typing.progress (hcon : Consistent Ax) {t : Tm} {A : Ty} (h : Typing D Ax [] t A) :
    Value t ∨ ∃ t', Step D t t' := by
  generalize hΓ : ([] : List Ty) = Γ at h
  induction h with
  | var hi => subst hΓ; simp at hi
  | @app Γ a b A₀ B ha hb iha _ =>
      right
      rcases iha hΓ with hv | ⟨a', ha'⟩
      · cases hv with
        | plain hp =>
            cases hp with
            | lam A₁ s => exact ⟨_, Step.beta A₁ s b⟩
            | tlam s =>
                obtain ⟨A', hA', _⟩ := ha.tlam_inv
                cases hA'
            | dcon K σ e =>
                obtain ⟨c, _, _, _, hA'⟩ := ha.dcon_inv
                exact absurd hA'.symm (tapps_ne_arrow _ _ _ _)
        | cast γ hp =>
            obtain ⟨A', hv, hγ⟩ := ha.cast_inv
            cases hp with
            | lam A₁ s => exact ⟨_, Step.pushApp A₁ s γ b⟩
            | tlam s =>
                obtain ⟨A'', rfl, _⟩ := hv.tlam_inv
                exact absurd (hcon γ _ _ _ _ hγ rfl rfl) (by simp)
            | dcon K σ e =>
                obtain ⟨c, _, _, _, rfl⟩ := hv.dcon_inv
                exact absurd (hcon γ _ _ _ _ hγ (tyHead_tapps _ _) rfl) (by simp)
      · exact ⟨_, Step.appL b ha'⟩
  | lam _ _ => left; exact Value.plain (PlainValue.lam _ _)
  | tlam _ _ => left; exact Value.plain (PlainValue.tlam _)
  | @tapp Γ t A₀ B ht iht =>
      right
      rcases iht hΓ with hv | ⟨t', ht'⟩
      · cases hv with
        | plain hp =>
            cases hp with
            | lam A₁ s =>
                obtain ⟨B', hB', _⟩ := ht.lam_inv
                cases hB'
            | tlam s => exact ⟨_, Step.tbeta s B⟩
            | dcon K σ e =>
                obtain ⟨c, _, _, _, hA'⟩ := ht.dcon_inv
                exact absurd hA'.symm (tapps_ne_all _ _ _)
        | cast γ hp =>
            obtain ⟨A', hv, hγ⟩ := ht.cast_inv
            cases hp with
            | lam A₁ s =>
                obtain ⟨B', rfl, _⟩ := hv.lam_inv
                exact absurd (hcon γ _ _ _ _ hγ rfl rfl) (by simp)
            | tlam s => exact ⟨_, Step.pushTApp s γ B⟩
            | dcon K σ e =>
                obtain ⟨c, _, _, _, rfl⟩ := hv.dcon_inv
                exact absurd (hcon γ _ _ _ _ hγ (tyHead_tapps _ _) rfl) (by simp)
      · exact ⟨_, Step.tapp B ht'⟩
  | @cast Γ t γ A₀ B _ _ iht =>
      rcases iht hΓ with hv | ⟨t', ht'⟩
      · cases hv with
        | plain hp => left; exact Value.cast γ hp
        | @cast v γ' hp => right; exact ⟨_, Step.castTrans v γ' γ⟩
      · right; exact ⟨_, Step.cast γ ht'⟩
  | dcon _ _ _ _ => left; exact Value.plain (PlainValue.dcon _ _ _)
  | @case Γ t K c σ t₁ t₂ B hK hσ ht _ _ iht _ _ =>
      right
      rcases iht hΓ with hv | ⟨t', ht'⟩
      · cases hv with
        | plain hp =>
            cases hp with
            | lam A₁ s =>
                obtain ⟨B', hB', _⟩ := ht.lam_inv
                exact absurd hB' (tapps_ne_arrow _ _ _ _)
            | tlam s =>
                obtain ⟨A', hA', _⟩ := ht.tlam_inv
                exact absurd hA' (tapps_ne_all _ _ _)
            | dcon K' σ' e =>
                by_cases hKK : K' = K
                · subst hKK; exact ⟨_, Step.caseMatch K' σ' e t₁ t₂⟩
                · exact ⟨_, Step.caseMiss hKK σ' e t₁ t₂⟩
        | cast γ hp =>
            obtain ⟨A', hv, hγ⟩ := ht.cast_inv
            cases hp with
            | lam A₁ s =>
                obtain ⟨B', rfl, _⟩ := hv.lam_inv
                exact absurd (hcon γ _ _ _ _ hγ rfl (tyHead_tapps _ _)) (by simp)
            | tlam s =>
                obtain ⟨A'', rfl, _⟩ := hv.tlam_inv
                exact absurd (hcon γ _ _ _ _ hγ rfl (tyHead_tapps _ _)) (by simp)
            | dcon K' σ' e =>
                by_cases hKK : K' = K
                · subst hKK; exact ⟨_, Step.casePush hK σ' e γ t₁ t₂⟩
                · exact ⟨_, Step.casePushMiss hKK σ' e γ t₁ t₂⟩
      · exact ⟨_, Step.caseScrut K t₁ t₂ ht'⟩

/-- **Type safety for System FC with data types**: under a well-scoped signature, well-scoped
axiom schemes and consistency, every reduct of a closed well-typed term has the same type and is a
value or takes a further step. -/
theorem Typing.safety (hD : SigOK D) (hAx : AxOK Ax) (hcon : Consistent Ax) {t t' : Tm} {A : Ty}
    (h : Typing D Ax [] t A) (hs : Relation.ReflTransGen (Step D) t t') :
    Typing D Ax [] t' A ∧ (Value t' ∨ ∃ t'', Step D t' t'') :=
  ⟨h.preservation_star hD hAx hs, (h.preservation_star hD hAx hs).progress hcon⟩

end FCTyCon
