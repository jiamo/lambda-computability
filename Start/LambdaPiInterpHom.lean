/-
**The interpretation of the substitutions of `λΠ`.**

`Start/LambdaPiInterpTotal.lean` interprets the *judgements* of the calculus: a derivable type
denotes a type of the model and a derivable term denotes a term of it, uniquely.  What is still
missing before the interpretation can be compared with the syntactic category is the interpretation
of the *substitutions*: a well-typed substitution from `Δ` to `Γ` should denote a morphism from the
object interpreting `Δ` to the object interpreting `Γ`, and exactly one.

This module proves that.  The relation `LambdaPi.SubI` of `Start/LambdaPiInterpSub.lean` already
says what it is for a morphism `σ` of the model to *carry* a raw substitution `f`; here it is shown
to determine `σ` uniquely (`LambdaPi.SubI.unique`) and to be inhabited whenever `f` is well typed
(`LambdaPi.SubI.total`), so that the interpretation of a substitution exists and is unique
(`LambdaPi.subI_exists_unique`).

The categorical ingredient is a general fact about a coherent category with attributes, proved
here:

* `Cwa.exists_tm_of_hom` — a morphism into an extended context splits as a term of the substituted
  type followed by the action on extended contexts, and that term is the value the morphism gives
  to the generic term;
* `Cwa.hom_eq_of_val_sub_var` — **a morphism into an extended context is determined by its
  composite with the display map together with the value it gives to the generic term**.  This is
  the universal property of context extension, in the form the de Bruijn reading of a semantic
  context uses.

Two consequences of uniqueness are recorded, and they are what makes the interpretation functorial:
it takes the identity substitution to the identity morphism (`LambdaPi.SubI.id_eq`) and a composite
to the composite (`LambdaPi.SubI.comp_eq`).  Finally `LambdaPi.SubI.conv_eq` shows that the
interpretation only depends on the substitution up to conversion, so that it descends to the
morphisms of the syntactic category, which are well-typed substitutions modulo conversion.
-/

import Start.LambdaPiInterpTotal
import Start.LambdaPiCat

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory Limits

namespace Cwa

variable {C : Type u} [Category.{v} C] {T : Cwa.{u, v, w} C}

/-- **A term of a substituted type is determined by the morphism it induces into the extended
context.**  Both terms are sections of the same display map, so the universal property of the
extension square applies. -/
theorem tm_ext_of_extend {Γ Δ : C} (σ : Δ ⟶ Γ) (A : T.Ty Γ) {x y : T.Tm Δ (T.tySub σ A)}
    (h : x.1 ≫ T.extend σ A = y.1 ≫ T.extend σ A) : x = y :=
  Tm.ext' ((T.isPullback σ A).hom_ext h (by rw [x.2, y.2]))

/-- The value the generic term takes along a morphism into an extended context: its type is the
type substituted along the composite with the display map. -/
theorem val_sub_var_eq {Γ Δ : C} {A : T.Ty Γ} (u : Δ ⟶ T.ext Γ A) :
    Val.sub u (⟨T.tySub (T.disp A) A, Cwa.var A⟩ : Val T (T.ext Γ A))
      = ⟨T.tySub (u ≫ T.disp A) A,
          tmCast (T.tySub_comp (T.disp A) u A).symm (T.tmSub u (Cwa.var A))⟩ :=
  Val.mk_tmCast (T.tySub_comp (T.disp A) u A).symm _

/-- **A morphism into an extended context is recovered from its two components**: the composite
with the display map, and the term the generic term is carried to. -/
theorem extend_tmSub_var (co : ExtCoherent T) {Γ Δ : C} {A : T.Ty Γ} (u : Δ ⟶ T.ext Γ A) :
    (tmCast (T.tySub_comp (T.disp A) u A).symm (T.tmSub u (Cwa.var A))).1
        ≫ T.extend (u ≫ T.disp A) A = u := by
  rw [tmCast_val, co.extend_comp (T.disp A) u A]
  slice_lhs 2 3 => rw [eqToHom_trans]
  rw [eqToHom_refl, Category.id_comp, ← Category.assoc, tmSub_extend u (Cwa.var A),
    Category.assoc, var_extend, Category.comp_id]

/-- **Splitting a morphism into an extended context**: it is a term of the type substituted along
its composite with the display map, followed by the action of that composite on extended contexts,
and the term is exactly the value it gives to the generic term. -/
theorem exists_tm_of_hom (co : ExtCoherent T) {Γ Δ : C} {A : T.Ty Γ} (u : Δ ⟶ T.ext Γ A)
    {σ : Δ ⟶ Γ} (hd : u ≫ T.disp A = σ) :
    ∃ x : T.Tm Δ (T.tySub σ A), x.1 ≫ T.extend σ A = u ∧
      Val.sub u (⟨T.tySub (T.disp A) A, Cwa.var A⟩ : Val T (T.ext Γ A)) = ⟨T.tySub σ A, x⟩ := by
  subst hd
  exact ⟨_, extend_tmSub_var co u, val_sub_var_eq u⟩

/-- Conversely, the value a morphism of the shape `x ≫ σ⁺` gives to the generic term is `x`. -/
theorem val_sub_var_extend (co : ExtCoherent T) {Γ Δ : C} {A : T.Ty Γ} {σ : Δ ⟶ Γ}
    (x : T.Tm Δ (T.tySub σ A)) :
    Val.sub (x.1 ≫ T.extend σ A) (⟨T.tySub (T.disp A) A, Cwa.var A⟩ : Val T (T.ext Γ A))
      = ⟨T.tySub σ A, x⟩ := by
  have hd : (x.1 ≫ T.extend σ A) ≫ T.disp A = σ := by
    rw [Category.assoc, (T.isPullback σ A).w, ← Category.assoc, x.2, Category.id_comp]
  obtain ⟨y, hy, hval⟩ := exists_tm_of_hom co (x.1 ≫ T.extend σ A) hd
  rw [hval, tm_ext_of_extend σ A hy]

/-- **The universal property of context extension, in de Bruijn form**: two morphisms into an
extended context which have the same composite with the display map and give the same value to the
generic term are equal. -/
theorem hom_eq_of_val_sub_var (co : ExtCoherent T) {Γ Δ : C} {A : T.Ty Γ}
    {u v : Δ ⟶ T.ext Γ A} (hd : u ≫ T.disp A = v ≫ T.disp A)
    (hval : Val.sub u (⟨T.tySub (T.disp A) A, Cwa.var A⟩ : Val T (T.ext Γ A))
      = Val.sub v ⟨T.tySub (T.disp A) A, Cwa.var A⟩) : u = v := by
  obtain ⟨x, hx, hxv⟩ := exists_tm_of_hom co u (rfl : u ≫ T.disp A = u ≫ T.disp A)
  obtain ⟨y, hy, hyv⟩ := exists_tm_of_hom co v hd.symm
  rw [hxv, hyv] at hval
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp hval
  rw [← hx, ← hy, eq_of_heq h2]

end Cwa

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### The interpretation of a substitution is unique -/

/-- A substitution carried into an extended semantic context is carried into the shorter one, by
the composite with the display map, once its first value is dropped. -/
theorem SubI.tail {Γ' Δ' : C} {s : SemCtx M Γ'} {r : SemCtx M Δ'} {A' : M.T.Ty Γ'}
    {σ : Δ' ⟶ M.T.ext Γ' A'} {f : ℕ → Tm} (h : SubI (s.cons A') r σ f) :
    SubI s r (σ ≫ M.T.disp A') (fun n => f (n + 1)) := by
  intro n p hp
  have hcons : (SemCtx.cons s A').varVal (n + 1) = some (Cwa.Val.sub (M.T.disp A') p) := by
    simp [SemCtx.varVal, hp]
  exact TmI.cast_val (h (n + 1) _ hcons) (M.co.val_sub_comp (M.T.disp A') σ p)

/-- The value a carried substitution gives to the first variable of an extended semantic
context. -/
theorem SubI.head {Γ' Δ' : C} {s : SemCtx M Γ'} {r : SemCtx M Δ'} {A' : M.T.Ty Γ'}
    {σ : Δ' ⟶ M.T.ext Γ' A'} {f : ℕ → Tm} (h : SubI (s.cons A') r σ f) :
    TmI r (f 0) (Cwa.Val.sub σ (⟨M.T.tySub (M.T.disp A') A', Cwa.var A'⟩ : TmVal M _)).1
      (Cwa.Val.sub σ ⟨M.T.tySub (M.T.disp A') A', Cwa.var A'⟩).2 :=
  h 0 _ rfl

/-- **The morphism carrying a substitution is unique.**  Over the empty context this is the
universal property of the terminal object; over an extended one it is the universal property of
context extension, the two components being the tail of the substitution and its value at the first
variable. -/
theorem SubI.unique (hinj : M.PiInj) {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (hs : CtxI Γ s)
    {Δ' : C} {r : SemCtx M Δ'} {f : ℕ → Tm} {σ τ : Δ' ⟶ Γ'}
    (hσ : SubI s r σ f) (hτ : SubI s r τ f) : σ = τ := by
  induction hs generalizing f with
  | nil => exact M.empIsTerminal.hom_ext σ τ
  | cons _ _ ih =>
      exact Cwa.hom_eq_of_val_sub_var M.co (ih hσ.tail hτ.tail)
        (TmI.unique_of_piInj hinj hσ.head hτ.head)

/-! ### The interpretation of a substitution exists -/

/-- The tail of a well-typed substitution into an extended context is a well-typed substitution
into the shorter one. -/
theorem SubOk.tail {f : ℕ → Tm} {A : Tm} {Γ Δ : Ctx} (h : SubOk f (A :: Γ) Δ) :
    SubOk (fun n => f (n + 1)) Γ Δ := by
  intro n B hB
  have h' := h (n + 1) (shift B) (Lookup.succ A hB)
  rwa [LambdaPiCat.subst_shift'] at h'

/-- The first value of a well-typed substitution into an extended context is a term of the
substituted head type. -/
theorem SubOk.head {f : ℕ → Tm} {A : Tm} {Γ Δ : Ctx} (h : SubOk f (A :: Γ) Δ) :
    Typing Δ (f 0) (subst (fun n => f (n + 1)) A) := by
  have h' := h 0 (shift A) (Lookup.zero Γ A)
  rwa [LambdaPiCat.subst_shift'] at h'

/-- **A well-typed substitution is carried by a morphism of the model.**  The morphism is built by
induction on the interpretation of the target context: the empty context uses the terminal object,
and an extension pairs the morphism carrying the tail with the term denoted by the value of the
substitution at the first variable. -/
theorem SubI.total (hinj : M.PiInj) {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (hs : CtxI Γ s)
    {Δ : Ctx} {Δ' : C} {r : SemCtx M Δ'} (hr : CtxI Δ r) {f : ℕ → Tm} (hf : SubOk f Γ Δ) :
    ∃ σ : Δ' ⟶ Γ', SubI s r σ f := by
  induction hs generalizing f with
  | nil =>
      refine ⟨M.empIsTerminal.from Δ', ?_⟩
      intro n p hp
      exact absurd hp (by simp [SemCtx.varVal])
  | @cons Γ Γ'' s A A' _ hA ih =>
      obtain ⟨σ₀, hσ₀⟩ := ih hf.tail
      have h0 : Typing Δ (f 0) (subst (fun n => f (n + 1)) A) := hf.head
      have hAsub : TyI r (subst (fun n => f (n + 1)) A) (M.T.tySub σ₀ A') := hA.subst hσ₀
      have hne : subst (fun n => f (n + 1)) A ≠ Tm.sort Srt.box := by
        intro hEq
        exact TyI.not_sort_box (hEq ▸ hAsub)
      obtain ⟨B', x, hB', hx⟩ := TmI.total hinj h0 hne hr
      have hBB : B' = M.T.tySub σ₀ A' := TyI.unique_of_piInj hinj hB' hAsub
      subst hBB
      refine ⟨x.1 ≫ M.T.extend σ₀ A', ?_⟩
      have hdisp : (x.1 ≫ M.T.extend σ₀ A') ≫ M.T.disp A' = σ₀ := by
        rw [Category.assoc, (M.T.isPullback σ₀ A').w, ← Category.assoc, x.2, Category.id_comp]
      intro n p hp
      cases n with
      | zero =>
          simp only [SemCtx.varVal, Option.some.injEq] at hp
          subst hp
          rw [Cwa.val_sub_var_extend M.co x]
          exact hx
      | succ m =>
          simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
          obtain ⟨q, hq, rfl⟩ := hp
          refine TmI.cast_val (hσ₀ m q hq) ?_
          exact (((M.co.val_sub_comp (M.T.disp A') _ q)).trans
            (congrArg (fun k => Cwa.Val.sub k q) hdisp)).symm

/-- **Existence and uniqueness of the interpretation of a substitution**: a well-typed substitution
from `Δ` to `Γ` is carried by exactly one morphism of the model between the objects interpreting
the two contexts. -/
theorem subI_exists_unique (hinj : M.PiInj) {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (hs : CtxI Γ s)
    {Δ : Ctx} {Δ' : C} {r : SemCtx M Δ'} (hr : CtxI Δ r) {f : ℕ → Tm} (hf : SubOk f Γ Δ) :
    ∃! σ : Δ' ⟶ Γ', SubI s r σ f := by
  obtain ⟨σ, hσ⟩ := SubI.total hinj hs hr hf
  exact ⟨σ, hσ, fun _ hτ => SubI.unique hinj hs hτ hσ⟩

/-! ### Functoriality -/

/-- **The identity substitution is carried by the identity morphism.** -/
theorem SubI.id {Γ' : C} (s : SemCtx M Γ') : SubI s s (𝟙 Γ') ids := fun _ p hp =>
  TmI.cast_val (TmI.var hp) (M.co.val_sub_id p).symm

/-- **A composite substitution is carried by the composite morphism.** -/
theorem SubI.comp {Γ' Δ' Θ' : C} {s : SemCtx M Γ'} {r : SemCtx M Δ'} {q : SemCtx M Θ'}
    {σ : Δ' ⟶ Γ'} {τ : Θ' ⟶ Δ'} {f g : ℕ → Tm} (hf : SubI s r σ f) (hg : SubI r q τ g) :
    SubI s q (τ ≫ σ) (fun n => subst g (f n)) := fun n p hp =>
  TmI.cast_val ((hf n p hp).subst hg) (M.co.val_sub_comp σ τ p)

/-- The interpretation takes the identity substitution to the identity morphism. -/
theorem SubI.id_eq (hinj : M.PiInj) {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (hs : CtxI Γ s)
    {σ : Γ' ⟶ Γ'} (hσ : SubI s s σ ids) : σ = 𝟙 Γ' :=
  SubI.unique hinj hs hσ (SubI.id s)

/-- The interpretation takes a composite of substitutions to the composite of the morphisms. -/
theorem SubI.comp_eq (hinj : M.PiInj) {Γ : Ctx} {Γ' Δ' Θ' : C} {s : SemCtx M Γ'}
    {r : SemCtx M Δ'} {q : SemCtx M Θ'} (hs : CtxI Γ s) {σ : Δ' ⟶ Γ'} {τ : Θ' ⟶ Δ'}
    {f g : ℕ → Tm} {υ : Θ' ⟶ Γ'} (hf : SubI s r σ f) (hg : SubI r q τ g)
    (hυ : SubI s q υ (fun n => subst g (f n))) : υ = τ ≫ σ :=
  SubI.unique hinj hs hυ (hf.comp hg)

/-! ### Invariance under conversion -/

/-- A variable which has a value in a semantic context interpreting `Γ` is a variable of `Γ`. -/
theorem varVal_lt {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (hs : CtxI Γ s) {n : ℕ}
    {p : TmVal M Γ'} (hp : s.varVal n = some p) : n < Γ.length := by
  induction hs generalizing n with
  | nil => simp [SemCtx.varVal] at hp
  | @cons Γ Γ'' s A A' _ _ ih =>
      cases n with
      | zero => simp
      | succ m =>
          simp only [SemCtx.varVal, Option.map_eq_some_iff] at hp
          obtain ⟨q, hq, -⟩ := hp
          simpa using Nat.succ_lt_succ (ih hq)

/-- **The interpretation of a substitution only depends on it up to conversion** at the variables
of the source context: two convertible substitutions are carried by the same morphism.  This is
what lets the interpretation descend to the morphisms of the syntactic category, which are
well-typed substitutions modulo conversion. -/
theorem SubI.conv_eq (hinj : M.PiInj) {Γ : Ctx} {Γ' : C} {s : SemCtx M Γ'} (hs : CtxI Γ s)
    {Δ' : C} {r : SemCtx M Δ'} {f g : ℕ → Tm} (hconv : ∀ n, n < Γ.length → Conv (f n) (g n))
    {σ τ : Δ' ⟶ Γ'} (hσ : SubI s r σ f) (hτ : SubI s r τ g) : σ = τ := by
  refine SubI.unique hinj hs hσ (fun n p hp => TmI.cast_val (hσ n p hp) ?_)
  exact TmI.conv_eq hinj (hconv n (varVal_lt hs hp)) (hσ n p hp) (hτ n p hp)

end LambdaPi
