/-
**Every derivation of `λΠ` is interpreted in every model**: the existence half of initiality.

`Start/LambdaPiInterp.lean` defines the interpretation as a relation and
`Start/LambdaPiInterpFun.lean` shows it is single-valued; what is proved here is that it is
*defined* on the derivable judgements.  Together the two say that the interpretation is a partial
function which is total on derivations, which is what "the syntax is initial" means at the level of
raw expressions.

* `LambdaPi.CtxI.lookup` — a variable of an interpreted context has an interpreted type, and its
  de Bruijn index reads exactly the corresponding value of the semantic context;
* `LambdaPi.TyI.pi_data` — whatever a product denotes, its domain denotes a code and its body a
  type over that code;
* `LambdaPi.Typing.interp_total` — **the interpretation is total on derivations**: a derivable type
  denotes a type of the model, and a derivable term denotes a term of the denotation of its type;
* `LambdaPi.TyI.total`, `LambdaPi.TmI.total`, `LambdaPi.CtxI.total` — the three consequences, for
  types, for terms and for well-formed contexts;
* `LambdaPi.interp_exists_unique` — **existence and uniqueness of the interpretation** of a
  derivable term, in a model whose product former is injective.

The proof is the usual one, by induction on the derivation.  The conversion rule is where the work
of `Start/LambdaPiInterpConv.lean` is used, and the substitution rule (the type of an application)
is where the work of `Start/LambdaPiInterpSub.lean` is used.  The hypothesis `Model.PiInj` enters
only through those two.
-/

import Start.LambdaPiInterpConv
import Start.LambdaPiUnique

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

open CategoryTheory

namespace LambdaPi

variable {C : Type u} [Category.{v} C] {M : Model.{u, v, w} C}

/-! ### Auxiliary steps -/

/-- A term of the universe denotes a type: this is the rule `El`, in the form in which the
induction uses it. -/
theorem TyI.of_star_tm {Γ' : C} {sc : SemCtx M Γ'} {t : Tm} {A' : M.T.Ty Γ'}
    {x : Cwa.Tm M.T Γ' A'} (hA : TyI sc (Tm.sort Srt.star) A') (hx : TmI sc t A' x) :
    ∃ B' : M.T.Ty Γ', TyI sc t B' := by
  have h := hA.sort_star_inv
  subst h
  exact ⟨M.Un.El x, TyI.el hx⟩

/-- **Whatever a product denotes**, directly or through its code, **its domain denotes a code and
its body a type over the decoding of that code.** -/
theorem TyI.pi_data {Γ' : C} {sc : SemCtx M Γ'} {A B : Tm} {P : M.T.Ty Γ'}
    (h : TyI sc (Tm.pi A B) P) :
    ∃ (a : Cwa.Tm M.T Γ' (M.Un.U Γ')) (B' : M.T.Ty (M.T.ext Γ' (M.Un.El a))),
      TmI sc A (M.Un.U Γ') a ∧ TyI (sc.cons (M.Un.El a)) B B' := by
  cases h with
  | @pi _ _ _ _ a B' ha hB => exact ⟨a, B', ha, hB⟩
  | el hc =>
      obtain ⟨a, b, ha, hb, _⟩ := hc.pi_inv
      exact ⟨a, M.Un.El b, ha, TyI.el hb⟩

/-- **A variable of an interpreted context has an interpreted type**, and the semantic context
reads at that index exactly a term of it. -/
theorem CtxI.lookup {Γ : Ctx} {n : ℕ} {A : Tm} (hA : Lookup Γ n A) :
    ∀ {Γ' : C} {sc : SemCtx M Γ'}, CtxI Γ sc →
      ∃ (A' : M.T.Ty Γ') (x : Cwa.Tm M.T Γ' A'), TyI sc A A' ∧ sc.varVal n = some ⟨A', x⟩ := by
  induction hA with
  | zero Γ A =>
      intro Γ' sc hc
      cases hc with
      | @cons _ Γ₀ s _ A' _ hA' =>
          exact ⟨M.T.tySub (M.T.disp A') A', Cwa.var A', hA'.weaken A', rfl⟩
  | @succ Γ n A B _ ih =>
      intro Γ' sc hc
      cases hc with
      | @cons _ Γ₀ s _ B' hΓ hB' =>
          obtain ⟨A', x, hA', hv⟩ := ih hΓ
          exact ⟨M.T.tySub (M.T.disp B') A', M.T.tmSub (M.T.disp B') x, hA'.weaken B', by
            simp [SemCtx.varVal, hv, Cwa.Val.sub]⟩

/-! ### Totality -/

/-- **The interpretation is total on derivations.**  A derivable *type* — an expression whose type
is a sort — denotes a type of the model, and a derivable *term* — one whose type is not the top
sort `□` — denotes a term of the denotation of its type. -/
theorem Typing.interp_total (hinj : M.PiInj) {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) :
    ∀ (Γ' : C) (sc : SemCtx M Γ'), CtxI Γ sc →
      ((A = Tm.sort Srt.star ∨ A = Tm.sort Srt.box) → ∃ A' : M.T.Ty Γ', TyI sc t A') ∧
      (A ≠ Tm.sort Srt.box → ∃ (A' : M.T.Ty Γ') (x : Cwa.Tm M.T Γ' A'),
        TyI sc A A' ∧ TmI sc t A' x) := by
  induction h with
  | ax Γ =>
      intro Γ' sc _
      exact ⟨fun _ => ⟨M.Un.U Γ', TyI.star sc⟩, fun hne => absurd rfl hne⟩
  | @var Γ n A hv =>
      intro Γ' sc hc
      obtain ⟨A', x, hA', hval⟩ := CtxI.lookup hv hc
      refine ⟨fun hor => ?_, fun _ => ⟨A', x, hA', TmI.var hval⟩⟩
      rcases hor with rfl | rfl
      · exact TyI.of_star_tm hA' (TmI.var hval)
      · exact absurd hA' TyI.not_sort_box
  | @pi Γ A B s k hr hA hB ihA ihB =>
      intro Γ' sc hc
      have hs : s = Srt.star := hr
      subst hs
      obtain ⟨U', a, hU, ha⟩ := (ihA Γ' sc hc).2 (by simp)
      have hUU : U' = M.Un.U Γ' := hU.sort_star_inv
      subst hUU
      have hcons : CtxI (A :: Γ) (sc.cons (M.Un.El a)) := CtxI.cons hc (TyI.el ha)
      refine ⟨fun _ => ?_, fun hne => ?_⟩
      · obtain ⟨B', hB'⟩ := (ihB _ _ hcons).1 (by cases k <;> simp)
        exact ⟨M.SP.Pi a B', TyI.pi ha hB'⟩
      · have hk : k = Srt.star := by cases k with
          | star => rfl
          | box => exact absurd rfl hne
        subst hk
        obtain ⟨U₂, b, hU₂, hb⟩ := (ihB _ _ hcons).2 (by simp)
        have : U₂ = M.Un.U (M.T.ext Γ' (M.Un.El a)) := hU₂.sort_star_inv
        subst this
        exact ⟨M.Un.U Γ', M.PC.code a b, TyI.star sc, TmI.pi ha hb⟩
  | @lam Γ A B b s hP hb ihP ihb =>
      intro Γ' sc hc
      refine ⟨fun hor => by rcases hor with h | h <;> exact absurd h (by simp), fun _ => ?_⟩
      obtain ⟨P', hP'⟩ := (ihP Γ' sc hc).1 (by cases s <;> simp)
      obtain ⟨a, B', ha, hB'⟩ := hP'.pi_data
      have hcons : CtxI (A :: Γ) (sc.cons (M.Un.El a)) := CtxI.cons hc (TyI.el ha)
      have hBne : B ≠ Tm.sort Srt.box := by
        rintro rfl
        exact TyI.not_sort_box hB'
      obtain ⟨B₂, x, hB₂, hx⟩ := (ihb _ _ hcons).2 hBne
      exact ⟨M.SP.Pi a B₂, M.SP.lam x, TyI.pi ha hB₂, TmI.lam ha hx⟩
  | @app Γ f g A B hf hg ihf ihg =>
      intro Γ' sc hc
      have hpine : Tm.pi A B ≠ Tm.sort Srt.box := by simp
      have htm : B[g] ≠ Tm.sort Srt.box →
          ∃ (A' : M.T.Ty Γ') (x : Cwa.Tm M.T Γ' A'),
            TyI sc (B[g]) A' ∧ TmI sc (Tm.app f g) A' x := by
        intro _
        obtain ⟨P', f', hP', hf'⟩ := (ihf Γ' sc hc).2 hpine
        obtain ⟨a, B', ha, hB'⟩ := hP'.pi_data
        have hPP : P' = M.SP.Pi a B' := TyI.unique_of_piInj hinj hP' (TyI.pi ha hB')
        subst hPP
        have hAne : A ≠ Tm.sort Srt.box := by
          rintro rfl
          exact TmI.not_sort ha
        obtain ⟨A₂, x, hA₂, hx⟩ := (ihg Γ' sc hc).2 hAne
        have hAA : A₂ = M.Un.El a := TyI.unique_of_piInj hinj hA₂ (TyI.el ha)
        subst hAA
        exact ⟨M.T.tySub x.1 B', M.T.tmSub x.1 (M.SP.app f'), hB'.inst hx, TmI.app hf' hx⟩
      refine ⟨fun hor => ?_, htm⟩
      rcases hor with hstar | hbox
      · obtain ⟨A', x, hA', hx⟩ := htm (by rw [hstar]; simp)
        rw [hstar] at hA'
        exact TyI.of_star_tm hA' hx
      · -- the type of an application is never the top sort
        exfalso
        cases B with
        | var n =>
            cases n with
            | zero =>
                have hgb : g = Tm.sort Srt.box := by simpa [LambdaPi.inst] using hbox
                subst hgb
                exact not_typing_box hg
            | succ m => simp [LambdaPi.inst, ids] at hbox
        | sort k =>
            have hk : k = Srt.box := by simpa [LambdaPi.inst] using hbox
            subst hk
            obtain ⟨P', f', hP', _⟩ := (ihf Γ' sc hc).2 hpine
            obtain ⟨a, B', _, hB'⟩ := hP'.pi_data
            exact TyI.not_sort_box hB'
        | app _ _ => simp [LambdaPi.inst] at hbox
        | lam _ _ => simp [LambdaPi.inst] at hbox
        | pi _ _ => simp [LambdaPi.inst] at hbox
  | @conv Γ t A B s ht hB hconv iht ihB =>
      intro Γ' sc hc
      obtain ⟨B', hB'⟩ := (ihB Γ' sc hc).1 (by cases s <;> simp)
      have hAne : A ≠ Tm.sort Srt.box := by
        rintro rfl
        obtain ⟨v, h1, h2⟩ := hconv.church_rosser
        have hv : v = Tm.sort Srt.box := Red.sort_inv h1
        subst hv
        exact TyI.not_sort_box (h2.interp_preserves_ty hinj hB')
      obtain ⟨A', x, hA', hx⟩ := (iht Γ' sc hc).2 hAne
      have hAB : A' = B' := TyI.conv_eq hinj hconv hA' hB'
      subst hAB
      refine ⟨fun hor => ?_, fun _ => ⟨A', x, hB', hx⟩⟩
      rcases hor with rfl | rfl
      · exact TyI.of_star_tm hB' hx
      · exact absurd hB (fun h => not_typing_box h)

/-- **A derivable type denotes a type of the model.** -/
theorem TyI.total (hinj : M.PiInj) {Γ : Ctx} {t : Tm} {k : Srt} (h : Typing Γ t (Tm.sort k))
    {Γ' : C} {sc : SemCtx M Γ'} (hc : CtxI Γ sc) : ∃ A' : M.T.Ty Γ', TyI sc t A' :=
  (h.interp_total hinj Γ' sc hc).1 (by cases k <;> simp)

/-- **A derivable term denotes a term of the model**, of the denotation of its type. -/
theorem TmI.total (hinj : M.PiInj) {Γ : Ctx} {t A : Tm} (h : Typing Γ t A)
    (hA : A ≠ Tm.sort Srt.box) {Γ' : C} {sc : SemCtx M Γ'} (hc : CtxI Γ sc) :
    ∃ (A' : M.T.Ty Γ') (x : Cwa.Tm M.T Γ' A'), TyI sc A A' ∧ TmI sc t A' x :=
  (h.interp_total hinj Γ' sc hc).2 hA

/-- **A well-formed context is interpreted.** -/
theorem CtxI.total (hinj : M.PiInj) {Γ : Ctx} (h : Wf Γ) :
    ∃ (Γ' : C) (sc : SemCtx M Γ'), CtxI Γ sc := by
  induction h with
  | nil => exact ⟨M.emp, SemCtx.nil, CtxI.nil⟩
  | @cons Γ A s _ hA ih =>
      obtain ⟨Γ', sc, hc⟩ := ih
      obtain ⟨A', hA'⟩ := TyI.total hinj hA hc
      exact ⟨M.T.ext Γ' A', sc.cons A', CtxI.cons hc hA'⟩

/-- **Existence and uniqueness of the interpretation of a derivable term** in a model whose
product former is injective: the raw term denotes exactly one term of the model, of exactly one
type. -/
theorem interp_exists_unique (hinj : M.PiInj) {Γ : Ctx} {t A : Tm} (h : Typing Γ t A)
    (hA : A ≠ Tm.sort Srt.box) {Γ' : C} {sc : SemCtx M Γ'} (hc : CtxI Γ sc) :
    ∃! p : TmVal M Γ', TmI sc t p.1 p.2 := by
  obtain ⟨A', x, _, hx⟩ := TmI.total hinj h hA hc
  refine ⟨⟨A', x⟩, hx, fun q hq => ?_⟩
  exact (TmI.unique_of_piInj hinj hq hx).trans rfl

end LambdaPi
