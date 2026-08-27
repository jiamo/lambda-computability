/-
**Type inference for `λΠ`.**

With conversion decidable (`Start/LambdaPiNormalize.lean`) the typing judgement itself can be
decided.  This module writes the bidirectional algorithm as a Lean function that is *correct by
construction*: it does not return a type, it returns a type **together with a derivation**, so
soundness is not a theorem but the type of the function.  Completeness is then proved separately,
and the two give decidability of typability.

* `LambdaPi.lookupTy` — the declared type of a variable, computed;
* `LambdaPi.checkSort` — the check that a term is a type or a kind, i.e. that its type converts to
  a sort;
* `LambdaPi.infer` — **type inference**: `infer Γ hΓ t` returns, if it succeeds, a type `A`
  together with a proof of `Γ ⊢ t : A`;
* `LambdaPi.infer_complete` — if a term is typable at all, inference succeeds;
* `LambdaPi.decidableTypable` — **typability is decidable**, and `LambdaPi.decidableTyping` —
  whether a term has a *given* type is decidable as well.
-/

import Start.LambdaPiNormalize

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### The type of a variable -/

/-- The type declared for a variable, computed from the context. -/
def lookupTy : Ctx → ℕ → Option Tm
  | [], _ => none
  | A :: _, 0 => some (shift A)
  | _ :: Γ, n + 1 => (lookupTy Γ n).map shift

theorem lookupTy_sound : ∀ {Γ : Ctx} {n : ℕ} {A : Tm}, lookupTy Γ n = some A → Lookup Γ n A := by
  intro Γ
  induction Γ with
  | nil => intro n A h; simp [lookupTy] at h
  | cons B Γ ih =>
      intro n A h
      cases n with
      | zero => rw [lookupTy] at h; cases h; exact Lookup.zero Γ B
      | succ n =>
          rw [lookupTy] at h
          rcases hl : lookupTy Γ n with _ | A' <;> rw [hl] at h
          · simp at h
          · cases h
            exact Lookup.succ B (ih hl)

theorem lookupTy_complete {Γ : Ctx} {n : ℕ} {A : Tm} (h : Lookup Γ n A) :
    lookupTy Γ n = some A := by
  induction h with
  | zero Γ A => rfl
  | @succ Γ n A B _ ih => rw [lookupTy, ih]; rfl

/-! ### Normal forms of types -/

/-- The type of a typable term is strongly normalizing, whether or not it is itself typable. -/
theorem sn_of_typeOf {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) : SN A := by
  rcases h.validity hΓ with rfl | ⟨s, hs⟩
  · exact sn_sort _
  · exact hs.sn hΓ

/-- A normal term is its own normal form. -/
theorem nf_eq_self {t : Tm} (h : SN t) (hn : Normal t) : nf t h = t :=
  nf_unique (nf_red t h) (nf_normal t h) (Red.refl t) hn

/-- The normal form of a term convertible to a sort is that sort. -/
theorem nf_eq_sort {t : Tm} (h : SN t) {s : Srt} (hc : Conv t (Tm.sort s)) :
    nf t h = Tm.sort s :=
  (conv_iff_normalForm_eq (nf_red t h) (nf_normal t h) (Red.refl (Tm.sort s))
    (fun _ hst => not_step_sort hst)).mp hc

/-- The normal form of a term convertible to a product is a product. -/
theorem nf_pi {t : Tm} (h : SN t) {A B : Tm} (hc : Conv t (Tm.pi A B)) :
    ∃ A' B', nf t h = Tm.pi A' B' := by
  obtain ⟨v, hv₁, hv₂⟩ := ((Conv.ofRed (nf_red t h)).symm.trans hc).church_rosser
  obtain ⟨A₁, B₁, rfl, _, _⟩ := hv₂.pi_inv
  exact ⟨A₁, B₁, ((nf_normal t h).red_eq hv₁).symm⟩

/-! ### Checking that a term is a type or a kind -/

/-- Check that a term whose type is known is a **type or a kind**, that is, that its type is a
sort.  The type of a term is either the top sort `□` — which is not itself typable, so it has to
be recognized syntactically — or a typable term, and then the only sort it can be convertible to
is `∗`. -/
def checkSort (Γ : Ctx) (hΓ : Wf Γ) (B T : Tm) (hT : Typing Γ B T) :
    Option (Σ' s : Srt, Typing Γ B (Tm.sort s)) :=
  if hbox : T = Tm.sort Srt.box then
    some ⟨Srt.box, by rw [hbox] at hT; exact hT⟩
  else
    if hstar : nf T (sn_of_typeOf hT hΓ) = Tm.sort Srt.star then
      some ⟨Srt.star, hT.conv (Typing.ax Γ)
        (Conv.ofRed (by rw [← hstar]; exact nf_red T (sn_of_typeOf hT hΓ)))⟩
    else none

/-- The check succeeds whenever the term really is a type or a kind. -/
theorem checkSort_isSome {Γ : Ctx} (hΓ : Wf Γ) {B T : Tm} (hT : Typing Γ B T) {s : Srt}
    (hs : Typing Γ B (Tm.sort s)) : (checkSort Γ hΓ B T hT).isSome := by
  rw [checkSort]
  by_cases hbox : T = Tm.sort Srt.box
  · simp [hbox]
  · have hconv : Conv T (Tm.sort s) := hT.unique hs
    have hsstar : s = Srt.star := by
      cases s with
      | star => rfl
      | box =>
          rcases hT.validity hΓ with rfl | ⟨s', hs'⟩
          · exact absurd rfl hbox
          · exact absurd (not_conv_box_of_typing hΓ hs' hconv) id
    subst hsstar
    have hnf : nf T (sn_of_typeOf hT hΓ) = Tm.sort Srt.star :=
      nf_eq_sort (sn_of_typeOf hT hΓ) hconv
    simp [hbox, hnf]

/-- The domain of a product type is a type. -/
theorem pi_dom_star {Γ : Ctx} (hΓ : Wf Γ) {f A B : Tm} (h : Typing Γ f (Tm.pi A B)) :
    Typing Γ A (Tm.sort Srt.star) := by
  obtain ⟨s', t', hr, hA, _, _⟩ := (h.typeTypable hΓ (by simp)).choose_spec.pi_inv
  cases hr
  exact hA

/-- If the normal form of the type of a term is a product, the term has that product as a type. -/
theorem typing_pi_of_nf {Γ : Ctx} (hΓ : Wf Γ) {f F : Tm} (hF : Typing Γ f F) {A B : Tm}
    (h : nf F (sn_of_typeOf hF hΓ) = Tm.pi A B) : Typing Γ f (Tm.pi A B) := by
  have hred : Red F (Tm.pi A B) := by
    rw [← h]; exact nf_red F (sn_of_typeOf hF hΓ)
  rcases hF.validity hΓ with rfl | ⟨s, hs⟩
  · have hself : nf (Tm.sort Srt.box) (sn_of_typeOf hF hΓ) = Tm.sort Srt.box :=
      nf_eq_self _ (fun _ hst => not_step_sort hst)
    rw [hself] at h
    exact absurd h (by simp)
  · exact hF.conv (hs.red hΓ hred) (Conv.ofRed hred)

/-- The last step of the application rule: the type of the argument, already inferred, is
compared with the domain of the product. -/
def inferApp (Γ : Ctx) (hΓ : Wf Γ) (f a A B : Tm) (hFpi : Typing Γ f (Tm.pi A B)) :
    Option (Σ' A' : Tm, Typing Γ a A') → Option (Σ' C : Tm, Typing Γ (Tm.app f a) C)
  | none => none
  | some ⟨A', ha⟩ =>
      if hc : nf A' (sn_of_typeOf ha hΓ) = nf A ((pi_dom_star hΓ hFpi).sn hΓ) then
        some ⟨B[a], Typing.app hFpi (ha.conv (pi_dom_star hΓ hFpi)
          ((conv_iff_normalForm_eq (nf_red A' (sn_of_typeOf ha hΓ))
            (nf_normal A' (sn_of_typeOf ha hΓ)) (nf_red A ((pi_dom_star hΓ hFpi).sn hΓ))
            (nf_normal A ((pi_dom_star hΓ hFpi).sn hΓ))).mpr hc))⟩
      else none

theorem inferApp_isSome {Γ : Ctx} {hΓ : Wf Γ} {f a A B : Tm} {hFpi : Typing Γ f (Tm.pi A B)}
    {A' : Tm} {ha : Typing Γ a A'} (hc : Conv A' A) :
    (inferApp Γ hΓ f a A B hFpi (some ⟨A', ha⟩)).isSome := by
  rw [inferApp]
  have heq : nf A' (sn_of_typeOf ha hΓ) = nf A ((pi_dom_star hΓ hFpi).sn hΓ) :=
    (conv_iff_normalForm_eq (nf_red A' (sn_of_typeOf ha hΓ))
      (nf_normal A' (sn_of_typeOf ha hΓ)) (nf_red A ((pi_dom_star hΓ hFpi).sn hΓ))
      (nf_normal A ((pi_dom_star hΓ hFpi).sn hΓ))).mp hc
  simp [heq]

/-- The application rule: normalize the type of the function part to expose a product, then check
the argument against its domain. -/
def inferAppOf (Γ : Ctx) (hΓ : Wf Γ) (f a F : Tm) (hF : Typing Γ f F)
    (r : Option (Σ' A' : Tm, Typing Γ a A')) : Option (Σ' C : Tm, Typing Γ (Tm.app f a) C) :=
  match hnf : nf F (sn_of_typeOf hF hΓ) with
  | Tm.pi A B => inferApp Γ hΓ f a A B (typing_pi_of_nf hΓ hF hnf) r
  | _ => none

theorem inferAppOf_isSome {Γ : Ctx} {hΓ : Wf Γ} {f a F : Tm} {hF : Typing Γ f F} {A B A' : Tm}
    {ha : Typing Γ a A'} (hnf : nf F (sn_of_typeOf hF hΓ) = Tm.pi A B) (hc : Conv A' A) :
    (inferAppOf Γ hΓ f a F hF (some ⟨A', ha⟩)).isSome := by
  rw [inferAppOf]
  split <;> rename_i heq <;> rw [hnf] at heq <;>
    first
      | (cases heq; exact inferApp_isSome hc)
      | exact absurd heq (by simp)

/-! ### Inference -/

/-- **Type inference for `λΠ`**, correct by construction: if it succeeds it returns a type of the
term *together with a derivation*.  The algorithm is the usual one — look up a variable, check
that the domain of a product or of an abstraction is a type, normalize the type of the function
part of an application to expose a product, and compare the type of the argument with the domain
by the decision procedure for conversion. -/
def infer : (Γ : Ctx) → Wf Γ → (t : Tm) → Option (Σ' A : Tm, Typing Γ t A)
  | Γ, _, Tm.sort Srt.star => some ⟨Tm.sort Srt.box, Typing.ax Γ⟩
  | _, _, Tm.sort Srt.box => none
  | Γ, _, Tm.var n =>
      match h : lookupTy Γ n with
      | none => none
      | some A => some ⟨A, Typing.var (lookupTy_sound h)⟩
  | Γ, hΓ, Tm.pi A B =>
      match infer Γ hΓ A with
      | none => none
      | some ⟨S, hS⟩ =>
          match checkSort Γ hΓ A S hS with
          | none => none
          | some ⟨Srt.box, _⟩ => none
          | some ⟨Srt.star, hA⟩ =>
              match infer (A :: Γ) (Wf.cons hΓ hA) B with
              | none => none
              | some ⟨T, hB⟩ =>
                  match checkSort (A :: Γ) (Wf.cons hΓ hA) B T hB with
                  | none => none
                  | some ⟨t, hBt⟩ => some ⟨Tm.sort t, Typing.pi rfl hA hBt⟩
  | Γ, hΓ, Tm.lam A b =>
      match infer Γ hΓ A with
      | none => none
      | some ⟨S, hS⟩ =>
          match checkSort Γ hΓ A S hS with
          | none => none
          | some ⟨Srt.box, _⟩ => none
          | some ⟨Srt.star, hA⟩ =>
              match infer (A :: Γ) (Wf.cons hΓ hA) b with
              | none => none
              | some ⟨B, hb⟩ =>
                  if hbox : B = Tm.sort Srt.box then none
                  else
                    some ⟨Tm.pi A B, by
                      obtain ⟨t, ht⟩ := hb.typeTypable (Wf.cons hΓ hA) hbox
                      exact Typing.lam (Typing.pi rfl hA ht) hb⟩
  | Γ, hΓ, Tm.app f a =>
      match infer Γ hΓ f with
      | none => none
      | some ⟨F, hF⟩ => inferAppOf Γ hΓ f a F hF (infer Γ hΓ a)

/-! ### Completeness -/

/-- **Inference is complete**: if a term is typable at all, inference succeeds. -/
theorem infer_isSome : ∀ (t : Tm) {Γ : Ctx} (hΓ : Wf Γ) {C : Tm}, Typing Γ t C →
    (infer Γ hΓ t).isSome := by
  intro t
  induction t with
  | sort s =>
      intro Γ hΓ C h
      cases s with
      | star => simp [infer]
      | box => exact absurd h (fun hh => not_typing_box hh)
  | var n =>
      intro Γ hΓ C h
      obtain ⟨A, hl, _⟩ := h.var_inv
      rw [infer]
      split
      · rename_i heq
        rw [lookupTy_complete hl] at heq
        simp at heq
      · simp
  | pi A B ihA ihB =>
      intro Γ hΓ C h
      obtain ⟨s, t, hr, hA, hB, _⟩ := h.pi_inv
      cases hr
      rw [infer]
      split
      · rename_i heq
        have := ihA hΓ hA
        rw [heq] at this
        simp at this
      · rename_i S hS heq
        split
        · rename_i heq'
          have := checkSort_isSome hΓ hS hA
          rw [heq'] at this
          simp at this
        · rename_i hAbox _
          exact Srt.noConfusion (sort_conv_inj (hAbox.unique hA))
        · rename_i hAstar _
          split
          · rename_i heq'
            have := ihB (Wf.cons hΓ hAstar) hB
            rw [heq'] at this
            simp at this
          · rename_i T hT heq'
            split
            · rename_i heq''
              have := checkSort_isSome (Wf.cons hΓ hAstar) hT hB
              rw [heq''] at this
              simp at this
            · simp
  | lam A b ihA ihb =>
      intro Γ hΓ C h
      obtain ⟨B, s, hP, hb, _⟩ := h.lam_inv
      obtain ⟨s', t', hr, hA, hB, _⟩ := hP.pi_inv
      cases hr
      rw [infer]
      split
      · rename_i heq
        have := ihA hΓ hA
        rw [heq] at this
        simp at this
      · rename_i S hS heq
        split
        · rename_i heq'
          have := checkSort_isSome hΓ hS hA
          rw [heq'] at this
          simp at this
        · rename_i hAbox _
          exact Srt.noConfusion (sort_conv_inj (hAbox.unique hA))
        · rename_i hAstar _
          split
          · rename_i heq'
            have := ihb (Wf.cons hΓ hAstar) hb
            rw [heq'] at this
            simp at this
          · rename_i B' hB' heq'
            split
            · rename_i hbox
              subst hbox
              exact ((not_conv_box_of_typing (Wf.cons hΓ hAstar) hB (hb.unique hB'))).elim
            · simp
  | app f a ihf iha =>
      intro Γ hΓ C h
      obtain ⟨A, B, hf, ha, _⟩ := h.app_inv
      rw [infer]
      split
      · rename_i heq
        have := ihf hΓ hf
        rw [heq] at this
        simp at this
      · rename_i F hF heq
        have hconv : Conv F (Tm.pi A B) := hF.unique hf
        obtain ⟨A₁, B₁, hnf⟩ := nf_pi (sn_of_typeOf hF hΓ) hconv
        rcases hr : infer Γ hΓ a with _ | ⟨A', ha'⟩
        · have := iha hΓ ha
          rw [hr] at this
          simp at this
        · refine inferAppOf_isSome hnf ?_
          have h1 : Conv A' A := ha'.unique ha
          have h2 : Conv (Tm.pi A₁ B₁) (Tm.pi A B) := by
            refine Conv.trans ?_ hconv
            refine (Conv.ofRed ?_).symm
            rw [← hnf]
            exact nf_red F (sn_of_typeOf hF hΓ)
          exact h1.trans (pi_inj_left h2).symm

/-! ### Decidability of typability -/

/-- **Typability is decidable**: run the inference algorithm. -/
def decidableTypable (Γ : Ctx) (hΓ : Wf Γ) (t : Tm) : Decidable (∃ A, Typing Γ t A) :=
  match hi : infer Γ hΓ t with
  | some ⟨A, hA⟩ => isTrue ⟨A, hA⟩
  | none => isFalse (by
      rintro ⟨A, hA⟩
      have := infer_isSome t hΓ hA
      rw [hi] at this
      simp at this)

/-- If a term has two types, one of them syntactically different from the other, then that one is
typable by a sort: only the top sort `□` fails to be, and it is a type of a term only when it is
*the* inferred one. -/
theorem typeTypable_of_ne {Γ : Ctx} (hΓ : Wf Γ) {t A₀ A : Tm} (h₀ : Typing Γ t A₀)
    (h : Typing Γ t A) (hne : A ≠ A₀) : ∃ s, Typing Γ A (Tm.sort s) := by
  rcases h.validity hΓ with rfl | hs
  · rcases h₀.validity hΓ with rfl | ⟨s', hs'⟩
    · exact absurd rfl hne
    · exact absurd (not_conv_box_of_typing hΓ hs' (h₀.unique h)) id
  · exact hs

/-- **Type checking is decidable**: whether a term has a *given* type is decidable.  The inferred
type is compared with the given one, which must itself be checked to be a type or a kind, since
the conversion rule may only retype a term at a well-formed type. -/
def decidableTyping (Γ : Ctx) (hΓ : Wf Γ) (t A : Tm) : Decidable (Typing Γ t A) :=
  match hi : infer Γ hΓ t with
  | none => isFalse (fun h => by
      have := infer_isSome t hΓ h
      rw [hi] at this
      simp at this)
  | some ⟨A₀, h₀⟩ =>
      if hA : A = A₀ then isTrue (by rw [hA]; exact h₀)
      else
        match hj : infer Γ hΓ A with
        | none => isFalse (fun h => by
            obtain ⟨s, hs⟩ := typeTypable_of_ne hΓ h₀ h hA
            have := infer_isSome A hΓ hs
            rw [hj] at this
            simp at this)
        | some ⟨S, hS⟩ =>
            match hk : checkSort Γ hΓ A S hS with
            | none => isFalse (fun h => by
                obtain ⟨s, hs⟩ := typeTypable_of_ne hΓ h₀ h hA
                have := checkSort_isSome hΓ hS hs
                rw [hk] at this
                simp at this)
            | some ⟨_, hAs⟩ =>
                if hc : nf A₀ (sn_of_typeOf h₀ hΓ) = nf A (hAs.sn hΓ) then
                  isTrue (h₀.conv hAs
                    ((conv_iff_normalForm_eq (nf_red A₀ (sn_of_typeOf h₀ hΓ))
                      (nf_normal A₀ (sn_of_typeOf h₀ hΓ)) (nf_red A (hAs.sn hΓ))
                      (nf_normal A (hAs.sn hΓ))).mpr hc))
                else isFalse (fun h => hc
                  ((conv_iff_normalForm_eq (nf_red A₀ (sn_of_typeOf h₀ hΓ))
                    (nf_normal A₀ (sn_of_typeOf h₀ hΓ)) (nf_red A (hAs.sn hΓ))
                    (nf_normal A (hAs.sn hΓ))).mp (h₀.unique h)))

/-! ### Deciding well-formedness of a context -/

/-- Check that a context is well formed, returning a proof if it is. -/
def checkWf : (Γ : Ctx) → Option (PLift (Wf Γ))
  | [] => some ⟨Wf.nil⟩
  | A :: Γ =>
      match checkWf Γ with
      | none => none
      | some ⟨hΓ⟩ =>
          match infer Γ hΓ A with
          | none => none
          | some ⟨S, hS⟩ =>
              match checkSort Γ hΓ A S hS with
              | none => none
              | some ⟨_, hAs⟩ => some ⟨Wf.cons hΓ hAs⟩

/-- The check succeeds on a well-formed context. -/
theorem checkWf_isSome : ∀ {Γ : Ctx}, Wf Γ → (checkWf Γ).isSome := by
  intro Γ
  induction Γ with
  | nil => intro _; simp [checkWf]
  | cons A Γ ih =>
      intro h
      obtain ⟨hΓ0, s, hA⟩ : ∃ _ : Wf Γ, ∃ s, Typing Γ A (Tm.sort s) := by
        cases h with
        | cons hΓ0 hA => exact ⟨hΓ0, _, hA⟩
      rw [checkWf]
      split
      · rename_i heq
        have := ih hΓ0
        rw [heq] at this
        simp at this
      · rename_i hΓ heq
        split
        · rename_i heq'
          have := infer_isSome A hΓ hA
          rw [heq'] at this
          simp at this
        · rename_i S hS heq'
          split
          · rename_i heq''
            have := checkSort_isSome hΓ hS hA
            rw [heq''] at this
            simp at this
          · simp

/-- **Well-formedness of a context is decidable.** -/
def decidableWf (Γ : Ctx) : Decidable (Wf Γ) :=
  match hc : checkWf Γ with
  | some h => isTrue h.down
  | none => isFalse (fun h => by
      have := checkWf_isSome h
      rw [hc] at this
      simp at this)

end LambdaPi
