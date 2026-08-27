/-
**Strong normalization of `λΠ`.**

`Start/LambdaPiSimple.lean` erases a dependent derivation to a simply typed one: a term typable in
`λΠ` is typable, as a raw term, in the simply typed calculus over the skeletons.  What remains is
to normalize the *simply typed* calculus, and this file does it by Tait's method of reducibility,
adapted to the fact that β-reduction of `λΠ` also reduces inside the type annotations of
abstractions and inside products.

* `LambdaPi.SN` — strong normalization: the reduction relation is well founded above the term;
* `LambdaPi.step_rename_inv` — a renaming reflects reduction: every step out of `rename ρ t` is
  the renaming of a step out of `t`; hence `LambdaPi.sn_rename`;
* `LambdaPi.Reducible` — Tait's reducibility predicate, in its Kripke form, quantifying over
  renamings at the arrow type, which is what makes it stable under weakening
  (`LambdaPi.Reducible.rename`);
* `LambdaPi.cr` — the three candidate conditions CR1, CR2, CR3;
* `LambdaPi.red_lam_app` — the abstraction lemma, by a threefold induction on the annotation, the
  body and the argument;
* `LambdaPi.STyping.reducible` — the fundamental lemma, and `LambdaPi.sn_of_styping`;
* `LambdaPi.Typing.sn` — **strong normalization for `λΠ`**, with the corollary
  `LambdaPi.Typing.hasNormalForm` that every typable term has a normal form.
-/

import Start.LambdaPiSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

/-! ### Strong normalization -/

/-- A term is **strongly normalizing** when β-reduction is well founded above it. -/
def SN (t : Tm) : Prop := Acc (fun a b => Step b a) t

theorem SN.intro {t : Tm} (h : ∀ t', Step t t' → SN t') : SN t := Acc.intro t h

theorem SN.step {t t' : Tm} (h : SN t) (hs : Step t t') : SN t' := h.inv hs

theorem not_step_var {n : ℕ} {t : Tm} : ¬ Step (Tm.var n) t := by intro h; cases h

theorem not_step_sort {s : Srt} {t : Tm} : ¬ Step (Tm.sort s) t := by intro h; cases h

theorem sn_var (n : ℕ) : SN (Tm.var n) := SN.intro fun _ h => absurd h not_step_var

theorem sn_sort (s : Srt) : SN (Tm.sort s) := SN.intro fun _ h => absurd h not_step_sort

/-- If a step-preserving map sends `t` to a strongly normalizing term, then `t` is strongly
normalizing. -/
theorem sn_of_map (f : Tm → Tm) (hf : ∀ a b, Step a b → Step (f a) (f b)) :
    ∀ {s : Tm}, SN s → ∀ t : Tm, f t = s → SN t := by
  intro s hs
  induction hs with
  | intro s _ ih =>
      intro t ht
      exact SN.intro fun t' hstep => ih (f t') (by rw [← ht]; exact hf t t' hstep) t' rfl

theorem sn_app_left {t u : Tm} (h : SN (Tm.app t u)) : SN t :=
  sn_of_map (fun a => Tm.app a u) (fun _ _ hs => Step.appL u hs) h t rfl

theorem sn_of_sn_subst {σ : ℕ → Tm} {t : Tm} (h : SN (subst σ t)) : SN t :=
  sn_of_map (subst σ) (fun _ _ hs => hs.subst σ) h t rfl

/-- A product of two strongly normalizing terms is strongly normalizing. -/
theorem sn_pi {A B : Tm} (hA : SN A) (hB : SN B) : SN (Tm.pi A B) := by
  induction hA generalizing B with
  | intro A hAacc ihA =>
      induction hB with
      | intro B hBacc ihB =>
          refine SN.intro fun w hw => ?_
          cases hw with
          | piL _ hst => exact ihA _ hst (Acc.intro B hBacc)
          | piR _ hst => exact ihB _ hst

/-- An abstraction whose annotation and body are strongly normalizing is strongly
normalizing. -/
theorem sn_lam {A b : Tm} (hA : SN A) (hb : SN b) : SN (Tm.lam A b) := by
  induction hA generalizing b with
  | intro A hAacc ihA =>
      induction hb with
      | intro b hbacc ihb =>
          refine SN.intro fun w hw => ?_
          cases hw with
          | lamL _ hst => exact ihA _ hst (Acc.intro b hbacc)
          | lamR _ hst => exact ihb _ hst

/-! ### Renamings reflect reduction -/

/-- **A renaming reflects reduction**: a step out of a renamed term is the renaming of a step out
of the term itself.  No injectivity of the renaming is needed: renaming does not change the shape
of a term. -/
theorem step_rename_inv {s u : Tm} (h : Step s u) :
    ∀ (ρ : ℕ → ℕ) (t : Tm), s = rename ρ t → ∃ u', u = rename ρ u' ∧ Step t u' := by
  induction h with
  | beta A b a =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | lam A0 b0 => simp at ht
      | pi A0 B0 => simp at ht
      | app f a0 =>
          rw [rename_app] at ht
          obtain ⟨hf, ha⟩ := Tm.app.inj ht
          cases f with
          | var n => simp at hf
          | sort s => simp at hf
          | app f0 a1 => simp at hf
          | pi A1 B1 => simp at hf
          | lam A1 b1 =>
              rw [rename_lam] at hf
              obtain ⟨hA, hb⟩ := Tm.lam.inj hf
              subst hA; subst hb; subst ha
              exact ⟨b1[a0], (inst_rename ρ a0 b1).symm, Step.beta A1 b1 a0⟩
  | @appL f f' a _ ih =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | lam A0 b0 => simp at ht
      | pi A0 B0 => simp at ht
      | app f0 a0 =>
          rw [rename_app] at ht
          obtain ⟨hf, ha⟩ := Tm.app.inj ht
          obtain ⟨f'', rfl, hst⟩ := ih ρ f0 hf
          exact ⟨Tm.app f'' a0, by rw [rename_app, ha], Step.appL a0 hst⟩
  | @appR f a a' _ ih =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | lam A0 b0 => simp at ht
      | pi A0 B0 => simp at ht
      | app f0 a0 =>
          rw [rename_app] at ht
          obtain ⟨hf, ha⟩ := Tm.app.inj ht
          obtain ⟨a'', rfl, hst⟩ := ih ρ a0 ha
          exact ⟨Tm.app f0 a'', by rw [rename_app, hf], Step.appR f0 hst⟩
  | @lamL A A' b _ ih =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | app f0 a0 => simp at ht
      | pi A0 B0 => simp at ht
      | lam A0 b0 =>
          rw [rename_lam] at ht
          obtain ⟨hA, hb⟩ := Tm.lam.inj ht
          obtain ⟨A'', rfl, hst⟩ := ih ρ A0 hA
          exact ⟨Tm.lam A'' b0, by rw [rename_lam, hb], Step.lamL b0 hst⟩
  | @lamR A b b' _ ih =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | app f0 a0 => simp at ht
      | pi A0 B0 => simp at ht
      | lam A0 b0 =>
          rw [rename_lam] at ht
          obtain ⟨hA, hb⟩ := Tm.lam.inj ht
          obtain ⟨b'', rfl, hst⟩ := ih (upr ρ) b0 hb
          exact ⟨Tm.lam A0 b'', by rw [rename_lam, hA], Step.lamR A0 hst⟩
  | @piL A A' B _ ih =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | app f0 a0 => simp at ht
      | lam A0 b0 => simp at ht
      | pi A0 B0 =>
          rw [rename_pi] at ht
          obtain ⟨hA, hB⟩ := Tm.pi.inj ht
          obtain ⟨A'', rfl, hst⟩ := ih ρ A0 hA
          exact ⟨Tm.pi A'' B0, by rw [rename_pi, hB], Step.piL B0 hst⟩
  | @piR A B B' _ ih =>
      intro ρ t ht
      cases t with
      | var n => simp at ht
      | sort s => simp at ht
      | app f0 a0 => simp at ht
      | lam A0 b0 => simp at ht
      | pi A0 B0 =>
          rw [rename_pi] at ht
          obtain ⟨hA, hB⟩ := Tm.pi.inj ht
          obtain ⟨B'', rfl, hst⟩ := ih (upr ρ) B0 hB
          exact ⟨Tm.pi A0 B'', by rw [rename_pi, hA], Step.piR A0 hst⟩

/-- Renaming preserves strong normalization. -/
theorem sn_rename {t : Tm} (h : SN t) (ρ : ℕ → ℕ) : SN (rename ρ t) := by
  induction h with
  | intro t _ ih =>
      refine SN.intro fun u hu => ?_
      obtain ⟨u', rfl, hst⟩ := step_rename_inv hu ρ t rfl
      exact ih u' hst

/-! ### Reducibility -/

/-- A term is *not an abstraction* when applying it cannot create a redex. -/
def NotAbs : Tm → Prop
  | Tm.lam _ _ => False
  | _ => True

theorem notAbs_var (n : ℕ) : NotAbs (Tm.var n) := trivial
theorem notAbs_app (f a : Tm) : NotAbs (Tm.app f a) := trivial

theorem notAbs_rename {t : Tm} (h : NotAbs t) (ρ : ℕ → ℕ) : NotAbs (rename ρ t) := by
  cases t with
  | lam A b => exact h.elim
  | var n => exact trivial
  | sort s => exact trivial
  | app f a => exact trivial
  | pi A B => exact trivial

/-- **Tait's reducibility predicate**, in Kripke form: at an arrow type a term is reducible when
all of its renamings send reducible arguments to reducible results.  Quantifying over the
renamings is what makes reducibility stable under weakening, which the substitution under a
binder needs. -/
def Reducible : STy → Tm → Prop
  | STy.base, t => SN t
  | STy.arrow σ τ, t => ∀ (ρ : ℕ → ℕ) (u : Tm), Reducible σ u → Reducible τ (Tm.app (rename ρ t) u)

@[simp] theorem reducible_base (t : Tm) : Reducible STy.base t ↔ SN t := Iff.rfl

@[simp] theorem reducible_arrow (σ τ : STy) (t : Tm) :
    Reducible (STy.arrow σ τ) t ↔
      ∀ (ρ : ℕ → ℕ) (u : Tm), Reducible σ u → Reducible τ (Tm.app (rename ρ t) u) := Iff.rfl

/-- Reducibility is stable under renaming. -/
theorem Reducible.rename {σ : STy} : ∀ {t : Tm}, Reducible σ t → ∀ ρ : ℕ → ℕ,
    Reducible σ (LambdaPi.rename ρ t) := by
  induction σ with
  | base => intro t h ρ; exact sn_rename h ρ
  | arrow σ τ _ _ =>
      intro t h ρ ρ' u hu
      rw [rename_rename]
      exact h _ u hu

/-- The three reducibility-candidate conditions: reducible terms are strongly normalizing (CR1),
reducibility is preserved by reduction (CR2), and a term that is not an abstraction and all of
whose reducts are reducible is reducible (CR3). -/
theorem cr (σ : STy) :
    (∀ t, Reducible σ t → SN t) ∧
    (∀ t t', Reducible σ t → Step t t' → Reducible σ t') ∧
    (∀ t, NotAbs t → (∀ t', Step t t' → Reducible σ t') → Reducible σ t) := by
  induction σ with
  | base => exact ⟨fun _ h => h, fun _ _ h hs => h.step hs, fun _ _ h => SN.intro h⟩
  | arrow σ τ ihσ ihτ =>
      obtain ⟨ihσ1, ihσ2, ihσ3⟩ := ihσ
      obtain ⟨ihτ1, ihτ2, ihτ3⟩ := ihτ
      have hvar : Reducible σ (Tm.var 0) :=
        ihσ3 _ (notAbs_var 0) fun _ h => absurd h not_step_var
      have key : ∀ s : Tm, NotAbs s → (∀ s', Step s s' → Reducible (STy.arrow σ τ) s') →
          ∀ u : Tm, Reducible σ u → Reducible τ (Tm.app s u) := by
        intro s hn h u hu
        have hsn : SN u := ihσ1 u hu
        induction hsn with
        | intro u hacc ihu =>
            refine ihτ3 _ (notAbs_app s u) fun w hw => ?_
            cases hw with
            | beta A b a => exact hn.elim
            | @appL _ s' _ hstep =>
                have := h s' hstep id u hu
                rwa [rename_id] at this
            | @appR _ _ u' hstep => exact ihu u' hstep (ihσ2 _ _ hu hstep)
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        have := ihτ1 _ (ht id (Tm.var 0) hvar)
        rw [rename_id] at this
        exact sn_app_left this
      · intro t t' ht hs ρ u hu
        exact ihτ2 _ _ (ht ρ u hu) (Step.appL u (hs.rename ρ))
      · intro t hn h ρ u hu
        refine key (LambdaPi.rename ρ t) (notAbs_rename hn ρ) (fun s' hs' => ?_) u hu
        obtain ⟨s'', rfl, hst⟩ := step_rename_inv hs' ρ t rfl
        exact (h s'' hst).rename ρ

theorem cr1 (σ : STy) {t : Tm} (h : Reducible σ t) : SN t := (cr σ).1 t h

theorem cr2 (σ : STy) {t t' : Tm} (h : Reducible σ t) (hs : Step t t') : Reducible σ t' :=
  (cr σ).2.1 t t' h hs

theorem cr3 (σ : STy) {t : Tm} (hn : NotAbs t) (h : ∀ t', Step t t' → Reducible σ t') :
    Reducible σ t := (cr σ).2.2 t hn h

theorem reducible_var (σ : STy) (n : ℕ) : Reducible σ (Tm.var n) :=
  cr3 σ (notAbs_var n) fun _ h => absurd h not_step_var

/-! ### The abstraction lemma -/

theorem red_lam_app_aux (σ τ : STy) :
    ∀ A : Tm, SN A → ∀ b : Tm, SN b → (∀ v, Reducible σ v → Reducible τ (b[v])) →
      ∀ u : Tm, SN u → Reducible σ u → Reducible τ (Tm.app (Tm.lam A b) u) := by
  intro A hA
  induction hA with
  | intro A hAacc ihA =>
      intro b hb
      induction hb with
      | intro b hbacc ihb =>
          intro hsub u hu
          induction hu with
          | intro u huacc ihu =>
              intro hru
              refine cr3 τ (notAbs_app _ _) fun w hw => ?_
              cases hw with
              | beta _ _ _ => exact hsub u hru
              | @appL _ f' _ hstep =>
                  cases hstep with
                  | @lamL _ A' _ hst =>
                      exact ihA A' hst b (Acc.intro b hbacc) hsub u (Acc.intro u huacc) hru
                  | @lamR _ _ b' hst =>
                      exact ihb b' hst (fun v hv => cr2 τ (hsub v hv) (hst.subst _)) u
                        (Acc.intro u huacc) hru
              | @appR _ _ u' hstep => exact ihu u' hstep (cr2 σ hru hstep)

/-- **Abstraction lemma**: if substituting a reducible term for the bound variable of the body
gives a reducible term, then applying the abstraction to a reducible argument is reducible. -/
theorem red_lam_app {σ τ : STy} {A b : Tm} (hA : SN A) (hb : SN b)
    (hsub : ∀ v, Reducible σ v → Reducible τ (b[v])) {u : Tm} (hu : Reducible σ u) :
    Reducible τ (Tm.app (Tm.lam A b) u) :=
  red_lam_app_aux σ τ A hA b hb hsub u (cr1 σ hu) hu

/-! ### The fundamental lemma -/

/-- Instantiating a lifted substitution. -/
theorem inst_subst_up (γ : ℕ → Tm) (v b : Tm) : (subst (up γ) b)[v] = subst (scons v γ) b := by
  simp only [inst, subst_subst]
  refine subst_congr (fun n => ?_) b
  cases n with
  | zero => rfl
  | succ n => simp [subst_rename]

/-- A reducible substitution stays reducible under a binder. -/
theorem reducible_up {Γs : List STy} {γ : ℕ → Tm}
    (hγ : ∀ n, Reducible (Γs.getD n STy.base) (γ n)) (X : STy) :
    ∀ n, Reducible ((X :: Γs).getD n STy.base) (up γ n) := by
  intro n
  cases n with
  | zero => simpa using reducible_var X 0
  | succ n => simpa using (hγ n).rename Nat.succ

/-- **Fundamental lemma of the reducibility method**: a simply typed term is reducible under any
reducible substitution. -/
theorem STyping.reducible {Γs : List STy} {t : Tm} {σ : STy} (h : STyping Γs t σ) :
    ∀ γ : ℕ → Tm, (∀ n, Reducible (Γs.getD n STy.base) (γ n)) → Reducible σ (subst γ t) := by
  induction h with
  | sort Γs s => intro γ _; simpa using sn_sort s
  | var Γs n => intro γ hγ; exact hγ n
  | @pi Γs A B σ' τ' _ _ ihA ihB =>
      intro γ hγ
      have hA := cr1 σ' (ihA γ hγ)
      have hB := cr1 τ' (ihB (up γ) (reducible_up hγ _))
      simpa using sn_pi hA hB
  | @lam Γs A b σ' τ' _ _ ihA ihb =>
      intro γ hγ
      rw [subst_lam]
      intro ρ u hu
      rw [rename_lam]
      have hAsn : SN (rename ρ (subst γ A)) := sn_rename (cr1 σ' (ihA γ hγ)) ρ
      have hbsn : SN (rename (upr ρ) (subst (up γ) b)) :=
        sn_rename (cr1 τ' (ihb (up γ) (reducible_up hγ _))) (upr ρ)
      refine red_lam_app hAsn hbsn (fun v hv => ?_) hu
      have hrw : rename (upr ρ) (subst (up γ) b) = subst (up fun k => rename ρ (γ k)) b := by
        rw [rename_subst]
        exact subst_congr (rename_up_subst ρ γ) b
      rw [hrw, inst_subst_up]
      refine ihb (scons v fun k => rename ρ (γ k)) (fun n => ?_)
      cases n with
      | zero => simpa using hv
      | succ n => simpa using (hγ n).rename ρ
  | @app Γs f a σ' τ' _ _ ihf iha =>
      intro γ hγ
      have := ihf γ hγ id (subst γ a) (iha γ hγ)
      rw [rename_id] at this
      simpa using this

/-- Every simply typable raw term is strongly normalizing. -/
theorem sn_of_styping {Γs : List STy} {t : Tm} {σ : STy} (h : STyping Γs t σ) : SN t := by
  have hred := h.reducible ids (fun n => reducible_var _ n)
  rw [subst_ids] at hred
  exact cr1 σ hred

/-! ### Strong normalization of `λΠ` -/

/-- **Strong normalization for `λΠ`**: in a well-formed context, every typable term is strongly
normalizing. -/
theorem Typing.sn {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) : SN t :=
  sn_of_styping (h.styping hΓ)

/-- A term is in **normal form** when no reduction applies to it. -/
def Normal (t : Tm) : Prop := ∀ t', ¬ Step t t'

/-- A term **has a normal form** when it reduces to a term to which no reduction applies. -/
def HasNormalForm (t : Tm) : Prop := ∃ u, Red t u ∧ Normal u

/-- A strongly normalizing term has a normal form. -/
theorem hasNormalForm_of_sn {t : Tm} (h : SN t) : HasNormalForm t := by
  induction h with
  | intro t _ ih =>
      by_cases hn : ∃ t', Step t t'
      · obtain ⟨t', ht'⟩ := hn
        obtain ⟨u, hu, hnu⟩ := ih t' ht'
        exact ⟨u, Red.head ht' hu, hnu⟩
      · exact ⟨t, Red.refl t, fun t' ht' => hn ⟨t', ht'⟩⟩

/-- Every term typable in a well-formed context has a normal form. -/
theorem Typing.hasNormalForm {Γ : Ctx} {t A : Tm} (h : Typing Γ t A) (hΓ : Wf Γ) :
    HasNormalForm t := hasNormalForm_of_sn (h.sn hΓ)

end LambdaPi
