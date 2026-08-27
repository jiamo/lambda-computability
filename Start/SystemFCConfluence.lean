/-
**Confluence of Church-style System F.**

`SystemFC.step` has two redexes, β and type-β, so the Tait–Martin-Löf argument of
`Start/Reduction.lean` has to be redone for the annotated calculus: `SystemFC.pstep` contracts any
set of redexes of either kind at once, `SystemFC.rho` contracts *all* of them, and every parallel
reduct of a term still parallel-reduces to that full development (`SystemFC.pstep_triangle`).  The
diamond property follows, and with the strip lemma so does confluence.

The equations that make this work are those of `Start/SystemFCSubst.lean`; the type-β rule needs
three of them, since a type instantiation has to be pushed through a lifting
(`SystemFC.substTyTm_lift`), through a term substitution (`SystemFC.subst_instTyTm`) and through
another type substitution (`SystemFC.substTyTm_instTyTm`).

* `SystemFC.pstep`, `SystemFC.rho`, `SystemFC.pstep_triangle`, `SystemFC.pstep_diamond`;
* `SystemFC.reducesC` — the reflexive-transitive closure of `SystemFC.step` — with its
  congruences;
* **`SystemFC.confluence`** — the Church-Rosser theorem for the annotated calculus, and
* **`SystemFC.exists_unique_normal_form`** — a typable annotated term has exactly one normal form,
  by confluence and the strong normalization theorem `SystemFC.sn_of_typingC`.
-/

import Start.SystemFCSubst

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SystemFC

open SystemF

/-! ### Parallel reduction -/

/-- Parallel reduction: any set of β- and type-β-redexes may be contracted at once. -/
inductive pstep : FTm → FTm → Prop
  /-- A variable reduces to itself. -/
  | var (i : ℕ) : pstep (FTm.var i) (FTm.var i)
  /-- Under an abstraction. -/
  | lam (A : FTy) {t t' : FTm} : pstep t t' → pstep (FTm.lam A t) (FTm.lam A t')
  /-- In both parts of an application. -/
  | app {a a' b b' : FTm} : pstep a a' → pstep b b' → pstep (FTm.app a b) (FTm.app a' b')
  /-- Contracting a β-redex. -/
  | beta (A : FTy) {t t' u u' : FTm} : pstep t t' → pstep u u' →
      pstep (FTm.app (FTm.lam A t) u) (subst u' 0 t')
  /-- Under a type abstraction. -/
  | tlam {t t' : FTm} : pstep t t' → pstep (FTm.tlam t) (FTm.tlam t')
  /-- In an instantiation. -/
  | tapp {t t' : FTm} (B : FTy) : pstep t t' → pstep (FTm.tapp t B) (FTm.tapp t' B)
  /-- Contracting a type-β-redex. -/
  | tbeta {t t' : FTm} (B : FTy) : pstep t t' →
      pstep (FTm.tapp (FTm.tlam t) B) (instTyTm B t')

theorem pstep_refl (t : FTm) : pstep t t := by
  induction t with
  | var i => exact pstep.var i
  | app a b iha ihb => exact pstep.app iha ihb
  | lam A t ih => exact pstep.lam A ih
  | tlam t ih => exact pstep.tlam ih
  | tapp t B ih => exact pstep.tapp B ih

theorem pstep_of_step {t t' : FTm} (h : step t t') : pstep t t' := by
  induction h with
  | beta A t u => exact pstep.beta A (pstep_refl t) (pstep_refl u)
  | tbeta t B => exact pstep.tbeta B (pstep_refl t)
  | appL b _ ih => exact pstep.app ih (pstep_refl b)
  | appR a _ ih => exact pstep.app (pstep_refl a) ih
  | lam A _ ih => exact pstep.lam A ih
  | tlam _ ih => exact pstep.tlam ih
  | tapp B _ ih => exact pstep.tapp B ih

/-- Parallel reduction is preserved by lifting. -/
theorem pstep_lift {t t' : FTm} (h : pstep t t') (n k : ℕ) :
    pstep (lift n k t) (lift n k t') := by
  induction h generalizing k with
  | var i =>
      by_cases hik : i < k
      · simpa [lift, hik] using pstep.var i
      · simpa [lift, hik] using pstep.var (i + n)
  | lam A _ ih => exact pstep.lam A (ih (k + 1))
  | app _ _ iha ihb => exact pstep.app (iha k) (ihb k)
  | beta A _ _ iht ihu =>
      simp only [lift, lift_subst_zero]
      exact pstep.beta A (iht (k + 1)) (ihu k)
  | tlam _ ih => exact pstep.tlam (ih k)
  | tapp B _ ih => exact pstep.tapp B (ih k)
  | @tbeta u u' B _ ih =>
      have hcomm : lift n k (instTyTm B u') = instTyTm B (lift n k u') :=
        (substTyTm_lift (tyScons B) n k u').symm
      simp only [lift]
      rw [hcomm]
      exact pstep.tbeta B (ih k)

/-- Parallel reduction is preserved by substitution of the type variables. -/
theorem pstep_substTyTm {t t' : FTm} (h : pstep t t') (s : ℕ → FTy) :
    pstep (substTyTm s t) (substTyTm s t') := by
  induction h generalizing s with
  | var i => exact pstep.var i
  | lam A _ ih => exact pstep.lam _ (ih s)
  | app _ _ iha ihb => exact pstep.app (iha s) (ihb s)
  | beta A _ _ iht ihu =>
      simp only [substTyTm, substTyTm_subst]
      exact pstep.beta _ (iht s) (ihu s)
  | tlam _ ih => exact pstep.tlam (ih (ups s))
  | tapp B _ ih => exact pstep.tapp _ (ih s)
  | tbeta B _ ih =>
      simp only [substTyTm, substTyTm_instTyTm]
      exact pstep.tbeta _ (ih (ups s))

theorem pstep_shiftTyTm {t t' : FTm} (h : pstep t t') : pstep (shiftTyTm t) (shiftTyTm t') :=
  pstep_substTyTm h _

/-- Parallel reduction is preserved by substitution, in both arguments. -/
theorem pstep_subst {t t' u u' : FTm} (ht : pstep t t') (hu : pstep u u') (x : ℕ) :
    pstep (subst u x t) (subst u' x t') := by
  induction ht generalizing u u' x with
  | var i =>
      simp only [subst]
      split_ifs <;> first | exact hu | exact pstep.var _
  | lam A _ ih => exact pstep.lam A (ih (pstep_lift hu 1 0) (x + 1))
  | app _ _ iha ihb => exact pstep.app (iha hu x) (ihb hu x)
  | beta A _ _ iht ihu =>
      simp only [subst, subst_subst_zero]
      exact pstep.beta A (iht (pstep_lift hu 1 0) (x + 1)) (ihu hu x)
  | tlam _ ih => exact pstep.tlam (ih (pstep_shiftTyTm hu) x)
  | tapp B _ ih => exact pstep.tapp B (ih hu x)
  | tbeta B _ ih =>
      simp only [subst, subst_instTyTm]
      exact pstep.tbeta B (ih (pstep_shiftTyTm hu) x)

/-! ### The full development -/

/-- The full development: contract every redex present in the term. -/
def rho : FTm → FTm
  | FTm.var i => FTm.var i
  | FTm.lam A t => FTm.lam A (rho t)
  | FTm.app (FTm.lam _ t) u => subst (rho u) 0 (rho t)
  | FTm.app a b => FTm.app (rho a) (rho b)
  | FTm.tlam t => FTm.tlam (rho t)
  | FTm.tapp (FTm.tlam t) B => instTyTm B (rho t)
  | FTm.tapp t B => FTm.tapp (rho t) B

theorem pstep_rho (t : FTm) : pstep t (rho t) := by
  induction t with
  | var i => exact pstep.var i
  | lam A t ih => exact pstep.lam A ih
  | tlam t ih => exact pstep.tlam ih
  | app a b iha ihb =>
      cases a with
      | lam A t =>
          cases iha with
          | lam _ ih => exact pstep.beta A ih ihb
      | var i => exact pstep.app iha ihb
      | app c d => exact pstep.app iha ihb
      | tlam t => exact pstep.app iha ihb
      | tapp t B => exact pstep.app iha ihb
  | tapp t B ih =>
      cases t with
      | tlam u =>
          cases ih with
          | tlam ih' => exact pstep.tbeta B ih'
      | var i => exact pstep.tapp B ih
      | app c d => exact pstep.tapp B ih
      | lam A u => exact pstep.tapp B ih
      | tapp u C => exact pstep.tapp B ih

/-- The triangle property: every parallel reduct of `t` parallel-reduces to `rho t`. -/
theorem pstep_triangle {t t' : FTm} (h : pstep t t') : pstep t' (rho t) := by
  induction h with
  | var i => exact pstep.var i
  | lam A _ ih => exact pstep.lam A ih
  | tlam _ ih => exact pstep.tlam ih
  | beta A _ _ iht ihu => exact pstep_subst iht ihu 0
  | tbeta B _ ih => exact pstep_substTyTm ih _
  | @app a a' b b' ha _ iha ihb =>
      cases a with
      | lam A u =>
          cases ha with
          | lam _ _ =>
              cases iha with
              | lam _ ih => exact pstep.beta A ih ihb
      | var i => exact pstep.app iha ihb
      | app c d => exact pstep.app iha ihb
      | tlam u => exact pstep.app iha ihb
      | tapp u C => exact pstep.app iha ihb
  | @tapp t t' B ht ih =>
      cases t with
      | tlam u =>
          cases ht with
          | tlam _ =>
              cases ih with
              | tlam ih' => exact pstep.tbeta B ih'
      | var i => exact pstep.tapp B ih
      | app c d => exact pstep.tapp B ih
      | lam A u => exact pstep.tapp B ih
      | tapp u C => exact pstep.tapp B ih

/-- The diamond property of parallel reduction. -/
theorem pstep_diamond {t t1 t2 : FTm} (h1 : pstep t t1) (h2 : pstep t t2) :
    ∃ t3, pstep t1 t3 ∧ pstep t2 t3 :=
  ⟨rho t, pstep_triangle h1, pstep_triangle h2⟩

/-! ### Multi-step reduction -/

/-- The reflexive-transitive closure of `SystemFC.step`. -/
inductive reducesC : FTm → FTm → Prop
  /-- No step. -/
  | refl (t : FTm) : reducesC t t
  /-- One step, then more. -/
  | step {t1 t2 t3 : FTm} : step t1 t2 → reducesC t2 t3 → reducesC t1 t3

theorem reducesC_trans {t1 t2 t3 : FTm} (h1 : reducesC t1 t2) (h2 : reducesC t2 t3) :
    reducesC t1 t3 := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact reducesC.step hs (ih h2)

theorem reducesC_one {t t' : FTm} (h : step t t') : reducesC t t' :=
  reducesC.step h (reducesC.refl t')

theorem reducesC_lam (A : FTy) {t t' : FTm} (h : reducesC t t') :
    reducesC (FTm.lam A t) (FTm.lam A t') := by
  induction h with
  | refl => exact reducesC.refl _
  | step hs _ ih => exact reducesC.step (step.lam A hs) ih

theorem reducesC_tlam {t t' : FTm} (h : reducesC t t') :
    reducesC (FTm.tlam t) (FTm.tlam t') := by
  induction h with
  | refl => exact reducesC.refl _
  | step hs _ ih => exact reducesC.step (step.tlam hs) ih

theorem reducesC_tapp (B : FTy) {t t' : FTm} (h : reducesC t t') :
    reducesC (FTm.tapp t B) (FTm.tapp t' B) := by
  induction h with
  | refl => exact reducesC.refl _
  | step hs _ ih => exact reducesC.step (step.tapp B hs) ih

theorem reducesC_appL {a a' : FTm} (b : FTm) (h : reducesC a a') :
    reducesC (FTm.app a b) (FTm.app a' b) := by
  induction h with
  | refl => exact reducesC.refl _
  | step hs _ ih => exact reducesC.step (step.appL b hs) ih

theorem reducesC_appR (a : FTm) {b b' : FTm} (h : reducesC b b') :
    reducesC (FTm.app a b) (FTm.app a b') := by
  induction h with
  | refl => exact reducesC.refl _
  | step hs _ ih => exact reducesC.step (step.appR a hs) ih

theorem reducesC_app {a a' b b' : FTm} (ha : reducesC a a') (hb : reducesC b b') :
    reducesC (FTm.app a b) (FTm.app a' b') :=
  reducesC_trans (reducesC_appL b ha) (reducesC_appR a' hb)

/-- A parallel step is a sequence of ordinary steps. -/
theorem reducesC_of_pstep {t t' : FTm} (h : pstep t t') : reducesC t t' := by
  induction h with
  | var i => exact reducesC.refl _
  | lam A _ ih => exact reducesC_lam A ih
  | app _ _ iha ihb => exact reducesC_app iha ihb
  | tlam _ ih => exact reducesC_tlam ih
  | tapp B _ ih => exact reducesC_tapp B ih
  | beta A _ _ iht ihu =>
      exact reducesC_trans (reducesC_app (reducesC_lam _ iht) ihu)
        (reducesC_one (step.beta _ _ _))
  | tbeta B _ ih =>
      exact reducesC_trans (reducesC_tapp B (reducesC_tlam ih)) (reducesC_one (step.tbeta _ _))

/-! ### Confluence -/

/-- The strip lemma. -/
theorem strip_lemma {t t1 t2 : FTm} (hp : pstep t t1) (hr : reducesC t t2) :
    ∃ t3, reducesC t1 t3 ∧ pstep t2 t3 := by
  induction hr generalizing t1 with
  | refl => exact ⟨t1, reducesC.refl t1, hp⟩
  | step hs _ ih =>
      obtain ⟨u, hu1, hu2⟩ := pstep_diamond hp (pstep_of_step hs)
      obtain ⟨t3, h1, h2⟩ := ih hu2
      exact ⟨t3, reducesC_trans (reducesC_of_pstep hu1) h1, h2⟩

/-- **Church-Rosser for Church-style System F.** -/
theorem confluence {t t1 t2 : FTm} (h1 : reducesC t t1) (h2 : reducesC t t2) :
    ∃ t3, reducesC t1 t3 ∧ reducesC t2 t3 := by
  induction h1 generalizing t2 with
  | refl => exact ⟨t2, h2, reducesC.refl t2⟩
  | @step a b c hs _ ih =>
      obtain ⟨u, hu1, hu2⟩ := strip_lemma (pstep_of_step hs) h2
      obtain ⟨t3, h3, h4⟩ := ih hu1
      exact ⟨t3, h3, reducesC_trans (reducesC_of_pstep hu2) h4⟩

/-- A term is normal when no step applies to it. -/
def NormalC (t : FTm) : Prop := ∀ u, ¬ step t u

theorem eq_of_reducesC_normal {t u : FTm} (h : reducesC t u) (hn : NormalC t) : u = t := by
  cases h with
  | refl => rfl
  | step hs _ => exact absurd hs (hn _)

/-- A strongly normalizing term reduces to a normal form. -/
theorem exists_normal_form_of_snc {t : FTm} (hsn : SNC t) :
    ∃ u, reducesC t u ∧ NormalC u := by
  induction hsn with
  | intro x _ ih =>
      by_cases hn : ∀ u, ¬ step x u
      · exact ⟨x, reducesC.refl x, hn⟩
      · push Not at hn
        obtain ⟨y, hy⟩ := hn
        obtain ⟨u, hu, hnu⟩ := ih y hy
        exact ⟨u, reducesC.step hy hu, hnu⟩

/-- Every typable annotated term reduces to a normal form. -/
theorem exists_normal_form {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    ∃ u, reducesC t u ∧ NormalC u :=
  exists_normal_form_of_snc (sn_of_typingC h)

/-- **A typable term of the annotated calculus has exactly one normal form.** -/
theorem exists_unique_normal_form {Γ : List FTy} {t : FTm} {A : FTy} (h : TypingC Γ t A) :
    ∃! u, reducesC t u ∧ NormalC u := by
  obtain ⟨u, hu, hnu⟩ := exists_normal_form h
  refine ⟨u, ⟨hu, hnu⟩, ?_⟩
  rintro v ⟨hv, hnv⟩
  obtain ⟨w, hw1, hw2⟩ := confluence hv hu
  exact (eq_of_reducesC_normal hw1 hnv).symm.trans (eq_of_reducesC_normal hw2 hnu)

end SystemFC
