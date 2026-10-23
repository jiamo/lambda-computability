import Start.TypeClassSuperFieldHead

/-!
# Series V, big round, run 4, item C1: coherence under `SuperField`
(row M25-TYPECLASS-SUPER-FIELD)

Uniqueness of dictionaries up to β-conversion when every instance is well formed for its
superclass (`SuperField`), without going through normal derivations (which need not exist under
`SuperField`, `normalize_super_superField_fails`).

* `Lambda.conv_substEnv_of_size` — a size-guarded congruence of parallel substitution for
  convertibility: only the arguments whose size is bounded by the size of the substituted term
  need to be convertible (every argument that occurs free qualifies, unused ones do not);
* **`DEnt.conv_superField`** — in a `SuperInstFragment` whose instances satisfy `SuperField`, any
  two dictionaries for one constraint are β-convertible;
* `AElab.conv_superField`, **`coherence_unannotated_superField`** — coherence of the
  unannotated elaboration with `NormalSuperFields` replaced by `SuperField`;
* `loopEnv_conv_eqBase` — non-vacuity in `loopEnv`, where normal derivations do not exist.

Proof of `DEnt.conv_superField`: outer strong induction on the sum of the sizes of the two
dictionaries, inner structural induction on the first derivation.  The second dictionary is put
in head form (`DEnt.headForm`).  At a hypothesis the two projection chains coincide
(`DEntHyp.unique`, `DEntHyp.not_instHead`).  At `sup` the first dictionary is put in head form:
either a chain (as before) or, after a contraction (`DEnt.superMeasure_lt`), a strictly smaller
term (outer induction).  At `inst I ds` the head form of the second side is the same instance
(`no_overlap`) and the context arguments that matter are compared by the inner induction
hypotheses, which are available for the subderivations whatever their size.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-- **Size-guarded congruence of parallel substitution.**  If every pair of arguments whose
combined size is bounded by the combined size of the two substitution results is convertible,
then the two results are convertible. -/
theorem conv_substEnv_of_size : ∀ (t : Lambda) (u v : ℕ → Lambda),
    (∀ k, dsize (u k) + dsize (v k) ≤
        dsize (Lambda.substEnv u t) + dsize (Lambda.substEnv v t) → Lambda.Conv (u k) (v k)) →
    Lambda.Conv (Lambda.substEnv u t) (Lambda.substEnv v t) := by
  intro t
  induction t with
  | var m => intro u v h; exact h m le_rfl
  | app a b iha ihb =>
    intro u v h
    simp only [Lambda.substEnv, dsize] at h ⊢
    obtain ⟨x, h1, h2⟩ := iha u v fun k hk => h k (by omega)
    obtain ⟨y, h3, h4⟩ := ihb u v fun k hk => h k (by omega)
    exact ⟨Lambda.app x y, Lambda.reduces_app h1 h3, Lambda.reduces_app h2 h4⟩
  | lam t ih =>
    intro u v h
    simp only [Lambda.substEnv, dsize] at h ⊢
    obtain ⟨x, h1, h2⟩ := ih (Lambda.envCons u) (Lambda.envCons v) fun k hk => by
      cases k with
      | zero => exact Lambda.conv_refl _
      | succ k =>
        simp only [Lambda.envCons, dsize_lift] at hk ⊢
        obtain ⟨w, hw1, hw2⟩ := h k (by omega)
        exact ⟨_, Lambda.reduces_lift hw1 1 0, Lambda.reduces_lift hw2 1 0⟩
    exact ⟨Lambda.lam x, Lambda.reduces_lam h1, Lambda.reduces_lam h2⟩

/-- **Coherence of dictionaries under `SuperField`**: in a `SuperInstFragment` whose instances
are all well formed for their superclass, any two dictionaries for one constraint are
β-convertible. -/
theorem DEnt.conv_superField {E : Env} {P : List Cstr} {n : ℕ} (hE : EnvGood E)
    (hSF : ∀ I ∈ E.insts, SuperField E I) (hF : SuperInstFragment E P) {C : Cstr}
    {d d' : Lambda} (h : DEnt E P n C d) (h' : DEnt E P n C d') : Lambda.Conv d d' := by
  suffices H : ∀ N, ∀ C d, DEnt E P n C d → ∀ d', DEnt E P n C d' →
      dsize d + dsize d' ≤ N → Lambda.Conv d d' from H _ C d h d' h' le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  -- a chain against an arbitrary dictionary
  have chain : ∀ C e d', DEntHyp E P n C e → DEnt E P n C d' → Lambda.Conv e d' := by
    intro C e d' he h'
    obtain ⟨e', he', hr', _⟩ := DEnt.headForm hE hSF h'
    cases he' with
    | ofHyp he' => rw [DEntHyp.unique hF he he']; exact ⟨e', Lambda.reduces.refl _, hr'⟩
    | inst hI _ _ => exact (DEntHyp.not_instHead hF hI he).elim
  intro C d h
  induction h with
  | hyp hi => intro d' h' _; exact chain _ _ d' (.hyp hi) h'
  | @sup c d₀ τ D dd hc hs hdd _ =>
    intro d' h' hle
    -- head form of the projected dictionary: a chain, or an instance (then contract)
    obtain ⟨f, hf, hrd, hfle⟩ := DEnt.headForm hE hSF hdd
    cases hf with
    | ofHyp hf =>
      obtain ⟨w, h1, h2⟩ := chain _ _ d' (.sup hc hs hf) h'
      exact ⟨w, Lambda.reduces_trans (reduces_recProj hrd) h1, h2⟩
    | @inst I s ds hI hds hall =>
      obtain ⟨sd, hsd, hred2, hlt⟩ := DEnt.superMeasure_lt hE (hSF I hI) hc hs hds hall
      obtain ⟨w, h1, h2⟩ := IHN _ (by simp only [recProj, dsize] at hlt hfle hle ⊢; omega) _ _ hsd d' h' le_rfl
      exact ⟨w, Lambda.reduces_trans (reduces_recProj hrd)
        (Lambda.reduces_trans hred2 h1), h2⟩
  | @inst I s ds hI hds hall ih =>
    intro d' h' hle
    obtain ⟨e', he', hr', hsz'⟩ := DEnt.headForm hE hSF h'
    generalize hC0 : (⟨I.cls, msubst s I.head⟩ : Cstr) = C0 at he'
    cases he' with
    | ofHyp he' => subst hC0; exact (DEntHyp.not_instHead hF hI he').elim
    | @inst I' s' ds' hI' hds' hall' =>
      obtain ⟨hcls, hhead⟩ := Cstr.mk.inj hC0
      obtain ⟨rfl, hctx⟩ := hF.no_overlap I hI I' hI' s s' hcls hhead
      obtain ⟨w, h1, h2⟩ := conv_substEnv_of_size I.dict (fun k => ds.getD k (Lambda.var 0))
        (fun k => ds'.getD k (Lambda.var 0)) (fun k hk => by
          by_cases hk1 : k < ds.length
          · have hkc : k < I.ctxt.length := hds ▸ hk1
            have hk2 : k < ds'.length := hds'.symm ▸ hkc
            have hd2 := hall' k hk2 hkc
            rw [← hctx _ (List.getElem_mem hkc)] at hd2
            rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2] at hk ⊢
            exact ih k hk1 hkc _ hd2 (by omega)
          · have hk2 : ¬ k < ds'.length := by omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hk1),
              List.getElem?_eq_none (Nat.le_of_not_lt hk2), Option.getD_none]
            exact Lambda.conv_refl _)
      exact ⟨w, h1, Lambda.reduces_trans hr' h2⟩

/-- **Coherence of annotated elaboration up to β under `SuperField`.** -/
theorem AElab.conv_superField {E : Env} {P : List Cstr} (hE : EnvGood E)
    (hSF : ∀ I ∈ E.insts, SuperField E I) (hF : SuperInstFragment E P)
    {Γ Γ' : List Mty} {e : ASexp} {τ τ' : Mty} {t t' : Lambda} (h : AElab E P Γ e τ t)
    (h' : AElab E P Γ' e τ' t') (hlen : Γ.length = Γ'.length) : Lambda.Conv t t' := by
  induction h generalizing Γ' τ' t' with
  | var _ => cases h'; exact Lambda.conv_refl _
  | lam _ ih =>
      cases h' with
      | lam h' =>
          obtain ⟨u, h1, h2⟩ := ih h' (by simp [hlen])
          exact ⟨Lambda.lam u, Lambda.reduces_lam h1, Lambda.reduces_lam h2⟩
  | app _ _ ihf iha =>
      cases h' with
      | app hf' ha' =>
          obtain ⟨u, h1, h2⟩ := ihf hf' hlen
          obtain ⟨v, h3, h4⟩ := iha ha' hlen
          exact ⟨Lambda.app u v, Lambda.reduces_app h1 h3, Lambda.reduces_app h2 h4⟩
  | @method Γ c j D m τ d hc hj hd =>
      cases h' with
      | method hc' hj' hd' =>
          rw [hc] at hc'
          cases hc'
          rw [← hlen] at hd'
          obtain ⟨u, h1, h2⟩ := DEnt.conv_superField hE hSF hF hd hd'
          exact ⟨_, reduces_recProj h1, reduces_recProj h2⟩

/-- **Coherence for unambiguous judgements under `SuperField`**: in a `SuperInstFragment` whose
instances are well formed for their superclass, an unambiguous derivable judgement has an
elaboration, and any two elaborations are β-convertible.  This is
`coherence_unannotated_superInst` with `NormalSuperFields` replaced by `SuperField`. -/
theorem coherence_unannotated_superField {E : Env} {P : List Cstr} (hE : EnvGood E)
    (hSF : ∀ I ∈ E.insts, SuperField E I) (hF : SuperInstFragment E P)
    {Γ : List Mty} {e : Sexp} {τ : Mty} (hB : Bidi E false Γ e τ) (hS : STyping E P Γ e τ) :
    (∃ t, ElabS E P Γ e τ t) ∧
      ∀ t t', ElabS E P Γ e τ t → ElabS E P Γ e τ t' → Lambda.Conv t t' := by
  refine ⟨?_, ?_⟩
  · obtain ⟨a, t, he, ha⟩ := hS.annotate
    exact ⟨t, a, he, ha⟩
  · rintro t t' ⟨a, he, ha⟩ ⟨a', he', ha'⟩
    obtain ⟨rfl, _⟩ := hB.annot_unique he he' ha ha' (fun _ => ⟨rfl, rfl⟩)
    exact AElab.conv_superField hE hSF hF ha ha' rfl

/-- **Non-vacuity** in `loopEnv`, where `normalize_super_superField_fails` shows that `Eq Base`
has no normal derivation: every dictionary for `Eq Base` is β-convertible to the superclass
projection of the `Ord Base` dictionary. -/
theorem loopEnv_conv_eqBase {n : ℕ} {d : Lambda} (h : DEnt loopEnv [] n ⟨0, Mty.base⟩ d) :
    Lambda.Conv d (recProj 2 0 ordBaseDict) :=
  DEnt.conv_superField loopEnv_good loopEnv_superField loopEnv_superInstFragment h
    (loopEnv_supInst [] n)

end TypeClass
