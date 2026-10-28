/-
**Martin-Löf type theory: normalization for full reduction** — milestone M30
(`M30-MLTT-WN`).

The logical relation of `Start/MLTTLogRel.lean` is defined for any generic equality.  Here it is
instantiated with the declarative equality strengthened by normalization: equal types and terms
are declaratively equal **and have normal forms** under full reduction, and equal neutral terms
have neutral normal forms (`MLTT.wnEq`).  The fundamental theorem at this instance gives full
normalization.

* `MLTT.WN`, `MLTT.WNe` — reduction (`FSteps`) to a normal form, to a neutral normal form;
* `MLTT.fsteps_beta_expand` — a reduction of `(λ c) a` to a normal form passes through `c[a]`;
* `MLTT.WN.of_eta` — a weak head normal term of a product type whose η-expansion has a normal
  form has a normal form (the `η` field of the generic equality);
* `MLTT.wnEq` — **the normalizing generic equality**;
* **`MLTT.HasTy.wn`**, **`MLTT.WfTy.wn`** — **every typable term and every well-formed type of
  MLTT has a normal form** under full `β`/`natrec` reduction (weak normalization).
-/

import Start.MLTTFullRed

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Weak normalization -/

/-- `t` reduces to a normal form. -/
def WN (t : Tm) : Prop := ∃ n, FSteps t n ∧ Nf n

/-- `t` reduces to a neutral normal form. -/
def WNe (t : Tm) : Prop := ∃ n, FSteps t n ∧ NeNf n

theorem WN.of_fsteps {t u : Tm} (h : FSteps t u) (hu : WN u) : WN t := by
  obtain ⟨n, hn, hnf⟩ := hu
  exact ⟨n, h.trans hn, hnf⟩

theorem WNe.wn {t : Tm} (h : WNe t) : WN t := by
  obtain ⟨n, hn, hnf⟩ := h
  exact ⟨n, hn, NfB.ne hnf⟩

theorem WN.rename {t : Tm} (h : WN t) (ρ : ℕ → ℕ) : WN (MLTT.rename ρ t) := by
  obtain ⟨n, hn, hnf⟩ := h
  exact ⟨_, hn.rename ρ, hnf.rename ρ⟩

theorem WNe.rename {t : Tm} (h : WNe t) (ρ : ℕ → ℕ) : WNe (MLTT.rename ρ t) := by
  obtain ⟨n, hn, hnf⟩ := h
  exact ⟨_, hn.rename ρ, hnf.rename ρ⟩

theorem WN.atom_univ (l : ℕ) : WN (Tm.univ l) := ⟨_, .refl, NfB.univ l⟩
theorem WN.atom_nat : WN Tm.nat := ⟨_, .refl, NfB.nat⟩
theorem WN.atom_empty : WN Tm.empty := ⟨_, .refl, NfB.empty⟩
theorem WN.atom_zero : WN Tm.zero := ⟨_, .refl, NfB.zero⟩
theorem WNe.var (i : ℕ) : WNe (Tm.var i) := ⟨_, .refl, NfB.var i⟩

theorem WN.pi {F G : Tm} (hF : WN F) (hG : WN G) : WN (Tm.pi F G) := by
  obtain ⟨n, hn, hnf⟩ := hF
  obtain ⟨m, hm, hmf⟩ := hG
  exact ⟨_, FSteps.pi hn hm, NfB.pi hnf hmf⟩

theorem WN.lam {b : Tm} (h : WN b) : WN (Tm.lam b) := by
  obtain ⟨n, hn, hnf⟩ := h
  exact ⟨_, FSteps.lam hn, NfB.lam hnf⟩

theorem WN.succ {n : Tm} (h : WN n) : WN (Tm.succ n) := by
  obtain ⟨m, hm, hmf⟩ := h
  exact ⟨_, FSteps.succ hm, NfB.succ hmf⟩

theorem WNe.app {f a : Tm} (hf : WNe f) (ha : WN a) : WNe (Tm.app f a) := by
  obtain ⟨n, hn, hnf⟩ := hf
  obtain ⟨m, hm, hmf⟩ := ha
  exact ⟨_, FSteps.app hn hm, NfB.app hnf hmf⟩

theorem WNe.natrec {P z s n : Tm} (hP : WN P) (hz : WN z) (hs : WN s) (hn : WNe n) :
    WNe (Tm.natrec P z s n) := by
  obtain ⟨P', hP, hPf⟩ := hP
  obtain ⟨z', hz, hzf⟩ := hz
  obtain ⟨s', hs, hsf⟩ := hs
  obtain ⟨n', hn, hnf⟩ := hn
  exact ⟨_, FSteps.natrec hP hz hs hn, NfB.natrec hPf hzf hsf hnf⟩

theorem WNe.emptyrec {P e : Tm} (hP : WN P) (he : WNe e) : WNe (Tm.emptyrec P e) := by
  obtain ⟨P', hP, hPf⟩ := hP
  obtain ⟨e', he, hef⟩ := he
  exact ⟨_, FSteps.emptyrec hP he, NfB.emptyrec hPf hef⟩

/-! ### Normal forms through β-redexes and η-expansions -/

/-- A reduction of `(λ c) a` to a normal form can be taken through `c[a]`. -/
theorem fsteps_beta_expand {c a n : Tm} (h : FSteps (app (lam c) a) n) (hn : Nf n) :
    FSteps (c[a]) n := by
  generalize e : app (lam c) a = x at h
  induction h using Relation.ReflTransGen.head_induction_on generalizing c a with
  | refl =>
      subst e
      cases hn with
      | ne h =>
          cases h with
          | app hf _ => cases hf
  | head hs hrest ih =>
      subst e
      cases hs with
      | beta => exact hrest
      | appL _ hf =>
          cases hf with
          | lam hc => exact Relation.ReflTransGen.head (hc.subst _) (ih rfl)
      | appR _ ha => exact (FSteps.inst_arg c (.single ha)).trans (ih rfl)

/-- The reducts of an application of a neutral term. -/
theorem fsteps_app_neutral {x v m : Tm} (hx : Neutral x) (h : FSteps (app x v) m) :
    ∃ x' v', m = app x' v' ∧ FSteps x x' ∧ FSteps v v' ∧ Neutral x' := by
  induction h with
  | refl => exact ⟨x, v, rfl, .refl, .refl, hx⟩
  | tail _ hs ih =>
      obtain ⟨x', v', rfl, hxx, hvv, hx'⟩ := ih
      cases hs with
      | beta => cases hx'
      | appL _ h => exact ⟨_, v', rfl, hxx.tail h, hvv, hx'.fstep h⟩
      | appR _ h => exact ⟨x', _, rfl, hxx, hvv.tail h, hx'⟩

/-- **The η-field**: a weak head normal term of a product type whose η-expansion has a normal
form has a normal form. -/
theorem WN.of_eta {Γ : Ctx} {f F G : Tm} (hf : HasTy Γ f (Tm.pi F G)) (hw : Whnf f)
    (h : WN (app (shift f) (Tm.var 0))) : WN f := by
  obtain ⟨n, hs, hn⟩ := h
  rcases Whnf.pi_canon hf hw with ⟨b, rfl⟩ | hne
  · have := fsteps_beta_expand hs hn
    rw [show (MLTT.rename (upr Nat.succ) b)[Tm.var 0] = b from shift_inst_rename b] at this
    exact WN.lam ⟨n, this, hn⟩
  · obtain ⟨x', v', rfl, hxx, -, -⟩ := fsteps_app_neutral (hne.rename Nat.succ) hs
    obtain ⟨f', hff, rfl⟩ := FSteps.unrename hxx
    cases hn with
    | ne h =>
        cases h with
        | app hx _ => exact ⟨f', hff, NfB.ne (NfB.unrename f' hx)⟩

/-! ### The normalizing generic equality -/

/-- **The normalizing generic equality**: declarative equality, with normal forms. -/
def wnEq : GenEq where
  ty Γ A B := TyEq Γ A B ∧ WN A ∧ WN B
  tm Γ t u A := DEq Γ t u A ∧ WN t ∧ WN u
  ne Γ k l A := DEq Γ k l A ∧ WNe k ∧ WNe l
  ne_tm := fun ⟨h, hk, hl⟩ => ⟨h, hk.wn, hl.wn⟩
  ty_eq := fun h => h.1
  tm_eq := fun h => h.1
  ne_eq := fun h => h.1
  univ := fun ⟨h, ha, hb⟩ => ⟨Der.elEq h, ha, hb⟩
  ty_symm := fun ⟨h, ha, hb⟩ => ⟨Der.symmT h, hb, ha⟩
  ty_trans := fun ⟨h, ha, _⟩ ⟨h', _, hc⟩ => ⟨Der.transT h h', ha, hc⟩
  tm_symm := fun ⟨h, ha, hb⟩ => ⟨Der.symm h, hb, ha⟩
  tm_trans := fun ⟨h, ha, _⟩ ⟨h', _, hc⟩ => ⟨Der.trans h h', ha, hc⟩
  ne_symm := fun ⟨h, ha, hb⟩ => ⟨Der.symm h, hb, ha⟩
  ne_trans := fun ⟨h, ha, _⟩ ⟨h', _, hc⟩ => ⟨Der.trans h h', ha, hc⟩
  tm_conv := fun ⟨h, ha, hb⟩ hAB => ⟨Der.eqConv h hAB, ha, hb⟩
  ne_conv := fun ⟨h, ha, hb⟩ hAB => ⟨Der.eqConv h hAB, ha, hb⟩
  ty_wk := fun hρ hΔ ⟨h, ha, hb⟩ => ⟨h.rename hρ hΔ, ha.rename _, hb.rename _⟩
  tm_wk := fun hρ hΔ ⟨h, ha, hb⟩ => ⟨h.rename hρ hΔ, ha.rename _, hb.rename _⟩
  ne_wk := fun hρ hΔ ⟨h, ha, hb⟩ => ⟨h.rename hρ hΔ, ha.rename _, hb.rename _⟩
  ty_red := fun hA hB _ _ ⟨h, ha, hb⟩ =>
    ⟨Der.transT (Der.transT hA.tyEq h) (Der.symmT hB.tyEq), WN.of_fsteps hA.red.fsteps ha,
      WN.of_fsteps hB.red.fsteps hb⟩
  tm_red := fun hAB ha hb _ _ _ ⟨h, ha', hb'⟩ =>
    ⟨Der.eqConv (Der.trans (Der.trans ha.red.deq h) (Der.symm hb.red.deq)) (Der.symmT hAB.tyEq),
      WN.of_fsteps ha.red.fsteps ha', WN.of_fsteps hb.red.fsteps hb'⟩
  univ_refl := fun l hΓ => ⟨Der.reflT (Der.univT l hΓ), WN.atom_univ l, WN.atom_univ l⟩
  univU_refl := fun l hΓ => ⟨Der.refl (Der.univU l hΓ), WN.atom_univ l, WN.atom_univ l⟩
  nat_refl := fun hΓ => ⟨Der.reflT (Der.natT hΓ), WN.atom_nat, WN.atom_nat⟩
  natU_refl := fun hΓ => ⟨Der.refl (Der.natU hΓ), WN.atom_nat, WN.atom_nat⟩
  empty_refl := fun hΓ => ⟨Der.reflT (Der.emptyT hΓ), WN.atom_empty, WN.atom_empty⟩
  emptyU_refl := fun hΓ => ⟨Der.refl (Der.emptyU hΓ), WN.atom_empty, WN.atom_empty⟩
  pi_cong := fun hF ⟨hFH, wF, wH⟩ ⟨hGE, wG, wE⟩ => ⟨Der.piCongT hF hFH hGE, WN.pi wF wG, WN.pi wH wE⟩
  piU_cong := fun hF ⟨hFH, wF, wH⟩ ⟨hGE, wG, wE⟩ =>
    ⟨Der.piCongU hF hFH hGE, WN.pi wF wG, WN.pi wH wE⟩
  zero_refl := fun hΓ => ⟨Der.refl (Der.zero hΓ), WN.atom_zero, WN.atom_zero⟩
  succ_cong := fun ⟨h, wm, wn⟩ => ⟨Der.succCong h, WN.succ wm, WN.succ wn⟩
  eta := fun hF hf hg hnf hng ⟨h, w₁, w₂⟩ =>
    ⟨Der.eta hF hf hg h, WN.of_eta hf hnf w₁, WN.of_eta hg hng w₂⟩
  var_refl := fun hv => ⟨Der.refl hv, WNe.var _, WNe.var _⟩
  app_cong := fun ⟨h, wf, wg⟩ ⟨h', wa, wb⟩ => ⟨Der.appCong h h', WNe.app wf wa, WNe.app wg wb⟩
  natrec_cong := fun hP ⟨hPP, wP, wP'⟩ ⟨hz, wz, wz'⟩ ⟨hs, ws, ws'⟩ ⟨hn, wn, wn'⟩ =>
    ⟨Der.natrecCong hP hPP hz hs hn, WNe.natrec wP wz ws wn, WNe.natrec wP' wz' ws' wn'⟩
  emptyrec_cong := fun ⟨hPP, wP, wP'⟩ ⟨he, we, we'⟩ =>
    ⟨Der.emptyrecCong hPP he, WNe.emptyrec wP we, WNe.emptyrec wP' we'⟩

/-! ### Normalization -/

/-- **Weak normalization**: every typable term of MLTT reduces to a normal form. -/
theorem HasTy.wn {Γ : Ctx} {t A : Tm} (h : HasTy Γ t A) : WN t := by
  have hv := h.valid wnEq
  have hs := SubstR.ids (h.wf.valid wnEq) h.wf
  obtain ⟨l, I, hI, ht⟩ := hv.red hs
  simp only [subst_ids] at hI ht
  exact (hI.escapeTm ht).2.2.2.1

/-- **Weak normalization of types.** -/
theorem WfTy.wn {Γ : Ctx} {A : Tm} (h : WfTy Γ A) : WN A := by
  obtain ⟨l, hl⟩ := WfTy.univ h
  exact hl.wn

end MLTT
