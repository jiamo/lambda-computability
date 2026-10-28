/-
**Bridge: System FC with coercions is the fragment of System FC with data types without data** —
milestone M31 (`M31-BRIDGE-SYSTEMFC`).

`Start/SystemFCoerce.lean` (System F with type-equality coercions, over the types of
`Start/SystemF.lean`) and `Start/SystemFCTyCon.lean` (the same calculus with type constructors,
data constructors, `case` and axiom schemes) were developed separately.  The embedding below shows
that the first is the second at the empty data signature, with each axiom `A ~ B` read as the
scheme with no parameters.

* `FCBridge.embTy`, `embCo`, `embTm`, `embAx` — the embedding;
* `embTy_tyRename`, `embTy_tySubst`, `embTy_tyInst`, `embCo_substTyCo`, `embTm_substTyTm`,
  `embTm_lift`, `embTm_subst` — it commutes with renaming, substitution and instantiation, at the
  level of types, coercions and terms;
* **`FCBridge.coTyping_emb`**, **`FCBridge.typing_emb`** — coercion typing and typing are
  preserved, for closed axioms (`FCoerce.AxClosed`, the hypothesis of the preservation theorem
  of System FC);
* **`FCBridge.step_emb`** — every reduction step is a step of System FC with data types.
-/

import Start.SystemFCoerce
import Start.SystemFCTyCon

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FCBridge

open SystemF

/-! ### The embedding -/

/-- Types of System F as types of System FC with data. -/
def embTy : FTy → FCTyCon.Ty
  | .var i => .var i
  | .arrow A B => .arrow (embTy A) (embTy B)
  | .all A => .all (embTy A)

/-- Coercions; the axiom `i` becomes the scheme `i` at no parameters. -/
def embCo : FCoerce.Co → FCTyCon.Co
  | .refl A => .refl (embTy A)
  | .sym γ => .sym (embCo γ)
  | .trans γ δ => .trans (embCo γ) (embCo δ)
  | .arr γ δ => .arr (embCo γ) (embCo δ)
  | .all γ => .all (embCo γ)
  | .inst γ C => .inst (embCo γ) (embTy C)
  | .ax i => .ax i []
  | .left γ => .left (embCo γ)
  | .right γ => .right (embCo γ)

/-- Terms. -/
def embTm : FCoerce.Tm → FCTyCon.Tm
  | .var i => .var i
  | .app a b => .app (embTm a) (embTm b)
  | .lam A t => .lam (embTy A) (embTm t)
  | .tlam t => .tlam (embTm t)
  | .tapp t B => .tapp (embTm t) (embTy B)
  | .cast t γ => .cast (embTm t) (embCo γ)

/-- Axioms, as schemes with no parameters. -/
def embAx (Ax : List (FTy × FTy)) : FCTyCon.AxSet := Ax.map fun p => (0, embTy p.1, embTy p.2)

/-! ### Commutation with renaming and substitution -/

theorem upr_eq (r : ℕ → ℕ) : FCTyCon.upr r = SystemF.upr r := by
  funext n
  cases n <;> rfl

theorem embTy_tyRename (A : FTy) : ∀ r : ℕ → ℕ, embTy (tyRename r A) = FCTyCon.tyRename r (embTy A) := by
  induction A with
  | var i => intro r; rfl
  | arrow A B ihA ihB => intro r; simp only [tyRename, embTy, FCTyCon.tyRename, ihA, ihB]
  | all A ih => intro r; simp only [tyRename, embTy, FCTyCon.tyRename, ih, upr_eq]

theorem embTy_tyShift (A : FTy) : embTy (tyShift A) = FCTyCon.tyShift (embTy A) :=
  embTy_tyRename A Nat.succ

theorem embTy_ups (s : ℕ → FTy) : (fun n => embTy (ups s n)) = FCTyCon.ups (fun n => embTy (s n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => exact embTy_tyShift (s n)

theorem embTy_tySubst (A : FTy) :
    ∀ s : ℕ → FTy, embTy (tySubst s A) = FCTyCon.tySubst (fun n => embTy (s n)) (embTy A) := by
  induction A with
  | var i => intro s; rfl
  | arrow A B ihA ihB => intro s; simp only [tySubst, embTy, FCTyCon.tySubst, ihA, ihB]
  | all A ih => intro s; simp only [tySubst, embTy, FCTyCon.tySubst, ih, embTy_ups]

theorem embTy_tyScons (B : FTy) :
    (fun n => embTy (tyScons B n)) = FCTyCon.tyCons (embTy B) FCTyCon.Ty.var := by
  funext n
  cases n <;> rfl

theorem embTy_tyInst (B A : FTy) : embTy (tyInst B A) = FCTyCon.tyInst (embTy B) (embTy A) := by
  rw [tyInst, embTy_tySubst, embTy_tyScons]
  rfl

theorem embCo_substTyCo (γ : FCoerce.Co) :
    ∀ s : ℕ → FTy, embCo (FCoerce.substTyCo s γ) =
      FCTyCon.substTyCo (fun n => embTy (s n)) (embCo γ) := by
  induction γ with
  | refl A => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, embTy_tySubst]
  | sym γ ih => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih]
  | trans γ δ ih₁ ih₂ => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih₁, ih₂]
  | arr γ δ ih₁ ih₂ => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih₁, ih₂]
  | all γ ih => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih, embTy_ups]
  | inst γ C ih =>
      intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih, embTy_tySubst]
  | ax i => intro s; rfl
  | left γ ih => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih]
  | right γ ih => intro s; simp only [FCoerce.substTyCo, embCo, FCTyCon.substTyCo, ih]

theorem embTm_substTyTm (t : FCoerce.Tm) :
    ∀ s : ℕ → FTy, embTm (FCoerce.substTyTm s t) =
      FCTyCon.substTyTm (fun n => embTy (s n)) (embTm t) := by
  induction t with
  | var i => intro s; rfl
  | app a b iha ihb => intro s; simp only [FCoerce.substTyTm, embTm, FCTyCon.substTyTm, iha, ihb]
  | lam A t ih =>
      intro s; simp only [FCoerce.substTyTm, embTm, FCTyCon.substTyTm, ih, embTy_tySubst]
  | tlam t ih => intro s; simp only [FCoerce.substTyTm, embTm, FCTyCon.substTyTm, ih, embTy_ups]
  | tapp t B ih =>
      intro s; simp only [FCoerce.substTyTm, embTm, FCTyCon.substTyTm, ih, embTy_tySubst]
  | cast t γ ih =>
      intro s; simp only [FCoerce.substTyTm, embTm, FCTyCon.substTyTm, ih, embCo_substTyCo]

theorem embTm_shiftTyTm (t : FCoerce.Tm) :
    embTm (FCoerce.shiftTyTm t) = FCTyCon.shiftTyTm (embTm t) := by
  rw [FCoerce.shiftTyTm, embTm_substTyTm]
  rfl

theorem embTm_lift (t : FCoerce.Tm) : ∀ n k : ℕ, embTm (FCoerce.lift n k t) = FCTyCon.lift n k (embTm t) := by
  induction t with
  | var y =>
      intro n k
      simp only [FCoerce.lift, FCTyCon.lift, embTm]
      split <;> rfl
  | app a b iha ihb => intro n k; simp only [FCoerce.lift, embTm, FCTyCon.lift, iha, ihb]
  | lam A t ih => intro n k; simp only [FCoerce.lift, embTm, FCTyCon.lift, ih]
  | tlam t ih => intro n k; simp only [FCoerce.lift, embTm, FCTyCon.lift, ih]
  | tapp t B ih => intro n k; simp only [FCoerce.lift, embTm, FCTyCon.lift, ih]
  | cast t γ ih => intro n k; simp only [FCoerce.lift, embTm, FCTyCon.lift, ih]

theorem embTm_subst (t : FCoerce.Tm) :
    ∀ (u : FCoerce.Tm) (x : ℕ), embTm (FCoerce.subst u x t) = FCTyCon.subst (embTm u) x (embTm t) := by
  induction t with
  | var y =>
      intro u x
      simp only [FCoerce.subst, FCTyCon.subst, embTm]
      split
      · rfl
      · split <;> rfl
  | app a b iha ihb => intro u x; simp only [FCoerce.subst, embTm, FCTyCon.subst, iha, ihb]
  | lam A t ih => intro u x; simp only [FCoerce.subst, embTm, FCTyCon.subst, ih, embTm_lift]
  | tlam t ih => intro u x; simp only [FCoerce.subst, embTm, FCTyCon.subst, ih, embTm_shiftTyTm]
  | tapp t B ih => intro u x; simp only [FCoerce.subst, embTm, FCTyCon.subst, ih]
  | cast t γ ih => intro u x; simp only [FCoerce.subst, embTm, FCTyCon.subst, ih]

/-! ### Typing and reduction are preserved -/

/-- **Coercion typing is preserved**, for closed axioms. -/
theorem coTyping_emb {Ax : List (FTy × FTy)} (hAx : FCoerce.AxClosed Ax) {γ : FCoerce.Co}
    {A B : FTy} (h : FCoerce.CoTyping Ax γ A B) :
    FCTyCon.CoTyping (embAx Ax) (embCo γ) (embTy A) (embTy B) := by
  induction h with
  | refl A => exact .refl _
  | sym _ ih => exact .sym ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | arr _ _ ih₁ ih₂ => exact .arr ih₁ ih₂
  | all _ ih => exact .all ih
  | inst C _ ih =>
      rw [embTy_tyInst, embTy_tyInst]
      exact .inst _ ih
  | @ax i A B hi =>
      have hi' : (embAx Ax)[i]? = some (0, embTy A, embTy B) := by
        simp [embAx, List.getElem?_map, hi]
      have h := FCTyCon.CoTyping.ax (σ := []) hi' rfl
      obtain ⟨h₁, h₂⟩ := hAx (A, B) (List.mem_of_getElem? hi) (fun _ => FTy.var 0)
      simp only at h₁ h₂
      have key : ∀ C : FTy, FCTyCon.tySubst (FCTyCon.listSub []) (embTy C) =
          embTy (tySubst (fun _ => FTy.var 0) C) := by
        intro C
        rw [embTy_tySubst]
        rfl
      have e₁ : FCTyCon.tySubst (FCTyCon.listSub []) (embTy A) = embTy A := by rw [key, h₁]
      have e₂ : FCTyCon.tySubst (FCTyCon.listSub []) (embTy B) = embTy B := by rw [key, h₂]
      rw [e₁, e₂] at h
      exact h
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- **Typing is preserved**, at the empty data signature, for closed axioms. -/
theorem typing_emb {Ax : List (FTy × FTy)} (hAx : FCoerce.AxClosed Ax) {Γ : List FTy}
    {t : FCoerce.Tm} {A : FTy} (h : FCoerce.Typing Ax Γ t A) :
    FCTyCon.Typing [] (embAx Ax) (Γ.map embTy) (embTm t) (embTy A) := by
  induction h with
  | var hi => exact .var (by simp [List.getElem?_map, hi])
  | app _ _ iha ihb => exact .app iha ihb
  | lam _ ih => exact .lam ih
  | @tlam Γ t A _ ih =>
      refine .tlam ?_
      have e : (Γ.map tyShift).map embTy = (Γ.map embTy).map FCTyCon.tyShift := by
        simp [List.map_map, Function.comp_def, embTy_tyShift]
      rw [← e]
      exact ih
  | tapp B _ ih =>
      rw [embTy_tyInst]
      exact .tapp _ ih
  | cast _ hγ ih => exact .cast ih (coTyping_emb hAx hγ)

/-- **Every reduction step is a step of System FC with data types.** -/
theorem step_emb {t t' : FCoerce.Tm} (h : FCoerce.Step t t') : FCTyCon.Step [] (embTm t) (embTm t') := by
  induction h with
  | beta A t u =>
      rw [embTm_subst]
      exact .beta _ _ _
  | tbeta t B =>
      rw [embTm_substTyTm, embTy_tyScons]
      exact .tbeta _ _
  | castTrans t γ δ => exact .castTrans _ _ _
  | pushApp A t γ u => exact .pushApp _ _ _ _
  | pushTApp t γ C => exact .pushTApp _ _ _
  | appL b _ ih => exact .appL _ ih
  | appR a _ ih => exact .appR _ ih
  | lam A _ ih => exact .lam _ ih
  | tlam _ ih => exact .tlam ih
  | tapp B _ ih => exact .tapp _ ih
  | cast γ _ ih => exact .cast _ ih

end FCBridge
