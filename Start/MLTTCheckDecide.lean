/-
**Martin-Löf type theory: decidable type checking** — milestone M30 (`M30-MLTT-CHECK`).

* `MLTT.tc_terminates` — **termination**: in a well-formed context the checker answers for all
  large fuels, on every term (inference), and against every well-formed type (checking); the
  answers are eventually constant (`Ev`);
* **`MLTT.HasTy.check_spec`**, **`MLTT.HasTy.decidable`** — for a checkable term of the
  bidirectional fragment, in a well-formed context and at a well-formed type, typing is decided
  by the checker;
* **`MLTT.WfTy.decidable`**, **`MLTT.WfCtx.decidable`** — well-formedness of types and of
  contexts whose entries are in the fragment is decidable;
* **`MLTT.typeCheck_decidable`** — the judgement `⊢ Γ`, `Γ ⊢ A` and `Γ ⊢ t : A` together is
  decidable for terms of the fragment: a verified kernel for Π, `U l`, ℕ and ⊥.
-/

import Start.MLTTCheck

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Eventually constant answers -/

/-- `f n = v` for all large `n`. -/
def Ev {α : Type} (f : ℕ → α) (v : α) : Prop := ∃ n₀, ∀ n, n₀ ≤ n → f n = v

theorem ev_obind {α β : Type} {x : ℕ → Option (Option α)} {f : ℕ → α → Option (Option β)}
    {v : Option α} (hx : Ev x (some v))
    (hf : ∀ a, v = some a → ∃ w, Ev (fun n => f n a) (some w)) :
    ∃ w, Ev (fun n => obind (x n) (f n)) (some w) := by
  obtain ⟨n₁, h₁⟩ := hx
  cases v with
  | none =>
      refine ⟨none, n₁, fun n hn => ?_⟩
      show obind (x n) (f n) = _
      rw [h₁ n hn]
      rfl
  | some a =>
      obtain ⟨w, n₂, h₂⟩ := hf a rfl
      refine ⟨w, max n₁ n₂, fun n hn => ?_⟩
      show obind (x n) (f n) = _
      rw [h₁ n (le_of_max_le_left hn)]
      exact h₂ n (le_of_max_le_right hn)

theorem ev_ofBool {β : Type} {r : ℕ → Option Bool} {b : Bool} (hr : Ev r (some b)) (v : β) :
    ∃ w, Ev (fun n => ofBool (r n) v) (some w) := by
  obtain ⟨n₀, h⟩ := hr
  refine ⟨if b then some v else none, n₀, fun n hn => ?_⟩
  show ofBool (r n) v = _
  rw [h n hn]
  cases b <;> rfl

theorem ev_univView {Γ : Ctx} {T : Tm} (hT : WfTy Γ T) :
    ∃ w, Ev (fun n => univView n T) (some w) := by
  obtain ⟨T', hr, hn⟩ := hT.whnf
  obtain ⟨n₀, h⟩ := whnfF_of_tyReds hr hn
  refine ⟨match T' with | .univ l => some l | _ => none, n₀, fun n hn' => ?_⟩
  show univView n T = _
  unfold univView
  rw [h n hn']
  cases T' <;> rfl

theorem ev_piView {Γ : Ctx} {T : Tm} (hT : WfTy Γ T) :
    ∃ w, Ev (fun n => piView n T) (some w) := by
  obtain ⟨T', hr, hn⟩ := hT.whnf
  obtain ⟨n₀, h⟩ := whnfF_of_tyReds hr hn
  refine ⟨match T' with | .pi F G => some (F, G) | _ => none, n₀, fun n hn' => ?_⟩
  show piView n T = _
  unfold piView
  rw [h n hn']
  cases T' <;> rfl

open Classical in
theorem ev_checkVia {Γ : Ctx} {t A : Tm} {r : Option Tm} (hΓ : WfCtx Γ)
    (hr : Ev (fun n => tcInfer n Γ t) (some r)) (hA : WfTy Γ A) :
    ∃ b, Ev (fun n => checkVia n Γ (tcInfer n Γ t) A) (some b) := by
  obtain ⟨n₁, h₁⟩ := hr
  cases r with
  | none =>
      refine ⟨false, n₁, fun n hn => ?_⟩
      show checkVia n Γ (tcInfer n Γ t) A = _
      rw [show tcInfer n Γ t = some none from h₁ n hn]
      rfl
  | some B =>
      have hB := tcInfer_sound hΓ (h₁ n₁ le_rfl)
      obtain ⟨n₂, h₂⟩ := TyEq.decide_spec hB.wfTy hA
      refine ⟨decide (TyUp Γ B A), max n₁ n₂, fun n hn => ?_⟩
      show checkVia n Γ (tcInfer n Γ t) A = _
      rw [show tcInfer n Γ t = some (some B) from h₁ n (le_of_max_le_left hn)]
      show (cRun n).tyUp Γ B A = _
      obtain ⟨b, hb, -⟩ := h₂ n (le_of_max_le_right hn)
      exact tyUp_eq_decide hB.wfTy hA (by rw [hb]; simp)

/-! ### Termination -/

/-- The termination statement for a term. -/
def TcTerm (t : Tm) : Prop :=
  ∀ {Γ : Ctx}, WfCtx Γ → (∃ r, Ev (fun n => tcInfer n Γ t) (some r)) ∧
    (∀ {A : Tm}, WfTy Γ A → ∃ b, Ev (fun n => tcCheck n Γ t A) (some b))

theorem TcTerm.of_infer {t : Tm} (hnl : ∀ b, t ≠ lam b)
    (h : ∀ {Γ : Ctx}, WfCtx Γ → ∃ r, Ev (fun n => tcInfer n Γ t) (some r)) : TcTerm t := by
  intro Γ hΓ
  refine ⟨h hΓ, fun {A} hA => ?_⟩
  obtain ⟨r, hr⟩ := h hΓ
  obtain ⟨b, n₀, hb⟩ := ev_checkVia hΓ hr hA
  refine ⟨b, n₀, fun n hn => ?_⟩
  show tcCheck n Γ t A = _
  rw [tcCheck_of_not_lam hnl]
  exact hb n hn

/-- An answer of inference that is eventually constant is a type of the term. -/
theorem ev_inferSound {Γ : Ctx} {t T : Tm} (hΓ : WfCtx Γ)
    (h : Ev (fun n => tcInfer n Γ t) (some (some T))) : HasTy Γ t T := by
  obtain ⟨n₀, h⟩ := h
  exact tcInfer_sound hΓ (h n₀ le_rfl)

/-- **The checker terminates.** -/
theorem tc_terminates : ∀ t, TcTerm t := by
  intro t
  induction t with
  | var i =>
      exact TcTerm.of_infer (fun _ e => by cases e) (fun {Γ} _ => ⟨ctxGet Γ i, 0, fun _ _ => rfl⟩)
  | univ l =>
      exact TcTerm.of_infer (fun _ e => by cases e) (fun _ => ⟨_, 0, fun _ _ => rfl⟩)
  | nat => exact TcTerm.of_infer (fun _ e => by cases e) (fun _ => ⟨_, 0, fun _ _ => rfl⟩)
  | empty => exact TcTerm.of_infer (fun _ e => by cases e) (fun _ => ⟨_, 0, fun _ _ => rfl⟩)
  | zero => exact TcTerm.of_infer (fun _ e => by cases e) (fun _ => ⟨_, 0, fun _ _ => rfl⟩)
  | succ m ihm =>
      refine TcTerm.of_infer (fun _ e => by cases e) (fun {Γ} hΓ => ?_)
      obtain ⟨b, hb⟩ := (ihm hΓ).2 (Der.natT hΓ)
      exact ev_ofBool hb Tm.nat
  | pi F G ihF ihG =>
      refine TcTerm.of_infer (fun _ e => by cases e) (fun {Γ} hΓ => ?_)
      simp only [tcInfer_pi]
      obtain ⟨r₁, hr₁⟩ := (ihF hΓ).1
      refine ev_obind hr₁ (fun T₁ hT₁ => ?_)
      subst hT₁
      have hF := ev_inferSound hΓ hr₁
      obtain ⟨w, hw⟩ := ev_univView hF.wfTy
      refine ev_obind hw (fun i hi => ?_)
      subst hi
      obtain ⟨n₂, h₂⟩ := hw
      have hFi := hF.univView (h₂ n₂ le_rfl)
      have hFΓ : WfCtx (F :: Γ) := Der.cons hΓ (Der.el hFi)
      obtain ⟨r₂, hr₂⟩ := (ihG hFΓ).1
      refine ev_obind hr₂ (fun T₂ hT₂ => ?_)
      subst hT₂
      have hG := ev_inferSound hFΓ hr₂
      obtain ⟨w', hw'⟩ := ev_univView hG.wfTy
      exact ev_obind hw' (fun j _ => ⟨_, 0, fun _ _ => rfl⟩)
  | app f a ihf iha =>
      refine TcTerm.of_infer (fun _ e => by cases e) (fun {Γ} hΓ => ?_)
      simp only [tcInfer_app]
      obtain ⟨r₁, hr₁⟩ := (ihf hΓ).1
      refine ev_obind hr₁ (fun T hT => ?_)
      subst hT
      have hf := ev_inferSound hΓ hr₁
      obtain ⟨w, hw⟩ := ev_piView hf.wfTy
      refine ev_obind hw (fun p hp => ?_)
      subst hp
      obtain ⟨n₂, h₂⟩ := hw
      have hfP := hf.piView (h₂ n₂ le_rfl)
      obtain ⟨b, hb⟩ := (iha hΓ).2 hfP.wfTy.pi_inv.1
      exact ev_ofBool hb _
  | natrec P z s m ihP ihz ihs ihm =>
      refine TcTerm.of_infer (fun _ e => by cases e) (fun {Γ} hΓ => ?_)
      simp only [tcInfer_natrec]
      have hN : WfCtx (Tm.nat :: Γ) := Der.cons hΓ (Der.natT hΓ)
      obtain ⟨r₁, hr₁⟩ := (ihP hN).1
      refine ev_obind hr₁ (fun T hT => ?_)
      subst hT
      have hP := ev_inferSound hN hr₁
      obtain ⟨w, hw⟩ := ev_univView hP.wfTy
      refine ev_obind hw (fun l hl => ?_)
      subst hl
      obtain ⟨n₂, h₂⟩ := hw
      have hPw : WfTy (Tm.nat :: Γ) P := Der.el (hP.univView (h₂ n₂ le_rfl))
      obtain ⟨bz, hbz⟩ := (ihz hΓ).2 (hPw.inst (Der.zero hΓ))
      obtain ⟨wz, hwz⟩ := ev_ofBool hbz ()
      refine ev_obind hwz (fun _ _ => ?_)
      obtain ⟨bs, hbs⟩ := (ihs (Der.cons hN hPw)).2 hPw.stepTy
      obtain ⟨ws, hws⟩ := ev_ofBool hbs ()
      refine ev_obind hws (fun _ _ => ?_)
      obtain ⟨bm, hbm⟩ := (ihm hΓ).2 (Der.natT hΓ)
      exact ev_ofBool hbm _
  | emptyrec P e ihP ihe =>
      refine TcTerm.of_infer (fun _ e => by cases e) (fun {Γ} hΓ => ?_)
      simp only [tcInfer_emptyrec]
      obtain ⟨r₁, hr₁⟩ := (ihP hΓ).1
      refine ev_obind hr₁ (fun T hT => ?_)
      subst hT
      have hP := ev_inferSound hΓ hr₁
      obtain ⟨w, hw⟩ := ev_univView hP.wfTy
      refine ev_obind hw (fun l _ => ?_)
      obtain ⟨b, hb⟩ := (ihe hΓ).2 (Der.emptyT hΓ)
      exact ev_ofBool hb _
  | lam b ihb =>
      intro Γ hΓ
      refine ⟨⟨none, 0, fun _ _ => rfl⟩, fun {A} hA => ?_⟩
      simp only [tcCheck_lam]
      obtain ⟨T', hr, hn⟩ := hA.whnf
      obtain ⟨n₁, h₁⟩ := whnfF_of_tyReds hr hn
      cases T'
      case pi F G =>
        obtain ⟨hF, hG⟩ := hr.wfR.pi_inv
        obtain ⟨bb, n₂, h₂⟩ := (ihb (Der.cons hΓ hF)).2 hG
        refine ⟨bb, max n₁ n₂, fun n hn' => ?_⟩
        show checkLam n A _ = _
        unfold checkLam piView
        rw [h₁ n (le_of_max_le_left hn')]
        exact h₂ n (le_of_max_le_right hn')
      all_goals
        refine ⟨false, n₁, fun n hn' => ?_⟩
        show checkLam n A _ = _
        unfold checkLam piView
        rw [h₁ n hn']

/-! ### Decidability of typing -/

/-- **The checker decides typing on the bidirectional fragment.** -/
theorem HasTy.check_spec {Γ : Ctx} {t A : Tm} (hΓ : WfCtx Γ) (hA : WfTy Γ A)
    (ht : Shape false t) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ b, tcCheck n Γ t A = some b ∧ (b = true ↔ HasTy Γ t A) := by
  obtain ⟨b, n₀, h⟩ := (tc_terminates t hΓ).2 hA
  refine ⟨n₀, fun n hn => ⟨b, h n hn, ?_⟩⟩
  constructor
  · intro hb
    subst hb
    exact tcCheck_sound hΓ hA (h n hn)
  · intro hty
    exact ht.ok hty (h n hn)

theorem HasTy.check_answers {Γ : Ctx} {t A : Tm} (hΓ : WfCtx Γ) (hA : WfTy Γ A) :
    ∃ n, tcCheck n Γ t A ≠ none := by
  obtain ⟨b, n₀, h⟩ := (tc_terminates t hΓ).2 hA
  have e : tcCheck n₀ Γ t A = some b := h n₀ le_rfl
  exact ⟨n₀, by rw [e]; simp⟩

/-- **The type checker**: run at the least fuel at which it answers. -/
def decideHasTy (Γ : Ctx) (t A : Tm) (h : ∃ n, tcCheck n Γ t A ≠ none) : Bool :=
  (tcCheck (Nat.find h) Γ t A).getD false

theorem decideHasTy_spec {Γ : Ctx} {t A : Tm} (hΓ : WfCtx Γ) (hA : WfTy Γ A)
    (ht : Shape false t) :
    decideHasTy Γ t A (HasTy.check_answers hΓ hA) = true ↔ HasTy Γ t A := by
  have hfind := Nat.find_spec (HasTy.check_answers (t := t) hΓ hA)
  unfold decideHasTy
  cases e : tcCheck (Nat.find (HasTy.check_answers (t := t) hΓ hA)) Γ t A with
  | none => exact absurd e hfind
  | some b =>
      simp only [Option.getD_some]
      constructor
      · intro hb
        subst hb
        exact tcCheck_sound hΓ hA e
      · intro hty
        exact ht.ok hty e

/-- **Typing of a term of the bidirectional fragment is decidable.** -/
def HasTy.decidable {Γ : Ctx} {t A : Tm} (hΓ : WfCtx Γ) (hA : WfTy Γ A) (ht : Shape false t) :
    Decidable (HasTy Γ t A) :=
  decidable_of_iff _ (decideHasTy_spec hΓ hA ht)

/-! ### Decidability of type formation and of contexts -/

/-- Is the term a type: infer its type and reduce it to a universe. -/
def tcIsType (n : ℕ) (Γ : Ctx) (A : Tm) : Option Bool :=
  match tcInfer n Γ A with
  | none => none
  | some none => some false
  | some (some T) => (univView n T).map Option.isSome

theorem tcIsType_sound {n : ℕ} {Γ : Ctx} {A : Tm} (hΓ : WfCtx Γ)
    (h : tcIsType n Γ A = some true) : WfTy Γ A := by
  unfold tcIsType at h
  split at h
  · cases h
  · cases h
  · next T hT =>
      obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
      cases r with
      | none => cases e
      | some l => exact Der.el ((tcInfer_sound hΓ hT).univView hr)

theorem tcIsType_complete {n : ℕ} {Γ : Ctx} {A : Tm} {b : Bool} (hA : Shape true A)
    (hw : WfTy Γ A) (h : tcIsType n Γ A = some b) : b = true := by
  obtain ⟨l, hl⟩ := hw.univ
  unfold tcIsType at h
  split at h
  · cases h
  · next hT =>
      obtain ⟨_, e, -⟩ := hA.ok hl hT
      cases e
  · next T hT =>
      obtain ⟨_, e, hTl⟩ := hA.ok hl hT
      cases e
      obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [univView_complete hTl hr]
      rfl

theorem tcIsType_terminates {Γ : Ctx} {A : Tm} (hΓ : WfCtx Γ) :
    ∃ b, Ev (fun n => tcIsType n Γ A) (some b) := by
  obtain ⟨r, n₁, h₁⟩ := (tc_terminates A hΓ).1
  cases r with
  | none =>
      refine ⟨false, n₁, fun n hn => ?_⟩
      show tcIsType n Γ A = _
      unfold tcIsType
      rw [show tcInfer n Γ A = some none from h₁ n hn]
  | some T =>
      have hT := tcInfer_sound hΓ (h₁ n₁ le_rfl)
      obtain ⟨w, n₂, h₂⟩ := ev_univView hT.wfTy
      refine ⟨w.isSome, max n₁ n₂, fun n hn => ?_⟩
      show tcIsType n Γ A = _
      unfold tcIsType
      rw [show tcInfer n Γ A = some (some T) from h₁ n (le_of_max_le_left hn)]
      show (univView n T).map Option.isSome = _
      rw [show univView n T = some w from h₂ n (le_of_max_le_right hn)]
      rfl

theorem WfTy.check_answers {Γ : Ctx} {A : Tm} (hΓ : WfCtx Γ) : ∃ n, tcIsType n Γ A ≠ none := by
  obtain ⟨b, n₀, h⟩ := tcIsType_terminates (A := A) hΓ
  have e : tcIsType n₀ Γ A = some b := h n₀ le_rfl
  exact ⟨n₀, by rw [e]; simp⟩

/-- **Type formation is decidable** for types of the bidirectional fragment. -/
def WfTy.decidable {Γ : Ctx} {A : Tm} (hΓ : WfCtx Γ) (hA : Shape true A) : Decidable (WfTy Γ A) :=
  decidable_of_iff ((tcIsType (Nat.find (WfTy.check_answers (A := A) hΓ)) Γ A).getD false = true) (by
    have hfind := Nat.find_spec (WfTy.check_answers (A := A) hΓ)
    cases e : tcIsType (Nat.find (WfTy.check_answers (A := A) hΓ)) Γ A with
    | none => exact absurd e hfind
    | some b =>
        simp only [Option.getD_some]
        constructor
        · intro hb
          subst hb
          exact tcIsType_sound hΓ e
        · intro hw
          exact tcIsType_complete hA hw e)

/-- **Well-formedness of contexts is decidable** for contexts of the bidirectional fragment. -/
def WfCtx.decidable : ∀ {Γ : Ctx}, (∀ B ∈ Γ, Shape true B) → Decidable (WfCtx Γ)
  | [], _ => isTrue Der.nil
  | A :: Γ, h =>
      match WfCtx.decidable (fun B hB => h B (List.mem_cons.mpr (Or.inr hB))) with
      | isFalse hΓ => isFalse (fun hc => hΓ (by cases hc with | cons hΓ' _ => exact hΓ'))
      | isTrue hΓ =>
          match WfTy.decidable hΓ (h A (List.mem_cons.mpr (Or.inl rfl))) with
          | isTrue hA => isTrue (Der.cons hΓ hA)
          | isFalse hA => isFalse (fun hc => hA (by cases hc with | cons _ hA' => exact hA'))

/-- **A verified kernel**: for a context, a type and a term of the bidirectional fragment, the
judgements `⊢ Γ`, `Γ ⊢ A` and `Γ ⊢ t : A` are decidable. -/
def typeCheck_decidable {Γ : Ctx} {t A : Tm} (hΓ : ∀ B ∈ Γ, Shape true B) (hA : Shape true A)
    (ht : Shape false t) : Decidable (WfCtx Γ ∧ WfTy Γ A ∧ HasTy Γ t A) :=
  match WfCtx.decidable hΓ with
  | isFalse h => isFalse (fun h' => h h'.1)
  | isTrue hc =>
      match WfTy.decidable hc hA with
      | isFalse h => isFalse (fun h' => h h'.2.1)
      | isTrue hw =>
          match HasTy.decidable hc hw ht with
          | isTrue h => isTrue ⟨hc, hw, h⟩
          | isFalse h => isFalse (fun h' => h h'.2.2)

/-! ### Examples, evaluated by the kernel -/

/-- The identity on ℕ checks against `ℕ → ℕ`. -/
example : tcCheck 3 List.nil (lam (var 0)) (pi Tm.nat Tm.nat) = some true := by decide

/-- …and is rejected against `ℕ → ⊥`. -/
example : tcCheck 3 List.nil (lam (var 0)) (pi Tm.nat Tm.empty) = some false := by decide

/-- The polymorphic identity `λ A x. x` checks against `Π (A : U 0). A → A`. -/
example : tcCheck 4 List.nil (lam (lam (var 0))) (pi (Tm.univ 0) (pi (var 0) (var 1))) = some true := by
  decide

/-- The type `Π (A : U 0). A → A` is inferred to live in `U 1`. -/
example : tcInfer 3 List.nil (pi (Tm.univ 0) (pi (var 0) (var 1))) = some (some (Tm.univ 1)) := by
  decide

end MLTT
