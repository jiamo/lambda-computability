/-
**Martin-Löf type theory: a bidirectional type checker** — milestone M30 (`M30-MLTT-CHECK`).

A type checker for the Curry-style terms of `Start/MLTTSyntax.lean`, in the bidirectional style
of the internal syntax of Agda: abstractions are checked against a product, everything else is
inferred, and a checked term that is not an abstraction is inferred and its type compared with
the expected one by the conversion program of `Start/MLTTDecide.lean`.

* `MLTT.tcInfer n Γ t`, `MLTT.tcCheck n Γ t A` — the checker with fuel `n` (the fuel bounds weak
  head normalization and conversion; the recursion is on the term): `none` when the fuel runs out,
  `some none` / `some false` when the term is rejected;
* `MLTT.Shape` — the **bidirectional fragment**: abstractions only in checking positions, i.e.
  never at the head of an application.  It contains every term without a `β`-redex `(λ b) a`;
* `MLTT.tc_sound` — **soundness**: an inferred type is a type of the term, and a term checked
  against a well-formed type has that type (for every term, in every well-formed context);
* `MLTT.Shape.ok` — **completeness** on the fragment: the inferred type of a typable term is
  equal to each of its types, and a typable term is accepted at each of its types.
-/

import Start.MLTTDecide

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### The checker -/

/-- Sequencing of answers: `none` — out of fuel; `some none` — rejected. -/
def obind {α β : Type} (x : Option (Option α)) (f : α → Option (Option β)) : Option (Option β) :=
  match x with
  | none => none
  | some none => some none
  | some (some a) => f a

/-- A Boolean answer as an answer with a value. -/
def ofBool {β : Type} (r : Option Bool) (v : β) : Option (Option β) :=
  match r with
  | none => none
  | some false => some none
  | some true => some (some v)

/-- Reduce a type and read off a universe. -/
def univView (n : ℕ) (T : Tm) : Option (Option ℕ) :=
  match whnfF n T with
  | none => none
  | some (.univ l) => some (some l)
  | some _ => some none

/-- Reduce a type and read off a product. -/
def piView (n : ℕ) (T : Tm) : Option (Option (Tm × Tm)) :=
  match whnfF n T with
  | none => none
  | some (.pi F G) => some (some (F, G))
  | some _ => some none

/-- Checking by inference and conversion. -/
def checkVia (n : ℕ) (Γ : Ctx) (r : Option (Option Tm)) (A : Tm) : Option Bool :=
  match r with
  | none => none
  | some none => some false
  | some (some B) => (cRun n).tyUp Γ B A

/-- Checking an abstraction against a type reducing to a product. -/
def checkLam (n : ℕ) (A : Tm) (k : Tm → Tm → Option Bool) : Option Bool :=
  match piView n A with
  | none => none
  | some none => some false
  | some (some (F, G)) => k F G

/-- The checker on a term: its inferred type, and its check against each type. -/
def tc (n : ℕ) : Tm → Ctx → Option (Option Tm) × (Tm → Option Bool)
  | .var i, Γ => (some (ctxGet Γ i), checkVia n Γ (some (ctxGet Γ i)))
  | .univ l, Γ => (some (some (.univ (l + 1))), checkVia n Γ (some (some (.univ (l + 1)))))
  | .nat, Γ => (some (some (.univ 0)), checkVia n Γ (some (some (.univ 0))))
  | .empty, Γ => (some (some (.univ 0)), checkVia n Γ (some (some (.univ 0))))
  | .zero, Γ => (some (some .nat), checkVia n Γ (some (some .nat)))
  | .succ m, Γ =>
      (ofBool ((tc n m Γ).2 .nat) Tm.nat, checkVia n Γ (ofBool ((tc n m Γ).2 .nat) Tm.nat))
  | .pi F G, Γ =>
      let r := obind (tc n F Γ).1 fun T₁ => obind (univView n T₁) fun i =>
        obind (tc n G (F :: Γ)).1 fun T₂ => obind (univView n T₂) fun j =>
        some (some (.univ (max i j)))
      (r, checkVia n Γ r)
  | .app f a, Γ =>
      let r := obind (tc n f Γ).1 fun T => obind (piView n T) fun p =>
        ofBool ((tc n a Γ).2 p.1) (inst a p.2)
      (r, checkVia n Γ r)
  | .natrec P z s m, Γ =>
      let r := obind (tc n P (.nat :: Γ)).1 fun T => obind (univView n T) fun _ =>
        obind (ofBool ((tc n z Γ).2 (inst .zero P)) ()) fun _ =>
        obind (ofBool ((tc n s (P :: .nat :: Γ)).2 (stepTy P)) ()) fun _ =>
        ofBool ((tc n m Γ).2 .nat) (inst m P)
      (r, checkVia n Γ r)
  | .emptyrec P e, Γ =>
      let r := obind (tc n P Γ).1 fun T => obind (univView n T) fun _ =>
        ofBool ((tc n e Γ).2 .empty) P
      (r, checkVia n Γ r)
  | .lam b, Γ => (some none, fun A => checkLam n A fun F G => (tc n b (F :: Γ)).2 G)

/-- **Type inference** with fuel `n`. -/
def tcInfer (n : ℕ) (Γ : Ctx) (t : Tm) : Option (Option Tm) := (tc n t Γ).1

/-- **Type checking** with fuel `n`. -/
def tcCheck (n : ℕ) (Γ : Ctx) (t A : Tm) : Option Bool := (tc n t Γ).2 A

theorem tcInfer_succ (n : ℕ) (Γ : Ctx) (m : Tm) :
    tcInfer n Γ (succ m) = ofBool (tcCheck n Γ m Tm.nat) Tm.nat := rfl

theorem tcInfer_pi (n : ℕ) (Γ : Ctx) (F G : Tm) :
    tcInfer n Γ (pi F G) = obind (tcInfer n Γ F) fun T₁ => obind (univView n T₁) fun i =>
      obind (tcInfer n (F :: Γ) G) fun T₂ => obind (univView n T₂) fun j =>
      some (some (Tm.univ (max i j))) := rfl

theorem tcInfer_app (n : ℕ) (Γ : Ctx) (f a : Tm) :
    tcInfer n Γ (app f a) = obind (tcInfer n Γ f) fun T => obind (piView n T) fun p =>
      ofBool (tcCheck n Γ a p.1) (inst a p.2) := rfl

theorem tcInfer_natrec (n : ℕ) (Γ : Ctx) (P z s m : Tm) :
    tcInfer n Γ (natrec P z s m) = obind (tcInfer n (Tm.nat :: Γ) P) fun T =>
      obind (univView n T) fun _ =>
      obind (ofBool (tcCheck n Γ z (inst Tm.zero P)) ()) fun _ =>
      obind (ofBool (tcCheck n (P :: Tm.nat :: Γ) s (stepTy P)) ()) fun _ =>
      ofBool (tcCheck n Γ m Tm.nat) (inst m P) := rfl

theorem tcInfer_emptyrec (n : ℕ) (Γ : Ctx) (P e : Tm) :
    tcInfer n Γ (emptyrec P e) = obind (tcInfer n Γ P) fun T => obind (univView n T) fun _ =>
      ofBool (tcCheck n Γ e Tm.empty) P := rfl

theorem tcCheck_lam (n : ℕ) (Γ : Ctx) (b A : Tm) :
    tcCheck n Γ (lam b) A = checkLam n A fun F G => tcCheck n (F :: Γ) b G := rfl

theorem tcInfer_lam (n : ℕ) (Γ : Ctx) (b : Tm) : tcInfer n Γ (lam b) = some none := rfl

theorem tcCheck_of_not_lam {n : ℕ} {Γ : Ctx} {t A : Tm} (ht : ∀ b, t ≠ lam b) :
    tcCheck n Γ t A = checkVia n Γ (tcInfer n Γ t) A := by
  cases t <;> first | rfl | exact absurd rfl (ht _)

/-! ### Reading answers -/

theorem obind_eq_some {α β : Type} {x : Option (Option α)} {f : α → Option (Option β)}
    {r : Option β} (h : obind x f = some r) :
    (x = some none ∧ r = none) ∨ ∃ a, x = some (some a) ∧ f a = some r := by
  rcases x with _ | _ | a
  · cases h
  · have h' : some none = some r := h
    cases h'
    exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨a, rfl, h⟩

theorem ofBool_eq_some {β : Type} {r : Option Bool} {v : β} {w : Option β}
    (h : ofBool r v = some w) : (r = some false ∧ w = none) ∨ (r = some true ∧ w = some v) := by
  rcases r with _ | _ | _
  · cases h
  · have h' : some none = some w := h
    cases h'
    exact Or.inl ⟨rfl, rfl⟩
  · have h' : some (some v) = some w := h
    cases h'
    exact Or.inr ⟨rfl, rfl⟩

theorem univView_eq_some {n : ℕ} {T : Tm} {r : Option ℕ} (h : univView n T = some r) :
    ∃ T', whnfF n T = some T' ∧ ∀ l, (r = some l ↔ T' = Tm.univ l) := by
  unfold univView at h
  split at h
  · cases h
  · next l e =>
      cases h
      exact ⟨_, e, fun l' => by simp⟩
  · next T' hne e =>
      cases h
      exact ⟨T', e, fun l => ⟨(fun h => by cases h), (fun h => absurd h (hne l))⟩⟩

theorem piView_eq_some {n : ℕ} {T : Tm} {r : Option (Tm × Tm)} (h : piView n T = some r) :
    ∃ T', whnfF n T = some T' ∧ ∀ F G, (r = some (F, G) ↔ T' = pi F G) := by
  unfold piView at h
  split at h
  · cases h
  · next F G e =>
      cases h
      exact ⟨_, e, fun F' G' => by simp⟩
  · next T' hne e =>
      cases h
      exact ⟨T', e, fun F G => ⟨(fun h => by cases h), (fun h => absurd h (hne F G))⟩⟩

theorem checkVia_eq_some {n : ℕ} {Γ : Ctx} {r : Option (Option Tm)} {A : Tm} {b : Bool}
    (h : checkVia n Γ r A = some b) :
    (r = some none ∧ b = false) ∨ ∃ B, r = some (some B) ∧ (cRun n).tyUp Γ B A = some b := by
  rcases r with _ | _ | B
  · cases h
  · have h' : some false = some b := h
    cases h'
    exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨B, rfl, h⟩

theorem checkLam_eq_some {n : ℕ} {A : Tm} {k : Tm → Tm → Option Bool} {b : Bool}
    (h : checkLam n A k = some b) :
    (∃ T', whnfF n A = some T' ∧ (∀ F G, T' ≠ pi F G) ∧ b = false) ∨
      ∃ F G, whnfF n A = some (pi F G) ∧ k F G = some b := by
  unfold checkLam at h
  split at h
  · cases h
  · next hv =>
      cases h
      obtain ⟨T', e, hT'⟩ := piView_eq_some hv
      exact Or.inl ⟨T', e, fun F G hp => by simpa using (hT' F G).mpr hp, rfl⟩
  · next F G hv =>
      obtain ⟨T', e, hT'⟩ := piView_eq_some hv
      have := (hT' F G).mp rfl
      subst this
      exact Or.inr ⟨F, G, e, h⟩

/-! ### Soundness -/

/-- The soundness statement for a term. -/
def TcSound (t : Tm) : Prop :=
  ∀ {n : ℕ} {Γ : Ctx}, WfCtx Γ →
    (∀ {A : Tm}, tcInfer n Γ t = some (some A) → HasTy Γ t A) ∧
    (∀ {A : Tm}, WfTy Γ A → tcCheck n Γ t A = some true → HasTy Γ t A)

theorem checkVia_sound {n : ℕ} {Γ : Ctx} {t A : Tm} {r : Option (Option Tm)}
    (hr : ∀ B, r = some (some B) → HasTy Γ t B) (hA : WfTy Γ A)
    (h : checkVia n Γ r A = some true) : HasTy Γ t A := by
  rcases checkVia_eq_some h with ⟨_, hb⟩ | ⟨B, rfl, hB⟩
  · cases hb
  · have htB := hr B rfl
    exact Der.conv htB (TyUp.sound (((cRun_correct n).2.1 htB.wfTy hA hB).mp rfl))

/-- A term of a type reducing to `T'` has type `T'`. -/
theorem HasTy.whnfF_ty {n : ℕ} {Γ : Ctx} {t T T' : Tm} (ht : HasTy Γ t T)
    (h : whnfF n T = some T') : HasTy Γ t T' :=
  Der.conv ht (whnfF_tyTyped ht.wfTy h).1.tyEq

theorem HasTy.univView {n : ℕ} {Γ : Ctx} {t T : Tm} {l : ℕ} (ht : HasTy Γ t T)
    (h : univView n T = some (some l)) : HasTy Γ t (Tm.univ l) := by
  obtain ⟨T', e, hT'⟩ := univView_eq_some h
  rw [(hT' l).mp rfl] at e
  exact ht.whnfF_ty e

theorem HasTy.piView {n : ℕ} {Γ : Ctx} {t T F G : Tm} (ht : HasTy Γ t T)
    (h : piView n T = some (some (F, G))) : HasTy Γ t (pi F G) := by
  obtain ⟨T', e, hT'⟩ := piView_eq_some h
  rw [(hT' F G).mp rfl] at e
  exact ht.whnfF_ty e

theorem WfTy.stepTy {Γ : Ctx} {P : Tm} (hP : WfTy (Tm.nat :: Γ) P) :
    WfTy (P :: Tm.nat :: Γ) (stepTy P) :=
  (TyEq.stepTy (Der.reflT hP)).wfL

/-- **Soundness of the checker.** -/
theorem tc_sound : ∀ t, TcSound t := by
  intro t
  induction t with
  | var i =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (var i) = some (some A) → HasTy Γ (var i) A := by
        intro A h
        have h' : some (ctxGet Γ i) = some (some A) := h
        exact Der.var hΓ (lookup_of_ctxGet (Option.some.inj h'))
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | univ l =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (Tm.univ l) = some (some A) → HasTy Γ (Tm.univ l) A := by
        intro A h
        cases h
        exact Der.univU l hΓ
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | nat =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ Tm.nat = some (some A) → HasTy Γ Tm.nat A := by
        intro A h
        cases h
        exact Der.natU hΓ
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | empty =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ Tm.empty = some (some A) → HasTy Γ Tm.empty A := by
        intro A h
        cases h
        exact Der.emptyU hΓ
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | zero =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ Tm.zero = some (some A) → HasTy Γ Tm.zero A := by
        intro A h
        cases h
        exact Der.zero hΓ
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | succ m ihm =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (succ m) = some (some A) → HasTy Γ (succ m) A := by
        intro A h
        rw [tcInfer_succ] at h
        rcases ofBool_eq_some h with ⟨_, h'⟩ | ⟨hc, h'⟩
        · cases h'
        · cases h'
          exact Der.succ ((ihm hΓ).2 (Der.natT hΓ) hc)
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | pi F G ihF ihG =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (pi F G) = some (some A) → HasTy Γ (pi F G) A := by
        intro A h
        rw [tcInfer_pi] at h
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨T₁, hT₁, h⟩
        · cases h'
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨i, hi, h⟩
        · cases h'
        have hF := ((ihF hΓ).1 hT₁).univView hi
        have hFΓ : WfCtx (F :: Γ) := Der.cons hΓ (Der.el hF)
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨T₂, hT₂, h⟩
        · cases h'
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨j, hj, h⟩
        · cases h'
        have hG := ((ihG hFΓ).1 hT₂).univView hj
        cases h
        exact Der.piU hF hG
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | app f a ihf iha =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (app f a) = some (some A) → HasTy Γ (app f a) A := by
        intro A h
        rw [tcInfer_app] at h
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨T, hT, h⟩
        · cases h'
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨⟨F', G'⟩, hp, h⟩
        · cases h'
        have hf := ((ihf hΓ).1 hT).piView hp
        rcases ofBool_eq_some h with ⟨_, h'⟩ | ⟨hc, h'⟩
        · cases h'
        cases h'
        exact Der.app hf ((iha hΓ).2 hf.wfTy.pi_inv.1 hc)
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | natrec P z s m ihP ihz ihs ihm =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (natrec P z s m) = some (some A) →
          HasTy Γ (natrec P z s m) A := by
        intro A h
        rw [tcInfer_natrec] at h
        have hN : WfCtx (Tm.nat :: Γ) := Der.cons hΓ (Der.natT hΓ)
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨T, hT, h⟩
        · cases h'
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨l, hl, h⟩
        · cases h'
        have hP : WfTy (Tm.nat :: Γ) P := Der.el (((ihP hN).1 hT).univView hl)
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨u₁, hz, h⟩
        · cases h'
        rcases ofBool_eq_some hz with ⟨_, h'⟩ | ⟨hz, -⟩
        · cases h'
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨u₂, hs, h⟩
        · cases h'
        rcases ofBool_eq_some hs with ⟨_, h'⟩ | ⟨hs, -⟩
        · cases h'
        rcases ofBool_eq_some h with ⟨_, h'⟩ | ⟨hm, h'⟩
        · cases h'
        cases h'
        exact Der.natrec hP ((ihz hΓ).2 (hP.inst (Der.zero hΓ)) hz)
          ((ihs (Der.cons hN hP)).2 hP.stepTy hs) ((ihm hΓ).2 (Der.natT hΓ) hm)
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | emptyrec P e ihP ihe =>
      intro n Γ hΓ
      have hinf : ∀ {A}, tcInfer n Γ (emptyrec P e) = some (some A) →
          HasTy Γ (emptyrec P e) A := by
        intro A h
        rw [tcInfer_emptyrec] at h
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨T, hT, h⟩
        · cases h'
        rcases obind_eq_some h with ⟨_, h'⟩ | ⟨l, hl, h⟩
        · cases h'
        have hP : WfTy Γ P := Der.el (((ihP hΓ).1 hT).univView hl)
        rcases ofBool_eq_some h with ⟨_, h'⟩ | ⟨he, h'⟩
        · cases h'
        cases h'
        exact Der.emptyrec hP ((ihe hΓ).2 (Der.emptyT hΓ) he)
      exact ⟨hinf, fun hA h => checkVia_sound (fun _ => hinf)
        hA (by rw [← tcCheck_of_not_lam (fun _ e => by cases e)]; exact h)⟩
  | lam b ihb =>
      intro n Γ hΓ
      refine ⟨(fun h => by cases h), fun {A} hA h => ?_⟩
      rw [tcCheck_lam] at h
      rcases checkLam_eq_some h with ⟨_, _, _, hb⟩ | ⟨F, G, e, h⟩
      · cases hb
      have hr := (whnfF_tyTyped hA e).1
      obtain ⟨hF, hG⟩ := hr.wfR.pi_inv
      have hb := (ihb (Der.cons hΓ hF)).2 hG h
      exact Der.conv (Der.lam hF hb) (Der.symmT hr.tyEq)

theorem tcInfer_sound {n : ℕ} {Γ : Ctx} {t A : Tm} (hΓ : WfCtx Γ)
    (h : tcInfer n Γ t = some (some A)) : HasTy Γ t A :=
  (tc_sound t hΓ).1 h

theorem tcCheck_sound {n : ℕ} {Γ : Ctx} {t A : Tm} (hΓ : WfCtx Γ) (hA : WfTy Γ A)
    (h : tcCheck n Γ t A = some true) : HasTy Γ t A :=
  (tc_sound t hΓ).2 hA h

/-! ### The bidirectional fragment -/

/-- **The bidirectional fragment**: `Shape true t` — `t` is inferable; `Shape false t` — `t` is
checkable.  Abstractions are checkable only; they never stand at the head of an application. -/
inductive Shape : Bool → Tm → Prop
  | var (i : ℕ) : Shape true (var i)
  | univ (l : ℕ) : Shape true (Tm.univ l)
  | nat : Shape true Tm.nat
  | empty : Shape true Tm.empty
  | zero : Shape true Tm.zero
  | succ {m : Tm} : Shape false m → Shape true (succ m)
  | pi {F G : Tm} : Shape true F → Shape true G → Shape true (pi F G)
  | app {f a : Tm} : Shape true f → Shape false a → Shape true (app f a)
  | natrec {P z s m : Tm} : Shape true P → Shape false z → Shape false s → Shape false m →
      Shape true (natrec P z s m)
  | emptyrec {P e : Tm} : Shape true P → Shape false e → Shape true (emptyrec P e)
  | lam {b : Tm} : Shape false b → Shape false (lam b)
  | inf {t : Tm} : Shape true t → Shape false t

theorem Shape.not_lam {t : Tm} (h : Shape true t) : ∀ b, t ≠ Tm.lam b := by
  intro b e
  subst e
  cases h

/-! ### Completeness on the fragment -/

/-- The completeness statement for a term of the fragment. -/
def ShapeOK : Bool → Tm → Prop
  | true, t => ∀ {n : ℕ} {Γ : Ctx} {A : Tm} {r : Option Tm}, HasTy Γ t A →
      tcInfer n Γ t = some r → ∃ B, r = some B ∧ TyEq Γ B A
  | false, t => ∀ {n : ℕ} {Γ : Ctx} {A : Tm} {b : Bool}, HasTy Γ t A →
      tcCheck n Γ t A = some b → b = true

/-- A typable term of a type reducing to a universe: the reduct is that universe. -/
theorem univView_complete {n : ℕ} {Γ : Ctx} {T : Tm} {l : ℕ} {r : Option ℕ}
    (hT : TyEq Γ T (Tm.univ l)) (h : univView n T = some r) : r = some l := by
  obtain ⟨T', e, hT'⟩ := univView_eq_some h
  obtain ⟨hr, hn⟩ := whnfF_tyTyped hT.wfL e
  have e' := TyEq.univ_whnf (Der.transT (Der.symmT hT) hr.tyEq) hn
  exact (hT' l).mpr e'

/-- **Completeness of the checker on the bidirectional fragment.** -/
theorem Shape.ok {c : Bool} {t : Tm} (h : Shape c t) : ShapeOK c t := by
  induction h with
  | var i =>
      intro n Γ A r ht h
      obtain ⟨X, hX, hAX⟩ := ht.inv_var
      have h' : some (ctxGet Γ i) = some r := h
      cases h'
      exact ⟨X, ctxGet_of_lookup hX, Der.symmT hAX⟩
  | univ l =>
      intro n Γ A r ht h
      cases h
      exact ⟨_, rfl, Der.symmT ht.inv_univ⟩
  | nat =>
      intro n Γ A r ht h
      cases h
      exact ⟨_, rfl, Der.symmT ht.inv_nat⟩
  | empty =>
      intro n Γ A r ht h
      cases h
      exact ⟨_, rfl, Der.symmT ht.inv_empty⟩
  | zero =>
      intro n Γ A r ht h
      cases h
      exact ⟨_, rfl, Der.symmT ht.inv_zero⟩
  | succ _ ihm =>
      intro n Γ A r ht h
      obtain ⟨hm, hA⟩ := ht.inv_succ
      rw [tcInfer_succ] at h
      rcases ofBool_eq_some h with ⟨hc, -⟩ | ⟨-, rfl⟩
      · cases ihm hm hc
      · exact ⟨_, rfl, Der.symmT hA⟩
  | @pi F G _ _ ihF ihG =>
      intro n Γ A r ht h
      obtain ⟨i, j, hF, hG, hA⟩ := ht.inv_pi
      rw [tcInfer_pi] at h
      rcases obind_eq_some h with ⟨hT₁, -⟩ | ⟨T₁, hT₁, h⟩
      · obtain ⟨B, e, -⟩ := ihF hF hT₁
        cases e
      obtain ⟨_, e₁, hT₁i⟩ := ihF hF hT₁
      cases e₁
      rcases obind_eq_some h with ⟨hu, -⟩ | ⟨i', hi', h⟩
      · cases univView_complete hT₁i hu
      cases univView_complete hT₁i hi'
      rcases obind_eq_some h with ⟨hT₂, -⟩ | ⟨T₂, hT₂, h⟩
      · obtain ⟨B, e, -⟩ := ihG hG hT₂
        cases e
      obtain ⟨_, e₂, hT₂j⟩ := ihG hG hT₂
      cases e₂
      rcases obind_eq_some h with ⟨hu, -⟩ | ⟨j', hj', h⟩
      · cases univView_complete hT₂j hu
      cases univView_complete hT₂j hj'
      cases h
      exact ⟨_, rfl, Der.symmT hA⟩
  | @app f a _ _ ihf iha =>
      intro n Γ A r ht h
      obtain ⟨F, G, hf, ha, hA⟩ := ht.inv_app
      rw [tcInfer_app] at h
      rcases obind_eq_some h with ⟨hT, -⟩ | ⟨T, hT, h⟩
      · obtain ⟨B, e, -⟩ := ihf hf hT
        cases e
      obtain ⟨_, e₁, hTP⟩ := ihf hf hT
      cases e₁
      rcases obind_eq_some h with ⟨hp, -⟩ | ⟨⟨F', G'⟩, hp, h⟩
      · obtain ⟨T', e, hT'⟩ := piView_eq_some hp
        obtain ⟨hr, hn⟩ := whnfF_tyTyped hTP.wfL e
        obtain ⟨H, E, e', -⟩ :=
          TyEq.pi_whnf (Der.transT (Der.symmT hTP) hr.tyEq) hn
        cases (hT' H E).mpr e'
      obtain ⟨T', e, hT'⟩ := piView_eq_some hp
      have eT := (hT' F' G').mp rfl
      subst eT
      obtain ⟨hr, -⟩ := whnfF_tyTyped hTP.wfL e
      obtain ⟨hFF, hGG⟩ := TyEq.pi_inj (Der.transT (Der.symmT hTP) hr.tyEq)
      rcases ofBool_eq_some h with ⟨hc, -⟩ | ⟨-, rfl⟩
      · cases iha (Der.conv ha hFF) hc
      exact ⟨_, rfl, Der.transT (Der.symmT (hGG.inst ha)) (Der.symmT hA)⟩
  | @natrec P z s m _ _ _ _ ihP ihz ihs ihm =>
      intro n Γ A r ht h
      obtain ⟨hP, hz, hs, hm, hA⟩ := ht.inv_natrec
      obtain ⟨l, hPl⟩ := hP.univ
      rw [tcInfer_natrec] at h
      rcases obind_eq_some h with ⟨hT, -⟩ | ⟨T, hT, h⟩
      · obtain ⟨B, e, -⟩ := ihP hPl hT
        cases e
      obtain ⟨_, e₁, hTl⟩ := ihP hPl hT
      cases e₁
      rcases obind_eq_some h with ⟨hu, -⟩ | ⟨l', hl', h⟩
      · cases univView_complete hTl hu
      rcases obind_eq_some h with ⟨hz', -⟩ | ⟨_, hz', h⟩
      · rcases ofBool_eq_some hz' with ⟨hc, -⟩ | ⟨-, e⟩
        · cases ihz hz hc
        · cases e
      rcases ofBool_eq_some hz' with ⟨_, e⟩ | ⟨-, -⟩
      · cases e
      rcases obind_eq_some h with ⟨hs', -⟩ | ⟨_, hs', h⟩
      · rcases ofBool_eq_some hs' with ⟨hc, -⟩ | ⟨-, e⟩
        · cases ihs hs hc
        · cases e
      rcases ofBool_eq_some hs' with ⟨_, e⟩ | ⟨-, -⟩
      · cases e
      rcases ofBool_eq_some h with ⟨hc, -⟩ | ⟨-, rfl⟩
      · cases ihm hm hc
      exact ⟨_, rfl, Der.symmT hA⟩
  | @emptyrec P e _ _ ihP ihe =>
      intro n Γ A r ht h
      obtain ⟨hP, he, hA⟩ := ht.inv_emptyrec
      obtain ⟨l, hPl⟩ := hP.univ
      rw [tcInfer_emptyrec] at h
      rcases obind_eq_some h with ⟨hT, -⟩ | ⟨T, hT, h⟩
      · obtain ⟨B, e, -⟩ := ihP hPl hT
        cases e
      obtain ⟨_, e₁, hTl⟩ := ihP hPl hT
      cases e₁
      rcases obind_eq_some h with ⟨hu, -⟩ | ⟨l', hl', h⟩
      · cases univView_complete hTl hu
      rcases ofBool_eq_some h with ⟨hc, -⟩ | ⟨-, rfl⟩
      · cases ihe he hc
      exact ⟨_, rfl, Der.symmT hA⟩
  | @lam b _ ihb =>
      intro n Γ A bb ht h
      obtain ⟨F₀, G₀, hF₀, hb, hA⟩ := ht.inv_lam
      rw [tcCheck_lam] at h
      rcases checkLam_eq_some h with ⟨T', e, hnp, -⟩ | ⟨F, G, e, h⟩
      · obtain ⟨hr, hn⟩ := whnfF_tyTyped hA.wfL e
        obtain ⟨H, E, e', -⟩ := TyEq.pi_whnf (Der.transT (Der.symmT hA) hr.tyEq) hn
        exact absurd e' (hnp H E)
      obtain ⟨hr, -⟩ := whnfF_tyTyped hA.wfL e
      obtain ⟨hFF, hGG⟩ := TyEq.pi_inj (Der.transT (Der.symmT hA) hr.tyEq)
      exact ihb (HasTy.ctxConv (Der.conv hb hGG) hFF) h
  | @inf t ht ih =>
      intro n Γ A b hty h
      rw [tcCheck_of_not_lam ht.not_lam] at h
      rcases checkVia_eq_some h with ⟨hr, rfl⟩ | ⟨B, hr, hB⟩
      · obtain ⟨_, e, -⟩ := ih hty hr
        cases e
      obtain ⟨_, e, hBA⟩ := ih hty hr
      cases e
      exact ((cRun_correct n).2.1 hBA.wfL hBA.wfR hB).mpr hBA.alg

end MLTT
