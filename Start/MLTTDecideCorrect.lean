/-
**Martin-Löf type theory: the answers of the conversion program are correct** — milestone M30
(`M30-MLTT-CONV`).

* `MLTT.CFns.Correct` — what correct comparisons answer on typed inputs;
* `MLTT.cRun_correct` — **every answer of the run is correct**, by induction on the fuel, through
  the correctness of each step (`neUpStep_correct`, `downStep_correct`, `tyDownStep_correct`,
  `natStep_correct`, `tmDownStep_correct`).
-/

import Start.MLTTDecideRun

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-! ### Auxiliary facts -/

/-- A well-formed neutral type is a term of a universe. -/
theorem WfTy.ne_univ {Γ : Ctx} {K : Tm} (h : WfTy Γ K) (hK : Neutral K) :
    ∃ l, HasTy Γ K (Tm.univ l) := by
  cases h with
  | el h => exact ⟨_, h⟩
  | univT => cases hK
  | natT => cases hK
  | emptyT => cases hK
  | piT => cases hK

/-- The η-expansion of a function, typed under the domain. -/
theorem HasTy.etaApp {Γ : Ctx} {t F G : Tm} (h : HasTy Γ t (pi F G)) :
    HasTy (F :: Γ) (app (shift t) (Tm.var 0)) G := by
  have hwf : WfCtx (F :: Γ) := Der.cons h.wf h.wfTy.pi_inv.1
  have ht := h.weaken hwf
  have hv : HasTy (F :: Γ) (Tm.var 0) (shift F) := Der.var hwf (Lookup.zero Γ F)
  have := Der.app ht hv
  rw [shift_inst_rename] at this
  exact this

theorem TyReds.wfR {Γ : Ctx} {A B : Tm} (h : TyReds Γ A B) : WfTy Γ B := h.tyEq.wfR

theorem andThen_eq_some {r : Option Bool} {k : Unit → Option Bool} {b : Bool}
    (h : andThen r k = some b) : (r = some false ∧ b = false) ∨ (r = some true ∧ k () = some b) := by
  cases r with
  | none => cases h
  | some c =>
      cases c with
      | false =>
          have h' : some false = some b := h
          cases h'
          exact Or.inl ⟨rfl, rfl⟩
      | true => exact Or.inr ⟨rfl, h⟩

theorem andThenNe_eq_some {r : Option Bool} {k : Unit → Option (Option Tm)} {v : Option Tm}
    (h : andThenNe r k = some v) :
    (r = some false ∧ v = none) ∨ (r = some true ∧ k () = some v) := by
  cases r with
  | none => cases h
  | some c =>
      cases c with
      | false =>
          have h' : some none = some v := h
          cases h'
          exact Or.inl ⟨rfl, rfl⟩
      | true => exact Or.inr ⟨rfl, h⟩

/-! ### Correct comparisons -/

/-- The answer `r` of a neutral comparison is correct for the relation `Rel`. -/
def NeAns (Rel : Ctx → Tm → Tm → Tm → Prop) (Γ : Ctx) (k l : Tm) (r : Option Tm) : Prop :=
  (∀ T, r = some T → Rel Γ k l T) ∧ (r = none → ∀ T, ¬ Rel Γ k l T)

/-- **Correct comparisons**: on typed inputs, every answer is correct. -/
def CFns.Correct (R : CFns) : Prop :=
  (∀ {Γ : Ctx} {k l Ak Al : Tm} {r : Option Tm}, HasTy Γ k Ak → HasTy Γ l Al →
      R.neDn Γ k l = some r → NeAns NeDown Γ k l r) ∧
  (∀ {Γ : Ctx} {A B : Tm} {b : Bool}, WfTy Γ A → WfTy Γ B → R.tyUp Γ A B = some b →
      (b = true ↔ TyUp Γ A B)) ∧
  (∀ {Γ : Ctx} {t u A : Tm} {b : Bool}, HasTy Γ t A → HasTy Γ u A → R.tmUp Γ t u A = some b →
      (b = true ↔ TmUp Γ t u A))

/-- Two weak head normal types of the same neutral term, one of them reached by a neutral
comparison, have the same head. -/
theorem NeDown.ty_eq {Γ : Ctx} {k l l' T T' : Tm} (h : NeDown Γ k l T) (h' : NeDown Γ k l' T') :
    TyEq Γ T T' :=
  (NeDown.neutral h).1.tyUnique (NeDown.sound h).tyL (NeDown.sound h').tyL

/-! ### Neutral terms -/

theorem neUpStep_correct {R : CFns} (hR : R.Correct) {Γ : Ctx} {k l Ak Al : Tm} {r : Option Tm}
    (hk : HasTy Γ k Ak) (hl : HasTy Γ l Al) (h : neUpStep R Γ k l = some r) :
    NeAns NeUp Γ k l r := by
  unfold neUpStep at h
  split at h
  · next i j =>
      simp only [Option.some.injEq] at h
      subst h
      constructor
      · intro T hT
        split at hT
        · next hij =>
            subst hij
            exact Alg.varRefl (Der.var hk.wf (lookup_of_ctxGet hT))
        · cases hT
      · intro hr T hT
        obtain ⟨e, hv⟩ := hT.inv_var
        cases e
        obtain ⟨X, hX, -⟩ := hv.inv_var
        rw [ite_eq_left rfl, ctxGet_of_lookup hX] at hr
        cases hr
  · next k a l b =>
      obtain ⟨Fk, Gk, hkF, haF, -⟩ := hk.inv_app
      obtain ⟨Fl, Gl, hlF, hbF, -⟩ := hl.inv_app
      obtain ⟨r₁, hr₁, h⟩ := Option.bind_eq_some_iff.mp h
      have c₁ := hR.1 hkF hlF hr₁
      cases r₁ with
      | none =>
          have h' : some none = some r := h
          cases h'
          refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
          obtain ⟨m, c, F, G, e, hd, -, -⟩ := hT.inv_app
          cases e
          exact c₁.2 rfl _ hd
      | some T₁ =>
          cases T₁
          case pi F G =>
            have hd := c₁.1 _ rfl
            have hnk := (NeDown.neutral hd).1
            have hnl := (NeDown.neutral hd).2
            have hkP := (NeDown.sound hd).tyL
            have hlP := (NeDown.sound hd).tyR
            have haF' := Der.conv haF (Der.symmT (TyEq.pi_inj (hnk.tyUnique hkP hkF)).1)
            have hbF' := Der.conv hbF (Der.symmT (TyEq.pi_inj (hnl.tyUnique hlP hlF)).1)
            have h' : (R.tmUp Γ a b F).map (fun ok => if ok then some (G[a]) else none) = some r := h
            obtain ⟨ok, hok, rfl⟩ := Option.map_eq_some_iff.mp h'
            have c₂ := hR.2.2 haF' hbF' hok
            constructor
            · intro T hT
              cases ok with
              | true =>
                  simp only [ite_true, Option.some.injEq] at hT
                  subst hT
                  exact Alg.appCong hd (c₂.mp rfl)
              | false => simp at hT
            · intro hr T hT
              cases ok with
              | true => simp at hr
              | false =>
                  obtain ⟨m, c, F', G', e, hd', hbc, -⟩ := hT.inv_app
                  cases e
                  have hPP := hd.ty_eq hd'
                  have := c₂.mpr (hbc.conv (Der.symmT (TyEq.pi_inj hPP).1))
                  cases this
          all_goals
            have h' : some none = some r := h
            cases h'
            refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
            obtain ⟨m, c, F', G', e, hd', -, -⟩ := hT.inv_app
            cases e
            have hd₁ := c₁.1 _ rfl
            obtain ⟨H, E, e₂, -⟩ := TyEq.pi_whnf (hd'.ty_eq hd₁) (NeDown.whnf hd₁)
            cases e₂
  · next P z s m P' z' s' m' =>
      obtain ⟨hP, hz, hs, hm, -⟩ := hk.inv_natrec
      obtain ⟨hP', hz', hs', hm', -⟩ := hl.inv_natrec
      rcases andThenNe_eq_some h with ⟨hPr, rfl⟩ | ⟨hPr, h⟩
      · refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
        obtain ⟨_, _, _, _, e, hPP, -⟩ := hT.inv_natrec
        cases e
        exact absurd ((hR.2.1 hP hP' hPr).mpr hPP) (by simp)
      · have hPP := (hR.2.1 hP hP' hPr).mp rfl
        have hPPe := TyUp.sound hPP
        have hz'' : HasTy Γ z' (P[Tm.zero]) :=
          Der.conv hz' (Der.symmT (hPPe.inst (Der.zero hk.wf)))
        rcases andThenNe_eq_some h with ⟨hzr, rfl⟩ | ⟨hzr, h⟩
        · refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
          obtain ⟨_, _, _, _, e, -, hzz, -⟩ := hT.inv_natrec
          cases e
          exact absurd ((hR.2.2 hz hz'' hzr).mpr hzz) (by simp)
        · have hzz := (hR.2.2 hz hz'' hzr).mp rfl
          have hs'' : HasTy (P :: Tm.nat :: Γ) s' (stepTy P) :=
            Der.conv (hs'.ctxConv (Der.symmT hPPe)) (Der.symmT hPPe.stepTy)
          rcases andThenNe_eq_some h with ⟨hsr, rfl⟩ | ⟨hsr, h⟩
          · refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
            obtain ⟨_, _, _, _, e, -, -, hss, -⟩ := hT.inv_natrec
            cases e
            exact absurd ((hR.2.2 hs hs'' hsr).mpr hss) (by simp)
          · have hss := (hR.2.2 hs hs'' hsr).mp rfl
            have h' : (R.neDn Γ m m').map
                (fun r => if r = some Tm.nat then some (P[m]) else none) = some r := h
            obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h'
            have c₂ := hR.1 hm hm' hr₂
            constructor
            · intro T hT
              split at hT
              · next he =>
                  simp only [Option.some.injEq] at hT
                  subst hT
                  exact Alg.natrecCong hPP hzz hss (c₂.1 _ he)
              · cases hT
            · intro hr T hT
              split at hr
              · cases hr
              · next hne =>
                  obtain ⟨_, _, _, _, e, -, -, -, hdn, -⟩ := hT.inv_natrec
                  cases e
                  cases r₂ with
                  | none => exact c₂.2 rfl _ hdn
                  | some T₂ =>
                      have hd₂ := c₂.1 _ rfl
                      exact hne (by rw [TyEq.nat_whnf (hdn.ty_eq hd₂) (NeDown.whnf hd₂)])
  · next P e P' e' =>
      obtain ⟨hP, he, -⟩ := hk.inv_emptyrec
      obtain ⟨hP', he', -⟩ := hl.inv_emptyrec
      rcases andThenNe_eq_some h with ⟨hPr, rfl⟩ | ⟨hPr, h⟩
      · refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
        obtain ⟨_, _, ee, hPP, -⟩ := hT.inv_emptyrec
        cases ee
        exact absurd ((hR.2.1 hP hP' hPr).mpr hPP) (by simp)
      · have hPP := (hR.2.1 hP hP' hPr).mp rfl
        have h' : (R.neDn Γ e e').map
            (fun r => if r = some Tm.empty then some P else none) = some r := h
        obtain ⟨r₂, hr₂, rfl⟩ := Option.map_eq_some_iff.mp h'
        have c₂ := hR.1 he he' hr₂
        constructor
        · intro T hT
          split at hT
          · next hq =>
              simp only [Option.some.injEq] at hT
              subst hT
              exact Alg.emptyrecCong hPP (c₂.1 _ hq)
          · cases hT
        · intro hr T hT
          split at hr
          · cases hr
          · next hne =>
              obtain ⟨_, _, ee, -, hde, -⟩ := hT.inv_emptyrec
              cases ee
              cases r₂ with
              | none => exact c₂.2 rfl _ hde
              | some T₂ =>
                  have hd₂ := c₂.1 _ rfl
                  exact hne (by rw [TyEq.empty_whnf (hde.ty_eq hd₂) (NeDown.whnf hd₂)])
  · next hvv happ hnr hem =>
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
      cases hT with
      | varRefl _ => exact hvv _ _ rfl rfl
      | appCong _ _ => exact happ _ _ _ _ rfl rfl
      | natrecCong _ _ _ _ => exact hnr _ _ _ _ _ _ _ _ rfl rfl
      | emptyrecCong _ _ => exact hem _ _ _ _ rfl rfl

theorem downStep_correct {R : CFns} (hR : R.Correct) {n : ℕ} {Γ : Ctx} {k l Ak Al : Tm}
    {r : Option Tm} (hk : HasTy Γ k Ak) (hl : HasTy Γ l Al)
    (h : downStep n (neUpStep R Γ k l) = some r) : NeAns NeDown Γ k l r := by
  cases e : neUpStep R Γ k l with
  | none => rw [e] at h; cases h
  | some r₀ =>
      have c := neUpStep_correct hR hk hl e
      rw [e] at h
      cases r₀ with
      | none =>
          have h' : some none = some r := h
          cases h'
          refine ⟨(fun T hT => by cases hT), fun _ T hT => ?_⟩
          obtain ⟨B, hB, -, -⟩ := hT.inv
          exact c.2 rfl _ hB
      | some A =>
          have hA := c.1 _ rfl
          have h' : (whnfF n A).map some = some r := h
          obtain ⟨A', hA', rfl⟩ := Option.map_eq_some_iff.mp h'
          obtain ⟨hr, hn⟩ := whnfF_tyTyped (NeUp.sound hA).tyL.wfTy hA'
          exact ⟨(fun T hT => by cases hT; exact Alg.down hA hr hn), (fun h => by cases h)⟩

/-! ### Types -/

theorem tyDownStep_correct {R : CFns} (hR : R.Correct) {Γ : Ctx} {A B : Tm} {b : Bool}
    (hA : WfTy Γ A) (hB : WfTy Γ B) (h : tyDownStep R Γ A B = some b) :
    b = true ↔ TyDown Γ A B := by
  unfold tyDownStep at h
  split at h
  · next i j =>
      simp only [Option.some.injEq] at h
      subst h
      constructor
      · intro e
        have := of_decide_eq_true e
        subst this
        exact Alg.univRefl hA.wf
      · intro hd
        have := hd.inv_univ
        simp only [univ.injEq] at this
        simp [this]
  · simp only [Option.some.injEq] at h
    subst h
    simp only [true_iff]
    exact Alg.natRefl hA.wf
  · simp only [Option.some.injEq] at h
    subst h
    simp only [true_iff]
    exact Alg.emptyRefl hA.wf
  · next F G H E =>
      obtain ⟨hF, hG⟩ := hA.pi_inv
      obtain ⟨hH, hE⟩ := hB.pi_inv
      rcases andThen_eq_some h with ⟨hFr, rfl⟩ | ⟨hFr, h⟩
      · simp only [Bool.false_eq_true, false_iff]
        intro hd
        obtain ⟨_, _, e, hFH, -⟩ := hd.inv_pi
        cases e
        exact absurd ((hR.2.1 hF hH hFr).mpr hFH) (by simp)
      · have hFH := (hR.2.1 hF hH hFr).mp rfl
        have hE' := hE.ctxConv (Der.symmT (TyUp.sound hFH))
        rw [hR.2.1 hG hE' h]
        constructor
        · intro hGE
          exact Alg.piCong hFH hGE
        · intro hd
          obtain ⟨_, _, e, -, hGE⟩ := hd.inv_pi
          cases e
          exact hGE
  · next hu hn he hp =>
      unfold neCmp at h
      split at h
      · next hne =>
          simp only [Bool.and_eq_true, isNe_iff] at hne
          obtain ⟨hnA, hnB⟩ := hne
          obtain ⟨la, hAl⟩ := hA.ne_univ hnA
          obtain ⟨lb, hBl⟩ := hB.ne_univ hnB
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
          have c := hR.1 hAl hBl hr
          constructor
          · intro hu'
            cases r with
            | none => simp [isUnivOpt] at hu'
            | some T =>
                cases T
                case univ l => exact Alg.neTy (c.1 _ rfl)
                all_goals simp [isUnivOpt] at hu'
          · intro hd
            obtain ⟨l', hd'⟩ := hd.inv_ne hnA
            cases r with
            | none => exact absurd hd' (c.2 rfl _)
            | some T =>
                have hd₁ := c.1 _ rfl
                rw [TyEq.univ_whnf (hd'.ty_eq hd₁) (NeDown.whnf hd₁)]
                rfl
      · next hne =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.false_eq_true, false_iff]
          intro hd
          cases hd with
          | univRefl _ => exact hu _ _ rfl rfl
          | natRefl _ => exact hn rfl rfl
          | emptyRefl _ => exact he rfl rfl
          | piCong _ _ => exact hp _ _ _ _ rfl rfl
          | neTy hd' =>
              obtain ⟨h₁, h₂⟩ := NeDown.neutral hd'
              simp [isNe_iff.mpr h₁, isNe_iff.mpr h₂] at hne

/-! ### Terms -/

theorem natStep_correct {R : CFns} (hR : R.Correct) {Γ : Ctx} {t u : Tm} {b : Bool}
    (ht : HasTy Γ t Tm.nat) (hu : HasTy Γ u Tm.nat) (h : natStep R Γ t u = some b) :
    b = true ↔ TmDown Γ t u Tm.nat := by
  unfold natStep at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [true_iff]
    exact Alg.zeroRefl ht.wf
  · next m m' =>
      rw [hR.2.2 ht.inv_succ.1 hu.inv_succ.1 h]
      constructor
      · exact Alg.succCong
      · intro hd
        obtain ⟨_, e, hd'⟩ := hd.inv_succ
        cases e
        exact hd'
  · next hz hs =>
      unfold neCmp at h
      split at h
      · next hne =>
          simp only [Bool.and_eq_true, isNe_iff] at hne
          obtain ⟨hnt, hnu⟩ := hne
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
          have c := hR.1 ht hu hr
          constructor
          · intro hq
            have hq' := of_decide_eq_true hq
            exact Alg.neNat (c.1 _ hq')
          · intro hd
            have hd' := hd.inv_nat_ne hnt
            cases r with
            | none => exact absurd hd' (c.2 rfl _)
            | some T =>
                have hd₁ := c.1 _ rfl
                rw [TyEq.nat_whnf (hd'.ty_eq hd₁) (NeDown.whnf hd₁)]
                simp
      · next hne =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.false_eq_true, false_iff]
          intro hd
          cases hd with
          | neNat hd' =>
              obtain ⟨h₁, h₂⟩ := NeDown.neutral hd'
              simp [isNe_iff.mpr h₁, isNe_iff.mpr h₂] at hne
          | neNe _ _ hA _ => cases hA
          | zeroRefl _ => exact hz rfl rfl
          | succCong _ => exact hs _ _ rfl rfl

theorem tmDownStep_correct {R : CFns} (hR : R.Correct) {Γ : Ctx} {t u A : Tm} {b : Bool}
    (ht : HasTy Γ t A) (hu : HasTy Γ u A) (hnt : Whnf t) (hnu : Whnf u)
    (h : tmDownStep R Γ t u A = some b) : b = true ↔ TmDown Γ t u A := by
  unfold tmDownStep at h
  split at h
  · next l =>
      rw [tyDownStep_correct hR (Der.el ht) (Der.el hu) h]
      constructor
      · exact Alg.univTm ht hu
      · intro hd
        exact hd.inv_univ.2
  · next F G =>
      rw [hR.2.2 ht.etaApp hu.etaApp h]
      constructor
      · exact Alg.eta ht hu hnt hnu
      · intro hd
        exact hd.inv_pi.2.2
  · exact natStep_correct hR ht hu h
  · unfold neCmp at h
    split at h
    · next hne =>
        simp only [Bool.and_eq_true, isNe_iff] at hne
        obtain ⟨hnt', hnu'⟩ := hne
        obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
        have c := hR.1 ht hu hr
        constructor
        · intro hq
          exact Alg.neEmpty (c.1 _ (of_decide_eq_true hq))
        · intro hd
          have hd' := hd.inv_empty
          cases r with
          | none => exact absurd hd' (c.2 rfl _)
          | some T =>
              have hd₁ := c.1 _ rfl
              rw [TyEq.empty_whnf (hd'.ty_eq hd₁) (NeDown.whnf hd₁)]
              simp
    · next hne =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.false_eq_true, false_iff]
        intro hd
        obtain ⟨h₁, h₂⟩ := NeDown.neutral hd.inv_empty
        simp [isNe_iff.mpr h₁, isNe_iff.mpr h₂] at hne
  · next hU hP hN hE =>
      split at h
      · next hA =>
          have hA' := isNe_iff.mp hA
          unfold neCmp at h
          split at h
          · next hne =>
              obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
              have c := hR.1 ht hu hr
              constructor
              · intro hq
                cases r with
                | none => simp at hq
                | some T => exact Alg.neNe ht hu hA' (c.1 _ rfl)
              · intro hd
                obtain ⟨_, -, hd'⟩ := hd.inv_neTy hA'
                cases r with
                | none => exact absurd hd' (c.2 rfl _)
                | some T => rfl
          · next hne =>
              simp only [Option.some.injEq] at h
              subst h
              simp only [Bool.false_eq_true, false_iff]
              intro hd
              obtain ⟨_, -, hd'⟩ := hd.inv_neTy hA'
              obtain ⟨h₁, h₂⟩ := NeDown.neutral hd'
              simp [isNe_iff.mpr h₁, isNe_iff.mpr h₂] at hne
      · next hA =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.false_eq_true, false_iff]
          intro hd
          cases hd with
          | neNat _ => exact hN rfl
          | neEmpty _ => exact hE rfl
          | neNe _ _ hA' _ => exact hA (isNe_iff.mpr hA')
          | univTm _ _ _ => exact hU _ rfl
          | zeroRefl _ => exact hN rfl
          | succCong _ => exact hN rfl
          | eta _ _ _ _ _ => exact hP _ _ rfl

/-! ### The run -/

/-- **Every answer of the run is correct.** -/
theorem cRun_correct : ∀ n, (cRun n).Correct
  | 0 => ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | n + 1 => by
      have hR := cRun_correct n
      refine ⟨fun hk hl h => downStep_correct hR hk hl h, fun {Γ A B b} hA hB h => ?_,
        fun {Γ t u A b} ht hu h => ?_⟩
      · have h' : (match whnfF n A, whnfF n B with
            | some A', some B' => tyDownStep (cRun n) Γ A' B'
            | _, _ => none) = some b := h
        split at h'
        · next A' B' hA' hB' =>
            obtain ⟨rA, nA⟩ := whnfF_tyTyped hA hA'
            obtain ⟨rB, nB⟩ := whnfF_tyTyped hB hB'
            rw [tyDownStep_correct hR rA.wfR rB.wfR h']
            constructor
            · exact Alg.tyRed rA rB nA nB
            · intro hd
              obtain ⟨A₂, B₂, rA₂, rB₂, nA₂, nB₂, hd'⟩ := hd.inv
              rw [TyReds.whnf_unique rA₂ rA nA₂ nA, TyReds.whnf_unique rB₂ rB nB₂ nB] at hd'
              exact hd'
        · cases h'
      · have h' : (match whnfF n A, whnfF n t, whnfF n u with
            | some A', some t', some u' => tmDownStep (cRun n) Γ t' u' A'
            | _, _, _ => none) = some b := h
        split at h'
        · next A' t' u' hA' ht' hu' =>
            obtain ⟨rA, nA⟩ := whnfF_tyTyped ht.wfTy hA'
            obtain ⟨rt, nt⟩ := whnfF_typed (Der.conv ht rA.tyEq) ht'
            obtain ⟨ru, nu⟩ := whnfF_typed (Der.conv hu rA.tyEq) hu'
            rw [tmDownStep_correct hR rt.tyRight ru.tyRight nt nu h']
            constructor
            · exact Alg.tmRed rA rt ru nA nt nu
            · intro hd
              obtain ⟨B₂, t₂, u₂, rA₂, rt₂, ru₂, nA₂, nt₂, nu₂, hd'⟩ := hd.inv
              rw [TyReds.whnf_unique rA₂ rA nA₂ nA] at rt₂ ru₂ hd'
              rw [TReds.whnf_unique rt₂ rt nt₂ nt, TReds.whnf_unique ru₂ ru nu₂ nu] at hd'
              exact hd'
        · cases h'

end MLTT
