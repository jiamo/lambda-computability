import Start.PTSErasureP2Kind

/-!
# The fundamental lemma of the two-level relation for λP2, and expansion postponement

Task `M29-EP-IMPREDICATIVE`, round 10, parts A2–A4, on top of the two-level relation of
`Start/PTSRouteIITwoLevel.lean` and the erasure `erP`/`erK` of `Start/PTSErasureP2Kind.lean`.

* `RouteII.SemT Γ ξ Δ T X Y` — the interpretation of a source type `T`: at `□` the target
  judgement normalizes (`NormNW`); at a kind, `X` is type reducible (`TRed`) at the semantic kind
  `KSem (erK T) ξ`; at a type, `X` is term reducible (`GoodP`) at `erP T` in the environment `ξ`;
* `RouteII.Sem`, `RouteII.SubstOK Γ Δ σ ξ` — **reducible substitutions** into a valid target
  context, with the candidate environment `ξ` interpreting the constructor variables; closed
  under weakening (Kripke), extension (`SubstOK.cons`) and lifting (`SubstOK.lift`);
* `RouteII.fundamental` — **the fundamental lemma** for the conversion judgement
  `HasType (cubeSpec lambdaP2)`: one case per rule (axiom, variable, weakening, product for
  `(∗,∗)`, `(□,∗)`, `(∗,□)`, abstraction, application, conversion);
* `RouteII.SubstOK.ids`, `RouteII.sortFundamental_lambdaP2` — the identity substitution
  (`GoodP.var`, `TRed.var`), hence normalization of every typing to the canonical judgement;
* `hsubstSort_lambdaP2 : HSubstSort (cubeSpec lambdaP2)`,
  `hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2)` (through `hsubstPi_iff_hsubstSort`) and
  **`lambdaP2_expansionPostponement : ExpansionPostponement (cubeSpec lambdaP2)`** (through
  `cube_expansionPostponement_of_hsubstPi`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PureTypeSystem

namespace RouteII

open LambdaPi (Srt)
open ErasureP2
open CoC (Cls cl ncons bindC ctxCl)

/-! ### Closure properties of type reducibility -/

/-- **Weakening of type reducibility.** -/
theorem TRed.weaken : ∀ {Cs : List Cand} {Γ : List (Expr Srt)} {U K : Expr Srt}
    (Γ₀ : List (Expr Srt)) {Δ : List (Expr Srt)}, TRed Cs Γ U K →
    List.Forall₂ Reduces (Γ₀ ++ Γ) Δ → ValidContextNW P2 Δ →
    TRed Cs (Γ₀ ++ Γ) (U.rename (wk Γ₀)) (K.rename (wk Γ₀))
  | [], _, _, _, Γ₀, _, h, hc, hv => NormNW.weaken h Γ₀ hc hv
  | _ :: _, _, _, _, Γ₀, _, h, hc, hv => ⟨NormNW.weaken h.1 Γ₀ hc hv,
      fun Γ₁ N A K' hK hN => by
        rw [rename_wk_wk] at hK ⊢
        rw [← List.append_assoc] at hN ⊢
        exact h.2 (Γ₁ ++ Γ₀) N A K' hK hN⟩

/-- **Type reducibility is closed under conversion of the kind.** -/
theorem TRed.convKind : ∀ {Cs : List Cand}, (∀ C ∈ Cs, IsCandN C) →
    ∀ {Γ : List (Expr Srt)} {U K K₂ : Expr Srt}, TRed Cs Γ U K → Converts K K₂ → TRed Cs Γ U K₂
  | [], _, _, _, _, _, h, hc => NormNW.convType h hc
  | C :: _, hCs, _, _, K, _, h, hc => by
      refine ⟨NormNW.convType h.1 hc, fun Γ₀ N A K' hK hN => ?_⟩
      have hc' : Converts (K.rename (wk Γ₀)) (.pi A K') :=
        converts_trans (converts_rename hc _) (Reduces.converts hK)
      obtain ⟨A₂, K₂', hK₂, hA₂, hK'₂⟩ := converts_pi_reduces hc'
      have hC := hCs C (List.mem_cons_self ..)
      have := h.2 Γ₀ N A₂ K₂' hK₂ (hC.conv hN (Reduces.converts hA₂))
      exact TRed.convKind (fun C' h' => hCs C' (List.mem_cons_of_mem _ h')) this
        (converts_symm (Reduces.converts (Reduces.instantiate hK'₂ .refl)))

/-- **The constructor abstraction case at the type level** (closure under β-expansion). -/
theorem TRed.lam {C : Cand} {Cs : List Cand} {Γ : List (Expr Srt)} {D b K : Expr Srt}
    (hn : NormNW P2 Γ (.lam D b) K)
    (hb : ∀ (Γ₀ : List (Expr Srt)) (N A K' : Expr Srt),
      Reduces (K.rename (wk Γ₀)) (.pi A K') → C (Γ₀ ++ Γ) N A →
      TRed Cs (Γ₀ ++ Γ) ((b.rename (Expr.liftRen (wk Γ₀))).instantiate N) (K'.instantiate N)) :
    TRed (C :: Cs) Γ (.lam D b) K :=
  ⟨hn, fun Γ₀ N A K' hK hN => TRed.expand (.single (Beta.head _ _ _)) (hb Γ₀ N A K' hK hN)⟩

/-- **The type abstraction case `(□,∗)` at the term level** (closure under β-expansion). -/
theorem GoodP.lam_all {κ : KSkP} {τ : SkP} {ξ : ℕ → Cand} (hξ : ∀ i, IsCandN (ξ i))
    {Γ : List (Expr Srt)} {D b T : Expr Srt} (hn : NormNW P2 Γ (.lam D b) T)
    (hb : ∀ (Γ₀ : List (Expr Srt)) (U K B : Expr Srt) (C : Cand), IsCandN C →
      Reduces (T.rename (wk Γ₀)) (.pi K B) → TRed (KSem κ ξ) (Γ₀ ++ Γ) U K →
      GoodP τ (consC C ξ) (Γ₀ ++ Γ) ((b.rename (Expr.liftRen (wk Γ₀))).instantiate U)
        (B.instantiate U)) :
    GoodP (.all κ τ) ξ Γ (.lam D b) T :=
  ⟨hn, fun Γ₀ U K B C hC hT hU => (GoodP.isCandN τ (consC C ξ) (consC_isCandN hC hξ)).expand
    (.single (Beta.head _ _ _)) (hb Γ₀ U K B C hC hT hU)⟩

/-! ### Canonical judgements: sorts, variables and product domains -/

theorem HasTypeNW.star_box_of_valid {Δ : List (Expr Srt)} (hv : ValidContextNW P2 Δ) :
    HasTypeNW P2 Δ (.sort .star) (.sort .box) := by
  induction hv with
  | nil => exact .ax ⟨rfl, rfl⟩
  | cons _ hA ih => exact .weaken ih hA

theorem HasTypeNW.lookup {Δ : List (Expr Srt)} (hv : ValidContextNW P2 Δ) :
    ∀ {n : ℕ} {A : Expr Srt}, Lookup Δ n A → HasTypeNW P2 Δ (.var n) A := by
  induction hv with
  | nil => intro n A hn; cases hn
  | cons _ hB ih =>
      intro n A hn
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

theorem rename_eq_pi {M A B : Expr Srt} {r : ℕ → ℕ} (h : M.rename r = .pi A B) :
    ∃ A₀ B₀, M = .pi A₀ B₀ ∧ A = A₀.rename r ∧ B = B₀.rename (Expr.liftRen r) := by
  cases M with
  | pi A₀ B₀ =>
      simp only [Expr.rename, Expr.pi.injEq] at h
      exact ⟨A₀, B₀, rfl, h.1.symm, h.2.symm⟩
  | _ => simp [Expr.rename] at h

/-- **Generation for canonical products**: the domain of a canonical product is canonically
typed by a sort. -/
theorem HasTypeNW.pi_dom {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasTypeNW P2 Γ M T) :
    ∀ {A B : Expr Srt}, M = .pi A B → ∃ s, HasTypeNW P2 Γ A (.sort s) := by
  induction h with
  | ax _ => intro A B h; cases h
  | var _ _ => intro A B h; cases h
  | weaken hM hA ihM _ =>
      intro A B h
      obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := rename_eq_pi h
      obtain ⟨s, hs⟩ := ihM rfl
      exact ⟨s, .weaken hs hA⟩
  | product hA _ _ _ _ => intro A B h; cases h; exact ⟨_, hA⟩
  | abstraction _ _ _ _ => intro A B h; cases h
  | application _ _ _ _ _ _ _ => intro A B h; cases h

/-- The domain of a normalizable product normalizes. -/
theorem NormNW.pi_dom {Δ : List (Expr Srt)} {A B : Expr Srt} {s : Srt}
    (h : NormNW P2 Δ (.pi A B) (.sort s)) : ∃ s₁, NormNW P2 Δ A (.sort s₁) := by
  obtain ⟨Δ', M', T', hc, hM, hT, hNW⟩ := h
  obtain ⟨A', B', rfl, hA, -⟩ := Reduces.pi_inv hM
  obtain ⟨s₁, hs₁⟩ := HasTypeNW.pi_dom hNW rfl
  exact ⟨s₁, Δ', A', _, hc, hA, .refl, hs₁⟩

/-- The new variable of a context extended by a normalizable type normalizes. -/
theorem NormNW.var0 {Δ : List (Expr Srt)} {X A : Expr Srt} {s : Srt}
    (h : NormNW P2 Δ X (.sort s)) (hr : Reduces A X) :
    NormNW P2 (X :: Δ) (.var 0) (A.rename Nat.succ) := by
  obtain ⟨Δ', X', T', hc, hX, hT, hNW⟩ := h
  rw [Reduces.sort_eq hT] at hNW
  exact ⟨X' :: Δ', .var 0, X'.rename Nat.succ, .cons hX hc, .refl,
    Reduces.rename (hr.trans hX) _, .var hNW⟩

/-- A normalizable judgement lives in a context which normalizes to a canonical one. -/
theorem NormNW.ctx {Δ : List (Expr Srt)} {M T : Expr Srt} (h : NormNW P2 Δ M T) :
    ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW P2 Δ' := by
  obtain ⟨Δ', M', T', hc, -, -, hNW⟩ := h
  exact ⟨Δ', hc, hNW.valid⟩

/-! ### The semantics of a judgement, by the class of its type -/

/-- Whether a class is the class of kinds. -/
def IsKindCls : Cls → Prop
  | .kind _ => True
  | _ => False

instance (c : Cls) : Decidable (IsKindCls c) := by
  cases c <;> simp only [IsKindCls] <;> infer_instance

theorem isKindCls_iff {c : Cls} : IsKindCls c ↔ ∃ k, c = .kind k := by
  cases c <;> simp [IsKindCls]

open Classical in
/-- **The semantics of the type `T` of `Γ`** at a target judgement `Δ ⊢ X : Y`, with the
candidates `ξ` for the (constructor) variables of `Γ`: for `T = □` (`X` a kind) normalization;
for a kind `T` (`X` a constructor) type reducibility at the semantic kind of `erK T`; otherwise
(`X` an object) term reducibility at the skeleton `erP T`. -/
noncomputable def SemT (Γ : List (Expr Srt)) (ξ : ℕ → Cand) (Δ : List (Expr Srt))
    (T X Y : Expr Srt) : Prop :=
  if T = .sort .box then NormNW P2 Δ X Y
  else if IsKindCls (cl (ctxCl Γ) T) then TRed (KSem (erK (ctxCl Γ) SkP.base T) ξ) Δ X Y
  else GoodP (erP (ctxCl Γ) SkP.base T) ξ Δ X Y

section SemT

variable {Γ : List (Expr Srt)} {ξ : ℕ → Cand} {Δ : List (Expr Srt)} {T X Y : Expr Srt}

theorem SemT_box : SemT Γ ξ Δ (.sort .box) X Y ↔ NormNW P2 Δ X Y := by
  unfold SemT; rw [ite_eq_left rfl]

theorem SemT_kind (hT : T ≠ .sort .box) (hk : IsKindCls (cl (ctxCl Γ) T)) :
    SemT Γ ξ Δ T X Y ↔ TRed (KSem (erK (ctxCl Γ) SkP.base T) ξ) Δ X Y := by
  unfold SemT; rw [ite_eq_right hT, ite_eq_left hk]

theorem SemT_type (hT : T ≠ .sort .box) (hk : ¬ IsKindCls (cl (ctxCl Γ) T)) :
    SemT Γ ξ Δ T X Y ↔ GoodP (erP (ctxCl Γ) SkP.base T) ξ Δ X Y := by
  unfold SemT; rw [ite_eq_right hT, ite_eq_right hk]

/-- CR1 for the semantics. -/
theorem SemT.norm (hξ : ∀ i, IsCandN (ξ i)) (h : SemT Γ ξ Δ T X Y) : NormNW P2 Δ X Y := by
  unfold SemT at h
  split_ifs at h
  · exact h
  · exact h.escape
  · exact (GoodP.isCandN _ ξ hξ).norm h

/-- The semantics is closed under conversion of the target type. -/
theorem SemT.conv (hξ : ∀ i, IsCandN (ξ i)) (h : SemT Γ ξ Δ T X Y) {Y' : Expr Srt}
    (hc : Converts Y Y') : SemT Γ ξ Δ T X Y' := by
  unfold SemT at h ⊢
  split_ifs at h ⊢
  · exact h.convType hc
  · exact TRed.convKind (KSem.isCandN _ ξ hξ) h hc
  · exact (GoodP.isCandN _ ξ hξ).conv h hc

/-- The semantics is closed under expansion of the subject. -/
theorem SemT.expand (hξ : ∀ i, IsCandN (ξ i)) {X' : Expr Srt} (hr : Reduces X X')
    (h : SemT Γ ξ Δ T X' Y) : SemT Γ ξ Δ T X Y := by
  unfold SemT at h ⊢
  split_ifs at h ⊢
  · exact NormNW.expand hr h
  · exact TRed.expand hr h
  · exact (GoodP.isCandN _ ξ hξ).expand hr h

/-- The semantics is closed under weakening. -/
theorem SemT.weaken (hξ : ∀ i, IsCandN (ξ i)) (h : SemT Γ ξ Δ T X Y) (Γ₀ : List (Expr Srt))
    {Δ' : List (Expr Srt)} (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ')
    (hv : ValidContextNW P2 Δ') :
    SemT Γ ξ (Γ₀ ++ Δ) T (X.rename (wk Γ₀)) (Y.rename (wk Γ₀)) := by
  unfold SemT at h ⊢
  split_ifs at h ⊢
  · exact h.weaken Γ₀ hc hv
  · exact TRed.weaken Γ₀ h hc hv
  · exact (GoodP.isCandN _ ξ hξ).weaken Γ₀ h hc hv

/-- CR3 at variables for the semantics. -/
theorem SemT.var (hξ : ∀ i, IsCandN (ξ i)) {x : ℕ} (h : NormNW P2 Δ (.var x) Y) :
    SemT Γ ξ Δ T (.var x) Y := by
  unfold SemT
  split_ifs
  · exact h
  · exact TRed.var (KSem.isCandN _ ξ hξ) h
  · exact GoodP.var hξ h

/-- At a sort, the semantics is normalization. -/
theorem SemT_sort {s : Srt} : SemT Γ ξ Δ (.sort s) X Y ↔ NormNW P2 Δ X Y := by
  cases s with
  | box => exact SemT_box
  | star =>
      rw [SemT_kind (by simp) (by simp [cl, IsKindCls])]
      simp only [erK, KSem, TRed]

end SemT

theorem erP_ctx_succ (A : Expr Srt) (Γ : List (Expr Srt)) (B : Expr Srt) :
    erP (ctxCl (A :: Γ)) SkP.base (B.rename Nat.succ) =
      (erP (ctxCl Γ) SkP.base B).rename Nat.succ := by
  rw [erP_rename, (erPK_skRename B _ _ _).1]
  rfl

theorem erK_ctx_succ (A : Expr Srt) (Γ : List (Expr Srt)) (B : Expr Srt) :
    erK (ctxCl (A :: Γ)) SkP.base (B.rename Nat.succ) =
      (erK (ctxCl Γ) SkP.base B).rename Nat.succ := by
  rw [erK_rename, (erPK_skRename B _ _ _).2]
  rfl

theorem cl_ctx_succ (A : Expr Srt) (Γ : List (Expr Srt)) (B : Expr Srt) :
    cl (ctxCl (A :: Γ)) (B.rename Nat.succ) = cl (ctxCl Γ) B := by
  rw [CoC.cl_rename, CoC.ctxCl_cons_comp_succ]

theorem rename_succ_eq_box {B : Expr Srt} : B.rename Nat.succ = .sort .box ↔ B = .sort .box := by
  cases B <;> simp [Expr.rename]

/-- **The semantics commutes with weakening of the source context.** -/
theorem SemT_rename_succ (A : Expr Srt) (Γ : List (Expr Srt)) (ξ : ℕ → Cand)
    (Δ : List (Expr Srt)) (B X Y : Expr Srt) :
    SemT (A :: Γ) ξ Δ (B.rename Nat.succ) X Y ↔ SemT Γ (fun i => ξ (i + 1)) Δ B X Y := by
  unfold SemT
  simp only [rename_succ_eq_box, cl_ctx_succ, erP_ctx_succ, erK_ctx_succ, GoodP_rename,
    KSem_rename]

/-- The semantics of a judgement `Γ ⊢ M : T` under the substitution `σ`. -/
noncomputable def Sem (Γ : List (Expr Srt)) (ξ : ℕ → Cand) (Δ : List (Expr Srt))
    (M T : Expr Srt) (σ : ℕ → Expr Srt) : Prop :=
  SemT Γ ξ Δ T (M.subst σ) (T.subst σ)

/-- **Reducible substitutions**: the target context normalizes to a canonical one, the
candidates are candidates, and every variable of `Γ` is sent to a term in the semantics of its
declared type (objects in `GoodP (erP A) ξ`, constructor variables `X : K` in
`TRed (KSem (erK K) ξ)`). -/
structure SubstOK (Γ Δ : List (Expr Srt)) (σ : ℕ → Expr Srt) (ξ : ℕ → Cand) : Prop where
  cands : ∀ i, IsCandN (ξ i)
  ctx : ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW P2 Δ'
  var : ∀ n A, Lookup Γ n A → Sem Γ ξ Δ (.var n) A σ

/-- Extending a substitution. -/
def scons (N : Expr Srt) (σ : ℕ → Expr Srt) : ℕ → Expr Srt
  | 0 => N
  | n + 1 => σ n

theorem SubstOK.tail {A : Expr Srt} {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt}
    {ξ : ℕ → Cand} (h : SubstOK (A :: Γ) Δ σ ξ) :
    SubstOK Γ Δ (fun n => σ (n + 1)) (fun i => ξ (i + 1)) where
  cands i := h.cands (i + 1)
  ctx := h.ctx
  var n B hB := by
    have := h.var (n + 1) (B.rename Nat.succ) (.succ A hB)
    unfold Sem at this ⊢
    rw [Expr.subst_rename, SemT_rename_succ] at this
    exact this

theorem SubstOK.weaken {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ℕ → Cand}
    (h : SubstOK Γ Δ σ ξ) (Γ₀ : List (Expr Srt)) {Δ' : List (Expr Srt)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ') (hv : ValidContextNW P2 Δ') :
    SubstOK Γ (Γ₀ ++ Δ) (fun n => (σ n).rename (wk Γ₀)) ξ where
  cands := h.cands
  ctx := ⟨Δ', hc, hv⟩
  var n B hB := by
    have := (h.var n B hB).weaken h.cands Γ₀ hc hv
    unfold Sem at this ⊢
    simp only [Expr.rename_subst] at this
    exact this

theorem SubstOK.cons {A N : Expr Srt} {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt}
    {ξ : ℕ → Cand} {C : Cand} (h : SubstOK Γ Δ σ ξ) (hC : IsCandN C)
    (hN : SemT Γ ξ Δ A N (A.subst σ)) :
    SubstOK (A :: Γ) Δ (scons N σ) (consC C ξ) where
  cands := consC_isCandN hC h.cands
  ctx := h.ctx
  var n B hB := by
    unfold Sem
    cases hB with
    | zero =>
        rw [Expr.subst_rename, SemT_rename_succ]
        exact hN
    | succ _ hB =>
        rw [Expr.subst_rename, SemT_rename_succ]
        exact h.var _ _ hB

theorem liftSub_eq_scons (σ : ℕ → Expr Srt) :
    Expr.liftSub σ = scons (.var 0) (fun n => (σ n).rename Nat.succ) := by
  funext n; cases n <;> rfl

theorem wk_single (X : Expr Srt) : wk [X] = Nat.succ := by
  funext n; simp [wk]

/-- **Lifting a reducible substitution under a binder** whose substituted domain reduces to a
normalizable type `X`. -/
theorem SubstOK.lift {A X : Expr Srt} {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt}
    {ξ : ℕ → Cand} {C : Cand} {s : Srt} (h : SubstOK Γ Δ σ ξ) (hC : IsCandN C)
    (hX : NormNW P2 Δ X (.sort s)) (hr : Reduces (A.subst σ) X) :
    SubstOK (A :: Γ) (X :: Δ) (Expr.liftSub σ) (consC C ξ) := by
  have h0 := NormNW.var0 hX hr
  obtain ⟨Δ', hc, hv⟩ := h0.ctx
  have hw := h.weaken [X] hc hv
  rw [wk_single] at hw
  rw [liftSub_eq_scons]
  refine hw.cons hC (SemT.var h.cands ?_)
  rw [← Expr.rename_subst]
  exact h0

/-! ### Typing and the class of a type -/

theorem type_branch {Γ : List (Expr Srt)} {T : Expr Srt}
    (h : HasType P2 Γ T (.sort .star)) :
    T ≠ .sort .box ∧ ¬ IsKindCls (cl (ctxCl Γ) T) := by
  refine ⟨CoC.ne_box_of_hasType h, fun hk => ?_⟩
  obtain ⟨k, hk⟩ := isKindCls_iff.1 hk
  exact CoC.not_kind h (cube_star_box _ h.valid) k hk

theorem kind_branch {Γ : List (Expr Srt)} {T : Expr Srt}
    (h : HasType P2 Γ T (.sort .box)) :
    T ≠ .sort .box ∧ IsKindCls (cl (ctxCl Γ) T) :=
  ⟨CoC.ne_box_of_hasType h, isKindCls_iff.2 (CoC.kind_cl h)⟩

/-- **The semantics depends only on the conversion class of a typed type.** -/
theorem SemT_srcConv {Γ : List (Expr Srt)} {ξ : ℕ → Cand} {Δ : List (Expr Srt)}
    {A B X Y : Expr Srt} {s : Srt} (hA : HasType P2 Γ A (.sort s))
    (hB : HasType P2 Γ B (.sort s)) (hc : Converts A B) :
    SemT Γ ξ Δ A X Y ↔ SemT Γ ξ Δ B X Y := by
  cases s with
  | star =>
      have hA' := type_branch hA
      have hB' := type_branch hB
      rw [SemT_type hA'.1 hA'.2, SemT_type hB'.1 hB'.2, erP_conv hA hB hc]
  | box =>
      have hA' := kind_branch hA
      have hB' := kind_branch hB
      rw [SemT_kind hA'.1 hA'.2, SemT_kind hB'.1 hB'.2, erK_conv hA hB hc]

theorem piCls_isKind {cA c : Cls} (h : IsKindCls (CoC.piCls cA c)) : IsKindCls c := by
  cases c <;> simp_all [CoC.piCls, IsKindCls]

theorem isC_piCls_of_not_kind {cA c : Cls} (h : ¬ IsKindCls (CoC.piCls cA c)) :
    IsC (CoC.piCls cA c) := by
  cases c <;> simp_all [CoC.piCls, IsKindCls, IsC]

/-! ### Skeleton bookkeeping at binders -/

theorem base_subst_eq (τ : ℕ → SkP) : (fun i => (SkP.base i).subst τ) = τ := rfl

theorem erP_obj_bind (Δc : ℕ → Cls) (B : Expr Srt) :
    erP Δc (ncons junkP SkP.base) B = (erP Δc SkP.base B).subst (ncons junkP SkP.base) := by
  rw [erP_skSubst, base_subst_eq]

theorem erK_obj_bind (Δc : ℕ → Cls) (B : Expr Srt) :
    erK Δc (ncons junkP SkP.base) B = (erK Δc SkP.base B).subst (ncons junkP SkP.base) := by
  rw [erK_skSubst, base_subst_eq]

theorem goodP_ncons_junk (ξ : ℕ → Cand) :
    (fun i => GoodP (ncons junkP SkP.base i) ξ) = consC (GoodP junkP ξ) ξ := by
  funext i; cases i <;> rfl

theorem GoodP_obj_bind (Δc : ℕ → Cls) (B : Expr Srt) (ξ : ℕ → Cand) :
    GoodP (erP Δc (ncons junkP SkP.base) B) ξ =
      GoodP (erP Δc SkP.base B) (consC (GoodP junkP ξ) ξ) := by
  rw [erP_obj_bind, GoodP_subst, goodP_ncons_junk]

theorem KSem_obj_bind (Δc : ℕ → Cls) (B : Expr Srt) (ξ : ℕ → Cand) :
    KSem (erK Δc (ncons junkP SkP.base) B) ξ =
      KSem (erK Δc SkP.base B) (consC (GoodP junkP ξ) ξ) := by
  rw [erK_obj_bind, KSem_subst, goodP_ncons_junk]

theorem erP_pi_kind' {Δ : ℕ → Cls} {ρ : ℕ → SkP} {A B : Expr Srt} {a : CoC.Sk}
    (h : IsC (cl Δ (.pi A B))) (hA : cl Δ A = .kind a) :
    erP Δ ρ (.pi A B) = .all (erK Δ ρ A) (erP (ncons (.constr a) Δ) (upSP ρ) B) := by
  have h' := h
  simp only [cl] at h'
  simp only [erP, ite_eq_left h']
  split
  · rename_i a' ha'
    rw [hA] at ha' ⊢
    cases ha'
    rfl
  · rename_i hne; exact absurd hA (hne a)

theorem erP_pi_type' {Δ : ℕ → Cls} {ρ : ℕ → SkP} {A B : Expr Srt}
    (h : IsC (cl Δ (.pi A B))) (hA : ∀ a, cl Δ A ≠ .kind a) :
    erP Δ ρ (.pi A B) = .arr (erP Δ ρ A) (erP (ncons .obj Δ) (ncons junkP ρ) B) := by
  have h' := h
  simp only [cl] at h'
  simp only [erP, ite_eq_left h']
  rw [CoC.bindC_of_not_kind hA]

/-! ### Substitution algebra -/

theorem subst_scons_wk (b N : Expr Srt) (σ : ℕ → Expr Srt) (Γ₀ : List (Expr Srt)) :
    b.subst (scons N (fun n => (σ n).rename (wk Γ₀))) =
      ((b.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N := by
  simp only [Expr.instantiate, Expr.rename_subst, Expr.subst_subst]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp only [scons, Expr.liftSub, Expr.rename_comp, Expr.subst_rename]
      rw [← Expr.subst_var_rename]
      rfl

/-! ### The fundamental lemma -/

theorem rule_P2_box {s₁ s₂ s₃ : Srt} (hr : P2.rule s₁ s₂ s₃) (h₂ : s₂ = .box) : s₁ = .star := by
  subst h₂
  cases s₁ with
  | star => rfl
  | box => exact absurd hr.2 (by simp [lambdaP2, CubeFeatures.allows])

/-- The Kripke instantiation step of the abstraction case: the body, under the substitution
extended by a reducible argument `N` in a context extension. -/
theorem body_inst {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ℕ → Cand} {A b B : Expr Srt}
    (hσ : SubstOK Γ Δ σ ξ)
    (ihb : ∀ {Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ℕ → Cand},
      SubstOK (A :: Γ) Δ σ ξ → Sem (A :: Γ) ξ Δ b B σ)
    (Γ₀ : List (Expr Srt)) (N : Expr Srt) (C : Cand) (hC : IsCandN C)
    (hN : SemT Γ ξ (Γ₀ ++ Δ) A N ((A.subst σ).rename (wk Γ₀))) :
    SemT (A :: Γ) (consC C ξ) (Γ₀ ++ Δ) B
      (((b.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N)
      (((B.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N) := by
  obtain ⟨Δ', hc, hv⟩ := (hN.norm hσ.cands).ctx
  have hN' : SemT Γ ξ (Γ₀ ++ Δ) A N (A.subst (fun n => (σ n).rename (wk Γ₀))) := by
    rw [← Expr.rename_subst]; exact hN
  have := ihb ((hσ.weaken Γ₀ hc hv).cons hC hN')
  unfold Sem at this
  rw [subst_scons_wk, subst_scons_wk] at this
  exact this

/-- **The fundamental lemma of the two-level relation for λP2**, for the conversion judgement
`HasType (cubeSpec lambdaP2)`: under a reducible substitution into a normalizable target
context, objects are term reducible (`GoodP` at the erased type), constructors are type
reducible (`TRed` at the semantic kind of the erased kind), and kinds normalize. -/
theorem fundamental {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType P2 Γ M T) :
    ∀ {Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ℕ → Cand},
      SubstOK Γ Δ σ ξ → Sem Γ ξ Δ M T σ := by
  induction h with
  | ax hst =>
      intro Δ σ ξ hσ
      obtain ⟨rfl, rfl⟩ := hst
      obtain ⟨Δ', hc, hv⟩ := hσ.ctx
      unfold Sem
      rw [SemT_box]
      exact ⟨Δ', _, _, hc, .refl, .refl, HasTypeNW.star_box_of_valid hv⟩
  | var _ _ =>
      intro Δ σ ξ hσ
      exact hσ.var 0 _ (.zero _ _)
  | weaken _ _ ihM _ =>
      intro Δ σ ξ hσ
      have := ihM hσ.tail
      unfold Sem at this ⊢
      rw [Expr.subst_rename, Expr.subst_rename, SemT_rename_succ]
      exact this
  | @product Γ A B s₁ s₂ s₃ _ _ hr ihA ihB =>
      intro Δ σ ξ hσ
      have hAn : NormNW P2 Δ (A.subst σ) (.sort s₁) := SemT_sort.1 (ihA hσ)
      have hσ' := hσ.lift (GoodP.isCandN junkP ξ hσ.cands) hAn .refl
      have hBn : NormNW P2 (A.subst σ :: Δ) (B.subst (Expr.liftSub σ)) (.sort s₂) :=
        SemT_sort.1 (ihB hσ')
      unfold Sem
      rw [SemT_sort]
      exact NormNW.product hAn hBn hr
  | @abstraction Γ A b B s hb hP ihb ihP =>
      intro Δ σ ξ hσ
      have hξ := hσ.cands
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hP.generation_pi
      have hPn : NormNW P2 Δ ((Expr.pi A B).subst σ) (.sort s) := SemT_sort.1 (ihP hσ)
      obtain ⟨s₁', hAn⟩ := NormNW.pi_dom hPn
      have hbn : NormNW P2 (A.subst σ :: Δ) (b.subst (Expr.liftSub σ))
          (B.subst (Expr.liftSub σ)) :=
        SemT.norm (consC_isCandN (GoodP.isCandN junkP ξ hξ) hξ)
          (ihb (hσ.lift (GoodP.isCandN junkP ξ hξ) hAn .refl))
      have hlam : NormNW P2 Δ ((Expr.lam A b).subst σ) ((Expr.pi A B).subst σ) :=
        NormNW.abstraction hbn hPn
      have hPne : Expr.pi A B ≠ .sort .box := by simp
      have hBne : B ≠ .sort .box := CoC.ne_box_of_hasType hB
      unfold Sem
      by_cases hk : IsKindCls (cl (ctxCl Γ) (.pi A B))
      · -- a constructor abstraction, rule `(∗,□)`
        rw [SemT_kind hPne hk]
        have hBk : IsKindCls (cl (ctxCl (A :: Γ)) B) := piCls_isKind hk
        have hs₂ : s₂ = .box := by
          cases s₂ with
          | box => rfl
          | star => exact absurd hBk (type_branch hB).2
        have hAt := type_branch (rule_P2_box hr hs₂ ▸ hA)
        have hAo : bindC (cl (ctxCl Γ) A) = .obj :=
          CoC.bindC_of_not_kind (fun k hk' => hAt.2 (isKindCls_iff.2 ⟨k, hk'⟩))
        simp only [erK, KSem]
        refine TRed.lam hlam (fun Γ₀ N A' K' hK hN => ?_)
        simp only [Expr.subst, Expr.rename] at hK
        obtain ⟨A₁, K₁, heq, hA₁, hK₁⟩ := Reduces.pi_inv hK
        cases heq
        have hN' : SemT Γ ξ (Γ₀ ++ Δ) A N ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemT_type hAt.1 hAt.2]
          exact (GoodP.isCandN _ ξ hξ).conv hN (converts_symm (Reduces.converts hA₁))
        have := body_inst hσ ihb Γ₀ N _ (GoodP.isCandN junkP ξ hξ) hN'
        rw [SemT_kind hBne hBk] at this
        rw [KSem_obj_bind]
        exact TRed.reduceKind this (Reduces.instantiate hK₁ .refl)
      · rw [SemT_type hPne hk]
        have hBk : ¬ IsKindCls (cl (ctxCl (A :: Γ)) B) := fun h' => hk (by
          simp only [cl]
          obtain ⟨k, hk'⟩ := isKindCls_iff.1 h'
          have : cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) B = .kind k := hk'
          simp [this, CoC.piCls, IsKindCls])
        have hIsC : IsC (cl (ctxCl Γ) (.pi A B)) := isC_piCls_of_not_kind hk
        by_cases hAk : IsKindCls (cl (ctxCl Γ) A)
        · -- a type abstraction, rule `(□,∗)`
          obtain ⟨a, ha⟩ := isKindCls_iff.1 hAk
          rw [erP_pi_kind' hIsC ha]
          have hs₁ : s₁ = .box := by
            cases s₁ with
            | box => rfl
            | star => exact absurd hAk (type_branch hA).2
          have hAk' := kind_branch (hs₁ ▸ hA)
          refine GoodP.lam_all hξ hlam (fun Γ₀ U K B' C hC hT hU => ?_)
          simp only [Expr.subst, Expr.rename] at hT
          obtain ⟨K₁, B₁, heq, hK₁, hB₁⟩ := Reduces.pi_inv hT
          cases heq
          have hU' : SemT Γ ξ (Γ₀ ++ Δ) A U ((A.subst σ).rename (wk Γ₀)) := by
            rw [SemT_kind hAk'.1 hAk]
            exact TRed.convKind (KSem.isCandN _ ξ hξ) hU
              (converts_symm (Reduces.converts hK₁))
          have := body_inst hσ ihb Γ₀ U C hC hU'
          rw [SemT_type hBne hBk] at this
          have hctx : ctxCl (A :: Γ) = ncons (.constr a) (ctxCl Γ) := by
            simp only [CoC.ctxCl, ha]; rfl
          rw [hctx] at this
          rw [SkPL.upSP_base]
          exact (GoodP.isCandN _ _ (consC_isCandN hC hξ)).conv this
            (Reduces.converts (Reduces.instantiate hB₁ .refl))
        · -- an object abstraction, rule `(∗,∗)`
          have hAk2 : ∀ a, cl (ctxCl Γ) A ≠ .kind a :=
            fun a ha => hAk (isKindCls_iff.2 ⟨a, ha⟩)
          rw [erP_pi_type' hIsC hAk2]
          refine GoodP.lam_arr hξ hlam (fun Γ₀ N A' B' hT hN => ?_)
          simp only [Expr.subst, Expr.rename] at hT
          obtain ⟨A₁, B₁, heq, hA₁, hB₁⟩ := Reduces.pi_inv hT
          cases heq
          have hN' : SemT Γ ξ (Γ₀ ++ Δ) A N ((A.subst σ).rename (wk Γ₀)) := by
            rw [SemT_type (CoC.ne_box_of_hasType hA) hAk]
            exact (GoodP.isCandN _ ξ hξ).conv hN (converts_symm (Reduces.converts hA₁))
          have := body_inst hσ ihb Γ₀ N _ (GoodP.isCandN junkP ξ hξ) hN'
          rw [SemT_type hBne hBk] at this
          have hctx : ctxCl (A :: Γ) = ncons .obj (ctxCl Γ) := by
            simp only [CoC.ctxCl, CoC.bindC_of_not_kind hAk2]
          rw [hctx] at this
          rw [GoodP_obj_bind]
          exact (GoodP.isCandN _ _ (consC_isCandN (GoodP.isCandN junkP ξ hξ) hξ)).conv this
            (Reduces.converts (Reduces.instantiate hB₁ .refl))
  | @application Γ F a A B hF ha ihF iha =>
      intro Δ σ ξ hσ
      have hξ := hσ.cands
      have hFs := ihF hσ
      have has := iha hσ
      unfold Sem at hFs has ⊢
      obtain ⟨s, hPs⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPs.generation_pi
      have hBa : HasType P2 Γ (B.instantiate a) (.sort s₂) := hB.instantiate ha
      rw [← Expr.instantiate_subst]
      have hPne : Expr.pi A B ≠ .sort .box := by simp
      by_cases hk : IsKindCls (cl (ctxCl Γ) (.pi A B))
      · -- a family application
        have hBk : IsKindCls (cl (ctxCl (A :: Γ)) B) := piCls_isKind hk
        have hs₂ : s₂ = .box := by
          cases s₂ with
          | box => rfl
          | star => exact absurd hBk (type_branch hB).2
        subst hs₂
        have hAt := type_branch (rule_P2_box hr rfl ▸ hA)
        have hAk2 : ∀ k, cl (ctxCl Γ) A ≠ .kind k :=
          fun k hk' => hAt.2 (isKindCls_iff.2 ⟨k, hk'⟩)
        rw [SemT_kind hPne hk] at hFs
        simp only [erK, KSem] at hFs
        rw [SemT_type hAt.1 hAt.2] at has
        have happ := TRed.app hFs has
        have hBak := kind_branch hBa
        rw [SemT_kind hBak.1 hBak.2]
        have hca : cl (ctxCl Γ) a = .obj := by
          rw [CoC.classify ha (CoC.ne_box_of_hasType hA)]
          exact CoC.bindC_of_not_kind hAk2
        obtain ⟨k, hkB⟩ := isKindCls_iff.1 hBk
        have hkB' : cl (ncons (cl (ctxCl Γ) a) (ctxCl Γ)) B = .kind k := by
          rw [hca, ← CoC.bindC_of_not_kind hAk2]; exact hkB
        rw [erK_instantiate_obj B a (ctxCl Γ) SkP.base junkP (CoC.ctxCl_ne_kind Γ)
          (by rw [hca]; simp [IsC]) (by rw [hca]; simp) hkB', hca]
        rw [CoC.bindC_of_not_kind hAk2] at happ
        exact happ
      · have hBk : ¬ IsKindCls (cl (ctxCl (A :: Γ)) B) := fun h' => hk (by
          simp only [cl]
          obtain ⟨k, hk'⟩ := isKindCls_iff.1 h'
          have : cl (ncons (bindC (cl (ctxCl Γ) A)) (ctxCl Γ)) B = .kind k := hk'
          simp [this, CoC.piCls, IsKindCls])
        have hs₂ : s₂ = .star := by
          cases s₂ with
          | star => rfl
          | box => exact absurd (kind_branch hB).2 hBk
        subst hs₂
        have hBat := type_branch hBa
        rw [SemT_type hBat.1 hBat.2]
        rw [SemT_type hPne hk] at hFs
        have hIsC : IsC (cl (ctxCl Γ) (.pi A B)) := isC_piCls_of_not_kind hk
        by_cases hAk : IsKindCls (cl (ctxCl Γ) A)
        · -- a type application, rule `(□,∗)`
          obtain ⟨k, hkA⟩ := isKindCls_iff.1 hAk
          rw [erP_pi_kind' hIsC hkA] at hFs
          have hs₁ : s₁ = .box := by
            cases s₁ with
            | box => rfl
            | star => exact absurd hAk (type_branch hA).2
          subst hs₁
          have hAk' := kind_branch hA
          rw [SemT_kind hAk'.1 hAk] at has
          have hca : cl (ctxCl Γ) a = .constr k := by
            rw [CoC.classify ha (CoC.ne_box_of_hasType hA), hkA]; rfl
          have := GoodP.tyApp_subst hξ (erP (ctxCl Γ) SkP.base a) hFs has
          rw [erP_instantiate B a (ctxCl Γ) SkP.base (CoC.ctxCl_ne_kind Γ)
            (by rw [hca]; simp), hca]
          exact this
        · -- an object application, rule `(∗,∗)`
          have hAk2 : ∀ k, cl (ctxCl Γ) A ≠ .kind k :=
            fun k hk' => hAk (isKindCls_iff.2 ⟨k, hk'⟩)
          rw [erP_pi_type' hIsC hAk2] at hFs
          rw [SemT_type (CoC.ne_box_of_hasType hA) hAk] at has
          have := GoodP.app hFs has
          have hca : cl (ctxCl Γ) a = .obj := by
            rw [CoC.classify ha (CoC.ne_box_of_hasType hA)]
            exact CoC.bindC_of_not_kind hAk2
          rw [erP_instantiate_obj B a (ctxCl Γ) SkP.base junkP (CoC.ctxCl_ne_kind Γ)
            (by rw [hca]; simp [IsC]) (by rw [hca]; simp), hca]
          exact this
  | @conversion Γ M A B s hM hB hc ihM _ =>
      intro Δ σ ξ hσ
      have hξ := hσ.cands
      have h1 := ihM hσ
      unfold Sem at h1 ⊢
      have h2 := h1.conv hξ (Converts.subst hc σ)
      obtain ⟨t, rfl⟩ | ⟨sA, hA⟩ := hM.regularity
      · cases t with
        | box => exact (CoC.not_conv_box hB (converts_symm hc)).elim
        | star =>
            have hA : HasType P2 Γ (.sort .star) (.sort .box) := cube_star_box _ hM.valid
            have hs := CoC.sort_unique_conv hA hB hc
            subst hs
            exact (SemT_srcConv hA hB hc).1 h2
      · have hs := CoC.sort_unique_conv hA hB hc
        subst hs
        exact (SemT_srcConv hA hB hc).1 h2

/-! ### Hereditary substitution for λP2 by the fundamental lemma -/

/-- The constant candidate assignment: every type variable is interpreted by normalization. -/
def ξN : ℕ → Cand := fun _ => NormNW P2

theorem ξN_cands : ∀ i, IsCandN (ξN i) := fun _ => isCandN_normNW

theorem consC_ξN : consC (NormNW P2) ξN = ξN := by
  funext i; cases i <;> rfl

/-- **The identity substitution is reducible** in every canonically valid context (`GoodP.var`,
`TRed.var`). -/
theorem SubstOK.ids {Γ : List (Expr Srt)} (hv : ValidContextNW P2 Γ) :
    SubstOK Γ Γ Expr.var ξN where
  cands := ξN_cands
  ctx := ⟨Γ, forall₂_reduces_refl Γ, hv⟩
  var n A hn := by
    unfold Sem
    simp only [Expr.subst_var]
    exact SemT.var ξN_cands ⟨Γ, _, _, forall₂_reduces_refl Γ, .refl, .refl,
      HasTypeNW.lookup hv hn⟩

theorem scons_var (N : Expr Srt) : scons N Expr.var = Expr.single N := by
  funext n; cases n <;> rfl

/-- **The substitution of a canonical `N : A` at depth `Δ` is reducible**: below the
substituted position it is the identity (neutral variables, `TRed.var` / `GoodP.var`), and `N`
itself is reducible by the fundamental lemma under the identity substitution. -/
theorem substOK_substAt {Γ : List (Expr Srt)} {N A : Expr Srt} (hN : HasTypeNW P2 Γ N A)
    {Δ Δ' : List (Expr Srt)} (hc : CtxSubstRed N Δ Δ') (hv : ValidContextNW P2 (Δ' ++ Γ)) :
    SubstOK (Δ ++ A :: Γ) (Δ' ++ Γ) (Expr.substAt N Δ.length) ξN := by
  induction hc with
  | nil =>
      have hid := SubstOK.ids hN.valid
      have hNsem : SemT Γ ξN Γ A N (A.subst Expr.var) := by
        have := fundamental hN.toHasType hid
        unfold Sem at this
        simp only [Expr.subst_var] at this ⊢
        exact this
      have := hid.cons isCandN_normNW hNsem
      rw [consC_ξN, scons_var] at this
      exact this
  | @cons Δ Δ' D D' _ hr ih =>
      cases hv with
      | cons hv' hD' =>
          have := (ih hv').lift isCandN_normNW
            ⟨_, D', _, forall₂_reduces_refl _, .refl, .refl, hD'⟩ hr
          rw [consC_ξN, ← Expr.substAt_succ] at this
          exact this

/-- **The sort-typed fundamental lemma for λP2** (`SortFundamental`, route (ii) at the product
premise). -/
theorem sortFundamental_lambdaP2 : SortFundamental P2 := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  have := fundamental hM.toHasType (substOK_substAt hN hc hv)
  unfold Sem at this
  exact SemT_sort.1 this

end RouteII

/-- **Hereditary substitution into sort-typed premises holds in λP2.** -/
theorem hsubstSort_lambdaP2 : HSubstSort (cubeSpec lambdaP2) :=
  RouteII.hsubstSort_of_sortFundamental RouteII.sortFundamental_lambdaP2

/-- **Hereditary substitution into product premises holds in λP2** (the board's target
`HSubstPi (cubeSpec lambdaP2)`, through `hsubstPi_iff_hsubstSort`). -/
theorem hsubstPi_lambdaP2 : HSubstPi (cubeSpec lambdaP2) :=
  (hsubstPi_iff_hsubstSort lambdaP2).2 hsubstSort_lambdaP2

/-- **Product normalization for the reduction-only judgement of λP2.** -/
theorem lambdaP2_productNormalizationR : ProductNormalizationR (cubeSpec lambdaP2) :=
  (cube_expansionPostponement_of_hsubstPi lambdaP2 hsubstPi_lambdaP2).1

/-- **Expansion postponement for λP2** (TLCA open problem 23 for the corner λP2), through
`cube_expansionPostponement_of_hsubstPi`. -/
theorem lambdaP2_expansionPostponement : ExpansionPostponement (cubeSpec lambdaP2) :=
  (cube_expansionPostponement_of_hsubstPi lambdaP2 hsubstPi_lambdaP2).2

end PureTypeSystem
