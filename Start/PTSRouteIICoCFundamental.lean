import Start.PTSRouteIICoC
import Start.PTSRouteIIFundamental

/-!
# Round 11, part A3: the fundamental lemma of route (ii) for coc

The semantics of a judgement `Γ ⊢ M : T` under a substitution `σ` and a valuation `ξ` of
semantic values for the constructor variables: for `T = □`, normalization; otherwise membership
in the candidate `⟦T⟧ξ` of the Fω interpretation over `RouteIICoC.candAlg`.  Kinds and types are
treated uniformly (a kind `Π x:A. K` is interpreted by an object product, `Π α:K. K'` by the
product over a constructor variable), so the rules `(∗,∗)`, `(□,∗)`, `(∗,□)` and `(□,□)` share
one abstraction case and one application case.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace RouteIICoC

open LambdaPi (Srt)
open RouteII (Cand NormNW NeNW wk wk_nil rename_wk_wk converts_pi_reduces converts_rename scons
  liftSub_eq_scons wk_single subst_scons_wk rename_succ_eq_box)
open ErasureCoC (V KAlg canonK ValK extK extK_self interpK interpK_conv interpK_rename
  interpK_instantiate interpK_agree AgreeK)
open CoC (Sk Cls cl ncons bindC RelC WC domSk ctxCl)

/-! ### Canonical judgements for coc -/

theorem HasTypeNW.star_box_of_valid' {Δ : List (Expr Srt)} (hv : ValidContextNW PC Δ) :
    HasTypeNW PC Δ (.sort .star) (.sort .box) := by
  induction hv with
  | nil => exact .ax ⟨rfl, rfl⟩
  | cons _ hA ih => exact .weaken ih hA

theorem HasTypeNW.pi_dom' {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasTypeNW PC Γ M T) :
    ∀ {A B : Expr Srt}, M = .pi A B → ∃ s, HasTypeNW PC Γ A (.sort s) := by
  induction h with
  | ax _ => intro A B h; cases h
  | var _ _ => intro A B h; cases h
  | weaken hM hA ihM _ =>
      intro A B h
      obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := RouteII.rename_eq_pi h
      obtain ⟨s, hs⟩ := ihM rfl
      exact ⟨s, .weaken hs hA⟩
  | product hA _ _ _ _ => intro A B h; cases h; exact ⟨_, hA⟩
  | abstraction _ _ _ _ => intro A B h; cases h
  | application _ _ _ _ _ _ _ => intro A B h; cases h

theorem NormNW.pi_dom' {Δ : List (Expr Srt)} {A B : Expr Srt} {s : Srt}
    (h : NormNW PC Δ (.pi A B) (.sort s)) : ∃ s₁, NormNW PC Δ A (.sort s₁) := by
  obtain ⟨Δ', M', T', hc, hM, hT, hNW⟩ := h
  obtain ⟨A', B', rfl, hA, -⟩ := Reduces.pi_inv hM
  obtain ⟨s₁, hs₁⟩ := HasTypeNW.pi_dom' hNW rfl
  exact ⟨s₁, Δ', A', _, hc, hA, .refl, hs₁⟩

theorem NormNW.var0' {Δ : List (Expr Srt)} {X A : Expr Srt} {s : Srt}
    (h : NormNW PC Δ X (.sort s)) (hr : Reduces A X) :
    NormNW PC (X :: Δ) (.var 0) (A.rename Nat.succ) := by
  obtain ⟨Δ', X', T', hc, hX, hT, hNW⟩ := h
  rw [Reduces.sort_eq hT] at hNW
  exact ⟨X' :: Δ', .var 0, X'.rename Nat.succ, .cons hX hc, .refl,
    Reduces.rename (hr.trans hX) _, .var hNW⟩

theorem NormNW.ctx' {Δ : List (Expr Srt)} {M T : Expr Srt} (h : NormNW PC Δ M T) :
    ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW PC Δ' := by
  obtain ⟨Δ', M', T', hc, -, -, hNW⟩ := h
  exact ⟨Δ', hc, hNW.valid⟩

/-! ### Types whose interpretation is a candidate -/

/-- A type is admissible when it is `□` or its interpretation is a candidate. -/
def TyOK (Γ : List (Expr Srt)) (ξ : ValK Cand) (T : Expr Srt) : Prop :=
  T = .sort .box ∨ IsCandC (interpK candAlg (ctxCl Γ) T .star ξ)

theorem tyOK_of_sorted {Γ : List (Expr Srt)} {ξ : ValK Cand} {T : Expr Srt} {s : Srt}
    (hT : HasType PC Γ T (.sort s)) (hξ : GoodVal (ctxCl Γ) ξ) : TyOK Γ ξ T :=
  .inr (interpC_cand T (CoC.wc_of_hasType hT) hξ (CoC.relC_of_sorted hT))

theorem tyOK_of_typed {Γ : List (Expr Srt)} {ξ : ValK Cand} {M T : Expr Srt}
    (h : HasType PC Γ M T) (hξ : GoodVal (ctxCl Γ) ξ) : TyOK Γ ξ T := by
  rcases CoC.type_sorted h with rfl | ⟨s, hT⟩
  · exact .inl rfl
  · exact tyOK_of_sorted hT hξ

theorem interpK_ctx_succ (A : Expr Srt) (Γ : List (Expr Srt)) (B : Expr Srt) (ξ : ValK Cand) :
    interpK candAlg (ctxCl (A :: Γ)) (B.rename Nat.succ) .star ξ =
      interpK candAlg (ctxCl Γ) B .star (fun i => ξ (i + 1)) := by
  rw [interpK_rename]
  rfl

theorem tyOK_rename_succ (A : Expr Srt) (Γ : List (Expr Srt)) (ξ : ValK Cand) (B : Expr Srt) :
    TyOK (A :: Γ) ξ (B.rename Nat.succ) ↔ TyOK Γ (fun i => ξ (i + 1)) B := by
  unfold TyOK
  rw [rename_succ_eq_box, interpK_ctx_succ]

/-! ### The semantics of a judgement -/

/-- **The semantics of the type `T` of `Γ`** at a target judgement `Δ ⊢ X : Y`. -/
def SemC (Γ : List (Expr Srt)) (ξ : ValK Cand) (Δ : List (Expr Srt)) (T X Y : Expr Srt) :
    Prop :=
  if T = .sort .box then NormNW PC Δ X Y else interpK candAlg (ctxCl Γ) T .star ξ Δ X Y

section SemC

variable {Γ : List (Expr Srt)} {ξ : ValK Cand} {Δ : List (Expr Srt)} {T X Y : Expr Srt}

theorem SemC_ne (hT : T ≠ .sort .box) :
    SemC Γ ξ Δ T X Y ↔ interpK candAlg (ctxCl Γ) T .star ξ Δ X Y := by
  unfold SemC; rw [ite_eq_right hT]

theorem SemC_sort {s : Srt} : SemC Γ ξ Δ (.sort s) X Y ↔ NormNW PC Δ X Y := by
  cases s with
  | box => unfold SemC; rw [ite_eq_left rfl]
  | star => unfold SemC; rw [ite_eq_right (by simp)]; rfl

theorem SemC.norm (hT : TyOK Γ ξ T) (h : SemC Γ ξ Δ T X Y) : NormNW PC Δ X Y := by
  unfold SemC at h
  split_ifs at h with hb
  · exact h
  · exact (hT.resolve_left hb).norm h

theorem SemC.conv (hT : TyOK Γ ξ T) (h : SemC Γ ξ Δ T X Y) {Y' : Expr Srt}
    (hc : Converts Y Y') : SemC Γ ξ Δ T X Y' := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact h.convType hc
  · exact (hT.resolve_left hb).conv h hc

theorem SemC.expand (hT : TyOK Γ ξ T) {X' : Expr Srt} (hr : Reduces X X')
    (h : SemC Γ ξ Δ T X' Y) : SemC Γ ξ Δ T X Y := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact RouteII.NormNW.expand hr h
  · exact (hT.resolve_left hb).expand hr h

theorem SemC.weaken (hT : TyOK Γ ξ T) (h : SemC Γ ξ Δ T X Y) (Γ₀ : List (Expr Srt))
    {Δ' : List (Expr Srt)} (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ')
    (hv : ValidContextNW PC Δ') :
    SemC Γ ξ (Γ₀ ++ Δ) T (X.rename (wk Γ₀)) (Y.rename (wk Γ₀)) := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact h.weaken Γ₀ hc hv
  · exact (hT.resolve_left hb).weaken Γ₀ h hc hv

theorem SemC.var (hT : TyOK Γ ξ T) {x : ℕ} (h : NormNW PC Δ (.var x) Y) :
    SemC Γ ξ Δ T (.var x) Y := by
  unfold SemC
  split_ifs with hb
  · exact h
  · exact (hT.resolve_left hb).neutral (RouteII.NeNW.of_var h)

end SemC

theorem SemC_rename_succ (A : Expr Srt) (Γ : List (Expr Srt)) (ξ : ValK Cand)
    (Δ : List (Expr Srt)) (B X Y : Expr Srt) :
    SemC (A :: Γ) ξ Δ (B.rename Nat.succ) X Y ↔ SemC Γ (fun i => ξ (i + 1)) Δ B X Y := by
  unfold SemC
  rw [interpK_ctx_succ]
  simp only [rename_succ_eq_box]

/-- The semantics of a judgement `Γ ⊢ M : T` under the substitution `σ`. -/
def Sem (Γ : List (Expr Srt)) (ξ : ValK Cand) (Δ : List (Expr Srt))
    (M T : Expr Srt) (σ : ℕ → Expr Srt) : Prop :=
  SemC Γ ξ Δ T (M.subst σ) (T.subst σ)

/-- **Reducible substitutions** for coc. -/
structure SubstOK (Γ Δ : List (Expr Srt)) (σ : ℕ → Expr Srt) (ξ : ValK Cand) : Prop where
  good : GoodVal (ctxCl Γ) ξ
  ctx : ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW PC Δ'
  tys : ∀ n A, Lookup Γ n A → TyOK Γ ξ A
  var : ∀ n A, Lookup Γ n A → Sem Γ ξ Δ (.var n) A σ

theorem GoodVal.tail {A : Expr Srt} {Γ : List (Expr Srt)} {ξ : ValK Cand}
    (h : GoodVal (ctxCl (A :: Γ)) ξ) : GoodVal (ctxCl Γ) (fun i => ξ (i + 1)) :=
  fun n k hk => h (n + 1) k hk

theorem GoodVal.ncons_canon {Δ : Nat → Cls} {ξ : ValK Cand} (h : GoodVal Δ ξ) (c : Cls) :
    GoodVal (ncons c Δ) (ncons (canonK candAlg) ξ) := by
  intro n k hk
  cases n with
  | zero => exact candC_canon k
  | succ n => exact h n k hk

theorem SubstOK.tail {A : Expr Srt} {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt}
    {ξ : ValK Cand} (h : SubstOK (A :: Γ) Δ σ ξ) :
    SubstOK Γ Δ (fun n => σ (n + 1)) (fun i => ξ (i + 1)) where
  good := h.good.tail
  ctx := h.ctx
  tys n B hB := (tyOK_rename_succ A Γ ξ B).1 (h.tys (n + 1) (B.rename Nat.succ) (.succ A hB))
  var n B hB := by
    have := h.var (n + 1) (B.rename Nat.succ) (.succ A hB)
    unfold Sem at this ⊢
    rw [Expr.subst_rename, SemC_rename_succ] at this
    exact this

theorem SubstOK.weaken {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ValK Cand}
    (h : SubstOK Γ Δ σ ξ) (Γ₀ : List (Expr Srt)) {Δ' : List (Expr Srt)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ') (hv : ValidContextNW PC Δ') :
    SubstOK Γ (Γ₀ ++ Δ) (fun n => (σ n).rename (wk Γ₀)) ξ where
  good := h.good
  ctx := ⟨Δ', hc, hv⟩
  tys := h.tys
  var n B hB := by
    have := (h.var n B hB).weaken (h.tys n B hB) Γ₀ hc hv
    unfold Sem at this ⊢
    simp only [Expr.rename_subst] at this
    exact this

theorem SubstOK.cons {A N : Expr Srt} {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt}
    {ξ : ValK Cand} {e : (k : Sk) → V Cand k} (h : SubstOK Γ Δ σ ξ)
    (hg : GoodVal (ctxCl (A :: Γ)) (ncons e ξ)) (hA : TyOK Γ ξ A)
    (hN : SemC Γ ξ Δ A N (A.subst σ)) :
    SubstOK (A :: Γ) Δ (scons N σ) (ncons e ξ) where
  good := hg
  ctx := h.ctx
  tys n B hB := by
    cases hB with
    | zero => exact (tyOK_rename_succ A Γ _ A).2 hA
    | succ _ hB => exact (tyOK_rename_succ A Γ _ _).2 (h.tys _ _ hB)
  var n B hB := by
    unfold Sem
    cases hB with
    | zero =>
        rw [Expr.subst_rename, SemC_rename_succ]
        exact hN
    | succ _ hB =>
        rw [Expr.subst_rename, SemC_rename_succ]
        exact h.var _ _ hB

theorem SubstOK.lift {A X : Expr Srt} {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt}
    {ξ : ValK Cand} {e : (k : Sk) → V Cand k} {s : Srt} (h : SubstOK Γ Δ σ ξ)
    (hg : GoodVal (ctxCl (A :: Γ)) (ncons e ξ)) (hA : TyOK Γ ξ A)
    (hX : NormNW PC Δ X (.sort s)) (hr : Reduces (A.subst σ) X) :
    SubstOK (A :: Γ) (X :: Δ) (Expr.liftSub σ) (ncons e ξ) := by
  have h0 := NormNW.var0' hX hr
  obtain ⟨Δ', hc, hv⟩ := NormNW.ctx' h0
  have hw := h.weaken [X] hc hv
  rw [wk_single] at hw
  rw [liftSub_eq_scons]
  refine hw.cons hg hA (SemC.var hA ?_)
  rw [← Expr.rename_subst]
  exact h0

/-- The Kripke instantiation step of the abstraction case. -/
theorem body_inst {Γ Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ValK Cand}
    {A b B : Expr Srt} {e : (k : Sk) → V Cand k} (hσ : SubstOK Γ Δ σ ξ)
    (hg : GoodVal (ctxCl (A :: Γ)) (ncons e ξ)) (hA : TyOK Γ ξ A)
    (ihb : ∀ {Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ValK Cand},
      SubstOK (A :: Γ) Δ σ ξ → Sem (A :: Γ) ξ Δ b B σ)
    (Γ₀ : List (Expr Srt)) (N : Expr Srt)
    (hN : SemC Γ ξ (Γ₀ ++ Δ) A N ((A.subst σ).rename (wk Γ₀))) :
    SemC (A :: Γ) (ncons e ξ) (Γ₀ ++ Δ) B
      (((b.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N)
      (((B.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N) := by
  obtain ⟨Δ', hc, hv⟩ := NormNW.ctx' (hN.norm hA)
  have hN' : SemC Γ ξ (Γ₀ ++ Δ) A N (A.subst (fun n => (σ n).rename (wk Γ₀))) := by
    rw [← Expr.rename_subst]; exact hN
  have := ihb ((hσ.weaken Γ₀ hc hv).cons hg hA hN')
  unfold Sem at this
  rw [subst_scons_wk, subst_scons_wk] at this
  exact this

/-- The good valuation extending `ξ` at a binder of domain `A`, for a candidate value `v` when
`A` is a kind of skeleton `a`. -/
theorem goodVal_bind_kind {Γ : List (Expr Srt)} {A : Expr Srt} {ξ : ValK Cand} {a : Sk}
    (hξ : GoodVal (ctxCl Γ) ξ) (ha : cl (ctxCl Γ) A = .kind a) {v : V Cand a}
    (hv : CandC a v) : GoodVal (ctxCl (A :: Γ)) (ncons (extK candAlg a v) ξ) := by
  have hctx : ctxCl (A :: Γ) = ncons (.constr a) (ctxCl Γ) := by
    simp only [CoC.ctxCl, ha]; rfl
  rw [hctx]
  exact hξ.ncons_ext hv

theorem ctxCl_bind_obj {Γ : List (Expr Srt)} {A : Expr Srt}
    (hA : ∀ a, cl (ctxCl Γ) A ≠ .kind a) : ctxCl (A :: Γ) = ncons .obj (ctxCl Γ) := by
  simp only [CoC.ctxCl, CoC.bindC_of_not_kind hA]

theorem ctxCl_bind_kind {Γ : List (Expr Srt)} {A : Expr Srt} {a : Sk}
    (ha : cl (ctxCl Γ) A = .kind a) : ctxCl (A :: Γ) = ncons (.constr a) (ctxCl Γ) := by
  simp only [CoC.ctxCl, ha]; rfl

/-! ### Unfolding the interpretation of a product -/

theorem interpK_pi_kind {Δ : Nat → Cls} {A B : Expr Srt} {a : Sk} {ξ : ValK Cand}
    (ha : cl Δ A = .kind a) :
    interpK candAlg Δ (.pi A B) .star ξ = piKC a (interpK candAlg Δ A .star ξ)
      (fun v => interpK candAlg (ncons (.constr a) Δ) B .star (ncons (extK candAlg a v) ξ)) := by
  simp only [interpK, ha]; rfl

theorem interpK_pi_obj {Δ : Nat → Cls} {A B : Expr Srt} {ξ : ValK Cand}
    (hA : ∀ a, cl Δ A ≠ .kind a) :
    interpK candAlg Δ (.pi A B) .star ξ = piOC (interpK candAlg Δ A .star ξ)
      (interpK candAlg (ncons .obj Δ) B .star (ncons (canonK candAlg) ξ)) := by
  rcases h : cl Δ A with a | a | _
  · exact absurd h (hA a)
  · simp only [interpK, h]; rfl
  · simp only [interpK, h]; rfl

/-! ### The fundamental lemma -/

/-- **The fundamental lemma of route (ii) for coc**, for the conversion judgement
`HasType (cubeSpec coc)`: under a reducible substitution into a normalizable target context,
every subject is in the semantics of its type (kinds normalize; constructors and objects are in
the candidate interpreting their type). -/
theorem fundamental {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType PC Γ M T) :
    ∀ {Δ : List (Expr Srt)} {σ : ℕ → Expr Srt} {ξ : ValK Cand},
      SubstOK Γ Δ σ ξ → Sem Γ ξ Δ M T σ := by
  induction h with
  | ax hst =>
      intro Δ σ ξ hσ
      obtain ⟨rfl, rfl⟩ := hst
      obtain ⟨Δ', hc, hv⟩ := hσ.ctx
      unfold Sem
      rw [SemC_sort]
      exact ⟨Δ', _, _, hc, .refl, .refl, HasTypeNW.star_box_of_valid' hv⟩
  | var _ _ =>
      intro Δ σ ξ hσ
      exact hσ.var 0 _ (.zero _ _)
  | weaken _ _ ihM _ =>
      intro Δ σ ξ hσ
      have := ihM hσ.tail
      unfold Sem at this ⊢
      rw [Expr.subst_rename, Expr.subst_rename, SemC_rename_succ]
      exact this
  | @product Γ A B s₁ s₂ s₃ hA _ hr ihA ihB =>
      intro Δ σ ξ hσ
      have hAn : NormNW PC Δ (A.subst σ) (.sort s₁) := SemC_sort.1 (ihA hσ)
      have hσ' := hσ.lift (hσ.good.ncons_canon _) (tyOK_of_sorted hA hσ.good) hAn .refl
      have hBn : NormNW PC (A.subst σ :: Δ) (B.subst (Expr.liftSub σ)) (.sort s₂) :=
        SemC_sort.1 (ihB hσ')
      unfold Sem
      rw [SemC_sort]
      exact RouteII.NormNW.product hAn hBn hr
  | @abstraction Γ A b B s hb hP ihb ihP =>
      intro Δ σ ξ hσ
      have hξ := hσ.good
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hP.generation_pi
      have hPn : NormNW PC Δ ((Expr.pi A B).subst σ) (.sort s) := SemC_sort.1 (ihP hσ)
      obtain ⟨s₁', hAn⟩ := NormNW.pi_dom' hPn
      have hAok := tyOK_of_sorted hA hξ
      have hbn : NormNW PC (A.subst σ :: Δ) (b.subst (Expr.liftSub σ))
          (B.subst (Expr.liftSub σ)) := by
        have hσ' := hσ.lift (hξ.ncons_canon _) hAok hAn .refl
        exact SemC.norm (tyOK_of_sorted hB hσ'.good) (ihb hσ')
      have hlam : NormNW PC Δ ((Expr.lam A b).subst σ) ((Expr.pi A B).subst σ) :=
        RouteII.NormNW.abstraction hbn hPn
      have hBne : B ≠ .sort .box := CoC.ne_box_of_hasType hB
      have hAne : A ≠ .sort .box := CoC.ne_box_of_hasType hA
      have hXA : IsCandC (interpK candAlg (ctxCl Γ) A .star ξ) := hAok.resolve_left hAne
      unfold Sem
      rw [SemC_ne (by simp)]
      by_cases hk : ∃ a, cl (ctxCl Γ) A = .kind a
      · obtain ⟨a, hcA⟩ := hk
        rw [interpK_pi_kind hcA]
        refine ⟨hlam, fun Γ₀ U K B' v hv hT hU => ?_⟩
        simp only [Expr.subst, Expr.rename] at hT
        obtain ⟨K₁, B₁, heq, hK₁, hB₁⟩ := Reduces.pi_inv hT
        cases heq
        have hg := goodVal_bind_kind hξ hcA hv
        have hU' : SemC Γ ξ (Γ₀ ++ Δ) A U ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemC_ne hAne]
          exact hXA.conv hU (RouteII.converts_symm (Reduces.converts hK₁))
        have := body_inst hσ hg hAok ihb Γ₀ U hU'
        rw [SemC_ne hBne, ctxCl_bind_kind hcA] at this
        have hXB : IsCandC (interpK candAlg (ncons (.constr a) (ctxCl Γ)) B .star
            (ncons (extK candAlg a v) ξ)) := by
          have := (tyOK_of_sorted hB hg).resolve_left hBne
          rwa [ctxCl_bind_kind hcA] at this
        refine hXB.expand (.single (.head _ _ _)) ?_
        exact hXB.conv this (Reduces.converts (Reduces.instantiate hB₁ .refl))
      · have hAk : ∀ a, cl (ctxCl Γ) A ≠ .kind a := fun a h => hk ⟨a, h⟩
        rw [interpK_pi_obj hAk]
        refine ⟨hlam, fun Γ₀ N A' B' hT hN => ?_⟩
        simp only [Expr.subst, Expr.rename] at hT
        obtain ⟨A₁, B₁, heq, hA₁, hB₁⟩ := Reduces.pi_inv hT
        cases heq
        have hg : GoodVal (ctxCl (A :: Γ)) (ncons (canonK candAlg) ξ) := hξ.ncons_canon _
        have hN' : SemC Γ ξ (Γ₀ ++ Δ) A N ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemC_ne hAne]
          exact hXA.conv hN (RouteII.converts_symm (Reduces.converts hA₁))
        have := body_inst hσ hg hAok ihb Γ₀ N hN'
        rw [SemC_ne hBne, ctxCl_bind_obj hAk] at this
        have hXB : IsCandC (interpK candAlg (ncons .obj (ctxCl Γ)) B .star
            (ncons (canonK candAlg) ξ)) := by
          have := (tyOK_of_sorted hB hg).resolve_left hBne
          rwa [ctxCl_bind_obj hAk] at this
        refine hXB.expand (.single (.head _ _ _)) ?_
        exact hXB.conv this (Reduces.converts (Reduces.instantiate hB₁ .refl))
  | @application Γ F a A B hF ha ihF iha =>
      intro Δ σ ξ hσ
      have hξ := hσ.good
      have hFs := ihF hσ
      have has := iha hσ
      unfold Sem at hFs has ⊢
      obtain ⟨s, hPs⟩ := hF.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hPs.generation_pi
      have hBa : HasType PC Γ (B.instantiate a) (.sort s₂) := hB.instantiate ha
      have hAne : A ≠ .sort .box := CoC.ne_box_of_hasType hA
      rw [← Expr.instantiate_subst]
      rw [SemC_ne (CoC.ne_box_of_hasType hBa), interpK_instantiate]
      rw [SemC_ne (by simp)] at hFs
      rw [SemC_ne hAne] at has
      have hca : cl (ctxCl Γ) a = bindC (cl (ctxCl Γ) A) := CoC.classify ha hAne
      by_cases hk : ∃ k, cl (ctxCl Γ) A = .kind k
      · obtain ⟨k, hcA⟩ := hk
        rw [interpK_pi_kind hcA] at hFs
        have hcak : cl (ctxCl Γ) a = .constr k := by rw [hca, hcA]; rfl
        have hv : CandC k (interpK candAlg (ctxCl Γ) a k ξ) :=
          interpC_cand a (CoC.wc_of_hasType ha) hξ (.inl hcak)
        have happ := hFs.2 [] (a.subst σ) (A.subst σ) (B.subst (Expr.liftSub σ)) _ hv
          (by rw [wk_nil, Expr.rename_id]; exact .refl) (by simpa using has)
        simp only [wk_nil, Expr.rename_id, List.nil_append] at happ
        rw [hcak]
        have hBwc : WC (ncons (.constr k) (ctxCl Γ)) B := by
          have := CoC.wc_of_hasType hB; rwa [ctxCl_bind_kind hcA] at this
        have hBrel : RelC (cl (ncons (.constr k) (ctxCl Γ)) B) .star := by
          have := CoC.relC_of_sorted hB; rwa [ctxCl_bind_kind hcA] at this
        have hAg : AgreeK (ncons (.constr k) (ctxCl Γ))
            (ncons (extK candAlg k (interpK candAlg (ctxCl Γ) a k ξ)) ξ)
            (ncons (fun k' => interpK candAlg (ctxCl Γ) a k' ξ) ξ) := by
          intro n k' hk'
          cases n with
          | zero =>
              have := RelC.constr_eq hk'
              subst this
              simp
          | succ n => rfl
        rw [← interpK_agree candAlg B hBwc hAg hBrel]
        exact happ
      · have hAk : ∀ k, cl (ctxCl Γ) A ≠ .kind k := fun k h => hk ⟨k, h⟩
        rw [interpK_pi_obj hAk] at hFs
        have hcao : cl (ctxCl Γ) a = .obj := by rw [hca]; exact CoC.bindC_of_not_kind hAk
        have happ := hFs.2 [] (a.subst σ) (A.subst σ) (B.subst (Expr.liftSub σ))
          (by rw [wk_nil, Expr.rename_id]; exact .refl) (by simpa using has)
        simp only [wk_nil, Expr.rename_id, List.nil_append] at happ
        rw [hcao]
        have hBwc : WC (ncons .obj (ctxCl Γ)) B := by
          have := CoC.wc_of_hasType hB; rwa [ctxCl_bind_obj hAk] at this
        have hBrel : RelC (cl (ncons .obj (ctxCl Γ)) B) .star := by
          have := CoC.relC_of_sorted hB; rwa [ctxCl_bind_obj hAk] at this
        have hAg : AgreeK (ncons .obj (ctxCl Γ)) (ncons (canonK candAlg) ξ)
            (ncons (fun k' => interpK candAlg (ctxCl Γ) a k' ξ) ξ) := by
          intro n k' hk'
          cases n with
          | zero => exact hk'.not_obj.elim
          | succ n => rfl
        rw [← interpK_agree candAlg B hBwc hAg hBrel]
        exact happ
  | @conversion Γ M A B s hM hB hc ihM _ =>
      intro Δ σ ξ hσ
      have h1 := ihM hσ
      unfold Sem at h1 ⊢
      have h2 := h1.conv (tyOK_of_typed hM hσ.good) (Converts.subst hc σ)
      have hBne := CoC.ne_box_of_hasType hB
      have hAs : ∃ t, HasType PC Γ A (.sort t) := by
        obtain ⟨t, rfl⟩ | hA := hM.regularity
        · cases t with
          | box => exact (CoC.not_conv_box hB (RouteII.converts_symm hc)).elim
          | star => exact ⟨_, cube_star_box _ hM.valid⟩
        · exact hA
      obtain ⟨t, hA⟩ := hAs
      rw [SemC_ne (CoC.ne_box_of_hasType hA)] at h2
      rw [SemC_ne hBne, ← interpC_conv hA hB hc]
      exact h2

end RouteIICoC

end PureTypeSystem
