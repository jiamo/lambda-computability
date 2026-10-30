import Start.PTSExpansionTopInterpVBeta
import Start.PTSExpansionTopSN
import Start.PTSRouteIIMorphismFundamental

/-!
# Series V, round 3, run 2, part A2: the route (ii) fundamental lemma for every specification
with a morphism into `cocTop` (rows M29-EP-TOP-SORT-FUNDAMENTAL, M29-EP-TOP-MORPHISM)

The morphism fundamental lemma of `Start/PTSRouteIIMorphismFundamental.lean`, with the target
coc replaced by `cocTop` (sorts `∗ : □ : Δ`, rules `(s₁, s₂, s₂)` with `s₁, s₂ ≠ Δ`).  The new
feature of `cocTop` is the kind variable `K : □`; its kind skeleton is the value `θ ℓ` of a
closed skeleton valuation at the level `ℓ` of its declaration.  Candidates are interpreted by
`TopSkel.interpV` (`Start/PTSExpansionTopInterpV.lean`): the abstract interpretation of the coc
image (`□, Δ ↦ □`) in the evaluated context classifier `CT θ Γ = evalCls θ ∘ ctxClV Γ`; its
invariance under conversion is `TopSkel.interpV_conv`.

* `TopFund.SemC` — tests whether the image type is `□` or `Δ` (normalization) and otherwise
  membership in the candidate interpreting it;
* `TopFund.fundamental` — the fundamental lemma for `HasType P`, for every `θ`;
* **`sortFundamental_of_topMorphism (m : TopMorphism P) : SNGeneric.SortFundamental P`**;
* **`expansionPostponement_of_topMorphism (m : TopMorphism P) : ExpansionPostponement P`**;
* **`cocTop_expansionPostponement : ExpansionPostponement cocTop`**;
* `cocTopTwo` (`∗ : □`, `□ : Δ`, `□ : Δ'`): in the top class, not functional, with no morphism into
  coc and no stratification; **`cocTopTwo_expansionPostponement`**.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace TopFund

open LambdaPi (Srt)
open SNGeneric (CandP IsCandC piOC piKC CandC candAlg candC_canon isCandC_normNW GoodVal
  interpC_cand NormNW NeNW wk converts_symm' converts_trans')
open ErasureCoC (V KAlg canonK ValK extK extK_self interpK interpK_rename interpK_instantiate
  interpK_agree AgreeK)
open CoC (Sk Cls cl ncons bindC RelC WC domSk)
open TopSkel

/-- The evaluated context classifier. -/
abbrev CT (θ : Nat → Sk) (Γ : List (Expr Srt3)) : Nat → Cls := evalCls θ ∘ ctxClV Γ

variable {S : Type} {P : Specification S}

theorem mapSort_srtC_eq_box {A : Expr Srt3} :
    A.mapSort srtC = .sort .box ↔ A = .sort .box ∨ A = .sort .top := by
  cases A with
  | sort t => cases t <;> simp [Expr.mapSort, srtC]
  | _ => simp [Expr.mapSort]

theorem ne_boxT_of_sorted {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (h : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top) : A.mapSort srtC ≠ .sort .box := by
  intro e
  rcases mapSort_srtC_eq_box.1 e with rfl | rfl
  · exact ne_box_of_sorted h hs rfl
  · exact top_untypable h

theorem rename_succ_boxT {B : Expr Srt3} :
    (B.rename Nat.succ).mapSort srtC = .sort .box ↔ B.mapSort srtC = .sort .box := by
  rw [Expr.mapSort_rename, MorphFund.rename_succ_eq_box]

/-! ### Admissible types -/

variable (P) in
/-- A `cocTop` type is admissible when its image is `□` (it is `□` or `Δ`) or its interpretation
is a `P`-candidate. -/
def TyOK (θ : Nat → Sk) (Γ : List (Expr Srt3)) (ξ : ValK (CandP S)) (T : Expr Srt3) : Prop :=
  T.mapSort srtC = .sort .box ∨
    IsCandC P (interpK (candAlg P) (CT θ Γ) (T.mapSort srtC) .star ξ)

theorem tyOK_of_sorted (hsn : SystemStronglyNormalizing P) {θ : Nat → Sk}
    {Γ : List (Expr Srt3)} {ξ : ValK (CandP S)} {T : Expr Srt3} {s : Srt3}
    (hT : HasType cocTop Γ T (.sort s)) (hξ : GoodVal P (CT θ Γ) ξ) : TyOK P θ Γ ξ T := by
  by_cases hs : s = .top
  · subst hs
    rcases not_top_typed hT with h | rfl
    · exact absurd rfl h
    · exact .inl rfl
  · exact .inr (interpC_cand hsn _ (wc_toC θ hT) hξ (relC_toC_of_sorted θ hT hs))

theorem tyOK_of_typed (hsn : SystemStronglyNormalizing P) {θ : Nat → Sk}
    {Γ : List (Expr Srt3)} {ξ : ValK (CandP S)} {M T : Expr Srt3}
    (h : HasType cocTop Γ M T) (hξ : GoodVal P (CT θ Γ) ξ) : TyOK P θ Γ ξ T := by
  rcases h.regularity with ⟨t, rfl⟩ | ⟨s, hT⟩
  · cases t with
    | star => exact .inr (isCandC_normNW (P := P))
    | box => exact .inl rfl
    | top => exact .inl rfl
  · exact tyOK_of_sorted hsn hT hξ

theorem interpK_ctx_succ {θ : Nat → Sk} (A : Expr Srt3) (Γ : List (Expr Srt3)) (B : Expr Srt3)
    (ξ : ValK (CandP S)) :
    interpK (candAlg P) (CT θ (A :: Γ)) ((B.rename Nat.succ).mapSort srtC) .star ξ =
      interpK (candAlg P) (CT θ Γ) (B.mapSort srtC) .star (fun i => ξ (i + 1)) := by
  rw [Expr.mapSort_rename, interpK_rename]
  rfl

theorem tyOK_rename_succ {θ : Nat → Sk} (A : Expr Srt3) (Γ : List (Expr Srt3))
    (ξ : ValK (CandP S)) (B : Expr Srt3) :
    TyOK P θ (A :: Γ) ξ (B.rename Nat.succ) ↔ TyOK P θ Γ (fun i => ξ (i + 1)) B := by
  unfold TyOK
  rw [interpK_ctx_succ, rename_succ_boxT]

/-! ### The semantics of a judgement -/

variable (P) in
/-- **The semantics of the (image) type `T`** at a target `P`-judgement `Δ ⊢ X : Y`. -/
def SemC (θ : Nat → Sk) (Γ : List (Expr Srt3)) (ξ : ValK (CandP S)) (Δ : List (Expr S))
    (T : Expr Srt3) (X Y : Expr S) : Prop :=
  if T.mapSort srtC = .sort .box then NormNW P Δ X Y
  else interpK (candAlg P) (CT θ Γ) (T.mapSort srtC) .star ξ Δ X Y

section SemC

variable {θ : Nat → Sk} {Γ : List (Expr Srt3)} {ξ : ValK (CandP S)} {Δ : List (Expr S)}
  {T : Expr Srt3} {X Y : Expr S}

theorem SemC_ne (hT : T.mapSort srtC ≠ .sort .box) :
    SemC P θ Γ ξ Δ T X Y ↔ interpK (candAlg P) (CT θ Γ) (T.mapSort srtC) .star ξ Δ X Y := by
  unfold SemC; rw [ite_eq_right hT]

theorem SemC_sort {s : Srt3} : SemC P θ Γ ξ Δ (.sort s) X Y ↔ NormNW P Δ X Y := by
  cases s with
  | box => unfold SemC; exact iff_of_eq (ite_eq_left rfl)
  | top => unfold SemC; exact iff_of_eq (ite_eq_left rfl)
  | star => unfold SemC; rw [ite_eq_right (by simp [Expr.mapSort, srtC])]; rfl

theorem SemC.norm (hT : TyOK P θ Γ ξ T) (h : SemC P θ Γ ξ Δ T X Y) : NormNW P Δ X Y := by
  unfold SemC at h
  split_ifs at h with hb
  · exact h
  · exact (hT.resolve_left hb).norm h

theorem SemC.conv (hT : TyOK P θ Γ ξ T) (h : SemC P θ Γ ξ Δ T X Y) {Y' : Expr S}
    (hc : Converts Y Y') : SemC P θ Γ ξ Δ T X Y' := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact h.convType hc
  · exact (hT.resolve_left hb).conv h hc

theorem SemC.expand (hT : TyOK P θ Γ ξ T) {X' : Expr S} (hr : Reduces X X')
    (h : SemC P θ Γ ξ Δ T X' Y) : SemC P θ Γ ξ Δ T X Y := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact SNGeneric.NormNW.expand hr h
  · exact (hT.resolve_left hb).expand hr h

theorem SemC.weaken (hT : TyOK P θ Γ ξ T) (h : SemC P θ Γ ξ Δ T X Y) (Γ₀ : List (Expr S))
    {Δ' : List (Expr S)} (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ')
    (hv : ValidContextNW P Δ') :
    SemC P θ Γ ξ (Γ₀ ++ Δ) T (X.rename (wk Γ₀)) (Y.rename (wk Γ₀)) := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact h.weaken Γ₀ hc hv
  · exact (hT.resolve_left hb).weaken Γ₀ h hc hv

theorem SemC.var (hT : TyOK P θ Γ ξ T) {x : ℕ} (h : NormNW P Δ (.var x) Y) :
    SemC P θ Γ ξ Δ T (.var x) Y := by
  unfold SemC
  split_ifs with hb
  · exact h
  · exact (hT.resolve_left hb).neutral (SNGeneric.NeNW.of_var h)

end SemC

theorem SemC_rename_succ {θ : Nat → Sk} (A : Expr Srt3) (Γ : List (Expr Srt3))
    (ξ : ValK (CandP S)) (Δ : List (Expr S)) (B : Expr Srt3) (X Y : Expr S) :
    SemC P θ (A :: Γ) ξ Δ (B.rename Nat.succ) X Y ↔ SemC P θ Γ (fun i => ξ (i + 1)) Δ B X Y := by
  unfold SemC
  rw [interpK_ctx_succ]
  simp only [rename_succ_boxT]

/-- The semantics of a `P`-judgement `Γ ⊢ M : T` under the substitution `σ`, read through the
morphism into `cocTop`. -/
def Sem (m : TopMorphism P) (θ : Nat → Sk) (Γ : List (Expr S)) (ξ : ValK (CandP S))
    (Δ : List (Expr S)) (M T : Expr S) (σ : ℕ → Expr S) : Prop :=
  SemC P θ (Γ.map (Expr.mapSort m.φ)) ξ Δ (T.mapSort m.φ) (M.subst σ) (T.subst σ)

/-- **Reducible substitutions** for `P`, classified through the morphism into `cocTop`. -/
structure SubstOK (m : TopMorphism P) (θ : Nat → Sk) (Γ Δ : List (Expr S)) (σ : ℕ → Expr S)
    (ξ : ValK (CandP S)) : Prop where
  good : GoodVal P (CT θ (Γ.map (Expr.mapSort m.φ))) ξ
  ctx : ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW P Δ'
  tys : ∀ n A, Lookup Γ n A → TyOK P θ (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ)
  var : ∀ n A, Lookup Γ n A → Sem m θ Γ ξ Δ (.var n) A σ

variable {m : TopMorphism P} {θ : Nat → Sk}

theorem GoodVal.tail {A : Expr Srt3} {Γ : List (Expr Srt3)} {ξ : ValK (CandP S)}
    (h : GoodVal P (CT θ (A :: Γ)) ξ) : GoodVal P (CT θ Γ) (fun i => ξ (i + 1)) :=
  fun n k hk => h (n + 1) k hk

theorem GoodVal.ncons_canon {A : Expr Srt3} {Γ : List (Expr Srt3)} {ξ : ValK (CandP S)}
    (h : GoodVal P (CT θ Γ) ξ) : GoodVal P (CT θ (A :: Γ)) (ncons (canonK (candAlg P)) ξ) := by
  intro n k hk
  cases n with
  | zero => exact candC_canon k
  | succ n => exact h n k hk

theorem SubstOK.tail {A : Expr S} {Γ Δ : List (Expr S)} {σ : ℕ → Expr S}
    {ξ : ValK (CandP S)} (h : SubstOK m θ (A :: Γ) Δ σ ξ) :
    SubstOK m θ Γ Δ (fun n => σ (n + 1)) (fun i => ξ (i + 1)) where
  good := GoodVal.tail (A := A.mapSort m.φ) h.good
  ctx := h.ctx
  tys n B hB := by
    have := h.tys (n + 1) (B.rename Nat.succ) (.succ A hB)
    rw [List.map_cons, Expr.mapSort_rename] at this
    exact (tyOK_rename_succ _ _ ξ _).1 this
  var n B hB := by
    have := h.var (n + 1) (B.rename Nat.succ) (.succ A hB)
    unfold Sem at this ⊢
    rw [Expr.subst_rename, List.map_cons, Expr.mapSort_rename, SemC_rename_succ] at this
    exact this

theorem SubstOK.weaken {Γ Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)}
    (h : SubstOK m θ Γ Δ σ ξ) (Γ₀ : List (Expr S)) {Δ' : List (Expr S)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ') (hv : ValidContextNW P Δ') :
    SubstOK m θ Γ (Γ₀ ++ Δ) (fun n => (σ n).rename (wk Γ₀)) ξ where
  good := h.good
  ctx := ⟨Δ', hc, hv⟩
  tys := h.tys
  var n B hB := by
    have := (h.var n B hB).weaken (h.tys n B hB) Γ₀ hc hv
    unfold Sem at this ⊢
    simp only [Expr.rename_subst] at this
    exact this

theorem SubstOK.cons {A N : Expr S} {Γ Δ : List (Expr S)} {σ : ℕ → Expr S}
    {ξ : ValK (CandP S)} {e : (k : Sk) → V (CandP S) k} (h : SubstOK m θ Γ Δ σ ξ)
    (hg : GoodVal P (CT θ ((A :: Γ).map (Expr.mapSort m.φ))) (ncons e ξ))
    (hA : TyOK P θ (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ))
    (hN : SemC P θ (Γ.map (Expr.mapSort m.φ)) ξ Δ (A.mapSort m.φ) N (A.subst σ)) :
    SubstOK m θ (A :: Γ) Δ (MorphFund.scons N σ) (ncons e ξ) where
  good := hg
  ctx := h.ctx
  tys n B hB := by
    rw [List.map_cons]
    cases hB with
    | zero => rw [Expr.mapSort_rename]; exact (tyOK_rename_succ _ _ _ _).2 hA
    | succ _ hB => rw [Expr.mapSort_rename]; exact (tyOK_rename_succ _ _ _ _).2 (h.tys _ _ hB)
  var n B hB := by
    unfold Sem
    rw [List.map_cons]
    cases hB with
    | zero =>
        rw [Expr.subst_rename, Expr.mapSort_rename, SemC_rename_succ]
        exact hN
    | succ _ hB =>
        rw [Expr.subst_rename, Expr.mapSort_rename, SemC_rename_succ]
        exact h.var _ _ hB

theorem SubstOK.lift {A X : Expr S} {Γ Δ : List (Expr S)} {σ : ℕ → Expr S}
    {ξ : ValK (CandP S)} {e : (k : Sk) → V (CandP S) k} {s : S} (h : SubstOK m θ Γ Δ σ ξ)
    (hg : GoodVal P (CT θ ((A :: Γ).map (Expr.mapSort m.φ))) (ncons e ξ))
    (hA : TyOK P θ (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ))
    (hX : NormNW P Δ X (.sort s)) (hr : Reduces (A.subst σ) X) :
    SubstOK m θ (A :: Γ) (X :: Δ) (Expr.liftSub σ) (ncons e ξ) := by
  have h0 := MorphFund.NormNW.var0'' hX hr
  obtain ⟨Δ', hc, hv⟩ := MorphFund.NormNW.ctx'' h0
  have hw := h.weaken [X] hc hv
  rw [MorphFund.wk_single] at hw
  rw [MorphFund.liftSub_eq_scons]
  refine hw.cons hg hA (SemC.var hA ?_)
  rw [← Expr.rename_subst]
  exact h0

/-- The Kripke instantiation step of the abstraction case. -/
theorem body_inst {Γ Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)}
    {A b B : Expr S} {e : (k : Sk) → V (CandP S) k} (hσ : SubstOK m θ Γ Δ σ ξ)
    (hg : GoodVal P (CT θ ((A :: Γ).map (Expr.mapSort m.φ))) (ncons e ξ))
    (hA : TyOK P θ (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ))
    (ihb : ∀ {Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)},
      SubstOK m θ (A :: Γ) Δ σ ξ → Sem m θ (A :: Γ) ξ Δ b B σ)
    (Γ₀ : List (Expr S)) (N : Expr S)
    (hN : SemC P θ (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) N
      ((A.subst σ).rename (wk Γ₀))) :
    SemC P θ ((A :: Γ).map (Expr.mapSort m.φ)) (ncons e ξ) (Γ₀ ++ Δ) (B.mapSort m.φ)
      (((b.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N)
      (((B.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N) := by
  obtain ⟨Δ', hc, hv⟩ := MorphFund.NormNW.ctx'' (hN.norm hA)
  have hN' : SemC P θ (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) N
      (A.subst (fun n => (σ n).rename (wk Γ₀))) := by
    rw [← Expr.rename_subst]; exact hN
  have := ihb ((hσ.weaken Γ₀ hc hv).cons hg hA hN')
  unfold Sem at this
  rw [MorphFund.subst_scons_wk, MorphFund.subst_scons_wk] at this
  exact this

theorem ctxCl_bind_kind {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3} {a : Sk}
    (hA : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top)
    (ha : cl (CT θ Γ) (A.mapSort srtC) = .kind a) :
    CT θ (A :: Γ) = ncons (.constr a) (CT θ Γ) := by
  rw [CT, evalCtx_cons θ hA hs, ha]; rfl

theorem ctxCl_bind_obj {Γ : List (Expr Srt3)} {A : Expr Srt3} {s : Srt3}
    (hA : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top)
    (hk : ∀ a, cl (CT θ Γ) (A.mapSort srtC) ≠ .kind a) :
    CT θ (A :: Γ) = ncons .obj (CT θ Γ) := by
  rw [CT, evalCtx_cons θ hA hs, CoC.bindC_of_not_kind hk]

theorem goodVal_bind_kind {Γ : List (Expr Srt3)} {A : Expr Srt3} {ξ : ValK (CandP S)} {s : Srt3}
    {a : Sk} (hξ : GoodVal P (CT θ Γ) ξ) (hA : HasType cocTop Γ A (.sort s)) (hs : s ≠ .top)
    (ha : cl (CT θ Γ) (A.mapSort srtC) = .kind a) {v : V (CandP S) a}
    (hv : CandC P a v) : GoodVal P (CT θ (A :: Γ)) (ncons (extK (candAlg P) a v) ξ) := by
  rw [ctxCl_bind_kind hA hs ha]
  exact hξ.ncons_ext hv

/-! ### The fundamental lemma -/

/-- **The fundamental lemma of route (ii) through a morphism into `cocTop`**, relative to any
closed skeleton valuation `θ` for the kind variables. -/
theorem fundamental (m : TopMorphism P) (θ : Nat → Sk) {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) :
    ∀ {Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)},
      SubstOK m θ Γ Δ σ ξ → Sem m θ Γ ξ Δ M T σ := by
  have hsn := m.stronglyNormalizing
  induction h with
  | ax hst =>
      intro Δ σ ξ hσ
      obtain ⟨Δ', hc, hv⟩ := hσ.ctx
      unfold Sem
      change SemC P θ _ ξ Δ (.sort _) (.sort _) (.sort _)
      rw [SemC_sort]
      exact ⟨Δ', _, _, hc, .refl, .refl, MorphFund.HasTypeNW.ax_of_valid hv hst⟩
  | var _ _ =>
      intro Δ σ ξ hσ
      exact hσ.var 0 _ (.zero _ _)
  | weaken _ _ ihM _ =>
      intro Δ σ ξ hσ
      have := ihM hσ.tail
      unfold Sem at this ⊢
      rw [Expr.subst_rename, Expr.subst_rename, List.map_cons, Expr.mapSort_rename,
        SemC_rename_succ]
      exact this
  | @product Γ A B s₁ s₂ s₃ hA _ hr ihA ihB =>
      intro Δ σ ξ hσ
      have hAn : NormNW P Δ (A.subst σ) (.sort s₁) := SemC_sort.1 (ihA hσ)
      have hσ' := hσ.lift (GoodVal.ncons_canon hσ.good)
        (tyOK_of_sorted hsn (m.hasType hA) hσ.good) hAn .refl
      have hBn : NormNW P (A.subst σ :: Δ) (B.subst (Expr.liftSub σ)) (.sort s₂) :=
        SemC_sort.1 (ihB hσ')
      unfold Sem
      change SemC P θ _ ξ Δ (.sort _) _ _
      rw [SemC_sort]
      exact SNGeneric.NormNW.product hAn hBn hr
  | @abstraction Γ A b B s hb hP ihb ihP =>
      intro Δ σ ξ hσ
      have hξ := hσ.good
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hP.generation_pi
      have hr' := m.rule_map _ _ _ hr
      have hs₁ : m.φ s₁ ≠ .top := hr'.2.1
      have hs₂ : m.φ s₂ ≠ .top := hr'.2.2
      have hPn : NormNW P Δ ((Expr.pi A B).subst σ) (.sort s) := SemC_sort.1 (ihP hσ)
      obtain ⟨s₁', hAn⟩ := MorphFund.NormNW.pi_dom'' hPn
      have hAc := m.hasType hA
      have hBc := m.hasType hB
      rw [List.map_cons] at hBc
      have hAok := tyOK_of_sorted hsn hAc hξ
      have hbn : NormNW P (A.subst σ :: Δ) (b.subst (Expr.liftSub σ))
          (B.subst (Expr.liftSub σ)) := by
        have hσ' := hσ.lift (GoodVal.ncons_canon hξ) hAok hAn .refl
        exact SemC.norm (tyOK_of_sorted hsn hBc hσ'.good) (ihb hσ')
      have hlam : NormNW P Δ ((Expr.lam A b).subst σ) ((Expr.pi A B).subst σ) :=
        SNGeneric.NormNW.abstraction hbn hPn
      have hBne := ne_boxT_of_sorted hBc hs₂
      have hAne := ne_boxT_of_sorted hAc hs₁
      have hXA : IsCandC P (interpK (candAlg P) (CT θ (Γ.map (Expr.mapSort m.φ)))
          ((A.mapSort m.φ).mapSort srtC) .star ξ) := hAok.resolve_left hAne
      unfold Sem
      rw [SemC_ne (by simp [Expr.mapSort])]
      show interpK (candAlg P) (CT θ (Γ.map (Expr.mapSort m.φ)))
        (.pi ((A.mapSort m.φ).mapSort srtC) ((B.mapSort m.φ).mapSort srtC)) .star ξ Δ _ _
      by_cases hk : ∃ a, cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((A.mapSort m.φ).mapSort srtC) =
          .kind a
      · obtain ⟨a, hcA⟩ := hk
        rw [MorphFund.interpK_pi_kind hcA]
        refine ⟨hlam, fun Γ₀ U K B' v hv hT hU => ?_⟩
        simp only [Expr.subst, Expr.rename] at hT
        obtain ⟨K₁, B₁, heq, hK₁, hB₁⟩ := Reduces.pi_inv hT
        cases heq
        have hg := goodVal_bind_kind hξ hAc hs₁ hcA hv
        have hU' : SemC P θ (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) U
            ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemC_ne hAne]
          exact hXA.conv hU (converts_symm' (Reduces.converts hK₁))
        have := body_inst hσ (by rw [List.map_cons]; exact hg) hAok ihb Γ₀ U hU'
        rw [List.map_cons, SemC_ne hBne, ctxCl_bind_kind hAc hs₁ hcA] at this
        have hXB : IsCandC P (interpK (candAlg P) (ncons (.constr a)
            (CT θ (Γ.map (Expr.mapSort m.φ)))) ((B.mapSort m.φ).mapSort srtC) .star
            (ncons (extK (candAlg P) a v) ξ)) := by
          have := (tyOK_of_sorted hsn hBc hg).resolve_left hBne
          rwa [ctxCl_bind_kind hAc hs₁ hcA] at this
        refine hXB.expand (.single (.head _ _ _)) ?_
        exact hXB.conv this (Reduces.converts (Reduces.instantiate hB₁ .refl))
      · have hAk : ∀ a, cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((A.mapSort m.φ).mapSort srtC) ≠
            .kind a := fun a h => hk ⟨a, h⟩
        rw [MorphFund.interpK_pi_obj hAk]
        refine ⟨hlam, fun Γ₀ N A' B' hT hN => ?_⟩
        simp only [Expr.subst, Expr.rename] at hT
        obtain ⟨A₁, B₁, heq, hA₁, hB₁⟩ := Reduces.pi_inv hT
        cases heq
        have hg : GoodVal P (CT θ (A.mapSort m.φ :: Γ.map (Expr.mapSort m.φ)))
            (ncons (canonK (candAlg P)) ξ) := GoodVal.ncons_canon hξ
        have hN' : SemC P θ (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) N
            ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemC_ne hAne]
          exact hXA.conv hN (converts_symm' (Reduces.converts hA₁))
        have := body_inst hσ (by rw [List.map_cons]; exact hg) hAok ihb Γ₀ N hN'
        rw [List.map_cons, SemC_ne hBne, ctxCl_bind_obj hAc hs₁ hAk] at this
        have hXB : IsCandC P (interpK (candAlg P) (ncons .obj
            (CT θ (Γ.map (Expr.mapSort m.φ)))) ((B.mapSort m.φ).mapSort srtC) .star
            (ncons (canonK (candAlg P)) ξ)) := by
          have := (tyOK_of_sorted hsn hBc hg).resolve_left hBne
          rwa [ctxCl_bind_obj hAc hs₁ hAk] at this
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
      have hr' := m.rule_map _ _ _ hr
      have hs₁ : m.φ s₁ ≠ .top := hr'.2.1
      have hs₂ : m.φ s₂ ≠ .top := hr'.2.2
      have hBa : HasType P Γ (B.instantiate a) (.sort s₂) := hB.instantiate ha
      have hAc := m.hasType hA
      have hBc := m.hasType hB
      rw [List.map_cons] at hBc
      have hac := m.hasType ha
      have hAne := ne_boxT_of_sorted hAc hs₁
      rw [← Expr.instantiate_subst]
      rw [SemC_ne (ne_boxT_of_sorted (m.hasType hBa) hs₂), Expr.mapSort_instantiate,
        Expr.mapSort_instantiate, interpK_instantiate]
      rw [SemC_ne (by simp [Expr.mapSort])] at hFs
      change interpK (candAlg P) (CT θ (Γ.map (Expr.mapSort m.φ)))
        (.pi ((A.mapSort m.φ).mapSort srtC) ((B.mapSort m.φ).mapSort srtC)) .star ξ Δ _ _ at hFs
      rw [SemC_ne hAne] at has
      have hca : cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((a.mapSort m.φ).mapSort srtC) =
          bindC (cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((A.mapSort m.φ).mapSort srtC)) := by
        rw [CT, cl_toC θ _ _ (wcv_of_hasType hac), cl_toC θ _ _ (wcv_of_hasType hAc),
          classifyFull hac (ne_box_of_sorted hAc hs₁) (fun e => top_untypable (e ▸ hAc)),
          evalCls_bindV]
      by_cases hk : ∃ k, cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((A.mapSort m.φ).mapSort srtC) =
          .kind k
      · obtain ⟨k, hcA⟩ := hk
        rw [MorphFund.interpK_pi_kind hcA] at hFs
        have hcak : cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((a.mapSort m.φ).mapSort srtC) =
            .constr k := by
          rw [hca, hcA]; rfl
        have hv : CandC P k (interpK (candAlg P) (CT θ (Γ.map (Expr.mapSort m.φ)))
            ((a.mapSort m.φ).mapSort srtC) k ξ) :=
          interpC_cand hsn _ (wc_toC θ hac) hξ (.inl hcak)
        have happ := hFs.2 [] (a.subst σ) (A.subst σ) (B.subst (Expr.liftSub σ)) _ hv
          (by rw [MorphFund.wk_nil, Expr.rename_id]; exact .refl) (by simpa using has)
        simp only [MorphFund.wk_nil, Expr.rename_id, List.nil_append] at happ
        rw [hcak]
        have hBwc : WC (ncons (.constr k) (CT θ (Γ.map (Expr.mapSort m.φ))))
            ((B.mapSort m.φ).mapSort srtC) := by
          have := wc_toC θ hBc; rwa [← CT, ctxCl_bind_kind hAc hs₁ hcA] at this
        have hBrel : RelC (cl (ncons (.constr k) (CT θ (Γ.map (Expr.mapSort m.φ))))
            ((B.mapSort m.φ).mapSort srtC)) .star := by
          have := relC_toC_of_sorted θ hBc hs₂; rwa [← CT, ctxCl_bind_kind hAc hs₁ hcA] at this
        have hAg : AgreeK (ncons (.constr k) (CT θ (Γ.map (Expr.mapSort m.φ))))
            (ncons (extK (candAlg P) k (interpK (candAlg P)
              (CT θ (Γ.map (Expr.mapSort m.φ))) ((a.mapSort m.φ).mapSort srtC) k ξ)) ξ)
            (ncons (fun k' => interpK (candAlg P) (CT θ (Γ.map (Expr.mapSort m.φ)))
              ((a.mapSort m.φ).mapSort srtC) k' ξ) ξ) := by
          intro n k' hk'
          cases n with
          | zero =>
              have := RelC.constr_eq hk'
              subst this
              simp
          | succ n => rfl
        rw [← interpK_agree (candAlg P) _ hBwc hAg hBrel]
        exact happ
      · have hAk : ∀ k, cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((A.mapSort m.φ).mapSort srtC) ≠
            .kind k := fun k h => hk ⟨k, h⟩
        rw [MorphFund.interpK_pi_obj hAk] at hFs
        have hcao : cl (CT θ (Γ.map (Expr.mapSort m.φ))) ((a.mapSort m.φ).mapSort srtC) =
            .obj := by
          rw [hca]; exact CoC.bindC_of_not_kind hAk
        have happ := hFs.2 [] (a.subst σ) (A.subst σ) (B.subst (Expr.liftSub σ))
          (by rw [MorphFund.wk_nil, Expr.rename_id]; exact .refl) (by simpa using has)
        simp only [MorphFund.wk_nil, Expr.rename_id, List.nil_append] at happ
        rw [hcao]
        have hBwc : WC (ncons .obj (CT θ (Γ.map (Expr.mapSort m.φ))))
            ((B.mapSort m.φ).mapSort srtC) := by
          have := wc_toC θ hBc; rwa [← CT, ctxCl_bind_obj hAc hs₁ hAk] at this
        have hBrel : RelC (cl (ncons .obj (CT θ (Γ.map (Expr.mapSort m.φ))))
            ((B.mapSort m.φ).mapSort srtC)) .star := by
          have := relC_toC_of_sorted θ hBc hs₂; rwa [← CT, ctxCl_bind_obj hAc hs₁ hAk] at this
        have hAg : AgreeK (ncons .obj (CT θ (Γ.map (Expr.mapSort m.φ))))
            (ncons (canonK (candAlg P)) ξ)
            (ncons (fun k' => interpK (candAlg P) (CT θ (Γ.map (Expr.mapSort m.φ)))
              ((a.mapSort m.φ).mapSort srtC) k' ξ) ξ) := by
          intro n k' hk'
          cases n with
          | zero => exact hk'.not_obj.elim
          | succ n => rfl
        rw [← interpK_agree (candAlg P) _ hBwc hAg hBrel]
        exact happ
  | @conversion Γ M A B s hM hB hc ihM _ =>
      intro Δ σ ξ hσ
      have h1 := ihM hσ
      unfold Sem at h1 ⊢
      have hMc := m.hasType hM
      have hBc := m.hasType hB
      have hcc := hc.mapSort m.φ
      have hAok := tyOK_of_typed hsn hMc hσ.good
      have h2 := h1.conv hAok (Converts.subst hc σ)
      by_cases hBb : (B.mapSort m.φ).mapSort srtC = .sort .box
      · unfold SemC; rw [ite_eq_left hBb]; exact h2.norm hAok
      have hs : m.φ s ≠ .top := by
        intro e
        rcases not_top_typed hBc with h' | h'
        · exact h' (by rw [← e]; rfl)
        · rw [h'] at hBb; exact hBb rfl
      have hAs : ∃ t, t ≠ .top ∧
          HasType cocTop (Γ.map (Expr.mapSort m.φ)) (A.mapSort m.φ) (.sort t) := by
        rcases hMc.regularity with ⟨t, ht⟩ | ⟨t, hA⟩
        · rw [ht] at hcc ⊢
          cases t with
          | box =>
              exact absurd (by rw [eq_box_of_conv hBc (converts_symm' hcc)]; rfl) hBb
          | top => exact (not_conv_top hBc (converts_symm' hcc)).elim
          | star => exact ⟨.box, by decide, star_box hMc.valid⟩
        · by_cases ht : t = .top
          · subst ht
            rcases not_top_typed hA with h' | h'
            · exact absurd rfl h'
            · rw [h'] at hcc
              exact absurd (by rw [eq_box_of_conv hBc (converts_symm' hcc)]; rfl) hBb
          · exact ⟨t, ht, hA⟩
      obtain ⟨t, ht, hA⟩ := hAs
      rw [SemC_ne (ne_boxT_of_sorted hA ht)] at h2
      have e := interpV_conv (candAlg P) θ hA ht hBc hs hcc ξ
      unfold interpV at e
      rw [SemC_ne hBb, ← e]
      exact h2

/-! ### The sort-typed fundamental lemma -/

/-- The identity substitution with the canonical valuation is reducible. -/
theorem SubstOK.ids (m : TopMorphism P) (θ : Nat → Sk) {Γ : List (Expr S)}
    (hv : ValidContextNW P Γ) : SubstOK m θ Γ Γ Expr.var (MorphFund.canonValC P) where
  good := MorphFund.goodVal_canon P _
  ctx := ⟨Γ, MorphFund.forall₂_reduces_refl Γ, hv⟩
  tys n A hn := tyOK_of_typed m.stronglyNormalizing
    (m.hasType (MorphFund.HasTypeNW.lookup'' hv hn).toHasType) (MorphFund.goodVal_canon P _)
  var n A hn := by
    unfold Sem
    simp only [Expr.subst_var]
    exact SemC.var (tyOK_of_typed m.stronglyNormalizing
      (m.hasType (MorphFund.HasTypeNW.lookup'' hv hn).toHasType) (MorphFund.goodVal_canon P _))
      ⟨Γ, _, _, MorphFund.forall₂_reduces_refl Γ, .refl, .refl,
        MorphFund.HasTypeNW.lookup'' hv hn⟩

/-- The substitution of a canonical `N : A` at depth `Δ` is reducible. -/
theorem substOK_substAt (m : TopMorphism P) (θ : Nat → Sk) {Γ : List (Expr S)} {N A : Expr S}
    (hN : HasTypeNW P Γ N A)
    {Δ Δ' : List (Expr S)} (hc : CtxSubstRed N Δ Δ') (hv : ValidContextNW P (Δ' ++ Γ))
    (hsrc : ValidContext P (Δ ++ A :: Γ)) :
    SubstOK m θ (Δ ++ A :: Γ) (Δ' ++ Γ) (Expr.substAt N Δ.length) (MorphFund.canonValC P) := by
  induction hc with
  | nil =>
      have hid := SubstOK.ids m θ hN.valid
      have hNsem : SemC P θ (Γ.map (Expr.mapSort m.φ)) (MorphFund.canonValC P) Γ
          (A.mapSort m.φ) N (A.subst Expr.var) := by
        have := fundamental m θ hN.toHasType hid
        unfold Sem at this
        simp only [Expr.subst_var] at this ⊢
        exact this
      have hg0 : GoodVal P (CT θ ((A :: Γ).map (Expr.mapSort m.φ)))
          (ncons (canonK (candAlg P)) (MorphFund.canonValC P)) := by
        rw [List.map_cons]; exact GoodVal.ncons_canon (MorphFund.goodVal_canon P _)
      have := hid.cons hg0
        (tyOK_of_typed m.stronglyNormalizing (m.hasType hN.toHasType)
          (MorphFund.goodVal_canon P _))
        hNsem
      rw [MorphFund.ncons_canonValC, MorphFund.scons_var] at this
      exact this
  | @cons Δ Δ' D D' _ hr ih =>
      cases hv with
      | cons hv' hD' =>
          cases hsrc with
          | cons hsrc' hD =>
              have := (ih hv' hsrc').lift
                (by rw [List.map_cons]; exact GoodVal.ncons_canon (MorphFund.goodVal_canon P _))
                (tyOK_of_sorted m.stronglyNormalizing (m.hasType hD)
                  (MorphFund.goodVal_canon P _))
                ⟨_, D', _, MorphFund.forall₂_reduces_refl _, .refl, .refl, hD'⟩ hr
              rw [MorphFund.ncons_canonValC, ← Expr.substAt_succ] at this
              exact this

end TopFund

/-- **The route (ii) sort-typed fundamental lemma for every specification with a morphism into
`cocTop`.** -/
theorem sortFundamental_of_topMorphism {S : Type} {P : Specification S} (m : TopMorphism P) :
    SNGeneric.SortFundamental P := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  have := TopFund.fundamental m (fun _ => .star) hM.toHasType
    (TopFund.substOK_substAt m (fun _ => .star) hN hc hv hM.toHasType.valid)
  unfold TopFund.Sem at this
  exact TopFund.SemC_sort.1 this

/-- **Expansion postponement for every specification with a morphism into `cocTop`.** -/
theorem expansionPostponement_of_topMorphism {S : Type} {P : Specification S}
    (m : TopMorphism P) : ExpansionPostponement P :=
  m.expansionPostponement_of_sortFundamental (sortFundamental_of_topMorphism m)

/-- **Expansion postponement for `cocTop`** (`∗ : □ : Δ`, kind variables `K : □`). -/
theorem cocTop_expansionPostponement : ExpansionPostponement cocTop :=
  expansionPostponement_of_topMorphism cocTop_topMorphism

end PureTypeSystem

namespace PureTypeSystem

/-! ### An instance in the top class, outside the coc-morphism and stratified classes, not
functional -/

/-- Sorts of `cocTop` with the top sort doubled. -/
inductive SrtTT where
  | star : SrtTT
  | box : SrtTT
  | top : SrtTT
  | top' : SrtTT
  deriving DecidableEq, Repr

/-- The collapse `Δ' ↦ Δ`. -/
def collapseTT : SrtTT → Srt3
  | .star => .star
  | .box => .box
  | .top => .top
  | .top' => .top

/-- `cocTop` with two top sorts: axioms `∗ : □`, `□ : Δ`, `□ : Δ'`; rules `(s₁, s₂, s₂)` with
`s₁, s₂ ∈ {∗, □}`. -/
def cocTopTwo : Specification SrtTT where
  axioms s t := (s = .star ∧ t = .box) ∨ (s = .box ∧ (t = .top ∨ t = .top'))
  rule s₁ s₂ s₃ := s₃ = s₂ ∧ (s₁ = .star ∨ s₁ = .box) ∧ (s₂ = .star ∨ s₂ = .box)

/-- `cocTopTwo` has a morphism into `cocTop`. -/
def cocTopTwo_topMorphism : TopMorphism cocTopTwo where
  φ := collapseTT
  axiom_map s t h := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩
    · exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
    · exact .inr ⟨rfl, rfl⟩
  rule_map a b c h := by
    obtain ⟨rfl, ha, hb⟩ := h
    refine ⟨rfl, ?_, ?_⟩ <;>
      first
      | (rcases ha with rfl | rfl <;> decide)
      | (rcases hb with rfl | rfl <;> decide)

/-- `cocTopTwo` is not functional (`□ : Δ` and `□ : Δ'`). -/
theorem cocTopTwo_not_functional : ¬ Functional cocTopTwo := by
  intro h
  have := h.1 .box .top .top' (.inr ⟨rfl, .inl rfl⟩) (.inr ⟨rfl, .inr rfl⟩)
  cases this

/-- `cocTopTwo` has no morphism into coc: `∗ : □` and `□ : Δ` would both be sent to `∗ : □`. -/
theorem cocTopTwo_not_cocMorphism (m : CoCMorphism cocTopTwo) : False := by
  have h1 := m.axiom_map .star .box (.inl ⟨rfl, rfl⟩)
  have h2 := m.axiom_map .box .top (.inr ⟨rfl, .inl rfl⟩)
  have e1 : m.φ .box = .box := h1.2
  have e2 : m.φ .box = .star := h2.1
  rw [e1] at e2
  cases e2

/-- `cocTopTwo` is not stratified (it has the dependent rule `(∗, □, □)`). -/
theorem cocTopTwo_not_stratified (L : Stratification cocTopTwo) : False :=
  not_stratified_of_dependent_rule (P := cocTopTwo) (s := .star) (t := .box) (r := .box)
    (.inl ⟨rfl, rfl⟩) ⟨rfl, .inl rfl, .inr rfl⟩ L

/-- **Expansion postponement for `cocTopTwo`**, a non-functional specification in the top class
with neither a morphism into coc nor a stratification. -/
theorem cocTopTwo_expansionPostponement : ExpansionPostponement cocTopTwo :=
  expansionPostponement_of_topMorphism cocTopTwo_topMorphism

end PureTypeSystem
