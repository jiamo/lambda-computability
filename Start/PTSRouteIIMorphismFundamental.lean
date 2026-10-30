import Start.PTSRouteIIMorphismCand
import Start.PTSExpansionCoCMorphism

/-!
# Series V, round 1, run 2, part A: the route (ii) fundamental lemma for every specification
with a morphism into coc (row M29-EP-COC-MORPHISM-FUNDAMENTAL)

The round-11 fundamental lemma for coc (`Start/PTSRouteIICoCFundamental.lean`), transported
along a morphism `m : CoCMorphism P`.  Candidates are sets of `P`-judgements
(`Start/PTSRouteIIMorphismCand.lean`); the type `T` of a `P`-judgement `Γ ⊢ M : T` is interpreted
through its image `T.mapSort m.φ` in the image context `Γ.map (Expr.mapSort m.φ)`, which is a coc
judgement by `CoCMorphism.hasType`; all classification facts are read off the image.

* `MorphFund.SemC` — tests `T.mapSort m.φ = □` (normalization) and otherwise membership in the
  candidate interpreting the image;
* `MorphFund.fundamental` — the fundamental lemma for `HasType P`;
* **`sortFundamental_of_cocMorphism (m : CoCMorphism P) : SNGeneric.SortFundamental P`**;
* **`expansionPostponement_of_cocMorphism (m : CoCMorphism P) : ExpansionPostponement P`**;
* **`cocBox2_expansionPostponement : ExpansionPostponement cocBox2`**;
* `cocDouble` (sorts `∗, ∗', □, □'`): a second instance outside the cube whose axioms are neither
  functional nor injective and whose rules are not functional;
  **`cocDouble_expansionPostponement : ExpansionPostponement cocDouble`**.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace MorphFund

open LambdaPi (Srt)
open SNGeneric (CandP IsCandC piOC piKC CandC candAlg candC_canon isCandC_normNW GoodVal
  interpC_cand NormNW NeNW wk rename_wk_wk' converts_symm' converts_trans')
open ErasureCoC (V KAlg canonK ValK extK extK_self interpK interpK_conv interpK_rename
  interpK_instantiate interpK_agree AgreeK)
open CoC (Sk Cls cl ncons bindC RelC WC domSk ctxCl)

/-- The specification of the calculus of constructions. -/
abbrev PC : Specification Srt := cubeSpec coc

variable {S : Type} {P : Specification S}

/-! ### Canonical judgements and substitution algebra over any sort type -/

theorem HasTypeNW.ax_of_valid {Δ : List (Expr S)} (hv : ValidContextNW P Δ) {s t : S}
    (hst : P.axioms s t) : HasTypeNW P Δ (.sort s) (.sort t) := by
  induction hv with
  | nil => exact .ax hst
  | cons _ hA ih => exact .weaken ih hA

theorem HasTypeNW.lookup'' {Δ : List (Expr S)} (hv : ValidContextNW P Δ) :
    ∀ {n : ℕ} {A : Expr S}, Lookup Δ n A → HasTypeNW P Δ (.var n) A := by
  induction hv with
  | nil => intro n A hn; cases hn
  | cons _ hB ih =>
      intro n A hn
      cases hn with
      | zero => exact .var hB
      | succ _ hn => exact .weaken (ih hn) hB

theorem rename_eq_pi'' {M A B : Expr S} {r : ℕ → ℕ} (h : M.rename r = .pi A B) :
    ∃ A₀ B₀, M = .pi A₀ B₀ ∧ A = A₀.rename r ∧ B = B₀.rename (Expr.liftRen r) := by
  cases M with
  | pi A₀ B₀ =>
      simp only [Expr.rename, Expr.pi.injEq] at h
      exact ⟨A₀, B₀, rfl, h.1.symm, h.2.symm⟩
  | _ => simp [Expr.rename] at h

theorem HasTypeNW.pi_dom'' {Γ : List (Expr S)} {M T : Expr S} (h : HasTypeNW P Γ M T) :
    ∀ {A B : Expr S}, M = .pi A B → ∃ s, HasTypeNW P Γ A (.sort s) := by
  induction h with
  | ax _ => intro A B h; cases h
  | var _ _ => intro A B h; cases h
  | weaken hM hA ihM _ =>
      intro A B h
      obtain ⟨A₀, B₀, rfl, rfl, rfl⟩ := rename_eq_pi'' h
      obtain ⟨s, hs⟩ := ihM rfl
      exact ⟨s, .weaken hs hA⟩
  | product hA _ _ _ _ => intro A B h; cases h; exact ⟨_, hA⟩
  | abstraction _ _ _ _ => intro A B h; cases h
  | application _ _ _ _ _ _ _ => intro A B h; cases h

theorem NormNW.pi_dom'' {Δ : List (Expr S)} {A B : Expr S} {s : S}
    (h : NormNW P Δ (.pi A B) (.sort s)) : ∃ s₁, NormNW P Δ A (.sort s₁) := by
  obtain ⟨Δ', M', T', hc, hM, hT, hNW⟩ := h
  obtain ⟨A', B', rfl, hA, -⟩ := Reduces.pi_inv hM
  obtain ⟨s₁, hs₁⟩ := HasTypeNW.pi_dom'' hNW rfl
  exact ⟨s₁, Δ', A', _, hc, hA, .refl, hs₁⟩

theorem NormNW.var0'' {Δ : List (Expr S)} {X A : Expr S} {s : S}
    (h : NormNW P Δ X (.sort s)) (hr : Reduces A X) :
    NormNW P (X :: Δ) (.var 0) (A.rename Nat.succ) := by
  obtain ⟨Δ', X', T', hc, hX, hT, hNW⟩ := h
  rw [Reduces.sort_eq hT] at hNW
  exact ⟨X' :: Δ', .var 0, X'.rename Nat.succ, .cons hX hc, .refl,
    Reduces.rename (hr.trans hX) _, .var hNW⟩

theorem NormNW.ctx'' {Δ : List (Expr S)} {M T : Expr S} (h : NormNW P Δ M T) :
    ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW P Δ' := by
  obtain ⟨Δ', M', T', hc, -, -, hNW⟩ := h
  exact ⟨Δ', hc, hNW.valid⟩

/-- Extending a substitution (any sort type). -/
def scons (N : Expr S) (σ : ℕ → Expr S) : ℕ → Expr S
  | 0 => N
  | n + 1 => σ n

theorem liftSub_eq_scons (σ : ℕ → Expr S) :
    Expr.liftSub σ = scons (.var 0) (fun n => (σ n).rename Nat.succ) := by
  funext n; cases n <;> rfl

theorem wk_single (X : Expr S) : wk [X] = Nat.succ := by
  funext n; simp [wk]

theorem wk_nil : wk ([] : List (Expr S)) = id := by funext n; simp [wk]

theorem subst_scons_wk (b N : Expr S) (σ : ℕ → Expr S) (Γ₀ : List (Expr S)) :
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

theorem scons_var (N : Expr S) : scons N Expr.var = Expr.single N := by
  funext n; cases n <;> rfl

theorem rename_succ_eq_box {B : Expr Srt} : B.rename Nat.succ = .sort .box ↔ B = .sort .box := by
  cases B <;> simp [Expr.rename]

/-! ### Types whose interpretation is a candidate (coc side, image types) -/

variable (P) in
/-- A coc type is admissible when it is `□` or its interpretation is a `P`-candidate. -/
def TyOK (Γ : List (Expr Srt)) (ξ : ValK (CandP S)) (T : Expr Srt) : Prop :=
  T = .sort .box ∨ IsCandC P (interpK (candAlg P) (ctxCl Γ) T .star ξ)

theorem tyOK_of_sorted (hsn : SystemStronglyNormalizing P) {Γ : List (Expr Srt)}
    {ξ : ValK (CandP S)} {T : Expr Srt} {s : Srt}
    (hT : HasType PC Γ T (.sort s)) (hξ : GoodVal P (ctxCl Γ) ξ) : TyOK P Γ ξ T :=
  .inr (interpC_cand hsn T (CoC.wc_of_hasType hT) hξ (CoC.relC_of_sorted hT))

theorem tyOK_of_typed (hsn : SystemStronglyNormalizing P) {Γ : List (Expr Srt)}
    {ξ : ValK (CandP S)} {M T : Expr Srt}
    (h : HasType PC Γ M T) (hξ : GoodVal P (ctxCl Γ) ξ) : TyOK P Γ ξ T := by
  rcases CoC.type_sorted h with rfl | ⟨s, hT⟩
  · exact .inl rfl
  · exact tyOK_of_sorted hsn hT hξ

theorem interpK_ctx_succ (A : Expr Srt) (Γ : List (Expr Srt)) (B : Expr Srt)
    (ξ : ValK (CandP S)) :
    interpK (candAlg P) (ctxCl (A :: Γ)) (B.rename Nat.succ) .star ξ =
      interpK (candAlg P) (ctxCl Γ) B .star (fun i => ξ (i + 1)) := by
  rw [interpK_rename]
  rfl

theorem tyOK_rename_succ (A : Expr Srt) (Γ : List (Expr Srt)) (ξ : ValK (CandP S))
    (B : Expr Srt) :
    TyOK P (A :: Γ) ξ (B.rename Nat.succ) ↔ TyOK P Γ (fun i => ξ (i + 1)) B := by
  unfold TyOK
  rw [rename_succ_eq_box, interpK_ctx_succ]

/-! ### The semantics of a judgement -/

variable (P) in
/-- **The semantics of the (image) type `T`** at a target `P`-judgement `Δ ⊢ X : Y`. -/
def SemC (Γ : List (Expr Srt)) (ξ : ValK (CandP S)) (Δ : List (Expr S)) (T : Expr Srt)
    (X Y : Expr S) : Prop :=
  if T = .sort .box then NormNW P Δ X Y else interpK (candAlg P) (ctxCl Γ) T .star ξ Δ X Y

section SemC

variable {Γ : List (Expr Srt)} {ξ : ValK (CandP S)} {Δ : List (Expr S)} {T : Expr Srt}
  {X Y : Expr S}

theorem SemC_ne (hT : T ≠ .sort .box) :
    SemC P Γ ξ Δ T X Y ↔ interpK (candAlg P) (ctxCl Γ) T .star ξ Δ X Y := by
  unfold SemC; rw [ite_eq_right hT]

theorem SemC_sort {s : Srt} : SemC P Γ ξ Δ (.sort s) X Y ↔ NormNW P Δ X Y := by
  cases s with
  | box => unfold SemC; rw [ite_eq_left rfl]
  | star => unfold SemC; rw [ite_eq_right (by simp)]; rfl

theorem SemC.norm (hT : TyOK P Γ ξ T) (h : SemC P Γ ξ Δ T X Y) : NormNW P Δ X Y := by
  unfold SemC at h
  split_ifs at h with hb
  · exact h
  · exact (hT.resolve_left hb).norm h

theorem SemC.conv (hT : TyOK P Γ ξ T) (h : SemC P Γ ξ Δ T X Y) {Y' : Expr S}
    (hc : Converts Y Y') : SemC P Γ ξ Δ T X Y' := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact h.convType hc
  · exact (hT.resolve_left hb).conv h hc

theorem SemC.expand (hT : TyOK P Γ ξ T) {X' : Expr S} (hr : Reduces X X')
    (h : SemC P Γ ξ Δ T X' Y) : SemC P Γ ξ Δ T X Y := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact SNGeneric.NormNW.expand hr h
  · exact (hT.resolve_left hb).expand hr h

theorem SemC.weaken (hT : TyOK P Γ ξ T) (h : SemC P Γ ξ Δ T X Y) (Γ₀ : List (Expr S))
    {Δ' : List (Expr S)} (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ')
    (hv : ValidContextNW P Δ') :
    SemC P Γ ξ (Γ₀ ++ Δ) T (X.rename (wk Γ₀)) (Y.rename (wk Γ₀)) := by
  unfold SemC at h ⊢
  split_ifs at h ⊢ with hb
  · exact h.weaken Γ₀ hc hv
  · exact (hT.resolve_left hb).weaken Γ₀ h hc hv

theorem SemC.var (hT : TyOK P Γ ξ T) {x : ℕ} (h : NormNW P Δ (.var x) Y) :
    SemC P Γ ξ Δ T (.var x) Y := by
  unfold SemC
  split_ifs with hb
  · exact h
  · exact (hT.resolve_left hb).neutral (SNGeneric.NeNW.of_var h)

end SemC

theorem SemC_rename_succ (A : Expr Srt) (Γ : List (Expr Srt)) (ξ : ValK (CandP S))
    (Δ : List (Expr S)) (B : Expr Srt) (X Y : Expr S) :
    SemC P (A :: Γ) ξ Δ (B.rename Nat.succ) X Y ↔ SemC P Γ (fun i => ξ (i + 1)) Δ B X Y := by
  unfold SemC
  rw [interpK_ctx_succ]
  simp only [rename_succ_eq_box]

/-- The semantics of a `P`-judgement `Γ ⊢ M : T` under the substitution `σ`, read through the
morphism. -/
def Sem (m : CoCMorphism P) (Γ : List (Expr S)) (ξ : ValK (CandP S)) (Δ : List (Expr S))
    (M T : Expr S) (σ : ℕ → Expr S) : Prop :=
  SemC P (Γ.map (Expr.mapSort m.φ)) ξ Δ (T.mapSort m.φ) (M.subst σ) (T.subst σ)

/-- **Reducible substitutions** for `P`, classified through the morphism. -/
structure SubstOK (m : CoCMorphism P) (Γ Δ : List (Expr S)) (σ : ℕ → Expr S)
    (ξ : ValK (CandP S)) : Prop where
  good : GoodVal P (ctxCl (Γ.map (Expr.mapSort m.φ))) ξ
  ctx : ∃ Δ', List.Forall₂ Reduces Δ Δ' ∧ ValidContextNW P Δ'
  tys : ∀ n A, Lookup Γ n A → TyOK P (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ)
  var : ∀ n A, Lookup Γ n A → Sem m Γ ξ Δ (.var n) A σ

variable {m : CoCMorphism P}

theorem GoodVal.tail {A : Expr Srt} {Γ : List (Expr Srt)} {ξ : ValK (CandP S)}
    (h : GoodVal P (ctxCl (A :: Γ)) ξ) : GoodVal P (ctxCl Γ) (fun i => ξ (i + 1)) :=
  fun n k hk => h (n + 1) k hk

theorem GoodVal.ncons_canon {Δ : Nat → Cls} {ξ : ValK (CandP S)} (h : GoodVal P Δ ξ)
    (c : Cls) : GoodVal P (ncons c Δ) (ncons (canonK (candAlg P)) ξ) := by
  intro n k hk
  cases n with
  | zero => exact candC_canon k
  | succ n => exact h n k hk

theorem SubstOK.tail {A : Expr S} {Γ Δ : List (Expr S)} {σ : ℕ → Expr S}
    {ξ : ValK (CandP S)} (h : SubstOK m (A :: Γ) Δ σ ξ) :
    SubstOK m Γ Δ (fun n => σ (n + 1)) (fun i => ξ (i + 1)) where
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
    (h : SubstOK m Γ Δ σ ξ) (Γ₀ : List (Expr S)) {Δ' : List (Expr S)}
    (hc : List.Forall₂ Reduces (Γ₀ ++ Δ) Δ') (hv : ValidContextNW P Δ') :
    SubstOK m Γ (Γ₀ ++ Δ) (fun n => (σ n).rename (wk Γ₀)) ξ where
  good := h.good
  ctx := ⟨Δ', hc, hv⟩
  tys := h.tys
  var n B hB := by
    have := (h.var n B hB).weaken (h.tys n B hB) Γ₀ hc hv
    unfold Sem at this ⊢
    simp only [Expr.rename_subst] at this
    exact this

theorem SubstOK.cons {A N : Expr S} {Γ Δ : List (Expr S)} {σ : ℕ → Expr S}
    {ξ : ValK (CandP S)} {e : (k : Sk) → V (CandP S) k} (h : SubstOK m Γ Δ σ ξ)
    (hg : GoodVal P (ctxCl ((A :: Γ).map (Expr.mapSort m.φ))) (ncons e ξ))
    (hA : TyOK P (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ))
    (hN : SemC P (Γ.map (Expr.mapSort m.φ)) ξ Δ (A.mapSort m.φ) N (A.subst σ)) :
    SubstOK m (A :: Γ) Δ (scons N σ) (ncons e ξ) where
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
    {ξ : ValK (CandP S)} {e : (k : Sk) → V (CandP S) k} {s : S} (h : SubstOK m Γ Δ σ ξ)
    (hg : GoodVal P (ctxCl ((A :: Γ).map (Expr.mapSort m.φ))) (ncons e ξ))
    (hA : TyOK P (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ))
    (hX : NormNW P Δ X (.sort s)) (hr : Reduces (A.subst σ) X) :
    SubstOK m (A :: Γ) (X :: Δ) (Expr.liftSub σ) (ncons e ξ) := by
  have h0 := NormNW.var0'' hX hr
  obtain ⟨Δ', hc, hv⟩ := NormNW.ctx'' h0
  have hw := h.weaken [X] hc hv
  rw [wk_single] at hw
  rw [liftSub_eq_scons]
  refine hw.cons hg hA (SemC.var hA ?_)
  rw [← Expr.rename_subst]
  exact h0

/-- The Kripke instantiation step of the abstraction case. -/
theorem body_inst {Γ Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)}
    {A b B : Expr S} {e : (k : Sk) → V (CandP S) k} (hσ : SubstOK m Γ Δ σ ξ)
    (hg : GoodVal P (ctxCl ((A :: Γ).map (Expr.mapSort m.φ))) (ncons e ξ))
    (hA : TyOK P (Γ.map (Expr.mapSort m.φ)) ξ (A.mapSort m.φ))
    (ihb : ∀ {Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)},
      SubstOK m (A :: Γ) Δ σ ξ → Sem m (A :: Γ) ξ Δ b B σ)
    (Γ₀ : List (Expr S)) (N : Expr S)
    (hN : SemC P (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) N
      ((A.subst σ).rename (wk Γ₀))) :
    SemC P ((A :: Γ).map (Expr.mapSort m.φ)) (ncons e ξ) (Γ₀ ++ Δ) (B.mapSort m.φ)
      (((b.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N)
      (((B.subst (Expr.liftSub σ)).rename (Expr.liftRen (wk Γ₀))).instantiate N) := by
  obtain ⟨Δ', hc, hv⟩ := NormNW.ctx'' (hN.norm hA)
  have hN' : SemC P (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) N
      (A.subst (fun n => (σ n).rename (wk Γ₀))) := by
    rw [← Expr.rename_subst]; exact hN
  have := ihb ((hσ.weaken Γ₀ hc hv).cons hg hA hN')
  unfold Sem at this
  rw [subst_scons_wk, subst_scons_wk] at this
  exact this

theorem goodVal_bind_kind {Γ : List (Expr Srt)} {A : Expr Srt} {ξ : ValK (CandP S)} {a : Sk}
    (hξ : GoodVal P (ctxCl Γ) ξ) (ha : cl (ctxCl Γ) A = .kind a) {v : V (CandP S) a}
    (hv : CandC P a v) : GoodVal P (ctxCl (A :: Γ)) (ncons (extK (candAlg P) a v) ξ) := by
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

theorem interpK_pi_kind {Δ : Nat → Cls} {A B : Expr Srt} {a : Sk} {ξ : ValK (CandP S)}
    (ha : cl Δ A = .kind a) :
    interpK (candAlg P) Δ (.pi A B) .star ξ = piKC P a (interpK (candAlg P) Δ A .star ξ)
      (fun v => interpK (candAlg P) (ncons (.constr a) Δ) B .star
        (ncons (extK (candAlg P) a v) ξ)) := by
  simp only [interpK, ha]; rfl

theorem interpK_pi_obj {Δ : Nat → Cls} {A B : Expr Srt} {ξ : ValK (CandP S)}
    (hA : ∀ a, cl Δ A ≠ .kind a) :
    interpK (candAlg P) Δ (.pi A B) .star ξ = piOC P (interpK (candAlg P) Δ A .star ξ)
      (interpK (candAlg P) (ncons .obj Δ) B .star (ncons (canonK (candAlg P)) ξ)) := by
  rcases h : cl Δ A with a | a | _
  · exact absurd h (hA a)
  · simp only [interpK, h]; rfl
  · simp only [interpK, h]; rfl

/-! ### The fundamental lemma -/

theorem mapSort_pi_ne_box (A B : Expr S) (f : S → Srt) :
    (Expr.pi A B).mapSort f ≠ .sort .box := by
  simp [Expr.mapSort]

/-- **The fundamental lemma of route (ii) through a morphism into coc**: under a reducible
substitution into a normalizable target context, every subject of a `P`-judgement is in the
semantics of its type, interpreted through the image of the type. -/
theorem fundamental (m : CoCMorphism P) {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) :
    ∀ {Δ : List (Expr S)} {σ : ℕ → Expr S} {ξ : ValK (CandP S)},
      SubstOK m Γ Δ σ ξ → Sem m Γ ξ Δ M T σ := by
  have hsn := m.stronglyNormalizing
  induction h with
  | ax hst =>
      intro Δ σ ξ hσ
      obtain ⟨Δ', hc, hv⟩ := hσ.ctx
      unfold Sem
      change SemC P _ ξ Δ (.sort _) (.sort _) (.sort _)
      rw [SemC_sort]
      exact ⟨Δ', _, _, hc, .refl, .refl, HasTypeNW.ax_of_valid hv hst⟩
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
      have hσ' := hσ.lift (GoodVal.ncons_canon hσ.good _)
        (tyOK_of_sorted hsn (m.hasType hA) hσ.good) hAn .refl
      have hBn : NormNW P (A.subst σ :: Δ) (B.subst (Expr.liftSub σ)) (.sort s₂) :=
        SemC_sort.1 (ihB hσ')
      unfold Sem
      change SemC P _ ξ Δ (.sort _) _ _
      rw [SemC_sort]
      exact SNGeneric.NormNW.product hAn hBn hr
  | @abstraction Γ A b B s hb hP ihb ihP =>
      intro Δ σ ξ hσ
      have hξ := hσ.good
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, -⟩ := hP.generation_pi
      have hPn : NormNW P Δ ((Expr.pi A B).subst σ) (.sort s) := SemC_sort.1 (ihP hσ)
      obtain ⟨s₁', hAn⟩ := NormNW.pi_dom'' hPn
      have hAc := m.hasType hA
      have hBc := m.hasType hB
      rw [List.map_cons] at hBc
      have hAok := tyOK_of_sorted hsn hAc hξ
      have hbn : NormNW P (A.subst σ :: Δ) (b.subst (Expr.liftSub σ))
          (B.subst (Expr.liftSub σ)) := by
        have hσ' := hσ.lift (GoodVal.ncons_canon hξ _) hAok hAn .refl
        exact SemC.norm (tyOK_of_sorted hsn hBc hσ'.good) (ihb hσ')
      have hlam : NormNW P Δ ((Expr.lam A b).subst σ) ((Expr.pi A B).subst σ) :=
        SNGeneric.NormNW.abstraction hbn hPn
      have hBne : B.mapSort m.φ ≠ .sort .box := CoC.ne_box_of_hasType hBc
      have hAne : A.mapSort m.φ ≠ .sort .box := CoC.ne_box_of_hasType hAc
      have hXA : IsCandC P (interpK (candAlg P) (ctxCl (Γ.map (Expr.mapSort m.φ)))
          (A.mapSort m.φ) .star ξ) := hAok.resolve_left hAne
      unfold Sem
      rw [SemC_ne (mapSort_pi_ne_box A B m.φ)]
      show interpK (candAlg P) (ctxCl (Γ.map (Expr.mapSort m.φ)))
        (.pi (A.mapSort m.φ) (B.mapSort m.φ)) .star ξ Δ _ _
      by_cases hk : ∃ a, cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (A.mapSort m.φ) = .kind a
      · obtain ⟨a, hcA⟩ := hk
        rw [interpK_pi_kind hcA]
        refine ⟨hlam, fun Γ₀ U K B' v hv hT hU => ?_⟩
        simp only [Expr.subst, Expr.rename] at hT
        obtain ⟨K₁, B₁, heq, hK₁, hB₁⟩ := Reduces.pi_inv hT
        cases heq
        have hg := goodVal_bind_kind hξ hcA hv
        have hU' : SemC P (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) U
            ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemC_ne hAne]
          exact hXA.conv hU (converts_symm' (Reduces.converts hK₁))
        have := body_inst hσ (by rw [List.map_cons]; exact hg) hAok ihb Γ₀ U hU'
        rw [List.map_cons, SemC_ne hBne, ctxCl_bind_kind hcA] at this
        have hXB : IsCandC P (interpK (candAlg P) (ncons (.constr a)
            (ctxCl (Γ.map (Expr.mapSort m.φ)))) (B.mapSort m.φ) .star
            (ncons (extK (candAlg P) a v) ξ)) := by
          have := (tyOK_of_sorted hsn hBc hg).resolve_left hBne
          rwa [ctxCl_bind_kind hcA] at this
        refine hXB.expand (.single (.head _ _ _)) ?_
        exact hXB.conv this (Reduces.converts (Reduces.instantiate hB₁ .refl))
      · have hAk : ∀ a, cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (A.mapSort m.φ) ≠ .kind a :=
          fun a h => hk ⟨a, h⟩
        rw [interpK_pi_obj hAk]
        refine ⟨hlam, fun Γ₀ N A' B' hT hN => ?_⟩
        simp only [Expr.subst, Expr.rename] at hT
        obtain ⟨A₁, B₁, heq, hA₁, hB₁⟩ := Reduces.pi_inv hT
        cases heq
        have hg : GoodVal P (ctxCl (A.mapSort m.φ :: Γ.map (Expr.mapSort m.φ)))
            (ncons (canonK (candAlg P)) ξ) := GoodVal.ncons_canon hξ _
        have hN' : SemC P (Γ.map (Expr.mapSort m.φ)) ξ (Γ₀ ++ Δ) (A.mapSort m.φ) N
            ((A.subst σ).rename (wk Γ₀)) := by
          rw [SemC_ne hAne]
          exact hXA.conv hN (converts_symm' (Reduces.converts hA₁))
        have := body_inst hσ (by rw [List.map_cons]; exact hg) hAok ihb Γ₀ N hN'
        rw [List.map_cons, SemC_ne hBne, ctxCl_bind_obj hAk] at this
        have hXB : IsCandC P (interpK (candAlg P) (ncons .obj
            (ctxCl (Γ.map (Expr.mapSort m.φ)))) (B.mapSort m.φ) .star
            (ncons (canonK (candAlg P)) ξ)) := by
          have := (tyOK_of_sorted hsn hBc hg).resolve_left hBne
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
      have hBa : HasType P Γ (B.instantiate a) (.sort s₂) := hB.instantiate ha
      have hAc := m.hasType hA
      have hBc := m.hasType hB
      rw [List.map_cons] at hBc
      have hac := m.hasType ha
      have hAne : A.mapSort m.φ ≠ .sort .box := CoC.ne_box_of_hasType hAc
      rw [← Expr.instantiate_subst]
      rw [SemC_ne (CoC.ne_box_of_hasType (m.hasType hBa)), Expr.mapSort_instantiate,
        interpK_instantiate]
      rw [SemC_ne (mapSort_pi_ne_box A B m.φ)] at hFs
      change interpK (candAlg P) (ctxCl (Γ.map (Expr.mapSort m.φ)))
        (.pi (A.mapSort m.φ) (B.mapSort m.φ)) .star ξ Δ _ _ at hFs
      rw [SemC_ne hAne] at has
      have hca : cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (a.mapSort m.φ) =
          bindC (cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (A.mapSort m.φ)) :=
        CoC.classify hac hAne
      by_cases hk : ∃ k, cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (A.mapSort m.φ) = .kind k
      · obtain ⟨k, hcA⟩ := hk
        rw [interpK_pi_kind hcA] at hFs
        have hcak : cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (a.mapSort m.φ) = .constr k := by
          rw [hca, hcA]; rfl
        have hv : CandC P k (interpK (candAlg P) (ctxCl (Γ.map (Expr.mapSort m.φ)))
            (a.mapSort m.φ) k ξ) :=
          interpC_cand hsn _ (CoC.wc_of_hasType hac) hξ (.inl hcak)
        have happ := hFs.2 [] (a.subst σ) (A.subst σ) (B.subst (Expr.liftSub σ)) _ hv
          (by rw [wk_nil, Expr.rename_id]; exact .refl) (by simpa using has)
        simp only [wk_nil, Expr.rename_id, List.nil_append] at happ
        rw [hcak]
        have hBwc : WC (ncons (.constr k) (ctxCl (Γ.map (Expr.mapSort m.φ))))
            (B.mapSort m.φ) := by
          have := CoC.wc_of_hasType hBc; rwa [ctxCl_bind_kind hcA] at this
        have hBrel : RelC (cl (ncons (.constr k) (ctxCl (Γ.map (Expr.mapSort m.φ))))
            (B.mapSort m.φ)) .star := by
          have := CoC.relC_of_sorted hBc; rwa [ctxCl_bind_kind hcA] at this
        have hAg : AgreeK (ncons (.constr k) (ctxCl (Γ.map (Expr.mapSort m.φ))))
            (ncons (extK (candAlg P) k (interpK (candAlg P)
              (ctxCl (Γ.map (Expr.mapSort m.φ))) (a.mapSort m.φ) k ξ)) ξ)
            (ncons (fun k' => interpK (candAlg P) (ctxCl (Γ.map (Expr.mapSort m.φ)))
              (a.mapSort m.φ) k' ξ) ξ) := by
          intro n k' hk'
          cases n with
          | zero =>
              have := RelC.constr_eq hk'
              subst this
              simp
          | succ n => rfl
        rw [← interpK_agree (candAlg P) _ hBwc hAg hBrel]
        exact happ
      · have hAk : ∀ k, cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (A.mapSort m.φ) ≠ .kind k :=
          fun k h => hk ⟨k, h⟩
        rw [interpK_pi_obj hAk] at hFs
        have hcao : cl (ctxCl (Γ.map (Expr.mapSort m.φ))) (a.mapSort m.φ) = .obj := by
          rw [hca]; exact CoC.bindC_of_not_kind hAk
        have happ := hFs.2 [] (a.subst σ) (A.subst σ) (B.subst (Expr.liftSub σ))
          (by rw [wk_nil, Expr.rename_id]; exact .refl) (by simpa using has)
        simp only [wk_nil, Expr.rename_id, List.nil_append] at happ
        rw [hcao]
        have hBwc : WC (ncons .obj (ctxCl (Γ.map (Expr.mapSort m.φ)))) (B.mapSort m.φ) := by
          have := CoC.wc_of_hasType hBc; rwa [ctxCl_bind_obj hAk] at this
        have hBrel : RelC (cl (ncons .obj (ctxCl (Γ.map (Expr.mapSort m.φ))))
            (B.mapSort m.φ)) .star := by
          have := CoC.relC_of_sorted hBc; rwa [ctxCl_bind_obj hAk] at this
        have hAg : AgreeK (ncons .obj (ctxCl (Γ.map (Expr.mapSort m.φ))))
            (ncons (canonK (candAlg P)) ξ)
            (ncons (fun k' => interpK (candAlg P) (ctxCl (Γ.map (Expr.mapSort m.φ)))
              (a.mapSort m.φ) k' ξ) ξ) := by
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
      have h2 := h1.conv (tyOK_of_typed hsn hMc hσ.good) (Converts.subst hc σ)
      have hBne := CoC.ne_box_of_hasType hBc
      have hAs : ∃ t, HasType PC (Γ.map (Expr.mapSort m.φ)) (A.mapSort m.φ) (.sort t) := by
        obtain ⟨t, ht⟩ | hA := hMc.regularity
        · rw [ht] at hcc ⊢
          cases t with
          | box => exact (CoC.not_conv_box hBc (converts_symm' hcc)).elim
          | star => exact ⟨_, cube_star_box _ hMc.valid⟩
        · exact hA
      obtain ⟨t, hA⟩ := hAs
      rw [SemC_ne (CoC.ne_box_of_hasType hA)] at h2
      rw [SemC_ne hBne, ← interpK_conv (candAlg P) hA hBc hcc]
      exact h2

/-! ### The sort-typed fundamental lemma -/

/-- The canonical valuation. -/
def canonValC (P : Specification S) : ValK (CandP S) := fun _ k => canonK (candAlg P) k

variable (P) in
theorem goodVal_canon (Δ : Nat → Cls) : GoodVal P Δ (canonValC P) :=
  fun _ k _ => candC_canon k

theorem ncons_canonValC : ncons (canonK (candAlg P)) (canonValC P) = (canonValC P) := by
  funext n; cases n <;> rfl

theorem forall₂_reduces_refl (Γ : List (Expr S)) : List.Forall₂ Reduces Γ Γ :=
  SNGeneric.forall₂_reduces_refl' Γ

/-- The identity substitution with the canonical valuation is reducible. -/
theorem SubstOK.ids (m : CoCMorphism P) {Γ : List (Expr S)} (hv : ValidContextNW P Γ) :
    SubstOK m Γ Γ Expr.var (canonValC P) where
  good := goodVal_canon P _
  ctx := ⟨Γ, forall₂_reduces_refl Γ, hv⟩
  tys n A hn := tyOK_of_typed m.stronglyNormalizing
    (m.hasType (HasTypeNW.lookup'' hv hn).toHasType) (goodVal_canon P _)
  var n A hn := by
    unfold Sem
    simp only [Expr.subst_var]
    exact SemC.var (tyOK_of_typed m.stronglyNormalizing
      (m.hasType (HasTypeNW.lookup'' hv hn).toHasType) (goodVal_canon P _))
      ⟨Γ, _, _, forall₂_reduces_refl Γ, .refl, .refl, HasTypeNW.lookup'' hv hn⟩

/-- The substitution of a canonical `N : A` at depth `Δ` is reducible. -/
theorem substOK_substAt (m : CoCMorphism P) {Γ : List (Expr S)} {N A : Expr S}
    (hN : HasTypeNW P Γ N A)
    {Δ Δ' : List (Expr S)} (hc : CtxSubstRed N Δ Δ') (hv : ValidContextNW P (Δ' ++ Γ))
    (hsrc : ValidContext P (Δ ++ A :: Γ)) :
    SubstOK m (Δ ++ A :: Γ) (Δ' ++ Γ) (Expr.substAt N Δ.length) (canonValC P) := by
  induction hc with
  | nil =>
      have hid := SubstOK.ids m hN.valid
      have hNsem : SemC P (Γ.map (Expr.mapSort m.φ)) (canonValC P) Γ (A.mapSort m.φ) N
          (A.subst Expr.var) := by
        have := fundamental m hN.toHasType hid
        unfold Sem at this
        simp only [Expr.subst_var] at this ⊢
        exact this
      have := hid.cons (by rw [List.map_cons]; exact GoodVal.ncons_canon (goodVal_canon P _) _)
        (tyOK_of_typed m.stronglyNormalizing (m.hasType hN.toHasType) (goodVal_canon P _))
        hNsem
      rw [ncons_canonValC, scons_var] at this
      exact this
  | @cons Δ Δ' D D' _ hr ih =>
      cases hv with
      | cons hv' hD' =>
          cases hsrc with
          | cons hsrc' hD =>
              have := (ih hv' hsrc').lift
                (by rw [List.map_cons]; exact GoodVal.ncons_canon (goodVal_canon P _) _)
                (tyOK_of_sorted m.stronglyNormalizing (m.hasType hD) (goodVal_canon P _))
                ⟨_, D', _, forall₂_reduces_refl _, .refl, .refl, hD'⟩ hr
              rw [ncons_canonValC, ← Expr.substAt_succ] at this
              exact this

end MorphFund

/-- **The route (ii) sort-typed fundamental lemma for every specification with a morphism into
coc.** -/
theorem sortFundamental_of_cocMorphism {S : Type} {P : Specification S} (m : CoCMorphism P) :
    SNGeneric.SortFundamental P := by
  intro Γ N A Δ Δ' M s hN hc hv hM
  have := MorphFund.fundamental m hM.toHasType
    (MorphFund.substOK_substAt m hN hc hv hM.toHasType.valid)
  unfold MorphFund.Sem at this
  exact MorphFund.SemC_sort.1 this

/-- **Expansion postponement for every specification with a morphism into coc.** -/
theorem expansionPostponement_of_cocMorphism {S : Type} {P : Specification S}
    (m : CoCMorphism P) : ExpansionPostponement P :=
  m.expansionPostponement_of_sortFundamental (sortFundamental_of_cocMorphism m)

/-- **Expansion postponement for `cocBox2`**, a non-functional, non-stratified specification
outside the cube. -/
theorem cocBox2_expansionPostponement : ExpansionPostponement cocBox2 :=
  expansionPostponement_of_cocMorphism cocBox2_cocMorphism

/-! ### A second instance outside the cube: doubled sorts, neither functional nor injective -/

/-- Sorts of coc with both sorts doubled. -/
inductive Srt4 where
  | star : Srt4
  | star' : Srt4
  | box : Srt4
  | box' : Srt4
  deriving DecidableEq, Repr

/-- The collapse `∗' ↦ ∗`, `□' ↦ □`. -/
def collapse4 : Srt4 → LambdaPi.Srt
  | .star => .star
  | .star' => .star
  | .box => .box
  | .box' => .box

/-- The calculus of constructions with both sorts doubled: axioms `s : t` for `s ∈ {∗, ∗'}` and
`t ∈ {□, □'}`, and every rule `(s₁, s₂, s₃)` whose third sort collapses to the second. -/
def cocDouble : Specification Srt4 where
  axioms s t := collapse4 s = .star ∧ collapse4 t = .box
  rule _ s₂ s₃ := collapse4 s₃ = collapse4 s₂

/-- `cocDouble` has a morphism into coc. -/
def cocDouble_cocMorphism : CoCMorphism cocDouble where
  φ := collapse4
  axiom_map _ _ h := h
  rule_map a b c h := ⟨h, by cases a <;> cases b <;> trivial⟩

/-- The axioms of `cocDouble` are not functional (`∗ : □` and `∗ : □'`). -/
theorem cocDouble_axioms_not_functional :
    ¬ ∀ s a b, cocDouble.axioms s a → cocDouble.axioms s b → a = b := by
  intro h
  have := h .star .box .box' ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  cases this

/-- The rules of `cocDouble` are not functional (`(∗, ∗, ∗)` and `(∗, ∗, ∗')`). -/
theorem cocDouble_rules_not_functional :
    ¬ ∀ a b c c', cocDouble.rule a b c → cocDouble.rule a b c' → c = c' := by
  intro h
  have := h .star .star .star .star' rfl rfl
  cases this

/-- The axioms of `cocDouble` are not injective (`∗ : □` and `∗' : □`). -/
theorem cocDouble_axioms_not_injective :
    ¬ ∀ s s' t, cocDouble.axioms s t → cocDouble.axioms s' t → s = s' := by
  intro h
  have := h .star .star' .box ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
  cases this

/-- `cocDouble` is not stratified (it has the dependent rule `(∗, □, □)`). -/
theorem cocDouble_not_stratified (L : Stratification cocDouble) : False :=
  not_stratified_of_dependent_rule (P := cocDouble) (s := .star) (t := .box) (r := .box)
    ⟨rfl, rfl⟩ rfl L

/-- **Expansion postponement for `cocDouble`**, a specification outside the cube whose axioms
are neither functional nor injective and whose rules are not functional. -/
theorem cocDouble_expansionPostponement : ExpansionPostponement cocDouble :=
  expansionPostponement_of_cocMorphism cocDouble_cocMorphism

end PureTypeSystem
