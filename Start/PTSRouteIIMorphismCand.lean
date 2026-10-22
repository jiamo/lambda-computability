import Start.PTSExpansionSNGeneric

/-!
# Series V, round 1, part C2: route (ii) candidates for a specification with SN

The candidate layer of the round-11 coc proof (`Start/PTSRouteIICoC.lean`), restated for an
arbitrary specification `P` over any sort type, with candidates as sets of `P`-judgements and the
round-11 interpretation (`ErasureCoC.interpK`, generic in its base) taken over them.  Strong
normalization of `P` is the only hypothesis (it is used for CR3 at neutral applications).

* `SNGeneric.IsCandC P`, `piOC P`, `piKC P`, `CandC P`, `candAlg P : KAlg (CandP S)`;
* `isCandC_piO`, `isCandC_piK` (CR1–CR3, expansion, weakening);
* `interpC_cand` — the interpretation of a well-classified coc kind or constructor under a good
  valuation of `P`-candidates is a `P`-candidate.

For a specification with a morphism `φ` into coc the interpreted term is the image
`T.mapSort φ`; the fundamental lemma over this layer is the open step
(`docs/goal/evidence/M29-EP.md`, Series V, round 1).
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace SNGeneric

open LambdaPi (Srt)
open ErasureCoC (V KAlg canonK ValK extK extK_self interpK)
open CoC (Sk Cls cl ncons RelC WC domSk)

/-- Judgement candidates over any sort type. -/
abbrev CandP (S : Type) := List (Expr S) → Expr S → Expr S → Prop

section

variable {S : Type} (P : Specification S)

theorem converts_pi_reduces' {T A B : Expr S} (h : Converts T (.pi A B)) :
    ∃ A₂ B₂, Reduces T (.pi A₂ B₂) ∧ Reduces A A₂ ∧ Reduces B B₂ := by
  obtain ⟨J, hTJ, hPJ⟩ := Converts.join h
  obtain ⟨A₂, B₂, rfl, hA, hB⟩ := Reduces.pi_inv hPJ
  exact ⟨A₂, B₂, hTJ, hA, hB⟩

theorem converts_symm' {M N : Expr S} (h : Converts M N) : Converts N M :=
  Relation.EqvGen.symm _ _ h

theorem converts_trans' {M N K : Expr S} (h₁ : Converts M N) (h₂ : Converts N K) :
    Converts M K :=
  Relation.EqvGen.trans _ _ _ h₁ h₂

theorem converts_rename' {M N : Expr S} (h : Converts M N) (ρ : ℕ → ℕ) :
    Converts (M.rename ρ) (N.rename ρ) :=
  Converts.rename h ρ

/-- **Candidates for coc.** -/
structure IsCandC (C : (CandP S)) : Prop where
  norm : ∀ {Γ M T}, C Γ M T → NormNW P Γ M T
  conv : ∀ {Γ M T T'}, C Γ M T → Converts T T' → C Γ M T'
  neutral : ∀ {Γ M T}, NeNW P Γ M T → C Γ M T
  expand : ∀ {Γ M M' T}, Reduces M M' → C Γ M' T → C Γ M T
  weaken : ∀ {Γ M T} (Γ₀ : List (Expr S)) {Δ : List (Expr S)}, C Γ M T →
    List.Forall₂ Reduces (Γ₀ ++ Γ) Δ → ValidContextNW P Δ →
    C (Γ₀ ++ Γ) (M.rename (wk Γ₀)) (T.rename (wk Γ₀))

/-- The base candidate: normalizable coc judgements. -/
theorem isCandC_normNW : IsCandC P (NormNW P) where
  norm h := h
  conv h hc := h.convType hc
  neutral h := h.toNormNW
  expand hr h := NormNW.expand hr h
  weaken := fun {_ _ _} Γ₀ {_} h hc hv => h.weaken Γ₀ hc hv

/-- The object product of candidates: Kripke closure under application to arguments in the
candidate of the domain. -/
def piOC (X Y : (CandP S)) : (CandP S) := fun Γ M T => NormNW P Γ M T ∧
  ∀ (Γ₀ : List (Expr S)) (N A B : Expr S),
    Reduces (T.rename (wk Γ₀)) (.pi A B) → X (Γ₀ ++ Γ) N A →
    Y (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) N) (B.instantiate N)

/-- **Candidates at a kind skeleton**: `IsCandC P` at `∗`, preservation at `arr`; object
products are transparent. -/
def CandC : (k : Sk) → V (CandP S) k → Prop
  | .star, X => IsCandC P X
  | .arrO k, v => CandC k v
  | .arr a k, F => ∀ v, CandC a v → CandC k (F v)

/-- The product over a constructor variable of skeleton `a`: Kripke closure under application to
every constructor `U` in the candidate `X` of the bound kind, for every candidate value `v` of
the bound variable. -/
def piKC (a : Sk) (X : (CandP S)) (F : V (CandP S) a → (CandP S)) : (CandP S) := fun Γ M T => NormNW P Γ M T ∧
  ∀ (Γ₀ : List (Expr S)) (U K B : Expr S) (v : V (CandP S) a), CandC P a v →
    Reduces (T.rename (wk Γ₀)) (.pi K B) → X (Γ₀ ++ Γ) U K →
    F v (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) U) (B.instantiate U)

/-- **The coc candidate algebra.** -/
def candAlg : KAlg (CandP S) where
  dflt := NormNW P
  piK := piKC P
  piO := piOC P

variable {P}

theorem candC_canon : ∀ k : Sk, CandC P k (canonK (candAlg P) k)
  | .star => isCandC_normNW P
  | .arrO k => candC_canon k
  | .arr _ k => fun _ _ => candC_canon k

/-- **CR1–CR3, expansion and weakening for the object product.** -/
theorem isCandC_piO (hsn : SystemStronglyNormalizing P) {X Y : (CandP S)} (hX : IsCandC P X) (hY : IsCandC P Y) : IsCandC P (piOC P X Y) := by
  refine ⟨fun h => h.1, fun {Γ M T T'} h hc => ⟨h.1.convType hc, ?_⟩, fun {Γ M T} h => ?_,
    fun {Γ M M' T} hr h => ⟨NormNW.expand hr h.1, fun Γ₀ N A B hT hN =>
      hY.expand (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ N A B hT hN)⟩,
    fun {Γ M T} Γ₀ {Δ} h hc hv => ⟨h.1.weaken Γ₀ hc hv, fun Γ₁ N A B hT hN => by
      rw [rename_wk_wk'] at hT ⊢
      rw [← List.append_assoc] at hN ⊢
      exact h.2 (Γ₁ ++ Γ₀) N A B hT hN⟩⟩
  · intro Γ₀ N A B hT' hN
    have hc' : Converts (T.rename (wk Γ₀)) (.pi A B) :=
      converts_trans' (converts_rename' hc _) (Reduces.converts hT')
    obtain ⟨A₂, B₂, hT₂, hA₂, hB₂⟩ := converts_pi_reduces' hc'
    have := h.2 Γ₀ N A₂ B₂ hT₂ (hX.conv hN (Reduces.converts hA₂))
    exact hY.conv this
      (converts_symm' (Reduces.converts (Reduces.instantiate hB₂ .refl)))
  · refine ⟨h.toNormNW, fun Γ₀ N A B hT hN => ?_⟩
    exact hY.neutral (NeNW.app_wk hsn h Γ₀ hT (hX.norm hN))

/-- **CR1–CR3, expansion and weakening for the product over a constructor variable.** -/
theorem isCandC_piK (hsn : SystemStronglyNormalizing P) {a : Sk} {X : (CandP S)} {F : V (CandP S) a → (CandP S)} (hX : IsCandC P X)
    (hF : ∀ v, CandC P a v → IsCandC P (F v)) : IsCandC P (piKC P a X F) := by
  refine ⟨fun h => h.1, fun {Γ M T T'} h hc => ⟨h.1.convType hc, ?_⟩, fun {Γ M T} h => ?_,
    fun {Γ M M' T} hr h => ⟨NormNW.expand hr h.1, fun Γ₀ U K B v hv hT hU =>
      (hF v hv).expand (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ U K B v hv hT hU)⟩,
    fun {Γ M T} Γ₀ {Δ} h hc hvd => ⟨h.1.weaken Γ₀ hc hvd, fun Γ₁ U K B v hv hT hU => by
      rw [rename_wk_wk'] at hT ⊢
      rw [← List.append_assoc] at hU ⊢
      exact h.2 (Γ₁ ++ Γ₀) U K B v hv hT hU⟩⟩
  · intro Γ₀ U K B v hv hT' hU
    have hc' : Converts (T.rename (wk Γ₀)) (.pi K B) :=
      converts_trans' (converts_rename' hc _) (Reduces.converts hT')
    obtain ⟨K₂, B₂, hT₂, hK₂, hB₂⟩ := converts_pi_reduces' hc'
    have := h.2 Γ₀ U K₂ B₂ v hv hT₂ (hX.conv hU (Reduces.converts hK₂))
    exact (hF v hv).conv this
      (converts_symm' (Reduces.converts (Reduces.instantiate hB₂ .refl)))
  · refine ⟨h.toNormNW, fun Γ₀ U K B v hv hT hU => ?_⟩
    exact (hF v hv).neutral (NeNW.app_wk hsn h Γ₀ hT (hX.norm hU))

/-! ### The interpretation lands in candidates -/

/-- A valuation is good when it assigns candidates to the relevant values. -/
def GoodVal (P : Specification S) (Δ : Nat → Cls) (ξ : ValK (CandP S)) : Prop := ∀ n k, RelC (Δ n) k → CandC P k (ξ n k)

theorem GoodVal.ncons_ext {Δ : Nat → Cls} {ξ : ValK (CandP S)} (h : GoodVal P Δ ξ) {a : Sk}
    {v : V (CandP S) a} (hv : CandC P a v) :
    GoodVal P (ncons (.constr a) Δ) (ncons (extK (candAlg P) a v) ξ) := by
  intro n k hk
  cases n with
  | zero =>
      have := RelC.constr_eq hk
      subst this
      simpa using hv
  | succ n => exact h n k hk

theorem GoodVal.ncons_obj {Δ : Nat → Cls} {ξ : ValK (CandP S)} (h : GoodVal P Δ ξ)
    (e : (k : Sk) → V (CandP S) k) : GoodVal P (ncons .obj Δ) (ncons e ξ) := by
  intro n k hk
  cases n with
  | zero => exact hk.not_obj.elim
  | succ n => exact h n k hk

/-- **The interpretation of a well-classified kind or constructor is a candidate.** -/
theorem interpC_cand (hsn : SystemStronglyNormalizing P) (M : Expr Srt) {Δ : Nat → Cls} {ξ : ValK (CandP S)} {k : Sk} (hM : WC Δ M)
    (hξ : GoodVal P Δ ξ) (hk : RelC (cl Δ M) k) : CandC P k (interpK (candAlg P) Δ M k ξ) := by
  induction M generalizing Δ ξ k with
  | var n => exact hξ n k hk
  | sort s => exact candC_canon k
  | app F U ihF ihU =>
      obtain ⟨hF, hU, hok⟩ := hM
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl Δ U = .constr a := hok
        simp only [interpK, hcU]
        exact ihF hF hξ (.inl ha) _ (ihU hU hξ (.inl hcU))
      · rw [ha] at hok
        have hcU : cl Δ U = .obj := hok
        simp only [interpK, hcU]
        exact ihF hF hξ (.inl ha)
  | lam A b ihA ihb =>
      obtain ⟨hA, hb⟩ := hM
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hb hb₀
        simp only [domSk, interpK, hcA]
        intro v hv
        exact ihb hb (hξ.ncons_ext hv) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interpK, hcA]
        exact ihb hb (hξ.ncons_obj _) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interpK, hcA]
        exact ihb hb (hξ.ncons_obj _) (.inl hb₀)
  | pi A B ihA ihB =>
      obtain ⟨hA, hB, hpA, hpB⟩ := hM
      have := hk.pi
      subst this
      have hXA : IsCandC P (interpK (candAlg P) Δ A .star ξ) := ihA hA hξ (.of_piOK hpA)
      simp only [interpK]
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hB hpB
        exact isCandC_piK hsn hXA (fun v hv => ihB hB (hξ.ncons_ext hv) (.of_piOK hpB))
      · rw [hcA] at hB hpB
        exact isCandC_piO hsn hXA (ihB hB (hξ.ncons_obj _) (.of_piOK hpB))
      · rw [hcA] at hB hpB
        exact isCandC_piO hsn hXA (ihB hB (hξ.ncons_obj _) (.of_piOK hpB))


end

end SNGeneric

end PureTypeSystem
