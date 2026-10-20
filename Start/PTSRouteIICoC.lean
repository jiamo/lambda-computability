import Start.PTSErasureCoCOmega
import Start.PTSRouteIITwoLevel

/-!
# Round 11, part A2: the route (ii) relation for coc, over the Fω interpretation

`Start/PTSErasureCoCOmega.lean` interprets coc kinds and constructors over an arbitrary base
algebra.  Here the base is the type `Cand` of round-10 judgement candidates, now for the
specification `cubeSpec coc`:

* `IsCandC` — candidates for coc: normalizable judgements, closed under conversion of the type,
  containing the neutral normalizable judgements (CR3), closed under expansion of the subject and
  under weakening (as `IsCandN` of round 10, with `cubeSpec coc` for `lambdaP2`);
* `CandC k v` — candidates at a kind skeleton: `IsCandC` at `∗`, preservation at
  `arr` (this is the `TRed` of the round-11 plan at `arr κ₁ κ₂`, on the semantic side);
* `candAlg : KAlg Cand` — the default candidate `NormNW (cubeSpec coc)`, the object product
  (Kripke closure under application, as `GoodP` at an arrow) and the product over a constructor
  variable of skeleton `a` (Kripke closure under application to every constructor `U` in the
  candidate of the bound kind, for every semantic value `v` with `CandC a v`, as `GoodP .all`);
* `isCandC_piO`, `isCandC_piK` — CR1–CR3, expansion and weakening for both products;
* **`interpC_cand`** — the interpretation of every well-classified kind or constructor under a
  valuation of candidates is a candidate (at `∗`, an `IsCandC`);
* `interpC_conv` — invariance under conversion, specialized from `ErasureCoC.interpK_conv`.

The fundamental lemma for `HasType (cubeSpec coc)` (part A3) is not proved here; see
`docs/goal/evidence/M29-EP.md`, round 11.
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace RouteIICoC

open LambdaPi (Srt)
open RouteII (Cand NormNW NeNW wk wk_nil rename_wk_wk converts_pi_reduces converts_rename)
open ErasureCoC (V KAlg canonK ValK extK extK_self interpK interpK_conv)
open CoC (Sk Cls cl ncons bindC RelC WC domSk ctxCl)

/-- The specification of the calculus of constructions. -/
abbrev PC : Specification Srt := cubeSpec coc

/-- **Candidates for coc.** -/
structure IsCandC (C : Cand) : Prop where
  norm : ∀ {Γ M T}, C Γ M T → NormNW PC Γ M T
  conv : ∀ {Γ M T T'}, C Γ M T → Converts T T' → C Γ M T'
  neutral : ∀ {Γ M T}, NeNW PC Γ M T → C Γ M T
  expand : ∀ {Γ M M' T}, Reduces M M' → C Γ M' T → C Γ M T
  weaken : ∀ {Γ M T} (Γ₀ : List (Expr Srt)) {Δ : List (Expr Srt)}, C Γ M T →
    List.Forall₂ Reduces (Γ₀ ++ Γ) Δ → ValidContextNW PC Δ →
    C (Γ₀ ++ Γ) (M.rename (wk Γ₀)) (T.rename (wk Γ₀))

/-- The base candidate: normalizable coc judgements. -/
theorem isCandC_normNW : IsCandC (NormNW PC) where
  norm h := h
  conv h hc := h.convType hc
  neutral h := h.toNormNW
  expand hr h := RouteII.NormNW.expand hr h
  weaken := fun {_ _ _} Γ₀ {_} h hc hv => h.weaken Γ₀ hc hv

/-- The object product of candidates: Kripke closure under application to arguments in the
candidate of the domain. -/
def piOC (X Y : Cand) : Cand := fun Γ M T => NormNW PC Γ M T ∧
  ∀ (Γ₀ : List (Expr Srt)) (N A B : Expr Srt),
    Reduces (T.rename (wk Γ₀)) (.pi A B) → X (Γ₀ ++ Γ) N A →
    Y (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) N) (B.instantiate N)

/-- **Candidates at a kind skeleton**: `IsCandC` at `∗`, preservation at `arr`; object
products are transparent. -/
def CandC : (k : Sk) → V Cand k → Prop
  | .star, X => IsCandC X
  | .arrO k, v => CandC k v
  | .arr a k, F => ∀ v, CandC a v → CandC k (F v)

/-- The product over a constructor variable of skeleton `a`: Kripke closure under application to
every constructor `U` in the candidate `X` of the bound kind, for every candidate value `v` of
the bound variable. -/
def piKC (a : Sk) (X : Cand) (F : V Cand a → Cand) : Cand := fun Γ M T => NormNW PC Γ M T ∧
  ∀ (Γ₀ : List (Expr Srt)) (U K B : Expr Srt) (v : V Cand a), CandC a v →
    Reduces (T.rename (wk Γ₀)) (.pi K B) → X (Γ₀ ++ Γ) U K →
    F v (Γ₀ ++ Γ) (.app (M.rename (wk Γ₀)) U) (B.instantiate U)

/-- **The coc candidate algebra.** -/
def candAlg : KAlg Cand where
  dflt := NormNW PC
  piK := piKC
  piO := piOC

theorem candC_canon : ∀ k : Sk, CandC k (canonK candAlg k)
  | .star => isCandC_normNW
  | .arrO k => candC_canon k
  | .arr _ k => fun _ _ => candC_canon k

/-- **CR1–CR3, expansion and weakening for the object product.** -/
theorem isCandC_piO {X Y : Cand} (hX : IsCandC X) (hY : IsCandC Y) : IsCandC (piOC X Y) := by
  refine ⟨fun h => h.1, fun {Γ M T T'} h hc => ⟨h.1.convType hc, ?_⟩, fun {Γ M T} h => ?_,
    fun {Γ M M' T} hr h => ⟨RouteII.NormNW.expand hr h.1, fun Γ₀ N A B hT hN =>
      hY.expand (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ N A B hT hN)⟩,
    fun {Γ M T} Γ₀ {Δ} h hc hv => ⟨h.1.weaken Γ₀ hc hv, fun Γ₁ N A B hT hN => by
      rw [rename_wk_wk] at hT ⊢
      rw [← List.append_assoc] at hN ⊢
      exact h.2 (Γ₁ ++ Γ₀) N A B hT hN⟩⟩
  · intro Γ₀ N A B hT' hN
    have hc' : Converts (T.rename (wk Γ₀)) (.pi A B) :=
      RouteII.converts_trans (converts_rename hc _) (Reduces.converts hT')
    obtain ⟨A₂, B₂, hT₂, hA₂, hB₂⟩ := converts_pi_reduces hc'
    have := h.2 Γ₀ N A₂ B₂ hT₂ (hX.conv hN (Reduces.converts hA₂))
    exact hY.conv this
      (RouteII.converts_symm (Reduces.converts (Reduces.instantiate hB₂ .refl)))
  · refine ⟨h.toNormNW, fun Γ₀ N A B hT hN => ?_⟩
    exact hY.neutral (RouteII.NeNW.app_wk coc h Γ₀ hT (hX.norm hN))

/-- **CR1–CR3, expansion and weakening for the product over a constructor variable.** -/
theorem isCandC_piK {a : Sk} {X : Cand} {F : V Cand a → Cand} (hX : IsCandC X)
    (hF : ∀ v, CandC a v → IsCandC (F v)) : IsCandC (piKC a X F) := by
  refine ⟨fun h => h.1, fun {Γ M T T'} h hc => ⟨h.1.convType hc, ?_⟩, fun {Γ M T} h => ?_,
    fun {Γ M M' T} hr h => ⟨RouteII.NormNW.expand hr h.1, fun Γ₀ U K B v hv hT hU =>
      (hF v hv).expand (Reduces.app (hr.rename _) .refl) (h.2 Γ₀ U K B v hv hT hU)⟩,
    fun {Γ M T} Γ₀ {Δ} h hc hvd => ⟨h.1.weaken Γ₀ hc hvd, fun Γ₁ U K B v hv hT hU => by
      rw [rename_wk_wk] at hT ⊢
      rw [← List.append_assoc] at hU ⊢
      exact h.2 (Γ₁ ++ Γ₀) U K B v hv hT hU⟩⟩
  · intro Γ₀ U K B v hv hT' hU
    have hc' : Converts (T.rename (wk Γ₀)) (.pi K B) :=
      RouteII.converts_trans (converts_rename hc _) (Reduces.converts hT')
    obtain ⟨K₂, B₂, hT₂, hK₂, hB₂⟩ := converts_pi_reduces hc'
    have := h.2 Γ₀ U K₂ B₂ v hv hT₂ (hX.conv hU (Reduces.converts hK₂))
    exact (hF v hv).conv this
      (RouteII.converts_symm (Reduces.converts (Reduces.instantiate hB₂ .refl)))
  · refine ⟨h.toNormNW, fun Γ₀ U K B v hv hT hU => ?_⟩
    exact (hF v hv).neutral (RouteII.NeNW.app_wk coc h Γ₀ hT (hX.norm hU))

/-! ### The interpretation lands in candidates -/

/-- A valuation is good when it assigns candidates to the relevant values. -/
def GoodVal (Δ : Nat → Cls) (ξ : ValK Cand) : Prop := ∀ n k, RelC (Δ n) k → CandC k (ξ n k)

theorem GoodVal.ncons_ext {Δ : Nat → Cls} {ξ : ValK Cand} (h : GoodVal Δ ξ) {a : Sk}
    {v : V Cand a} (hv : CandC a v) :
    GoodVal (ncons (.constr a) Δ) (ncons (extK candAlg a v) ξ) := by
  intro n k hk
  cases n with
  | zero =>
      have := RelC.constr_eq hk
      subst this
      simpa using hv
  | succ n => exact h n k hk

theorem GoodVal.ncons_obj {Δ : Nat → Cls} {ξ : ValK Cand} (h : GoodVal Δ ξ)
    (e : (k : Sk) → V Cand k) : GoodVal (ncons .obj Δ) (ncons e ξ) := by
  intro n k hk
  cases n with
  | zero => exact hk.not_obj.elim
  | succ n => exact h n k hk

/-- **The interpretation of a well-classified kind or constructor is a candidate.** -/
theorem interpC_cand (M : Expr Srt) {Δ : Nat → Cls} {ξ : ValK Cand} {k : Sk} (hM : WC Δ M)
    (hξ : GoodVal Δ ξ) (hk : RelC (cl Δ M) k) : CandC k (interpK candAlg Δ M k ξ) := by
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
      have hXA : IsCandC (interpK candAlg Δ A .star ξ) := ihA hA hξ (.of_piOK hpA)
      simp only [interpK]
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hB hpB
        exact isCandC_piK hXA (fun v hv => ihB hB (hξ.ncons_ext hv) (.of_piOK hpB))
      · rw [hcA] at hB hpB
        exact isCandC_piO hXA (ihB hB (hξ.ncons_obj _) (.of_piOK hpB))
      · rw [hcA] at hB hpB
        exact isCandC_piO hXA (ihB hB (hξ.ncons_obj _) (.of_piOK hpB))

/-- **Invariance under conversion** of the coc candidate interpretation of well-typed kinds and
types (`erω_conv` for the candidate algebra). -/
theorem interpC_conv {Γ : List (Expr Srt)} {A B : Expr Srt} {s t : Srt}
    (hA : HasType PC Γ A (.sort s)) (hB : HasType PC Γ B (.sort t))
    (hc : Converts A B) (ξ : ValK Cand) :
    interpK candAlg (ctxCl Γ) A .star ξ = interpK candAlg (ctxCl Γ) B .star ξ :=
  interpK_conv candAlg hA hB hc ξ

end RouteIICoC

end PureTypeSystem
