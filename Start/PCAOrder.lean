/-
**The order of partial combinatory algebras under applicative morphisms.**

Longley's programme orders the partial combinatory algebras by the existence of an applicative
morphism (`Start/PCAMorphism.lean`).  This module formalizes that order and the first separation
in it.

Two things have to be said, and the first is a warning:

* the *plain* order — `Realizability.PCALe A B`, "there is an applicative morphism `A → B`" — is a
  preorder (`Realizability.pcaLe_refl`, `Realizability.pcaLe_trans`) but it is **degenerate**:
  every algebra maps to every algebra, by the trivial morphism of
  `Start/KleeneNoRetraction.lean`, so all algebras are equivalent
  (`Realizability.pcaLe_trivial`, `Realizability.pcaEquiv_of_any`).  Nothing can be separated in
  it, which is exactly why `Start/KleeneNoRetraction.lean` had to assume that the target can read
  something back off a representative;
* the informative order is therefore the one carried by the morphisms that *decide* their
  representatives: `Realizability.AppMorphism.Decides γ` asks for a single element of the target
  that recovers, from any representative, whether it represents the combinator `k` or the
  combinator `k i` of the source.  This is again a preorder — the identity decides, and decidable
  morphisms compose (`Realizability.AppMorphism.decides_id`,
  `Realizability.AppMorphism.Decides.comp`) — and in it the two Kleene algebras **are** separated:

  * `Realizability.KleeneTwo.kOneToTwo_decides` — the morphism `K₁ → K₂` decides, so `K₁ ⪯ K₂`;
  * `Realizability.KleeneTwo.not_decides` — no applicative morphism `K₂ → K₁` decides, because a
    decision of the booleans already separates bits in the sense of
    `Realizability.KleeneTwo.SeparatesBits`, which no morphism does;
  * `Realizability.KleeneTwo.kleene_strict` — hence `K₁ < K₂` strictly.

That the two combinators are distinct in a nontrivial algebra is `Realizability.PCA.k_ne_kI` of
`Start/ModestColimits.lean`.
-/

import Start.KleeneNoRetraction
import Start.ModestColimits

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

noncomputable section

namespace Realizability

open scoped Realizability.Kleene

/-! ### The plain order, and its degeneracy -/

/-- `A ⪯ B`: there is an applicative morphism from `A` to `B`. -/
def PCALe (A B : Type u) [PCA A] [PCA B] : Prop := Nonempty (AppMorphism A B)

theorem pcaLe_refl (A : Type u) [PCA A] : PCALe A A := ⟨AppMorphism.id A⟩

theorem pcaLe_trans {A B C : Type u} [PCA A] [PCA B] [PCA C]
    (h₁ : PCALe A B) (h₂ : PCALe B C) : PCALe A C :=
  ⟨h₁.some.comp h₂.some⟩

/-- The equivalence induced by the order. -/
def PCAEquiv (A B : Type u) [PCA A] [PCA B] : Prop := PCALe A B ∧ PCALe B A

theorem pcaEquiv_refl (A : Type u) [PCA A] : PCAEquiv A A := ⟨pcaLe_refl A, pcaLe_refl A⟩

theorem PCAEquiv.symm {A B : Type u} [PCA A] [PCA B] (h : PCAEquiv A B) : PCAEquiv B A :=
  ⟨h.2, h.1⟩

theorem PCAEquiv.trans {A B C : Type u} [PCA A] [PCA B] [PCA C]
    (h₁ : PCAEquiv A B) (h₂ : PCAEquiv B C) : PCAEquiv A C :=
  ⟨pcaLe_trans h₁.1 h₂.1, pcaLe_trans h₂.2 h₁.2⟩

/-- **The plain order is degenerate**: the trivial morphism makes every algebra precede every
algebra. -/
theorem pcaLe_trivial (A B : Type u) [PCA A] [PCA B] : PCALe A B :=
  ⟨AppMorphism.trivialMor A B⟩

/-- Hence all partial combinatory algebras are equivalent in the plain order: it separates
nothing. -/
theorem pcaEquiv_of_any (A B : Type u) [PCA A] [PCA B] : PCAEquiv A B :=
  ⟨pcaLe_trivial A B, pcaLe_trivial B A⟩

/-! ### Morphisms that decide their representatives -/

namespace AppMorphism

variable {A B C : Type u} [PCA A] [PCA B] [PCA C]

/-- A morphism **decides** when one element of the target recovers, from any representative,
whether the element represented is the combinator `k` or the combinator `k i`. -/
def Decides (γ : AppMorphism A B) : Prop :=
  ∃ q : B,
    (∀ b, γ.map (PCA.k : A) b → PCA.app q b = Part.some (PCA.k : B)) ∧
    (∀ b, γ.map (PCA.kI A) b → PCA.app q b = Part.some (PCA.kI B))

/-- The identity morphism decides, by the identity combinator. -/
theorem decides_id (A : Type u) [PCA A] : (AppMorphism.id A).Decides := by
  refine ⟨PCA.i A, ?_, ?_⟩ <;> rintro b rfl <;> simp [PCA.i_app]

/-- One step of a composite decision: from a representative `c` of `b`, the realizer of `δ`
applied to a representative `e` of the decider `q` of `γ` produces a representative of `q · b`,
which the decider `r` of `δ` then reads. -/
theorem decides_step {δ : AppMorphism B C} {q b v : B} {e c r w : C}
    (he : δ.map q e) (hbc : δ.map b c) (hq : PCA.app q b = Part.some v)
    (hw : ∀ d, δ.map v d → PCA.app r d = Part.some w) :
    PCA.app (PCA.lam1 ((Expr.const r).app
      (((Expr.const δ.realizer).app (Expr.const e)).app (Expr.var 0)))) c = Part.some w := by
  obtain ⟨d, hd, hdmem⟩ :=
    δ.realizer_app q b e c he hbc v (by rw [hq]; exact Part.mem_some _)
  have hdec : PCA.app r d = Part.some w := hw d hd
  have hle := PCA.lam1_app ((Expr.const r).app
    (((Expr.const δ.realizer).app (Expr.const e)).app (Expr.var 0))) c
  have hev : ((Expr.const r).app
      (((Expr.const δ.realizer).app (Expr.const e)).app (Expr.var 0))).eval
        (Function.update (PCA.env0 C) 0 c)
      = Part.some r ⬝ ((Part.some δ.realizer ⬝ Part.some e) ⬝ Part.some c) := by
    simp only [Expr.eval_app, Expr.eval_const, Expr.eval_var, Function.update_self]
  have hmem0 : w ∈ ((Expr.const r).app
      (((Expr.const δ.realizer).app (Expr.const e)).app (Expr.var 0))).eval
        (Function.update (PCA.env0 C) 0 c) := by
    rw [hev]
    exact mem_papp (Part.mem_some r) hdmem (by rw [hdec]; exact Part.mem_some _)
  have hmem := hle w hmem0
  rw [papp_some_some] at hmem
  exact Part.eq_some_iff.2 hmem

/-- Decidable morphisms compose: the composite decider reads the representative through the
realizer of the second morphism, applied to a representative of the first decider. -/
theorem Decides.comp {γ : AppMorphism A B} {δ : AppMorphism B C}
    (hγ : γ.Decides) (hδ : δ.Decides) : (γ.comp δ).Decides := by
  obtain ⟨q, hqk, hqkI⟩ := hγ
  obtain ⟨r, hrk, hrkI⟩ := hδ
  obtain ⟨e, he⟩ := δ.map_nonempty q
  refine ⟨PCA.lam1 ((Expr.const r).app
      (((Expr.const δ.realizer).app (Expr.const e)).app (Expr.var 0))), ?_, ?_⟩
  · rintro c ⟨b, hb, hbc⟩
    exact decides_step he hbc (hqk b hb) hrk
  · rintro c ⟨b, hb, hbc⟩
    exact decides_step he hbc (hqkI b hb) hrkI

end AppMorphism

/-! ### The informative order -/

/-- `A ⪯ B` in the informative order: there is an applicative morphism `A → B` that decides its
representatives. -/
def PCALeD (A B : Type u) [PCA A] [PCA B] : Prop := ∃ γ : AppMorphism A B, γ.Decides

theorem pcaLeD_refl (A : Type u) [PCA A] : PCALeD A A :=
  ⟨AppMorphism.id A, AppMorphism.decides_id A⟩

theorem pcaLeD_trans {A B C : Type u} [PCA A] [PCA B] [PCA C]
    (h₁ : PCALeD A B) (h₂ : PCALeD B C) : PCALeD A C := by
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨δ, hδ⟩ := h₂
  exact ⟨γ.comp δ, hγ.comp hδ⟩

theorem pcaLe_of_pcaLeD {A B : Type u} [PCA A] [PCA B] (h : PCALeD A B) : PCALe A B :=
  ⟨h.choose⟩

/-! ### The two Kleene algebras are separated -/

namespace KleeneTwo

open scoped Realizability.Kleene

/-- The operation on Baire space that reads its argument at `0` and returns the first or the
second projection combinator of `K₂` according to whether the value read is `n₀`. -/
noncomputable def selEl (n₀ : ℕ) : (ℕ → ℕ) → ℕ → ℕ :=
  fun β => if β 0 = n₀ then (PCA.k : ℕ → ℕ) else PCA.kI (ℕ → ℕ)

theorem cont_selEl (n₀ : ℕ) : Cont (selEl n₀) := by
  intro β _
  refine ⟨1, fun β' h => ?_⟩
  simp only [selEl, h 0 (by omega)]

/-- The element of `K₂` performing that test. -/
noncomputable def selAssoc (n₀ : ℕ) : ℕ → ℕ := detAssoc (selEl n₀)

theorem appK_selAssoc (n₀ : ℕ) (β : ℕ → ℕ) :
    appK (selAssoc n₀) β = Part.some (selEl n₀ β) :=
  appK_detAssoc (cont_selEl n₀) β

theorem selEl_natEl_self (n₀ : ℕ) : selEl n₀ (natEl n₀) = (PCA.k : ℕ → ℕ) := by
  simp [selEl, natEl]

theorem selEl_natEl_ne {n₀ n : ℕ} (h : n ≠ n₀) : selEl n₀ (natEl n) = PCA.kI (ℕ → ℕ) := by
  simp [selEl, natEl, h]

/-- Both Kleene algebras have two distinct elements, so their projection combinators differ
(`Realizability.PCA.k_ne_kI`). -/
theorem kI_ne_k_nat : (PCA.kI ℕ) ≠ (PCA.k : ℕ) := fun h => PCA.k_ne_kI (A := ℕ) h.symm

theorem kI_ne_k_baire : (PCA.kI (ℕ → ℕ)) ≠ (PCA.k : ℕ → ℕ) :=
  fun h => PCA.k_ne_kI (A := ℕ → ℕ) h.symm

/-- **The morphism `K₁ → K₂` decides**: a representative is the constant function naming the
number, and a test on its value at `0` tells the two projection combinators apart. -/
theorem kOneToTwo_decides : kOneToTwo.Decides := by
  refine ⟨selAssoc (PCA.k : ℕ), ?_, ?_⟩
  · rintro b rfl
    change appK (selAssoc (PCA.k : ℕ)) (natEl (PCA.k : ℕ)) = _
    rw [appK_selAssoc, selEl_natEl_self]
  · rintro b rfl
    change appK (selAssoc (PCA.k : ℕ)) (natEl (PCA.kI ℕ)) = _
    rw [appK_selAssoc, selEl_natEl_ne kI_ne_k_nat]

/-- A decision of the projection combinators already separates bits: the `K₂` element
`selAssoc 0` turns the constant function `0` into the first and the constant function `1` into
the second combinator, and a partial recursive code turns the answer back into the bit. -/
theorem separatesBits_of_decides {δ : AppMorphism (ℕ → ℕ) ℕ} (h : δ.Decides) :
    SeparatesBits δ := by
  classical
  obtain ⟨q, hqk, hqkI⟩ := h
  obtain ⟨p, hp⟩ := δ.map_nonempty (selAssoc 0)
  -- the decoder: the first combinator of `K₁` stands for the bit `0`, everything else for `1`
  obtain ⟨cdec, hcdec⟩ := Kleene.exists_code_of_computable
    (f := fun n => if n = (PCA.k : ℕ) then 0 else 1)
    (Primrec.to_comp (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const (PCA.k : ℕ)))
      (Primrec.const 0) (Primrec.const 1)))
  set dec : ℕ := Encodable.encode cdec with hdecdef
  have hdecval : ∀ n : ℕ, PCA.app dec n = Part.some (if n = (PCA.k : ℕ) then 0 else 1) := by
    intro n
    rw [Kleene.k1_app, hdecdef, Kleene.natApp_encode, hcdec]
  refine ⟨PCA.lam1 ((Expr.const (PCA.comp dec q)).app
      (((Expr.const δ.realizer).app (Expr.const p)).app (Expr.var 0))), ?_⟩
  intro b m hb hm
  have hval : PCA.app (selAssoc 0) (natEl b) = Part.some (selEl 0 (natEl b)) := by
    change appK (selAssoc 0) (natEl b) = _
    rw [appK_selAssoc]
  have hstep : ∀ (v : ℕ → ℕ) (w : ℕ), selEl 0 (natEl b) = v →
      (∀ d, δ.map v d → PCA.app (PCA.comp dec q) d = Part.some w) →
      PCA.app (PCA.lam1 ((Expr.const (PCA.comp dec q)).app
        (((Expr.const δ.realizer).app (Expr.const p)).app (Expr.var 0)))) m = Part.some w := by
    intro v w hv hw
    exact AppMorphism.decides_step hp hm (by rw [hval, hv]) hw
  have hcomp : ∀ (d n : ℕ), PCA.app q d = Part.some n →
      PCA.app (PCA.comp dec q) d = Part.some (if n = (PCA.k : ℕ) then 0 else 1) := by
    intro d n hn
    have hle := PCA.comp_app dec q d
    have hmem : (if n = (PCA.k : ℕ) then 0 else 1) ∈
        Part.some dec ⬝ (Part.some q ⬝ Part.some d) := by
      rw [papp_some_some, hn, papp_some_some, hdecval]
      exact Part.mem_some _
    have := hle _ hmem
    rw [papp_some_some] at this
    exact Part.eq_some_iff.2 this
  interval_cases b
  · have hv : selEl 0 (natEl 0) = (PCA.k : ℕ → ℕ) := selEl_natEl_self 0
    have := hstep (PCA.k : ℕ → ℕ) 0 hv (fun d hd => by
      rw [hcomp d (PCA.k : ℕ) (hqk d hd)]
      simp)
    rw [← Kleene.k1_app, this]
    exact Part.mem_some _
  · have hv : selEl 0 (natEl 1) = PCA.kI (ℕ → ℕ) := selEl_natEl_ne (by omega)
    have := hstep (PCA.kI (ℕ → ℕ)) 1 hv (fun d hd => by
      rw [hcomp d (PCA.kI ℕ) (hqkI d hd)]
      simp [kI_ne_k_nat])
    rw [← Kleene.k1_app, this]
    exact Part.mem_some _

/-- **No applicative morphism `K₂ → K₁` decides.** -/
theorem not_decides (δ : AppMorphism (ℕ → ℕ) ℕ) : ¬ δ.Decides := fun h =>
  no_separatesBits_morphism δ (separatesBits_of_decides h)

theorem pcaLeD_kleene : PCALeD ℕ (ℕ → ℕ) := ⟨kOneToTwo, kOneToTwo_decides⟩

theorem not_pcaLeD_kleene : ¬ PCALeD (ℕ → ℕ) ℕ := by
  rintro ⟨δ, hδ⟩
  exact not_decides δ hδ

/-- **`K₁ < K₂`**: Kleene's first algebra precedes the second in the informative order, and not
conversely. -/
theorem kleene_strict : PCALeD ℕ (ℕ → ℕ) ∧ ¬ PCALeD (ℕ → ℕ) ℕ :=
  ⟨pcaLeD_kleene, not_pcaLeD_kleene⟩

end KleeneTwo

end Realizability
