/-
**Applicative morphisms of partial combinatory algebras, and the morphism `K₁ → K₂`.**

Longley's programme organises computability as the theory of partial combinatory algebras and of
the *applicative morphisms* between them: a morphism `A → B` does not send an element to an
element, but to a nonempty set of elements of `B` that represent it, and a single element of `B`
must track the application uniformly.

* `Realizability.AppMorphism` — the structure: a total relation `map`, and a `realizer` such that
  `realizer · b · b'` represents `a · a'` whenever `b` represents `a`, `b'` represents `a'` and
  `a · a'` is defined;
* `Realizability.AppMorphism.id` — the identity morphism of any PCA, realized by `λ x y. x y`
  from combinatory completeness;
* `Realizability.KleeneTwo.kOneToTwo` — **the morphism from Kleene's first algebra to Kleene's
  second**: a number `n` is represented by the constant function with value `n`, and the realizer
  is the canonical associate of the operation that reads its two arguments at `0` and runs the
  first, as a partial recursive code, on the second.

The morphism is the concrete link between the two poles of the picture: number realizability
lands inside function realizability.
-/

import Start.KleeneTwo
import Start.PCAKleene

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

namespace Realizability

/-- An **applicative morphism** `A → B`: a total relation `map` assigning to each element of `A`
a nonempty set of elements of `B` representing it, and a single element `realizer` of `B` that
tracks application. -/
structure AppMorphism (A B : Type u) [PCA A] [PCA B] where
  /-- `map a b` : the element `b` of `B` represents the element `a` of `A`. -/
  map : A → B → Prop
  /-- Every element of `A` has a representative. -/
  map_nonempty : ∀ a, ∃ b, map a b
  /-- The element of `B` tracking the application of `A`. -/
  realizer : B
  /-- The realizer applied to one argument is always defined. -/
  realizer_dom : ∀ b, (PCA.app realizer b).Dom
  /-- The realizer tracks application: it maps representatives of `a` and `a'` to a
  representative of `a · a'`. -/
  realizer_app : ∀ (a a' : A) (b b' : B), map a b → map a' b' → ∀ c ∈ PCA.app a a',
    ∃ d, map c d ∧ d ∈ (Part.some realizer ⬝ Part.some b) ⬝ Part.some b'

namespace AppMorphism

variable (A : Type u) [PCA A]

/-- The identity applicative morphism, realized by `λ x y. x y`. -/
noncomputable def id : AppMorphism A A where
  map a b := a = b
  map_nonempty a := ⟨a, rfl⟩
  realizer := PCA.lam2 ((Expr.var 0).app (Expr.var 1))
  realizer_dom b := by
    have h := PCA.lam2_app_dom ((Expr.var 0).app (Expr.var 1)) b
    simpa [papp] using h
  realizer_app a a' b b' hb hb' c hc := by
    cases hb
    cases hb'
    refine ⟨c, rfl, ?_⟩
    refine PCA.lam2_app_app ((Expr.var 0).app (Expr.var 1)) a a' c ?_
    simpa [papp] using hc

/-- The composite of two applicative morphisms: a representative of `a` in `C` is a
representative of a representative of `a` in `B`, and the realizer is
`λ x y. t (t e x) y`, where `t` is the realizer of the second morphism and `e` a representative
of the realizer of the first. -/
noncomputable def comp {A B C : Type u} [PCA A] [PCA B] [PCA C]
    (γ : AppMorphism A B) (δ : AppMorphism B C) : AppMorphism A C where
  map a c := ∃ b, γ.map a b ∧ δ.map b c
  map_nonempty a := by
    obtain ⟨b, hb⟩ := γ.map_nonempty a
    obtain ⟨c, hc⟩ := δ.map_nonempty b
    exact ⟨c, b, hb, hc⟩
  realizer := PCA.lam2 (((Expr.const δ.realizer).app
      (((Expr.const δ.realizer).app
        (Expr.const (δ.map_nonempty γ.realizer).choose)).app (Expr.var 0))).app (Expr.var 1))
  realizer_dom c := by
    have h := PCA.lam2_app_dom (((Expr.const δ.realizer).app
      (((Expr.const δ.realizer).app
        (Expr.const (δ.map_nonempty γ.realizer).choose)).app (Expr.var 0))).app (Expr.var 1)) c
    simpa [papp] using h
  realizer_app a a' c c' hc hc' v hv := by
    obtain ⟨b, hb, hbc⟩ := hc
    obtain ⟨b', hb', hb'c'⟩ := hc'
    obtain ⟨d, hvd, hd⟩ := γ.realizer_app a a' b b' hb hb' v hv
    rw [papp_some_some, papp_some_right, Part.mem_bind_iff] at hd
    obtain ⟨p, hp, hd⟩ := hd
    have hre : δ.map γ.realizer (δ.map_nonempty γ.realizer).choose :=
      (δ.map_nonempty γ.realizer).choose_spec
    obtain ⟨q, hq, hqmem⟩ :=
      δ.realizer_app γ.realizer b (δ.map_nonempty γ.realizer).choose c hre hbc p hp
    obtain ⟨w, hw, hwmem⟩ := δ.realizer_app p b' q c' hq hb'c' d hd
    refine ⟨w, ⟨d, hvd, hw⟩, ?_⟩
    refine PCA.lam2_app_app _ c c' w ?_
    have hmono : (Part.some δ.realizer ⬝ Part.some q) ⬝ Part.some c'
        ≤ (Part.some δ.realizer ⬝
            ((Part.some δ.realizer ⬝ Part.some (δ.map_nonempty γ.realizer).choose)
              ⬝ Part.some c)) ⬝ Part.some c' :=
      papp_mono (papp_mono le_rfl (some_le_of_mem hqmem)) le_rfl
    simpa [papp] using hmono w hwmem

end AppMorphism

/-! ### From `K₁` to `K₂` -/

namespace KleeneTwo

open scoped Realizability.Kleene

@[simp] theorem pca_app_eq (α β : ℕ → ℕ) : PCA.app α β = appK α β := rfl

/-- The element of `K₂` representing the number `n`: the constant function with value `n`. -/
def natEl (n : ℕ) : ℕ → ℕ := fun _ => n

open Classical in
/-- The result of running the `a`-th partial recursive code on `b`, with the junk value `0` if
that computation diverges. -/
noncomputable def evalVal (a b : ℕ) : ℕ :=
  if h : (Kleene.natApp a b).Dom then (Kleene.natApp a b).get h else 0

theorem evalVal_of_mem {a b c : ℕ} (h : c ∈ Kleene.natApp a b) : evalVal a b = c := by
  have hdom : (Kleene.natApp a b).Dom := Part.dom_iff_mem.2 ⟨c, h⟩
  rw [evalVal, dif_pos hdom]
  exact (Part.get_eq_iff_mem hdom).2 h

/-- The operation on Baire space that reads its two arguments at `0` and runs the first, as a
partial recursive code, on the second. -/
noncomputable def evalEl (α β : ℕ → ℕ) : ℕ → ℕ := fun _ => evalVal (α 0) (β 0)

theorem cont_evalEl (α : ℕ → ℕ) : Cont (evalEl α) := by
  intro β _
  refine ⟨1, fun β' h => ?_⟩
  simp only [evalEl, h 0 (by omega)]

/-- The element `r · α` of `K₂`, for the realizer `r` of the morphism out of `K₁`. -/
noncomputable def evalStage (α : ℕ → ℕ) : ℕ → ℕ := detAssoc (evalEl α)

theorem cont_evalStage : Cont evalStage := by
  intro α _
  refine ⟨1, fun α' h => ?_⟩
  have hfun : evalEl α' = evalEl α := by
    funext β x
    simp only [evalEl, h 0 (by omega)]
  simp only [evalStage, hfun]

/-- The realizer of the morphism `K₁ → K₂`. -/
noncomputable def evalAssoc : ℕ → ℕ := detAssoc evalStage

theorem appK_evalAssoc (α : ℕ → ℕ) : appK evalAssoc α = Part.some (evalStage α) :=
  appK_detAssoc cont_evalStage α

theorem appK_evalStage (α β : ℕ → ℕ) : appK (evalStage α) β = Part.some (evalEl α β) :=
  appK_detAssoc (cont_evalEl α) β

/-- The realizer computes Turing application on the constant functions. -/
theorem evalAssoc_app {m n c : ℕ} (h : c ∈ Kleene.natApp m n) :
    (Part.some evalAssoc ⬝ Part.some (natEl m)) ⬝ Part.some (natEl n) = Part.some (natEl c) := by
  rw [papp_some_some, pca_app_eq, appK_evalAssoc, papp_some_some, pca_app_eq, appK_evalStage]
  refine congrArg Part.some (funext fun _ => ?_)
  simp only [evalEl, natEl]
  exact evalVal_of_mem h

/-- **Kleene's first algebra maps into Kleene's second**: the constant function with value `n`
represents `n`, and the associate of "run the code read at `0` on the argument read at `0`"
tracks Turing application. -/
noncomputable def kOneToTwo : AppMorphism ℕ (ℕ → ℕ) where
  map n α := α = natEl n
  map_nonempty n := ⟨natEl n, rfl⟩
  realizer := evalAssoc
  realizer_dom b := by
    change (appK evalAssoc b).Dom
    rw [appK_evalAssoc]
    trivial
  realizer_app m n b b' hb hb' c hc := by
    cases hb
    cases hb'
    refine ⟨natEl c, rfl, ?_⟩
    have hc' : c ∈ Kleene.natApp m n := by
      have hk : PCA.app m n = Kleene.natApp m n := Kleene.k1_app m n
      rwa [hk] at hc
    rw [evalAssoc_app hc']
    exact Part.mem_some _

end KleeneTwo

end Realizability
