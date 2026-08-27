/-
**Closure of a universe under the dependent product is genuine extra structure.**

`Start/CwaUniverse.lean` separates two pieces of data on a category with attributes:

* `Cwa.Universe.SmallPi` — dependent products may be formed over the type named by a code, the
  product itself being an arbitrary type of the model;
* `Cwa.Universe.PiClosed` — the product of two *small* types is small again, i.e. there is a code
  `code a b` with `El (code a b) = Pi a (El b)`.

Every model whose type former is defined over all types has the first (`smallPiOfWeakPi`).  This
file shows that it does **not** have the second in general: in the standard model of families of
types (`Start/CwaType.lean`) the two-element universe naming `PEmpty` and `Bool` has dependent
products over its small types — the ambient model has all of them — but is not closed under them,
because `Bool → Bool` has four elements and the universe names no such type.

* `CwaTypeNotClosed.twoUniverse` — the universe with two codes in the standard model;
* `CwaTypeNotClosed.twoSmallPi` — its dependent products over small types;
* `CwaTypeNotClosed.not_piClosed` — **there is no `PiClosed` structure on it**;
* `CwaTypeNotClosed.not_codePi`, `CwaTypeNotClosed.not_codeSigma` — nor even the weaker
  product-of-codes and sum-of-codes data used by the interpretation of the syntax.

So the closure asked for by `PiClosed` (and, in the weaker form used by the interpretation of the
syntax, by `Cwa.Universe.CodePi`) is a genuine requirement on the universe object, not a
consequence of the ambient model having dependent products.
-/

import Start.CwaType
import Start.CwaUniverse
import Start.CwaCodePi
import Start.CwaCodeSigma
import Mathlib.Data.Fintype.BigOperators

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory

namespace CwaTypeNotClosed

open CwaType

/-- The two types named by the codes of `twoUniverse`: `PEmpty` and `Bool`. -/
def dec : Bool → Type u
  | true => ULift.{u} Bool
  | false => PEmpty.{u + 1}

/-- A term of the type of codes, from a family of booleans. -/
def codeTm {Γ : Type u} (f : Γ → Bool) :
    Cwa.Tm families.{u} Γ (fun _ => ULift.{u} Bool) :=
  ⟨↾fun x => ⟨x, ULift.up (f x)⟩, rfl⟩

/-- The boolean named by a code. -/
def bitOf {Γ : Type u} (a : Cwa.Tm families.{u} Γ (fun _ => ULift.{u} Bool)) (x : Γ) : Bool :=
  (a.1 x).2.down

@[simp] theorem bitOf_codeTm {Γ : Type u} (f : Γ → Bool) (x : Γ) : bitOf (codeTm f) x = f x := rfl

/-- **A universe with two codes in the standard model of families of types.**  A code in a
context `Γ` is a family of booleans, naming `Bool` or `PEmpty` pointwise. -/
def twoUniverse : Cwa.Universe families.{u} where
  U _ := fun _ => ULift.{u} Bool
  U_sub _ := rfl
  El a := fun x => dec (bitOf a x)
  El_sub := by
    intro Γ Δ σ a
    funext d
    have h := ConcreteCategory.congr_hom (Cwa.tmSub_extend (T := families.{u}) σ a) d
    have h2 : ((families.tmSub σ a).1 d).2 = (a.1 (σ d)).2 :=
      congrArg (fun p : (Σ _ : Γ, ULift.{u} Bool) => p.2) h
    change dec (bitOf a (σ d)) = dec ((families.tmSub σ a).1 d).2.down
    rw [h2]
    rfl

@[simp] theorem twoUniverse_El {Γ : Type u} (a : Cwa.Tm families.{u} Γ (twoUniverse.U Γ)) :
    twoUniverse.El a = fun x => dec (bitOf a x) := rfl

/-- The universe has dependent products over its small types: they are those of the ambient
model, the dependent function types. -/
noncomputable def twoSmallPi : Cwa.Universe.SmallPi twoUniverse.{u} :=
  Cwa.Universe.smallPiOfWeakPi _ piStruct.toWeakPiStruct

@[simp] theorem twoSmallPi_Pi {Γ : Type u} (a : Cwa.Tm families.{u} Γ (twoUniverse.U Γ))
    (B : families.Ty (families.ext Γ (twoUniverse.El a))) :
    twoSmallPi.Pi a B = fun x => (y : dec (bitOf a x)) → B ⟨x, y⟩ := rfl

/-- **The universe of `twoUniverse` is not closed under the dependent products it has.**  A code
names `Bool` or `PEmpty`, but the product of the constant family `Bool` over `Bool` is the type
`Bool → Bool`, which has four elements; so no code decodes to it. -/
theorem not_piClosed : IsEmpty (Cwa.Universe.PiClosed twoUniverse.{u} twoSmallPi.{u}) := by
  constructor
  intro pc
  set Γ : Type u := PUnit.{u + 1} with hΓ
  set a : Cwa.Tm families.{u} Γ (twoUniverse.U Γ) := codeTm (fun _ => true) with ha
  set b : Cwa.Tm families.{u} (families.ext Γ (twoUniverse.El a))
      (twoUniverse.U (families.ext Γ (twoUniverse.El a))) := codeTm (fun _ => true) with hb
  have h' : dec (bitOf (pc.code a b) PUnit.unit) = (ULift.{u} Bool → ULift.{u} Bool) :=
    congrFun (pc.El_code a b) PUnit.unit
  cases hbit : bitOf (pc.code a b) PUnit.unit with
  | false =>
      rw [hbit] at h'
      exact (cast h'.symm (fun y => y)).elim
  | true =>
      rw [hbit] at h'
      have hcard : Fintype.card (ULift.{u} Bool) = Fintype.card (ULift.{u} Bool → ULift.{u} Bool) :=
        Fintype.card_congr (Equiv.cast (by rw [← h']; rfl))
      rw [Fintype.card_fun] at hcard
      simp at hcard

/-! ### The weaker interface `CodePi` fails as well -/

/-- The code naming `Bool` in the one-point context. -/
def aCode : Cwa.Tm families.{u} PUnit.{u + 1} (twoUniverse.{u}.U PUnit.{u + 1}) :=
  codeTm (fun _ => true)

/-- The code naming `Bool` in the context extended by the decoding of `aCode`. -/
def bCode : Cwa.Tm families.{u} (families.ext PUnit.{u + 1} (twoUniverse.{u}.El aCode.{u}))
    (twoUniverse.{u}.U (families.ext PUnit.{u + 1} (twoUniverse.{u}.El aCode.{u}))) :=
  codeTm (fun _ => true)

/-- Three pairwise distinct elements do not fit into the two-element type. -/
theorem no_three_distinct (x y z : ULift.{u} Bool) (h₁ : x ≠ y) (h₂ : x ≠ z) (h₃ : y ≠ z) :
    False := by
  obtain ⟨x⟩ := x; obtain ⟨y⟩ := y; obtain ⟨z⟩ := z
  simp only [ne_eq, ULift.up.injEq] at h₁ h₂ h₃
  revert h₁ h₂ h₃
  revert x y z
  decide

/-- Three pairwise distinct elements do not fit into a type named by a code: a code names
either the empty type or the two-element type. -/
theorem no_three_in_dec {c : Bool} (x y z : dec.{u} c) (h₁ : x ≠ y) (h₂ : x ≠ z) (h₃ : y ≠ z) :
    False := by
  cases c with
  | false => exact x.elim
  | true => exact no_three_distinct x y z h₁ h₂ h₃

/-- **The universe of `twoUniverse` does not even carry the weaker product data
`Cwa.Universe.CodePi`.**  There abstraction is only asked to be a section of application, but that
already makes it injective, and it would embed the four dependent functions `Bool → Bool` into the
at most two terms of the type named by any code. -/
theorem not_codePi : IsEmpty (Cwa.Universe.CodePi twoUniverse.{u}) := by
  constructor
  intro Q
  have hinj : Function.Injective (Q.lam (a := aCode.{u}) (b := bCode.{u})) := by
    intro x y h
    rw [← Q.app_lam x, ← Q.app_lam y, h]
  -- the composite sending a function `Bool → Bool` to the value at the point of its abstraction
  set w : (((_ : PUnit.{u + 1}) × ULift.{u} Bool) → ULift.{u} Bool) →
      dec.{u} (bitOf (Q.code aCode.{u} bCode.{u}) PUnit.unit) :=
    fun f => secEquiv _ (Q.lam (a := aCode.{u}) (b := bCode.{u})
      ((secEquiv (twoUniverse.El bCode.{u})).symm f)) PUnit.unit with hw
  have hwinj : Function.Injective w := by
    intro f g h
    rw [hw] at h
    have h' : secEquiv _ (Q.lam (a := aCode.{u}) (b := bCode.{u})
        ((secEquiv (twoUniverse.El bCode.{u})).symm f))
      = secEquiv _ (Q.lam (a := aCode.{u}) (b := bCode.{u})
        ((secEquiv (twoUniverse.El bCode.{u})).symm g)) := by
      funext x
      obtain ⟨⟩ := x
      exact h
    have h'' := hinj ((secEquiv _).injective h')
    exact (secEquiv (twoUniverse.El bCode.{u})).symm.injective h''
  have h13 : w (fun _ => ULift.up true) ≠ w (fun p => p.2) := by
    intro h
    have := hwinj h
    have := congrFun this ⟨PUnit.unit, ULift.up false⟩
    exact absurd this (by simp)
  have h23 : w (fun _ => ULift.up false) ≠ w (fun p => p.2) := by
    intro h
    have := hwinj h
    have := congrFun this ⟨PUnit.unit, ULift.up true⟩
    exact absurd this (by simp)
  have h12 : w (fun _ => ULift.up true) ≠ w (fun _ => ULift.up false) := by
    intro h
    have := hwinj h
    have := congrFun this ⟨PUnit.unit, ULift.up true⟩
    exact absurd this (by simp)
  exact no_three_in_dec _ _ _ h12 h13 h23

/-! ### The universe is not closed under dependent sums either -/

/-- **The universe of `twoUniverse` does not carry the sum-of-codes data
`Cwa.Universe.CodeSigma`.**  Pairing would make the context extended twice — by `Bool` and then
by `Bool` again, four points — isomorphic to the context extended by a single code, of at most
two points. -/
theorem not_codeSigma : IsEmpty (Cwa.Universe.CodeSigma twoUniverse.{u}) := by
  constructor
  intro S
  have hinj : Function.Injective
      (fun e : families.ext (families.ext PUnit.{u + 1} (twoUniverse.El aCode.{u}))
            (twoUniverse.El bCode.{u}) =>
        Equiv.uniqueSigma (fun x : PUnit.{u + 1} => twoUniverse.El (S.code aCode.{u} bCode.{u}) x)
          ((S.pair aCode.{u} bCode.{u}).toEquiv e)) :=
    (Equiv.uniqueSigma _).injective.comp (S.pair aCode.{u} bCode.{u}).toEquiv.injective
  set e₁ : families.ext (families.ext PUnit.{u + 1} (twoUniverse.El aCode.{u}))
      (twoUniverse.El bCode.{u}) := ⟨⟨PUnit.unit, ULift.up true⟩, ULift.up true⟩ with he₁
  set e₂ : families.ext (families.ext PUnit.{u + 1} (twoUniverse.El aCode.{u}))
      (twoUniverse.El bCode.{u}) := ⟨⟨PUnit.unit, ULift.up true⟩, ULift.up false⟩ with he₂
  set e₃ : families.ext (families.ext PUnit.{u + 1} (twoUniverse.El aCode.{u}))
      (twoUniverse.El bCode.{u}) := ⟨⟨PUnit.unit, ULift.up false⟩, ULift.up true⟩ with he₃
  have h₁₂ : e₁ ≠ e₂ := by
    rw [he₁, he₂]
    intro h
    exact absurd (congrArg (fun p => (p.2 : ULift.{u} Bool).down) h) (by simp)
  have h₁₃ : e₁ ≠ e₃ := by
    rw [he₁, he₃]
    intro h
    exact absurd (congrArg (fun p => (p.1.2 : ULift.{u} Bool).down) h) (by simp)
  have h₂₃ : e₂ ≠ e₃ := by
    rw [he₂, he₃]
    intro h
    exact absurd (congrArg (fun p => (p.1.2 : ULift.{u} Bool).down) h) (by simp)
  exact no_three_in_dec _ _ _ (fun h => h₁₂ (hinj h)) (fun h => h₁₃ (hinj h))
    (fun h => h₂₃ (hinj h))

end CwaTypeNotClosed
