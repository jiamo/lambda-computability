/-
**A natural numbers object for the modest sets.**

`Start/AssemblyNNO.lean` builds the assembly of natural numbers over a partial combinatory algebra
— `a` realizes `n` when `a` behaves as the `n`-th Church numeral — and proves that it satisfies
Lawvere's universal property in `Asm(A)`.  This module shows that assembly is **modest** as soon as
the algebra has more than one element, so that it lives in the full subcategory of the modest
assemblies and is a natural numbers object there as well.

Modesty is the statement that a single element of the algebra cannot be a numeral for two
different natural numbers.  The separating computation is iterated tagging: taking
`r = λx. pair k x` and `b = k`, the `n`-fold iterate of `r` on `b` is the tower of `n` nested pairs
over `k`, and a numeral for `n` must compute it.  Two towers of different heights are different,
because Church pairing is injective (`Realizability.Assembly.pairEl_inj`) and `k` is not itself a
pair over `k` — the latter is exactly where more than one element is needed
(`Realizability.PCA.k_ne_pairEl_k`); over a one-element algebra every element is a numeral for
every number.

Main definitions:

* `Realizability.nestK` — the tower of nested pairs, the value of the iterated tagging;
* `Realizability.Modest.natModest` — the natural numbers as a modest assembly.

Main results:

* `Realizability.PCA.k_ne_pairEl_k` — over an algebra with more than one element `k` is not a pair
  whose first component is `k`;
* `Realizability.Assembly.modest_natAsm` — **the assembly of natural numbers is modest**;
* `Realizability.Modest.isNNO_natModest` — **the modest assemblies have a natural numbers
  object**, the same one as `Asm(A)`.
-/

import Start.AssemblyNNO
import Start.ModestReflect

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Realizability

variable {A : Type u} [PCA A]

/-! ### `k` is not a pair over `k` -/

namespace PCA

/-- If `k` is its own value at `k`, the algebra has only one element: `k a = k` for every `a`, so
every `a` equals `k`. -/
theorem subsingleton_of_k_app_k (h : PCA.app (PCA.k : A) (PCA.k : A) = Part.some PCA.k)
    (g : A) : g = (PCA.k : A) := by
  have hconst : ∀ y : A, PCA.app (PCA.k : A) y = Part.some PCA.k := by
    intro y
    have h₁ := PCA.k_app_app (A := A) (PCA.k : A) y
    rwa [papp_some_some, h, papp_some_some] at h₁
  have h₂ := PCA.k_app_app (A := A) g g
  rw [papp_some_some, hconst g, papp_some_some, hconst g] at h₂
  exact (Part.some_inj.1 h₂).symm

/-- **Over an algebra with more than one element, `k` is not a Church pair whose first component
is `k`.**  Applying such an equation to `k` would give `k k = k`, which forces the algebra to be a
singleton. -/
theorem k_ne_pairEl_k [Nontrivial A] (X : A) : (PCA.k : A) ≠ PCA.pairEl (PCA.k : A) X := by
  intro h
  have hmem : (PCA.k : A) ∈ Part.some (PCA.pairEl (PCA.k : A) X) ⬝ Part.some (PCA.k : A) :=
    PCA.pairEl_app (PCA.k : A) X (PCA.k : A) _ (by rw [PCA.k_app_app]; exact Part.mem_some _)
  rw [← h, papp_some_some] at hmem
  have hkk : PCA.app (PCA.k : A) (PCA.k : A) = Part.some PCA.k := Part.eq_some_iff.2 hmem
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  exact hab ((subsingleton_of_k_app_k hkk a).trans (subsingleton_of_k_app_k hkk b).symm)

end PCA

/-! ### Towers of nested pairs -/

/-- The tower of `n` nested pairs over `k`: the value of the `n`-fold iterate of the tagging
combinator `λx. pair k x` on `k`. -/
noncomputable def nestK (A : Type u) [PCA A] : ℕ → A
  | 0 => (PCA.k : A)
  | n + 1 => PCA.pairEl (PCA.k : A) (nestK A n)

theorem nestK_mem_iterp (A : Type u) [PCA A] (n : ℕ) :
    nestK A n ∈ iterp (Assembly.tagComb (PCA.k : A)) n (PCA.k : A) := by
  induction n with
  | zero => exact Part.mem_some _
  | succ n ih =>
      rw [iterp_succ]
      exact Part.mem_bind_iff.2 ⟨nestK A n, ih, Assembly.tagComb_app _ _⟩

/-- Towers of different heights are different. -/
theorem nestK_injective [Nontrivial A] : Function.Injective (nestK A) := by
  intro m
  induction m with
  | zero =>
      intro n h
      cases n with
      | zero => rfl
      | succ n => exact absurd h (PCA.k_ne_pairEl_k _)
  | succ m ih =>
      intro n h
      cases n with
      | zero => exact absurd h.symm (PCA.k_ne_pairEl_k _)
      | succ n => exact congrArg Nat.succ (ih ((Assembly.pairEl_inj h).2))

namespace Assembly

/-- **The assembly of natural numbers is modest** over an algebra with more than one element: a
numeral for `n` computes the tower of `n` nested pairs, and towers of different heights
differ. -/
theorem modest_natAsm [Nontrivial A] : (natAsm.{u, u} A).Modest := by
  intro a x y hx hy
  have hx' := hx (tagComb (PCA.k : A)) (PCA.k : A) (nestK A x.down)
    (nestK_mem_iterp A x.down)
  have hy' := hy (tagComb (PCA.k : A)) (PCA.k : A) (nestK A y.down)
    (nestK_mem_iterp A y.down)
  exact ULift.ext _ _ (nestK_injective (Part.mem_unique hx' hy'))

end Assembly

/-! ### The natural numbers object of the modest assemblies -/

namespace Modest

open Assembly

variable [Nontrivial A]

/-- The natural numbers as a modest assembly. -/
noncomputable def natModest (A : Type u) [PCA A] [Nontrivial A] : ModestCat A :=
  ⟨natAsm A, modest_natAsm⟩

/-- Zero, as a morphism of modest assemblies. -/
noncomputable def natZeroModest (A : Type u) [PCA A] [Nontrivial A] :
    unitModest A ⟶ natModest A :=
  ObjectProperty.homMk (natZero A)

/-- The successor, as a morphism of modest assemblies. -/
noncomputable def natSuccModest (A : Type u) [PCA A] [Nontrivial A] :
    natModest A ⟶ natModest A :=
  ObjectProperty.homMk (natSucc A)

/-- **The modest assemblies have a natural numbers object**: the assembly of natural numbers, with
the same zero and successor as in `Asm(A)`.  The inclusion is full, so definition by iteration in
the subcategory is definition by iteration in `Asm(A)`. -/
theorem isNNO_natModest (A : Type u) [PCA A] [Nontrivial A] :
    IsNNO (natZeroModest A) (natSuccModest A) := by
  refine ⟨⟨isTerminalUnitModest⟩, fun X q f => ?_⟩
  obtain ⟨u, ⟨h₀, hs⟩, huniq⟩ := (isNNO_natAsm.{u, u} A).existsUnique_rec X.obj q.hom f.hom
  refine ⟨ObjectProperty.homMk u, ⟨ObjectProperty.hom_ext _ h₀, ObjectProperty.hom_ext _ hs⟩, ?_⟩
  rintro m ⟨hm₀, hms⟩
  exact ObjectProperty.hom_ext _
    (huniq m.hom ⟨congrArg (fun k : unitModest A ⟶ X => k.hom) hm₀,
      congrArg (fun k : natModest A ⟶ X => k.hom) hms⟩)

end Modest

end Realizability
