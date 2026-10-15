# M23-ID-TYPES — identity types for categories with attributes

**Status:** DONE_STRONG.

Module: `Start/CwaId.lean` (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`
only — see `docs/goal/evidence/M29-PART1-axioms.txt`).

## Statements

For a category with attributes `T` (`Start/Cwa.lean`):

* `Cwa.wk A = A[p]`, `Cwa.ext2 Γ A = Γ.A.A⁺` (two variables of type `A`), `Cwa.diag A : Γ.A ⟶ Γ.A.A⁺`
  (the generic term `var A`), `Cwa.liftLift σ A : Δ.A[σ].A[σ]⁺ ⟶ Γ.A.A⁺` (`σ` extended past both
  variables, by the pullback property), `Cwa.reflMap r : Γ.A ⟶ Γ.A.A⁺.I` (substitution along a term
  over the diagonal).
* `Cwa.IdStruct T` (first exit criterion):
  * `Id A : Ty (Γ.A.A⁺)` — formation;
  * `refl A : Tm (Γ.A) (Id A)[diag A]` — reflexivity;
  * `J M d : Tm (Γ.A.A⁺.Id A) M` for a motive `M` and `d : Tm (Γ.A) M[reflMap (refl A)]`;
  * `J_comp : (J M d)[reflMap (refl A)] = d` — the computation rule;
  * `Id_sub`, `refl_sub`, `J_sub` — formation, reflexivity and `J` commute with substitution along
    `σ : Δ ⟶ Γ` (transported along `Id_sub` where needed).
* `Cwa.IdStruct.UIP I` (second exit criterion): for every `Γ` and `A`, the type `Id (Id A)` over
  `Γ, x y : A, q r : Id x y` has a term (uniqueness of identity proofs as a property of the
  structure).

## Instance

* `CwaType.idStruct : Cwa.IdStruct CwaType.families` — in the families model, `Id A ⟨⟨x, a⟩, b⟩` is
  `ULift (PLift (a = b))`; `refl` is `rfl`; `J` is defined pointwise by transporting `d` along the
  equation `reflMap (refl A) e.1.1 = e` (every element of the identity type is reflexivity up to
  this equation, `reflMap_eq_of`). The computation and substitution laws are proved pointwise via
  `secEquiv` (terms of the families model are dependent functions).
* `CwaType.idStruct_UIP : CwaType.idStruct.UIP` — the identity types of the families model are
  subsingletons.

No existing module was changed.
