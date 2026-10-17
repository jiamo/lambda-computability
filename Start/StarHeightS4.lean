import Start.StarHeightHCore

/-!
# `S₄` over the `S₃`-core

* `S4Klein.kleinHom : Perm (Fin 4) →* Perm (Fin 3)`: the action of `S₄` on the three pairings
  `{{0, j + 1}, rest}` of `{0, 1, 2, 3}`.  It is surjective, and its kernel is the Klein four
  group `V₄ = {x ↦ x xor a}`, which is abelian.
* `height_one_S4_of_core`: if the `S₃`-core holds, every language recognized by `S₄` has
  generalized star height at most one.

All finite checks are `decide` on statements about `Fin 4`-valued tuples, never on `Perm (Fin 4)`.
-/

namespace GeneralizedStarHeight

universe u

namespace S4Klein

/-- `pidx u v` is the index `j` of the pairing `{{0, j + 1}, rest}` in which `{u, v}` is a block
(for `u ≠ v`). -/
def pidx (u v : Fin 4) : Fin 3 :=
  ![![0, 0, 1, 2], ![0, 0, 2, 1], ![1, 2, 0, 0], ![2, 1, 0, 0]] u v

/-- A bijection of `{0, 1, 2, 3}` maps pairings to pairings. -/
lemma pidx_equivariant : ∀ a b c d u v : Fin 4, ([a, b, c, d].Nodup ∧ u ≠ v) →
    pidx (![a, b, c, d] u) (![a, b, c, d] v) = pidx a (![a, b, c, d] (Fin.succ (pidx u v))) := by
  decide

lemma pidx_zero_succ : ∀ j : Fin 3, pidx 0 j.succ = j := by decide

/-- The Klein four group acting by `xor`. -/
def kx (a i : Fin 4) : Fin 4 := ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a i

lemma ker_vals : ∀ a b c d : Fin 4, ([a, b, c, d].Nodup ∧
    pidx a b = 0 ∧ pidx a c = 1 ∧ pidx a d = 2) → (b = kx a 1 ∧ c = kx a 2 ∧ d = kx a 3) := by
  decide

lemma kx_zero : ∀ a : Fin 4, kx a 0 = a := by decide

lemma kx_comm : ∀ a b i : Fin 4, kx a (kx b i) = kx b (kx a i) := by decide

lemma perm_eq_vec (σ : Equiv.Perm (Fin 4)) : (σ : Fin 4 → Fin 4) = ![σ 0, σ 1, σ 2, σ 3] := by
  funext i
  fin_cases i <;> rfl

lemma nodup_vals (σ : Equiv.Perm (Fin 4)) : [σ 0, σ 1, σ 2, σ 3].Nodup := by
  simp [σ.injective.eq_iff]

/-- The action on pairings. -/
def act (σ : Equiv.Perm (Fin 4)) (j : Fin 3) : Fin 3 := pidx (σ 0) (σ j.succ)

lemma act_one (j : Fin 3) : act 1 j = j := pidx_zero_succ j

lemma act_mul (σ τ : Equiv.Perm (Fin 4)) (j : Fin 3) : act (σ * τ) j = act σ (act τ j) := by
  have hne : τ 0 ≠ τ j.succ := τ.injective.ne (Fin.succ_ne_zero j).symm
  have h := pidx_equivariant (σ 0) (σ 1) (σ 2) (σ 3) (τ 0) (τ j.succ) ⟨nodup_vals σ, hne⟩
  rw [← perm_eq_vec σ] at h
  exact h

/-- `S₄ → S₃`. -/
def kleinHom : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) where
  toFun σ :=
    { toFun := act σ
      invFun := act σ⁻¹
      left_inv := fun j => by rw [← act_mul, inv_mul_cancel, act_one]
      right_inv := fun j => by rw [← act_mul, mul_inv_cancel, act_one] }
  map_one' := Equiv.ext act_one
  map_mul' σ τ := Equiv.ext (act_mul σ τ)

lemma kleinHom_apply (σ : Equiv.Perm (Fin 4)) (j : Fin 3) : kleinHom σ j = act σ j := rfl

lemma kleinHom_surjective : Function.Surjective kleinHom := by
  intro τ
  refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), Equiv.ext fun j => ?_⟩
  rw [kleinHom_apply, act, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply, pidx_zero_succ]

lemma mem_ker_apply {σ : Equiv.Perm (Fin 4)} (hσ : σ ∈ kleinHom.ker) (i : Fin 4) :
    σ i = kx (σ 0) i := by
  have h : ∀ j, act σ j = j := fun j => by
    have := congrArg (fun π : Equiv.Perm (Fin 3) => π j) (MonoidHom.mem_ker.mp hσ)
    simpa [kleinHom_apply] using this
  obtain ⟨h1, h2, h3⟩ := ker_vals (σ 0) (σ 1) (σ 2) (σ 3) ⟨nodup_vals σ, h 0, h 1, h 2⟩
  fin_cases i
  · exact (kx_zero _).symm
  · exact h1
  · exact h2
  · exact h3

/-- The kernel `V₄` is abelian. -/
lemma ker_comm : ∀ x ∈ kleinHom.ker, ∀ y ∈ kleinHom.ker, x * y = y * x := by
  intro x hx y hy
  ext i
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [mem_ker_apply hx, mem_ker_apply hy, mem_ker_apply hy (x i), mem_ker_apply hx i, kx_comm]

/-- `S₄ ⧸ V₄ ≃* S₃`. -/
noncomputable def quotEquiv : Equiv.Perm (Fin 4) ⧸ kleinHom.ker ≃* Equiv.Perm (Fin 3) :=
  QuotientGroup.quotientKerEquivOfSurjective _ kleinHom_surjective

end S4Klein

/-- **`S₄` over the `S₃`-core.** If the `S₃`-core holds, every language recognized by `S₄` has
generalized star height at most one. -/
theorem height_one_S4_of_core (hcore : HCoreHeightOne (Equiv.Perm (Fin 3))) {Alphabet : Type u}
    [Finite Alphabet] (T : FreeMonoid Alphabet →* Equiv.Perm (Fin 4)) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  height_one_of_abelian_normal_of_core_equiv S4Klein.kleinHom.ker S4Klein.ker_comm
    S4Klein.quotEquiv hcore T F

end GeneralizedStarHeight
