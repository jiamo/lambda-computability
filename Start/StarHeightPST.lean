import Start.StarHeightPSTLanguage

/-!
# Reductions for the PST candidate

* `PST.recog : FreeMonoid AB →* Perm (Fin 4) × Multiplicative (ZMod 2)` and
  `PST.LPST_recognized`: `L_PST` is recognized by `S₄ × Z₂`.
* `height_one_prod`: a language recognized by `G × H` is a Boolean combination of languages
  recognized by `G` and by `H`.
* `PST.pst_candidate_height_one_of_S4`, `PST.pst_candidate_height_one_of_core`: if every language
  recognized by `S₄` has height at most one (for instance if the `S₃`-core holds), then so has
  `L_PST`.
* `PST.pst_candidate_iff`: `L_PST` has height at most one iff the single `S₃` coset count
  `K = {w | (hcount ρ₃ 1 b w + hcount ρ₃ (1 2) b w) is even}` has (`ρ₃ a = (0 1)`, `ρ₃ b = (0 2)`):
  this count is the number of `b` read in the state `0`.

The `S₄ × Z₂` recognizer was found by a computer search; its correctness is the finite check
`decode_step_a`, `decode_step_b` on `Fin 4`-valued pairs.
-/

namespace GeneralizedStarHeight

universe u

/-- **Products.** If every language recognized by `G` and every language recognized by `H` has
height at most one, so has every language recognized by `G × H`. -/
theorem height_one_prod {A : Type u} {G H : Type} [Monoid G] [Monoid H] [Finite G] [Finite H]
    (hG : ∀ (T : FreeMonoid A →* G) (F : Set G), HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1)
    (hH : ∀ (T : FreeMonoid A →* H) (F : Set H), HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1)
    (T : FreeMonoid A →* G × H) (F : Set (G × H)) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language A) = ⨆ g : F,
      ({w | (MonoidHom.fst G H).comp T (FreeMonoid.ofList w) ∈ ({g.1.1} : Set G)} ⊓
        {w | (MonoidHom.snd G H).comp T (FreeMonoid.ofList w) ∈ ({g.1.2} : Set H)}) := by
    ext w
    constructor
    · intro hw
      exact Language.mem_iSup.mpr ⟨⟨_, hw⟩, rfl, rfl⟩
    · intro hw
      obtain ⟨g, h1, h2⟩ := Language.mem_iSup.mp hw
      have h1' : (T (FreeMonoid.ofList w)).1 = g.1.1 := h1
      have h2' : (T (FreeMonoid.ofList w)).2 = g.1.2 := h2
      show T (FreeMonoid.ofList w) ∈ F
      rw [Prod.ext h1' h2']
      exact g.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun g => (hG _ _).inter (hH _ _)

namespace PST

open AB

/-! ### The recognizer -/

/-- `(2 3)`. -/
def permA : Equiv.Perm (Fin 4) := ⟨![0, 1, 3, 2], ![0, 1, 3, 2], by decide, by decide⟩

/-- `(0 1 2 3)`. -/
def permB : Equiv.Perm (Fin 4) := ⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩

/-- The images of the letters. -/
def gen : AB → Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)
  | a => (permA, 1)
  | b => (permB, Multiplicative.ofAdd 1)

/-- **The recognizer** `{a, b}* → S₄ × Z₂`. -/
def recog : FreeMonoid AB →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2) := FreeMonoid.lift gen

/-- The state, from `(σ⁻¹ 0, σ⁻¹ 3)`. -/
def stTab (u v : Fin 4) : Fin 3 :=
  ![![0, 2, 1, 0], ![2, 0, 0, 1], ![1, 0, 0, 2], ![0, 1, 2, 0]] u v

/-- The parity offset, from `(σ⁻¹ 0, σ⁻¹ 3)`. -/
def parTab (u v : Fin 4) : ZMod 2 :=
  ![![0, 1, 0, 0], ![1, 0, 1, 1], ![0, 1, 0, 0], ![0, 1, 0, 0]] u v

/-- The pair (state, parity of `b` read in `0`) of the automaton. -/
def stepZ (st : Fin 3 × ZMod 2) (x : AB) : Fin 3 × ZMod 2 :=
  (move st.1 x, st.2 + if x = b ∧ st.1 = 0 then 1 else 0)

/-- Decoding from `(σ⁻¹ 0, σ⁻¹ 3, z)`. -/
def decodeUV (u v : Fin 4) (z : ZMod 2) : Fin 3 × ZMod 2 := (stTab u v, parTab u v + z)

/-- Decoding an element of `S₄ × Z₂`. -/
def decode (g : Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) : Fin 3 × ZMod 2 :=
  decodeUV (g.1.symm 0) (g.1.symm 3) (Multiplicative.toAdd g.2)

lemma decode_step_a : ∀ (u v : Fin 4) (z : ZMod 2), u ≠ v →
    decodeUV (![0, 1, 3, 2] u) (![0, 1, 3, 2] v) (z + 0) = stepZ (decodeUV u v z) a := by
  decide

lemma decode_step_b : ∀ (u v : Fin 4) (z : ZMod 2), u ≠ v →
    decodeUV (![3, 0, 1, 2] u) (![3, 0, 1, 2] v) (z + 1) = stepZ (decodeUV u v z) b := by
  decide

lemma decode_mul (g : Equiv.Perm (Fin 4) × Multiplicative (ZMod 2)) (x : AB) :
    decode (g * gen x) = stepZ (decode g) x := by
  have hne : g.1.symm 0 ≠ g.1.symm 3 := g.1.symm.injective.ne (by decide)
  cases x with
  | a => exact decode_step_a _ _ _ hne
  | b => exact decode_step_b _ _ _ hne

lemma stateOf_append_single (s : Fin 3) (w : List AB) (x : AB) :
    stateOf s (w ++ [x]) = move (stateOf s w) x := by
  rw [stateOf_append]; rfl

lemma b0count_append_single (s : Fin 3) (w : List AB) (x : AB) :
    b0count s (w ++ [x]) = b0count s w + if x = b ∧ stateOf s w = 0 then 1 else 0 := by
  rw [b0count_append]
  simp [b0count]

lemma decode_recog (w : List AB) :
    decode (recog (FreeMonoid.ofList w)) = (stateOf 0 w, (b0count 0 w : ZMod 2)) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, recog,
        FreeMonoid.lift_eval_of, ← recog, decode_mul, ih, stateOf_append_single,
        b0count_append_single]
      simp only [stepZ]
      push_cast
      rfl

lemma mem_LPST (w : List AB) : w ∈ LPST ↔ stateOf 0 w = 0 ∧ b0count 0 w % 2 = 0 := by
  rw [LPST_eq]
  rfl

/-- **`L_PST` is recognized by `S₄ × Z₂`.** -/
theorem LPST_recognized :
    LPST = {w | recog (FreeMonoid.ofList w) ∈ {g | decode g = ((0 : Fin 3), (0 : ZMod 2))}} := by
  ext w
  show w ∈ LPST ↔ decode (recog (FreeMonoid.ofList w)) = _
  rw [mem_LPST, decode_recog, Prod.mk.injEq, ← Nat.cast_zero (R := ZMod 2),
    ZMod.natCast_eq_natCast_iff', Nat.zero_mod]

/-! ### The reductions -/

/-- **`L_PST` from `S₄`.** -/
theorem pst_candidate_height_one_of_S4 (h : ∀ {A : Type} [Finite A] (T : FreeMonoid A →* Equiv.Perm (Fin 4)) (F : Set (Equiv.Perm (Fin 4))),
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1) : HasHeightAtMost LPST 1 := by
  rw [LPST_recognized]
  exact height_one_prod (fun T F => h T F)
    (fun T F => height_one_of_comm (fun x y => mul_comm x y) T F) recog _

/-- **`L_PST` from the `S₃`-core.** -/
theorem pst_candidate_height_one_of_core (hcore : HCoreHeightOne (Equiv.Perm (Fin 3))) :
    HasHeightAtMost LPST 1 :=
  pst_candidate_height_one_of_S4 fun T F => height_one_S4_of_core hcore T F

/-! ### The `S₃` walk and the single coset count -/

/-- `ρ₃ a = (0 1)`, `ρ₃ b = (0 2)`. -/
def rho3 : AB → Equiv.Perm (Fin 3)
  | a => Equiv.swap 0 1
  | b => Equiv.swap 0 2

/-- The walk in `S₃`. -/
def walk3 : FreeMonoid AB →* Equiv.Perm (Fin 3) := FreeMonoid.lift rho3

lemma rho3_symm_apply : ∀ (x : AB) (s : Fin 3), (rho3 x).symm s = move s x := by
  intro x s
  cases x <;> revert s <;> decide

lemma stateOf_eq_walk3 (s : Fin 3) (w : List AB) :
    stateOf s w = (walk3 (FreeMonoid.ofList w)).symm s := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [stateOf_append_single, ih, FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton,
        walk3, FreeMonoid.lift_eval_of, ← walk3, Equiv.Perm.mul_def, Equiv.symm_trans_apply,
        rho3_symm_apply]

/-- The states form an `S₃`-language of height at most one (`A₃` has prime index). -/
theorem stateOf_height (s : Fin 3) : HasHeightAtMost {w : List AB | stateOf 0 w = s} 1 := by
  have hcomm : ∀ x ∈ alternatingGroup (Fin 3), ∀ y ∈ alternatingGroup (Fin 3), x * y = y * x := by
    intro x hx y hy
    have hc := (alternatingGroup.isMulCommutative_of_card_le_three (α := Fin 3) (by simp)).is_comm.comm
      ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val hc
  have heq : ({w : List AB | stateOf 0 w = s} : Language AB) =
      {w | walk3 (FreeMonoid.ofList w) ∈ {g : Equiv.Perm (Fin 3) | g.symm 0 = s}} := by
    ext w
    show stateOf 0 w = s ↔ _
    rw [stateOf_eq_walk3]
    rfl
  rw [heq]
  exact height_one_of_abelian_prime_index (alternatingGroup (Fin 3)) hcomm
    (p := 2) alternatingGroup.index_eq_two walk3 _

lemma fix_zero_iff : ∀ g : Equiv.Perm (Fin 3),
    (if g.symm 0 = 0 then 1 else 0) = (if g = 1 then 1 else 0) + (if g = Equiv.swap 1 2 then 1 else 0) := by
  decide

/-- The number of `b` read in the state `0` is an `S₃` coset count. -/
lemma b0count_eq_hcount : ∀ (w : List AB) (h : Equiv.Perm (Fin 3)),
    b0count (h.symm 0) w = hcountFrom rho3 1 b h w + hcountFrom rho3 (Equiv.swap 1 2) b h w
  | [], h => by simp [b0count, hcountFrom_nil]
  | x :: w, h => by
      have hmove : move (h.symm 0) x = (h * rho3 x).symm 0 := by
        rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, rho3_symm_apply]
      rw [b0count, hcountFrom_cons, hcountFrom_cons, hmove, b0count_eq_hcount w (h * rho3 x)]
      by_cases hx : x = b
      · have := fix_zero_iff h
        simp only [hx, true_and] at this ⊢
        omega
      · simp [hx]

/-- The single coset count `K`: the number of `b` read in the state `0` is even. -/
def K : Language AB :=
  {w | (hcount rho3 1 b w + hcount rho3 (Equiv.swap 1 2) b w) % 2 = 0}

lemma mem_K (w : List AB) : w ∈ K ↔ b0count 0 w % 2 = 0 := by
  show (hcount rho3 1 b w + hcount rho3 (Equiv.swap 1 2) b w) % 2 = 0 ↔ _
  rw [hcount_eq_hcountFrom, hcount_eq_hcountFrom, ← b0count_eq_hcount w 1]
  rfl

/-- **The smallest open instance.** `L_PST` has height at most one iff the single `S₃` coset count
`K` has. -/
theorem pst_candidate_iff : HasHeightAtMost LPST 1 ↔ HasHeightAtMost K 1 := by
  constructor
  · intro h
    have heq : K = ({w | stateOf 0 w = 0} ⊓ LPST) ⊔
        (({w | stateOf 0 w = 1} ⊓ rightQuot a LPST) ⊔ ({w | stateOf 0 w = 2} ⊓ rightQuot b LPST)) := by
      ext w
      rw [mem_K]
      change b0count 0 w % 2 = 0 ↔ (stateOf 0 w = 0 ∧ w ∈ LPST) ∨
        ((stateOf 0 w = 1 ∧ w ++ [a] ∈ LPST) ∨ (stateOf 0 w = 2 ∧ w ++ [b] ∈ LPST))
      rw [mem_LPST, mem_LPST, mem_LPST, stateOf_append_single, stateOf_append_single,
        b0count_append_single, b0count_append_single]
      generalize stateOf 0 w = s
      fin_cases s <;> simp [move]
    rw [heq]
    exact ((stateOf_height 0).inter h).union (((stateOf_height 1).inter (h.rightQuot a)).union
      ((stateOf_height 2).inter (h.rightQuot b)))
  · intro h
    have heq : LPST = {w | stateOf 0 w = 0} ⊓ K := by
      ext w
      change w ∈ LPST ↔ stateOf 0 w = 0 ∧ w ∈ K
      rw [mem_K, mem_LPST]
    rw [heq]
    exact (stateOf_height 0).inter h

end PST

end GeneralizedStarHeight
