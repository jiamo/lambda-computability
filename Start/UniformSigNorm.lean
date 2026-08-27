/-
# Every Cobham term is well formed at every arity, and every language in P is P-uniformly decidable

`Start/UniformSigAll.lean` compiles the terms satisfying the arity discipline
`Complexity.CobShape`.  That discipline is no restriction on the *functions* denoted: a projection
naming an argument that does not exist returns the empty word, a smash with too few arguments
returns the empty word, and so on.  `Complexity.shapeAt r v` performs those replacements, and
denotes the same function as `v` on argument lists of length `r`.

Together with `Start/UniformSigLang.lean` this removes the last hypothesis from the reduction:
**every language in P is decided by a P-uniform family of circuits, and therefore reduces to SAT in
polynomial time.**

Main definitions:

* `Complexity.shapeAt` — the well-formed term of arity `r` denoting the same function.

Main results:

* `Complexity.cobShape_shapeAt`, `Complexity.eval_shapeAt` — it is well formed, and it denotes the
  same function on arguments lists of the right length;
* `Complexity.pUniformDecidable_of_cob` — the language of an arbitrary Cobham term is P-uniformly
  decidable;
* `Complexity.pUniformDecidable_of_inP`, `Complexity.polyManyOne_SAT_of_inP_viaCircuits` —
  **every language in
  P is P-uniformly decidable, and reduces to SAT in polynomial time.**
-/

import Start.UniformSigLang

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Normalizing a term at a given arity -/

/-- The well-formed term of arity `r` denoting the same function as `v` on argument lists of
length `r`: a projection out of range, and a smash with too few arguments, denote the constant
empty word, and a successor with no argument is applied to the constant empty word. -/
def shapeAt : ℕ → Cob → Cob
  | r, .proj i => if i < r then .proj i else .empty
  | _, .empty => .empty
  | r, .app b => if 0 < r then .app b else .comp (.app b) [.empty]
  | r, .smash => if 2 ≤ r then .smash else .empty
  | r, .comp f gs => .comp (shapeAt gs.length f) (gs.attach.map (fun g => shapeAt r g.1))
  | 0, .bRec g _ _ _ => shapeAt 0 g
  | (p + 1), .bRec g h₀ h₁ bd =>
      .bRec (shapeAt p g) (shapeAt (p + 2) h₀) (shapeAt (p + 2) h₁) (shapeAt (p + 1) bd)
decreasing_by
  all_goals (simp_wf; try omega)
  all_goals
    (have := List.sizeOf_lt_of_mem g.2
     omega)

/-- **The normalized term is well formed.** -/
theorem cobShape_shapeAt : ∀ (r : ℕ) (v : Cob), CobShape r (shapeAt r v) := by
  intro r v
  induction r, v using shapeAt.induct with
  | case1 r i h => rw [shapeAt, if_pos h]; exact CobShape.proj h
  | case2 r i h => rw [shapeAt, if_neg h]; exact CobShape.empty
  | case3 r => rw [shapeAt]; exact CobShape.empty
  | case4 r b h => rw [shapeAt, if_pos h]; exact CobShape.app h
  | case5 r b h =>
      rw [shapeAt, if_neg h]
      exact CobShape.comp (CobShape.app (by simp)) (by
        intro g hg
        rw [List.mem_singleton.1 hg]
        exact CobShape.empty)
  | case6 r h => rw [shapeAt, if_pos h]; exact CobShape.smash h
  | case7 r h => rw [shapeAt, if_neg h]; exact CobShape.empty
  | case8 r f gs ihf ihgs =>
      rw [shapeAt]
      refine CobShape.comp ?_ ?_
      · simpa using ihf
      · intro g hg
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists] at hg
        obtain ⟨g', hg', rfl⟩ := hg
        exact ihgs ⟨g', hg'⟩
  | case9 g h₀ h₁ bd ih => rw [shapeAt]; exact ih
  | case10 p g h₀ h₁ bd ih1 ih2 ih3 ih4 =>
      rw [shapeAt]
      exact CobShape.bRec ih1 ih2 ih3 ih4

/-- **The normalized term denotes the same function** on argument lists of the arity it was
normalized at. -/
theorem eval_shapeAt : ∀ (r : ℕ) (v : Cob) (args : List Word), args.length = r →
    (shapeAt r v).eval args = v.eval args := by
  intro r v
  induction r, v using shapeAt.induct with
  | case1 r i h => intro args _; rw [shapeAt, if_pos h]
  | case2 r i h =>
      intro args hargs
      rw [shapeAt, if_neg h, Cob.eval_empty, Cob.eval_proj,
        List.getD_eq_default _ _ (by omega)]
  | case3 r => intro args _; rw [shapeAt]
  | case4 r b h => intro args _; rw [shapeAt, if_pos h]
  | case5 r b h =>
      intro args hargs
      have hnil : args = [] := by
        cases args with
        | nil => rfl
        | cons u us => exfalso; simp at hargs; omega
      subst hnil
      rw [shapeAt, if_neg h]
      simp
  | case6 r h => intro args _; rw [shapeAt, if_pos h]
  | case7 r h =>
      intro args hargs
      rw [shapeAt, if_neg h, Cob.eval_empty, Cob.eval_smash,
        List.getD_eq_default (l := args) (n := 1) [] (by omega)]
      simp
  | case8 r f gs ihf ihgs =>
      intro args hargs
      rw [shapeAt, Cob.eval_comp, Cob.eval_comp]
      have hmap : (gs.attach.map (fun g => shapeAt r g.1)).map (fun t => t.eval args)
          = gs.map (fun g => g.eval args) := by
        rw [List.map_map,
          show (gs.map fun g => g.eval args) = gs.attach.map (fun g => g.1.eval args) from
            (List.attach_map_val (l := gs) (f := fun g => g.eval args)).symm]
        exact List.map_congr_left (fun g _ => ihgs g args hargs)
      rw [hmap]
      exact ihf (gs.map (fun g => g.eval args)) (by simp)
  | case9 g h₀ h₁ bd ih =>
      intro args hargs
      have hnil : args = [] := by
        cases args with
        | nil => rfl
        | cons u us => exfalso; simp at hargs
      subst hnil
      rw [shapeAt, ih [] rfl, Cob.eval_bRec]
      rfl
  | case10 p g h₀ h₁ bd ih1 ih2 ih3 ih4 =>
      intro args hargs
      obtain ⟨y, rest, rfl⟩ : ∃ y rest, args = y :: rest := by
        cases args with
        | nil => simp at hargs
        | cons y rest => exact ⟨y, rest, rfl⟩
      have hrest : rest.length = p := by simpa using hargs
      clear hargs
      rw [shapeAt]
      induction y with
      | nil => rw [Cob.eval_bRec_nil, Cob.eval_bRec_nil]; exact ih1 rest hrest
      | cons b y ihy =>
          rw [Cob.eval_bRec_cons, Cob.eval_bRec_cons, ihy,
            ih4 ((b :: y) :: rest) (by simp [hrest])]
          cases b
          · simp only [Bool.false_eq_true, if_false]
            rw [ih2 (y :: _ :: rest) (by simp [hrest])]
          · simp only [if_true]
            rw [ih3 (y :: _ :: rest) (by simp [hrest])]

/-! ### Every language in P -/

/-- **The language of an arbitrary Cobham term of one argument is decided by a P-uniform
family.** -/
theorem pUniformDecidable_of_cob (v : Cob) {L : Language}
    (hacc : ∀ x : Word, L x ↔ v.eval [x] ≠ []) : PUniformDecidable L := by
  refine pUniformDecidable_of_cobShape (v := shapeAt 1 v) (cobShape_shapeAt 1 v) (fun x => ?_)
  rw [eval_shapeAt 1 v [x] rfl]
  exact hacc x

/-- **Every language in P is decided by a P-uniform family of circuits.** -/
theorem pUniformDecidable_of_inP {L : Language} (h : InP L) : PUniformDecidable L := by
  obtain ⟨v, hv⟩ := h
  exact pUniformDecidable_of_cob v hv

/-- **Every language in P reduces to SAT in polynomial time**, with no hypothesis left over. -/
theorem polyManyOne_SAT_of_inP_viaCircuits {L : Language} (h : InP L) : L ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_of_inP h)

end Complexity
