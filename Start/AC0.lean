/-
**`AC⁰`: constant-depth, polynomial-size circuits with unbounded fan-in.**

The circuits of `Start/PolyCircuit.lean` have gates of fan-in two, which is the right model for
polynomial size but not for constant depth.  This module adds the unbounded fan-in model of
`AC⁰`: a circuit is a tree whose leaves are literals `xᵢ`, `¬xᵢ` or constants and whose inner
gates are `NOT`, and `AND`/`OR` of an arbitrary finite list of subcircuits.

Trees rather than shared circuits: at constant depth `d` the two differ only polynomially (a
shared circuit of size `s` unfolds to a tree of size at most `s ^ d`), so the class `AC⁰` is the
same.  Depth counts the `AND`/`OR` layers; a `NOT` gate adds no depth, since negations can be
pushed to the inputs at no cost in depth (`ACCirc.nnf`).

Main definitions:

* `Complexity.ACCirc` with `ACCirc.eval`, `ACCirc.depth`, `ACCirc.size`;
* `Complexity.ACCirc.NoNot` — negation normal form: negations only on input literals;
* `Complexity.ACCirc.nnf` — pushing negations to the inputs (De Morgan);
* `Complexity.InAC0` — the class `AC⁰` of languages decided, at each input length `n`, by a
  circuit of size polynomial in `n` and of depth bounded by a constant.

Main results:

* `Complexity.ACCirc.eval_nnf`, `depth_nnf`, `size_nnf`, `noNot_nnf` — the negation normal form
  computes the same function (or its negation), with the same depth and no larger size;
* `Complexity.ACCirc.eval_and_join`, `eval_or_join` and the depth bounds `depth_and_join_le`,
  `depth_or_join_le` — **merging layers**: an `AND` of `AND`s is one `AND` of all the inputs, one
  layer shallower, and likewise for `OR`;
* `Complexity.InAC0.compl`, `InAC0.inter`, `InAC0.union` — `AC⁰` is closed under the Boolean
  operations, and `InAC0.exists_noNot` — its circuits may be taken in negation normal form;
* `Complexity.inAC0_someOne`, `Complexity.inAC0_allOne` — non-vacuity: "some bit is `1`" and
  "every bit is `1`" are in `AC⁰`, with depth one.
-/

import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Circuits -/

/-- An unbounded fan-in circuit, as a tree: literals, constants, `NOT`, and `AND`/`OR` of a list
of subcircuits. -/
inductive ACCirc : Type
  /-- The literal `xᵢ` if `b = true`, `¬xᵢ` if `b = false`. -/
  | lit (i : ℕ) (b : Bool)
  /-- A constant. -/
  | const (b : Bool)
  /-- Negation. -/
  | not (c : ACCirc)
  /-- Conjunction of a list of subcircuits. -/
  | and (cs : List ACCirc)
  /-- Disjunction of a list of subcircuits. -/
  | or (cs : List ACCirc)
  deriving Inhabited

namespace ACCirc

/-- Induction on circuits, with the hypothesis for every member of the list of inputs of a gate. -/
theorem induct' (P : ACCirc → Prop) (hl : ∀ i b, P (.lit i b)) (hc : ∀ b, P (.const b))
    (hn : ∀ c, P c → P (.not c)) (ha : ∀ cs, (∀ c ∈ cs, P c) → P (.and cs))
    (ho : ∀ cs, (∀ c ∈ cs, P c) → P (.or cs)) : ∀ c, P c := by
  intro c
  induction c using ACCirc.rec (motive_2 := fun cs => ∀ c ∈ cs, P c) with
  | lit i b => exact hl i b
  | const b => exact hc b
  | not c ih => exact hn c ih
  | and cs ih => exact ha cs ih
  | or cs ih => exact ho cs ih
  | nil => rename_i h; simp at h
  | cons c cs ih1 ih2 =>
      rename_i d hd
      rcases List.mem_cons.1 hd with rfl | h
      · exact ih1
      · exact ih2 d h

/-- The value of a circuit on an input word; bits beyond the word read as `false`. -/
def eval (x : Word) : ACCirc → Bool
  | .lit i b => x.getD i false == b
  | .const b => b
  | .not c => !c.eval x
  | .and cs => cs.attach.all (fun c => c.1.eval x)
  | .or cs => cs.attach.any (fun c => c.1.eval x)
decreasing_by
  all_goals first
    | (simp only [ACCirc.not.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem (Subtype.property ‹Subtype _›)
       simp only [ACCirc.and.sizeOf_spec, ACCirc.or.sizeOf_spec]; omega)

/-- The depth: the number of `AND`/`OR` layers on the longest path. -/
def depth : ACCirc → ℕ
  | .lit _ _ => 0
  | .const _ => 0
  | .not c => c.depth
  | .and cs => (cs.attach.map (fun c => c.1.depth)).foldr max 0 + 1
  | .or cs => (cs.attach.map (fun c => c.1.depth)).foldr max 0 + 1
decreasing_by
  all_goals first
    | (simp only [ACCirc.not.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem (Subtype.property ‹Subtype _›)
       simp only [ACCirc.and.sizeOf_spec, ACCirc.or.sizeOf_spec]; omega)

/-- The size: the number of nodes (leaves and gates). -/
def size : ACCirc → ℕ
  | .lit _ _ => 1
  | .const _ => 1
  | .not c => c.size + 1
  | .and cs => (cs.attach.map (fun c => c.1.size)).sum + 1
  | .or cs => (cs.attach.map (fun c => c.1.size)).sum + 1
decreasing_by
  all_goals first
    | (simp only [ACCirc.not.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem (Subtype.property ‹Subtype _›)
       simp only [ACCirc.and.sizeOf_spec, ACCirc.or.sizeOf_spec]; omega)

/-- The maximum of a function over a list (`0` on the empty list). -/
def lmax {α : Type} (f : α → ℕ) (l : List α) : ℕ := (l.map f).foldr max 0

theorem le_lmax {α : Type} (f : α → ℕ) {l : List α} {a : α} (h : a ∈ l) : f a ≤ lmax f l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
      rcases List.mem_cons.1 h with rfl | h
      · simp [lmax]
      · exact le_trans (ih h) (by simp [lmax])

theorem lmax_le {α : Type} (f : α → ℕ) {l : List α} {m : ℕ} (h : ∀ a ∈ l, f a ≤ m) :
    lmax f l ≤ m := by
  induction l with
  | nil => simp [lmax]
  | cons b l ih =>
      simp only [lmax, List.map_cons, List.foldr_cons] at ih ⊢
      exact max_le (h b (by simp)) (ih fun a ha => h a (by simp [ha]))

theorem lmax_append {α : Type} (f : α → ℕ) (l₁ l₂ : List α) :
    lmax f (l₁ ++ l₂) = max (lmax f l₁) (lmax f l₂) := by
  induction l₁ with
  | nil => simp [lmax]
  | cons b l ih =>
      simp only [lmax, List.cons_append, List.map_cons, List.foldr_cons] at ih ⊢
      rw [ih, max_assoc]

@[simp] theorem eval_lit (x : Word) (i : ℕ) (b : Bool) :
    (lit i b).eval x = (x.getD i false == b) := by
  rw [eval]

@[simp] theorem eval_const (x : Word) (b : Bool) : (const b).eval x = b := by
  rw [eval]

@[simp] theorem eval_not (x : Word) (c : ACCirc) : (not c).eval x = !c.eval x := by
  rw [eval]

@[simp] theorem eval_and (x : Word) (cs : List ACCirc) :
    (and cs).eval x = cs.all (fun c => c.eval x) := by
  rw [eval]
  simp [List.all_eq]

@[simp] theorem eval_or (x : Word) (cs : List ACCirc) :
    (or cs).eval x = cs.any (fun c => c.eval x) := by
  rw [eval]
  simp [List.any_eq]

@[simp] theorem depth_lit (i : ℕ) (b : Bool) : (lit i b).depth = 0 := by rw [depth]

@[simp] theorem depth_const (b : Bool) : (const b).depth = 0 := by rw [depth]

@[simp] theorem depth_not (c : ACCirc) : (not c).depth = c.depth := by rw [depth]

theorem attach_map_foldr {α : Type} (l : List α) (f : α → ℕ) :
    (l.attach.map (fun c => f c.1)).foldr max 0 = lmax f l := by
  rw [lmax]
  congr 1
  simp

theorem attach_map_sum {α : Type} (l : List α) (f : α → ℕ) :
    (l.attach.map (fun c => f c.1)).sum = (l.map f).sum := by
  simp

@[simp] theorem depth_and (cs : List ACCirc) : (and cs).depth = lmax depth cs + 1 := by
  rw [depth, attach_map_foldr cs depth]

@[simp] theorem depth_or (cs : List ACCirc) : (or cs).depth = lmax depth cs + 1 := by
  rw [depth, attach_map_foldr cs depth]

@[simp] theorem size_lit (i : ℕ) (b : Bool) : (lit i b).size = 1 := by rw [size]

@[simp] theorem size_const (b : Bool) : (const b).size = 1 := by rw [size]

@[simp] theorem size_not (c : ACCirc) : (not c).size = c.size + 1 := by rw [size]

@[simp] theorem size_and (cs : List ACCirc) : (and cs).size = (cs.map size).sum + 1 := by
  rw [size, attach_map_sum cs size]

@[simp] theorem size_or (cs : List ACCirc) : (or cs).size = (cs.map size).sum + 1 := by
  rw [size, attach_map_sum cs size]

/-! ### Negation normal form -/

/-- A circuit in **negation normal form**: no `NOT` gate (negations only on input literals). -/
def NoNot : ACCirc → Prop
  | .lit _ _ => True
  | .const _ => True
  | .not _ => False
  | .and cs => ∀ c ∈ cs, NoNot c
  | .or cs => ∀ c ∈ cs, NoNot c

/-- **Pushing negations to the inputs**: `nnf true c` computes `c` and `nnf false c` computes
`¬ c`, by De Morgan's laws. -/
def nnf : Bool → ACCirc → ACCirc
  | p, .lit i b => .lit i (b == p)
  | p, .const b => .const (b == p)
  | p, .not c => nnf (!p) c
  | true, .and cs => .and (cs.attach.map fun c => nnf true c.1)
  | false, .and cs => .or (cs.attach.map fun c => nnf false c.1)
  | true, .or cs => .or (cs.attach.map fun c => nnf true c.1)
  | false, .or cs => .and (cs.attach.map fun c => nnf false c.1)
termination_by _ c => c
decreasing_by
  all_goals first
    | (simp only [ACCirc.not.sizeOf_spec]; omega)
    | (have := List.sizeOf_lt_of_mem (Subtype.property ‹Subtype _›)
       simp only [ACCirc.and.sizeOf_spec, ACCirc.or.sizeOf_spec]; omega)

theorem nnf_not (p : Bool) (c : ACCirc) : nnf p (.not c) = nnf (!p) c := by
  rw [nnf]

theorem nnf_and (p : Bool) (cs : List ACCirc) :
    nnf p (.and cs) = if p then .and (cs.map (nnf true)) else .or (cs.map (nnf false)) := by
  cases p <;> rw [nnf] <;> simp

theorem nnf_or (p : Bool) (cs : List ACCirc) :
    nnf p (.or cs) = if p then .or (cs.map (nnf true)) else .and (cs.map (nnf false)) := by
  cases p <;> rw [nnf] <;> simp

theorem nnf_lit (p : Bool) (i : ℕ) (b : Bool) : nnf p (.lit i b) = .lit i (b == p) := by
  rw [nnf]

theorem nnf_const (p : Bool) (b : Bool) : nnf p (.const b) = .const (b == p) := by
  rw [nnf]

theorem any_congr' {l : List ACCirc} {f g : ACCirc → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      simp only [List.any_cons]
      rw [h c (by simp), ih fun a ha => h a (by simp [ha])]

theorem all_congr' {l : List ACCirc} {f g : ACCirc → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons c l ih =>
      simp only [List.all_cons]
      rw [h c (by simp), ih fun a ha => h a (by simp [ha])]

theorem any_not_eq (l : List ACCirc) (f : ACCirc → Bool) :
    (l.any fun a => !f a) = !(l.all f) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.any_cons, List.all_cons, ih, Bool.not_and]

theorem all_not_eq (l : List ACCirc) (f : ACCirc → Bool) :
    (l.all fun a => !f a) = !(l.any f) := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [List.any_cons, List.all_cons, ih, Bool.not_or]

/-- The negation normal form computes the circuit (`p = true`) or its negation (`p = false`). -/
theorem eval_nnf (x : Word) : ∀ (c : ACCirc) (p : Bool), (nnf p c).eval x = (c.eval x == p) := by
  refine induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b p
    rw [nnf_lit, eval_lit, eval_lit]
    generalize x.getD i false = y
    cases y <;> cases p <;> cases b <;> rfl
  · intro b p
    rw [nnf_const, eval_const, eval_const]
  · intro c ih p
    rw [nnf_not, ih, eval_not]
    cases p <;> cases c.eval x <;> rfl
  · intro cs ih p
    rw [nnf_and]
    cases p
    · simp only [Bool.false_eq_true, if_false, eval_or, eval_and, List.any_map,
        Function.comp_def]
      rw [any_congr' (g := fun c => !c.eval x) (fun c hc => by
        rw [ih c hc false]; cases c.eval x <;> rfl), any_not_eq]
      cases (cs.all fun c => c.eval x) <;> rfl
    · simp only [if_true, eval_and, List.all_map, Function.comp_def]
      rw [all_congr' (g := fun c => c.eval x) (fun c hc => by
        rw [ih c hc true]; cases c.eval x <;> rfl)]
      cases (cs.all fun c => c.eval x) <;> rfl
  · intro cs ih p
    rw [nnf_or]
    cases p
    · simp only [Bool.false_eq_true, if_false, eval_or, eval_and, List.all_map,
        Function.comp_def]
      rw [all_congr' (g := fun c => !c.eval x) (fun c hc => by
        rw [ih c hc false]; cases c.eval x <;> rfl), all_not_eq]
      cases (cs.any fun c => c.eval x) <;> rfl
    · simp only [if_true, eval_or, List.any_map, Function.comp_def]
      rw [any_congr' (g := fun c => c.eval x) (fun c hc => by
        rw [ih c hc true]; cases c.eval x <;> rfl)]
      cases (cs.any fun c => c.eval x) <;> rfl

theorem lmax_map_congr {cs : List ACCirc} {f : ACCirc → ACCirc}
    (h : ∀ c ∈ cs, (f c).depth = c.depth) : lmax depth (cs.map f) = lmax depth cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [lmax, List.map_cons, List.foldr_cons] at ih ⊢
      rw [h c (by simp), ih fun d hd => h d (by simp [hd])]

theorem sum_map_le {cs : List ACCirc} {f : ACCirc → ACCirc}
    (h : ∀ c ∈ cs, (f c).size ≤ c.size) : ((cs.map f).map size).sum ≤ (cs.map size).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h c (by simp)) (ih fun d hd => h d (by simp [hd]))

/-- Pushing negations to the inputs does not change the depth. -/
theorem depth_nnf : ∀ (c : ACCirc) (p : Bool), (nnf p c).depth = c.depth := by
  refine induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b p; rw [nnf_lit]; simp
  · intro b p; rw [nnf_const]; simp
  · intro c ih p; rw [nnf_not, ih]; simp
  · intro cs ih p
    rw [nnf_and]
    cases p <;> simp only [Bool.false_eq_true, if_false, if_true, depth_or, depth_and] <;>
      rw [lmax_map_congr fun c hc => ih c hc _]
  · intro cs ih p
    rw [nnf_or]
    cases p <;> simp only [Bool.false_eq_true, if_false, if_true, depth_or, depth_and] <;>
      rw [lmax_map_congr fun c hc => ih c hc _]

/-- Pushing negations to the inputs does not increase the size. -/
theorem size_nnf : ∀ (c : ACCirc) (p : Bool), (nnf p c).size ≤ c.size := by
  refine induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b p; rw [nnf_lit]; simp
  · intro b p; rw [nnf_const]; simp
  · intro c ih p; rw [nnf_not]; simp only [size_not]; exact le_trans (ih _) (by omega)
  · intro cs ih p
    rw [nnf_and]
    cases p <;> simp only [Bool.false_eq_true, if_false, if_true, size_or, size_and] <;>
      exact Nat.add_le_add_right (sum_map_le fun c hc => ih c hc _) 1
  · intro cs ih p
    rw [nnf_or]
    cases p <;> simp only [Bool.false_eq_true, if_false, if_true, size_or, size_and] <;>
      exact Nat.add_le_add_right (sum_map_le fun c hc => ih c hc _) 1

/-- The negation normal form has no `NOT` gate. -/
theorem noNot_nnf : ∀ (c : ACCirc) (p : Bool), NoNot (nnf p c) := by
  refine induct' _ ?_ ?_ ?_ ?_ ?_
  · intro i b p; rw [nnf_lit, NoNot]; trivial
  · intro b p; rw [nnf_const, NoNot]; trivial
  · intro c ih p; rw [nnf_not]; exact ih _
  · intro cs ih p
    rw [nnf_and]
    cases p <;> simp only [Bool.false_eq_true, if_false, if_true, NoNot, List.mem_map] <;>
      rintro _ ⟨c, hc, rfl⟩ <;> exact ih c hc _
  · intro cs ih p
    rw [nnf_or]
    cases p <;> simp only [Bool.false_eq_true, if_false, if_true, NoNot, List.mem_map] <;>
      rintro _ ⟨c, hc, rfl⟩ <;> exact ih c hc _

/-! ### Merging layers -/

theorem lmax_flatten (dss : List (List ACCirc)) :
    lmax depth dss.flatten = lmax (lmax depth) dss := by
  induction dss with
  | nil => rfl
  | cons ds dss ih =>
      rw [List.flatten_cons, lmax_append, ih]
      simp [lmax]

theorem lmax_map_and (dss : List (List ACCirc)) :
    lmax depth (dss.map and) = lmax (fun ds => lmax depth ds + 1) dss := by
  induction dss with
  | nil => rfl
  | cons ds dss ih =>
      simp only [lmax, List.map_cons, List.foldr_cons, depth_and] at ih ⊢
      rw [ih]

theorem lmax_map_or (dss : List (List ACCirc)) :
    lmax depth (dss.map or) = lmax (fun ds => lmax depth ds + 1) dss := by
  induction dss with
  | nil => rfl
  | cons ds dss ih =>
      simp only [lmax, List.map_cons, List.foldr_cons, depth_or] at ih ⊢
      rw [ih]

/-- **Merging two `AND` layers**: an `AND` of `AND`s is the `AND` of all their inputs. -/
theorem eval_and_join (x : Word) (dss : List (List ACCirc)) :
    (and dss.flatten).eval x = (and (dss.map and)).eval x := by
  simp [List.all_flatten, List.all_map, Function.comp_def]

/-- **Merging two `OR` layers**: an `OR` of `OR`s is the `OR` of all their inputs. -/
theorem eval_or_join (x : Word) (dss : List (List ACCirc)) :
    (or dss.flatten).eval x = (or (dss.map or)).eval x := by
  simp [List.any_flatten, List.any_map, Function.comp_def]

theorem lmax_succ {α : Type} (f : α → ℕ) {l : List α} (hl : l ≠ []) :
    lmax (fun a => f a + 1) l = lmax f l + 1 := by
  induction l with
  | nil => exact absurd rfl hl
  | cons b l ih =>
      cases l with
      | nil => simp [lmax]
      | cons c l =>
          have := ih (by simp)
          simp only [lmax, List.map_cons, List.foldr_cons] at this ⊢
          rw [this]
          omega

/-- Merging two `AND` layers saves a layer. -/
theorem depth_and_join_le {dss : List (List ACCirc)} (h : dss ≠ []) :
    (and dss.flatten).depth + 1 ≤ (and (dss.map and)).depth := by
  rw [depth_and, depth_and, lmax_flatten, lmax_map_and, lmax_succ _ h]

/-- Merging two `OR` layers saves a layer. -/
theorem depth_or_join_le {dss : List (List ACCirc)} (h : dss ≠ []) :
    (or dss.flatten).depth + 1 ≤ (or (dss.map or)).depth := by
  rw [depth_or, depth_or, lmax_flatten, lmax_map_or, lmax_succ _ h]

theorem sum_flatten (dss : List (List ACCirc)) :
    (dss.flatten.map size).sum = (dss.map fun ds => (ds.map size).sum).sum := by
  induction dss with
  | nil => rfl
  | cons ds dss ih => simp [Function.comp_def]

/-- Merging two `AND` layers does not increase the size. -/
theorem size_and_join_le (dss : List (List ACCirc)) :
    (and dss.flatten).size ≤ (and (dss.map and)).size := by
  rw [size_and, size_and, sum_flatten]
  refine Nat.add_le_add_right ?_ 1
  induction dss with
  | nil => simp
  | cons ds dss ih => simp only [List.map_cons, List.sum_cons, size_and]; omega

/-- Merging two `OR` layers does not increase the size. -/
theorem size_or_join_le (dss : List (List ACCirc)) :
    (or dss.flatten).size ≤ (or (dss.map or)).size := by
  rw [size_or, size_or, sum_flatten]
  refine Nat.add_le_add_right ?_ 1
  induction dss with
  | nil => simp
  | cons ds dss ih => simp only [List.map_cons, List.sum_cons, size_or]; omega

end ACCirc

/-! ### The class `AC⁰` -/

/-- **`AC⁰`**: `L` is decided, at every input length `n`, by an unbounded fan-in circuit of size
at most `p n` for a polynomial `p` and of depth at most a constant `d`. -/
def InAC0 (L : Language) : Prop :=
  ∃ (d : ℕ) (p : ℕ → ℕ), PolyBound p ∧ ∀ n, ∃ C : ACCirc, C.depth ≤ d ∧ C.size ≤ p n ∧
    ∀ x : Word, x.length = n → (L x ↔ C.eval x = true)

/-- `AC⁰` circuits may be taken in negation normal form, at the same depth and size bound. -/
theorem InAC0.exists_noNot {L : Language} (h : InAC0 L) :
    ∃ (d : ℕ) (p : ℕ → ℕ), PolyBound p ∧ ∀ n, ∃ C : ACCirc, C.NoNot ∧ C.depth ≤ d ∧
      C.size ≤ p n ∧ ∀ x : Word, x.length = n → (L x ↔ C.eval x = true) := by
  obtain ⟨d, p, hp, hC⟩ := h
  refine ⟨d, p, hp, fun n => ?_⟩
  obtain ⟨C, hd, hs, hx⟩ := hC n
  refine ⟨ACCirc.nnf true C, ACCirc.noNot_nnf C true, by rw [ACCirc.depth_nnf]; exact hd,
    le_trans (ACCirc.size_nnf C true) hs, fun x hlen => ?_⟩
  rw [hx x hlen, ACCirc.eval_nnf]
  cases C.eval x <;> simp

/-- **`AC⁰` is closed under complement.** -/
theorem InAC0.compl {L : Language} (h : InAC0 L) : InAC0 (fun x => ¬ L x) := by
  obtain ⟨d, p, hp, hC⟩ := h
  refine ⟨d, fun n => p n + 1, hp.add (polyBound_const 1), fun n => ?_⟩
  obtain ⟨C, hd, hs, hx⟩ := hC n
  refine ⟨.not C, by simpa using hd, by simpa using hs, fun x hlen => ?_⟩
  dsimp only
  rw [hx x hlen, ACCirc.eval_not]
  cases C.eval x <;> simp

/-- **`AC⁰` is closed under intersection.** -/
theorem InAC0.inter {L₁ L₂ : Language} (h₁ : InAC0 L₁) (h₂ : InAC0 L₂) :
    InAC0 (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨d₁, p₁, hp₁, hC₁⟩ := h₁
  obtain ⟨d₂, p₂, hp₂, hC₂⟩ := h₂
  refine ⟨max d₁ d₂ + 1, fun n => p₁ n + p₂ n + 1, (hp₁.add hp₂).add (polyBound_const 1),
    fun n => ?_⟩
  obtain ⟨C₁, hd₁, hs₁, hx₁⟩ := hC₁ n
  obtain ⟨C₂, hd₂, hs₂, hx₂⟩ := hC₂ n
  refine ⟨.and [C₁, C₂], ?_, ?_, fun x hlen => ?_⟩
  · simp only [ACCirc.depth_and, ACCirc.lmax, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil]
    omega
  · simp only [ACCirc.size_and, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · dsimp only
    rw [hx₁ x hlen, hx₂ x hlen]
    simp

/-- **`AC⁰` is closed under union.** -/
theorem InAC0.union {L₁ L₂ : Language} (h₁ : InAC0 L₁) (h₂ : InAC0 L₂) :
    InAC0 (fun x => L₁ x ∨ L₂ x) := by
  obtain ⟨d₁, p₁, hp₁, hC₁⟩ := h₁
  obtain ⟨d₂, p₂, hp₂, hC₂⟩ := h₂
  refine ⟨max d₁ d₂ + 1, fun n => p₁ n + p₂ n + 1, (hp₁.add hp₂).add (polyBound_const 1),
    fun n => ?_⟩
  obtain ⟨C₁, hd₁, hs₁, hx₁⟩ := hC₁ n
  obtain ⟨C₂, hd₂, hs₂, hx₂⟩ := hC₂ n
  refine ⟨.or [C₁, C₂], ?_, ?_, fun x hlen => ?_⟩
  · simp only [ACCirc.depth_or, ACCirc.lmax, List.map_cons, List.map_nil, List.foldr_cons,
      List.foldr_nil]
    omega
  · simp only [ACCirc.size_or, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  · dsimp only
    rw [hx₁ x hlen, hx₂ x hlen]
    simp

/-! ### Non-vacuity -/

/-- The `OR` of the first `n` input bits. -/
def orAll (n : ℕ) : ACCirc := .or ((List.range n).map fun i => .lit i true)

/-- The `AND` of the first `n` input bits. -/
def andAll (n : ℕ) : ACCirc := .and ((List.range n).map fun i => .lit i true)

theorem getD_of_mem {x : Word} {b : Bool} (h : b ∈ x) : ∃ i < x.length, x.getD i false = b := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  exact ⟨i, hi, by simp [hi]⟩

/-- **"Some bit is `1`" is in `AC⁰`**, by a single `OR` gate. -/
theorem inAC0_someOne : InAC0 (fun x => true ∈ x) := by
  refine ⟨1, fun n => n + 1, ⟨1, 1, fun n => by simp⟩, fun n => ⟨orAll n, ?_, ?_, ?_⟩⟩
  · have : ACCirc.lmax ACCirc.depth ((List.range n).map fun i => ACCirc.lit i true) ≤ 0 :=
      ACCirc.lmax_le _ fun c hc => by obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc; simp
    simp only [orAll, ACCirc.depth_or]
    omega
  · simp [orAll, Function.comp_def]
  · intro x hlen
    simp only [orAll, ACCirc.eval_or, List.any_map, Function.comp_def, ACCirc.eval_lit,
      List.any_eq_true, List.mem_range]
    constructor
    · intro hx
      obtain ⟨i, hi, hb⟩ := getD_of_mem hx
      exact ⟨i, hlen ▸ hi, by simpa using hb⟩
    · rintro ⟨i, hi, hb⟩
      have hb' : x.getD i false = true := by simpa using hb
      rw [List.getD_eq_getElem _ _ (hlen ▸ hi)] at hb'
      exact hb' ▸ List.getElem_mem _

/-- **"Every bit is `1`" is in `AC⁰`**, by a single `AND` gate. -/
theorem inAC0_allOne : InAC0 (fun x => ∀ b ∈ x, b = true) := by
  refine ⟨1, fun n => n + 1, ⟨1, 1, fun n => by simp⟩, fun n => ⟨andAll n, ?_, ?_, ?_⟩⟩
  · have : ACCirc.lmax ACCirc.depth ((List.range n).map fun i => ACCirc.lit i true) ≤ 0 :=
      ACCirc.lmax_le _ fun c hc => by obtain ⟨i, _, rfl⟩ := List.mem_map.1 hc; simp
    simp only [andAll, ACCirc.depth_and]
    omega
  · simp [andAll, Function.comp_def]
  · intro x hlen
    simp only [andAll, ACCirc.eval_and, List.all_map, Function.comp_def, ACCirc.eval_lit,
      List.all_eq_true, List.mem_range]
    constructor
    · intro hx i hi
      rw [List.getD_eq_getElem _ _ (hlen ▸ hi)]
      simp [hx _ (List.getElem_mem _)]
    · intro hx b hb
      obtain ⟨i, hi, rfl⟩ := getD_of_mem hb
      simpa using hx i (hlen ▸ hi)

end Complexity
