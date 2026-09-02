/-
A natural numbers object in the category of assemblies.

Over an arbitrary partial combinatory algebra, the natural numbers carry an assembly structure in
which `a` realizes `n` exactly when `a` behaves as the `n`-th Church numeral: applied to `r` and
`b` it computes the `n`-fold iterate of `r` on `b`.  Zero and successor are realized by explicit
combinators, and the resulting object satisfies Lawvere's universal property.

* `CategoryTheory.Limits.IsNNO` — Lawvere's natural numbers object, stated for a category with a
  terminal object;
* `Realizability.iterp`, `Realizability.cnum`, `Realizability.IsNumeral` — iterated application,
  the Church numerals, and the property of computing iteration;
* `Realizability.Assembly.natAsm`, `.natZero`, `.natSucc`;
* `Realizability.Assembly.isNNO_natAsm` — the universal property.
-/

import Start.Assembly

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v w

namespace CategoryTheory.Limits

variable {C : Type w} [Category C]

/-- **Lawvere's natural numbers object**: `T` is terminal, and for every `q : T ⟶ X` and every
endomorphism `f` of `X` there is a unique `u` with `zero ≫ u = q` and `succ ≫ u = u ≫ f`, i.e. a
unique map defined by primitive recursion. -/
structure IsNNO {T N : C} (zero : T ⟶ N) (succ : N ⟶ N) : Prop where
  /-- The source of `zero` is a terminal object. -/
  isTerminal : Nonempty (IsTerminal T)
  /-- Definition by iteration is possible, and the result is unique. -/
  existsUnique_rec : ∀ (X : C) (q : T ⟶ X) (f : X ⟶ X),
    ∃! u : N ⟶ X, zero ≫ u = q ∧ succ ≫ u = u ≫ f

/-- The map out of a natural numbers object defined by iteration from a base point and an
endomorphism. -/
noncomputable def IsNNO.iter {T N : C} {zero : T ⟶ N} {succ : N ⟶ N} (h : IsNNO zero succ)
    {X : C} (q : T ⟶ X) (f : X ⟶ X) : N ⟶ X :=
  (h.existsUnique_rec X q f).exists.choose

theorem IsNNO.zero_comp_iter {T N : C} {zero : T ⟶ N} {succ : N ⟶ N} (h : IsNNO zero succ)
    {X : C} (q : T ⟶ X) (f : X ⟶ X) : zero ≫ h.iter q f = q :=
  (h.existsUnique_rec X q f).exists.choose_spec.1

theorem IsNNO.succ_comp_iter {T N : C} {zero : T ⟶ N} {succ : N ⟶ N} (h : IsNNO zero succ)
    {X : C} (q : T ⟶ X) (f : X ⟶ X) : succ ≫ h.iter q f = h.iter q f ≫ f :=
  (h.existsUnique_rec X q f).exists.choose_spec.2

/-- Two maps out of a natural numbers object defined by the same iteration agree. -/
theorem IsNNO.iter_unique {T N : C} {zero : T ⟶ N} {succ : N ⟶ N} (h : IsNNO zero succ)
    {X : C} {q : T ⟶ X} {f : X ⟶ X} {u v : N ⟶ X} (hu₀ : zero ≫ u = q)
    (hus : succ ≫ u = u ≫ f) (hv₀ : zero ≫ v = q) (hvs : succ ≫ v = v ≫ f) : u = v := by
  obtain ⟨w, -, hw⟩ := h.existsUnique_rec X q f
  rw [hw u ⟨hu₀, hus⟩, hw v ⟨hv₀, hvs⟩]

/-- A natural numbers object is unique up to isomorphism: two natural numbers objects with the
same terminal object are isomorphic, by the maps each defines by iteration into the other. -/
noncomputable def IsNNO.iso {T N₁ N₂ : C} {zero₁ : T ⟶ N₁} {succ₁ : N₁ ⟶ N₁} {zero₂ : T ⟶ N₂}
    {succ₂ : N₂ ⟶ N₂} (h₁ : IsNNO zero₁ succ₁) (h₂ : IsNNO zero₂ succ₂) : N₁ ≅ N₂ where
  hom := h₁.iter zero₂ succ₂
  inv := h₂.iter zero₁ succ₁
  hom_inv_id :=
    h₁.iter_unique (q := zero₁) (f := succ₁)
      (by rw [← Category.assoc, h₁.zero_comp_iter, h₂.zero_comp_iter])
      (by rw [← Category.assoc, h₁.succ_comp_iter, Category.assoc, h₂.succ_comp_iter,
        Category.assoc])
      (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])
  inv_hom_id :=
    h₂.iter_unique (q := zero₂) (f := succ₂)
      (by rw [← Category.assoc, h₂.zero_comp_iter, h₁.zero_comp_iter])
      (by rw [← Category.assoc, h₂.succ_comp_iter, Category.assoc, h₁.succ_comp_iter,
        Category.assoc])
      (Category.comp_id _) (by rw [Category.comp_id, Category.id_comp])

end CategoryTheory.Limits

namespace Realizability

open CategoryTheory CategoryTheory.Limits

variable {A : Type u} [PCA A]

/-! ### Church numerals in a partial combinatory algebra -/

/-- `iterp r n b` is the `n`-fold application of `r` to `b`, a partial element. -/
def iterp (r : A) : ℕ → A → Part A
  | 0, b => Part.some b
  | n + 1, b => (iterp r n b).bind fun v => PCA.app r v

@[simp] theorem iterp_zero (r b : A) : iterp r 0 b = Part.some b := rfl

theorem iterp_succ (r : A) (n : ℕ) (b : A) :
    iterp r (n + 1) b = (iterp r n b).bind fun v => PCA.app r v := rfl

/-- `a` is a **numeral for `n`** when applying it to `r` and `b` computes the `n`-fold iterate of
`r` on `b`.  This is the realizability relation of the natural numbers object. -/
def IsNumeral (a : A) (n : ℕ) : Prop :=
  ∀ r b v : A, v ∈ iterp r n b → v ∈ (Part.some a ⬝ Part.some r) ⬝ Part.some b

/-- The `n`-th Church numeral `λ f x. f (f (⋯ (f x)))`. -/
noncomputable def cnum (A : Type u) [PCA A] : ℕ → A
  | 0 => PCA.kI A
  | n + 1 => PCA.lam2 (Expr.app (Expr.var 0)
      (Expr.app (Expr.app (Expr.const (cnum A n)) (Expr.var 0)) (Expr.var 1)))

theorem isNumeral_cnum (A : Type u) [PCA A] (n : ℕ) : IsNumeral (cnum A n) n := by
  induction n with
  | zero =>
      intro r b v hv
      rw [iterp_zero, Part.mem_some_iff] at hv
      subst hv
      rw [show cnum A 0 = PCA.kI A from rfl, PCA.kI_app]
      exact Part.mem_some v
  | succ n ih =>
      intro r b v hv
      rw [iterp_succ, Part.mem_bind_iff] at hv
      obtain ⟨w, hw, hv⟩ := hv
      have hbody : v ∈ (Part.some r) ⬝ ((Part.some (cnum A n) ⬝ Part.some r) ⬝ Part.some b) := by
        rw [papp_some_left]
        exact Part.mem_bind_iff.2 ⟨w, ih r b w hw, hv⟩
      have := PCA.lam2_app_app (Expr.app (Expr.var 0)
        (Expr.app (Expr.app (Expr.const (cnum A n)) (Expr.var 0)) (Expr.var 1))) r b
      refine this v ?_
      simpa [Expr.eval, Function.update_apply] using hbody

/-! ### The assembly of natural numbers -/

namespace Assembly

/-- The natural numbers as an assembly: `a` realizes `n` when `a` is a numeral for `n`. -/
noncomputable def natAsm (A : Type u) [PCA A] : Assembly.{u, v} A where
  carrier := ULift ℕ
  realizes a x := IsNumeral a x.down
  exists_realizer x := ⟨cnum A x.down, isNumeral_cnum A x.down⟩

/-- Zero, realized by `λ y. (λ f x. x)`. -/
noncomputable def natZero (A : Type u) [PCA A] : unitAsm.{u, v} A ⟶ natAsm A where
  toFun _ := ⟨0⟩
  tracked := by
    refine ⟨PCA.lam1 (Expr.const (PCA.kI A)), fun a _ _ => ⟨PCA.kI A, ?_, ?_⟩⟩
    · have := PCA.lam1_app (Expr.const (PCA.kI A)) a
      rw [papp_some_some] at this
      exact this _ (Part.mem_some _)
    · intro r b v hv
      rw [iterp_zero, Part.mem_some_iff] at hv
      subst hv
      rw [PCA.kI_app]
      exact Part.mem_some _

/-- The body `λ n f x. f (n f x)` of the successor combinator. -/
def succBody (A : Type u) [PCA A] : Expr A :=
  Expr.app (Expr.var 1) (Expr.app (Expr.app (Expr.var 0) (Expr.var 1)) (Expr.var 2))

/-- The successor combinator. -/
noncomputable def succEl (A : Type u) [PCA A] : A := PCA.lam3 (succBody A)

theorem isNumeral_succEl {a : A} {n : ℕ} (ha : IsNumeral a n) {w : A}
    (hw : Part.some w = Part.some (succEl A) ⬝ Part.some a) : IsNumeral w (n + 1) := by
  intro r b v hv
  rw [iterp_succ, Part.mem_bind_iff] at hv
  obtain ⟨u, hu, hv⟩ := hv
  have hbody : v ∈ (Part.some r) ⬝ ((Part.some a ⬝ Part.some r) ⬝ Part.some b) := by
    rw [papp_some_left]
    exact Part.mem_bind_iff.2 ⟨u, ha r b u hu, hv⟩
  have hstep := PCA.lam3_app_app_app (succBody A) a r b
  rw [hw]
  refine hstep v ?_
  simpa [succBody, Expr.eval, Function.update_apply] using hbody

/-- The successor map of assemblies. -/
noncomputable def natSucc (A : Type u) [PCA A] : natAsm.{u, v} A ⟶ natAsm A where
  toFun x := ⟨x.down + 1⟩
  tracked := by
    refine ⟨succEl A, fun a x ha => ?_⟩
    obtain ⟨w, hw⟩ : ∃ w : A, Part.some w = Part.some (succEl A) ⬝ Part.some a :=
      ⟨_, Part.some_get (PCA.lam3_app_dom (succBody A) a)⟩
    refine ⟨w, ?_, isNumeral_succEl ha hw⟩
    have : w ∈ Part.some (succEl A) ⬝ Part.some a := hw ▸ Part.mem_some w
    rwa [papp_some_some] at this

@[simp] theorem natZero_toFun (x : (unitAsm.{u, v} A).carrier) :
    (natZero.{u, v} A).toFun x = ⟨0⟩ := rfl

@[simp] theorem natSucc_toFun (x : (natAsm.{u, v} A).carrier) :
    (natSucc.{u, v} A).toFun x = ⟨x.down + 1⟩ := rfl

/-- The iteration realizer `λ n. n f x` associated with a base point and an endomorphism. -/
noncomputable def iterEl (rf rq : A) : A :=
  PCA.lam1 (Expr.app (Expr.app (Expr.var 0) (Expr.const rf)) (Expr.const rq))

variable {X : Assembly.{u, v} A}

theorem exists_mem_iterp {rf rq : A} {f : X.carrier → X.carrier} (hrf : RealizesFun X X rf f)
    {x0 : X.carrier} (hrq : X.realizes rq x0) (n : ℕ) :
    ∃ v ∈ iterp rf n rq, X.realizes v (f^[n] x0) := by
  induction n with
  | zero => exact ⟨rq, Part.mem_some _, hrq⟩
  | succ n ih =>
      obtain ⟨v, hv, hvx⟩ := ih
      obtain ⟨v', hv', hv'x⟩ := hrf v (f^[n] x0) hvx
      refine ⟨v', ?_, ?_⟩
      · rw [iterp_succ]
        exact Part.mem_bind_iff.2 ⟨v, hv, hv'⟩
      · rwa [Function.iterate_succ_apply']

theorem tracked_iter {rf rq : A} {f : X.carrier → X.carrier} (hrf : RealizesFun X X rf f)
    {x0 : X.carrier} (hrq : X.realizes rq x0) :
    RealizesFun (natAsm.{u, v} A) X (iterEl rf rq) fun x => f^[x.down] x0 := by
  intro a x ha
  obtain ⟨v, hv, hvx⟩ := exists_mem_iterp hrf hrq x.down
  refine ⟨v, ?_, hvx⟩
  have hmem : v ∈ (Part.some a ⬝ Part.some rf) ⬝ Part.some rq := ha rf rq v hv
  have := PCA.lam1_app (Expr.app (Expr.app (Expr.var 0) (Expr.const rf)) (Expr.const rq)) a
  rw [papp_some_some] at this
  refine this v ?_
  simpa [Expr.eval, iterEl] using hmem

/-- **The assembly of natural numbers is a natural numbers object.** -/
theorem isNNO_natAsm (A : Type u) [PCA A] :
    IsNNO (natZero.{u, v} A) (natSucc.{u, v} A) := by
  refine ⟨⟨isTerminalUnitAsm⟩, fun X q f => ?_⟩
  obtain ⟨rq, hrq⟩ := X.exists_realizer (q.toFun PUnit.unit)
  obtain ⟨rf, hrf⟩ := f.tracked
  refine ⟨⟨fun x => f.toFun^[x.down] (q.toFun PUnit.unit),
    ⟨iterEl rf rq, tracked_iter hrf hrq⟩⟩, ⟨?_, ?_⟩, ?_⟩
  · exact hom_ext fun x => by cases x; rfl
  · exact hom_ext fun x => (Function.iterate_succ_apply' _ _ _)
  · rintro m ⟨h₀, hs⟩
    refine hom_ext fun x => ?_
    obtain ⟨n⟩ := x
    induction n with
    | zero =>
        have := congrArg (fun k : unitAsm.{u, v} A ⟶ X => k.toFun PUnit.unit) h₀
        exact this
    | succ n ih =>
        have hstep : m.toFun ⟨n + 1⟩ = f.toFun (m.toFun ⟨n⟩) :=
          congrArg (fun k : natAsm.{u, v} A ⟶ X => k.toFun ⟨n⟩) hs
        have hih : f.toFun (m.toFun ⟨n⟩) = f.toFun (f.toFun^[n] (q.toFun PUnit.unit)) :=
          congrArg f.toFun ih
        exact hstep.trans (hih.trans
          (Function.iterate_succ_apply' f.toFun n (q.toFun PUnit.unit)).symm)

end Assembly

end Realizability
