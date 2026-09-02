/-
The standard assembly of natural numbers over Kleene's first algebra.

Over `K₁` — the natural numbers under Turing application — the natural numbers carry a second,
much more concrete assembly structure than the Church numerals of `Start/AssemblyNNO.lean`: a
number is realized by *itself*.  This file identifies the maps of that assembly and shows that it
is again a natural numbers object, so that the two structures are isomorphic in `Asm(K₁)`.

* `Realizability.Kleene.natK1` — the standard numbers assembly, `a` realizes `n` iff `a = n`, and
  `Realizability.Kleene.modest_natK1`;
* `Realizability.Kleene.tracked_natK1_iff` — **effective Church's thesis for `Asm(K₁)`**: a
  function `ℕ → ℕ` is tracked exactly when it is computable, so the endomorphisms of the standard
  numbers assembly are precisely the computable functions
  (`Realizability.Kleene.natK1EndEquiv`);
* `Realizability.Kleene.exists_not_tracked_natK1`, `.not_full_gammaFunctor` — some function of
  natural numbers is not tracked, so the global sections functor is not full and `Asm(K₁)` is not
  the category of sets;
* `Realizability.Kleene.tracked_prod_natK1_iff` — the same for binary functions, out of the
  product of two copies of the assembly;
* `Realizability.Kleene.realizes_expAsm_natK1`, `.expAsmNatK1Equiv` — the function object of the
  standard numbers assembly has the computable functions as elements and their indices as
  realizers;
* `Realizability.Kleene.isNNO_natK1` — the standard numbers assembly is a natural numbers object,
  and `Realizability.Kleene.natK1IsoNatAsm` — it is therefore isomorphic to the Church numeral
  object, the isomorphism being the effective conversion between numbers and numerals.

The uniqueness of a natural numbers object used for the last item is
`CategoryTheory.Limits.IsNNO.iso`, proved in `Start/AssemblyNNO.lean`.
-/

import Start.AssemblyCcc
import Start.AssemblyGlobalSections
import Start.AssemblyNNO
import Start.PCAKleene

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

namespace Kleene

open CategoryTheory CategoryTheory.Limits
open Nat.Partrec (Code)
open Nat.Partrec.Code
open Encodable Denumerable
open Realizability.Assembly

/-! ### The standard numbers assembly -/

/-- The **standard assembly of natural numbers** over `K₁`: a number realizes itself. -/
def natK1 : Assembly.{0, 0} ℕ where
  carrier := ℕ
  realizes a n := a = n
  exists_realizer n := ⟨n, rfl⟩

@[simp] theorem natK1_realizes (a n : ℕ) : natK1.realizes a n ↔ a = n := Iff.rfl

/-- The standard numbers assembly is modest: a realizer determines its element. -/
theorem modest_natK1 : natK1.Modest := by
  intro a x y hx hy
  exact ((hx : a = x).symm.trans (hy : a = y))

/-! ### The maps of the standard numbers assembly are the computable functions -/

theorem mem_natApp_encode {c : Code} {f : ℕ → ℕ} (hc : ∀ n, eval c n = Part.some (f n)) (n : ℕ) :
    f n ∈ natApp (encode c) n := by
  rw [natApp_encode, hc]
  exact Part.mem_some _

/-- **Effective Church's thesis in `Asm(K₁)`**: a function of natural numbers is tracked in
Kleene's first algebra exactly when it is computable. -/
theorem tracked_natK1_iff {f : ℕ → ℕ} : Tracked natK1 natK1 f ↔ Computable f := by
  constructor
  · rintro ⟨r, hr⟩
    have hmem : ∀ n : ℕ, f n ∈ natApp r n := by
      intro n
      obtain ⟨v, hv, hvx⟩ := hr n n rfl
      have hv' : v ∈ natApp r n := hv
      have : v = f n := hvx
      rwa [this] at hv'
    have hpart : Partrec fun n : ℕ => natApp r n :=
      Partrec₂.comp (f := natApp) partrec_natApp (Computable.const r) Computable.id
    refine hpart.of_eq fun n => ?_
    rw [Part.eq_some_iff.2 (hmem n)]
    rfl
  · intro hf
    obtain ⟨c, hc⟩ := exists_code_of_computable hf
    refine ⟨encode c, fun a n ha => ⟨f n, ?_, rfl⟩⟩
    have hna : a = n := ha
    exact hna ▸ mem_natApp_encode hc n

/-- The endomorphisms of the standard numbers assembly are exactly the computable functions. -/
noncomputable def natK1EndEquiv : (natK1 ⟶ natK1) ≃ {f : ℕ → ℕ // Computable f} where
  toFun g := ⟨g.toFun, tracked_natK1_iff.1 g.tracked⟩
  invFun f := ⟨f.1, tracked_natK1_iff.2 f.2⟩
  left_inv _ := AsmHom.ext rfl
  right_inv _ := Subtype.ext rfl

open scoped Classical in
/-- The diagonal function `n ↦ φₙ(n) + 1`, undefined values being sent to `0`. -/
noncomputable def diag (n : ℕ) : ℕ :=
  if h : (natApp n n).Dom then (natApp n n).get h + 1 else 0

/-- The diagonal function is not tracked, so the underlying-function map on `Asm(K₁)` misses some
functions of natural numbers: `Asm(K₁)` is not the category of sets. -/
theorem not_tracked_diag : ¬ Tracked natK1 natK1 diag := by
  intro h
  have hc : Computable diag := tracked_natK1_iff.1 h
  obtain ⟨c, hcc⟩ := exists_code_of_computable hc
  set r : ℕ := encode c with hr
  have hmem : diag r ∈ natApp r r := mem_natApp_encode hcc r
  have hdom : (natApp r r).Dom := Part.dom_iff_mem.2 ⟨_, hmem⟩
  have hget : (natApp r r).get hdom = diag r := Part.get_eq_of_mem hmem hdom
  have hstep : diag r = (natApp r r).get hdom + 1 := by
    classical
    rw [diag, dif_pos hdom]
  omega

/-- Not every function of natural numbers underlies a morphism of the standard numbers
assembly. -/
theorem exists_not_tracked_natK1 : ∃ f : ℕ → ℕ, ¬ Tracked natK1 natK1 f :=
  ⟨diag, not_tracked_diag⟩

/-- **Global sections do not see all functions**: the functor forgetting the realizers is not
full over Kleene's first algebra, since the diagonal function is a map of carriers underlying no
morphism of assemblies. -/
theorem not_full_gammaFunctor : ¬ (gammaFunctor.{0, 0} ℕ).Full := by
  intro h
  obtain ⟨g, hg⟩ := h.map_surjective (X := natK1) (Y := natK1) (↾ diag)
  have hfun : g.toFun = diag :=
    funext fun n => congrFun (congrArg (fun k : ℕ ⟶ ℕ => (k : ℕ → ℕ)) hg) n
  exact not_tracked_diag (hfun ▸ g.tracked)

/-! ### Binary functions: the product assembly -/

/-- Church pairing of `K₁` as a partial value: the pairing combinator applied to two numbers. -/
noncomputable def pairK1 (m n : ℕ) : Part ℕ :=
  (natApp (PCA.pairComb ℕ) m).bind fun u => natApp u n

theorem pairK1_eq (m n : ℕ) : pairK1 m n = Part.some (PCA.pairEl m n) := by
  have h := PCA.pairComb_app (A := ℕ) m n
  rw [papp_some_some (PCA.pairComb ℕ) m] at h
  simp only [papp, Part.bind_some] at h
  exact h

theorem partrec_pairK1 : Partrec₂ pairK1 := by
  refine Partrec.bind (Partrec₂.comp (f := natApp) partrec_natApp
    (Computable.const (PCA.pairComb ℕ)) Computable.fst) ?_
  exact Partrec₂.comp (f := natApp) partrec_natApp Computable.snd
    (Computable.snd.comp Computable.fst)

/-- Church pairing is computable in Kleene's first algebra. -/
theorem computable_pairEl : Computable fun z : ℕ × ℕ => PCA.pairEl z.1 z.2 := by
  refine (partrec_pairK1.comp Computable.fst Computable.snd).of_eq fun z => ?_
  rw [pairK1_eq]
  rfl

theorem natApp_fstComb_pairEl (m n : ℕ) :
    natApp (PCA.fstComb ℕ) (PCA.pairEl m n) = Part.some m := by
  have h := PCA.fstComb_pairEl (A := ℕ) m n
  rwa [papp_some_some] at h

theorem natApp_sndComb_pairEl (m n : ℕ) :
    natApp (PCA.sndComb ℕ) (PCA.pairEl m n) = Part.some n := by
  have h := PCA.sndComb_pairEl (A := ℕ) m n
  rwa [papp_some_some] at h

theorem mem_natApp_pair_code {c : Code} {f : ℕ × ℕ → ℕ}
    (hc : eval c = fun p : ℕ => (natApp (PCA.fstComb ℕ) p).bind fun m =>
      (natApp (PCA.sndComb ℕ) p).bind fun n => Part.some (f (m, n))) (a b : ℕ) :
    f (a, b) ∈ natApp (encode c) (PCA.pairEl a b) := by
  rw [natApp_encode, hc]
  simp only [natApp_fstComb_pairEl, Part.bind_some, natApp_sndComb_pairEl]
  exact Part.mem_some _

/-- **Effective Church's thesis for binary functions**: a function of two natural numbers is
tracked out of the product of two copies of the standard numbers assembly exactly when it is
computable.  A tracker must be applied to a Church pair, which is computed from its two components
and decomposed again by the two projection combinators. -/
theorem tracked_prod_natK1_iff {f : ℕ × ℕ → ℕ} :
    Tracked (prodAsm natK1 natK1) natK1 f ↔ Computable f := by
  constructor
  · rintro ⟨r, hr⟩
    have hmem : ∀ z : ℕ × ℕ, f z ∈ natApp r (PCA.pairEl z.1 z.2) := by
      intro z
      obtain ⟨v, hv, hvx⟩ := hr (PCA.pairEl z.1 z.2) z ⟨z.1, z.2, rfl, rfl, rfl⟩
      have hv' : v ∈ natApp r (PCA.pairEl z.1 z.2) := hv
      have hveq : v = f z := hvx
      rwa [hveq] at hv'
    have hpart : Partrec fun z : ℕ × ℕ => natApp r (PCA.pairEl z.1 z.2) :=
      Partrec₂.comp (f := natApp) partrec_natApp (Computable.const r) computable_pairEl
    refine hpart.of_eq fun z => ?_
    rw [Part.eq_some_iff.2 (hmem z)]
    rfl
  · intro hf
    have hpart : Partrec fun p : ℕ => (natApp (PCA.fstComb ℕ) p).bind fun m =>
        (natApp (PCA.sndComb ℕ) p).bind fun n => Part.some (f (m, n)) := by
      refine Partrec.bind (Partrec₂.comp (f := natApp) partrec_natApp
        (Computable.const (PCA.fstComb ℕ)) Computable.id) ?_
      refine Partrec.bind (Partrec₂.comp (f := natApp) partrec_natApp
        (Computable.const (PCA.sndComb ℕ)) Computable.fst) ?_
      exact (hf.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)).partrec
    obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 hpart)
    refine ⟨encode c, fun p z hz => ?_⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    refine ⟨f z, ?_, rfl⟩
    have h1 : a = z.1 := ha
    have h2 : b = z.2 := hb
    have hz : (z : ℕ × ℕ) = (a, b) := Prod.ext h1.symm h2.symm
    have hfz : f z = f (a, b) := congrArg f hz
    rw [hfz]
    exact mem_natApp_pair_code hc a b

/-! ### The function object -/

/-- A realizer of an element of the function object `natK1 ⇒ natK1` is exactly an **index** for
the function: the machine it names must converge on every input to the value of the function. -/
theorem realizes_expAsm_natK1 (r : ℕ) (f : (expAsm natK1 natK1).carrier) :
    (expAsm natK1 natK1).realizes r f ↔ ∀ n : ℕ, f.1 n ∈ natApp r n := by
  constructor
  · intro hr n
    obtain ⟨v, hv, hvx⟩ := hr n n rfl
    have hv' : v ∈ natApp r n := hv
    have hveq : v = f.1 n := hvx
    rwa [hveq] at hv'
  · intro hr a n ha
    have hna : a = n := ha
    exact ⟨f.1 n, hna ▸ hr n, rfl⟩

/-- The carrier of the function object `natK1 ⇒ natK1` is the set of computable functions. -/
noncomputable def expAsmNatK1Equiv :
    (expAsm natK1 natK1).carrier ≃ {f : ℕ → ℕ // Computable f} where
  toFun f := ⟨f.1, tracked_natK1_iff.1 f.2⟩
  invFun f := ⟨f.1, tracked_natK1_iff.2 f.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-! ### Zero and successor -/

theorem mem_natApp_kFun (a b : ℕ) : b ∈ natApp (kFun b) a := by
  rw [natApp_kFun]
  exact Part.mem_some _

/-- Zero, realized by the number `0`. -/
noncomputable def zeroK1 : unitAsm.{0, 0} ℕ ⟶ natK1 where
  toFun _ := (0 : ℕ)
  tracked := ⟨kFun 0, fun a _ _ => ⟨0, mem_natApp_kFun a 0, rfl⟩⟩

/-- The successor map of the standard numbers assembly. -/
noncomputable def succK1 : natK1 ⟶ natK1 where
  toFun := Nat.succ
  tracked := tracked_natK1_iff.2 Computable.succ

@[simp] theorem zeroK1_toFun (x : (unitAsm.{0, 0} ℕ).carrier) : zeroK1.toFun x = (0 : ℕ) := rfl

@[simp] theorem succK1_toFun (n : ℕ) : succK1.toFun n = n + 1 := rfl

/-! ### The standard numbers assembly is a natural numbers object -/

/-- The `n`-fold Turing application of `t` to `b`, as a partial value. -/
def iterApp (t b : ℕ) (n : ℕ) : Part ℕ :=
  Nat.rec (Part.some b) (fun _ IH => IH.bind fun i => natApp t i) n

@[simp] theorem iterApp_zero (t b : ℕ) : iterApp t b 0 = Part.some b := rfl

theorem iterApp_succ (t b n : ℕ) :
    iterApp t b (n + 1) = (iterApp t b n).bind fun i => natApp t i := rfl

theorem partrec_iterApp (t b : ℕ) : Partrec (iterApp t b) := by
  have h := Partrec.nat_rec (f := fun n : ℕ => n) (g := fun _ : ℕ => (Part.some b : Part ℕ))
    (h := fun (_ : ℕ) (p : ℕ × ℕ) => natApp t p.2) Computable.id
    (Computable.const b).partrec
    (Partrec₂.comp (f := natApp) partrec_natApp (Computable.const t)
      (Computable.snd.comp Computable.snd))
  exact h.of_eq fun n => rfl

/-- An element of `K₁` performing the iteration: it maps `n` to the `n`-fold Turing application
of `t` to `b`. -/
noncomputable def iterK1 (t b : ℕ) : ℕ :=
  encode (exists_code.1 (Partrec.nat_iff.1 (partrec_iterApp t b))).choose

theorem natApp_iterK1 (t b n : ℕ) : natApp (iterK1 t b) n = iterApp t b n := by
  rw [iterK1, natApp_encode]
  exact congrFun (exists_code.1 (Partrec.nat_iff.1 (partrec_iterApp t b))).choose_spec n

variable {X : Assembly.{0, 0} ℕ}

theorem exists_mem_iterApp {t b : ℕ} {f : X.carrier → X.carrier}
    (ht : RealizesFun X X t f) {x0 : X.carrier} (hb : X.realizes b x0) (n : ℕ) :
    ∃ v ∈ iterApp t b n, X.realizes v (f^[n] x0) := by
  induction n with
  | zero => exact ⟨b, Part.mem_some _, hb⟩
  | succ n ih =>
      obtain ⟨v, hv, hvx⟩ := ih
      obtain ⟨w, hw, hwx⟩ := ht v (f^[n] x0) hvx
      refine ⟨w, ?_, ?_⟩
      · rw [iterApp_succ]
        exact Part.mem_bind_iff.2 ⟨v, hv, hw⟩
      · rwa [Function.iterate_succ_apply']

theorem tracked_iterK1 {t b : ℕ} {f : X.carrier → X.carrier} (ht : RealizesFun X X t f)
    {x0 : X.carrier} (hb : X.realizes b x0) :
    RealizesFun natK1 X (iterK1 t b) fun n => f^[n] x0 := by
  intro a n ha
  have hna : a = n := ha
  subst hna
  obtain ⟨v, hv, hvx⟩ := exists_mem_iterApp ht hb a
  refine ⟨v, ?_, hvx⟩
  have : v ∈ natApp (iterK1 t b) a := by rw [natApp_iterK1]; exact hv
  exact this

/-- **The standard assembly of natural numbers is a natural numbers object** in `Asm(K₁)`. -/
theorem isNNO_natK1 : IsNNO zeroK1 succK1 := by
  refine ⟨⟨isTerminalUnitAsm⟩, fun X q f => ?_⟩
  obtain ⟨b, hb⟩ := X.exists_realizer (q.toFun PUnit.unit)
  obtain ⟨t, ht⟩ := f.tracked
  refine ⟨⟨fun n => f.toFun^[n] (q.toFun PUnit.unit), ⟨iterK1 t b, tracked_iterK1 ht hb⟩⟩,
    ⟨?_, ?_⟩, ?_⟩
  · exact hom_ext fun x => by cases x; rfl
  · exact hom_ext fun n => Function.iterate_succ_apply' _ _ _
  · rintro m ⟨h₀, hs⟩
    refine hom_ext fun n => ?_
    induction n with
    | zero => exact congrArg (fun k : unitAsm.{0, 0} ℕ ⟶ X => k.toFun PUnit.unit) h₀
    | succ n ih =>
        have hstep : m.toFun (n + 1) = f.toFun (m.toFun n) :=
          congrArg (fun k : natK1 ⟶ X => k.toFun n) hs
        exact hstep.trans ((congrArg f.toFun ih).trans
          (Function.iterate_succ_apply' f.toFun n (q.toFun PUnit.unit)).symm)

/-- The standard numbers assembly is isomorphic to the Church numeral one: numbers and numerals
are effectively interconvertible in `K₁`. -/
noncomputable def natK1IsoNatAsm : natK1 ≅ natAsm.{0, 0} ℕ :=
  isNNO_natK1.iso (isNNO_natAsm ℕ)

end Kleene

end Realizability
