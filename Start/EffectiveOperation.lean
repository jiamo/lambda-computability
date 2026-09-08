/-
**The Myhill–Shepherdson theorem: an effective operation is continuous.**

An *effective operation* on the partial computable functions is an algorithm on **indices** that
respects the function named: a partial computable `Ψ : ℕ →. ℕ` such that `Ψ e` depends only on
`φ_e`.  Nothing in that definition says that `Ψ e` may only inspect finitely much of `φ_e` — the
algorithm is handed a program, and a program is a finite object that determines the whole of the
infinite graph.  The Myhill–Shepherdson theorem says that it makes no difference: an effective
operation is automatically **monotone** and **continuous** for the Scott topology, that is, its
value is already produced by a finite part of the argument.

The proofs are the ones the module `Start/RiceShapiro.lean` uses for the analogous statements
about r.e. sets: from a failure of the theorem one builds a computable family of programs whose
membership in the class `{e | v ∈ Ψ e}` is exactly *non*-membership in the halting set, so the
complement of the halting set would be r.e. (`Lambda.Post.false_of_compl_haltK_iff`).

* `Lambda.Post.phi` — the partial function named by an index, and `Lambda.Post.exists_index_eval`,
  the s-m-n theorem in the form that names a partial computable family *with its values*;
* `Lambda.Post.ExtensionalOp` — the operation depends only on the function named;
* `Lambda.Post.SubFun`, `.FiniteDom` — a subfunction, and a finite domain;
* `Lambda.Post.effop_mono` — **monotonicity**: an effective operation cannot lose a value when
  its argument is extended;
* `Lambda.Post.effop_finite_witness` — **compactness**: a value of an effective operation is
  already produced by a finite subfunction of its argument;
* `Lambda.Post.effop_continuous` — the two together, in the form of Scott continuity;
* `Lambda.Post.effop_const_of_empty` — a consequence: an effective operation that already has a
  value at the nowhere-defined function has that same value everywhere, so it cannot test for
  divergence.

The theorem is the partial-function half of the classical picture.  Its counterpart for *total*
computable functions — the Kreisel–Lacombe–Shoenfield theorem — is not proved here; the type-two
form of continuity, for functions computed from names rather than from indices, is
`Start/ComputableReal.lean`.
-/

import Start.RiceShapiro

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

namespace Post

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### Indices and the functions they name -/

/-- The partial function named by an index. -/
def phi (e : ℕ) : ℕ →. ℕ := Code.eval (ofNat Code e)

theorem wset_iff_phi_dom (e x : ℕ) : Wset e x ↔ (phi e x).Dom := Iff.rfl

/-- **The s-m-n theorem, with values**: a partial computable family of partial functions is
named by a computable family of indices. -/
theorem exists_index_eval (F : ℕ → ℕ →. ℕ) (hF : Partrec₂ F) :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ n, phi (h n) = F n := by
  have hG : Nat.Partrec fun q : ℕ => F (Nat.unpair q).1 (Nat.unpair q).2 :=
    Partrec.nat_iff.1 (hF.comp (Computable.fst.comp Primrec.unpair.to_comp)
      (Computable.snd.comp Primrec.unpair.to_comp))
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hG
  refine ⟨fun n => Encodable.encode (Code.curry c n),
    (Primrec.encode.comp (Nat.Partrec.Code.primrec₂_curry.comp
      (Primrec.const c) Primrec.id)).to_comp, fun n => ?_⟩
  funext x
  simp only [phi, Denumerable.ofNat_encode, Code.eval_curry, hc]
  simp

/-! ### Effective operations -/

/-- An **effective operation**: the value depends only on the function named by the index. -/
def ExtensionalOp (Psi : ℕ →. ℕ) : Prop := ∀ e d : ℕ, phi e = phi d → Psi e = Psi d

/-- `SubFun d e` : the function named by `d` is a restriction of the one named by `e`. -/
def SubFun (d e : ℕ) : Prop := ∀ x v : ℕ, v ∈ phi d x → v ∈ phi e x

/-- The function named by `d` is defined at finitely many points. -/
def FiniteDom (d : ℕ) : Prop := {x : ℕ | (phi d x).Dom}.Finite

/-- The class of indices at which an effective operation takes a given value is r.e. -/
theorem rePred_value {Psi : ℕ →. ℕ} (hPsi : Partrec Psi) (v : ℕ) :
    REPred fun e => v ∈ Psi e := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 (Partrec.nat_iff.1 hPsi)
  have hev : Primrec fun q : ℕ × ℕ => Code.evaln q.2 c q.1 :=
    Code.primrec_evaln.comp ((Primrec.snd.pair (Primrec.const c)).pair Primrec.fst)
  refine rePred_of_exists_comp (fun e s => decide (Code.evaln s c e = some v))
    ((Primrec.eq.comp hev (Primrec.const (some v))).decide).to_comp fun e => ?_
  constructor
  · intro hv
    rw [← hc] at hv
    obtain ⟨s, hs⟩ := Code.evaln_complete.1 hv
    exact ⟨s, by simp [Option.mem_def.1 hs]⟩
  · rintro ⟨s, hs⟩
    have hval : Code.evaln s c e = some v := of_decide_eq_true hs
    have := Code.evaln_sound hval
    rwa [hc] at this

/-! ### The universal halting function -/

/-- The search for a stage at which `n` enters the halting set: a partial function defined at `n`
exactly when `n` is in the halting set. -/
def kPart (n : ℕ) : Part ℕ := Nat.rfind fun s => Part.some (acc n s n)

theorem partrec_kPart : Partrec kPart :=
  Partrec.rfind (Computable₂.partrec₂
    (computable_acc Computable.fst Computable.snd Computable.fst))

theorem kPart_dom_iff (n : ℕ) : (kPart n).Dom ↔ HaltK n := by
  rw [haltK_iff_exists_acc]
  constructor
  · intro h
    obtain ⟨s, hs, -⟩ := Nat.rfind_dom.1 h
    exact ⟨s, by simpa using hs⟩
  · rintro ⟨s, hs⟩
    exact Nat.rfind_dom.2 ⟨s, by simp [hs], fun {_} _ => trivial⟩

/-! ### The functions named by indices are partial computable -/

theorem partrec_phi_snd (e : ℕ) : Partrec fun q : ℕ × ℕ => phi e q.2 :=
  Code.eval_part.comp (Computable.const (ofNat Code e)) Computable.snd

theorem partrec_phi_snd_fst (e : ℕ) : Partrec₂ fun (q : ℕ × ℕ) (_ : ℕ) => phi e q.2 :=
  Code.eval_part.comp (Computable.const (ofNat Code e)) (Computable.snd.comp Computable.fst)

/-! ### Monotonicity -/

/-- **An effective operation is monotone.**  If it takes the value `v` at `e` and the function
named by `e` is a restriction of the one named by `d`, then it takes the value `v` at `d`.

Otherwise the family `φ (h n) = φ e ∪ (φ d if n halts)` would satisfy `n ∉ K ↔ v ∈ Ψ (h n)`. -/
theorem effop_mono {Psi : ℕ →. ℕ} (hPsi : Partrec Psi) (hext : ExtensionalOp Psi)
    {e d v : ℕ} (he : v ∈ Psi e) (hsub : SubFun e d) : v ∈ Psi d := by
  by_contra hnd
  -- the two branches: the function named by `e`, and the one named by `d` guarded by `n ∈ K`
  have hf : Partrec fun q : ℕ × ℕ => phi e q.2 := partrec_phi_snd e
  have hg : Partrec fun q : ℕ × ℕ => (kPart q.1).bind fun _ => phi d q.2 :=
    (partrec_kPart.comp Computable.fst).bind (partrec_phi_snd_fst d)
  have hagree : ∀ q : ℕ × ℕ, ∀ x ∈ (fun q : ℕ × ℕ => phi e q.2) q,
      ∀ y ∈ (fun q : ℕ × ℕ => (kPart q.1).bind fun _ => phi d q.2) q, x = y := by
    rintro ⟨n, x⟩ u hu w hw
    rw [Part.mem_bind_iff] at hw
    obtain ⟨-, -, hw⟩ := hw
    exact Part.mem_unique (hsub x u hu) hw
  obtain ⟨k, hk, hkspec⟩ := Partrec.merge hf hg hagree
  obtain ⟨h, hh, hhspec⟩ := exists_index_eval (fun n x => k (n, x)) hk
  refine false_of_compl_haltK_iff (rePred_value hPsi v) hh fun n => ?_
  constructor
  · -- `n` does not halt: the family names the function of `e`
    intro hn
    have : phi (h n) = phi e := by
      rw [hhspec n]
      funext x
      apply Part.ext
      intro u
      rw [hkspec (n, x) u]
      constructor
      · rintro (hu | hu)
        · exact hu
        · rw [Part.mem_bind_iff] at hu
          obtain ⟨w, hw, -⟩ := hu
          exact absurd ((kPart_dom_iff n).1 hw.fst) hn
      · exact Or.inl
    rw [hext _ _ this]
    exact he
  · -- `n` halts: the family names the function of `d`, at which the value is not `v`
    intro hv
    by_contra hn
    have hdom : (kPart n).Dom := (kPart_dom_iff n).2 hn
    have : phi (h n) = phi d := by
      rw [hhspec n]
      funext x
      apply Part.ext
      intro u
      rw [hkspec (n, x) u]
      constructor
      · rintro (hu | hu)
        · exact hsub x u hu
        · rw [Part.mem_bind_iff] at hu
          obtain ⟨-, -, hu⟩ := hu
          exact hu
      · intro hu
        refine Or.inr ?_
        rw [Part.mem_bind_iff]
        exact ⟨(kPart n).get hdom, Part.get_mem hdom, hu⟩
    rw [hext _ _ this] at hv
    exact hnd hv

/-! ### Cutting a computation off at a stage -/

/-- `cutTest e n x s` : the computation of `φ e x` has converged by stage `s`, and `n` has not
entered the halting set by stage `s`. -/
def cutTest (e n x s : ℕ) : Bool := (Code.evaln s (ofNat Code e) x).isSome && !(acc n s n)

/-- The function named by `e`, cut off at the stage at which `n` enters the halting set: the
whole of `φ e` if `n` never enters, a finite restriction of it if it does. -/
def cutFun (e n : ℕ) : ℕ →. ℕ := fun x =>
  (Nat.rfind fun s => Part.some (cutTest e n x s)).bind fun s =>
    ((Code.evaln s (ofNat Code e) x : Option ℕ) : Part ℕ)

theorem primrec_cutTest (e : ℕ) :
    Computable fun q : (ℕ × ℕ) × ℕ => cutTest e q.1.1 q.1.2 q.2 := by
  have hev : Primrec fun q : (ℕ × ℕ) × ℕ => Code.evaln q.2 (ofNat Code e) q.1.2 :=
    Code.primrec_evaln.comp ((Primrec.snd.pair (Primrec.const (ofNat Code e))).pair
      (Primrec.snd.comp Primrec.fst))
  have hacc : Computable fun q : (ℕ × ℕ) × ℕ => acc q.1.1 q.2 q.1.1 :=
    computable_acc (Computable.fst.comp Computable.fst) Computable.snd
      (Computable.fst.comp Computable.fst)
  exact (Primrec.dom_bool₂ (fun a b => a && b)).to_comp.comp
    (Primrec.option_isSome.comp hev).to_comp
    ((Primrec.dom_bool (fun b => !b)).to_comp.comp hacc)

theorem partrec_cutFun (e : ℕ) : Partrec₂ (cutFun e) := by
  have hrfind : Partrec fun q : ℕ × ℕ =>
      Nat.rfind fun s => Part.some (cutTest e q.1 q.2 s) :=
    Partrec.rfind (Computable₂.partrec₂ (primrec_cutTest e))
  refine hrfind.bind ?_
  exact Computable.ofOption
    ((Code.primrec_evaln.comp ((Primrec.snd.pair (Primrec.const (ofNat Code e))).pair
      (Primrec.snd.comp Primrec.fst))).to_comp)

/-- What the cut-off function computes. -/
theorem mem_cutFun_iff {e n x u : ℕ} :
    u ∈ cutFun e n x ↔ ∃ s, cutTest e n x s = Bool.true ∧
      Code.evaln s (ofNat Code e) x = some u := by
  constructor
  · intro hu
    rw [cutFun, Part.mem_bind_iff] at hu
    obtain ⟨s, hs, hu⟩ := hu
    refine ⟨s, ?_, ?_⟩
    · simpa using Nat.rfind_spec hs
    · simpa using hu
  · rintro ⟨s, hs, hval⟩
    have hdom : (Nat.rfind fun t => Part.some (cutTest e n x t)).Dom :=
      Nat.rfind_dom.2 ⟨s, by simp [hs], fun {_} _ => trivial⟩
    set t := (Nat.rfind fun t => Part.some (cutTest e n x t)).get hdom with ht
    have htmem : t ∈ Nat.rfind fun t => Part.some (cutTest e n x t) := Part.get_mem hdom
    have httrue : cutTest e n x t = Bool.true := by simpa using Nat.rfind_spec htmem
    have htsome : (Code.evaln t (ofNat Code e) x).isSome = Bool.true := by
      simpa [cutTest] using (Bool.and_eq_true_iff.1 httrue).1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 htsome
    have hwu : w = u :=
      Part.mem_unique (Code.evaln_sound hw) (Code.evaln_sound hval)
    rw [cutFun, Part.mem_bind_iff]
    exact ⟨t, htmem, by simp [hw, hwu]⟩

/-! ### Compactness -/

/-- **An effective operation is compact.**  A value it takes at `e` is already taken at some
finite restriction of the function named by `e`.

Otherwise the family `φ (h n) = φ e` cut off at the stage at which `n` enters `K` — the whole of
`φ e` when `n` never enters, a finite restriction of it when it does — would satisfy
`n ∉ K ↔ v ∈ Ψ (h n)`. -/
theorem effop_finite_witness {Psi : ℕ →. ℕ} (hPsi : Partrec Psi) (hext : ExtensionalOp Psi)
    {e v : ℕ} (he : v ∈ Psi e) : ∃ d, SubFun d e ∧ FiniteDom d ∧ v ∈ Psi d := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h, hh, hhspec⟩ := exists_index_eval (cutFun e) (partrec_cutFun e)
  have hsub : ∀ n, SubFun (h n) e := by
    intro n x u hu
    rw [hhspec n] at hu
    obtain ⟨s, -, hval⟩ := mem_cutFun_iff.1 hu
    exact Code.evaln_sound hval
  refine false_of_compl_haltK_iff (rePred_value hPsi v) hh fun n => ?_
  constructor
  · -- `n` does not halt: the family names the whole of `φ e`
    intro hn
    have hnacc : ∀ s, acc n s n = Bool.false := by
      intro s
      by_contra hs
      exact hn ((haltK_iff_exists_acc n).2 ⟨s, by simpa using hs⟩)
    have heq : phi (h n) = phi e := by
      funext x
      apply Part.ext
      intro u
      rw [hhspec n]
      constructor
      · intro hu
        obtain ⟨s, -, hval⟩ := mem_cutFun_iff.1 hu
        exact Code.evaln_sound hval
      · intro hu
        obtain ⟨s, hs⟩ := Code.evaln_complete.1 hu
        have hval : Code.evaln s (ofNat Code e) x = some u := Option.mem_def.1 hs
        exact mem_cutFun_iff.2 ⟨s, by simp [cutTest, hval, hnacc s], hval⟩
    rw [hext _ _ heq]
    exact he
  · intro hv
    by_contra hn
    -- `n` halts, so the family names a finite restriction of `φ e`
    obtain ⟨s₀, hs₀⟩ := (haltK_iff_exists_acc n).1 hn
    have hfin : FiniteDom (h n) := by
      refine Set.Finite.subset (Set.finite_Iio s₀) ?_
      intro x hx
      simp only [Set.mem_ofPred_eq, hhspec n] at hx
      obtain ⟨u, hu⟩ := Part.dom_iff_mem.1 hx
      obtain ⟨s, hs, hval⟩ := mem_cutFun_iff.1 hu
      have hne : acc n s n = Bool.false := by
        simpa [cutTest] using (Bool.and_eq_true_iff.1 hs).2
      have hslt : s < s₀ := by
        by_contra hge
        exact absurd (acc_mono (not_lt.1 hge) hs₀) (by simp [hne])
      exact Set.mem_Iio.2 (lt_trans (Code.evaln_bound hval) hslt)
    exact hcon _ (hsub n) hfin hv

/-- An effective operation with a value at the nowhere-defined function takes that value at every
index: the nowhere-defined function is a restriction of every function, so monotonicity applies.
An effective operation therefore cannot answer one thing on a divergent computation and another
thing on a convergent one. -/
theorem effop_const_of_empty {Psi : ℕ →. ℕ} (hPsi : Partrec Psi) (hext : ExtensionalOp Psi)
    {e v : ℕ} (hempty : ∀ x, ¬ (phi e x).Dom) (he : v ∈ Psi e) (d : ℕ) : v ∈ Psi d :=
  effop_mono hPsi hext he fun x _ hu => absurd hu.fst (hempty x)

/-- **The Myhill–Shepherdson theorem**: an effective operation is Scott continuous — it takes a
value at an index exactly when it takes it at some index of a finite restriction. -/
theorem effop_continuous {Psi : ℕ →. ℕ} (hPsi : Partrec Psi) (hext : ExtensionalOp Psi)
    (e v : ℕ) : v ∈ Psi e ↔ ∃ d, SubFun d e ∧ FiniteDom d ∧ v ∈ Psi d := by
  constructor
  · exact effop_finite_witness hPsi hext
  · rintro ⟨d, hsub, -, hv⟩
    exact effop_mono hPsi hext hv hsub

end Post

end Lambda
