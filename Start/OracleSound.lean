/-
**Soundness of the oracle-machine indexing.**

`Start/OracleSim.lean` shows that every partial function recursive in an oracle `A` is computed by
some machine `Φ_e^A`.  This file proves the converse: each `Φ_e^A` is itself recursive in `A`.
Together the two give the exact characterisation

```
RecursiveIn {oracleFun A} f ↔ ∃ e, Phi A e = f
```

(`Lambda.Oracle.recursiveIn_iff_exists_index`), so the indexed family `Φ^A` really enumerates the
partial functions of the Turing degree cone below `A`.

The proof runs the stage function of the machine relative to the oracle: the initial segments
`segNum A s` are computable in `A` (`Lambda.Oracle.recursiveIn_segNum`, by primitive recursion on
`s` with one oracle query at each step), the step function is a primitive recursive post-processing
of them (`Lambda.Oracle.recursiveIn_stageFun`), and the machine itself is an `rfind` over the
stages followed by reading off the value.
-/

import Start.OracleSim

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)
open scoped Computability

variable {A : ℕ → Bool}

/-- Relative recursiveness only depends on the function, so it transfers along pointwise
equalities. -/
theorem recursiveIn_of_eq {O : Set (ℕ →. ℕ)} {f g : ℕ →. ℕ} (hf : RecursiveIn O f)
    (h : ∀ n, f n = g n) : RecursiveIn O g := by
  have hfg : f = g := funext h
  rwa [hfg] at hf

/-- A partial recursive function is recursive in any set of oracles. -/
theorem recursiveIn_of_partrec {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : Nat.Partrec f) :
    RecursiveIn O f :=
  RecursiveIn.iff_nat.mpr hf.recursiveIn

theorem recursiveIn_oracleFun : RecursiveIn {oracleFun A} (oracleFun A) :=
  RecursiveIn.oracle _ (by simp)

/-- Binding, with the original input still available to the continuation. -/
theorem recursiveIn_bindPair {O : Set (ℕ →. ℕ)} {f g : ℕ →. ℕ} (hf : RecursiveIn O f)
    (hg : RecursiveIn O g) :
    RecursiveIn O fun n => (g n).bind fun v => f (Nat.pair n v) := by
  have hid : RecursiveIn O fun n : ℕ => Part.some n :=
    recursiveIn_of_partrec (Partrec.nat_iff.1 Computable.id.partrec)
  have hmap : RecursiveIn O fun n => Part.map (Nat.pair n) (g n) :=
    recursiveIn_of_eq (recIn_pair hid hg) fun n => by simp [Seq.seq]
  exact recursiveIn_of_eq (recIn_comp hf hmap) fun n => Part.bind_map (Nat.pair n) (g n) f

/-- Composing a relatively recursive function with a partial recursive one. -/
theorem recursiveIn_compPartrec {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : RecursiveIn O f)
    {g : ℕ → ℕ} (hg : Computable g) : RecursiveIn O fun n => f (g n) :=
  recursiveIn_of_eq (recIn_comp hf (recursiveIn_of_partrec (Partrec.nat_iff.1 hg.partrec)))
    fun n => Part.bind_some (g n) f

/-- Extending a coded oracle segment by one answer. -/
def segAppend (sigma b : ℕ) : ℕ := encode (segDecode sigma ++ [if b = 1 then true else false])

theorem primrec_segAppend : Primrec₂ segAppend := by
  have hdec : Primrec fun sigma : ℕ => segDecode sigma :=
    Primrec.option_getD.comp (Primrec.decode (α := List Bool)) (Primrec.const [])
  have h : Primrec₂ fun sigma b : ℕ =>
      encode (segDecode sigma ++ [if b = 1 then true else false]) :=
    Primrec.encode.comp (Primrec.list_append.comp (hdec.comp Primrec.fst)
      (Primrec.list_cons.comp
        (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
          (Primrec.const true) (Primrec.const false)) (Primrec.const [])))
  exact h

theorem segNum_succ (A : ℕ → Bool) (s : ℕ) :
    segNum A (s + 1) = segAppend (segNum A s) (if A s then 1 else 0) := by
  have hb : (if (if A s then 1 else 0) = 1 then true else false) = A s := by
    by_cases h : A s <;> simp [h]
  rw [segAppend, segDecode_segNum, hb]
  simp [segNum, segList, List.range_succ]

/-- The initial segments of the oracle are computable relative to the oracle. -/
theorem recursiveIn_segNum (A : ℕ → Bool) :
    RecursiveIn {oracleFun A} fun s => (Part.some (segNum A s) : Part ℕ) := by
  have hquery : RecursiveIn {oracleFun A} fun u : ℕ => oracleFun A u.unpair.2.unpair.1 :=
    recursiveIn_compPartrec (recursiveIn_oracleFun (A := A))
      (Primrec.to_comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
  have hpost : Nat.Partrec fun w : ℕ =>
      (Part.some (segAppend w.unpair.1.unpair.2.unpair.2 w.unpair.2) : Part ℕ) :=
    Partrec.nat_iff.1 (Primrec.to_comp (primrec_segAppend.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp
        (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))))
      (Primrec.snd.comp Primrec.unpair))).partrec
  have hstep := recursiveIn_bindPair (recursiveIn_of_partrec hpost) hquery
  have hzero : RecursiveIn {oracleFun A} fun _ : ℕ => (Part.some 0 : Part ℕ) :=
    recursiveIn_of_partrec Nat.Partrec.zero
  have hprec := recIn_prec hzero hstep
  have hbody : ∀ n : ℕ, (Nat.rec (motive := fun _ => Part ℕ) (Part.some 0)
      (fun y IH => IH.bind fun i => Part.some (segAppend i (if A y then 1 else 0))) n) =
      Part.some (segNum A n) := by
    intro n
    induction n with
    | zero => simp [segNum, segList]
    | succ n ih => simp [ih, segNum_succ A n]
  have hprec' : RecursiveIn {oracleFun A} fun p : ℕ =>
      (Part.some (segNum A p.unpair.2) : Part ℕ) :=
    recursiveIn_of_eq hprec fun p => by simpa [oracleFun] using hbody p.unpair.2
  exact recursiveIn_of_eq
    (recursiveIn_compPartrec hprec'
      (Primrec.to_comp (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id)))
    fun s => by simp

/-! ## Oracle machines are computable relative to the oracle -/

/-- Coding an `Option ℕ` by a number: `none` becomes `0`, `some y` becomes `y + 1`. -/
def optEnc (o : Option ℕ) : ℕ := (o.map Nat.succ).getD 0

theorem primrec_optEnc : Primrec optEnc :=
  Primrec.option_getD.comp (Primrec.option_map Primrec.id (Primrec.succ.comp Primrec.snd).to₂)
    (Primrec.const 0)

/-- The stage function of the `e`-th machine, as a partial function of the pair `(x, s)`. -/
noncomputable def stageFun (A : ℕ → Bool) (e : ℕ) : ℕ →. ℕ := fun w =>
  Part.some (optEnc (oracleStep A (ofNat Code e) w.unpair.1 w.unpair.2))

theorem recursiveIn_stageFun (A : ℕ → Bool) (e : ℕ) :
    RecursiveIn {oracleFun A} (stageFun A e) := by
  have hseg : RecursiveIn {oracleFun A} fun w : ℕ =>
      (Part.some (segNum A w.unpair.2.unpair.2) : Part ℕ) :=
    recursiveIn_compPartrec (recursiveIn_segNum A)
      (Primrec.to_comp (Primrec.snd.comp (Primrec.unpair.comp
        (Primrec.snd.comp Primrec.unpair))))
  have hpost : Nat.Partrec fun u : ℕ =>
      (Part.some (optEnc (Code.evaln u.unpair.1.unpair.2.unpair.1 (ofNat Code e)
        (Nat.pair u.unpair.2 u.unpair.1.unpair.1))) : Part ℕ) := by
    have hfuel : Primrec fun u : ℕ => u.unpair.1.unpair.2.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    have hinp : Primrec fun u : ℕ => Nat.pair u.unpair.2 u.unpair.1.unpair.1 :=
      Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    have harg : Primrec fun u : ℕ => ((u.unpair.1.unpair.2.unpair.1, ofNat Code e),
        Nat.pair u.unpair.2 u.unpair.1.unpair.1) :=
      Primrec.pair (Primrec.pair hfuel (Primrec.const (ofNat Code e))) hinp
    exact Partrec.nat_iff.1
      (Primrec.to_comp (primrec_optEnc.comp (Code.primrec_evaln.comp harg))).partrec
  exact recursiveIn_of_eq (recursiveIn_bindPair (recursiveIn_of_partrec hpost) hseg)
    fun w => by simp [stageFun, oracleStep]

@[simp] theorem optEnc_none : optEnc none = 0 := rfl

@[simp] theorem optEnc_some (y : ℕ) : optEnc (some y) = y + 1 := rfl

theorem optEnc_eq_zero_iff {o : Option ℕ} : optEnc o = 0 ↔ o = none := by
  cases o <;> simp

/-- The search predicate: `0` exactly at the stages where the machine has converged. -/
noncomputable def searchFun (A : ℕ → Bool) (e : ℕ) : ℕ →. ℕ := fun w =>
  Part.some (if optEnc (oracleStep A (ofNat Code e) w.unpair.1 w.unpair.2) = 0 then 1 else 0)

/-- The value read off at a stage, `0` if the stage has not converged. -/
noncomputable def valFun (A : ℕ → Bool) (e : ℕ) : ℕ →. ℕ := fun w =>
  Part.some (optEnc (oracleStep A (ofNat Code e) w.unpair.1 w.unpair.2) - 1)

theorem recursiveIn_searchFun (A : ℕ → Bool) (e : ℕ) :
    RecursiveIn {oracleFun A} (searchFun A e) := by
  have hpost : Nat.Partrec fun u : ℕ =>
      (Part.some (if u.unpair.2 = 0 then 1 else 0) : Part ℕ) :=
    Partrec.nat_iff.1 (Primrec.to_comp (Primrec.ite
      (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
      (Primrec.const 1) (Primrec.const 0))).partrec
  exact recursiveIn_of_eq
    (recursiveIn_bindPair (recursiveIn_of_partrec hpost) (recursiveIn_stageFun A e))
    fun w => by simp [stageFun, searchFun]

theorem recursiveIn_valFun (A : ℕ → Bool) (e : ℕ) :
    RecursiveIn {oracleFun A} (valFun A e) := by
  have hpost : Nat.Partrec fun u : ℕ => (Part.some (u.unpair.2 - 1) : Part ℕ) :=
    Partrec.nat_iff.1 (Primrec.to_comp
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))).partrec
  exact recursiveIn_of_eq
    (recursiveIn_bindPair (recursiveIn_of_partrec hpost) (recursiveIn_stageFun A e))
    fun w => by simp [stageFun, valFun]

/-- **Soundness of the oracle-machine indexing**: every machine `Φ_e^A` computes a partial
function that is recursive in `A`. -/
theorem recursiveIn_Phi (A : ℕ → Bool) (e : ℕ) : RecursiveIn {oracleFun A} (Phi A e) := by
  have hsearch := recIn_rfind (recursiveIn_searchFun A e)
  have h := recursiveIn_bindPair (recursiveIn_valFun A e) hsearch
  refine recursiveIn_of_eq h fun x => ?_
  have hp : ∀ n : ℕ, ((fun m => decide (m = 0)) <$> searchFun A e (Nat.pair x n)) =
      Part.some (decide (oracleStep A (ofNat Code e) x n ≠ none)) := by
    intro n
    cases hstep : oracleStep A (ofNat Code e) x n with
    | none => simp [searchFun, hstep]
    | some z => simp [searchFun, hstep]
  ext y
  simp only [Phi]
  rw [Part.mem_bind_iff, mem_evalOracle_iff]
  constructor
  · rintro ⟨v, hv, hy⟩
    have hv' := Nat.mem_rfind.mp hv
    have h1 : true ∈ Part.some (decide (oracleStep A (ofNat Code e) x v ≠ none)) := hp v ▸ hv'.1
    have hvsome : oracleStep A (ofNat Code e) x v ≠ none :=
      of_decide_eq_true (Part.mem_some_iff.mp h1).symm
    have hval : valFun A e (Nat.pair x v) =
        Part.some (optEnc (oracleStep A (ofNat Code e) x v) - 1) := by
      simp only [valFun, Nat.unpair_pair]
    have hy' : y = optEnc (oracleStep A (ofNat Code e) x v) - 1 :=
      Part.mem_some_iff.mp (hval ▸ hy)
    refine ⟨v, ?_, ?_⟩
    · cases hstep : oracleStep A (ofNat Code e) x v with
      | none => exact absurd hstep hvsome
      | some z =>
          rw [hstep] at hy'
          simp only [optEnc_some, Nat.add_sub_cancel] at hy'
          exact congrArg some hy'.symm
    · intro m hm
      have h2 : false ∈ Part.some (decide (oracleStep A (ofNat Code e) x m ≠ none)) :=
        hp m ▸ hv'.2 (m := m) hm
      by_contra hne
      simp [hne] at h2
  · rintro ⟨s, hs, hlt⟩
    refine ⟨s, Nat.mem_rfind.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hp]; simp [hs]
    · intro m hm
      rw [hp]; simp [hlt m hm]
    · simp only [valFun, Nat.unpair_pair, hs, optEnc_some, Nat.add_sub_cancel]
      exact Part.mem_some y

/-- **The characterisation of relative computability by oracle machines.**  A partial function is
recursive in the oracle `A` exactly when it is computed by one of the machines `Φ_e^A`. -/
theorem recursiveIn_iff_exists_index {A : ℕ → Bool} {f : ℕ →. ℕ} :
    RecursiveIn {oracleFun A} f ↔ ∃ e : ℕ, Phi A e = f := by
  refine ⟨exists_index_of_recursiveIn, ?_⟩
  rintro ⟨e, rfl⟩
  exact recursiveIn_Phi A e

/-- Every oracle machine is Turing reducible to its oracle. -/
theorem phi_turingReducible (A : ℕ → Bool) (e : ℕ) : Phi A e ≤ᵀ oracleFun A :=
  recursiveIn_Phi A e

end Oracle
end Lambda
