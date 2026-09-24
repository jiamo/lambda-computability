/-
**`TQBF` is `PSPACE`-hard.**

`Start/QbfCobMachine.lean` writes the code of the reduction formula with a single Cobham term,
given the input *and* a parameter word holding the width of a configuration, the depth of the
midpoint recursion and a handful of products of the two.  This module removes the parameter: for a
machine running in polynomial space, every field of the parameter word is a polynomial in the
length of the input, and a polynomial in unary is a Cobham function of the input.  The reduction
is then a single Cobham term applied to the input alone, which is exactly a polynomial-time
many-one reduction in the sense of `Complexity.PolyManyOne`.

Main definitions:

* `Complexity.Cob.onesT`, `.powT`, `.nsmulT` — unary polynomials of the length of the input;
* `Complexity.Qbf.QBF.redTerm` — the reduction as a Cobham term of the input alone.

Main results:

* `Complexity.Qbf.QBF.eval_redTerm` — **the term writes the code of the reduction formula**;
* `Complexity.Qbf.QBF.npspaceHard_tqbfLang`, `.pspaceHard_tqbfLang` — **every language in
  (nondeterministic) polynomial space reduces to `TQBF` in polynomial time.**
-/

import Mathlib
import Start.QbfCobMachine
import Start.QbfPspace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Unary polynomials of the length of the input -/

/-- The word `1^{|x|}`, where `x` is the first argument. -/
def Cob.onesT : Cob := .comp .smash [.proj 0, Cob.trueC]

theorem Cob.eval_onesT (x : Word) (rest : List Word) :
    Cob.onesT.eval (x :: rest) = List.replicate x.length true := by
  simp [Cob.onesT]

/-- The word `1^{(|x| + 1) ^ d}`. -/
def Cob.powT : ℕ → Cob
  | 0 => Cob.constT [true]
  | d + 1 => .comp .smash [Cob.powT d, Cob.uSucc Cob.onesT]

theorem Cob.eval_powT : ∀ (d : ℕ) (x : Word) (rest : List Word),
    (Cob.powT d).eval (x :: rest) = List.replicate ((x.length + 1) ^ d) true := by
  intro d
  induction d with
  | zero => intro x rest; simp [Cob.powT]
  | succ d ih =>
      intro x rest
      have hsucc : (Cob.uSucc Cob.onesT).eval (x :: rest)
          = List.replicate (x.length + 1) true :=
        Cob.eval_uSucc (Cob.eval_onesT x rest)
      simp only [Cob.powT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
        List.getD_cons_zero, List.getD_cons_succ, ih x rest, hsucc, List.length_replicate]
      rw [pow_succ]

/-- The word `1^{a * m}`, where `1^m` is the value of `t`. -/
def Cob.nsmulT : ℕ → Cob → Cob
  | 0, _ => Cob.empty
  | a + 1, t => Cob.uAdd t (Cob.nsmulT a t)

theorem Cob.eval_nsmulT : ∀ (a : ℕ) (t : Cob) (args : List Word) (m : ℕ),
    t.eval args = List.replicate m true →
    (Cob.nsmulT a t).eval args = List.replicate (a * m) true := by
  intro a
  induction a with
  | zero => intro t args m _; simp [Cob.nsmulT]
  | succ a ih =>
      intro t args m ht
      have h := Cob.eval_uAdd ht (ih t args m ht)
      rw [Cob.nsmulT, h]
      congr 1
      ring

end Complexity

namespace Complexity.Qbf

namespace QBF

open Complexity Complexity.Space

/-! ### The fields of the parameter word, as polynomials of the input -/

/-- The space bound the reduction uses: a computable polynomial above the space bound of the
machine, and positive. -/
def spaceOf (a d : ℕ) (n : ℕ) : ℕ := a * (n + 1) ^ d + 1

theorem spaceOf_pos (a d n : ℕ) : 0 < spaceOf a d n := by simp [spaceOf]

/-- `1^{|x| + 1}`. -/
def lenSuccT : Cob := Cob.uSucc Cob.onesT

/-- `1^{spaceOf a d |x|}`. -/
def spaceT (a d : ℕ) : Cob := Cob.uSucc (Cob.nsmulT a (Cob.powT d))

/-- `1^{cfgWidth M x (spaceOf a d |x|)}`. -/
def widthT (M : Machine) (a d : ℕ) : Cob :=
  Cob.uAdd (Cob.constT (List.replicate M.states true))
    (Cob.uAdd lenSuccT (Cob.uAdd (spaceT a d) (spaceT a d)))

/-- `1^{kBound M (spaceOf a d) |x|}`. -/
def depthT (M : Machine) (a d : ℕ) : Cob :=
  Cob.uAdd (Cob.constT (List.replicate M.states true))
    (Cob.uAdd lenSuccT
      (Cob.uAdd (Cob.uAdd (Cob.uAdd (spaceT a d) (spaceT a d)) (Cob.constT (List.replicate 2 true)))
        (spaceT a d)))

theorem eval_lenSuccT (x : Word) (rest : List Word) :
    lenSuccT.eval (x :: rest) = List.replicate (x.length + 1) true :=
  Cob.eval_uSucc (Cob.eval_onesT x rest)

theorem eval_spaceT (a d : ℕ) (x : Word) (rest : List Word) :
    (spaceT a d).eval (x :: rest) = List.replicate (spaceOf a d x.length) true :=
  Cob.eval_uSucc (Cob.eval_nsmulT a (Cob.powT d) _ _ (Cob.eval_powT d x rest))

theorem eval_widthT (M : Machine) (a d : ℕ) (x : List Bool) (rest : List Word) :
    (widthT M a d).eval (x :: rest)
      = List.replicate (cfgWidth M x (spaceOf a d x.length)) true := by
  have hs := eval_spaceT a d x rest
  have h : (widthT M a d).eval (x :: rest)
      = List.replicate (M.states + ((x.length + 1) +
          (spaceOf a d x.length + spaceOf a d x.length))) true :=
    Cob.eval_uAdd (Cob.eval_constT _ _)
      (Cob.eval_uAdd (eval_lenSuccT x rest) (Cob.eval_uAdd hs hs))
  rw [h, cfgWidth]
  congr 1
  omega

theorem eval_depthT (M : Machine) (a d : ℕ) (x : List Bool) (rest : List Word) :
    (depthT M a d).eval (x :: rest)
      = List.replicate (kBound M (spaceOf a d) x.length) true := by
  have hs := eval_spaceT a d x rest
  have h2 : (Cob.constT (List.replicate 2 true)).eval (x :: rest) = List.replicate 2 true :=
    Cob.eval_constT _ _
  have h : (depthT M a d).eval (x :: rest)
      = List.replicate (M.states + ((x.length + 1) +
          ((spaceOf a d x.length + spaceOf a d x.length + 2) + spaceOf a d x.length))) true :=
    Cob.eval_uAdd (Cob.eval_constT _ _)
      (Cob.eval_uAdd (eval_lenSuccT x rest)
        (Cob.eval_uAdd (Cob.eval_uAdd (Cob.eval_uAdd hs hs) h2) hs))
  rw [h, kBound]
  congr 1
  omega

/-! ### The reduction as a term of the input alone -/

/-- The term assembling the parameter word of the reduction out of the input alone. -/
def machineParamT (M : Machine) (a d : ℕ) : Cob :=
  Cob.catL
    [Cob.fieldsT
      [widthT M a d,
        depthT M a d,
        spaceT a d,
        Cob.onesT,
        Cob.constT (List.replicate M.states true),
        Cob.uAdd (Cob.constT (List.replicate M.states true)) lenSuccT,
        Cob.uAdd (Cob.uAdd (Cob.constT (List.replicate M.states true)) lenSuccT) (spaceT a d),
        .comp .smash [Cob.nsmulT 3 (depthT M a d), widthT M a d],
        Cob.nsmulT 2 (widthT M a d),
        Cob.nsmulT 3 (widthT M a d),
        Cob.nsmulT 4 (widthT M a d),
        .comp .smash
          [.comp .smash
            [Cob.uAdd (widthT M a d)
              (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true))),
             Cob.uAdd (widthT M a d)
              (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))],
           Cob.uAdd (widthT M a d)
            (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))]],
      .proj 0]

/-- **The reduction as a Cobham term of the input alone.** -/
def redTerm (M : Machine) (a d : ℕ) : Cob :=
  .comp (machineTerm M) [.proj 0, machineParamT M a d]

theorem eval_machineParamT (M : Machine) (a d : ℕ) (x : List Bool) :
    (machineParamT M a d).eval [x]
      = machineParam M x (spaceOf a d x.length) (kBound M (spaceOf a d) x.length) := by
  set S := spaceOf a d x.length with hS
  set K := kBound M (spaceOf a d) x.length with hK
  set W := cfgWidth M x S with hWdef
  have hw : (widthT M a d).eval [x] = List.replicate W true := eval_widthT M a d x []
  have hk : (depthT M a d).eval [x] = List.replicate K true := eval_depthT M a d x []
  have hs : (spaceT a d).eval [x] = List.replicate S true := eval_spaceT a d x []
  have hn : Cob.onesT.eval [x] = List.replicate x.length true := Cob.eval_onesT x []
  have hst : (Cob.constT (List.replicate M.states true)).eval [x]
      = List.replicate M.states true := Cob.eval_constT _ _
  have hls : lenSuccT.eval [x] = List.replicate (x.length + 1) true := eval_lenSuccT x []
  have h5 : (Cob.uAdd (Cob.constT (List.replicate M.states true)) lenSuccT).eval [x]
      = List.replicate (M.states + (x.length + 1)) true := Cob.eval_uAdd hst hls
  have h6 : (Cob.uAdd (Cob.uAdd (Cob.constT (List.replicate M.states true)) lenSuccT)
      (spaceT a d)).eval [x]
      = List.replicate (M.states + (x.length + 1) + S) true := Cob.eval_uAdd h5 hs
  have h3k : (Cob.nsmulT 3 (depthT M a d)).eval [x] = List.replicate (3 * K) true :=
    Cob.eval_nsmulT 3 _ _ _ hk
  have h7 : (Cob.comp .smash [Cob.nsmulT 3 (depthT M a d), widthT M a d]).eval [x]
      = List.replicate (3 * K * W) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, List.getD_cons_zero,
      List.getD_cons_succ, h3k, hw, List.length_replicate]
  have h8 : (Cob.nsmulT 2 (widthT M a d)).eval [x] = List.replicate (2 * W) true :=
    Cob.eval_nsmulT 2 _ _ _ hw
  have h9 : (Cob.nsmulT 3 (widthT M a d)).eval [x] = List.replicate (3 * W) true :=
    Cob.eval_nsmulT 3 _ _ _ hw
  have h10 : (Cob.nsmulT 4 (widthT M a d)).eval [x] = List.replicate (4 * W) true :=
    Cob.eval_nsmulT 4 _ _ _ hw
  have h8c : (Cob.constT (List.replicate 8 true)).eval [x] = List.replicate 8 true :=
    Cob.eval_constT _ _
  have hq : (Cob.uAdd (widthT M a d)
      (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))).eval [x]
      = List.replicate (W + 3 * K + 8) true := by
    have h := Cob.eval_uAdd hw (Cob.eval_uAdd h3k h8c)
    have harith : W + (3 * K + 8) = W + 3 * K + 8 := by omega
    rw [h, harith]
  have h11 : (Cob.comp .smash
      [Cob.comp .smash
        [Cob.uAdd (widthT M a d)
          (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true))),
         Cob.uAdd (widthT M a d)
          (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))],
       Cob.uAdd (widthT M a d)
        (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))]).eval [x]
      = List.replicate (levelsPad W K) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, List.getD_cons_zero,
      List.getD_cons_succ, hq, List.length_replicate, levelsPad]
  have hfields : (Cob.fieldsT
      [widthT M a d, depthT M a d, spaceT a d, Cob.onesT,
        Cob.constT (List.replicate M.states true),
        Cob.uAdd (Cob.constT (List.replicate M.states true)) lenSuccT,
        Cob.uAdd (Cob.uAdd (Cob.constT (List.replicate M.states true)) lenSuccT) (spaceT a d),
        .comp .smash [Cob.nsmulT 3 (depthT M a d), widthT M a d],
        Cob.nsmulT 2 (widthT M a d), Cob.nsmulT 3 (widthT M a d), Cob.nsmulT 4 (widthT M a d),
        .comp .smash
          [.comp .smash
            [Cob.uAdd (widthT M a d)
              (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true))),
             Cob.uAdd (widthT M a d)
              (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))],
           Cob.uAdd (widthT M a d)
            (Cob.uAdd (Cob.nsmulT 3 (depthT M a d)) (Cob.constT (List.replicate 8 true)))]]).eval
        [x] = fieldsWord (machineFields M x S K) := by
    rw [machineFields]
    refine Cob.eval_fieldsT ?_
    exact .cons hw (.cons hk (.cons hs (.cons hn (.cons hst (.cons h5 (.cons h6
      (.cons h7 (.cons h8 (.cons h9 (.cons h10 (.cons h11 .nil)))))))))))
  have hx : (Cob.proj 0).eval [x] = x := by simp
  simp only [machineParamT, Cob.eval_catL, List.map_cons, List.map_nil, hfields, hx,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [machineParam]

/-- **The term writes the code of the reduction formula.** -/
theorem eval_redTerm (M : Machine) (a d : ℕ) (hstates : 0 < M.states) (x : List Bool) :
    (redTerm M a d).eval [x]
      = enc (machineFk M x (spaceOf a d x.length) (kBound M (spaceOf a d) x.length)) := by
  simp only [redTerm, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, eval_machineParamT]
  exact (enc_machineFk_eval M x _ _ hstates).symm

/-! ### `TQBF` is hard for polynomial space -/

/-- **Every language in nondeterministic polynomial space reduces to `TQBF` in polynomial
time.** -/
theorem npspaceHard_tqbfLang {L : Complexity.Space.Language} (h : Complexity.Space.NPSPACE L) :
    Complexity.PolyManyOne L tqbfLang := by
  obtain ⟨s, hs, M, hwf, hsp, hL⟩ := h
  obtain ⟨a, d, ha⟩ := hs
  refine ⟨redTerm M a d, fun x => ?_⟩
  have hspx : M.SpaceBoundedOn x (spaceOf a d x.length) := by
    intro n c hc
    have := hsp x n c hc
    have hb := ha x.length
    simp only [spaceOf]
    omega
  have hk : savitchDepth M x (spaceOf a d x.length)
      ≤ kBound M (spaceOf a d) x.length :=
    savitchDepth_le_kBound M (spaceOf a d) x
  rw [eval_redTerm M a d hwf.1 x, tqbfLang_enc_iff,
    tqbf_machineFk_iff hwf hspx (spaceOf_pos a d x.length) hk]
  exact hL x

/-- **`TQBF` is `PSPACE`-hard**: every language in polynomial space reduces to it in polynomial
time. -/
theorem pspaceHard_tqbfLang {L : Complexity.Space.Language} (h : Complexity.Space.PSPACE L) :
    Complexity.PolyManyOne L tqbfLang :=
  npspaceHard_tqbfLang (Complexity.Space.npspace_of_pspace h)

end QBF

end Complexity.Qbf
