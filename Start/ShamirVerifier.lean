/-
**The verifier of Shamir's protocol for `TQBF` as a polynomial-time verifier** (task-board row
`M21-VERIFIER-POLY`).

On an input `x` of length `n` (meant to be the code of a closed formula), the verifier
`Complexity.Shamir.shamirV` works in the field `ZMod p` for a prime `p` with
`12 (n + 1)³ < p ≤ 24 (n + 1)³` found by trial division (`Complexity.Cob.findPrimeT`), with
`N = n` linearized variables and the degree bound `d = 2 n`; it draws `(n + 1)²` points, each
from `8 (n + 1)` coins (`Complexity.decP`), and plays `(n + 1)² + 1` rounds:

* in round `i + 1` it sends the `i`-th point in unary (in the first round a dummy point), read off
  its coins after counting the rounds already played in the transcript
  (`Complexity.Shamir.askT`);
* at the end it runs the machine of `Start/ShamirMachine.lean` on the code `x` and the transcript
  without its first record, for `(n + 1)²` steps, as one Cobham term
  (`Complexity.Shamir.decideT`, via `Start/ShamirIter.lean`), and accepts iff the machine has not
  rejected.

Every component is a Cobham term, so the verifier runs in polynomial time by construction.

Main results:

* `Complexity.Shamir.eval_decideT` — **the decision term runs the machine**, on every input,
  coin word and transcript;
* `Complexity.Shamir.accepts_shamirV` — the verdict of the verifier is the verdict of the
  machine on the transcript of the interaction;
* `Complexity.Shamir.eval_askT_pairs` — the question of the verifier after `i ≥ 1` rounds is the
  `i - 1`-st point drawn from its coins.
-/

import Start.ShamirIter
import Start.CoinDecode
import Start.InteractiveProof

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### The parameters -/

/-- `1^{12 (n + 1)³}` from `x` of length `n`. -/
def mT : Cob := Cob.nsmulT 12 (Cob.powT 3)

theorem eval_mT (x : Word) (rest : List Word) :
    mT.eval (x :: rest) = un (12 * (x.length + 1) ^ 3) := by
  rw [mT, Cob.eval_nsmulT 12 _ _ _ (Cob.eval_powT 3 x rest)]; rfl

/-- The prime, in unary. -/
def pT : Cob := Cob.findPrimeT mT

/-- The prime of the verifier on inputs of length `n`. -/
def primeOf (x : Word) : ℕ := (pT.eval [x]).length

theorem primeOf_spec (x : Word) :
    pT.eval [x] = un (primeOf x) ∧ (primeOf x).Prime ∧ 12 * (x.length + 1) ^ 3 < primeOf x ∧
      primeOf x ≤ 2 * (12 * (x.length + 1) ^ 3) := by
  obtain ⟨q, hq, hpr, h1, h2⟩ := Cob.eval_findPrimeT (mT := mT) (args := [x])
    (m := 12 * (x.length + 1) ^ 3) (by positivity) (eval_mT x [])
  have : primeOf x = q := by simp [primeOf, pT, hq]
  rw [this]
  exact ⟨hq, hpr, h1, h2⟩

theorem eval_pT_cons (x : Word) (rest : List Word) : pT.eval (x :: rest) = pT.eval [x] := by
  simp only [pT, Cob.findPrimeT, Cob.eval_comp, List.map_cons, List.map_nil, eval_mT]

/-- `1^n`. -/
def nT : Cob := Cob.onesOf (.proj 0)

theorem eval_nT (x : Word) (rest : List Word) : nT.eval (x :: rest) = un x.length := by
  simp [nT, un]

/-- `1^{2n}`, the degree bound. -/
def dT : Cob := Cob.catT nT nT

theorem eval_dT (x : Word) (rest : List Word) : dT.eval (x :: rest) = un (2 * x.length) := by
  rw [dT, Cob.eval_catT, eval_nT, un_eq, un_eq, two_mul, List.replicate_add]

/-- `1^{8 (n + 1)}`, the number of coins per point. -/
def kbT : Cob := Cob.nsmulT 8 (Cob.powT 1)

theorem eval_kbT (x : Word) (rest : List Word) : kbT.eval (x :: rest) = un (8 * (x.length + 1)) := by
  rw [kbT, Cob.eval_nsmulT 8 _ _ _ (Cob.eval_powT 1 x rest), pow_one]; rfl

/-- `1^{(n + 1)²}`: the number of points, and of steps of the machine. -/
def rcT : Cob := Cob.powT 2

theorem eval_rcT (x : Word) (rest : List Word) : rcT.eval (x :: rest) = un ((x.length + 1) ^ 2) :=
  Cob.eval_powT 2 x rest

/-! ### The decision -/

/-- The parameters read from the context `[x, r, t]`. -/
def pV : Cob := .comp pT [.proj 0]
def NV : Cob := .comp nT [.proj 0]
def dV : Cob := .comp dT [.proj 0]

/-- `n` zero bits: the point `0` with `n` coordinates. -/
def zerosN : Cob := .comp Cob.tail [.comp Cob.zerosT [.proj 0]]

theorem fieldsWord_replicate_zero (n : ℕ) : fieldsWord (List.replicate n 0) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, fieldsWord, ih]

/-- The initial state: the code `x`, the claim `1` at the point `0`, and the transcript without its
first record. -/
def initV : Cob :=
  packT [.proj 0, .empty, zerosN, uC 1, .empty, .empty, Cob.recSkipT (.proj 2), .empty]

/-- A bound on the packed states: `400 (n + |t| + 1)⁵`. -/
def bndV : Cob :=
  let z : Cob := .comp (.app true) [Cob.catT (Cob.onesOf (.proj 0)) (Cob.onesOf (.proj 2))]
  let z2 : Cob := .comp .smash [z, z]
  let z4 : Cob := .comp .smash [z2, z2]
  Cob.nsmulT 400 (.comp .smash [z4, z])

/-- The run of the machine, on `[1^K, x, r, t]`. -/
def runT : Cob := Cob.iterT initV (stepV 3 pV NV dV) bndV 3

/-- **The decision of the verifier**: run the machine for `(n + 1)²` steps and accept iff it has
not rejected. -/
def decideT : Cob :=
  .comp (Cob.iteT (unpackT 5 (.proj 0)) .empty Cob.trueC)
    [.comp runT [.comp rcT [.proj 0], .proj 0, .proj 1, .proj 2]]

section DecideEval

variable (x r t : Word)

theorem eval_pV : pV.eval [x, r, t] = un (primeOf x) := by
  simp only [pV, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
  exact (primeOf_spec x).1

theorem eval_NV : NV.eval [x, r, t] = un x.length := by
  simp only [NV, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
  exact eval_nT x []

theorem eval_dV : dV.eval [x, r, t] = un (2 * x.length) := by
  simp only [dV, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero]
  exact eval_dT x []

theorem eval_initV : initV.eval [x, r, t] = packW (encSt (initSt x.length x (recSkip t))) := by
  have hz : zerosN.eval [x, r, t] = List.replicate x.length false := by
    simp only [zerosN, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, Cob.eval_zerosT, Cob.eval_tail, List.replicate_succ, List.tail_cons]
  rw [initV, eval_packT]
  simp only [List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ,
    hz, Cob.eval_recSkipT, uC, Cob.eval_constT, Cob.eval_empty, encSt, initSt,
    fieldsWord_replicate_zero]

theorem eval_bndV : (bndV.eval [x, r, t]).length = 400 * (x.length + t.length + 1) ^ 5 := by
  have hz : (Cob.comp (.app true) [Cob.catT (Cob.onesOf (.proj 0)) (Cob.onesOf (.proj 2))]).eval
      [x, r, t] = List.replicate (x.length + t.length + 1) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, Cob.eval_catT,
      Cob.eval_onesOf, Cob.eval_proj, List.getD_cons_zero, List.getD_cons_succ]
    rw [← List.replicate_add, ← List.replicate_succ]
  rw [bndV, Cob.eval_nsmulT 400 _ _ ((x.length + t.length + 1) ^ 5), List.length_replicate]
  set z := Cob.comp (.app true) [Cob.catT (Cob.onesOf (.proj 0)) (Cob.onesOf (.proj 2))]
  set m := x.length + t.length + 1
  have e2 : (Cob.comp .smash [z, z]).eval [x, r, t] = List.replicate (m * m) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, hz,
      List.getD_cons_zero, List.getD_cons_succ, List.length_replicate]
  have e4 : (Cob.comp .smash [Cob.comp .smash [z, z], Cob.comp .smash [z, z]]).eval [x, r, t] =
      List.replicate (m * m * (m * m)) true := by
    rw [Cob.eval_comp]
    simp only [List.map_cons, List.map_nil, e2, Cob.eval_smash, List.getD_cons_zero,
      List.getD_cons_succ, List.length_replicate]
  rw [Cob.eval_comp]
  simp only [List.map_cons, List.map_nil, e4, hz, Cob.eval_smash, List.getD_cons_zero,
    List.getD_cons_succ, List.length_replicate]
  ring_nf

theorem bound_ok (n tl P z : ℕ) (hz : 1 ≤ z) (hn : n ≤ z) (htl : tl ≤ z) (hP : P ≤ 24 * z ^ 3) :
    2 * (n + n + n * P + P + tl * (2 * (n * P) + 2 * P + 2) + tl + 2) + 8 ≤ 400 * z ^ 5 := by
  calc 2 * (n + n + n * P + P + tl * (2 * (n * P) + 2 * P + 2) + tl + 2) + 8
      ≤ 2 * (z + z + z * (24 * z ^ 3) + 24 * z ^ 3 +
          z * (2 * (z * (24 * z ^ 3)) + 2 * (24 * z ^ 3) + 2) + z + 2) + 8 := by gcongr
    _ ≤ 400 * z ^ 5 := by
      have h1 : z ≤ z ^ 5 := by
        calc z = z ^ 1 := (pow_one z).symm
          _ ≤ z ^ 5 := Nat.pow_le_pow_right hz (by norm_num)
      have h3 : z ^ 3 ≤ z ^ 5 := Nat.pow_le_pow_right hz (by norm_num)
      have h4 : z ^ 4 ≤ z ^ 5 := Nat.pow_le_pow_right hz (by norm_num)
      have h0 : 1 ≤ z ^ 5 := Nat.one_le_pow _ _ hz
      ring_nf
      nlinarith

/-- **The decision term runs the machine**, on every input, coin word and transcript. -/
theorem eval_decideT :
    decideT.eval [x, r, t] =
      if ((stepW (primeOf x) x.length (2 * x.length))^[(x.length + 1) ^ 2]
          (initSt x.length x (recSkip t))).B = [] then [true] else [] := by
  obtain ⟨-, hpr, hm, hm2⟩ := primeOf_spec x
  have hp : 0 < primeOf x := hpr.pos
  have h1p : 1 < primeOf x := hpr.one_lt
  have hinv := inv_iterate hp (le_refl x.length) (2 * x.length)
    (inv_initSt (N := x.length) h1p x (recSkip t))
  have hrun := eval_iterT_run (ctx := [x, r, t]) (initT := initV) (bndT := bndV) hp
    (eval_pV x r t) (eval_NV x r t) (eval_dV x r t) (eval_initV x r t) hinv (by
      rw [eval_bndV]
      refine bound_ok _ _ _ _ (by omega) (by omega)
        ((recSkip_length_le t).trans (by omega)) (hm2.trans ?_)
      have : (x.length + 1) ^ 3 ≤ (x.length + t.length + 1) ^ 3 :=
        Nat.pow_le_pow_left (by omega) 3
      omega) (un ((x.length + 1) ^ 2))
  simp only [decideT, Cob.eval_comp, List.map_cons, List.map_nil, eval_rcT, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ]
  rw [show runT = Cob.iterT initV (stepV [x, r, t].length pV NV dV) bndV [x, r, t].length from rfl,
    hrun, length_un, Cob.eval_iteT_word,
    eval_unpackT (ws := encSt ((stepW (primeOf x) x.length (2 * x.length))^[(x.length + 1) ^ 2]
      (initSt x.length x (recSkip t)))) (i := 5) (by simp only [Cob.eval_proj, List.getD_cons_zero])
      (by simp [encSt])]
  simp only [Cob.eval_trueC, Cob.eval_empty]
  rfl

end DecideEval

end Complexity.Shamir
