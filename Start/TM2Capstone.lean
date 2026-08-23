/-
# Machine computability and partial recursiveness agree

`Start/TM2Partrec.lean` arithmetizes an arbitrary bundled Turing machine
(`Turing.FinTM2` with finite stack alphabets) and proves that the partial function it computes
on symbol codes is partial recursive.  `Start/TM2Forward.lean` bundles `Mathlib`'s compiler
from partial recursive functions into machines as such a machine.  This file combines the two
into an equivalence for partial functions on the naturals.

To state it, a machine has to be told how to read a natural number as the initial contents of
its input stack, and how to read the final contents of its output stack as a natural number.
Both translations are required to be computable, which is what makes the statement have
content; `TM2Partrec.TM2Realization` packages a machine together with them.

Main results:

* `TM2Partrec.natBits`, `TM2Partrec.numOf` — the binary encoding used by `Mathlib`'s machine,
  read on symbol codes, together with its inverse; both are primitive recursive;
* `TM2Partrec.evalCode_trFinTM2` — the bundled machine of a code computes it on codes;
* `TM2Partrec.tm2Computable_iff_partrec` — **a partial function on the naturals is computable
  by a bundled Turing machine exactly when it is partial recursive**;
* `lambdaComputable_iff_tm2Computable` — the two models of computation of this development,
  the lambda calculus and Turing machines, define the same partial functions.
-/

import Start.TM2Forward
import Start.TM2Partrec
import Start.PartialCapstone

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TM2Partrec

open Turing Turing.PartrecToTM2 Turing.ToPartrec

/-! ## Binary numerals on symbol codes -/

/-- The list of binary digits of `n`, least significant first, written with the codes `b0`
and `b1` of the two digit symbols.  This is the code-level form of
`Turing.PartrecToTM2.trNat`. -/
def natBits (b0 b1 : ℕ) : ℕ → List ℕ
  | 0 => []
  | (n + 1) => (if (n + 1) % 2 = 1 then b1 else b0) :: natBits b0 b1 ((n + 1) / 2)
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) (by omega)

theorem natBits_zero (b0 b1 : ℕ) : natBits b0 b1 0 = [] := by rw [natBits]

theorem natBits_pos (b0 b1 : ℕ) {n : ℕ} (hn : n ≠ 0) :
    natBits b0 b1 n = (if n % 2 = 1 then b1 else b0) :: natBits b0 b1 (n / 2) := by
  cases n with
  | zero => exact absurd rfl hn
  | succ m => rw [natBits]

theorem primrec_natBits (b0 b1 : ℕ) : Primrec (natBits b0 b1) := by
  have hg : Primrec₂ fun (_ : Unit) (l : List (List ℕ)) =>
      (some (if l.length = 0 then []
        else (if l.length % 2 = 1 then b1 else b0) :: (l[l.length / 2]?.getD [])) :
          Option (List ℕ)) := by
    have hlen : Primrec fun p : Unit × List (List ℕ) => p.2.length :=
      Primrec.list_length.comp Primrec.snd
    have hdigit : Primrec fun p : Unit × List (List ℕ) =>
        if p.2.length % 2 = 1 then b1 else b0 :=
      Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hlen (Primrec.const 2))
        (Primrec.const 1)) (Primrec.const b1) (Primrec.const b0)
    have htail : Primrec fun p : Unit × List (List ℕ) => p.2[p.2.length / 2]?.getD [] :=
      Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.snd (Primrec.nat_div.comp hlen (Primrec.const 2)))
        (Primrec.const [])
    exact Primrec.option_some.comp
      (Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const [])
        (Primrec.list_cons.comp hdigit htail))
  have hstrong : Primrec₂ fun (_ : Unit) (n : ℕ) => natBits b0 b1 n := by
    refine Primrec.nat_strong_rec _ hg fun _ n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [natBits_zero]
    · have hlen : ((List.range n).map (natBits b0 b1)).length = n := by simp
      have hget : ((List.range n).map (natBits b0 b1))[n / 2]? =
          some (natBits b0 b1 (n / 2)) := by
        have hlt : n / 2 < n := Nat.div_lt_self hn (by omega)
        rw [List.getElem?_map]
        simp [List.getElem?_range hlt]
      simp only [hlen, hget, Option.getD_some]
      rw [if_neg (by omega : ¬ n = 0)]
      exact congrArg some (natBits_pos b0 b1 (by omega)).symm
  exact hstrong.comp (Primrec.const ()) Primrec.id

theorem natBits_posNum (g : Γ' → ℕ) : ∀ p : PosNum,
    natBits (g Γ'.bit0) (g Γ'.bit1) (p : ℕ) = (trPosNum p).map g := by
  intro p
  induction p with
  | one =>
      rw [natBits_pos _ _ (by norm_num)]
      simp [trPosNum, natBits_zero]
  | bit0 p ih =>
      have hp : 0 < (p : ℕ) := by exact_mod_cast p.cast_pos (α := ℕ)
      have hcast : ((PosNum.bit0 p : PosNum) : ℕ) = 2 * (p : ℕ) := by
        simp only [PosNum.cast_bit0]
        ring
      rw [hcast, natBits_pos _ _ (by omega)]
      have h1 : 2 * (p : ℕ) % 2 = 0 := by omega
      have h2 : 2 * (p : ℕ) / 2 = (p : ℕ) := by omega
      rw [h1, h2, if_neg (by norm_num), ih]
      simp [trPosNum]
  | bit1 p ih =>
      have hp : 0 < (p : ℕ) := by exact_mod_cast p.cast_pos (α := ℕ)
      have hcast : ((PosNum.bit1 p : PosNum) : ℕ) = 2 * (p : ℕ) + 1 := by
        simp only [PosNum.cast_bit1]
        ring
      rw [hcast, natBits_pos _ _ (by omega)]
      have h1 : (2 * (p : ℕ) + 1) % 2 = 1 := by omega
      have h2 : (2 * (p : ℕ) + 1) / 2 = (p : ℕ) := by omega
      rw [h1, h2, if_pos rfl, ih]
      simp [trPosNum]

/-- The code-level binary digits are the codes of the digit symbols the machine uses. -/
theorem natBits_eq_trNat (g : Γ' → ℕ) (n : ℕ) :
    natBits (g Γ'.bit0) (g Γ'.bit1) n = (trNat n).map g := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [natBits_zero, trNat_zero]
  · obtain ⟨p, hp⟩ : ∃ p : PosNum, (n : Num) = Num.pos p := by
      cases hnum : (n : Num) with
      | zero =>
          exfalso
          have hz : ((n : Num) : ℕ) = 0 := by rw [hnum]; rfl
          rw [show ((n : Num) : ℕ) = n by simp] at hz
          omega
      | pos p => exact ⟨p, rfl⟩
    have hpn : (p : ℕ) = n := by
      have hc := congrArg (fun x : Num => (x : ℕ)) hp
      simpa using hc.symm
    rw [trNat, hp, ← hpn]
    exact natBits_posNum g p

/-- Reading a list of symbol codes as a binary numeral, least significant digit first; the
first symbol which is not a digit ends the numeral. -/
def numOf (b0 b1 : ℕ) (l : List ℕ) : ℕ :=
  l.foldr (fun x s => if x = b1 then 2 * s + 1 else if x = b0 then 2 * s else 0) 0

theorem primrec_numOf (b0 b1 : ℕ) : Primrec (numOf b0 b1) := by
  have hh : Primrec₂ fun (_ : List ℕ) (p : ℕ × ℕ) =>
      if p.1 = b1 then 2 * p.2 + 1 else if p.1 = b0 then 2 * p.2 else 0 := by
    have hx : Primrec fun q : List ℕ × (ℕ × ℕ) => q.2.1 := Primrec.fst.comp Primrec.snd
    have hs : Primrec fun q : List ℕ × (ℕ × ℕ) => q.2.2 := Primrec.snd.comp Primrec.snd
    have hdouble : Primrec fun q : List ℕ × (ℕ × ℕ) => 2 * q.2.2 :=
      Primrec.nat_mul.comp (Primrec.const 2) hs
    exact Primrec.ite (Primrec.eq.comp hx (Primrec.const b1))
      (Primrec.succ.comp hdouble)
      (Primrec.ite (Primrec.eq.comp hx (Primrec.const b0)) hdouble (Primrec.const 0))
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) hh

theorem numOf_nil (b0 b1 : ℕ) : numOf b0 b1 [] = 0 := rfl

theorem numOf_cons (b0 b1 x : ℕ) (l : List ℕ) :
    numOf b0 b1 (x :: l) =
      if x = b1 then 2 * numOf b0 b1 l + 1 else if x = b0 then 2 * numOf b0 b1 l else 0 :=
  rfl

/-- The numeral reader inverts the numeral writer, as long as the three symbol codes are
distinct. -/
theorem numOf_natBits (b0 b1 e : ℕ) (h01 : b0 ≠ b1) (he0 : e ≠ b0) (he1 : e ≠ b1) :
    ∀ n : ℕ, numOf b0 b1 (natBits b0 b1 n ++ [e]) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [natBits_zero]
        simp [numOf_cons, he0, he1]
      · have hlt : n / 2 < n := Nat.div_lt_self hn (by omega)
        rw [natBits_pos b0 b1 (by omega), List.cons_append, numOf_cons, ih _ hlt]
        by_cases hpar : n % 2 = 1
        · rw [if_pos hpar, if_pos rfl]
          omega
        · rw [if_neg hpar, if_neg h01, if_pos rfl]
          omega

/-! ## The code-level behaviour of the bundled machine of a code -/

/-- The numbering of the machine's stack alphabet used by the arithmetization. -/
noncomputable def gamma (x : Γ') : ℕ := (Fintype.equivFin Γ' x : ℕ)

theorem gamma_injective : Function.Injective gamma := fun x y h => by
  have h' : Fintype.equivFin Γ' x = Fintype.equivFin Γ' y := Fin.val_injective h
  exact (Fintype.equivFin Γ').injective h'

theorem encG_trFinTM2 (c : Code) (k : (trFinTM2 c).K) (x : (trFinTM2 c).Γ k) :
    encG (trFinTM2 c) x = gamma x := rfl

/-- The input word of the bundled machine, as a list of symbol codes. -/
noncomputable def inputCodes (n : ℕ) : List ℕ :=
  natBits (gamma Γ'.bit0) (gamma Γ'.bit1) n ++ [gamma Γ'.cons]

/-- The output value read off the machine's output stack. -/
noncomputable def outputValue (l : List ℕ) : ℕ := numOf (gamma Γ'.bit0) (gamma Γ'.bit1) l

theorem computable_inputCodes : Computable inputCodes :=
  Primrec.to_comp
    (Primrec.list_append.comp (primrec_natBits _ _) (Primrec.const [gamma Γ'.cons]))

theorem computable_outputValue : Computable outputValue :=
  Primrec.to_comp (primrec_numOf _ _)

theorem inputCodes_eq (n : ℕ) : inputCodes n = (trList [n]).map gamma := by
  rw [inputCodes, natBits_eq_trNat gamma n]
  simp [trList]

theorem outputValue_inputCodes (n : ℕ) : outputValue ((trList [n]).map gamma) = n := by
  have hne : ∀ {x y : Γ'}, x ≠ y → gamma x ≠ gamma y := fun hxy h => hxy (gamma_injective h)
  rw [← inputCodes_eq, inputCodes, outputValue]
  exact numOf_natBits _ _ _ (hne (by decide)) (hne (by decide)) (hne (by decide)) n

/-- **The bundled machine of a code computes that code**, at the level of symbol codes. -/
theorem evalCode_trFinTM2 (c : Code) {v w : List ℕ} (h : w ∈ Code.eval c v) :
    evalCode (trFinTM2 c) ((trList v).map gamma) = Part.some ((trList w).map gamma) :=
  evalCode_of_outputs (trFinTM2 c) (trFinTM2_outputs c h)

/-- Conversely, if the code-level function of the bundled machine of `c` converges, so does
the code. -/
theorem code_eval_dom_of_evalCode (c : Code) (v : List ℕ) {w : List ℕ}
    (h : w ∈ evalCode (trFinTM2 c) ((trList v).map gamma)) : (Code.eval c v).Dom := by
  obtain ⟨t, cfg, ht, hl⟩ := exists_halted_of_evalCode (trFinTM2 c) h
  have hmap := iterate_map_opt (codeLabels c) (mainLabel c) tr (supportsStmt_tr c) t
    (some (initList (trFinTM2 c) (trList v)))
  have e1 : Option.map (mapCfg (codeLabels c)) (some (initList (trFinTM2 c) (trList v))) =
      some (init c v) := congrArg some (mapCfg_initList c v)
  have e2 : (flip Bind.bind (TM2.step (restrict (codeLabels c) (mainLabel c) tr)))^[t]
      (some (initList (trFinTM2 c) (trList v))) = some cfg := ht
  have hmap2 : some (mapCfg (codeLabels c) cfg) =
      (flip Bind.bind (TM2.step tr))^[t] (some (init c v)) :=
    (congrArg (Option.map (mapCfg (codeLabels c))) e2).symm.trans (hmap.trans (congrArg _ e1))
  have hstep : TM2.step tr (mapCfg (codeLabels c) cfg) = none := by
    obtain ⟨l, var, stk⟩ := cfg
    simp only at hl
    subst hl
    rfl
  have hmem : mapCfg (codeLabels c) cfg ∈ Turing.eval (TM2.step tr) (init c v) :=
    Turing.mem_eval.2 ⟨reaches_of_iterate t hmap2.symm, hstep⟩
  rw [tr_eval c v] at hmem
  obtain ⟨w', hw', -⟩ := (Part.mem_map_iff _).1 hmem
  exact Part.dom_iff_mem.2 ⟨w', hw'⟩

/-! ## Machine computability of a partial function on the naturals -/

/-- A realization of a partial function on the naturals by a bundled Turing machine: the
machine, the finiteness of its stack alphabets, and computable translations between natural
numbers and the contents of its input and output stacks. -/
structure TM2Realization (f : ℕ →. ℕ) where
  /-- the machine -/
  tm : Turing.FinTM2
  /-- all its stack alphabets are finite -/
  ΓFin : ∀ k, Fintype (tm.Γ k)
  /-- how a natural number is written on the input stack -/
  inp : ℕ → List ℕ
  /-- how the contents of the output stack are read as a natural number -/
  out : List ℕ → ℕ
  /-- the input translation is computable -/
  inp_computable : Computable inp
  /-- the output translation is computable -/
  out_computable : Computable out
  /-- the machine computes `f` through these translations -/
  eval_eq : ∀ n, f n = (@evalCode tm ΓFin (inp n)).map out

/-- A partial function on the naturals is *machine computable* when some bundled Turing
machine with finite stack alphabets computes it through computable translations. -/
def TM2ComputableNat (f : ℕ →. ℕ) : Prop := Nonempty (TM2Realization f)

/-- A machine computable function is partial recursive. -/
theorem partrec_of_tm2ComputableNat {f : ℕ →. ℕ} (h : TM2ComputableNat f) : Partrec f := by
  obtain ⟨tm, ΓFin, inp, out, hinp, hout, heval⟩ := h
  have hpart : Partrec fun n => (@evalCode tm ΓFin (inp n)).map out :=
    ((@partrec_evalCode tm ΓFin).comp hinp).map (hout.comp Computable.snd).to₂
  exact hpart.of_eq fun n => (heval n).symm

/-- Every partial recursive function is computed by a bundled Turing machine. -/
theorem tm2ComputableNat_of_partrec {f : ℕ →. ℕ} (hf : Partrec f) : TM2ComputableNat f := by
  obtain ⟨c, hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.2 hf)
  have hcode : ∀ n : ℕ, Code.eval c [n] = (f n).map fun m => [m] := by
    intro n
    have h := hc (⟨[n], rfl⟩ : List.Vector ℕ 1)
    have hh : List.Vector.head (⟨[n], rfl⟩ : List.Vector ℕ 1) = n := rfl
    rw [hh] at h
    have hpure : (fun m : ℕ => [m]) = (pure : ℕ → List ℕ) := rfl
    rw [hpure]
    simpa [Part.map_eq_map] using h
  refine ⟨trFinTM2 c, trFinTM2_ΓFin c, inputCodes, outputValue, computable_inputCodes,
    computable_outputValue, fun n => ?_⟩
  refine Part.ext fun m => ?_
  constructor
  · intro hm
    have hlist : [m] ∈ Code.eval c [n] := by
      rw [hcode n]
      exact Part.mem_map _ hm
    have heval := evalCode_trFinTM2 c hlist
    rw [inputCodes_eq n]
    rw [heval]
    refine (Part.mem_map_iff _).2 ⟨(trList [m]).map gamma, Part.mem_some _, ?_⟩
    exact outputValue_inputCodes m
  · intro hm
    obtain ⟨w, hw, hwm⟩ := (Part.mem_map_iff _).1 hm
    rw [inputCodes_eq n] at hw
    have hdom : (Code.eval c [n]).Dom := code_eval_dom_of_evalCode c [n] hw
    obtain ⟨l, hl⟩ : ∃ l, l ∈ Code.eval c [n] :=
      ⟨(Code.eval c [n]).get hdom, Part.get_mem hdom⟩
    have hl' : l ∈ (f n).map fun m => [m] := by rw [← hcode n]; exact hl
    obtain ⟨m', hm', hml⟩ := (Part.mem_map_iff _).1 hl'
    have heval := evalCode_trFinTM2 c hl
    rw [heval] at hw
    have hwval : w = (trList l).map gamma := Part.mem_some_iff.1 hw
    subst hwval
    rw [← hml, outputValue_inputCodes m'] at hwm
    rwa [← hwm]

/-- **Machine computability and partial recursiveness agree.**  A partial function on the
naturals is computed by a bundled Turing machine with finite stack alphabets, through
computable translations of its input and output, exactly when it is partial recursive. -/
theorem tm2Computable_iff_partrec {f : ℕ →. ℕ} : TM2ComputableNat f ↔ Partrec f :=
  ⟨partrec_of_tm2ComputableNat, tm2ComputableNat_of_partrec⟩

/-- The notion is not vacuous: the identity is computed by a bundled machine. -/
example : TM2ComputableNat (fun n => Part.some n) :=
  tm2ComputableNat_of_partrec (Computable.partrec Computable.id)

end TM2Partrec

/-- **The two models agree.**  A partial function on the naturals is lambda-definable exactly
when it is computable by a bundled Turing machine. -/
theorem lambdaComputable_iff_tm2Computable {f : ℕ →. ℕ} :
    LambdaComputable f ↔ TM2Partrec.TM2ComputableNat f :=
  lambdaComputable_iff_partrec.trans TM2Partrec.tm2Computable_iff_partrec.symm
