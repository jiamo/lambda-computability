/-
**`NP^A ⊆ PSPACE^A` (and `P^A ⊆ PSPACE^A`).**

An `NP^A` language is decided in polynomial space with the oracle `A` by trying every witness in
turn.  The witnesses of length at most `ℓ` are coded by the words `u` of length `ℓ + 1`
(`u = 1^{ℓ - |w|} 0 w` codes `w`, `Complexity.Space.NPW.decodeW`), and these are enumerated by a
binary counter (`Complexity.Space.NPW.bits`, advanced by the Cobham term
`Complexity.Space.NPW.incrC`).  The loop of the oracle tape program runs the compiled verifier
(`Complexity.Space.OProg.compileQ`) on each of them, keeps the disjunction of the answers in one
register, and stops after the counter has been all ones.  Every register stays polynomially
long, so the program runs in polynomial space by `Complexity.Space.OProg.odspace_of_oexec`.

* `Complexity.Space.inPSPACE_rel_of_inP_rel` — `P^A ⊆ PSPACE^A`;
* `Complexity.Space.inPSPACE_rel_of_inNP_rel` — **`NP^A ⊆ PSPACE^A`**, for every oracle `A`.
-/

import Mathlib
import Start.OracleCobSpace
import Start.OracleClasses
import Start.CollapsingOracle
import Start.CobhamPspace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace NPW

/-! ### Words as counters -/

/-- The word of length `m` that is the binary expansion of `k mod 2^m`, least significant bit
first. -/
def bits : ℕ → ℕ → Word
  | 0, _ => []
  | m + 1, k => (k % 2 == 1) :: bits m (k / 2)

@[simp] theorem length_bits (m k : ℕ) : (bits m k).length = m := by
  induction m generalizing k with
  | zero => rfl
  | succ m ih => simp [bits, ih]

/-- The successor of a counter, wrapping around. -/
def incrW : Word → Word
  | [] => []
  | false :: u => true :: u
  | true :: u => false :: incrW u

@[simp] theorem length_incrW : ∀ u : Word, (incrW u).length = u.length
  | [] => rfl
  | false :: u => by simp [incrW]
  | true :: u => by simp [incrW, length_incrW u]

theorem incrW_bits (m : ℕ) : ∀ k, incrW (bits m k) = bits m (k + 1) := by
  induction m with
  | zero => intro k; rfl
  | succ m ih =>
      intro k
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have h1 : (j + j) % 2 = 0 := by omega
        have h2 : (j + j + 1) % 2 = 1 := by omega
        have h3 : (j + j) / 2 = j := by omega
        have h4 : (j + j + 1) / 2 = j := by omega
        simp [bits, incrW, h1, h2, h3, h4]
      · have h1 : (2 * j + 1) % 2 = 1 := by omega
        have h2 : (2 * j + 1 + 1) % 2 = 0 := by omega
        have h3 : (2 * j + 1) / 2 = j := by omega
        have h4 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
        simp [bits, incrW, h1, h2, h3, h4, ih]

/-- `[true]` if the word has a `0`, `[]` if it is all ones. -/
def notAllW : Word → Word
  | [] => []
  | false :: _ => [true]
  | true :: u => notAllW u

theorem length_notAllW_le : ∀ u : Word, (notAllW u).length ≤ 1
  | [] => by simp [notAllW]
  | false :: _ => by simp [notAllW]
  | true :: u => by simpa [notAllW] using length_notAllW_le u

theorem notAllW_bits (m : ℕ) : ∀ k, k < 2 ^ m →
    notAllW (bits m k) = if k + 1 < 2 ^ m then [true] else [] := by
  induction m with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := by simpa using hk
    simp [bits, notAllW]
  | succ m ih =>
      intro k hk
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have h1 : (j + j) % 2 = 0 := by omega
        have h3 : (j + j) / 2 = j := by omega
        have : j + j + 1 < 2 ^ (m + 1) := by rw [pow_succ]; omega
        simp [bits, notAllW, h1, h3, this]
      · have h1 : (2 * j + 1) % 2 = 1 := by omega
        have h3 : (2 * j + 1) / 2 = j := by omega
        have hj : j < 2 ^ m := by rw [pow_succ] at hk; omega
        simp only [bits, h1, h3, beq_self_eq_true, notAllW]
        rw [ih j hj]
        have : (j + 1 < 2 ^ m) ↔ (2 * j + 1 + 1 < 2 ^ (m + 1)) := by rw [pow_succ]; omega
        by_cases h : j + 1 < 2 ^ m
        · rw [if_pos h, if_pos (this.1 h)]
        · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]

/-- Every word of length `m` is a counter value below `2^m`. -/
theorem exists_bits : ∀ (u : Word), ∃ k, k < 2 ^ u.length ∧ bits u.length k = u
  | [] => ⟨0, by simp, rfl⟩
  | b :: u => by
      obtain ⟨k, hk, hbk⟩ := exists_bits u
      refine ⟨(if b then 1 else 0) + 2 * k, ?_, ?_⟩
      · simp only [List.length_cons, pow_succ]; cases b <;> simp <;> omega
      · simp only [List.length_cons, bits]
        cases b
        · have h1 : (0 + 2 * k) % 2 = 0 := by omega
          have h3 : (0 + 2 * k) / 2 = k := by omega
          simp [hbk]
        · have h1 : (1 + 2 * k) % 2 = 1 := by omega
          have h3 : (1 + 2 * k) / 2 = k := by omega
          simp [h1, h3, hbk]

/-- The witness coded by a word: drop the leading ones and the first zero. -/
def decodeW : Word → Word
  | [] => []
  | true :: u => decodeW u
  | false :: u => u

theorem length_decodeW_le : ∀ u : Word, (decodeW u).length ≤ u.length
  | [] => le_rfl
  | true :: u => by simp only [decodeW, List.length_cons]; have := length_decodeW_le u; omega
  | false :: u => by simp [decodeW]

theorem decodeW_code (j : ℕ) (w : Word) : decodeW (List.replicate j true ++ false :: w) = w := by
  induction j with
  | zero => rfl
  | succ j ih => simpa [List.replicate_succ, decodeW] using ih

/-! ### The Cobham terms -/

/-- `incrW` as a Cobham term. -/
def incrC : Cob :=
  .bRec .empty (.comp (.app true) [.proj 0]) (.comp (.app false) [.proj 1]) (.proj 0)

@[simp] theorem eval_incrC (u : Word) : incrC.eval [u] = incrW u := by
  induction u with
  | nil => simp [incrC, incrW]
  | cons b u ih =>
      rw [incrC, Cob.eval_bRec_cons, ← incrC, ih]
      cases b <;> simp [incrW, List.take_of_length_le]

/-- `notAllW` as a Cobham term. -/
def notAllC : Cob := .bRec .empty Cob.trueC (.proj 1) (.proj 0)

@[simp] theorem eval_notAllC (u : Word) : notAllC.eval [u] = notAllW u := by
  induction u with
  | nil => simp [notAllC, notAllW]
  | cons b u ih =>
      rw [notAllC, Cob.eval_bRec_cons, ← notAllC, ih]
      cases b
      · simp [notAllW]
      · have := length_notAllW_le u
        simp only [if_true, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, notAllW,
          List.length_cons]
        exact List.take_of_length_le (by omega)

/-- `decodeW` as a Cobham term. -/
def decodeC : Cob := .bRec .empty (.proj 0) (.proj 1) (.proj 0)

@[simp] theorem eval_decodeC (u : Word) : decodeC.eval [u] = decodeW u := by
  induction u with
  | nil => simp [decodeC, decodeW]
  | cons b u ih =>
      rw [decodeC, Cob.eval_bRec_cons, ← decodeC, ih]
      cases b
      · simp [decodeW, List.take_of_length_le]
      · have := length_decodeW_le u
        simp only [if_true, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, decodeW,
          List.length_cons]
        exact List.take_of_length_le (by omega)

/-- The word `0^{|u|}`. -/
def zerosC : Cob :=
  .bRec .empty (.comp (.app false) [.proj 1]) (.comp (.app false) [.proj 1]) (.proj 0)

@[simp] theorem eval_zerosC (u : Word) : zerosC.eval [u] = List.replicate u.length false := by
  induction u with
  | nil => simp [zerosC]
  | cons b u ih =>
      rw [zerosC, Cob.eval_bRec_cons, ← zerosC, ih]
      cases b <;> simp [List.replicate_succ, List.take_of_length_le]

end NPW

namespace OProg

open Prog Tracks

/-! ### From a specification to `PSPACE^A` -/

/-- **Membership in `PSPACE^A` from a specification**: a program that runs from the empty
configuration, within a polynomial number of cells, to a state whose scanned bit is set exactly on
the members of `L`. -/
theorem inPSPACE_rel_of_oruns (A : Oracle) (p : OProg) (L : Language) (B : List Bool → ℕ)
    (s : ℕ → ℕ) (hs : PolyBound s) (out : List Bool → TState) (hB1 : ∀ x, 1 ≤ B x)
    (hBs : ∀ x, B x ≤ s x.length)
    (hrun : ∀ x, ORuns A x (B x) p ⟨fun _ => false, 0, 0⟩ (out x))
    (hout : ∀ x, (out x).view (out x).head = true ↔ L x) : InPSPACE_rel A L := by
  have hex : ∀ x, ∃ d, OExec A x (fun c => c.space ≤ B x) p oinit d ∧ d.abs = out x ∧
      d.qtape = [] ∧ d.space ≤ B x := fun x =>
    hrun x oinit (by simp [OConfig.abs, oinit]) rfl
      (le_trans (by simp [OConfig.space, oinit]) (hB1 x))
  choose dd hdd using hex
  refine ⟨s, hs, odspace_of_oexec A p L B s dd hBs (fun x => (hdd x).1) (fun x => (hdd x).2.2.2)
    (fun x => ?_)⟩
  rw [← hout x, ← (hdd x).2.1]
  rfl

/-! ### `P^A ⊆ PSPACE^A` -/

/-- The oracle program deciding the language of an oracle term `t`. -/
def oDecider (t : CobQ) : OProg :=
  .seq (lift (write true)) (.seq (lift (copyInput (t.need + 2) 0))
    (.seq (compileQ (t.need + 2) t [0] 1 2) (lift (mvR 3))))

theorem oruns_oDecider (A : Oracle) (t : CobQ) (x : List Bool) :
    ORuns A x ((t.spaceW x.length + 3) * wd (t.need + 2)) (oDecider t) ⟨fun _ => false, 0, 0⟩
      ⟨lay (t.need + 2) (Function.update (Function.update (fun _ => []) 0 x) 1
        (CobQ.eval A t [x])), 3, x.length⟩ := by
  set K := t.need + 2 with hK
  set B := (t.spaceW x.length + 3) * wd K with hB
  have hle := CobQ.le_spaceW t x.length
  have hB' : (x.length + 3) * wd K ≤ B := Nat.mul_le_mul_right _ (by omega)
  unfold oDecider
  refine (ORuns.lift (runs_write true _ 0 0)).seq ?_
  rw [lay_empty K]
  refine (ORuns.lift (runs_copyInput (fun _ => []) 0 (by omega) rfl x.length le_rfl hB')).seq ?_
  have hc := compileQOK (A := A) (K := K) (x := x) (B := B) t [0] 1 2
    (Function.update (fun _ => []) 0 x) x.length x.length (by simp) (by omega) (by simp)
    (by omega) (fun r hr => by rw [Function.update_of_ne (by omega)])
    (fun r => by rw [Function.update_apply]; split_ifs <;> simp) le_rfl
  simp only [List.map_cons, List.map_nil, Function.update_self] at hc
  refine hc.seq ?_
  refine (ORuns.lift (runs_mvR 3 _ 0 _ ?_)).of_eq rfl (by simp)
  have : 3 < wd K := by womega
  have : wd K ≤ B :=
    le_trans (by omega) (Nat.mul_le_mul_right _ (show 1 ≤ t.spaceW x.length + 3 by omega))
  omega

end OProg

open OProg Tracks in
/-- **`P^A ⊆ PSPACE^A`**, for every oracle `A`. -/
theorem inPSPACE_rel_of_inP_rel {A : Oracle} {L : Language} (hL : InP_rel A L) :
    InPSPACE_rel A L := by
  obtain ⟨t, ht⟩ := hL
  refine inPSPACE_rel_of_oruns A (oDecider t) L
    (fun x => (t.spaceW x.length + 3) * wd (t.need + 2))
    (fun n => (t.spaceW n + 3) * wd (t.need + 2))
    (PolyBound.mul_const' ((CobQ.spaceW_polyBound t).add (polyBound_const 3)) _) _ (fun x => ?_)
    (fun x => le_rfl) (oruns_oDecider A t) (fun x => ?_)
  · have : 1 ≤ wd (t.need + 2) := by womega
    nlinarith
  · dsimp only
    have := lay_pres (K := t.need + 2)
      (Function.update (Function.update (fun _ => []) 0 x) 1 (CobQ.eval A t [x])) 1 (by omega) 0
    simp only [zero_mul, zero_add, Function.update_self] at this
    rw [show (3 : ℕ) = 2 * 1 + 1 from rfl, this, ht x, decide_eq_true_iff, List.length_pos_iff]


/-! ### `NP^A ⊆ PSPACE^A` -/

namespace NPW

open OProg Prog Tracks

/-- The registers of the witness loop: the input, the counter, the flag "a witness was found",
the flag "continue", and one temporary register. -/
def regs (x u f c t : Word) : ℕ → Word
  | 0 => x
  | 1 => u
  | 2 => f
  | 3 => c
  | 4 => t
  | _ + 5 => []

@[simp] theorem regs_zero (x u f c t : Word) : regs x u f c t 0 = x := rfl
@[simp] theorem regs_one (x u f c t : Word) : regs x u f c t 1 = u := rfl
@[simp] theorem regs_two (x u f c t : Word) : regs x u f c t 2 = f := rfl
@[simp] theorem regs_three (x u f c t : Word) : regs x u f c t 3 = c := rfl
@[simp] theorem regs_four (x u f c t : Word) : regs x u f c t 4 = t := rfl

theorem regs_high (x u f c t : Word) (r : ℕ) (hr : 5 ≤ r) : regs x u f c t r = [] := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 5 := ⟨r - 5, by omega⟩
  rfl

theorem regs_len (x u f c t : Word) (N : ℕ) (hx : x.length ≤ N) (hu : u.length ≤ N)
    (hf : f.length ≤ N) (hc : c.length ≤ N) (ht : t.length ≤ N) (r : ℕ) :
    (regs x u f c t r).length ≤ N := by
  rcases r with _ | _ | _ | _ | _ | r <;> simp [regs, *]

theorem update_regs_one (x u f c t u' : Word) :
    Function.update (regs x u f c t) 1 u' = regs x u' f c t := by
  funext r; rcases r with _ | _ | _ | _ | _ | r <;> simp [Function.update, regs]

theorem update_regs_two (x u f c t f' : Word) :
    Function.update (regs x u f c t) 2 f' = regs x u f' c t := by
  funext r; rcases r with _ | _ | _ | _ | _ | r <;> simp [Function.update, regs]

theorem update_regs_three (x u f c t c' : Word) :
    Function.update (regs x u f c t) 3 c' = regs x u f c' t := by
  funext r; rcases r with _ | _ | _ | _ | _ | r <;> simp [Function.update, regs]

theorem update_regs_four (x u f c t t' : Word) :
    Function.update (regs x u f c t) 4 t' = regs x u f c t' := by
  funext r; rcases r with _ | _ | _ | _ | _ | r <;> simp [Function.update, regs]

theorem update_empty_zero (x : Word) :
    Function.update (fun _ => ([] : Word)) 0 x = regs x [] [] [] [] := by
  funext r; rcases r with _ | _ | _ | _ | _ | r <;> simp [Function.update, regs]

/-- The step of the witness loop: `f := f ∨ v(x, decode u)`. -/
def tF (v : CobQ) : CobQ :=
  .comp CobQ.orQ [.comp v [.proj 0, .comp (CobQ.ofCob decodeC) [.proj 1]], .proj 2]

theorem eval_tF (A : Oracle) (v : CobQ) (x u f : Word) :
    CobQ.eval A (tF v) [x, u, f] = if CobQ.eval A v [x, decodeW u] = [] then f else [true] := by
  simp [tF, CobQ.eval_ofCob]

/-- The "continue" test: the counter is not all ones. -/
def tNA : CobQ := CobQ.ofCob notAllC

/-- The increment of the counter. -/
def tInc : CobQ := CobQ.ofCob incrC

/-- The initial counter `0^m`, `m = a (|x| + 1)^k + 1`. -/
def tZ (a k : ℕ) : CobQ := CobQ.ofCob (.comp zerosC [.comp (.app true) [Collapse.polyC a k]])

theorem eval_tZ (A : Oracle) (a k : ℕ) (x : Word) :
    CobQ.eval A (tZ a k) [x] = List.replicate (a * (x.length + 1) ^ k + 1) false := by
  simp [tZ, CobQ.eval_ofCob]

/-- The constant `[true]`. -/
def tT : CobQ := CobQ.ofCob Cob.trueC

/-- The body of the witness loop. -/
def npBody (v : CobQ) (K : ℕ) : OProg :=
  .seq (compileQ K (tF v) [0, 1, 2] 4 6) (.seq (lift (assign K 4 2)) (.seq (lift (clear K 4))
    (.seq (compileQ K tNA [1] 3 6) (.seq (compileQ K tInc [1] 4 6)
      (.seq (lift (assign K 4 1)) (lift (clear K 4)))))))

/-- The whole decider. -/
def npProg (v : CobQ) (a k K : ℕ) : OProg :=
  .seq (lift (write true)) (.seq (lift (copyInput K 0)) (.seq (compileQ K (tZ a k) [0] 1 6)
    (.seq (compileQ K tT [] 3 6) (.seq (owhileNE 3 (npBody v K)) (lift (mvR 5))))))

theorem oruns_npBody (A : Oracle) (v : CobQ) (K : ℕ) (x : List Bool) (B N : ℕ) (u f c : Word)
    (i : ℕ) (hKF : 6 + (tF v).need ≤ K) (hKN : 6 + tNA.need ≤ K) (hKI : 6 + tInc.need ≤ K)
    (hx : x.length ≤ N) (hu : u.length ≤ N) (hf : f.length ≤ 1) (hc : c.length ≤ N)
    (hN1 : 1 ≤ N) (hBF : ((tF v).spaceW N + 3) * wd K ≤ B)
    (hBN : (tNA.spaceW N + 3) * wd K ≤ B) (hBI : (tInc.spaceW N + 3) * wd K ≤ B) :
    ORuns A x B (npBody v K) ⟨lay K (regs x u f c []), 0, i⟩
      ⟨lay K (regs x (incrW u) (if CobQ.eval A v [x, decodeW u] = [] then f else [true])
        (notAllW u) []), 0, i⟩ := by
  have hB : (N + 3) * wd K ≤ B :=
    le_trans (Nat.mul_le_mul_right _ (by have := CobQ.le_spaceW (tF v) N; omega)) hBF
  have hf'1 : (if CobQ.eval A v [x, decodeW u] = [] then f else [true]).length ≤ 1 := by
    split_ifs <;> simp [hf]
  have hna := length_notAllW_le u
  unfold npBody
  have h1 := compileQOK (A := A) (K := K) (x := x) (B := B) (tF v) [0, 1, 2] 4 6
    (regs x u f c []) N i (by simp) (by omega) (by simp) hKF
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N hx hu (by omega) hc (by simp)) hBF
  simp only [List.map_cons, List.map_nil, regs_zero, regs_one, regs_two, eval_tF,
    update_regs_four] at h1
  generalize (if CobQ.eval A v [x, decodeW u] = [] then f else [true]) = f' at h1 hf'1 ⊢
  refine h1.seq ?_
  refine ORunsQ.seq ((oruns_assign _ 4 2 (by omega) (by omega) (by omega) N (by simp; omega)
    (by simp; omega) hB i).of_eq rfl (by rw [regs_four, update_regs_two])) ?_
  refine ORunsQ.seq ((oruns_clear _ 4 (by omega) N (by simp; omega) hB i).of_eq rfl
    (by rw [update_regs_four])) ?_
  have h4 := compileQOK (A := A) (K := K) (x := x) (B := B) tNA [1] 3 6
    (regs x u f' c []) N i (by simp) (by omega) (by simp) hKN
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N hx hu (by omega) hc (by simp)) hBN
  simp only [List.map_cons, List.map_nil, regs_one, tNA, CobQ.eval_ofCob, eval_notAllC,
    update_regs_three] at h4
  refine ORunsQ.seq h4 ?_
  have h5 := compileQOK (A := A) (K := K) (x := x) (B := B) tInc [1] 4 6
    (regs x u f' (notAllW u) []) N i (by simp) (by omega) (by simp) hKI
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N hx hu (by omega) (by omega) (by simp)) hBI
  simp only [List.map_cons, List.map_nil, regs_one, tInc, CobQ.eval_ofCob, eval_incrC,
    update_regs_four] at h5
  refine ORunsQ.seq h5 ?_
  refine ORunsQ.seq ((oruns_assign _ 4 1 (by omega) (by omega) (by omega) N (by simp; omega)
    (by simp; omega) hB i).of_eq rfl (by rw [regs_four, update_regs_one])) ?_
  exact (oruns_clear _ 4 (by omega) N (by simp; omega) hB i).of_eq rfl (by rw [update_regs_four])

/-! #### The loop invariant -/

theorem bits_zero (m : ℕ) : bits m 0 = List.replicate m false := by
  induction m with
  | zero => rfl
  | succ m ih => simp [bits, ih, List.replicate_succ]

/-- The flag register after the first `j` counter values. -/
def foundW (A : Oracle) (v : CobQ) (x : Word) (m : ℕ) : ℕ → Word
  | 0 => []
  | j + 1 => if CobQ.eval A v [x, decodeW (bits m j)] = [] then foundW A v x m j else [true]

theorem length_foundW_le (A : Oracle) (v : CobQ) (x : Word) (m : ℕ) :
    ∀ j, (foundW A v x m j).length ≤ 1
  | 0 => by simp [foundW]
  | j + 1 => by
      simp only [foundW]
      split_ifs
      · exact length_foundW_le A v x m j
      · simp

theorem foundW_ne_nil_iff (A : Oracle) (v : CobQ) (x : Word) (m : ℕ) :
    ∀ j, foundW A v x m j ≠ [] ↔ ∃ i < j, CobQ.eval A v [x, decodeW (bits m i)] ≠ []
  | 0 => by simp [foundW]
  | j + 1 => by
      simp only [foundW]
      split_ifs with h
      · rw [foundW_ne_nil_iff A v x m j]
        constructor
        · rintro ⟨i, hi, hne⟩; exact ⟨i, by omega, hne⟩
        · rintro ⟨i, hi, hne⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
          · exact ⟨i, hi, hne⟩
          · exact absurd h hne
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff]
        exact ⟨j, by omega, h⟩

/-- **Every short witness is tried.** -/
theorem exists_witness_iff (A : Oracle) (v : CobQ) (x : Word) (ℓ : ℕ)
    (hlen : ∀ w, CobQ.eval A v [x, w] ≠ [] → w.length ≤ ℓ) :
    (∃ i < 2 ^ (ℓ + 1), CobQ.eval A v [x, decodeW (bits (ℓ + 1) i)] ≠ []) ↔
      ∃ w, CobQ.eval A v [x, w] ≠ [] := by
  constructor
  · rintro ⟨i, -, h⟩; exact ⟨_, h⟩
  · rintro ⟨w, hw⟩
    have hwl := hlen w hw
    set u := List.replicate (ℓ - w.length) true ++ false :: w with hu
    have hul : u.length = ℓ + 1 := by simp [hu]; omega
    obtain ⟨i, hi, hbi⟩ := exists_bits u
    rw [hul] at hi hbi
    refine ⟨i, hi, ?_⟩
    rw [hbi, hu, decodeW_code]
    exact hw

/-- The "continue" register after `j` steps. -/
def contW (m j : ℕ) : Word := if j < 2 ^ m then [true] else []

/-! #### The decider -/

/-- The length of the counter. -/
def mW (a k n : ℕ) : ℕ := a * (n + 1) ^ k + 1

/-- A bound on every register. -/
def NW (a k n : ℕ) : ℕ := n + mW a k n + 1

/-- The work space of the compiled terms. -/
def SW (v : CobQ) (a k N : ℕ) : ℕ :=
  (tF v).spaceW N + tNA.spaceW N + tInc.spaceW N + (tZ a k).spaceW N + tT.spaceW N

/-- The number of registers. -/
def npK (v : CobQ) (a k : ℕ) : ℕ :=
  7 + (tF v).need + tNA.need + tInc.need + (tZ a k).need + tT.need

/-- The space bound. -/
def npB (v : CobQ) (a k n : ℕ) : ℕ := (SW v a k (NW a k n) + 3) * wd (npK v a k)

theorem oruns_npProg (A : Oracle) (v : CobQ) (a k : ℕ) (x : List Bool) :
    ORuns A x (npB v a k x.length) (npProg v a k (npK v a k)) ⟨fun _ => false, 0, 0⟩
      ⟨lay (npK v a k) (regs x (bits (mW a k x.length) (2 ^ mW a k x.length))
        (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)) [] []), 5, x.length⟩ := by
  set n := x.length with hn
  set m := mW a k n with hm
  set N := NW a k n with hN
  set K := npK v a k with hK
  set B := npB v a k n with hB
  have hKv : 7 + (tF v).need + tNA.need + tInc.need + (tZ a k).need + tT.need = K := rfl
  have hBv : (SW v a k N + 3) * wd K = B := rfl
  have hSv : SW v a k N =
      (tF v).spaceW N + tNA.spaceW N + tInc.spaceW N + (tZ a k).spaceW N + tT.spaceW N := rfl
  have hNv : N = n + m + 1 := rfl
  have hle := CobQ.le_spaceW (tF v) N
  have hBF : ((tF v).spaceW N + 3) * wd K ≤ B := hBv ▸ Nat.mul_le_mul_right _ (by omega)
  have hBN : (tNA.spaceW N + 3) * wd K ≤ B := hBv ▸ Nat.mul_le_mul_right _ (by omega)
  have hBI : (tInc.spaceW N + 3) * wd K ≤ B := hBv ▸ Nat.mul_le_mul_right _ (by omega)
  have hBZ : ((tZ a k).spaceW N + 3) * wd K ≤ B := hBv ▸ Nat.mul_le_mul_right _ (by omega)
  have hBT : (tT.spaceW N + 3) * wd K ≤ B := hBv ▸ Nat.mul_le_mul_right _ (by omega)
  have hB3 : (N + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hBF
  have hwd : 5 < wd K := by womega
  have hwdB : wd K < B := lt_of_lt_of_le (by nlinarith) hB3
  unfold npProg
  refine (ORuns.lift (runs_write true _ 0 0)).seq ?_
  rw [lay_empty K]
  refine (ORuns.lift (runs_copyInput (fun _ => []) 0 (by omega) rfl N (by omega) hB3)).seq ?_
  rw [update_empty_zero]
  have hz := compileQOK (A := A) (K := K) (x := x) (B := B) (tZ a k) [0] 1 6
    (regs x [] [] [] []) N n (by simp) (by omega) (by simp) (by omega)
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N (by omega) (by simp) (by simp) (by simp) (by simp)) hBZ
  simp only [List.map_cons, List.map_nil, regs_zero, eval_tZ, update_regs_one, ← hn] at hz
  rw [show a * (n + 1) ^ k + 1 = m from rfl, ← bits_zero] at hz
  refine ORunsQ.seq hz ?_
  have ht := compileQOK (A := A) (K := K) (x := x) (B := B) tT [] 3 6
    (regs x (bits m 0) [] [] []) N n (by simp) (by omega) (by simp) (by omega)
    (fun r hr => regs_high _ _ _ _ _ r (by omega))
    (regs_len _ _ _ _ _ N (by omega) (by simp; omega) (by simp) (by simp) (by simp)) hBT
  simp only [List.map_nil, tT, CobQ.eval_ofCob, Cob.eval_trueC, update_regs_three] at ht
  refine ORunsQ.seq ht ?_
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hloop := oruns_whileNE (A := A) (x := x) (B := B)
    (fun j => regs x (bits m j) (foundW A v x m j) (contW m j) []) 3 (2 ^ m) (K := K)
    (by omega) (npBody v K) (fun j hj => by simp [contW, hj]) (by simp [contW]) hwdB n
    (fun j hj => by
      have := oruns_npBody A v K x B N (bits m j) (foundW A v x m j) (contW m j) n
        (by omega) (by omega) (by omega) (by omega) (by simp; omega) (length_foundW_le A v x m j)
        (by simp only [contW, hj, if_true, List.length_singleton]; omega) (by omega) hBF hBN hBI
      refine this.of_eq rfl ?_
      rw [incrW_bits, notAllW_bits m j hj]
      rfl)
  have h0 : regs x (bits m 0) [] [true] [] =
      regs x (bits m 0) (foundW A v x m 0) (contW m 0) [] := by
    simp [foundW, contW, hpos]
  rw [h0]
  refine ORunsQ.seq hloop ?_
  simp only [contW, lt_irrefl, if_false]
  exact (ORuns.lift (runs_mvR 5 _ 0 n (by omega))).of_eq rfl (by simp)

end NPW

open OProg Tracks NPW in
/-- **`NP^A ⊆ PSPACE^A`**, for every oracle `A`: try every witness in polynomial space. -/
theorem inPSPACE_rel_of_inNP_rel {A : Oracle} {L : Language} (hL : InNP_rel A L) :
    InPSPACE_rel A L := by
  obtain ⟨v, p, ⟨a, k, ha⟩, -, hlen, hLv⟩ := hL
  have hid : PolyBound (fun n => n) := ⟨1, 1, fun n => by simp⟩
  have hak : PolyBound (fun n => a * (n + 1) ^ k) := ⟨a, k, fun _ => le_rfl⟩
  have hNW : PolyBound (NW a k) :=
    PolyBound.mono (((hid.add hak).add (polyBound_const 1)).add (polyBound_const 1))
      (fun _ => le_rfl)
  have hSW : PolyBound (SW v a k) :=
    PolyBound.mono (((((CobQ.spaceW_polyBound (tF v)).add (CobQ.spaceW_polyBound tNA)).add
      (CobQ.spaceW_polyBound tInc)).add (CobQ.spaceW_polyBound (tZ a k))).add
      (CobQ.spaceW_polyBound tT)) (fun _ => le_rfl)
  refine inPSPACE_rel_of_oruns A (npProg v a k (npK v a k)) L (fun x => npB v a k x.length)
    (npB v a k) (PolyBound.mono (PolyBound.mul_const' ((hSW.comp hNW).add (polyBound_const 3))
      (wd (npK v a k))) (fun _ => le_rfl)) _ (fun x => ?_) (fun x => le_rfl)
    (oruns_npProg A v a k) (fun x => ?_)
  · have : 1 ≤ wd (npK v a k) := by womega
    unfold npB
    nlinarith
  · dsimp only
    have := lay_pres (K := npK v a k) (regs x (bits (mW a k x.length) (2 ^ mW a k x.length))
      (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)) [] []) 2 (by unfold npK; omega) 0
    simp only [zero_mul, zero_add, regs_two] at this
    have h5 : lay (npK v a k) (regs x (bits (mW a k x.length) (2 ^ mW a k x.length))
        (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)) [] []) 5 = true ↔
        0 < (foundW A v x (mW a k x.length) (2 ^ mW a k x.length)).length := by
      rw [show (5 : ℕ) = 2 * 2 + 1 from rfl, this]
      exact decide_eq_true_iff
    rw [h5, hLv x, List.length_pos_iff, foundW_ne_nil_iff, mW]
    exact exists_witness_iff A v x _ (fun w hw => le_trans (hlen x w hw) (ha _))

end Complexity.Space
