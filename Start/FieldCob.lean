/-
**Arithmetic in `ZMod p` as Cobham terms, polynomial evaluation, and a prime found by the
verifier.**

The verifier of Shamir's protocol computes in a prime field `ZMod p` whose size is only
*polynomial* in the length of the input: `p` has to exceed the soundness bound
`d · rounds` of `Start/SumCheck.lean` by a constant factor, and nothing more.  An element of
`ZMod p` can therefore be written in **unary**, `k ↦ 1^k` with `k < p`, at polynomial cost, and in
that representation the field operations are one-line Cobham terms over the unary toolkit of the
library: concatenation and the smash function followed by Euclidean division
(`Complexity.Cob.modT`).  This replaces the binary representation of the task description; the
point of the binary representation — keeping the word lengths polynomial — is already met.

Main definitions:

* `Complexity.Cob.fAdd`, `.fMul`, `.fSub` — addition, multiplication and subtraction modulo `p`;
* `Complexity.Cob.hornerT`, `Complexity.Cob.polyEvalT` — the evaluation, by Horner's rule, of a
  polynomial given by its list of coefficients (a word of unary fields,
  `Complexity.fieldsWord`) at a point;
* `Complexity.Cob.isPrimeT` — primality of a unary number by trial division;
* `Complexity.Cob.findPrimeT` — a prime in `(m, 2m]`, found by trial division of the candidates.

Main results:

* `Complexity.Cob.eval_fAdd`, `.eval_fMul`, `.eval_fSub` with `Complexity.zmod_fAdd`,
  `.zmod_fMul`, `.zmod_fSub` — **the operations are Cobham functions, correct against
  `ZMod p`**;
* `Complexity.Cob.eval_polyEvalT`, `Complexity.zmod_hornerN` — **evaluation of a coefficient
  list at a point is a Cobham function**, computing `Complexity.Qbf.evalL` in `ZMod p`;
* `Complexity.Cob.eval_isPrimeT` — **primality of a unary number is decided by a Cobham term**;
* `Complexity.Cob.eval_findPrimeT` — **a prime `p` with `m < p ≤ 2m` is computed by a Cobham
  term from `1^m`** (by Bertrand's postulate, the search always succeeds).
-/

import Start.UniformGrid
import Start.CobhamUnary
import Start.SumCheck

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Field operations -/

/-- Addition modulo the length of `s`. -/
def Cob.fAdd (t u s : Cob) : Cob := Cob.modT (Cob.uAdd t u) s

/-- Multiplication modulo the length of `s`. -/
def Cob.fMul (t u s : Cob) : Cob := Cob.modT (.comp .smash [t, u]) s

/-- Subtraction modulo the length of `s` (for a subtrahend at most `p`). -/
def Cob.fSub (t u s : Cob) : Cob := Cob.modT (Cob.uAdd t (.comp Cob.dropU [u, s])) s

theorem Cob.eval_fAdd {t u s : Cob} {args : List Word} {a b p : ℕ} (hp : 0 < p)
    (ht : t.eval args = List.replicate a true) (hu : u.eval args = List.replicate b true)
    (hs : s.eval args = List.replicate p true) :
    (Cob.fAdd t u s).eval args = List.replicate ((a + b) % p) true :=
  Cob.eval_modT hp (Cob.eval_uAdd ht hu) hs

theorem Cob.eval_fMul {t u s : Cob} {args : List Word} {a b p : ℕ} (hp : 0 < p)
    (ht : t.eval args = List.replicate a true) (hu : u.eval args = List.replicate b true)
    (hs : s.eval args = List.replicate p true) :
    (Cob.fMul t u s).eval args = List.replicate ((a * b) % p) true :=
  Cob.eval_modT hp (by simp [ht, hu]) hs

theorem Cob.eval_fSub {t u s : Cob} {args : List Word} {a b p : ℕ} (hp : 0 < p)
    (ht : t.eval args = List.replicate a true) (hu : u.eval args = List.replicate b true)
    (hs : s.eval args = List.replicate p true) :
    (Cob.fSub t u s).eval args = List.replicate ((a + (p - b)) % p) true :=
  Cob.eval_modT hp (Cob.eval_uAdd ht (by simp [hu, hs])) hs

theorem zmod_fAdd (p a b : ℕ) : (((a + b) % p : ℕ) : ZMod p) = a + b := by
  rw [ZMod.natCast_mod]; push_cast; ring

theorem zmod_fMul (p a b : ℕ) : (((a * b) % p : ℕ) : ZMod p) = a * b := by
  rw [ZMod.natCast_mod]; push_cast; ring

theorem zmod_fSub {p b : ℕ} (a : ℕ) (hb : b ≤ p) : (((a + (p - b)) % p : ℕ) : ZMod p) = a - b := by
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub hb, ZMod.natCast_self]; ring

/-! ### Horner's rule on a word of unary coefficients -/

/-- The state of the Horner recursion, read from the right: the value `V` of the coefficients
already completed, and the count `c` of the ones of the current coefficient. -/
def hornerSt (x p : ℕ) : Word → ℕ × ℕ
  | [] => (0, 0)
  | true :: w => ((hornerSt x p w).1, (hornerSt x p w).2 + 1)
  | false :: w => (((hornerSt x p w).2 + (x * (hornerSt x p w).1) % p) % p, 0)

/-- Horner's rule on a list of numbers, modulo `p`. -/
def hornerN (x p : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => (c + (x * hornerN x p cs) % p) % p

theorem hornerSt_fst_lt {x p : ℕ} (hp : 0 < p) : ∀ w : Word, (hornerSt x p w).1 < p
  | [] => hp
  | true :: w => hornerSt_fst_lt hp w
  | false :: _ => Nat.mod_lt _ hp

theorem hornerSt_snd_le (x p : ℕ) : ∀ w : Word, (hornerSt x p w).2 ≤ w.length
  | [] => le_rfl
  | true :: w => by have := hornerSt_snd_le x p w; simp [hornerSt]; omega
  | false :: _ => by simp [hornerSt]

theorem hornerSt_replicate_append (x p : ℕ) (c : ℕ) (w : Word) :
    hornerSt x p (List.replicate c true ++ w) =
      ((hornerSt x p w).1, (hornerSt x p w).2 + c) := by
  induction c with
  | zero => simp
  | succ c ih =>
      rw [List.replicate_succ, List.cons_append, hornerSt, ih]
      simp; omega

theorem hornerSt_fieldsWord (x p : ℕ) :
    ∀ (c : ℕ) (cs : List ℕ), hornerSt x p (fieldsWord (c :: cs)) = (hornerN x p cs, c)
  | c, [] => by simp [fieldsWord, hornerSt_replicate_append, hornerSt, hornerN]
  | c, c' :: cs => by
      rw [fieldsWord, List.append_assoc, hornerSt_replicate_append, List.singleton_append,
        hornerSt, hornerSt_fieldsWord x p c' cs]
      simp [hornerN]

/-- `hornerN` computes the value of the coefficient list in `ZMod p`. -/
theorem zmod_hornerN (x p : ℕ) :
    ∀ cs : List ℕ, (hornerN x p cs : ZMod p) =
      Qbf.evalL (cs.map fun c => (c : ZMod p)) (x : ZMod p)
  | [] => by simp [hornerN, Qbf.evalL]
  | c :: cs => by
      rw [hornerN, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod, Nat.cast_mul,
        zmod_hornerN x p cs]
      rfl

/-- The current coefficient, read off a Horner state `1^V 0 1^c`. -/
def Cob.stC (st : Cob) : Cob := .comp Cob.tail [.comp Cob.dropOnes [st]]

/-- The completed value, read off a Horner state `1^V 0 1^c`. -/
def Cob.stV (st : Cob) : Cob := .comp Cob.leadOnes [st]

theorem Cob.eval_stC {st : Cob} {args : List Word} {V c : ℕ} (h : st.eval args = dmW V c) :
    (Cob.stC st).eval args = List.replicate c true := by
  simp [Cob.stC, h]

theorem Cob.eval_stV {st : Cob} {args : List Word} {V c : ℕ} (h : st.eval args = dmW V c) :
    (Cob.stV st).eval args = List.replicate V true := by
  simp [Cob.stV, h]

/-- The Horner recursion as a bounded recursion on notation over the coefficient word, with the
point and the modulus as the other two arguments. -/
def Cob.hornerT : Cob :=
  .bRec (Cob.constT [false])
    (.comp Cob.concat
      [Cob.fAdd (Cob.stC (.proj 1)) (Cob.fMul (.proj 2) (Cob.stV (.proj 1)) (.proj 3)) (.proj 3),
        Cob.constT [false]])
    (.comp Cob.concat [.proj 1, Cob.constT [true]])
    (Cob.uSucc (Cob.uAdd (.proj 0) (.proj 2)))

theorem Cob.eval_hornerT {p : ℕ} (hp : 0 < p) (x : ℕ) :
    ∀ w : Word, Cob.hornerT.eval [w, (List.replicate x true), List.replicate p true] =
      dmW (hornerSt x p w).1 (hornerSt x p w).2
  | [] => by simp [Cob.hornerT, hornerSt, dmW]
  | b :: w => by
      have ih := Cob.eval_hornerT hp x w
      have hV := hornerSt_fst_lt (x := x) hp w
      have hc := hornerSt_snd_le x p w
      rw [Cob.hornerT, Cob.eval_bRec_cons, ← Cob.hornerT, ih]
      have hbd : ((Cob.uSucc (Cob.uAdd (.proj 0) (.proj 2))).eval
          ((b :: w) :: [List.replicate x true, List.replicate p true])).length =
            (b :: w).length + p + 1 := by
        simp [Cob.uSucc, Cob.uAdd]; omega
      rw [hbd]
      cases b
      · simp only [Bool.false_eq_true, if_false]
        set V := (hornerSt x p w).1
        set c := (hornerSt x p w).2
        have hst : (Cob.proj 1).eval
            (w :: dmW V c :: [List.replicate x true, List.replicate p true]) = dmW V c := by
          simp
        have hp3 : (Cob.proj 3).eval
            (w :: dmW V c :: [List.replicate x true, List.replicate p true]) =
              List.replicate p true := by simp
        have hmul := Cob.eval_fMul (t := .proj 2) (u := Cob.stV (.proj 1)) (s := .proj 3)
          (a := x) (b := V) hp
          (args := w :: dmW V c :: [List.replicate x true, List.replicate p true])
          (by simp) (Cob.eval_stV hst) hp3
        have hadd := Cob.eval_fAdd hp (Cob.eval_stC hst) hmul hp3
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hadd,
          Cob.eval_constT]
        rw [List.take_of_length_le (by
          have h1 := hbd; simp only [List.length_cons] at h1
          simp only [Nat.add_mod_mod, List.length_append, List.length_replicate, List.length_cons,
            List.length_nil, zero_add, add_le_add_iff_right, ge_iff_le]
          have := Nat.mod_lt (c + x * V) hp
          omega)]
        simp [hornerSt, dmW, V, c]
      · simp only [if_true]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, Cob.eval_proj,
          List.getD_cons_succ, List.getD_cons_zero, Cob.eval_constT]
        rw [List.take_of_length_le (by
          have h1 := hbd; simp only [List.length_cons] at h1
          simp; omega)]
        simp [hornerSt, dmW, List.replicate_succ']

/-- Evaluation of a polynomial, given by the word of its unary coefficients, at a point, modulo
`p`. -/
def Cob.polyEvalT (cT xT pT : Cob) : Cob :=
  Cob.fAdd (Cob.stC (.comp Cob.hornerT [cT, xT, pT]))
    (Cob.fMul xT (Cob.stV (.comp Cob.hornerT [cT, xT, pT])) pT) pT

/-- **Evaluation of a coefficient list at a point is a Cobham function.** -/
theorem Cob.eval_polyEvalT {cT xT pT : Cob} {args : List Word} {cs : List ℕ} {x p : ℕ}
    (hp : 0 < p) (hc : cT.eval args = fieldsWord cs) (hx : xT.eval args = List.replicate x true)
    (hpT : pT.eval args = List.replicate p true) :
    (Cob.polyEvalT cT xT pT).eval args = List.replicate (hornerN x p cs) true := by
  have hst : (Cob.comp Cob.hornerT [cT, xT, pT]).eval args =
      dmW (hornerSt x p (fieldsWord cs)).1 (hornerSt x p (fieldsWord cs)).2 := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hc, hx, hpT]
    exact Cob.eval_hornerT hp x _
  rw [Cob.polyEvalT, Cob.eval_fAdd hp (Cob.eval_stC hst)
    (Cob.eval_fMul hp hx (Cob.eval_stV hst) hpT) hpT]
  congr 1
  cases cs with
  | nil => simp [fieldsWord, hornerSt, hornerN]
  | cons c cs => simp [hornerSt_fieldsWord, hornerN]

/-! ### Primality by trial division -/

/-- The trial-division loop: on `1^j` and `1^k`, whether no `d` with `2 ≤ d ≤ j`, `d < k`
divides `k`. -/
def Cob.primLoop : Cob :=
  let step : Cob :=
    Cob.andT (.proj 1)
      (Cob.orT (Cob.leU (.proj 2) (Cob.uSucc (.proj 0)))
        (Cob.orT (Cob.ltU (Cob.uSucc (.proj 0)) (Cob.constT [true, true]))
          (Cob.boolT (Cob.modT (.proj 2) (Cob.uSucc (.proj 0))))))
  .bRec Cob.trueC step step Cob.trueC

/-- The trial-division condition, as a decidable proposition. -/
def noSmallDiv (k j : ℕ) : Prop := ∀ d < j + 1, 2 ≤ d → d < k → k % d ≠ 0

instance (k j : ℕ) : Decidable (noSmallDiv k j) := by unfold noSmallDiv; infer_instance

theorem noSmallDiv_succ (k j : ℕ) :
    noSmallDiv k (j + 1) ↔ noSmallDiv k j ∧ (k ≤ j + 1 ∨ j + 1 < 2 ∨ k % (j + 1) ≠ 0) := by
  constructor
  · intro h
    refine ⟨fun d hd => h d (by omega), ?_⟩
    by_cases h1 : k ≤ j + 1
    · exact Or.inl h1
    by_cases h2 : j + 1 < 2
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (h (j + 1) (by omega) (by omega) (by omega)))
  · rintro ⟨h, h'⟩ d hd h2 hk
    rcases Nat.lt_or_ge d (j + 1) with hlt | hge
    · exact h d hlt h2 hk
    · have : d = j + 1 := by omega
      subst this
      rcases h' with h' | h' | h'
      · omega
      · omega
      · exact h'

theorem Cob.eval_primLoop (k : ℕ) :
    ∀ j : ℕ, Cob.primLoop.eval [List.replicate j true, List.replicate k true] =
      bw (decide (noSmallDiv k j))
  | 0 => by
      have : noSmallDiv k 0 := fun d hd h2 => by omega
      simp [Cob.primLoop, this]
  | j + 1 => by
      have ih := Cob.eval_primLoop k j
      rw [List.replicate_succ, Cob.primLoop, Cob.eval_bRec_cons, ← Cob.primLoop, ih]
      simp only [if_true]
      set args : List Word := List.replicate j true :: bw (decide (noSmallDiv k j)) ::
        [List.replicate k true]
      have hd : (Cob.uSucc (.proj 0)).eval args = List.replicate (j + 1) true :=
        Cob.eval_uSucc (by simp [args])
      have hk : (Cob.proj 2).eval args = List.replicate k true := by simp [args]
      have h1 : (Cob.leU (.proj 2) (Cob.uSucc (.proj 0))).eval args =
          bw (decide (k ≤ j + 1)) := by rw [Cob.eval_leU, hd, hk]; simp
      have h2 : (Cob.ltU (Cob.uSucc (.proj 0)) (Cob.constT [true, true])).eval args =
          bw (decide (j + 1 < 2)) := by rw [Cob.eval_ltU, hd]; simp
      have h3 : (Cob.boolT (Cob.modT (.proj 2) (Cob.uSucc (.proj 0)))).eval args =
          bw (decide (k % (j + 1) ≠ 0)) := by
        refine Cob.eval_boolT _ _ _ ?_
        rw [Cob.eval_modT (by omega) hk hd]
        simp
      have h0 : (Cob.proj 1).eval args = bw (decide (noSmallDiv k j)) := by simp [args]
      rw [Cob.eval_andT h0 (Cob.eval_orT h1 (Cob.eval_orT h2 h3))]
      have hlen : (bw (decide (noSmallDiv k (j + 1)))).length ≤
          (Cob.trueC.eval ((true :: List.replicate j true) :: [List.replicate k true])).length := by
        unfold bw; split <;> simp
      have hdec : decide (noSmallDiv k (j + 1)) = (decide (noSmallDiv k j) &&
          (decide (k ≤ j + 1) || (decide (j + 1 < 2) || decide (k % (j + 1) ≠ 0)))) := by
        rw [Bool.eq_iff_iff]; simp [noSmallDiv_succ]
      rw [← hdec, List.take_of_length_le hlen]

theorem prime_iff_noSmallDiv (k : ℕ) : Nat.Prime k ↔ 2 ≤ k ∧ noSmallDiv k k := by
  rw [Nat.prime_def_lt]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d _ hd2 hdk hmod => ?_⟩
    have := h d hdk (Nat.dvd_of_mod_eq_zero hmod)
    omega
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [Nat.zero_dvd] at hdvd; omega
      · rfl
    · exact absurd (Nat.mod_eq_zero_of_dvd hdvd) (h m (by omega) hm2 hm)

/-- Primality of a unary number. -/
def Cob.isPrimeT (kT : Cob) : Cob :=
  Cob.andT (Cob.leU (Cob.constT [true, true]) kT) (.comp Cob.primLoop [kT, kT])

/-- **Primality of a unary number is decided by a Cobham term** (trial division). -/
theorem Cob.eval_isPrimeT {kT : Cob} {args : List Word} {k : ℕ}
    (hk : kT.eval args = List.replicate k true) :
    (Cob.isPrimeT kT).eval args = bw (decide (Nat.Prime k)) := by
  have h1 : (Cob.leU (Cob.constT [true, true]) kT).eval args = bw (decide (2 ≤ k)) := by
    rw [Cob.eval_leU, hk]; simp
  have h2 : (Cob.comp Cob.primLoop [kT, kT]).eval args = bw (decide (noSmallDiv k k)) := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hk]
    exact Cob.eval_primLoop k k
  rw [Cob.isPrimeT, Cob.eval_andT h1 h2]
  congr 1
  rw [Bool.eq_iff_iff]
  simp [prime_iff_noSmallDiv]

/-! ### Finding a prime -/

/-- The search loop: on `1^j` and `1^m`, the last prime met among the candidates
`2m, 2m - 1, …, 2m - j + 1`, or the empty word. -/
def Cob.primeSearch : Cob :=
  let cand : Cob := .comp Cob.dropU [.proj 0, Cob.uAdd (.proj 2) (.proj 2)]
  let step : Cob := Cob.iteT (Cob.isPrimeT cand) cand (.proj 1)
  .bRec .empty step step (Cob.uAdd (.proj 1) (.proj 1))

/-- The invariant of the search. -/
def SearchInv (m j : ℕ) (w : Word) : Prop :=
  (w = [] ∧ ¬ ∃ q, Nat.Prime q ∧ 2 * m - j < q ∧ q ≤ 2 * m) ∨
    (∃ q, w = List.replicate q true ∧ Nat.Prime q ∧ 2 * m - j < q ∧ q ≤ 2 * m)

theorem Cob.primeSearch_inv (m : ℕ) :
    ∀ j ≤ m, SearchInv m j (Cob.primeSearch.eval [List.replicate j true, List.replicate m true])
  | 0, _ => by
      left
      refine ⟨by simp [Cob.primeSearch], ?_⟩
      rintro ⟨q, _, h1, h2⟩; omega
  | j + 1, hj => by
      have ih := Cob.primeSearch_inv m j (by omega)
      rw [List.replicate_succ, Cob.primeSearch, Cob.eval_bRec_cons, ← Cob.primeSearch]
      simp only [if_true]
      set acc := Cob.primeSearch.eval [List.replicate j true, List.replicate m true]
      set args : List Word := List.replicate j true :: acc :: [List.replicate m true]
      have hcand : (Cob.comp Cob.dropU [.proj 0, Cob.uAdd (.proj 2) (.proj 2)]).eval args =
          List.replicate (2 * m - j) true := by
        have h2m : (Cob.uAdd (.proj 2) (.proj 2)).eval args = List.replicate (m + m) true :=
          Cob.eval_uAdd (by simp [args]) (by simp [args])
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, h2m, Cob.eval_dropU]
        simp [args, List.drop_replicate, two_mul]
      have hacc : (Cob.proj 1).eval args = acc := by simp [args]
      rw [Cob.eval_iteW (Cob.eval_isPrimeT hcand) hcand hacc]
      have hbd : (Cob.uAdd (.proj 1) (.proj 1)).eval
          ((true :: List.replicate j true) :: [List.replicate m true]) =
            List.replicate (m + m) true := Cob.eval_uAdd (by simp) (by simp)
      rw [hbd]
      by_cases hpr : Nat.Prime (2 * m - j)
      · simp only [hpr, decide_true, if_true]
        rw [List.take_of_length_le (by simp; omega)]
        right
        exact ⟨_, rfl, hpr, by omega, by omega⟩
      · simp only [hpr, decide_false, Bool.false_eq_true, if_false]
        rcases ih with ⟨hacc, hnone⟩ | ⟨q, hacc, hq, h1, h2⟩
        · left
          rw [hacc]
          refine ⟨by simp, ?_⟩
          rintro ⟨q, hq, h1, h2⟩
          by_cases hqe : q = 2 * m - j
          · exact hpr (hqe ▸ hq)
          · exact hnone ⟨q, hq, by omega, h2⟩
        · right
          rw [hacc, List.take_of_length_le (by simp; omega)]
          exact ⟨q, rfl, hq, by omega, h2⟩

/-- A prime in `(m, 2m]`, from `1^m`. -/
def Cob.findPrimeT (mT : Cob) : Cob := .comp Cob.primeSearch [mT, mT]

/-- **A prime `p` with `m < p ≤ 2m` is computed by a Cobham term from `1^m`**, for `m ≥ 1`. -/
theorem Cob.eval_findPrimeT {mT : Cob} {args : List Word} {m : ℕ} (hm : m ≠ 0)
    (h : mT.eval args = List.replicate m true) :
    ∃ q, (Cob.findPrimeT mT).eval args = List.replicate q true ∧ Nat.Prime q ∧ m < q ∧
      q ≤ 2 * m := by
  have hinv := Cob.primeSearch_inv m m le_rfl
  simp only [Cob.findPrimeT, Cob.eval_comp, List.map_cons, List.map_nil, h]
  rcases hinv with ⟨_, hnone⟩ | ⟨q, hq, hpr, h1, h2⟩
  · obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul m hm
    exact absurd ⟨q, hq, by omega, h2⟩ hnone
  · exact ⟨q, hq, hpr, by omega, h2⟩

end Complexity
