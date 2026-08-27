/-
# A little language for the wires of a gadget

`Start/UniformSigSel.lean` reduces a combinational gadget to three *flat* gates per output wire,
each written by a Cobham term.  Writing those terms by hand — the arithmetic of the wire index in
unary, the case distinctions on where the wire sits inside a signal — is the same work every time.

This module does it once.  A wire is described by a term of a tiny language: an index is built
from the column `j`, the half-width `m n`, the width `2 * m n`, literals, addition, truncated
subtraction and remainder; a gate is a constant, a circuit input at such an index, or a case
distinction on a comparison of two indices.  Every such description is interpreted both as a gate
(`Complexity.Tseitin.GateE.gate`) and as a Cobham term writing that gate's token
(`Complexity.Tseitin.GateE.term`), and the two agree.

Main definitions:

* `Complexity.Tseitin.IdxE`, `Complexity.Tseitin.CondE`, `Complexity.Tseitin.GateE` — the language;
* `Complexity.Tseitin.GateE.gate`, `Complexity.Tseitin.GateE.term` — its two interpretations;
* `Complexity.Tseitin.GateE.bnd` — the largest input index a description can read.

Main results:

* `Complexity.Tseitin.GateE.eval_term` — the term writes the token of the gate;
* `Complexity.sigUniform_of_selLayerE` — **a selector layer whose three gates are given by
  descriptions realizes the function its wires describe**: `Complexity.sigUniform_of_selLayer`
  with the Cobham terms supplied.
-/

import Start.UniformSigSel

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Indices -/

/-- An index into the input word of a gadget, as a function of the column `j`, the half-width
`mm` and the width `M`. -/
inductive IdxE : Type
  /-- The column. -/
  | col
  /-- The half-width. -/
  | half
  /-- The width. -/
  | width
  /-- A literal. -/
  | lit (k : ℕ)
  /-- Addition. -/
  | add (a b : IdxE)
  /-- Truncated subtraction. -/
  | sub (a b : IdxE)
  /-- Remainder, with the convention `a % 0 = a`. -/
  | mod (a b : IdxE)
  deriving Inhabited

/-- The value of an index description. -/
def IdxE.val (j mm M : ℕ) : IdxE → ℕ
  | .col => j
  | .half => mm
  | .width => M
  | .lit k => k
  | .add a b => a.val j mm M + b.val j mm M
  | .sub a b => a.val j mm M - b.val j mm M
  | .mod a b => a.val j mm M % b.val j mm M

/-- The Cobham term computing an index in unary, from the arguments `[y, 1^j, pw]` and terms
`mmT`, `MT` for the half-width and the width. -/
def IdxE.term (mmT MT : Cob) : IdxE → Cob
  | .col => .proj 1
  | .half => mmT
  | .width => MT
  | .lit k => Cob.constT (List.replicate k true)
  | .add a b => Cob.catL [a.term mmT MT, b.term mmT MT]
  | .sub a b => .comp Cob.dropU [b.term mmT MT, a.term mmT MT]
  | .mod a b =>
      Cob.iteT (b.term mmT MT) (Cob.modT (a.term mmT MT) (b.term mmT MT)) (a.term mmT MT)

theorem IdxE.eval_term {mmT MT : Cob} {args : List Word} {j mm M : ℕ}
    (hj : args.getD 1 [] = List.replicate j true)
    (hmm : mmT.eval args = List.replicate mm true)
    (hM : MT.eval args = List.replicate M true) :
    ∀ e : IdxE, (e.term mmT MT).eval args = List.replicate (e.val j mm M) true := by
  intro e
  induction e with
  | col => simpa [IdxE.term, IdxE.val] using hj
  | half => simpa [IdxE.term, IdxE.val] using hmm
  | width => simpa [IdxE.term, IdxE.val] using hM
  | lit k => simp [IdxE.term, IdxE.val]
  | add a b iha ihb =>
      simp only [IdxE.term, IdxE.val, Cob.eval_catL, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, iha, ihb, ← List.replicate_add]
  | sub a b iha ihb =>
      simp only [IdxE.term, IdxE.val, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU,
        iha, ihb, List.length_replicate, List.drop_replicate]
  | mod a b iha ihb =>
      rcases Nat.eq_zero_or_pos (b.val j mm M) with hb | hb
      · simp only [IdxE.term, IdxE.val, eval_iteT_eval, ihb, hb, List.replicate_zero,
          iha, Nat.mod_zero, if_pos]
      · have hne : List.replicate (b.val j mm M) true ≠ [] := by
          simp only [ne_eq, List.replicate_eq_nil_iff]
          omega
        rw [IdxE.term, eval_iteT_eval, ihb, if_neg hne, Cob.eval_modT hb iha ihb, IdxE.val]

/-! ### Conditions -/

/-- A comparison of two indices. -/
inductive CondE : Type
  /-- Strict inequality. -/
  | lt (a b : IdxE)
  /-- Difference. -/
  | ne (a b : IdxE)
  deriving Inhabited

/-- Whether a comparison holds. -/
def CondE.holds (j mm M : ℕ) : CondE → Prop
  | .lt a b => a.val j mm M < b.val j mm M
  | .ne a b => a.val j mm M ≠ b.val j mm M

instance (j mm M : ℕ) (c : CondE) : Decidable (c.holds j mm M) := by
  cases c <;> · rw [CondE.holds]; infer_instance

/-- The Cobham term testing a comparison: its value is empty exactly when the comparison
fails. -/
def CondE.term (mmT MT : Cob) : CondE → Cob
  | .lt a b => .comp Cob.dropU [a.term mmT MT, b.term mmT MT]
  | .ne a b =>
      Cob.catL [.comp Cob.dropU [a.term mmT MT, b.term mmT MT],
        .comp Cob.dropU [b.term mmT MT, a.term mmT MT]]

theorem CondE.eval_term_eq_nil_iff {mmT MT : Cob} {args : List Word} {j mm M : ℕ}
    (hj : args.getD 1 [] = List.replicate j true)
    (hmm : mmT.eval args = List.replicate mm true)
    (hM : MT.eval args = List.replicate M true) (c : CondE) :
    (c.term mmT MT).eval args = [] ↔ ¬ c.holds j mm M := by
  cases c with
  | lt a b =>
      simp only [CondE.term, CondE.holds, Cob.eval_comp, List.map_cons, List.map_nil,
        Cob.eval_dropU, IdxE.eval_term hj hmm hM, List.length_replicate, List.drop_replicate,
        List.replicate_eq_nil_iff]
      omega
  | ne a b =>
      simp only [CondE.term, CondE.holds, Cob.eval_catL, List.map_cons, List.map_nil,
        List.flatten_cons, List.flatten_nil, List.append_nil, Cob.eval_comp, Cob.eval_dropU,
        IdxE.eval_term hj hmm hM, List.length_replicate, List.drop_replicate,
        List.append_eq_nil_iff, List.replicate_eq_nil_iff, not_not]
      omega

/-! ### Gates -/

/-- The description of a flat gate: a constant, a circuit input at a computed index, or a case
distinction. -/
inductive GateE : Type
  /-- A constant. -/
  | cstE (b : Bool)
  /-- A circuit input. -/
  | inpE (e : IdxE)
  /-- A case distinction. -/
  | iteE (c : CondE) (t f : GateE)
  deriving Inhabited

/-- The gate a description denotes. -/
def GateE.gate (j mm M : ℕ) : GateE → Gate
  | .cstE b => .cst b
  | .inpE e => .inp (e.val j mm M)
  | .iteE c t f => if c.holds j mm M then t.gate j mm M else f.gate j mm M

/-- The input index a description reads, or `0` if it reads none. -/
def GateE.bnd (j mm M : ℕ) : GateE → ℕ
  | .cstE _ => 0
  | .inpE e => e.val j mm M
  | .iteE c t f => if c.holds j mm M then t.bnd j mm M else f.bnd j mm M

/-- The Cobham term writing the token of the gate a description denotes. -/
def GateE.term (mmT MT : Cob) : GateE → Cob
  | .cstE b => CircCode.tokTerm (if b then 3 else 2) .empty .empty
  | .inpE e => CircCode.tokTerm 1 (e.term mmT MT) .empty
  | .iteE c t f => Cob.iteT (c.term mmT MT) (t.term mmT MT) (f.term mmT MT)

theorem GateE.flat (j mm M : ℕ) : ∀ e : GateE, flatGate (e.gate j mm M) := by
  intro e
  induction e with
  | cstE b => exact trivial
  | inpE e => exact trivial
  | iteE c t f iht ihf =>
      rw [GateE.gate]
      split_ifs
      · exact iht
      · exact ihf

theorem GateE.inpLt_of_bnd {j mm M w : ℕ} :
    ∀ e : GateE, e.bnd j mm M < w → inpLt w (e.gate j mm M) := by
  intro e
  induction e with
  | cstE b => exact fun _ => trivial
  | inpE e => exact fun h => h
  | iteE c t f iht ihf =>
      intro h
      rw [GateE.bnd] at h
      rw [GateE.gate]
      split_ifs at h ⊢ with hc
      · exact iht h
      · exact ihf h

theorem GateE.length_encGate_le (j mm M : ℕ) :
    ∀ e : GateE, (CircCode.encGate (e.gate j mm M)).length ≤ e.bnd j mm M + 8 := by
  intro e
  induction e with
  | cstE b =>
      rw [CircCode.length_encGate]
      cases b <;> simp [GateE.gate, GateE.bnd, CircCode.tag, CircCode.fld1, CircCode.fld2]
  | inpE e =>
      rw [CircCode.length_encGate]
      simp only [GateE.gate, GateE.bnd, CircCode.tag, CircCode.fld1, CircCode.fld2]
      omega
  | iteE c t f iht ihf =>
      rw [GateE.gate, GateE.bnd]
      split_ifs
      · exact iht
      · exact ihf

theorem GateE.eval_term {mmT MT : Cob} {args : List Word} {j mm M : ℕ}
    (hj : args.getD 1 [] = List.replicate j true)
    (hmm : mmT.eval args = List.replicate mm true)
    (hM : MT.eval args = List.replicate M true) :
    ∀ e : GateE, (e.term mmT MT).eval args = CircCode.encGate (e.gate j mm M) := by
  intro e
  induction e with
  | cstE b =>
      have h := CircCode.eval_tokTerm (g := Gate.cst b) (aT := (.empty : Cob))
        (bT := (.empty : Cob)) (args := args) (by simp [CircCode.fld1]) (by simp [CircCode.fld2])
      rw [show CircCode.tag (Gate.cst b) = (if b then 3 else 2) by cases b <;> rfl] at h
      exact h
  | inpE e =>
      have h := CircCode.eval_tokTerm (g := Gate.inp (e.val j mm M)) (aT := e.term mmT MT)
        (bT := (.empty : Cob)) (args := args) (IdxE.eval_term hj hmm hM e)
        (by simp [CircCode.fld2])
      exact h
  | iteE c t f iht ihf =>
      rw [GateE.term, eval_iteT_eval, GateE.gate]
      by_cases hc : c.holds j mm M
      · rw [if_neg (fun h => ((CondE.eval_term_eq_nil_iff hj hmm hM c).1 h) hc), if_pos hc]
        exact iht
      · rw [if_pos ((CondE.eval_term_eq_nil_iff hj hmm hM c).2 hc), if_neg hc]
        exact ihf

end Tseitin

open Complexity.Tseitin in
/-- **A selector layer whose three gates are given by descriptions realizes the function its wires
describe.**  This is `Complexity.sigUniform_of_selLayer` with the Cobham terms writing the gates
supplied by `Complexity.Tseitin.GateE.term`, so that only the arithmetic of the indices and the
meaning of the wires are left to prove. -/
theorem sigUniform_of_selLayerE {r : ℕ} {m : ℕ → ℕ} {F : List Word → Word}
    {mT : Cob} {ea eb ec : Tseitin.GateE} {K : ℕ}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hAi : ∀ n j, j < 2 * m n → ea.bnd j (m n) (2 * m n) < r * (2 * m n))
    (hBi : ∀ n j, j < 2 * m n → eb.bnd j (m n) (2 * m n) < r * (2 * m n))
    (hCi : ∀ n j, j < 2 * m n → ec.bnd j (m n) (2 * m n) < r * (2 * m n))
    (hAb : ∀ n j, ea.bnd j (m n) (2 * m n) + 8 ≤ K * (j + (n + 2 * m n + 1) + 1))
    (hBb : ∀ n j, eb.bnd j (m n) (2 * m n) + 8 ≤ K * (j + (n + 2 * m n + 1) + 1))
    (hCb : ∀ n j, ec.bnd j (m n) (2 * m n) + 8 ≤ K * (j + (n + 2 * m n + 1) + 1))
    (hval : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
      (List.range (2 * m n)).map (fun j => Tseitin.selBit
          (Tseitin.gateVal (encArgs (m n) args) [] (ea.gate j (m n) (2 * m n)))
          (Tseitin.gateVal (encArgs (m n) args) [] (eb.gate j (m n) (2 * m n)))
          (Tseitin.gateVal (encArgs (m n) args) [] (ec.gate j (m n) (2 * m n))))
        = encSig (m n) (F args)) :
    SigUniform r m F := by
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  set mmT : Cob := .comp mT [.comp Cob.leadOnes [Cob.proj 2]] with hmmT
  set MT : Cob := CircCode.selWid twoT 2 with hMT
  have hmmn : ∀ (n : ℕ) (y : Word) (j : ℕ),
      mmT.eval [y, List.replicate j true, dmW n (2 * m n)] = List.replicate (m n) true := by
    intro n y j
    simp only [hmmT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, lead1_dmW]
    rw [hm (List.replicate n true), List.length_replicate]
  have hMn : ∀ (n : ℕ) (y : Word) (j : ℕ),
      MT.eval [y, List.replicate j true, dmW n (2 * m n)] = List.replicate (2 * m n) true := by
    intro n y j
    refine CircCode.eval_selWid (n := n) (by simp) ?_
    rw [htwo, List.length_replicate]
  have hjn : ∀ (n : ℕ) (y : Word) (j : ℕ),
      ([y, List.replicate j true, dmW n (2 * m n)] : List Word).getD 1 []
        = List.replicate j true := by
    intro n y j
    simp
  have hlen : ∀ n : ℕ, (dmW n (2 * m n)).length = n + 2 * m n + 1 := by
    intro n
    simp
  refine sigUniform_of_selLayer (K := K) (mT := mT)
    (A := fun n j => ea.gate j (m n) (2 * m n)) (B := fun n j => eb.gate j (m n) (2 * m n))
    (C := fun n j => ec.gate j (m n) (2 * m n))
    (aT := ea.term mmT MT) (bT := eb.term mmT MT) (cT := ec.term mmT MT)
    hm (fun n j => Tseitin.GateE.flat _ _ _ _) (fun n j => Tseitin.GateE.flat _ _ _ _)
    (fun n j => Tseitin.GateE.flat _ _ _ _)
    (fun n j hj => Tseitin.GateE.inpLt_of_bnd _ (hAi n j hj))
    (fun n j hj => Tseitin.GateE.inpLt_of_bnd _ (hBi n j hj))
    (fun n j hj => Tseitin.GateE.inpLt_of_bnd _ (hCi n j hj))
    (fun n y j => Tseitin.GateE.eval_term (hjn n y j) (hmmn n y j) (hMn n y j) ea)
    (fun n y j => Tseitin.GateE.eval_term (hjn n y j) (hmmn n y j) (hMn n y j) eb)
    (fun n y j => Tseitin.GateE.eval_term (hjn n y j) (hmmn n y j) (hMn n y j) ec)
    ?_ ?_ ?_ hval
  · intro n j
    rw [hlen n]
    exact (Tseitin.GateE.length_encGate_le _ _ _ ea).trans (hAb n j)
  · intro n j
    rw [hlen n]
    exact (Tseitin.GateE.length_encGate_le _ _ _ eb).trans (hBb n j)
  · intro n j
    rw [hlen n]
    exact (Tseitin.GateE.length_encGate_le _ _ _ ec).trans (hCb n j)

end Complexity
