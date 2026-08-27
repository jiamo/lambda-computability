/-
**Renumbering the variables of an encoded CNF is a Cobham function.**

Assembling a formula out of pieces — which is what a Cook–Levin style reduction does — needs the
variables of a piece to be moved out of the way of the variables of the other pieces.  On codes,
that is the operation `u ↦ code of the CNF of u with every variable shifted by k`, and this module
proves it is polynomial-time: it is computed by the single Cobham term `Complexity.Sat.shiftTerm`,
applied to the code and to `k` in unary.

The term is an instance of the transducer toolkit of `Start/CobhamTransducer.lean`.  The code of
`Start/Sat.lean` is read from the *right* by a three-phase automaton (ticks, one escape bit, two
escape bits), which is exactly the scanning direction of `Complexity.rrun`; the transducer copies
its input bit for bit and emits `k` extra ticks after every escape bit read in the tick phase.
Those extra ticks land immediately to the right of the command bits of a literal, so they increase
its variable by `k`; the ones emitted at a clause separator are discarded by the decoder, which
resets its tick counter when a clause closes.

Main definitions:

* `Complexity.Sat.shiftLit`, `Complexity.Sat.shiftCnf` — renumbering the variables;
* `Complexity.Sat.shiftTerm` — the Cobham term.

Main results:

* `Complexity.Sat.decode_eval_shiftTerm` — **the term renumbers the variables of the encoded CNF**;
* `Complexity.Sat.satisfiable_shiftCnf` — renumbering preserves satisfiability;
* `Complexity.Sat.SAT_eval_shiftTerm` — the shifted code is in SAT exactly when the original CNF is
  satisfiable.
-/

import Start.CobhamTransducer

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Sat

/-! ### Renumbering the variables -/

/-- The literal `l` with its variable moved up by `k`. -/
def shiftLit (k : ℕ) (l : Lit) : Lit := (l.1, l.2 + k)

/-- The CNF `F` with every variable moved up by `k`. -/
def shiftCnf (k : ℕ) (F : Cnf) : Cnf := F.map (List.map (shiftLit k))

/-! ### The transducer -/

/-- The transition function of the shifting transducer: the three phases of the decoder of
`Start/Sat.lean`, read from the right.  State `0` is the tick phase, `1` is "one escape bit read",
`2` is "two escape bits read". -/
def shiftDelta : ℕ → Bool → ℕ
  | 0, false => 1
  | 1, false => 2
  | _, _ => 0

theorem shiftDelta_lt (s : ℕ) (b : Bool) : shiftDelta s b < 3 := by
  rcases s with _ | _ | n <;> cases b <;> simp [shiftDelta]

/-- The output blocks of the shifting transducer, as Cobham terms in the parameter `1^k`: the bit
is copied, and an escape bit read in the tick phase is followed by `k` extra ticks. -/
def shiftOutT (s : ℕ) (b : Bool) : Cob :=
  if s = 0 ∧ b = false then Cob.pre [false] (.proj 0) else Cob.pre [b] .empty

/-- The output blocks of the shifting transducer. -/
def shiftOut (k : ℕ) (s : ℕ) (b : Bool) : Word :=
  if s = 0 ∧ b = false then false :: List.replicate k true else [b]

theorem eval_shiftOutT (s : ℕ) (b : Bool) (k : ℕ) :
    (shiftOutT s b).eval [List.replicate k true] = shiftOut k s b := by
  by_cases h : s = 0 ∧ b = false
  · simp [shiftOutT, shiftOut, h]
  · simp [shiftOutT, shiftOut, h]

theorem length_shiftOut (k s : ℕ) (b : Bool) : (shiftOut k s b).length ≤ 1 + k := by
  by_cases h : s = 0 ∧ b = false <;> simp [shiftOut, h]

/-! ### What the transducer does on a code -/

theorem shift_st_replicate (v : ℕ) : rst shiftDelta 0 (List.replicate v true) = 0 := by
  induction v with
  | zero => rfl
  | succ v ih => rw [List.replicate_succ, rst, ih]; rfl

theorem shift_run_replicate (k v : ℕ) :
    rrun shiftDelta (shiftOut k) 0 (List.replicate v true) = List.replicate v true := by
  induction v with
  | zero => rfl
  | succ v ih =>
      rw [List.replicate_succ, rrun, ih, shift_st_replicate]
      simp [shiftOut]

theorem shift_run_sep (k : ℕ) : rrun shiftDelta (shiftOut k) 0 [false, false, false]
    = [false, false, false] ++ List.replicate k true := by
  simp [rrun, rst, shiftDelta, shiftOut]

theorem shift_run_negMarker (k : ℕ) : rrun shiftDelta (shiftOut k) 0 [true, false]
    = [true, false] ++ List.replicate k true := by
  simp [rrun, rst, shiftDelta, shiftOut]

theorem shift_run_posMarker (k : ℕ) : rrun shiftDelta (shiftOut k) 0 [true, false, false]
    = [true, false, false] ++ List.replicate k true := by
  simp [rrun, rst, shiftDelta, shiftOut]

theorem encLit_neg (v : ℕ) : encLit (false, v) = [true, false] ++ List.replicate v true := by
  simp [encLit]

theorem encLit_pos (v : ℕ) : encLit (true, v) = [true, false, false] ++ List.replicate v true := by
  simp [encLit]

theorem shift_st_encLit (l : Lit) : rst shiftDelta 0 (encLit l) = 0 := by
  obtain ⟨s, v⟩ := l
  cases s
  · rw [encLit_neg, rst_append, shift_st_replicate]; rfl
  · rw [encLit_pos, rst_append, shift_st_replicate]; rfl

theorem shift_run_encLit (k : ℕ) (l : Lit) :
    rrun shiftDelta (shiftOut k) 0 (encLit l) = encLit (shiftLit k l) := by
  obtain ⟨s, v⟩ := l
  have hrep : List.replicate k true ++ List.replicate v true = List.replicate (v + k) true := by
    rw [← List.replicate_add]
    congr 1
    omega
  cases s
  · rw [encLit_neg, rrun_append, shift_st_replicate, shift_run_replicate, shift_run_negMarker,
      List.append_assoc, hrep, shiftLit, encLit_neg]
  · rw [encLit_pos, rrun_append, shift_st_replicate, shift_run_replicate, shift_run_posMarker,
      List.append_assoc, hrep, shiftLit, encLit_pos]

theorem shift_st_lits (C : Clause) : rst shiftDelta 0 (C.flatMap encLit) = 0 := by
  induction C with
  | nil => rfl
  | cons l C ih => rw [List.flatMap_cons, rst_append, ih, shift_st_encLit]

theorem shift_run_lits (k : ℕ) (C : Clause) :
    rrun shiftDelta (shiftOut k) 0 (C.flatMap encLit)
      = (C.map (shiftLit k)).flatMap encLit := by
  induction C with
  | nil => rfl
  | cons l C ih =>
      rw [List.flatMap_cons, rrun_append, shift_st_lits, ih, shift_run_encLit, List.map_cons,
        List.flatMap_cons]

/-- The code of a clause with the variables shifted, and the `k` extra ticks that the transducer
emits at the separator. -/
def encClauseSh (k : ℕ) (C : Clause) : Word :=
  ([false, false, false] ++ List.replicate k true) ++ (C.map (shiftLit k)).flatMap encLit

/-- The code of a CNF with the variables shifted, as the transducer writes it. -/
def encCnfSh (k : ℕ) (F : Cnf) : Word := F.flatMap (encClauseSh k)

theorem shift_st_encClause (C : Clause) : rst shiftDelta 0 (encClause C) = 0 := by
  rw [encClause, rst_append, shift_st_lits]
  rfl

theorem shift_run_encClause (k : ℕ) (C : Clause) :
    rrun shiftDelta (shiftOut k) 0 (encClause C) = encClauseSh k C := by
  rw [encClause, rrun_append, shift_st_lits, shift_run_lits, encClauseSh, shift_run_sep]

theorem shift_st_encCnf (F : Cnf) : rst shiftDelta 0 (encCnf F) = 0 := by
  induction F with
  | nil => rfl
  | cons C F ih => rw [encCnf, List.flatMap_cons, ← encCnf, rst_append, ih, shift_st_encClause]

theorem shift_run_encCnf (k : ℕ) (F : Cnf) :
    rrun shiftDelta (shiftOut k) 0 (encCnf F) = encCnfSh k F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      rw [encCnf, List.flatMap_cons, ← encCnf, rrun_append, shift_st_encCnf, ih,
        shift_run_encClause]
      rfl

/-! ### The extra ticks are ignored by the decoder -/

theorem drunFrom_encClauseSh (d : DSt) (hp : d.phase = .main) (ht : d.ticks = 0) (hc : d.cur = [])
    (k : ℕ) (C : Clause) :
    drunFrom d (encClauseSh k C) = ⟨C.map (shiftLit k) :: d.done, [], 0, .main⟩ := by
  rw [encClauseSh, drunFrom_append, drunFrom_lits d hp ht _, drunFrom_append,
    drunFrom_replicate _ rfl k]
  simp only [hc, List.append_nil]
  cases d
  simp_all [drunFrom, dstep]

theorem drun_encCnfSh (k : ℕ) (F : Cnf) :
    drun (encCnfSh k F) = ⟨shiftCnf k F, [], 0, .main⟩ := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      rw [encCnfSh, List.flatMap_cons, ← encCnfSh, drun, drunFrom_append, ← drun, ih,
        drunFrom_encClauseSh _ rfl rfl rfl]
      rfl

theorem decode_encCnfSh (k : ℕ) (F : Cnf) : decode (encCnfSh k F) = shiftCnf k F := by
  rw [decode, drun_encCnfSh]

/-! ### The Cobham term -/

/-- **The Cobham term renumbering the variables of an encoded CNF**: applied to the code of `F`
and to `1^k`, its value decodes to `F` with every variable moved up by `k`. -/
def shiftTerm : Cob := fstRunTerm 3 shiftDelta shiftOutT 1

theorem eval_shiftTerm (k : ℕ) (u : Word) :
    shiftTerm.eval [u, List.replicate k true] = rrun shiftDelta (shiftOut k) 0 u := by
  have hK : ∀ s b, ((shiftOutT s b).eval [List.replicate k true]).length
      ≤ 1 + (List.replicate k true : Word).length := by
    intro s b
    rw [eval_shiftOutT]
    simpa using length_shiftOut k s b
  have h := eval_fstRunTerm (m := 3) (K := 1) (by norm_num)
    (fun s b => shiftDelta_lt s b) shiftOutT (List.replicate k true) hK u
  rw [shiftTerm, h]
  simp only [eval_shiftOutT]

/-- **Renumbering the variables of an encoded CNF is a polynomial-time operation.** -/
theorem decode_eval_shiftTerm (k : ℕ) (F : Cnf) :
    decode (shiftTerm.eval [encCnf F, List.replicate k true]) = shiftCnf k F := by
  rw [eval_shiftTerm, shift_run_encCnf, decode_encCnfSh]

/-! ### Renumbering preserves satisfiability -/

theorem litVal_shiftLit (k : ℕ) (σ : Word) (l : Lit) :
    litVal σ (shiftLit k l) = litVal (σ.drop k) l := by
  obtain ⟨s, i⟩ := l
  have hget : (σ.drop k).getD i false = σ.getD (i + k) false := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop,
      Nat.add_comm]
  cases s
  · simp only [litVal, shiftLit, hget]
    rfl
  · simp only [litVal, shiftLit, hget]

theorem clauseVal_map_shiftLit (k : ℕ) (σ : Word) (C : Clause) :
    clauseVal σ (C.map (shiftLit k)) = clauseVal (σ.drop k) C := by
  induction C with
  | nil => rfl
  | cons l C ih => rw [List.map_cons, clauseVal_cons, clauseVal_cons, ih, litVal_shiftLit]

/-- Shifting the variables by `k` is undone on assignments by dropping the first `k` bits. -/
theorem cnfVal_shiftCnf (k : ℕ) (σ : Word) (F : Cnf) :
    cnfVal σ (shiftCnf k F) = cnfVal (σ.drop k) F := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      rw [shiftCnf, List.map_cons, cnfVal_cons, ← shiftCnf, ih, cnfVal_cons,
        clauseVal_map_shiftLit]

/-- **Renumbering the variables preserves satisfiability.** -/
theorem satisfiable_shiftCnf (k : ℕ) (F : Cnf) :
    (∃ σ : Word, cnfVal σ (shiftCnf k F) = true) ↔ ∃ σ : Word, cnfVal σ F = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.drop k, by rwa [cnfVal_shiftCnf] at hσ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨List.replicate k false ++ σ, ?_⟩
    rw [cnfVal_shiftCnf]
    simpa using hσ

/-- The shifted code is in SAT exactly when the original CNF is satisfiable. -/
theorem SAT_eval_shiftTerm (k : ℕ) (F : Cnf) :
    SAT (shiftTerm.eval [encCnf F, List.replicate k true]) ↔ ∃ σ : Word, cnfVal σ F = true := by
  rw [SAT, decode_eval_shiftTerm]
  exact satisfiable_shiftCnf k F

end Sat

end Complexity
