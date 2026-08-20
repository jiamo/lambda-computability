/-
# Time-bounded machine computability

`Start/TM2Capstone.lean` characterises the partial functions computed by a bundled Turing machine
with no bound on the running time.  This module refines the notion by counting steps.

* `TM2Partrec.HaltsWithin` — the machine, started on the given input codes, has produced its
  output after at most `m` steps.
* `TM2Partrec.haltsWithin_of_outputsInTime` — `Mathlib`'s timed statement `Turing.TM2OutputsInTime`
  implies it, so the notion is the code-level form of the usual one.
* `TM2Partrec.TM2TimeRealization` — a realization of a partial function on the naturals together
  with a bound on the number of steps, and `TM2ComputableNatInTime` /
  `TM2ComputableNatInPolyTime` built from it.
* `TM2Partrec.computable_of_tm2ComputableNatInTime` — a time-bounded machine computes a *total*
  function, and that function is computable; with `lambdaComputable_of_tm2ComputableNatInPolyTime`
  the polynomial-time class lands inside the lambda-definable functions.
* `TM2Partrec.haltTM` and `TM2Partrec.tm2ComputableNatInPolyTime_id` — a one-instruction machine
  and the identity, so none of this is vacuous.
* `TM2Partrec.partrec_of_tm2ComputableInPolyTime` — the corresponding bridge for `Mathlib`'s own
  `Turing.TM2ComputableInPolyTime`.
-/

import Start.Encodings

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TM2Partrec

open Turing

/-! ## Halting within a step bound -/

section Bound

variable (tm : Turing.FinTM2) [∀ k, Fintype (tm.Γ k)]

/-- The machine, started on the input codes `l`, has produced an output after at most `m`
steps. -/
def HaltsWithin (l : List ℕ) (m : ℕ) : Prop :=
  ∃ t ≤ m, ((nrun tm (initN tm l) t).bind (outN tm)).isSome

/-- A timed output statement in the sense of `Mathlib` gives a step bound at the level of
codes. -/
theorem haltsWithin_of_outputsInTime {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)} {m : ℕ}
    (h : Turing.TM2OutputsInTime tm l (some l') m) :
    HaltsWithin tm (l.map (encG tm)) m := by
  obtain ⟨⟨n, hn⟩, hle⟩ := h
  refine ⟨n, hle, ?_⟩
  simp only [Option.map_some] at hn
  have hrun : nrun tm (initN tm (l.map (encG tm))) n =
      some (toN tm (Turing.haltList tm l')) := by
    rw [initN_eq, nrun_toN, hn, Option.map_some]
  rw [hrun, Option.bind_some, outN_toN_haltList]
  exact rfl

/-- A machine that halts within a bound converges on that input. -/
theorem dom_evalCode_of_haltsWithin {l : List ℕ} {m : ℕ} (h : HaltsWithin tm l m) :
    (evalCode tm l).Dom := by
  obtain ⟨t, -, ht⟩ := h
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ht
  exact Nat.rfindOpt_dom.2 ⟨t, w, hw⟩

end Bound

/-! ## Time-bounded realizations of partial functions on the naturals -/

/-- A realization of a partial function on the naturals by a bundled Turing machine which,
in addition, halts within `time n` steps on the input `n`. -/
structure TM2TimeRealization (f : ℕ →. ℕ) (time : ℕ → ℕ) extends TM2Realization f where
  /-- the machine halts within the bound on every input -/
  halts : ∀ n, @HaltsWithin tm ΓFin (inp n) (time n)

/-- A partial function on the naturals is computable in time `time` when some bundled machine
computes it and halts within `time n` steps on the input `n`. -/
def TM2ComputableNatInTime (f : ℕ →. ℕ) (time : ℕ → ℕ) : Prop :=
  Nonempty (TM2TimeRealization f time)

/-- Polynomial-time machine computability. -/
def TM2ComputableNatInPolyTime (f : ℕ →. ℕ) : Prop :=
  ∃ p : Polynomial ℕ, TM2ComputableNatInTime f fun n => p.eval n

/-- Forgetting the bound. -/
theorem tm2ComputableNat_of_inTime {f : ℕ →. ℕ} {time : ℕ → ℕ}
    (h : TM2ComputableNatInTime f time) : TM2ComputableNat f :=
  ⟨h.some.toTM2Realization⟩

/-- **A time-bounded machine computes a total function.** -/
theorem dom_of_tm2ComputableNatInTime {f : ℕ →. ℕ} {time : ℕ → ℕ}
    (h : TM2ComputableNatInTime f time) (n : ℕ) : (f n).Dom := by
  obtain ⟨r⟩ := h
  have hdom : (@evalCode r.tm r.ΓFin (r.inp n)).Dom :=
    @dom_evalCode_of_haltsWithin r.tm r.ΓFin _ _ (r.halts n)
  obtain ⟨w, hw⟩ := Part.dom_iff_mem.1 hdom
  rw [r.eval_eq n]
  exact Part.dom_iff_mem.2 ⟨r.out w, Part.mem_map _ hw⟩

/-- **A time-bounded machine computes a computable total function.** -/
theorem computable_of_tm2ComputableNatInTime {f : ℕ →. ℕ} {time : ℕ → ℕ}
    (h : TM2ComputableNatInTime f time) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ n, f n = Part.some (g n) := by
  have hpart : Partrec f := partrec_of_tm2ComputableNat (tm2ComputableNat_of_inTime h)
  have hdom := dom_of_tm2ComputableNatInTime h
  refine ⟨fun n => (f n).get (hdom n), Partrec.of_eq_tot hpart fun n => Part.get_mem _,
    fun n => ?_⟩
  exact (Part.get_eq_iff_eq_some.1 rfl)

/-- A polynomial-time machine computes a computable total function. -/
theorem computable_of_tm2ComputableNatInPolyTime {f : ℕ →. ℕ}
    (h : TM2ComputableNatInPolyTime f) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ n, f n = Part.some (g n) := by
  obtain ⟨p, hp⟩ := h
  exact computable_of_tm2ComputableNatInTime hp

/-- **Polynomial-time machine computable functions are lambda-definable.** -/
theorem lambdaComputable_of_tm2ComputableNatInPolyTime {f : ℕ →. ℕ}
    (h : TM2ComputableNatInPolyTime f) : LambdaComputable f :=
  lambdaComputable_iff_partrec.2
    (partrec_of_tm2ComputableNat (tm2ComputableNat_of_inTime h.choose_spec))

/-! ## Non-vacuity: a machine that halts at once -/

/-- A machine with one stack, one label and one instruction: halt.  Started on a stack it halts
after a single step leaving that stack untouched. -/
def haltTM : Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := Turing.TM2.Stmt.halt

instance haltTM_ΓFin : ∀ k, Fintype (haltTM.Γ k) := fun _ => inferInstanceAs (Fintype Bool)

/-- On any input the halting machine outputs its input stack after one step. -/
def haltTM_outputsInTime (l : List (haltTM.Γ haltTM.k₀)) :
    Turing.TM2OutputsInTime haltTM l (some l) 1 :=
  ⟨⟨1, rfl⟩, le_refl 1⟩

noncomputable section NonVacuity

/-- The code of the single symbol used by the non-vacuity witness. -/
def haltCode : ℕ := @encG haltTM haltTM_ΓFin haltTM.k₀ false

/-- The input translation of the non-vacuity witness: `n` becomes a stack of `n` copies of the
first symbol. -/
def haltInp (n : ℕ) : List ℕ := (List.range n).map fun _ => haltCode

theorem range_map_const (n c : ℕ) : (List.range n).map (fun _ => c) = List.replicate n c := by
  simp

theorem haltInp_eq (n : ℕ) :
    haltInp n = List.map (@encG haltTM haltTM_ΓFin haltTM.k₀)
      (List.replicate n (false : haltTM.Γ haltTM.k₀)) := by
  rw [haltInp, range_map_const, haltCode, List.map_replicate]

theorem computable_haltInp : Computable haltInp := by
  have h : Primrec fun n : ℕ => (List.range n).map fun _ => haltCode :=
    Primrec.list_map Primrec.list_range (Primrec.const haltCode).to₂
  exact h.to_comp

theorem haltInp_length (n : ℕ) : (haltInp n).length = n := by simp [haltInp]

theorem evalCode_haltInp (n : ℕ) : evalCode haltTM (haltInp n) = Part.some (haltInp n) := by
  rw [haltInp_eq]
  exact evalCode_of_outputs haltTM
    (haltTM_outputsInTime (List.replicate n (false : haltTM.Γ haltTM.k₀))).toEvalsTo

/-- **The time-bounded notion is not vacuous**: the identity is computed in one step. -/
def idTimeRealization : TM2TimeRealization (fun n => Part.some n) (fun _ => 1) where
  tm := haltTM
  ΓFin := haltTM_ΓFin
  inp := haltInp
  out := List.length
  inp_computable := computable_haltInp
  out_computable := Primrec.list_length.to_comp
  eval_eq n := by
    rw [evalCode_haltInp n, Part.map_some, haltInp_length]
  halts n := by
    have h := haltsWithin_of_outputsInTime haltTM
      (haltTM_outputsInTime (List.replicate n (false : haltTM.Γ haltTM.k₀)))
    rwa [← haltInp_eq n] at h

theorem tm2ComputableNatInTime_id : TM2ComputableNatInTime (fun n => Part.some n) (fun _ => 1) :=
  ⟨idTimeRealization⟩

theorem tm2ComputableNatInPolyTime_id : TM2ComputableNatInPolyTime (fun n => Part.some n) :=
  ⟨1, by simpa using tm2ComputableNatInTime_id⟩

end NonVacuity

/-! ## `Mathlib`'s polynomial-time class -/

/-- **Polynomial-time computability in the sense of `Mathlib` implies partial recursiveness**, in
the same form as `TM2Partrec.partrec_of_tm2Computable`: the code-level function of the machine is
partial recursive and returns the codes of the encoded output. -/
theorem partrec_of_tm2ComputableInPolyTime {α β : Type} {ea : Computability.FinEncoding α}
    {eb : Computability.FinEncoding β} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) [inst : ∀ k, Fintype (h.tm.Γ k)] :
    Partrec (evalCode h.tm) ∧ ∀ a : α,
      evalCode h.tm ((List.map h.inputAlphabet.invFun (ea.encode a)).map (encG h.tm)) =
        Part.some ((List.map h.outputAlphabet.invFun (eb.encode (f a))).map (encG h.tm)) :=
  @partrec_of_tm2Computable α β ea eb f h.toTM2ComputableInTime.toTM2Computable inst

/-- The step bound of `Mathlib`'s polynomial-time class, read at the level of codes. -/
theorem haltsWithin_of_tm2ComputableInPolyTime {α β : Type} {ea : Computability.FinEncoding α}
    {eb : Computability.FinEncoding β} {f : α → β}
    (h : Turing.TM2ComputableInPolyTime ea eb f) [∀ k, Fintype (h.tm.Γ k)] (a : α) :
    HaltsWithin h.tm ((List.map h.inputAlphabet.invFun (ea.encode a)).map (encG h.tm))
      (h.time.eval (ea.encode a).length) :=
  haltsWithin_of_outputsInTime h.tm (h.outputsFun a)

end TM2Partrec
