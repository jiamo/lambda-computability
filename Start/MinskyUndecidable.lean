/-
**Undecidability of two-counter halting for a fixed machine** — task `M25-KCM-UNIVERSAL`
(round 10, part B4).

* `Minsky.Universal.uCode` — a universal code (`exists_universal_code`);
* `Minsky.Universal.uProg` — its compilation to a structured counter program, input in
  register `0`, output in register `1`, scratch registers from `2`;
* `Minsky.Universal.M_u` — **the fixed two-counter machine**: the code of `uProg` (whose exit is
  the halting label), compiled to two counters by Minsky's construction;
* `Minsky.Universal.M_u_halts_iff` — `M_u` halts from `(3 ^ m, 0)` exactly when `uCode` halts on
  `m`;
* `Minsky.Universal.cm_halts_undecidable` —
  `¬ ComputablePred (fun ab : ℕ × ℕ => CM.Halts M_u ab.1 ab.2)`.
-/

import Start.MinskyCompile
import Start.MinskyUniversal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Universal

open Function Nat.Partrec FsubGhelli

/-- A universal code. -/
noncomputable def uCode : Code := Classical.choose exists_universal_code

theorem uCode_spec (c : Code) (x : ℕ) :
    uCode.eval (Nat.pair (Encodable.encode c) x) = c.eval x :=
  Classical.choose_spec exists_universal_code c x

/-- The universal code compiled to a structured counter program: input register `0`, output
register `1`, scratch registers from `2`. -/
noncomputable def uProg : Prog := Prog.compile uCode 0 1 2

/-- The counter machine of `uProg`. -/
noncomputable def KM_u : KM := uProg.code 0 uProg.len

/-- A bound on the registers of `uProg`. -/
noncomputable def k_u : ℕ := uProg.regs.foldr max 0 + 1

theorem regsBelow_KM_u : RegsBelow KM_u k_u := by
  intro ins hins
  refine Prog.regsBelow_code uProg 0 uProg.len k_u (fun i hi => ?_) ins hins
  have : ∀ (l : List ℕ), i ∈ l → i ≤ l.foldr max 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons x l ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.1 hl with rfl | hl
      · exact le_max_left _ _
      · exact le_trans (ih hl) (le_max_right _ _)
  have := this _ hi
  unfold k_u
  omega

/-- **The fixed two-counter machine.** -/
noncomputable def M_u : CM := Minsky.compile KM_u

/-- The initial registers: `m` in the input register, everything else zero. -/
def initRegs (m : ℕ) : ℕ → ℕ := update (fun _ => 0) 0 m

theorem godel_initRegs {k : ℕ} (hk : 0 < k) (m : ℕ) : godel k (initRegs m) = 3 ^ m := by
  unfold godel
  rw [Finset.prod_eq_single 0]
  · simp [initRegs, base, Nat.fermatNumber]
  · intro i _ hi
    simp [initRegs, hi]
  · intro h
    exact absurd (Finset.mem_range.2 hk) h

theorem uProg_exec_iff (m : ℕ) : (∃ r', Prog.Exec uProg (initRegs m) r') ↔ (uCode.eval m).Dom := by
  have hg := Prog.good_compile uCode (inp := 0) (out := 1) (b := 2) (by omega) (by omega)
    (by omega) (initRegs m) (by simp [initRegs]) (by
      intro j hj; simp only [initRegs, update_apply]; split_ifs <;> omega)
  simp only [initRegs, update_self] at hg
  constructor
  · rintro ⟨r', hr'⟩
    obtain ⟨v, hv, _⟩ := (hg r').1 hr'
    exact Part.dom_iff_mem.2 ⟨v, hv⟩
  · intro hd
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.1 hd
    exact ⟨_, (hg _).2 ⟨v, hv, rfl⟩⟩

/-- **`M_u` halts from `(3 ^ m, 0)` exactly when the universal code halts on `m`.** -/
theorem M_u_halts_iff (m : ℕ) : CM.Halts M_u (3 ^ m) 0 ↔ (uCode.eval m).Dom := by
  rw [← uProg_exec_iff, ← Prog.halts_iff_exec, ← godel_initRegs (k := k_u) (by unfold k_u; omega)]
  exact (halts_iff regsBelow_KM_u (initRegs m)).symm

/-- **Two-counter halting is undecidable for the fixed machine `M_u`.** -/
theorem cm_halts_undecidable : ¬ ComputablePred (fun ab : ℕ × ℕ => CM.Halts M_u ab.1 ab.2) := by
  rintro ⟨hd, hc⟩
  apply universal_dom_undecidable uCode_spec
  refine ⟨fun m => @decidable_of_iff _ _ (M_u_halts_iff m) (hd (3 ^ m, 0)), ?_⟩
  have hg : Computable (fun m : ℕ => ((3 ^ m, 0) : ℕ × ℕ)) :=
    (Primrec.pair (Primrec₂.comp (Primrec₂.unpaired'.1 Nat.Primrec.pow) (Primrec.const 3)
      Primrec.id)
      (Primrec.const 0)).to_comp
  have := hc.comp hg
  convert this using 2 with m
  simp only [decide_eq_decide]
  exact (M_u_halts_iff m).symm

/-- **The F<: corollary, as a many-one reduction** (part B5): the universal code halts on `m`
exactly when the F<: subtyping goal `FsubPierce.enc M_u (3 ^ m) 0` is derivable.  (A
`¬ ComputablePred` statement for `Sub` additionally needs a `Primcodable` encoding of F<: goals
and the computability of `m ↦ FsubPierce.enc M_u (3 ^ m) 0`.) -/
theorem universal_dom_iff_sub (m : ℕ) :
    (uCode.eval m).Dom ↔ Sub (FsubPierce.enc M_u (3 ^ m) 0) :=
  (M_u_halts_iff m).symm.trans (FsubPierce.cm_halts_iff_sub _ _ _)

end Universal

end Minsky
