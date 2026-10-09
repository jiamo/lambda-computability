import Start.SpaceProgCounter

/-!
# Finite dispatch for tape programs

This library's own combinators on top of `Start/SpaceProgCounter.lean` (task
`M27-LOGSPACE-TRANSFER`, reverse direction): a tape program has a fixed finite control, so a
simulator of another machine must *branch* on the finitely many values it reads (a control state
stored in unary, symbols under several simulated heads) and continue with a program depending on
the values read.  This module provides

* `Tracks.seqFor` — a sequence of `n` programs indexed by `ℕ`, with its stage rule;
* `Tracks.appendN` — append `n` copies of a bit to a register;
* `Tracks.caseUnary` — branch on the value of a register holding a number in unary, restoring
  it, with its specification `Tracks.runs_caseUnary`;
* `Tracks.readAll` — read `n` values with a reading primitive and continue with the function
  of all values read (`Tracks.runs_readAll`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace Tracks

open Prog

variable {x : List Bool} {B : ℕ} {K : ℕ}

/-- `op 0; op 1; …; op (n - 1)`. -/
def seqFor : ℕ → (ℕ → Prog) → Prog
  | 0, _ => skip
  | n + 1, op => .seq (seqFor n op) (op n)

theorem runs_seqFor (op : ℕ → Prog) (st : ℕ → TState) (n : ℕ)
    (hst : ∀ k, st k = ⟨(st k).view, (st k).head, (st k).inHead⟩)
    (h : ∀ k, k < n → Runs x B (op k) (st k) (st (k + 1))) :
    Runs x B (seqFor n op) (st 0) (st n) := by
  induction n with
  | zero => exact (runs_skip _ _ _).of_eq (hst 0) (hst 0).symm
  | succ n ih => exact (ih (fun k hk => h k (by omega))).seq (h n (by omega))

/-- Append `n` copies of `β` to register `j`. -/
def appendN (K j : ℕ) (β : Bool) (n : ℕ) : Prog := seqFor n (fun _ => append K j β)

theorem runs_appendN (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (β : Bool) (n N : ℕ)
    (hN : (R j).length + n ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (appendN K j β n) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R j (R j ++ List.replicate n β)), 0, i⟩ := by
  have := runs_seqFor (x := x) (B := B) (fun _ => append K j β)
    (fun k => ⟨lay K (Function.update R j (R j ++ List.replicate k β)), 0, i⟩) n
    (fun _ => rfl) (fun k hk => by
      have h := runs_append (x := x) (B := B) (Function.update R j (R j ++ List.replicate k β))
        j hj β N (by simp; omega) hB i
      simp only [Function.update_self, Function.update_idem] at h
      refine h.of_eq rfl ?_
      rw [List.replicate_succ', List.append_assoc])
  refine this.of_eq ?_ rfl
  simp

/-- Branch on the value `v ≤ d` of register `j`, which holds `v` in unary (`true`s); the register is
restored before `g v` runs. -/
def caseUnary (K j : ℕ) : ℕ → (ℕ → Prog) → Prog
  | 0, g => g 0
  | d + 1, g => ifNE j
      (popBranch K j (caseUnary K j d (fun v => .seq (append K j true) (g (v + 1))))
        (caseUnary K j d (fun v => .seq (append K j true) (g (v + 1)))))
      (g 0)

theorem runs_caseUnary (j : ℕ) (hj : j < K) (N : ℕ) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    ∀ (d : ℕ) (R : ℕ → List Bool) (v : ℕ) (g : ℕ → Prog) (s' : TState),
      R j = List.replicate v true → v ≤ d → v ≤ N →
      Runs x B (g v) ⟨lay K R, 0, i⟩ s' →
      Runs x B (caseUnary K j d g) ⟨lay K R, 0, i⟩ s' := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  intro d
  induction d with
  | zero =>
      intro R v g s' _ hv _ hg
      obtain rfl : v = 0 := by omega
      exact hg
  | succ d ih =>
      intro R v g s' hR hv hvN hg
      refine runs_ifNE R j hj hwB i _ _ _ (fun hne => ?_) (fun he => ?_)
      · obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := by
          cases v with
          | zero => simp [hR] at hne
          | succ v => exact ⟨v, rfl⟩
        refine runs_popBranch R j hj hne N (by rw [hR]; simp; omega) hB i _ _ _ ?_
        have hR' : (Function.update R j (R j).dropLast) j = List.replicate v' true := by
          rw [Function.update_self, hR, List.replicate_succ', List.dropLast_concat]
        have hcont : Runs x B (.seq (append K j true) (g (v' + 1)))
            ⟨lay K (Function.update R j (R j).dropLast), 0, i⟩ s' := by
          refine (runs_append _ j hj true N (by rw [hR']; simp; omega) hB i).seq ?_
          rw [Function.update_idem, hR', ← List.replicate_succ', ← hR, Function.update_eq_self]
          exact hg
        split
        · exact ih _ v' _ s' hR' (by omega) (by omega) hcont
        · exact ih _ v' _ s' hR' (by omega) (by omega) hcont
      · obtain rfl : v = 0 := by
          cases v with
          | zero => rfl
          | succ v => simp [hR] at he
        exact hg

/-- Read the values number `0, …, n - 1` with the primitive `rd`, then continue with `k` applied to
the function of the values read (`dflt` beyond `n`). -/
def readAll {α : Type} (rd : ℕ → (α → Prog) → Prog) (dflt : α) :
    ℕ → ((ℕ → α) → Prog) → Prog
  | 0, k => k (fun _ => dflt)
  | n + 1, k => readAll rd dflt n (fun f => rd n (fun a => k (Function.update f n a)))

theorem runs_readAll {α : Type} (rd : ℕ → (α → Prog) → Prog) (dflt : α) (val : ℕ → α)
    (s : TState) (n : ℕ)
    (hrd : ∀ j, j < n → ∀ (cont : α → Prog) (s' : TState),
      Runs x B (cont (val j)) s s' → Runs x B (rd j cont) s s') :
    ∀ (k : (ℕ → α) → Prog) (s' : TState),
      Runs x B (k (fun i => if i < n then val i else dflt)) s s' →
      Runs x B (readAll rd dflt n k) s s' := by
  induction n with
  | zero =>
      intro k s' h
      simp only [Nat.not_lt_zero, if_false] at h
      exact h
  | succ n ih =>
      intro k s' h
      refine ih (fun j hj => hrd j (by omega)) _ s' ?_
      refine hrd n (by omega) _ s' ?_
      convert h using 2
      funext i
      simp only [Function.update_apply]
      split_ifs <;> first | (subst_vars; rfl) | omega | rfl

end Tracks

end Complexity.Space
