/-
**The whole replay of the verifier as one Cobham term** (the second exit criterion of
`M21-VERIFIER-STEP-COB`).

The eight words of a state of `Complexity.Shamir.stepW` are packed into one word as a sequence of
records (`Complexity.Shamir.packW`); the step of `Start/ShamirCob.lean` then becomes one Cobham
term on packed states (`Complexity.Shamir.stepPT`, `Complexity.Shamir.eval_stepPT`), and the run of
the machine is `Complexity.Cob.iterT` of it, as long as the packed states stay below a bound
(`Complexity.Shamir.eval_iterT_run`).

Main definitions:

* `Complexity.Shamir.packW`, `Complexity.Shamir.unpackT`, `Complexity.Shamir.packT` — packing;
* `Complexity.Shamir.stepPT` — the step on packed states.

Main results:

* `Complexity.Shamir.eval_stepPT` — the packed step computes the step;
* `Complexity.Shamir.eval_iterT_run` — the iteration term computes the run;
* `Complexity.Shamir.length_packW_le` — the length of a packed state satisfying the invariant of
  `Start/ShamirBound.lean`.
-/

import Start.ShamirCob
import Start.CobhamTimeIter

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### Packing -/

/-- A list of words as one word: the sequence of their records. -/
def packW (ws : List Word) : Word := (ws.map encMsg).flatten

/-- The record number `i` of the value of `t`. -/
def unpackT (i : ℕ) (t : Cob) : Cob := Cob.recGetT (Nat.iterate Cob.recSkipT i t)

theorem eval_iterate_recSkipT (t : Cob) (args : List Word) :
    ∀ i, (Nat.iterate Cob.recSkipT i t).eval args = recSkip^[i] (t.eval args)
  | 0 => rfl
  | i + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Cob.eval_recSkipT,
        eval_iterate_recSkipT t args i]

theorem recSkip_iterate_packW : ∀ (ws : List Word) (i : ℕ), i ≤ ws.length →
    recSkip^[i] (packW ws) = packW (ws.drop i)
  | _, 0, _ => rfl
  | [], i + 1, h => by simp at h
  | w :: ws, i + 1, h => by
      rw [Function.iterate_succ_apply]
      have : recSkip (packW (w :: ws)) = packW ws := by simp [packW]
      rw [this, recSkip_iterate_packW ws i (by simpa using h)]
      rfl

theorem eval_unpackT {t : Cob} {args : List Word} {ws : List Word} (ht : t.eval args = packW ws)
    {i : ℕ} (hi : i < ws.length) : (unpackT i t).eval args = ws[i] := by
  rw [unpackT, Cob.eval_recGetT, eval_iterate_recSkipT, ht, recSkip_iterate_packW _ _ hi.le]
  have e : ws.drop i = ws[i] :: ws.drop (i + 1) := List.drop_eq_getElem_cons hi
  rw [e, packW, List.map_cons, List.flatten_cons, recGet_encMsg]

/-- Packing the values of a list of terms. -/
def packT : List Cob → Cob
  | [] => .empty
  | t :: ts => Cob.catT (Cob.encMsgT t) (packT ts)

theorem eval_packT (args : List Word) :
    ∀ ts : List Cob, (packT ts).eval args = packW (ts.map fun g => g.eval args)
  | [] => by simp [packT, packW]
  | t :: ts => by simp [packT, packW, eval_packT args ts]

theorem length_packW (ws : List Word) :
    (packW ws).length = (ws.map fun w => 2 * w.length + 1).sum := by
  induction ws with
  | nil => simp [packW]
  | cons w ws ih => simp [packW] at ih ⊢; rw [ih]

/-! ### The packed step -/

/-- The arguments of the step terms, read from `[W, 1^p, 1^N, 1^d]` with `W` a packed state. -/
def unpackArgs : List Cob :=
  [unpackT 0 (.proj 0), unpackT 1 (.proj 0), unpackT 2 (.proj 0), unpackT 3 (.proj 0),
    unpackT 4 (.proj 0), unpackT 5 (.proj 0), unpackT 6 (.proj 0), unpackT 7 (.proj 0),
    .proj 1, .proj 2, .proj 3]

/-- **The step on packed states.** -/
def stepPT : Cob := packT (stepTs.map fun g => .comp g unpackArgs)

theorem eval_unpack_encSt (p N d : ℕ) (s : St) (i : ℕ) (hi : i < 8) :
    (unpackT i (.proj 0)).eval [packW (encSt s), un p, un N, un d] =
      (encSt s)[i]'(by simpa [encSt] using hi) :=
  eval_unpackT (by simp) _

theorem eval_unpackArgs (p N d : ℕ) (s : St) :
    unpackArgs.map (fun g => g.eval [packW (encSt s), un p, un N, un d]) = encArgs p N d s := by
  simp only [unpackArgs, List.map_cons, List.map_nil]
  rw [eval_unpack_encSt p N d s 0 (by omega), eval_unpack_encSt p N d s 1 (by omega),
    eval_unpack_encSt p N d s 2 (by omega), eval_unpack_encSt p N d s 3 (by omega),
    eval_unpack_encSt p N d s 4 (by omega), eval_unpack_encSt p N d s 5 (by omega),
    eval_unpack_encSt p N d s 6 (by omega), eval_unpack_encSt p N d s 7 (by omega)]
  simp [encSt, encArgs]

/-- **The packed step computes the step of the verifier**, on every state. -/
theorem eval_stepPT {p : ℕ} (hp : 0 < p) (N d : ℕ) (s : St) :
    stepPT.eval [packW (encSt s), un p, un N, un d] = packW (encSt (stepW p N d s)) := by
  rw [stepPT, eval_packT, ← eval_stepTs N d s hp, List.map_map]
  congr 1
  apply List.map_congr_left
  intro g _
  simp only [Function.comp_apply, Cob.eval_comp, eval_unpackArgs]

/-! ### Bounds -/

/-- **The length of a packed state satisfying the invariant.** -/
theorem length_packW_le {p N cl tl : ℕ} {s : St} (h : Inv p N cl tl s) :
    (packW (encSt s)).length ≤
      2 * (cl + N + N * p + p + tl * (2 * (N * p) + 2 * p + 2) + tl + 2) + 8 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h.length_le
  rw [length_packW]
  simp only [encSt, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-! ### The run as an iteration -/

/-- A term over a context `ctx` of `c` words, read from `W :: ctx`. -/
def shiftT (c : ℕ) (t : Cob) : Cob := .comp t (Cob.shiftArgs c 1)

theorem eval_shiftT (t : Cob) (W : Word) (ctx : List Word) :
    (shiftT ctx.length t).eval (W :: ctx) = t.eval ctx := by
  have hm := Cob.map_eval_shiftArgs [W] ctx
  simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hm
  rw [shiftT, Cob.eval_comp, hm]

/-- The packed step with the parameters `1^p`, `1^N`, `1^d` computed from a context of `c`
words. -/
def stepV (c : ℕ) (pT NT dT : Cob) : Cob :=
  .comp stepPT [.proj 0, shiftT c pT, shiftT c NT, shiftT c dT]

theorem eval_stepV {ctx : List Word} {pT NT dT : Cob} {p N d : ℕ} (hp : 0 < p)
    (hpT : pT.eval ctx = un p) (hNT : NT.eval ctx = un N) (hdT : dT.eval ctx = un d) (s : St) :
    (stepV ctx.length pT NT dT).eval (packW (encSt s) :: ctx) =
      packW (encSt (stepW p N d s)) := by
  simp only [stepV, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, eval_shiftT, hpT, hNT, hdT]
  exact eval_stepPT hp N d s

theorem iterate_stepV {ctx : List Word} {pT NT dT : Cob} {p N d : ℕ} (hp : 0 < p)
    (hpT : pT.eval ctx = un p) (hNT : NT.eval ctx = un N) (hdT : dT.eval ctx = un d) (s : St) :
    ∀ j, (fun W => (stepV ctx.length pT NT dT).eval (W :: ctx))^[j] (packW (encSt s)) =
      packW (encSt ((stepW p N d)^[j] s))
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', iterate_stepV hp hpT hNT hdT s j,
        Function.iterate_succ_apply', eval_stepV hp hpT hNT hdT]

/-- **The iteration term computes the run of the verifier**, as long as the run keeps the
invariant and the bound term exceeds the bound of `length_packW_le`. -/
theorem eval_iterT_run {ctx : List Word} {initT pT NT dT bndT : Cob} {p N d cl tl : ℕ}
    (hp : 0 < p) (hpT : pT.eval ctx = un p) (hNT : NT.eval ctx = un N) (hdT : dT.eval ctx = un d)
    {s : St} (hinit : initT.eval ctx = packW (encSt s))
    (hinv : ∀ j, Inv p N cl tl ((stepW p N d)^[j] s))
    (hbnd : 2 * (cl + N + N * p + p + tl * (2 * (N * p) + 2 * p + 2) + tl + 2) + 8 ≤
      (bndT.eval ctx).length) (w : Word) :
    (Cob.iterT initT (stepV ctx.length pT NT dT) bndT ctx.length).eval (w :: ctx) =
      packW (encSt ((stepW p N d)^[w.length] s)) := by
  rw [Cob.eval_iterT, hinit, iterate_stepV hp hpT hNT hdT]
  intro j _ _
  rw [hinit, iterate_stepV hp hpT hNT hdT]
  exact (length_packW_le (hinv j)).trans hbnd

end Complexity.Shamir
