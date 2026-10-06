/-
**Iterating a Cobham term a polynomial number of times, in polynomial time.**

Cobham's class is closed under bounded recursion on notation, and that is exactly what is needed
to run a *step* function a number of times given in unary, as long as every intermediate state is
shorter than a bound computed by a Cobham term: the recursion runs over the counter `1^k`, its
value after `j` bits is the state after `j` steps, and the truncation to the bound — which bounded
recursion imposes — never bites.  This is the time-model counterpart of
`Start/CobhamIterate.lean`, which iterates Cobham terms *on a tape* (in polynomial space, for any
number of rounds).

The verifier of Shamir's protocol (`M21-VERIFIER-POLY`) is such an iteration: it replays the
protocol over the transcript one step at a time, carrying a state of polynomial length.

Main definitions:

* `Complexity.Cob.shiftArgs` — the context words of a term, read from a later position;
* `Complexity.Cob.iterT` — the iteration of a step term, the number of rounds given by the length
  of the first argument.

Main results:

* `Complexity.Cob.eval_iterT` — **the iteration term computes the `k`-fold iterate of the step**,
  on a counter of length `k`, when every intermediate state fits in the bound.
-/

import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- The projections onto the arguments `off, off + 1, …, off + c - 1`. -/
def Cob.shiftArgs (c off : ℕ) : List Cob := (List.range c).map fun i => Cob.proj (i + off)

theorem Cob.map_eval_shiftArgs (pre ctx : List Word) :
    (Cob.shiftArgs ctx.length pre.length).map (fun g => g.eval (pre ++ ctx)) = ctx := by
  apply List.ext_getElem
  · simp [Cob.shiftArgs]
  · intro i h₁ h₂
    simp only [Cob.shiftArgs, List.map_map, List.getElem_map, List.getElem_range,
      Function.comp_apply, Cob.eval_proj]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    rw [List.getElem_append_right (by omega)]
    congr 1; omega

/-- The iteration of `step`: on `(w, ctx)` with `ctx` of `c` words, `|w|` rounds of
`s ↦ step(s, ctx)` from `init(ctx)`, every state truncated to the length of `bnd(ctx)`. -/
def Cob.iterT (init step bnd : Cob) (c : ℕ) : Cob :=
  let h : Cob := .comp step (Cob.proj 1 :: Cob.shiftArgs c 2)
  .bRec init h h (.comp bnd (Cob.shiftArgs c 1))

/-- **Iterating a Cobham term**: on a counter of length `k`, the iteration term computes the
`k`-th iterate of the step, as long as no intermediate state exceeds the bound. -/
theorem Cob.eval_iterT (init step bnd : Cob) (ctx : List Word) :
    ∀ (w : Word),
      (∀ j, 1 ≤ j → j ≤ w.length →
        ((fun s => step.eval (s :: ctx))^[j] (init.eval ctx)).length ≤ (bnd.eval ctx).length) →
      (Cob.iterT init step bnd ctx.length).eval (w :: ctx) =
        (fun s => step.eval (s :: ctx))^[w.length] (init.eval ctx)
  | [], _ => by simp [Cob.iterT]
  | b :: w, hb => by
      have ih := Cob.eval_iterT init step bnd ctx w
        (fun j h1 h2 => hb j h1 (by simp; omega))
      rw [Cob.iterT, Cob.eval_bRec_cons, ← Cob.iterT, ih]
      have hstep : (Cob.comp step (Cob.proj 1 :: Cob.shiftArgs ctx.length 2)).eval
          (w :: (fun s => step.eval (s :: ctx))^[w.length] (init.eval ctx) :: ctx) =
            step.eval ((fun s => step.eval (s :: ctx))^[w.length] (init.eval ctx) :: ctx) := by
        have hm := Cob.map_eval_shiftArgs
          [w, (fun s => step.eval (s :: ctx))^[w.length] (init.eval ctx)] ctx
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hm
        rw [Cob.eval_comp, List.map_cons, hm, Cob.eval_proj]
        rfl
      have hbd : (Cob.comp bnd (Cob.shiftArgs ctx.length 1)).eval ((b :: w) :: ctx) =
          bnd.eval ctx := by
        have hm := Cob.map_eval_shiftArgs [b :: w] ctx
        simp only [List.cons_append, List.nil_append, List.length_cons, List.length_nil] at hm
        rw [Cob.eval_comp, hm]
      have hlen := hb (w.length + 1) (by omega) (by simp)
      rw [Function.iterate_succ_apply'] at hlen
      rw [hbd]
      split <;>
      · rw [hstep, List.take_of_length_le hlen]
        simp [Function.iterate_succ_apply']

end Complexity
