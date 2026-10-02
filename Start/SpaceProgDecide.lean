/-
**Deciding a language by a tape program.**

The last reusable piece between the exact-state specifications of `Start/SpaceProgLib.lean` and
the classes of `Start/SpaceMachine.lean`.  A *decider* is a tape program `p` followed by a test
of the bit under the work head: if it is set the machine halts in its accepting state, otherwise
it loops forever (the machine of a program has no rejecting halting state, so rejection is
non-termination, as everywhere in `Start/SpaceProg.lean`).

`Complexity.Space.Prog.dspace_of_runs` is the theorem a client uses: if on every input `x` the
program `p` runs, within `B x` cells, from the blank tape to a state in which the bit under the
work head says whether `x ∈ L`, then `L ∈ DSPACE s` for any `s` with `B x ≤ s |x|`.  The run-level
argument — the machine is deterministic, its unique run is the run of `p` followed by the test,
and every configuration it ever reaches fits in the bound — is done once here, through
`Complexity.Space.Realizes`.

Main definitions:

* `Complexity.Space.Prog.decider` — the program `p; if bit then halt (accept) else loop`.

Main results:

* `Complexity.Space.Prog.dspace_of_runs`, `Complexity.Space.Prog.pspace_of_runs`.
-/

import Mathlib
import Start.SpaceProgLib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

theorem writeAt_getD_self : ∀ (l : List Bool) (i : ℕ), i < l.length →
    writeAt l i (l.getD i false) = l
  | [], _, h => absurd h (by simp)
  | a :: t, 0, _ => by simp [writeAt]
  | a :: t, i + 1, h => by
      simp only [writeAt, List.getD_cons_succ]
      rw [writeAt_getD_self t i (by simpa using h)]

theorem touch_touch (x : List Bool) (c : Config) : touch x (touch x c) = touch x c := by
  simp only [touch, eff, rdW, moveIn, moveWork]
  congr 1
  exact writeAt_getD_self _ _ (by simp only [writeAt_length]; omega)

@[simp] theorem touch_at (x : List Bool) (c : Config) (q : ℕ) : touch x (c.at q) = touch x c :=
  rfl

theorem init_abs : init.abs = ⟨fun _ => false, 0, 0⟩ := by
  simp only [Config.abs, init]
  congr 1

namespace Prog

/-- The decider of a program: run `p`, then accept (halt in the final state) if the bit under the
work head is set, and loop forever otherwise. -/
def decider (p : Prog) : Prog := .seq p (.ite (fun _ w => w) skip (.loop (fun _ _ => true) skip))

theorem step_act {M : Machine} {f : Option Bool → Bool → Bool × Dir × Dir} {b e : ℕ}
    (h : Hosts M (.act f) b e) (x : List Bool) (c : Config) (hc : c.state = b) :
    M.Step x c ((eff x c (f (rdIn x c) (rdW c))).at e) := by
  have h1 := h c.state (by omega) (by simp [size]; omega) (rdIn x c) (rdW c)
  have h2 : M.delta c.state (rdIn x c) (rdW c) = [(e, f (rdIn x c) (rdW c))] := by
    rw [h1]; simp [delta, hc]
  exact step_of_delta h2

theorem step_ite {M : Machine} {t : Test} {p q : Prog} {b e : ℕ} (h : Hosts M (.ite t p q) b e)
    (x : List Bool) (c : Config) (hc : c.state = b) :
    M.Step x c ((touch x c).at (if t (rdIn x c) (rdW c) then b + 1 else b + 1 + p.size)) := by
  subst hc
  exact step_of_delta (h.test (rdIn x c) (rdW c))

theorem step_loop {M : Machine} {t : Test} {p : Prog} {b e : ℕ} (h : Hosts M (.loop t p) b e)
    (x : List Bool) (c : Config) (hc : c.state = b) :
    M.Step x c ((touch x c).at (if t (rdIn x c) (rdW c) then b + 1 else e)) := by
  subst hc
  exact step_of_delta (h.loop_test (rdIn x c) (rdW c))

theorem seg_of_path {M : Machine} {x : List Bool} {B : ℕ} {a b : Config}
    (h : M.Path x (M.Quiet B) a b) (hne : a.state ≠ b.state) : M.Seg x B a b := by
  cases h with
  | refl => exact absurd rfl hne
  | head _ hs hr => exact ⟨_, hs, hr⟩

/-- **Deciding a language by a tape program.**  If on every input `x` the program `p` runs within
`B x` cells from the blank tape to a state in which the bit under the work head is set exactly
when `x ∈ L`, then `L` is decided by the machine of `decider p` in space `B`. -/
theorem dspace_of_runs (p : Prog) (L : Language) (B : List Bool → ℕ) (s : ℕ → ℕ)
    (out : List Bool → TState) (hB1 : ∀ x, 1 ≤ B x) (hBs : ∀ x, B x ≤ s x.length)
    (hrun : ∀ x, Runs x (B x) p ⟨fun _ => false, 0, 0⟩ (out x))
    (hout : ∀ x, (out x).view (out x).head = true ↔ L x) : DSPACE s L := by
  classical
  have hosts := machine_hosts (decider p)
  have hp : Hosts (decider p).machine p 0 (0 + p.size) := hosts.seq_left
  have hite : Hosts (decider p).machine (.ite (fun _ w => w) skip (.loop (fun _ _ => true) skip))
      (0 + p.size) (decider p).size := hosts.seq_right
  have hsz : (decider p).size = p.size + 4 := by
    simp only [decider, size, skip]
  have hskip : Hosts (decider p).machine skip (0 + p.size + 1) (decider p).size := hite.ite_left
  have hloop : Hosts (decider p).machine (.loop (fun _ _ => true) skip)
      (0 + p.size + 1 + skip.size) (decider p).size := hite.ite_right
  have hskip' : Hosts (decider p).machine skip (0 + p.size + 1 + skip.size + 1)
      (0 + p.size + 1 + skip.size) := hloop.loop_body
  have hsk1 : skip.size = 1 := rfl
  have hacc : ∀ q, (decider p).machine.accept q = decide (q = p.size + 4) := by
    intro q; rw [machine_accept, hsz]
  -- the run of `p` on each input
  have hex : ∀ x, ∃ d, Exec x (fun c => c.space ≤ B x) p init d ∧ d.abs = out x ∧
      d.space ≤ B x := fun x => hrun x init init_abs
    (le_trans (by simp [Config.space, init]) (hB1 x))
  choose dd hdd using hex
  -- the steps after it
  have hstep_skip : ∀ x (c : Config), c.state = p.size + 1 →
      (decider p).machine.Step x c ((touch x c).at (p.size + 4)) := by
    intro x c hc
    have := step_act hskip x c (by omega)
    rw [hsz] at this
    exact this
  have hstep_test : ∀ x (c : Config), c.state = p.size →
      (decider p).machine.Step x c ((touch x c).at (if rdW c then p.size + 1 else p.size + 2)) := by
    intro x c hc
    have := step_ite hite x c (by omega)
    rw [hsk1, show 0 + p.size + 1 + 1 = p.size + 2 by omega,
      show 0 + p.size + 1 = p.size + 1 by omega] at this
    exact this
  have hstep_loop : ∀ x (c : Config), c.state = p.size + 2 →
      (decider p).machine.Step x c ((touch x c).at (p.size + 3)) := by
    intro x c hc
    have := step_loop hloop x c (by rw [hsk1]; omega)
    rw [if_pos rfl, hsk1, show 0 + p.size + 1 + 1 + 1 = p.size + 3 by omega] at this
    exact this
  have hstep_body : ∀ x (c : Config), c.state = p.size + 3 →
      (decider p).machine.Step x c ((touch x c).at (p.size + 2)) := by
    intro x c hc
    have := step_act hskip' x c (by rw [hsk1]; omega)
    rw [hsk1, show 0 + p.size + 1 + 1 = p.size + 2 by omega] at this
    exact this
  -- the path through `p`
  have hpath : ∀ x, (decider p).machine.Path x ((decider p).machine.Quiet (B x)) init
      ((dd x).at p.size) := by
    intro x
    have h := path_of_exec (hdd x).1 rfl hp
    rw [zero_add] at h
    refine h.mono ?_
    rintro e ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1, ?_⟩
    rw [hacc, decide_eq_false_iff_not]; omega
  have hread : ∀ x, rdW ((dd x).at p.size) = decide (L x) := by
    intro x
    have h1 : rdW ((dd x).at p.size) = (out x).view (out x).head := by rw [← (hdd x).2.1]; rfl
    rw [h1]
    by_cases hx : L x
    · simp [hx, (hout x).2 hx]
    · simp only [hx, decide_false]
      cases h : (out x).view (out x).head
      · rfl
      · exact absurd ((hout x).1 h) hx
  have hspace_d : ∀ x, (dd x).space ≤ B x := fun x => (hdd x).2.2
  -- the abstract machine
  let A : AbsMachine (Bool × Bool) :=
    { start := fun x => (false, decide (L x))
      step := fun s => if s.1 then (if s.2 then none else some (true, false)) else some (true, s.2)
      accept := fun s => s.1 && s.2 }
  let code : List Bool → Bool × Bool → Config := fun x s =>
    if s.1 then
      (if s.2 then (touch x (touch x ((dd x).at p.size))).at (p.size + 4)
       else (touch x ((dd x).at p.size)).at (p.size + 2))
    else init
  have hreach : ∀ x s, A.Reaches x s →
      s = (false, decide (L x)) ∨ s = (true, decide (L x)) := by
    intro x s hs
    induction hs with
    | refl => exact Or.inl rfl
    | tail _ hst ih =>
        simp only [AbsMachine.StepRel, A] at hst
        rcases ih with rfl | rfl
        · simp at hst; exact Or.inr hst.symm
        · cases h : decide (L x) <;>
            simp only [↓reduceIte, h, Bool.false_eq_true, Option.some.injEq, reduceCtorEq] at hst
          exact Or.inr (by rw [← hst])
  have hq : ∀ x, (init.at 0).state ≠ ((dd x).at p.size).state := by
    intro x; simp [init]; have := size_pos p; omega
  have hR : Realizes (decider p).machine A code B := by
    refine ⟨fun x => rfl, ?_, ?_, ?_, ?_⟩
    · intro x s _
      rcases s with ⟨_ | _, _ | _⟩ <;> simp [code, A, hacc, init]
    · intro x s _
      rcases s with ⟨_ | _, _ | _⟩ <;>
        simp only [code, if_true, if_false, Bool.false_eq_true, Config.at_space, space_touch] <;>
        first | exact le_trans (show init.space ≤ 1 by simp [Config.space, init]) (hB1 x) |
          exact hspace_d x
    · intro x s _ hs
      rcases s with ⟨_ | _, _ | _⟩ <;> simp [A] at hs
      exact machine_final_halts _ _ _ (by simp [code, hsz])
    · intro x s s' hs hss
      rcases hreach x s hs with rfl | rfl
      · simp only [A, Bool.false_eq_true, if_false, Option.some.injEq] at hss
        subst hss
        have hquiet : (decider p).machine.Quiet (B x) ((dd x).at p.size) :=
          ⟨by simpa using hspace_d x, by rw [hacc]; simp⟩
        have hseg := seg_of_path (hpath x) (hq x)
        have h1 := hstep_test x ((dd x).at p.size) rfl
        rw [hread x] at h1
        cases hL : decide (L x)
        · rw [hL] at h1
          exact hseg.trans hquiet (Machine.Seg.single h1)
        · rw [hL, if_pos rfl] at h1
          refine hseg.trans hquiet (Machine.Seg.trans (Machine.Seg.single h1) ⟨?_, ?_⟩
            (Machine.Seg.single (hstep_skip x _ rfl)))
          · simpa [space_touch] using hspace_d x
          · rw [hacc]; simp
      · cases hL : decide (L x) <;>
          simp only [↓reduceIte, hL, Bool.false_eq_true, Option.some.injEq, reduceCtorEq, A] at hss
        subst hss
        simp only [code, if_true, Bool.false_eq_true, if_false]
        have h1 := hstep_loop x ((touch x ((dd x).at p.size)).at (p.size + 2)) rfl
        have h3 := hstep_body x ((touch x ((touch x ((dd x).at p.size)).at (p.size + 2))).at
          (p.size + 3)) rfl
        simp only [touch_at, touch_touch] at h1 h3
        refine Machine.Seg.trans (Machine.Seg.single h1) ⟨?_, ?_⟩ (Machine.Seg.single h3)
        · simpa [space_touch] using hspace_d x
        · rw [hacc]; simp
  obtain ⟨M', hwf, hdet, hsp, hL⟩ :=
    hR.dspace (machine_wellFormed _) (machine_deterministic _) hBs
  refine ⟨M', hwf, hdet, hsp, fun x => ?_⟩
  rw [← hL x]
  constructor
  · intro hx
    refine ⟨(true, decide (L x)), Relation.ReflTransGen.single (by simp [A, AbsMachine.StepRel]),
      by simp [A, hx]⟩
  · rintro ⟨s, hs, hacc'⟩
    rcases hreach x s hs with rfl | rfl <;> simp_all [A]

/-- **Membership in `PSPACE` from a tape program.** -/
theorem pspace_of_runs (p : Prog) (L : Language) (B : List Bool → ℕ) (s : ℕ → ℕ)
    (hs : PolyBound s) (out : List Bool → TState) (hB1 : ∀ x, 1 ≤ B x)
    (hBs : ∀ x, B x ≤ s x.length)
    (hrun : ∀ x, Runs x (B x) p ⟨fun _ => false, 0, 0⟩ (out x))
    (hout : ∀ x, (out x).view (out x).head = true ↔ L x) : PSPACE L :=
  ⟨s, hs, dspace_of_runs p L B s out hB1 hBs hrun hout⟩

end Prog

end Complexity.Space
