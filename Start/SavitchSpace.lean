/-
Savitch's theorem: a nondeterministic machine running in space `s` is simulated deterministically
in space `O(s²)` — here, by the stack machine of `Start/SavitchVM.lean` run on the configuration
graph of `Start/SpaceConfigCount.lean`.

The three ingredients are in place: acceptance by a machine running in space `s` is reachability
in a graph with at most `q · (n+1) · (s+1)² · 2 ^ s` vertices; reachability in a graph with at
most `2 ^ k` vertices is the midpoint recursion of depth `k`; and the midpoint recursion of depth
`k` is executed by a deterministic stack machine that never holds more than `k` activation
records.  Writing `k` for `⌈log₂⌉` of the number of configurations — which is also the number of
bits one configuration takes, since the configurations inject into `{0, …, 2 ^ k - 1}` — the
simulation therefore runs in `O(k²)` bits, and `k = O(s + log n)`.

Main definitions:

* `Complexity.Space.savitchDepth M x s` — the depth `k` of the recursion, `⌈log₂⌉` of the
  configuration count;
* `Complexity.Space.savitchDecide M x s` — the decision: some accepting configuration is
  reachable from the initial one by the recursion of depth `k`.

Main results:

* `Complexity.Space.savitch_accepts_iff` — the decision is correct: it answers `true` exactly on
  the inputs the nondeterministic machine accepts;
* `Complexity.Space.savitch_trace` — each of its reachability queries is run by the deterministic
  stack machine, which never holds more than `k` activation records;
* `Complexity.Space.savitch_memBits_le` — hence in `(k + 1) · (4 k + 3)` bits of memory;
* `Complexity.Space.savitchDepth_le` — `k ≤ log₂ q + log₂ (n+1) + 2 log₂ (s+1) + s`, so the
  memory is `O((s + log n)²)`: Savitch's `O(s²)`;
* `Complexity.Space.savitch_poly_memory` — for a language in `NPSPACE` the memory the simulation
  uses is bounded by a polynomial in the length of the input.

The honest boundary: the deterministic simulation is exhibited on the stack machine, whose memory
is counted in bits of activation records, and not as an offline Turing machine of
`Start/SpaceMachine.lean`; compiling the stack machine into that model — which is the routine,
laborious half of the model-independence of space — is not formalized here, so `NPSPACE = PSPACE`
is not claimed as a theorem about `Complexity.Space.DSPACE`.
-/

import Mathlib
import Start.SpaceConfigCount
import Start.SavitchVM

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity.Reach Complexity.Savitch

variable {M : Machine} {x : List Bool} {s : ℕ}

/-! ### The depth of the recursion -/

/-- `⌈log₂⌉` of the number of configurations: the depth of Savitch's recursion, and also the
number of bits one configuration takes. -/
def savitchDepth (M : Machine) (x : List Bool) (s : ℕ) : ℕ := Nat.clog 2 (cfgBound M x s)

theorem card_le_two_pow_savitchDepth (M : Machine) (x : List Bool) (s : ℕ) :
    Fintype.card (BoundedCfg M x s) ≤ 2 ^ savitchDepth M x s :=
  le_trans (card_boundedCfg_le M x s) (Nat.le_pow_clog (by norm_num) _)

private theorem clog_mul_le (a b : ℕ) : Nat.clog 2 (a * b) ≤ Nat.clog 2 a + Nat.clog 2 b := by
  refine Nat.clog_le_of_le_pow ?_
  rw [pow_add]
  exact Nat.mul_le_mul (Nat.le_pow_clog (by norm_num) a) (Nat.le_pow_clog (by norm_num) b)

/-- The depth of the recursion is logarithmic in the number of configurations, hence linear in the
space bound and logarithmic in the length of the input. -/
theorem savitchDepth_le (M : Machine) (x : List Bool) (s : ℕ) :
    savitchDepth M x s ≤
      Nat.clog 2 M.states + Nat.clog 2 (x.length + 1) + 2 * Nat.clog 2 (s + 1) + s := by
  have h2 : Nat.clog 2 (2 ^ s) = s := Nat.clog_pow 2 s (by norm_num)
  calc savitchDepth M x s
      = Nat.clog 2 (M.states * (x.length + 1) * (s + 1) * 2 ^ s * (s + 1)) := rfl
    _ ≤ Nat.clog 2 (M.states * (x.length + 1) * (s + 1) * 2 ^ s) + Nat.clog 2 (s + 1) :=
        clog_mul_le _ _
    _ ≤ (Nat.clog 2 (M.states * (x.length + 1) * (s + 1)) + Nat.clog 2 (2 ^ s))
          + Nat.clog 2 (s + 1) := by
        exact Nat.add_le_add_right (clog_mul_le _ _) _
    _ ≤ ((Nat.clog 2 (M.states * (x.length + 1)) + Nat.clog 2 (s + 1)) + Nat.clog 2 (2 ^ s))
          + Nat.clog 2 (s + 1) := by
        exact Nat.add_le_add_right (Nat.add_le_add_right (clog_mul_le _ _) _) _
    _ ≤ (((Nat.clog 2 M.states + Nat.clog 2 (x.length + 1)) + Nat.clog 2 (s + 1))
          + Nat.clog 2 (2 ^ s)) + Nat.clog 2 (s + 1) := by
        exact Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.add_le_add_right (clog_mul_le _ _) _) _) _
    _ = Nat.clog 2 M.states + Nat.clog 2 (x.length + 1) + 2 * Nat.clog 2 (s + 1) + s := by
        rw [h2]; ring

/-! ### The decision procedure -/

/-- An enumeration of the configurations, used as the list of candidate midpoints.  The machine
never stores it: an activation record holds an *index* into it. -/
noncomputable def cfgList (M : Machine) (x : List Bool) (s : ℕ) : List (BoundedCfg M x s) :=
  (Finset.univ : Finset (BoundedCfg M x s)).toList

theorem mem_cfgList (c : BoundedCfg M x s) : c ∈ cfgList M x s :=
  Finset.mem_toList.2 (Finset.mem_univ c)

/-- Savitch's decision: some accepting configuration is reachable from the initial one, as
witnessed by the midpoint recursion of depth `savitchDepth M x s`. -/
noncomputable def savitchDecide (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) : Bool :=
  (cfgList M x s).any fun c =>
    M.accept c.1.state &&
      reachL (BoundedCfg.stepB M x s) (cfgList M x s) (savitchDepth M x s) (initB hwf hsp) c

/-- The decision is correct. -/
theorem savitch_accepts_iff (hwf : M.WellFormed) (hsp : M.SpaceBoundedOn x s) :
    M.Accepts x ↔ savitchDecide hwf hsp = true := by
  classical
  rw [accepts_iff_exists_reachable_accepting hwf hsp]
  constructor
  · rintro ⟨n, c, hc, hacc⟩
    refine List.any_eq_true.2 ⟨c, mem_cfgList c, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨hacc, ?_⟩
    rw [reachL_eq_reachB _ _ mem_cfgList,
      Reach.reachB_iff_exists_steps _ _ (card_le_two_pow_savitchDepth M x s)]
    exact ⟨n, by simpa [BoundedCfg.stepB] using hc⟩
  · intro h
    obtain ⟨c, -, hc⟩ := List.any_eq_true.1 h
    rw [Bool.and_eq_true] at hc
    obtain ⟨hacc, hreach⟩ := hc
    rw [reachL_eq_reachB _ _ mem_cfgList,
      Reach.reachB_iff_exists_steps _ _ (card_le_two_pow_savitchDepth M x s)] at hreach
    obtain ⟨n, hn⟩ := hreach
    exact ⟨n, c, by simpa [BoundedCfg.stepB] using hn, hacc⟩

/-! ### The memory bound -/

/-- Each reachability query of the decision is run by the deterministic stack machine, which
returns the answer and never holds more than `savitchDepth M x s` activation records. -/
theorem savitch_trace (a b : BoundedCfg M x s) :
    Trace (BoundedCfg.stepB M x s) (cfgList M x s) (savitchDepth M x s)
      ⟨.call a b (savitchDepth M x s), []⟩
      ⟨.ret (reachL (BoundedCfg.stepB M x s) (cfgList M x s) (savitchDepth M x s) a b), []⟩ := by
  simpa using
    trace_call (BoundedCfg.stepB M x s) (cfgList M x s) (savitchDepth M x s) a b []

/-- The memory the simulation uses, in bits: a configuration takes `savitchDepth M x s` bits — the
configurations inject into `{0, …, 2 ^ savitchDepth - 1}` — and so does each of the two counters
of an activation record, up to one bit. -/
theorem savitch_memBits_le (a u : VM (BoundedCfg M x s))
    (h : Trace (BoundedCfg.stepB M x s) (cfgList M x s) (savitchDepth M x s) a u) :
    memBits (savitchDepth M x s) (savitchDepth M x s + 1) u
      ≤ (savitchDepth M x s + 1) * (4 * savitchDepth M x s + 3) := by
  have := memBits_le_of_visited (w := savitchDepth M x s) (d := savitchDepth M x s + 1) h
  calc memBits (savitchDepth M x s) (savitchDepth M x s + 1) u
      ≤ (savitchDepth M x s + 1) *
          (2 * savitchDepth M x s + 2 * (savitchDepth M x s + 1) + 1) := this
    _ = (savitchDepth M x s + 1) * (4 * savitchDepth M x s + 3) := by ring

/-! ### Polynomial space -/

/-- For a language in `NPSPACE` the deterministic simulation runs in polynomially bounded memory:
there are a machine, a space bound and a polynomial bound on the memory of the stack machine that
decides the language.  This is Savitch's theorem in the cost model of `Start/SavitchVM.lean`. -/
theorem savitch_poly_memory {L : Language} (h : NPSPACE L) :
    ∃ (M : Machine) (s : ℕ → ℕ) (hwf : M.WellFormed) (p : ℕ → ℕ), Complexity.PolyBound p ∧
      (∀ x, ∃ hsp : M.SpaceBoundedOn x (s x.length),
        (L x ↔ savitchDecide hwf hsp = true) ∧
        ∀ (a u : VM (BoundedCfg M x (s x.length))),
          Trace (BoundedCfg.stepB M x (s x.length)) (cfgList M x (s x.length))
            (savitchDepth M x (s x.length)) a u →
          memBits (savitchDepth M x (s x.length)) (savitchDepth M x (s x.length) + 1) u
            ≤ p x.length) := by
  obtain ⟨s, ⟨as, ks, hs⟩, M, hwf, hsp, hL⟩ := h
  -- the depth is at most `log₂ q + log₂ (n+1) + 2 log₂ (s+1) + s`, which is polynomial in `n`
  refine ⟨M, s, hwf, fun n =>
    (Nat.clog 2 M.states + Nat.clog 2 (n + 1) + 2 * Nat.clog 2 (s n + 1) + s n + 1) *
      (4 * (Nat.clog 2 M.states + Nat.clog 2 (n + 1) + 2 * Nat.clog 2 (s n + 1) + s n) + 3), ?_, ?_⟩
  · -- a polynomial bound: every summand is bounded by a polynomial in `n`
    have hlog : ∀ m : ℕ, Nat.clog 2 (m + 1) ≤ m := by
      intro m
      refine Nat.clog_le_of_le_pow ?_
      exact Nat.succ_le_of_lt (Nat.lt_two_pow_self)
    have hbound : ∀ n : ℕ,
        Nat.clog 2 M.states + Nat.clog 2 (n + 1) + 2 * Nat.clog 2 (s n + 1) + s n
          ≤ M.states + n + 3 * (as * (n + 1) ^ ks) := by
      intro n
      have h1 : Nat.clog 2 M.states ≤ M.states := by
        rcases Nat.eq_zero_or_pos M.states with h | h
        · simp [h]
        · have := hlog (M.states - 1)
          have heq : M.states - 1 + 1 = M.states := by omega
          rw [heq] at this
          omega
      have h2 : Nat.clog 2 (n + 1) ≤ n := hlog n
      have h3 : Nat.clog 2 (s n + 1) ≤ s n := hlog (s n)
      have h4 : s n ≤ as * (n + 1) ^ ks := hs n
      omega
    obtain ⟨a', k', hp⟩ :
        Complexity.PolyBound (fun n => M.states + n + 3 * (as * (n + 1) ^ ks)) := by
      refine Complexity.PolyBound.add (Complexity.PolyBound.add ?_ ?_) ?_
      · exact Complexity.polyBound_const M.states
      · exact ⟨1, 1, fun n => by simp⟩
      · exact ⟨3 * as, ks, fun n => by simp [mul_assoc]⟩
    refine ⟨(a' + 1) * (4 * a' + 3) * (a' + 1), 2 * k' + k' + 1, ?_⟩
    intro n
    have hb := le_trans (hbound n) (hp n)
    have hmono :
        (Nat.clog 2 M.states + Nat.clog 2 (n + 1) + 2 * Nat.clog 2 (s n + 1) + s n + 1) *
          (4 * (Nat.clog 2 M.states + Nat.clog 2 (n + 1) + 2 * Nat.clog 2 (s n + 1) + s n) + 3)
          ≤ (a' * (n + 1) ^ k' + 1) * (4 * (a' * (n + 1) ^ k') + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    refine le_trans hmono ?_
    have hpow : (n + 1) ^ k' ≤ (n + 1) ^ (2 * k' + k' + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    calc (a' * (n + 1) ^ k' + 1) * (4 * (a' * (n + 1) ^ k') + 3)
        ≤ (a' + 1) * (n + 1) ^ k' * ((4 * a' + 3) * (n + 1) ^ k') := by
          refine Nat.mul_le_mul ?_ ?_
          · have : (1 : ℕ) ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
            nlinarith [this]
          · have : (1 : ℕ) ≤ (n + 1) ^ k' := Nat.one_le_pow _ _ (by omega)
            nlinarith [this]
      _ = (a' + 1) * (4 * a' + 3) * ((n + 1) ^ k' * (n + 1) ^ k') := by ring
      _ ≤ (a' + 1) * (4 * a' + 3) * (a' + 1) * (n + 1) ^ (2 * k' + k' + 1) := by
          have h1 : (n + 1) ^ k' * (n + 1) ^ k' = (n + 1) ^ (2 * k') := by
            rw [← pow_add]; ring_nf
          rw [h1]
          have h2 : (n + 1) ^ (2 * k') ≤ (a' + 1) * (n + 1) ^ (2 * k' + k' + 1) := by
            have : (n + 1) ^ (2 * k') ≤ (n + 1) ^ (2 * k' + k' + 1) :=
              Nat.pow_le_pow_right (by omega) (by omega)
            calc (n + 1) ^ (2 * k') ≤ (n + 1) ^ (2 * k' + k' + 1) := this
              _ ≤ (a' + 1) * (n + 1) ^ (2 * k' + k' + 1) := Nat.le_mul_of_pos_left _ (by omega)
          calc (a' + 1) * (4 * a' + 3) * (n + 1) ^ (2 * k')
              ≤ (a' + 1) * (4 * a' + 3) * ((a' + 1) * (n + 1) ^ (2 * k' + k' + 1)) :=
                Nat.mul_le_mul_left _ h2
            _ = (a' + 1) * (4 * a' + 3) * (a' + 1) * (n + 1) ^ (2 * k' + k' + 1) := by ring
  · intro x
    refine ⟨M.spaceBoundedOn_of_spaceBounded hsp x, (hL x).trans (savitch_accepts_iff _ _), ?_⟩
    intro a u hu
    refine le_trans (savitch_memBits_le a u hu) ?_
    exact Nat.mul_le_mul (by
      have := savitchDepth_le M x (s x.length); omega) (by
      have := savitchDepth_le M x (s x.length); omega)

end Complexity.Space
