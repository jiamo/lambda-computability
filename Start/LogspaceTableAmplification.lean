import Start.LogspaceTransitionTables

/-
Absorbed from github.com/openai/math (commit 3014888, i.e. 301488868beec11bfd897168433b0a64f5258559,
Apache-2.0), original path `lean/OAI/Computability/Logspace/Amplification.lean`, family 103,
paper "Exact Derandomization of Logarithmic Space: L = RL = BPL".
Adapted to this library's Lean v4.33.0 / Mathlib `v4.33.0` pin: the `OAI` namespace was dropped,
imports were renamed to `Start.Logspace*`, and proofs were repaired where the pin required it.
See `NOTICE` at the repository root.

Reconciliation with `Start/LogspaceAmplification.lean`: upstream's file ends with a class-level
wrapper `ExactDerandomization.RL_subset_BPL : RL ⊆ BPL`, built from the table-level construction
below.  This library already proves that exact statement, under that exact name, in
`Start/LogspaceAmplification.lean` (via the two-trial machine `Machine.twoTrial`).  To avoid a
duplicate declaration, the upstream wrapper is omitted here and `Start/LogspaceEquality.lean`
uses the existing `ExactDerandomization.RL_subset_BPL`; the table-level two-run amplification
(`Table.TM.twice`, `halts_twice`, `space_twice`, `prob_twice`, ...) is absorbed unchanged.
-/
/-!
Two independent finite-coin trials and the inclusion of one-sided in two-sided randomized logspace.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-!
Interleaved parallel two-run one-sided-error amplification for concrete
tables. There is no reset pass: both copies start in fresh configurations.
The input heads and work tapes are duplicated. Each pair of fresh coin bits
supplies one step of each copy; a halted copy stutters and ignores its bits.
-/

namespace ExactDerandomization.Table.TM

variable {S W H : Type} (P : TM S W H)

abbrev PS (S : Type) := (S × S) × Option Bool

def ans (a b : Option Bool) : Option Bool :=
  match a,b with
  | some c, some d => some (c || d)
  | _, _ => none

def combineAct (a b : Act S W H) : Act (PS S) (W⊕W) (H⊕H) :=
  { next := ((a.next, b.next), none)
    write := Sum.elim a.write b.write
    workMove := Sum.elim a.workMove b.workMove
    inputMove := Sum.elim a.inputMove b.inputMove }

def twice : TM (PS S) (W⊕W) (H⊕H) :=
  { start := ((P.start,P.start), none)
    out := fun s => match s.2 with
      | some _ => none
      | none => ans (P.out s.1.1) (P.out s.1.2)
    go := fun s i v coin => match s.2 with
      | none => idle (s.1, some coin) v
      | some c => combineAct
          (P.goStutter s.1.1 (fun j => i (.inl j)) (fun k => v (.inl k)) c)
          (P.goStutter s.1.2 (fun j => i (.inr j)) (fun k => v (.inr k)) coin) }

def join {n : ℕ} (c d : Conf S W H n) (p : Option Bool) : Conf (PS S) (W⊕W) (H⊕H) n :=
  ⟨((c.state,d.state),p), Sum.elim c.inputPos d.inputPos, Sum.elim c.workPos d.workPos,
    Sum.elim c.work d.work⟩

def pend (a b : S) (p : Bool) : Option Bool :=
  if ans (P.out a) (P.out b) = none then some p else none

theorem step_buf (x : Word) (c d : Conf S W H x.length) (p : Bool) :
    P.twice.step x p (join c d none) =
      join c d (P.pend c.state d.state p) := by
  cases e : ans (P.out c.state) (P.out d.state) <;>
    simp [step, pend, twice, join, idle, applyAct, e, Direction.moveInput, Direction.move]

theorem step_exec (x : Word) (c d : Conf S W H x.length) (p q : Bool) :
    P.twice.step x q (join c d (some p)) =
      join (P.step x p c) (P.step x q d) none := by
  rw [step_eq_apply (P:=P), step_eq_apply (P:=P)]

  refine Conf.ext ?_ ?_ ?_ ?_
  · rfl
  · funext j; cases j <;> rfl
  · funext k; cases k <;> rfl
  · funext k; cases k <;> rfl

theorem step_two (x : Word) (c d : Conf S W H x.length) (p q : Bool) :
    P.twice.step x q (P.twice.step x p (join c d none)) =
      join (P.step x p c) (P.step x q d) none := by
  rw [step_buf]
  cases ha : P.out c.state <;> cases hb : P.out d.state
  · rw [show P.pend c.state d.state p = _ from (by simp [pend, ha, hb, ans] :
        P.pend c.state d.state p = some p), step_exec]
  · have h : P.pend c.state d.state p = some p := by simp [pend, ha, hb, ans]
    rw [h, step_exec]
  · have h : P.pend c.state d.state p = some p := by simp [pend, ha, hb, ans]
    rw [h, step_exec]
  · have hp (r : Bool) : P.pend c.state d.state r = none := by simp [pend, ha, hb, ans]
    rw [hp p, step_buf, hp q]
    simp [step, ha, hb]

def ev (coins : CoinTape) : CoinTape := fun t => coins (t*2)
def od (coins : CoinTape) : CoinTape := fun t => coins (t*2+1)

theorem run_twice (x : Word) (coins : CoinTape) (t : ℕ) :
    P.twice.run x coins (t*2) =
      join (P.run x (ev coins) t) (P.run x (od coins) t) none := by
  induction t with
  | zero =>
    refine Conf.ext ?_ ?_ ?_ ?_
    · rfl
    · funext j; cases j <;> rfl
    · funext k; cases k <;> rfl
    · funext k; cases k <;> rfl
  | succ t ih =>
    rw [show t.succ*2 = t*2+1+1 by omega, run, run, ih, step_two]
    rfl

theorem positions_twice (x : Word) (coins : CoinTape) (s : ℕ) :
    (P.twice.run x coins s).workPos = Sum.elim ((P.run x (ev coins) (s / 2)).workPos)
      ((P.run x (od coins) (s / 2)).workPos) := by
  generalize e : s / 2 = t
  have : s = t*2 ∨ s = t*2+1 := by omega
  rcases this with eq | eq <;> subst s
  · rw [run_twice]; rfl
  · rw [run, run_twice, step_buf]; rfl

theorem out_twice (x : Word) (coins : CoinTape) (t : ℕ) :
    P.twice.out (P.twice.run x coins (t*2)).state =
      ans (P.out (P.run x (ev coins) t).state) (P.out (P.run x (od coins) t).state) := by
  rw [run_twice]; rfl

theorem halts_twice (x : Word) (t : ℕ) (e : P.halts x t) :
    P.twice.halts x (t*2) := by
  intro coins
  obtain ⟨a, ha⟩ := e (ev coins)
  obtain ⟨b, hb⟩ := e (od coins)
  exact ⟨a||b, by rw [out_twice, ha, hb]; rfl⟩

theorem half_le (f : ℕ → ℤ) (s : ℕ) :
    ((Finset.range (s+1)).image (fun t => f (t/2))).card ≤
      ((Finset.range (s/2+1)).image f).card :=
  Finset.card_le_card (by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    simp only [Finset.mem_range] at ht
    exact Finset.mem_image.mpr ⟨t/2, Finset.mem_range.mpr (by omega), rfl⟩)

theorem space_twice [Fintype W] (x : Word) (coins : CoinTape) (t : ℕ) :
    P.twice.spaceThrough x coins t ≤ P.spaceThrough x (ev coins) (t/2)
          + P.spaceThrough x (od coins) (t/2) := by
  simp only [spaceThrough, positions_twice, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  exact add_le_add (Finset.sum_le_sum (fun k _ =>
    half_le (fun r => (P.run x (ev coins) r).workPos k) t))
    (Finset.sum_le_sum (fun k _ => half_le (fun r => (P.run x (od coins) r).workPos k) t))

abbrev Flips (t : ℕ) := Fin t → Bool

def flipSplit (t : ℕ) : Flips (t*2) ≃ Flips t × Flips t where
  toFun f := (fun i => f ⟨i*2, by omega⟩, fun i => f ⟨i*2+1, by omega⟩)
  invFun g := fun i =>
    if i.val % 2 = 0 then g.1 ⟨i.val/2, by omega⟩ else g.2 ⟨i.val/2, by omega⟩
  left_inv f := by
    funext i
    dsimp
    split
    · congr 1; ext; simp; omega
    · congr 1; ext; simp; omega
  right_inv g := by
    apply Prod.ext
    · funext i; simp
    · funext i
      have he (i : ℕ) : (i*2+1)%2 = 1 := by omega
      have hd (i : ℕ) : (i*2+1)/2 = i := by omega
      simp [he, hd]

theorem split_ev (t : ℕ) (f : Flips (t*2)) :
    ev (Machine.extendCoins f) = Machine.extendCoins ((flipSplit t f).1) := by
  funext i
  unfold ev Machine.extendCoins
  by_cases e : i<t
  · have h : i*2<t*2 := by omega
    simp [e,h,flipSplit]
  · have h : ¬(i*2<t*2) := by omega
    simp [e,h]

theorem split_od (t : ℕ) (f : Flips (t*2)) :
    od (Machine.extendCoins f) = Machine.extendCoins ((flipSplit t f).2) := by
  funext i
  unfold od Machine.extendCoins
  by_cases e : i<t
  · have h : i*2+1<t*2 := by omega
    simp [e,h,flipSplit]
  · have h : ¬(i*2+1<t*2) := by omega
    simp [e,h]

abbrev wins (x : Word) (t : ℕ) : Flips t → Prop :=
  fun f => P.out (P.run x (Machine.extendCoins f) t).state = some true

abbrev Losers (x : Word) (t : ℕ) := { f // ¬ P.wins x t f }

theorem prob_losers (x : Word) (t : ℕ) :
    P.prob x t = 1 - (Fintype.card (P.Losers x t) : ℚ) / 2 ^ t := by
  change (((Finset.univ.filter (P.wins x t)).card : ℚ) / 2 ^ t) = _
  have h :
      (Finset.univ.filter (P.wins x t)).card + Fintype.card (P.Losers x t) = 2 ^ t := by
    simp only [Losers, Fintype.card_subtype]
    rw [Finset.card_filter_add_card_filter_not (P.wins x t)]
    simp [Flips]
  have hc : ((Finset.univ.filter (P.wins x t)).card : ℚ) +
      (Fintype.card (P.Losers x t) : ℚ) = 2 ^ t := by exact_mod_cast h
  field_simp
  linarith

theorem prob_twice (x : Word) (t : ℕ) (e : P.halts x t) :
    P.twice.prob x (t*2) = 1 - (1 - P.prob x t)^2 := by
  have losses (f : Flips (t*2)) :
      ¬ (P.twice.wins x (t*2) f) ↔
        ((¬ P.wins x t (flipSplit t f).1) ∧ (¬ P.wins x t (flipSplit t f).2)) := by
    simp only [wins, out_twice, split_ev, split_od]
    obtain ⟨a, ha⟩ := e (Machine.extendCoins (flipSplit t f).1)
    obtain ⟨b, hb⟩ := e (Machine.extendCoins (flipSplit t f).2)
    rw [ha,hb]
    cases a <;> cases b <;> decide
  let ft : P.twice.Losers x (t*2) ≃ P.Losers x t × P.Losers x t :=
    (Equiv.subtypeEquiv (p:=fun f => ¬P.twice.wins x (t*2) f)
      (q:=fun g : Flips t × Flips t =>
        (¬ P.wins x t g.1) ∧ (¬ P.wins x t g.2)) (flipSplit t) losses).trans
        (@Equiv.subtypeProdEquivProd _ _ (fun f => ¬P.wins x t f) (fun f => ¬P.wins x t f))
  rw [prob_losers, prob_losers, Fintype.card_congr ft, Fintype.card_prod,
    Nat.cast_mul, pow_mul]
  ring

end ExactDerandomization.Table.TM

end
