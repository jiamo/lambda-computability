import Start.LogspaceDeterministic

/-!
# One-sided error amplification in randomized logarithmic space: `RL ⊆ BPL`

This module is this library's own (it is not part of the upstream file absorbed as
`Start/LogspaceDeterministic.lean`).  It works in exactly the machine model of that file.

Given a randomized logarithmic-space machine `M`, the *two-trial machine* `M.twoTrial` runs two
copies of `M` side by side on disjoint work tapes and disjoint input heads, alternating steps:
at even times the first copy moves (reading the coin of that step), at odd times the second copy
moves.  It halts once both copies have halted and accepts iff one of them accepted.  If `M`
halts within `T` steps on every coin tape, the two-trial machine halts within `2 * T` steps, its
coin bits at even and odd positions are two independent coin tapes for the copies, and its
acceptance probability is `1 - (1 - p) ^ 2` where `p` is that of `M`.  Its work space is at most
twice that of `M`.

Consequences proved here:

* `RL_subset_BPL : RL ⊆ BPL`;
* `RL_subset_L_of_BPL_subset_L : BPL ⊆ L → RL ⊆ L`;
* `L_eq_RL_and_L_eq_BPL_of_BPL_subset_L : BPL ⊆ L → L = RL ∧ L = BPL`.

The remaining inclusion `BPL ⊆ L`, the main theorem of the paper "Exact Derandomization of
Logarithmic Space: L = RL = BPL", is proved unconditionally in `Start/LogspaceEquality.lean`
(absorbed from github.com/openai/math, commit 3014888, family 103), which uses
`RL_subset_BPL` from this module to conclude `L = RL ∧ RL = BPL`.
-/

namespace ExactDerandomization

namespace Machine

variable {q w h : ℕ}

/-- The action of `M` that leaves a configuration unchanged: same state, rewrite the scanned
bits, no head moves. -/
def idleAction (s : Fin (q + 1)) (bits : Fin w → Bool) : Action q w h where
  nextState := s
  write := bits
  workMove := fun _ => .stay
  inputMove := fun _ => .stay

/-- The action `M` takes in state `s`, idling once `s` is an output state. -/
def guardedAction (M : Machine q w h) (s : Fin (q + 1)) (inp : Fin h → InputSymbol)
    (bits : Fin w → Bool) (coin : Bool) : Action q w h :=
  match M.output s with
  | some _ => idleAction s bits
  | none => M.transition s inp bits coin

/-- Apply an action to a configuration. -/
def applyAction {n : ℕ} (c : Configuration q w h n) (a : Action q w h) :
    Configuration q w h n where
  state := a.nextState
  inputPos := fun j => (a.inputMove j).moveInput (c.inputPos j)
  workPos := fun k => (a.workMove k).move (c.workPos k)
  work := fun k => Function.update (c.work k) (c.workPos k) (a.write k)

theorem applyAction_idle {n : ℕ} (c : Configuration q w h n) :
    applyAction c (idleAction c.state (fun k => c.work k (c.workPos k))) = c := by
  cases c
  simp [applyAction, idleAction, Direction.move, Direction.moveInput]

theorem step_eq_applyAction (M : Machine q w h) (x : Word) (b : Bool)
    (c : Configuration q w h x.length) :
    M.step x b c = applyAction c (M.guardedAction c.state
      (fun j => readInput x (c.inputPos j)) (fun k => c.work k (c.workPos k)) b) := by
  unfold step guardedAction
  cases hout : M.output c.state with
  | some d => simp only; exact (applyAction_idle c).symm
  | none => rfl

/-! ### The two-trial machine -/

/-- State count of the two-trial machine (minus one). -/
def pairStates (q : ℕ) : ℕ := 2 * ((q + 1) * (q + 1)) - 1

/-- States of the two-trial machine: whose turn it is, and the two copies' states. -/
noncomputable def pairCode (q : ℕ) : Bool × Fin (q + 1) × Fin (q + 1) ≃ Fin (pairStates q + 1) :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, pairStates]
    have : 0 < (q + 1) * (q + 1) := by positivity
    omega)

/-- The two-trial machine. -/
noncomputable def twoTrial (M : Machine q w h) : Machine (pairStates q) (w + w) (h + h) where
  initialState := pairCode q (false, M.initialState, M.initialState)
  output s :=
    match M.output ((pairCode q).symm s).2.1, M.output ((pairCode q).symm s).2.2 with
    | some b₁, some b₂ => some (b₁ || b₂)
    | _, _ => none
  transition s inp bits coin :=
    let p := (pairCode q).symm s
    if p.1 = false then
      let a := M.guardedAction p.2.1 (fun j => inp (Fin.castAdd h j))
        (fun k => bits (Fin.castAdd w k)) coin
      { nextState := pairCode q (true, a.nextState, p.2.2)
        write := Fin.addCases a.write (fun k => bits (Fin.natAdd w k))
        workMove := Fin.addCases a.workMove (fun _ => .stay)
        inputMove := Fin.addCases a.inputMove (fun _ => .stay) }
    else
      let a := M.guardedAction p.2.2 (fun j => inp (Fin.natAdd h j))
        (fun k => bits (Fin.natAdd w k)) coin
      { nextState := pairCode q (false, p.2.1, a.nextState)
        write := Fin.addCases (fun k => bits (Fin.castAdd w k)) a.write
        workMove := Fin.addCases (fun _ => .stay) a.workMove
        inputMove := Fin.addCases (fun _ => .stay) a.inputMove }

/-- First copy of a two-trial configuration. -/
noncomputable def proj₁ {n : ℕ} (c : Configuration (pairStates q) (w + w) (h + h) n) :
    Configuration q w h n where
  state := ((pairCode q).symm c.state).2.1
  inputPos := fun j => c.inputPos (Fin.castAdd h j)
  workPos := fun k => c.workPos (Fin.castAdd w k)
  work := fun k => c.work (Fin.castAdd w k)

/-- Second copy of a two-trial configuration. -/
noncomputable def proj₂ {n : ℕ} (c : Configuration (pairStates q) (w + w) (h + h) n) :
    Configuration q w h n where
  state := ((pairCode q).symm c.state).2.2
  inputPos := fun j => c.inputPos (Fin.natAdd h j)
  workPos := fun k => c.workPos (Fin.natAdd w k)
  work := fun k => c.work (Fin.natAdd w k)

/-- Whose turn it is (`false`: first copy). -/
noncomputable def phase {n : ℕ} (c : Configuration (pairStates q) (w + w) (h + h) n) : Bool :=
  ((pairCode q).symm c.state).1

/-- Coins of the first copy: the even positions. -/
def evenCoins (coins : CoinTape) : CoinTape := fun i => coins (2 * i)

/-- Coins of the second copy: the odd positions. -/
def oddCoins (coins : CoinTape) : CoinTape := fun i => coins (2 * i + 1)

variable (M : Machine q w h)

theorem twoTrial_output_eq_some {s : Fin (pairStates q + 1)} {b : Bool} :
    M.twoTrial.output s = some b ↔ ∃ b₁ b₂, M.output ((pairCode q).symm s).2.1 = some b₁ ∧
      M.output ((pairCode q).symm s).2.2 = some b₂ ∧ b = (b₁ || b₂) := by
  unfold twoTrial
  dsimp only
  cases h₁ : M.output ((pairCode q).symm s).2.1 <;>
    cases h₂ : M.output ((pairCode q).symm s).2.2 <;> simp [eq_comm]

theorem twoTrial_output_eq_none {s : Fin (pairStates q + 1)} :
    M.twoTrial.output s = none ↔
      M.output ((pairCode q).symm s).2.1 = none ∨ M.output ((pairCode q).symm s).2.2 = none := by
  unfold twoTrial
  dsimp only
  cases h₁ : M.output ((pairCode q).symm s).2.1 <;>
    cases h₂ : M.output ((pairCode q).symm s).2.2 <;> simp

theorem step_first {x : Word} (b : Bool) (c : Configuration (pairStates q) (w + w) (h + h) x.length)
    (hout : M.twoTrial.output c.state = none) (hph : phase c = false) :
    proj₁ (M.twoTrial.step x b c) = M.step x b (proj₁ c) ∧
      proj₂ (M.twoTrial.step x b c) = proj₂ c ∧ phase (M.twoTrial.step x b c) = true := by
  have hstep : M.twoTrial.step x b c = applyAction c (M.twoTrial.transition c.state
      (fun j => readInput x (c.inputPos j)) (fun k => c.work k (c.workPos k)) b) := by
    unfold step; rw [hout]; rfl
  rw [hstep, step_eq_applyAction]
  simp only [phase] at hph
  refine ⟨?_, ?_, ?_⟩
  · simp [applyAction, twoTrial, hph, proj₁, Direction.move, Direction.moveInput, -Fin.natAdd_eq_addNat]
  · simp [applyAction, twoTrial, hph, proj₂, Direction.move, Direction.moveInput, -Fin.natAdd_eq_addNat]
  · simp [applyAction, twoTrial, hph, phase, Direction.move, Direction.moveInput, -Fin.natAdd_eq_addNat]

theorem step_second {x : Word} (b : Bool) (c : Configuration (pairStates q) (w + w) (h + h) x.length)
    (hout : M.twoTrial.output c.state = none) (hph : phase c = true) :
    proj₁ (M.twoTrial.step x b c) = proj₁ c ∧
      proj₂ (M.twoTrial.step x b c) = M.step x b (proj₂ c) ∧
        phase (M.twoTrial.step x b c) = false := by
  have hstep : M.twoTrial.step x b c = applyAction c (M.twoTrial.transition c.state
      (fun j => readInput x (c.inputPos j)) (fun k => c.work k (c.workPos k)) b) := by
    unfold step; rw [hout]; rfl
  rw [hstep, step_eq_applyAction]
  simp only [phase] at hph
  refine ⟨?_, ?_, ?_⟩
  · simp [applyAction, twoTrial, hph, proj₁, Direction.move, Direction.moveInput, -Fin.natAdd_eq_addNat]
  · simp [applyAction, twoTrial, hph, proj₂, Direction.move, Direction.moveInput, -Fin.natAdd_eq_addNat]
  · simp [applyAction, twoTrial, hph, phase, Direction.move, Direction.moveInput, -Fin.natAdd_eq_addNat]

theorem proj_initial (n : ℕ) :
    proj₁ (M.twoTrial.initial n) = M.initial n ∧ proj₂ (M.twoTrial.initial n) = M.initial n ∧
      phase (M.twoTrial.initial n) = false := by
  simp [proj₁, proj₂, phase, initial, twoTrial]

/-- The simulation invariant of the two-trial machine. -/
theorem twoTrial_run (x : Word) (coins : CoinTape) (t : ℕ) :
    (M.twoTrial.output (M.twoTrial.run x coins t).state = none →
        phase (M.twoTrial.run x coins t) = decide (t % 2 = 1)) ∧
      proj₁ (M.twoTrial.run x coins t) = M.run x (evenCoins coins) ((t + 1) / 2) ∧
      proj₂ (M.twoTrial.run x coins t) = M.run x (oddCoins coins) (t / 2) := by
  induction t with
  | zero =>
    obtain ⟨h₁, h₂, h₃⟩ := M.proj_initial x.length
    exact ⟨fun _ => by simpa using h₃, by simpa using h₁, by simpa using h₂⟩
  | succ t ih =>
    obtain ⟨hph, h₁, h₂⟩ := ih
    rw [run_succ]
    cases hP : M.twoTrial.output (M.twoTrial.run x coins t).state with
    | some d =>
      rw [step_eq_self_of_output hP]
      obtain ⟨b₁, b₂, hb₁, hb₂, -⟩ := (M.twoTrial_output_eq_some).1 hP
      have hb₁' : M.output (M.run x (evenCoins coins) ((t + 1) / 2)).state = some b₁ := by
        rw [← h₁]; exact hb₁
      have hb₂' : M.output (M.run x (oddCoins coins) (t / 2)).state = some b₂ := by
        rw [← h₂]; exact hb₂
      refine ⟨fun h => (by rw [hP] at h; cases h), ?_, ?_⟩
      · rw [h₁]; exact (run_later_of_output hb₁' (by omega)).symm
      · rw [h₂]; exact (run_later_of_output hb₂' (by omega)).symm
    | none =>
      have hph := hph hP
      rcases Nat.mod_two_eq_zero_or_one t with ht | ht
      · have hph' : phase (M.twoTrial.run x coins t) = false := by simpa [ht] using hph
        obtain ⟨k₁, k₂, k₃⟩ := M.step_first (coins t) _ hP hph'
        refine ⟨fun _ => by simpa [k₃] using (by omega : (t + 1) % 2 = 1), ?_, ?_⟩
        · rw [k₁, h₁]
          have e₁ : (t + 1) / 2 = t / 2 := by omega
          have e₂ : (t + 1 + 1) / 2 = t / 2 + 1 := by omega
          rw [e₁, e₂, run_succ]
          congr 1
          simp only [evenCoins]; congr 1; omega
        · rw [k₂, h₂]; congr 1; omega
      · have hph' : phase (M.twoTrial.run x coins t) = true := by simpa [ht] using hph
        obtain ⟨k₁, k₂, k₃⟩ := M.step_second (coins t) _ hP hph'
        refine ⟨fun _ => by simpa [k₃] using (by omega : (t + 1) % 2 = 0), ?_, ?_⟩
        · rw [k₁, h₁]; congr 1; omega
        · rw [k₂, h₂]
          have e₂ : (t + 1) / 2 = t / 2 + 1 := by omega
          rw [e₂, run_succ]
          congr 1
          simp only [oddCoins]; congr 1; omega

theorem twoTrial_haltsBy {x : Word} {T : ℕ} (hT : M.HaltsBy x T) :
    M.twoTrial.HaltsBy x (2 * T) := by
  intro coins
  obtain ⟨-, h₁, h₂⟩ := M.twoTrial_run x coins (2 * T)
  obtain ⟨b₁, hb₁⟩ := hT (evenCoins coins)
  obtain ⟨b₂, hb₂⟩ := hT (oddCoins coins)
  have e₁ : (2 * T + 1) / 2 = T := by omega
  have e₂ : 2 * T / 2 = T := by omega
  rw [e₁] at h₁
  rw [e₂] at h₂
  refine ⟨b₁ || b₂, (M.twoTrial_output_eq_some).2 ⟨b₁, b₂, ?_, ?_, rfl⟩⟩
  · change M.output (proj₁ (M.twoTrial.run x coins (2 * T))).state = some b₁
    rw [h₁]; exact hb₁
  · change M.output (proj₂ (M.twoTrial.run x coins (2 * T))).state = some b₂
    rw [h₂]; exact hb₂

theorem twoTrial_accepts_iff {x : Word} {T : ℕ} (hT : M.HaltsBy x T) (coins : CoinTape) :
    M.twoTrial.output (M.twoTrial.run x coins (2 * T)).state = some true ↔
      (M.output (M.run x (evenCoins coins) T).state = some true ∨
        M.output (M.run x (oddCoins coins) T).state = some true) := by
  obtain ⟨-, h₁, h₂⟩ := M.twoTrial_run x coins (2 * T)
  obtain ⟨b₁, hb₁⟩ := hT (evenCoins coins)
  obtain ⟨b₂, hb₂⟩ := hT (oddCoins coins)
  have e₁ : (2 * T + 1) / 2 = T := by omega
  have e₂ : 2 * T / 2 = T := by omega
  rw [e₁] at h₁
  rw [e₂] at h₂
  have k₁ : M.output ((pairCode q).symm (M.twoTrial.run x coins (2 * T)).state).2.1 = some b₁ := by
    change M.output (proj₁ (M.twoTrial.run x coins (2 * T))).state = some b₁
    rw [h₁]; exact hb₁
  have k₂ : M.output ((pairCode q).symm (M.twoTrial.run x coins (2 * T)).state).2.2 = some b₂ := by
    change M.output (proj₂ (M.twoTrial.run x coins (2 * T))).state = some b₂
    rw [h₂]; exact hb₂
  rw [M.twoTrial_output_eq_some, hb₁, hb₂]
  simp only [k₁, k₂, Option.some.injEq]
  constructor
  · rintro ⟨c₁, c₂, rfl, rfl, h⟩
    revert h; cases b₁ <;> cases b₂ <;> simp
  · intro h
    exact ⟨b₁, b₂, rfl, rfl, by revert h; cases b₁ <;> cases b₂ <;> simp⟩

/-- Splitting `2 * T` coin bits into the even-position and odd-position halves. -/
def splitBits (T : ℕ) : (Fin (2 * T) → Bool) ≃ (Fin T → Bool) × (Fin T → Bool) where
  toFun bits := (fun i => bits ⟨2 * i.val, by omega⟩, fun i => bits ⟨2 * i.val + 1, by omega⟩)
  invFun p j := if j.val % 2 = 0 then p.1 ⟨j.val / 2, by omega⟩ else p.2 ⟨j.val / 2, by omega⟩
  left_inv bits := by
    funext j
    by_cases hj : j.val % 2 = 0
    · simp only [hj, if_true]; exact congrArg _ (Fin.ext (by simp only; omega))
    · simp only [hj, if_false]; exact congrArg _ (Fin.ext (by simp only; omega))
  right_inv p := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp only
      rw [if_pos (by omega)]; exact congrArg _ (Fin.ext (by simp only; omega))
    · simp only
      rw [if_neg (by omega)]; exact congrArg _ (Fin.ext (by simp only; omega))

theorem run_evenCoins_extend {x : Word} {T : ℕ} (bits : Fin (2 * T) → Bool) :
    M.run x (evenCoins (extendCoins bits)) T = M.run x (extendCoins (splitBits T bits).1) T := by
  apply run_eq_of_prefix
  intro s hs
  simp [evenCoins, extendCoins, splitBits, hs, (by omega : 2 * s < 2 * T)]

theorem run_oddCoins_extend {x : Word} {T : ℕ} (bits : Fin (2 * T) → Bool) :
    M.run x (oddCoins (extendCoins bits)) T = M.run x (extendCoins (splitBits T bits).2) T := by
  apply run_eq_of_prefix
  intro s hs
  simp [oddCoins, extendCoins, splitBits, hs, (by omega : 2 * s + 1 < 2 * T)]

theorem twoTrial_acceptanceProbability {x : Word} {T : ℕ} (hT : M.HaltsBy x T) :
    M.twoTrial.acceptanceProbability x (2 * T) =
      1 - (1 - M.acceptanceProbability x T) ^ 2 := by
  classical
  set A : (Fin T → Bool) → Prop := fun u => M.output (M.run x (extendCoins u) T).state = some true
    with hA
  have hcard : (Finset.univ.filter (fun bits : Fin (2 * T) → Bool =>
      M.twoTrial.output (M.twoTrial.run x (extendCoins bits) (2 * T)).state = some true)).card =
      (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin T → Bool) => A p.1 ∨ A p.2)).card := by
    apply Finset.card_equiv (splitBits T)
    intro bits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [M.twoTrial_accepts_iff hT, run_evenCoins_extend, run_oddCoins_extend]
  set a := (Finset.univ.filter A).card with ha
  set b := (Finset.univ.filter (fun u => ¬ A u)).card with hb
  have hab : a + b = 2 ^ T := by
    rw [ha, hb, Finset.card_filter_add_card_filter_not]
    simp
  have hor : (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin T → Bool) => A p.1 ∨ A p.2)).card
      + b * b = 2 ^ T * 2 ^ T := by
    have hnot : (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin T → Bool) =>
        ¬ (A p.1 ∨ A p.2))).card = b * b := by
      have : (Finset.univ.filter (fun p : (Fin T → Bool) × (Fin T → Bool) =>
          ¬ (A p.1 ∨ A p.2))) =
          (Finset.univ.filter (fun u => ¬ A u)) ×ˢ (Finset.univ.filter (fun u => ¬ A u)) := by
        rw [← Finset.filter_product, Finset.univ_product_univ]
        simp only [not_or]
      rw [this, Finset.card_product]
    rw [← hnot, Finset.card_filter_add_card_filter_not]
    simp
  unfold acceptanceProbability
  rw [hcard]
  have ha' : (Finset.univ.filter (fun bits : Fin T → Bool =>
      M.output (M.run x (extendCoins bits) T).state = some true)).card = a := rfl
  rw [ha']
  have hq : ((Finset.univ.filter (fun p : (Fin T → Bool) × (Fin T → Bool) =>
      A p.1 ∨ A p.2)).card : ℚ) = 2 ^ T * 2 ^ T - (b : ℚ) * b := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hor
    push_cast at this
    linarith
  have hb' : (b : ℚ) = 2 ^ T - a := by
    have := congrArg (fun n : ℕ => (n : ℚ)) hab
    push_cast at this
    linarith
  rw [hq, hb']
  have h2 : (2 : ℚ) ^ T ≠ 0 := by positivity
  rw [show (2 : ℚ) ^ (2 * T) = 2 ^ T * 2 ^ T by rw [two_mul, pow_add]]
  field_simp

theorem twoTrial_spaceThrough (x : Word) (coins : CoinTape) (t : ℕ) :
    M.twoTrial.spaceThrough x coins t ≤
      M.spaceThrough x (evenCoins coins) t + M.spaceThrough x (oddCoins coins) t := by
  unfold spaceThrough
  rw [Fin.sum_univ_add]
  apply Nat.add_le_add
  · apply Finset.sum_le_sum
    intro k _
    apply Finset.card_le_card
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    have h₁ := (M.twoTrial_run x coins s).2.1
    have hk : (M.twoTrial.run x coins s).workPos (Fin.castAdd w k) =
        (M.run x (evenCoins coins) ((s + 1) / 2)).workPos k := by
      rw [← h₁]; rfl
    rw [hk]
    exact Finset.mem_image.mpr ⟨(s + 1) / 2, by simp at hs ⊢; omega, rfl⟩
  · apply Finset.sum_le_sum
    intro k _
    apply Finset.card_le_card
    intro z hz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hz
    have h₂ := (M.twoTrial_run x coins s).2.2
    have hk : (M.twoTrial.run x coins s).workPos (Fin.natAdd w k) =
        (M.run x (oddCoins coins) (s / 2)).workPos k := by
      rw [← h₂]; rfl
    rw [hk]
    exact Finset.mem_image.mpr ⟨s / 2, by simp at hs ⊢; omega, rfl⟩

theorem twoTrial_logSpace (hM : M.LogSpace) : M.twoTrial.LogSpace := by
  obtain ⟨c, hc, hs⟩ := hM
  refine ⟨2 * c, by omega, fun x coins t => ?_⟩
  have h₁ := hs x (evenCoins coins) t
  have h₂ := hs x (oddCoins coins) t
  have := M.twoTrial_spaceThrough x coins t
  nlinarith

end Machine

theorem RL_subset_BPL : RL ⊆ BPL := by
  intro A hA
  obtain ⟨q, w, h, M, hspace, c, k, hc, hx⟩ := hA
  refine ⟨_, _, _, M.twoTrial, M.twoTrial_logSpace hspace, 2 * c, k, by omega, fun x => ?_⟩
  obtain ⟨hhalt, hyes, hno⟩ := hx x
  have hclock : polynomialClock (2 * c) k x.length = 2 * polynomialClock c k x.length := by
    unfold polynomialClock; ring
  rw [hclock, M.twoTrial_acceptanceProbability hhalt]
  refine ⟨M.twoTrial_haltsBy hhalt, fun hxA => ?_, fun hxA => ?_⟩
  · have := two_trial_probability_gap (hyes hxA) (M.acceptanceProbability_le_one _ _)
    linarith
  · rw [hno hxA]; norm_num

theorem RL_subset_L_of_BPL_subset_L (h : BPL ⊆ L) : RL ⊆ L :=
  RL_subset_BPL.trans h

theorem L_eq_RL_and_L_eq_BPL_of_BPL_subset_L (h : BPL ⊆ L) : L = RL ∧ L = BPL :=
  ⟨Set.Subset.antisymm L_subset_RL (RL_subset_L_of_BPL_subset_L h),
    Set.Subset.antisymm L_subset_BPL h⟩

end ExactDerandomization
