import Start.SpaceProgDispatch
import Start.LogspaceDeterministic

/-!
# A two-sided work tape in a window, held in two registers

This library's own module (task `M27-LOGSPACE-TRANSFER`, reverse direction).  A two-sided tape
`g : ℤ → Bool` whose head `p` stays in the window `[-W, W]` is held in two registers of the track
layout: `lftOf g p W` — the cells `-W, …, p - 1` from left to right — and `rgtOf g p W` — the cells
`W, …, p` (so that the last bit is the cell under the head).  `Tracks.tapeOp` writes a bit under
the head and moves it, by moving one bit between the two registers; `Tracks.runs_tapeOp` is its
specification.
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace Tracks

open Prog

/-- The cells `a, a + 1, …, a + m - 1` of a two-sided tape. -/
def cells (g : ℤ → Bool) (a : ℤ) (m : ℕ) : List Bool :=
  (List.range m).map (fun i : ℕ => g (a + (i : ℤ)))

@[simp] theorem length_cells (g : ℤ → Bool) (a : ℤ) (m : ℕ) : (cells g a m).length = m := by
  simp [cells]

theorem cells_succ_right (g : ℤ → Bool) (a : ℤ) (m : ℕ) :
    cells g a (m + 1) = cells g a m ++ [g (a + m)] := by
  simp [cells, List.range_succ]

theorem cells_succ_left (g : ℤ → Bool) (a : ℤ) (m : ℕ) :
    cells g a (m + 1) = g a :: cells g (a + 1) m := by
  induction m with
  | zero => simp [cells]
  | succ m ih =>
      rw [cells_succ_right, ih, cells_succ_right, List.cons_append]
      congr 3; push_cast; ring

theorem cells_congr {g g' : ℤ → Bool} {a : ℤ} {m : ℕ}
    (h : ∀ i : ℕ, i < m → g (a + i) = g' (a + i)) : cells g a m = cells g' a m := by
  unfold cells
  exact List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))

/-- The cells left of the head, inside the window. -/
def lftOf (g : ℤ → Bool) (p W : ℤ) : List Bool := cells g (-W) (p + W).toNat

/-- The cells from the right end of the window down to the head. -/
def rgtOf (g : ℤ → Bool) (p W : ℤ) : List Bool := (cells g p (W - p + 1).toNat).reverse

theorem length_lftOf (g : ℤ → Bool) (p W : ℤ) : (lftOf g p W).length = (p + W).toNat := by
  simp [lftOf]

theorem length_rgtOf (g : ℤ → Bool) (p W : ℤ) : (rgtOf g p W).length = (W - p + 1).toNat := by
  simp [rgtOf]

theorem rgtOf_eq (g : ℤ → Bool) (p W : ℤ) (hp : p ≤ W) :
    rgtOf g p W = rgtOf g (p + 1) W ++ [g p] := by
  unfold rgtOf
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (W - p + 1).toNat = m + 1 := ⟨(W - p).toNat, by omega⟩
  rw [hm, cells_succ_left, List.reverse_cons, show (W - (p + 1) + 1).toNat = m by omega]

theorem rgtOf_ne_nil (g : ℤ → Bool) (p W : ℤ) (hp : p ≤ W) : rgtOf g p W ≠ [] := by
  rw [rgtOf_eq g p W hp]; simp

theorem rgtOf_getLast (g : ℤ → Bool) (p W : ℤ) (hp : p ≤ W) :
    (rgtOf g p W).getLast (rgtOf_ne_nil g p W hp) = g p := by
  simp only [rgtOf_eq g p W hp, List.getLast_append_singleton]

theorem rgtOf_dropLast (g : ℤ → Bool) (p W : ℤ) (hp : p ≤ W) :
    (rgtOf g p W).dropLast = rgtOf g (p + 1) W := by
  rw [rgtOf_eq g p W hp, List.dropLast_concat]

theorem lftOf_succ (g : ℤ → Bool) (p W : ℤ) (hp : -W ≤ p) :
    lftOf g (p + 1) W = lftOf g p W ++ [g p] := by
  unfold lftOf
  rw [show (p + 1 + W).toNat = (p + W).toNat + 1 by omega, cells_succ_right]
  congr 3; omega

theorem lftOf_ne_nil (g : ℤ → Bool) (p W : ℤ) (hp : -W < p) : lftOf g p W ≠ [] := by
  have := lftOf_succ g (p - 1) W (by omega)
  rw [sub_add_cancel] at this
  rw [this]; simp

theorem lftOf_getLast (g : ℤ → Bool) (p W : ℤ) (hp : -W < p) :
    (lftOf g p W).getLast (lftOf_ne_nil g p W hp) = g (p - 1) := by
  have := lftOf_succ g (p - 1) W (by omega)
  rw [sub_add_cancel] at this
  simp only [this, List.getLast_append_singleton]

theorem lftOf_dropLast (g : ℤ → Bool) (p W : ℤ) (hp : -W < p) :
    (lftOf g p W).dropLast = lftOf g (p - 1) W := by
  have := lftOf_succ g (p - 1) W (by omega)
  rw [sub_add_cancel] at this
  rw [this, List.dropLast_concat]

theorem lftOf_update (g : ℤ → Bool) (p W : ℤ) (b : Bool) :
    lftOf (Function.update g p b) p W = lftOf g p W := by
  unfold lftOf
  apply cells_congr
  intro i hi
  rw [Function.update_of_ne]
  omega

theorem rgtOf_update (g : ℤ → Bool) (p W : ℤ) (b : Bool) (hp : p ≤ W) :
    rgtOf (Function.update g p b) p W = (rgtOf g p W).dropLast ++ [b] := by
  rw [rgtOf_eq _ p W hp, rgtOf_dropLast g p W hp, Function.update_self]
  congr 1
  unfold rgtOf
  congr 1
  apply cells_congr
  intro i _
  rw [Function.update_of_ne]
  omega

/-! ### The tape operation -/

variable {x : List Bool} {B : ℕ} {K : ℕ}

/-- Overwrite the last bit of register `r` with `b`. -/
def writeTop (K r : ℕ) (b : Bool) : Prog := popBranch K r (append K r b) (append K r b)

/-- Move the head of the tape held in registers `l`, `r`. -/
def moveTape (K l r : ℕ) : ExactDerandomization.Direction → Prog
  | .right => popBranch K r (append K l false) (append K l true)
  | .left => popBranch K l (append K r false) (append K r true)
  | .stay => skip

/-- Write `b` under the head of the tape held in registers `l`, `r`, then move it by `d`. -/
def tapeOp (K l r : ℕ) (b : Bool) (d : ExactDerandomization.Direction) : Prog :=
  .seq (writeTop K r b) (moveTape K l r d)

theorem runs_writeTop (R : ℕ → List Bool) (r : ℕ) (hr : r < K) (hne : R r ≠ []) (b : Bool)
    (N : ℕ) (hN : (R r).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (writeTop K r b) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R r ((R r).dropLast ++ [b])), 0, i⟩ := by
  refine runs_popBranch R r hr hne N hN hB i _ _ _ ?_
  have := List.length_pos_of_ne_nil hne
  have h := runs_append (x := x) (B := B) (Function.update R r (R r).dropLast) r hr b N
    (by simp; omega) hB i
  simp only [Function.update_self, Function.update_idem] at h
  split <;> exact h

theorem runs_tapeOp (R : ℕ → List Bool) (l r : ℕ) (hl : l < K) (hr : r < K) (hlr : l ≠ r)
    (g : ℤ → Bool) (p W : ℤ) (hRl : R l = lftOf g p W) (hRr : R r = rgtOf g p W)
    (b : Bool) (d : ExactDerandomization.Direction) (hp : -W ≤ p ∧ p ≤ W)
    (hp' : -W ≤ d.move p ∧ d.move p ≤ W) (N : ℕ) (hN : (2 * W + 1).toNat ≤ N)
    (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (tapeOp K l r b d) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update (Function.update R l (lftOf (Function.update g p b) (d.move p) W))
        r (rgtOf (Function.update g p b) (d.move p) W)), 0, i⟩ := by
  have hlenR : (R r).length = (W - p + 1).toNat := by rw [hRr, length_rgtOf]
  have hlenL : (R l).length = (p + W).toNat := by rw [hRl, length_lftOf]
  refine (runs_writeTop R r hr (by rw [hRr]; exact rgtOf_ne_nil g p W hp.2) b N
    (by omega) hB i).seq ?_
  set g' := Function.update g p b with hg'
  have hw : (R r).dropLast ++ [b] = rgtOf g' p W := by rw [hRr, hg', rgtOf_update g p W b hp.2]
  rw [hw]
  set R₁ := Function.update R r (rgtOf g' p W) with hR₁
  have h1l : R₁ l = lftOf g' p W := by
    rw [hR₁, Function.update_of_ne hlr, hRl, hg', lftOf_update]
  have h1r : R₁ r = rgtOf g' p W := by rw [hR₁, Function.update_self]
  cases d with
  | stay =>
      refine (runs_skip _ 0 i).of_eq rfl ?_
      simp only [ExactDerandomization.Direction.move]
      rw [← h1l, hR₁, Function.update_of_ne hlr, Function.update_eq_self]
  | right =>
      simp only [ExactDerandomization.Direction.move] at hp' ⊢
      refine runs_popBranch R₁ r hr (by rw [h1r]; exact rgtOf_ne_nil g' p W hp.2) N
        (by rw [h1r, length_rgtOf]; omega) hB i _ _ _ ?_
      have hlast : (R₁ r).getLast (by rw [h1r]; exact rgtOf_ne_nil g' p W hp.2) = g' p := by
        simp only [h1r]; exact rgtOf_getLast g' p W hp.2
      have hdl : (R₁ r).dropLast = rgtOf g' (p + 1) W := by
        rw [h1r, rgtOf_dropLast g' p W hp.2]
      rw [hlast, hdl]
      have h := runs_append (x := x) (B := B) (Function.update R₁ r (rgtOf g' (p + 1) W)) l hl
        (g' p) N (by rw [Function.update_of_ne hlr, h1l, length_lftOf]; omega) hB i
      rw [Function.update_of_ne hlr, h1l, ← lftOf_succ g' p W hp.1] at h
      have heq : Function.update (Function.update R₁ r (rgtOf g' (p + 1) W)) l
          (lftOf g' (p + 1) W) = Function.update (Function.update R l (lftOf g' (p + 1) W)) r
            (rgtOf g' (p + 1) W) := by
        rw [hR₁, Function.update_idem, Function.update_comm hlr.symm]
      rw [heq] at h
      cases hgp : g' p
      · rw [hgp] at h; exact h
      · rw [hgp] at h; exact h
  | left =>
      simp only [ExactDerandomization.Direction.move] at hp' ⊢
      refine runs_popBranch R₁ l hl (by rw [h1l]; exact lftOf_ne_nil g' p W (by omega)) N
        (by rw [h1l, length_lftOf]; omega) hB i _ _ _ ?_
      have hlast : (R₁ l).getLast (by rw [h1l]; exact lftOf_ne_nil g' p W (by omega)) =
          g' (p - 1) := by
        simp only [h1l]; exact lftOf_getLast g' p W (by omega)
      have hdl : (R₁ l).dropLast = lftOf g' (p - 1) W := by
        rw [h1l, lftOf_dropLast g' p W (by omega)]
      rw [hlast, hdl]
      have h := runs_append (x := x) (B := B) (Function.update R₁ l (lftOf g' (p - 1) W)) r hr
        (g' (p - 1)) N (by rw [Function.update_of_ne hlr.symm, h1r, length_rgtOf]; omega) hB i
      have hre : rgtOf g' p W ++ [g' (p - 1)] = rgtOf g' (p - 1) W := by
        rw [rgtOf_eq g' (p - 1) W (by omega), sub_add_cancel]
      rw [Function.update_of_ne hlr.symm, h1r, hre] at h
      have heq : Function.update (Function.update R₁ l (lftOf g' (p - 1) W)) r
          (rgtOf g' (p - 1) W) = Function.update (Function.update R l (lftOf g' (p - 1) W)) r
            (rgtOf g' (p - 1) W) := by
        rw [hR₁, Function.update_comm hlr.symm, Function.update_idem]
      rw [heq] at h
      cases hgp : g' (p - 1)
      · rw [hgp] at h; exact h
      · rw [hgp] at h; exact h

end Tracks

end Complexity.Space
