/-
**Register operations on the track layout, as tape programs with exact-state specifications.**

On top of `Start/SpaceProgLib.lean`: with the work tape laid out in `K` tracks
(`Complexity.Space.Tracks.lay K R` for a register file `R : ℕ → Word`), this module programs and
specifies the operations a compiler needs on registers.  Every operation starts and ends with the
work head on cell `0` (*home*), leaves the input head alone (except `copyInput`), and is specified
by `Complexity.Space.Prog.Runs` from `lay K R` to `lay K R'`:

* `goHome` — return to cell `0` from anywhere, by the ruler;
* `clear j` — `R j := []`;
* `copyOff a d δ` — write `R a` into track `d` from block `δ` on (`δ = 0`: copy);
* `assign a d` — `R d := R a`;
* `prepend j s β` — `R j := β :: R j`, with the scratch track `s`;
* `append j β` — `R j := R j ++ [β]`;
* `truncate w l` — `R w := (R w).take (R l).length`;
* `popBranch j p₀ p₁` — remove the last bit `β` of `R j` and continue with `p_β`;
* `whileNE j body` — repeat `body` while `R j` is non-empty;
* `copyInput j` — `R j := x`, the input word.

The space used is at most `(N + 3) (2K + 1)` cells when every register involved has length at
most `N`.
-/

import Mathlib
import Start.SpaceProgLib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace Tracks

open Prog

/-- The presence bits of a word on a track. -/
def presOf (w : List Bool) (b : ℕ) : Bool := decide (b < w.length)

/-- The value bits of a word on a track. -/
def valOf (w : List Bool) (b : ℕ) : Bool := w.getD b false

theorem lay_eq (K : ℕ) (R : ℕ → List Bool) :
    lay K R = mk K (fun j => presOf (R j)) (fun j => valOf (R j)) := rfl

theorem lay_update (K : ℕ) (R : ℕ → List Bool) (j : ℕ) (w : List Bool) :
    lay K (Function.update R j w) =
      mk K (Function.update (fun j => presOf (R j)) j (presOf w))
        (Function.update (fun j => valOf (R j)) j (valOf w)) := by
  rw [lay_eq]
  congr 1 <;> funext j' <;> by_cases h : j' = j <;> simp [h]

theorem lay_split (K : ℕ) (R : ℕ → List Bool) (j : ℕ) :
    lay K R = mk K (Function.update (fun j => presOf (R j)) j (presOf (R j)))
        (Function.update (fun j => valOf (R j)) j (valOf (R j))) := by
  rw [← lay_update, Function.update_eq_self]

theorem update_mk_pres' (K : ℕ) (P V : ℕ → ℕ → Bool) (f : ℕ → Bool) (b j : ℕ) (hj : j < K)
    (β : Bool) :
    Function.update (mk K (Function.update P j f) V) (b * wd K + (2 * j + 1)) β =
      mk K (Function.update P j (Function.update f b β)) V := by
  rw [update_mk_pres _ _ _ _ _ hj]; simp

theorem update_mk_val' (K : ℕ) (P V : ℕ → ℕ → Bool) (f : ℕ → Bool) (b j : ℕ) (hj : j < K)
    (β : Bool) :
    Function.update (mk K P (Function.update V j f)) (b * wd K + (2 * j + 2)) β =
      mk K P (Function.update V j (Function.update f b β)) := by
  rw [update_mk_val _ _ _ _ _ hj]; simp

theorem presOf_nil : presOf [] = fun _ => false := by funext b; simp [presOf]

theorem valOf_nil : valOf [] = fun _ => false := by funext b; simp [valOf]

theorem valOf_ge {w : List Bool} {b : ℕ} (h : w.length ≤ b) : valOf w b = false := by
  simp [valOf, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-- Positions inside the first `N + 2` blocks are within the bound. -/
theorem blk_lt {k N w B o : ℕ} (hk : k ≤ N + 1) (ho : o < w) (hB : (N + 3) * w ≤ B) :
    k * w + w + o < B := by
  have : (k + 2) * w ≤ (N + 3) * w := Nat.mul_le_mul_right _ (by omega)
  nlinarith

theorem succ_blk (k w o : ℕ) : (k + 1) * w + o = k * w + (w + o) := by ring

variable {x : List Bool} {B : ℕ} {K : ℕ}

/-! ### Writing on a track -/

theorem runs_wP (P V : ℕ → ℕ → Bool) (f : ℕ → Bool) (b j : ℕ) (hj : j < K) (β : Bool) (i : ℕ) :
    Runs x B (write β) ⟨mk K (Function.update P j f) V, b * wd K + (2 * j + 1), i⟩
      ⟨mk K (Function.update P j (Function.update f b β)) V, b * wd K + (2 * j + 1), i⟩ :=
  (runs_write β _ _ i).of_eq rfl (by rw [update_mk_pres' _ _ _ _ _ _ hj])

theorem runs_wV (P V : ℕ → ℕ → Bool) (f : ℕ → Bool) (b j : ℕ) (hj : j < K) (β : Bool) (i : ℕ) :
    Runs x B (write β) ⟨mk K P (Function.update V j f), b * wd K + (2 * j + 2), i⟩
      ⟨mk K P (Function.update V j (Function.update f b β)), b * wd K + (2 * j + 2), i⟩ :=
  (runs_write β _ _ i).of_eq rfl (by rw [update_mk_val' _ _ _ _ _ _ hj])

/-! ### Returning home -/

/-- Return to cell `0`: move to the ruler cell of the current block, then block by block to the
left until the ruler is set. -/
def goHome (K o : ℕ) : Prog := .seq (mvL o) (.loop (fun _ w => !w) (mvL (wd K)))

theorem runs_goHome (P V : ℕ → ℕ → Bool) (b o i : ℕ) :
    Runs x B (goHome K o) ⟨mk K P V, b * wd K + o, i⟩ ⟨mk K P V, 0, i⟩ := by
  refine (runs_mvL o _ _ i).seq ?_
  refine (Runs.loop_stages (fun k => ⟨mk K P V, (b - k) * wd K, i⟩) b ?_ ?_).of_eq
    (by simp) (by simp)
  · intro k hk
    simp only [mk_ruler]
    by_cases h : k < b
    · simp [h]; omega
    · simp [h]; omega
  · intro k hk
    refine (runs_mvL _ _ _ i).of_eq rfl ?_
    congr 1
    rw [Nat.sub_mul, Nat.sub_mul, Nat.sub_sub, add_mul, one_mul]

/-! ### Clearing a track -/

/-- Clear the cell of track `j` under the head (at its presence bit) and move to the next
block. -/
def clrBody (K : ℕ) : Prog :=
  .seq (write false) (.seq (wmove .right) (.seq (write false) (mvR (2 * K))))

/-- `R j := []`. -/
def clear (K j : ℕ) : Prog :=
  .seq (mvR (2 * j + 1)) (.seq (.loop (fun _ w => w) (clrBody K)) (goHome K (2 * j + 1)))

theorem runs_clear (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (N : ℕ) (hN : (R j).length ≤ N)
    (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (clear K j) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R j []), 0, i⟩ := by
  obtain ⟨L, hL⟩ : ∃ L, L = (R j).length := ⟨_, rfl⟩
  let P0 : ℕ → ℕ → Bool := fun j => presOf (R j)
  let V0 : ℕ → ℕ → Bool := fun j => valOf (R j)
  let f : ℕ → ℕ → Bool := fun k b => decide (k ≤ b ∧ b < L)
  let g : ℕ → ℕ → Bool := fun k b => if b < k then false else valOf (R j) b
  let stage : ℕ → TState := fun k =>
    ⟨mk K (Function.update P0 j (f k)) (Function.update V0 j (g k)), k * wd K + (2 * j + 1), i⟩
  have h0 : mk K (Function.update P0 j (f 0)) (Function.update V0 j (g 0)) = lay K R := by
    rw [lay_split K R j]
    congr 2; funext b; simp [f, presOf, hL]
  have hLv : mk K (Function.update P0 j (f L)) (Function.update V0 j (g L)) =
      lay K (Function.update R j []) := by
    rw [lay_update, presOf_nil, valOf_nil]
    congr 2 <;> funext b
    · simp [f]
    · simp only [g]; split_ifs with h <;> first | rfl | exact valOf_ge (by omega)
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * j + 1) (by omega) (by womega) hB
  refine (runs_mvR _ _ 0 i (by omega)).seq ?_
  refine Runs.seq ?_ ((runs_goHome (x := x) (B := B) _ _ L (2 * j + 1) i).of_eq rfl
    (by rw [hLv]))
  refine (Runs.loop_stages stage L ?_ ?_).of_eq (by simp [stage, h0]) rfl
  · intro k hk
    simp only [stage, mk_pres _ _ _ _ _ hj, Function.update_self, f]
    by_cases h : k < L <;> simp [h]
  · intro k hk
    have hpos := blk_lt (k := k) (N := N) (o := 2 * j + 1) (by omega) (by womega) hB
    refine (runs_wP _ _ _ k j hj false i).seq ?_
    refine (runs_wmoveR _ _ i (by womega)).seq ?_
    refine Runs.seq ((runs_wV _ _ _ k j hj false i).of_eq rfl rfl) ?_
    refine (runs_mvR (2 * K) _ _ i (by womega)).of_eq rfl ?_
    simp only [stage]
    congr 1
    · congr 2 <;> funext b <;> simp only [Function.update_apply, f, g] <;> bool_omega
    · simp only [wd]; ring

/-! ### Copying a track, possibly shifted -/

/-- Write the bit `β` into track `d` at the block `δ` further on, then move to the presence bit
of track `a` in the next block.  (Starts at the value bit of track `a`.) -/
def cpBit (K a d δ : ℕ) (β : Bool) : Prog :=
  .seq (moveTo (2 * a + 2) (δ * wd K + (2 * d + 1))) (.seq (write true) (.seq (wmove .right)
    (.seq (write β) (moveTo (δ * wd K + (2 * d + 2)) (wd K + (2 * a + 1))))))

/-- One block of `copyOff`. -/
def cpBody (K a d δ : ℕ) : Prog :=
  .seq (wmove .right) (.ite (fun _ w => w) (cpBit K a d δ true) (cpBit K a d δ false))

/-- Write `R a` into the (empty) track `d`, starting at block `δ`. -/
def copyOff (K a d δ : ℕ) : Prog :=
  .seq (mvR (2 * a + 1)) (.seq (.loop (fun _ w => w) (cpBody K a d δ)) (goHome K (2 * a + 1)))

theorem runs_copyOff (R : ℕ → List Bool) (a d δ : ℕ) (ha : a < K) (hd : d < K) (hne : a ≠ d)
    (hRd : R d = []) (hδ : δ ≤ 1) (N : ℕ) (hN : (R a).length ≤ N)
    (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (copyOff K a d δ) ⟨lay K R, 0, i⟩
      ⟨mk K (Function.update (fun j => presOf (R j)) d
          (fun b => decide (δ ≤ b ∧ b < (R a).length + δ)))
        (Function.update (fun j => valOf (R j)) d
          (fun b => if δ ≤ b ∧ b < (R a).length + δ then valOf (R a) (b - δ) else false)),
        0, i⟩ := by
  obtain ⟨L, hL⟩ : ∃ L, L = (R a).length := ⟨_, rfl⟩
  rw [← hL]
  let P0 : ℕ → ℕ → Bool := fun j => presOf (R j)
  let V0 : ℕ → ℕ → Bool := fun j => valOf (R j)
  let f : ℕ → ℕ → Bool := fun k b => decide (δ ≤ b ∧ b < k + δ)
  let g : ℕ → ℕ → Bool := fun k b => if δ ≤ b ∧ b < k + δ then valOf (R a) (b - δ) else false
  let stage : ℕ → TState := fun k =>
    ⟨mk K (Function.update P0 d (f k)) (Function.update V0 d (g k)), k * wd K + (2 * a + 1), i⟩
  have h0 : mk K (Function.update P0 d (f 0)) (Function.update V0 d (g 0)) = lay K R := by
    rw [lay_split K R d, hRd, presOf_nil, valOf_nil]
    congr 2 <;> funext b <;> simp only [f, g] <;> bool_omega
  have hδw : δ * wd K ≤ wd K := by
    calc δ * wd K ≤ 1 * wd K := Nat.mul_le_mul_right _ hδ
      _ = wd K := one_mul _
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * a + 1) (by omega) (by womega) hB
  refine (runs_mvR _ _ 0 i (by omega)).seq ?_
  refine Runs.seq ?_ ((runs_goHome (x := x) (B := B) _ _ L (2 * a + 1) i).of_eq rfl rfl)
  refine (Runs.loop_stages stage L ?_ ?_).of_eq (by simp [stage, h0]) rfl
  · intro k hk
    simp only [stage, mk_pres _ _ _ _ _ ha, Function.update_of_ne hne, P0, presOf, hL]
  · intro k hk
    have hpos := blk_lt (k := k) (N := N) (o := 2 * K) (by omega) (by womega) hB
    have hcp : ∀ β, β = valOf (R a) k →
        Runs x B (cpBit K a d δ β)
          ⟨mk K (Function.update P0 d (f k)) (Function.update V0 d (g k)),
            k * wd K + (2 * a + 2), i⟩
          (stage (k + 1)) := by
      intro β hβ
      refine (runs_moveTo _ _ _ (k * wd K) i (by womega)).seq ?_
      refine Runs.seq ((runs_wP (x := x) (B := B) _ _ _ (k + δ) d hd true i).of_eq
        (by congr 1; ring) rfl) ?_
      refine (runs_wmoveR _ _ i (by
        have : (k + δ) * wd K = k * wd K + δ * wd K := by ring
        womega)).seq ?_
      refine Runs.seq ((runs_wV (x := x) (B := B) _ _ _ (k + δ) d hd β i).of_eq rfl rfl) ?_
      refine ((runs_moveTo _ _ _ (k * wd K) i (by womega)).of_eq (by congr 1; ring) ?_)
      simp only [stage]
      congr 1
      · congr 2 <;> funext b
        · simp only [Function.update_apply, f]; bool_omega
        · simp only [Function.update_apply, g]
          by_cases hb : b = k + δ
          · subst hb; simp [hβ]
          · rw [if_neg hb]; bool_omega
      · simp only [wd]; ring
    refine (runs_wmoveR _ _ i (by womega)).seq ?_
    have hv : (mk K (Function.update P0 d (f k)) (Function.update V0 d (g k)))
        (k * wd K + (2 * a + 1) + 1) = valOf (R a) k := by
      rw [show k * wd K + (2 * a + 1) + 1 = k * wd K + (2 * a + 2) by ring, mk_val _ _ _ _ _ ha,
        Function.update_of_ne hne]
    refine Runs.ite (fun ht => ?_) (fun ht => ?_)
    · exact (hcp true (by rw [← hv]; exact ht.symm)).of_eq (by congr 1) rfl
    · exact (hcp false (by rw [← hv]; exact ht.symm)).of_eq (by congr 1) rfl

/-- `R d := R a`, for an empty track `d`. -/
theorem runs_copy (R : ℕ → List Bool) (a d : ℕ) (ha : a < K) (hd : d < K) (hne : a ≠ d)
    (hRd : R d = []) (N : ℕ) (hN : (R a).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (copyOff K a d 0) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R d (R a)), 0, i⟩ := by
  refine (runs_copyOff R a d 0 ha hd hne hRd zero_le_one N hN hB i).of_eq rfl ?_
  rw [lay_update]
  congr 3 <;> funext b
  · simp [presOf]
  · simp only [zero_le, true_and, add_zero, Nat.sub_zero]
    split_ifs with h
    · rfl
    · exact (valOf_ge (by omega)).symm

/-- `R d := R a`. -/
def assign (K a d : ℕ) : Prog := .seq (clear K d) (copyOff K a d 0)

theorem runs_assign (R : ℕ → List Bool) (a d : ℕ) (ha : a < K) (hd : d < K) (hne : a ≠ d)
    (N : ℕ) (hNa : (R a).length ≤ N) (hNd : (R d).length ≤ N) (hB : (N + 3) * wd K ≤ B)
    (i : ℕ) :
    Runs x B (assign K a d) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R d (R a)), 0, i⟩ := by
  refine (runs_clear R d hd N hNd hB i).seq ?_
  have := runs_copy (x := x) (Function.update R d []) a d ha hd hne (by simp) N
    (by rw [Function.update_of_ne hne]; exact hNa) hB i
  rw [Function.update_idem, Function.update_of_ne hne] at this
  exact this

/-! ### Finding the end of a track -/

/-- Move from home to the presence bit of track `j` in the first block where it is unset. -/
def seekEnd (K j : ℕ) : Prog := .seq (mvR (2 * j + 1)) (.loop (fun _ w => w) (mvR (wd K)))

theorem runs_seekEnd (v : ℕ → Bool) (j L : ℕ)
    (hv : ∀ k, v (k * wd K + (2 * j + 1)) = decide (k < L))
    (hj : j < K) (N : ℕ) (hL : L ≤ N + 1) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (seekEnd K j) ⟨v, 0, i⟩ ⟨v, L * wd K + (2 * j + 1), i⟩ := by
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * j + 1) (by omega) (by womega) hB
  refine (runs_mvR _ _ 0 i (by omega)).seq ?_
  refine (Runs.loop_stages (fun k => ⟨v, k * wd K + (2 * j + 1), i⟩) L ?_ ?_).of_eq
    (by simp) rfl
  · intro k hk; exact hv k
  · intro k hk
    have hpos := blk_lt (k := k) (N := N) (o := 2 * j + 1) (by omega) (by womega) hB
    exact (runs_mvR _ _ _ i (by omega)).of_eq rfl (by congr 1; ring)

theorem lay_pres (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (k : ℕ) :
    lay K R (k * wd K + (2 * j + 1)) = decide (k < (R j).length) := by
  rw [lay_eq, mk_pres _ _ _ _ _ hj]; rfl

theorem lay_val (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (k : ℕ) :
    lay K R (k * wd K + (2 * j + 2)) = valOf (R j) k := by
  rw [lay_eq, mk_val _ _ _ _ _ hj]

/-! ### Appending a bit -/

theorem presOf_concat (w : List Bool) (β : Bool) :
    Function.update (presOf w) w.length true = presOf (w ++ [β]) := by
  funext b; simp only [Function.update_apply, presOf, List.length_append, List.length_singleton]
  bool_omega

theorem valOf_concat (w : List Bool) (β : Bool) :
    Function.update (valOf w) w.length β = valOf (w ++ [β]) := by
  funext b
  simp only [Function.update_apply, valOf]
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · rw [List.getD_append _ _ _ _ h]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-- `R j := R j ++ [β]`. -/
def append (K j : ℕ) (β : Bool) : Prog :=
  .seq (seekEnd K j) (.seq (write true) (.seq (wmove .right)
    (.seq (write β) (goHome K (2 * j + 2)))))

theorem runs_append (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (β : Bool) (N : ℕ)
    (hN : (R j).length + 1 ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (append K j β) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R j (R j ++ [β])), 0, i⟩ := by
  have hpos := blk_lt (k := (R j).length) (N := N) (o := 2 * j + 2) (by omega) (by womega) hB
  refine (runs_seekEnd _ j (R j).length (lay_pres R j hj) hj N (by omega) hB i).seq ?_
  rw [lay_split K R j]
  refine (runs_wP _ _ _ _ j hj true i).seq ?_
  refine (runs_wmoveR _ _ i (by womega)).seq ?_
  refine Runs.seq ((runs_wV _ _ _ _ j hj β i).of_eq rfl rfl) ?_
  refine (runs_goHome _ _ _ _ i).of_eq rfl ?_
  rw [lay_update, presOf_concat, valOf_concat]

/-! ### Removing the last bit -/

theorem presOf_dropLast (w : List Bool) :
    Function.update (presOf w) (w.length - 1) false = presOf w.dropLast := by
  funext b; simp only [Function.update_apply, presOf, List.length_dropLast]
  bool_omega

theorem valOf_dropLast (w : List Bool) :
    Function.update (valOf w) (w.length - 1) false = valOf w.dropLast := by
  funext b
  simp only [Function.update_apply, valOf]
  split_ifs with h
  · rw [List.getD_eq_default _ _ (by simp; omega)]
  · by_cases hb : b < w.length - 1
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_dropLast,
        if_pos hb]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem valOf_last (w : List Bool) (h : w ≠ []) : valOf w (w.length - 1) = w.getLast h := by
  have hl : 0 < w.length := List.length_pos_of_ne_nil h
  rw [valOf, List.getD_eq_getElem _ _ (by omega), List.getLast_eq_getElem]

/-- Clear the last cell of track `j` (starting at its value bit) and return home. -/
def popTail (K j : ℕ) : Prog :=
  .seq (write false) (.seq (wmove .left) (.seq (write false) (goHome K (2 * j + 1))))

/-- Remove the last bit `β` of `R j`, then run `p₀` or `p₁` according to `β`. -/
def popBranch (K j : ℕ) (p₀ p₁ : Prog) : Prog :=
  .seq (seekEnd K j) (.seq (moveTo (wd K + (2 * j + 1)) (2 * j + 2))
    (.ite (fun _ w => w) (.seq (popTail K j) p₁) (.seq (popTail K j) p₀)))

theorem runs_popBranch (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (hne : R j ≠ []) (N : ℕ)
    (hN : (R j).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) (p₀ p₁ : Prog) (s' : TState)
    (hp : Runs x B (if (R j).getLast hne then p₁ else p₀)
      ⟨lay K (Function.update R j (R j).dropLast), 0, i⟩ s') :
    Runs x B (popBranch K j p₀ p₁) ⟨lay K R, 0, i⟩ s' := by
  have hl : 0 < (R j).length := List.length_pos_of_ne_nil hne
  obtain ⟨m, hm⟩ : ∃ m, (R j).length = m + 1 := ⟨(R j).length - 1, by omega⟩
  have hpos := blk_lt (k := m) (N := N) (o := 2 * j + 2) (by omega) (by womega) hB
  refine (runs_seekEnd _ j (R j).length (lay_pres R j hj) hj N (by omega) hB i).seq ?_
  rw [hm]
  refine Runs.seq ((runs_moveTo _ _ _ (m * wd K) i (by womega)).of_eq (by congr 1; ring) rfl) ?_
  have hpop : Runs x B (popTail K j) ⟨lay K R, m * wd K + (2 * j + 2), i⟩
      ⟨lay K (Function.update R j (R j).dropLast), 0, i⟩ := by
    rw [lay_split K R j]
    refine (runs_wV _ _ _ _ j hj false i).seq ?_
    refine (runs_wmoveL _ _ i).seq ?_
    refine Runs.seq ((runs_wP _ _ _ m j hj false i).of_eq (by congr 1) rfl) ?_
    refine (runs_goHome _ _ _ _ i).of_eq rfl ?_
    rw [lay_update, ← presOf_dropLast, ← valOf_dropLast, hm, Nat.add_sub_cancel]
  have hv : lay K R (m * wd K + (2 * j + 2)) = (R j).getLast hne := by
    rw [lay_val R j hj, ← valOf_last _ hne, hm, Nat.add_sub_cancel]
  refine Runs.ite (fun ht => ?_) (fun ht => ?_)
  · have h1 : (R j).getLast hne = true := by rw [← hv]; exact ht
    rw [h1, if_pos rfl] at hp
    exact hpop.seq hp
  · have h1 : (R j).getLast hne = false := by rw [← hv]; exact ht
    rw [h1] at hp
    exact hpop.seq hp

/-! ### Truncating a track to the length of another -/

/-- One block of `truncate`: if track `l` is absent at this block, clear the cell of track `w`. -/
def trBody (K w l : ℕ) : Prog :=
  .seq (moveTo (2 * w + 1) (2 * l + 1))
    (.ite (fun _ b => b) (moveTo (2 * l + 1) (wd K + (2 * w + 1)))
    (.seq (moveTo (2 * l + 1) (2 * w + 1)) (.seq (write false) (.seq (wmove .right)
      (.seq (write false) (moveTo (2 * w + 2) (wd K + (2 * w + 1))))))))

/-- `R w := (R w).take (R l).length`. -/
def truncate (K w l : ℕ) : Prog :=
  .seq (mvR (2 * w + 1)) (.seq (.loop (fun _ b => b) (trBody K w l)) (goHome K (2 * w + 1)))

theorem runs_truncate (R : ℕ → List Bool) (w l : ℕ) (hw : w < K) (hl : l < K) (hne : w ≠ l)
    (N : ℕ) (hN : (R w).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (truncate K w l) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R w ((R w).take (R l).length)), 0, i⟩ := by
  obtain ⟨L, hL⟩ : ∃ L, L = (R w).length := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (R l).length := ⟨_, rfl⟩
  let P0 : ℕ → ℕ → Bool := fun j => presOf (R j)
  let V0 : ℕ → ℕ → Bool := fun j => valOf (R j)
  let f : ℕ → ℕ → Bool := fun k b => decide (b < L ∧ (k ≤ b ∨ b < M))
  let g : ℕ → ℕ → Bool := fun k b => if b < k ∧ M ≤ b then false else valOf (R w) b
  let stage : ℕ → TState := fun k =>
    ⟨mk K (Function.update P0 w (f k)) (Function.update V0 w (g k)), k * wd K + (2 * w + 1), i⟩
  have h0 : mk K (Function.update P0 w (f 0)) (Function.update V0 w (g 0)) = lay K R := by
    rw [lay_split K R w]
    congr 2; funext b; simp only [f, presOf, ← hL]; bool_omega
  have hLv : mk K (Function.update P0 w (f L)) (Function.update V0 w (g L)) =
      lay K (Function.update R w ((R w).take (R l).length)) := by
    rw [lay_update]
    congr 2 <;> funext b
    · simp only [f, presOf, List.length_take, ← hL, ← hM]; bool_omega
    · simp only [g, valOf, ← hM]
      split_ifs with h
      · rw [List.getD_eq_default _ _ (by simp; omega)]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take]
        by_cases hb : b < M
        · rw [if_pos hb]
        · rw [if_neg hb, List.getElem?_eq_none (by omega)]
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * w + 1) (by omega) (by womega) hB
  refine (runs_mvR _ _ 0 i (by omega)).seq ?_
  refine Runs.seq ?_ ((runs_goHome (x := x) (B := B) _ _ L (2 * w + 1) i).of_eq rfl
    (by rw [hLv]))
  refine (Runs.loop_stages stage L ?_ ?_).of_eq (by simp [stage, h0]) rfl
  · intro k hk
    simp only [stage, mk_pres _ _ _ _ _ hw, Function.update_self, f]
    bool_omega
  · intro k hk
    have hpos := blk_lt (k := k) (N := N) (o := 2 * K) (by omega) (by womega) hB
    refine (runs_moveTo _ _ _ (k * wd K) i (by womega)).seq ?_
    have hv : (mk K (Function.update P0 w (f k)) (Function.update V0 w (g k)))
        (k * wd K + (2 * l + 1)) = decide (k < M) := by
      rw [mk_pres _ _ _ _ _ hl, Function.update_of_ne (Ne.symm hne)]; simp [P0, presOf, hM]
    refine Runs.ite (fun ht => ?_) (fun ht => ?_)
    · have hkM : k < M := by dsimp only at ht; rw [hv] at ht; simpa using ht
      refine (runs_moveTo _ _ _ (k * wd K) i (by womega)).of_eq rfl ?_
      simp only [stage]
      congr 1
      · congr 2 <;> funext b <;> simp only [f, g] <;> bool_omega
      · simp only [wd]; ring
    · have hkM : M ≤ k := by dsimp only at ht; rw [hv] at ht; simpa using ht
      refine (runs_moveTo _ _ _ (k * wd K) i (by womega)).seq ?_
      refine (runs_wP _ _ _ k w hw false i).seq ?_
      refine (runs_wmoveR _ _ i (by womega)).seq ?_
      refine Runs.seq ((runs_wV _ _ _ k w hw false i).of_eq rfl rfl) ?_
      refine (runs_moveTo _ _ _ (k * wd K) i (by womega)).of_eq (by congr 1) ?_
      simp only [stage]
      congr 1
      · congr 2 <;> funext b <;> simp only [Function.update_apply, f, g] <;> bool_omega
      · simp only [wd]; ring

/-! ### Prepending a bit -/

/-- `R j := β :: R j`, using the empty scratch track `s`. -/
def prepend (K j s : ℕ) (β : Bool) : Prog :=
  .seq (copyOff K j s 1) (.seq (mvR (2 * s + 1)) (.seq (write true) (.seq (wmove .right)
    (.seq (write β) (.seq (goHome K (2 * s + 2)) (.seq (clear K j)
      (.seq (copyOff K s j 0) (clear K s))))))))

theorem runs_prepend (R : ℕ → List Bool) (j s : ℕ) (hj : j < K) (hs : s < K) (hne : j ≠ s)
    (hRs : R s = []) (β : Bool) (N : ℕ) (hN : (R j).length + 1 ≤ N) (hB : (N + 3) * wd K ≤ B)
    (i : ℕ) :
    Runs x B (prepend K j s β) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R j (β :: R j)), 0, i⟩ := by
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * s + 2) (by omega) (by womega) hB
  refine (runs_copyOff R j s 1 hj hs hne hRs le_rfl N (by omega) hB i).seq ?_
  refine (runs_mvR _ _ 0 i (by omega)).seq ?_
  refine Runs.seq ((runs_wP (fun j => presOf (R j)) (Function.update (fun j => valOf (R j)) s
    (fun b => if 1 ≤ b ∧ b < (R j).length + 1 then valOf (R j) (b - 1) else false))
    (fun b => decide (1 ≤ b ∧ b < (R j).length + 1)) 0 s hs true i).of_eq
    (by simp only [zero_mul]) rfl) ?_
  refine (runs_wmoveR _ _ i (by womega)).seq ?_
  refine Runs.seq ((runs_wV (Function.update (fun j => presOf (R j)) s
      (Function.update (fun b => decide (1 ≤ b ∧ b < (R j).length + 1)) 0 true))
    (fun j => valOf (R j))
    (fun b => if 1 ≤ b ∧ b < (R j).length + 1 then valOf (R j) (b - 1) else false) 0 s hs β
    i).of_eq (by simp only [TState.mk.injEq, zero_mul, true_and, and_true]; omega) rfl) ?_
  have hR1 : mk K (Function.update (fun j => presOf (R j)) s
      (Function.update (fun b => decide (1 ≤ b ∧ b < (R j).length + 1)) 0 true))
      (Function.update (fun j => valOf (R j)) s (Function.update
        (fun b => if 1 ≤ b ∧ b < (R j).length + 1 then valOf (R j) (b - 1) else false) 0 β)) =
      lay K (Function.update R s (β :: R j)) := by
    rw [lay_update]
    congr 2 <;> funext b
    · simp only [Function.update_apply, presOf, List.length_cons]; bool_omega
    · simp only [Function.update_apply, valOf]
      rcases b with _ | b
      · simp
      · simp only [Nat.add_one_ne_zero, if_false, List.getD_cons_succ, Nat.add_sub_cancel]
        split_ifs with h
        · rfl
        · rw [List.getD_eq_default _ _ (by omega)]
  refine Runs.seq ((runs_goHome (Function.update (fun j => presOf (R j)) s
      (Function.update (fun b => decide (1 ≤ b ∧ b < (R j).length + 1)) 0 true))
    (Function.update (fun j => valOf (R j)) s (Function.update
        (fun b => if 1 ≤ b ∧ b < (R j).length + 1 then valOf (R j) (b - 1) else false) 0 β))
    0 (2 * s + 2) i).of_eq rfl (by rw [hR1])) ?_
  refine (runs_clear _ j hj N (by rw [Function.update_of_ne hne]; omega) hB i).seq ?_
  refine (runs_copy (Function.update (Function.update R s (β :: R j)) j []) s j hs hj
    (Ne.symm hne) (by simp) N (by simp [Ne.symm hne]; omega) hB i).seq ?_
  refine (runs_clear (Function.update (Function.update (Function.update R s (β :: R j)) j [])
    j (β :: R j)) s hs N (by simp [Ne.symm hne]; omega) hB i).of_eq
    (by simp [Ne.symm hne]) ?_
  congr 2
  funext r
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-! ### Loops over a non-empty track -/

/-- Repeat `body` (from home to home) as long as track `j` is non-empty. -/
def whileNE (j : ℕ) (body : Prog) : Prog :=
  .seq (mvR (2 * j + 1)) (.seq (.loop (fun _ w => w) (.seq (mvL (2 * j + 1))
    (.seq body (mvR (2 * j + 1))))) (mvL (2 * j + 1)))

theorem runs_whileNE (Rs : ℕ → ℕ → List Bool) (j L : ℕ) (hj : j < K) (body : Prog)
    (hne : ∀ k, k < L → Rs k j ≠ []) (hL : Rs L j = []) (hB : wd K < B) (i : ℕ)
    (hbody : ∀ k, k < L → Runs x B body ⟨lay K (Rs k), 0, i⟩ ⟨lay K (Rs (k + 1)), 0, i⟩) :
    Runs x B (whileNE j body) ⟨lay K (Rs 0), 0, i⟩ ⟨lay K (Rs L), 0, i⟩ := by
  refine (runs_mvR _ _ 0 i (by womega)).seq ?_
  refine Runs.seq ?_ ((runs_mvL (2 * j + 1) (lay K (Rs L)) (0 + (2 * j + 1)) i).of_eq rfl
    (by simp))
  refine (Runs.loop_stages (fun k => ⟨lay K (Rs k), 0 + (2 * j + 1), i⟩) L ?_ ?_).of_eq rfl rfl
  · intro k hk
    have := lay_pres (Rs k) j hj 0
    simp only [zero_mul] at this
    simp only [this]
    by_cases h : k < L
    · simp [h, List.length_pos_of_ne_nil (hne k h)]
    · simp [show k = L by omega, hL]
  · intro k hk
    refine (runs_mvL _ _ _ i).seq ?_
    refine Runs.seq ((hbody k hk).of_eq (by simp) rfl) ?_
    exact runs_mvR _ _ 0 i (by womega)

/-! ### Reading the input -/

/-- One block of `copyInput`: write the input bit `β` into track `j`, advance both heads. -/
def inBit (K j : ℕ) (β : Bool) : Prog :=
  .seq (write true) (.seq (wmove .right) (.seq (write β) (.seq (imove .right)
    (moveTo (2 * j + 2) (wd K + (2 * j + 1))))))

/-- `R j := x`, for an empty track `j` and the input head at the start. -/
def copyInput (K j : ℕ) : Prog :=
  .seq (mvR (2 * j + 1)) (.seq (.loop (fun a _ => a.isSome)
    (.ite (fun a _ => a == some true) (inBit K j true) (inBit K j false))) (goHome K (2 * j + 1)))

theorem runs_copyInput (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (hRj : R j = []) (N : ℕ)
    (hN : x.length ≤ N) (hB : (N + 3) * wd K ≤ B) :
    Runs x B (copyInput K j) ⟨lay K R, 0, 0⟩ ⟨lay K (Function.update R j x), 0, x.length⟩ := by
  let P0 : ℕ → ℕ → Bool := fun j => presOf (R j)
  let V0 : ℕ → ℕ → Bool := fun j => valOf (R j)
  let f : ℕ → ℕ → Bool := fun k b => decide (b < k)
  let g : ℕ → ℕ → Bool := fun k b => if b < k then valOf x b else false
  let stage : ℕ → TState := fun k =>
    ⟨mk K (Function.update P0 j (f k)) (Function.update V0 j (g k)), k * wd K + (2 * j + 1), k⟩
  have h0 : mk K (Function.update P0 j (f 0)) (Function.update V0 j (g 0)) = lay K R := by
    rw [lay_split K R j, hRj, presOf_nil, valOf_nil]
    congr 2
  have hLv : mk K (Function.update P0 j (f x.length)) (Function.update V0 j (g x.length)) =
      lay K (Function.update R j x) := by
    rw [lay_update]
    congr 2; funext b; simp only [g]; split_ifs <;>
      first | rfl | exact (valOf_ge (by omega)).symm
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * j + 1) (by omega) (by womega) hB
  refine (runs_mvR _ _ 0 0 (by omega)).seq ?_
  refine Runs.seq ?_ ((runs_goHome (x := x) (B := B) _ _ x.length (2 * j + 1) x.length).of_eq rfl
    (by rw [hLv]))
  refine (Runs.loop_stages stage x.length ?_ ?_).of_eq (by simp [stage, h0]) rfl
  · intro k hk
    simp only [stage]
    by_cases h : k < x.length
    · simp [h]
    · simp [h]
  · intro k hk
    have hpos := blk_lt (k := k) (N := N) (o := 2 * K) (by omega) (by womega) hB
    have hx : x[k]? = some (valOf x k) := by
      rw [List.getElem?_eq_getElem hk, valOf, List.getD_eq_getElem _ _ hk]
    have hin : ∀ β, β = valOf x k →
        Runs x B (inBit K j β)
          ⟨mk K (Function.update P0 j (f k)) (Function.update V0 j (g k)),
            k * wd K + (2 * j + 1), k⟩
          (stage (k + 1)) := by
      intro β hβ
      refine (runs_wP _ _ _ k j hj true k).seq ?_
      refine (runs_wmoveR _ _ k (by womega)).seq ?_
      refine Runs.seq ((runs_wV _ _ _ k j hj β k).of_eq rfl rfl) ?_
      refine (runs_imoveR _ _ k).seq ?_
      refine (runs_moveTo _ _ _ (k * wd K) _ (by womega)).of_eq (by congr 1) ?_
      simp only [stage]
      congr 1
      · congr 2 <;> funext b
        · simp only [Function.update_apply, f]; bool_omega
        · simp only [Function.update_apply, g]
          by_cases hb : b = k
          · subst hb; simp [hβ]
          · rw [if_neg hb]; bool_omega
      · simp only [wd]; ring
      · omega
    refine Runs.ite (fun ht => ?_) (fun ht => ?_)
    · refine hin true ?_
      simp only [stage] at ht
      rw [hx] at ht
      simpa using ht.symm
    · refine hin false ?_
      simp only [stage] at ht
      rw [hx] at ht
      cases h : valOf x k <;> simp_all

end Tracks

end Complexity.Space
