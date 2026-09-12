/-
**Writing a state of the Krivine machine with binary pointers: the logarithmic overhead.**

`Start/KrivineSpace.lean` measures the space of a state of the shared implementation as the
number of cells it keeps alive, and shows that the dead cells can be removed
(`Krivine.Impl.gcState`).  That is a measure in *cells*; a machine works in *bits*, and the
translation costs a factor: an address of a heap of `n` cells needs `log₂ n` bits, not one.

`Krivine.Impl.encState` (`Start/KrivineHeapCost.lean`) writes addresses in unary, which is
harmless for a polynomial time bound and useless here — it costs one bit per unit of address.
This module writes a state with **fixed-width binary fields** instead, and proves the two
statements a space bound needs: the encoding is faithful, and the encoding of a collected state
is bounded by the number of live cells times the number of bits of an address.

Main definitions:

* `Krivine.Impl.bitsOf`, `Krivine.Impl.numOf` — a natural number in `w` bits, and back;
* `Krivine.Impl.encStateBin` — the state as a word: code, environment pointer, stack (with its
  length) and heap (with its length), every field in `w` bits;
* `Krivine.Impl.decStateBin` — the decoder;
* `Krivine.Impl.FitsIn` — every field of the state fits in `w` bits.

Main results:

* `Krivine.Impl.decStateBin_encStateBin`, `Krivine.Impl.encStateBin_inj` — **the encoding is
  faithful**: a state that fits in `w` bits is determined by its word;
* `Krivine.Impl.encStateBin_length` — its exact length;
* `Krivine.Impl.fitsIn_gcState` — a collected state fits in `Krivine.Impl.widthOf` bits, which is
  the number of bits of the size of the table plus the space plus the height of the stack;
* `Krivine.Impl.encStateBin_gcState_length_le` — **the logarithmic overhead**: the collected
  state occupies at most `(4 + |stack| + 3 · space) · (w + 1)` bits, with `w` that number of
  bits;
* `Krivine.Impl.space_le_encStateBin_gcState_length` — and at least `space` bits, so the two
  measures agree up to that logarithmic factor.
-/

import Mathlib.Data.Nat.Size
import Start.KrivineSpaceGc

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-! ### Numbers in binary, on a fixed width -/

/-- A natural number in `w` bits, least significant bit first. -/
def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => decide (n % 2 = 1) :: bitsOf w (n / 2)

/-- The number a word denotes, least significant bit first. -/
def numOf : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * numOf bs

@[simp] theorem bitsOf_length (w n : ℕ) : (bitsOf w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [bitsOf, ih]

theorem numOf_bitsOf (w n : ℕ) : numOf (bitsOf w n) = n % 2 ^ w := by
  induction w generalizing n with
  | zero => simp [bitsOf, numOf, Nat.mod_one]
  | succ w ih =>
      rw [bitsOf, numOf, ih, pow_succ, mul_comm (2 ^ w) 2, Nat.mod_mul]
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- On a width that is large enough, reading back the bits gives the number. -/
theorem numOf_bitsOf_of_lt {w n : ℕ} (h : n < 2 ^ w) : numOf (bitsOf w n) = n := by
  rw [numOf_bitsOf, Nat.mod_eq_of_lt h]

/-! ### A state as a word -/

/-- A pointer: a tag bit, then the address (`0` when the pointer is empty). -/
def encPtrBin (w : ℕ) : Option ℕ → List Bool
  | none => false :: bitsOf w 0
  | some p => true :: bitsOf w p

/-- A cell: a tag bit, then the address it holds, then the pointer it holds. -/
def encCellBin (w : ℕ) : Cell → List Bool
  | Cell.clos c e => false :: (bitsOf w c ++ encPtrBin w e)
  | Cell.cons a t => true :: (bitsOf w a ++ encPtrBin w t)

/-- **The state as a word**: the code, the environment pointer, the stack preceded by its
length, and the heap preceded by its length, every field on `w` bits. -/
def encStateBin (w : ℕ) (s : HState) : List Bool :=
  bitsOf w s.code ++ encPtrBin w s.env ++ bitsOf w s.stack.length ++
    s.stack.flatMap (bitsOf w) ++ bitsOf w s.heap.length ++ s.heap.flatMap (encCellBin w)

@[simp] theorem encPtrBin_length (w : ℕ) (p : Option ℕ) : (encPtrBin w p).length = w + 1 := by
  cases p <;> simp [encPtrBin]

@[simp] theorem encCellBin_length (w : ℕ) (c : Cell) : (encCellBin w c).length = 2 * w + 2 := by
  cases c <;> simp [encCellBin] <;> omega

theorem length_flatMap_bitsOf (w : ℕ) (l : List ℕ) :
    (l.flatMap (bitsOf w)).length = l.length * w := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, List.length_append, bitsOf_length, ih, List.length_cons]
      ring

theorem length_flatMap_encCell (w : ℕ) (hp : Heap) :
    (hp.flatMap (encCellBin w)).length = hp.length * (2 * w + 2) := by
  induction hp with
  | nil => simp
  | cons c hp ih =>
      rw [List.flatMap_cons, List.length_append, encCellBin_length, ih, List.length_cons]
      ring

/-- **The exact length of the word.** -/
theorem encStateBin_length (w : ℕ) (s : HState) :
    (encStateBin w s).length =
      4 * w + 1 + s.stack.length * w + s.heap.length * (2 * w + 2) := by
  simp only [encStateBin, List.length_append, bitsOf_length, encPtrBin_length,
    length_flatMap_bitsOf, length_flatMap_encCell]
  omega

/-! ### Reading the word back -/

/-- Reading one `w`-bit field. -/
def decNum (w : ℕ) (bs : List Bool) : ℕ × List Bool := (numOf (bs.take w), bs.drop w)

/-- Reading a pointer. -/
def decPtr (w : ℕ) : List Bool → Option ℕ × List Bool
  | [] => (none, [])
  | b :: bs =>
      let r := decNum w bs
      (if b then some r.1 else none, r.2)

/-- Reading a cell. -/
def decCell (w : ℕ) : List Bool → Cell × List Bool
  | [] => (Cell.clos 0 none, [])
  | b :: bs =>
      let r := decNum w bs
      let r' := decPtr w r.2
      (if b then Cell.cons r.1 r'.1 else Cell.clos r.1 r'.1, r'.2)

/-- Reading `k` addresses. -/
def decNums (w : ℕ) : ℕ → List Bool → List ℕ × List Bool
  | 0, bs => ([], bs)
  | k + 1, bs =>
      let r := decNum w bs
      let r' := decNums w k r.2
      (r.1 :: r'.1, r'.2)

/-- Reading `k` cells. -/
def decCells (w : ℕ) : ℕ → List Bool → Heap × List Bool
  | 0, bs => ([], bs)
  | k + 1, bs =>
      let r := decCell w bs
      let r' := decCells w k r.2
      (r.1 :: r'.1, r'.2)

/-- **The decoder.** -/
def decStateBin (w : ℕ) (bs : List Bool) : HState :=
  let r0 := decNum w bs
  let r1 := decPtr w r0.2
  let r2 := decNum w r1.2
  let r3 := decNums w r2.1 r2.2
  let r4 := decNum w r3.2
  let r5 := decCells w r4.1 r4.2
  ⟨r0.1, r1.1, r3.1, r5.1⟩

/-! ### The encoding is faithful -/

theorem decNum_append {w n : ℕ} (h : n < 2 ^ w) (r : List Bool) :
    decNum w (bitsOf w n ++ r) = (n, r) := by
  have ht : (bitsOf w n ++ r).take w = bitsOf w n := by
    have h := List.take_left (l₁ := bitsOf w n) (l₂ := r)
    rwa [bitsOf_length] at h
  have hd : (bitsOf w n ++ r).drop w = r := by
    have h := List.drop_left (l₁ := bitsOf w n) (l₂ := r)
    rwa [bitsOf_length] at h
  rw [decNum, ht, hd, numOf_bitsOf_of_lt h]

theorem decPtr_append {w : ℕ} {p : Option ℕ} (h : ∀ j ∈ p, j < 2 ^ w) (r : List Bool) :
    decPtr w (encPtrBin w p ++ r) = (p, r) := by
  cases p with
  | none =>
      simp only [encPtrBin, List.cons_append, decPtr, decNum_append (Nat.two_pow_pos w)]
      simp
  | some j =>
      simp only [encPtrBin, List.cons_append, decPtr, decNum_append (h j rfl)]
      simp

/-- Every field of a cell fits in `w` bits. -/
def CellFits (w : ℕ) : Cell → Prop
  | Cell.clos c e => c < 2 ^ w ∧ ∀ j ∈ e, j < 2 ^ w
  | Cell.cons a t => a < 2 ^ w ∧ ∀ j ∈ t, j < 2 ^ w

theorem decCell_append {w : ℕ} {c : Cell} (h : CellFits w c) (r : List Bool) :
    decCell w (encCellBin w c ++ r) = (c, r) := by
  cases c with
  | clos code e =>
      obtain ⟨hc, he⟩ := h
      simp only [encCellBin, List.cons_append, List.append_assoc, decCell, decNum_append hc,
        decPtr_append he]
      simp
  | cons a t =>
      obtain ⟨ha, ht⟩ := h
      simp only [encCellBin, List.cons_append, List.append_assoc, decCell, decNum_append ha,
        decPtr_append ht]
      simp

theorem decNums_append {w : ℕ} {l : List ℕ} (h : ∀ n ∈ l, n < 2 ^ w) (r : List Bool) :
    decNums w l.length (l.flatMap (bitsOf w) ++ r) = (l, r) := by
  induction l generalizing r with
  | nil => simp [decNums]
  | cons a l ih =>
      have ha : a < 2 ^ w := h a (by simp)
      have hl : ∀ n ∈ l, n < 2 ^ w := fun n hn => h n (by simp [hn])
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decNums,
        decNum_append ha, ih hl]

theorem decCells_append {w : ℕ} {hp : Heap} (h : ∀ c ∈ hp, CellFits w c) (r : List Bool) :
    decCells w hp.length (hp.flatMap (encCellBin w) ++ r) = (hp, r) := by
  induction hp generalizing r with
  | nil => simp [decCells]
  | cons c hp ih =>
      have hc : CellFits w c := h c (by simp)
      have hl : ∀ d ∈ hp, CellFits w d := fun d hd => h d (by simp [hd])
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, decCells,
        decCell_append hc, ih hl]

/-- Every field of a state fits in `w` bits. -/
structure FitsIn (w : ℕ) (s : HState) : Prop where
  /-- The code address fits. -/
  code : s.code < 2 ^ w
  /-- The environment pointer fits. -/
  env : ∀ j ∈ s.env, j < 2 ^ w
  /-- The height of the stack fits. -/
  stackLen : s.stack.length < 2 ^ w
  /-- Every pointer of the stack fits. -/
  stack : ∀ p ∈ s.stack, p < 2 ^ w
  /-- The size of the heap fits. -/
  heapLen : s.heap.length < 2 ^ w
  /-- Every cell of the heap fits. -/
  cells : ∀ c ∈ s.heap, CellFits w c

/-- **The encoding is faithful**: the decoder recovers a state that fits. -/
theorem decStateBin_encStateBin {w : ℕ} {s : HState} (h : FitsIn w s) :
    decStateBin w (encStateBin w s) = s := by
  have hcells : decCells w s.heap.length (s.heap.flatMap (encCellBin w)) = (s.heap, []) := by
    simpa using decCells_append (w := w) h.cells []
  simp only [decStateBin, encStateBin, List.append_assoc, decNum_append h.code,
    decPtr_append h.env, decNum_append h.stackLen, decNums_append h.stack,
    decNum_append h.heapLen, hcells]

/-- **A state that fits in `w` bits is determined by its word.** -/
theorem encStateBin_inj {w : ℕ} {s s' : HState} (h : FitsIn w s) (h' : FitsIn w s')
    (heq : encStateBin w s = encStateBin w s') : s = s' := by
  have := decStateBin_encStateBin h
  rw [heq, decStateBin_encStateBin h'] at this
  exact this.symm

/-! ### The width a collected state needs, and the logarithmic overhead -/

/-- The width used to write a collected state: the number of bits of the size of the code table,
the height of the stack and the space of the state. -/
def widthOf (tab : Tab) (s : HState) : ℕ := Nat.size (tab.length + s.stack.length + space s)

theorem lt_two_pow_widthOf {tab : Tab} {s : HState} {n : ℕ}
    (h : n ≤ tab.length + s.stack.length + space s) : n < 2 ^ widthOf tab s :=
  lt_of_le_of_lt h (Nat.lt_size_self _)

/-- The cell at a live address, read from the invariant. -/
private theorem cellTyped_of_getElem? {tab : Tab} {s : HState} (hv : Valid tab s) {a : ℕ}
    {c : Cell} (hc : s.heap[a]? = some c) : CellTyped tab s.heap c := by
  have ha : a < s.heap.length := lt_length_of_getElem? hc
  have hcase : (s.heap[a]'ha) = c := by
    have := List.getElem?_eq_getElem ha
    rw [this] at hc
    exact Option.some_inj.1 hc
  have := hv.heapTyped a ha
  rwa [hcase] at this

/-- Every cell of a collected heap fits: its code address is an address of the table, and its
pointers are ranks of live cells. -/
theorem cellFits_gcState {tab : Tab} {s : HState} (hv : Valid tab s) {d : Cell}
    (hd : d ∈ (gcState s).heap) : CellFits (widthOf tab s) d := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hd
  obtain ⟨a, c, hlive, hc, -, rfl⟩ := getElem?_gcHeap_eq (by rwa [gcState_heap] at hk)
  have hcty : CellTyped tab s.heap c := cellTyped_of_getElem? hv hc
  have hcl : Closed (IsLive s) s.heap := isLive_closed hv.heapWF
  have halt : a < s.heap.length := lt_length_of_getElem? hc
  have hrefs : ∀ b ∈ c.refs, rankIn (IsLive s) b < 2 ^ widthOf tab s := by
    intro b hb
    have hbl : IsLive s b := hcl a c halt hlive hc b hb
    exact lt_two_pow_widthOf (by have := rankIn_lt_space hbl; omega)
  cases c with
  | clos code e =>
      refine ⟨lt_two_pow_widthOf (by have := hcty.1; omega), ?_⟩
      intro j hj
      obtain ⟨i, hi, rfl⟩ : ∃ i, i ∈ e ∧ rankIn (IsLive s) i = j := by
        cases e with
        | none => simp at hj
        | some i => exact ⟨i, rfl, by simpa using hj⟩
      exact hrefs i (by simpa using hi)
  | cons x t =>
      refine ⟨hrefs x (by simp), ?_⟩
      intro j hj
      obtain ⟨i, hi, rfl⟩ : ∃ i, i ∈ t ∧ rankIn (IsLive s) i = j := by
        cases t with
        | none => simp at hj
        | some i => exact ⟨i, rfl, by simpa using hj⟩
      exact hrefs i (List.mem_cons_of_mem _ (Option.mem_toList.2 hi))

/-- **A collected state fits in `Krivine.Impl.widthOf` bits.** -/
theorem fitsIn_gcState {tab : Tab} {s : HState} (hv : Valid tab s) :
    FitsIn (widthOf tab s) (gcState s) := by
  refine ⟨lt_two_pow_widthOf (by rw [gcState_code]; have := hv.code_lt; omega), ?_, ?_, ?_, ?_,
    fun c hc => cellFits_gcState hv hc⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_gcState_env hj
    obtain ⟨x, t, hx⟩ := hv.env_ty i hi
    have hlive : IsLive s i := isLive_root (mem_roots_env (s := s) hi) hx
    exact lt_two_pow_widthOf (by have := rankIn_lt_space hlive; omega)
  · rw [gcState_stack, List.length_map]
    exact lt_two_pow_widthOf (by omega)
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (by rwa [gcState_stack] at hp)
    obtain ⟨code, e, hcell⟩ := hv.stack_ty i hi
    have hlive : IsLive s i := isLive_root (mem_roots_stack hi) hcell
    exact lt_two_pow_widthOf (by have := rankIn_lt_space hlive; omega)
  · rw [gcState_heap_length]
    exact lt_two_pow_widthOf (by omega)

/-- The exact length of the word of a collected state. -/
theorem encStateBin_gcState_length (w : ℕ) (s : HState) :
    (encStateBin w (gcState s)).length =
      4 * w + 1 + s.stack.length * w + space s * (2 * w + 2) := by
  rw [encStateBin_length, gcState_stack, gcState_heap_length, List.length_map]

/-- **The logarithmic overhead**: a collected state is written in a number of bits that is its
number of live cells and the height of its stack, times the number of bits of an address. -/
theorem encStateBin_gcState_length_le (w : ℕ) (s : HState) :
    (encStateBin w (gcState s)).length ≤ (4 + s.stack.length + 3 * space s) * (w + 1) := by
  rw [encStateBin_gcState_length]
  have key : (4 + s.stack.length + 3 * space s) * (w + 1)
      = (4 * w + 1 + s.stack.length * w + space s * (2 * w + 2))
        + (3 + s.stack.length + space s * w + space s) := by
    ring
  rw [key]
  exact Nat.le_add_right _ _

/-- **The two measures agree up to that factor**: the word is at least as long as the number of
live cells. -/
theorem space_le_encStateBin_gcState_length (w : ℕ) (s : HState) :
    space s ≤ (encStateBin w (gcState s)).length := by
  rw [encStateBin_gcState_length]
  have h : space s ≤ space s * (2 * w + 2) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- **The state of the machine, written faithfully with a logarithmic overhead.**  Collected and
written on `Krivine.Impl.widthOf` bits per field — the number of bits of the size of the code
table, the height of the stack and the space of the state — a state is recovered from its word,
and the word is no longer than the number of live cells and the height of the stack, times that
number of bits. -/
theorem gcState_encoded_log {tab : Tab} {s : HState} (hv : Valid tab s) :
    decStateBin (widthOf tab s) (encStateBin (widthOf tab s) (gcState s)) = gcState s ∧
      (encStateBin (widthOf tab s) (gcState s)).length
        ≤ (4 + s.stack.length + 3 * space s) * (widthOf tab s + 1) :=
  ⟨decStateBin_encStateBin (fitsIn_gcState hv), encStateBin_gcState_length_le _ _⟩

end Impl

end Krivine
