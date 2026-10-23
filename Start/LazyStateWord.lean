import Start.LazyMachine
import Start.KolmogorovCount

/-!
# A binary encoding of the states of the lazy machine
(row M25-CBNEED-STEP-PROG, first exit criterion; big round 2, run 1, item W3)

The call-by-need machine of `Start/LazyMachine.lean` has states with a code, an environment of
heap addresses, a stack of argument and update frames, and a heap of thunk, hole and value cells.
This module encodes them as words, prefix-freely:

* `Lazy.natBits` — numbers in unary (`Lambda.sizeBits (var n)`); `Lazy.listBits` — lists, with a
  `1` before each entry and a final `0`, and its unique decoding `Lazy.listBits_append_inj`;
* `Lazy.lclosBits`, `Lazy.cellBits`, `Lazy.lframeBits`, `Lazy.lstateBits`;
* **`Lazy.lstateBits_injective`** — the encoding of states is injective.
-/

set_option autoImplicit false

namespace Lazy

/-- Numbers in unary, `1ⁿ⁺¹ 0`. -/
def natBits (n : ℕ) : List Bool := Lambda.sizeBits (.var n)

theorem natBits_append_inj (n n' : ℕ) (r r' : List Bool) (h : natBits n ++ r = natBits n' ++ r') :
    n = n' ∧ r = r' := by
  obtain ⟨e, rfl⟩ := Lambda.sizeBits_append_inj _ _ _ _ h
  cases e
  exact ⟨rfl, rfl⟩

/-- Lists: a `1` before each entry, a final `0`. -/
def listBits {α : Type} (f : α → List Bool) : List α → List Bool
  | [] => [false]
  | a :: l => true :: (f a ++ listBits f l)

theorem listBits_append_inj {α : Type} {f : α → List Bool}
    (hf : ∀ (a a' : α) (r r' : List Bool), f a ++ r = f a' ++ r' → a = a' ∧ r = r') :
    ∀ (l l' : List α) (r r' : List Bool), listBits f l ++ r = listBits f l' ++ r' → l = l' ∧ r = r'
  | [], [], r, r', h => by simpa [listBits] using h
  | [], _ :: _, _, _, h => by simp [listBits] at h
  | _ :: _, [], _, _, h => by simp [listBits] at h
  | a :: l, a' :: l', r, r', h => by
    simp only [listBits, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := hf a a' _ _ h
    obtain ⟨rfl, rfl⟩ := listBits_append_inj hf l l' r r' h2
    exact ⟨rfl, rfl⟩

/-- The code of a closure: its term, then its environment of addresses. -/
def lclosBits (c : LClos) : List Bool := Lambda.sizeBits c.code ++ listBits natBits c.env

theorem lclosBits_append_inj (c c' : LClos) (r r' : List Bool)
    (h : lclosBits c ++ r = lclosBits c' ++ r') : c = c' ∧ r = r' := by
  obtain ⟨t, e⟩ := c
  obtain ⟨t', e'⟩ := c'
  simp only [lclosBits, List.append_assoc] at h
  obtain ⟨rfl, h2⟩ := Lambda.sizeBits_append_inj t t' _ _ h
  obtain ⟨rfl, rfl⟩ := listBits_append_inj natBits_append_inj e e' r r' h2
  exact ⟨rfl, rfl⟩

/-- The code of a heap cell. -/
def cellBits : Cell → List Bool
  | .thunk c => false :: false :: lclosBits c
  | .hole c => false :: true :: lclosBits c
  | .value c v => true :: (lclosBits c ++ lclosBits v)

theorem cellBits_append_inj : ∀ (c c' : Cell) (r r' : List Bool),
    cellBits c ++ r = cellBits c' ++ r' → c = c' ∧ r = r'
  | .thunk c, .thunk c', r, r', h => by
    simp only [cellBits, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := lclosBits_append_inj c c' r r' h
    exact ⟨rfl, rfl⟩
  | .hole c, .hole c', r, r', h => by
    simp only [cellBits, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := lclosBits_append_inj c c' r r' h
    exact ⟨rfl, rfl⟩
  | .value c v, .value c' v', r, r', h => by
    simp only [cellBits, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := lclosBits_append_inj c c' _ _ h
    obtain ⟨rfl, rfl⟩ := lclosBits_append_inj v v' r r' h2
    exact ⟨rfl, rfl⟩
  | .thunk _, .hole _, _, _, h => by simp [cellBits] at h
  | .thunk _, .value _ _, _, _, h => by simp [cellBits] at h
  | .hole _, .thunk _, _, _, h => by simp [cellBits] at h
  | .hole _, .value _ _, _, _, h => by simp [cellBits] at h
  | .value _ _, .thunk _, _, _, h => by simp [cellBits] at h
  | .value _ _, .hole _, _, _, h => by simp [cellBits] at h

/-- The code of a stack frame. -/
def lframeBits : Frame → List Bool
  | .arg a => false :: natBits a
  | .upd a => true :: natBits a

theorem lframeBits_append_inj : ∀ (f f' : Frame) (r r' : List Bool),
    lframeBits f ++ r = lframeBits f' ++ r' → f = f' ∧ r = r'
  | .arg a, .arg a', r, r', h => by
    simp only [lframeBits, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := natBits_append_inj a a' r r' h
    exact ⟨rfl, rfl⟩
  | .upd a, .upd a', r, r', h => by
    simp only [lframeBits, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := natBits_append_inj a a' r r' h
    exact ⟨rfl, rfl⟩
  | .arg _, .upd _, _, _, h => by simp [lframeBits] at h
  | .upd _, .arg _, _, _, h => by simp [lframeBits] at h

/-- **The code of a state of the lazy machine**: code, environment, stack, heap. -/
def lstateBits (s : LState) : List Bool :=
  Lambda.sizeBits s.code ++ listBits natBits s.env ++ listBits lframeBits s.stack ++
    listBits cellBits s.heap

/-- **The encoding of lazy machine states is injective.** -/
theorem lstateBits_injective : Function.Injective lstateBits := by
  intro s s' h
  obtain ⟨t, e, k, hp⟩ := s
  obtain ⟨t', e', k', hp'⟩ := s'
  simp only [lstateBits, List.append_assoc] at h
  obtain ⟨rfl, h2⟩ := Lambda.sizeBits_append_inj t t' _ _ h
  obtain ⟨rfl, h3⟩ := listBits_append_inj natBits_append_inj e e' _ _ h2
  obtain ⟨rfl, h4⟩ := listBits_append_inj lframeBits_append_inj k k' _ _ h3
  obtain ⟨rfl, -⟩ := listBits_append_inj cellBits_append_inj hp hp' [] [] (by simpa using h4)
  rfl

end Lazy
