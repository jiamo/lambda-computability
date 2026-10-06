/-
**Word-level data structures of the verifier of Shamir's protocol.**

The verifier of `Start/ShamirMachine.lean` keeps its data in binary words, in formats that the
Cobham terms of `Start/ShamirCob.lean` can manipulate:

* a **record** `1^{|w|} 0 w` (`Complexity.encMsg`) — the transcript of an interactive proof is a
  sequence of records, and so is the stack of the verifier; `Complexity.Shamir.recGet` reads the
  first record of a word and `Complexity.Shamir.recSkip` drops it;
* a **list of field elements** in unary fields (`Complexity.fieldsWord`) — the current point of
  the verifier; `Complexity.Shamir.fieldAt` reads the field at a position and
  `Complexity.Shamir.setField` overwrites it;
* a **message** of the prover, an arbitrary word read as the list of the lengths of its maximal
  runs of ones that are followed by a zero (`Complexity.Shamir.decF`); trailing ones are ignored,
  and the normalised word `Complexity.Shamir.trimW` (the message with its trailing ones removed) is
  exactly `fieldsWord (decF w)` (`Complexity.Shamir.fieldsWord_decF`).
-/

import Start.InteractiveProof
import Start.QbfEvalMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf.EvalW (fieldsWord_append length_fieldsWord)

/-- A number in unary. -/
def un (n : ℕ) : Word := List.replicate n true

@[simp] theorem length_un (n : ℕ) : (un n).length = n := by simp [un]

/-! ### Records -/

/-- The rest of a word after its first record. -/
def recSkip (t : Word) : Word := t.drop (2 * lead1 t + 1)

/-- The content of the first record of a word. -/
def recGet (t : Word) : Word := (t.drop (lead1 t + 1)).take (lead1 t)

theorem encMsg_eq (w : Word) : encMsg w = List.replicate w.length true ++ false :: w := rfl

@[simp] theorem lead1_encMsg_append (w t : Word) : lead1 (encMsg w ++ t) = w.length := by
  rw [encMsg_eq, List.append_assoc, List.cons_append, lead1_replicate_append]

@[simp] theorem recSkip_encMsg (w t : Word) : recSkip (encMsg w ++ t) = t := by
  rw [recSkip, lead1_encMsg_append]
  exact List.drop_left' (by simp)

@[simp] theorem recGet_encMsg (w t : Word) : recGet (encMsg w ++ t) = w := by
  rw [recGet, lead1_encMsg_append,
    show encMsg w ++ t = (List.replicate w.length true ++ [false]) ++ (w ++ t) by simp [encMsg],
    List.drop_left' (by simp), List.take_left' rfl]

theorem recSkip_length_le (t : Word) : (recSkip t).length ≤ t.length := by
  simp [recSkip]

/-! ### Fields -/

/-- Dropping the first unary field. -/
def dropF (A : Word) : Word := (drop1 A).tail

/-- Dropping the first `i` unary fields. -/
def dropFs : ℕ → Word → Word
  | 0, A => A
  | i + 1, A => dropFs i (dropF A)

theorem dropF_fieldsWord : ∀ a : List ℕ, dropF (fieldsWord a) = fieldsWord a.tail
  | [] => by simp [dropF, fieldsWord, drop1]
  | a :: as => by simp [dropF]

theorem dropFs_fieldsWord : ∀ (i : ℕ) (a : List ℕ), dropFs i (fieldsWord a) = fieldsWord (a.drop i)
  | 0, a => rfl
  | i + 1, a => by rw [dropFs, dropF_fieldsWord, dropFs_fieldsWord i, List.drop_tail]

theorem dropFs_add : ∀ (i j : ℕ) (A : Word), dropFs (i + j) A = dropFs j (dropFs i A)
  | 0, j, A => by simp [dropFs]
  | i + 1, j, A => by rw [Nat.add_right_comm, dropFs, dropFs, dropFs_add i j]

theorem length_dropF_le (A : Word) : (dropF A).length ≤ A.length := by
  simp only [dropF, List.length_tail]
  have := length_drop1 A
  omega

theorem length_dropFs_le : ∀ (i : ℕ) (A : Word), (dropFs i A).length ≤ A.length
  | 0, _ => le_rfl
  | i + 1, A => (length_dropFs_le i _).trans (length_dropF_le A)

/-- The field at position `i`. -/
def fieldAt (i : ℕ) (A : Word) : ℕ := lead1 (dropFs i A)

theorem fieldAt_fieldsWord (i : ℕ) (a : List ℕ) : fieldAt i (fieldsWord a) = a.getD i 0 := by
  rw [fieldAt, dropFs_fieldsWord]
  cases h : a.drop i with
  | nil =>
      rw [List.drop_eq_nil_iff] at h
      simp [fieldsWord, lead1, List.getElem?_eq_none h]
  | cons c cs =>
      rw [lead1_fieldsWord]
      have h2 : (a.drop i)[0]? = some c := by rw [h]; rfl
      rw [List.getElem?_drop, add_zero] at h2
      simp [List.getD_eq_getElem?_getD, h2]

/-- The first `i` fields, as a word. -/
def takeFs (i : ℕ) (A : Word) : Word := A.take (A.length - (dropFs i A).length)

theorem takeFs_fieldsWord (i : ℕ) (a : List ℕ) : takeFs i (fieldsWord a) = fieldsWord (a.take i) := by
  rw [takeFs, dropFs_fieldsWord]
  have e : fieldsWord a = fieldsWord (a.take i) ++ fieldsWord (a.drop i) := by
    rw [← fieldsWord_append, List.take_append_drop]
  rw [e, List.length_append, Nat.add_sub_cancel, List.take_left' rfl]

/-- Overwriting the field at position `i` with `s`. -/
def setField (i s : ℕ) (A : Word) : Word := takeFs i A ++ (un s ++ [false]) ++ dropFs (i + 1) A

theorem setField_fieldsWord {i : ℕ} (s : ℕ) {a : List ℕ} (hi : i < a.length) :
    setField i s (fieldsWord a) = fieldsWord (a.set i s) := by
  rw [setField, takeFs_fieldsWord, dropFs_fieldsWord, List.set_eq_take_append_cons_drop,
    if_pos hi, fieldsWord_append]
  simp [fieldsWord, un]

/-! ### Messages -/

/-- The run lengths of ones closed by a zero, the current run having length `c`. -/
def decAux : ℕ → Word → List ℕ
  | _, [] => []
  | c, true :: w => decAux (c + 1) w
  | c, false :: w => c :: decAux 0 w

/-- **A message as a list of numbers**: the lengths of the runs of ones closed by a zero. -/
def decF (w : Word) : List ℕ := decAux 0 w

/-- A word with its trailing ones removed. -/
def trimW (w : Word) : Word := (drop1 w.reverse).reverse

theorem drop1_append_false : ∀ (X Y : Word), drop1 (X ++ false :: Y) = drop1 X ++ false :: Y
  | [], Y => by simp [drop1]
  | false :: X, Y => by simp [drop1]
  | true :: X, Y => by simp only [List.cons_append, drop1]; exact drop1_append_false X Y

theorem drop1_replicate (c : ℕ) : drop1 (List.replicate c true) = [] := by
  induction c with
  | zero => rfl
  | succ c ih => rw [List.replicate_succ, drop1, ih]

theorem trimW_append_false (u v : Word) : trimW (u ++ false :: v) = u ++ false :: trimW v := by
  simp only [trimW, List.reverse_append, List.reverse_cons, List.append_assoc,
    List.singleton_append]
  rw [drop1_append_false]
  simp

theorem fieldsWord_decAux : ∀ (c : ℕ) (w : Word),
    fieldsWord (decAux c w) = trimW (List.replicate c true ++ w)
  | c, [] => by
      simp [decAux, fieldsWord, trimW, List.reverse_replicate, drop1_replicate]
  | c, true :: w => by
      rw [decAux, fieldsWord_decAux (c + 1) w, List.replicate_succ']
      simp
  | c, false :: w => by
      rw [decAux, fieldsWord, fieldsWord_decAux 0 w, trimW_append_false]
      simp

/-- **The normalised message is the word of its numbers.** -/
theorem fieldsWord_decF (w : Word) : fieldsWord (decF w) = trimW w := by
  rw [decF]; simpa using fieldsWord_decAux 0 w

theorem decAux_replicate (w : Word) : ∀ (a c : ℕ),
    decAux c (List.replicate a true ++ false :: w) = (c + a) :: decAux 0 w
  | 0, c => by simp [decAux]
  | a + 1, c => by
      rw [List.replicate_succ, List.cons_append, decAux, decAux_replicate w a (c + 1)]
      simp only [List.cons.injEq, and_true]
      omega

/-- Decoding inverts the field format. -/
theorem decF_fieldsWord : ∀ l : List ℕ, decF (fieldsWord l) = l
  | [] => rfl
  | a :: as => by
      rw [decF, fieldsWord, List.append_assoc, List.singleton_append, decAux_replicate, zero_add]
      rw [← decF, decF_fieldsWord as]

end Complexity.Shamir
