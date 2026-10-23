import Start.CbvMachine
import Start.KolmogorovCount

/-!
# A binary encoding of the states of the CEK machine
(row M25-CBV-STEP-PROG, first exit criterion; big round 2, run 1, item W3)

The CEK machine of `Start/CbvMachine.lean` has states `eval t e k` and `ret c k` with nested
environments of closures (`Krivine.Clos`) and continuations of frames.  This module encodes them
as words, prefix-freely, from the prefix-free code of terms `Lambda.sizeBits`
(`Start/KolmogorovCount.lean`):

* `CEK.closBits`, `CEK.envBits` (mutual), `CEK.frameBits`, `CEK.stackBits`, `CEK.stateBits`;
* `CEK.closBits_append_inj`, `CEK.envBits_append_inj`, `CEK.frameBits_append_inj`,
  `CEK.stackBits_append_inj` — unique decoding;
* **`CEK.stateBits_injective`** — the encoding of states is injective.
-/

set_option autoImplicit false

namespace CEK

open Krivine (Clos Env)

mutual
/-- The code of a closure: its term, then its environment. -/
def closBits : Clos → List Bool
  | .mk t e => Lambda.sizeBits t ++ envBits e
/-- The code of an environment: `1` before each closure, `0` at the end. -/
def envBits : List Clos → List Bool
  | [] => [false]
  | c :: e => true :: (closBits c ++ envBits e)
end

mutual
theorem closBits_append_inj : ∀ (c c' : Clos) (r r' : List Bool),
    closBits c ++ r = closBits c' ++ r' → c = c' ∧ r = r'
  | .mk t e, .mk t' e', r, r', h => by
    simp only [closBits, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := Lambda.sizeBits_append_inj t t' _ _ h
    obtain ⟨rfl, rfl⟩ := envBits_append_inj e e' r r' h2
    exact ⟨rfl, rfl⟩
theorem envBits_append_inj : ∀ (e e' : List Clos) (r r' : List Bool),
    envBits e ++ r = envBits e' ++ r' → e = e' ∧ r = r'
  | [], [], r, r', h => by simpa [envBits] using h
  | [], _ :: _, _, _, h => by simp [envBits] at h
  | _ :: _, [], _, _, h => by simp [envBits] at h
  | c :: e, c' :: e', r, r', h => by
    simp only [envBits, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := closBits_append_inj c c' _ _ h
    obtain ⟨rfl, rfl⟩ := envBits_append_inj e e' r r' h2
    exact ⟨rfl, rfl⟩
end

/-- The code of a frame. -/
def frameBits : Frame → List Bool
  | .arg u e => false :: (Lambda.sizeBits u ++ envBits e)
  | .fn c => true :: closBits c

/-- The code of a continuation. -/
def stackBits : List Frame → List Bool
  | [] => [false]
  | f :: k => true :: (frameBits f ++ stackBits k)

/-- **The code of a CEK state.** -/
def stateBits : State → List Bool
  | .eval t e k => false :: (Lambda.sizeBits t ++ envBits e ++ stackBits k)
  | .ret c k => true :: (closBits c ++ stackBits k)

theorem frameBits_append_inj : ∀ (f f' : Frame) (r r' : List Bool),
    frameBits f ++ r = frameBits f' ++ r' → f = f' ∧ r = r'
  | .arg u e, .arg u' e', r, r', h => by
    simp only [frameBits, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := Lambda.sizeBits_append_inj u u' _ _ h
    obtain ⟨rfl, rfl⟩ := envBits_append_inj e e' r r' h2
    exact ⟨rfl, rfl⟩
  | .arg _ _, .fn _, _, _, h => by simp [frameBits] at h
  | .fn _, .arg _ _, _, _, h => by simp [frameBits] at h
  | .fn c, .fn c', r, r', h => by
    simp only [frameBits, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := closBits_append_inj c c' r r' h
    exact ⟨rfl, rfl⟩

theorem stackBits_append_inj : ∀ (k k' : List Frame) (r r' : List Bool),
    stackBits k ++ r = stackBits k' ++ r' → k = k' ∧ r = r'
  | [], [], r, r', h => by simpa [stackBits] using h
  | [], _ :: _, _, _, h => by simp [stackBits] at h
  | _ :: _, [], _, _, h => by simp [stackBits] at h
  | f :: k, f' :: k', r, r', h => by
    simp only [stackBits, List.cons_append, List.cons.injEq, true_and, List.append_assoc] at h
    obtain ⟨rfl, h2⟩ := frameBits_append_inj f f' _ _ h
    obtain ⟨rfl, rfl⟩ := stackBits_append_inj k k' r r' h2
    exact ⟨rfl, rfl⟩

/-- **The encoding of CEK states is injective.** -/
theorem stateBits_injective : Function.Injective stateBits := by
  intro s s' h
  cases s with
  | eval t e k =>
    cases s' with
    | eval t' e' k' =>
      simp only [stateBits, List.cons.injEq, true_and, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := Lambda.sizeBits_append_inj t t' _ _ h
      obtain ⟨rfl, h3⟩ := envBits_append_inj e e' _ _ h2
      obtain ⟨rfl, -⟩ := stackBits_append_inj k k' [] [] (by simpa using h3)
      rfl
    | ret _ _ => simp [stateBits] at h
  | ret c k =>
    cases s' with
    | eval _ _ _ => simp [stateBits] at h
    | ret c' k' =>
      simp only [stateBits, List.cons.injEq, true_and] at h
      obtain ⟨rfl, h2⟩ := closBits_append_inj c c' _ _ h
      obtain ⟨rfl, -⟩ := stackBits_append_inj k k' [] [] (by simpa using h2)
      rfl

end CEK
