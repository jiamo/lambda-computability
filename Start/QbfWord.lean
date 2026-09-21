/-
**Quantified Boolean formulas as binary words, and `TQBF` as a language.**

The classes of `Start/SpaceMachine.lean` are classes of *languages*: sets of binary words.  To
speak of `TQBF` as one of them — and so to state its hardness — the formulas have to be written
down as words.  This module gives a self-delimiting binary code for formulas: three tag bits per
node (two for a variable or a negation) and a variable index in unary.  A decoder reads a formula
back off the front of a word, so the code is injective, and the length of the code of a formula is
at most `size * (varBound + 3)`.

Putting this together with `Start/QbfVarBound.lean` — every variable of the reduction formula of a
space-bounded machine is below `(3 k + 5) * cfgWidth` — and with `Start/QbfPspace.lean` — its size
is bounded by a polynomial in the length of the input — gives the reduction as a map *on words*
whose output is polynomially long: every language in `NPSPACE`, hence every language in `PSPACE`,
is mapped to the language `Complexity.Qbf.tqbfLang` of the codes of true closed formulas by a map
whose output length is bounded by a single polynomial in the input length.

What is still missing for the `PSPACE`-hardness of `TQBF` is that this map is *computed* in
polynomial time — that its word-to-word transformation is a Cobham function.  That remains the
open boundary recorded as `M14-TQBF-PSPACE-HARD`.

Main definitions:

* `Complexity.Qbf.QBF.unary`, `.enc` — the code of a variable index and of a formula;
* `Complexity.Qbf.QBF.decUnary`, `.dec` — the decoder, driven by a fuel bound;
* `Complexity.Qbf.tqbfLang` — the language of the codes of true closed formulas;
* `Complexity.Qbf.QBF.varBoundOf`, `.wordBound` — the bound on the variables and on the length of
  the code, as functions of the input length.

Main results:

* `Complexity.Qbf.QBF.dec_enc_append` — **the decoder reads a formula back off its code**;
* `Complexity.Qbf.QBF.enc_injective` — the code is injective;
* `Complexity.Qbf.QBF.length_enc_le` — a formula of size `n` whose variables are below `v` has a
  code of length at most `n * (v + 3)`;
* `Complexity.Qbf.tqbfLang_enc_iff` — a code lies in the language exactly when its formula is a
  true closed formula;
* `Complexity.Qbf.QBF.npspace_polyLength_tqbfWord`, `.pspace_polyLength_tqbfWord` — **every
  language in `NPSPACE`, hence in `PSPACE`, is mapped into `tqbfLang` by a map whose output words
  are of polynomially bounded length**.
-/

import Mathlib
import Start.QbfVarBound
import Start.QbfPspace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Qbf

namespace QBF

/-! ### The code -/

/-- A natural number in unary, terminated by a zero bit. -/
def unary (i : ℕ) : List Bool := List.replicate i true ++ [false]

@[simp] theorem length_unary (i : ℕ) : (unary i).length = i + 1 := by simp [unary]

/-- The code of a formula: three tag bits per node (two for a variable or a negation), the
variable indices in unary, and the codes of the subformulas in order. -/
def enc : QBF → List Bool
  | .var i => [false, false] ++ unary i
  | .neg p => [false, true] ++ enc p
  | .conj p q => [true, false, false] ++ (enc p ++ enc q)
  | .disj p q => [true, false, true] ++ (enc p ++ enc q)
  | .all i p => [true, true, false] ++ (unary i ++ enc p)
  | .ex i p => [true, true, true] ++ (unary i ++ enc p)

/-! ### The decoder -/

/-- Reading a unary index off the front of a word. -/
def decUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: r => some (0, r)
  | true :: r =>
      match decUnary r with
      | some (i, r') => some (i + 1, r')
      | none => none

theorem decUnary_unary (i : ℕ) (r : List Bool) : decUnary (unary i ++ r) = some (i, r) := by
  induction i with
  | zero => simp [unary, decUnary]
  | succ i ih =>
      have : unary (i + 1) ++ r = true :: (unary i ++ r) := by
        simp [unary, List.replicate_succ]
      rw [this]
      simp [decUnary, ih]

/-- Reading a formula off the front of a word; the first argument is a fuel bound, which the size
of the formula supplies. -/
def dec : ℕ → List Bool → Option (QBF × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | _ + 1, false :: false :: r =>
      match decUnary r with
      | some (i, r') => some (.var i, r')
      | none => none
  | f + 1, false :: true :: r =>
      match dec f r with
      | some (p, r') => some (.neg p, r')
      | none => none
  | _ + 1, [_, _] => none
  | f + 1, true :: false :: false :: r =>
      match dec f r with
      | some (p, r₁) =>
          match dec f r₁ with
          | some (q, r₂) => some (.conj p q, r₂)
          | none => none
      | none => none
  | f + 1, true :: false :: true :: r =>
      match dec f r with
      | some (p, r₁) =>
          match dec f r₁ with
          | some (q, r₂) => some (.disj p q, r₂)
          | none => none
      | none => none
  | f + 1, true :: true :: false :: r =>
      match decUnary r with
      | some (i, r₁) =>
          match dec f r₁ with
          | some (p, r₂) => some (.all i p, r₂)
          | none => none
      | none => none
  | f + 1, true :: true :: true :: r =>
      match decUnary r with
      | some (i, r₁) =>
          match dec f r₁ with
          | some (p, r₂) => some (.ex i p, r₂)
          | none => none
      | none => none

/-- **The decoder reads a formula back off its code**, leaving the rest of the word untouched, as
soon as the fuel is at least the size of the formula. -/
theorem dec_enc_append : ∀ (p : QBF) (f : ℕ), p.size ≤ f → ∀ r : List Bool,
    dec f (enc p ++ r) = some (p, r) := by
  intro p
  induction p with
  | var i =>
      intro f hf r
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [size] at hf; omega⟩
      simp [enc, dec, decUnary_unary]
  | neg p ih =>
      intro f hf r
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [size] at hf; omega⟩
      have hg : p.size ≤ g := by simp [size] at hf; omega
      simp [enc, dec, ih g hg r]
  | conj p q ihp ihq =>
      intro f hf r
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [size] at hf; omega⟩
      have hp : p.size ≤ g := by simp [size] at hf; omega
      have hq : q.size ≤ g := by simp [size] at hf; omega
      have hass : enc (QBF.conj p q) ++ r =
          true :: false :: false :: (enc p ++ (enc q ++ r)) := by
        simp [enc]
      rw [hass]
      simp [dec, ihp g hp (enc q ++ r), ihq g hq r]
  | disj p q ihp ihq =>
      intro f hf r
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [size] at hf; omega⟩
      have hp : p.size ≤ g := by simp [size] at hf; omega
      have hq : q.size ≤ g := by simp [size] at hf; omega
      have hass : enc (QBF.disj p q) ++ r =
          true :: false :: true :: (enc p ++ (enc q ++ r)) := by
        simp [enc]
      rw [hass]
      simp [dec, ihp g hp (enc q ++ r), ihq g hq r]
  | all i p ih =>
      intro f hf r
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [size] at hf; omega⟩
      have hp : p.size ≤ g := by simp [size] at hf; omega
      have hass : enc (QBF.all i p) ++ r =
          true :: true :: false :: (unary i ++ (enc p ++ r)) := by
        simp [enc]
      rw [hass]
      simp [dec, decUnary_unary, ih g hp r]
  | ex i p ih =>
      intro f hf r
      obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp [size] at hf; omega⟩
      have hp : p.size ≤ g := by simp [size] at hf; omega
      have hass : enc (QBF.ex i p) ++ r =
          true :: true :: true :: (unary i ++ (enc p ++ r)) := by
        simp [enc]
      rw [hass]
      simp [dec, decUnary_unary, ih g hp r]

theorem dec_enc (p : QBF) : dec p.size (enc p) = some (p, []) := by
  have := dec_enc_append p p.size le_rfl []
  simpa using this

/-- The code is injective. -/
theorem enc_injective : Function.Injective enc := by
  intro p q hpq
  have hp := dec_enc_append p (max p.size q.size) (le_max_left _ _) []
  have hq := dec_enc_append q (max p.size q.size) (le_max_right _ _) []
  rw [hpq] at hp
  rw [hp] at hq
  have h2 : (p, ([] : List Bool)) = (q, ([] : List Bool)) := Option.some.inj hq
  exact congrArg Prod.fst h2

/-! ### The length of the code -/

/-- A formula of size `n` all of whose variables are below `v` has a code of length at most
`n * (v + 3)`. -/
theorem length_enc_le : ∀ (p : QBF) (v : ℕ), p.varBound ≤ v →
    (enc p).length ≤ p.size * (v + 3) := by
  intro p
  induction p with
  | var i =>
      intro v hv
      simp only [varBound] at hv
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil, length_unary]
      omega
  | neg p ih =>
      intro v hv
      have h := ih v hv
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil]
      have : (p.size + 1) * (v + 3) = p.size * (v + 3) + (v + 3) := by ring
      omega
  | conj p q ihp ihq =>
      intro v hv
      simp only [varBound] at hv
      have hp := ihp v (le_trans (le_max_left _ _) hv)
      have hq := ihq v (le_trans (le_max_right _ _) hv)
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil]
      have : (p.size + q.size + 1) * (v + 3) =
          p.size * (v + 3) + q.size * (v + 3) + (v + 3) := by ring
      omega
  | disj p q ihp ihq =>
      intro v hv
      simp only [varBound] at hv
      have hp := ihp v (le_trans (le_max_left _ _) hv)
      have hq := ihq v (le_trans (le_max_right _ _) hv)
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil]
      have : (p.size + q.size + 1) * (v + 3) =
          p.size * (v + 3) + q.size * (v + 3) + (v + 3) := by ring
      omega
  | all i p ih =>
      intro v hv
      simp only [varBound] at hv
      have hi : i + 1 ≤ v := le_trans (le_max_left _ _) hv
      have h := ih v (le_trans (le_max_right _ _) hv)
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil, length_unary]
      have : (p.size + 1) * (v + 3) = p.size * (v + 3) + (v + 3) := by ring
      omega
  | ex i p ih =>
      intro v hv
      simp only [varBound] at hv
      have hi : i + 1 ≤ v := le_trans (le_max_left _ _) hv
      have h := ih v (le_trans (le_max_right _ _) hv)
      simp only [enc, size, List.length_append, List.length_cons, List.length_nil, length_unary]
      have : (p.size + 1) * (v + 3) = p.size * (v + 3) + (v + 3) := by ring
      omega

end QBF

/-! ### `TQBF` as a language of words -/

open Complexity.Space in
/-- The language of the codes of true closed quantified Boolean formulas. -/
def tqbfLang : Language := fun w => ∃ p : QBF, QBF.enc p = w ∧ TQBF p

/-- A code lies in the language exactly when its formula is a true closed formula. -/
theorem tqbfLang_enc_iff (p : QBF) : tqbfLang (QBF.enc p) ↔ TQBF p := by
  constructor
  · rintro ⟨q, hq, hqt⟩
    rwa [QBF.enc_injective hq] at hqt
  · intro h
    exact ⟨p, rfl, h⟩

namespace QBF

open Complexity.Space

/-! ### The reduction as a map on words -/

/-- A bound on the variables of the reduction formula of an input of length `n`. -/
def varBoundOf (M : Machine) (s : ℕ → ℕ) (n : ℕ) : ℕ := (3 * kBound M s n + 5) * wBound M s n

/-- A bound on the length of the code of the reduction formula of an input of length `n`. -/
def wordBound (M : Machine) (s : ℕ → ℕ) (n : ℕ) : ℕ :=
  sizeBound M s n * (varBoundOf M s n + 3)

theorem varBound_machineF_le_varBoundOf (M : Machine) (s : ℕ → ℕ) (x : List Bool) :
    (machineF M x (s x.length)).varBound ≤ varBoundOf M s x.length := by
  refine le_trans (varBound_machineF_le M x (s x.length)) ?_
  refine Nat.mul_le_mul ?_ ?_
  · have := savitchDepth_le_kBound M s x
    omega
  · exact le_of_eq (cfgWidth_eq_wBound M s x)

/-- The code of the reduction formula of an input of length `n` is at most `wordBound M s n`
bits long. -/
theorem length_enc_machineF_le (M : Machine) (s : ℕ → ℕ) (x : List Bool) :
    (enc (machineF M x (s x.length))).length ≤ wordBound M s x.length := by
  refine le_trans (length_enc_le _ _ (varBound_machineF_le_varBoundOf M s x)) ?_
  exact Nat.mul_le_mul_right _ (size_machineF_le_sizeBound M s x)

theorem polyBound_varBoundOf (M : Machine) {s : ℕ → ℕ} (hs : PolyBound s) :
    PolyBound (varBoundOf M s) := by
  have hconst : ∀ c : ℕ, PolyBound (fun _ => c) := polyBound_const
  have hsucc : PolyBound (fun n => n + 1) := polyBound_id.add (hconst 1)
  have hw : PolyBound (wBound M s) :=
    (((hconst M.states).add hsucc).add hs).add hs
  have hk : PolyBound (kBound M s) :=
    (((hconst M.states).add hsucc).add ((hconst 2).mul (hs.add (hconst 1)))).add hs
  exact ((hconst 3).mul hk).add (hconst 5) |>.mul hw

theorem polyBound_wordBound (M : Machine) {s : ℕ → ℕ} (hs : PolyBound s) :
    PolyBound (wordBound M s) :=
  (polyBound_sizeBound M hs).mul ((polyBound_varBoundOf M hs).add (polyBound_const 3))

/-- **Every language in `NPSPACE` is mapped into `tqbfLang` by a map on words whose output is of
polynomially bounded length**: the code of the reduction formula.  What this does not say — and
what the `PSPACE`-hardness of `TQBF` needs on top of it — is that the map is computable in
polynomial time. -/
theorem npspace_polyLength_tqbfWord {L : Language} (h : NPSPACE L) :
    ∃ (f : List Bool → List Bool) (p : ℕ → ℕ), PolyBound p ∧
      ∀ x : List Bool, (f x).length ≤ p x.length ∧ (tqbfLang (f x) ↔ L x) := by
  obtain ⟨s, hs, M, hwf, hsp, hL⟩ := h
  refine ⟨fun x => enc (machineF M x (s x.length + 1)),
    wordBound M (fun n => s n + 1), polyBound_wordBound M (hs.add (polyBound_const 1)), ?_⟩
  intro x
  refine ⟨length_enc_machineF_le M (fun n => s n + 1) x, ?_⟩
  rw [tqbfLang_enc_iff]
  have hspx : M.SpaceBoundedOn x (s x.length + 1) := fun n c hc =>
    le_trans (hsp x n c hc) (Nat.le_succ _)
  rw [tqbf_machineF_iff hwf hspx (Nat.succ_pos _)]
  exact (hL x).symm

/-- The same for a language in `PSPACE`, which is a special case of `NPSPACE`. -/
theorem pspace_polyLength_tqbfWord {L : Language} (h : PSPACE L) :
    ∃ (f : List Bool → List Bool) (p : ℕ → ℕ), PolyBound p ∧
      ∀ x : List Bool, (f x).length ≤ p x.length ∧ (tqbfLang (f x) ↔ L x) :=
  npspace_polyLength_tqbfWord (npspace_of_pspace h)

end QBF

end Complexity.Qbf
