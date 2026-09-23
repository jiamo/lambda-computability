/-
**An enumeration of the polynomial-time oracle machines.**

A diagonalization has to run through the machines one after another, so it needs a surjection
`ℕ → Complexity.CobQ`.  The type is a *nested* inductive — the composition constructor carries a
`List CobQ` — so the `Countable` deriving handler does not apply to it; this file codes the terms
by hand instead, by the pairing function of `Nat` and the encoding of lists of naturals, and
proves the code injective.

* `Complexity.CobQ.code` — the code of a term, and `Complexity.CobQ.tag` — its constructor;
* `Complexity.CobQ.code_injective` — the code is injective;
* `Complexity.CobQ.instCountable` — hence the oracle machines are countable;
* `Complexity.CobQ.exists_enumeration` — hence they are enumerated by a surjection `ℕ → CobQ`.
-/

import Mathlib
import Start.OracleCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobQ

/-- The constructor of a term, as a number. -/
def tag : CobQ → ℕ
  | .proj _ => 0
  | .empty => 1
  | .app _ => 2
  | .smash => 3
  | .query => 4
  | .comp _ _ => 5
  | .bRec _ _ _ _ => 6

/-- The code of an oracle Cobham term: its constructor paired with the codes of its parts. -/
def code : CobQ → ℕ
  | .proj i => Nat.pair 0 i
  | .empty => Nat.pair 1 0
  | .app b => Nat.pair 2 (if b then 1 else 0)
  | .smash => Nat.pair 3 0
  | .query => Nat.pair 4 0
  | .comp f gs =>
      Nat.pair 5 (Nat.pair (code f) (Encodable.encode (gs.attach.map fun g => code g.1)))
  | .bRec g h₀ h₁ bd =>
      Nat.pair 6 (Nat.pair (code g) (Nat.pair (code h₀) (Nat.pair (code h₁) (code bd))))
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem g.2; omega)

@[simp] theorem code_proj (i : ℕ) : code (.proj i) = Nat.pair 0 i := by rw [code]
@[simp] theorem code_empty : code .empty = Nat.pair 1 0 := by rw [code]
@[simp] theorem code_app (b : Bool) : code (.app b) = Nat.pair 2 (if b then 1 else 0) := by
  rw [code]
@[simp] theorem code_smash : code .smash = Nat.pair 3 0 := by rw [code]
@[simp] theorem code_query : code .query = Nat.pair 4 0 := by rw [code]

theorem code_comp (f : CobQ) (gs : List CobQ) :
    code (.comp f gs) = Nat.pair 5 (Nat.pair (code f) (Encodable.encode (gs.map code))) := by
  rw [code]
  congr 2
  simp

theorem code_bRec (g h₀ h₁ bd : CobQ) :
    code (.bRec g h₀ h₁ bd)
      = Nat.pair 6 (Nat.pair (code g) (Nat.pair (code h₀) (Nat.pair (code h₁) (code bd)))) := by
  rw [code]

/-- The first component of the code is the constructor. -/
@[simp] theorem unpair_code_fst (t : CobQ) : (code t).unpair.1 = tag t := by
  cases t <;> simp [tag, code_comp, code_bRec]

/-- Pointwise injectivity of the code on the members of a list lifts to the list. -/
theorem list_eq_of_map_code {n : ℕ} {gs gs' : List CobQ}
    (ih : ∀ t t' : CobQ, sizeOf t ≤ n → code t = code t' → t = t')
    (hsz : ∀ g ∈ gs, sizeOf g ≤ n) (h : gs.map code = gs'.map code) : gs = gs' := by
  induction gs generalizing gs' with
  | nil =>
      cases gs' with
      | nil => rfl
      | cons g' gs' => simp at h
  | cons g gs ihg =>
      cases gs' with
      | nil => simp at h
      | cons g' gs' =>
          simp only [List.map_cons, List.cons.injEq] at h
          rw [ih g g' (hsz g (by simp)) h.1,
            ihg (fun g'' hg'' => hsz g'' (by simp [hg''])) h.2]

theorem code_injective_aux : ∀ (n : ℕ) (t t' : CobQ), sizeOf t ≤ n → code t = code t' → t = t' := by
  intro n
  induction n with
  | zero =>
      intro t t' ht _
      exfalso
      cases t <;> simp at ht
  | succ n ih =>
      intro t t' ht h
      have htag : tag t = tag t' := by
        rw [← unpair_code_fst, ← unpair_code_fst, h]
      cases t with
      | proj i =>
          cases t' with
          | proj j =>
              have hij : i = j := by simpa using h
              rw [hij]
          | _ => simp [tag] at htag
      | empty =>
          cases t' with
          | empty => rfl
          | _ => simp [tag] at htag
      | app b =>
          cases t' with
          | app b' =>
              have hb : (if b then (1 : ℕ) else 0) = (if b' then (1 : ℕ) else 0) := by
                simpa using h
              cases b <;> cases b' <;> simp_all
          | _ => simp [tag] at htag
      | smash =>
          cases t' with
          | smash => rfl
          | _ => simp [tag] at htag
      | query =>
          cases t' with
          | query => rfl
          | _ => simp [tag] at htag
      | comp f gs =>
          cases t' with
          | comp f' gs' =>
              rw [code_comp, code_comp] at h
              have h' := (Nat.pair_eq_pair.1 h).2
              have hf : code f = code f' := (Nat.pair_eq_pair.1 h').1
              have hgs : gs.map code = gs'.map code :=
                Encodable.encode_injective (Nat.pair_eq_pair.1 h').2
              have hszf : sizeOf f ≤ n := by simp at ht; omega
              have hszg : ∀ g ∈ gs, sizeOf g ≤ n := by
                intro g hg
                have := List.sizeOf_lt_of_mem hg
                simp at ht
                omega
              rw [list_eq_of_map_code (ih := ih) hszg hgs, ih f f' hszf hf]
          | _ => simp [tag] at htag
      | bRec g h₀ h₁ bd =>
          cases t' with
          | bRec g' h₀' h₁' bd' =>
              rw [code_bRec, code_bRec] at h
              have h1 := (Nat.pair_eq_pair.1 h).2
              have hg : code g = code g' := (Nat.pair_eq_pair.1 h1).1
              have h2 := (Nat.pair_eq_pair.1 h1).2
              have hh0 : code h₀ = code h₀' := (Nat.pair_eq_pair.1 h2).1
              have h3 := (Nat.pair_eq_pair.1 h2).2
              have hh1 : code h₁ = code h₁' := (Nat.pair_eq_pair.1 h3).1
              have hbd : code bd = code bd' := (Nat.pair_eq_pair.1 h3).2
              have hszg : sizeOf g ≤ n := by simp at ht; omega
              have hsz0 : sizeOf h₀ ≤ n := by simp at ht; omega
              have hsz1 : sizeOf h₁ ≤ n := by simp at ht; omega
              have hszbd : sizeOf bd ≤ n := by simp at ht; omega
              rw [ih g g' hszg hg, ih h₀ h₀' hsz0 hh0, ih h₁ h₁' hsz1 hh1, ih bd bd' hszbd hbd]
          | _ => simp [tag] at htag

/-- **The code of an oracle Cobham term determines the term.** -/
theorem code_injective : Function.Injective code :=
  fun t t' h => code_injective_aux (sizeOf t) t t' le_rfl h

instance instCountable : Countable CobQ := code_injective.countable

/-- **The polynomial-time oracle machines are enumerated**: there is a surjection from the
naturals onto the oracle Cobham terms, which is what a stage-wise diagonalization runs through. -/
theorem exists_enumeration : ∃ f : ℕ → CobQ, Function.Surjective f :=
  exists_surjective_nat CobQ

end CobQ

end Complexity
