/-
**Oracle machines and relative computability.**

A machine with oracle `A : ℕ → Bool` is an ordinary partial recursive code `c` which is run on
inputs of the form `Nat.pair sigma x`, where `sigma` codes a finite initial segment of the oracle
(see `Start/OracleSegment.lean`).  Running the machine means searching, over all pairs
`(fuel, segment length)`, for the first stage at which the code converges; the value found is the
value of the oracle computation:

```
evalOracle A c x = Nat.rfindOpt fun s => Code.evaln s.unpair.1 c (Nat.pair (segNum A s.unpair.2) x)
```

Because the search is bounded by the stage number, only finitely much of the oracle is consulted
before a value is produced.  That is the **use principle**, `Lambda.Oracle.evalOracle_of_agree`:
a converging oracle computation keeps its value if the oracle is changed only above the use.

* `Lambda.Oracle.oracleStep`, `Lambda.Oracle.evalOracle`, `Lambda.Oracle.Phi` — the stage function,
  the oracle computation of a code, and the indexed family `Φ_e^A`;
* `Lambda.Oracle.mem_rfindOpt_iff` — the least-witness description of `Nat.rfindOpt`;
* `Lambda.Oracle.evalOracle_of_agree`, `Lambda.Oracle.evalOracle_eq_of_agree` — the use principle,
  in the "some value survives" and in the "whole computation survives" form;
* `Lambda.Oracle.Phi_of_agree` — the same statement for the indexed family.
-/

import Start.OracleSegment

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)

/-- The least-witness description of `Nat.rfindOpt`. -/
theorem mem_rfindOpt_iff {f : ℕ → Option ℕ} {y : ℕ} :
    y ∈ Nat.rfindOpt f ↔ ∃ s, f s = some y ∧ ∀ m < s, f m = none := by
  have key : Nat.rfindOpt f
      = (Nat.rfind (fun n => ((f n).isSome : Bool))).bind (fun n => (f n : Part ℕ)) := rfl
  rw [key]
  constructor
  · intro h
    rw [Part.mem_bind_iff] at h
    obtain ⟨s, hs, hy⟩ := h
    have hs' := Nat.mem_rfind.mp hs
    refine ⟨s, by simpa using hy, fun m hm => ?_⟩
    have hm' : (f m).isSome = false := by
      have := hs'.2 (m := m) hm
      simpa using this
    simpa using hm'
  · rintro ⟨s, hs, hlt⟩
    rw [Part.mem_bind_iff]
    refine ⟨s, Nat.mem_rfind.mpr ⟨by simp [hs], ?_⟩, by simp [hs]⟩
    intro m hm
    simp [hlt m hm]

/-- One stage of an oracle computation: the stage number `s` provides both the fuel
`s.unpair.1` and the length `s.unpair.2` of the oracle segment handed to the code. -/
def oracleStep (A : ℕ → Bool) (c : Code) (x s : ℕ) : Option ℕ :=
  Code.evaln s.unpair.1 c (Nat.pair (segNum A s.unpair.2) x)

/-- The partial function computed by the code `c` with oracle `A`. -/
def evalOracle (A : ℕ → Bool) (c : Code) (x : ℕ) : Part ℕ :=
  Nat.rfindOpt (oracleStep A c x)

/-- The `e`-th oracle machine with oracle `A`: the standard indexing `Φ_e^A` of the partial
functions computable relative to `A`. -/
def Phi (A : ℕ → Bool) (e : ℕ) (x : ℕ) : Part ℕ :=
  evalOracle A (ofNat Code e) x

@[simp] theorem Phi_encode (A : ℕ → Bool) (c : Code) (x : ℕ) :
    Phi A (encode c) x = evalOracle A c x := by
  simp [Phi]

theorem mem_evalOracle_iff {A : ℕ → Bool} {c : Code} {x y : ℕ} :
    y ∈ evalOracle A c x ↔
      ∃ s, oracleStep A c x s = some y ∧ ∀ m < s, oracleStep A c x m = none :=
  mem_rfindOpt_iff

/-- A converging oracle computation converges at some stage. -/
theorem exists_stage_of_mem_evalOracle {A : ℕ → Bool} {c : Code} {x y : ℕ}
    (h : y ∈ evalOracle A c x) : ∃ s, oracleStep A c x s = some y :=
  ⟨_, (mem_evalOracle_iff.1 h).choose_spec.1⟩

/-- The stage `s` of an oracle computation only consults the oracle below `s`. -/
theorem oracleStep_congr {A B : ℕ → Bool} {c : Code} {x s u : ℕ} (hsu : s < u)
    (h : ∀ n < u, A n = B n) : oracleStep A c x s = oracleStep B c x s := by
  have hle : s.unpair.2 ≤ s := Nat.unpair_right_le s
  have : segNum A s.unpair.2 = segNum B s.unpair.2 :=
    segNum_congr fun n hn => h n (lt_of_lt_of_le hn (le_trans hle (le_of_lt hsu)))
  simp [oracleStep, this]

/-- **The use principle.**  A converging oracle computation only consults a finite part of the
oracle, and keeps its value if the oracle is changed above that part. -/
theorem evalOracle_of_agree {A : ℕ → Bool} {c : Code} {x y : ℕ} (h : y ∈ evalOracle A c x) :
    ∃ u, ∀ B : ℕ → Bool, (∀ n < u, A n = B n) → y ∈ evalOracle B c x := by
  obtain ⟨s, hs, hlt⟩ := mem_evalOracle_iff.1 h
  refine ⟨s + 1, fun B hB => mem_evalOracle_iff.2 ⟨s, ?_, ?_⟩⟩
  · rw [← oracleStep_congr (Nat.lt_succ_self s) hB]; exact hs
  · intro m hm
    rw [← oracleStep_congr (lt_trans hm (Nat.lt_succ_self s)) hB]
    exact hlt m hm

/-- The use principle for the indexed family. -/
theorem Phi_of_agree {A : ℕ → Bool} {e x y : ℕ} (h : y ∈ Phi A e x) :
    ∃ u, ∀ B : ℕ → Bool, (∀ n < u, A n = B n) → y ∈ Phi B e x :=
  evalOracle_of_agree h

/-- Two oracles that agree everywhere below the use give the same computation; here is the form
in which the oracle is only changed above a bound that works for *both* directions. -/
theorem evalOracle_eq_of_agree {A B : ℕ → Bool} {c : Code} {x : ℕ}
    (h : ∀ n, A n = B n) : evalOracle A c x = evalOracle B c x := by
  have : A = B := funext h
  subst this
  rfl

end Oracle
end Lambda
