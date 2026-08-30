/-
**Forcing with finite oracle strings.**

A finite string `l : List Bool` is a partial description of an oracle: it says what the oracle does
below `l.length` and leaves the rest open.  An oracle `B` *extends* `l` when it agrees with it
there (`Lambda.Oracle.strAgree`), and `l` **forces** the value `y` for the computation `Φ_e(x)`
when every oracle extending `l` makes that computation converge to `y`
(`Lambda.Oracle.Forces`).

The use principle of `Start/OracleMachine.lean` says exactly that convergence is always forced by
a finite initial segment of the oracle (`Lambda.Oracle.exists_forces_of_mem`), and forcing is
preserved by lengthening the string (`Lambda.Oracle.Forces.mono`).  These two facts are what makes
the finite-extension constructions of degree theory work.
-/

import Start.OracleSound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Nat.Partrec (Code)

/-- The oracle `B` extends the finite string `l`. -/
def strAgree (l : List Bool) (B : ℕ → Bool) : Prop := ∀ n < l.length, B n = l.getD n false

/-- The finite string `l` forces the computation `Φ_e(x)` to converge to `y`. -/
def Forces (l : List Bool) (e x y : ℕ) : Prop := ∀ B : ℕ → Bool, strAgree l B → y ∈ Phi B e x

theorem getD_eq_of_prefix {l l' : List Bool} (h : l <+: l') {i : ℕ} (hi : i < l.length) :
    l.getD i false = l'.getD i false := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

theorem strAgree_of_prefix {l l' : List Bool} {B : ℕ → Bool} (h : l <+: l')
    (hB : strAgree l' B) : strAgree l B := by
  intro n hn
  have hn' : n < l'.length := lt_of_lt_of_le hn (h.length_le)
  rw [hB n hn', getD_eq_of_prefix h hn]

theorem Forces.mono {l l' : List Bool} {e x y : ℕ} (hpre : l <+: l') (h : Forces l e x y) :
    Forces l' e x y := fun B hB => h B (strAgree_of_prefix hpre hB)

theorem strAgree_segList (B : ℕ → Bool) (k : ℕ) : strAgree (segList B k) B := by
  intro n hn
  rw [segList_length] at hn
  rw [List.getD_eq_getElem?_getD, segList_getElem?]
  simp [hn]

/-- A string is a prefix of any long enough initial segment of an oracle extending it. -/
theorem prefix_segList_of_agree {l : List Bool} {B : ℕ → Bool} (hB : strAgree l B)
    {k : ℕ} (hk : l.length ≤ k) : l <+: segList B k := by
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simp [hk]) ?_
  intro i hi hi'
  have hlen : i < l.length := hi
  have hgetD : l.getD i false = l[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    rfl
  have hBi : B i = l[i] := by rw [hB i hlen, hgetD]
  rw [List.getElem_take]
  have : (segList B k)[i]'(by simpa using lt_of_lt_of_le hlen hk) = B i := by
    have h2 := segList_getElem? B k i
    rw [List.getElem?_eq_getElem (by simpa using lt_of_lt_of_le hlen hk)] at h2
    simpa [lt_of_lt_of_le hlen hk] using h2
  rw [this, hBi]

/-- **Convergence is forced by a finite part of the oracle.** -/
theorem exists_forces_of_mem {B : ℕ → Bool} {e x y : ℕ} (h : y ∈ Phi B e x) :
    ∃ k, Forces (segList B k) e x y := by
  obtain ⟨u, hu⟩ := Phi_of_agree h
  refine ⟨u, fun C hC => hu C ?_⟩
  intro n hn
  have := hC n (by simpa using hn)
  rw [this, List.getD_eq_getElem?_getD, segList_getElem?]
  simp [hn]

/-- If no extension of `l` forces a value for `Φ_e(x)`, then the computation diverges for every
oracle extending `l`. -/
theorem not_mem_of_no_forcing_extension {l : List Bool} {e x : ℕ}
    (h : ¬ ∃ p : List Bool × ℕ, l <+: p.1 ∧ Forces p.1 e x p.2)
    {B : ℕ → Bool} (hB : strAgree l B) (y : ℕ) : y ∉ Phi B e x := by
  intro hy
  obtain ⟨k, hk⟩ := exists_forces_of_mem hy
  refine h ⟨(segList B (max k l.length), y), ?_, ?_⟩
  · exact prefix_segList_of_agree hB (le_max_right _ _)
  · refine hk.mono ?_
    refine prefix_segList_of_agree (strAgree_segList B k) ?_
    simp

end Oracle
end Lambda
