/-
Reading a word off a **segment** of the circuit input.

`Start/WordCircuit.lean` reads a word off the first `2 * N` positions of the circuit input
(`Complexity.Tseitin.inWord`).  For the Cook–Levin reduction one needs *two* words read off two
disjoint segments of the same input — the instance and the witness — so this module repeats the
construction with an offset.

Main definitions:

* `Complexity.Tseitin.inWordAt` — the word read off the positions `[off, off + 2 * N)`.

Main results:

* `Complexity.Tseitin.exists_inputSigAt` — the signal reading a word off an input segment;
* `Complexity.Tseitin.inWord_eq_of_pinned` — if the input positions `2 * i` and `2 * i + 1`
  carry, for `i < |u|`, the bits `true` and `u i`, then the word read off is exactly `u`.
-/

import Start.WordCircuit

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-- The word encoded by the input positions `[off, off + 2 * N)`. -/
def inWordAt (off N : ℕ) (x : Word) : Word := inWord N (x.drop off)

theorem getD_drop_add (x : Word) (off k : ℕ) :
    (x.drop off).getD k false = x.getD (off + k) false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

@[simp] theorem inWordAt_zero (N : ℕ) (x : Word) : inWordAt 0 N x = inWord N x := by
  simp [inWordAt]

theorem length_inWordAt_le (off N : ℕ) (x : Word) : (inWordAt off N x).length ≤ N :=
  length_inWord_le N _

/-- **Every short enough word is read off some input segment**, whatever the bits before the
segment are. -/
theorem exists_inWordAt (off N : ℕ) (u : Word) (hu : u.length ≤ N) (pre : Word)
    (hpre : pre.length = off) : ∃ x : Word, x.take off = pre ∧ inWordAt off N x = u := by
  obtain ⟨z, hz⟩ := exists_inWord N u hu
  refine ⟨pre ++ z, ?_, ?_⟩
  · rw [← hpre, List.take_left]
  · rw [inWordAt, ← hpre, List.drop_left, hz]

/-- The signal reading a word off the input positions `[off, off + 2 * N)`. -/
theorem exists_inputSigAt (C : Circuit) (hC : wf C) (off N : ℕ) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧
      C'.length ≤ C.length + 2 * N + N * (N + 2) + N ∧ WHolds C' N ps bs (inWordAt off N) := by
  obtain ⟨C₁, iws, e₁, w₁, hleni, hszi, hiw⟩ :=
    exists_wire_list hC (2 * N) 1 (fun k x => x.getD (off + k) false)
      (fun D hD _ k _ => by
        obtain ⟨D', e, hw, hl, hh⟩ := exists_inp D hD (off + k)
        exact ⟨D', D.length, e, hw, by omega, hh⟩)
  obtain ⟨C₂, pws, e₂, w₂, hlenp, hszp, hpw⟩ :=
    exists_wire_list w₁ N (N + 2) (fun i x => decide (i < (inWordAt off N x).length))
      (fun D hD he i hi => by
        obtain ⟨D', w, e, hw, hs, hh⟩ :=
          exists_bigAnd hD (i + 1) ((List.range (i + 1)).map (fun j => iws.getD (2 * j) 0))
            (fun j x => x.getD (off + 2 * j) false) (fun j hj => by
              have hget : ((List.range (i + 1)).map (fun j => iws.getD (2 * j) 0)).getD j 0
                  = iws.getD (2 * j) 0 := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
                rfl
              rw [hget]
              exact (hiw (2 * j) (by omega)).mono he)
        refine ⟨D', w, e, hw, by omega, hh.congr fun x => ?_⟩
        have h := (inWord_pres N i (x.drop off) hi).symm
        simp only [getD_drop_add] at h
        exact h)
  obtain ⟨C₃, bws, e₃, w₃, hlenb, hszb, hbw⟩ :=
    exists_wire_list w₂ N 1 (fun i x => (inWordAt off N x).getD i false)
      (fun D hD he i hi => by
        obtain ⟨D', e, hw, hl, hh⟩ :=
          exists_conj hD ((hiw (2 * i + 1) (by omega)).mono (e₂.trans he))
            ((hpw i hi).mono he)
        refine ⟨D', D.length, e, hw, by omega, hh.congr fun x => ?_⟩
        simp only [inWordAt]
        rw [inWord_bit N i (x.drop off), getD_drop_add]
        try rfl)
  refine ⟨C₃, pws, bws, e₁.trans (e₂.trans e₃), w₃, ?_, hlenp, hlenb,
    fun x => length_inWordAt_le off N x, fun i hi => (hpw i hi).mono e₃, fun i hi => hbw i hi⟩
  have h₁ := e₁.length_le
  have h₂ := e₂.length_le
  omega

/-! ### Pinning the input positions -/

/-- **Pinning the input**: if the positions `2 * i` carry `true` and the positions `2 * i + 1`
carry the bits of `u`, for all `i < |u|`, then the word read off the first `2 * |u|` input
positions is exactly `u`. -/
theorem inWord_eq_of_pinned (u x : Word)
    (h : ∀ i, i < u.length → x.getD (2 * i) false = true ∧
      x.getD (2 * i + 1) false = u.getD i false) :
    inWord u.length x = u := by
  have hlen : (inWord u.length x).length = u.length := by
    refine le_antisymm (length_inWord_le _ _) ?_
    by_contra hlt₀
    have hlt := Nat.lt_of_not_le hlt₀
    set i := (inWord u.length x).length with hi
    have hiu : i < u.length := hlt
    have := inWord_pres u.length i x hiu
    have hall : (List.range (i + 1)).all (fun j => x.getD (2 * j) false) = true := by
      refine List.all_eq_true.2 fun j hj => ?_
      rw [List.mem_range] at hj
      exact (h j (by omega)).1
    rw [hall] at this
    simp only [decide_eq_true_eq] at this
    omega
  refine List.ext_getElem (by rw [hlen]) fun i h₁ h₂ => ?_
  have hiu : i < u.length := by rwa [hlen] at h₁
  have hb := inWord_bit u.length i x
  rw [(h i hiu).2] at hb
  have hlt : decide (i < (inWord u.length x).length) = true := by
    rw [hlen]; simp [hiu]
  rw [hlt, Bool.and_true] at hb
  have e₁ : (inWord u.length x)[i] = (inWord u.length x).getD i false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]
    rfl
  have e₂ : u[i] = u.getD i false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
    rfl
  rw [e₁, e₂, hb]

end Tseitin

end Complexity
