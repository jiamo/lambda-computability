/-
# Reading a word off a segment of an *arbitrary* circuit input

`Start/UniformSigLang.lean` decodes a word from a circuit input that is *pinned*: the flag
positions are known to carry `true`, so the presence bits of the signal are constants.  The
Cook–Levin reduction needs more: the acceptance circuits of `Start/CookLevinBound.lean` are fed an
arbitrary input, off which two words are read — the instance, at the positions `[0, 2n)`, and the
witness, at the positions `[2n, 2n + 2p)`.  On such an input the presence bits are no longer
constants: the `c`-th one is the conjunction of the flags `0, …, c` of the segment.

This module builds the general decoder.  `Complexity.Tseitin.segDec off N` is a block of `5 * N`
gates: the flags of the segment, the running conjunctions of the flags (a rerouted copy of the
conjunction circuits `Complexity.CircCode.andCirc`), the bits of the segment, and the value bits.
Its wires `[2N, 3N)` carry the presence bits and its wires `[4N, 5N)` the value bits of
`Complexity.Tseitin.inWordAt off N`.  `Complexity.Tseitin.sigBlock` then copies a presence block
and a value block into the signal format, padding both with constants.

Main definitions:

* `Complexity.Tseitin.conj2Layer` — a layer of pointwise conjunctions of two blocks of wires;
* `Complexity.Tseitin.segDec` — the segment decoder;
* `Complexity.Tseitin.sigBlock` — the signal built from a presence block and a value block.

Main results:

* `Complexity.Tseitin.getD_vals_segDec_pres`, `Complexity.Tseitin.getD_vals_segDec_val` — **the
  decoder carries the presence and value bits of the word read off the segment**;
* `Complexity.Tseitin.vals_sigBlock_append` — the signal block carries the signal of that word;
* `Complexity.codeUniform_segDec`, `Complexity.codeUniform_sigBlock` — both are P-uniform.
-/

import Start.UniformSigLang
import Start.UniformAnd
import Start.InputSegment

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### A layer of pointwise conjunctions -/

/-- A layer of `m` conjunction gates: the gate `c` of the layer conjoins the gate `b₁ + c` with
the gate `b₂ + c` of the circuit underneath. -/
def conj2Layer (b1 b2 m : ℕ) : Circuit :=
  CircCode.layer (fun c => Gate.conj (b1 + c) (b2 + c)) m

@[simp] theorem length_conj2Layer (b1 b2 m : ℕ) : (conj2Layer b1 b2 m).length = m := by
  simp [conj2Layer]

theorem conj2Layer_succ (b1 b2 m : ℕ) :
    conj2Layer b1 b2 (m + 1) = Gate.conj (b1 + m) (b2 + m) :: conj2Layer b1 b2 m := rfl

theorem wf_conj2Layer_append {b1 b2 : ℕ} {C : Circuit} (hC : wf C) (m : ℕ)
    (h : ∀ c, c < m → b1 + c < C.length ∧ b2 + c < C.length) :
    wf (conj2Layer b1 b2 m ++ C) := by
  induction m with
  | zero => simpa [conj2Layer, CircCode.layer] using hC
  | succ m ih =>
      have hm := h m (Nat.lt_succ_self m)
      have hlen : (conj2Layer b1 b2 m ++ C).length = m + C.length := by simp
      rw [conj2Layer_succ, List.cons_append]
      refine ⟨?_, ih (fun c hc => h c (Nat.lt_succ_of_lt hc))⟩
      simp only [gateWf, hlen]
      exact ⟨by omega, by omega⟩

theorem inpsLt_conj2Layer_append {b1 b2 : ℕ} {C : Circuit} {w : ℕ} (hC : inpsLt w C) (m : ℕ) :
    inpsLt w (conj2Layer b1 b2 m ++ C) := by
  induction m with
  | zero => simpa [conj2Layer, CircCode.layer] using hC
  | succ m ih =>
      rw [conj2Layer_succ, List.cons_append]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact trivial
      · exact ih g hg'

/-- **The layer carries the pointwise conjunctions of the two blocks.** -/
theorem vals_conj2Layer_append (x : Word) {b1 b2 : ℕ} {C : Circuit} (m : ℕ)
    (h : ∀ c, c < m → b1 + c < C.length ∧ b2 + c < C.length) :
    vals x (conj2Layer b1 b2 m ++ C)
      = vals x C ++ (List.range m).map
          (fun c => (vals x C).getD (b1 + c) false && (vals x C).getD (b2 + c) false) := by
  induction m with
  | zero =>
      have hnil : conj2Layer b1 b2 0 = [] := rfl
      rw [hnil]
      simp
  | succ m ih =>
      have hm := h m (Nat.lt_succ_self m)
      have hlenC : (vals x C).length = C.length := by simp
      have hprev := ih (fun c hc => h c (Nat.lt_succ_of_lt hc))
      have hget : ∀ i, i < C.length →
          (vals x C ++ (List.range m).map
            (fun c => (vals x C).getD (b1 + c) false && (vals x C).getD (b2 + c) false)).getD i
              false = (vals x C).getD i false := by
        intro i hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      rw [conj2Layer_succ, List.cons_append, vals, hprev, List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil, List.append_assoc, gateVal, hget _ hm.1,
        hget _ hm.2]

/-! ### The segment decoder -/

/-- The flags of the segment: the gate `c` reads the input `off + 2c`. -/
def segFlags (off N : ℕ) : Circuit := inpLayer (fun c => off + 2 * min c N) N

/-- The flags of the segment with the running conjunctions of the flags on top. -/
def segPres (off N : ℕ) : Circuit :=
  reroute N 0 (CircCode.andCirc N) ++ segFlags off N

/-- The running conjunctions with the bits of the segment on top. -/
def segBits (off N : ℕ) : Circuit :=
  inpLayer (fun c => off + 2 * min c N + 1) N ++ segPres off N

/-- **The segment decoder**: `5 * N` gates, whose wires `[2N, 3N)` carry the presence bits and
whose wires `[4N, 5N)` carry the value bits of the word read off the input positions
`[off, off + 2N)`. -/
def segDec (off N : ℕ) : Circuit := conj2Layer (3 * N) (2 * N) N ++ segBits off N

@[simp] theorem length_segFlags (off N : ℕ) : (segFlags off N).length = N := by
  simp [segFlags]

@[simp] theorem length_segPres (off N : ℕ) : (segPres off N).length = 3 * N := by
  simp only [segPres, List.length_append, length_reroute, CircCode.length_andCirc,
    length_segFlags]
  omega

@[simp] theorem length_segBits (off N : ℕ) : (segBits off N).length = 4 * N := by
  simp only [segBits, List.length_append, length_inpLayer, length_segPres]
  omega

@[simp] theorem length_segDec (off N : ℕ) : (segDec off N).length = 5 * N := by
  simp only [segDec, List.length_append, length_conj2Layer, length_segBits]
  omega

theorem vals_segFlags (x : Word) (off N : ℕ) :
    vals x (segFlags off N)
      = (List.range N).map (fun c => x.getD (off + 2 * min c N) false) := by
  have h := vals_inpLayer_append (C := []) x (idx := fun c => off + 2 * min c N) N
  simpa [segFlags, vals] using h

theorem getD_vals_segFlags (x : Word) (off N : ℕ) {c : ℕ} (hc : c < N) :
    (vals x (segFlags off N)).getD c false = x.getD (off + 2 * c) false := by
  rw [vals_segFlags, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, show min c N = c from by omega]

/-- The conjunction circuits are well formed, the empty one included. -/
theorem wf_andCirc' (N : ℕ) : wf (CircCode.andCirc N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact trivial
  · exact CircCode.wf_andCirc N hN

theorem vals_segPres (x : Word) (off N : ℕ) :
    vals x (segPres off N)
      = vals x (segFlags off N) ++ vals (vals x (segFlags off N)) (CircCode.andCirc N) := by
  have hlen : (segFlags off N).length = N := length_segFlags off N
  have h := vals_reroute_append x (segFlags off N) 0 (Nat.zero_le _) (CircCode.andCirc N)
    (wf_andCirc' N) (by
      rw [hlen]
      simpa using CircCode.inpsLt_andCirc N)
  rw [hlen] at h
  simpa [segPres] using h

/-! ### The presence bits -/

theorem andPrefix_eq_all (z : Word) : ∀ c : ℕ,
    CircCode.andPrefix z c = (List.range (c + 1)).all (fun j => z.getD j false) := by
  intro c
  induction c with
  | zero => simp [CircCode.andPrefix]
  | succ c ih =>
      have hr : List.range (c + 1 + 1) = List.range (c + 1) ++ [c + 1] := List.range_succ
      rw [CircCode.andPrefix, ih, hr, List.all_append]
      simp

theorem all_range_congr {f g : ℕ → Bool} (k : ℕ) (h : ∀ j, j < k → f j = g j) :
    (List.range k).all f = (List.range k).all g := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hr : List.range (k + 1) = List.range k ++ [k] := List.range_succ
      rw [hr, List.all_append, List.all_append, ih (fun j hj => h j (by omega))]
      simp [h k (Nat.lt_succ_self k)]

/-- **The presence bits**: the wire `2N + c` of the decoder says that the word read off the
segment has more than `c` bits. -/
theorem getD_vals_segPres (x : Word) (off N : ℕ) {c : ℕ} (hc : c < N) :
    (vals x (segPres off N)).getD (2 * N + c) false
      = decide (c < (inWordAt off N x).length) := by
  set z : List Bool := vals x (segFlags off N) with hz
  have hzlen : z.length = N := by rw [hz]; simp
  rw [vals_segPres, ← hz, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hzlen, ← List.getD_eq_getElem?_getD,
    show 2 * N + c - N = N + c from by omega]
  have hand : (vals z (CircCode.andCirc N)).getD (N + c) false = CircCode.andPrefix z c :=
    CircCode.wval_andCirc_top z N N le_rfl c hc
  rw [hand, andPrefix_eq_all, inWordAt, inWord_pres N c (x.drop off) hc]
  refine all_range_congr (c + 1) (fun j hj => ?_)
  rw [hz, getD_vals_segFlags x off N (by omega), getD_drop_add]

theorem getD_vals_segBits_low (x : Word) (off N : ℕ) {i : ℕ} (hi : i < 3 * N) :
    (vals x (segBits off N)).getD i false = (vals x (segPres off N)).getD i false := by
  rw [segBits]
  exact vals_append_getD x _ (segPres off N) (by rw [length_segPres]; omega)

theorem getD_vals_segBits_bit (x : Word) (off N : ℕ) {c : ℕ} (hc : c < N) :
    (vals x (segBits off N)).getD (3 * N + c) false = x.getD (off + 2 * c + 1) false := by
  have hlen : (vals x (segPres off N)).length = 3 * N := by simp
  rw [segBits, vals_inpLayer_append, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), hlen, List.getElem?_map,
    List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some,
    show 3 * N + c - 3 * N = c from by omega, show min c N = c from by omega]

theorem vals_segDec (x : Word) (off N : ℕ) :
    vals x (segDec off N)
      = vals x (segBits off N) ++ (List.range N).map
          (fun c => (vals x (segBits off N)).getD (3 * N + c) false &&
            (vals x (segBits off N)).getD (2 * N + c) false) := by
  rw [segDec]
  exact vals_conj2Layer_append x N (fun c hc => by rw [length_segBits]; omega)

/-- **The presence bits of the decoder.** -/
theorem getD_vals_segDec_pres (x : Word) (off N : ℕ) {c : ℕ} (hc : c < N) :
    (vals x (segDec off N)).getD (2 * N + c) false
      = decide (c < (inWordAt off N x).length) := by
  rw [segDec, vals_append_getD x _ (segBits off N) (by rw [length_segBits]; omega),
    getD_vals_segBits_low x off N (by omega), getD_vals_segPres x off N hc]

/-- **The value bits of the decoder.** -/
theorem getD_vals_segDec_val (x : Word) (off N : ℕ) {c : ℕ} (hc : c < N) :
    (vals x (segDec off N)).getD (4 * N + c) false = (inWordAt off N x).getD c false := by
  have hlen : (vals x (segBits off N)).length = 4 * N := by simp
  rw [vals_segDec, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
    List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some, show 4 * N + c - 4 * N = c from by omega]
  rw [getD_vals_segBits_bit x off N hc, getD_vals_segBits_low x off N (by omega),
    getD_vals_segPres x off N hc, inWordAt, inWord_bit N c (x.drop off), getD_drop_add,
    Nat.add_assoc]

/-! ### Well-formedness -/

theorem wf_segFlags (off N : ℕ) : wf (segFlags off N) := by
  simpa [segFlags] using
    wf_inpLayer_append (C := []) (idx := fun c => off + 2 * min c N) trivial N

theorem inpsLt_segFlags (off N : ℕ) : inpsLt (off + 2 * N) (segFlags off N) := by
  have h := inpsLt_inpLayer_append (C := []) (idx := fun c => off + 2 * min c N)
    (w := off + 2 * N) (fun g hg => absurd hg (by simp)) N
    (fun c hc => by have : min c N ≤ c := Nat.min_le_left _ _; omega)
  simpa [segFlags] using h

theorem wf_segPres (off N : ℕ) : wf (segPres off N) := by
  have h : segPres off N = reroute (segFlags off N).length 0 (CircCode.andCirc N)
      ++ segFlags off N := by rw [segPres, length_segFlags]
  rw [h]
  exact wf_reroute_append _ (wf_segFlags off N) 0 (Nat.zero_le _) _ (wf_andCirc' N)
    (by rw [length_segFlags]; simpa using CircCode.inpsLt_andCirc N)

theorem inpsLt_segPres (off N : ℕ) : inpsLt (off + 2 * N) (segPres off N) := by
  intro g hg
  rw [segPres, List.mem_append] at hg
  rcases hg with hg | hg
  · obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
    cases g' <;> trivial
  · exact inpsLt_segFlags off N g hg

theorem wf_segBits (off N : ℕ) : wf (segBits off N) :=
  wf_inpLayer_append (wf_segPres off N) N

theorem inpsLt_segBits (off N : ℕ) : inpsLt (off + 2 * N + 1) (segBits off N) := by
  refine inpsLt_inpLayer_append (fun g hg => ?_) N
    (fun c hc => by have : min c N ≤ c := Nat.min_le_left _ _; omega)
  have := inpsLt_segPres off N g hg
  cases g <;> first | trivial | (simp_all [inpLt]; omega)

theorem wf_segDec (off N : ℕ) : wf (segDec off N) :=
  wf_conj2Layer_append (wf_segBits off N) N
    (fun c hc => by rw [length_segBits]; omega)

theorem inpsLt_segDec (off N : ℕ) : inpsLt (off + 2 * N + 1) (segDec off N) :=
  inpsLt_conj2Layer_append (inpsLt_segBits off N) N

/-! ### From a presence block and a value block to a signal -/

/-- **The signal block**: the presence block of `N` wires starting at `bp` and the value block of
`N` wires starting at `bv`, each padded with constants to the width `M`. -/
def sigBlock (bp bv N M : ℕ) : Circuit :=
  cstLayer false (M - N) ++ (selLayer bv N ++ (cstLayer false (M - N) ++ selLayer bp N))

theorem length_sigBlock (bp bv N M : ℕ) (h : N ≤ M) :
    (sigBlock bp bv N M).length = 2 * M := by
  simp only [sigBlock, List.length_append, length_cstLayer, length_selLayer]
  omega

theorem wf_sigBlock_append {bp bv N M : ℕ} {C : Circuit} (hC : wf C)
    (hp : ∀ c, c < N → bp + c < C.length) (hv : ∀ c, c < N → bv + c < C.length) :
    wf (sigBlock bp bv N M ++ C) := by
  have h1 : wf (selLayer bp N ++ C) :=
    wf_wireLayer_append hC N (fun c hc => hp c hc)
  have h2 : wf (cstLayer false (M - N) ++ (selLayer bp N ++ C)) :=
    wf_cstLayer_append _ h1 _
  have hlen2 : (cstLayer false (M - N) ++ (selLayer bp N ++ C)).length
      = (M - N) + N + C.length := by
    simp only [List.length_append, length_cstLayer, length_selLayer]
    omega
  have h3 : wf (selLayer bv N ++ (cstLayer false (M - N) ++ (selLayer bp N ++ C))) := by
    refine wf_wireLayer_append h2 N (fun c hc => ?_)
    have := hv c hc
    rw [hlen2]
    omega
  have h4 := wf_cstLayer_append (b := false)
    (C := selLayer bv N ++ (cstLayer false (M - N) ++ (selLayer bp N ++ C))) h3 (M - N)
  simpa [sigBlock, List.append_assoc] using h4

theorem inpsLt_sigBlock_append {bp bv N M w : ℕ} {C : Circuit} (hC : inpsLt w C) :
    inpsLt w (sigBlock bp bv N M ++ C) := by
  have h1 : inpsLt w (selLayer bp N ++ C) := inpsLt_wireLayer_append hC N
  have h2 := inpsLt_cstLayer_append (b := false) h1 (M - N)
  have h3 : inpsLt w (selLayer bv N ++ (cstLayer false (M - N) ++ (selLayer bp N ++ C))) :=
    inpsLt_wireLayer_append (idx := fun c => bv + c) h2 N
  have h4 := inpsLt_cstLayer_append (b := false) h3 (M - N)
  simpa [sigBlock, List.append_assoc] using h4

theorem map_range_pad_pres {w : Word} {N M : ℕ} (hw : w.length ≤ N) (hNM : N ≤ M) :
    (List.range N).map (fun c => decide (c < w.length)) ++ List.replicate (M - N) false
      = (List.range M).map (fun j => decide (j < w.length)) := by
  refine List.ext_getElem (by simp; omega) ?_
  intro i h1 h2
  have hi : i < M := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  by_cases hin : i < N
  · rw [List.getElem_append_left (by simpa using hin)]
    simp
  · rw [List.getElem_append_right (by simpa using hin)]
    simp only [List.getElem_replicate]
    exact (decide_eq_false (by omega)).symm

theorem map_range_pad_val {w : Word} {N M : ℕ} (hw : w.length ≤ N) (hNM : N ≤ M) :
    (List.range N).map (fun c => w.getD c false) ++ List.replicate (M - N) false
      = (List.range M).map (fun j => w.getD j false) := by
  refine List.ext_getElem (by simp; omega) ?_
  intro i h1 h2
  have hi : i < M := by simpa using h2
  simp only [List.getElem_map, List.getElem_range]
  by_cases hin : i < N
  · rw [List.getElem_append_left (by simpa using hin)]
    simp
  · rw [List.getElem_append_right (by simpa using hin)]
    have hnone : w[i]? = none := List.getElem?_eq_none (by omega)
    simp [hnone]

/-- **The signal block carries the signal of the word its two blocks describe.** -/
theorem vals_sigBlock_append (x : Word) {bp bv N M : ℕ} {C : Circuit} {w : Word}
    (hp : ∀ c, c < N → bp + c < C.length) (hv : ∀ c, c < N → bv + c < C.length)
    (hpv : ∀ c, c < N → (vals x C).getD (bp + c) false = decide (c < w.length))
    (hvv : ∀ c, c < N → (vals x C).getD (bv + c) false = w.getD c false)
    (hw : w.length ≤ N) (hNM : N ≤ M) :
    vals x (sigBlock bp bv N M ++ C) = vals x C ++ encSig M w := by
  have hlenC : (vals x C).length = C.length := by simp
  -- the presence layer
  have e1 : vals x (selLayer bp N ++ C)
      = vals x C ++ (List.range N).map (fun c => decide (c < w.length)) := by
    rw [selLayer, vals_wireLayer_append x N (fun c hc => hp c hc)]
    congr 1
    exact List.map_congr_left (fun c hc => hpv c (by simpa using hc))
  have e2 : vals x (cstLayer false (M - N) ++ (selLayer bp N ++ C))
      = vals x C ++ (List.range M).map (fun j => decide (j < w.length)) := by
    rw [vals_cstLayer_append, e1, List.append_assoc, map_range_pad_pres hw hNM]
  -- the value layer
  have hlen2 : (cstLayer false (M - N) ++ (selLayer bp N ++ C)).length
      = (M - N) + N + C.length := by
    simp only [List.length_append, length_cstLayer, length_selLayer]
    omega
  have hget2 : ∀ c, c < N →
      (vals x (cstLayer false (M - N) ++ (selLayer bp N ++ C))).getD (bv + c) false
        = w.getD c false := by
    intro c hc
    have hlt : bv + c < C.length := hv c hc
    rw [e2, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD, hvv c hc]
  have e3 : vals x (selLayer bv N ++ (cstLayer false (M - N) ++ (selLayer bp N ++ C)))
      = vals x C ++ (List.range M).map (fun j => decide (j < w.length))
        ++ (List.range N).map (fun c => w.getD c false) := by
    rw [selLayer, vals_wireLayer_append x N (fun c hc => by
      have := hv c hc
      rw [hlen2]
      omega), e2]
    congr 1
    refine List.map_congr_left (fun c hc => ?_)
    have hc' : c < N := by simpa using hc
    have := hget2 c hc'
    rw [e2] at this
    exact this
  have e4 : vals x (sigBlock bp bv N M ++ C)
      = vals x C ++ (List.range M).map (fun j => decide (j < w.length))
        ++ ((List.range N).map (fun c => w.getD c false) ++ List.replicate (M - N) false) := by
    have h := vals_cstLayer_append (C := selLayer bv N ++
      (cstLayer false (M - N) ++ (selLayer bp N ++ C))) x false (M - N)
    rw [e3] at h
    rw [show sigBlock bp bv N M ++ C = cstLayer false (M - N) ++ (selLayer bv N ++
        (cstLayer false (M - N) ++ (selLayer bp N ++ C))) from by
      simp [sigBlock, List.append_assoc], h, List.append_assoc]
  rw [e4, map_range_pad_val hw hNM, encSig, List.append_assoc]

end Tseitin

open Complexity.Tseitin

/-! ### Unary-computable length functions -/

/-- A constant length function is unary-computable. -/
theorem unaryLen_const (a : ℕ) : UnaryLen (fun _ => a) :=
  ⟨Cob.constT (List.replicate a true), by intro x; simp⟩

/-- Unary-computable length functions are closed under multiplication, by the smash function. -/
theorem UnaryLen.mul {k k' : ℕ → ℕ} (hk : UnaryLen k) (hk' : UnaryLen k') :
    UnaryLen (fun n => k n * k' n) := by
  obtain ⟨T, hT⟩ := hk
  obtain ⟨T', hT'⟩ := hk'
  refine ⟨.comp .smash [T, T'], fun x => ?_⟩
  simp [hT, hT']

/-- Unary-computable length functions are closed under truncated subtraction. -/
theorem UnaryLen.sub {k k' : ℕ → ℕ} (hk : UnaryLen k) (hk' : UnaryLen k') :
    UnaryLen (fun n => k n - k' n) := by
  obtain ⟨T, hT⟩ := hk
  obtain ⟨T', hT'⟩ := hk'
  refine ⟨.comp Cob.dropU [T', T], fun x => ?_⟩
  simp [hT, hT', List.drop_replicate]

/-- Every polynomial with natural coefficients is unary-computable. -/
theorem unaryLen_poly (a k : ℕ) : UnaryLen (fun n => a * (n + 1) ^ k) := by
  have hbase : UnaryLen (fun n => (n + 1) ^ k) := by
    induction k with
    | zero => simpa using unaryLen_const 1
    | succ k ih =>
        have := (unaryLen_id.succ).mul ih
        simpa [pow_succ, Nat.mul_comm] using this
  simpa using (unaryLen_const a).mul hbase

/-! ### Uniformity of the pieces -/

/-- **A P-uniform family may be reindexed** along a unary-computable function. -/
theorem codeUniform_reindex {cf : ℕ → Tseitin.Circuit} {N : ℕ → ℕ} (h : CodeUniform cf)
    (hN : UnaryLen N) : CodeUniform (fun n => cf (N n)) := by
  obtain ⟨gen, hgen⟩ := h
  obtain ⟨NT, hNT⟩ := hN
  refine ⟨.comp gen [NT], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hNT x]
  rw [hgen (List.replicate (N x.length) true), List.length_replicate]

/-- The value at `1^c` and `1^n 0 1^S` of the term reading a base off the parameter word. -/
theorem eval_baseIdxT {T : Cob} {f : ℕ → ℕ}
    (hT : ∀ x : Word, T.eval [x] = List.replicate (f x.length) true) (n c S : ℕ) (y : Word) :
    (Cob.comp T [.comp Cob.leadOnes [Cob.proj 2]]).eval [y, List.replicate c true, dmW n S]
      = List.replicate (f n) true := by
  have hlead : (Cob.comp Cob.leadOnes [Cob.proj 2]).eval
      [y, List.replicate c true, dmW n S] = List.replicate n true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [lead1_dmW]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, hlead]
  rw [hT (List.replicate n true), List.length_replicate]

/-- **A layer of pointwise conjunctions of two blocks is a P-uniform family.** -/
theorem codeUniform_conj2Layer {b1 b2 m : ℕ → ℕ} (hb1 : UnaryLen b1) (hb2 : UnaryLen b2)
    (hm : UnaryLen m) : CodeUniform (fun n => Tseitin.conj2Layer (b1 n) (b2 n) (m n)) := by
  obtain ⟨b1T, hb1T⟩ := hb1
  obtain ⟨b2T, hb2T⟩ := hb2
  obtain ⟨mT, hmT⟩ := hm
  set S : ℕ → ℕ := fun n => b1 n + b2 n with hS
  set sT : Cob := Cob.catL [b1T, b2T] with hsTdef
  have hsT : ∀ x : Word, sT.eval [x] = List.replicate (S x.length) true := by
    intro x
    simp only [hsTdef, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, hb1T x, hb2T x, ← List.replicate_add, hS]
  set lenT : Cob := .comp .smash [Cob.proj 0, Cob.constT [true]] with hlenT
  have hlenTn : ∀ x : Word, lenT.eval [x] = List.replicate x.length true := by
    intro x; simp [hlenT]
  set padT : Cob := Cob.catL [lenT, Cob.constT [false], sT] with hpadT
  have hpadTn : ∀ x : Word, padT.eval [x] = dmW x.length (S x.length) := by
    intro x
    simp only [hpadT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_constT, hlenTn x, hsT x]
    simp [dmW]
  have hidx : ∀ (T : Cob) (f : ℕ → ℕ),
      (∀ x : Word, T.eval [x] = List.replicate (f x.length) true) → ∀ (n c : ℕ) (y : Word),
      (Cob.comp Cob.concat [.comp T [.comp Cob.leadOnes [Cob.proj 2]], Cob.proj 1]).eval
        [y, List.replicate c true, dmW n (S n)] = List.replicate (f n + c) true := by
    intro T f hT n c y
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat,
      eval_baseIdxT hT n c (S n) y, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero,
      ← List.replicate_add]
  refine codeUniform_layerP (K := 11) (cnt := mT) (padT := padT) (pw := fun n => dmW n (S n))
    (blkT := CircCode.tokTerm 5
      (.comp Cob.concat [.comp b1T [.comp Cob.leadOnes [Cob.proj 2]], Cob.proj 1])
      (.comp Cob.concat [.comp b2T [.comp Cob.leadOnes [Cob.proj 2]], Cob.proj 1]))
    (tmpl := fun n c => Tseitin.Gate.conj (b1 n + c) (b2 n + c)) hmT hpadTn ?_ ?_
  · intro n y c
    exact CircCode.eval_tokTerm (g := Tseitin.Gate.conj (b1 n + c) (b2 n + c))
      (hidx b1T b1 hb1T n c y) (hidx b2T b2 hb2T n c y)
  · intro n c l hc
    rw [CircCode.length_encGate]
    simp only [CircCode.tag, CircCode.fld1, CircCode.fld2, length_dmW, hS]
    omega

/-- **The layer reading the flags, or the bits, of a segment of the input is P-uniform.** -/
theorem codeUniform_segInpLayer {off N m : ℕ → ℕ} (d : ℕ) (hoff : UnaryLen off)
    (hN : UnaryLen N) (hm : UnaryLen m) :
    CodeUniform (fun n => Tseitin.inpLayer (fun c => off n + 2 * min c (N n) + d) (m n)) := by
  obtain ⟨offT, hoffT⟩ := hoff
  obtain ⟨NT, hNT⟩ := hN
  obtain ⟨mT, hmT⟩ := hm
  set S : ℕ → ℕ := fun n => off n + 2 * N n + d with hS
  set sT : Cob := Cob.catL [offT, NT, NT, Cob.constT (List.replicate d true)] with hsTdef
  have hsT : ∀ x : Word, sT.eval [x] = List.replicate (S x.length) true := by
    intro x
    simp only [hsTdef, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_constT, hoffT x, hNT x, ← List.replicate_add,
      hS]
    congr 1
    omega
  set A : Cob := .comp Cob.dropU [.comp NT [.comp Cob.leadOnes [Cob.proj 2]], Cob.proj 1] with hA
  set B : Cob := .comp Cob.dropU [A, Cob.proj 1] with hB
  refine codeUniform_inpLayer (idx := fun n c => off n + 2 * min c (N n) + d) (S := S)
    (fun n c => by
      have : min c (N n) ≤ N n := Nat.min_le_right _ _
      simp only [hS]
      omega)
    hmT hsT
    (idxT := Cob.catL [.comp offT [.comp Cob.leadOnes [Cob.proj 2]], B, B,
      Cob.constT (List.replicate d true)]) ?_
  intro n c y
  have hAv : A.eval [y, List.replicate c true, dmW n (S n)]
      = List.replicate (c - N n) true := by
    simp only [hA, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU,
      eval_baseIdxT hNT n c (S n) y, Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero,
      List.length_replicate, List.drop_replicate]
  have hBv : B.eval [y, List.replicate c true, dmW n (S n)]
      = List.replicate (min c (N n)) true := by
    simp only [hB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, hAv,
      Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, List.length_replicate,
      List.drop_replicate]
    congr 1
    omega
  simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.append_nil, Cob.eval_constT, hBv, eval_baseIdxT hoffT n c (S n) y,
    ← List.replicate_add]
  congr 1
  omega

/-- **The segment decoder is a P-uniform family.** -/
theorem codeUniform_segDec {off N : ℕ → ℕ} (hoff : UnaryLen off) (hN : UnaryLen N) :
    CodeUniform (fun n => Tseitin.segDec (off n) (N n)) := by
  have hflags : CodeUniform (fun n => Tseitin.segFlags (off n) (N n)) := by
    have h := codeUniform_segInpLayer (off := off) (N := N) (m := N) 0 hoff hN hN
    have heq : (fun n => Tseitin.inpLayer (fun c => off n + 2 * min c (N n) + 0) (N n))
        = fun n => Tseitin.segFlags (off n) (N n) := by
      funext n
      simp [Tseitin.segFlags]
    rwa [heq] at h
  have hpres : CodeUniform (fun n => Tseitin.segPres (off n) (N n)) := by
    have hcomp := codeUniform_compose (e := fun _ => 0)
      (codeUniform_reindex codeUniform_andCirc hN) hflags
      (eT := .empty) (fun x => by simp)
    have heq : (fun n => Tseitin.reroute (Tseitin.segFlags (off n) (N n)).length 0
        (CircCode.andCirc (N n)) ++ Tseitin.segFlags (off n) (N n))
        = fun n => Tseitin.segPres (off n) (N n) := by
      funext n
      rw [Tseitin.segPres, Tseitin.length_segFlags]
    rwa [heq] at hcomp
  have hbits : CodeUniform (fun n => Tseitin.segBits (off n) (N n)) := by
    have h := codeUniform_segInpLayer (off := off) (N := N) (m := N) 1 hoff hN hN
    exact codeUniform_append h hpres
  have hconj : CodeUniform (fun n => Tseitin.conj2Layer (3 * N n) (2 * N n) (N n)) :=
    codeUniform_conj2Layer ((unaryLen_const 3).mul hN) ((unaryLen_const 2).mul hN) hN
  exact codeUniform_append hconj hbits

/-- **The signal block is a P-uniform family.** -/
theorem codeUniform_sigBlock {bp bv N M : ℕ → ℕ} (hbp : UnaryLen bp) (hbv : UnaryLen bv)
    (hN : UnaryLen N) (hM : UnaryLen M) :
    CodeUniform (fun n => Tseitin.sigBlock (bp n) (bv n) (N n) (M n)) := by
  obtain ⟨padT, hpadT⟩ := hM.sub hN
  obtain ⟨bpT, hbpT⟩ := hbp
  obtain ⟨bvT, hbvT⟩ := hbv
  obtain ⟨NT, hNT⟩ := hN
  set Sf : ℕ → ℕ := fun n => bp n + bv n with hSf
  obtain ⟨sT, hsT⟩ : UnaryLen Sf := ⟨Cob.catL [bpT, bvT], fun x => by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, hbpT x, hbvT x, ← List.replicate_add, hSf]⟩
  have hcst : CodeUniform (fun n => Tseitin.cstLayer false (M n - N n)) :=
    codeUniform_cstLayerU false hpadT
  have hselp : CodeUniform (fun n => Tseitin.selLayer (bp n) (N n)) :=
    codeUniform_selLayer (S := Sf) (fun n => by simp only [hSf]; omega) hbpT hNT hsT
  have hselv : CodeUniform (fun n => Tseitin.selLayer (bv n) (N n)) :=
    codeUniform_selLayer (S := Sf) (fun n => by simp only [hSf]; omega) hbvT hNT hsT
  exact codeUniform_append hcst (codeUniform_append hselv (codeUniform_append hcst hselp))

end Complexity
