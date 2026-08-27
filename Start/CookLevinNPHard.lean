/-
# Cook–Levin: SAT is NP-complete, with nothing left over

`Start/CookLevinBound.lean` isolates the last missing step of the Cook–Levin argument as
`Complexity.StdUniformAcceptFamilies`: for every Cobham verifier `v` and every standard witness
bound `n ↦ a * (n + 1) ^ k` there is a P-uniform family of well-formed circuits whose output at
the input `x` is the verdict of `v` on the instance and the witness read off `x`.  This module
**proves that hypothesis**, and with it the Cook–Levin theorem.

The construction puts together the two halves built earlier.  `Start/UniformSegDec.lean` decodes
the two words off an arbitrary circuit input and presents them in the signal format;
`Start/UniformSigAll.lean` compiles the verifier — normalized to a well-formed term of two
arguments by `Complexity.shapeAt` — into a P-uniform family reading exactly that format.
`Complexity.Tseitin.decideSigE` stacks the second on the first and reads the verdict off the first
presence wire of the value signal.

Main definitions:

* `Complexity.Tseitin.pairBase`, `Complexity.Tseitin.pairDec` — the decoder for the instance and
  the witness;
* `Complexity.Tseitin.decideSigE` — a compiled family run on a decoder, with the verdict on top.

Main results:

* `Complexity.Tseitin.vals_pairDec` — **the decoder carries the signals of the two words read off
  the input**;
* `Complexity.stdUniformAcceptFamilies` — **the uniformity hypothesis holds**;
* `Complexity.npHard_SAT`, `Complexity.npComplete_SAT` — **SAT is NP-hard, and NP-complete**;
* `Complexity.peqNP_iff_inP_SAT` — hence `P = NP` if and only if SAT is in `P`.
-/

import Start.UniformSegDec
import Start.UniformSigNorm
import Start.CookLevinBound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### The decoder for two segments -/

/-- The two segment decoders side by side: the instance at the input positions `[0, 2n)` and the
witness at the positions `[2n, 2n + 2N)`. -/
def pairBase (n N : ℕ) : Circuit := stackC (segDec (2 * n) N) (segDec 0 n)

@[simp] theorem length_pairBase (n N : ℕ) : (pairBase n N).length = 5 * n + 5 * N := by
  simp only [pairBase, length_stackC, length_segDec]
  omega

theorem wf_pairBase (n N : ℕ) : wf (pairBase n N) :=
  wf_stackC (wf_segDec _ _) (wf_segDec _ _)

theorem vals_pairBase (x : Word) (n N : ℕ) :
    vals x (pairBase n N) = vals x (segDec 0 n) ++ vals x (segDec (2 * n) N) :=
  vals_stackC x (segDec 0 n) (wf_segDec _ _)

theorem getD_vals_pairBase_fst (x : Word) (n N : ℕ) {i : ℕ} (hi : i < 5 * n) :
    (vals x (pairBase n N)).getD i false = (vals x (segDec 0 n)).getD i false := by
  have hlen : (vals x (segDec 0 n)).length = 5 * n := by simp
  rw [vals_pairBase, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
    ← List.getD_eq_getElem?_getD]

theorem getD_vals_pairBase_snd (x : Word) (n N : ℕ) (i : ℕ) :
    (vals x (pairBase n N)).getD (5 * n + i) false
      = (vals x (segDec (2 * n) N)).getD i false := by
  have hlen : (vals x (segDec 0 n)).length = 5 * n := by simp
  rw [vals_pairBase, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
    ← List.getD_eq_getElem?_getD, show 5 * n + i - 5 * n = i from by omega]

/-- **The decoder**: the two segment decoders, with the two signals on top. -/
def pairDec (n N M : ℕ) : Circuit :=
  sigBlock (5 * n + 2 * N) (5 * n + 4 * N) N M ++
    (sigBlock (2 * n) (4 * n) n M ++ pairBase n N)

theorem length_pairDec (n N M : ℕ) (hn : n ≤ M) (hN : N ≤ M) :
    (pairDec n N M).length = 5 * n + 5 * N + 4 * M := by
  simp only [pairDec, List.length_append, length_sigBlock _ _ _ _ hn,
    length_sigBlock _ _ _ _ hN, length_pairBase]
  omega

theorem wf_pairDec (n N M : ℕ) : wf (pairDec n N M) := by
  have h1 : wf (sigBlock (2 * n) (4 * n) n M ++ pairBase n N) :=
    wf_sigBlock_append (wf_pairBase n N) (fun c hc => by rw [length_pairBase]; omega)
      (fun c hc => by rw [length_pairBase]; omega)
  have hlen1 : (sigBlock (2 * n) (4 * n) n M ++ pairBase n N).length
      = (sigBlock (2 * n) (4 * n) n M).length + (5 * n + 5 * N) := by
    simp only [List.length_append, length_pairBase]
  exact wf_sigBlock_append h1 (fun c hc => by rw [hlen1]; omega)
    (fun c hc => by rw [hlen1]; omega)

/-- **The decoder carries the signals of the two words read off the input.** -/
theorem vals_pairDec (x : Word) (n N M : ℕ) (hn : n ≤ M) (hN : N ≤ M) :
    vals x (pairDec n N M)
      = vals x (pairBase n N) ++ encSig M (inWord n x) ++ encSig M (inWordAt (2 * n) N x) := by
  have hlenB : (vals x (pairBase n N)).length = 5 * n + 5 * N := by simp
  -- the instance
  have e1 : vals x (sigBlock (2 * n) (4 * n) n M ++ pairBase n N)
      = vals x (pairBase n N) ++ encSig M (inWord n x) := by
    refine vals_sigBlock_append x (w := inWord n x)
      (fun c hc => by rw [length_pairBase]; omega)
      (fun c hc => by rw [length_pairBase]; omega) (fun c hc => ?_) (fun c hc => ?_)
      (by simpa using length_inWord_le n x) hn
    · rw [getD_vals_pairBase_fst x n N (by omega), getD_vals_segDec_pres x 0 n hc,
        inWordAt_zero]
    · rw [getD_vals_pairBase_fst x n N (by omega), getD_vals_segDec_val x 0 n hc,
        inWordAt_zero]
  -- the witness
  have hget : ∀ i, i < 5 * n + 5 * N →
      (vals x (sigBlock (2 * n) (4 * n) n M ++ pairBase n N)).getD i false
        = (vals x (pairBase n N)).getD i false := by
    intro i hi
    rw [e1, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]
  have hlen1 : (sigBlock (2 * n) (4 * n) n M ++ pairBase n N).length
      = 2 * M + (5 * n + 5 * N) := by
    simp only [List.length_append, length_pairBase, length_sigBlock _ _ _ _ hn]
  have e2 : vals x (pairDec n N M)
      = vals x (sigBlock (2 * n) (4 * n) n M ++ pairBase n N)
        ++ encSig M (inWordAt (2 * n) N x) := by
    refine vals_sigBlock_append x (w := inWordAt (2 * n) N x)
      (fun c hc => by rw [hlen1]; omega) (fun c hc => by rw [hlen1]; omega)
      (fun c hc => ?_) (fun c hc => ?_) (length_inWordAt_le _ _ _) hN
    · rw [hget _ (by omega), show 5 * n + 2 * N + c = 5 * n + (2 * N + c) from by omega,
        getD_vals_pairBase_snd x n N _, getD_vals_segDec_pres x (2 * n) N hc]
    · rw [hget _ (by omega), show 5 * n + 4 * N + c = 5 * n + (4 * N + c) from by omega,
        getD_vals_pairBase_snd x n N _, getD_vals_segDec_val x (2 * n) N hc]
  rw [e2, e1]

/-! ### Deciding on top of a decoder -/

/-- The compiled circuit `C` run on the wires of `D` from the wire `e` upwards, with one gate on
top reading the first presence bit of the value signal. -/
def decideSigE (C D : Circuit) (e w : ℕ) : Circuit :=
  Gate.conj (C.length + D.length - w) (C.length + D.length - w) :: (reroute D.length e C ++ D)

theorem wf_decideSigE {C D : Circuit} {e w : ℕ} (hC : wf C) (hD : wf D) (he : e ≤ D.length)
    (hin : inpsLt (D.length - e) C) (hw : 0 < w) (hwC : w ≤ C.length) :
    wf (decideSigE C D e w) := by
  refine ⟨?_, wf_reroute_append D hD e he C hC hin⟩
  have hlen : (reroute D.length e C ++ D).length = C.length + D.length := by simp
  rw [hlen]
  exact ⟨by omega, by omega⟩

theorem out_decideSigE (y : Word) {C D : Circuit} {e w : ℕ} (hC : wf C) (he : e ≤ D.length)
    (hin : inpsLt (D.length - e) C) (hwC : w ≤ C.length) :
    out y (decideSigE C D e w)
      = (topVals w (vals ((vals y D).drop e) C)).getD 0 false := by
  rw [decideSigE, out, vals_reroute_append y D e he C hC hin]
  simp only [gateVal, Bool.and_self]
  have hlenD : (vals y D).length = D.length := by simp
  have hlenC : (vals ((vals y D).drop e) C).length = C.length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), topVals,
    List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

end Tseitin

open Complexity.Tseitin

/-! ### The uniformity hypothesis holds -/

/-- **P-uniform compilation of verifiers, with a standard polynomial witness bound**: the
hypothesis isolated in `Start/CookLevinBound.lean` is a theorem. -/
theorem stdUniformAcceptFamilies : StdUniformAcceptFamilies := by
  intro v a k
  classical
  -- the witness bound and the normalized verifier
  set p : ℕ → ℕ := fun n => a * (n + 1) ^ k with hp
  have hpU : UnaryLen p := unaryLen_poly a k
  set v' : Cob := shapeAt 2 v with hv'
  have hshape : CobShape 2 v' := cobShape_shapeAt 2 v
  -- the width
  set kb : ℕ → ℕ := fun n => n + p n with hkb
  have hkbU : UnaryLen kb := unaryLen_id.add hpU
  set M : ℕ → ℕ := fun n => cobLen v' (kb n) + kb n + 1 with hM
  have hMU : UnaryLen M := ((unaryLen_cobLen hkbU v').add hkbU).succ
  obtain ⟨MT, hMT⟩ := hMU
  have hnM : ∀ n, n ≤ M n := by
    intro n
    simp only [hM, hkb]
    omega
  have hpM : ∀ n, p n ≤ M n := by
    intro n
    simp only [hM, hkb]
    omega
  -- the compiled verifier
  have hsig : SigUniformB 2 M kb v'.eval :=
    sigUniformB_of_cobShape hMT hshape kb hkbU (fun n => by simp only [hM]; omega)
  obtain ⟨cv, hcv⟩ := hsig
  -- the decoder
  set D : ℕ → Tseitin.Circuit := fun n => Tseitin.pairDec n (p n) (M n) with hD
  set E : ℕ → ℕ := fun n => 5 * n + 5 * p n with hE
  have hDlen : ∀ n, (D n).length = E n + 4 * M n := by
    intro n
    simp only [hD, hE]
    rw [Tseitin.length_pairDec n (p n) (M n) (hnM n) (hpM n)]
  have hEle : ∀ n, E n ≤ (D n).length := by
    intro n; rw [hDlen n]; omega
  have hin : ∀ n, Tseitin.inpsLt ((D n).length - E n) (cv n) := by
    intro n
    have h := hcv.inpC n
    rw [hDlen n, show E n + 4 * M n - E n = 2 * (2 * M n) from by omega]
    exact h
  refine ⟨fun n => Tseitin.decideSigE (cv n) (D n) (E n) (2 * M n), fun n => ?_, fun n x => ?_,
    ?_⟩
  · -- well formed
    exact Tseitin.wf_decideSigE (hcv.wfC n) (Tseitin.wf_pairDec _ _ _) (hEle n) (hin n)
      (by simp only [hM]; omega) (hcv.widthC n)
  · -- correctness
    have hdrop : (Tseitin.vals x (D n)).drop (E n)
        = Tseitin.encArgs (M n) [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] := by
      have hv := Tseitin.vals_pairDec x n (p n) (M n) (hnM n) (hpM n)
      have hlenB : (Tseitin.vals x (Tseitin.pairBase n (p n))).length = E n := by
        simp only [hE]
        simp
      rw [hD]
      simp only
      rw [hv, List.append_assoc, ← hlenB, List.drop_left]
      simp [Tseitin.encArgs]
    have hout := hcv.outC n [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] (by simp) (by
      intro u hu
      rcases List.mem_cons.1 hu with rfl | hu'
      · have := Tseitin.length_inWord_le n x
        simp only [hkb]
        omega
      · rcases List.mem_singleton.1 hu' with rfl
        have := Tseitin.length_inWordAt_le (2 * n) (p n) x
        simp only [hkb]
        omega)
    rw [Tseitin.out_decideSigE x (hcv.wfC n) (hEle n) (hin n) (hcv.widthC n), hdrop, hout]
    set w1 : Word := Tseitin.inWord n x with hw1
    set w2 : Word := Tseitin.inWordAt (2 * n) (p n) x with hw2
    have hget : (Tseitin.encSig (M n) (v'.eval [w1, w2])).getD 0 false
        = decide (v'.eval [w1, w2] ≠ []) := by
      rw [Tseitin.encSig, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by
          simp only [List.length_map, List.length_range]
          have := hnM n
          simp only [hM]
          omega), List.getElem?_map,
        List.getElem?_range (by simp only [hM]; omega)]
      cases hF : v'.eval [w1, w2] with
      | nil => simp
      | cons b w => simp
    rw [hget, hv', eval_shapeAt 2 v [w1, w2] (by simp)]
  · -- uniformity
    have hpairBase : CodeUniform (fun n => Tseitin.pairBase n (p n)) :=
      codeUniform_stack (codeUniform_segDec ((unaryLen_const 2).mul unaryLen_id) hpU)
        (codeUniform_segDec (unaryLen_const 0) unaryLen_id)
    have hb1 : UnaryLen (fun n => 2 * n) := (unaryLen_const 2).mul unaryLen_id
    have hb2 : UnaryLen (fun n => 4 * n) := (unaryLen_const 4).mul unaryLen_id
    have hb3 : UnaryLen (fun n => 5 * n + 2 * p n) :=
      ((unaryLen_const 5).mul unaryLen_id).add ((unaryLen_const 2).mul hpU)
    have hb4 : UnaryLen (fun n => 5 * n + 4 * p n) :=
      ((unaryLen_const 5).mul unaryLen_id).add ((unaryLen_const 4).mul hpU)
    have hMU' : UnaryLen M := ⟨MT, hMT⟩
    have hDu : CodeUniform D :=
      codeUniform_append (codeUniform_sigBlock hb3 hb4 hpU hMU')
        (codeUniform_append (codeUniform_sigBlock hb1 hb2 unaryLen_id hMU') hpairBase)
    obtain ⟨lenT, hlenT⟩ := exists_lenTerm hcv.codeC
    obtain ⟨ET, hET⟩ : UnaryLen E :=
      ((unaryLen_const 5).mul unaryLen_id).add ((unaryLen_const 5).mul hpU)
    have hcomp : CodeUniform (fun n =>
        Tseitin.reroute (D n).length (E n) (cv n) ++ D n) :=
      codeUniform_compose hcv.codeC hDu (eT := ET) hET
    have hidx : ∀ n, (cv n).length + (D n).length - 2 * M n
        = (cv n).length + (E n + 2 * M n) := by
      intro n
      rw [hDlen n]
      omega
    obtain ⟨idxT, hidxT⟩ : UnaryLen (fun n => (cv n).length + (E n + 2 * M n)) := by
      refine ⟨Cob.catL [lenT, ET, MT, MT], fun x => ?_⟩
      simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, hlenT x, hET x, hMT x, ← List.replicate_add]
      congr 1
      omega
    have hgate : CodeUniform (fun n =>
        [Tseitin.Gate.conj ((cv n).length + (D n).length - 2 * M n)
          ((cv n).length + (D n).length - 2 * M n)]) := by
      refine codeUniform_gate (t := 5) (aT := idxT) (bT := idxT) (fun _ => rfl) ?_ ?_ <;>
        · intro x
          simp only [CircCode.fld1, CircCode.fld2, hidx x.length]
          exact hidxT x
    exact codeUniform_append hgate hcomp

/-! ### Cook–Levin -/

/-- **SAT is NP-hard**, with no hypothesis left over. -/
theorem npHard_SAT : NPHard Sat.SAT := npHard_SAT_of_stdUniform stdUniformAcceptFamilies

/-- **The Cook–Levin theorem**: SAT is NP-complete. -/
theorem npComplete_SAT : NPComplete Sat.SAT := npComplete_SAT_of_stdUniform stdUniformAcceptFamilies

/-- `P = NP` if and only if SAT is in `P`. -/
theorem peqNP_iff_inP_SAT : PeqNP ↔ InP Sat.SAT :=
  peqNP_iff_inP_SAT_of_stdUniform stdUniformAcceptFamilies

end Complexity
