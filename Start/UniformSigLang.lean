/-
# From the compiler to languages: every Cobham-decided language is P-uniformly decidable

`Start/UniformSigAll.lean` compiles every well-formed Cobham term into a P-uniform family of
circuits, presented in the *signal* format: the circuit inputs are the argument signals, and the
topmost wires carry the signal of the value.  `Start/UniformDecide.lean` asks for something else —
a family whose input presents a word in the *pinned* format of `Complexity.Tseitin.inWord`, and
whose single output wire says whether the word is in the language.  This module builds the bridge.

Two pieces of plumbing are needed.  `Complexity.Tseitin.sigInC n m` is the decoder: a layer of
`2 * m` gates which, from an input pinning a word of length `n`, produces the signal of that word
at width `m` — its presence bits are constants, since the length of the word is `n` whatever the
input is, and its value bits read the odd positions of the input.  `Complexity.Tseitin.decideSigC`
then runs the compiled circuit on the decoded signal and puts one gate on top, reading the first
presence bit of the value signal: that bit says exactly that the value is nonempty.

Main definitions:

* `Complexity.Tseitin.sigInC` — the decoder from a pinned input to a signal;
* `Complexity.Tseitin.decideSigC` — the deciding circuit.

Main results:

* `Complexity.Tseitin.vals_sigInC` — **the decoder carries the signal of the word its input pins**;
* `Complexity.codeUniform_cstLayerU`, `Complexity.codeUniform_oddInpLayer`,
  `Complexity.codeUniform_sigInC` — the decoder is P-uniform;
* `Complexity.pUniformDecidable_of_sigUniformB` — **a language whose acceptance is computed by a
  realized word function is decided by a P-uniform family**;
* `Complexity.pUniformDecidable_of_cobShape`, `Complexity.polyManyOne_SAT_of_cobShape` — hence the
  language of a well-formed Cobham term is P-uniformly decidable, and **reduces to SAT in
  polynomial time**.
-/

import Start.UniformSigAll
import Start.UniformDecide

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### The decoder -/

theorem vals_cstLayer_append (x : Word) (b : Bool) {C : Circuit} (m : ℕ) :
    vals x (cstLayer b m ++ C) = vals x C ++ List.replicate m b := by
  induction m with
  | zero => simp [cstLayer, CircCode.layer]
  | succ m ih =>
      rw [cstLayer_succ, List.cons_append, vals, ih]
      simp only [gateVal, List.append_assoc]
      congr 1
      exact (List.replicate_succ' (n := m) (a := b)).symm

theorem wf_cstLayer_append (b : Bool) {C : Circuit} (hC : wf C) (m : ℕ) :
    wf (cstLayer b m ++ C) := by
  induction m with
  | zero => simpa [cstLayer, CircCode.layer] using hC
  | succ m ih =>
      rw [cstLayer_succ, List.cons_append]
      exact ⟨trivial, ih⟩

theorem inpsLt_cstLayer_append (b : Bool) {C : Circuit} {w : ℕ} (hC : inpsLt w C) (m : ℕ) :
    inpsLt w (cstLayer b m ++ C) := by
  induction m with
  | zero => simpa [cstLayer, CircCode.layer] using hC
  | succ m ih =>
      rw [cstLayer_succ, List.cons_append]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact trivial
      · exact ih g hg'

/-- **The decoder**: from a circuit input pinning a word of length `n`, the signal of that word at
width `m`, carried by `2 * m` gates.  The presence bits are constants — the word pinned into the
input has length `n` whatever the input is — and the value bits read the odd positions of the
input. -/
def sigInC (n m : ℕ) : Circuit :=
  cstLayer false (m - n) ++ (inpLayer (fun j => 2 * min j n + 1) n ++
    (cstLayer false (m - n) ++ cstLayer true n))

theorem length_sigInC (n m : ℕ) (h : n ≤ m) : (sigInC n m).length = 2 * m := by
  simp only [sigInC, List.length_append, length_cstLayer, length_inpLayer]
  omega

theorem wf_sigInC (n m : ℕ) : wf (sigInC n m) :=
  wf_cstLayer_append _ (wf_inpLayer_append (wf_cstLayer_append _ (wf_cstLayer _ _) _) _) _

theorem inpsLt_sigInC (n m : ℕ) : inpsLt (2 * n) (sigInC n m) := by
  refine inpsLt_cstLayer_append _ (inpsLt_inpLayer_append
    (inpsLt_cstLayer_append _ (inpsLt_cstLayer _ _ _) _) _ ?_) _
  intro c hc
  have : min c n = c := by omega
  omega

/-- **The decoder carries the signal of the word its input pins.** -/
theorem vals_sigInC {n m : ℕ} (y : Word) (h : n ≤ m) (hy : Pinned n y) :
    vals y (sigInC n m) = encSig m (inWord n y) := by
  have hlen : (inWord n y).length = n := by
    rw [inWord_of_pinned n y hy]; simp
  rw [sigInC, vals_cstLayer_append, vals_inpLayer_append, vals_cstLayer_append, vals_cstLayer,
    encSig]
  have h1 : (List.range m).map (fun j => decide (j < (inWord n y).length))
      = List.replicate n true ++ List.replicate (m - n) false := by
    rw [hlen]
    refine List.ext_getElem (by simp; omega) ?_
    intro i h1 h2
    have hi : i < m := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    by_cases hin : i < n
    · rw [List.getElem_append_left (by simpa using hin)]
      simp [hin]
    · rw [List.getElem_append_right (by simpa using hin)]
      simp [hin]
  have h2 : (List.range m).map (fun j => (inWord n y).getD j false)
      = (List.range n).map (fun c => y.getD (2 * min c n + 1) false)
        ++ List.replicate (m - n) false := by
    refine List.ext_getElem (by simp; omega) ?_
    intro i h1 h2
    have hi : i < m := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    by_cases hin : i < n
    · rw [List.getElem_append_left (by simpa using hin)]
      have hmin : min i n = i := by omega
      simp only [List.getElem_map, List.getElem_range, hmin]
      rw [inWord_of_pinned n y hy, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hin]
      rfl
    · rw [List.getElem_append_right (by simpa using hin)]
      have hnone : (inWord n y)[i]? = none := List.getElem?_eq_none (by omega)
      simp [hnone]
  rw [h1, h2]
  simp [List.append_assoc]

/-! ### The deciding circuit -/

/-- **The deciding circuit**: the compiled circuit `C`, run on the decoded signal `D`, with one
gate on top reading the first presence bit of the value signal. -/
def decideSigC (C D : Circuit) (w : ℕ) : Circuit :=
  Gate.conj (C.length + D.length - w) (C.length + D.length - w) :: (reroute D.length 0 C ++ D)

theorem wf_decideSigC {C D : Circuit} {w : ℕ} (hC : wf C) (hD : wf D)
    (hin : inpsLt D.length C) (hw : 0 < w) (hwC : w ≤ C.length) : wf (decideSigC C D w) := by
  refine ⟨?_, wf_reroute_append D hD 0 (Nat.zero_le _) C hC (by simpa using hin)⟩
  have hlen : (reroute D.length 0 C ++ D).length = C.length + D.length := by simp
  rw [hlen]
  exact ⟨by omega, by omega⟩

theorem out_decideSigC (y : Word) {C D : Circuit} {w : ℕ} (hC : wf C)
    (hin : inpsLt D.length C) (hwC : w ≤ C.length) :
    out y (decideSigC C D w) = (topVals w (vals (vals y D) C)).getD 0 false := by
  rw [decideSigC, out,
    vals_reroute_append y D 0 (Nat.zero_le _) C hC (by simpa using hin)]
  simp only [List.drop_zero, gateVal, Bool.and_self]
  have hlenD : (vals y D).length = D.length := by simp
  have hlenC : (vals (vals y D) C).length = C.length := by simp
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), topVals,
    List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2
  omega

end Tseitin

open Complexity.Tseitin

/-! ### Uniformity of the decoder -/

/-- **A layer of constant gates is a P-uniform family** as soon as its size is written in unary by
a Cobham term. -/
theorem codeUniform_cstLayerU {c : ℕ → ℕ} {cntT : Cob} (b : Bool)
    (hc : ∀ x : Word, cntT.eval [x] = List.replicate (c x.length) true) :
    CodeUniform (fun n => Tseitin.cstLayer b (c n)) := by
  refine codeUniform_layerP (K := 11) (cnt := cntT)
    (padT := Cob.catL [.comp .smash [Cob.proj 0, Cob.constT [true]], Cob.constT [false], cntT])
    (pw := fun n => dmW n (c n))
    (blkT := CircCode.tokTerm (CircCode.tag (Tseitin.Gate.cst b)) .empty .empty)
    (tmpl := fun _ _ => Tseitin.Gate.cst b) hc ?_ ?_ ?_
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_constT, Cob.eval_comp, Cob.eval_smash, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, hc x]
    simp [dmW]
  · intro n y i
    exact CircCode.eval_tokTerm (g := Tseitin.Gate.cst b) (by simp [CircCode.fld1])
      (by simp [CircCode.fld2])
  · intro n i l _
    rw [CircCode.length_encGate]
    simp only [CircCode.fld1, CircCode.fld2, length_dmW]
    cases b <;> simp [CircCode.tag] <;> omega

/-- **The layer reading the odd positions of a pinned input is a P-uniform family.** -/
theorem codeUniform_oddInpLayer :
    CodeUniform (fun n => Tseitin.inpLayer (fun j => 2 * min j n + 1) n) := by
  set nT : Cob := .comp Cob.leadOnes [.proj 2] with hnT
  set A : Cob := .comp Cob.dropU [nT, .proj 1] with hA
  set B : Cob := .comp Cob.dropU [A, .proj 1] with hB
  refine codeUniform_inpLayer (idx := fun n c => 2 * min c n + 1) (S := fun n => 2 * n + 1)
    (fun n c => by have h := Nat.min_le_right c n; omega)
    (mT := Cob.unary (.proj 0)) (sT := Cob.catL [Cob.unary (.proj 0), Cob.unary (.proj 0),
      Cob.constT [true]])
    (idxT := Cob.catL [B, B, Cob.constT [true]]) (fun x => by simp) ?_ ?_
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_constT, Cob.eval_unary, Cob.eval_proj, List.getD_cons_zero]
    rw [show ([true] : Word) = List.replicate 1 true from rfl, ← List.replicate_add,
      ← List.replicate_add]
    congr 1
    omega
  · intro n c y
    have hn : nT.eval [y, List.replicate c true, dmW n (2 * n + 1)] = List.replicate n true := by
      simp only [hnT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes,
        Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero]
      rw [lead1_dmW]
    have hAv : A.eval [y, List.replicate c true, dmW n (2 * n + 1)]
        = List.replicate (c - n) true := by
      simp only [hA, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, hn,
        Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, List.length_replicate,
        List.drop_replicate]
    have hBv : B.eval [y, List.replicate c true, dmW n (2 * n + 1)]
        = List.replicate (min c n) true := by
      simp only [hB, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, hAv,
        Cob.eval_proj, List.getD_cons_succ, List.getD_cons_zero, List.length_replicate,
        List.drop_replicate]
      congr 1
      omega
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_constT, hBv]
    rw [show ([true] : Word) = List.replicate 1 true from rfl, ← List.replicate_add,
      ← List.replicate_add]
    congr 1
    omega

/-- **The decoder is a P-uniform family.** -/
theorem codeUniform_sigInC {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    CodeUniform (fun n => Tseitin.sigInC n (m n)) := by
  have hsub : ∀ x : Word, (Cob.comp Cob.dropU [Cob.unary (.proj 0), mT]).eval [x]
      = List.replicate (m x.length - x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, Cob.eval_unary,
      Cob.eval_proj, List.getD_cons_zero, hm x, List.length_replicate, List.drop_replicate]
  have hid : ∀ x : Word, (Cob.unary (Cob.proj 0)).eval [x] = List.replicate x.length true := by
    intro x; simp
  exact codeUniform_append (codeUniform_cstLayerU false hsub)
    (codeUniform_append codeUniform_oddInpLayer
      (codeUniform_append (codeUniform_cstLayerU false hsub) (codeUniform_cstLayerU true hid)))

/-! ### The bridge -/

/-- **A language whose acceptance is the nonemptiness of a realized word function is decided by a
P-uniform family.** -/
theorem pUniformDecidable_of_sigUniformB {m k : ℕ → ℕ} {F : List Word → Word} {L : Language}
    (h : SigUniformB 1 m k F) (hnm : ∀ n, n ≤ m n) (hnk : ∀ n, n ≤ k n) (hm0 : ∀ n, 0 < m n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hacc : ∀ x : Word, L x ↔ F [x] ≠ []) :
    PUniformDecidable L := by
  obtain ⟨cf, hcf⟩ := h
  have hDlen : ∀ n, (Tseitin.sigInC n (m n)).length = 2 * m n :=
    fun n => Tseitin.length_sigInC n (m n) (hnm n)
  have hinp : ∀ n, Tseitin.inpsLt (Tseitin.sigInC n (m n)).length (cf n) := by
    intro n
    have := hcf.inpC n
    rw [hDlen n]
    simpa using this
  have hwidth : ∀ n, 2 * m n ≤ (cf n).length := hcf.widthC
  refine ⟨fun n => Tseitin.decideSigC (cf n) (Tseitin.sigInC n (m n)) (2 * m n),
    fun n => by simp [Tseitin.decideSigC], fun n => ?_, fun n y hy => ?_, ?_⟩
  · exact Tseitin.wf_decideSigC (hcf.wfC n) (Tseitin.wf_sigInC n (m n)) (hinp n)
      (by have := hm0 n; omega) (hwidth n)
  · -- correctness
    have hu : (Tseitin.inWord n y).length = n := by
      rw [Tseitin.inWord_of_pinned n y hy]; simp
    have hvals : Tseitin.vals y (Tseitin.sigInC n (m n))
        = Tseitin.encArgs (m n) [Tseitin.inWord n y] := by
      rw [Tseitin.vals_sigInC y (hnm n) hy]
      simp [Tseitin.encArgs]
    have hout := hcf.outC n [Tseitin.inWord n y] (by simp) (by
      intro u hu'
      rcases List.mem_singleton.1 hu' with rfl
      rw [hu]
      exact hnk n)
    rw [Tseitin.out_decideSigC y (hcf.wfC n) (hinp n) (hwidth n), hvals, hout]
    have hget : (Tseitin.encSig (m n) (F [Tseitin.inWord n y])).getD 0 false
        = decide (F [Tseitin.inWord n y] ≠ []) := by
      rw [Tseitin.encSig, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by
          simp only [List.length_map, List.length_range]; exact hm0 n), List.getElem?_map,
        List.getElem?_range (hm0 n)]
      cases hF : F [Tseitin.inWord n y] with
      | nil => simp
      | cons b w => simp
    rw [hget]
    simp only [decide_eq_true_eq]
    exact (hacc (Tseitin.inWord n y)).symm
  · -- uniformity
    obtain ⟨lenT, hlenT⟩ := exists_lenTerm hcf.codeC
    have hr : ∀ n, (cf n).length + (Tseitin.sigInC n (m n)).length - 2 * m n = (cf n).length := by
      intro n
      rw [hDlen n]
      omega
    have hgate : CodeUniform (fun n =>
        [Tseitin.Gate.conj ((cf n).length + (Tseitin.sigInC n (m n)).length - 2 * m n)
          ((cf n).length + (Tseitin.sigInC n (m n)).length - 2 * m n)]) := by
      refine codeUniform_gate (t := 5) (aT := lenT) (bT := lenT) (fun _ => rfl) ?_ ?_ <;>
        · intro x
          simp only [CircCode.fld1, CircCode.fld2, hr x.length]
          exact hlenT x
    have hcomp : CodeUniform (fun n =>
        Tseitin.reroute (Tseitin.sigInC n (m n)).length 0 (cf n) ++ Tseitin.sigInC n (m n)) :=
      codeUniform_compose hcf.codeC (codeUniform_sigInC hm) (eT := .empty) (fun x => by simp)
    exact codeUniform_append hgate hcomp

/-! ### The language of a Cobham term -/

/-- **The language of a well-formed Cobham term of one argument is decided by a P-uniform
family.** -/
theorem pUniformDecidable_of_cobShape {v : Cob} {L : Language} (h : CobShape 1 v)
    (hacc : ∀ x : Word, L x ↔ v.eval [x] ≠ []) : PUniformDecidable L := by
  obtain ⟨T, hT⟩ := exists_cobLenT v
  set m : ℕ → ℕ := fun n => cobLen v n + 1 with hmdef
  have hm : ∀ x : Word, (Cob.catL [T, Cob.constT [true]]).eval [x]
      = List.replicate (m x.length) true := by
    intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, hT x, Cob.eval_constT,
      List.flatten_cons, List.flatten_nil, List.append_nil, hmdef]
    rw [show ([true] : Word) = List.replicate 1 true from rfl, ← List.replicate_add]
  have hsig : SigUniformB 1 m (fun n => n) v.eval :=
    sigUniformB_of_cobShape hm h _ unaryLen_id (fun n => by simp only [hmdef]; omega)
  refine pUniformDecidable_of_sigUniformB hsig (fun n => ?_) (fun n => le_rfl)
    (fun n => by simp only [hmdef]; omega) hm hacc
  have := le_cobLen v n
  simp only [hmdef]
  omega

/-- **The language of a well-formed Cobham term reduces to SAT in polynomial time**, with no
hypothesis left over. -/
theorem polyManyOne_SAT_of_cobShape {v : Cob} {L : Language} (h : CobShape 1 v)
    (hacc : ∀ x : Word, L x ↔ v.eval [x] ≠ []) : L ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable (pUniformDecidable_of_cobShape h hacc)

end Complexity
