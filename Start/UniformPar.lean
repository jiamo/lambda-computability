/-
# Routing: copying wires, and the parallel product of two P-uniform families

`Start/UniformIterate.lean` stacks copies of one circuit on top of another and rewires the copies
to one another, which is the shape the *unrolling of a loop* has.  A compiler that walks a term
needs one more shape: the **parallel product**, in which two circuits are run on the same circuit
input and their output vectors are laid side by side, so that a later stage may read both at once.
That is what a composition `f(g₁(x), …, g_r(x))` of a term-rewriting compiler asks for, and the
gates of the two factors do not sit next to one another in the stack, so the two vectors must be
*copied* to the top.

This module supplies the copying.

* `Complexity.Tseitin.wireLayer idx m` is a layer of `m` copy gates, the gate `c` of the layer
  copying the value of the gate `idx c` of the circuit underneath;
* `Complexity.Tseitin.selLayer base m` copies the block of `m` consecutive gates starting at
  `base`;
* `Complexity.Tseitin.parC B₁ B₂ w₁ w₂` runs `B₁` and `B₂` on the same circuit input and copies the
  topmost `w₁` gates of `B₁` and the topmost `w₂` gates of `B₂` to the top of the result.

Main results:

* `Complexity.Tseitin.vals_wireLayer_append` — the layer carries the values it selects;
* `Complexity.Tseitin.wf_wireLayer_append`, `Complexity.Tseitin.inpsLt_wireLayer_append` — it is
  well formed and adds no circuit input;
* `Complexity.Tseitin.topVals_parC` — **the topmost `w₁ + w₂` gates of the product carry the
  topmost `w₁` gates of `B₁` followed by the topmost `w₂` gates of `B₂`**;
* `Complexity.Tseitin.stepC_parC` — hence the product of two stages is a stage computing both;
* `Complexity.codeUniform_wireLayer`, `Complexity.codeUniform_selLayer` — **a layer of copy gates
  whose sources are Cobham-computable in unary is a P-uniform family**;
* `Complexity.codeUniform_parC` — **the parallel product of two P-uniform families is
  P-uniform.**

The sources of a copy gate are gates of the circuit underneath, so its token is *long*: this is
again a case for the padded layer rule `Complexity.codeUniform_layerP`, with the parameter word
`1^n 0 1^{S n}`, `S n` bounding the identifiers that may be copied.
-/

import Start.UniformIterate

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### A layer of copy gates -/

/-- A layer of `m` copy gates: the gate with identifier `c` of the layer copies the value of the
gate `idx c` of the circuit underneath.  A copy is a disjunction of a gate with itself. -/
def wireLayer (idx : ℕ → ℕ) (m : ℕ) : Circuit :=
  CircCode.layer (fun c => Gate.disj (idx c) (idx c)) m

@[simp] theorem length_wireLayer (idx : ℕ → ℕ) (m : ℕ) : (wireLayer idx m).length = m := by
  simp [wireLayer]

theorem wireLayer_succ (idx : ℕ → ℕ) (m : ℕ) :
    wireLayer idx (m + 1) = Gate.disj (idx m) (idx m) :: wireLayer idx m := rfl

/-- The layer is well formed on top of a well-formed circuit as soon as it copies gates of that
circuit. -/
theorem wf_wireLayer_append {idx : ℕ → ℕ} {C : Circuit} (hC : wf C) (m : ℕ)
    (h : ∀ c, c < m → idx c < C.length) : wf (wireLayer idx m ++ C) := by
  induction m with
  | zero => simpa [wireLayer, CircCode.layer] using hC
  | succ m ih =>
      have hm : idx m < C.length := h m (Nat.lt_succ_self m)
      have hlen : (wireLayer idx m ++ C).length = m + C.length := by simp
      rw [wireLayer_succ, List.cons_append]
      refine ⟨?_, ih (fun c hc => h c (Nat.lt_succ_of_lt hc))⟩
      simp only [gateWf, hlen]
      exact ⟨by omega, by omega⟩

/-- A copy gate is not a circuit input, so the layer adds none. -/
theorem inpsLt_wireLayer_append {idx : ℕ → ℕ} {C : Circuit} {w : ℕ} (hC : inpsLt w C) (m : ℕ) :
    inpsLt w (wireLayer idx m ++ C) := by
  induction m with
  | zero => simpa [wireLayer, CircCode.layer] using hC
  | succ m ih =>
      rw [wireLayer_succ, List.cons_append]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact trivial
      · exact ih g hg'

/-- **The layer carries the values it selects.** -/
theorem vals_wireLayer_append (x : Word) {idx : ℕ → ℕ} {C : Circuit} (m : ℕ)
    (h : ∀ c, c < m → idx c < C.length) :
    vals x (wireLayer idx m ++ C)
      = vals x C ++ (List.range m).map (fun c => (vals x C).getD (idx c) false) := by
  induction m with
  | zero =>
      have hnil : wireLayer idx 0 = [] := rfl
      rw [hnil]
      simp
  | succ m ih =>
      have hm : idx m < C.length := h m (Nat.lt_succ_self m)
      have hlenC : (vals x C).length = C.length := by simp
      have hprev := ih (fun c hc => h c (Nat.lt_succ_of_lt hc))
      have hget : (vals x C ++ (List.range m).map
          (fun c => (vals x C).getD (idx c) false)).getD (idx m) false
          = (vals x C).getD (idx m) false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
      rw [wireLayer_succ, List.cons_append, vals, hprev, List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil, List.append_assoc, gateVal, hget, Bool.or_self]

/-! ### Selecting a block of consecutive gates -/

/-- The layer copying the block of `m` consecutive gates starting at `base`. -/
def selLayer (base m : ℕ) : Circuit := wireLayer (fun c => base + c) m

@[simp] theorem length_selLayer (base m : ℕ) : (selLayer base m).length = m := by
  simp [selLayer]

/-- The values carried by the topmost `w` gates of a circuit are the values of the block of `w`
gates ending at its top. -/
theorem topVals_append_right (u v : List Bool) : topVals v.length (u ++ v) = v := by
  simp [topVals]

/-! ### The parallel product -/

/-- **The parallel product**: `B₁` and `B₂` run on the same circuit input, with the topmost `w₁`
gates of `B₁` and then the topmost `w₂` gates of `B₂` copied to the top. -/
def parC (B1 B2 : Circuit) (w1 w2 : ℕ) : Circuit :=
  selLayer (B2.length - w2) w2 ++
    (selLayer (B2.length + B1.length - w1) w1 ++ stackC B1 B2)

@[simp] theorem length_parC (B1 B2 : Circuit) (w1 w2 : ℕ) :
    (parC B1 B2 w1 w2).length = w1 + w2 + (B1.length + B2.length) := by
  simp only [parC, List.length_append, length_selLayer, length_stackC]
  omega

/-- The values of the product, before the copies: the values of `B₂` and then those of `B₁`. -/
theorem vals_stack_parC (x : Word) {B1 B2 : Circuit} (hB1 : wf B1) :
    vals x (stackC B1 B2) = vals x B2 ++ vals x B1 :=
  vals_stackC x B2 hB1

/-- **The topmost `w₁ + w₂` gates of the product** carry the topmost `w₁` gates of `B₁` followed
by the topmost `w₂` gates of `B₂`. -/
theorem topVals_parC (x : Word) {B1 B2 : Circuit} {w1 w2 : ℕ} (hB1 : wf B1)
    (hw1 : w1 ≤ B1.length) (hw2 : w2 ≤ B2.length) :
    topVals (w1 + w2) (vals x (parC B1 B2 w1 w2))
      = topVals w1 (vals x B1) ++ topVals w2 (vals x B2) := by
  have hlen1 : (vals x B1).length = B1.length := by simp
  have hlen2 : (vals x B2).length = B2.length := by simp
  have hS : vals x (stackC B1 B2) = vals x B2 ++ vals x B1 := vals_stack_parC x hB1
  have hSlen : (vals x (stackC B1 B2)).length = B2.length + B1.length := by
    rw [hS]; simp
  -- the upper layer copies the topmost `w₁` gates of `B₁`
  have hup : ∀ c, c < w1 → B2.length + B1.length - w1 + c < (stackC B1 B2).length := by
    intro c hc
    simp only [length_stackC]
    omega
  have hA : vals x (selLayer (B2.length + B1.length - w1) w1 ++ stackC B1 B2)
      = vals x (stackC B1 B2) ++ topVals w1 (vals x B1) := by
    rw [selLayer, vals_wireLayer_append x w1 hup]
    congr 1
    have hone : ∀ c, c < w1 → (vals x (stackC B1 B2)).getD (B2.length + B1.length - w1 + c) false
        = (topVals w1 (vals x B1)).getD c false := by
      intro c hc
      rw [hS, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
        ← List.getD_eq_getElem?_getD, hlen2, topVals, hlen1, getD_drop]
      congr 1
      omega
    refine List.ext_getElem (by simp [topVals, hlen1]; omega) ?_
    intro i h1 h2
    have hi : i < w1 := by simpa using h1
    have := hone i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    simpa [List.getElem?_eq_getElem, h1, h2] using this
  -- the lower layer copies the topmost `w₂` gates of `B₂`
  have hlow : ∀ c, c < w2 → B2.length - w2 + c
      < (selLayer (B2.length + B1.length - w1) w1 ++ stackC B1 B2).length := by
    intro c hc
    simp only [List.length_append, length_selLayer, length_stackC]
    omega
  have hB : vals x (parC B1 B2 w1 w2)
      = (vals x (stackC B1 B2) ++ topVals w1 (vals x B1)) ++ topVals w2 (vals x B2) := by
    rw [parC, selLayer, vals_wireLayer_append x w2 hlow, hA]
    congr 1
    have hone : ∀ c, c < w2 →
        ((vals x (stackC B1 B2)) ++ topVals w1 (vals x B1)).getD (B2.length - w2 + c) false
          = (topVals w2 (vals x B2)).getD c false := by
      intro c hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hSlen]; omega),
        ← List.getD_eq_getElem?_getD, hS, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hlen2]; omega), ← List.getD_eq_getElem?_getD,
        topVals, hlen2, getD_drop]
    refine List.ext_getElem (by simp [topVals, hlen2]; omega) ?_
    intro i h1 h2
    have hi : i < w2 := by simpa using h1
    have := hone i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at this
    simpa [List.getElem?_eq_getElem, h1, h2] using this
  rw [hB]
  have hl1 : (topVals w1 (vals x B1)).length = w1 := by
    simp only [topVals, List.length_drop, hlen1]; omega
  have hl2 : (topVals w2 (vals x B2)).length = w2 := by
    simp only [topVals, List.length_drop, hlen2]; omega
  have := topVals_append_right (vals x (stackC B1 B2))
    (topVals w1 (vals x B1) ++ topVals w2 (vals x B2))
  rw [List.length_append, hl1, hl2] at this
  rw [← List.append_assoc] at this
  rw [← this]

/-- **The product of two stages is a stage computing both.** -/
theorem stepC_parC {B1 B2 : Circuit} {w1 w2 : ℕ} (hB1 : wf B1) (hw1 : w1 ≤ B1.length)
    (hw2 : w2 ≤ B2.length) (s : List Bool) :
    stepC (parC B1 B2 w1 w2) (w1 + w2) s = stepC B1 w1 s ++ stepC B2 w2 s :=
  topVals_parC s hB1 hw1 hw2

/-- The product is well formed. -/
theorem wf_parC {B1 B2 : Circuit} {w1 w2 : ℕ} (hB1 : wf B1) (hB2 : wf B2)
    (hw1 : w1 ≤ B1.length) (hw2 : w2 ≤ B2.length) : wf (parC B1 B2 w1 w2) := by
  have hS : wf (stackC B1 B2) := wf_stackC hB1 hB2
  have hup : wf (selLayer (B2.length + B1.length - w1) w1 ++ stackC B1 B2) := by
    refine wf_wireLayer_append hS w1 (fun c hc => ?_)
    simp only [length_stackC]
    omega
  refine wf_wireLayer_append hup w2 (fun c hc => ?_)
  simp only [List.length_append, length_selLayer, length_stackC]
  omega

/-- The product reads no circuit input that its factors do not read. -/
theorem inpsLt_parC {B1 B2 : Circuit} {w1 w2 : ℕ} {w : ℕ} (h1 : inpsLt w B1) (h2 : inpsLt w B2) :
    inpsLt w (parC B1 B2 w1 w2) := by
  have hS : inpsLt w (stackC B1 B2) := by
    intro g hg
    rcases List.mem_append.1 hg with hg' | hg'
    · obtain ⟨g', hg'mem, rfl⟩ := List.mem_map.1 hg'
      have := h1 g' hg'mem
      cases g' <;> simp_all [Gate.shiftBy, inpLt]
    · exact h2 g hg'
  exact inpsLt_wireLayer_append (inpsLt_wireLayer_append hS w1) w2


/-! ### A layer reading the circuit input -/

/-- A layer of `m` input gates: the gate with identifier `c` of the layer reads the circuit input
`idx c`.  This is the base of a transducer: it presents a block of the input as a vector of
wires. -/
def inpLayer (idx : ℕ → ℕ) (m : ℕ) : Circuit :=
  CircCode.layer (fun c => Gate.inp (idx c)) m

@[simp] theorem length_inpLayer (idx : ℕ → ℕ) (m : ℕ) : (inpLayer idx m).length = m := by
  simp [inpLayer]

theorem inpLayer_succ (idx : ℕ → ℕ) (m : ℕ) :
    inpLayer idx (m + 1) = Gate.inp (idx m) :: inpLayer idx m := rfl

/-- A layer of input gates is well formed. -/
theorem wf_inpLayer_append {idx : ℕ → ℕ} {C : Circuit} (hC : wf C) (m : ℕ) :
    wf (inpLayer idx m ++ C) := by
  induction m with
  | zero => simpa [inpLayer, CircCode.layer] using hC
  | succ m ih =>
      rw [inpLayer_succ, List.cons_append]
      exact ⟨trivial, ih⟩

/-- The inputs it reads are the ones it is given. -/
theorem inpsLt_inpLayer_append {idx : ℕ → ℕ} {C : Circuit} {w : ℕ} (hC : inpsLt w C) (m : ℕ)
    (h : ∀ c, c < m → idx c < w) : inpsLt w (inpLayer idx m ++ C) := by
  induction m with
  | zero => simpa [inpLayer, CircCode.layer] using hC
  | succ m ih =>
      rw [inpLayer_succ, List.cons_append]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact h m (Nat.lt_succ_self m)
      · exact ih (fun c hc => h c (Nat.lt_succ_of_lt hc)) g hg'

/-- **The layer carries the bits of the circuit input that it reads.** -/
theorem vals_inpLayer_append (x : Word) {idx : ℕ → ℕ} {C : Circuit} (m : ℕ) :
    vals x (inpLayer idx m ++ C)
      = vals x C ++ (List.range m).map (fun c => x.getD (idx c) false) := by
  induction m with
  | zero =>
      have hnil : inpLayer idx 0 = [] := rfl
      rw [hnil]
      simp
  | succ m ih =>
      rw [inpLayer_succ, List.cons_append, vals, ih, List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil, List.append_assoc, gateVal]

end Tseitin

/-! ### Uniformity -/

open Complexity.Tseitin

/-- **A layer of copy gates is a P-uniform family** as soon as the source of the gate `c` is
computed in unary by a Cobham term, from `1^c` and from the parameter word `1^n 0 1^{S n}`, and is
bounded by `S n + c`. -/
theorem codeUniform_wireLayer {idx : ℕ → ℕ → ℕ} {m S : ℕ → ℕ}
    (hidx : ∀ n c, idx n c ≤ S n + c)
    {mT sT idxT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hs : ∀ x : Word, sT.eval [x] = List.replicate (S x.length) true)
    (hidxT : ∀ (n c : ℕ) (y : Word),
      idxT.eval [y, List.replicate c true, dmW n (S n)] = List.replicate (idx n c) true) :
    CodeUniform (fun n => Tseitin.wireLayer (idx n) (m n)) := by
  set lenT : Cob := .comp .smash [Cob.proj 0, Cob.constT [true]] with hlenT
  have hlenTn : ∀ x : Word, lenT.eval [x] = List.replicate x.length true := by
    intro x; simp [hlenT]
  set padT : Cob := Cob.catL [lenT, Cob.constT [false], sT] with hpadT
  have hpadTn : ∀ x : Word, padT.eval [x] = dmW x.length (S x.length) := by
    intro x
    simp only [hpadT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_constT, hlenTn x, hs x]
    simp [dmW]
  refine codeUniform_layerP (K := 11) (cnt := mT) (padT := padT) (pw := fun n => dmW n (S n))
    (blkT := CircCode.tokTerm 6 idxT idxT)
    (tmpl := fun n c => Tseitin.Gate.disj (idx n c) (idx n c)) hm hpadTn ?_ ?_
  · intro n y c
    exact CircCode.eval_tokTerm (g := Tseitin.Gate.disj (idx n c) (idx n c))
      (hidxT n c y) (hidxT n c y)
  · intro n c l hc
    have hb := hidx n c
    rw [CircCode.length_encGate]
    simp only [CircCode.tag, CircCode.fld1, CircCode.fld2, length_dmW]
    omega

/-- **A layer copying a block of consecutive gates is a P-uniform family**, the start of the block
being computed in unary from `1^n`. -/
theorem codeUniform_selLayer {base m S : ℕ → ℕ} (hb : ∀ n, base n ≤ S n)
    {baseT mT sT : Cob}
    (hbT : ∀ x : Word, baseT.eval [x] = List.replicate (base x.length) true)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hs : ∀ x : Word, sT.eval [x] = List.replicate (S x.length) true) :
    CodeUniform (fun n => Tseitin.selLayer (base n) (m n)) := by
  refine codeUniform_wireLayer (idx := fun n c => base n + c) (S := S)
    (fun n c => Nat.add_le_add_right (hb n) c) hm hs
    (idxT := .comp Cob.concat [.comp baseT [.comp Cob.leadOnes [.proj 2]], Cob.proj 1]) ?_
  intro n c y
  have hlead : (Cob.comp Cob.leadOnes [Cob.proj 2]).eval
      [y, List.replicate c true, dmW n (S n)] = List.replicate n true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [lead1_dmW]
  have hbase : (Cob.comp baseT [.comp Cob.leadOnes [Cob.proj 2]]).eval
      [y, List.replicate c true, dmW n (S n)] = List.replicate (base n) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hlead]
    rw [hbT (List.replicate n true), List.length_replicate]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hbase, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero, ← List.replicate_add]

/-- **The parallel product of two P-uniform families is P-uniform**: the two factors are stacked,
and the two blocks of wires to be copied are found by arithmetic on the sizes of the factors,
which are themselves Cobham-computable in unary. -/
theorem codeUniform_parC {cb1 cb2 : ℕ → Tseitin.Circuit} {w1 w2 : ℕ → ℕ}
    (h1 : CodeUniform cb1) (h2 : CodeUniform cb2)
    {w1T w2T : Cob}
    (hw1 : ∀ x : Word, w1T.eval [x] = List.replicate (w1 x.length) true)
    (hw2 : ∀ x : Word, w2T.eval [x] = List.replicate (w2 x.length) true) :
    CodeUniform (fun n => Tseitin.parC (cb1 n) (cb2 n) (w1 n) (w2 n)) := by
  obtain ⟨l1, hl1⟩ := exists_lenTerm h1
  obtain ⟨l2, hl2⟩ := exists_lenTerm h2
  set L1 : ℕ → ℕ := fun n => (cb1 n).length with hL1
  set L2 : ℕ → ℕ := fun n => (cb2 n).length with hL2
  set S : ℕ → ℕ := fun n => L2 n + L1 n with hSdef
  have hsT : ∀ x : Word, (Cob.comp Cob.concat [l2, l1]).eval [x]
      = List.replicate (S x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hl1 x, hl2 x,
      ← List.replicate_add]
    rfl
  -- the two blocks
  have hlowT : ∀ x : Word, (Cob.comp Cob.dropU [w2T, l2]).eval [x]
      = List.replicate (L2 x.length - w2 x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, hw2 x, hl2 x,
      List.length_replicate, List.drop_replicate]
    rfl
  have hupT : ∀ x : Word, (Cob.comp Cob.dropU [w1T, .comp Cob.concat [l2, l1]]).eval [x]
      = List.replicate (L2 x.length + L1 x.length - w1 x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, hw1 x, hsT x,
      List.length_replicate, List.drop_replicate, hSdef]
  have hlow : CodeUniform (fun n => Tseitin.selLayer (L2 n - w2 n) (w2 n)) :=
    codeUniform_selLayer (S := S) (fun n => by simp only [hSdef]; omega) hlowT hw2 hsT
  have hup : CodeUniform (fun n => Tseitin.selLayer (L2 n + L1 n - w1 n) (w1 n)) :=
    codeUniform_selLayer (S := S) (fun n => by simp only [hSdef]; omega) hupT hw1 hsT
  have hstack : CodeUniform (fun n => Tseitin.stackC (cb1 n) (cb2 n)) := codeUniform_stack h1 h2
  exact codeUniform_append hlow (codeUniform_append hup hstack)

/-- **A layer of input gates is a P-uniform family** as soon as the input read by the gate `c` is
computed in unary by a Cobham term, from `1^c` and from the parameter word `1^n 0 1^{S n}`, and is
bounded by `S n + c`. -/
theorem codeUniform_inpLayer {idx : ℕ → ℕ → ℕ} {m S : ℕ → ℕ}
    (hidx : ∀ n c, idx n c ≤ S n + c)
    {mT sT idxT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hs : ∀ x : Word, sT.eval [x] = List.replicate (S x.length) true)
    (hidxT : ∀ (n c : ℕ) (y : Word),
      idxT.eval [y, List.replicate c true, dmW n (S n)] = List.replicate (idx n c) true) :
    CodeUniform (fun n => Tseitin.inpLayer (idx n) (m n)) := by
  set lenT : Cob := .comp .smash [Cob.proj 0, Cob.constT [true]] with hlenT
  have hlenTn : ∀ x : Word, lenT.eval [x] = List.replicate x.length true := by
    intro x; simp [hlenT]
  set padT : Cob := Cob.catL [lenT, Cob.constT [false], sT] with hpadT
  have hpadTn : ∀ x : Word, padT.eval [x] = dmW x.length (S x.length) := by
    intro x
    simp only [hpadT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, Cob.eval_constT, hlenTn x, hs x]
    simp [dmW]
  refine codeUniform_layerP (K := 11) (cnt := mT) (padT := padT) (pw := fun n => dmW n (S n))
    (blkT := CircCode.tokTerm 1 idxT .empty)
    (tmpl := fun n c => Tseitin.Gate.inp (idx n c)) hm hpadTn ?_ ?_
  · intro n y c
    exact CircCode.eval_tokTerm (g := Tseitin.Gate.inp (idx n c)) (hidxT n c y)
      (by simp [CircCode.fld2])
  · intro n c l hc
    have hb := hidx n c
    rw [CircCode.length_encGate]
    simp only [CircCode.tag, CircCode.fld1, CircCode.fld2, length_dmW]
    omega

/-- **A layer reading a block of consecutive circuit inputs is a P-uniform family.** -/
theorem codeUniform_selInpLayer {base m S : ℕ → ℕ} (hb : ∀ n, base n ≤ S n)
    {baseT mT sT : Cob}
    (hbT : ∀ x : Word, baseT.eval [x] = List.replicate (base x.length) true)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true)
    (hs : ∀ x : Word, sT.eval [x] = List.replicate (S x.length) true) :
    CodeUniform (fun n => Tseitin.inpLayer (fun c => base n + c) (m n)) := by
  refine codeUniform_inpLayer (idx := fun n c => base n + c) (S := S)
    (fun n c => Nat.add_le_add_right (hb n) c) hm hs
    (idxT := .comp Cob.concat [.comp baseT [.comp Cob.leadOnes [.proj 2]], Cob.proj 1]) ?_
  intro n c y
  have hlead : (Cob.comp Cob.leadOnes [Cob.proj 2]).eval
      [y, List.replicate c true, dmW n (S n)] = List.replicate n true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_leadOnes, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero]
    rw [lead1_dmW]
  have hbase : (Cob.comp baseT [.comp Cob.leadOnes [Cob.proj 2]]).eval
      [y, List.replicate c true, dmW n (S n)] = List.replicate (base n) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, hlead]
    rw [hbT (List.replicate n true), List.length_replicate]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hbase, Cob.eval_proj,
    List.getD_cons_succ, List.getD_cons_zero, ← List.replicate_add]

end Complexity
