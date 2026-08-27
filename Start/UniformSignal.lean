/-
# Word signals, and the compiler for a Cobham term as a P-uniform family

The rules collected so far build P-uniform families of circuits *by hand*: a grid here, a stack of
copies there.  What the Cook–Levin argument still misses is a **compiler**: a function which, from
a Cobham term, produces a P-uniform family of circuits computing it.  This module sets up the
interface such a compiler works against, and discharges its first cases.

A word of length at most `m` is presented on `2 * m` wires: `m` *presence* bits, saying which
positions are occupied, followed by `m` *value* bits (`Complexity.Tseitin.encSig`).  A term of
arity `r` is compiled into a family of circuits whose circuit inputs are the `r` argument signals,
laid side by side (`Complexity.Tseitin.encArgs`), and whose topmost `2 * m` gates carry the signal
of the value.  `Complexity.Tseitin.SigFam` packages that, together with well-formedness and
P-uniformity of the family; `Complexity.SigUniform` is its existential form.

Main definitions:

* `Complexity.Tseitin.encSig`, `Complexity.Tseitin.encArgs` — the presentation of words and of
  argument lists on wires;
* `Complexity.Tseitin.SigFam`, `Complexity.SigUniform` — a P-uniform family realizing a word
  function;
* `Complexity.Tseitin.cstLayer` — a layer of constant gates.

Main results:

* `Complexity.sigUniform_empty` — the constant empty word is realized;
* `Complexity.sigUniform_proj` — every projection is realized;
* `Complexity.sigUniform_of_eval_eq` — a function realized at a given width is realized by any
  function with the same values on the arguments that the width admits.

The width `m` is a parameter: it must be computed in unary from `1^n` by a Cobham term, and it must
be large enough for the values of the term.  Widths of that shape exist for every Cobham term,
since `Complexity.Cob.polyLen` bounds the length of its values by a polynomial.
-/

import Start.UniformPar

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Words on wires -/

/-- The presentation of a word `u` of length at most `m` on `2 * m` wires: the `m` presence bits,
saying which positions are occupied, followed by the `m` value bits. -/
def encSig (m : ℕ) (u : Word) : List Bool :=
  (List.range m).map (fun j => decide (j < u.length)) ++
    (List.range m).map (fun j => u.getD j false)

@[simp] theorem length_encSig (m : ℕ) (u : Word) : (encSig m u).length = 2 * m := by
  simp only [encSig, List.length_append, List.length_map, List.length_range]
  omega

theorem encSig_nil (m : ℕ) : encSig m [] = List.replicate (2 * m) false := by
  have h : ∀ f : ℕ → Bool, (∀ j, j < m → f j = false) →
      (List.range m).map f = List.replicate m false := by
    intro f hf
    refine List.ext_getElem (by simp) ?_
    intro i h1 h2
    have hi : i < m := by simpa using h1
    simp [hf i hi]
  rw [encSig, h _ (fun j _ => by simp), h _ (fun j _ => by simp),
    ← List.replicate_add]
  congr 1
  omega

/-- The circuit input presenting a list of arguments: their signals, laid side by side. -/
def encArgs (m : ℕ) (args : List Word) : Word := (args.map (encSig m)).flatten

@[simp] theorem length_encArgs (m : ℕ) (args : List Word) :
    (encArgs m args).length = args.length * (2 * m) := by
  induction args with
  | nil => simp [encArgs]
  | cons u us ih =>
      simp only [encArgs, List.map_cons, List.flatten_cons, List.length_append,
        length_encSig] at *
      simp [ih]
      ring

/-- **Reading a bit of an argument off the input word.** -/
theorem getD_encArgs (m : ℕ) (args : List Word) {i j : ℕ} (hi : i < args.length)
    (hj : j < 2 * m) :
    (encArgs m args).getD (i * (2 * m) + j) false
      = (encSig m (args.getD i [])).getD j false := by
  induction args generalizing i with
  | nil => simp at hi
  | cons u us ih =>
      cases i with
      | zero =>
          simp only [encArgs, List.map_cons, List.flatten_cons, Nat.zero_mul, Nat.zero_add,
            List.getD_cons_zero]
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_append_left (by rw [length_encSig]; omega),
            ← List.getD_eq_getElem?_getD]
      | succ i =>
          have hi' : i < us.length := by simpa using hi
          simp only [encArgs, List.map_cons, List.flatten_cons, List.getD_cons_succ]
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_append_right (by rw [length_encSig]; nlinarith),
            ← List.getD_eq_getElem?_getD, length_encSig]
          have harith : (i + 1) * (2 * m) + j - 2 * m = i * (2 * m) + j := by ring_nf; omega
          rw [harith]
          exact ih hi'

/-! ### A layer of constant gates -/

/-- A layer of `m` constant gates. -/
def cstLayer (b : Bool) (m : ℕ) : Circuit := CircCode.layer (fun _ => Gate.cst b) m

@[simp] theorem length_cstLayer (b : Bool) (m : ℕ) : (cstLayer b m).length = m := by
  simp [cstLayer]

theorem cstLayer_succ (b : Bool) (m : ℕ) :
    cstLayer b (m + 1) = Gate.cst b :: cstLayer b m := rfl

theorem wf_cstLayer (b : Bool) (m : ℕ) : wf (cstLayer b m) := by
  induction m with
  | zero => exact trivial
  | succ m ih => exact ⟨trivial, ih⟩

theorem inpsLt_cstLayer (b : Bool) (m w : ℕ) : inpsLt w (cstLayer b m) := by
  induction m with
  | zero => intro g hg; cases hg
  | succ m ih =>
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg'
      · exact trivial
      · exact ih g hg'

theorem vals_cstLayer (x : Word) (b : Bool) (m : ℕ) :
    vals x (cstLayer b m) = List.replicate m b := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [cstLayer_succ, vals, ih]
      simp only [gateVal]
      exact (List.replicate_succ' (n := m) (a := b)).symm

/-! ### The standalone layers -/

theorem wf_inpLayer (idx : ℕ → ℕ) (m : ℕ) : wf (inpLayer idx m) := by
  have h := wf_inpLayer_append (C := []) (idx := idx) trivial m
  simpa using h

theorem inpsLt_inpLayer {idx : ℕ → ℕ} {w : ℕ} (m : ℕ) (h : ∀ c, c < m → idx c < w) :
    inpsLt w (inpLayer idx m) := by
  have h' := inpsLt_inpLayer_append (C := []) (w := w) (idx := idx)
    (fun g hg => absurd hg (by simp)) m h
  simpa using h'

theorem vals_inpLayer (x : Word) (idx : ℕ → ℕ) (m : ℕ) :
    vals x (inpLayer idx m) = (List.range m).map (fun c => x.getD (idx c) false) := by
  have h := vals_inpLayer_append (C := []) x (idx := idx) m
  simpa [vals] using h

/-! ### Families realizing a word function -/

/-- **A P-uniform family realizing the word function `F` of `r` arguments at width `m`**: its
circuit inputs are the `r` argument signals laid side by side, and its topmost `2 * m` gates carry
the signal of the value. -/
structure SigFam (r : ℕ) (m : ℕ → ℕ) (F : List Word → Word) (cf : ℕ → Circuit) : Prop where
  /-- Every member is well formed. -/
  wfC : ∀ n, wf (cf n)
  /-- It reads only the wires of the argument signals. -/
  inpC : ∀ n, inpsLt (r * (2 * m n)) (cf n)
  /-- It has at least as many gates as the output signal has wires. -/
  widthC : ∀ n, 2 * m n ≤ (cf n).length
  /-- Its descriptions are produced by a single Cobham term. -/
  codeC : CodeUniform cf
  /-- **Its topmost `2 * m n` gates carry the value.** -/
  outC : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
    topVals (2 * m n) (vals (encArgs (m n) args) (cf n)) = encSig (m n) (F args)

end Tseitin

open Complexity.Tseitin

/-- The word function `F` of `r` arguments is realized at width `m` by some P-uniform family. -/
def SigUniform (r : ℕ) (m : ℕ → ℕ) (F : List Word → Word) : Prop :=
  ∃ cf : ℕ → Tseitin.Circuit, Tseitin.SigFam r m F cf

/-- Realizability only depends on the values of the function on the arguments the width admits. -/
theorem sigUniform_of_eval_eq {r : ℕ} {m : ℕ → ℕ} {F G : List Word → Word}
    (h : SigUniform r m F)
    (heq : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
      encSig (m n) (F args) = encSig (m n) (G args)) :
    SigUniform r m G := by
  obtain ⟨cf, hcf⟩ := h
  exact ⟨cf, { hcf with
    outC := fun n args hlen hle => by rw [hcf.outC n args hlen hle, heq n args hlen hle] }⟩

/-- A Cobham term writing `1^{2 * m n}` from a term writing `1^{m n}`. -/
theorem exists_twiceT {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (2 * m x.length) true := by
  refine ⟨.comp Cob.concat [mT, mT], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_concat, hm x,
    ← List.replicate_add]
  congr 1
  omega

/-- A Cobham term writing `1^{i * k n}` from a term writing `1^{k n}`. -/
theorem exists_mulConstT {k : ℕ → ℕ} {kT : Cob} (i : ℕ)
    (hk : ∀ x : Word, kT.eval [x] = List.replicate (k x.length) true) :
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (i * k x.length) true := by
  refine ⟨.comp .smash [Cob.constT (List.replicate i true), kT], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_constT, hk x,
    List.getD_cons_zero, List.getD_cons_succ, List.length_replicate]

/-! ### The constant empty word -/

/-- **The constant empty word is realized**: a layer of constant gates. -/
theorem sigUniform_empty {r : ℕ} {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun _ => []) := by
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  refine ⟨fun n => Tseitin.cstLayer false (2 * m n), ?_⟩
  refine ⟨fun n => Tseitin.wf_cstLayer _ _, fun n => Tseitin.inpsLt_cstLayer _ _ _,
    fun n => by simp, ?_, ?_⟩
  · -- the description of a layer of constant gates
    refine codeUniform_layerP (K := 11) (cnt := twoT)
      (padT := Cob.catL [.comp .smash [Cob.proj 0, Cob.constT [true]], Cob.constT [false], twoT])
      (pw := fun n => dmW n (2 * m n))
      (blkT := CircCode.tokTerm 2 .empty .empty)
      (tmpl := fun _ _ => Tseitin.Gate.cst false) htwo ?_ ?_ ?_
    · intro x
      simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil, Cob.eval_constT, Cob.eval_comp, Cob.eval_smash, Cob.eval_proj,
        List.getD_cons_zero, List.getD_cons_succ, htwo x]
      simp [dmW]
    · intro n y c
      exact CircCode.eval_tokTerm (g := Tseitin.Gate.cst false) (by simp [CircCode.fld1])
        (by simp [CircCode.fld2])
    · intro n c l hc
      rw [CircCode.length_encGate]
      simp only [CircCode.tag, CircCode.fld1, CircCode.fld2, length_dmW]
      omega
  · intro n args hlen hle
    have hv : vals (encArgs (m n) args) (Tseitin.cstLayer false (2 * m n))
        = List.replicate (2 * m n) false := Tseitin.vals_cstLayer _ _ _
    rw [hv, Tseitin.topVals, List.length_replicate, Nat.sub_self, List.drop_zero,
      Tseitin.encSig_nil]

/-! ### The projections -/

/-- **A projection is realized**: a layer of input gates reading the block of the argument. -/
theorem sigUniform_proj {r i : ℕ} {m : ℕ → ℕ} {mT : Cob} (hi : i < r)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => args.getD i []) := by
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  obtain ⟨baseT, hbase⟩ := exists_mulConstT (k := fun n => 2 * m n) i htwo
  obtain ⟨sT, hs⟩ := exists_mulConstT (k := fun n => 2 * m n) r htwo
  refine ⟨fun n => Tseitin.inpLayer (fun c => i * (2 * m n) + c) (2 * m n), ?_⟩
  refine ⟨fun n => Tseitin.wf_inpLayer _ _, ?_, fun n => by simp, ?_, ?_⟩
  · intro n
    refine Tseitin.inpsLt_inpLayer _ (fun c hc => ?_)
    have : (i + 1) * (2 * m n) ≤ r * (2 * m n) := Nat.mul_le_mul_right _ hi
    nlinarith
  · exact codeUniform_selInpLayer (S := fun n => r * (2 * m n))
      (fun n => Nat.mul_le_mul_right _ (le_of_lt hi)) hbase htwo hs
  · intro n args hlen hle
    have hv := Tseitin.vals_inpLayer (encArgs (m n) args) (fun c => i * (2 * m n) + c) (2 * m n)
    rw [hv, Tseitin.topVals]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.drop_zero]
    refine List.ext_getElem (by simp) ?_
    intro j h1 h2
    have hj : j < 2 * m n := by simpa using h1
    have hgi : i < args.length := by omega
    have hval := getD_encArgs (m n) args hgi hj
    rw [List.getD_eq_getElem (l := Tseitin.encSig (m n) (args.getD i [])) (d := false)
      (by simpa using h2)] at hval
    simp only [List.getElem_map, List.getElem_range]
    exact hval

end Complexity
