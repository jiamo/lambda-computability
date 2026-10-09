/-
**`coNP` and the polynomial hierarchy.**

The levels of the polynomial hierarchy are defined from `P` by alternating a polynomially bounded
existential quantifier with complementation:

* `Σ₀ᵖ = P`;
* `Πₖᵖ` is the class of complements of `Σₖᵖ` languages;
* `Σₖ₊₁ᵖ = ∃ᵖ Πₖᵖ`: `x ∈ L` exactly when some witness `w` puts the pair `⟨x, w⟩` into a `Πₖᵖ`
  language `L'`.

Pairs are the self-delimiting pairing `Complexity.pairW` of `Start/NPInter.lean`.  The witness
bound follows the convention of `Complexity.InNP`: membership `⟨x, w⟩ ∈ L'` itself forces
`|w| ≤ p |x|` for a monotone polynomial `p`, rather than the bound being an extra conjunct.  With
`k = 0` this gives back exactly `NP` (`Complexity.inSigma_one_iff`), so the convention is the one
of the library's `NP`.

Main definitions:

* `Complexity.InCoNP` — the class `coNP`;
* `Complexity.ExistsP` — the polynomially bounded existential quantifier applied to a class;
* `Complexity.InSigma`, `Complexity.InPi` — the levels `Σₖᵖ`, `Πₖᵖ`;
* `Complexity.pairT` — the Cobham term computing the pairing `Complexity.pairW`.

Main results:

* `Complexity.inSigma_one_iff`, `Complexity.inPi_one_iff` — `Σ₁ᵖ = NP` and `Π₁ᵖ = coNP`;
* `Complexity.InNP.of_existsP` — `∃ᵖ NP = NP`: two existential quantifiers merge into one;
* `Complexity.inNP_of_inSigma_of_NP_eq_coNP`, `Complexity.inNP_of_inPi_of_NP_eq_coNP` —
  **if `NP = coNP` then the hierarchy collapses to `NP`**;
* `Complexity.NP_eq_coNP_of_peqNP` — `P = NP` implies `NP = coNP`;
* `Complexity.inP_of_inSigma_of_peqNP`, `Complexity.inP_of_inPi_of_peqNP` —
  **if `P = NP` then the hierarchy collapses to `P`**.
-/

import Start.NPInter

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### The pairing as a Cobham function -/

/-- The output block of the doubling transducer: every bit is written twice. -/
def dblOutT (_ : ℕ) (b : Bool) : Cob := .comp (.app b) [.app b]

/-- The Cobham term doubling every bit of its argument. -/
def dblTerm : Cob := lrunTerm 1 (fun _ _ => 0) dblOutT 2

theorem lrun_dbl (x : Word) :
    lrun (fun _ _ => 0) (fun _ b => [b, b]) 0 x = x.flatMap fun b => [b, b] := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [lrun, ih]

theorem eval_dblTerm (x : Word) : dblTerm.eval [x, []] = x.flatMap fun b => [b, b] := by
  have hK : ∀ s b, ((dblOutT s b).eval [([] : Word)]).length ≤ 2 + ([] : Word).length := by
    intro s b
    simp [dblOutT]
  rw [dblTerm, eval_lrunTerm (m := 1) (by norm_num) (fun _ _ => by norm_num) dblOutT [] hK x,
    ← lrun_dbl]
  simp [dblOutT]

/-- The Cobham term computing the pairing `pairW` of its first two arguments. -/
def pairT : Cob :=
  .comp Cob.concat
    [.comp Cob.concat [.comp dblTerm [.proj 0, .empty], .comp (.app true) [.comp (.app false)
      [.empty]]], .proj 1]

@[simp] theorem eval_pairT (x w : Word) : pairT.eval [x, w] = pairW x w := by
  simp [pairT, eval_dblTerm, pairW]

theorem length_pairW (x w : Word) : (pairW x w).length = 2 * x.length + 2 + w.length := by
  simp only [pairW, List.length_append, List.length_flatMap, List.length_cons, List.length_nil]
  simp [List.sum_replicate, List.map_const']
  ring

/-! ### `coNP` and the levels of the hierarchy -/

/-- `L` is in `coNP`: its complement is in `NP`. -/
def InCoNP (L : Language) : Prop := InNP (fun x => ¬ L x)

/-- The polynomially bounded existential quantifier applied to a class `C` of languages: `L` is
in `∃ᵖ C` when there are `L' ∈ C` and a monotone polynomial `p` such that `⟨x, w⟩ ∈ L'` forces
`|w| ≤ p |x|`, and `x ∈ L` exactly when `⟨x, w⟩ ∈ L'` for some `w`. -/
def ExistsP (C : Language → Prop) (L : Language) : Prop :=
  ∃ (L' : Language) (p : ℕ → ℕ), C L' ∧ PolyBound p ∧ Monotone p ∧
    (∀ x w, L' (pairW x w) → w.length ≤ p x.length) ∧
    (∀ x, L x ↔ ∃ w, L' (pairW x w))

/-- The level `Σₖᵖ` of the polynomial hierarchy: `Σ₀ᵖ = P` and `Σₖ₊₁ᵖ = ∃ᵖ Πₖᵖ`, where `Πₖᵖ`
consists of the complements of the `Σₖᵖ` languages. -/
def InSigma : ℕ → Language → Prop
  | 0 => InP
  | k + 1 => ExistsP (fun L' => InSigma k (fun x => ¬ L' x))

/-- The level `Πₖᵖ` of the polynomial hierarchy: the complements of the `Σₖᵖ` languages. -/
def InPi (k : ℕ) (L : Language) : Prop := InSigma k (fun x => ¬ L x)

@[simp] theorem inSigma_zero (L : Language) : InSigma 0 L ↔ InP L := Iff.rfl

theorem inSigma_succ (k : ℕ) (L : Language) : InSigma (k + 1) L ↔ ExistsP (InPi k) L := Iff.rfl

theorem ExistsP.mono {C D : Language → Prop} (hCD : ∀ L, C L → D L) {L : Language}
    (h : ExistsP C L) : ExistsP D L := by
  obtain ⟨L', p, hC, hp, hm, hb, hc⟩ := h
  exact ⟨L', p, hCD L' hC, hp, hm, hb, hc⟩

/-- A language and its double complement are the same. -/
theorem compl_compl_lang (L : Language) : (fun x => ¬ ¬ L x) = L := by
  funext x
  simp

theorem InP.of_compl {L : Language} (h : InP (fun x => ¬ L x)) : InP L := by
  have := h.compl
  rwa [compl_compl_lang] at this

/-! ### Two existential quantifiers merge -/

/-- **`∃ᵖ NP = NP`**: the witness of the merged quantifier is the pairing of the two witnesses. -/
theorem InNP.of_existsP {L : Language} (h : ExistsP InNP L) : InNP L := by
  obtain ⟨L', p, ⟨v, q, hqpoly, hqmono, hqbound, hqchar⟩, hpoly, hmono, hbound, hchar⟩ := h
  set V : Cob := .comp v [.comp pairT [.proj 0, .comp fstTerm [.proj 1, .empty]],
    .comp sndTerm [.proj 1, .empty]] with hV
  have hev : ∀ x y : Word, V.eval [x, y] = v.eval [pairW x (fstOf y), sndOf y] := by
    intro x y
    simp only [hV, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_succ, List.getD_cons_zero, Cob.eval_empty]
    rw [eval_fstTerm, eval_sndTerm, eval_pairT]
  refine ⟨V, fun n => 2 * p n + 3 + q (2 * n + 2 + p n), ?_, ?_, ?_, ?_⟩
  · have hlin : PolyBound (fun n => 2 * n + 2 + p n) :=
      (PolyBound.add (⟨2, 1, fun n => by ring_nf; omega⟩ : PolyBound (fun n => 2 * n + 2))
        hpoly)
    have hsum : PolyBound (fun n => p n + p n + 3 + q (2 * n + 2 + p n)) :=
      ((hpoly.add hpoly).add (polyBound_const 3)).add (hqpoly.comp hlin)
    exact hsum.mono (fun n => by omega)
  · intro m n hmn
    have h₁ := hmono hmn
    have h₂ : q (2 * m + 2 + p m) ≤ q (2 * n + 2 + p n) := hqmono (by omega)
    change 2 * p m + 3 + q (2 * m + 2 + p m) ≤ 2 * p n + 3 + q (2 * n + 2 + p n)
    omega
  · intro x y hy
    rw [hev] at hy
    have hL' : L' (pairW x (fstOf y)) := (hqchar _).2 ⟨_, hy⟩
    have hf := hbound x _ hL'
    have hs := hqbound _ _ hy
    rw [length_pairW] at hs
    have hs' : q (2 * x.length + 2 + (fstOf y).length) ≤ q (2 * x.length + 2 + p x.length) :=
      hqmono (by omega)
    have hlen := length_le_of_proj y
    change y.length ≤ 2 * p x.length + 3 + q (2 * x.length + 2 + p x.length)
    omega
  · intro x
    rw [hchar x]
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨u, hu⟩ := (hqchar _).1 hw
      refine ⟨pairW w u, ?_⟩
      rw [hev, fstOf_pairW, sndOf_pairW]
      exact hu
    · rintro ⟨y, hy⟩
      rw [hev] at hy
      exact ⟨_, (hqchar _).2 ⟨_, hy⟩⟩

/-! ### The first level -/

/-- **`Σ₁ᵖ = NP`.** -/
theorem inSigma_one_iff (L : Language) : InSigma 1 L ↔ InNP L := by
  constructor
  · intro h
    refine InNP.of_existsP (ExistsP.mono (fun L' hL' => ?_) h)
    exact inNP_of_inP (InP.of_compl hL')
  · rintro ⟨v, p, hpoly, hmono, hbound, hchar⟩
    set L' : Language := fun z => v.eval [fstOf z, sndOf z] ≠ [] with hL'
    have hP : InP L' := by
      refine ⟨.comp v [.comp fstTerm [.proj 0, .empty], .comp sndTerm [.proj 0, .empty]],
        fun z => ?_⟩
      simp only [hL', Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
        List.getD_cons_zero, Cob.eval_empty]
      rw [eval_fstTerm, eval_sndTerm]
    refine ⟨L', p, ?_, hpoly, hmono, ?_, ?_⟩
    · show InP (fun x => ¬ L' x)
      exact hP.compl
    · intro x w hw
      simp only [hL', fstOf_pairW, sndOf_pairW] at hw
      exact hbound x w hw
    · intro x
      simp only [hL', fstOf_pairW, sndOf_pairW]
      exact hchar x

/-- **`Π₁ᵖ = coNP`.** -/
theorem inPi_one_iff (L : Language) : InPi 1 L ↔ InCoNP L :=
  inSigma_one_iff _

/-! ### Collapses -/

/-- **If `NP = coNP`, every level `Σₖᵖ` is contained in `NP`.** -/
theorem inNP_of_inSigma_of_NP_eq_coNP (h : ∀ L, InNP L ↔ InCoNP L) :
    ∀ (k : ℕ) (L : Language), InSigma k L → InNP L := by
  intro k
  induction k with
  | zero => exact fun L hL => inNP_of_inP hL
  | succ k ih =>
      intro L hL
      refine InNP.of_existsP (ExistsP.mono (fun L' hL' => ?_) hL)
      exact (h L').2 (ih _ hL')

/-- **If `NP = coNP`, every level `Πₖᵖ` is contained in `NP`.** -/
theorem inNP_of_inPi_of_NP_eq_coNP (h : ∀ L, InNP L ↔ InCoNP L) (k : ℕ) (L : Language)
    (hL : InPi k L) : InNP L :=
  (h L).2 (inNP_of_inSigma_of_NP_eq_coNP h k _ hL)

/-- **The hierarchy collapses to `NP` if `NP = coNP`**: every level `Σₖᵖ` and `Πₖᵖ` equals
`NP` from the first level on. -/
theorem ph_collapse_of_NP_eq_coNP (h : ∀ L, InNP L ↔ InCoNP L) (k : ℕ) (L : Language) :
    (InSigma (k + 1) L ↔ InNP L) ∧ (InPi (k + 1) L ↔ InNP L) := by
  induction k generalizing L with
  | zero =>
      exact ⟨inSigma_one_iff L, (inPi_one_iff L).trans (h L).symm⟩
  | succ k ih =>
      have hS : ∀ L, InSigma (k + 2) L ↔ InNP L := by
        intro L
        refine ⟨inNP_of_inSigma_of_NP_eq_coNP h _ L, fun hL => ?_⟩
        obtain ⟨L', p, hC, hp, hm, hb, hc⟩ := (inSigma_one_iff L).2 hL
        exact ⟨L', p, (ih _).1.2 (inNP_of_inP hC), hp, hm, hb, hc⟩
      exact ⟨hS L, (hS _).trans (h L).symm⟩

/-- **`P = NP` implies `NP = coNP`**, since `P` is closed under complement. -/
theorem NP_eq_coNP_of_peqNP (h : PeqNP) (L : Language) : InNP L ↔ InCoNP L := by
  constructor
  · intro hL
    exact inNP_of_inP (h L hL).compl
  · intro hL
    exact inNP_of_inP (InP.of_compl (h _ hL))

/-- **If `P = NP`, every level `Σₖᵖ` is contained in `P`.** -/
theorem inP_of_inSigma_of_peqNP (h : PeqNP) (k : ℕ) (L : Language) (hL : InSigma k L) :
    InP L :=
  h L (inNP_of_inSigma_of_NP_eq_coNP (NP_eq_coNP_of_peqNP h) k L hL)

/-- **If `P = NP`, every level `Πₖᵖ` is contained in `P`.** -/
theorem inP_of_inPi_of_peqNP (h : PeqNP) (k : ℕ) (L : Language) (hL : InPi k L) : InP L :=
  h L (inNP_of_inPi_of_NP_eq_coNP (NP_eq_coNP_of_peqNP h) k L hL)

end Complexity
