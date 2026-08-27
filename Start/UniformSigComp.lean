/-
# Composition: the compiler's rule for `Cob.comp`

`Start/UniformSignal.lean` presents a word on wires and says what it is for a P-uniform family of
circuits to *realize* a word function of `r` arguments.  This module supplies the rule for the
composition `f(g₁(x), …, g_r(x))`.

Two ingredients are needed, and both are now available.  The values of the `gᵢ` have to be produced
*side by side*, which is the parallel product of `Start/UniformPar.lean`; and the family for `f`
has to be run on those wires, which is the composition of P-uniform families of
`Start/UniformCompose.lean`.

Main definitions:

* `Complexity.Tseitin.SigListFam`, `Complexity.SigListUniform` — a P-uniform family realizing a
  *list* of word functions, its output being the argument word of the next stage.

Main results:

* `Complexity.sigListUniform_nil`, `Complexity.sigListUniform_cons` — the list of realized
  functions is built one function at a time, by the parallel product;
* `Complexity.sigUniform_comp` — **a composition of realized functions is realized.**
-/

import Start.UniformSignal

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Two small facts about circuits -/

/-- The topmost values of a concatenation come from its upper part. -/
theorem topVals_append_of_le {u v : List Bool} {w : ℕ} (h : w ≤ v.length) :
    topVals w (u ++ v) = topVals w v := by
  have hlen : (u ++ v).length = u.length + v.length := by simp
  rw [topVals, topVals, hlen]
  have hsplit : u.length + v.length - w = u.length + (v.length - w) := by omega
  rw [hsplit, List.drop_append]
  simp

/-- A rerouted circuit reads no circuit input at all. -/
theorem inpsLt_reroute (w d e : ℕ) (C : Circuit) : inpsLt w (reroute d e C) := by
  intro g hg
  obtain ⟨g', -, rfl⟩ := List.mem_map.1 hg
  cases g' <;> exact trivial

/-- The empty list of values occupies no wire. -/
@[simp] theorem encArgs_nil (m : ℕ) : encArgs m [] = [] := rfl

/-- The signals of a list of values, one after the other. -/
theorem encArgs_cons (m : ℕ) (u : Word) (us : List Word) :
    encArgs m (u :: us) = encSig m u ++ encArgs m us := rfl

/-- **A P-uniform family realizing a list of word functions**: its topmost wires carry the
argument word made of their values. -/
structure SigListFam (r : ℕ) (m : ℕ → ℕ) (Fs : List (List Word → Word)) (cf : ℕ → Circuit) :
    Prop where
  /-- Every member is well formed. -/
  wfC : ∀ n, wf (cf n)
  /-- It reads only the wires of the argument signals. -/
  inpC : ∀ n, inpsLt (r * (2 * m n)) (cf n)
  /-- It has at least as many gates as its output has wires. -/
  widthC : ∀ n, Fs.length * (2 * m n) ≤ (cf n).length
  /-- Its descriptions are produced by a single Cobham term. -/
  codeC : CodeUniform cf
  /-- **Its topmost wires carry the values of the functions.** -/
  outC : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
    topVals (Fs.length * (2 * m n)) (vals (encArgs (m n) args) (cf n))
      = encArgs (m n) (Fs.map (fun F => F args))

end Tseitin

open Complexity.Tseitin

/-- The list of word functions `Fs` of `r` arguments is realized at width `m` by some P-uniform
family. -/
def SigListUniform (r : ℕ) (m : ℕ → ℕ) (Fs : List (List Word → Word)) : Prop :=
  ∃ cf : ℕ → Tseitin.Circuit, Tseitin.SigListFam r m Fs cf

/-- **The empty list is realized** by the empty circuit. -/
theorem sigListUniform_nil {r : ℕ} {m : ℕ → ℕ} : SigListUniform r m [] := by
  refine ⟨fun _ => [], ⟨fun _ => trivial, fun _ g hg => absurd hg (by simp), fun _ => by simp,
    codeUniform_const [], ?_⟩⟩
  intro n args _ _
  have hnil : vals (encArgs (m n) args) ([] : Tseitin.Circuit) = [] := rfl
  simp [Tseitin.topVals, hnil]

/-- **One more function is realized** by the parallel product of its family with the family of the
others. -/
theorem sigListUniform_cons {r : ℕ} {m : ℕ → ℕ} {F : List Word → Word}
    {Fs : List (List Word → Word)} (hF : SigUniform r m F) (hFs : SigListUniform r m Fs)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigListUniform r m (F :: Fs) := by
  obtain ⟨cf1, h1⟩ := hF
  obtain ⟨cf2, h2⟩ := hFs
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  obtain ⟨wsT, hws⟩ := exists_mulConstT (k := fun n => 2 * m n) Fs.length htwo
  refine ⟨fun n => Tseitin.parC (cf1 n) (cf2 n) (2 * m n) (Fs.length * (2 * m n)), ?_⟩
  refine ⟨fun n => Tseitin.wf_parC (h1.wfC n) (h2.wfC n) (h1.widthC n) (h2.widthC n),
    fun n => Tseitin.inpsLt_parC (h1.inpC n) (h2.inpC n), fun n => ?_,
    codeUniform_parC h1.codeC h2.codeC htwo hws, ?_⟩
  · have hlen := Tseitin.length_parC (cf1 n) (cf2 n) (2 * m n) (Fs.length * (2 * m n))
    rw [hlen, List.length_cons]
    ring_nf
    omega
  · intro n args hlen hle
    have hpar := Tseitin.topVals_parC (encArgs (m n) args) (B1 := cf1 n) (B2 := cf2 n)
      (w1 := 2 * m n) (w2 := Fs.length * (2 * m n)) (h1.wfC n) (h1.widthC n) (h2.widthC n)
    have harith : (F :: Fs).length * (2 * m n) = 2 * m n + Fs.length * (2 * m n) := by
      rw [List.length_cons]
      ring
    rw [harith, hpar, h1.outC n args hlen hle, h2.outC n args hlen hle, List.map_cons,
      Tseitin.encArgs_cons]

/-- **A composition of realized functions is realized**: the values of the inner functions are
produced side by side by the parallel product, and the family of the outer function is run on
them. -/
theorem sigUniform_comp {r : ℕ} {m : ℕ → ℕ} {f : List Word → Word}
    {Fs : List (List Word → Word)} (hf : SigUniform Fs.length m f)
    (hFs : SigListUniform r m Fs)
    (hbnd : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ m n) →
      ∀ F ∈ Fs, (F args).length ≤ m n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniform r m (fun args => f (Fs.map (fun F => F args))) := by
  obtain ⟨cff, hff⟩ := hf
  obtain ⟨cg, hg⟩ := hFs
  obtain ⟨twoT, htwo⟩ := exists_twiceT hm
  obtain ⟨wsT, hws⟩ := exists_mulConstT (k := fun n => 2 * m n) Fs.length htwo
  obtain ⟨lenG, hlenG⟩ := exists_lenTerm hg.codeC
  set W : ℕ → ℕ := fun n => Fs.length * (2 * m n) with hW
  set e : ℕ → ℕ := fun n => (cg n).length - W n with he
  have heT : ∀ x : Word, (Cob.comp Cob.dropU [wsT, lenG]).eval [x]
      = List.replicate (e x.length) true := by
    intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_dropU, hws x, hlenG x,
      List.length_replicate, List.drop_replicate]
    rfl
  have hele : ∀ n, e n ≤ (cg n).length := fun n => Nat.sub_le _ _
  have hsub : ∀ n, (cg n).length - e n = W n := by
    intro n
    have := hg.widthC n
    simp only [he, hW] at *
    omega
  refine ⟨fun n => Tseitin.reroute (cg n).length (e n) (cff n) ++ cg n, ?_⟩
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_,
    codeUniform_compose hff.codeC hg.codeC heT, ?_⟩
  · refine Tseitin.wf_reroute_append (cg n) (hg.wfC n) (e n) (hele n) (cff n) (hff.wfC n) ?_
    rw [hsub n]
    exact hff.inpC n
  · intro g hgmem
    rcases List.mem_append.1 hgmem with hg' | hg'
    · exact Tseitin.inpsLt_reroute _ _ _ _ g hg'
    · exact hg.inpC n g hg'
  · have := hff.widthC n
    simp only [List.length_append, Tseitin.length_reroute]
    omega
  · intro n args hlen hle
    have hvals := Tseitin.vals_reroute_append (encArgs (m n) args) (cg n) (e n) (hele n)
      (cff n) (hff.wfC n) (by rw [hsub n]; exact hff.inpC n)
    have hdrop : (vals (encArgs (m n) args) (cg n)).drop (e n)
        = encArgs (m n) (Fs.map (fun F => F args)) := by
      have hlenv : (vals (encArgs (m n) args) (cg n)).length = (cg n).length := by simp
      have := hg.outC n args hlen hle
      rw [Tseitin.topVals, hlenv] at this
      rw [← this, he]
    have hargs : (Fs.map (fun F => F args)).length = Fs.length := by simp
    have hargsle : ∀ u ∈ Fs.map (fun F => F args), u.length ≤ m n := by
      intro u hu
      obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hu
      exact hbnd n args hlen hle F hF
    have hupper := hff.outC n (Fs.map (fun F => F args)) hargs hargsle
    rw [hvals, hdrop, Tseitin.topVals_append_of_le (by simpa using hff.widthC n), hupper]

end Complexity
