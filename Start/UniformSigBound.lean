/-
# Realizing a word function on arguments of a bounded length

`Start/UniformSigComp.lean` composes families that realize their functions on *every* argument the
width admits.  That is too strong a demand for a compiler: a term such as `x ↦ b :: x` lengthens
its argument, so a composition of such terms is correct only on arguments that leave room for the
growth.  The remedy is to separate the two roles the width plays, by carrying a second function `k`
— the length the arguments are promised not to exceed — beside the width `m` of the wires.

Everything else is unchanged: the same circuits, the same parallel product, the same composition of
P-uniform families.  Only the correctness clause is relativized, and the composition rule now asks
that the values of the inner terms respect the promise made to the outer one.

Main definitions:

* `Complexity.Tseitin.SigFamB`, `Complexity.SigUniformB` — a P-uniform family realizing a word
  function on arguments of length at most `k n`, on wires of width `m n`;
* `Complexity.Tseitin.SigListFamB`, `Complexity.SigListUniformB` — the same for a list of
  functions.

Main results:

* `Complexity.sigUniformB_of_sigUniform` — a family correct at every admissible argument is in
  particular correct at the short ones;
* `Complexity.sigListUniformB_nil`, `Complexity.sigListUniformB_cons` — the list of realized
  functions is built one function at a time;
* `Complexity.sigUniformB_comp` — **a composition is realized whenever the values of the inner
  terms obey the promise made to the outer term.**
-/

import Start.UniformSigComp

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-- **A P-uniform family realizing `F` on arguments of length at most `k n`**, on wires of width
`m n`. -/
structure SigFamB (r : ℕ) (m k : ℕ → ℕ) (F : List Word → Word) (cf : ℕ → Circuit) : Prop where
  /-- Every member is well formed. -/
  wfC : ∀ n, wf (cf n)
  /-- It reads only the wires of the argument signals. -/
  inpC : ∀ n, inpsLt (r * (2 * m n)) (cf n)
  /-- It has at least as many gates as the output signal has wires. -/
  widthC : ∀ n, 2 * m n ≤ (cf n).length
  /-- Its descriptions are produced by a single Cobham term. -/
  codeC : CodeUniform cf
  /-- **Its topmost `2 * m n` gates carry the value**, at every short argument. -/
  outC : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
    topVals (2 * m n) (vals (encArgs (m n) args) (cf n)) = encSig (m n) (F args)

/-- **A P-uniform family realizing a list of word functions** on arguments of length at most
`k n`. -/
structure SigListFamB (r : ℕ) (m k : ℕ → ℕ) (Fs : List (List Word → Word)) (cf : ℕ → Circuit) :
    Prop where
  /-- Every member is well formed. -/
  wfC : ∀ n, wf (cf n)
  /-- It reads only the wires of the argument signals. -/
  inpC : ∀ n, inpsLt (r * (2 * m n)) (cf n)
  /-- It has at least as many gates as its output has wires. -/
  widthC : ∀ n, Fs.length * (2 * m n) ≤ (cf n).length
  /-- Its descriptions are produced by a single Cobham term. -/
  codeC : CodeUniform cf
  /-- **Its topmost wires carry the values of the functions**, at every short argument. -/
  outC : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
    topVals (Fs.length * (2 * m n)) (vals (encArgs (m n) args) (cf n))
      = encArgs (m n) (Fs.map (fun F => F args))

end Tseitin

open Complexity.Tseitin

/-- The word function `F` of `r` arguments is realized at width `m` on arguments of length at most
`k`. -/
def SigUniformB (r : ℕ) (m k : ℕ → ℕ) (F : List Word → Word) : Prop :=
  ∃ cf : ℕ → Tseitin.Circuit, Tseitin.SigFamB r m k F cf

/-- The list `Fs` of word functions of `r` arguments is realized at width `m` on arguments of
length at most `k`. -/
def SigListUniformB (r : ℕ) (m k : ℕ → ℕ) (Fs : List (List Word → Word)) : Prop :=
  ∃ cf : ℕ → Tseitin.Circuit, Tseitin.SigListFamB r m k Fs cf

/-- A family correct at every argument the width admits is correct at the short arguments. -/
theorem sigUniformB_of_sigUniform {r : ℕ} {m k : ℕ → ℕ} {F : List Word → Word}
    (h : SigUniform r m F) (hk : ∀ n, k n ≤ m n) : SigUniformB r m k F := by
  obtain ⟨cf, hcf⟩ := h
  exact ⟨cf, ⟨hcf.wfC, hcf.inpC, hcf.widthC, hcf.codeC, fun n args hlen hle =>
    hcf.outC n args hlen (fun u hu => le_trans (hle u hu) (hk n))⟩⟩

/-- **The empty list is realized** by the empty circuit. -/
theorem sigListUniformB_nil {r : ℕ} {m k : ℕ → ℕ} : SigListUniformB r m k [] := by
  refine ⟨fun _ => [], ⟨fun _ => trivial, fun _ g hg => absurd hg (by simp), fun _ => by simp,
    codeUniform_const [], ?_⟩⟩
  intro n args _ _
  have hnil : vals (encArgs (m n) args) ([] : Tseitin.Circuit) = [] := rfl
  simp [Tseitin.topVals, hnil]

/-- **One more function is realized** by the parallel product of its family with the family of the
others. -/
theorem sigListUniformB_cons {r : ℕ} {m k : ℕ → ℕ} {F : List Word → Word}
    {Fs : List (List Word → Word)} (hF : SigUniformB r m k F) (hFs : SigListUniformB r m k Fs)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigListUniformB r m k (F :: Fs) := by
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

/-- **A composition is realized** whenever the values of the inner functions, at the arguments the
inner promise admits, obey the promise made to the outer function. -/
theorem sigUniformB_comp {r : ℕ} {m k k' : ℕ → ℕ} {f : List Word → Word}
    {Fs : List (List Word → Word)} (hf : SigUniformB Fs.length m k' f)
    (hFs : SigListUniformB r m k Fs)
    (hbnd : ∀ (n : ℕ) (args : List Word), args.length = r → (∀ u ∈ args, u.length ≤ k n) →
      ∀ F ∈ Fs, (F args).length ≤ k' n)
    {mT : Cob} (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniformB r m k (fun args => f (Fs.map (fun F => F args))) := by
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
    have hargsle : ∀ u ∈ Fs.map (fun F => F args), u.length ≤ k' n := by
      intro u hu
      obtain ⟨F, hF, rfl⟩ := List.mem_map.1 hu
      exact hbnd n args hlen hle F hF
    have hupper := hff.outC n (Fs.map (fun F => F args)) hargs hargsle
    rw [hvals, hdrop, Tseitin.topVals_append_of_le (by simpa using hff.widthC n), hupper]

end Complexity
