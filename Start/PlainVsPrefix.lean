/-
# Plain versus prefix-free complexity

Two complexity measures for a natural number live in this development:

* `Lambda.kolm s` — *plain* complexity, the least number of **syntax nodes** of a closed program
  for `s` (`Start/Kolmogorov.lean`);
* `Lambda.kolmP s` — *prefix* complexity, the least number of **bits** of a closed program for `s`
  in the self-delimiting binary coding `Lambda.bits` (`Start/ChaitinOmega.lean`).

Chaitin's comparison theorem relates the plain and prefix complexities of a string; here it takes
the following sharp form, because a self-delimiting code word has at least one bit per syntax node
and at most two:

  `Lambda.kolm s ≤ Lambda.kolmP s ≤ 2 * Lambda.kolm s`   (`Lambda.kolm_le_kolmP_le_two_mul_kolm`).

In particular no logarithmic correction term is needed: passing to the self-delimiting coding
costs at most a factor two, and the classical `+ 2 log` overhead is already paid for by the fact
that `Lambda.bits` spends two bits on every constructor.  Combining with the compact numerals of
`Start/KolmogorovBinary.lean` gives the logarithmic upper bound
`Lambda.exists_const_kolmP_le_size : kolmP n = O(log n)`, and Kraft's inequality
(`Lambda.kraft_kolmP`) shows the prefix measure cannot be lowered much further: the counting
bound `Lambda.exists_incompressible_kolmP` produces numbers of arbitrarily large prefix
complexity.
-/

import Start.ChaitinOmega
import Start.KolmogorovBinary

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- A self-delimiting code word has at least one bit per syntax node. -/
theorem size_le_bits_length : ∀ t : Lambda, size t ≤ (bits t).length := by
  intro t
  induction t with
  | var i => simp [size]
  | lam u ih => simp [size]; omega
  | app a b iha ihb => simp [size]; omega

/-- **Plain complexity is below prefix complexity.**  (Both are measured with their own unit: a
syntax node for `kolm`, a bit for `kolmP`.) -/
theorem kolm_le_kolmP (s : ℕ) : kolm s ≤ kolmP s := by
  obtain ⟨t, ht, hlen⟩ := exists_program_of_kolmP s
  calc kolm s ≤ size t := kolm_le_of_isProgramFor ht
    _ ≤ (bits t).length := size_le_bits_length t
    _ = kolmP s := hlen

/-- **The comparison theorem for the plain and the prefix measure.** -/
theorem kolm_le_kolmP_le_two_mul_kolm (s : ℕ) : kolm s ≤ kolmP s ∧ kolmP s ≤ 2 * kolm s :=
  ⟨kolm_le_kolmP s, kolmP_le_two_mul_kolm s⟩

/-- Prefix complexity is also logarithmic in the number described. -/
theorem exists_const_kolmP_le_size : ∃ c : ℕ, ∀ n : ℕ, kolmP n ≤ c * (Nat.size n + 1) := by
  obtain ⟨c, hc⟩ := exists_const_kolm_le_size
  refine ⟨2 * c, fun n => ?_⟩
  calc kolmP n ≤ 2 * kolm n := kolmP_le_two_mul_kolm n
    _ ≤ 2 * (c * (Nat.size n + 1)) := by
        exact Nat.mul_le_mul_left 2 (hc n)
    _ = 2 * c * (Nat.size n + 1) := by ring

/-- Incompressibility transfers to the prefix measure. -/
theorem exists_incompressible_kolmP (n : ℕ) : ∃ s : ℕ, n ≤ kolmP s := by
  obtain ⟨s, hs⟩ := exists_incompressible n
  exact ⟨s, le_trans hs (kolm_le_kolmP s)⟩

/-- A code word is at most `4 * encode t + 2` bits long: the bit length is bounded by twice the
size, and the size by twice the code. -/
theorem bits_length_le_encode (t : Lambda) : (bits t).length ≤ 4 * Lambda.encode t + 2 := by
  have h1 := bits_length_le_two_mul_size t
  have h2 := size_le_encode t
  omega

/-- **The relation `kolmP s ≤ n` is undecidable** — Berry's paradox for the prefix measure. -/
theorem not_computablePred_kolmP_le : ¬ ComputablePred (fun p : ℕ × ℕ => kolmP p.1 ≤ p.2) := by
  intro hdec
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp hdec.not
  have hfe' : ∀ s n : ℕ, (¬ kolmP s ≤ n) ↔ f (s, n) = Bool.true := by
    intro s n
    exact iff_of_eq (congrFun hfe (s, n))
  set pr : ℕ → ℕ →. Bool := fun c s => (Part.some (f (s, 4 * c + 2)) : Part Bool)
  have hprPartrec : Partrec₂ pr := by
    have hcomp : Computable fun x : ℕ × ℕ => f (x.2, 4 * x.1 + 2) :=
      hf.comp (Computable.pair Computable.snd
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.fst)
          (Primrec.const 2)).to_comp)
    exact hcomp.partrec
  have hsearch : Partrec fun c => Nat.rfind (pr c) := Partrec.rfind hprPartrec
  have hdom : ∀ c : ℕ, (Nat.rfind (pr c)).Dom := by
    intro c
    obtain ⟨s, hs⟩ := exists_incompressible_kolmP (4 * c + 3)
    refine Nat.rfind_dom.mpr ⟨s, ?_, fun {_} _ => trivial⟩
    have hne : ¬ kolmP s ≤ 4 * c + 2 := by omega
    have hval : pr c s = Part.some (f (s, 4 * c + 2)) := rfl
    rw [hval, (hfe' s (4 * c + 2)).mp hne]
    exact Part.mem_some _
  obtain ⟨G, hGc, hG⟩ := lambdaComputable_of_partrec_closed hsearch
  obtain ⟨X, hXc, hX⟩ := exists_code_fixed_point_closed hGc
  set c : ℕ := Lambda.encode X
  set m : ℕ := (Nat.rfind (pr c)).get (hdom c)
  have hmem : Nat.rfind (pr c) = Part.some m := Part.get_eq_iff_eq_some.mp rfl
  have hbig : ¬ kolmP m ≤ 4 * c + 2 := by
    have hspec : Bool.true ∈ pr c m := Nat.rfind_spec (hmem ▸ Part.mem_some m)
    have hval : pr c m = Part.some (f (m, 4 * c + 2)) := rfl
    rw [hval] at hspec
    exact (hfe' m (4 * c + 2)).mpr (Part.mem_some_iff.mp hspec).symm
  have hred : Lambda.reduces (Lambda.app G (Lambda.church c)) (Lambda.church m) :=
    (hG c m).1 hmem
  have hprog : IsProgramFor X m := ⟨hXc, Lambda.reduces_trans hX hred⟩
  have h1 : kolmP m ≤ (bits X).length := kolmP_le_of_isProgramFor hprog
  have h2 : (bits X).length ≤ 4 * c + 2 := bits_length_le_encode X
  exact hbig (le_trans h1 h2)

/-- **Prefix complexity is not computable.** -/
theorem not_computable_kolmP : ¬ Computable kolmP := by
  intro hK
  obtain ⟨_, hprim⟩ := Primrec.nat_le
  have hle : Computable fun q : ℕ × ℕ => decide (q.1 ≤ q.2) :=
    hprim.to_comp.of_eq (fun q => by simp)
  refine not_computablePred_kolmP_le (ComputablePred.computable_iff.mpr
    ⟨fun p : ℕ × ℕ => decide (kolmP p.1 ≤ p.2), ?_, by funext p; simp⟩)
  exact (hle.comp (Computable.pair (hK.comp Computable.fst) Computable.snd)).of_eq
    (fun p => by simp)

end Lambda

end
