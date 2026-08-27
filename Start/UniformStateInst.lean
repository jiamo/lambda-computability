/-
# An instance of the poly-state rule: divisibility of the binary value by the length

`Start/UniformStateCode.lean` shows that the language of an automaton whose number of states may
grow polynomially with the length of the input is decided by a P-uniform circuit family, provided
the data of the automaton is computed in unary by Cobham terms.  Here we exercise that rule on a
concrete language that is neither regular nor symmetric:

> the word `x`, read as a binary numeral (most significant bit first), is divisible by `|x| + 1`.

The automaton reads the bits of `x` and keeps the value read so far modulo `|x| + 1`; it therefore
has `|x| + 1` states, so it is genuinely a poly-state automaton and no finite automaton can be
substituted for it.

Main definitions:

* `Complexity.binVal` — the binary value of a word, most significant bit first;
* `Complexity.BinDivLang` — the language above;
* `Complexity.binDelta`, `Complexity.binAc` — the automaton.

Main results:

* `Complexity.stateLang_binDelta` — the automaton decides `BinDivLang`;
* `Complexity.stateUniform_bin` — its data is Cobham-computable in unary;
* `Complexity.pUniformDecidable_binDiv` — **`BinDivLang` is decided by a P-uniform circuit
  family**;
* `Complexity.polyManyOne_SAT_binDiv` — hence it reduces to SAT in polynomial time.
-/
import Start.UniformStateCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### The binary value of a word -/

/-- The binary value of a word, most significant bit first. -/
def binVal (x : Word) : ℕ := x.foldl (fun v b => 2 * v + cond b 1 0) 0

/-- Folding the binary value modulo `k` computes the binary value modulo `k`. -/
theorem foldl_binVal_mod (k : ℕ) : ∀ (x : Word) (s : ℕ),
    x.foldl (fun s b => (2 * s + cond b 1 0) % k) (s % k)
      = (x.foldl (fun v b => 2 * v + cond b 1 0) s) % k := by
  intro x
  induction x with
  | nil => intro s; rfl
  | cons b t ih =>
      intro s
      have hstep : (2 * (s % k) + cond b 1 0) % k = (2 * s + cond b 1 0) % k :=
        (((Nat.mod_modEq s k).mul_left 2).add_right (cond b 1 0))
      rw [List.foldl_cons, List.foldl_cons, hstep, ih (2 * s + cond b 1 0)]

/-- **The language**: the binary value of the word is divisible by its length plus one. -/
def BinDivLang : Language := fun x => binVal x % (x.length + 1) = 0

/-! ### The automaton -/

/-- The transition function: keep the value read so far modulo `n + 1`. -/
def binDelta (n s : ℕ) (b : Bool) : ℕ := (2 * s + cond b 1 0) % (n + 1)

/-- The accepting states: the value read is `0` modulo `n + 1`. -/
def binAc : ℕ → ℕ → Bool := fun _ s => decide (s = 0)

theorem binDelta_lt (n s : ℕ) (b : Bool) : binDelta n s b < n + 1 :=
  Nat.mod_lt _ (Nat.succ_pos n)

/-- **The automaton decides the language.** -/
theorem stateLang_binDelta : StateLang binDelta binAc = BinDivLang := by
  funext x
  have h := foldl_binVal_mod (x.length + 1) x 0
  rw [Nat.zero_mod] at h
  simp only [StateLang, BinDivLang, binDelta, binAc, h, binVal, decide_eq_true_eq]

/-! ### Uniformity -/

/-- **The data of the automaton is computed in unary by Cobham terms.** -/
theorem stateUniform_bin : StateUniform binDelta binAc := by
  refine ⟨fun n => n + 1,
    .comp (.app true) [.comp .smash [.proj 0, Cob.constT [true]]],
    Cob.modT (.comp .smash [.proj 0, Cob.constT [true, true]])
      (.comp (.app true) [.proj 1]),
    Cob.modT (.comp (.app true) [.comp .smash [.proj 0, Cob.constT [true, true]]])
      (.comp (.app true) [.proj 1]),
    .comp Cob.notC [.proj 0],
    fun n => Nat.succ_pos n, binDelta_lt, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, Cob.eval_smash,
      Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
      List.length_cons, List.length_nil, List.replicate_succ]
    norm_num
  · intro s p
    have hp : (Cob.comp (Cob.app true) [Cob.proj 1]).eval
        [List.replicate s true, List.replicate p true] = List.replicate (p + 1) true := by
      simp [List.replicate_succ]
    have hs : (Cob.comp Cob.smash [Cob.proj 0, Cob.constT [true, true]]).eval
        [List.replicate s true, List.replicate p true] = List.replicate (2 * s) true := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
        Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, List.length_replicate,
        List.length_cons, List.length_nil]
      congr 1
      ring
    rw [Cob.eval_modT (Nat.succ_pos p) hs hp, binDelta]
    simp
  · intro s p
    have hp : (Cob.comp (Cob.app true) [Cob.proj 1]).eval
        [List.replicate s true, List.replicate p true] = List.replicate (p + 1) true := by
      simp [List.replicate_succ]
    have hs : (Cob.comp (Cob.app true)
        [Cob.comp Cob.smash [Cob.proj 0, Cob.constT [true, true]]]).eval
        [List.replicate s true, List.replicate p true] = List.replicate (2 * s + 1) true := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_app, Cob.eval_smash,
        Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ,
        List.length_replicate, List.length_cons, List.length_nil]
      rw [show 2 * s + 1 = (s * 2) + 1 from by ring, List.replicate_succ]
    rw [Cob.eval_modT (Nat.succ_pos p) hs hp, binDelta]
    simp
  · intro s p
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, Cob.eval_notC,
      List.getD_cons_zero, binAc, bw]
    by_cases h : s = 0
    · simp [h]
    · simp [h, List.replicate_eq_nil_iff]

/-- **The language is decided by a P-uniform circuit family.** -/
theorem pUniformDecidable_binDiv : PUniformDecidable BinDivLang := by
  rw [← stateLang_binDelta]
  exact pUniformDecidable_stateLang stateUniform_bin

/-- **The language reduces to SAT in polynomial time**, unconditionally. -/
theorem polyManyOne_SAT_binDiv : BinDivLang ≤ₘᵖ Sat.SAT :=
  polyManyOne_SAT_of_pUniformDecidable pUniformDecidable_binDiv

end Complexity
