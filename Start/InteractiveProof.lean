/-
**Interactive proofs.**

The class `IP` of Goldwasser, Micali and Rackoff, in the time model of this library: the verifier
is given by Cobham terms (`Start/ComplexityClasses.lean`), so it runs in polynomial time; the
prover is an arbitrary function; the acceptance probability is a rational number obtained by
counting over the random words of the prescribed length (`Start/CountProb.lean`) — a finite
average, no measure theory.

**The protocol.**  A verifier `V` fixes, as polynomial-time functions of the input `x`, the number
of rounds `|V.rounds(x)|`, the number of random bits `|V.coins(x)|` and a bound `|V.msgLen(x)|`
on the length of every message.  The verifier's coins `r` are private.  In every round the verifier
sends `V.ask(x, r, t)`, and the prover answers with `P(t')`, where `t` is the transcript so far and
`t'` is `t` extended by the verifier's message.  Both messages are cut to the length bound, and the
transcript records each message `w` as `1^{|w|} 0 w` (`Complexity.encMsg`), so that it can be read
back by a polynomial-time function.  After the last round the verifier decides with
`V.decide(x, r, t)`.

Because every length involved is the length of the value of a Cobham term on `x`, all of them are
polynomial in `|x|` (`Complexity.Cob.polyLen`), and so is the length of the transcript
(`Complexity.Verifier.length_transcript_le`).

Main definitions:

* `Complexity.encMsg` — the self-delimiting record of a message in the transcript;
* `Complexity.Verifier`, `Complexity.Prover` — the two parties;
* `Complexity.Verifier.transcript`, `.accepts`, `.accProb` — the run of the protocol on given
  coins, its verdict, and the acceptance probability;
* `Complexity.IP` — the class: completeness `≥ 2/3` with some prover, soundness `≤ 1/3` against
  every prover.

Main results:

* `Complexity.inIP_of_inNP` — `NP ⊆ IP` (one message, no randomness);
* `Complexity.IP.of_reduction` — `IP` is closed downwards under polynomial-time many-one
  reductions.
-/

import Start.CountProb
import Start.CobhamFields
import Start.QbfCobReduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- The record of a message `w` in a transcript: its length in unary, a zero, then `w`. -/
def encMsg (w : Word) : Word := List.replicate w.length true ++ false :: w

@[simp] theorem length_encMsg (w : Word) : (encMsg w).length = 2 * w.length + 1 := by
  simp [encMsg]; omega

/-- A verifier of an interactive proof: five polynomial-time functions.  The number of rounds, the
number of random bits and the bound on the message length are the lengths of the values of
`rounds`, `coins` and `msgLen` on the input; `ask` computes the verifier's next message and
`decide` the final verdict from the input, the random word and the transcript. -/
structure Verifier where
  /-- The number of rounds is `|rounds(x)|`. -/
  rounds : Cob
  /-- The number of random bits is `|coins(x)|`. -/
  coins : Cob
  /-- Every message is cut to length `|msgLen(x)|`. -/
  msgLen : Cob
  /-- The verifier's next message, from `[x, r, t]`. -/
  ask : Cob
  /-- The verdict, from `[x, r, t]`: accept iff the value is nonempty. -/
  decide : Cob

/-- A prover: an arbitrary function from the transcript so far to its next message. -/
abbrev Prover := Word → Word

namespace Verifier

variable (V : Verifier)

/-- The number of rounds on input `x`. -/
def numRounds (x : Word) : ℕ := (V.rounds.eval [x]).length

/-- The number of random bits on input `x`. -/
def numCoins (x : Word) : ℕ := (V.coins.eval [x]).length

/-- The bound on the length of a message on input `x`. -/
def maxMsg (x : Word) : ℕ := (V.msgLen.eval [x]).length

/-- One round: the verifier's message, then the prover's answer, both cut to the length bound and
recorded in the transcript. -/
def round (P : Prover) (x r t : Word) : Word :=
  let t' := t ++ encMsg ((V.ask.eval [x, r, t]).take (V.maxMsg x))
  t' ++ encMsg ((P t').take (V.maxMsg x))

/-- The transcript of the whole interaction on input `x` and random word `r`. -/
def transcript (P : Prover) (x r : Word) : Word :=
  (V.round P x r)^[V.numRounds x] []

/-- The verdict of the verifier on input `x` and random word `r`. -/
def accepts (P : Prover) (x : Word) (r : List Bool) : Bool :=
  !(V.decide.eval [x, r, V.transcript P x r]).isEmpty

/-- The number of random words of the prescribed length on which the verifier accepts. -/
def accCount (P : Prover) (x : Word) : ℕ := cntL (V.numCoins x) (V.accepts P x)

/-- **The acceptance probability**: the fraction of the random words of length `|coins(x)|` on
which the verifier accepts. -/
def accProb (P : Prover) (x : Word) : ℚ := (V.accCount P x : ℚ) / 2 ^ V.numCoins x

theorem length_round_le (P : Prover) (x r t : Word) :
    (V.round P x r t).length ≤ t.length + 2 * (2 * V.maxMsg x + 1) := by
  simp only [round, List.length_append, length_encMsg, List.length_take]
  have h1 := min_le_left (V.maxMsg x) (V.ask.eval [x, r, t]).length
  have h2 := min_le_left (V.maxMsg x)
    (P (t ++ encMsg (List.take (V.maxMsg x) (V.ask.eval [x, r, t])))).length
  omega

/-- **The transcript is polynomially long**: at most `rounds · (4 · msgLen + 2)` bits. -/
theorem length_transcript_le (P : Prover) (x r : Word) :
    (V.transcript P x r).length ≤ V.numRounds x * (2 * (2 * V.maxMsg x + 1)) := by
  unfold transcript
  generalize V.numRounds x = k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h := V.length_round_le P x r ((V.round P x r)^[k] [])
      calc _ ≤ k * (2 * (2 * V.maxMsg x + 1)) + 2 * (2 * V.maxMsg x + 1) := by omega
        _ = (k + 1) * (2 * (2 * V.maxMsg x + 1)) := by ring

theorem accProb_nonneg (P : Prover) (x : Word) : 0 ≤ V.accProb P x := by
  unfold accProb; positivity

theorem accProb_le_one (P : Prover) (x : Word) : V.accProb P x ≤ 1 := by
  unfold accProb accCount
  rw [div_le_one (by positivity)]
  exact_mod_cast (cntL_le_pow _ _).trans (by simp)

end Verifier

/-- **The class `IP`**: there is a polynomial-time verifier such that on every input in the
language some prover is accepted with probability at least `2/3`, and on every input outside it
every prover is accepted with probability at most `1/3`. -/
def IP (L : Language) : Prop :=
  ∃ V : Verifier, ∀ x : Word,
    (L x → ∃ P : Prover, (2 : ℚ) / 3 ≤ V.accProb P x) ∧
    (¬ L x → ∀ P : Prover, V.accProb P x ≤ 1 / 3)

/-! ### `IP` is closed under polynomial-time reductions -/

/-- The verifier for `x` that runs `V` on `f(x)`. -/
def Verifier.precomp (V : Verifier) (f : Cob) : Verifier where
  rounds := .comp V.rounds [f]
  coins := .comp V.coins [f]
  msgLen := .comp V.msgLen [f]
  ask := .comp V.ask [.comp f [.proj 0], .proj 1, .proj 2]
  decide := .comp V.decide [.comp f [.proj 0], .proj 1, .proj 2]

theorem Verifier.accProb_precomp (V : Verifier) (f : Cob) (P : Prover) (x : Word) :
    (V.precomp f).accProb P x = V.accProb P (f.eval [x]) := by
  have hR : (V.precomp f).numRounds x = V.numRounds (f.eval [x]) := by
    simp [Verifier.precomp, Verifier.numRounds]
  have hC : (V.precomp f).numCoins x = V.numCoins (f.eval [x]) := by
    simp [Verifier.precomp, Verifier.numCoins]
  have hM : (V.precomp f).maxMsg x = V.maxMsg (f.eval [x]) := by
    simp [Verifier.precomp, Verifier.maxMsg]
  have hround : ∀ r, (V.precomp f).round P x r = V.round P (f.eval [x]) r := by
    intro r; funext t
    simp only [Verifier.round, hM]
    simp [Verifier.precomp]
  have htr : ∀ r, (V.precomp f).transcript P x r = V.transcript P (f.eval [x]) r := by
    intro r; simp [Verifier.transcript, hR, hround]
  have hacc : (V.precomp f).accepts P x = V.accepts P (f.eval [x]) := by
    funext r
    simp only [Verifier.accepts, htr]
    simp [Verifier.precomp]
  simp [Verifier.accProb, Verifier.accCount, hC, hacc]

/-- **`IP` is closed downwards under polynomial-time many-one reductions.** -/
theorem IP.of_reduction {L₁ L₂ : Language} (hred : L₁ ≤ₘᵖ L₂) (h : IP L₂) : IP L₁ := by
  obtain ⟨f, hf⟩ := hred
  obtain ⟨V, hV⟩ := h
  refine ⟨V.precomp f, fun x => ⟨fun hx => ?_, fun hx P => ?_⟩⟩
  · obtain ⟨P, hP⟩ := (hV (f.eval [x])).1 ((hf x).1 hx)
    exact ⟨P, by rwa [Verifier.accProb_precomp]⟩
  · rw [Verifier.accProb_precomp]
    exact (hV (f.eval [x])).2 (fun h => hx ((hf x).2 h)) P

/-! ### `NP ⊆ IP` -/

/-- The one-round verifier of an `NP` language: no coins, no question; it reads the prover's
answer off the transcript and runs the `NP` verifier `v` on it. -/
def npVerifier (v : Cob) (a k : ℕ) : Verifier where
  rounds := Cob.trueC
  coins := .empty
  msgLen := Cob.nsmulT a (Cob.powT k)
  ask := .empty
  decide := .comp v [.proj 0, .comp Cob.tail [.comp Cob.dropOnes [.comp Cob.tail [.proj 2]]]]

theorem npVerifier_accepts (v : Cob) (a k : ℕ) (P : Prover) (x r : Word) :
    (npVerifier v a k).accepts P x r =
      !(v.eval [x, (P [false]).take (a * (x.length + 1) ^ k)]).isEmpty := by
  have hM : (npVerifier v a k).maxMsg x = a * (x.length + 1) ^ k := by
    simp only [Verifier.maxMsg, npVerifier]
    rw [Cob.eval_nsmulT a _ [x] _ (Cob.eval_powT k x [])]
    simp
  have hR : (npVerifier v a k).numRounds x = 1 := by
    simp [Verifier.numRounds, npVerifier]
  have htr : (npVerifier v a k).transcript P x r =
      false :: encMsg ((P [false]).take (a * (x.length + 1) ^ k)) := by
    simp only [Verifier.transcript, hR, Function.iterate_one, Verifier.round, hM]
    simp [npVerifier, encMsg]
  simp only [Verifier.accepts, htr]
  simp [npVerifier, encMsg]

/-- **`NP ⊆ IP`**: the prover sends a witness, the verifier checks it; no randomness is used. -/
theorem inIP_of_inNP {L : Language} (h : InNP L) : IP L := by
  obtain ⟨v, p, ⟨a, k, hp⟩, _, hlen, hL⟩ := h
  refine ⟨npVerifier v a k, fun x => ⟨fun hx => ?_, fun hx P => ?_⟩⟩
  · obtain ⟨w, hw⟩ := (hL x).1 hx
    refine ⟨fun _ => w, ?_⟩
    have hwl : w.length ≤ a * (x.length + 1) ^ k := (hlen x w hw).trans (hp _)
    have hacc : ∀ r, (npVerifier v a k).accepts (fun _ => w) x r = true := by
      intro r
      rw [npVerifier_accepts, List.take_of_length_le hwl]
      simpa using hw
    have : (npVerifier v a k).accCount (fun _ => w) x = 2 ^ (npVerifier v a k).numCoins x := by
      rw [Verifier.accCount, cntL_true _ (fun r _ => hacc r)]
      simp
    rw [Verifier.accProb, this]
    norm_num
  · have hacc : ∀ r, (npVerifier v a k).accepts P x r = false := by
      intro r
      rw [npVerifier_accepts]
      have : v.eval [x, (P [false]).take (a * (x.length + 1) ^ k)] = [] := by
        by_contra hne
        exact hx ((hL x).2 ⟨_, hne⟩)
      simp [this]
    rw [Verifier.accProb, Verifier.accCount, cntL_false _ (fun r _ => hacc r)]
    norm_num

end Complexity
