/-
**The value of an interactive proof: the best prover, by a recursion over transcripts.**

For a verifier `V` and an input `x`, the largest number of coin words on which some prover is
accepted is computed by a recursion over partial transcripts (`Complexity.IPValue.F`): with `k`
rounds still to play after the transcript `t`, it is the sum over the verifier's possible next
messages `q` of the maximum over the prover's possible answers `a` of the value after
`t · q · a`; with no round left, it is the number of coin words `r` that are *consistent* with
`t` (the verifier with coins `r`, fed the answers recorded in `t`, produces exactly `t`) and on
which the verifier accepts `t`.  Messages range over all words of length at most the message
bound (`Complexity.IPValue.wsL`); sums and maxima over them are written as recursions that
extend a word one bit at a time (`Complexity.IPValue.sumW`, `Complexity.IPValue.supW`), which is
the shape the polynomial-space evaluation of `Start/IPSpace.lean` follows.

Main results:

* `Complexity.IPValue.accCount_le_F` — **no prover does better than the recursion**;
* `Complexity.IPValue.exists_F_le_accCount` — **some prover achieves it** (it answers each
  question by a maximizing answer).
-/

import Start.InteractiveProof
import Start.ShamirWords

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.IPValue

open Complexity.Shamir

/-! ### Words of bounded length, sums and maxima over them -/

/-- All words of length at most `d`. -/
def wsL : ℕ → List Word
  | 0 => [[]]
  | d + 1 => [] :: ((wsL d).map (· ++ [false]) ++ (wsL d).map (· ++ [true]))

theorem mem_wsL : ∀ (d : ℕ) (w : Word), w ∈ wsL d ↔ w.length ≤ d
  | 0, w => by simp [wsL]
  | d + 1, w => by
      simp only [wsL, List.mem_cons, List.mem_append, List.mem_map, mem_wsL d]
      constructor
      · rintro (rfl | ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;> simp <;> omega
      · intro h
        rcases List.eq_nil_or_concat w with rfl | ⟨L, b, rfl⟩
        · exact Or.inl rfl
        · right
          simp at h
          cases b
          · exact Or.inl ⟨L, by omega, List.concat_eq_append.symm⟩
          · exact Or.inr ⟨L, by omega, List.concat_eq_append.symm⟩

theorem nodup_wsL : ∀ d : ℕ, (wsL d).Nodup
  | 0 => by simp [wsL]
  | d + 1 => by
      have ih := nodup_wsL d
      simp only [wsL, List.nodup_cons, List.mem_append, List.mem_map]
      refine ⟨?_, ?_⟩
      · rintro (⟨u, -, hu⟩ | ⟨u, -, hu⟩) <;> simp at hu
      · refine List.Nodup.append (ih.map (fun a b h => by simpa using h))
          (ih.map (fun a b h => by simpa using h)) ?_
        intro w hw1 hw2
        simp only [List.mem_map] at hw1 hw2
        obtain ⟨u, -, rfl⟩ := hw1
        obtain ⟨v, -, hv⟩ := hw2
        have := congrArg List.getLast? hv
        simp at this

/-- The sum of `f (u ++ q)` over the words `u` of length at most `d`, extending `q` one bit at a
time at the front. -/
def sumW : ℕ → (Word → ℕ) → Word → ℕ
  | 0, f, q => f q
  | d + 1, f, q => f q + (sumW d f (false :: q) + sumW d f (true :: q))

/-- The maximum of `f (u ++ q)` over the words `u` of length at most `d`. -/
def supW : ℕ → (Word → ℕ) → Word → ℕ
  | 0, f, q => f q
  | d + 1, f, q => max (f q) (max (supW d f (false :: q)) (supW d f (true :: q)))

theorem sumW_eq (f : Word → ℕ) : ∀ (d : ℕ) (q : Word),
    sumW d f q = ((wsL d).map (fun u => f (u ++ q))).sum
  | 0, q => by simp [sumW, wsL]
  | d + 1, q => by
      simp only [sumW, wsL, List.map_cons, List.sum_cons, List.map_append, List.map_map,
        List.sum_append, sumW_eq f d]
      simp [Function.comp_def]

theorem le_supW (f : Word → ℕ) : ∀ (d : ℕ) (q u : Word), u ∈ wsL d → f (u ++ q) ≤ supW d f q
  | 0, q, u, hu => by simp [wsL] at hu; subst hu; simp [supW]
  | d + 1, q, u, hu => by
      simp only [wsL, List.mem_cons, List.mem_append, List.mem_map] at hu
      simp only [supW]
      rcases hu with rfl | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · simp
      · have := le_supW f d (false :: q) v hv
        simp only [List.append_assoc, List.singleton_append] at this ⊢
        omega
      · have := le_supW f d (true :: q) v hv
        simp only [List.append_assoc, List.singleton_append] at this ⊢
        omega

theorem supW_attained (f : Word → ℕ) : ∀ (d : ℕ) (q : Word),
    ∃ u ∈ wsL d, supW d f q = f (u ++ q)
  | 0, q => ⟨[], by simp [wsL], by simp [supW]⟩
  | d + 1, q => by
      obtain ⟨u0, hu0, e0⟩ := supW_attained f d (false :: q)
      obtain ⟨u1, hu1, e1⟩ := supW_attained f d (true :: q)
      simp only [supW]
      by_cases h1 : max (supW d f (false :: q)) (supW d f (true :: q)) ≤ f q
      · exact ⟨[], by simp [wsL], by simp [max_eq_left h1]⟩
      · rw [max_eq_right (by omega)]
        by_cases h2 : supW d f (true :: q) ≤ supW d f (false :: q)
        · refine ⟨u0 ++ [false], ?_, by rw [max_eq_left h2, e0]; simp⟩
          simp only [wsL, List.mem_cons, List.mem_append, List.mem_map]
          exact Or.inr (Or.inl ⟨u0, hu0, rfl⟩)
        · refine ⟨u1 ++ [true], ?_, by rw [max_eq_right (by omega), e1]; simp⟩
          simp only [wsL, List.mem_cons, List.mem_append, List.mem_map]
          exact Or.inr (Or.inr ⟨u1, hu1, rfl⟩)

/-! ### Splitting a count by a function with values in a list -/

theorem sum_ite_eq_one {a : Word} : ∀ {Q : List Word}, Q.Nodup → a ∈ Q →
    (Q.map (fun q => if a = q then 1 else 0)).sum = 1
  | [], _, h => by simp at h
  | q :: Q, hnd, h => by
      rw [List.nodup_cons] at hnd
      simp only [List.map_cons, List.sum_cons]
      by_cases haq : a = q
      · subst haq
        have : (Q.map (fun q => if a = q then 1 else 0)).sum = 0 := by
          rw [List.sum_eq_zero_iff]
          intro n hn
          simp only [List.mem_map] at hn
          obtain ⟨q', hq', rfl⟩ := hn
          have : a ≠ q' := fun h => hnd.1 (h ▸ hq')
          simp [this]
        simp [this]
      · rcases List.mem_cons.1 h with h | h
        · exact absurd h haq
        · simp [haq, sum_ite_eq_one hnd.2 h]

theorem sumL_listSum {α : Type*} [Fintype α] (n : ℕ) (f : Word → List α → ℕ) :
    ∀ Q : List Word,
      sumL n (fun ρ => (Q.map (fun q => f q ρ)).sum) = (Q.map (fun q => sumL n (f q))).sum
  | [] => by simp [sumL_const]
  | q :: Q => by
      simp only [List.map_cons, List.sum_cons]
      rw [sumL_add, sumL_listSum n f Q]

/-- **Splitting a count** by a function `g` whose values lie in a list without repetitions. -/
theorem cntL_split (n : ℕ) (E : List Bool → Bool) (g : List Bool → Word) (Q : List Word)
    (hQ : Q.Nodup) (hg : ∀ r, g r ∈ Q) :
    cntL n E = (Q.map (fun q => cntL n (fun r => E r && decide (g r = q)))).sum := by
  unfold cntL
  rw [← sumL_listSum]
  congr 1
  funext r
  by_cases hE : E r
  · simp only [hE, if_true, Bool.true_and, decide_eq_true_eq]
    exact (sum_ite_eq_one hQ (hg r)).symm
  · simp [hE]

/-! ### Transcripts as lists of messages -/

/-- The word of a list of messages, each recorded by `encMsg`. -/
def encs (l : List Word) : Word := (l.map encMsg).flatten

@[simp] theorem encs_nil : encs [] = [] := rfl

@[simp] theorem encs_cons (w : Word) (l : List Word) : encs (w :: l) = encMsg w ++ encs l := by
  simp [encs]

theorem encs_append (l m : List Word) : encs (l ++ m) = encs l ++ encs m := by
  simp [encs]

theorem encMsg_ne_nil' (w : Word) : encMsg w ≠ [] := by simp [encMsg]

/-- Records form a prefix code. -/
theorem encs_prefix : ∀ (m l : List Word) (X : Word), encs m ++ X = encs l →
    m = l.take m.length ∧ X = encs (l.drop m.length)
  | [], l, X, h => by simpa using h
  | w :: m, [], X, h => by simp [encMsg] at h
  | w :: m, v :: l, X, h => by
      simp only [encs_cons, List.append_assoc] at h
      have hw : w = v := by
        have := congrArg recGet h
        simpa using this
      subst hw
      have hrest : encs m ++ X = encs l := by
        have := congrArg recSkip h
        simpa using this
      obtain ⟨h1, h2⟩ := encs_prefix m l X hrest
      exact ⟨by simp [← h1], by simpa using h2⟩

theorem encs_inj {l m : List Word} (h : encs l = encs m) : l = m := by
  have := encs_prefix l m [] (by simpa using h)
  have hlen : l.length = m.length := by
    have h2 := this.2
    rcases Nat.lt_or_ge l.length m.length with hl | hl
    · exfalso
      have : m.drop l.length ≠ [] := by simp; omega
      obtain ⟨w, ws, hw⟩ := List.exists_cons_of_ne_nil this
      rw [hw] at h2; simp [encMsg] at h2
    · have := congrArg List.length this.1
      simp at this; omega
  rw [this.1, hlen, List.take_length]

/-- Parsing a word into its records (with fuel). -/
def decAux : ℕ → Word → List Word
  | 0, _ => []
  | n + 1, s => if s = [] then [] else recGet s :: decAux n (recSkip s)

/-- Parsing a word into its records. -/
def dec (s : Word) : List Word := decAux s.length s

theorem decAux_encs : ∀ (l : List Word) (n : ℕ), l.length ≤ n → decAux n (encs l) = l
  | [], n, _ => by cases n <;> simp [decAux]
  | w :: l, n, h => by
      obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
      simp only [decAux, encs_cons]
      rw [if_neg (by simp [encMsg]), recGet_encMsg, recSkip_encMsg,
        decAux_encs l n (by simp at h; omega)]

theorem length_le_length_encs : ∀ l : List Word, l.length ≤ (encs l).length
  | [] => by simp
  | w :: l => by
      have := length_le_length_encs l
      simp [encs_cons, length_encMsg]; omega

theorem dec_encs (l : List Word) : dec (encs l) = l :=
  decAux_encs l _ (length_le_length_encs l)

theorem exists_split_two {l : List Word} {j : ℕ} (h : l.length = 2 * j + 2) :
    ∃ m q a, l = m ++ [q, a] ∧ m.length = 2 * j := by
  refine ⟨l.take (2 * j), (l.drop (2 * j)).getD 0 [], (l.drop (2 * j)).getD 1 [], ?_, by simp; omega⟩
  have hd : (l.drop (2 * j)).length = 2 := by simp; omega
  obtain ⟨q, a, hqa⟩ := List.length_eq_two.1 hd
  conv_lhs => rw [← List.take_append_drop (2 * j) l]
  rw [hqa]; rfl

/-! ### The protocol -/

section Protocol

variable (V : Verifier) (x : Word)

/-- The prover that reads its answers off the transcript `t`. -/
def rd (t : Word) : Prover := fun s => recGet (t.drop s.length)

/-- A coin word `r` is consistent with `t` and the verifier accepts. -/
def leafOK (t r : Word) : Bool :=
  decide (V.transcript (rd t) x r = t) && !(V.decide.eval [x, r, t]).isEmpty

/-- **The value of the game** after the transcript `t`, with `k` rounds still to play. -/
def F : ℕ → Word → ℕ
  | 0, t => cntL (V.numCoins x) (leafOK V x t)
  | k + 1, t => sumW (V.maxMsg x)
      (fun q => supW (V.maxMsg x) (fun a => F k (t ++ encMsg q ++ encMsg a)) []) []

/-- The transcript after `j` rounds. -/
def tr (P : Prover) (r : Word) (j : ℕ) : Word := (V.round P x r)^[j] []

/-- The verifier's question after the transcript `t`. -/
def qOf (r t : Word) : Word := (V.ask.eval [x, r, t]).take (V.maxMsg x)

theorem tr_succ (P : Prover) (r : Word) (j : ℕ) :
    tr V x P r (j + 1) = tr V x P r j ++ encMsg (qOf V x r (tr V x P r j)) ++
      encMsg ((P (tr V x P r j ++ encMsg (qOf V x r (tr V x P r j)))).take (V.maxMsg x)) := by
  rw [tr, Function.iterate_succ_apply']; rfl

theorem exists_tr_eq (P : Prover) (r : Word) : ∀ j, ∃ m : List Word,
    m.length = 2 * j ∧ tr V x P r j = encs m
  | 0 => ⟨[], rfl, rfl⟩
  | j + 1 => by
      obtain ⟨m, hm, e⟩ := exists_tr_eq P r j
      refine ⟨m ++ [qOf V x r (encs m), (P (encs m ++ encMsg (qOf V x r (encs m)))).take
        (V.maxMsg x)], by simp; omega, ?_⟩
      rw [tr_succ, e, encs_append]; simp [List.append_assoc]

/-- The questions recorded in a list of messages are those of the coins `r`. -/
inductive QOK (r : Word) : List Word → Prop
  | nil : QOK r []
  | snoc {m : List Word} {q : Word} (a : Word) : QOK r m → q = qOf V x r (encs m) →
      QOK r (m ++ [q, a])

/-- The answers recorded in a list of messages are those of the prover `P`. -/
inductive AOK (P : Prover) : List Word → Prop
  | nil : AOK P []
  | snoc {m : List Word} {a : Word} (q : Word) : AOK P m →
      a = (P (encs m ++ encMsg q)).take (V.maxMsg x) → AOK P (m ++ [q, a])

theorem append_two_inj {m m' : List Word} {q a q' a' : Word}
    (h : m ++ [q, a] = m' ++ [q', a']) : m = m' ∧ q = q' ∧ a = a' := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  simp at h2
  exact ⟨h1, h2⟩

theorem QOK.snoc_iff {r : Word} {m : List Word} {q a : Word} :
    QOK V x r (m ++ [q, a]) ↔ QOK V x r m ∧ q = qOf V x r (encs m) := by
  constructor
  · intro h
    generalize hl : m ++ [q, a] = l at h
    cases h with
    | nil => simp at hl
    | snoc a' h hq =>
        obtain ⟨rfl, rfl, -⟩ := append_two_inj hl
        exact ⟨h, hq⟩
  · rintro ⟨h, hq⟩; exact QOK.snoc a h hq

theorem AOK.snoc_iff {P : Prover} {m : List Word} {q a : Word} :
    AOK V x P (m ++ [q, a]) ↔ AOK V x P m ∧ a = (P (encs m ++ encMsg q)).take (V.maxMsg x) := by
  constructor
  · intro h
    generalize hl : m ++ [q, a] = l at h
    cases h with
    | nil => simp at hl
    | snoc q' h ha =>
        obtain ⟨rfl, rfl, rfl⟩ := append_two_inj hl
        exact ⟨h, ha⟩
  · rintro ⟨h, ha⟩; exact AOK.snoc q h ha

/-- **Transcripts as lists of messages**: the transcript after `j` rounds is `encs l` iff the
questions in `l` are those of the coins and the answers those of the prover. -/
theorem tr_eq_encs_iff (P : Prover) (r : Word) : ∀ (j : ℕ) (l : List Word), l.length = 2 * j →
    (tr V x P r j = encs l ↔ QOK V x r l ∧ AOK V x P l)
  | 0, l, hl => by
      obtain rfl : l = [] := List.length_eq_zero_iff.1 (by simpa using hl)
      exact ⟨fun _ => ⟨QOK.nil, AOK.nil⟩, fun _ => rfl⟩
  | j + 1, l, hl => by
      obtain ⟨m, q, a, rfl, hm⟩ := exists_split_two (show l.length = 2 * j + 2 by omega)
      rw [QOK.snoc_iff, AOK.snoc_iff, tr_succ]
      have hencs : encs (m ++ [q, a]) = encs m ++ encMsg q ++ encMsg a := by
        rw [encs_append]; simp [List.append_assoc]
      rw [hencs]
      constructor
      · intro h
        obtain ⟨m', hm', e'⟩ := exists_tr_eq V x P r j
        rw [e'] at h
        have h2 : encs (m' ++ [qOf V x r (encs m'), (P (encs m' ++
            encMsg (qOf V x r (encs m')))).take (V.maxMsg x)]) = encs (m ++ [q, a]) := by
          rw [hencs, encs_append]; simpa [List.append_assoc] using h
        obtain ⟨rfl, hq, ha⟩ := append_two_inj (encs_inj h2)
        have := (tr_eq_encs_iff P r j m' hm').1 e'
        exact ⟨⟨this.1, hq.symm⟩, ⟨this.2, by rw [← ha, hq]⟩⟩
      · rintro ⟨⟨h1, hq⟩, ⟨h2, ha⟩⟩
        have e := (tr_eq_encs_iff P r j m hm).2 ⟨h1, h2⟩
        rw [e, ← hq, ← ha]

/-- The prover reading its answers off a transcript produces the answers recorded there. -/
theorem AOK.rd {P : Prover} : ∀ {l : List Word}, AOK V x P l → ∀ rest : List Word,
    AOK V x (rd (encs (l ++ rest))) l
  | _, AOK.nil, _ => AOK.nil
  | _, @AOK.snoc _ _ _ m a q hA ha, rest => by
      refine AOK.snoc q ?_ ?_
      · have := AOK.rd hA ([q, a] ++ rest)
        simpa [List.append_assoc] using this
      · have hlen : a.length ≤ V.maxMsg x := by rw [ha]; simp
        have hd : (encs (m ++ [q, a] ++ rest)).drop (encs m ++ encMsg q).length =
            encMsg a ++ encs rest := by
          rw [encs_append, encs_append]
          simp [List.append_assoc]
        simp only [Complexity.IPValue.rd, hd, recGet_encMsg]
        rw [List.take_of_length_le hlen]

/-- The number of coin words whose run with `P` passes through `t` after `j` rounds and is
accepted. -/
def G (P : Prover) (j : ℕ) (t : Word) : ℕ :=
  cntL (V.numCoins x) (fun r => decide (tr V x P r j = t) && V.accepts P x r)

theorem accCount_eq_G (P : Prover) : V.accCount P x = G V x P 0 [] := by
  simp [G, Verifier.accCount, tr]

/-- **The count splits over the next question.** -/
theorem G_split (P : Prover) (j : ℕ) (l : List Word) (hl : l.length = 2 * j) :
    G V x P j (encs l) = ((wsL (V.maxMsg x)).map (fun q => G V x P (j + 1)
      (encs l ++ encMsg q ++ encMsg ((P (encs l ++ encMsg q)).take (V.maxMsg x))))).sum := by
  rw [G, cntL_split _ _ (fun r => qOf V x r (tr V x P r j)) (wsL (V.maxMsg x))
    (nodup_wsL _) (fun r => by rw [mem_wsL]; simp [qOf])]
  congr 1
  apply List.map_congr_left
  intro q _
  rw [G]
  congr 1
  funext r
  have key : (tr V x P r j = encs l ∧ qOf V x r (tr V x P r j) = q) ↔
      tr V x P r (j + 1) =
        encs l ++ encMsg q ++ encMsg ((P (encs l ++ encMsg q)).take (V.maxMsg x)) := by
    rw [tr_succ]
    constructor
    · rintro ⟨h1, h2⟩; rw [h2, h1]
    · intro h
      obtain ⟨m, hm, e⟩ := exists_tr_eq V x P r j
      rw [e] at h ⊢
      have h2 : encs (m ++ [qOf V x r (encs m), (P (encs m ++
          encMsg (qOf V x r (encs m)))).take (V.maxMsg x)]) =
          encs (l ++ [q, (P (encs l ++ encMsg q)).take (V.maxMsg x)]) := by
        rw [encs_append, encs_append]; simpa [List.append_assoc] using h
      obtain ⟨rfl, hq, -⟩ := append_two_inj (encs_inj h2)
      exact ⟨rfl, hq⟩
  by_cases hacc : V.accepts P x r
  · simp only [hacc, Bool.and_true, Bool.decide_and, ← key]
  · simp [hacc]

theorem transcript_eq_tr (P : Prover) (r : Word) :
    V.transcript P x r = tr V x P r (V.numRounds x) := rfl

/-- **No prover beats the recursion** below a transcript. -/
theorem G_le_F (P : Prover) : ∀ (k j : ℕ) (l : List Word), j + k = V.numRounds x →
    l.length = 2 * j → G V x P j (encs l) ≤ F V x k (encs l)
  | 0, j, l, hjk, hl => by
      simp only [Nat.add_zero] at hjk
      subst hjk
      rw [G, F]
      apply cntL_mono
      intro r hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨htr, hacc⟩ := hr
      obtain ⟨hQ, hA⟩ := (tr_eq_encs_iff V x P r _ l hl).1 htr
      have hrd : tr V x (rd (encs l)) r (V.numRounds x) = encs l :=
        (tr_eq_encs_iff V x _ r _ l hl).2 ⟨hQ, by simpa using hA.rd V x []⟩
      simp only [leafOK, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hrd, ?_⟩
      simpa [Verifier.accepts, transcript_eq_tr, htr] using hacc
  | k + 1, j, l, hjk, hl => by
      rw [G_split V x P j l hl, F, sumW_eq]
      apply List.sum_le_sum
      intro q _
      simp only [List.append_nil]
      set a := (P (encs l ++ encMsg q)).take (V.maxMsg x) with ha
      have h1 := G_le_F P k (j + 1) (l ++ [q, a]) (by omega) (by simp; omega)
      have he : encs (l ++ [q, a]) = encs l ++ encMsg q ++ encMsg a := by
        rw [encs_append]; simp [List.append_assoc]
      rw [he] at h1
      refine h1.trans ?_
      have := le_supW (fun a => F V x k (encs l ++ encMsg q ++ encMsg a)) (V.maxMsg x) [] a
        (by rw [mem_wsL, ha]; simp)
      simpa using this

/-- **No prover is accepted on more coin words than the value of the game.** -/
theorem accCount_le_F (P : Prover) : V.accCount P x ≤ F V x (V.numRounds x) [] := by
  rw [accCount_eq_G]
  exact G_le_F V x P (V.numRounds x) 0 [] (by simp) rfl

/-! ### The best prover -/

/-- A best answer to the question `q` after `t`, with `k` rounds to play after it. -/
noncomputable def best (k : ℕ) (t q : Word) : Word :=
  Classical.choose (supW_attained (fun a => F V x k (t ++ encMsg q ++ encMsg a)) (V.maxMsg x) [])

theorem best_mem (k : ℕ) (t q : Word) : best V x k t q ∈ wsL (V.maxMsg x) :=
  (Classical.choose_spec
    (supW_attained (fun a => F V x k (t ++ encMsg q ++ encMsg a)) (V.maxMsg x) [])).1

theorem best_spec (k : ℕ) (t q : Word) :
    supW (V.maxMsg x) (fun a => F V x k (t ++ encMsg q ++ encMsg a)) [] =
      F V x k (t ++ encMsg q ++ encMsg (best V x k t q)) := by
  have := (Classical.choose_spec
    (supW_attained (fun a => F V x k (t ++ encMsg q ++ encMsg a)) (V.maxMsg x) [])).2
  rw [best]; simpa using this

/-- **The best prover**: it parses the transcript and answers by a maximizing answer. -/
noncomputable def pBest (s : Word) : Word :=
  best V x (V.numRounds x - (dec s).length / 2 - 1) (encs (dec s).dropLast) ((dec s).getLastD [])

theorem pBest_eq (m : List Word) (j : ℕ) (hm : m.length = 2 * j) (q : Word) :
    pBest V x (encs m ++ encMsg q) = best V x (V.numRounds x - j - 1) (encs m) q := by
  have : encs m ++ encMsg q = encs (m ++ [q]) := by rw [encs_append]; simp
  rw [pBest, this, dec_encs]
  simp only [List.length_append, List.length_singleton, hm, List.dropLast_concat,
    List.getLastD_concat]
  congr 2
  omega

/-- **The best prover achieves the recursion** below a transcript whose answers are its own. -/
theorem F_le_G : ∀ (k j : ℕ) (l : List Word), j + k = V.numRounds x →
    l.length = 2 * j → AOK V x (pBest V x) l → F V x k (encs l) ≤ G V x (pBest V x) j (encs l)
  | 0, j, l, hjk, hl, hA => by
      simp only [Nat.add_zero] at hjk
      subst hjk
      rw [G, F]
      apply cntL_mono
      intro r hr
      simp only [leafOK, Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨hrd, hacc⟩ := hr
      obtain ⟨hQ, -⟩ := (tr_eq_encs_iff V x _ r _ l hl).1 hrd
      have htr : tr V x (pBest V x) r (V.numRounds x) = encs l :=
        (tr_eq_encs_iff V x _ r _ l hl).2 ⟨hQ, hA⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨htr, ?_⟩
      simpa [Verifier.accepts, transcript_eq_tr, htr] using hacc
  | k + 1, j, l, hjk, hl, hA => by
      rw [G_split V x _ j l hl, F, sumW_eq]
      apply List.sum_le_sum
      intro q _
      simp only [List.append_nil]
      have hb : (pBest V x (encs l ++ encMsg q)).take (V.maxMsg x) = best V x k (encs l) q := by
        rw [pBest_eq V x l j hl, show V.numRounds x - j - 1 = k by omega]
        exact List.take_of_length_le ((mem_wsL _ _).1 (best_mem V x k _ q))
      rw [hb, best_spec]
      have h1 := F_le_G k (j + 1) (l ++ [q, best V x k (encs l) q]) (by omega) (by simp; omega)
        (AOK.snoc q hA hb.symm)
      have he : encs (l ++ [q, best V x k (encs l) q]) =
          encs l ++ encMsg q ++ encMsg (best V x k (encs l) q) := by
        rw [encs_append]; simp [List.append_assoc]
      rwa [he] at h1

/-- **Some prover achieves the value of the game.** -/
theorem exists_F_le_accCount : ∃ P : Prover, F V x (V.numRounds x) [] ≤ V.accCount P x := by
  refine ⟨pBest V x, ?_⟩
  rw [accCount_eq_G]
  exact F_le_G V x (V.numRounds x) 0 [] (by simp) rfl AOK.nil

end Protocol

end Complexity.IPValue
