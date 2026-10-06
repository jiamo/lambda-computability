/-
**The sum-check protocol over a finite field, as a game: perfect completeness and soundness.**

This is the interactive heart of Shamir's theorem, stated for an arbitrary operator expression of
`Start/QbfLinearize.lean` over a finite field `F`.  A *claim* is a node `t` of the expression, a
point `a : ℕ → F` and a value `v`, asserting `t.eval a = v`.  The verifier reduces a claim at a
node to claims at its children:

* at a variable it checks `a i = v` itself;
* at a negation the claim `1 - f = v` becomes `f = 1 - v`;
* at a conjunction or disjunction the prover sends the two values `[b, c]` of the children; the
  verifier checks that they combine to `v`, draws a random point (which it does not use: every
  message is followed by a point, so that the protocol alternates strictly) and recurses on both;
* at a quantifier `∀ x_i`, `∃ x_i` or a linearization `L_i` — a **round** — the prover sends the
  coefficient list of a polynomial `h` of degree at most `d`, meant to be the restriction of the
  child to the line through `a` in direction `i`; the verifier checks that `h` combines to `v`
  (`h(0) h(1)`, `1 - (1 - h(0))(1 - h(1))`, `a_i h(1) + (1 - a_i) h(0)` respectively), draws a
  random point `s` and continues with the claim `h(s)` at the point `a[i := s]`.

The prover is an arbitrary strategy (`Complexity.Qbf.Strat`): its message may depend on the whole
history of the interaction (and, for convenience, on the current node and point, which are
determined by the history).  The random points form a list of length `t.rounds`, and probabilities
are counted over all such lists (`Complexity.cntL`).

Main definitions:

* `Complexity.Qbf.evalL`, `Complexity.Qbf.toPoly` — a coefficient list as a function and as a
  polynomial;
* `Complexity.Qbf.run` — one run of the protocol on a claim, given the prover and the random
  points; it returns the verdict and the extended history;
* `Complexity.Qbf.scProb` — the acceptance probability;
* `Complexity.Qbf.honest` — the honest prover.

Main results:

* `Complexity.Qbf.run_honest` — **completeness**: on a true claim the honest prover is accepted on
  every choice of the random points, when the degree bound `d` is respected
  (`Complexity.Qbf.Op.RoundDeg`);
* `Complexity.Qbf.cntL_run_false` — **soundness**: on a false claim every prover is accepted on at
  most a `d · rounds / |F|` fraction of the random points, by induction on the expression with the
  one-round estimate `Polynomial.card_eval_eq_le`;
* `Complexity.Qbf.scProb_honest`, `Complexity.Qbf.scProb_le` — the same as probabilities.
-/

import Start.QbfLinearize
import Start.CountProb

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Polynomial

namespace Complexity.Qbf

/-! ### Coefficient lists -/

section Coeffs

variable {R : Type*} [CommRing R]

/-- A coefficient list `[c₀, c₁, …]` evaluated at `x` by Horner's rule. -/
def evalL : List R → R → R
  | [], _ => 0
  | c :: cs, x => c + x * evalL cs x

/-- A coefficient list as a polynomial. -/
noncomputable def toPoly : List R → R[X]
  | [] => 0
  | c :: cs => C c + X * toPoly cs

theorem eval_toPoly (l : List R) (x : R) : (toPoly l).eval x = evalL l x := by
  induction l with
  | nil => simp [toPoly, evalL]
  | cons c cs ih => simp [toPoly, evalL, ih]

theorem natDegree_toPoly (l : List R) : (toPoly l).natDegree ≤ l.length - 1 := by
  induction l with
  | nil => simp [toPoly]
  | cons c cs ih =>
      cases cs with
      | nil => simp [toPoly]
      | cons c' cs' =>
          simp only [toPoly] at ih ⊢
          refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
          refine natDegree_mul_le.trans ?_
          have := natDegree_X_le (R := R)
          simp only [List.length_cons] at ih ⊢
          omega

/-- The first `n` coefficients of a polynomial. -/
noncomputable def coeffs : R[X] → ℕ → List R
  | _, 0 => []
  | q, n + 1 => q.coeff 0 :: coeffs q.divX n

@[simp] theorem length_coeffs (q : R[X]) (n : ℕ) : (coeffs q n).length = n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [coeffs, ih]

theorem toPoly_coeffs : ∀ (n : ℕ) (q : R[X]), q.natDegree < n ∨ q = 0 → toPoly (coeffs q n) = q
  | 0, q, h => by
      rcases h with h | h
      · omega
      · simp [coeffs, toPoly, h]
  | n + 1, q, h => by
      have hdiv : q.divX.natDegree < n ∨ q.divX = 0 := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · right
          subst hn
          rcases h with h | h
          · rw [divX_eq_zero_iff]; exact eq_C_of_natDegree_eq_zero (by omega)
          · simp [h]
        · left
          rw [natDegree_divX_eq_natDegree_tsub_one]
          rcases h with h | h
          · omega
          · simp [h]; omega
      rw [coeffs, toPoly, toPoly_coeffs n q.divX hdiv, add_comm]
      exact X_mul_divX_add q

theorem evalL_coeffs {q : R[X]} {d : ℕ} (hq : q.natDegree ≤ d) (x : R) :
    evalL (coeffs q (d + 1)) x = q.eval x := by
  rw [← eval_toPoly, toPoly_coeffs _ _ (Or.inl (by omega))]

end Coeffs

/-! ### The protocol -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A prover strategy: from the history of the interaction (the messages and random points so
far), the current node and the current point, the next message. -/
abbrev Strat (F : Type*) := List (List F) → Op → (ℕ → F) → List F

/-- **One run of the protocol** with degree bound `d`, prover `P`, on the claim `t.eval a = v`,
with history `hist` and random points `ρ`: the verdict and the extended history. -/
def run (d : ℕ) (P : Strat F) : Op → (ℕ → F) → F → List (List F) → List F → Bool × List (List F)
  | .var i, a, v, hist, _ => (decide (a i = v), hist)
  | .neg p, a, v, hist, ρ => run d P p a (1 - v) hist ρ
  | .conj p q, a, v, hist, ρ =>
      match P hist (.conj p q) a with
      | [b, c] =>
          if b * c = v then
            let r₁ := run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)
            let r₂ := run d P q a c r₁.2 (ρ.tail.drop p.rounds)
            (r₁.1 && r₂.1, r₂.2)
          else (false, hist)
      | _ => (false, hist)
  | .disj p q, a, v, hist, ρ =>
      match P hist (.disj p q) a with
      | [b, c] =>
          if 1 - (1 - b) * (1 - c) = v then
            let r₁ := run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)
            let r₂ := run d P q a c r₁.2 (ρ.tail.drop p.rounds)
            (r₁.1 && r₂.1, r₂.2)
          else (false, hist)
      | _ => (false, hist)
  | .all i p, a, v, hist, ρ =>
      let m := P hist (.all i p) a
      if m.length ≤ d + 1 ∧ evalL m 0 * evalL m 1 = v then
        run d P p (Function.update a i (ρ.headD 0)) (evalL m (ρ.headD 0))
          (hist ++ [m, [ρ.headD 0]]) ρ.tail
      else (false, hist)
  | .ex i p, a, v, hist, ρ =>
      let m := P hist (.ex i p) a
      if m.length ≤ d + 1 ∧ 1 - (1 - evalL m 0) * (1 - evalL m 1) = v then
        run d P p (Function.update a i (ρ.headD 0)) (evalL m (ρ.headD 0))
          (hist ++ [m, [ρ.headD 0]]) ρ.tail
      else (false, hist)
  | .lin j p, a, v, hist, ρ =>
      let m := P hist (.lin j p) a
      if m.length ≤ d + 1 ∧ a j * evalL m 1 + (1 - a j) * evalL m 0 = v then
        run d P p (Function.update a j (ρ.headD 0)) (evalL m (ρ.headD 0))
          (hist ++ [m, [ρ.headD 0]]) ρ.tail
      else (false, hist)

/-- **The acceptance probability** of the protocol on the claim `t.eval a = v`: the fraction of
the lists of `t.rounds` random points on which the verifier accepts. -/
noncomputable def scProb (d : ℕ) (P : Strat F) (t : Op) (a : ℕ → F) (v : F) : ℚ :=
  (cntL t.rounds (fun ρ => (run d P t a v [] ρ).1) : ℚ) / (Fintype.card F : ℚ) ^ t.rounds

open Classical in
/-- **The honest prover**: it sends the true values of the children at a conjunction or a
disjunction, and the first `d + 1` coefficients of the true restriction at a round. -/
noncomputable def honest (d : ℕ) : Strat F := fun _ t a =>
  match t with
  | .conj p q => [p.eval a, q.eval a]
  | .disj p q => [p.eval a, q.eval a]
  | .all i p | .ex i p | .lin i p =>
      if h : ∃ g : F[X], g.natDegree ≤ d ∧ ∀ x, g.eval x = p.eval (Function.update a i x) then
        coeffs (Classical.choose h) (d + 1)
      else []
  | _ => []

omit [Fintype F] [DecidableEq F] in
theorem honest_round {d : ℕ} {p : Op} {i : ℕ} {a : ℕ → F}
    (hdeg : UniDeg (fun b : ℕ → F => p.eval b) i d) (t : Op)
    (ht : t = .all i p ∨ t = .ex i p ∨ t = .lin i p) (hist : List (List F)) :
    (honest d hist t a).length = d + 1 ∧
      ∀ x, evalL (honest d hist t a) x = p.eval (Function.update a i x) := by
  have hex := hdeg a
  have key : (honest d hist t a) = coeffs (Classical.choose hex) (d + 1) := by
    rcases ht with rfl | rfl | rfl <;> simp [honest, hex]
  rw [key]
  refine ⟨by simp, fun x => ?_⟩
  rw [evalL_coeffs (Classical.choose_spec hex).1, (Classical.choose_spec hex).2]

omit [Fintype F] in
/-- **Completeness**: on a true claim, and when every round respects the degree bound, the honest
prover is accepted whatever the random points. -/
theorem run_honest (d : ℕ) :
    ∀ (t : Op), Op.RoundDeg F d t → ∀ (a : ℕ → F) (v : F) (hist : List (List F)) (ρ : List F),
      v = t.eval a → (run d (honest d) t a v hist ρ).1 = true := by
  intro t
  induction t with
  | var i => intro _ a v hist ρ hv; simp [run, Op.eval, hv]
  | neg p ih =>
      intro hd a v hist ρ hv
      exact ih hd a _ hist ρ (by rw [hv, Op.eval]; ring)
  | conj p q ihp ihq =>
      intro hd a v hist ρ hv
      have hm : honest d hist (.conj p q) a = [p.eval a, q.eval a] := rfl
      simp only [run, hm]
      rw [if_pos (by rw [hv]; rfl)]
      simp only [Bool.and_eq_true]
      exact ⟨ihp hd.1 _ _ _ _ rfl, ihq hd.2 _ _ _ _ rfl⟩
  | disj p q ihp ihq =>
      intro hd a v hist ρ hv
      have hm : honest d hist (.disj p q) a = [p.eval a, q.eval a] := rfl
      simp only [run, hm]
      rw [if_pos (by rw [hv]; rfl)]
      simp only [Bool.and_eq_true]
      exact ⟨ihp hd.1 _ _ _ _ rfl, ihq hd.2 _ _ _ _ rfl⟩
  | all i p ih =>
      intro hd a v hist ρ hv
      obtain ⟨hlen, hval⟩ := honest_round hd.1 (.all i p) (Or.inl rfl) hist (a := a)
      simp only [run]
      rw [if_pos ⟨hlen.le, by rw [hval, hval, hv]; rfl⟩]
      exact ih hd.2 _ _ _ _ (hval _)
  | ex i p ih =>
      intro hd a v hist ρ hv
      obtain ⟨hlen, hval⟩ := honest_round hd.1 (.ex i p) (Or.inr (Or.inl rfl)) hist (a := a)
      simp only [run]
      rw [if_pos ⟨hlen.le, by rw [hval, hval, hv]; rfl⟩]
      exact ih hd.2 _ _ _ _ (hval _)
  | lin j p ih =>
      intro hd a v hist ρ hv
      obtain ⟨hlen, hval⟩ := honest_round hd.1 (.lin j p) (Or.inr (Or.inr rfl)) hist (a := a)
      simp only [run]
      rw [if_pos ⟨hlen.le, by rw [hval, hval, hv]; rfl⟩]
      exact ih hd.2 _ _ _ _ (hval _)

/-- **Perfect completeness**, as a probability. -/
theorem scProb_honest {d : ℕ} {t : Op} (hd : Op.RoundDeg F d t) (a : ℕ → F) :
    scProb d (honest d) t a (t.eval a) = 1 := by
  unfold scProb
  rw [cntL_true _ (fun ρ _ => run_honest d t hd a _ [] ρ rfl)]
  have : (0 : ℚ) < (Fintype.card F : ℚ) ^ t.rounds := by
    have := Fintype.card_pos (α := F); positivity
  push_cast
  exact div_self this.ne'

/-! ### Soundness -/

omit [DecidableEq F] in
/-- The counting step of a round: if the prover's polynomial `m` differs from the true restriction
`g`, it agrees with it at no more than `d` points, and away from those points the claim passed on
is false. -/
theorem round_count {n d D : ℕ} (E : F → List F → Bool) {m : List F} {g : F[X]}
    (hml : m.length ≤ d + 1) (hg : g.natDegree ≤ d) (hne : toPoly m ≠ g)
    (ih : ∀ s, evalL m s ≠ g.eval s → cntL n (E s) * Fintype.card F ≤ D * Fintype.card F ^ n) :
    cntL (n + 1) (fun ρ => E (ρ.headD 0) ρ.tail) * Fintype.card F ≤
      (d + D) * Fintype.card F ^ (n + 1) := by
  classical
  set k := Fintype.card F
  rw [cntL_succ]
  simp only [List.headD_cons, List.tail_cons]
  have hb : ∀ s, cntL n (E s) * k ≤
      (if evalL m s = g.eval s then k ^ n * k else 0) + D * k ^ n := by
    intro s
    by_cases hs : evalL m s = g.eval s
    · rw [if_pos hs]
      exact (Nat.mul_le_mul_right _ (cntL_le_pow n _)).trans (Nat.le_add_right _ _)
    · rw [if_neg hs, zero_add]; exact ih s hs
  have hgood : (Finset.univ.filter fun s => evalL m s = g.eval s).card ≤ d := by
    have := card_eval_eq_le hne ((natDegree_toPoly m).trans (by omega)) hg
    simpa [eval_toPoly] using this
  calc (∑ s : F, cntL n (E s)) * k = ∑ s : F, cntL n (E s) * k := Finset.sum_mul ..
    _ ≤ ∑ s : F, ((if evalL m s = g.eval s then k ^ n * k else 0) + D * k ^ n) :=
        Finset.sum_le_sum fun s _ => hb s
    _ = (Finset.univ.filter fun s => evalL m s = g.eval s).card * (k ^ n * k) +
          k * (D * k ^ n) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, Finset.card_univ]
    _ ≤ d * (k ^ n * k) + k * (D * k ^ n) := Nat.add_le_add_right
        (Nat.mul_le_mul_right _ hgood) _
    _ = (d + D) * k ^ (n + 1) := by ring

omit [Field F] [DecidableEq F] in
/-- The counting step of a conjunction or disjunction: if the claim passed to the first child is
false, or the one passed to the second child is false whatever happened in the first, the
acceptance count is bounded by the bound of that child. -/
theorem split_count {n₁ n₂ D₁ D₂ : ℕ} (E₁ : List F → Bool) (E₂ : List F → List F → Bool)
    (h : (∀ ρ₁, ρ₁.length = n₁ → cntL n₂ (E₂ ρ₁) * Fintype.card F ≤ D₂ * Fintype.card F ^ n₂) ∨
      cntL n₁ E₁ * Fintype.card F ≤ D₁ * Fintype.card F ^ n₁) :
    cntL (n₁ + n₂) (fun ρ => E₁ (ρ.take n₁) && E₂ (ρ.take n₁) (ρ.drop n₁)) * Fintype.card F ≤
      (D₁ + D₂) * Fintype.card F ^ (n₁ + n₂) := by
  set k := Fintype.card F
  have hsplit : cntL (n₁ + n₂) (fun ρ => E₁ (ρ.take n₁) && E₂ (ρ.take n₁) (ρ.drop n₁)) =
      sumL n₁ (fun ρ₁ => if E₁ ρ₁ then cntL n₂ (E₂ ρ₁) else 0) := by
    rw [cntL, sumL_append]
    refine sumL_congr fun ρ₁ hρ₁ => ?_
    simp only [List.take_left' hρ₁, List.drop_left' hρ₁]
    by_cases hE : E₁ ρ₁ = true
    · simp [hE, cntL]
    · simp only [hE, Bool.false_and]
      simp [sumL_const]
  rw [hsplit]
  rcases h with h | h
  · calc sumL n₁ (fun ρ₁ => if E₁ ρ₁ then cntL n₂ (E₂ ρ₁) else 0) * k
        = sumL n₁ (fun ρ₁ => (if E₁ ρ₁ then cntL n₂ (E₂ ρ₁) else 0) * k) := by
          rw [mul_comm, ← sumL_mul_left]; simp only [mul_comm]
      _ ≤ sumL n₁ (fun _ => D₂ * k ^ n₂) := sumL_le_of_length fun ρ₁ hρ₁ => by
          split
          · exact h ρ₁ hρ₁
          · simp
      _ = k ^ n₁ * (D₂ * k ^ n₂) := sumL_const _ _
      _ ≤ (D₁ + D₂) * k ^ (n₁ + n₂) := by
          rw [pow_add]; nlinarith [Nat.zero_le (D₁ * (k ^ n₁ * k ^ n₂))]
  · calc sumL n₁ (fun ρ₁ => if E₁ ρ₁ then cntL n₂ (E₂ ρ₁) else 0) * k
        ≤ sumL n₁ (fun ρ₁ => (if E₁ ρ₁ then 1 else 0) * k ^ n₂) * k := by
          refine Nat.mul_le_mul_right _ (sumL_mono fun ρ₁ => ?_)
          split
          · simpa using cntL_le_pow n₂ (E₂ ρ₁)
          · simp
      _ = cntL n₁ E₁ * k * k ^ n₂ := by
          unfold cntL
          rw [show (fun ρ₁ => (if E₁ ρ₁ then 1 else 0) * k ^ n₂) =
              (fun ρ₁ => k ^ n₂ * (if E₁ ρ₁ then 1 else 0)) from funext fun _ => mul_comm _ _,
            sumL_mul_left]
          ring
      _ ≤ D₁ * k ^ n₁ * k ^ n₂ := Nat.mul_le_mul_right _ h
      _ ≤ (D₁ + D₂) * k ^ (n₁ + n₂) := by
          rw [pow_add]; nlinarith [Nat.zero_le (D₂ * (k ^ n₁ * k ^ n₂))]

omit [Fintype F] in
/-- The run of a conjunction or disjunction node, unfolded: after a well-formed message, the
verdict is the conjunction of the verdicts on the two children. -/
theorem run_conj_eq (d : ℕ) (P : Strat F) (p q : Op) (a : ℕ → F) (v : F) (hist : List (List F))
    (ρ : List F) :
    (run d P (.conj p q) a v hist ρ).1 = true →
      ∃ b c, P hist (.conj p q) a = [b, c] ∧ b * c = v ∧
        (run d P (.conj p q) a v hist ρ).1 =
          ((run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 &&
            (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
              (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1) := by
  intro h
  simp only [run] at h ⊢
  split at h
  · rename_i b c hm
    split at h
    · rename_i hbc
      refine ⟨b, c, hm, hbc, ?_⟩
      simp [hbc]
    · simp at h
  · simp at h

omit [Fintype F] in
theorem run_disj_eq (d : ℕ) (P : Strat F) (p q : Op) (a : ℕ → F) (v : F) (hist : List (List F))
    (ρ : List F) :
    (run d P (.disj p q) a v hist ρ).1 = true →
      ∃ b c, P hist (.disj p q) a = [b, c] ∧ 1 - (1 - b) * (1 - c) = v ∧
        (run d P (.disj p q) a v hist ρ).1 =
          ((run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 &&
            (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
              (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1) := by
  intro h
  simp only [run] at h ⊢
  split at h
  · rename_i b c hm
    split at h
    · rename_i hbc
      refine ⟨b, c, hm, hbc, ?_⟩
      simp [hbc]
    · simp at h
  · simp at h

/-- The binary nodes, uniformly: the acceptance count of a false claim is bounded. -/
theorem binary_count {d : ℕ} (P : Strat F) (p q : Op) (a : ℕ → F) (v : F)
    (hist : List (List F)) (t : Op) (comb : F → F → F)
    (htrue : t.eval a = comb (p.eval a) (q.eval a))
    (hv : v ≠ t.eval a) (hrounds : t.rounds = p.rounds + q.rounds + 1)
    (hrun : ∀ ρ, (run d P t a v hist ρ).1 = true →
      ∃ b c, P hist t a = [b, c] ∧ comb b c = v ∧
        (run d P t a v hist ρ).1 =
          ((run d P p a b (hist ++ [[b, c], [ρ.headD 0]]) (ρ.tail.take p.rounds)).1 &&
            (run d P q a c (run d P p a b (hist ++ [[b, c], [ρ.headD 0]])
              (ρ.tail.take p.rounds)).2 (ρ.tail.drop p.rounds)).1))
    (ihp : ∀ (P : Strat F) a v hist, v ≠ p.eval a →
      cntL p.rounds (fun ρ => (run d P p a v hist ρ).1) * Fintype.card F ≤
        d * p.rounds * Fintype.card F ^ p.rounds)
    (ihq : ∀ (P : Strat F) a v hist, v ≠ q.eval a →
      cntL q.rounds (fun ρ => (run d P q a v hist ρ).1) * Fintype.card F ≤
        d * q.rounds * Fintype.card F ^ q.rounds) :
    cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) * Fintype.card F ≤
      d * t.rounds * Fintype.card F ^ t.rounds := by
  set k := Fintype.card F
  by_cases hm : ∃ b c, P hist t a = [b, c] ∧ comb b c = v
  · obtain ⟨b, c, hm, hbc⟩ := hm
    set E : F → List F → Bool := fun s ρ =>
      (run d P p a b (hist ++ [[b, c], [s]]) (ρ.take p.rounds)).1 &&
        (run d P q a c (run d P p a b (hist ++ [[b, c], [s]]) (ρ.take p.rounds)).2
          (ρ.drop p.rounds)).1 with hE
    have hle : cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) ≤
        cntL (p.rounds + q.rounds + 1) (fun ρ => E (ρ.headD 0) ρ.tail) := by
      rw [hrounds]
      refine cntL_mono fun ρ hρ => ?_
      obtain ⟨b', c', hm', _, heq⟩ := hrun ρ hρ
      rw [hm] at hm'
      simp only [List.cons.injEq, and_true] at hm'
      obtain ⟨rfl, rfl⟩ := hm'
      simp only [hE]; rw [← heq]; exact hρ
    have hs : ∀ s : F, cntL (p.rounds + q.rounds) (E s) * k ≤
        (d * p.rounds + d * q.rounds) * k ^ (p.rounds + q.rounds) := by
      intro s
      refine split_count (n₁ := p.rounds) (n₂ := q.rounds) (D₁ := d * p.rounds)
        (D₂ := d * q.rounds) (fun ρ₁ => (run d P p a b (hist ++ [[b, c], [s]]) ρ₁).1)
        (fun ρ₁ ρ₂ => (run d P q a c (run d P p a b (hist ++ [[b, c], [s]]) ρ₁).2 ρ₂).1) ?_
      by_cases hb : b = p.eval a
      · left
        intro ρ₁ _
        refine ihq _ _ _ _ fun hc => hv ?_
        rw [htrue, ← hb, ← hc, hbc]
      · right
        exact ihp _ _ _ _ hb
    have hsum : cntL (p.rounds + q.rounds + 1) (fun ρ => E (ρ.headD 0) ρ.tail) * k ≤
        k * ((d * p.rounds + d * q.rounds) * k ^ (p.rounds + q.rounds)) := by
      rw [cntL_succ]
      simp only [List.headD_cons, List.tail_cons]
      rw [Finset.sum_mul]
      calc _ ≤ ∑ _s : F, (d * p.rounds + d * q.rounds) * k ^ (p.rounds + q.rounds) :=
            Finset.sum_le_sum fun s _ => hs s
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    calc cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) * k
        ≤ cntL (p.rounds + q.rounds + 1) (fun ρ => E (ρ.headD 0) ρ.tail) * k :=
          Nat.mul_le_mul_right _ hle
      _ ≤ k * ((d * p.rounds + d * q.rounds) * k ^ (p.rounds + q.rounds)) := hsum
      _ ≤ d * t.rounds * k ^ t.rounds := by
          rw [hrounds, pow_succ]
          nlinarith [Nat.zero_le (d * k ^ (p.rounds + q.rounds) * k)]
  · have : cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) = 0 :=
      cntL_false _ fun ρ _ => by
        by_contra h
        obtain ⟨b, c, h1, h2, _⟩ := hrun ρ (by simpa using h)
        exact hm ⟨b, c, h1, h2⟩
    rw [this]; simp

/-- The rounds, uniformly. -/
theorem quant_count {d : ℕ} (P : Strat F) (p : Op) (i : ℕ) (a : ℕ → F) (v : F)
    (hist : List (List F)) (t : Op) (check : List F → Prop) [DecidablePred check]
    (truth : (F → F) → F)
    (hcheck_true : ∀ m : List F, check m → (∀ x, evalL m x = p.eval (Function.update a i x)) →
      v = truth fun x => p.eval (Function.update a i x))
    (htrue : t.eval a = truth fun x => p.eval (Function.update a i x))
    (hv : v ≠ t.eval a) (hrounds : t.rounds = p.rounds + 1)
    (hrun : ∀ ρ, (run d P t a v hist ρ).1 =
      if (P hist t a).length ≤ d + 1 ∧ check (P hist t a) then
        (run d P p (Function.update a i (ρ.headD 0)) (evalL (P hist t a) (ρ.headD 0))
          (hist ++ [P hist t a, [ρ.headD 0]]) ρ.tail).1
      else false)
    (hdeg : UniDeg (fun b : ℕ → F => p.eval b) i d)
    (ihp : ∀ (P : Strat F) a v hist, v ≠ p.eval a →
      cntL p.rounds (fun ρ => (run d P p a v hist ρ).1) * Fintype.card F ≤
        d * p.rounds * Fintype.card F ^ p.rounds) :
    cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) * Fintype.card F ≤
      d * t.rounds * Fintype.card F ^ t.rounds := by
  set m := P hist t a
  by_cases hc : m.length ≤ d + 1 ∧ check m
  · obtain ⟨g, hg, hgx⟩ := hdeg a
    have hne : toPoly m ≠ g := by
      intro heq
      apply hv
      rw [htrue]
      refine hcheck_true m hc.2 fun x => ?_
      rw [← eval_toPoly, heq, hgx]
    have := round_count (n := p.rounds) (d := d) (D := d * p.rounds)
      (fun s ρ => (run d P p (Function.update a i s) (evalL m s) (hist ++ [m, [s]]) ρ).1)
      hc.1 hg hne (fun s hs => ihp _ _ _ _ (fun h => hs (h.trans (hgx s).symm)))
    rw [hrounds]
    have heq : (fun ρ => (run d P t a v hist ρ).1) =
        (fun ρ => (run d P p (Function.update a i (ρ.headD 0)) (evalL m (ρ.headD 0))
          (hist ++ [m, [ρ.headD 0]]) ρ.tail).1) := by
      funext ρ; rw [hrun ρ, if_pos hc]
    rw [heq]
    calc _ ≤ (d + d * p.rounds) * Fintype.card F ^ (p.rounds + 1) := this
      _ = _ := by ring
  · have : cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) = 0 :=
      cntL_false _ fun ρ _ => by rw [hrun ρ, if_neg hc]
    rw [this]; simp

/-- **Soundness of sum-check**: on a false claim, every prover is accepted on at most
`d · rounds · |F| ^ (rounds - 1)` of the `|F| ^ rounds` lists of random points. -/
theorem cntL_run_false (d : ℕ) :
    ∀ (t : Op), Op.RoundDeg F d t → ∀ (P : Strat F) (a : ℕ → F) (v : F) (hist : List (List F)),
      v ≠ t.eval a →
      cntL t.rounds (fun ρ => (run d P t a v hist ρ).1) * Fintype.card F ≤
        d * t.rounds * Fintype.card F ^ t.rounds := by
  intro t
  induction t with
  | var i =>
      intro _ P a v hist hv
      have hv' : a i ≠ v := fun h => hv (by rw [Op.eval, h])
      rw [cntL_false _ fun ρ _ => by simp only [run, decide_eq_false_iff_not]; exact hv']
      simp
  | neg p ih =>
      intro hd P a v hist hv
      exact ih hd P a (1 - v) hist (fun h => hv (by simp [Op.eval, ← h]))
  | conj p q ihp ihq =>
      intro hd P a v hist hv
      exact binary_count P p q a v hist (.conj p q) (· * ·) rfl hv rfl
        (run_conj_eq d P p q a v hist) (ihp hd.1) (ihq hd.2)
  | disj p q ihp ihq =>
      intro hd P a v hist hv
      exact binary_count P p q a v hist (.disj p q) (fun b c => 1 - (1 - b) * (1 - c)) rfl hv rfl
        (run_disj_eq d P p q a v hist) (ihp hd.1) (ihq hd.2)
  | all i p ih =>
      intro hd P a v hist hv
      exact quant_count P p i a v hist (.all i p) (fun m => evalL m 0 * evalL m 1 = v)
        (fun f => f 0 * f 1) (fun m hm hx => by rw [← hm, hx, hx]) rfl hv rfl
        (fun ρ => by simp only [run]; split <;> rfl) hd.1 (ih hd.2)
  | ex i p ih =>
      intro hd P a v hist hv
      exact quant_count P p i a v hist (.ex i p)
        (fun m => 1 - (1 - evalL m 0) * (1 - evalL m 1) = v)
        (fun f => 1 - (1 - f 0) * (1 - f 1)) (fun m hm hx => by rw [← hm, hx, hx]) rfl hv rfl
        (fun ρ => by simp only [run]; split <;> rfl) hd.1 (ih hd.2)
  | lin j p ih =>
      intro hd P a v hist hv
      exact quant_count P p j a v hist (.lin j p)
        (fun m => a j * evalL m 1 + (1 - a j) * evalL m 0 = v)
        (fun f => a j * f 1 + (1 - a j) * f 0) (fun m hm hx => by rw [← hm, hx, hx]) rfl hv rfl
        (fun ρ => by simp only [run]; split <;> rfl) hd.1 (ih hd.2)

/-- **Soundness**, as a probability: on a false claim every prover is accepted with probability
at most `d · rounds / |F|`. -/
theorem scProb_le {d : ℕ} {t : Op} (hd : Op.RoundDeg F d t) (P : Strat F) (a : ℕ → F) {v : F}
    (hv : v ≠ t.eval a) :
    scProb d P t a v ≤ (d * t.rounds : ℚ) / Fintype.card F := by
  unfold scProb
  have hk : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h := cntL_run_false d t hd P a v [] hv
  rw [div_le_div_iff₀ (by positivity) hk]
  have h' : ((cntL t.rounds fun ρ => (run d P t a v [] ρ).1 : ℕ) : ℚ) * Fintype.card F ≤
      (d * t.rounds : ℚ) * (Fintype.card F : ℚ) ^ t.rounds := by exact_mod_cast h
  exact h'

/-! ### The game for a formula -/

/-- **Sum-check for `TQBF`, completeness**: for a true closed formula the honest prover convinces
the verifier of the claim "the operator tree evaluates to `1` at `0`" with probability `1`. -/
theorem tqbf_sumcheck_complete {N : ℕ} {p : QBF} (hp : p.Closed) (hN : p.varBound ≤ N)
    (h : TQBF p) :
    scProb (2 * p.size) (honest (2 * p.size)) (QBF.toOp N p) (fun _ => (0 : F)) 1 = 1 := by
  have h1 := (QBF.tqbf_iff_toOp (R := F) N hp).1 h
  have := scProb_honest (QBF.roundDeg_toOp (R := F) p hN) (fun _ => (0 : F))
  rwa [h1] at this

/-- **Sum-check for `TQBF`, soundness**: for a false closed formula every prover convinces the
verifier with probability at most `2 · size p · (N + 1) · size p / |F|`. -/
theorem tqbf_sumcheck_sound {N : ℕ} {p : QBF} (hp : p.Closed) (hN : p.varBound ≤ N)
    (h : ¬ TQBF p) (P : Strat F) :
    scProb (2 * p.size) P (QBF.toOp N p) (fun _ => (0 : F)) 1 ≤
      (2 * p.size * ((N + 1) * p.size) : ℚ) / Fintype.card F := by
  have hv : (1 : F) ≠ (QBF.toOp N p).eval (fun _ => (0 : F)) :=
    fun h1 => h ((QBF.tqbf_iff_toOp (R := F) N hp).2 h1.symm)
  refine (scProb_le (QBF.roundDeg_toOp (R := F) p hN) P _ hv).trans ?_
  have hk : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hr : ((QBF.toOp N p).rounds : ℚ) ≤ (N + 1) * p.size := by
    exact_mod_cast (Op.rounds_le_size _).trans (QBF.size_toOp N p)
  gcongr
  push_cast
  gcongr

end Complexity.Qbf
