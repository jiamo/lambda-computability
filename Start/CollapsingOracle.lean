/-
**An oracle that collapses `P` and `NP`.**

The relativization barrier needs, besides the separating oracle of `Start/BakerGillSolovay.lean`,
an oracle `A` with `P^A = NP^A`.  Classically one takes a `PSPACE`-complete language.  Here the
collapsing oracle is built directly, by a *self-referential* construction that needs no space
machines at all: the oracle answers, on a padded query

  `z = 1^K 0 1^L 0 1^c 0 x`,

whether the oracle verifier with code `c` accepts `(x, w)` for some witness `w` with `|w| ≤ L`,
where the verifier itself is run with the oracle *restricted to words shorter than `z`*.  The
restriction makes the definition well founded (by recursion on the length of `z`), and the padding
`1^K` makes every query that the verifier can ask on such inputs shorter than `z` once `K` is large
enough, so that by the use principle (`Complexity.CobQ.eval_congr`) the restricted run is the real
run.  An `NP^A` language is then decided in `P^A` by a single query: compute `z` from `x` (a
Cobham term) and ask the oracle.

* `Complexity.Collapse.oracleC` — the oracle;
* `Complexity.Collapse.oracleC_eq` — its fixed-point equation;
* `Complexity.Collapse.peqNP_rel_oracleC` — **`P^A = NP^A` for `A = oracleC`**;
* `Complexity.bgs_equal` — hence some oracle collapses `P` and `NP`.
-/

import Mathlib
import Start.OracleEnum
import Start.OracleClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Collapse

/-! ### Padded words -/

/-- `pad m y = 1^m 0 y`. -/
def pad (m : ℕ) (y : Word) : Word := List.replicate m true ++ false :: y

@[simp] theorem length_pad (m : ℕ) (y : Word) : (pad m y).length = m + y.length + 1 := by
  simp [pad]; omega

theorem pad_inj {m m' : ℕ} {y y' : Word} (h : pad m y = pad m' y') : m = m' ∧ y = y' := by
  induction m generalizing m' with
  | zero =>
      cases m' with
      | zero => simpa [pad] using h
      | succ m' => simp [pad, List.replicate_succ] at h
  | succ m ih =>
      cases m' with
      | zero => simp [pad, List.replicate_succ] at h
      | succ m' =>
          have h' : pad m y = pad m' y' := by
            simpa [pad, List.replicate_succ] using h
          obtain ⟨h1, h2⟩ := ih h'
          exact ⟨by omega, h2⟩

/-! ### The construction -/

/-- The oracle `B` restricted to words of length below `n`. -/
def trunc (B : Oracle) (n : ℕ) : Oracle := fun u => B u && decide (u.length < n)

/-- An injective numbering of the oracle Cobham terms. -/
noncomputable def termCode : CobQ → ℕ := @Encodable.encode CobQ (Encodable.ofCountable CobQ)

theorem termCode_injective : Function.Injective termCode :=
  @Encodable.encode_injective CobQ (Encodable.ofCountable CobQ)

/-- One step of the construction: `z` is a padded query `1^K 0 1^L 0 1^c 0 x` and the verifier
with code `c`, run with `B` restricted to words shorter than `z`, accepts `(x, w)` for some `w` of
length at most `L`. -/
def Step (B : Oracle) (z : Word) : Prop :=
  ∃ (K L : ℕ) (v : CobQ) (x : Word), z = pad K (pad L (pad (termCode v) x)) ∧
    ∃ w : Word, w.length ≤ L ∧ CobQ.eval (trunc B z.length) v [x, w] ≠ []

open Classical in
/-- The approximations: `approx (n + 1)` is the step applied to `approx n`. -/
noncomputable def approx : ℕ → Oracle
  | 0 => fun _ => false
  | n + 1 => fun z => decide (Step (approx n) z)

/-- **The collapsing oracle**: on `z`, the approximation of index `|z| + 1`. -/
noncomputable def oracleC : Oracle := fun z => approx (z.length + 1) z

/-- The step only looks at the oracle on words shorter than its argument. -/
theorem step_congr {B B' : Oracle} {z : Word} (h : ∀ u : Word, u.length < z.length → B u = B' u) :
    Step B z ↔ Step B' z := by
  have ht : trunc B z.length = trunc B' z.length := by
    funext u
    by_cases hu : u.length < z.length
    · simp [trunc, h u hu]
    · simp [trunc, hu]
  unfold Step
  rw [ht]

open Classical in
theorem approx_eq_oracleC : ∀ (n : ℕ) (z : Word), z.length < n → approx n z = oracleC z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro z hz
      match n, ih, hz with
      | 0, _, hz => exact absurd hz (Nat.not_lt_zero _)
      | n + 1, ih, hz =>
          change decide (Step (approx n) z) = decide (Step (approx z.length) z)
          have h1 : Step (approx n) z ↔ Step oracleC z :=
            step_congr fun u hu => ih n (Nat.lt_succ_self n) u (by omega)
          have h2 : Step (approx z.length) z ↔ Step oracleC z :=
            step_congr fun u hu => ih z.length (by omega) u hu
          simp only [h1, h2]

open Classical in
/-- **The fixed-point equation of the collapsing oracle.** -/
theorem oracleC_eq (z : Word) : oracleC z = decide (Step oracleC z) := by
  change decide (Step (approx z.length) z) = decide (Step oracleC z)
  have h : Step (approx z.length) z ↔ Step oracleC z :=
    step_congr fun u hu => approx_eq_oracleC z.length u hu
  simp only [h]

/-! ### Cobham terms producing the padding -/

/-- The constant word `1^a`. -/
def onesC : ℕ → Cob
  | 0 => .empty
  | a + 1 => .comp (.app true) [onesC a]

@[simp] theorem eval_onesC (a : ℕ) (args : List Word) :
    (onesC a).eval args = List.replicate a true := by
  induction a with
  | zero => simp [onesC]
  | succ a ih => simp [onesC, ih, List.replicate_succ]

/-- `x ↦ 1^{|x| + 1}`. -/
def unaryC : Cob := .comp .smash [.comp (.app true) [.proj 0], Cob.trueC]

@[simp] theorem eval_unaryC (x : Word) :
    unaryC.eval [x] = List.replicate (x.length + 1) true := by
  simp [unaryC]

/-- `x ↦ 1^{a (|x| + 1)^k}`. -/
def polyC (a : ℕ) : ℕ → Cob
  | 0 => onesC a
  | k + 1 => .comp .smash [polyC a k, unaryC]

@[simp] theorem eval_polyC (a k : ℕ) (x : Word) :
    (polyC a k).eval [x] = List.replicate (a * (x.length + 1) ^ k) true := by
  induction k with
  | zero => simp [polyC]
  | succ k ih =>
      simp only [polyC, Cob.eval_comp, List.map_cons, List.map_nil, ih, eval_unaryC,
        Cob.eval_smash, List.getD_cons_zero, List.getD_cons_succ, List.length_replicate]
      rw [pow_succ, mul_assoc]

/-- `x ↦ pad |u x| (inner x)` for a unary `u`. -/
def padC (u inner : Cob) : Cob := .comp Cob.concat [u, .comp (.app false) [inner]]

theorem eval_padC (u inner : Cob) (x : Word) (m : ℕ) (hu : u.eval [x] = List.replicate m true) :
    (padC u inner).eval [x] = pad m (inner.eval [x]) := by
  simp [padC, hu, pad]

/-- The term computing the padded query `1^{b(|x|+1)^j} 0 1^{a(|x|+1)^k} 0 1^c 0 x`. -/
def queryWordC (b j a k c : ℕ) : Cob :=
  padC (polyC b j) (padC (polyC a k) (padC (onesC c) (.proj 0)))

theorem eval_queryWordC (b j a k c : ℕ) (x : Word) :
    (queryWordC b j a k c).eval [x] =
      pad (b * (x.length + 1) ^ j) (pad (a * (x.length + 1) ^ k) (pad c x)) := by
  unfold queryWordC
  rw [eval_padC _ _ _ _ (eval_polyC b j x), eval_padC _ _ _ _ (eval_polyC a k x),
    eval_padC _ _ _ _ (eval_onesC c [x])]
  simp

/-! ### The collapse -/

/-- The single-query decider: ask the oracle about the padded query word. -/
def decider (b j a k c : ℕ) : CobQ := .comp .query [CobQ.ofCob (queryWordC b j a k c)]

theorem eval_decider (A : Oracle) (b j a k c : ℕ) (x : Word) :
    CobQ.eval A (decider b j a k c) [x] ≠ [] ↔ A ((queryWordC b j a k c).eval [x]) = true := by
  unfold decider CobQ.eval
  rw [CobQ.run_comp]
  simp only [List.map_cons, List.map_nil, CobQ.eval_ofCob, CobQ.run_query, List.getD_cons_zero]
  cases A ((queryWordC b j a k c).eval [x]) <;> simp

/-- **`P^A = NP^A` for the collapsing oracle.** -/
theorem peqNP_rel_oracleC : PeqNP_rel oracleC := by
  classical
  intro Lang hL
  obtain ⟨v, p, hp, -, hlen, hLx⟩ := hL
  obtain ⟨a, k, hak⟩ := hp
  obtain ⟨q, ⟨hqb, hqm⟩, hq⟩ := CobQ.polyQueryLen v
  have hpoly : PolyBound (fun n => q (n + a * (n + 1) ^ k)) :=
    hqb.comp (PolyBound.add ⟨1, 1, fun n => by simp⟩ ⟨a, k, fun n => le_rfl⟩)
  obtain ⟨b, j, hbj⟩ := hpoly
  refine ⟨decider b j a k (termCode v), fun x => ?_⟩
  rw [eval_decider, eval_queryWordC, oracleC_eq, decide_eq_true_iff]
  set n := x.length
  set z := pad (b * (n + 1) ^ j) (pad (a * (n + 1) ^ k) (pad (termCode v) x)) with hz
  -- Every query of the verifier on a witness of length at most `a (n+1)^k` is shorter than `z`.
  have hshort : ∀ w : Word, w.length ≤ a * (n + 1) ^ k →
      CobQ.eval (trunc oracleC z.length) v [x, w] = CobQ.eval oracleC v [x, w] := by
    intro w hw
    symm
    apply CobQ.eval_congr
    intro u hu
    have hu1 : u.length ≤ q (maxLen [x, w]) := hq oracleC [x, w] u hu
    have hmax : maxLen [x, w] ≤ n + a * (n + 1) ^ k := by
      simp [maxLen]; omega
    have hu2 : u.length < z.length := by
      have := hqm hmax
      have : q (n + a * (n + 1) ^ k) ≤ b * (n + 1) ^ j := hbj n
      simp only [hz, length_pad]
      omega
    simp [trunc, hu2]
  rw [hLx x]
  constructor
  · rintro ⟨w, hw⟩
    have hwl : w.length ≤ a * (n + 1) ^ k := le_trans (hlen x w hw) (hak _)
    exact ⟨_, _, v, x, rfl, w, hwl, by rw [hshort w hwl]; exact hw⟩
  · rintro ⟨K, L, v', x', heq, w, hw, hacc⟩
    obtain ⟨hK, h1⟩ := pad_inj heq
    obtain ⟨hL', h2⟩ := pad_inj h1
    obtain ⟨hc, hx⟩ := pad_inj h2
    have hv : v' = v := termCode_injective hc.symm
    subst hv hx hL'
    exact ⟨w, by rw [← hshort w hw]; exact hacc⟩

end Collapse

/-- **Baker–Gill–Solovay, the collapsing half: there is an oracle with `P^A = NP^A`.** -/
theorem bgs_equal : ∃ A : Oracle, PeqNP_rel A := ⟨Collapse.oracleC, Collapse.peqNP_rel_oracleC⟩

end Complexity
