/-
Complexity classes: `FP`, `P`, `NP`, polynomial-time many-one reductions and NP-completeness.

The polynomial-time computable *functions* on binary words are defined à la **Cobham** (1965): as
the smallest class containing the empty word, the projections, the two successor functions
`x ↦ 0x`, `x ↦ 1x` and the smash function `x # y = 1^{|x|·|y|}`, and closed under composition and
*bounded recursion on notation*.  Cobham's theorem — that this class coincides with the functions
computable by a Turing machine in polynomial time — is **not** formalized here; see the boundary
note at the end of the file.  What the syntactic definition buys us is that closure under
composition is a constructor rather than a theorem, which is exactly what the structural results
about `P`, `NP` and `≤ₘᵖ` need.

Main definitions:

* `Complexity.Cob`, `Complexity.Cob.eval` — Cobham's class and its semantics;
* `Complexity.InP`, `Complexity.InNP` — the classes `P` and `NP` of languages over `List Bool`;
* `Complexity.PolyManyOne` (`≤ₘᵖ`), `Complexity.NPHard`, `Complexity.NPComplete`;
* `Complexity.PeqNP` — the statement `P = NP`.

Main results:

* `Complexity.Cob.polyLen` — a Cobham function has polynomially bounded output length;
* `Complexity.Cob.eval_concat` — concatenation of words is a Cobham function;
* `Complexity.inNP_of_inP` — `P ⊆ NP`;
* `Complexity.polyManyOne_refl`, `Complexity.polyManyOne_trans` — `≤ₘᵖ` is a preorder;
* `Complexity.InP.of_reduction`, `Complexity.InNP.of_reduction` — `P` and `NP` are closed
  downwards under `≤ₘᵖ`;
* `Complexity.peqNP_of_npComplete_of_inP` — an NP-complete language in `P` collapses `P` and `NP`;
* `Complexity.InNP.union` — `NP` is closed under union;
* `Complexity.bruteForce_decides` — an `NP` language is decided by exhaustive search over the
  witnesses of bounded length;
* non-vacuity and closure: `Complexity.inP_univ`, `Complexity.inP_nonempty`,
  `Complexity.InP.compl`, `Complexity.InP.inter`, `Complexity.InP.union`.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- A binary word. -/
abbrev Word := List Bool

/-! ### Cobham's class of polynomial-time functions -/

/-- Syntax for Cobham's class of polynomial-time computable functions on binary words.  A term
denotes a function `List Word → Word`; arguments are addressed by position, and a missing
argument reads as the empty word. -/
inductive Cob : Type
  /-- The `i`-th argument. -/
  | proj (i : ℕ)
  /-- The constant empty word. -/
  | empty
  /-- The successor function `x ↦ b :: x` on the first argument. -/
  | app (b : Bool)
  /-- The smash function `x # y = 1^{|x|·|y|}` on the first two arguments. -/
  | smash
  /-- Composition. -/
  | comp (f : Cob) (gs : List Cob)
  /-- Bounded recursion on notation over the first argument, with base `g`, steps `h₀`, `h₁` and
  bound `bd`. -/
  | bRec (g h₀ h₁ bd : Cob)
  deriving Inhabited

/-- The function denoted by a Cobham term.  In the `bRec` case the recursion runs on the first
argument, the step functions receive `(tail of the recursion argument, recursive value, other
arguments)`, and the result is truncated to the length of the bound. -/
def Cob.eval : Cob → List Word → Word
  | .proj i, args => args.getD i []
  | .empty, _ => []
  | .app b, args => b :: args.getD 0 []
  | .smash, args =>
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true
  | .comp f gs, args => f.eval (gs.attach.map (fun g => g.1.eval args))
  | .bRec g h₀ h₁ bd, args =>
      List.rec (g.eval args.tail)
        (fun b x' ih =>
          (if b then h₁.eval (x' :: ih :: args.tail) else h₀.eval (x' :: ih :: args.tail)).take
            ((bd.eval ((b :: x') :: args.tail)).length))
        (args.headD [])
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    · have := List.sizeOf_lt_of_mem g.2; omega
    all_goals omega

@[simp] theorem Cob.eval_proj (i : ℕ) (args : List Word) :
    (Cob.proj i).eval args = args.getD i [] := by
  rw [Cob.eval]

@[simp] theorem Cob.eval_empty (args : List Word) : Cob.empty.eval args = [] := by
  rw [Cob.eval]

@[simp] theorem Cob.eval_app (b : Bool) (args : List Word) :
    (Cob.app b).eval args = b :: args.getD 0 [] := by
  rw [Cob.eval]

@[simp] theorem Cob.eval_smash (args : List Word) :
    Cob.smash.eval args =
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true := by
  rw [Cob.eval]

@[simp] theorem Cob.eval_comp (f : Cob) (gs : List Cob) (args : List Word) :
    (Cob.comp f gs).eval args = f.eval (gs.map (fun g => g.eval args)) := by
  rw [Cob.eval]
  congr 1
  exact List.attach_map_val (l := gs) (f := fun g => g.eval args)

theorem Cob.eval_bRec (g h₀ h₁ bd : Cob) (args : List Word) :
    (Cob.bRec g h₀ h₁ bd).eval args =
      List.rec (g.eval args.tail)
        (fun b x' ih =>
          (if b then h₁.eval (x' :: ih :: args.tail) else h₀.eval (x' :: ih :: args.tail)).take
            ((bd.eval ((b :: x') :: args.tail)).length))
        (args.headD []) := by
  rw [Cob.eval]

@[simp] theorem Cob.eval_bRec_nil (g h₀ h₁ bd : Cob) (rest : List Word) :
    (Cob.bRec g h₀ h₁ bd).eval ([] :: rest) = g.eval rest := by
  rw [Cob.eval_bRec]; rfl

@[simp] theorem Cob.eval_bRec_cons (g h₀ h₁ bd : Cob) (b : Bool) (x : Word) (rest : List Word) :
    (Cob.bRec g h₀ h₁ bd).eval ((b :: x) :: rest) =
      (if b then h₁.eval (x :: (Cob.bRec g h₀ h₁ bd).eval (x :: rest) :: rest)
        else h₀.eval (x :: (Cob.bRec g h₀ h₁ bd).eval (x :: rest) :: rest)).take
        ((bd.eval ((b :: x) :: rest)).length) := by
  rw [Cob.eval_bRec, Cob.eval_bRec]; rfl

/-! ### A few gadgets -/

/-- The constant word `[true]`, used as the "accept" value. -/
def Cob.trueC : Cob := .comp (.app Bool.true) [.empty]

@[simp] theorem Cob.eval_trueC (args : List Word) : Cob.trueC.eval args = [Bool.true] := by
  simp [Cob.trueC]

/-- Boolean negation: the first argument is read as a truth value, "true" meaning nonempty. -/
def Cob.notC : Cob := .bRec .trueC .empty .empty .empty

@[simp] theorem Cob.eval_notC (u : Word) (rest : List Word) :
    Cob.notC.eval (u :: rest) = if u = [] then [Bool.true] else [] := by
  cases u with
  | nil => simp [Cob.notC]
  | cons b x => cases b <;> simp [Cob.notC]

/-- Conjunction: `andC u v` is `v` if `u` is nonempty, and the empty word otherwise. -/
def Cob.andC : Cob := .bRec .empty (.proj 2) (.proj 2) (.proj 1)

@[simp] theorem Cob.eval_andC (u v : Word) :
    Cob.andC.eval [u, v] = if u = [] then [] else v := by
  cases u with
  | nil => simp [Cob.andC]
  | cons b x => cases b <;> simp [Cob.andC]

/-- Disjunction: `orC u v` is `[true]` if `u` is nonempty, and `v` otherwise. -/
def Cob.orC : Cob := .bRec (.proj 0) .trueC .trueC .trueC

@[simp] theorem Cob.eval_orC (u v : Word) :
    Cob.orC.eval [u, v] = if u = [] then v else [Bool.true] := by
  cases u with
  | nil => simp [Cob.orC]
  | cons b x => cases b <;> simp [Cob.orC]

/-- The tail of the first argument. -/
def Cob.tailC : Cob := .bRec .empty (.proj 0) (.proj 0) (.proj 0)

@[simp] theorem Cob.eval_tailC (u : Word) (rest : List Word) :
    Cob.tailC.eval (u :: rest) = u.tail := by
  cases u with
  | nil => simp [Cob.tailC]
  | cons b x => cases b <;> simp [Cob.tailC, List.take_of_length_le]

/-- Tests whether the first argument starts with the bit `true`. -/
def Cob.headTrue : Cob := .bRec .empty .empty .trueC .trueC

@[simp] theorem Cob.eval_headTrue (u : Word) (rest : List Word) :
    Cob.headTrue.eval (u :: rest) = if u.headD Bool.false then [Bool.true] else [] := by
  cases u with
  | nil => simp [Cob.headTrue]
  | cons b x => cases b <;> simp [Cob.headTrue]

/-- The word `1^{|x|·|y|+|x|+|y|+1}`, a convenient Cobham bound for concatenation. -/
def Cob.padBound : Cob := .comp .smash [.comp (.app Bool.true) [.proj 0],
  .comp (.app Bool.true) [.proj 1]]

@[simp] theorem Cob.length_eval_padBound (x y : Word) :
    (Cob.padBound.eval [x, y]).length = (x.length + 1) * (y.length + 1) := by
  simp [Cob.padBound]

/-- Concatenation of words, by bounded recursion on notation over the first argument. -/
def Cob.concat : Cob :=
  .bRec (.proj 0) (.comp (.app Bool.false) [.proj 1]) (.comp (.app Bool.true) [.proj 1]) .padBound

/-- **Concatenation is a polynomial-time function** in the sense of Cobham: a nontrivial witness
that the class is usable. -/
@[simp] theorem Cob.eval_concat : ∀ (x y : Word), Cob.concat.eval [x, y] = x ++ y := by
  intro x
  induction x with
  | nil => intro y; simp [Cob.concat]
  | cons b x ih =>
      intro y
      rw [Cob.concat, Cob.eval_bRec_cons, ← Cob.concat, ih y, Cob.length_eval_padBound]
      have hlen : (b :: (x ++ y)).length ≤ ((b :: x).length + 1) * (y.length + 1) := by
        simp only [List.length_cons, List.length_append]
        nlinarith [Nat.zero_le (x.length * y.length)]
      cases b
      · rw [if_neg (by simp)]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
          List.getD_cons_succ, List.getD_cons_zero, Cob.eval_app]
        rw [List.take_of_length_le hlen]
        rfl
      · rw [if_pos rfl]
        simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
          List.getD_cons_succ, List.getD_cons_zero, Cob.eval_app]
        rw [List.take_of_length_le hlen]
        rfl

/-! ### Polynomial bounds -/

/-- `p` is bounded by a polynomial. -/
def PolyBound (p : ℕ → ℕ) : Prop := ∃ a k : ℕ, ∀ n, p n ≤ a * (n + 1) ^ k

theorem polyBound_const (c : ℕ) : PolyBound (fun _ => c) := ⟨c, 0, by simp⟩

theorem PolyBound.comp {p q : ℕ → ℕ} (hp : PolyBound p) (hq : PolyBound q) :
    PolyBound (fun n => p (q n)) := by
  obtain ⟨a, k, ha⟩ := hp
  obtain ⟨b, m, hb⟩ := hq
  refine ⟨a * (b + 1) ^ k, m * k, fun n => ?_⟩
  have hpow : 1 ≤ (n + 1) ^ m := Nat.one_le_pow _ _ (by omega)
  have h1 : q n + 1 ≤ (b + 1) * (n + 1) ^ m := by
    have := hb n
    nlinarith
  calc p (q n) ≤ a * (q n + 1) ^ k := ha (q n)
    _ ≤ a * ((b + 1) * (n + 1) ^ m) ^ k := by
        exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left h1 k)
    _ = a * (b + 1) ^ k * (n + 1) ^ (m * k) := by
        rw [mul_pow, ← pow_mul, mul_assoc]

theorem PolyBound.add {p q : ℕ → ℕ} (hp : PolyBound p) (hq : PolyBound q) :
    PolyBound (fun n => p n + q n) := by
  obtain ⟨a, k, ha⟩ := hp
  obtain ⟨b, m, hb⟩ := hq
  refine ⟨a + b, max k m, fun n => ?_⟩
  have h1 : a * (n + 1) ^ k ≤ a * (n + 1) ^ max k m :=
    Nat.mul_le_mul_left a (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have h2 : b * (n + 1) ^ m ≤ b * (n + 1) ^ max k m :=
    Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have := ha n
  have := hb n
  calc p n + q n ≤ a * (n + 1) ^ max k m + b * (n + 1) ^ max k m := by omega
    _ = (a + b) * (n + 1) ^ max k m := by ring

theorem PolyBound.mono {p q : ℕ → ℕ} (hp : PolyBound p) (h : ∀ n, q n ≤ p n) : PolyBound q :=
  let ⟨a, k, ha⟩ := hp; ⟨a, k, fun n => le_trans (h n) (ha n)⟩

/-- The length of the longest argument. -/
def maxLen (args : List Word) : ℕ := (args.map List.length).foldr max 0

@[simp] theorem maxLen_nil : maxLen [] = 0 := rfl

@[simp] theorem maxLen_cons (x : Word) (rest : List Word) :
    maxLen (x :: rest) = max x.length (maxLen rest) := rfl

theorem length_le_maxLen {x : Word} {args : List Word} (h : x ∈ args) : x.length ≤ maxLen args := by
  induction args with
  | nil => cases h
  | cons y ys ih =>
      rcases List.mem_cons.1 h with rfl | h'
      · simp
      · exact le_trans (ih h') (by simp)

theorem length_getD_le_maxLen (args : List Word) (i : ℕ) :
    (args.getD i []).length ≤ maxLen args := by
  by_cases h : i < args.length
  · exact length_le_maxLen (by
      rw [List.getD_eq_getElem _ _ h]
      exact List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem maxLen_tail_le (args : List Word) : maxLen args.tail ≤ maxLen args := by
  cases args with
  | nil => simp
  | cons x xs => simp

/-- A function on argument lists whose output length is polynomially bounded in the length of the
longest argument. -/
def PolyLen (F : List Word → Word) : Prop :=
  ∃ a k : ℕ, ∀ args, (F args).length ≤ a * (maxLen args + 1) ^ k

theorem maxLen_map_le {gs : List Cob} {args : List Word} {B : ℕ}
    (h : ∀ g ∈ gs, (g.eval args).length ≤ B) :
    maxLen (gs.map fun g => g.eval args) ≤ B := by
  induction gs with
  | nil => simp [maxLen]
  | cons g gs ih =>
      simp only [List.map_cons, maxLen_cons]
      exact max_le (h g (by simp)) (ih fun g' hg' => h g' (by simp [hg']))

/-- Monotonicity of the standard polynomial bound in all of its parameters. -/
theorem bound_mono {a k a' k' N N' : ℕ} (ha : a ≤ a') (hk : k ≤ k') (hN : N ≤ N') :
    a * (N + 1) ^ k ≤ a' * (N' + 1) ^ k' :=
  Nat.mul_le_mul ha
    (le_trans (Nat.pow_le_pow_left (by omega) k) (Nat.pow_le_pow_right (by omega) hk))

/-- Substituting a polynomially bounded quantity into a polynomial bound stays polynomial. -/
theorem bound_comp_le {a k b m M N : ℕ} (h : M ≤ b * (N + 1) ^ m) :
    a * (M + 1) ^ k ≤ a * (b + 1) ^ k * (N + 1) ^ (m * k) := by
  have hpow : 1 ≤ (N + 1) ^ m := Nat.one_le_pow _ _ (by omega)
  have h1 : M + 1 ≤ (b + 1) * (N + 1) ^ m := by nlinarith
  calc a * (M + 1) ^ k ≤ a * ((b + 1) * (N + 1) ^ m) ^ k :=
        Nat.mul_le_mul_left a (Nat.pow_le_pow_left h1 k)
    _ = a * (b + 1) ^ k * (N + 1) ^ (m * k) := by rw [mul_pow, ← pow_mul, mul_assoc]

theorem Cob.polyLen_aux : ∀ (n : ℕ) (c : Cob), sizeOf c ≤ n → PolyLen c.eval := by
  intro n
  induction n with
  | zero =>
      intro c hc
      exfalso
      cases c <;> simp at hc
  | succ n ih =>
      intro c hc
      match c with
      | .proj i =>
          refine ⟨1, 1, fun args => ?_⟩
          simp only [Cob.eval_proj, pow_one, one_mul]
          exact le_trans (length_getD_le_maxLen args i) (Nat.le_succ _)
      | .empty => exact ⟨0, 0, fun args => by simp⟩
      | .app b =>
          refine ⟨1, 1, fun args => ?_⟩
          simp only [Cob.eval_app, pow_one, one_mul, List.length_cons]
          have := length_getD_le_maxLen args 0
          omega
      | .smash =>
          refine ⟨1, 2, fun args => ?_⟩
          simp only [Cob.eval_smash, List.length_replicate, one_mul]
          have h0 := length_getD_le_maxLen args 0
          have h1 := length_getD_le_maxLen args 1
          calc (args.getD 0 []).length * (args.getD 1 []).length
              ≤ maxLen args * maxLen args := Nat.mul_le_mul h0 h1
            _ ≤ (maxLen args + 1) ^ 2 := by ring_nf; omega
      | .comp f gs =>
          have hf : sizeOf f ≤ n := by simp at hc; omega
          obtain ⟨af, kf, hafk⟩ := ih f hf
          have hsz : ∀ g ∈ gs, sizeOf g ≤ n := by
            intro g hg
            have h1 := List.sizeOf_lt_of_mem hg
            simp at hc
            omega
          have hgs : ∃ a k, ∀ g ∈ gs, ∀ args,
              (g.eval args).length ≤ a * (maxLen args + 1) ^ k := by
            clear hc hf hafk
            revert hsz
            induction gs with
            | nil => intro _; exact ⟨0, 0, by simp⟩
            | cons g gs ihg =>
                intro hsz
                obtain ⟨a1, k1, h1⟩ := ih g (hsz g (by simp))
                obtain ⟨a2, k2, h2⟩ := ihg (fun g' hg' => hsz g' (by simp [hg']))
                refine ⟨a1 + a2, max k1 k2, ?_⟩
                intro g' hg' args
                rcases List.mem_cons.1 hg' with rfl | hg''
                · exact le_trans (h1 args) (bound_mono (by omega) (le_max_left _ _) le_rfl)
                · exact le_trans (h2 g' hg'' args)
                    (bound_mono (by omega) (le_max_right _ _) le_rfl)
          obtain ⟨a, k, hgsb⟩ := hgs
          refine ⟨af * (a + 1) ^ kf, k * kf, fun args => ?_⟩
          have hM : maxLen (gs.map fun g => g.eval args) ≤ a * (maxLen args + 1) ^ k :=
            maxLen_map_le (fun g hg => hgsb g hg args)
          calc ((Cob.comp f gs).eval args).length
              = (f.eval (gs.map fun g => g.eval args)).length := by rw [Cob.eval_comp]
            _ ≤ af * (maxLen (gs.map fun g => g.eval args) + 1) ^ kf := hafk _
            _ ≤ af * (a + 1) ^ kf * (maxLen args + 1) ^ (k * kf) := bound_comp_le hM
      | .bRec g h₀ h₁ bd =>
          have hg : sizeOf g ≤ n := by simp at hc; omega
          have hbd : sizeOf bd ≤ n := by simp at hc; omega
          obtain ⟨ag, kg, hgb⟩ := ih g hg
          obtain ⟨ab, kb, hbb⟩ := ih bd hbd
          refine ⟨ag + ab, max kg kb, fun args => ?_⟩
          match args with
          | [] =>
              have hev : (Cob.bRec g h₀ h₁ bd).eval [] = g.eval [] := by
                rw [Cob.eval_bRec]; rfl
              rw [hev]
              exact le_trans (hgb []) (bound_mono (by omega) (le_max_left _ _) le_rfl)
          | [] :: rest =>
              rw [Cob.eval_bRec_nil]
              refine le_trans (hgb rest) (bound_mono (by omega) (le_max_left _ _) ?_)
              simp
          | (b :: x) :: rest =>
              rw [Cob.eval_bRec_cons]
              refine le_trans (le_trans (le_of_eq (List.length_take ..)) (min_le_left _ _)) ?_
              exact le_trans (hbb ((b :: x) :: rest))
                (bound_mono (by omega) (le_max_right _ _) le_rfl)

/-- **Cobham functions have polynomially bounded output length.** -/
theorem Cob.polyLen (c : Cob) : PolyLen c.eval := Cob.polyLen_aux (sizeOf c) c le_rfl

/-! ### The classes `P` and `NP` -/

/-- A language over binary words. -/
abbrev Language := Word → Prop

/-- `L` is in `P`: some polynomial-time function decides it, "accept" meaning a nonempty
output. -/
def InP (L : Language) : Prop := ∃ c : Cob, ∀ x, (L x ↔ c.eval [x] ≠ [])

/-- `L` is in `NP`: some polynomial-time verifier accepts `(x, w)` only for witnesses `w` of
polynomially bounded length, and `x ∈ L` exactly when some witness is accepted. -/
def InNP (L : Language) : Prop :=
  ∃ (v : Cob) (p : ℕ → ℕ), PolyBound p ∧ Monotone p ∧
    (∀ x w, v.eval [x, w] ≠ [] → w.length ≤ p x.length) ∧
    (∀ x, L x ↔ ∃ w, v.eval [x, w] ≠ [])

/-- Polynomial-time many-one reducibility. -/
def PolyManyOne (L₁ L₂ : Language) : Prop := ∃ r : Cob, ∀ x, (L₁ x ↔ L₂ (r.eval [x]))

@[inherit_doc] scoped infix:50 " ≤ₘᵖ " => PolyManyOne

/-- `L` is NP-hard: every language in `NP` reduces to it in polynomial time. -/
def NPHard (L : Language) : Prop := ∀ L' : Language, InNP L' → L' ≤ₘᵖ L

/-- `L` is NP-complete. -/
def NPComplete (L : Language) : Prop := InNP L ∧ NPHard L

/-- The statement `P = NP`. -/
def PeqNP : Prop := ∀ L : Language, InNP L → InP L

/-! ### Basic structural results -/

/-- **`P ⊆ NP`.** -/
theorem inNP_of_inP {L : Language} (h : InP L) : InNP L := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp .andC [.comp c [.proj 0], .comp .notC [.proj 1]], fun _ => 0,
    polyBound_const 0, monotone_const, ?_, ?_⟩
  · intro x w hacc
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, Cob.eval_andC,
      Cob.eval_notC] at hacc
    by_cases hx : c.eval [x] = []
    · simp [hx] at hacc
    · by_cases hw : w = []
      · simp [hw]
      · simp [hx, hw] at hacc
  · intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, Cob.eval_andC,
      Cob.eval_notC]
    constructor
    · intro hx
      refine ⟨[], ?_⟩
      have : c.eval [x] ≠ [] := (hc x).1 hx
      simp [this]
    · rintro ⟨w, hw⟩
      by_cases hx : c.eval [x] = []
      · simp [hx] at hw
      · exact (hc x).2 hx

theorem polyManyOne_refl (L : Language) : L ≤ₘᵖ L := ⟨.proj 0, fun x => by simp⟩

theorem polyManyOne_trans {L₁ L₂ L₃ : Language} (h₁ : L₁ ≤ₘᵖ L₂) (h₂ : L₂ ≤ₘᵖ L₃) :
    L₁ ≤ₘᵖ L₃ := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨.comp r₂ [.comp r₁ [.proj 0]], fun x => by simpa using (hr₁ x).trans (hr₂ _)⟩

/-- **`P` is closed downwards under `≤ₘᵖ`.** -/
theorem InP.of_reduction {L₁ L₂ : Language} (hred : L₁ ≤ₘᵖ L₂) (h : InP L₂) : InP L₁ := by
  obtain ⟨r, hr⟩ := hred
  obtain ⟨c, hc⟩ := h
  exact ⟨.comp c [.comp r [.proj 0]], fun x => by simpa using (hr x).trans (hc _)⟩

/-- **`NP` is closed downwards under `≤ₘᵖ`.** -/
theorem InNP.of_reduction {L₁ L₂ : Language} (hred : L₁ ≤ₘᵖ L₂) (h : InNP L₂) : InNP L₁ := by
  obtain ⟨r, hr⟩ := hred
  obtain ⟨v, p, hpoly, hmono, hbound, hchar⟩ := h
  obtain ⟨b, k, hrb⟩ := r.polyLen
  set q : ℕ → ℕ := fun n => b * (n + 1) ^ k with hq
  have hrlen : ∀ x : Word, (r.eval [x]).length ≤ q x.length := by
    intro x
    have := hrb [x]
    simpa [hq, maxLen] using this
  have hqmono : Monotone q := by
    intro m n hmn
    exact Nat.mul_le_mul_left b (Nat.pow_le_pow_left (by omega) k)
  have hqpoly : PolyBound q := ⟨b, k, fun _ => le_rfl⟩
  have hev : ∀ x w : Word,
      (Cob.comp v [Cob.comp r [Cob.proj 0], Cob.proj 1]).eval [x, w] = v.eval [r.eval [x], w] := by
    intro x w
    simp
  refine ⟨.comp v [.comp r [.proj 0], .proj 1], fun n => p (q n), hpoly.comp hqpoly,
    hmono.comp hqmono, ?_, ?_⟩
  · intro x w hacc
    rw [hev] at hacc
    exact le_trans (hbound _ w hacc) (hmono (hrlen x))
  · intro x
    rw [hr x, hchar (r.eval [x])]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [hev]; exact hw⟩
    · rintro ⟨w, hw⟩
      rw [hev] at hw
      exact ⟨w, hw⟩

/-- Reductions transport NP-hardness. -/
theorem NPHard.of_reduction {L L' : Language} (h : NPHard L) (hred : L ≤ₘᵖ L') : NPHard L' :=
  fun L'' hL'' => polyManyOne_trans (h L'' hL'') hred

/-- **If some NP-complete language is in `P`, then `P = NP`.** -/
theorem peqNP_of_npComplete_of_inP {L : Language} (hc : NPComplete L) (hP : InP L) : PeqNP :=
  fun L' hL' => InP.of_reduction (hc.2 L' hL') hP

/-- Conversely, if `P = NP` then every NP-complete language is in `P`. -/
theorem inP_of_peqNP {L : Language} (h : PeqNP) (hc : NPComplete L) : InP L := h L hc.1

/-! ### Non-vacuity -/

theorem inP_univ : InP (fun _ => True) := ⟨.trueC, fun x => by simp⟩

theorem inP_empty : InP (fun _ => False) := ⟨.empty, fun x => by simp⟩

/-- The language of nonempty words is in `P`. -/
theorem inP_nonempty : InP (fun x => x ≠ []) := ⟨.proj 0, fun x => by simp⟩

/-- **`P` is closed under complement.** -/
theorem InP.compl {L : Language} (h : InP L) : InP (fun x => ¬ L x) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp .notC [.comp c [.proj 0]], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, Cob.eval_notC]
  by_cases hx : c.eval [x] = []
  · simp [hx, (hc x)]
  · simp [hx, (hc x)]

/-- **`P` is closed under intersection.** -/
theorem InP.inter {L₁ L₂ : Language} (h₁ : InP L₁) (h₂ : InP L₂) :
    InP (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨.comp .andC [.comp c₁ [.proj 0], .comp c₂ [.proj 0]], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, Cob.eval_andC]
  by_cases h : c₁.eval [x] = []
  · simp [h, (hc₁ x)]
  · simp [h, (hc₁ x), (hc₂ x)]

/-- **`P` is closed under union.** -/
theorem InP.union {L₁ L₂ : Language} (h₁ : InP L₁) (h₂ : InP L₂) :
    InP (fun x => L₁ x ∨ L₂ x) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨.comp .orC [.comp c₁ [.proj 0], .comp c₂ [.proj 0]], fun x => ?_⟩
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, Cob.eval_orC]
  by_cases h : c₁.eval [x] = []
  · simp [h, (hc₁ x), (hc₂ x)]
  · simp [h, (hc₁ x)]

/-- **`NP` is closed under union.**  The witness carries a tag bit saying which of the two
verifiers to run. -/
theorem InNP.union {L₁ L₂ : Language} (h₁ : InNP L₁) (h₂ : InNP L₂) :
    InNP (fun x => L₁ x ∨ L₂ x) := by
  obtain ⟨v₁, p₁, hpoly₁, hmono₁, hbound₁, hchar₁⟩ := h₁
  obtain ⟨v₂, p₂, hpoly₂, hmono₂, hbound₂, hchar₂⟩ := h₂
  set head : Cob := .comp .headTrue [.proj 1] with hhead
  set tl : Cob := .comp .tailC [.proj 1] with htl
  set v : Cob := .comp .orC
    [.comp .andC [head, .comp v₁ [.proj 0, tl]],
     .comp .andC [.comp .notC [head], .comp v₂ [.proj 0, tl]]] with hv
  have hacc_true : ∀ (x w' : Word),
      (v.eval [x, Bool.true :: w'] ≠ []) ↔ (v₁.eval [x, w'] ≠ []) := by
    intro x w'
    simp only [hv, hhead, htl, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, Cob.eval_headTrue, Cob.eval_tailC,
      Cob.eval_notC, Cob.eval_andC, Cob.eval_orC]
    by_cases h : v₁.eval [x, w'] = [] <;> simp [h]
  have hacc_false : ∀ (x w : Word), w.headD Bool.false = Bool.false →
      ((v.eval [x, w] ≠ []) ↔ (v₂.eval [x, w.tail] ≠ [])) := by
    intro x w hw
    simp only [hv, hhead, htl, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, Cob.eval_headTrue, Cob.eval_tailC,
      Cob.eval_notC, Cob.eval_andC, Cob.eval_orC, hw]
    by_cases h : v₂.eval [x, w.tail] = [] <;> simp [h]
  refine ⟨v, fun n => p₁ n + p₂ n + 1, (hpoly₁.add hpoly₂).add (polyBound_const 1),
    fun m n hmn => by simp only; have := hmono₁ hmn; have := hmono₂ hmn; omega, ?_, ?_⟩
  · intro x w hacc
    cases w with
    | nil => simp
    | cons b w' =>
        cases b with
        | true =>
            have := hbound₁ x w' ((hacc_true x w').1 hacc)
            simp only [List.length_cons]
            omega
        | false =>
            have := hbound₂ x w' ((hacc_false x (Bool.false :: w') rfl).1 hacc)
            simp only [List.length_cons]
            omega
  · intro x
    constructor
    · rintro (hx | hx)
      · obtain ⟨w', hw'⟩ := (hchar₁ x).1 hx
        exact ⟨Bool.true :: w', (hacc_true x w').2 hw'⟩
      · obtain ⟨w', hw'⟩ := (hchar₂ x).1 hx
        exact ⟨Bool.false :: w', (hacc_false x (Bool.false :: w') rfl).2 hw'⟩
    · rintro ⟨w, hw⟩
      cases w with
      | nil =>
          exact Or.inr ((hchar₂ x).2 ⟨[], (hacc_false x [] rfl).1 hw⟩)
      | cons b w' =>
          cases b with
          | true => exact Or.inl ((hchar₁ x).2 ⟨w', (hacc_true x w').1 hw⟩)
          | false =>
              exact Or.inr ((hchar₂ x).2 ⟨w', (hacc_false x (Bool.false :: w') rfl).1 hw⟩)

/-! ### Brute-force search

An `NP` language is decided by exhaustive search over the (finitely many) witnesses of bounded
length. -/

/-- All words of length exactly `n`. -/
def wordsOfLen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).flatMap fun w => [Bool.false :: w, Bool.true :: w]

theorem mem_wordsOfLen : ∀ (n : ℕ) (w : Word), w ∈ wordsOfLen n ↔ w.length = n := by
  intro n
  induction n with
  | zero => intro w; simp [wordsOfLen]
  | succ n ih =>
      intro w
      simp only [wordsOfLen, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨u, hu, rfl | rfl⟩ <;> simp [(ih u).1 hu]
      · intro hlen
        cases w with
        | nil => simp at hlen
        | cons b x =>
            refine ⟨x, (ih x).2 (by simpa using hlen), ?_⟩
            cases b <;> simp

/-- All words of length at most `n`. -/
def wordsUpTo (n : ℕ) : List Word := (List.range (n + 1)).flatMap wordsOfLen

theorem mem_wordsUpTo (n : ℕ) (w : Word) : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  simp only [wordsUpTo, List.mem_flatMap, List.mem_range, mem_wordsOfLen]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨w.length, by omega, rfl⟩

/-- The exhaustive-search decision procedure attached to a verifier and a witness bound: try
every witness of length at most `p |x|`. -/
def bruteForce (v : Cob) (p : ℕ → ℕ) (x : Word) : Bool :=
  (wordsUpTo (p x.length)).any fun w => !(v.eval [x, w]).isEmpty

/-- **An `NP` language is decided by exhaustive search over the witnesses of bounded length.**
The decision procedure `bruteForce v p` is an explicit total function on words — it runs in
exponential time, which is why this does not put `NP` inside `P`. -/
theorem bruteForce_decides {L : Language} (h : InNP L) :
    ∃ (v : Cob) (p : ℕ → ℕ), PolyBound p ∧ ∀ x, (L x ↔ bruteForce v p x = Bool.true) := by
  obtain ⟨v, p, hpoly, -, hbound, hchar⟩ := h
  refine ⟨v, p, hpoly, fun x => ?_⟩
  rw [hchar x, bruteForce, List.any_eq_true]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (mem_wordsUpTo _ _).2 (hbound x w hw), by simpa [List.isEmpty_iff] using hw⟩
  · rintro ⟨w, -, hw⟩
    exact ⟨w, by simpa [List.isEmpty_iff] using hw⟩

/-! ### Boundary

What is **not** here:

* Cobham's theorem, i.e. that `Cob` denotes exactly the functions computable by a Turing machine
  in polynomial time.  The class is *defined* by the Cobham axioms, so "polynomial time" is used
  here in that sense; nothing below depends on the machine characterization.
* Cook–Levin.  No language is proved NP-complete here: that needs an encoding of Boolean formulas
  as words together with a polynomial-time simulation of a nondeterministic machine by a formula,
  and is a much larger undertaking.
* Consequently `NPHard` is not shown to be inhabited, and `PeqNP` is neither proved nor refuted —
  the results above are the structural theory that a proof of Cook–Levin would plug into.
* No link is made to `Mathlib`'s `Computable`: `Cob.eval` is a total Lean function, but it is not
  proved to be computable in the sense of `Mathlib.Computability`, so nothing here is stated in
  terms of `Computable` or `Partrec`.  (Statements of the form "languages in `P` are decidable"
  would in any case be vacuous in Lean, since `Nonempty (DecidablePred L)` holds classically for
  every `L`; that is why `bruteForce` is given as an explicit function instead.)
-/

end Complexity
