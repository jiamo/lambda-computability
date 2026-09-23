/-
**Polynomial time relative to an oracle.**

Polynomial time is Cobham's class in this library (`Start/ComplexityClasses.lean`): a syntax
whose closure under composition is a constructor rather than a theorem.  Relativizing it means
adding one constructor, `CobQ.query`, which asks the oracle about the first argument and answers
with the truth value `[true]` / `[]`.  A term of `CobQ` therefore denotes, for each oracle `A`, a
function `List Word → Word`; this is the "polynomial-time machine with an oracle tape" of the
relativized classes.

What a diagonalization against such machines needs is not only the value but the *queries*: the
evaluation is therefore given by `CobQ.run`, which returns the value together with the list of
words the oracle was asked about, in the order in which they were asked.  The three facts that
make the class behave like a relativized polynomial-time class are proved here, all with
constants that do not depend on the oracle:

* `Complexity.CobQ.polyLen` — the output length is polynomially bounded;
* `Complexity.CobQ.polyQueryCount` — the **number** of queries is polynomially bounded;
* `Complexity.CobQ.polyQueryLen` — every queried word is polynomially long;
* `Complexity.CobQ.run_congr` — the **use principle**: two oracles that agree on the words
  actually queried give the same run, hence the same value.

Together with `Complexity.CobQ.ofCob` (an unrelativized Cobham function is an oracle function
that asks nothing) and `Complexity.CobQ.erase` (the empty oracle gives back an unrelativized
Cobham function) these are exactly the ingredients of the Baker–Gill–Solovay constructions.
-/

import Mathlib
import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-- An oracle: a language of binary words, given by its characteristic function. -/
abbrev Oracle := Word → Bool

/-- Cobham's syntax with one extra constructor: `query` asks the oracle about the first
argument. -/
inductive CobQ : Type
  /-- The `i`-th argument. -/
  | proj (i : ℕ)
  /-- The constant empty word. -/
  | empty
  /-- The successor function `x ↦ b :: x` on the first argument. -/
  | app (b : Bool)
  /-- The smash function `x # y = 1^{|x|·|y|}` on the first two arguments. -/
  | smash
  /-- Composition. -/
  | comp (f : CobQ) (gs : List CobQ)
  /-- Bounded recursion on notation over the first argument. -/
  | bRec (g h₀ h₁ bd : CobQ)
  /-- The oracle query on the first argument. -/
  | query
  deriving Inhabited

namespace CobQ

/-- The evaluation of an oracle Cobham term: the value together with the list of words the
oracle was asked about.  The value clauses are those of `Complexity.Cob.eval`; `query` answers
`[true]` when the first argument belongs to the oracle and `[]` otherwise. -/
def run (A : Oracle) : CobQ → List Word → Word × List Word
  | .proj i, args => (args.getD i [], [])
  | .empty, _ => ([], [])
  | .app b, args => (b :: args.getD 0 [], [])
  | .smash, args =>
      (List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true, [])
  | .query, args => ((if A (args.getD 0 []) then [Bool.true] else []), [args.getD 0 []])
  | .comp f gs, args =>
      let rs := gs.attach.map (fun g => run A g.1 args)
      let r := run A f (rs.map Prod.fst)
      (r.1, rs.flatMap Prod.snd ++ r.2)
  | .bRec g h₀ h₁ bd, args =>
      List.rec (run A g args.tail)
        (fun b x' ih =>
          let rb := run A bd ((b :: x') :: args.tail)
          let rh :=
            if b then run A h₁ (x' :: ih.1 :: args.tail)
            else run A h₀ (x' :: ih.1 :: args.tail)
          (rh.1.take rb.1.length, ih.2 ++ rb.2 ++ rh.2))
        (args.headD [])
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    · have := List.sizeOf_lt_of_mem g.2; omega
    all_goals omega

/-- The value computed by an oracle Cobham term. -/
def eval (A : Oracle) (t : CobQ) (args : List Word) : Word := (run A t args).1

/-- The words the oracle was asked about, in order. -/
def queries (A : Oracle) (t : CobQ) (args : List Word) : List Word := (run A t args).2

@[simp] theorem run_proj (A : Oracle) (i : ℕ) (args : List Word) :
    run A (.proj i) args = (args.getD i [], []) := by rw [run]

@[simp] theorem run_empty (A : Oracle) (args : List Word) :
    run A .empty args = ([], []) := by rw [run]

@[simp] theorem run_app (A : Oracle) (b : Bool) (args : List Word) :
    run A (.app b) args = (b :: args.getD 0 [], []) := by rw [run]

@[simp] theorem run_smash (A : Oracle) (args : List Word) :
    run A .smash args =
      (List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true, []) := by
  rw [run]

@[simp] theorem run_query (A : Oracle) (args : List Word) :
    run A .query args =
      ((if A (args.getD 0 []) then [Bool.true] else []), [args.getD 0 []]) := by
  rw [run]

theorem run_comp (A : Oracle) (f : CobQ) (gs : List CobQ) (args : List Word) :
    run A (.comp f gs) args =
      ((run A f (gs.map fun g => eval A g args)).1,
        (gs.map fun g => queries A g args).flatten ++ (run A f (gs.map fun g => eval A g args)).2)
    := by
  rw [run]
  have hmap : (gs.attach.map (fun g => run A g.1 args)).map Prod.fst
      = gs.map fun g => eval A g args := by
    simp [List.map_map, eval, Function.comp_def]
  have hflat : (gs.attach.map (fun g => run A g.1 args)).flatMap Prod.snd
      = (gs.map fun g => queries A g args).flatten := by
    simp [List.flatMap_def, List.map_map, queries, Function.comp_def]
  simp only [hmap, hflat]

theorem run_bRec (A : Oracle) (g h₀ h₁ bd : CobQ) (args : List Word) :
    run A (.bRec g h₀ h₁ bd) args =
      List.rec (run A g args.tail)
        (fun b x' ih =>
          let rb := run A bd ((b :: x') :: args.tail)
          let rh :=
            if b then run A h₁ (x' :: ih.1 :: args.tail)
            else run A h₀ (x' :: ih.1 :: args.tail)
          (rh.1.take rb.1.length, ih.2 ++ rb.2 ++ rh.2))
        (args.headD []) := by
  rw [run]

@[simp] theorem run_bRec_nil (A : Oracle) (g h₀ h₁ bd : CobQ) (rest : List Word) :
    run A (.bRec g h₀ h₁ bd) ([] :: rest) = run A g rest := by
  rw [run_bRec]; rfl

theorem run_bRec_cons (A : Oracle) (g h₀ h₁ bd : CobQ) (b : Bool) (x : Word)
    (rest : List Word) :
    run A (.bRec g h₀ h₁ bd) ((b :: x) :: rest) =
      (let ih := run A (.bRec g h₀ h₁ bd) (x :: rest)
       let rb := run A bd ((b :: x) :: rest)
       let rh :=
         if b then run A h₁ (x :: ih.1 :: rest) else run A h₀ (x :: ih.1 :: rest)
       (rh.1.take rb.1.length, ih.2 ++ rb.2 ++ rh.2)) := by
  rw [run_bRec, run_bRec]; rfl

/-! ### The value alone -/

@[simp] theorem eval_proj (A : Oracle) (i : ℕ) (args : List Word) :
    eval A (.proj i) args = args.getD i [] := by simp [eval]

@[simp] theorem eval_empty (A : Oracle) (args : List Word) : eval A .empty args = [] := by
  simp [eval]

@[simp] theorem eval_app (A : Oracle) (b : Bool) (args : List Word) :
    eval A (.app b) args = b :: args.getD 0 [] := by simp [eval]

@[simp] theorem eval_smash (A : Oracle) (args : List Word) :
    eval A .smash args =
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true := by simp [eval]

@[simp] theorem eval_query (A : Oracle) (args : List Word) :
    eval A .query args = if A (args.getD 0 []) then [Bool.true] else [] := by simp [eval]

@[simp] theorem eval_comp (A : Oracle) (f : CobQ) (gs : List CobQ) (args : List Word) :
    eval A (.comp f gs) args = eval A f (gs.map fun g => eval A g args) := by
  simp [eval, run_comp]

@[simp] theorem eval_bRec_nil (A : Oracle) (g h₀ h₁ bd : CobQ) (rest : List Word) :
    eval A (.bRec g h₀ h₁ bd) ([] :: rest) = eval A g rest := by simp [eval]

theorem eval_bRec_cons (A : Oracle) (g h₀ h₁ bd : CobQ) (b : Bool) (x : Word)
    (rest : List Word) :
    eval A (.bRec g h₀ h₁ bd) ((b :: x) :: rest) =
      (if b then eval A h₁ (x :: eval A (.bRec g h₀ h₁ bd) (x :: rest) :: rest)
        else eval A h₀ (x :: eval A (.bRec g h₀ h₁ bd) (x :: rest) :: rest)).take
        (eval A bd ((b :: x) :: rest)).length := by
  rw [eval, run_bRec_cons]
  cases b <;> simp [eval]

/-! ### The queries alone -/

@[simp] theorem queries_proj (A : Oracle) (i : ℕ) (args : List Word) :
    queries A (.proj i) args = [] := by simp [queries]

@[simp] theorem queries_empty (A : Oracle) (args : List Word) :
    queries A .empty args = [] := by simp [queries]

@[simp] theorem queries_app (A : Oracle) (b : Bool) (args : List Word) :
    queries A (.app b) args = [] := by simp [queries]

@[simp] theorem queries_smash (A : Oracle) (args : List Word) :
    queries A .smash args = [] := by simp [queries]

@[simp] theorem queries_query (A : Oracle) (args : List Word) :
    queries A .query args = [args.getD 0 []] := by simp [queries]

theorem queries_comp (A : Oracle) (f : CobQ) (gs : List CobQ) (args : List Word) :
    queries A (.comp f gs) args =
      (gs.map fun g => queries A g args).flatten ++
        queries A f (gs.map fun g => eval A g args) := by
  simp [queries, run_comp]

@[simp] theorem queries_bRec_nil (A : Oracle) (g h₀ h₁ bd : CobQ) (rest : List Word) :
    queries A (.bRec g h₀ h₁ bd) ([] :: rest) = queries A g rest := by simp [queries]

theorem queries_bRec_cons (A : Oracle) (g h₀ h₁ bd : CobQ) (b : Bool) (x : Word)
    (rest : List Word) :
    queries A (.bRec g h₀ h₁ bd) ((b :: x) :: rest) =
      queries A (.bRec g h₀ h₁ bd) (x :: rest) ++ queries A bd ((b :: x) :: rest) ++
        (if b then queries A h₁ (x :: eval A (.bRec g h₀ h₁ bd) (x :: rest) :: rest)
          else queries A h₀ (x :: eval A (.bRec g h₀ h₁ bd) (x :: rest) :: rest)) := by
  rw [queries, run_bRec_cons]
  cases b <;> simp [queries, eval]

@[simp] theorem run_bRec_args_nil (A : Oracle) (g h₀ h₁ bd : CobQ) :
    run A (.bRec g h₀ h₁ bd) [] = run A g [] := by
  rw [run_bRec]; rfl

end CobQ

/-! ### Monotone polynomial bounds -/

/-- A monotone polynomial bound; the bounds of this file are all of this shape, which makes them
closed under the operations used in the induction over a term. -/
def PolyMono (p : ℕ → ℕ) : Prop := PolyBound p ∧ Monotone p

theorem polyMono_const (c : ℕ) : PolyMono (fun _ => c) := ⟨polyBound_const c, monotone_const⟩

theorem polyMono_id : PolyMono (fun N => N) :=
  ⟨⟨1, 1, fun n => by simp⟩, fun _ _ h => h⟩

theorem polyMono_succ : PolyMono (fun N => N + 1) :=
  ⟨⟨1, 1, fun n => by simp⟩, fun _ _ h => Nat.add_le_add_right h 1⟩

theorem PolyMono.add {p q : ℕ → ℕ} (hp : PolyMono p) (hq : PolyMono q) :
    PolyMono (fun N => p N + q N) :=
  ⟨hp.1.add hq.1, fun _ _ h => Nat.add_le_add (hp.2 h) (hq.2 h)⟩

theorem PolyMono.mul {p q : ℕ → ℕ} (hp : PolyMono p) (hq : PolyMono q) :
    PolyMono (fun N => p N * q N) := by
  refine ⟨?_, fun _ _ h => Nat.mul_le_mul (hp.2 h) (hq.2 h)⟩
  obtain ⟨a, k, ha⟩ := hp.1
  obtain ⟨b, m, hb⟩ := hq.1
  refine ⟨a * b, k + m, fun n => ?_⟩
  calc p n * q n ≤ (a * (n + 1) ^ k) * (b * (n + 1) ^ m) := Nat.mul_le_mul (ha n) (hb n)
    _ = a * b * (n + 1) ^ (k + m) := by rw [pow_add]; ring

theorem PolyMono.comp {p q : ℕ → ℕ} (hp : PolyMono p) (hq : PolyMono q) :
    PolyMono (fun N => p (q N)) :=
  ⟨hp.1.comp hq.1, fun _ _ h => hp.2 (hq.2 h)⟩

namespace CobQ

/-! ### The uniform polynomial bounds -/

/-- The three quantities of an oracle Cobham term that a diagonalization needs to control: the
length of the value, the number of queries and the length of every query.  All three are bounded
by one monotone polynomial in the length of the longest argument, and the bound does not depend
on the oracle. -/
def Bounded (t : CobQ) : Prop :=
  ∃ p : ℕ → ℕ, PolyMono p ∧ ∀ (A : Oracle) (args : List Word),
    (eval A t args).length ≤ p (maxLen args) ∧
      (queries A t args).length ≤ p (maxLen args) ∧
      ∀ w ∈ queries A t args, w.length ≤ p (maxLen args)

/-- A bound on every entry of a list of words bounds the length of the longest one. -/
theorem maxLen_le_of_forall {l : List Word} {B : ℕ} (h : ∀ u ∈ l, u.length ≤ B) :
    maxLen l ≤ B := by
  induction l with
  | nil => simp [maxLen]
  | cons u t ih =>
      simp only [maxLen_cons]
      exact max_le (h u (by simp)) (ih fun u' hu' => h u' (by simp [hu']))

/-- A bound valid for every term of a list. -/
theorem exists_bounded_list {gs : List CobQ} (h : ∀ g ∈ gs, Bounded g) :
    ∃ p : ℕ → ℕ, PolyMono p ∧ ∀ g ∈ gs, ∀ (A : Oracle) (args : List Word),
      (eval A g args).length ≤ p (maxLen args) ∧
        (queries A g args).length ≤ p (maxLen args) ∧
        ∀ w ∈ queries A g args, w.length ≤ p (maxLen args) := by
  induction gs with
  | nil => exact ⟨fun _ => 0, polyMono_const 0, by simp⟩
  | cons g gs ih =>
      obtain ⟨p, hp, hpg⟩ := h g (by simp)
      obtain ⟨q, hq, hqs⟩ := ih fun g' hg' => h g' (by simp [hg'])
      refine ⟨fun N => p N + q N, hp.add hq, ?_⟩
      intro g' hg' A args
      dsimp only
      rcases List.mem_cons.1 hg' with rfl | hg''
      · obtain ⟨h1, h2, h3⟩ := hpg A args
        exact ⟨by omega, by omega, fun w hw => by have := h3 w hw; omega⟩
      · obtain ⟨h1, h2, h3⟩ := hqs g' hg'' A args
        exact ⟨by omega, by omega, fun w hw => by have := h3 w hw; omega⟩

theorem length_flatten_le {l : List (List Word)} {B : ℕ} (h : ∀ u ∈ l, u.length ≤ B) :
    l.flatten.length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons u t ih =>
      have h1 : u.length ≤ B := h u (by simp)
      have h2 : t.flatten.length ≤ t.length * B := ih fun u' hu' => h u' (by simp [hu'])
      simp only [List.flatten_cons, List.length_append, List.length_cons]
      have : (t.length + 1) * B = t.length * B + B := by ring
      omega

/-- The step of the induction for `bRec`: with the bounds of the four subterms in hand, the
value, the number of queries and the length of the queries of the bounded recursion are
controlled along the recursion. -/
theorem bRec_bounds {g h₀ h₁ bd : CobQ} {pg ph pbd : ℕ → ℕ}
    (hpg : Monotone pg) (hph : Monotone ph) (hpbd : Monotone pbd)
    (hg : ∀ (A : Oracle) (args : List Word),
      (eval A g args).length ≤ pg (maxLen args) ∧
        (queries A g args).length ≤ pg (maxLen args) ∧
        ∀ w ∈ queries A g args, w.length ≤ pg (maxLen args))
    (hh : ∀ (A : Oracle) (args : List Word),
      ((eval A h₀ args).length ≤ ph (maxLen args) ∧
        (queries A h₀ args).length ≤ ph (maxLen args) ∧
        ∀ w ∈ queries A h₀ args, w.length ≤ ph (maxLen args)) ∧
      ((eval A h₁ args).length ≤ ph (maxLen args) ∧
        (queries A h₁ args).length ≤ ph (maxLen args) ∧
        ∀ w ∈ queries A h₁ args, w.length ≤ ph (maxLen args)))
    (hbd : ∀ (A : Oracle) (args : List Word),
      (eval A bd args).length ≤ pbd (maxLen args) ∧
        (queries A bd args).length ≤ pbd (maxLen args) ∧
        ∀ w ∈ queries A bd args, w.length ≤ pbd (maxLen args))
    (A : Oracle) (N : ℕ) (rest : List Word) :
    ∀ x : Word, maxLen (x :: rest) ≤ N →
      (eval A (.bRec g h₀ h₁ bd) (x :: rest)).length ≤ pg N + pbd N ∧
        (queries A (.bRec g h₀ h₁ bd) (x :: rest)).length ≤
          pg N + x.length * (pbd N + ph (N + (pg N + pbd N))) ∧
        ∀ w ∈ queries A (.bRec g h₀ h₁ bd) (x :: rest),
          w.length ≤ pg N + pbd N + ph (N + (pg N + pbd N)) := by
  intro x
  induction x with
  | nil =>
      intro hN
      have hrest : maxLen rest ≤ N := le_trans (by simp) hN
      obtain ⟨h1, h2, h3⟩ := hg A rest
      have hmono : pg (maxLen rest) ≤ pg N := hpg hrest
      refine ⟨?_, ?_, ?_⟩
      · simpa using le_trans h1 (by omega)
      · simpa using le_trans h2 (by omega)
      · intro w hw
        simp only [queries_bRec_nil] at hw
        have := h3 w hw
        omega
  | cons b x ih =>
      intro hN
      have hsub : maxLen (x :: rest) ≤ N := by
        have h1 : maxLen (x :: rest) ≤ maxLen ((b :: x) :: rest) := by
          simp only [maxLen_cons, List.length_cons]
          exact max_le_max (by omega) le_rfl
        omega
      obtain ⟨ih1, ih2, ih3⟩ := ih hsub
      obtain ⟨hb1, hb2, hb3⟩ := hbd A ((b :: x) :: rest)
      set v : Word := eval A (.bRec g h₀ h₁ bd) (x :: rest) with hv
      have hargs : maxLen (x :: v :: rest) ≤ N + (pg N + pbd N) := by
        have hx : x.length ≤ N := by
          have : x.length ≤ maxLen (x :: rest) := by simp
          omega
        have hr : maxLen rest ≤ N := by
          have : maxLen rest ≤ maxLen (x :: rest) := by simp
          omega
        simp only [maxLen_cons]
        exact max_le (by omega) (max_le (by omega) (by omega))
      have hbdN : pbd (maxLen ((b :: x) :: rest)) ≤ pbd N := hpbd hN
      have hhN : ph (maxLen (x :: v :: rest)) ≤ ph (N + (pg N + pbd N)) := hph hargs
      obtain ⟨hh0, hh1⟩ := hh A (x :: v :: rest)
      refine ⟨?_, ?_, ?_⟩
      · rw [eval_bRec_cons]
        calc ((if b then eval A h₁ (x :: v :: rest) else eval A h₀ (x :: v :: rest)).take
              (eval A bd ((b :: x) :: rest)).length).length
            ≤ (eval A bd ((b :: x) :: rest)).length := by
              simp
          _ ≤ pbd N := le_trans hb1 hbdN
          _ ≤ pg N + pbd N := by omega
      · rw [queries_bRec_cons, ← hv]
        have hhcount :
            (if b then queries A h₁ (x :: v :: rest) else queries A h₀ (x :: v :: rest)).length
              ≤ ph (N + (pg N + pbd N)) := by
          cases b
          · simpa using le_trans hh0.2.1 hhN
          · simpa using le_trans hh1.2.1 hhN
        simp only [List.length_append]
        have hbc : (queries A bd ((b :: x) :: rest)).length ≤ pbd N := le_trans hb2 hbdN
        simp only [List.length_cons]
        have hstep : (x.length + 1) * (pbd N + ph (N + (pg N + pbd N)))
            = x.length * (pbd N + ph (N + (pg N + pbd N)))
              + (pbd N + ph (N + (pg N + pbd N))) := by ring
        omega
      · intro w hw
        rw [queries_bRec_cons, ← hv] at hw
        rcases List.mem_append.1 hw with hw' | hw'
        · rcases List.mem_append.1 hw' with hw'' | hw''
          · have := ih3 w hw''
            omega
          · have := hb3 w hw''
            have : w.length ≤ pbd N := le_trans this hbdN
            omega
        · have : w.length ≤ ph (N + (pg N + pbd N)) := by
            cases b
            · exact le_trans (hh0.2.2 w hw') hhN
            · exact le_trans (hh1.2.2 w hw') hhN
          omega

theorem bounded_aux : ∀ (n : ℕ) (t : CobQ), sizeOf t ≤ n → Bounded t := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      cases t <;> simp at ht
  | succ n ih =>
      intro t ht
      match t with
      | .proj i =>
          refine ⟨fun N => N + 1, polyMono_succ, ?_⟩
          intro A args
          dsimp only
          refine ⟨?_, by simp, by simp⟩
          simpa using le_trans (length_getD_le_maxLen args i) (Nat.le_succ _)
      | .empty =>
          refine ⟨fun _ => 0, polyMono_const 0, ?_⟩
          intro A args
          dsimp only
          simp
      | .app b =>
          refine ⟨fun N => N + 1, polyMono_succ, ?_⟩
          intro A args
          dsimp only
          refine ⟨?_, by simp, by simp⟩
          have := length_getD_le_maxLen args 0
          simp only [eval_app, List.length_cons]
          omega
      | .smash =>
          refine ⟨fun N => (N + 1) * (N + 1), polyMono_succ.mul polyMono_succ, ?_⟩
          intro A args
          dsimp only
          refine ⟨?_, by simp, by simp⟩
          have h0 := length_getD_le_maxLen args 0
          have h1 := length_getD_le_maxLen args 1
          simp only [eval_smash, List.length_replicate]
          exact le_trans (Nat.mul_le_mul h0 h1) (Nat.mul_le_mul (by omega) (by omega))
      | .query =>
          refine ⟨fun N => N + 1, polyMono_succ, ?_⟩
          intro A args
          dsimp only
          refine ⟨?_, by simp, ?_⟩
          · have h1 : (eval A .query args).length ≤ 1 := by
              rw [eval_query]
              split <;> simp
            omega
          · intro w hw
            simp only [queries_query, List.mem_singleton] at hw
            subst hw
            have := length_getD_le_maxLen args 0
            omega
      | .comp f gs =>
          have hf : sizeOf f ≤ n := by simp at ht; omega
          have hsz : ∀ g ∈ gs, sizeOf g ≤ n := by
            intro g hg
            have h1 := List.sizeOf_lt_of_mem hg
            simp at ht
            omega
          obtain ⟨pf, hpf, hfb⟩ := ih f hf
          obtain ⟨pg, hpg, hgb⟩ := exists_bounded_list (fun g hg => ih g (hsz g hg))
          refine ⟨fun N => gs.length * pg N + pf (pg N),
            ((polyMono_const gs.length).mul hpg).add (hpf.comp hpg), ?_⟩
          intro A args
          dsimp only
          have hM : maxLen (gs.map fun g => eval A g args) ≤ pg (maxLen args) := by
            refine maxLen_le_of_forall ?_
            intro u hu
            obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hu
            exact (hgb g hg A args).1
          obtain ⟨hf1, hf2, hf3⟩ := hfb A (gs.map fun g => eval A g args)
          have hf1' : (eval A f (gs.map fun g => eval A g args)).length ≤ pf (pg (maxLen args)) :=
            le_trans hf1 (hpf.2 hM)
          have hf2' : (queries A f (gs.map fun g => eval A g args)).length
              ≤ pf (pg (maxLen args)) := le_trans hf2 (hpf.2 hM)
          refine ⟨?_, ?_, ?_⟩
          · rw [eval_comp]; omega
          · rw [queries_comp]
            have hflat : ((gs.map fun g => queries A g args).flatten).length
                ≤ gs.length * pg (maxLen args) := by
              have := length_flatten_le (l := gs.map fun g => queries A g args)
                (B := pg (maxLen args)) ?_
              · simpa using this
              · intro u hu
                obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hu
                exact (hgb g hg A args).2.1
            simp only [List.length_append]
            omega
          · intro w hw
            rw [queries_comp] at hw
            rcases List.mem_append.1 hw with hw' | hw'
            · obtain ⟨u, hu, hwu⟩ := List.mem_flatten.1 hw'
              obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hu
              have := (hgb g hg A args).2.2 w hwu
              have hgl : pg (maxLen args) ≤ gs.length * pg (maxLen args) + pf (pg (maxLen args)) :=
                by
                have : 1 * pg (maxLen args) ≤ gs.length * pg (maxLen args) := by
                  rcases Nat.eq_zero_or_pos gs.length with h | h
                  · exfalso
                    rw [List.length_eq_zero_iff] at h
                    subst h
                    simp at hg
                  · exact Nat.mul_le_mul_right _ h
                omega
              omega
            · have := hf3 w hw'
              have : w.length ≤ pf (pg (maxLen args)) := le_trans this (hpf.2 hM)
              omega
      | .bRec g h₀ h₁ bd =>
          have hg : sizeOf g ≤ n := by simp at ht; omega
          have hh0 : sizeOf h₀ ≤ n := by simp at ht; omega
          have hh1 : sizeOf h₁ ≤ n := by simp at ht; omega
          have hbd : sizeOf bd ≤ n := by simp at ht; omega
          obtain ⟨pg', hpg', hgb⟩ := ih g hg
          obtain ⟨p0, hp0, h0b⟩ := ih h₀ hh0
          obtain ⟨p1, hp1, h1b⟩ := ih h₁ hh1
          obtain ⟨pbd, hpbd, hbdb⟩ := ih bd hbd
          have hphMono : PolyMono (fun N => p0 N + p1 N) := hp0.add hp1
          have hh : ∀ (A : Oracle) (args : List Word),
              ((eval A h₀ args).length ≤ p0 (maxLen args) + p1 (maxLen args) ∧
                (queries A h₀ args).length ≤ p0 (maxLen args) + p1 (maxLen args) ∧
                ∀ w ∈ queries A h₀ args, w.length ≤ p0 (maxLen args) + p1 (maxLen args)) ∧
              ((eval A h₁ args).length ≤ p0 (maxLen args) + p1 (maxLen args) ∧
                (queries A h₁ args).length ≤ p0 (maxLen args) + p1 (maxLen args) ∧
                ∀ w ∈ queries A h₁ args, w.length ≤ p0 (maxLen args) + p1 (maxLen args)) := by
            intro A args
            obtain ⟨a1, a2, a3⟩ := h0b A args
            obtain ⟨b1, b2, b3⟩ := h1b A args
            exact ⟨⟨by omega, by omega, fun w hw => by have := a3 w hw; omega⟩,
              ⟨by omega, by omega, fun w hw => by have := b3 w hw; omega⟩⟩
          have hQ : PolyMono (fun N => N + (pg' N + pbd N)) :=
            polyMono_id.add (hpg'.add hpbd)
          have hphQ : PolyMono
              (fun N => p0 (N + (pg' N + pbd N)) + p1 (N + (pg' N + pbd N))) :=
            hphMono.comp hQ
          refine ⟨fun N => pg' N + pbd N
              + (N + 1) * (pbd N + (p0 (N + (pg' N + pbd N)) + p1 (N + (pg' N + pbd N))))
              + (p0 (N + (pg' N + pbd N)) + p1 (N + (pg' N + pbd N))), ?_, ?_⟩
          · exact ((hpg'.add hpbd).add (polyMono_succ.mul (hpbd.add hphQ))).add hphQ
          · intro A args
            dsimp only
            match args with
            | [] =>
                obtain ⟨a1, a2, a3⟩ := hgb A []
                have he : eval A (.bRec g h₀ h₁ bd) [] = eval A g [] := by
                  simp [eval]
                have hq : queries A (.bRec g h₀ h₁ bd) [] = queries A g [] := by
                  simp [queries]
                refine ⟨?_, ?_, ?_⟩
                · rw [he]; omega
                · rw [hq]; omega
                · intro w hw
                  rw [hq] at hw
                  have := a3 w hw
                  omega
            | x :: rest =>
                obtain ⟨b1, b2, b3⟩ :=
                  bRec_bounds (g := g) (h₀ := h₀) (h₁ := h₁) (bd := bd)
                    (pg := pg') (ph := fun N => p0 N + p1 N) (pbd := pbd)
                    hpg'.2 hphMono.2 hpbd.2 hgb hh hbdb A (maxLen (x :: rest)) rest x le_rfl
                have hxlen : x.length ≤ maxLen (x :: rest) := by simp
                have hmul : x.length * (pbd (maxLen (x :: rest))
                      + (p0 (maxLen (x :: rest) + (pg' (maxLen (x :: rest))
                          + pbd (maxLen (x :: rest))))
                        + p1 (maxLen (x :: rest) + (pg' (maxLen (x :: rest))
                          + pbd (maxLen (x :: rest))))))
                    ≤ (maxLen (x :: rest) + 1) * (pbd (maxLen (x :: rest))
                      + (p0 (maxLen (x :: rest) + (pg' (maxLen (x :: rest))
                          + pbd (maxLen (x :: rest))))
                        + p1 (maxLen (x :: rest) + (pg' (maxLen (x :: rest))
                          + pbd (maxLen (x :: rest)))))) :=
                  Nat.mul_le_mul_right _ (by omega)
                exact ⟨by omega, by omega, fun w hw => by have := b3 w hw; omega⟩

/-- **Every oracle Cobham term is polynomially bounded**, uniformly in the oracle: the value, the
number of queries and the length of every query. -/
theorem bounded (t : CobQ) : Bounded t := bounded_aux (sizeOf t) t le_rfl

/-! ### The use principle -/

/-- The step of the use principle for `bRec`. -/
theorem bRec_run_congr {g h₀ h₁ bd : CobQ}
    (Hg : ∀ (A B : Oracle) (args : List Word),
      (∀ w ∈ queries A g args, A w = B w) → run A g args = run B g args)
    (H0 : ∀ (A B : Oracle) (args : List Word),
      (∀ w ∈ queries A h₀ args, A w = B w) → run A h₀ args = run B h₀ args)
    (H1 : ∀ (A B : Oracle) (args : List Word),
      (∀ w ∈ queries A h₁ args, A w = B w) → run A h₁ args = run B h₁ args)
    (Hbd : ∀ (A B : Oracle) (args : List Word),
      (∀ w ∈ queries A bd args, A w = B w) → run A bd args = run B bd args)
    (A B : Oracle) (rest : List Word) :
    ∀ x : Word, (∀ w ∈ queries A (.bRec g h₀ h₁ bd) (x :: rest), A w = B w) →
      run A (.bRec g h₀ h₁ bd) (x :: rest) = run B (.bRec g h₀ h₁ bd) (x :: rest) := by
  intro x
  induction x with
  | nil =>
      intro hAB
      simp only [run_bRec_nil]
      exact Hg A B rest (by simpa [queries] using hAB)
  | cons b x ih =>
      intro hAB
      have hAB' := hAB
      rw [queries_bRec_cons] at hAB'
      have hIH : run A (.bRec g h₀ h₁ bd) (x :: rest) = run B (.bRec g h₀ h₁ bd) (x :: rest) := by
        refine ih fun w hw => hAB' w ?_
        exact List.mem_append_left _ (List.mem_append_left _ hw)
      have hbdeq : run A bd ((b :: x) :: rest) = run B bd ((b :: x) :: rest) := by
        refine Hbd A B _ fun w hw => hAB' w ?_
        exact List.mem_append_left _ (List.mem_append_right _ hw)
      cases b
      · have hh0eq : run A h₀ (x :: (run A (.bRec g h₀ h₁ bd) (x :: rest)).1 :: rest)
            = run B h₀ (x :: (run A (.bRec g h₀ h₁ bd) (x :: rest)).1 :: rest) := by
          refine H0 A B _ fun w hw => hAB' w ?_
          exact List.mem_append_right _ hw
        rw [run_bRec_cons, run_bRec_cons]
        simp only [Bool.false_eq_true, if_false]
        rw [hh0eq, hbdeq, hIH]
      · have hh1eq : run A h₁ (x :: (run A (.bRec g h₀ h₁ bd) (x :: rest)).1 :: rest)
            = run B h₁ (x :: (run A (.bRec g h₀ h₁ bd) (x :: rest)).1 :: rest) := by
          refine H1 A B _ fun w hw => hAB' w ?_
          exact List.mem_append_right _ hw
        rw [run_bRec_cons, run_bRec_cons]
        simp only [if_true]
        rw [hh1eq, hbdeq, hIH]

theorem run_congr_aux : ∀ (n : ℕ) (t : CobQ), sizeOf t ≤ n →
    ∀ (A B : Oracle) (args : List Word),
      (∀ w ∈ queries A t args, A w = B w) → run A t args = run B t args := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      cases t <;> simp at ht
  | succ n ih =>
      intro t ht
      match t with
      | .proj i => intro A B args _; simp
      | .empty => intro A B args _; simp
      | .app b => intro A B args _; simp
      | .smash => intro A B args _; simp
      | .query =>
          intro A B args hAB
          have hq := hAB (args.getD 0 []) (by simp)
          rw [run_query, run_query, hq]
      | .comp f gs =>
          have hfsz : sizeOf f ≤ n := by simp at ht; omega
          have hsz : ∀ g ∈ gs, sizeOf g ≤ n := by
            intro g hg
            have h1 := List.sizeOf_lt_of_mem hg
            simp at ht
            omega
          intro A B args hAB
          rw [queries_comp] at hAB
          have hgs : ∀ g ∈ gs, run A g args = run B g args := by
            intro g hg
            refine ih g (hsz g hg) A B args fun w hw => hAB w ?_
            exact List.mem_append_left _
              (List.mem_flatten.2 ⟨queries A g args, List.mem_map_of_mem hg, hw⟩)
          have hmapE : (gs.map fun g => eval A g args) = gs.map fun g => eval B g args := by
            refine List.map_congr_left fun g hg => ?_
            unfold eval; rw [hgs g hg]
          have hmapQ : (gs.map fun g => queries A g args) = gs.map fun g => queries B g args := by
            refine List.map_congr_left fun g hg => ?_
            unfold queries; rw [hgs g hg]
          have hfrun : run A f (gs.map fun g => eval A g args)
              = run B f (gs.map fun g => eval B g args) := by
            rw [← hmapE]
            refine ih f hfsz A B _ fun w hw => hAB w ?_
            exact List.mem_append_right _ hw
          rw [run_comp, run_comp, ← hmapE, ← hmapQ, hfrun, hmapE]
      | .bRec g h₀ h₁ bd =>
          have hg : sizeOf g ≤ n := by simp at ht; omega
          have hh0 : sizeOf h₀ ≤ n := by simp at ht; omega
          have hh1 : sizeOf h₁ ≤ n := by simp at ht; omega
          have hbd : sizeOf bd ≤ n := by simp at ht; omega
          intro A B args hAB
          match args with
          | [] =>
              rw [run_bRec_args_nil, run_bRec_args_nil]
              refine ih g hg A B [] fun w hw => hAB w ?_
              simpa [queries] using hw
          | x :: rest =>
              exact bRec_run_congr (ih g hg) (ih h₀ hh0) (ih h₁ hh1) (ih bd hbd) A B rest x hAB

/-- **The use principle.**  Two oracles that agree on the words actually queried give the same
run: the same value and the same queries. -/
theorem run_congr (t : CobQ) (A B : Oracle) (args : List Word)
    (h : ∀ w ∈ queries A t args, A w = B w) : run A t args = run B t args :=
  run_congr_aux (sizeOf t) t le_rfl A B args h

/-- The use principle for the value alone. -/
theorem eval_congr (t : CobQ) (A B : Oracle) (args : List Word)
    (h : ∀ w ∈ queries A t args, A w = B w) : eval A t args = eval B t args := by
  unfold eval; rw [run_congr t A B args h]

/-- The output length of an oracle Cobham term is polynomially bounded. -/
theorem polyLen (t : CobQ) : ∃ p : ℕ → ℕ, PolyMono p ∧ ∀ (A : Oracle) (args : List Word),
    (eval A t args).length ≤ p (maxLen args) := by
  obtain ⟨p, hp, h⟩ := bounded t
  exact ⟨p, hp, fun A args => (h A args).1⟩

/-- **The number of oracle queries is polynomially bounded**, uniformly in the oracle: this is
what a diagonalization needs, since it makes the queried set too small to exhaust the words of a
given length. -/
theorem polyQueryCount (t : CobQ) : ∃ p : ℕ → ℕ, PolyMono p ∧ ∀ (A : Oracle) (args : List Word),
    (queries A t args).length ≤ p (maxLen args) := by
  obtain ⟨p, hp, h⟩ := bounded t
  exact ⟨p, hp, fun A args => (h A args).2.1⟩

/-- Every queried word is polynomially long. -/
theorem polyQueryLen (t : CobQ) : ∃ p : ℕ → ℕ, PolyMono p ∧ ∀ (A : Oracle) (args : List Word),
    ∀ w ∈ queries A t args, w.length ≤ p (maxLen args) := by
  obtain ⟨p, hp, h⟩ := bounded t
  exact ⟨p, hp, fun A args => (h A args).2.2⟩

end CobQ

end Complexity
