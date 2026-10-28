/-
**Cobham terms as word-register programs** — task `M26-UNIFY-DEPTHTHREE-COBMT`, first layer.

The host's polynomial-time functions are the functions denoted by Cobham terms (`Complexity.Cob`,
`Start/ComplexityClasses.lean`).  To run them on multi-tape machines, they are first compiled into
programs over registers holding words, whose instructions are the ones a multi-tape machine
performs on one tape per register: clear a register, append a bit, truncate a register to the
length of another, and loop over the bits of a register, forwards or backwards.

* `Complexity.CobMT.RProg`, `Complexity.CobMT.run` — the programs and their semantics;
* `Complexity.CobMT.compile` — the compiler: `compile v args out fr` writes `v` applied to the
  registers `args` into the register `out`, using the registers from `fr` on as scratch space and
  emptying them again (`regsUsed v` of them);
* **`Complexity.CobMT.compile_spec`** — the compiler is correct: the output register receives
  `v.eval`, the registers below `fr` other than `out` are unchanged, and the scratch registers are
  empty again.
-/

import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobMT

/-- A file of word registers. -/
abbrev Regs := ℕ → Word

/-- **Word-register programs.** -/
inductive RProg where
  | skip
  /-- Empty a register. -/
  | clear (r : ℕ)
  /-- Append a bit to a register. -/
  | push (r : ℕ) (b : Bool)
  /-- Truncate the register `r` to the length of the register `s`. -/
  | trunc (r s : ℕ)
  | seq (p q : RProg)
  /-- Run `p₀` or `p₁` for each bit of `r`, from the first to the last. -/
  | forBits (r : ℕ) (p₀ p₁ : RProg)
  /-- Run `p₀` or `p₁` for each bit of `r`, from the last to the first. -/
  | forBitsRev (r : ℕ) (p₀ p₁ : RProg)

namespace RProg

/-- **The semantics.** The bits a loop runs over are those of the register when the loop starts. -/
def run : RProg → Regs → Regs
  | .skip, R => R
  | .clear r, R => Function.update R r []
  | .push r b, R => Function.update R r (R r ++ [b])
  | .trunc r s, R => Function.update R r ((R r).take (R s).length)
  | .seq p q, R => run q (run p R)
  | .forBits r p₀ p₁, R => (R r).foldl (fun R' b => bif b then run p₁ R' else run p₀ R') R
  | .forBitsRev r p₀ p₁, R => (R r).foldr (fun b R' => bif b then run p₁ R' else run p₀ R') R

/-- A sequence of programs. -/
def seqs : List RProg → RProg
  | [] => .skip
  | p :: ps => .seq p (seqs ps)

/-- Append the register `a` to the register `d`. -/
def append (a d : ℕ) : RProg := .forBits a (.push d false) (.push d true)

/-- Copy the register `a` into the register `d`. -/
def copy (a d : ℕ) : RProg := .seq (.clear d) (append a d)

/-- Empty the registers `fr, …, fr + n - 1`. -/
def clearRange (fr : ℕ) : ℕ → RProg
  | 0 => .skip
  | n + 1 => .seq (clearRange fr n) (.clear (fr + n))

@[simp] theorem run_skip (R : Regs) : run .skip R = R := rfl
@[simp] theorem run_clear (r : ℕ) (R : Regs) : run (.clear r) R = Function.update R r [] := rfl
@[simp] theorem run_push (r : ℕ) (b : Bool) (R : Regs) :
    run (.push r b) R = Function.update R r (R r ++ [b]) := rfl
@[simp] theorem run_trunc (r s : ℕ) (R : Regs) :
    run (.trunc r s) R = Function.update R r ((R r).take (R s).length) := rfl
@[simp] theorem run_seq (p q : RProg) (R : Regs) : run (.seq p q) R = run q (run p R) := rfl

theorem run_seqs_nil (R : Regs) : run (seqs []) R = R := rfl

theorem run_seqs_cons (p : RProg) (ps : List RProg) (R : Regs) :
    run (seqs (p :: ps)) R = run (seqs ps) (run p R) := rfl

theorem run_append {a d : ℕ} (h : a ≠ d) (R : Regs) :
    run (append a d) R = Function.update R d (R d ++ R a) := by
  show (R a).foldl _ R = _
  have key : ∀ (L : List Bool) (R' : Regs), R' a = R a →
      L.foldl (fun R'' b => bif b then run (.push d true) R'' else run (.push d false) R'') R' =
        Function.update R' d (R' d ++ L) := by
    intro L
    induction L with
    | nil => intro R' _; simp
    | cons b L ih =>
        intro R' hR'
        rw [List.foldl_cons]
        have hstep : (bif b then run (.push d true) R' else run (.push d false) R') =
            Function.update R' d (R' d ++ [b]) := by cases b <;> rfl
        rw [hstep, ih _ (by rw [Function.update_of_ne h]; exact hR')]
        funext r
        by_cases hr : r = d
        · subst hr; simp
        · simp [Function.update_of_ne hr]
  exact key (R a) R rfl

theorem run_copy {a d : ℕ} (h : a ≠ d) (R : Regs) :
    run (copy a d) R = Function.update R d (R a) := by
  rw [copy, run_seq, run_clear, run_append h]
  funext r
  by_cases hr : r = d
  · subst hr; simp [Function.update_of_ne h]
  · simp [Function.update_of_ne hr]

theorem run_clearRange (fr n : ℕ) (R : Regs) (r : ℕ) :
    run (clearRange fr n) R r = if fr ≤ r ∧ r < fr + n then [] else R r := by
  induction n generalizing r with
  | zero => simp only [clearRange, run_skip]; split <;> first | rfl | omega
  | succ n ih =>
      simp only [clearRange, run_seq, run_clear]
      by_cases hr : r = fr + n
      · subst hr; simp
      · rw [Function.update_of_ne hr, ih]
        split <;> split <;> first | rfl | omega

/-- The loop over the bits of a register appending `true` to `o` for each of them. -/
theorem run_forBits_push {a o : ℕ} (h : a ≠ o) (R : Regs) :
    run (.forBits a (.push o true) (.push o true)) R =
      Function.update R o (R o ++ List.replicate (R a).length true) := by
  show (R a).foldl _ R = _
  have key : ∀ (L : List Bool) (R' : Regs),
      L.foldl (fun R'' b => bif b then run (.push o true) R'' else run (.push o true) R'') R' =
        Function.update R' o (R' o ++ List.replicate L.length true) := by
    intro L
    induction L with
    | nil => intro R'; simp
    | cons b L ih =>
        intro R'
        rw [List.foldl_cons]
        have hstep : (bif b then run (.push o true) R' else run (.push o true) R') =
            Function.update R' o (R' o ++ [true]) := by cases b <;> rfl
        rw [hstep, ih]
        funext r
        by_cases hr : r = o
        · subst hr
          simp only [Function.update_self, List.length_cons, List.append_assoc,
            List.singleton_append]
          rw [← List.replicate_succ, List.replicate_succ']
        · simp [Function.update_of_ne hr]
  exact key (R a) R

/-- Nested loops: `|a₀| · |a₁|` copies of `true`. -/
theorem run_smashLoop {a₀ a₁ o : ℕ} (h₀ : a₀ ≠ o) (h₁ : a₁ ≠ o) (R : Regs) :
    run (.forBits a₀ (.forBits a₁ (.push o true) (.push o true))
      (.forBits a₁ (.push o true) (.push o true))) R =
      Function.update R o (R o ++ List.replicate ((R a₀).length * (R a₁).length) true) := by
  show (R a₀).foldl _ R = _
  have key : ∀ (L : List Bool) (R' : Regs), R' a₁ = R a₁ →
      L.foldl (fun R'' b => bif b then run (.forBits a₁ (.push o true) (.push o true)) R''
        else run (.forBits a₁ (.push o true) (.push o true)) R'') R' =
        Function.update R' o (R' o ++ List.replicate (L.length * (R a₁).length) true) := by
    intro L
    induction L with
    | nil => intro R' _; simp
    | cons b L ih =>
        intro R' hR'
        rw [List.foldl_cons]
        have hstep : (bif b then run (.forBits a₁ (.push o true) (.push o true)) R'
            else run (.forBits a₁ (.push o true) (.push o true)) R') =
            Function.update R' o (R' o ++ List.replicate (R a₁).length true) := by
          cases b <;> simp only [cond_true, cond_false] <;> rw [run_forBits_push h₁, hR']
        rw [hstep, ih _ (by rw [Function.update_of_ne h₁]; exact hR')]
        funext r
        by_cases hr : r = o
        · subst hr
          simp only [Function.update_self, List.append_assoc, List.length_cons,
            ← List.replicate_add]
          congr 2
          ring
        · simp [Function.update_of_ne hr]
  exact key (R a₀) R rfl

end RProg

open RProg

/-! ### The compiler -/

/-- The number of scratch registers the compiled program of a term uses. -/
def regsUsed : Cob → ℕ
  | .proj _ => 0
  | .empty => 0
  | .app _ => 0
  | .smash => 0
  | .comp f gs => gs.length + max (regsUsed f) ((gs.attach.map fun g => regsUsed g.1).foldr max 0)
  | .bRec g h₀ h₁ bd => 5 + max (max (regsUsed g) (regsUsed h₀)) (max (regsUsed h₁) (regsUsed bd))
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    · omega
    · have := List.sizeOf_lt_of_mem g.2; omega
    all_goals omega

/-- One step of bounded recursion on notation, for the bit `b`: with the suffix in `fr` and the
value in `fr + 1`, run the step program `ch` into `fr + 2`, form `b :: suffix` in `fr + 3`, run
the bound program `cbd` into `fr + 4`, truncate, and move on. -/
def bRecBody (ch cbd : RProg) (b : Bool) (fr : ℕ) : RProg :=
  seqs [ch, .clear (fr + 3), .push (fr + 3) b, append fr (fr + 3), cbd,
    copy (fr + 2) (fr + 1), .trunc (fr + 1) (fr + 4), copy (fr + 3) fr,
    .clear (fr + 2), .clear (fr + 3), .clear (fr + 4)]

/-- The loop of bounded recursion, over the bits of the recursion argument from the last one. -/
def bRecLoop (x : Option ℕ) (p₀ p₁ : RProg) : RProg :=
  match x with
  | some x => .forBitsRev x p₀ p₁
  | none => .skip

mutual

/-- **The compiler.** `compile v args out fr` computes `v` on the registers `args` into `out`,
with scratch registers `fr, …, fr + regsUsed v - 1`. -/
def compile : Cob → List ℕ → ℕ → ℕ → RProg
  | .proj i, args, out, _ =>
      match args[i]? with
      | some a => copy a out
      | none => .clear out
  | .empty, _, out, _ => .clear out
  | .app b, args, out, _ =>
      .seq (.clear out) (.seq (.push out b)
        (match args[0]? with
          | some a => append a out
          | none => .skip))
  | .smash, args, out, _ =>
      .seq (.clear out)
        (match args[0]?, args[1]? with
          | some a₀, some a₁ =>
              .forBits a₀ (.forBits a₁ (.push out true) (.push out true))
                (.forBits a₁ (.push out true) (.push out true))
          | _, _ => .skip)
  | .comp f gs, args, out, fr =>
      .seq (compileList gs args fr (fr + gs.length))
        (.seq (compile f (List.range' fr gs.length) out (fr + gs.length))
          (clearRange fr gs.length))
  | .bRec g h₀ h₁ bd, args, out, fr =>
      seqs [compile g args.tail (fr + 1) (fr + 5),
        bRecLoop args[0]?
          (bRecBody (compile h₀ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
            (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) false fr)
          (bRecBody (compile h₁ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
            (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) true fr),
        copy (fr + 1) out, clearRange fr 5]
  termination_by v => sizeOf v

/-- Compile a list of terms into consecutive registers `j, j + 1, …`, with scratch from `sc`. -/
def compileList : List Cob → List ℕ → ℕ → ℕ → RProg
  | [], _, _, _ => .skip
  | g :: gs, args, j, sc => .seq (compile g args j sc) (compileList gs args (j + 1) sc)
  termination_by gs => sizeOf gs

end

/-! ### Correctness -/

/-- The specification of a compiled program. -/
def Spec (v : Cob) (args : List ℕ) (out fr : ℕ) : Prop :=
  ∀ R : Regs, (∀ a ∈ args, a < fr) → out < fr → out ∉ args → (∀ r, fr ≤ r → R r = []) →
    (run (compile v args out fr) R) out = v.eval (args.map R) ∧
      (∀ r, r ≠ out → r < fr → run (compile v args out fr) R r = R r) ∧
      (∀ r, fr ≤ r → run (compile v args out fr) R r = [])

theorem getD_map (args : List ℕ) (R : Regs) (i : ℕ) :
    (args.map R).getD i [] = match args[i]? with | some a => R a | none => [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases args[i]? <;> rfl

theorem spec_proj (i : ℕ) (args : List ℕ) (out fr : ℕ) : Spec (.proj i) args out fr := by
  intro R hargs hout hna hscr
  rw [compile, Cob.eval_proj, getD_map]
  cases hi : args[i]? with
  | none =>
      refine ⟨by simp, fun r hr _ => by simp [Function.update_of_ne hr], fun r hr => ?_⟩
      simp only [run_clear]
      rw [Function.update_of_ne (by omega)]
      exact hscr r hr
  | some a =>
      have ha : a ∈ args := List.mem_of_getElem? hi
      have hne : a ≠ out := fun h => hna (h ▸ ha)
      refine ⟨by simp [run_copy hne], fun r hr _ => by simp [run_copy hne,
        Function.update_of_ne hr], fun r hr => ?_⟩
      rw [run_copy hne, Function.update_of_ne (by omega)]
      exact hscr r hr

theorem spec_empty (args : List ℕ) (out fr : ℕ) : Spec .empty args out fr := by
  intro R _ hout _ hscr
  rw [compile, Cob.eval_empty]
  refine ⟨by simp, fun r hr _ => by simp [Function.update_of_ne hr], fun r hr => ?_⟩
  simp only [run_clear]
  rw [Function.update_of_ne (by omega)]
  exact hscr r hr

theorem spec_app (b : Bool) (args : List ℕ) (out fr : ℕ) : Spec (.app b) args out fr := by
  intro R hargs hout hna hscr
  rw [compile, Cob.eval_app, getD_map]
  cases h0 : args[0]? with
  | none =>
      simp only [run_seq, run_clear, run_push, run_skip]
      refine ⟨by simp, fun r hr _ => by simp [Function.update_of_ne hr], fun r hr => ?_⟩
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hscr r hr
  | some a =>
      have ha : a ∈ args := List.mem_of_getElem? h0
      have hne : a ≠ out := fun h => hna (h ▸ ha)
      simp only [run_seq, run_clear, run_push, run_append hne]
      refine ⟨by simp [Function.update_of_ne hne], fun r hr _ => by
        simp [Function.update_of_ne hr], fun r hr => ?_⟩
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hscr r hr

theorem spec_smash (args : List ℕ) (out fr : ℕ) : Spec .smash args out fr := by
  intro R hargs hout hna hscr
  rw [compile, Cob.eval_smash, getD_map, getD_map]
  cases h0 : args[0]? with
  | none =>
      simp only [run_seq, run_clear, run_skip, List.length_nil, zero_mul, List.replicate_zero]
      refine ⟨by simp, fun r hr _ => by simp [Function.update_of_ne hr], fun r hr => ?_⟩
      rw [Function.update_of_ne (by omega)]
      exact hscr r hr
  | some a₀ =>
      cases h1 : args[1]? with
      | none =>
          simp only [run_seq, run_clear, run_skip, List.length_nil, mul_zero,
            List.replicate_zero]
          refine ⟨by simp, fun r hr _ => by simp [Function.update_of_ne hr], fun r hr => ?_⟩
          rw [Function.update_of_ne (by omega)]
          exact hscr r hr
      | some a₁ =>
          have hne₀ : a₀ ≠ out := fun h => hna (h ▸ List.mem_of_getElem? h0)
          have hne₁ : a₁ ≠ out := fun h => hna (h ▸ List.mem_of_getElem? h1)
          simp only [run_seq, run_clear, run_smashLoop hne₀ hne₁]
          refine ⟨by simp [Function.update_of_ne hne₀, Function.update_of_ne hne₁],
            fun r hr _ => by simp [Function.update_of_ne hr], fun r hr => ?_⟩
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hscr r hr

/-- The specification of a compiled list of terms. -/
theorem spec_list (gs : List Cob) (hgs : ∀ g ∈ gs, ∀ args out fr, Spec g args out fr) :
    ∀ (args : List ℕ) (j sc : ℕ) (R : Regs), (∀ a ∈ args, a < j) → j + gs.length ≤ sc →
      (∀ r, sc ≤ r → R r = []) →
      (∀ i (hi : i < gs.length), run (compileList gs args j sc) R (j + i) =
          gs[i].eval (args.map R)) ∧
        (∀ r, (r < j ∨ (j + gs.length ≤ r ∧ r < sc)) → run (compileList gs args j sc) R r = R r) ∧
        (∀ r, sc ≤ r → run (compileList gs args j sc) R r = []) := by
  induction gs with
  | nil =>
      intro args j sc R _ _ hscr
      rw [compileList]
      exact ⟨fun i hi => absurd hi (by simp), fun r _ => rfl, hscr⟩
  | cons g gs ih =>
      intro args j sc R hargs hlen hscr
      simp only [List.length_cons] at hlen
      rw [compileList, run_seq]
      obtain ⟨g1, g2, g3⟩ := hgs g List.mem_cons_self args j sc R
        (fun a ha => by have := hargs a ha; omega) (by omega)
        (fun h => by have := hargs j h; omega) hscr
      set R1 := run (compile g args j sc) R
      have hmap : args.map R1 = args.map R :=
        List.map_congr_left fun a ha => g2 a (by have := hargs a ha; omega)
          (by have := hargs a ha; omega)
      obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) args (j + 1) sc
        R1 (fun a ha => by have := hargs a ha; omega) (by omega) g3
      refine ⟨fun i hi => ?_, fun r hr => ?_, i3⟩
      · cases i with
        | zero =>
            rw [show j + 0 = j from rfl, i2 j (by omega)]
            exact g1
        | succ i =>
            rw [show j + (i + 1) = j + 1 + i by omega, i1 i (by simpa using hi), hmap]
            rfl
      · rw [i2 r (by simp only [List.length_cons] at hr; omega)]
        exact g2 r (by simp only [List.length_cons] at hr; omega)
          (by simp only [List.length_cons] at hr; omega)

theorem spec_comp (f : Cob) (gs : List Cob) (hf : ∀ args out fr, Spec f args out fr)
    (hgs : ∀ g ∈ gs, ∀ args out fr, Spec g args out fr) (args : List ℕ) (out fr : ℕ) :
    Spec (.comp f gs) args out fr := by
  intro R hargs hout hna hscr
  rw [compile, Cob.eval_comp]
  simp only [run_seq]
  set n := gs.length
  obtain ⟨l1, l2, l3⟩ := spec_list gs hgs args fr (fr + n) R hargs le_rfl
    (fun r hr => hscr r (by omega))
  set R1 := run (compileList gs args fr (fr + n)) R
  obtain ⟨f1, f2, f3⟩ := hf (List.range' fr n) out (fr + n) R1
    (fun a ha => by simp [List.mem_range'] at ha; omega) (by omega)
    (fun h => by simp [List.mem_range'] at h; omega) l3
  set R2 := run (compile f (List.range' fr n) out (fr + n)) R1
  have hmap : (List.range' fr n).map R1 = gs.map fun g => g.eval (args.map R) := by
    apply List.ext_getElem (by simp [n])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range']
    rw [show fr + 1 * i = fr + i by ring, l1 i (by simpa [n] using h2)]
  refine ⟨?_, fun r hr hlt => ?_, fun r hr => ?_⟩
  · rw [run_clearRange, if_neg (by omega), f1, hmap]
  · rw [run_clearRange, if_neg (by omega), f2 r hr (by omega), l2 r (Or.inl hlt)]
  · rw [run_clearRange]
    split
    · rfl
    · exact f3 r (by omega)

/-- The loop invariant of bounded recursion: the suffix `sl` processed so far in `fr`, its value
in `fr + 1`, the work registers `fr + 2, fr + 3, fr + 4` empty, the registers below `fr` as in
`R`, and the scratch registers from `fr + 5` on empty. -/
def BInv (F : Cob) (Ys : List Word) (R : Regs) (fr : ℕ) (sl : Word) (S : Regs) : Prop :=
  S fr = sl ∧ S (fr + 1) = F.eval (sl :: Ys) ∧ S (fr + 2) = [] ∧ S (fr + 3) = [] ∧
    S (fr + 4) = [] ∧ (∀ r, r < fr → S r = R r) ∧ (∀ r, fr + 5 ≤ r → S r = [])

theorem bRecBody_spec {F h bd : Cob} {args : List ℕ} {fr : ℕ} {R : Regs} {b : Bool} {sl : Word}
    (hargs : ∀ a ∈ args, a < fr)
    (hh : Spec h (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
    (hbd : Spec bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5))
    (hF : F.eval ((b :: sl) :: args.tail.map R) =
      (h.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R)).take
        (bd.eval ((b :: sl) :: args.tail.map R)).length)
    {S : Regs} (hS : BInv F (args.tail.map R) R fr sl S) :
    BInv F (args.tail.map R) R fr (b :: sl)
      (run (bRecBody (compile h (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
        (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) b fr) S) := by
  obtain ⟨s0, s1, s2, s3, s4, slow, shigh⟩ := hS
  have htail : ∀ a ∈ args.tail, a < fr := fun a ha => hargs a (List.mem_of_mem_tail ha)
  have hYs : args.tail.map S = args.tail.map R :=
    List.map_congr_left fun a ha => slow a (htail a ha)
  simp only [bRecBody, run_seqs_cons, run_seqs_nil]
  -- the step program
  obtain ⟨h1, h2, h3⟩ := hh S
    (fun a ha => by
      simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · omega
      · omega
      · have := htail a ha; omega)
    (by omega)
    (fun ha => by
      simp only [List.mem_cons] at ha
      rcases ha with ha | ha | ha
      · omega
      · omega
      · have := htail _ ha; omega)
    shigh
  set S1 := run (compile h (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5)) S
  have e1 : S1 (fr + 2) = h.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R) := by
    rw [h1]; simp [s0, s1, hYs]
  -- forming `b :: sl`
  set S4 := run (append fr (fr + 3)) (run (.push (fr + 3) b) (run (.clear (fr + 3)) S1))
  have e4 : S4 = Function.update S1 (fr + 3) (b :: sl) := by
    simp only [S4, run_push, run_clear, run_append (show fr ≠ fr + 3 by omega)]
    funext r
    by_cases hr : r = fr + 3
    · subst hr
      simp only [Function.update_self, Function.update_of_ne (show fr ≠ fr + 3 by omega)]
      rw [h2 fr (by omega) (by omega), s0]
      rfl
    · simp [Function.update_of_ne hr]
  -- the bound program
  obtain ⟨b1, b2, b3⟩ := hbd S4
    (fun a ha => by
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · have := htail a ha; omega)
    (by omega)
    (fun ha => by
      simp only [List.mem_cons] at ha
      rcases ha with ha | ha
      · omega
      · have := htail _ ha; omega)
    (fun r hr => by rw [e4, Function.update_of_ne (by omega)]; exact h3 r hr)
  set S5 := run (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) S4
  have hYs4 : args.tail.map S4 = args.tail.map R := by
    rw [e4]
    refine List.map_congr_left fun a ha => ?_
    have := htail a ha
    rw [Function.update_of_ne (by omega), h2 a (by omega) (by omega), slow a this]
  have e5 : S5 (fr + 4) = bd.eval ((b :: sl) :: args.tail.map R) := by
    rw [b1, List.map_cons, hYs4, e4, Function.update_self]
  have e52 : S5 (fr + 2) = h.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R) := by
    rw [b2 _ (by omega) (by omega), e4, Function.update_of_ne (by omega), e1]
  have e53 : S5 (fr + 3) = b :: sl := by
    rw [b2 _ (by omega) (by omega), e4]; simp
  have e5low : ∀ r, r < fr → S5 r = R r := fun r hr => by
    rw [b2 r (by omega) (by omega), e4, Function.update_of_ne (by omega),
      h2 r (by omega) (by omega), slow r hr]
  -- the rest are explicit updates
  rw [run_copy (show fr + 2 ≠ fr + 1 by omega), run_trunc, run_copy (show fr + 3 ≠ fr by omega)]
  simp only [run_clear]
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_⟩
  · simp only [Function.update_of_ne (show fr ≠ fr + 4 by omega),
      Function.update_of_ne (show fr ≠ fr + 3 by omega),
      Function.update_of_ne (show fr ≠ fr + 2 by omega), Function.update_self]
    rw [Function.update_of_ne (show fr + 3 ≠ fr + 1 by omega),
      Function.update_of_ne (show fr + 3 ≠ fr + 1 by omega), e53]
  · simp only [Function.update_of_ne (show fr + 1 ≠ fr + 4 by omega),
      Function.update_of_ne (show fr + 1 ≠ fr + 3 by omega),
      Function.update_of_ne (show fr + 1 ≠ fr + 2 by omega),
      Function.update_of_ne (show fr + 1 ≠ fr by omega), Function.update_self]
    rw [Function.update_of_ne (show fr + 4 ≠ fr + 1 by omega), e52, e5, hF]
  · simp
  · simp
  · simp
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact e5low r hr
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact b3 r hr

theorem spec_bRec (g h₀ h₁ bd : Cob) (hg : ∀ args out fr, Spec g args out fr)
    (hh₀ : ∀ args out fr, Spec h₀ args out fr) (hh₁ : ∀ args out fr, Spec h₁ args out fr)
    (hbd : ∀ args out fr, Spec bd args out fr) (args : List ℕ) (out fr : ℕ) :
    Spec (.bRec g h₀ h₁ bd) args out fr := by
  intro R hargs hout hna hscr
  set F := Cob.bRec g h₀ h₁ bd
  have htail : ∀ a ∈ args.tail, a < fr := fun a ha => hargs a (List.mem_of_mem_tail ha)
  rw [compile]
  simp only [run_seqs_cons, run_seqs_nil]
  -- the base
  obtain ⟨g1, g2, g3⟩ := hg args.tail (fr + 1) (fr + 5) R
    (fun a ha => by have := htail a ha; omega) (by omega)
    (fun ha => by have := htail _ ha; omega) (fun r hr => hscr r (by omega))
  set R1 := run (compile g args.tail (fr + 1) (fr + 5)) R
  have hinv0 : BInv F (args.tail.map R) R fr [] R1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => g2 r (by omega) (by omega), g3⟩
    · rw [g2 fr (by omega) (by omega)]; exact hscr fr le_rfl
    · rw [g1, Cob.eval_bRec_nil]
    · rw [g2 _ (by omega) (by omega)]; exact hscr _ (by omega)
    · rw [g2 _ (by omega) (by omega)]; exact hscr _ (by omega)
    · rw [g2 _ (by omega) (by omega)]; exact hscr _ (by omega)
  -- the loop
  have hloop : (∃ X : Word, BInv F (args.tail.map R) R fr X
      (run (bRecLoop args[0]?
              (bRecBody (compile h₀ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
                (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) false fr)
              (bRecBody (compile h₁ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
                (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) true fr)) R1) ∧
        args.map R = X :: args.tail.map R) ∨
      (args = [] ∧ BInv F [] R fr [] R1) := by
    cases hx : args[0]? with
    | none =>
        right
        have hnil : args = [] := by
          cases args with
          | nil => rfl
          | cons a l => simp at hx
        subst hnil
        exact ⟨rfl, hinv0⟩
    | some x =>
        left
        have hxmem : args = x :: args.tail := by
          cases args with
          | nil => simp at hx
          | cons a l => simp at hx; subst hx; rfl
        have hxlt : x < fr := hargs x (by rw [hxmem]; exact List.mem_cons_self)
        refine ⟨R x, ?_, by rw [hxmem]; simp⟩
        rw [bRecLoop]
        show BInv F _ R fr (R x) ((R1 x).foldr _ R1)
        rw [show R1 x = R x from g2 x (by omega) (by omega)]
        have key : ∀ L : Word, BInv F (args.tail.map R) R fr L (L.foldr (fun b S =>
            bif b then run (bRecBody (compile h₁ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
              (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) true fr) S
            else run (bRecBody (compile h₀ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
              (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) false fr) S) R1) := by
          intro L
          induction L with
          | nil => exact hinv0
          | cons b L ih =>
              rw [List.foldr_cons]
              cases b with
              | false =>
                  exact bRecBody_spec hargs (hh₀ _ _ _) (hbd _ _ _)
                    (by rw [Cob.eval_bRec_cons]; rfl) ih
              | true =>
                  exact bRecBody_spec hargs (hh₁ _ _ _) (hbd _ _ _)
                    (by rw [Cob.eval_bRec_cons]; rfl) ih
        exact key (R x)
  set R2 := run (bRecLoop args[0]?
              (bRecBody (compile h₀ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
                (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) false fr)
              (bRecBody (compile h₁ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
                (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) true fr)) R1 with hR2
  -- the facts about `R2` needed below
  have hfacts : R2 (fr + 1) = F.eval (args.map R) ∧ (∀ r, r < fr → R2 r = R r) ∧
      (∀ r, fr + 5 ≤ r → R2 r = []) := by
    rcases hloop with ⟨X, ⟨_, i1, _, _, _, ilow, ihigh⟩, hX⟩ | ⟨hnil, hinv⟩
    · exact ⟨by rw [i1, hX], ilow, ihigh⟩
    · subst hnil
      have hR2' : R2 = R1 := by rw [hR2]; simp [bRecLoop]
      obtain ⟨_, i1, _, _, _, ilow, ihigh⟩ := hinv
      refine ⟨?_, ?_, ?_⟩
      · rw [hR2', i1]
        simp [F, Cob.eval_bRec]
      · intro r hr; rw [hR2']; exact ilow r hr
      · intro r hr; rw [hR2']; exact ihigh r hr
  obtain ⟨f1, flow, fhigh⟩ := hfacts
  have hne : fr + 1 ≠ out := by omega
  refine ⟨?_, fun r hr hlt => ?_, fun r hr => ?_⟩
  · rw [run_clearRange, if_neg (by omega), run_copy hne]
    simp [f1]
  · rw [run_clearRange, if_neg (by omega), run_copy hne, Function.update_of_ne hr]
    exact flow r hlt
  · rw [run_clearRange]
    split
    · rfl
    · rw [run_copy hne, Function.update_of_ne (by omega)]
      exact fhigh r (by omega)

/-- **The compiler is correct.** -/
theorem compile_spec_aux : ∀ (n : ℕ) (v : Cob), sizeOf v ≤ n → ∀ args out fr, Spec v args out fr := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv args out fr
    cases v with
    | proj i => exact spec_proj i args out fr
    | empty => exact spec_empty args out fr
    | app b => exact spec_app b args out fr
    | smash => exact spec_smash args out fr
    | comp f gs =>
        simp only [Cob.comp.sizeOf_spec] at hv
        exact spec_comp f gs (ih (sizeOf f) (by omega) f le_rfl)
          (fun g hg => ih (sizeOf g) (by have := List.sizeOf_lt_of_mem hg; omega) g le_rfl)
          args out fr
    | bRec g h₀ h₁ bd =>
        simp only [Cob.bRec.sizeOf_spec] at hv
        exact spec_bRec g h₀ h₁ bd (ih _ (by omega) g le_rfl) (ih _ (by omega) h₀ le_rfl)
          (ih _ (by omega) h₁ le_rfl) (ih _ (by omega) bd le_rfl) args out fr

theorem compile_spec (v : Cob) (args : List ℕ) (out fr : ℕ) : Spec v args out fr :=
  compile_spec_aux (sizeOf v) v le_rfl args out fr

end CobMT

end Complexity
