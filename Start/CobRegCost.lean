/-
**The cost of compiled Cobham terms is polynomial** — task `M26-UNIFY-DEPTHTHREE-COBMT`, second
layer.

`Start/CobRegProg.lean` compiles Cobham terms into word-register programs.  This module charges each
instruction the number of head moves a multi-tape machine needs for it (clearing or appending to a
register walks over it and back, a loop walks over its register once, …) and proves that the
compiled program of a term costs at most a polynomial in the length of its longest argument.

* `Complexity.CobMT.RProg.cost` — the cost of a program on a register file;
* `Complexity.CobMT.PolyM` — monotone functions bounded by a polynomial, with their closure
  properties;
* **`Complexity.CobMT.compile_cost`** — for every term `v` there is a monotone polynomial `f` with
  `cost (compile v args out fr) R ≤ f (maxLen (args.map R))` whenever the scratch registers and
  the output register are empty.
-/

import Start.CobRegProg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobMT

namespace RProg

/-- The cost of the iterations of a loop. -/
def iterCost (c₀ c₁ : Regs → ℕ) (f₀ f₁ : Regs → Regs) : List Bool → Regs → ℕ
  | [], _ => 0
  | b :: L, S => (bif b then c₁ S else c₀ S) + 3 + iterCost c₀ c₁ f₀ f₁ L (bif b then f₁ S else f₀ S)

/-- **The cost of a program**: the head moves of its machine. -/
def cost : RProg → Regs → ℕ
  | .skip, _ => 1
  | .clear r, R => 2 * (R r).length + 5
  | .push r _, R => 2 * (R r).length + 5
  | .trunc r s, R => 3 * ((R r).length + (R s).length) + 8
  | .seq p q, R => cost p R + cost q (run p R)
  | .forBits r p₀ p₁, R =>
      iterCost (cost p₀) (cost p₁) (run p₀) (run p₁) (R r) R + 2 * (R r).length + 5
  | .forBitsRev r p₀ p₁, R =>
      iterCost (cost p₀) (cost p₁) (run p₀) (run p₁) (R r).reverse R + 2 * (R r).length + 5

theorem iterCost_le {c₀ c₁ : Regs → ℕ} {f₀ f₁ : Regs → Regs} (B : ℕ)
    (Q : List Bool → Regs → Prop)
    (hQ : ∀ b L S, Q (b :: L) S →
      (bif b then c₁ S else c₀ S) ≤ B ∧ Q L (bif b then f₁ S else f₀ S)) :
    ∀ (L : List Bool) (S : Regs), Q L S → iterCost c₀ c₁ f₀ f₁ L S ≤ L.length * (B + 3) := by
  intro L
  induction L with
  | nil => intro S _; simp [iterCost]
  | cons b L ih =>
      intro S hS
      obtain ⟨h1, h2⟩ := hQ b L S hS
      have := ih _ h2
      simp only [iterCost, List.length_cons]
      nlinarith

/-- A loop pushing a bit to `o` for each bit of `r`. -/
theorem cost_pushLoop (r o : ℕ) (b₀ b₁ : Bool) (R : Regs) :
    cost (.forBits r (.push o b₀) (.push o b₁)) R ≤
      (R r).length * (2 * ((R o).length + (R r).length) + 8) + 2 * (R r).length + 5 := by
  rw [cost]
  have := iterCost_le (c₀ := cost (.push o b₀)) (c₁ := cost (.push o b₁))
    (f₀ := run (.push o b₀)) (f₁ := run (.push o b₁)) (2 * ((R o).length + (R r).length) + 5)
    (fun L S => (S o).length + L.length ≤ (R o).length + (R r).length)
    (fun b L S hS => by
      simp only [List.length_cons] at hS
      cases b <;> simp only [Bool.cond_true, Bool.cond_false, cost, run_push, Function.update_self,
        List.length_append, List.length_singleton] <;> constructor <;> omega)
    (R r) R (le_refl _)
  nlinarith

theorem cost_append_le (a d : ℕ) (R : Regs) :
    cost (append a d) R ≤
      (R a).length * (2 * ((R d).length + (R a).length) + 8) + 2 * (R a).length + 5 :=
  cost_pushLoop a d false true R

theorem cost_copy_le {a d : ℕ} (h : a ≠ d) (R : Regs) :
    cost (copy a d) R ≤ 2 * (R d).length + 5 +
      ((R a).length * (2 * (R a).length + 8) + 2 * (R a).length + 5) := by
  simp only [copy, cost, run_clear]
  have := cost_append_le a d (Function.update R d [])
  rw [Function.update_self, Function.update_of_ne h] at this
  simpa using this

theorem cost_clearRange_le (fr n B : ℕ) (R : Regs) (h : ∀ r, fr ≤ r → r < fr + n → (R r).length ≤ B) :
    cost (clearRange fr n) R ≤ n * (2 * B + 6) + 1 := by
  induction n with
  | zero => simp [clearRange, cost]
  | succ n ih =>
      simp only [clearRange, cost]
      have h1 := ih (fun r hr1 hr2 => h r hr1 (by omega))
      rw [run_clearRange, ite_eq_right (by omega)]
      have h2 := h (fr + n) (by omega) (by omega)
      nlinarith

theorem cost_seqs_cons (p : RProg) (ps : List RProg) (R : Regs) :
    cost (seqs (p :: ps)) R = cost p R + cost (seqs ps) (run p R) := rfl

theorem cost_seqs_nil (R : Regs) : cost (seqs []) R = 1 := rfl

end RProg

open RProg

/-! ### Monotone polynomial bounds -/

/-- A monotone function bounded by a polynomial. -/
def PolyM (f : ℕ → ℕ) : Prop := Monotone f ∧ ∃ C a : ℕ, ∀ M, f M ≤ C * (M + 1) ^ a

theorem PolyM.const (c : ℕ) : PolyM fun _ => c :=
  ⟨fun _ _ _ => le_rfl, c, 0, fun _ => by simp⟩

theorem PolyM.id : PolyM fun M => M :=
  ⟨fun _ _ h => h, 1, 1, fun M => by simp⟩

theorem PolyM.add {f g : ℕ → ℕ} (hf : PolyM f) (hg : PolyM g) : PolyM fun M => f M + g M := by
  obtain ⟨mf, C, a, hC⟩ := hf
  obtain ⟨mg, D, b, hD⟩ := hg
  refine ⟨fun x y h => Nat.add_le_add (mf h) (mg h), C + D, max a b, fun M => ?_⟩
  have h1 : (M + 1) ^ a ≤ (M + 1) ^ max a b := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h2 : (M + 1) ^ b ≤ (M + 1) ^ max a b := Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := hC M
  have := hD M
  nlinarith

theorem PolyM.mul {f g : ℕ → ℕ} (hf : PolyM f) (hg : PolyM g) : PolyM fun M => f M * g M := by
  obtain ⟨mf, C, a, hC⟩ := hf
  obtain ⟨mg, D, b, hD⟩ := hg
  refine ⟨fun x y h => Nat.mul_le_mul (mf h) (mg h), C * D, a + b, fun M => ?_⟩
  calc f M * g M ≤ (C * (M + 1) ^ a) * (D * (M + 1) ^ b) := Nat.mul_le_mul (hC M) (hD M)
    _ = C * D * (M + 1) ^ (a + b) := by rw [pow_add]; ring

theorem PolyM.comp {f g : ℕ → ℕ} (hf : PolyM f) (hg : PolyM g) : PolyM fun M => f (g M) := by
  obtain ⟨mf, C, a, hC⟩ := hf
  obtain ⟨mg, D, b, hD⟩ := hg
  refine ⟨fun x y h => mf (mg h), C * (D + 1) ^ a, b * a, fun M => ?_⟩
  exact (hC (g M)).trans (bound_comp_le (hD M))

theorem PolyM.mono_le {f g : ℕ → ℕ} (hg : PolyM g) (h : ∀ M, f M ≤ g M) (hf : Monotone f) :
    PolyM f := by
  obtain ⟨-, C, a, hC⟩ := hg
  exact ⟨hf, C, a, fun M => (h M).trans (hC M)⟩

/-- The length of the output of a term is bounded by a monotone polynomial in its arguments. -/
theorem Cob.polyM_len (v : Cob) : ∃ f, PolyM f ∧ ∀ args, (v.eval args).length ≤ f (maxLen args) := by
  obtain ⟨A, k, h⟩ := Cob.polyLen v
  refine ⟨fun M => A * (M + 1) ^ k, ⟨fun x y hxy => Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) _), A, k, fun _ => le_rfl⟩, h⟩

/-! ### The cost of compiled terms -/

/-- `f` bounds the cost of the compiled program of `v`. -/
def CostBound (v : Cob) (f : ℕ → ℕ) : Prop :=
  ∀ (args : List ℕ) (out fr : ℕ) (R : Regs), (∀ a ∈ args, a < fr) → out < fr → out ∉ args →
    (∀ r, fr ≤ r → R r = []) → R out = [] →
      cost (compile v args out fr) R ≤ f (maxLen (args.map R))

theorem length_le_of_mem_args {args : List ℕ} {R : Regs} {a : ℕ} (ha : a ∈ args) :
    (R a).length ≤ maxLen (args.map R) :=
  length_le_maxLen (List.mem_map_of_mem ha)

theorem polyM_quad : PolyM fun M => M * (2 * M + 10) := PolyM.id.mul ((PolyM.const 2).mul
  PolyM.id |>.add (PolyM.const 10))

theorem cost_proj (i : ℕ) : CostBound (.proj i) fun M => 10 + M * (2 * M + 10) := by
  intro args out fr R hargs hout hna hscr hR
  rw [compile]
  cases hi : args[i]? with
  | none => simp only [cost, hR]; simp only [List.length_nil]; exact Nat.le_add_right_of_le (by norm_num)
  | some a =>
      have ha : a ∈ args := List.mem_of_getElem? hi
      have hne : a ≠ out := fun h => hna (h ▸ ha)
      have h1 := cost_copy_le hne R
      have h2 := length_le_of_mem_args (R := R) ha
      simp only [hR, List.length_nil, mul_zero, zero_add] at h1
      calc _ ≤ _ := h1
        _ ≤ _ := by nlinarith

theorem cost_empty : CostBound .empty fun _ => 5 := by
  intro args out fr R _ _ _ _ hR
  rw [compile]; simp [cost, hR]

theorem cost_app (b : Bool) : CostBound (.app b) fun M => 15 + M * (2 * M + 12) := by
  intro args out fr R hargs hout hna hscr hR
  rw [compile]
  simp only [cost, run_clear, run_push, Function.update_self, hR, List.length_nil, mul_zero,
    zero_add, List.nil_append]
  cases h0 : args[0]? with
  | none => simp only [cost]; exact Nat.le_add_right_of_le (by norm_num)
  | some a =>
      have ha : a ∈ args := List.mem_of_getElem? h0
      have hne : a ≠ out := fun h => hna (h ▸ ha)
      have h1 := cost_append_le a out (Function.update (Function.update R out []) out [b])
      simp only [Function.update_self, Function.update_of_ne hne, List.length_singleton] at h1
      have h2 := length_le_of_mem_args (R := R) ha
      simp only
      nlinarith

theorem cost_smash : CostBound .smash
    fun M => 11 + M * (M * (2 * (M * M + M) + 8) + 2 * M + 8) + 2 * M := by
  intro args out fr R hargs hout hna hscr hR
  rw [compile]
  simp only [cost, hR, List.length_nil, mul_zero, zero_add]
  cases h0 : args[0]? with
  | none => simp only [cost]; exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (by norm_num))
  | some a₀ =>
      cases h1 : args[1]? with
      | none => simp only [cost]; exact Nat.le_add_right_of_le (Nat.le_add_right_of_le (by norm_num))
      | some a₁ =>
          simp only
          have hne₁ : a₁ ≠ out := fun h => hna (h ▸ List.mem_of_getElem? h1)
          have l0 := length_le_of_mem_args (R := R) (List.mem_of_getElem? h0)
          have l1 := length_le_of_mem_args (R := R) (List.mem_of_getElem? h1)
          set M := maxLen (args.map R)
          set R0 := Function.update R out []
          have hR0o : R0 out = [] := Function.update_self _ _ _
          have hR0a₀ : R0 a₀ = R a₀ := Function.update_of_ne (fun h => hna
            (by rw [← h]; exact List.mem_of_getElem? h0)) _ _
          have hR0a₁ : R0 a₁ = R a₁ := Function.update_of_ne hne₁ _ _
          rw [cost]
          set B := (R a₁).length * (2 * ((R a₀).length * (R a₁).length + (R a₁).length) + 8) +
            2 * (R a₁).length + 5
          have hit := iterCost_le (c₀ := cost (.forBits a₁ (.push out true) (.push out true)))
            (c₁ := cost (.forBits a₁ (.push out true) (.push out true)))
            (f₀ := run (.forBits a₁ (.push out true) (.push out true)))
            (f₁ := run (.forBits a₁ (.push out true) (.push out true))) B
            (fun L S => S a₁ = R a₁ ∧ (S out).length + L.length * (R a₁).length ≤
              (R a₀).length * (R a₁).length)
            (fun b L S hS => by
              obtain ⟨hSa, hSo⟩ := hS
              simp only [List.length_cons] at hSo
              have hc := cost_pushLoop a₁ out true true S
              have hr := run_forBits_push hne₁ S
              rw [hSa] at hc hr
              have key : cost (.forBits a₁ (.push out true) (.push out true)) S ≤ B ∧
                  (run (.forBits a₁ (.push out true) (.push out true)) S a₁ = R a₁ ∧
                    (run (.forBits a₁ (.push out true) (.push out true)) S out).length +
                      L.length * (R a₁).length ≤ (R a₀).length * (R a₁).length) := by
                have hx : (S out).length ≤ (R a₀).length * (R a₁).length :=
                  le_trans (Nat.le_add_right _ _) hSo
                have hx2 := Nat.mul_le_mul_left ((R a₁).length * 2) hx
                refine ⟨hc.trans (by simp only [B]; nlinarith), ?_, ?_⟩
                · rw [hr, Function.update_of_ne hne₁, hSa]
                · rw [hr, Function.update_self, List.length_append, List.length_replicate]
                  nlinarith
              cases b <;> exact key)
            (R0 a₀) R0 ⟨hR0a₁, by rw [hR0o, hR0a₀]; simp⟩
          rw [hR0a₀] at hit
          have hB : B ≤ M * (2 * (M * M + M) + 8) + 2 * M + 5 := by
            simp only [B]
            have : (R a₀).length * (R a₁).length ≤ M * M := Nat.mul_le_mul l0 l1
            nlinarith
          simp only [run_clear]
          rw [show Function.update R out [] = R0 from rfl, hR0a₀]
          nlinarith

/-- The cost of a compiled list of terms. -/
theorem cost_list (gs : List Cob) (F : Cob → ℕ → ℕ) (hF : ∀ g ∈ gs, CostBound g (F g))
    (hspec : ∀ g ∈ gs, ∀ args out fr, Spec g args out fr) :
    ∀ (args : List ℕ) (j sc : ℕ) (R : Regs), (∀ a ∈ args, a < j) → j + gs.length ≤ sc →
      (∀ r, j ≤ r → R r = []) →
      cost (compileList gs args j sc) R ≤ (gs.map fun g => F g (maxLen (args.map R))).sum + 1 := by
  induction gs with
  | nil => intro args j sc R _ _ _; simp [compileList, cost]
  | cons g gs ih =>
      intro args j sc R hargs hlen hscr
      simp only [List.length_cons] at hlen
      rw [compileList, cost]
      have hg := hF g List.mem_cons_self args j sc R (fun a ha => by have := hargs a ha; omega)
        (by omega) (fun h => by have := hargs j h; omega) (fun r hr => hscr r (by omega))
        (hscr j le_rfl)
      obtain ⟨_, g2, g3⟩ := hspec g List.mem_cons_self args j sc R
        (fun a ha => by have := hargs a ha; omega) (by omega)
        (fun h => by have := hargs j h; omega) (fun r hr => hscr r (by omega))
      set R1 := run (compile g args j sc) R
      have hmap : args.map R1 = args.map R :=
        List.map_congr_left fun a ha => g2 a (by have := hargs a ha; omega)
          (by have := hargs a ha; omega)
      have hrest := ih (fun g' hg' => hF g' (List.mem_cons_of_mem _ hg'))
        (fun g' hg' => hspec g' (List.mem_cons_of_mem _ hg')) args (j + 1) sc R1
        (fun a ha => by have := hargs a ha; omega) (by omega)
        (fun r hr => by
          by_cases hrs : r < sc
          · rw [g2 r (by omega) hrs]; exact hscr r (by omega)
          · exact g3 r (by omega))
      rw [hmap] at hrest
      simp only [List.map_cons, List.sum_cons]
      omega

theorem PolyM.sum (gs : List Cob) (F : Cob → ℕ → ℕ) (hF : ∀ g ∈ gs, PolyM (F g)) :
    PolyM fun M => (gs.map fun g => F g M).sum := by
  induction gs with
  | nil => simpa using PolyM.const 0
  | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hF g List.mem_cons_self).add (ih fun g' hg' => hF g' (List.mem_cons_of_mem _ hg'))

theorem maxLen_le_of {L : List Word} {B : ℕ} (h : ∀ x ∈ L, x.length ≤ B) : maxLen L ≤ B := by
  induction L with
  | nil => simp
  | cons x L ih =>
      rw [maxLen_cons]
      exact max_le (h x List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem cost_comp (f : Cob) (gs : List Cob) (ff : ℕ → ℕ) (hff : PolyM ff) (hfc : CostBound f ff)
    (hfs : ∀ args out fr, Spec f args out fr) (F : Cob → ℕ → ℕ) (hFp : ∀ g ∈ gs, PolyM (F g))
    (hFc : ∀ g ∈ gs, CostBound g (F g)) (hgs : ∀ g ∈ gs, ∀ args out fr, Spec g args out fr) :
    ∃ fc, PolyM fc ∧ CostBound (.comp f gs) fc := by
  choose L hLp hLb using Cob.polyM_len
  let Ls : ℕ → ℕ := fun M => (gs.map fun g => L g M).sum
  have hLs : PolyM Ls := PolyM.sum gs L fun g _ => hLp g
  refine ⟨fun M => (gs.map fun g => F g M).sum + 1 + ff (Ls M) + (gs.length * (2 * Ls M + 6) + 1),
    (((PolyM.sum gs F hFp).add (PolyM.const 1)).add (hff.comp hLs)).add
      (((PolyM.const gs.length).mul (((PolyM.const 2).mul hLs).add (PolyM.const 6))).add
        (PolyM.const 1)), ?_⟩
  intro args out fr R hargs hout hna hscr hR
  rw [compile]
  simp only [cost]
  have c1 := cost_list gs F hFc hgs args fr (fr + gs.length) R hargs le_rfl hscr
  obtain ⟨l1, l2, l3⟩ := spec_list gs hgs args fr (fr + gs.length) R hargs le_rfl
    (fun r hr => hscr r (by omega))
  have hlen : ∀ i (hi : i < gs.length),
      (run (compileList gs args fr (fr + gs.length)) R (fr + i)).length ≤
        Ls (maxLen (args.map R)) := by
    intro i hi
    rw [l1 i hi]
    refine (hLb _ _).trans ?_
    exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem hi))
  have hmax : maxLen ((List.range' fr gs.length).map
      (run (compileList gs args fr (fr + gs.length)) R)) ≤ Ls (maxLen (args.map R)) := by
    refine maxLen_le_of fun x hx => ?_
    simp only [List.mem_map, List.mem_range'] at hx
    obtain ⟨r, ⟨i, hi, rfl⟩, rfl⟩ := hx
    simpa using hlen i hi
  have c2 := hfc (List.range' fr gs.length) out (fr + gs.length)
    (run (compileList gs args fr (fr + gs.length)) R)
    (fun a ha => by simp [List.mem_range'] at ha; omega) (by omega)
    (fun h => by simp [List.mem_range'] at h; omega) l3 (by rw [l2 out (Or.inl hout)]; exact hR)
  obtain ⟨_, f2, _⟩ := hfs (List.range' fr gs.length) out (fr + gs.length)
    (run (compileList gs args fr (fr + gs.length)) R)
    (fun a ha => by simp [List.mem_range'] at ha; omega) (by omega)
    (fun h => by simp [List.mem_range'] at h; omega) l3
  have c3 := cost_clearRange_le fr gs.length (Ls (maxLen (args.map R)))
    (run (compile f (List.range' fr gs.length) out (fr + gs.length))
      (run (compileList gs args fr (fr + gs.length)) R)) (fun r hr1 hr2 => by
      rw [f2 r (by omega) (by omega)]
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hr1
      exact hlen i (by omega))
  have c2' := c2.trans (hff.1 hmax)
  omega

theorem iterCost_append {c₀ c₁ : Regs → ℕ} {f₀ f₁ : Regs → Regs} (A B : List Bool) (S : Regs) :
    iterCost c₀ c₁ f₀ f₁ (A ++ B) S = iterCost c₀ c₁ f₀ f₁ A S +
      iterCost c₀ c₁ f₀ f₁ B (A.foldl (fun S' b => bif b then f₁ S' else f₀ S') S) := by
  induction A generalizing S with
  | nil => simp [iterCost]
  | cons b A ih => simp only [List.cons_append, iterCost, ih, List.foldl_cons]; omega

/-- The quadratic bound on the cost of the auxiliary instructions of a recursion step. -/
def auxQ (W : ℕ) : ℕ := 4 * W * W + 20 * W + 20

theorem bRecBody_cost {F h bd : Cob} {args : List ℕ} {fr : ℕ} {R : Regs} {b : Bool} {sl : Word}
    (hargs : ∀ a ∈ args, a < fr)
    (hh : Spec h (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
    (hbd : Spec bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5))
    {fh fbd : ℕ → ℕ} (mfh : Monotone fh) (mfbd : Monotone fbd)
    (hhc : CostBound h fh) (hbdc : CostBound bd fbd) {W : ℕ}
    (hW1 : maxLen ((fr :: (fr + 1) :: args.tail).map (fun r => if r = fr then sl else
      if r = fr + 1 then F.eval (sl :: args.tail.map R) else R r)) ≤ W)
    (hW2 : maxLen ((b :: sl) :: args.tail.map R) ≤ W)
    (hWv : (F.eval (sl :: args.tail.map R)).length ≤ W)
    (hWt : (h.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R)).length ≤ W)
    (hWw : (bd.eval ((b :: sl) :: args.tail.map R)).length ≤ W)
    {S : Regs} (hS : BInv F (args.tail.map R) R fr sl S) :
    cost (bRecBody (compile h (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
      (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) b fr) S ≤
        fh W + fbd W + 10 * auxQ W := by
  obtain ⟨s0, s1, s2, s3, s4, slow, shigh⟩ := hS
  have htail : ∀ a ∈ args.tail, a < fr := fun a ha => hargs a (List.mem_of_mem_tail ha)
  have hYs : args.tail.map S = args.tail.map R :=
    List.map_congr_left fun a ha => slow a (htail a ha)
  have hsl1 : sl.length + 1 ≤ W := le_trans (by simp) hW2
  have hsl : sl.length ≤ W := by omega
  simp only [bRecBody, cost_seqs_cons]
  have hargs1 : ∀ a ∈ (fr :: (fr + 1) :: args.tail), a < fr + 5 := fun a ha => by
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · omega
    · omega
    · have := htail a ha; omega
  have hout1 : fr + 2 ∉ (fr :: (fr + 1) :: args.tail) := fun ha => by
    simp only [List.mem_cons] at ha
    rcases ha with ha | ha | ha
    · omega
    · omega
    · have := htail _ ha; omega
  -- the step program
  have hmap1 : (fr :: (fr + 1) :: args.tail).map S = (fr :: (fr + 1) :: args.tail).map
      (fun r => if r = fr then sl else if r = fr + 1 then F.eval (sl :: args.tail.map R) else R r) := by
    simp only [List.map_cons, ite_true, s0, s1, ite_eq_right (show fr + 1 ≠ fr by omega)]
    rw [hYs]
    congr 2
    refine (List.map_congr_left fun a ha => ?_).symm
    have := htail a ha
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have c1 := hhc _ _ _ S hargs1 (by omega) hout1 shigh s2
  rw [hmap1] at c1
  replace c1 := c1.trans (mfh hW1)
  obtain ⟨h1, h2, h3⟩ := hh S hargs1 (by omega) hout1 shigh
  set S1 := run (compile h (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5)) S
  have e1 : S1 (fr + 2) = h.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R) := by
    rw [h1]; simp [s0, s1, hYs]
  have e13 : S1 (fr + 3) = [] := by rw [h2 _ (by omega) (by omega)]; exact s3
  have e10 : S1 fr = sl := by rw [h2 _ (by omega) (by omega)]; exact s0
  -- forming `b :: sl`
  set S4 := run (append fr (fr + 3)) (run (.push (fr + 3) b) (run (.clear (fr + 3)) S1))
  have c2 : cost (.clear (fr + 3)) S1 ≤ auxQ W := by simp [cost, e13, auxQ]
  have c3 : cost (.push (fr + 3) b) (run (.clear (fr + 3)) S1) ≤ auxQ W := by
    simp [cost, auxQ]
  have c4 : cost (append fr (fr + 3)) (run (.push (fr + 3) b) (run (.clear (fr + 3)) S1)) ≤
      auxQ W := by
    refine (cost_append_le _ _ _).trans ?_
    simp only [run_push, run_clear, Function.update_self, Function.update_of_ne
      (show fr ≠ fr + 3 by omega), e10, List.nil_append, List.length_singleton]
    simp only [auxQ]; nlinarith
  have e4 : S4 = Function.update S1 (fr + 3) (b :: sl) := by
    simp only [S4, run_push, run_clear, run_append (show fr ≠ fr + 3 by omega)]
    funext r
    by_cases hr : r = fr + 3
    · subst hr
      simp only [Function.update_self, Function.update_of_ne (show fr ≠ fr + 3 by omega), e10]
      rfl
    · simp [Function.update_of_ne hr]
  -- the bound program
  have hargs2 : ∀ a ∈ ((fr + 3) :: args.tail), a < fr + 5 := fun a ha => by
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · omega
    · have := htail a ha; omega
  have hout2 : fr + 4 ∉ ((fr + 3) :: args.tail) := fun ha => by
    simp only [List.mem_cons] at ha
    rcases ha with ha | ha
    · omega
    · have := htail _ ha; omega
  have hscr4 : ∀ r, fr + 5 ≤ r → S4 r = [] := fun r hr => by
    rw [e4, Function.update_of_ne (by omega)]; exact h3 r hr
  have hYs4 : args.tail.map S4 = args.tail.map R := by
    rw [e4]
    refine List.map_congr_left fun a ha => ?_
    have := htail a ha
    rw [Function.update_of_ne (by omega), h2 a (by omega) (by omega), slow a this]
  have c5 : cost (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) S4 ≤ fbd W := by
    refine (hbdc _ _ _ S4 hargs2 (by omega) hout2 hscr4
      (by rw [e4, Function.update_of_ne (by omega), h2 _ (by omega) (by omega)]; exact s4)).trans ?_
    rw [List.map_cons, hYs4, e4, Function.update_self]
    exact mfbd hW2
  obtain ⟨b1, b2, b3⟩ := hbd S4 hargs2 (by omega) hout2 hscr4
  set S5 := run (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) S4
  have e54 : S5 (fr + 4) = bd.eval ((b :: sl) :: args.tail.map R) := by
    rw [b1, List.map_cons, hYs4, e4, Function.update_self]
  have e52 : S5 (fr + 2) = h.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R) := by
    rw [b2 _ (by omega) (by omega), e4, Function.update_of_ne (by omega), e1]
  have e53 : S5 (fr + 3) = b :: sl := by
    rw [b2 _ (by omega) (by omega), e4]; simp
  have e51 : S5 (fr + 1) = F.eval (sl :: args.tail.map R) := by
    rw [b2 _ (by omega) (by omega), e4, Function.update_of_ne (by omega),
      h2 _ (by omega) (by omega), s1]
  have e50 : S5 fr = sl := by
    rw [b2 _ (by omega) (by omega), e4, Function.update_of_ne (by omega), e10]
  -- the auxiliary instructions
  have c6 : cost (copy (fr + 2) (fr + 1)) S5 ≤ auxQ W := by
    refine (cost_copy_le (by omega) _).trans ?_
    rw [e51, e52]; simp only [auxQ]; nlinarith
  have q1 : 1 ≤ auxQ W := by simp only [auxQ]; omega
  refine le_trans (Nat.add_le_add c1 (Nat.add_le_add (?_ : _ ≤ auxQ W)
    (Nat.add_le_add (?_ : _ ≤ auxQ W) (Nat.add_le_add c4 (Nat.add_le_add c5
    (Nat.add_le_add c6 (Nat.add_le_add (?_ : _ ≤ auxQ W) (Nat.add_le_add (?_ : _ ≤ auxQ W)
    (Nat.add_le_add (?_ : _ ≤ auxQ W) (Nat.add_le_add (?_ : _ ≤ auxQ W)
    (Nat.add_le_add (?_ : _ ≤ auxQ W) (?_ : _ ≤ auxQ W)))))))))))) (by omega)
  · simp [cost, e13, auxQ]
  · simp [cost, auxQ]
  · rw [run_copy (show fr + 2 ≠ fr + 1 by omega)]
    simp only [cost, Function.update_self, Function.update_of_ne (show fr + 4 ≠ fr + 1 by omega),
      e52, e54]
    simp only [auxQ]; nlinarith
  · rw [run_copy (show fr + 2 ≠ fr + 1 by omega), run_trunc]
    refine (cost_copy_le (by omega) _).trans ?_
    simp only [Function.update_of_ne (show fr ≠ fr + 1 by omega),
      Function.update_of_ne (show fr + 3 ≠ fr + 1 by omega), e50, e53, List.length_cons]
    have := Nat.mul_le_mul hsl1 hsl1
    simp only [auxQ]; nlinarith
  · rw [run_copy (show fr + 2 ≠ fr + 1 by omega), run_trunc, run_copy (show fr + 3 ≠ fr by omega)]
    simp only [cost, Function.update_of_ne (show fr + 2 ≠ fr by omega),
      Function.update_of_ne (show fr + 2 ≠ fr + 1 by omega), e52]
    simp only [auxQ]; nlinarith
  · rw [run_copy (show fr + 2 ≠ fr + 1 by omega), run_trunc, run_copy (show fr + 3 ≠ fr by omega)]
    simp only [cost, run_clear, Function.update_of_ne (show fr + 3 ≠ fr + 2 by omega),
      Function.update_of_ne (show fr + 3 ≠ fr by omega),
      Function.update_of_ne (show fr + 3 ≠ fr + 1 by omega), e53, List.length_cons]
    simp only [auxQ]; nlinarith
  · rw [run_copy (show fr + 2 ≠ fr + 1 by omega), run_trunc, run_copy (show fr + 3 ≠ fr by omega)]
    simp only [cost, run_clear, Function.update_of_ne (show fr + 4 ≠ fr + 3 by omega),
      Function.update_of_ne (show fr + 4 ≠ fr + 2 by omega),
      Function.update_of_ne (show fr + 4 ≠ fr by omega),
      Function.update_of_ne (show fr + 4 ≠ fr + 1 by omega), e54]
    simp only [auxQ]; nlinarith
  · exact q1

theorem bRec_cost (g h₀ h₁ bd : Cob)
    (hgs : ∀ args out fr, Spec g args out fr) (hh₀s : ∀ args out fr, Spec h₀ args out fr)
    (hh₁s : ∀ args out fr, Spec h₁ args out fr) (hbds : ∀ args out fr, Spec bd args out fr)
    {fg fh₀ fh₁ fbd : ℕ → ℕ} (pg : PolyM fg) (ph₀ : PolyM fh₀) (ph₁ : PolyM fh₁) (pbd : PolyM fbd)
    (cg : CostBound g fg) (ch₀ : CostBound h₀ fh₀) (ch₁ : CostBound h₁ fh₁)
    (cbd : CostBound bd fbd) :
    ∃ fc, PolyM fc ∧ CostBound (.bRec g h₀ h₁ bd) fc := by
  set F := Cob.bRec g h₀ h₁ bd
  obtain ⟨LF, pLF, hLF⟩ := Cob.polyM_len F
  obtain ⟨L₀, pL₀, hL₀⟩ := Cob.polyM_len h₀
  obtain ⟨L₁, pL₁, hL₁⟩ := Cob.polyM_len h₁
  obtain ⟨Lb, pLb, hLb⟩ := Cob.polyM_len bd
  let W : ℕ → ℕ := fun M => M + 1 + LF M + (L₀ (M + LF M) + L₁ (M + LF M)) + Lb (M + 1)
  have pW : PolyM W :=
    (((PolyM.id.add (PolyM.const 1)).add pLF).add
      ((pL₀.comp (PolyM.id.add pLF)).add (pL₁.comp (PolyM.id.add pLF)))).add
      (pLb.comp (PolyM.id.add (PolyM.const 1)))
  let B : ℕ → ℕ := fun M => (fh₀ (W M) + fh₁ (W M)) + fbd (W M) + 10 * auxQ (W M)
  have pauxQ : PolyM auxQ := by
    have : PolyM fun W => 4 * W * W + 20 * W + 20 :=
      ((((PolyM.const 4).mul PolyM.id).mul PolyM.id).add ((PolyM.const 20).mul PolyM.id)).add
        (PolyM.const 20)
    exact this
  have pB : PolyM B :=
    (((ph₀.comp pW).add (ph₁.comp pW)).add (pbd.comp pW)).add ((PolyM.const 10).mul (pauxQ.comp pW))
  have p1 : PolyM fun M => M * (B M + 3) + 2 * M + 5 :=
    ((PolyM.id.mul (pB.add (PolyM.const 3))).add ((PolyM.const 2).mul PolyM.id)).add
      (PolyM.const 5)
  have p2 : PolyM fun M => 10 + LF M * (2 * LF M + 10) :=
    (PolyM.const 10).add (pLF.mul (((PolyM.const 2).mul pLF).add (PolyM.const 10)))
  have p3 : PolyM fun M => 5 * (2 * (M + LF M) + 6) + 1 :=
    ((PolyM.const 5).mul (((PolyM.const 2).mul (PolyM.id.add pLF)).add (PolyM.const 6))).add
      (PolyM.const 1)
  refine ⟨fun M => fg M + (M * (B M + 3) + 2 * M + 5) + (10 + LF M * (2 * LF M + 10)) +
      (5 * (2 * (M + LF M) + 6) + 1) + 1, (((pg.add p1).add p2).add p3).add (PolyM.const 1), ?_⟩
  intro args out fr R hargs hout hna hscr hR
  have mW := pW.1
  have mB := pB.1
  have htail : ∀ a ∈ args.tail, a < fr := fun a ha => hargs a (List.mem_of_mem_tail ha)
  have hYsM : maxLen (args.tail.map R) ≤ maxLen (args.map R) := by
    cases args with
    | nil => simp
    | cons a l => simp only [List.tail_cons, List.map_cons, maxLen_cons]; exact le_max_right _ _
  set M := maxLen (args.map R)
  rw [compile]
  simp only [cost_seqs_cons, cost_seqs_nil]
  -- the base
  have c1 := (cg args.tail (fr + 1) (fr + 5) R (fun a ha => by have := htail a ha; omega)
    (by omega) (fun ha => by have := htail _ ha; omega) (fun r hr => hscr r (by omega))
    (hscr _ (by omega))).trans (pg.1 hYsM)
  obtain ⟨g1, g2, g3⟩ := hgs args.tail (fr + 1) (fr + 5) R
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
  -- the bodies
  set body₀ := bRecBody (compile h₀ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
    (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) false fr
  set body₁ := bRecBody (compile h₁ (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
    (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) true fr
  have hinv : ∀ L : Word, BInv F (args.tail.map R) R fr L
      (L.foldr (fun b S => bif b then run body₁ S else run body₀ S) R1) := by
    intro L
    induction L with
    | nil => exact hinv0
    | cons b L ih =>
        rw [List.foldr_cons]
        cases b with
        | false =>
            exact bRecBody_spec hargs (hh₀s _ _ _) (hbds _ _ _) (by rw [Cob.eval_bRec_cons]; rfl) ih
        | true =>
            exact bRecBody_spec hargs (hh₁s _ _ _) (hbds _ _ _) (by rw [Cob.eval_bRec_cons]; rfl) ih
  -- one iteration
  have hbody : ∀ (b : Bool) (sl : Word), sl.length ≤ M → ∀ S, BInv F (args.tail.map R) R fr sl S →
      (bif b then cost body₁ S else cost body₀ S) ≤ B M := by
    intro b sl hsl S hS
    have hv : (F.eval (sl :: args.tail.map R)).length ≤ LF M :=
      (hLF _).trans (pLF.1 (by rw [maxLen_cons]; exact max_le hsl hYsM))
    have hvsl : maxLen (sl :: args.tail.map R) ≤ M := by rw [maxLen_cons]; exact max_le hsl hYsM
    have hW1 : maxLen ((fr :: (fr + 1) :: args.tail).map (fun r => if r = fr then sl else
        if r = fr + 1 then F.eval (sl :: args.tail.map R) else R r)) ≤ W M := by
      refine maxLen_le_of fun x hx => ?_
      simp only [List.map_cons, List.mem_cons, ite_true, ite_eq_right (show fr + 1 ≠ fr by omega),
        List.mem_map] at hx
      rcases hx with rfl | rfl | ⟨r, hr, rfl⟩
      · simp only [W]; omega
      · simp only [W]; omega
      · have := htail r hr
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        have := length_le_maxLen (List.mem_map_of_mem (f := R) hr)
        simp only [W]; omega
    have hmax3 : maxLen (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R) ≤ M + LF M := by
      simp only [maxLen_cons]
      exact max_le (by omega) (max_le (by omega) (by omega))
    have hW2 : maxLen ((b :: sl) :: args.tail.map R) ≤ W M := by
      rw [maxLen_cons]
      simp only [List.length_cons, W]
      exact max_le (by omega) (by omega)
    have hmax4 : maxLen ((b :: sl) :: args.tail.map R) ≤ M + 1 := by
      rw [maxLen_cons]; simp only [List.length_cons]; exact max_le (by omega) (by omega)
    have hWw : (bd.eval ((b :: sl) :: args.tail.map R)).length ≤ W M := by
      have := (hLb _).trans (pLb.1 hmax4)
      simp only [W]; omega
    cases b with
    | false =>
        have hWt : (h₀.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R)).length ≤
            W M := by
          have := (hL₀ _).trans (pL₀.1 hmax3)
          simp only [W]; omega
        have : cost body₀ S ≤ fh₀ (W M) + fbd (W M) + 10 * auxQ (W M) :=
          bRecBody_cost (F := F) hargs (hh₀s _ _ _) (hbds _ _ _) ph₀.1 pbd.1 ch₀ cbd hW1 hW2
            (by simp only [W]; omega) hWt hWw hS
        simp only [Bool.cond_false]
        have hB : B M = fh₀ (W M) + fh₁ (W M) + fbd (W M) + 10 * auxQ (W M) := rfl
        omega
    | true =>
        have hWt : (h₁.eval (sl :: F.eval (sl :: args.tail.map R) :: args.tail.map R)).length ≤
            W M := by
          have := (hL₁ _).trans (pL₁.1 hmax3)
          simp only [W]; omega
        have : cost body₁ S ≤ fh₁ (W M) + fbd (W M) + 10 * auxQ (W M) :=
          bRecBody_cost (F := F) hargs (hh₁s _ _ _) (hbds _ _ _) ph₁.1 pbd.1 ch₁ cbd hW1 hW2
            (by simp only [W]; omega) hWt hWw hS
        simp only [Bool.cond_true]
        have hB : B M = fh₀ (W M) + fh₁ (W M) + fbd (W M) + 10 * auxQ (W M) := rfl
        omega
  -- all iterations
  have hiter : ∀ L : Word, L.length ≤ M →
      iterCost (cost body₀) (cost body₁) (run body₀) (run body₁) L.reverse R1 ≤
        L.length * (B M + 3) := by
    intro L
    induction L with
    | nil => intro _; simp [iterCost]
    | cons b L ih =>
        intro hL
        simp only [List.length_cons] at hL
        rw [List.reverse_cons, iterCost_append, List.foldl_reverse]
        have h1 := ih (by omega)
        have h2 := hbody b L (by omega) _ (hinv L)
        simp only [iterCost]
        simp only [List.length_cons]
        nlinarith
  -- the loop and what follows it
  have hfacts : ∃ R2 : Regs, cost (bRecLoop args[0]? body₀ body₁) R1 ≤ M * (B M + 3) + 2 * M + 5 ∧
      run (bRecLoop args[0]? body₀ body₁) R1 = R2 ∧
      R2 (fr + 1) = F.eval (args.map R) ∧ (∀ r, r < fr → R2 r = R r) ∧
      (R2 fr).length ≤ M ∧ R2 (fr + 2) = [] ∧ R2 (fr + 3) = [] ∧ R2 (fr + 4) = [] ∧
      (∀ r, fr + 5 ≤ r → R2 r = []) := by
    cases hx : args[0]? with
    | none =>
        have hnil : args = [] := by
          cases args with
          | nil => rfl
          | cons a l => simp at hx
        obtain ⟨i0, i1, i2, i3, i4, ilow, ihigh⟩ := hinv0
        refine ⟨R1, by simp [bRecLoop, cost], by simp [bRecLoop], ?_, ilow, by rw [i0]; simp,
          i2, i3, i4, ihigh⟩
        rw [i1, hnil]
        simp [F, Cob.eval_bRec]
    | some x =>
        have hxmem : args = x :: args.tail := by
          cases args with
          | nil => simp at hx
          | cons a l => simp at hx; subst hx; rfl
        have hxlt : x < fr := hargs x (by rw [hxmem]; exact List.mem_cons_self)
        have hR1x : R1 x = R x := g2 x (by omega) (by omega)
        have hxM : (R x).length ≤ M := length_le_of_mem_args (by rw [hxmem]; exact List.mem_cons_self)
        obtain ⟨i0, i1, i2, i3, i4, ilow, ihigh⟩ := hinv (R x)
        refine ⟨(R x).foldr (fun b S => bif b then run body₁ S else run body₀ S) R1, ?_, ?_,
          ?_, ilow, by rw [i0]; exact hxM, i2, i3, i4, ihigh⟩
        · simp only [bRecLoop, cost, hR1x]
          have := hiter (R x) hxM
          nlinarith
        · simp only [bRecLoop, run, hR1x]
        · rw [i1, hxmem]; simp
  obtain ⟨R2, cl, hrun, f1, flow, f0, f2, f3, f4, fhigh⟩ := hfacts
  rw [hrun]
  have hne : fr + 1 ≠ out := by omega
  have hvlen : (F.eval (args.map R)).length ≤ LF M := hLF _
  have c3 := cost_copy_le hne R2
  rw [f1, flow out hout, hR] at c3
  have c4 := cost_clearRange_le fr 5 (M + LF M) (run (copy (fr + 1) out) R2) (fun r hr1 hr2 => by
    rw [run_copy hne, Function.update_of_ne (by omega)]
    rcases (by omega : r = fr ∨ r = fr + 1 ∨ r = fr + 2 ∨ r = fr + 3 ∨ r = fr + 4) with
      rfl | rfl | rfl | rfl | rfl
    · omega
    · rw [f1]; omega
    · rw [f2]; simp
    · rw [f3]; simp
    · rw [f4]; simp)
  simp only [List.length_nil, mul_zero, zero_add] at c3
  have : (F.eval (args.map R)).length * (2 * (F.eval (args.map R)).length + 8) +
      2 * (F.eval (args.map R)).length ≤ LF M * (2 * LF M + 10) := by nlinarith
  omega

/-- **The cost of a compiled term is polynomial.** -/
theorem compile_cost_aux : ∀ (n : ℕ) (v : Cob), sizeOf v ≤ n → ∃ f, PolyM f ∧ CostBound v f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    cases v with
    | proj i =>
        exact ⟨_, (PolyM.const 10).add (PolyM.id.mul (((PolyM.const 2).mul PolyM.id).add
          (PolyM.const 10))), cost_proj i⟩
    | empty => exact ⟨_, PolyM.const 5, cost_empty⟩
    | app b =>
        exact ⟨_, (PolyM.const 15).add (PolyM.id.mul (((PolyM.const 2).mul PolyM.id).add
          (PolyM.const 12))), cost_app b⟩
    | smash =>
        refine ⟨_, ?_, cost_smash⟩
        have q1 : PolyM fun M => M * (2 * (M * M + M) + 8) :=
          PolyM.id.mul (((PolyM.const 2).mul ((PolyM.id.mul PolyM.id).add PolyM.id)).add
            (PolyM.const 8))
        have q2 : PolyM fun M => M * (M * (2 * (M * M + M) + 8) + 2 * M + 8) :=
          PolyM.id.mul ((q1.add ((PolyM.const 2).mul PolyM.id)).add (PolyM.const 8))
        exact ((PolyM.const 11).add q2).add ((PolyM.const 2).mul PolyM.id)
    | comp f gs =>
        simp only [Cob.comp.sizeOf_spec] at hv
        obtain ⟨ff, pff, cff⟩ := ih (sizeOf f) (by omega) f le_rfl
        have hgs : ∀ g ∈ gs, ∃ fg, PolyM fg ∧ CostBound g fg := fun g hg =>
          ih (sizeOf g) (by have := List.sizeOf_lt_of_mem hg; omega) g le_rfl
        choose! Fg pFg cFg using hgs
        exact cost_comp f gs ff pff cff (compile_spec f) Fg pFg cFg
          (fun g _ => compile_spec g)
    | bRec g h₀ h₁ bd =>
        simp only [Cob.bRec.sizeOf_spec] at hv
        obtain ⟨fg, pg, cg⟩ := ih _ (by omega) g le_rfl
        obtain ⟨f0, p0, c0⟩ := ih _ (by omega) h₀ le_rfl
        obtain ⟨f1, p1, c1⟩ := ih _ (by omega) h₁ le_rfl
        obtain ⟨fb, pb, cb⟩ := ih _ (by omega) bd le_rfl
        exact bRec_cost g h₀ h₁ bd (compile_spec g) (compile_spec h₀) (compile_spec h₁)
          (compile_spec bd) pg p0 p1 pb cg c0 c1 cb

theorem compile_cost (v : Cob) : ∃ f, PolyM f ∧ CostBound v f :=
  compile_cost_aux (sizeOf v) v le_rfl

end CobMT

end Complexity
