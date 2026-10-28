/-
**Cobham's `P` is polynomial time on multi-tape machines** — task `M26-UNIFY-DEPTHTHREE-COBMT`,
the assembly, and task `M27-POLYTIME-MODEL-EQUIV`.

The register program of a Cobham term `v`, compiled with the input in register `0` and the result
in register `1` (`Complexity.CobMT.compile`), is flattened between an initialisation, which copies
the input into register `0`, and a final test of register `1`; the interpreter of
`Start/CobMultiTape.lean`, with one tape per register, runs it (`Complexity.CobMT.sim`).

* `Complexity.CobMT.Within` — a program is well formed and uses only registers of a given set;
  `Complexity.CobMT.compile_good` — compiled programs are, for distinct arguments;
* `Complexity.CobMT.cobMachine` — the multi-tape machine of a Cobham term;
* **`Complexity.CobMT.cobMachine_haltsIn`** — on input `x` it halts within `2 |x| + 6 + f |x|`
  steps, for a monotone polynomial `f`, accepting iff `v.eval [x]` is not empty;
* **`Complexity.CobMT.multiTape_of_inP`** — every language in `P` is decided by a multi-tape
  machine within `C (n + 1) ^ a` steps (`multiTape_decide_of_inP`: the output is `decide (L w)`);
* **`Complexity.CobMT.inP_iff_multiTape`** — with
  `Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn`, Cobham's `P` is exactly the class of
  languages decided by `FiniteMultiTapeMachine`s in polynomially many steps.
-/

import Start.CobMultiTapeSim
import Start.MultiTapeCobham

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobMT

open DepthThreeLowerBound RProg

namespace RProg

/-- A bound on the registers a program uses. -/
def bound : RProg → ℕ
  | .skip => 0
  | .clear r => r + 1
  | .push r _ => r + 1
  | .trunc r s => r + s + 1
  | .seq p q => bound p + bound q
  | .forBits r p₀ p₁ => r + 1 + bound p₀ + bound p₁
  | .forBitsRev r p₀ p₁ => r + 1 + bound p₀ + bound p₁

theorem lt_bound (p : RProg) : ∀ {x : ℕ}, Touches p x → x < bound p := by
  induction p with
  | skip => intro x h; simp only [Touches] at h
  | clear r => intro x h; simp only [Touches] at h; simp only [bound]; omega
  | push r b => intro x h; simp only [Touches] at h; simp only [bound]; omega
  | trunc r s => intro x h; simp only [Touches] at h; simp only [bound]; omega
  | seq p q ihp ihq =>
      intro x h
      simp only [Touches] at h
      simp only [bound]
      rcases h with h | h
      · have := ihp h; omega
      · have := ihq h; omega
  | forBits r p₀ p₁ ih₀ ih₁ =>
      intro x h
      simp only [Touches] at h
      simp only [bound]
      rcases h with h | h | h
      · omega
      · have := ih₀ h; omega
      · have := ih₁ h; omega
  | forBitsRev r p₀ p₁ ih₀ ih₁ =>
      intro x h
      simp only [Touches] at h
      simp only [bound]
      rcases h with h | h | h
      · omega
      · have := ih₀ h; omega
      · have := ih₁ h; omega

end RProg

/-! ### Well-formed compiled programs -/

/-- `p` is well formed and uses only registers satisfying `P`. -/
def Within (P : ℕ → Prop) (p : RProg) : Prop := WF p ∧ ∀ x, Touches p x → P x

section Within

variable {P Q : ℕ → Prop}

theorem Within.mono {p : RProg} (h : Within P p) (hPQ : ∀ x, P x → Q x) : Within Q p :=
  ⟨h.1, fun x hx => hPQ x (h.2 x hx)⟩

theorem Within.skip : Within P .skip :=
  ⟨by simp only [WF], fun _ h => by simp only [Touches] at h⟩

theorem Within.clear {r : ℕ} (hr : P r) : Within P (.clear r) :=
  ⟨by simp only [WF], fun x h => by simp only [Touches] at h; exact h ▸ hr⟩

theorem Within.push {r : ℕ} {b : Bool} (hr : P r) : Within P (.push r b) :=
  ⟨by simp only [WF], fun x h => by simp only [Touches] at h; exact h ▸ hr⟩

theorem Within.trunc {r s : ℕ} (hr : P r) (hs : P s) (hrs : r ≠ s) : Within P (.trunc r s) :=
  ⟨by simp only [WF]; exact hrs, fun x h => by
    simp only [Touches] at h
    rcases h with rfl | rfl
    · exact hr
    · exact hs⟩

theorem Within.seq {p q : RProg} (hp : Within P p) (hq : Within P q) : Within P (.seq p q) :=
  ⟨by simp only [WF]; exact ⟨hp.1, hq.1⟩, fun x h => by
    simp only [Touches] at h
    exact h.elim (hp.2 x) (hq.2 x)⟩

theorem Within.forBits {r : ℕ} {p₀ p₁ : RProg} (hr : P r) (h₀ : Within (fun x => P x ∧ x ≠ r) p₀)
    (h₁ : Within (fun x => P x ∧ x ≠ r) p₁) : Within P (.forBits r p₀ p₁) :=
  ⟨by simp only [WF]; exact ⟨fun h => (h₀.2 r h).2 rfl, fun h => (h₁.2 r h).2 rfl, h₀.1, h₁.1⟩,
    fun x h => by
      simp only [Touches] at h
      rcases h with rfl | h | h
      · exact hr
      · exact (h₀.2 x h).1
      · exact (h₁.2 x h).1⟩

theorem Within.forBitsRev {r : ℕ} {p₀ p₁ : RProg} (hr : P r)
    (h₀ : Within (fun x => P x ∧ x ≠ r) p₀) (h₁ : Within (fun x => P x ∧ x ≠ r) p₁) :
    Within P (.forBitsRev r p₀ p₁) :=
  ⟨by simp only [WF]; exact ⟨fun h => (h₀.2 r h).2 rfl, fun h => (h₁.2 r h).2 rfl, h₀.1, h₁.1⟩,
    fun x h => by
      simp only [Touches] at h
      rcases h with rfl | h | h
      · exact hr
      · exact (h₀.2 x h).1
      · exact (h₁.2 x h).1⟩

theorem Within.seqs {ps : List RProg} (h : ∀ p ∈ ps, Within P p) : Within P (RProg.seqs ps) := by
  induction ps with
  | nil => exact Within.skip
  | cons p ps ih =>
      exact Within.seq (h p (by simp)) (ih fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem Within.append {a d : ℕ} (ha : P a) (hd : P d) (had : a ≠ d) :
    Within P (RProg.append a d) :=
  Within.forBits ha (Within.push ⟨hd, had.symm⟩) (Within.push ⟨hd, had.symm⟩)

theorem Within.copy {a d : ℕ} (ha : P a) (hd : P d) (had : a ≠ d) : Within P (RProg.copy a d) :=
  Within.seq (Within.clear hd) (Within.append ha hd had)

theorem Within.clearRange {fr : ℕ} :
    ∀ {n : ℕ}, (∀ i < n, P (fr + i)) → Within P (RProg.clearRange fr n)
  | 0, _ => Within.skip
  | n + 1, h => Within.seq (Within.clearRange fun i hi => h i (by omega)) (Within.clear (h n (by omega)))

end Within

/-- Compiled programs are well formed and use only their arguments, their output and the registers
from `fr` on. -/
def Good (v : Cob) : Prop :=
  ∀ (args : List ℕ) (out fr : ℕ), args.Nodup → (∀ a ∈ args, a < fr) → out < fr → out ∉ args →
    Within (fun x => x ∈ args ∨ x = out ∨ fr ≤ x) (compile v args out fr)

theorem good_proj (i : ℕ) : Good (.proj i) := by
  intro args out fr _ _ _ hna
  rw [compile]
  cases hi : args[i]? with
  | none => exact Within.clear (Or.inr (Or.inl rfl))
  | some a =>
      have ha : a ∈ args := List.mem_of_getElem? hi
      exact Within.copy (Or.inl ha) (Or.inr (Or.inl rfl)) (fun h => hna (h ▸ ha))

theorem good_empty : Good .empty := by
  intro args out fr _ _ _ _
  rw [compile]
  exact Within.clear (Or.inr (Or.inl rfl))

theorem good_app (b : Bool) : Good (.app b) := by
  intro args out fr _ _ _ hna
  rw [compile]
  refine Within.seq (Within.clear (Or.inr (Or.inl rfl)))
    (Within.seq (Within.push (Or.inr (Or.inl rfl))) ?_)
  cases h0 : args[0]? with
  | none => exact Within.skip
  | some a =>
      have ha : a ∈ args := List.mem_of_getElem? h0
      exact Within.append (Or.inl ha) (Or.inr (Or.inl rfl)) (fun h => hna (h ▸ ha))

theorem good_smash : Good .smash := by
  intro args out fr hnd _ _ hna
  rcases args with _ | ⟨a₀, _ | ⟨a₁, rest⟩⟩
  · rw [compile]
    exact Within.seq (Within.clear (Or.inr (Or.inl rfl))) Within.skip
  · rw [compile]
    exact Within.seq (Within.clear (Or.inr (Or.inl rfl))) Within.skip
  · rw [compile]
    have h01 : a₀ ≠ a₁ := by intro h; subst h; simp at hnd
    have h0 : a₀ ≠ out := by intro h; subst h; simp at hna
    have h1 : a₁ ≠ out := by intro h; subst h; simp at hna
    have hin : Within (fun x => (x ∈ a₀ :: a₁ :: rest ∨ x = out ∨ fr ≤ x) ∧ x ≠ a₀)
        (.forBits a₁ (.push out true) (.push out true)) :=
      Within.forBits ⟨Or.inl (by simp), h01.symm⟩
        (Within.push ⟨⟨Or.inr (Or.inl rfl), h0.symm⟩, h1.symm⟩)
        (Within.push ⟨⟨Or.inr (Or.inl rfl), h0.symm⟩, h1.symm⟩)
    exact Within.seq (Within.clear (Or.inr (Or.inl rfl))) (Within.forBits (Or.inl (by simp)) hin hin)

theorem good_list (gs : List Cob) (hgs : ∀ g ∈ gs, Good g) :
    ∀ (args : List ℕ) (j sc : ℕ), args.Nodup → (∀ a ∈ args, a < j) → j + gs.length ≤ sc →
      Within (fun x => x ∈ args ∨ j ≤ x) (compileList gs args j sc) := by
  induction gs with
  | nil => intro args j sc _ _ _; rw [compileList]; exact Within.skip
  | cons g gs ih =>
      intro args j sc hnd hargs hlen
      simp only [List.length_cons] at hlen
      rw [compileList]
      refine Within.seq ((hgs g (by simp) args j sc hnd (fun a ha => by have := hargs a ha; omega)
        (by omega) (fun h => by have := hargs j h; omega)).mono fun x hx => ?_)
        ((ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg)) args (j + 1) sc hnd
          (fun a ha => by have := hargs a ha; omega) (by omega)).mono fun x hx => ?_)
      · rcases hx with hx | hx | hx
        · exact Or.inl hx
        · exact Or.inr (by omega)
        · exact Or.inr (by omega)
      · rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (by omega)

theorem good_comp (f : Cob) (gs : List Cob) (hf : Good f) (hgs : ∀ g ∈ gs, Good g) :
    Good (.comp f gs) := by
  intro args out fr hnd hargs hout hna
  rw [compile]
  refine Within.seq ((good_list gs hgs args fr (fr + gs.length) hnd hargs le_rfl).mono
    fun x hx => ?_) (Within.seq ((hf (List.range' fr gs.length) out (fr + gs.length)
      List.nodup_range' (fun a ha => ?_) (by omega) (fun h => ?_)).mono fun x hx => ?_)
      (Within.clearRange fun i _ => Or.inr (Or.inr (by omega))))
  · rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  · rw [List.mem_range'_1] at ha; omega
  · rw [List.mem_range'_1] at h; omega
  · rcases hx with hx | hx | hx
    · rw [List.mem_range'_1] at hx; exact Or.inr (Or.inr hx.1)
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (by omega))

theorem good_bRec (g h₀ h₁ bd : Cob) (hg : Good g) (hh₀ : Good h₀) (hh₁ : Good h₁)
    (hbd : Good bd) : Good (.bRec g h₀ h₁ bd) := by
  intro args out fr hnd hargs hout hna
  rw [compile]
  have htail : args.tail.Nodup := hnd.sublist (List.tail_sublist args)
  have htl : ∀ a ∈ args.tail, a < fr := fun a ha => hargs a (List.mem_of_mem_tail ha)
  have hstep : ∀ c : Cob, Good c → Within (fun x => x ∈ args.tail ∨ fr ≤ x)
      (compile c (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5)) := by
    intro c hc
    refine (hc _ _ _ ?_ ?_ (by omega) ?_).mono fun x hx => ?_
    · refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, htail⟩⟩
      · intro h
        simp only [List.mem_cons] at h
        rcases h with h | h
        · omega
        · have := htl _ h; omega
      · intro h; have := htl _ h; omega
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | rfl | ha
      · omega
      · omega
      · have := htl a ha; omega
    · intro h
      simp only [List.mem_cons] at h
      rcases h with h | h | h
      · omega
      · omega
      · have := htl _ h; omega
    · simp only [List.mem_cons] at hx
      rcases hx with (hx | hx | hx) | hx | hx
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)
      · exact Or.inl hx
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  have hbound : Within (fun x => x ∈ args.tail ∨ fr ≤ x)
      (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) := by
    refine (hbd _ _ _ ?_ ?_ (by omega) ?_).mono fun x hx => ?_
    · exact List.nodup_cons.2 ⟨fun h => by have := htl _ h; omega, htail⟩
    · intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · omega
      · have := htl a ha; omega
    · intro h
      simp only [List.mem_cons] at h
      rcases h with h | h
      · omega
      · have := htl _ h; omega
    · simp only [List.mem_cons] at hx
      rcases hx with (hx | hx) | hx | hx
      · exact Or.inr (by omega)
      · exact Or.inl hx
      · exact Or.inr (by omega)
      · exact Or.inr (by omega)
  have hbody : ∀ (c : Cob) (b : Bool), Good c → Within (fun x => x ∈ args.tail ∨ fr ≤ x)
      (bRecBody (compile c (fr :: (fr + 1) :: args.tail) (fr + 2) (fr + 5))
        (compile bd ((fr + 3) :: args.tail) (fr + 4) (fr + 5)) b fr) := by
    intro c b hc
    have hr : ∀ x, fr ≤ x → x ∈ args.tail ∨ fr ≤ x := fun x hx => Or.inr hx
    rw [bRecBody]
    refine Within.seqs fun p hp => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hstep c hc
    · exact Within.clear (hr _ (by omega))
    · exact Within.push (hr _ (by omega))
    · exact Within.append (hr _ (by omega)) (hr _ (by omega)) (by omega)
    · exact hbound
    · exact Within.copy (hr _ (by omega)) (hr _ (by omega)) (by omega)
    · exact Within.trunc (hr _ (by omega)) (hr _ (by omega)) (by omega)
    · exact Within.copy (hr _ (by omega)) (hr _ (by omega)) (by omega)
    · exact Within.clear (hr _ (by omega))
    · exact Within.clear (hr _ (by omega))
    · exact Within.clear (hr _ (by omega))
  refine Within.seqs fun p hp => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine (hg args.tail (fr + 1) (fr + 5) htail (fun a ha => by have := htl a ha; omega)
      (by omega) (fun h => by have := htl _ h; omega)).mono fun x hx => ?_
    rcases hx with hx | hx | hx
    · exact Or.inl (List.mem_of_mem_tail hx)
    · exact Or.inr (Or.inr (by omega))
    · exact Or.inr (Or.inr (by omega))
  · cases args with
    | nil => exact Within.skip
    | cons x₀ rest =>
        have hx₀ : x₀ ∉ rest := (List.nodup_cons.1 hnd).1
        have hx₀fr : x₀ < fr := hargs x₀ (by simp)
        have hmono : ∀ x, (x ∈ rest ∨ fr ≤ x) →
            (x ∈ x₀ :: rest ∨ x = out ∨ fr ≤ x) ∧ x ≠ x₀ := by
          intro x hx
          rcases hx with hx | hx
          · exact ⟨Or.inl (List.mem_cons_of_mem _ hx), fun h => hx₀ (h ▸ hx)⟩
          · exact ⟨Or.inr (Or.inr hx), by omega⟩
        exact Within.forBitsRev (Or.inl (by simp)) ((hbody h₀ false hh₀).mono hmono)
          ((hbody h₁ true hh₁).mono hmono)
  · exact Within.copy (Or.inr (Or.inr (by omega))) (Or.inr (Or.inl rfl)) (by omega)
  · exact Within.clearRange fun i _ => Or.inr (Or.inr (by omega))

theorem good_aux : ∀ (n : ℕ) (v : Cob), sizeOf v ≤ n → Good v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    cases v with
    | proj i => exact good_proj i
    | empty => exact good_empty
    | app b => exact good_app b
    | smash => exact good_smash
    | comp f gs =>
        simp only [Cob.comp.sizeOf_spec] at hv
        exact good_comp f gs (ih (sizeOf f) (by omega) f le_rfl)
          (fun g hg => ih (sizeOf g) (by have := List.sizeOf_lt_of_mem hg; omega) g le_rfl)
    | bRec g h₀ h₁ bd =>
        simp only [Cob.bRec.sizeOf_spec] at hv
        exact good_bRec g h₀ h₁ bd (ih _ (by omega) g le_rfl) (ih _ (by omega) h₀ le_rfl)
          (ih _ (by omega) h₁ le_rfl) (ih _ (by omega) bd le_rfl)

/-- **Compiled programs are well formed**, for distinct arguments below the scratch registers. -/
theorem compile_good (v : Cob) : Good v := good_aux (sizeOf v) v le_rfl

/-! ### The machine of a Cobham term -/

/-- The register program of a Cobham term: the input in register `0`, the result in register `1`,
scratch registers from `2` on. -/
def mainProg (v : Cob) : RProg := compile v [0] 1 2

/-- The low-level program: initialise, run the register program, test the result. -/
def lowProg (v : Cob) : List LInstr := .init :: (flat (mainProg v) 1 ++ [.test 1])

/-- The number of register tapes. -/
def regCount (v : Cob) : ℕ := bound (mainProg v) + 2

/-- **The multi-tape machine of a Cobham term.** -/
abbrev cobMachine (v : Cob) : FiniteMultiTapeMachine := machine (lowProg v) (regCount v)

/-- The registers at the start: the input in register `0`, the others empty. -/
def inputRegs (x : Word) : Regs := Function.update (fun _ => []) 0 x

theorem inputRegs_zero (x : Word) : inputRegs x 0 = x := Function.update_self ..

theorem inputRegs_ne (x : Word) {r : ℕ} (h : r ≠ 0) : inputRegs x r = [] := by
  rw [inputRegs, Function.update_of_ne h]

theorem regCount_pos (v : Cob) : 0 < regCount v := by unfold regCount; omega

theorem regCount_one (v : Cob) : 1 < regCount v := by unfold regCount; omega

theorem touches_lt (v : Cob) {y : ℕ} (hy : Touches (mainProg v) y) : y < regCount v := by
  have := lt_bound _ hy
  unfold regCount
  omega

theorem lowProg_init (v : Cob) : (lowProg v)[0]? = some .init := rfl

theorem lowProg_contains (v : Cob) : Contains (lowProg v) (flat (mainProg v) 1) 1 := by
  intro k hk
  rw [lowProg, Nat.add_comm, List.getElem?_cons_succ, List.getElem?_append_left hk,
    List.getElem?_eq_getElem hk]

theorem lowProg_test (v : Cob) : (lowProg v)[1 + flen (mainProg v)]? = some (.test 1) := by
  rw [lowProg, Nat.add_comm, List.getElem?_cons_succ,
    List.getElem?_append_right (le_of_eq (flat_length _ _)), flat_length, Nat.sub_self]
  rfl

/-- **The machine of a Cobham term runs in polynomial time**: on input `x` it halts within
`2 |x| + 6 + f |x|` steps, for a monotone polynomial `f`, accepting iff `v.eval [x]` is not
empty. -/
theorem cobMachine_haltsIn (v : Cob) : ∃ f : ℕ → ℕ, PolyM f ∧ ∀ x : Word,
    MultiTapeHaltsIn (cobMachine v) x (decide (v.eval [x] ≠ [])) (2 * x.length + 6 + f x.length) := by
  obtain ⟨f, hf, hcost⟩ := compile_cost v
  refine ⟨f, hf, fun x => ?_⟩
  -- initialisation
  obtain ⟨T1, hT1₀, hT1r, hrun1⟩ := run_initI (prog := lowProg v) (N := regCount v)
    (lowProg_init v) (regCount_pos v) x
  -- the register program
  have hpre : SimPre (lowProg v) (regCount v) (mainProg v) 1 (inputRegs x) T1 := by
    refine ⟨(compile_good v [0] 1 2 (by simp) (by simp) (by omega) (by simp)).1,
      fun y hy => touches_lt v hy, lowProg_contains v, fun y hy => ?_⟩
    by_cases hy0 : y = 0
    · subst hy0
      rw [inputRegs_zero]
      exact hT1₀
    · rw [inputRegs_ne x hy0]
      exact hT1r y (touches_lt v hy) hy0
  obtain ⟨T2, hT2, hframe, hrun2⟩ := sim (mainProg v) 1 (inputRegs x) T1 hpre
  have hspec := compile_spec v [0] 1 2 (inputRegs x) (by simp) (by omega) (by simp)
    (fun r hr => inputRegs_ne x (by omega))
  have hout : run (mainProg v) (inputRegs x) 1 = v.eval [x] := by
    rw [mainProg, hspec.1]
    simp [inputRegs_zero]
  have hrep : RepT (T2 (reg (regCount v) 1)) (enc (v.eval [x])) 0 := by
    rw [← hout]
    by_cases h1 : Touches (mainProg v) 1
    · exact hT2 1 h1
    · rw [hframe _ fun y hy => reg_ne_of (regCount_one v) (touches_lt v hy)
        (by rintro rfl; exact h1 hy), run_untouched _ h1, inputRegs_ne x one_ne_zero]
      exact hT1r 1 (regCount_one v) one_ne_zero
  -- the test
  obtain ⟨T3, hrun3⟩ := run_testI (lowProg_test v) T2 (v.eval [x]) hrep
  -- the time
  have hc : cost (mainProg v) (inputRegs x) ≤ f x.length := by
    have h := hcost [0] 1 2 (inputRegs x) (by simp) (by omega) (by simp)
      (fun r hr => inputRegs_ne x (by omega)) (inputRegs_ne x one_ne_zero)
    have hmax : maxLen ([0].map (inputRegs x)) = x.length := by
      simp [maxLen, inputRegs_zero]
    rw [hmax] at h
    exact h
  obtain ⟨n, hn, hrun⟩ := hrun1.trans (hrun2.trans hrun3)
  exact ⟨n, by omega, ⟨.inr (decide (v.eval [x] ≠ [])), T3⟩, hrun, rfl, rfl⟩

theorem multiTapeHaltsIn_mono {M : FiniteMultiTapeMachine} {x : List Bool} {b : Bool} {s t : ℕ}
    (h : MultiTapeHaltsIn M x b s) (hst : s ≤ t) : MultiTapeHaltsIn M x b t := by
  obtain ⟨k, hk, c, h1, h2, h3⟩ := h
  exact ⟨k, hk.trans hst, c, h1, h2, h3⟩

/-- **Every language in `P` is decided by a multi-tape machine in polynomial time.** -/
theorem multiTape_of_inP {L : Language} (hL : InP L) :
    ∃ (M : FiniteMultiTapeMachine) (C a : ℕ), 0 < C ∧ 0 < a ∧ ∀ x,
      ∃ b, MultiTapeHaltsIn M x b (C * (x.length + 1) ^ a) ∧ (L x ↔ b = true) := by
  obtain ⟨v, hv⟩ := hL
  obtain ⟨f, ⟨-, C, a, hfC⟩, hhalt⟩ := cobMachine_haltsIn v
  refine ⟨cobMachine v, C + 8, a + 1, by omega, by omega, fun x =>
    ⟨_, multiTapeHaltsIn_mono (hhalt x) ?_, by rw [hv x]; simp⟩⟩
  have h1 : 1 ≤ (x.length + 1) ^ a := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have h2 : (x.length + 1) ^ (a + 1) = (x.length + 1) ^ a * (x.length + 1) := pow_succ _ _
  have h3 : (x.length + 1) ^ a ≤ (x.length + 1) ^ (a + 1) := by
    rw [h2]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h4 : x.length + 1 ≤ (x.length + 1) ^ (a + 1) := by
    rw [h2]; exact Nat.le_mul_of_pos_left _ h1
  have h5 := Nat.mul_le_mul_left C h3
  have h6 := hfC x.length
  rw [Nat.add_mul]
  omega

/-- The same, with the answer `decide (L w)`. -/
theorem multiTape_decide_of_inP {L : Language} [DecidablePred L] (hL : InP L) :
    ∃ (M : FiniteMultiTapeMachine) (C a : ℕ), 0 < C ∧ 0 < a ∧ ∀ w,
      MultiTapeHaltsIn M w (decide (L w)) (C * (w.length + 1) ^ a) := by
  obtain ⟨M, C, a, hC, ha, h⟩ := multiTape_of_inP hL
  refine ⟨M, C, a, hC, ha, fun w => ?_⟩
  obtain ⟨b, hb, hLb⟩ := h w
  have : decide (L w) = b := by cases b <;> simp [hLb]
  rw [this]
  exact hb

/-- **Cobham's `P` is polynomial time on multi-tape machines**: a language is in `InP` iff a
`FiniteMultiTapeMachine` decides it within a polynomial number of steps. -/
theorem inP_iff_multiTape (L : Language) :
    InP L ↔ ∃ (M : FiniteMultiTapeMachine) (p : ℕ → ℕ), PolyBound p ∧
      ∀ x, ∃ b, MultiTapeHaltsIn M x b (p x.length) ∧ (L x ↔ b = true) := by
  constructor
  · intro hL
    obtain ⟨M, C, a, -, -, h⟩ := multiTape_of_inP hL
    exact ⟨M, fun n => C * (n + 1) ^ a, ⟨C, a, fun _ => le_rfl⟩, h⟩
  · rintro ⟨M, p, hp, h⟩
    exact MultiTapeCobham.inP_of_multiTapeHaltsIn M L p hp h

end CobMT

end Complexity
