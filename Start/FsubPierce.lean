/-
**The simulation of two-counter machines in F<:^D** — task `M25-FSUB-UNDECIDABLE` (round 7,
steps D1/D3).

The rules of the deterministic fragment F<:^D (`FsubRowing.DStep`) are read as a small
continuation-passing machine:

* a goal `Γ ⊢ P <: ∀X₁<:V₁ … ∀Xₘ<:Vₘ. ¬K` is the *call* of the process `P` with the arguments
  `V₁ … Vₘ` and the continuation `K` (`FsubPierce.frameD`);
* a process `∀X₁<:Top … ∀Xₘ<:Top. ¬F` (`FsubPierce.lamN`) binds its arguments in the context
  (`m` steps of the `Top`-bounded quantifier rule), and the negation rule then swaps the sides:
  the received continuation `K` becomes the next process and the frame `F` built by the process
  its arguments and continuation (`FsubPierce.call_steps`);
* a variable on the left is a reference to a process, followed by promotion
  (`FsubPierce.res_steps`).

Recursion is obtained by passing every code as an argument: all calls have the same arity
`m = n + 6` (for a program of length `n`), with slots for the two counters, two scratch slots,
the codes of the `n` instructions and of halting, and a trampoline `dispT` that re-issues the
call of the code it receives as continuation.  A counter `v` is a chain of numerals
`succT s (succT s (… zeroT))`: the zero numeral calls its first scratch slot, a successor calls
the second one with its predecessor in the counter slot.  A zero test stores the two branch
codes in the scratch slots and calls the counter.  The halting code `∀X̄<:Top. ¬Top` reaches
the axiom `· <: Top`.

* `FsubPierce.enc` — the encoding of a machine and its initial counters as an F<:^D goal;
* `FsubPierce.sim_step` — **the step lemma**: one machine step is a non-empty run of `DStep`
  between encoded configurations (two calls for an increment, four for a zero test);
* `FsubPierce.sim_halt` — a halted configuration runs to an axiom;
* `FsubPierce.halts_iff_drun` — `CM.Halts M a b ↔ DRun (enc M a b)`;
* `FsubPierce.sub_to_subD_of_noStuck` — full F<: is conservative over F<:^D on every goal whose
  deterministic run never gets stuck, and `FsubPierce.enc_noStuck` shows that encoded goals have
  this property;
* `FsubPierce.simulation` — the simulation named as the first missing lemma in round 6;
* `FsubPierce.rowingFirstLemma` — `FsubGhelli.RowingFirstLemma`;
* `FsubPierce.cm_halts_iff_sub` — the many-one reduction of two-counter halting to
  subtyping in full F<: (`CM.Halts M a b ↔ Sub (enc M a b)`).
-/

import Start.FsubRowing

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace FsubPierce

open FsubGhelli FsubRowing

/-! ### de Bruijn lemmas -/

theorem lift_zero (c : ℕ) (T : Ty) : Ty.lift 0 c T = T := by
  induction T generalizing c with
  | top => rfl
  | var i => simp [Ty.lift]
  | all S T ihS ihT => simp [Ty.lift, ihS, ihT]

theorem lift_lift (a b c : ℕ) (T : Ty) : Ty.lift a c (Ty.lift b c T) = Ty.lift (a + b) c T := by
  induction T generalizing c with
  | top => rfl
  | var i =>
      by_cases h : i < c
      · simp [Ty.lift, h]
      · have h' : ¬ i + b < c := by omega
        simp [Ty.lift, h, h']
        omega
  | all S T ihS ihT => simp [Ty.lift, ihS, ihT]

theorem lift_comm (c d e k : ℕ) (V : Ty) :
    Ty.lift c (d + e + k) (Ty.lift e k V) = Ty.lift e k (Ty.lift c (d + k) V) := by
  induction V generalizing k with
  | top => rfl
  | var i =>
      by_cases h1 : i < k
      · have h2 : i < d + e + k := by omega
        have h3 : i < d + k := by omega
        simp [Ty.lift, h1, h2, h3]
      · by_cases h3 : i < d + k
        · have h2 : i + e < d + e + k := by omega
          simp [Ty.lift, h1, h2, h3]
        · have h2 : ¬ i + e < d + e + k := by omega
          have h4 : ¬ i + c < k := by omega
          simp [Ty.lift, h1, h2, h3, h4]
          omega
  | all S T ihS ihT =>
      simp only [Ty.lift]
      have h := ihT (k + 1)
      rw [show d + e + k + 1 = d + e + (k + 1) by omega, show d + k + 1 = d + (k + 1) by omega, h,
        ihS k]

theorem lift_var_ge (c d i : ℕ) (h : d ≤ i) : Ty.lift c d (.var i) = .var (i + c) := by
  simp [Ty.lift]; omega

theorem lift_var_lt (c d i : ℕ) (h : i < d) : Ty.lift c d (.var i) = .var i := by
  simp [Ty.lift, h]

theorem lift_neg (c d : ℕ) (S : Ty) : Ty.lift c d (neg S) = neg (Ty.lift c d S) := by
  simp [neg, Ty.lift]

/-! ### Processes and frames -/

/-- A process with `k` arguments: `∀X₁<:Top … ∀Xₖ<:Top. ¬F`. -/
def lamN : ℕ → Ty → Ty
  | 0, F => neg F
  | k + 1, F => .all .top (lamN k F)

/-- The frame `∀X₁<:V₁ … ∀Xₖ<:Vₖ. ¬K` at depth `d`: the arguments and the continuation are
given relative to the outer context and lifted under the binders already passed. -/
def frameD : ℕ → List Ty → Ty → Ty
  | d, [], K => neg (Ty.lift d 0 K)
  | d, V :: Vs, K => .all (Ty.lift d 0 V) (frameD (d + 1) Vs K)

/-- The context after the arguments of a frame have been bound. -/
def pushD : ℕ → List Ty → List Ty → List Ty
  | _, [], Γ => Γ
  | d, V :: Vs, Γ => pushD (d + 1) Vs (Ty.lift d 0 V :: Γ)

theorem lamN_ne_var (k : ℕ) (F : Ty) (i : ℕ) : lamN k F ≠ .var i := by
  cases k <;> simp [lamN, neg]

theorem frameD_ne_var (d : ℕ) (Vs : List Ty) (K : Ty) (i : ℕ) : frameD d Vs K ≠ .var i := by
  cases Vs <;> simp [frameD, neg]

theorem frameD_ne_top (d : ℕ) (Vs : List Ty) (K : Ty) : frameD d Vs K ≠ .top := by
  cases Vs <;> simp [frameD, neg]

theorem lift_lamN (c d k : ℕ) (F : Ty) :
    Ty.lift c d (lamN k F) = lamN k (Ty.lift c (d + k) F) := by
  induction k generalizing d with
  | zero => simp [lamN, lift_neg]
  | succ k ih =>
      simp only [lamN, Ty.lift]
      rw [ih, show d + 1 + k = d + (k + 1) by omega]

theorem lift_frameD (c d : ℕ) (K : Ty) : ∀ (Vs : List Ty) (e : ℕ),
    Ty.lift c (d + e) (frameD e Vs K) = frameD e (Vs.map (Ty.lift c d)) (Ty.lift c d K)
  | [], e => by
      simp only [frameD, lift_neg, List.map_nil]
      have := lift_comm c d e 0 K
      simp only [Nat.add_zero] at this
      rw [this]
  | V :: Vs, e => by
      simp only [frameD, Ty.lift, List.map_cons]
      have h1 := lift_comm c d e 0 V
      simp only [Nat.add_zero] at h1
      rw [h1]
      have h2 := lift_frameD c d K Vs (e + 1)
      rw [← Nat.add_assoc] at h2
      rw [h2]

/-- **A call**: a process with `|Vs|` arguments against a frame binds the arguments and swaps:
the continuation becomes the next process, the process's frame the next right-hand side. -/
theorem call_steps (F K : Ty) : ∀ (Vs : List Ty) (d : ℕ) (Γ : List Ty),
    Relation.TransGen DStep ⟨Γ, lamN Vs.length F, frameD d Vs K⟩
      ⟨pushD d Vs Γ, Ty.lift (d + Vs.length) 0 K, F⟩
  | [], d, Γ => by
      simp only [List.length_nil, lamN, frameD, pushD, Nat.add_zero]
      exact .single DStep.neg
  | V :: Vs, d, Γ => by
      have h := call_steps F K Vs (d + 1) (Ty.lift d 0 V :: Γ)
      rw [show d + 1 + Vs.length = d + (V :: Vs).length by simp; omega] at h
      exact .head (DStep.allTop (Or.inr (lamN_ne_var _ _ _))) h

/-! ### Lookup in contexts -/

/-- The bound of the variable `i` in `Γ`, as a type valid in `Γ`. -/
def get (Γ : List Ty) (i : ℕ) : Option Ty := (Γ[i]?).map (Ty.lift (i + 1) 0)

theorem get_append (Δ Γ : List Ty) (i : ℕ) :
    get (Δ ++ Γ) (i + Δ.length) = (get Γ i).map (Ty.lift Δ.length 0) := by
  simp only [get, List.getElem?_append_right (by omega : Δ.length ≤ i + Δ.length),
    Nat.add_sub_cancel, Option.map_map]
  congr 1
  funext B
  simp only [Function.comp_apply, lift_lift]
  congr 1
  omega

theorem pushD_eq : ∀ (Vs : List Ty) (d : ℕ) (Γ : List Ty),
    ∃ Δ, pushD d Vs Γ = Δ ++ Γ ∧ Δ.length = Vs.length
  | [], _, Γ => ⟨[], rfl, rfl⟩
  | V :: Vs, d, Γ => by
      obtain ⟨Δ, h1, h2⟩ := pushD_eq Vs (d + 1) (Ty.lift d 0 V :: Γ)
      exact ⟨Δ ++ [Ty.lift d 0 V], by simp [pushD, h1], by simp [h2]⟩

theorem get_pushD_outer (Vs : List Ty) (d : ℕ) (Γ : List Ty) (i : ℕ) :
    get (pushD d Vs Γ) (i + Vs.length) = (get Γ i).map (Ty.lift Vs.length 0) := by
  obtain ⟨Δ, h1, h2⟩ := pushD_eq Vs d Γ
  rw [h1, ← h2, get_append]

theorem get_pushD_param : ∀ (Vs : List Ty) (d : ℕ) (Γ : List Ty) (k : ℕ) (hk : k < Vs.length),
    get (pushD d Vs Γ) (Vs.length - 1 - k) = some (Ty.lift (d + Vs.length) 0 Vs[k])
  | [], _, _, k, hk => by simp at hk
  | V :: Vs, d, Γ, 0, _ => by
      obtain ⟨Δ, h1, h2⟩ := pushD_eq Vs (d + 1) (Ty.lift d 0 V :: Γ)
      simp only [pushD, h1, List.length_cons, List.getElem_cons_zero]
      have := get_append Δ (Ty.lift d 0 V :: Γ) 0
      rw [Nat.zero_add] at this
      rw [show Vs.length + 1 - 1 - 0 = Δ.length by omega, this]
      simp only [get, List.getElem?_cons_zero, Option.map_some, lift_lift]
      congr 2
      omega
  | V :: Vs, d, Γ, k + 1, hk => by
      have h := get_pushD_param Vs (d + 1) (Ty.lift d 0 V :: Γ) k (by simp at hk; omega)
      simp only [pushD, List.length_cons, List.getElem_cons_succ]
      rw [show Vs.length + 1 - 1 - (k + 1) = Vs.length - 1 - k by omega, h,
        show d + 1 + Vs.length = d + (Vs.length + 1) by omega]

/-- **Resolution**: following promotions from the variable `i` reaches the type `T`. -/
inductive Res (Γ : List Ty) : ℕ → Ty → Prop
  | here {i : ℕ} {T : Ty} : get Γ i = some T → Res Γ i T
  | ind {i j : ℕ} {T : Ty} : get Γ i = some (.var j) → Res Γ j T → Res Γ i T

/-- Promotion follows a resolution against a right-hand side other than a variable or `Top`. -/
theorem res_steps {Γ : List Ty} {i : ℕ} {T R : Ty} (h : Res Γ i T) (hR1 : ∀ j, R ≠ .var j)
    (hR2 : R ≠ .top) : Relation.TransGen DStep ⟨Γ, .var i, R⟩ ⟨Γ, T, R⟩ := by
  induction h with
  | @here i T hg =>
      obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hg
      exact .single (DStep.promote hB (hR1 i) hR2)
  | @ind i j T hg _ ih =>
      obtain ⟨B, hB, hBe⟩ := Option.map_eq_some_iff.1 hg
      have hs := DStep.promote (T := R) hB (hR1 i) hR2
      rw [hBe] at hs
      exact .head hs ih

theorem Res.append {Γ : List Ty} {i : ℕ} {T : Ty} (Δ : List Ty) (h : Res Γ i T) :
    Res (Δ ++ Γ) (i + Δ.length) (Ty.lift Δ.length 0 T) := by
  induction h with
  | here hg => exact .here (by rw [get_append, hg]; rfl)
  | @ind i j T hg _ ih =>
      refine .ind (j := j + Δ.length) ?_ ih
      rw [get_append, hg]
      simp [Ty.lift]

theorem Res.push {Γ : List Ty} {i : ℕ} {T : Ty} (Vs : List Ty) (d : ℕ) (h : Res Γ i T) :
    Res (pushD d Vs Γ) (i + Vs.length) (Ty.lift Vs.length 0 T) := by
  obtain ⟨Δ, h1, h2⟩ := pushD_eq Vs d Γ
  rw [h1, ← h2]
  exact h.append Δ


/-! ### The machine: codes, numerals and the trampoline -/

/-- The counter slot of a register (`true` is the first counter). -/
def sl : Bool → ℕ
  | true => 0
  | false => 1

theorem sl_lt (r : Bool) : sl r < 2 := by cases r <;> simp [sl]

section Machine

variable (n : ℕ)

/-- The `n + 6` arguments of a call, given slot by slot. -/
def al (f : ℕ → Ty) : List Ty := (List.range (n + 6)).map f

theorem al_length (f : ℕ → Ty) : (al n f).length = n + 6 := by simp [al]

/-- The parameter `k` inside a process of arity `n + 6`. -/
def pv (k : ℕ) : Ty := .var (n + 5 - k)

/-- A process of arity `n + 6` whose frame passes the arguments `f` and the continuation `K`. -/
def proc (f : ℕ → Ty) (K : Ty) : Ty := lamN (n + 6) (frameD 0 (al n f) K)

/-- The trampoline: re-issue the call of the received continuation, passing the arguments
unchanged and itself as the next continuation. -/
def dispT : Ty := proc n (pv n) (pv n (n + 5))

/-- The halting code: its frame is `Top`, so the next goal is an axiom. -/
def haltT : Ty := lamN (n + 6) .top

/-- The numeral zero: call the first scratch slot. -/
def zeroT : Ty := proc n (pv n) (pv n 2)

/-- The successor numeral of the counter in slot `s`, with predecessor `T`: put the predecessor
in the slot and call the second scratch slot. -/
def succT (s : ℕ) (T : Ty) : Ty :=
  proc n (fun k => if k = s then Ty.lift (n + 6) 0 T else pv n k) (pv n 3)

/-- The slot of the code of label `l` (labels from `n` on all halt). -/
def lab (l : ℕ) : ℕ := 4 + min l n

/-- The argument function of the code of an increment of slot `s`. -/
def incArgs (s : ℕ) : ℕ → Ty := fun k => if k = s then succT n s (pv n s) else pv n k

/-- The argument function of the code of a zero test: the branches go to the scratch slots. -/
def testArgs (l₁ l₂ : ℕ) : ℕ → Ty :=
  fun k => if k = 2 then pv n (lab n l₁) else if k = 3 then pv n (lab n l₂) else pv n k

/-- **The code of an instruction** (a context entry, closed). -/
def codeT : CMInstr → Ty
  | .inc r l => proc n (incArgs n (sl r)) (pv n (lab n l))
  | .test r l₁ l₂ => proc n (testArgs n l₁ l₂) (pv n (sl r))

end Machine

/-- The code at label `l` of a machine. -/
def codeAt (M : CM) (l : ℕ) : Ty :=
  match M[l]? with
  | some i => codeT M.length i
  | none => haltT M.length

theorem codeAt_min (M : CM) (l : ℕ) : codeAt M (min l M.length) = codeAt M l := by
  rcases Nat.lt_or_ge l M.length with h | h
  · rw [min_eq_left h.le]
  · rw [min_eq_right h]
    simp [codeAt, List.getElem?_eq_none h]

/-! ### Closedness of the codes -/

section Lift

variable (n : ℕ)

theorem lift_pv (c d k : ℕ) : Ty.lift c (d + (n + 6)) (pv n k) = pv n k :=
  lift_var_lt _ _ _ (by omega)

theorem al_map (f : ℕ → Ty) (g : Ty → Ty) : (al n f).map g = al n (fun k => g (f k)) := by
  simp [al, List.map_map, Function.comp_def]

theorem lift_proc (c d : ℕ) (f : ℕ → Ty) (K : Ty) :
    Ty.lift c d (proc n f K) =
      proc n (fun k => Ty.lift c (d + (n + 6)) (f k)) (Ty.lift c (d + (n + 6)) K) := by
  unfold proc
  rw [lift_lamN]
  have := lift_frameD c (d + (n + 6)) K (al n f) 0
  rw [Nat.add_zero] at this
  rw [this, al_map]

theorem lift_dispT (c d : ℕ) : Ty.lift c d (dispT n) = dispT n := by
  simp only [dispT, lift_proc, lift_pv]

theorem lift_zeroT (c d : ℕ) : Ty.lift c d (zeroT n) = zeroT n := by
  simp only [zeroT, lift_proc, lift_pv]

theorem lift_haltT (c d : ℕ) : Ty.lift c d (haltT n) = haltT n := by
  simp [haltT, lift_lamN, Ty.lift]

theorem lift_succT (c d s : ℕ) (T : Ty) :
    Ty.lift c d (succT n s T) = succT n s (Ty.lift c d T) := by
  simp only [succT, lift_proc, lift_pv]
  congr 1
  funext k
  split_ifs
  · have := lift_comm c d (n + 6) 0 T
    simpa using this
  · exact lift_pv n c d k

theorem lift_codeT (c d : ℕ) (i : CMInstr) : Ty.lift c d (codeT n i) = codeT n i := by
  cases i with
  | inc r l =>
      simp only [codeT, lift_proc, lift_pv]
      congr 1
      funext k
      simp only [incArgs]
      split_ifs
      · rw [lift_succT, lift_pv]
      · exact lift_pv n c d k
  | test r l₁ l₂ =>
      simp only [codeT, lift_proc, lift_pv]
      congr 1
      funext k
      simp only [testArgs]
      split_ifs <;> exact lift_pv n _ _ _

theorem lift_codeAt (M : CM) (c d l : ℕ) : Ty.lift c d (codeAt M l) = codeAt M l := by
  unfold codeAt
  split
  · exact lift_codeT _ _ _ _
  · exact lift_haltT _ _ _

end Lift

/-! ### Counters -/

/-- **Representation of a counter**: the variable `i` resolves to a chain of `v` successor
numerals of slot `s` ending in zero. -/
def Rep (n s : ℕ) (Γ : List Ty) : ℕ → ℕ → Prop
  | i, 0 => Res Γ i (zeroT n)
  | i, v + 1 => ∃ j, Res Γ i (succT n s (.var j)) ∧ Rep n s Γ j v

theorem Rep.append {n s : ℕ} {Γ : List Ty} (Δ : List Ty) :
    ∀ {i v : ℕ}, Rep n s Γ i v → Rep n s (Δ ++ Γ) (i + Δ.length) v
  | i, 0, h => by
      have := Res.append Δ (show Res Γ i (zeroT n) from h)
      rwa [lift_zeroT] at this
  | i, v + 1, h => by
      obtain ⟨j, hj, hr⟩ := h
      refine ⟨j + Δ.length, ?_, Rep.append Δ hr⟩
      have := Res.append Δ hj
      rwa [lift_succT, lift_var_ge _ _ _ (Nat.zero_le _)] at this

theorem Rep.ind {n s : ℕ} {Γ : List Ty} {i j : ℕ} (hg : get Γ i = some (.var j)) :
    ∀ {v : ℕ}, Rep n s Γ j v → Rep n s Γ i v
  | 0, h => Res.ind hg h
  | _ + 1, h => by
      obtain ⟨k, hk, hr⟩ := h
      exact ⟨k, Res.ind hg hk, hr⟩

/-! ### Calls between processes of arity `n + 6` -/

section Calls

variable {n : ℕ}

theorem get_push_al (Γ : List Ty) (g : ℕ → Ty) {k : ℕ} (hk : k < n + 6) :
    get (pushD 0 (al n g) Γ) (n + 5 - k) = some (Ty.lift (n + 6) 0 (g k)) := by
  have := get_pushD_param (al n g) 0 Γ k (by rw [al_length]; exact hk)
  simp only [al_length, Nat.zero_add] at this
  rw [show n + 5 - k = n + 6 - 1 - k by omega, this]
  simp [al]

theorem Res.pushAl {Γ : List Ty} {i : ℕ} {T : Ty} (g : ℕ → Ty) (h : Res Γ i T) :
    Res (pushD 0 (al n g) Γ) (i + (n + 6)) (Ty.lift (n + 6) 0 T) := by
  have := h.push (al n g) 0
  rwa [al_length] at this

theorem Rep.pushAl {s : ℕ} {Γ : List Ty} {i v : ℕ} (g : ℕ → Ty) (h : Rep n s Γ i v) :
    Rep n s (pushD 0 (al n g) Γ) (i + (n + 6)) v := by
  obtain ⟨Δ, h1, h2⟩ := pushD_eq (al n g) 0 Γ
  rw [h1, ← al_length n g, ← h2]
  exact h.append Δ

/-- The goal of a call of the variable `p` with the arguments `is` and the continuation `q`. -/
def dispGoal (n : ℕ) (Γ : List Ty) (p : ℕ) (is : ℕ → ℕ) (q : ℕ) : Goal :=
  ⟨Γ, .var p, frameD 0 (al n (fun k => .var (is k))) (.var q)⟩

theorem call_proc {Γ : List Ty} {p q : ℕ} {f g : ℕ → Ty} {K : Ty}
    (hp : Res Γ p (proc n f K)) :
    Relation.TransGen DStep ⟨Γ, .var p, frameD 0 (al n g) (.var q)⟩
      ⟨pushD 0 (al n g) Γ, .var (q + (n + 6)), frameD 0 (al n f) K⟩ := by
  refine (res_steps hp (frameD_ne_var _ _ _) (frameD_ne_top _ _ _)).trans ?_
  have := call_steps (frameD 0 (al n f) K) (.var q) (al n g) 0 Γ
  rw [al_length, Nat.zero_add, lift_var_ge _ _ _ (Nat.zero_le _)] at this
  exact this

/-- The context after a call with the arguments `is` and then a call with the arguments `g`. -/
def ctx2 (n : ℕ) (Γ : List Ty) (is : ℕ → ℕ) (g : ℕ → Ty) : List Ty :=
  pushD 0 (al n g) (pushD 0 (al n (fun k => .var (is k))) Γ)

/-- **Two calls**: a process whose frame calls the trampoline, followed by the trampoline. -/
theorem cycle2 {Γ : List Ty} {p q r : ℕ} {is : ℕ → ℕ} {g : ℕ → Ty}
    (hp : Res Γ p (proc n g (pv n r))) (hq : Res Γ q (dispT n)) :
    Relation.TransGen DStep (dispGoal n Γ p is q)
      (dispGoal n (ctx2 n Γ is g) (n + 5 - r + (n + 6)) (fun k => n + 5 - k) 0) := by
  refine (call_proc hp).trans ?_
  have hq' := hq.pushAl (n := n) (fun k => .var (is k))
  rw [lift_dispT] at hq'
  have := call_proc (g := g) (q := n + 5 - r) hq'
  rw [show pv n (n + 5) = .var 0 by simp [pv]] at this
  exact this

variable {Γ : List Ty} {is : ℕ → ℕ} {g : ℕ → Ty}

theorem res_inner {k : ℕ} {X : Ty} (hk : k < n + 6) (h : Res Γ (is k) X) :
    Res (pushD 0 (al n (fun k => .var (is k))) Γ) (n + 5 - k) (Ty.lift (n + 6) 0 X) := by
  refine Res.ind ?_ (h.pushAl (n := n) (fun k => .var (is k)))
  rw [get_push_al _ _ hk, lift_var_ge _ _ _ (Nat.zero_le _)]

theorem rep_inner {s k v : ℕ} (hk : k < n + 6) (h : Rep n s Γ (is k) v) :
    Rep n s (pushD 0 (al n (fun k => .var (is k))) Γ) (n + 5 - k) v := by
  refine Rep.ind ?_ (h.pushAl (n := n) (fun k => .var (is k)))
  rw [get_push_al _ _ hk, lift_var_ge _ _ _ (Nat.zero_le _)]

/-- Transfer through two calls: a slot copied from the slot `k₀`. -/
theorem res_copy {k k₀ : ℕ} {X : Ty} (hk : k < n + 6) (hk₀ : k₀ < n + 6) (hg : g k = pv n k₀)
    (h : Res Γ (is k₀) X) :
    Res (ctx2 n Γ is g) (n + 5 - k) (Ty.lift (n + 6) 0 (Ty.lift (n + 6) 0 X)) := by
  refine Res.ind ?_ ((res_inner hk₀ h).pushAl g)
  unfold ctx2
  rw [get_push_al _ _ hk, hg, pv, lift_var_ge _ _ _ (Nat.zero_le _)]

theorem rep_copy {s k k₀ v : ℕ} (hk : k < n + 6) (hk₀ : k₀ < n + 6) (hg : g k = pv n k₀)
    (h : Rep n s Γ (is k₀) v) : Rep n s (ctx2 n Γ is g) (n + 5 - k) v := by
  refine Rep.ind ?_ ((rep_inner hk₀ h).pushAl g)
  unfold ctx2
  rw [get_push_al _ _ hk, hg, pv, lift_var_ge _ _ _ (Nat.zero_le _)]

/-- Transfer through two calls: the next process, taken from the slot `r`. -/
theorem res_next {r : ℕ} {X : Ty} (hr : r < n + 6) (h : Res Γ (is r) X) :
    Res (ctx2 n Γ is g) (n + 5 - r + (n + 6)) (Ty.lift (n + 6) 0 (Ty.lift (n + 6) 0 X)) :=
  (res_inner hr h).pushAl g

/-- Transfer through two calls: a slot holding the successor of the slot `k₀`. -/
theorem rep_succ {s k k₀ v : ℕ} (hk : k < n + 6) (hk₀ : k₀ < n + 6)
    (hg : g k = succT n s (pv n k₀)) (h : Rep n s Γ (is k₀) v) :
    Rep n s (ctx2 n Γ is g) (n + 5 - k) (v + 1) := by
  refine ⟨n + 5 - k₀ + (n + 6), .here ?_, (rep_inner hk₀ h).pushAl g⟩
  unfold ctx2
  rw [get_push_al _ _ hk, hg, lift_succT, pv, lift_var_ge _ _ _ (Nat.zero_le _)]

/-- Transfer through two calls: a slot holding a variable of the outer context. -/
theorem rep_free {s k j v : ℕ} (hk : k < n + 6) (hg : g k = Ty.lift (n + 6) 0 (.var j))
    (h : Rep n s Γ j v) : Rep n s (ctx2 n Γ is g) (n + 5 - k) v := by
  refine Rep.ind ?_ ((h.pushAl (n := n) (fun k => .var (is k))).pushAl g)
  unfold ctx2
  rw [get_push_al _ _ hk, hg, lift_var_ge _ _ _ (Nat.zero_le _),
    lift_var_ge _ _ _ (Nat.zero_le _)]

end Calls


/-! ### The configuration invariant and the step lemma -/

/-- The counters of a configuration, by slot. -/
def cnt (c : CMConf) (s : ℕ) : ℕ := if s = 0 then c.a else c.b

/-- **The encoding of a configuration** at a call `dispGoal Γ p is q`: the process `p` is the
code of the current label, the continuation `q` is the trampoline, the code slots hold the codes,
the last slot the trampoline, and the two counter slots represent the counters. -/
structure DInv (M : CM) (Γ : List Ty) (p : ℕ) (is : ℕ → ℕ) (q : ℕ) (c : CMConf) : Prop where
  pc : Res Γ p (codeAt M c.pc)
  disp : Res Γ q (dispT M.length)
  code : ∀ l ≤ M.length, Res Γ (is (4 + l)) (codeAt M l)
  dslot : Res Γ (is (M.length + 5)) (dispT M.length)
  rep : ∀ s < 2, Rep M.length s Γ (is s) (cnt c s)

theorem codeAt_some {M : CM} {l : ℕ} {i : CMInstr} (h : M[l]? = some i) :
    codeAt M l = codeT M.length i := by
  simp [codeAt, h]

theorem codeAt_none {M : CM} {l : ℕ} (h : M.length ≤ l) : codeAt M l = haltT M.length := by
  simp [codeAt, List.getElem?_eq_none h]

section Step

variable {M : CM} {Γ : List Ty} {p q : ℕ} {is : ℕ → ℕ} {c c' : CMConf}

/-- The step lemma for an increment (two calls). -/
theorem step_inc {r : Bool} {l : ℕ} (h : DInv M Γ p is q c) (hi : M[c.pc]? = some (.inc r l))
    (hpc : c'.pc = l) (hc : ∀ s < 2, cnt c' s = if s = sl r then cnt c s + 1 else cnt c s) :
    ∃ Γ' p' is' q', Relation.TransGen DStep (dispGoal M.length Γ p is q)
      (dispGoal M.length Γ' p' is' q') ∧ DInv M Γ' p' is' q' c' := by
  have hp := h.pc
  rw [codeAt_some hi] at hp
  refine ⟨_, _, _, _, cycle2 (is := is) hp h.disp, ?_⟩
  have hsl := sl_lt r
  have hgk : ∀ k, k ≠ sl r → incArgs M.length (sl r) k = pv M.length k := fun k hk => by
    simp only [incArgs]; rw [if_neg hk]
  have hd : Res (ctx2 M.length Γ is (incArgs M.length (sl r))) (M.length + 5 - (M.length + 5))
      (dispT M.length) := by
    have := res_copy (n := M.length) (k := M.length + 5) (k₀ := M.length + 5) (by omega) (by omega)
      (hgk _ (by omega)) h.dslot
    rwa [lift_dispT, lift_dispT] at this
  constructor
  · rw [hpc]
    have := res_next (n := M.length) (g := incArgs M.length (sl r)) (r := lab M.length l)
      (by simp only [lab]; omega) (h.code _ (min_le_right l M.length))
    rwa [codeAt_min, lift_codeAt, lift_codeAt] at this
  · simpa using hd
  · intro l' hl'
    have := res_copy (n := M.length) (k := 4 + l') (k₀ := 4 + l') (by omega) (by omega) (hgk _ (by omega))
      (h.code l' hl')
    rwa [lift_codeAt, lift_codeAt] at this
  · exact hd
  · intro s hs
    rw [hc s hs]
    split_ifs with hss
    · subst hss
      exact rep_succ (n := M.length) (by omega) (by omega) (by simp [incArgs]) (h.rep _ hs)
    · exact rep_copy (n := M.length) (by omega) (by omega) (hgk _ hss) (h.rep s hs)

theorem testArgs_eq {n l₁ l₂ k : ℕ} (h2 : k ≠ 2) (h3 : k ≠ 3) :
    testArgs n l₁ l₂ k = pv n k := by
  simp only [testArgs]; rw [if_neg h2, if_neg h3]

/-- The step lemma for a zero test of a counter equal to zero (four calls). -/
theorem step_zero {r : Bool} {l₁ l₂ : ℕ} (h : DInv M Γ p is q c)
    (hi : M[c.pc]? = some (.test r l₁ l₂)) (hz : cnt c (sl r) = 0) (hpc : c'.pc = l₁)
    (hc : ∀ s < 2, cnt c' s = cnt c s) :
    ∃ Γ' p' is' q', Relation.TransGen DStep (dispGoal M.length Γ p is q)
      (dispGoal M.length Γ' p' is' q') ∧ DInv M Γ' p' is' q' c' := by
  have hp := h.pc
  rw [codeAt_some hi] at hp
  have hsl := sl_lt r
  have c1 := cycle2 (is := is) hp h.disp
  have hnum : Res (ctx2 M.length Γ is (testArgs M.length l₁ l₂))
      (M.length + 5 - sl r + (M.length + 6)) (zeroT M.length) := by
    have h0 := h.rep (sl r) hsl
    rw [hz] at h0
    have := res_next (n := M.length) (g := testArgs M.length l₁ l₂) (by omega) h0
    rwa [lift_zeroT, lift_zeroT] at this
  have hd : Res (ctx2 M.length Γ is (testArgs M.length l₁ l₂)) (M.length + 5 - (M.length + 5))
      (dispT M.length) := by
    have := res_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := M.length + 5)
      (k₀ := M.length + 5) (by omega) (by omega) (testArgs_eq (by omega) (by omega)) h.dslot
    rwa [lift_dispT, lift_dispT] at this
  have c2 := cycle2 (is := fun k => M.length + 5 - k) (g := pv M.length) (r := 2)
    (hnum : Res _ _ (proc M.length (pv M.length) (pv M.length 2))) (by simpa using hd)
  refine ⟨_, _, _, _, c1.trans c2, ?_⟩
  have hd2 := res_copy (n := M.length) (is := fun k => M.length + 5 - k) (g := pv M.length) (k := M.length + 5)
    (k₀ := M.length + 5) (by omega) (by omega) rfl hd
  rw [lift_dispT, lift_dispT] at hd2
  constructor
  · rw [hpc]
    have h1 := res_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := 2) (k₀ := lab M.length l₁)
      (by omega) (by simp only [lab]; omega) (by simp [testArgs])
      (h.code _ (min_le_right l₁ M.length))
    have := res_next (n := M.length) (is := fun k => M.length + 5 - k) (g := pv M.length) (r := 2) (by omega) h1
    rwa [codeAt_min, lift_codeAt, lift_codeAt, lift_codeAt, lift_codeAt] at this
  · simpa using hd2
  · intro l' hl'
    have h1 := res_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := 4 + l') (k₀ := 4 + l') (by omega)
      (by omega) (testArgs_eq (by omega) (by omega)) (h.code l' hl')
    have := res_copy (n := M.length) (is := fun k => M.length + 5 - k) (g := pv M.length) (k := 4 + l')
      (k₀ := 4 + l') (by omega) (by omega) rfl h1
    rwa [lift_codeAt, lift_codeAt, lift_codeAt, lift_codeAt] at this
  · exact hd2
  · intro s hs
    rw [hc s hs]
    have h1 := rep_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := s) (k₀ := s) (by omega) (by omega)
      (testArgs_eq (by omega) (by omega)) (h.rep s hs)
    exact rep_copy (n := M.length) (is := fun k => M.length + 5 - k) (g := pv M.length) (k := s) (k₀ := s)
      (by omega) (by omega) rfl h1

/-- The step lemma for a zero test of a positive counter, with decrement (four calls). -/
theorem step_dec {r : Bool} {l₁ l₂ v : ℕ} (h : DInv M Γ p is q c)
    (hi : M[c.pc]? = some (.test r l₁ l₂)) (hz : cnt c (sl r) = v + 1) (hpc : c'.pc = l₂)
    (hc : ∀ s < 2, cnt c' s = if s = sl r then v else cnt c s) :
    ∃ Γ' p' is' q', Relation.TransGen DStep (dispGoal M.length Γ p is q)
      (dispGoal M.length Γ' p' is' q') ∧ DInv M Γ' p' is' q' c' := by
  have hp := h.pc
  rw [codeAt_some hi] at hp
  have hsl := sl_lt r
  have c1 := cycle2 (is := is) hp h.disp
  have h0 := h.rep (sl r) hsl
  rw [hz] at h0
  obtain ⟨j, hj, hrj⟩ := h0
  have hnum : Res (ctx2 M.length Γ is (testArgs M.length l₁ l₂))
      (M.length + 5 - sl r + (M.length + 6))
      (succT M.length (sl r) (.var (j + (M.length + 6) + (M.length + 6)))) := by
    have := res_next (n := M.length) (g := testArgs M.length l₁ l₂) (by omega) hj
    rwa [lift_succT, lift_succT, lift_var_ge _ _ _ (Nat.zero_le _),
      lift_var_ge _ _ _ (Nat.zero_le _)] at this
  have hrep2 : Rep M.length (sl r) (ctx2 M.length Γ is (testArgs M.length l₁ l₂))
      (j + (M.length + 6) + (M.length + 6)) v :=
    (hrj.pushAl (n := M.length) (fun k => .var (is k))).pushAl _
  have hd : Res (ctx2 M.length Γ is (testArgs M.length l₁ l₂)) (M.length + 5 - (M.length + 5))
      (dispT M.length) := by
    have := res_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := M.length + 5)
      (k₀ := M.length + 5) (by omega) (by omega) (testArgs_eq (by omega) (by omega)) h.dslot
    rwa [lift_dispT, lift_dispT] at this
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : ℕ → Ty, g₂ = fun k => if k = sl r then
    Ty.lift (M.length + 6) 0 (.var (j + (M.length + 6) + (M.length + 6))) else pv M.length k :=
    ⟨_, rfl⟩
  have hg₂k : ∀ k, k ≠ sl r → g₂ k = pv M.length k := fun k hk => by
    simp only [hg₂]; rw [if_neg hk]
  have c2 := cycle2 (is := fun k => M.length + 5 - k) (g := g₂) (r := 3)
    (by rw [hg₂]; exact hnum) (by simpa using hd)
  refine ⟨_, _, _, _, c1.trans c2, ?_⟩
  have hd2 := res_copy (n := M.length) (is := fun k => M.length + 5 - k) (g := g₂) (k := M.length + 5)
    (k₀ := M.length + 5) (by omega) (by omega) (hg₂k _ (by omega)) hd
  rw [lift_dispT, lift_dispT] at hd2
  constructor
  · rw [hpc]
    have h1 := res_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := 3) (k₀ := lab M.length l₂)
      (by omega) (by simp only [lab]; omega) (by simp [testArgs])
      (h.code _ (min_le_right l₂ M.length))
    have := res_next (n := M.length) (is := fun k => M.length + 5 - k) (g := g₂) (r := 3) (by omega) h1
    rwa [codeAt_min, lift_codeAt, lift_codeAt, lift_codeAt, lift_codeAt] at this
  · simpa using hd2
  · intro l' hl'
    have h1 := res_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := 4 + l') (k₀ := 4 + l') (by omega)
      (by omega) (testArgs_eq (by omega) (by omega)) (h.code l' hl')
    have := res_copy (n := M.length) (is := fun k => M.length + 5 - k) (g := g₂) (k := 4 + l')
      (k₀ := 4 + l') (by omega) (by omega) (hg₂k _ (by omega)) h1
    rwa [lift_codeAt, lift_codeAt, lift_codeAt, lift_codeAt] at this
  · exact hd2
  · intro s hs
    rw [hc s hs]
    split_ifs with hss
    · subst hss
      exact rep_free (n := M.length) (is := fun k => M.length + 5 - k) (g := g₂) (by omega)
        (by simp [hg₂]) hrep2
    · have h1 := rep_copy (n := M.length) (g := testArgs M.length l₁ l₂) (k := s) (k₀ := s) (by omega)
        (by omega) (testArgs_eq (by omega) (by omega)) (h.rep s hs)
      exact rep_copy (n := M.length) (is := fun k => M.length + 5 - k) (g := g₂) (k := s) (k₀ := s)
        (by omega) (by omega) (hg₂k _ hss) h1

/-- **The step lemma**: one machine step is a non-empty run of `DStep` between encoded
configurations. -/
theorem sim_step (h : DInv M Γ p is q c) (hs : CM.Step M c c') :
    ∃ Γ' p' is' q', Relation.TransGen DStep (dispGoal M.length Γ p is q)
      (dispGoal M.length Γ' p' is' q') ∧ DInv M Γ' p' is' q' c' := by
  cases hs with
  | incA hi =>
      exact step_inc h hi rfl (fun s hs => by rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [cnt, sl])
  | incB hi =>
      exact step_inc h hi rfl (fun s hs => by rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [cnt, sl])
  | zeroA hi hz =>
      exact step_zero h hi (by simp [cnt, sl, hz]) rfl (fun s hs => by simp [cnt])
  | @decA _ _ v hi hz =>
      exact step_dec (v := v) h hi (by simp [cnt, sl, hz]) rfl
        (fun s hs => by rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [cnt, sl])
  | zeroB hi hz =>
      exact step_zero h hi (by simp [cnt, sl, hz]) rfl (fun s hs => by simp [cnt])
  | @decB _ _ v hi hz =>
      exact step_dec (v := v) h hi (by simp [cnt, sl, hz]) rfl
        (fun s hs => by rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> simp [cnt, sl])

/-- **A halted configuration runs to an axiom.** -/
theorem sim_halt (h : DInv M Γ p is q c) (hpc : M.length ≤ c.pc) :
    ∃ g, Relation.TransGen DStep (dispGoal M.length Γ p is q) g ∧ IsAxiom g := by
  have hp := h.pc
  rw [codeAt_none hpc] at hp
  have := call_steps .top (.var q) (al M.length (fun k => .var (is k))) 0 Γ
  rw [al_length] at this
  exact ⟨_, (res_steps hp (frameD_ne_var _ _ _) (frameD_ne_top _ _ _)).trans this, Or.inl rfl⟩

end Step

/-- A machine can step from every configuration whose label is inside the program. -/
theorem progress {M : CM} {c : CMConf} (h : c.pc < M.length) : ∃ c', CM.Step M c c' := by
  obtain ⟨i, hi⟩ : ∃ i, M[c.pc]? = some i := ⟨M[c.pc], List.getElem?_eq_getElem h⟩
  cases i with
  | inc r l =>
      cases r
      · exact ⟨_, CM.Step.incB hi⟩
      · exact ⟨_, CM.Step.incA hi⟩
  | test r l₁ l₂ =>
      cases r
      · rcases Nat.eq_zero_or_eq_succ_pred c.b with hb | hb
        · exact ⟨_, CM.Step.zeroB hi hb⟩
        · exact ⟨_, CM.Step.decB hi hb⟩
      · rcases Nat.eq_zero_or_eq_succ_pred c.a with ha | ha
        · exact ⟨_, CM.Step.zeroA hi ha⟩
        · exact ⟨_, CM.Step.decA hi ha⟩


/-! ### Determinism and the run -/

theorem isAxiom_no_step {g g' : Goal} (h : IsAxiom g) : ¬ DStep g g' := by
  intro hs
  rcases h with h | ⟨i, h1, h2⟩ <;> cases hs <;> simp_all [neg]

theorem dispGoal_not_axiom (n : ℕ) (Γ : List Ty) (p : ℕ) (is : ℕ → ℕ) (q : ℕ) :
    ¬ IsAxiom (dispGoal n Γ p is q) := by
  rintro (h | ⟨i, h1, h2⟩)
  · exact frameD_ne_top _ _ _ h
  · exact frameD_ne_var _ _ _ i h2

theorem det_rtg {g g₁ g' : Goal} (hs : DStep g g₁) (h : Relation.ReflTransGen DStep g g') :
    g = g' ∨ Relation.ReflTransGen DStep g₁ g' := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨x, hx, hr⟩
  · exact Or.inl h
  · rw [DStep.deterministic hs hx]; exact Or.inr hr

theorem det_tg {g g₁ g' : Goal} (hs : DStep g g₁) (h : Relation.TransGen DStep g g') :
    Relation.ReflTransGen DStep g₁ g' := by
  obtain ⟨x, hx, hr⟩ := Relation.TransGen.head'_iff.1 h
  rw [DStep.deterministic hs hx]; exact hr

/-- The machine halts from the configuration `c`. -/
def MHalts (M : CM) (c : CMConf) : Prop :=
  ∃ c', Relation.ReflTransGen (CM.Step M) c c' ∧ M.length ≤ c'.pc

/-- A halting configuration has a deterministic run to an axiom. -/
theorem drun_of_halts {M : CM} {c : CMConf} (hh : MHalts M c) :
    ∀ {Γ p is q}, DInv M Γ p is q c → DRun (dispGoal M.length Γ p is q) := by
  obtain ⟨c', hr, hpc⟩ := hh
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro Γ p is q h
      obtain ⟨g, hg, hax⟩ := sim_halt h hpc
      exact ⟨g, hg.to_reflTransGen, hax⟩
  | head hs _ ih =>
      intro Γ p is q h
      obtain ⟨Γ', p', is', q', ht, h'⟩ := sim_step h hs
      obtain ⟨g, hg, hax⟩ := ih h'
      exact ⟨g, ht.to_reflTransGen.trans hg, hax⟩

/-- A goal on the path to an encoded configuration that reaches an axiom comes from a halting
configuration. -/
theorem halts_of_run {M : CM} {g ax : Goal} (hr : Relation.ReflTransGen DStep g ax)
    (hax : IsAxiom ax) : ∀ Γ p is q c, DInv M Γ p is q c →
      Relation.ReflTransGen DStep g (dispGoal M.length Γ p is q) → MHalts M c := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro Γ p is q c _ h
      rcases Relation.ReflTransGen.cases_head h with h | ⟨x, hx, _⟩
      · exact absurd (h ▸ hax) (dispGoal_not_axiom _ _ _ _ _)
      · exact absurd hx (isAxiom_no_step hax)
  | head hs _ ih =>
      intro Γ p is q c hinv h
      rcases det_rtg hs h with he | h'
      · by_cases hpc : M.length ≤ c.pc
        · exact ⟨c, .refl, hpc⟩
        · obtain ⟨c₁, hc₁⟩ := progress (Nat.lt_of_not_le hpc)
          obtain ⟨Γ', p', is', q', ht, hinv'⟩ := sim_step hinv hc₁
          obtain ⟨c', h1, h2⟩ := ih Γ' p' is' q' c₁ hinv' (det_tg hs (he ▸ ht))
          exact ⟨c', .head hc₁ h1, h2⟩
      · exact ih Γ p is q c hinv h'

/-! ### Conservativity of full F<: over F<:^D on runs that never get stuck -/

/-- The deterministic run from `g` never gets stuck: every goal it reaches is an axiom or makes
a step. -/
def NoStuck (g : Goal) : Prop :=
  ∀ g', Relation.ReflTransGen DStep g g' → IsAxiom g' ∨ ∃ g'', DStep g' g''

/-- **Conservativity**: on a goal whose deterministic run never gets stuck, a derivation in full
F<: gives a derivation in F<:^D.  At a non-axiom goal the deterministic step is always one of the
premises of the rule of full F<: that derives it. -/
theorem sub_to_subD_of_noStuck {g : Goal} (hs : Sub g) (hg : NoStuck g) : SubD g := by
  induction hs with
  | top => exact SubD.top
  | refl => exact SubD.refl
  | promote hB h1 h2 _ ih =>
      exact SubD.promote hB h1 h2 (ih fun g' hr => hg g' (.head (DStep.promote hB h1 h2) hr))
  | @all Γ S₁ S₂ T₁ T₂ _ _ ih₁ ih₂ =>
      rcases hg _ .refl with hax | ⟨g'', hs''⟩
      · rcases hax with h | ⟨i, h1, h2⟩ <;> simp at *
      · cases hs'' with
        | allTop h =>
            exact SubD.allTop (ih₂ fun g' hr => hg g' (.head (DStep.allTop h) hr))
        | neg =>
            exact SubD.neg (ih₁ fun g' hr => hg g' (.head DStep.neg hr))

/-- A goal lies on the run of an encoded configuration, or on a run to an axiom. -/
def OnRun (M : CM) (g : Goal) : Prop :=
  (∃ Γ p is q c, DInv M Γ p is q c ∧ Relation.ReflTransGen DStep g (dispGoal M.length Γ p is q))
    ∨ ∃ ax, IsAxiom ax ∧ Relation.ReflTransGen DStep g ax

/-- From an encoded configuration the run continues to the next encoded configuration or to
an axiom. -/
theorem dispGoal_next {M : CM} {Γ : List Ty} {p q : ℕ} {is : ℕ → ℕ} {c : CMConf}
    (h : DInv M Γ p is q c) : ∃ X, Relation.TransGen DStep (dispGoal M.length Γ p is q) X ∧
      OnRun M X := by
  by_cases hpc : M.length ≤ c.pc
  · obtain ⟨g, hg, hax⟩ := sim_halt h hpc
    exact ⟨g, hg, Or.inr ⟨g, hax, .refl⟩⟩
  · obtain ⟨c₁, hc₁⟩ := progress (Nat.lt_of_not_le hpc)
    obtain ⟨Γ', p', is', q', ht, h'⟩ := sim_step h hc₁
    exact ⟨_, ht, Or.inl ⟨Γ', p', is', q', c₁, h', .refl⟩⟩

theorem OnRun.progress {M : CM} {g : Goal} (h : OnRun M g) : IsAxiom g ∨ ∃ g'', DStep g g'' := by
  rcases h with ⟨Γ, p, is, q, c, hinv, hr⟩ | ⟨ax, hax, hr⟩
  · rcases Relation.ReflTransGen.cases_head hr with he | ⟨x, hx, _⟩
    · subst he
      obtain ⟨X, ht, _⟩ := dispGoal_next hinv
      obtain ⟨y, hy, _⟩ := Relation.TransGen.head'_iff.1 ht
      exact Or.inr ⟨y, hy⟩
    · exact Or.inr ⟨x, hx⟩
  · rcases Relation.ReflTransGen.cases_head hr with he | ⟨x, hx, _⟩
    · exact Or.inl (he ▸ hax)
    · exact Or.inr ⟨x, hx⟩

theorem OnRun.step {M : CM} {g g₁ : Goal} (h : OnRun M g) (hs : DStep g g₁) : OnRun M g₁ := by
  rcases h with ⟨Γ, p, is, q, c, hinv, hr⟩ | ⟨ax, hax, hr⟩
  · rcases det_rtg hs hr with he | h'
    · subst he
      obtain ⟨X, ht, hX⟩ := dispGoal_next hinv
      have h1 := det_tg hs ht
      rcases hX with ⟨Γ', p', is', q', c', hinv', hr'⟩ | ⟨ax, hax, hr'⟩
      · exact Or.inl ⟨Γ', p', is', q', c', hinv', h1.trans hr'⟩
      · exact Or.inr ⟨ax, hax, h1.trans hr'⟩
    · exact Or.inl ⟨Γ, p, is, q, c, hinv, h'⟩
  · rcases det_rtg hs hr with he | h'
    · subst he; exact absurd hs (isAxiom_no_step hax)
    · exact Or.inr ⟨ax, hax, h'⟩

theorem OnRun.rtg {M : CM} {g g' : Goal} (h : OnRun M g) (hr : Relation.ReflTransGen DStep g g') :
    OnRun M g' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem noStuck_of_onRun {M : CM} {g : Goal} (h : OnRun M g) : NoStuck g :=
  fun _ hr => (h.rtg hr).progress


/-! ### The initial goal -/

/-- The context entries of a counter equal to `v` in slot `s`: a chain of numerals. -/
def chain (n s : ℕ) : ℕ → List Ty
  | 0 => [zeroT n]
  | v + 1 => succT n s (.var 0) :: chain n s v

theorem chain_length (n s v : ℕ) : (chain n s v).length = v + 1 := by
  induction v <;> simp [chain, *]

theorem rep_chain (n s : ℕ) (R : List Ty) : ∀ v, Rep n s (chain n s v ++ R) 0 v
  | 0 => Res.here (by simp [get, chain, lift_zeroT])
  | v + 1 => by
      refine ⟨1, Res.here ?_, ?_⟩
      · simp [get, chain, lift_succT, Ty.lift]
      · have := (rep_chain n s R v).append [succT n s (.var 0)]
        simpa [chain] using this

/-- The program part of the initial context: the codes of the labels `0 … n` and the
trampoline. -/
def progCtx (M : CM) : List Ty :=
  (List.range (M.length + 1)).map (codeAt M) ++ [dispT M.length]

/-- The initial context: the two counters and the program. -/
def initCtx (M : CM) (a b : ℕ) : List Ty :=
  (chain M.length 0 a ++ chain M.length 1 b) ++ progCtx M

/-- The initial slots: the counters, then (for the code slots) the codes, and the trampoline. -/
def initSlots (M : CM) (a b : ℕ) : ℕ → ℕ := fun k =>
  if k = 0 then 0 else if k = 1 then a + 1
  else if k ≤ M.length + 4 then (k - 4) + (a + b + 2) else (M.length + 1) + (a + b + 2)

/-- **The encoding of a two-counter machine and its initial counters as an F<:^D goal**: the
call of the code of label `0` with the initial slots and the trampoline as continuation. -/
def enc (M : CM) (a b : ℕ) : Goal :=
  dispGoal M.length (initCtx M a b) (0 + (a + b + 2)) (initSlots M a b)
    ((M.length + 1) + (a + b + 2))

theorem res_closed {Δ L : List Ty} {l : ℕ} {X : Ty} (hL : L[l]? = some X)
    (hX : ∀ c, Ty.lift c 0 X = X) : Res (Δ ++ L) (l + Δ.length) X :=
  Res.here (by rw [get_append]; simp [get, hL, hX])

theorem initCtx_eq (M : CM) (a b : ℕ) :
    initCtx M a b = (chain M.length 0 a ++ chain M.length 1 b) ++ progCtx M := rfl

theorem init_len (M : CM) (a b : ℕ) :
    (chain M.length 0 a ++ chain M.length 1 b).length = a + b + 2 := by
  simp [chain_length]; omega

theorem res_init_code (M : CM) (a b : ℕ) {l : ℕ} (hl : l ≤ M.length) :
    Res (initCtx M a b) (l + (a + b + 2)) (codeAt M l) := by
  rw [initCtx_eq, ← init_len M a b]
  refine res_closed ?_ (fun c => lift_codeAt M c 0 l)
  rw [progCtx, List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_range (by omega : l < M.length + 1)]

theorem res_init_disp (M : CM) (a b : ℕ) :
    Res (initCtx M a b) ((M.length + 1) + (a + b + 2)) (dispT M.length) := by
  rw [initCtx_eq, ← init_len M a b]
  refine res_closed ?_ (fun c => lift_dispT M.length c 0)
  rw [progCtx, List.getElem?_append_right (by simp)]
  simp

/-- The initial goal encodes the initial configuration. -/
theorem enc_inv (M : CM) (a b : ℕ) :
    DInv M (initCtx M a b) (0 + (a + b + 2)) (initSlots M a b) ((M.length + 1) + (a + b + 2))
      ⟨0, a, b⟩ where
  pc := res_init_code M a b (Nat.zero_le _)
  disp := res_init_disp M a b
  code l hl := by
    have : initSlots M a b (4 + l) = l + (a + b + 2) := by
      simp only [initSlots]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      omega
    rw [this]
    exact res_init_code M a b hl
  dslot := by
    have : initSlots M a b (M.length + 5) = (M.length + 1) + (a + b + 2) := by
      simp only [initSlots]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rw [this]
    exact res_init_disp M a b
  rep s hs := by
    rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · simp only [initSlots, cnt, if_pos]
      rw [initCtx_eq, List.append_assoc]
      exact rep_chain _ _ _ a
    · simp only [initSlots, cnt, if_neg (by omega : (1 : ℕ) ≠ 0), if_pos]
      rw [initCtx_eq, List.append_assoc]
      have := (rep_chain M.length 1 (progCtx M) b).append (chain M.length 0 a)
      rwa [chain_length, Nat.zero_add] at this

/-! ### The simulation -/

/-- **Halting is a halting deterministic run**: `CM.Halts M a b ↔ DRun (enc M a b)`. -/
theorem halts_iff_drun (M : CM) (a b : ℕ) : CM.Halts M a b ↔ DRun (enc M a b) :=
  ⟨fun h => drun_of_halts (c := ⟨0, a, b⟩) h (enc_inv M a b),
    fun ⟨_, hr, hax⟩ => halts_of_run hr hax _ _ _ _ _ (enc_inv M a b) .refl⟩

/-- The deterministic run from an encoded goal never gets stuck. -/
theorem enc_noStuck (M : CM) (a b : ℕ) : NoStuck (enc M a b) :=
  noStuck_of_onRun (Or.inl ⟨_, _, _, _, _, enc_inv M a b, .refl⟩)

/-- **Conservativity on encoded goals**: full F<: derives an encoded goal only if F<:^D does. -/
theorem enc_conservative (M : CM) (a b : ℕ) : Sub (enc M a b) → SubD (enc M a b) :=
  fun h => sub_to_subD_of_noStuck h (enc_noStuck M a b)

/-- **The simulation** (the first missing lemma named in round 6). -/
theorem simulation : ∃ enc : CM → ℕ → ℕ → Goal,
    (∀ M a b, CM.Halts M a b ↔ DRun (enc M a b)) ∧ ∀ M a b, Sub (enc M a b) → SubD (enc M a b) :=
  ⟨enc, halts_iff_drun, enc_conservative⟩

/-- **Pierce's first lemma**: `FsubGhelli.RowingFirstLemma`. -/
theorem rowingFirstLemma : RowingFirstLemma := rowingFirstLemma_of_simulation simulation

/-- **The reduction of two-counter halting to subtyping in full F<:**: a machine halts from
`(0, a, b)` exactly when the encoded goal is derivable in full F<: (and exactly when it is
derivable in F<:^D). -/
theorem cm_halts_iff_sub (M : CM) (a b : ℕ) : CM.Halts M a b ↔ Sub (enc M a b) :=
  ⟨fun h => sub_of_run ((halts_iff_drun M a b).1 h),
    fun h => (halts_iff_drun M a b).2 (subD_iff_run.1 (enc_conservative M a b h))⟩

theorem cm_halts_iff_subD (M : CM) (a b : ℕ) : CM.Halts M a b ↔ SubD (enc M a b) :=
  (halts_iff_drun M a b).trans subD_iff_run.symm

end FsubPierce
