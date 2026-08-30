/-
**Every function recursive in an oracle is an oracle machine.**

`Start/OracleMachine.lean` defines the indexed family `Φ_e^A` of oracle machines.  This file
proves that the family is *complete*: every partial function that is recursive in `A` — in
mathlib's sense, `RecursiveIn {oracleFun A} f` — is `Φ_e^A` for some index `e`.  This is what
turns diagonal arguments over the indices into theorems about relative computability.

The proof goes through an intermediate notion.  A partial recursive `F : ℕ →. ℕ`, thought of as
reading a coded oracle segment together with the real input, *simulates* `f` when the value of `f`
is exactly the value that `F` produces once the segment is long enough
(`Lambda.Oracle.Simulates`).  Simulation is preserved by all the closure operations of relative
recursion (`Lambda.Oracle.Simulates.pair`, `.comp`, `.prec`, `.rfind`), and a simulation can be
compiled into an index (`Lambda.Oracle.exists_index_of_simulates`).

* `Lambda.Oracle.oracleFun` — the oracle as a partial function, the shape mathlib's `RecursiveIn`
  expects;
* `Lambda.Oracle.Simulates` — the simulation relation;
* `Lambda.Oracle.exists_index_of_simulates` — a simulation yields an index of the simulated
  function;
* `Lambda.Oracle.exists_simulates_of_recursiveIn` — every function recursive in `A` is simulated;
* `Lambda.Oracle.exists_index_of_recursiveIn` — **completeness of the indexing**: every function
  recursive in `A` is `Φ_e^A` for some `e`.
-/

import Start.OracleMachine
import Mathlib.Computability.TuringDegree

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)

/-! ### Closure rules for `RecursiveIn` on `ℕ →. ℕ`

Mathlib states the closure rules of relative recursiveness as the constructors of the inductive
predicate `Nat.RecursiveIn`, while the bundled `RecursiveIn` used throughout this development is
its `Primcodable` wrapper.  The following wrappers transport each constructor across
`RecursiveIn.iff_nat`, so that the numeric closure rules are available for `RecursiveIn` itself. -/

variable {O : Set (ℕ →. ℕ)}

/-- The zero function is recursive in any oracle. -/
theorem recIn_zero : RecursiveIn O fun _ : ℕ => (0 : Part ℕ) :=
  RecursiveIn.iff_nat.mpr .zero

/-- The successor function is recursive in any oracle. -/
theorem recIn_succ : RecursiveIn O fun n : ℕ => (Nat.succ n : Part ℕ) :=
  RecursiveIn.iff_nat.mpr .succ

/-- The left projection of the pairing is recursive in any oracle. -/
theorem recIn_left : RecursiveIn O fun n : ℕ => ((Nat.unpair n).1 : Part ℕ) :=
  RecursiveIn.iff_nat.mpr .left

/-- The right projection of the pairing is recursive in any oracle. -/
theorem recIn_right : RecursiveIn O fun n : ℕ => ((Nat.unpair n).2 : Part ℕ) :=
  RecursiveIn.iff_nat.mpr .right

/-- Relative recursiveness is closed under pairing. -/
theorem recIn_pair {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O fun n => (Nat.pair <$> f n <*> g n) :=
  RecursiveIn.iff_nat.mpr (.pair (RecursiveIn.iff_nat.mp hf) (RecursiveIn.iff_nat.mp hg))

/-- Relative recursiveness is closed under composition. -/
theorem recIn_comp {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O fun n => g n >>= f :=
  RecursiveIn.iff_nat.mpr (.comp (RecursiveIn.iff_nat.mp hf) (RecursiveIn.iff_nat.mp hg))

/-- Relative recursiveness is closed under primitive recursion. -/
theorem recIn_prec {f g : ℕ →. ℕ} (hf : RecursiveIn O f) (hg : RecursiveIn O g) :
    RecursiveIn O fun p : ℕ =>
      Nat.rec (motive := fun _ => Part ℕ) (f (Nat.unpair p).1)
        (fun y IH => IH.bind fun i => g (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))
        (Nat.unpair p).2 :=
  RecursiveIn.iff_nat.mpr (.prec (RecursiveIn.iff_nat.mp hf) (RecursiveIn.iff_nat.mp hg))

/-- Relative recursiveness is closed under unbounded search. -/
theorem recIn_rfind {f : ℕ →. ℕ} (hf : RecursiveIn O f) :
    RecursiveIn O fun a => Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n) :=
  RecursiveIn.iff_nat.mpr (.rfind (RecursiveIn.iff_nat.mp hf))

/-- The oracle `A`, viewed as a (total) partial function, the shape that mathlib's `RecursiveIn`
expects. -/
def oracleFun (A : ℕ → Bool) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)

/-- `F` **simulates** `f` with oracle `A`: reading longer segments of the oracle never withdraws a
value, and the values of `f` are exactly the values `F` produces from some segment. -/
def Simulates (A : ℕ → Bool) (F f : ℕ →. ℕ) : Prop :=
  (∀ x y s t, s ≤ t → y ∈ F (Nat.pair (segNum A s) x) → y ∈ F (Nat.pair (segNum A t) x)) ∧
  (∀ x y, y ∈ f x ↔ ∃ s, y ∈ F (Nat.pair (segNum A s) x))

namespace Simulates

variable {A : ℕ → Bool} {F f : ℕ →. ℕ}

theorem mono (h : Simulates A F f) {x y s t : ℕ} (hst : s ≤ t)
    (hy : y ∈ F (Nat.pair (segNum A s) x)) : y ∈ F (Nat.pair (segNum A t) x) :=
  h.1 x y s t hst hy

theorem mem_iff (h : Simulates A F f) {x y : ℕ} :
    y ∈ f x ↔ ∃ s, y ∈ F (Nat.pair (segNum A s) x) := h.2 x y

/-- Two values obtained from possibly different segments are obtained from a common one. -/
theorem mono_max (h : Simulates A F f) {x y s t : ℕ}
    (hy : y ∈ F (Nat.pair (segNum A s) x)) : y ∈ F (Nat.pair (segNum A (max s t)) x) :=
  h.mono (le_max_left s t) hy

end Simulates

/-! ## From a simulation to an index -/

/-- If some stage of `Nat.rfindOpt` converges and all converging stages agree, then the search
returns that common value. -/
theorem mem_rfindOpt_of_unique {g : ℕ → Option ℕ} {y s : ℕ} (hs : g s = some y)
    (huniq : ∀ m z, g m = some z → z = y) : y ∈ Nat.rfindOpt g := by
  classical
  have hex : ∃ m, (g m).isSome := ⟨s, by simp [hs]⟩
  obtain ⟨z, hz⟩ : ∃ z, g (Nat.find hex) = some z := Option.isSome_iff_exists.1 (Nat.find_spec hex)
  have hzy : z = y := huniq _ _ hz
  refine mem_rfindOpt_iff.2 ⟨Nat.find hex, by rw [hz, hzy], fun m hm => ?_⟩
  have hmin := Nat.find_min hex hm
  exact Option.not_isSome_iff_eq_none.1 hmin

/-- A code that simulates `f` computes `f` as an oracle machine. -/
theorem evalOracle_eq_of_simulates {A : ℕ → Bool} {c : Code} {f : ℕ →. ℕ}
    (hsim : Simulates A (Code.eval c) f) : evalOracle A c = f := by
  funext x
  apply Part.ext
  intro y
  constructor
  · intro hy
    obtain ⟨s, hs⟩ := exists_stage_of_mem_evalOracle hy
    have : y ∈ Code.eval c (Nat.pair (segNum A s.unpair.2) x) :=
      Code.evaln_sound (by simpa [oracleStep] using hs)
    exact hsim.mem_iff.2 ⟨s.unpair.2, this⟩
  · intro hy
    obtain ⟨s, hs⟩ := hsim.mem_iff.1 hy
    obtain ⟨k, hk⟩ := Code.evaln_complete.1 hs
    refine mem_rfindOpt_of_unique (s := Nat.pair k s) ?_ ?_
    · simpa [oracleStep, Nat.unpair_pair] using hk
    · intro m z hm
      have hz : z ∈ Code.eval c (Nat.pair (segNum A m.unpair.2) x) :=
        Code.evaln_sound (by simpa [oracleStep] using hm)
      have h1 : z ∈ Code.eval c (Nat.pair (segNum A (max m.unpair.2 s)) x) := hsim.mono_max hz
      have h2 : y ∈ Code.eval c (Nat.pair (segNum A (max m.unpair.2 s)) x) :=
        hsim.mono (le_max_right m.unpair.2 s) hs
      exact Part.mem_unique h1 h2

/-- A simulation can be compiled into an index of the simulated function. -/
theorem exists_index_of_simulates {A : ℕ → Bool} {F f : ℕ →. ℕ} (hF : Nat.Partrec F)
    (hsim : Simulates A F f) : ∃ e : ℕ, Phi A e = f := by
  obtain ⟨c, hc⟩ := Code.exists_code.1 hF
  refine ⟨encode c, ?_⟩
  funext x
  rw [Phi_encode]
  exact congrFun (evalOracle_eq_of_simulates (by rw [hc]; exact hsim)) x

/-! ## Simulations for the closure operations -/

/-- A machine that ignores the oracle simulates the function it computes. -/
def liftFun (g : ℕ →. ℕ) : ℕ →. ℕ := fun z => g z.unpair.2

theorem partrec_liftFun {g : ℕ →. ℕ} (hg : Nat.Partrec g) : Nat.Partrec (liftFun g) := by
  have : Partrec fun z : ℕ => g z.unpair.2 :=
    (Partrec.nat_iff.2 hg).comp (Primrec.snd.comp Primrec.unpair).to_comp
  exact Partrec.nat_iff.1 this

theorem simulates_liftFun (A : ℕ → Bool) (g : ℕ →. ℕ) : Simulates A (liftFun g) g := by
  constructor
  · intro x y s t _ hy
    simpa [liftFun] using hy
  · intro x y
    constructor
    · intro hy; exact ⟨0, by simpa [liftFun] using hy⟩
    · rintro ⟨s, hs⟩; simpa [liftFun] using hs

/-- The machine that answers an oracle query out of the segment it was given. -/
def queryFun : ℕ →. ℕ := fun z =>
  ((segQuery z.unpair.1 z.unpair.2).map fun b => if b then 1 else 0 : Option ℕ)

theorem primrec_segQuery : Primrec₂ segQuery := by
  have hdec : Primrec fun sigma : ℕ => segDecode sigma :=
    Primrec.option_getD.comp (Primrec.decode (α := List Bool)) (Primrec.const [])
  have h : Primrec₂ fun sigma x : ℕ => (segDecode sigma)[x]? :=
    Primrec₂.comp Primrec.list_getElem? (hdec.comp Primrec.fst) Primrec.snd
  exact h

theorem partrec_queryFun : Nat.Partrec queryFun := by
  have hcomp : Computable fun z : ℕ =>
      (segQuery z.unpair.1 z.unpair.2).map fun b => if b then 1 else 0 :=
    Primrec.to_comp <| Primrec.option_map
      (primrec_segQuery.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0)).to₂
  exact Partrec.nat_iff.1 (Computable.ofOption hcomp)

theorem simulates_queryFun (A : ℕ → Bool) : Simulates A queryFun (oracleFun A) := by
  constructor
  · intro x y s t hst hy
    simp only [queryFun, Nat.unpair_pair, Option.mem_def, Option.map_eq_some_iff,
      Part.mem_coe] at hy ⊢
    obtain ⟨b, hb, hy⟩ := hy
    exact ⟨b, segQuery_mono hst hb, hy⟩
  · intro x y
    simp only [queryFun, Nat.unpair_pair, oracleFun, Part.mem_some_iff, Part.mem_coe,
      Option.mem_def, Option.map_eq_some_iff]
    constructor
    · intro hy
      exact ⟨x + 1, A x, segQuery_segNum_of_lt (Nat.lt_succ_self x), by rw [← hy]⟩
    · rintro ⟨s, b, hb, hy⟩
      rw [segQuery_segNum] at hb
      by_cases hx : x < s
      · simp only [hx, if_true, Option.some_inj] at hb
        rw [← hy, hb]
      · simp [hx] at hb

/-! ## Closure of simulations under the recursion-theoretic operations -/


theorem mem_pair_seq {G₁ G₂ : Part ℕ} {y : ℕ} :
    y ∈ (Nat.pair <$> G₁ <*> G₂) ↔ ∃ u ∈ G₁, ∃ v ∈ G₂, y = Nat.pair u v := by
  simp [Seq.seq, Part.mem_bind_iff]
  aesop

/-- Simulations are closed under pairing. -/
theorem Simulates.pairing {A : ℕ → Bool} {F₁ F₂ f₁ f₂ : ℕ →. ℕ}
    (h₁ : Simulates A F₁ f₁) (h₂ : Simulates A F₂ f₂) :
    Simulates A (fun z => Nat.pair <$> F₁ z <*> F₂ z) (fun n => Nat.pair <$> f₁ n <*> f₂ n) := by
  constructor
  · intro x y s t hst hy
    rw [mem_pair_seq] at hy ⊢
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    exact ⟨u, h₁.mono hst hu, v, h₂.mono hst hv, rfl⟩
  · intro x y
    rw [mem_pair_seq]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      obtain ⟨s₁, hs₁⟩ := h₁.mem_iff.1 hu
      obtain ⟨s₂, hs₂⟩ := h₂.mem_iff.1 hv
      refine ⟨max s₁ s₂, mem_pair_seq.2 ⟨u, h₁.mono (le_max_left _ _) hs₁, v,
        h₂.mono (le_max_right _ _) hs₂, rfl⟩⟩
    · rintro ⟨s, hs⟩
      rw [mem_pair_seq] at hs
      obtain ⟨u, hu, v, hv, rfl⟩ := hs
      exact ⟨u, h₁.mem_iff.2 ⟨s, hu⟩, v, h₂.mem_iff.2 ⟨s, hv⟩, rfl⟩

/-- Simulations are closed under composition. -/
theorem Simulates.composition {A : ℕ → Bool} {F₁ F₂ f₁ f₂ : ℕ →. ℕ}
    (h₁ : Simulates A F₁ f₁) (h₂ : Simulates A F₂ f₂) :
    Simulates A (fun z => (F₂ z).bind fun v => F₁ (Nat.pair z.unpair.1 v))
      (fun n => (f₂ n).bind f₁) := by
  constructor
  · intro x y s t hst hy
    simp only [Nat.unpair_pair, Part.mem_bind_iff] at hy ⊢
    obtain ⟨v, hv, hy⟩ := hy
    exact ⟨v, h₂.mono hst hv, h₁.mono hst hy⟩
  · intro x y
    simp only [Nat.unpair_pair, Part.mem_bind_iff]
    constructor
    · intro hmem
      obtain ⟨v, hv, hy⟩ := Part.mem_bind_iff.mp hmem
      obtain ⟨s₁, hs₁⟩ := h₂.mem_iff.1 hv
      obtain ⟨s₂, hs₂⟩ := h₁.mem_iff.1 hy
      exact ⟨max s₁ s₂, v, h₂.mono (le_max_left _ _) hs₁, h₁.mono (le_max_right _ _) hs₂⟩
    · rintro ⟨s, v, hv, hy⟩
      exact Part.mem_bind_iff.mpr ⟨v, h₂.mem_iff.2 ⟨s, hv⟩, h₁.mem_iff.2 ⟨s, hy⟩⟩



/-- The oracle version of primitive recursion: the segment is threaded through the recursion. -/
def precFun (F₁ F₂ : ℕ →. ℕ) : ℕ →. ℕ := fun z =>
  Nat.rec (F₁ (Nat.pair z.unpair.1 z.unpair.2.unpair.1))
    (fun y IH => IH.bind fun i =>
      F₂ (Nat.pair z.unpair.1 (Nat.pair z.unpair.2.unpair.1 (Nat.pair y i))))
    z.unpair.2.unpair.2

theorem precFun_zero (F₁ F₂ : ℕ →. ℕ) (sigma a : ℕ) :
    precFun F₁ F₂ (Nat.pair sigma (Nat.pair a 0)) = F₁ (Nat.pair sigma a) := by
  simp [precFun]

theorem precFun_succ (F₁ F₂ : ℕ →. ℕ) (sigma a n : ℕ) :
    precFun F₁ F₂ (Nat.pair sigma (Nat.pair a (n + 1))) =
      (precFun F₁ F₂ (Nat.pair sigma (Nat.pair a n))).bind fun i =>
        F₂ (Nat.pair sigma (Nat.pair a (Nat.pair n i))) := by
  simp [precFun]

theorem partrec_precFun {F₁ F₂ : ℕ →. ℕ} (h₁ : Nat.Partrec F₁) (h₂ : Nat.Partrec F₂) :
    Nat.Partrec (precFun F₁ F₂) := by
  have h₂' : Nat.Partrec fun u : ℕ =>
      F₂ (Nat.pair u.unpair.1.unpair.1 (Nat.pair u.unpair.1.unpair.2 u.unpair.2)) := by
    refine Partrec.nat_iff.1 ((Partrec.nat_iff.2 h₂).comp ?_)
    exact Primrec.to_comp <| Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair))
  have hG := Nat.Partrec.prec h₁ h₂'
  have hcomp : Nat.Partrec fun z : ℕ =>
      (Nat.unpaired fun w n =>
        Nat.rec (F₁ w)
          (fun y IH => IH.bind fun i =>
            F₂ (Nat.pair (Nat.pair w (Nat.pair y i)).unpair.1.unpair.1
              (Nat.pair (Nat.pair w (Nat.pair y i)).unpair.1.unpair.2
                (Nat.pair w (Nat.pair y i)).unpair.2)))
          n)
        (Nat.pair (Nat.pair z.unpair.1 z.unpair.2.unpair.1) z.unpair.2.unpair.2) := by
    refine Partrec.nat_iff.1 ((Partrec.nat_iff.2 hG).comp ?_)
    exact Primrec.to_comp <| Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  refine hcomp.of_eq fun z => ?_
  simp [precFun, Nat.unpaired]

/-- Primitive recursion on the unrelativised side. -/
def precBase (f₁ f₂ : ℕ →. ℕ) : ℕ →. ℕ := fun p =>
  Nat.rec (f₁ p.unpair.1)
    (fun y IH => IH.bind fun i => f₂ (Nat.pair p.unpair.1 (Nat.pair y i))) p.unpair.2

theorem precBase_zero (f₁ f₂ : ℕ →. ℕ) (a : ℕ) :
    precBase f₁ f₂ (Nat.pair a 0) = f₁ a := by simp [precBase]

theorem precBase_succ (f₁ f₂ : ℕ →. ℕ) (a n : ℕ) :
    precBase f₁ f₂ (Nat.pair a (n + 1)) =
      (precBase f₁ f₂ (Nat.pair a n)).bind fun i => f₂ (Nat.pair a (Nat.pair n i)) := by
  simp [precBase]

theorem Simulates.precn {A : ℕ → Bool} {F₁ F₂ f₁ f₂ : ℕ →. ℕ}
    (h₁ : Simulates A F₁ f₁) (h₂ : Simulates A F₂ f₂) :
    Simulates A (precFun F₁ F₂) (precBase f₁ f₂) := by
  have hmono : ∀ n a y s t, s ≤ t →
      y ∈ precFun F₁ F₂ (Nat.pair (segNum A s) (Nat.pair a n)) →
      y ∈ precFun F₁ F₂ (Nat.pair (segNum A t) (Nat.pair a n)) := by
    intro n
    induction n with
    | zero =>
        intro a y s t hst hy
        rw [precFun_zero] at hy ⊢
        exact h₁.mono hst hy
    | succ n ih =>
        intro a y s t hst hy
        rw [precFun_succ] at hy ⊢
        simp only [Part.mem_bind_iff] at hy ⊢
        obtain ⟨i, hi, hy⟩ := hy
        exact ⟨i, ih a i s t hst hi, h₂.mono hst hy⟩
  refine ⟨?_, ?_⟩
  · intro x y s t hst hy
    have hx : Nat.pair x.unpair.1 x.unpair.2 = x := Nat.pair_unpair x
    rw [← hx] at hy ⊢
    exact hmono _ _ _ _ _ hst hy
  · have key : ∀ n a y, y ∈ precBase f₁ f₂ (Nat.pair a n) ↔
        ∃ s, y ∈ precFun F₁ F₂ (Nat.pair (segNum A s) (Nat.pair a n)) := by
      intro n
      induction n with
      | zero =>
          intro a y
          rw [precBase_zero]
          constructor
          · intro hy
            obtain ⟨s, hs⟩ := h₁.mem_iff.1 hy
            exact ⟨s, by rw [precFun_zero]; exact hs⟩
          · rintro ⟨s, hs⟩
            rw [precFun_zero] at hs
            exact h₁.mem_iff.2 ⟨s, hs⟩
      | succ n ih =>
          intro a y
          rw [precBase_succ]
          simp only [Part.mem_bind_iff]
          constructor
          · rintro ⟨i, hi, hy⟩
            obtain ⟨s₁, hs₁⟩ := (ih a i).1 hi
            obtain ⟨s₂, hs₂⟩ := h₂.mem_iff.1 hy
            refine ⟨max s₁ s₂, ?_⟩
            rw [precFun_succ]
            simp only [Part.mem_bind_iff]
            exact ⟨i, hmono _ _ _ _ _ (le_max_left s₁ s₂) hs₁,
              h₂.mono (le_max_right s₁ s₂) hs₂⟩
          · rintro ⟨s, hs⟩
            rw [precFun_succ] at hs
            simp only [Part.mem_bind_iff] at hs
            obtain ⟨i, hi, hy⟩ := hs
            exact ⟨i, (ih a i).2 ⟨s, hi⟩, h₂.mem_iff.2 ⟨s, hy⟩⟩
    intro x y
    have hx : Nat.pair x.unpair.1 x.unpair.2 = x := Nat.pair_unpair x
    rw [← hx]
    exact key _ _ _



/-- The oracle version of unbounded search. -/
def rfindFun (F₁ : ℕ →. ℕ) : ℕ →. ℕ := fun z =>
  Nat.rfind fun n =>
    (fun m => decide (m = 0)) <$> F₁ (Nat.pair z.unpair.1 (Nat.pair z.unpair.2 n))

/-- Unbounded search on the unrelativised side. -/
def rfindBase (f₁ : ℕ →. ℕ) : ℕ →. ℕ := fun a =>
  Nat.rfind fun n => (fun m => decide (m = 0)) <$> f₁ (Nat.pair a n)

theorem partrec_rfindFun {F₁ : ℕ →. ℕ} (h₁ : Nat.Partrec F₁) : Nat.Partrec (rfindFun F₁) := by
  have h₁' : Nat.Partrec fun u : ℕ =>
      F₁ (Nat.pair u.unpair.1.unpair.1 (Nat.pair u.unpair.1.unpair.2 u.unpair.2)) := by
    refine Partrec.nat_iff.1 ((Partrec.nat_iff.2 h₁).comp ?_)
    exact Primrec.to_comp <| Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec₂.natPair.comp
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
        (Primrec.snd.comp Primrec.unpair))
  refine (Nat.Partrec.rfind h₁').of_eq fun z => ?_
  simp [rfindFun]

theorem mem_rfind_iff {g : ℕ →. ℕ} {y : ℕ} :
    y ∈ (Nat.rfind fun n => (fun m => decide (m = 0)) <$> g n) ↔
      (0 : ℕ) ∈ g y ∧ ∀ m < y, ∃ v, v ∈ g m ∧ v ≠ 0 := by
  constructor
  · intro hmem
    obtain ⟨h0, hlt⟩ := Nat.mem_rfind.mp hmem
    simp only [Part.map_eq_map, Part.mem_map_iff, decide_eq_true_eq, exists_eq_right] at h0
    refine ⟨h0, fun m hm => ?_⟩
    have h := hlt (m := m) hm
    simp only [Part.map_eq_map, Part.mem_map_iff, decide_eq_false_iff_not] at h
    obtain ⟨v, hv, hv0⟩ := h
    exact ⟨v, hv, hv0⟩
  · rintro ⟨h0, hlt⟩
    refine Nat.mem_rfind.mpr ⟨?_, ?_⟩
    · simp only [Part.map_eq_map, Part.mem_map_iff, decide_eq_true_eq, exists_eq_right]
      exact h0
    · intro m hm
      obtain ⟨v, hv, hv0⟩ := hlt m hm
      simp only [Part.map_eq_map, Part.mem_map_iff, decide_eq_false_iff_not]
      exact ⟨v, hv, hv0⟩

theorem Simulates.rfindn {A : ℕ → Bool} {F₁ f₁ : ℕ →. ℕ} (h₁ : Simulates A F₁ f₁) :
    Simulates A (rfindFun F₁) (rfindBase f₁) := by
  have hFmem : ∀ s x y, y ∈ rfindFun F₁ (Nat.pair (segNum A s) x) ↔
      (0 : ℕ) ∈ F₁ (Nat.pair (segNum A s) (Nat.pair x y)) ∧
        ∀ m < y, ∃ v, v ∈ F₁ (Nat.pair (segNum A s) (Nat.pair x m)) ∧ v ≠ 0 := by
    intro s x y
    simp only [rfindFun, Nat.unpair_pair]
    exact mem_rfind_iff (g := fun n => F₁ (Nat.pair (segNum A s) (Nat.pair x n)))
  have hfmem : ∀ x y, y ∈ rfindBase f₁ x ↔
      (0 : ℕ) ∈ f₁ (Nat.pair x y) ∧ ∀ m < y, ∃ v, v ∈ f₁ (Nat.pair x m) ∧ v ≠ 0 := by
    intro x y
    exact mem_rfind_iff (g := fun n => f₁ (Nat.pair x n))
  refine ⟨?_, ?_⟩
  · intro x y s t hst hy
    rw [hFmem] at hy ⊢
    refine ⟨h₁.mono hst hy.1, fun m hm => ?_⟩
    obtain ⟨v, hv, hv0⟩ := hy.2 m hm
    exact ⟨v, h₁.mono hst hv, hv0⟩
  · intro x y
    rw [hfmem]
    constructor
    · rintro ⟨h0, hlt⟩
      -- collect a single segment good for all the finitely many values below `y`
      have key : ∀ N, (∀ m < N, ∃ v, v ∈ f₁ (Nat.pair x m) ∧ v ≠ 0) →
          ∃ s, ∀ m < N, ∃ v, v ∈ F₁ (Nat.pair (segNum A s) (Nat.pair x m)) ∧ v ≠ 0 := by
        intro N
        induction N with
        | zero => intro _; exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
        | succ N ih =>
            intro hN
            obtain ⟨s, hs⟩ := ih fun m hm => hN m (Nat.lt_succ_of_lt hm)
            obtain ⟨v, hv, hv0⟩ := hN N (Nat.lt_succ_self N)
            obtain ⟨s', hs'⟩ := h₁.mem_iff.1 hv
            refine ⟨max s s', fun m hm => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm' | rfl
            · obtain ⟨w, hw, hw0⟩ := hs m hm'
              exact ⟨w, h₁.mono (le_max_left s s') hw, hw0⟩
            · exact ⟨v, h₁.mono (le_max_right s s') hs', hv0⟩
      obtain ⟨s₁, hs₁⟩ := key y hlt
      obtain ⟨s₂, hs₂⟩ := h₁.mem_iff.1 h0
      refine ⟨max s₁ s₂, ?_⟩
      rw [hFmem]
      refine ⟨h₁.mono (le_max_right s₁ s₂) hs₂, fun m hm => ?_⟩
      obtain ⟨v, hv, hv0⟩ := hs₁ m hm
      exact ⟨v, h₁.mono (le_max_left s₁ s₂) hv, hv0⟩
    · rintro ⟨s, hs⟩
      rw [hFmem] at hs
      refine ⟨h₁.mem_iff.2 ⟨s, hs.1⟩, fun m hm => ?_⟩
      obtain ⟨v, hv, hv0⟩ := hs.2 m hm
      exact ⟨v, h₁.mem_iff.2 ⟨s, hv⟩, hv0⟩


/-! ## Completeness of the indexing -/

/-- Every partial function recursive in the oracle `A` is simulated by a partial recursive
machine reading segments of `A`. -/
theorem exists_simulates_of_recursiveIn {A : ℕ → Bool} {f : ℕ →. ℕ}
    (h : RecursiveIn {oracleFun A} f) : ∃ F, Nat.Partrec F ∧ Simulates A F f := by
  replace h : Nat.RecursiveIn {oracleFun A} f := RecursiveIn.iff_nat.mp h
  induction h with
  | zero => exact ⟨liftFun fun _ => 0, partrec_liftFun Nat.Partrec.zero, simulates_liftFun A _⟩
  | succ => exact ⟨liftFun Nat.succ, partrec_liftFun Nat.Partrec.succ, simulates_liftFun A _⟩
  | left => exact ⟨liftFun fun n => (Nat.unpair n).1, partrec_liftFun Nat.Partrec.left,
      simulates_liftFun A _⟩
  | right => exact ⟨liftFun fun n => (Nat.unpair n).2, partrec_liftFun Nat.Partrec.right,
      simulates_liftFun A _⟩
  | oracle g hg =>
      have hgA : g = oracleFun A := by simpa using hg
      exact ⟨queryFun, partrec_queryFun, hgA ▸ simulates_queryFun A⟩
  | pair _ _ ih₁ ih₂ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      obtain ⟨F₂, hF₂, hs₂⟩ := ih₂
      exact ⟨fun z => Nat.pair <$> F₁ z <*> F₂ z, Nat.Partrec.pair hF₁ hF₂, hs₁.pairing hs₂⟩
  | comp _ _ ih₁ ih₂ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      obtain ⟨F₂, hF₂, hs₂⟩ := ih₂
      refine ⟨fun z => (F₂ z).bind fun v => F₁ (Nat.pair z.unpair.1 v), ?_, hs₁.composition hs₂⟩
      refine Partrec.nat_iff.1 (Partrec.bind (Partrec.nat_iff.2 hF₂) ?_)
      exact (Partrec.nat_iff.2 hF₁).comp
        (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst))
          Primrec.snd).to_comp
  | prec _ _ ih₁ ih₂ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      obtain ⟨F₂, hF₂, hs₂⟩ := ih₂
      exact ⟨precFun F₁ F₂, partrec_precFun hF₁ hF₂, hs₁.precn hs₂⟩
  | rfind _ ih₁ =>
      obtain ⟨F₁, hF₁, hs₁⟩ := ih₁
      exact ⟨rfindFun F₁, partrec_rfindFun hF₁, hs₁.rfindn⟩

/-- **Completeness of the oracle indexing**: every partial function recursive in `A` is `Φ_e^A`
for some index `e`. -/
theorem exists_index_of_recursiveIn {A : ℕ → Bool} {f : ℕ →. ℕ}
    (h : RecursiveIn {oracleFun A} f) : ∃ e : ℕ, Phi A e = f := by
  obtain ⟨F, hF, hsim⟩ := exists_simulates_of_recursiveIn h
  exact exists_index_of_simulates hF hsim

end Oracle
end Lambda
