/-
**A computable approximation of the halting oracle `∅'`.**

The halting oracle `∅' = jumpChar (fun _ => false)` of `Start/JumpSigmaOne.lean` is not computable,
but it is *recursively enumerable*: a number enters `∅'` as soon as the corresponding computation
has been seen to converge.  Counting the stages of that search gives a computable, monotone
approximation `Lambda.Oracle.jumpApprox : ℕ → ℕ → Bool` with `∅' = ⋃ s, jumpApprox s`.

This file builds the approximation and proves the three properties the limit lemma
(`Start/LimitLemma.lean`) needs of it: it is primitive recursive, it is sound and monotone, and on
any finite initial segment it agrees with `∅'` from some stage on.

It also contains the small piece of bookkeeping used to run an oracle machine for finitely many
stages: `Lambda.Oracle.scanOf F b` returns the value of the first `t < b` at which `F t` converges.

* `Lambda.Oracle.jumpApprox`, `Lambda.Oracle.primrec₂_jumpApprox`;
* `Lambda.Oracle.jumpApprox_mono`, `Lambda.Oracle.jumpApprox_le_haltingOracle`,
  `Lambda.Oracle.haltingOracle_eq_true_iff` — the approximation is monotone and its union is `∅'`;
* `Lambda.Oracle.exists_jumpApprox_agree` — for every bound `L` the approximation agrees with `∅'`
  below `L` from some stage on;
* `Lambda.Oracle.scanOf`, `Lambda.Oracle.scanOf_eq_none_iff`, `Lambda.Oracle.scanOf_eq_some`.
-/

import Start.JumpSigmaOne

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Oracle

open Encodable Denumerable
open Nat.Partrec (Code)
open scoped Computability

/-! ## Two small helpers -/

/-- A primitive recursive predicate has a primitive recursive characteristic function.  (This
repeats `Lambda.Post.primrec_decide`, which lives in the lambda-calculus part of the library; the
oracle modules do not depend on that part.) -/
theorem primrec_decide_pred {α : Type} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (h : PrimrecPred p) : Primrec fun a => decide (p a) := by
  obtain ⟨_, hprim⟩ := h
  exact hprim.of_eq fun a => by congr 1

/-! ## Segments of a uniformly computable family of oracles -/

/-- The initial segments of a primitive recursive family of oracles are primitive recursive. -/
theorem primrec₂_segNum_family {f : ℕ → ℕ → Bool} (hf : Primrec₂ f) :
    Primrec₂ fun s m => segNum (fun n => f s n) m := by
  have hmap : Primrec fun p : ℕ × ℕ => (List.range p.2).map fun n => f p.1 n :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (hf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.encode.comp hmap

/-- The stage function of a machine run against a primitive recursive family of oracles is
primitive recursive. -/
theorem primrec_oracleStep_family {f : ℕ → ℕ → Bool} (hf : Primrec₂ f) (c : Code) :
    Primrec fun p : (ℕ × ℕ) × ℕ => oracleStep (fun n => f p.1.1 n) c p.1.2 p.2 := by
  have hseg : Primrec fun p : (ℕ × ℕ) × ℕ => segNum (fun n => f p.1.1 n) p.2.unpair.2 :=
    (primrec₂_segNum_family hf).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
  have hinput : Primrec fun p : (ℕ × ℕ) × ℕ =>
      Nat.pair (segNum (fun n => f p.1.1 n) p.2.unpair.2) p.1.2 :=
    Primrec₂.natPair.comp hseg (Primrec.snd.comp Primrec.fst)
  have hfuel : Primrec fun p : (ℕ × ℕ) × ℕ => p.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
  exact Code.primrec_evaln.comp ((hfuel.pair (Primrec.const c)).pair hinput)

/-! ## The approximation -/

/-- The empty oracle. -/
def emptyOracle : ℕ → Bool := fun _ => false

theorem haltingOracle_eq : haltingOracle = jumpChar emptyOracle := rfl

/-- The stage-`s` approximation of the halting oracle: `x` is declared to be in `∅'` as soon as
one of the first `s` stages of the computation `Φ_x^∅(x)` has been seen to converge. -/
def jumpApprox (s x : ℕ) : Bool :=
  s.rec (motive := fun _ => Bool) false
    fun t ih => ih || (oracleStep emptyOracle (ofNat Code x) x t).isSome

@[simp] theorem jumpApprox_zero (x : ℕ) : jumpApprox 0 x = false := rfl

theorem jumpApprox_succ (s x : ℕ) :
    jumpApprox (s + 1) x =
      (jumpApprox s x || (oracleStep emptyOracle (ofNat Code x) x s).isSome) := rfl

theorem primrec₂_jumpApprox : Primrec₂ jumpApprox := by
  have hstep : Primrec fun p : ℕ × (ℕ × Bool) =>
      (oracleStep emptyOracle (ofNat Code p.1) p.1 p.2.1).isSome := by
    have hseg : Primrec fun p : ℕ × (ℕ × Bool) => segNum emptyOracle p.2.1.unpair.2 := by
      have : Primrec fun m : ℕ => segNum emptyOracle m := by
        have hmap : Primrec fun m : ℕ => (List.range m).map fun _ => false :=
          Primrec.list_map Primrec.list_range (Primrec.const false).to₂
        exact Primrec.encode.comp hmap
      exact this.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
    have hcode : Primrec fun p : ℕ × (ℕ × Bool) => (ofNat Code p.1) :=
      (Primrec.ofNat Code).comp Primrec.fst
    have hinput : Primrec fun p : ℕ × (ℕ × Bool) =>
        Nat.pair (segNum emptyOracle p.2.1.unpair.2) p.1 :=
      Primrec₂.natPair.comp hseg Primrec.fst
    have hfuel : Primrec fun p : ℕ × (ℕ × Bool) => p.2.1.unpair.1 :=
      Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd))
    have hev : Primrec fun p : ℕ × (ℕ × Bool) =>
        Code.evaln p.2.1.unpair.1 (ofNat Code p.1)
          (Nat.pair (segNum emptyOracle p.2.1.unpair.2) p.1) :=
      Code.primrec_evaln.comp ((hfuel.pair hcode).pair hinput)
    exact Primrec.option_isSome.comp hev
  have hbody : Primrec₂ fun (x : ℕ) (p : ℕ × Bool) =>
      (p.2 || (oracleStep emptyOracle (ofNat Code x) x p.1).isSome) :=
    (Primrec.dom_bool₂ (· || ·)).comp (Primrec.snd.comp Primrec.snd) hstep
  exact (Primrec.nat_rec (f := fun _ : ℕ => false) (Primrec.const false) hbody).comp₂
    Primrec₂.right Primrec₂.left

theorem jumpApprox_succ_of (s x : ℕ) (h : jumpApprox s x = true) : jumpApprox (s + 1) x = true := by
  rw [jumpApprox_succ, h, Bool.true_or]

/-- The approximation is monotone in the stage. -/
theorem jumpApprox_mono {s t x : ℕ} (hst : s ≤ t) (h : jumpApprox s x = true) :
    jumpApprox t x = true := by
  induction t with
  | zero =>
    rw [Nat.le_zero.1 hst] at h
    exact h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hst) with hlt | rfl
    · exact jumpApprox_succ_of n x (ih (Nat.lt_succ_iff.1 hlt))
    · exact h

theorem jumpApprox_eq_true_iff (s x : ℕ) :
    jumpApprox s x = true ↔ ∃ t < s, (oracleStep emptyOracle (ofNat Code x) x t).isSome := by
  induction s with
  | zero => simp
  | succ n ih =>
    rw [jumpApprox_succ]
    constructor
    · intro h
      rcases Bool.or_eq_true_iff.1 h with h | h
      · obtain ⟨t, ht, hts⟩ := ih.1 h
        exact ⟨t, Nat.lt_succ_of_lt ht, hts⟩
      · exact ⟨n, Nat.lt_succ_self n, h⟩
    · rintro ⟨t, ht, hts⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt | rfl
      · exact Bool.or_eq_true_iff.2 (Or.inl (ih.2 ⟨t, hlt, hts⟩))
      · exact Bool.or_eq_true_iff.2 (Or.inr hts)

/-- The union of the approximations is the halting oracle. -/
theorem haltingOracle_eq_true_iff (x : ℕ) :
    haltingOracle x = true ↔ ∃ s, jumpApprox s x = true := by
  rw [haltingOracle_eq, jumpChar_eq_true_iff]
  constructor
  · intro h
    have hdom : (Nat.rfindOpt (oracleStep emptyOracle (ofNat Code x) x)).Dom := h
    obtain ⟨t, y, hty⟩ := Nat.rfindOpt_dom.1 hdom
    exact ⟨t + 1, (jumpApprox_eq_true_iff (t + 1) x).2 ⟨t, Nat.lt_succ_self t, by
      rw [Option.mem_def.1 hty]; rfl⟩⟩
  · rintro ⟨s, hs⟩
    obtain ⟨t, -, hts⟩ := (jumpApprox_eq_true_iff s x).1 hs
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hts
    have : (Nat.rfindOpt (oracleStep emptyOracle (ofNat Code x) x)).Dom :=
      Nat.rfindOpt_dom.2 ⟨t, y, by simp [hy]⟩
    exact this

/-- The approximation never overshoots. -/
theorem jumpApprox_le_haltingOracle {s x : ℕ} (h : jumpApprox s x = true) :
    haltingOracle x = true :=
  (haltingOracle_eq_true_iff x).2 ⟨s, h⟩

/-- **The approximation settles on every finite initial segment.** -/
theorem exists_jumpApprox_agree (L : ℕ) :
    ∃ s₀, ∀ s, s₀ ≤ s → ∀ n < L, jumpApprox s n = haltingOracle n := by
  induction L with
  | zero => exact ⟨0, fun s _ n hn => absurd hn (Nat.not_lt_zero n)⟩
  | succ L ih =>
    obtain ⟨s₀, hs₀⟩ := ih
    by_cases hL : haltingOracle L = true
    · obtain ⟨s₁, hs₁⟩ := (haltingOracle_eq_true_iff L).1 hL
      refine ⟨max s₀ s₁, fun s hs n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | rfl
      · exact hs₀ s (le_trans (le_max_left s₀ s₁) hs) n hlt
      · rw [hL, jumpApprox_mono (le_trans (le_max_right s₀ s₁) hs) hs₁]
    · refine ⟨s₀, fun s hs n hn => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hn with hlt | rfl
      · exact hs₀ s hs n hlt
      · have hfalse : haltingOracle n = false := Bool.eq_false_iff.2 hL
        have happrox : jumpApprox s n = false := by
          rcases Bool.eq_false_or_eq_true (jumpApprox s n) with h' | h'
          · exact absurd (jumpApprox_le_haltingOracle h') hL
          · exact h'
        rw [hfalse, happrox]

/-! ## Running a machine for finitely many stages -/

/-- The value of the first stage `t < b` at which `F` converges, if there is one. -/
def scanOf (F : ℕ → Option ℕ) (b : ℕ) : Option ℕ :=
  b.rec (motive := fun _ => Option ℕ) none fun t ih => Option.casesOn ih (F t) fun y => some y

@[simp] theorem scanOf_zero (F : ℕ → Option ℕ) : scanOf F 0 = none := rfl

theorem scanOf_succ (F : ℕ → Option ℕ) (b : ℕ) :
    scanOf F (b + 1) = Option.casesOn (scanOf F b) (F b) fun y => some y := rfl

theorem scanOf_eq_none_iff (F : ℕ → Option ℕ) (b : ℕ) :
    scanOf F b = none ↔ ∀ t < b, F t = none := by
  induction b with
  | zero => simp
  | succ n ih =>
    rw [scanOf_succ]
    constructor
    · intro h t ht
      rcases hn : scanOf F n with - | y
      · rw [hn] at h
        simp only at h
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with hlt | rfl
        · exact (ih.1 hn) t hlt
        · exact h
      · rw [hn] at h
        exact absurd h (by simp)
    · intro h
      have hn : scanOf F n = none := ih.2 fun t ht => h t (Nat.lt_succ_of_lt ht)
      rw [hn]
      exact h n (Nat.lt_succ_self n)

/-- If `F` first converges at `t`, with value `v`, then every scan past `t` returns `v`. -/
theorem scanOf_eq_some {F : ℕ → Option ℕ} {t v b : ℕ} (hnone : ∀ u < t, F u = none)
    (ht : F t = some v) (hb : t < b) : scanOf F b = some v := by
  induction b with
  | zero => exact absurd hb (Nat.not_lt_zero t)
  | succ n ih =>
    rw [scanOf_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hlt | rfl
    · rw [ih hlt]
    · have hn : scanOf F t = none := (scanOf_eq_none_iff F t).2 hnone
      rw [hn]
      exact ht

end Oracle
end Lambda
