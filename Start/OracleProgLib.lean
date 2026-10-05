/-
**Exact-state specifications for oracle tape programs, and the query gadget.**

The relativized counterpart of `Start/SpaceProgLib.lean`.  `Complexity.Space.OProg.ORunsQ` is the
specification of an oracle program by its observable state (`Complexity.Space.TState`) and the
contents of the query tape at both ends, with a bound on the cells used (work tape and query tape
together); `Complexity.Space.OProg.ORuns` is the case of an empty query tape at both ends, which is
how every compiled program is specified.

* `Complexity.Space.OProg.ORunsQ.lift` — **every specification of a plain program is a
  specification of its lift**, with the query tape untouched; so the whole combinator library of
  `Start/SpaceProgLib.lean` and `Start/SpaceProgTracks.lean` carries over;
* `ORunsQ.seq`, `.ite`, `.loop_stages`, `ORunsQ.qbit`, `ORunsQ.askT`, `ORunsQ.askF` — the rules;
* `Complexity.Space.OProg.opopBranch`, `.owhileNE` — the two track combinators whose bodies are
  oracle programs, with their specifications;
* `Complexity.Space.OProg.queryReg` — **the query gadget**: `R d := [true]` if `R a` belongs to
  the oracle and `R d := []` otherwise, writing `R a` on the query tape and asking.
-/

import Mathlib
import Start.OracleProg
import Start.SpaceProgTracks

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

open Complexity (Oracle Word)

/-- The observable state of an oracle configuration. -/
def OConfig.abs (c : OConfig) : TState := ⟨fun i => c.tape.getD i false, c.wHead, c.inHead⟩

/-- The plain configuration underneath an oracle configuration. -/
def OConfig.toC (c : OConfig) : Config := ⟨c.state, c.inHead, c.tape, c.wHead⟩

theorem OConfig.toC_withQ (c : OConfig) : c.toC.withQ c.qtape = c := rfl

theorem OConfig.abs_toC (c : OConfig) : c.toC.abs = c.abs := rfl

@[simp] theorem abs_withQ (c : Config) (q : List Bool) : (c.withQ q).abs = c.abs := rfl

theorem OConfig.space_toC_le (c : OConfig) : c.toC.space ≤ c.space := by
  simp only [OConfig.space, Config.space, OConfig.toC]; omega

theorem OConfig.qtape_le_space (c : OConfig) : c.qtape.length ≤ c.space := by
  simp only [OConfig.space]; omega

theorem oabs_otouch (x : List Bool) (c : OConfig) : (otouch x c).abs = c.abs := by
  exact abs_touch x c.toC

@[simp] theorem otouch_qtape (x : List Bool) (c : OConfig) : (otouch x c).qtape = c.qtape := rfl

namespace OProg

open Prog Tracks

/-! ### Specifications -/

/-- `ORunsQ A x B p s q s' q'`: from every configuration with observable state `s`, query tape `q`
and at most `B` cells, the program runs to a configuration with observable state `s'`, query tape
`q'` and at most `B` cells, every configuration on the way using at most `B` cells. -/
def ORunsQ (A : Oracle) (x : List Bool) (B : ℕ) (p : OProg) (s : TState) (q : List Bool)
    (s' : TState) (q' : List Bool) : Prop :=
  ∀ c : OConfig, c.abs = s → c.qtape = q → c.space ≤ B →
    ∃ d, OExec A x (fun c => c.space ≤ B) p c d ∧ d.abs = s' ∧ d.qtape = q' ∧ d.space ≤ B

/-- The specification with an empty query tape at both ends. -/
abbrev ORuns (A : Oracle) (x : List Bool) (B : ℕ) (p : OProg) (s s' : TState) : Prop :=
  ORunsQ A x B p s [] s' []

variable {A : Oracle} {x : List Bool} {B : ℕ}

theorem ORunsQ.seq {p p' : OProg} {s t u : TState} {q r w : List Bool}
    (h₁ : ORunsQ A x B p s q t r) (h₂ : ORunsQ A x B p' t r u w) :
    ORunsQ A x B (.seq p p') s q u w := by
  intro c hc hq hB
  obtain ⟨d, hd, hdt, hdq, hdB⟩ := h₁ c hc hq hB
  obtain ⟨e, he, heu, heq, heB⟩ := h₂ d hdt hdq hdB
  exact ⟨e, .seq hd he, heu, heq, heB⟩

theorem ORunsQ.of_eq {p : OProg} {s s' t t' : TState} {q r : List Bool}
    (h : ORunsQ A x B p s q t r) (hs : s' = s) (ht : t = t') : ORunsQ A x B p s' q t' r :=
  hs ▸ ht ▸ h

/-- **Lifting.**  A specification of a plain program is one of its lift, the query tape being
left alone. -/
theorem ORunsQ.lift {p : Prog} {s s' : TState} (q : List Bool) (h : Runs x B p s s') :
    ORunsQ A x B (lift p) s q s' q := by
  intro c hc hq hB
  subst hq
  have hqB : c.qtape.length ≤ B := le_trans c.qtape_le_space hB
  obtain ⟨d, hd, hds, hdB⟩ := h c.toC (by rw [OConfig.abs_toC, hc])
    (le_trans c.space_toC_le hB)
  refine ⟨d.withQ c.qtape, ?_, by rw [abs_withQ, hds], rfl, ?_⟩
  · have := oexec_lift (A := A) (Q := fun c => c.space ≤ B) (q := c.qtape)
      (fun d hd => by rw [space_withQ]; exact max_le hd hqB) hd
    rw [OConfig.toC_withQ] at this
    exact this
  · rw [space_withQ]; exact max_le hdB hqB

/-- Lifting with an empty query tape. -/
theorem ORuns.lift {p : Prog} {s s' : TState} (h : Runs x B p s s') :
    ORuns A x B (lift p) s s' := ORunsQ.lift [] h

theorem ORunsQ.iteT {t : Test} {p p' : OProg} {s s' : TState} {q q' : List Bool}
    (ht : t x[s.inHead]? (s.view s.head) = true) (hp : ORunsQ A x B p s q s' q') :
    ORunsQ A x B (.ite t p p') s q s' q' := by
  intro c hc hq hB
  subst hc
  obtain ⟨d, hd, hds, hdq, hdB⟩ := hp (otouch x c) (oabs_otouch x c) (by simpa using hq)
    (by rw [ospace_otouch]; exact hB)
  exact ⟨d, .iteT hB ht hd, hds, hdq, hdB⟩

theorem ORunsQ.iteF {t : Test} {p p' : OProg} {s s' : TState} {q q' : List Bool}
    (ht : t x[s.inHead]? (s.view s.head) = false) (hp : ORunsQ A x B p' s q s' q') :
    ORunsQ A x B (.ite t p p') s q s' q' := by
  intro c hc hq hB
  subst hc
  obtain ⟨d, hd, hds, hdq, hdB⟩ := hp (otouch x c) (oabs_otouch x c) (by simpa using hq)
    (by rw [ospace_otouch]; exact hB)
  exact ⟨d, .iteF hB ht hd, hds, hdq, hdB⟩

theorem ORunsQ.ite {t : Test} {p p' : OProg} {s s' : TState} {q q' : List Bool}
    (hp : t x[s.inHead]? (s.view s.head) = true → ORunsQ A x B p s q s' q')
    (hp' : t x[s.inHead]? (s.view s.head) = false → ORunsQ A x B p' s q s' q') :
    ORunsQ A x B (.ite t p p') s q s' q' := by
  cases ht : t x[s.inHead]? (s.view s.head)
  · exact ORunsQ.iteF ht (hp' ht)
  · exact ORunsQ.iteT ht (hp ht)

/-- **Loops through stages.** -/
theorem ORunsQ.loop_stages {t : Test} {body : OProg} (stage : ℕ → TState) (qs : ℕ → List Bool)
    (L : ℕ)
    (htest : ∀ k, k ≤ L →
      t x[(stage k).inHead]? ((stage k).view (stage k).head) = decide (k < L))
    (hbody : ∀ k, k < L → ORunsQ A x B body (stage k) (qs k) (stage (k + 1)) (qs (k + 1))) :
    ORunsQ A x B (.loop t body) (stage 0) (qs 0) (stage L) (qs L) := by
  suffices h : ∀ m k, k + m = L → ORunsQ A x B (.loop t body) (stage k) (qs k) (stage L) (qs L)
    from h L 0 (by omega)
  intro m
  induction m with
  | zero =>
      intro k hk c hc hq hB
      have ht : t (ordIn x c) (ordW c) = false := by
        have := htest k (by omega)
        rw [← hc] at this
        simp only [show ¬ k < L by omega, decide_false] at this
        exact this
      refine ⟨otouch x c, .loopF hB ht, ?_, ?_, by rw [ospace_otouch]; exact hB⟩
      · rw [oabs_otouch, hc, show k = L by omega]
      · rw [otouch_qtape, hq, show k = L by omega]
  | succ m ih =>
      intro k hk c hc hq hB
      have ht : t (ordIn x c) (ordW c) = true := by
        have := htest k (by omega)
        rw [← hc] at this
        simp only [show k < L by omega, decide_true] at this
        exact this
      obtain ⟨d, hd, hds, hdq, hdB⟩ :=
        hbody k (by omega) (otouch x c) (by rw [oabs_otouch, hc]) (by rw [otouch_qtape, hq])
          (by rw [ospace_otouch]; exact hB)
      obtain ⟨e, he, hes, heq, heB⟩ := ih (k + 1) (by omega) d hds hdq hdB
      exact ⟨e, .loopT hB ht hd he, hes, heq, heB⟩

/-- Appending the scanned bit to the query tape. -/
theorem ORunsQ.qbit (v : ℕ → Bool) (h i : ℕ) (q : List Bool) (hq : q.length + 1 ≤ B) :
    ORunsQ A x B .qbit ⟨v, h, i⟩ q ⟨v, h, i⟩ (q ++ [v h]) := by
  intro c hc hcq hB
  have hvh : ordW c = v h := by
    have h1 : c.abs.view c.abs.head = v h := by rw [hc]
    exact h1
  refine ⟨_, .qbit hB, ?_, ?_, ?_⟩
  · have := oabs_otouch x c
    rw [hc] at this
    rw [← this]
    rfl
  · simp only [oeff, hcq, hvh]
  · simp only [OConfig.space, oeff, writeAt_length, moveWork, List.length_append,
      List.length_singleton] at hB ⊢
    rw [hcq] at hB ⊢
    omega

/-- A query answered positively. -/
theorem ORunsQ.askT {p p' : OProg} {s s' : TState} {q q' : List Bool} (hA : A q = true)
    (hp : ORunsQ A x B p s [] s' q') : ORunsQ A x B (.ask p p') s q s' q' := by
  intro c hc hq hB
  obtain ⟨d, hd, hds, hdq, hdB⟩ := hp { c with qtape := [] } hc rfl
    (le_trans (by simp only [OConfig.space, List.length_nil]; omega) hB)
  exact ⟨d, .askT hB (by rw [hq]; exact hA) hd, hds, hdq, hdB⟩

/-- A query answered negatively. -/
theorem ORunsQ.askF {p p' : OProg} {s s' : TState} {q q' : List Bool} (hA : A q = false)
    (hp : ORunsQ A x B p' s [] s' q') : ORunsQ A x B (.ask p p') s q s' q' := by
  intro c hc hq hB
  obtain ⟨d, hd, hds, hdq, hdB⟩ := hp { c with qtape := [] } hc rfl
    (le_trans (by simp only [OConfig.space, List.length_nil]; omega) hB)
  exact ⟨d, .askF hB (by rw [hq]; exact hA) hd, hds, hdq, hdB⟩

/-! ### Track combinators with oracle bodies -/

/-- `popBranch` with oracle programs as branches. -/
def opopBranch (K j : ℕ) (p₀ p₁ : OProg) : OProg :=
  .seq (lift (seekEnd K j)) (.seq (lift (moveTo (wd K + (2 * j + 1)) (2 * j + 2)))
    (.ite (fun _ w => w) (.seq (lift (popTail K j)) p₁) (.seq (lift (popTail K j)) p₀)))

theorem oruns_popBranch (R : ℕ → List Bool) (j : ℕ) {K : ℕ} (hj : j < K) (hne : R j ≠ [])
    (N : ℕ) (hN : (R j).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) (p₀ p₁ : OProg)
    (s' : TState)
    (hp : ORuns A x B (if (R j).getLast hne then p₁ else p₀)
      ⟨lay K (Function.update R j (R j).dropLast), 0, i⟩ s') :
    ORuns A x B (opopBranch K j p₀ p₁) ⟨lay K R, 0, i⟩ s' := by
  have hl : 0 < (R j).length := List.length_pos_of_ne_nil hne
  obtain ⟨m, hm⟩ : ∃ m, (R j).length = m + 1 := ⟨(R j).length - 1, by omega⟩
  have hpos := blk_lt (k := m) (N := N) (o := 2 * j + 2) (by omega) (by womega) hB
  refine (ORuns.lift (runs_seekEnd _ j (R j).length (lay_pres R j hj) hj N (by omega) hB i)).seq ?_
  rw [hm]
  refine ORunsQ.seq (ORuns.lift ((runs_moveTo _ _ _ (m * wd K) i (by womega)).of_eq
    (by congr 1; ring) rfl)) ?_
  have hpop : Runs x B (popTail K j) ⟨lay K R, m * wd K + (2 * j + 2), i⟩
      ⟨lay K (Function.update R j (R j).dropLast), 0, i⟩ := by
    rw [lay_split K R j]
    refine (runs_wV _ _ _ _ j hj false i).seq ?_
    refine (runs_wmoveL _ _ i).seq ?_
    refine Runs.seq ((runs_wP _ _ _ m j hj false i).of_eq (by congr 1) rfl) ?_
    refine (runs_goHome _ _ _ _ i).of_eq rfl ?_
    rw [lay_update, ← presOf_dropLast, ← valOf_dropLast, hm, Nat.add_sub_cancel]
  have hv : lay K R (m * wd K + (2 * j + 2)) = (R j).getLast hne := by
    rw [lay_val R j hj, ← valOf_last _ hne, hm, Nat.add_sub_cancel]
  refine ORunsQ.ite (fun ht => ?_) (fun ht => ?_)
  · have h1 : (R j).getLast hne = true := by rw [← hv]; exact ht
    rw [h1, if_pos rfl] at hp
    exact (ORuns.lift hpop).seq hp
  · have h1 : (R j).getLast hne = false := by rw [← hv]; exact ht
    rw [h1] at hp
    exact (ORuns.lift hpop).seq hp

/-- `whileNE` with an oracle program as body. -/
def owhileNE (j : ℕ) (body : OProg) : OProg :=
  .seq (lift (mvR (2 * j + 1))) (.seq (.loop (fun _ w => w) (.seq (lift (mvL (2 * j + 1)))
    (.seq body (lift (mvR (2 * j + 1)))))) (lift (mvL (2 * j + 1))))

theorem oruns_whileNE (Rs : ℕ → ℕ → List Bool) (j L : ℕ) {K : ℕ} (hj : j < K) (body : OProg)
    (hne : ∀ k, k < L → Rs k j ≠ []) (hL : Rs L j = []) (hB : wd K < B) (i : ℕ)
    (hbody : ∀ k, k < L → ORuns A x B body ⟨lay K (Rs k), 0, i⟩ ⟨lay K (Rs (k + 1)), 0, i⟩) :
    ORuns A x B (owhileNE j body) ⟨lay K (Rs 0), 0, i⟩ ⟨lay K (Rs L), 0, i⟩ := by
  refine (ORuns.lift (runs_mvR _ _ 0 i (by womega))).seq ?_
  refine ORunsQ.seq ?_ (ORuns.lift ((runs_mvL (2 * j + 1) (lay K (Rs L)) (0 + (2 * j + 1)) i).of_eq
    rfl (by simp)))
  refine (ORunsQ.loop_stages (fun k => ⟨lay K (Rs k), 0 + (2 * j + 1), i⟩) (fun _ => []) L ?_ ?_)
  · intro k hk
    have := lay_pres (Rs k) j hj 0
    simp only [zero_mul] at this
    simp only [this]
    by_cases h : k < L
    · simp [h, List.length_pos_of_ne_nil (hne k h)]
    · simp [show k = L by omega, hL]
  · intro k hk
    refine (ORuns.lift (runs_mvL _ _ _ i)).seq ?_
    refine ORunsQ.seq ((hbody k hk).of_eq (by simp) rfl) ?_
    exact ORuns.lift (runs_mvR _ _ 0 i (by womega))

/-! ### The query gadget -/

/-- One block of the query loop: from the presence bit of track `a`, append its value bit to the
query tape and move to the presence bit of the next block. -/
def qBody (K : ℕ) : OProg := .seq (lift (wmove .right)) (.seq .qbit (lift (mvR (2 * K))))

/-- **The query gadget**: write `R a` on the query tape, ask, and set `R d := [true]` on a
positive answer and `R d := []` on a negative one. -/
def queryReg (K a d : ℕ) : OProg :=
  .seq (lift (mvR (2 * a + 1))) (.seq (.loop (fun _ w => w) (qBody K))
    (.seq (lift (goHome K (2 * a + 1))) (.seq (lift (clear K d))
      (.ask (lift (append K d true)) (lift skip)))))

theorem oruns_queryReg (R : ℕ → List Bool) (a d : ℕ) {K : ℕ} (ha : a < K) (hd : d < K)
    (N : ℕ) (hN1 : 1 ≤ N) (hNa : (R a).length ≤ N) (hNd : (R d).length ≤ N)
    (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    ORuns A x B (queryReg K a d) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (if A (R a) then [true] else [])), 0, i⟩ := by
  set L := (R a).length with hL
  have hpos0 := blk_lt (k := 0) (N := N) (o := 2 * a + 1) (by omega) (by womega) hB
  refine (ORuns.lift (runs_mvR _ _ 0 i (by womega))).seq ?_
  have hloop : ORunsQ A x B (.loop (fun _ w => w) (qBody K)) ⟨lay K R, 0 + (2 * a + 1), i⟩ []
      ⟨lay K R, L * wd K + (2 * a + 1), i⟩ (R a) := by
    have := ORunsQ.loop_stages (A := A) (x := x) (B := B) (t := fun _ w => w) (body := qBody K)
      (fun k => ⟨lay K R, k * wd K + (2 * a + 1), i⟩) (fun k => (R a).take k) L ?_ ?_
    · simpa [hL] using this
    · intro k hk
      simp only [lay_pres R a ha, hL]
    · intro k hk
      have hpos := blk_lt (k := k) (N := N) (o := 2 * a + 2) (by omega) (by womega) hB
      unfold qBody
      refine (ORunsQ.lift _ (runs_wmoveR _ _ i (by womega))).seq ?_
      have hval : lay K R (k * wd K + (2 * a + 1) + 1) = (R a)[k] := by
        rw [show k * wd K + (2 * a + 1) + 1 = k * wd K + (2 * a + 2) by ring, lay_val R a ha,
          valOf, List.getD_eq_getElem _ _ hk]
      have hkw : k ≤ k * wd K := Nat.le_mul_of_pos_right _ (by womega)
      refine ORunsQ.seq (ORunsQ.qbit _ _ i _ (by simp; omega)) ?_
      rw [hval, ← List.take_succ_eq_append_getElem hk]
      refine (ORunsQ.lift _ (runs_mvR _ _ _ i ?_)).of_eq rfl ?_
      · have := blk_lt (k := k) (N := N) (o := 2 * a + 1) (by omega) (by womega) hB
        womega
      · congr 1; simp only [wd]; ring
  refine ORunsQ.seq hloop ?_
  refine ORunsQ.seq
    (ORunsQ.lift _ ((runs_goHome (K := K) (x := x) (B := B) _ _ L (2 * a + 1) i))) ?_
  refine ORunsQ.seq (ORunsQ.lift _ (runs_clear R d hd N hNd hB i)) ?_
  cases hA : A (R a)
  · refine ORunsQ.askF hA ((ORuns.lift (runs_skip _ _ _)).of_eq rfl ?_)
    simp
  · refine ORunsQ.askT hA ((ORuns.lift (runs_append _ d hd true N (by simp; omega) hB i)).of_eq
      rfl ?_)
    simp

end OProg

end Complexity.Space
