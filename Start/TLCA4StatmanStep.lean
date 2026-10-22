import Start.TLCA4PolyClosure
import Start.HeadReduction

/-!
# TLCA open problem 4 under βη: Statman's Corollary 0.1 (rows M20-TLCA4-STATMAN-STEP-ONE,
M20-TLCA4-POLYNOMIAL; series V, round 3, run 1)

Statman ("To Type a Mockingbird", 2011) splits his first step into Lemma 0.1 (a `B`,`M`,`I`-term
whose applicative instance has a head normal form with a free head variable is weakly
normalizing) and Corollary 0.1 (a weakly normal term is βη-equal to a polynomial).  This module
proves **Corollary 0.1** for the library's weak reduction, and reduces `StatmanStepOne` to Lemma 0.1
(for one argument) plus the fixed-point bridge, both stated as propositions:

* `WNF` — weak normality (`li t = none`: no leftmost-innermost weak redex);
* `wstep_of_li`, `weq_of_seq`, `isBMI_li`, `isBMI_seq` — the `li`-strategy is weak reduction and
  stays inside closed `B`,`M`,`I`-terms;
* **`isBMI_wnf_polyGen`** — a weakly normal closed `B`,`M`,`I`-term lies in the grammar `PolyGen`
  (it is `B`, `M`, `I`, `B U` or `B U V` with `U`, `V` weakly normal);
* **`wnf_betaEta_poly`** — Statman's Corollary 0.1: it is βη-equal to a polynomial;
* **`weaklyNormalizing_betaEta_poly`**, **`wn_betaEta_poly`** — the same for terms whose
  `li`-sequence terminates, and for terms with some weakly normal weak reduct (`WN`);
* `hd`, `HnfHead` — the free head variable of a λ-term, and "has a head normal form with free head
  `x`";
* `StatmanLemmaOne` (Lemma 0.1, one argument) and `FixHeadBridge` (A3) — stated here; proved in
  `Start/TLCA4StatmanProof.lean` (`statmanLemmaOne`) and `Start/TLCA4FixBridge.lean`
  (`fixHeadBridge`);
* `statmanStepOne_of_lemma_bridge` — together they give `StatmanStepOne`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm

/-- Weak normality: no weak redex (the leftmost-innermost strategy is stuck). -/
def WNF (t : Tm) : Prop := li t = none

theorem root_wstep {u v t' : Tm} (h : root u v = some t') : WStep (app u v) t' := by
  unfold root at h
  split at h
  · cases h; exact WStep.b _ _ _
  · cases h; exact WStep.m _
  · cases h; exact WStep.i _
  · cases h

/-- The leftmost-innermost step is a weak reduction step. -/
theorem wstep_of_li : ∀ {t t' : Tm}, li t = some t' → WStep t t'
  | app u v, t', h => by
      rw [li_app] at h
      rcases hu : li u with _ | u'
      · rw [hu] at h
        rcases hv : li v with _ | v'
        · rw [hv] at h; exact root_wstep h
        · rw [hv] at h; cases h; exact WStep.appR _ (wstep_of_li hv)
      · rw [hu] at h; cases h; exact WStep.appL _ (wstep_of_li hu)
  | B, _, h => by cases h
  | M, _, h => by cases h
  | I, _, h => by cases h
  | var _, _, h => by cases h

theorem weq_step (t : Tm) : WEq t (step t) := by
  unfold step
  rcases h : li t with _ | t'
  · exact WEq.refl _
  · exact WEq.step (wstep_of_li h)

/-- The `li`-sequence stays in the weak conversion class. -/
theorem weq_of_seq (t : Tm) : ∀ n, WEq t (seq t n)
  | 0 => WEq.refl _
  | n + 1 => by rw [seq_succ]; exact (weq_of_seq t n).trans (weq_step _)

theorem isBMI_root {u v t' : Tm} (hu : IsBMI u) (hv : IsBMI v) (h : root u v = some t') :
    IsBMI t' := by
  unfold root at h
  split at h
  · cases h
    cases hu with
    | app h1 hb => cases h1 with
      | app _ ha => exact .app ha (.app hb hv)
  · cases h; exact .app hv hv
  · cases h; exact hv
  · cases h

theorem isBMI_li : ∀ {t t' : Tm}, IsBMI t → li t = some t' → IsBMI t'
  | app u v, t', ht, h => by
      cases ht with
      | app hu hv =>
        rw [li_app] at h
        rcases hu' : li u with _ | u'
        · rw [hu'] at h
          rcases hv' : li v with _ | v'
          · rw [hv'] at h; exact isBMI_root hu hv h
          · rw [hv'] at h; cases h; exact .app hu (isBMI_li hv hv')
        · rw [hu'] at h; cases h; exact .app (isBMI_li hu hu') hv
  | B, _, _, h => by cases h
  | M, _, _, h => by cases h
  | I, _, _, h => by cases h
  | var _, _, _, h => by cases h

theorem isBMI_step {t : Tm} (ht : IsBMI t) : IsBMI (step t) := by
  unfold step
  rcases h : li t with _ | t'
  · exact ht
  · exact isBMI_li ht h

theorem isBMI_seq {t : Tm} (ht : IsBMI t) : ∀ n, IsBMI (seq t n)
  | 0 => ht
  | n + 1 => by rw [seq_succ]; exact isBMI_step (isBMI_seq ht n)

/-- **A weakly normal closed `B`,`M`,`I`-term is in `PolyGen`**: it is `B`, `M`, `I`, `B U` or
`B U V` with `U`, `V` weakly normal (`M U` and `I U` are redexes). -/
theorem isBMI_wnf_polyGen {t : Tm} (ht : IsBMI t) (hn : WNF t) : PolyGen t := by
  induction ht with
  | B => exact .B
  | M => exact .M
  | I => exact .I
  | @app u v hu hv ihu ihv =>
      unfold WNF at hn
      rw [li_app] at hn
      rcases hu' : li u with _ | u'
      · rw [hu'] at hn
        rcases hv' : li v with _ | v'
        · rw [hv'] at hn
          have pu := ihu hu'
          have pv := ihv hv'
          cases pu with
          | B => exact .B1 pv
          | M => simp [root] at hn
          | I => simp [root] at hn
          | B1 py => exact .B2 py pv
          | B2 _ _ => simp [root] at hn
          | I1 _ => simp only [li, root] at hu'; split at hu' <;> cases hu'
        · rw [hv'] at hn; cases hn
      · rw [hu'] at hn; cases hn

/-- **Statman's Corollary 0.1**: a weakly normal closed `B`,`M`,`I`-term is βη-equal to a
polynomial. -/
theorem wnf_betaEta_poly {t : Tm} (ht : IsBMI t) (hn : WNF t) :
    ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam t) (toLam (polyTm m ps)) :=
  polyGen_betaEta_poly (isBMI_wnf_polyGen ht hn)

/-- Corollary 0.1 for weakly normalizing terms. -/
theorem weaklyNormalizing_betaEta_poly {t : Tm} (ht : IsBMI t) (hn : ∃ n, WNF (seq t n)) :
    ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam t) (toLam (polyTm m ps)) := by
  obtain ⟨n, hn⟩ := hn
  obtain ⟨m, ps, h⟩ := wnf_betaEta_poly (isBMI_seq ht n) hn
  exact ⟨m, ps, (toLam_weq (weq_of_seq t n)).trans h⟩

/-- Weak normalizability: some weak reduct is weakly normal. -/
def WN (t : Tm) : Prop := ∃ N, Relation.ReflTransGen WStep t N ∧ WNF N

theorem isBMI_wstep {t t' : Tm} (h : WStep t t') (ht : IsBMI t) : IsBMI t' := by
  induction h with
  | b u v w =>
      cases ht with | app h1 hw => cases h1 with | app h2 hv => cases h2 with
        | app _ hu => exact .app hu (.app hv hw)
  | m u => cases ht with | app _ hu => exact .app hu hu
  | i u => cases ht with | app _ hu => exact hu
  | appL v _ ih => cases ht with | app hu hv => exact .app (ih hu) hv
  | appR u _ ih => cases ht with | app hu hv => exact .app hu (ih hv)

theorem weq_of_rtg {t N : Tm} (h : Relation.ReflTransGen WStep t N) : WEq t N := by
  induction h with
  | refl => exact WEq.refl _
  | tail _ hs ih => exact ih.trans (WEq.step hs)

theorem isBMI_of_rtg {t N : Tm} (h : Relation.ReflTransGen WStep t N) (ht : IsBMI t) : IsBMI N := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact isBMI_wstep hs ih

/-- Corollary 0.1 for weakly normalizable terms. -/
theorem wn_betaEta_poly {t : Tm} (ht : IsBMI t) (hn : WN t) :
    ∃ (m : Mono) (ps : List Mono), Lambda.betaEtaConv (toLam t) (toLam (polyTm m ps)) := by
  obtain ⟨N, hr, hN⟩ := hn
  obtain ⟨m, ps, h⟩ := wnf_betaEta_poly (isBMI_of_rtg hr ht) hN
  exact ⟨m, ps, (toLam_weq (weq_of_rtg hr)).trans h⟩

/-! ## Free head variables and the reduction of `StatmanStepOne` -/

/-- The free head variable of a λ-term (de Bruijn index relative to the outside), if any. -/
def hd : Lambda → Option ℕ
  | .var n => some n
  | .app f _ => hd f
  | .lam t => (hd t).bind fun n => if n = 0 then none else some (n - 1)

/-- `t` has a head normal form whose head is the free variable `x`. -/
def HnfHead (x : ℕ) (t : Lambda) : Prop :=
  ∃ u, Lambda.reduces t u ∧ Lambda.IsHnf u ∧ hd u = some x

/-- Statman's Lemma 0.1 for one argument: if `toLam (X x)` has a head normal form with free head
`x`, then `X` weakly reduces to a weakly normal term.  Proved as `statmanLemmaOne`. -/
def StatmanLemmaOne : Prop :=
  ∀ X : Tm, IsBMI X → HnfHead 0 (toLam (app X (var 0))) → WN X

/-- The fixed-point bridge (A3): a βη fixed-point combinator has a head normal form with head `x`.
Proved as `fixHeadBridge`. -/
def FixHeadBridge : Prop :=
  ∀ Y : Tm, IsBMI Y → Lambda.betaEtaConv (toLam (app Y (var 0)))
      (toLam (app (var 0) (app Y (var 0)))) → HnfHead 0 (toLam (app Y (var 0)))

/-- Lemma 0.1 and the bridge give Statman's first step, via Corollary 0.1. -/
theorem statmanStepOne_of_lemma_bridge (hL : StatmanLemmaOne) (hB : FixHeadBridge) :
    StatmanStepOne := fun Y hY hfix =>
  wn_betaEta_poly hY (hL Y hY (hB Y hY hfix))

end TLCA4
