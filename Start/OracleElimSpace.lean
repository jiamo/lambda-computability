/-
**Oracle Cobham terms compiled into plain tape programs, with the oracle replaced by a gadget.**

`Start/OracleCobSpace.lean` compiles an oracle Cobham term into an *oracle* tape program, whose
query is a write on the query tape and a question to the oracle.  This module compiles it into a
*plain* tape program instead: the query is a tape program `G a d fr` (a *gadget*) which sets
register `d` to the answer of the oracle on register `a`, using the scratch registers from `fr`
on.  If the oracle is decided in polynomial space by such a gadget, every oracle Cobham term is
then evaluated in polynomial space without an oracle; this is how a `PSPACE` oracle is removed.

* `Complexity.Space.Elim.compileT` — the compiler, with the gadget `G` for the query;
* `Complexity.Space.Elim.GadgetOK` — the specification of a gadget for the oracle `A`, with `q`
  scratch registers, within `(T N + 3) · (2K + 1)` cells on registers of length at most `N`;
* **`Complexity.Space.Elim.compileTOK`** — the compiled program of `c` sets its destination
  register to `CobQ.eval A c`, within `(T (CobQ.spaceW c N) + 3) · (2K + 1)` cells, for every
  monotone `T` above the identity.

The proofs are those of `Start/OracleCobSpace.lean`, with plain programs.
-/

import Mathlib
import Start.OracleCobSpace

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Complexity.Space

namespace Elim

open Prog Tracks

mutual
/-- **The compiler**: `compileT K G c as d fr` sets register `d` to the value of the oracle Cobham
term `c` on the registers `as`, the query being the gadget `G`, using the scratch registers from
`fr` on. -/
def compileT (K : ℕ) (G : ℕ → ℕ → ℕ → Prog) : CobQ → List ℕ → ℕ → ℕ → Prog
  | .proj i, as, d, fr => compile K (.proj i) as d fr
  | .empty, as, d, fr => compile K .empty as d fr
  | .app b, as, d, fr => compile K (.app b) as d fr
  | .smash, as, d, fr => compile K .smash as d fr
  | .query, as, d, fr =>
      match as[0]? with
      | some a => G a d fr
      | none => .seq (clear K d) (G d d fr)
  | .comp f gs, as, d, fr =>
      .seq (compilesT K G gs as fr (fr + gs.length))
        (.seq (compileT K G f (List.range' fr gs.length) d (fr + gs.length))
          (clearFrom K fr gs.length))
  | .bRec g h₀ h₁ bd, as, d, fr =>
      .seq (match as[0]? with
        | some a => assign K a fr
        | none => skip)
      (.seq (compileT K G g as.tail (fr + 2) (fr + 6))
      (.seq (whileNE fr (popBranch K fr
          (brStep K fr (compileT K G h₀ ((fr + 1) :: (fr + 2) :: as.tail) (fr + 3) (fr + 6))
            (compileT K G bd ((fr + 1) :: as.tail) (fr + 4) (fr + 6)) false)
          (brStep K fr (compileT K G h₁ ((fr + 1) :: (fr + 2) :: as.tail) (fr + 3) (fr + 6))
            (compileT K G bd ((fr + 1) :: as.tail) (fr + 4) (fr + 6)) true)))
      (.seq (assign K (fr + 2) d) (.seq (clear K (fr + 1)) (clear K (fr + 2))))))
/-- Compile the terms `gs` into the consecutive registers from `t` on. -/
def compilesT (K : ℕ) (G : ℕ → ℕ → ℕ → Prog) : List CobQ → List ℕ → ℕ → ℕ → Prog
  | [], _, _, _ => skip
  | g :: gs, as, t, fr => .seq (compileT K G g as t fr) (compilesT K G gs as (t + 1) fr)
end

/-- The specification of a gadget for the oracle `A`: on registers of length at most `N`, with
the scratch registers from `fr` on empty, it sets register `d` to the answer of `A` on register
`a` (possibly `a = d`), within `(T N + 3) · (2K + 1)` cells. -/
def GadgetOK (A : Oracle) (G : ℕ → ℕ → ℕ → Prog) (q : ℕ) (T : ℕ → ℕ) (K : ℕ) (x : List Bool)
    (B : ℕ) : Prop :=
  ∀ (a d fr : ℕ) (R : ℕ → List Bool) (N i : ℕ), a < fr → d < fr → fr + q ≤ K →
    (∀ r, fr ≤ r → R r = []) → (∀ r, (R r).length ≤ N) → (T N + 3) * wd K ≤ B →
    Runs x B (G a d fr) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (if A (R a) then [true] else [])), 0, i⟩

/-- The specification of the compiled program of an oracle term `c`. -/
def CompileTOK (A : Oracle) (G : ℕ → ℕ → ℕ → Prog) (q : ℕ) (T : ℕ → ℕ) (K : ℕ)
    (x : List Bool) (B : ℕ) (c : CobQ) : Prop :=
  ∀ (as : List ℕ) (d fr : ℕ) (R : ℕ → List Bool) (N i : ℕ),
    (∀ a ∈ as, a < fr) → d < fr → d ∉ as → fr + c.need + q ≤ K →
    (∀ r, fr ≤ r → R r = []) → (∀ r, (R r).length ≤ N) → (T (c.spaceW N) + 3) * wd K ≤ B →
    Runs x B (compileT K G c as d fr) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (CobQ.eval A c (as.map R))), 0, i⟩

section Compile

variable {A : Oracle} {G : ℕ → ℕ → ℕ → Prog} {q : ℕ} {T : ℕ → ℕ} {K : ℕ} {x : List Bool}
  {B : ℕ} (hTm : Monotone T) (hTid : ∀ n, n ≤ T n)

include hTm hTid

theorem bT {m n : ℕ} (hmn : m ≤ n) (hB : (T n + 3) * wd K ≤ B) : (m + 3) * wd K ≤ B :=
  le_trans (Nat.mul_le_mul_right _ (by have := hTid n; omega)) hB

theorem bTT {m n : ℕ} (hmn : m ≤ n) (hB : (T n + 3) * wd K ≤ B) : (T m + 3) * wd K ≤ B :=
  le_trans (Nat.mul_le_mul_right _ (by have := hTm hmn; omega)) hB

/-! #### The oracle-free constructors, from the unrelativized compiler -/

theorem compileTOK_lift (c : Cob) (c' : CobQ) (hc : ∀ args, CobQ.eval A c' args = c.eval args)
    (hsp : ∀ N, c'.spaceW N = c.spaceW N) (hn : c'.need = c.need)
    (hprog : ∀ as d fr, compileT K G c' as d fr = compile K c as d fr) :
    CompileTOK A G q T K x B c' := by
  intro as d fr R N i has hd hne hK hfr hN hB
  rw [hprog, hc]
  exact compileOK (K := K) (x := x) (B := B) c as d fr R N i has hd hne
    (by rw [← hn]; omega) hfr hN (by rw [← hsp]; exact bT hTm hTid le_rfl hB)

theorem compileTOK_proj (i : ℕ) : CompileTOK A G q T K x B (.proj i) :=
  compileTOK_lift hTm hTid (.proj i) _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

theorem compileTOK_empty : CompileTOK A G q T K x B .empty :=
  compileTOK_lift hTm hTid .empty _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

theorem compileTOK_app (b : Bool) : CompileTOK A G q T K x B (.app b) :=
  compileTOK_lift hTm hTid (.app b) _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

theorem compileTOK_smash : CompileTOK A G q T K x B .smash :=
  compileTOK_lift hTm hTid .smash _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

/-! #### The query -/

theorem compileTOK_query (hG : GadgetOK A G q T K x B) : CompileTOK A G q T K x B .query := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [CobQ.spaceW] at hB
  simp only [CobQ.need] at hK
  simp only [compileT, CobQ.eval_query, getD_map_eq]
  cases h0 : as[0]? with
  | none =>
      dsimp only
      refine (runs_clear R d (by omega) (N + 1) (by have := hN d; omega)
        (bT hTm hTid le_rfl hB) i).seq ?_
      have := hG d d fr (Function.update R d []) (N + 1) i hd hd (by omega)
        (fun r hr => by rw [Function.update_of_ne (by omega)]; exact hfr r hr)
        (fun r => by rw [Function.update_apply]; split_ifs
                     · simp
                     · have := hN r; omega) hB
      rw [Function.update_self, Function.update_idem] at this
      exact this
  | some a =>
      dsimp only
      have ha : a ∈ as := List.mem_of_getElem? h0
      exact hG a d fr R (N + 1) i (has a ha) hd (by omega) hfr (fun r => by have := hN r; omega)
        hB

theorem runs_compiles (gs : List CobQ) (hgs : ∀ g ∈ gs, CompileTOK A G q T K x B g) (as : List ℕ)
    (fr' : ℕ) (hK : fr' + CobQ.needs gs + q ≤ K) (N N' : ℕ) (i : ℕ) :
    ∀ (t : ℕ) (R : ℕ → List Bool), (∀ a ∈ as, a < t) → t + gs.length ≤ fr' →
    (∀ r, t ≤ r → R r = []) → (∀ a ∈ as, (R a).length ≤ N) → (∀ r, (R r).length ≤ N') →
    (∀ g ∈ gs, g.spaceW N ≤ N' ∧ (T (g.spaceW N') + 3) * wd K ≤ B) →
    Runs x B (compilesT K G gs as t fr') ⟨lay K R, 0, i⟩
      ⟨lay K (setFrom R t (gs.map fun g => CobQ.eval A g (as.map R))), 0, i⟩ := by
  induction gs with
  | nil =>
      intro t R _ _ _ _ _ _
      simp only [compilesT, List.map_nil, setFrom_nil]
      exact runs_skip _ 0 i
  | cons g gs ih =>
      intro t R has ht hfr hNa hN hsp
      simp only [CobQ.needs] at hK
      simp only [List.length_cons] at ht
      have hmap : as.map (Function.update R t (CobQ.eval A g (as.map R))) = as.map R :=
        List.map_congr_left (fun a ha => Function.update_of_ne (by have := has a ha; omega) _ _)
      simp only [compilesT]
      refine ((hgs g (by simp)) as t fr' R N' i (fun a ha => by have := has a ha; omega)
        (by omega) (fun h => by have := has t h; omega) (by omega)
        (fun r hr => hfr r (by omega)) hN (hsp g (by simp)).2).seq ?_
      have := ih (fun g' hg' => hgs g' (by simp [hg'])) (by omega) (t + 1)
        (Function.update R t (CobQ.eval A g (as.map R))) (fun a ha => by have := has a ha; omega)
        (by omega)
        (fun r hr => by rw [Function.update_of_ne (by omega)]; exact hfr r (by omega))
        (fun a ha => by rw [Function.update_of_ne (by have := has a ha; omega)]; exact hNa a ha)
        (fun r => by
          rw [Function.update_apply]; split_ifs
          · exact le_trans (CobQ.eval_length_le A g _ N (fun w hw => by
              obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hw; exact hNa a ha)) (hsp g (by simp)).1
          · exact hN r)
        (fun g' hg' => hsp g' (by simp [hg']))
      rw [hmap, setFrom_cons] at this
      simpa only [List.map_cons] using this

theorem compileTOK_comp (f : CobQ) (gs : List CobQ) (hf : CompileTOK A G q T K x B f)
    (hgs : ∀ g ∈ gs, CompileTOK A G q T K x B g) : CompileTOK A G q T K x B (.comp f gs) := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [CobQ.need] at hK
  simp only [CobQ.spaceW] at hB
  simp only [compileT, CobQ.eval_comp]
  obtain ⟨M, hM⟩ : ∃ M, M = N + CobQ.spaceWs gs N := ⟨_, rfl⟩
  rw [← hM] at hB
  have hfM := CobQ.le_spaceW f M
  have hBM : (M + 3) * wd K ≤ B := bT hTm hTid (by omega) hB
  set ws := gs.map fun g => CobQ.eval A g (as.map R) with hws
  have hwsl : ws.length = gs.length := by simp [ws]
  have hlen2 : ∀ r, (setFrom R fr ws r).length ≤ M := by
    intro r; simp only [setFrom]; split_ifs with h
    · rw [List.getD_eq_getElem?_getD]
      cases hw : ws[r - fr]? with
      | none => simp
      | some w =>
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hw)
          have := CobQ.eval_length_le A g (as.map R) N (fun w hw => by
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a)
          have := CobQ.spaceWs_le gs N g hg
          simp only [Option.getD_some]; omega
    · have := hN r; omega
  refine (runs_compiles hTm hTid gs hgs as (fr + gs.length) (by omega) N M i fr R has (by omega) hfr
    (fun a _ => hN a) (fun r => by have := hN r; omega) (fun g hg => ⟨?_, ?_⟩)).seq ?_
  · have := CobQ.spaceWs_le gs N g hg; omega
  · have h1 := CobQ.spaceWs_le gs M g hg
    exact bTT hTm hTid (by omega) hB
  refine Runs.seq (hf (List.range' fr gs.length) d (fr + gs.length) (setFrom R fr ws) M i
    (fun a ha => by rw [List.mem_range'_1] at ha; omega) (by omega)
    (fun h => by rw [List.mem_range'_1] at h; omega) (by omega)
    (fun r hr => by simp only [setFrom]; rw [ite_eq_right (by omega)]; exact hfr r (by omega))
    hlen2 (bTT hTm hTid (by omega) hB)) ?_
  rw [show List.range' fr gs.length = List.range' fr ws.length by rw [hwsl],
    map_range'_setFrom]
  have hwsM : ∀ w ∈ ws, w.length ≤ M := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
    have := CobQ.eval_length_le A g (as.map R) N (fun w hw => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a)
    have := CobQ.spaceWs_le gs N g hg
    omega
  refine (runs_clearFrom gs.length (Function.update (setFrom R fr ws) d (CobQ.eval A f ws)) fr
    (by omega)
    (f.spaceW M) (fun r => by
    rw [Function.update_apply]; split_ifs
    · exact CobQ.eval_length_le A f ws M hwsM
    · have := hlen2 r; omega) (bT hTm hTid (by omega) hB) i).of_eq rfl ?_
  congr 2; funext r
  simp only [Function.update_apply, setFrom, hwsl]
  split_ifs <;> first | rfl | omega | (symm; exact hfr r (by omega))

theorem runs_brStepT (h bd : CobQ) (hh : CompileTOK A G q T K x B h) (hbd : CompileTOK A G q T K x B bd)
    (as' : List ℕ) (fr : ℕ) (β : Bool) (R : ℕ → List Bool) (M M' : ℕ) (i : ℕ)
    (has : ∀ a ∈ as', a < fr) (hKh : fr + 6 + h.need + q ≤ K) (hKb : fr + 6 + bd.need + q ≤ K)
    (hfr : ∀ r, fr + 3 ≤ r → R r = []) (hN : ∀ r, (R r).length ≤ M)
    (hS : (R (fr + 1)).length + 1 ≤ M') (hMM' : M ≤ M') (hhM : h.spaceW M ≤ M')
    (hB1 : (T (h.spaceW M) + 3) * wd K ≤ B) (hB2 : (T (bd.spaceW M') + 3) * wd K ≤ B) :
    Runs x B (brStep K fr (compileT K G h ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6))
      (compileT K G bd ((fr + 1) :: as') (fr + 4) (fr + 6)) β) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update (Function.update R (fr + 1) (β :: R (fr + 1))) (fr + 2)
        ((CobQ.eval A h (R (fr + 1) :: R (fr + 2) :: as'.map R)).take
          (CobQ.eval A bd ((β :: R (fr + 1)) :: as'.map R)).length)), 0, i⟩ := by
  have hM'b := CobQ.le_spaceW bd M'
  have hB3 : (M' + 3) * wd K ≤ B := bT hTm hTid (by omega) hB2
  have hB2p : (bd.spaceW M' + 3) * wd K ≤ B := bT hTm hTid le_rfl hB2
  have hmap : ∀ (R' : ℕ → List Bool), (∀ a ∈ as', R' a = R a) → as'.map R' = as'.map R :=
    fun R' hR' => List.map_congr_left hR'
  set W := CobQ.eval A h (R (fr + 1) :: R (fr + 2) :: as'.map R) with hW
  have hWl : W.length ≤ M' := le_trans (CobQ.eval_length_le A h _ M (fun w hw => by
    simp only [List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | rfl | ⟨a, -, rfl⟩ <;> exact hN _)) hhM
  -- step 1
  have h1 := hh ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6) R M i
    (fun a ha => by simp only [List.mem_cons] at ha; rcases ha with rfl | rfl | ha <;>
      first | omega | (have := has _ ha; omega))
    (by omega) (fun ha => by simp only [List.mem_cons] at ha; rcases ha with h | h | ha <;>
      first | omega | (have := has _ ha; omega))
    (by omega) (fun r hr => hfr r (by omega)) hN hB1
  simp only [List.map_cons] at h1
  rw [← hW] at h1
  unfold brStep
  refine h1.seq ?_
  -- step 2
  set R1 := Function.update R (fr + 3) W with hR1
  have h2 := runs_prepend (x := x) (B := B) R1 (fr + 1) (fr + 5) (by omega) (by omega)
    (by omega)
    (by simp [R1, hfr (fr + 5) (by omega)]) β M'
    (by simp only [R1, Function.update_of_ne (show fr + 1 ≠ fr + 3 by omega)]; exact hS) hB3 i
  refine h2.seq ?_
  -- step 3
  set R2 := Function.update R1 (fr + 1) (β :: R1 (fr + 1)) with hR2
  have hR1N : ∀ r, (R1 r).length ≤ M' := by
    intro r; simp only [R1, Function.update_apply]; split_ifs
    · exact hWl
    · have := hN r; omega
  have hR2N : ∀ r, (R2 r).length ≤ M' := by
    intro r; simp only [R2, Function.update_apply]; split_ifs with hr
    · subst hr
      simp only [R1, Function.update_of_ne (show fr + 1 ≠ fr + 3 by omega), List.length_cons]
      exact hS
    · exact hR1N r
  have h3 := hbd ((fr + 1) :: as') (fr + 4) (fr + 6) R2 M' i
    (fun a ha => by simp only [List.mem_cons] at ha; rcases ha with rfl | ha <;>
      [omega; (have := has a ha; omega)])
    (by omega) (fun ha => by simp only [List.mem_cons] at ha; rcases ha with h | ha <;>
      [omega; (have := has _ ha; omega)])
    (by omega) (fun r hr => by
      simp only [R2, R1, Function.update_apply]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      exact hfr r (by omega)) hR2N hB2
  have hR2a : as'.map R2 = as'.map R := hmap R2 (fun a ha => by
    have := has a ha
    simp only [R2, R1, Function.update_apply]; rw [ite_eq_right (by omega), ite_eq_right (by omega)])
  have hR21 : R2 (fr + 1) = β :: R (fr + 1) := by
    simp [R2, R1]
  simp only [List.map_cons, hR2a, hR21] at h3
  refine h3.seq ?_
  -- step 4
  set T := CobQ.eval A bd ((β :: R (fr + 1)) :: as'.map R) with hT
  have hTl : T.length ≤ bd.spaceW M' := CobQ.eval_length_le A bd _ M' (fun w hw => by
    simp only [List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨a, -, rfl⟩
    · simp only [List.length_cons]; have := hR21 ▸ hR2N (fr + 1); simpa using this
    · have := hN a; omega)
  set R3 := Function.update R2 (fr + 4) T with hR3
  have hR3N : ∀ r, (R3 r).length ≤ bd.spaceW M' := by
    intro r; simp only [R3, Function.update_apply]
    split_ifs
    · exact hTl
    · have := hR2N r; omega
  have hR33 : R3 (fr + 3) = W := by simp [R3, R2, R1]
  have hR34 : R3 (fr + 4) = T := by simp [R3]
  have h4 := runs_truncate (x := x) (B := B) R3 (fr + 3) (fr + 4) (by omega) (by omega)
    (by omega)
    _ (hR3N _) hB2p i
  rw [hR33, hR34] at h4
  refine h4.seq ?_
  -- step 5
  set R4 := Function.update R3 (fr + 3) (W.take T.length) with hR4
  have hR4N : ∀ r, (R4 r).length ≤ bd.spaceW M' := by
    intro r; simp only [R4, Function.update_apply]
    split_ifs
    · simp only [List.length_take]; have := hR3N (fr + 3); rw [hR33] at this; omega
    · exact hR3N r
  have h5 := runs_assign (x := x) (B := B) R4 (fr + 3) (fr + 2) (by omega) (by omega)
    (by omega)
    _ (hR4N _) (hR4N _) hB2p i
  refine h5.seq ?_
  -- steps 6, 7
  set R5 := Function.update R4 (fr + 2) (R4 (fr + 3)) with hR5
  have hR5N : ∀ r, (R5 r).length ≤ bd.spaceW M' := by
    intro r; simp only [R5, Function.update_apply]
    split_ifs
    · exact hR4N _
    · exact hR4N r
  refine (runs_clear R5 (fr + 3) (by omega) _ (hR5N _) hB2p i).seq ?_
  refine (runs_clear (Function.update R5 (fr + 3) []) (fr + 4) (by omega) _ (by
    rw [Function.update_apply]; split_ifs
    · simp
    · exact hR5N _) hB2p i).of_eq rfl ?_
  congr 2; funext r
  simp only [R5, R4, R3, R2, R1, Function.update_apply]
  split_ifs <;> first | rfl | omega | (subst_vars; simp_all)

theorem compileTOK_bRec (g h₀ h₁ bd : CobQ) (hg : CompileTOK A G q T K x B g)
    (hh₀ : CompileTOK A G q T K x B h₀)
    (hh₁ : CompileTOK A G q T K x B h₁) (hbd : CompileTOK A G q T K x B bd) :
    CompileTOK A G q T K x B (.bRec g h₀ h₁ bd) := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [CobQ.need] at hK
  simp only [CobQ.spaceW] at hB
  obtain ⟨M, hM⟩ : ∃ M, M = N + g.spaceW N + bd.spaceW N := ⟨_, rfl⟩
  rw [← hM] at hB
  obtain ⟨M', hM'⟩ : ∃ M', M' = M + h₀.spaceW M + h₁.spaceW M := ⟨_, rfl⟩
  rw [← hM'] at hB
  have hbM' := CobQ.le_spaceW bd M'
  have hgN := CobQ.le_spaceW g N
  have hB3 : (M + 3) * wd K ≤ B := bT hTm hTid (by omega) hB
  rw [CobQ.eval_bRec_headD]
  set as' := as.tail with has'
  have has'f : ∀ a ∈ as', a < fr := fun a ha => has a (List.mem_of_mem_tail ha)
  have hrest : (as.map R).tail = as'.map R := by cases as <;> rfl
  rw [hrest]
  set X := (as.map R).headD [] with hX
  set rest := as'.map R with hrestd
  have hXN : X.length ≤ N := by
    cases as with
    | nil => simp [X]
    | cons a t => simpa [X] using hN a
  have hfirst : Runs x B (match as[0]? with
      | some a => assign K a fr
      | none => skip) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R fr X), 0, i⟩ := by
    cases as with
    | nil =>
        refine (runs_skip _ 0 i).of_eq rfl ?_
        congr 2; simp only [X, List.map_nil, List.headD_nil]
        rw [← hfr fr le_rfl, Function.update_eq_self]
    | cons a t =>
        have ha := has a (by simp)
        exact runs_assign R a fr (by omega) (by omega) (by omega) N (hN a) (hN fr) (by
          exact le_trans (Nat.mul_le_mul_right _ (by omega)) hB3) i
  simp only [compileT]
  refine hfirst.seq ?_
  obtain ⟨L, hL⟩ : ∃ L, L = X.length := ⟨_, rfl⟩
  let V : ℕ → List Bool := fun k => CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (X.drop (L - k) :: rest)
  let Rs : ℕ → ℕ → List Bool := fun k =>
    Function.update (Function.update (Function.update R fr (X.take (L - k))) (fr + 1)
      (X.drop (L - k))) (fr + 2) (V k)
  have hrestN : ∀ w ∈ rest, w.length ≤ N := fun w hw => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a
  have hVN : ∀ k, (V k).length ≤ g.spaceW N + bd.spaceW N := fun k =>
    CobQ.bRec_length_le A g h₀ h₁ bd rest N (CobQ.eval_length_le A g rest N hrestN)
      (fun y hy => CobQ.eval_length_le A bd _ N (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hy
        · exact hrestN w hw)) _ (by simp only [List.length_drop]; omega)
  have hRsN : ∀ k r, (Rs k r).length ≤ M := by
    intro k r; simp only [Rs, Function.update_apply]
    split_ifs
    · have := hVN k; omega
    · simp only [List.length_drop]; omega
    · simp only [List.length_take]; omega
    · have := hN r; omega
  have hmapR : ∀ R' : ℕ → List Bool, (∀ r, r < fr → R' r = R r) → as'.map R' = rest :=
    fun R' hR' => List.map_congr_left (fun a ha => hR' a (has'f a ha))
  -- the base value
  have hg' := hg as' (fr + 2) (fr + 6) (Function.update R fr X) N i
    (fun a ha => by have := has'f a ha; omega) (by omega)
    (fun h => by have := has'f _ h; omega) (by omega)
    (fun r hr => by rw [Function.update_of_ne (by omega)]; exact hfr r (by omega))
    (fun r => by rw [Function.update_apply]; split_ifs
                 · exact hXN
                 · exact hN r)
    (bTT hTm hTid (by omega) hB)
  rw [hmapR _ (fun r hr => Function.update_of_ne (by omega) _ _)] at hg'
  refine Runs.seq (t := ⟨lay K (Rs 0), 0, i⟩) (hg'.of_eq rfl ?_) ?_
  · congr 2; funext r
    simp only [Rs, V, Function.update_apply, Nat.sub_zero, hL, List.take_length,
      List.drop_length, CobQ.eval_bRec_nil]
    split_ifs <;> first | rfl | omega | exact hfr r (by omega)
  refine Runs.seq (t := ⟨lay K (Rs L), 0, i⟩) ?_ ?_
  swap
  · have hRsL2 : Rs L (fr + 2) = CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (X :: rest) := by
      simp [Rs, V]
    refine (runs_assign (Rs L) (fr + 2) d (by omega) (by omega) (by omega) M (hRsN _ _)
      (hRsN _ _) hB3 i).seq ?_
    rw [hRsL2]
    have hU : ∀ r,
        (Function.update (Rs L) d (CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (X :: rest)) r).length
        ≤ M := by
      intro r; rw [Function.update_apply]; split_ifs
      · rw [← hRsL2]; exact hRsN _ _
      · exact hRsN _ _
    refine (runs_clear _ (fr + 1) (by omega) M (hU _) hB3 i).seq ?_
    refine (runs_clear _ (fr + 2) (by omega) M (by
      rw [Function.update_apply]; split_ifs
      · simp
      · exact hU _) hB3 i).of_eq rfl ?_
    congr 2; funext r
    simp only [Rs, Function.update_apply, Nat.sub_self, List.take_zero]
    split_ifs <;> first | rfl | omega | exact (hfr r (by omega)).symm
  have hBw : wd K < B := by nlinarith
  have hRsfr : ∀ k, Rs k fr = X.take (L - k) := fun k => by simp [Rs]
  refine runs_whileNE Rs fr L (by omega) _ (fun k hk => ?_) ?_ hBw i (fun k hk => ?_)
  · rw [hRsfr]; intro h; have := congrArg List.length h
    rw [List.length_take, ← hL, List.length_nil] at this; omega
  · rw [hRsfr, Nat.sub_self, List.take_zero]
  have hne' : Rs k fr ≠ [] := by
    rw [hRsfr]; intro h; have := congrArg List.length h
    rw [List.length_take, ← hL, List.length_nil] at this; omega
  refine runs_popBranch (Rs k) fr (by omega) hne' M (hRsN k fr) hB3 i _ _ _ ?_
  have hlast : (Rs k fr).getLast hne' = X[L - k - 1]'(by omega) := by
    have : ∀ (l : List Bool) (h : l ≠ []), l = X.take (L - k) →
        l.getLast h = X[L - k - 1]'(by omega) := by
      intro l h hl; subst hl; exact take_getLast_eq X (L - k) (by omega) (by omega) h
    exact this _ _ (hRsfr k)
  set R' := Function.update (Rs k) fr (Rs k fr).dropLast with hR'
  have hR'1 : R' (fr + 1) = X.drop (L - k) := by simp [R', Rs]
  have hR'2 : R' (fr + 2) = V k := by simp [R', Rs]
  have hR'a : as'.map R' = rest := hmapR R' (fun r hr => by
    simp only [R', Rs, Function.update_apply]; rw [ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)])
  have hR'fr : ∀ r, fr + 3 ≤ r → R' r = [] := fun r hr => by
    simp only [R', Rs, Function.update_apply]; rw [ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]; exact hfr r (by omega)
  have hR'N : ∀ r, (R' r).length ≤ M := fun r => by
    simp only [R', Function.update_apply]; split_ifs
    · simp only [List.length_dropLast]; have := hRsN k fr; omega
    · exact hRsN k r
  have key : ∀ (β : Bool) (h : CobQ), CompileTOK A G q T K x B h → fr + 6 + h.need + q ≤ K →
      h.spaceW M ≤ M' → X[L - k - 1]'(by omega) = β →
      (∀ ys, CobQ.eval A (CobQ.bRec g h₀ h₁ bd) ((β :: ys) :: rest) =
        (CobQ.eval A h (ys :: CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (ys :: rest) :: rest)).take
          (CobQ.eval A bd ((β :: ys) :: rest)).length) →
      Runs x B (brStep K fr (compileT K G h ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6))
        (compileT K G bd ((fr + 1) :: as') (fr + 4) (fr + 6)) β) ⟨lay K R', 0, i⟩
        ⟨lay K (Rs (k + 1)), 0, i⟩ := by
    intro β h hh hKh hhM hβ hrec
    have := runs_brStepT hTm hTid h bd hh hbd as' fr β R' M M' i has'f hKh (by omega) hR'fr hR'N
      (by rw [hR'1, List.length_drop]; omega) (by omega) hhM
      (bTT hTm hTid (by omega) hB)
      (bTT hTm hTid (by omega) hB)
    rw [hR'1, hR'2, hR'a] at this
    refine this.of_eq rfl ?_
    have hdrop : X.drop (L - (k + 1)) = β :: X.drop (L - k) := by
      rw [List.drop_eq_getElem_cons (by omega), show L - (k + 1) + 1 = L - k by omega]
      congr 1
    have hV : V (k + 1) = (CobQ.eval A h (X.drop (L - k) :: V k :: rest)).take
        (CobQ.eval A bd ((β :: X.drop (L - k)) :: rest)).length := by
      simp only [V]; rw [hdrop, hrec]
    have hR'eq : R' = Function.update (Rs k) fr (X.take (L - (k + 1))) := by
      simp only [R', hRsfr, dropLast_take_eq _ _ (show L - k ≤ X.length by omega), Nat.sub_sub]
    rw [hR'eq]
    congr 2; funext r
    simp only [Rs, Function.update_apply]
    split_ifs <;> first | rfl | omega | exact hV.symm | exact hdrop.symm
  rw [hlast]
  cases hβ : X[L - k - 1]'(by omega)
  · simp only [Bool.false_eq_true, ite_false]
    exact key false h₀ hh₀ (by omega) (by omega) hβ (fun ys => by simp [CobQ.eval_bRec_cons])
  · simp only [ite_true]
    exact key true h₁ hh₁ (by omega) (by omega) hβ (fun ys => by simp [CobQ.eval_bRec_cons])


mutual
/-- **Compiler correctness**, for every oracle Cobham term, given a gadget for the oracle. -/
theorem compileTOK (hG : GadgetOK A G q T K x B) : ∀ c : CobQ, CompileTOK A G q T K x B c
  | .proj i => compileTOK_proj hTm hTid i
  | .empty => compileTOK_empty hTm hTid
  | .app b => compileTOK_app hTm hTid b
  | .smash => compileTOK_smash hTm hTid
  | .query => compileTOK_query hTm hTid hG
  | .comp f gs => compileTOK_comp hTm hTid f gs (compileTOK hG f) (compilesTOK hG gs)
  | .bRec g h₀ h₁ bd =>
      compileTOK_bRec hTm hTid g h₀ h₁ bd (compileTOK hG g) (compileTOK hG h₀) (compileTOK hG h₁)
        (compileTOK hG bd)
theorem compilesTOK (hG : GadgetOK A G q T K x B) :
    ∀ gs : List CobQ, ∀ g ∈ gs, CompileTOK A G q T K x B g
  | [], _, h => absurd h (by simp)
  | g :: gs, g', h => by
      rcases List.mem_cons.1 h with h1 | h1
      · rw [h1]; exact compileTOK hG g
      · exact compilesTOK hG gs g' h1
end

end Compile

end Elim

end Complexity.Space
