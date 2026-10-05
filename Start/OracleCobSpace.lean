/-
**Oracle Cobham terms compiled into oracle tape programs, with polynomial space.**

The relativized counterpart of `Start/CobhamSpace.lean`.  `Complexity.Space.OProg.compileQ` turns an
oracle Cobham term (`Complexity.CobQ`) into an oracle tape program on the register file laid out in
tracks.  The oracle-free constructors are compiled by the unrelativized compiler and lifted; the
composition and the bounded recursion are compiled as before, with oracle programs as their
pieces; and the query writes its argument register on the query tape and asks
(`Complexity.Space.OProg.queryReg`).

`Complexity.Space.OProg.compileQOK` is its correctness: on registers of length at most `N` the
compiled program of `c` sets its destination register to the value `CobQ.eval A c` and never uses
more than `(CobQ.spaceW c N + 3) · (2K + 1)` cells, work tape and query tape together, where
`CobQ.spaceW c` is a polynomial (`Complexity.CobQ.spaceW_polyBound`).
-/

import Mathlib
import Start.OracleProgLib
import Start.CobhamSpace

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobQ

mutual
/-- A bound on the lengths of all the words handled while evaluating an oracle Cobham term. -/
def spaceW : CobQ → ℕ → ℕ
  | .proj _, N => N
  | .empty, N => N
  | .app _, N => N + 1
  | .smash, N => N + N * N
  | .query, N => N + 1
  | .comp f gs, N => f.spaceW (N + spaceWs gs N) + spaceWs gs (N + spaceWs gs N)
  | .bRec g h₀ h₁ bd, N =>
      bd.spaceW (N + g.spaceW N + bd.spaceW N + h₀.spaceW (N + g.spaceW N + bd.spaceW N) +
          h₁.spaceW (N + g.spaceW N + bd.spaceW N)) +
        (N + g.spaceW N + bd.spaceW N + h₀.spaceW (N + g.spaceW N + bd.spaceW N) +
          h₁.spaceW (N + g.spaceW N + bd.spaceW N))
/-- `spaceW`, summed over a list of terms. -/
def spaceWs : List CobQ → ℕ → ℕ
  | [], _ => 0
  | g :: gs, N => g.spaceW N + spaceWs gs N
end

mutual
/-- The number of scratch registers the compiled program of a term uses. -/
def need : CobQ → ℕ
  | .proj _ => 0
  | .empty => 0
  | .app _ => 1
  | .smash => 2
  | .query => 0
  | .comp f gs => gs.length + f.need + needs gs
  | .bRec g h₀ h₁ bd => 6 + g.need + h₀.need + h₁.need + bd.need
/-- `need`, summed over a list of terms. -/
def needs : List CobQ → ℕ
  | [] => 0
  | g :: gs => g.need + needs gs
end

mutual
theorem spaceW_mono : ∀ c : CobQ, Monotone c.spaceW
  | .proj _ => fun _ _ h => by simpa [spaceW] using h
  | .empty => fun _ _ h => by simpa [spaceW] using h
  | .app _ => fun _ _ h => by simp [spaceW]; omega
  | .smash => fun a b h => by simp only [spaceW]; have := Nat.mul_le_mul h h; omega
  | .query => fun _ _ h => by simp [spaceW]; omega
  | .comp f gs => fun a b h => by
      simp only [spaceW]
      have h1 : a + spaceWs gs a ≤ b + spaceWs gs b := Nat.add_le_add h (spaceWs_mono gs h)
      exact Nat.add_le_add (spaceW_mono f h1) (spaceWs_mono gs h1)
  | .bRec g h₀ h₁ bd => fun a b h => by
      simp only [spaceW]
      have hM : a + g.spaceW a + bd.spaceW a ≤ b + g.spaceW b + bd.spaceW b :=
        Nat.add_le_add (Nat.add_le_add h (spaceW_mono g h)) (spaceW_mono bd h)
      have hM' : a + g.spaceW a + bd.spaceW a + h₀.spaceW (a + g.spaceW a + bd.spaceW a) +
            h₁.spaceW (a + g.spaceW a + bd.spaceW a) ≤
          b + g.spaceW b + bd.spaceW b + h₀.spaceW (b + g.spaceW b + bd.spaceW b) +
            h₁.spaceW (b + g.spaceW b + bd.spaceW b) :=
        Nat.add_le_add (Nat.add_le_add hM (spaceW_mono h₀ hM)) (spaceW_mono h₁ hM)
      exact Nat.add_le_add (spaceW_mono bd hM') hM'
theorem spaceWs_mono : ∀ gs : List CobQ, Monotone (spaceWs gs)
  | [] => fun _ _ _ => le_rfl
  | g :: gs => fun _ _ h => by
      simp only [spaceWs]; exact Nat.add_le_add (spaceW_mono g h) (spaceWs_mono gs h)
end

mutual
theorem le_spaceW : ∀ (c : CobQ) (N : ℕ), N ≤ c.spaceW N
  | .proj _, N => by simp [spaceW]
  | .empty, N => by simp [spaceW]
  | .app _, N => by simp [spaceW]
  | .smash, N => by simp [spaceW]
  | .query, N => by simp [spaceW]
  | .comp f gs, N => by
      simp only [spaceW]
      have := le_spaceW f (N + spaceWs gs N)
      omega
  | .bRec g h₀ h₁ bd, N => by
      simp only [spaceW]
      omega
theorem spaceWs_le : ∀ (gs : List CobQ) (N : ℕ), ∀ g ∈ gs, g.spaceW N ≤ spaceWs gs N
  | [], _, _, h => absurd h (by simp)
  | g :: gs, N, g', h => by
      simp only [spaceWs]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := spaceWs_le gs N g' h; omega
end

mutual
theorem spaceW_polyBound : ∀ c : CobQ, PolyBound c.spaceW
  | .proj _ => Cob.polyBound_id
  | .empty => Cob.polyBound_id
  | .app _ => Cob.polyBound_id.add (polyBound_const 1)
  | .smash => Cob.polyBound_id.add ⟨1, 2, fun n => by nlinarith⟩
  | .query => Cob.polyBound_id.add (polyBound_const 1)
  | .comp f gs => by
      have hM : PolyBound (fun N => N + spaceWs gs N) :=
        Cob.polyBound_id.add (spaceWs_polyBound gs)
      exact (PolyBound.comp (spaceW_polyBound f) hM).add (PolyBound.comp (spaceWs_polyBound gs) hM)
  | .bRec g h₀ h₁ bd => by
      have hM : PolyBound (fun N => N + g.spaceW N + bd.spaceW N) :=
        (Cob.polyBound_id.add (spaceW_polyBound g)).add (spaceW_polyBound bd)
      have hM' : PolyBound (fun N => N + g.spaceW N + bd.spaceW N +
          h₀.spaceW (N + g.spaceW N + bd.spaceW N) + h₁.spaceW (N + g.spaceW N + bd.spaceW N)) :=
        (hM.add (PolyBound.comp (spaceW_polyBound h₀) hM)).add
          (PolyBound.comp (spaceW_polyBound h₁) hM)
      exact (PolyBound.comp (spaceW_polyBound bd) hM').add hM'
theorem spaceWs_polyBound : ∀ gs : List CobQ, PolyBound (spaceWs gs)
  | [] => polyBound_const 0
  | g :: gs => (spaceW_polyBound g).add (spaceWs_polyBound gs)
end

/-! ### Values are bounded by `spaceW` -/

theorem eval_bRec_headD (A : Oracle) (g h₀ h₁ bd : CobQ) (args : List Word) :
    eval A (.bRec g h₀ h₁ bd) args = eval A (.bRec g h₀ h₁ bd) (args.headD [] :: args.tail) := by
  unfold eval
  rw [run_bRec, run_bRec]
  rfl

theorem bRec_length_le (A : Oracle) (g h₀ h₁ bd : CobQ) (rest : List Word) (N : ℕ)
    (hg : (eval A g rest).length ≤ g.spaceW N)
    (hbd : ∀ y : Word, y.length ≤ N → (eval A bd (y :: rest)).length ≤ bd.spaceW N) :
    ∀ y : Word, y.length ≤ N →
      (eval A (.bRec g h₀ h₁ bd) (y :: rest)).length ≤ g.spaceW N + bd.spaceW N
  | [], _ => by rw [eval_bRec_nil]; omega
  | b :: y, hy => by
      rw [eval_bRec_cons]
      have := hbd (b :: y) hy
      rw [List.length_take]
      omega

mutual
theorem eval_length_le (A : Oracle) : ∀ (c : CobQ) (args : List Word) (N : ℕ),
    (∀ a ∈ args, a.length ≤ N) → (eval A c args).length ≤ c.spaceW N
  | .proj i, args, N, h => by simpa [spaceW] using Cob.getD_length_le h i
  | .empty, args, N, h => by simp
  | .app b, args, N, h => by simpa [spaceW] using Cob.getD_length_le h 0
  | .smash, args, N, h => by
      simp only [eval_smash, List.length_replicate, spaceW]
      have := Nat.mul_le_mul (Cob.getD_length_le h 0) (Cob.getD_length_le h 1)
      omega
  | .query, args, N, h => by
      simp only [eval_query, spaceW]
      split <;> simp
  | .comp f gs, args, N, h => by
      rw [eval_comp, spaceW]
      have hM : ∀ a ∈ gs.map (fun g => eval A g args), a.length ≤ N + spaceWs gs N := by
        intro a ha
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
        have := evals_length_le A gs args N h g hg
        have := spaceWs_le gs N g hg
        omega
      have := eval_length_le A f _ _ hM
      omega
  | .bRec g h₀ h₁ bd, args, N, h => by
      rw [eval_bRec_headD]
      have hrest : ∀ a ∈ args.tail, a.length ≤ N := fun a ha => h a (List.mem_of_mem_tail ha)
      have hhead : (args.headD []).length ≤ N := by
        cases args with
        | nil => simp
        | cons a t => exact h a (by simp)
      have := bRec_length_le A g h₀ h₁ bd args.tail N (eval_length_le A g _ _ hrest)
        (fun y hy => eval_length_le A bd _ _ (by
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hy
          · exact hrest a ha)) _ hhead
      simp only [spaceW]
      omega
theorem evals_length_le (A : Oracle) : ∀ (gs : List CobQ) (args : List Word) (N : ℕ),
    (∀ a ∈ args, a.length ≤ N) → ∀ g ∈ gs, (eval A g args).length ≤ g.spaceW N
  | [], _, _, _, _, hg => absurd hg (by simp)
  | g :: gs, args, N, h, g', hg => by
      rcases List.mem_cons.1 hg with h1 | h1
      · rw [h1]; exact eval_length_le A g args N h
      · exact evals_length_le A gs args N h g' h1
end

end CobQ

/-! ### The compiler -/

namespace Space

namespace OProg

open Prog Tracks

/-- One step of bounded recursion, with oracle programs for the step and the bound. -/
def obrStep (K fr : ℕ) (ph pbd : OProg) (β : Bool) : OProg :=
  .seq ph (.seq (lift (prepend K (fr + 1) (fr + 5) β)) (.seq pbd
    (.seq (lift (truncate K (fr + 3) (fr + 4)))
    (.seq (lift (assign K (fr + 3) (fr + 2))) (.seq (lift (clear K (fr + 3)))
      (lift (clear K (fr + 4))))))))

/-- The query on the register `a?` (or on the empty word), into the register `d`. -/
def queryProg (K : ℕ) (a? : Option ℕ) (d : ℕ) : OProg :=
  match a? with
  | some a => queryReg K a d
  | none => .seq (lift (clear K d)) (.ask (lift (append K d true)) (lift skip))

mutual
/-- **The compiler**: `compileQ K c as d fr` sets register `d` to the value of the oracle Cobham
term `c` on the registers `as`, using the scratch registers from `fr` on. -/
def compileQ (K : ℕ) : CobQ → List ℕ → ℕ → ℕ → OProg
  | .proj i, as, d, fr => lift (compile K (.proj i) as d fr)
  | .empty, as, d, fr => lift (compile K .empty as d fr)
  | .app b, as, d, fr => lift (compile K (.app b) as d fr)
  | .smash, as, d, fr => lift (compile K .smash as d fr)
  | .query, as, d, _ => queryProg K as[0]? d
  | .comp f gs, as, d, fr =>
      .seq (compilesQ K gs as fr (fr + gs.length))
        (.seq (compileQ K f (List.range' fr gs.length) d (fr + gs.length))
          (lift (clearFrom K fr gs.length)))
  | .bRec g h₀ h₁ bd, as, d, fr =>
      .seq (match as[0]? with
        | some a => lift (assign K a fr)
        | none => lift skip)
      (.seq (compileQ K g as.tail (fr + 2) (fr + 6))
      (.seq (owhileNE fr (opopBranch K fr
          (obrStep K fr (compileQ K h₀ ((fr + 1) :: (fr + 2) :: as.tail) (fr + 3) (fr + 6))
            (compileQ K bd ((fr + 1) :: as.tail) (fr + 4) (fr + 6)) false)
          (obrStep K fr (compileQ K h₁ ((fr + 1) :: (fr + 2) :: as.tail) (fr + 3) (fr + 6))
            (compileQ K bd ((fr + 1) :: as.tail) (fr + 4) (fr + 6)) true)))
      (.seq (lift (assign K (fr + 2) d)) (.seq (lift (clear K (fr + 1)))
        (lift (clear K (fr + 2)))))))
/-- Compile the terms `gs` into the consecutive registers from `t` on. -/
def compilesQ (K : ℕ) : List CobQ → List ℕ → ℕ → ℕ → OProg
  | [], _, _, _ => lift skip
  | g :: gs, as, t, fr => .seq (compileQ K g as t fr) (compilesQ K gs as (t + 1) fr)
end

/-! ### Correctness -/

/-- The specification of the compiled program of an oracle term `c`. -/
def CompileQOK (A : Oracle) (K : ℕ) (x : List Bool) (B : ℕ) (c : CobQ) : Prop :=
  ∀ (as : List ℕ) (d fr : ℕ) (R : ℕ → List Bool) (N i : ℕ),
    (∀ a ∈ as, a < fr) → d < fr → d ∉ as → fr + c.need ≤ K →
    (∀ r, fr ≤ r → R r = []) → (∀ r, (R r).length ≤ N) → (c.spaceW N + 3) * wd K ≤ B →
    ORuns A x B (compileQ K c as d fr) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (CobQ.eval A c (as.map R))), 0, i⟩

variable {A : Oracle} {K : ℕ} {x : List Bool} {B : ℕ}

/-! #### Lifted primitives -/

theorem oruns_skip (v : ℕ → Bool) (h i : ℕ) :
    ORuns A x B (lift skip) ⟨v, h, i⟩ ⟨v, h, i⟩ := ORuns.lift (runs_skip v h i)

theorem oruns_clear (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (N : ℕ) (hN : (R j).length ≤ N)
    (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    ORuns A x B (lift (clear K j)) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R j []), 0, i⟩ :=
  ORuns.lift (runs_clear R j hj N hN hB i)

theorem oruns_assign (R : ℕ → List Bool) (a d : ℕ) (ha : a < K) (hd : d < K) (hne : a ≠ d)
    (N : ℕ) (hNa : (R a).length ≤ N) (hNd : (R d).length ≤ N) (hB : (N + 3) * wd K ≤ B)
    (i : ℕ) :
    ORuns A x B (lift (assign K a d)) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (R a)), 0, i⟩ :=
  ORuns.lift (runs_assign R a d ha hd hne N hNa hNd hB i)

theorem oruns_prepend (R : ℕ → List Bool) (j s : ℕ) (hj : j < K) (hs : s < K) (hne : j ≠ s)
    (hRs : R s = []) (β : Bool) (N : ℕ) (hN : (R j).length + 1 ≤ N) (hB : (N + 3) * wd K ≤ B)
    (i : ℕ) :
    ORuns A x B (lift (prepend K j s β)) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R j (β :: R j)), 0, i⟩ :=
  ORuns.lift (runs_prepend R j s hj hs hne hRs β N hN hB i)

theorem oruns_truncate (R : ℕ → List Bool) (w l : ℕ) (hw : w < K) (hl : l < K) (hne : w ≠ l)
    (N : ℕ) (hN : (R w).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    ORuns A x B (lift (truncate K w l)) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R w ((R w).take (R l).length)), 0, i⟩ :=
  ORuns.lift (runs_truncate R w l hw hl hne N hN hB i)

theorem oruns_clearFrom (n : ℕ) (R : ℕ → List Bool) (t : ℕ) (ht : t + n ≤ K) (N : ℕ)
    (hN : ∀ r, (R r).length ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    ORuns A x B (lift (clearFrom K t n)) ⟨lay K R, 0, i⟩
      ⟨lay K (fun r => if t ≤ r ∧ r < t + n then [] else R r), 0, i⟩ :=
  ORuns.lift (runs_clearFrom n R t ht N hN hB i)

/-! #### The oracle-free constructors, from the unrelativized compiler -/

theorem compileQOK_lift (c : Cob) (c' : CobQ) (hc : ∀ args, CobQ.eval A c' args = c.eval args)
    (hsp : ∀ N, c'.spaceW N = c.spaceW N) (hn : c'.need = c.need)
    (hprog : ∀ as d fr, compileQ K c' as d fr = lift (compile K c as d fr)) :
    CompileQOK A K x B c' := by
  intro as d fr R N i has hd hne hK hfr hN hB
  rw [hprog, hc]
  exact ORuns.lift (compileOK (K := K) (x := x) (B := B) c as d fr R N i has hd hne
    (by rw [← hn]; exact hK) hfr hN (by rw [← hsp]; exact hB))

theorem compileQOK_proj (i : ℕ) : CompileQOK A K x B (.proj i) :=
  compileQOK_lift (.proj i) _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

theorem compileQOK_empty : CompileQOK A K x B .empty :=
  compileQOK_lift .empty _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

theorem compileQOK_app (b : Bool) : CompileQOK A K x B (.app b) :=
  compileQOK_lift (.app b) _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

theorem compileQOK_smash : CompileQOK A K x B .smash :=
  compileQOK_lift .smash _ (fun _ => by simp) (fun _ => rfl) rfl (fun _ _ _ => rfl)

/-! #### The query -/

theorem compileQOK_query : CompileQOK A K x B .query := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [CobQ.spaceW] at hB
  simp only [CobQ.need] at hK
  simp only [compileQ, CobQ.eval_query, getD_map_eq]
  have hB' : (N + 1 + 3) * wd K ≤ B := by simpa [add_assoc] using hB
  unfold queryProg
  cases h0 : as[0]? with
  | none =>
      dsimp only
      refine (oruns_clear R d (by omega) (N + 1) (by have := hN d; omega) hB' i).seq ?_
      cases hA : A [] with
      | false =>
          refine ORunsQ.askF hA ((oruns_skip _ _ _).of_eq rfl ?_)
          simp
      | true =>
          refine ORunsQ.askT hA ((ORuns.lift (runs_append _ d (by omega) true (N + 1)
            (by simp) hB' i)).of_eq rfl ?_)
          simp
  | some a =>
      dsimp only
      have ha : a ∈ as := List.mem_of_getElem? h0
      have := oruns_queryReg (A := A) (x := x) (B := B) R a d (K := K)
        (by have := has a ha; omega) (by omega) (N + 1) (by omega)
        (by have := hN a; omega) (by have := hN d; omega) hB' i
      exact this

theorem runs_compiles (gs : List CobQ) (hgs : ∀ g ∈ gs, CompileQOK A K x B g) (as : List ℕ)
    (fr' : ℕ) (hK : fr' + CobQ.needs gs ≤ K) (N N' : ℕ) (i : ℕ) :
    ∀ (t : ℕ) (R : ℕ → List Bool), (∀ a ∈ as, a < t) → t + gs.length ≤ fr' →
    (∀ r, t ≤ r → R r = []) → (∀ a ∈ as, (R a).length ≤ N) → (∀ r, (R r).length ≤ N') →
    (∀ g ∈ gs, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B) →
    ORuns A x B (compilesQ K gs as t fr') ⟨lay K R, 0, i⟩
      ⟨lay K (setFrom R t (gs.map fun g => CobQ.eval A g (as.map R))), 0, i⟩ := by
  induction gs with
  | nil =>
      intro t R _ _ _ _ _ _
      simp only [compilesQ, List.map_nil, setFrom_nil]
      exact oruns_skip _ 0 i
  | cons g gs ih =>
      intro t R has ht hfr hNa hN hsp
      simp only [CobQ.needs] at hK
      simp only [List.length_cons] at ht
      have hmap : as.map (Function.update R t (CobQ.eval A g (as.map R))) = as.map R :=
        List.map_congr_left (fun a ha => Function.update_of_ne (by have := has a ha; omega) _ _)
      simp only [compilesQ]
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

theorem compileQOK_comp (f : CobQ) (gs : List CobQ) (hf : CompileQOK A K x B f)
    (hgs : ∀ g ∈ gs, CompileQOK A K x B g) : CompileQOK A K x B (.comp f gs) := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [CobQ.need] at hK
  simp only [CobQ.spaceW] at hB
  simp only [compileQ, CobQ.eval_comp]
  obtain ⟨M, hM⟩ : ∃ M, M = N + CobQ.spaceWs gs N := ⟨_, rfl⟩
  rw [← hM] at hB
  have hfM := CobQ.le_spaceW f M
  have hBM : (M + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
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
  refine (runs_compiles gs hgs as (fr + gs.length) (by omega) N M i fr R has (by omega) hfr
    (fun a _ => hN a) (fun r => by have := hN r; omega) (fun g hg => ⟨?_, ?_⟩)).seq ?_
  · have := CobQ.spaceWs_le gs N g hg; omega
  · have h1 := CobQ.spaceWs_le gs M g hg
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  refine ORunsQ.seq (hf (List.range' fr gs.length) d (fr + gs.length) (setFrom R fr ws) M i
    (fun a ha => by rw [List.mem_range'_1] at ha; omega) (by omega)
    (fun h => by rw [List.mem_range'_1] at h; omega) (by omega)
    (fun r hr => by simp only [setFrom]; rw [if_neg (by omega)]; exact hfr r (by omega))
    hlen2 (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)) ?_
  rw [show List.range' fr gs.length = List.range' fr ws.length by rw [hwsl],
    map_range'_setFrom]
  have hwsM : ∀ w ∈ ws, w.length ≤ M := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
    have := CobQ.eval_length_le A g (as.map R) N (fun w hw => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a)
    have := CobQ.spaceWs_le gs N g hg
    omega
  refine (oruns_clearFrom gs.length (Function.update (setFrom R fr ws) d (CobQ.eval A f ws)) fr
    (by omega)
    (f.spaceW M) (fun r => by
    rw [Function.update_apply]; split_ifs
    · exact CobQ.eval_length_le A f ws M hwsM
    · have := hlen2 r; omega) (le_trans (Nat.mul_le_mul_right _ (by omega)) hB) i).of_eq rfl ?_
  congr 2; funext r
  simp only [Function.update_apply, setFrom, hwsl]
  split_ifs <;> first | rfl | omega | (symm; exact hfr r (by omega))

theorem oruns_brStep (h bd : CobQ) (hh : CompileQOK A K x B h) (hbd : CompileQOK A K x B bd)
    (as' : List ℕ) (fr : ℕ) (β : Bool) (R : ℕ → List Bool) (M M' : ℕ) (i : ℕ)
    (has : ∀ a ∈ as', a < fr) (hKh : fr + 6 + h.need ≤ K) (hKb : fr + 6 + bd.need ≤ K)
    (hfr : ∀ r, fr + 3 ≤ r → R r = []) (hN : ∀ r, (R r).length ≤ M)
    (hS : (R (fr + 1)).length + 1 ≤ M') (hMM' : M ≤ M') (hhM : h.spaceW M ≤ M')
    (hB1 : (h.spaceW M + 3) * wd K ≤ B) (hB2 : (bd.spaceW M' + 3) * wd K ≤ B) :
    ORuns A x B (obrStep K fr (compileQ K h ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6))
      (compileQ K bd ((fr + 1) :: as') (fr + 4) (fr + 6)) β) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update (Function.update R (fr + 1) (β :: R (fr + 1))) (fr + 2)
        ((CobQ.eval A h (R (fr + 1) :: R (fr + 2) :: as'.map R)).take
          (CobQ.eval A bd ((β :: R (fr + 1)) :: as'.map R)).length)), 0, i⟩ := by
  have hM'b := CobQ.le_spaceW bd M'
  have hB3 : (M' + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB2
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
  unfold obrStep
  refine h1.seq ?_
  -- step 2
  set R1 := Function.update R (fr + 3) W with hR1
  have h2 := oruns_prepend (A := A) (x := x) (B := B) R1 (fr + 1) (fr + 5) (by omega) (by omega)
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
      simp only [R2, R1, Function.update_apply]; rw [if_neg (by omega), if_neg (by omega)]
      exact hfr r (by omega)) hR2N hB2
  have hR2a : as'.map R2 = as'.map R := hmap R2 (fun a ha => by
    have := has a ha
    simp only [R2, R1, Function.update_apply]; rw [if_neg (by omega), if_neg (by omega)])
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
  have h4 := oruns_truncate (A := A) (x := x) (B := B) R3 (fr + 3) (fr + 4) (by omega) (by omega)
    (by omega)
    _ (hR3N _) hB2 i
  rw [hR33, hR34] at h4
  refine h4.seq ?_
  -- step 5
  set R4 := Function.update R3 (fr + 3) (W.take T.length) with hR4
  have hR4N : ∀ r, (R4 r).length ≤ bd.spaceW M' := by
    intro r; simp only [R4, Function.update_apply]
    split_ifs
    · simp only [List.length_take]; have := hR3N (fr + 3); rw [hR33] at this; omega
    · exact hR3N r
  have h5 := oruns_assign (A := A) (x := x) (B := B) R4 (fr + 3) (fr + 2) (by omega) (by omega)
    (by omega)
    _ (hR4N _) (hR4N _) hB2 i
  refine h5.seq ?_
  -- steps 6, 7
  set R5 := Function.update R4 (fr + 2) (R4 (fr + 3)) with hR5
  have hR5N : ∀ r, (R5 r).length ≤ bd.spaceW M' := by
    intro r; simp only [R5, Function.update_apply]
    split_ifs
    · exact hR4N _
    · exact hR4N r
  refine (oruns_clear R5 (fr + 3) (by omega) _ (hR5N _) hB2 i).seq ?_
  refine (oruns_clear (Function.update R5 (fr + 3) []) (fr + 4) (by omega) _ (by
    rw [Function.update_apply]; split_ifs
    · simp
    · exact hR5N _) hB2 i).of_eq rfl ?_
  congr 2; funext r
  simp only [R5, R4, R3, R2, R1, Function.update_apply]
  split_ifs <;> first | rfl | omega | (subst_vars; simp_all)

theorem compileQOK_bRec (g h₀ h₁ bd : CobQ) (hg : CompileQOK A K x B g)
    (hh₀ : CompileQOK A K x B h₀)
    (hh₁ : CompileQOK A K x B h₁) (hbd : CompileQOK A K x B bd) :
    CompileQOK A K x B (.bRec g h₀ h₁ bd) := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [CobQ.need] at hK
  simp only [CobQ.spaceW] at hB
  obtain ⟨M, hM⟩ : ∃ M, M = N + g.spaceW N + bd.spaceW N := ⟨_, rfl⟩
  rw [← hM] at hB
  obtain ⟨M', hM'⟩ : ∃ M', M' = M + h₀.spaceW M + h₁.spaceW M := ⟨_, rfl⟩
  rw [← hM'] at hB
  have hbM' := CobQ.le_spaceW bd M'
  have hgN := CobQ.le_spaceW g N
  have hB3 : (M + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
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
  have hfirst : ORuns A x B (match as[0]? with
      | some a => lift (assign K a fr)
      | none => lift skip) ⟨lay K R, 0, i⟩ ⟨lay K (Function.update R fr X), 0, i⟩ := by
    cases as with
    | nil =>
        refine (oruns_skip _ 0 i).of_eq rfl ?_
        congr 2; simp only [X, List.map_nil, List.headD_nil]
        rw [← hfr fr le_rfl, Function.update_eq_self]
    | cons a t =>
        have ha := has a (by simp)
        exact oruns_assign R a fr (by omega) (by omega) (by omega) N (hN a) (hN fr) (by
          exact le_trans (Nat.mul_le_mul_right _ (by omega)) hB3) i
  simp only [compileQ]
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
    (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)
  rw [hmapR _ (fun r hr => Function.update_of_ne (by omega) _ _)] at hg'
  refine ORunsQ.seq (r := []) (t := ⟨lay K (Rs 0), 0, i⟩) (hg'.of_eq rfl ?_) ?_
  · congr 2; funext r
    simp only [Rs, V, Function.update_apply, Nat.sub_zero, hL, List.take_length,
      List.drop_length, CobQ.eval_bRec_nil]
    split_ifs <;> first | rfl | omega | exact hfr r (by omega)
  refine ORunsQ.seq (r := []) (t := ⟨lay K (Rs L), 0, i⟩) ?_ ?_
  swap
  · have hRsL2 : Rs L (fr + 2) = CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (X :: rest) := by
      simp [Rs, V]
    refine (oruns_assign (Rs L) (fr + 2) d (by omega) (by omega) (by omega) M (hRsN _ _)
      (hRsN _ _) hB3 i).seq ?_
    rw [hRsL2]
    have hU : ∀ r,
        (Function.update (Rs L) d (CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (X :: rest)) r).length
        ≤ M := by
      intro r; rw [Function.update_apply]; split_ifs
      · rw [← hRsL2]; exact hRsN _ _
      · exact hRsN _ _
    refine (oruns_clear _ (fr + 1) (by omega) M (hU _) hB3 i).seq ?_
    refine (oruns_clear _ (fr + 2) (by omega) M (by
      rw [Function.update_apply]; split_ifs
      · simp
      · exact hU _) hB3 i).of_eq rfl ?_
    congr 2; funext r
    simp only [Rs, Function.update_apply, Nat.sub_self, List.take_zero]
    split_ifs <;> first | rfl | omega | exact (hfr r (by omega)).symm
  have hBw : wd K < B := by nlinarith
  have hRsfr : ∀ k, Rs k fr = X.take (L - k) := fun k => by simp [Rs]
  refine oruns_whileNE Rs fr L (by omega) _ (fun k hk => ?_) ?_ hBw i (fun k hk => ?_)
  · rw [hRsfr]; intro h; have := congrArg List.length h
    rw [List.length_take, ← hL, List.length_nil] at this; omega
  · rw [hRsfr, Nat.sub_self, List.take_zero]
  have hne' : Rs k fr ≠ [] := by
    rw [hRsfr]; intro h; have := congrArg List.length h
    rw [List.length_take, ← hL, List.length_nil] at this; omega
  refine oruns_popBranch (Rs k) fr (by omega) hne' M (hRsN k fr) hB3 i _ _ _ ?_
  have hlast : (Rs k fr).getLast hne' = X[L - k - 1]'(by omega) := by
    have : ∀ (l : List Bool) (h : l ≠ []), l = X.take (L - k) →
        l.getLast h = X[L - k - 1]'(by omega) := by
      intro l h hl; subst hl; exact take_getLast_eq X (L - k) (by omega) (by omega) h
    exact this _ _ (hRsfr k)
  set R' := Function.update (Rs k) fr (Rs k fr).dropLast with hR'
  have hR'1 : R' (fr + 1) = X.drop (L - k) := by simp [R', Rs]
  have hR'2 : R' (fr + 2) = V k := by simp [R', Rs]
  have hR'a : as'.map R' = rest := hmapR R' (fun r hr => by
    simp only [R', Rs, Function.update_apply]; rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)])
  have hR'fr : ∀ r, fr + 3 ≤ r → R' r = [] := fun r hr => by
    simp only [R', Rs, Function.update_apply]; rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]; exact hfr r (by omega)
  have hR'N : ∀ r, (R' r).length ≤ M := fun r => by
    simp only [R', Function.update_apply]; split_ifs
    · simp only [List.length_dropLast]; have := hRsN k fr; omega
    · exact hRsN k r
  have key : ∀ (β : Bool) (h : CobQ), CompileQOK A K x B h → fr + 6 + h.need ≤ K →
      h.spaceW M ≤ M' → X[L - k - 1]'(by omega) = β →
      (∀ ys, CobQ.eval A (CobQ.bRec g h₀ h₁ bd) ((β :: ys) :: rest) =
        (CobQ.eval A h (ys :: CobQ.eval A (CobQ.bRec g h₀ h₁ bd) (ys :: rest) :: rest)).take
          (CobQ.eval A bd ((β :: ys) :: rest)).length) →
      ORuns A x B (obrStep K fr (compileQ K h ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6))
        (compileQ K bd ((fr + 1) :: as') (fr + 4) (fr + 6)) β) ⟨lay K R', 0, i⟩
        ⟨lay K (Rs (k + 1)), 0, i⟩ := by
    intro β h hh hKh hhM hβ hrec
    have := oruns_brStep h bd hh hbd as' fr β R' M M' i has'f hKh (by omega) hR'fr hR'N
      (by rw [hR'1, List.length_drop]; omega) (by omega) hhM
      (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)
      (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)
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
  · simp only [Bool.false_eq_true, if_false]
    exact key false h₀ hh₀ (by omega) (by omega) hβ (fun ys => by simp [CobQ.eval_bRec_cons])
  · simp only [if_true]
    exact key true h₁ hh₁ (by omega) (by omega) hβ (fun ys => by simp [CobQ.eval_bRec_cons])

mutual
/-- **Compiler correctness**, for every oracle Cobham term. -/
theorem compileQOK : ∀ c : CobQ, CompileQOK A K x B c
  | .proj i => compileQOK_proj i
  | .empty => compileQOK_empty
  | .app b => compileQOK_app b
  | .smash => compileQOK_smash
  | .query => compileQOK_query
  | .comp f gs => compileQOK_comp f gs (compileQOK f) (compilesQOK gs)
  | .bRec g h₀ h₁ bd =>
      compileQOK_bRec g h₀ h₁ bd (compileQOK g) (compileQOK h₀) (compileQOK h₁) (compileQOK bd)
theorem compilesQOK : ∀ gs : List CobQ, ∀ g ∈ gs, CompileQOK A K x B g
  | [], _, h => absurd h (by simp)
  | g :: gs, g', h => by
      rcases List.mem_cons.1 h with h1 | h1
      · rw [h1]; exact compileQOK g
      · exact compilesQOK gs g' h1
end

end OProg

end Space

end Complexity
