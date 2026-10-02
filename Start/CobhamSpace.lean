/-
**Cobham terms compiled into tape programs, with polynomial space.**

The compiler `Complexity.Space.compile` turns a Cobham term into a tape program on the register
file laid out in tracks (`Start/SpaceProgTracks.lean`): projections and constants are track
copies, `app` is a prepend, the smash function is two nested counting loops, composition evaluates
the arguments into fresh registers, and bounded recursion runs over the recursion word from its
end, keeping the suffix read so far, the value on it, and two scratch registers for the step and
the bound.

`Complexity.Space.compileOK` is its correctness: on registers of length at most `N` the compiled
program of `c` sets its destination register to the value of `c` and never uses more than
`(Cob.spaceW c N + 3) · (2K + 1)` work cells, where `Cob.spaceW c` is a polynomial
(`Complexity.Cob.spaceW_polyBound`) bounding every word handled while evaluating `c`.
-/

import Mathlib
import Start.SpaceProgTracks

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Cob

mutual
/-- A bound on the lengths of all the words handled while evaluating a Cobham term, in terms of a
bound `N` on the lengths of the words already present. -/
def spaceW : Cob → ℕ → ℕ
  | .proj _, N => N
  | .empty, N => N
  | .app _, N => N + 1
  | .smash, N => N + N * N
  | .comp f gs, N => f.spaceW (N + spaceWs gs N) + spaceWs gs (N + spaceWs gs N)
  | .bRec g h₀ h₁ bd, N =>
      bd.spaceW (N + g.spaceW N + bd.spaceW N + h₀.spaceW (N + g.spaceW N + bd.spaceW N) +
          h₁.spaceW (N + g.spaceW N + bd.spaceW N)) +
        (N + g.spaceW N + bd.spaceW N + h₀.spaceW (N + g.spaceW N + bd.spaceW N) +
          h₁.spaceW (N + g.spaceW N + bd.spaceW N))
/-- `spaceW`, summed over a list of terms. -/
def spaceWs : List Cob → ℕ → ℕ
  | [], _ => 0
  | g :: gs, N => g.spaceW N + spaceWs gs N
end

mutual
/-- The number of scratch registers the compiled program of a term uses. -/
def need : Cob → ℕ
  | .proj _ => 0
  | .empty => 0
  | .app _ => 1
  | .smash => 2
  | .comp f gs => gs.length + f.need + needs gs
  | .bRec g h₀ h₁ bd => 6 + g.need + h₀.need + h₁.need + bd.need
/-- `need`, summed over a list of terms. -/
def needs : List Cob → ℕ
  | [] => 0
  | g :: gs => g.need + needs gs
end

/-! ### The bound is monotone, dominates its argument, and is polynomial -/

mutual
theorem spaceW_mono : ∀ c : Cob, Monotone c.spaceW
  | .proj _ => fun _ _ h => by simpa [spaceW] using h
  | .empty => fun _ _ h => by simpa [spaceW] using h
  | .app _ => fun _ _ h => by simp [spaceW]; omega
  | .smash => fun a b h => by simp only [spaceW]; have := Nat.mul_le_mul h h; omega
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
theorem spaceWs_mono : ∀ gs : List Cob, Monotone (spaceWs gs)
  | [] => fun _ _ _ => le_rfl
  | g :: gs => fun _ _ h => Nat.add_le_add (spaceW_mono g h) (spaceWs_mono gs h)
end

mutual
theorem le_spaceW : ∀ (c : Cob) (N : ℕ), N ≤ c.spaceW N
  | .proj _, N => le_rfl
  | .empty, N => le_rfl
  | .app _, N => Nat.le_succ N
  | .smash, N => Nat.le_add_right _ _
  | .comp f gs, N => by
      simp only [spaceW]
      have := le_spaceW f (N + spaceWs gs N)
      omega
  | .bRec g h₀ h₁ bd, N => by
      simp only [spaceW]
      omega
theorem spaceWs_le : ∀ (gs : List Cob) (N : ℕ), ∀ g ∈ gs, g.spaceW N ≤ spaceWs gs N
  | [], _, _, h => absurd h (by simp)
  | g :: gs, N, g', h => by
      simp only [spaceWs]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := spaceWs_le gs N g' h; omega
end

theorem polyBound_id : PolyBound (fun n => n) := ⟨1, 1, fun n => by simp⟩

mutual
theorem spaceW_polyBound : ∀ c : Cob, PolyBound c.spaceW
  | .proj _ => polyBound_id
  | .empty => polyBound_id
  | .app _ => polyBound_id.add (polyBound_const 1)
  | .smash => polyBound_id.add ⟨1, 2, fun n => by nlinarith⟩
  | .comp f gs => by
      have hM : PolyBound (fun N => N + spaceWs gs N) := polyBound_id.add (spaceWs_polyBound gs)
      exact (PolyBound.comp (spaceW_polyBound f) hM).add (PolyBound.comp (spaceWs_polyBound gs) hM)
  | .bRec g h₀ h₁ bd => by
      have hM : PolyBound (fun N => N + g.spaceW N + bd.spaceW N) :=
        (polyBound_id.add (spaceW_polyBound g)).add (spaceW_polyBound bd)
      have hM' : PolyBound (fun N => N + g.spaceW N + bd.spaceW N +
          h₀.spaceW (N + g.spaceW N + bd.spaceW N) + h₁.spaceW (N + g.spaceW N + bd.spaceW N)) :=
        (hM.add (PolyBound.comp (spaceW_polyBound h₀) hM)).add
          (PolyBound.comp (spaceW_polyBound h₁) hM)
      exact (PolyBound.comp (spaceW_polyBound bd) hM').add hM'
theorem spaceWs_polyBound : ∀ gs : List Cob, PolyBound (spaceWs gs)
  | [] => polyBound_const 0
  | g :: gs => (spaceW_polyBound g).add (spaceWs_polyBound gs)
end

/-! ### Values are bounded by `spaceW` -/

theorem eval_bRec_headD (g h₀ h₁ bd : Cob) (args : List Word) :
    (Cob.bRec g h₀ h₁ bd).eval args = (Cob.bRec g h₀ h₁ bd).eval (args.headD [] :: args.tail) := by
  rw [Cob.eval_bRec, Cob.eval_bRec]; rfl

theorem bRec_length_le (g h₀ h₁ bd : Cob) (rest : List Word) (N : ℕ)
    (hg : (g.eval rest).length ≤ g.spaceW N)
    (hbd : ∀ y : Word, y.length ≤ N → (bd.eval (y :: rest)).length ≤ bd.spaceW N) :
    ∀ y : Word, y.length ≤ N →
      ((Cob.bRec g h₀ h₁ bd).eval (y :: rest)).length ≤ g.spaceW N + bd.spaceW N
  | [], _ => by rw [Cob.eval_bRec_nil]; omega
  | b :: y, hy => by
      rw [Cob.eval_bRec_cons]
      have := hbd (b :: y) hy
      rw [List.length_take]
      omega

theorem getD_length_le {args : List Word} {N : ℕ} (h : ∀ a ∈ args, a.length ≤ N) (i : ℕ) :
    (args.getD i []).length ≤ N := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : args[i]? with
  | none => simp
  | some a => exact h a (List.mem_of_getElem? hi)

mutual
theorem eval_length_le : ∀ (c : Cob) (args : List Word) (N : ℕ),
    (∀ a ∈ args, a.length ≤ N) → (c.eval args).length ≤ c.spaceW N
  | .proj i, args, N, h => by simpa [spaceW] using getD_length_le h i
  | .empty, args, N, h => by simp
  | .app b, args, N, h => by simpa [spaceW] using getD_length_le h 0
  | .smash, args, N, h => by
      simp only [Cob.eval_smash, List.length_replicate, spaceW]
      have := Nat.mul_le_mul (getD_length_le h 0) (getD_length_le h 1)
      omega
  | .comp f gs, args, N, h => by
      rw [Cob.eval_comp, spaceW]
      have hM : ∀ a ∈ gs.map (fun g => g.eval args), a.length ≤ N + spaceWs gs N := by
        intro a ha
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 ha
        have := evals_length_le gs args N h g hg
        have := spaceWs_le gs N g hg
        omega
      have := eval_length_le f _ _ hM
      omega
  | .bRec g h₀ h₁ bd, args, N, h => by
      rw [eval_bRec_headD]
      have hrest : ∀ a ∈ args.tail, a.length ≤ N := fun a ha => h a (List.mem_of_mem_tail ha)
      have hhead : (args.headD []).length ≤ N := by
        cases args with
        | nil => simp
        | cons a t => exact h a (by simp)
      have := bRec_length_le g h₀ h₁ bd args.tail N (eval_length_le g _ _ hrest)
        (fun y hy => eval_length_le bd _ _ (by
          intro a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hy
          · exact hrest a ha)) _ hhead
      simp only [spaceW]
      omega
theorem evals_length_le : ∀ (gs : List Cob) (args : List Word) (N : ℕ),
    (∀ a ∈ args, a.length ≤ N) → ∀ g ∈ gs, (g.eval args).length ≤ g.spaceW N
  | [], _, _, _, _, hg => absurd hg (by simp)
  | g :: gs, args, N, h, g', hg => by
      rcases List.mem_cons.1 hg with h1 | h1
      · rw [h1]; exact eval_length_le g args N h
      · exact evals_length_le gs args N h g' h1
end

end Cob

/-! ### The compiler -/

namespace Space

open Prog Tracks

/-- `R d := R a` if the argument exists, `R d := []` otherwise. -/
def argOr (K : ℕ) (a? : Option ℕ) (d : ℕ) : Prog :=
  match a? with
  | some a => assign K a d
  | none => clear K d

/-- Clear the `n` tracks `t, …, t + n - 1`. -/
def clearFrom (K : ℕ) : ℕ → ℕ → Prog
  | _, 0 => skip
  | t, n + 1 => .seq (clear K t) (clearFrom K (t + 1) n)

/-- The inner loop of the smash function: append `|R a₁|` ones to `R d`, counting down a copy of
`R a₁` in track `t`. -/
def smashInner (K a₁ d t : ℕ) : Prog :=
  .seq (assign K a₁ t) (whileNE t (popBranch K t (append K d true) (append K d true)))

/-- The smash function `R d := 1^{|R a₀| · |R a₁|}`, with scratch tracks `fr`, `fr + 1`. -/
def smashProg (K : ℕ) (as : List ℕ) (d fr : ℕ) : Prog :=
  match as[0]?, as[1]? with
  | some a₀, some a₁ =>
      .seq (clear K d) (.seq (assign K a₀ fr)
        (whileNE fr (popBranch K fr (smashInner K a₁ d (fr + 1)) (smashInner K a₁ d (fr + 1)))))
  | _, _ => clear K d

/-- One step of bounded recursion, on the registers `S = fr + 1` (the suffix read so far),
`V = fr + 2` (the value on it), `W = fr + 3`, `T = fr + 4` and the scratch track `fr + 5`: with
`ph` computing `h_β(S, V, rest)` into `W` and `pbd` computing `bd(S, rest)` into `T`,
`V := (h_β(S, V, rest)).take |bd(β :: S, rest)|` and `S := β :: S`. -/
def brStep (K fr : ℕ) (ph pbd : Prog) (β : Bool) : Prog :=
  .seq ph (.seq (prepend K (fr + 1) (fr + 5) β) (.seq pbd (.seq (truncate K (fr + 3) (fr + 4))
    (.seq (assign K (fr + 3) (fr + 2)) (.seq (clear K (fr + 3)) (clear K (fr + 4)))))))

mutual
/-- **The compiler.**  `compile K c as d fr`: a tape program which, on the track layout with `K`
tracks, sets register `d` to the value of the Cobham term `c` on the registers `as`, using the
scratch registers from `fr` on (and leaving them empty). -/
def compile (K : ℕ) : Cob → List ℕ → ℕ → ℕ → Prog
  | .proj i, as, d, _ => argOr K as[i]? d
  | .empty, _, d, _ => clear K d
  | .app b, as, d, fr => .seq (argOr K as[0]? d) (prepend K d fr b)
  | .smash, as, d, fr => smashProg K as d fr
  | .comp f gs, as, d, fr =>
      .seq (compiles K gs as fr (fr + gs.length))
        (.seq (compile K f (List.range' fr gs.length) d (fr + gs.length))
          (clearFrom K fr gs.length))
  | .bRec g h₀ h₁ bd, as, d, fr =>
      .seq (match as[0]? with
        | some a => assign K a fr
        | none => skip)
      (.seq (compile K g as.tail (fr + 2) (fr + 6))
      (.seq (whileNE fr (popBranch K fr
          (brStep K fr (compile K h₀ ((fr + 1) :: (fr + 2) :: as.tail) (fr + 3) (fr + 6))
            (compile K bd ((fr + 1) :: as.tail) (fr + 4) (fr + 6)) false)
          (brStep K fr (compile K h₁ ((fr + 1) :: (fr + 2) :: as.tail) (fr + 3) (fr + 6))
            (compile K bd ((fr + 1) :: as.tail) (fr + 4) (fr + 6)) true)))
      (.seq (assign K (fr + 2) d) (.seq (clear K (fr + 1)) (clear K (fr + 2))))))
/-- Compile the terms `gs` into the consecutive registers from `t` on. -/
def compiles (K : ℕ) : List Cob → List ℕ → ℕ → ℕ → Prog
  | [], _, _, _ => skip
  | g :: gs, as, t, fr => .seq (compile K g as t fr) (compiles K gs as (t + 1) fr)
end

/-! ### Correctness -/

/-- The specification of the compiled program of a term `c`: on registers `R` whose lengths are
at most `N`, with the scratch registers from `fr` on empty, it sets `R d` to the value of `c` on
the registers `as`, within `(spaceW c N + 3)(2K + 1)` cells. -/
def CompileOK (K : ℕ) (x : List Bool) (B : ℕ) (c : Cob) : Prop :=
  ∀ (as : List ℕ) (d fr : ℕ) (R : ℕ → List Bool) (N i : ℕ),
    (∀ a ∈ as, a < fr) → d < fr → d ∉ as → fr + c.need ≤ K →
    (∀ r, fr ≤ r → R r = []) → (∀ r, (R r).length ≤ N) → (c.spaceW N + 3) * wd K ≤ B →
    Runs x B (compile K c as d fr) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (c.eval (as.map R))), 0, i⟩

variable {K : ℕ} {x : List Bool} {B : ℕ}

theorem getD_map_eq (as : List ℕ) (R : ℕ → List Bool) (j : ℕ) :
    (as.map R).getD j [] = match as[j]? with
      | some a => R a
      | none => [] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases as[j]? <;> rfl

theorem runs_argOr (as : List ℕ) (j d : ℕ) (R : ℕ → List Bool) (N : ℕ) (hd : d < K)
    (has : ∀ a ∈ as, a < K) (hne : d ∉ as) (hN : ∀ r, (R r).length ≤ N)
    (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (argOr K as[j]? d) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d ((as.map R).getD j [])), 0, i⟩ := by
  rw [getD_map_eq]
  unfold argOr
  cases h : as[j]? with
  | none => exact runs_clear R d hd N (hN d) hB i
  | some a =>
      have ha : a ∈ as := List.mem_of_getElem? h
      exact runs_assign R a d (has a ha) hd (fun e => hne (e ▸ ha)) N (hN a) (hN d) hB i

theorem compileOK_proj (i : ℕ) : CompileOK K x B (.proj i) := by
  intro as d fr R N i' has hd hne hK hfr hN hB
  simp only [Cob.spaceW] at hB
  simp only [compile, Cob.eval_proj]
  exact runs_argOr as i d R N (by simp [Cob.need] at hK; omega)
    (fun a ha => by have := has a ha; simp [Cob.need] at hK; omega) hne hN hB i'

theorem compileOK_empty : CompileOK K x B .empty := by
  intro as d fr R N i' has hd hne hK hfr hN hB
  simp only [Cob.spaceW] at hB
  simp only [compile, Cob.eval_empty]
  exact runs_clear R d (by simp [Cob.need] at hK; omega) N (hN d) hB i'

theorem compileOK_app (b : Bool) : CompileOK K x B (.app b) := by
  intro as d fr R N i' has hd hne hK hfr hN hB
  simp only [Cob.spaceW] at hB
  simp only [Cob.need] at hK
  simp only [compile, Cob.eval_app]
  have hB' : (N + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  refine (runs_argOr as 0 d R N (by omega) (fun a ha => by have := has a ha; omega) hne hN hB'
    i').seq ?_
  have hlen := Cob.getD_length_le (args := as.map R) (N := N) (fun a ha => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 ha; exact hN r) 0
  have := runs_prepend (x := x) (B := B) (K := K) (Function.update R d ((as.map R).getD 0 [])) d fr
    (by omega) (by omega) (by omega) (by rw [Function.update_of_ne (by omega)]; exact hfr fr le_rfl)
    b (N + 1) (by simp only [Function.update_self]; omega) hB i'
  rw [Function.update_idem, Function.update_self] at this
  exact this

theorem dropLast_take_eq (l : List Bool) (n : ℕ) (h : n ≤ l.length) :
    (l.take n).dropLast = l.take (n - 1) := by
  rw [List.dropLast_eq_take, List.take_take, List.length_take]; congr 1; omega

theorem runs_smashInner (R : ℕ → List Bool) (a₁ d t : ℕ) (ha : a₁ < K) (hd : d < K) (ht : t < K)
    (had : a₁ ≠ d) (hat : a₁ ≠ t) (hdt : d ≠ t) (hRt : R t = []) (M : ℕ)
    (hM : ∀ r, (R r).length ≤ M) (hdM : (R d).length + (R a₁).length ≤ M)
    (hB : (M + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (smashInner K a₁ d t) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R d (R d ++ List.replicate (R a₁).length true)), 0, i⟩ := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (R a₁).length := ⟨_, rfl⟩
  let Rs : ℕ → ℕ → List Bool := fun m =>
    Function.update (Function.update R t ((R a₁).take (Q - m))) d (R d ++ List.replicate m true)
  refine (runs_assign R a₁ t ha ht hat M (hM a₁) (hM t) hB i).seq ?_
  have h0 : Function.update R t (R a₁) = Rs 0 := by
    funext r; simp only [Rs, Function.update_apply]; split_ifs <;> simp_all
  have hQe : Function.update R d (R d ++ List.replicate (R a₁).length true) = Rs Q := by
    funext r; simp only [Rs, Function.update_apply]; split_ifs <;> simp_all
  rw [h0, hQe]
  have hBw : wd K < B := by nlinarith
  refine runs_whileNE Rs t Q ht _ (fun m hm => ?_) ?_ hBw i (fun m hm => ?_)
  · simp only [Rs, Function.update_of_ne (Ne.symm hdt), Function.update_self]
    intro h; have := congrArg List.length h
    rw [List.length_take, ← hQ, List.length_nil] at this; omega
  · simp [Rs, Function.update_of_ne (Ne.symm hdt)]
  · have hlen : ∀ r, (Rs m r).length ≤ M := by
      intro r; simp only [Rs, Function.update_apply]
      split_ifs
      · simp; omega
      · simp; have := hM a₁; omega
      · exact hM r
    have hne : Rs m t ≠ [] := by
      simp only [Rs, Function.update_of_ne (Ne.symm hdt), Function.update_self]
      intro h; have := congrArg List.length h
      rw [List.length_take, ← hQ, List.length_nil] at this; omega
    refine runs_popBranch (Rs m) t ht hne M (hlen t) hB i _ _ _ ?_
    rw [ite_self]
    have := runs_append (x := x) (Function.update (Rs m) t (Rs m t).dropLast) d hd true M
      (by
        simp only [Function.update_of_ne hdt, Rs, Function.update_self, List.length_append,
          List.length_replicate]; omega) hB i
    refine this.of_eq rfl ?_
    congr 2
    funext r
    simp only [Rs, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [List.replicate_succ', dropLast_take_eq, Nat.sub_sub]

theorem compileOK_smash : CompileOK K x B .smash := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [Cob.spaceW] at hB
  simp only [Cob.need] at hK
  have hB' : (N + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  simp only [Cob.eval_smash, getD_map_eq]
  simp only [compile, smashProg]
  cases h0 : as[0]? with
  | none => simpa using runs_clear R d (by omega) N (hN d) hB' i
  | some a₀ =>
  cases h1 : as[1]? with
  | none => simpa using runs_clear R d (by omega) N (hN d) hB' i
  | some a₁ =>
  dsimp only
  have ha₀ : a₀ ∈ as := List.mem_of_getElem? h0
  have ha₁ : a₁ ∈ as := List.mem_of_getElem? h1
  have ha₀f := has a₀ ha₀
  have ha₁f := has a₁ ha₁
  have hd₀ : d ≠ a₀ := fun e => hne (e ▸ ha₀)
  have hd₁ : d ≠ a₁ := fun e => hne (e ▸ ha₁)
  obtain ⟨P, hP⟩ : ∃ P, P = (R a₀).length := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (R a₁).length := ⟨_, rfl⟩
  have hPN : P ≤ N := hP ▸ hN a₀
  have hQN : Q ≤ N := hQ ▸ hN a₁
  have hPQ : P * Q ≤ N * N := Nat.mul_le_mul hPN hQN
  let Rs : ℕ → ℕ → List Bool := fun k =>
    Function.update (Function.update R fr ((R a₀).take (P - k))) d (List.replicate (k * Q) true)
  refine (runs_clear R d (by omega) N (hN d) hB' i).seq ?_
  refine Runs.seq (t := ⟨lay K (Rs 0), 0, i⟩) ?_ ?_
  · have := runs_assign (x := x) (Function.update R d []) a₀ fr (by omega) (by omega) (by omega) N
      (by rw [Function.update_of_ne (Ne.symm hd₀)]; exact hN a₀)
      (by rw [Function.update_of_ne (by omega)]; exact hN fr) hB' i
    refine this.of_eq rfl ?_
    congr 2; funext r; simp only [Rs, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  have hfin : Function.update R d (List.replicate (P * Q) true) = Rs P := by
    funext r; simp only [Rs, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  rw [← hP, ← hQ, hfin]
  have hBw : wd K < B := by nlinarith
  refine runs_whileNE Rs fr P (by omega) _ (fun k hk => ?_) ?_ hBw i (fun k hk => ?_)
  · simp only [Rs, Function.update_of_ne (show fr ≠ d by omega), Function.update_self]
    intro h; have := congrArg List.length h
    rw [List.length_take, ← hP, List.length_nil] at this; omega
  · simp [Rs, Function.update_of_ne (show fr ≠ d by omega)]
  · have hkQ : (k + 1) * Q ≤ P * Q := Nat.mul_le_mul_right _ hk
    have hlen : ∀ r, (Rs k r).length ≤ N + N * N := by
      intro r; simp only [Rs, Function.update_apply]
      split_ifs
      · simp only [List.length_replicate]; nlinarith
      · simp only [List.length_take]; omega
      · have := hN r; omega
    have hne : Rs k fr ≠ [] := by
      simp only [Rs, Function.update_of_ne (show fr ≠ d by omega), Function.update_self]
      intro h; have := congrArg List.length h
      rw [List.length_take, ← hP, List.length_nil] at this; omega
    refine runs_popBranch (Rs k) fr (by omega) hne _ (hlen fr) hB i _ _ _ ?_
    rw [ite_self]
    set R' := Function.update (Rs k) fr (Rs k fr).dropLast with hR'
    have hR'd : R' d = List.replicate (k * Q) true := by
      simp [R', Rs, Function.update_of_ne (show d ≠ fr by omega)]
    have hR'a : R' a₁ = R a₁ := by
      simp [R', Rs, Function.update_of_ne (show a₁ ≠ fr by omega),
        Function.update_of_ne (Ne.symm hd₁)]
    have hR'len : ∀ r, (R' r).length ≤ N + N * N := by
      intro r; simp only [R', Function.update_apply]
      split_ifs
      · simp only [List.length_dropLast]; have := hlen fr; omega
      · exact hlen r
    have := runs_smashInner (x := x) R' a₁ d (fr + 1) (by omega) (by omega) (by omega)
      (Ne.symm hd₁) (by omega) (by omega)
      (by simp [R', Rs,
            Function.update_of_ne (show fr + 1 ≠ d by omega), hfr]) _ hR'len
      (by rw [hR'd, hR'a, List.length_replicate, ← hQ]; nlinarith) hB i
    refine this.of_eq rfl ?_
    congr 2
    rw [hR'd, hR'a, ← hQ, List.replicate_append_replicate]
    funext r
    simp only [R', Rs, Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all [dropLast_take_eq, Nat.sub_sub, Nat.succ_mul]

/-- The register file `R` with the words `ws` written into the registers `t, t + 1, …`. -/
def setFrom (R : ℕ → List Bool) (t : ℕ) (ws : List (List Bool)) : ℕ → List Bool := fun r =>
  if t ≤ r ∧ r < t + ws.length then ws.getD (r - t) [] else R r

theorem setFrom_nil (R : ℕ → List Bool) (t : ℕ) : setFrom R t [] = R := by
  funext r; simp [setFrom]

theorem setFrom_cons (R : ℕ → List Bool) (t : ℕ) (w : List Bool) (ws : List (List Bool)) :
    setFrom (Function.update R t w) (t + 1) ws = setFrom R t (w :: ws) := by
  funext r
  simp only [setFrom, Function.update_apply, List.length_cons]
  by_cases h : r = t
  · subst h; simp
  · split_ifs with h1 h2 h2 <;> try omega
    · obtain ⟨k, rfl⟩ : ∃ k, r - (t + 1) = k := ⟨_, rfl⟩
      rw [show r - t = (r - (t + 1)) + 1 by omega]; simp
    · rfl

theorem map_range'_setFrom (ws : List (List Bool)) :
    ∀ (R : ℕ → List Bool) (t : ℕ), (List.range' t ws.length).map (setFrom R t ws) = ws := by
  induction ws with
  | nil => intro R t; rfl
  | cons w ws ih =>
      intro R t
      rw [List.length_cons, List.range'_succ, List.map_cons, ← setFrom_cons, ih]
      simp [setFrom]

/-- Clear the tracks `t, …, t + n - 1`. -/
theorem runs_clearFrom (n : ℕ) : ∀ (R : ℕ → List Bool) (t : ℕ), t + n ≤ K → ∀ (N : ℕ),
    (∀ r, (R r).length ≤ N) → (N + 3) * wd K ≤ B → ∀ i,
    Runs x B (clearFrom K t n) ⟨lay K R, 0, i⟩
      ⟨lay K (fun r => if t ≤ r ∧ r < t + n then [] else R r), 0, i⟩ := by
  induction n with
  | zero =>
      intro R t _ N _ _ i
      refine (runs_skip _ 0 i).of_eq rfl ?_
      congr 2; funext r; simp
  | succ n ih =>
      intro R t ht N hN hB i
      refine (runs_clear R t (by omega) N (hN t) hB i).seq ?_
      refine (ih (Function.update R t []) (t + 1) (by omega) N (fun r => by
        rw [Function.update_apply]; split_ifs
        · simp
        · exact hN r) hB i).of_eq rfl ?_
      congr 2; funext r
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | omega

theorem runs_compiles (gs : List Cob) (hgs : ∀ g ∈ gs, CompileOK K x B g) (as : List ℕ)
    (fr' : ℕ) (hK : fr' + Cob.needs gs ≤ K) (N N' : ℕ) (i : ℕ) :
    ∀ (t : ℕ) (R : ℕ → List Bool), (∀ a ∈ as, a < t) → t + gs.length ≤ fr' →
    (∀ r, t ≤ r → R r = []) → (∀ a ∈ as, (R a).length ≤ N) → (∀ r, (R r).length ≤ N') →
    (∀ g ∈ gs, g.spaceW N ≤ N' ∧ (g.spaceW N' + 3) * wd K ≤ B) →
    Runs x B (compiles K gs as t fr') ⟨lay K R, 0, i⟩
      ⟨lay K (setFrom R t (gs.map fun g => g.eval (as.map R))), 0, i⟩ := by
  induction gs with
  | nil =>
      intro t R _ _ _ _ _ _
      simp only [compiles, List.map_nil, setFrom_nil]
      exact runs_skip _ 0 i
  | cons g gs ih =>
      intro t R has ht hfr hNa hN hsp
      simp only [Cob.needs] at hK
      simp only [List.length_cons] at ht
      have hmap : as.map (Function.update R t (g.eval (as.map R))) = as.map R :=
        List.map_congr_left (fun a ha => Function.update_of_ne (by have := has a ha; omega) _ _)
      simp only [compiles]
      refine ((hgs g (by simp)) as t fr' R N' i (fun a ha => by have := has a ha; omega)
        (by omega) (fun h => by have := has t h; omega) (by omega)
        (fun r hr => hfr r (by omega)) hN (hsp g (by simp)).2).seq ?_
      have := ih (fun g' hg' => hgs g' (by simp [hg'])) (by omega) (t + 1)
        (Function.update R t (g.eval (as.map R))) (fun a ha => by have := has a ha; omega)
        (by omega)
        (fun r hr => by rw [Function.update_of_ne (by omega)]; exact hfr r (by omega))
        (fun a ha => by rw [Function.update_of_ne (by have := has a ha; omega)]; exact hNa a ha)
        (fun r => by
          rw [Function.update_apply]; split_ifs
          · exact le_trans (Cob.eval_length_le g _ N (fun w hw => by
              obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hw; exact hNa a ha)) (hsp g (by simp)).1
          · exact hN r)
        (fun g' hg' => hsp g' (by simp [hg']))
      rw [hmap, setFrom_cons] at this
      simpa only [List.map_cons] using this

theorem compileOK_comp (f : Cob) (gs : List Cob) (hf : CompileOK K x B f)
    (hgs : ∀ g ∈ gs, CompileOK K x B g) : CompileOK K x B (.comp f gs) := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [Cob.need] at hK
  simp only [Cob.spaceW] at hB
  simp only [compile, Cob.eval_comp]
  obtain ⟨M, hM⟩ : ∃ M, M = N + Cob.spaceWs gs N := ⟨_, rfl⟩
  rw [← hM] at hB
  have hfM := Cob.le_spaceW f M
  have hBM : (M + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  set ws := gs.map fun g => g.eval (as.map R) with hws
  have hwsl : ws.length = gs.length := by simp [ws]
  have hlen2 : ∀ r, (setFrom R fr ws r).length ≤ M := by
    intro r; simp only [setFrom]; split_ifs with h
    · rw [List.getD_eq_getElem?_getD]
      cases hw : ws[r - fr]? with
      | none => simp
      | some w =>
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hw)
          have := Cob.eval_length_le g (as.map R) N (fun w hw => by
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a)
          have := Cob.spaceWs_le gs N g hg
          simp only [Option.getD_some]; omega
    · have := hN r; omega
  refine (runs_compiles gs hgs as (fr + gs.length) (by omega) N M i fr R has (by omega) hfr
    (fun a _ => hN a) (fun r => by have := hN r; omega) (fun g hg => ⟨?_, ?_⟩)).seq ?_
  · have := Cob.spaceWs_le gs N g hg; omega
  · have h1 := Cob.spaceWs_le gs M g hg
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  refine Runs.seq (hf (List.range' fr gs.length) d (fr + gs.length) (setFrom R fr ws) M i
    (fun a ha => by rw [List.mem_range'_1] at ha; omega) (by omega)
    (fun h => by rw [List.mem_range'_1] at h; omega) (by omega)
    (fun r hr => by simp only [setFrom]; rw [if_neg (by omega)]; exact hfr r (by omega))
    hlen2 (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)) ?_
  rw [show List.range' fr gs.length = List.range' fr ws.length by rw [hwsl],
    map_range'_setFrom]
  have hwsM : ∀ w ∈ ws, w.length ≤ M := by
    intro w hw
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
    have := Cob.eval_length_le g (as.map R) N (fun w hw => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a)
    have := Cob.spaceWs_le gs N g hg
    omega
  refine (runs_clearFrom gs.length (Function.update (setFrom R fr ws) d (f.eval ws)) fr (by omega)
    (f.spaceW M) (fun r => by
    rw [Function.update_apply]; split_ifs
    · exact Cob.eval_length_le f ws M hwsM
    · have := hlen2 r; omega) (le_trans (Nat.mul_le_mul_right _ (by omega)) hB) i).of_eq rfl ?_
  congr 2; funext r
  simp only [Function.update_apply, setFrom, hwsl]
  split_ifs <;> first | rfl | omega | (symm; exact hfr r (by omega))

theorem runs_brStep (h bd : Cob) (hh : CompileOK K x B h) (hbd : CompileOK K x B bd)
    (as' : List ℕ) (fr : ℕ) (β : Bool) (R : ℕ → List Bool) (M M' : ℕ) (i : ℕ)
    (has : ∀ a ∈ as', a < fr) (hKh : fr + 6 + h.need ≤ K) (hKb : fr + 6 + bd.need ≤ K)
    (hfr : ∀ r, fr + 3 ≤ r → R r = []) (hN : ∀ r, (R r).length ≤ M)
    (hS : (R (fr + 1)).length + 1 ≤ M') (hMM' : M ≤ M') (hhM : h.spaceW M ≤ M')
    (hB1 : (h.spaceW M + 3) * wd K ≤ B) (hB2 : (bd.spaceW M' + 3) * wd K ≤ B) :
    Runs x B (brStep K fr (compile K h ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6))
      (compile K bd ((fr + 1) :: as') (fr + 4) (fr + 6)) β) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update (Function.update R (fr + 1) (β :: R (fr + 1))) (fr + 2)
        ((h.eval (R (fr + 1) :: R (fr + 2) :: as'.map R)).take
          (bd.eval ((β :: R (fr + 1)) :: as'.map R)).length)), 0, i⟩ := by
  have hM'b := Cob.le_spaceW bd M'
  have hB3 : (M' + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB2
  have hmap : ∀ (R' : ℕ → List Bool), (∀ a ∈ as', R' a = R a) → as'.map R' = as'.map R :=
    fun R' hR' => List.map_congr_left hR'
  set W := h.eval (R (fr + 1) :: R (fr + 2) :: as'.map R) with hW
  have hWl : W.length ≤ M' := le_trans (Cob.eval_length_le h _ M (fun w hw => by
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
  have h2 := runs_prepend (x := x) (B := B) R1 (fr + 1) (fr + 5) (by omega) (by omega) (by omega)
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
  set T := bd.eval ((β :: R (fr + 1)) :: as'.map R) with hT
  have hTl : T.length ≤ bd.spaceW M' := Cob.eval_length_le bd _ M' (fun w hw => by
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
  have h4 := runs_truncate (x := x) (B := B) R3 (fr + 3) (fr + 4) (by omega) (by omega) (by omega)
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
  have h5 := runs_assign (x := x) (B := B) R4 (fr + 3) (fr + 2) (by omega) (by omega) (by omega)
    _ (hR4N _) (hR4N _) hB2 i
  refine h5.seq ?_
  -- steps 6, 7
  set R5 := Function.update R4 (fr + 2) (R4 (fr + 3)) with hR5
  have hR5N : ∀ r, (R5 r).length ≤ bd.spaceW M' := by
    intro r; simp only [R5, Function.update_apply]
    split_ifs
    · exact hR4N _
    · exact hR4N r
  refine (runs_clear R5 (fr + 3) (by omega) _ (hR5N _) hB2 i).seq ?_
  refine (runs_clear (Function.update R5 (fr + 3) []) (fr + 4) (by omega) _ (by
    rw [Function.update_apply]; split_ifs
    · simp
    · exact hR5N _) hB2 i).of_eq rfl ?_
  congr 2; funext r
  simp only [R5, R4, R3, R2, R1, Function.update_apply]
  split_ifs <;> first | rfl | omega | (subst_vars; simp_all)

theorem take_getLast_eq (X : List Bool) (n : ℕ) (hn : 0 < n) (hnX : n ≤ X.length)
    (hne : X.take n ≠ []) : (X.take n).getLast hne = X[n - 1]'(by omega) := by
  rw [List.getLast_eq_getElem, List.getElem_take]
  congr 1; simp; omega

theorem compileOK_bRec (g h₀ h₁ bd : Cob) (hg : CompileOK K x B g) (hh₀ : CompileOK K x B h₀)
    (hh₁ : CompileOK K x B h₁) (hbd : CompileOK K x B bd) :
    CompileOK K x B (.bRec g h₀ h₁ bd) := by
  intro as d fr R N i has hd hne hK hfr hN hB
  simp only [Cob.need] at hK
  simp only [Cob.spaceW] at hB
  obtain ⟨M, hM⟩ : ∃ M, M = N + g.spaceW N + bd.spaceW N := ⟨_, rfl⟩
  rw [← hM] at hB
  obtain ⟨M', hM'⟩ : ∃ M', M' = M + h₀.spaceW M + h₁.spaceW M := ⟨_, rfl⟩
  rw [← hM'] at hB
  have hbM' := Cob.le_spaceW bd M'
  have hgN := Cob.le_spaceW g N
  have hB3 : (M + 3) * wd K ≤ B := le_trans (Nat.mul_le_mul_right _ (by omega)) hB
  rw [Cob.eval_bRec_headD]
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
  simp only [compile]
  refine hfirst.seq ?_
  obtain ⟨L, hL⟩ : ∃ L, L = X.length := ⟨_, rfl⟩
  let V : ℕ → List Bool := fun k => (Cob.bRec g h₀ h₁ bd).eval (X.drop (L - k) :: rest)
  let Rs : ℕ → ℕ → List Bool := fun k =>
    Function.update (Function.update (Function.update R fr (X.take (L - k))) (fr + 1)
      (X.drop (L - k))) (fr + 2) (V k)
  have hrestN : ∀ w ∈ rest, w.length ≤ N := fun w hw => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw; exact hN a
  have hVN : ∀ k, (V k).length ≤ g.spaceW N + bd.spaceW N := fun k =>
    Cob.bRec_length_le g h₀ h₁ bd rest N (Cob.eval_length_le g rest N hrestN)
      (fun y hy => Cob.eval_length_le bd _ N (fun w hw => by
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
  refine Runs.seq (t := ⟨lay K (Rs 0), 0, i⟩) (hg'.of_eq rfl ?_) ?_
  · congr 2; funext r
    simp only [Rs, V, Function.update_apply, Nat.sub_zero, hL, List.take_length,
      List.drop_length, Cob.eval_bRec_nil]
    split_ifs <;> first | rfl | omega | exact hfr r (by omega)
  refine Runs.seq (t := ⟨lay K (Rs L), 0, i⟩) ?_ ?_
  swap
  · have hRsL2 : Rs L (fr + 2) = (Cob.bRec g h₀ h₁ bd).eval (X :: rest) := by
      simp [Rs, V]
    refine (runs_assign (Rs L) (fr + 2) d (by omega) (by omega) (by omega) M (hRsN _ _)
      (hRsN _ _) hB3 i).seq ?_
    rw [hRsL2]
    have hU : ∀ r, (Function.update (Rs L) d ((Cob.bRec g h₀ h₁ bd).eval (X :: rest)) r).length
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
    simp only [R', Rs, Function.update_apply]; rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)])
  have hR'fr : ∀ r, fr + 3 ≤ r → R' r = [] := fun r hr => by
    simp only [R', Rs, Function.update_apply]; rw [if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]; exact hfr r (by omega)
  have hR'N : ∀ r, (R' r).length ≤ M := fun r => by
    simp only [R', Function.update_apply]; split_ifs
    · simp only [List.length_dropLast]; have := hRsN k fr; omega
    · exact hRsN k r
  have key : ∀ (β : Bool) (h : Cob), CompileOK K x B h → fr + 6 + h.need ≤ K →
      h.spaceW M ≤ M' → X[L - k - 1]'(by omega) = β →
      (∀ ys, (Cob.bRec g h₀ h₁ bd).eval ((β :: ys) :: rest) =
        (h.eval (ys :: (Cob.bRec g h₀ h₁ bd).eval (ys :: rest) :: rest)).take
          (bd.eval ((β :: ys) :: rest)).length) →
      Runs x B (brStep K fr (compile K h ((fr + 1) :: (fr + 2) :: as') (fr + 3) (fr + 6))
        (compile K bd ((fr + 1) :: as') (fr + 4) (fr + 6)) β) ⟨lay K R', 0, i⟩
        ⟨lay K (Rs (k + 1)), 0, i⟩ := by
    intro β h hh hKh hhM hβ hrec
    have := runs_brStep h bd hh hbd as' fr β R' M M' i has'f hKh (by omega) hR'fr hR'N
      (by rw [hR'1, List.length_drop]; omega) (by omega) hhM
      (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)
      (le_trans (Nat.mul_le_mul_right _ (by omega)) hB)
    rw [hR'1, hR'2, hR'a] at this
    refine this.of_eq rfl ?_
    have hdrop : X.drop (L - (k + 1)) = β :: X.drop (L - k) := by
      rw [List.drop_eq_getElem_cons (by omega), show L - (k + 1) + 1 = L - k by omega]
      congr 1
    have hV : V (k + 1) = (h.eval (X.drop (L - k) :: V k :: rest)).take
        (bd.eval ((β :: X.drop (L - k)) :: rest)).length := by
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
    exact key false h₀ hh₀ (by omega) (by omega) hβ (fun ys => by simp [Cob.eval_bRec_cons])
  · simp only [if_true]
    exact key true h₁ hh₁ (by omega) (by omega) hβ (fun ys => by simp [Cob.eval_bRec_cons])

mutual
/-- **Compiler correctness**, for every Cobham term. -/
theorem compileOK : ∀ c : Cob, CompileOK K x B c
  | .proj i => compileOK_proj i
  | .empty => compileOK_empty
  | .app b => compileOK_app b
  | .smash => compileOK_smash
  | .comp f gs => compileOK_comp f gs (compileOK f) (compilesOK gs)
  | .bRec g h₀ h₁ bd =>
      compileOK_bRec g h₀ h₁ bd (compileOK g) (compileOK h₀) (compileOK h₁) (compileOK bd)
theorem compilesOK : ∀ gs : List Cob, ∀ g ∈ gs, CompileOK K x B g
  | [], _, h => absurd h (by simp)
  | g :: gs, g', h => by
      rcases List.mem_cons.1 h with h1 | h1
      · rw [h1]; exact compileOK g
      · exact compilesOK gs g' h1
end

end Space
end Complexity
