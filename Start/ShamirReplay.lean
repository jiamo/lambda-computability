/-
**The verifier machine replays the sum-check protocol** (task-board row `M21-SUMCHECK-REPLAY`).

`Start/ShamirMachine.lean` defines a small-step machine `Complexity.Shamir.stepW` on eight words
that walks the code `Complexity.Qbf.QBF.enc q` of a formula, generating the `N` linearizations at
each quantifier, and reads the prover's messages and the random points from a transcript of
records.  This module proves that it computes the verdict of the sum-check protocol
`Complexity.Qbf.run` of `Start/SumCheck.lean` on the linearized operator tree
`Complexity.Qbf.QBF.toOp N q`, over `ZMod p`, for the prover `Complexity.Shamir.idxStrat` that
sends the `k`-th message of the transcript at its `k`-th turn.

The proof is a simulation, node by node (`Complexity.Shamir.Replays`): started at a node with
claim `(a, v)` and the records of the node's rounds at the front of the transcript, after exactly
`size` steps the machine has either rejected and halted (when the run rejects) or arrived at the
end of the node's code, consumed its records and popped its stack (when the run accepts).

Main results:

* `Complexity.Shamir.replays_toOp` — the node-by-node simulation, for every formula with
  `varBound q ≤ N`;
* `Complexity.Shamir.sim` — **the machine replays the protocol**: from the initial state on the
  code of `q`, the claim `1` at the point `0` and an empty stack, after any number `K ≥ size
  (toOp N q)` of steps the rejection flag is empty iff the run accepts.
-/

import Start.ShamirSim

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### Words -/

theorem tr_add (msgW : ℕ → Word) (ptN : ℕ → ℕ) :
    ∀ (k a b : ℕ), tr msgW ptN k (a + b) = tr msgW ptN k a ++ tr msgW ptN (k + a) b
  | k, 0, b => by simp [tr]
  | k, a + 1, b => by
      rw [Nat.add_right_comm, tr, tr, tr_add msgW ptN (k + 1) a b]
      simp [Nat.add_right_comm, Nat.add_assoc]

theorem fieldsWord_eq_nil {l : List ℕ} : fieldsWord l = [] ↔ l = [] := by
  cases l with
  | nil => simp [fieldsWord]
  | cons a l => simp [fieldsWord]

theorem dropFs_trim_nil (w : Word) (i : ℕ) :
    dropFs i (trimW w) = [] ↔ (decF w).length ≤ i := by
  rw [← fieldsWord_decF, dropFs_fieldsWord, fieldsWord_eq_nil, List.drop_eq_nil_iff]

theorem fieldAt_trim (w : Word) (i : ℕ) : fieldAt i (trimW w) = (decF w).getD i 0 := by
  rw [← fieldsWord_decF, fieldAt_fieldsWord]

theorem pop_push (s : St) (A u S : Word) :
    pop { s with S := encMsg A ++ encMsg u ++ S } = { s with A := A, V := u, S := S } := by
  have hne : encMsg A ++ (encMsg u ++ S) ≠ [] := by simp [encMsg]
  simp only [pop, List.append_assoc]
  rw [if_neg hne]
  simp only [recGet_encMsg, recSkip_encMsg]

theorem pop_push' (C J A' V' A u S B T H : Word) :
    pop ⟨C, J, A', V', encMsg A ++ encMsg u ++ S, B, T, H⟩ = ⟨C, J, A, u, S, B, T, H⟩ := by
  have hne : encMsg A ++ (encMsg u ++ S) ≠ [] := by simp [encMsg]
  simp only [pop, List.append_assoc]
  rw [if_neg hne]
  simp only [recGet_encMsg, recSkip_encMsg]

theorem iterate_rej_eq {p N d : ℕ} (s : St) (K : ℕ) : (stepW p N d)^[K] (rej s) = rej s :=
  iterate_halted (by simp) K

/-! ### Values -/

section Arith

variable {p : ℕ} [hp : Fact p.Prime]

theorem getD_lt {a : List ℕ} (ha : ∀ x ∈ a, x < p) (i : ℕ) : a.getD i 0 < p := by
  rw [List.getD_eq_getElem?_getD]
  cases h : a[i]? with
  | none => exact p_pos
  | some x => exact ha x (List.mem_of_getElem? h)

theorem cast_mod (x : ℕ) : (((x % p : ℕ)) : ZMod p) = x := ZMod.natCast_mod x p

omit hp in
theorem set_lt {a : List ℕ} (ha : ∀ x ∈ a, x < p) (j y : ℕ) (hy : y < p) :
    ∀ x ∈ a.set j y, x < p := by
  intro x hx
  rcases List.mem_or_eq_of_mem_set hx with h | h
  · exact ha x h
  · exact h ▸ hy

end Arith

/-! ### The simulation relation -/

variable (p N d : ℕ) (msgW : ℕ → Word) (ptN : ℕ → ℕ)

/-- The outcome of processing a node of the operator tree `t` from the state `s`: if the run's
verdict is `true`, after `t.size` steps the machine has reached the code `X` and the transcript
`Tr` and popped its stack; if it is `false`, it has rejected and halted. -/
def Good (t : Op) (s : St) (X Tr : Word) (b : Bool) : Prop :=
  (b = true → ∃ (a' : List ℕ) (v' : ℕ), a'.length = N ∧ (∀ x ∈ a', x < p) ∧ v' < p ∧
      (stepW p N d)^[t.size] s =
        pop { s with C := X, J := [], A := fieldsWord a', V := un v', T := Tr }) ∧
  (b = false → ((stepW p N d)^[t.size] s).B ≠ [] ∧ ((stepW p N d)^[t.size] s).H ≠ [])

/-- **The machine replays the node `t`, whose code is `C`, when started with `j` linearizations
done**: from every state at the front of `C`, with a claim `(a, v)` and the records of the
`t.rounds` rounds of `t` at the front of the transcript, the outcome is the verdict of the run of
the protocol on `t`. -/
def Replays [Fact p.Prime] (t : Op) (C : Word) (j : ℕ) : Prop :=
  ∀ (s : St) (X : Word) (a : List ℕ) (v k : ℕ) (Tr : Word) (hist : List (List (ZMod p))),
    s.H = [] → s.C = C ++ X → s.J.length = j → s.A = fieldsWord a → a.length = N →
    (∀ x ∈ a, x < p) → s.V = un v → v < p → s.T = tr msgW ptN k t.rounds ++ Tr →
    hist.length = 2 * k →
    Good p N d t s X Tr
      (run d (idxStrat p msgW) t (toF p a) (v : ZMod p) hist (pts p ptN k t.rounds)).1

variable [hp : Fact p.Prime]

omit hp in
/-- Rejection at the first step. -/
theorem good_rej {t : Op} {s : St} {X Tr : Word} (ht : 1 ≤ t.size)
    (h : stepW p N d s = rej s) : Good p N d t s X Tr false := by
  refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le ht
  rw [hm, Nat.add_comm, Function.iterate_succ_apply, h, iterate_rej_eq]
  simp

/-! ### Variables -/

omit hp in
/-- `Good` only depends on the state reached and on the fields `S`, `B`, `H` of the start. -/
theorem good_congr {t t' : Op} {s s' : St} {X Tr : Word} {b : Bool} (h : Good p N d t' s' X Tr b)
    (hit : (stepW p N d)^[t.size] s = (stepW p N d)^[t'.size] s') (hS : s.S = s'.S)
    (hB : s.B = s'.B) (hH : s.H = s'.H) : Good p N d t s X Tr b := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨a', v', h1, h2, h3, h4⟩ := h1 hb
    refine ⟨a', v', h1, h2, h3, ?_⟩
    rw [hit, h4]
    cases s; cases s'; simp_all
  · rw [hit]; exact h2 hb

theorem replays_var (i : ℕ) : Replays p N d msgW ptN (.var i) (QBF.enc (.var i)) 0 := by
  intro s X a v k Tr hist hH hC hJ hA ha hlt hV hv hT _
  have hC' : s.C = false :: false :: (QBF.unary i ++ X) := by rw [hC]; simp [QBF.enc]
  have hstep := stepW_var (p := p) (N := N) (d := d) hH hC'
  have hJ' : s.J = [] := List.eq_nil_of_length_eq_zero hJ
  simp only [Op.rounds, tr, List.nil_append] at hT
  have hfa : fieldAt i s.A = a.getD i 0 := by rw [hA, fieldAt_fieldsWord]
  have hVl : s.V.length = v := by rw [hV, length_un]
  have key : toF p a i = (v : ZMod p) ↔ a.getD i 0 = v := cast_eq_iff (getD_lt hlt i) hv
  simp only [run, key]
  unfold Good
  simp only [Op.size, Function.iterate_one, hstep, hfa, hVl]
  refine ⟨fun hacc => ⟨a, v, ha, hlt, hv, ?_⟩, fun hrej => ?_⟩
  · rw [if_pos (of_decide_eq_true hacc)]
    congr 1; cases s; simp_all
  · rw [if_neg (of_decide_eq_false hrej)]; simp

/-! ### Negation -/

theorem replays_neg {t : Op} {C : Word} (h : Replays p N d msgW ptN t C 0) :
    Replays p N d msgW ptN (.neg t) (false :: true :: C) 0 := by
  intro s X a v k Tr hist hH hC hJ hA ha hlt hV hv hT hh
  have hC' : s.C = false :: true :: (C ++ X) := by rw [hC]; simp
  have hstep := stepW_neg (p := p) (N := N) (d := d) hH hC'
  have hVl : s.V.length = v := by rw [hV, length_un]
  rw [hVl] at hstep
  have hcast : (((fsub p 1 v : ℕ)) : ZMod p) = 1 - (v : ZMod p) := by
    rw [cast_fsub _ hv.le, Nat.cast_one]
  have := h { s with V := un (fsub p 1 v), C := C ++ X } X a (fsub p 1 v) k Tr hist hH rfl hJ hA
    ha hlt rfl (fsub_lt _ _) hT hh
  rw [hcast] at this
  show Good p N d (.neg t) s X Tr (run d (idxStrat p msgW) t (toF p a) (1 - (v : ZMod p)) hist
    (pts p ptN k t.rounds)).1
  refine good_congr p N d this ?_ rfl rfl rfl
  rw [Op.size, Function.iterate_succ_apply, hstep]

/-! ### Conjunction and disjunction -/

omit hp in
theorem iterate_bin (f : St → St) (s : St) (m n : ℕ) :
    f^[m + n + 1] s = f^[n] (f^[m] (f s)) := by
  rw [Function.iterate_succ_apply, Nat.add_comm, Function.iterate_add_apply]

theorem replays_bin_gen (b : Bool) {t u t0 : Op} {C D : Word}
    (combF : ZMod p → ZMod p → ZMod p)
    (hR : t0.rounds = t.rounds + u.rounds + 1) (hS : t0.size = t.size + u.size + 1)
    (hcomb : ∀ x y : ℕ, x < p → y < p → ((comb p b x y : ℕ) : ZMod p) = combF x y)
    (hrun2 : ∀ a v hist ρ x y, idxStrat p msgW hist t0 a = [x, y] →
      run d (idxStrat p msgW) t0 a v hist ρ =
          if combF x y = v then
            ((run d (idxStrat p msgW) t a x (hist ++ [[x, y], [ρ.headD 0]])
                (ρ.tail.take t.rounds)).1 &&
              (run d (idxStrat p msgW) u a y (run d (idxStrat p msgW) t a x
                (hist ++ [[x, y], [ρ.headD 0]]) (ρ.tail.take t.rounds)).2
                (ρ.tail.drop t.rounds)).1,
             (run d (idxStrat p msgW) u a y (run d (idxStrat p msgW) t a x
                (hist ++ [[x, y], [ρ.headD 0]]) (ρ.tail.take t.rounds)).2
                (ρ.tail.drop t.rounds)).2)
          else (false, hist))
    (hrunN : ∀ a v hist ρ, (∀ x y, idxStrat p msgW hist t0 a ≠ [x, y]) →
      run d (idxStrat p msgW) t0 a v hist ρ = (false, hist))
    (ht : Replays p N d msgW ptN t C 0) (hu : Replays p N d msgW ptN u D 0) :
    Replays p N d msgW ptN t0 (true :: false :: b :: (C ++ D)) 0 := by
  intro s X a v k Tr hist hH hC hJ hA ha hlt hV hv hT hh
  have hC' : s.C = true :: false :: b :: (C ++ (D ++ X)) := by rw [hC]; simp
  have hT' : s.T = encMsg (msgW k) ++ (encMsg (un (ptN k)) ++
      (tr msgW ptN (k + 1) t.rounds ++ (tr msgW ptN (k + 1 + t.rounds) u.rounds ++ Tr))) := by
    rw [hT, hR, tr, tr_add]; simp
  have hstep := stepW_bin (p := p) (N := N) (d := d) hH hC' hT'
  simp only [dropFs_trim_nil, fieldAt_trim, ne_eq] at hstep
  have hP : idxStrat p msgW hist t0 (toF p a) =
      (decF (msgW k)).map (fun c : ℕ => ((c : ℕ) : ZMod p)) := by
    simp only [idxStrat, hh, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    induction decF (msgW k) <;> simp_all
  have hρ : pts p ptN k t0.rounds = (ptN k : ZMod p) ::
      (pts p ptN (k + 1) t.rounds ++ pts p ptN (k + 1 + t.rounds) u.rounds) := by
    rw [hR, pts_succ, pts_add]
  have hVl : s.V.length = v := by rw [hV, length_un]
  rw [hVl] at hstep
  generalize decF (msgW k) = M at hstep hP
  rcases M with _ | ⟨x, _ | ⟨y, _ | ⟨z, M⟩⟩⟩
  · rw [hrunN _ _ _ _ (by intro x y; rw [hP]; simp)]
    simp at hstep; exact good_rej p N d (by omega) hstep
  · rw [hrunN _ _ _ _ (by intro x y; rw [hP]; simp)]
    simp at hstep; exact good_rej p N d (by omega) hstep
  swap
  · rw [hrunN _ _ _ _ (by intro x y; rw [hP]; simp)]
    simp at hstep; exact good_rej p N d (by omega) hstep
  rw [hrun2 _ _ _ _ x y (by rw [hP]; rfl), hρ]
  simp only [List.headD_cons, List.tail_cons]
  rw [List.take_left' (by simp), List.drop_left' (by simp)]
  simp only [List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
    at hstep
  have hiff : comb p b (x % p) (y % p) = v ↔ combF (x : ZMod p) y = v := by
    rw [← cast_eq_iff (comb_lt _ _ _) hv, hcomb _ _ (Nat.mod_lt _ p_pos) (Nat.mod_lt _ p_pos),
      cast_mod, cast_mod]
  by_cases hc : combF (x : ZMod p) y = v
  swap
  · rw [if_neg (by simpa using mt hiff.1 hc)] at hstep
    rw [if_neg hc]
    exact good_rej p N d (by omega) hstep
  rw [if_pos (by simpa using hiff.2 hc)] at hstep
  rw [if_pos hc]
  have IH := ht
    { s with
      C := C ++ (D ++ X), V := un (x % p)
      S := encMsg s.A ++ encMsg (un (y % p)) ++ s.S
      T := tr msgW ptN (k + 1) t.rounds ++ (tr msgW ptN (k + 1 + t.rounds) u.rounds ++ Tr) }
    (D ++ X) a (x % p) (k + 1)
    (tr msgW ptN (k + 1 + t.rounds) u.rounds ++ Tr)
    (hist ++ [[(x : ZMod p), (y : ZMod p)], [(ptN k : ZMod p)]]) hH rfl hJ hA ha hlt rfl
    (Nat.mod_lt _ p_pos) rfl (by simp [hh]; ring)
  rw [cast_mod] at IH
  generalize hr1 : run d (idxStrat p msgW) t (toF p a) (x : ZMod p)
    (hist ++ [[(x : ZMod p), (y : ZMod p)], [(ptN k : ZMod p)]])
    (pts p ptN (k + 1) t.rounds) = r1 at IH ⊢
  obtain ⟨b1, H1⟩ := r1
  cases b1 with
  | false =>
      obtain ⟨hB, hHH⟩ := IH.2 rfl
      refine ⟨fun h => by simp at h, fun _ => ?_⟩
      rw [hS, iterate_bin, hstep, iterate_halted hHH]
      exact ⟨hB, hHH⟩
  | true =>
      obtain ⟨a', v', -, -, -, hit⟩ := IH.1 rfl
      have hlen : H1.length = 2 * (k + 1 + t.rounds) := by
        have := length_run_out d (idxStrat p msgW) t (toF p a) (x : ZMod p)
          (hist ++ [[(x : ZMod p), (y : ZMod p)], [(ptN k : ZMod p)]])
          (pts p ptN (k + 1) t.rounds) (by simp) (by rw [hr1])
        rw [hr1] at this
        rw [this]; simp [hh]; ring
      have IH2 := hu
        { s with
          C := D ++ X, J := [], A := s.A, V := un (y % p), S := s.S
          T := tr msgW ptN (k + 1 + t.rounds) u.rounds ++ Tr } X a (y % p)
        (k + 1 + t.rounds) Tr H1 hH rfl rfl hA ha hlt rfl (Nat.mod_lt _ p_pos) rfl hlen
      rw [cast_mod] at IH2
      simp only [Bool.true_and]
      refine good_congr p N d IH2 ?_ rfl rfl rfl
      rw [hS, iterate_bin, hstep, hit]
      dsimp only
      rw [pop_push']

theorem replays_bin (b : Bool) {t u : Op} {C D : Word} (ht : Replays p N d msgW ptN t C 0)
    (hu : Replays p N d msgW ptN u D 0) :
    Replays p N d msgW ptN (if b then .disj t u else .conj t u) (true :: false :: b :: (C ++ D))
      0 := by
  cases b
  · show Replays p N d msgW ptN (.conj t u) (true :: false :: false :: (C ++ D)) 0
    refine replays_bin_gen p N d msgW ptN false (fun x y => x * y) rfl rfl ?_ ?_ ?_ ht hu
    · intro x y hx hy
      rw [cast_comb false hx.le hy.le]; simp
    · intro a v hist ρ x y h; rw [run_conj_def, h]
    · intro a v hist ρ h; rw [run_conj_def]; split
      · rename_i x y hxy; exact absurd hxy (h x y)
      · rfl
  · show Replays p N d msgW ptN (.disj t u) (true :: false :: true :: (C ++ D)) 0
    refine replays_bin_gen p N d msgW ptN true (fun x y => 1 - (1 - x) * (1 - y)) rfl rfl ?_ ?_
      ?_ ht hu
    · intro x y hx hy
      rw [cast_comb true hx.le hy.le]; simp
    · intro a v hist ρ x y h; rw [run_disj_def, h]
    · intro a v hist ρ h; rw [run_disj_def]; split
      · rename_i x y hxy; exact absurd hxy (h x y)
      · rfl

/-! ### Quantifiers and their linearizations -/

/-- The quantifier node `∀ x_i` (`b = false`) or `∃ x_i` (`b = true`). -/
def quantOp (b : Bool) (i : ℕ) (t : Op) : Op := if b then .ex i t else .all i t

theorem idx_map {hist : List (List (ZMod p))} {k : ℕ} (hh : hist.length = 2 * k) (t : Op)
    (a : ℕ → ZMod p) :
    idxStrat p msgW hist t a = (decF (msgW k)).map (fun c : ℕ => ((c : ℕ) : ZMod p)) := by
  simp only [idxStrat, hh, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  induction decF (msgW k) <;> simp_all

theorem length_idx_le {hist : List (List (ZMod p))} {k : ℕ} (hh : hist.length = 2 * k) (t : Op)
    (a : ℕ → ZMod p) :
    (idxStrat p msgW hist t a).length ≤ d + 1 ↔ dropFs (d + 1) (trimW (msgW k)) = [] := by
  rw [idx_map p msgW hh, List.length_map, dropFs_trim_nil]

theorem evalL_idx {hist : List (List (ZMod p))} {k : ℕ} (hh : hist.length = 2 * k) (t : Op)
    (a : ℕ → ZMod p) (x : ℕ) :
    evalL (idxStrat p msgW hist t a) (x : ZMod p) = ((hornerN x p (decF (msgW k)) : ℕ) : ZMod p) := by
  rw [idx_map p msgW hh, cast_hornerN]
  congr 1
  induction decF (msgW k) <;> simp_all

theorem evalL_idx0 {hist : List (List (ZMod p))} {k : ℕ} (hh : hist.length = 2 * k) (t : Op)
    (a : ℕ → ZMod p) :
    evalL (idxStrat p msgW hist t a) 0 = ((hornerN 0 p (decF (msgW k)) : ℕ) : ZMod p) := by
  rw [← evalL_idx p msgW hh t a 0, Nat.cast_zero]

theorem evalL_idx1 {hist : List (List (ZMod p))} {k : ℕ} (hh : hist.length = 2 * k) (t : Op)
    (a : ℕ → ZMod p) :
    evalL (idxStrat p msgW hist t a) 1 = ((hornerN 1 p (decF (msgW k)) : ℕ) : ZMod p) := by
  rw [← evalL_idx p msgW hh t a 1, Nat.cast_one]

theorem replays_quant_gen (b : Bool) {i : ℕ} (hi : i < N) {t t0 : Op} {C : Word}
    (combF : ZMod p → ZMod p → ZMod p)
    (hR : t0.rounds = t.rounds + 1) (hS : t0.size = t.size + 1)
    (hcomb : ∀ x y : ℕ, x < p → y < p → ((comb p b x y : ℕ) : ZMod p) = combF x y)
    (hrun : ∀ a v hist ρ, run d (idxStrat p msgW) t0 a v hist ρ =
      if (idxStrat p msgW hist t0 a).length ≤ d + 1 ∧
          combF (evalL (idxStrat p msgW hist t0 a) 0) (evalL (idxStrat p msgW hist t0 a) 1) = v then
        run d (idxStrat p msgW) t (Function.update a i (ρ.headD 0))
          (evalL (idxStrat p msgW hist t0 a) (ρ.headD 0))
          (hist ++ [idxStrat p msgW hist t0 a, [ρ.headD 0]]) ρ.tail
      else (false, hist))
    (ht : Replays p N d msgW ptN t C 0) :
    Replays p N d msgW ptN t0 (true :: true :: b :: (QBF.unary i ++ C)) N := by
  intro s X a v k Tr hist hH hC hJ hA ha hlt hV hv hT hh
  have hC' : s.C = true :: true :: b :: (QBF.unary i ++ (C ++ X)) := by rw [hC]; simp
  have hT' : s.T = encMsg (msgW k) ++ (encMsg (un (ptN k)) ++ (tr msgW ptN (k + 1) t.rounds ++ Tr)) := by
    rw [hT, hR, tr]; simp
  have hstep := stepW_quant (p := p) (N := N) (d := d) hH hC' hT' (by omega)
  have hVl : s.V.length = v := by rw [hV, length_un]
  rw [hVl, length_un] at hstep
  have hρ : pts p ptN k t0.rounds = (ptN k : ZMod p) :: pts p ptN (k + 1) t.rounds := by
    rw [hR, pts_succ]
  rw [hrun, hρ]
  simp only [List.headD_cons, List.tail_cons, length_idx_le p d msgW hh, evalL_idx0 p msgW hh,
    evalL_idx1 p msgW hh]
  have hiff : comb p b (hornerN 0 p (decF (msgW k))) (hornerN 1 p (decF (msgW k))) = v ↔
      combF ((hornerN 0 p (decF (msgW k)) : ℕ) : ZMod p) ((hornerN 1 p (decF (msgW k)) : ℕ) : ZMod p)
        = v := by
    rw [← cast_eq_iff (comb_lt _ _ _) hv, hcomb _ _ (hornerN_lt _ _) (hornerN_lt _ _)]
  by_cases hc : dropFs (d + 1) (trimW (msgW k)) = [] ∧
      combF ((hornerN 0 p (decF (msgW k)) : ℕ) : ZMod p) ((hornerN 1 p (decF (msgW k)) : ℕ) : ZMod p)
        = v
  swap
  · rw [if_neg (by rwa [hiff])] at hstep
    rw [if_neg hc]
    exact good_rej p N d (by omega) hstep
  rw [if_pos (by rwa [hiff])] at hstep
  rw [if_pos hc]
  have hA' : setField i (ptN k % p) s.A = fieldsWord (a.set i (ptN k % p)) := by
    rw [hA, setField_fieldsWord _ (by omega)]
  have IH := ht
    { s with
      C := C ++ X, J := [], A := setField i (ptN k % p) s.A
      V := un (hornerN (ptN k % p) p (decF (msgW k)))
      T := tr msgW ptN (k + 1) t.rounds ++ Tr }
    X (a.set i (ptN k % p)) (hornerN (ptN k % p) p (decF (msgW k))) (k + 1) Tr
    (hist ++ [idxStrat p msgW hist t0 (toF p a), [(ptN k : ZMod p)]]) hH rfl rfl hA'
    (by simp [ha]) (set_lt hlt _ _ (Nat.mod_lt _ p_pos)) rfl (hornerN_lt _ _) rfl
    (by simp [hh]; ring)
  rw [toF_set (by omega), ← evalL_idx p msgW hh t0 (toF p a)] at IH
  simp only [cast_mod] at IH
  refine good_congr p N d IH ?_ rfl rfl rfl
  rw [hS, Function.iterate_succ_apply, hstep]

theorem replays_quant (b : Bool) {i : ℕ} (hi : i < N) {t : Op} {C : Word}
    (ht : Replays p N d msgW ptN t C 0) :
    Replays p N d msgW ptN (quantOp b i t) (true :: true :: b :: (QBF.unary i ++ C)) N := by
  cases b
  · refine replays_quant_gen p N d msgW ptN false hi (fun x y => x * y) rfl rfl ?_ ?_ ht
    · intro x y hx hy
      rw [cast_comb false hx.le hy.le]; simp
    · intro a v hist ρ; rw [quantOp, if_neg Bool.false_ne_true, run_all_def]
  · refine replays_quant_gen p N d msgW ptN true hi (fun x y => 1 - (1 - x) * (1 - y)) rfl rfl ?_
      ?_ ht
    · intro x y hx hy
      rw [cast_comb true hx.le hy.le]; simp
    · intro a v hist ρ; rw [quantOp, if_pos rfl, run_ex_def]

theorem replays_lin {b : Bool} {i j : ℕ} (hj : j < N) {t : Op} {C : Word}
    (ht : Replays p N d msgW ptN t (true :: true :: b :: (QBF.unary i ++ C)) (j + 1)) :
    Replays p N d msgW ptN (.lin j t) (true :: true :: b :: (QBF.unary i ++ C)) j := by
  intro s X a v k Tr hist hH hC hJ hA ha hlt hV hv hT hh
  have hC' : s.C = true :: true :: b :: (QBF.unary i ++ C ++ X) := by rw [hC]; simp
  have hT' : s.T = encMsg (msgW k) ++ (encMsg (un (ptN k)) ++ (tr msgW ptN (k + 1) t.rounds ++ Tr)) := by
    rw [hT, Op.rounds, tr]; simp
  have hstep := stepW_lin (p := p) (N := N) (d := d) hH hC' hT' (by omega)
  have hVl : s.V.length = v := by rw [hV, length_un]
  have hfa : fieldAt s.J.length s.A = a.getD j 0 := by rw [hA, fieldAt_fieldsWord, hJ]
  rw [hVl, length_un, hfa] at hstep
  rw [hJ] at hstep
  have hρ : pts p ptN k (Op.lin j t).rounds = (ptN k : ZMod p) :: pts p ptN (k + 1) t.rounds := by
    rw [Op.rounds, pts_succ]
  rw [run_lin_def, hρ]
  simp only [List.headD_cons, List.tail_cons, length_idx_le p d msgW hh, evalL_idx0 p msgW hh,
    evalL_idx1 p msgW hh]
  have hgl := getD_lt hlt j
  have hiff : fadd p (fmul p (a.getD j 0) (hornerN 1 p (decF (msgW k))))
        (fmul p (fsub p 1 (a.getD j 0)) (hornerN 0 p (decF (msgW k)))) = v ↔
      toF p a j * ((hornerN 1 p (decF (msgW k)) : ℕ) : ZMod p) +
        (1 - toF p a j) * ((hornerN 0 p (decF (msgW k)) : ℕ) : ZMod p) = v := by
    rw [← cast_eq_iff (fadd_lt _ _) hv, cast_fadd, cast_fmul, cast_fmul, cast_fsub _ hgl.le]
    simp [toF]
  by_cases hc : dropFs (d + 1) (trimW (msgW k)) = [] ∧
      toF p a j * ((hornerN 1 p (decF (msgW k)) : ℕ) : ZMod p) +
        (1 - toF p a j) * ((hornerN 0 p (decF (msgW k)) : ℕ) : ZMod p) = v
  swap
  · rw [if_neg (by rwa [hiff])] at hstep
    rw [if_neg hc]
    exact good_rej p N d (by simp [Op.size]) hstep
  rw [if_pos (by rwa [hiff])] at hstep
  rw [if_pos hc]
  have hA' : setField j (ptN k % p) s.A = fieldsWord (a.set j (ptN k % p)) := by
    rw [hA, setField_fieldsWord _ (by omega)]
  have IH := ht
    { s with
      J := true :: s.J, A := setField j (ptN k % p) s.A
      V := un (hornerN (ptN k % p) p (decF (msgW k)))
      T := tr msgW ptN (k + 1) t.rounds ++ Tr }
    X (a.set j (ptN k % p)) (hornerN (ptN k % p) p (decF (msgW k))) (k + 1) Tr
    (hist ++ [idxStrat p msgW hist (.lin j t) (toF p a), [(ptN k : ZMod p)]]) hH hC
    (by simp [hJ]) hA' (by simp [ha]) (set_lt hlt _ _ (Nat.mod_lt _ p_pos)) rfl (hornerN_lt _ _)
    rfl (by simp [hh]; ring)
  rw [toF_set (by omega), ← evalL_idx p msgW hh (.lin j t) (toF p a)] at IH
  simp only [cast_mod] at IH
  refine good_congr p N d IH ?_ rfl rfl rfl
  rw [Op.size, Function.iterate_succ_apply, hstep]

theorem replays_linAll (b : Bool) {i : ℕ} (hi : i < N) {t : Op} {C : Word}
    (ht : Replays p N d msgW ptN t C 0) :
    ∀ m j, j + m = N → Replays p N d msgW ptN (Op.linAll (List.range' j m) (quantOp b i t))
      (true :: true :: b :: (QBF.unary i ++ C)) j
  | 0, j, h => by
      rw [show j = N by omega]
      exact replays_quant p N d msgW ptN b hi ht
  | m + 1, j, h => by
      rw [List.range'_succ, Op.linAll]
      exact replays_lin p N d msgW ptN (by omega)
        (replays_linAll b hi ht m (j + 1) (by omega))

/-! ### Formulas -/

theorem replays_toOp : ∀ q : QBF, q.varBound ≤ N →
    Replays p N d msgW ptN (QBF.toOp N q) (QBF.enc q) 0
  | .var i, _ => replays_var p N d msgW ptN i
  | .neg q, h => replays_neg p N d msgW ptN (replays_toOp q h)
  | .conj q r, h => by
      simp only [QBF.varBound, max_le_iff] at h
      show Replays p N d msgW ptN (.conj (QBF.toOp N q) (QBF.toOp N r))
        (true :: false :: false :: (QBF.enc q ++ QBF.enc r)) 0
      exact replays_bin p N d msgW ptN false (replays_toOp q h.1) (replays_toOp r h.2)
  | .disj q r, h => by
      simp only [QBF.varBound, max_le_iff] at h
      show Replays p N d msgW ptN (.disj (QBF.toOp N q) (QBF.toOp N r))
        (true :: false :: true :: (QBF.enc q ++ QBF.enc r)) 0
      exact replays_bin p N d msgW ptN true (replays_toOp q h.1) (replays_toOp r h.2)
  | .all i q, h => by
      simp only [QBF.varBound, max_le_iff] at h
      have := replays_linAll p N d msgW ptN false (Nat.lt_of_succ_le h.1) (replays_toOp q h.2) N 0
        (by omega)
      simpa [QBF.toOp, QBF.enc, List.range_eq_range', quantOp] using this
  | .ex i q, h => by
      simp only [QBF.varBound, max_le_iff] at h
      have := replays_linAll p N d msgW ptN true (Nat.lt_of_succ_le h.1) (replays_toOp q h.2) N 0
        (by omega)
      simpa [QBF.toOp, QBF.enc, List.range_eq_range', quantOp] using this

/-! ### The whole run -/

/-- The initial state of the verifier on the code of `q`: the claim `1` at the point `0` (with `N`
coordinates), an empty stack, and the transcript `T`. -/
def initSt (N : ℕ) (C T : Word) : St :=
  ⟨C, [], fieldsWord (List.replicate N 0), un 1, [], [], T, []⟩

/-- **The verifier machine replays the sum-check protocol.**  On the code of a formula `q` with
`varBound q ≤ N`, a transcript of messages `msgW k` and points `ptN k` (followed by anything), and
after any number `K ≥ size (toOp N q)` of steps, the rejection flag of the machine is empty exactly
when the protocol run on the claim `toOp N q = 1` at the point `0`, with the prover reading its
messages off the transcript, accepts. -/
theorem sim {q : QBF} (hq : q.varBound ≤ N) {K : ℕ} (hK : (QBF.toOp N q).size ≤ K) (Tr : Word) :
    ((stepW p N d)^[K] (initSt N (QBF.enc q)
        (tr msgW ptN 0 (QBF.toOp N q).rounds ++ Tr))).B = [] ↔
      (run d (idxStrat p msgW) (QBF.toOp N q) (fun _ => (0 : ZMod p)) 1 []
        (pts p ptN 0 (QBF.toOp N q).rounds)).1 = true := by
  have h1p : 1 < p := hp.out.one_lt
  have hR := replays_toOp p N d msgW ptN q hq (initSt N (QBF.enc q)
    (tr msgW ptN 0 (QBF.toOp N q).rounds ++ Tr)) [] (List.replicate N 0) 1 0 Tr []
    rfl (by simp [initSt]) rfl rfl (by simp) (by simp; omega) rfl h1p rfl rfl
  have hF : toF p (List.replicate N 0) = fun _ => (0 : ZMod p) := by
    funext j; simp [toF, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> simp
  rw [hF, Nat.cast_one] at hR
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [Nat.add_comm, Function.iterate_add_apply]
  generalize hr : (run d (idxStrat p msgW) (QBF.toOp N q) (fun _ => (0 : ZMod p)) 1 []
    (pts p ptN 0 (QBF.toOp N q).rounds)).1 = r at hR
  cases r with
  | true =>
      obtain ⟨a', v', -, -, -, hit⟩ := hR.1 rfl
      rw [hit]
      have hpop : pop { initSt N (QBF.enc q) (tr msgW ptN 0 (QBF.toOp N q).rounds ++ Tr) with
          C := [], J := [], A := fieldsWord a', V := un v', T := Tr } =
          ⟨[], [], fieldsWord a', un v', [], [], Tr, [true]⟩ := by
        simp [pop, initSt]
      rw [hpop, iterate_halted (by simp)]
      simp
  | false =>
      obtain ⟨hB, hH⟩ := hR.2 rfl
      rw [iterate_halted hH]
      simpa using hB

end Complexity.Shamir
