/-
**Soundness of the verifier of Shamir's protocol** (towards task-board row `M21-TQBF-IN-IP`).

On the code of a false closed formula, every prover is accepted by
`Complexity.Shamir.shamirV` with probability at most `1/3`
(`Complexity.Shamir.accProb_shamirV_le`).

The proof: by `Complexity.Shamir.accepts_eq_run` the verdict on coins `r` is the verdict of a
sum-check run against the prover reading the transcript; since the `k`-th message of the prover
only depends on the questions asked so far, the run is the run against a strategy that depends on
the history (`Complexity.Shamir.SS`, `Complexity.Qbf.run_congr`), up to the first, unused, coin
block.  The probability over the coin words is at most twice the probability over field elements
(`Complexity.cntL_blocks_le`), the unused points are summed out, and sum-check soundness
(`Complexity.Qbf.cntL_run_false`) bounds the rest by `2 · d · rounds / p ≤ 1/3`.
-/

import Start.ShamirSound
import Start.CoinDecode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### Histories and prefixes -/

theorem length_ptsOf {F : Type*} [Field F] :
    ∀ H : List (List F), Even H.length → (ptsOf H).length = H.length / 2
  | [], _ => by simp [ptsOf]
  | [_], h => by simp at h
  | _ :: _ :: H, h => by
      have ih := length_ptsOf H (by simpa [Nat.even_add_one] using h)
      simp only [ptsOf, List.length_cons, ih]
      omega

theorem mW_congr (P : Prover) (M : ℕ) {vs ws : List ℕ} {k : ℕ}
    (h : vs.take (k + 1) = ws.take (k + 1)) : mW P M vs k = mW P M ws k := by
  have h1 : vs.take k = ws.take k := by
    have := congrArg (List.take k) h
    simpa [List.take_take] using this
  have h2 : vs.getD k 0 = ws.getD k 0 := by
    have e : ∀ l : List ℕ, l.getD k 0 = (l.take (k + 1)).getD k 0 := by
      intro l
      simp [List.getD_eq_getElem?_getD]
    rw [e vs, e ws, h]
  simp only [mW, h1, h2]

/-- The points `vs₁, …, vs_R`, as the points of a sum-check run. -/
theorem pts_eq (p : ℕ) (vs : List ℕ) {R : ℕ} (hR : R < vs.length) :
    pts p (fun j => vs.getD (j + 1) 0) 0 R = (vs.tail.take R).map fun v : ℕ => (v : ZMod p) := by
  apply List.ext_getElem
  · simp [pts]; omega
  · intro i h1 h2
    have hi : i + 1 < vs.length := by simp [pts] at h1; omega
    rw [List.getElem_map, List.getElem_take, List.getElem_tail]
    simp only [pts, List.getElem_map, List.getElem_range']
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

section Strategy

variable {p : ℕ} [Fact p.Prime]

/-- **The prover as a strategy of the sum-check game**, given the first question `c`: at a
history with `k` points it sends the `k`-th message of the interaction whose questions are `c`
followed by the points. -/
def SS (P : Prover) (M c : ℕ) : Strat (ZMod p) := fun H _ _ =>
  (decF (mW P M (c :: (ptsOf H).map ZMod.val) (H.length / 2))).map fun z => (z : ZMod p)

theorem run_idx_eq (P : Prover) (M d : ℕ) (T : Op) (vs : List ℕ) (hvs : ∀ v ∈ vs, v < p)
    (hR : T.rounds < vs.length) :
    (run d (idxStrat p (mW P M vs)) T (fun _ => 0) 1 []
        (pts p (fun j => vs.getD (j + 1) 0) 0 T.rounds)).1 =
      (run d (SS P M (vs.headD 0)) T (fun _ => 0) 1 []
        ((vs.tail.take T.rounds).map fun v : ℕ => (v : ZMod p))).1 := by
  rw [pts_eq p vs hR]
  obtain ⟨c, ws, rfl⟩ : ∃ c ws, vs = c :: ws := List.exists_cons_of_length_pos (by omega)
  refine (run_congr d _ _ T _ _ [] _ ((ws.drop T.rounds).map fun v : ℕ => (v : ZMod p))
    (by simp at hR ⊢; omega) (by simp) ?_).1
  intro H n x he hpre
  simp only [idxStrat, SS]
  congr 2
  simp only [List.headD_cons]
  congr 1
  apply mW_congr
  have hk := length_ptsOf H he
  simp only [ptsOf, List.nil_append, List.tail_cons, ← List.map_append,
    List.take_append_drop] at hpre
  rw [List.prefix_iff_eq_take] at hpre
  rw [hpre, hk]
  have hws : ∀ v ∈ ws, v < p := fun v hv => hvs v (List.mem_cons_of_mem c hv)
  have : ((List.map (fun v : ℕ => (v : ZMod p)) ws).take (H.length / 2)).map ZMod.val =
      ws.take (H.length / 2) := by
    rw [← List.map_take, List.map_map]
    conv_rhs => rw [← List.map_id (ws.take (H.length / 2))]
    apply List.map_congr_left
    intro v hv
    exact ZMod.val_cast_of_lt (hws v (List.mem_of_mem_take hv))
  rw [this]
  simp [List.take_succ_cons]

end Strategy

/-! ### Counting -/

theorem blocks_eq_bvs (p kb : ℕ) : ∀ (n : ℕ) (r : Word), blocks p kb n r = bvs p kb r n
  | 0, r => rfl
  | n + 1, r => by
      rw [blocks, blocks_eq_bvs p kb n (r.drop kb), bvs, bvs, List.range_succ_eq_map,
        List.map_cons, List.map_map]
      simp only [bv, mul_zero, List.drop_zero, List.cons.injEq,
        true_and]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp, bv, List.drop_drop]
      rw [show kb * k.succ = kb + kb * k by rw [Nat.mul_succ, Nat.add_comm]]

theorem cntL_cons_take {p : ℕ} [NeZero p] (R m : ℕ) (G : ZMod p → List (ZMod p) → Bool) :
    cntL (R + m + 1) (fun l => G (l.headD 0) (l.tail.take R)) =
      ∑ c : ZMod p, cntL R (G c) * p ^ m := by
  rw [cntL_succ]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [List.headD_cons, List.tail_cons]
  unfold cntL
  rw [sumL_append, sumL_congr (g := fun ρ₁ => p ^ m * (if G c ρ₁ then 1 else 0)), sumL_mul_left,
    mul_comm]
  intro ρ₁ hρ₁
  have e : ∀ ρ₂ : List (ZMod p), (ρ₁ ++ ρ₂).take R = ρ₁ := fun ρ₂ => by
    rw [← hρ₁]; exact List.take_left' rfl
  simp only [e, sumL_const, ZMod.card]

/-- `96 m⁵ ≤ 2 ^ (8 m)`: the coin blocks are long enough. -/
theorem pow_five_le (m : ℕ) (hm : 1 ≤ m) : 96 * m ^ 5 ≤ 2 ^ (8 * m) := by
  induction m with
  | zero => omega
  | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hm'
      · norm_num
      · have ih := ih hm'
        have h2 : (m + 1) ^ 5 ≤ 32 * m ^ 5 := by
          have : m + 1 ≤ 2 * m := by omega
          calc (m + 1) ^ 5 ≤ (2 * m) ^ 5 := Nat.pow_le_pow_left this 5
            _ = 32 * m ^ 5 := by ring
        rw [show 8 * (m + 1) = 8 * m + 8 by ring, pow_add]
        have : (2 : ℕ) ^ 8 = 256 := by norm_num
        rw [this]
        calc 96 * (m + 1) ^ 5 ≤ 96 * (32 * m ^ 5) := by gcongr
          _ = 32 * (96 * m ^ 5) := by ring
          _ ≤ 32 * 2 ^ (8 * m) := by gcongr
          _ ≤ 2 ^ (8 * m) * 256 := by omega

/-! ### Soundness -/

theorem rdsOf_le_mul (q : QBF) :
    rdsOf q ≤ ((QBF.enc q).length + 1) * (QBF.enc q).length := by
  have h1 := QBF.size_toOp (QBF.enc q).length q
  have h2 := QBF.size_le_length_enc q
  have h3 := Op.rounds_le_size (QBF.toOp (QBF.enc q).length q)
  calc rdsOf q ≤ ((QBF.enc q).length + 1) * q.size := h3.trans h1
    _ ≤ _ := by gcongr

/-- **Soundness of the verifier of Shamir's protocol**: on the code of a false closed formula,
every prover is accepted with probability at most `1/3`. -/
theorem accProb_shamirV_le (q : QBF) (hc : q.Closed) (hf : ¬ TQBF q) (P : Prover) :
    shamirV.accProb P (QBF.enc q) ≤ 1 / 3 := by
  obtain ⟨-, hpr, hp1, hp2⟩ := primeOf_spec (QBF.enc q)
  have : Fact (primeOf (QBF.enc q)).Prime := ⟨hpr⟩
  have hRle := rdsOf_le_mul q
  set x := QBF.enc q with hx
  set n := x.length with hn
  set p := primeOf x with hpdef
  set kb := 8 * (n + 1) with hkb
  set nb := (n + 1) ^ 2 + 1 with hnb
  set R := rdsOf q with hR
  set M := shamirV.maxMsg x with hM
  set d := 2 * n with hd
  set T := QBF.toOp n q with hT
  have hRnb : R < nb := by
    have : R ≤ (n + 1) ^ 2 := by nlinarith
    omega
  let E : List (ZMod p) → Bool := fun l =>
    (run d (SS (p := p) P M (l.headD 0).val) T (fun _ => 0) 1 [] (l.tail.take R)).1
  have hacc : shamirV.accCount P x =
      cntL (nb * kb) (fun r => E ((blocks p kb nb r).map fun v : ℕ => (v : ZMod p))) := by
    rw [Verifier.accCount, numCoins_shamirV]
    congr 1
    funext r
    rw [accepts_eq_run q P r]
    have hvs : ∀ v ∈ bvs p kb r nb, v < p := by
      intro v hv
      simp only [bvs, List.mem_map] at hv
      obtain ⟨k, -, rfl⟩ := hv
      exact bv_lt x r k
    have hlen : (bvs p kb r nb).length = nb := by simp [bvs]
    rw [run_idx_eq P M d T _ hvs (by rw [hlen]; exact hRnb), blocks_eq_bvs]
    obtain ⟨c, ws, hcw⟩ : ∃ c ws, bvs p kb r nb = c :: ws :=
      List.exists_cons_of_length_pos (by omega)
    have hc' : c < p := hvs c (by rw [hcw]; simp)
    simp only [E, hcw, List.headD_cons, List.map_cons, List.tail_cons, ZMod.val_cast_of_lt hc',
      List.map_take]
    rfl
  have hK : 2 * nb * p ≤ 2 ^ kb := by
    have h5 := pow_five_le (n + 1) (by omega)
    have h1 : nb ≤ 2 * (n + 1) ^ 2 := by
      have : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
      omega
    calc 2 * nb * p ≤ 2 * (2 * (n + 1) ^ 2) * (2 * (12 * (n + 1) ^ 3)) := by gcongr
      _ = 96 * (n + 1) ^ 5 := by ring
      _ ≤ _ := h5
  have hblk := cntL_blocks_le hpr.pos kb nb hK E
  obtain ⟨m, hm⟩ : ∃ m, nb = R + m + 1 := ⟨nb - 1 - R, by omega⟩
  have hcnt : cntL nb E * p ≤ d * R * p ^ nb := by
    have hdeg : Op.RoundDeg (ZMod p) d T :=
      (QBF.roundDeg_toOp q (QBF.varBound_le_length_enc q)).mono
        (by have : q.size ≤ n := QBF.size_le_length_enc q
            omega)
    have hv : (1 : ZMod p) ≠ T.eval (fun _ => 0) := fun h1 =>
      hf ((QBF.tqbf_iff_toOp n hc).2 h1.symm)
    have hb : ∀ c : ZMod p,
        cntL R (fun ρ => (run d (SS (p := p) P M c.val) T (fun _ => 0) 1 [] ρ).1) * p ≤ d * R * p ^ R := by
      intro c
      have := cntL_run_false d T hdeg (SS (p := p) P M c.val) (fun _ => 0) 1 [] hv
      simpa [ZMod.card] using this
    have hE : cntL nb E = cntL (R + m + 1) (fun l =>
        (fun (c : ZMod p) ρ => (run d (SS (p := p) P M c.val) T (fun _ => 0) 1 [] ρ).1)
          (l.headD 0) (l.tail.take R)) := by rw [hm]
    rw [hE, cntL_cons_take (p := p) R m
      (fun (c : ZMod p) ρ => (run d (SS (p := p) P M c.val) T (fun _ => 0) 1 [] ρ).1),
      Finset.sum_mul]
    calc ∑ c : ZMod p, cntL R (fun ρ => (run d (SS (p := p) P M c.val) T (fun _ => 0) 1 [] ρ).1) *
          p ^ m * p
        = ∑ c : ZMod p, (cntL R (fun ρ => (run d (SS (p := p) P M c.val) T (fun _ => 0) 1 [] ρ).1) * p) *
          p ^ m := Finset.sum_congr rfl fun c _ => by ring
      _ ≤ ∑ _c : ZMod p, (d * R * p ^ R) * p ^ m :=
          Finset.sum_le_sum fun c _ => Nat.mul_le_mul_right _ (hb c)
      _ = d * R * p ^ nb := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, hm]
          ring
  have h6 : 6 * d * R ≤ p := by
    have : 6 * d * R ≤ 12 * (n + 1) ^ 3 := by
      calc 6 * d * R ≤ 6 * (2 * n) * ((n + 1) * n) := by gcongr
        _ ≤ 12 * (n + 1) ^ 3 := by nlinarith
    omega
  have hpq : (0 : ℚ) < p := by exact_mod_cast hpr.pos
  rw [Verifier.accProb, hacc, numCoins_shamirV]
  have hcq : (cntL nb E : ℚ) / (p : ℚ) ^ nb ≤ d * R / p := by
    rw [div_le_div_iff₀ (by positivity) hpq]
    have : ((cntL nb E * p : ℕ) : ℚ) ≤ ((d * R * p ^ nb : ℕ) : ℚ) := by exact_mod_cast hcnt
    push_cast at this
    linarith
  have h6q : (6 * d * R : ℚ) ≤ p := by exact_mod_cast h6
  calc _ ≤ 2 * ((cntL nb E : ℚ) / (p : ℚ) ^ nb) := hblk
    _ ≤ 2 * (d * R / p) := by gcongr
    _ ≤ 1 / 3 := by
        rw [mul_div_assoc', div_le_div_iff₀ hpq (by norm_num)]
        linarith

end Complexity.Shamir
