/-
**Completeness of the verifier of Shamir's protocol** (towards task-board row `M21-TQBF-IN-IP`).

On the code of a true closed formula, the prover `Complexity.Shamir.honP` is accepted by
`Complexity.Shamir.shamirV` with probability `1` (`Complexity.Shamir.accProb_honP`).

The prover reads the questions asked so far off the transcript (`Complexity.Shamir.qsF`), runs
the honest strategy of sum-check on the points read so far (padded with zeros) and sends the
message of the honest run at the current round, as unary fields.  By causality
(`Complexity.Qbf.run_causal`) this is the message of the honest run on the actual points, so the
run of sum-check against the prover reading the transcript replays the honest run
(`Complexity.Qbf.run_replay`), which accepts (`Complexity.Qbf.run_honest`).
-/

import Start.ShamirSoundness

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Shamir

open Complexity.Qbf

/-! ### Reading the questions off a transcript -/

/-- The lengths of the records `0, 2, 4, …` of a transcript: the questions of the verifier. -/
def qsF : ℕ → Word → List ℕ
  | 0, _ => []
  | f + 1, t => if t = [] then [] else (recGet t).length :: qsF f (recSkip (recSkip t))

theorem recSkip_nil : recSkip [] = [] := rfl

theorem qsF_nil : ∀ f, qsF f [] = []
  | 0 => rfl
  | _ + 1 => by simp [qsF]

theorem qsF_pairsW (v : ℕ) : ∀ (L : List (Word × Word)) (f : ℕ), L.length + 1 ≤ f →
    qsF f (pairsW L ++ encMsg (un v)) = L.map (fun ab => ab.1.length) ++ [v]
  | [], f, hf => by
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      have hne : encMsg (un v) ≠ [] := by simp [encMsg]
      have e := recSkip_encMsg (un v) []
      have e2 := recGet_encMsg (un v) []
      rw [List.append_nil] at e e2
      simp [qsF, pairsW, hne, e, e2, recSkip_nil, qsF_nil]
  | ab :: L, f, hf => by
      obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
      have hne : pairsW (ab :: L) ++ encMsg (un v) ≠ [] := by simp [pairsW, encMsg]
      have e : pairsW (ab :: L) ++ encMsg (un v) =
          encMsg ab.1 ++ (encMsg ab.2 ++ (pairsW L ++ encMsg (un v))) := by
        simp [pairsW, List.append_assoc]
      rw [qsF, if_neg hne, e, recGet_encMsg, recSkip_encMsg, recSkip_encMsg,
        qsF_pairsW v L f (by simp at hf; omega)]
      simp

theorem foldl_stepT_fst (P : Prover) (M : ℕ) :
    ∀ (vs : List ℕ) (L0 : List (Word × Word)), ∃ L : List (Word × Word),
      L.map Prod.fst = L0.map Prod.fst ++ vs.map un ∧ vs.foldl (stepT P M) (pairsW L0) = pairsW L
  | [], L0 => ⟨L0, by simp, rfl⟩
  | v :: vs, L0 => by
      obtain ⟨L, hL, he⟩ := foldl_stepT_fst P M vs
        (L0 ++ [(un v, (P (pairsW L0 ++ encMsg (un v))).take M)])
      refine ⟨L, by simp [hL], ?_⟩
      rw [List.foldl_cons, ← he]
      congr 1
      simp [stepT, pairsW, List.append_assoc]

/-- **The prover reads the questions asked so far**: in round `k` it sees the questions
`vs₀, …, vs_k`. -/
theorem qsF_round (P : Prover) (M : ℕ) (vs : List ℕ) {k : ℕ} (hk : k < vs.length) :
    qsF ((vs.take k).foldl (stepT P M) [] ++ encMsg (un (vs.getD k 0))).length
      ((vs.take k).foldl (stepT P M) [] ++ encMsg (un (vs.getD k 0))) = vs.take (k + 1) := by
  obtain ⟨L, hL, he⟩ := foldl_stepT_fst P M (vs.take k) []
  rw [show ([] : Word) = pairsW [] from rfl, he]
  have hL' : L.map (fun ab => ab.1.length) = vs.take k := by
    have := congrArg (List.map List.length) hL
    simpa [List.map_map, Function.comp_def] using this
  have hlen : L.length = k := by
    have := congrArg List.length hL'
    simp only [List.length_map, List.length_take] at this
    omega
  rw [qsF_pairsW _ L _ (by
    have := length_pairsW_ge L
    simp only [List.length_append, length_encMsg]
    omega), hL', List.take_add_one, List.getElem?_eq_getElem hk]
  simp [List.getD_eq_getElem?_getD, hk]

/-! ### Lengths of honest messages -/

theorem length_fieldsWord_le_mul {p : ℕ} : ∀ l : List ℕ, (∀ a ∈ l, a < p) →
    (fieldsWord l).length ≤ l.length * p
  | [], _ => by simp [fieldsWord]
  | a :: l, h => by
      have ih := length_fieldsWord_le_mul l fun b hb => h b (List.mem_cons_of_mem a hb)
      have ha := h a (by simp)
      simp only [fieldsWord, List.length_append, List.length_replicate, List.length_cons,
        List.length_nil]
      nlinarith

theorem mem_inter {F : Type*} : ∀ (ms : List (List F)) (ρ : List F) (y : List F),
    y ∈ inter ms ρ → y ∈ ms ∨ ∃ s, y = [s]
  | m :: ms, s :: ρ, y, h => by
      simp only [inter, List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inl (by simp)
      · exact Or.inr ⟨s, rfl⟩
      · rcases mem_inter ms ρ y h with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
  | [], _, y, h => by simp [inter] at h
  | _ :: _, [], y, h => by simp [inter] at h

theorem length_honest_le {F : Type*} [Field F] [DecidableEq F] (d : ℕ) (hd : 1 ≤ d)
    (H : List (List F)) (t : Op) (a : ℕ → F) : (honest d H t a).length ≤ d + 1 := by
  unfold honest
  split
  · simp; omega
  · simp; omega
  all_goals first
    | (split <;> simp)
    | simp

/-! ### The honest prover -/

/-- **The honest prover of the interaction**: it reads the questions so far off the transcript,
runs the honest strategy of sum-check on the points read (padded with zeros to `R` points) and
sends the message of that run at the current round, as unary fields. -/
noncomputable def honP (p : ℕ) [Fact p.Prime] (d R : ℕ) (T : Op) : Prover := fun t =>
  fieldsWord (((run d (honest d) T (fun _ => (0 : ZMod p)) 1 []
    ((((qsF t.length t).tail.map fun v : ℕ => (v : ZMod p)) ++ List.replicate R 0).take R)).2.getD
      (2 * ((qsF t.length t).length - 1)) []).map ZMod.val)

theorem idxStrat_eq (p : ℕ) (msgW : ℕ → Word) (H : List (List (ZMod p))) (t : Op)
    (a : ℕ → ZMod p) :
    idxStrat p msgW H t a = (decF (msgW (H.length / 2))).map (fun z : ℕ => (z : ZMod p)) := by
  have key : ∀ l : List ℕ, List.flatMap (fun a : ℕ => [(a : ZMod p)]) l =
      l.map (fun z : ℕ => (z : ZMod p)) := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => rw [List.flatMap_cons, ih]; rfl
  simp [idxStrat, key]

theorem getD_eq_take_getD {α : Type*} (l : List α) (i : ℕ) (x : α) :
    l.getD i x = (l.take (i + 1)).getD i x := by
  simp [List.getD_eq_getElem?_getD]

section Honest

variable {p : ℕ} [Fact p.Prime]

/-- **The messages of the honest prover are those of the honest run** on the actual points. -/
theorem mW_honP {d M : ℕ} (hd : 1 ≤ d) {T : Op} (hdeg : Op.RoundDeg (ZMod p) d T)
    (htrue : (1 : ZMod p) = T.eval (fun _ => 0)) {vs : List ℕ} (hvs : ∀ v ∈ vs, v < p)
    (hR : T.rounds < vs.length) (hM : (d + 1) * p ≤ M) {k : ℕ} (hk : k < T.rounds) :
    (decF (mW (honP p d T.rounds T) M vs k)).map (fun z : ℕ => (z : ZMod p)) =
      (run d (honest d) T (fun _ => 0) 1 []
        ((vs.tail.take T.rounds).map fun v : ℕ => (v : ZMod p))).2.getD (2 * k) [] := by
  set R := T.rounds with hRdef
  have hq := qsF_round (honP p d R T) M vs (k := k) (by omega)
  have hlen : (vs.take (k + 1)).length - 1 = k := by simp; omega
  have htail : (vs.take (k + 1)).tail = vs.tail.take k := by cases vs <;> simp
  set ρk : List (ZMod p) :=
    ((vs.tail.take k).map (fun v : ℕ => (v : ZMod p)) ++ List.replicate R 0).take R with hρk
  set ρ : List (ZMod p) := (vs.tail.take R).map (fun v : ℕ => (v : ZMod p)) with hρ
  have hmsg : mW (honP p d R T) M vs k =
      (fieldsWord (((run d (honest d) T (fun _ => (0 : ZMod p)) 1 [] ρk).2.getD (2 * k) []).map
        ZMod.val)).take M := by
    simp only [mW, honP]
    rw [hq, hlen, htail]
  have hlρk : ρk.length = R := by simp [hρk]
  have hlρ : ρ.length = R := by simp [hρ]; omega
  have hacc : ∀ σ : List (ZMod p), (run d (honest d) T (fun _ => 0) 1 [] σ).1 = true :=
    fun σ => run_honest d T hdeg _ _ [] σ htrue
  have htk : ρk.take k = ρ.take k := by
    rw [hρk, hρ, List.take_take, min_eq_left hk.le, List.take_append_of_le_length (by simp; omega),
      List.take_of_length_le (by simp), ← List.map_take, List.take_take, min_eq_left hk.le]
  have hcaus := run_causal d (honest d) T (fun _ => 0) 1 [] ρk ρ k hlρk hlρ (hacc _) (hacc _) htk
  simp only [List.length_nil, zero_add] at hcaus
  have hget : (run d (honest d) T (fun _ => (0 : ZMod p)) 1 [] ρk).2.getD (2 * k) [] =
      (run d (honest d) T (fun _ => 0) 1 [] ρ).2.getD (2 * k) [] := by
    rw [getD_eq_take_getD, hcaus, ← getD_eq_take_getD]
  rw [hmsg, hget]
  set m := (run d (honest d) T (fun _ => (0 : ZMod p)) 1 [] ρ).2.getD (2 * k) [] with hm
  have hml : m.length ≤ d + 1 := by
    obtain ⟨ms, -, hms, he⟩ := run_out d (honest d) T (fun _ => 0) 1 [] ρ hlρ (hacc _)
    rw [hm, List.getD_eq_getElem?_getD]
    cases hi : (run d (honest d) T (fun _ => (0 : ZMod p)) 1 [] ρ).2[2 * k]? with
    | none => simp
    | some y =>
        have hy : y ∈ (run d (honest d) T (fun _ => (0 : ZMod p)) 1 [] ρ).2 :=
          List.mem_of_getElem? hi
        rw [he, List.nil_append] at hy
        simp only [Option.getD_some]
        rcases mem_inter ms ρ y hy with hy | ⟨s, rfl⟩
        · obtain ⟨H, n, x, rfl⟩ := hms y hy
          exact length_honest_le d hd H n x
        · simp
  have hlt : ∀ a ∈ m.map ZMod.val, a < p := by
    intro a ha
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 ha
    exact ZMod.val_lt z
  have hfl := length_fieldsWord_le_mul (m.map ZMod.val) hlt
  rw [List.take_of_length_le (by
    rw [List.length_map] at hfl
    calc _ ≤ m.length * p := hfl
      _ ≤ (d + 1) * p := Nat.mul_le_mul_right _ hml
      _ ≤ M := hM), decF_fieldsWord, List.map_map]
  conv_rhs => rw [← List.map_id m]
  apply List.map_congr_left
  intro z _
  simp

end Honest

theorem one_le_size : ∀ q : QBF, 1 ≤ q.size := by
  intro q; cases q <;> simp [QBF.size]

/-- **Completeness of the verifier of Shamir's protocol**: on the code of a true closed formula,
some prover is accepted with probability `1`. -/
theorem accProb_shamirV_complete (q : QBF) (hc : q.Closed) (ht : TQBF q) :
    ∃ P : Prover, shamirV.accProb P (QBF.enc q) = 1 := by
  obtain ⟨-, hpr, -, -⟩ := primeOf_spec (QBF.enc q)
  have : Fact (primeOf (QBF.enc q)).Prime := ⟨hpr⟩
  have hsz := QBF.size_le_length_enc q
  have h1 := one_le_size q
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
    have : R ≤ (n + 1) ^ 2 := rdsOf_le q
    omega
  have hdeg : Op.RoundDeg (ZMod p) d T :=
    (QBF.roundDeg_toOp q (QBF.varBound_le_length_enc q)).mono (by
      have : q.size ≤ n := hsz
      omega)
  have htrue : (1 : ZMod p) = T.eval (fun _ => 0) := ((QBF.tqbf_iff_toOp n hc).1 ht).symm
  have hMd : (d + 1) * p ≤ M := by
    rw [hM, maxMsg_shamirV]
    exact Nat.mul_le_mul_right _ (by omega)
  refine ⟨honP p d R T, ?_⟩
  have hall : ∀ r : List Bool, shamirV.accepts (honP p d R T) x r = true := by
    intro r
    rw [accepts_eq_run q _ r]
    set vs := bvs p kb r nb with hvs_def
    have hvs : ∀ v ∈ vs, v < p := by
      intro v hv
      simp only [hvs_def, bvs, List.mem_map] at hv
      obtain ⟨k, -, rfl⟩ := hv
      exact bv_lt x r k
    have hlen : vs.length = nb := by simp [hvs_def, bvs]
    have hRv : T.rounds < vs.length := by rw [hlen]; exact hRnb
    rw [show rdsOf q = T.rounds from rfl, pts_eq p vs hRv]
    set ρ : List (ZMod p) := (vs.tail.take T.rounds).map (fun v : ℕ => (v : ZMod p)) with hρ
    have hlρ : ρ.length = T.rounds := by simp [hρ]; omega
    set out := run d (honest d) T (fun _ => (0 : ZMod p)) 1 [] ρ with hout
    have hacc : out.1 = true := run_honest d T hdeg _ _ [] ρ htrue
    let Q' : Strat (ZMod p) := fun H n' y =>
      if Even H.length then idxStrat p (mW (honP p d R T) M vs) H n' y else out.2.getD H.length []
    have hc1 := (run_congr d (idxStrat p (mW (honP p d R T) M vs)) Q' T (fun _ => 0) 1 [] ρ []
      hlρ (by simp) (fun H n' y he _ => by simp [Q', he])).1
    have hc2 : run d Q' T (fun _ => 0) 1 [] ρ = out := by
      refine run_replay d (honest d) Q' T (fun _ => 0) 1 [] ρ hlρ hacc ?_
      intro H n' y _ hlt
      by_cases he : Even H.length
      · have hol := length_run_out d (honest d) T (fun _ => 0) 1 [] ρ hlρ hacc
        simp only [List.length_nil, zero_add] at hol
        simp only [← hout] at hlt hol
        obtain ⟨k, hk⟩ := he
        have hk2 : H.length / 2 = k := by omega
        simp only [Q', show Even H.length from ⟨k, hk⟩, if_true, idxStrat_eq, hk2]
        rw [mW_honP (by omega) hdeg htrue hvs hRv hMd (by omega)]
        rw [show H.length = 2 * k by omega]
      · simp [Q', he, hout]
    rw [hc1, hc2, hacc]
  rw [Verifier.accProb, Verifier.accCount, cntL_true _ (fun r _ => hall r)]
  simp

end Complexity.Shamir
