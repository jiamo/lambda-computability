import Start.SpaceProgTracks

/-!
# Binary counters on the track layout, and moving the input head to a counted position

This library's own extension of `Start/SpaceProgTracks.lean` (task `M27-LOGSPACE-TRANSFER`,
reverse direction).  It adds to the register operations of tape programs:

* `Tracks.ifNE` — branch on whether a register is empty;
* induction-friendly rules for `Tracks.whileNE` in which the input head may move
  (`Tracks.WL`, `Tracks.runs_whileNE_of_wl`);
* counters in *bijective base two* (digits `1 ↦ false`, `2 ↦ true`, most significant first), for
  which the value `0` is exactly the empty word: `Tracks.bval`, with `Tracks.bincr`/`Tracks.bdecr`
  and their tape programs `Tracks.incr`/`Tracks.decr` (using a carry register and a flag
  register); a counter of value `v` occupies `⌊log₂ (v + 1)⌋` cells (`Tracks.two_pow_length_le`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Space

namespace Tracks

open Prog

variable {x : List Bool} {B : ℕ} {K : ℕ}

/-! ### Branching on emptiness -/

/-- Run `p` if register `j` is non-empty and `q` otherwise (home to home). -/
def ifNE (j : ℕ) (p q : Prog) : Prog :=
  .seq (mvR (2 * j + 1)) (.ite (fun _ w => w) (.seq (mvL (2 * j + 1)) p)
    (.seq (mvL (2 * j + 1)) q))

theorem runs_ifNE (R : ℕ → List Bool) (j : ℕ) (hj : j < K) (hB : wd K < B) (i : ℕ)
    (p q : Prog) (s' : TState)
    (hp : R j ≠ [] → Runs x B p ⟨lay K R, 0, i⟩ s')
    (hq : R j = [] → Runs x B q ⟨lay K R, 0, i⟩ s') :
    Runs x B (ifNE j p q) ⟨lay K R, 0, i⟩ s' := by
  refine (runs_mvR _ _ 0 i (by womega)).seq ?_
  have hpres := lay_pres R j hj 0
  simp only [zero_mul, zero_add] at hpres
  refine Runs.ite (fun ht => ?_) (fun ht => ?_)
  · have hne : R j ≠ [] := by
      intro h; simp only [zero_add] at ht; rw [hpres, h] at ht; simp at ht
    exact ((runs_mvL _ _ _ i).of_eq rfl (by simp)).seq (hp hne)
  · have he : R j = [] := by
      simp only [zero_add] at ht; rw [hpres] at ht
      simpa [List.length_pos_iff] using ht
    exact ((runs_mvL _ _ _ i).of_eq rfl (by simp)).seq (hq he)

/-! ### Loops, one iteration at a time -/

theorem Runs.loop_unroll {t : Test} {body : Prog} {s s₁ u : TState}
    (ht : t x[s.inHead]? (s.view s.head) = true) (hb : Runs x B body s s₁)
    (hl : Runs x B (.loop t body) s₁ u) : Runs x B (.loop t body) s u := by
  intro c hc hB
  subst hc
  obtain ⟨d, hd, hds, hdB⟩ := hb (touch x c) (abs_touch x c) (by rw [space_touch]; exact hB)
  obtain ⟨e, he, hes, heB⟩ := hl d hds hdB
  exact ⟨e, .loopT hB ht hd he, hes, heB⟩

theorem Runs.loop_stop {t : Test} {body : Prog} {s : TState}
    (ht : t x[s.inHead]? (s.view s.head) = false) : Runs x B (.loop t body) s s := by
  intro c hc hB
  subst hc
  exact ⟨touch x c, .loopF hB ht, abs_touch x c, by rw [space_touch]; exact hB⟩

/-- The inner loop of `whileNE`, between two register files and input-head positions. -/
def WL (x : List Bool) (B K j : ℕ) (body : Prog) (R : ℕ → List Bool) (i : ℕ)
    (R' : ℕ → List Bool) (i' : ℕ) : Prop :=
  Runs x B (.loop (fun _ w => w) (.seq (mvL (2 * j + 1)) (.seq body (mvR (2 * j + 1)))))
    ⟨lay K R, 2 * j + 1, i⟩ ⟨lay K R', 2 * j + 1, i'⟩

theorem wl_stop {j : ℕ} (hj : j < K) {body : Prog} (R : ℕ → List Bool) (i : ℕ) (h : R j = []) :
    WL x B K j body R i R i := by
  apply Runs.loop_stop
  have hpres := lay_pres R j hj 0
  simp only [zero_mul, zero_add] at hpres
  simp only [hpres, h, List.length_nil, lt_self_iff_false, decide_false]

theorem wl_step {j : ℕ} (hj : j < K) (hB : wd K < B) {body : Prog} (R R₁ R' : ℕ → List Bool)
    (i i₁ i' : ℕ) (hne : R j ≠ []) (hb : Runs x B body ⟨lay K R, 0, i⟩ ⟨lay K R₁, 0, i₁⟩)
    (hl : WL x B K j body R₁ i₁ R' i') : WL x B K j body R i R' i' := by
  refine Runs.loop_unroll ?_ ?_ hl
  · have hpres := lay_pres R j hj 0
    simp only [zero_mul, zero_add] at hpres
    simp only [hpres, List.length_pos_of_ne_nil hne, decide_true]
  · refine ((runs_mvL _ _ _ i).of_eq rfl (by simp)).seq (hb.seq ?_)
    exact (runs_mvR _ _ 0 i₁ (by womega)).of_eq rfl (by simp)

theorem runs_whileNE_of_wl {j : ℕ} (hj : j < K) (hB : wd K < B) {body : Prog}
    {R R' : ℕ → List Bool} {i i' : ℕ} (h : WL x B K j body R i R' i') :
    Runs x B (whileNE j body) ⟨lay K R, 0, i⟩ ⟨lay K R', 0, i'⟩ := by
  refine (runs_mvR _ _ 0 i (by womega)).seq ?_
  refine Runs.seq (h.of_eq (by simp) rfl) ?_
  exact (runs_mvL _ _ _ i').of_eq rfl (by simp)

/-! ### Bijective base-two numerals -/

/-- The value of a numeral in bijective base two, most significant digit first
(`false` is the digit `1`, `true` the digit `2`). -/
def bval (l : List Bool) : ℕ := l.foldl (fun a d => 2 * a + if d then 2 else 1) 0

@[simp] theorem bval_nil : bval [] = 0 := rfl

@[simp] theorem bval_concat (l : List Bool) (d : Bool) :
    bval (l ++ [d]) = 2 * bval l + if d then 2 else 1 := by
  simp [bval, List.foldl_append]

theorem bval_eq_zero_iff (l : List Bool) : bval l = 0 ↔ l = [] := by
  constructor
  · intro h
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l d _ => rw [bval_concat] at h; split at h <;> omega
  · rintro rfl; rfl

theorem bval_replicate_true (m : ℕ) (l : List Bool) :
    bval (l ++ List.replicate m true) + 2 = 2 ^ m * (bval l + 2) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ', ← List.append_assoc, bval_concat, if_pos rfl, pow_succ]
      linarith

theorem bval_replicate_false (m : ℕ) (l : List Bool) :
    bval (l ++ List.replicate m false) + 1 = 2 ^ m * (bval l + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ', ← List.append_assoc, bval_concat, pow_succ]
      simp only [Bool.false_eq_true, if_false]
      linarith

/-- A numeral of value `v` has at most `log₂ (v + 1)` digits. -/
theorem two_pow_length_le (l : List Bool) : 2 ^ l.length ≤ bval l + 1 := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l d ih =>
      rw [bval_concat, List.length_append, List.length_singleton, pow_succ]
      split <;> omega

theorem length_le_log (l : List Bool) : l.length ≤ Nat.log 2 (bval l + 1) := by
  exact Nat.le_log_of_pow_le (by norm_num) (two_pow_length_le l)

/-- Decomposition for the increment: trailing digits `2`, preceded by nothing or by a `1`. -/
theorem decomp_incr (l : List Bool) : ∃ (pre : List Bool) (m : ℕ),
    l = pre ++ List.replicate m true ∧ (pre = [] ∨ ∃ t, pre = t ++ [false]) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], 0, by simp, Or.inl rfl⟩
  | append_singleton l d ih =>
      cases d with
      | false => exact ⟨l ++ [false], 0, by simp, Or.inr ⟨l, rfl⟩⟩
      | true =>
          obtain ⟨pre, m, hl, hpre⟩ := ih
          refine ⟨pre, m + 1, ?_, hpre⟩
          rw [hl, List.replicate_succ', List.append_assoc]

/-- Decomposition for the decrement: trailing digits `1`, preceded by nothing or by a `2`. -/
theorem decomp_decr (l : List Bool) : ∃ (pre : List Bool) (m : ℕ),
    l = pre ++ List.replicate m false ∧ (pre = [] ∨ ∃ t, pre = t ++ [true]) := by
  induction l using List.reverseRecOn with
  | nil => exact ⟨[], 0, by simp, Or.inl rfl⟩
  | append_singleton l d ih =>
      cases d with
      | true => exact ⟨l ++ [true], 0, by simp, Or.inr ⟨l, rfl⟩⟩
      | false =>
          obtain ⟨pre, m, hl, hpre⟩ := ih
          refine ⟨pre, m + 1, ?_, hpre⟩
          rw [hl, List.replicate_succ', List.append_assoc]

/-! ### Increment -/

/-- Increment, least significant digit first. -/
def incrR : List Bool → List Bool
  | [] => [false]
  | false :: t => true :: t
  | true :: t => false :: incrR t

/-- Increment of a bijective base-two numeral. -/
def bincr (l : List Bool) : List Bool := (incrR l.reverse).reverse

theorem incrR_replicate (m : ℕ) (r : List Bool) :
    incrR (List.replicate m true ++ r) = List.replicate m false ++ incrR r := by
  induction m with
  | zero => rfl
  | succ m ih => simp [List.replicate_succ, incrR, ih]

/-- The carry-free part of an increment. -/
def incrHead (pre : List Bool) : List Bool := if pre = [] then [false] else pre.dropLast ++ [true]

theorem bincr_shape (pre : List Bool) (m : ℕ) (hpre : pre = [] ∨ ∃ t, pre = t ++ [false]) :
    bincr (pre ++ List.replicate m true) = incrHead pre ++ List.replicate m false := by
  unfold bincr
  rw [List.reverse_append, List.reverse_replicate, incrR_replicate, List.reverse_append,
    List.reverse_replicate]
  congr 1
  rcases hpre with rfl | ⟨t, rfl⟩
  · simp [incrR, incrHead]
  · simp [incrR, incrHead]

theorem bval_incrHead (pre : List Bool) (hpre : pre = [] ∨ ∃ t, pre = t ++ [false]) :
    bval (incrHead pre) + 1 = bval pre + 2 := by
  rcases hpre with rfl | ⟨t, rfl⟩
  · rfl
  · simp [incrHead]

theorem bval_bincr (l : List Bool) : bval (bincr l) = bval l + 1 := by
  obtain ⟨pre, m, rfl, hpre⟩ := decomp_incr l
  rw [bincr_shape pre m hpre]
  have h1 := bval_replicate_false m (incrHead pre)
  have h2 := bval_replicate_true m pre
  have h3 := bval_incrHead pre hpre
  have : 2 ^ m * (bval (incrHead pre) + 1) = 2 ^ m * (bval pre + 2) := by rw [h3]
  omega

theorem length_incrHead (pre : List Bool) : (incrHead pre).length ≤ pre.length + 1 := by
  unfold incrHead; split <;> simp

theorem length_bincr (l : List Bool) : (bincr l).length ≤ l.length + 1 := by
  obtain ⟨pre, m, rfl, hpre⟩ := decomp_incr l
  rw [bincr_shape pre m hpre]
  have := length_incrHead pre
  simp only [List.length_append, List.length_replicate]; omega

/-- One round of the carry loop of `incr`: a trailing `2` is moved to the carry register `c`;
otherwise the last digit is incremented without carry and the flag `f` is cleared. -/
def incrBody (K j c f : ℕ) : Prog :=
  ifNE j (popBranch K j (.seq (append K j true) (clear K f)) (append K c true))
    (.seq (append K j false) (clear K f))

/-- Write the carried digits back as `1`s. -/
def carryBack (K j c : ℕ) (β : Bool) : Prog :=
  whileNE c (popBranch K c (append K j β) (append K j β))

/-- `R j := bincr (R j)`, with an empty carry register `c` and an empty flag register `f`. -/
def incr (K j c f : ℕ) : Prog :=
  .seq (append K f true) (.seq (whileNE f (incrBody K j c f)) (carryBack K j c false))

/-- The register file with three registers replaced. -/
def upd3 (R : ℕ → List Bool) (j : ℕ) (a : List Bool) (c : ℕ) (b : List Bool) (f : ℕ)
    (d : List Bool) : ℕ → List Bool :=
  Function.update (Function.update (Function.update R j a) c b) f d

section upd3
variable {R : ℕ → List Bool} {j c f : ℕ}

theorem upd3_j (hjc : j ≠ c) (hjf : j ≠ f) (a b d : List Bool) : upd3 R j a c b f d j = a := by
  simp [upd3, hjc, hjf]

theorem upd3_c (hcf : c ≠ f) (a b d : List Bool) : upd3 R j a c b f d c = b := by
  simp [upd3, hcf]

theorem upd3_f (a b d : List Bool) : upd3 R j a c b f d f = d := by
  simp [upd3]

theorem upd3_upd_j (hjc : j ≠ c) (hjf : j ≠ f) (a b d e : List Bool) :
    Function.update (upd3 R j a c b f d) j e = upd3 R j e c b f d := by
  funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all

theorem upd3_upd_c (hcf : c ≠ f) (a b d e : List Bool) :
    Function.update (upd3 R j a c b f d) c e = upd3 R j a c e f d := by
  funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all

theorem upd3_upd_f (a b d e : List Bool) :
    Function.update (upd3 R j a c b f d) f e = upd3 R j a c b f e := by
  funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all

end upd3

theorem runs_incr (R : ℕ → List Bool) (j c f : ℕ) (hj : j < K) (hc : c < K) (hf : f < K)
    (hjc : j ≠ c) (hjf : j ≠ f) (hcf : c ≠ f) (hRc : R c = []) (hRf : R f = []) (N : ℕ)
    (hN : (R j).length + 1 ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (incr K j c f) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R j (bincr (R j))), 0, i⟩ := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  obtain ⟨pre, m, hRj, hpre⟩ := decomp_incr (R j)
  have hlen : (R j).length = pre.length + m := by rw [hRj]; simp
  have hhead := length_incrHead pre
  -- the carry loop
  have loop1 : ∀ k, k ≤ m → WL x B K f (incrBody K j c f)
      (upd3 R j (pre ++ List.replicate k true) c (List.replicate (m - k) true) f [true]) i
      (upd3 R j (incrHead pre) c (List.replicate m true) f []) i := by
    intro k
    induction k with
    | zero =>
        intro _
        refine wl_step hf hwB _ _ _ i i i (by rw [upd3_f]; simp) ?_ (wl_stop hf _ i (upd3_f _ _ _))
        simp only [List.replicate_zero, List.append_nil, Nat.sub_zero]
        refine runs_ifNE _ j hj hwB i _ _ _ (fun hne => ?_) (fun he => ?_)
        · rw [upd3_j hjc hjf] at hne
          obtain ⟨t, rfl⟩ := hpre.resolve_left hne
          refine runs_popBranch _ j hj (by rw [upd3_j hjc hjf]; simp) N
            (by rw [upd3_j hjc hjf]; simp at hlen ⊢; omega) hB i _ _ _ ?_
          simp only [upd3_j hjc hjf, List.getLast_append_singleton, Bool.false_eq_true,
            if_false, List.dropLast_concat, upd3_upd_j hjc hjf]
          refine (runs_append _ j hj true N (by rw [upd3_j hjc hjf]; simp at hlen ⊢; omega)
            hB i).seq ?_
          rw [upd3_upd_j hjc hjf, upd3_j hjc hjf]
          refine (runs_clear _ f hf N (by rw [upd3_f]; simp; omega) hB i).of_eq rfl ?_
          rw [upd3_upd_f]; simp [incrHead]
        · rw [upd3_j hjc hjf] at he
          subst he
          refine (runs_append _ j hj false N (by rw [upd3_j hjc hjf]; simp; omega) hB i).seq ?_
          rw [upd3_upd_j hjc hjf, upd3_j hjc hjf]
          refine (runs_clear _ f hf N (by rw [upd3_f]; simp; omega) hB i).of_eq rfl ?_
          rw [upd3_upd_f]; simp [incrHead]
    | succ k ih =>
        intro hk
        refine wl_step hf hwB _ _ _ i i i (by rw [upd3_f]; simp) ?_ (ih (by omega))
        refine runs_ifNE _ j hj hwB i _ _ _ (fun hne => ?_) (fun he => ?_)
        · refine runs_popBranch _ j hj hne N
            (by rw [upd3_j hjc hjf]; simp; omega) hB i _ _ _ ?_
          simp only [upd3_j hjc hjf, List.replicate_succ', ← List.append_assoc,
            List.getLast_append_singleton, if_true, List.dropLast_concat, upd3_upd_j hjc hjf]
          refine (runs_append _ c hc true N (by rw [upd3_c hcf]; simp; omega) hB i).of_eq rfl ?_
          rw [upd3_upd_c hcf, upd3_c hcf, show m - k = m - (k + 1) + 1 by omega,
            List.replicate_succ']
        · exfalso; rw [upd3_j hjc hjf] at he; simp at he
  -- writing the carries back
  have loop2 : ∀ k, k ≤ m → WL x B K c (popBranch K c (append K j false) (append K j false))
      (upd3 R j (incrHead pre ++ List.replicate (m - k) false) c (List.replicate k true) f []) i
      (upd3 R j (incrHead pre ++ List.replicate m false) c [] f []) i := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using wl_stop (x := x) (B := B) (body := popBranch K c (append K j false)
          (append K j false)) hc
          (upd3 R j (incrHead pre ++ List.replicate m false) c [] f []) i (upd3_c hcf _ _ _)
    | succ k ih =>
        intro hk
        refine wl_step hc hwB _ _ _ i i i (by rw [upd3_c hcf]; simp) ?_ (ih (by omega))
        refine runs_popBranch _ c hc (by rw [upd3_c hcf]; simp) N
          (by rw [upd3_c hcf]; simp; omega) hB i _ _ _ ?_
        simp only [upd3_c hcf, List.replicate_succ', List.getLast_append_singleton, if_true,
          List.dropLast_concat, upd3_upd_c hcf]
        refine (runs_append _ j hj false N (by rw [upd3_j hjc hjf]; simp; omega) hB i).of_eq rfl
          ?_
        rw [upd3_upd_j hjc hjf, upd3_j hjc hjf, List.append_assoc, ← List.replicate_succ',
          show m - (k + 1) + 1 = m - k by omega]
  -- assembling
  have e0 : Function.update R f [true] =
      upd3 R j (pre ++ List.replicate m true) c (List.replicate (m - m) true) f [true] := by
    rw [← hRj, Nat.sub_self, List.replicate_zero, ← hRc]
    funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all
  refine (runs_append R f hf true N (by rw [hRf]; simp; omega) hB i).seq ?_
  rw [hRf, List.nil_append, e0]
  refine (runs_whileNE_of_wl hf hwB (loop1 m le_rfl)).seq ?_
  have e1 : upd3 R j (incrHead pre) c (List.replicate m true) f [] =
      upd3 R j (incrHead pre ++ List.replicate (m - m) false) c (List.replicate m true) f [] := by
    simp
  rw [e1]
  refine (runs_whileNE_of_wl hc hwB (loop2 m le_rfl)).of_eq rfl ?_
  rw [hRj, bincr_shape pre m hpre]
  congr 2
  funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all

/-! ### Decrement -/

/-- Decrement, least significant digit first (`0 - 1 = 0`). -/
def decrR : List Bool → List Bool
  | [] => []
  | true :: t => false :: t
  | [false] => []
  | false :: b :: t => true :: decrR (b :: t)

/-- Decrement of a bijective base-two numeral (`0 - 1 = 0`). -/
def bdecr (l : List Bool) : List Bool := (decrR l.reverse).reverse

theorem decrR_replicate_true (m : ℕ) (t : List Bool) :
    decrR (List.replicate m false ++ true :: t) = List.replicate m true ++ false :: t := by
  induction m with
  | zero => rfl
  | succ m ih =>
      cases m with
      | zero => rfl
      | succ m =>
          rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append]
          rw [List.replicate_succ, List.cons_append] at ih
          simp only [decrR, ih, List.replicate_succ, List.cons_append]

theorem decrR_replicate_nil (m : ℕ) : decrR (List.replicate m false) = List.replicate (m - 1) true := by
  induction m with
  | zero => rfl
  | succ m ih =>
      cases m with
      | zero => rfl
      | succ m =>
          rw [List.replicate_succ, List.replicate_succ]
          rw [List.replicate_succ] at ih
          simp only [decrR, ih, Nat.add_sub_cancel]
          cases m <;> simp [List.replicate_succ]

/-- The borrow-free part of a decrement. -/
def decrHead (pre : List Bool) : List Bool := if pre = [] then [] else pre.dropLast ++ [false]

/-- The number of `2`s written back by a decrement. -/
def decrCarry (pre : List Bool) (m : ℕ) : ℕ := if pre = [] then m - 1 else m

theorem bdecr_shape (pre : List Bool) (m : ℕ) (hpre : pre = [] ∨ ∃ t, pre = t ++ [true]) :
    bdecr (pre ++ List.replicate m false) =
      decrHead pre ++ List.replicate (decrCarry pre m) true := by
  unfold bdecr
  rcases hpre with rfl | ⟨t, rfl⟩
  · simp [decrR_replicate_nil, decrHead, decrCarry]
  · rw [List.reverse_append, List.reverse_replicate, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, decrR_replicate_true,
      List.reverse_append, List.reverse_replicate, List.reverse_cons, decrHead, decrCarry]
    simp only [List.append_eq_nil_iff, List.cons_ne_nil, and_false, if_false,
      List.dropLast_concat, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.reverse_reverse]
    rw [List.singleton_append, decrR_replicate_true]
    simp

theorem bval_bdecr (l : List Bool) : bval (bdecr l) = bval l - 1 := by
  obtain ⟨pre, m, rfl, hpre⟩ := decomp_decr l
  rw [bdecr_shape pre m hpre]
  have h1 := bval_replicate_false m pre
  rcases hpre with rfl | ⟨t, rfl⟩
  · simp only [decrHead, decrCarry, if_true, List.nil_append]
    simp only [bval_nil, mul_one, List.nil_append] at h1
    cases m with
    | zero => simp
    | succ m =>
        have h2 := bval_replicate_true m []
        simp only [List.nil_append, bval_nil, zero_add, Nat.add_sub_cancel] at h2 ⊢
        rw [pow_succ] at h1
        omega
  · have hne : t ++ [true] ≠ [] := by simp
    simp only [decrHead, decrCarry, hne, if_false, List.dropLast_concat]
    have h2 := bval_replicate_true m (t ++ [false])
    simp only [bval_concat, if_true, Bool.false_eq_true, if_false] at h1 h2
    have : 2 ^ m * (2 * bval t + 1 + 2) = 2 ^ m * (2 * bval t + 2 + 1) := by ring_nf
    omega

theorem length_bdecr (l : List Bool) : (bdecr l).length ≤ l.length := by
  obtain ⟨pre, m, rfl, hpre⟩ := decomp_decr l
  rw [bdecr_shape pre m hpre]
  rcases hpre with rfl | ⟨t, rfl⟩
  · simp [decrHead, decrCarry]
  · simp [decrHead, decrCarry]

/-- One round of the borrow loop of `decr`. -/
def decrBody (K j c f : ℕ) : Prog :=
  ifNE j (popBranch K j (append K c true) (.seq (append K j false) (clear K f))) (clear K f)

/-- `R j := bdecr (R j)`, with an empty carry register `c` and an empty flag register `f`. -/
def decr (K j c f : ℕ) : Prog :=
  .seq (append K f true) (.seq (whileNE f (decrBody K j c f))
    (.seq (ifNE j skip (ifNE c (popBranch K c skip skip) skip)) (carryBack K j c true)))

theorem runs_decr (R : ℕ → List Bool) (j c f : ℕ) (hj : j < K) (hc : c < K) (hf : f < K)
    (hjc : j ≠ c) (hjf : j ≠ f) (hcf : c ≠ f) (hRc : R c = []) (hRf : R f = []) (N : ℕ)
    (hN : (R j).length + 1 ≤ N) (hB : (N + 3) * wd K ≤ B) (i : ℕ) :
    Runs x B (decr K j c f) ⟨lay K R, 0, i⟩
      ⟨lay K (Function.update R j (bdecr (R j))), 0, i⟩ := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  obtain ⟨pre, m, hRj, hpre⟩ := decomp_decr (R j)
  have hlen : (R j).length = pre.length + m := by rw [hRj]; simp
  have loop1 : ∀ k, k ≤ m → WL x B K f (decrBody K j c f)
      (upd3 R j (pre ++ List.replicate k false) c (List.replicate (m - k) true) f [true]) i
      (upd3 R j (decrHead pre) c (List.replicate m true) f []) i := by
    intro k
    induction k with
    | zero =>
        intro _
        refine wl_step hf hwB _ _ _ i i i (by rw [upd3_f]; simp) ?_ (wl_stop hf _ i (upd3_f _ _ _))
        simp only [List.replicate_zero, List.append_nil, Nat.sub_zero]
        refine runs_ifNE _ j hj hwB i _ _ _ (fun hne => ?_) (fun he => ?_)
        · rw [upd3_j hjc hjf] at hne
          obtain ⟨t, rfl⟩ := hpre.resolve_left hne
          refine runs_popBranch _ j hj (by rw [upd3_j hjc hjf]; simp) N
            (by rw [upd3_j hjc hjf]; simp at hlen ⊢; omega) hB i _ _ _ ?_
          simp only [upd3_j hjc hjf, List.getLast_append_singleton, if_true,
            List.dropLast_concat, upd3_upd_j hjc hjf]
          refine (runs_append _ j hj false N (by rw [upd3_j hjc hjf]; simp at hlen ⊢; omega)
            hB i).seq ?_
          rw [upd3_upd_j hjc hjf, upd3_j hjc hjf]
          refine (runs_clear _ f hf N (by rw [upd3_f]; simp; omega) hB i).of_eq rfl ?_
          rw [upd3_upd_f]; simp [decrHead]
        · rw [upd3_j hjc hjf] at he
          subst he
          refine (runs_clear _ f hf N (by rw [upd3_f]; simp; omega) hB i).of_eq rfl ?_
          rw [upd3_upd_f]; simp [decrHead]
    | succ k ih =>
        intro hk
        refine wl_step hf hwB _ _ _ i i i (by rw [upd3_f]; simp) ?_ (ih (by omega))
        refine runs_ifNE _ j hj hwB i _ _ _ (fun hne => ?_) (fun he => ?_)
        · refine runs_popBranch _ j hj hne N
            (by rw [upd3_j hjc hjf]; simp; omega) hB i _ _ _ ?_
          simp only [upd3_j hjc hjf, List.replicate_succ', ← List.append_assoc,
            List.getLast_append_singleton, Bool.false_eq_true, if_false, List.dropLast_concat,
            upd3_upd_j hjc hjf]
          refine (runs_append _ c hc true N (by rw [upd3_c hcf]; simp; omega) hB i).of_eq rfl ?_
          rw [upd3_upd_c hcf, upd3_c hcf, show m - k = m - (k + 1) + 1 by omega,
            List.replicate_succ']
        · exfalso; rw [upd3_j hjc hjf] at he; simp at he
  have loop2 : ∀ k, k ≤ decrCarry pre m →
      WL x B K c (popBranch K c (append K j true) (append K j true))
      (upd3 R j (decrHead pre ++ List.replicate (decrCarry pre m - k) true) c
        (List.replicate k true) f []) i
      (upd3 R j (decrHead pre ++ List.replicate (decrCarry pre m) true) c [] f []) i := by
    have hdc : decrCarry pre m ≤ m := by unfold decrCarry; split <;> omega
    intro k
    induction k with
    | zero =>
        intro _
        simpa using wl_stop (x := x) (B := B) (body := popBranch K c (append K j true)
          (append K j true)) hc
          (upd3 R j (decrHead pre ++ List.replicate (decrCarry pre m) true) c [] f []) i
          (upd3_c hcf _ _ _)
    | succ k ih =>
        intro hk
        refine wl_step hc hwB _ _ _ i i i (by rw [upd3_c hcf]; simp) ?_ (ih (by omega))
        refine runs_popBranch _ c hc (by rw [upd3_c hcf]; simp) N
          (by rw [upd3_c hcf]; simp; omega) hB i _ _ _ ?_
        simp only [upd3_c hcf, List.replicate_succ', List.getLast_append_singleton, if_true,
          List.dropLast_concat, upd3_upd_c hcf]
        have hdh : (decrHead pre).length ≤ pre.length := by
          unfold decrHead; split
          · simp
          · rename_i h; have := List.length_pos_of_ne_nil h; simp; omega
        refine (runs_append _ j hj true N (by rw [upd3_j hjc hjf]; simp; omega) hB i).of_eq rfl
          ?_
        rw [upd3_upd_j hjc hjf, upd3_j hjc hjf, List.append_assoc, ← List.replicate_succ',
          show decrCarry pre m - (k + 1) + 1 = decrCarry pre m - k by omega]
  have e0 : Function.update R f [true] =
      upd3 R j (pre ++ List.replicate m false) c (List.replicate (m - m) true) f [true] := by
    rw [← hRj, Nat.sub_self, List.replicate_zero, ← hRc]
    funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all
  refine (runs_append R f hf true N (by rw [hRf]; simp; omega) hB i).seq ?_
  rw [hRf, List.nil_append, e0]
  refine (runs_whileNE_of_wl hf hwB (loop1 m le_rfl)).seq ?_
  -- the correction for an all-`1` numeral
  have fix : Runs x B (ifNE j skip (ifNE c (popBranch K c skip skip) skip))
      ⟨lay K (upd3 R j (decrHead pre) c (List.replicate m true) f []), 0, i⟩
      ⟨lay K (upd3 R j (decrHead pre ++ List.replicate (decrCarry pre m - decrCarry pre m) true)
        c (List.replicate (decrCarry pre m) true) f []), 0, i⟩ := by
    rcases hpre with rfl | ⟨t, rfl⟩
    · refine runs_ifNE _ j hj hwB i _ _ _ (fun hne => ?_) (fun _ => ?_)
      · exfalso; rw [upd3_j hjc hjf] at hne; simp [decrHead] at hne
      refine runs_ifNE _ c hc hwB i _ _ _ (fun hne => ?_) (fun he => ?_)
      · refine runs_popBranch _ c hc hne N (by rw [upd3_c hcf]; simp; omega) hB i _ _ _ ?_
        simp only [ite_self, upd3_upd_c hcf, upd3_c hcf]
        refine (runs_skip _ 0 i).of_eq rfl ?_
        have hm : m ≠ 0 := by intro h; subst h; rw [upd3_c hcf] at hne; simp at hne
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp [decrCarry, decrHead, List.replicate_succ', List.dropLast_concat]
      · rw [upd3_c hcf] at he
        have hm : m = 0 := by simpa using he
        subst hm
        refine (runs_skip _ 0 i).of_eq rfl ?_
        simp [decrCarry]
    · refine runs_ifNE _ j hj hwB i _ _ _ (fun _ => ?_) (fun he => ?_)
      · refine (runs_skip _ 0 i).of_eq rfl ?_
        simp [decrCarry]
      · exfalso; rw [upd3_j hjc hjf] at he; simp [decrHead] at he
  refine fix.seq ?_
  refine (runs_whileNE_of_wl hc hwB (loop2 _ le_rfl)).of_eq rfl ?_
  rw [hRj, bdecr_shape pre m hpre]
  congr 2
  funext r; simp only [upd3, Function.update_apply]; split_ifs <;> simp_all

/-! ### Moving the input head by a counted distance -/

theorem runs_imoveL (v : ℕ → Bool) (h i : ℕ) :
    Runs x B (imove .left) ⟨v, h, i⟩ ⟨v, h, i - 1⟩ :=
  (Runs.act (f := fun _ w => (w, .left, .stay)) (dw := .stay) rfl (Or.inl le_rfl)).of_eq rfl
    (by simp only [moveWork, moveIn, Function.update_eq_self])

/-- Move the input head `bval (R s)` cells in direction `d`, emptying the counter `s`. -/
def moveBy (K s c f : ℕ) (d : Dir) : Prog := whileNE s (.seq (decr K s c f) (imove d))

/-- Move the input head `bval (R j) - 1` cells in direction `d`, using the scratch counter `s`. -/
def seekCounter (K j s c f : ℕ) (d : Dir) : Prog :=
  .seq (assign K j s) (.seq (decr K s c f) (moveBy K s c f d))

section seek

variable (R : ℕ → List Bool) (j s c f : ℕ) (hj : j < K) (hs : s < K) (hc : c < K) (hf : f < K)
  (hjs : j ≠ s) (hjc : j ≠ c) (hjf : j ≠ f) (hsc : s ≠ c) (hsf : s ≠ f) (hcf : c ≠ f)
  (hRs : R s = []) (hRc : R c = []) (hRf : R f = []) (N : ℕ) (hB : (N + 3) * wd K ≤ B)
include hs hc hf hsc hsf hcf hRc hRf hB

theorem wl_moveBy_right (hN : ∀ l : List Bool, l.length ≤ (R j).length → l.length + 1 ≤ N)
    (hjN : (R j).length + 1 ≤ N) :
    ∀ (r : ℕ) (l : List Bool) (i : ℕ), bval l = r → l.length ≤ (R j).length →
      i + r ≤ x.length →
      WL x B K s (.seq (decr K s c f) (imove .right)) (Function.update R s l) i
        (Function.update R s []) (i + r) := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  intro r
  induction r with
  | zero =>
      intro l i hl _ _
      rw [(bval_eq_zero_iff l).mp hl]
      exact wl_stop hs _ i (by simp)
  | succ r ih =>
      intro l i hl hlen hi
      have hne : l ≠ [] := by intro h; subst h; simp at hl
      refine wl_step hs hwB _ (Function.update R s (bdecr l)) _ i (i + 1) _ (by simpa using hne)
        ?_ ((ih (bdecr l) (i + 1) (by rw [bval_bdecr, hl]; omega)
          ((length_bdecr l).trans hlen) (by omega)).of_eq rfl
          (by rw [show i + 1 + r = i + (r + 1) by omega]))
      have hd := runs_decr (x := x) (B := B) (Function.update R s l) s c f hs hc hf hsc hsf hcf
        (by rw [Function.update_of_ne hsc.symm]; exact hRc)
        (by rw [Function.update_of_ne hsf.symm]; exact hRf) N
        (by simp only [Function.update_self]; exact hN l hlen) hB i
      simp only [Function.update_self, Function.update_idem] at hd
      refine hd.seq ((runs_imoveR _ 0 i).of_eq rfl ?_)
      congr 1; omega

theorem wl_moveBy_left (hN : ∀ l : List Bool, l.length ≤ (R j).length → l.length + 1 ≤ N) :
    ∀ (r : ℕ) (l : List Bool) (i : ℕ), bval l = r → l.length ≤ (R j).length →
      WL x B K s (.seq (decr K s c f) (imove .left)) (Function.update R s l) i
        (Function.update R s []) (i - r) := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  intro r
  induction r with
  | zero =>
      intro l i hl _
      rw [(bval_eq_zero_iff l).mp hl]
      exact wl_stop hs _ i (by simp)
  | succ r ih =>
      intro l i hl hlen
      have hne : l ≠ [] := by intro h; subst h; simp at hl
      refine wl_step hs hwB _ (Function.update R s (bdecr l)) _ i (i - 1) _ (by simpa using hne)
        ?_ ((ih (bdecr l) (i - 1) (by rw [bval_bdecr, hl]; omega)
          ((length_bdecr l).trans hlen)).of_eq rfl
          (by rw [show i - 1 - r = i - (r + 1) by omega]))
      have hd := runs_decr (x := x) (B := B) (Function.update R s l) s c f hs hc hf hsc hsf hcf
        (by rw [Function.update_of_ne hsc.symm]; exact hRc)
        (by rw [Function.update_of_ne hsf.symm]; exact hRf) N
        (by simp only [Function.update_self]; exact hN l hlen) hB i
      simp only [Function.update_self, Function.update_idem] at hd
      exact hd.seq (runs_imoveL _ 0 i)

include hj hjs hjc hjf hRs in
theorem runs_seekCounter_right (hN : (R j).length + 1 ≤ N) (i : ℕ)
    (hi : i + (bval (R j) - 1) ≤ x.length) :
    Runs x B (seekCounter K j s c f .right) ⟨lay K R, 0, i⟩
      ⟨lay K R, 0, i + (bval (R j) - 1)⟩ := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  have hN' : ∀ l : List Bool, l.length ≤ (R j).length → l.length + 1 ≤ N := by
    intro l hl; omega
  refine (runs_assign R j s hj hs hjs N (by omega) (by rw [hRs]; simp) hB i).seq ?_
  have hd := runs_decr (x := x) (B := B) (Function.update R s (R j)) s c f hs hc hf hsc hsf hcf
    (by rw [Function.update_of_ne hsc.symm]; exact hRc)
    (by rw [Function.update_of_ne hsf.symm]; exact hRf) N
    (by simp only [Function.update_self]; exact hN) hB i
  simp only [Function.update_self, Function.update_idem] at hd
  refine hd.seq ?_
  have hw := wl_moveBy_right (x := x) R j s c f hs hc hf hsc hsf hcf hRc hRf N hB hN' hN
    (bval (R j) - 1) (bdecr (R j)) i (bval_bdecr _) (length_bdecr _) hi
  refine (runs_whileNE_of_wl hs hwB hw).of_eq rfl ?_
  rw [← hRs, Function.update_eq_self]

include hj hjs hjc hjf hRs in
theorem runs_seekCounter_left (hN : (R j).length + 1 ≤ N) (i : ℕ) :
    Runs x B (seekCounter K j s c f .left) ⟨lay K R, 0, i⟩
      ⟨lay K R, 0, i - (bval (R j) - 1)⟩ := by
  have hwB : wd K < B := by
    have : 3 * wd K ≤ (N + 3) * wd K := Nat.mul_le_mul_right _ (by omega)
    have : 0 < wd K := by womega
    omega
  have hN' : ∀ l : List Bool, l.length ≤ (R j).length → l.length + 1 ≤ N := by
    intro l hl; omega
  refine (runs_assign R j s hj hs hjs N (by omega) (by rw [hRs]; simp) hB i).seq ?_
  have hd := runs_decr (x := x) (B := B) (Function.update R s (R j)) s c f hs hc hf hsc hsf hcf
    (by rw [Function.update_of_ne hsc.symm]; exact hRc)
    (by rw [Function.update_of_ne hsf.symm]; exact hRf) N
    (by simp only [Function.update_self]; exact hN) hB i
  simp only [Function.update_self, Function.update_idem] at hd
  refine hd.seq ?_
  have hw := wl_moveBy_left (x := x) R j s c f hs hc hf hsc hsf hcf hRc hRf N hB hN'
    (bval (R j) - 1) (bdecr (R j)) i (bval_bdecr _) (length_bdecr _)
  refine (runs_whileNE_of_wl hs hwB hw).of_eq rfl ?_
  rw [← hRs, Function.update_eq_self]

end seek

/-- Read the input symbol at position `bval (R j) - 1` (with the input head parked at `0`), return
the head to `0`, and continue with `cont` applied to the symbol read (`none` past the end). -/
def readSym (K j s c f : ℕ) (cont : Option Bool → Prog) : Prog :=
  .seq (seekCounter K j s c f .right)
    (.ite (fun a _ => a == some true) (.seq (seekCounter K j s c f .left) (cont (some true)))
      (.ite (fun a _ => a == some false) (.seq (seekCounter K j s c f .left) (cont (some false)))
        (.seq (seekCounter K j s c f .left) (cont none))))

theorem runs_readSym (R : ℕ → List Bool) (j s c f : ℕ) (hj : j < K) (hs : s < K) (hc : c < K)
    (hf : f < K) (hjs : j ≠ s) (hjc : j ≠ c) (hjf : j ≠ f) (hsc : s ≠ c) (hsf : s ≠ f)
    (hcf : c ≠ f) (hRs : R s = []) (hRc : R c = []) (hRf : R f = []) (N : ℕ)
    (hB : (N + 3) * wd K ≤ B) (hN : (R j).length + 1 ≤ N) (hv : bval (R j) - 1 ≤ x.length)
    (cont : Option Bool → Prog) (s' : TState)
    (hcont : Runs x B (cont x[bval (R j) - 1]?) ⟨lay K R, 0, 0⟩ s') :
    Runs x B (readSym K j s c f cont) ⟨lay K R, 0, 0⟩ s' := by
  have hr := runs_seekCounter_right (x := x) R j s c f hj hs hc hf hjs hjc hjf hsc hsf hcf hRs
    hRc hRf N hB hN 0 (by omega)
  have hl := runs_seekCounter_left (x := x) R j s c f hj hs hc hf hjs hjc hjf hsc hsf hcf hRs
    hRc hRf N hB hN (0 + (bval (R j) - 1))
  simp only [zero_add, Nat.sub_self] at hr hl
  refine hr.seq ?_
  refine Runs.ite (fun ht => ?_) (fun ht => Runs.ite (fun ht' => ?_) (fun ht' => ?_))
  · have : x[bval (R j) - 1]? = some true := by simpa using ht
    rw [this] at hcont; exact hl.seq hcont
  · have : x[bval (R j) - 1]? = some false := by simpa using ht'
    rw [this] at hcont; exact hl.seq hcont
  · have : x[bval (R j) - 1]? = none := by
      simp only [beq_iff_eq] at ht ht'
      cases h : x[bval (R j) - 1]? with
      | none => rfl
      | some b => cases b <;> simp_all
    rw [this] at hcont; exact hl.seq hcont

/-! ### Canonical numerals -/

theorem bval_inj : ∀ {l l' : List Bool}, bval l = bval l' → l = l' := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro l' h; exact ((bval_eq_zero_iff l').mp h.symm).symm
  | append_singleton l d ih =>
      intro l' h
      induction l' using List.reverseRecOn with
      | nil => exact absurd ((bval_eq_zero_iff _).mp h) (by simp)
      | append_singleton l' d' _ =>
          rw [bval_concat, bval_concat] at h
          have hd : d = d' := by
            cases d <;> cases d' <;> first | rfl | (simp at h; omega)
          subst hd
          have : bval l = bval l' := by cases d <;> simp at h <;> omega
          rw [ih this]

/-- The numeral of a number. -/
def bnum : ℕ → List Bool
  | 0 => []
  | v + 1 => bincr (bnum v)

@[simp] theorem bval_bnum (v : ℕ) : bval (bnum v) = v := by
  induction v with
  | zero => rfl
  | succ v ih => simp [bnum, bval_bincr, ih]

theorem eq_bnum (l : List Bool) : l = bnum (bval l) := bval_inj (by simp)

theorem bincr_bnum (v : ℕ) : bincr (bnum v) = bnum (v + 1) := rfl

theorem bdecr_bnum (v : ℕ) : bdecr (bnum v) = bnum (v - 1) := bval_inj (by simp [bval_bdecr])

theorem bval_lt_two_pow (l : List Bool) : bval l + 2 ≤ 2 ^ (l.length + 1) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l d ih =>
      rw [bval_concat, List.length_append, List.length_singleton, pow_succ]
      split <;> omega

theorem length_bnum_le (v : ℕ) : (bnum v).length ≤ Nat.log 2 (v + 1) := by
  have := length_le_log (bnum v); simpa using this

theorem lt_two_pow_length_bnum (v : ℕ) : v + 2 ≤ 2 ^ ((bnum v).length + 1) := by
  have := bval_lt_two_pow (bnum v); simpa using this

end Tracks

end Complexity.Space
