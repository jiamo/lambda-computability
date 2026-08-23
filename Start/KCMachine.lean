/-
# A universal prefix machine, built by Kraft–Chaitin allocation

This file constructs, from scratch, a *universal prefix-free machine* `KC.U` and its prefix
complexity `KC.KU`.  The construction is the Kraft–Chaitin ("machine existence") one, run once on
a universal stream of requests, which is what makes the resulting machine additively optimal.

* A **request** is a pair `(r, x)`: "reserve a program of length `r` for the output `x`".
  The `e`-th partial recursive code is read as the `e`-th stream of requests; requests are
  discovered at the stage at which the code first converges (`KC.emit`), and a request is
  *accepted* only while the accumulated weight `∑ 2 ^ (-r)` of the stream stays below `1`
  (`KC.accepted`).  The accepted request of stream `e` is *granted* the length `r + e + 2`
  (`KC.grant`), so that the total granted weight is at most `1 / 2`.
* Granted requests are served by the greedy aligned allocation `KC.slot`: the next dyadic
  interval of the required size, starting at the least aligned position beyond everything
  allocated so far.  Rounding up to alignment wastes at most as much as it allocates, which is
  why the `1 / 2` budget suffices.  Allocated intervals are disjoint by construction, and
  disjoint aligned dyadic intervals are incomparable bit strings, so the domain of the machine
  is prefix free.
* `KC.U σ` runs the allocation and returns the value attached to the interval named by `σ`, if
  any; `KC.KU x` is the least length of a `U`-program for `x`.

The two headline properties are

* `KC.kraft_KU` — Kraft's inequality for `KU`;
* `KC.exists_const_KU_le` — the **Kraft–Chaitin theorem**: for every computably enumerated stream
  of requests of total weight at most one there is a constant `c` with `KU x ≤ r + c` for every
  request `(r, x)` of the stream.  Optimality of `U` with respect to every other prefix machine
  is the special case where the requests are the programs of that machine.

`KC.Omega` is the halting probability of `U`, the total weight of its domain.
-/

import Start.BitString
import Start.Kraft
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Halting

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace KC

open Nat.Partrec (Code)

------------------------------------------------------------------------
-- Requests
------------------------------------------------------------------------

/-- The value emitted by the `e`-th code on input `i`, if the computation converges *exactly* at
stage `s`.  Because of this "first stage" condition each pair `(e, i)` emits at most once. -/
def emit (e i s : ℕ) : Option ℕ :=
  match Code.evaln (s + 1) (Denumerable.ofNat Code e) i with
  | none => none
  | some v =>
    match Code.evaln s (Denumerable.ofNat Code e) i with
    | none => some v
    | some _ => none

/-- The request discovered by the `e`-th stream at step `j`: the step `j` codes a pair
`(i, s)` of an input and the stage at which it converges, and the emitted value codes the pair
`(r, x)` of a requested length and an output. -/
def reqAt (e j : ℕ) : Option (ℕ × ℕ) :=
  (emit e j.unpair.1 j.unpair.2).map Nat.unpair

/-- Adding `2 ^ (-r)` to the dyadic rational `w.1 / 2 ^ w.2`. -/
def addPow (w : ℕ × ℕ) (r : ℕ) : ℕ × ℕ :=
  if r ≤ w.2 then (w.1 + 2 ^ (w.2 - r), w.2) else (w.1 * 2 ^ (r - w.2) + 1, r)

/-- The real number named by a dyadic pair. -/
noncomputable def dyadic (w : ℕ × ℕ) : ℝ := (w.1 : ℝ) / 2 ^ w.2

/-- The weight `2 ^ (-r)` of a request of length `r`. -/
noncomputable def wt (r : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ r

/-- The weight of an optional request. -/
noncomputable def wtOpt : Option (ℕ × ℕ) → ℝ
  | none => 0
  | some (r, _) => wt r

/-- The weight accumulated by the accepted requests of the `e`-th stream before step `j`. -/
def accW (e : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | j + 1 =>
    match reqAt e j with
    | none => accW e j
    | some (r, _) =>
      let w := addPow (accW e j) r
      if w.1 ≤ 2 ^ w.2 then w else accW e j

/-- The request accepted at step `j` of the `e`-th stream, if any: a request is accepted only if
the accumulated weight of the stream stays at most `1`. -/
def accepted (e j : ℕ) : Option (ℕ × ℕ) :=
  match reqAt e j with
  | none => none
  | some (r, x) =>
    let w := addPow (accW e j) r
    if w.1 ≤ 2 ^ w.2 then some (r, x) else none

/-- The request granted at global step `t`, which codes a pair `(e, j)`: the length asked for by
the `e`-th stream is padded by `e + 2` bits, so that the total granted weight is at most `1/2`. -/
def grant (t : ℕ) : Option (ℕ × ℕ) :=
  (accepted t.unpair.1 t.unpair.2).map fun p => (p.1 + t.unpair.1 + 2, p.2)

------------------------------------------------------------------------
-- Allocation
------------------------------------------------------------------------

/-- Rounding the dyadic rational `st.1 / 2 ^ st.2` up to a multiple of `2 ^ (-L)`, returned as
the numerator over `2 ^ L`. -/
def ceilAt (st : ℕ × ℕ) (L : ℕ) : ℕ :=
  if st.2 ≤ L then st.1 * 2 ^ (L - st.2) else (st.1 + 2 ^ (st.2 - L) - 1) / 2 ^ (st.2 - L)

/-- The right endpoint of the allocated part after `t` steps, as a dyadic pair. -/
def state : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | t + 1 =>
    match grant t with
    | none => state t
    | some (L, _) => (ceilAt (state t) L + 1, L)

/-- The program allocated at step `t`: its numeric value `m`, its length `L`, and the output `x`
it is a program for. -/
def slot (t : ℕ) : Option (ℕ × ℕ × ℕ) :=
  (grant t).map fun p => (ceilAt (state t) p.1, p.1, p.2)

/-- The bit string allocated at step `t`. -/
def slotStr (t : ℕ) : Option (List Bool) :=
  (slot t).map fun p => BitStr.ofNat p.2.1 p.1

/-- The output the allocation of step `t` attaches to the bit string `σ`, if it names `σ`. -/
def Ustep (σ : List Bool) (t : ℕ) : Option ℕ :=
  match slot t with
  | none => none
  | some (m, L, x) => if m = BitStr.toNat σ ∧ L = σ.length then some x else none

/-- **The universal prefix machine.**  On a bit string `σ` it returns the output attached to the
interval named by `σ`, if that interval was ever allocated. -/
def U (σ : List Bool) : Part ℕ := Nat.rfindOpt (Ustep σ)

/-- **Prefix complexity**: the least length of a `U`-program for `x`. -/
noncomputable def KU (x : ℕ) : ℕ := sInf {n | ∃ σ : List Bool, σ.length = n ∧ x ∈ U σ}

------------------------------------------------------------------------
-- Basic arithmetic of the allocation
------------------------------------------------------------------------

/-- The weight granted at step `t`. -/
noncomputable def gwt (t : ℕ) : ℝ := wtOpt (grant t)

theorem wt_pos (r : ℕ) : 0 < wt r := by
  unfold wt; positivity

theorem wtOpt_nonneg (o : Option (ℕ × ℕ)) : 0 ≤ wtOpt o := by
  cases o with
  | none => simp [wtOpt]
  | some p => exact (wt_pos p.1).le

theorem gwt_nonneg (t : ℕ) : 0 ≤ gwt t := wtOpt_nonneg _

theorem dyadic_nonneg (w : ℕ × ℕ) : 0 ≤ dyadic w := by
  unfold dyadic; positivity

theorem dyadic_le_one_iff (w : ℕ × ℕ) : dyadic w ≤ 1 ↔ w.1 ≤ 2 ^ w.2 := by
  unfold dyadic
  rw [div_le_one (by positivity)]
  exact_mod_cast Iff.rfl

/-- Adding a weight to a dyadic rational adds `2 ^ (-r)` to its value. -/
theorem dyadic_addPow (w : ℕ × ℕ) (r : ℕ) : dyadic (addPow w r) = dyadic w + wt r := by
  unfold addPow dyadic wt
  by_cases h : r ≤ w.2
  · simp only [h, if_pos]
    push_cast
    rw [add_div]
    congr 1
    have hsplit : (2 : ℝ) ^ w.2 = 2 ^ r * 2 ^ (w.2 - r) := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, inv_pow]
    field_simp
  · simp only [h, if_neg, not_false_iff]
    push_cast
    rw [add_div]
    congr 1
    · have hsplit : (2 : ℝ) ^ (r - w.2) * 2 ^ w.2 = 2 ^ r := by
        rw [← pow_add]; congr 1; omega
      rw [div_eq_div_iff (by positivity) (by positivity), mul_assoc, hsplit]
    · rw [inv_pow, one_div]

/-- The accepted weight of the `e`-th stream never exceeds `1`. -/
theorem dyadic_accW_le_one (e j : ℕ) : dyadic (accW e j) ≤ 1 := by
  induction j with
  | zero => simp [accW, dyadic]
  | succ j ih =>
      rw [accW]
      cases hreq : reqAt e j with
      | none => simpa [hreq] using ih
      | some p =>
          by_cases hle : (addPow (accW e j) p.1).1 ≤ 2 ^ (addPow (accW e j) p.1).2
          · simpa [hle] using (dyadic_le_one_iff _).2 hle
          · simpa [hle] using ih

/-- The accumulated weight is the sum of the weights of the accepted requests. -/
theorem dyadic_accW_eq_sum (e J : ℕ) :
    dyadic (accW e J) = ∑ j ∈ Finset.range J, wtOpt (accepted e j) := by
  induction J with
  | zero => simp [accW, dyadic]
  | succ J ih =>
      rw [Finset.sum_range_succ, ← ih, accW, accepted]
      cases hreq : reqAt e J with
      | none => simp [wtOpt]
      | some p =>
          by_cases hle : (addPow (accW e J) p.1).1 ≤ 2 ^ (addPow (accW e J) p.1).2
          · simp only [hle, if_pos]
            rw [dyadic_addPow]
            rfl
          · simp [hle, wtOpt]

theorem gwt_eq (t : ℕ) :
    gwt t = wtOpt (accepted t.unpair.1 t.unpair.2) * wt (t.unpair.1 + 2) := by
  unfold gwt grant
  cases h : accepted t.unpair.1 t.unpair.2 with
  | none => simp [wtOpt]
  | some p =>
      simp only [Option.map_some, wtOpt, wt]
      rw [show p.1 + t.unpair.1 + 2 = p.1 + (t.unpair.1 + 2) from by omega, pow_add]

theorem sum_wt_succ_succ_le (T : ℕ) : ∑ e ∈ Finset.range T, wt (e + 2) ≤ 1 / 2 := by
  have hgeom : ∑ i ∈ Finset.range T, (1 / 2 : ℝ) ^ i ≤ 2 := sum_geometric_two_le T
  have hrw : ∀ e : ℕ, wt (e + 2) = (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ e := by
    intro e
    unfold wt
    rw [pow_add]
    norm_num
    ring
  calc ∑ e ∈ Finset.range T, wt (e + 2)
      = (1 / 4 : ℝ) * ∑ e ∈ Finset.range T, (1 / 2 : ℝ) ^ e := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => hrw e
    _ ≤ (1 / 4 : ℝ) * 2 := by
        have : (0 : ℝ) ≤ 1 / 4 := by norm_num
        exact mul_le_mul_of_nonneg_left hgeom this
    _ = 1 / 2 := by norm_num

/-- The total granted weight of the first `T` steps is at most `1 / 2`. -/
theorem sum_gwt_le (T : ℕ) : ∑ t ∈ Finset.range T, gwt t ≤ 1 / 2 := by
  classical
  set F : ℕ × ℕ → ℝ := fun p => wtOpt (accepted p.1 p.2) * wt (p.1 + 2) with hF
  have hFnonneg : ∀ p : ℕ × ℕ, 0 ≤ F p := fun p =>
    mul_nonneg (wtOpt_nonneg _) (wt_pos _).le
  have hinj : Set.InjOn Nat.unpair (Finset.range T : Set ℕ) := by
    intro a _ b _ h
    have := congrArg (fun p : ℕ × ℕ => Nat.pair p.1 p.2) h
    simpa using this
  have hstep : ∑ t ∈ Finset.range T, gwt t
      = ∑ p ∈ (Finset.range T).image Nat.unpair, F p := by
    rw [Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun t _ => gwt_eq t
  have hsub : (Finset.range T).image Nat.unpair ⊆ Finset.range T ×ˢ Finset.range T := by
    intro p hp
    simp only [Finset.mem_image, Finset.mem_range] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (Nat.unpair_left_le t) ht, lt_of_le_of_lt (Nat.unpair_right_le t) ht⟩
  have hle : ∑ p ∈ (Finset.range T).image Nat.unpair, F p
      ≤ ∑ p ∈ Finset.range T ×ˢ Finset.range T, F p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hFnonneg p
  have hprod : ∑ p ∈ Finset.range T ×ˢ Finset.range T, F p
      = ∑ e ∈ Finset.range T, dyadic (accW e T) * wt (e + 2) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [hF]
    rw [dyadic_accW_eq_sum, ← Finset.sum_mul]
  have hbound : ∑ e ∈ Finset.range T, dyadic (accW e T) * wt (e + 2)
      ≤ ∑ e ∈ Finset.range T, wt (e + 2) := by
    refine Finset.sum_le_sum fun e _ => ?_
    have h1 : dyadic (accW e T) ≤ 1 := dyadic_accW_le_one e T
    nlinarith [wt_pos (e + 2)]
  calc ∑ t ∈ Finset.range T, gwt t = ∑ p ∈ (Finset.range T).image Nat.unpair, F p := hstep
    _ ≤ ∑ p ∈ Finset.range T ×ˢ Finset.range T, F p := hle
    _ = ∑ e ∈ Finset.range T, dyadic (accW e T) * wt (e + 2) := hprod
    _ ≤ ∑ e ∈ Finset.range T, wt (e + 2) := hbound
    _ ≤ 1 / 2 := sum_wt_succ_succ_le T

theorem wt_eq_div (L : ℕ) : wt L = 1 / 2 ^ L := by
  unfold wt; rw [inv_pow, one_div]

/-- The ceiling division `⌈a / k⌉` is at least `a / k`. -/
theorem ceil_div_ge (a k : ℕ) (hk : 0 < k) : a ≤ (a + k - 1) / k * k := by
  have h : k * ((a + k - 1) / k) + (a + k - 1) % k = a + k - 1 := Nat.div_add_mod _ _
  have hm : (a + k - 1) % k < k := Nat.mod_lt _ hk
  rw [Nat.mul_comm] at h
  generalize (a + k - 1) / k * k = Q at h
  generalize (a + k - 1) % k = R at h hm
  omega

/-- Rounding up does not move the position to the left (numerator form). -/
theorem ceilAt_nat_lower (st : ℕ × ℕ) (L : ℕ) : st.1 * 2 ^ L ≤ ceilAt st L * 2 ^ st.2 := by
  unfold ceilAt
  by_cases h : st.2 ≤ L
  · rw [if_pos h, mul_assoc, ← pow_add]
    have hL : L - st.2 + st.2 = L := by omega
    rw [hL]
  · rw [if_neg h]
    have hd : st.2 = st.2 - L + L := by omega
    have hsplit : (2 : ℕ) ^ st.2 = 2 ^ (st.2 - L) * 2 ^ L := by rw [← pow_add, ← hd]
    rw [hsplit, ← mul_assoc]
    exact Nat.mul_le_mul (ceil_div_ge st.1 (2 ^ (st.2 - L)) (by positivity)) (le_refl _)

/-- Rounding up wastes less than the size of the allocated interval (numerator form). -/
theorem ceilAt_nat_upper (st : ℕ × ℕ) (L : ℕ) :
    ceilAt st L * 2 ^ st.2 ≤ st.1 * 2 ^ L + 2 ^ st.2 := by
  unfold ceilAt
  by_cases h : st.2 ≤ L
  · rw [if_pos h, mul_assoc, ← pow_add]
    have hL : L - st.2 + st.2 = L := by omega
    rw [hL]
    exact Nat.le_add_right _ _
  · rw [if_neg h]
    have hd : st.2 = st.2 - L + L := by omega
    have hsplit : (2 : ℕ) ^ st.2 = 2 ^ (st.2 - L) * 2 ^ L := by rw [← pow_add, ← hd]
    have h1 : (st.1 + 2 ^ (st.2 - L) - 1) / 2 ^ (st.2 - L) * 2 ^ (st.2 - L)
        ≤ st.1 + 2 ^ (st.2 - L) :=
      le_trans (Nat.div_mul_le_self _ _) (Nat.sub_le _ _)
    rw [hsplit, ← mul_assoc]
    calc (st.1 + 2 ^ (st.2 - L) - 1) / 2 ^ (st.2 - L) * 2 ^ (st.2 - L) * 2 ^ L
        ≤ (st.1 + 2 ^ (st.2 - L)) * 2 ^ L := Nat.mul_le_mul h1 (le_refl _)
      _ = st.1 * 2 ^ L + 2 ^ (st.2 - L) * 2 ^ L := by ring

/-- Rounding up does not move the position to the left. -/
theorem le_ceilAt (st : ℕ × ℕ) (L : ℕ) : dyadic st ≤ (ceilAt st L : ℝ) / 2 ^ L := by
  unfold dyadic
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast ceilAt_nat_lower st L

/-- Rounding up wastes at most the size of the allocated interval. -/
theorem ceilAt_le (st : ℕ × ℕ) (L : ℕ) : (ceilAt st L : ℝ) / 2 ^ L ≤ dyadic st + wt L := by
  have hR : (ceilAt st L : ℝ) * 2 ^ st.2 ≤ (st.1 : ℝ) * 2 ^ L + 2 ^ st.2 := by
    exact_mod_cast ceilAt_nat_upper st L
  have hP : (0 : ℝ) < 2 ^ L := by positivity
  have hQ : (0 : ℝ) < (2 : ℝ) ^ st.2 := by positivity
  unfold dyadic
  rw [wt_eq_div]
  have expand : (st.1 : ℝ) / 2 ^ st.2 + 1 / 2 ^ L - (ceilAt st L : ℝ) / 2 ^ L
      = ((st.1 : ℝ) * 2 ^ L + 2 ^ st.2 - (ceilAt st L : ℝ) * 2 ^ st.2) / (2 ^ st.2 * 2 ^ L) := by
    field_simp
  have hnum : (0 : ℝ) ≤ (st.1 : ℝ) * 2 ^ L + 2 ^ st.2 - (ceilAt st L : ℝ) * 2 ^ st.2 := by
    linarith
  have hdiv : (0 : ℝ)
      ≤ ((st.1 : ℝ) * 2 ^ L + 2 ^ st.2 - (ceilAt st L : ℝ) * 2 ^ st.2) / (2 ^ st.2 * 2 ^ L) :=
    div_nonneg hnum (by positivity)
  rw [← expand] at hdiv
  linarith

theorem state_succ_of_grant {t L x : ℕ} (h : grant t = some (L, x)) :
    state (t + 1) = (ceilAt (state t) L + 1, L) := by
  rw [state, h]

theorem state_succ_of_none {t : ℕ} (h : grant t = none) : state (t + 1) = state t := by
  rw [state, h]

/-- The allocated part after `t` steps is at most twice the granted weight, hence at most `1`. -/
theorem dyadic_state_le (t : ℕ) : dyadic (state t) ≤ 2 * ∑ t' ∈ Finset.range t, gwt t' := by
  induction t with
  | zero => simp [state, dyadic]
  | succ t ih =>
      rw [Finset.sum_range_succ]
      cases h : grant t with
      | none =>
          rw [state_succ_of_none h]
          have : gwt t = 0 := by unfold gwt; rw [h]; rfl
          rw [this]
          linarith
      | some p =>
          obtain ⟨L, x⟩ := p
          rw [state_succ_of_grant h]
          have hgw : gwt t = wt L := by unfold gwt; rw [h]; rfl
          have hceil := ceilAt_le (state t) L
          have hkey : dyadic (ceilAt (state t) L + 1, L)
              = (ceilAt (state t) L : ℝ) / 2 ^ L + wt L := by
            unfold dyadic
            rw [wt_eq_div]
            push_cast
            ring
          rw [hkey, hgw]
          linarith

/-- The allocated part never exceeds the whole interval. -/
theorem dyadic_state_le_one (t : ℕ) : dyadic (state t) ≤ 1 := by
  have h1 := dyadic_state_le t
  have h2 := sum_gwt_le t
  linarith

theorem dyadic_state_le_succ (t : ℕ) : dyadic (state t) ≤ dyadic (state (t + 1)) := by
  cases h : grant t with
  | none => rw [state_succ_of_none h]
  | some p =>
      obtain ⟨L, x⟩ := p
      rw [state_succ_of_grant h]
      have hle := le_ceilAt (state t) L
      have hval : dyadic (ceilAt (state t) L + 1, L)
          = (ceilAt (state t) L : ℝ) / 2 ^ L + 1 / 2 ^ L := by
        unfold dyadic
        push_cast
        ring
      have hpos : (0 : ℝ) < 1 / 2 ^ L := by positivity
      rw [hval]
      linarith

/-- The allocation only moves to the right. -/
theorem dyadic_state_mono : Monotone fun t => dyadic (state t) :=
  monotone_nat_of_le_succ dyadic_state_le_succ

theorem slot_eq_some {t m L x : ℕ} (h : slot t = some (m, L, x)) :
    grant t = some (L, x) ∧ m = ceilAt (state t) L := by
  unfold slot at h
  cases hg : grant t with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some p =>
      obtain ⟨L₀, x₀⟩ := p
      rw [hg] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hm, hL, hx⟩ := h
      subst hL
      subst hx
      exact ⟨rfl, hm.symm⟩

theorem state_succ_of_slot {t m L x : ℕ} (h : slot t = some (m, L, x)) :
    state (t + 1) = (m + 1, L) := by
  obtain ⟨hg, hm⟩ := slot_eq_some h
  rw [state_succ_of_grant hg, hm]

theorem dyadic_state_le_slot {t m L x : ℕ} (h : slot t = some (m, L, x)) :
    dyadic (state t) ≤ (m : ℝ) / 2 ^ L := by
  obtain ⟨-, hm⟩ := slot_eq_some h
  rw [hm]
  exact le_ceilAt _ _

/-- The intervals are allocated from left to right: the interval of a later step starts at or
after the end of the interval of an earlier step. -/
theorem slot_disjoint {t t' m L x m' L' x' : ℕ} (hlt : t < t')
    (h : slot t = some (m, L, x)) (h' : slot t' = some (m', L', x')) :
    (m + 1) * 2 ^ L' ≤ m' * 2 ^ L := by
  have h1 : dyadic (state (t + 1)) = ((m : ℝ) + 1) / 2 ^ L := by
    rw [state_succ_of_slot h]
    unfold dyadic
    push_cast
    ring
  have h2 : dyadic (state (t + 1)) ≤ dyadic (state t') := dyadic_state_mono hlt
  have h3 := dyadic_state_le_slot h'
  rw [h1] at h2
  have hR : ((m : ℝ) + 1) / 2 ^ L ≤ (m' : ℝ) / 2 ^ L' := le_trans h2 h3
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hR
  exact_mod_cast hR

/-- Two allocations naming the same dyadic interval happen at the same step. -/
theorem slot_unique {t t' m L x x' : ℕ} (h : slot t = some (m, L, x))
    (h' : slot t' = some (m, L, x')) : t = t' := by
  by_contra hne
  have hexp : (m + 1) * 2 ^ L = m * 2 ^ L + 2 ^ L := by ring
  have hpos : 0 < 2 ^ L := by positivity
  rcases Nat.lt_or_ge t t' with hlt | hge
  · have := slot_disjoint hlt h h'
    omega
  · have hlt' : t' < t := by omega
    have := slot_disjoint hlt' h' h
    omega

------------------------------------------------------------------------
-- The machine
------------------------------------------------------------------------

/-- `Nat.rfindOpt` of a function taking at most one value returns that value. -/
theorem mem_rfindOpt_of_unique {α : Type} {f : ℕ → Option α}
    (H : ∀ {a b : α} {m n : ℕ}, a ∈ f m → b ∈ f n → a = b) {a : α} :
    a ∈ Nat.rfindOpt f ↔ ∃ n, a ∈ f n := by
  refine ⟨Nat.rfindOpt_spec, ?_⟩
  rintro ⟨n, hn⟩
  have hdom : (Nat.rfindOpt f).Dom := Nat.rfindOpt_dom.2 ⟨n, a, hn⟩
  obtain ⟨k, hk⟩ := Nat.rfindOpt_spec (Part.get_mem hdom)
  have heq : (Nat.rfindOpt f).get hdom = a := H hk hn
  exact heq ▸ Part.get_mem hdom

theorem mem_Ustep_iff {σ : List Bool} {t y : ℕ} :
    y ∈ Ustep σ t ↔ slot t = some (BitStr.toNat σ, σ.length, y) := by
  unfold Ustep
  cases hs : slot t with
  | none => simp
  | some p =>
      obtain ⟨m, L, z⟩ := p
      by_cases hc : m = BitStr.toNat σ ∧ L = σ.length
      · obtain ⟨hm, hL⟩ := hc
        subst hm
        subst hL
        simp [eq_comm]
      · simp only [if_neg hc, Option.mem_def]
        constructor
        · intro hy
          exact absurd hy (by simp)
        · intro hy
          simp only [Option.some.injEq, Prod.mk.injEq] at hy
          exact absurd ⟨hy.1, hy.2.1⟩ hc

/-- The programs of `U` are exactly the allocated strings. -/
theorem mem_U_iff {σ : List Bool} {x : ℕ} :
    x ∈ U σ ↔ ∃ t, slot t = some (BitStr.toNat σ, σ.length, x) := by
  unfold U
  rw [mem_rfindOpt_of_unique]
  · exact exists_congr fun t => mem_Ustep_iff
  · intro a b m n ha hb
    rw [mem_Ustep_iff] at ha hb
    have : m = n := slot_unique ha hb
    subst this
    rw [ha] at hb
    simpa using hb

/-- **The domain of `U` is prefix free.** -/
theorem prefixFree_U {σ τ : List Bool} (hσ : (U σ).Dom) (hτ : (U τ).Dom) (h : σ <+: τ) :
    σ = τ := by
  obtain ⟨t, ht⟩ := mem_U_iff.1 (Part.get_mem hσ)
  obtain ⟨t', ht'⟩ := mem_U_iff.1 (Part.get_mem hτ)
  rcases Nat.lt_trichotomy t t' with hlt | heq | hgt
  · exact absurd h (BitStr.not_prefix_of_lt (slot_disjoint hlt ht ht'))
  · subst heq
    rw [ht] at ht'
    simp only [Option.some.injEq, Prod.mk.injEq] at ht'
    obtain ⟨hval, hlen, -⟩ := ht'
    calc σ = BitStr.ofNat σ.length (BitStr.toNat σ) := (BitStr.ofNat_toNat σ).symm
      _ = BitStr.ofNat τ.length (BitStr.toNat τ) := by rw [hval, hlen]
      _ = τ := BitStr.ofNat_toNat τ
  · exact absurd h (BitStr.not_prefix_of_lt' (slot_disjoint hgt ht' ht))

theorem KU_le_of_mem {σ : List Bool} {x : ℕ} (h : x ∈ U σ) : KU x ≤ σ.length :=
  Nat.sInf_le ⟨σ, rfl, h⟩

/-- An allocated interval fits inside the unit interval. -/
theorem slot_lt {t m L x : ℕ} (h : slot t = some (m, L, x)) : m < 2 ^ L := by
  have h1 : dyadic (state (t + 1)) ≤ 1 := dyadic_state_le_one (t + 1)
  rw [state_succ_of_slot h] at h1
  exact (dyadic_le_one_iff (m + 1, L)).1 h1

/-- The string naming an allocated interval is a program for its output. -/
theorem mem_U_of_slot {t m L x : ℕ} (h : slot t = some (m, L, x)) :
    x ∈ U (BitStr.ofNat L m) := by
  rw [mem_U_iff]
  refine ⟨t, ?_⟩
  rw [BitStr.toNat_ofNat, BitStr.length_ofNat, Nat.mod_eq_of_lt (slot_lt h)]
  exact h

theorem KU_le_of_slot {t m L x : ℕ} (h : slot t = some (m, L, x)) : KU x ≤ L := by
  simpa using KU_le_of_mem (mem_U_of_slot h)

theorem grant_eq_of_accepted {e j r x : ℕ} (h : accepted e j = some (r, x)) :
    grant (Nat.pair e j) = some (r + e + 2, x) := by
  unfold grant
  rw [Nat.unpair_pair, h]
  rfl

theorem slot_of_accepted {e j r x : ℕ} (h : accepted e j = some (r, x)) :
    ∃ m, slot (Nat.pair e j) = some (m, r + e + 2, x) := by
  refine ⟨ceilAt (state (Nat.pair e j)) (r + e + 2), ?_⟩
  unfold slot
  rw [grant_eq_of_accepted h]
  rfl

/-- An accepted request of the `e`-th stream is served by a program of length `r + e + 2`. -/
theorem KU_le_of_accepted {e j r x : ℕ} (h : accepted e j = some (r, x)) :
    KU x ≤ r + (e + 2) := by
  obtain ⟨m, hm⟩ := slot_of_accepted h
  have := KU_le_of_slot hm
  omega

------------------------------------------------------------------------
-- The Kraft–Chaitin theorem
------------------------------------------------------------------------

theorem emit_of_evaln_none {e i s : ℕ}
    (h : Code.evaln (s + 1) (Denumerable.ofNat Code e) i = none) : emit e i s = none := by
  unfold emit
  rw [h]

theorem emit_eq_some {e i s v : ℕ}
    (h1 : Code.evaln (s + 1) (Denumerable.ofNat Code e) i = some v)
    (h2 : Code.evaln s (Denumerable.ofNat Code e) i = none) : emit e i s = some v := by
  unfold emit
  rw [h1, h2]

theorem emit_eq_none_of_earlier {e i s v w : ℕ}
    (h1 : Code.evaln (s + 1) (Denumerable.ofNat Code e) i = some v)
    (h2 : Code.evaln s (Denumerable.ofNat Code e) i = some w) : emit e i s = none := by
  unfold emit
  rw [h1, h2]

/-- Anything emitted by a stream is a value of the underlying partial function. -/
theorem emit_sound {e i s v : ℕ} (h : emit e i s = some v) :
    v ∈ Code.eval (Denumerable.ofNat Code e) i := by
  cases hv : Code.evaln (s + 1) (Denumerable.ofNat Code e) i with
  | none => rw [emit_of_evaln_none hv] at h; exact absurd h (by simp)
  | some w =>
      cases hs : Code.evaln s (Denumerable.ofNat Code e) i with
      | none =>
          rw [emit_eq_some hv hs] at h
          simp only [Option.some.injEq] at h
          subst h
          exact Code.evaln_sound hv
      | some u => rw [emit_eq_none_of_earlier hv hs] at h; exact absurd h (by simp)

/-- Every value of the underlying partial function is emitted, at exactly one stage. -/
theorem exists_emit {e i v : ℕ} (h : v ∈ Code.eval (Denumerable.ofNat Code e) i) :
    ∃ s, emit e i s = some v ∧ ∀ s', s' ≠ s → emit e i s' = none := by
  classical
  have hex : ∃ k, v ∈ Code.evaln k (Denumerable.ofNat Code e) i := Code.evaln_complete.1 h
  have hspec : Code.evaln (Nat.find hex) (Denumerable.ofNat Code e) i = some v := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    by_contra hc
    have h0 : Nat.find hex = 0 := by omega
    rw [h0] at hspec
    exact absurd (Code.evaln_bound (Option.mem_def.2 hspec)) (by omega)
  have hnone : ∀ k, k < Nat.find hex → Code.evaln k (Denumerable.ofNat Code e) i = none := by
    intro k hk
    cases hkv : Code.evaln k (Denumerable.ofNat Code e) i with
    | none => rfl
    | some w =>
        have hw : w ∈ Code.eval (Denumerable.ofNat Code e) i := Code.evaln_sound hkv
        have hwv : w = v := Part.mem_unique hw h
        subst hwv
        exact absurd hkv (Nat.find_min hex hk)
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · have h1 : Code.evaln (Nat.find hex - 1 + 1) (Denumerable.ofNat Code e) i = some v := by
      rw [show Nat.find hex - 1 + 1 = Nat.find hex from by omega]
      exact hspec
    exact emit_eq_some h1 (hnone _ (by omega))
  · intro s' hs'
    rcases lt_or_gt_of_ne hs' with hlt | hgt
    · exact emit_of_evaln_none (hnone (s' + 1) (by omega))
    · have hmono : Code.evaln s' (Denumerable.ofNat Code e) i = some v :=
        Code.evaln_mono (by omega) (Option.mem_def.2 hspec)
      cases hv : Code.evaln (s' + 1) (Denumerable.ofNat Code e) i with
      | none => exact emit_of_evaln_none hv
      | some w => exact emit_eq_none_of_earlier hv hmono

/-- Two stages of the same stream that both emit are equal. -/
theorem emit_stage_unique {e i s s' : ℕ} (h1 : emit e i s ≠ none) (h2 : emit e i s' ≠ none) :
    s = s' := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨s₀, -, hs₀⟩ := exists_emit (emit_sound hv)
  have e1 : s = s₀ := by by_contra hne; exact h1 (hs₀ s hne)
  have e2 : s' = s₀ := by by_contra hne; exact h2 (hs₀ s' hne)
  omega

/-- Two steps of the same stream that both discover a request are equal. -/
theorem reqAt_inj {e j j' : ℕ} (h1 : reqAt e j ≠ none) (h2 : reqAt e j' ≠ none)
    (hi : j.unpair.1 = j'.unpair.1) : j = j' := by
  unfold reqAt at h1 h2
  have h1' : emit e j.unpair.1 j.unpair.2 ≠ none := fun hc => h1 (by rw [hc]; rfl)
  have h2' : emit e j'.unpair.1 j'.unpair.2 ≠ none := fun hc => h2 (by rw [hc]; rfl)
  rw [hi] at h1'
  have hs := emit_stage_unique h1' h2'
  calc j = Nat.pair j.unpair.1 j.unpair.2 := (Nat.pair_unpair j).symm
    _ = Nat.pair j'.unpair.1 j'.unpair.2 := by rw [hi, hs]
    _ = j' := Nat.pair_unpair j'

/-- **Kraft–Chaitin machine existence.**  If `g` computably enumerates requests `(r, x)` whose
weights sum to at most one, then every requested output has a `U`-program of length exactly `r`
plus a constant depending only on `g`. -/
theorem exists_const_program {g : ℕ → Option (ℕ × ℕ)} (hg : Computable g)
    (hw : ∀ F : Finset ℕ, ∑ i ∈ F, wtOpt (g i) ≤ 1) :
    ∃ c : ℕ, ∀ t r x, g t = some (r, x) → ∃ σ : List Bool, σ.length = r + c ∧ x ∈ U σ := by
  classical
  have hmap : Computable₂ fun (_ : ℕ) (p : ℕ × ℕ) => Nat.pair p.1 p.2 :=
    Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  have hpf : Partrec fun i => ((g i).map fun p => Nat.pair p.1 p.2 : Part ℕ) :=
    Computable.ofOption (hg.option_map hmap)
  obtain ⟨c₀, hc₀⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hpf)
  refine ⟨Encodable.encode c₀ + 2, ?_⟩
  set e := Encodable.encode c₀ with he
  have hev : ∀ i, Code.eval (Denumerable.ofNat Code e) i
      = ((g i).map fun p => Nat.pair p.1 p.2 : Part ℕ) := by
    intro i
    rw [he, Denumerable.ofNat_encode, hc₀]
  -- every request of `g` is discovered by the stream
  have hA : ∀ i r x, g i = some (r, x) → ∃ s, reqAt e (Nat.pair i s) = some (r, x) := by
    intro i r x hgi
    have hmem : Nat.pair r x ∈ Code.eval (Denumerable.ofNat Code e) i := by
      rw [hev, hgi]
      simp
    obtain ⟨s, hs, -⟩ := exists_emit hmem
    refine ⟨s, ?_⟩
    unfold reqAt
    rw [Nat.unpair_pair, hs]
    simp
  -- every request discovered by the stream is a request of `g`
  have hB : ∀ j r x, reqAt e j = some (r, x) → g j.unpair.1 = some (r, x) := by
    intro j r x h
    unfold reqAt at h
    cases hem : emit e j.unpair.1 j.unpair.2 with
    | none => rw [hem] at h; exact absurd h (by simp)
    | some v =>
        rw [hem] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hmem := emit_sound hem
        rw [hev] at hmem
        cases hgi : g j.unpair.1 with
        | none => rw [hgi] at hmem; simp at hmem
        | some p =>
            obtain ⟨r', x'⟩ := p
            rw [hgi] at hmem
            simp only [Option.map_some, Part.mem_coe, Option.mem_def,
              Option.some.injEq] at hmem
            subst hmem
            rw [Nat.unpair_pair] at h
            rw [← h]
  -- the discovered requests weigh no more than the requests of `g`
  have hwt : ∀ F : Finset ℕ, ∑ j ∈ F, wtOpt (reqAt e j) ≤ 1 := by
    intro F
    have hsub : ∑ j ∈ F, wtOpt (reqAt e j)
        = ∑ j ∈ F.filter (fun j => reqAt e j ≠ none), wtOpt (reqAt e j) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro j hj hj'
      simp only [Finset.mem_filter, not_and, not_not] at hj'
      rw [hj' hj]
      rfl
    have hinj : ∀ a ∈ F.filter (fun j => reqAt e j ≠ none),
        ∀ b ∈ F.filter (fun j => reqAt e j ≠ none), a.unpair.1 = b.unpair.1 → a = b := by
      intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb
      exact reqAt_inj ha.2 hb.2 hab
    have hval : ∀ j ∈ F.filter (fun j => reqAt e j ≠ none),
        wtOpt (reqAt e j) = wtOpt (g j.unpair.1) := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 hj.2
      obtain ⟨r, x⟩ := p
      rw [hp, hB j r x hp]
    calc ∑ j ∈ F, wtOpt (reqAt e j)
        = ∑ j ∈ F.filter (fun j => reqAt e j ≠ none), wtOpt (reqAt e j) := hsub
      _ = ∑ j ∈ F.filter (fun j => reqAt e j ≠ none), wtOpt (g j.unpair.1) :=
          Finset.sum_congr rfl hval
      _ = ∑ i ∈ (F.filter (fun j => reqAt e j ≠ none)).image (fun j => j.unpair.1),
            wtOpt (g i) := by rw [Finset.sum_image hinj]
      _ ≤ 1 := hw _
  -- hence no request of this stream is ever trimmed
  have hacc : ∀ j, accepted e j = reqAt e j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
        have hsum : dyadic (accW e j) = ∑ j' ∈ Finset.range j, wtOpt (reqAt e j') := by
          rw [dyadic_accW_eq_sum]
          exact Finset.sum_congr rfl fun j' hj' => by rw [ih j' (Finset.mem_range.1 hj')]
        unfold accepted
        cases hr : reqAt e j with
        | none => rfl
        | some p =>
            obtain ⟨r, x⟩ := p
            have htot : ∑ j' ∈ Finset.range (j + 1), wtOpt (reqAt e j') ≤ 1 := hwt _
            rw [Finset.sum_range_succ, hr] at htot
            have hle : dyadic (addPow (accW e j) r) ≤ 1 := by
              rw [dyadic_addPow, hsum]
              exact htot
            have hcond := (dyadic_le_one_iff _).1 hle
            simp [hcond]
  intro t r x hgt
  obtain ⟨s, hs⟩ := hA t r x hgt
  have hfin : accepted e (Nat.pair t s) = some (r, x) := by rw [hacc, hs]
  obtain ⟨m, hm⟩ := slot_of_accepted hfin
  refine ⟨BitStr.ofNat (r + e + 2) m, ?_, mem_U_of_slot hm⟩
  rw [BitStr.length_ofNat]
  omega

/-- **Kraft–Chaitin machine existence, in the form of optimality of `U`.**  If `g` computably
enumerates requests `(r, x)` whose weights sum to at most one, then every requested output has a
`U`-program of length at most `r` plus a constant depending only on `g`. -/
theorem exists_const_KU_le {g : ℕ → Option (ℕ × ℕ)} (hg : Computable g)
    (hw : ∀ F : Finset ℕ, ∑ i ∈ F, wtOpt (g i) ≤ 1) :
    ∃ c : ℕ, ∀ t r x, g t = some (r, x) → KU x ≤ r + c := by
  obtain ⟨c, hc⟩ := exists_const_program hg hw
  refine ⟨c, fun t r x hgt => ?_⟩
  obtain ⟨σ, hlen, hmem⟩ := hc t r x hgt
  simpa [hlen] using KU_le_of_mem hmem

theorem wt_le_wt {a b : ℕ} (h : a ≤ b) : wt b ≤ wt a := by
  unfold wt
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem sum_le_of_range_le {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) {c : ℝ}
    (h : ∀ N, ∑ i ∈ Finset.range N, f i ≤ c) (F : Finset ℕ) : ∑ i ∈ F, f i ≤ c := by
  obtain ⟨N, hN⟩ := F.exists_nat_subset_range
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hN fun i _ _ => hf i) (h N)

/-- Every number has a `U`-program: the complexity `KU` is total. -/
theorem exists_program (x : ℕ) : ∃ σ : List Bool, x ∈ U σ := by
  have hgc : Computable fun n : ℕ => (some (2 * n + 2, n) : Option (ℕ × ℕ)) := by
    refine Computable.option_some.comp (Computable.pair ?_ Computable.id)
    exact Primrec.to_comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 2))
  have hgw : ∀ F : Finset ℕ, ∑ i ∈ F, wtOpt (some (2 * i + 2, i)) ≤ 1 := by
    refine sum_le_of_range_le (fun i => wtOpt_nonneg _) (fun N => ?_)
    have hstep : ∀ i ∈ Finset.range N, wtOpt (some (2 * i + 2, i)) ≤ wt (i + 2) := by
      intro i _
      simpa [wtOpt] using wt_le_wt (show i + 2 ≤ 2 * i + 2 by omega)
    calc ∑ i ∈ Finset.range N, wtOpt (some (2 * i + 2, i))
        ≤ ∑ i ∈ Finset.range N, wt (i + 2) := Finset.sum_le_sum hstep
      _ ≤ 1 / 2 := sum_wt_succ_succ_le N
      _ ≤ 1 := by norm_num
  obtain ⟨c, hc⟩ := exists_const_program hgc hgw
  obtain ⟨σ, -, hσ⟩ := hc x (2 * x + 2) x rfl
  exact ⟨σ, hσ⟩

theorem KU_spec (x : ℕ) : ∃ σ : List Bool, σ.length = KU x ∧ x ∈ U σ := by
  obtain ⟨σ, hσ⟩ := exists_program x
  have hne : Set.Nonempty {n | ∃ τ : List Bool, τ.length = n ∧ x ∈ U τ} :=
    ⟨σ.length, σ, rfl, hσ⟩
  exact Nat.sInf_mem hne

open Classical in
/-- A shortest `U`-program for `x`. -/
noncomputable def prog (x : ℕ) : List Bool := (KU_spec x).choose

theorem prog_length (x : ℕ) : (prog x).length = KU x := (KU_spec x).choose_spec.1

theorem prog_mem (x : ℕ) : x ∈ U (prog x) := (KU_spec x).choose_spec.2

/-- Shortest programs form a prefix-free code. -/
theorem prefixFree_prog : Kraft.PrefixFreeCoding prog := by
  intro x y h
  have heq : prog x = prog y := prefixFree_U (prog_mem x).fst (prog_mem y).fst h
  have hy : y ∈ U (prog x) := by rw [heq]; exact prog_mem y
  exact Part.mem_unique (prog_mem x) hy

/-- **Kraft's inequality for `KU`.** -/
theorem kraft_KU (F : Finset ℕ) : ∑ x ∈ F, wt (KU x) ≤ 1 := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    (Kraft.sum_wt_le_one prefixFree_prog F)
  unfold wt Kraft.wt
  rw [prog_length]

------------------------------------------------------------------------
-- Chaitin's constant of `U`
------------------------------------------------------------------------

/-- The weight allocated at step `t`. -/
noncomputable def omegaW (t : ℕ) : ℝ :=
  match slot t with
  | none => 0
  | some (_, L, _) => wt L

theorem omegaW_nonneg (t : ℕ) : 0 ≤ omegaW t := by
  unfold omegaW wt
  cases slot t with
  | none => simp
  | some p => positivity

theorem omegaW_eq_gwt (t : ℕ) : omegaW t = gwt t := by
  unfold omegaW gwt slot
  cases hg : grant t with
  | none => rfl
  | some p =>
      obtain ⟨L, x⟩ := p
      rfl

theorem sum_omegaW_le (n : ℕ) : ∑ i ∈ Finset.range n, omegaW i ≤ 1 / 2 := by
  simpa only [omegaW_eq_gwt] using sum_gwt_le n

theorem summable_omegaW : Summable omegaW :=
  summable_of_sum_range_le omegaW_nonneg sum_omegaW_le

/-- **Chaitin's constant of the universal prefix machine**: the halting probability of `U`. -/
noncomputable def Omega : ℝ := ∑' t, omegaW t

theorem Omega_le_half : Omega ≤ 1 / 2 :=
  Real.tsum_le_of_sum_range_le omegaW_nonneg sum_omegaW_le

theorem Omega_pos : 0 < Omega := by
  obtain ⟨σ, hσ⟩ := exists_program 0
  obtain ⟨t, ht⟩ := mem_U_iff.1 hσ
  have hpos : 0 < omegaW t := by
    unfold omegaW
    rw [ht]
    exact wt_pos _
  have hle : omegaW t ≤ Omega := summable_omegaW.le_tsum t fun j _ => omegaW_nonneg j
  linarith

end KC
