/-
# The universal prefix machine is a machine

The allocation `KC.slot` of `Start/KCMachine.lean` is primitive recursive, so the machine `KC.U`
built from it is partial recursive.  This is what makes `KC.U` a *universal prefix machine* rather
than just a prefix-free partial function, and it is what lets the invariance theorem
`KC.exists_const_KU_comp` be deduced from the Kraft–Chaitin theorem.
-/

import Start.KCMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace KC

open Nat.Partrec (Code)

theorem primrec_two_pow : Primrec fun n : ℕ => 2 ^ n := by
  have h : Primrec (Nat.rec (motive := fun _ => ℕ) 1 fun _ ih => 2 * ih) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd).to₂
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ k ih =>
      change 2 * (Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => 2 * ih) k) = 2 ^ (k + 1)
      rw [ih, pow_succ]
      ring

theorem primrec_emit : Primrec fun p : ℕ × ℕ × ℕ => emit p.1 p.2.1 p.2.2 := by
  have hcode : Primrec fun p : ℕ × ℕ × ℕ => Denumerable.ofNat Code p.1 :=
    (Primrec.ofNat Code).comp Primrec.fst
  have hi : Primrec fun p : ℕ × ℕ × ℕ => p.2.1 := Primrec.fst.comp Primrec.snd
  have hs : Primrec fun p : ℕ × ℕ × ℕ => p.2.2 := Primrec.snd.comp Primrec.snd
  have hA : Primrec fun p : ℕ × ℕ × ℕ =>
      Code.evaln (p.2.2 + 1) (Denumerable.ofNat Code p.1) p.2.1 :=
    Code.primrec_evaln.comp (((Primrec.succ.comp hs).pair hcode).pair hi)
  have hB : Primrec fun q : (ℕ × ℕ × ℕ) × ℕ =>
      Code.evaln q.1.2.2 (Denumerable.ofNat Code q.1.1) q.1.2.1 :=
    Code.primrec_evaln.comp
      (((hs.comp Primrec.fst).pair (hcode.comp Primrec.fst)).pair (hi.comp Primrec.fst))
  have hinner : Primrec₂ fun (p : ℕ × ℕ × ℕ) (v : ℕ) =>
      (Option.casesOn (Code.evaln p.2.2 (Denumerable.ofNat Code p.1) p.2.1) (some v)
        (fun _ => none) : Option ℕ) :=
    Primrec.option_casesOn hB (Primrec.option_some.comp Primrec.snd)
      (Primrec.const (none : Option ℕ)).to₂
  refine (Primrec.option_casesOn hA (Primrec.const none) hinner).of_eq fun p => ?_
  unfold emit
  cases Code.evaln (p.2.2 + 1) (Denumerable.ofNat Code p.1) p.2.1 with
  | none => rfl
  | some v => cases Code.evaln p.2.2 (Denumerable.ofNat Code p.1) p.2.1 <;> rfl

theorem primrec_reqAt : Primrec₂ reqAt := by
  have h : Primrec fun q : ℕ × ℕ => emit q.1 q.2.unpair.1 q.2.unpair.2 :=
    primrec_emit.comp (Primrec.fst.pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))))
  exact Primrec.option_map h (Primrec.unpair.comp Primrec.snd).to₂

theorem primrec_addPow : Primrec₂ addPow := by
  have hw1 : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
  have hw2 : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
  have hr : Primrec fun q : (ℕ × ℕ) × ℕ => q.2 := Primrec.snd
  have hcond : PrimrecPred fun q : (ℕ × ℕ) × ℕ => q.2 ≤ q.1.2 :=
    Primrec.nat_le.comp hr hw2
  have hthen : Primrec fun q : (ℕ × ℕ) × ℕ => (q.1.1 + 2 ^ (q.1.2 - q.2), q.1.2) :=
    (Primrec.nat_add.comp hw1 (primrec_two_pow.comp (Primrec.nat_sub.comp hw2 hr))).pair hw2
  have helse : Primrec fun q : (ℕ × ℕ) × ℕ => (q.1.1 * 2 ^ (q.2 - q.1.2) + 1, q.2) :=
    (Primrec.succ.comp (Primrec.nat_mul.comp hw1
      (primrec_two_pow.comp (Primrec.nat_sub.comp hr hw2)))).pair hr
  exact Primrec.ite hcond hthen helse

/-- One step of the weight accumulation of a request stream. -/
def accStep (e : ℕ) (q : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  match reqAt e q.1 with
  | none => q.2
  | some (r, _) =>
    let w := addPow q.2 r
    if w.1 ≤ 2 ^ w.2 then w else q.2

theorem accW_eq_rec (e j : ℕ) :
    accW e j = Nat.rec (motive := fun _ => ℕ × ℕ) (0, 0) (fun n IH => accStep e (n, IH)) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [accW, ih]; rfl

theorem primrec_accStep : Primrec₂ accStep := by
  have hreq : Primrec fun z : ℕ × (ℕ × (ℕ × ℕ)) => reqAt z.1 z.2.1 :=
    primrec_reqAt.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hih : Primrec fun z : ℕ × (ℕ × (ℕ × ℕ)) => z.2.2 := Primrec.snd.comp Primrec.snd
  have haddp : Primrec fun y : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) => addPow y.1.2.2 y.2.1 :=
    primrec_addPow.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  have hihy : Primrec fun y : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) => y.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hcond : PrimrecPred fun y : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) =>
      (addPow y.1.2.2 y.2.1).1 ≤ 2 ^ (addPow y.1.2.2 y.2.1).2 :=
    Primrec.nat_le.comp (Primrec.fst.comp haddp) (primrec_two_pow.comp (Primrec.snd.comp haddp))
  have hg : Primrec₂ fun (z : ℕ × (ℕ × (ℕ × ℕ))) (p : ℕ × ℕ) =>
      (if (addPow z.2.2 p.1).1 ≤ 2 ^ (addPow z.2.2 p.1).2 then addPow z.2.2 p.1 else z.2.2
        : ℕ × ℕ) := Primrec.ite hcond haddp hihy
  refine (Primrec.option_casesOn hreq hih hg).of_eq fun z => ?_
  change _ = accStep z.1 z.2
  unfold accStep
  cases reqAt z.1 z.2.1 with
  | none => rfl
  | some p => obtain ⟨r, x⟩ := p; rfl

theorem primrec_accW : Primrec₂ accW := by
  refine (Primrec.nat_rec (Primrec.const ((0, 0) : ℕ × ℕ)) primrec_accStep).of_eq ?_
  intro e j
  exact (accW_eq_rec e j).symm

theorem primrec_accepted : Primrec₂ accepted := by
  have hreq : Primrec fun q : ℕ × ℕ => reqAt q.1 q.2 := primrec_reqAt
  have haddp : Primrec fun y : (ℕ × ℕ) × (ℕ × ℕ) => addPow (accW y.1.1 y.1.2) y.2.1 :=
    primrec_addPow.comp
      (primrec_accW.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)
  have hcond : PrimrecPred fun y : (ℕ × ℕ) × (ℕ × ℕ) =>
      (addPow (accW y.1.1 y.1.2) y.2.1).1 ≤ 2 ^ (addPow (accW y.1.1 y.1.2) y.2.1).2 :=
    Primrec.nat_le.comp (Primrec.fst.comp haddp) (primrec_two_pow.comp (Primrec.snd.comp haddp))
  have hg : Primrec₂ fun (q : ℕ × ℕ) (p : ℕ × ℕ) =>
      (if (addPow (accW q.1 q.2) p.1).1 ≤ 2 ^ (addPow (accW q.1 q.2) p.1).2 then some p
        else none : Option (ℕ × ℕ)) :=
    Primrec.ite hcond (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  refine (Primrec.option_casesOn hreq (Primrec.const none) hg).of_eq ?_
  rintro ⟨e, j⟩
  change _ = accepted e j
  unfold accepted
  cases reqAt e j with
  | none => rfl
  | some p => obtain ⟨r, x⟩ := p; rfl

theorem primrec_grant : Primrec grant := by
  have hacc : Primrec fun t : ℕ => accepted t.unpair.1 t.unpair.2 :=
    primrec_accepted.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
  have hg : Primrec₂ fun (t : ℕ) (p : ℕ × ℕ) => ((p.1 + t.unpair.1 + 2, p.2) : ℕ × ℕ) :=
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)))
      (Primrec.const 2)).pair (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_map hacc hg

theorem primrec_ceilAt : Primrec₂ ceilAt := by
  have hst1 : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 := Primrec.fst.comp Primrec.fst
  have hst2 : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.2 := Primrec.snd.comp Primrec.fst
  have hL : Primrec fun q : (ℕ × ℕ) × ℕ => q.2 := Primrec.snd
  have hcond : PrimrecPred fun q : (ℕ × ℕ) × ℕ => q.1.2 ≤ q.2 :=
    Primrec.nat_le.comp hst2 hL
  have hthen : Primrec fun q : (ℕ × ℕ) × ℕ => q.1.1 * 2 ^ (q.2 - q.1.2) :=
    Primrec.nat_mul.comp hst1 (primrec_two_pow.comp (Primrec.nat_sub.comp hL hst2))
  have hpow : Primrec fun q : (ℕ × ℕ) × ℕ => 2 ^ (q.1.2 - q.2) :=
    primrec_two_pow.comp (Primrec.nat_sub.comp hst2 hL)
  have helse : Primrec fun q : (ℕ × ℕ) × ℕ =>
      (q.1.1 + 2 ^ (q.1.2 - q.2) - 1) / 2 ^ (q.1.2 - q.2) :=
    Primrec.nat_div.comp
      (Primrec.nat_sub.comp (Primrec.nat_add.comp hst1 hpow) (Primrec.const 1)) hpow
  exact Primrec.ite hcond hthen helse

/-- One step of the allocation. -/
def stateStep (q : ℕ × (ℕ × ℕ)) : ℕ × ℕ :=
  match grant q.1 with
  | none => q.2
  | some (L, _) => (ceilAt q.2 L + 1, L)

theorem state_eq_rec (t : ℕ) :
    state t = Nat.rec (motive := fun _ => ℕ × ℕ) (0, 0) (fun n IH => stateStep (n, IH)) t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [state, ih]; rfl

theorem primrec_stateStep : Primrec stateStep := by
  have hgr : Primrec fun z : ℕ × (ℕ × ℕ) => grant z.1 := primrec_grant.comp Primrec.fst
  have hih : Primrec fun z : ℕ × (ℕ × ℕ) => z.2 := Primrec.snd
  have hg : Primrec₂ fun (z : ℕ × (ℕ × ℕ)) (p : ℕ × ℕ) =>
      ((ceilAt z.2 p.1 + 1, p.1) : ℕ × ℕ) :=
    (Primrec.succ.comp (primrec_ceilAt.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd))).pair (Primrec.fst.comp Primrec.snd)
  refine (Primrec.option_casesOn hgr hih hg).of_eq fun z => ?_
  unfold stateStep
  cases grant z.1 with
  | none => rfl
  | some p => obtain ⟨L, x⟩ := p; rfl

theorem primrec_state : Primrec state := by
  have h : Primrec fun t : ℕ =>
      Nat.rec (motive := fun _ => ℕ × ℕ) (0, 0) (fun n IH => stateStep (n, IH)) t :=
    Primrec.nat_rec' Primrec.id (Primrec.const ((0, 0) : ℕ × ℕ))
      (primrec_stateStep.comp Primrec.snd).to₂
  exact h.of_eq fun t => (state_eq_rec t).symm

theorem slot_primrec : Primrec slot := by
  have hg : Primrec₂ fun (t : ℕ) (p : ℕ × ℕ) =>
      ((ceilAt (state t) p.1, p.1, p.2) : ℕ × ℕ × ℕ) :=
    (primrec_ceilAt.comp (primrec_state.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.option_map primrec_grant hg

theorem primrec_Ustep : Primrec₂ Ustep := by
  have hslot : Primrec fun z : List Bool × ℕ => slot z.2 := slot_primrec.comp Primrec.snd
  have hm : Primrec fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) => y.2.1 :=
    Primrec.fst.comp Primrec.snd
  have hL : Primrec fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) => y.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hx : Primrec fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) => y.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hval : Primrec fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) => BitStr.toNat y.1.1 :=
    BitStr.primrec_toNat.comp (Primrec.fst.comp Primrec.fst)
  have hlen : Primrec fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) => y.1.1.length :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hc1 : PrimrecPred fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) =>
      y.2.1 = BitStr.toNat y.1.1 := Primrec.eq.comp hm hval
  have hc2 : PrimrecPred fun y : (List Bool × ℕ) × (ℕ × ℕ × ℕ) =>
      y.2.2.1 = y.1.1.length := Primrec.eq.comp hL hlen
  have hg : Primrec₂ fun (z : List Bool × ℕ) (p : ℕ × ℕ × ℕ) =>
      (if p.1 = BitStr.toNat z.1 ∧ p.2.1 = z.1.length then some p.2.2 else none : Option ℕ) :=
    Primrec.ite (hc1.and hc2) (Primrec.option_some.comp hx) (Primrec.const none)
  refine (Primrec.option_casesOn hslot (Primrec.const none) hg).of_eq ?_
  rintro ⟨σ, t⟩
  change _ = Ustep σ t
  unfold Ustep
  cases slot t with
  | none => rfl
  | some p => obtain ⟨m, L, x⟩ := p; rfl

theorem computable_Ustep : Computable₂ Ustep := primrec_Ustep.to_comp

theorem partrec_U : Partrec U := Partrec.rfindOpt computable_Ustep

------------------------------------------------------------------------
-- The invariance theorem
------------------------------------------------------------------------

/-- The request stream that transports `U`-programs along the partial recursive function coded by
`ec`: the step `n` codes a pair `(t, s)`; if the allocation of step `t` is a program of length `L`
for `x`, and the `s`-th stage is the first at which the machine `ec` converges on `x` with value
`y`, then a program of length `L` is requested for `y`. -/
def compReq (ec n : ℕ) : Option (ℕ × ℕ) :=
  (slot n.unpair.1).bind fun p => (emit ec p.2.2 n.unpair.2).map fun y => (p.2.1, y)

theorem primrec_compReq : Primrec₂ compReq := by
  have hslot : Primrec fun z : ℕ × ℕ => slot z.2.unpair.1 :=
    slot_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have hemit : Primrec fun y : (ℕ × ℕ) × (ℕ × ℕ × ℕ) => emit y.1.1 y.2.2.2 y.1.2.unpair.2 :=
    primrec_emit.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))))
  have hpair : Primrec₂ fun (y : (ℕ × ℕ) × (ℕ × ℕ × ℕ)) (v : ℕ) => ((y.2.2.1, v) : ℕ × ℕ) :=
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd
  exact Primrec.option_bind hslot (Primrec.option_map hemit hpair)

theorem compReq_eq_some {ec n r y : ℕ} (h : compReq ec n = some (r, y)) :
    ∃ m x, slot n.unpair.1 = some (m, r, x) ∧ emit ec x n.unpair.2 = some y := by
  unfold compReq at h
  cases hs : slot n.unpair.1 with
  | none => rw [hs] at h; exact absurd h (by simp)
  | some p =>
      obtain ⟨m, L, x⟩ := p
      rw [hs] at h
      rw [Option.bind_some] at h
      cases he : emit ec x n.unpair.2 with
      | none => rw [he] at h; exact absurd h (by simp)
      | some v =>
          rw [he] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hL, hv⟩ := h
          subst hL
          subst hv
          exact ⟨m, x, rfl, he⟩

theorem wtOpt_compReq {ec n : ℕ} (h : compReq ec n ≠ none) :
    wtOpt (compReq ec n) = omegaW n.unpair.1 := by
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨r, y⟩ := p
  obtain ⟨m, x, hs, -⟩ := compReq_eq_some hp
  rw [hp]
  unfold omegaW
  rw [hs]
  rfl

theorem compReq_inj {ec a b : ℕ} (ha : compReq ec a ≠ none) (hb : compReq ec b ≠ none)
    (h : a.unpair.1 = b.unpair.1) : a = b := by
  obtain ⟨⟨ra, ya⟩, hpa⟩ := Option.ne_none_iff_exists'.1 ha
  obtain ⟨⟨rb, yb⟩, hpb⟩ := Option.ne_none_iff_exists'.1 hb
  obtain ⟨ma, xa, hsa, hea⟩ := compReq_eq_some hpa
  obtain ⟨mb, xb, hsb, heb⟩ := compReq_eq_some hpb
  rw [h, hsb] at hsa
  simp only [Option.some.injEq, Prod.mk.injEq] at hsa
  obtain ⟨-, -, hx⟩ := hsa
  subst hx
  have hstage : a.unpair.2 = b.unpair.2 :=
    emit_stage_unique (by rw [hea]; simp) (by rw [heb]; simp)
  calc a = Nat.pair a.unpair.1 a.unpair.2 := (Nat.pair_unpair a).symm
    _ = Nat.pair b.unpair.1 b.unpair.2 := by rw [h, hstage]
    _ = b := Nat.pair_unpair b

theorem sum_wtOpt_compReq_le (ec : ℕ) (F : Finset ℕ) : ∑ n ∈ F, wtOpt (compReq ec n) ≤ 1 := by
  classical
  have hsub : ∑ n ∈ F, wtOpt (compReq ec n)
      = ∑ n ∈ F.filter (fun n => compReq ec n ≠ none), wtOpt (compReq ec n) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro n hn hn'
    simp only [Finset.mem_filter, not_and, not_not] at hn'
    rw [hn' hn]
    rfl
  have hinj : ∀ a ∈ F.filter (fun n => compReq ec n ≠ none),
      ∀ b ∈ F.filter (fun n => compReq ec n ≠ none), a.unpair.1 = b.unpair.1 → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_filter] at ha hb
    exact compReq_inj ha.2 hb.2 hab
  have hval : ∀ n ∈ F.filter (fun n => compReq ec n ≠ none),
      wtOpt (compReq ec n) = omegaW n.unpair.1 := by
    intro n hn
    simp only [Finset.mem_filter] at hn
    exact wtOpt_compReq hn.2
  calc ∑ n ∈ F, wtOpt (compReq ec n)
      = ∑ n ∈ F.filter (fun n => compReq ec n ≠ none), wtOpt (compReq ec n) := hsub
    _ = ∑ n ∈ F.filter (fun n => compReq ec n ≠ none), omegaW n.unpair.1 :=
        Finset.sum_congr rfl hval
    _ = ∑ t ∈ (F.filter (fun n => compReq ec n ≠ none)).image (fun n => n.unpair.1),
          omegaW t := by rw [Finset.sum_image hinj]
    _ ≤ Omega := summable_omegaW.sum_le_tsum _ (fun t _ => omegaW_nonneg t)
    _ ≤ 1 := le_trans Omega_le_half (by norm_num)

/-- **Invariance.**  Complexity does not increase by more than a constant along a partial
recursive function. -/
theorem exists_const_KU_comp {f : ℕ →. ℕ} (hf : Partrec f) :
    ∃ c : ℕ, ∀ x y : ℕ, y ∈ f x → KU y ≤ KU x + c := by
  obtain ⟨c₀, hc₀⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hf)
  obtain ⟨c, hc⟩ := exists_const_KU_le (g := compReq (Encodable.encode c₀))
    ((primrec_compReq.comp (Primrec.const _) Primrec.id).to_comp)
    (sum_wtOpt_compReq_le _)
  refine ⟨c, fun x y hy => ?_⟩
  obtain ⟨t, ht⟩ := mem_U_iff.1 (prog_mem x)
  have hyx : y ∈ Code.eval (Denumerable.ofNat Code (Encodable.encode c₀)) x := by
    rw [Denumerable.ofNat_encode, hc₀]
    exact hy
  obtain ⟨s, hs, -⟩ := exists_emit hyx
  have hreq : compReq (Encodable.encode c₀) (Nat.pair t s) = some ((prog x).length, y) := by
    unfold compReq
    rw [Nat.unpair_pair, ht]
    simp [hs]
  have hfin := hc (Nat.pair t s) (prog x).length y hreq
  rwa [prog_length] at hfin

end KC
