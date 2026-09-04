/-
Confluence for Gödel's System T.

`Start/SystemT.lean` proves strong normalization for the β/ι-reduction of System T and
`Start/SystemTCanon.lean` proves canonicity.  Neither says that the normal form is *unique*.
This file supplies that missing piece, by the classical route:

* `GodelT.reduces_appL`, `GodelT.reduces_lam`, … — congruence lemmas for many-step reduction;
* `GodelT.step_lift`, `GodelT.reduces_subst_arg` — reduction commutes with lifting, and reduction
  inside the term being substituted;
* `GodelT.local_confluence` — the weak diamond property, by inspection of the critical pairs of
  β and the two ι-rules;
* `GodelT.confluence` — **Newman's lemma**: a strongly normalizing term is confluent.  Every
  typable term is strongly normalizing, so `GodelT.confluence_of_typing` applies to all of them;
* `GodelT.eq_of_reduces_num` — a strongly normalizing term reduces to at most one numeral, which
  is the form in which confluence is used by the adequacy proof of `Start/SystemTDenot.lean`.
-/

import Start.Rewriting
import Start.SystemTCanon

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GodelT

------------------------------------------------------------------------
-- Congruence lemmas for many-step reduction
------------------------------------------------------------------------

theorem reduces_appL {a a' b : Tm} (h : reduces a a') : reduces (Tm.app a b) (Tm.app a' b) := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.appL _ _ _ hs) ih

theorem reduces_appR {a b b' : Tm} (h : reduces b b') : reduces (Tm.app a b) (Tm.app a b') := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.appR _ _ _ hs) ih

theorem reduces_app {a a' b b' : Tm} (ha : reduces a a') (hb : reduces b b') :
    reduces (Tm.app a b) (Tm.app a' b') :=
  (reduces_appL ha).trans (reduces_appR hb)

theorem reduces_lam {t t' : Tm} (h : reduces t t') : reduces (Tm.lam t) (Tm.lam t') := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.lam _ _ hs) ih

theorem reduces_recL {z z' f n : Tm} (h : reduces z z') :
    reduces (Tm.natrec z f n) (Tm.natrec z' f n) := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.recL _ _ _ _ hs) ih

theorem reduces_recM {z f f' n : Tm} (h : reduces f f') :
    reduces (Tm.natrec z f n) (Tm.natrec z f' n) := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.recM _ _ _ _ hs) ih

theorem reduces_recR {z f n n' : Tm} (h : reduces n n') :
    reduces (Tm.natrec z f n) (Tm.natrec z f n') := by
  induction h with
  | refl _ => exact reduces.refl _
  | step hs _ ih => exact reduces.step (step.recR _ _ _ _ hs) ih

theorem reduces_natrec {z z' f f' n n' : Tm} (hz : reduces z z') (hf : reduces f f')
    (hn : reduces n n') : reduces (Tm.natrec z f n) (Tm.natrec z' f' n') :=
  ((reduces_recL hz).trans (reduces_recM hf)).trans (reduces_recR hn)

------------------------------------------------------------------------
-- Lifting commutes with substitution and with reduction
------------------------------------------------------------------------

/-- Lifting above the substituted variable: the companion of `GodelT.lift_subst`, for a
substitution position *below* the lifting threshold. -/
theorem lift_subst_le (t : Tm) : ∀ (s : Tm) (n k x : ℕ), x ≤ k →
    lift n k (subst s x t) = subst (lift n k s) x (lift n (k + 1) t) := by
  induction t with
  | var y =>
      intro s n k x h
      by_cases hyx : y = x
      · subst hyx
        have hy : y < k + 1 := Nat.lt_succ_of_le h
        simp [lift, subst, hy]
      · by_cases hgt : y > x
        · have hy1 : 1 ≤ y := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le x) hgt)
          by_cases hyk : y < k + 1
          · have h1 : y - 1 < k := by omega
            simp [lift, subst, hyx, hgt, hyk, h1]
          · have h1 : ¬ y - 1 < k := by omega
            have h2 : y + n > x := by omega
            have h3 : y + n ≠ x := by omega
            have h4 : y + n - 1 = y - 1 + n := by omega
            simp [lift, subst, hyx, hgt, hyk, h1, h2, h3, h4]
        · have hlt : y < x := by omega
          have hyk : y < k + 1 := by omega
          have hyk' : y < k := by omega
          simp [lift, subst, hyx, hgt, hyk, hyk']
  | app a b iha ihb =>
      intro s n k x h
      simp [lift, subst, iha s n k x h, ihb s n k x h]
  | lam t ih =>
      intro s n k x h
      have hlift : lift n (k + 1) (lift 1 0 s) = lift 1 0 (lift n k s) :=
        (lift_lift s 1 n 0 k (Nat.zero_le k)).symm
      have := ih (lift 1 0 s) n (k + 1) (x + 1) (Nat.succ_le_succ h)
      simp only [lift, subst]
      rw [this, hlift]
  | zero => intro s n k x _; simp [lift, subst]
  | succ t ih => intro s n k x h; simp [lift, subst, ih s n k x h]
  | natrec z f m ihz ihf ihm =>
      intro s n k x h
      simp [lift, subst, ihz s n k x h, ihf s n k x h, ihm s n k x h]

/-- Reduction commutes with lifting. -/
theorem step_lift {t t' : Tm} (h : step t t') : ∀ n k : ℕ, step (lift n k t) (lift n k t') := by
  induction h with
  | beta a b =>
      intro n k
      have hb := step.beta (lift n (k + 1) a) (lift n k b)
      have heq : lift n k (subst b 0 a) = subst (lift n k b) 0 (lift n (k + 1) a) :=
        lift_subst_le a b n k 0 (Nat.zero_le k)
      simpa [lift, heq] using hb
  | appL a a' b _ ih => intro n k; exact step.appL _ _ _ (ih n k)
  | appR a b b' _ ih => intro n k; exact step.appR _ _ _ (ih n k)
  | lam t t' _ ih => intro n k; exact step.lam _ _ (ih n (k + 1))
  | succ t t' _ ih => intro n k; exact step.succ _ _ (ih n k)
  | recZero z f => intro n k; exact step.recZero _ _
  | recSucc z f m => intro n k; exact step.recSucc _ _ _
  | recL z z' f m _ ih => intro n k; exact step.recL _ _ _ _ (ih n k)
  | recM z f f' m _ ih => intro n k; exact step.recM _ _ _ _ (ih n k)
  | recR z f m m' _ ih => intro n k; exact step.recR _ _ _ _ (ih n k)

/-- Reduction inside the term that is substituted. -/
theorem reduces_subst_arg (t : Tm) :
    ∀ {v v' : Tm}, step v v' → ∀ x : ℕ, reduces (subst v x t) (subst v' x t) := by
  induction t with
  | var y =>
      intro v v' h x
      by_cases hy : y = x
      · simp only [subst, if_pos hy]
        exact reduces.step h (reduces.refl _)
      · simp only [subst, if_neg hy]
        exact reduces.refl _
  | app a b iha ihb => intro v v' h x; exact reduces_app (iha h x) (ihb h x)
  | lam t ih => intro v v' h x; exact reduces_lam (ih (step_lift h 1 0) (x + 1))
  | zero => intro v v' _ x; exact reduces.refl _
  | succ t ih => intro v v' h x; exact reduces_succ (ih h x)
  | natrec z f m ihz ihf ihm =>
      intro v v' h x; exact reduces_natrec (ihz h x) (ihf h x) (ihm h x)

------------------------------------------------------------------------
-- Local confluence
------------------------------------------------------------------------

/-- **Local confluence** (the weak diamond property) for β/ι-reduction. -/
theorem local_confluence {t u : Tm} (h1 : step t u) :
    ∀ {v : Tm}, step t v → ∃ w, reduces u w ∧ reduces v w := by
  induction h1 with
  | beta a b =>
      intro v h2
      cases h2 with
      | beta a b => exact ⟨subst b 0 a, reduces.refl _, reduces.refl _⟩
      | appL _ a' _ hs =>
          cases hs with
          | lam _ a0 ha =>
              exact ⟨subst b 0 a0, reduces.step (step_subst ha b 0) (reduces.refl _),
                reduces.step (step.beta _ _) (reduces.refl _)⟩
      | appR _ _ b' hb =>
          exact ⟨subst b' 0 a, reduces_subst_arg a hb 0,
            reduces.step (step.beta _ _) (reduces.refl _)⟩
  | appL a a' b ha ih =>
      intro v h2
      cases h2 with
      | beta a0 b0 =>
          cases ha with
          | lam _ a0' ha' =>
              exact ⟨subst b 0 a0', reduces.step (step.beta _ _) (reduces.refl _),
                reduces.step (step_subst ha' b 0) (reduces.refl _)⟩
      | appL _ a'' _ ha'' =>
          obtain ⟨w, hw1, hw2⟩ := ih ha''
          exact ⟨Tm.app w b, reduces_appL hw1, reduces_appL hw2⟩
      | appR _ _ b' hb =>
          exact ⟨Tm.app a' b', reduces_appR (reduces.step hb (reduces.refl _)),
            reduces_appL (reduces.step ha (reduces.refl _))⟩
  | appR a b b' hb ih =>
      intro v h2
      cases h2 with
      | beta a0 b0 =>
          exact ⟨subst b' 0 a0, reduces.step (step.beta _ _) (reduces.refl _),
            reduces_subst_arg a0 hb 0⟩
      | appL _ a' _ ha =>
          exact ⟨Tm.app a' b', reduces_appL (reduces.step ha (reduces.refl _)),
            reduces_appR (reduces.step hb (reduces.refl _))⟩
      | appR _ _ b'' hb'' =>
          obtain ⟨w, hw1, hw2⟩ := ih hb''
          exact ⟨Tm.app a w, reduces_appR hw1, reduces_appR hw2⟩
  | lam t t' ht ih =>
      intro v h2
      cases h2 with
      | lam _ t'' ht'' =>
          obtain ⟨w, hw1, hw2⟩ := ih ht''
          exact ⟨Tm.lam w, reduces_lam hw1, reduces_lam hw2⟩
  | succ t t' ht ih =>
      intro v h2
      cases h2 with
      | succ _ t'' ht'' =>
          obtain ⟨w, hw1, hw2⟩ := ih ht''
          exact ⟨Tm.succ w, reduces_succ hw1, reduces_succ hw2⟩
  | recZero z f =>
      intro v h2
      cases h2 with
      | recZero _ _ => exact ⟨z, reduces.refl _, reduces.refl _⟩
      | recL _ z' _ _ hz =>
          exact ⟨z', reduces.step hz (reduces.refl _),
            reduces.step (step.recZero _ _) (reduces.refl _)⟩
      | recM _ _ f' _ _ => exact ⟨z, reduces.refl _,
          reduces.step (step.recZero _ _) (reduces.refl _)⟩
      | recR _ _ _ n' hn => exact absurd hn not_step_zero
  | recSucc z f n =>
      intro v h2
      cases h2 with
      | recSucc _ _ _ => exact ⟨_, reduces.refl _, reduces.refl _⟩
      | recL _ z' _ _ hz =>
          refine ⟨Tm.app (Tm.app f n) (Tm.natrec z' f n), ?_, ?_⟩
          · exact reduces_appR (reduces_recL (reduces.step hz (reduces.refl _)))
          · exact reduces.step (step.recSucc _ _ _) (reduces.refl _)
      | recM _ _ f' _ hf =>
          refine ⟨Tm.app (Tm.app f' n) (Tm.natrec z f' n), ?_, ?_⟩
          · exact reduces_app (reduces_appL (reduces.step hf (reduces.refl _)))
              (reduces_recM (reduces.step hf (reduces.refl _)))
          · exact reduces.step (step.recSucc _ _ _) (reduces.refl _)
      | recR _ _ _ n' hn =>
          cases hn with
          | succ _ n'' hn'' =>
              refine ⟨Tm.app (Tm.app f n'') (Tm.natrec z f n''), ?_, ?_⟩
              · exact reduces_app (reduces_appR (reduces.step hn'' (reduces.refl _)))
                  (reduces_recR (reduces.step hn'' (reduces.refl _)))
              · exact reduces.step (step.recSucc _ _ _) (reduces.refl _)
  | recL z z' f n hz ih =>
      intro v h2
      cases h2 with
      | recZero _ _ =>
          exact ⟨z', reduces.step (step.recZero _ _) (reduces.refl _),
            reduces.step hz (reduces.refl _)⟩
      | recSucc _ _ n0 =>
          refine ⟨Tm.app (Tm.app f n0) (Tm.natrec z' f n0), ?_, ?_⟩
          · exact reduces.step (step.recSucc _ _ _) (reduces.refl _)
          · exact reduces_appR (reduces_recL (reduces.step hz (reduces.refl _)))
      | recL _ z'' _ _ hz'' =>
          obtain ⟨w, hw1, hw2⟩ := ih hz''
          exact ⟨Tm.natrec w f n, reduces_recL hw1, reduces_recL hw2⟩
      | recM _ _ f' _ hf =>
          exact ⟨Tm.natrec z' f' n, reduces_recM (reduces.step hf (reduces.refl _)),
            reduces_recL (reduces.step hz (reduces.refl _))⟩
      | recR _ _ _ n' hn =>
          exact ⟨Tm.natrec z' f n', reduces_recR (reduces.step hn (reduces.refl _)),
            reduces_recL (reduces.step hz (reduces.refl _))⟩
  | recM z f f' n hf ih =>
      intro v h2
      cases h2 with
      | recZero _ _ =>
          exact ⟨z, reduces.step (step.recZero _ _) (reduces.refl _), reduces.refl _⟩
      | recSucc _ _ n0 =>
          refine ⟨Tm.app (Tm.app f' n0) (Tm.natrec z f' n0), ?_, ?_⟩
          · exact reduces.step (step.recSucc _ _ _) (reduces.refl _)
          · exact reduces_app (reduces_appL (reduces.step hf (reduces.refl _)))
              (reduces_recM (reduces.step hf (reduces.refl _)))
      | recL _ z' _ _ hz =>
          exact ⟨Tm.natrec z' f' n, reduces_recL (reduces.step hz (reduces.refl _)),
            reduces_recM (reduces.step hf (reduces.refl _))⟩
      | recM _ _ f'' _ hf'' =>
          obtain ⟨w, hw1, hw2⟩ := ih hf''
          exact ⟨Tm.natrec z w n, reduces_recM hw1, reduces_recM hw2⟩
      | recR _ _ _ n' hn =>
          exact ⟨Tm.natrec z f' n', reduces_recR (reduces.step hn (reduces.refl _)),
            reduces_recM (reduces.step hf (reduces.refl _))⟩
  | recR z f n n' hn ih =>
      intro v h2
      cases h2 with
      | recZero _ _ => exact absurd hn not_step_zero
      | recSucc _ _ n0 =>
          cases hn with
          | succ _ n0' hn0 =>
              refine ⟨Tm.app (Tm.app f n0') (Tm.natrec z f n0'), ?_, ?_⟩
              · exact reduces.step (step.recSucc _ _ _) (reduces.refl _)
              · exact reduces_app (reduces_appR (reduces.step hn0 (reduces.refl _)))
                  (reduces_recR (reduces.step hn0 (reduces.refl _)))
      | recL _ z' _ _ hz =>
          exact ⟨Tm.natrec z' f n', reduces_recL (reduces.step hz (reduces.refl _)),
            reduces_recR (reduces.step hn (reduces.refl _))⟩
      | recM _ _ f' _ hf =>
          exact ⟨Tm.natrec z f' n', reduces_recM (reduces.step hf (reduces.refl _)),
            reduces_recR (reduces.step hn (reduces.refl _))⟩
      | recR _ _ _ n'' hn'' =>
          obtain ⟨w, hw1, hw2⟩ := ih hn''
          exact ⟨Tm.natrec z f w, reduces_recR hw1, reduces_recR hw2⟩

------------------------------------------------------------------------
-- Newman's lemma
------------------------------------------------------------------------

/-- **Bridge to the abstract rewriting interface** (`Start/Rewriting.lean`): `reduces` is the
reflexive–transitive closure of `step`, and `SN` is its notion of strong normalization. -/
theorem reduces_iff_star {t u : Tm} : reduces t u ↔ Rewriting.Star step t u := by
  constructor
  · intro h
    induction h with
    | refl t => exact Rewriting.Star.refl t
    | step hs _ ih => exact Rewriting.Star.head hs ih
  · intro h
    induction h with
    | refl => exact reduces.refl t
    | tail _ hbc ih => exact ih.trans (reduces.step hbc (reduces.refl _))

theorem SN.reduces {t u : Tm} (h : SN t) (hr : reduces t u) : SN u :=
  Rewriting.SN.star h (reduces_iff_star.1 hr)

/-- **Newman's lemma**: a strongly normalizing term is confluent.  An instance of
`Rewriting.confluent_of_sn`, whose hypothesis is exactly `local_confluence`. -/
theorem confluence {t : Tm} (h : SN t) :
    ∀ {u v : Tm}, reduces t u → reduces t v → ∃ w, reduces u w ∧ reduces v w := by
  intro u v hu hv
  obtain ⟨w, hw₁, hw₂⟩ :=
    Rewriting.confluent_of_sn
      (fun _ _ _ h₁ h₂ => by
        obtain ⟨w, hw₁, hw₂⟩ := local_confluence h₁ h₂
        exact ⟨w, reduces_iff_star.1 hw₁, reduces_iff_star.1 hw₂⟩)
      h (reduces_iff_star.1 hu) (reduces_iff_star.1 hv)
  exact ⟨w, reduces_iff_star.2 hw₁, reduces_iff_star.2 hw₂⟩

/-- Confluence for typable terms: they are all strongly normalizing. -/
theorem confluence_of_typing {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A)
    {u v : Tm} (hu : reduces t u) (hv : reduces t v) : ∃ w, reduces u w ∧ reduces v w :=
  confluence (sn_of_typing h) hu hv

------------------------------------------------------------------------
-- Uniqueness of normal forms and of numerals
------------------------------------------------------------------------

theorem eq_of_normal_reduces {t u : Tm} (h : IsNormal t) (hr : reduces t u) : t = u := by
  cases hr with
  | refl _ => rfl
  | step hs _ => exact absurd hs (h _)

theorem isNormal_num (n : ℕ) : IsNormal (num n) := by
  induction n with
  | zero => intro t' h; exact not_step_zero h
  | succ n ih =>
      intro t' h
      cases h with
      | succ _ t'' ht'' => exact ih t'' ht''

theorem num_injective {n m : ℕ} (h : num n = num m) : n = m := by
  induction n generalizing m with
  | zero => cases m with
    | zero => rfl
    | succ m => simp [num] at h
  | succ n ih => cases m with
    | zero => simp [num] at h
    | succ m =>
        have : num n = num m := by
          simpa [num] using h
        exact congrArg Nat.succ (ih this)

/-- A strongly normalizing term reduces to at most one numeral. -/
theorem eq_of_reduces_num {t : Tm} (h : SN t) {n m : ℕ} (hn : reduces t (num n))
    (hm : reduces t (num m)) : n = m := by
  obtain ⟨w, hw1, hw2⟩ := confluence h hn hm
  have h1 : num n = w := eq_of_normal_reduces (isNormal_num n) hw1
  have h2 : num m = w := eq_of_normal_reduces (isNormal_num m) hw2
  exact num_injective (h1.trans h2.symm)

/-- The same, for a typable term. -/
theorem eq_of_reduces_num_of_typing {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A)
    {n m : ℕ} (hn : reduces t (num n)) (hm : reduces t (num m)) : n = m :=
  eq_of_reduces_num (sn_of_typing h) hn hm

end GodelT
