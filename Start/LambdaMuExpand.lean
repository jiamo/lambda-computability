/-
**The expansion lemmas of typed λμ** (support for `M23-LAMBDA-MU-SN`, round 6).

* `LambdaMu.Tm.step_ren_inv` — **reflection of reduction along an arbitrary renaming**: a step of
  `ren r t` is the renaming of a step of `t` (no injectivity needed); hence `LambdaMu.SN.ren`.
* `LambdaMu.sn_mu` — `SN t → SN (μα.[β]t)`, by well-founded induction on reduction together with
  "body of a μ" (the renaming rule replaces a body by a renaming of a sub-body).
* `LambdaMu.Tm.W` — the encoding of the command `[β]t` (with `α` free) as the term
  `μδ.[β+1](↑t)`.  It turns the structural substitution *at the binder* into a structural
  substitution at a *free* name, so `Step.sstr` (round 5) applies: `LambdaMu.mstep_sb`.
* `LambdaMu.sn_apps_mu` — **the μ-expansion lemma with stacks** (the first missing lemma of
  round 5): for a typed `μα.[β]t : A`, a typed stack `π` of SN terms, if the body after the
  structural substitution of the whole stack is SN, then `(μα.[β]t) π` is SN.
* `LambdaMu.sn_apps_beta` — **the β-expansion lemma with stacks**.
-/

import Start.LambdaMuSstr
import Start.LambdaMuSN

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

open Tm

namespace Tm

/-! ### Renaming: structural substitution and reflection of steps -/

/-- Structural substitution commutes with a renaming that is injective at the name. -/
theorem sstr_ren_at (r : ℕ → ℕ) (a : ℕ) (hr : ∀ b, r b = r a → b = a) (v t : Tm) :
    ren r (sstr a v t) = sstr (r a) (ren r v) (ren r t) := by
  induction t generalizing r a v with
  | var i => rfl
  | lam t ih =>
      have hup : ∀ b, up r b = up r (a + 1) → b = a + 1 := by
        intro b h
        cases b with
        | zero => simp [up] at h
        | succ b => simp only [up, Nat.succ_inj] at h; rw [hr b h]
      have hv : ren (up r) (ren Nat.succ v) = ren Nat.succ (ren r v) := by
        rw [ren_ren, ren_ren]; rfl
      simp only [sstr, ren, ih (up r) (a + 1) hup, hv]
      rfl
  | app t u iht ihu => simp [sstr, ren, iht r a hr, ihu r a hr]
  | mu β t ih =>
      have hup : ∀ b, up r b = up r (a + 1) → b = a + 1 := by
        intro b h
        cases b with
        | zero => simp [up] at h
        | succ b => simp only [up, Nat.succ_inj] at h; rw [hr b h]
      have hv : ren (up r) (ren Nat.succ v) = ren Nat.succ (ren r v) := by
        rw [ren_ren, ren_ren]; rfl
      have hcond : (β = a + 1) ↔ (up r β = r a + 1) := by
        constructor
        · rintro rfl; rfl
        · intro h; exact hup β h
      by_cases h : β = a + 1
      · have h' : up r β = r a + 1 := hcond.1 h
        simp only [sstr, ren, if_pos h, if_pos h', ih (up r) (a + 1) hup, hv]
        rfl
      · have h' : ¬ up r β = r a + 1 := fun hc => h (hcond.2 hc)
        simp only [sstr, ren, if_neg h, if_neg h', ih (up r) (a + 1) hup, hv]
        rfl

theorem up_eq_zero (r : ℕ → ℕ) : ∀ b, up r b = up r 0 → b = 0
  | 0, _ => rfl
  | b + 1, h => by simp [up] at h

/-- **Reflection of reduction along a renaming.** -/
theorem step_ren_inv : ∀ (t : Tm) (r : ℕ → ℕ) (s : Tm), Step (ren r t) s →
    ∃ t', s = ren r t' ∧ Step t t'
  | var i, r, s, h => absurd h not_step_var
  | lam t, r, s, h => by
      simp only [ren] at h
      cases h with
      | lam h' =>
          obtain ⟨t', rfl, ht⟩ := step_ren_inv t (up r) _ h'
          exact ⟨lam t', rfl, Step.lam ht⟩
  | app t u, r, s, h => by
      simp only [ren] at h
      generalize hx : ren r t = x at h
      cases h with
      | beta b _ =>
          cases t with
          | lam t0 =>
              simp only [ren, lam.injEq] at hx
              subst hx
              exact ⟨subst (single u) t0, (ren_single r u t0).symm, Step.beta _ _⟩
          | var _ => simp [ren] at hx
          | app _ _ => simp [ren] at hx
          | mu _ _ => simp [ren] at hx
      | struct β b _ =>
          cases t with
          | mu β0 t0 =>
              simp only [ren, mu.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              have hv : ren (up r) (ren Nat.succ u) = ren Nat.succ (ren r u) := by
                rw [ren_ren, ren_ren]; rfl
              have hs := sstr_ren_at (up r) 0 (up_eq_zero r) (ren Nat.succ u) t0
              rw [hv] at hs
              have hβ : (up r β0 = 0) ↔ (β0 = 0) := by
                cases β0 with
                | zero => simp [up]
                | succ i => simp [up]
              refine ⟨mu β0 (if β0 = 0 then app (sstr 0 (ren Nat.succ u) t0) (ren Nat.succ u)
                else sstr 0 (ren Nat.succ u) t0), ?_, Step.struct _ _ _⟩
              by_cases h0 : β0 = 0
              · rw [if_pos (hβ.2 h0)]
                simp only [ren, if_pos h0, hs, hv]
                rfl
              · rw [if_neg (fun h' => h0 (hβ.1 h'))]
                simp only [ren, if_neg h0, hs]
                rfl
          | var _ => simp [ren] at hx
          | app _ _ => simp [ren] at hx
          | lam _ => simp [ren] at hx
      | appL _ h' =>
          subst hx
          obtain ⟨t', rfl, ht⟩ := step_ren_inv t r _ h'
          exact ⟨app t' u, rfl, Step.appL _ ht⟩
      | appR _ h' =>
          subst hx
          obtain ⟨u', rfl, hu⟩ := step_ren_inv u r _ h'
          exact ⟨app t u', rfl, Step.appR _ hu⟩
  | mu β t, r, s, h => by
      simp only [ren] at h
      generalize hx : ren (up r) t = x at h
      cases h with
      | rename _ γ y =>
          cases t with
          | mu γ0 t0 =>
              simp only [ren, mu.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              refine ⟨mu (nameOf (single (var β) γ0)) (subst (single (var β)) t0), ?_,
                Step.rename _ _ _⟩
              have hbody : ren (up r) (subst (single (var β)) t0) =
                  subst (single (var (up r β))) (ren (up (up r)) t0) := by
                rw [ren_subst, subst_ren]
                congr 1
                funext i
                cases i <;> rfl
              have hname : up r (nameOf (single (var β) γ0)) =
                  nameOf (single (var (up r β)) (up (up r) γ0)) := by
                cases γ0 <;> rfl
              simp only [ren, hbody, hname]
          | var _ => simp [ren] at hx
          | app _ _ => simp [ren] at hx
          | lam _ => simp [ren] at hx
      | mu _ h' =>
          subst hx
          obtain ⟨t', rfl, ht⟩ := step_ren_inv t (up r) _ h'
          exact ⟨mu β t', rfl, Step.mu _ ht⟩

/-- Substitution by variables is renaming. -/
theorem subst_varRen (g : ℕ → ℕ) (t : Tm) : subst (fun i => var (g i)) t = ren g t := by
  induction t generalizing g with
  | var i => rfl
  | lam t ih =>
      have h : upS (fun i => var (g i)) = fun i => var (up g i) := by
        funext i; cases i <;> rfl
      simp only [subst, ren, h, ih]
  | app t u iht ihu => simp [subst, ren, iht, ihu]
  | mu β t ih =>
      have h : upS (fun i => var (g i)) = fun i => var (up g i) := by
        funext i; cases i <;> rfl
      simp only [subst, ren, h, ih, nameOf]

theorem ren_succ_inj {s t : Tm} (h : ren Nat.succ s = ren Nat.succ t) : s = t := by
  have := congrArg (ren Nat.pred) h
  rw [ren_ren, ren_ren] at this
  have hid : (fun i => Nat.pred (Nat.succ i)) = id := by funext i; rfl
  rwa [hid, ren_id, ren_id] at this

/-- `TmFree` along a renaming. -/
theorem tmFree_ren : ∀ (t : Tm) (r : ℕ → ℕ) (a b : ℕ), (∀ i, r i = b → i = a) →
    TmFree a t → TmFree b (ren r t)
  | var i, r, a, b, hr, h => fun hb => h (hr i hb)
  | lam t, r, a, b, hr, h => by
      refine tmFree_ren t (up r) (a + 1) (b + 1) ?_ h
      intro i hi
      cases i with
      | zero => simp [up] at hi
      | succ i => simp only [up, Nat.succ_inj] at hi; rw [hr i hi]
  | app t u, r, a, b, hr, h => ⟨tmFree_ren t r a b hr h.1, tmFree_ren u r a b hr h.2⟩
  | mu β t, r, a, b, hr, h => by
      refine tmFree_ren t (up r) (a + 1) (b + 1) ?_ h
      intro i hi
      cases i with
      | zero => simp [up] at hi
      | succ i => simp only [up, Nat.succ_inj] at hi; rw [hr i hi]

end Tm

/-! ### SN along renamings, and under μ -/

theorem SN.ren {t : Tm} (h : SN t) (r : ℕ → ℕ) : SN (Tm.ren r t) := by
  induction h with
  | intro t _ ih =>
      refine SN.intro fun s hs => ?_
      obtain ⟨t', rfl, ht⟩ := Tm.step_ren_inv t r s hs
      exact ih t' ht

theorem SN.of_ren_succ {t : Tm} (h : SN (Tm.ren Nat.succ t)) : SN t :=
  sn_of_map (Tm.ren Nat.succ) (fun _ _ hs => Step.ren hs _ Nat.succ_injective) h

theorem SN.transGen {t t' : Tm} (h : SN t) (hs : Relation.TransGen Step t t') : SN t' := by
  induction hs with
  | single hs => exact h.step hs
  | tail _ hs ih => exact ih.step hs

theorem SN.rtg {t t' : Tm} (h : SN t) (hs : Relation.ReflTransGen Step t t') : SN t' := by
  induction hs with
  | refl => exact h
  | tail _ hs ih => exact ih.step hs

theorem transGen_flip {a b : Tm} (h : Relation.TransGen Step a b) :
    Relation.TransGen (fun x y => Step y x) b a := by
  induction h with
  | single hs => exact .single hs
  | tail _ hs ih => exact .head hs ih

/-- `a` is the body of the μ-abstraction `b`. -/
def BodyOf (a b : Tm) : Prop := ∃ γ, b = mu γ a

/-- Reduction or "body of a μ". -/
def SR (a b : Tm) : Prop := Step b a ∨ BodyOf a b

theorem bodyOf_commute {a b : Tm} (h : Relation.ReflTransGen BodyOf a b) :
    ∀ {a'}, Step a a' → ∃ b', Step b b' ∧ Relation.ReflTransGen BodyOf a' b' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro a' hs; exact ⟨a', hs, .refl⟩
  | head hac _ ih =>
      intro a' hs
      obtain ⟨γ, rfl⟩ := hac
      obtain ⟨b', hb, hrel⟩ := ih (Step.mu γ hs)
      exact ⟨b', hb, .head ⟨γ, rfl⟩ hrel⟩

theorem acc_SR_inv {a b : Tm} (h : Relation.ReflTransGen BodyOf a b) (hb : Acc SR b) :
    Acc SR a := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hb
  | head hac _ ih => exact ih.inv (Or.inr hac)

/-- SN terms are accessible for "reduction or body of a μ". -/
theorem acc_SR {b : Tm} (h : SN b) : Acc SR b := by
  induction h with
  | intro b _ ih1 =>
      have key : ∀ a, Relation.ReflTransGen BodyOf a b → Acc SR a := by
        intro a
        refine (measure (fun t : Tm => sizeOf t)).wf.induction
          (C := fun a => Relation.ReflTransGen BodyOf a b → Acc SR a) a ?_
        intro a iha hab
        refine Acc.intro a fun c hc => ?_
        rcases hc with hs | hbody
        · obtain ⟨b', hb', hrel⟩ := bodyOf_commute hab hs
          exact acc_SR_inv hrel (ih1 b' hb')
        · obtain ⟨γ, rfl⟩ := hbody
          refine iha c ?_ (.head ⟨γ, rfl⟩ hab)
          show sizeOf c < sizeOf (mu γ c)
          simp only [Tm.mu.sizeOf_spec]
          omega
      exact key b .refl

theorem sn_mu_ren_acc {X : Tm} (hX : Acc SR X) : ∀ (β : ℕ) (f : ℕ → ℕ), SN (mu β (Tm.ren f X)) := by
  induction hX with
  | intro X _ ih =>
      intro β f
      refine SN.intro fun s hs => ?_
      generalize hx : Tm.ren f X = x at hs
      cases hs with
      | rename _ γ y =>
          cases X with
          | mu γ0 X0 =>
              simp only [Tm.ren, mu.injEq] at hx
              obtain ⟨rfl, rfl⟩ := hx
              let g : ℕ → ℕ := fun i => match i with | 0 => β | i + 1 => f i
              have hg : subst (single (var β)) (Tm.ren (up f) X0) = Tm.ren g X0 := by
                rw [subst_ren, ← subst_varRen]
                congr 1
                funext i
                cases i <;> rfl
              rw [hg]
              exact ih X0 (Or.inr ⟨γ0, rfl⟩) _ g
          | var _ => simp [Tm.ren] at hx
          | app _ _ => simp [Tm.ren] at hx
          | lam _ => simp [Tm.ren] at hx
      | mu _ h =>
          subst hx
          obtain ⟨X', rfl, hX'⟩ := Tm.step_ren_inv X f _ h
          exact ih X' (Or.inl hX') β f

/-- **SN is closed under μ-abstraction.** -/
theorem sn_mu {X : Tm} (h : SN X) (β : ℕ) : SN (mu β X) := by
  simpa [Tm.ren_id] using sn_mu_ren_acc (acc_SR h) β id

/-! ### The command encoding `W` and structural substitution at the binder -/

/-- The body produced by one structural step: `[β]t` with `[α]w ↦ [α](w v)` (`α` = index `0`). -/
def sb (v : Tm) (β : ℕ) (t : Tm) : Tm :=
  if β = 0 then app (sstr 0 v t) v else sstr 0 v t

/-- The command `[β]t` (with `α` = index `0` free) as a term: `μδ.[β+1](↑t)`. -/
def W (β : ℕ) (t : Tm) : Tm := mu (β + 1) (Tm.ren Nat.succ t)

theorem sstr_W (v : Tm) (β : ℕ) (t : Tm) : sstr 0 v (W β t) = W β (sb v β t) := by
  have h := sstr_ren_succ 0 v t
  by_cases h0 : β = 0
  · subst h0
    simp only [W, sb, sstr, if_true, Tm.ren, h]
  · have h1 : ¬ (β + 1 = 0 + 1) := by omega
    simp only [W, sb, sstr, if_neg h1, if_neg h0, h]

theorem step_mu_shape {β : ℕ} {t M : Tm} (h : Step (mu β t) M) : ∃ β1 t1, M = mu β1 t1 := by
  cases h with
  | rename => exact ⟨_, _, rfl⟩
  | mu _ _ => exact ⟨_, _, rfl⟩

theorem step_to_W {β β1 : ℕ} {t t1 : Tm} (h : Step (mu β t) (mu β1 t1)) :
    Step (W β t) (W β1 t1) := by
  cases h with
  | rename _ γ t2 =>
      show Step (mu (β + 1) (mu (up Nat.succ γ) (Tm.ren (up Nat.succ) t2)))
        (mu (nameOf (single (var β) γ) + 1) (Tm.ren Nat.succ (subst (single (var β)) t2)))
      have e1 : Tm.ren Nat.succ (subst (single (var β)) t2) =
          subst (single (var (β + 1))) (Tm.ren (up Nat.succ) t2) := ren_single _ _ _
      have e2 : nameOf (single (var β) γ) + 1 = nameOf (single (var (β + 1)) (up Nat.succ γ)) := by
        cases γ <;> rfl
      rw [e1, e2]
      exact Step.rename _ _ _
  | mu _ h => exact Step.mu _ (Step.ren h _ Nat.succ_injective)

theorem W_step_inv {β : ℕ} {t Z : Tm} (h : Step (W β t) Z) :
    ∃ β1 t1, Z = W β1 t1 ∧ Step (mu β t) (mu β1 t1) := by
  unfold W at h
  generalize hx : Tm.ren Nat.succ t = x at h
  cases h with
  | rename _ γ y =>
      cases t with
      | mu γ0 t0 =>
          simp only [Tm.ren, mu.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          refine ⟨_, _, ?_, Step.rename β γ0 t0⟩
          have e1 : Tm.ren Nat.succ (subst (single (var β)) t0) =
              subst (single (var (β + 1))) (Tm.ren (up Nat.succ) t0) := ren_single _ _ _
          have e2 : nameOf (single (var β) γ0) + 1 =
              nameOf (single (var (β + 1)) (up Nat.succ γ0)) := by
            cases γ0 <;> rfl
          simp only [W, e1, e2]
      | var _ => simp [Tm.ren] at hx
      | app _ _ => simp [Tm.ren] at hx
      | lam _ => simp [Tm.ren] at hx
  | mu _ h =>
      subst hx
      obtain ⟨t', rfl, ht⟩ := Tm.step_ren_inv t _ _ h
      exact ⟨β, t', rfl, Step.mu _ ht⟩

theorem W_inj {β β' : ℕ} {t t' : Tm} (h : W β t = W β' t') : β = β' ∧ t = t' := by
  simp only [W, mu.injEq, Nat.succ_inj] at h
  exact ⟨h.1, ren_succ_inj h.2⟩

/-- Steps between μ-abstractions, on pairs (name, body). -/
def MStep (p q : ℕ × Tm) : Prop := Step (mu p.1 p.2) (mu q.1 q.2)

theorem W_transGen {β : ℕ} {t : Tm} :
    ∀ {Z : Tm}, Relation.TransGen Step (W β t) Z →
      ∃ β1 t1, Z = W β1 t1 ∧ Relation.TransGen MStep (β, t) (β1, t1) := by
  intro Z h
  induction h with
  | single h =>
      obtain ⟨β1, t1, rfl, hs⟩ := W_step_inv h
      exact ⟨β1, t1, rfl, .single hs⟩
  | tail _ h ih =>
      obtain ⟨b, s, rfl, hc⟩ := ih
      obtain ⟨β1, t1, rfl, hs⟩ := W_step_inv h
      exact ⟨β1, t1, rfl, .tail hc hs⟩

/-- **One structural step at the binder commutes with a step of the μ-abstraction.** -/
theorem mstep_sb {β β1 : ℕ} {t t1 : Tm} (hf : TmFree 0 t) (h : Step (mu β t) (mu β1 t1))
    (v : Tm) : Relation.TransGen MStep (β, sb v β t) (β1, sb v β1 t1) := by
  have hW := step_to_W h
  have hfree : TmFree 0 (W β t) :=
    Tm.tmFree_ren t Nat.succ 0 1 (fun i hi => by simpa using hi) hf
  have hs := Step.sstr hW 0 v hfree
  rw [sstr_W, sstr_W] at hs
  obtain ⟨b, s, he, hc⟩ := W_transGen hs
  obtain ⟨rfl, rfl⟩ := W_inj he
  exact hc

theorem tmFree_body {Δ : List Entry} {β : ℕ} {t : Tm} {A : Ty} (h : Typ Δ (mu β t) A) :
    TmFree 0 t := by
  cases h with
  | @mu _ _ _ _ B ht _ => exact ht.tmFree 0 A (by simp)

theorem mstep_typ {Δ : List Entry} {A : Ty} {p q : ℕ × Tm} (h : MStep p q)
    (ht : Typ Δ (mu p.1 p.2) A) : Typ Δ (mu q.1 q.2) A := ht.step h

theorem mstep_sb_chain {Δ : List Entry} {A : Ty} (v : Tm) {p q : ℕ × Tm}
    (h : Relation.TransGen MStep p q) :
    Typ Δ (mu p.1 p.2) A → Relation.TransGen MStep (p.1, sb v p.1 p.2) (q.1, sb v q.1 q.2) := by
  induction h using Relation.TransGen.head_induction_on with
  | single h => intro ht; exact mstep_sb (tmFree_body ht) h v
  | head h _ ih =>
      intro ht
      exact (mstep_sb (tmFree_body ht) h v).trans (ih (mstep_typ h ht))

/-! ### Stacks -/

/-- Typed stacks: applying a term of type `A` to `π` gives type `R`. -/
inductive TStk (Δ : List Entry) : Ty → List Tm → Ty → Prop
  | nil (A : Ty) : TStk Δ A [] A
  | cons {u : Tm} {A B : Ty} {π : List Tm} {R : Ty} :
      Typ Δ u A → TStk Δ B π R → TStk Δ (.arr A B) (u :: π) R

theorem typ_apps {Δ : List Entry} {A R : Ty} {π : List Tm} (h : TStk Δ A π R) :
    ∀ {x : Tm}, Typ Δ x A → Typ Δ (apps x π) R := by
  induction h with
  | nil => intro x hx; exact hx
  | cons hu _ ih => intro x hx; exact ih (.app hx hu)

/-- The iterated structural substitution of a stack at the binder. -/
def sbs : List Tm → ℕ → Tm → Tm
  | [], _, t => t
  | v :: π, β, t => sbs π β (sb (Tm.ren Nat.succ v) β t)

theorem typ_sb {Δ : List Entry} {β : ℕ} {t v : Tm} {C A : Ty} (h : Typ Δ (mu β t) (.arr C A))
    (hv : Typ Δ v C) : Typ Δ (mu β (sb (Tm.ren Nat.succ v) β t)) A :=
  Typ.step (Step.struct β t v) (.app h hv)

theorem mstep_sbs_chain : ∀ (π : List Tm) {Δ : List Entry} {A R : Ty} {p q : ℕ × Tm},
    Typ Δ (mu p.1 p.2) A → TStk Δ A π R → Relation.TransGen MStep p q →
      Relation.TransGen MStep (p.1, sbs π p.1 p.2) (q.1, sbs π q.1 q.2)
  | [], _, _, _, _, _, _, _, h => h
  | v :: π, Δ, _, R, p, q, ht, hT, h => by
      cases hT with
      | cons hv hπ =>
          have h1 := mstep_sb_chain (Tm.ren Nat.succ v) h ht
          exact mstep_sbs_chain π (p := (p.1, sb (Tm.ren Nat.succ v) p.1 p.2))
            (q := (q.1, sb (Tm.ren Nat.succ v) q.1 q.2)) (typ_sb ht hv) hπ h1

theorem mstep_sbs_rtg (π : List Tm) {Δ : List Entry} {A R : Ty} {p q : ℕ × Tm}
    (ht : Typ Δ (mu p.1 p.2) A) (hT : TStk Δ A π R) (h : Relation.ReflTransGen MStep p q) :
    Relation.ReflTransGen MStep (p.1, sbs π p.1 p.2) (q.1, sbs π q.1 q.2) := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with rfl | h
  · exact .refl
  · exact (mstep_sbs_chain π ht hT h).to_reflTransGen

theorem mstep_lift_transGen {p q : ℕ × Tm} (h : Relation.TransGen MStep p q) :
    Relation.TransGen Step (mu p.1 p.2) (mu q.1 q.2) :=
  Relation.TransGen.lift (fun p : ℕ × Tm => mu p.1 p.2) (fun _ _ h => h) _ _ h

theorem mstep_lift_rtg {p q : ℕ × Tm} (h : Relation.ReflTransGen MStep p q) :
    Relation.ReflTransGen Step (mu p.1 p.2) (mu q.1 q.2) :=
  Relation.ReflTransGen.lift (fun p : ℕ × Tm => mu p.1 p.2) (fun _ _ h => h) _ _ h

/-! ### Reduction of the substituted term -/

theorem sstr_step_v {v v1 : Tm} (hv : Step v v1) :
    ∀ (t : Tm) (a : ℕ), Relation.ReflTransGen Step (sstr a v t) (sstr a v1 t) := by
  intro t
  induction t generalizing v v1 with
  | var i => intro a; exact .refl
  | lam t ih =>
      intro a
      exact Relation.ReflTransGen.lift lam (fun _ _ h => Step.lam h) _ _
        (ih (Step.ren hv _ Nat.succ_injective) (a + 1))
  | app t u iht ihu =>
      intro a
      exact (Relation.ReflTransGen.lift (fun x => app x (sstr a v u)) (fun _ _ h => Step.appL _ h)
        _ _ (iht hv a)).trans
        (Relation.ReflTransGen.lift (fun x => app (sstr a v1 t) x) (fun _ _ h => Step.appR _ h)
        _ _ (ihu hv a))
  | mu β t ih =>
      intro a
      have hv' := Step.ren hv _ Nat.succ_injective
      have h1 := ih hv' (a + 1)
      simp only [sstr]
      split_ifs
      · refine Relation.ReflTransGen.lift (mu β) (fun _ _ h => Step.mu _ h) _ _ ?_
        exact (Relation.ReflTransGen.lift (fun x => app x _) (fun _ _ h => Step.appL _ h) _ _
          h1).trans (.single (Step.appR _ hv'))
      · exact Relation.ReflTransGen.lift (mu β) (fun _ _ h => Step.mu _ h) _ _ h1

theorem sb_step_v {v v1 : Tm} (hv : Step v v1) (β : ℕ) (t : Tm) :
    Relation.ReflTransGen Step (sb v β t) (sb v1 β t) := by
  unfold sb
  split_ifs
  · exact (Relation.ReflTransGen.lift (fun x => app x v) (fun _ _ h => Step.appL _ h) _ _
      (sstr_step_v hv t 0)).trans (.single (Step.appR _ hv))
  · exact sstr_step_v hv t 0

/-! ### Stacks of SN terms -/

theorem apps_step_left {X X' : Tm} (h : Step X X') : ∀ π, Step (apps X π) (apps X' π)
  | [] => h
  | u :: π => apps_step_left (Step.appL u h) π

theorem apps_rtg_left {X X' : Tm} (h : Relation.ReflTransGen Step X X') (π : List Tm) :
    Relation.ReflTransGen Step (apps X π) (apps X' π) :=
  Relation.ReflTransGen.lift (fun x => apps x π) (fun _ _ h => apps_step_left h π) _ _ h

/-- One step in one component of a stack. -/
inductive ListStep : List Tm → List Tm → Prop
  | head {u u' : Tm} (π : List Tm) : Step u u' → ListStep (u :: π) (u' :: π)
  | tail (u : Tm) {π π' : List Tm} : ListStep π π' → ListStep (u :: π) (u :: π')

theorem apps_listStep {π π' : List Tm} (h : ListStep π π') : ∀ X, Step (apps X π) (apps X π') := by
  induction h with
  | head π hs => intro X; exact apps_step_left (Step.appR X hs) π
  | tail u _ ih => intro X; exact ih (app X u)

theorem apps_step_inv : ∀ (π : List Tm) (X Z : Tm), (∀ t, X ≠ lam t) → (∀ β t, X ≠ mu β t) →
    Step (apps X π) Z →
      (∃ X', Step X X' ∧ Z = apps X' π) ∨ (∃ π', ListStep π π' ∧ Z = apps X π')
  | [], X, Z, _, _, h => .inl ⟨Z, h, rfl⟩
  | u :: π, X, Z, hl, hm, h => by
      rcases apps_step_inv π (app X u) Z (by simp) (by simp) h with ⟨X'', hs, rfl⟩ | ⟨π', hπ, rfl⟩
      · cases hs with
        | beta t _ => exact absurd rfl (hl t)
        | struct β t _ => exact absurd rfl (hm β t)
        | appL _ hs => exact .inl ⟨_, hs, rfl⟩
        | appR _ hs => exact .inr ⟨_, ListStep.head π hs, rfl⟩
      · exact .inr ⟨u :: π', ListStep.tail u hπ, rfl⟩

theorem sn_apps_varHead : ∀ (π : List Tm) {h : Tm}, VarHead h → SN h → (∀ v ∈ π, SN v) →
    SN (apps h π)
  | [], _, _, hh, _ => hh
  | u :: π, _, hv, hh, hπ =>
      sn_apps_varHead π (.app u hv) (sn_app_varHead hv hh (hπ u (by simp)))
        (fun v hv' => hπ v (by simp [hv']))

theorem listStep_sn {π π' : List Tm} (h : ListStep π π') (hπ : ∀ v ∈ π, SN v) :
    ∀ v ∈ π', SN v := by
  induction h with
  | head π hs =>
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact (hπ _ (by simp)).step hs
      · exact hπ v (by simp [hv])
  | tail u _ ih =>
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact hπ _ (by simp)
      · exact ih (fun w hw => hπ w (by simp [hw])) v hv

/-- **Head expansion with a stack of SN terms**, for a head that is neither a λ nor a μ. -/
theorem sn_apps_head {π : List Tm} (hπ : ∀ v ∈ π, SN v) {X : Tm} (hl : ∀ t, X ≠ lam t)
    (hm : ∀ β t, X ≠ mu β t) (h : ∀ X', Step X X' → SN (apps X' π)) : SN (apps X π) := by
  have hsn := sn_apps_varHead π (.var 0) (sn_var 0) hπ
  generalize hy : apps (var 0) π = y at hsn
  induction hsn generalizing π with
  | intro y _ ih =>
      subst hy
      refine SN.intro fun Z hZ => ?_
      rcases apps_step_inv π X Z hl hm hZ with ⟨X', hs, rfl⟩ | ⟨π', hπ', rfl⟩
      · exact h X' hs
      · refine ih _ (apps_listStep hπ' (var 0)) (π := π') (listStep_sn hπ' hπ) ?_ rfl
        intro X' hX'
        exact (h X' hX').step (apps_listStep hπ' X')

/-! ### The μ-expansion lemma -/

/-- **The μ-expansion lemma with stacks.** -/
theorem sn_apps_mu : ∀ (π : List Tm) {Δ : List Entry} {A R : Ty} {β : ℕ} {t : Tm},
    Typ Δ (mu β t) A → TStk Δ A π R → (∀ v ∈ π, SN v) → SN (mu β (sbs π β t)) →
      SN (apps (mu β t) π)
  | [], _, _, _, _, _, _, _, _, h => h
  | v :: π0, Δ, A, R, β, t, ht, hT, hπ, hm => by
      cases hT with
      | @cons _ C A' _ _ hv hπ0 =>
          have hπ0SN : ∀ w ∈ π0, SN w := fun w hw => hπ w (by simp [hw])
          have key : ∀ v, SN v → Typ Δ v C → ∀ β t, Typ Δ (mu β t) (.arr C A') →
              SN (mu β (sbs (v :: π0) β t)) → SN (apps (app (mu β t) v) π0) := by
            intro v hvSN
            induction hvSN with
            | intro v _ ihv =>
                intro hv
                have inner : ∀ m, Acc (Relation.TransGen fun a b => Step b a) m → ∀ β t,
                    m = mu β (sbs (v :: π0) β t) → Typ Δ (mu β t) (.arr C A') → SN m →
                    SN (apps (app (mu β t) v) π0) := by
                  intro m hacc
                  induction hacc with
                  | intro m _ ihm =>
                      intro β t hmdef ht hm
                      subst hmdef
                      refine sn_apps_head hπ0SN (by simp) (by simp) fun X' hX' => ?_
                      cases hX' with
                      | struct =>
                          exact sn_apps_mu π0 (typ_sb ht hv) hπ0 hπ0SN hm
                      | appL _ h =>
                          obtain ⟨β1, t1, rfl⟩ := step_mu_shape h
                          have hc := mstep_sbs_chain (v :: π0) (p := (β, t)) (q := (β1, t1)) ht
                            (.cons hv hπ0) (.single h)
                          have hc' := mstep_lift_transGen hc
                          exact ihm _ (transGen_flip hc') β1 t1 rfl (ht.step h)
                            (SN.transGen hm hc')
                      | appR _ h =>
                          have h1 : Relation.ReflTransGen MStep (β, sb (Tm.ren Nat.succ v) β t)
                              (β, sb (Tm.ren Nat.succ _) β t) :=
                            Relation.ReflTransGen.lift (fun s => (β, s))
                              (fun _ _ h => Step.mu β h) _ _
                              (sb_step_v (Step.ren h _ Nat.succ_injective) β t)
                          have h2 := mstep_lift_rtg (mstep_sbs_rtg π0 (typ_sb ht hv) hπ0 h1)
                          exact ihv _ h (hv.step h) β t ht (SN.rtg hm h2)
                intro β t ht hm
                exact inner _ (Acc.transGen hm) β t rfl ht hm
          exact key v (hπ v (by simp)) hv β t ht hm

/-! ### The β-expansion lemma -/

theorem Typ.nameFree {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ (a : ℕ) (B : Ty), Γ[a]? = some (.tm B) → NameFree a t := by
  induction h with
  | var _ => intro a B _; trivial
  | lam _ ih => intro a B ha; exact ih (a + 1) B (by simpa using ha)
  | app _ _ iht ihu => intro a B ha; exact ⟨iht a B ha, ihu a B ha⟩
  | @mu Γ β t A B' _ hβ ih =>
      intro a B ha
      refine ⟨?_, ih (a + 1) B (by simpa using ha)⟩
      rintro rfl
      have : (Entry.nm A :: Γ)[a + 1]? = Γ[a]? := by simp
      rw [this, ha] at hβ
      cases hβ

theorem subst_step_arg {u u1 : Tm} (hu : Step u u1) :
    ∀ (X : Tm) (a : ℕ) (σ σ' : ℕ → Tm), NameFree a X → σ a = u → σ' a = u1 →
      (∀ i, i ≠ a → σ i = σ' i) → Relation.ReflTransGen Step (subst σ X) (subst σ' X) := by
  intro X
  induction X generalizing u u1 with
  | var i =>
      intro a σ σ' _ h1 h2 h3
      by_cases hi : i = a
      · subst hi; simp only [subst, h1, h2]; exact .single hu
      · simp only [subst, h3 i hi]; exact .refl
  | lam X ih =>
      intro a σ σ' hX h1 h2 h3
      refine Relation.ReflTransGen.lift lam (fun _ _ h => Step.lam h) _ _
        (ih (Step.ren hu _ Nat.succ_injective) (a + 1) (upS σ) (upS σ') hX
          (by simp [upS, h1]) (by simp [upS, h2]) ?_)
      intro i hi
      cases i with
      | zero => rfl
      | succ i => simp [upS, h3 i (by omega)]
  | app t w iht ihw =>
      intro a σ σ' hX h1 h2 h3
      exact (Relation.ReflTransGen.lift (fun x => app x (subst σ w)) (fun _ _ h => Step.appL _ h)
        _ _ (iht hu a σ σ' hX.1 h1 h2 h3)).trans
        (Relation.ReflTransGen.lift (fun x => app (subst σ' t) x) (fun _ _ h => Step.appR _ h)
        _ _ (ihw hu a σ σ' hX.2 h1 h2 h3))
  | mu β X ih =>
      intro a σ σ' hX h1 h2 h3
      have h3' : ∀ i, i ≠ a + 1 → upS σ i = upS σ' i := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => simp [upS, h3 i (by omega)]
      simp only [subst, h3' β hX.1]
      exact Relation.ReflTransGen.lift (mu _) (fun _ _ h => Step.mu _ h) _ _
        (ih (Step.ren hu _ Nat.succ_injective) (a + 1) (upS σ) (upS σ') hX.2
          (by simp [upS, h1]) (by simp [upS, h2]) h3')

/-- **The β-expansion lemma with stacks.** -/
theorem sn_apps_beta {Δ : List Entry} {C B : Ty} {u : Tm} (hu : SN u) :
    ∀ {X : Tm}, Typ (.tm C :: Δ) X B → ∀ {π : List Tm}, (∀ v ∈ π, SN v) →
      SN (apps (subst (single u) X) π) → SN (apps (app (lam X) u) π) := by
  induction hu with
  | intro u _ ihu =>
      have inner : ∀ m, SN m → ∀ X, Typ (.tm C :: Δ) X B → ∀ π, (∀ v ∈ π, SN v) →
          m = apps (subst (single u) X) π → SN (apps (app (lam X) u) π) := by
        intro m hm
        induction hm with
        | intro m hm' ihm =>
            intro X hX π hπ hmdef
            subst hmdef
            refine sn_apps_head hπ (by simp) (by simp) fun X' hX' => ?_
            cases hX' with
            | beta => exact Acc.intro _ hm'
            | appL _ h =>
                cases h with
                | lam h' =>
                    exact ihm _ (apps_step_left (Step.subst h' _ (namesVar_single_of_typ hX u)) π)
                      _ (hX.step h') π hπ rfl
            | appR _ h =>
                refine ihu _ h hX hπ (SN.rtg (Acc.intro _ hm') (apps_rtg_left ?_ π))
                exact subst_step_arg h X 0 _ _ (hX.nameFree 0 C (by simp)) rfl rfl
                  (fun i hi => by cases i with
                    | zero => exact absurd rfl hi
                    | succ i => rfl)
      intro X hX π hπ hm
      exact inner _ hm X hX π hπ rfl

end LambdaMu
