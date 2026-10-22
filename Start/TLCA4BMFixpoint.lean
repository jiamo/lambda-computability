import Mathlib.Tactic

/-!
# TLCA open problem 4: no fixed-point combinator from `B` and `M` (row M20-TLCA4-BM-FIXPOINT)

Combinatory terms over the constants `B`, `M` (= ω), `I` and variables, with weak reduction
`B u v w ⇒ u (v w)`, `M u ⇒ u u`, `I u ⇒ u` and weak equivalence `WEq` (its equivalence closure).

We follow the trace argument (Imamura, arXiv:2609.21765 v3):

* `li` is the deterministic leftmost-innermost step, `ann` its annotation (`some (p, q)` at an
  `M`-contraction, `none` otherwise) and `str u n` the raw annotation stream of the
  `li`-sequence of `u`.
* `Agree u v` — the trace invariant: both `li`-sequences reach the same normal term, or both
  diverge with tail-equivalent annotation streams.  `Agree` is an equivalence relation and a
  congruence (Theorem 2.9), it validates the three contractions (Theorem 2.10), hence it contains
  `WEq` (`agree_of_weq`, Theorem 2.11).
* `q_strictMono` — the duplicated-argument sizes `q` along the `li`-sequence of `P x` (`P` normal)
  strictly increase (Lemma 3.3 / Corollary 3.4), proved through the factor form
  `List.foldr app (app V A) L` with the rightmost leaf of `V` equal to `x`.
* `not_weq_iterate`, `no_fixedPoint`, `no_BMI_fixedPointCombinator`, `no_BM_fixedPointCombinator`.
-/

set_option autoImplicit false

namespace TLCA4

/-- Combinatory terms over `B`, `M`, `I` and variables. -/
inductive Tm where
  | B : Tm
  | M : Tm
  | I : Tm
  | var : ℕ → Tm
  | app : Tm → Tm → Tm
  deriving DecidableEq, Repr

namespace Tm

/-- Number of occurrences of the variable `x`. -/
def occ (x : ℕ) : Tm → ℕ
  | var y => if y = x then 1 else 0
  | app u v => occ x u + occ x v
  | _ => 0

/-- `iterX x r u = x (x (… (x u)))` with `r` copies of `x`. -/
def iterX (x : ℕ) : ℕ → Tm → Tm
  | 0, u => u
  | r + 1, u => app (var x) (iterX x r u)

/-- One weak-reduction step: a contraction anywhere in the term. -/
inductive WStep : Tm → Tm → Prop
  | b (u v w : Tm) : WStep (app (app (app B u) v) w) (app u (app v w))
  | m (u : Tm) : WStep (app M u) (app u u)
  | i (u : Tm) : WStep (app I u) u
  | appL {u u' : Tm} (v : Tm) : WStep u u' → WStep (app u v) (app u' v)
  | appR (u : Tm) {v v' : Tm} : WStep v v' → WStep (app u v) (app u v')

/-- Weak equivalence: the equivalence closure of `WStep`. -/
inductive WEq : Tm → Tm → Prop
  | step {u v : Tm} : WStep u v → WEq u v
  | refl (u : Tm) : WEq u u
  | symm {u v : Tm} : WEq u v → WEq v u
  | trans {u v w : Tm} : WEq u v → WEq v w → WEq u w

/-- Terms built from `B` and `M` only. -/
inductive IsBM : Tm → Prop
  | B : IsBM B
  | M : IsBM M
  | app {u v : Tm} : IsBM u → IsBM v → IsBM (app u v)

/-- Terms built from `B`, `M` and `I` only. -/
inductive IsBMI : Tm → Prop
  | B : IsBMI B
  | M : IsBMI M
  | I : IsBMI I
  | app {u v : Tm} : IsBMI u → IsBMI v → IsBMI (app u v)

/-! ## The leftmost-innermost step -/

/-- Root contraction of `u v`. -/
def root : Tm → Tm → Option Tm
  | app (app B a) b, v => some (app a (app b v))
  | M, v => some (app v v)
  | I, v => some v
  | _, _ => none

/-- The leftmost-innermost step. -/
def li : Tm → Option Tm
  | app u v =>
    match li u with
    | some u' => some (app u' v)
    | none =>
      match li v with
      | some v' => some (app u v')
      | none => root u v
  | _ => none

/-- Shift of the first coordinate of an annotation. -/
def shiftO (c : ℕ) (a : Option (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  a.map fun pq => (pq.1 + c, pq.2)

/-- Annotation of the root contraction. -/
def rootAnn (x : ℕ) : Tm → Tm → Option (ℕ × ℕ)
  | M, v => some (0, occ x v)
  | _, _ => none

/-- Annotation of the `li`-step: `some (p, q)` at an `M`-contraction `Γ[M v]`, with `p` the
occurrences of `x` strictly left of the redex and `q = |v|_x`; `none` otherwise. -/
def ann (x : ℕ) : Tm → Option (ℕ × ℕ)
  | app u v =>
    match li u with
    | some _ => ann x u
    | none =>
      match li v with
      | some _ => shiftO (occ x u) (ann x v)
      | none => rootAnn x u v
  | _ => none

/-- One step of the `li`-sequence (normal terms are fixed). -/
def step (t : Tm) : Tm := (li t).getD t

/-- The `li`-sequence. -/
def seq (t : Tm) (n : ℕ) : Tm := step^[n] t

/-- The raw annotation stream. -/
def str (x : ℕ) (t : Tm) (n : ℕ) : Option (ℕ × ℕ) := ann x (seq t n)

/-- The `li`-sequence of `t` terminates. -/
def Term (t : Tm) : Prop := ∃ n, li (seq t n) = none

/-- Tail equivalence of streams. -/
def TailEq {α : Type} (a b : ℕ → α) : Prop := ∃ i j, ∀ k, a (i + k) = b (j + k)

/-- The trace invariant. -/
def Agree (x : ℕ) (u v : Tm) : Prop :=
  (∃ N, li N = none ∧ (∃ n, seq u n = N) ∧ ∃ m, seq v m = N) ∨
  (¬ Term u ∧ ¬ Term v ∧ TailEq (str x u) (str x v))

/-! ## Basic facts -/

theorem li_app (u v : Tm) : li (app u v) =
    match li u with
    | some u' => some (app u' v)
    | none =>
      match li v with
      | some v' => some (app u v')
      | none => root u v := rfl

theorem ann_app (x : ℕ) (u v : Tm) : ann x (app u v) =
    match li u with
    | some _ => ann x u
    | none =>
      match li v with
      | some _ => shiftO (occ x u) (ann x v)
      | none => rootAnn x u v := rfl

theorem li_app_left {u u' : Tm} (v : Tm) (h : li u = some u') : li (app u v) = some (app u' v) := by
  rw [li_app, h]

theorem li_app_right {u v v' : Tm} (hu : li u = none) (h : li v = some v') :
    li (app u v) = some (app u v') := by
  rw [li_app, hu]; simp [h]

theorem li_app_root {u v : Tm} (hu : li u = none) (hv : li v = none) :
    li (app u v) = root u v := by
  rw [li_app, hu]; simp [hv]

theorem ann_app_left (x : ℕ) {u u' : Tm} (v : Tm) (h : li u = some u') :
    ann x (app u v) = ann x u := by
  rw [ann_app, h]

theorem ann_app_right (x : ℕ) {u v v' : Tm} (hu : li u = none) (h : li v = some v') :
    ann x (app u v) = shiftO (occ x u) (ann x v) := by
  rw [ann_app, hu]; simp [h]

theorem ann_app_root (x : ℕ) {u v : Tm} (hu : li u = none) (hv : li v = none) :
    ann x (app u v) = rootAnn x u v := by
  rw [ann_app, hu]; simp [hv]

theorem rootAnn_isSome {x : ℕ} {u v : Tm} (h : rootAnn x u v ≠ none) : root u v ≠ none := by
  cases u <;> simp_all [rootAnn, root]

theorem ann_none_of_normal (x : ℕ) : ∀ {t : Tm}, li t = none → ann x t = none
  | B, _ => rfl
  | M, _ => rfl
  | I, _ => rfl
  | var _, _ => rfl
  | app u v, h => by
    rcases hu : li u with _ | u'
    · rcases hv : li v with _ | v'
      · rw [ann_app_root x hu hv]
        rw [li_app_root hu hv] at h
        by_contra hc
        exact rootAnn_isSome hc h
      · rw [li_app_right hu hv] at h; cases h
    · rw [li_app_left v hu] at h; cases h

theorem shiftO_none (c : ℕ) : shiftO c none = none := rfl

theorem shiftO_zero (a : Option (ℕ × ℕ)) : shiftO 0 a = a := by
  cases a <;> simp [shiftO]

theorem shiftO_shiftO (c d : ℕ) (a : Option (ℕ × ℕ)) :
    shiftO c (shiftO d a) = shiftO (d + c) a := by
  cases a <;> simp [shiftO, Nat.add_assoc]

theorem step_of_li {t t' : Tm} (h : li t = some t') : step t = t' := by
  simp [step, h]

theorem step_of_normal {t : Tm} (h : li t = none) : step t = t := by
  simp [step, h]

theorem seq_zero (t : Tm) : seq t 0 = t := rfl

theorem seq_succ (t : Tm) (n : ℕ) : seq t (n + 1) = step (seq t n) :=
  Function.iterate_succ_apply' step n t

theorem seq_add (t : Tm) (n m : ℕ) : seq t (n + m) = seq (seq t n) m := by
  unfold seq
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem seq_normal {N : Tm} (h : li N = none) (k : ℕ) : seq N k = N := by
  induction k with
  | zero => rfl
  | succ k ih => rw [seq_succ, ih, step_of_normal h]

theorem seq_fixed {t N : Tm} {n : ℕ} (h : seq t n = N) (hN : li N = none) (k : ℕ) :
    seq t (n + k) = N := by
  rw [seq_add, h, seq_normal hN]

/-- Normal forms reached by an `li`-sequence are unique. -/
theorem nf_unique {t N N' : Tm} {n n' : ℕ} (h : seq t n = N) (hN : li N = none)
    (h' : seq t n' = N') (hN' : li N' = none) : N = N' := by
  have h1 := seq_fixed h hN n'
  have h2 := seq_fixed h' hN' n
  rw [Nat.add_comm] at h2
  rw [← h1, h2]

/-- A minimal index reaching a normal term. -/
theorem reach_min {t N : Tm} {n : ℕ} (h : seq t n = N) (hN : li N = none) :
    ∃ n₀, seq t n₀ = N ∧ ∀ m < n₀, li (seq t m) ≠ none := by
  classical
  have hex : ∃ m, li (seq t m) = none := ⟨n, by rw [h]; exact hN⟩
  refine ⟨Nat.find hex, ?_, fun m hm => Nat.find_min hex hm⟩
  exact nf_unique rfl (Nat.find_spec hex) h hN

theorem not_term_iff {t : Tm} : ¬ Term t ↔ ∀ n, li (seq t n) ≠ none := by
  simp [Term]

theorem term_of_reach {t N : Tm} {n : ℕ} (h : seq t n = N) (hN : li N = none) : Term t :=
  ⟨n, by rw [h]; exact hN⟩

theorem reach_of_term {t : Tm} (h : Term t) : ∃ N n, seq t n = N ∧ li N = none := by
  obtain ⟨n, hn⟩ := h
  exact ⟨_, n, rfl, hn⟩

/-! ## `Agree` is an equivalence relation -/

theorem tailEq_refl {α : Type} (a : ℕ → α) : TailEq a a := ⟨0, 0, fun _ => rfl⟩

theorem tailEq_symm {α : Type} {a b : ℕ → α} (h : TailEq a b) : TailEq b a := by
  obtain ⟨i, j, h⟩ := h
  exact ⟨j, i, fun k => (h k).symm⟩

theorem tailEq_trans {α : Type} {a b c : ℕ → α} (h₁ : TailEq a b) (h₂ : TailEq b c) :
    TailEq a c := by
  obtain ⟨i, j, h₁⟩ := h₁
  obtain ⟨j', l, h₂⟩ := h₂
  refine ⟨i + j', l + j, fun k => ?_⟩
  have e1 := h₁ (j' + k)
  have e2 := h₂ (j + k)
  rw [show i + j' + k = i + (j' + k) by omega, e1, show j + (j' + k) = j' + (j + k) by omega, e2,
    show l + (j + k) = l + j + k by omega]

theorem tailEq_map {α β : Type} (f : α → β) {a b : ℕ → α} (h : TailEq a b) :
    TailEq (fun n => f (a n)) (fun n => f (b n)) := by
  obtain ⟨i, j, h⟩ := h
  exact ⟨i, j, fun k => by simp only [h k]⟩

theorem agree_refl (x : ℕ) (t : Tm) : Agree x t t := by
  by_cases h : Term t
  · obtain ⟨N, n, hn, hN⟩ := reach_of_term h
    exact Or.inl ⟨N, hN, ⟨n, hn⟩, ⟨n, hn⟩⟩
  · exact Or.inr ⟨h, h, tailEq_refl _⟩

theorem agree_symm {x : ℕ} {u v : Tm} (h : Agree x u v) : Agree x v u := by
  rcases h with ⟨N, hN, h1, h2⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨N, hN, h2, h1⟩
  · exact Or.inr ⟨h2, h1, tailEq_symm h3⟩

theorem agree_trans {x : ℕ} {u v w : Tm} (h₁ : Agree x u v) (h₂ : Agree x v w) : Agree x u w := by
  rcases h₁ with ⟨N, hN, ⟨n1, h1⟩, ⟨m1, h1'⟩⟩ | ⟨a1, a2, a3⟩ <;>
    rcases h₂ with ⟨N', hN', ⟨n2, h2⟩, ⟨m2, h2'⟩⟩ | ⟨b1, b2, b3⟩
  · have := nf_unique h1' hN h2 hN'
    subst this
    exact Or.inl ⟨N, hN, ⟨n1, h1⟩, ⟨m2, h2'⟩⟩
  · exact absurd (term_of_reach h1' hN) b1
  · exact absurd (term_of_reach h2 hN') a2
  · exact Or.inr ⟨a1, b2, tailEq_trans a3 b3⟩

/-- Lemma 2.5: a term agrees with each of its `li`-reducts. -/
theorem agree_seq (x : ℕ) (t : Tm) (n : ℕ) : Agree x t (seq t n) := by
  by_cases h : Term t
  · obtain ⟨N, m, hm, hN⟩ := reach_of_term h
    refine Or.inl ⟨N, hN, ⟨m, hm⟩, ⟨m, ?_⟩⟩
    rw [← seq_add, Nat.add_comm]
    exact seq_fixed hm hN n
  · refine Or.inr ⟨h, ?_, n, 0, fun k => ?_⟩
    · rintro ⟨k, hk⟩
      exact h ⟨n + k, by rw [seq_add]; exact hk⟩
    · simp only [str, Nat.zero_add, seq_add]

theorem agree_of_seq {x : ℕ} {t s : Tm} {n : ℕ} (h : seq t n = s) : Agree x t s :=
  h ▸ agree_seq x t n

theorem agree_of_str {x : ℕ} {u v : Tm} (hu : ¬ Term u) (hv : ¬ Term v)
    (h : ∀ n, str x u n = str x v n) : Agree x u v :=
  Or.inr ⟨hu, hv, 0, 0, fun _ => h _⟩

/-! ## Context lemmas -/

theorem seq_app_left (u v : Tm) :
    ∀ n, (∀ m < n, li (seq u m) ≠ none) → seq (app u v) n = app (seq u n) v
  | 0, _ => rfl
  | n + 1, h => by
    have ih := seq_app_left u v n (fun m hm => h m (by omega))
    obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp (h n (by omega))
    rw [seq_succ, ih, seq_succ, step_of_li (li_app_left v hu'), step_of_li hu']

theorem seq_app_right {U : Tm} (hU : li U = none) (v : Tm) :
    ∀ n, (∀ m < n, li (seq v m) ≠ none) → seq (app U v) n = app U (seq v n)
  | 0, _ => rfl
  | n + 1, h => by
    have ih := seq_app_right hU v n (fun m hm => h m (by omega))
    obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp (h n (by omega))
    rw [seq_succ, ih, seq_succ, step_of_li (li_app_right hU hv'), step_of_li hv']

theorem str_app_left_of_not_term (x : ℕ) {u : Tm} (hu : ¬ Term u) (v : Tm) (n : ℕ) :
    str x (app u v) n = str x u n := by
  rw [not_term_iff] at hu
  obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp (hu n)
  simp only [str]
  rw [seq_app_left u v n (fun m _ => hu m), ann_app_left x v hu']

theorem not_term_app_left {u : Tm} (hu : ¬ Term u) (v : Tm) : ¬ Term (app u v) := by
  rw [not_term_iff] at hu ⊢
  intro n
  obtain ⟨u', hu'⟩ := Option.ne_none_iff_exists'.mp (hu n)
  rw [seq_app_left u v n (fun m _ => hu m), li_app_left v hu']
  simp

theorem str_app_right_of_not_term (x : ℕ) {U : Tm} (hU : li U = none) {v : Tm} (hv : ¬ Term v)
    (n : ℕ) : str x (app U v) n = shiftO (occ x U) (str x v n) := by
  rw [not_term_iff] at hv
  obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp (hv n)
  simp only [str]
  rw [seq_app_right hU v n (fun m _ => hv m), ann_app_right x hU hv']

theorem not_term_app_right {U : Tm} (hU : li U = none) {v : Tm} (hv : ¬ Term v) :
    ¬ Term (app U v) := by
  rw [not_term_iff] at hv ⊢
  intro n
  obtain ⟨v', hv'⟩ := Option.ne_none_iff_exists'.mp (hv n)
  rw [seq_app_right hU v n (fun m _ => hv m), li_app_right hU hv']
  simp

/-- If `u` terminates in `U`, then `u v` agrees with `U v`. -/
theorem agree_app_nf_left (x : ℕ) {u U : Tm} {n : ℕ} (h : seq u n = U) (hU : li U = none)
    (v : Tm) : Agree x (app u v) (app U v) := by
  obtain ⟨n₀, h₀, hmin⟩ := reach_min h hU
  exact agree_of_seq (by rw [seq_app_left u v n₀ hmin, h₀])

theorem agree_app_nf_right (x : ℕ) {U : Tm} (hU : li U = none) {v V : Tm} {n : ℕ}
    (h : seq v n = V) (hV : li V = none) : Agree x (app U v) (app U V) := by
  obtain ⟨n₀, h₀, hmin⟩ := reach_min h hV
  exact agree_of_seq (by rw [seq_app_right hU v n₀ hmin, h₀])

/-! ## Theorem 2.9: `Agree` is a congruence -/

theorem agree_congr_left {x : ℕ} {u u' : Tm} (h : Agree x u u') (v : Tm) :
    Agree x (app u v) (app u' v) := by
  rcases h with ⟨N, hN, ⟨n, hn⟩, ⟨m, hm⟩⟩ | ⟨h1, h2, h3⟩
  · exact agree_trans (agree_app_nf_left x hn hN v) (agree_symm (agree_app_nf_left x hm hN v))
  · refine Or.inr ⟨not_term_app_left h1 v, not_term_app_left h2 v, ?_⟩
    have e1 := funext (str_app_left_of_not_term x h1 v)
    have e2 := funext (str_app_left_of_not_term x h2 v)
    rw [e1, e2]; exact h3

theorem agree_congr_right_normal {x : ℕ} {U : Tm} (hU : li U = none) {v v' : Tm}
    (h : Agree x v v') : Agree x (app U v) (app U v') := by
  rcases h with ⟨N, hN, ⟨n, hn⟩, ⟨m, hm⟩⟩ | ⟨h1, h2, h3⟩
  · exact agree_trans (agree_app_nf_right x hU hn hN)
      (agree_symm (agree_app_nf_right x hU hm hN))
  · refine Or.inr ⟨not_term_app_right hU h1, not_term_app_right hU h2, ?_⟩
    have e1 := funext (str_app_right_of_not_term x hU h1)
    have e2 := funext (str_app_right_of_not_term x hU h2)
    rw [e1, e2]; exact tailEq_map _ h3

theorem agree_congr_right {x : ℕ} (u : Tm) {v v' : Tm} (h : Agree x v v') :
    Agree x (app u v) (app u v') := by
  by_cases hu : Term u
  · obtain ⟨U, n, hn, hU⟩ := reach_of_term hu
    exact agree_trans (agree_app_nf_left x hn hU v)
      (agree_trans (agree_congr_right_normal hU h) (agree_symm (agree_app_nf_left x hn hU v')))
  · refine Or.inr ⟨not_term_app_left hu v, not_term_app_left hu v', ?_⟩
    rw [funext (str_app_left_of_not_term x hu v), funext (str_app_left_of_not_term x hu v')]
    exact tailEq_refl _

theorem agree_congr {x : ℕ} {u u' v v' : Tm} (hu : Agree x u u') (hv : Agree x v v') :
    Agree x (app u v) (app u' v') :=
  agree_trans (agree_congr_left hu v) (agree_congr_right u' hv)

/-! ## Theorem 2.10: the contractions -/

theorem li_B : li B = none := rfl
theorem li_M : li M = none := rfl
theorem li_I : li I = none := rfl

theorem li_app_B {a : Tm} (ha : li a = none) : li (app B a) = none := by
  rw [li_app_root li_B ha]; rfl

theorem li_app_app_B {a b : Tm} (ha : li a = none) (hb : li b = none) :
    li (app (app B a) b) = none := by
  rw [li_app_root (li_app_B ha) hb]; rfl

/-- Normalize the argument of a context. -/
theorem agree_nf {x : ℕ} {u U : Tm} {n : ℕ} (h : seq u n = U) : Agree x u U := agree_of_seq h

theorem agree_I (x : ℕ) (u : Tm) : Agree x (app I u) u := by
  by_cases hu : Term u
  · obtain ⟨U, n, hn, hU⟩ := reach_of_term hu
    refine agree_trans (agree_congr_right I (agree_nf (x := x) hn)) ?_
    refine agree_trans (agree_of_seq (n := 1) ?_) (agree_symm (agree_nf hn))
    rw [seq_succ, seq_zero, step_of_li (li_app_root li_I hU)]
  · refine agree_of_str (not_term_app_right li_I hu) hu (fun n => ?_)
    rw [str_app_right_of_not_term x li_I hu]
    exact shiftO_zero _

theorem agree_M (x : ℕ) (u : Tm) : Agree x (app M u) (app u u) := by
  by_cases hu : Term u
  · obtain ⟨U, n, hn, hU⟩ := reach_of_term hu
    refine agree_trans (agree_congr_right M (agree_nf (x := x) hn)) ?_
    refine agree_trans (agree_of_seq (n := 1) ?_) (agree_symm (agree_congr (agree_nf hn)
      (agree_nf hn)))
    rw [seq_succ, seq_zero, step_of_li (li_app_root li_M hU)]
  · refine agree_of_str (not_term_app_right li_M hu) (not_term_app_left hu u) (fun n => ?_)
    rw [str_app_right_of_not_term x li_M hu, str_app_left_of_not_term x hu]
    exact shiftO_zero _

theorem occ_B (x : ℕ) : occ x B = 0 := rfl

theorem agree_B (x : ℕ) (a b c : Tm) :
    Agree x (app (app (app B a) b) c) (app a (app b c)) := by
  by_cases ha : Term a
  swap
  · refine agree_of_str
      (not_term_app_left (not_term_app_left (not_term_app_right li_B ha) b) c)
      (not_term_app_left ha _) (fun n => ?_)
    rw [str_app_left_of_not_term x (not_term_app_left (not_term_app_right li_B ha) b),
      str_app_left_of_not_term x (not_term_app_right li_B ha),
      str_app_right_of_not_term x li_B ha, str_app_left_of_not_term x ha, occ_B, shiftO_zero]
  obtain ⟨A, n, hn, hA⟩ := reach_of_term ha
  have eA : Agree x a A := agree_nf hn
  refine agree_trans (agree_congr_left (agree_congr_left (agree_congr_right B eA) b) c)
    (agree_trans ?_ (agree_symm (agree_congr_left eA _)))
  by_cases hb : Term b
  swap
  · have h1 : ¬ Term (app (app B A) b) := not_term_app_right (li_app_B hA) hb
    refine agree_of_str (not_term_app_left h1 c)
      (not_term_app_right hA (not_term_app_left hb c)) (fun n => ?_)
    rw [str_app_left_of_not_term x h1, str_app_right_of_not_term x (li_app_B hA) hb,
      str_app_right_of_not_term x hA (not_term_app_left hb c), str_app_left_of_not_term x hb]
    simp [occ]
  obtain ⟨B', m, hm, hB'⟩ := reach_of_term hb
  have eB : Agree x b B' := agree_nf hm
  refine agree_trans (agree_congr_left (agree_congr_right _ eB) c)
    (agree_trans ?_ (agree_symm (agree_congr_right A (agree_congr_left eB c))))
  by_cases hc : Term c
  swap
  · refine agree_of_str (not_term_app_right (li_app_app_B hA hB') hc)
      (not_term_app_right hA (not_term_app_right hB' hc)) (fun n => ?_)
    rw [str_app_right_of_not_term x (li_app_app_B hA hB') hc,
      str_app_right_of_not_term x hA (not_term_app_right hB' hc),
      str_app_right_of_not_term x hB' hc, shiftO_shiftO]
    simp [occ, Nat.add_comm]
  obtain ⟨C, k, hk, hC⟩ := reach_of_term hc
  have eC : Agree x c C := agree_nf hk
  refine agree_trans (agree_congr_right _ eC)
    (agree_trans ?_ (agree_symm (agree_congr_right A (agree_congr_right B' eC))))
  refine agree_of_seq (n := 1) ?_
  rw [seq_succ, seq_zero, step_of_li (li_app_root (li_app_app_B hA hB') hC)]

/-- Theorem 2.11: weakly equivalent terms agree. -/
theorem agree_of_wstep (x : ℕ) {u v : Tm} (h : WStep u v) : Agree x u v := by
  induction h with
  | b u v w => exact agree_B x u v w
  | m u => exact agree_M x u
  | i u => exact agree_I x u
  | appL v _ ih => exact agree_congr_left ih v
  | appR u _ ih => exact agree_congr_right u ih

theorem agree_of_weq (x : ℕ) {u v : Tm} (h : WEq u v) : Agree x u v := by
  induction h with
  | step h => exact agree_of_wstep x h
  | refl u => exact agree_refl x u
  | symm _ ih => exact agree_symm ih
  | trans _ _ ih₁ ih₂ => exact agree_trans ih₁ ih₂

/-! ## Lemma 2.1: infinitely many `M`-contractions -/

/-- Number of leaves. -/
def size : Tm → ℕ
  | app u v => size u + size v
  | _ => 1

theorem size_pos : ∀ t : Tm, 1 ≤ size t
  | app u _ => by have := size_pos u; simp only [size]; omega
  | B => le_rfl
  | M => le_rfl
  | I => le_rfl
  | var _ => le_rfl

theorem root_cases {U S c : Tm} (h : root U S = some c) :
    (U = M ∧ c = app S S) ∨ (U = I ∧ c = S) ∨
      ∃ a b, U = app (app B a) b ∧ c = app a (app b S) := by
  rcases U with _ | _ | _ | _ | ⟨_ | _ | _ | _ | ⟨_ | _ | _ | _ | _, a⟩, b⟩ <;>
    simp_all [root]

theorem root_size (x : ℕ) {u v t' : Tm} (h : root u v = some t') (h2 : rootAnn x u v = none) :
    size t' < size u + size v := by
  rcases root_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩
  · simp [rootAnn] at h2
  · simp [size]
  · simp [size]; omega

theorem shiftO_eq_none {c : ℕ} {a : Option (ℕ × ℕ)} : shiftO c a = none ↔ a = none := by
  cases a <;> simp [shiftO]

/-- `B`- and `I`-contractions lower the number of leaves. -/
theorem li_size (x : ℕ) : ∀ {t t' : Tm}, li t = some t' → ann x t = none → size t' < size t
  | app u v, t', h, ha => by
    rcases hu : li u with _ | u'
    · rcases hv : li v with _ | v'
      · rw [li_app_root hu hv] at h
        rw [ann_app_root x hu hv] at ha
        exact root_size x h ha
      · rw [li_app_right hu hv] at h
        rw [ann_app_right x hu hv, shiftO_eq_none] at ha
        cases h
        have := li_size x hv ha
        simp only [size]; omega
    · rw [li_app_left v hu] at h
      rw [ann_app_left x v hu] at ha
      cases h
      have := li_size x hu ha
      simp only [size]; omega
  | B, _, h, _ => by cases h
  | M, _, h, _ => by cases h
  | I, _, h, _ => by cases h
  | var _, _, h, _ => by cases h

/-- Lemma 2.1: a diverging `li`-sequence has an `M`-contraction after every point. -/
theorem exists_ann_of_not_term (x : ℕ) {t : Tm} (ht : ¬ Term t) (j : ℕ) :
    ∃ k, str x t (j + k) ≠ none := by
  by_contra hc
  push Not at hc
  rw [not_term_iff] at ht
  have key : ∀ k, size (seq t (j + k)) + k ≤ size (seq t j) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp (ht (j + k))
      have hs := li_size x ht' (hc k)
      rw [show j + (k + 1) = (j + k) + 1 by omega, seq_succ, step_of_li ht']
      omega
  have := key (size (seq t j) + 1)
  omega

/-! ## Occurrences along reduction -/

theorem occ_root {x : ℕ} {u v c : Tm} (h : root u v = some c) (h0 : occ x u + occ x v = 0) :
    occ x c = 0 := by
  rcases root_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ <;> simp_all [occ]

theorem occ_li {x : ℕ} : ∀ {t t' : Tm}, li t = some t' → occ x t = 0 → occ x t' = 0
  | app u v, t', h, h0 => by
    simp only [occ] at h0
    rcases hu : li u with _ | u'
    · rcases hv : li v with _ | v'
      · rw [li_app_root hu hv] at h
        exact occ_root h (by omega)
      · rw [li_app_right hu hv] at h
        cases h
        have := occ_li (x := x) hv (by omega)
        simp only [occ]; omega
    · rw [li_app_left v hu] at h
      cases h
      have := occ_li (x := x) hu (by omega)
      simp only [occ]; omega
  | B, _, h, _ => by cases h
  | M, _, h, _ => by cases h
  | I, _, h, _ => by cases h
  | var _, _, h, _ => by cases h

theorem occ_seq {x : ℕ} {t : Tm} (h0 : occ x t = 0) : ∀ n, occ x (seq t n) = 0
  | 0 => h0
  | n + 1 => by
    rw [seq_succ]
    rcases hl : li (seq t n) with _ | t'
    · rw [step_of_normal hl]; exact occ_seq h0 n
    · rw [step_of_li hl]; exact occ_li hl (occ_seq h0 n)

/-- The two coordinates of an annotation count distinct occurrences of `x`. -/
theorem ann_le_occ (x : ℕ) : ∀ {t : Tm} {p q : ℕ}, ann x t = some (p, q) → p + q ≤ occ x t
  | app u v, p, q, h => by
    rcases hu : li u with _ | u'
    · rcases hv : li v with _ | v'
      · rw [ann_app_root x hu hv] at h
        cases u <;> simp [rootAnn] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [occ]
      · rw [ann_app_right x hu hv] at h
        rcases ha : ann x v with _ | ⟨p', q'⟩
        · rw [ha] at h; cases h
        · rw [ha] at h
          simp [shiftO] at h
          obtain ⟨rfl, rfl⟩ := h
          have := ann_le_occ x ha
          simp only [occ]; omega
    · rw [ann_app_left x v hu] at h
      have := ann_le_occ x h
      simp only [occ]; omega
  | B, _, _, h => by cases h
  | M, _, _, h => by cases h
  | I, _, _, h => by cases h
  | var _, _, _, h => by cases h

/-! ## Iterated application of the variable (Lemma 3.6) -/

theorem li_app_var (y : ℕ) (w : Tm) : li (app (var y) w) = (li w).map (app (var y)) := by
  rcases hw : li w with _ | w'
  · rw [li_app_root rfl hw]; rfl
  · rw [li_app_right rfl hw]; rfl

theorem ann_app_var (x : ℕ) (w : Tm) : ann x (app (var x) w) = shiftO 1 (ann x w) := by
  rcases hw : li w with _ | w'
  · rw [ann_app_root x rfl hw, ann_none_of_normal x hw]; rfl
  · rw [ann_app_right x rfl hw]; simp [occ]

theorem li_iterX (x r : ℕ) (w : Tm) : li (iterX x r w) = (li w).map (iterX x r) := by
  induction r with
  | zero => simp [iterX]
  | succ r ih =>
    simp only [iterX]
    rw [li_app_var, ih, Option.map_map]
    rfl

theorem ann_iterX (x r : ℕ) (w : Tm) : ann x (iterX x r w) = shiftO r (ann x w) := by
  induction r with
  | zero => simp [iterX, shiftO_zero]
  | succ r ih =>
    simp only [iterX]
    rw [ann_app_var, ih, shiftO_shiftO]

theorem step_iterX (x r : ℕ) (w : Tm) : step (iterX x r w) = iterX x r (step w) := by
  rcases hw : li w with _ | w'
  · rw [step_of_normal hw, step_of_normal (by rw [li_iterX, hw]; rfl)]
  · rw [step_of_li hw, step_of_li (by rw [li_iterX, hw]; rfl)]

theorem seq_iterX (x r : ℕ) (w : Tm) : ∀ n, seq (iterX x r w) n = iterX x r (seq w n)
  | 0 => rfl
  | n + 1 => by rw [seq_succ, seq_iterX x r w n, step_iterX, ← seq_succ]

theorem str_iterX (x r : ℕ) (w : Tm) (n : ℕ) :
    str x (iterX x r w) n = shiftO r (str x w n) := by
  simp only [str, seq_iterX, ann_iterX]

theorem not_term_iterX (x r : ℕ) {w : Tm} (hw : ¬ Term w) : ¬ Term (iterX x r w) := by
  rw [not_term_iff] at hw ⊢
  intro n
  rw [seq_iterX, li_iterX]
  simpa using hw n

theorem occ_iterX (x r : ℕ) (w : Tm) : occ x (iterX x r w) = r + occ x w := by
  induction r with
  | zero => simp [iterX]
  | succ r ih => simp [iterX, occ, ih]; omega

/-! ## Lemma 3.3: the factor form and the growth of the duplicated argument -/

/-- The factor form `U₁ (U₂ (… (Uₖ W)))`. -/
def F (W : Tm) (L : List Tm) : Tm := L.foldr app W

/-- The rightmost leaf. -/
def rl : Tm → Tm
  | app _ v => rl v
  | t => t

/-- The `q`-coordinate of the annotation. -/
def annQ (x : ℕ) (t : Tm) : Option ℕ := (ann x t).map Prod.snd

theorem annQ_shiftO (c : ℕ) (a : Option (ℕ × ℕ)) : (shiftO c a).map Prod.snd = a.map Prod.snd := by
  cases a <;> rfl

theorem F_cons (W U : Tm) (L : List Tm) : F W (U :: L) = app U (F W L) := rfl

theorem F_append (W : Tm) (L₁ L₂ : List Tm) : F W (L₁ ++ L₂) = F (F W L₂) L₁ := by
  simp [F, List.foldr_append]

theorem rl_F (W : Tm) : ∀ L : List Tm, rl (F W L) = rl W
  | [] => rfl
  | _ :: L => rl_F W L

theorem occ_le_F (x : ℕ) (W : Tm) : ∀ L : List Tm, occ x W ≤ occ x (F W L)
  | [] => le_rfl
  | U :: L => by
    have := occ_le_F x W L
    rw [F_cons]; simp only [occ]; omega

theorem occ_pos_of_rl {x : ℕ} : ∀ {t : Tm}, rl t = var x → 1 ≤ occ x t
  | app u v, h => by
    have := occ_pos_of_rl (t := v) h
    simp only [occ]; omega
  | var y, h => by
    simp [rl] at h; subst h; simp [occ]
  | B, h => by cases h
  | M, h => by cases h
  | I, h => by cases h

theorem normal_app {u v : Tm} (h : li (app u v) = none) :
    li u = none ∧ li v = none ∧ root u v = none := by
  rcases hu : li u with _ | u'
  · rcases hv : li v with _ | v'
    · rw [li_app_root hu hv] at h; exact ⟨rfl, rfl, h⟩
    · rw [li_app_right hu hv] at h; cases h
  · rw [li_app_left v hu] at h; cases h

theorem li_F_inner (x : ℕ) {W W' : Tm} (hW : li W = some W') :
    ∀ L : List Tm, (∀ U ∈ L, li U = none) →
      li (F W L) = some (F W' L) ∧ annQ x (F W L) = annQ x W
  | [], _ => ⟨hW, rfl⟩
  | U :: L, hL => by
    have hU : li U = none := hL U List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := li_F_inner x hW L (fun V hV => hL V (List.mem_cons_of_mem _ hV))
    refine ⟨by rw [F_cons, li_app_right hU ih1]; rfl, ?_⟩
    rw [F_cons, annQ, ann_app_right x hU ih1, annQ_shiftO]
    exact ih2

theorem li_F_normal {W : Tm} (hW : li W = none) :
    ∀ L : List Tm, (∀ U ∈ L, li U = none) →
      li (F W L) = none ∨ ∃ L₁ U L₂, L = L₁ ++ U :: L₂ ∧ li (F W L₂) = none ∧
        li (app U (F W L₂)) ≠ none
  | [], _ => Or.inl hW
  | U :: L, hL => by
    have hU : li U = none := hL U List.mem_cons_self
    rcases li_F_normal hW L (fun V hV => hL V (List.mem_cons_of_mem _ hV)) with h | ⟨L₁, U', L₂, rfl, h1, h2⟩
    · by_cases hr : li (app U (F W L)) = none
      · exact Or.inl hr
      · exact Or.inr ⟨[], U, L, rfl, h, hr⟩
    · exact Or.inr ⟨U :: L₁, U', L₂, rfl, h1, h2⟩

/-- One `li`-step from a factor form with normal factors and normal core. -/
theorem step_cases (x : ℕ) {W : Tm} (hW : li W = none) {L : List Tm}
    (hL : ∀ U ∈ L, li U = none) {t' : Tm} (h : li (F W L) = some t') :
    (annQ x (F W L) = none ∧ ∃ L', (∀ U ∈ L', li U = none) ∧ t' = F W L') ∨
    (∃ L₁ L₂, annQ x (F W L) = some (occ x (F W L₂)) ∧ li (F W L₂) = none ∧
      t' = F (app (F W L₂) (F W L₂)) L₁ ∧ (∀ U ∈ L₁, li U = none)) := by
  rcases li_F_normal hW L hL with h0 | ⟨L₁, U, L₂, rfl, hS, hr⟩
  · rw [h0] at h; cases h
  have hU : li U = none := hL U (by simp)
  have hL₁ : ∀ V ∈ L₁, li V = none := fun V hV => hL V (by simp [hV])
  have hL₂ : ∀ V ∈ L₂, li V = none := fun V hV => hL V (by simp [hV])
  rw [li_app_root hU hS] at hr
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hr
  have hli : li (app U (F W L₂)) = some c := by rw [li_app_root hU hS]; exact hc
  obtain ⟨e1, e2⟩ := li_F_inner x hli L₁ hL₁
  have eF : F W (L₁ ++ U :: L₂) = F (app U (F W L₂)) L₁ := by rw [F_append, F_cons]
  rw [eF] at h ⊢
  rw [e1] at h
  cases h
  have eq : annQ x (app U (F W L₂)) = (rootAnn x U (F W L₂)).map Prod.snd := by
    rw [annQ, ann_app_root x hU hS]
  rw [e2, eq]
  rcases root_cases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩
  · exact Or.inr ⟨L₁, L₂, rfl, hS, rfl, hL₁⟩
  · refine Or.inl ⟨rfl, L₁ ++ L₂, ?_, by rw [F_append]⟩
    intro V hV
    rcases List.mem_append.mp hV with hV | hV
    · exact hL₁ V hV
    · exact hL₂ V hV
  · obtain ⟨hBa, hb, _⟩ := normal_app hU
    obtain ⟨_, ha, _⟩ := normal_app hBa
    refine Or.inl ⟨rfl, L₁ ++ a :: b :: L₂, ?_, by rw [F_append]; rfl⟩
    intro V hV
    simp only [List.mem_append, List.mem_cons] at hV
    rcases hV with hV | rfl | rfl | hV
    · exact hL₁ V hV
    · exact ha
    · exact hb
    · exact hL₂ V hV

/-- Factor form whose core has rightmost leaf `x`. -/
def Good (x : ℕ) (t : Tm) : Prop :=
  ∃ L W, t = F W L ∧ (∀ U ∈ L, li U = none) ∧ li W = none ∧ rl W = var x

/-- The invariant of Lemma 3.3 after an `M`-contraction with argument size `q`: the term is
`U₁ (… (Uₖ (V A)))` with all factors normal, `rl V = x`, `rl A = x` and `q ≤ |A|_x`. -/
def Inv (x : ℕ) (q : ℕ) (t : Tm) : Prop :=
  ∃ L V A, t = F (app V A) L ∧ (∀ U ∈ L, li U = none) ∧ li V = none ∧ li A = none ∧
    rl V = var x ∧ rl A = var x ∧ q ≤ occ x A

theorem good_step (x : ℕ) {t t' : Tm} (ht : Good x t) (h : li t = some t') :
    (annQ x t = none ∧ Good x t') ∨ (∃ q, annQ x t = some q ∧ Inv x q t') := by
  obtain ⟨L, W, rfl, hL, hW, hrl⟩ := ht
  rcases step_cases x hW hL h with ⟨ha, L', hL', rfl⟩ | ⟨L₁, L₂, ha, hS, rfl, hL₁⟩
  · exact Or.inl ⟨ha, L', W, rfl, hL', hW, hrl⟩
  · refine Or.inr ⟨_, ha, L₁, F W L₂, F W L₂, rfl, hL₁, hS, hS, ?_, ?_, le_rfl⟩ <;>
      (rw [rl_F]; exact hrl)

/-- Lemma 3.3: from the invariant, the next `M`-contraction has a strictly larger argument. -/
theorem inv_step (x : ℕ) {q : ℕ} {t t' : Tm} (ht : Inv x q t) (h : li t = some t') :
    (annQ x t = none ∧ Inv x q t') ∨ (∃ q', annQ x t = some q' ∧ q < q' ∧ Inv x q' t') := by
  obtain ⟨L, V, A, rfl, hL, hV, hA, hrV, hrA, hq⟩ := ht
  rcases hVA : li (app V A) with _ | W'
  · rcases step_cases x hVA hL h with ⟨ha, L', hL', rfl⟩ | ⟨L₁, L₂, ha, hS, rfl, hL₁⟩
    · exact Or.inl ⟨ha, L', V, A, rfl, hL', hV, hA, hrV, hrA, hq⟩
    · refine Or.inr ⟨_, ha, ?_, L₁, _, _, rfl, hL₁, hS, hS, ?_, ?_, le_rfl⟩
      · have h1 := occ_le_F x (app V A) L₂
        have h2 := occ_pos_of_rl hrV
        simp only [occ] at h1
        omega
      · rw [rl_F]; exact hrA
      · rw [rl_F]; exact hrA
  · obtain ⟨e1, e2⟩ := li_F_inner x hVA L hL
    rw [e1] at h
    cases h
    rw [li_app_root hV hA] at hVA
    rcases root_cases hVA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩
    · cases hrV
    · cases hrV
    · obtain ⟨hBa, hb, _⟩ := normal_app hV
      obtain ⟨_, ha, _⟩ := normal_app hBa
      refine Or.inl ⟨?_, L ++ [a], b, A, ?_, ?_, hb, hA, hrV, hrA, hq⟩
      · rw [e2, annQ, ann_app_root x hV hA]; rfl
      · rw [F_append]; rfl
      · intro U hU
        rcases List.mem_append.mp hU with hU | hU
        · exact hL U hU
        · simp at hU; subst hU; exact ha

theorem annQ_ne_none {x : ℕ} {t : Tm} (h : annQ x t ≠ none) : li t ≠ none := by
  intro hl
  apply h
  simp [annQ, ann_none_of_normal x hl]

/-- Iterating Lemma 3.3. -/
theorem inv_seq (x : ℕ) : ∀ (k : ℕ) {q q' : ℕ} {t : Tm}, Inv x q t →
    annQ x (seq t k) = some q' → q < q'
  | k, q, q', t, ht, hk => by
    rcases hl : li t with _ | t'
    · rw [seq_normal hl, annQ, ann_none_of_normal x hl] at hk; cases hk
    cases k with
    | zero =>
      rcases inv_step x ht hl with ⟨ha, _⟩ | ⟨q'', ha, hlt, _⟩
      · rw [seq_zero, ha] at hk; cases hk
      · rw [seq_zero, ha] at hk; cases hk; exact hlt
    | succ k =>
      rw [Nat.add_comm, seq_add, show seq t 1 = t' by rw [seq_succ, seq_zero, step_of_li hl]] at hk
      rcases inv_step x ht hl with ⟨_, ht'⟩ | ⟨q'', _, hlt, ht'⟩
      · exact inv_seq x k ht' hk
      · exact lt_trans hlt (inv_seq x k ht' hk)

/-- Lemma 3.2 together with the invariant: every reduct of `P x` is in factor form. -/
theorem state_seq (x : ℕ) {P : Tm} (hP : li P = none) :
    ∀ n, Good x (seq (app P (var x)) n) ∨ ∃ q, Inv x q (seq (app P (var x)) n)
  | 0 => Or.inl ⟨[P], var x, rfl, by simpa using hP, rfl, rfl⟩
  | n + 1 => by
    rw [seq_succ]
    rcases hl : li (seq (app P (var x)) n) with _ | t'
    · rw [step_of_normal hl]; exact state_seq x hP n
    rw [step_of_li hl]
    rcases state_seq x hP n with hg | ⟨q, hi⟩
    · rcases good_step x hg hl with ⟨_, h⟩ | ⟨q, _, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨q, h⟩
    · rcases inv_step x hi hl with ⟨_, h⟩ | ⟨q', _, _, h⟩
      · exact Or.inr ⟨q, h⟩
      · exact Or.inr ⟨q', h⟩

/-- Corollary 3.4: the `q`-coordinates along the `li`-sequence of `P x` strictly increase. -/
theorem q_strictMono (x : ℕ) {P : Tm} (hP : li P = none) {n m q q' : ℕ} (hnm : n < m)
    (hn : annQ x (seq (app P (var x)) n) = some q)
    (hm : annQ x (seq (app P (var x)) m) = some q') : q < q' := by
  have hl := annQ_ne_none (by rw [hn]; simp)
  obtain ⟨t', ht'⟩ := Option.ne_none_iff_exists'.mp hl
  have hinv : Inv x q t' := by
    rcases state_seq x hP n with hg | ⟨q₀, hi⟩
    · rcases good_step x hg ht' with ⟨ha, _⟩ | ⟨q₁, ha, h⟩
      · rw [ha] at hn; cases hn
      · rw [ha] at hn; cases hn; exact h
    · rcases inv_step x hi ht' with ⟨ha, _⟩ | ⟨q₁, ha, _, h⟩
      · rw [ha] at hn; cases hn
      · rw [ha] at hn; cases hn; exact h
  obtain ⟨k, rfl⟩ : ∃ k, m = n + 1 + k := ⟨m - (n + 1), by omega⟩
  rw [seq_add, seq_succ, step_of_li ht'] at hm
  exact inv_seq x k hinv hm

/-- Lemma 3.5: the stream of `P x` is not tail equivalent to its shift. -/
theorem not_tailEq_shift (x : ℕ) {P : Tm} (hP : li P = none) (hs : ¬ Term (app P (var x)))
    {r : ℕ} (hr : 1 ≤ r) :
    ¬ TailEq (str x (app P (var x))) (fun n => shiftO r (str x (app P (var x)) n)) := by
  rintro ⟨i, j, h⟩
  obtain ⟨k, hk⟩ := exists_ann_of_not_term x hs j
  obtain ⟨⟨p, q⟩, hpq⟩ := Option.ne_none_iff_exists'.mp hk
  have hi : str x (app P (var x)) (i + k) = shiftO r (str x (app P (var x)) (j + k)) := h k
  rw [hpq] at hi
  simp only [shiftO, Option.map_some] at hi
  have hni : annQ x (seq (app P (var x)) (i + k)) = some q := by
    simp only [annQ]; rw [show ann x _ = str x _ (i + k) from rfl, hi]; rfl
  have hnj : annQ x (seq (app P (var x)) (j + k)) = some q := by
    simp only [annQ]; rw [show ann x _ = str x _ (j + k) from rfl, hpq]; rfl
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact lt_irrefl _ (q_strictMono x hP (by omega) hni hnj)
  · rw [hpq] at hi; simp at hi; omega
  · exact lt_irrefl _ (q_strictMono x hP (by omega) hnj hni)

/-! ## Theorem 3.1 -/

theorem iterX_one (x : ℕ) (t : Tm) : iterX x 1 t = app (var x) t := rfl

/-- **Theorem 3.1.** For `Y` without `x` and `r ≥ 1`, `Y x` is not weakly equivalent to
`x^r (Y x)`. -/
theorem not_weq_iterate (Y : Tm) (x : ℕ) (hY : occ x Y = 0) (r : ℕ) (hr : 1 ≤ r) :
    ¬ WEq (.app Y (.var x)) (iterX x r (.app Y (.var x))) := by
  intro hw
  have hA := agree_of_weq x hw
  by_cases hYt : Term Y
  · obtain ⟨P, n, hn, hP⟩ := reach_of_term hYt
    obtain ⟨n₀, hn₀, hmin⟩ := reach_min hn hP
    have hseq : seq (app Y (var x)) n₀ = app P (var x) := by
      rw [seq_app_left Y (var x) n₀ hmin, hn₀]
    have h1 : Agree x (app Y (var x)) (app P (var x)) := agree_of_seq hseq
    have h2 : Agree x (iterX x r (app Y (var x))) (iterX x r (app P (var x))) :=
      agree_of_seq (by rw [seq_iterX, hseq])
    have hB := agree_trans (agree_symm h1) (agree_trans hA h2)
    rcases hB with ⟨N, hN, ⟨a, ha⟩, ⟨b, hb⟩⟩ | ⟨hs, _, htl⟩
    · rw [seq_iterX] at hb
      have hN₁ : li (seq (app P (var x)) b) = none := by
        have := hN; rw [← hb, li_iterX] at this; simpa using this
      have e := nf_unique ha hN rfl hN₁
      have := congrArg (occ x) hb
      rw [occ_iterX, ← e] at this
      omega
    · apply not_tailEq_shift x hP hs hr
      have : str x (iterX x r (app P (var x))) = fun n => shiftO r (str x (app P (var x)) n) :=
        funext (str_iterX x r _)
      rw [← this]; exact htl
  · have hs : ¬ Term (app Y (var x)) := not_term_app_left hYt _
    rcases hA with ⟨N, hN, ⟨a, ha⟩, _⟩ | ⟨_, _, ⟨i, j, h⟩⟩
    · exact hs (term_of_reach ha hN)
    obtain ⟨k, hk⟩ := exists_ann_of_not_term x hYt j
    obtain ⟨⟨p, q⟩, hpq⟩ := Option.ne_none_iff_exists'.mp hk
    have hi := h k
    rw [str_iterX, str_app_left_of_not_term x hYt, str_app_left_of_not_term x hYt, hpq] at hi
    simp only [shiftO, Option.map_some] at hi
    have hle := ann_le_occ x (t := seq Y (i + k)) hi
    rw [occ_seq hY] at hle
    omega

/-- **No fixed point.** For `Y` without `x`, `Y x` is not weakly equivalent to `x (Y x)`. -/
theorem no_fixedPoint (Y : Tm) (x : ℕ) (hY : occ x Y = 0) :
    ¬ WEq (.app Y (.var x)) (.app (.var x) (.app Y (.var x))) :=
  not_weq_iterate Y x hY 1 le_rfl

theorem occ_of_isBMI {Y : Tm} (h : IsBMI Y) (x : ℕ) : occ x Y = 0 := by
  induction h with
  | B => rfl
  | M => rfl
  | I => rfl
  | app _ _ ih1 ih2 => simp [occ, ih1, ih2]

theorem IsBM.isBMI {Y : Tm} (h : IsBM Y) : IsBMI Y := by
  induction h with
  | B => exact IsBMI.B
  | M => exact IsBMI.M
  | app _ _ ih1 ih2 => exact IsBMI.app ih1 ih2

/-- A fixed-point combinator under weak equivalence. -/
def IsFixedPointCombinator (Y : Tm) : Prop := ∀ F : Tm, WEq (app Y F) (app F (app Y F))

/-- No applicative combination of `B`, `M` and `I` is a fixed-point combinator under `=w`. -/
theorem no_BMI_fixedPointCombinator (Y : Tm) (hY : IsBMI Y) : ¬ IsFixedPointCombinator Y :=
  fun h => no_fixedPoint Y 0 (occ_of_isBMI hY 0) (h (var 0))

/-- **TLCA problem 4 (weak equivalence).** No applicative combination of `B` and `M` (= ω) is a
fixed-point combinator under `=w`. -/
theorem no_BM_fixedPointCombinator (Y : Tm) (hY : IsBM Y) : ¬ IsFixedPointCombinator Y :=
  no_BMI_fixedPointCombinator Y hY.isBMI

end Tm

end TLCA4
