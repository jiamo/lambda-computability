/-
**Call-by-value: Plotkin's reduction, a CEK machine, and the simulation between them.**

`Start/Krivine.lean` and `Start/KrivineDecode.lean` implement call-by-name (weak head) reduction
by the Krivine machine.  This module does the same for **call-by-value**.

The calculus.  The values are the abstractions and the variables (Plotkin's `λv`).  A
call-by-value step (`Lambda.cbvstep`) contracts `(λ P) V` only when the argument `V` is a value,
and reduces an application from left to right: first the function part, then — once the
function part is a value — the argument.  It is a sub-relation of β (`Lambda.cbvstep_imp_step`)
and deterministic (`Lambda.cbvstep_deterministic`).

The machine.  A CEK machine (`CEK.State`) either *evaluates* a code in an environment, or
*returns* a closure, with a continuation: a stack of frames `arg u e` (the argument `u` still to
be evaluated in `e`) and `fn c` (the function value `c` waiting for its argument).  Closures and
environments are those of the Krivine machine; environments only ever bind values.  The
transitions are five administrative ones and one β transition, which binds the returned value in
the environment of the function's body.

The simulation, in the shape of `Start/KrivineDecode.lean`.  A state decodes
(`CEK.State.decode`) to the term obtained by plugging the unfolded closure into the evaluation
context its continuation stands for, and on the states reachable from a term (`CEK.State.Good`):

* `CEK.Trans.decode_eq` — administrative transitions do not change the decoding;
* `CEK.Trans.decode_cbvstep` — a β transition is exactly one call-by-value step;
* `CEK.Run.decode_cbvIn` — a run with `b` β transitions is a call-by-value reduction of `b` steps;
* `CEK.IsFinal.cbvNormal_decode` — a final state decodes to a call-by-value normal form;
* `CEK.eval_sound` — what the machine returns is reached by as many call-by-value steps as it
  made β transitions, and it is normal;
* `CEK.exists_final_of_cbvIn` — **conversely**, if the decoded term reaches a call-by-value
  normal form in `k` steps, the machine reaches a final state decoding to it, with exactly `k` β
  transitions (the administrative transitions always come to rest, by a size measure:
  `CEK.exists_beta_or_final`);
* `CEK.eval_complete` — the same from the initial state of a term.
-/

import Start.KrivineDecode

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ### Call-by-value reduction -/

/-- The **values** of call-by-value: abstractions and variables. -/
def IsValue : Lambda → Prop
  | Lambda.var _ => True
  | Lambda.lam _ => True
  | Lambda.app _ _ => False

@[simp] theorem isValue_var (n : ℕ) : IsValue (Lambda.var n) := trivial
@[simp] theorem isValue_lam (t : Lambda) : IsValue (Lambda.lam t) := trivial
@[simp] theorem not_isValue_app (a b : Lambda) : ¬ IsValue (Lambda.app a b) := id

/-- **One step of call-by-value reduction** (Plotkin), left to right. -/
inductive cbvstep : Lambda → Lambda → Prop
  /-- `β_v`: an abstraction applied to a value. -/
  | beta (P V : Lambda) : IsValue V → cbvstep (Lambda.app (Lambda.lam P) V) (Lambda.subst V 0 P)
  /-- Reduce the function part. -/
  | appL {M M' : Lambda} (N : Lambda) : cbvstep M M' → cbvstep (Lambda.app M N) (Lambda.app M' N)
  /-- Once the function part is a value, reduce the argument. -/
  | appR {N N' : Lambda} (V : Lambda) : IsValue V → cbvstep N N' →
      cbvstep (Lambda.app V N) (Lambda.app V N')

/-- A call-by-value normal form: a term with no call-by-value step. -/
def CbvNormal (t : Lambda) : Prop := ∀ t', ¬ cbvstep t t'

/-- Values do not reduce. -/
theorem IsValue.cbvNormal {V : Lambda} (h : IsValue V) : CbvNormal V := by
  intro t' ht
  cases ht <;> exact h

/-- Call-by-value steps are β-steps. -/
theorem cbvstep_imp_step {t t' : Lambda} (h : cbvstep t t') : Lambda.step t t' := by
  induction h with
  | beta P V _ => exact Lambda.step.beta P V
  | appL N _ ih => exact Lambda.step.app_left _ _ _ ih
  | appR V _ _ ih => exact Lambda.step.app_right _ _ _ ih

/-- **Call-by-value reduction is deterministic.** -/
theorem cbvstep_deterministic {t t₁ t₂ : Lambda} (h₁ : cbvstep t t₁) (h₂ : cbvstep t t₂) :
    t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | beta P V hV =>
      cases h₂ with
      | beta _ _ _ => rfl
      | appL _ h => cases h
      | appR _ _ h => exact absurd h (hV.cbvNormal _)
  | appL N h ih =>
      cases h₂ with
      | beta _ _ _ => cases h
      | appL _ h' => rw [ih h']
      | appR _ hV _ => exact absurd h (hV.cbvNormal _)
  | appR V hV h ih =>
      cases h₂ with
      | beta _ _ hV' => exact absurd h (hV'.cbvNormal _)
      | appL _ h' => exact absurd h' (hV.cbvNormal _)
      | appR _ _ h' => rw [ih h']

/-- `cbvIn k t u`: `t` reduces to `u` in exactly `k` call-by-value steps. -/
inductive cbvIn : ℕ → Lambda → Lambda → Prop
  /-- No step. -/
  | refl (t : Lambda) : cbvIn 0 t t
  /-- One step, then more. -/
  | cons {k : ℕ} {t u v : Lambda} : cbvstep t u → cbvIn k u v → cbvIn (k + 1) t v

theorem cbvIn.trans {k l : ℕ} {t u v : Lambda} (h₁ : cbvIn k t u) (h₂ : cbvIn l u v) :
    cbvIn (k + l) t v := by
  induction h₁ with
  | refl => simpa using h₂
  | cons h _ ih => rw [Nat.add_right_comm]; exact cbvIn.cons h (ih h₂)

theorem cbvIn.zero_eq {t u : Lambda} (h : cbvIn 0 t u) : t = u := by
  cases h
  rfl

/-- A call-by-value reduction is a β-reduction. -/
theorem cbvIn.reduces {k : ℕ} {t u : Lambda} (h : cbvIn k t u) : Lambda.reduces t u := by
  induction h with
  | refl t => exact Lambda.reduces.refl t
  | cons h _ ih => exact Lambda.reduces.step _ _ _ (cbvstep_imp_step h) ih

end Lambda

namespace CEK

open Krivine (Clos Env unfoldEnv)

/-! ### The machine -/

/-- A frame of the continuation. -/
inductive Frame where
  /-- The argument `u`, still to be evaluated in the environment `e`. -/
  | arg (u : Lambda) (e : Env)
  /-- The function value `c`, waiting for its argument. -/
  | fn (c : Clos)

/-- A state of the CEK machine. -/
inductive State where
  /-- Evaluate the code `t` in the environment `e`, with continuation `k`. -/
  | eval (t : Lambda) (e : Env) (k : List Frame)
  /-- Return the value closure `c` to the continuation `k`. -/
  | ret (c : Clos) (k : List Frame)

/-- The initial state on a term. -/
def State.init (t : Lambda) : State := .eval t [] []

/-- Administrative transitions and β transitions. -/
inductive Label where
  /-- An administrative transition. -/
  | admin : Label
  /-- A β transition. -/
  | beta : Label
  deriving DecidableEq

/-- The number of β-steps a transition performs. -/
def Label.betaCount : Label → ℕ
  | .admin => 0
  | .beta => 1

/-- **The transitions of the CEK machine.** -/
inductive Trans : Label → State → State → Prop
  /-- Evaluate the function part first. -/
  | app (t u : Lambda) (e : Env) (k : List Frame) :
      Trans .admin (.eval (.app t u) e k) (.eval t e (.arg u e :: k))
  /-- An abstraction is a value. -/
  | lam (t : Lambda) (e : Env) (k : List Frame) :
      Trans .admin (.eval (.lam t) e k) (.ret (Clos.mk (.lam t) e) k)
  /-- A bound variable returns the value it is bound to. -/
  | var (n : ℕ) (e : Env) (c : Clos) (k : List Frame) (h : e[n]? = some c) :
      Trans .admin (.eval (.var n) e k) (.ret c k)
  /-- A free variable is a value. -/
  | free (n : ℕ) (e : Env) (k : List Frame) (h : e[n]? = none) :
      Trans .admin (.eval (.var n) e k) (.ret (Clos.mk (.var n) e) k)
  /-- The function value is known: evaluate the argument. -/
  | swap (c : Clos) (u : Lambda) (e : Env) (k : List Frame) :
      Trans .admin (.ret c (.arg u e :: k)) (.eval u e (.fn c :: k))
  /-- The argument value is known: the β transition. -/
  | beta (t : Lambda) (e : Env) (v : Clos) (k : List Frame) :
      Trans .beta (.ret v (.fn (Clos.mk (.lam t) e) :: k)) (.eval t (v :: e) k)

/-- A state is **final** when no transition applies. -/
def IsFinal (s : State) : Prop := ∀ l s', ¬ Trans l s s'

/-- A run: `Run n b s s'` — `n` transitions, `b` of them β transitions. -/
inductive Run : ℕ → ℕ → State → State → Prop
  /-- The empty run. -/
  | refl (s : State) : Run 0 0 s s
  /-- One transition, followed by a run. -/
  | cons {l : Label} {n b : ℕ} {s₁ s₂ s₃ : State} :
      Trans l s₁ s₂ → Run n b s₂ s₃ → Run (n + 1) (b + l.betaCount) s₁ s₃

theorem Run.trans {n b n' b' : ℕ} {s₁ s₂ s₃ : State} (h₁ : Run n b s₁ s₂) (h₂ : Run n' b' s₂ s₃) :
    Run (n + n') (b + b') s₁ s₃ := by
  induction h₁ with
  | refl => simpa using h₂
  | @cons l n b _ _ _ ht _ ih =>
      have := Run.cons ht (ih h₂)
      rwa [show n + n' + 1 = n + 1 + n' by omega,
        show b + b' + l.betaCount = b + l.betaCount + b' by omega] at this

/-! ### The invariant: environments bind values -/

/-- A closure is **good** when its environment consists of good closures and it is a value: an
abstraction, or a variable its environment does not bind. -/
inductive Good : Clos → Prop
  /-- The only rule. -/
  | mk (t : Lambda) (e : Env) : (∀ c ∈ e, Good c) →
      ((∃ t', t = .lam t') ∨ (∃ n, t = .var n ∧ e[n]? = none)) → Good (Clos.mk t e)

/-- A frame is good when its closures are. -/
def Frame.Good : Frame → Prop
  | .arg _ e => ∀ c ∈ e, CEK.Good c
  | .fn c => CEK.Good c

/-- The invariant of the states reachable from a term. -/
def State.Good : State → Prop
  | .eval _ e k => (∀ c ∈ e, CEK.Good c) ∧ ∀ f ∈ k, f.Good
  | .ret c k => CEK.Good c ∧ ∀ f ∈ k, f.Good

theorem State.good_init (t : Lambda) : (State.init t).Good := by
  simp [State.init, State.Good]

/-- Transitions preserve the invariant. -/
theorem Trans.good {l : Label} {s s' : State} (h : Trans l s s') (hs : s.Good) : s'.Good := by
  cases h with
  | app t u e k =>
      obtain ⟨he, hk⟩ := hs
      refine ⟨he, ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact he
      · exact hk f hf
  | lam t e k =>
      obtain ⟨he, hk⟩ := hs
      exact ⟨Good.mk _ _ he (Or.inl ⟨t, rfl⟩), hk⟩
  | var n e c k hn =>
      obtain ⟨he, hk⟩ := hs
      exact ⟨he c (List.mem_of_getElem? hn), hk⟩
  | free n e k hn =>
      obtain ⟨he, hk⟩ := hs
      exact ⟨Good.mk _ _ he (Or.inr ⟨n, rfl, hn⟩), hk⟩
  | swap c u e k =>
      obtain ⟨hc, hk⟩ := hs
      refine ⟨hk (Frame.arg u e) (by simp), ?_⟩
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · exact hc
      · exact hk f (by simp [hf])
  | beta t e v k =>
      obtain ⟨hv, hk⟩ := hs
      have hfn : Good (Clos.mk (.lam t) e) := hk (Frame.fn (Clos.mk (.lam t) e)) (by simp)
      cases hfn with
      | mk _ _ he _ =>
          refine ⟨?_, fun f hf => hk f (by simp [hf])⟩
          intro c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact hv
          · exact he c hc

theorem Run.good {n b : ℕ} {s s' : State} (h : Run n b s s') (hs : s.Good) : s'.Good := by
  induction h with
  | refl => exact hs
  | cons ht _ ih => exact ih (ht.good hs)

/-- A good closure unfolds to a value. -/
theorem Good.isValue {c : Clos} (h : Good c) : Lambda.IsValue c.unfold := by
  cases h with
  | mk t e _ hv =>
      rcases hv with ⟨t', rfl⟩ | ⟨n, rfl, hn⟩
      · simp [Krivine.Clos.unfold_mk, Lambda.substEnv]
      · obtain ⟨m, hm⟩ := Krivine.unfoldEnv_of_getElem?_none hn
        rw [Krivine.Clos.unfold_mk, Lambda.substEnv, hm]
        trivial

/-! ### Decoding a state -/

/-- The evaluation context a continuation stands for, applied to a term. -/
def plug : List Frame → Lambda → Lambda
  | [], M => M
  | .arg u e :: k, M => plug k (.app M (Clos.mk u e).unfold)
  | .fn c :: k, M => plug k (.app c.unfold M)

/-- **The term a state stands for.** -/
def State.decode : State → Lambda
  | .eval t e k => plug k (Clos.mk t e).unfold
  | .ret c k => plug k c.unfold

theorem State.decode_init (t : Lambda) : (State.init t).decode = t := by
  simp only [State.init, State.decode, plug, Krivine.Clos.unfold_mk]
  have : unfoldEnv [] = fun i => Lambda.var i := by funext i; rfl
  rw [this]
  exact Lambda.substEnv_var_id t

/-- A call-by-value step inside the evaluation context of a good continuation. -/
theorem cbvstep_plug {k : List Frame} (hk : ∀ f ∈ k, f.Good) {M M' : Lambda}
    (h : Lambda.cbvstep M M') : Lambda.cbvstep (plug k M) (plug k M') := by
  induction k generalizing M M' with
  | nil => exact h
  | cons f k ih =>
      have hk' : ∀ f ∈ k, f.Good := fun f hf => hk f (by simp [hf])
      cases f with
      | arg u e => exact ih hk' (Lambda.cbvstep.appL _ h)
      | fn c =>
          have hc : Good c := hk (Frame.fn c) (by simp)
          exact ih hk' (Lambda.cbvstep.appR _ hc.isValue h)

/-- **The administrative transitions do not change the term.** -/
theorem Trans.decode_eq {s s' : State} (h : Trans .admin s s') : s.decode = s'.decode := by
  cases h with
  | app t u e k => simp [State.decode, plug, Krivine.Clos.unfold_mk, Lambda.substEnv]
  | lam t e k => rfl
  | var n e c k hn =>
      simp only [State.decode, Krivine.Clos.unfold_mk, Lambda.substEnv]
      rw [Krivine.unfoldEnv_of_getElem? hn]
  | free n e k hn => rfl
  | swap c u e k => rfl

/-- **A β transition is one call-by-value step of the decoded term.** -/
theorem Trans.decode_cbvstep {s s' : State} (h : Trans .beta s s') (hs : s.Good) :
    Lambda.cbvstep s.decode s'.decode := by
  cases h with
  | beta t e v k =>
      obtain ⟨hv, hk⟩ := hs
      simp only [State.decode, plug, Krivine.Clos.unfold_mk, Lambda.substEnv]
      refine cbvstep_plug (fun f hf => hk f (by simp [hf])) ?_
      have hbeta := Lambda.cbvstep.beta
        (Lambda.substEnv (Lambda.envCons (unfoldEnv e)) t) v.unfold hv.isValue
      rwa [Lambda.subst_zero_substEnv, ← Krivine.unfoldEnv_cons] at hbeta

/-- **The machine performs exactly the call-by-value steps**: a run with `b` β transitions is a
call-by-value reduction of `b` steps. -/
theorem Run.decode_cbvIn {n b : ℕ} {s s' : State} (h : Run n b s s') (hs : s.Good) :
    Lambda.cbvIn b s.decode s'.decode := by
  induction h with
  | refl s => exact Lambda.cbvIn.refl _
  | @cons l n b s₁ s₂ s₃ ht _ ih =>
      have ih' := ih (ht.good hs)
      cases l with
      | admin =>
          rw [Trans.decode_eq ht]
          simpa [Label.betaCount] using ih'
      | beta =>
          have := Lambda.cbvIn.cons (Trans.decode_cbvstep ht hs) ih'
          simpa [Label.betaCount, Nat.add_comm] using this

theorem Run.decode_eq_of_no_beta {n : ℕ} {s s' : State} (h : Run n 0 s s') (hs : s.Good) :
    s.decode = s'.decode := by
  exact Lambda.cbvIn.zero_eq (h.decode_cbvIn hs)

/-! ### Final states -/

/-- A term is **stuck**: not a value, and in call-by-value normal form. -/
def Stuck (M : Lambda) : Prop := ¬ Lambda.IsValue M ∧ Lambda.CbvNormal M

theorem stuck_app_left {M : Lambda} (h : Stuck M) (N : Lambda) : Stuck (Lambda.app M N) := by
  obtain ⟨hnv, hnf⟩ := h
  refine ⟨id, fun t' ht' => ?_⟩
  cases ht' with
  | beta _ _ _ => exact hnv trivial
  | appL _ h' => exact hnf _ h'
  | appR _ hV _ => exact hnv hV

theorem stuck_app_right {W M : Lambda} (hW : Lambda.IsValue W) (h : Stuck M) :
    Stuck (Lambda.app W M) := by
  obtain ⟨hnv, hnf⟩ := h
  refine ⟨id, fun t' ht' => ?_⟩
  cases ht' with
  | beta _ _ hV => exact hnv hV
  | appL _ h' => exact hW.cbvNormal _ h'
  | appR _ _ h' => exact hnf _ h'

theorem stuck_plug {k : List Frame} (hk : ∀ f ∈ k, f.Good) {M : Lambda} (h : Stuck M) :
    Stuck (plug k M) := by
  induction k generalizing M with
  | nil => exact h
  | cons f k ih =>
      have hk' : ∀ f ∈ k, f.Good := fun f hf => hk f (by simp [hf])
      cases f with
      | arg u e => exact ih hk' (stuck_app_left h _)
      | fn c =>
          have hc : Good c := hk (Frame.fn c) (by simp)
          exact ih hk' (stuck_app_right hc.isValue h)

/-- **A final state decodes to a call-by-value normal form.** -/
theorem IsFinal.cbvNormal_decode {s : State} (hf : IsFinal s) (hs : s.Good) :
    Lambda.CbvNormal s.decode := by
  cases s with
  | eval t e k =>
      exfalso
      cases t with
      | var n =>
          cases hn : e[n]? with
          | none => exact hf _ _ (Trans.free n e k hn)
          | some c => exact hf _ _ (Trans.var n e c k hn)
      | app a b => exact hf _ _ (Trans.app a b e k)
      | lam t => exact hf _ _ (Trans.lam t e k)
  | ret c k =>
      obtain ⟨hc, hk⟩ := hs
      cases k with
      | nil => exact hc.isValue.cbvNormal
      | cons f k =>
          cases f with
          | arg u e => exact absurd (Trans.swap c u e k) (hf _ _)
          | fn d =>
              have hd : Good d := hk (Frame.fn d) (by simp)
              have hk' : ∀ f ∈ k, f.Good := fun f hf => hk f (by simp [hf])
              cases hd with
              | mk t e he hv =>
                  rcases hv with ⟨t', rfl⟩ | ⟨n, rfl, hn⟩
                  · exact absurd (Trans.beta t' e c k) (hf _ _)
                  · obtain ⟨m, hm⟩ := Krivine.unfoldEnv_of_getElem?_none hn
                    have hst : Stuck (Lambda.app (Lambda.var m) c.unfold) := by
                      refine ⟨id, fun t' ht' => ?_⟩
                      cases ht' with
                      | appL _ h' => cases h'
                      | appR _ _ h' => exact hc.isValue.cbvNormal _ h'
                    have := (stuck_plug hk' hst).2
                    simpa [State.decode, plug, Krivine.Clos.unfold_mk, Lambda.substEnv, hm]
                      using this

/-- **Soundness of the machine**: if the machine halts, its result is reached from the initial
term by exactly as many call-by-value steps as it made β transitions, and it is normal. -/
theorem eval_sound {t : Lambda} {n b : ℕ} {s : State} (h : Run n b (State.init t) s)
    (hf : IsFinal s) : Lambda.cbvIn b t s.decode ∧ Lambda.CbvNormal s.decode := by
  refine ⟨?_, hf.cbvNormal_decode (h.good (State.good_init t))⟩
  have := h.decode_cbvIn (State.good_init t)
  rwa [State.decode_init] at this

/-! ### The administrative transitions come to rest -/

/-- The weight of a continuation: the arguments still to be evaluated. -/
def kWeight : List Frame → ℕ
  | [] => 0
  | .arg u _ :: k => 3 * Lambda.size u + 2 + kWeight k
  | .fn _ :: k => kWeight k

/-- The measure decreased by every administrative transition. -/
def measure : State → ℕ
  | .eval t _ k => 3 * Lambda.size t + kWeight k
  | .ret _ k => kWeight k

theorem Trans.measure_lt {s s' : State} (h : Trans .admin s s') : measure s' < measure s := by
  cases h with
  | app t u e k => simp [measure, kWeight]; omega
  | lam t e k => simp [measure]
  | var n e c k _ => simp [measure]
  | free n e k _ => simp [measure]
  | swap c u e k => simp [measure, kWeight]

/-- From any state the machine reaches, without a β transition, either a final state or one about
to perform a β transition. -/
theorem exists_beta_or_final (s : State) :
    ∃ n s', Run n 0 s s' ∧ (IsFinal s' ∨ ∃ s'', Trans .beta s' s'') := by
  induction h : measure s using Nat.strong_induction_on generalizing s with
  | _ m ih =>
      by_cases hf : IsFinal s
      · exact ⟨0, s, Run.refl s, Or.inl hf⟩
      · simp only [IsFinal, not_forall, not_not] at hf
        obtain ⟨l, s', hs'⟩ := hf
        cases l with
        | beta => exact ⟨0, s, Run.refl s, Or.inr ⟨s', hs'⟩⟩
        | admin =>
            obtain ⟨n, s'', hrun, hfin⟩ := ih _ (h ▸ hs'.measure_lt) s' rfl
            exact ⟨n + 1, s'', by simpa [Label.betaCount] using Run.cons hs' hrun, hfin⟩

/-- **Completeness of the machine**: if the term a good state stands for reaches a call-by-value
normal form in `k` steps, the machine reaches a final state that decodes to it, with exactly `k`
β transitions. -/
theorem exists_final_of_cbvIn :
    ∀ (k : ℕ) (s : State) (N : Lambda), s.Good → Lambda.cbvIn k s.decode N →
      Lambda.CbvNormal N → ∃ (n : ℕ) (s' : State), Run n k s s' ∧ IsFinal s' ∧ s'.decode = N := by
  intro k
  induction k with
  | zero =>
      intro s N hs hred hN
      cases hred
      obtain ⟨n, s', hrun, hfin⟩ := exists_beta_or_final s
      have hdec : s.decode = s'.decode := hrun.decode_eq_of_no_beta hs
      rcases hfin with hfin | ⟨s'', hbeta⟩
      · exact ⟨n, s', hrun, hfin, hdec.symm⟩
      · exfalso
        have := Trans.decode_cbvstep hbeta (hrun.good hs)
        rw [← hdec] at this
        exact hN _ this
  | succ k ih =>
      intro s N hs hred hN
      obtain ⟨n, s', hrun, hfin⟩ := exists_beta_or_final s
      have hdec : s.decode = s'.decode := hrun.decode_eq_of_no_beta hs
      have hs' : s'.Good := hrun.good hs
      cases hred with
      | @cons _ _ u _ hstep hrest =>
          rcases hfin with hfin | ⟨s'', hbeta⟩
          · exact absurd (hdec ▸ hstep) (hfin.cbvNormal_decode hs' u)
          · have hc := Trans.decode_cbvstep hbeta hs'
            rw [← hdec] at hc
            have huu : u = s''.decode := Lambda.cbvstep_deterministic hstep hc
            subst huu
            obtain ⟨n', s₃, hrun', hfin', hdec'⟩ := ih s'' N (hbeta.good hs') hrest hN
            have hstep' : Run (n' + 1) (k + 1) s' s₃ := by
              simpa [Label.betaCount] using Run.cons hbeta hrun'
            exact ⟨n + (n' + 1), s₃, by simpa using hrun.trans hstep', hfin', hdec'⟩

/-- **Completeness from a term**: if `t` reaches a call-by-value normal form `N` in `k` steps,
the machine started on `t` halts with exactly `k` β transitions, on a state decoding to `N`. -/
theorem eval_complete {t N : Lambda} {k : ℕ} (hred : Lambda.cbvIn k t N) (hN : Lambda.CbvNormal N) :
    ∃ (n : ℕ) (s : State), Run n k (State.init t) s ∧ IsFinal s ∧ s.decode = N :=
  exists_final_of_cbvIn k (State.init t) N (State.good_init t) (by rwa [State.decode_init]) hN

end CEK
