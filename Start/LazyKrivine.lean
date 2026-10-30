/-
**Call-by-need agrees with call-by-name** — tasks `M25-CBNEED-MACHINE` and `M25-CBNEED-COST`.

The lazy machine of `Start/LazyMachine.lean` is simulated by the Krivine machine of
`Start/Krivine.lean`.  A lazy state is decoded (`Lazy.dS`) into a Krivine state by reading every
heap address as the closure it was *allocated* with (`Lazy.decA`, through `Cell.orig`), and by
dropping the update markers.  Under this decoding:

* `app`, `beta`, `force` are the Krivine transitions `app`, `beta`, `var`;
* `fetch` is the Krivine `var` transition followed by the whole re-evaluation of the thunk, which
  the invariant `Lazy.Inv` records for every value cell;
* `update` is no Krivine transition at all.

Main results:

* `Lazy.sim_run` — a lazy run is simulated by a Krivine run between the decoded states, with at
  least as many β transitions;
* `Lazy.halts_iff` — **the lazy machine halts on `t` exactly when the Krivine machine does**
  (halting of the lazy machine: reaching a final state that is not a black hole);
* `Lazy.result_agree` — and then the decoded final lazy state *is* the final Krivine state, so the
  two machines compute the same weak head normal form;
* `Lazy.no_blackhole` — if the Krivine machine halts on `t`, the lazy machine never meets a
  black hole on `t`;
* `Lazy.beta_le` — **cost**: on a term on which the Krivine machine halts, the lazy machine
  makes no more β transitions than the Krivine machine.
-/

import Start.LazyMachine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lazy

open Krivine

/-! ### Decoding -/

/-- A placeholder closure. -/
def dummy : Clos := Clos.mk (.var 0) []

/-- The Krivine closure a heap address stands for: the closure it was allocated with, decoded
recursively (the guard `b < a` is always true on well-formed heaps). -/
def decA (H : List Cell) (a : ℕ) : Clos :=
  match H[a]? with
  | some cell => Clos.mk cell.orig.code
      (cell.orig.env.map fun b => if _h : b < a then decA H b else dummy)
  | none => dummy
termination_by a

theorem decA_congr {H H' : List Cell} :
    ∀ a, (∀ b ≤ a, (H[b]?).map Cell.orig = (H'[b]?).map Cell.orig) → decA H a = decA H' a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
      intro hag
      rw [decA, decA]
      have ha := hag a le_rfl
      cases h1 : H[a]? with
      | none =>
          cases h2 : H'[a]? with
          | none => rfl
          | some _ => simp [h1, h2] at ha
      | some c1 =>
          cases h2 : H'[a]? with
          | none => simp [h1, h2] at ha
          | some c2 =>
              simp only [h1, h2, Option.map_some, Option.some.injEq] at ha
              simp only
              rw [ha]
              congr 1
              refine List.map_congr_left fun b _ => ?_
              split_ifs with hb
              · exact ih b hb fun b' hb' => hag b' (by omega)
              · rfl

theorem decA_of {H : List Cell} {a : ℕ} {cell : Cell} (h : H[a]? = some cell)
    (hwf : ∀ b ∈ cell.orig.env, b < a) :
    decA H a = Clos.mk cell.orig.code (cell.orig.env.map (decA H)) := by
  rw [decA]
  simp only [h]
  congr 1
  exact List.map_congr_left fun b hb => dite_eq_left (hwf b hb)

/-- Decoding a list of addresses. -/
def decs (H : List Cell) (l : List ℕ) : List Clos := l.map (decA H)

/-- The argument addresses of a stack. -/
def argsOf : List Frame → List ℕ
  | [] => []
  | .arg a :: S => a :: argsOf S
  | .upd _ :: S => argsOf S

/-- The update-marker addresses of a stack. -/
def updsOf : List Frame → List ℕ
  | [] => []
  | .arg _ :: S => updsOf S
  | .upd a :: S => a :: updsOf S

/-- The address of a frame. -/
def Frame.addr : Frame → ℕ
  | .arg a => a
  | .upd a => a

@[simp] theorem argsOf_append (S₁ S₂ : List Frame) :
    argsOf (S₁ ++ S₂) = argsOf S₁ ++ argsOf S₂ := by
  induction S₁ with
  | nil => rfl
  | cons f S ih => cases f <;> simp [argsOf, ih]

@[simp] theorem updsOf_append (S₁ S₂ : List Frame) :
    updsOf (S₁ ++ S₂) = updsOf S₁ ++ updsOf S₂ := by
  induction S₁ with
  | nil => rfl
  | cons f S ih => cases f <;> simp [updsOf, ih]

theorem mem_updsOf {x : ℕ} {S : List Frame} (h : x ∈ updsOf S) :
    ∃ S₁ S₂, S = S₁ ++ .upd x :: S₂ := by
  induction S with
  | nil => simp [updsOf] at h
  | cons f S ih =>
      cases f with
      | arg a =>
          obtain ⟨S₁, S₂, rfl⟩ := ih h
          exact ⟨.arg a :: S₁, S₂, rfl⟩
      | upd a =>
          simp only [updsOf, List.mem_cons] at h
          rcases h with rfl | h
          · exact ⟨[], S, rfl⟩
          · obtain ⟨S₁, S₂, rfl⟩ := ih h
            exact ⟨.upd a :: S₁, S₂, rfl⟩

theorem mem_argsOf {x : ℕ} {S : List Frame} (h : x ∈ argsOf S) : Frame.arg x ∈ S := by
  induction S with
  | nil => simp [argsOf] at h
  | cons f S ih =>
      cases f with
      | arg a =>
          simp only [argsOf, List.mem_cons] at h
          rcases h with rfl | h
          · simp
          · exact List.mem_cons_of_mem _ (ih h)
      | upd a => exact List.mem_cons_of_mem _ (ih h)

/-- **The decoding of a lazy state**: addresses read as their original closures, update markers
dropped. -/
def dS (s : LState) : State := ⟨s.code, decs s.heap s.env, decs s.heap (argsOf s.stack)⟩

@[simp] theorem dS_init (t : Lambda) : dS (LState.init t) = State.init t := rfl

theorem lt_of_getElem?_some {α : Type*} {l : List α} {a : ℕ} {x : α} (h : l[a]? = some x) :
    a < l.length := by
  by_contra hge
  simp [List.getElem?_eq_none (by omega : l.length ≤ a)] at h

theorem decs_append {H : List Cell} (x : Cell) {l : List ℕ} (hl : ∀ b ∈ l, b < H.length) :
    decs (H ++ [x]) l = decs H l := by
  refine List.map_congr_left fun b hb => decA_congr b fun b' hb' => ?_
  have : b' < H.length := lt_of_le_of_lt hb' (hl b hb)
  simp [List.getElem?_append_left this]

theorem decA_set {H : List Cell} {p : ℕ} {x : Cell} (hx : ∀ y, H[p]? = some y → y.orig = x.orig)
    (b : ℕ) : decA (H.set p x) b = decA H b := by
  refine decA_congr b fun b' _ => ?_
  by_cases hbp : b' = p
  · subst hbp
    cases h : H[b']? with
    | none =>
        have : H.length ≤ b' := by
          by_contra hlt; simp [List.getElem?_eq_getElem (by omega : b' < H.length)] at h
        simp [List.getElem?_eq_none (by simpa using this : (H.set b' x).length ≤ b')]
    | some y =>
        have hlt := lt_of_getElem?_some h
        simp [List.getElem?_set_self hlt, hx y h]
  · simp [List.getElem?_set_ne (Ne.symm hbp)]

theorem decs_set {H : List Cell} {p : ℕ} {x : Cell} (hx : ∀ y, H[p]? = some y → y.orig = x.orig)
    (l : List ℕ) : decs (H.set p x) l = decs H l :=
  List.map_congr_left fun b _ => decA_set hx b

/-! ### Extending the stack of a Krivine run -/

/-- Append `ρ` to the stack of a Krivine state. -/
def ext (ρ : List Clos) (s : State) : State := ⟨s.code, s.env, s.stack ++ ρ⟩

theorem _root_.Krivine.Trans.ext {l : Label} {s s' : State} (h : Trans l s s') (ρ : List Clos) :
    Trans l (ext ρ s) (ext ρ s') := by
  cases h with
  | app t u e π => exact Trans.app t u e (π ++ ρ)
  | beta t e c π => exact Trans.beta t e c (π ++ ρ)
  | var n e c π hc => exact Trans.var n e c (π ++ ρ) hc

theorem _root_.Krivine.Run.ext {n b : ℕ} {s s' : State} (h : Run n b s s') (ρ : List Clos) :
    Run n b (ext ρ s) (ext ρ s') := by
  induction h with
  | refl s => exact Run.refl _
  | cons hstep _ ih => exact Run.cons (hstep.ext ρ) ih

theorem _root_.Krivine.Run.ext' {n b : ℕ} {t t' : Lambda} {e e' : Env} {π π' : List Clos}
    (h : Run n b ⟨t, e, π⟩ ⟨t', e', π'⟩) (ρ : List Clos) :
    Run n b ⟨t, e, π ++ ρ⟩ ⟨t', e', π' ++ ρ⟩ :=
  h.ext ρ

/-! ### The invariant -/

/-- **The invariant of the simulation.** -/
structure Inv (s : LState) : Prop where
  /-- The original environment of a cell only refers to older cells. -/
  wf : ∀ (a : ℕ) (cell : Cell), s.heap[a]? = some cell → ∀ b ∈ cell.orig.env, b < a
  /-- The environment refers to existing cells. -/
  envB : ∀ b ∈ s.env, b < s.heap.length
  /-- The stack refers to existing cells. -/
  stackB : ∀ f ∈ s.stack, f.addr < s.heap.length
  /-- A value is an abstraction, whose environment refers to existing cells, and which the
  Krivine machine reaches from the cell's original closure. -/
  val : ∀ (a : ℕ) (c v : LClos), s.heap[a]? = some (.value c v) →
    (∀ b ∈ v.env, b < s.heap.length) ∧ (∃ t, v.code = .lam t) ∧
    ∃ n b, Run n b ⟨c.code, decs s.heap c.env, []⟩ ⟨v.code, decs s.heap v.env, []⟩
  /-- Every black hole has its update marker on the stack. -/
  hole : ∀ (a : ℕ) (c : LClos), s.heap[a]? = some (.hole c) → a ∈ updsOf s.stack
  /-- No address has two update markers. -/
  updNodup : (updsOf s.stack).Nodup
  /-- Every update marker marks a black hole, and the Krivine machine reaches the current state,
  restricted to the frames above the marker, from the black hole's closure. -/
  marker : ∀ (S₁ : List Frame) (a : ℕ) (S₂ : List Frame), s.stack = S₁ ++ .upd a :: S₂ → ∃ c, s.heap[a]? = some (.hole c) ∧
    ∃ n b, Run n b ⟨c.code, decs s.heap c.env, []⟩
      ⟨s.code, decs s.heap s.env, decs s.heap (argsOf S₁)⟩

theorem inv_init (t : Lambda) : Inv (LState.init t) where
  wf := by simp [LState.init]
  envB := by simp [LState.init]
  stackB := by simp [LState.init]
  val := by simp [LState.init]
  hole := by simp [LState.init]
  updNodup := by simp [LState.init, updsOf]
  marker := by simp [LState.init]

theorem getElem?_append_single {H : List Cell} {x y : Cell} {a : ℕ} :
    (H ++ [x])[a]? = some y ↔ (a < H.length ∧ H[a]? = some y) ∨ (a = H.length ∧ y = x) := by
  rcases lt_trichotomy a H.length with h | h | h
  · simp [List.getElem?_append_left h, h, Nat.ne_of_lt h]
  · subst h; simp [eq_comm]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [reduceCtorEq, false_iff, not_or, not_and]
    exact ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega)⟩

theorem getElem?_set_some {H : List Cell} {p a : ℕ} {x y : Cell} (h : (H.set p x)[a]? = some y) :
    (a = p ∧ y = x) ∨ (a ≠ p ∧ H[a]? = some y) := by
  by_cases hap : a = p
  · subst hap
    have hlt : a < H.length := by simpa using lt_of_getElem?_some h
    rw [List.getElem?_set_self hlt] at h
    exact Or.inl ⟨rfl, (Option.some_inj.1 h).symm⟩
  · rw [List.getElem?_set_ne (Ne.symm hap)] at h
    exact Or.inr ⟨hap, h⟩

/-! ### The simulation, rule by rule -/

theorem sim_app (t u : Lambda) (e : List ℕ) (S : List Frame) (H : List Cell)
    (hI : Inv ⟨.app t u, e, S, H⟩) :
    Inv ⟨t, e, .arg H.length :: S, H ++ [.thunk ⟨u, e⟩]⟩ ∧
      Run 1 0 (dS ⟨.app t u, e, S, H⟩) (dS ⟨t, e, .arg H.length :: S, H ++ [.thunk ⟨u, e⟩]⟩) := by
  set H' := H ++ [Cell.thunk ⟨u, e⟩] with hH'
  have envB : ∀ b ∈ e, b < H.length := hI.envB
  have stackB : ∀ f ∈ S, f.addr < H.length := hI.stackB
  have hlen : H'.length = H.length + 1 := by simp [H']
  have hnew : decA H' H.length = Clos.mk u (decs H e) := by
    rw [decA_of (cell := .thunk ⟨u, e⟩) (by simp [H']) (fun b hb => hI.envB b hb)]
    simp only [Cell.orig]
    exact congrArg _ (decs_append _ hI.envB)
  have hstackB : ∀ b ∈ argsOf S, b < H.length := fun b hb => by
    simpa [Frame.addr] using hI.stackB _ (mem_argsOf hb)
  have hdecS : ∀ l : List ℕ, (∀ b ∈ l, b < H.length) → decs H' l = decs H l :=
    fun l hl => decs_append _ hl
  have hrun : ∀ π : List ℕ, (∀ b ∈ π, b < H.length) →
      Trans Label.app ⟨.app t u, decs H e, decs H π⟩ ⟨t, decs H' e, decs H' (H.length :: π)⟩ := by
    intro π hπ
    have : decs H' (H.length :: π) = Clos.mk u (decs H e) :: decs H π := by
      simp only [decs, List.map_cons]; rw [hnew]; exact congrArg _ (hdecS π hπ)
    rw [this, hdecS e hI.envB]
    exact Trans.app t u _ _
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a cell h
    rcases getElem?_append_single.1 h with ⟨_, h⟩ | ⟨rfl, rfl⟩
    · exact hI.wf a cell h
    · exact hI.envB
  · intro b hb; simp only [hlen]; have := envB b hb; omega
  · intro f hf
    simp only [List.mem_cons] at hf
    simp only [hlen]
    rcases hf with rfl | hf
    · simp [Frame.addr]
    · have := stackB f hf; omega
  · intro a c v h
    rcases getElem?_append_single.1 h with ⟨ha, h⟩ | ⟨_, h⟩
    · obtain ⟨hb, hl, n, b, hr⟩ := hI.val a c v h
      have hb' : ∀ x ∈ v.env, x < H.length := hb
      refine ⟨fun x hx => by simp only [hlen]; have := hb' x hx; omega, hl, n, b, ?_⟩
      have hc : ∀ x ∈ c.env, x < H.length := fun x hx => by
        have := hI.wf a _ h x hx
        have := lt_of_getElem?_some (show H[a]? = some _ from h); omega
      show Run n b ⟨c.code, decs H' c.env, []⟩ ⟨v.code, decs H' v.env, []⟩
      rw [hdecS _ hc, hdecS _ hb']
      exact hr
    · cases h
  · intro a c h
    rcases getElem?_append_single.1 h with ⟨_, h⟩ | ⟨_, h⟩
    · simpa [updsOf] using hI.hole a c h
    · cases h
  · simpa [updsOf] using hI.updNodup
  · intro S₁ a S₂ hS
    rcases List.cons_eq_append_iff.1 hS with ⟨rfl, h⟩ | ⟨S₁', rfl, h⟩
    · cases h
    · obtain ⟨c, hc, n, b, hr⟩ := hI.marker S₁' a S₂ h
      have hlt := lt_of_getElem?_some hc
      refine ⟨c, by simp [H', List.getElem?_append_left hlt, hc], n + 1, b + 0, ?_⟩
      have hce : ∀ x ∈ c.env, x < H.length := fun x hx => by
        have := hI.wf a _ hc x hx
        have := lt_of_getElem?_some (show H[a]? = some _ from hc); omega
      have hS₁ : ∀ x ∈ argsOf S₁', x < H.length := fun x hx => by
        apply hstackB; rw [h]; simp [hx]
      show Run (n + 1) (b + 0) ⟨c.code, decs H' c.env, []⟩
        ⟨t, decs H' e, decs H' (H.length :: argsOf S₁')⟩
      rw [hdecS _ hce]
      exact hr.trans (Run.single (hrun _ hS₁))
  · have := Run.single (hrun _ hstackB)
    simpa [dS, argsOf] using this

theorem sim_beta (t : Lambda) (e : List ℕ) (a : ℕ) (S : List Frame) (H : List Cell)
    (hI : Inv ⟨.lam t, e, .arg a :: S, H⟩) :
    Inv ⟨t, a :: e, S, H⟩ ∧ Run 1 1 (dS ⟨.lam t, e, .arg a :: S, H⟩) (dS ⟨t, a :: e, S, H⟩) := by
  have envB : ∀ b ∈ e, b < H.length := hI.envB
  have stackB : ∀ f ∈ Frame.arg a :: S, f.addr < H.length := hI.stackB
  have hstep : ∀ π : List ℕ, Trans Label.beta ⟨.lam t, decs H e, decs H (a :: π)⟩
      ⟨t, decs H (a :: e), decs H π⟩ := fun π => Trans.beta t _ _ _
  refine ⟨⟨hI.wf, ?_, ?_, hI.val, ?_, ?_, ?_⟩, ?_⟩
  · intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · simpa [Frame.addr] using stackB _ List.mem_cons_self
    · exact envB b hb
  · exact fun f hf => stackB f (List.mem_cons_of_mem _ hf)
  · intro x c h; simpa [updsOf] using hI.hole x c h
  · simpa [updsOf] using hI.updNodup
  · intro S₁ x S₂ hS
    have hS' : S = S₁ ++ Frame.upd x :: S₂ := hS
    obtain ⟨c, hc, n, b, hr⟩ := hI.marker (.arg a :: S₁) x S₂ (by simp [hS'])
    exact ⟨c, hc, n + 1, b + 1, hr.trans (Run.single (hstep (argsOf S₁)))⟩
  · simpa [dS, argsOf] using Run.single (hstep (argsOf S))

theorem sim_force (n : ℕ) (e : List ℕ) (S : List Frame) (H : List Cell) (a : ℕ) (c : LClos)
    (he : e[n]? = some a) (hc : H[a]? = some (.thunk c)) (hI : Inv ⟨.var n, e, S, H⟩) :
    Inv ⟨c.code, c.env, .upd a :: S, H.set a (.hole c)⟩ ∧
      Run 1 0 (dS ⟨.var n, e, S, H⟩) (dS ⟨c.code, c.env, .upd a :: S, H.set a (.hole c)⟩) := by
  set H' := H.set a (.hole c) with hH'
  have hlt : a < H.length := lt_of_getElem?_some hc
  have hcw : ∀ b ∈ c.env, b < a := hI.wf a _ hc
  have hD : ∀ l, decs H' l = decs H l :=
    decs_set (fun y hy => by rw [hc] at hy; cases hy; rfl)
  have hDA : ∀ b, decA H' b = decA H b := decA_set (fun y hy => by rw [hc] at hy; cases hy; rfl)
  have hdec : decA H a = Clos.mk c.code (decs H c.env) := decA_of hc hcw
  have hstep : ∀ π : List ℕ, Trans Label.var ⟨.var n, decs H e, decs H π⟩
      ⟨c.code, decs H' c.env, decs H' π⟩ := by
    intro π
    rw [hD, hD]
    have := Trans.var n (decs H e) (decA H a) (decs H π) (by simp [decs, he])
    rwa [hdec] at this
  have hnotupd : a ∉ updsOf S := by
    intro hm
    obtain ⟨S₁, S₂, hS⟩ := mem_updsOf hm
    obtain ⟨c', hc', _⟩ := hI.marker S₁ a S₂ hS
    rw [hc] at hc'; cases hc'
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x cell h
    rcases getElem?_set_some h with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · exact hcw
    · exact hI.wf x cell h
  · intro b hb; simp only [H', List.length_set]; have := hcw b hb; omega
  · intro f hf
    simp only [H', List.length_set]
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact hlt
    · exact hI.stackB f hf
  · intro x c' v h
    rcases getElem?_set_some h with ⟨_, h⟩ | ⟨_, h⟩
    · cases h
    · obtain ⟨hb, hl, k, b, hr⟩ := hI.val x c' v h
      refine ⟨by simpa [H'] using hb, hl, k, b, ?_⟩
      show Run k b ⟨c'.code, decs H' c'.env, []⟩ ⟨v.code, decs H' v.env, []⟩
      rw [hD, hD]; exact hr
  · intro x c' h
    rcases getElem?_set_some h with ⟨rfl, _⟩ | ⟨_, h⟩
    · simp [updsOf]
    · exact List.mem_cons_of_mem _ (hI.hole x c' h)
  · exact List.nodup_cons.2 ⟨hnotupd, hI.updNodup⟩
  · intro S₁ x S₂ hS
    rcases List.cons_eq_append_iff.1 hS with ⟨rfl, h⟩ | ⟨S₁', rfl, h⟩
    · simp only [List.cons.injEq, Frame.upd.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨c, by simp [H', List.getElem?_set_self hlt], 0, 0, ?_⟩
      exact Run.refl _
    · obtain ⟨c', hc', k, b, hr⟩ := hI.marker S₁' x S₂ h
      have hxa : x ≠ a := by rintro rfl; rw [hc] at hc'; cases hc'
      refine ⟨c', by simp [H', List.getElem?_set_ne (Ne.symm hxa), hc'], k + 1, b + 0, ?_⟩
      show Run (k + 1) (b + 0) ⟨c'.code, decs H' c'.env, []⟩
        ⟨c.code, decs H' c.env, decs H' (argsOf S₁')⟩
      rw [hD c'.env]
      exact hr.trans (Run.single (hstep _))
  · simpa [dS, argsOf] using Run.single (hstep (argsOf S))

theorem sim_fetch (n : ℕ) (e : List ℕ) (S : List Frame) (H : List Cell) (a : ℕ) (c v : LClos)
    (he : e[n]? = some a) (hc : H[a]? = some (.value c v)) (hI : Inv ⟨.var n, e, S, H⟩) :
    Inv ⟨v.code, v.env, S, H⟩ ∧
      ∃ k b, Run (k + 1) b (dS ⟨.var n, e, S, H⟩) (dS ⟨v.code, v.env, S, H⟩) := by
  have hcw : ∀ b ∈ c.env, b < a := hI.wf a _ hc
  have hdec : decA H a = Clos.mk c.code (decs H c.env) := decA_of hc hcw
  obtain ⟨hvb, _, k, b, hr⟩ := hI.val a c v hc
  have hrun : ∀ π : List ℕ, Run (1 + k) (0 + b) ⟨.var n, decs H e, decs H π⟩
      ⟨v.code, decs H v.env, decs H π⟩ := by
    intro π
    have h1 := Trans.var n (decs H e) (decA H a) (decs H π) (by simp [decs, he])
    rw [hdec] at h1
    have h2 := hr.ext (decs H π)
    simp only [ext, List.nil_append] at h2
    exact (Run.single h1).trans h2
  refine ⟨⟨hI.wf, hvb, hI.stackB, hI.val, hI.hole, hI.updNodup, ?_⟩, k, b, ?_⟩
  · intro S₁ x S₂ hS
    obtain ⟨c', hc', k', b', hr'⟩ := hI.marker S₁ x S₂ hS
    exact ⟨c', hc', k' + (1 + k), b' + (0 + b), hr'.trans (hrun _)⟩
  · have := hrun (argsOf S)
    rw [Nat.add_comm 1 k, Nat.zero_add] at this
    exact this

theorem sim_update (t : Lambda) (e : List ℕ) (a : ℕ) (S : List Frame) (H : List Cell) (c : LClos)
    (hc : H[a]? = some (.hole c)) (hI : Inv ⟨.lam t, e, .upd a :: S, H⟩) :
    Inv ⟨.lam t, e, S, H.set a (.value c ⟨.lam t, e⟩)⟩ ∧
      dS ⟨.lam t, e, S, H.set a (.value c ⟨.lam t, e⟩)⟩ = dS ⟨.lam t, e, .upd a :: S, H⟩ := by
  set H' := H.set a (.value c ⟨.lam t, e⟩) with hH'
  have hlt : a < H.length := lt_of_getElem?_some hc
  have hD : ∀ l, decs H' l = decs H l :=
    decs_set (fun y hy => by rw [hc] at hy; cases hy; rfl)
  have envB : ∀ b ∈ e, b < H.length := hI.envB
  have hnd : (a :: updsOf S).Nodup := hI.updNodup
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x cell h
    rcases getElem?_set_some h with ⟨rfl, rfl⟩ | ⟨_, h⟩
    · exact hI.wf _ (.hole c) hc
    · exact hI.wf x cell h
  · simpa [H'] using envB
  · intro f hf
    simpa [H'] using hI.stackB f (List.mem_cons_of_mem _ hf)
  · intro x c' v h
    rcases getElem?_set_some h with ⟨rfl, h'⟩ | ⟨_, h'⟩
    · clear h
      cases h'
      obtain ⟨c'', hc'', k, b, hr⟩ := hI.marker [] x S rfl
      rw [hc] at hc''; cases hc''
      refine ⟨by simpa [H'] using envB, ⟨t, rfl⟩, k, b, ?_⟩
      show Run k b ⟨c.code, decs H' c.env, []⟩ ⟨.lam t, decs H' e, []⟩
      rw [hD, hD]; exact hr
    · obtain ⟨hb, hl, k, b, hr⟩ := hI.val x c' v h'
      refine ⟨by simpa [H'] using hb, hl, k, b, ?_⟩
      show Run k b ⟨c'.code, decs H' c'.env, []⟩ ⟨v.code, decs H' v.env, []⟩
      rw [hD, hD]; exact hr
  · intro x c' h
    rcases getElem?_set_some h with ⟨_, h⟩ | ⟨hxa, h⟩
    · cases h
    · have := hI.hole x c' h
      simp only [updsOf, List.mem_cons] at this
      rcases this with rfl | this
      · exact absurd rfl hxa
      · exact this
  · exact (List.nodup_cons.1 hnd).2
  · intro S₁ x S₂ hS
    have hS' : S = S₁ ++ Frame.upd x :: S₂ := hS
    obtain ⟨c', hc', k, b, hr⟩ := hI.marker (.upd a :: S₁) x S₂ (by simp [hS'])
    have hxa : x ≠ a := by
      rintro rfl
      apply (List.nodup_cons.1 hnd).1
      rw [hS']; simp [updsOf]
    refine ⟨c', by simp [H', List.getElem?_set_ne (Ne.symm hxa), hc'], k, b, ?_⟩
    show Run k b ⟨c'.code, decs H' c'.env, []⟩ ⟨.lam t, decs H' e, decs H' (argsOf S₁)⟩
    rw [hD, hD, hD]; exact hr
  · simp [dS, argsOf, hD]

/-! ### One step, and runs -/

/-- **One lazy step is simulated** by a Krivine run between the decoded states, with at least as
many β transitions; only `update` is simulated by the empty run. -/
theorem sim {l : LLabel} {s s' : LState} (h : LTrans l s s') (hI : Inv s) :
    Inv s' ∧ ∃ k b, Run k b (dS s) (dS s') ∧ l.betaCount ≤ b ∧ ((l = .update ∧ k = 0) ∨ 1 ≤ k) := by
  cases h with
  | app t u e S H =>
      obtain ⟨h1, h2⟩ := sim_app t u e S H hI
      exact ⟨h1, 1, 0, h2, le_rfl, Or.inr le_rfl⟩
  | beta t e a S H =>
      obtain ⟨h1, h2⟩ := sim_beta t e a S H hI
      exact ⟨h1, 1, 1, h2, le_rfl, Or.inr le_rfl⟩
  | force n e S H a c he hc =>
      obtain ⟨h1, h2⟩ := sim_force n e S H a c he hc hI
      exact ⟨h1, 1, 0, h2, le_rfl, Or.inr le_rfl⟩
  | fetch n e S H a c v he hc =>
      obtain ⟨h1, k, b, h2⟩ := sim_fetch n e S H a c v he hc hI
      exact ⟨h1, k + 1, b, h2, Nat.zero_le _, Or.inr (by omega)⟩
  | update t e a S H c hc =>
      obtain ⟨h1, h2⟩ := sim_update t e a S H c hc hI
      exact ⟨h1, 0, 0, by rw [h2]; exact Run.refl _, le_rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- **A lazy run is simulated by a Krivine run** with at least as many β transitions. -/
theorem sim_run {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s') (hI : Inv s) :
    Inv s' ∧ ∃ k b', Run k b' (dS s) (dS s') ∧ b ≤ b' := by
  induction h with
  | refl s => exact ⟨hI, 0, 0, Run.refl _, le_rfl⟩
  | cons hstep _ ih =>
      obtain ⟨hI₂, k, b₁, hr₁, hb₁, -⟩ := sim hstep hI
      obtain ⟨hI₃, k', b', hr', hb'⟩ := ih hI₂
      exact ⟨hI₃, k + k', b₁ + b', hr₁.trans hr', by omega⟩

/-! ### Krivine runs towards a final state -/

/-- A Krivine run to a final state passes through every state the machine reaches. -/
theorem _root_.Krivine.Run.split_final {m c : ℕ} {s g : State} (hg : Run m c s g) :
    ∀ {n b : ℕ} {f : State}, Run n b s f → IsFinal f →
      m ≤ n ∧ ∃ c', Run (n - m) c' g f ∧ b = c + c' := by
  induction hg with
  | refl s => intro n b f h _; exact ⟨Nat.zero_le _, b, by simpa using h, by omega⟩
  | @cons l m c s₁ s₂ s₃ hstep _ ih =>
      intro n b f h hf
      cases h with
      | refl _ => exact absurd (Step.of_trans hstep) (hf _)
      | @cons l' n' b'' _ s₂' _ hstep' hrest =>
          obtain ⟨rfl, rfl⟩ := Trans.deterministic hstep hstep'
          obtain ⟨hle, c', hr, hb⟩ := ih hrest hf
          refine ⟨by omega, c', ?_, by omega⟩
          have : n' + 1 - (m + 1) = n' - m := by omega
          rw [this]; exact hr

/-- Two runs to final states agree. -/
theorem _root_.Krivine.Run.final_unique {m c n b : ℕ} {s g f : State} (hg : Run m c s g)
    (hgf : IsFinal g) (hf : Run n b s f) (hff : IsFinal f) : m = n ∧ c = b ∧ g = f := by
  obtain ⟨h1, c', hr, hb⟩ := hg.split_final hf hff
  obtain ⟨h2, -, -, -⟩ := hf.split_final hg hgf
  have hnm : n - m = 0 := by omega
  rw [hnm] at hr
  cases hr with
  | refl _ => exact ⟨by omega, by omega, rfl⟩

/-! ### Black holes -/

/-- A lazy state **stuck on a black hole**: a variable bound to a cell under evaluation. -/
def HoleStuck (s : LState) : Prop :=
  ∃ n a c, s.code = .var n ∧ s.env[n]? = some a ∧ s.heap[a]? = some (.hole c)

theorem ext_ext (ρ σ : List Clos) (X : State) : ext σ (ext ρ X) = ext (ρ ++ σ) X := by
  simp [ext, List.append_assoc]

/-- A Krivine state that comes back to itself with a longer stack never halts. -/
theorem loop_no_final {m b : ℕ} {ρ : List Clos} {X : State} (hX : Run (m + 1) b X (ext ρ X)) :
    ∀ (N : ℕ) (σ : List Clos) (n b' : ℕ) (f : State), n ≤ N → Run n b' (ext σ X) f →
      ¬ IsFinal f := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
      intro σ n b' f hn hf hfin
      have hX' : Run (m + 1) b (ext σ X) (ext (ρ ++ σ) X) := by
        rw [← ext_ext]; exact hX.ext σ
      obtain ⟨hle, c', hr, -⟩ := hX'.split_final hf hfin
      exact ih (n - (m + 1)) (by omega) (ρ ++ σ) (n - (m + 1)) c' f le_rfl hr hfin

theorem argsOf_split (S₁ S₂ : List Frame) (a : ℕ) :
    argsOf (S₁ ++ .upd a :: S₂) = argsOf S₁ ++ argsOf S₂ := by
  simp [argsOf]

/-- **A black hole is never met when the Krivine machine halts** from the decoded state. -/
theorem hole_absurd {s : LState} (hI : Inv s) (hs : HoleStuck s) {n b : ℕ} {f : State}
    (hf : Run n b (dS s) f) (hfin : IsFinal f) : False := by
  obtain ⟨t, e, S, H⟩ := s
  obtain ⟨k, a, c, hk, he, hc⟩ := hs
  simp only at hk he hc
  subst hk
  have hm : a ∈ updsOf S := hI.hole a c hc
  obtain ⟨S₁, S₂, rfl⟩ := mem_updsOf hm
  obtain ⟨c', hc', m, b₀, hr⟩ := hI.marker S₁ a S₂ rfl
  rw [hc] at hc'; cases hc'
  have hcw : ∀ x ∈ c.env, x < a := hI.wf a _ hc
  have hdec : decA H a = Clos.mk c.code (decs H c.env) := decA_of hc hcw
  have hstep : ∀ π, Trans Label.var ⟨.var k, decs H e, π⟩ ⟨c.code, decs H c.env, π⟩ := by
    intro π
    have := Trans.var k (decs H e) (decA H a) π (by simp [decs, he])
    rwa [hdec] at this
  set X : State := ⟨c.code, decs H c.env, []⟩
  have hX : Run (m + 1) (b₀ + 0) X (ext (decs H (argsOf S₁)) X) :=
    hr.trans (Run.single (hstep _))
  have h1 : Run 1 0 (dS ⟨.var k, e, S₁ ++ .upd a :: S₂, H⟩)
      (ext (decs H (argsOf S₂)) (ext (decs H (argsOf S₁)) X)) := by
    have := Run.single (hstep (decs H (argsOf S₁) ++ decs H (argsOf S₂)))
    simpa [dS, argsOf_split, argsOf, decs, ext, X] using this
  obtain ⟨-, c'', hr', -⟩ := h1.split_final hf hfin
  rw [ext_ext] at hr'
  exact loop_no_final hX _ _ _ _ _ le_rfl hr' hfin

/-! ### Final states -/

theorem getElem?_decs {H : List Cell} {l : List ℕ} {n : ℕ} :
    (decs H l)[n]? = (l[n]?).map (decA H) := by
  simp [decs]

/-- A final lazy state is either decoded to a final Krivine state or stuck on a black hole. -/
theorem final_cases {s : LState} (hI : Inv s) (hs : LFinal s) : IsFinal (dS s) ∨ HoleStuck s := by
  obtain ⟨t, e, S, H⟩ := s
  cases t with
  | app t u => exact absurd ⟨_, LTrans.app t u e S H⟩ (hs _)
  | lam t =>
      cases S with
      | nil =>
          left
          exact (isFinal_iff _).2 (Or.inl ⟨⟨t, rfl⟩, by simp [dS, argsOf, decs]⟩)
      | cons f S =>
          cases f with
          | arg a => exact absurd ⟨_, LTrans.beta t e a S H⟩ (hs _)
          | upd a =>
              obtain ⟨c, hc, -⟩ := hI.marker [] a S rfl
              exact absurd ⟨_, LTrans.update t e a S H c hc⟩ (hs _)
  | var n =>
      cases hn : e[n]? with
      | none =>
          left
          exact (isFinal_iff _).2 (Or.inr ⟨n, rfl, by simp [dS, getElem?_decs, hn]⟩)
      | some a =>
          have hlt : a < H.length := hI.envB a (List.mem_of_getElem? hn)
          cases hc : H[a]? with
          | none => simp [List.getElem?_eq_getElem hlt] at hc
          | some cell =>
              cases cell with
              | thunk c => exact absurd ⟨_, LTrans.force n e S H a c hn hc⟩ (hs _)
              | value c v => exact absurd ⟨_, LTrans.fetch n e S H a c v hn hc⟩ (hs _)
              | hole c => exact Or.inr ⟨n, a, c, rfl, hn, hc⟩

/-! ### Progress -/

theorem length_updsOf_cons_upd (a : ℕ) (S : List Frame) :
    (updsOf (.upd a :: S)).length = (updsOf S).length + 1 := by simp [updsOf]

/-- If the Krivine machine halts from the decoded state, the lazy machine reaches a final state. -/
theorem progress : ∀ (M : ℕ) (s : LState), Inv s → ∀ (R b : ℕ) (f : State),
    Run R b (dS s) f → IsFinal f → 2 * R + (updsOf s.stack).length ≤ M →
    ∃ n b' fs s', LRun n b' fs s s' ∧ LFinal s' := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
      intro s hI R b f hf hfin hM
      by_cases hs : LFinal s
      · exact ⟨0, 0, [], s, LRun.refl s, hs⟩
      · simp only [LFinal, not_forall, not_not] at hs
        obtain ⟨s', l, hstep⟩ := hs
        obtain ⟨hI', k, b₁, hr, -, hk⟩ := sim hstep hI
        obtain ⟨hle, c', hr', -⟩ := hr.split_final hf hfin
        have hmeas : 2 * (R - k) + (updsOf s'.stack).length <
            2 * R + (updsOf s.stack).length := by
          cases hstep with
          | app => rcases hk with ⟨h, _⟩ | hk; · cases h
                   · simp only [updsOf]; omega
          | beta => rcases hk with ⟨h, _⟩ | hk; · cases h
                    · simp only [updsOf]; omega
          | force => rcases hk with ⟨h, _⟩ | hk; · cases h
                     · simp only [updsOf, List.length_cons]; omega
          | fetch => rcases hk with ⟨h, _⟩ | hk; · cases h
                     · simp only; omega
          | update =>
              simp only [updsOf, List.length_cons]
              rcases hk with ⟨_, rfl⟩ | hk <;> omega
        obtain ⟨n, b', fs, s'', hrun, hfin'⟩ :=
          ih _ (by omega) s' hI' (R - k) c' f hr' hfin le_rfl
        exact ⟨n + 1, b' + l.betaCount, l.forced ++ fs, s'', LRun.cons hstep hrun, hfin'⟩

/-! ### Agreement -/

/-- The lazy machine **halts** on `t`: it reaches a final state that is not a black hole. -/
def LHalts (t : Lambda) : Prop :=
  ∃ n b fs s, LRun n b fs (LState.init t) s ∧ LFinal s ∧ ¬ HoleStuck s

/-- The Krivine machine halts on `t`. -/
def KHalts (t : Lambda) : Prop := ∃ n b s, Run n b (State.init t) s ∧ IsFinal s

/-- **The lazy machine halts on `t` exactly when the Krivine machine does.** -/
theorem halts_iff (t : Lambda) : LHalts t ↔ KHalts t := by
  constructor
  · rintro ⟨n, b, fs, s, hrun, hfin, hnh⟩
    obtain ⟨hI, k, b', hr, -⟩ := sim_run hrun (inv_init t)
    rcases final_cases hI hfin with h | h
    · exact ⟨k, b', dS s, by simpa using hr, h⟩
    · exact absurd h hnh
  · rintro ⟨R, b, f, hf, hfin⟩
    obtain ⟨n, b', fs, s, hrun, hfin'⟩ :=
      progress _ (LState.init t) (inv_init t) R b f (by simpa using hf) hfin le_rfl
    refine ⟨n, b', fs, s, hrun, hfin', fun hh => ?_⟩
    obtain ⟨hI, k, b'', hr, -⟩ := sim_run hrun (inv_init t)
    obtain ⟨-, c', hr', -⟩ := hr.split_final (by simpa using hf) hfin
    exact hole_absurd hI hh hr' hfin

/-- **If the Krivine machine halts on `t`, the lazy machine never meets a black hole on `t`.** -/
theorem no_blackhole {t : Lambda} (hK : KHalts t) {n b : ℕ} {fs : List ℕ} {s : LState}
    (hrun : LRun n b fs (LState.init t) s) : ¬ HoleStuck s := by
  intro hh
  obtain ⟨R, b₀, f, hf, hfin⟩ := hK
  obtain ⟨hI, k, b'', hr, -⟩ := sim_run hrun (inv_init t)
  obtain ⟨-, c', hr', -⟩ := hr.split_final (by simpa using hf) hfin
  exact hole_absurd hI hh hr' hfin

/-- **The two machines compute the same result**: the final lazy state decodes to the final
Krivine state, hence to the same weak head normal form. -/
theorem result_agree {t : Lambda} {n b : ℕ} {fs : List ℕ} {s : LState}
    (hrun : LRun n b fs (LState.init t) s) (hfin : LFinal s) {m c : ℕ} {f : State}
    (hf : Run m c (State.init t) f) (hff : IsFinal f) :
    dS s = f ∧ ∃ b', Lambda.reducesIn b' t (dS s).decode ∧ Lambda.IsWhnf (dS s).decode := by
  obtain ⟨hI, k, b', hr, -⟩ := sim_run hrun (inv_init t)
  have hr0 : Run k b' (State.init t) (dS s) := by simpa using hr
  have hnh : ¬ HoleStuck s := no_blackhole ⟨m, c, f, hf, hff⟩ hrun
  rcases final_cases hI hfin with h | h
  · obtain ⟨-, -, heq⟩ := hr0.final_unique h hf hff
    exact ⟨heq, b', eval_sound hr0 h⟩
  · exact absurd h hnh

/-- **Cost**: along any lazy run on a term on which the Krivine machine halts, the lazy machine
makes no more β transitions than the whole Krivine run. -/
theorem beta_le {t : Lambda} {n b : ℕ} {fs : List ℕ} {s : LState}
    (hrun : LRun n b fs (LState.init t) s) {m c : ℕ} {f : State}
    (hf : Run m c (State.init t) f) (hff : IsFinal f) : b ≤ c := by
  obtain ⟨-, k, b', hr, hb⟩ := sim_run hrun (inv_init t)
  obtain ⟨-, c', -, hc⟩ := (show Run k b' (State.init t) (dS s) by simpa using hr).split_final hf hff
  omega

/-- **Cost, on every weak head normalising term**: if `t` reaches a weak head normal form in at
most `k` weak head steps, the lazy machine halts on `t`, and every lazy run on `t` makes no more
β transitions than the Krivine machine makes on `t` (which is at most `k`). -/
theorem beta_le_of_whnIn {t : Lambda} {k : ℕ} (ht : Lambda.WHNIn k t) :
    LHalts t ∧ ∃ m c f, Run m c (State.init t) f ∧ IsFinal f ∧ c ≤ k ∧
      ∀ n b fs s, LRun n b fs (LState.init t) s → b ≤ c := by
  obtain ⟨m, c, f, hf, hff, hck⟩ :=
    exists_final_of_whnIn k (State.init t) (by simpa [State.decode_init] using ht)
  exact ⟨(halts_iff t).2 ⟨m, c, f, hf, hff⟩, m, c, f, hf, hff, hck,
    fun _ _ _ _ hrun => beta_le hrun hf hff⟩

end Lazy
