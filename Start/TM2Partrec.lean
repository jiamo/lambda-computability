/-
# TM2-computable implies partial recursive

The machine side of the Church–Turing correspondence.  Mathlib provides the forward
translation (`Mathlib/Computability/TMToPartrec.lean` compiles partial recursive functions
into machines) and defines `Turing.TM2Computable`, but proves no reduction of machine
computability back to `Nat.Partrec`.  This file supplies that reduction.

The development is arithmetic: a configuration of a bundled machine `tm : Turing.FinTM2`
is represented by an element of the concrete `Primcodable` type

  `NCfg tm = Option (Fin nL) × Fin nS × (Fin nK → List ℕ)`,

where the finite label, state and stack-index types are transported along the canonical
equivalences with `Fin`, and stack symbols are represented by their index in `Fin (card (Γ k))`.
The one-step transition of the machine, read through this representation, is proved
primitive recursive by induction on `Turing.TM2.Stmt`; the run is then obtained by
step-indexed iteration and minimisation over the halting time.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TM2Partrec

open Turing Primrec Encodable

noncomputable section

/-! ## A primitive recursion helper: case analysis on a finite parameter -/

/-- If `f a` is primitive recursive for each `a` in a fixed list, then so is the function
that maps `b` to the list of all values `f a b`. -/
theorem primrec_map_const_list {α β σ : Type} [Primcodable β] [Primcodable σ] {f : α → β → σ}
    (h : ∀ a, Primrec (f a)) : ∀ l : List α, Primrec fun b => l.map fun a => f a b
  | [] => (Primrec.const []).of_eq (by simp)
  | a :: l => (Primrec.list_cons.comp (h a) (primrec_map_const_list h l)).of_eq (by simp)

/-- A function of two arguments whose first argument ranges over a finite type is primitive
recursive as soon as it is primitive recursive for each fixed value of that argument. -/
theorem Primrec.finite_cases {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    [Finite α] {f : α → β → σ} (h : ∀ a, Primrec (f a)) : Primrec₂ f := by
  have := decidableEqOfEncodable α
  obtain ⟨l, _, m⟩ := Finite.exists_univ_list α
  refine Primrec.option_some_iff.1 ?_
  have h1 : Primrec fun p : α × β => l.map fun a => f a p.2 :=
    (primrec_map_const_list h l).comp Primrec.snd
  have h2 : Primrec fun p : α × β => l.idxOf p.1 := (Primrec.list_idxOf₁ l).comp Primrec.fst
  refine (Primrec.list_getElem?.comp h1 h2).of_eq fun p => ?_
  rw [List.getElem?_map, List.getElem?_idxOf (m p.1), Option.map_some]

/-- A `filterMap` whose function never fails is a `map`. -/
theorem list_filterMap_eq_map {α β : Type} {f : α → Option β} {g : α → β}
    (h : ∀ x, f x = some (g x)) : ∀ l : List α, l.filterMap f = l.map g
  | [] => rfl
  | a :: l => by simp [h a, list_filterMap_eq_map h l]

/-- A `filterMap` whose function always fails yields the empty list. -/
theorem list_filterMap_eq_nil {α β : Type} {f : α → Option β} (h : ∀ x, f x = none) :
    ∀ l : List α, l.filterMap f = []
  | [] => rfl
  | a :: l => by simp [h a, list_filterMap_eq_nil h l]

/-! ## The finite data of a bundled machine -/

section Setup

variable (tm : Turing.FinTM2)

instance fintypeK : Fintype tm.K := tm.kFin
instance fintypeL : Fintype tm.Λ := tm.ΛFin
instance fintypeS : Fintype tm.σ := tm.σFin

variable [∀ k, Fintype (tm.Γ k)]

/-- Number of stacks. -/
def nK : ℕ := Fintype.card tm.K

/-- Number of function labels. -/
def nL : ℕ := Fintype.card tm.Λ

/-- Number of internal states. -/
def nS : ℕ := Fintype.card tm.σ

/-- Size of the alphabet of stack `k`. -/
def nG (k : tm.K) : ℕ := Fintype.card (tm.Γ k)

/-- Canonical numbering of the stacks. -/
def eK : tm.K ≃ Fin (nK tm) := Fintype.equivFin tm.K

/-- Canonical numbering of the function labels. -/
def eL : tm.Λ ≃ Fin (nL tm) := Fintype.equivFin tm.Λ

/-- Canonical numbering of the internal states. -/
def eS : tm.σ ≃ Fin (nS tm) := Fintype.equivFin tm.σ

/-- Canonical numbering of the alphabet of stack `k`. -/
def eG (k : tm.K) : tm.Γ k ≃ Fin (nG tm k) := Fintype.equivFin (tm.Γ k)

/-- The natural number code of a stack symbol. -/
def encG {k : tm.K} (x : tm.Γ k) : ℕ := (eG tm k x : ℕ)

theorem encG_lt {k : tm.K} (x : tm.Γ k) : encG tm x < nG tm k := (eG tm k x).isLt

/-- Decoding a natural number to a stack symbol.  Codes are read modulo the alphabet size, so
decoding fails only when the alphabet is empty. -/
def decG (k : tm.K) (n : ℕ) : Option (tm.Γ k) :=
  ((List.finRange (nG tm k))[n % nG tm k]?).map (eG tm k).symm

theorem decG_of_pos {k : tm.K} (h : 0 < nG tm k) (n : ℕ) :
    decG tm k n = some ((eG tm k).symm ⟨n % nG tm k, Nat.mod_lt _ h⟩) := by
  have : (List.finRange (nG tm k))[n % nG tm k]? = some ⟨n % nG tm k, Nat.mod_lt _ h⟩ := by
    simp [Nat.mod_lt _ h]
  simp [decG, this]

theorem decG_of_zero {k : tm.K} (h : nG tm k = 0) (n : ℕ) : decG tm k n = none := by
  simp [decG, h]

theorem decG_encG {k : tm.K} (x : tm.Γ k) : decG tm k (encG tm x) = some x := by
  have h : 0 < nG tm k := lt_of_le_of_lt (Nat.zero_le _) (encG_lt tm x)
  rw [decG_of_pos tm h]
  have : encG tm x % nG tm k = encG tm x := Nat.mod_eq_of_lt (encG_lt tm x)
  simp only [this]
  congr 1
  exact (Equiv.symm_apply_eq _).2 rfl

/-! ## Concrete representation of configurations -/

/-- Concrete representation of the collection of stacks: for each stack index, the list of
codes of its symbols. -/
abbrev NStk : Type := Fin (nK tm) → List ℕ

/-- Concrete representation of a machine configuration. -/
abbrev NCfg : Type := Option (Fin (nL tm)) × Fin (nS tm) × NStk tm

/-- The codes of the contents of stack `k`. -/
def stkCode (S : ∀ k, List (tm.Γ k)) (k : tm.K) : List ℕ := (S k).map (encG tm)

/-- Encoding of the collection of stacks. -/
def encStk (S : ∀ k, List (tm.Γ k)) : NStk tm := fun i => stkCode tm S ((eK tm).symm i)

/-- Decoding of the collection of stacks; unusable codes are dropped. -/
def decStk (g : NStk tm) : ∀ k, List (tm.Γ k) := fun k => (g (eK tm k)).filterMap (decG tm k)

theorem encStk_apply (S : ∀ k, List (tm.Γ k)) (k : tm.K) :
    encStk tm S (eK tm k) = (S k).map (encG tm) := by
  have h : encStk tm S (eK tm k) = stkCode tm S k := by
    simp [encStk, Equiv.symm_apply_apply]
  rw [h, stkCode]

theorem decStk_encStk (S : ∀ k, List (tm.Γ k)) : decStk tm (encStk tm S) = S := by
  funext k
  simp only [decStk, encStk_apply, List.filterMap_map]
  rw [list_filterMap_eq_map (f := decG tm k ∘ encG tm) (g := id) (fun x => decG_encG tm x)]
  simp

/-- Encoding of a configuration. -/
def toN (c : tm.Cfg) : NCfg tm := (c.l.map (eL tm), eS tm c.var, encStk tm c.stk)

/-- Decoding of a configuration. -/
def ofN (p : NCfg tm) : tm.Cfg :=
  ⟨p.1.map (eL tm).symm, (eS tm).symm p.2.1, decStk tm p.2.2⟩

theorem ofN_toN (c : tm.Cfg) : ofN tm (toN tm c) = c := by
  cases c with
  | mk l v S =>
    simp only [ofN, toN, decStk_encStk, Equiv.symm_apply_apply, Option.map_map,
      Equiv.symm_comp_self, Option.map_id_fun, id_eq]
    rfl

/-! ## Primitive recursiveness of the concrete stack operations -/

/-- Normalisation of a list of symbol codes for an alphabet of size `m`. -/
def normList (m : ℕ) (l : List ℕ) : List ℕ := if 0 < m then l.map (· % m) else []

theorem primrec_normList : Primrec₂ normList := by
  have h : Primrec fun p : ℕ × List ℕ => p.2.map (· % p.1) :=
    Primrec.list_map Primrec.snd (Primrec.nat_mod.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
  exact Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) Primrec.fst) h (Primrec.const [])

theorem encStk_decStk (g : NStk tm) :
    encStk tm (decStk tm g) = fun i => normList (nG tm ((eK tm).symm i)) (g i) := by
  funext i
  set k := (eK tm).symm i with hk
  have hik : eK tm k = i := by simp [hk]
  have h1 : encStk tm (decStk tm g) i = ((g i).filterMap (decG tm k)).map (encG tm) := by
    simp only [encStk, stkCode, decStk, ← hk, hik]
    rfl
  rw [h1, List.map_filterMap]
  rcases Nat.eq_zero_or_pos (nG tm k) with h | h
  · rw [list_filterMap_eq_nil (fun n => by rw [decG_of_zero tm h]; rfl)]
    simp [normList, h]
  · rw [list_filterMap_eq_map (g := fun n => n % nG tm k) (fun n => ?_)]
    · simp [normList, h]
    · rw [decG_of_pos tm h]
      simp [encG]

theorem primrec_encStk_decStk : Primrec fun g : NStk tm => encStk tm (decStk tm g) := by
  have h : Primrec fun g : NStk tm => fun i => normList (nG tm ((eK tm).symm i)) (g i) := by
    refine Primrec.fin_curry.2 ?_
    exact primrec_normList.comp
      ((Primrec.dom_finite fun i => nG tm ((eK tm).symm i)).comp Primrec.snd) Primrec.fin_app
  exact h.of_eq fun g => (encStk_decStk tm g).symm

/-- The code of the top symbol of stack `k`, as an index in the alphabet of `k`. -/
def hdCode (k : tm.K) (g : NStk tm) : Option (Fin (nG tm k)) :=
  ((g (eK tm k)).filterMap fun n => (List.finRange (nG tm k))[n % nG tm k]?).head?

theorem head?_decStk (k : tm.K) (g : NStk tm) :
    (decStk tm g k).head? = (hdCode tm k g).map (eG tm k).symm := by
  have : decStk tm g k =
      ((g (eK tm k)).filterMap fun n => (List.finRange (nG tm k))[n % nG tm k]?).map
        (eG tm k).symm := by
    rw [List.map_filterMap]
    rfl
  rw [this, List.head?_map, hdCode]

theorem primrec_hdCode {α : Type} [Primcodable α] (k : tm.K) {s : α → NStk tm}
    (hs : Primrec s) : Primrec fun a => hdCode tm k (s a) := by
  have h1 : Primrec fun a : α => s a (eK tm k) :=
    Primrec.fin_app.comp hs (Primrec.const (eK tm k))
  have h2 : Primrec₂ fun (_ : α) (n : ℕ) => (List.finRange (nG tm k))[n % nG tm k]? :=
    Primrec.list_getElem?.comp (Primrec.const _)
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const _))
  exact Primrec.list_head?.comp (Primrec.listFilterMap h1 h2)

/-- Pushing a symbol code onto stack `k`. -/
def pushCode (k : tm.K) (n : ℕ) (g : NStk tm) : NStk tm :=
  Function.update g (eK tm k) (n :: g (eK tm k))

/-- Popping stack `k`. -/
def popCode (k : tm.K) (g : NStk tm) : NStk tm :=
  Function.update g (eK tm k) (g (eK tm k)).tail

theorem decStk_pushCode (k : tm.K) (x : tm.Γ k) (g : NStk tm) :
    decStk tm (pushCode tm k (encG tm x) g) =
      Function.update (decStk tm g) k (x :: decStk tm g k) := by
  funext k'
  by_cases h : k' = k
  · subst h
    simp only [decStk, pushCode, Function.update_self, List.filterMap_cons, decG_encG]
  · have h1 : eK tm k' ≠ eK tm k := fun hh => h ((eK tm).injective hh)
    simp only [decStk, pushCode, Function.update_of_ne h1, Function.update_of_ne h]

theorem decStk_popCode (k : tm.K) (g : NStk tm) :
    decStk tm (popCode tm k g) = Function.update (decStk tm g) k (decStk tm g k).tail := by
  funext k'
  by_cases h : k' = k
  · subst h
    have key : ∀ l : List ℕ, l.tail.filterMap (decG tm k') = (l.filterMap (decG tm k')).tail := by
      intro l
      rcases Nat.eq_zero_or_pos (nG tm k') with hz | hp
      · rw [list_filterMap_eq_nil (decG_of_zero tm hz), list_filterMap_eq_nil (decG_of_zero tm hz)]
        rfl
      · rw [list_filterMap_eq_map (decG_of_pos tm hp), list_filterMap_eq_map (decG_of_pos tm hp),
          List.map_tail]
    simp only [decStk, popCode, Function.update_self]
    exact key _
  · have h1 : eK tm k' ≠ eK tm k := fun hh => h ((eK tm).injective hh)
    simp only [decStk, popCode, Function.update_of_ne h1, Function.update_of_ne h]

omit [∀ k, Fintype (tm.Γ k)] in
theorem primrec_pushCode {α : Type} [Primcodable α] (k : tm.K) {c : α → ℕ} {s : α → NStk tm}
    (hc : Primrec c) (hs : Primrec s) : Primrec fun a => pushCode tm k (c a) (s a) := by
  refine Primrec.fin_curry.2 ?_
  have happ : Primrec fun p : α × Fin (nK tm) => s p.1 p.2 :=
    Primrec.fin_app.comp (hs.comp Primrec.fst) Primrec.snd
  have hat : Primrec fun p : α × Fin (nK tm) => s p.1 (eK tm k) :=
    Primrec.fin_app.comp (hs.comp Primrec.fst) (Primrec.const _)
  have := Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const (eK tm k)))
    (Primrec.list_cons.comp (hc.comp Primrec.fst) hat) happ
  exact this.of_eq fun p => by simp [pushCode, Function.update_apply]

omit [∀ k, Fintype (tm.Γ k)] in
theorem primrec_popCode {α : Type} [Primcodable α] (k : tm.K) {s : α → NStk tm}
    (hs : Primrec s) : Primrec fun a => popCode tm k (s a) := by
  refine Primrec.fin_curry.2 ?_
  have happ : Primrec fun p : α × Fin (nK tm) => s p.1 p.2 :=
    Primrec.fin_app.comp (hs.comp Primrec.fst) Primrec.snd
  have hat : Primrec fun p : α × Fin (nK tm) => s p.1 (eK tm k) :=
    Primrec.fin_app.comp (hs.comp Primrec.fst) (Primrec.const _)
  have := Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const (eK tm k)))
    (Primrec.list_tail.comp hat) happ
  exact this.of_eq fun p => by simp [popCode, Function.update_apply]

/-! ## The one-step transition is primitive recursive -/

/-- The body of the transition function, read through the concrete representation. -/
def nStepAux (q : TM2.Stmt tm.Γ tm.Λ tm.σ) (p : Fin (nS tm) × NStk tm) : NCfg tm :=
  toN tm (TM2.stepAux q ((eS tm).symm p.1) (decStk tm p.2))

/-- The new internal state after a `peek` or `pop` on stack `k`. -/
def peekState (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) (p : Fin (nS tm) × NStk tm) :
    Fin (nS tm) :=
  eS tm (f ((eS tm).symm p.1) ((hdCode tm k p.2).map (eG tm k).symm))

theorem primrec_peekState (k : tm.K) (f : tm.σ → Option (tm.Γ k) → tm.σ) :
    Primrec (peekState tm k f) := by
  have hpair : Primrec fun p : Fin (nS tm) × NStk tm => (p.1, hdCode tm k p.2) :=
    Primrec.pair Primrec.fst (primrec_hdCode tm k Primrec.snd)
  exact (Primrec.dom_finite fun r : Fin (nS tm) × Option (Fin (nG tm k)) =>
    eS tm (f ((eS tm).symm r.1) (r.2.map (eG tm k).symm))).comp hpair

theorem primrec_nStepAux : ∀ q : TM2.Stmt tm.Γ tm.Λ tm.σ, Primrec (nStepAux tm q)
  | .push k f q => by
      have hc : Primrec fun p : Fin (nS tm) × NStk tm => encG tm (f ((eS tm).symm p.1)) :=
        (Primrec.dom_finite fun a : Fin (nS tm) => encG tm (f ((eS tm).symm a))).comp Primrec.fst
      have h := (primrec_nStepAux q).comp
        (Primrec.pair Primrec.fst (primrec_pushCode tm k hc Primrec.snd))
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux, decStk_pushCode]
  | .peek k f q => by
      have h := (primrec_nStepAux q).comp
        (Primrec.pair (primrec_peekState tm k f) Primrec.snd)
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux, peekState, Equiv.symm_apply_apply,
        ← head?_decStk tm k p.2]
  | .pop k f q => by
      have h := (primrec_nStepAux q).comp
        (Primrec.pair (primrec_peekState tm k f) (primrec_popCode tm k Primrec.snd))
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux, peekState, Equiv.symm_apply_apply,
        ← head?_decStk tm k p.2, decStk_popCode]
  | .load a q => by
      have hc : Primrec fun p : Fin (nS tm) × NStk tm => eS tm (a ((eS tm).symm p.1)) :=
        (Primrec.dom_finite fun r : Fin (nS tm) => eS tm (a ((eS tm).symm r))).comp Primrec.fst
      have h := (primrec_nStepAux q).comp (Primrec.pair hc Primrec.snd)
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux, Equiv.symm_apply_apply]
  | .branch f q₁ q₂ => by
      have hc : Primrec fun p : Fin (nS tm) × NStk tm => f ((eS tm).symm p.1) :=
        (Primrec.dom_finite fun r : Fin (nS tm) => f ((eS tm).symm r)).comp Primrec.fst
      have h := Primrec.cond hc (primrec_nStepAux q₁) (primrec_nStepAux q₂)
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux]
      cases f ((eS tm).symm p.1) <;> rfl
  | .goto f => by
      have hc : Primrec fun p : Fin (nS tm) × NStk tm => some (eL tm (f ((eS tm).symm p.1))) :=
        (Primrec.dom_finite fun r : Fin (nS tm) => some (eL tm (f ((eS tm).symm r)))).comp
          Primrec.fst
      have h := Primrec.pair hc
        (Primrec.pair Primrec.fst (primrec_encStk_decStk tm |>.comp Primrec.snd))
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux, toN, Equiv.apply_symm_apply, Option.map_some]
  | .halt => by
      have h : Primrec fun p : Fin (nS tm) × NStk tm =>
          ((none : Option (Fin (nL tm))), p.1, encStk tm (decStk tm p.2)) :=
        Primrec.pair (Primrec.const none)
          (Primrec.pair Primrec.fst (primrec_encStk_decStk tm |>.comp Primrec.snd))
      refine h.of_eq fun p => ?_
      simp only [nStepAux, TM2.stepAux, toN, Equiv.apply_symm_apply, Option.map_none]

/-- The one-step transition of the machine, read through the concrete representation. -/
def nstep (p : NCfg tm) : Option (NCfg tm) := (tm.step (ofN tm p)).map (toN tm)

theorem primrec_nstep : Primrec (nstep tm) := by
  have hg : Primrec₂ fun (p : NCfg tm) (a : Fin (nL tm)) =>
      some (nStepAux tm (tm.m ((eL tm).symm a)) (p.2.1, p.2.2)) := by
    have h1 : Primrec₂ fun (a : Fin (nL tm)) (r : Fin (nS tm) × NStk tm) =>
        nStepAux tm (tm.m ((eL tm).symm a)) r :=
      Primrec.finite_cases fun a => primrec_nStepAux tm (tm.m ((eL tm).symm a))
    exact Primrec.option_some.comp (h1.comp Primrec.snd
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have h := Primrec.option_casesOn (o := fun p : NCfg tm => p.1) Primrec.fst
    (Primrec.const none) hg
  refine h.of_eq fun p => ?_
  obtain ⟨l, v, S⟩ := p
  cases l with
  | none => simp only [nstep, ofN, Turing.FinTM2.step, TM2.step]; rfl
  | some a => simp only [nstep, ofN, Turing.FinTM2.step, TM2.step, nStepAux]; rfl

/-! ## Step-indexed iteration -/

/-- Iterating the concrete transition `t` times. -/
def nrun (p : NCfg tm) : ℕ → Option (NCfg tm)
  | 0 => some p
  | t + 1 => (nrun p t).bind (nstep tm)

theorem primrec_nrun : Primrec₂ (nrun tm) := by
  have hg : Primrec₂ fun (_ : NCfg tm) (r : ℕ × Option (NCfg tm)) => r.2.bind (nstep tm) :=
    Primrec.option_bind (Primrec.snd.comp Primrec.snd) ((primrec_nstep tm).comp Primrec.snd)
  have h := Primrec.nat_rec (f := fun p : NCfg tm => some p) Primrec.option_some hg
  refine h.of_eq fun p t => ?_
  induction t with
  | zero => rfl
  | succ t ih => simpa [nrun] using congrArg (fun o => Option.bind o (nstep tm)) ih

theorem nstep_toN (c : tm.Cfg) : nstep tm (toN tm c) = (tm.step c).map (toN tm) := by
  rw [nstep, ofN_toN]


/-- The concrete iteration simulates the machine. -/
theorem nrun_toN (c : tm.Cfg) (t : ℕ) :
    nrun tm (toN tm c) t = ((flip Bind.bind tm.step)^[t] (some c)).map (toN tm) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [nrun, ih, Function.iterate_succ_apply']
      cases h : (flip Bind.bind tm.step)^[t] (some c) with
      | none => simp only [flip]; rfl
      | some d => simp only [flip]; exact nstep_toN tm d

theorem nrun_none_mono {p : NCfg tm} {t t' : ℕ} (h : nrun tm p t = none) (hle : t ≤ t') :
    nrun tm p t' = none := by
  induction t' with
  | zero =>
      have : t = 0 := Nat.le_zero.1 hle
      rwa [this] at h
  | succ m ih =>
      rcases Nat.lt_or_ge t (m + 1) with hlt | hge
      · rw [nrun, ih (Nat.lt_succ_iff.1 hlt)]
        rfl
      · have hEq : t = m + 1 := le_antisymm hle hge
        rwa [hEq] at h

/-! ## Reading the machine off its concrete representation -/

/-- The initial configuration built from a list of input symbol codes. -/
def initN (l : List ℕ) : NCfg tm :=
  (some (eL tm tm.main), eS tm tm.initialState, fun i => if i = eK tm tm.k₀ then l else [])

omit [∀ k, Fintype (tm.Γ k)] in
theorem primrec_initN : Primrec (initN tm) := by
  refine Primrec.pair (Primrec.const _) (Primrec.pair (Primrec.const _) ?_)
  exact Primrec.fin_curry.2
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const _)) Primrec.fst (Primrec.const []))

theorem initN_eq (l : List (tm.Γ tm.k₀)) :
    initN tm (l.map (encG tm)) = toN tm (Turing.initList tm l) := by
  have hstk : (fun i => if i = eK tm tm.k₀ then l.map (encG tm) else [])
      = encStk tm (Turing.initList tm l).stk := by
    funext i
    by_cases h : i = eK tm tm.k₀
    · subst h
      rw [encStk_apply, if_pos rfl]
      congr 1
      simp [Turing.initList]
    · rw [if_neg h]
      have h2 : (eK tm).symm i ≠ tm.k₀ := fun hh => h (by rw [← hh]; simp)
      have h3 : encStk tm (Turing.initList tm l).stk i
          = ((Turing.initList tm l).stk ((eK tm).symm i)).map (encG tm) := rfl
      rw [h3, show (Turing.initList tm l).stk ((eK tm).symm i) = [] from by
        simp [Turing.initList, h2]]
      rfl
  simp only [initN, toN, hstk, Turing.initList, Option.map_some]

/-- The output read off the designated output stack of a halted configuration. -/
def outN (p : NCfg tm) : Option (List ℕ) :=
  Option.casesOn p.1 (some (p.2.2 (eK tm tm.k₁))) fun _ => none

omit [∀ k, Fintype (tm.Γ k)] in
theorem primrec_outN : Primrec (outN tm) :=
  Primrec.option_casesOn (o := fun p : NCfg tm => p.1) Primrec.fst
    (Primrec.option_some.comp
      (Primrec.fin_app.comp (Primrec.snd.comp Primrec.snd) (Primrec.const _)))
    (Primrec.const none)

omit [∀ k, Fintype (tm.Γ k)] in
theorem fst_eq_none_of_outN {p : NCfg tm} {w : List ℕ} (h : outN tm p = some w) : p.1 = none := by
  cases hp : p.1 with
  | none => rfl
  | some a => rw [outN, hp] at h; exact absurd h (by simp)

/-- Once the concrete run produces an output, the next step is undefined: a halted
configuration has no successor. -/
theorem nrun_succ_eq_none_of_out {p : NCfg tm} {t : ℕ} {w : List ℕ}
    (h : (nrun tm p t).bind (outN tm) = some w) : nrun tm p (t + 1) = none := by
  cases hr : nrun tm p t with
  | none => rw [nrun, hr]; rfl
  | some c =>
      rw [hr] at h
      have hc : c.1 = none := fst_eq_none_of_outN tm h
      rw [nrun, hr]
      have hstep : TM2.step tm.m (ofN tm c) = none := by
        obtain ⟨cl, cv, cS⟩ := c
        simp only at hc
        subst hc
        rfl
      change Option.map (toN tm) (TM2.step tm.m (ofN tm c)) = none
      rw [hstep]
      rfl

/-- The partial function on symbol codes computed by the machine: run the machine from the
initial configuration determined by the input codes and, at the first halting time, read off
the codes on the output stack. -/
def evalCode (l : List ℕ) : Part (List ℕ) :=
  Nat.rfindOpt fun t => (nrun tm (initN tm l) t).bind (outN tm)

/-- **TM2-computable implies partial recursive.**  The code-level behaviour of any bundled
Turing machine with finite stack alphabets is a partial recursive function. -/
theorem partrec_evalCode : Partrec (evalCode tm) := by
  refine Partrec.rfindOpt (f := fun l t => (nrun tm (initN tm l) t).bind (outN tm)) ?_
  refine Primrec₂.to_comp ?_
  exact Primrec.option_bind
    ((primrec_nrun tm).comp ((primrec_initN tm).comp Primrec.fst) Primrec.snd)
    ((primrec_outN tm).comp Primrec.snd)

/-- Numerical form of the previous theorem: the behaviour of the machine, read as a partial
function of a single natural number, is partial recursive. -/
theorem partrec_evalNat : Partrec fun n : ℕ =>
    (evalCode tm ((Encodable.decode (α := List ℕ) n).getD [])).map
      (Encodable.encode : List ℕ → ℕ) := by
  have hdec : Computable fun n : ℕ => (Encodable.decode (α := List ℕ) n).getD [] :=
    Computable.option_getD Computable.decode (Computable.const [])
  exact ((partrec_evalCode tm).comp hdec).map (Computable.encode.comp Computable.snd).to₂

/-! ## Correctness against `Turing.TM2Outputs` -/

theorem rfindOpt_eq_some {α : Type} {f : ℕ → Option α} {n : ℕ} {v : α} (hn : f n = some v)
    (hlt : ∀ t, t < n → f t = none) : Nat.rfindOpt f = Part.some v := by
  have h1 : n ∈ Nat.rfind ((fun m => (f m).isSome : ℕ → Bool) : ℕ →. Bool) := by
    rw [Nat.mem_rfind]
    exact ⟨by simp [hn], fun {m} hm => by simp [hlt m hm]⟩
  rw [Part.eq_some_iff]
  exact Part.mem_bind_iff.2 ⟨n, h1, by simp [hn]⟩

theorem outN_toN_haltList (l' : List (tm.Γ tm.k₁)) :
    outN tm (toN tm (Turing.haltList tm l')) = some (l'.map (encG tm)) := by
  have h1 : (toN tm (Turing.haltList tm l')).1 = none := by
    simp [toN, Turing.haltList]
  have h2 : (toN tm (Turing.haltList tm l')).2.2 (eK tm tm.k₁) = l'.map (encG tm) := by
    simp only [toN, encStk_apply]
    congr 1
    simp [Turing.haltList]
  rw [outN, h1]
  exact congrArg some h2

/-- Soundness: whenever the machine outputs `l'` on input `l`, the code-level function returns
the codes of `l'`. -/
theorem evalCode_of_outputs {l : List (tm.Γ tm.k₀)} {l' : List (tm.Γ tm.k₁)}
    (h : Turing.TM2Outputs tm l (some l')) :
    evalCode tm (l.map (encG tm)) = Part.some (l'.map (encG tm)) := by
  obtain ⟨n, hn⟩ := h
  simp only [Option.map_some] at hn
  have hrun : ∀ t, nrun tm (initN tm (l.map (encG tm))) t =
      ((flip Bind.bind tm.step)^[t] (some (Turing.initList tm l))).map (toN tm) := fun t => by
    rw [initN_eq, nrun_toN]
  have hn' : nrun tm (initN tm (l.map (encG tm))) n = some (toN tm (Turing.haltList tm l')) := by
    rw [hrun, hn, Option.map_some]
  refine rfindOpt_eq_some (n := n) ?_ ?_
  · rw [hn', Option.bind_some]
    exact outN_toN_haltList tm l'
  · intro t ht
    by_contra hcon
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hcon
    have hnone := nrun_succ_eq_none_of_out tm hw
    rw [nrun_none_mono tm hnone ht] at hn'
    exact absurd hn' (by simp)

/-! ## Completeness: a converging run really halts -/

/-- Whenever the code-level function of the machine converges on the codes of an input, the
machine itself reaches, in finitely many steps, a configuration with no label — a halted
configuration. -/
theorem exists_halted_of_evalCode {l : List (tm.Γ tm.k₀)} {w : List ℕ}
    (h : w ∈ evalCode tm (l.map (encG tm))) :
    ∃ (t : ℕ) (c : tm.Cfg),
      (flip Bind.bind tm.step)^[t] (some (Turing.initList tm l)) = some c ∧ c.l = none := by
  obtain ⟨t, ht⟩ := Nat.rfindOpt_spec h
  rw [Option.mem_def, initN_eq, nrun_toN] at ht
  cases hx : (flip Bind.bind tm.step)^[t] (some (Turing.initList tm l)) with
  | none => rw [hx] at ht; exact absurd ht (by simp)
  | some c =>
      refine ⟨t, c, hx, ?_⟩
      rw [hx, Option.map_some, Option.bind_some] at ht
      have h1 : (toN tm c).1 = none := fst_eq_none_of_outN tm ht
      simpa [toN] using h1

/-! ## The capstone for bundled machines -/

end Setup

/-- **TM2-computable implies partial recursive**, in the form of `Turing.TM2Computable`: if a
bundled machine with finite stack alphabets computes `f`, then the code-level partial function
of that machine is partial recursive and returns, on the codes of the encoded input, the codes
of the encoded output. -/
theorem partrec_of_tm2Computable {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (h : Turing.TM2Computable ea eb f)
    [∀ k, Fintype (h.tm.Γ k)] :
    Partrec (evalCode h.tm) ∧ ∀ a : α,
      evalCode h.tm ((List.map h.inputAlphabet.invFun (ea a)).map (encG h.tm)) =
        Part.some ((List.map h.outputAlphabet.invFun (eb (f a))).map (encG h.tm)) :=
  ⟨partrec_evalCode h.tm, fun a => evalCode_of_outputs h.tm (h.outputsFun a)⟩

/-- The finiteness hypothesis of the development is satisfiable: it holds for the identity
machine of `Turing.idComputable`, so the theorems above are not vacuous. -/
example {α αΓ : Type} [Fintype αΓ] (ea : α → List αΓ) :
    letI : ∀ k, Fintype ((Turing.idComputable ea).tm.Γ k) := fun _ => inferInstanceAs (Fintype αΓ)
    Partrec (evalCode (Turing.idComputable ea).tm) :=
  letI : ∀ k, Fintype ((Turing.idComputable ea).tm.Γ k) := fun _ => inferInstanceAs (Fintype αΓ)
  partrec_evalCode _

end

end TM2Partrec
