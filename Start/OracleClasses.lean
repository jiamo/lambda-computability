/-
**Relativized complexity classes: `P^A` and `NP^A`.**

On top of the oracle Cobham terms of `Start/OracleCob.lean` this file defines the relativized
classes and proves the facts that make them a relativization: an unrelativized Cobham function is
an oracle function that never asks anything (`Complexity.CobQ.ofCob`), an oracle term run with the
empty oracle is an unrelativized Cobham function (`Complexity.CobQ.erase`), and hence the
unrelativized classes are exactly the classes of the empty oracle.

Main definitions:

* `Complexity.InP_rel`, `Complexity.InNP_rel` — `P^A` and `NP^A`;
* `Complexity.PolyManyOne_rel` — polynomial-time many-one reducibility with the oracle `A`;
* `Complexity.PeqNP_rel` — the statement `P^A = NP^A`.

Main results:

* `Complexity.CobQ.eval_ofCob`, `Complexity.CobQ.queries_ofCob` — an unrelativized term keeps its
  value and asks nothing;
* `Complexity.CobQ.eval_erase` — with the empty oracle an oracle term is an unrelativized term;
* `Complexity.inP_rel_empty_iff`, `Complexity.inNP_rel_empty_iff` — the empty oracle gives back
  `P` and `NP`;
* `Complexity.InP.to_rel`, `Complexity.InNP.to_rel` — `P ⊆ P^A` and `NP ⊆ NP^A` for every `A`;
* `Complexity.inNP_rel_of_inP_rel` — `P^A ⊆ NP^A`;
* `Complexity.InP_rel.compl`, `.inter`, `.union`, `Complexity.InP_rel.of_reduction` — the same
  closure properties as in the unrelativized case;
* `Complexity.inP_rel_oracle` — the oracle itself is in `P^A`, which is what makes the
  relativized classes differ from the unrelativized ones.
-/

import Mathlib
import Start.OracleCob

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobQ

/-! ### Unrelativized terms as oracle terms -/

/-- An unrelativized Cobham term, read as an oracle term that never queries. -/
def ofCob : Cob → CobQ
  | .proj i => .proj i
  | .empty => .empty
  | .app b => .app b
  | .smash => .smash
  | .comp f gs => .comp (ofCob f) (gs.attach.map fun g => ofCob g.1)
  | .bRec g h₀ h₁ bd => .bRec (ofCob g) (ofCob h₀) (ofCob h₁) (ofCob bd)
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem g.2; omega)

@[simp] theorem ofCob_proj (i : ℕ) : ofCob (.proj i) = .proj i := by rw [ofCob]
@[simp] theorem ofCob_empty : ofCob .empty = .empty := by rw [ofCob]
@[simp] theorem ofCob_app (b : Bool) : ofCob (.app b) = .app b := by rw [ofCob]
@[simp] theorem ofCob_smash : ofCob .smash = .smash := by rw [ofCob]

theorem ofCob_comp (f : Cob) (gs : List Cob) :
    ofCob (.comp f gs) = .comp (ofCob f) (gs.map ofCob) := by
  rw [ofCob]
  congr 1
  simp

theorem ofCob_bRec (g h₀ h₁ bd : Cob) :
    ofCob (.bRec g h₀ h₁ bd) = .bRec (ofCob g) (ofCob h₀) (ofCob h₁) (ofCob bd) := by
  rw [ofCob]

/-- The recursion step of `eval_ofCob`. -/
theorem eval_ofCob_bRec {g h₀ h₁ bd : Cob} (A : Oracle)
    (Hg : ∀ args, eval A (ofCob g) args = g.eval args)
    (H0 : ∀ args, eval A (ofCob h₀) args = h₀.eval args)
    (H1 : ∀ args, eval A (ofCob h₁) args = h₁.eval args)
    (Hbd : ∀ args, eval A (ofCob bd) args = bd.eval args)
    (rest : List Word) :
    ∀ x : Word, eval A (ofCob (.bRec g h₀ h₁ bd)) (x :: rest)
      = (Cob.bRec g h₀ h₁ bd).eval (x :: rest) := by
  intro x
  induction x with
  | nil => rw [ofCob_bRec, eval_bRec_nil, Cob.eval_bRec_nil, Hg]
  | cons b x ih =>
      rw [ofCob_bRec, eval_bRec_cons, Cob.eval_bRec_cons, ← ofCob_bRec, ih, Hbd]
      cases b
      · simp only [Bool.false_eq_true, if_false, H0]
      · simp only [if_true, H1]

theorem eval_ofCob_aux : ∀ (n : ℕ) (c : Cob), sizeOf c ≤ n →
    ∀ (A : Oracle) (args : List Word), eval A (ofCob c) args = c.eval args := by
  intro n
  induction n with
  | zero =>
      intro c hc
      exfalso
      cases c <;> simp at hc
  | succ n ih =>
      intro c hc
      match c with
      | .proj i => intro A args; simp
      | .empty => intro A args; simp
      | .app b => intro A args; simp
      | .smash => intro A args; simp
      | .comp f gs =>
          have hf : sizeOf f ≤ n := by simp at hc; omega
          have hsz : ∀ g ∈ gs, sizeOf g ≤ n := by
            intro g hg
            have h1 := List.sizeOf_lt_of_mem hg
            simp at hc
            omega
          intro A args
          rw [ofCob_comp, eval_comp, Cob.eval_comp]
          have hmap : ((gs.map ofCob).map fun t => eval A t args)
              = gs.map fun g => g.eval args := by
            rw [List.map_map]
            refine List.map_congr_left fun g hg => ?_
            simpa using ih g (hsz g hg) A args
          rw [hmap, ih f hf]
      | .bRec g h₀ h₁ bd =>
          have hg : sizeOf g ≤ n := by simp at hc; omega
          have hh0 : sizeOf h₀ ≤ n := by simp at hc; omega
          have hh1 : sizeOf h₁ ≤ n := by simp at hc; omega
          have hbd : sizeOf bd ≤ n := by simp at hc; omega
          intro A args
          match args with
          | [] =>
              have h1 : eval A (ofCob (.bRec g h₀ h₁ bd)) [] = eval A (ofCob g) [] := by
                rw [ofCob_bRec]; simp [eval]
              have h2 : (Cob.bRec g h₀ h₁ bd).eval [] = g.eval [] := by
                rw [Cob.eval_bRec]; rfl
              rw [h1, h2, ih g hg]
          | x :: rest =>
              exact eval_ofCob_bRec A (ih g hg A) (ih h₀ hh0 A) (ih h₁ hh1 A) (ih bd hbd A)
                rest x

/-- **An unrelativized Cobham function is an oracle function**, with the same value. -/
theorem eval_ofCob (A : Oracle) (c : Cob) (args : List Word) :
    eval A (ofCob c) args = c.eval args :=
  eval_ofCob_aux (sizeOf c) c le_rfl A args

/-! ### Oracle terms with the empty oracle -/

/-- Erasing the queries of an oracle term: a query is replaced by the answer of the empty
oracle. -/
def erase : CobQ → Cob
  | .proj i => .proj i
  | .empty => .empty
  | .app b => .app b
  | .smash => .smash
  | .query => .empty
  | .comp f gs => .comp (erase f) (gs.attach.map fun g => erase g.1)
  | .bRec g h₀ h₁ bd => .bRec (erase g) (erase h₀) (erase h₁) (erase bd)
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem g.2; omega)

@[simp] theorem erase_proj (i : ℕ) : erase (.proj i) = .proj i := by rw [erase]
@[simp] theorem erase_empty : erase .empty = .empty := by rw [erase]
@[simp] theorem erase_app (b : Bool) : erase (.app b) = .app b := by rw [erase]
@[simp] theorem erase_smash : erase .smash = .smash := by rw [erase]
@[simp] theorem erase_query : erase .query = .empty := by rw [erase]

theorem erase_comp (f : CobQ) (gs : List CobQ) :
    erase (.comp f gs) = .comp (erase f) (gs.map erase) := by
  rw [erase]
  congr 1
  simp

theorem erase_bRec (g h₀ h₁ bd : CobQ) :
    erase (.bRec g h₀ h₁ bd) = .bRec (erase g) (erase h₀) (erase h₁) (erase bd) := by
  rw [erase]

/-- The empty oracle. -/
def emptyOracle : Oracle := fun _ => false

@[simp] theorem emptyOracle_apply (w : Word) : emptyOracle w = false := rfl

/-- The recursion step of `eval_erase`. -/
theorem eval_erase_bRec {g h₀ h₁ bd : CobQ}
    (Hg : ∀ args, (erase g).eval args = eval emptyOracle g args)
    (H0 : ∀ args, (erase h₀).eval args = eval emptyOracle h₀ args)
    (H1 : ∀ args, (erase h₁).eval args = eval emptyOracle h₁ args)
    (Hbd : ∀ args, (erase bd).eval args = eval emptyOracle bd args)
    (rest : List Word) :
    ∀ x : Word, (erase (.bRec g h₀ h₁ bd)).eval (x :: rest)
      = eval emptyOracle (.bRec g h₀ h₁ bd) (x :: rest) := by
  intro x
  induction x with
  | nil => rw [erase_bRec, Cob.eval_bRec_nil, eval_bRec_nil, Hg]
  | cons b x ih =>
      rw [erase_bRec, Cob.eval_bRec_cons, eval_bRec_cons, ← erase_bRec, ih, Hbd]
      cases b
      · simp only [Bool.false_eq_true, if_false, H0]
      · simp only [if_true, H1]

theorem eval_erase_aux : ∀ (n : ℕ) (t : CobQ), sizeOf t ≤ n →
    ∀ args : List Word, (erase t).eval args = eval emptyOracle t args := by
  intro n
  induction n with
  | zero =>
      intro t ht
      exfalso
      cases t <;> simp at ht
  | succ n ih =>
      intro t ht
      match t with
      | .proj i => intro args; simp
      | .empty => intro args; simp
      | .app b => intro args; simp
      | .smash => intro args; simp
      | .query => intro args; simp
      | .comp f gs =>
          have hf : sizeOf f ≤ n := by simp at ht; omega
          have hsz : ∀ g ∈ gs, sizeOf g ≤ n := by
            intro g hg
            have h1 := List.sizeOf_lt_of_mem hg
            simp at ht
            omega
          intro args
          rw [erase_comp, Cob.eval_comp, eval_comp]
          have hmap : ((gs.map erase).map fun c => c.eval args)
              = gs.map fun g => eval emptyOracle g args := by
            rw [List.map_map]
            refine List.map_congr_left fun g hg => ?_
            simpa using ih g (hsz g hg) args
          rw [hmap, ih f hf]
      | .bRec g h₀ h₁ bd =>
          have hg : sizeOf g ≤ n := by simp at ht; omega
          have hh0 : sizeOf h₀ ≤ n := by simp at ht; omega
          have hh1 : sizeOf h₁ ≤ n := by simp at ht; omega
          have hbd : sizeOf bd ≤ n := by simp at ht; omega
          intro args
          match args with
          | [] =>
              have h1 : (erase (.bRec g h₀ h₁ bd)).eval [] = (erase g).eval [] := by
                rw [erase_bRec, Cob.eval_bRec]; rfl
              have h2 : eval emptyOracle (.bRec g h₀ h₁ bd) [] = eval emptyOracle g [] := by
                simp [eval]
              rw [h1, h2, ih g hg]
          | x :: rest =>
              exact eval_erase_bRec (ih g hg) (ih h₀ hh0) (ih h₁ hh1) (ih bd hbd) rest x

/-- **With the empty oracle an oracle term is an unrelativized Cobham function.** -/
theorem eval_erase (t : CobQ) (args : List Word) :
    (erase t).eval args = eval emptyOracle t args :=
  eval_erase_aux (sizeOf t) t le_rfl args

end CobQ

/-! ### The relativized classes -/

/-- `L ∈ P^A`: some polynomial-time oracle term with oracle `A` decides it. -/
def InP_rel (A : Oracle) (L : Language) : Prop :=
  ∃ t : CobQ, ∀ x, (L x ↔ CobQ.eval A t [x] ≠ [])

/-- `L ∈ NP^A`: some polynomial-time oracle verifier with oracle `A` accepts `(x, w)` only for
witnesses of polynomially bounded length, and `x ∈ L` exactly when some witness is accepted. -/
def InNP_rel (A : Oracle) (L : Language) : Prop :=
  ∃ (v : CobQ) (p : ℕ → ℕ), PolyBound p ∧ Monotone p ∧
    (∀ x w, CobQ.eval A v [x, w] ≠ [] → w.length ≤ p x.length) ∧
    (∀ x, L x ↔ ∃ w, CobQ.eval A v [x, w] ≠ [])

/-- Polynomial-time many-one reducibility with the oracle `A`. -/
def PolyManyOne_rel (A : Oracle) (L₁ L₂ : Language) : Prop :=
  ∃ r : CobQ, ∀ x, (L₁ x ↔ L₂ (CobQ.eval A r [x]))

/-- The statement `P^A = NP^A`. -/
def PeqNP_rel (A : Oracle) : Prop := ∀ L : Language, InNP_rel A L → InP_rel A L

/-! ### The unrelativized classes are the classes of the empty oracle -/

/-- `P ⊆ P^A` for every oracle. -/
theorem InP.to_rel {L : Language} (h : InP L) (A : Oracle) : InP_rel A L := by
  obtain ⟨c, hc⟩ := h
  exact ⟨CobQ.ofCob c, fun x => by rw [CobQ.eval_ofCob]; exact hc x⟩

/-- `NP ⊆ NP^A` for every oracle. -/
theorem InNP.to_rel {L : Language} (h : InNP L) (A : Oracle) : InNP_rel A L := by
  obtain ⟨v, p, hp, hmono, hlen, hL⟩ := h
  refine ⟨CobQ.ofCob v, p, hp, hmono, ?_, ?_⟩
  · intro x w hacc
    rw [CobQ.eval_ofCob] at hacc
    exact hlen x w hacc
  · intro x
    rw [hL x]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w, by rw [CobQ.eval_ofCob]; exact hw⟩
    · rintro ⟨w, hw⟩
      rw [CobQ.eval_ofCob] at hw
      exact ⟨w, hw⟩

/-- **The empty oracle gives back `P`.** -/
theorem inP_rel_empty_iff {L : Language} : InP_rel CobQ.emptyOracle L ↔ InP L := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨CobQ.erase t, fun x => by rw [CobQ.eval_erase]; exact ht x⟩
  · intro h
    exact h.to_rel _

/-- **The empty oracle gives back `NP`.** -/
theorem inNP_rel_empty_iff {L : Language} : InNP_rel CobQ.emptyOracle L ↔ InNP L := by
  constructor
  · rintro ⟨v, p, hp, hmono, hlen, hL⟩
    refine ⟨CobQ.erase v, p, hp, hmono, ?_, ?_⟩
    · intro x w hacc
      rw [CobQ.eval_erase] at hacc
      exact hlen x w hacc
    · intro x
      rw [hL x]
      constructor
      · rintro ⟨w, hw⟩
        exact ⟨w, by rw [CobQ.eval_erase]; exact hw⟩
      · rintro ⟨w, hw⟩
        rw [CobQ.eval_erase] at hw
        exact ⟨w, hw⟩
  · intro h
    exact h.to_rel _

/-! ### Structural results, relativized -/

/-! Gadgets, as oracle terms. -/

namespace CobQ

/-- Boolean negation as an oracle term. -/
def notQ : CobQ := ofCob .notC

/-- Conjunction as an oracle term. -/
def andQ : CobQ := ofCob .andC

/-- Disjunction as an oracle term. -/
def orQ : CobQ := ofCob .orC

@[simp] theorem eval_notQ (A : Oracle) (u : Word) (rest : List Word) :
    eval A notQ (u :: rest) = if u = [] then [Bool.true] else [] := by
  simp [notQ, eval_ofCob]

@[simp] theorem eval_andQ (A : Oracle) (u v : Word) :
    eval A andQ [u, v] = if u = [] then [] else v := by
  simp [andQ, eval_ofCob]

@[simp] theorem eval_orQ (A : Oracle) (u v : Word) :
    eval A orQ [u, v] = if u = [] then v else [Bool.true] := by
  simp [orQ, eval_ofCob]

end CobQ

/-- **`P^A ⊆ NP^A`.** -/
theorem inNP_rel_of_inP_rel {A : Oracle} {L : Language} (h : InP_rel A L) : InNP_rel A L := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp CobQ.andQ [.comp c [.proj 0], .comp CobQ.notQ [.proj 1]], fun _ => 0,
    polyBound_const 0, monotone_const, ?_, ?_⟩
  · intro x w hacc
    simp only [CobQ.eval_comp, List.map_cons, List.map_nil, CobQ.eval_proj, CobQ.eval_andQ,
      CobQ.eval_notQ] at hacc
    by_cases hx : CobQ.eval A c [x] = []
    · simp [hx] at hacc
    · by_cases hw : w = []
      · simp [hw]
      · simp [hx, hw] at hacc
  · intro x
    simp only [CobQ.eval_comp, List.map_cons, List.map_nil, CobQ.eval_proj, CobQ.eval_andQ,
      CobQ.eval_notQ]
    constructor
    · intro hx
      refine ⟨[], ?_⟩
      have : CobQ.eval A c [x] ≠ [] := (hc x).1 hx
      simp [this]
    · rintro ⟨w, hw⟩
      by_cases hx : CobQ.eval A c [x] = []
      · simp [hx] at hw
      · exact (hc x).2 hx

/-- `P^A` is closed under complement. -/
theorem InP_rel.compl {A : Oracle} {L : Language} (h : InP_rel A L) :
    InP_rel A (fun x => ¬ L x) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp CobQ.notQ [c], fun x => ?_⟩
  simp only [CobQ.eval_comp, List.map_cons, List.map_nil, CobQ.eval_notQ]
  by_cases hx : CobQ.eval A c [x] = [] <;> simp [hx, hc x]

/-- `P^A` is closed under intersection. -/
theorem InP_rel.inter {A : Oracle} {L₁ L₂ : Language} (h₁ : InP_rel A L₁) (h₂ : InP_rel A L₂) :
    InP_rel A (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨.comp CobQ.andQ [c₁, c₂], fun x => ?_⟩
  simp only [CobQ.eval_comp, List.map_cons, List.map_nil, CobQ.eval_andQ]
  by_cases hx : CobQ.eval A c₁ [x] = [] <;> simp [hx, hc₁ x, hc₂ x]

/-- `P^A` is closed under union. -/
theorem InP_rel.union {A : Oracle} {L₁ L₂ : Language} (h₁ : InP_rel A L₁) (h₂ : InP_rel A L₂) :
    InP_rel A (fun x => L₁ x ∨ L₂ x) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨.comp CobQ.orQ [c₁, c₂], fun x => ?_⟩
  simp only [CobQ.eval_comp, List.map_cons, List.map_nil, CobQ.eval_orQ]
  by_cases hx : CobQ.eval A c₁ [x] = [] <;> simp [hx, hc₁ x, hc₂ x]

/-- `P^A` is closed downwards under many-one reductions computed with the oracle. -/
theorem InP_rel.of_reduction {A : Oracle} {L₁ L₂ : Language}
    (hred : PolyManyOne_rel A L₁ L₂) (h : InP_rel A L₂) : InP_rel A L₁ := by
  obtain ⟨r, hr⟩ := hred
  obtain ⟨c, hc⟩ := h
  exact ⟨.comp c [r], fun x => by simpa using (hr x).trans (hc _)⟩

/-- **The oracle itself is decidable in `P^A`.**  This is the point of relativizing: `P^A` is in
general bigger than `P`. -/
theorem inP_rel_oracle (A : Oracle) : InP_rel A (fun x => A x = true) := by
  refine ⟨.query, fun x => ?_⟩
  rw [CobQ.eval_query]
  by_cases hA : A x <;> simp [hA]

end Complexity
