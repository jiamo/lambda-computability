/-
Building straight-line Boolean circuits incrementally.

`Start/Tseitin.lean` defines circuits as lists of gates written *output first*, the identifier of a
gate being the number of gates below it.  Consequently a circuit is *extended* by putting new gates
in front of it, and the identifiers — hence the values — of the old gates do not change.  This
module turns that observation into a small toolkit for constructing circuits piece by piece:

* `Complexity.Tseitin.wval` — the value of a wire, as a function of the circuit input;
* `Complexity.Tseitin.Ext` — `C'` extends `C` (new gates on top);
* `Complexity.Tseitin.Holds` — the wire `w` of `C` computes the Boolean function `f`.

Every gadget below is stated as an *existence* lemma: from a well-formed circuit `C` whose wires
compute certain functions, there is a well-formed extension `C'` with a new wire computing the
desired function, and `C'` has boundedly many more gates than `C`.  Chaining such lemmas is how
the compiler in `Start/CobhamCircuit.lean` is built.

Main results:

* `Complexity.Tseitin.Holds.mono` — wire specifications survive extension;
* `Complexity.Tseitin.exists_inp`, `exists_cst`, `exists_neg`, `exists_conj`, `exists_disj` — the
  five kinds of gate;
* `Complexity.Tseitin.exists_ite` — multiplexing;
* `Complexity.Tseitin.exists_bigOr` — the disjunction of a list of wires.
-/

import Start.Tseitin

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### Wires and extensions -/

/-- The value of the wire `w` of the circuit `C` on the circuit input `x`. -/
def wval (C : Circuit) (w : ℕ) (x : Word) : Bool := (vals x C).getD w false

/-- `C'` extends `C`: it is obtained by adding gates on top of `C`. -/
def Ext (C C' : Circuit) : Prop := ∃ D, C' = D ++ C

theorem Ext.rfl' (C : Circuit) : Ext C C := ⟨[], rfl⟩

theorem Ext.trans {C₁ C₂ C₃ : Circuit} (h₁ : Ext C₁ C₂) (h₂ : Ext C₂ C₃) : Ext C₁ C₃ := by
  obtain ⟨D, rfl⟩ := h₁
  obtain ⟨E, rfl⟩ := h₂
  exact ⟨E ++ D, by simp⟩

theorem Ext.cons (g : Gate) (C : Circuit) : Ext C (g :: C) := ⟨[g], rfl⟩

theorem Ext.length_le {C C' : Circuit} (h : Ext C C') : C.length ≤ C'.length := by
  obtain ⟨D, rfl⟩ := h
  simp

theorem vals_append_getD (x : Word) (D C : Circuit) {j : ℕ} (hj : j < C.length) :
    (vals x (D ++ C)).getD j false = (vals x C).getD j false := by
  induction D with
  | nil => rfl
  | cons g D ih =>
      have hlt : j < (D ++ C).length := by
        simp only [List.length_append]; omega
      rw [List.cons_append, vals_cons_getD_lt x g (D ++ C) hlt, ih]

/-- The values of the old wires do not change when a circuit is extended. -/
theorem wval_of_ext {C C' : Circuit} (h : Ext C C') {w : ℕ} (hw : w < C.length) (x : Word) :
    wval C' w x = wval C w x := by
  obtain ⟨D, rfl⟩ := h
  exact vals_append_getD x D C hw

/-- `wf` is inherited by the part of a circuit below any extension. -/
theorem wf_append_right {D C : Circuit} (h : wf (D ++ C)) : wf C := by
  induction D with
  | nil => exact h
  | cons g D ih => exact ih h.2

/-! ### Wire specifications -/

/-- The wire `w` of the circuit `C` computes the Boolean function `f` of the circuit input. -/
def Holds (C : Circuit) (w : ℕ) (f : Word → Bool) : Prop :=
  w < C.length ∧ ∀ x, wval C w x = f x

theorem Holds.lt {C : Circuit} {w : ℕ} {f : Word → Bool} (h : Holds C w f) : w < C.length := h.1

theorem Holds.eq {C : Circuit} {w : ℕ} {f : Word → Bool} (h : Holds C w f) (x : Word) :
    wval C w x = f x := h.2 x

/-- A wire specification survives any extension of the circuit. -/
theorem Holds.mono {C C' : Circuit} {w : ℕ} {f : Word → Bool} (h : Holds C w f) (he : Ext C C') :
    Holds C' w f :=
  ⟨lt_of_lt_of_le h.1 he.length_le, fun x => by rw [wval_of_ext he h.1 x]; exact h.2 x⟩

theorem Holds.congr {C : Circuit} {w : ℕ} {f g : Word → Bool} (h : Holds C w f)
    (hfg : ∀ x, f x = g x) : Holds C w g :=
  ⟨h.1, fun x => (h.2 x).trans (hfg x)⟩

/-! ### The value of the wire added on top -/

theorem wval_top (x : Word) (g : Gate) (C : Circuit) :
    wval (g :: C) C.length x = gateVal x (vals x C) g :=
  vals_cons_getD_length x g C

/-! ### The individual gates -/

/-- Adding an input gate. -/
theorem exists_inp (C : Circuit) (hC : wf C) (i : ℕ) :
    ∃ C' : Circuit, Ext C C' ∧ wf C' ∧ C'.length = C.length + 1 ∧
      Holds C' C.length (fun x => x.getD i false) := by
  refine ⟨Gate.inp i :: C, Ext.cons _ _, ⟨trivial, hC⟩, by simp, by simp, fun x => ?_⟩
  rw [wval_top]
  rfl

/-- Adding a constant gate. -/
theorem exists_cst (C : Circuit) (hC : wf C) (b : Bool) :
    ∃ C' : Circuit, Ext C C' ∧ wf C' ∧ C'.length = C.length + 1 ∧
      Holds C' C.length (fun _ => b) := by
  refine ⟨Gate.cst b :: C, Ext.cons _ _, ⟨trivial, hC⟩, by simp, by simp, fun x => ?_⟩
  rw [wval_top]
  rfl

/-- Adding a negation gate. -/
theorem exists_neg {C : Circuit} (hC : wf C) {r : ℕ} {f : Word → Bool} (hr : Holds C r f) :
    ∃ C' : Circuit, Ext C C' ∧ wf C' ∧ C'.length = C.length + 1 ∧
      Holds C' C.length (fun x => !f x) := by
  refine ⟨Gate.neg r :: C, Ext.cons _ _, ⟨hr.1, hC⟩, by simp, by simp, fun x => ?_⟩
  rw [wval_top]
  simp only [gateVal]
  rw [show (vals x C).getD r false = wval C r x from rfl, hr.2 x]

/-- Adding a conjunction gate. -/
theorem exists_conj {C : Circuit} (hC : wf C) {r s : ℕ} {f g : Word → Bool} (hr : Holds C r f)
    (hs : Holds C s g) :
    ∃ C' : Circuit, Ext C C' ∧ wf C' ∧ C'.length = C.length + 1 ∧
      Holds C' C.length (fun x => f x && g x) := by
  refine ⟨Gate.conj r s :: C, Ext.cons _ _, ⟨⟨hr.1, hs.1⟩, hC⟩, by simp, by simp, fun x => ?_⟩
  rw [wval_top]
  simp only [gateVal]
  rw [show (vals x C).getD r false = wval C r x from rfl,
    show (vals x C).getD s false = wval C s x from rfl, hr.2 x, hs.2 x]

/-- Adding a disjunction gate. -/
theorem exists_disj {C : Circuit} (hC : wf C) {r s : ℕ} {f g : Word → Bool} (hr : Holds C r f)
    (hs : Holds C s g) :
    ∃ C' : Circuit, Ext C C' ∧ wf C' ∧ C'.length = C.length + 1 ∧
      Holds C' C.length (fun x => f x || g x) := by
  refine ⟨Gate.disj r s :: C, Ext.cons _ _, ⟨⟨hr.1, hs.1⟩, hC⟩, by simp, by simp, fun x => ?_⟩
  rw [wval_top]
  simp only [gateVal]
  rw [show (vals x C).getD r false = wval C r x from rfl,
    show (vals x C).getD s false = wval C s x from rfl, hr.2 x, hs.2 x]

/-! ### Derived gadgets -/

/-- Multiplexing: `if c then f else g`. -/
theorem exists_ite {C : Circuit} (hC : wf C) {c r s : ℕ} {fc f g : Word → Bool}
    (hc : Holds C c fc) (hr : Holds C r f) (hs : Holds C s g) :
    ∃ (C' : Circuit) (w : ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + 4 ∧
      Holds C' w (fun x => if fc x then f x else g x) := by
  obtain ⟨C₁, e₁, w₁, l₁, h₁⟩ := exists_neg hC hc
  obtain ⟨C₂, e₂, w₂, l₂, h₂⟩ := exists_conj w₁ (hc.mono e₁) (hr.mono e₁)
  obtain ⟨C₃, e₃, w₃, l₃, h₃⟩ := exists_conj w₂ (h₁.mono e₂) (hs.mono (e₁.trans e₂))
  obtain ⟨C₄, e₄, w₄, l₄, h₄⟩ := exists_disj w₃ (h₂.mono e₃) h₃
  refine ⟨C₄, C₃.length, e₁.trans (e₂.trans (e₃.trans e₄)), w₄, by omega, h₄.congr fun x => ?_⟩
  cases fc x <;> simp

/-- The disjunction of the first `n` wires of a list. -/
theorem exists_bigOr {C : Circuit} (hC : wf C) (n : ℕ) (ws : List ℕ) (F : ℕ → Word → Bool)
    (h : ∀ i, i < n → Holds C (ws.getD i 0) (F i)) :
    ∃ (C' : Circuit) (w : ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + n + 1 ∧
      Holds C' w (fun x => (List.range n).any (fun i => F i x)) := by
  induction n with
  | zero =>
      obtain ⟨C', e, w', l', h'⟩ := exists_cst C hC false
      exact ⟨C', C.length, e, w', by omega, h'.congr fun x => by simp⟩
  | succ n ih =>
      obtain ⟨C₁, w₁, e₁, hw₁, l₁, hh₁⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨C₂, e₂, hw₂, l₂, hh₂⟩ :=
        exists_disj hw₁ hh₁ ((h n (by omega)).mono e₁)
      refine ⟨C₂, C₁.length, e₁.trans e₂, hw₂, by omega, hh₂.congr fun x => ?_⟩
      rw [List.range_succ]
      simp

/-- The conjunction of the first `n` wires of a list. -/
theorem exists_bigAnd {C : Circuit} (hC : wf C) (n : ℕ) (ws : List ℕ) (F : ℕ → Word → Bool)
    (h : ∀ i, i < n → Holds C (ws.getD i 0) (F i)) :
    ∃ (C' : Circuit) (w : ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + n + 1 ∧
      Holds C' w (fun x => (List.range n).all (fun i => F i x)) := by
  induction n with
  | zero =>
      obtain ⟨C', e, w', l', h'⟩ := exists_cst C hC true
      exact ⟨C', C.length, e, w', by omega, h'.congr fun x => by simp⟩
  | succ n ih =>
      obtain ⟨C₁, w₁, e₁, hw₁, l₁, hh₁⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨C₂, e₂, hw₂, l₂, hh₂⟩ :=
        exists_conj hw₁ hh₁ ((h n (by omega)).mono e₁)
      refine ⟨C₂, C₁.length, e₁.trans e₂, hw₂, by omega, hh₂.congr fun x => ?_⟩
      rw [List.range_succ]
      simp

/-- **Building a list of wires.**  If, on top of any extension of `C₀`, a wire computing `F i` can
be added at a cost of `cost` gates, then a whole list of `n` wires computing `F 0, …, F (n-1)` can
be added at a cost of `n * cost` gates. -/
theorem exists_wire_list {C₀ : Circuit} (hC₀ : wf C₀) (n cost : ℕ) (F : ℕ → Word → Bool)
    (step : ∀ C : Circuit, wf C → Ext C₀ C → ∀ i, i < n →
      ∃ (C' : Circuit) (w : ℕ), Ext C C' ∧ wf C' ∧ C'.length ≤ C.length + cost ∧
        Holds C' w (F i)) :
    ∃ (C' : Circuit) (ws : List ℕ), Ext C₀ C' ∧ wf C' ∧ ws.length = n ∧
      C'.length ≤ C₀.length + n * cost ∧ ∀ i, i < n → Holds C' (ws.getD i 0) (F i) := by
  induction n with
  | zero => exact ⟨C₀, [], Ext.rfl' _, hC₀, rfl, by simp, by omega⟩
  | succ n ih =>
      obtain ⟨C₁, ws, e₁, w₁, hlen, hsz, hws⟩ :=
        ih (fun C hC he i hi => step C hC he i (by omega))
      obtain ⟨C₂, w, e₂, w₂, hsz₂, hw⟩ := step C₁ w₁ e₁ n (by omega)
      refine ⟨C₂, ws ++ [w], e₁.trans e₂, w₂, by simp [hlen], by
        have := e₁.length_le
        calc C₂.length ≤ C₁.length + cost := hsz₂
          _ ≤ C₀.length + n * cost + cost := by omega
          _ = C₀.length + (n + 1) * cost := by ring_nf, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · have : (ws ++ [w]).getD i 0 = ws.getD i 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
            ← List.getD_eq_getElem?_getD]
        rw [this]
        exact (hws i hi').mono e₂
      · have : (ws ++ [w]).getD i 0 = w := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          simp [hlen]
        rw [this]
        exact hw

end Tseitin

end Complexity
