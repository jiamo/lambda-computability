/-
**Compiling Cobham's polynomial-time functions into Boolean circuits.**

The polynomial-time functions of `Start/ComplexityClasses.lean` are Cobham terms: projections, the
empty word, the two successors, the smash function, composition and bounded recursion on notation.
This module compiles every such term into a Boolean circuit of *polynomial size*, using the word
signals of `Start/WordCircuit.lean`: the arguments of the term arrive as pairs of wire vectors, and
the compiler returns a wire vector computing the value of the term.

Every case except bounded recursion on notation is settled here; bounded recursion, which is the
one construction that needs an idea, is dealt with in `Start/CobhamBRec.lean`.

Main definitions:

* `Complexity.MonoPoly` — a monotone, polynomially bounded function `ℕ → ℕ` (the shape of all the
  size and width bounds used here);
* `Complexity.Tseitin.argsOf`, `Complexity.Tseitin.ArgSig` — argument lists and their signals;
* `Complexity.Tseitin.CompilesAt`, `Complexity.Tseitin.CobCompiles` — the compilation statement
  for one Cobham term.

Main results:

* `Complexity.Tseitin.cobCompiles_proj`, `Complexity.Tseitin.cobCompiles_empty`,
  `Complexity.Tseitin.cobCompiles_app`, `Complexity.Tseitin.cobCompiles_smash`,
  `Complexity.Tseitin.cobCompiles_comp` — the compilation of every Cobham term except bounded
  recursion, which is dealt with in `Start/CobhamBRec.lean`.
-/

import Start.WordCircuit
import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

/-! ### Monotone polynomial bounds -/

/-- A monotone, polynomially bounded function: the shape of every width and size bound below. -/
structure MonoPoly (f : ℕ → ℕ) : Prop where
  mono : Monotone f
  poly : PolyBound f

theorem MonoPoly.const (c : ℕ) : MonoPoly (fun _ => c) :=
  ⟨monotone_const, polyBound_const c⟩

theorem MonoPoly.id' : MonoPoly (fun n => n) :=
  ⟨monotone_id, ⟨1, 1, fun n => by simp⟩⟩

theorem MonoPoly.add {f g : ℕ → ℕ} (hf : MonoPoly f) (hg : MonoPoly g) :
    MonoPoly (fun n => f n + g n) :=
  ⟨fun _ _ hab => Nat.add_le_add (hf.mono hab) (hg.mono hab), hf.poly.add hg.poly⟩

theorem MonoPoly.mul {f g : ℕ → ℕ} (hf : MonoPoly f) (hg : MonoPoly g) :
    MonoPoly (fun n => f n * g n) := by
  refine ⟨fun _ _ hab => Nat.mul_le_mul (hf.mono hab) (hg.mono hab), ?_⟩
  obtain ⟨a, k, ha⟩ := hf.poly
  obtain ⟨b, m, hb⟩ := hg.poly
  refine ⟨a * b, k + m, fun n => ?_⟩
  calc f n * g n ≤ (a * (n + 1) ^ k) * (b * (n + 1) ^ m) := Nat.mul_le_mul (ha n) (hb n)
    _ = a * b * (n + 1) ^ (k + m) := by rw [pow_add]; ring

theorem MonoPoly.comp {f g : ℕ → ℕ} (hf : MonoPoly f) (hg : MonoPoly g) :
    MonoPoly (fun n => f (g n)) :=
  ⟨fun _ _ hab => hf.mono (hg.mono hab), hf.poly.comp hg.poly⟩

theorem MonoPoly.mono' {f g : ℕ → ℕ} (hf : MonoPoly f) (hmono : Monotone g)
    (h : ∀ n, g n ≤ f n) : MonoPoly g :=
  ⟨hmono, hf.poly.mono h⟩

/-- The standard polynomial `n ↦ a * (n + 1) ^ k`. -/
theorem MonoPoly.std (a k : ℕ) : MonoPoly (fun n => a * (n + 1) ^ k) :=
  ⟨fun _ _ hpq => Nat.mul_le_mul_left a (Nat.pow_le_pow_left (by omega) k),
    ⟨a, k, fun _ => le_rfl⟩⟩

namespace Tseitin

/-! ### Argument lists -/

/-- The list of the first `n` arguments, as a function of the circuit input. -/
def argsOf (F : ℕ → Word → Word) (n : ℕ) (x : Word) : List Word :=
  (List.range n).map (fun i => F i x)

@[simp] theorem length_argsOf (F : ℕ → Word → Word) (n : ℕ) (x : Word) :
    (argsOf F n x).length = n := by simp [argsOf]

theorem getD_argsOf {F : ℕ → Word → Word} {n : ℕ} (htriv : ∀ i, n ≤ i → ∀ x, F i x = [])
    (x : Word) (i : ℕ) : (argsOf F n x).getD i [] = F i x := by
  by_cases h : i < n
  · rw [List.getD_eq_getElem?_getD, argsOf, List.getElem?_map, List.getElem?_range h]
    rfl
  · rw [List.getD_eq_default _ _ (by simp; omega), htriv i (by omega) x]

theorem headD_argsOf {F : ℕ → Word → Word} {n : ℕ} (htriv : ∀ i, n ≤ i → ∀ x, F i x = [])
    (x : Word) : (argsOf F n x).headD [] = F 0 x := by
  cases n with
  | zero => rw [argsOf, List.range_zero, List.map_nil, List.headD_nil, htriv 0 (by omega) x]
  | succ n => simp [argsOf, List.range_succ_eq_map]

theorem tail_argsOf (F : ℕ → Word → Word) (n : ℕ) (x : Word) :
    (argsOf F n x).tail = argsOf (fun i => F (i + 1)) (n - 1) x := by
  cases n with
  | zero => simp [argsOf]
  | succ n =>
      simp only [argsOf, List.range_succ_eq_map, List.map_cons, List.tail_cons, List.map_map,
        Nat.add_sub_cancel]
      rfl

/-- Prefixing an argument to an indexed family of arguments. -/
def consFun (a : Word → Word) (F : ℕ → Word → Word) : ℕ → Word → Word
  | 0 => a
  | (j + 1) => F j

/-- Prefixing a signal to an indexed family of signals. -/
def consSigs (p : List ℕ × List ℕ) (S : ℕ → List ℕ × List ℕ) : ℕ → List ℕ × List ℕ
  | 0 => p
  | (j + 1) => S j

/-- Consing an argument in front of an argument list. -/
theorem argsOf_consFun (a : Word → Word) (F : ℕ → Word → Word) (n : ℕ) (x : Word) :
    argsOf (consFun a F) (n + 1) x = a x :: argsOf F n x := by
  simp only [argsOf, List.range_succ_eq_map, List.map_cons, List.map_map]
  rfl

/-! ### Signals for an argument list -/

/-- The signals `S 0, …, S (n-1)` represent the arguments `F 0, …, F (n-1)`, all of width at most
`m`, and the arguments beyond `n` are empty. -/
structure ArgSig (C : Circuit) (m n : ℕ) (S : ℕ → List ℕ × List ℕ) (F : ℕ → Word → Word) :
    Prop where
  triv : ∀ i, n ≤ i → ∀ x, F i x = []
  holds : ∀ i, i < n → WHolds C (S i).1.length (S i).1 (S i).2 (F i)
  bnd : ∀ i, i < n → (S i).1.length ≤ m

theorem ArgSig.mono {C C' : Circuit} {m n : ℕ} {S : ℕ → List ℕ × List ℕ} {F : ℕ → Word → Word}
    (h : ArgSig C m n S F) (he : Ext C C') : ArgSig C' m n S F :=
  ⟨h.triv, fun i hi => (h.holds i hi).mono he, h.bnd⟩

theorem ArgSig.widen {C : Circuit} {m m' n : ℕ} {S : ℕ → List ℕ × List ℕ} {F : ℕ → Word → Word}
    (h : ArgSig C m n S F) (hm : m ≤ m') : ArgSig C m' n S F :=
  ⟨h.triv, h.holds, fun i hi => le_trans (h.bnd i hi) hm⟩

theorem ArgSig.tail {C : Circuit} {m n : ℕ} {S : ℕ → List ℕ × List ℕ} {F : ℕ → Word → Word}
    (h : ArgSig C m n S F) :
    ArgSig C m (n - 1) (fun i => S (i + 1)) (fun i => F (i + 1)) :=
  ⟨fun i hi x => h.triv (i + 1) (by omega) x, fun i hi => h.holds (i + 1) (by omega),
    fun i hi => h.bnd (i + 1) (by omega)⟩

/-- Prefixing one more argument to an argument list. -/
theorem ArgSig.cons {C : Circuit} {m n : ℕ} {S : ℕ → List ℕ × List ℕ} {F : ℕ → Word → Word}
    (h : ArgSig C m n S F) {M : ℕ} {ps bs : List ℕ} {a : Word → Word}
    (ha : WHolds C M ps bs a) (hM : M ≤ m) :
    ArgSig C m (n + 1) (consSigs (ps, bs) S) (consFun a F) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi x
    match i with
    | 0 => exact absurd hi (by omega)
    | (j + 1) => exact h.triv j (by omega) x
  · intro i hi
    match i with
    | 0 =>
        simp only [consSigs, consFun, ha.lenP]
        exact ha
    | (j + 1) => exact h.holds j (by omega)
  · intro i hi
    match i with
    | 0 =>
        simp only [consSigs, ha.lenP]
        exact hM
    | (j + 1) => exact h.bnd j (by omega)

theorem maxLen_le_of_mem {l : List Word} {B : ℕ} (h : ∀ w ∈ l, w.length ≤ B) : maxLen l ≤ B := by
  induction l with
  | nil => simp [maxLen]
  | cons a l ih =>
      simp only [maxLen_cons]
      exact max_le (h a (by simp)) (ih fun w hw => h w (by simp [hw]))

theorem ArgSig.maxLen_le {C : Circuit} {m n : ℕ} {S : ℕ → List ℕ × List ℕ} {F : ℕ → Word → Word}
    (h : ArgSig C m n S F) (x : Word) : maxLen (argsOf F n x) ≤ m := by
  have hstep : ∀ i, i < n → (F i x).length ≤ m := by
    intro i hi
    exact le_trans ((h.holds i hi).bnd x) (h.bnd i hi)
  refine maxLen_le_of_mem ?_
  intro w hw
  simp only [argsOf, List.mem_map, List.mem_range] at hw
  obtain ⟨i, hi, rfl⟩ := hw
  exact hstep i hi

/-- The signal of one argument: the given one if the index is live, the empty signal otherwise. -/
theorem exists_argSig {C : Circuit} (hC : wf C) {m n : ℕ} {S : ℕ → List ℕ × List ℕ}
    {F : ℕ → Word → Word} (h : ArgSig C m n S F) (i : ℕ) :
    ∃ (C' : Circuit) (M : ℕ) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧ M ≤ m ∧
      C'.length ≤ C.length + 2 ∧ WHolds C' M ps bs (F i) := by
  by_cases hi : i < n
  · exact ⟨C, (S i).1.length, (S i).1, (S i).2, Ext.rfl' _, hC, h.bnd i hi, by omega,
      h.holds i hi⟩
  · obtain ⟨C', ps, bs, e, w, l, hh⟩ := exists_emptySig C hC 0
    exact ⟨C', 0, ps, bs, e, w, Nat.zero_le _, l,
      hh.congr fun x => (h.triv i (by omega) x).symm⟩

/-! ### The compilation statement -/

/-- **A Cobham term compiles into circuits at width `m` and cost `c`**: on top of any well-formed
circuit carrying signals for the arguments (all of width at most `m`), a signal for the value of
the term can be built with at most `c` further gates. -/
def CompilesAt (v : Cob) (m c : ℕ) : Prop :=
  ∀ (n Mout : ℕ) (C : Circuit) (S : ℕ → List ℕ × List ℕ) (F : ℕ → Word → Word),
    wf C → ArgSig C m n S F → Mout ≤ m →
    (∀ x, (v.eval (argsOf F n x)).length ≤ Mout) →
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧
      WHolds C' Mout ps bs (fun x => v.eval (argsOf F n x)) ∧
      C'.length ≤ C.length + c

theorem CompilesAt.weaken {v : Cob} {m c c' : ℕ} (h : CompilesAt v m c) (hc : c ≤ c') :
    CompilesAt v m c' := by
  intro n Mout C S F hC hS hMout hbnd
  obtain ⟨C', ps, bs, e, w, hh, l⟩ := h n Mout C S F hC hS hMout hbnd
  exact ⟨C', ps, bs, e, w, hh, by omega⟩

/-- **A Cobham term compiles into circuits of polynomial size**: the cost is bounded by a monotone
polynomial in the width of the arguments. -/
def CobCompiles (v : Cob) : Prop :=
  ∃ bd : ℕ → ℕ, MonoPoly bd ∧ ∀ m, CompilesAt v m (bd m)

/-! ### The base cases -/

theorem cobCompiles_proj (i : ℕ) : CobCompiles (.proj i) := by
  refine ⟨fun _ => 3, MonoPoly.const 3, ?_⟩
  intro m n Mout C S F hC hS hMout hbnd
  obtain ⟨C₁, M₁, ps₁, bs₁, e₁, w₁, hM₁, l₁, hh₁⟩ := exists_argSig hC hS i
  have hval : ∀ x, (Cob.proj i).eval (argsOf F n x) = F i x := by
    intro x
    rw [Cob.eval_proj, getD_argsOf hS.triv x i]
  obtain ⟨C₂, ps, bs, e₂, w₂, l₂, hh₂⟩ :=
    exists_resize w₁ hh₁ Mout (fun x => by rw [← hval x]; exact hbnd x)
  exact ⟨C₂, ps, bs, e₁.trans e₂, w₂, hh₂.congr fun x => (hval x).symm,
    show C₂.length ≤ C.length + 3 by omega⟩

theorem cobCompiles_empty : CobCompiles .empty := by
  refine ⟨fun _ => 2, MonoPoly.const 2, ?_⟩
  intro m n Mout C S F hC _ _ _
  obtain ⟨C₁, ps, bs, e, w, l, hh⟩ := exists_emptySig C hC Mout
  exact ⟨C₁, ps, bs, e, w, hh.congr fun x => (Cob.eval_empty (argsOf F n x)).symm, l⟩

theorem cobCompiles_app (b : Bool) : CobCompiles (.app b) := by
  refine ⟨fun _ => 5, MonoPoly.const 5, ?_⟩
  intro m n Mout C S F hC hS hMout hbnd
  obtain ⟨C₁, M₁, ps₁, bs₁, e₁, w₁, hM₁, l₁, hh₁⟩ := exists_argSig hC hS 0
  have hval : ∀ x, (Cob.app b).eval (argsOf F n x) = b :: F 0 x := by
    intro x
    rw [Cob.eval_app, getD_argsOf hS.triv x 0]
  obtain ⟨C₂, ps, bs, e₂, w₂, l₂, hh₂⟩ :=
    exists_consSig w₁ b hh₁ Mout (fun x => by
      have hb := hbnd x
      rw [hval x] at hb
      simpa using hb)
  exact ⟨C₂, ps, bs, e₁.trans e₂, w₂, hh₂.congr fun x => (hval x).symm,
    show C₂.length ≤ C.length + 5 by omega⟩

theorem cobCompiles_smash : CobCompiles .smash := by
  refine ⟨fun m => 4 + m * (2 * (m * m) + 2),
    (MonoPoly.const 4).add (MonoPoly.id'.mul
      (((MonoPoly.const 2).mul (MonoPoly.id'.mul MonoPoly.id')).add (MonoPoly.const 2))), ?_⟩
  intro m n Mout C S F hC hS hMout hbnd
  obtain ⟨C₁, M₁, ps₁, bs₁, e₁, w₁, hM₁, l₁, hh₁⟩ := exists_argSig hC hS 0
  obtain ⟨C₂, M₂, ps₂, bs₂, e₂, w₂, hM₂, l₂, hh₂⟩ := exists_argSig w₁ (hS.mono e₁) 1
  have hval : ∀ x, Cob.smash.eval (argsOf F n x)
      = List.replicate ((F 0 x).length * (F 1 x).length) true := by
    intro x
    rw [Cob.eval_smash, getD_argsOf hS.triv x 0, getD_argsOf hS.triv x 1]
  obtain ⟨C₃, ps, bs, e₃, w₃, l₃, hh₃⟩ :=
    exists_smashSig w₂ (hh₁.mono e₂) hh₂ Mout (fun x => by
      have hb := hbnd x
      rw [hval x] at hb
      simpa using hb)
  refine ⟨C₃, ps, bs, e₁.trans (e₂.trans e₃), w₃, hh₃.congr fun x => (hval x).symm, ?_⟩
  change C₃.length ≤ C.length + (4 + m * (2 * (m * m) + 2))
  have hle : Mout * (2 * (M₁ * M₂) + 2) ≤ m * (2 * (m * m) + 2) :=
    Nat.mul_le_mul hMout (by have := Nat.mul_le_mul hM₁ hM₂; omega)
  omega

/-! ### Composition -/

/-- Reindexing a list through `getD` over its own range. -/
theorem map_range_getD {α β : Type} (l : List α) (d : α) (φ : α → β) :
    (List.range l.length).map (fun i => φ (l.getD i d)) = l.map φ := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  have h₃ : i < l.length := by simpa using h₂
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ h₃]

/-- Signals for the values of a whole list of Cobham terms, built one after another. -/
theorem exists_argsCircuit : ∀ (gs : List Cob), (∀ g ∈ gs, CobCompiles g) →
    ∃ Mg bdg : ℕ → ℕ, MonoPoly Mg ∧ MonoPoly bdg ∧ (∀ m, m ≤ Mg m) ∧
      ∀ (m n : ℕ) (C : Circuit) (S : ℕ → List ℕ × List ℕ) (F : ℕ → Word → Word),
        wf C → ArgSig C m n S F →
        ∃ (C' : Circuit) (S' : ℕ → List ℕ × List ℕ), Ext C C' ∧ wf C' ∧
          ArgSig C' (Mg m) gs.length S'
            (fun i x => (gs.getD i Cob.empty).eval (argsOf F n x)) ∧
          C'.length ≤ C.length + bdg m := by
  intro gs
  induction gs with
  | nil =>
      intro _
      refine ⟨fun m => m, fun _ => 0, MonoPoly.id', MonoPoly.const 0, fun _ => le_rfl, ?_⟩
      intro m n C S F hC _
      refine ⟨C, fun _ => ([], []), Ext.rfl' _, hC, ⟨fun i _ x => by simp, ?_, ?_⟩, by simp⟩
      · intro i hi
        simp at hi
      · intro i hi
        simp at hi
  | cons g gs ih =>
      intro hall
      obtain ⟨Mg', bdg', hMg', hbdg', hmle', hrec⟩ := ih fun g' hg' => hall g' (by simp [hg'])
      obtain ⟨bdG, hbdG, hG⟩ := hall g (by simp)
      obtain ⟨ag, kg, hag⟩ := Cob.polyLen g
      refine ⟨fun m => m + ag * (m + 1) ^ kg + Mg' m,
        fun m => bdG (m + ag * (m + 1) ^ kg + Mg' m) + bdg' m,
        (MonoPoly.id'.add (MonoPoly.std ag kg)).add hMg',
        (hbdG.comp ((MonoPoly.id'.add (MonoPoly.std ag kg)).add hMg')).add hbdg',
        fun m => by change m ≤ m + ag * (m + 1) ^ kg + Mg' m; omega, ?_⟩
      intro m n C S F hC hS
      set W := fun m : ℕ => m + ag * (m + 1) ^ kg + Mg' m with hW
      have hMgle : m ≤ W m := by simp only [hW]; omega
      have hbndg : ∀ x, (g.eval (argsOf F n x)).length ≤ W m := by
        intro x
        have h₁ := hag (argsOf F n x)
        have h₂ : maxLen (argsOf F n x) ≤ m := hS.maxLen_le x
        have h₃ : ag * (maxLen (argsOf F n x) + 1) ^ kg ≤ ag * (m + 1) ^ kg :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        simp only [hW]
        omega
      obtain ⟨C₁, ps, bs, e₁, w₁, hh₁, l₁⟩ :=
        hG (W m) n (W m) C S F hC (hS.widen hMgle) le_rfl hbndg
      obtain ⟨C₂, S'', e₂, w₂, hA₂, l₂⟩ := hrec m n C₁ S F w₁ (hS.mono e₁)
      refine ⟨C₂, fun i => match i with | 0 => (ps, bs) | (j + 1) => S'' j,
        e₁.trans e₂, w₂, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro i hi x
        rw [List.getD_eq_default _ _ (by simpa using hi), Cob.eval_empty]
      · intro i hi
        match i with
        | 0 =>
            simp only [hh₁.lenP]
            exact (hh₁.mono e₂).congr fun x => by simp
        | (j + 1) =>
            exact (hA₂.holds j (by simpa using hi)).congr fun x => by simp
      · intro i hi
        match i with
        | 0 =>
            simp only [hh₁.lenP]
            exact le_rfl
        | (j + 1) =>
            exact le_trans (hA₂.bnd j (by simpa using hi)) (by simp only [hW]; omega)
      · change C₂.length ≤ C.length + (bdG (W m) + bdg' m)
        omega

theorem cobCompiles_comp (f : Cob) (gs : List Cob) (hf : CobCompiles f)
    (hgs : ∀ g ∈ gs, CobCompiles g) : CobCompiles (.comp f gs) := by
  obtain ⟨bdf, hbdf, hfc⟩ := hf
  obtain ⟨Mg, bdg, hMg, hbdg, hmle, hargc⟩ := exists_argsCircuit gs hgs
  refine ⟨fun m => bdg m + bdf (Mg m), hbdg.add (hbdf.comp hMg), ?_⟩
  intro m n Mout C S F hC hS hMout hbnd
  obtain ⟨C₁, S', e₁, w₁, hA, l₁⟩ := hargc m n C S F hC hS
  have hval : ∀ x, (Cob.comp f gs).eval (argsOf F n x)
      = f.eval (argsOf (fun i y => (gs.getD i Cob.empty).eval (argsOf F n y)) gs.length x) := by
    intro x
    rw [Cob.eval_comp]
    congr 1
    exact (map_range_getD gs Cob.empty (fun g => g.eval (argsOf F n x))).symm
  obtain ⟨C₂, ps, bs, e₂, w₂, hh, l₂⟩ :=
    hfc (Mg m) gs.length Mout C₁ S' _ w₁ hA (le_trans hMout (hmle m))
      (fun x => by rw [← hval x]; exact hbnd x)
  refine ⟨C₂, ps, bs, e₁.trans e₂, w₂, hh.congr fun x => (hval x).symm, ?_⟩
  change C₂.length ≤ C.length + (bdg m + bdf (Mg m))
  omega

end Tseitin

end Complexity
