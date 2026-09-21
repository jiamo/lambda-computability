/-
Relativized polynomial time: the classes `Pᴬ` and `NPᴬ` for an oracle `A` on binary words.

`Start/ComplexityClasses.lean` defines `P` and `NP` through Cobham's syntactic class of
polynomial-time functions.  Relativizing that definition costs one constructor: a *query gate*
`CobO.query`, which reads the oracle at its first argument and answers with the accept word
`[true]` or the empty word.  Everything else — composition, bounded recursion on notation, the
smash function — is copied verbatim, so an oracle Cobham term is exactly a polynomial-time
procedure with oracle access, and the unrelativized class is the sub-class of terms that contain
no query gate (`Complexity.Oracle.CobO.ofCob`).

Main definitions:

* `Complexity.Oracle.CobO`, `Complexity.Oracle.CobO.eval` — oracle Cobham terms and their
  semantics in an oracle `A : Word → Bool`;
* `Complexity.Oracle.CobO.ofCob` — the oracle-free terms, with
  `Complexity.Oracle.CobO.eval_ofCob`;
* `Complexity.Oracle.InPO`, `Complexity.Oracle.InNPO` — the relativized classes `Pᴬ` and `NPᴬ`;
* `Complexity.Oracle.PolyManyOneO` (`≤ₘᵖ[A]`) — polynomial-time many-one reducibility computed
  with the oracle;
* `Complexity.Oracle.PeqNPO` — the statement `Pᴬ = NPᴬ`, the form in which the two halves of the
  Baker–Gill–Solovay theorem are stated.

Main results:

* `Complexity.Oracle.inPO_of_inP`, `Complexity.Oracle.inNPO_of_inNP` — the unrelativized classes
  are contained in the relativized ones;
* `Complexity.Oracle.inNPO_of_inPO` — `Pᴬ ⊆ NPᴬ`;
* `Complexity.Oracle.inPO_oracle` — the oracle itself is decided in `Pᴬ` (this is what
  relativization is for: an oracle is a free decision procedure);
* `Complexity.Oracle.InPO.compl`, `.inter`, `.union`, `Complexity.Oracle.InNPO.union` — closure
  properties of the relativized classes;
* `Complexity.Oracle.polyManyOneO_refl`, `Complexity.Oracle.polyManyOneO_trans`,
  `Complexity.Oracle.InPO.of_reduction`, `Complexity.Oracle.InNPO.of_reduction` — `≤ₘᵖ[A]` is a
  preorder and both relativized classes are closed downwards under it;
* `Complexity.Oracle.peqNPO_of_inPO_of_npHardO` — an `NPᴬ`-hard language in `Pᴬ` collapses the
  two classes;
* `Complexity.Oracle.inPO_univ`, `Complexity.Oracle.inPO_empty` — non-vacuity.

Honest boundary: nothing here separates the two classes for any oracle.  The Baker–Gill–Solovay
theorem needs, for the collapsing half, a PSPACE-complete oracle (the missing ingredient is the
hardness of `TQBF`, recorded on the task board), and for the separating half a counting argument
on the queries an oracle term can make, which is not formalized: the definitions above deliberately
carry no cost measure, so the number of queries is not bounded by anything yet.
-/

import Start.ComplexityClasses

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity
namespace Oracle

/-! ### Oracle Cobham terms -/

/-- Syntax for the polynomial-time functions with access to an oracle on binary words: Cobham's
class together with a query gate. -/
inductive CobO : Type
  /-- The `i`-th argument. -/
  | proj (i : ℕ)
  /-- The constant empty word. -/
  | empty
  /-- The successor function `x ↦ b :: x` on the first argument. -/
  | app (b : Bool)
  /-- The smash function `x # y = 1^{|x|·|y|}` on the first two arguments. -/
  | smash
  /-- The query gate: ask the oracle about the first argument. -/
  | query
  /-- Composition. -/
  | comp (f : CobO) (gs : List CobO)
  /-- Bounded recursion on notation over the first argument. -/
  | bRec (g h₀ h₁ bd : CobO)
  deriving Inhabited

/-- The function denoted by an oracle Cobham term, in the oracle `A`.  The query gate answers
`[true]` when the oracle accepts its first argument and the empty word otherwise, so that the
accept convention of `Start/ComplexityClasses.lean` — a nonempty output means "accept" — is the
same on both sides. -/
def CobO.eval (A : Word → Bool) : CobO → List Word → Word
  | .proj i, args => args.getD i []
  | .empty, _ => []
  | .app b, args => b :: args.getD 0 []
  | .smash, args =>
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true
  | .query, args => if A (args.getD 0 []) then [Bool.true] else []
  | .comp f gs, args => CobO.eval A f (gs.attach.map (fun g => CobO.eval A g.1 args))
  | .bRec g h₀ h₁ bd, args =>
      List.rec (CobO.eval A g args.tail)
        (fun b x' ih =>
          (if b then CobO.eval A h₁ (x' :: ih :: args.tail)
            else CobO.eval A h₀ (x' :: ih :: args.tail)).take
            ((CobO.eval A bd ((b :: x') :: args.tail)).length))
        (args.headD [])
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    · have := List.sizeOf_lt_of_mem g.2; omega
    all_goals omega

variable {A : Word → Bool}

@[simp] theorem CobO.eval_proj (i : ℕ) (args : List Word) :
    (CobO.proj i).eval A args = args.getD i [] := by
  rw [CobO.eval]

@[simp] theorem CobO.eval_empty (args : List Word) : CobO.empty.eval A args = [] := by
  rw [CobO.eval]

@[simp] theorem CobO.eval_app (b : Bool) (args : List Word) :
    (CobO.app b).eval A args = b :: args.getD 0 [] := by
  rw [CobO.eval]

@[simp] theorem CobO.eval_smash (args : List Word) :
    CobO.smash.eval A args =
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true := by
  rw [CobO.eval]

@[simp] theorem CobO.eval_query (args : List Word) :
    CobO.query.eval A args = if A (args.getD 0 []) then [Bool.true] else [] := by
  rw [CobO.eval]

@[simp] theorem CobO.eval_comp (f : CobO) (gs : List CobO) (args : List Word) :
    (CobO.comp f gs).eval A args = f.eval A (gs.map (fun g => g.eval A args)) := by
  rw [CobO.eval]
  congr 1
  exact List.attach_map_val (l := gs) (f := fun g => g.eval A args)

theorem CobO.eval_bRec (g h₀ h₁ bd : CobO) (args : List Word) :
    (CobO.bRec g h₀ h₁ bd).eval A args =
      List.rec (g.eval A args.tail)
        (fun b x' ih =>
          (if b then h₁.eval A (x' :: ih :: args.tail) else h₀.eval A (x' :: ih :: args.tail)).take
            ((bd.eval A ((b :: x') :: args.tail)).length))
        (args.headD []) := by
  rw [CobO.eval]

@[simp] theorem CobO.eval_bRec_nil (g h₀ h₁ bd : CobO) (rest : List Word) :
    (CobO.bRec g h₀ h₁ bd).eval A ([] :: rest) = g.eval A rest := by
  rw [CobO.eval_bRec]; rfl

@[simp] theorem CobO.eval_bRec_cons (g h₀ h₁ bd : CobO) (b : Bool) (x : Word) (rest : List Word) :
    (CobO.bRec g h₀ h₁ bd).eval A ((b :: x) :: rest) =
      (if b then h₁.eval A (x :: (CobO.bRec g h₀ h₁ bd).eval A (x :: rest) :: rest)
        else h₀.eval A (x :: (CobO.bRec g h₀ h₁ bd).eval A (x :: rest) :: rest)).take
        ((bd.eval A ((b :: x) :: rest)).length) := by
  rw [CobO.eval_bRec, CobO.eval_bRec]; rfl

/-! ### The oracle-free terms -/

/-- Every Cobham term is an oracle Cobham term: the one with no query gate. -/
def CobO.ofCob : Cob → CobO
  | .proj i => .proj i
  | .empty => .empty
  | .app b => .app b
  | .smash => .smash
  | .comp f gs => .comp (CobO.ofCob f) (gs.attach.map fun g => CobO.ofCob g.1)
  | .bRec g h₀ h₁ bd =>
      .bRec (CobO.ofCob g) (CobO.ofCob h₀) (CobO.ofCob h₁) (CobO.ofCob bd)
  termination_by c => sizeOf c
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have := List.sizeOf_lt_of_mem g.2; omega)

@[simp] theorem CobO.ofCob_comp (f : Cob) (gs : List Cob) :
    CobO.ofCob (.comp f gs) = .comp (CobO.ofCob f) (gs.map CobO.ofCob) := by
  rw [CobO.ofCob]
  congr 1
  exact List.attach_map_val (l := gs) (f := CobO.ofCob)

/-- **The oracle-free terms compute what they computed before**: an oracle plays no part in the
value of a term without query gates. -/
theorem CobO.eval_ofCob : ∀ (c : Cob) (args : List Word),
    (CobO.ofCob c).eval A args = c.eval args := by
  intro c
  induction c using Cob.rec
    (motive_2 := fun gs => ∀ args : List Word,
      (gs.map fun g => (CobO.ofCob g).eval A args) = gs.map fun g => g.eval args)
    with
  | proj i => intro args; simp [CobO.ofCob]
  | empty => intro args; simp [CobO.ofCob]
  | app b => intro args; simp [CobO.ofCob]
  | smash => intro args; simp [CobO.ofCob]
  | comp f gs ihf ihgs =>
      intro args
      simp only [CobO.ofCob_comp, CobO.eval_comp, Cob.eval_comp, List.map_map,
        Function.comp_def]
      rw [ihgs args, ihf]
  | bRec g h₀ h₁ bd ihg ih₀ ih₁ ihbd =>
      -- both sides recurse on the head argument in the same way
      rintro (_ | ⟨w, rest⟩)
      · simp only [CobO.ofCob, CobO.eval_bRec, Cob.eval_bRec]
        simpa using ihg []
      · induction w with
        | nil =>
            simp only [CobO.ofCob, CobO.eval_bRec_nil, Cob.eval_bRec_nil]
            exact ihg rest
        | cons b x ih =>
            simp only [CobO.ofCob] at ih ⊢
            rw [CobO.eval_bRec_cons, Cob.eval_bRec_cons, ih, ihbd, ih₀, ih₁]
  | nil => simp
  | cons g gs ihg ihgs =>
      simp only [List.map_cons]
      rw [ihg, ihgs]

/-! ### Polynomially bounded output length -/

theorem maxLen_le_of_forall {ws : List Word} {B : ℕ} (h : ∀ w ∈ ws, w.length ≤ B) :
    maxLen ws ≤ B := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
      simp only [maxLen_cons]
      exact max_le (h w (by simp)) (ih fun w' hw' => h w' (by simp [hw']))

theorem CobO.polyLenO_aux : ∀ (n : ℕ) (c : CobO), sizeOf c ≤ n → PolyLen (c.eval A) := by
  intro n
  induction n with
  | zero =>
      intro c hc
      exfalso
      cases c <;> simp at hc
  | succ n ih =>
      intro c hc
      match c with
      | .proj i =>
          refine ⟨1, 1, fun args => ?_⟩
          simp only [CobO.eval_proj, pow_one, one_mul]
          exact le_trans (length_getD_le_maxLen args i) (Nat.le_succ _)
      | .empty => exact ⟨0, 0, fun args => by simp⟩
      | .app b =>
          refine ⟨1, 1, fun args => ?_⟩
          simp only [CobO.eval_app, pow_one, one_mul, List.length_cons]
          have := length_getD_le_maxLen args 0
          omega
      | .smash =>
          refine ⟨1, 2, fun args => ?_⟩
          simp only [CobO.eval_smash, List.length_replicate, one_mul]
          have h0 := length_getD_le_maxLen args 0
          have h1 := length_getD_le_maxLen args 1
          calc (args.getD 0 []).length * (args.getD 1 []).length
              ≤ maxLen args * maxLen args := Nat.mul_le_mul h0 h1
            _ ≤ (maxLen args + 1) ^ 2 := by ring_nf; omega
      | .query =>
          refine ⟨1, 0, fun args => ?_⟩
          simp only [CobO.eval_query, pow_zero, mul_one]
          split <;> simp
      | .comp f gs =>
          have hf : sizeOf f ≤ n := by simp at hc; omega
          obtain ⟨af, kf, hafk⟩ := ih f hf
          have hsz : ∀ g ∈ gs, sizeOf g ≤ n := by
            intro g hg
            have h1 := List.sizeOf_lt_of_mem hg
            simp at hc
            omega
          have hgs : ∃ a k, ∀ g ∈ gs, ∀ args,
              (g.eval A args).length ≤ a * (maxLen args + 1) ^ k := by
            clear hc hf hafk
            revert hsz
            induction gs with
            | nil => intro _; exact ⟨0, 0, by simp⟩
            | cons g gs ihg =>
                intro hsz
                obtain ⟨a1, k1, h1⟩ := ih g (hsz g (by simp))
                obtain ⟨a2, k2, h2⟩ := ihg (fun g' hg' => hsz g' (by simp [hg']))
                refine ⟨a1 + a2, max k1 k2, ?_⟩
                intro g' hg' args
                rcases List.mem_cons.1 hg' with rfl | hg''
                · exact le_trans (h1 args) (bound_mono (by omega) (le_max_left _ _) le_rfl)
                · exact le_trans (h2 g' hg'' args)
                    (bound_mono (by omega) (le_max_right _ _) le_rfl)
          obtain ⟨a, k, hgsb⟩ := hgs
          refine ⟨af * (a + 1) ^ kf, k * kf, fun args => ?_⟩
          have hM : maxLen (gs.map fun g => g.eval A args) ≤ a * (maxLen args + 1) ^ k := by
            refine maxLen_le_of_forall ?_
            intro w hw
            obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hw
            exact hgsb g hg args
          calc ((CobO.comp f gs).eval A args).length
              = (f.eval A (gs.map fun g => g.eval A args)).length := by rw [CobO.eval_comp]
            _ ≤ af * (maxLen (gs.map fun g => g.eval A args) + 1) ^ kf := hafk _
            _ ≤ af * (a + 1) ^ kf * (maxLen args + 1) ^ (k * kf) := bound_comp_le hM
      | .bRec g h₀ h₁ bd =>
          have hg : sizeOf g ≤ n := by simp at hc; omega
          have hbd : sizeOf bd ≤ n := by simp at hc; omega
          obtain ⟨ag, kg, hgb⟩ := ih g hg
          obtain ⟨ab, kb, hbb⟩ := ih bd hbd
          refine ⟨ag + ab, max kg kb, fun args => ?_⟩
          match args with
          | [] =>
              have hev : (CobO.bRec g h₀ h₁ bd).eval A [] = g.eval A [] := by
                rw [CobO.eval_bRec]; rfl
              rw [hev]
              exact le_trans (hgb []) (bound_mono (by omega) (le_max_left _ _) le_rfl)
          | [] :: rest =>
              rw [CobO.eval_bRec_nil]
              refine le_trans (hgb rest) (bound_mono (by omega) (le_max_left _ _) ?_)
              simp
          | (b :: x) :: rest =>
              rw [CobO.eval_bRec_cons]
              refine le_trans (le_trans (le_of_eq (List.length_take ..)) (min_le_left _ _)) ?_
              exact le_trans (hbb ((b :: x) :: rest))
                (bound_mono (by omega) (le_max_right _ _) le_rfl)

/-- **Oracle Cobham functions have polynomially bounded output length.**  A query gate answers
with at most one bit, so the bound is proved exactly as in the unrelativized case. -/
theorem CobO.polyLenO (c : CobO) : PolyLen (c.eval A) :=
  CobO.polyLenO_aux (sizeOf c) c le_rfl

/-! ### The relativized classes -/

/-- `L` is in `Pᴬ`: some oracle Cobham term decides it, "accept" meaning a nonempty output. -/
def InPO (A : Word → Bool) (L : Language) : Prop :=
  ∃ c : CobO, ∀ x, (L x ↔ c.eval A [x] ≠ [])

/-- `L` is in `NPᴬ`: some oracle verifier accepts `(x, w)` only for witnesses `w` of polynomially
bounded length, and `x ∈ L` exactly when some witness is accepted. -/
def InNPO (A : Word → Bool) (L : Language) : Prop :=
  ∃ (v : CobO) (p : ℕ → ℕ), PolyBound p ∧ Monotone p ∧
    (∀ x w, v.eval A [x, w] ≠ [] → w.length ≤ p x.length) ∧
    (∀ x, L x ↔ ∃ w, v.eval A [x, w] ≠ [])

/-- Polynomial-time many-one reducibility computed with the oracle. -/
def PolyManyOneO (A : Word → Bool) (L₁ L₂ : Language) : Prop :=
  ∃ r : CobO, ∀ x, (L₁ x ↔ L₂ (r.eval A [x]))

@[inherit_doc] scoped notation:50 L₁ " ≤ₘᵖ[" A "] " L₂ => PolyManyOneO A L₁ L₂

/-- `L` is `NPᴬ`-hard. -/
def NPHardO (A : Word → Bool) (L : Language) : Prop :=
  ∀ L' : Language, InNPO A L' → PolyManyOneO A L' L

/-- `L` is `NPᴬ`-complete. -/
def NPCompleteO (A : Word → Bool) (L : Language) : Prop := InNPO A L ∧ NPHardO A L

/-- The statement `Pᴬ = NPᴬ`. -/
def PeqNPO (A : Word → Bool) : Prop := ∀ L : Language, InNPO A L → InPO A L

/-! ### The unrelativized classes sit inside the relativized ones -/

/-- **`P ⊆ Pᴬ`.** -/
theorem inPO_of_inP {L : Language} (h : InP L) : InPO A L := by
  obtain ⟨c, hc⟩ := h
  exact ⟨CobO.ofCob c, fun x => by rw [CobO.eval_ofCob]; exact hc x⟩

/-- **`NP ⊆ NPᴬ`.** -/
theorem inNPO_of_inNP {L : Language} (h : InNP L) : InNPO A L := by
  obtain ⟨v, p, hp, hmono, hlen, hspec⟩ := h
  refine ⟨CobO.ofCob v, p, hp, hmono, ?_, ?_⟩
  · intro x w hacc
    rw [CobO.eval_ofCob] at hacc
    exact hlen x w hacc
  · intro x
    rw [hspec x]
    constructor
    · rintro ⟨w, hw⟩; exact ⟨w, by rw [CobO.eval_ofCob]; exact hw⟩
    · rintro ⟨w, hw⟩; rw [CobO.eval_ofCob] at hw; exact ⟨w, hw⟩

/-! ### The oracle is free -/

/-- **The oracle is decided in `Pᴬ`**: the query gate on the input is a one-gate decision
procedure for the language of the oracle. -/
theorem inPO_oracle : InPO A (fun x => A x = true) := by
  refine ⟨.query, fun x => ?_⟩
  by_cases hx : A x <;> simp [hx]

/-! ### Structural results -/

/-- **`Pᴬ ⊆ NPᴬ`.** -/
theorem inNPO_of_inPO {L : Language} (h : InPO A L) : InNPO A L := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp (CobO.ofCob .andC) [.comp c [.proj 0], .comp (CobO.ofCob .notC) [.proj 1]],
    fun _ => 0, polyBound_const 0, monotone_const, ?_, ?_⟩
  · intro x w hacc
    simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj,
      CobO.eval_ofCob, Cob.eval_andC, Cob.eval_notC] at hacc
    by_cases hx : c.eval A [x] = []
    · simp [hx] at hacc
    · by_cases hw : w = []
      · simp [hw]
      · simp [hx, hw] at hacc
  · intro x
    simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj,
      CobO.eval_ofCob, Cob.eval_andC, Cob.eval_notC]
    constructor
    · intro hx
      exact ⟨[], by simp [(hc x).1 hx]⟩
    · rintro ⟨w, hw⟩
      by_cases hx : c.eval A [x] = []
      · simp [hx] at hw
      · exact (hc x).2 hx

theorem polyManyOneO_refl (L : Language) : PolyManyOneO A L L := ⟨.proj 0, fun x => by simp⟩

theorem polyManyOneO_trans {L₁ L₂ L₃ : Language} (h₁ : PolyManyOneO A L₁ L₂)
    (h₂ : PolyManyOneO A L₂ L₃) : PolyManyOneO A L₁ L₃ := by
  obtain ⟨r₁, hr₁⟩ := h₁
  obtain ⟨r₂, hr₂⟩ := h₂
  exact ⟨.comp r₂ [.comp r₁ [.proj 0]], fun x => by simpa using (hr₁ x).trans (hr₂ _)⟩

/-- **`Pᴬ` is closed downwards under `≤ₘᵖ[A]`.** -/
theorem InPO.of_reduction {L₁ L₂ : Language} (hred : PolyManyOneO A L₁ L₂) (h : InPO A L₂) :
    InPO A L₁ := by
  obtain ⟨r, hr⟩ := hred
  obtain ⟨c, hc⟩ := h
  exact ⟨.comp c [r], fun x => by simpa using (hr x).trans (hc _)⟩

/-- **`NPᴬ` is closed downwards under `≤ₘᵖ[A]`.** -/
theorem InNPO.of_reduction {L₁ L₂ : Language} (hred : PolyManyOneO A L₁ L₂) (h : InNPO A L₂) :
    InNPO A L₁ := by
  obtain ⟨r, hr⟩ := hred
  obtain ⟨v, p, hp, hmono, hlen, hspec⟩ := h
  obtain ⟨a, k, hak⟩ := (CobO.polyLenO (A := A) r)
  refine ⟨.comp v [.comp r [.proj 0], .proj 1], fun n => p (a * (n + 1) ^ k),
    hp.comp ⟨a, k, fun _ => le_rfl⟩, ?_, ?_, ?_⟩
  · intro m n hmn
    exact hmono (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  · intro x w hacc
    simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj] at hacc
    have h1 : w.length ≤ p (r.eval A [x]).length := hlen _ _ hacc
    exact h1.trans (hmono (by simpa using hak [x]))
  · intro x
    simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj]
    exact (hr x).trans (hspec _)

/-- An `NPᴬ`-hard language in `Pᴬ` collapses the two relativized classes. -/
theorem peqNPO_of_inPO_of_npHardO {L : Language} (hhard : NPHardO A L) (hL : InPO A L) :
    PeqNPO A := fun L' hL' => InPO.of_reduction (hhard L' hL') hL

/-! ### Non-vacuity and closure -/

theorem inPO_univ : InPO A (fun _ => True) := inPO_of_inP inP_univ

theorem inPO_empty : InPO A (fun _ => False) := inPO_of_inP inP_empty

/-- **`Pᴬ` is closed under complement.** -/
theorem InPO.compl {L : Language} (h : InPO A L) : InPO A (fun x => ¬ L x) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨.comp (CobO.ofCob .notC) [.comp c [.proj 0]], fun x => ?_⟩
  simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj, CobO.eval_ofCob,
    Cob.eval_notC]
  by_cases hx : c.eval A [x] = [] <;> simp [hx, hc x]

/-- **`Pᴬ` is closed under intersection.** -/
theorem InPO.inter {L₁ L₂ : Language} (h₁ : InPO A L₁) (h₂ : InPO A L₂) :
    InPO A (fun x => L₁ x ∧ L₂ x) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨.comp (CobO.ofCob .andC) [.comp c₁ [.proj 0], .comp c₂ [.proj 0]], fun x => ?_⟩
  simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj, CobO.eval_ofCob,
    Cob.eval_andC]
  by_cases h : c₁.eval A [x] = []
  · simp [h, hc₁ x]
  · simp [h, hc₁ x, hc₂ x]

/-- **`Pᴬ` is closed under union.** -/
theorem InPO.union {L₁ L₂ : Language} (h₁ : InPO A L₁) (h₂ : InPO A L₂) :
    InPO A (fun x => L₁ x ∨ L₂ x) := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  refine ⟨.comp (CobO.ofCob .orC) [.comp c₁ [.proj 0], .comp c₂ [.proj 0]], fun x => ?_⟩
  simp only [CobO.eval_comp, List.map_cons, List.map_nil, CobO.eval_proj, CobO.eval_ofCob,
    Cob.eval_orC]
  by_cases h : c₁.eval A [x] = []
  · simp [h, hc₁ x, hc₂ x]
  · simp [h, hc₁ x]

end Oracle
end Complexity
