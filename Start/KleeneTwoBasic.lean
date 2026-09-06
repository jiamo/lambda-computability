/-
**Kleene's second algebra `K₂`, part one: Baire space and its application.**

`Start/PCAKleene.lean` builds Kleene's *first* algebra `K₁`: the natural numbers with Turing
application.  Its counterpart at the other end of the Longley–Normann picture is Kleene's
*second* algebra `K₂`, whose underlying set is Baire space `ℕ → ℕ` and whose application is the
one of **function realizability**: `α` is read as a partial continuous operation on Baire space,
answering queries about finite initial segments of its argument.

Concretely, `α | β` is the function whose value at `n` is `α ⟨n, β(0), …, β(k-1)⟩ - 1` for the
least `k` at which that number is positive; it is undefined at `n` if no such `k` exists.

This module sets up the underlying space and the general tool used to construct elements of it:

* `Realizability.KleeneTwo.enc`, `.dec`, `.restr` — codes of finite sequences and the initial
  segment `⟨β 0, …, β (k-1)⟩`;
* `Realizability.KleeneTwo.AppAt`, `.appK` — the value of `α | β` at a point, and the resulting
  partial application `ℕ → ℕ → Part (ℕ → ℕ)`; `mem_appK` characterises its members;
* `Realizability.KleeneTwo.AppAt.exists_modulus` — **Kleene's continuity / the use principle**:
  a value of `α | β` is already produced by a finite initial segment of `β`;
* `Realizability.KleeneTwo.detAssoc` — the *canonical associate* of a continuous operation
  `F : (ℕ → ℕ) → (ℕ → ℕ)`: on the query `⟨y, s⟩` it answers the value `F α y` if that value is
  the same for every `α` extending the finite sequence `s`, and `0` ("no information") otherwise;
* `Realizability.KleeneTwo.appK_detAssoc` — the associate works: `detAssoc F | α = F α` whenever
  `F` is continuous (`Realizability.KleeneTwo.Cont`);
* `Realizability.KleeneTwo.kEl` — the combinator `k` of `K₂` and its computation rules.

The combinator `s`, which needs a genuine approximation argument, is built in
`Start/KleeneTwo.lean`, where the `PCA (ℕ → ℕ)` instance is assembled.
-/

import Start.PCA
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

namespace KleeneTwo

/-! ### Codes for finite sequences -/

/-- The code of a finite sequence of naturals. -/
def enc (l : List ℕ) : ℕ := Encodable.encode l

/-- The finite sequence coded by a natural number (the empty sequence for a non-code). -/
def dec (x : ℕ) : List ℕ := ((Encodable.decode x : Option (List ℕ))).getD []

@[simp] theorem dec_enc (l : List ℕ) : dec (enc l) = l := by
  simp [dec, enc]

/-! ### Initial segments -/

/-- The initial segment `⟨β 0, …, β (k-1)⟩` of `β`. -/
def restr (β : ℕ → ℕ) (k : ℕ) : List ℕ := (List.range k).map β

@[simp] theorem restr_length (β : ℕ → ℕ) (k : ℕ) : (restr β k).length = k := by
  simp [restr]

@[simp] theorem restr_zero (β : ℕ → ℕ) : restr β 0 = [] := by
  simp [restr]

theorem restr_getElem (β : ℕ → ℕ) {i k : ℕ} (h : i < (restr β k).length) :
    (restr β k)[i] = β i := by
  simp [restr]

theorem restr_succ (β : ℕ → ℕ) (k : ℕ) : restr β (k + 1) = restr β k ++ [β k] := by
  simp [restr, List.range_succ]

theorem restr_take (β : ℕ → ℕ) {k K : ℕ} (h : k ≤ K) : (restr β K).take k = restr β k := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left h]
  · intro i h1 h2
    simp [restr]

theorem restr_congr {β β' : ℕ → ℕ} {k : ℕ} (h : ∀ i < k, β' i = β i) :
    restr β' k = restr β k := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [restr, List.getElem_map, List.getElem_range]
    exact h i (by simpa [restr] using h1)

/-! ### The application of `K₂` -/

/-- The answer `α` gives to the query "the argument begins with `β 0, …, β (k-1)`; what is the
value at `n`?".  A positive answer `v + 1` means "the value is `v`", the answer `0` means "not
enough information yet". -/
def qv (α β : ℕ → ℕ) (n k : ℕ) : ℕ := α (enc (n :: restr β k))

/-- `AppAt α β n v` : the application `α | β` is defined at `n` with value `v`. -/
def AppAt (α β : ℕ → ℕ) (n v : ℕ) : Prop :=
  ∃ k, qv α β n k = v + 1 ∧ ∀ j < k, qv α β n j = 0

theorem AppAt.unique {α β : ℕ → ℕ} {n v w : ℕ} (h : AppAt α β n v) (h' : AppAt α β n w) :
    v = w := by
  obtain ⟨k, hk, hlt⟩ := h
  obtain ⟨k', hk', hlt'⟩ := h'
  rcases lt_trichotomy k k' with h1 | h1 | h1
  · have := hlt' k h1; omega
  · subst h1; omega
  · have := hlt k' h1; omega

/-- **Kleene's continuity**: a value of `α | β` is produced by a finite initial segment of `β`,
so it survives any change of `β` beyond that segment. -/
theorem AppAt.exists_modulus {α β : ℕ → ℕ} {n v : ℕ} (h : AppAt α β n v) :
    ∃ N, ∀ β' : ℕ → ℕ, (∀ i < N, β' i = β i) → AppAt α β' n v := by
  obtain ⟨k, hk, hlt⟩ := h
  refine ⟨k, fun β' hβ => ⟨k, ?_, fun j hj => ?_⟩⟩
  · rw [qv, restr_congr (fun i hi => hβ i hi)]
    exact hk
  · rw [qv, restr_congr (fun i hi => hβ i (by omega))]
    exact hlt j hj

/-- The application of `K₂`: `appK α β` is defined when `α | β` has a value at every point. -/
noncomputable def appK (α β : ℕ → ℕ) : Part (ℕ → ℕ) :=
  ⟨∃ f : ℕ → ℕ, ∀ n, AppAt α β n (f n), fun h => h.choose⟩

theorem mem_appK {α β f : ℕ → ℕ} : f ∈ appK α β ↔ ∀ n, AppAt α β n (f n) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro h
    have hd : ∃ f : ℕ → ℕ, ∀ n, AppAt α β n (f n) := ⟨f, h⟩
    refine ⟨hd, ?_⟩
    change hd.choose = f
    funext n
    exact (hd.choose_spec n).unique (h n)

theorem appK_dom_iff {α β : ℕ → ℕ} : (appK α β).Dom ↔ ∃ f : ℕ → ℕ, ∀ n, AppAt α β n (f n) :=
  Iff.rfl

/-! ### Extensions of finite sequences -/

/-- `Ext α s` : the sequence `α` begins with the finite sequence `s`. -/
def Ext (α : ℕ → ℕ) (s : List ℕ) : Prop := ∀ i, ∀ h : i < s.length, α i = s[i]

theorem ext_restr (α : ℕ → ℕ) (k : ℕ) : Ext α (restr α k) := by
  intro i h
  rw [restr_getElem]

theorem exists_ext (s : List ℕ) : ∃ α : ℕ → ℕ, Ext α s :=
  ⟨fun i => s.getD i 0, fun _i h => List.getD_eq_getElem s 0 h⟩

theorem ext_restr_of_agree {α α' : ℕ → ℕ} {N : ℕ} (h : ∀ i < N, α' i = α i) :
    Ext α' (restr α N) := by
  intro i hi
  rw [restr_getElem]
  exact h i (by simpa using hi)

/-! ### Least witnesses -/

theorem exists_least {P : ℕ → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m < n, ¬ P m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun m hm => Nat.find_min h hm⟩

/-! ### Canonical associates -/

open Classical in
/-- The **canonical associate** of an operation `F` on Baire space: at the query `⟨y, s⟩` it
answers `v + 1` if `F α y = v` for *every* `α` extending the finite sequence `s`, and `0`
otherwise. -/
noncomputable def detAssoc (F : (ℕ → ℕ) → ℕ → ℕ) (z : ℕ) : ℕ :=
  match dec z with
  | [] => 0
  | y :: s => if h : ∃ v, ∀ α, Ext α s → F α y = v then h.choose + 1 else 0

theorem detAssoc_nil {F : (ℕ → ℕ) → ℕ → ℕ} {z : ℕ} (hz : dec z = []) : detAssoc F z = 0 := by
  unfold detAssoc; rw [hz]

open Classical in
theorem detAssoc_cons {F : (ℕ → ℕ) → ℕ → ℕ} {z y : ℕ} {s : List ℕ} (hz : dec z = y :: s) :
    detAssoc F z = if h : ∃ v, ∀ α, Ext α s → F α y = v then h.choose + 1 else 0 := by
  unfold detAssoc; rw [hz]

/-- A positive answer of the canonical associate is the true value. -/
theorem detAssoc_sound {F : (ℕ → ℕ) → ℕ → ℕ} {z y : ℕ} {s : List ℕ} (hz : dec z = y :: s)
    {α : ℕ → ℕ} (hα : Ext α s) {v : ℕ} (h : detAssoc F z = v + 1) : F α y = v := by
  rw [detAssoc_cons hz] at h
  split at h
  · rename_i hex
    have h1 := hex.choose_spec α hα
    omega
  · omega

/-- If the value is already determined by `s`, the canonical associate answers. -/
theorem detAssoc_pos {F : (ℕ → ℕ) → ℕ → ℕ} {z y : ℕ} {s : List ℕ} (hz : dec z = y :: s)
    (hdet : ∃ v, ∀ α, Ext α s → F α y = v) : 0 < detAssoc F z := by
  rw [detAssoc_cons hz, dif_pos hdet]
  omega

/-- Continuity of an operation on Baire space: every value depends on a finite initial segment
of the argument. -/
def Cont (F : (ℕ → ℕ) → ℕ → ℕ) : Prop :=
  ∀ (α : ℕ → ℕ) (y : ℕ), ∃ N, ∀ α' : ℕ → ℕ, (∀ i < N, α' i = α i) → F α' y = F α y

/-- **The canonical associate computes its operation**: for a continuous `F`, applying
`detAssoc F` to `α` in `K₂` returns `F α`. -/
theorem appK_detAssoc {F : (ℕ → ℕ) → ℕ → ℕ} (hF : Cont F) (α : ℕ → ℕ) :
    appK (detAssoc F) α = Part.some (F α) := by
  refine Part.eq_some_iff.2 (mem_appK.2 fun y => ?_)
  obtain ⟨N, hN⟩ := hF α y
  have hdet : ∃ v, ∀ α', Ext α' (restr α N) → F α' y = v := by
    refine ⟨F α y, fun α' h => hN α' fun i hi => ?_⟩
    have := h i (by simpa using hi)
    rw [restr_getElem] at this
    exact this
  have hposN : 0 < qv (detAssoc F) α y N := detAssoc_pos (dec_enc _) hdet
  obtain ⟨k, hk, hmin⟩ := exists_least (P := fun k => 0 < qv (detAssoc F) α y k) ⟨N, hposN⟩
  obtain ⟨v, hv⟩ : ∃ v, qv (detAssoc F) α y k = v + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hk).symm⟩
  have hval : F α y = v := detAssoc_sound (dec_enc _) (ext_restr α k) hv
  refine ⟨k, ?_, fun j hj => ?_⟩
  · rw [hv, hval]
  · have := hmin j hj; omega

/-! ### The combinator `k` -/

theorem cont_const (a : ℕ → ℕ) : Cont (fun _ : ℕ → ℕ => a) := fun _ _ => ⟨0, fun _ _ => rfl⟩

/-- The element `k · a` of `K₂`: the associate of the constant operation with value `a`. -/
noncomputable def constAssoc (a : ℕ → ℕ) : ℕ → ℕ := detAssoc (fun _ : ℕ → ℕ => a)

theorem constAssoc_cons {a : ℕ → ℕ} {z y : ℕ} {s : List ℕ} (hz : dec z = y :: s) :
    constAssoc a z = a y + 1 := by
  have hdet : ∃ v, ∀ α, Ext α s → (fun _ : ℕ → ℕ => a) α y = v := ⟨a y, fun _ _ => rfl⟩
  rw [constAssoc, detAssoc_cons hz, dif_pos hdet]
  obtain ⟨α₀, hα₀⟩ := exists_ext s
  have h1 : a y = hdet.choose := hdet.choose_spec α₀ hα₀
  omega

theorem constAssoc_nil {a : ℕ → ℕ} {z : ℕ} (hz : dec z = []) : constAssoc a z = 0 :=
  detAssoc_nil hz

theorem cont_constAssoc : Cont constAssoc := by
  intro a z
  cases hz : dec z with
  | nil => exact ⟨0, fun a' _ => by rw [constAssoc_nil hz, constAssoc_nil hz]⟩
  | cons y s =>
      refine ⟨y + 1, fun a' h => ?_⟩
      rw [constAssoc_cons hz, constAssoc_cons hz, h y (by omega)]

/-- The combinator `k` of `K₂`. -/
noncomputable def kEl : ℕ → ℕ := detAssoc constAssoc

theorem appK_kEl (a : ℕ → ℕ) : appK kEl a = Part.some (constAssoc a) :=
  appK_detAssoc cont_constAssoc a

theorem appK_constAssoc (a b : ℕ → ℕ) : appK (constAssoc a) b = Part.some a :=
  appK_detAssoc (cont_const a) b

end KleeneTwo

end Realizability
