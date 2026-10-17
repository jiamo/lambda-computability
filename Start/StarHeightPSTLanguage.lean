import Start.StarHeightS4

/-!
# The Pin–Straubing–Thérien candidate `L_PST`

`L_PST = (a b* a ∪ b a* b (a b* a)* b a* b)*` over `{a, b}`, proposed in Section 8 of Pin,
Straubing and Thérien, *Some results on the generalized star-height problem*, as a possible
language of generalized star height `2`.

* `PST.LPST`: the regular expression, with the operations of `Language`.
* `PST.LPST_eq`: the automaton description.  On the states `{0, 1, 2}`, `a` acts as `(0 1)` and
  `b` as `(0 2)`; then `u ∈ L_PST` iff `0·u = 0` and the number of `b` read in the state `0` is
  even.

The proof factors a word returning to `0` into first returns `a b* a` (no `b` read in `0`) and
`b a* b` (one `b` read in `0`).
-/

namespace GeneralizedStarHeight

namespace PST

open scoped Computability

/-- The alphabet `{a, b}`. -/
inductive AB
  | a
  | b
  deriving DecidableEq

open AB

instance : Fintype AB := ⟨{a, b}, fun x => by cases x <;> simp⟩

/-- `a` acts as `(0 1)`, `b` as `(0 2)`. -/
def move : Fin 3 → AB → Fin 3
  | s, a => ![1, 0, 2] s
  | s, b => ![2, 1, 0] s

/-- The state `s·w`. -/
def stateOf (s : Fin 3) (w : List AB) : Fin 3 := w.foldl move s

/-- The number of `b` read in the state `0`, starting from `s`. -/
def b0count : Fin 3 → List AB → ℕ
  | _, [] => 0
  | s, x :: w => (if x = b ∧ s = 0 then 1 else 0) + b0count (move s x) w

/-- **The PST candidate** `(a b* a ∪ b a* b (a b* a)* b a* b)*`. -/
def LPST : Language AB :=
  ({[a]} * {[b]}∗ * {[a]} +
    {[b]} * {[a]}∗ * {[b]} * ({[a]} * {[b]}∗ * {[a]})∗ * {[b]} * {[a]}∗ * {[b]})∗

/-- `a b* a`. -/
def X0 : Language AB := {[a]} * {[b]}∗ * {[a]}

/-- `b a* b`. -/
def X1 : Language AB := {[b]} * {[a]}∗ * {[b]}

lemma LPST_eq_X : LPST = (X0 + X1 * X0∗ * X1)∗ := by
  simp only [LPST, X0, X1, mul_assoc]

/-! ### The automaton -/

lemma stateOf_cons (s : Fin 3) (x : AB) (w : List AB) : stateOf s (x :: w) = stateOf (move s x) w :=
  rfl

lemma stateOf_append (s : Fin 3) (u v : List AB) : stateOf s (u ++ v) = stateOf (stateOf s u) v :=
  List.foldl_append

lemma b0count_append : ∀ (s : Fin 3) (u v : List AB),
    b0count s (u ++ v) = b0count s u + b0count (stateOf s u) v
  | s, [], v => by simp [b0count, stateOf]
  | s, x :: u, v => by
      rw [List.cons_append, b0count, b0count, b0count_append (move s x) u v, stateOf_cons]
      omega

lemma ret_append {u : List AB} (hu : stateOf 0 u = 0) (v : List AB) :
    stateOf 0 (u ++ v) = stateOf 0 v ∧ b0count 0 (u ++ v) = b0count 0 u + b0count 0 v := by
  rw [stateOf_append, b0count_append, hu]
  exact ⟨rfl, rfl⟩

lemma stateOf_rep_b (n : ℕ) : stateOf 1 (List.replicate n b) = 1 ∧ b0count 1 (List.replicate n b) = 0 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      rw [List.replicate_succ, stateOf_cons, b0count]
      exact ⟨ih.1, by rw [show move 1 b = 1 from rfl, ih.2]; rfl⟩

lemma stateOf_rep_a (n : ℕ) : stateOf 2 (List.replicate n a) = 2 ∧ b0count 2 (List.replicate n a) = 0 := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      rw [List.replicate_succ, stateOf_cons, b0count]
      exact ⟨ih.1, by rw [show move 2 a = 2 from rfl, ih.2]; rfl⟩

/-! ### Membership in the building blocks -/

lemma mem_kstar_single (c : AB) (w : List AB) :
    w ∈ ({[c]} : Language AB)∗ ↔ ∃ n, w = List.replicate n c := by
  constructor
  · intro hw
    obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hw
    clear hw
    induction L with
    | nil => exact ⟨0, rfl⟩
    | cons y L ih =>
        obtain ⟨n, hn⟩ := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
        have hy : y = [c] := hL y List.mem_cons_self
        exact ⟨n + 1, by rw [List.flatten_cons, hn, hy, List.replicate_succ]; rfl⟩
  · rintro ⟨n, rfl⟩
    refine Language.mem_kstar.mpr ⟨List.replicate n [c], ?_, fun y hy => ?_⟩
    · induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, List.replicate_succ, List.flatten_cons, ← ih]; rfl
    · rw [List.eq_of_mem_replicate hy]; rfl

lemma mem_X0 (y : List AB) : y ∈ X0 ↔ ∃ n, y = a :: (List.replicate n b ++ [a]) := by
  constructor
  · intro hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hy
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Language.mem_mul.mp hu
    obtain ⟨n, rfl⟩ := (mem_kstar_single b u2).mp hu2
    have h1 : u1 = [a] := hu1
    have h2 : v = [a] := hv
    exact ⟨n, by rw [h1, h2]; rfl⟩
  · rintro ⟨n, rfl⟩
    exact Language.mem_mul.mpr ⟨[a] ++ List.replicate n b, Language.mem_mul.mpr
      ⟨[a], rfl, _, (mem_kstar_single b _).mpr ⟨n, rfl⟩, rfl⟩, [a], rfl, by simp⟩

lemma mem_X1 (y : List AB) : y ∈ X1 ↔ ∃ n, y = b :: (List.replicate n a ++ [b]) := by
  constructor
  · intro hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hy
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Language.mem_mul.mp hu
    obtain ⟨n, rfl⟩ := (mem_kstar_single a u2).mp hu2
    have h1 : u1 = [b] := hu1
    have h2 : v = [b] := hv
    exact ⟨n, by rw [h1, h2]; rfl⟩
  · rintro ⟨n, rfl⟩
    exact Language.mem_mul.mpr ⟨[b] ++ List.replicate n a, Language.mem_mul.mpr
      ⟨[b], rfl, _, (mem_kstar_single a _).mpr ⟨n, rfl⟩, rfl⟩, [b], rfl, by simp⟩

lemma X0_ret {y : List AB} (hy : y ∈ X0) : stateOf 0 y = 0 ∧ b0count 0 y = 0 := by
  obtain ⟨n, rfl⟩ := (mem_X0 y).mp hy
  have h := stateOf_rep_b n
  rw [stateOf_cons, b0count, stateOf_append, b0count_append, show move 0 a = 1 from rfl, h.1, h.2]
  exact ⟨rfl, rfl⟩

lemma X1_ret {y : List AB} (hy : y ∈ X1) : stateOf 0 y = 0 ∧ b0count 0 y = 1 := by
  obtain ⟨n, rfl⟩ := (mem_X1 y).mp hy
  have h := stateOf_rep_a n
  rw [stateOf_cons, b0count, stateOf_append, b0count_append, show move 0 b = 2 from rfl, h.1, h.2]
  exact ⟨rfl, rfl⟩

lemma kstar_cons {l : Language AB} {y v : List AB} (hy : y ∈ l) (hv : v ∈ l∗) : y ++ v ∈ l∗ := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hv
  refine Language.mem_kstar.mpr ⟨y :: L, by simp, fun z hz => ?_⟩
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hy
  · exact hL z hz

lemma X0star_ret {v : List AB} (hv : v ∈ X0∗) : stateOf 0 v = 0 ∧ b0count 0 v = 0 := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hv
  clear hv
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons y L ih =>
      have hy := X0_ret (hL y List.mem_cons_self)
      have ih' := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
      rw [List.flatten_cons]
      obtain ⟨h1, h2⟩ := ret_append hy.1 L.flatten
      exact ⟨h1.trans ih'.1, by rw [h2, hy.2, ih'.2]⟩

/-! ### `L_PST ⊆` the automaton language -/

lemma Y_ret {y : List AB} (hy : y ∈ X0 + X1 * X0∗ * X1) :
    stateOf 0 y = 0 ∧ b0count 0 y % 2 = 0 := by
  rcases (Language.mem_add _ _ _).mp hy with hy | hy
  · have := X0_ret hy
    exact ⟨this.1, by rw [this.2]⟩
  · obtain ⟨uv, huv, t, ht, rfl⟩ := Language.mem_mul.mp hy
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp huv
    have h1 := X1_ret hu
    have h2 := X0star_ret hv
    have h3 := X1_ret ht
    obtain ⟨e1, e2⟩ := ret_append h1.1 v
    obtain ⟨e3, e4⟩ := ret_append (e1.trans h2.1) t
    refine ⟨e3.trans h3.1, ?_⟩
    rw [e4, e2, h1.2, h2.2, h3.2]

lemma LPST_sub {w : List AB} (hw : w ∈ LPST) : stateOf 0 w = 0 ∧ b0count 0 w % 2 = 0 := by
  rw [LPST_eq_X] at hw
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hw
  clear hw
  induction L with
  | nil => exact ⟨rfl, rfl⟩
  | cons y L ih =>
      have hy := Y_ret (hL y List.mem_cons_self)
      have ih' := ih fun z hz => hL z (List.mem_cons_of_mem _ hz)
      rw [List.flatten_cons]
      obtain ⟨h1, h2⟩ := ret_append hy.1 L.flatten
      exact ⟨h1.trans ih'.1, by rw [h2]; omega⟩

/-! ### The automaton language `⊆ L_PST` -/

lemma split_b : ∀ t : List AB, stateOf 1 t = 0 → ∃ n t', t = List.replicate n b ++ a :: t'
  | [], h => absurd h (by decide)
  | a :: t, _ => ⟨0, t, rfl⟩
  | b :: t, h => by
      obtain ⟨n, t', rfl⟩ := split_b t h
      exact ⟨n + 1, t', rfl⟩

lemma split_a : ∀ t : List AB, stateOf 2 t = 0 → ∃ n t', t = List.replicate n a ++ b :: t'
  | [], h => absurd h (by decide)
  | b :: t, _ => ⟨0, t, rfl⟩
  | a :: t, h => by
      obtain ⟨n, t', rfl⟩ := split_a t h
      exact ⟨n + 1, t', rfl⟩

/-- **First returns.** -/
lemma first_return {w : List AB} (hne : w ≠ []) (hw : stateOf 0 w = 0) :
    ∃ y t, w = y ++ t ∧ stateOf 0 t = 0 ∧ t.length < w.length ∧
      ((y ∈ X0 ∧ b0count 0 w = b0count 0 t) ∨ (y ∈ X1 ∧ b0count 0 w = b0count 0 t + 1)) := by
  obtain ⟨x, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  cases x with
  | a =>
      obtain ⟨n, t', rfl⟩ := split_b t hw
      have hy : a :: (List.replicate n b ++ [a]) ∈ X0 := (mem_X0 _).mpr ⟨n, rfl⟩
      have hsplit : a :: (List.replicate n b ++ a :: t') =
          a :: (List.replicate n b ++ [a]) ++ t' := by simp
      obtain ⟨e1, e2⟩ := ret_append (X0_ret hy).1 t'
      rw [hsplit] at hw ⊢
      refine ⟨_, t', rfl, e1 ▸ hw, by simp; omega, Or.inl ⟨hy, ?_⟩⟩
      rw [e2, (X0_ret hy).2, zero_add]
  | b =>
      obtain ⟨n, t', rfl⟩ := split_a t hw
      have hy : b :: (List.replicate n a ++ [b]) ∈ X1 := (mem_X1 _).mpr ⟨n, rfl⟩
      have hsplit : b :: (List.replicate n a ++ b :: t') =
          b :: (List.replicate n a ++ [b]) ++ t' := by simp
      obtain ⟨e1, e2⟩ := ret_append (X1_ret hy).1 t'
      rw [hsplit] at hw ⊢
      refine ⟨_, t', rfl, e1 ▸ hw, by simp; omega, Or.inr ⟨hy, ?_⟩⟩
      rw [e2, (X1_ret hy).2, add_comm]

lemma sup_aux : ∀ (n : ℕ) (w : List AB), w.length ≤ n → stateOf 0 w = 0 →
    (b0count 0 w % 2 = 0 → w ∈ (X0 + X1 * X0∗ * X1)∗) ∧
      (b0count 0 w % 2 = 1 → w ∈ X0∗ * X1 * (X0 + X1 * X0∗ * X1)∗) := by
  intro n
  induction n with
  | zero =>
      intro w hl _
      have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨fun _ => Language.nil_mem_kstar _, fun h => absurd h (by decide)⟩
  | succ n ih =>
      intro w hl hw
      by_cases hne : w = []
      · subst hne
        exact ⟨fun _ => Language.nil_mem_kstar _, fun h => absurd h (by decide)⟩
      obtain ⟨y, t, rfl, ht, htl, hy⟩ := first_return hne hw
      have iht := ih t (by omega) ht
      rcases hy with ⟨hy, hc⟩ | ⟨hy, hc⟩
      · have hyY : y ∈ X0 + X1 * X0∗ * X1 := (Language.mem_add _ _ _).mpr (Or.inl hy)
        refine ⟨fun h => kstar_cons hyY (iht.1 (by omega)), fun h => ?_⟩
        obtain ⟨pq, hpq, r, hr, hpqr⟩ := Language.mem_mul.mp (iht.2 (by omega))
        obtain ⟨p, hp, q, hq, rfl⟩ := Language.mem_mul.mp hpq
        rw [← hpqr]
        exact Language.mem_mul.mpr ⟨y ++ p ++ q, Language.mem_mul.mpr
          ⟨y ++ p, kstar_cons hy hp, q, hq, rfl⟩, r, hr, by simp⟩
      · refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨pq, hpq, r, hr, hpqr⟩ := Language.mem_mul.mp (iht.2 (by omega))
          obtain ⟨p, hp, q, hq, rfl⟩ := Language.mem_mul.mp hpq
          rw [← hpqr]
          have hY : y ++ p ++ q ∈ X0 + X1 * X0∗ * X1 := (Language.mem_add _ _ _).mpr (Or.inr
            (Language.mem_mul.mpr ⟨y ++ p, Language.mem_mul.mpr ⟨y, hy, p, hp, rfl⟩, q, hq, rfl⟩))
          have := kstar_cons hY hr
          simpa using this
        · exact Language.mem_mul.mpr ⟨[] ++ y, Language.mem_mul.mpr
            ⟨[], Language.nil_mem_kstar _, y, hy, rfl⟩, t, iht.1 (by omega), by simp⟩

/-- **The automaton description of `L_PST`.** -/
theorem LPST_eq : LPST = {u | stateOf 0 u = 0 ∧ b0count 0 u % 2 = 0} := by
  ext u
  constructor
  · exact LPST_sub
  · rintro ⟨h1, h2⟩
    rw [LPST_eq_X]
    exact (sup_aux u.length u le_rfl h1).1 h2

end PST

end GeneralizedStarHeight
