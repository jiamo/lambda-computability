/-
**The pairing macro for counter machines** — task `M25-KCM-UNIVERSAL` (round 9, part B),
continuing `Start/MinskyMacros.lean`.

* `Minsky.Macro.cmp_run` — **comparison by simultaneous decrement**: the two-instruction loop
  `test y LGE L₁; test x LLT L₀` exits at `LGE` when `r y ≤ r x` (with `y` emptied) and at
  `LLT` when `r x < r y` (with `x` emptied), touching only `x` and `y`;
* `Minsky.Macro.pairCode` — the 51-instruction program computing `r k += Nat.pair (r i) (r j)`
  (copies of the arguments, the comparison, and in each branch the arithmetic of
  `Nat.pair a b = if a < b then b * b + a else a * a + a + b` with `mul`, `copy`, `clear`);
* `Minsky.Macro.pair_run` — **correctness of the pairing macro**, placed at any offset `o` of
  any program: the arguments are preserved, the scratch registers `x y t` are zero before and
  after, and nothing else changes.
-/

import Start.MinskyMacros

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Macro

open Function

theorem AgreeOff.get {r r' : ℕ → ℕ} {xs : List ℕ} (h : AgreeOff r r' xs) {x : ℕ}
    (hx : x ∉ xs) : r' x = r x := h x hx

/-! ### Comparison by simultaneous decrement -/

/-- **Comparison by simultaneous decrement.**  At label `c`: `test y lge c₁`; at `c₁`:
`test x llt c`.  The loop exits at `lge` with `y` emptied when `r y ≤ r x`, and at `llt` with
`x` emptied when `r x < r y`; only `x` and `y` change. -/
theorem cmp_run {M : KM} {c c₁ lge llt x y : ℕ} (hxy : x ≠ y)
    (h₀ : M[c]? = some (.test y lge c₁)) (h₁ : M[c₁]? = some (.test x llt c)) :
    ∀ (r : ℕ → ℕ), ∃ r', AgreeOff r r' [x, y] ∧
      ((r y ≤ r x ∧ Run M ⟨c, r⟩ ⟨lge, r'⟩ ∧ r' y = 0) ∨
       (r x < r y ∧ Run M ⟨c, r⟩ ⟨llt, r'⟩ ∧ r' x = 0)) := by
  intro r
  induction hn : r y generalizing r with
  | zero =>
      exact ⟨r, fun _ _ => rfl, Or.inl ⟨Nat.zero_le _, .single (KM.Step.zero h₀ hn), hn⟩⟩
  | succ n ih =>
      have hs₁ : KM.Step M ⟨c, r⟩ ⟨c₁, update r y n⟩ := KM.Step.dec h₀ hn
      rcases hx : r x with _ | m
      · have hs₂ : KM.Step M ⟨c₁, update r y n⟩ ⟨llt, update r y n⟩ :=
          KM.Step.zero h₁ (by simp [hxy, hx])
        refine ⟨update r y n, ?_, Or.inr ⟨by omega, .head hs₁ (.single hs₂), by simp [hxy, hx]⟩⟩
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp [hz.2]
      · have hs₂ : KM.Step M ⟨c₁, update r y n⟩ ⟨c, update (update r y n) x m⟩ :=
          KM.Step.dec h₁ (by simp [hxy, hx])
        obtain ⟨r', hag, hcase⟩ := ih (update (update r y n) x m) (by simp [Ne.symm hxy])
        refine ⟨r', ?_, ?_⟩
        · intro z hz
          rw [hag z hz]
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          simp [hz.1, hz.2]
        · rcases hcase with ⟨hle, hrun, h0⟩ | ⟨hlt, hrun, h0⟩
          · exact Or.inl ⟨by simp only [update_self] at hle; omega, .head hs₁ (.head hs₂ hrun), h0⟩
          · exact Or.inr ⟨by simp only [update_self] at hlt; omega, .head hs₁ (.head hs₂ hrun), h0⟩

/-! ### The pairing macro -/

/-- **The pairing program** at offset `o`, exiting at `e`: `r k += Nat.pair (r i) (r j)`, with
scratch registers `x y t`. -/
def pairCode (o e i j k x y t : ℕ) : List KInstr :=
  [.test i (o + 3) (o + 1),
   .inc x (o + 2),
   .inc t (o),
   .test t (o + 5) (o + 4),
   .inc i (o + 3),
   .test j (o + 5 + 3) (o + 5 + 1),
   .inc y (o + 5 + 2),
   .inc t (o + 5),
   .test t (o + 10) (o + 5 + 4),
   .inc j (o + 5 + 3),
   .test y (o + 12) (o + 11),
   .test x (o + 34) (o + 10),
   .test x (o + 13) (o + 12),
   .test i (o + 13 + 3) (o + 13 + 1),
   .inc x (o + 13 + 2),
   .inc t (o + 13),
   .test t (o + 18) (o + 13 + 4),
   .inc i (o + 13 + 3),
   .test x (o + 24) (o + 18 + 1),
   .test i (o + 18 + 1 + 3) (o + 18 + 1 + 1),
   .inc k (o + 18 + 1 + 2),
   .inc t (o + 18 + 1),
   .test t (o + 18) (o + 18 + 1 + 4),
   .inc i (o + 18 + 1 + 3),
   .test i (o + 24 + 3) (o + 24 + 1),
   .inc k (o + 24 + 2),
   .inc t (o + 24),
   .test t (o + 29) (o + 24 + 4),
   .inc i (o + 24 + 3),
   .test j (o + 29 + 3) (o + 29 + 1),
   .inc k (o + 29 + 2),
   .inc t (o + 29),
   .test t e (o + 29 + 4),
   .inc j (o + 29 + 3),
   .test y (o + 35) (o + 34),
   .test j (o + 35 + 3) (o + 35 + 1),
   .inc x (o + 35 + 2),
   .inc t (o + 35),
   .test t (o + 40) (o + 35 + 4),
   .inc j (o + 35 + 3),
   .test x (o + 46) (o + 40 + 1),
   .test j (o + 40 + 1 + 3) (o + 40 + 1 + 1),
   .inc k (o + 40 + 1 + 2),
   .inc t (o + 40 + 1),
   .test t (o + 40) (o + 40 + 1 + 4),
   .inc j (o + 40 + 1 + 3),
   .test i (o + 46 + 3) (o + 46 + 1),
   .inc k (o + 46 + 2),
   .inc t (o + 46),
   .test t e (o + 46 + 4),
   .inc i (o + 46 + 3)]

theorem pairCode_length (o e i j k x y t : ℕ) : (pairCode o e i j k x y t).length = 51 := rfl

/-- The program `M` contains the code `L` at offset `o`. -/
def Contains (M : KM) (o : ℕ) (L : List KInstr) : Prop :=
  ∀ n (hn : n < L.length), M[o + n]? = some L[n]

theorem Contains.fetch {M : KM} {o : ℕ} {L : List KInstr} (h : Contains M o L) (n : ℕ)
    {ins : KInstr} (hn : L[n]? = some ins) {p : ℕ} (hp : p = o + n) : M[p]? = some ins := by
  subst hp
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 hn
  rw [h n hlt, heq]

set_option maxHeartbeats 4000000 in
/-- **Correctness of the pairing macro.** -/
theorem pair_run {M : KM} {o e i j k x y t : ℕ} (hnd : [i, j, k, x, y, t].Nodup)
    (hM : Contains M o (pairCode o e i j k x y t)) (r : ℕ → ℕ)
    (hx : r x = 0) (hy : r y = 0) (ht : r t = 0) :
    ∃ r', Run M ⟨o, r⟩ ⟨e, r'⟩ ∧ r' k = r k + Nat.pair (r i) (r j) ∧ r' i = r i ∧
      r' j = r j ∧ r' x = 0 ∧ r' y = 0 ∧ r' t = 0 ∧ AgreeOff r r' [i, j, k, x, y, t] := by
  have hij : i ≠ j := by intro h; simp [h] at hnd
  have hik : i ≠ k := by intro h; simp [h] at hnd
  have hix : i ≠ x := by intro h; simp [h] at hnd
  have hiy : i ≠ y := by intro h; simp [h] at hnd
  have hit : i ≠ t := by intro h; simp [h] at hnd
  have hjk : j ≠ k := by intro h; simp [h] at hnd
  have hjx : j ≠ x := by intro h; simp [h] at hnd
  have hjy : j ≠ y := by intro h; simp [h] at hnd
  have hjt : j ≠ t := by intro h; simp [h] at hnd
  have hkx : k ≠ x := by intro h; simp [h] at hnd
  have hky : k ≠ y := by intro h; simp [h] at hnd
  have hkt : k ≠ t := by intro h; simp [h] at hnd
  have hxy : x ≠ y := by intro h; simp [h] at hnd
  have hxt : x ≠ t := by intro h; simp [h] at hnd
  have hyt : y ≠ t := by intro h; simp [h] at hnd
  -- copy i → x
  obtain ⟨r₁, hrun₁, hi₁, hx₁, ht₁, hag₁⟩ := copy_run hix hit hxt
    (hM.fetch 0 rfl (by omega)) (hM.fetch 1 rfl (by omega))
    (hM.fetch 2 rfl (by omega)) (hM.fetch 3 rfl (by omega))
    (hM.fetch 4 rfl (by omega)) r ht
  -- copy j → y
  obtain ⟨r₂, hrun₂, hj₂, hy₂, ht₂, hag₂⟩ := copy_run (M := M) (o := o + 5) (e := o + 10) hjy hjt
    hyt (hM.fetch 5 rfl (by omega))
    (hM.fetch 6 rfl (by omega))
    (hM.fetch 7 rfl (by omega))
    (hM.fetch 8 rfl (by omega))
    (hM.fetch 9 rfl (by omega)) r₁ ht₁
  have ha₂ : r₂ i = r i := by rw [hag₂.get (by simp; omega), hi₁]
  have hb₂ : r₂ j = r j := by rw [hj₂, hag₁.get (by simp; omega)]
  have hx₂ : r₂ x = r i := by rw [hag₂.get (by simp; omega), hx₁, hx]; simp
  have hy₂' : r₂ y = r j := by rw [hy₂, hag₁.get (by simp; omega), hy, hag₁.get (by simp; omega)]
                               simp
  have hk₂ : r₂ k = r k := by rw [hag₂.get (by simp; omega), hag₁.get (by simp; omega)]
  have hag₁₂ : AgreeOff r r₂ [i, j, k, x, y, t] := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hag₂.get (by simp; omega), hag₁.get (by simp; omega)]
  -- compare
  obtain ⟨r₃, hag₃, hcase⟩ := cmp_run (M := M) (c := o + 10) (c₁ := o + 11) (lge := o + 12)
    (llt := o + 34) hxy (hM.fetch 10 rfl (by omega))
    (hM.fetch 11 rfl (by omega)) r₂
  have ha₃ : r₃ i = r i := by rw [hag₃.get (by simp; omega), ha₂]
  have hb₃ : r₃ j = r j := by rw [hag₃.get (by simp; omega), hb₂]
  have hk₃ : r₃ k = r k := by rw [hag₃.get (by simp; omega), hk₂]
  have ht₃ : r₃ t = 0 := by rw [hag₃.get (by simp; omega), ht₂]
  have hag₁₃ : AgreeOff r r₃ [i, j, k, x, y, t] := by
    intro z hz
    have hz' := hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz'
    rw [hag₃.get (by simp; omega), hag₁₂ z hz]
  rcases hcase with ⟨hle, hrun₃, hy₃⟩ | ⟨hlt, hrun₃, hx₃⟩
  · -- b ≤ a: k += a * a + a + b
    rw [hx₂, hy₂'] at hle
    have hrun₄ := clear_run (M := M) (o := o + 12) (e := o + 13) (i := x)
      (hM.fetch 12 rfl (by omega)) r₃
    set r₄ := update r₃ x 0 with hr₄
    obtain ⟨r₅, hrun₅, hi₅, hx₅, ht₅, hag₅⟩ := copy_run (M := M) (o := o + 13) (e := o + 18)
      hix hit hxt (hM.fetch 13 rfl (by omega))
      (hM.fetch 14 rfl (by omega))
      (hM.fetch 15 rfl (by omega))
      (hM.fetch 16 rfl (by omega))
      (hM.fetch 17 rfl (by omega)) r₄ (by rw [hr₄, update_of_ne (Ne.symm hxt), ht₃])
    obtain ⟨r₆, hrun₆, hx₆, hi₆, hk₆, ht₆, hag₆⟩ := mul_run (M := M) (o := o + 18) (e := o + 24)
      (Ne.symm hix) hkx.symm hxt hik hit hkt
      (hM.fetch 18 rfl (by omega))
      (hM.fetch 19 rfl (by omega))
      (hM.fetch 20 rfl (by omega))
      (hM.fetch 21 rfl (by omega))
      (hM.fetch 22 rfl (by omega))
      (hM.fetch 23 rfl (by omega)) r₅ ht₅
    obtain ⟨r₇, hrun₇, hi₇, hk₇, ht₇, hag₇⟩ := copy_run (M := M) (o := o + 24) (e := o + 29)
      hik hit hkt (hM.fetch 24 rfl (by omega))
      (hM.fetch 25 rfl (by omega))
      (hM.fetch 26 rfl (by omega))
      (hM.fetch 27 rfl (by omega))
      (hM.fetch 28 rfl (by omega)) r₆ ht₆
    obtain ⟨r₈, hrun₈, hj₈, hk₈, ht₈, hag₈⟩ := copy_run (M := M) (o := o + 29) (e := e)
      hjk hjt hkt (hM.fetch 29 rfl (by omega))
      (hM.fetch 30 rfl (by omega))
      (hM.fetch 31 rfl (by omega))
      (hM.fetch 32 rfl (by omega))
      (hM.fetch 33 rfl (by omega)) r₇ ht₇
    -- the values
    have ha₄ : r₄ i = r i := by simp [hr₄, hix, ha₃]
    have hi₅' : r₅ i = r i := by rw [hi₅, ha₄]
    have hx₅' : r₅ x = r i := by rw [hx₅, ha₄]; simp [hr₄]
    have hk₅ : r₅ k = r k := by rw [hag₅.get (by simp; omega)]; simp [hr₄, hkx, hk₃]
    have hj₅ : r₅ j = r j := by rw [hag₅.get (by simp; omega)]; simp [hr₄, hjx, hb₃]
    have hy₅ : r₅ y = 0 := by rw [hag₅.get (by simp; omega)]; simp [hr₄, Ne.symm hxy, hy₃]
    have hi₆' : r₆ i = r i := by rw [hi₆, hi₅']
    have hk₆' : r₆ k = r k + r i * r i := by rw [hk₆, hk₅, hx₅', hi₅']
    have hj₆ : r₆ j = r j := by rw [hag₆.get (by simp; omega), hj₅]
    have hy₆ : r₆ y = 0 := by rw [hag₆.get (by simp; omega), hy₅]
    have hk₇' : r₇ k = r k + r i * r i + r i := by rw [hk₇, hk₆', hi₆']
    have hj₇ : r₇ j = r j := by rw [hag₇.get (by simp; omega), hj₆]
    refine ⟨r₈, hrun₁.trans (hrun₂.trans (hrun₃.trans (hrun₄.trans (hrun₅.trans
      (hrun₆.trans (hrun₇.trans hrun₈)))))), ?_, ?_, ?_, ?_, ?_, ht₈, ?_⟩
    · rw [hk₈, hk₇', hj₇, Nat.pair, ite_eq_right (by omega)]; ring
    · rw [hag₈.get (by simp; omega), hi₇, hi₆']
    · rw [hj₈, hj₇]
    · rw [hag₈.get (by simp; omega), hag₇.get (by simp; omega), hx₆]
    · rw [hag₈.get (by simp; omega), hag₇.get (by simp; omega), hy₆]
    · intro z hz
      have hz' := hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz'
      rw [hag₈.get (by simp; omega), hag₇.get (by simp; omega), hag₆.get (by simp; omega),
        hag₅.get (by simp; omega)]
      simp only [hr₄]
      rw [update_of_ne hz'.2.2.2.1, hag₁₃ z hz]
  · -- a < b: k += b * b + a
    rw [hx₂, hy₂'] at hlt
    have hrun₄ := clear_run (M := M) (o := o + 34) (e := o + 35) (i := y)
      (hM.fetch 34 rfl (by omega)) r₃
    set r₄ := update r₃ y 0 with hr₄
    obtain ⟨r₅, hrun₅, hj₅, hx₅, ht₅, hag₅⟩ := copy_run (M := M) (o := o + 35) (e := o + 40)
      hjx hjt hxt (hM.fetch 35 rfl (by omega))
      (hM.fetch 36 rfl (by omega))
      (hM.fetch 37 rfl (by omega))
      (hM.fetch 38 rfl (by omega))
      (hM.fetch 39 rfl (by omega)) r₄ (by rw [hr₄, update_of_ne (Ne.symm hyt), ht₃])
    obtain ⟨r₆, hrun₆, hx₆, hj₆, hk₆, ht₆, hag₆⟩ := mul_run (M := M) (o := o + 40) (e := o + 46)
      (Ne.symm hjx) hkx.symm hxt hjk hjt hkt
      (hM.fetch 40 rfl (by omega))
      (hM.fetch 41 rfl (by omega))
      (hM.fetch 42 rfl (by omega))
      (hM.fetch 43 rfl (by omega))
      (hM.fetch 44 rfl (by omega))
      (hM.fetch 45 rfl (by omega)) r₅ ht₅
    obtain ⟨r₇, hrun₇, hi₇, hk₇, ht₇, hag₇⟩ := copy_run (M := M) (o := o + 46) (e := e)
      hik hit hkt (hM.fetch 46 rfl (by omega))
      (hM.fetch 47 rfl (by omega))
      (hM.fetch 48 rfl (by omega))
      (hM.fetch 49 rfl (by omega))
      (hM.fetch 50 rfl (by omega)) r₆ ht₆
    have hb₄ : r₄ j = r j := by simp [hr₄, hjy, hb₃]
    have hj₅' : r₅ j = r j := by rw [hj₅, hb₄]
    have hx₅' : r₅ x = r j := by
      rw [hx₅, hb₄, hr₄, update_of_ne hxy, hx₃, Nat.zero_add]
    have hk₅ : r₅ k = r k := by rw [hag₅.get (by simp; omega)]; simp [hr₄, hky, hk₃]
    have hi₅ : r₅ i = r i := by rw [hag₅.get (by simp; omega)]; simp [hr₄, hiy, ha₃]
    have hy₅ : r₅ y = 0 := by rw [hag₅.get (by simp; omega)]; simp [hr₄]
    have hj₆' : r₆ j = r j := by rw [hj₆, hj₅']
    have hk₆' : r₆ k = r k + r j * r j := by rw [hk₆, hk₅, hx₅', hj₅']
    have hi₆ : r₆ i = r i := by rw [hag₆.get (by simp; omega), hi₅]
    have hy₆ : r₆ y = 0 := by rw [hag₆.get (by simp; omega), hy₅]
    refine ⟨r₇, hrun₁.trans (hrun₂.trans (hrun₃.trans (hrun₄.trans (hrun₅.trans
      (hrun₆.trans hrun₇))))), ?_, ?_, ?_, ?_, ?_, ht₇, ?_⟩
    · rw [hk₇, hk₆', hi₆, Nat.pair, ite_eq_left hlt]; ring
    · rw [hi₇, hi₆]
    · rw [hag₇.get (by simp; omega), hj₆']
    · rw [hag₇.get (by simp; omega), hx₆]
    · rw [hag₇.get (by simp; omega), hy₆]
    · intro z hz
      have hz' := hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz'
      rw [hag₇.get (by simp; omega), hag₆.get (by simp; omega), hag₅.get (by simp; omega)]
      simp only [hr₄]
      rw [update_of_ne hz'.2.2.2.2.1, hag₁₃ z hz]

end Macro

end Minsky
