/-
**Kleene's second algebra `K₂`, part two: the combinator `s`, and the PCA structure.**

`Start/KleeneTwoBasic.lean` sets up Baire space `ℕ → ℕ` with the application of function
realizability and the canonical associate of a continuous operation.  What is missing for a
partial combinatory algebra is the combinator `s`, and it cannot be produced by the canonical
associate alone: the operation `(α, β) ↦ (the associate of γ ↦ (α|γ)|(β|γ))` has to be continuous
in `α` and in `β`, which forces the innermost associate to be built by an explicit *finite
approximation* rather than by a quantification over all extensions.

That approximation is the content of this module.  Given a finite initial segment `t` of `β` and
a finite initial segment `l` of `γ`:

* `Realizability.KleeneTwo.delA` — the value of `α | γ` at a point, as far as `l` determines it;
* `Realizability.KleeneTwo.epsA` — the value of `β | γ` at a point, as far as `t` and `l`
  determine it;
* `Realizability.KleeneTwo.compAux` — the resulting approximation to the value of
  `(α|γ) | (β|γ)`, obtained by feeding the approximate values of `β|γ` to the approximate values
  of `α|γ`;
* `Realizability.KleeneTwo.sOne` — the element `s · α`: on the query `⟨y, t⟩` it answers the
  approximation computed from `t`, as soon as `t` is long enough for every lookup it needs
  (`Realizability.KleeneTwo.guardB`);
* `Realizability.KleeneTwo.sEl` — the combinator `s`, the canonical associate of `sOne`, which
  is continuous by `Realizability.KleeneTwo.cont_sOne`.

The two halves of the correctness proof are `compAux_sound` (a positive answer is the true value)
and `compAux_complete` (for a long enough initial segment of `γ` the true value is answered);
together they give `Realizability.KleeneTwo.sOne_app_spec`, and hence

* `Realizability.KleeneTwo.instPCABaire` — **`K₂` is a partial combinatory algebra**.

Two features of `K₂` are recorded at the end: the application is genuinely partial
(`appK_zero_eq_none`), and it is continuous (`appK_continuous`) — a value of `α | β` depends only
on a finite initial segment of `β`, which is Kleene's continuity principle and the reason `K₂` is
the algebra of *function* realizability.
-/

import Start.KleeneTwoBasic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

namespace KleeneTwo

/-! ### Bounded search for the first positive answer -/

/-- `searchFrom f k fuel` looks at `f k, f (k+1), …` for at most `fuel` steps and returns
`f j - 1` for the first `j` at which `f j` is positive. -/
def searchFrom (f : ℕ → ℕ) (k : ℕ) : ℕ → Option ℕ
  | 0 => none
  | fuel + 1 => if f k = 0 then searchFrom f (k + 1) fuel else some (f k - 1)

theorem searchFrom_sound {f : ℕ → ℕ} : ∀ {fuel k v : ℕ}, searchFrom f k fuel = some v →
    ∃ j, k ≤ j ∧ j < k + fuel ∧ f j = v + 1 ∧ ∀ i, k ≤ i → i < j → f i = 0 := by
  intro fuel
  induction fuel with
  | zero => intro k v h; simp [searchFrom] at h
  | succ fuel ih =>
      intro k v h
      rw [searchFrom] at h
      split at h
      · rename_i hz
        obtain ⟨j, hj1, hj2, hj3, hj4⟩ := ih h
        refine ⟨j, by omega, by omega, hj3, fun i hi1 hi2 => ?_⟩
        rcases Nat.eq_or_lt_of_le hi1 with rfl | h'
        · exact hz
        · exact hj4 i (by omega) hi2
      · rename_i hz
        rw [Option.some_inj] at h
        exact ⟨k, le_rfl, by omega, by omega, fun i hi1 hi2 => by omega⟩

theorem searchFrom_complete {f : ℕ → ℕ} : ∀ {fuel k j v : ℕ}, k ≤ j → j < k + fuel →
    f j = v + 1 → (∀ i, k ≤ i → i < j → f i = 0) → searchFrom f k fuel = some v := by
  intro fuel
  induction fuel with
  | zero => intro k j v h1 h2 _ _; omega
  | succ fuel ih =>
      intro k j v h1 h2 h3 h4
      rw [searchFrom]
      by_cases hk : f k = 0
      · rw [if_pos hk]
        have hkj : k ≠ j := by rintro rfl; omega
        exact ih (by omega) (by omega) h3 fun i hi1 hi2 => h4 i (by omega) hi2
      · rw [if_neg hk]
        have hkj : k = j := by
          by_contra hne
          exact hk (h4 k le_rfl (by omega))
        subst hkj
        simp [h3]

theorem searchFrom_congr {f g : ℕ → ℕ} : ∀ {fuel k : ℕ},
    (∀ i, k ≤ i → i < k + fuel → f i = g i) → searchFrom f k fuel = searchFrom g k fuel := by
  intro fuel
  induction fuel with
  | zero => intro k _; rfl
  | succ fuel ih =>
      intro k h
      have hk : f k = g k := h k le_rfl (by omega)
      rw [searchFrom, searchFrom, hk]
      by_cases hz : g k = 0
      · rw [if_pos hz, if_pos hz]
        exact ih fun i hi1 hi2 => h i (by omega) (by omega)
      · rw [if_neg hz, if_neg hz]

/-! ### A maximum over a list -/

theorem le_foldr_max {p : ℕ} {L : List ℕ} (h : p ∈ L) : p ≤ L.foldr max 0 := by
  induction L with
  | nil => cases h
  | cons a L ih =>
      rcases List.mem_cons.1 h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (ih h') (le_max_right _ _)

/-! ### Approximating the value of an application from an initial segment -/

/-- The value of `α | γ` at `y`, as far as the initial segment `l` of `γ` determines it. -/
def delA (α : ℕ → ℕ) (l : List ℕ) (y : ℕ) : Option ℕ :=
  searchFrom (fun k => α (enc (y :: l.take k))) 0 (l.length + 1)

theorem delA_sound {α γ : ℕ → ℕ} {K y w : ℕ} (h : delA α (restr γ K) y = some w) :
    AppAt α γ y w := by
  obtain ⟨j, _, hj2, hj3, hj4⟩ := searchFrom_sound h
  have hjK : j ≤ K := by simp only [restr_length] at hj2; omega
  refine ⟨j, ?_, fun i hi => ?_⟩
  · rw [qv, ← restr_take γ hjK]
    exact hj3
  · rw [qv, ← restr_take γ (le_trans hi.le hjK)]
    exact hj4 i (Nat.zero_le _) hi

theorem delA_complete {α γ : ℕ → ℕ} {y w k K : ℕ} (hk : k ≤ K) (h1 : qv α γ y k = w + 1)
    (h0 : ∀ j < k, qv α γ y j = 0) : delA α (restr γ K) y = some w := by
  have hlen : (restr γ K).length = K := restr_length γ K
  refine searchFrom_complete (j := k) (Nat.zero_le _) ?_ ?_ ?_
  · rw [hlen]; omega
  · simpa [qv, restr_take γ hk] using h1
  · intro i _ hi
    simpa [qv, restr_take γ (le_trans hi.le hk)] using h0 i hi

theorem delA_modulus (l : List ℕ) (y : ℕ) (α : ℕ → ℕ) :
    ∃ N, ∀ α' : ℕ → ℕ, (∀ i < N, α' i = α i) → delA α' l y = delA α l y := by
  refine ⟨(((List.range (l.length + 1)).map fun k => enc (y :: l.take k)).foldr max 0) + 1,
    fun α' h => searchFrom_congr fun i _ hi => ?_⟩
  have hmem : enc (y :: l.take i) ∈ (List.range (l.length + 1)).map fun k => enc (y :: l.take k) :=
    List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
  exact h _ (by have := le_foldr_max hmem; omega)

/-! ### The points of `β` consulted by the approximation -/

/-- The finite set of queries into `β` that the approximation over the initial segment `l` of `γ`
can make. -/
def qpts (l : List ℕ) : List ℕ :=
  (List.range (l.length + 1)).flatMap fun j =>
    (List.range (l.length + 1)).map fun k => enc (j :: l.take k)

theorem mem_qpts {l : List ℕ} {j k : ℕ} (hj : j ≤ l.length) (hk : k ≤ l.length) :
    enc (j :: l.take k) ∈ qpts l := by
  simp only [qpts, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨j, by omega, k, by omega, rfl⟩

/-- The initial segment `t` of `β` is long enough for every query the approximation over `l`
can make. -/
def guardB (l t : List ℕ) : Bool := (qpts l).all fun p => decide (p < t.length)

theorem guardB_iff {l t : List ℕ} : guardB l t = true ↔ ∀ p ∈ qpts l, p < t.length := by
  simp [guardB]

theorem exists_guard (l : List ℕ) (β : ℕ → ℕ) : ∃ K, ∀ k, K ≤ k → guardB l (restr β k) = true := by
  refine ⟨(qpts l).foldr max 0 + 1, fun k hk => guardB_iff.2 fun p hp => ?_⟩
  have := le_foldr_max hp
  simp only [restr_length]
  omega

/-- The value of `β | γ` at `j`, as far as the initial segments `t` of `β` and `l` of `γ`
determine it. -/
def epsA (t l : List ℕ) (j : ℕ) : Option ℕ :=
  searchFrom (fun k => t.getD (enc (j :: l.take k)) 0) 0 (l.length + 1)

theorem epsA_eq_delA {β : ℕ → ℕ} {kt : ℕ} {l : List ℕ} {j : ℕ}
    (hg : guardB l (restr β kt) = true) (hj : j ≤ l.length) :
    epsA (restr β kt) l j = delA β l j := by
  refine searchFrom_congr fun i _ hi => ?_
  have hi' : i ≤ l.length := by omega
  have hlt : enc (j :: l.take i) < (restr β kt).length := guardB_iff.1 hg _ (mem_qpts hj hi')
  rw [List.getD_eq_getElem _ _ hlt, restr_getElem]

/-! ### The approximation to the composite -/

/-- The approximation to the value of `(α|γ) | (β|γ)` at `n`: feed the approximate values of
`β|γ` to the approximate values of `α|γ`, for at most `fuel` steps.  The answer `0` means "not
determined yet", the answer `v + 1` means "the value is `v`". -/
def compAux (α : ℕ → ℕ) (t l : List ℕ) (n : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, e =>
    match delA α l (enc (n :: e)) with
    | none => 0
    | some 0 => (epsA t l e.length).elim 0 fun c => compAux α t l n fuel (e ++ [c])
    | some (w + 1) => w + 1

theorem compAux_zero (α : ℕ → ℕ) (t l : List ℕ) (n : ℕ) (e : List ℕ) :
    compAux α t l n 0 e = 0 := rfl

theorem compAux_succ (α : ℕ → ℕ) (t l : List ℕ) (n fuel : ℕ) (e : List ℕ) :
    compAux α t l n (fuel + 1) e =
      match delA α l (enc (n :: e)) with
      | none => 0
      | some 0 => (epsA t l e.length).elim 0 fun c => compAux α t l n fuel (e ++ [c])
      | some (w + 1) => w + 1 := rfl

theorem compAux_modulus (t l : List ℕ) (n : ℕ) (α : ℕ → ℕ) (fuel : ℕ) :
    ∀ e : List ℕ, ∃ N, ∀ α' : ℕ → ℕ, (∀ i < N, α' i = α i) →
      compAux α' t l n fuel e = compAux α t l n fuel e := by
  induction fuel with
  | zero => intro e; exact ⟨0, fun _ _ => rfl⟩
  | succ fuel ih =>
      intro e
      obtain ⟨N0, hN0⟩ := delA_modulus l (enc (n :: e)) α
      cases hc : epsA t l e.length with
      | none =>
          refine ⟨N0, fun α' h => ?_⟩
          rw [compAux_succ, compAux_succ, hN0 α' h]
          cases hd : delA α l (enc (n :: e)) with
          | none => rfl
          | some w =>
              cases w with
              | zero => simp [hc]
              | succ w => rfl
      | some c =>
          obtain ⟨N1, hN1⟩ := ih (e ++ [c])
          refine ⟨max N0 N1, fun α' h => ?_⟩
          rw [compAux_succ, compAux_succ, hN0 α' fun i hi => h i (by omega)]
          cases hd : delA α l (enc (n :: e)) with
          | none => rfl
          | some w =>
              cases w with
              | zero =>
                  simp only [hc, Option.elim]
                  exact hN1 α' fun i hi => h i (by omega)
              | succ w => rfl

/-! ### The element `s · α` -/

/-- The approximate value, at the query point `y = ⟨n, l⟩`, of the associate of
`γ ↦ (α|γ) | (β|γ)`, computed from the initial segment `t` of `β`. -/
def approx (α : ℕ → ℕ) (t : List ℕ) (y : ℕ) : ℕ :=
  match dec y with
  | [] => 0
  | n :: l => compAux α t l n (l.length + 1) []

theorem approx_cons {α : ℕ → ℕ} {t : List ℕ} {y n : ℕ} {l : List ℕ} (hy : dec y = n :: l) :
    approx α t y = compAux α t l n (l.length + 1) [] := by
  unfold approx; rw [hy]

theorem approx_nil {α : ℕ → ℕ} {t : List ℕ} {y : ℕ} (hy : dec y = []) : approx α t y = 0 := by
  unfold approx; rw [hy]

/-- The element `s · α` of `K₂`: it answers a query `⟨y, t⟩` as soon as the initial segment `t`
of the argument is long enough for the approximation at `y`. -/
def sOne (α : ℕ → ℕ) (z : ℕ) : ℕ :=
  match dec z with
  | [] => 0
  | y :: t => cond (guardB (dec y).tail t) (approx α t y + 1) 0

theorem sOne_nil {α : ℕ → ℕ} {z : ℕ} (hz : dec z = []) : sOne α z = 0 := by
  unfold sOne; rw [hz]

theorem sOne_cons {α : ℕ → ℕ} {z y : ℕ} {t : List ℕ} (hz : dec z = y :: t) :
    sOne α z = cond (guardB (dec y).tail t) (approx α t y + 1) 0 := by
  unfold sOne; rw [hz]

theorem cont_sOne : Cont sOne := by
  intro α z
  cases hz : dec z with
  | nil => exact ⟨0, fun α' _ => by rw [sOne_nil hz, sOne_nil hz]⟩
  | cons y t =>
      cases hy : dec y with
      | nil =>
          refine ⟨0, fun α' _ => ?_⟩
          rw [sOne_cons hz, sOne_cons hz, approx_nil hy, approx_nil hy]
      | cons n l =>
          obtain ⟨N, hN⟩ := compAux_modulus t l n α (l.length + 1) []
          refine ⟨N, fun α' h => ?_⟩
          rw [sOne_cons hz, sOne_cons hz, approx_cons hy, approx_cons hy, hN α' h]

/-- The combinator `s` of `K₂`. -/
noncomputable def sEl : ℕ → ℕ := detAssoc sOne

theorem appK_sEl (α : ℕ → ℕ) : appK sEl α = Part.some (sOne α) := appK_detAssoc cont_sOne α

/-! ### `s · α · β` is always defined -/

theorem exists_appAt_sOne (α β : ℕ → ℕ) (y : ℕ) : ∃ v, AppAt (sOne α) β y v := by
  obtain ⟨K, hK⟩ := exists_guard (dec y).tail β
  have hpos : 0 < qv (sOne α) β y K := by
    have h1 : qv (sOne α) β y K = approx α (restr β K) y + 1 := by
      rw [qv, sOne_cons (dec_enc _), hK K le_rfl, cond_true]
    omega
  obtain ⟨k, hk, hmin⟩ := exists_least (P := fun k => 0 < qv (sOne α) β y k) ⟨K, hpos⟩
  exact ⟨qv (sOne α) β y k - 1, k, by omega, fun j hj => by have := hmin j hj; omega⟩

theorem sOne_dom (α β : ℕ → ℕ) : (appK (sOne α) β).Dom :=
  ⟨fun y => (exists_appAt_sOne α β y).choose, fun y => (exists_appAt_sOne α β y).choose_spec⟩

/-! ### Soundness and completeness of the approximation -/

section SApp

variable {α β γ δ ε : ℕ → ℕ}

/-- A positive answer of the approximation is the true value of `(α|γ) | (β|γ)`. -/
theorem compAux_sound (hδ : ∀ y, AppAt α γ y (δ y)) (hε : ∀ j, AppAt β γ j (ε j))
    {K kt : ℕ} (hg : guardB (restr γ K) (restr β kt) = true) (n : ℕ) :
    ∀ (fuel m v : ℕ), m + fuel ≤ K + 1 → (∀ m' < m, δ (enc (n :: restr ε m')) = 0) →
      compAux α (restr β kt) (restr γ K) n fuel (restr ε m) = v + 1 → AppAt δ ε n v := by
  intro fuel
  induction fuel with
  | zero => intro m v _ _ h; rw [compAux_zero] at h; omega
  | succ fuel ih =>
      intro m v hlen hzero h
      rw [compAux_succ] at h
      cases hd : delA α (restr γ K) (enc (n :: restr ε m)) with
      | none =>
          simp only [hd] at h
          exact absurd h (by omega)
      | some w =>
          have hw : δ (enc (n :: restr ε m)) = w := (hδ _).unique (delA_sound hd)
          cases w with
          | succ w =>
              simp only [hd] at h
              refine ⟨m, ?_, fun j hj => ?_⟩
              · rw [qv, hw]; omega
              · rw [qv]; exact hzero j hj
          | zero =>
              simp only [hd] at h
              have hmK : m ≤ K := by omega
              simp only [restr_length] at h
              cases hc : epsA (restr β kt) (restr γ K) m with
              | none =>
                  simp only [hc, Option.elim] at h
                  exact absurd h (by omega)
              | some c =>
                  simp only [hc, Option.elim] at h
                  have hce : c = ε m := by
                    rw [epsA_eq_delA hg (by simp only [restr_length]; omega)] at hc
                    exact (delA_sound hc).unique (hε m)
                  rw [hce, ← restr_succ] at h
                  refine ih (m + 1) v (by omega) ?_ h
                  intro m' hm'
                  rcases Nat.lt_or_ge m' m with h' | h'
                  · exact hzero m' h'
                  · have hm'' : m' = m := by omega
                    rw [hm'', hw]

/-- For a long enough initial segment of `γ` the approximation returns the true value. -/
theorem compAux_complete {K kt : ℕ} (n m0 v : ℕ)
    (hval : δ (enc (n :: restr ε m0)) = v + 1)
    (hzero : ∀ m < m0, δ (enc (n :: restr ε m)) = 0)
    (hdel : ∀ m ≤ m0, delA α (restr γ K) (enc (n :: restr ε m))
      = some (δ (enc (n :: restr ε m))))
    (heps : ∀ j < m0, epsA (restr β kt) (restr γ K) j = some (ε j)) :
    ∀ (fuel m : ℕ), m ≤ m0 → m0 < m + fuel →
      compAux α (restr β kt) (restr γ K) n fuel (restr ε m) = v + 1 := by
  intro fuel
  induction fuel with
  | zero => intro m h1 h2; omega
  | succ fuel ih =>
      intro m hle hlt
      rw [compAux_succ]
      simp only [hdel m hle]
      rcases Nat.eq_or_lt_of_le hle with heq | hlt'
      · rw [heq, hval]
      · simp only [hzero m hlt', restr_length, heps m hlt', Option.elim, ← restr_succ]
        exact ih (m + 1) (by omega) (by omega)

end SApp

/-- The value of `(s · α) · β` at a query point is the approximation computed from some initial
segment of `β` that is long enough for it. -/
theorem sOne_value {α β W : ℕ → ℕ} (hW : ∀ y, AppAt (sOne α) β y (W y)) (n : ℕ) (l : List ℕ) :
    ∃ kt, guardB l (restr β kt) = true ∧
      compAux α (restr β kt) l n (l.length + 1) [] = W (enc (n :: l)) := by
  obtain ⟨kt, hkt, _⟩ := hW (enc (n :: l))
  rw [qv, sOne_cons (dec_enc _), dec_enc] at hkt
  simp only [List.tail_cons] at hkt
  cases hgd : guardB l (restr β kt) with
  | true =>
      rw [hgd, cond_true] at hkt
      refine ⟨kt, hgd, ?_⟩
      rw [← approx_cons (dec_enc (n :: l))]
      omega
  | false =>
      rw [hgd, cond_false] at hkt
      exact absurd hkt (by omega)

/-- **The composite is computed**: if `W` is the value of `(s · α) · β`, then applying `W` to `γ`
returns `(α|γ) | (β|γ)`. -/
theorem sOne_app_spec {α β γ W δ ε g : ℕ → ℕ}
    (hW : ∀ y, AppAt (sOne α) β y (W y))
    (hδ : ∀ y, AppAt α γ y (δ y)) (hε : ∀ j, AppAt β γ j (ε j))
    (hcomp : ∀ n, AppAt δ ε n (g n)) : ∀ n, AppAt W γ n (g n) := by
  intro n
  -- soundness: any positive answer of `W` is the value of `δ | ε`
  have hsound : ∀ K' v, qv W γ n K' = v + 1 → v = g n := by
    intro K' v hv
    obtain ⟨kt, hgd, hWy⟩ := sOne_value hW n (restr γ K')
    rw [qv] at hv
    rw [hv, restr_length] at hWy
    have hzero : ∀ m' < 0, δ (enc (n :: restr ε m')) = 0 := by omega
    have := compAux_sound hδ hε hgd n (K' + 1) 0 v (by omega) hzero (by simpa using hWy)
    exact this.unique (hcomp n)
  -- the witness for the value of `δ | ε` at `n`
  obtain ⟨m0, hm0, hm0z⟩ := hcomp n
  rw [qv] at hm0
  simp only [qv] at hm0z
  -- the moduli of the values of `α | γ` and `β | γ` that the computation consults
  set kd : ℕ → ℕ := fun m => (hδ (enc (n :: restr ε m))).choose with hkd
  set ke : ℕ → ℕ := fun j => (hε j).choose with hke
  set K : ℕ := max (max ((Finset.range (m0 + 1)).sup kd) ((Finset.range (m0 + 1)).sup ke)) m0
    with hK
  have hkdK : ∀ m ≤ m0, kd m ≤ K := by
    intro m hm
    have h1 : kd m ≤ (Finset.range (m0 + 1)).sup kd :=
      Finset.le_sup (Finset.mem_range.2 (by omega))
    have h2 : (Finset.range (m0 + 1)).sup kd ≤ K := by
      rw [hK]; exact le_max_of_le_left (le_max_left _ _)
    omega
  have hkeK : ∀ j ≤ m0, ke j ≤ K := by
    intro j hj
    have h1 : ke j ≤ (Finset.range (m0 + 1)).sup ke :=
      Finset.le_sup (Finset.mem_range.2 (by omega))
    have h2 : (Finset.range (m0 + 1)).sup ke ≤ K := by
      rw [hK]; exact le_max_of_le_left (le_max_right _ _)
    omega
  have hm0K : m0 ≤ K := by rw [hK]; exact le_max_right _ _
  -- completeness: at the initial segment of length `K` the answer is positive
  have hpos : qv W γ n K = g n + 1 := by
    obtain ⟨kt, hgd, hWy⟩ := sOne_value hW n (restr γ K)
    have hdel : ∀ m ≤ m0, delA α (restr γ K) (enc (n :: restr ε m))
        = some (δ (enc (n :: restr ε m))) := by
      intro m hm
      obtain ⟨h1, h2⟩ := (hδ (enc (n :: restr ε m))).choose_spec
      exact delA_complete (hkdK m hm) h1 h2
    have heps : ∀ j < m0, epsA (restr β kt) (restr γ K) j = some (ε j) := by
      intro j hj
      rw [epsA_eq_delA hgd (by simp only [restr_length]; omega)]
      obtain ⟨h1, h2⟩ := (hε j).choose_spec
      exact delA_complete (hkeK j (by omega)) h1 h2
    have hcc := compAux_complete (α := α) (β := β) (γ := γ) (δ := δ) (ε := ε)
      (K := K) (kt := kt) n m0 (g n) hm0 hm0z hdel heps (K + 1) 0 (by omega) (by omega)
    rw [qv, ← hWy, restr_length]
    simpa using hcc
  -- take the least such initial segment
  obtain ⟨K', hK', hmin⟩ := exists_least (P := fun k => 0 < qv W γ n k) ⟨K, by omega⟩
  refine ⟨K', ?_, fun j hj => by have := hmin j hj; omega⟩
  have hv : qv W γ n K' = (qv W γ n K' - 1) + 1 := by omega
  have := hsound K' _ hv
  omega

/-! ### `K₂` is a partial combinatory algebra -/

/-- **Kleene's second algebra**: Baire space with the application of function realizability is a
partial combinatory algebra. -/
noncomputable scoped instance instPCABaire : PCA (ℕ → ℕ) where
  app := appK
  k := kEl
  s := sEl
  k_dom a := by
    show (appK kEl a).Dom
    rw [appK_kEl]
    trivial
  k_app a b := by
    show ((appK kEl a).bind fun f => appK f b) = Part.some a
    rw [appK_kEl, Part.bind_some]
    exact appK_constAssoc a b
  s_dom a b := by
    show (((appK sEl a).bind fun f => appK f b)).Dom
    rw [appK_sEl, Part.bind_some]
    exact sOne_dom a b
  s_app a b c := by
    intro g hg
    simp only [Part.mem_bind_iff] at hg
    obtain ⟨d, hd, e, he, hg⟩ := hg
    show g ∈ ((appK sEl a).bind fun f => appK f b).bind fun h => appK h c
    rw [appK_sEl, Part.bind_some]
    refine Part.mem_bind_iff.2 ⟨_, Part.get_mem (sOne_dom a b), ?_⟩
    exact mem_appK.2 (sOne_app_spec (mem_appK.1 (Part.get_mem (sOne_dom a b)))
      (mem_appK.1 hd) (mem_appK.1 he) (mem_appK.1 hg))

/-! ### The combinatory axioms of `K₂`, spelled out -/

/-- `k · a · b = a` in `K₂`. -/
theorem k2_k_app (a b : ℕ → ℕ) : ((appK kEl a).bind fun f => appK f b) = Part.some a :=
  PCA.k_app a b

/-- `s · a · b` is always defined in `K₂`. -/
theorem k2_s_dom (a b : ℕ → ℕ) : ((appK sEl a).bind fun f => appK f b).Dom :=
  PCA.s_dom a b

/-- `s · a · b · c ⊒ (a · c) (b · c)` in `K₂`. -/
theorem k2_s_app (a b c : ℕ → ℕ) :
    ((appK a c).bind fun u => (appK b c).bind fun v => appK u v)
      ≤ (((appK sEl a).bind fun f => appK f b).bind fun g => appK g c) :=
  PCA.s_app a b c

/-! ### Two features of `K₂` -/

/-- The application of `K₂` is genuinely partial: an element that never answers a query applies
to nothing. -/
theorem appK_zero_eq_none (β : ℕ → ℕ) : appK (fun _ => 0) β = Part.none := by
  rw [Part.eq_none_iff']
  rintro ⟨f, hf⟩
  obtain ⟨k, hk, _⟩ := hf 0
  rw [qv] at hk
  omega

/-- **Kleene's continuity principle for `K₂`**: each value of `α | β` is already determined by a
finite initial segment of `β`. -/
theorem appK_continuous {α β f : ℕ → ℕ} (hf : f ∈ appK α β) (n : ℕ) :
    ∃ N, ∀ β' f' : ℕ → ℕ, (∀ i < N, β' i = β i) → f' ∈ appK α β' → f' n = f n := by
  obtain ⟨N, hN⟩ := (mem_appK.1 hf n).exists_modulus
  exact ⟨N, fun β' f' hβ hf' => (mem_appK.1 hf' n).unique (hN β' hβ)⟩

/-- **No element of `K₂` decides whether its argument is the zero function.**  The test is not
continuous, and every operation of `K₂` is: this is the Brouwerian flavour of function
realizability. -/
theorem no_zero_test :
    ¬ ∃ α : ℕ → ℕ, ∀ β : ℕ → ℕ, ∃ f, f ∈ appK α β ∧ (f 0 = 1 ↔ ∀ n, β n = 0) := by
  rintro ⟨α, hα⟩
  obtain ⟨f, hf, hf1⟩ := hα (fun _ => 0)
  have hone : f 0 = 1 := hf1.2 fun _ => rfl
  obtain ⟨N, hN⟩ := appK_continuous hf 0
  obtain ⟨g, hg, hg1⟩ := hα (Function.update (fun _ => 0) N 1)
  have hagree : ∀ i < N, Function.update (fun _ : ℕ => 0) N 1 i = (fun _ : ℕ => 0) i := by
    intro i hi
    exact Function.update_of_ne (by omega) _ _
  have hg0 : g 0 = f 0 := hN _ g hagree hg
  have hzero := hg1.1 (by omega)
  have := hzero N
  rw [Function.update_self] at this
  omega

end KleeneTwo

end Realizability
