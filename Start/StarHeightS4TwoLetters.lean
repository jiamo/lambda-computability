import Start.StarHeightS4Classes
import Start.StarHeightAperiodic

/-!
# Every language over two letters recognized by `S₄` has generalized star height at most one

For a morphism `T : FreeMonoid (Fin 2) →* S₄` and an arbitrary `F ⊆ S₄`, the language
`{w | T w ∈ F}` has generalized star height at most one (`height_one_S4_two_letters`).

The proof follows `classify_pairs`.  If the two letters have a common fixed point, centralize a
double transposition, or are both even, they lie in a proper subgroup of `S₄`, which has order at
most `12`: `height_one_of_mem_proper`.  Otherwise the pair is conjugate, possibly after swapping
the two letters, to one of the five normal forms, and for each normal form three observers of
`T w` of height at most one determine `T w` (`height_one_of_three_observers`):

* `u ↦ u⁻¹ p` for a good base point `p`, the state of the four-point automaton
  `δ q x = (T x)⁻¹ q`.  Its first-return code and its avoiding paths are star-free, certified by
  an aperiodic transformation monoid of the return automaton (`good_base4`);
* for the first class, where only the base point `2` is good, the three-point automaton of the
  action on the three pairings of `Fin 4` (`obP`, `good_base3`), whose stabilizer is the dihedral
  group `D₄ = ⟨(1 3), (0 1)(2 3)⟩`;
* the sign, a commutative count (`sign_height`).

The three observers separate the elements of `S₄`: two distinct fixed points and the sign
determine a permutation of four points (`two_points_sign`), as do the point `2`, the pairing and
the sign (`sep_class0`).
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Two

open Equiv

/-! ### The automata of `T` -/

/-- The four-point automaton of `T`: `δ q x = (T x)⁻¹ q`. -/
def dT (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (q : Fin 4) (x : Fin 2) : Fin 4 :=
  (T (FreeMonoid.of x))⁻¹ q

lemma point_runQ (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (p : Fin 4) (w : List (Fin 2)) :
    (T (FreeMonoid.ofList w))⁻¹ p = DFAReturn.runQ (dT T) p w :=
  inv_smul_runQ T p w

/-- Which of the three pairings of `Fin 4` contains `{x, y}` (`0` on the diagonal). -/
def pidx : Fin 4 → Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 0, 2, 1], ![1, 2, 0, 0], ![2, 1, 0, 0]]

/-- The action of a permutation on the three pairings. -/
def pact (Y : Equiv.Perm (Fin 4)) (i : Fin 3) : Fin 3 := pidx (Y 0) (Y (![1, 2, 3] i))

lemma pact_tab : ∀ (i : Fin 24) (x y : Fin 4), x ≠ y →
    pidx (tab i x) (tab i y) = pidx (tab i 0) (tab i (![1, 2, 3] (pidx x y))) := by decide +kernel

lemma pact_spec (Y : Equiv.Perm (Fin 4)) (x y : Fin 4) (hxy : x ≠ y) :
    pidx (Y x) (Y y) = pact Y (pidx x y) := by
  obtain ⟨i, hi⟩ := perm_tab Y
  simp only [pact, hi]
  exact pact_tab i x y hxy

/-- The pairing observer: the pairing containing `{u⁻¹ 0, u⁻¹ 2}`. -/
def obP (u : Equiv.Perm (Fin 4)) : Fin 3 := pidx (u⁻¹ 0) (u⁻¹ 2)

/-- The three-point pairing automaton of `T`. -/
def dP (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (i : Fin 3) (x : Fin 2) : Fin 3 :=
  pact (T (FreeMonoid.of x))⁻¹ i

lemma obP_one : obP 1 = 1 := by decide

lemma obP_runQ (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (w : List (Fin 2)) :
    obP (T (FreeMonoid.ofList w)) = DFAReturn.runQ (dP T) 1 w := by
  have hstep : ∀ (g : Equiv.Perm (Fin 4)) (x : Fin 2),
      obP (g * T (FreeMonoid.of x)) = dP T (obP g) x := by
    intro g x
    have hne : (g⁻¹ 0 : Fin 4) ≠ g⁻¹ 2 := by
      intro h
      have := congrArg g h
      simp at this
    show pidx ((g * T (FreeMonoid.of x))⁻¹ 0) ((g * T (FreeMonoid.of x))⁻¹ 2) =
      pact (T (FreeMonoid.of x))⁻¹ (pidx (g⁻¹ 0) (g⁻¹ 2))
    rw [← pact_spec _ _ _ hne]
    rfl
  have h := obs_runQ T obP (dP T) hstep w
  rwa [obP_one] at h

/-! ### Star-free returns from an aperiodicity certificate -/

/-- The states of the return automaton on four points with base `p` (closed under the letters). -/
def st4 (p : Fin 4) : List (Option (Fin 4 × Bool)) :=
  [some (0, false), some (1, false), some (2, false), some (3, false), some (p, true), none]

/-- The states of the return automaton on three points with base `p`. -/
def st3 (p : Fin 3) : List (Option (Fin 3 × Bool)) :=
  [some (0, false), some (1, false), some (2, false), some (p, true), none]

lemma st4_step : ∀ p r : Fin 4, some (r, decide (r = p)) ∈ st4 p := by decide

lemma st3_step : ∀ p r : Fin 3, some (r, decide (r = p)) ∈ st3 p := by decide

lemma st4_start : ∀ p : Fin 4, some (p, false) ∈ st4 p := by decide

lemma st3_start : ∀ p : Fin 3, some (p, false) ∈ st3 p := by decide

lemma st4_closed (δ : Fin 4 → Fin 2 → Fin 4) (p : Fin 4) :
    ∀ s ∈ st4 p, ∀ x, DFAReturn.retAut δ p s x ∈ st4 p := by
  intro s hs x
  simp only [st4, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
  any_goals exact st4_step p _
  all_goals simp [DFAReturn.retAut, st4]

lemma st3_closed (δ : Fin 3 → Fin 2 → Fin 3) (p : Fin 3) :
    ∀ s ∈ st3 p, ∀ x, DFAReturn.retAut δ p s x ∈ st3 p := by
  intro s hs x
  simp only [st3, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl
  any_goals exact st3_step p _
  all_goals simp [DFAReturn.retAut, st3]

lemma letters_mem : ∀ x : Fin 2, x ∈ [(0 : Fin 2), 1] := by decide

/-- **A good base point of a four-point automaton**: if the transformation monoid of its return
automaton is aperiodic, every state language has height at most one. -/
lemma good_base4 (δ : Fin 4 → Fin 2 → Fin 4) (p : Fin 4) (N : ℕ)
    (hcert : Aperiodic.certOK (st4 p) [0, 1] (DFAReturn.retAut δ p)
      (Aperiodic.dfaCert (st4 p) [0, 1] (DFAReturn.retAut δ p) 200) N = true) (q : Fin 4) :
    HasHeightAtMost {w : List (Fin 2) | DFAReturn.runQ δ p w = q} 1 := by
  have hsf : ∀ P : Option (Fin 4 × Bool) → Prop,
      HasHeightAtMost {w : List (Fin 2) |
        P (w.foldl (DFAReturn.retAut δ p) (some (p, false)))} 0 :=
    fun P => Aperiodic.starFree_of_dfa_closed (st4 p) (some (p, false)) (st4_start p) [0, 1]
      letters_mem (DFAReturn.retAut δ p) (st4_closed δ p) _ N hcert P
  refine height_one_of_starFree_returns δ p q ?_ ?_
  · rw [DFAReturn.firstReturn_eq_retAut]
    exact hsf fun s => s = some (p, true)
  · rw [DFAReturn.avoidTo_eq_retAut]
    exact hsf fun s => s = some (q, false)

/-- **A good base point of a three-point automaton.** -/
lemma good_base3 (δ : Fin 3 → Fin 2 → Fin 3) (p : Fin 3) (N : ℕ)
    (hcert : Aperiodic.certOK (st3 p) [0, 1] (DFAReturn.retAut δ p)
      (Aperiodic.dfaCert (st3 p) [0, 1] (DFAReturn.retAut δ p) 200) N = true) (q : Fin 3) :
    HasHeightAtMost {w : List (Fin 2) | DFAReturn.runQ δ p w = q} 1 := by
  have hsf : ∀ P : Option (Fin 3 × Bool) → Prop,
      HasHeightAtMost {w : List (Fin 2) |
        P (w.foldl (DFAReturn.retAut δ p) (some (p, false)))} 0 :=
    fun P => Aperiodic.starFree_of_dfa_closed (st3 p) (some (p, false)) (st3_start p) [0, 1]
      letters_mem (DFAReturn.retAut δ p) (st3_closed δ p) _ N hcert P
  refine height_one_of_starFree_returns δ p q ?_ ?_
  · rw [DFAReturn.firstReturn_eq_retAut]
    exact hsf fun s => s = some (p, true)
  · rw [DFAReturn.avoidTo_eq_retAut]
    exact hsf fun s => s = some (q, false)

/-! ### The sign -/

/-- The sign is a commutative count. -/
lemma sign_height (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (s : ℤˣ) :
    HasHeightAtMost {w : List (Fin 2) | Equiv.Perm.sign (T (FreeMonoid.ofList w)) = s} 1 :=
  height_one_of_comm (fun x y => mul_comm x y)
    ((Equiv.Perm.sign : Equiv.Perm (Fin 4) →* ℤˣ).comp T) ({s} : Set ℤˣ)

/-! ### Separation -/

lemma fix_two_tab : ∀ (i : Fin 24) (p q : Fin 4), p ≠ q → tab i p = p → tab i q = q →
    (∀ x, tab i x = x) ∨
      ∃ r s : Fin 4, r ≠ s ∧ ∀ x, tab i x = if x = r then s else if x = s then r else x := by
  decide +kernel

/-- A permutation of four points that fixes two points and is even is the identity. -/
lemma two_points_sign (σ : Equiv.Perm (Fin 4)) (p q : Fin 4) (hpq : p ≠ q) (hp : σ p = p)
    (hq : σ q = q) (hs : Equiv.Perm.sign σ = 1) : σ = 1 := by
  obtain ⟨i, hi⟩ := perm_tab σ
  rw [hi] at hp hq
  rcases fix_two_tab i p q hpq hp hq with h | ⟨r, s, hrs, h⟩
  · exact Equiv.ext fun x => by rw [congrFun hi x, h x]; rfl
  · have hsw : σ = swap r s := Equiv.ext fun x => by rw [congrFun hi x, h x, swap_apply_def]
    rw [hsw, Equiv.Perm.sign_swap hrs] at hs
    exact absurd hs (by decide)

lemma sep_two_points {p q : Fin 4} (hpq : p ≠ q) (u v : Equiv.Perm (Fin 4))
    (hp : u⁻¹ p = v⁻¹ p) (hq : u⁻¹ q = v⁻¹ q)
    (hs : Equiv.Perm.sign u = Equiv.Perm.sign v) : u = v := by
  have h1 : (v * u⁻¹) p = p := by
    rw [Equiv.Perm.mul_apply, hp]
    simp
  have h2 : (v * u⁻¹) q = q := by
    rw [Equiv.Perm.mul_apply, hq]
    simp
  have h3 : Equiv.Perm.sign (v * u⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hs]
    simp
  have h4 : v * u⁻¹ = 1 := two_points_sign _ p q hpq h1 h2 h3
  exact (mul_inv_eq_one.mp h4).symm

lemma pidx_inj : ∀ y z x : Fin 4, y ≠ x → z ≠ x → pidx y x = pidx z x → y = z := by decide

lemma inv_ne (u : Equiv.Perm (Fin 4)) {x y : Fin 4} (hxy : x ≠ y) : u⁻¹ x ≠ u⁻¹ y :=
  fun h => hxy (u⁻¹.injective h)

/-- The point `2`, the pairing and the sign determine a permutation of four points. -/
lemma sep_class0 (u v : Equiv.Perm (Fin 4)) (h2 : u⁻¹ 2 = v⁻¹ 2) (hP : obP u = obP v)
    (hs : Equiv.Perm.sign u = Equiv.Perm.sign v) : u = v := by
  have h0 : u⁻¹ 0 = v⁻¹ 0 := by
    refine pidx_inj _ _ (u⁻¹ 2) (inv_ne u (by decide)) ?_ ?_
    · rw [h2]
      exact inv_ne v (by decide)
    · have hP' : pidx (u⁻¹ 0) (u⁻¹ 2) = pidx (v⁻¹ 0) (v⁻¹ 2) := hP
      rw [h2] at hP' ⊢
      exact hP'
  exact sep_two_points (by decide : (0 : Fin 4) ≠ 2) u v h0 h2 hs

/-! ### The five normal forms -/

/-- The four-point automaton of the first normal form, `a = (2 3)`, `b = (0 1 2)`. -/
def tbl0 (q : Fin 4) (x : Fin 2) : Fin 4 :=
  ⟨lk [[0, 2], [1, 0], [3, 1], [2, 3]] q x % 4, Nat.mod_lt _ (by decide)⟩

/-- The pairing automaton of the first normal form. -/
def ptbl0 (q : Fin 3) (x : Fin 2) : Fin 3 :=
  ⟨lk [[0, 1], [2, 2], [1, 0]] q x % 3, Nat.mod_lt _ (by decide)⟩

/-- The four-point automaton of the second normal form, `a = (2 3)`, `b = (0 1 2 3)`. -/
def tbl1 (q : Fin 4) (x : Fin 2) : Fin 4 :=
  ⟨lk [[0, 3], [1, 0], [3, 1], [2, 2]] q x % 4, Nat.mod_lt _ (by decide)⟩

/-- The four-point automaton of the third normal form, `a = (1 2 3)`, `b = (0 1 2 3)`. -/
def tbl2 (q : Fin 4) (x : Fin 2) : Fin 4 :=
  ⟨lk [[0, 3], [3, 0], [1, 1], [2, 2]] q x % 4, Nat.mod_lt _ (by decide)⟩

/-- The four-point automaton of the fourth normal form, `a = (1 2 3)`, `b = (0 1 3 2)`. -/
def tbl3 (q : Fin 4) (x : Fin 2) : Fin 4 :=
  ⟨lk [[0, 2], [3, 0], [1, 3], [2, 1]] q x % 4, Nat.mod_lt _ (by decide)⟩

/-- The four-point automaton of the fifth normal form, `a = (0 1 2 3)`, `b = (0 1 3 2)`. -/
def tbl4 (q : Fin 4) (x : Fin 2) : Fin 4 :=
  ⟨lk [[3, 2], [0, 0], [1, 3], [2, 1]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma cert0_2 : Aperiodic.certOK (st4 2) [0, 1] (DFAReturn.retAut tbl0 2)
    (Aperiodic.dfaCert (st4 2) [0, 1] (DFAReturn.retAut tbl0 2) 200) 4 = true := by decide +kernel

lemma cert0_P : Aperiodic.certOK (st3 1) [0, 1] (DFAReturn.retAut ptbl0 1)
    (Aperiodic.dfaCert (st3 1) [0, 1] (DFAReturn.retAut ptbl0 1) 200) 4 = true := by decide +kernel

lemma cert1_2 : Aperiodic.certOK (st4 2) [0, 1] (DFAReturn.retAut tbl1 2)
    (Aperiodic.dfaCert (st4 2) [0, 1] (DFAReturn.retAut tbl1 2) 200) 5 = true := by decide +kernel

lemma cert1_3 : Aperiodic.certOK (st4 3) [0, 1] (DFAReturn.retAut tbl1 3)
    (Aperiodic.dfaCert (st4 3) [0, 1] (DFAReturn.retAut tbl1 3) 200) 5 = true := by decide +kernel

lemma cert2_2 : Aperiodic.certOK (st4 2) [0, 1] (DFAReturn.retAut tbl2 2)
    (Aperiodic.dfaCert (st4 2) [0, 1] (DFAReturn.retAut tbl2 2) 200) 5 = true := by decide +kernel

lemma cert2_3 : Aperiodic.certOK (st4 3) [0, 1] (DFAReturn.retAut tbl2 3)
    (Aperiodic.dfaCert (st4 3) [0, 1] (DFAReturn.retAut tbl2 3) 200) 5 = true := by decide +kernel

lemma cert3_1 : Aperiodic.certOK (st4 1) [0, 1] (DFAReturn.retAut tbl3 1)
    (Aperiodic.dfaCert (st4 1) [0, 1] (DFAReturn.retAut tbl3 1) 200) 5 = true := by decide +kernel

lemma cert3_2 : Aperiodic.certOK (st4 2) [0, 1] (DFAReturn.retAut tbl3 2)
    (Aperiodic.dfaCert (st4 2) [0, 1] (DFAReturn.retAut tbl3 2) 200) 5 = true := by decide +kernel

lemma cert4_2 : Aperiodic.certOK (st4 2) [0, 1] (DFAReturn.retAut tbl4 2)
    (Aperiodic.dfaCert (st4 2) [0, 1] (DFAReturn.retAut tbl4 2) 200) 5 = true := by decide +kernel

lemma cert4_3 : Aperiodic.certOK (st4 3) [0, 1] (DFAReturn.retAut tbl4 3)
    (Aperiodic.dfaCert (st4 3) [0, 1] (DFAReturn.retAut tbl4 3) 200) 5 = true := by decide +kernel

/-! ### The classes -/

/-- The point language of a base point, as a language of the four-point automaton. -/
lemma point_language (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (p r : Fin 4) :
    ({w | (T (FreeMonoid.ofList w))⁻¹ p = r} : Language (Fin 2)) =
      {w | DFAReturn.runQ (dT T) p w = r} := by
  ext w
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, point_runQ]

/-- The pairing language, as a language of the three-point automaton. -/
lemma pairing_language (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4)) (r : Fin 3) :
    ({w | obP (T (FreeMonoid.ofList w)) = r} : Language (Fin 2)) =
      {w | DFAReturn.runQ (dP T) 1 w = r} := by
  ext w
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, obP_runQ]

/-- **The first normal form**, `a = (2 3)`, `b = (0 1 2)`: the base point `2`, the pairing
automaton of `D₄` and the sign. -/
theorem class0_height_one (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (h0 : T (FreeMonoid.of 0) = repA 0) (h1 : T (FreeMonoid.of 1) = repB 0)
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hd : dT T = tbl0 := by
    funext q x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp only [dT, h0]
      revert q
      decide
    · simp only [dT, h1]
      revert q
      decide
  have hp : dP T = ptbl0 := by
    funext i x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp only [dP, h0]
      revert i
      decide
    · simp only [dP, h1]
      revert i
      decide
  refine height_one_of_three_observers T (fun u => u⁻¹ (2 : Fin 4)) obP
    (fun u => Equiv.Perm.sign u) sep_class0 (fun r => ?_) (fun r => ?_) (sign_height T) F
  · rw [point_language, hd]
    exact good_base4 tbl0 2 4 cert0_2 r
  · rw [pairing_language, hp]
    exact good_base3 ptbl0 1 4 cert0_P r

/-- **The second normal form**, `a = (2 3)`, `b = (0 1 2 3)`: the base points `2` and `3` and the
sign. -/
theorem class1_height_one (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (h0 : T (FreeMonoid.of 0) = repA 1) (h1 : T (FreeMonoid.of 1) = repB 1)
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hd : dT T = tbl1 := by
    funext q x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp only [dT, h0]
      revert q
      decide
    · simp only [dT, h1]
      revert q
      decide
  refine height_one_of_three_observers T (fun u => u⁻¹ (2 : Fin 4)) (fun u => u⁻¹ (3 : Fin 4))
    (fun u => Equiv.Perm.sign u) (fun u v => sep_two_points (by decide) u v) (fun r => ?_)
    (fun r => ?_) (sign_height T) F
  · rw [point_language, hd]
    exact good_base4 tbl1 2 5 cert1_2 r
  · rw [point_language, hd]
    exact good_base4 tbl1 3 5 cert1_3 r

/-- **The third normal form**, `a = (1 2 3)`, `b = (0 1 2 3)`: the base points `2` and `3` and
the sign. -/
theorem class2_height_one (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (h0 : T (FreeMonoid.of 0) = repA 2) (h1 : T (FreeMonoid.of 1) = repB 2)
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hd : dT T = tbl2 := by
    funext q x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp only [dT, h0]
      revert q
      decide
    · simp only [dT, h1]
      revert q
      decide
  refine height_one_of_three_observers T (fun u => u⁻¹ (2 : Fin 4)) (fun u => u⁻¹ (3 : Fin 4))
    (fun u => Equiv.Perm.sign u) (fun u v => sep_two_points (by decide) u v) (fun r => ?_)
    (fun r => ?_) (sign_height T) F
  · rw [point_language, hd]
    exact good_base4 tbl2 2 5 cert2_2 r
  · rw [point_language, hd]
    exact good_base4 tbl2 3 5 cert2_3 r

/-- **The fourth normal form**, `a = (1 2 3)`, `b = (0 1 3 2)`: the base points `1` and `2` and
the sign. -/
theorem class3_height_one (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (h0 : T (FreeMonoid.of 0) = repA 3) (h1 : T (FreeMonoid.of 1) = repB 3)
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hd : dT T = tbl3 := by
    funext q x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp only [dT, h0]
      revert q
      decide
    · simp only [dT, h1]
      revert q
      decide
  refine height_one_of_three_observers T (fun u => u⁻¹ (1 : Fin 4)) (fun u => u⁻¹ (2 : Fin 4))
    (fun u => Equiv.Perm.sign u) (fun u v => sep_two_points (by decide) u v) (fun r => ?_)
    (fun r => ?_) (sign_height T) F
  · rw [point_language, hd]
    exact good_base4 tbl3 1 5 cert3_1 r
  · rw [point_language, hd]
    exact good_base4 tbl3 2 5 cert3_2 r

/-- **The fifth normal form**, `a = (0 1 2 3)`, `b = (0 1 3 2)`: the base points `2` and `3` and
the sign. -/
theorem class4_height_one (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (h0 : T (FreeMonoid.of 0) = repA 4) (h1 : T (FreeMonoid.of 1) = repB 4)
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hd : dT T = tbl4 := by
    funext q x
    have hx : x = 0 ∨ x = 1 := by revert x; decide
    rcases hx with rfl | rfl
    · simp only [dT, h0]
      revert q
      decide
    · simp only [dT, h1]
      revert q
      decide
  refine height_one_of_three_observers T (fun u => u⁻¹ (2 : Fin 4)) (fun u => u⁻¹ (3 : Fin 4))
    (fun u => Equiv.Perm.sign u) (fun u v => sep_two_points (by decide) u v) (fun r => ?_)
    (fun r => ?_) (sign_height T) F
  · rw [point_language, hd]
    exact good_base4 tbl4 2 5 cert4_2 r
  · rw [point_language, hd]
    exact good_base4 tbl4 3 5 cert4_3 r

/-- Every normal form. -/
theorem class_height_one (k : Fin 5) (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (h0 : T (FreeMonoid.of 0) = repA k) (h1 : T (FreeMonoid.of 1) = repB k)
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  fin_cases k
  · exact class0_height_one T h0 h1 F
  · exact class1_height_one T h0 h1 F
  · exact class2_height_one T h0 h1 F
  · exact class3_height_one T h0 h1 F
  · exact class4_height_one T h0 h1 F

/-! ### The theorem -/

/-- **Every language over two letters recognized by `S₄` has generalized star height at most
one.** -/
theorem height_one_S4_two_letters (T : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  rcases classify_pairs (T (FreeMonoid.of 0)) (T (FreeMonoid.of 1)) with
    ⟨p, hA, hB⟩ | ⟨m, hA, hB⟩ | ⟨hA, hB⟩ | ⟨c, k, hk⟩
  · refine height_one_of_mem_proper _ (stab_ne_top p) T (fun x => ?_) F
    fin_cases x
    · exact MulAction.mem_stabilizer_iff.mpr hA
    · exact MulAction.mem_stabilizer_iff.mpr hB
  · refine height_one_of_mem_proper _ (centralizer_ne_top m) T (fun x => ?_) F
    fin_cases x
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hA.symm
    · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hB.symm
  · refine height_one_of_mem_proper _ evenSub_ne_top T (fun x => ?_) F
    fin_cases x
    · exact hA
    · exact hB
  · rw [conj_language c T F]
    set S := (MulAut.conj c).toMonoidHom.comp T with hS
    have hS0 : S (FreeMonoid.of 0) = c * T (FreeMonoid.of 0) * c⁻¹ := rfl
    have hS1 : S (FreeMonoid.of 1) = c * T (FreeMonoid.of 1) * c⁻¹ := rfl
    rcases hk with ⟨hkA, hkB⟩ | ⟨hkA, hkB⟩
    · exact class_height_one k S (by rw [hS0, hkA, mul_inv_cancel_right])
        (by rw [hS1, hkB, mul_inv_cancel_right]) _
    · refine height_one_of_swap S _ ?_
      refine class_height_one k _ ?_ ?_ _
      · show S (FreeMonoid.of (Equiv.swap (0 : Fin 2) 1 0)) = repA k
        rw [show Equiv.swap (0 : Fin 2) 1 0 = 1 from by decide, hS1, hkB, mul_inv_cancel_right]
      · show S (FreeMonoid.of (Equiv.swap (0 : Fin 2) 1 1)) = repB k
        rw [show Equiv.swap (0 : Fin 2) 1 1 = 0 from by decide, hS0, hkA, mul_inv_cancel_right]

/-- **Every language over an alphabet whose letters take at most two values under `T`** has
generalized star height at most one. -/
theorem height_one_S4_two_values {α : Type} [Finite α]
    (T : FreeMonoid α →* Equiv.Perm (Fin 4)) (f : α → Fin 2)
    (T2 : FreeMonoid (Fin 2) →* Equiv.Perm (Fin 4))
    (hT : ∀ x, T (FreeMonoid.of x) = T2 (FreeMonoid.of (f x)))
    (F : Set (Equiv.Perm (Fin 4))) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hcomp : T = T2.comp (FreeMonoid.map f) := FreeMonoid.hom_eq fun x => by
    simpa using hT x
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language α) =
      comapL f {w | T2 (FreeMonoid.ofList w) ∈ F} := by
    ext w
    show T (FreeMonoid.ofList w) ∈ F ↔ T2 (FreeMonoid.ofList (w.map f)) ∈ F
    rw [hcomp]
    rfl
  rw [heq]
  exact HasHeightAtMost.comap f (height_one_S4_two_letters T2 F)

/-- **Every language over an arbitrary two-letter alphabet recognized by `S₄`** has generalized
star height at most one. -/
theorem height_one_S4_card_two {α : Type} [Fintype α] (hα : Fintype.card α = 2)
    (T : FreeMonoid α →* Equiv.Perm (Fin 4)) (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  let e := Fintype.equivFinOfCardEq hα
  exact height_one_S4_two_values T e (T.comp (FreeMonoid.map e.symm)) (fun x => by simp [e]) F

end S4Two

end GeneralizedStarHeight
