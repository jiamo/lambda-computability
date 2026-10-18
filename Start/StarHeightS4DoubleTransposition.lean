import Start.StarHeightS4ThreeLetters

/-!
# The double-transposition obstruction for one good automaton

Let `T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)` be onto, with a letter `x₀` whose value `a` is
a double transposition.  Let `δ` be a permutation automaton over three letters with base `q₀` in
which every letter acts as a single cycle through `q₀` or as the identity (`CycleLetters`; every
good automaton has this property, `cycleLetters_of_good`).

`dbl_obstruction`: for every `d ∈ V₄` (`d = 1` or `d` a double transposition) some word `w`
returns `δ` to `q₀` and has `T w = d`.  So a single good automaton, together with the good coset
automata of `S₄` (which determine `T w` modulo `V₄` at best), never determines `T w`
(`not_determined_single`).

The proof.  Let `R` be the set of values `T w` of the words that return to `q₀`; it is a subgroup
(`R` is closed under products, and `T u ^ 23 = (T u)⁻¹`).  Let `s = T w` and `q = δ*(q₀, w)`.
* If `x₀` fixes `q`, then with a word `v` leading back from `q` to `q₀`, both `w v` and `w x₀ v`
  return, so `s a s⁻¹ ∈ R`.
* Otherwise `q = x₀ᵏ q₀`, and `w x₀ʲ` returns for suitable `j`, so `s ∈ R` or `s a ∈ R`.
Since `T` is onto, this holds for every `s ∈ S₄` (`trichotomy`).  For a `4`-cycle `g` with
`g² = a` it gives `a ∈ R`; for a `4`-cycle `h` with `h² = d ≠ a` it then gives `d ∈ R`
(`mem_of_trichotomy`).  No aperiodicity beyond the cycle property is used.

The statement for finite families of good automata (`FamilyObstruction`) is open.
-/

namespace GeneralizedStarHeight

namespace S4Dbl

open S4Two S4Three

variable {n : ℕ}

/-! ### Automata whose letters are cycles through the base -/

/-- Every letter acts as a permutation that is a single cycle through `q₀`, or as the identity. -/
def CycleLetters (δ : Fin n → Fin 3 → Fin n) (q₀ : Fin n) : Prop :=
  ∀ x, Function.Bijective (fun q => δ q x) ∧
    ∀ q, δ q x = q ∨ ∃ k, (fun r => δ r x)^[k] q₀ = q

/-- The `k`-th power of a word. -/
def powW (u : List (Fin 3)) (k : ℕ) : List (Fin 3) := (List.replicate k u).flatten

/-- **Good automata**: permutation automata whose return automaton (`DFAReturn.retAut δ q₀`) has
an aperiodic transformation monoid: `f ^ (N + 1) = f ^ N` for every element `f`. -/
def Good (δ : Fin n → Fin 3 → Fin n) (q₀ : Fin n) : Prop :=
  (∀ x, Function.Bijective (fun q => δ q x)) ∧
    ∃ N, ∀ (u : List (Fin 3)) (s : Option (Fin n × Bool)),
      (powW u (N + 1)).foldl (DFAReturn.retAut δ q₀) s = (powW u N).foldl (DFAReturn.retAut δ q₀) s

lemma powW_single (x : Fin 3) (k : ℕ) : powW [x] k = List.replicate k x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [powW, List.replicate_succ, List.flatten_cons, ← powW, ih, List.singleton_append,
        ← List.replicate_succ]

lemma retAut_replicate (δ : Fin n → Fin 3 → Fin n) (q₀ : Fin n) (x : Fin 3) (q : Fin n) :
    ∀ k, (∀ j, 1 ≤ j → j ≤ k → (fun r => δ r x)^[j] q ≠ q₀) →
      (List.replicate k x).foldl (DFAReturn.retAut δ q₀) (some (q, false)) =
        some ((fun r => δ r x)^[k] q, false)
  | 0, _ => rfl
  | k + 1, h => by
      rw [List.replicate_succ', List.foldl_append,
        retAut_replicate δ q₀ x q k fun j hj hjk => h j hj (by omega)]
      have hne := h (k + 1) (by omega) le_rfl
      rw [Function.iterate_succ_apply'] at hne ⊢
      simp [DFAReturn.retAut, hne]

lemma iterate_card_eq_id (f : Fin n → Fin n) (hf : Function.Bijective f) :
    f^[Fintype.card (Equiv.Perm (Fin n))] = id := by
  have h := pow_card_eq_one (G := Equiv.Perm (Fin n)) (x := Equiv.ofBijective f hf)
  funext q
  have hq := congrArg (fun σ : Equiv.Perm (Fin n) => σ q) h
  simp only [Equiv.Perm.coe_pow, Equiv.Perm.one_apply] at hq
  exact hq

lemma card_perm_pos : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos

lemma pred_mul_add (M j : ℕ) (h : 0 < M) : (M - 1) * j + j = M * j := by
  cases M with
  | zero => omega
  | succ m => rw [Nat.add_sub_cancel, Nat.succ_mul]

/-- **Every good automaton has letters that are cycles through the base.** -/
theorem cycleLetters_of_good {δ : Fin n → Fin 3 → Fin n} {q₀ : Fin n} (h : Good δ q₀) :
    CycleLetters δ q₀ := by
  obtain ⟨hbij, N, hN⟩ := h
  intro x
  refine ⟨hbij x, fun q => ?_⟩
  set f := fun r => δ r x with hf
  set M := Fintype.card (Equiv.Perm (Fin n))
  have hM : f^[M] = id := iterate_card_eq_id f (hbij x)
  by_cases hvis : ∃ j, 1 ≤ j ∧ f^[j] q = q₀
  · obtain ⟨j, -, hj⟩ := hvis
    right
    refine ⟨(M - 1) * j, ?_⟩
    rw [← hj, ← Function.iterate_add_apply, pred_mul_add M j card_perm_pos, Function.iterate_mul,
      hM, Function.iterate_id]
    rfl
  · left
    simp only [not_exists, not_and] at hvis
    have h1 := hN [x] (some (q, false))
    rw [powW_single, powW_single,
      retAut_replicate δ q₀ x q (N + 1) fun j hj _ => hvis j hj,
      retAut_replicate δ q₀ x q N fun j hj _ => hvis j hj] at h1
    simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h1
    rw [Function.iterate_succ_apply'] at h1
    have hinj : Function.Injective f^[N] := (hbij x).1.iterate N
    have h2 : f^[N] (f q) = f^[N] q := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact h1
    exact hinj h2

/-! ### The values of the returning words -/

/-- The values of `T` on the words that return to `q₀`. -/
def retVals (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) (δ : Fin n → Fin 3 → Fin n)
    (q₀ : Fin n) : Set (Equiv.Perm (Fin 4)) :=
  {s | ∃ w, DFAReturn.runQ δ q₀ w = q₀ ∧ T (FreeMonoid.ofList w) = s}

variable (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) (δ : Fin n → Fin 3 → Fin n) (q₀ : Fin n)

lemma one_mem_retVals : (1 : Equiv.Perm (Fin 4)) ∈ retVals T δ q₀ :=
  ⟨[], rfl, map_one T⟩

lemma mul_mem_retVals {s t : Equiv.Perm (Fin 4)} (hs : s ∈ retVals T δ q₀)
    (ht : t ∈ retVals T δ q₀) : s * t ∈ retVals T δ q₀ := by
  obtain ⟨u, hu, rfl⟩ := hs
  obtain ⟨v, hv, rfl⟩ := ht
  exact ⟨u ++ v, by rw [DFAReturn.runQ_append, hu, hv], by
    rw [FreeMonoid.ofList_append, map_mul]⟩

lemma runQ_powW {u : List (Fin 3)} (hu : DFAReturn.runQ δ q₀ u = q₀) :
    ∀ k, DFAReturn.runQ δ q₀ (powW u k) = q₀
  | 0 => rfl
  | k + 1 => by
      rw [powW, List.replicate_succ', List.flatten_append, ← powW, DFAReturn.runQ_append,
        runQ_powW hu k, List.flatten_singleton, hu]

lemma T_powW (u : List (Fin 3)) :
    ∀ k, T (FreeMonoid.ofList (powW u k)) = T (FreeMonoid.ofList u) ^ k
  | 0 => by simp [powW]
  | k + 1 => by
      rw [powW, List.replicate_succ', List.flatten_append, ← powW, FreeMonoid.ofList_append,
        map_mul, T_powW u k, List.flatten_singleton, pow_succ]

lemma inv_mem_retVals {s : Equiv.Perm (Fin 4)} (hs : s ∈ retVals T δ q₀) :
    s⁻¹ ∈ retVals T δ q₀ := by
  obtain ⟨u, hu, rfl⟩ := hs
  refine ⟨powW u 23, runQ_powW δ q₀ hu 23, ?_⟩
  rw [T_powW]
  have h24 : T (FreeMonoid.ofList u) ^ 24 = 1 := by
    have := pow_card_eq_one (x := T (FreeMonoid.ofList u))
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  exact h24

/-! ### Words leading back to the base -/

/-- A word that undoes `w`: its letters reversed, each repeated `|Perm (Fin n)| - 1` times. -/
def backW (w : List (Fin 3)) : List (Fin 3) :=
  (w.reverse.map fun x => List.replicate (Fintype.card (Equiv.Perm (Fin n)) - 1) x).flatten

lemma runQ_replicate (x : Fin 3) (q : Fin n) :
    ∀ k, DFAReturn.runQ δ q (List.replicate k x) = (fun r => δ r x)^[k] q
  | 0 => rfl
  | k + 1 => by
      rw [List.replicate_succ', DFAReturn.runQ_append, runQ_replicate x q k,
        Function.iterate_succ_apply']
      rfl

lemma runQ_backW (hbij : ∀ x, Function.Bijective (fun q => δ q x)) :
    ∀ (w : List (Fin 3)) (q : Fin n), DFAReturn.runQ δ (DFAReturn.runQ δ q w) (backW (n := n) w) = q
  | [], _ => rfl
  | x :: w, q => by
      have hrev : backW (n := n) (x :: w) =
          backW (n := n) w ++ List.replicate (Fintype.card (Equiv.Perm (Fin n)) - 1) x := by
        simp [backW]
      rw [hrev, DFAReturn.runQ_append, show DFAReturn.runQ δ q (x :: w) =
        DFAReturn.runQ δ (δ q x) w from rfl, runQ_backW hbij w, runQ_replicate]
      have hM := iterate_card_eq_id (fun r => δ r x) (hbij x)
      have hpos := card_perm_pos (n := n)
      have : (fun r => δ r x)^[Fintype.card (Equiv.Perm (Fin n)) - 1] (δ q x) =
          (fun r => δ r x)^[Fintype.card (Equiv.Perm (Fin n))] q := by
        conv_rhs => rw [show Fintype.card (Equiv.Perm (Fin n)) =
          (Fintype.card (Equiv.Perm (Fin n)) - 1) + 1 by omega]
        rw [Function.iterate_succ_apply]
      rw [this, hM]
      rfl

/-! ### The trichotomy -/

/-- **The trichotomy.**  If the letter `x₀` has value `a` with `a * a = 1`, then for every word `w`
with value `s`: `s ∈ R`, or `s * a ∈ R`, or `s * a * s⁻¹ ∈ R`, where `R` is the set of values of
the returning words. -/
theorem trichotomy (hδ : CycleLetters δ q₀) (x₀ : Fin 3)
    (ha : T (FreeMonoid.of x₀) * T (FreeMonoid.of x₀) = 1) (w : List (Fin 3)) :
    T (FreeMonoid.ofList w) ∈ retVals T δ q₀ ∨
      T (FreeMonoid.ofList w) * T (FreeMonoid.of x₀) ∈ retVals T δ q₀ ∨
      T (FreeMonoid.ofList w) * T (FreeMonoid.of x₀) * (T (FreeMonoid.ofList w))⁻¹ ∈
        retVals T δ q₀ := by
  have hbij : ∀ x, Function.Bijective (fun q => δ q x) := fun x => (hδ x).1
  set a := T (FreeMonoid.of x₀)
  set s := T (FreeMonoid.ofList w)
  set q := DFAReturn.runQ δ q₀ w
  rcases (hδ x₀).2 q with hfix | ⟨k, hk⟩
  · right; right
    set v := backW (n := n) w
    have h1 : s * T (FreeMonoid.ofList v) ∈ retVals T δ q₀ :=
      ⟨w ++ v, by rw [DFAReturn.runQ_append, runQ_backW δ hbij], by
        rw [FreeMonoid.ofList_append, map_mul]⟩
    have h2 : s * a * T (FreeMonoid.ofList v) ∈ retVals T δ q₀ := by
      refine ⟨w ++ [x₀] ++ v, ?_, ?_⟩
      · rw [DFAReturn.runQ_append, DFAReturn.runQ_append_single, hfix]
        exact runQ_backW δ hbij w q₀
      · rw [FreeMonoid.ofList_append, FreeMonoid.ofList_append, map_mul, map_mul,
          FreeMonoid.ofList_singleton]
    have h3 := mul_mem_retVals T δ q₀ h2 (inv_mem_retVals T δ q₀ h1)
    rwa [show s * a * T (FreeMonoid.ofList v) * (s * T (FreeMonoid.ofList v))⁻¹ =
      s * a * s⁻¹ by group] at h3
  · set M := Fintype.card (Equiv.Perm (Fin n))
    have hM := iterate_card_eq_id (fun r => δ r x₀) (hbij x₀)
    have hret : DFAReturn.runQ δ q₀ (w ++ List.replicate ((M - 1) * k) x₀) = q₀ := by
      rw [DFAReturn.runQ_append, runQ_replicate]
      change (fun r => δ r x₀)^[(M - 1) * k] q = q₀
      rw [← hk, ← Function.iterate_add_apply, pred_mul_add M k card_perm_pos, Function.iterate_mul,
        hM, Function.iterate_id]
      rfl
    have hval : T (FreeMonoid.ofList (w ++ List.replicate ((M - 1) * k) x₀)) =
        s * a ^ ((M - 1) * k) := by
      rw [FreeMonoid.ofList_append, map_mul, ← powW_single, T_powW, FreeMonoid.ofList_singleton]
    have hmem : s * a ^ ((M - 1) * k) ∈ retVals T δ q₀ := ⟨_, hret, hval⟩
    have hpow : ∀ j, a ^ j = a ^ (j % 2) := by
      intro j
      conv_lhs => rw [← Nat.div_add_mod j 2, pow_add, pow_mul, sq, ha, one_pow, one_mul]
    rw [hpow] at hmem
    rcases Nat.mod_two_eq_zero_or_one ((M - 1) * k) with h | h
    · left
      rwa [h, pow_zero, mul_one] at hmem
    · right; left
      rwa [h, pow_one] at hmem

/-! ### The group-theoretic step in `S₄` -/

lemma dblT_of_mem {σ : Equiv.Perm (Fin 4)} {i : Fin 24} (hσ : ⇑σ = tab i) (h : σ ∈ dbl) :
    dblT i = true := by
  simp only [dblT, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have := congrArg (fun τ : Equiv.Perm (Fin 4) => τ x) h.1
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, hσ] at this
    exact this
  · have := h.2 x
    rwa [hσ] at this

lemma sq_root_tab : ∀ i : Fin 24, dblT i = true → ∃ j : Fin 24, ∀ x, tab j (tab j x) = tab i x := by
  decide +kernel

lemma sq_root_conj_tab : ∀ i k : Fin 24, dblT i = true → dblT k = true → i ≠ k →
    ∃ j : Fin 24, (∀ x, tab j (tab j x) = tab k x) ∧
      ∀ x, tab j (tab i (tab (tinv j) x)) = tab i (tab k x) := by
  decide +kernel

/-- Every double transposition is the square of a permutation. -/
lemma exists_sq_eq {a : Equiv.Perm (Fin 4)} (ha : a ∈ dbl) :
    ∃ g : Equiv.Perm (Fin 4), g * g = a := by
  obtain ⟨i, hi⟩ := perm_tab a
  obtain ⟨j, hj⟩ := sq_root_tab i (dblT_of_mem hi ha)
  exact ⟨permOf j, Equiv.ext fun x => by
    rw [Equiv.Perm.mul_apply, coe_permOf, hj, hi]⟩

/-- For distinct double transpositions `a`, `d`: some `h` has `h² = d` and `h a h⁻¹ = a d`. -/
lemma exists_sq_conj {a d : Equiv.Perm (Fin 4)} (ha : a ∈ dbl) (hd : d ∈ dbl) (had : a ≠ d) :
    ∃ h : Equiv.Perm (Fin 4), h * h = d ∧ h * a * h⁻¹ = a * d := by
  obtain ⟨i, hi⟩ := perm_tab a
  obtain ⟨k, hk⟩ := perm_tab d
  have hik : i ≠ k := by
    rintro rfl
    exact had (DFunLike.coe_injective (hi.trans hk.symm))
  obtain ⟨j, hj1, hj2⟩ := sq_root_conj_tab i k (dblT_of_mem hi ha) (dblT_of_mem hk hd) hik
  refine ⟨permOf j, Equiv.ext fun x => ?_, Equiv.ext fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, coe_permOf, hj1, hk]
  · simp only [Equiv.Perm.mul_apply, coe_permOf, hi, hk]
    exact hj2 x

/-- **The step in `S₄`.**  A subgroup `R` such that every `s` satisfies `s ∈ R`, `s * a ∈ R` or
`s * a * s⁻¹ ∈ R`, for a double transposition `a`, contains every double transposition. -/
theorem mem_of_trichotomy (R : Set (Equiv.Perm (Fin 4)))
    (hmul : ∀ s t, s ∈ R → t ∈ R → s * t ∈ R) {a : Equiv.Perm (Fin 4)} (ha : a ∈ dbl)
    (htri : ∀ s, s ∈ R ∨ s * a ∈ R ∨ s * a * s⁻¹ ∈ R) {d : Equiv.Perm (Fin 4)} (hd : d ∈ dbl) :
    d ∈ R := by
  have haa : a * a = 1 := ha.1
  have haR : a ∈ R := by
    obtain ⟨g, hg⟩ := exists_sq_eq ha
    have hga : g * a * g⁻¹ = a := by rw [← hg]; group
    rcases htri g with h | h | h
    · rw [← hg]; exact hmul _ _ h h
    · have := hmul _ _ h h
      rwa [show g * a * (g * a) = a by
        calc g * a * (g * a) = a * a * a := by rw [← hg]; group
          _ = a := by rw [haa, one_mul]] at this
    · rwa [hga] at h
  by_cases had : a = d
  · exact had ▸ haR
  obtain ⟨h, hh, hconj⟩ := exists_sq_conj ha hd had
  rcases htri h with h1 | h1 | h1
  · rw [← hh]; exact hmul _ _ h1 h1
  · have hR : h ∈ R := by
      have := hmul _ _ h1 haR
      rwa [mul_assoc, haa, mul_one] at this
    rw [← hh]; exact hmul _ _ hR hR
  · rw [hconj] at h1
    have := hmul _ _ haR h1
    rwa [← mul_assoc, haa, one_mul] at this

/-! ### The obstruction -/

/-- **The double-transposition obstruction for one good automaton.**  If `T` is onto and some
letter is a double transposition, then for every automaton whose letters are cycles through the
base, and every `d ∈ V₄`, some word returns to the base and has value `d`. -/
theorem dbl_obstruction (hsurj : ∀ σ, ∃ w : List (Fin 3), T (FreeMonoid.ofList w) = σ)
    (x₀ : Fin 3) (ha : T (FreeMonoid.of x₀) ∈ dbl) (hδ : CycleLetters δ q₀)
    {d : Equiv.Perm (Fin 4)} (hd : d = 1 ∨ d ∈ dbl) :
    ∃ w : List (Fin 3), DFAReturn.runQ δ q₀ w = q₀ ∧ T (FreeMonoid.ofList w) = d := by
  rcases hd with rfl | hd
  · exact one_mem_retVals T δ q₀
  refine mem_of_trichotomy (retVals T δ q₀) (fun s t => mul_mem_retVals T δ q₀) ha
    (fun s => ?_) hd
  obtain ⟨w, rfl⟩ := hsurj s
  exact trichotomy T δ q₀ hδ x₀ ha.1 w

/-- **One good automaton does not determine `T`**: two words with different values reach the
same state. -/
theorem not_determined_single (hsurj : ∀ σ, ∃ w : List (Fin 3), T (FreeMonoid.ofList w) = σ)
    (x₀ : Fin 3) (ha : T (FreeMonoid.of x₀) ∈ dbl) (hδ : Good δ q₀) :
    ∃ u v : List (Fin 3), T (FreeMonoid.ofList u) ≠ T (FreeMonoid.ofList v) ∧
      DFAReturn.runQ δ q₀ u = DFAReturn.runQ δ q₀ v := by
  obtain ⟨w, hw, hT⟩ := dbl_obstruction T δ q₀ hsurj x₀ ha (cycleLetters_of_good hδ) (Or.inr ha)
  refine ⟨w, [], ?_, by rw [hw]; rfl⟩
  rw [hT, show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one]
  intro h
  have := ha.2 0
  rw [h] at this
  exact this rfl

/-! ### The smallest class -/

/-- The smallest class: `(2 3)`, `(1 2)`, `(0 1)(2 3)`. -/
def Tsmall : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  FreeMonoid.lift ![Equiv.swap 2 3, Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 2 3]

/-- Words with every value, as tables (checked below). -/
def wordsSmall : List (List (Fin 3)) :=
  [[], [0], [1], [0, 1], [1, 0], [0, 1, 0], [2], [2, 0], [2, 1], [2, 0, 1], [2, 1, 0], [2, 0, 1, 0],
    [1, 2], [1, 2, 0], [1, 2, 1], [1, 2, 0, 1], [1, 2, 1, 0], [1, 2, 0, 1, 0], [0, 1, 2],
    [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 0, 1], [0, 1, 2, 1, 0], [0, 1, 2, 0, 1, 0]]

/-- The table of the value of a word under `Tsmall`. -/
def tsTab (w : List (Fin 3)) (i : Fin 4) : Fin 4 :=
  w.foldr (fun x f => fun j => ![Equiv.swap 2 3, Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 2 3] x (f j)) id i

lemma Tsmall_tab (w : List (Fin 3)) : ⇑(Tsmall (FreeMonoid.ofList w)) = tsTab w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      funext i
      rw [show FreeMonoid.ofList (x :: w) = FreeMonoid.of x * FreeMonoid.ofList w from rfl,
        map_mul, Equiv.Perm.mul_apply, ih]
      simp [Tsmall, tsTab, FreeMonoid.lift_eval_of]

lemma wordsSmall_cover : ∀ i : Fin 24, ∃ w ∈ wordsSmall, ∀ x, tsTab w x = tab i x := by
  decide +kernel

lemma Tsmall_surj (σ : Equiv.Perm (Fin 4)) :
    ∃ w : List (Fin 3), Tsmall (FreeMonoid.ofList w) = σ := by
  obtain ⟨i, hi⟩ := perm_tab σ
  obtain ⟨w, -, hw⟩ := wordsSmall_cover i
  exact ⟨w, DFunLike.coe_injective (by rw [Tsmall_tab, hi]; exact funext hw)⟩

lemma Tsmall_dbl : Tsmall (FreeMonoid.of 2) ∈ dbl := by
  refine ⟨?_, ?_⟩
  · rw [Tsmall, FreeMonoid.lift_eval_of]
    decide
  · rw [Tsmall, FreeMonoid.lift_eval_of]
    decide

/-- **The smallest class.**  Every good automaton over three letters has two words with distinct
values under `Tsmall` that lead to the same state. -/
theorem not_determined_small (δ : Fin n → Fin 3 → Fin n) (q₀ : Fin n) (hδ : Good δ q₀) :
    ∃ u v : List (Fin 3), Tsmall (FreeMonoid.ofList u) ≠ Tsmall (FreeMonoid.ofList v) ∧
      DFAReturn.runQ δ q₀ u = DFAReturn.runQ δ q₀ v :=
  not_determined_single Tsmall δ q₀ Tsmall_surj 2 Tsmall_dbl hδ

/-! ### The open statement for families -/

/-- **The open statement**: every finite family of good automata has two words with distinct
values under `T` that lead every automaton of the family to the same state.  Proved above for
families of one automaton (`not_determined_single`); open for two or more. -/
def FamilyObstruction (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) : Prop :=
  ∀ (m : ℕ) (ns : Fin m → ℕ) (δs : ∀ i, Fin (ns i) → Fin 3 → Fin (ns i)) (q₀s : ∀ i, Fin (ns i)),
    (∀ i, Good (δs i) (q₀s i)) →
      ∃ u v : List (Fin 3), T (FreeMonoid.ofList u) ≠ T (FreeMonoid.ofList v) ∧
        ∀ i, DFAReturn.runQ (δs i) (q₀s i) u = DFAReturn.runQ (δs i) (q₀s i) v

end S4Dbl

end GeneralizedStarHeight
