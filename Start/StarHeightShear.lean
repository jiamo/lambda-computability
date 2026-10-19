import Start.StarHeightNilpotentFour

/-!
# The shear reduction for `L(abac, k, p)` and `L(abca, k, p)`

Letters `a = 0`, `b = 1`, `c = 2` of `Fin 3`.  For a prefix `v` let `A = |v|_a`, `C = |v|_c` and
`S = scount [a, c] v`.  The *shear automaton* `Sh_p` has states `(Z/p)²`: `a` sends `(A, λ)` to
`(A + 1, λ)`, `c` sends it to `(A, λ + A)`, and `b` fixes it.  Its state after `v` is
`shState p v = (A mod p, S mod p)`, and `shcount p q u` counts the positions of `u` reading `b` in
state `q`.

Exact identities modulo `p` (proved by induction on the last letter):

  `scount abac ≡ S · scount ab − Σ_q q₁ q₂ · shcount q − C · Σ_b A_t² + Σ_b A_t² C_t`
                                                                   (`scount_abac_cast`)
  `scount abca ≡ (A C − S) · scount ab + Σ_q q₁ q₂ · shcount q − A · Σ_b A_t C_t`
                                                                   (`scount_abca_cast`)

The sums over the `b`'s of `A_t²`, `A_t² C_t`, `A_t C_t` are combinations of letter-in-state counts
of the translation automaton `(A, C)` on `(Z/p)²` (`vcount_height_one_prime`).  Hence
`height_one_abac_of_shear` and `height_one_abca_of_shear`: if every `shcount p q` is good modulo `p`,
then `L(abac, k, p)` and `L(abca, k, p)` have height at most one.  Every prime `p`, `2` included.

At `p = 2` the reduction is an equivalence (`shear_mod_two_iff_abac`), from

  `shcount q ≡ scount acab + (q₂ + 1) scount ab + q₁ scount acb + (q₁ + 1)(q₂ + 1) |u|_b  (mod 2)`
                                                                   (`shcount_two_cast`)

(`acab` is `abac` with `b` and `c` swapped).  So for `p = 2` the shear count is exactly as hard
as `L(abac, k, 2)`.
-/

namespace GeneralizedStarHeight

/-- The state of the shear automaton after `v`: `(|v|_a, scount [a, c] v)` modulo `p`. -/
def shState (p : ℕ) (v : List (Fin 3)) : ZMod p × ZMod p :=
  ((v.count 0 : ℕ), (scount [0, 2] v : ℕ))

/-- The number of positions of `u` reading `b = 1` in shear state `q`. -/
def shcount (p : ℕ) (q : ZMod p × ZMod p) (u : List (Fin 3)) : ℕ :=
  ((Finset.range u.length).filter (fun t => u[t]? = some 1 ∧ shState p (u.take t) = q)).card

section Snoc

universe u

variable {β : Type u} [DecidableEq β]

/-- Appending a letter to a word adds at most one position to a position count. -/
lemma posCount_snoc (P : List β → Prop) [DecidablePred P] (y x : β) (u : List β) :
    ((Finset.range (u ++ [x]).length).filter
        (fun t => (u ++ [x])[t]? = some y ∧ P ((u ++ [x]).take t))).card =
      ((Finset.range u.length).filter (fun t => u[t]? = some y ∧ P (u.take t))).card +
        if x = y ∧ P u then 1 else 0 := by
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have hcongr : (Finset.range u.length).filter
      (fun t => (u ++ [x])[t]? = some y ∧ P ((u ++ [x]).take t)) =
      (Finset.range u.length).filter (fun t => u[t]? = some y ∧ P (u.take t)) := by
    apply Finset.filter_congr
    intro t ht
    rw [Finset.mem_range] at ht
    rw [List.getElem?_append_left ht, List.take_append_of_le_length ht.le]
  have hlast : ((u ++ [x])[u.length]? = some y ∧ P ((u ++ [x]).take u.length)) ↔
      (x = y ∧ P u) := by
    simp
  rw [hcongr]
  by_cases h : x = y ∧ P u
  · rw [if_pos (hlast.mpr h), if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg (fun h' => h (hlast.mp h')), if_neg h, add_zero]

/-- `scount (w ++ [y]) (u ++ [x]) = scount (w ++ [y]) u + [x = y] scount w u`. -/
lemma scount_snoc (y x : β) : ∀ (u w : List β),
    scount (w ++ [y]) (u ++ [x]) = scount (w ++ [y]) u + if x = y then scount w u else 0
  | [], [] => by simp [scount_cons_cons]
  | [], _ :: w => by
      simp only [List.nil_append, List.cons_append, scount_cons_cons, scount_cons_nil]
      cases w <;> simp
  | z :: u, [] => by
      have ih := scount_snoc y x u []
      simp only [List.nil_append, List.cons_append, scount_cons_cons, scount_nil_left] at ih ⊢
      rw [ih]
      split_ifs <;> ring
  | z :: u, y' :: w => by
      have ih1 := scount_snoc y x u (y' :: w)
      have ih2 := scount_snoc y x u w
      simp only [List.cons_append, scount_cons_cons] at ih1 ih2 ⊢
      rw [ih1, ih2]
      split_ifs <;> ring

end Snoc

section Identity

variable (p : ℕ) [NeZero p]

/-- The translation automaton `(A, C)` on `(Z/p)²`. -/
def acStep (z : Fin 3) : ZMod p × ZMod p :=
  ((if z = 0 then 1 else 0), (if z = 2 then 1 else 0))

omit [NeZero p] in
lemma acStep_sum (u : List (Fin 3)) :
    (u.map (acStep p)).sum = ((u.count 0 : ZMod p), (u.count 2 : ZMod p)) :=
  sum_map_pair_indicator p 0 2 u

omit [NeZero p] in
lemma shcount_snoc (q : ZMod p × ZMod p) (u : List (Fin 3)) (x : Fin 3) :
    shcount p q (u ++ [x]) = shcount p q u + if x = 1 ∧ shState p u = q then 1 else 0 :=
  posCount_snoc (fun v => shState p v = q) 1 x u

omit [NeZero p] in
lemma vcount_snoc (q : ZMod p × ZMod p) (u : List (Fin 3)) (x : Fin 3) :
    vcount (acStep p) q 1 (u ++ [x]) =
      vcount (acStep p) q 1 u + if x = 1 ∧ (u.map (acStep p)).sum = q then 1 else 0 := by
  classical
  unfold vcount
  convert posCount_snoc (fun v => (v.map (acStep p)).sum = q) 1 x u

/-- Summing a weight against a position count that grew by one position in state `s`. -/
lemma sum_mul_snoc (f : ZMod p × ZMod p → ZMod p) (c c' : ZMod p × ZMod p → ℕ)
    (s : ZMod p × ZMod p) (b : Prop) [Decidable b]
    (h : ∀ q, c' q = c q + if b ∧ s = q then 1 else 0) :
    ∑ q, f q * (c' q : ZMod p) = ∑ q, f q * (c q : ZMod p) + if b then f s else 0 := by
  simp only [h, Nat.cast_add, mul_add, Finset.sum_add_distrib]
  congr 1
  by_cases hb : b
  · simp only [hb, true_and, if_true, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
  · simp [hb]

/-- `Σ_q q₁ q₂ · shcount q`: the sum of `A_t S_t` over the positions reading `b`. -/
def shSum (u : List (Fin 3)) : ZMod p := ∑ q : ZMod p × ZMod p, q.1 * q.2 * (shcount p q u : ZMod p)

/-- `Σ_b A_t^i C_t^j`, as a combination of letter-in-state counts of `(A, C)`. -/
noncomputable def acSum (i j : ℕ) (u : List (Fin 3)) : ZMod p :=
  ∑ q : ZMod p × ZMod p, q.1 ^ i * q.2 ^ j * (vcount (acStep p) q 1 u : ZMod p)

lemma shSum_snoc (u : List (Fin 3)) (x : Fin 3) :
    shSum p (u ++ [x]) = shSum p u +
      if x = 1 then (u.count 0 : ZMod p) * (scount [0, 2] u : ZMod p) else 0 :=
  sum_mul_snoc p (fun q => q.1 * q.2) _ _ (shState p u) (x = 1) (fun q => shcount_snoc p q u x)

lemma acSum_snoc (i j : ℕ) (u : List (Fin 3)) (x : Fin 3) :
    acSum p i j (u ++ [x]) = acSum p i j u +
      if x = 1 then (u.count 0 : ZMod p) ^ i * (u.count 2 : ZMod p) ^ j else 0 := by
  have := sum_mul_snoc p (fun q => q.1 ^ i * q.2 ^ j) _ _ ((u.map (acStep p)).sum) (x = 1)
    (fun q => vcount_snoc p q u x)
  rw [acStep_sum] at this
  exact this

omit [NeZero p] in
lemma count_snoc (z x : Fin 3) (u : List (Fin 3)) :
    ((u ++ [x]).count z : ZMod p) = (u.count z : ZMod p) + if x = z then 1 else 0 := by
  rw [List.count_append]
  push_cast
  congr 1
  by_cases h : x = z
  · subst h; simp
  · simp [h]

omit [NeZero p] in
lemma scount_snoc_cast (w : List (Fin 3)) (y x : Fin 3) (u : List (Fin 3)) :
    (scount (w ++ [y]) (u ++ [x]) : ZMod p) =
      (scount (w ++ [y]) u : ZMod p) + if x = y then (scount w u : ZMod p) else 0 := by
  rw [scount_snoc]
  push_cast
  split_ifs <;> simp

/-- `scount aba ≡ A · scount ab − Σ_b A_t²`. -/
lemma scount_aba_cast (u : List (Fin 3)) :
    (scount [0, 1, 0] u : ZMod p) =
      (u.count 0 : ZMod p) * (scount [0, 1] u : ZMod p) - acSum p 2 0 u := by
  induction u using List.reverseRecOn with
  | nil => simp [acSum, vcount]
  | append_singleton u x ih =>
      have e1 := scount_snoc_cast p [0, 1] 0 x u
      have e2 := scount_snoc_cast p [0] 1 x u
      have e3 := count_snoc p 0 x u
      have e4 := acSum_snoc p 2 0 u x
      simp only [List.cons_append, List.nil_append] at e1 e2
      rw [scount_singleton] at e2
      rw [e1, e2, e3, e4]
      fin_cases x <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
        linear_combination ih

/-- **The shear identity for `abac`.** -/
theorem scount_abac_cast (u : List (Fin 3)) :
    (scount [0, 1, 0, 2] u : ZMod p) =
      (scount [0, 2] u : ZMod p) * (scount [0, 1] u : ZMod p) - shSum p u -
        (u.count 2 : ZMod p) * acSum p 2 0 u + acSum p 2 1 u := by
  induction u using List.reverseRecOn with
  | nil => simp [acSum, shSum, vcount, shcount]
  | append_singleton u x ih =>
      have e0 := scount_snoc_cast p [0, 1, 0] 2 x u
      have e1 := scount_snoc_cast p [0] 2 x u
      have e2 := scount_snoc_cast p [0] 1 x u
      have e3 := count_snoc p 2 x u
      have e4 := acSum_snoc p 2 0 u x
      have e5 := acSum_snoc p 2 1 u x
      have e6 := shSum_snoc p u x
      have haba := scount_aba_cast p u
      simp only [List.cons_append, List.nil_append] at e0 e1 e2
      rw [scount_singleton] at e1 e2
      rw [e0, e1, e2, e3, e4, e5, e6]
      fin_cases x <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
        first | linear_combination ih | linear_combination ih + haba

/-- `scount abc ≡ C · scount ab − Σ_b A_t C_t`. -/
lemma scount_abc_cast (u : List (Fin 3)) :
    (scount [0, 1, 2] u : ZMod p) =
      (u.count 2 : ZMod p) * (scount [0, 1] u : ZMod p) - acSum p 1 1 u := by
  induction u using List.reverseRecOn with
  | nil => simp [acSum, vcount]
  | append_singleton u x ih =>
      have e1 := scount_snoc_cast p [0, 1] 2 x u
      have e2 := scount_snoc_cast p [0] 1 x u
      have e3 := count_snoc p 2 x u
      have e4 := acSum_snoc p 1 1 u x
      simp only [List.cons_append, List.nil_append] at e1 e2
      rw [scount_singleton] at e2
      rw [e1, e2, e3, e4]
      fin_cases x <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
        linear_combination ih

/-- **The shear identity for `abca`.** -/
theorem scount_abca_cast (u : List (Fin 3)) :
    (scount [0, 1, 2, 0] u : ZMod p) =
      ((u.count 0 : ZMod p) * (u.count 2 : ZMod p) - (scount [0, 2] u : ZMod p)) *
          (scount [0, 1] u : ZMod p) + shSum p u - (u.count 0 : ZMod p) * acSum p 1 1 u := by
  induction u using List.reverseRecOn with
  | nil => simp [acSum, shSum, vcount, shcount]
  | append_singleton u x ih =>
      have e0 := scount_snoc_cast p [0, 1, 2] 0 x u
      have e1 := scount_snoc_cast p [0] 2 x u
      have e2 := scount_snoc_cast p [0] 1 x u
      have e3 := count_snoc p 2 x u
      have e3' := count_snoc p 0 x u
      have e4 := acSum_snoc p 1 1 u x
      have e6 := shSum_snoc p u x
      have habc := scount_abc_cast p u
      simp only [List.cons_append, List.nil_append] at e0 e1 e2
      rw [scount_singleton] at e1 e2
      rw [e0, e1, e2, e3, e3', e4, e6]
      fin_cases x <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
        first | linear_combination ih | linear_combination ih + habc

end Identity

section Reduction

variable (p : ℕ) [Fact p.Prime]

/-- The counts that determine `scount abac` and `scount abca` modulo `p`. -/
noncomputable def shearFamily :
    Fin 4 ⊕ (ZMod p × ZMod p) ⊕ (ZMod p × ZMod p) → List (Fin 3) → ℕ
  | Sum.inl i => ![fun u => u.count 0, fun u => u.count 2, scount [0, 2], scount [0, 1]] i
  | Sum.inr (Sum.inl q) => vcount (acStep p) q 1
  | Sum.inr (Sum.inr q) => shcount p q

lemma shearFamily_goodMod
    (hsh : ∀ (q : ZMod p × ZMod p) (k : ℕ), k < p → HasHeightAtMost {u | shcount p q u % p = k} 1)
    (i : Fin 4 ⊕ (ZMod p × ZMod p) ⊕ (ZMod p × ZMod p)) : GoodMod p (shearFamily p i) := by
  rcases i with i | q | q
  · fin_cases i
    · exact (goodCount_count 0).goodMod p
    · exact (goodCount_count 2).goodMod p
    · exact (goodCount_scount_le_three _ (by simp)).goodMod p
    · exact (goodCount_scount_le_three _ (by simp)).goodMod p
  · exact (goodCount_vcount_prime (p := p) (acStep p) q 1).goodMod p
  · exact fun k hk => hsh q k hk

/-- Equal residues of the family give equal residues of every quantity in the identities. -/
lemma shearFamily_det {u w : List (Fin 3)}
    (h : ∀ i, (shearFamily p i u : ZMod p) = shearFamily p i w) :
    (u.count 0 : ZMod p) = w.count 0 ∧ (u.count 2 : ZMod p) = w.count 2 ∧
      (scount [0, 2] u : ZMod p) = scount [0, 2] w ∧ (scount [0, 1] u : ZMod p) = scount [0, 1] w ∧
      shSum p u = shSum p w ∧ ∀ i j, acSum p i j u = acSum p i j w := by
  refine ⟨h (Sum.inl 0), h (Sum.inl 1), h (Sum.inl 2), h (Sum.inl 3), ?_, fun i j => ?_⟩
  · exact Finset.sum_congr rfl fun q _ => by
      have := h (Sum.inr (Sum.inr q))
      simp only [shearFamily] at this
      rw [this]
  · exact Finset.sum_congr rfl fun q _ => by
      have := h (Sum.inr (Sum.inl q))
      simp only [shearFamily] at this
      rw [this]

/-- **The shear reduction for `abac`.** If every shear count is good modulo `p`, then every
residue class of `scount abac` modulo `p` has height at most one. -/
theorem height_one_abac_of_shear
    (hsh : ∀ (q : ZMod p × ZMod p) (k : ℕ), k < p → HasHeightAtMost {u | shcount p q u % p = k} 1)
    {k : ℕ} (hk : k < p) : HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 0, 2] u % p = k} 1 := by
  refine goodMod_of_det (Fact.out : p.Prime).pos (shearFamily p) (shearFamily_goodMod p hsh) ?_ k hk
  intro u w h
  obtain ⟨-, h2, hS, hAB, hX, hY⟩ := shearFamily_det p h
  rw [scount_abac_cast, scount_abac_cast, h2, hS, hAB, hX, hY, hY]

/-- **The shear reduction for `abca`.** -/
theorem height_one_abca_of_shear
    (hsh : ∀ (q : ZMod p × ZMod p) (k : ℕ), k < p → HasHeightAtMost {u | shcount p q u % p = k} 1)
    {k : ℕ} (hk : k < p) : HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 2, 0] u % p = k} 1 := by
  refine goodMod_of_det (Fact.out : p.Prime).pos (shearFamily p) (shearFamily_goodMod p hsh) ?_ k hk
  intro u w h
  obtain ⟨h0, h2, hS, hAB, hX, hY⟩ := shearFamily_det p h
  rw [scount_abca_cast, scount_abca_cast, h0, h2, hS, hAB, hX, hY]

end Reduction

/-! ### At `p = 2` the shear count and `scount acab` are good together -/

section ModTwo

universe v

/-- Injective letter maps preserve scattered subword counts. -/
lemma scount_map_inj {β γ : Type v} [DecidableEq β] [DecidableEq γ] {ψ : β → γ}
    (hψ : Function.Injective ψ) : ∀ (u w : List β), scount (w.map ψ) (u.map ψ) = scount w u
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => by simp
  | x :: u, y :: w => by
      have h1 := scount_map_inj hψ u (y :: w)
      have h2 := scount_map_inj hψ u w
      simp only [List.map_cons] at h1 ⊢
      rw [scount_cons_cons, scount_cons_cons, h1, h2]
      simp only [hψ.eq_iff]

/-- Inverse letter maps preserve goodness modulo `n`. -/
lemma GoodMod.comp_map {β γ : Type v} [Finite β] {n : ℕ} {g : List γ → ℕ} (hg : GoodMod n g)
    (ψ : β → γ) : GoodMod n (fun u => g (u.map ψ)) := by
  intro r hr
  have heq : {u : List β | g (u.map ψ) % n = r} =
      invAlph (fun a => some (ψ a)) {w | g w % n = r} := by
    ext u
    have hfm : (u.filterMap fun a => some (ψ a)) = u.map ψ := by
      induction u with
      | nil => rfl
      | cons b u ih => simp [ih]
    show _ ↔ g (u.filterMap fun a => some (ψ a)) % n = r
    rw [hfm]
    rfl
  rw [heq]
  exact (hg r hr).invAlph _

/-- `scount aca ≡ A · S + S (mod 2)`. -/
lemma scount_aca_cast_two (u : List (Fin 3)) :
    (scount [0, 2, 0] u : ZMod 2) =
      (u.count 0 : ZMod 2) * (scount [0, 2] u : ZMod 2) + (scount [0, 2] u : ZMod 2) := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u x ih =>
      have e1 := scount_snoc_cast 2 [0, 2] 0 x u
      have e2 := scount_snoc_cast 2 [0] 2 x u
      have e3 := count_snoc 2 0 x u
      simp only [List.cons_append, List.nil_append] at e1 e2
      rw [scount_singleton] at e2
      have hsq : ∀ a : ZMod 2, a * a = a := by decide
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [e1, e2, e3]
      fin_cases x <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
        first | linear_combination ih |
          linear_combination ih - hsq (u.count 0 : ZMod 2) -
            (u.count 0 : ZMod 2) * h2

lemma indicator_zmod_two (a b : ZMod 2) (q : ZMod 2 × ZMod 2) :
    (if (a, b) = q then (1 : ZMod 2) else 0) = (a + q.1 + 1) * (b + q.2 + 1) := by
  obtain ⟨q1, q2⟩ := q
  revert a b q1 q2
  decide

/-- **The shear count modulo 2**:
`shcount q ≡ scount acab + (q₂ + 1) scount ab + q₁ scount acb + (q₁ + 1)(q₂ + 1) |u|_b`. -/
theorem shcount_two_cast (q : ZMod 2 × ZMod 2) (u : List (Fin 3)) :
    (shcount 2 q u : ZMod 2) = (scount [0, 2, 0, 1] u : ZMod 2) +
      (q.2 + 1) * (scount [0, 1] u : ZMod 2) + q.1 * (scount [0, 2, 1] u : ZMod 2) +
        (q.1 + 1) * (q.2 + 1) * (u.count 1 : ZMod 2) := by
  induction u using List.reverseRecOn with
  | nil => simp [shcount]
  | append_singleton u x ih =>
      have e0 := scount_snoc_cast 2 [0, 2, 0] 1 x u
      have e1 := scount_snoc_cast 2 [0] 1 x u
      have e2 := scount_snoc_cast 2 [0, 2] 1 x u
      have e3 := count_snoc 2 1 x u
      have e4 := shcount_snoc 2 q u x
      have haca := scount_aca_cast_two u
      have hind : (if shState 2 u = q then (1 : ZMod 2) else 0) =
          ((u.count 0 : ZMod 2) + q.1 + 1) * ((scount [0, 2] u : ZMod 2) + q.2 + 1) :=
        indicator_zmod_two _ _ q
      simp only [List.cons_append, List.nil_append] at e0 e1 e2
      rw [scount_singleton] at e1
      have e4' : (shcount 2 q (u ++ [x]) : ZMod 2) = (shcount 2 q u : ZMod 2) +
          if x = 1 then (if shState 2 u = q then 1 else 0) else 0 := by
        rw [e4]
        by_cases hx : x = 1 <;> by_cases hs : shState 2 u = q <;> simp [hx, hs]
      rw [e0, e1, e2, e3, e4']
      fin_cases x <;> simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
        first | linear_combination ih | linear_combination ih + hind - haca

/-- **At `p = 2` the reduction is an equivalence**: every shear count is good modulo 2 iff
`scount abac` is. -/
theorem shear_mod_two_iff_abac :
    (∀ (q : ZMod 2 × ZMod 2) (k : ℕ), k < 2 → HasHeightAtMost {u | shcount 2 q u % 2 = k} 1) ↔
      ∀ k, k < 2 → HasHeightAtMost {u : List (Fin 3) | scount [0, 1, 0, 2] u % 2 = k} 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hsh k hk
    exact height_one_abac_of_shear 2 hsh hk
  · intro habac q k hk
    let ψ : Fin 3 → Fin 3 := ![0, 2, 1]
    have hψ : Function.Injective ψ := by decide
    have hacab : GoodMod 2 (scount ([0, 2, 0, 1] : List (Fin 3))) := by
      have h := GoodMod.comp_map (fun r hr => habac r hr) ψ
      have heq : ∀ u : List (Fin 3), scount [0, 1, 0, 2] (u.map ψ) = scount [0, 2, 0, 1] u := by
        intro u
        have := scount_map_inj hψ u [0, 2, 0, 1]
        rwa [show ([0, 2, 0, 1] : List (Fin 3)).map ψ = [0, 1, 0, 2] by decide] at this
      intro r hr
      have := h r hr
      simp only [heq] at this
      exact this
    refine goodMod_of_det (by norm_num)
      ![scount ([0, 2, 0, 1] : List (Fin 3)), scount [0, 1], scount [0, 2, 1], fun u => u.count 1]
      ?_ ?_ k hk
    · intro i
      fin_cases i
      · exact hacab
      · exact (goodCount_scount_le_three _ (by simp)).goodMod 2
      · exact (goodCount_scount_le_three _ (by simp)).goodMod 2
      · exact (goodCount_count 1).goodMod 2
    · intro u w h
      have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2 h3
      rw [shcount_two_cast, shcount_two_cast, h0, h1, h2, h3]

end ModTwo

end GeneralizedStarHeight
