import Start.StarHeightIndexPrime

/-!
# Abelian normal subgroups with elementary abelian quotient, for every prime

* `vcount_height_one_prime`: for a prime `p`, every letter-in-state count of a translation
  automaton on a finite `ZMod p`-vector space has height at most one modulo every `n`.
* `height_one_of_abelian_normal_exponent_prime`: if `N` is an abelian normal subgroup of a finite
  group `G` such that `G ⧸ N` is abelian of exponent `p`, every language recognized by `G` has
  generalized star height at most one.
* `height_one_of_abelian_normal_exponent_two`: the case `p = 2` (PST's `Gcom ∗ (Z/2)ʳ`), where
  commutativity of the quotient is automatic.
* `height_one_of_abelian_normal_exponent_three_of_prime`: Bourne's case `p = 3` again.
* `G3025 = (Z₁₁ × Z₁₁) ⋊ (Z₅ × Z₅)` and `height_one_G3025`.

The reduction to one dimension is the character sum of `Start/StarHeightBourne.lean`.  With `D` the
dual of `V` and `|D| = p·c`,

  `Σ_{φ ∈ D} vcount (φ ∘ δ) (φ q) x w = c · |w|ₓ + (p - 1)·c · vcount δ q x w`

(`charSum_vcount`), and each `vcount (φ ∘ δ) (φ q) x w` is a `ZMod p` core count at the state
`φ q` (`vcount_zp_height`, from `zpcore`).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-! ### Characters of a `ZMod p`-vector space -/

section Characters

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

lemma finite_dual_prime [Finite V] : Finite (Module.Dual (ZMod p) V) :=
  Finite.of_injective (fun φ : Module.Dual (ZMod p) V => (φ : V → ZMod p)) DFunLike.coe_injective

/-- **Counting lemma.** For `v ≠ 0`, exactly a `p`-th of the characters vanish at `v`. -/
lemma card_dual_ker_prime [Fintype (Module.Dual (ZMod p) V)] (v : V) (hv : v ≠ 0) :
    p * (Finset.univ.filter (fun φ : Module.Dual (ZMod p) V => φ v = 0)).card =
      Fintype.card (Module.Dual (ZMod p) V) := by
  classical
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : Module.Dual (ZMod p) V, φ0 v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod p) v).mp h)
  set φ1 := (φ0 v)⁻¹ • φ0 with hφ1def
  have hφ1 : φ1 v = 1 := by
    rw [hφ1def, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ0]
  have hfib : ∀ t : ZMod p,
      (Finset.univ.filter (fun φ : Module.Dual (ZMod p) V => φ v = t)).card =
        (Finset.univ.filter (fun φ : Module.Dual (ZMod p) V => φ v = 0)).card := by
    intro t
    apply Finset.card_bij (fun φ _ => φ - t • φ1)
    · intro φ hφ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
      simp [hφ, hφ1]
    · intro a _ b _ h
      simpa using h
    · intro ψ hψ
      refine ⟨ψ + t • φ1, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hψ ⊢
      simp [hψ, hφ1]
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun φ : Module.Dual (ZMod p) V => φ v)
    (s := Finset.univ) (t := (Finset.univ : Finset (ZMod p))) (by simp)
  rw [Finset.card_univ] at hsum
  rw [hsum, Finset.sum_congr rfl (fun t _ => hfib t)]
  simp [Finset.sum_const, ZMod.card]

variable {α : Type u} [DecidableEq α]

open Classical in
/-- **The character identity.** -/
lemma charSum_vcount [Fintype (Module.Dual (ZMod p) V)] (δ : α → V) (q : V) (x : α) (c : ℕ)
    (hc0 : Fintype.card (Module.Dual (ZMod p) V) = p * c)
    (hc : ∀ v : V, v ≠ 0 →
      (Finset.univ.filter (fun φ : Module.Dual (ZMod p) V => φ v = 0)).card = c)
    (s : V) (w : List α) :
    ∑ φ : Module.Dual (ZMod p) V, vcountFrom (fun a => φ (δ a)) (φ q) x (φ s) w =
      c * w.count x + (p - 1) * c * vcountFrom δ q x s w := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  induction w generalizing s with
  | nil => simp [vcountFrom_nil]
  | cons b w ih =>
      simp only [vcountFrom_cons]
      rw [Finset.sum_add_distrib]
      have hadd : ∀ φ : Module.Dual (ZMod p) V, φ s + φ (δ b) = φ (s + δ b) :=
        fun φ => (map_add φ s (δ b)).symm
      simp_rw [hadd]
      rw [ih (s + δ b), List.count_cons]
      by_cases hb : b = x
      · subst hb
        simp only [true_and, beq_self_eq_true, ite_true]
        rw [← Finset.card_filter]
        have hf : (Finset.univ.filter fun φ : Module.Dual (ZMod p) V => φ s = φ q) =
            Finset.univ.filter fun φ : Module.Dual (ZMod p) V => φ (s - q) = 0 := by
          ext φ
          simp [sub_eq_zero]
        rw [hf]
        by_cases hs : s = q
        · subst hs
          simp only [sub_self, map_zero, Finset.filter_true, Finset.card_univ, hc0, ite_true]
          obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        · rw [hc _ (sub_ne_zero.mpr hs), ite_eq_right hs]
          ring
      · have hb' : ¬ (b == x) = true := by simpa using hb
        simp only [hb, false_and, ite_false, Finset.sum_const_zero, hb', Bool.false_eq_true,
          add_zero, zero_add]

end Characters

/-- The number of occurrences of a letter is a state count of the trivial automaton. -/
lemma vcountFrom_const_zero {α : Type u} [DecidableEq α] {V : Type} [AddMonoid V] (x : α) :
    ∀ (w : List α), vcountFrom (fun _ => (0 : V)) 0 x 0 w = w.count x
  | [] => by simp [vcountFrom_nil]
  | b :: w => by
      rw [vcountFrom_cons, add_zero, vcountFrom_const_zero x w, List.count_cons]
      by_cases hb : b = x
      · simp [hb, add_comm]
      · simp [hb]

/-- **Letter-in-state counts on `(ZMod p)ʳ`.** Every letter-in-state count of a translation
automaton on a finite `ZMod p`-vector space (`p` prime) has height at most one modulo every `n`. -/
theorem vcount_height_one_prime {α : Type u} [Finite α] [DecidableEq α] {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] [Finite V] (δ : α → V) (q : V) (x : α) (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcount : ∀ m r, r < m → HasHeightAtMost {w : List α | w.count x % m = r} 1 := by
    intro m r hr
    have := vcount_zp_height p (fun _ : α => (0 : ZMod p)) 0 x m r hr
    simpa only [vcount_eq_vcountFrom, vcountFrom_const_zero] using this
  by_cases hV : ∀ v : V, v = 0
  · have hall : ∀ (w : List α) (s : V), vcountFrom δ q x s w = w.count x := by
      intro w
      induction w with
      | nil => intro s; simp [vcountFrom_nil]
      | cons b w ih =>
          intro s
          rw [vcountFrom_cons, ih, List.count_cons, hV s, hV q]
          by_cases hb : b = x
          · simp [hb, add_comm]
          · simp [hb]
    have : {w : List α | vcount δ q x w % n = k} = {w : List α | w.count x % n = k} := by
      ext w
      show vcount δ q x w % n = k ↔ w.count x % n = k
      rw [vcount_eq_vcountFrom, hall]
    rw [this]
    exact hcount n k hk
  push Not at hV
  obtain ⟨v0, hv0⟩ := hV
  have : Finite (Module.Dual (ZMod p) V) := finite_dual_prime
  let : Fintype (Module.Dual (ZMod p) V) := Fintype.ofFinite _
  set c := (Finset.univ.filter (fun φ : Module.Dual (ZMod p) V => φ v0 = 0)).card with hcdef
  have hc0 : Fintype.card (Module.Dual (ZMod p) V) = p * c :=
    (card_dual_ker_prime (p := p) v0 hv0).symm
  have hc : ∀ v : V, v ≠ 0 →
      (Finset.univ.filter (fun φ : Module.Dual (ZMod p) V => φ v = 0)).card = c := by
    intro v hv
    have h1 := card_dual_ker_prime (p := p) v hv
    rw [hc0] at h1
    exact Nat.eq_of_mul_eq_mul_left (by omega) h1
  have hcpos : 0 < c := by
    have : 0 < Fintype.card (Module.Dual (ZMod p) V) := Fintype.card_pos
    rw [hc0] at this
    exact Nat.pos_of_mul_pos_left this
  have hn : 0 < n := by omega
  have hp1 : 0 < p - 1 := by omega
  have hM : 0 < (p - 1) * c * n := by positivity
  refine height_one_of_residues (ι := Option (Module.Dual (ZMod p) V))
    (fun i w => i.elim (w.count x) (fun φ => vcount (fun a => φ (δ a)) (φ q) x w)) hM ?_ _
    (fun r => (∑ φ : Module.Dual (ZMod p) V, (r (some φ) : ZMod ((p - 1) * c * n))) -
      (c : ZMod ((p - 1) * c * n)) * (r none : ZMod ((p - 1) * c * n)) =
        (((p - 1) * c * k : ℕ) : ZMod ((p - 1) * c * n)))
    ?_
  · intro i r hr
    cases i with
    | none => exact hcount _ r hr
    | some φ => exact vcount_zp_height p (fun a => φ (δ a)) (φ q) x _ r hr
  · intro w
    show vcount δ q x w % n = k ↔ _
    simp only [Option.elim, ZMod.natCast_mod]
    have hid := charSum_vcount δ q x c hc0 hc 0 w
    simp only [map_zero] at hid
    simp only [vcount_eq_vcountFrom]
    rw [← Nat.cast_sum, hid]
    have : ((c * w.count x + (p - 1) * c * vcountFrom δ q x 0 w : ℕ) : ZMod ((p - 1) * c * n)) -
        (c : ZMod ((p - 1) * c * n)) * (w.count x : ZMod ((p - 1) * c * n)) =
          (((p - 1) * c * vcountFrom δ q x 0 w : ℕ) : ZMod ((p - 1) * c * n)) := by
      push_cast; ring
    rw [this, ZMod.natCast_eq_natCast_iff', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
      Nat.mod_eq_of_lt hk]
    constructor
    · intro h; rw [h]
    · intro h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-! ### Assembly: groups in `AbGrp * (Z_p)ʳ` -/

section Assembly

open Classical

variable {Alphabet : Type u}

/-- **Abelian normal subgroups with elementary abelian quotient.** If `N` is an abelian normal
subgroup of a finite group `G` such that `G ⧸ N` is abelian of prime exponent `p`, every language
recognized by `G` has generalized star height at most one. -/
theorem height_one_of_abelian_normal_exponent_prime [Finite Alphabet] {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) {p : ℕ} [Fact p.Prime] (hexp : ∀ x : G, x ^ p ∈ N)
    (T : FreeMonoid Alphabet →* G) (F : Set G) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have := Fintype.ofFinite Alphabet
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hcardN : 0 < Nat.card N := Nat.card_pos
  have hQ : ∀ x y : G ⧸ N, x * y = y * x := by
    intro x y
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    have h1 : ((x * y * x⁻¹ * y⁻¹ : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr (hcomm x y)
    have h2 : ((x : G ⧸ N) * y) * ((y : G ⧸ N) * x)⁻¹ = 1 := by
      rw [← h1]; simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]; group
    exact mul_inv_eq_one.mp h2
  have hQp : ∀ q : G ⧸ N, q ^ p = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hexp x)
  let : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hQ }
  let : Module (ZMod p) (Additive (G ⧸ N)) := AddCommGroup.zmodModule (fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow, hQp]; rfl)
  let δ : Alphabet → Additive (G ⧸ N) := fun a => Additive.ofMul (psi N T (FreeMonoid.of a))
  have hcount : ∀ (w : List Alphabet) (pr : (G ⧸ N) × Alphabet),
      (tpairs N T 1 w).count pr = vcount δ (Additive.ofMul pr.1) pr.2 w := by
    intro w pr
    rw [vcount_eq_vcountFrom]
    exact tpairs_count_eq_vcountFrom N T pr.1 pr.2 w 1
  have hval : ∀ w : List Alphabet, T (FreeMonoid.ofList w) =
      (valN N T hab (fun pr => (tpairs N T 1 w).count pr % Nat.card N) : G) *
        rep N (psi N T (FreeMonoid.ofList w)) := by
    intro w
    have ht := telescope N T 1 w
    rw [rep_one, one_mul, one_mul, list_prod_cv N T hab, mul_inv_eq_iff_eq_mul] at ht
    exact ht
  let Idx := {z : (G ⧸ N) × ((G ⧸ N) × Alphabet → Fin (Nat.card N)) //
    (valN N T hab (fun pr => (z.2 pr : ℕ)) : G) * rep N z.1 ∈ F}
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) = ⨆ z : Idx,
      ({w | psi N T (FreeMonoid.ofList w) = z.1.1} ⊓
        ⨅ pr : (G ⧸ N) × Alphabet,
          {w | vcount δ (Additive.ofMul pr.1) pr.2 w % Nat.card N = z.1.2 pr}) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨(psi N T (FreeMonoid.ofList w), fun pr =>
        ⟨(tpairs N T 1 w).count pr % Nat.card N, Nat.mod_lt _ hcardN⟩), ?_⟩, rfl, ?_⟩
      · show _ ∈ F
        rw [← hval]; exact hw
      · refine HasHeightAtMost.mem_iInf_lang.mpr fun pr => ?_
        show _ = _
        simp only
        rw [hcount]
    · intro hw
      obtain ⟨z, hz1, hz2⟩ := Language.mem_iSup.mp hw
      have hz2' := HasHeightAtMost.mem_iInf_lang.mp hz2
      show T (FreeMonoid.ofList w) ∈ F
      rw [hval]
      have hres : (fun pr => (tpairs N T 1 w).count pr % Nat.card N) =
          fun pr => (z.1.2 pr : ℕ) := by
        funext pr
        rw [hcount]; exact hz2' pr
      have hz1' : psi N T (FreeMonoid.ofList w) = z.1.1 := hz1
      rw [hres, hz1']
      exact z.2
  rw [heq]
  refine HasHeightAtMost.iSup _ fun z => HasHeightAtMost.inter ?_ ?_
  · simpa using height_one_of_comm hQ (psi N T) {z.1.1}
  · exact HasHeightAtMost.iInf _ fun pr =>
      vcount_height_one_prime (p := p) δ (Additive.ofMul pr.1) pr.2 (Nat.card N) (z.1.2 pr) (z.1.2 pr).2

/-- **Bourne's case `p = 3`**, recovered from the prime case. -/
theorem height_one_of_abelian_normal_exponent_three_of_prime [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x : G, x ^ 3 ∈ N)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  height_one_of_abelian_normal_exponent_prime N hab hcomm hexp T F

/-- **The case `p = 2`** (PST's `Gcom ∗ (Z/2)ʳ`). A quotient of exponent `2` is automatically
abelian, so no commutator hypothesis is needed. -/
theorem height_one_of_abelian_normal_exponent_two [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hexp : ∀ x : G, x ^ 2 ∈ N) (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hsq : ∀ q : G ⧸ N, q * q = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_mul, ← pow_two]
    exact (QuotientGroup.eq_one_iff _).mpr (hexp x)
  have hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N := by
    intro x y
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [inv_eq_of_mul_eq_one_right (hsq (x : G ⧸ N)), inv_eq_of_mul_eq_one_right (hsq (y : G ⧸ N))]
    simpa only [mul_assoc] using hsq ((x : G ⧸ N) * y)
  exact height_one_of_abelian_normal_exponent_prime (p := 2) N hab hcomm hexp T F

end Assembly

/-! ### The group `(Z₁₁ × Z₁₁) ⋊ (Z₅ × Z₅)` of order `3025`

`(i, j) ∈ Z₅ × Z₅` acts on `Z₁₁ × Z₁₁` by `diag(3^i, 3^j)`.  The base `Z₁₁ × Z₁₁` is an abelian
normal subgroup with quotient `(Z₅)²`, elementary abelian of exponent `5`.  The group has no abelian
normal subgroup of prime index: such a subgroup `A` would contain the commutator subgroup
`Z₁₁ × Z₁₁` and have index `5`, so `A = Z₁₁² ⋊ C` with `C` a line of `(Z₅)²`; a nonzero `(i, j) ∈ C`
acts nontrivially on `Z₁₁²` (as `3` has order `5` mod `11`), so `A` is not abelian.  Hence
`height_one_of_abelian_prime_index` does not apply to it (this remark is not formalized). -/

/-- `(Z₁₁ × Z₁₁) ⋊ (Z₅ × Z₅)`. -/
@[ext] structure G3025 where
  /-- First `Z₁₁` coordinate. -/
  b₁ : ZMod 11
  /-- Second `Z₁₁` coordinate. -/
  b₂ : ZMod 11
  /-- First `Z₅` coordinate. -/
  e₁ : ZMod 5
  /-- Second `Z₅` coordinate. -/
  e₂ : ZMod 5
  deriving DecidableEq

namespace G3025

instance : Mul G3025 :=
  ⟨fun g h => ⟨g.b₁ + G55.tw g.e₁ * h.b₁, g.b₂ + G55.tw g.e₂ * h.b₂, g.e₁ + h.e₁, g.e₂ + h.e₂⟩⟩
instance : One G3025 := ⟨⟨0, 0, 0, 0⟩⟩
instance : Inv G3025 :=
  ⟨fun g => ⟨-(G55.tw (-g.e₁) * g.b₁), -(G55.tw (-g.e₂) * g.b₂), -g.e₁, -g.e₂⟩⟩

lemma mul_def (g h : G3025) :
    g * h = ⟨g.b₁ + G55.tw g.e₁ * h.b₁, g.b₂ + G55.tw g.e₂ * h.b₂, g.e₁ + h.e₁, g.e₂ + h.e₂⟩ := rfl

lemma one_def : (1 : G3025) = ⟨0, 0, 0, 0⟩ := rfl

instance : Group G3025 where
  mul_assoc f g h := by
    ext
    · simp only [mul_def, G55.tw_add]; ring
    · simp only [mul_def, G55.tw_add]; ring
    · simp only [mul_def]; ring
    · simp only [mul_def]; ring
  one_mul f := by ext <;> simp [mul_def, one_def, G55.tw_zero]
  mul_one f := by ext <;> simp [mul_def, one_def]
  inv_mul_cancel f := by
    ext
    · show -(G55.tw (-f.e₁) * f.b₁) + G55.tw (-f.e₁) * f.b₁ = 0
      ring
    · show -(G55.tw (-f.e₂) * f.b₂) + G55.tw (-f.e₂) * f.b₂ = 0
      ring
    · show -f.e₁ + f.e₁ = 0
      ring
    · show -f.e₂ + f.e₂ = 0
      ring

/-- `G3025 ≃ Z₁₁ × Z₁₁ × Z₅ × Z₅`. -/
def equivProd : G3025 ≃ ZMod 11 × ZMod 11 × ZMod 5 × ZMod 5 where
  toFun g := (g.b₁, g.b₂, g.e₁, g.e₂)
  invFun q := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩

instance : Fintype G3025 := Fintype.ofEquiv _ equivProd.symm

lemma card : Fintype.card G3025 = 3025 := by
  rw [Fintype.card_congr equivProd]
  simp [Fintype.card_prod, ZMod.card]

/-- `G3025` is not abelian. -/
lemma not_comm : ∃ g h : G3025, g * h ≠ h * g :=
  ⟨⟨1, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, by decide⟩

/-- The projection onto `Z₅ × Z₅`. -/
def proj : G3025 →* Multiplicative (ZMod 5 × ZMod 5) where
  toFun g := Multiplicative.ofAdd (g.e₁, g.e₂)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The normal subgroup `Z₁₁ × Z₁₁`. -/
def base : Subgroup G3025 := proj.ker

instance : base.Normal := MonoidHom.normal_ker _

lemma mem_base {g : G3025} : g ∈ base ↔ g.e₁ = 0 ∧ g.e₂ = 0 := by
  show Multiplicative.ofAdd (g.e₁, g.e₂) = 1 ↔ _
  rw [← ofAdd_zero, EmbeddingLike.apply_eq_iff_eq, Prod.mk_eq_zero]

lemma base_comm : ∀ x ∈ base, ∀ y ∈ base, x * y = y * x := by
  intro x hx y hy
  rw [mem_base] at hx hy
  ext
  · simp only [mul_def, hx, hy, G55.tw_zero, one_mul, add_comm]
  · simp only [mul_def, hx, hy, G55.tw_zero, one_mul, add_comm]
  · simp only [mul_def, hx, hy]
  · simp only [mul_def, hx, hy]

lemma comm_mem (x y : G3025) : x * y * x⁻¹ * y⁻¹ ∈ base := by
  show proj _ = 1
  simp only [map_mul, map_inv]
  rw [mul_right_comm (proj x), mul_inv_cancel, one_mul, mul_inv_cancel]

lemma pow_five_mem (x : G3025) : x ^ 5 ∈ base := by
  show proj _ = 1
  rw [map_pow]
  have h : ∀ e : ZMod 5 × ZMod 5, 5 • e = 0 := by decide
  exact (ofAdd_nsmul _ _).symm.trans (by rw [h]; rfl)

end G3025

/-- **`(Z₁₁ × Z₁₁) ⋊ (Z₅ × Z₅)`.** Every language recognized by `G3025` has generalized star
height at most one. -/
theorem height_one_G3025 {Alphabet : Type u} [Finite Alphabet] (T : FreeMonoid Alphabet →* G3025)
    (F : Set G3025) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  height_one_of_abelian_normal_exponent_prime G3025.base G3025.base_comm G3025.comm_mem
    G3025.pow_five_mem T F

end GeneralizedStarHeight
