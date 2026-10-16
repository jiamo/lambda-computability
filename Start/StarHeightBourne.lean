import Start.StarHeightIndexThreeAll

/-!
# Bourne's Conjectures 4.11 and 4.12 in full

* `vcount δ q x w`: the number of positions of `w` that read the letter `x` in the state `q` of the
  translation automaton on a finite `ZMod 3`-vector space `V` (letter `b` adds `δ b`, words are read
  from `0`).
* `vcount_height_one`: for every `n` and `k < n`, the words with `vcount δ q x w ≡ k (mod n)` have
  generalized star height at most one (Bourne's Conjecture 4.12, state set `(Z₃)ʳ`).
* `height_one_of_abelian_normal_exponent_three`: every language recognized by a finite group with
  an abelian normal subgroup `N` such that `G ⧸ N` is abelian of exponent `3` has height at most
  one (Bourne's Conjecture 4.11, for groups of `AbGrp * Z₃`).

The reduction to one dimension is a character sum.  With `D` the dual of `V` and `|D| = 3c`,
`#{φ ∈ D | φ v = 0}` is `3c` for `v = 0` and `c` otherwise, so for every word

  `Σ_{φ ∈ D} zcount (φ ∘ δ) (φ q) x 0 w = c · |w|ₓ + 2c · vcount δ q x w`

(`charSum_zcount`).  Each `zcount (φ ∘ δ) (φ q) x 0 w` is a state count of a `ZMod 3` automaton,
of height one modulo every `m` (`zcount_height_one_mod`), so all counts are taken modulo `2cn`.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-! ### Languages fixed by residues of counts -/

/-- A language decided by the residues modulo `M` of finitely many counts, each of whose residue
classes has height at most one, has height at most one. -/
theorem height_one_of_residues {α : Type u} {ι : Type} [Finite ι] (g : ι → List α → ℕ) {M : ℕ}
    (hM : 0 < M) (hg : ∀ i r, r < M → HasHeightAtMost {w | g i w % M = r} 1) (L : Language α)
    (P : (ι → ℕ) → Prop) (hL : ∀ w, w ∈ L ↔ P (fun i => g i w % M)) :
    HasHeightAtMost L 1 := by
  have heq : L = ⨆ z : {z : ι → Fin M // P (fun i => (z i : ℕ))},
      ⨅ i, ({w | g i w % M = z.1 i} : Language α) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨fun i => ⟨g i w % M, Nat.mod_lt _ hM⟩, (hL w).mp hw⟩, ?_⟩
      exact HasHeightAtMost.mem_iInf_lang.mpr fun i => rfl
    · intro hw
      obtain ⟨z, hz⟩ := Language.mem_iSup.mp hw
      have hz' := HasHeightAtMost.mem_iInf_lang.mp hz
      rw [hL w]
      have : (fun i => g i w % M) = fun i => (z.1 i : ℕ) := funext fun i => hz' i
      rw [this]
      exact z.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun z => HasHeightAtMost.iInf _ fun i => hg i _ (z.1 i).2

/-! ### Letter-in-state counts on a vector space -/

section VCount

variable {α : Type u} [DecidableEq α] {V : Type}

open Classical

/-- The number of positions `i` of `w` with `w[i] = x` whose state `((w.take i).map δ).sum`
is `q`. -/
noncomputable def vcount [AddMonoid V] (δ : α → V) (q : V) (x : α) (w : List α) : ℕ :=
  ((Finset.range w.length).filter
    (fun i => w[i]? = some x ∧ ((w.take i).map δ).sum = q)).card

/-- `vcount`, read from the state `s`. -/
noncomputable def vcountFrom [AddMonoid V] (δ : α → V) (q : V) (x : α) (s : V) (w : List α) : ℕ :=
  ((Finset.range w.length).filter
    (fun i => w[i]? = some x ∧ s + ((w.take i).map δ).sum = q)).card

lemma vcount_eq_vcountFrom [AddMonoid V] (δ : α → V) (q : V) (x : α) (w : List α) :
    vcount δ q x w = vcountFrom δ q x 0 w := by
  unfold vcount vcountFrom
  congr 1
  exact Finset.filter_congr fun i _ => by rw [zero_add]

lemma vcountFrom_nil [AddMonoid V] (δ : α → V) (q : V) (x : α) (s : V) :
    vcountFrom δ q x s [] = 0 := by
  simp [vcountFrom]

lemma vcountFrom_cons [AddMonoid V] (δ : α → V) (q : V) (x : α) (s : V) (b : α) (w : List α) :
    vcountFrom δ q x s (b :: w) =
      (if b = x ∧ s = q then 1 else 0) + vcountFrom δ q x (s + δ b) w := by
  simp only [vcountFrom, Finset.card_filter, List.length_cons, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [List.take_succ_cons, add_assoc]

end VCount

/-! ### Characters of `V` -/

section Characters

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

lemma finite_dual [Finite V] : Finite (Module.Dual (ZMod 3) V) :=
  Finite.of_injective (fun φ : Module.Dual (ZMod 3) V => (φ : V → ZMod 3)) DFunLike.coe_injective

/-- **Counting lemma.** For `v ≠ 0`, exactly a third of the characters vanish at `v`. -/
lemma card_dual_ker [Fintype (Module.Dual (ZMod 3) V)] (v : V) (hv : v ≠ 0) :
    3 * (Finset.univ.filter (fun φ : Module.Dual (ZMod 3) V => φ v = 0)).card =
      Fintype.card (Module.Dual (ZMod 3) V) := by
  classical
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : Module.Dual (ZMod 3) V, φ0 v ≠ 0 := by
    by_contra h
    push Not at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff (ZMod 3) v).mp h)
  set φ1 := (φ0 v)⁻¹ • φ0 with hφ1def
  have hφ1 : φ1 v = 1 := by
    rw [hφ1def, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ0]
  have hfib : ∀ t : ZMod 3,
      (Finset.univ.filter (fun φ : Module.Dual (ZMod 3) V => φ v = t)).card =
        (Finset.univ.filter (fun φ : Module.Dual (ZMod 3) V => φ v = 0)).card := by
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
  have hsum := Finset.card_eq_sum_card_fiberwise (f := fun φ : Module.Dual (ZMod 3) V => φ v)
    (s := Finset.univ) (t := (Finset.univ : Finset (ZMod 3))) (by simp)
  rw [Finset.card_univ] at hsum
  rw [hsum, Finset.sum_congr rfl (fun t _ => hfib t)]
  simp [Finset.sum_const, ZMod.card]

variable {α : Type u} [DecidableEq α]

open Classical in
/-- **The character identity.** -/
lemma charSum_zcount [Fintype (Module.Dual (ZMod 3) V)] (δ : α → V) (q : V) (x : α) (c : ℕ)
    (hc0 : Fintype.card (Module.Dual (ZMod 3) V) = 3 * c)
    (hc : ∀ v : V, v ≠ 0 →
      (Finset.univ.filter (fun φ : Module.Dual (ZMod 3) V => φ v = 0)).card = c)
    (s : V) (w : List α) :
    ∑ φ : Module.Dual (ZMod 3) V, zcount (fun a => φ (δ a)) (φ q) x (φ s) w =
      c * w.count x + 2 * c * vcountFrom δ q x s w := by
  induction w generalizing s with
  | nil => simp [zcount, vcountFrom_nil]
  | cons b w ih =>
      simp only [zcount]
      rw [Finset.sum_add_distrib]
      have hadd : ∀ φ : Module.Dual (ZMod 3) V, φ s + φ (δ b) = φ (s + δ b) :=
        fun φ => (map_add φ s (δ b)).symm
      simp_rw [hadd]
      rw [ih (s + δ b), vcountFrom_cons, List.count_cons]
      by_cases hb : b = x
      · subst hb
        simp only [true_and, beq_self_eq_true, if_true]
        rw [← Finset.card_filter]
        have hf : (Finset.univ.filter fun φ : Module.Dual (ZMod 3) V => φ s = φ q) =
            Finset.univ.filter fun φ : Module.Dual (ZMod 3) V => φ (s - q) = 0 := by
          ext φ
          simp [sub_eq_zero]
        rw [hf]
        by_cases hs : s = q
        · subst hs
          simp only [sub_self, map_zero, Finset.filter_true, Finset.card_univ, hc0, if_true]
          ring
        · rw [hc _ (sub_ne_zero.mpr hs), if_neg hs]
          ring
      · have hb' : ¬ (b == x) = true := by simpa using hb
        simp only [hb, false_and, if_false, Finset.sum_const_zero, hb', Bool.false_eq_true,
          add_zero, zero_add]

end Characters

/-- The number of occurrences of a letter is a state count of the trivial automaton. -/
lemma zcount_const_zero {α : Type u} [DecidableEq α] (x : α) :
    ∀ (w : List α), zcount (fun _ => (0 : ZMod 3)) 0 x 0 w = w.count x
  | [] => rfl
  | b :: w => by
      rw [zcount, add_zero, zcount_const_zero x w, List.count_cons]
      by_cases hb : b = x
      · simp [hb, add_comm]
      · simp [hb]

/-- **Bourne's Conjecture 4.12.** Every letter-in-state count of a translation automaton on a
finite `ZMod 3`-vector space has height at most one modulo every `n`. -/
theorem vcount_height_one {α : Type u} [Finite α] [DecidableEq α] {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [Finite V] (δ : α → V) (q : V) (x : α)
    (n k : ℕ) (hk : k < n) :
    HasHeightAtMost {w : List α | vcount δ q x w % n = k} 1 := by
  classical
  have hcount : ∀ m r, r < m → HasHeightAtMost {w : List α | w.count x % m = r} 1 := by
    intro m r hr
    have := zcount_height_one_mod (fun _ : α => (0 : ZMod 3)) x 0 hr
    simpa only [zcount_const_zero] using this
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
  have : Finite (Module.Dual (ZMod 3) V) := finite_dual
  let : Fintype (Module.Dual (ZMod 3) V) := Fintype.ofFinite _
  set c := (Finset.univ.filter (fun φ : Module.Dual (ZMod 3) V => φ v0 = 0)).card with hcdef
  have hc0 : Fintype.card (Module.Dual (ZMod 3) V) = 3 * c := (card_dual_ker v0 hv0).symm
  have hc : ∀ v : V, v ≠ 0 →
      (Finset.univ.filter (fun φ : Module.Dual (ZMod 3) V => φ v = 0)).card = c := by
    intro v hv
    have := card_dual_ker v hv
    omega
  have hcpos : 0 < c := by
    have : 0 < Fintype.card (Module.Dual (ZMod 3) V) := Fintype.card_pos
    omega
  have hn : 0 < n := by omega
  have hM : 0 < 2 * c * n := by positivity
  refine height_one_of_residues (ι := Option (Module.Dual (ZMod 3) V))
    (fun i w => i.elim (w.count x) (fun φ => zcount (fun a => φ (δ a)) (φ q) x 0 w)) hM ?_ _
    (fun r => (∑ φ : Module.Dual (ZMod 3) V, (r (some φ) : ZMod (2 * c * n))) -
      (c : ZMod (2 * c * n)) * (r none : ZMod (2 * c * n)) = ((2 * c * k : ℕ) : ZMod (2 * c * n)))
    ?_
  · intro i r hr
    cases i with
    | none => exact hcount _ r hr
    | some φ => exact zcount_height_one_mod (fun a => φ (δ a)) x (φ q) hr
  · intro w
    show vcount δ q x w % n = k ↔ _
    simp only [Option.elim, ZMod.natCast_mod]
    have hid := charSum_zcount δ q x c hc0 hc 0 w
    simp only [map_zero] at hid
    rw [← Nat.cast_sum, hid, vcount_eq_vcountFrom]
    have : ((c * w.count x + 2 * c * vcountFrom δ q x 0 w : ℕ) : ZMod (2 * c * n)) -
        (c : ZMod (2 * c * n)) * (w.count x : ZMod (2 * c * n)) =
          ((2 * c * vcountFrom δ q x 0 w : ℕ) : ZMod (2 * c * n)) := by
      push_cast; ring
    rw [this, ZMod.natCast_eq_natCast_iff', Nat.mul_mod_mul_left, Nat.mul_mod_mul_left,
      Nat.mod_eq_of_lt hk]
    constructor
    · intro h; rw [h]
    · intro h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h

/-! ### Assembly: groups in `AbGrp * Z₃` -/

section Assembly

open Classical

variable {Alphabet : Type u}

lemma tpairs_count_eq_vcountFrom {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (T : FreeMonoid Alphabet →* G) (q' : G ⧸ N) (a : Alphabet) :
    ∀ (w : List Alphabet) (q : G ⧸ N), (tpairs N T q w).count (q', a) =
      vcountFrom (fun b => Additive.ofMul (psi N T (FreeMonoid.of b))) (Additive.ofMul q') a
        (Additive.ofMul q) w
  | [], q => by simp [tpairs, vcountFrom_nil]
  | b :: w, q => by
      rw [tpairs, List.count_cons, vcountFrom_cons, tpairs_count_eq_vcountFrom N T q' a w,
        ← ofMul_mul, add_comm]
      congr 1
      by_cases hb : b = a
      · subst hb
        by_cases hq : q = q'
        · simp [hq]
        · have : ¬ Additive.ofMul q = Additive.ofMul q' := fun e => hq (Additive.ofMul.injective e)
          simp [hq, this]
      · simp [hb]

/-- **Bourne's Conjecture 4.11, for groups.** If `N` is an abelian normal subgroup of a finite
group `G` such that `G ⧸ N` is abelian of exponent `3`, every language recognized by `G` has
generalized star height at most one. -/
theorem height_one_of_abelian_normal_exponent_three [Finite Alphabet] {G : Type} [Group G]
    [Fintype G] (N : Subgroup G) [N.Normal] (hab : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hcomm : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) (hexp : ∀ x : G, x ^ 3 ∈ N)
    (T : FreeMonoid Alphabet →* G) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
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
  have hQ3 : ∀ q : G ⧸ N, q ^ 3 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with | H x => ?_
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hexp x)
  let : CommGroup (G ⧸ N) := { (inferInstance : Group (G ⧸ N)) with mul_comm := hQ }
  let : Module (ZMod 3) (Additive (G ⧸ N)) := AddCommGroup.zmodModule (fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow, hQ3]; rfl)
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
      vcount_height_one δ (Additive.ofMul pr.1) pr.2 (Nat.card N) (z.1.2 pr) (z.1.2 pr).2

end Assembly

end GeneralizedStarHeight
