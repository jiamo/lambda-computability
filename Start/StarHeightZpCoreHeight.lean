import Start.StarHeightZpCore

/-!
# The `Z_p` core: assembly

* `zpcore_moving`: `δ x = 1` and no other letter of displacement `0`.
* `zpcore_fixed`: `δ x = 0`.
* `zpcore`: `ZpCoreHeightOne p` for every prime `p`, by the reductions (erase the other letters of
  displacement `0`, scale by `(δ x)⁻¹`).
* `z5core : Z5CoreHeightOne` (Bourne's Question 5.8 for `r = 5`).
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability
open Classical

/-! ### Decomposing the weighted pair counts -/

section Decomp

variable {β : Type} {p : ℕ} [NeZero p] (σ : β → ZMod p)

lemma pairW_eq_sum (Q : β → β → Prop) : ∀ (u : List β) (s : ZMod p) (prev : Option β),
    pairW σ Q s prev u = ∑ s₀ : ZMod p, zphi s₀ * pcB σ Q s₀ s prev u
  | [], _, _ => by simp [pairW, pcB]
  | c :: u, s, prev => by
      rw [pairW, pairW_eq_sum Q u]
      simp only [pcB, mul_add, Finset.sum_add_distrib]
      congr 1
      by_cases h : ∃ a, prev = some a ∧ Q a c
      · simp [h]
      · simp [h]

lemma pcB_split (Q : β → β → Prop) (s₀ : ZMod p) : ∀ (u : List β) (s : ZMod p) (prev : Option β),
    pcB σ Q s₀ s prev u = ∑ d : ZMod p, pcB σ (fun a c => Q a c ∧ σ c = d) s₀ s prev u
  | [], _, _ => by simp [pcB]
  | c :: u, s, prev => by
      rw [pcB, pcB_split Q s₀ u]
      simp only [pcB, Finset.sum_add_distrib]
      congr 1
      cases prev with
      | none => simp
      | some b =>
          by_cases h1 : Q b c
          · by_cases h2 : s = s₀ <;> simp [h1, h2]
          · simp [h1]

lemma pairW_eq_sum2 (Q : β → β → Prop) (u : List β) :
    pairW σ Q 0 none u =
      ∑ s₀ : ZMod p, zphi s₀ * ∑ d : ZMod p, pcB σ (fun a c => Q a c ∧ σ c = d) s₀ 0 none u := by
  rw [pairW_eq_sum]
  exact Finset.sum_congr rfl fun s₀ _ => by rw [pcB_split σ Q s₀]

omit [NeZero p] in
lemma zpSum_eq_sum [Fintype β] [DecidableEq β] (w : List β) :
    zpSum σ w = ∑ b : β, (w.count b : ZMod p) * σ b := by
  induction w with
  | nil => simp
  | cons c w ih =>
      rw [zpSum_cons, ih]
      simp only [List.count_cons, Nat.cast_add, add_mul, Finset.sum_add_distrib]
      rw [add_comm]
      congr 1
      simp [beq_iff_eq]

end Decomp

/-! ### Simple counts -/

section Simple

variable {β : Type}

lemma count_height [Finite β] [DecidableEq β] (b : β) {M r : ℕ} (hM : 0 < M) (hr : r < M) :
    HasHeightAtMost {w : List β | w.count b % M = r} 1 := by
  have : NeZero M := ⟨by omega⟩
  let T : FreeMonoid β →* Multiplicative (ZMod M) :=
    FreeMonoid.lift fun a => Multiplicative.ofAdd (if a = b then 1 else 0)
  have hT : ∀ w : List β, T (FreeMonoid.ofList w) = Multiplicative.ofAdd (w.count b : ZMod M) := by
    intro w
    rw [FreeMonoid.lift_apply, FreeMonoid.toList_ofList]
    induction w with
    | nil => simp
    | cons c w ih =>
        rw [List.map_cons, List.prod_cons, ih, ← ofAdd_add, List.count_cons]
        congr 1
        by_cases h : c = b
        · simp [h, add_comm]
        · simp [h, beq_iff_eq]
  have heq : {w : List β | w.count b % M = r} =
      {w | T (FreeMonoid.ofList w) ∈ ({Multiplicative.ofAdd (r : ZMod M)} : Set _)} := by
    ext w
    show w.count b % M = r ↔ T (FreeMonoid.ofList w) = Multiplicative.ofAdd (r : ZMod M)
    rw [hT, EmbeddingLike.apply_eq_iff_eq]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  rw [heq]
  exact height_one_of_comm (fun x y => mul_comm x y) T _

lemma ind_height (L : Language β) (hL : HasHeightAtMost L 1) (M r : ℕ) :
    HasHeightAtMost ({w : List β | (if w ∈ L then 1 else 0) % M = r} : Language β) 1 := by
  have key : ∀ w, w ∈ ({w : List β | (if w ∈ L then 1 else 0) % M = r} : Language β) ↔
      (if w ∈ L then 1 % M = r else 0 % M = r) := by
    intro w
    show (if w ∈ L then 1 else 0) % M = r ↔ _
    by_cases hw : w ∈ L
    · rw [if_pos hw, if_pos hw]
    · rw [if_neg hw, if_neg hw]
  by_cases h1 : 1 % M = r <;> by_cases h0 : 0 % M = r
  · have : ({w : List β | (if w ∈ L then 1 else 0) % M = r} : Language β) = ⊤ := by
      ext w
      rw [key]
      exact ⟨fun _ => trivial, fun _ => by split_ifs <;> assumption⟩
    rw [this]; exact HasHeightAtMost.top 1
  · have : ({w : List β | (if w ∈ L then 1 else 0) % M = r} : Language β) = L := by
      ext w
      rw [key]
      by_cases hw : w ∈ L
      · rw [if_pos hw]; exact ⟨fun _ => hw, fun _ => h1⟩
      · rw [if_neg hw]; exact ⟨fun h => absurd h h0, fun h => absurd h hw⟩
    rw [this]; exact hL
  · have : ({w : List β | (if w ∈ L then 1 else 0) % M = r} : Language β) = Lᶜ := by
      ext w
      rw [key]
      by_cases hw : w ∈ L
      · rw [if_pos hw]; exact ⟨fun h => absurd h h1, fun h => absurd hw h⟩
      · rw [if_neg hw]; exact ⟨fun _ => hw, fun _ => h0⟩
    rw [this]; exact hL.compl
  · have : ({w : List β | (if w ∈ L then 1 else 0) % M = r} : Language β) = (0 : Language β) := by
      ext w
      rw [key]
      constructor
      · intro h
        split_ifs at h
        · exact absurd h h1
        · exact absurd h h0
      · intro h
        exact absurd h (Language.notMem_zero w)
    rw [this]; exact HasHeightAtMost.zero 1

lemma lastOr_none_eq (x : β) (w : List β) : lastOr none w = some x ↔ w ∈ (⊤ : Language β) * {[x]} := by
  constructor
  · intro h
    rcases List.eq_nil_or_concat w with rfl | ⟨v, a, rfl⟩
    · simp [lastOr] at h
    · simp only [List.concat_eq_append, lastOr_snoc, Option.some.injEq] at h ⊢
      subst h
      exact Language.mem_mul.mpr ⟨v, trivial, [a], rfl, rfl⟩
  · intro h
    obtain ⟨v, -, y, hy, rfl⟩ := Language.mem_mul.mp h
    have hy' : y = [x] := hy
    rw [hy', lastOr_snoc]

lemma lastx_height [Finite β] [DecidableEq β] (x : β) (M r : ℕ) :
    HasHeightAtMost {w : List β | (if lastOr none w = some x then 1 else 0) % M = r} 1 := by
  have h := ind_height ((⊤ : Language β) * {[x]})
    ((Aperiodic.sf_top.concat (HasHeightAtMost.singleton _ 0)).mono (by omega)) M r
  have heq : ({w : List β | (if lastOr none w = some x then 1 else 0) % M = r} : Language β) =
      {w : List β | (if w ∈ (⊤ : Language β) * {[x]} then 1 else 0) % M = r} := by
    ext w
    show (if lastOr none w = some x then 1 else 0) % M = r ↔
      (if w ∈ (⊤ : Language β) * {[x]} then 1 else 0) % M = r
    by_cases hw : lastOr none w = some x
    · rw [if_pos hw, if_pos ((lastOr_none_eq x w).mp hw)]
    · rw [if_neg hw, if_neg (fun h => hw ((lastOr_none_eq x w).mpr h))]
  rw [heq]; exact h

end Simple

/-! ### The moving case -/

section Moving

variable {β : Type} [Fintype β] [DecidableEq β] {p : ℕ} [hp : Fact p.Prime]

/-- The two pair relations. -/
def QAB (x : β) : Bool → β → β → Prop
  | true => QA x
  | false => QB x

/-- The counts: letters, pairs (relation, state, displacement of the second letter), last
letter. -/
noncomputable def zpG (σ : β → ZMod p) (x : β) :
    β ⊕ (Bool × ZMod p × ZMod p) ⊕ Unit → List β → ℕ :=
  Sum.elim (fun b w => w.count b)
    (Sum.elim (fun t w => pcB σ (fun a c => QAB x t.1 a c ∧ σ c = t.2.2) t.2.1 0 none w)
      (fun _ w => if lastOr none w = some x then 1 else 0))

omit [Fintype β] in
/-- **The identity modulo `M`.** -/
lemma zp_identity_cast (σ : β → ZMod p) (x : β) (hx : σ x = 1) (M : ℕ) (w : List β) :
    ((p * vcount σ 0 x w : ℕ) : ZMod M) =
      (w.count x : ZMod M) +
        ∑ s₀ : ZMod p, (zphi s₀ : ZMod M) *
          ∑ d : ZMod p, (pcB σ (fun a c => QAB x false a c ∧ σ c = d) s₀ 0 none w : ZMod M) -
        ∑ s₀ : ZMod p, (zphi s₀ : ZMod M) *
          ∑ d : ZMod p, (pcB σ (fun a c => QAB x true a c ∧ σ c = d) s₀ 0 none w : ZMod M) +
        (if lastOr none w = some x then (zphi (zpSum σ w) : ZMod M) else 0) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have h := zp_identity_aux σ x hx w 0 none (fun _ => rfl)
  rw [pairW_eq_sum2, pairW_eq_sum2, if_neg (by simp), zero_add] at h
  rw [vcount_eq_vcountFrom]
  have h' := congrArg (fun t : ℕ => (t : ZMod M)) h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, add_zero] at h'
  have e : (if lastOr none w = some x then ((zphi (zpSum σ w) : ℕ) : ZMod M) else 0) =
      (((if lastOr none w = some x then zphi (zpSum σ w) else 0 : ℕ)) : ZMod M) := by
    split_ifs <;> simp
  rw [e]
  push_cast
  show _ = _ + ∑ s₀ : ZMod p, (zphi s₀ : ZMod M) *
      ∑ d : ZMod p, (pcB σ (fun a c => QB x a c ∧ σ c = d) s₀ 0 none w : ZMod M) -
    ∑ s₀ : ZMod p, (zphi s₀ : ZMod M) *
      ∑ d : ZMod p, (pcB σ (fun a c => QA x a c ∧ σ c = d) s₀ 0 none w : ZMod M) + _
  push_cast at h'
  linear_combination h'

/-- **The moving case** `δ x = 1`, every other letter of nonzero displacement. -/
theorem zpcore_moving (σ : β → ZMod p) (x : β) (hx : σ x = 1) (hne : ∀ c, c ≠ x → σ c ≠ 0)
    {n k : ℕ} (hk : k < n) : HasHeightAtMost {w : List β | vcount σ 0 x w % n = k} 1 := by
  have hp0 : 0 < p := hp.out.pos
  have hp2 : 2 ≤ p := hp.out.two_le
  have hM : 0 < p * n := Nat.mul_pos hp0 (by omega)
  have hM2 : 1 < p * n := by nlinarith
  have hdvd : p ∣ p * n := dvd_mul_right p n
  have hcastp : ∀ a : ℕ, (((a % (p * n) : ℕ)) : ZMod p) = a := fun a => by
    rw [← ZMod.natCast_mod (a % (p * n)) p, Nat.mod_mod_of_dvd _ hdvd, ZMod.natCast_mod]
  let P : (β ⊕ (Bool × ZMod p × ZMod p) ⊕ Unit → ℕ) → Prop := fun z =>
    ((p * k : ℕ) : ZMod (p * n)) =
      (z (Sum.inl x) : ZMod (p * n)) +
        ∑ s₀ : ZMod p, (zphi s₀ : ZMod (p * n)) *
          ∑ d : ZMod p, (z (Sum.inr (Sum.inl (false, s₀, d))) : ZMod (p * n)) -
        ∑ s₀ : ZMod p, (zphi s₀ : ZMod (p * n)) *
          ∑ d : ZMod p, (z (Sum.inr (Sum.inl (true, s₀, d))) : ZMod (p * n)) +
        (if z (Sum.inr (Sum.inr ())) = 1 then
          (zphi (∑ b : β, ((z (Sum.inl b) : ℕ) : ZMod p) * σ b) : ZMod (p * n)) else 0)
  have hL : ∀ w, w ∈ ({w : List β | vcount σ 0 x w % n = k} : Language β) ↔
      P (fun i => zpG σ x i w % (p * n)) := by
    intro w
    show vcount σ 0 x w % n = k ↔ _
    rw [← zmod_mul_iff hp0 hk, zp_identity_cast σ x hx (p * n) w]
    have hind : ((if lastOr none w = some x then 1 else 0) % (p * n) = 1) ↔
        lastOr none w = some x := by
      by_cases h : lastOr none w = some x
      · simp only [h, if_true, Nat.mod_eq_of_lt hM2]
      · simp only [h, if_false, Nat.zero_mod, iff_false]; omega
    have hsum : ∑ b : β, (((w.count b % (p * n) : ℕ)) : ZMod p) * σ b = zpSum σ w := by
      rw [zpSum_eq_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [hcastp]
    simp only [P, zpG, Sum.elim_inl, Sum.elim_inr, ZMod.natCast_mod, hind, hsum]
    exact eq_comm
  refine height_one_of_residues (zpG σ x) hM ?_ _ P hL
  rintro (b | ⟨t, s₀, d⟩ | ⟨⟩) r hr
  · exact count_height b hM hr
  · have hQ : ∀ a c, (QAB x t a c ∧ σ c = d) → σ c ≠ 0 := by
      rintro a c ⟨h, -⟩
      cases t with
      | true => obtain ⟨-, rfl⟩ := h; rw [hx]; exact one_ne_zero
      | false => exact hne c h.2
    have hP : (∀ a c, (QAB x t a c ∧ σ c = d) → a = x ∧ c ≠ x) ∨
        (∀ a c, (QAB x t a c ∧ σ c = d) → a ≠ x ∧ c = x) := by
      cases t with
      | true => exact Or.inr fun a c h => h.1
      | false => exact Or.inl fun a c h => h.1
    exact pcB_height σ _ (fun a c h => h.2) hQ hP hr
  · exact lastx_height x (p * n) r

end Moving

/-! ### The fixed case -/

section Fixed

variable {β : Type} [DecidableEq β] {p : ℕ} (σ : β → ZMod p)

lemma vcountFrom_append_zp (x : β) (u v : List β) (s : ZMod p) :
    vcountFrom σ 0 x s (u ++ v) = vcountFrom σ 0 x s u + vcountFrom σ 0 x (s + zpSum σ u) v := by
  induction u generalizing s with
  | nil => simp [vcountFrom_nil]
  | cons c u ih =>
      rw [List.cons_append, vcountFrom_cons, vcountFrom_cons, ih, zpSum_cons, add_assoc,
        add_assoc]

lemma vcountFrom_zero_of (x : β) :
    ∀ (u : List β) (s : ZMod p), (∀ q, q <+: u → q ≠ u → s + zpSum σ q ≠ 0) →
      vcountFrom σ 0 x s u = 0
  | [], _, _ => vcountFrom_nil ..
  | c :: u, s, h => by
      have h0 : s ≠ 0 := by
        have := h [] List.nil_prefix (by simp)
        simpa using this
      rw [vcountFrom_cons, if_neg (fun h' => h0 h'.2), zero_add]
      refine vcountFrom_zero_of x u _ fun q hq hne => ?_
      have := h (c :: q) (List.cons_prefix_cons.mpr ⟨rfl, hq⟩) (by simpa using hne)
      rwa [zpSum_cons, ← add_assoc] at this

/-- The positions of `x` in state `0` inside a word of `zpNR σ` after its first letter. -/
lemma vcountFrom_tail (x : β) (hx : σ x = 0) {c : β} {t : List β} (ht : c :: t ∈ zpNR σ) :
    vcountFrom σ 0 x 0 (c :: t) = 0 := by
  have hc : σ c ≠ 0 := by
    have := ht [c] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (by simp)
    rwa [zpSum_single] at this
  have hcx : c ≠ x := fun h => hc (h ▸ hx)
  rw [vcountFrom_cons, if_neg (fun h => hcx h.1), zero_add]
  refine vcountFrom_zero_of σ x t _ fun q hq _ => ?_
  have := ht (c :: q) (List.cons_prefix_cons.mpr ⟨rfl, hq⟩) (by simp)
  rwa [zpSum_cons, zero_add] at *

lemma vcountFrom_block_fixed (x : β) (hx : σ x = 0) {e : List β} (he : e ∈ zpX σ) :
    vcountFrom σ 0 x 0 e = if e = [x] then 1 else 0 := by
  obtain ⟨hne, h0, hpre⟩ := he
  rcases e with _ | ⟨c, e'⟩
  · exact absurd rfl hne
  by_cases hcx : c = x
  · subst hcx
    have he' : e' = [] := by
      by_contra hne'
      exact hpre [c] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (by simp)
        (by simpa using hne') (by rw [zpSum_single]; exact hx)
    subst he'
    simp [vcountFrom_cons, vcountFrom_nil]
  · rw [if_neg (by simp [hcx]), vcountFrom_cons, if_neg (fun h => hcx h.1), zero_add]
    refine vcountFrom_zero_of σ x e' _ fun q hq hqne => ?_
    have := hpre (c :: q) (List.cons_prefix_cons.mpr ⟨rfl, hq⟩) (by simp) (by simpa using hqne)
    rwa [zpSum_cons, zero_add] at *

lemma vcount_fixed_eq (x : β) (hx : σ x = 0) (w : List β) :
    vcount σ 0 x w = bcount ({[x]} : Language β) (zpSplit σ w).1 := by
  obtain ⟨h1, h2, h3⟩ := zpSplit_spec σ w
  rw [vcount_eq_vcountFrom]
  conv_lhs => rw [← h1]
  generalize (zpSplit σ w).1 = es at h2 ⊢
  induction es with
  | nil =>
      simp only [List.flatten_nil, List.nil_append, bcount, List.countP_nil]
      rcases hT : (zpSplit σ w).2 with _ | ⟨c, t⟩
      · exact vcountFrom_nil ..
      · rw [hT] at h3; exact vcountFrom_tail σ x hx h3
  | cons e es ih =>
      have he := h2 e (by simp)
      rw [List.flatten_cons, List.append_assoc, vcountFrom_append_zp, vcountFrom_block_fixed σ x hx he,
        zero_add, he.2.1, ih (fun f hf => h2 f (by simp [hf]))]
      simp only [bcount, List.countP_cons]
      rw [add_comm]
      congr 1
      by_cases h : e = [x]
      · subst h
        rw [if_pos rfl, if_pos]
        exact decide_eq_true rfl
      · simp [h, show e ∉ ({[x]} : Language β) from h]

/-- **The fixed case** `δ x = 0`. -/
theorem zpcore_fixed [Fact p.Prime] [Finite β] (x : β) (hx : σ x = 0) {n k : ℕ} (hk : k < n) :
    HasHeightAtMost {w : List β | vcount σ 0 x w % n = k} 1 := by
  have hK : ({[x]} : Language β) ≤ zpX σ := by
    intro e he
    have he' : e = [x] := he
    subst he'
    refine ⟨by simp, by rw [zpSum_single]; exact hx, fun q hq hne hqe => ?_⟩
    rcases List.prefix_cons_iff.mp hq with h | ⟨q', rfl, hq'⟩
    · exact absurd h hne
    · rw [List.prefix_nil.mp hq'] at hqe; exact absurd rfl hqe
  have h := bcount_split_height σ ({[x]} : Language β) hK (HasHeightAtMost.singleton _ 0)
    (kstar_singleton_starFree [x] (by simp) (fun j h1 h2 => by simp at h2; omega)) hk
  have heq : {w : List β | vcount σ 0 x w % n = k} =
      {w | bcount ({[x]} : Language β) (zpSplit σ w).1 % n = k} := by
    ext w
    show vcount σ 0 x w % n = k ↔ bcount ({[x]} : Language β) (zpSplit σ w).1 % n = k
    rw [vcount_fixed_eq σ x hx]
  rw [heq]; exact h

end Fixed

/-! ### The core for every prime -/

/-- **The `Z_p` core.** -/
def ZpCoreHeightOne (p : ℕ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod p) (x : α) (n k : ℕ),
    k < n → HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1

/-- Transport of the count along an alphabetic morphism that erases letters of displacement `0`
other than `x`. -/
lemma vcountFrom_filterMap_erase {α β : Type} [DecidableEq α] [DecidableEq β] {V : Type}
    [AddMonoid V] (δ : α → V) (x : α) (σ : β → V) (x' : β) (φ : α → Option β)
    (h0 : ∀ y, φ y = none → δ y = 0 ∧ y ≠ x)
    (h1 : ∀ y c, φ y = some c → σ c = δ y ∧ (y = x ↔ c = x')) :
    ∀ (w : List α) (s : V), vcountFrom δ 0 x s w = vcountFrom σ 0 x' s (w.filterMap φ)
  | [], s => by simp [vcountFrom_nil]
  | b :: w, s => by
      rw [vcountFrom_cons]
      cases hb : φ b with
      | none =>
          obtain ⟨hd, hx⟩ := h0 b hb
          rw [List.filterMap_cons, hb, if_neg (fun h => hx h.1), hd, add_zero, zero_add]
          exact vcountFrom_filterMap_erase δ x σ x' φ h0 h1 w s
      | some c =>
          obtain ⟨hd, hx⟩ := h1 b c hb
          rw [List.filterMap_cons, hb, vcountFrom_cons, ← hd,
            vcountFrom_filterMap_erase δ x σ x' φ h0 h1 w]
          congr 1
          by_cases hc : c = x' ∧ s = 0
          · rw [if_pos hc, if_pos ⟨hx.mpr hc.1, hc.2⟩]
          · rw [if_neg hc, if_neg (fun h => hc ⟨hx.mp h.1, h.2⟩)]

/-- **The `Z_p` core holds for every prime `p`.** -/
theorem zpcore (p : ℕ) [Fact p.Prime] : ZpCoreHeightOne p := by
  intro α _ _ δ x n k hk
  by_cases h0 : δ x = 0
  · exact zpcore_fixed δ x h0 hk
  -- scale by `(δ x)⁻¹`
  set c := (δ x)⁻¹ with hcdef
  have hc : c ≠ 0 := inv_ne_zero h0
  let f : ZMod p →+ ZMod p := AddMonoidHom.mulLeft c
  have hf : Function.Injective f := fun a b h => mul_left_cancel₀ hc h
  let δ' : α → ZMod p := fun a => c * δ a
  have hδ'x : δ' x = 1 := inv_mul_cancel₀ h0
  have hscale : ∀ w, vcount δ 0 x w = vcount δ' 0 x w := by
    intro w
    rw [vcount_eq_vcountFrom, vcount_eq_vcountFrom, ← vcountFrom_hom f hf δ 0 x 0 w]
    simp [f, δ']
  -- erase the other letters of displacement `0`
  let β := {a : α // a = x ∨ δ' a ≠ 0}
  let x' : β := ⟨x, Or.inl rfl⟩
  let σ : β → ZMod p := fun b => δ' b.1
  let φ : α → Option β := fun a => if h : a = x ∨ δ' a ≠ 0 then some ⟨a, h⟩ else none
  have hφ0 : ∀ y, φ y = none → δ' y = 0 ∧ y ≠ x := by
    intro y hy
    simp only [φ] at hy
    split_ifs at hy with h
    push Not at h
    exact ⟨h.2, h.1⟩
  have hφ1 : ∀ y b, φ y = some b → σ b = δ' y ∧ (y = x ↔ b = x') := by
    intro y b hy
    simp only [φ] at hy
    split_ifs at hy with h
    simp only [Option.some.injEq] at hy
    subst hy
    exact ⟨rfl, ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩⟩
  have hne : ∀ b, b ≠ x' → σ b ≠ 0 := by
    rintro ⟨b, hb | hb⟩ hbx
    · exact absurd (Subtype.ext hb) hbx
    · exact hb
  have heq : {w : List α | vcount δ 0 x w % n = k} =
      invAlph φ {u : List β | vcount σ 0 x' u % n = k} := by
    ext w
    show vcount δ 0 x w % n = k ↔ vcount σ 0 x' (w.filterMap φ) % n = k
    rw [hscale, vcount_eq_vcountFrom, vcount_eq_vcountFrom,
      vcountFrom_filterMap_erase δ' x σ x' φ hφ0 hφ1 w 0]
  rw [heq]
  exact (zpcore_moving σ x' hδ'x hne hk).invAlph φ

/-- **The `Z₅` core** (Bourne's Question 5.8 for `r = 5`). -/
def Z5CoreHeightOne : Prop := ∀ (α : Type) [Fintype α] [DecidableEq α] (δ : α → ZMod 5) (x : α) (n k : ℕ),
  k < n → HasHeightAtMost {w : List α | vcount δ 0 x w % n = k} 1

/-- **The `Z₅` core holds.** -/
theorem z5core : Z5CoreHeightOne := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact zpcore 5

end GeneralizedStarHeight
