/-
**Size-change termination** — task `M23-SIZE-CHANGE` (round 7), after Lee, Jones and Ben-Amram,
*The size-change principle for program termination* (POPL 2001), the basis of Agda's
termination checker.

* `SizeChange.SCG n` — size-change graphs over the parameters `Fin n`, with strict (`↓`) and
  non-strict (`↓=`) arcs; `SizeChange.SCG.comp` — their composition (associative,
  `SCG.comp_assoc`);
* `SizeChange.SCT 𝒢` — the call-sequence semantics: every infinite multipath of graphs of `𝒢`
  has an infinite thread with infinitely many strict descents;
* `SizeChange.InCl 𝒢` — the composition closure; `SizeChange.Criterion 𝒢` — the closure
  criterion: every idempotent graph `G = G;G` of the closure has a strict self-arc;
* `SizeChange.ramsey_pairs` — the **infinite Ramsey theorem for pairs** with finitely many
  colours (none was found in the pinned Mathlib, which has Hindman's and Hales–Jewett's
  theorems);
* `SizeChange.sct_of_criterion` — **the closure criterion implies size-change termination**
  (the direction a termination checker uses), by Ramsey's theorem;
* `SizeChange.closureFS`, `SizeChange.mem_closureFS_iff` — the closure computed by saturation,
  stabilising within `Fintype.card (SCG n)` steps; `SizeChange.Criterion.decidable` — **the
  criterion is decidable**; `SizeChange.sct_of_decide` — the checker;
* `SizeChange.criterion_of_sct` — conversely, size-change termination implies the criterion
  (periodic unfolding of an idempotent graph; no Ramsey argument needed);
* `SizeChange.sct_iff_criterion` — **the closure criterion characterises SCT**, and
  `SizeChange.SCT.decidable` — **SCT is decidable**.

Simplification: a single parameter set for all graphs (every multipath is composable).  The
general program setting, with a parameter set per function and multipaths following the call
graph, is not formalised.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false


namespace SizeChange

theorem infinite_fiber {S : Set ℕ} (h : S.Infinite) {α : Type} [Finite α] (c : ℕ → α) :
    ∃ a, {x | x ∈ S ∧ c x = a}.Infinite := by
  by_contra hne
  simp only [not_exists, Set.not_infinite] at hne
  apply h
  have : S = ⋃ a, {x | x ∈ S ∧ c x = a} := by
    ext x; simp
  rw [this]
  exact Set.finite_iUnion fun a => hne a

theorem ramsey_step {α : Type} [Finite α] (c : ℕ → ℕ → α) (S : Set ℕ) (hS : S.Infinite) :
    ∃ p : ℕ × α × {S' : Set ℕ // S'.Infinite},
      p.1 ∈ S ∧ p.2.2.1 ⊆ S ∧ ∀ x ∈ p.2.2.1, p.1 < x ∧ c p.1 x = p.2.1 := by
  obtain ⟨m, hm⟩ := hS.nonempty
  have h1 : {x | x ∈ S ∧ m < x}.Infinite := by
    have : {x | x ∈ S ∧ m < x} = S \ Set.Iic m := by ext; simp
    rw [this]; exact hS.sdiff (Set.finite_Iic m)
  obtain ⟨a, ha⟩ := infinite_fiber h1 (c m)
  exact ⟨⟨m, a, _, ha⟩, hm, fun x hx => hx.1.1, fun x hx => ⟨hx.1.2, hx.2⟩⟩

/-- **Infinite Ramsey theorem for pairs**, finitely many colours. -/
theorem ramsey_pairs {α : Type} [Finite α] (c : ℕ → ℕ → α) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∃ a : α, ∀ i j, i < j → c (f i) (f j) = a := by
  classical
  -- the iteration on infinite sets
  let pick : {S : Set ℕ // S.Infinite} → ℕ × α × {S' : Set ℕ // S'.Infinite} := fun S =>
    Classical.choose (ramsey_step c S.1 S.2)
  have hpick : ∀ S, (pick S).1 ∈ S.1 ∧ (pick S).2.2.1 ⊆ S.1 ∧
      ∀ x ∈ (pick S).2.2.1, (pick S).1 < x ∧ c (pick S).1 x = (pick S).2.1 := fun S =>
    Classical.choose_spec (ramsey_step c S.1 S.2)
  let step : {S : Set ℕ // S.Infinite} → {S : Set ℕ // S.Infinite} := fun S => (pick S).2.2
  let pt : {S : Set ℕ // S.Infinite} → ℕ := fun S => (pick S).1
  let col : {S : Set ℕ // S.Infinite} → α := fun S => (pick S).2.1
  have hpt : ∀ S, pt S ∈ S.1 := fun S => (hpick S).1
  have hsub : ∀ S, (step S).1 ⊆ S.1 := fun S => (hpick S).2.1
  have hcol : ∀ S, ∀ x ∈ (step S).1, pt S < x ∧ c (pt S) x = col S := fun S => (hpick S).2.2
  let seq : ℕ → {S : Set ℕ // S.Infinite} := fun k => step^[k] ⟨Set.univ, Set.infinite_univ⟩
  have hseq : ∀ k, seq (k + 1) = step (seq k) := fun k => Function.iterate_succ_apply' _ _ _
  have hmono : ∀ k l, k ≤ l → (seq l).1 ⊆ (seq k).1 := by
    intro k l hkl
    induction hkl with
    | refl => exact le_rfl
    | step _ ih => rw [hseq]; exact (hsub _).trans ih
  have hpair : ∀ k l, k < l → pt (seq k) < pt (seq l) ∧ c (pt (seq k)) (pt (seq l)) = col (seq k) := by
    intro k l hkl
    have : pt (seq l) ∈ (step (seq k)).1 := by
      rw [← hseq]; exact hmono (k + 1) l hkl (hpt _)
    exact hcol _ _ this
  obtain ⟨a, ha⟩ := infinite_fiber (Set.infinite_univ (α := ℕ)) (fun k => col (seq k))
  have ha' : (Set.ofPred fun k => col (seq k) = a).Infinite := by
    simpa using ha
  refine ⟨fun i => pt (seq (Nat.nth (fun k => col (seq k) = a) i)), ?_, a, ?_⟩
  · intro i j hij
    exact (hpair _ _ (Nat.nth_strictMono ha' hij)).1
  · intro i j hij
    rw [(hpair _ _ (Nat.nth_strictMono ha' hij)).2]
    exact Nat.nth_mem_of_infinite ha' i


/-! ### Size-change graphs and their composition -/

/-- A **size-change graph** over the parameters `Fin n`: a set of arcs `(x, y, strict)`, where
`strict = true` is a decreasing arc `x ↓ y` and `strict = false` a non-increasing arc `x ↓= y`. -/
abbrev SCG (n : ℕ) := Finset (Fin n × Fin n × Bool)

variable {n : ℕ}

/-- Composition of size-change graphs: an arc `x → z` for each `x → y` in `G` and `y → z` in `H`,
strict when one of the two is. -/
def SCG.comp (G H : SCG n) : SCG n :=
  ((G ×ˢ H).filter (fun p => p.1.2.1 = p.2.1)).image
    (fun p => (p.1.1, p.2.2.1, p.1.2.2 || p.2.2.2))

theorem SCG.mem_comp {G H : SCG n} {x z : Fin n} {b : Bool} :
    (x, z, b) ∈ G.comp H ↔ ∃ y b₁ b₂, (x, y, b₁) ∈ G ∧ (y, z, b₂) ∈ H ∧ b = (b₁ || b₂) := by
  simp only [SCG.comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨x', y, b₁⟩, ⟨y', z', b₂⟩⟩, ⟨⟨h₁, h₂⟩, hy⟩, hx, hz, hb⟩
    simp only at hy hx hz hb h₁ h₂
    subst hy hx hz hb
    exact ⟨y, b₁, b₂, h₁, h₂, rfl⟩
  · rintro ⟨y, b₁, b₂, h₁, h₂, rfl⟩
    exact ⟨⟨⟨x, y, b₁⟩, ⟨y, z, b₂⟩⟩, ⟨⟨h₁, h₂⟩, rfl⟩, rfl, rfl, rfl⟩

theorem SCG.comp_assoc (G H K : SCG n) : (G.comp H).comp K = G.comp (H.comp K) := by
  ext ⟨x, z, b⟩
  simp only [SCG.mem_comp]
  constructor
  · rintro ⟨w, b₁₂, b₃, ⟨y, b₁, b₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    exact ⟨y, b₁, b₂ || b₃, h₁, ⟨w, b₂, b₃, h₂, h₃, rfl⟩, by simp [Bool.or_assoc]⟩
  · rintro ⟨y, b₁, b₂₃, h₁, ⟨w, b₂, b₃, h₂, h₃, rfl⟩, rfl⟩
    exact ⟨w, b₁ || b₂, b₃, ⟨y, b₁, b₂, h₁, h₂, rfl⟩, h₃, by simp [Bool.or_assoc]⟩

/-! ### Multipaths, threads, and the size-change termination property -/

/-- The composition `g i ; g (i+1) ; … ; g (i+m)` of a block of a multipath. -/
def compR (g : ℕ → SCG n) (i : ℕ) : ℕ → SCG n
  | 0 => g i
  | m + 1 => (compR g i m).comp (g (i + m + 1))

/-- **Size-change termination** of a set `𝒢` of size-change graphs (the call-sequence
semantics): every infinite multipath `g 0, g 1, …` of graphs of `𝒢` has, from some point `i`
on, an infinite thread `t` (with arc labels `l`) with infinitely many strict descents. -/
def SCT (𝒢 : Finset (SCG n)) : Prop :=
  ∀ g : ℕ → SCG n, (∀ k, g k ∈ 𝒢) → ∃ (i : ℕ) (t : ℕ → Fin n) (l : ℕ → Bool),
    (∀ p, i ≤ p → (t p, t (p + 1), l p) ∈ g p) ∧ ∀ N, ∃ p, N ≤ p ∧ i ≤ p ∧ l p = true

/-- The **composition closure** of `𝒢`. -/
inductive InCl (𝒢 : Finset (SCG n)) : SCG n → Prop
  | base {G} : G ∈ 𝒢 → InCl 𝒢 G
  | comp {G H} : InCl 𝒢 G → InCl 𝒢 H → InCl 𝒢 (G.comp H)

/-- **The closure criterion**: every idempotent graph of the composition closure has a strict
self-arc. -/
def Criterion (𝒢 : Finset (SCG n)) : Prop :=
  ∀ G, InCl 𝒢 G → G.comp G = G → ∃ x, (x, x, true) ∈ G

theorem compR_inCl {𝒢 : Finset (SCG n)} {g : ℕ → SCG n} (hg : ∀ k, g k ∈ 𝒢) (i : ℕ) :
    ∀ m, InCl 𝒢 (compR g i m)
  | 0 => .base (hg i)
  | m + 1 => .comp (compR_inCl hg i m) (.base (hg _))

theorem compR_add (g : ℕ → SCG n) (i a : ℕ) :
    ∀ b, compR g i (a + b + 1) = (compR g i a).comp (compR g (i + a + 1) b)
  | 0 => rfl
  | b + 1 => by
      rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega, compR, compR_add g i a b, compR,
        SCG.comp_assoc]
      congr 3
      omega

/-- An arc of a block composition is realised by a path through the block. -/
theorem compR_path (g : ℕ → SCG n) (i : ℕ) :
    ∀ (m : ℕ) {x z : Fin n} {b : Bool}, (x, z, b) ∈ compR g i m →
      ∃ (t : ℕ → Fin n) (l : ℕ → Bool), t i = x ∧ t (i + m + 1) = z ∧
        (∀ p, i ≤ p → p < i + m + 1 → (t p, t (p + 1), l p) ∈ g p) ∧
        (b = true → ∃ p, i ≤ p ∧ p < i + m + 1 ∧ l p = true)
  | 0, x, z, b, h => by
      refine ⟨fun p => if p = i then x else z, fun _ => b, by simp, by simp, ?_, ?_⟩
      · intro p hp hp'
        obtain rfl : p = i := by omega
        simpa [compR] using h
      · intro hb; exact ⟨i, le_rfl, by omega, hb⟩
  | m + 1, x, z, b, h => by
      obtain ⟨y, b₁, b₂, h₁, h₂, rfl⟩ := SCG.mem_comp.1 h
      obtain ⟨t, l, ht0, ht1, harc, hdesc⟩ := compR_path g i m h₁
      refine ⟨fun p => if p ≤ i + m + 1 then t p else z,
        fun p => if p = i + m + 1 then b₂ else l p, by dsimp only; rw [if_pos (by omega)]; exact ht0,
        by dsimp only; rw [if_neg (by omega)], ?_, ?_⟩
      · intro p hp hp'
        by_cases hpe : p = i + m + 1
        · subst hpe
          simp only [le_refl, if_true, show ¬ (i + m + 1 + 1 ≤ i + m + 1) by omega, if_false]
          rw [ht1]; exact h₂
        · have hlt : p < i + m + 1 := by omega
          simp only [show p ≤ i + m + 1 by omega, show p + 1 ≤ i + m + 1 by omega, if_true,
            hpe, if_false]
          exact harc p hp hlt
      · intro hb
        rcases Bool.or_eq_true_iff.1 hb with hb | hb
        · obtain ⟨p, hp, hp', hl⟩ := hdesc hb
          exact ⟨p, hp, by omega, by simp [show p ≠ i + m + 1 by omega, hl]⟩
        · exact ⟨i + m + 1, by omega, by omega, by simp [hb]⟩

/-! ### Soundness of the closure criterion (by Ramsey's theorem) -/

/-- **The closure criterion implies size-change termination** (Lee, Jones and Ben-Amram,
Theorem 4; the direction a termination checker uses).  Proof by the infinite Ramsey theorem for
pairs, colouring `i < j` by the composition of the block `[i, j)`. -/
theorem sct_of_criterion {𝒢 : Finset (SCG n)} (hc : Criterion 𝒢) : SCT 𝒢 := by
  classical
  intro g hg
  obtain ⟨f, hf, G, hG⟩ := ramsey_pairs (fun i j => compR g i (j - i - 1))
  have hblock : ∀ k, compR g (f k) (f (k + 1) - f k - 1) = G :=
    fun k => hG k (k + 1) (Nat.lt_succ_self k)
  have hfk : ∀ k, f k < f (k + 1) := fun k => hf (Nat.lt_succ_self k)
  -- `G` lies in the closure and is idempotent
  have hGcl : InCl 𝒢 G := hblock 0 ▸ compR_inCl hg _ _
  have hidem : G.comp G = G := by
    have h02 := hG 0 2 (by norm_num)
    have hf01 : f 0 < f 1 := hfk 0
    have hf12 : f 1 < f 2 := hfk 1
    calc G.comp G = (compR g (f 0) (f 1 - f 0 - 1)).comp (compR g (f 1) (f 2 - f 1 - 1)) := by
          rw [hblock 0, hblock 1]
      _ = (compR g (f 0) (f 1 - f 0 - 1)).comp
            (compR g (f 0 + (f 1 - f 0 - 1) + 1) (f 2 - f 1 - 1)) := by
          congr 2; omega
      _ = compR g (f 0) ((f 1 - f 0 - 1) + (f 2 - f 1 - 1) + 1) := (compR_add _ _ _ _).symm
      _ = compR g (f 0) (f 2 - f 0 - 1) := by congr 1; omega
      _ = G := h02
  obtain ⟨x, hx⟩ := hc G hGcl hidem
  -- a path from `x` back to `x` with a descent in every block
  have hpath : ∀ k, ∃ (t : ℕ → Fin n) (l : ℕ → Bool), t (f k) = x ∧ t (f (k + 1)) = x ∧
      (∀ p, f k ≤ p → p < f (k + 1) → (t p, t (p + 1), l p) ∈ g p) ∧
      ∃ p, f k ≤ p ∧ p < f (k + 1) ∧ l p = true := by
    intro k
    have hk := hfk k
    have hmem : (x, x, true) ∈ compR g (f k) (f (k + 1) - f k - 1) := (hblock k).symm ▸ hx
    obtain ⟨t, l, h0, h1, harc, hdesc⟩ := compR_path g _ _ hmem
    have he : f k + (f (k + 1) - f k - 1) + 1 = f (k + 1) := by omega
    rw [he] at h1 harc hdesc
    exact ⟨t, l, h0, h1, harc, hdesc rfl⟩
  choose T L hT0 hT1 harc hdesc using hpath
  -- the block containing a position
  have hex : ∀ p, ∃ k, p < f (k + 1) := fun p => ⟨p, lt_of_lt_of_le (Nat.lt_succ_self p)
    (hf.id_le (p + 1))⟩
  let blk : ℕ → ℕ := fun p => Nat.find (hex p)
  have hblk_lt : ∀ p, p < f (blk p + 1) := fun p => Nat.find_spec (hex p)
  have hblk_ge : ∀ p, f 0 ≤ p → f (blk p) ≤ p := by
    intro p hp
    rcases h : blk p with _ | k
    · exact hp
    · have := Nat.find_min (hex p) (show k < blk p by omega)
      exact not_lt.1 this
  have hblk_eq : ∀ p k, f k ≤ p → p < f (k + 1) → blk p = k := by
    intro p k h1 h2
    have hle : blk p ≤ k := Nat.find_min' (hex p) h2
    by_contra hne
    have hlt : blk p + 1 ≤ k := by omega
    have := hf.monotone hlt
    have := hblk_lt p
    omega
  refine ⟨f 0, fun p => T (blk p) p, fun p => L (blk p) p, ?_, ?_⟩
  · intro p hp
    have hk1 := hblk_ge p hp
    have hk2 := hblk_lt p
    have harc' := harc (blk p) p hk1 hk2
    by_cases hnext : p + 1 < f (blk p + 1)
    · have : blk (p + 1) = blk p := hblk_eq (p + 1) (blk p) (by omega) hnext
      simp only [this]
      exact harc'
    · have hp1 : p + 1 = f (blk p + 1) := by omega
      have : blk (p + 1) = blk p + 1 := hblk_eq (p + 1) (blk p + 1) (by omega) (by
        rw [hp1]; exact hfk _)
      simp only [this]
      rw [hp1, hT0, ← hT1 (blk p), ← hp1]
      exact harc'
  · intro N
    obtain ⟨p, hp1, hp2, hl⟩ := hdesc N
    refine ⟨p, le_trans (hf.id_le N) hp1, le_trans (hf.monotone (Nat.zero_le N)) hp1, ?_⟩
    have : blk p = N := hblk_eq p N hp1 hp2
    simp only [this]
    exact hl


/-! ### Decidability of the closure criterion -/

/-- One saturation step of the closure computation. -/
def stepCl (𝒢 S : Finset (SCG n)) : Finset (SCG n) :=
  S ∪ 𝒢 ∪ (S ×ˢ S).image (fun p => p.1.comp p.2)

/-- The `k`-th approximation of the closure. -/
def iterCl (𝒢 : Finset (SCG n)) (k : ℕ) : Finset (SCG n) := (stepCl 𝒢)^[k] ∅

/-- **The composition closure, computed** (finitely many graphs, so the saturation stabilises
within `Fintype.card (SCG n)` steps). -/
def closureFS (𝒢 : Finset (SCG n)) : Finset (SCG n) := iterCl 𝒢 (Fintype.card (SCG n))

theorem iterCl_succ (𝒢 : Finset (SCG n)) (k : ℕ) :
    iterCl 𝒢 (k + 1) = stepCl 𝒢 (iterCl 𝒢 k) := Function.iterate_succ_apply' _ _ _

theorem subset_stepCl (𝒢 S : Finset (SCG n)) : S ⊆ stepCl 𝒢 S := fun _ h =>
  Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem iterCl_mono (𝒢 : Finset (SCG n)) {k l : ℕ} (h : k ≤ l) : iterCl 𝒢 k ⊆ iterCl 𝒢 l := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [iterCl_succ]; exact ih.trans (subset_stepCl _ _)

theorem inCl_of_mem_iterCl (𝒢 : Finset (SCG n)) :
    ∀ k G, G ∈ iterCl 𝒢 k → InCl 𝒢 G
  | 0, G, h => by simp [iterCl] at h
  | k + 1, G, h => by
      rw [iterCl_succ] at h
      simp only [stepCl, Finset.mem_union, Finset.mem_image, Finset.mem_product] at h
      rcases h with (h | h) | ⟨⟨G₁, G₂⟩, ⟨h₁, h₂⟩, rfl⟩
      · exact inCl_of_mem_iterCl 𝒢 k G h
      · exact .base h
      · exact .comp (inCl_of_mem_iterCl 𝒢 k G₁ h₁) (inCl_of_mem_iterCl 𝒢 k G₂ h₂)

theorem exists_mem_iterCl {𝒢 : Finset (SCG n)} {G : SCG n} (h : InCl 𝒢 G) :
    ∃ k, G ∈ iterCl 𝒢 k := by
  induction h with
  | base h => exact ⟨1, by rw [iterCl_succ]; simp [stepCl, h]⟩
  | @comp G H _ _ ihG ihH =>
      obtain ⟨a, ha⟩ := ihG
      obtain ⟨b, hb⟩ := ihH
      refine ⟨max a b + 1, ?_⟩
      rw [iterCl_succ]
      simp only [stepCl, Finset.mem_union, Finset.mem_image, Finset.mem_product]
      exact Or.inr ⟨⟨G, H⟩, ⟨iterCl_mono 𝒢 (le_max_left a b) ha,
        iterCl_mono 𝒢 (le_max_right a b) hb⟩, rfl⟩

/-- The saturation reaches a fixed point within `Fintype.card (SCG n)` steps. -/
theorem iterCl_stable (𝒢 : Finset (SCG n)) :
    ∃ j ≤ Fintype.card (SCG n), iterCl 𝒢 (j + 1) = iterCl 𝒢 j := by
  by_contra hne
  push Not at hne
  have hcard : ∀ k, k ≤ Fintype.card (SCG n) + 1 → k ≤ (iterCl 𝒢 k).card := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
        intro hk
        have hss : iterCl 𝒢 k ⊂ iterCl 𝒢 (k + 1) :=
          Finset.ssubset_iff_subset_ne.2 ⟨iterCl_mono 𝒢 (Nat.le_succ k),
            fun h => hne k (by omega) h.symm⟩
        have := Finset.card_lt_card hss
        have := ih (by omega)
        omega
  have h1 := hcard _ le_rfl
  have h2 := Finset.card_le_univ (iterCl 𝒢 (Fintype.card (SCG n) + 1))
  omega

theorem iterCl_subset_closureFS (𝒢 : Finset (SCG n)) (k : ℕ) :
    iterCl 𝒢 k ⊆ closureFS 𝒢 := by
  obtain ⟨j, hj, hfix⟩ := iterCl_stable 𝒢
  have hconst : ∀ m, iterCl 𝒢 (j + m) = iterCl 𝒢 j := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [← Nat.add_assoc, iterCl_succ, ih, ← iterCl_succ, hfix]
  have hN : closureFS 𝒢 = iterCl 𝒢 j := by
    unfold closureFS
    rw [show Fintype.card (SCG n) = j + (Fintype.card (SCG n) - j) by omega, hconst]
  rw [hN, ← hconst k]
  exact iterCl_mono 𝒢 (by omega)

/-- **The computed closure is the composition closure.** -/
theorem mem_closureFS_iff {𝒢 : Finset (SCG n)} {G : SCG n} : G ∈ closureFS 𝒢 ↔ InCl 𝒢 G := by
  constructor
  · exact inCl_of_mem_iterCl 𝒢 _ G
  · intro h
    obtain ⟨k, hk⟩ := exists_mem_iterCl h
    exact iterCl_subset_closureFS 𝒢 k hk

/-- The closure criterion as a finite check on the computed closure. -/
theorem criterion_iff_finite (𝒢 : Finset (SCG n)) :
    Criterion 𝒢 ↔ ∀ G ∈ closureFS 𝒢, G.comp G = G → ∃ x, (x, x, true) ∈ G := by
  simp only [Criterion, mem_closureFS_iff]

/-- **The closure criterion is decidable.** -/
instance Criterion.decidable (𝒢 : Finset (SCG n)) : Decidable (Criterion 𝒢) :=
  decidable_of_iff _ (criterion_iff_finite 𝒢).symm

/-- **Size-change termination checker**: if the (decidable) closure criterion holds, the set of
graphs is size-change terminating. -/
theorem sct_of_decide (𝒢 : Finset (SCG n)) (h : decide (Criterion 𝒢) = true) : SCT 𝒢 :=
  sct_of_criterion (of_decide_eq_true h)

/-! ### Completeness of the closure criterion, and decidability of SCT -/

theorem compR_congr {g g' : ℕ → SCG n} {i i' : ℕ} :
    ∀ m, (∀ q, q ≤ m → g (i + q) = g' (i' + q)) → compR g i m = compR g' i' m
  | 0, h => by simpa [compR] using h 0 le_rfl
  | m + 1, h => by
      simp only [compR]
      rw [compR_congr m (fun q hq => h q (by omega))]
      have := h (m + 1) le_rfl
      rw [show i + m + 1 = i + (m + 1) by omega, show i' + m + 1 = i' + (m + 1) by omega, this]

/-- A path through a block gives an arc of the block composition, strict if the path has a
descent. -/
theorem compR_arc (g : ℕ → SCG n) (i : ℕ) (t : ℕ → Fin n) (l : ℕ → Bool) :
    ∀ m, (∀ p, i ≤ p → p < i + m + 1 → (t p, t (p + 1), l p) ∈ g p) →
      ∃ b, (t i, t (i + m + 1), b) ∈ compR g i m ∧
        ((∃ p, i ≤ p ∧ p < i + m + 1 ∧ l p = true) → b = true)
  | 0, h => ⟨l i, by simpa [compR] using h i le_rfl (by omega), by
      rintro ⟨p, hp1, hp2, hl⟩; obtain rfl : p = i := by omega
      exact hl⟩
  | m + 1, h => by
      obtain ⟨b₁, hb₁, hd⟩ := compR_arc g i t l m (fun p hp1 hp2 => h p hp1 (by omega))
      refine ⟨b₁ || l (i + m + 1), ?_, ?_⟩
      · simp only [compR]
        rw [show i + (m + 1) + 1 = i + m + 1 + 1 by omega]
        exact SCG.mem_comp.2 ⟨_, _, _, hb₁, h _ (by omega) (by omega), rfl⟩
      · rintro ⟨p, hp1, hp2, hl⟩
        by_cases hpe : p = i + m + 1
        · subst hpe; simp [hl]
        · simp [hd ⟨p, hp1, by omega, hl⟩]

/-- Every graph of the closure is the composition of a finite block of graphs of `𝒢`. -/
theorem InCl.realize {𝒢 : Finset (SCG n)} {G : SCG n} (hG : InCl 𝒢 G) :
    ∃ (L : ℕ) (h : ℕ → SCG n), 0 < L ∧ (∀ k, h k ∈ 𝒢) ∧ compR h 0 (L - 1) = G := by
  induction hG with
  | @base G hG => exact ⟨1, fun _ => G, by norm_num, fun _ => hG, rfl⟩
  | @comp G H _ _ ihG ihH =>
      obtain ⟨L₁, h₁, hL₁, hh₁, hc₁⟩ := ihG
      obtain ⟨L₂, h₂, hL₂, hh₂, hc₂⟩ := ihH
      refine ⟨L₁ + L₂, fun k => if k < L₁ then h₁ k else h₂ (k - L₁), by omega, ?_, ?_⟩
      · intro k; dsimp only; split_ifs; exacts [hh₁ k, hh₂ _]
      · rw [show L₁ + L₂ - 1 = (L₁ - 1) + (L₂ - 1) + 1 by omega, compR_add, ← hc₁, ← hc₂]
        congr 1
        · exact compR_congr _ fun q hq => by simp [show q < L₁ by omega]
        · exact compR_congr _ fun q hq => by
            simp only [show ¬ (0 + (L₁ - 1) + 1 + q < L₁) by omega, if_false]
            congr 1; omega

/-- **Completeness of the closure criterion**: size-change termination implies the criterion
(every idempotent graph of the closure has a strict self-arc).  No Ramsey argument is needed:
an idempotent graph is unfolded into a periodic multipath and the descending thread is cut at
two block boundaries where it visits the same parameter. -/
theorem criterion_of_sct {𝒢 : Finset (SCG n)} (hs : SCT 𝒢) : Criterion 𝒢 := by
  intro G hG hidem
  obtain ⟨L, h, hL, hh, hc⟩ := hG.realize
  let g : ℕ → SCG n := fun k => h (k % L)
  have hg : ∀ k, g k ∈ 𝒢 := fun k => hh _
  have hblock : ∀ j, compR g (j * L) (L - 1) = G := by
    intro j
    rw [← hc]
    refine compR_congr _ fun q hq => ?_
    simp only [g, zero_add]
    congr 1
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hblocks : ∀ j k, compR g (j * L) (k * L + L - 1) = G := by
    intro j k
    induction k with
    | zero => simpa using hblock j
    | succ k ih =>
        rw [show (k + 1) * L + L - 1 = (k * L + L - 1) + (L - 1) + 1 by
              rw [Nat.succ_mul]; omega,
          compR_add, ih,
          show j * L + (k * L + L - 1) + 1 = (j + k + 1) * L by
              rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega,
          hblock, hidem]
  obtain ⟨i, t, l, harc, hdesc⟩ := hs g hg
  obtain ⟨x, hx⟩ := infinite_fiber (Set.infinite_univ (α := ℕ)) (fun j => t ((i + j) * L))
  obtain ⟨j₁, hj₁⟩ := hx.nonempty
  obtain ⟨p, hp1, hp2, hlp⟩ := hdesc ((i + j₁) * L)
  obtain ⟨j₂, hj₂, hj₂p⟩ := hx.exists_gt p
  simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and] at hj₁ hj₂
  have hLj : ∀ j, j ≤ j * L := fun j => Nat.le_mul_of_pos_right j hL
  have hlt : j₁ < j₂ := by have := hLj (i + j₁); omega
  have hiL : i ≤ (i + j₁) * L := by have := hLj (i + j₁); omega
  have hend : (i + j₁) * L + ((j₂ - j₁ - 1) * L + L - 1) + 1 = (i + j₂) * L := by
    have h1 : (j₂ - j₁ - 1) * L + L = (j₂ - j₁) * L := by
      rw [← Nat.succ_mul]; congr 1; omega
    have h2 : (i + j₁) * L + (j₂ - j₁) * L = (i + j₂) * L := by
      rw [← Nat.add_mul]; congr 1; omega
    have h3 : 0 < (j₂ - j₁ - 1) * L + L := by omega
    omega
  obtain ⟨b, hb, hbd⟩ := compR_arc g ((i + j₁) * L) t l ((j₂ - j₁ - 1) * L + L - 1)
    (fun q hq1 _ => harc q (le_trans hiL hq1))
  rw [hend, hblocks, hj₁, hj₂] at hb
  have hp3 : p < (i + j₂) * L := by have := hLj (i + j₂); omega
  rw [hbd ⟨p, hp1, by rw [hend]; exact hp3, hlp⟩] at hb
  exact ⟨x, hb⟩

/-- **The closure criterion characterises size-change termination.** -/
theorem sct_iff_criterion (𝒢 : Finset (SCG n)) : SCT 𝒢 ↔ Criterion 𝒢 :=
  ⟨criterion_of_sct, sct_of_criterion⟩

/-- **Size-change termination is decidable.** -/
instance SCT.decidable (𝒢 : Finset (SCG n)) : Decidable (SCT 𝒢) :=
  decidable_of_iff _ (sct_iff_criterion 𝒢).symm

end SizeChange
