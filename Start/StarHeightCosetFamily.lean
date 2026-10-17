import Start.StarHeightCommutative
import Start.StarHeightDFAReturns

/-!
# Assembling height one from a separating family of automata

A finite monoid `M`, a morphism `T : FreeMonoid α →* M` and a family of *observers*
`ob i : M → X` that jointly separate the elements of `M`.  If every observed language
`{w | ob i (T w) = x}` has generalized star height at most one, then so does every language
`{w | T w ∈ F}` recognized by `T`:

* `height_one_of_separating_family`: the general statement (`{w | T w ∈ F}` is the finite union
  over `g ∈ F` of the finite intersection over `i` of the observed languages);
* `height_one_of_three_observers`: the three-observer form used in applications;
* `height_one_of_coset_family`: the coset form.  For a family of subgroups `H i` of a finite
  group `G` whose intersection is trivial, the observers are the right cosets `H i * ({g} : Set G)`:
  `g ↦ (H i g)ᵢ` is injective, so it is enough that every coset language has height at most one.

The bridge from an automaton to an observer:

* `obs_runQ`: if `ob (g * T x) = δ (ob g) x` for every `g` and every letter `x`, then
  `ob (T w) = runQ δ (ob 1) w` is the state reached by the automaton `δ`;
* `stab_coset_eq_runQ`: for a point stabilizer `H = stabilizer G p` of an action of `G` on `X`,
  the coset of `T w` is determined by `(T w)⁻¹ • p`, the state of the automaton
  `δ q x = (T x)⁻¹ • q` started at `p`.
-/

namespace GeneralizedStarHeight

universe u

variable {Alphabet : Type u}

/-! ### Separating families of observers -/

section Family

variable {M : Type*} [Monoid M] [Fintype M] {X : Type*}

/-- **A separating family of height-one observers gives height one.** -/
theorem height_one_of_separating_family (T : FreeMonoid Alphabet →* M) {ι : Type*} [Fintype ι]
    (ob : ι → M → X) (hsep : ∀ u v : M, (∀ i, ob i u = ob i v) → u = v)
    (hgood : ∀ (i : ι) (x : X), HasHeightAtMost {w | ob i (T (FreeMonoid.ofList w)) = x} 1)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      ⨆ g : F, ⨅ i, ({w | ob i (T (FreeMonoid.ofList w)) = ob i g.1} : Language Alphabet) := by
    ext w
    constructor
    · intro hw
      exact Language.mem_iSup.mpr
        ⟨⟨_, hw⟩, HasHeightAtMost.mem_iInf_lang.mpr fun _ => rfl⟩
    · intro hw
      obtain ⟨g, hg⟩ := Language.mem_iSup.mp hw
      have hEq := hsep _ _ fun i => HasHeightAtMost.mem_iInf_lang.mp hg i
      show T (FreeMonoid.ofList w) ∈ F
      rw [hEq]
      exact g.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun g => HasHeightAtMost.iInf _ fun i => hgood i _

/-- **Three separating height-one observers give height one.** -/
theorem height_one_of_three_observers {X Y Z : Type*} (T : FreeMonoid Alphabet →* M)
    (f : M → X) (g : M → Y) (h : M → Z)
    (hsep : ∀ u v : M, f u = f v → g u = g v → h u = h v → u = v)
    (hf : ∀ x, HasHeightAtMost {w | f (T (FreeMonoid.ofList w)) = x} 1)
    (hg : ∀ y, HasHeightAtMost {w | g (T (FreeMonoid.ofList w)) = y} 1)
    (hh : ∀ z, HasHeightAtMost {w | h (T (FreeMonoid.ofList w)) = z} 1)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      ⨆ d : F, (({w | f (T (FreeMonoid.ofList w)) = f d.1} ⊓
        {w | g (T (FreeMonoid.ofList w)) = g d.1}) ⊓
          {w | h (T (FreeMonoid.ofList w)) = h d.1}) := by
    ext w
    constructor
    · intro hw
      exact Language.mem_iSup.mpr ⟨⟨_, hw⟩, ⟨⟨rfl, rfl⟩, rfl⟩⟩
    · intro hw
      obtain ⟨d, ⟨⟨h1, h2⟩, h3⟩⟩ := Language.mem_iSup.mp hw
      show T (FreeMonoid.ofList w) ∈ F
      rw [hsep _ _ h1 h2 h3]
      exact d.2
  rw [heq]
  exact HasHeightAtMost.iSup _ fun d => ((hf _).inter (hg _)).inter (hh _)

end Family

/-! ### Coset families -/

section Coset

open scoped Pointwise

variable {G : Type*} [Group G]

lemma mem_coset_iff (H : Subgroup G) (u v : G) : u ∈ (H : Set G) * ({v} : Set G) ↔ u * v⁻¹ ∈ H := by
  rw [Set.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst hb
    simpa using ha
  · intro h
    exact ⟨u * v⁻¹, h, v, Set.mem_singleton _, by group⟩

lemma coset_eq_iff (H : Subgroup G) (u v : G) :
    (H : Set G) * ({u} : Set G) = (H : Set G) * ({v} : Set G) ↔ u ∈ (H : Set G) * ({v} : Set G) := by
  constructor
  · intro h
    have hu : u ∈ (H : Set G) * ({u} : Set G) := (mem_coset_iff H u u).mpr (by simp)
    rwa [h] at hu
  · intro h
    rw [mem_coset_iff] at h
    ext x
    rw [mem_coset_iff, mem_coset_iff]
    constructor
    · intro hx
      have : x * v⁻¹ = (x * u⁻¹) * (u * v⁻¹) := by group
      rw [this]
      exact H.mul_mem hx h
    · intro hx
      have : x * u⁻¹ = (x * v⁻¹) * (u * v⁻¹)⁻¹ := by group
      rw [this]
      exact H.mul_mem hx (H.inv_mem h)

variable [Fintype G]

/-- **A family of subgroups meeting in `{1}`, all of whose coset languages have height at most
one, gives height at most one for every recognized language.** -/
theorem height_one_of_coset_family (T : FreeMonoid Alphabet →* G) {ι : Type*} [Fintype ι]
    (H : ι → Subgroup G)
    (hgood : ∀ i (g : G),
      HasHeightAtMost {w | (T (FreeMonoid.ofList w) : G) ∈ (H i : Set G) * ({g} : Set G)} 1)
    (hD : ⨅ i, H i = ⊥) (F : Set G) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  refine height_one_of_separating_family T (X := Set G) (fun i u => (H i : Set G) * ({u} : Set G)) ?_ ?_ F
  · intro u v huv
    have hmem : u * v⁻¹ ∈ ⨅ i, H i :=
      Subgroup.mem_iInf.mpr fun i => (mem_coset_iff (H i) u v).mp
        ((coset_eq_iff (H i) u v).mp (huv i))
    rw [hD, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  · intro i x
    by_cases hx : ∃ g : G, (H i : Set G) * ({g} : Set G) = x
    · obtain ⟨g, rfl⟩ := hx
      have heq : {w : List Alphabet |
            (H i : Set G) * ({T (FreeMonoid.ofList w)} : Set G) = (H i : Set G) * ({g} : Set G)} =
          {w : List Alphabet | T (FreeMonoid.ofList w) ∈ (H i : Set G) * ({g} : Set G)} := by
        ext w
        exact coset_eq_iff (H i) _ g
      rw [show ({w : List Alphabet |
          (H i : Set G) * ({T (FreeMonoid.ofList w)} : Set G) = (H i : Set G) * ({g} : Set G)} : Language Alphabet) =
          {w | T (FreeMonoid.ofList w) ∈ (H i : Set G) * ({g} : Set G)} from heq]
      exact hgood i g
    · have hempty : ({w : List Alphabet |
          (H i : Set G) * ({T (FreeMonoid.ofList w)} : Set G) = x} : Language Alphabet) =
          (0 : Language Alphabet) := by
        ext w
        constructor
        · intro hw
          exact absurd ⟨T (FreeMonoid.ofList w), hw⟩ hx
        · intro hw
          exact absurd hw (by simp [Language.zero_def])
      rw [hempty]
      exact HasHeightAtMost.zero 1

end Coset

/-! ### The bridge from an automaton -/

section Bridge

variable {M : Type*} [Monoid M] {X : Type*}

/-- **An observer that is driven by an automaton.** -/
lemma obs_runQ (T : FreeMonoid Alphabet →* M) (ob : M → X) (δ : X → Alphabet → X)
    (hstep : ∀ (g : M) (x : Alphabet), ob (g * T (FreeMonoid.of x)) = δ (ob g) x)
    (w : List Alphabet) :
    ob (T (FreeMonoid.ofList w)) = DFAReturn.runQ δ (ob 1) w := by
  induction w using List.reverseRecOn with
  | nil =>
      rw [show FreeMonoid.ofList ([] : List Alphabet) = 1 from rfl, map_one]
      rfl
  | append_singleton w x ih =>
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, hstep, ih,
        DFAReturn.runQ_append_single]

end Bridge

section StabBridge

open scoped Pointwise

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

lemma inv_smul_runQ (T : FreeMonoid Alphabet →* G) (p : X) (w : List Alphabet) :
    (T (FreeMonoid.ofList w))⁻¹ • p =
      DFAReturn.runQ (fun q (x : Alphabet) => (T (FreeMonoid.of x))⁻¹ • q) p w := by
  have h := obs_runQ T (fun u : G => u⁻¹ • p)
    (fun q (x : Alphabet) => (T (FreeMonoid.of x))⁻¹ • q)
    (fun g x => by rw [mul_inv_rev, mul_smul]) w
  simpa using h

/-- **The coset of `T w` modulo a point stabilizer is the state of the inverse automaton.** -/
lemma stab_coset_eq_runQ (T : FreeMonoid Alphabet →* G) (p : X) (g : G) :
    {w : List Alphabet |
        T (FreeMonoid.ofList w) ∈ ((MulAction.stabilizer G p : Subgroup G) : Set G) * ({g} : Set G)} =
      {w | DFAReturn.runQ (fun q (x : Alphabet) => (T (FreeMonoid.of x))⁻¹ • q) p w = g⁻¹ • p} := by
  ext w
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, mem_coset_iff, MulAction.mem_stabilizer_iff,
    ← inv_smul_runQ]
  constructor
  · intro h
    rw [mul_smul] at h
    have h2 := congrArg (fun y => (T (FreeMonoid.ofList w))⁻¹ • y) h
    simpa [inv_smul_smul] using h2.symm
  · intro h
    rw [mul_smul, ← h, smul_inv_smul]

end StabBridge

end GeneralizedStarHeight
