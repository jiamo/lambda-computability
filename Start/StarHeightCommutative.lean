import Start.StarHeightSingleSplit

/-!
# Generalized star height two for commutative monoids, through a single split

* `singleSplit_of_fiber_height`: if every fiber of `T` has height at most one, then
  `SingleSplit T` holds, with the first-return code to `1` as `E`, a one-point state set and
  the tests `P () = E`, `Q () = 1`.
* `fiber_height_one_of_comm`: every fiber of a morphism into a finite commutative monoid has
  height at most one (letter counts up to an eventually periodic threshold).
* `singleSplit_of_comm` and `height_two_of_comm`: the single-split hypothesis, and hence
  height at most two, for every language recognized by a finite commutative monoid.
* `comm_class_nontrivial_subgroup`: the class contains `Multiplicative (ZMod 2)`, which has a
  nontrivial subgroup.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

namespace HasHeightAtMost

variable {Alphabet : Type u} {n : ℕ}

lemma top (n : ℕ) : HasHeightAtMost (⊤ : Language Alphabet) n := by
  have h := (zero (Alphabet := Alphabet) n).compl
  have he : ((0 : Language Alphabet)ᶜ) = ⊤ := by
    ext w
    change w ∉ (0 : Language Alphabet) ↔ True
    simp
  rwa [he] at h

lemma mem_iInf_lang {ι : Type*} {L : ι → Language Alphabet} {w : List Alphabet} :
    w ∈ (⨅ i, L i) ↔ ∀ i, w ∈ L i :=
  Set.mem_iInter

lemma iInf {ι : Type*} [Finite ι] (L : ι → Language Alphabet)
    (h : ∀ i, HasHeightAtMost (L i) n) : HasHeightAtMost (⨅ i, L i) n := by
  have h' := (HasHeightAtMost.iSup (fun i => (L i)ᶜ) (fun i => (h i).compl)).compl
  have he : (⨆ i, (L i)ᶜ)ᶜ = ⨅ i, L i := by
    ext w
    constructor
    · intro hw
      exact mem_iInf_lang.mpr (fun i => by_contra fun hi => hw (Language.mem_iSup.mpr ⟨i, hi⟩))
    · intro hw hw'
      obtain ⟨i, hi⟩ := Language.mem_iSup.mp hw'
      exact hi (mem_iInf_lang.mp hw i)
  rwa [he] at h'

end HasHeightAtMost

section FirstReturn

variable {Alphabet : Type u} {M : Type} [Monoid M]

/-- The fiber of `T` over `d`, as a language. -/
def fiberLang (T : FreeMonoid Alphabet →* M) (d : M) : Language Alphabet :=
  {w | T (FreeMonoid.ofList w) = d}

/-- The first-return code of `T` to `1`. -/
def firstReturn (T : FreeMonoid Alphabet →* M) : Language Alphabet :=
  {w | w ≠ [] ∧ T (FreeMonoid.ofList w) = 1 ∧
    ∀ p, p <+: w → p ≠ [] → p ≠ w → T (FreeMonoid.ofList p) ≠ 1}

lemma firstReturn_prefixCode (T : FreeMonoid Alphabet →* M) : PrefixCode (firstReturn T) := by
  refine ⟨fun h => h.1 rfl, ?_⟩
  intro e he f hf hef
  by_contra hne
  exact hf.2.2 e hef he.1 hne he.2.1

lemma firstReturn_eq (T : FreeMonoid Alphabet →* M) :
    firstReturn T = (fiberLang T 1 ⊓ (1 : Language Alphabet)ᶜ) ⊓
      ((fiberLang T 1 ⊓ (1 : Language Alphabet)ᶜ) * (1 : Language Alphabet)ᶜ)ᶜ := by
  ext w
  have hone : ∀ v : List Alphabet, v ∈ (1 : Language Alphabet) ↔ v = [] := Language.mem_one
  constructor
  · rintro ⟨hne, h1, hp⟩
    refine ⟨⟨h1, fun h => hne ((hone w).mp h)⟩, ?_⟩
    intro hm
    obtain ⟨p, ⟨hp1, hpne⟩, s, hsne, hps⟩ := Language.mem_mul.mp hm
    have hpne' : p ≠ [] := fun h => hpne ((hone p).mpr h)
    have hsne' : s ≠ [] := fun h => hsne ((hone s).mpr h)
    subst hps
    exact hp p (List.prefix_append p s) hpne' (by simpa using hsne') hp1
  · rintro ⟨⟨h1, hne⟩, hp⟩
    refine ⟨fun h => hne ((hone w).mpr h), h1, ?_⟩
    intro p ⟨s, hs⟩ hpne hpw hp1
    apply hp
    refine Language.mem_mul.mpr ⟨p, ⟨hp1, fun h => hpne ((hone p).mp h)⟩, s, ?_, hs⟩
    intro h
    have hs0 : s = [] := (hone s).mp h
    subst hs0
    exact hpw (by simpa using hs)

lemma firstReturn_T {T : FreeMonoid Alphabet →* M} :
    ∀ es : List (List Alphabet), AllIn (firstReturn T) es →
      T (FreeMonoid.ofList es.flatten) = 1
  | [], _ => by simp
  | e :: es, h => by
    rw [List.flatten_cons, FreeMonoid.ofList_append, map_mul, (h e (by simp)).2.1,
      firstReturn_T es (fun a ha => h a (by simp [ha])), one_mul]

lemma graph_unit_eq_kstar (E : Language Alphabet) (x y : Unit) :
    graph E (fun _ _ => ()) x y = E∗ := by
  ext w
  rw [Language.mem_kstar]
  constructor
  · rintro ⟨es, he, rfl, _⟩
    exact ⟨es, rfl, he⟩
  · rintro ⟨es, rfl, he⟩
    exact ⟨es, he, rfl, rfl⟩

/-- If every fiber of `T` has height at most one, the single-split hypothesis holds. -/
theorem singleSplit_of_fiber_height {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M)
    (hfib : ∀ d, HasHeightAtMost {w | T (FreeMonoid.ofList w) = d} 1) : SingleSplit T := by
  classical
  have hE : PrefixCode (firstReturn T) := firstReturn_prefixCode T
  have hEh : HasHeightAtMost (firstReturn T) 1 := by
    rw [firstReturn_eq]
    have h1 := (hfib 1).inter (HasHeightAtMost.one (Alphabet := Alphabet) 1).compl
    exact h1.inter (h1.concat (HasHeightAtMost.one 1).compl).compl
  refine ⟨firstReturn T, Unit, inferInstance, fun _ _ => (), fun _ => firstReturn T,
    fun _ => 1, hE, hEh, ?_, ?_, ?_, fun _ => hEh, fun _ => HasHeightAtMost.one 1, ?_⟩
  · intro d
    have heq : ({w | w ∈ remainder (firstReturn T) ∧ T (FreeMonoid.ofList w) = d} :
        Language Alphabet) = (firstReturn T * ⊤)ᶜ ⊓ {w | T (FreeMonoid.ofList w) = d} := by
      rw [← remainder_eq]
      rfl
    rw [heq]
    exact (hEh.concat (HasHeightAtMost.top 1)).compl.inter (hfib d)
  · intro x y es u v hes hu hv huv
    rw [Language.mem_one] at hv
    subst hv
    rw [List.append_nil] at huv
    cases es with
    | nil =>
      exfalso
      have := List.eq_nil_of_prefix_nil huv
      exact hu.1 this
    | cons e fs =>
      refine ⟨e, fs, rfl, ?_, rfl⟩
      rw [List.append_nil]
      have heE := hes e (by simp)
      have hep : e <+: (e :: fs).flatten := List.prefix_append _ _
      rcases List.prefix_or_prefix_of_prefix huv hep with h | h
      · exact hE.2 u hu e heE h
      · exact (hE.2 e heE u hu h).symm
  · intro e he _ x
    exact Language.mem_mul.mpr ⟨e, he, [], (Language.mem_one _).mpr rfl, List.append_nil e⟩
  · intro d
    refine ⟨if d = 1 then Set.univ else ∅, ?_⟩
    ext w
    constructor
    · rintro ⟨hw, hT⟩
      have hd : d = 1 := by
        obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hw
        exact hT.symm.trans (firstReturn_T es hes)
      subst hd
      have hg : w ∈ graph (firstReturn T) (fun _ _ => ()) () () := by
        rw [graph_unit_eq_kstar]
        exact hw
      exact Language.mem_iSup.mpr ⟨((), (), (), ()),
        Language.mem_iSup.mpr ⟨by simp, ⟨hg, hg⟩⟩⟩
    · intro h
      obtain ⟨r, hr⟩ := Language.mem_iSup.mp h
      obtain ⟨hrR, hw⟩ := Language.mem_iSup.mp hr
      by_cases hd : d = 1
      · subst hd
        have hw1 := hw.1
        rw [graph_unit_eq_kstar] at hw1
        refine ⟨hw1, ?_⟩
        obtain ⟨es, rfl, hes⟩ := Language.mem_kstar.mp hw1
        exact firstReturn_T es hes
      · simp [hd] at hrR

end FirstReturn

section Counting

variable {Alphabet : Type u} [DecidableEq Alphabet]

/-- Words containing the letter `a` exactly `k` times. -/
def countIs (a : Alphabet) (k : ℕ) : Language Alphabet := {w | w.count a = k}

/-- Words containing `a` exactly `p` times and ending with `a`. -/
def countBlock (a : Alphabet) (p : ℕ) : Language Alphabet :=
  {w | w.count a = p ∧ ∃ v, w = v ++ [a]}

lemma exists_split_count (a : Alphabet) :
    ∀ (w : List Alphabet) (k : ℕ), 0 < k → k ≤ w.count a →
      ∃ y z, w = y ++ z ∧ y.count a = k ∧ ∃ v, y = v ++ [a]
  | [], k, hk, hkc => by simp at hkc; omega
  | b :: w, k, hk, hkc => by
    by_cases hb : b = a
    · subst hb
      by_cases hk1 : k = 1
      · subst hk1
        exact ⟨[b], w, rfl, by simp, [], rfl⟩
      · rw [List.count_cons_self] at hkc
        obtain ⟨y, z, rfl, hy, v, rfl⟩ := exists_split_count b w (k - 1) (by omega) (by omega)
        refine ⟨b :: (v ++ [b]), z, rfl, ?_, b :: v, rfl⟩
        rw [List.count_cons_self, hy]
        omega
    · rw [List.count_cons_of_ne hb] at hkc
      obtain ⟨y, z, rfl, hy, v, rfl⟩ := exists_split_count a w k hk hkc
      refine ⟨b :: (v ++ [a]), z, rfl, ?_, b :: v, rfl⟩
      rw [List.count_cons_of_ne hb, hy]

lemma countIs_zero_eq (a : Alphabet) :
    countIs a 0 = (⊤ * {[a]} * ⊤ : Language Alphabet)ᶜ := by
  ext w
  change w.count a = 0 ↔ w ∉ (⊤ * {[a]} * ⊤ : Language Alphabet)
  rw [List.count_eq_zero]
  constructor
  · rintro h ⟨xy, ⟨x, -, y, hy, rfl⟩, z, -, rfl⟩
    obtain rfl : y = [a] := hy
    exact h (by simp)
  · intro h ha
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
    exact h ⟨s ++ [a], ⟨s, trivial, [a], rfl, rfl⟩, t, trivial, by simp⟩

lemma countIs_succ_eq (a : Alphabet) (k : ℕ) :
    countIs a (k + 1) = countIs a 0 * {[a]} * countIs a k := by
  ext w
  constructor
  · intro hw
    change w.count a = k + 1 at hw
    obtain ⟨y, z, rfl, hy, v, rfl⟩ := exists_split_count a w 1 (by omega) (by omega)
    rw [List.count_append, hy] at hw
    have hv : v.count a = 0 := by
      rw [List.count_append, List.count_singleton_self] at hy
      omega
    exact Language.mem_mul.mpr ⟨v ++ [a], Language.mem_mul.mpr ⟨v, hv, [a], rfl, rfl⟩, z,
      (by change z.count a = k; omega), rfl⟩
  · intro h
    obtain ⟨xy, hxy, z, hz, rfl⟩ := Language.mem_mul.mp h
    obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp hxy
    obtain rfl : y = [a] := hy
    change x.count a = 0 at hx
    change z.count a = k at hz
    change (x ++ [a] ++ z).count a = k + 1
    rw [List.count_append, List.count_append, hx, hz, List.count_singleton_self]
    omega

lemma countIs_zero_height (a : Alphabet) : HasHeightAtMost (countIs a 0) 0 := by
  rw [countIs_zero_eq]
  exact (((HasHeightAtMost.top 0).concat (HasHeightAtMost.singleton [a] 0)).concat
    (HasHeightAtMost.top 0)).compl

lemma countIs_height (a : Alphabet) (k : ℕ) : HasHeightAtMost (countIs a k) 0 := by
  induction k with
  | zero => exact countIs_zero_height a
  | succ k ih =>
    rw [countIs_succ_eq]
    exact ((countIs_zero_height a).concat (HasHeightAtMost.singleton [a] 0)).concat ih

lemma countBlock_height (a : Alphabet) (p : ℕ) : HasHeightAtMost (countBlock a p) 0 := by
  cases p with
  | zero =>
    have : countBlock a 0 = 0 := by
      ext w
      constructor
      · rintro ⟨h, v, rfl⟩
        simp at h
      · intro h
        exact h.elim
    rw [this]
    exact HasHeightAtMost.zero 0
  | succ p =>
    have : countBlock a (p + 1) = countIs a p * {[a]} := by
      ext w
      constructor
      · rintro ⟨hw, v, rfl⟩
        refine Language.mem_mul.mpr ⟨v, ?_, [a], rfl, rfl⟩
        change v.count a = p
        rw [List.count_append, List.count_singleton_self] at hw
        omega
      · intro h
        obtain ⟨x, hx, z, hz, rfl⟩ := Language.mem_mul.mp h
        obtain rfl : z = [a] := hz
        change x.count a = p at hx
        refine ⟨?_, x, rfl⟩
        rw [List.count_append, List.count_singleton_self, hx]
    rw [this]
    exact (countIs_height a p).concat (HasHeightAtMost.singleton [a] 0)

lemma mem_countBlock_kstar (a : Alphabet) {p : ℕ} (hp : 0 < p) (w : List Alphabet) :
    w ∈ (countBlock a p)∗ ↔ p ∣ w.count a ∧ (w = [] ∨ ∃ v, w = v ++ [a]) := by
  constructor
  · intro hw
    obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.mp hw
    clear hw
    induction S with
    | nil => simp
    | cons y S ih =>
      have hy := hS y (by simp)
      obtain ⟨hdvd, hend⟩ := ih (fun b hb => hS b (by simp [hb]))
      obtain ⟨hyc, v, rfl⟩ := hy
      refine ⟨?_, Or.inr ?_⟩
      · rw [List.flatten_cons, List.count_append, hyc]
        exact dvd_add dvd_rfl hdvd
      · rcases hend with h | ⟨u, hu⟩
        · exact ⟨v, by rw [List.flatten_cons, h, List.append_nil]⟩
        · exact ⟨v ++ [a] ++ u, by rw [List.flatten_cons, hu]; simp only [List.append_assoc]⟩
  · rintro ⟨⟨j, hj⟩, hend⟩
    induction j generalizing w with
    | zero =>
      rcases hend with rfl | ⟨v, rfl⟩
      · exact Language.nil_mem_kstar _
      · simp at hj
    | succ j ih =>
      have hle : p ≤ w.count a := by rw [hj]; nlinarith
      obtain ⟨y, z, rfl, hy, v, rfl⟩ := exists_split_count a w p hp hle
      rw [List.count_append, hy] at hj
      have hz : z.count a = p * j := by rw [Nat.mul_succ] at hj; omega
      have hzend : z = [] ∨ ∃ u, z = u ++ [a] := by
        rcases z.eq_nil_or_concat' with h | ⟨L, b, rfl⟩
        · exact Or.inl h
        · rcases hend with h | ⟨u, hu⟩
          · simp at h
          · have hu' : (v ++ [a] ++ L) ++ [b] = u ++ [a] := by
              rw [← hu]
              simp only [List.append_assoc]
            have hba := (List.append_inj' hu' rfl).2
            simp only [List.cons.injEq, and_true] at hba
            exact Or.inr ⟨L, by rw [hba]⟩
      have hzs := ih z hzend hz
      obtain ⟨S, hS, hSm⟩ := Language.mem_kstar.mp hzs
      apply Language.mem_kstar.mpr
      refine ⟨(v ++ [a]) :: S, by rw [List.flatten_cons, hS], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hy, v, rfl⟩
      · exact hSm b hb

lemma countMod_eq (a : Alphabet) {p : ℕ} (hp : 0 < p) (c : ℕ) (hc : c < p) :
    ({w | w.count a % p = c} : Language Alphabet) = (countBlock a p)∗ * countIs a c := by
  ext w
  constructor
  · intro hw
    change w.count a % p = c at hw
    by_cases h0 : w.count a = c
    · exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, w, h0, rfl⟩
    · have hle : c < w.count a := by
        have := Nat.mod_le (w.count a) p
        omega
      obtain ⟨y, z, hyz, hy, v, rfl⟩ :=
        exists_split_count a w (w.count a - c) (by omega) (by omega)
      have hcount : w.count a = (v ++ [a]).count a + z.count a := by
        rw [hyz, List.count_append]
      have hzc : z.count a = c := by omega
      refine Language.mem_mul.mpr ⟨v ++ [a],
        (mem_countBlock_kstar a hp _).mpr ⟨?_, Or.inr ⟨v, rfl⟩⟩, z, hzc, hyz.symm⟩
      rw [hy]
      have := Nat.dvd_sub_mod (n := p) (w.count a)
      rwa [hw] at this
  · intro h
    obtain ⟨y, hy, z, hz, rfl⟩ := Language.mem_mul.mp h
    obtain ⟨⟨j, hj⟩, -⟩ := (mem_countBlock_kstar a hp y).mp hy
    change z.count a = c at hz
    change (y ++ z).count a % p = c
    rw [List.count_append, hj, hz, Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hc]

lemma countMod_height (a : Alphabet) {p : ℕ} (hp : 0 < p) (c : ℕ) (hc : c < p) :
    HasHeightAtMost ({w | w.count a % p = c} : Language Alphabet) 1 := by
  rw [countMod_eq a hp c hc]
  exact (countBlock_height a p).star.concat ((countIs_height a c).mono (by omega))

lemma periodic_mem {K : Set ℕ} {m p : ℕ} (hK : ∀ k, m ≤ k → (k ∈ K ↔ k + p ∈ K)) :
    ∀ t k, m ≤ k → (k ∈ K ↔ k + p * t ∈ K)
  | 0, k, _ => by simp
  | t + 1, k, hk => by
    rw [periodic_mem hK t k hk, hK (k + p * t) (by omega)]
    ring_nf

lemma mod_shift {n m p j : ℕ} (hj : j < p) (hm : m ≤ n) :
    n % p = (m + j) % p ↔ (n - m) % p = j := by
  have hn : n = m + (n - m) := by omega
  constructor
  · intro h
    have h' : m + (n - m) ≡ m + j [MOD p] := by
      rw [← hn]
      exact h
    have h'' := Nat.ModEq.add_left_cancel' m h'
    unfold Nat.ModEq at h''
    rwa [Nat.mod_eq_of_lt hj] at h''
  · intro h
    change n ≡ m + j [MOD p]
    rw [hn]
    apply Nat.ModEq.add_left
    unfold Nat.ModEq
    rw [h, Nat.mod_eq_of_lt hj]

/-- A letter count lying in an eventually periodic set gives a language of height one. -/
lemma countIn_height (a : Alphabet) {K : Set ℕ} {m p : ℕ} (hp : 0 < p)
    (hK : ∀ k, m ≤ k → (k ∈ K ↔ k + p ∈ K)) :
    HasHeightAtMost ({w | w.count a ∈ K} : Language Alphabet) 1 := by
  classical
  let small : Language Alphabet := ⨆ k : {k : Fin m // (k : ℕ) ∈ K}, countIs a k.1
  let below : Language Alphabet := ⨆ k : Fin m, countIs a k
  let large : Language Alphabet := ⨆ j : {j : Fin p // m + (j : ℕ) ∈ K},
    ({w | w.count a % p = (m + j.1) % p} : Language Alphabet) ⊓ belowᶜ
  have hbelow : ∀ w : List Alphabet, w ∈ below ↔ w.count a < m := by
    intro w
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Language.mem_iSup.mp h
      change w.count a = k at hk
      omega
    · intro h
      exact Language.mem_iSup.mpr ⟨⟨w.count a, h⟩, rfl⟩
  have hdec : ∀ n, m ≤ n → m + (n - m) % p + p * ((n - m) / p) = n := by
    intro n hn
    have := Nat.mod_add_div (n - m) p
    omega
  have heq : ({w | w.count a ∈ K} : Language Alphabet) = small + large := by
    ext w
    constructor
    · intro hw
      change w.count a ∈ K at hw
      by_cases hm : w.count a < m
      · exact Or.inl (Language.mem_iSup.mpr ⟨⟨⟨w.count a, hm⟩, hw⟩, rfl⟩)
      · right
        push Not at hm
        have hj : (w.count a - m) % p < p := Nat.mod_lt _ hp
        have hrep := periodic_mem hK ((w.count a - m) / p) (m + (w.count a - m) % p) (by omega)
        rw [hdec _ hm] at hrep
        refine Language.mem_iSup.mpr ⟨⟨⟨(w.count a - m) % p, hj⟩, hrep.mpr hw⟩, ?_, ?_⟩
        · exact (mod_shift (n := w.count a) hj hm).mpr rfl
        · intro hb
          have := (hbelow w).mp hb
          omega
    · intro h
      rcases h with h | h
      · obtain ⟨k, hk⟩ := Language.mem_iSup.mp h
        change w.count a = k.1 at hk
        change w.count a ∈ K
        rw [hk]
        exact k.2
      · obtain ⟨j, hj1, hj2⟩ := Language.mem_iSup.mp h
        change w.count a % p = (m + j.1) % p at hj1
        have hm : m ≤ w.count a := by
          by_contra hlt
          exact hj2 ((hbelow w).mpr (by omega))
        have hjm := (mod_shift j.1.2 hm).mp hj1
        have hrep := periodic_mem hK ((w.count a - m) / p) (m + j.1) (by omega)
        rw [← hjm, hdec _ hm] at hrep
        exact hrep.mp (by rw [hjm]; exact j.2)
  rw [heq]
  refine (HasHeightAtMost.iSup _ (fun k => (countIs_height a _).mono (by omega))).union
    (HasHeightAtMost.iSup _ (fun j => (countMod_height a hp _ (Nat.mod_lt _ hp)).inter
      (HasHeightAtMost.iSup _ (fun k => (countIs_height a _).mono (by omega))).compl))

end Counting

section Commutative

variable {Alphabet : Type u}

lemma pow_eventually_periodic {M : Type} [Monoid M] [Finite M] (x : M) :
    ∃ m p, 0 < p ∧ ∀ k, m ≤ k → x ^ (k + p) = x ^ k := by
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => x ^ k)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · refine ⟨i, j - i, by omega, fun k hk => ?_⟩
    have : k + (j - i) = (k - i) + j := by omega
    rw [this, pow_add, ← he, ← pow_add]
    congr 1
    omega
  · refine ⟨j, i - j, by omega, fun k hk => ?_⟩
    have : k + (i - j) = (k - j) + i := by omega
    rw [this, pow_add, he, ← pow_add]
    congr 1
    omega

lemma comm_product [Fintype Alphabet] [DecidableEq Alphabet] {M : Type} [CommMonoid M]
    (T : FreeMonoid Alphabet →* M) (w : List Alphabet) :
    T (FreeMonoid.ofList w) = ∏ a, T (FreeMonoid.of a) ^ w.count a := by
  induction w with
  | nil => simp
  | cons b w ih =>
    rw [show FreeMonoid.ofList (b :: w) = FreeMonoid.of b * FreeMonoid.ofList w from rfl,
      map_mul, ih]
    simp only [List.count_cons, beq_iff_eq, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single b]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp

/-- Every fiber of a morphism into a finite commutative monoid has height at most one. -/
theorem fiber_height_one_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) (d : M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) = d} 1 := by
  classical
  let : Fintype Alphabet := Fintype.ofFinite Alphabet
  let : CommMonoid M := { (inferInstance : Monoid M) with mul_comm := hM }
  have heq : ({w | T (FreeMonoid.ofList w) = d} : Language Alphabet) =
      ⨆ f : {f : Alphabet → M // ∏ a, f a = d},
        ⨅ a, ({w | T (FreeMonoid.of a) ^ w.count a = f.1 a} : Language Alphabet) := by
    ext w
    constructor
    · intro hw
      refine Language.mem_iSup.mpr ⟨⟨fun a => T (FreeMonoid.of a) ^ w.count a, ?_⟩, ?_⟩
      · change T (FreeMonoid.ofList w) = d at hw
        rw [← hw, comm_product]
      · exact HasHeightAtMost.mem_iInf_lang.mpr (fun a => rfl)
    · intro h
      obtain ⟨f, hf⟩ := Language.mem_iSup.mp h
      have hf := HasHeightAtMost.mem_iInf_lang.mp hf
      change T (FreeMonoid.ofList w) = d
      rw [comm_product, ← f.2]
      exact Finset.prod_congr rfl (fun a _ => hf a)
  rw [heq]
  refine HasHeightAtMost.iSup _ (fun f => HasHeightAtMost.iInf _ (fun a => ?_))
  obtain ⟨m, p, hp, hper⟩ := pow_eventually_periodic (T (FreeMonoid.of a))
  exact countIn_height a (K := {k | T (FreeMonoid.of a) ^ k = f.1 a}) hp
    (fun k hk => by
      change T (FreeMonoid.of a) ^ k = f.1 a ↔ T (FreeMonoid.of a) ^ (k + p) = f.1 a
      rw [hper k hk])

/-- Every language recognized by a finite commutative monoid has height at most one. -/
theorem height_one_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) (F : Set M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 1 := by
  classical
  have heq : ({w | T (FreeMonoid.ofList w) ∈ F} : Language Alphabet) =
      ⨆ d : F, ({w | T (FreeMonoid.ofList w) = d.1} : Language Alphabet) := by
    ext w
    constructor
    · intro hw
      exact Language.mem_iSup.mpr ⟨⟨_, hw⟩, rfl⟩
    · intro h
      obtain ⟨d, hd⟩ := Language.mem_iSup.mp h
      change T (FreeMonoid.ofList w) = d.1 at hd
      change T (FreeMonoid.ofList w) ∈ F
      rw [hd]
      exact d.2
  rw [heq]
  exact HasHeightAtMost.iSup _ (fun d => fiber_height_one_of_comm hM T d.1)

/-- The single-split hypothesis holds for every morphism into a finite commutative monoid. -/
theorem singleSplit_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) : SingleSplit T :=
  singleSplit_of_fiber_height T (fiber_height_one_of_comm hM T)

/-- Every language recognized by a finite commutative monoid has generalized star height at
most two, through `height_two_of_singleSplit`. -/
theorem height_two_of_comm [Finite Alphabet] {M : Type} [Monoid M] [Fintype M]
    (hM : ∀ x y : M, x * y = y * x) (T : FreeMonoid Alphabet →* M) (F : Set M) :
    HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2 :=
  height_two_of_singleSplit T (singleSplit_of_comm hM T) F

/-- The class of finite commutative monoids contains a monoid with a nontrivial subgroup
(`Multiplicative (ZMod 2)`, a group of order two). -/
theorem comm_class_nontrivial_subgroup :
    (∀ x y : Multiplicative (ZMod 2), x * y = y * x) ∧
      ∃ x : Multiplicative (ZMod 2), x ≠ 1 ∧ x * x = 1 :=
  ⟨fun x y => mul_comm x y, Multiplicative.ofAdd 1, by decide, by decide⟩

end Commutative

end GeneralizedStarHeight
