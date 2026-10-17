import Start.StarHeightHeight

/-!
# Schützenberger's theorem: aperiodic recognition implies star-freeness

* `starFree_of_aperiodic`: if `M` is a finite monoid in which every element satisfies
  `x ^ (n + 1) = x ^ n` for some `n`, every fiber of a morphism `FreeMonoid A →* M` is star-free
  (`HasHeightAtMost _ 0`).
* `starFree_of_dfa`: a decidable certificate for automata.  Given `δ : Q → A → Q`, a list `R` of
  transformations of `Q` that contains the identity, is closed under right composition with every
  letter, and satisfies `f^[N+1] = f^[N]` for every element, every language
  `{w | P (w.foldl δ q₀)}` is star-free.  `dfaCert` computes such a list by breadth-first search.

The proof is the local-divisor proof (Diekert–Kufleitner): induction on `|M|`, and inside on the
set of letters used.  If every letter maps to `1`, the fibers are trivial.  Otherwise pick a letter
`c` with `φ c ≠ 1` and `B` the other letters; a word containing `c` factors as
`u₀ c (u₁ c) ⋯ (u_{k-1} c) u_k` with `uᵢ ∈ B∗`, and the middle part is evaluated in the local
divisor `M_c = φ(c)M ∩ Mφ(c)` (`LocalDiv`), which is aperiodic and smaller than `M`.  The words
`(u₁ c) ⋯ (u_{k-1} c)` with a star-free condition on `φ(u₁) ⋯ φ(u_{k-1}) ∈ M∗` form a star-free
language (`subst_starFree`), because `B∗c` is a prefix code.
-/

namespace GeneralizedStarHeight

universe u

open scoped Computability

namespace Aperiodic

/-! ### Generalities -/

section Basic

variable {A : Type u}

lemma sf_top : HasHeightAtMost (⊤ : Language A) 0 := by
  have h := (HasHeightAtMost.zero (Alphabet := A) 0).compl
  have he : ((0 : Language A)ᶜ) = ⊤ := by
    ext w
    change w ∉ (0 : Language A) ↔ True
    simp
  rwa [he] at h

/-- The words all of whose letters lie in `S`. -/
def overL (S : Set A) : Language A := {w | ∀ a ∈ w, a ∈ S}

lemma overL_eq (S : Set A) :
    overL S = (⊤ * (⨆ a : {a : A // a ∉ S}, ({[a.1]} : Language A)) * ⊤)ᶜ := by
  ext w
  constructor
  · intro hw hm
    obtain ⟨xy, hxy, z, -, rfl⟩ := Language.mem_mul.mp hm
    obtain ⟨x, -, y, hy, rfl⟩ := Language.mem_mul.mp hxy
    obtain ⟨⟨a, ha⟩, hya⟩ := Language.mem_iSup.mp hy
    have hya' : y = [a] := hya
    subst hya'
    exact ha (hw a (by simp))
  · intro hw a ha
    by_contra hS
    obtain ⟨x, z, rfl⟩ := List.append_of_mem ha
    apply hw
    refine Language.mem_mul.mpr ⟨x ++ [a], Language.mem_mul.mpr ⟨x, trivial, [a], ?_, rfl⟩,
      z, trivial, by simp⟩
    exact Language.mem_iSup.mpr ⟨⟨a, hS⟩, rfl⟩

lemma overL_starFree [Finite A] (S : Set A) : HasHeightAtMost (overL S) 0 := by
  rw [overL_eq]
  exact ((sf_top.concat (HasHeightAtMost.iSup _ fun (a : {a : A // a ∉ S}) => HasHeightAtMost.letter a.1 0)).concat
    sf_top).compl

end Basic

/-! ### The local divisor -/

section LocalDivisor

variable {M : Type u} [Monoid M]

/-- The local divisor `cM ∩ Mc` of `M` at `c`. -/
def LocalDiv (c : M) : Type u := {x : M // (∃ p, x = p * c) ∧ ∃ q, x = c * q}

namespace LocalDiv

variable {c : M}

/-- A right factor `q` with `x = c * q`. -/
noncomputable def rq (x : LocalDiv c) : M := Classical.choose x.2.2

lemma rq_spec (x : LocalDiv c) : x.1 = c * x.rq := Classical.choose_spec x.2.2

/-- A left factor `p` with `x = p * c`. -/
noncomputable def lp (x : LocalDiv c) : M := Classical.choose x.2.1

lemma lp_spec (x : LocalDiv c) : x.1 = x.lp * c := Classical.choose_spec x.2.1

/-- The product `(p c) ∘ (c q) = p c q`. -/
noncomputable instance : Mul (LocalDiv c) where
  mul x y := ⟨x.1 * y.rq, ⟨x.lp * y.lp, by
      rw [x.lp_spec, mul_assoc, ← y.rq_spec, y.lp_spec, mul_assoc]⟩,
    ⟨x.rq * y.rq, by rw [x.rq_spec, mul_assoc]⟩⟩

instance : One (LocalDiv c) where
  one := ⟨c, ⟨1, by simp⟩, ⟨1, by simp⟩⟩

lemma one_val : (1 : LocalDiv c).1 = c := rfl

lemma mul_val_def (x y : LocalDiv c) : (x * y).1 = x.1 * y.rq := rfl

lemma mul_val_of_left {x : LocalDiv c} {p : M} (hx : x.1 = p * c) (y : LocalDiv c) :
    (x * y).1 = p * y.1 := by
  rw [mul_val_def, hx, mul_assoc, ← y.rq_spec]

lemma mul_val_of_right (x : LocalDiv c) {y : LocalDiv c} {q : M} (hy : y.1 = c * q) :
    (x * y).1 = x.1 * q := by
  rw [mul_val_of_left x.lp_spec, hy, x.lp_spec, mul_assoc]

noncomputable instance : Monoid (LocalDiv c) where
  mul_assoc x y z := by
    apply Subtype.ext
    have hyz : (y * z).1 = c * (y.rq * z.rq) := by
      rw [mul_val_def, y.rq_spec, mul_assoc]
    rw [mul_val_of_right x hyz, mul_val_def, mul_val_def, mul_assoc]
  one_mul y := by
    apply Subtype.ext
    rw [mul_val_def, one_val, ← y.rq_spec]
  mul_one x := by
    apply Subtype.ext
    rw [mul_val_of_right x (show (1 : LocalDiv c).1 = c * 1 by simp [one_val]), mul_one]

lemma pow_val (x : LocalDiv c) {q : M} (hq : x.1 = c * q) :
    ∀ n : ℕ, (x ^ (n + 1)).1 = c * q ^ (n + 1)
  | 0 => by simp [hq]
  | n + 1 => by
      rw [pow_succ, mul_val_of_right _ hq, pow_val x hq n, mul_assoc, ← pow_succ]

lemma aperiodic (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (x : LocalDiv c) :
    ∃ n : ℕ, x ^ (n + 1) = x ^ n := by
  obtain ⟨n, hn⟩ := hM x.rq
  refine ⟨n + 1, Subtype.ext ?_⟩
  rw [pow_val x x.rq_spec, pow_val x x.rq_spec]
  congr 1
  calc x.rq ^ (n + 1 + 1) = x.rq ^ (n + 1) * x.rq := pow_succ _ _
    _ = x.rq ^ n * x.rq := by rw [hn]
    _ = x.rq ^ (n + 1) := (pow_succ _ _).symm

lemma one_not_mem [Finite M] (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (hc : c ≠ 1) :
    ¬ ((∃ p, (1 : M) = p * c) ∧ ∃ q, (1 : M) = c * q) := by
  rintro ⟨-, q, hq⟩
  have hqc : q * c = 1 := mul_eq_one_comm.mp hq.symm
  let v : Mˣ := ⟨c, q, hq.symm, hqc⟩
  obtain ⟨n, hn⟩ := hM c
  have hv : v ^ (n + 1) = v ^ n := Units.ext (by simpa using hn)
  rw [pow_succ, mul_eq_left] at hv
  exact hc (congrArg Units.val hv)

lemma card_lt [Finite M] (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (hc : c ≠ 1) :
    Nat.card (LocalDiv c) < Nat.card M :=
  Finite.card_subtype_lt (one_not_mem hM hc)

instance [Finite M] : Finite (LocalDiv c) := Subtype.finite

/-- `t ↦ c t c`, extended to words. -/
def psiGen (c t : M) : LocalDiv c := ⟨c * t * c, ⟨c * t, rfl⟩, ⟨t * c, by rw [mul_assoc]⟩⟩

/-- `t ↦ c t c`, extended to words. -/
noncomputable def psi (c : M) : FreeMonoid M →* LocalDiv c := FreeMonoid.lift (psiGen c)

lemma psi_val (ts : List M) :
    (psi c (FreeMonoid.ofList ts)).1 = c * (ts.map (· * c)).prod := by
  induction ts with
  | nil => simp [one_val]
  | cons t ts ih =>
      rw [FreeMonoid.ofList_cons, map_mul, mul_val_of_left (p := c * t) (by
        unfold psi; rw [FreeMonoid.lift_eval_of]; rfl), ih]
      simp [mul_assoc]

end LocalDiv

end LocalDivisor


/-! ### Words cut at a letter -/

section Words

variable {A : Type u} (c : A)

/-- `(u₁ c)(u₂ c) ⋯ (u_k c)`. -/
def cflat (us : List (List A)) : List A := (us.map (· ++ [c])).flatten

@[simp] lemma cflat_nil : cflat c [] = [] := rfl

lemma cflat_cons (u : List A) (us : List (List A)) :
    cflat c (u :: us) = u ++ c :: cflat c us := by
  simp [cflat]

lemma cflat_append (us vs : List (List A)) : cflat c (us ++ vs) = cflat c us ++ cflat c vs := by
  simp [cflat]

lemma mem_cflat {us : List (List A)} {u : List A} (hu : u ∈ us) {a : A} (ha : a ∈ u) :
    a ∈ cflat c us := by
  simp only [cflat, List.mem_flatten, List.mem_map]
  exact ⟨u ++ [c], ⟨u, hu, rfl⟩, List.mem_append_left _ ha⟩

variable {c}

lemma split_unique : ∀ {u u' r r' : List A}, c ∉ u → c ∉ u' → u ++ c :: r = u' ++ c :: r' →
    u = u' ∧ r = r'
  | [], [], r, r', _, _, h => by simpa using h
  | [], a :: u', r, r', _, hu', h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu'
  | a :: u, [], r, r', hu, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) hu
  | a :: u, a' :: u', r, r', hu, hu', h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := split_unique (fun h' => hu (List.mem_cons_of_mem _ h'))
        (fun h' => hu' (List.mem_cons_of_mem _ h')) h
      exact ⟨rfl, rfl⟩

lemma cflat_inj : ∀ {us us' : List (List A)}, (∀ u ∈ us, c ∉ u) → (∀ u ∈ us', c ∉ u) →
    cflat c us = cflat c us' → us = us'
  | [], [], _, _, _ => rfl
  | [], u :: us', _, _, h => by simp [cflat_cons] at h
  | u :: us, [], _, _, h => by simp [cflat_cons] at h
  | u :: us, u' :: us', hus, hus', h => by
      rw [cflat_cons, cflat_cons] at h
      obtain ⟨rfl, h'⟩ := split_unique (hus u (by simp)) (hus' u' (by simp)) h
      rw [cflat_inj (fun v hv => hus v (by simp [hv])) (fun v hv => hus' v (by simp [hv])) h']

variable (c) in
/-- Every word is `(u₁ c) ⋯ (u_k c) r` with `c ∉ uᵢ`, `c ∉ r`. -/
lemma decompose [DecidableEq A] : ∀ v : List A,
    ∃ us r, (∀ u ∈ us, c ∉ u) ∧ c ∉ r ∧ v = cflat c us ++ r
  | [] => ⟨[], [], by simp, by simp, rfl⟩
  | a :: v => by
      obtain ⟨us, r, hus, hr, rfl⟩ := decompose v
      by_cases ha : a = c
      · subst ha
        refine ⟨[] :: us, r, ?_, hr, by simp [cflat_cons]⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · simp
        · exact hus u hu
      · rcases us with _ | ⟨u, us⟩
        · refine ⟨[], a :: r, by simp, ?_, by simp⟩
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => ha h.symm, hr⟩
        · refine ⟨(a :: u) :: us, r, ?_, hr, by simp [cflat_cons]⟩
          intro u' hu'
          rcases List.mem_cons.mp hu' with rfl | hu'
          · simp only [List.mem_cons, not_or]
            exact ⟨fun h => ha h.symm, hus u (by simp)⟩
          · exact hus u' (by simp [hu'])

end Words

/-! ### Substitution -/

section Subst

variable {A : Type u} {M : Type u} [Monoid M] (φ : FreeMonoid A →* M)

/-- The fiber of `m` among the words over `S`. -/
def fibL (S : Set A) (m : M) : Language A := {w | w ∈ overL S ∧ φ (FreeMonoid.ofList w) = m}

lemma map_cflat (c : A) (us : List (List A)) :
    φ (FreeMonoid.ofList (cflat c us)) =
      (us.map (fun u => φ (FreeMonoid.ofList u) * φ (FreeMonoid.of c))).prod := by
  induction us with
  | nil => simp
  | cons u us ih =>
      rw [cflat_cons, FreeMonoid.ofList_append, FreeMonoid.ofList_cons, map_mul, map_mul, ih]
      simp [mul_assoc]

/-- `σ(K)`: the words `(u₁ c) ⋯ (u_k c)` with `uᵢ ∈ B∗` and `φ(u₁) ⋯ φ(u_k) ∈ K`. -/
def subst (B : Set A) (c : A) (K : Language M) : Language A :=
  {w | ∃ us : List (List A), (∀ u ∈ us, u ∈ overL B) ∧ w = cflat c us ∧
    us.map (fun u => φ (FreeMonoid.ofList u)) ∈ K}

variable {φ} {B : Set A} {c : A}

lemma subst_zero : subst φ B c 0 = 0 := by
  ext w
  constructor
  · rintro ⟨us, -, -, h⟩; exact h
  · intro h; exact absurd h (by simp)

lemma subst_one : subst φ B c 1 = 1 := by
  ext w
  rw [Language.mem_one]
  constructor
  · rintro ⟨us, -, rfl, h⟩
    rw [Language.mem_one, List.map_eq_nil_iff] at h
    subst h; rfl
  · rintro rfl
    exact ⟨[], by simp, rfl, (Language.mem_one _).mpr rfl⟩

lemma subst_letter (t : M) : subst φ B c {[t]} = fibL φ B t * {[c]} := by
  ext w
  rw [Language.mem_mul]
  constructor
  · rintro ⟨us, hus, rfl, h⟩
    have h' : us.map (fun u => φ (FreeMonoid.ofList u)) = [t] := h
    rw [List.map_eq_singleton_iff] at h'
    obtain ⟨u, rfl, hu⟩ := h'
    exact ⟨u, ⟨hus u (by simp), hu⟩, [c], rfl, by simp [cflat]⟩
  · rintro ⟨u, ⟨hu, hut⟩, cc, hcc, rfl⟩
    have hcc' : cc = [c] := hcc
    subst hcc'
    refine ⟨[u], by simpa using hu, by simp [cflat], ?_⟩
    show [φ (FreeMonoid.ofList u)] = [t]
    rw [hut]

lemma subst_add (K K' : Language M) : subst φ B c (K + K') = subst φ B c K + subst φ B c K' := by
  ext w
  rw [Language.mem_add]
  constructor
  · rintro ⟨us, hus, rfl, h⟩
    rcases (Language.mem_add _ _ _).mp h with h | h
    · exact Or.inl ⟨us, hus, rfl, h⟩
    · exact Or.inr ⟨us, hus, rfl, h⟩
  · rintro (⟨us, hus, rfl, h⟩ | ⟨us, hus, rfl, h⟩)
    · exact ⟨us, hus, rfl, (Language.mem_add _ _ _).mpr (Or.inl h)⟩
    · exact ⟨us, hus, rfl, (Language.mem_add _ _ _).mpr (Or.inr h)⟩

lemma subst_mul (K K' : Language M) : subst φ B c (K * K') = subst φ B c K * subst φ B c K' := by
  ext w
  rw [Language.mem_mul]
  constructor
  · rintro ⟨us, hus, rfl, h⟩
    obtain ⟨k, hk, k', hk', he⟩ := Language.mem_mul.mp h
    obtain ⟨us₁, us₂, rfl, rfl, rfl⟩ := List.map_eq_append_iff.mp he.symm
    exact ⟨cflat c us₁, ⟨us₁, fun u hu => hus u (by simp [hu]), rfl, hk⟩,
      cflat c us₂, ⟨us₂, fun u hu => hus u (by simp [hu]), rfl, hk'⟩, (cflat_append c _ _).symm⟩
  · rintro ⟨x, ⟨us₁, hus₁, rfl, h₁⟩, y, ⟨us₂, hus₂, rfl, h₂⟩, rfl⟩
    refine ⟨us₁ ++ us₂, ?_, (cflat_append c _ _).symm, ?_⟩
    · intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact hus₁ u hu
      · exact hus₂ u hu
    · rw [List.map_append]
      exact Language.mem_mul.mpr ⟨_, h₁, _, h₂, rfl⟩

lemma not_mem_of_overL (hc : c ∉ B) {u : List A} (hu : u ∈ overL B) : c ∉ u :=
  fun h => hc (hu c h)

lemma subst_compl (hc : c ∉ B) (K : Language M) :
    subst φ B c Kᶜ = subst φ B c ⊤ ⊓ (subst φ B c K)ᶜ := by
  ext w
  constructor
  · rintro ⟨us, hus, rfl, h⟩
    refine ⟨⟨us, hus, rfl, trivial⟩, ?_⟩
    rintro ⟨us', hus', he, h'⟩
    have := cflat_inj (fun u hu => not_mem_of_overL hc (hus' u hu))
      (fun u hu => not_mem_of_overL hc (hus u hu)) he.symm
    subst this
    exact h h'
  · rintro ⟨⟨us, hus, rfl, -⟩, h⟩
    exact ⟨us, hus, rfl, fun h' => h ⟨us, hus, rfl, h'⟩⟩

lemma subst_top [DecidableEq A] :
    subst φ B c ⊤ = 1 + overL (insert c B) * {[c]} := by
  ext w
  rw [Language.mem_add, Language.mem_one, Language.mem_mul]
  constructor
  · rintro ⟨us, hus, rfl, -⟩
    rcases List.eq_nil_or_concat us with rfl | ⟨us₀, u, rfl⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨cflat c us₀ ++ u, ?_, [c], rfl, ?_⟩
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · simp only [cflat, List.mem_flatten, List.mem_map] at ha
          obtain ⟨l, ⟨v, hv, rfl⟩, ha⟩ := ha
          rcases List.mem_append.mp ha with ha | ha
          · exact Set.mem_insert_of_mem _ (hus v (by simp [hv]) a ha)
          · rw [List.mem_singleton.mp ha]; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (hus u (by simp) a ha)
      · rw [List.concat_eq_append, cflat_append]; simp [cflat]
  · rintro (rfl | ⟨v, hv, cc, hcc, rfl⟩)
    · exact ⟨[], by simp, rfl, trivial⟩
    · have hcc' : cc = [c] := hcc
      subst hcc'
      obtain ⟨us, r, hus, hr, rfl⟩ := decompose c v
      have hB : ∀ {a}, a ∈ cflat c us ++ r → a ≠ c → a ∈ B := by
        intro a ha hac
        rcases hv a ha with h | h
        · exact absurd h hac
        · exact h
      refine ⟨us ++ [r], ?_, by rw [cflat_append]; simp [cflat], trivial⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · intro a ha
        exact hB (List.mem_append_left _ (mem_cflat c hu ha))
          (fun h => hus u hu (h ▸ ha))
      · rw [List.mem_singleton.mp hu]
        intro a ha
        exact hB (List.mem_append_right _ ha) (fun h => hr (h ▸ ha))

/-- **Substitution lemma.** If `K ⊆ M∗` is star-free, so is `σ(K)`. -/
lemma subst_starFree [Finite A] [DecidableEq A] (hc : c ∉ B)
    (hB : ∀ t, HasHeightAtMost (fibL φ B t) 0) :
    ∀ E : Expression M, E.height = 0 → HasHeightAtMost (subst φ B c E.language) 0
  | .zero, _ => by rw [Expression.language, subst_zero]; exact HasHeightAtMost.zero 0
  | .one, _ => by rw [Expression.language, subst_one]; exact HasHeightAtMost.one 0
  | .letter t, _ => by
      rw [Expression.language, subst_letter]; exact (hB t).concat (HasHeightAtMost.letter c 0)
  | .union P Q, h => by
      have hP : P.height = 0 := by simp [Expression.height] at h; omega
      have hQ : Q.height = 0 := by simp [Expression.height] at h; omega
      rw [Expression.language, subst_add]
      exact (subst_starFree hc hB P hP).union (subst_starFree hc hB Q hQ)
  | .concat P Q, h => by
      have hP : P.height = 0 := by simp [Expression.height] at h; omega
      have hQ : Q.height = 0 := by simp [Expression.height] at h; omega
      rw [Expression.language, subst_mul]
      exact (subst_starFree hc hB P hP).concat (subst_starFree hc hB Q hQ)
  | .compl P, h => by
      rw [Expression.language, subst_compl hc, subst_top]
      exact ((HasHeightAtMost.one 0).union ((overL_starFree _).concat
        (HasHeightAtMost.letter c 0))).inter (subst_starFree hc hB P h).compl
  | .star P, h => by simp [Expression.height] at h

lemma subst_starFree' [Finite A] [DecidableEq A] (hc : c ∉ B)
    (hB : ∀ t, HasHeightAtMost (fibL φ B t) 0) {K : Language M} (hK : HasHeightAtMost K 0) :
    HasHeightAtMost (subst φ B c K) 0 := by
  obtain ⟨E, rfl, hE⟩ := hK
  exact subst_starFree hc hB E (by omega)

end Subst

/-! ### The induction -/

section Main

variable {A : Type u} {M : Type u} [Monoid M]

lemma fibL_trivial [Finite A] (φ : FreeMonoid A →* M) (S : Set A)
    (hS : ∀ a ∈ S, φ (FreeMonoid.of a) = 1) (m : M) : HasHeightAtMost (fibL φ S m) 0 := by
  have hval : ∀ w ∈ overL S, φ (FreeMonoid.ofList w) = 1 := by
    intro w hw
    induction w with
    | nil => simp
    | cons a w ih =>
        rw [FreeMonoid.ofList_cons, map_mul, hS a (hw a (by simp)),
          ih (fun b hb => hw b (by simp [hb])), one_mul]
  by_cases hm : m = 1
  · have : fibL φ S m = overL S := by
      ext w
      exact ⟨fun h => h.1, fun h => ⟨h, hm ▸ hval w h⟩⟩
    rw [this]
    exact overL_starFree S
  · have : fibL φ S m = 0 := by
      ext w
      constructor
      · rintro ⟨h1, h2⟩
        exact hm (h2.symm.trans (hval w h1))
      · intro h
        exact absurd h (by simp)
    rw [this]
    exact HasHeightAtMost.zero 0

/-- Index of the decomposition `p · n · q = m` with `n` in the local divisor. -/
def DIdx (c m : M) := {z : M × LocalDiv c × M // z.1 * z.2.1.1 * z.2.2 = m}

instance [Finite M] (c m : M) : Finite (DIdx c m) := by unfold DIdx; infer_instance

lemma psi_map_val (φ : FreeMonoid A →* M) (c : A) (us : List (List A)) :
    (LocalDiv.psi (φ (FreeMonoid.of c))
        (FreeMonoid.ofList (us.map fun u => φ (FreeMonoid.ofList u)))).1 =
      φ (FreeMonoid.of c) * φ (FreeMonoid.ofList (cflat c us)) := by
  rw [LocalDiv.psi_val, map_cflat, List.map_map]
  rfl

lemma overL_of_insert {B : Set A} {c : A} {u v : List A} (hv : v ∈ overL (insert c B))
    (huv : ∀ a ∈ u, a ∈ v) (hcu : c ∉ u) : u ∈ overL B := by
  intro a ha
  rcases hv a (huv a ha) with h | h
  · exact absurd (h ▸ ha) hcu
  · exact h

/-- **The decomposition at `c`.** -/
lemma fibL_insert_eq [DecidableEq A] (φ : FreeMonoid A →* M) {B : Set A} {c : A} (hc : c ∉ B)
    (m : M) :
    fibL φ (insert c B) m = fibL φ B m + ⨆ z : DIdx (φ (FreeMonoid.of c)) m,
      fibL φ B z.1.1 * {[c]} *
        subst φ B c {ts | LocalDiv.psi (φ (FreeMonoid.of c)) (FreeMonoid.ofList ts) = z.1.2.1} *
          fibL φ B z.1.2.2 := by
  ext w
  rw [Language.mem_add]
  constructor
  · rintro ⟨hw, hwm⟩
    obtain ⟨us, r, hus, hr, rfl⟩ := decompose c w
    have hrB : r ∈ overL B :=
      overL_of_insert hw (fun a ha => List.mem_append_right _ ha) hr
    have husB : ∀ u ∈ us, u ∈ overL B := fun u hu =>
      overL_of_insert hw (fun a ha => List.mem_append_left _ (mem_cflat c hu ha)) (hus u hu)
    rcases us with _ | ⟨u₀, us⟩
    · exact Or.inl ⟨hrB, hwm⟩
    · right
      refine Language.mem_iSup.mpr ⟨⟨(φ (FreeMonoid.ofList u₀),
        LocalDiv.psi (φ (FreeMonoid.of c))
          (FreeMonoid.ofList (us.map fun u => φ (FreeMonoid.ofList u))),
        φ (FreeMonoid.ofList r)), ?_⟩, ?_⟩
      · simp only
        rw [psi_map_val, ← hwm, cflat_cons]
        simp only [FreeMonoid.ofList_append, FreeMonoid.ofList_cons, map_mul, mul_assoc]
      · refine Language.mem_mul.mpr ⟨u₀ ++ [c] ++ cflat c us, ?_, r, ⟨hrB, rfl⟩, ?_⟩
        · refine Language.mem_mul.mpr ⟨u₀ ++ [c], ?_, cflat c us,
            ⟨us, fun u hu => husB u (by simp [hu]), rfl, rfl⟩, rfl⟩
          exact Language.mem_mul.mpr ⟨u₀, ⟨husB u₀ (by simp), rfl⟩, [c], rfl, rfl⟩
        · simp [cflat_cons]
  · rintro (⟨hw, hwm⟩ | hw)
    · exact ⟨fun a ha => Set.mem_insert_of_mem _ (hw a ha), hwm⟩
    · obtain ⟨⟨⟨p, n, q⟩, hz⟩, hw⟩ := Language.mem_iSup.mp hw
      obtain ⟨xy, hxy, r, ⟨hrB, hrq⟩, rfl⟩ := Language.mem_mul.mp hw
      obtain ⟨xc, hxc, y, ⟨us, husB, rfl, hus⟩, rfl⟩ := Language.mem_mul.mp hxy
      obtain ⟨x, ⟨hxB, hxp⟩, cc, hcc, rfl⟩ := Language.mem_mul.mp hxc
      have hcc' : cc = [c] := hcc
      subst hcc'
      have hus' : LocalDiv.psi (φ (FreeMonoid.of c))
          (FreeMonoid.ofList (us.map fun u => φ (FreeMonoid.ofList u))) = n := hus
      refine ⟨?_, ?_⟩
      · intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ((ha | rfl) | ha) | ha
        · exact Set.mem_insert_of_mem _ (hxB a ha)
        · exact Set.mem_insert _ _
        · simp only [cflat, List.mem_flatten, List.mem_map] at ha
          obtain ⟨l, ⟨v, hv, rfl⟩, ha⟩ := ha
          rcases List.mem_append.mp ha with ha | ha
          · exact Set.mem_insert_of_mem _ (husB v hv a ha)
          · rw [List.mem_singleton.mp ha]; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (hrB a ha)
      · have hxp' : φ (FreeMonoid.ofList x) = p := hxp
        have hrq' : φ (FreeMonoid.ofList r) = q := hrq
        rw [← hz, ← hxp', ← hrq', ← hus', psi_map_val]
        simp only [FreeMonoid.ofList_append, FreeMonoid.ofList_cons, FreeMonoid.ofList_nil,
          map_mul, mul_one, mul_assoc]

theorem fibL_starFree_aux : ∀ (n : ℕ) (M : Type u) [Monoid M] [Finite M], Nat.card M = n →
    (∀ x : M, ∃ k : ℕ, x ^ (k + 1) = x ^ k) →
    ∀ (A : Type u) [Finite A] (φ : FreeMonoid A →* M) (S : Finset A) (m : M),
      HasHeightAtMost (fibL φ (S : Set A) m) 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihM =>
  intro M _ _ hcard hM A _ φ S
  classical
  induction S using Finset.strongInduction with
  | H S ihS =>
  intro m
  by_cases htriv : ∀ a ∈ S, φ (FreeMonoid.of a) = 1
  · exact fibL_trivial φ _ (by simpa using htriv) m
  push Not at htriv
  obtain ⟨c, hcS, hc1⟩ := htriv
  have hS : (S : Set A) = insert c ((S.erase c : Finset A) : Set A) := by
    rw [Finset.coe_erase, Set.insert_sdiff_singleton, Set.insert_eq_of_mem (by simpa using hcS)]
  have hcB : c ∉ ((S.erase c : Finset A) : Set A) := by simp
  have hB : ∀ t, HasHeightAtMost (fibL φ ((S.erase c : Finset A) : Set A) t) 0 :=
    fun t => ihS _ (Finset.erase_ssubset hcS) t
  rw [hS, fibL_insert_eq φ hcB m]
  refine (hB m).union (HasHeightAtMost.iSup _ fun z => ?_)
  refine (((hB _).concat (HasHeightAtMost.letter c 0)).concat (subst_starFree' hcB hB ?_)).concat
    (hB _)
  have hlt := LocalDiv.card_lt hM hc1
  have : Fintype M := Fintype.ofFinite M
  have h := ihM _ (hcard ▸ hlt) (LocalDiv (φ (FreeMonoid.of c))) rfl (LocalDiv.aperiodic hM) M
    (LocalDiv.psi _) Finset.univ z.1.2.1
  have heq : fibL (LocalDiv.psi (φ (FreeMonoid.of c))) ((Finset.univ : Finset M) : Set M) z.1.2.1 =
      {ts | LocalDiv.psi (φ (FreeMonoid.of c)) (FreeMonoid.ofList ts) = z.1.2.1} := by
    ext ts
    exact ⟨fun h => h.2, fun h => ⟨fun a _ => by simp, h⟩⟩
  rwa [heq] at h

/-- **Schützenberger's theorem** (aperiodic ⇒ star-free). Every fiber of a morphism from a free
monoid on a finite alphabet onto a finite aperiodic monoid is star-free. -/
theorem starFree_of_aperiodic {A : Type u} [Finite A] {M : Type u} [Monoid M] [Finite M]
    (hM : ∀ x : M, ∃ n : ℕ, x ^ (n + 1) = x ^ n) (φ : FreeMonoid A →* M) (m : M) :
    HasHeightAtMost {w : List A | φ (FreeMonoid.ofList w) = m} 0 := by
  have : Fintype A := Fintype.ofFinite A
  have h := fibL_starFree_aux _ M rfl hM A φ Finset.univ m
  have heq : fibL φ ((Finset.univ : Finset A) : Set A) m =
      {w : List A | φ (FreeMonoid.ofList w) = m} := by
    ext w
    exact ⟨fun h => h.2, fun h => ⟨fun a _ => by simp, h⟩⟩
  rwa [heq] at h

end Main

/-! ### Automata: a decidable certificate -/

section DFA

variable {A Q : Type u}

/-- Equality of two transformations, tested on the states `qs`. -/
def tEq [DecidableEq Q] (qs : List Q) (f g : Q → Q) : Bool := qs.all fun q => decide (f q = g q)

/-- Right composition with a letter. -/
def tStep (δ : Q → A → Q) (f : Q → Q) (a : A) : Q → Q := fun q => δ (f q) a

/-- **The certificate.** `R` contains the identity, is closed under right composition with every
letter, and every element satisfies `f^[N+1] = f^[N]`. -/
def certOK [DecidableEq Q] (qs : List Q) (letters : List A) (δ : Q → A → Q) (R : List (Q → Q)) (N : ℕ) : Bool :=
  (R.any (tEq qs id) && R.all (fun f => letters.all fun a => R.any (tEq qs (tStep δ f a)))) &&
    R.all (fun f => tEq qs (f^[N + 1]) (f^[N]))

/-- Add `g` to the queue and to the seen list unless it was seen. -/
def tInsert [DecidableEq Q] (qs : List Q) (acc : List (Q → Q) × List (Q → Q)) (g : Q → Q) :
    List (Q → Q) × List (Q → Q) :=
  if acc.2.any (tEq qs g) then acc else (acc.1 ++ [g], acc.2 ++ [g])

/-- Breadth-first closure of a list of transformations under right composition with letters. -/
def tClose [DecidableEq Q] (qs : List Q) (letters : List A) (δ : Q → A → Q) :
    ℕ → List (Q → Q) → List (Q → Q) → List (Q → Q)
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, f :: todo, seen =>
      let r := letters.foldl (fun acc a => tInsert qs acc (tStep δ f a)) (todo, seen)
      tClose qs letters δ n r.1 r.2

/-- The transformation monoid of `δ`, computed with `fuel` steps of breadth-first search. -/
def dfaCert [DecidableEq Q] (qs : List Q) (letters : List A) (δ : Q → A → Q) (fuel : ℕ) : List (Q → Q) :=
  tClose qs letters δ fuel [id] [id]

lemma tEq_iff [DecidableEq Q] {qs : List Q} (hqs : ∀ q, q ∈ qs) {f g : Q → Q} : tEq qs f g = true ↔ f = g := by
  unfold tEq
  rw [List.all_eq_true]
  constructor
  · intro h
    funext q
    exact of_decide_eq_true (h q (hqs q))
  · rintro rfl q _
    exact decide_eq_true rfl

/-- Transformations of `Q` composed left to right (`f * g` applies `f` first). -/
def RT (Q : Type u) : Type u := Q → Q

instance : Monoid (RT Q) where
  mul f g := fun q => g (f q)
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- Application of a transformation. -/
def RT.ap (f : RT Q) (q : Q) : Q := f q

lemma rt_mul_apply (f g : RT Q) (q : Q) : (f * g : RT Q) q = g (f q) := rfl

lemma rt_pow_apply (f : RT Q) : ∀ (n : ℕ) (q : Q), (f ^ n : RT Q) q = (f : Q → Q)^[n] q
  | 0, _ => rfl
  | n + 1, q => by
      rw [pow_succ, rt_mul_apply, rt_pow_apply f n]
      exact (Function.iterate_succ_apply' (f : Q → Q) n q).symm

/-- The transition morphism of `δ`. -/
def transMor (δ : Q → A → Q) : FreeMonoid A →* RT Q :=
  FreeMonoid.lift fun a => ((fun q => δ q a : Q → Q) : RT Q)

lemma transMor_of (δ : Q → A → Q) (a : A) :
    transMor δ (FreeMonoid.of a) = ((fun q => δ q a : Q → Q) : RT Q) :=
  FreeMonoid.lift_eval_of _ _

lemma transMor_apply (δ : Q → A → Q) (w : List A) (q : Q) :
    (transMor δ (FreeMonoid.ofList w) : Q → Q) q = w.foldl δ q := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      rw [FreeMonoid.ofList_cons, map_mul, rt_mul_apply, transMor_of, ih]
      rfl

lemma tEq_iff_on [DecidableEq Q] {qs : List Q} {f g : Q → Q} :
    tEq qs f g = true ↔ ∀ q ∈ qs, f q = g q := by
  unfold tEq
  rw [List.all_eq_true]
  exact ⟨fun h q hq => of_decide_eq_true (h q hq), fun h q hq => decide_eq_true (h q hq)⟩

/-- **Star-freeness from a transformation-monoid certificate**, for an automaton restricted to a
list `qs` of states that contains the initial state and is closed under the transitions (for
instance its reachable states). The certificate only compares transformations on `qs`. -/
theorem starFree_of_dfa_closed [DecidableEq Q] (qs : List Q) (q₀ : Q) (hq₀ : q₀ ∈ qs)
    (letters : List A) (hl : ∀ a, a ∈ letters) (δ : Q → A → Q)
    (hcl : ∀ q ∈ qs, ∀ a, δ q a ∈ qs) (R : List (Q → Q)) (N : ℕ)
    (hR : certOK qs letters δ R N = true) (P : Q → Prop) :
    HasHeightAtMost {w : List A | P (w.foldl δ q₀)} 0 := by
  have hFA : Finite A := by
    refine Finite.of_surjective (fun i : Fin letters.length => letters.get i) fun a => ?_
    obtain ⟨i, hi⟩ := List.get_of_mem (hl a)
    exact ⟨i, hi⟩
  have hFQ : Finite {q // q ∈ qs} := by
    refine Finite.of_surjective (fun i : Fin qs.length => (⟨qs.get i, List.get_mem _ _⟩ :
      {q // q ∈ qs})) fun q => ?_
    obtain ⟨i, hi⟩ := List.get_of_mem q.2
    exact ⟨i, Subtype.ext hi⟩
  have hFE : Finite (RT {q // q ∈ qs}) := inferInstanceAs (Finite ({q // q ∈ qs} → {q // q ∈ qs}))
  let δ' : {q // q ∈ qs} → A → {q // q ∈ qs} := fun q a => ⟨δ q.1 a, hcl q.1 q.2 a⟩
  have hfold : ∀ (w : List A) (q : {q // q ∈ qs}), (w.foldl δ' q).1 = w.foldl δ q.1 := by
    intro w
    induction w with
    | nil => intro q; rfl
    | cons a w ih => intro q; exact ih _
  simp only [certOK, Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hR
  obtain ⟨⟨⟨g₀, hg₀, hid⟩, hcl'⟩, hap⟩ := hR
  have hmem : ∀ w : List A, ∃ g ∈ R, ∀ q ∈ qs, g q = w.foldl δ q := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact ⟨g₀, hg₀, fun q hq => (tEq_iff_on.mp hid q hq).symm⟩
    | append_singleton w a ih =>
        obtain ⟨g, hg, hge⟩ := ih
        obtain ⟨g', hg', he⟩ := hcl' _ hg a (hl a)
        refine ⟨g', hg', fun q hq => ?_⟩
        rw [← tEq_iff_on.mp he q hq]
        simp [tStep, List.foldl_append, hge q hq]
  let Φ := transMor (A := A) δ'
  have hMap : ∀ x : MonoidHom.mrange Φ, ∃ n : ℕ, x ^ (n + 1) = x ^ n := by
    rintro ⟨x, y, rfl⟩
    refine ⟨N, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow]
    obtain ⟨g, hg, hge⟩ := hmem (FreeMonoid.toList y)
    have hΦ : ∀ q' : {q // q ∈ qs}, (RT.ap (Φ y) q').1 = g q'.1 := by
      intro q'
      rw [hge q'.1 q'.2, ← hfold, ← transMor_apply δ' (FreeMonoid.toList y) q']
      rfl
    have hit : ∀ (n : ℕ) (q' : {q // q ∈ qs}),
        (((Φ y : RT {q // q ∈ qs}) : {q // q ∈ qs} → {q // q ∈ qs})^[n] q').1 = g^[n] q'.1 := by
      intro n
      induction n with
      | zero => intro q'; rfl
      | succ n ih =>
          intro q'
          have e : ((Φ y : RT {q // q ∈ qs}) : {q // q ∈ qs} → {q // q ∈ qs})^[n + 1] q' =
              RT.ap (Φ y) (((Φ y : RT {q // q ∈ qs}) : {q // q ∈ qs} → {q // q ∈ qs})^[n] q') :=
            Function.iterate_succ_apply' _ n q'
          rw [e, hΦ, ih, Function.iterate_succ_apply']
    have hgN : ∀ q ∈ qs, g^[N + 1] q = g^[N] q := tEq_iff_on.mp (hap g hg)
    funext q'
    apply Subtype.ext
    rw [rt_pow_apply, rt_pow_apply, hit, hit, hgN q'.1 q'.2]
  let Ψ := Φ.mrangeRestrict
  have heq : ({w : List A | P (w.foldl δ q₀)} : Language A) =
      ⨆ y : {y : MonoidHom.mrange Φ // P (RT.ap y.1 ⟨q₀, hq₀⟩).1},
        ({w : List A | Ψ (FreeMonoid.ofList w) = y.1} : Language A) := by
    ext w
    refine Iff.trans ?_ Language.mem_iSup.symm
    constructor
    · intro hw
      refine ⟨⟨Ψ (FreeMonoid.ofList w), ?_⟩, rfl⟩
      show P (RT.ap (Φ (FreeMonoid.ofList w)) ⟨q₀, hq₀⟩).1
      rw [RT.ap, transMor_apply, hfold]
      exact hw
    · rintro ⟨⟨y, hy⟩, hwy⟩
      have hwy' : Ψ (FreeMonoid.ofList w) = y := hwy
      show P (w.foldl δ q₀)
      have h1 : Φ (FreeMonoid.ofList w) = y.1 := congrArg Subtype.val hwy'
      have h2 := transMor_apply δ' w ⟨q₀, hq₀⟩
      rw [h1] at h2
      have h3 : (RT.ap y.1 ⟨q₀, hq₀⟩).1 = w.foldl δ q₀ := by
        exact (congrArg Subtype.val h2).trans (hfold w ⟨q₀, hq₀⟩)
      rw [← h3]
      exact hy
  rw [heq]
  exact HasHeightAtMost.iSup _ fun y => starFree_of_aperiodic hMap Ψ y.1

/-- **Star-freeness from a transformation-monoid certificate.** `qs` lists all states. -/
theorem starFree_of_dfa [DecidableEq Q] (qs : List Q) (hqs : ∀ q, q ∈ qs) (letters : List A)
    (hl : ∀ a, a ∈ letters) (δ : Q → A → Q) (R : List (Q → Q)) (N : ℕ)
    (hR : certOK qs letters δ R N = true) (q₀ : Q) (P : Q → Prop) :
    HasHeightAtMost {w : List A | P (w.foldl δ q₀)} 0 :=
  starFree_of_dfa_closed qs q₀ (hqs q₀) letters hl δ (fun _ _ _ => hqs _) R N hR P

end DFA

end Aperiodic

end GeneralizedStarHeight
