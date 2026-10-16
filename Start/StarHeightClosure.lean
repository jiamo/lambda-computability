import Start.StarHeightCommutative
import Start.StarHeightResetCount

/-!
# Closure properties of generalized star height

Pin, Straubing and Thérien (1992, "Some results on the generalized star-height problem"):

* `HasHeightAtMost.leftQuot`, `HasHeightAtMost.rightQuot`: letter quotients do not increase the
  generalized star height (structural induction on expressions).
* `HasHeightAtMost.reverse`: neither does reversal.
* `HasHeightAtMost.invAlph`: inverse images under alphabetic morphisms (every letter is sent to a
  letter or to the empty word) do not increase the generalized star height (PST Corollary 4.7).
-/

namespace GeneralizedStarHeight

universe u v

open scoped Computability

/-- The left quotient `a⁻¹L`. -/
def leftQuot {α : Type u} (a : α) (L : Language α) : Language α := {w | a :: w ∈ L}

/-- The right quotient `La⁻¹`. -/
def rightQuot {α : Type u} (a : α) (L : Language α) : Language α := {w | w ++ [a] ∈ L}

/-- The inverse image of `L` under the alphabetic morphism given by `φ` (`none` = empty word). -/
def invAlph {α : Type u} {β : Type v} (φ : α → Option β) (L : Language β) : Language α :=
  {w | w.filterMap φ ∈ L}

namespace HasHeightAtMost

variable {α : Type u}

/-! ### Reversal -/

lemma reverse {L : Language α} {n : ℕ} (h : HasHeightAtMost L n) :
    HasHeightAtMost L.reverse n := by
  obtain ⟨P, rfl, hP⟩ := h
  induction P generalizing n with
  | zero =>
      have : (Expression.zero : Expression α).language.reverse = 0 := by
        ext w; exact Iff.rfl
      rw [this]; exact HasHeightAtMost.zero n
  | one =>
      have : (Expression.one : Expression α).language.reverse = 1 := by
        ext w; simp [Expression.language, Language.mem_one]
      rw [this]; exact HasHeightAtMost.one n
  | letter a =>
      have : (Expression.letter a : Expression α).language.reverse = {[a]} := by
        ext w
        simp only [Expression.language, Language.mem_reverse]
        constructor
        · intro h
          have h' : w.reverse = [a] := h
          rw [← List.reverse_reverse w, h']; rfl
        · intro h
          have h' : w = [a] := h
          show w.reverse ∈ ({[a]} : Set (List α))
          rw [h']; rfl
      rw [this]; exact HasHeightAtMost.letter a n
  | union P Q ihP ihQ =>
      simp only [Expression.height] at hP
      have : (Expression.union P Q).language.reverse = P.language.reverse + Q.language.reverse := by
        ext w; exact Iff.rfl
      rw [this]
      exact (ihP (le_of_max_le_left hP)).union (ihQ (le_of_max_le_right hP))
  | concat P Q ihP ihQ =>
      simp only [Expression.height] at hP
      have : (Expression.concat P Q).language.reverse = Q.language.reverse * P.language.reverse := by
        simp [Expression.language, Language.reverse_mul]
      rw [this]
      exact (ihQ (le_of_max_le_right hP)).concat (ihP (le_of_max_le_left hP))
  | compl P ihP =>
      simp only [Expression.height] at hP
      have : (Expression.compl P).language.reverse = (P.language.reverse)ᶜ := by
        ext w; exact Iff.rfl
      rw [this]
      exact (ihP hP).compl
  | star P ihP =>
      simp only [Expression.height] at hP
      have : (Expression.star P).language.reverse = (P.language.reverse)∗ := by
        simp [Expression.language, Language.reverse_kstar]
      rw [this]
      have := (ihP (n := P.height) le_rfl).star
      exact this.mono hP

/-! ### Left quotients -/

lemma cons_mem_kstar_iff {E : Language α} {a : α} {w : List α} :
    a :: w ∈ E∗ ↔ ∃ x ∈ leftQuot a E, ∃ y ∈ E∗, x ++ y = w := by
  constructor
  · intro h
    obtain ⟨S, hS, hE⟩ := Language.mem_kstar.mp h
    induction S with
    | nil => simp at hS
    | cons s S ih =>
        rcases s with _ | ⟨b, s⟩
        · exact ih (by simpa using hS) (fun y hy => hE y (by simp [hy]))
        · simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hS
          obtain ⟨rfl, rfl⟩ := hS
          exact ⟨s, hE _ (by simp), S.flatten,
            Language.mem_kstar.mpr ⟨S, rfl, fun y hy => hE y (by simp [hy])⟩, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.mp hy
    refine Language.mem_kstar.mpr ⟨(a :: x) :: S, by simp, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hx
    · exact hS z hz

open Classical in
lemma leftQuot_mul (E F : Language α) (a : α) :
    leftQuot a (E * F) = leftQuot a E * F + (if [] ∈ E then leftQuot a F else 0) := by
  ext w
  rw [Language.mem_add]
  constructor
  · intro h
    have h' : a :: w ∈ E * F := h
    obtain ⟨x, hx, y, hy, hxy⟩ := Language.mem_mul.mp h'
    rcases x with _ | ⟨b, x⟩
    · right
      rw [if_pos hx]
      simp only [List.nil_append] at hxy
      show a :: w ∈ F
      rw [← hxy]; exact hy
    · left
      simp only [List.cons_append, List.cons.injEq] at hxy
      obtain ⟨rfl, rfl⟩ := hxy
      exact Language.mem_mul.mpr ⟨x, hx, y, hy, rfl⟩
  · rintro (h | h)
    · obtain ⟨x, hx, y, hy, rfl⟩ := Language.mem_mul.mp h
      exact Language.mem_mul.mpr ⟨a :: x, hx, y, hy, rfl⟩
    · split_ifs at h with hE
      · exact Language.mem_mul.mpr ⟨[], hE, a :: w, h, rfl⟩
      · exact absurd h (Language.notMem_zero _)

lemma leftQuot_kstar (E : Language α) (a : α) : leftQuot a (E∗) = leftQuot a E * E∗ := by
  ext w
  exact (cons_mem_kstar_iff).trans Language.mem_mul.symm

lemma leftQuot [DecidableEq α] {L : Language α} {n : ℕ} (h : HasHeightAtMost L n) (a : α) :
    HasHeightAtMost (GeneralizedStarHeight.leftQuot a L) n := by
  classical
  obtain ⟨P, rfl, hP⟩ := h
  induction P generalizing n with
  | zero =>
      have : GeneralizedStarHeight.leftQuot a (Expression.zero : Expression α).language = 0 := by
        ext w; exact Iff.rfl
      rw [this]; exact HasHeightAtMost.zero n
  | one =>
      have : GeneralizedStarHeight.leftQuot a (Expression.one : Expression α).language = 0 := by
        ext w
        constructor
        · intro h
          have h' : a :: w = [] := (Language.mem_one _).mp h
          simp at h'
        · intro h; exact absurd h (Language.notMem_zero _)
      rw [this]; exact HasHeightAtMost.zero n
  | letter b =>
      by_cases hab : a = b
      · subst hab
        have : GeneralizedStarHeight.leftQuot a (Expression.letter a : Expression α).language
            = 1 := by
          ext w
          simp only [GeneralizedStarHeight.leftQuot, Expression.language, Language.mem_one]
          constructor
          · intro h
            have h' : a :: w = [a] := h
            simpa using h'
          · intro h
            subst h; rfl
        rw [this]; exact HasHeightAtMost.one n
      · have : GeneralizedStarHeight.leftQuot a (Expression.letter b : Expression α).language
            = 0 := by
          ext w
          simp only [GeneralizedStarHeight.leftQuot, Expression.language]
          constructor
          · intro h
            have h' : a :: w = [b] := h
            simp at h'
            exact absurd h'.1 hab
          · intro h; exact absurd h (Language.notMem_zero _)
        rw [this]; exact HasHeightAtMost.zero n
  | union P Q ihP ihQ =>
      simp only [Expression.height] at hP
      have : GeneralizedStarHeight.leftQuot a (Expression.union P Q).language =
          GeneralizedStarHeight.leftQuot a P.language +
            GeneralizedStarHeight.leftQuot a Q.language := by
        ext w; exact Iff.rfl
      rw [this]
      exact (ihP (le_of_max_le_left hP)).union (ihQ (le_of_max_le_right hP))
  | concat P Q ihP ihQ =>
      simp only [Expression.height] at hP
      simp only [Expression.language]
      rw [leftQuot_mul]
      refine ((ihP (le_of_max_le_left hP)).concat ⟨Q, rfl, le_of_max_le_right hP⟩).union ?_
      split_ifs
      · exact ihQ (le_of_max_le_right hP)
      · exact HasHeightAtMost.zero n
  | compl P ihP =>
      simp only [Expression.height] at hP
      have : GeneralizedStarHeight.leftQuot a (Expression.compl P).language =
          (GeneralizedStarHeight.leftQuot a P.language)ᶜ := by
        ext w; exact Iff.rfl
      rw [this]
      exact (ihP hP).compl
  | star P ihP =>
      simp only [Expression.height] at hP
      simp only [Expression.language]
      rw [leftQuot_kstar]
      exact ((ihP (n := P.height) le_rfl).mono (by omega)).concat
        ((HasHeightAtMost.star (⟨P, rfl, le_rfl⟩ : HasHeightAtMost P.language P.height)).mono hP)

lemma rightQuot_eq (a : α) (L : Language α) :
    GeneralizedStarHeight.rightQuot a L =
      (GeneralizedStarHeight.leftQuot a L.reverse).reverse := by
  ext w
  show w ++ [a] ∈ L ↔ (a :: w.reverse).reverse ∈ L
  simp

lemma rightQuot [DecidableEq α] {L : Language α} {n : ℕ} (h : HasHeightAtMost L n) (a : α) :
    HasHeightAtMost (GeneralizedStarHeight.rightQuot a L) n := by
  rw [rightQuot_eq]
  exact (h.reverse.leftQuot a).reverse

/-! ### Inverse alphabetic morphisms -/

variable {β : Type v}

lemma invAlph_one (φ : α → Option β) :
    invAlph φ (1 : Language β) = allIn (fun b => φ b = none) := by
  ext w
  simp [invAlph, allIn, Language.mem_one, List.filterMap_eq_nil_iff]

lemma filterMap_eq_singleton {φ : α → Option β} {c : β} :
    ∀ w : List α, w.filterMap φ = [c] →
      ∃ x b z, w = x ++ b :: z ∧ (∀ d ∈ x, φ d = none) ∧ φ b = some c ∧ (∀ d ∈ z, φ d = none)
  | [], h => by simp at h
  | b :: w, h => by
      cases hb : φ b with
      | none =>
          rw [List.filterMap_cons, hb] at h
          obtain ⟨x, b', z, rfl, hx, hb', hz⟩ := filterMap_eq_singleton w h
          refine ⟨b :: x, b', z, rfl, ?_, hb', hz⟩
          intro d hd
          rcases List.mem_cons.mp hd with rfl | hd
          · exact hb
          · exact hx d hd
      | some d =>
          rw [List.filterMap_cons, hb] at h
          simp only [List.cons.injEq] at h
          obtain ⟨rfl, hw⟩ := h
          exact ⟨[], b, w, rfl, by simp, hb, List.filterMap_eq_nil_iff.mp hw⟩

lemma invAlph_letter (φ : α → Option β) (c : β) :
    invAlph φ ({[c]} : Language β) =
      allIn (fun b => φ b = none) * letters (fun b => φ b = some c) *
        allIn (fun b => φ b = none) := by
  ext w
  simp only [invAlph]
  constructor
  · intro h
    obtain ⟨x, b, z, rfl, hx, hb, hz⟩ := filterMap_eq_singleton w h
    exact Language.mem_mul.mpr ⟨x ++ [b], Language.mem_mul.mpr ⟨x, hx, [b], ⟨b, hb, rfl⟩, rfl⟩,
      z, hz, by simp⟩
  · intro h
    obtain ⟨xy, hxy, z, hz, rfl⟩ := Language.mem_mul.mp h
    obtain ⟨x, hx, y, ⟨b, hb, rfl⟩, rfl⟩ := Language.mem_mul.mp hxy
    have hx' : x.filterMap φ = [] := List.filterMap_eq_nil_iff.mpr hx
    have hz' : z.filterMap φ = [] := List.filterMap_eq_nil_iff.mpr hz
    show (x ++ [b] ++ z).filterMap φ ∈ ({[c]} : Language β)
    simp [List.filterMap_append, hx', hz', hb]
    rfl

lemma invAlph_mul (φ : α → Option β) (K L : Language β) :
    invAlph φ (K * L) = invAlph φ K * invAlph φ L := by
  ext w
  simp only [invAlph]
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp h
    obtain ⟨w₁, w₂, rfl, h1, h2⟩ := List.filterMap_eq_append_iff.mp huv.symm
    exact Language.mem_mul.mpr ⟨w₁, by show _ ∈ K; rw [h1]; exact hu, w₂,
      by show _ ∈ L; rw [h2]; exact hv, rfl⟩
  · intro h
    obtain ⟨w₁, h1, w₂, h2, rfl⟩ := Language.mem_mul.mp h
    exact Language.mem_mul.mpr ⟨_, h1, _, h2, (List.filterMap_append).symm⟩

lemma invAlph_kstar_aux (φ : α → Option β) (K : Language β) :
    ∀ (S : List (List β)) (w : List α), w.filterMap φ = S.flatten → (∀ y ∈ S, y ∈ K) →
      w ∈ (invAlph φ K)∗ ∨ w ∈ allIn (fun b => φ b = none)
  | [], w, h, _ => Or.inr (List.filterMap_eq_nil_iff.mp (by simpa using h))
  | s :: S, w, h, hK => by
      rw [List.flatten_cons] at h
      obtain ⟨w₁, w₂, rfl, h1, h2⟩ := List.filterMap_eq_append_iff.mp h
      have hw₁ : w₁ ∈ invAlph φ K := by
        show w₁.filterMap φ ∈ K
        rw [h1]; exact hK s (by simp)
      left
      rcases invAlph_kstar_aux φ K S w₂ h2 (fun y hy => hK y (by simp [hy])) with h' | h'
      · obtain ⟨T, rfl, hT⟩ := Language.mem_kstar.mp h'
        refine Language.mem_kstar.mpr ⟨w₁ :: T, by simp, ?_⟩
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hw₁
        · exact hT z hz
      · refine Language.mem_kstar.mpr ⟨[w₁ ++ w₂], by simp, ?_⟩
        intro z hz
        rw [List.mem_singleton] at hz
        subst hz
        show (w₁ ++ w₂).filterMap φ ∈ K
        rw [List.filterMap_append, h1, List.filterMap_eq_nil_iff.mpr h', List.append_nil]
        exact hK s (by simp)

lemma invAlph_kstar (φ : α → Option β) (K : Language β) :
    invAlph φ (K∗) = (invAlph φ K)∗ + allIn (fun b => φ b = none) := by
  ext w
  simp only [Language.mem_add]
  constructor
  · intro h
    obtain ⟨S, hS, hK⟩ := Language.mem_kstar.mp h
    exact invAlph_kstar_aux φ K S w hS hK
  · rintro (h | h)
    · obtain ⟨S, rfl, hS⟩ := Language.mem_kstar.mp h
      show (S.flatten).filterMap φ ∈ K∗
      rw [List.filterMap_flatten]
      exact Language.mem_kstar.mpr ⟨_, rfl, fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact hS z hz⟩
    · have : w.filterMap φ = [] := List.filterMap_eq_nil_iff.mpr h
      show w.filterMap φ ∈ K∗
      rw [this]
      exact Language.nil_mem_kstar _

/-- **Inverse alphabetic morphisms** (PST Corollary 4.7): if every letter is sent to a letter or to
the empty word, the inverse image has generalized star height at most that of the image. -/
lemma invAlph [Finite α] {L : Language β} {n : ℕ} (h : HasHeightAtMost L n) (φ : α → Option β) :
    HasHeightAtMost (GeneralizedStarHeight.invAlph φ L) n := by
  obtain ⟨P, rfl, hP⟩ := h
  induction P generalizing n with
  | zero =>
      have : GeneralizedStarHeight.invAlph φ (Expression.zero : Expression β).language = 0 := by
        ext w; exact Iff.rfl
      rw [this]; exact HasHeightAtMost.zero n
  | one =>
      simp only [Expression.language]
      rw [invAlph_one]; exact allIn_height _ n
  | letter c =>
      simp only [Expression.language]
      rw [invAlph_letter]
      exact ((allIn_height _ n).concat (letters_height _ n)).concat (allIn_height _ n)
  | union P Q ihP ihQ =>
      simp only [Expression.height] at hP
      have : GeneralizedStarHeight.invAlph φ (Expression.union P Q).language =
          GeneralizedStarHeight.invAlph φ P.language +
            GeneralizedStarHeight.invAlph φ Q.language := by
        ext w; exact Iff.rfl
      rw [this]
      exact (ihP (le_of_max_le_left hP)).union (ihQ (le_of_max_le_right hP))
  | concat P Q ihP ihQ =>
      simp only [Expression.height] at hP
      simp only [Expression.language]
      rw [invAlph_mul]
      exact (ihP (le_of_max_le_left hP)).concat (ihQ (le_of_max_le_right hP))
  | compl P ihP =>
      simp only [Expression.height] at hP
      have : GeneralizedStarHeight.invAlph φ (Expression.compl P).language =
          (GeneralizedStarHeight.invAlph φ P.language)ᶜ := by
        ext w; exact Iff.rfl
      rw [this]
      exact (ihP hP).compl
  | star P ihP =>
      simp only [Expression.height] at hP
      simp only [Expression.language]
      rw [invAlph_kstar]
      exact ((ihP (n := P.height) le_rfl).star.mono hP).union (allIn_height _ n)

end HasHeightAtMost

end GeneralizedStarHeight
