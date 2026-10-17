import Start.StarHeightHeight

/-!
# Renaming the alphabet preserves generalized star height

A bijection `e : α ≃ β` of alphabets induces a bijection `List.map e` of words, hence an
isomorphism `Language.map e` of the Boolean algebras of languages that also respects
concatenation and the Kleene star.  Renaming an expression letter by letter therefore preserves
its height:

* `Expression.rename`, `Expression.height_rename`, `Expression.language_rename`;
* `HasHeightAtMost.map_equiv`: `HasHeightAtMost L n → HasHeightAtMost (Language.map e L) n`;
* `HasHeightAtMost.comap_equiv`: the same for the preimage `{w | List.map e w ∈ L}`.
-/

namespace GeneralizedStarHeight

universe u v

namespace Expression

variable {α : Type u} {β : Type v}

/-- Renaming the letters of an expression. -/
def rename (e : α → β) : Expression α → Expression β
  | .zero => .zero
  | .one => .one
  | .letter a => .letter (e a)
  | .union P Q => .union (P.rename e) (Q.rename e)
  | .concat P Q => .concat (P.rename e) (Q.rename e)
  | .compl P => .compl (P.rename e)
  | .star P => .star (P.rename e)

lemma height_rename (e : α → β) : ∀ P : Expression α, (P.rename e).height = P.height
  | .zero | .one | .letter _ => rfl
  | .union P Q => by
      rw [rename, height, height, height_rename e P, height_rename e Q]
  | .concat P Q => by
      rw [rename, height, height, height_rename e P, height_rename e Q]
  | .compl P => by rw [rename, height, height, height_rename e P]
  | .star P => by rw [rename, height, height, height_rename e P]

open scoped Computability

lemma map_compl (e : α ≃ β) (L : Language α) : Language.map e Lᶜ = (Language.map e L)ᶜ := by
  have hb : Function.Bijective (List.map e) := by
    constructor
    · exact List.map_injective_iff.mpr e.injective
    · intro w
      exact ⟨w.map e.symm, by simp⟩
  exact Set.image_compl_eq hb

lemma map_letter (e : α ≃ β) (a : α) :
    Language.map e ({[a]} : Language α) = ({[e a]} : Language β) := by
  show Set.image (List.map e) {[a]} = {[e a]}
  simp

lemma language_rename (e : α ≃ β) : ∀ P : Expression α,
    (P.rename e).language = Language.map e P.language
  | .zero => (map_zero _).symm
  | .one => (map_one _).symm
  | .letter a => (map_letter e a).symm
  | .union P Q => by
      rw [rename, language, language, language_rename e P, language_rename e Q, map_add]
  | .concat P Q => by
      rw [rename, language, language, language_rename e P, language_rename e Q, map_mul]
  | .compl P => by
      rw [rename, language, language, language_rename e P, map_compl]
  | .star P => by
      rw [rename, language, language, language_rename e P, Language.map_kstar]

end Expression

/-- **Renaming the alphabet by a bijection preserves generalized star height.** -/
theorem HasHeightAtMost.map_equiv {α : Type u} {β : Type v} {L : Language α} {n : ℕ}
    (e : α ≃ β) (h : HasHeightAtMost L n) : HasHeightAtMost (Language.map e L) n := by
  obtain ⟨P, rfl, hP⟩ := h
  exact ⟨P.rename e, Expression.language_rename e P, by rwa [Expression.height_rename]⟩

/-- **Reading the letters through a bijection preserves generalized star height.** -/
theorem HasHeightAtMost.comap_equiv {α : Type u} {β : Type v} {L : Language β} {n : ℕ}
    (e : α ≃ β) (h : HasHeightAtMost L n) :
    HasHeightAtMost ({w : List α | List.map e w ∈ L} : Language α) n := by
  have heq : ({w : List α | List.map e w ∈ L} : Language α) = Language.map e.symm L := by
    ext w
    show List.map e w ∈ L ↔ w ∈ Set.image (List.map e.symm) L
    constructor
    · intro hw
      exact ⟨List.map e w, hw, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      have hvv : List.map e (List.map e.symm v) = v := by simp
      rw [hvv]
      exact hv
  rw [heq]
  exact h.map_equiv e.symm


/-! ### Reading the letters through an arbitrary map -/

section Comap

open scoped Computability

variable {α : Type u} {β : Type v} (f : α → β)

/-- The words whose image under `f` lies in `L`. -/
def comapL (L : Language β) : Language α := {w : List α | List.map f w ∈ L}

lemma mem_comapL {L : Language β} {w : List α} : w ∈ comapL f L ↔ List.map f w ∈ L := Iff.rfl

lemma comapL_zero : comapL f (0 : Language β) = 0 := by
  ext w
  exact Iff.rfl

lemma comapL_one : comapL f (1 : Language β) = 1 := by
  ext w
  constructor
  · intro hw
    have h : List.map f w = [] := hw
    exact List.map_eq_nil_iff.mp h
  · intro hw
    have h : w = [] := hw
    rw [show (comapL f 1 : Set (List α)) = {w | List.map f w ∈ (1 : Language β)} from rfl]
    rw [h]
    rfl

lemma comapL_add (L M : Language β) : comapL f (L + M) = comapL f L + comapL f M := rfl

lemma comapL_compl (L : Language β) : comapL f Lᶜ = (comapL f L)ᶜ := rfl

lemma comapL_mul (L M : Language β) : comapL f (L * M) = comapL f L * comapL f M := by
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, v, hv, huv⟩ := Language.mem_mul.mp hw
    refine Language.mem_mul.mpr ⟨w.take u.length, ?_, w.drop u.length, ?_,
      List.take_append_drop _ _⟩
    · show List.map f (w.take u.length) ∈ L
      rw [List.map_take, ← huv, List.take_left]
      exact hu
    · show List.map f (w.drop u.length) ∈ M
      rw [List.map_drop, ← huv, List.drop_left]
      exact hv
  · intro hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hw
    show List.map f (u ++ v) ∈ L * M
    rw [List.map_append]
    exact Language.mem_mul.mpr ⟨List.map f u, hu, List.map f v, hv, rfl⟩

lemma comapL_pow (g : α → β) (L : Language β) : ∀ n : ℕ, comapL g (L ^ n) = (comapL g L) ^ n
  | 0 => by rw [pow_zero, pow_zero, comapL_one]
  | n + 1 => by rw [pow_succ, pow_succ, comapL_mul, comapL_pow g L n]

lemma comapL_kstar (L : Language β) : comapL f L∗ = (comapL f L)∗ := by
  rw [Language.kstar_eq_iSup_pow, Language.kstar_eq_iSup_pow]
  ext w
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := Language.mem_iSup.mp (mem_comapL f |>.mp hw)
    exact Language.mem_iSup.mpr ⟨n, by rw [← comapL_pow f L n]; exact hn⟩
  · intro hw
    obtain ⟨n, hn⟩ := Language.mem_iSup.mp hw
    rw [← comapL_pow f L n] at hn
    exact Language.mem_iSup.mpr ⟨n, hn⟩

/-- **Reading the letters through an arbitrary map of a finite alphabet preserves generalized
star height.** -/
theorem HasHeightAtMost.comap [Finite α] {L : Language β} {n : ℕ}
    (h : HasHeightAtMost L n) : HasHeightAtMost (comapL f L) n := by
  obtain ⟨P, rfl, hP⟩ := h
  refine HasHeightAtMost.mono ?_ hP
  clear hP n
  induction P with
  | zero =>
      rw [show (Expression.zero : Expression β).language = 0 from rfl, comapL_zero]
      exact HasHeightAtMost.zero _
  | one =>
      rw [show (Expression.one : Expression β).language = 1 from rfl, comapL_one]
      exact HasHeightAtMost.one _
  | letter b =>
      have hfin : (comapL f (Expression.letter b).language : Set (List α)).Finite := by
        refine Set.Finite.subset (Set.finite_range (fun a : α => [a])) ?_
        rintro w hw
        have hw' : List.map f w = [b] := hw
        match w, hw' with
        | [a], _ => exact ⟨a, rfl⟩
      exact HasHeightAtMost.finite _ hfin _
  | union P Q ihP ihQ =>
      rw [show (P.union Q).language = P.language + Q.language from rfl, comapL_add]
      exact (ihP.mono (le_max_left _ _)).union (ihQ.mono (le_max_right _ _))
  | concat P Q ihP ihQ =>
      rw [show (P.concat Q).language = P.language * Q.language from rfl, comapL_mul]
      exact (ihP.mono (le_max_left _ _)).concat (ihQ.mono (le_max_right _ _))
  | compl P ih =>
      rw [show (P.compl).language = P.languageᶜ from rfl, comapL_compl]
      exact ih.compl
  | star P ih =>
      rw [show (P.star).language = P.language∗ from rfl, comapL_kstar]
      exact ih.star

end Comap

end GeneralizedStarHeight
