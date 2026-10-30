/-
**Håstad's switching lemma, by Razborov's counting argument.**

Restrictions are counted, not measured.

* `Restriction n := Fin n → Option Bool`; `R n ℓ` is the finite set of restrictions with exactly
  `ℓ` free variables.
* A term is a list of literals `(i, b)` (the literal `xᵢ = b`), a DNF a list of terms.
  `Term.WellFormed`: the variables of a term are distinct.
* `DTree n`: decision trees; `Computes T F ρ`: `T` computes `F` on every input that extends `ρ`.
* `cdt F ρ`: the canonical decision tree of `F` under `ρ` (`cdt_computes`).
* `encode F s ρ`: Razborov's encoding of a bad restriction `ρ` (one whose canonical decision tree
  has depth at least `s`) as a pair: a restriction with `s` fewer free variables, and a code word
  of `s` letters, each a position `< k` in a term and two bits.
* `encode_injOn`: the encoding is injective on bad restrictions; `encode_mem`: it lands in
  `R n (ℓ - s) ×ˢ codes k s`.
* `card_bad_le`: the number of `ρ ∈ R n ℓ` under which a `k`-DNF has no decision tree of depth
  `< s` is at most `|R n (ℓ - s)| · (4k)^s`.
* `switching_lemma`: for `2ℓ ≤ n`, the fraction of such restrictions in `R n ℓ` is at most
  `(16 k ℓ / n)^s`, i.e. `(c p k)^s` with `p = ℓ / n` and `c = 16`.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity.Switching

open Finset

variable {n : ℕ}

/-- A restriction: each variable is fixed to a bit or left free (`none`). -/
abbrev Restriction (n : ℕ) := Fin n → Option Bool

/-- A literal `(i, b)`: the variable `xᵢ` takes the value `b`. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- A term (conjunction of literals). -/
abbrev Term (n : ℕ) := List (Lit n)

/-- A DNF (disjunction of terms). -/
abbrev DNF (n : ℕ) := List (Term n)

/-- The free variables of a restriction. -/
def freeSet (ρ : Restriction n) : Finset (Fin n) := univ.filter (fun i => ρ i = none)

/-- The restrictions with exactly `ℓ` free variables. -/
def R (n ℓ : ℕ) : Finset (Restriction n) := univ.filter (fun ρ => (freeSet ρ).card = ℓ)

namespace Term

def eval (C : Term n) (x : Fin n → Bool) : Bool := C.all (fun l => x l.1 == l.2)

/-- Some literal of the term is set to the wrong value. -/
def Falsified (C : Term n) (ρ : Restriction n) : Prop := ∃ l ∈ C, ρ l.1 = some (!l.2)

/-- Every literal of the term is set to the right value. -/
def Satisfied (C : Term n) (ρ : Restriction n) : Prop := ∀ l ∈ C, ρ l.1 = some l.2

instance (C : Term n) (ρ : Restriction n) : Decidable (C.Falsified ρ) := by
  unfold Falsified; infer_instance

instance (C : Term n) (ρ : Restriction n) : Decidable (C.Satisfied ρ) := by
  unfold Satisfied; infer_instance

/-- The variables of a term are distinct. -/
def WellFormed (C : Term n) : Prop := (C.map Prod.fst).Nodup

/-- The literals of the term whose variable is free, with their positions in the term. -/
def freeLits (C : Term n) (ρ : Restriction n) : List (Lit n × ℕ) :=
  C.zipIdx.filter (fun p => ρ p.1.1 = none)

/-- The free variables of the term. -/
def freeVars (C : Term n) (ρ : Restriction n) : List (Fin n) :=
  (C.freeLits ρ).map (fun p => p.1.1)

end Term

def DNF.eval (F : DNF n) (x : Fin n → Bool) : Bool := F.any (fun C => C.eval x)

/-- The input `x` extends the restriction `ρ`. -/
def Extends (ρ : Restriction n) (x : Fin n → Bool) : Prop := ∀ i b, ρ i = some b → x i = b

/-- Decision trees over `n` variables. -/
inductive DTree (n : ℕ)
  | leaf (b : Bool)
  | node (i : Fin n) (t₀ t₁ : DTree n)

namespace DTree

def eval : DTree n → (Fin n → Bool) → Bool
  | leaf b, _ => b
  | node i t₀ t₁, x => if x i then t₁.eval x else t₀.eval x

def depth : DTree n → ℕ
  | leaf _ => 0
  | node _ t₀ t₁ => max t₀.depth t₁.depth + 1

end DTree

/-- `T` computes `F` on every input extending `ρ`. -/
def Computes (T : DTree n) (F : DNF n) (ρ : Restriction n) : Prop :=
  ∀ x, Extends ρ x → T.eval x = F.eval x

/-- Fix a variable. -/
def setVar (ρ : Restriction n) (i : Fin n) (b : Bool) : Restriction n :=
  Function.update ρ i (some b)

/-- Query the variables of `K` one after the other, then continue with `cont`. -/
def queryAll (cont : Restriction n → DTree n) : List (Fin n) → Restriction n → DTree n
  | [], ρ => cont ρ
  | i :: K, ρ => .node i (queryAll cont K (setVar ρ i false)) (queryAll cont K (setVar ρ i true))

/-- The canonical decision tree of a DNF under a restriction. -/
def cdt : DNF n → Restriction n → DTree n
  | [], _ => .leaf false
  | C :: F, ρ =>
      if C.Falsified ρ then cdt F ρ
      else if C.Satisfied ρ then .leaf true
      else queryAll (fun ρ' => if C.Satisfied ρ' then .leaf true else cdt F ρ') (C.freeVars ρ) ρ

/-- `ρ'` is obtained from `ρ` by fixing the variables of `K` (and nothing else). -/
def ExtOn (K : List (Fin n)) (ρ ρ' : Restriction n) : Prop :=
  ∀ i, (i ∈ K → ρ' i ≠ none) ∧ (i ∉ K → ρ' i = ρ i)

/-! ### The canonical decision tree computes the DNF -/

theorem ExtOn.cons {K : List (Fin n)} {ρ ρ' : Restriction n} {i : Fin n} {b : Bool}
    (h : ExtOn K (setVar ρ i b) ρ') : ExtOn (i :: K) ρ ρ' := by
  intro j
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · by_cases hjK : j ∈ K
    · exact (h j).1 hjK
    · have hji : j = i := by simpa [hjK] using hj
      subst hji
      rw [(h j).2 hjK]
      simp [setVar]
  · simp only [List.mem_cons, not_or] at hj
    rw [(h j).2 hj.2]
    simp [setVar, hj.1]

theorem queryAll_eval (cont : Restriction n → DTree n) (K : List (Fin n)) (ρ : Restriction n)
    (x : Fin n → Bool) : ∃ ρ', ExtOn K ρ ρ' ∧ (∀ i ∈ K, ρ' i = some (x i)) ∧
      (queryAll cont K ρ).eval x = (cont ρ').eval x := by
  induction K generalizing ρ with
  | nil => exact ⟨ρ, fun i => ⟨by simp, fun _ => rfl⟩, by simp, rfl⟩
  | cons i K ih =>
      obtain ⟨ρ', hext, hval, heval⟩ := ih (setVar ρ i (x i))
      refine ⟨ρ', hext.cons, fun j hj => ?_, ?_⟩
      · by_cases hjK : j ∈ K
        · exact hval j hjK
        · have hji : j = i := by simpa [hjK] using hj
          subst hji
          rw [(hext j).2 hjK]
          simp [setVar]
      · simp only [queryAll, DTree.eval]
        cases hx : x i <;> rw [hx] at heval <;> simpa using heval

theorem queryAll_depth_le (cont : Restriction n → DTree n) (K : List (Fin n))
    (ρ : Restriction n) (d : ℕ) (h : ∀ ρ', ExtOn K ρ ρ' → (cont ρ').depth ≤ d) :
    (queryAll cont K ρ).depth ≤ K.length + d := by
  induction K generalizing ρ with
  | nil => simpa [queryAll] using h ρ (fun i => ⟨by simp, fun _ => rfl⟩)
  | cons i K ih =>
      have h0 := ih (setVar ρ i false) (fun ρ' h' => h ρ' h'.cons)
      have h1 := ih (setVar ρ i true) (fun ρ' h' => h ρ' h'.cons)
      simp only [queryAll, DTree.depth, List.length_cons]
      omega

theorem Term.freeLits_map_fst (C : Term n) (ρ : Restriction n) :
    (C.freeLits ρ).map Prod.fst = C.filter (fun l => ρ l.1 = none) := by
  unfold Term.freeLits
  rw [show (fun p : Lit n × ℕ => decide (ρ p.1.1 = none)) =
    (fun l : Lit n => decide (ρ l.1 = none)) ∘ Prod.fst from rfl, ← List.filter_map]
  simp

theorem Term.mem_freeVars {C : Term n} {ρ : Restriction n} {l : Lit n} (hl : l ∈ C)
    (hρ : ρ l.1 = none) : l.1 ∈ C.freeVars ρ := by
  have : l ∈ (C.freeLits ρ).map Prod.fst := by
    rw [Term.freeLits_map_fst]
    simp [hl, hρ]
  unfold Term.freeVars
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 this
  exact List.mem_map.2 ⟨p, hp, rfl⟩

theorem Term.eval_false_of_falsified {C : Term n} {ρ : Restriction n} {x : Fin n → Bool}
    (hx : Extends ρ x) (h : C.Falsified ρ) : C.eval x = false := by
  obtain ⟨l, hl, hρ⟩ := h
  have := hx _ _ hρ
  unfold Term.eval
  rw [List.all_eq_false]
  exact ⟨l, hl, by simp [this]⟩

theorem Term.eval_true_of_satisfied {C : Term n} {ρ : Restriction n} {x : Fin n → Bool}
    (hx : Extends ρ x) (h : C.Satisfied ρ) : C.eval x = true := by
  unfold Term.eval
  rw [List.all_eq_true]
  intro l hl
  simp [hx _ _ (h l hl)]

theorem cdt_computes (F : DNF n) (ρ : Restriction n) : Computes (cdt F ρ) F ρ := by
  induction F generalizing ρ with
  | nil => intro x _; simp [cdt, DTree.eval, DNF.eval]
  | cons C F ih =>
      intro x hx
      have hcons : DNF.eval (C :: F) x = (C.eval x || DNF.eval F x) := by
        simp [DNF.eval]
      rw [hcons]
      unfold cdt
      split_ifs with h1 h2
      · rw [ih ρ x hx, Term.eval_false_of_falsified hx h1]
        simp
      · simp [DTree.eval, Term.eval_true_of_satisfied hx h2]
      · obtain ⟨ρ', hext, hval, heval⟩ := queryAll_eval
          (fun ρ' => if C.Satisfied ρ' then .leaf true else cdt F ρ') (C.freeVars ρ) ρ x
        rw [heval]
        have hx' : Extends ρ' x := by
          intro i b hi
          by_cases hiK : i ∈ C.freeVars ρ
          · rw [hval i hiK] at hi
            exact Option.some.inj hi
          · rw [(hext i).2 hiK] at hi
            exact hx i b hi
        split_ifs with h3
        · simp [DTree.eval, Term.eval_true_of_satisfied hx' h3]
        · have hf : C.Falsified ρ' := by
            simp only [Term.Satisfied, not_forall] at h3
            obtain ⟨l, hl, hne⟩ := h3
            refine ⟨l, hl, ?_⟩
            have hset : ρ' l.1 ≠ none := by
              by_cases hK : l.1 ∈ C.freeVars ρ
              · exact (hext _).1 hK
              · rw [(hext _).2 hK]
                intro hnone
                exact hK (Term.mem_freeVars hl hnone)
            obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hset
            rw [hb] at hne ⊢
            cases b <;> cases hl2 : l.2 <;> simp_all
          rw [ih ρ' x hx', Term.eval_false_of_falsified hx' hf]
          simp

/-! ### Razborov's encoding -/

/-- Fix the variables of the listed literals to the values that satisfy them. -/
def setLits (ρ : Restriction n) (L : List (Lit n × ℕ)) : Restriction n := fun i =>
  match L.find? (fun p => p.1.1 = i) with
  | some p => some p.1.2
  | none => ρ i

/-- The code word of a block: for each listed literal, its position in its term, whether it is
the last of the block, and the value read on the path. -/
def blockCode (ρ' : Restriction n) (L : List (Lit n × ℕ)) : List (ℕ × Bool × Bool) :=
  L.mapIdx (fun i p => (p.2, decide (i + 1 = L.length), (ρ' p.1.1).getD false))

open Classical in
/-- The path chosen in the canonical decision tree: an extension on the free variables of `C`
that falsifies `C` and below which the tree still has depth at least `s'`. -/
noncomputable def choosePath (C : Term n) (F : DNF n) (s' : ℕ) (ρ : Restriction n) :
    Restriction n :=
  Classical.epsilon (fun ρ' => ExtOn (C.freeVars ρ) ρ ρ' ∧ ¬ C.Satisfied ρ' ∧
    s' ≤ (cdt F ρ').depth)

open Classical in
/-- **Razborov's encoding** of a restriction under which the canonical decision tree of `F` has
depth at least `s`. -/
noncomputable def encode : DNF n → ℕ → Restriction n → Restriction n × List (ℕ × Bool × Bool)
  | [], _, ρ => (ρ, [])
  | C :: F, s, ρ =>
      if C.Falsified ρ then encode F s ρ
      else if (C.freeLits ρ).length < s then
        let ρ' := choosePath C F (s - (C.freeLits ρ).length) ρ
        let r := encode F (s - (C.freeLits ρ).length) ρ'
        (setLits r.1 (C.freeLits ρ), blockCode ρ' (C.freeLits ρ) ++ r.2)
      else
        (setLits ρ ((C.freeLits ρ).take s), blockCode ρ ((C.freeLits ρ).take s))

/-- The code words: lists of `s` letters `(j, b, b')` with `j < k`. -/
def codes (k s : ℕ) : Finset (List (ℕ × Bool × Bool)) :=
  (univ : Finset (Fin s → Fin k × Bool × Bool)).image
    (fun f => List.ofFn (fun i => ((f i).1.val, (f i).2.1, (f i).2.2)))

theorem mem_codes {k : ℕ} (l : List (ℕ × Bool × Bool)) (h : ∀ e ∈ l, e.1 < k) :
    l ∈ codes k l.length := by
  refine mem_image.2 ⟨fun i => (⟨l[i].1, h _ (List.getElem_mem _)⟩, l[i].2.1, l[i].2.2),
    mem_univ _, ?_⟩
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem card_codes_le (k s : ℕ) : (codes k s).card ≤ (4 * k) ^ s := by
  refine (card_image_le).trans ?_
  simp only [card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  exact le_of_eq (by ring)

/-- A `k`-DNF: well-formed terms of length at most `k`. -/
def IsKDNF (k : ℕ) (F : DNF n) : Prop := ∀ C ∈ F, C.length ≤ k ∧ C.WellFormed


/-! ### Lemmas for the encoding -/

/-- `ρ'` refines `ρ`: every variable fixed by `ρ` is fixed to the same value by `ρ'`. -/
def Refines (ρ ρ' : Restriction n) : Prop := ∀ i b, ρ i = some b → ρ' i = some b

section Helpers

variable {C : Term n} {ρ : Restriction n}

theorem mem_freeLits {p : Lit n × ℕ} : p ∈ C.freeLits ρ ↔ p ∈ C.zipIdx ∧ ρ p.1.1 = none := by
  simp [Term.freeLits, List.mem_filter]

theorem mem_of_mem_zipIdx {p : Lit n × ℕ} (h : p ∈ C.zipIdx) : p.1 ∈ C ∧ p.2 < C.length := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  exact ⟨List.mem_of_getElem? h, (List.getElem?_eq_some_iff.1 h).1⟩

theorem exists_mem_zipIdx {l : Lit n} (hl : l ∈ C) : ∃ j, (l, j) ∈ C.zipIdx := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hl
  exact ⟨i, List.mem_zipIdx_iff_getElem?.2 hi⟩

theorem freeVars_eq (C : Term n) (ρ : Restriction n) :
    C.freeVars ρ = (C.freeLits ρ).map (fun p => p.1.1) := rfl

theorem vars_nodup_of_sublist (hC : C.WellFormed) {T : List (Lit n × ℕ)}
    (hT : T.Sublist (C.freeLits ρ)) : (T.map (fun p => p.1.1)).Nodup := by
  have h1 : (C.freeLits ρ).map (fun p => p.1.1) = ((C.freeLits ρ).map Prod.fst).map Prod.fst := by
    simp [List.map_map, Function.comp_def]
  have h2 : ((C.freeLits ρ).map (fun p => p.1.1)).Nodup := by
    rw [h1, Term.freeLits_map_fst]
    exact hC.sublist (List.filter_sublist.map _)
  exact h2.sublist (hT.map _)

theorem lit_eq_of_var_eq (hC : C.WellFormed) {l l' : Lit n} (hl : l ∈ C) (hl' : l' ∈ C)
    (h : l.1 = l'.1) : l = l' :=
  List.inj_on_of_nodup_map hC hl hl' h

theorem value_of_not_falsified (hfal : ¬ C.Falsified ρ) {l : Lit n} (hl : l ∈ C) {b : Bool}
    (hb : ρ l.1 = some b) : b = l.2 := by
  by_contra hne
  apply hfal
  refine ⟨l, hl, ?_⟩
  rw [hb]
  cases b <;> cases h2 : l.2 <;> simp_all

theorem satisfied_of_freeLits_nil (hfal : ¬ C.Falsified ρ) (h : C.freeLits ρ = []) :
    C.Satisfied ρ := by
  intro l hl
  obtain ⟨j, hj⟩ := exists_mem_zipIdx hl
  have hne : ρ l.1 ≠ none := fun hn => by
    have : (l, j) ∈ C.freeLits ρ := mem_freeLits.2 ⟨hj, hn⟩
    rw [h] at this
    simp at this
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hne
  rw [hb, value_of_not_falsified hfal hl hb]

theorem eq_of_positions {L₁ L₂ : List (Lit n × ℕ)} (h₁ : ∀ p ∈ L₁, p ∈ C.zipIdx)
    (h₂ : ∀ p ∈ L₂, p ∈ C.zipIdx) (h : L₁.map Prod.snd = L₂.map Prod.snd) : L₁ = L₂ := by
  have key : ∀ L : List (Lit n × ℕ), (∀ p ∈ L, p ∈ C.zipIdx) →
      L.map (fun p => (some p.1, p.2)) = (L.map Prod.snd).map (fun j => (C[j]?, j)) := by
    intro L hL
    rw [List.map_map]
    apply List.map_congr_left
    intro p hp
    simp [List.mem_zipIdx_iff_getElem?.1 (hL p hp)]
  have hinj : Function.Injective (fun p : Lit n × ℕ => (some p.1, p.2)) := by
    intro a b hab
    simp only [Prod.mk.injEq, Option.some.injEq] at hab
    exact Prod.ext hab.1 hab.2
  apply List.map_injective_iff.2 hinj
  rw [key L₁ h₁, key L₂ h₂, h]

end Helpers

theorem setLits_of_not_mem {L : List (Lit n × ℕ)} {i : Fin n}
    (h : i ∉ L.map (fun p => p.1.1)) (ρ : Restriction n) : setLits ρ L i = ρ i := by
  unfold setLits
  rw [List.find?_eq_none.2]
  intro p hp hpi
  exact h (List.mem_map.2 ⟨p, hp, by simpa using hpi⟩)

theorem setLits_of_mem {L : List (Lit n × ℕ)} (hL : (L.map (fun p => p.1.1)).Nodup)
    {p : Lit n × ℕ} (hp : p ∈ L) (ρ : Restriction n) : setLits ρ L p.1.1 = some p.1.2 := by
  unfold setLits
  cases hf : L.find? (fun q => decide (q.1.1 = p.1.1)) with
  | none => exact absurd (List.find?_eq_none.1 hf p hp) (by simp)
  | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have hqp := List.find?_some hf
      simp only [decide_eq_true_eq] at hqp
      have := List.inj_on_of_nodup_map hL hq hp hqp
      simp [this]

theorem setLits_ne_none {L : List (Lit n × ℕ)} {i : Fin n} (h : i ∈ L.map (fun p => p.1.1))
    (ρ : Restriction n) : setLits ρ L i ≠ none := by
  unfold setLits
  cases hf : L.find? (fun q => decide (q.1.1 = i)) with
  | none =>
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact absurd (List.find?_eq_none.1 hf p hp) (by simp)
  | some q => simp

theorem setLits_nil (ρ : Restriction n) : setLits ρ [] = ρ := by
  funext i
  simp [setLits]

theorem freeSet_setLits (ρ : Restriction n) (L : List (Lit n × ℕ)) :
    freeSet (setLits ρ L) = freeSet ρ \ (L.map (fun p => p.1.1)).toFinset := by
  ext i
  simp only [freeSet, mem_filter, mem_univ, true_and, mem_sdiff, List.mem_toFinset]
  by_cases hi : i ∈ L.map (fun p => p.1.1)
  · simp only [hi, not_true_eq_false, and_false, iff_false]
    exact setLits_ne_none hi ρ
  · simp only [hi, not_false_eq_true, and_true]
    rw [setLits_of_not_mem hi]

theorem blockCode_length (ρ' : Restriction n) (L : List (Lit n × ℕ)) :
    (blockCode ρ' L).length = L.length := by
  simp [blockCode]

theorem blockCode_map_fst (ρ' : Restriction n) (L : List (Lit n × ℕ)) :
    (blockCode ρ' L).map Prod.fst = L.map Prod.snd := by
  apply List.ext_getElem?
  intro i
  simp only [blockCode, List.getElem?_map, List.getElem?_mapIdx]
  cases L[i]? <;> rfl

theorem blockCode_map_val (ρ' : Restriction n) (L : List (Lit n × ℕ)) :
    (blockCode ρ' L).map (fun e => e.2.2) = L.map (fun p => (ρ' p.1.1).getD false) := by
  apply List.ext_getElem?
  intro i
  simp only [blockCode, List.getElem?_map, List.getElem?_mapIdx]
  cases L[i]? <;> rfl

theorem blockCode_last (ρ' : Restriction n) (L : List (Lit n × ℕ))
    (r : List (ℕ × Bool × Bool)) {i : ℕ} (hi : i < L.length) :
    ((blockCode ρ' L ++ r)[i]?).map (fun e => e.2.1) = some (decide (i + 1 = L.length)) := by
  rw [List.getElem?_append_left (by rw [blockCode_length]; exact hi)]
  simp [blockCode, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]

theorem cdt_falsified {C : Term n} {F : DNF n} {ρ : Restriction n} (h : C.Falsified ρ) :
    cdt (C :: F) ρ = cdt F ρ := by
  rw [cdt, ite_eq_left h]

theorem encode_falsified {C : Term n} {F : DNF n} {s : ℕ} {ρ : Restriction n}
    (h : C.Falsified ρ) : encode (C :: F) s ρ = encode F s ρ := by
  rw [encode, ite_eq_left h]

theorem encode_lt {C : Term n} {F : DNF n} {s : ℕ} {ρ : Restriction n}
    (h : ¬ C.Falsified ρ) (hlt : (C.freeLits ρ).length < s) :
    encode (C :: F) s ρ =
      (setLits (encode F (s - (C.freeLits ρ).length)
          (choosePath C F (s - (C.freeLits ρ).length) ρ)).1 (C.freeLits ρ),
        blockCode (choosePath C F (s - (C.freeLits ρ).length) ρ) (C.freeLits ρ) ++
          (encode F (s - (C.freeLits ρ).length)
            (choosePath C F (s - (C.freeLits ρ).length) ρ)).2) := by
  rw [encode, ite_eq_right h, ite_eq_left hlt]

theorem encode_ge {C : Term n} {F : DNF n} {s : ℕ} {ρ : Restriction n}
    (h : ¬ C.Falsified ρ) (hlt : ¬ (C.freeLits ρ).length < s) :
    encode (C :: F) s ρ = (setLits ρ ((C.freeLits ρ).take s),
      blockCode ρ ((C.freeLits ρ).take s)) := by
  rw [encode, ite_eq_right h, ite_eq_right hlt]

theorem encode_zero (F : DNF n) (ρ : Restriction n) : encode F 0 ρ = (ρ, []) := by
  induction F with
  | nil => rfl
  | cons C F ih =>
      by_cases h : C.Falsified ρ
      · rw [encode_falsified h, ih]
      · rw [encode_ge h (by omega)]
        simp [setLits_nil, blockCode]

theorem choosePath_spec {C : Term n} {F : DNF n} {s : ℕ} {ρ : Restriction n}
    (hfal : ¬ C.Falsified ρ) (hlt : (C.freeLits ρ).length < s)
    (hbad : s ≤ (cdt (C :: F) ρ).depth) :
    ExtOn (C.freeVars ρ) ρ (choosePath C F (s - (C.freeLits ρ).length) ρ) ∧
      ¬ C.Satisfied (choosePath C F (s - (C.freeLits ρ).length) ρ) ∧
      s - (C.freeLits ρ).length ≤ (cdt F (choosePath C F (s - (C.freeLits ρ).length) ρ)).depth := by
  apply Classical.epsilon_spec (p := fun ρ' => ExtOn (C.freeVars ρ) ρ ρ' ∧ ¬ C.Satisfied ρ' ∧
    s - (C.freeLits ρ).length ≤ (cdt F ρ').depth)
  by_contra hne
  have hsat : ¬ C.Satisfied ρ := by
    intro h
    rw [cdt, ite_eq_right hfal, ite_eq_left h] at hbad
    simp [DTree.depth] at hbad
    omega
  have hd := queryAll_depth_le
    (fun ρ' => if C.Satisfied ρ' then .leaf true else cdt F ρ') (C.freeVars ρ) ρ
    (s - (C.freeLits ρ).length - 1) (fun ρ' hρ' => by
      by_cases hs : C.Satisfied ρ'
      · simp [hs, DTree.depth]
      · simp only [hs, ite_false]
        have : ¬ (s - (C.freeLits ρ).length ≤ (cdt F ρ').depth) := fun h => hne ⟨ρ', hρ', hs, h⟩
        omega)
  rw [cdt, ite_eq_right hfal, ite_eq_right hsat] at hbad
  have hlen : (C.freeVars ρ).length = (C.freeLits ρ).length := by simp [Term.freeVars]
  omega

theorem encode_spec {k : ℕ} (F : DNF n) (hF : IsKDNF k F) : ∀ (s : ℕ) (ρ : Restriction n),
    s ≤ (cdt F ρ).depth →
    Refines ρ (encode F s ρ).1 ∧ freeSet (encode F s ρ).1 ⊆ freeSet ρ ∧
    (freeSet (encode F s ρ).1).card + s = (freeSet ρ).card ∧
    (encode F s ρ).2.length = s ∧ ∀ e ∈ (encode F s ρ).2, e.1 < k := by
  induction F with
  | nil =>
      intro s ρ hs
      simp only [cdt, DTree.depth, Nat.le_zero] at hs
      subst hs
      simp [encode, Refines]
  | cons C F ih =>
      intro s ρ hs
      have hC : C.length ≤ k ∧ C.WellFormed := hF C (by simp)
      have hF' : IsKDNF k F := fun C' hC' => hF C' (by simp [hC'])
      by_cases hfal : C.Falsified ρ
      · rw [encode_falsified hfal]
        rw [cdt_falsified hfal] at hs
        exact ih hF' s ρ hs
      · have hKfree : ∀ i ∈ C.freeVars ρ, ρ i = none := by
          intro i hi
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
          exact (mem_freeLits.1 hp).2
        have hKnodup : (C.freeVars ρ).Nodup := vars_nodup_of_sublist hC.2 (List.Sublist.refl _)
        have hposL : ∀ (ρ' : Restriction n) (T : List (Lit n × ℕ)), T.Sublist (C.freeLits ρ) →
            ∀ e ∈ blockCode ρ' T, e.1 < k := by
          intro ρ' T hT e he
          have : e.1 ∈ T.map Prod.snd := by
            rw [← blockCode_map_fst ρ' T]
            exact List.mem_map.2 ⟨e, he, rfl⟩
          obtain ⟨p, hp, hpe⟩ := List.mem_map.1 this
          have := (mem_of_mem_zipIdx (mem_freeLits.1 (hT.subset hp)).1).2
          omega
        by_cases hlt : (C.freeLits ρ).length < s
        · obtain ⟨hext, -, hbad'⟩ := choosePath_spec hfal hlt hs
          obtain ⟨r1, r2, r3, r4, r5⟩ := ih hF' _ _ hbad'
          rw [encode_lt hfal hlt]
          set L := C.freeLits ρ with hLdef
          set ρ' := choosePath C F (s - L.length) ρ with hρ'def
          set r := encode F (s - L.length) ρ' with hrdef
          have hρρ' : Refines ρ ρ' := by
            intro i b hi
            have hiK : i ∉ C.freeVars ρ := fun h => by rw [hKfree i h] at hi; cases hi
            rw [(hext i).2 hiK, hi]
          have hfree' : freeSet ρ' = freeSet ρ \ (C.freeVars ρ).toFinset := by
            ext i
            simp only [freeSet, mem_filter, mem_univ, true_and, mem_sdiff, List.mem_toFinset]
            by_cases hiK : i ∈ C.freeVars ρ
            · simp only [hiK, not_true_eq_false, and_false, iff_false]
              exact (hext i).1 hiK
            · simp only [hiK, not_false_eq_true, and_true]
              rw [(hext i).2 hiK]
          have hKsub : (C.freeVars ρ).toFinset ⊆ freeSet ρ := by
            intro i hi
            simp only [freeSet, mem_filter, mem_univ, true_and]
            exact hKfree i (List.mem_toFinset.1 hi)
          have hKcard : (C.freeVars ρ).toFinset.card = L.length := by
            rw [List.toFinset_card_of_nodup hKnodup]
            simp [Term.freeVars, hLdef]
          have hout : freeSet (setLits r.1 L) = freeSet r.1 := by
            rw [freeSet_setLits]
            apply sdiff_eq_left.2
            rw [Finset.disjoint_left]
            intro i hi hiK
            have := r2 hi
            rw [hfree'] at this
            exact (mem_sdiff.1 this).2 hiK
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro i b hi
            have hiK : i ∉ C.freeVars ρ := fun h => by rw [hKfree i h] at hi; cases hi
            show setLits r.1 L i = some b
            rw [setLits_of_not_mem hiK]
            exact r1 i b (hρρ' i b hi)
          · show freeSet (setLits r.1 L) ⊆ freeSet ρ
            rw [hout]
            exact r2.trans (hfree' ▸ sdiff_subset)
          · show (freeSet (setLits r.1 L)).card + s = (freeSet ρ).card
            rw [hout]
            have h1 := card_sdiff_add_card_eq_card hKsub
            rw [← hfree'] at h1
            omega
          · show (blockCode ρ' L ++ r.2).length = s
            rw [List.length_append, blockCode_length, r4]
            omega
          · intro e he
            rcases List.mem_append.1 he with he | he
            · exact hposL ρ' L (List.Sublist.refl _) e he
            · exact r5 e he
        · rw [encode_ge hfal hlt]
          set L := C.freeLits ρ with hLdef
          set T := L.take s with hTdef
          have hTsub : T.Sublist L := List.take_sublist _ _
          have hTnodup : (T.map (fun p => p.1.1)).Nodup := vars_nodup_of_sublist hC.2 hTsub
          have hTfree : ∀ i ∈ T.map (fun p => p.1.1), ρ i = none := by
            intro i hi
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
            exact (mem_freeLits.1 (hTsub.subset hp)).2
          have hTlen : T.length = s := by
            simp only [hTdef, List.length_take]
            omega
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · intro i b hi
            have hiT : i ∉ T.map (fun p => p.1.1) := fun h => by rw [hTfree i h] at hi; cases hi
            show setLits ρ T i = some b
            rw [setLits_of_not_mem hiT, hi]
          · show freeSet (setLits ρ T) ⊆ freeSet ρ
            rw [freeSet_setLits]
            exact sdiff_subset
          · show (freeSet (setLits ρ T)).card + s = (freeSet ρ).card
            rw [freeSet_setLits]
            have hsub : (T.map (fun p => p.1.1)).toFinset ⊆ freeSet ρ := by
              intro i hi
              simp only [freeSet, mem_filter, mem_univ, true_and]
              exact hTfree i (List.mem_toFinset.1 hi)
            have h1 := card_sdiff_add_card_eq_card hsub
            rw [List.toFinset_card_of_nodup hTnodup, List.length_map, hTlen] at h1
            exact h1
          · show (blockCode ρ T).length = s
            rw [blockCode_length, hTlen]
          · exact hposL ρ T hTsub

theorem encode_mem {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (s ℓ : ℕ) (ρ : Restriction n)
    (hρ : ρ ∈ R n ℓ) (hbad : s ≤ (cdt F ρ).depth) :
    s ≤ ℓ ∧ encode F s ρ ∈ R n (ℓ - s) ×ˢ codes k s := by
  obtain ⟨-, -, h3, h4, h5⟩ := encode_spec F hF s ρ hbad
  have hρ' : (freeSet ρ).card = ℓ := by simpa [R] using hρ
  refine ⟨by omega, mem_product.2 ⟨?_, ?_⟩⟩
  · simp only [R, mem_filter, mem_univ, true_and]
    omega
  · have := mem_codes _ h5
    rwa [h4] at this

theorem Refines.falsified {C : Term n} {ρ ρ' : Restriction n} (h : Refines ρ ρ')
    (hC : C.Falsified ρ) : C.Falsified ρ' := by
  obtain ⟨l, hl, hv⟩ := hC
  exact ⟨l, hl, h _ _ hv⟩

theorem not_mem_freeVars {C : Term n} {ρ : Restriction n} {l : Lit n} (hl : l ∈ C)
    (h : l.1 ∉ C.freeVars ρ) : ρ l.1 ≠ none := fun hn => h (Term.mem_freeVars hl hn)

/-- The encoding never falsifies the first term that the restriction leaves alive. -/
theorem encode_not_falsified {C : Term n} {F : DNF n} (hC : C.WellFormed) {s : ℕ}
    {ρ : Restriction n} (hfal : ¬ C.Falsified ρ) (hbad : s ≤ (cdt (C :: F) ρ).depth)
    (hspec : ∀ (s : ℕ) (ρ : Restriction n), s ≤ (cdt F ρ).depth → Refines ρ (encode F s ρ).1) :
    ¬ C.Falsified (encode (C :: F) s ρ).1 := by
  rintro ⟨l, hl, hv⟩
  have hval : ∀ (T : List (Lit n × ℕ)), T.Sublist (C.freeLits ρ) → ∀ (ρ₀ : Restriction n),
      l.1 ∈ T.map (fun p => p.1.1) → setLits ρ₀ T l.1 = some l.2 := by
    intro T hT ρ₀ hm
    obtain ⟨q, hq, hql⟩ := List.mem_map.1 hm
    have hqC := (mem_of_mem_zipIdx (mem_freeLits.1 (hT.subset hq)).1).1
    have := lit_eq_of_var_eq hC hqC hl hql
    rw [← hql, setLits_of_mem (vars_nodup_of_sublist hC hT) hq, this]
  have hne : ∀ b : Bool, some l.2 ≠ some (!b) → True := fun _ _ => trivial
  by_cases hlt : (C.freeLits ρ).length < s
  · obtain ⟨hext, -, hbad'⟩ := choosePath_spec hfal hlt hbad
    rw [encode_lt hfal hlt] at hv
    simp only at hv
    by_cases hm : l.1 ∈ (C.freeLits ρ).map (fun p => p.1.1)
    · rw [hval _ (List.Sublist.refl _) _ hm] at hv
      cases h2 : l.2 <;> simp [h2] at hv
    · rw [setLits_of_not_mem hm] at hv
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (not_mem_freeVars hl hm)
      have hb2 := value_of_not_falsified hfal hl hb
      have h1 : choosePath C F (s - (C.freeLits ρ).length) ρ l.1 = some b := by
        rw [(hext l.1).2 hm, hb]
      rw [hspec _ _ hbad' _ _ h1, hb2] at hv
      cases h2 : l.2 <;> simp [h2] at hv
  · rw [encode_ge hfal hlt] at hv
    simp only at hv
    by_cases hm : l.1 ∈ ((C.freeLits ρ).take s).map (fun p => p.1.1)
    · rw [hval _ (List.take_sublist _ _) _ hm] at hv
      cases h2 : l.2 <;> simp [h2] at hv
    · rw [setLits_of_not_mem hm] at hv
      exact hfal ⟨l, hl, hv⟩

theorem encode_inj_aux {k : ℕ} (F : DNF n) (hF : IsKDNF k F) : ∀ (s : ℕ) (ρ₁ ρ₂ : Restriction n),
    s ≤ (cdt F ρ₁).depth → s ≤ (cdt F ρ₂).depth → encode F s ρ₁ = encode F s ρ₂ → ρ₁ = ρ₂ := by
  induction F with
  | nil =>
      intro s ρ₁ ρ₂ _ _ he
      simpa [encode] using congrArg Prod.fst he
  | cons C F ih =>
      intro s ρ₁ ρ₂ h₁ h₂ he
      have hC : C.length ≤ k ∧ C.WellFormed := hF C (by simp)
      have hF' : IsKDNF k F := fun C' hC' => hF C' (by simp [hC'])
      have hspec := fun s ρ h => (encode_spec F hF' s ρ h).1
      rcases Nat.eq_zero_or_pos s with hs0 | hspos
      · subst hs0
        rw [encode_zero, encode_zero] at he
        exact congrArg Prod.fst he
      by_cases f₁ : C.Falsified ρ₁ <;> by_cases f₂ : C.Falsified ρ₂
      · rw [encode_falsified f₁, encode_falsified f₂] at he
        rw [cdt_falsified f₁] at h₁
        rw [cdt_falsified f₂] at h₂
        exact ih hF' s ρ₁ ρ₂ h₁ h₂ he
      · exfalso
        have hA : C.Falsified (encode (C :: F) s ρ₁).1 := by
          rw [encode_falsified f₁]
          rw [cdt_falsified f₁] at h₁
          exact (hspec s ρ₁ h₁).falsified f₁
        rw [he] at hA
        exact encode_not_falsified hC.2 f₂ h₂ hspec hA
      · exfalso
        have hA : C.Falsified (encode (C :: F) s ρ₂).1 := by
          rw [encode_falsified f₂]
          rw [cdt_falsified f₂] at h₂
          exact (hspec s ρ₂ h₂).falsified f₂
        rw [← he] at hA
        exact encode_not_falsified hC.2 f₁ h₁ hspec hA
      · -- the main case: `C` is alive under both restrictions
        have hnil : ∀ ρ, ¬ C.Falsified ρ → s ≤ (cdt (C :: F) ρ).depth → C.freeLits ρ ≠ [] := by
          intro ρ hf hb hn
          have := satisfied_of_freeLits_nil hf hn
          rw [cdt, ite_eq_right hf, ite_eq_left this] at hb
          simp [DTree.depth] at hb
          omega
        have hz : ∀ ρ, ∀ p ∈ C.freeLits ρ, p ∈ C.zipIdx := fun ρ p hp => (mem_freeLits.1 hp).1
        have hfree : ∀ ρ, ∀ T : List (Lit n × ℕ), T.Sublist (C.freeLits ρ) →
            ∀ i ∈ T.map (fun p => p.1.1), ρ i = none := by
          intro ρ T hT i hi
          obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
          exact (mem_freeLits.1 (hT.subset hp)).2
        have hlen₁ := List.length_pos_of_ne_nil (hnil ρ₁ f₁ h₁)
        have hlen₂ := List.length_pos_of_ne_nil (hnil ρ₂ f₂ h₂)
        by_cases lt₁ : (C.freeLits ρ₁).length < s <;> by_cases lt₂ : (C.freeLits ρ₂).length < s
        · rw [encode_lt f₁ lt₁, encode_lt f₂ lt₂, Prod.mk.injEq] at he
          obtain ⟨he₁, he₂⟩ := he
          set L₁ := C.freeLits ρ₁ with hL₁
          set L₂ := C.freeLits ρ₂ with hL₂
          -- the two blocks have the same length
          have hlen : L₁.length = L₂.length := by
            by_contra hne
            rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
            · have a := blockCode_last (choosePath C F (s - L₁.length) ρ₁) L₁
                (encode F (s - L₁.length) (choosePath C F (s - L₁.length) ρ₁)).2
                (i := L₁.length - 1) (by omega)
              have b := blockCode_last (choosePath C F (s - L₂.length) ρ₂) L₂
                (encode F (s - L₂.length) (choosePath C F (s - L₂.length) ρ₂)).2
                (i := L₁.length - 1) (by omega)
              rw [he₂] at a
              rw [a] at b
              simp at b
              omega
            · have a := blockCode_last (choosePath C F (s - L₂.length) ρ₂) L₂
                (encode F (s - L₂.length) (choosePath C F (s - L₂.length) ρ₂)).2
                (i := L₂.length - 1) (by omega)
              have b := blockCode_last (choosePath C F (s - L₁.length) ρ₁) L₁
                (encode F (s - L₁.length) (choosePath C F (s - L₁.length) ρ₁)).2
                (i := L₂.length - 1) (by omega)
              rw [← he₂] at a
              rw [a] at b
              simp at b
              omega
          obtain ⟨hb, hr⟩ := List.append_inj he₂ (by rw [blockCode_length, blockCode_length, hlen])
          have hL : L₁ = L₂ := eq_of_positions (hz ρ₁) (hz ρ₂) (by
            rw [← blockCode_map_fst, ← blockCode_map_fst, hb])
          have hvals := blockCode_map_val (choosePath C F (s - L₁.length) ρ₁) L₁
          rw [hb, blockCode_map_val, ← hL] at hvals
          obtain ⟨hext₁, -, hbad₁⟩ := choosePath_spec f₁ lt₁ h₁
          obtain ⟨hext₂, -, hbad₂⟩ := choosePath_spec f₂ lt₂ h₂
          rw [← hL₁] at hext₁ hbad₁
          rw [← hL₂] at hext₂ hbad₂
          have hK : C.freeVars ρ₁ = C.freeVars ρ₂ := by
            rw [freeVars_eq, freeVars_eq, ← hL₁, ← hL₂, hL]
          rw [← hL] at hext₂ hbad₂ he₁ hr
          rw [← hK] at hext₂
          set ρ'₁ := choosePath C F (s - L₁.length) ρ₁
          set ρ'₂ := choosePath C F (s - L₁.length) ρ₂
          -- the two paths agree on the block
          have hagree : ∀ i ∈ C.freeVars ρ₁, ρ'₁ i = ρ'₂ i := by
            intro i hi
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
            have := (List.map_inj_left.1 hvals.symm) p hp
            obtain ⟨b₁, hb₁⟩ := Option.ne_none_iff_exists'.1 ((hext₁ p.1.1).1 hi)
            obtain ⟨b₂, hb₂⟩ := Option.ne_none_iff_exists'.1 ((hext₂ p.1.1).1 hi)
            simp only [hb₁, hb₂, Option.getD_some] at this
            rw [hb₁, hb₂, this]
          have hspec₁ := encode_spec F hF' _ _ hbad₁
          have hspec₂ := encode_spec F hF' _ _ hbad₂
          have hr1 : (encode F (s - L₁.length) ρ'₁).1 = (encode F (s - L₁.length) ρ'₂).1 := by
            funext i
            by_cases hi : i ∈ C.freeVars ρ₁
            · obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 ((hext₁ i).1 hi)
              rw [hspec₁.1 i b hb, hspec₂.1 i b (by rw [← hagree i hi, hb])]
            · have := congrFun he₁ i
              rwa [setLits_of_not_mem hi, setLits_of_not_mem hi] at this
          have hρ' : ρ'₁ = ρ'₂ := ih hF' _ _ _ hbad₁ hbad₂ (Prod.ext hr1 hr)
          funext i
          by_cases hi : i ∈ C.freeVars ρ₁
          · rw [hfree ρ₁ L₁ (List.Sublist.refl _) i hi]
            rw [hK] at hi
            rw [hfree ρ₂ L₂ (List.Sublist.refl _) i hi]
          · rw [← (hext₁ i).2 hi, ← (hext₂ i).2 hi, hρ']
        · exfalso
          rw [encode_lt f₁ lt₁, encode_ge f₂ lt₂, Prod.mk.injEq] at he
          have a := blockCode_last (choosePath C F (s - (C.freeLits ρ₁).length) ρ₁)
            (C.freeLits ρ₁)
            (encode F (s - (C.freeLits ρ₁).length)
              (choosePath C F (s - (C.freeLits ρ₁).length) ρ₁)).2
            (i := (C.freeLits ρ₁).length - 1) (by omega)
          have hT : ((C.freeLits ρ₂).take s).length = s := by simp; omega
          have b := blockCode_last ρ₂ ((C.freeLits ρ₂).take s) []
            (i := (C.freeLits ρ₁).length - 1) (by omega)
          rw [List.append_nil, ← he.2] at b
          rw [a, hT] at b
          simp at b
          omega
        · exfalso
          rw [encode_ge f₁ lt₁, encode_lt f₂ lt₂, Prod.mk.injEq] at he
          have a := blockCode_last (choosePath C F (s - (C.freeLits ρ₂).length) ρ₂)
            (C.freeLits ρ₂)
            (encode F (s - (C.freeLits ρ₂).length)
              (choosePath C F (s - (C.freeLits ρ₂).length) ρ₂)).2
            (i := (C.freeLits ρ₂).length - 1) (by omega)
          have hT : ((C.freeLits ρ₁).take s).length = s := by simp; omega
          have b := blockCode_last ρ₁ ((C.freeLits ρ₁).take s) []
            (i := (C.freeLits ρ₂).length - 1) (by omega)
          rw [List.append_nil, he.2] at b
          rw [a, hT] at b
          simp at b
          omega
        · rw [encode_ge f₁ lt₁, encode_ge f₂ lt₂, Prod.mk.injEq] at he
          obtain ⟨he₁, he₂⟩ := he
          have hsub₁ := List.take_sublist s (C.freeLits ρ₁)
          have hsub₂ := List.take_sublist s (C.freeLits ρ₂)
          have hT : (C.freeLits ρ₁).take s = (C.freeLits ρ₂).take s :=
            eq_of_positions (fun p hp => hz ρ₁ p (hsub₁.subset hp))
              (fun p hp => hz ρ₂ p (hsub₂.subset hp)) (by
                rw [← blockCode_map_fst ρ₁, ← blockCode_map_fst ρ₂, he₂])
          rw [← hT] at he₁ hsub₂
          funext i
          by_cases hi : i ∈ ((C.freeLits ρ₁).take s).map (fun p => p.1.1)
          · rw [hfree ρ₁ _ hsub₁ i hi, hfree ρ₂ _ hsub₂ i hi]
          · have := congrFun he₁ i
            rwa [setLits_of_not_mem hi, setLits_of_not_mem hi] at this

theorem encode_injOn {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (s : ℕ) :
    Set.InjOn (encode F s) {ρ | s ≤ (cdt F ρ).depth} :=
  fun ρ₁ h₁ ρ₂ h₂ he => encode_inj_aux F hF s ρ₁ ρ₂ h₁ h₂ he

open Classical in
/-- The restrictions in `R n ℓ` under which `F` has no decision tree of depth `< s`. -/
noncomputable def Bad (F : DNF n) (ℓ s : ℕ) : Finset (Restriction n) :=
  (R n ℓ).filter (fun ρ => ¬ ∃ T : DTree n, T.depth < s ∧ Computes T F ρ)

open Classical in
theorem bad_subset_R (F : DNF n) (ℓ s : ℕ) : Bad F ℓ s ⊆ R n ℓ := filter_subset _ _

theorem bad_subset (F : DNF n) (ℓ s : ℕ) :
    Bad F ℓ s ⊆ (R n ℓ).filter (fun ρ => s ≤ (cdt F ρ).depth) := by
  intro ρ hρ
  simp only [Bad, mem_filter] at hρ ⊢
  refine ⟨hρ.1, ?_⟩
  by_contra h
  exact hρ.2 ⟨cdt F ρ, Nat.lt_of_not_le h, cdt_computes F ρ⟩

/-- **Razborov's counting bound.** -/
theorem card_bad_le {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (ℓ s : ℕ) :
    (Bad F ℓ s).card ≤ (R n (ℓ - s)).card * (4 * k) ^ s := by
  calc (Bad F ℓ s).card ≤ ((R n ℓ).filter (fun ρ => s ≤ (cdt F ρ).depth)).card :=
        card_le_card (bad_subset F ℓ s)
    _ ≤ (R n (ℓ - s) ×ˢ codes k s).card := by
        refine card_le_card_of_injOn (encode F s) (fun ρ hρ => ?_) ?_
        · have hρ' := mem_filter.1 hρ
          exact (encode_mem F hF s ℓ ρ hρ'.1 hρ'.2).2
        · intro ρ₁ h₁ ρ₂ h₂ he
          exact encode_injOn F hF s (mem_filter.1 (mem_coe.1 h₁)).2
            (mem_filter.1 (mem_coe.1 h₂)).2 he
    _ = (R n (ℓ - s)).card * (codes k s).card := card_product _ _
    _ ≤ (R n (ℓ - s)).card * (4 * k) ^ s := Nat.mul_le_mul_left _ (card_codes_le k s)

theorem bad_eq_empty {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (ℓ s : ℕ) (h : ℓ < s) :
    Bad F ℓ s = ∅ := by
  apply eq_empty_of_forall_notMem
  intro ρ hρ
  have := bad_subset F ℓ s hρ
  simp only [mem_filter] at this
  have := (encode_mem F hF s ℓ ρ this.1 this.2).1
  omega

theorem card_fiber (S : Finset (Fin n)) :
    (univ.filter (fun ρ : Restriction n => freeSet ρ = S)).card = 2 ^ (n - S.card) := by
  classical
  have h : univ.filter (fun ρ : Restriction n => freeSet ρ = S) =
      Fintype.piFinset (fun i => if i ∈ S then ({none} : Finset (Option Bool))
        else {some false, some true}) := by
    ext ρ
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro rfl i
      by_cases hi : ρ i = none
      · simp [freeSet, hi]
      · have : i ∉ freeSet ρ := by simp [freeSet, hi]
        rw [ite_eq_right this]
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hi
        cases b <;> simp [hb]
    · intro h
      ext i
      have hi := h i
      simp only [freeSet, mem_filter, mem_univ, true_and]
      by_cases his : i ∈ S
      · rw [ite_eq_left his] at hi
        simpa [his] using hi
      · rw [ite_eq_right his] at hi
        simp only [mem_insert, mem_singleton] at hi
        rcases hi with hi | hi <;> simp [hi, his]
  rw [h, Fintype.card_piFinset]
  have hc : ∀ i, (if i ∈ S then ({none} : Finset (Option Bool))
      else {some false, some true}).card = if i ∈ S then 1 else 2 := by
    intro i
    split_ifs <;> rfl
  simp only [hc]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  have : (univ.filter (fun i => i ∉ S)) = Sᶜ := by ext; simp
  rw [this, card_compl, Fintype.card_fin]

theorem card_R (n ℓ : ℕ) : (R n ℓ).card = n.choose ℓ * 2 ^ (n - ℓ) := by
  classical
  rw [card_eq_sum_card_fiberwise (f := freeSet) (t := powersetCard ℓ univ)]
  · have : ∀ S ∈ powersetCard ℓ (univ : Finset (Fin n)),
        ((R n ℓ).filter (fun ρ => freeSet ρ = S)).card = 2 ^ (n - ℓ) := by
      intro S hS
      rw [mem_powersetCard] at hS
      rw [← hS.2, ← card_fiber S]
      congr 1
      ext ρ
      simp only [R, mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      rintro rfl
      rfl
    rw [sum_congr rfl this, sum_const, card_powersetCard, card_univ, Fintype.card_fin,
      smul_eq_mul]
  · intro ρ hρ
    have : (freeSet ρ).card = ℓ := by simpa [R] using hρ
    simp [mem_powersetCard, this]

theorem card_R_step {ℓ m : ℕ} (hm : 1 ≤ m) (hmℓ : m ≤ ℓ) (hℓ : 2 * ℓ ≤ n) :
    (R n (m - 1)).card * n ≤ (R n m).card * (4 * ℓ) := by
  rw [card_R, card_R]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hc := Nat.choose_succ_right_eq n j
  have hpow : 2 ^ (n - j) = 2 * 2 ^ (n - (j + 1)) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow]
  have hpos : 0 < n - j := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  have key : n.choose j * (n - j) * (2 * n) ≤ n.choose (j + 1) * (4 * ℓ) * (n - j) := by
    rw [← hc]
    have h1 : (j + 1) * (2 * n) ≤ 4 * ℓ * (n - j) := by
      have : n ≤ 2 * (n - j) := by omega
      nlinarith
    calc n.choose (j + 1) * (j + 1) * (2 * n) = n.choose (j + 1) * ((j + 1) * (2 * n)) := by
          ring
      _ ≤ n.choose (j + 1) * (4 * ℓ * (n - j)) := Nat.mul_le_mul_left _ h1
      _ = n.choose (j + 1) * (4 * ℓ) * (n - j) := by ring
  calc n.choose j * (2 * 2 ^ (n - (j + 1))) * n * (n - j)
      = (n.choose j * (n - j) * (2 * n)) * 2 ^ (n - (j + 1)) := by ring
    _ ≤ (n.choose (j + 1) * (4 * ℓ) * (n - j)) * 2 ^ (n - (j + 1)) :=
        Nat.mul_le_mul_right _ key
    _ = n.choose (j + 1) * 2 ^ (n - (j + 1)) * (4 * ℓ) * (n - j) := by ring

theorem card_R_iter {ℓ : ℕ} (hℓ : 2 * ℓ ≤ n) :
    ∀ s ≤ ℓ, (R n (ℓ - s)).card * n ^ s ≤ (R n ℓ).card * (4 * ℓ) ^ s := by
  intro s
  induction s with
  | zero => intro _; simp
  | succ s ih =>
      intro hs
      have h1 := card_R_step (n := n) (ℓ := ℓ) (m := ℓ - s) (by omega) (by omega) hℓ
      have h2 := ih (by omega)
      have he : ℓ - (s + 1) = ℓ - s - 1 := by omega
      rw [he]
      calc (R n (ℓ - s - 1)).card * n ^ (s + 1) = ((R n (ℓ - s - 1)).card * n) * n ^ s := by
            ring
        _ ≤ ((R n (ℓ - s)).card * (4 * ℓ)) * n ^ s := Nat.mul_le_mul_right _ h1
        _ = ((R n (ℓ - s)).card * n ^ s) * (4 * ℓ) := by ring
        _ ≤ ((R n ℓ).card * (4 * ℓ) ^ s) * (4 * ℓ) := Nat.mul_le_mul_right _ h2
        _ = (R n ℓ).card * (4 * ℓ) ^ (s + 1) := by ring

/-- **Håstad's switching lemma.**  If `2ℓ ≤ n`, the fraction of restrictions with `ℓ` free
variables under which a `k`-DNF has no decision tree of depth `< s` is at most `(16 k ℓ / n)^s`. -/
theorem switching_lemma {k : ℕ} (F : DNF n) (hF : IsKDNF k F) (ℓ s : ℕ) (hℓ : 2 * ℓ ≤ n) :
    ((Bad F ℓ s).card : ℚ) / (R n ℓ).card ≤ (16 * k * ℓ / n : ℚ) ^ s := by
  by_cases hs : ℓ < s
  · rw [bad_eq_empty F hF ℓ s hs]
    simp only [card_empty, Nat.cast_zero, zero_div]
    positivity
  replace hs := Nat.le_of_not_lt hs
  have hnat : (Bad F ℓ s).card * n ^ s ≤ (R n ℓ).card * (16 * k * ℓ) ^ s := by
    calc (Bad F ℓ s).card * n ^ s ≤ (R n (ℓ - s)).card * (4 * k) ^ s * n ^ s :=
          Nat.mul_le_mul_right _ (card_bad_le F hF ℓ s)
      _ = ((R n (ℓ - s)).card * n ^ s) * (4 * k) ^ s := by ring
      _ ≤ ((R n ℓ).card * (4 * ℓ) ^ s) * (4 * k) ^ s :=
          Nat.mul_le_mul_right _ (card_R_iter hℓ s hs)
      _ = (R n ℓ).card * (16 * k * ℓ) ^ s := by
          rw [mul_assoc, ← mul_pow, show 4 * ℓ * (4 * k) = 16 * k * ℓ by ring]
  have hq : ((Bad F ℓ s).card : ℚ) * (n : ℚ) ^ s ≤ ((R n ℓ).card : ℚ) * (16 * k * ℓ) ^ s := by
    exact_mod_cast hnat
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hs0 : s = 0 := by omega
    subst hs0
    simp only [pow_zero]
    exact div_le_one_of_le₀ (by exact_mod_cast card_le_card (bad_subset_R F ℓ 0)) (by positivity)
  rcases Nat.eq_zero_or_pos (R n ℓ).card with hR | hR
  · rw [hR]; simp only [Nat.cast_zero, div_zero]; positivity
  rw [div_le_iff₀ (by exact_mod_cast hR), div_pow, mul_comm, ← mul_div_assoc,
    le_div_iff₀ (by positivity)]
  linarith

end Complexity.Switching
