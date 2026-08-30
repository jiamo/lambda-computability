/-
**Creative sets are recursively isomorphic to the halting set.**

`Start/PostCreative.lean` proves Myhill's completeness theorem: a creative set is many-one
complete.  `Start/MyhillIso.lean` proves Myhill's isomorphism theorem: one-one equivalent sets are
recursively isomorphic.  This module joins the two by upgrading the many-one reduction to a
*one-one* reduction, which gives the classical classification of the creative sets: they are all
recursively isomorphic to Kleene's `K`, hence to one another.

The missing ingredient is that a productive set has an *injective* production function.  It is
obtained by a chase, the same combinatorial device as in `Start/MyhillIso.lean`: to produce a
value outside a finite list `L`, apply the production function `p` to the current index `e`; if
`p e` lies in `L`, adjoin `p e` to the `e`-th r.e. set (`Lambda.Post.exists_adjoin`) and repeat.
All the values produced along the way are distinct, so the chase escapes `L` within `L.length + 1`
steps.  Running the chase at input `n` against the list of the values already produced at
`0, …, n - 1` gives an injective production function.

* `Lambda.Post.exists_injective_productive` — a productive set has an injective computable
  production function;
* `Lambda.Post.oneOneReducible_of_productive_compl` — the one-one form of Myhill's theorem;
* `Lambda.Post.Creative.oneOneComplete`, `Lambda.Post.Creative.oneOneEquiv_haltK` — a creative set
  is one-one complete, hence one-one equivalent to `K`;
* `Lambda.Post.Creative.recIso_haltK`, `Lambda.Post.Creative.recIso` — hence recursively
  isomorphic to `K`, and any two creative sets are recursively isomorphic;
* `Lambda.Post.creative_iff_recIso_haltK` — the classification: a set is creative exactly when it
  is recursively isomorphic to `K`;
* the lambda-calculus instances: `Lambda.recIso_codeHasNormalForm_haltK`,
  `Lambda.recIso_codeConverges_haltK`, `Lambda.recIso_codeSet_conv_church_haltK`.
-/

import Start.CreativeCodeSets
import Start.MyhillIso

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

namespace Post

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ## The chase for a fresh produced value

`p` is a production function and `adj` names the r.e. set `W e ∪ {a}`.  Starting from an index
`e`, the chase runs through the indices `e`, `adj e (p e)`, … until the produced value lies
outside a given finite list.
-/

section Chase

/-- The index sequence of the chase. -/
def chaseIdx (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) (i e : ℕ) : ℕ := (fun z => adj z (p z))^[i] e

variable (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) (L : List ℕ)

theorem chaseIdx_zero (e : ℕ) : chaseIdx p adj 0 e = e := rfl

theorem chaseIdx_succ (i e : ℕ) : chaseIdx p adj (i + 1) e = chaseIdx p adj i (adj e (p e)) := by
  simp [chaseIdx, Function.iterate_succ_apply]

theorem chaseIdx_succ' (i e : ℕ) :
    chaseIdx p adj (i + 1) e = adj (chaseIdx p adj i e) (p (chaseIdx p adj i e)) := by
  simp [chaseIdx, Function.iterate_succ_apply']

/-- One step of the chase: once a value has been found, stop; otherwise test `p e`, and adjoin it
to the current set if it is not usable. -/
def prodStep (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) (L : List ℕ) : ℕ × ℕ × Bool → ℕ × ℕ × Bool
  | (e, v, Bool.true) => (e, v, Bool.true)
  | (e, v, Bool.false) =>
      if L.elem (p e) then (adj e (p e), v, Bool.false) else (e, p e, Bool.true)

theorem prodStep_eq (s : ℕ × ℕ × Bool) :
    prodStep p adj L s =
      cond s.2.2 s
        (cond (L.elem (p s.1)) (adj s.1 (p s.1), s.2.1, Bool.false)
          (s.1, p s.1, Bool.true)) := by
  obtain ⟨e, v, b⟩ := s
  cases b with
  | false => simp [prodStep]
  | true => rfl

/-- The chase from `e`, run for `b` steps. -/
def prodRun (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) (L : List ℕ) (b e : ℕ) : ℕ × ℕ × Bool :=
  (prodStep p adj L)^[b] (e, 0, Bool.false)

/-- A number larger than every member of `L`, used when the chase does not succeed. -/
def freshOf (L : List ℕ) : ℕ := L.foldr max 0 + 1

theorem le_foldr_max {x : ℕ} {L : List ℕ} (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => exact absurd h (by simp)
  | cons a t ih =>
      rcases List.mem_cons.1 h with h' | h'
      · exact h' ▸ le_max_left _ _
      · exact le_trans (ih h') (le_max_right _ _)

theorem freshOf_notMem (L : List ℕ) : freshOf L ∉ L := fun h =>
  absurd (le_foldr_max h) (by simp [freshOf])

/-- The value produced by the chase: the escaping value if there is one, and a fresh number
otherwise. -/
def prodEsc (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) (L : List ℕ) (b e : ℕ) : ℕ :=
  if (prodRun p adj L b e).2.2 then (prodRun p adj L b e).2.1 else freshOf L

theorem prodRun_stable (e v b : ℕ) :
    (prodStep p adj L)^[b] (e, v, Bool.true) = (e, v, Bool.true) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [Function.iterate_succ_apply]; exact ih

/-- Whenever the chase reports success, the value it carries is outside `L`. -/
theorem iterate_true_notMem (b : ℕ) :
    ∀ s : ℕ × ℕ × Bool, (s.2.2 = Bool.true → s.2.1 ∉ L) →
      ((prodStep p adj L)^[b] s).2.2 = Bool.true → ((prodStep p adj L)^[b] s).2.1 ∉ L := by
  induction b with
  | zero => intro s hs; exact hs
  | succ b ih =>
      intro s hs
      rw [Function.iterate_succ_apply]
      refine ih (prodStep p adj L s) ?_
      obtain ⟨e, v, c⟩ := s
      cases c with
      | true => exact hs
      | false =>
          by_cases h : p e ∈ L
          · simp only [prodStep, List.elem_eq_mem, decide_eq_true_eq, if_pos h]
            exact fun hc => absurd hc (by simp)
          · simp only [prodStep, List.elem_eq_mem, decide_eq_true_eq, if_neg h]
            exact fun _ => h

theorem prodEsc_notMem (b e : ℕ) : prodEsc p adj L b e ∉ L := by
  by_cases h : (prodRun p adj L b e).2.2 = Bool.true
  · rw [prodEsc, if_pos h]
    exact iterate_true_notMem p adj L b (e, 0, Bool.false) (by simp) h
  · rw [prodEsc, if_neg h]
    exact freshOf_notMem L

/-- A step of the chase when the produced value is unusable: the value is adjoined to the current
set and the chase continues. -/
theorem prodRun_succ_of_mem {e : ℕ} (h : p e ∈ L) (b : ℕ) :
    prodRun p adj L (b + 1) e = prodRun p adj L b (adj e (p e)) := by
  have hstep : prodStep p adj L (e, 0, Bool.false) = (adj e (p e), 0, Bool.false) := by
    simp only [prodStep, List.elem_eq_mem, decide_eq_true_eq, if_pos h]
  rw [prodRun, Function.iterate_succ_apply, hstep, prodRun]

/-- A step of the chase when the produced value is usable: the chase stops with that value. -/
theorem prodRun_succ_of_notMem {e : ℕ} (h : p e ∉ L) (b : ℕ) :
    prodRun p adj L (b + 1) e = (e, p e, Bool.true) := by
  have hstep : prodStep p adj L (e, 0, Bool.false) = (e, p e, Bool.true) := by
    simp only [prodStep, List.elem_eq_mem, decide_eq_true_eq, if_neg h]
  rw [prodRun, Function.iterate_succ_apply, hstep]
  exact prodRun_stable p adj L e (p e) b

/-- If some value along the chase escapes `L` within `b` steps, the chase returns one of the
chase values. -/
theorem prodEsc_eq_chase (b : ℕ) :
    ∀ e : ℕ, (∃ i < b, p (chaseIdx p adj i e) ∉ L) →
      ∃ i, prodEsc p adj L b e = p (chaseIdx p adj i e) := by
  induction b with
  | zero =>
      intro e hex
      obtain ⟨i, hi, -⟩ := hex
      exact absurd hi (Nat.not_lt_zero i)
  | succ b ih =>
      intro e hex
      by_cases h : p e ∈ L
      · have hex' : ∃ i < b, p (chaseIdx p adj i (adj e (p e))) ∉ L := by
          obtain ⟨i, hi, hval⟩ := hex
          cases i with
          | zero => rw [chaseIdx_zero] at hval; exact absurd h hval
          | succ i =>
              refine ⟨i, Nat.lt_of_succ_lt_succ hi, ?_⟩
              rwa [chaseIdx_succ] at hval
        obtain ⟨i, hi⟩ := ih (adj e (p e)) hex'
        refine ⟨i + 1, ?_⟩
        rw [prodEsc, prodRun_succ_of_mem p adj L h b, chaseIdx_succ, ← hi, prodEsc]
      · refine ⟨0, ?_⟩
        rw [prodEsc, prodRun_succ_of_notMem p adj L h b, chaseIdx_zero]
        simp

end Chase

/-! ## The chase produces new elements of a productive set -/

section Productive

variable {P : ℕ → Prop} {p : ℕ → ℕ} {adj : ℕ → ℕ → ℕ}
variable (hprod : ∀ e, (∀ x, Wset e x → P x) → P (p e) ∧ ¬ Wset e (p e))
variable (hadj : ∀ e a x, (Wset (adj e a) x ↔ (x = a ∨ Wset e x)))

include hprod hadj

/-- Every stage of the chase names a subset of `P`. -/
theorem chase_sub {e : ℕ} (he : ∀ x, Wset e x → P x) (i : ℕ) :
    ∀ x, Wset (chaseIdx p adj i e) x → P x := by
  induction i with
  | zero => rw [chaseIdx_zero]; exact he
  | succ i ih =>
      intro x hx
      rw [chaseIdx_succ', hadj] at hx
      rcases hx with hx | hx
      · exact hx ▸ (hprod _ ih).1
      · exact ih x hx

/-- The chase values lie in `P`. -/
theorem chase_val_mem {e : ℕ} (he : ∀ x, Wset e x → P x) (i : ℕ) :
    P (p (chaseIdx p adj i e)) :=
  (hprod _ (chase_sub hprod hadj he i)).1

/-- A chase value is not in the set named by its own stage. -/
theorem chase_val_notMem {e : ℕ} (he : ∀ x, Wset e x → P x) (i : ℕ) :
    ¬ Wset (chaseIdx p adj i e) (p (chaseIdx p adj i e)) :=
  (hprod _ (chase_sub hprod hadj he i)).2

omit hprod in
/-- The sets named by the stages increase along the chase. -/
theorem chase_Wset_mono {e : ℕ} {i j : ℕ} (hij : i ≤ j) {x : ℕ}
    (hx : Wset (chaseIdx p adj i e) x) : Wset (chaseIdx p adj j e) x := by
  induction j, hij using Nat.le_induction with
  | base => exact hx
  | succ j _ ih => rw [chaseIdx_succ', hadj]; exact Or.inr ih

omit hprod in
/-- The value produced at an earlier stage belongs to every later stage. -/
theorem chase_val_mem_later {e : ℕ} {i j : ℕ} (hij : i < j) :
    Wset (chaseIdx p adj j e) (p (chaseIdx p adj i e)) :=
  chase_Wset_mono hadj hij (by rw [chaseIdx_succ', hadj]; exact Or.inl rfl)

/-- The chase values are pairwise distinct. -/
theorem chase_val_injective {e : ℕ} (he : ∀ x, Wset e x → P x) :
    Function.Injective fun i => p (chaseIdx p adj i e) := by
  have key : ∀ i j : ℕ, i < j → p (chaseIdx p adj i e) ≠ p (chaseIdx p adj j e) := by
    intro i j hij hne
    exact chase_val_notMem hprod hadj he j (hne ▸ chase_val_mem_later hadj hij)
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (key i j h)
  · exact h
  · exact absurd hij.symm (key j i h)

/-- **The escape lemma for the production chase.**  Within `L.length + 1` steps the chase produces
a value outside `L`. -/
theorem exists_chase_escape {e : ℕ} (he : ∀ x, Wset e x → P x) (L : List ℕ) :
    ∃ i < L.length + 1, p (chaseIdx p adj i e) ∉ L := by
  by_contra hcon
  push Not at hcon
  have hmaps : Set.MapsTo (fun i => p (chaseIdx p adj i e))
      ↑(Finset.range (L.length + 1)) ↑L.toFinset := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    simpa using hcon i hi
  have hinj : Set.InjOn (fun i => p (chaseIdx p adj i e))
      ↑(Finset.range (L.length + 1)) :=
    (chase_val_injective hprod hadj he).injOn
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  have h2 := L.toFinset_card_le
  omega

/-- The chase produces an element of `P` outside the set named by the starting index. -/
theorem prodEsc_prod {e : ℕ} (he : ∀ x, Wset e x → P x) {L : List ℕ} {b : ℕ}
    (hb : L.length < b) :
    P (prodEsc p adj L b e) ∧ ¬ Wset e (prodEsc p adj L b e) := by
  obtain ⟨i, hi, hnot⟩ := exists_chase_escape hprod hadj he L
  obtain ⟨j, hj⟩ := prodEsc_eq_chase p adj L b e ⟨i, lt_of_lt_of_le hi hb, hnot⟩
  refine ⟨hj ▸ chase_val_mem hprod hadj he j, ?_⟩
  rw [hj]
  intro hmem
  refine chase_val_notMem hprod hadj he j (chase_Wset_mono hadj (Nat.zero_le j) ?_)
  rwa [chaseIdx_zero]

end Productive

/-! ## An injective production function -/

section Injective

/-- The list of the values produced at the inputs `0, …, n - 1`. -/
def escList (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => escList p adj n ++ [prodEsc p adj (escList p adj n) (n + 1) n]

/-- The injective production function: at `n`, chase from the index `n` dodging all the values
already produced. -/
def prodInj (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ) (n : ℕ) : ℕ :=
  prodEsc p adj (escList p adj n) (n + 1) n

variable (p : ℕ → ℕ) (adj : ℕ → ℕ → ℕ)

theorem escList_length (n : ℕ) : (escList p adj n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [escList, ih]

theorem escList_succ (n : ℕ) :
    escList p adj (n + 1) = escList p adj n ++ [prodInj p adj n] := rfl

theorem mem_escList {i n : ℕ} (h : i < n) : prodInj p adj i ∈ escList p adj n := by
  induction n with
  | zero => exact absurd h (Nat.not_lt_zero i)
  | succ n ih =>
      rw [escList_succ]
      rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | h'
      · exact List.mem_append_left _ (ih h')
      · exact h' ▸ List.mem_append_right _ (by simp)

theorem prodInj_notMem (n : ℕ) : prodInj p adj n ∉ escList p adj n :=
  prodEsc_notMem p adj (escList p adj n) (n + 1) n

theorem prodInj_injective : Function.Injective (prodInj p adj) := by
  have key : ∀ i n : ℕ, i < n → prodInj p adj i ≠ prodInj p adj n := by
    intro i n hin heq
    exact prodInj_notMem p adj n (heq ▸ mem_escList p adj hin)
  intro i j hij
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hij (key i j h)
  · exact h
  · exact absurd hij.symm (key j i h)

/-! ### Computability of the construction -/

theorem primrec_freshOf : Primrec freshOf :=
  (Primrec.succ.comp
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun _ => rfl

theorem prodEsc_eq_cond (L : List ℕ) (b e : ℕ) :
    prodEsc p adj L b e =
      cond (prodRun p adj L b e).2.2 (prodRun p adj L b e).2.1 (freshOf L) := by
  rw [prodEsc]
  cases (prodRun p adj L b e).2.2 <;> simp

theorem computable_prodStep (hp : Computable p) (hadjc : Computable₂ adj) :
    Computable₂ fun (L : List ℕ) (s : ℕ × ℕ × Bool) => prodStep p adj L s := by
  have hpe : Computable fun a : List ℕ × (ℕ × ℕ × Bool) => p a.2.1 :=
    hp.comp (Computable.fst.comp Computable.snd)
  have hmem : Computable fun a : List ℕ × (ℕ × ℕ × Bool) => List.elem (p a.2.1) a.1 :=
    Myhill.primrec_elem.to_comp.comp Computable.fst hpe
  have hadjv : Computable fun a : List ℕ × (ℕ × ℕ × Bool) => adj a.2.1 (p a.2.1) :=
    hadjc.comp (Computable.fst.comp Computable.snd) hpe
  have hbranch : Computable fun a : List ℕ × (ℕ × ℕ × Bool) =>
      cond (List.elem (p a.2.1) a.1) (adj a.2.1 (p a.2.1), a.2.2.1, Bool.false)
        (a.2.1, p a.2.1, Bool.true) :=
    Computable.cond hmem
      (hadjv.pair ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.const Bool.false)))
      ((Computable.fst.comp Computable.snd).pair (hpe.pair (Computable.const Bool.true)))
  exact ((Computable.cond (Computable.snd.comp (Computable.snd.comp Computable.snd))
    Computable.snd hbranch).of_eq fun a => (prodStep_eq p adj a.1 a.2).symm).to₂

theorem computable_prodEsc (hp : Computable p) (hadjc : Computable₂ adj) :
    Computable fun a : List ℕ × ℕ × ℕ => prodEsc p adj a.1 a.2.1 a.2.2 := by
  have hn : Computable fun a : List ℕ × ℕ × ℕ => a.2.1 := Computable.fst.comp Computable.snd
  have hst : Computable fun a : List ℕ × ℕ × ℕ => (a.2.2, 0, Bool.false) :=
    (Computable.snd.comp Computable.snd).pair
      ((Computable.const 0).pair (Computable.const Bool.false))
  have hh : Computable₂ fun (a : List ℕ × ℕ × ℕ) (s : ℕ × ℕ × Bool) => prodStep p adj a.1 s :=
    ((computable_prodStep p adj hp hadjc).comp (Computable.fst.comp Computable.fst)
      Computable.snd).to₂
  have hrun : Computable fun a : List ℕ × ℕ × ℕ => prodRun p adj a.1 a.2.1 a.2.2 :=
    Myhill.computable_iterate hn hst hh
  exact (Computable.cond (Computable.snd.comp (Computable.snd.comp hrun))
    (Computable.fst.comp (Computable.snd.comp hrun))
    (primrec_freshOf.to_comp.comp Computable.fst)).of_eq
    fun a => (prodEsc_eq_cond p adj a.1 a.2.1 a.2.2).symm

theorem computable_escList (hp : Computable p) (hadjc : Computable₂ adj) :
    Computable (escList p adj) := by
  have key : ∀ n : ℕ, Nat.rec (motive := fun _ => List ℕ) []
      (fun k IH => IH ++ [prodEsc p adj IH (k + 1) k]) n = escList p adj n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [escList_succ, prodInj, ← ih]
  have hstep : Computable₂ fun (_ : ℕ) (q : ℕ × List ℕ) =>
      q.2 ++ [prodEsc p adj q.2 (q.1 + 1) q.1] := by
    have harg : Computable fun a : ℕ × (ℕ × List ℕ) => (a.2.2, a.2.1 + 1, a.2.1) :=
      (Computable.snd.comp Computable.snd).pair
        ((Primrec.succ.comp (Primrec.fst.comp Primrec.snd)).to_comp.pair
          (Computable.fst.comp Computable.snd))
    exact (Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.snd)
      (Primrec.list_cons.to_comp.comp
        ((computable_prodEsc p adj hp hadjc).comp harg) (Computable.const []))).to₂
  exact (Computable.nat_rec Computable.id (Computable.const []) hstep).of_eq key

theorem computable_prodInj (hp : Computable p) (hadjc : Computable₂ adj) :
    Computable (prodInj p adj) := by
  have h1 : Computable fun n : ℕ => (n + 1, n) := Primrec.succ.to_comp.pair Computable.id
  have harg : Computable fun n : ℕ => (escList p adj n, n + 1, n) :=
    (computable_escList p adj hp hadjc).pair h1
  exact ((computable_prodEsc p adj hp hadjc).comp harg).of_eq fun _ => rfl

end Injective

/-- **A productive set has an injective production function.** -/
theorem exists_injective_productive {P : ℕ → Prop} (hP : Productive P) :
    ∃ q : ℕ → ℕ, Computable q ∧ Function.Injective q ∧
      ∀ e, (∀ x, Wset e x → P x) → P (q e) ∧ ¬ Wset e (q e) := by
  obtain ⟨p, hp, hprod⟩ := hP
  obtain ⟨adj, hadjc, hadj⟩ := exists_adjoin
  refine ⟨prodInj p adj, computable_prodInj p adj hp hadjc, prodInj_injective p adj,
    fun e he => ?_⟩
  exact prodEsc_prod hprod hadj he (by rw [escList_length]; exact Nat.lt_succ_self e)

/-! ## The one-one form of Myhill's theorem -/

/-- The recursion theorem with parameters, with an injective indexing. -/
theorem exists_recursion_index_inj (G : ℕ → ℕ → ℕ →. ℕ)
    (hG : Partrec fun q : ℕ × ℕ × ℕ => G q.1 q.2.1 q.2.2) :
    ∃ h : ℕ → ℕ, Computable h ∧ Function.Injective h ∧
      ∀ x y, (Wset (h x) y ↔ (G (h x) x y).Dom) := by
  have hcurry : Computable fun q : Code × ℕ =>
      Encodable.encode (Code.curry q.1 (Nat.unpair q.2).1) :=
    (Primrec.encode.comp (Code.primrec₂_curry.comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))).to_comp
  have hF : Partrec₂ fun (c : Code) (n : ℕ) =>
      G (Encodable.encode (Code.curry c (Nat.unpair n).1)) (Nat.unpair n).1 (Nat.unpair n).2 :=
    hG.comp (hcurry.pair (((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp))
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hF
  refine ⟨fun x => Encodable.encode (Code.curry c x),
    (Primrec.encode.comp (Code.primrec₂_curry.comp (Primrec.const c) Primrec.id)).to_comp,
    fun a b hab => (Code.curry_inj (Encodable.encode_injective hab)).2, fun x y => ?_⟩
  simp only [Wset, Denumerable.ofNat_encode, Code.eval_curry, hc, Nat.unpair_pair]

/-- **Myhill's theorem, one-one form.**  If the complement of `C` is productive then every r.e.
set reduces to `C` by an injective computable function. -/
theorem oneOneReducible_of_productive_compl {C A : ℕ → Prop}
    (hC : Productive fun x => ¬ C x) (hA : REPred A) : A ≤₁ C := by
  obtain ⟨p, hp, hpi, hprod⟩ := exists_injective_productive hC
  have hsd : Partrec fun x : ℕ => Part.assert (A x) fun _ => Part.some (0 : ℕ) := by
    have := hA.map (g := fun (_ : ℕ) (_ : Unit) => (0 : ℕ)) (Computable.const 0)
    refine this.of_eq fun x => ?_
    ext v
    simp [Part.mem_assert_iff, eq_comm]
  have hG : Partrec fun q : ℕ × ℕ × ℕ =>
      bif decide (q.2.2 = p q.1) then (Part.assert (A q.2.1) fun _ => Part.some (0 : ℕ))
      else Part.none := by
    have hcond : Computable fun q : ℕ × ℕ × ℕ => decide (q.2.2 = p q.1) :=
      computable_decide_eq (Computable.snd.comp Computable.snd) (hp.comp Computable.fst)
    exact Partrec.cond hcond (hsd.comp (Computable.fst.comp Computable.snd)) Partrec.none
  obtain ⟨h, hh, hhi, hspec⟩ := exists_recursion_index_inj
    (fun e x y => bif decide (y = p e) then (Part.assert (A x) fun _ => Part.some (0 : ℕ))
      else Part.none) hG
  refine ⟨fun x => p (h x), hp.comp hh, hpi.comp hhi, fun x => ?_⟩
  have hW : ∀ y, Wset (h x) y ↔ (y = p (h x) ∧ A x) := by
    intro y
    rw [hspec x y]
    by_cases hy : y = p (h x) <;> simp [hy, Part.assert]
  constructor
  · intro hAx
    by_contra hnC
    have hsub : ∀ y, Wset (h x) y → ¬ C y := by
      intro y hy
      rw [hW y] at hy
      exact hy.1 ▸ hnC
    exact (hprod (h x) hsub).2 ((hW _).2 ⟨rfl, hAx⟩)
  · intro hCx
    by_contra hAx
    have hsub : ∀ y, Wset (h x) y → ¬ C y := by
      intro y hy
      rw [hW y] at hy
      exact absurd hy.2 hAx
    exact (hprod (h x) hsub).1 hCx

/-- **Every creative set is one-one complete.** -/
theorem Creative.oneOneComplete {C : ℕ → Prop} (hC : Creative C) :
    ∀ q : ℕ → Prop, REPred q → q ≤₁ C :=
  fun _ hq => oneOneReducible_of_productive_compl hC.2 hq

/-- **Every creative set is one-one equivalent to `K`.** -/
theorem Creative.oneOneEquiv_haltK {C : ℕ → Prop} (hC : Creative C) : OneOneEquiv C HaltK :=
  ⟨rePred_le_one_haltK hC.1, hC.oneOneComplete HaltK rePred_haltK⟩

/-- **Every creative set is recursively isomorphic to `K`**: a computable bijection of `ℕ` carries
it onto Kleene's halting set. -/
theorem Creative.recIso_haltK {C : ℕ → Prop} (hC : Creative C) : Myhill.RecIso C HaltK :=
  Myhill.recIso_of_oneOneEquiv hC.oneOneEquiv_haltK

/-- **Any two creative sets are recursively isomorphic.** -/
theorem Creative.recIso {C D : ℕ → Prop} (hC : Creative C) (hD : Creative D) :
    Myhill.RecIso C D :=
  Myhill.recIso_of_oneOneEquiv
    ⟨hD.oneOneComplete C hC.1, hC.oneOneComplete D hD.1⟩

/-- A set recursively isomorphic to `K` is creative. -/
theorem creative_of_recIso_haltK {C : ℕ → Prop} (h : Myhill.RecIso C HaltK) : Creative C := by
  have hm : ManyOneEquiv C HaltK := (Myhill.oneOneEquiv_of_recIso h).to_many_one
  have hre : REPred C := by
    obtain ⟨f, hf, hs⟩ := hm.1
    have hEq : (fun x => HaltK (f x)) = C := funext fun x => propext (hs x).symm
    exact hEq ▸ rePred_haltK.comp hf
  exact creative_of_manyOneComplete hre fun q hq => (rePred_le_haltK hq).trans hm.2

/-- **The classification of the creative sets**: a set of numbers is creative exactly when it is
recursively isomorphic to Kleene's `K`. -/
theorem creative_iff_recIso_haltK {C : ℕ → Prop} : Creative C ↔ Myhill.RecIso C HaltK :=
  ⟨Creative.recIso_haltK, creative_of_recIso_haltK⟩

/-- For r.e. sets, creativity is one-one completeness. -/
theorem creative_iff_oneOneComplete {C : ℕ → Prop} :
    Creative C ↔ REPred C ∧ ∀ q : ℕ → Prop, REPred q → q ≤₁ C := by
  refine ⟨fun hC => ⟨hC.1, hC.oneOneComplete⟩, fun ⟨hre, hall⟩ => ?_⟩
  exact creative_of_manyOneComplete hre fun q hq => (hall q hq).to_many_one

end Post

/-! ## The lambda-calculus instances -/

/-- The set of codes of the terms with a normal form is recursively isomorphic to `K`. -/
theorem recIso_codeHasNormalForm_haltK : Myhill.RecIso CodeHasNormalForm HaltK :=
  Myhill.recIso_of_oneOneEquiv oneOneEquiv_haltK_codeHasNormalForm.symm

/-- The set of codes converging to a Church numeral is recursively isomorphic to `K`. -/
theorem recIso_codeConverges_haltK : Myhill.RecIso CodeConverges HaltK :=
  Myhill.recIso_of_oneOneEquiv oneOneEquiv_haltK_codeConverges.symm

/-- The set of codes of the terms convertible with `church m` is recursively isomorphic to `K`. -/
theorem recIso_codeSet_conv_church_haltK (m : ℕ) :
    Myhill.RecIso (CodeSet fun t => Conv t (church m)) HaltK :=
  (creative_codeSet_conv_church m).recIso_haltK

end Lambda
