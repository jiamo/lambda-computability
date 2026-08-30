/-
**Myhill's isomorphism theorem**: one-one equivalent sets are recursively isomorphic.

If `A ≤₁ B` and `B ≤₁ A` — that is, there are injective computable `f` and `g` with
`A x ↔ B (f x)` and `B y ↔ A (g y)` — then there is a computable *bijection* `h : ℕ → ℕ`
with `A x ↔ B (h x)`.

The proof is the classical back-and-forth construction.  A stage of the construction is a
finite partial map `p : List (ℕ × ℕ)`, injective in both directions, all of whose pairs
`(x, y)` satisfy `A x ↔ B y`.  Two extension steps alternate.  To put a new `x` into the
domain, *chase* through `p`: look at `f x`; if it is not yet in the range of `p`, use it;
otherwise replace `x` by the `p`-preimage of `f x` — which has the same `A`-status — and
repeat.  The points visited are distinct elements of the domain of `p`, so the chase stops
within `p.length + 1` steps.  Putting a new `y` into the range is the mirror image, with `g`
and the forward direction of `p`.

The union of the stages is a bijection, and it is computable because each stage is.

* `Lambda.Myhill.RecIso` — recursive isomorphism of two sets of numbers;
* `Lambda.Myhill.recIso_of_oneOneEquiv` — Myhill's isomorphism theorem;
* `Lambda.Myhill.recIso_iff_oneOneEquiv` — with its (easy) converse.
-/

import Mathlib.Computability.Reduce

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda
namespace Myhill

/-! ## The chase

The chase is a generic construction: from a start `x`, follow the sequence
`x, G (F x), G (F (G (F x))), …` until `F` of the current point leaves a finite list `out`.
-/

section Esc

variable (F G : ℕ → ℕ) (out : List ℕ)

/-- The sequence `x, G (F x), G (F (G (F x))), …`. -/
def iterGF (F G : ℕ → ℕ) (i x : ℕ) : ℕ := (fun z => G (F z))^[i] x

theorem iterGF_zero (x : ℕ) : iterGF F G 0 x = x := rfl

theorem iterGF_succ (i x : ℕ) : iterGF F G (i + 1) x = iterGF F G i (G (F x)) := by
  simp [iterGF, Function.iterate_succ_apply]

theorem iterGF_succ' (i x : ℕ) : iterGF F G (i + 1) x = G (F (iterGF F G i x)) := by
  simp [iterGF, Function.iterate_succ_apply']

/-- One step of the chase: if a value has already been found, stop; otherwise test `F z`, and
move on to `G (F z)` if `F z` is not usable. -/
def escStep : ℕ × ℕ × Bool → ℕ × ℕ × Bool
  | (z, v, true) => (z, v, true)
  | (z, v, false) => if out.elem (F z) then (G (F z), v, false) else (z, F z, true)

/-- The chase from `x`, run for `b` steps. -/
def escRun (b x : ℕ) : ℕ × ℕ × Bool := (escStep F G out)^[b] (x, 0, false)

/-- The first member of the sequence `F x, F (G (F x)), …` outside `out`, if `b` steps
suffice. -/
def esc (b x : ℕ) : ℕ := (escRun F G out b x).2.1

theorem escStep_found (z v : ℕ) : escStep F G out (z, v, true) = (z, v, true) := rfl

theorem escRun_stable (z v : ℕ) (k : ℕ) :
    (escStep F G out)^[k] (z, v, true) = (z, v, true) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, escStep_found F G out, ih]

/-- **Correctness of the chase.**  If some member of the sequence leaves `out` within `b`
steps, the chase returns the first one, together with the record that all earlier members
were inside `out`. -/
theorem esc_spec (b x : ℕ) (hex : ∃ i < b, F (iterGF F G i x) ∉ out) :
    (∃ i, esc F G out b x = F (iterGF F G i x) ∧
        ∀ j < i, F (iterGF F G j x) ∈ out) ∧
      esc F G out b x ∉ out := by
  induction b generalizing x with
  | zero => obtain ⟨i, hi, -⟩ := hex; exact absurd hi (Nat.not_lt_zero i)
  | succ b ih =>
      by_cases h1 : F x ∈ out
      · -- the first value is unusable: continue the chase from `G (F x)`
        have h1b : out.elem (F x) = true := List.contains_iff_mem.2 h1
        have hstep : escStep F G out (x, 0, false) = (G (F x), 0, false) := by
          rw [escStep, if_pos h1b]
        have hrun : escRun F G out (b + 1) x = escRun F G out b (G (F x)) := by
          rw [escRun, Function.iterate_succ_apply, hstep, escRun]
        have hex' : ∃ i < b, F (iterGF F G i (G (F x))) ∉ out := by
          obtain ⟨i, hi, hval⟩ := hex
          cases i with
          | zero => rw [iterGF_zero] at hval; exact absurd h1 hval
          | succ i =>
              exact ⟨i, Nat.lt_of_succ_lt_succ hi, by rwa [iterGF_succ] at hval⟩
        obtain ⟨⟨i, hi, hprev⟩, hout⟩ := ih (G (F x)) hex'
        refine ⟨⟨i + 1, ?_, ?_⟩, ?_⟩
        · rw [esc, hrun, iterGF_succ]; exact hi
        · intro j hj
          cases j with
          | zero => rwa [iterGF_zero]
          | succ j => rw [iterGF_succ]; exact hprev j (Nat.lt_of_succ_lt_succ hj)
        · rw [esc, hrun]; exact hout
      · -- the first value is usable
        have h1' : ¬ out.elem (F x) = true := fun hmem => h1 (List.contains_iff_mem.1 hmem)
        have hstep : escStep F G out (x, 0, false) = (x, F x, true) := by
          rw [escStep, if_neg h1']
        have hrun : escRun F G out (b + 1) x = (x, F x, true) := by
          rw [escRun, Function.iterate_succ_apply, hstep]
          exact escRun_stable F G out x (F x) b
        refine ⟨⟨0, ?_, ?_⟩, ?_⟩
        · rw [esc, hrun, iterGF_zero]
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · rw [esc, hrun]; exact h1

end Esc

/-! ## Finite partial maps -/

/-- A stage of the back-and-forth construction: a finite partial map, as a list of pairs. -/
abbrev PMap := List (ℕ × ℕ)

/-- The domain of a stage. -/
def dom (p : PMap) : List ℕ := p.map Prod.fst

/-- The range of a stage. -/
def ran (p : PMap) : List ℕ := p.map Prod.snd

/-- The inverse of a stage. -/
def swapMap (p : PMap) : PMap := p.map Prod.swap

/-- Forward lookup in a stage; `0` off the domain. -/
def look : PMap → ℕ → ℕ
  | [], _ => 0
  | (a, b) :: t, x => if a = x then b else look t x

/-- Backward lookup in a stage; `0` off the range. -/
def colook (p : PMap) (y : ℕ) : ℕ := look (swapMap p) y

theorem mem_dom_iff {p : PMap} {x : ℕ} : x ∈ dom p ↔ ∃ y, (x, y) ∈ p := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := List.mem_map.1 h
    exact ⟨b, hq⟩
  · rintro ⟨y, hy⟩
    exact List.mem_map.2 ⟨(x, y), hy, rfl⟩

theorem mem_ran_iff {p : PMap} {y : ℕ} : y ∈ ran p ↔ ∃ x, (x, y) ∈ p := by
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hq, rfl⟩ := List.mem_map.1 h
    exact ⟨a, hq⟩
  · rintro ⟨x, hx⟩
    exact List.mem_map.2 ⟨(x, y), hx, rfl⟩

theorem mem_swapMap {p : PMap} {x y : ℕ} : (y, x) ∈ swapMap p ↔ (x, y) ∈ p := by
  constructor
  · intro h
    obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h
    obtain ⟨a, b⟩ := q
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hq'
    obtain ⟨rfl, rfl⟩ := hq'
    exact hq
  · intro h
    exact List.mem_map.2 ⟨(x, y), h, rfl⟩

theorem dom_swapMap (p : PMap) : dom (swapMap p) = ran p := by
  simp [dom, ran, swapMap, List.map_map, Function.comp_def]

theorem ran_swapMap (p : PMap) : ran (swapMap p) = dom p := by
  simp [dom, ran, swapMap, List.map_map, Function.comp_def]

theorem swapMap_swapMap (p : PMap) : swapMap (swapMap p) = p := by
  simp [swapMap, List.map_map, Function.comp_def]

theorem length_swapMap (p : PMap) : (swapMap p).length = p.length := by
  simp [swapMap]

theorem look_eq_of_mem : ∀ {p : PMap}, (dom p).Nodup → ∀ {x y : ℕ}, (x, y) ∈ p →
    look p x = y := by
  intro p
  induction p with
  | nil => intro _ x y h; exact absurd h (by simp)
  | cons q t ih =>
      obtain ⟨a, b⟩ := q
      intro hnd x y h
      have hnd' : (dom t).Nodup := by
        simpa [dom] using hnd.of_cons
      have hnot : a ∉ dom t := by
        simpa [dom] using hnd.notMem
      rcases List.mem_cons.1 h with hq | hq
      · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hq
        simp [look]
      · have hx : x ∈ dom t := mem_dom_iff.2 ⟨y, hq⟩
        have hax : a ≠ x := fun hax => hnot (hax ▸ hx)
        simp only [look, if_neg hax]
        exact ih hnd' hq

theorem colook_eq_of_mem {p : PMap} (hnd : (ran p).Nodup) {x y : ℕ} (h : (x, y) ∈ p) :
    colook p y = x :=
  look_eq_of_mem (by rwa [dom_swapMap]) (mem_swapMap.2 h)

theorem look_mem {p : PMap} {x : ℕ} (h : x ∈ dom p) : (x, look p x) ∈ p := by
  induction p with
  | nil => exact absurd h (by simp [dom])
  | cons q t ih =>
      obtain ⟨a, b⟩ := q
      by_cases hax : a = x
      · subst hax
        simp [look]
      · have hx : x ∈ dom t := by
          rcases List.mem_cons.1 (show x ∈ a :: dom t from h) with h' | h'
          · exact absurd h'.symm hax
          · exact h'
        simp only [look, if_neg hax]
        exact List.mem_cons_of_mem _ (ih hx)

theorem mem_of_mem_ran {p : PMap} {y : ℕ} (h : y ∈ ran p) : (colook p y, y) ∈ p :=
  mem_swapMap.1 (look_mem (by rwa [dom_swapMap]))

/-! ## The invariant -/

variable {A B : ℕ → Prop}

/-- A stage is *good* when it is injective in both directions and preserves membership. -/
structure Good (A B : ℕ → Prop) (p : PMap) : Prop where
  /-- distinct arguments -/
  domNodup : (dom p).Nodup
  /-- distinct values -/
  ranNodup : (ran p).Nodup
  /-- membership is preserved -/
  pres : ∀ q ∈ p, (A q.1 ↔ B q.2)

theorem good_swapMap {p : PMap} (h : Good A B p) : Good B A (swapMap p) where
  domNodup := by rw [dom_swapMap]; exact h.ranNodup
  ranNodup := by rw [ran_swapMap]; exact h.domNodup
  pres := by
    intro q hq
    obtain ⟨a, b⟩ := q
    exact (h.pres (b, a) (mem_swapMap.1 hq)).symm

/-! ## The escape lemma

The chase used to extend the domain of a stage `p` by a point `x ∉ dom p` runs
`F := f` and `G := colook p`, looking for a value outside `ran p`.  It succeeds within
`p.length + 1` steps, because otherwise it would visit that many distinct points of
`dom p`.
-/

section Escape

variable {f : ℕ → ℕ} {p : PMap}

theorem chase_pair {x i : ℕ} (h : f (iterGF f (colook p) i x) ∈ ran p) :
    (iterGF f (colook p) (i + 1) x, f (iterGF f (colook p) i x)) ∈ p := by
  rw [iterGF_succ']
  exact mem_of_mem_ran h

theorem chase_mem_dom {x i : ℕ} (h : f (iterGF f (colook p) i x) ∈ ran p) :
    iterGF f (colook p) (i + 1) x ∈ dom p :=
  mem_dom_iff.2 ⟨_, chase_pair h⟩

theorem chase_descent (hdn : (dom p).Nodup) (hf : Function.Injective f) {x i j : ℕ}
    (hi : f (iterGF f (colook p) i x) ∈ ran p) (hj : f (iterGF f (colook p) j x) ∈ ran p)
    (he : iterGF f (colook p) (i + 1) x = iterGF f (colook p) (j + 1) x) :
    iterGF f (colook p) i x = iterGF f (colook p) j x := by
  have h1 := chase_pair hi
  have h2 := chase_pair hj
  rw [he] at h1
  exact hf ((look_eq_of_mem hdn h1).symm.trans (look_eq_of_mem hdn h2))

theorem chase_inj (hdn : (dom p).Nodup) (hf : Function.Injective f) {x : ℕ} (hx : x ∉ dom p)
    {n : ℕ} (hall : ∀ i < n, f (iterGF f (colook p) i x) ∈ ran p) :
    ∀ i ≤ n, ∀ j ≤ n, iterGF f (colook p) i x = iterGF f (colook p) j x → i = j := by
  intro i
  induction i with
  | zero =>
      intro _ j hj he
      cases j with
      | zero => rfl
      | succ j =>
          exact absurd (he ▸ chase_mem_dom (hall j (Nat.lt_of_succ_le hj))) (by
            rw [iterGF_zero] at he
            simpa [iterGF_zero, ← he] using hx)
  | succ i ih =>
      intro hi j hj he
      cases j with
      | zero =>
          rw [iterGF_zero] at he
          exact absurd (he ▸ chase_mem_dom (hall i (Nat.lt_of_succ_le hi))) (by simpa using hx)
      | succ j =>
          have := chase_descent hdn hf (hall i (Nat.lt_of_succ_le hi))
            (hall j (Nat.lt_of_succ_le hj)) he
          exact congrArg Nat.succ
            (ih (Nat.le_of_succ_le hi) j (Nat.le_of_succ_le hj) this)

/-- **The escape lemma.**  Chasing from a point outside the domain of `p` reaches a value
outside the range of `p` within `p.length + 1` steps. -/
theorem exists_escape (hdn : (dom p).Nodup) (hf : Function.Injective f) {x : ℕ}
    (hx : x ∉ dom p) : ∃ i < p.length + 1, f (iterGF f (colook p) i x) ∉ ran p := by
  by_contra hcon
  push Not at hcon
  have hmaps : Set.MapsTo (fun i => iterGF f (colook p) (i + 1) x)
      ↑(Finset.range (p.length + 1)) ↑(dom p).toFinset := by
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    simpa using chase_mem_dom (hcon i hi)
  have hinj : Set.InjOn (fun i => iterGF f (colook p) (i + 1) x)
      ↑(Finset.range (p.length + 1)) := by
    intro i hi j hj he
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have := chase_inj hdn hf hx (n := p.length + 1) hcon (i + 1) hi j.succ hj he
    omega
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at hcard
  have h2 := (dom p).toFinset_card_le
  have h3 : (dom p).length = p.length := by simp [dom]
  omega

end Escape

/-! ## Extending a stage -/

section Extend

variable {f g : ℕ → ℕ} {p : PMap}

theorem eq_of_pairs_dom (hg : Good A B p) {x y y' : ℕ} (h : (x, y) ∈ p) (h' : (x, y') ∈ p) :
    y = y' :=
  (look_eq_of_mem hg.domNodup h).symm.trans (look_eq_of_mem hg.domNodup h')

theorem eq_of_pairs_ran (hg : Good A B p) {x x' y : ℕ} (h : (x, y) ∈ p) (h' : (x', y) ∈ p) :
    x = x' :=
  (colook_eq_of_mem hg.ranNodup h).symm.trans (colook_eq_of_mem hg.ranNodup h')

/-- The chase preserves `A`-status: every point it visits has the same status as the start. -/
theorem chase_status (hg : Good A B p) (hAB : ∀ z, A z ↔ B (f z)) (x : ℕ) :
    ∀ i, (∀ j < i, f (iterGF f (colook p) j x) ∈ ran p) →
      (A (iterGF f (colook p) i x) ↔ A x) := by
  intro i
  induction i with
  | zero => intro _; rw [iterGF_zero]
  | succ i ih =>
      intro hprev
      have h1 : A (iterGF f (colook p) (i + 1) x) ↔ B (f (iterGF f (colook p) i x)) :=
        hg.pres _ (chase_pair (hprev i (Nat.lt_succ_self i)))
      rw [h1, ← hAB]
      exact ih fun j hj => hprev j (Nat.lt_succ_of_lt hj)

/-- Extend a stage so that `x` lies in its domain. -/
def extDom (f : ℕ → ℕ) (p : PMap) (x : ℕ) : PMap :=
  if x ∈ dom p then p
  else p ++ [(x, esc f (colook p) (ran p) (p.length + 1) x)]

theorem extDom_of_mem {x : ℕ} (h : x ∈ dom p) : extDom f p x = p := if_pos h

theorem extDom_of_notMem {x : ℕ} (h : x ∉ dom p) :
    extDom f p x = p ++ [(x, esc f (colook p) (ran p) (p.length + 1) x)] := if_neg h

theorem extDom_prefix (f : ℕ → ℕ) (p : PMap) (x : ℕ) : p <+: extDom f p x := by
  by_cases h : x ∈ dom p
  · rw [extDom_of_mem h]
  · rw [extDom_of_notMem h]; exact ⟨_, rfl⟩

theorem mem_dom_extDom (f : ℕ → ℕ) (p : PMap) (x : ℕ) : x ∈ dom (extDom f p x) := by
  by_cases h : x ∈ dom p
  · rwa [extDom_of_mem h]
  · rw [extDom_of_notMem h]; simp [dom]

theorem good_extDom (hf : Function.Injective f) (hAB : ∀ z, A z ↔ B (f z)) (hg : Good A B p)
    (x : ℕ) : Good A B (extDom f p x) := by
  by_cases hx : x ∈ dom p
  · rwa [extDom_of_mem hx]
  · obtain ⟨⟨i, hyi, hprev⟩, hyout⟩ :=
      esc_spec f (colook p) (ran p) (p.length + 1) x (exists_escape hg.domNodup hf hx)
    rw [extDom_of_notMem hx]
    set y := esc f (colook p) (ran p) (p.length + 1) x with hy
    have hAxy : A x ↔ B y := by
      rw [hyi, ← hAB]
      exact (chase_status hg hAB x i hprev).symm
    have hd : dom (p ++ [(x, y)]) = dom p ++ [x] := by simp [dom]
    have hr : ran (p ++ [(x, y)]) = ran p ++ [y] := by simp [ran]
    refine ⟨?_, ?_, ?_⟩
    · rw [hd]
      simp only [List.nodup_append, hg.domNodup, List.nodup_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_self, true_and]
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb; subst hab
      exact hx ha
    · rw [hr]
      simp only [List.nodup_append, hg.ranNodup, List.nodup_cons, List.not_mem_nil,
        not_false_eq_true, List.nodup_nil, and_self, true_and]
      intro a ha b hb hab
      rw [List.mem_singleton] at hb
      subst hb; subst hab
      exact hyout ha
    · intro q hq
      rcases List.mem_append.1 hq with h | h
      · exact hg.pres q h
      · rw [List.mem_singleton] at h
        subst h
        exact hAxy

/-- Extend a stage so that `y` lies in its range. -/
def extRan (g : ℕ → ℕ) (p : PMap) (y : ℕ) : PMap := swapMap (extDom g (swapMap p) y)

theorem extRan_prefix (g : ℕ → ℕ) (p : PMap) (y : ℕ) : p <+: extRan g p y := by
  have h := (extDom_prefix g (swapMap p) y).map Prod.swap
  rw [← swapMap, ← swapMap, swapMap_swapMap] at h
  exact h

theorem mem_ran_extRan (g : ℕ → ℕ) (p : PMap) (y : ℕ) : y ∈ ran (extRan g p y) := by
  rw [extRan, ran_swapMap]; exact mem_dom_extDom g (swapMap p) y

theorem good_extRan (hg' : Function.Injective g) (hBA : ∀ z, B z ↔ A (g z)) (hg : Good A B p)
    (y : ℕ) : Good A B (extRan g p y) := by
  have := good_extDom hg' hBA (good_swapMap hg) y
  simpa [extRan] using good_swapMap this

end Extend

/-! ## The back-and-forth construction -/

/-- The stages of the construction: even steps put a new point into the domain, odd steps
put a new point into the range. -/
def stage (f g : ℕ → ℕ) : ℕ → PMap
  | 0 => []
  | n + 1 => if n % 2 = 0 then extDom f (stage f g n) (n / 2) else extRan g (stage f g n) (n / 2)

section Stage

variable {A B : ℕ → Prop} {f g : ℕ → ℕ}

theorem stage_zero (f g : ℕ → ℕ) : stage f g 0 = [] := rfl

theorem stage_succ (f g : ℕ → ℕ) (n : ℕ) :
    stage f g (n + 1) =
      if n % 2 = 0 then extDom f (stage f g n) (n / 2) else extRan g (stage f g n) (n / 2) := rfl

theorem stage_prefix_succ (f g : ℕ → ℕ) (n : ℕ) : stage f g n <+: stage f g (n + 1) := by
  rw [stage_succ]
  split
  · exact extDom_prefix _ _ _
  · exact extRan_prefix _ _ _

theorem stage_prefix (f g : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) : stage f g m <+: stage f g n := by
  induction n with
  | zero => rw [Nat.le_zero.1 h]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · exact (ih (Nat.lt_succ_iff.1 hm)).trans (stage_prefix_succ f g n)
      · rw [Nat.le_antisymm h hm]

theorem mem_stage_mono (f g : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) {q : ℕ × ℕ} (hq : q ∈ stage f g m) :
    q ∈ stage f g n :=
  (stage_prefix f g h).subset hq

theorem good_stage (hf : Function.Injective f) (hAB : ∀ z, A z ↔ B (f z))
    (hg' : Function.Injective g) (hBA : ∀ z, B z ↔ A (g z)) (n : ℕ) : Good A B (stage f g n) := by
  induction n with
  | zero =>
      exact ⟨List.nodup_nil, List.nodup_nil, fun q hq => absurd hq (by simp [stage_zero])⟩
  | succ n ih =>
      rw [stage_succ]
      split
      · exact good_extDom hf hAB ih _
      · exact good_extRan hg' hBA ih _

theorem mem_dom_stage (f g : ℕ → ℕ) (x : ℕ) : x ∈ dom (stage f g (2 * x + 1)) := by
  rw [stage_succ]
  rw [if_pos (Nat.mul_mod_right 2 x), Nat.mul_div_cancel_left x (by omega)]
  exact mem_dom_extDom f _ x

theorem mem_ran_stage (f g : ℕ → ℕ) (y : ℕ) : y ∈ ran (stage f g (2 * y + 2)) := by
  have h1 : (2 * y + 1) % 2 ≠ 0 := by omega
  have h2 : (2 * y + 1) / 2 = y := by omega
  have : stage f g (2 * y + 2) = extRan g (stage f g (2 * y + 1)) y := by
    rw [show 2 * y + 2 = (2 * y + 1) + 1 from rfl, stage_succ, if_neg h1, h2]
  rw [this]
  exact mem_ran_extRan g _ y

/-- The isomorphism produced by the construction. -/
def isoFun (f g : ℕ → ℕ) (x : ℕ) : ℕ := look (stage f g (2 * x + 1)) x

theorem isoFun_pair (f g : ℕ → ℕ) (x : ℕ) : (x, isoFun f g x) ∈ stage f g (2 * x + 1) :=
  look_mem (mem_dom_stage f g x)

theorem isoFun_eq_of_mem (hf : Function.Injective f) (hAB : ∀ z, A z ↔ B (f z))
    (hg' : Function.Injective g) (hBA : ∀ z, B z ↔ A (g z)) {x y n : ℕ}
    (h : (x, y) ∈ stage f g n) : isoFun f g x = y :=
  eq_of_pairs_dom (good_stage hf hAB hg' hBA (max n (2 * x + 1)))
    (mem_stage_mono f g (le_max_right n (2 * x + 1)) (isoFun_pair f g x))
    (mem_stage_mono f g (le_max_left n (2 * x + 1)) h)

theorem isoFun_injective (hf : Function.Injective f) (hAB : ∀ z, A z ↔ B (f z))
    (hg' : Function.Injective g) (hBA : ∀ z, B z ↔ A (g z)) :
    Function.Injective (isoFun f g) := by
  intro x x' hxx
  set n := max (2 * x + 1) (2 * x' + 1) with hn
  refine eq_of_pairs_ran (good_stage hf hAB hg' hBA n)
    (mem_stage_mono f g (le_max_left _ _) (isoFun_pair f g x)) ?_
  have := mem_stage_mono f g (le_max_right (2 * x + 1) (2 * x' + 1)) (isoFun_pair f g x')
  rwa [← hxx] at this

theorem isoFun_surjective (hf : Function.Injective f) (hAB : ∀ z, A z ↔ B (f z))
    (hg' : Function.Injective g) (hBA : ∀ z, B z ↔ A (g z)) :
    Function.Surjective (isoFun f g) := by
  intro y
  obtain ⟨x, hx⟩ := mem_ran_iff.1 (mem_ran_stage f g y)
  exact ⟨x, isoFun_eq_of_mem hf hAB hg' hBA hx⟩

theorem isoFun_spec (hf : Function.Injective f) (hAB : ∀ z, A z ↔ B (f z))
    (hg' : Function.Injective g) (hBA : ∀ z, B z ↔ A (g z)) (x : ℕ) :
    A x ↔ B (isoFun f g x) :=
  (good_stage hf hAB hg' hBA (2 * x + 1)).pres _ (isoFun_pair f g x)

end Stage

/-! ## Computability of the construction -/

section Computability

/-- Iterating a computable step function a computable number of times is computable. -/
theorem computable_iterate {α σ : Type} [Primcodable α] [Primcodable σ] {n : α → ℕ} {st : α → σ}
    {h : α → σ → σ} (hn : Computable n) (hst : Computable st) (hh : Computable₂ h) :
    Computable fun a => (h a)^[n a] (st a) := by
  have key : ∀ (k : ℕ) (a : α),
      Nat.rec (motive := fun _ => σ) (st a) (fun _ IH => h a IH) k = (h a)^[k] (st a) := by
    intro k
    induction k with
    | zero => intro a; rfl
    | succ k ih => intro a; rw [Function.iterate_succ_apply']; exact congrArg (h a) (ih a)
  exact (Computable.nat_rec hn hst
    (hh.comp Computable.fst (Computable.snd.comp Computable.snd)).to₂).of_eq
    fun a => key (n a) a

theorem primrec_elem : Primrec₂ fun (l : List ℕ) (y : ℕ) => List.elem y l := by
  have h : PrimrecPred fun a : List ℕ × ℕ => a.2 ∈ a.1 :=
    PrimrecPred.of_eq
      (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.snd Primrec.fst)
        (Primrec.list_length.comp Primrec.fst))
      fun _ => List.idxOf_lt_length_iff
  exact h.decide.of_eq fun _ => by simp

theorem primrec_dom : Primrec dom :=
  (Primrec.list_map Primrec.id (Primrec.fst.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_ran : Primrec ran :=
  (Primrec.list_map Primrec.id (Primrec.snd.comp Primrec.snd).to₂).of_eq fun _ => rfl

theorem primrec_swapMap : Primrec swapMap :=
  (Primrec.list_map Primrec.id
    ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)).to₂).of_eq fun _ => rfl

theorem look_eq_rec (p : PMap) (x : ℕ) :
    List.rec (motive := fun _ => ℕ) 0 (fun q _ IH => if q.1 = x then q.2 else IH) p = look p x := by
  induction p with
  | nil => rfl
  | cons u t ih =>
      obtain ⟨u1, u2⟩ := u
      change (if u1 = x then u2 else
        List.rec (motive := fun _ => ℕ) 0 (fun q _ IH => if q.1 = x then q.2 else IH) t) =
          look ((u1, u2) :: t) x
      rw [ih]
      rfl

theorem primrec_look : Primrec₂ look := by
  have hh : Primrec₂ fun (a : PMap × ℕ) (t : (ℕ × ℕ) × PMap × ℕ) =>
      if t.1.1 = a.2 then t.1.2 else t.2.2 :=
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.list_rec (α := PMap × ℕ) (β := ℕ × ℕ) (σ := ℕ)
    (f := fun a => a.1) (g := fun _ => 0)
    (h := fun a t => if t.1.1 = a.2 then t.1.2 else t.2.2)
    Primrec.fst (Primrec.const 0) hh
  exact h.of_eq fun a => look_eq_rec a.1 a.2

theorem primrec_colook : Primrec₂ colook :=
  primrec_look.comp (primrec_swapMap.comp Primrec.fst) Primrec.snd

theorem escStep_eq (F G : ℕ → ℕ) (out : List ℕ) (s : ℕ × ℕ × Bool) :
    escStep F G out s =
      cond s.2.2 s (cond (List.elem (F s.1) out) (G (F s.1), s.2.1, false) (s.1, F s.1, true)) := by
  obtain ⟨z, v, b⟩ := s
  cases b
  · change (if List.elem (F z) out = true then (G (F z), v, false) else (z, F z, true)) =
      cond false (z, v, false)
        (cond (List.elem (F z) out) (G (F z), v, false) (z, F z, true))
    cases hc : List.elem (F z) out <;> rfl
  · rfl

variable {f g : ℕ → ℕ}

theorem computable_escStepPMap (hf : Computable f) :
    Computable₂ fun (p : PMap) (s : ℕ × ℕ × Bool) => escStep f (colook p) (ran p) s := by
  have hFz : Computable fun a : PMap × (ℕ × ℕ × Bool) => f a.2.1 :=
    hf.comp (Computable.fst.comp Computable.snd)
  have hran : Computable fun a : PMap × (ℕ × ℕ × Bool) => ran a.1 :=
    primrec_ran.to_comp.comp Computable.fst
  have hmem : Computable fun a : PMap × (ℕ × ℕ × Bool) => List.elem (f a.2.1) (ran a.1) :=
    primrec_elem.to_comp.comp hran hFz
  have hco : Computable fun a : PMap × (ℕ × ℕ × Bool) => colook a.1 (f a.2.1) :=
    primrec_colook.to_comp.comp Computable.fst hFz
  have hbranch : Computable fun a : PMap × (ℕ × ℕ × Bool) =>
      cond (List.elem (f a.2.1) (ran a.1)) (colook a.1 (f a.2.1), a.2.2.1, false)
        (a.2.1, f a.2.1, true) :=
    Computable.cond hmem
      (hco.pair ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
        (Computable.const false)))
      ((Computable.fst.comp Computable.snd).pair (hFz.pair (Computable.const true)))
  exact ((Computable.cond
    (Computable.snd.comp (Computable.snd.comp Computable.snd)) Computable.snd hbranch).of_eq
    fun a => (escStep_eq f (colook a.1) (ran a.1) a.2).symm).to₂

theorem computable_escPMap (hf : Computable f) :
    Computable fun a : PMap × ℕ => esc f (colook a.1) (ran a.1) (a.1.length + 1) a.2 := by
  have hn : Computable fun a : PMap × ℕ => a.1.length + 1 :=
    (Primrec.succ.comp (Primrec.list_length.comp Primrec.fst)).to_comp
  have hst : Computable fun a : PMap × ℕ => (a.2, 0, false) :=
    (Primrec.snd.pair ((Primrec.const 0).pair (Primrec.const false))).to_comp
  have hh : Computable₂ fun (a : PMap × ℕ) (s : ℕ × ℕ × Bool) =>
      escStep f (colook a.1) (ran a.1) s :=
    ((computable_escStepPMap hf).comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  exact Computable.fst.comp (Computable.snd.comp (computable_iterate hn hst hh))

theorem extDom_eq_cond (f : ℕ → ℕ) (p : PMap) (x : ℕ) :
    extDom f p x =
      cond (List.elem x (dom p)) p (p ++ [(x, esc f (colook p) (ran p) (p.length + 1) x)]) := by
  by_cases hx : x ∈ dom p
  · rw [extDom_of_mem hx, show List.elem x (dom p) = true from List.contains_iff_mem.2 hx]
    rfl
  · have h : List.elem x (dom p) = false := by
      cases he : List.elem x (dom p)
      · rfl
      · exact absurd (List.contains_iff_mem.1 he) hx
    rw [extDom_of_notMem hx, h]
    rfl

theorem computable_extDom (hf : Computable f) : Computable₂ (extDom f) := by
  have hdom : Computable fun a : PMap × ℕ => dom a.1 := primrec_dom.to_comp.comp Computable.fst
  have hmem : Computable fun a : PMap × ℕ => List.elem a.2 (dom a.1) :=
    primrec_elem.to_comp.comp hdom Computable.snd
  have hnew : Computable fun a : PMap × ℕ =>
      a.1 ++ [(a.2, esc f (colook a.1) (ran a.1) (a.1.length + 1) a.2)] :=
    Primrec.list_append.to_comp.comp Computable.fst
      (Primrec.list_cons.to_comp.comp (Computable.snd.pair (computable_escPMap hf))
        (Computable.const []))
  exact ((Computable.cond hmem Computable.fst hnew).of_eq
    fun a => (extDom_eq_cond f a.1 a.2).symm).to₂

theorem computable_extRan (hg : Computable g) : Computable₂ (extRan g) :=
  (primrec_swapMap.to_comp.comp
    ((computable_extDom hg).comp (primrec_swapMap.to_comp.comp Computable.fst)
      Computable.snd)).to₂

theorem computable_stage (hf : Computable f) (hg : Computable g) : Computable (stage f g) := by
  have key : ∀ n : ℕ, Nat.rec (motive := fun _ => PMap) []
      (fun k IH => cond (decide (k % 2 = 0)) (extDom f IH (k / 2)) (extRan g IH (k / 2))) n
      = stage f g n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [stage_succ, ← ih]
        exact Bool.cond_decide _ _ _
  have hk : Computable fun a : ℕ × (ℕ × PMap) => a.2.1 / 2 :=
    (Primrec.nat_div.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2)).to_comp
  have hIH : Computable fun a : ℕ × (ℕ × PMap) => a.2.2 :=
    Computable.snd.comp Computable.snd
  have hc : Computable fun a : ℕ × (ℕ × PMap) => decide (a.2.1 % 2 = 0) :=
    (PrimrecPred.decide (p := fun a : ℕ × (ℕ × PMap) => a.2.1 % 2 = 0)
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 2))
        (Primrec.const 0))).to_comp
  have hstep : Computable₂ fun (_ : ℕ) (q : ℕ × PMap) =>
      cond (decide (q.1 % 2 = 0)) (extDom f q.2 (q.1 / 2)) (extRan g q.2 (q.1 / 2)) :=
    (Computable.cond hc ((computable_extDom hf).comp hIH hk)
      ((computable_extRan hg).comp hIH hk)).to₂
  exact (Computable.nat_rec Computable.id (Computable.const []) hstep).of_eq key

theorem computable_isoFun (hf : Computable f) (hg : Computable g) : Computable (isoFun f g) :=
  primrec_look.to_comp.comp
    ((computable_stage hf hg).comp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).to_comp)
    Computable.id

end Computability

/-! ## Myhill's isomorphism theorem -/

/-- Two sets of numbers are *recursively isomorphic* when some computable bijection of `ℕ`
carries one onto the other. -/
def RecIso (A B : ℕ → Prop) : Prop :=
  ∃ h : ℕ → ℕ, Computable h ∧ Function.Bijective h ∧ ∀ x, A x ↔ B (h x)

/-- **Myhill's isomorphism theorem.**  One-one equivalent sets of numbers are recursively
isomorphic. -/
theorem recIso_of_oneOneEquiv {A B : ℕ → Prop} (h : OneOneEquiv A B) : RecIso A B := by
  obtain ⟨⟨f, hfc, hfi, hfs⟩, ⟨g, hgc, hgi, hgs⟩⟩ := h
  exact ⟨isoFun f g, computable_isoFun hfc hgc,
    ⟨isoFun_injective hfi hfs hgi hgs, isoFun_surjective hfi hfs hgi hgs⟩,
    isoFun_spec hfi hfs hgi hgs⟩

/-- The inverse of a computable bijection of `ℕ` is computable: search for the (unique)
preimage. -/
theorem exists_computable_inverse {h : ℕ → ℕ} (hc : Computable h) (hb : Function.Bijective h) :
    ∃ k : ℕ → ℕ, Computable k ∧ Function.LeftInverse k h ∧ Function.RightInverse k h := by
  have hsurj : ∀ y, ∃ x, h x = y := hb.2
  refine ⟨fun y => Nat.find (hsurj y), ?_, ?_, ?_⟩
  · have hdec : Computable₂ fun y x : ℕ => decide (h x = y) :=
      ((Primrec.eq.decide.to_comp.to₂).comp (hc.comp Computable.snd) Computable.fst).to₂
    have hP : Partrec₂ fun y x : ℕ => (decide (h x = y) : Part Bool) := hdec.partrec₂
    refine (Partrec.rfind hP).of_eq fun y => ?_
    refine Part.eq_some_iff.2 (Nat.mem_rfind.2 ⟨?_, ?_⟩)
    · simp [Nat.find_spec (hsurj y)]
    · intro m hm
      simp [Nat.find_min (hsurj y) hm]
  · intro x
    exact hb.1 (Nat.find_spec (hsurj (h x)))
  · intro y
    exact Nat.find_spec (hsurj y)

/-- The converse of Myhill's theorem: recursively isomorphic sets are one-one equivalent. -/
theorem oneOneEquiv_of_recIso {A B : ℕ → Prop} (h : RecIso A B) : OneOneEquiv A B := by
  obtain ⟨hh, hc, hb, hs⟩ := h
  obtain ⟨k, hkc, -, hkr⟩ := exists_computable_inverse hc hb
  exact ⟨⟨hh, hc, hb.1, hs⟩, ⟨k, hkc, hkr.injective, fun y => by rw [hs (k y), hkr y]⟩⟩

/-- **Myhill's isomorphism theorem**, as a characterisation: two sets of numbers are
recursively isomorphic exactly when they are one-one equivalent. -/
theorem recIso_iff_oneOneEquiv {A B : ℕ → Prop} : RecIso A B ↔ OneOneEquiv A B :=
  ⟨oneOneEquiv_of_recIso, recIso_of_oneOneEquiv⟩


end Myhill
end Lambda
