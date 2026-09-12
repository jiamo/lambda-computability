/-
**The space of the Krivine machine with sharing: live data and garbage collection.**

`Start/KrivineHeap.lean` implements the Krivine machine on a code table and a heap and proves
that the implementation simulates the machine step for step; `Start/KrivineHeapCost.lean` measures
what a transition *costs in time*.  Nothing there measures space, and the reason is visible in
`Krivine.Impl.hstep`: every administrative transition appends a cell and no cell is ever removed,
so the length of the heap after `n` transitions is `n` — a time measure wearing the clothes of a
space measure.

This module supplies the missing notion.  The space of a state is the number of cells that are
*live*: reachable from the environment pointer or from the stack.  What makes this a legitimate
measure, rather than an optimistic under-count, is proved here:

* nothing but the live cells is ever read — two heaps that agree on them decode the state the
  same way (`Krivine.Impl.decState_congr_live`);
* the dead cells can actually be removed — that is `Start/KrivineSpaceGc.lean`.

Main definitions:

* `Krivine.Impl.Cell.refs` — the addresses a cell refers to;
* `Krivine.Impl.reachF`, `Krivine.Impl.reach` — the addresses reachable from an address;
* `Krivine.Impl.liveList`, `Krivine.Impl.space` — the live addresses of a state, in increasing
  order, and their number;
* `Krivine.Impl.rankIn` — the rank of an address among the selected ones, which
  `Start/KrivineSpaceGc.lean` uses to rename the live addresses.

Main results:

* `Krivine.Impl.reachF_eq_reach` — reachability does not depend on the fuel used to compute it;
* `Krivine.Impl.reach_refs` — the reachable set is closed under the references of its cells;
* `Krivine.Impl.decState_congr_live` — **only the live cells are read**;
* `Krivine.Impl.space_initState`, `Krivine.Impl.space_hstep_le` — the space is zero initially and
  grows by at most one per transition.

Garbage collection itself — that the dead cells can be removed without changing the run — is
`Start/KrivineSpaceGc.lean`.
-/

import Start.KrivineHeap

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-! ### The references of a cell -/

/-- The addresses a cell refers to. -/
def Cell.refs : Cell → List ℕ
  | Cell.clos _ e => e.toList
  | Cell.cons a t => a :: t.toList

@[simp] theorem Cell.refs_clos (c : ℕ) (e : Option ℕ) :
    (Cell.clos c e).refs = e.toList := rfl

@[simp] theorem Cell.refs_cons (a : ℕ) (t : Option ℕ) :
    (Cell.cons a t).refs = a :: t.toList := rfl

/-- Under well-formedness the references of the cell at `p` are below `p`. -/
theorem Cell.refs_lt {c : Cell} {p : ℕ} (h : c.refsLt p) : ∀ b ∈ c.refs, b < p := by
  cases c with
  | clos c e =>
      intro b hb
      exact h b (by simpa using hb)
  | cons a t =>
      intro b hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact h.1
      · exact h.2 b (by simpa using hb)

/-! ### Reachability -/

/-- The addresses reachable from `p`, with `fuel` bounding the depth of the walk.  A dangling
address contributes nothing. -/
def reachF (hp : Heap) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, p =>
      match hp[p]? with
      | none => []
      | some c => p :: c.refs.flatMap (reachF hp fuel)

/-- **The addresses reachable from `p`.** -/
def reach (hp : Heap) (p : ℕ) : List ℕ := reachF hp hp.length p

theorem reachF_succ_eq {hp : Heap} {fuel p : ℕ} {c : Cell} (h : hp[p]? = some c) :
    reachF hp (fuel + 1) p = p :: c.refs.flatMap (reachF hp fuel) := by
  simp only [reachF, h]

theorem reachF_succ_none {hp : Heap} {fuel p : ℕ} (h : hp[p]? = none) :
    reachF hp (fuel + 1) p = [] := by
  simp only [reachF, h]

/-- Everything reachable is an address of the heap. -/
theorem mem_reachF_lt {hp : Heap} : ∀ (fuel p a : ℕ), a ∈ reachF hp fuel p → a < hp.length := by
  intro fuel
  induction fuel with
  | zero => intro p a ha; simp [reachF] at ha
  | succ fuel ih =>
      intro p a ha
      cases hc : hp[p]? with
      | none => rw [reachF_succ_none hc] at ha; simp at ha
      | some c =>
          rw [reachF_succ_eq hc] at ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact lt_length_of_getElem? hc
          · obtain ⟨b, _, hb⟩ := List.mem_flatMap.1 ha
            exact ih b a hb

/-- With at least one unit of fuel, a live address is reachable from itself. -/
theorem mem_reachF_self {hp : Heap} {fuel p : ℕ} {c : Cell} (h : hp[p]? = some c) :
    p ∈ reachF hp (fuel + 1) p := by
  rw [reachF_succ_eq h]; exact List.mem_cons_self ..

/-- Reachability does not depend on the fuel, as long as there is enough of it: with a
well-formed heap the walk from `p` only visits addresses below `p`. -/
theorem reachF_eq_of_lt {hp : Heap} (hwf : HeapWF hp) :
    ∀ p, ∀ f₁ f₂, p < f₁ → p < f₂ → reachF hp f₁ p = reachF hp f₂ p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
      intro f₁ f₂ h₁ h₂
      obtain ⟨k₁, rfl⟩ : ∃ k, f₁ = k + 1 := ⟨f₁ - 1, by omega⟩
      obtain ⟨k₂, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
      cases hc : hp[p]? with
      | none => rw [reachF_succ_none hc, reachF_succ_none hc]
      | some c =>
          have hplt : p < hp.length := lt_length_of_getElem? hc
          have hcase : (hp[p]'hplt) = c := by
            have := List.getElem?_eq_getElem hplt
            rw [this] at hc
            exact Option.some_inj.1 hc
          have hrefs : c.refsLt p := by
            have := hwf p hplt
            rwa [hcase] at this
          rw [reachF_succ_eq hc, reachF_succ_eq hc]
          congr 1
          refine List.flatMap_congr ?_
          intro b hb
          have hblt : b < p := Cell.refs_lt hrefs b hb
          exact ih b hblt k₁ k₂ (by omega) (by omega)

/-- Reachability computed with any sufficient fuel is `Krivine.Impl.reach`. -/
theorem reachF_eq_reach {hp : Heap} (hwf : HeapWF hp) {p f : ℕ} (hp0 : p < hp.length)
    (hf : p < f) : reachF hp f p = reach hp p :=
  reachF_eq_of_lt hwf p f hp.length hf hp0

/-- Everything reachable is an address of the heap. -/
theorem mem_reach_lt {hp : Heap} {p a : ℕ} (h : a ∈ reach hp p) : a < hp.length :=
  mem_reachF_lt hp.length p a h

/-- A dangling address reaches nothing. -/
theorem reach_eq_nil {hp : Heap} {p : ℕ} (h : hp[p]? = none) : reach hp p = [] := by
  cases hlen : hp.length with
  | zero => simp [reach, hlen, reachF]
  | succ m => rw [reach, hlen, reachF_succ_none h]

/-- A live address is reachable from itself. -/
theorem mem_reach_self {hp : Heap} {p : ℕ} {c : Cell} (h : hp[p]? = some c) : p ∈ reach hp p := by
  have hplt : p < hp.length := lt_length_of_getElem? h
  obtain ⟨m, hm⟩ : ∃ m, hp.length = m + 1 := ⟨hp.length - 1, by omega⟩
  rw [reach, hm]
  exact mem_reachF_self h

/-- Unfolding reachability one step. -/
theorem reach_eq {hp : Heap} (hwf : HeapWF hp) {p : ℕ} {c : Cell} (h : hp[p]? = some c) :
    reach hp p = p :: c.refs.flatMap (reach hp) := by
  have hplt : p < hp.length := lt_length_of_getElem? h
  have hcase : (hp[p]'hplt) = c := by
    have := List.getElem?_eq_getElem hplt
    rw [this] at h
    exact Option.some_inj.1 h
  have hrefs : c.refsLt p := by
    have := hwf p hplt
    rwa [hcase] at this
  obtain ⟨m, hm⟩ : ∃ m, hp.length = m + 1 := ⟨hp.length - 1, by omega⟩
  rw [reach, hm, reachF_succ_eq h]
  congr 1
  refine List.flatMap_congr ?_
  intro b hb
  have hblt : b < p := Cell.refs_lt hrefs b hb
  exact reachF_eq_reach hwf (by omega) (by omega)

/-- **The reachable set is closed under references.** -/
theorem reach_refs {hp : Heap} (hwf : HeapWF hp) {p a : ℕ} (ha : a ∈ reach hp p) {c : Cell}
    (hc : hp[a]? = some c) {b : ℕ} (hb : b ∈ c.refs) : b ∈ reach hp p := by
  -- induction on the address `p`, which strictly decreases along references
  induction p using Nat.strong_induction_on with
  | _ p ih =>
      cases hcp : hp[p]? with
      | none => rw [reach_eq_nil hcp] at ha; simp at ha
      | some cp =>
          have hplt : p < hp.length := lt_length_of_getElem? hcp
          have hcase : (hp[p]'hplt) = cp := by
            have := List.getElem?_eq_getElem hplt
            rw [this] at hcp
            exact Option.some_inj.1 hcp
          have hrefs : cp.refsLt p := by
            have := hwf p hplt
            rwa [hcase] at this
          rw [reach_eq hwf hcp] at ha ⊢
          rcases List.mem_cons.1 ha with rfl | ha
          · -- `a = p`: the references of `p` are reachable from `p`
            have : c = cp := by rw [hc] at hcp; exact Option.some_inj.1 hcp
            subst this
            refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, hb, ?_⟩)
            have hblt : b < a := Cell.refs_lt hrefs b hb
            have hbl : b < hp.length := lt_trans hblt hplt
            exact mem_reach_self (List.getElem?_eq_getElem hbl)
          · obtain ⟨q, hq, haq⟩ := List.mem_flatMap.1 ha
            have hqlt : q < p := Cell.refs_lt hrefs q hq
            exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨q, hq, ih q hqlt haq⟩)

/-- A closure walked to a dangling address is the dummy closure. -/
theorem decClos_of_none {tab : Tab} {hp : Heap} {p : ℕ} (h : hp[p]? = none) :
    decClos tab hp p = Clos.mk (Lambda.var 0) [] := by
  rw [decClos]
  cases hlen : hp.length with
  | zero => simp [decClF]
  | succ m => simp only [decClF, h]

/-- An environment read at a dangling address is empty. -/
theorem decEnvP_of_none {tab : Tab} {hp : Heap} {p : ℕ} (h : hp[p]? = none) :
    decEnvP tab hp (some p) = [] := by
  rw [decEnvP]
  cases hlen : hp.length with
  | zero => simp [decEnvF]
  | succ m => simp only [decEnvF, h]

/-- An environment read at a closure cell is empty. -/
theorem decEnvP_of_clos {tab : Tab} {hp : Heap} {p c : ℕ} {e : Option ℕ}
    (h : hp[p]? = some (Cell.clos c e)) : decEnvP tab hp (some p) = [] := by
  have hplt : p < hp.length := lt_length_of_getElem? h
  obtain ⟨m, hm⟩ : ∃ m, hp.length = m + 1 := ⟨hp.length - 1, by omega⟩
  rw [decEnvP, hm]
  exact decEnvF_clos_eq h

/-- A closure read at a cons cell is the dummy closure. -/
theorem decClos_of_cons {tab : Tab} {hp : Heap} {p a : ℕ} {t : Option ℕ}
    (h : hp[p]? = some (Cell.cons a t)) : decClos tab hp p = Clos.mk (Lambda.var 0) [] := by
  have hplt : p < hp.length := lt_length_of_getElem? h
  obtain ⟨m, hm⟩ : ∃ m, hp.length = m + 1 := ⟨hp.length - 1, by omega⟩
  rw [decClos, hm]
  exact decClF_cons_eq h

/-- What is reachable from a reference of a cell is reachable from the cell. -/
theorem reach_subset_of_refs {hp : Heap} (hwf : HeapWF hp) {p : ℕ} {c : Cell}
    (hc : hp[p]? = some c) {b : ℕ} (hb : b ∈ c.refs) : ∀ a ∈ reach hp b, a ∈ reach hp p := by
  intro a ha
  rw [reach_eq hwf hc]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, hb, ha⟩)

/-- A reference of a cell is reachable from it. -/
theorem mem_reach_of_refs {hp : Heap} (hwf : HeapWF hp) {p : ℕ} {c : Cell}
    (hc : hp[p]? = some c) {b : ℕ} (hb : b ∈ c.refs) : b ∈ reach hp p := by
  have hplt : p < hp.length := lt_length_of_getElem? hc
  have hcase : (hp[p]'hplt) = c := by
    have := List.getElem?_eq_getElem hplt
    rw [this] at hc
    exact Option.some_inj.1 hc
  have hrefs : c.refsLt p := by
    have := hwf p hplt
    rwa [hcase] at this
  have hblt : b < p := Cell.refs_lt hrefs b hb
  exact reach_subset_of_refs hwf hc hb b (mem_reach_self (List.getElem?_eq_getElem
    (lt_trans hblt hplt)))

/-! ### Only the live cells are read -/

/-- The joint statement for the two decoders: they only look at the cells reachable from the
address they are given. -/
private theorem dec_congr_aux {tab : Tab} {hp hp' : Heap} (hwf : HeapWF hp)
    (hwf' : HeapWF hp') :
    ∀ p, (∀ a ∈ p :: reach hp p, hp[a]? = hp'[a]?) →
      decClos tab hp p = decClos tab hp' p ∧
        decEnvP tab hp (some p) = decEnvP tab hp' (some p) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hag
    have hp_eq : hp[p]? = hp'[p]? := hag p (List.mem_cons_self ..)
    cases hc : hp[p]? with
    | none =>
        have hc' : hp'[p]? = none := by rw [← hp_eq, hc]
        exact ⟨by rw [decClos_of_none hc, decClos_of_none hc'],
          by rw [decEnvP_of_none hc, decEnvP_of_none hc']⟩
    | some c =>
        have hc' : hp'[p]? = some c := by rw [← hp_eq, hc]
        have hplt : p < hp.length := lt_length_of_getElem? hc
        have hcase : (hp[p]'hplt) = c := by
          have := List.getElem?_eq_getElem hplt
          rw [this] at hc
          exact Option.some_inj.1 hc
        have hrefs : c.refsLt p := by
          have := hwf p hplt
          rwa [hcase] at this
        -- the agreement transfers to every reference of the cell
        have hsub : ∀ b ∈ c.refs, ∀ a ∈ b :: reach hp b, hp[a]? = hp'[a]? := by
          intro b hb a ha
          rcases List.mem_cons.1 ha with rfl | ha
          · exact hag a (List.mem_cons_of_mem _ (mem_reach_of_refs hwf hc hb))
          · exact hag a (List.mem_cons_of_mem _ (reach_subset_of_refs hwf hc hb a ha))
        cases c with
        | clos code e =>
            have henv : decEnvP tab hp e = decEnvP tab hp' e := by
              cases e with
              | none => simp
              | some j =>
                  have hj : j < p := Cell.refs_lt hrefs j (by simp)
                  exact (ih j hj (hsub j (by simp))).2
            exact ⟨by rw [decClos_clos hwf hc, decClos_clos hwf' hc', henv],
              by rw [decEnvP_of_clos hc, decEnvP_of_clos hc']⟩
        | cons a t =>
            have hacl : decClos tab hp a = decClos tab hp' a := by
              have hj : a < p := Cell.refs_lt hrefs a (by simp)
              exact (ih a hj (hsub a (by simp))).1
            have htl : decEnvP tab hp t = decEnvP tab hp' t := by
              cases t with
              | none => simp
              | some j =>
                  have hj : j < p := Cell.refs_lt hrefs j (by simp)
                  exact (ih j hj (hsub j (by simp))).2
            refine ⟨by rw [decClos_of_cons hc, decClos_of_cons hc'], ?_⟩
            rw [decEnvP_cons hwf hc, decEnvP_cons hwf' hc', hacl, htl]

/-! ### Selecting addresses, and their ranks -/

/-- The addresses below `n` satisfying `P`, in increasing order. -/
def upto (P : ℕ → Bool) (n : ℕ) : List ℕ := (List.range n).filter P

/-- **The rank of an address**: how many selected addresses lie strictly below it.  On a selected
address this is its position in `Krivine.Impl.upto`, which is what garbage collection renames it
to. -/
def rankIn (P : ℕ → Bool) (a : ℕ) : ℕ := (upto P a).length

@[simp] theorem mem_upto {P : ℕ → Bool} {n a : ℕ} : a ∈ upto P n ↔ a < n ∧ P a := by
  simp [upto, List.mem_filter]

theorem upto_succ (P : ℕ → Bool) (n : ℕ) :
    upto P (n + 1) = upto P n ++ (if P n then [n] else []) := by
  simp only [upto, List.range_succ, List.filter_append]
  cases h : P n <;> simp [List.filter, h]

theorem upto_prefix {P : ℕ → Bool} {m n : ℕ} (h : m ≤ n) : upto P m <+: upto P n := by
  induction n with
  | zero => simp only [Nat.le_zero] at h; subst h; exact List.prefix_refl _
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact (ih (by omega)).trans (by rw [upto_succ]; exact List.prefix_append _ _)
      · have : m = n + 1 := by omega
        subst this
        exact List.prefix_refl _

theorem rankIn_succ_of_true {P : ℕ → Bool} {a : ℕ} (h : P a) :
    rankIn P (a + 1) = rankIn P a + 1 := by
  simp [rankIn, upto_succ, h]

/-- Ranks are monotone. -/
theorem rankIn_mono {P : ℕ → Bool} {m n : ℕ} (h : m ≤ n) : rankIn P m ≤ rankIn P n :=
  (upto_prefix h).length_le

/-- Ranks separate selected addresses. -/
theorem rankIn_lt_rankIn {P : ℕ → Bool} {b a : ℕ} (hb : P b) (hlt : b < a) :
    rankIn P b < rankIn P a := by
  have h1 : rankIn P (b + 1) ≤ rankIn P a := rankIn_mono (by omega)
  rw [rankIn_succ_of_true hb] at h1
  omega

/-- A selected address sits at its rank. -/
theorem getElem?_upto_rankIn {P : ℕ → Bool} {n a : ℕ} (ha : a < n) (hPa : P a) :
    (upto P n)[rankIn P a]? = some a := by
  obtain ⟨r, hr⟩ := upto_prefix (P := P) (m := a + 1) (n := n) (by omega)
  have hval : (upto P (a + 1))[rankIn P a]? = some a := by
    rw [upto_succ, if_pos hPa, rankIn]
    simp
  have hlen : rankIn P a < (upto P (a + 1)).length := by
    rw [upto_succ, if_pos hPa]
    simp [rankIn]
  rw [← hr, List.getElem?_append_left hlen]
  exact hval

/-- The address at a given position has that position as its rank. -/
theorem rankIn_of_getElem? {P : ℕ → Bool} :
    ∀ {n k a : ℕ}, (upto P n)[k]? = some a → rankIn P a = k := by
  intro n
  induction n with
  | zero => intro k a h; simp [upto] at h
  | succ n ih =>
      intro k a h
      rw [upto_succ] at h
      by_cases hP : P n
      · rw [if_pos hP] at h
        rcases Nat.lt_or_ge k (upto P n).length with hlt | hge
        · exact ih (by rwa [List.getElem?_append_left hlt] at h)
        · rw [List.getElem?_append_right hge] at h
          rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · have hk : k - (upto P n).length = 0 := by omega
            rw [hk] at h
            simp only [List.getElem?_cons_zero, Option.some_inj] at h
            subst h
            rw [rankIn]
            omega
          · have hk : k - (upto P n).length ≠ 0 := by omega
            obtain ⟨j, hj⟩ : ∃ j, k - (upto P n).length = j + 1 :=
              ⟨k - (upto P n).length - 1, by omega⟩
            rw [hj] at h
            simp at h
      · rw [if_neg hP, List.append_nil] at h
        exact ih h
/-! ### Reachability is stable under allocation -/

private theorem reachF_prefix_aux {hp hp' : Heap} (hwf : HeapWF hp) (hpre : hp <+: hp') :
    ∀ p, p < hp.length → ∀ f₁ f₂, p < f₁ → p < f₂ → reachF hp f₁ p = reachF hp' f₂ p := by
  obtain ⟨r, rfl⟩ := hpre
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hplt f₁ f₂ h₁ h₂
    obtain ⟨k₁, rfl⟩ : ∃ k, f₁ = k + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
    have hcell : hp[p]? = some (hp[p]'hplt) := List.getElem?_eq_getElem hplt
    have hcell' : (hp ++ r)[p]? = some (hp[p]'hplt) := by
      rw [List.getElem?_append_left hplt, hcell]
    have hrefs : (hp[p]'hplt).refsLt p := hwf p hplt
    rw [reachF_succ_eq hcell, reachF_succ_eq hcell']
    congr 1
    refine List.flatMap_congr ?_
    intro b hb
    have hblt : b < p := Cell.refs_lt hrefs b hb
    exact ih b hblt (lt_trans hblt hplt) k₁ k₂ (by omega) (by omega)

/-- **Allocating a cell does not change what is reachable from an old address.** -/
theorem reach_append {hp : Heap} (hwf : HeapWF hp) (c : Cell) {p : ℕ} (hp0 : p < hp.length) :
    reach (hp ++ [c]) p = reach hp p := by
  refine (reachF_prefix_aux hwf (List.prefix_append hp [c]) p hp0 hp.length _ hp0 ?_).symm
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ### The live cells of a state, and its space -/

/-- The roots of a state: its environment pointer and its stack. -/
def roots (s : HState) : List ℕ := s.env.toList ++ s.stack

/-- The addresses reachable from the roots, with repetitions. -/
def reachRoots (s : HState) : List ℕ := (roots s).flatMap (reach s.heap)

/-- **A cell is live** when it is reachable from a root. -/
def IsLive (s : HState) (a : ℕ) : Bool := decide (a ∈ reachRoots s)

theorem isLive_iff {s : HState} {a : ℕ} :
    IsLive s a ↔ ∃ p ∈ roots s, a ∈ reach s.heap p := by
  simp [IsLive, reachRoots, List.mem_flatMap]

/-- **The live addresses of a state**, in increasing order. -/
def liveList (s : HState) : List ℕ := upto (IsLive s) s.heap.length

/-- **The space of a state**: the number of cells it keeps alive. -/
def space (s : HState) : ℕ := (liveList s).length

/-- A selection of addresses is **closed** when the references of a selected cell are selected:
this is what makes the unselected cells garbage. -/
def Closed (P : ℕ → Bool) (hp : Heap) : Prop :=
  ∀ a c, a < hp.length → P a → hp[a]? = some c → ∀ b ∈ c.refs, P b

/-- The live cells are closed under references, so the others really are garbage. -/
theorem isLive_closed {s : HState} (hwf : HeapWF s.heap) : Closed (IsLive s) s.heap := by
  intro a c _ hPa hc b hb
  obtain ⟨p, hp, ha⟩ := isLive_iff.1 hPa
  exact isLive_iff.2 ⟨p, hp, reach_refs hwf ha hc hb⟩

/-- A root that points at a cell is live. -/
theorem isLive_root {s : HState} {p : ℕ} (hp : p ∈ roots s) {c : Cell} (hc : s.heap[p]? = some c) :
    IsLive s p :=
  isLive_iff.2 ⟨p, hp, mem_reach_self hc⟩

/-- Everything live is an address of the heap. -/
theorem isLive_lt {s : HState} {a : ℕ} (h : IsLive s a) : a < s.heap.length := by
  obtain ⟨p, _, ha⟩ := isLive_iff.1 h
  exact mem_reach_lt ha

/-- A live address has a rank below the space. -/
theorem rankIn_lt_space {s : HState} {a : ℕ} (h : IsLive s a) :
    rankIn (IsLive s) a < space s :=
  lt_length_of_getElem? (l := liveList s)
    (getElem?_upto_rankIn (P := IsLive s) (n := s.heap.length) (isLive_lt h) h)

/-- An environment pointer is a root. -/
theorem mem_roots_env {s : HState} {i : ℕ} (hi : i ∈ s.env) : i ∈ roots s :=
  List.mem_append_left _ (Option.mem_toList.2 hi)

/-- A stack pointer is a root. -/
theorem mem_roots_stack {s : HState} {i : ℕ} (hi : i ∈ s.stack) : i ∈ roots s :=
  List.mem_append_right _ hi
/-- The space of a state is at most the length of its heap. -/
theorem space_le_heap_length (s : HState) : space s ≤ s.heap.length := by
  have := List.length_filter_le (IsLive s) (List.range s.heap.length)
  simpa [space, liveList, upto] using this
/-- The initial state uses no space. -/
@[simp] theorem space_initState (t : Lambda) : space (initState t) = 0 := by
  simp [space, liveList, upto, initState]

/-! ### Only the live cells are read -/

/-- **The decoded state depends only on the live cells**: two states with the same code and the
same pointers, whose heaps agree on everything reachable from the roots, decode the same. -/
theorem decState_congr_live {tab : Tab} {s s' : HState} (hwf : HeapWF s.heap)
    (hwf' : HeapWF s'.heap) (hcode : s.code = s'.code) (henv : s.env = s'.env)
    (hstack : s.stack = s'.stack)
    (hag : ∀ p ∈ roots s, ∀ a ∈ p :: reach s.heap p, s.heap[a]? = s'.heap[a]?) :
    decState tab s = decState tab s' := by
  have he : decEnvP tab s.heap s.env = decEnvP tab s'.heap s'.env := by
    cases hE : s.env with
    | none => rw [← henv, hE]; simp
    | some j =>
        have hj : j ∈ roots s := mem_roots_env (s := s) hE
        have hres := (dec_congr_aux (tab := tab) hwf hwf' j (hag j hj)).2
        rw [← henv, hE]
        exact hres
  have hs : s.stack.map (decClos tab s.heap) = s'.stack.map (decClos tab s'.heap) := by
    rw [← hstack]
    refine List.map_congr_left ?_
    intro p hp
    exact (dec_congr_aux hwf hwf' p (hag p (mem_roots_stack hp))).1
  simp only [decState, hcode, he, hs]

/-! ### The space of a transition -/

/-- Reachability is transitive. -/
theorem reach_trans {hp : Heap} (hwf : HeapWF hp) {p q a : ℕ} (hq : q ∈ reach hp p)
    (ha : a ∈ reach hp q) : a ∈ reach hp p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
      cases hcp : hp[p]? with
      | none => rw [reach_eq_nil hcp] at hq; simp at hq
      | some cp =>
          have hplt : p < hp.length := lt_length_of_getElem? hcp
          have hcase : (hp[p]'hplt) = cp := by
            have := List.getElem?_eq_getElem hplt
            rw [this] at hcp
            exact Option.some_inj.1 hcp
          have hrefs : cp.refsLt p := by
            have := hwf p hplt
            rwa [hcase] at this
          rw [reach_eq hwf hcp] at hq ⊢
          rcases List.mem_cons.1 hq with rfl | hq
          · rw [reach_eq hwf hcp] at ha
            exact ha
          · obtain ⟨b, hb, hqb⟩ := List.mem_flatMap.1 hq
            have hblt : b < p := Cell.refs_lt hrefs b hb
            exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨b, hb, ih b hblt hqb⟩)

/-- The closure a variable lookup lands on is reachable from the environment. -/
theorem mem_reach_envNth {hp : Heap} (hwf : HeapWF hp) :
    ∀ (n : ℕ) (e : Option ℕ) (q : ℕ), envNth hp e n = some q → ∃ p ∈ e, q ∈ reach hp p := by
  intro n
  induction n with
  | zero =>
      intro e q h
      cases e with
      | none => simp at h
      | some p =>
          cases hcell : hp[p]? with
          | none => rw [envNth, hcell] at h; simp at h
          | some c =>
              cases c with
              | clos code e' => rw [envNth, hcell] at h; simp at h
              | cons x t =>
                  rw [envNth_zero_cons hcell] at h
                  have hq : q = x := (Option.some_inj.1 h).symm
                  subst hq
                  exact ⟨p, rfl, mem_reach_of_refs hwf hcell (by simp)⟩
  | succ n ih =>
      intro e q h
      cases e with
      | none => simp at h
      | some p =>
          cases hcell : hp[p]? with
          | none => rw [envNth, hcell] at h; simp at h
          | some c =>
              cases c with
              | clos code e' => rw [envNth, hcell] at h; simp at h
              | cons x t =>
                  rw [envNth_succ_cons hcell] at h
                  obtain ⟨j, hj, hqj⟩ := ih t q h
                  refine ⟨p, rfl, ?_⟩
                  have hjref : j ∈ (Cell.cons x t).refs :=
                    List.mem_cons_of_mem _ (Option.mem_toList.2 hj)
                  exact reach_trans hwf (mem_reach_of_refs hwf hcell hjref) hqj

/-- Counting the live cells through an inclusion. -/
theorem space_le_of_live_subset {s s' : HState} {extra : List ℕ}
    (h : ∀ a, IsLive s' a → IsLive s a ∨ a ∈ extra) :
    space s' ≤ space s + extra.length := by
  have hnd : (liveList s').Nodup := List.nodup_range.filter _
  have hsub : liveList s' ⊆ liveList s ++ extra := by
    intro a ha
    rw [liveList, mem_upto] at ha
    rcases h a ha.2 with hl | hl
    · exact List.mem_append_left _ (by rw [liveList, mem_upto]; exact ⟨isLive_lt hl, hl⟩)
    · exact List.mem_append_right _ hl
  have hlen := hnd.length_le_of_subset hsub
  simpa [space] using hlen

/-- Allocating one cell whose references are roots costs at most one cell of space. -/
theorem space_alloc_le {s s' : HState} (hwf : HeapWF s.heap) {c : Cell}
    (hc : c.refsLt s.heap.length) (hheap : s'.heap = s.heap ++ [c])
    (hrlt : ∀ p ∈ roots s, p < s.heap.length)
    (hroots : ∀ p ∈ roots s', p = s.heap.length ∨ p ∈ roots s)
    (hcrefs : ∀ b ∈ c.refs, b ∈ roots s) : space s' ≤ space s + 1 := by
  have hwf' : HeapWF (s.heap ++ [c]) := heapWF_append hwf hc
  have hnew : (s.heap ++ [c])[s.heap.length]? = some c := by simp
  refine space_le_of_live_subset (extra := [s.heap.length]) ?_
  intro a ha
  obtain ⟨p, hp, hap⟩ := isLive_iff.1 ha
  rw [hheap] at hap
  rcases hroots p hp with rfl | hp'
  · rw [reach_eq hwf' hnew] at hap
    rcases List.mem_cons.1 hap with rfl | hap
    · exact Or.inr (by simp)
    · obtain ⟨b, hb, hab⟩ := List.mem_flatMap.1 hap
      have hbr : b ∈ roots s := hcrefs b hb
      rw [reach_append hwf c (hrlt b hbr)] at hab
      exact Or.inl (isLive_iff.2 ⟨b, hbr, hab⟩)
  · rw [reach_append hwf c (hrlt p hp')] at hap
    exact Or.inl (isLive_iff.2 ⟨p, hp', hap⟩)

/-- **A transition costs at most one cell of space.** -/
theorem space_hstep_le {tab : Tab} {s : HState} (hv : Valid tab s) {l : Label} {s' : HState}
    (h : hstep tab s = some (l, s')) : space s' ≤ space s + 1 := by
  have hrlt : ∀ p ∈ roots s, p < s.heap.length := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hv.env_lt p (Option.mem_toList.1 hp)
    · exact hv.stack_lt p hp
  obtain ⟨nd, hnd⟩ : ∃ nd, tab[s.code]? = some nd :=
    ⟨_, List.getElem?_eq_getElem hv.code_lt⟩
  cases nd with
  | var n =>
      cases hw : envNth s.heap s.env n with
      | none => rw [hstep_var_none_eq hnd hw] at h; exact absurd h (by simp)
      | some q =>
          obtain ⟨c, e, hcell⟩ :=
            isClosPtr_envNth hv.heapWF hv.heapTyped hv.env_lt hv.env_ty hw
          rw [hstep_var_eq hnd hw hcell] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨-, hs⟩ := h
          subst hs
          -- the heap does not change, and the new environment is reachable from the old one
          have hsub : ∀ a, IsLive (⟨c, e, s.stack, s.heap⟩ : HState) a →
              IsLive s a ∨ a ∈ ([] : List ℕ) := by
            intro a ha
            obtain ⟨p, hp, hap⟩ := isLive_iff.1 ha
            refine Or.inl (isLive_iff.2 ?_)
            rcases List.mem_append.1 hp with hp | hp
            · -- `p` is the environment of the closure the lookup landed on
              have hpe : p ∈ e := Option.mem_toList.1 hp
              obtain ⟨r, hr, hqr⟩ := mem_reach_envNth hv.heapWF n s.env q hw
              have hpq : p ∈ reach s.heap q :=
                mem_reach_of_refs hv.heapWF hcell (by simpa using hpe)
              refine ⟨r, mem_roots_env (s := s) hr, ?_⟩
              exact reach_trans hv.heapWF hqr (reach_trans hv.heapWF hpq hap)
            · exact ⟨p, mem_roots_stack hp, hap⟩
          have hle := space_le_of_live_subset (s := s) hsub
          simp only [List.length_nil, Nat.add_zero] at hle
          omega
  | app f a =>
      rw [hstep_app_eq hnd] at h
      simp only [Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨-, hs⟩ := h
      subst hs
      refine space_alloc_le hv.heapWF (c := Cell.clos a s.env) (fun j hj => hv.env_lt j hj)
        rfl hrlt ?_ ?_
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact Or.inr (List.mem_append_left _ hp)
        · rcases List.mem_cons.1 hp with rfl | hp
          · exact Or.inl rfl
          · exact Or.inr (mem_roots_stack hp)
      · intro b hb
        exact mem_roots_env (s := s) (Option.mem_toList.1 (by simpa using hb))
  | lam b =>
      cases hst : s.stack with
      | nil => rw [hstep_lam_nil_eq hnd hst] at h; exact absurd h (by simp)
      | cons p π =>
          rw [hstep_lam_cons_eq hnd hst] at h
          simp only [Option.some_inj, Prod.mk.injEq] at h
          obtain ⟨-, hs⟩ := h
          subst hs
          have hplt : p < s.heap.length := hv.stack_lt p (by rw [hst]; simp)
          refine space_alloc_le hv.heapWF (c := Cell.cons p s.env)
            ⟨hplt, fun j hj => hv.env_lt j hj⟩ rfl hrlt ?_ ?_
          · intro r hr
            rcases List.mem_append.1 hr with hr | hr
            · left
              simp at hr
              omega
            · exact Or.inr (mem_roots_stack (by rw [hst]; exact List.mem_cons_of_mem p hr))
          · intro x hx
            rcases (by simpa using hx : x = p ∨ s.env = some x) with rfl | hx
            · exact mem_roots_stack (by rw [hst]; simp)
            · exact mem_roots_env (s := s) hx
end Impl

end Krivine
