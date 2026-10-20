/-
**Size-change termination for call graphs** — task `M23-SIZE-CHANGE` (round 8, part F; an
extension of the row).  Round 7 proved the closure criterion for one parameter set shared by all
graphs (`Start/SizeChange.lean`).  Here the per-function form used by termination checkers:

* `SizeChange.CallGraph m n` — a program with functions `Fin m`, each with an arity `≤ n`
  (its parameters are the `x : Fin n` with `x < arity f`), and a finite set of calls
  `(f, g, G)` labelled by size-change graphs from the parameters of the caller `f` to those of
  the callee `g` (`CallGraph.WF`: arcs only between parameters);
* `SizeChange.CallGraph.SCT` — multipaths follow call sequences: every infinite call sequence
  `f₀ → f₁ → …` with graphs `G₀, G₁, …` has an infinite thread with infinitely many strict
  descents;
* `SizeChange.CallGraph.InCl 𝒞 f g G` — the composition closure along composable call
  sequences from `f` to `g`; `SizeChange.CallGraph.Criterion` — **the closure criterion at each
  function**: every idempotent graph `G = G;G` of the closure from a function `f` to itself has a
  strict self-arc;
* `SizeChange.thread_of_idempotent_blocks` — the thread construction of round 7, factored out:
  a multipath cut into blocks all composing to one graph with a strict self-arc has an infinite
  descending thread;
* `SizeChange.CallGraph.sct_of_criterion` — **the per-function closure criterion implies
  size-change termination**, by `ramsey_pairs` colouring a pair of positions by the function at
  the first position and the composite graph of the block.

Parameters of all functions live in one `Fin n` (`n` bounds the arities); well-formedness
(`CallGraph.WF`) keeps every arc between parameters of the right functions, so the threads only
visit parameters.  The soundness theorem does not need well-formedness.
-/

import Start.SizeChange

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace SizeChange

variable {n : ℕ}

/-- **The thread construction**: if a multipath is cut by a strictly increasing `f` into blocks
which all compose to `G`, and `G` has a strict self-arc at `x`, there is an infinite thread
with infinitely many strict descents. -/
theorem thread_of_idempotent_blocks (g : ℕ → SCG n) (f : ℕ → ℕ) (hf : StrictMono f) (G : SCG n)
    (hblock : ∀ k, compR g (f k) (f (k + 1) - f k - 1) = G) (x : Fin n)
    (hx : (x, x, true) ∈ G) :
    ∃ (i : ℕ) (t : ℕ → Fin n) (l : ℕ → Bool),
      (∀ p, i ≤ p → (t p, t (p + 1), l p) ∈ g p) ∧ ∀ N, ∃ p, N ≤ p ∧ i ≤ p ∧ l p = true := by
  classical
  have hfk : ∀ k, f k < f (k + 1) := fun k => hf (Nat.lt_succ_self k)
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



/-! ### Call graphs -/

/-- A program's call graph with size-change graphs: functions `Fin m`, arities bounded by `n`,
and calls `(caller, callee, graph)`. -/
structure CallGraph (m n : ℕ) where
  /-- The arity of each function; its parameters are the `x : Fin n` with `x < arity f`. -/
  arity : Fin m → ℕ
  /-- The calls, each labelled with a size-change graph. -/
  calls : Finset (Fin m × Fin m × SCG n)

namespace CallGraph

variable {m : ℕ}

/-- Well-formedness: every arc of a call `f → g` goes from a parameter of `f` to a parameter
of `g`. -/
def WF (𝒞 : CallGraph m n) : Prop :=
  ∀ f g G, (f, g, G) ∈ 𝒞.calls → ∀ x y b, (x, y, b) ∈ G → x.val < 𝒞.arity f ∧ y.val < 𝒞.arity g

/-- **Size-change termination along call sequences**: every infinite call sequence
`fn 0 → fn 1 → …` with graphs `g 0, g 1, …` has, from some point on, an infinite thread with
infinitely many strict descents. -/
def SCT (𝒞 : CallGraph m n) : Prop :=
  ∀ (fn : ℕ → Fin m) (g : ℕ → SCG n), (∀ k, (fn k, fn (k + 1), g k) ∈ 𝒞.calls) →
    ∃ (i : ℕ) (t : ℕ → Fin n) (l : ℕ → Bool),
      (∀ p, i ≤ p → (t p, t (p + 1), l p) ∈ g p) ∧ ∀ N, ∃ p, N ≤ p ∧ i ≤ p ∧ l p = true

/-- **The composition closure along composable call sequences**: `InCl 𝒞 f g G` when `G` is the
composite of the graphs of a non-empty call sequence from `f` to `g`. -/
inductive InCl (𝒞 : CallGraph m n) : Fin m → Fin m → SCG n → Prop
  | base {f g G} : (f, g, G) ∈ 𝒞.calls → InCl 𝒞 f g G
  | comp {f g h G H} : InCl 𝒞 f g G → InCl 𝒞 g h H → InCl 𝒞 f h (G.comp H)

/-- **The closure criterion at each function**: every idempotent graph of the closure from a
function to itself has a strict self-arc. -/
def Criterion (𝒞 : CallGraph m n) : Prop :=
  ∀ f G, InCl 𝒞 f f G → G.comp G = G → ∃ x, (x, x, true) ∈ G

theorem compR_inCl {𝒞 : CallGraph m n} {fn : ℕ → Fin m} {g : ℕ → SCG n}
    (hg : ∀ k, (fn k, fn (k + 1), g k) ∈ 𝒞.calls) (i : ℕ) :
    ∀ k, InCl 𝒞 (fn i) (fn (i + k + 1)) (compR g i k)
  | 0 => .base (hg i)
  | k + 1 => .comp (compR_inCl hg i k) (by
      have := hg (i + k + 1)
      rw [show i + (k + 1) + 1 = i + k + 1 + 1 by omega]
      exact .base this)

/-- **The per-function closure criterion implies size-change termination along call
sequences.** -/
theorem sct_of_criterion {𝒞 : CallGraph m n} (hc : Criterion 𝒞) : SCT 𝒞 := by
  classical
  intro fn g hg
  obtain ⟨f, hf, ⟨F, G⟩, hG⟩ := ramsey_pairs (fun i j => (fn i, compR g i (j - i - 1)))
  have hfk : ∀ k, f k < f (k + 1) := fun k => hf (Nat.lt_succ_self k)
  have hblock : ∀ k, compR g (f k) (f (k + 1) - f k - 1) = G :=
    fun k => (Prod.mk.inj (hG k (k + 1) (Nat.lt_succ_self k))).2
  have hfn : ∀ k, fn (f k) = F := fun k => (Prod.mk.inj (hG k (k + 1) (Nat.lt_succ_self k))).1
  -- `G` lies in the closure from `F` to `F`
  have hGcl : InCl 𝒞 F F G := by
    have h := compR_inCl hg (f 0) (f 1 - f 0 - 1)
    have he : f 0 + (f 1 - f 0 - 1) + 1 = f 1 := by have : f 0 < f 1 := hfk 0; omega
    rw [he, hfn 0, hfn 1, hblock 0] at h
    exact h
  -- `G` is idempotent
  have hidem : G.comp G = G := by
    have h02 := (Prod.mk.inj (hG 0 2 (by norm_num))).2
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
  obtain ⟨x, hx⟩ := hc F G hGcl hidem
  exact thread_of_idempotent_blocks g f hf G hblock x hx

end CallGraph

end SizeChange
