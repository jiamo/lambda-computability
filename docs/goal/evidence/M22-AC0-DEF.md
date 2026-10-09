# M22-AC0-DEF — AC0: constant-depth unbounded fan-in circuits of polynomial size

**Status:** DONE_STRONG

## Terminal statements (`Start/AC0.lean`)

```lean
inductive Complexity.ACCirc | lit (i : ℕ) (b : Bool) | const (b : Bool) | not (c : ACCirc)
  | and (cs : List ACCirc) | or (cs : List ACCirc)
def ACCirc.eval (x : Word) : ACCirc → Bool
def ACCirc.depth : ACCirc → ℕ        -- AND/OR layers; NOT is free
def ACCirc.size : ACCirc → ℕ         -- number of nodes
def ACCirc.NoNot : ACCirc → Prop     -- negation normal form
def ACCirc.nnf : Bool → ACCirc → ACCirc
def Complexity.InAC0 (L : Language) : Prop :=
  ∃ d p, PolyBound p ∧ ∀ n, ∃ C, C.depth ≤ d ∧ C.size ≤ p n ∧
    ∀ x, x.length = n → (L x ↔ C.eval x = true)

theorem ACCirc.eval_nnf x c p : (nnf p c).eval x = (c.eval x == p)
theorem ACCirc.depth_nnf c p : (nnf p c).depth = c.depth
theorem ACCirc.size_nnf c p : (nnf p c).size ≤ c.size
theorem ACCirc.noNot_nnf c p : NoNot (nnf p c)
theorem ACCirc.eval_and_join x dss : (and dss.flatten).eval x = (and (dss.map and)).eval x
theorem ACCirc.depth_and_join_le (h : dss ≠ []) :
    (and dss.flatten).depth + 1 ≤ (and (dss.map and)).depth
theorem ACCirc.size_and_join_le dss : (and dss.flatten).size ≤ (and (dss.map and)).size
-- and the same three for OR
theorem InAC0.exists_noNot, InAC0.compl, InAC0.inter, InAC0.union
theorem inAC0_someOne : InAC0 (fun x => true ∈ x)
theorem inAC0_allOne : InAC0 (fun x => ∀ b ∈ x, b = true)
```

## Design notes

* Circuits are trees.  At constant depth `d` a shared circuit of size `s` unfolds into a tree of
  size at most `s ^ d`, so the class `AC⁰` is the same as with shared circuits; trees keep the
  switching-lemma rows simple (restriction is a structural map).
* A gate of the input list form `and cs`/`or cs` has unbounded fan-in.  `and []` is the constant
  `true`, `or []` the constant `false`.
* Depth counts the `AND`/`OR` layers only.  This makes "pushing negations to the inputs" exactly
  depth-preserving (`depth_nnf`) and size-non-increasing (`size_nnf`).
* Merging layers: an `AND` of `AND`s (a nonempty list of them) equals one `AND` of the
  concatenated inputs and is one layer shallower; likewise for `OR`.  This is the step used after
  the switching lemma turns a bottom layer of CNFs into DNFs.

## Gates

```
lake build
python3 scripts/check_sorry.py
python3 scripts/check_closure.py
python3 scripts/goal_state.py validate
```
