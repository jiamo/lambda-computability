# M25-CBNEED-MACHINE and M25-CBNEED-COST — call-by-need

Status: M25-CBNEED-MACHINE is **DONE_STRONG** (B1–B3).  M25-CBNEED-COST is **DONE_WEAK**: its
second clause (never more β transitions, and an exponential family) is proved (B4); its first
clause, a time cost model in the form of M11-KRIVINE-INVARIANCE (B5), is open, gap row
M25-CBNEED-TIME.

## Modules

| module | content |
| --- | --- |
| `Start/LazyMachine.lean` | the lazy machine, determinism, sharing (B1, B3) |
| `Start/LazyKrivine.lean` | decoding into Krivine states, the simulation, agreement, the β bound (B2, B4 first half) |
| `Start/LazyCost.lean` | the exponential family (B4 second half) |

## B1. The machine (Sestoft style)

* Heap `List Cell`; a cell is `thunk c` (an unevaluated closure), `hole c` (a thunk under
  evaluation, Sestoft's black hole) or `value c v` (evaluated; `c` is the closure it was allocated
  with, `v` its value).  Environments are lists of heap addresses (`LClos = code × List ℕ`).
* Stack frames: `arg a` (an argument, by address) and `upd a` (an update marker).
* Transitions `LTrans l s s'` (labels `app`, `beta`, `force a`, `fetch`, `update`):
  * `app`: `⟨t u, e, S, H⟩ → ⟨t, e, arg |H| :: S, H ++ [thunk ⟨u, e⟩]⟩` (allocates a thunk);
  * `beta`: `⟨λt, e, arg a :: S, H⟩ → ⟨t, a :: e, S, H⟩` (the only β transition);
  * `force`: a variable bound to a thunk: the cell becomes a hole, `upd a` is pushed, the thunk's
    closure is evaluated;
  * `fetch`: a variable bound to a value returns the value (no re-evaluation);
  * `update`: a value meeting `upd a` overwrites the cell `a` with the value.

```lean
theorem LTrans.deterministic {l l' : LLabel} {s s₁ s₂ : LState} (h₁ : LTrans l s s₁)
    (h₂ : LTrans l' s s₂) : l = l' ∧ s₁ = s₂
```

## B3. Sharing

```lean
theorem LRun.value_persist {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s')
    {a : ℕ} {c v : LClos} (ha : s.heap[a]? = some (.value c v)) :
    s'.heap[a]? = some (.value c v)
theorem LRun.value_not_thunk {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s')
    {a : ℕ} {c v : LClos} (ha : s.heap[a]? = some (.value c v)) (c' : LClos) :
    s'.heap[a]? ≠ some (.thunk c')
theorem LRun.forced_nodup {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s') :
    fs.Nodup
```

`LRun n b fs s s'` is a run of `n` transitions, `b` of them β, which forces the addresses `fs` (in
order); `forced_nodup` says each address is forced from a thunk at most once.

## B2. Agreement with call-by-name

Decoding `dS : LState → Krivine.State` reads every address as the closure the cell was
*allocated* with (`decA`, well-founded on the address: a cell only refers to older cells), and
drops update markers.  The invariant `Inv` records well-formedness, that each value is reached by
the Krivine machine from the cell's original closure, and that each update marker marks a black
hole from which the Krivine machine reaches the current state (restricted to the frames above the
marker).  Under the decoding `app`, `beta`, `force` are single Krivine transitions, `fetch` is a
`var` transition followed by the re-evaluation recorded in `Inv`, and `update` is the empty run.

```lean
theorem sim_run {n b : ℕ} {fs : List ℕ} {s s' : LState} (h : LRun n b fs s s') (hI : Inv s) :
    Inv s' ∧ ∃ k b', Run k b' (dS s) (dS s') ∧ b ≤ b'
def LHalts (t : Lambda) : Prop :=
  ∃ n b fs s, LRun n b fs (LState.init t) s ∧ LFinal s ∧ ¬ HoleStuck s
def KHalts (t : Lambda) : Prop := ∃ n b s, Run n b (State.init t) s ∧ IsFinal s
theorem halts_iff (t : Lambda) : LHalts t ↔ KHalts t
theorem no_blackhole {t : Lambda} (hK : KHalts t) {n b : ℕ} {fs : List ℕ} {s : LState}
    (hrun : LRun n b fs (LState.init t) s) : ¬ HoleStuck s
theorem result_agree {t : Lambda} {n b : ℕ} {fs : List ℕ} {s : LState}
    (hrun : LRun n b fs (LState.init t) s) (hfin : LFinal s) {m c : ℕ} {f : State}
    (hf : Run m c (State.init t) f) (hff : IsFinal f) :
    dS s = f ∧ ∃ b', Lambda.reducesIn b' t (dS s).decode ∧ Lambda.IsWhnf (dS s).decode
```

Halting of the lazy machine means reaching a final state that is not stuck on a black hole
(`HoleStuck`); `no_blackhole` shows black holes never occur when the Krivine machine halts (a
black hole would make the Krivine machine loop: `loop_no_final`).  The converse direction of
`halts_iff` is a progress argument with measure `2·(remaining Krivine steps) + #update markers`.
`result_agree`: the decoded final lazy state is the final Krivine state, so the two machines
compute the same weak head normal form (`eval_sound`).

## B4. Cost

```lean
theorem beta_le {t : Lambda} {n b : ℕ} {fs : List ℕ} {s : LState}
    (hrun : LRun n b fs (LState.init t) s) {m c : ℕ} {f : State}
    (hf : Run m c (State.init t) f) (hff : IsFinal f) : b ≤ c
theorem beta_le_of_whnIn {t : Lambda} {k : ℕ} (ht : Lambda.WHNIn k t) :
    LHalts t ∧ ∃ m c f, Run m c (State.init t) f ∧ IsFinal f ∧ c ≤ k ∧
      ∀ n b fs s, LRun n b fs (LState.init t) s → b ≤ c
```

The family (`Start/LazyCost.lean`): `W 0 = x`, `W (m+1) = (λ. W m) (x x)`,
`tfam n = (λ. W n) I`, i.e. `(λx₀. (λx₁. ⋯ (λxₙ. xₙ) (xₙ₋₁ xₙ₋₁) ⋯) (x₀ x₀)) I`.  Each `x_{k+1}`
uses `x_k` twice.  Under call-by-name evaluating `x_{k+1}` costs `2·C(k) + 1` β transitions
(`C(0) = 0`), so `C(n) = 2ⁿ − 1`, plus `n + 1` for binding; the lazy machine evaluates each `x_k`
once (`L(k+1) = L(k) + 1`).

```lean
theorem krivine_tfam (n : ℕ) :
    ∃ N f, Run N (2 ^ n + n) (State.init (tfam n)) f ∧ IsFinal f
theorem lazy_tfam (n : ℕ) :
    ∃ N fs s, LRun N (2 * n + 1) fs (LState.init (tfam n)) s ∧ LFinal s
theorem cbneed_exponential_gap (n : ℕ) :
    (∃ N fs s, LRun N (2 * n + 1) fs (LState.init (tfam n)) s ∧ LFinal s ∧ ¬ HoleStuck s) ∧
      (∃ N f, Run N (2 ^ n + n) (State.init (tfam n)) f ∧ IsFinal f) ∧
      ∀ N b f, Run N b (State.init (tfam n)) f → IsFinal f → b = 2 ^ n + n
```

## B5. Open: the time cost model (gap row M25-CBNEED-TIME)

First missing result: the analogue of M11-KRIVINE-INVARIANCE for the lazy machine — the number of
lazy transitions is polynomial in the number of β transitions and the size of the term, and one
transition is realized by a tape program (`Complexity.Space.Realizes`, `Start/SpaceCompile.lean`)
in time polynomial in the size of the state.  The first lemma is the transition count bound
`n ≤ p(b, |t|)` for `LRun n b fs (LState.init t) s`, then the heap-size bound.

## Axioms

`M25-CBNEED-MACHINE-axioms.txt`, `M25-CBNEED-COST-axioms.txt`: at most
`[propext, Classical.choice, Quot.sound]`.
