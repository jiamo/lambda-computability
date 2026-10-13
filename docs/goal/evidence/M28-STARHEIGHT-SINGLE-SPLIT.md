# M28-STARHEIGHT-SINGLE-SPLIT — generalized star height two from one split

## Terminal statements (`Start/StarHeightSingleSplit.lean`)

```lean
def SingleSplit {Alphabet : Type u} {M : Type} [Monoid M] [Fintype M]
    (T : FreeMonoid Alphabet →* M) : Prop :=
  ∃ (E : Language Alphabet) (S : Type) (_ : Fintype S) (G : List Alphabet → S → S)
    (P Q : S → Language Alphabet),
    PrefixCode E ∧ HasHeightAtMost E 1 ∧
    (∀ d, HasHeightAtMost {w | w ∈ remainder E ∧ T (FreeMonoid.ofList w) = d} 1) ∧
    SplitSound E G P Q ∧ SplitAvailable E 0 G P Q ∧
    (∀ x, HasHeightAtMost (P x) 1) ∧ (∀ y, HasHeightAtMost (Q y) 1) ∧
    ∀ d, ∃ R : Set (S × S × S × S),
      {w | w ∈ E∗ ∧ T (FreeMonoid.ofList w) = d} =
        ⨆ r ∈ R, graph E G r.1 r.2.1 ⊓ graph E G r.2.2.1 r.2.2.2

theorem height_two_of_singleSplit {Alphabet : Type u} [Finite Alphabet] {M : Type}
    [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M) (hT : SingleSplit T)
    (F : Set M) : HasHeightAtMost {w | T (FreeMonoid.ofList w) ∈ F} 2

theorem main_two_of_singleSplit {Alphabet : Type u} [Finite Alphabet]
    (h : ∀ (M : Type) [Monoid M] [Fintype M] (T : FreeMonoid Alphabet →* M),
      SingleSplit T)
    (L : Language Alphabet) (hL : L.IsRegular) : HasHeightAtMost L 2
```

The definition is the one in the instruction, verbatim; its form was not changed.

Auxiliary result in the same module: `single_split_graph_height` — with `D = E`, `D' = 0`,
`H = 0` (`empty_skip_height`), `split_height` gives `max 2 (1 + 0) = 2` for every graph
language `graph E G x y`.

## Proof

1. Every `graph E G x y` has height ≤ 2 (`single_split_graph_height`).
2. Each fiber `{w ∈ E∗ | T w = d}` equals `⨆ r ∈ R, graph … ⊓ graph …`; `R` is a subset of the
   finite type `S × S × S × S`, so it is finite and `HasHeightAtMost.finset_iSup` with
   `HasHeightAtMost.inter` gives height ≤ 2.
3. `factor_remainder` splits every word as `es.flatten ++ r` with `es` episodes and `r` in
   `remainder E`; the recognized language is `⨆_{d f, d f ∈ F} A_d · B_f`, with `A_d` the fibers
   on `E∗` (height ≤ 2) and `B_f` the remainder fibers (height ≤ 1). This is the assembly of
   `FiniteRecognition.recognized_height_three`, with 2 in place of 3.
4. `main_two_of_singleSplit`: the empty alphabet is handled as in `GeneralizedStarHeight.main`
   (finite language); otherwise `FiniteRecognition.of_regular` gives `T`, `F`.

## Axioms

```
'GeneralizedStarHeight.height_two_of_singleSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'GeneralizedStarHeight.main_two_of_singleSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Which upstream lemma fails to give `SingleSplit`, and on which episodes

The upstream construction (`SourceSchedule.episode_linear_graphs`, via
`SourceSchedule.Early.outer_graph_height` in `Start/StarHeightEpisodeHeight.lean`) has every
ingredient of `SingleSplit` except one:

* `E = L.endRule.complete L.lag` is a prefix code (`prefix_code`) of height ≤ 1
  (`complete_height`), with remainder fibers of height ≤ 1 (`remainder_fiber_height`);
* the outer tests `OuterStream.prefixLanguage` / `OuterStream.suffixLanguage` have height ≤ 1
  (`prefix_height`, `suffix_height`) and are `SplitSound` on all of `E`
  (`OuterStream.word_sound`);
* the fibers have the two-graph shape (`AffineRecovery.recovery`, used through
  `recovery_height`).

The lemma that fails is the availability lemma **`OuterStream.word_available`**
(`Start/StarHeightSplitLanguages.lean`), fed by `SourceSchedule.Early.outer_available`
(`Start/StarHeightUsableCopies.lean`). It proves only

```lean
SplitAvailable (A.endRule.complete lag) (A.failedDomain lag) (wordUpdate A clock T ρ β lag)
  (prefixLanguage A H clock T ρ β lag) (suffixLanguage A H clock T ρ reference)
```

i.e. availability with skipped class `A.failedDomain lag`, not `SplitAvailable E 0`. Its
hypothesis `havail` (and `outer_available`'s hypothesis `hn`) requires
`¬ A.Failed f lag (A.anchor f (b - A.endRule.tail) lag)`.

The episodes on which it fails are exactly the episodes of
`A.failedDomain lag = A.endRule.complete lag ⊓ A.failedLanguage lag`
(`Start/StarHeightWordStreams.lean`): complete episodes `e` whose stream `f = stream e`
satisfies `A.Failed f lag (A.anchor f (e.length - A.endRule.tail) lag)`, where
(`Start/StarHeightExceptionalOrigins.lean`)

* `Failed f t Q := A.Z f t ∨ A.Star f t Q`;
* `Z f t`: the end-marker search is unstable (`EndSearch.Unstable … A.endRule.d …` or
  `EndSearch.Unstable … (3 * A.endRule.d) …`) — the clock/end condition fails;
* `Star f t Q`: the residue `A.φ (Q - t)` lies in the exceptional set `A.W`, or some inner marker
  search fails (`MarkerSearch.InnerFailure`) — the marker condition fails.

On these episodes the upstream proof uses a second split (`inner_graph_height`, with
`InnerStream` tests on `failedDomain`, `0` skipped), and the resulting height-2 graphs serve as
the skip graphs of the outer split, giving `max 2 (1 + 2) = 3`. With a single split, availability
would be needed on `failedDomain` as well.

## Gates

`lake build --wfail`, `scripts/check_manifest.py`, `scripts/check_sorry.py`,
`scripts/check_closure.py` and `scripts/goal_state.py validate` were run on the delivered tree.
