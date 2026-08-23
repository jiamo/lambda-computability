# M9-SCOTT-DINF

**Status:** DONE_STRONG

Modules `Start/ScottTower.lean`, `Start/ScottDinf.lean`, `Start/ScottPsi.lean`,
`Start/ScottDinfIso.lean`, `Start/ScottDinfModel.lean` and `Start/ScottDinfOmega.lean`, all
imported by `Start.lean`.  They build without `sorry` and without linter warnings;
`#print axioms` on the headline theorems reports only `propext`, `Classical.choice`,
`Quot.sound`.

The files carry out Scott's original inverse-limit construction of a model of the untyped
lambda calculus, and then use it to interpret terms.

## The tower (first exit criterion) — `Start/ScottTower.lean`

A bare recursive definition of the *type* family `D 0 = Bool`, `D (n+1) = [D n →𝒄 D n]` is
impossible in Lean, because the function-space type already needs the order instance of the
previous level.  The file therefore introduces a bundled structure `Dom` (a carrier with an
`OmegaCompletePartialOrder` instance, a least element, and the proof that it is least), the
function-space operation `Dom.fn`, the base `baseDom = Bool`, and defines `tower : ℕ → Dom` by
recursion; `D n := (tower n).carrier`.

`toFn`/`ofFn` are the (definitional) coercions `D (n+1) ≃ (D n →𝒄 D n)`, with `toFn_ext`,
`toFn_le_iff` and `toFn_ωSup` giving extensionality, the pointwise order and pointwise suprema.

The embedding–projection pairs are defined by *simultaneous* recursion in
`ep : ∀ n, (D n →𝒄 D (n+1)) × (D (n+1) →𝒄 D n)`, using the auxiliary continuity lemma
`sandwich_continuous`.  The two ep-pair laws are `prj_emb : prj n (emb n x) = x` and
`emb_prj_le : emb n (prj n f) ≤ f`, together with `prj_botD`.

## The inverse limit (second exit criterion) — `Start/ScottDinf.lean`

`Coherent x` says `prj n (x (n+1)) = x n`; `Dinf` is the subtype of coherent sequences, an
ω-cpo by `OmegaCompletePartialOrder.subtype` (suprema are computed componentwise,
`Dinf.ωSup_app`), with least element `botDinf`.

`theta n x` is the `n`-th finite approximation of `x` (it agrees with `x` up to level `n` and is
embedded upwards above it); `theta_le`, `theta_mono` and finally

* **`ωSup_thetaChain : ωSup (thetaChain x) = x`** — every element of `D∞` is the supremum of its
  finite approximations.

This is the key lemma of the whole construction.

## The embeddings of the levels — `Start/ScottPsi.lean`

`psi n : D n →𝒄 D∞` sends `z` to the least element of the limit whose `n`-th component is `z`
(iterated projections below level `n`, iterated embeddings above it).  It is built from
`downSeq`/`psiSeq` by recursion on the level, with the diagonal case handled by a transport
`castD` along an equality of levels.  Main properties: `psiFun_app_self : (psi n z).app n = z`,
`psi_app_le : psi n (x.app n) ≤ x`, `psi_theta : psi n (x.app n) = theta n x`, and continuity of
each component (`ωScottContinuous_psiSeq`), which is what bundles `psi n` as a continuous map.

## The isomorphism (third exit criterion) — `Start/ScottDinfIso.lean`

Application is the supremum of its finite approximations: `mulLevel x n y = toFn (x.app (n+1))
(y.app n)`, `appChain x n = psi n ∘ mulLevel x n`, and `Phi x = ωSup (appChain x)`.  The chain is
monotone by the adjunction `psi_le_iff : psi n z ≤ w ↔ z ≤ w.app n` together with
`mulLevel_le_prj`.  The computation rule

* `Phi_app_psi : (Phi x (psi n z)).app n = toFn (x.app (n+1)) z`

is proved by showing (`appChain_app_of_le`, by induction from `n` upwards) that all terms of the
chain of index `≥ n` have the same `n`-th component.

The inverse `Psi f` has components `ofFn (fun z => (f (psi n z)).app n)`; coherence uses
`psi_emb : psi (n+1) (emb n z) = psi n z`.  Then `Psi_Phi : Psi (Phi x) = x` follows from the
computation rule, and `Phi_Psi : Phi (Psi f) = f` from `ωSup_thetaChain`, continuity of `f`, and a
diagonal argument on the double chain `theta m (f (theta n y))`.

* **`dinfOrderIso : Dinf ≃o (Dinf →𝒄 Dinf)`** — Scott's theorem.

`Phi_continuous` and `Psi_continuous` show both directions are Scott continuous (so this is an
isomorphism of ω-cpos, not merely of posets), and `dinf_nontrivial` exhibits two distinct
elements, so the model is not degenerate.

## The lambda model (fourth exit criterion) — `Start/ScottDinfModel.lean`

Environments are `DEnv := ℕ → D∞` with the pointwise order.  Abstraction is *totalised* as

```
dlamAny g = if h : ωScottContinuous g then Psi (ofFun g h) else botDinf
```

so that the interpretation

```
ddenot (var i) ρ = ρ i
ddenot (app s t) ρ = Phi (ddenot s ρ) (ddenot t ρ)
ddenot (lam s) ρ = dlamAny (fun X => ddenot s (dcons X ρ))
```

can be defined by plain structural recursion, the continuity being proved afterwards:
`ddenot_cont` shows `ρ ↦ ⟦t⟧ρ` is Scott continuous, by induction on `t` (the lambda case uses
`Psi_continuous` and the pointwise criterion `ωScottContinuous_hom` for maps into a continuous
function space).  Consequently `dlamAny` is `Psi` on every function that actually arises, and

* `ddenot_lift`, `ddenot_subst`, `ddenot_beta` — the lifting, substitution and beta rules;
* `ddenot_step`, `ddenot_reduces`, `ddenot_conv` — **soundness** for beta;
* `ddenot_eta : ⟦λ. (t↑) 0⟧ρ = ⟦t⟧ρ` — **eta**, valid because `Φ` is an isomorphism and not just
  a retraction.  This is what distinguishes `D∞` from the graph model of `M9-GRAPH-MODEL`.

## The denotation of `Ω` and consistency of `λη` — `Start/ScottDinfOmega.lean`

Writing `d = ⟦λx. x x⟧`, the levels of `d` are computed explicitly
(`deltaD_app_succ : toFn (d.app (n+1)) z = toFn (emb n z) z`), and an induction on the level
(`deltaD_selfapp_bot`) shows `toFn (d.app (n+1)) (d.app n) = ⊥` for every `n`.  Since
`Φ d d` is by definition the supremum of exactly those values embedded into the limit,

* **`ddenot_omega : ⟦Ω⟧ρ = ⊥`**.

On the other side, `Phi_botDinf` shows `⊥` acts as the everywhere-undefined function, so
`ddenot_I_ne_bot : ⟦I⟧ρ ≠ ⊥` (otherwise the identity on `D∞` would be constant, contradicting
`dinf_nontrivial`).

`ConvBE` is the compatible equivalence relation generated by beta reduction *and* eta
contraction — conversion in the `λη` calculus.  `ddenot_convBE` proves the model sound for it,
and therefore

* **`not_convBE_omega_I : ¬ ConvBE Ω I`** and `convBE_consistent` — the `λη` calculus is
  consistent.

This strengthens the consistency result of `M9-GRAPH-MODEL`, which only covers beta: the graph
model is not extensional and so cannot see eta.

## Boundary

* The base of the tower is the flat two-point domain `Bool`, and the ep-pair at level `0` is the
  standard one; no other choice of base is considered, and the construction is not stated for a
  general base domain.
* No adequacy, completeness or full-abstraction result is proved: nothing here says that equal
  denotations imply convertibility (that would be the local structure of `D∞`, i.e. the theory
  `λη` plus the identification of unsolvable terms, which is not formalized).
* `D∞` is not related to the graph model of `Start/GraphModel.lean`; the two models are built
  independently.
