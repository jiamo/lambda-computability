# M7-BOHM-SEPARATION

**Status:** DONE_STRONG

Modules `Start/Bohm.lean`, `Start/BohmOut.lean` and `Start/BohmEta.lean`, all imported by
`Start.lean`.  They build without `sorry` and without linter warnings.

## Finite Böhm trees (first exit criterion)

* `Lambda.BohmNF` — the finite Böhm tree of a normal form: `node b y [t₁, …, tₖ]` stands for
  `λ…λ y t₁ … tₖ` with `b` leading abstractions, `y` a de Bruijn index and the `tᵢ` again Böhm
  trees.  `Lambda.BohmNF.ind_mem` is the induction principle with the hypothesis available for
  every argument.
* `Lambda.BohmNF.toTerm` — the term denoted by a tree, built with `Lambda.lamN` (iterated
  abstraction) and `Lambda.appList`.
* `Lambda.BohmNF.is_normal_toTerm` — every tree denotes a normal form.
* `Lambda.exists_bohmNF_of_normal` / `Lambda.is_normal_iff_exists_bohmNF` — every normal form is
  denoted by a tree, so the normal terms are *exactly* the denotations of finite Böhm trees.
* `Lambda.BohmNF.toTerm_injective` / `Lambda.BohmNF.toTerm_inj_iff` — the representation is
  faithful: distinct trees denote distinct terms.  The supporting uniqueness lemmas
  `Lambda.lamN_inj` and `Lambda.appList_inj` are of independent use.

## Separation at the root (`Start/Bohm.lean`)

`Lambda.Separable M N` holds when some list of **closed** arguments sends `M` to `Lambda.true`
and `N` to `Lambda.false`; `Lambda.Separable.symm` shows the relation is symmetric (append
`false, true` to the argument list).

The substitution machinery is `Lambda.substDown` — the substitution performed when `λ…λ t` is
applied to a list of closed arguments — together with `Lambda.reduces_appList_lamN` and
`Lambda.argsFor` with `Lambda.substDown_argsFor_var`, which realises any prescribed substitution
of the bound variables by closed terms.

Both base cases of Böhm's induction are proved in η-general form: the two terms may have
different numbers `r₁, r₂` of leading abstractions and are compared after η-expansion to a common
arity `m₁ + r₁ = m₂ + r₂` (`Lambda.reduces_argsFor_head` carries out this η-expansion).

* `Lambda.separable_of_head_ne_gen` — different bound heads after η-expansion.
* `Lambda.separable_of_length_lt_gen` — the same head but different numbers of arguments.
* `Lambda.separable_of_root_ne_gen` — the two cases combined, phrased for Böhm trees;
  `Lambda.separable_of_root_ne` is the equal-arity special case.

## Böhm out (`Start/BohmOut.lean`)

The missing ingredient of Böhm's theorem — transporting a difference occurring deep inside the
two trees up to the root — is carried out with a *tagged tuple* substitution: every variable in
scope is replaced by the closed term

    Gᵢ = λ u₁ … u_K w. w u₁ … u_K ⟨i⟩

which stores the `K` arguments it receives together with a tag `⟨i⟩` identifying the variable and
hands them all to its last argument.  Because `Gᵢ` destroys no information, a *closed* applicative
context suffices to walk down the tree; no fresh variables are needed.

* `Lambda.csub` / `Lambda.csubEnv` — parallel substitution of closed terms, with
  `Lambda.reduces_appList_csub`: an `b`-fold abstraction applied to `b` closed arguments.
* `Lambda.projSel`, `Lambda.tagTuple`, `Lambda.reduces_appList_tagTuple`,
  `Lambda.reduces_tagTuple_extract` — the tuples and the way a context reads a stored argument
  or the tag back out.
* `Lambda.instTree` — the term denoted by a tree with closed terms substituted for its free
  variables; `Lambda.reduces_instTree_node` is one step of the descent.
* `Lambda.separable_tagTuple_of_tag_ne` and `Lambda.separable_tagTuple_of_length_lt` — two
  applied tagged tuples with different tags, resp. different numbers of stored arguments, are
  separable.
* `Lambda.BohmDiffer` — the two trees carry the same number of binders and the same head down to
  some node, where the heads or the arities differ.  `Lambda.separable_instTree` is the induction
  and `Lambda.separable_toTerm_of_bohmDiffer` the conclusion for closed trees.
* `Lambda.BohmSameBinders` with `Lambda.separable_toTerm_of_ne` and
  `Lambda.separable_of_toTerm_ne`: two *distinct* closed normal forms whose trees carry the same
  number of binders at every node are separable.

## η-general separation (`Start/BohmEta.lean`, second exit criterion)

The binder-matching hypothesis above is removed by comparing the two trees *after η-expanding
each node to the common arity* `max b₁ b₂`, and by naming variables with tags instead of de
Bruijn indices, so that subtrees living on the two sides of an η-expansion can still be compared.

* `Lambda.expEnv`, `Lambda.headTag`, `Lambda.argTreeOf`, `Lambda.argEnvOf` — the η-expanded view
  of a node: the binders met at a node receive the fresh tags `base, …, base + m - 1`, the `e`
  arguments added by η-expansion are the corresponding variables.
* `Lambda.TagEq` — η-equality of two tagged trees: at every node the η-expanded head tags, the
  η-expanded arities and all corresponding arguments agree.  `Lambda.tagEq_refl` (reflexivity)
  and the worked example showing that the trees of `λz. z` and `λz w. z w` are `TagEq` document
  the relation.
* `Lambda.TagDiffer` — its positive negation, with `Lambda.tagDiffer_of_not_tagEq` and
  `Lambda.not_tagDiffer_of_tagEq`: the two relations are complementary, so η-equal trees are
  never claimed to be separable.
* `Lambda.reduces_node_eta` — one step of the η-general descent: feeding the `b + e` tagged
  arguments of a node exposes the tag of its head applied to the instantiated arguments followed
  by the tags introduced by the η-expansion.
* `Lambda.separable_of_tagDiffer` — the η-general Böhm-out induction.
* `Lambda.separable_toTerm_of_not_tagEq` — **Böhm's theorem**: two closed normal forms whose
  Böhm trees are not η-equal are separable by a single list of closed arguments.
  `Lambda.separable_I_K` is a worked instance whose two trees have different numbers of binders
  at the root, so it is out of reach of the binder-matching form.

The restriction to η-*different* trees is necessary and not a gap: `Lambda.Separable` is defined
through β-reduction to the exact terms `true` and `false`, and η-equal terms have the same
applicative behaviour.  βη-equality of normal forms is rendered here by the tree relation
`Lambda.TagEq` (the node-wise comparison of the η-expanded trees), since the development has no
term-level η-reduction.

Gates: `lake build` succeeds; no `sorry`; no linter warnings.
