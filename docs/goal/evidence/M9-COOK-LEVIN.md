# M9-COOK-LEVIN

**Status:** DONE_STRONG

Modules `Start/Sat.lean`, `Start/Tseitin.lean`, `Start/CircuitBuild.lean`,
`Start/WordCircuit.lean`, `Start/CobhamCircuit.lean`, `Start/CobhamBRec.lean`,
`Start/PolyCircuit.lean`, `Start/CookLevin.lean`, `Start/InputSegment.lean`,
`Start/PinnedCnf.lean`, `Start/PinnedCircuit.lean`, `Start/CobhamPin.lean`,
`Start/CookLevinUniform.lean`, `Start/CobhamTransducer.lean`, `Start/CobhamShift.lean`,
`Start/CobhamBlock.lean`, `Start/CircuitCode.lean`, `Start/CobhamTseitin.lean`,
`Start/CookLevinCode.lean`, `Start/CodeUniformExample.lean`, `Start/CobCountable.lean`,
`Start/CookLevinExists.lean`, `Start/UniformCircuit.lean`, `Start/CookLevinBound.lean`,
`Start/UniformAuto.lean`, `Start/UniformMaj.lean`, `Start/UniformSym.lean`,
`Start/UniformLoop.lean`, `Start/UniformGrid.lean`, `Start/UniformState.lean`,
`Start/UniformStateCode.lean`, `Start/UniformStateSubsume.lean`, `Start/UniformStateInst.lean`,
`Start/UniformCA.lean`, `Start/UniformCACode.lean`, `Start/UniformCAInst.lean`,
`Start/UniformTM.lean`, `Start/UniformTMInst.lean`, `Start/UniformLayerPad.lean`,
`Start/UniformSelect.lean`, `Start/UniformIterate.lean`, `Start/UniformIterLang.lean`,
`Start/UniformIterateInst.lean`,
all imported by
`Start.lean`.  They build
without `sorry` and without linter warnings.

Two of the three exit criteria are met unconditionally: Boolean formulas and satisfiability are
encoded as a language over binary words, and **SAT is proved to be in NP**.  The third — that
every language in `NP` reduces to SAT — is *not* proved; what is proved is that it follows from a
single precisely stated compilation hypothesis, together with the Tseitin translation, which is
formalized in full.

## Formulas as a language over binary words (first exit criterion)

`Start/Sat.lean`.  A CNF is a list of clauses, a clause a list of literals, a literal a pair
`(sign, index)`; `Complexity.Sat.cnfVal σ F` is the truth value of `F` under the assignment `σ`,
a binary word whose missing bits read `false`.

Words encode CNFs by a prefix-free token code that is read **from the right**, which is the
direction in which Cobham's bounded recursion on notation consumes its argument:

* `1` — a tick, incrementing the variable index of the literal being read;
* `0 1` — a negative literal on the current tick count, `0 0 1` — a positive literal;
* `0 0 0` — a clause separator.

`encLit`, `encClause`, `encCnf` write the code; the decoder `decode : Word → Cnf` is a total,
junk-tolerant automaton (`DSt`, `dstep`, `drun`), so every word denotes some CNF.
`decode_encCnf` proves that decoding inverts the encoding.  `SAT` is the language
`{u | ∃ σ, cnfVal σ (decode u) = true}`, and `SAT_encCnf`, `SAT_encCnf_nil`,
`not_SAT_encCnf_empty_clause` show it is neither empty nor everything.

## SAT is in NP (second exit criterion)

`Complexity.Sat.inNP_SAT`.  The verifier is an explicit Cobham term.

* `MSt`/`mstep`/`mrun` is a second automaton that reads the same token code while *evaluating* it
  against an assignment `σ`, carrying only four items of state: the truth of the clauses read so
  far, the truth of the clause being read, the unread suffix of `σ`, and a two-bit phase.
  `mrun_eq` proves it simulates the decoder: its state is always the truth value of the decoded
  data.
* `satMachine` implements that automaton as a Cobham term by bounded recursion on notation, with
  the state packed into a word `allSat :: curSat :: phase bits :: assignment pointer`;
  `eval_satMachine` proves `satMachine.eval [u, σ] = encMSt (mrun σ u)`.  The bound needed by
  `bRec` is `boundT`, and `length_boundT`/`mrun_ptr_length` supply the length inequality that
  makes the truncation harmless.
* `satVerifier` runs the machine and reads its `allSat` bit, after checking with `Cob.dropU` that
  the witness is not longer than the input; `eval_satVerifier` characterizes when it accepts.
* The witness bound is the identity: `litVal_take`, `clauseVal_take`, `cnfVal_take` and the index
  bound `drun_bounded` show that a satisfying assignment may always be truncated to the length of
  the input, since a word of length `n` decodes to a CNF whose variables are all `< n`.

Reusable Cobham gadgets added on the way: `bw`, `Cob.iteC`, `Cob.dropU` (drop `|u|` bits),
`Cob.tailN`, `Cob.nthBit`, `Cob.andT/orT/notT/iteT/consT`.

## The Tseitin translation (part of the third exit criterion)

`Start/Tseitin.lean`.  A circuit is a straight-line program `Circuit = List Gate`, written output
first, in which a gate may refer only to the gates after it in the list; the identifier of a gate
is the number of gates below it, so identifiers are stable under passing to a suffix, which makes
both the evaluator (`vals`, `out`) and the translation structurally recursive.  `csat C` says some
input word makes the output true.

`toCnf` is the Tseitin translation: the CNF variable `2 * j + 1` stands for the gate `j` and
`2 * i` for the circuit input `i`, and the clauses assert the defining equivalence of every gate
plus the truth of the output gate.

* `cnfValF_defsCnf` — the canonical assignment (input bits on the even variables, gate values on
  the odd ones) satisfies the defining clauses;
* `vals_of_cnfValF` — conversely, *every* satisfying assignment computes the gate values of the
  circuit run on the input it describes;
* `csat_iff_sat_toCnf` — **the translation preserves satisfiability**;
* `length_toCnf_le` — it has linear size, at most `3 * |C| + 1` clauses.

The bridge between the two notions of assignment (a word, as `SAT` uses, and a function, as the
induction uses) is `cnfVal_eq_cnfValF` together with `cnfVal_map_range` and the variable bound
`toCnf_vars`.

## Compiling Cobham terms into circuits

`Start/CircuitBuild.lean`, `Start/WordCircuit.lean`, `Start/CobhamCircuit.lean`,
`Start/CobhamBRec.lean` and `Start/PolyCircuit.lean` carry out the compilation of an arbitrary
Cobham term into a Boolean circuit of polynomial size.

* `Start/CircuitBuild.lean` — circuits are built incrementally.  `Ext C C'` says `C'` is `C` with
  gates added on top, `Holds C w f` says the wire `w` computes `f`, and every gadget is an
  *existence* lemma: `exists_inp`, `exists_cst`, `exists_neg`, `exists_conj`, `exists_disj`,
  `exists_ite`, `exists_bigOr`, `exists_bigAnd`, and `exists_wire_list`, which builds `n` wires at
  a cost of `n * cost` gates.
* `Start/WordCircuit.lean` — a *word signal* `WHolds C M ps bs f` represents the word-valued
  function `f`, of length at most `M`, by two wire vectors: presence and bits, left-aligned.
  Dropping a prefix (`WHolds.drop`) costs no gates at all — it is a shift of the two vectors —
  which is what later makes bounded recursion unrollable.  Gadgets: `exists_constSig`,
  `exists_emptySig`, `exists_resize`, `exists_iteSig`, `exists_takeSig`, `exists_consSig`,
  `exists_smashSig`, and `exists_inputSig`, which reads a word of length at most `N` off the
  circuit input; `exists_inWord` shows every such word is read off some input.
* `Start/CobhamCircuit.lean` — `CompilesAt v m c` says that on top of any well-formed circuit
  carrying signals for the arguments (all of width at most `m`), a signal for `v` can be built
  with `c` further gates, and `CobCompiles v` asks the cost to be a monotone polynomial in `m`.
  The projections, the empty word, the successors, the smash function and composition are handled
  here (`cobCompiles_proj`, `cobCompiles_empty`, `cobCompiles_app`, `cobCompiles_smash`,
  `cobCompiles_comp`).
* `Start/CobhamBRec.lean` — bounded recursion on notation.  The recursion argument is not known at
  compile time, so the step is unrolled once per position; at position `j` the step value is
  multiplexed against the value carried over on the presence wire of that position, and truncated
  against the compiled bound.  `exists_bRecSig` performs the unrolling and `cobCompiles_bRec` the
  induction; `cobCompiles` concludes that **every Cobham term compiles into circuits of
  polynomial size**.
* `Start/PolyCircuit.lean` — the application layer.  `exists_decideCircuit` is `P ⊆ P/poly`: for
  every Cobham term `c` there is a monotone polynomial `sz` such that for every `N` some
  well-formed circuit of at most `sz N` gates outputs, on input `x`, whether `c` accepts the word
  of length at most `N` read off `x`.  `exists_witnessCircuit` and `exists_npCircuitFamily` give
  the satisfiability version: for every language in `NP` there is a family `cc` of well-formed
  circuits of polynomial size with `csat (cc x) ↔ L x`.

## What remains, and its exact statement

`Start/CookLevin.lean` isolates the missing step as

```lean
def CircuitCompilable (v : Cob) : Prop :=
  ∃ (cc : Word → Tseitin.Circuit) (gen : Cob),
    (∀ x, Tseitin.wf (cc x)) ∧
    (∀ x, Tseitin.csat (cc x) ↔ ∃ w : Word, v.eval [x, w] ≠ []) ∧
    (∀ x, gen.eval [x] = Sat.encCnf (Tseitin.toCnf (cc x)))
```

— an arbitrary Cobham verifier compiles, uniformly in the input, into a Boolean circuit whose
satisfying inputs are its accepted witnesses, the translation being produced by a Cobham term.
Granted it:

* `npHard_SAT_of_circuitCompilable` — **SAT is NP-hard**;
* `npComplete_SAT_of_circuitCompilable` — **SAT is NP-complete**;
* `peqNP_iff_inP_SAT_of_circuitCompilable` — `P = NP` iff `SAT ∈ P`.

The hypothesis is never assumed: it occurs only as an antecedent, and no other module mentions it.

Of the two things `CircuitCompilable` asks for, the *circuits* are now supplied unconditionally by
`Complexity.Tseitin.exists_npCircuitFamily`; only their *uniform generation* is missing.  That
residue is isolated as

```lean
def UniformlyGenerated (cc : Word → Tseitin.Circuit) : Prop :=
  ∃ gen : Cob, ∀ x, gen.eval [x] = Sat.encCnf (Tseitin.toCnf (cc x))
```

and `npHard_SAT_of_uniform`, `npComplete_SAT_of_uniform` derive NP-hardness and NP-completeness of
SAT from it alone.

Unconditionally, `polyManyOne_SAT_of_inP` shows that every language in `P` reduces to SAT (the
reduction decides the language and returns a fixed satisfiable or unsatisfiable formula), so the
reduction apparatus around `SAT` is not vacuous.

## Removing the dependence on the instance

The hypothesis above still quantifies over the instance.  Four further modules reduce it to the
standard *P-uniformity* of a circuit family, a statement about the length of the instance only.

**The instance is read off the circuit input.**  `Start/InputSegment.lean` repeats the word-reading
gadget of `Start/WordCircuit.lean` with an offset: `Complexity.Tseitin.inWordAt off N x` is the
word encoded by the input positions `[off, off + 2N)`, and `exists_inputSigAt` builds the
corresponding signal.  With it, `Start/PinnedCircuit.lean` builds

```lean
theorem exists_pinAcceptCircuit (v : Cob) :
    ∃ sz : ℕ → ℕ, MonoPoly sz ∧ ∀ (n N : ℕ),
      ∃ C : Circuit, wf C ∧ C.length ≤ sz (max n N) ∧
        ∀ x, out x C = decide (v.eval [inWord n x, inWordAt (2 * n) N x] ≠ [])
```

— the instance is read off `[0, 2n)` and the witness off `[2n, 2n + 2N)`, so the circuit depends on
the two *lengths* only.

**The instance is written into the formula by unit clauses.**  `Start/PinnedCnf.lean` defines the
clauses `pinCnfW u` pinning the input `2m` to `true` and the input `2m + 1` to `u m`, and proves

```lean
theorem sat_append_pinCnfW (C : Circuit) (hC : wf C) (u : Word) :
    (∃ σ : Word, cnfVal σ (toCnf C ++ pinCnfW u) = true) ↔
      ∃ x : Word, out x C = true ∧ ∀ m, m < u.length →
        x.getD (2 * m) false = true ∧ x.getD (2 * m + 1) false = u.getD m false
```

together with `inWord_eq_of_pinned`, which turns that pinning pattern back into the equation
`inWord |u| x = u`.

**Those clauses are produced by an explicit Cobham term.**  `Start/CobhamPin.lean` writes their
code as a bounded recursion on notation over the scanned suffix of the word, the whole word being
passed along so that the position of the current bit — needed for the unary variable index — is
recoverable as `|x| - |suffix| - 1`:

```lean
theorem eval_pinTerm (x : Word) : pinTerm.eval [x] = encCnf (pinCnfW x)
```

**The resulting reduction.**  `Start/CookLevinUniform.lean` composes the two halves,
`r x = gen x ++ pinTerm x`, and proves

```lean
def LengthUniform (cf : ℕ → Tseitin.Circuit) : Prop :=
  ∃ gen : Cob, ∀ x : Word, gen.eval [x] = Sat.encCnf (Tseitin.toCnf (cf x.length))
```

* `npHard_SAT_of_lengthUniform` — **SAT is NP-hard** as soon as the length-indexed acceptance
  circuits are P-uniform;
* `npComplete_SAT_of_lengthUniform` — **SAT is NP-complete** under the same hypothesis.

Like the earlier hypotheses, this one is nowhere assumed; it appears only as an antecedent.  It is
strictly weaker than `UniformlyGenerated`: it says that the description of the `n`-th circuit is
computable in polynomial time from a word of length `n`, and no longer mentions the instance.

## A Cobham programming toolkit, and the Tseitin translation as a Cobham function

Four further modules remove the *translation* from the residual hypothesis, leaving only the
uniformity of the circuit family itself.

**Finite-state transducers are Cobham functions.**  `Start/CobhamTransducer.lean` defines the
semantics of a finite-state transducer scanning a word from the right (`rst`, `rrun`) and from the
left (`lst`, `lrun`), and compiles each into a single Cobham term: `eval_fstRunTerm`,
`eval_lrunTerm`.  Word reversal (`Cob.eval_revTerm`) is a Cobham function, and is what carries one
direction to the other.  `Start/CobhamShift.lean` applies the scheme to renumber the variables of
an encoded CNF (`Sat.decode_eval_shiftTerm`, `Sat.SAT_eval_shiftTerm`).

**Block-emitting recursions are Cobham functions.**  Writing a formula out of a description needs
more than a transducer: the block emitted at a position contains unary variable indices, so it may
be as long as the input, and it depends on how many tokens have already been passed.
`Start/CobhamBlock.lean` provides that scheme.  A block-emitting recursion is given by a
finite-state control, a bounded counter increment, and, for every state and bit, a Cobham term
computing the block from the suffix, from the counter in unary and from a parameter.
`eval_cntTerm` computes the counter, `eval_blkRunTerm` the whole output; the emitted blocks may
grow linearly with the suffix, so the output is quadratic.  Reading a unary field off the front of
a word (`Cob.eval_leadOnes`, `Cob.eval_dropOnes`, `Cob.eval_tail`) comes with it.

**Circuits as words.**  `Start/CircuitCode.lean` writes a gate as a self-delimiting token
`0 1^tag 0 1^{a+1} 0 1^{b+1}` — a marker bit, a bounded tag naming the kind of the gate, and two
unary fields, each shifted by one so that it is nonempty — and a circuit as the concatenation of
the tokens of its gates, output gate first (`encGate`, `encCirc`).  A finite-state control scanning
the word from the right therefore knows, at every `0`, whether that `0` is the marker of a token
and what the tag of the token is, and the counter of the recursion counts the markers already
passed, which is exactly the identifier of the gate whose token starts there (`rcnt_encCirc`).
`brun_encCirc` proves that the resulting block-emitting recursion outputs the code of
`Complexity.Tseitin.defsCnf`.

**The Tseitin translation is a Cobham function.**  `Start/CobhamTseitin.lean` supplies the terms:
one per kind of gate, computing the code of the defining CNF of that gate from the fields of its
token and from its identifier, with the doubling and shifting of unary indices done by the gadgets
`Cob.oddU`, `Cob.oddUm1`, `Cob.evenUm1`.  Feeding them to `blkRunTerm`, and prefixing the clause
asserting the output gate, gives

```lean
theorem eval_tseitinTerm (C : Circuit) :
    tseitinTerm.eval [encCirc C] = Sat.encCnf (toCnf C)
```

**The resulting hypothesis.**  `Start/CookLevinCode.lean` composes with it:

```lean
def CodeUniform (cf : ℕ → Tseitin.Circuit) : Prop :=
  ∃ gen : Cob, ∀ x : Word, gen.eval [x] = CircCode.encCirc (cf x.length)
```

* `lengthUniform_of_codeUniform` — P-uniform descriptions give `LengthUniform`;
* `npHard_SAT_of_codeUniform`, `npComplete_SAT_of_codeUniform` — **SAT is NP-hard, hence
  NP-complete, as soon as the length-indexed acceptance circuits have P-uniform descriptions.**

This is the textbook hypothesis: what has to be produced in polynomial time from `1^n` is the
*description of the circuit*, not the code of a formula.  Like the earlier ones, it is nowhere
assumed; it appears only as an antecedent.

**The hypothesis is inhabited.**  `Start/CodeUniformExample.lean` exhibits an explicit family that
meets it: `cfNeg (n + 1)` is one input gate with `n` negations on top, so it has `n + 1` gates and
its description grows without bound.  It is well formed (`wf_cfNeg`), its circuits are satisfiable
(`csat_cfNeg`, via `out_cfNeg`, which computes the output as the `n`-fold negation of the first
input bit), and `codeUniform_cfNeg` proves `CodeUniform cfNeg`: the generator smashes the input to
`1^n` and runs a block-emitting recursion writing one gate token per position, the counter
supplying the identifier of the gate.

## The residual hypothesis, in non-vacuous form

`Start/CobCountable.lean` and `Start/CookLevinExists.lean`.

The three conditional statements above (`npHard_SAT_of_uniform`, `npHard_SAT_of_lengthUniform`,
`npHard_SAT_of_codeUniform`) take as antecedent that **every** well-formed family of acceptance
circuits of polynomial size is P-uniform.  That antecedent is false, so those implications, while
true, are vacuous.

* `Complexity.Cob.encNat` is a Gödel numbering of Cobham terms, `Complexity.Cob.encNat_injective`
  proves it injective, and `Complexity.instCountableCob` concludes that **there are only countably
  many Cobham terms**; `Complexity.exists_surjective_cob` turns that into a sequence running
  through all of them.
* `Complexity.Tseitin.falseC j` is the constant `false` under `j` double negations: well formed
  (`wf_falseC`), of `2 * j + 1` gates, and with output `false` on every input (`out_falseC`), hence
  unsatisfiable (`not_csat_falseC`).  Padding it by one double negation or none, as dictated by a
  diagonal against that sequence, gives `Complexity.Tseitin.diagFam`, a family of at most three
  gates whose description no Cobham term writes (`Complexity.Tseitin.not_uniform_diagFam`).
* Hence `Complexity.not_forall_uniformlyGenerated`, `Complexity.not_forall_lengthUniform` and
  `Complexity.not_forall_codeUniform`: **the antecedents of the earlier conditional forms are
  false.**

The hypothesis that is actually wanted quantifies existentially over the family:

```lean
def PUniformAcceptFamilies : Prop :=
  ∀ (v : Cob) (p : ℕ → ℕ), ∃ cf : ℕ → Tseitin.Circuit,
    (∀ n, Tseitin.wf (cf n)) ∧
    (∀ (n : ℕ) (x : Word), Tseitin.out x (cf n) =
      decide (v.eval [Tseitin.inWord n x, Tseitin.inWordAt (2 * n) (p n) x] ≠ [])) ∧
    CodeUniform cf
```

`Complexity.polyManyOne_SAT_of_acceptFamily` builds the reduction attached to one such family, and
`Complexity.npHard_SAT_of_pUniform`, `Complexity.npComplete_SAT_of_pUniform`,
`Complexity.peqNP_iff_inP_SAT_of_pUniform` draw the conclusions.  This hypothesis is exactly the
P-uniform compilation of Cobham verifiers into circuits; like the earlier ones it is nowhere
assumed.

## An algebra of P-uniform descriptions

`Start/UniformCircuit.lean` collects the closure properties a description-writing program is built
from:

* `Complexity.codeUniform_const` — a fixed circuit is a uniform family;
* `Complexity.codeUniform_append` — descriptions may be concatenated
  (`Complexity.CircCode.encCirc_append`);
* `Complexity.codeUniform_layer` — a **layer**, `k n` gates whose kind and fields are read off the
  identifier of the gate and off `1^n`, is uniform as soon as one Cobham term writes the token of
  the gate with identifier `c` and the count `k n` is written in unary by another; this is the loop
  of the program, supplied by the block-emitting recursion of `Start/CobhamBlock.lean`.

The chain of negations of `Start/CodeUniformExample.lean` is a layer, and
`Complexity.codeUniform_cfNeg_of_layer` recovers its uniformity from the general lemma alone.

## A nontrivial P-uniform family

`Start/UniformAnd.lean` exercises the algebra on a family that computes something.
`Complexity.CircCode.andCirc n` is two layers — `n` input gates below, and above them `n`
conjunction gates accumulating the running conjunction — and both halves of the picture are proved:

* `Complexity.CircCode.wf_andCirc` — the circuits are well formed;
* `Complexity.CircCode.out_andCirc` — the output of `andCirc n` is the conjunction of the first `n`
  bits of the circuit input (`Complexity.CircCode.andPrefix`);
* `Complexity.codeUniform_andCirc` — a single Cobham term writes the description of `andCirc n`
  from any word of length `n`, obtained from `codeUniform_append` applied to two instances of
  `codeUniform_layer`.

So `Complexity.CodeUniform` is inhabited by a linear-size family deciding a nontrivial language,
and the layer lemma is shown to be usable with a template whose fields depend on the parameter `n`
as well as on the gate identifier.

## Putting two circuits into one

Concatenating descriptions is not concatenating circuits: gates are numbered from the bottom of the
list, so writing `C` on top of `D` shifts every identifier of `C` by the length of `D`.  Two further
modules supply the operations that repair this, and show that both are performed on *descriptions*
by a Cobham term.

`Start/UniformShift.lean` relocates a circuit.  `Complexity.Tseitin.reloc d C` raises every
reference of every gate of `C` by `d`, leaving inputs and constants alone; the semantics is
preserved (`Complexity.Tseitin.vals_reloc_append`, `Complexity.Tseitin.out_reloc_append`) and so is
well-formedness (`Complexity.Tseitin.wf_reloc_append`).  The relocation of a description is carried
out by the block-emitting recursion of `Start/CobhamBlock.lean`, run over the code of `C` with the
shift `1^d` as parameter, rewriting every token through the field readers of
`Start/CobhamTseitin.lean` (`Complexity.CircCode.eval_relocTerm`).  Hence
`Complexity.codeUniform_reloc` and, since the length of a circuit is read off its code by the
counter of that recursion, the stacking rule `Complexity.codeUniform_stack`: **two P-uniform
families may be written into one circuit.**

`Start/UniformCompose.lean` connects them.  `Complexity.Tseitin.reroute d e C` relocates `C` by `d`
and additionally rewires its circuit inputs: the input `i` of `C` becomes a reference to the gate
`i + e` of the circuit underneath, so that `reroute D.length e C ++ D` runs `C` on the word read off
the values of the gates `e, e + 1, …` of `D` (`Complexity.Tseitin.out_reroute_append`, under the
range condition `Complexity.Tseitin.inpsLt`).  The rewriting is again a Cobham function of the
description, with the two shifts packed into one parameter word
(`Complexity.CircCode.eval_rerouteTerm`), whence `Complexity.codeUniform_reroute` and
`Complexity.codeUniform_compose`: **two P-uniform families may be composed.**

Both operations are exercised on the two families that are available with proved semantics: the
conjunction circuits side by side with the chain of negations
(`Complexity.CircCode.andOverNeg`, `Complexity.CircCode.out_andOverNeg`,
`Complexity.codeUniform_andOverNeg`) and fed by it
(`Complexity.CircCode.andAfterNeg`, `Complexity.CircCode.out_andAfterNeg`,
`Complexity.codeUniform_andAfterNeg`).

## The loop rules: automata, blocks, and grids

The rules above write a circuit whose gate at identifier `c` is read off `c` alone.  A compiler does
not produce circuits of that shape: it produces a sequence of *blocks*, and the gate to write
depends on which block it belongs to and on its offset inside the block.  Three rules, in
`Start/UniformBlock.lean`, `Start/UniformLoop.lean` and `Start/UniformGrid.lean`, close that gap.

* `Complexity.codeUniform_autoLayer` — **the loop may carry a finite-state control.**  The gate
  written at `c` may depend on the state of an arbitrary finite automaton after reading `1^c` and on
  the counter it accumulates, with one Cobham term per state
  (`Complexity.CircCode.brun_layer_auto` is the underlying computation of the block-emitting
  recursion of `Start/CobhamBlock.lean`).
* `Complexity.codeUniform_blockLayer` — taking the automaton to be the cycle of length `K₀`, its
  state after `1^c` is `c % K₀` and its counter is `c / K₀` (`Complexity.CircCode.rst_cyc`,
  `Complexity.CircCode.rcnt_cyc`), so **a family made of blocks of a fixed size is P-uniform**,
  given one Cobham term per offset inside the block.
* `Complexity.Cob.eval_divmodT` — **Euclidean division in unary is a Cobham function**: a bounded
  recursion on notation over `1^c` carries the pair `(q, r)` written as `1^q 0 1^r`, increments the
  remainder at each step and turns it over into a carry when it reaches the divisor; the bound is
  the length of the recursion argument plus one, which suffices because `c/w + c%w ≤ c`.
* `Complexity.codeUniform_gridLayer` — with division available the block size need no longer be
  constant: **a family whose `n`-th circuit is a grid of blocks of width `w n` is P-uniform** as soon
  as one Cobham term writes the gate at a given row and column from those two indices in unary and
  from `1^n`, and `w` is itself computed in unary from the instance.  This is the shape the
  unrolling of a bounded recursion has, each stage being a circuit of width polynomial in `n`.

Each rule is inhabited by an explicit family, so none of them is vacuous.
`Complexity.CircCode.pairCirc` (`Start/UniformLoop.lean`) is `n` blocks of four gates computing
`⋁_{i<n} (x_{2i} ∧ x_{2i+1})`; its blocks are *not* independent — each reads the accumulator of the
block below it, as the unrolling of a recursion does — and its first block is a special case, so the
term writing the last gate of a block branches on whether the block index is zero.  Its semantics
are `Complexity.CircCode.out_pairCirc_iff` and its uniformity `Complexity.codeUniform_pairCirc`.
Two general tools are used to write it: `Complexity.CircCode.tokTerm`, which writes the token of a
gate with a fixed tag and two unary fields, and `Complexity.CircCode.linT`, which computes
`1^{q·i+r}` from `1^i`.  For the grid rule, `Complexity.codeUniform_gridCirc` is a family of `n + 1`
rows of `n + 1` gates in which each row reads the row below it, so the block width really does grow
with the instance.

## Boolean combinations, and an unconditional reduction to SAT

`Start/UniformBool.lean` completes the algebra of P-uniform descriptions with the one connection
that was still missing: joining the *outputs* of two circuits by a single gate.
`Complexity.Tseitin.stackC` writes one circuit on top of another with the references relocated,
and `Complexity.Tseitin.negC`, `conjC`, `disjC` put a negation, a conjunction or a disjunction gate
on top.  Their semantics is proved (`out_negC`, `out_conjC`, `out_disjC`: the composite computes the
Boolean connective of the outputs of its parts on the *same* circuit input), they preserve
well-formedness (`wf_negC`, `wf_conjC`, `wf_disjC`), and they preserve P-uniformity
(`Complexity.codeUniform_negC`, `codeUniform_conjC`, `codeUniform_disjC`).  The uniformity proofs
rest on two new general tools: `Complexity.exists_lenTerm`, which extracts from a P-uniform family
a Cobham term writing the *number of gates* of `cf n` in unary, and
`Complexity.codeUniform_gate`, which says a one-gate family is P-uniform as soon as its tag is
constant and its two fields are unary Cobham functions of `1^n`.

`Start/UniformDecide.lean` then draws the consequence that does not need the open hypothesis.  A
language is `Complexity.PUniformDecidable` when some P-uniform family of well-formed, nonempty
circuits decides it: on every input `Complexity.Tseitin.Pinned n y` presenting a word of length `n`
in the paired format of `Complexity.Tseitin.inWord`, the circuit `cf n` outputs `true` exactly on
the members of the language.  For such a language the Cook–Levin reduction goes through with no
hypothesis left over:

* `Complexity.polyManyOne_SAT_of_pUniformDecidable` — **every P-uniformly decidable language
  reduces to SAT in polynomial time.**  The reduction is the same as in the conditional forms —
  the Tseitin translation of the `|x|`-th circuit together with the unit clauses pinning `x` into
  its input — and `Complexity.Tseitin.sat_append_pinCnfW` identifies the satisfying assignments of
  the result with the pinned inputs accepted by the circuit.
* `Complexity.PUniformDecidable.not`, `.and`, `.or` — the class is closed under the Boolean
  operations, by the three combinators above.
* `Complexity.pUniformDecidable_allOnes` — the class is **inhabited by a nontrivial language**:
  `Complexity.AllOnes`, the words all of whose bits are `true`, is decided by
  `Complexity.allOnesC n`, the conjunction circuit over the first `2 * n` input bits with a
  constant gate underneath, whose uniformity comes from `Complexity.codeUniform_andCirc`
  reindexed along the doubling term and `Complexity.codeUniform_stack`.  Hence
  `Complexity.polyManyOne_SAT_allOnes`.
* `Complexity.pUniformDecidable_someOne` — and by a second, dual language: `Complexity.SomeOne`,
  the words with at least one bit `true`, is decided by `Complexity.someOneC n`, built from the
  block loop rule family `Complexity.CircCode.pairCirc` — on a pinned input the first component of
  every pair is the flag, so its disjunction over pairs runs over the bits of the word.  Hence
  `Complexity.polyManyOne_SAT_someOne`.
* `Complexity.npHard_SAT_of_pUniformDecidable`, `npComplete_SAT_of_pUniformDecidable` — SAT is
  NP-hard, hence NP-complete, as soon as every language in NP is decided by a P-uniform family.
  This is a second non-vacuous form of the residual hypothesis, stated about languages rather than
  about verifiers and witness bounds.

This is the shape the eventual Cook–Levin proof will have: what `Complexity.PUniformAcceptFamilies`
is still needed for is only the *construction* of the deciding family for an arbitrary NP language,
not the reduction that follows from it.

## The witness bound of the residual hypothesis — `Start/CookLevinBound.lean`

The hypothesis under which NP-hardness of SAT used to be derived,
`Complexity.PUniformAcceptFamilies`, quantified over an *arbitrary* function `p : ℕ → ℕ` bounding
the length of the witness.  That hypothesis is **false**, and it is refuted here.

* `Complexity.CircCode.encCirc_injective` — the token code of a circuit determines the circuit; the
  noncomputable decoder `Complexity.CircCode.circOf` inverts it (`circOf_encCirc`).
* `Complexity.Cob.parityVerifier` — an explicit Cobham verifier that accepts a pair exactly when the
  witness has odd length (`eval_parityVerifier`, `parityVerifier_accepts`).
* `Complexity.not_pUniformAcceptFamilies` — no P-uniform acceptance family exists for every verifier
  and every witness bound.  For the parity verifier the `n`-th acceptance circuit determines the
  parity of `p n`, so a Cobham description of the family computes `p n mod 2` in polynomial time;
  since `p` is an arbitrary function, choosing it to diagonalize against the countably many Cobham
  terms (`Complexity.exists_surjective_cob`) defeats every candidate description.
  `Complexity.not_pUniformAcceptFamilies_mono` sharpens this: the hypothesis fails even when `p` is
  required to be monotone and polynomially bounded, taking `p n = 2 * n + b n` with `b n ∈ {0,1}`
  the diagonal bit.
* `Complexity.StdUniformAcceptFamilies` is the corrected hypothesis: the witness bound is a standard
  polynomial `n ↦ a * (n + 1) ^ k`, which is what the definition of `NP` actually provides.  From it
  the same argument as before gives `Complexity.npHard_SAT_of_stdUniform`,
  `Complexity.npComplete_SAT_of_stdUniform` and
  `Complexity.peqNP_iff_inP_SAT_of_stdUniform`.  It is nowhere assumed.

So the residual hypothesis of this task is now one that the diagonal argument does not refute, and
the earlier statement of it is kept only as a refuted one.

## Every regular language is P-uniformly decidable — `Start/UniformAuto.lean`

The inhabitants of `Complexity.PUniformDecidable` used to be two ad-hoc languages.  They are now
subsumed by a general construction: **the language of an arbitrary finite automaton**.

`Complexity.AutoLang δ ac` is the language of the automaton with states `ℕ`, transition `δ`, initial
state `0` and accepting predicate `ac`, and the deciding family is an explicit chain of one block of
`4 + 2 * m * m + m` gates per input bit, for an automaton with `m` states:

* offsets `0`–`3` of a block hold the constants, the input bit `.inp (2 i + 1)` and its negation;
* for each pair of states `(s, t)` a conjunction gate says "the automaton was in `s` and the bit
  read sends `s` to `t`", and an accumulator gate disjoins those conjunctions over `s`, so the
  accumulator at `(s, m - 1)` is the one-hot bit "the automaton is in state `t`" (`lval_state`);
* a final chain of `m` gates disjoins the one-hot bits of the accepting states (`lval_fin`,
  `out_autoCirc`).

`Complexity.CircCode.autoBlk` is the single Cobham term writing the token of the gate at offset `o`
of block `c` from `1^o`, `1^c` and `1^n`, and `Complexity.CircCode.autoT_fld_le` bounds the fields of
that token linearly, so `Complexity.codeUniform_blockLayer` applies:
**`Complexity.codeUniform_autoCirc`** — the descriptions of the family are written by one Cobham
term.  With a constant gate stacked underneath for the empty word
(`Complexity.CircCode.autoDec`, `out_autoDec`) this gives

* **`Complexity.pUniformDecidable_autoLang`** — every regular language is decided by a P-uniform
  circuit family, and hence
* **`Complexity.polyManyOne_SAT_autoLang`** — every regular language reduces to SAT in polynomial
  time, unconditionally.

## Past finite-state computation: the majority language — `Start/UniformMaj.lean`

The blocks of the automaton family have a size that does not depend on the input length, so that
construction reaches exactly the regular languages.  The grid rule
`Complexity.codeUniform_gridLayer` allows blocks that *grow* with the instance, and this module uses
it on a language that is **not** regular.

`Complexity.Maj` is the set of words at least half of whose bits are `true`.  The deciding circuit
is the counting grid of width `n + 1`: the gate of row `3 * t`, column `j` holds "at least `j` of
the first `t` bits are `true`" (`Complexity.CircCode.lval_maj_count`), the three rows above it copy
the bit `t`, form the conjunctions `c(t, j - 1) ∧ x t` and take the disjunctions

`c(t + 1, j) = c(t, j) ∨ (c(t, j - 1) ∧ x t)`,

and one selector gate on top reads off the column `⌈n/2⌉` of the last count row
(`Complexity.CircCode.out_majC`).  Recovering the row and the column of a gate from its identifier
needs Euclidean division in unary, which is exactly what the grid rule provides; the block-writing
term is `Complexity.CircCode.majBlk` and the field bound is
`Complexity.CircCode.length_encGate_majT`.  Hence

* **`Complexity.codeUniform_majC`** — the descriptions of the deciding family are written by a
  single Cobham term;
* **`Complexity.pUniformDecidable_maj`** and **`Complexity.polyManyOne_SAT_maj`** — the majority
  language is P-uniformly decidable, and reduces to SAT in polynomial time, unconditionally;
* **`Complexity.maj_ne_autoLang`** — and it is *not* the language of any finite automaton: two
  prefixes `1^a` and `1^b` with `a < b ≤ m` must lead an `m`-state automaton to the same state, and
  appending `0^b` separates them in `Maj`.  So this family is not an instance of the previous one.

## Reading the whole counting grid: uniform symmetric languages — `Start/UniformSym.lean`

`Start/UniformMaj.lean` uses one column of the last row of the counting grid.  This module uses all
of them, and thereby replaces the individual instances by a single general theorem.

Let `acc : ℕ → ℕ → Bool` be a *count predicate*, `acc n c` the verdict on a word of length `n` with
`c` bits `true`, and let `Complexity.SymLang acc` be the language it defines.  Say that the
predicate is *uniform* (`Complexity.CountUniform acc`) when a single Cobham term decides `acc n c`
from `1^c` and `1^n`.

* `Complexity.CircCode.symT`, `Complexity.CircCode.symTop` — the **selection chain**: one block of
  six gates per possible count `j ≤ n`, holding the thresholds `c(j)` and `c(j + 1)`, the negation
  of the latter, the conjunction `c(j) ∧ ¬c(j + 1)` — "exactly `j` bits are `true`" — its masking
  by the constant verdict `acc n j`, and the running disjunction of the masked bits
  (`Complexity.CircCode.lval_sym_exact`, `lval_sym5`, `out_symTop`).
* The chain is a family of blocks of a *fixed* size, so `Complexity.codeUniform_blockLayer`
  applies: `Complexity.CircCode.symBlkT` is the term writing the gate at each offset — it decides
  `j < n` and `j = 0` by unary comparison, and calls the given term for `acc n j` — and
  `Complexity.codeUniform_symTop` is its uniformity.
* `Complexity.CircCode.symC` composes the chain with the counting grid by
  `Complexity.Tseitin.reroute`, its circuit inputs rewired to the gates of the last count row, so
  `Complexity.CircCode.out_symC` reads `acc n c` off the whole grid, and
  `Complexity.codeUniform_symC` follows from `Complexity.codeUniform_compose`.

Hence

* **`Complexity.pUniformDecidable_symLang`** — every symmetric language with a Cobham-decidable
  count predicate is decided by a P-uniform circuit family, and
* **`Complexity.polyManyOne_SAT_symLang`** — reduces to SAT in polynomial time, unconditionally.

Three instances are recorded, each with the Cobham term for its predicate: majority
(`Complexity.countUniform_maj`, `Complexity.symLang_maj`, so
`Complexity.pUniformDecidable_maj'` re-derives the earlier result), the words in which exactly half
of the bits are `true` (`Complexity.pUniformDecidable_exactHalf`,
`Complexity.polyManyOne_SAT_exactHalf`), and the words whose number of `true` bits is divisible by
`k` (`Complexity.pUniformDecidable_countMod`).  The exact-half language is proved not to be the
language of any finite automaton (`Complexity.exactHalf_ne_autoLang`), so this family is not an
instance of the automaton construction; and `Complexity.pUniformDecidable_autoLang_and_symLang`
combines a regular condition with a count condition through the Boolean closure.

## Automata with polynomially many states

`Start/UniformState.lean`, `Start/UniformStateCode.lean` and `Start/UniformStateInst.lean` unify
the two previous constructions.  An *automaton with polynomially many states* on inputs of length
`n` has `m n` states, a transition function `δ n : ℕ → Bool → ℕ` and an acceptance predicate
`ac n : ℕ → Bool`; its language is `Complexity.StateLang δ ac`, and the uniformity hypothesis
`Complexity.StateUniform δ ac` asks that `m`, the two branches of `δ` and `ac` be computed in unary
by Cobham terms.

* `Start/UniformState.lean` builds the circuit `Complexity.CircCode.stGrid δ ac (m n) n`: a grid of
  `m n` columns, one per state, made of one block of `2 * m n + 4` rows per input bit followed by
  an acceptance row.  Inside the block of the bit `t` the one-hot vector of the state after `t`
  bits is recomputed from the one-hot vector after `t - 1` bits: for each target state `s` a
  conjunction row selects, for every source state `j`, the constant `true`, the bit, its negation
  or the constant `false` according to which of the two transitions out of `j` land on `s`, and an
  accumulator row takes the disjunction along the row.  `Complexity.CircCode.lval_st_state` proves
  that the one-hot bits really do record the state, and `Complexity.CircCode.out_stGrid` that the
  grid accepts exactly the language of the automaton.
* `Start/UniformStateCode.lean` writes the description of that grid with a single Cobham term
  (`Complexity.CircCode.stBlkT`, `Complexity.CircCode.eval_stBlkT`), bounds the size of each gate
  (`Complexity.CircCode.length_encGate_stT`), and concludes with the grid rule
  `Complexity.codeUniform_gridLayer` that the family is P-uniform
  (`Complexity.codeUniform_stGrid`).  Hence **the language of a uniform poly-state automaton is
  P-uniformly decidable** (`Complexity.pUniformDecidable_stateLang`) and reduces to SAT in
  polynomial time (`Complexity.polyManyOne_SAT_stateLang`).
* `Start/UniformStateSubsume.lean` checks that the two earlier families really are instances: a
  finite automaton with `m` states becomes a poly-state automaton whose transition table and
  accepting set are finite, hence Cobham-computable by `Cob.tableSel`
  (`Complexity.pUniformDecidable_autoLang_of_state`), and a symmetric language becomes the counting
  automaton whose state is the number of `true` bits read so far, capped at the length of the input
  (`Complexity.pUniformDecidable_symLang_of_state`).
* `Start/UniformStateInst.lean` exercises the rule on a language that is neither regular nor
  symmetric: the words whose binary value, most significant bit first, is divisible by their length
  plus one (`Complexity.BinDivLang`).  The automaton keeps the value read so far modulo `n + 1`, so
  it has `n + 1` states; `Complexity.stateLang_binDelta` identifies its language,
  `Complexity.stateUniform_bin` supplies the Cobham terms, and
  `Complexity.pUniformDecidable_binDiv`, `Complexity.polyManyOne_SAT_binDiv` conclude.

### The Cook–Levin tableau: cellular automata

The rules above all compile *one-way* devices: the circuit follows a single left-to-right scan of
the input.  `Start/UniformCA.lean` and `Start/UniformCACode.lean` compile the device Cook–Levin
really rests on, a **cellular automaton** over a fixed finite alphabet run for polynomially many
steps on a tape of polynomial length.  The circuit is the *tableau*, the space–time diagram of the
computation, so information flows in both directions and every cell is revisited at every step.

* `Complexity.CellAuto` is a cellular automaton: `K` symbols, a blank carried outside the tape, the
  initial contents of a cell from its input bit and a first-cell flag, a local rule `stp a b c`
  reading a cell and its two neighbours, and a set of accepting symbols.
  `Complexity.CircCode.caCell` is the contents of a cell at a given time.
* `Start/UniformCA.lean` lays out the tableau as a grid of width `W`, one column per tape cell.
  Row `0` is the constant `false`, row `1` the constant `true`, row `2` holds the input bit of the
  column, and the next `K` rows hold the one-hot encoding of the initial tape.  Each step of the
  automaton is a block of `caHb K` rows: for every triple `(a, b, c)` of symbols two conjunction
  rows compute `prev_a[j-1] ∧ prev_b[j] ∧ prev_c[j+1]`, and for every target symbol an accumulator
  runs through the triples, collecting those whose local rule gives that symbol.  Because the
  alphabet is fixed, a block has constant height.  `Complexity.CircCode.wf_caGrid` proves the
  tableau is a well-formed circuit, `Complexity.CircCode.lval_ca_state` that **its one-hot bits
  record the contents of the tape**, and `Complexity.CircCode.out_caGrid` that **the output gate is
  the verdict of the automaton**.
* `Start/UniformCACode.lean` writes the description of the tableau with a single Cobham term.
  Every gate is determined by simple arithmetic on its row and column: the index of the block is a
  Euclidean division in unary, and the phase inside the block selects from a finite table
  (`Cob.tableSel`) whose entries are computed at the meta level from the local rule.
  `Complexity.CircCode.caBlkT` is the term, `Complexity.CircCode.eval_caBlkT` proves it writes
  exactly the gates, `Complexity.CircCode.length_encGate_caT` bounds their size, and the grid rule
  `Complexity.codeUniform_gridLayer` concludes that the family is P-uniform
  (`Complexity.codeUniform_caGrid`).  Hence **the language of a cellular automaton whose tape width
  and running time are computed in unary by Cobham terms is P-uniformly decidable**
  (`Complexity.pUniformDecidable_caLang`) and reduces to SAT in polynomial time
  (`Complexity.polyManyOne_SAT_caLang`).
* `Start/UniformCAInst.lean` exercises the rule on the spreading automaton, whose local rule is the
  disjunction of a cell and its two neighbours: `Complexity.caCell_orCA` identifies the contents of
  a cell with the disjunction of the window it can see, `Complexity.caLang_orCA_eq_someOne`
  identifies its language with `Complexity.SomeOne`, and
  `Complexity.pUniformDecidable_someOne_of_ca` re-derives that language through the tableau.

### Turing machines through the tableau

`Start/UniformTM.lean` runs the standard sequential device on the tableau.  A
`Complexity.TuringMachine` is a one-tape deterministic machine over the alphabet `Bool` with `Q`
states and an arbitrary transition table `st`, `wr`, `mv`, `acc` — no computability assumption is
placed on the table, only that the number of states is finite.

* `Complexity.tmCA` is the simulating cellular automaton.  Its alphabet has `3 + 2 * Q` symbols:
  the accept symbol `0`, the two headless bits `Complexity.tmN`, and the two head symbols
  `Complexity.tmH s` for each state `s`.  The local rule `Complexity.tmStp` lets the accept symbol
  travel leftwards, turns an accepting head into the accept symbol, and otherwise writes the bit
  the local head asks for and receives the head of whichever neighbour is moving onto the cell.
* `Complexity.tmConf` is the configuration of the machine after `t` steps on a tape of `W` cells:
  the head position `W` means the head has walked off the tape and the machine is dead, and the
  machine freezes as soon as it enters an accepting state.  `Complexity.tmZero` says that the
  accept signal, created one step after an accepting configuration and travelling one cell per
  step to the left, has reached a given cell.
* `Complexity.caCell_tmCA_aux` is the simulation theorem, proved by a single induction on time:
  every cell of the tableau carries the accept symbol once the signal has reached it, and the
  symbol of the machine's configuration before that (`Complexity.caCell_tmCA_eq`,
  `Complexity.caCell_tmCA_zero_iff`).  In particular the first cell of the tableau carries the
  accept symbol at the deadline exactly when the machine accepts in time
  (`Complexity.caCell_tmCA_zero_iff_accBy`).
* Acceptance in time, `Complexity.tmAccBy`, is sandwiched between the two natural notions by
  `Complexity.tmAccBy_of_acc_le` (an accepting configuration reached within `T` steps is counted
  as accepting for every deadline `H ≥ 2 * T + 1`, since the head is then at most `T` cells away)
  and `Complexity.acc_lt_of_tmAccBy` (a machine counted as accepting within `H` does reach an
  accepting configuration before `H`).
* Hence **the language of a one-tape deterministic Turing machine whose tape width and running
  time are computed in unary by Cobham terms is P-uniformly decidable**
  (`Complexity.pUniformDecidable_tmLang`) and reduces to SAT in polynomial time
  (`Complexity.polyManyOne_SAT_tmLang`).
* `Start/UniformTMInst.lean` exercises the rule on the scanning machine, which walks to the right
  and accepts as soon as it reads a `1`: `Complexity.tmAccBy_scanTM` identifies the inputs it
  accepts within the deadline `2 * n + 3`, `Complexity.tmLang_scanTM_eq_someOne` identifies its
  language with `Complexity.SomeOne`, and `Complexity.pUniformDecidable_someOne_of_tm` re-derives
  that language through a Turing machine.

## Unrolling a loop whose body is a circuit

`Start/UniformLayerPad.lean`, `Start/UniformSelect.lean`, `Start/UniformIterate.lean`.  The loop
rules above all write the gate with identifier `c` out of *arithmetic* on `c`.  A compiler that
unrolls a bounded recursion cannot: the body of its loop is the circuit compiled for the step of the
recursion, and each copy of that circuit reads the outputs of the copy below.  Three modules supply
that shape.

* **A longer parameter for the block-emitting recursion.**  The recursion of
  `Start/CobhamBlock.lean` bounds the block it emits by `K * (|suffix| + |parameter| + 1)`, and the
  layer and grid rules take the parameter to be `1^n`.  A circuit assembled out of blocks that are
  themselves circuits of polynomial size refers, from its very first gate, to gates whose
  identifiers are polynomial in `n`, so its tokens are *not* of length linear in `n`.
  `Complexity.CircCode.layerGenP` hands the recursion an arbitrary word `pw n`, written by a Cobham
  term, in place of `1^n`; `Complexity.codeUniform_layerP` and
  `Complexity.codeUniform_gridLayerP` are the layer and the grid rules for that parameter, a token
  having only to be of length linear in the identifier of its gate and in `|pw n|`.
* **Copying a gate off a description.**  `Complexity.CircCode.selTokTerm` is a Cobham term which,
  from the code of a circuit and from `1^o`, writes the token of the gate of that circuit whose
  identifier is `o` (`Complexity.CircCode.eval_selTokTerm_lt`).  It is the block-emitting recursion
  run over the code with the finite-state control of `Start/CircuitCode.lean`: at every marker the
  counter holds the identifier of the gate whose token starts there, so the recursion has only to
  compare that counter with `o` — a comparison of two words of ones — and to re-emit the token it is
  reading when they agree.  This is the first rule here that writes gates it is *given* rather than
  gates it computes.
* **The stack.**  `Complexity.Tseitin.iterC B D w k` stacks `k` copies of the stage `B` on top of
  the base `D`, the circuit inputs of every copy rewired to the topmost `w` gates of the stack below
  it.  `Complexity.Tseitin.wf_iterC` says it is well formed and `Complexity.Tseitin.state_iterC`
  that its topmost `w` gates carry the `k`-th iterate of the step function
  `Complexity.Tseitin.stepC` of the stage; `Complexity.Tseitin.out_iterC` and
  `Complexity.Tseitin.out_iterC_state` read its output off that state.
  **`Complexity.codeUniform_iterC` is the rule**: if the stage and the base are P-uniform families,
  the stage is well formed and reads only the `w n` wires it is given, and the number of copies and
  the width are computed in unary from `1^n`, then the stack is P-uniform.  The proof lays the stack
  out as a grid and applies `Complexity.codeUniform_gridLayerP` with the parameter
  `pw n = 1^n 0 1^{S n}`, `S n` being the size of the whole stack: the gate at row `i`, column `j`
  is the gate `j` of the stage, relocated by `Complexity.CircCode.rerouteTerm` applied to the token
  that `Complexity.CircCode.selTokTerm` copies off the description of the stage.

`Start/UniformIterLang.lean` packages the rule as a statement about *languages*:
`Complexity.pUniformDecidable_iterLang` says that a device whose configuration is a word of `w n`
wires, whose initial configuration is produced by a P-uniform family and whose one-step transition
is computed by a P-uniform family, decides — after a Cobham-computable number of steps, on the last
wire of its configuration — a P-uniformly decidable language, hence
(`Complexity.polyManyOne_SAT_iterLang`) one that reduces to SAT in polynomial time.

The rule is not vacuous.  `Start/UniformIterateInst.lean` runs it on a stage that really grows with
the instance: a shift register with an accumulator, of `n + 2` wires, whose stage shifts the
register down by one place and disjoins the bit that falls off into the accumulator
(`Complexity.CircCode.stateC_sreg`).  After `n` copies the accumulator — the topmost gate, hence the
output — holds the disjunction of all the bits of the input (`Complexity.CircCode.out_sregC`), so
`Complexity.codeUniform_sregC` and `Complexity.pUniformDecidable_someOne_of_iter` re-derive
`Complexity.SomeOne` through the iteration rule, and `Complexity.polyManyOne_SAT_someOne_of_iter`
reduces it to SAT.

## Walking a Cobham term: the compiler for a fragment

`Start/UniformPar.lean`, `Start/UniformSignal.lean`, `Start/UniformSigApp.lean`,
`Start/UniformSigComp.lean`, `Start/UniformSigBound.lean`, `Start/UniformSigCompile.lean`.  The
loop and stack rules above say how a description-writing program may *shape* a circuit.  A compiler
also has to walk a Cobham term, and for that it needs a circuit-level notion of a **word on wires**
and one rule per shape of term.

* **Words on wires.**  `Complexity.Tseitin.encSig m u` presents a word `u` on `2 * m` wires: `m`
  presence bits, the bit `j` saying that `u` has a `j`-th letter, followed by `m` value bits.
  `Complexity.Tseitin.encArgs m args` lays the signals of a list of words side by side, and is what
  the circuit inputs of a stage carry.  `Complexity.Tseitin.SigFam` — a P-uniform family whose
  topmost `2 * m n` gates carry the signal of the value of a word function of `r` arguments —
  and its existential form `Complexity.SigUniform` say that a family **realizes** that function.
* **Routing.**  `Complexity.Tseitin.wireLayer` copies gates of the circuit underneath, and
  `Complexity.Tseitin.parC B₁ B₂ w₁ w₂` runs two circuits on the same input and copies the topmost
  wires of both to the top of the result: `Complexity.Tseitin.topVals_parC` is its semantics and
  `Complexity.codeUniform_parC` its uniformity.  This is the shape that a composition
  `f(g₁(x), …, g_r(x))` asks for, since the values of the `gᵢ` have to be produced side by side.
* **The rules.**  `Complexity.sigUniform_empty` (a layer of constant gates),
  `Complexity.sigUniform_proj` (a layer of input gates reading the block of the argument named),
  `Complexity.sigUniform_app` (a layer that shifts both blocks of the signal by one place, the two
  wires freed being written by constants) and `Complexity.sigUniform_comp` (the parallel product of
  the inner families, with the family of the outer function rerouted on top of it) realize the four
  shapes.  `Complexity.sigUniform_of_flatLayer` is the general rule behind the first three: a layer
  of constant and input gates written by a Cobham term realizes the function its values describe.
* **The promise.**  A term such as `x ↦ b :: x` lengthens its argument, so a composition of such
  terms is correct only on arguments that leave room for the growth.
  `Complexity.Tseitin.SigFamB` and `Complexity.SigUniformB` therefore carry, beside the width `m`
  of the wires, the length `k` the arguments are promised not to exceed;
  `Complexity.sigUniformB_comp` is the composition rule, and it asks exactly that the values of the
  inner terms obey the promise made to the outer one.
* **The fragment.**  `Complexity.SigShape r v` is the fragment the four rules cover: a term of
  arity `r` built from projections of an argument that exists, the empty word, the successors, and
  composition.  Such a term lengthens its arguments by at most the constant
  `Complexity.addLen v` (`Complexity.length_eval_le_of_sigShape`), so
  `Complexity.sigUniformB_of_sigShape` compiles it at any width leaving room for that growth, and
  `Complexity.sigUniformB_of_sigShape_std` at the width `n + addLen v`, with no hypothesis at all:
  **every term of the fragment is realized by a P-uniform family of circuits.**

The two shapes still missing are `Cob.smash` and `Cob.bRec`.  A term using either of them is not
covered by `Complexity.SigShape`, and both would also force the width bookkeeping to become
polynomial rather than additive, since a smash multiplies lengths.

## The whole non-recursive fragment — `Start/UniformSigFlat.lean`

The smash of `Start/UniformSigSmash.lean` and the four rules above are put together here, so the
fragment the compiler covers becomes **every shape of Cobham term except the bounded recursion**
(`Complexity.FlatShape`).

Adding the smash changes the bookkeeping of the widths: a term of the earlier fragment lengthens
its arguments by a constant, whereas a smash multiplies two lengths, so the width has to be a
function of the promise rather than the promise plus a constant.  `Complexity.flatLen` is that
function — `flatLen v n` bounds the length of the value of `v` at arguments of length at most `n`
(`Complexity.length_eval_le_of_flatShape`), it is monotone in `n`, it dominates `n`, and, in the
case of a composition, it dominates the growth of each of the inner terms, which is what lets one
width serve the whole tree of subterms.

What makes such a width admissible is that it is itself Cobham-computable in unary:
`Complexity.exists_flatLenT` builds, by recursion on the term, a Cobham term writing
`1^{flatLen v n}` from any word of length `n`, out of the unary length `x ↦ 1^{|x|}`, prepending a
bit, the concatenation `Cob.catL` (for the sums) and the smash itself (for the products).

Hence `Complexity.sigUniformB_of_flatShape` — **every term of the non-recursive fragment is realized
by a P-uniform family of circuits**, at every width leaving room for its growth — and
`Complexity.sigUniformB_of_flatShape_std`, the same at the width `flatLen v` with no hypothesis at
all.  A term the earlier fragment cannot express, `x ↦ 1^{|x|²}`, is compiled as an example.

The only shape still missing is `Cob.bRec`.

## Bounded recursion, and the compiler for the whole Cobham algebra — `Start/UniformSigAll.lean`

`Complexity.cobLen v n` bounds the length of `v.eval args` when the arguments have length at most
`n`, the `bRec` case evaluating its subterms at the promise `brecProm`; `Complexity.exists_cobLenT`
writes `1^{cobLen v n}` by a Cobham term.  `Complexity.CobShape r v` is the arity discipline, now
including the recursion shape, and

```lean
theorem sigUniformB_of_cobShape_std {r : ℕ} {v : Cob} (h : CobShape r v) :
    SigUniformB r (cobLen v) (fun n => n) v.eval
```

compiles **every** well-formed Cobham term — the recursion included — into a P-uniform family of
circuits reading and writing the signal format, at the width given by the growth of the term
itself.

`Start/UniformSigNorm.lean` removes the well-formedness proviso: `Complexity.shapeAt r v`
normalizes an arbitrary term into a `CobShape r`-term with the same values on argument lists of
length `r` (`Complexity.cobShape_shapeAt`, `Complexity.eval_shapeAt`).

## Every language in `P` is P-uniformly decidable — `Start/UniformSigLang.lean`

`Complexity.Tseitin.sigInC` decodes a *pinned* circuit input into a signal and
`Complexity.Tseitin.decideSigC` reads the verdict off the first presence wire of the value signal,
giving `Complexity.pUniformDecidable_of_cobShape` and, after normalization,

```lean
theorem pUniformDecidable_of_inP {L : Language} (h : InP L) : PUniformDecidable L
theorem polyManyOne_SAT_of_inP_viaCircuits {L : Language} (h : InP L) : L ≤ₘᵖ Sat.SAT
```

so the class of P-uniformly decidable languages is now all of `P`.

## The general decoder, and Cook–Levin — `Start/UniformSegDec.lean`, `Start/CookLevinNPHard.lean`

The acceptance circuits of the residual hypothesis are fed an *arbitrary* input, off which two
words are read, so their presence bits are no longer constants.  `Complexity.Tseitin.segDec off N`
decodes a segment of such an input: the flags of the segment, their running conjunctions — a
rerouted copy of `Complexity.CircCode.andCirc` — the bits of the segment, and the value bits, its
wires `[2N, 3N)` and `[4N, 5N)` carrying the presence and the value bits of
`Complexity.Tseitin.inWordAt off N` (`Complexity.Tseitin.getD_vals_segDec_pres`,
`Complexity.Tseitin.getD_vals_segDec_val`).  `Complexity.Tseitin.sigBlock` pads those two blocks
into the signal format, and all of it is P-uniform (`Complexity.codeUniform_segDec`,
`Complexity.codeUniform_sigBlock`), on top of a layer of pointwise conjunctions
(`Complexity.codeUniform_conj2Layer`), a reindexing rule (`Complexity.codeUniform_reindex`) and the
closure of unary-computable length functions under products and truncated differences
(`Complexity.UnaryLen.mul`, `Complexity.UnaryLen.sub`, `Complexity.unaryLen_poly`).

`Complexity.Tseitin.pairDec` puts two segment decoders side by side — the instance at the input
positions `[0, 2n)`, the witness at `[2n, 2n + 2p(n))` — and stacks the two signals on top
(`Complexity.Tseitin.vals_pairDec`).  `Complexity.Tseitin.decideSigE` runs the compiled verifier on
those signals, reading them off the decoder from a fixed wire upwards, and puts the verdict gate on
top.  This proves the residual hypothesis, and with it the theorem:

```lean
theorem stdUniformAcceptFamilies : StdUniformAcceptFamilies
theorem npHard_SAT : NPHard Sat.SAT
theorem npComplete_SAT : NPComplete Sat.SAT
theorem peqNP_iff_inP_SAT : PeqNP ↔ InP Sat.SAT
```

All three exit criteria are therefore met unconditionally: formulas are a language over binary
words, SAT is in `NP`, and every language in `NP` reduces to SAT in polynomial time.

## Boundary

* Nothing above is conditional: `Complexity.npComplete_SAT` depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
* Cobham's theorem (that `Cob` is exactly polynomial-time Turing computability) remains
  unformalized, as recorded in `M9-COMPLEXITY-CLASSES`; nothing here depends on it.  `NP` and `P`
  are the Cobham-verifier and Cobham-decider classes throughout.

## Boundary (historical, superseded by the sections above)

The bullets below record the state of the development before the compiler and the general decoder
were built; they are kept for the history of the milestone and are no longer accurate.


* **P-uniformity is not formalized.**  The compilation of a Cobham verifier into a polynomial-size
  circuit *is* formalized (`Complexity.Tseitin.exists_npCircuitFamily`,
  `Complexity.Tseitin.exists_pinAcceptCircuit`), but only as an existence statement: the circuits
  are obtained by chaining existence lemmas, so no explicit function from the length `n` to the
  circuit is defined, and nothing says that the description of the `n`-th circuit is computed from
  `1^n` by a Cobham term.  The *second* half of what used to be missing is now supplied: given the
  description, the code of its Tseitin translation is computed by an explicit Cobham term
  (`Complexity.CircCode.eval_tseitinTerm`), so the residual hypothesis is exactly the standard
  P-uniformity of the circuit family (`Complexity.CodeUniform`).  Closing it would require turning
  the chain of existence lemmas of `Start/CircuitBuild.lean`, `Start/WordCircuit.lean`,
  `Start/CobhamCircuit.lean` and `Start/CobhamBRec.lean` into an explicit compiler — a function
  from a Cobham term and a length to a circuit — and then proving that this function is itself
  computed by a Cobham term on the codes.  The loop rules above are the missing structural
  ingredients of such a compiler — a description-writing program may now loop over blocks of a
  fixed or of a growing size — but the compiler itself is not built.  The sections above build the
  compiler for the whole *non-recursive* fragment of the Cobham algebra — the projections, the
  empty word, the successors, the smash and composition
  (`Complexity.sigUniformB_of_flatShape`, `Complexity.sigUniformB_of_flatShape_std`); the shape
  `Cob.bRec` is not compiled, so an arbitrary Cobham term still cannot be turned into a stage
  circuit together with a number of copies.
* Consequently `NPHard` is still not known to be inhabited, and `PeqNP` is neither proved nor
  refuted.
* The precise statement that remains open is `Complexity.StdUniformAcceptFamilies`.  Both the
  universally quantified variants and the earlier existential form
  `Complexity.PUniformAcceptFamilies` are *refuted* here, so a proof must **construct** the family,
  for a witness bound that is a genuine polynomial.
* The class of languages known unconditionally to be P-uniformly decidable now contains every
  regular language (`Complexity.pUniformDecidable_autoLang`), is closed under the Boolean
  operations, and contains every symmetric language with a Cobham-decidable count predicate
  (`Complexity.pUniformDecidable_symLang`), among them non-regular ones
  (`Complexity.pUniformDecidable_maj`, `Complexity.maj_ne_autoLang`,
  `Complexity.pUniformDecidable_exactHalf`, `Complexity.exactHalf_ne_autoLang`).  It is still very
  far from all
  of `P`, let alone from the acceptance families of arbitrary NP verifiers: each of these families
  is built by hand, and no general compiler produces one from a Cobham term.
* The class of languages known unconditionally to be P-uniformly decidable now also contains the
  language of every automaton with polynomially many states whose data is Cobham-computable in
  unary (`Complexity.pUniformDecidable_stateLang`), which subsumes both the finite-automaton and
  the symmetric-language families; `Complexity.pUniformDecidable_binDiv` is an instance that is
  neither regular nor symmetric.  This is still very far from all of `P`: the number of states is
  polynomial, the machine is one-way and it never revisits a bit.
* The class of languages known unconditionally to be P-uniformly decidable now also contains the
  language of every cellular automaton over a fixed finite alphabet whose tape width and running
  time are Cobham-computable in unary (`Complexity.pUniformDecidable_caLang`).  This is the first
  rule here that compiles a *two-way* device, and it is the Cook–Levin tableau proper.  What it
  does not supply is the last compiler: nothing here turns an arbitrary Cobham term into a
  cellular automaton (or into a Turing machine and then into one), so no language is known to be
  P-uniformly decidable merely from being in `P`.
* The class of languages known unconditionally to be P-uniformly decidable now also contains the
  language of every one-tape deterministic Turing machine with finitely many states whose tape
  width and running time are Cobham-computable in unary
  (`Complexity.pUniformDecidable_tmLang`), with no computability assumption on the transition
  table.  This removes the restriction to a fixed alphabet of hand-built automata: the device is
  now the standard one.  What is still missing is exactly the compiler in the other direction —
  nothing here turns an arbitrary Cobham term into such a machine (that is Cobham's theorem, plus
  the choice of a tape bound), so a language is still not known to be P-uniformly decidable merely
  from being in `P`.
* The loop rules now include one whose body is a P-uniform *family* rather than a pattern of gates
  (`Complexity.codeUniform_iterC`), which is the shape the unrolling of a bounded recursion has,
  together with a Cobham term that copies a gate off a description
  (`Complexity.CircCode.selTokTerm`) and the padded layer and grid rules that make the long tokens
  of such a stack admissible (`Complexity.codeUniform_layerP`,
  `Complexity.codeUniform_gridLayerP`).  What is still missing is what chooses the stage: nothing
  here turns a Cobham term into a stage circuit together with a number of copies, so the compiler is
  still not built and `NPHard` is still not known to be inhabited.
* Cobham's theorem (that `Cob` is exactly polynomial-time Turing computability) remains
  unformalized, as recorded in `M9-COMPLEXITY-CLASSES`; nothing here depends on it.
