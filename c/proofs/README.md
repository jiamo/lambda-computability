# proofs/

The verification (rounds 1 and 2) is carried out by Aristotle as machine-checked proofs about the
C code in `src/` (the code itself, not a hand-written model of it), against the reference
semantics of `spec/CTSpec.lean` (round 1) and of the definitions of `Start/` named in
`../PROOFS.md` (round 2).

**The proofs cannot be exported.** Aristotle keeps the formal encoding of C programs, the Lean
statements written over that encoding, and the proofs built on it internal. This directory
therefore contains neither the formal model of the C code nor the proofs, and the requested
`proofs/<module>/` directories are not provided. For the same reason, the exact Lean statements of
the properties cannot be placed in `proofs/statements/`: they are written over the internal
encoding of C programs.

What is delivered instead:

- `../PROOFS.md` gives, for every property of rounds 1 and 2, its precise statement in prose
  (inputs, caller obligations, the result on `CT_OK`, the behavior on errors), its status
  (**proved** / **refuted** / **open**) and its artifact. Each property marked **proved** has a
  complete machine-checked proof, with no unproved step, under exactly the assumptions listed in
  that file.
- The Lean definitions those statements refer to are those of `../spec/CTSpec.lean` (round 1)
  and the definitions of the repository's `Start/` modules named in each round-2 entry. The
  round-2 restatement of those definitions is kept internal, like the proofs.
