# proofs/

The verification of round 1 was carried out by Aristotle as machine-checked proofs about the C
code in `src/` (the code itself, not a hand-written model of it), against the reference
semantics of `spec/CTSpec.lean`.

The proof artifacts themselves are not included in this directory: Aristotle keeps the formal
encoding of C programs and the proofs built on it internal. What is delivered instead is the
precise statement and status of every property, in `../PROOFS.md`; each property marked
**proved** there has a complete machine-checked proof, with no unproved step, under exactly the
assumptions listed in that file.
