# M15-TIME-HIERARCHY-REL

## Big round 2, run 8

Started, design only. The run 8 sandbox had no Lean toolchain, so nothing was built or type-checked.

Started in big round 2, run 8 (W6), design only (no Lean toolchain in run 8, nothing type-checked). The oracle classes of M15-ORACLE-CLASSES (Start/OracleClasses.lean: InP_rel A L := ∃ t : CobQ, ∀ x, (L x ↔ CobQ.eval A t [x] ≠ [])) are Cobham-style and carry no time function, so the hierarchy cannot be stated on them. First missing definition: a time-bounded oracle class, e.g. def Complexity.DTIME_rel (A : Oracle) (t : ℕ → ℕ) (L : Language) : Prop on an oracle Turing machine with a query tape and a step count, with InP_rel A L ↔ ∃ k, DTIME_rel A (fun n => n ^ k + k) L as the link; then the universal oracle machine with an O(t log t) simulation overhead, and theorem Complexity.dtime_rel_hierarchy (A : Oracle) {f g : ℕ → ℕ} (hg : TimeConstructible g) (hfg : f = o(g / log g)) : ∃ L, DTIME_rel A g L ∧ ¬ DTIME_rel A f L.
