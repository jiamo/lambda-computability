# M23-HURKENS — System U⁻ is inconsistent

**Status:** DONE_STRONG.

`Start/PTSHurkens.lean` (this library's own, on the absorbed PTS framework):

* `Hurkens.USort` (`∗ □ △`), `Hurkens.uMinus` — the sorts, axioms `∗ : □`, `□ : △` and rules
  `(∗,∗) (□,∗) (□,□) (△,□)` of System U⁻ as a `Specification`.
* `Hurkens.hurkens` — Hurkens' term, built from named syntax and compiled to de Bruijn form.
* `Hurkens.hurkens_typed : HasType uMinus ([]) hurkens botE` with
  `botE = Π A : ∗. A` — checked by the verified inference procedure (`Check.infer_sound`) and a
  kernel `decide`; the target type is not assumed.
* `no_normal_closed_bot` — in *every* PTS no normal closed term has type `Π A : s. A`.
* `Hurkens.uMinus_inconsistent` — every closed type of sort `∗` is inhabited.
* `Hurkens.hurkens_not_weaklyNormalizing`, `Hurkens.uMinus_not_wn`, `Hurkens.uMinus_not_sn` —
  hence U⁻ is neither weakly nor strongly normalizing.

This is an object-theory statement about derivations of U⁻; nothing is concluded in Lean's
metatheory.  Classical: Girard's paradox, Hurkens' 1995 simplification.  New here: the checked
encoding in the PTS framework and the precise failure of normalization.
