/-
**Bridge: the simply typed λ-calculus in realizability** — milestone M31 (`M31-BRIDGE-STLC`).

`Start/CccModel.lean` interprets the simply typed λ-calculus (`Start/Stlc.lean`, with its
syntactic category `Start/StlcCcc.lean` and normalization by evaluation
`Start/StlcNbE.lean`, `Start/StlcNbEComplete.lean`) in every cartesian closed category.
`Start/AssemblyCcc.lean` proves that the assemblies over a PCA form one.  This module puts the
two together.

* `Stlc.asmTm` — **the realizability interpretation**: over any PCA, with any assembly for the
  base type, a term `Γ ⊢ t : B` is a morphism of assemblies `⟦Γ⟧ ⟶ ⟦B⟧`;
* `Stlc.asmTm_tracked` — so its underlying function is **tracked**: one element of the algebra
  computes it on realizers;
* `Stlc.asmTm_conv` — **soundness**: βη-convertible terms have the same interpretation;
* `Stlc.asmTm_nf` — a term and its normal form by evaluation have the same interpretation.
-/

import Start.CccModel
import Start.AssemblyCcc
import Start.StlcNbEComplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Stlc

open CategoryTheory Realizability

universe u v

variable {A : Type u} [PCA A]

/-- **The realizability interpretation** of a simply typed term over a PCA. -/
noncomputable def asmTm (S : Assembly.{u, v} A) {Γ : Ctx} {B : Ty} (t : Tm Γ B) :
    ctxObj S Γ ⟶ tyObj S B :=
  tmMor S t

/-- The interpretation of a term is tracked by an element of the algebra. -/
theorem asmTm_tracked (S : Assembly.{u, v} A) {Γ : Ctx} {B : Ty} (t : Tm Γ B) :
    Assembly.Tracked (ctxObj S Γ) (tyObj S B) (asmTm S t).toFun :=
  (asmTm S t).tracked

/-- **Soundness of the realizability interpretation**: convertible terms are interpreted by the
same morphism of assemblies. -/
theorem asmTm_conv (S : Assembly.{u, v} A) {Γ : Ctx} {B : Ty} {t u : Tm Γ B} (h : Conv t u) :
    asmTm S t = asmTm S u :=
  tmMor_conv S h

/-- A term and its normal form by evaluation have the same interpretation. -/
theorem asmTm_nf (S : Assembly.{u, v} A) {Γ : Ctx} {B : Ty} (t : Tm Γ B) :
    asmTm S t = asmTm S (StlcNbE.nf t) :=
  asmTm_conv S (StlcNbE.nf_sound t)

end Stlc
