/-
Kleene's first partial combinatory algebra `K₁`.

The natural numbers with **Turing application** `a · b = φ_a(b)` — run the `a`-th partial
recursive code on the input `b` — form a partial combinatory algebra.  This is the algebra whose
realizability interpretation is *recursive* realizability; it is the reason PCAs are the right
setting for the effective topos.

The two combinators are produced by the s-m-n theorem, in mathlib's form
`Nat.Partrec.Code.curry`:

* `Realizability.Kleene.natApp` — Turing application, `eval (ofNat Code a) b`;
* `Realizability.Kleene.kEl`, `.sEl` — the combinators, obtained by currying a code for the left
  projection resp. a code for the universal "apply twice" function;
* `Realizability.Kleene.instPCANat` — the resulting `PCA ℕ` (scoped instance);
* `Realizability.Kleene.k1_app` — the application of the algebra *is* Turing application.

Non-totality is essential here: `natApp a b` diverges whenever the `a`-th machine diverges at
`b`, so `K₁` is a genuinely partial combinatory algebra.
-/

import Start.PCA
import Mathlib.Computability.PartrecCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

namespace Kleene

open Nat.Partrec (Code)
open Nat.Partrec.Code
open Encodable Denumerable

/-- **Turing application**: `natApp a b` is the result of running the `a`-th partial recursive
code on the input `b`. -/
def natApp (a b : ℕ) : Part ℕ := eval (ofNat Code a) b

@[simp] theorem natApp_encode (c : Code) (b : ℕ) : natApp (encode c) b = eval c b := by
  rw [natApp, Denumerable.ofNat_encode]

theorem partrec_natApp : Partrec₂ natApp :=
  Partrec₂.comp (f := fun (c : Code) (n : ℕ) => eval c n) eval_part
    ((Computable.ofNat Code).comp Computable.fst) Computable.snd

/-- Every computable function is `eval` of some code. -/
theorem exists_code_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, ∀ n, eval c n = Part.some (f n) := by
  obtain ⟨c, hc⟩ := exists_code.1 (Partrec.nat_iff.1 hf.partrec)
  exact ⟨c, fun n => by rw [hc]; rfl⟩

/-! ### The combinator `k` -/

/-- `k a` is a code for the constant function with value `a`: curry the left projection. -/
def kFun (a : ℕ) : ℕ := encode (curry Code.left a)

theorem computable_kFun : Computable kFun :=
  Computable.encode.comp
    (Computable₂.comp (f := curry) (Primrec₂.to_comp primrec₂_curry)
      (Computable.const Code.left) Computable.id)

/-- A code computing `kFun`. -/
noncomputable def kCode : Code := (exists_code_of_computable computable_kFun).choose

theorem eval_kCode (a : ℕ) : eval kCode a = Part.some (kFun a) :=
  (exists_code_of_computable computable_kFun).choose_spec a

/-- The combinator `k` of `K₁`. -/
noncomputable def kEl : ℕ := encode kCode

theorem natApp_kEl (a : ℕ) : natApp kEl a = Part.some (kFun a) := by
  rw [kEl, natApp_encode, eval_kCode]

theorem natApp_kFun (a b : ℕ) : natApp (kFun a) b = Part.some a := by
  rw [kFun, natApp_encode, eval_curry]
  change (Part.some (Nat.unpair (Nat.pair a b)).1 : Part ℕ) = Part.some a
  simp

/-! ### The combinator `s` -/

/-- The "apply twice" function `⟨a, b, c⟩ ↦ (a c) (b c)`, which the third argument of `s`
triggers. -/
def sBody (n : ℕ) : Part ℕ :=
  (natApp n.unpair.1 n.unpair.2.unpair.2).bind fun u =>
    (natApp n.unpair.2.unpair.1 n.unpair.2.unpair.2).bind fun v => natApp u v

theorem partrec_sBody : Partrec sBody := by
  have hu1 : Computable fun n : ℕ => n.unpair.1 := (Primrec.fst.comp Primrec.unpair).to_comp
  have hu21 : Computable fun n : ℕ => n.unpair.2.unpair.1 :=
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hu22 : Computable fun n : ℕ => n.unpair.2.unpair.2 :=
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp
  have hF : Partrec fun n : ℕ => natApp n.unpair.1 n.unpair.2.unpair.2 :=
    Partrec₂.comp (f := natApp) partrec_natApp hu1 hu22
  have hG : Partrec fun n : ℕ => natApp n.unpair.2.unpair.1 n.unpair.2.unpair.2 :=
    Partrec₂.comp (f := natApp) partrec_natApp hu21 hu22
  have hinner : Partrec₂ fun (n u : ℕ) =>
      (natApp n.unpair.2.unpair.1 n.unpair.2.unpair.2).bind fun v => natApp u v := by
    refine Partrec.bind (hG.comp Computable.fst) ?_
    exact Partrec₂.comp (f := natApp) partrec_natApp (Computable.snd.comp Computable.fst)
      Computable.snd
  exact Partrec.bind hF hinner

/-- A code computing `sBody`. -/
noncomputable def sCode : Code := (exists_code.1 (Partrec.nat_iff.1 partrec_sBody)).choose

theorem eval_sCode : eval sCode = sBody :=
  (exists_code.1 (Partrec.nat_iff.1 partrec_sBody)).choose_spec

/-- `s a b`, the second stage. -/
noncomputable def sTwo (a b : ℕ) : ℕ := encode (curry (curry sCode a) b)

theorem computable_sTwo : Computable fun n : ℕ => sTwo n.unpair.1 n.unpair.2 := by
  have hcurry : Computable₂ curry := Primrec₂.to_comp primrec₂_curry
  have h1 : Computable fun n : ℕ => curry sCode n.unpair.1 :=
    Computable₂.comp (f := curry) hcurry (Computable.const sCode)
      ((Primrec.fst.comp Primrec.unpair).to_comp)
  have h2 : Computable fun n : ℕ => curry (curry sCode n.unpair.1) n.unpair.2 :=
    Computable₂.comp (f := curry) hcurry h1 ((Primrec.snd.comp Primrec.unpair).to_comp)
  exact Computable.encode.comp h2

/-- A code computing the pairing of `sTwo`. -/
noncomputable def sPairCode : Code := (exists_code_of_computable computable_sTwo).choose

theorem eval_sPairCode (n : ℕ) : eval sPairCode n = Part.some (sTwo n.unpair.1 n.unpair.2) :=
  (exists_code_of_computable computable_sTwo).choose_spec n

/-- `s a`, the first stage. -/
noncomputable def sOne (a : ℕ) : ℕ := encode (curry sPairCode a)

theorem computable_sOne : Computable sOne :=
  Computable.encode.comp
    (Computable₂.comp (f := curry) (Primrec₂.to_comp primrec₂_curry)
      (Computable.const sPairCode) Computable.id)

/-- A code computing `sOne`. -/
noncomputable def sOneCode : Code := (exists_code_of_computable computable_sOne).choose

theorem eval_sOneCode (a : ℕ) : eval sOneCode a = Part.some (sOne a) :=
  (exists_code_of_computable computable_sOne).choose_spec a

/-- The combinator `s` of `K₁`. -/
noncomputable def sEl : ℕ := encode sOneCode

theorem natApp_sEl (a : ℕ) : natApp sEl a = Part.some (sOne a) := by
  rw [sEl, natApp_encode, eval_sOneCode]

theorem natApp_sOne (a b : ℕ) : natApp (sOne a) b = Part.some (sTwo a b) := by
  rw [sOne, natApp_encode, eval_curry, eval_sPairCode]
  simp

theorem natApp_sTwo (a b c : ℕ) :
    natApp (sTwo a b) c
      = (natApp a c).bind fun u => (natApp b c).bind fun v => natApp u v := by
  rw [sTwo, natApp_encode, eval_curry, eval_curry, eval_sCode]
  simp [sBody]

/-! ### The algebra -/

/-- **Kleene's first algebra** `K₁`: the natural numbers under Turing application. -/
noncomputable scoped instance instPCANat : PCA ℕ where
  app := natApp
  k := kEl
  s := sEl
  k_dom a := by rw [natApp_kEl]; trivial
  k_app a b := by rw [natApp_kEl, Part.bind_some, natApp_kFun]
  s_dom a b := by rw [natApp_sEl, Part.bind_some, natApp_sOne]; trivial
  s_app a b c := by
    rw [natApp_sEl, Part.bind_some, natApp_sOne, Part.bind_some, natApp_sTwo]

theorem k1_app (a b : ℕ) : PCA.app a b = natApp a b := rfl

end Kleene

end Realizability
