/-
**Bridge: the λ core as a combinatory algebra, compared with Kleene's first algebra** —
milestone M31 (`M31-FOUND-REALIZABILITY`).

The realizability development (`Start/PCA.lean`, `Start/Assembly*.lean`, …) works over an
abstract partial combinatory algebra.  Its instances so far are Kleene's first algebra on codes of
partial recursive functions (`Start/PCAKleene.lean`) and the algebras of abstract λ-models
(`Start/PCATotal.lean`).  This module builds the term model of the λ core itself and compares the
realizability it gives with Kleene's.

* `Realizability.TermModel.LTerm` — λ-terms modulo β-convertibility (`Relation.EqvGen
  Lambda.step`); **`Realizability.TermModel.instTCA`** — with application of terms and the
  combinators `Lambda.K`, `Lambda.S` it is a total combinatory algebra (`K a b ↠ a`,
  `S a b c ↠ a c (b c)`), hence a PCA;
* `Realizability.TermModel.conv_common` — convertible terms have a common reduct (Church–Rosser,
  `Lambda.confluence_theorem`), so conversion to a Church numeral is reduction to it;
* `Realizability.natAsm` — the natural numbers as an assembly over any PCA, from a choice of
  realizers (Church numerals in the term model, the numbers themselves in Kleene's algebra);
* **`Realizability.TermModel.tracked_iff_computable`**, **`Realizability.Kleene.tracked_iff_computable`**
  — a function `ℕ → ℕ` is a morphism of the natural-number assemblies over the λ term model iff
  it is computable, iff it is one over Kleene's first algebra;
  **`Realizability.tracked_termModel_iff_kleene`** — the two realizability models have the same
  arithmetic functions.
-/

import Start.PCATotal
import Start.PCAKleene
import Start.Assembly
import Start.PartrecLambda
import Start.EvalSound
import Start.Arithmetic

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Realizability

/-- The natural numbers as an assembly over a PCA: `num n` is the realizer of `n`. -/
def natAsm {A : Type} [PCA A] (num : ℕ → A) : Assembly.{0, 0} A where
  carrier := ℕ
  realizes a n := a = num n
  exists_realizer n := ⟨num n, rfl⟩

namespace TermModel

/-- β-convertibility. -/
def conv : Lambda → Lambda → Prop := Relation.EqvGen Lambda.step

/-- β-convertibility as a setoid. -/
@[instance_reducible]
def betaSetoid : Setoid Lambda := ⟨conv, Relation.EqvGen.is_equivalence _⟩

attribute [local instance] betaSetoid

/-- **The term model**: λ-terms modulo β-convertibility. -/
abbrev LTerm : Type := Quotient betaSetoid

theorem conv_map {f : Lambda → Lambda} (hf : ∀ a b, Lambda.step a b → Lambda.step (f a) (f b))
    {a b : Lambda} (h : conv a b) : conv (f a) (f b) := by
  induction h with
  | rel x y hxy => exact .rel _ _ (hf _ _ hxy)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

theorem conv_of_reduces {a b : Lambda} (h : Lambda.reduces a b) : conv a b := by
  induction h with
  | refl => exact .refl _
  | step _ _ _ hs _ ih => exact .trans _ _ _ (.rel _ _ hs) ih

/-- **Church–Rosser**: convertible terms have a common reduct. -/
theorem conv_common {a b : Lambda} (h : conv a b) : ∃ u, Lambda.reduces a u ∧ Lambda.reduces b u := by
  induction h with
  | rel x y hxy => exact ⟨y, .step _ _ _ hxy (.refl _), .refl _⟩
  | refl x => exact ⟨x, .refl _, .refl _⟩
  | symm _ _ _ ih =>
      obtain ⟨u, h1, h2⟩ := ih
      exact ⟨u, h2, h1⟩
  | trans _ _ _ _ _ ih1 ih2 =>
      obtain ⟨u1, hx, hy1⟩ := ih1
      obtain ⟨u2, hy2, hz⟩ := ih2
      obtain ⟨w, h1, h2⟩ := Lambda.confluence_theorem hy1 hy2
      exact ⟨w, Lambda.reduces_trans hx h1, Lambda.reduces_trans hz h2⟩

theorem reduces_normal_eq {t u : Lambda} (h : Lambda.reduces t u) (hn : Lambda.is_normal t) :
    u = t := by
  cases h with
  | refl => rfl
  | step _ t₂ _ hs _ => exact absurd hs (hn t₂)

/-- A term convertible to a normal form reduces to it. -/
theorem reduces_of_conv_normal {a b : Lambda} (h : conv a b) (hn : Lambda.is_normal b) :
    Lambda.reduces a b := by
  obtain ⟨u, ha, hb⟩ := conv_common h
  rw [reduces_normal_eq hb hn] at ha
  exact ha

/-- Application of the term model. -/
def tapp (x y : LTerm) : LTerm :=
  Quotient.lift₂ (fun a b => (⟦Lambda.app a b⟧ : LTerm))
    (fun a b a' b' (ha : conv a a') (hb : conv b b') => Quotient.sound
      (show conv (Lambda.app a b) (Lambda.app a' b') from
        .trans _ _ _ (conv_map (fun _ _ h => Lambda.step.app_left _ _ _ h) ha)
          (conv_map (fun _ _ h => Lambda.step.app_right _ _ _ h) hb))) x y

theorem K_reduces (a b : Lambda) : Lambda.reduces (.app (.app Lambda.K a) b) a := by
  have h1 : Lambda.step (.app Lambda.K a) (.lam (Lambda.lift 1 0 a)) := by
    have := Lambda.step.beta (.lam (.var 1)) a
    simpa [Lambda.K, Lambda.subst] using this
  refine .step _ _ _ (.app_left _ _ _ h1) (.step _ _ _ (.beta _ _) ?_)
  rw [Lambda.subst_lift]
  exact .refl _

theorem S_reduces (a b c : Lambda) :
    Lambda.reduces (.app (.app (.app Lambda.S a) b) c) (.app (.app a c) (.app b c)) := by
  have h1 : Lambda.step (.app Lambda.S a) (.lam (.lam (.app (.app
      (Lambda.lift 1 0 (Lambda.lift 1 0 a)) (.var 0)) (.app (.var 1) (.var 0))))) := by
    have := Lambda.step.beta (.lam (.lam (.app (.app (.var 2) (.var 0))
      (.app (.var 1) (.var 0))))) a
    simpa [Lambda.S, Lambda.subst] using this
  have e : Lambda.subst (Lambda.lift 1 0 b) 1 (Lambda.lift 1 0 (Lambda.lift 1 0 a)) =
      Lambda.lift 1 0 a := by
    rw [Lambda.lift_lift a 1 1 0 0 (le_refl 0), Nat.zero_add, Lambda.subst_lift]
  have h2 : Lambda.step (.app (.lam (.lam (.app (.app
      (Lambda.lift 1 0 (Lambda.lift 1 0 a)) (.var 0)) (.app (.var 1) (.var 0))))) b)
      (.lam (.app (.app (Lambda.lift 1 0 a) (.var 0)) (.app (Lambda.lift 1 0 b) (.var 0)))) := by
    have := Lambda.step.beta (.lam (.app (.app
      (Lambda.lift 1 0 (Lambda.lift 1 0 a)) (.var 0)) (.app (.var 1) (.var 0)))) b
    simp only [Lambda.subst, e] at this
    simpa using this
  have h3 : Lambda.step (.app (.lam (.app (.app (Lambda.lift 1 0 a) (.var 0))
      (.app (Lambda.lift 1 0 b) (.var 0)))) c) (.app (.app a c) (.app b c)) := by
    have := Lambda.step.beta (.app (.app (Lambda.lift 1 0 a) (.var 0))
      (.app (Lambda.lift 1 0 b) (.var 0))) c
    simpa [Lambda.subst, Lambda.subst_lift] using this
  exact .step _ _ _ (.app_left _ _ _ (.app_left _ _ _ h1))
    (.step _ _ _ (.app_left _ _ _ h2) (.step _ _ _ h3 (.refl _)))

/-- **The term model of the λ core is a total combinatory algebra**, hence a PCA. -/
noncomputable instance instTCA : TCA LTerm where
  tapp := tapp
  k := ⟦Lambda.K⟧
  s := ⟦Lambda.S⟧
  k_eq a b := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound (conv_of_reduces (K_reduces _ _))
  s_eq a b c := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    induction c using Quotient.inductionOn
    exact Quotient.sound (conv_of_reduces (S_reduces _ _ _))

/-- The realizer of `n` in the term model: its Church numeral. -/
def churchL (n : ℕ) : LTerm := ⟦Lambda.church n⟧

/-- **The arithmetic functions of the term model are the computable functions.** -/
theorem tracked_iff_computable (f : ℕ → ℕ) :
    Assembly.Tracked (natAsm churchL) (natAsm churchL) f ↔ Computable f := by
  rw [← lambdaComputable_iff_computable]
  constructor
  · rintro ⟨r, hr⟩
    induction r using Quotient.inductionOn with
    | h F =>
      have hF : ∀ n, Lambda.reduces (.app F (Lambda.church n)) (Lambda.church (f n)) := by
        intro n
        obtain ⟨v, hv, hvf⟩ := hr (churchL n) n rfl
        rw [TCA.app_eq, Part.mem_some_iff] at hv
        have : (⟦Lambda.app F (Lambda.church n)⟧ : LTerm) = ⟦Lambda.church (f n)⟧ :=
          (hv.symm.trans hvf : TCA.tapp ⟦F⟧ (churchL n) = churchL (f n))
        exact reduces_of_conv_normal (Quotient.exact this) (Lambda.church_normal _)
      refine ⟨F, fun n m => ⟨fun h => ?_, fun h => ?_⟩⟩
      · rw [Part.some_inj] at h
        rw [← h]
        exact hF n
      · obtain ⟨w, h1, h2⟩ := Lambda.confluence_theorem (hF n) h
        have e1 := reduces_normal_eq h1 (Lambda.church_normal _)
        have e2 := reduces_normal_eq h2 (Lambda.church_normal _)
        have := Lambda.church_injective (e2.symm.trans e1)
        show Part.some (f n) = Part.some m
        rw [this]
  · rintro ⟨F, hF⟩
    refine ⟨⟦F⟧, fun a n ha => ⟨churchL (f n), ?_, rfl⟩⟩
    rw [ha, TCA.app_eq, Part.mem_some_iff]
    exact (Quotient.sound (conv_of_reduces ((hF n (f n)).1 rfl))).symm

end TermModel

namespace Kleene

open Nat.Partrec (Code)
open scoped Realizability.Kleene

/-- **The arithmetic functions of Kleene's first algebra are the computable functions.** -/
theorem tracked_iff_computable (f : ℕ → ℕ) :
    Assembly.Tracked (natAsm (fun n : ℕ => n)) (natAsm (fun n : ℕ => n)) f ↔ Computable f := by
  constructor
  · rintro ⟨r, hr⟩
    have h : ∀ n, natApp r n = Part.some (f n) := by
      intro n
      obtain ⟨v, hv, hvf⟩ := hr n n rfl
      rw [hvf] at hv
      exact Part.eq_some_iff.2 hv
    have hp : Partrec fun n => Code.eval (Denumerable.ofNat Code r) n :=
      Code.eval_part.comp (Computable.const _) Computable.id
    exact hp.of_eq fun n => h n
  · intro hf
    obtain ⟨c, hc⟩ := exists_code_of_computable hf
    refine ⟨Encodable.encode c, fun a n ha => ⟨f n, ?_, rfl⟩⟩
    show f n ∈ Code.eval (Denumerable.ofNat Code (Encodable.encode c)) a
    rw [ha, Denumerable.ofNat_encode, hc]
    exact Part.mem_some _

end Kleene

/-- **The λ term model and Kleene's first algebra have the same arithmetic functions**: a function
`ℕ → ℕ` is a morphism of the natural-number assemblies over one iff over the other. -/
theorem tracked_termModel_iff_kleene (f : ℕ → ℕ) :
    Assembly.Tracked (natAsm TermModel.churchL) (natAsm TermModel.churchL) f ↔
      @Assembly.Tracked ℕ Kleene.instPCANat (@natAsm ℕ Kleene.instPCANat fun n => n)
        (@natAsm ℕ Kleene.instPCANat fun n => n) f :=
  (TermModel.tracked_iff_computable f).trans (Kleene.tracked_iff_computable f).symm

end Realizability
