/-
The normalisation theorem of the intersection type system.

`Start/FilterModel.lean` characterises *typability* by head normalisation.  This file
characterises the ω-free fragment: a term can be typed with a type and a basis in which the
universal type `ω` does not occur **iff** it has a β-normal form (Coppo–Dezani).

* `Inter.Proper` — an `ω`-free strict type: every arrow has a nonempty source (the empty
  intersection is `ω`);
* `Inter.ProperBasis` — a basis all of whose components are `ω`-free (a component may still be
  the empty intersection, which just means the variable carries no assumption);
* `Inter.hasNormalForm_of_properDeriv` — the hard direction, `ω`-free typability implies
  normalisation;
* `Inter.properDeriv_of_hasNormalForm` — the converse;
* `Inter.properTypable_iff_hasNormalForm` — **the normalisation theorem**.

The proof of the hard direction goes through the approximation theorem for the graph model
(`GraphModel.exists_reduct_mem_denot_direct`) instead of a computability argument: a proper type
in the denotation of `M` already lives in the denotation of the *direct approximant* of some
reduct `M'`, and two facts about proper types then force that approximant to contain no `Ω`,
which says exactly that `M'` is a normal form.

* `Inter.proper_of_mem_denot_neutral` — along a neutral spine a proper basis yields only proper
  types, so an arrow with source `ω` never appears;
* `Inter.isNormal_of_mem_denot_direct` — hence the direct approximant carrying a proper type is
  `Ω`-free, and the term it approximates is normal.
-/

import Start.FilterModel
import Start.GraphApproxTheorem
import Start.NormalizationUndecidable

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Inter

open GraphModel

/-! ### `ω`-free types -/

/-- A strict type is **proper** when the universal type `ω` — the empty intersection — does not
occur in it, that is, when every arrow it contains has a nonempty source. -/
inductive Proper : Sty → Prop
  | atom (n : ℕ) : Proper (Tok.atom n)
  | arrow {a : Ty} {b : Sty} :
      a ≠ [] → (∀ τ ∈ a, Proper τ) → Proper b → Proper (Tok.arrow a b)

theorem Proper.arrow_ne_nil {a : Ty} {b : Sty} (h : Proper (Tok.arrow a b)) : a ≠ [] := by
  cases h with | arrow h _ _ => exact h

theorem Proper.arrow_src {a : Ty} {b : Sty} (h : Proper (Tok.arrow a b)) : ∀ τ ∈ a, Proper τ := by
  cases h with | arrow _ h _ => exact h

theorem Proper.arrow_tgt {a : Ty} {b : Sty} (h : Proper (Tok.arrow a b)) : Proper b := by
  cases h with | arrow _ _ h => exact h

/-- A basis is proper when every type it assigns is proper.  The empty intersection is allowed as
a *component of the basis*: it carries no assumption about the variable. -/
def ProperBasis (Γ : Basis) : Prop := ∀ i, ∀ τ ∈ Γ i, Proper τ

theorem properBasis_push {a : Ty} {Γ : Basis} (ha : ∀ τ ∈ a, Proper τ) (hΓ : ProperBasis Γ) :
    ProperBasis (push a Γ) := by
  intro i
  cases i with
  | zero => exact ha
  | succ j => exact hΓ j

/-! ### Proper types along a neutral spine -/

/-- In a proper basis, every type of a **neutral** term is proper.  This is what rules out an
arrow with source `ω`: the head of the spine is a variable, whose types come from the basis, and
each application peels off one proper arrow. -/
theorem proper_of_mem_denot_neutral {Γ : Basis} (hΓ : ProperBasis Γ) :
    ∀ {A : Lambda}, Lambda.Neutral A → ∀ σ ∈ denot A (basisEnv Γ), Proper σ := by
  intro A hA
  induction hA with
  | var n =>
      intro σ hσ
      exact hΓ n σ (mem_lset.1 hσ)
  | app N _ ih =>
      intro σ hσ
      obtain ⟨a, -, harr⟩ := hσ
      exact (ih _ harr).arrow_tgt

/-! ### The direct approximant of a properly typed term is `Ω`-free -/

/-- If the direct approximant of `A` carries a proper type over a proper basis, then `A` contains
no β-redex at all: every application node of `A` survives into the approximant with a variable
head, and every argument is itself typed. -/
theorem isNormal_of_mem_denot_direct :
    ∀ (A : Lambda) (Γ : Basis), ProperBasis Γ → ∀ σ : Sty, Proper σ →
      σ ∈ denot (Lambda.direct A) (basisEnv Γ) → Lambda.is_normal A := by
  intro A
  induction A with
  | var n => intro _ _ _ _ _; exact Lambda.var_normal n
  | lam B ih =>
      intro Γ hΓ σ hσ hmem
      rw [Lambda.direct_lam, denot_lam] at hmem
      cases σ with
      | atom n => exact absurd hmem atom_notMem_graph
      | arrow a τ =>
          have hτ : τ ∈ denot (Lambda.direct B) (basisEnv (push a Γ)) := by
            rw [basisEnv_push]
            exact mem_graph.1 hmem
          exact Lambda.lam_normal
            (ih (push a Γ) (properBasis_push hσ.arrow_src hΓ) τ hσ.arrow_tgt hτ)
  | app P Q ihP ihQ =>
      intro Γ hΓ σ hσ hmem
      rw [Lambda.direct_app] at hmem
      by_cases hh : Lambda.headVar P = Bool.true
      · rw [if_pos hh] at hmem
        obtain ⟨a, ha, harr⟩ := hmem
        have hPn : Lambda.Neutral P := Lambda.neutral_iff_headVar.2 hh
        have hprop : Proper (Tok.arrow a σ) :=
          proper_of_mem_denot_neutral hΓ (Lambda.neutral_direct hPn) _ harr
        obtain ⟨τ, hτa⟩ := List.exists_mem_of_ne_nil a hprop.arrow_ne_nil
        have hτ : τ ∈ denot (Lambda.direct Q) (basisEnv Γ) := ha (mem_lset.2 hτa)
        exact Lambda.app_normal (ihP Γ hΓ _ hprop harr)
          (ihQ Γ hΓ τ (hprop.arrow_src τ hτa) hτ) hPn.ne_lam
      · rw [if_neg hh, denot_omega] at hmem
        exact absurd hmem (by simp)

/-- **`ω`-free typability implies normalisation.** -/
theorem hasNormalForm_of_properDeriv {Γ : Basis} {σ : Sty} {M : Lambda}
    (hΓ : ProperBasis Γ) (hσ : Proper σ) (h : Deriv Γ M σ) : Lambda.HasNormalForm M := by
  rw [deriv_iff_mem_denot] at h
  obtain ⟨M', hred, hmem⟩ := exists_reduct_mem_denot_direct h
  exact ⟨M', hred, isNormal_of_mem_denot_direct M' Γ hΓ σ hσ hmem⟩

/-! ### Normal forms are typable without `ω` -/

/-- Two mutually dependent facts about normal forms, proved by one structural induction: a normal
*neutral* term can be given **any** proper type (by choosing the basis), and every normal term
can be given some proper type. -/
theorem properDeriv_aux : ∀ M : Lambda,
    (Lambda.Neutral M → Lambda.is_normal M →
      ∀ σ : Sty, Proper σ → ∃ Γ : Basis, ProperBasis Γ ∧ Deriv Γ M σ) ∧
    (Lambda.is_normal M →
      ∃ (Γ : Basis) (σ : Sty), ProperBasis Γ ∧ Proper σ ∧ Deriv Γ M σ) := by
  intro M
  induction M with
  | var i =>
      have hvar : ∀ σ : Sty, Proper σ → ∃ Γ : Basis, ProperBasis Γ ∧ Deriv Γ (Lambda.var i) σ := by
        intro σ hσ
        refine ⟨fun j => if j = i then [σ] else [], ?_, Deriv.var (by simp)⟩
        intro j τ hτ
        by_cases hj : j = i
        · have hts : τ = σ := by simpa [hj] using hτ
          exact hts ▸ hσ
        · simp [hj] at hτ
      refine ⟨fun _ _ σ hσ => hvar σ hσ, fun _ => ?_⟩
      obtain ⟨Γ, hΓ, hd⟩ := hvar (Tok.atom 0) (Proper.atom 0)
      exact ⟨Γ, Tok.atom 0, hΓ, Proper.atom 0, hd⟩
  | lam B ih =>
      refine ⟨fun hn => absurd rfl (hn.ne_lam B), fun hnorm => ?_⟩
      obtain ⟨Γ, σ, hΓ, hσ, hd⟩ := ih.2 (Lambda.is_normal_of_lam hnorm)
      refine ⟨fun j => Γ (j + 1), Tok.arrow (Γ 0 ++ [Tok.atom 0]) σ, fun j => hΓ (j + 1), ?_, ?_⟩
      · refine Proper.arrow (by simp) ?_ hσ
        intro τ hτ
        rcases List.mem_append.1 hτ with h | h
        · exact hΓ 0 τ h
        · rw [List.mem_singleton.1 h]; exact Proper.atom 0
      · refine Deriv.lam (hd.weaken ?_)
        intro i τ hτ
        cases i with
        | zero => exact List.mem_append.2 (Or.inl hτ)
        | succ j => exact hτ
  | app P Q ihP ihQ =>
      have hneut : Lambda.Neutral (Lambda.app P Q) → Lambda.is_normal (Lambda.app P Q) →
          ∀ σ : Sty, Proper σ →
            ∃ Γ : Basis, ProperBasis Γ ∧ Deriv Γ (Lambda.app P Q) σ := by
        intro hn hnorm σ hσ
        have hPn : Lambda.Neutral P := by
          cases hn with | app _ h => exact h
        obtain ⟨ΓQ, τ, hΓQ, hτ, hdQ⟩ := ihQ.2 (Lambda.is_normal_of_app_right hnorm)
        obtain ⟨ΓP, hΓP, hdP⟩ :=
          ihP.1 hPn (Lambda.is_normal_of_app_left hnorm) (Tok.arrow [τ] σ)
            (Proper.arrow (by simp) (by intro x hx; rw [List.mem_singleton.1 hx]; exact hτ) hσ)
        refine ⟨fun j => ΓP j ++ ΓQ j, ?_, ?_⟩
        · intro j x hx
          rcases List.mem_append.1 hx with h | h
          · exact hΓP j x h
          · exact hΓQ j x h
        · refine Deriv.app (hdP.weaken fun i x hx => List.mem_append.2 (Or.inl hx)) ?_
          intro x hx
          rw [List.mem_singleton.1 hx]
          exact hdQ.weaken fun i y hy => List.mem_append.2 (Or.inr hy)
      refine ⟨hneut, fun hnorm => ?_⟩
      have hn : Lambda.Neutral (Lambda.app P Q) := by
        refine Lambda.neutral_of_isWhnf (Lambda.isWhnf_of_is_normal hnorm) ?_
        intro R hR
        exact Lambda.noConfusion hR
      obtain ⟨Γ, hΓ, hd⟩ := hneut hn hnorm (Tok.atom 0) (Proper.atom 0)
      exact ⟨Γ, Tok.atom 0, hΓ, Proper.atom 0, hd⟩

/-- **Normalisation implies `ω`-free typability**, by subject expansion from the normal form. -/
theorem properDeriv_of_hasNormalForm {M : Lambda} (h : Lambda.HasNormalForm M) :
    ∃ (Γ : Basis) (σ : Sty), ProperBasis Γ ∧ Proper σ ∧ Deriv Γ M σ := by
  obtain ⟨N, hred, hnorm⟩ := h
  obtain ⟨Γ, σ, hΓ, hσ, hd⟩ := (properDeriv_aux N).2 hnorm
  exact ⟨Γ, σ, hΓ, hσ, deriv_expansion hred hd⟩

/-- **The normalisation theorem.**  A term of the untyped calculus has a β-normal form exactly
when it is typable in the intersection type system with a type and a basis in which the
universal type `ω` does not occur. -/
theorem properTypable_iff_hasNormalForm (M : Lambda) :
    (∃ (Γ : Basis) (σ : Sty), ProperBasis Γ ∧ Proper σ ∧ Deriv Γ M σ) ↔
      Lambda.HasNormalForm M :=
  ⟨fun ⟨_, _, hΓ, hσ, hd⟩ => hasNormalForm_of_properDeriv hΓ hσ hd,
    properDeriv_of_hasNormalForm⟩

/-- Normalisation is stronger than typability. -/
theorem hasNormalForm_imp_typable {M : Lambda} (h : Lambda.HasNormalForm M) : Typable M := by
  obtain ⟨Γ, σ, -, -, hd⟩ := properDeriv_of_hasNormalForm h
  exact ⟨Γ, σ, hd⟩

/-! ### The two characterisations are different -/

/-- A normal form is in particular a head normal form. -/
theorem isHnf_of_is_normal : ∀ {t : Lambda}, Lambda.is_normal t → Lambda.IsHnf t := by
  intro t
  induction t with
  | var n => intro _; exact Lambda.IsHnf.neutral (Lambda.Neutral.var n)
  | lam B ih => intro h; exact Lambda.IsHnf.lam (ih (Lambda.is_normal_of_lam h))
  | app P Q _ _ =>
      intro h
      refine Lambda.IsHnf.neutral (Lambda.neutral_of_isWhnf (Lambda.isWhnf_of_is_normal h) ?_)
      intro R hR
      exact Lambda.noConfusion hR

theorem hasHnf_of_hasNormalForm {t : Lambda} (h : Lambda.HasNormalForm t) : Lambda.HasHnf t := by
  obtain ⟨N, hred, hn⟩ := h
  exact ⟨N, hred, isHnf_of_is_normal hn⟩

theorem not_hasNormalForm_omega : ¬ Lambda.HasNormalForm Lambda.omega :=
  fun h => GraphModel.not_hasHnf_omega (hasHnf_of_hasNormalForm h)

/-- The witness separating the two theorems: `x Ω` is a head normal form, hence typable, but it
has no normal form, hence no typing avoiding `ω`. -/
def varOmega : Lambda := Lambda.app (Lambda.var 0) Lambda.omega

theorem typable_varOmega : Typable varOmega :=
  typable_of_hasHnf (Lambda.hasHnf_of_neutral (Lambda.Neutral.app _ (Lambda.Neutral.var 0)))

theorem not_hasNormalForm_varOmega : ¬ Lambda.HasNormalForm varOmega := by
  rintro ⟨N, hred, hn⟩
  obtain ⟨M', N', rfl, -, hN'⟩ := Lambda.reduces_neutral_app (Lambda.Neutral.var 0) hred
  exact not_hasNormalForm_omega ⟨N', hN', Lambda.is_normal_of_app_right hn⟩

/-- **Typability and `ω`-free typability are different properties**: `x Ω` witnesses the gap
between the head-normalisation theorem of `Start/FilterModel.lean` and the normalisation theorem
above. -/
theorem exists_typable_not_properTypable :
    ∃ M : Lambda, Typable M ∧ ¬ ∃ (Γ : Basis) (σ : Sty), ProperBasis Γ ∧ Proper σ ∧ Deriv Γ M σ :=
  ⟨varOmega, typable_varOmega,
    fun h => not_hasNormalForm_varOmega ((properTypable_iff_hasNormalForm varOmega).1 h)⟩

end Inter
