import Start.PTSExpansionTopSN

/-!
# Series V, round 2, run 1, part A: expansion postponement for `cocTop` in kind-free contexts
(row M29-EP-TOP-MORPHISM)

* `HasTypeR.mapSort'` — transport of reduction-only derivations along a morphism of specifications;
* `TopSN.noTop` — legal `cocTop` expressions do not mention `Δ` (except a type equal to `Δ`);
* **`TopSN.cocTop_expansionPostponement_kindFree`** — expansion postponement for every `cocTop`
  judgement in a context without kind variables (`K : □`) whose type is not `Δ`, transported from
  `coc_expansionPostponement` along the collapse `Δ ↦ □` and back.

What remains for `cocTop_expansionPostponement` is exactly the contexts with kind variables, where
the kind substitution of `Start/PTSExpansionTopSN.lean` changes the subject.
-/

set_option autoImplicit false

namespace PureTypeSystem

open LambdaPi (Srt)

theorem HasTypeR.mapSort' {S T : Type} {P : Specification S} {Q : Specification T}
    {Γ : List (Expr S)} {M A : Expr S}
    (h : HasTypeR P Γ M A) (f : S → T)
    (ha : ∀ s t, P.axioms s t → Q.axioms (f s) (f t))
    (hr : ∀ a b c, P.rule a b c → Q.rule (f a) (f b) (f c)) :
    HasTypeR Q (Γ.map (Expr.mapSort f)) (M.mapSort f) (A.mapSort f) := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => simpa only [List.map_cons, Expr.mapSort, Expr.mapSort_rename] using HasTypeR.var ih
  | weaken _ _ ihM ihA =>
      simpa only [List.map_cons, Expr.mapSort_rename] using HasTypeR.weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha =>
      simpa only [Expr.mapSort, Expr.mapSort_instantiate] using HasTypeR.application ihf iha
  | reduction _ hb ih => exact .reduction ih (hb.mapSort f)

theorem rtBeta_mapSort {S T : Type} {A B : Expr S} (h : Relation.ReflTransGen Beta A B)
    (f : S → T) : Relation.ReflTransGen Beta (A.mapSort f) (B.mapSort f) := by
  induction h with
  | refl => exact .refl
  | tail _ hb ih => exact ih.tail (hb.mapSort f)

namespace TopSN

/-- `Δ ↦ □` and back into `Srt3`: the identity on every `Δ`-free expression. -/
def g3 : Srt3 → Srt3 := srtToSrt3 ∘ cut

/-- **Legal `cocTop` expressions do not mention `Δ`** (apart from a type equal to `Δ`). -/
theorem noTop {Γ : List (Expr Srt3)} {M A : Expr Srt3} (h : HasType cocTop Γ M A) :
    M.mapSort g3 = M ∧ (A = .sort .top ∨ A.mapSort g3 = A) := by
  induction h with
  | ax hst =>
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, .inr rfl⟩
      · exact ⟨rfl, .inl rfl⟩
  | var _ ih =>
      refine ⟨rfl, .inr ?_⟩
      rw [Expr.mapSort_rename, ih.1]
  | weaken _ _ ihM _ =>
      refine ⟨by rw [Expr.mapSort_rename, ihM.1], ?_⟩
      rcases ihM.2 with e | e
      · exact .inl (by rw [e]; rfl)
      · exact .inr (by rw [Expr.mapSort_rename, e])
  | @product _ _ _ s₁ s₂ s₃ _ _ hr ihA ihB =>
      obtain ⟨e3, _, h2⟩ := hr
      refine ⟨by simp only [Expr.mapSort, ihA.1, ihB.1], .inr ?_⟩
      rw [e3]
      cases s₂ <;> first | rfl | exact absurd rfl h2
  | abstraction _ _ ihb ihPi =>
      have e := ihPi.1
      simp only [Expr.mapSort, Expr.pi.injEq] at e
      exact ⟨by simp only [Expr.mapSort, e.1, ihb.1], .inr (by simp only [Expr.mapSort, e.1, e.2])⟩
  | application _ _ ihf iha =>
      refine ⟨by simp only [Expr.mapSort, ihf.1, iha.1], .inr ?_⟩
      rcases ihf.2 with e | e
      · cases e
      · simp only [Expr.mapSort, Expr.pi.injEq] at e
        rw [Expr.mapSort_instantiate, e.2, iha.1]
  | conversion _ _ _ ihM ihB => exact ⟨ihM.1, .inr ihB.1⟩

theorem ctx_noTop {Γ : List (Expr Srt3)} (hΓ : ValidContext cocTop Γ) :
    Γ.map (Expr.mapSort g3) = Γ := by
  induction hΓ with
  | nil => rfl
  | cons _ hA ih => simp only [List.map_cons, ih, (noTop hA).1]

theorem srtToSrt3_axiom (s t : Srt) (h : (cubeSpec coc).axioms s t) :
    cocTop.axioms (srtToSrt3 s) (srtToSrt3 t) := by
  obtain ⟨rfl, rfl⟩ := h
  exact Or.inl ⟨rfl, rfl⟩

theorem srtToSrt3_rule (a b c : Srt) (h : (cubeSpec coc).rule a b c) :
    cocTop.rule (srtToSrt3 a) (srtToSrt3 b) (srtToSrt3 c) := by
  obtain ⟨rfl, _⟩ := h
  refine ⟨rfl, ?_, ?_⟩ <;> cases a <;> cases c <;> decide

/-- **Expansion postponement for `cocTop` in kind-free contexts**: a `cocTop` judgement in a
context without kind variables (`K : □`) whose type is not `Δ` has a reduction-only derivation at
a reduct of its type. -/
theorem cocTop_expansionPostponement_kindFree {Γ : List (Expr Srt3)} {M A : Expr Srt3}
    (h : HasType cocTop Γ M A) (hKF : ∀ C ∈ Γ, C ≠ .sort .box) (hA : A ≠ .sort .top) :
    ∃ B, Relation.ReflTransGen Beta A B ∧ HasTypeR cocTop Γ M B := by
  obtain ⟨B', hAB, hR⟩ := coc_expansionPostponement _ _ _ (kf_coc h hKF hA)
  have hR' := hR.mapSort' srtToSrt3 srtToSrt3_axiom srtToSrt3_rule
  have hAB' := rtBeta_mapSort hAB srtToSrt3
  simp only [List.map_map, Expr.mapSort_comp] at hR' hAB'
  have hM : M.mapSort (srtToSrt3 ∘ cut) = M := (noTop h).1
  have hA' : A.mapSort (srtToSrt3 ∘ cut) = A := by
    rcases (noTop h).2 with e | e
    · exact absurd e hA
    · exact e
  have hΓ : List.map (Expr.mapSort srtToSrt3 ∘ Expr.mapSort cut) Γ = Γ := by
    have := ctx_noTop h.valid
    simpa [g3, Function.comp_def, Expr.mapSort_comp] using this
  rw [hM] at hR'
  rw [hA'] at hAB'
  rw [hΓ] at hR'
  exact ⟨_, hAB', hR'⟩

end TopSN

end PureTypeSystem
