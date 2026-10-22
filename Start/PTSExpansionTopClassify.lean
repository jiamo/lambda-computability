import Start.PTSExpansionTopSkel

/-!
# Series V, round 3, run 1, part B1: the classifier with skeleton variables under renaming and
substitution (row M29-EP-TOP-SORT-FUNDAMENTAL)

The structural half of `TopSkel.classifyV`: the classifier `clV` and well-classification `WCV` of
`Start/PTSExpansionTopSkel.lean` commute with renaming (weakening) and with substitution of
expressions whose classes match the variables' classes; the context classifier `ctxClV` is the
`ncons`-extension at every declaration other than a kind-variable declaration `K : □`.

* `clV_rename`, `WCV_rename` — invariance under renaming;
* `clV_subst`, `clV_instantiate` — classes under substitution (no side condition: the classes, not
  the skeleton variables, are substituted);
* `WCV_subst`, `WCV_instantiate` — well-classification under substitution, given well-classified
  substituends of matching class;
* `ctxClV_comp_succ`, `ctxClV_cons_of_ne` — the context classifier under weakening and at a
  declaration `A ≠ □`.

* `top_untypable`, `not_conv_top`, **`eq_box_of_conv`** — `Δ` is untypable and no typable
  expression converts to it; a typable expression convertible to `□` is `□` (the `cocTop` analogue
  of `CoC.not_conv_box`).

`classifyV` itself is in `Start/PTSExpansionTopClassifyV.lean`.
-/

set_option autoImplicit false

namespace PureTypeSystem.TopSkel

open CoC (ncons ncons_comp_liftRen)

theorem clV_rename (M : Expr Srt3) (Δ : Nat → ClsV) (ρ : Nat → Nat) :
    clV Δ (M.rename ρ) = clV (Δ ∘ ρ) M := by
  induction M generalizing Δ ρ with
  | var n => rfl
  | sort s => cases s <;> rfl
  | app f a ihf _ => simp only [Expr.rename, clV, ihf]
  | lam A b ihA ihb => simp only [Expr.rename, clV, ihA, ihb, ncons_comp_liftRen]
  | pi A B ihA ihB => simp only [Expr.rename, clV, ihA, ihB, ncons_comp_liftRen]

theorem WCV_rename (M : Expr Srt3) (Δ : Nat → ClsV) (ρ : Nat → Nat) :
    WCV Δ (M.rename ρ) ↔ WCV (Δ ∘ ρ) M := by
  induction M generalizing Δ ρ with
  | var n => exact Iff.rfl
  | sort s => exact Iff.rfl
  | app f a ihf iha => simp only [Expr.rename, WCV, clV_rename, ihf, iha]
  | lam A b ihA ihb => simp only [Expr.rename, WCV, ihA, ihb, clV_rename, ncons_comp_liftRen]
  | pi A B ihA ihB => simp only [Expr.rename, WCV, ihA, ihB, clV_rename, ncons_comp_liftRen]

theorem clV_liftSub {Δ Δ' : Nat → ClsV} {σ : Nat → Expr Srt3} (hσ : ∀ n, clV Δ (σ n) = Δ' n)
    (c : ClsV) (n : Nat) : clV (ncons c Δ) (Expr.liftSub σ n) = ncons c Δ' n := by
  cases n with
  | zero => rfl
  | succ n => simp only [Expr.liftSub_succ, clV_rename, CoC.ncons_comp_succ, hσ, CoC.ncons_succ]

/-- Classes under substitution. -/
theorem clV_subst (M : Expr Srt3) {Δ Δ' : Nat → ClsV} {σ : Nat → Expr Srt3}
    (hσ : ∀ n, clV Δ (σ n) = Δ' n) : clV Δ (M.subst σ) = clV Δ' M := by
  induction M generalizing Δ Δ' σ with
  | var n => exact hσ n
  | sort s => cases s <;> rfl
  | app f a ihf _ => simp only [Expr.subst, clV, ihf hσ]
  | lam A b ihA ihb =>
      simp only [Expr.subst, clV, ihA hσ]
      rw [ihb (clV_liftSub hσ _)]
  | pi A B ihA ihB =>
      simp only [Expr.subst, clV, ihA hσ]
      rw [ihB (clV_liftSub hσ _)]

theorem clV_single {Δ : Nat → ClsV} (U : Expr Srt3) :
    ∀ n, clV Δ (Expr.single U n) = ncons (clV Δ U) Δ n
  | 0 => rfl
  | _ + 1 => rfl

theorem clV_instantiate (b U : Expr Srt3) (Δ : Nat → ClsV) :
    clV Δ (b.instantiate U) = clV (ncons (clV Δ U) Δ) b :=
  clV_subst b (clV_single U)

theorem WCV_liftSub {Δ : Nat → ClsV} {σ : Nat → Expr Srt3}
    (hw : ∀ n, WCV Δ (σ n)) (c : ClsV) (n : Nat) : WCV (ncons c Δ) (Expr.liftSub σ n) := by
  cases n with
  | zero => trivial
  | succ n =>
      simp only [Expr.liftSub_succ]
      rw [WCV_rename, CoC.ncons_comp_succ]
      exact hw n

/-- Well-classification under substitution. -/
theorem WCV_subst (M : Expr Srt3) {Δ Δ' : Nat → ClsV} {σ : Nat → Expr Srt3}
    (hσ : ∀ n, clV Δ (σ n) = Δ' n) (hw : ∀ n, WCV Δ (σ n)) (hM : WCV Δ' M) :
    WCV Δ (M.subst σ) := by
  induction M generalizing Δ Δ' σ with
  | var n => exact hw n
  | sort s => trivial
  | app f a ihf iha =>
      obtain ⟨h1, h2, h3⟩ := hM
      refine ⟨?_, ihf hσ hw h2, iha hσ hw h3⟩
      rw [clV_subst f hσ]; exact h1
  | lam A b ihA ihb =>
      obtain ⟨h1, h2⟩ := hM
      refine ⟨ihA hσ hw h1, ?_⟩
      rw [clV_subst A hσ]
      exact ihb (clV_liftSub hσ _) (WCV_liftSub hw _) h2
  | pi A B ihA ihB =>
      obtain ⟨h1, h2⟩ := hM
      refine ⟨ihA hσ hw h1, ?_⟩
      rw [clV_subst A hσ]
      exact ihB (clV_liftSub hσ _) (WCV_liftSub hw _) h2

theorem WCV_instantiate (b U : Expr Srt3) (Δ : Nat → ClsV) (hU : WCV Δ U)
    (hb : WCV (ncons (clV Δ U) Δ) b) : WCV Δ (b.instantiate U) :=
  WCV_subst b (clV_single U) (fun n => by cases n <;> first | exact hU | trivial) hb

@[simp] theorem ctxClV_comp_succ (A : Expr Srt3) (Γ : List (Expr Srt3)) :
    ctxClV (A :: Γ) ∘ Nat.succ = ctxClV Γ := rfl

/-- At a declaration other than `K : □` the context classifier is the `ncons`-extension. -/
theorem ctxClV_cons_of_ne {A : Expr Srt3} (hA : A ≠ .sort .box) (Γ : List (Expr Srt3)) :
    ctxClV (A :: Γ) = ncons (bindV (clV (ctxClV Γ) A)) (ctxClV Γ) := by
  funext n
  cases n with
  | zero => simp [ctxClV, hA]
  | succ n => rfl

/-- At a kind-variable declaration the variable is a kind of skeleton `svar ℓ`. -/
theorem ctxClV_cons_box (Γ : List (Expr Srt3)) :
    ctxClV (.sort .box :: Γ) 0 = .kind (.svar Γ.length) := by
  simp [ctxClV]

/-! ### `Δ` and `□` in `cocTop` -/

theorem top_untypable {Γ : List (Expr Srt3)} {T : Expr Srt3} :
    ¬ HasType cocTop Γ (.sort .top) T := by
  intro h
  obtain ⟨t, ht, _⟩ := h.generation
  simp [cocTop] at ht

theorem reduces_from_sort {s : Srt3} {N : Expr Srt3} (h : Reduces (.sort s) N) : N = .sort s := by
  induction h with
  | refl => rfl
  | tail _ hb ih => subst ih; cases hb

theorem beta_to_sort {A : Expr Srt3} {s : Srt3} (h : Beta A (.sort s)) :
    ∃ X b a, A = .app (.lam X b) a ∧ b.instantiate a = .sort s := by
  revert h
  generalize e : Expr.sort s = N
  intro h
  cases h with
  | head X b a => exact ⟨X, b, a, rfl, rfl⟩
  | _ => cases e

theorem instantiate_eq_sort {b a : Expr Srt3} {s : Srt3} (h : b.instantiate a = .sort s) :
    b = .sort s ∨ (b = .var 0 ∧ a = .sort s) := by
  cases b with
  | var n =>
      cases n with
      | zero => exact .inr ⟨rfl, h⟩
      | succ n => cases h
  | sort t => exact .inl h
  | app _ _ => cases h
  | lam _ _ => cases h
  | pi _ _ => cases h

/-- No typable expression reduces to `Δ`. -/
theorem not_reduces_top {Γ : List (Expr Srt3)} {A T : Expr Srt3} (h : HasType cocTop Γ A T)
    (hr : Reduces A (.sort .top)) : False :=
  top_untypable (h.subject_reduces hr)

theorem not_conv_top {Γ : List (Expr Srt3)} {A T : Expr Srt3} (h : HasType cocTop Γ A T)
    (hc : Converts A (.sort .top)) : False := by
  obtain ⟨C, hAC, hTC⟩ := hc.join
  rw [reduces_from_sort hTC] at hAC
  exact not_reduces_top h hAC

/-- A typable expression that β-reduces to `□` in one step does not exist. -/
theorem not_beta_box {Γ : List (Expr Srt3)} {A T : Expr Srt3} (h : HasType cocTop Γ A T)
    (hb : Beta A (.sort .box)) : False := by
  obtain ⟨X, b, a, rfl, hi⟩ := beta_to_sort hb
  obtain ⟨A', B', hf, ha, _⟩ := h.generation_app
  rcases instantiate_eq_sort hi with rfl | ⟨rfl, rfl⟩
  · obtain ⟨B, s, hb', hPi, _⟩ := hf.generation_lam
    obtain ⟨t, ht, hBt⟩ := hb'.generation
    have htop : t = .top := by
      simp only [cocTop] at ht
      rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
      · cases h1
      · exact h2
    subst htop
    obtain ⟨s₁, s₂, s₃, _, hB, _, _⟩ := hPi.generation_pi
    exact not_conv_top hB hBt
  · obtain ⟨t, ht, hAt⟩ := ha.generation
    have htop : t = .top := by
      simp only [cocTop] at ht
      rcases ht with ⟨h1, _⟩ | ⟨_, h2⟩
      · cases h1
      · exact h2
    subst htop
    obtain ⟨s, hPi⟩ := hf.product_type_sorted
    obtain ⟨s₁, s₂, s₃, hA', _, _, _⟩ := hPi.generation_pi
    exact not_conv_top hA' hAt

/-- **A typable expression convertible to `□` is `□`** (the `cocTop` analogue of
`CoC.not_conv_box`). -/
theorem eq_box_of_reduces {Γ : List (Expr Srt3)} {A T : Expr Srt3} (h : HasType cocTop Γ A T)
    (hAC : Reduces A (.sort .box)) : A = .sort .box := by
  induction hAC using Relation.ReflTransGen.head_induction_on generalizing T with
  | refl => rfl
  | head hb hr ih =>
      have h1 := ih (h.subject_reduction hb)
      subst h1
      exact (not_beta_box h hb).elim

theorem eq_box_of_conv {Γ : List (Expr Srt3)} {A T : Expr Srt3} (h : HasType cocTop Γ A T)
    (hc : Converts A (.sort .box)) : A = .sort .box := by
  obtain ⟨C, hAC, hTC⟩ := hc.join
  rw [reduces_from_sort hTC] at hAC
  exact eq_box_of_reduces h hAC

end PureTypeSystem.TopSkel
