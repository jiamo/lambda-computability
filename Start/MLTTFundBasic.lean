/-
**Martin-Löf type theory: the fundamental theorem, structural and basic rules** — milestone
M30 (`M30-MLTT-FUND`).

The validity of the rules of `MLTT.Der` other than those of dependent products and of the
eliminators: universes, `ℕ` and `⊥` as types and as terms of `U 0`, variables, conversion,
`Der.el`, the equivalence rules for type and term equality, `zero` and `succ`.

* canonical reducibility proofs `TyR.univ_canon`, `TyR.nat_canon`, `TyR.empty_canon` with
  their interpretations `univI`, `natI`, `emptyI`;
* `ValidCtx.lookup` — the declared types of a valid context are valid;
* the rules: `valid_univT`, `valid_natT`, `valid_emptyT`, `valid_el`, `valid_univU`,
  `valid_natU`, `valid_emptyU`, `valid_var`, `valid_conv`, `valid_reflT`, `valid_symmT`,
  `valid_transT`, `valid_elEq`, `valid_refl`, `valid_symm`, `valid_trans`, `valid_eqConv`,
  `valid_zero`, `valid_succ`, `valid_succCong`.
-/

import Start.MLTTValidLemmas

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

variable {E : GenEq}

/-! ### Canonical reducibility proofs -/

/-- The interpretation of the universe `U l'`. -/
def univI (E : GenEq) (Δ : Ctx) (l' : ℕ) : Interp where
  tyEq := fun B => TyRedsT Δ B (univ l')
  tmEq := fun t u => ∃ t' u', TRedsT Δ t t' (univ l') ∧ TRedsT Δ u u' (univ l') ∧
    Whnf t' ∧ Whnf u' ∧ E.tm Δ t' u' (univ l') ∧ (∃ I, TyR E l' Δ t I ∧ I.tyEq u) ∧
    (∃ J, TyR E l' Δ u J)

/-- The interpretation of `ℕ`. -/
def natI (E : GenEq) (Δ : Ctx) : Interp where
  tyEq := fun B => TyRedsT Δ B nat
  tmEq := NatR E Δ

/-- The interpretation of `⊥`. -/
def emptyI (E : GenEq) (Δ : Ctx) : Interp where
  tyEq := fun B => TyRedsT Δ B empty
  tmEq := EmptyR E Δ

theorem TyR.univ_canon {Δ : Ctx} (hΔ : WfCtx Δ) {l' l : ℕ} (hl : l' < l) :
    TyR E l Δ (univ l') (univI E Δ l') := by
  rw [TyR.unfold]
  exact TyRAt.univ hl (TyRedsT.refl (Der.univT l' hΔ))

theorem TyR.nat_canon {Δ : Ctx} (hΔ : WfCtx Δ) (l : ℕ) : TyR E l Δ nat (natI E Δ) := by
  rw [TyR.unfold]
  exact TyRAt.nat (TyRedsT.refl (Der.natT hΔ))

theorem TyR.empty_canon {Δ : Ctx} (hΔ : WfCtx Δ) (l : ℕ) : TyR E l Δ empty (emptyI E Δ) := by
  rw [TyR.unfold]
  exact TyRAt.empty (TyRedsT.refl (Der.emptyT hΔ))

/-! ### Valid contexts -/

theorem ValidTy.shift {Γ : Ctx} {A B : Tm} (h : ValidTy E Γ A) : ValidTy E (B :: Γ) (shift A) := by
  obtain ⟨l, hl⟩ := h
  refine ⟨l, fun Δ σ σ' hs => ?_⟩
  rw [subst_shift_stail, subst_shift_stail]
  exact hl Δ (stail σ) (stail σ') hs.1

theorem ValidCtx.lookup {Γ : Ctx} {n : ℕ} {A : Tm} (hl : Lookup Γ n A) (hΓ : ValidCtx E Γ) :
    ValidTy E Γ A := by
  induction hl with
  | zero Γ A => exact hΓ.2.shift
  | succ B _ ih => exact (ih hΓ.1).shift

/-! ### Universes, natural numbers and the empty type as types -/

theorem valid_univT {Γ : Ctx} (l : ℕ) : ValidTy E Γ (univ l) :=
  ⟨l + 1, fun Δ _ _ hs =>
    ⟨univI E Δ l, TyR.univ_canon hs.wfCtx (Nat.lt_succ_self l), TyRedsT.refl (Der.univT l hs.wfCtx)⟩⟩

theorem valid_natT {Γ : Ctx} : ValidTy E Γ nat :=
  ⟨0, fun Δ _ _ hs => ⟨natI E Δ, TyR.nat_canon hs.wfCtx 0, TyRedsT.refl (Der.natT hs.wfCtx)⟩⟩

theorem valid_emptyT {Γ : Ctx} : ValidTy E Γ empty :=
  ⟨0, fun Δ _ _ hs =>
    ⟨emptyI E Δ, TyR.empty_canon hs.wfCtx 0, TyRedsT.refl (Der.emptyT hs.wfCtx)⟩⟩

/-- A term of a universe is a type, at the level of the universe. -/
theorem valid_el_at {Γ : Ctx} {A : Tm} {l : ℕ} (h : ValidTm E Γ A (univ l)) :
    ∀ Δ σ σ', SubstR E Γ Δ σ σ' → ∃ I, TyR E l Δ (subst σ A) I ∧ I.tyEq (subst σ' A) := by
  intro Δ σ σ' hs
  obtain ⟨t', u', -, -, -, -, -, ⟨I, hI, hIu⟩, -⟩ :=
    h.2 Δ σ σ' hs (l + 1) (univI E Δ l) (TyR.univ_canon hs.wfCtx (Nat.lt_succ_self l))
  exact ⟨I, hI, hIu⟩

/-- **A term of a universe is a type.** -/
theorem valid_el {Γ : Ctx} {A : Tm} {l : ℕ} (h : ValidTm E Γ A (univ l)) : ValidTy E Γ A := by
  refine ⟨l, fun Δ σ σ' hs => ?_⟩
  obtain ⟨t', u', -, -, -, -, -, ⟨I, hI, hIu⟩, -⟩ :=
    h.2 Δ σ σ' hs (l + 1) (univI E Δ l) (TyR.univ_canon hs.wfCtx (Nat.lt_succ_self l))
  exact ⟨I, hI, hIu⟩

/-! ### Universes, natural numbers and the empty type as terms -/

theorem valid_univU {Γ : Ctx} (l : ℕ) : ValidTm E Γ (univ l) (univ (l + 1)) := by
  refine ValidTm.intro (valid_univT (l + 1)) (fun Δ σ σ' hs => ?_)
  have hΔ := hs.wfCtx
  refine ⟨l + 2, univI E Δ (l + 1), TyR.univ_canon hΔ (by omega), ?_⟩
  have hU := TRedsT.refl (Der.univU l hΔ)
  exact ⟨univ l, univ l, hU, hU, Whnf.univ _, Whnf.univ _, E.univU_refl l hΔ,
    ⟨univI E Δ l, TyR.univ_canon hΔ (Nat.lt_succ_self l), TyRedsT.refl (Der.univT l hΔ)⟩,
    ⟨univI E Δ l, TyR.univ_canon hΔ (Nat.lt_succ_self l)⟩⟩

theorem valid_natU {Γ : Ctx} : ValidTm E Γ nat (univ 0) := by
  refine ValidTm.intro (valid_univT 0) (fun Δ σ σ' hs => ?_)
  have hΔ := hs.wfCtx
  refine ⟨1, univI E Δ 0, TyR.univ_canon hΔ Nat.zero_lt_one, ?_⟩
  have hN := TRedsT.refl (Der.natU hΔ)
  exact ⟨nat, nat, hN, hN, Whnf.nat, Whnf.nat, E.natU_refl hΔ,
    ⟨natI E Δ, TyR.nat_canon hΔ 0, TyRedsT.refl (Der.natT hΔ)⟩, ⟨natI E Δ, TyR.nat_canon hΔ 0⟩⟩

theorem valid_emptyU {Γ : Ctx} : ValidTm E Γ empty (univ 0) := by
  refine ValidTm.intro (valid_univT 0) (fun Δ σ σ' hs => ?_)
  have hΔ := hs.wfCtx
  refine ⟨1, univI E Δ 0, TyR.univ_canon hΔ Nat.zero_lt_one, ?_⟩
  have hN := TRedsT.refl (Der.emptyU hΔ)
  exact ⟨empty, empty, hN, hN, Whnf.empty, Whnf.empty, E.emptyU_refl hΔ,
    ⟨emptyI E Δ, TyR.empty_canon hΔ 0, TyRedsT.refl (Der.emptyT hΔ)⟩,
    ⟨emptyI E Δ, TyR.empty_canon hΔ 0⟩⟩

/-! ### Variables and conversion -/

theorem valid_var {Γ : Ctx} {n : ℕ} {A : Tm} (hΓ : ValidCtx E Γ) (hl : Lookup Γ n A) :
    ValidTm E Γ (var n) A :=
  ⟨hΓ.lookup hl, fun _ _ _ hs l I hI => SubstR.lookup hl hΓ hs l I hI⟩

theorem valid_conv {Γ : Ctx} {t A B : Tm} (hΓ : ValidCtx E Γ) (ht : ValidTm E Γ t A)
    (hAB : ValidTyEq E Γ A B) : ValidTm E Γ t B := by
  refine ⟨hAB.2.1, fun Δ σ σ' hs l J hJ => ?_⟩
  obtain ⟨l₀, I, hI, -⟩ := ht.1.red hs
  have hIt := ht.2 Δ σ σ' hs l₀ I hI
  have hIB := hAB.2.2 Δ σ σ (hs.left hΓ) l₀ I hI
  exact ((TyR.good l₀ hI).conv hJ hIB _ _).mp hIt

/-! ### Type equality -/

theorem valid_reflT {Γ : Ctx} {A : Tm} (hA : ValidTy E Γ A) : ValidTyEq E Γ A A :=
  ValidTyEq.intro hA hA (fun _ _ _ hs => hA.red hs)

theorem valid_symmT {Γ : Ctx} {A B : Tm} (hΓ : ValidCtx E Γ) (h : ValidTyEq E Γ A B) :
    ValidTyEq E Γ B A := by
  refine ValidTyEq.intro h.2.1 h.1 (fun Δ σ σ' hs => ?_)
  have hs' := hs.right hΓ
  obtain ⟨l, J, hJ, hJB⟩ := h.2.1.red hs
  obtain ⟨lK, K, hK, -⟩ := h.1.red hs'
  have hKB := h.2.2 Δ σ' σ' hs' lK K hK
  obtain ⟨lL, L, hL, -⟩ := h.2.1.red hs'
  have hLA : L.tyEq (subst σ' A) := (TyR.good lK hK).tySymm hL hKB
  exact ⟨l, J, hJ, (TyR.good l hJ).tyTrans hL hJB hLA⟩

theorem valid_transT {Γ : Ctx} {A B C : Tm} (hΓ : ValidCtx E Γ) (h₁ : ValidTyEq E Γ A B)
    (h₂ : ValidTyEq E Γ B C) : ValidTyEq E Γ A C := by
  refine ValidTyEq.intro h₁.1 h₂.2.1 (fun Δ σ σ' hs => ?_)
  have hs' := hs.right hΓ
  obtain ⟨l, I, hI, -⟩ := h₁.1.red hs
  have hIB := h₁.2.2 Δ σ σ' hs l I hI
  obtain ⟨lL, L, hL, -⟩ := h₂.1.red hs'
  have hLC := h₂.2.2 Δ σ' σ' hs' lL L hL
  exact ⟨l, I, hI, (TyR.good l hI).tyTrans hL hIB hLC⟩

theorem valid_elEq {Γ : Ctx} {A B : Tm} {l : ℕ} (h : ValidEq E Γ A B (univ l)) :
    ValidTyEq E Γ A B := by
  refine ValidTyEq.intro (valid_el h.1) (valid_el h.2.1) (fun Δ σ σ' hs => ?_)
  obtain ⟨t', u', -, -, -, -, -, ⟨I, hI, hIu⟩, -⟩ :=
    h.2.2 Δ σ σ' hs (l + 1) (univI E Δ l) (TyR.univ_canon hs.wfCtx (Nat.lt_succ_self l))
  exact ⟨l, I, hI, hIu⟩

/-! ### Term equality -/

theorem valid_refl {Γ : Ctx} {t A : Tm} (h : ValidTm E Γ t A) : ValidEq E Γ t t A :=
  ⟨h, h, h.2⟩

theorem valid_symm {Γ : Ctx} {t u A : Tm} (hΓ : ValidCtx E Γ) (h : ValidEq E Γ t u A) :
    ValidEq E Γ u t A := by
  refine ⟨h.2.1, h.1, fun Δ σ σ' hs l I hI => ?_⟩
  have hs' := hs.symm hΓ
  obtain ⟨l', I', hI', hI'A⟩ := h.1.1.red hs'
  have h₁ := h.2.2 Δ σ' σ hs' l' I' hI'
  -- `I'` is the interpretation at `σ'`, equal to the one at `σ`
  have hIA : I.tyEq (subst σ' A) := by
    obtain ⟨l₀, I₀, hI₀, hI₀A⟩ := h.1.1.red hs
    exact ((TyR.irrel hI₀ hI).1 _).mp hI₀A
  have hconv := (TyR.good l hI).conv hI' hIA
  exact (TyR.good l hI).symm ((hconv _ _).mpr h₁)

theorem valid_trans {Γ : Ctx} {t u v A : Tm} (hΓ : ValidCtx E Γ) (h₁ : ValidEq E Γ t u A)
    (h₂ : ValidEq E Γ u v A) : ValidEq E Γ t v A := by
  refine ⟨h₁.1, h₂.2.1, fun Δ σ σ' hs l I hI => ?_⟩
  have hs' := hs.right hΓ
  have e₁ := h₁.2.2 Δ σ σ' hs l I hI
  obtain ⟨l', I', hI', -⟩ := h₁.1.1.red hs'
  have e₂ := h₂.2.2 Δ σ' σ' hs' l' I' hI'
  have hIA : I.tyEq (subst σ' A) := by
    obtain ⟨l₀, I₀, hI₀, hI₀A⟩ := h₁.1.1.red hs
    exact ((TyR.irrel hI₀ hI).1 _).mp hI₀A
  have hconv := (TyR.good l hI).conv hI' hIA
  exact (TyR.good l hI).trans e₁ ((hconv _ _).mpr e₂)

theorem valid_eqConv {Γ : Ctx} {t u A B : Tm} (hΓ : ValidCtx E Γ) (h : ValidEq E Γ t u A)
    (hAB : ValidTyEq E Γ A B) : ValidEq E Γ t u B := by
  refine ⟨valid_conv hΓ h.1 hAB, valid_conv hΓ h.2.1 hAB, fun Δ σ σ' hs l J hJ => ?_⟩
  obtain ⟨l₀, I, hI, -⟩ := h.1.1.red hs
  have hIt := h.2.2 Δ σ σ' hs l₀ I hI
  have hIB := hAB.2.2 Δ σ σ (hs.left hΓ) l₀ I hI
  exact ((TyR.good l₀ hI).conv hJ hIB _ _).mp hIt

/-! ### Zero and successor -/

theorem valid_zero {Γ : Ctx} : ValidTm E Γ zero nat := by
  refine ValidTm.intro valid_natT (fun Δ σ σ' hs => ?_)
  have hz := TRedsT.refl (Der.zero hs.wfCtx)
  exact ⟨0, natI E Δ, TyR.nat_canon hs.wfCtx 0, NatR.zero hz hz⟩

theorem valid_succCong {Γ : Ctx} {n m : Tm} (h : ValidEq E Γ n m nat) :
    ValidEq E Γ (succ n) (succ m) nat := by
  have key : ∀ {a b : Tm}, ValidEq E Γ a b nat → ∀ Δ σ σ', SubstR E Γ Δ σ σ' →
      ∃ l I, TyR E l Δ (subst σ nat) I ∧ I.tmEq (subst σ (succ a)) (subst σ' (succ b)) := by
    intro a b hab Δ σ σ' hs
    have hN := TyR.nat_canon (E := E) hs.wfCtx 0
    have hr : NatR E Δ (subst σ a) (subst σ' b) := hab.2.2 Δ σ σ' hs 0 (natI E Δ) hN
    obtain ⟨ha, hb, hab'⟩ := hr.escape
    exact ⟨0, natI E Δ, hN, NatR.succ (TRedsT.refl (Der.succ ha)) (TRedsT.refl (Der.succ hb))
      (E.succ_cong hab') hr⟩
  have hn : ValidEq E Γ n n nat := valid_refl h.1
  have hm : ValidEq E Γ m m nat := valid_refl h.2.1
  exact ValidEq.intro (ValidTm.intro valid_natT (key hn)) (ValidTm.intro valid_natT (key hm))
    (key h)

theorem valid_succ {Γ : Ctx} {n : Tm} (h : ValidTm E Γ n nat) : ValidTm E Γ (succ n) nat :=
  (valid_succCong (valid_refl h)).1

end MLTT
