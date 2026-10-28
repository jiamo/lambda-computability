/-
**MLTT and the absorbed pure type systems** — milestone M30 (`M30-UNIFY-PTS-MLTT`).

The Π-and-universe fragment of MLTT is the pure type system `MLTT.mlttPTS` (sorts `ℕ`, axioms
`l : l+1`, rules `(i, j, max i j)`) of the absorbed development `Start/PTS*.lean` (family 245).
This module connects the two.

* `MLTT.toTm` — erasure of the domain annotations of abstractions, `Expr ℕ → Tm`; it commutes
  with renaming, substitution and instantiation, and a `β`-step of the PTS is erased to at most
  one step of full reduction (`toTm_reduces`);
* `MLTT.converts_tyEq` — conversion in the PTS of two types whose erasures are well formed is
  judgemental equality of the erasures (through the confluence of the absorbed development,
  `PureTypeSystem.Reduces.confluent`, and subject reduction `FSteps.tyEq`);
* **`MLTT.HasType.toTm`** — **the erasure is sound**: a typing of `mlttPTS` is a typing of MLTT;
* **`MLTT.Legal.toTm_wn`** — the erasure of every legal term of `mlttPTS` has a normal form
  (by `MLTT.HasTy.wn`, `Start/MLTTNormalize.lean`);
* `MLTT.FSteps.liftPTS` — a reduction of an erasure lifts to a reduction in the PTS; hence
  **`MLTT.Legal.reduces_nf`**: every legal term reduces to a legal term with a normal erasure,
  where every remaining redex lies inside a domain annotation (`MLTT.normal_of_nf`);
* `MLTT.AnnotationWN` — the remaining statement: legal terms with normal erasure are weakly
  normalizing; **`MLTT.mlttPTS_sn_of_annotationWN`** — it implies system-wide weak normalization
  and, by the absorbed `PureTypeSystem.weak_implies_strong`, **strong normalization of
  `mlttPTS`**.
-/

import Start.MLTTNormalize
import Start.PTSNormalization

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace MLTT

open Tm

/-- **The PTS of the Π-and-universe fragment of MLTT**: sorts `ℕ`, axioms `l : l+1`, rules
`(i, j, max i j)`. -/
def mlttPTS : PureTypeSystem.Specification ℕ where
  axioms l m := m = l + 1
  rule i j k := k = max i j

/-- **Erasure** of the domain annotations of abstractions. -/
def toTm : PureTypeSystem.Expr ℕ → Tm
  | .var n => Tm.var n
  | .sort l => Tm.univ l
  | .app f a => Tm.app (toTm f) (toTm a)
  | .lam _ b => Tm.lam (toTm b)
  | .pi A B => Tm.pi (toTm A) (toTm B)

/-- Erasure of a context. -/
def toCtx (Γ : List (PureTypeSystem.Expr ℕ)) : Ctx := Γ.map toTm

/-! ### Erasure commutes with renaming and substitution -/

theorem liftRen_eq_upr (ρ : ℕ → ℕ) : PureTypeSystem.Expr.liftRen ρ = upr ρ := by
  funext n
  cases n <;> rfl

theorem toTm_rename (M : PureTypeSystem.Expr ℕ) :
    ∀ ρ : ℕ → ℕ, toTm (M.rename ρ) = MLTT.rename ρ (toTm M) := by
  induction M with
  | var n => intro ρ; rfl
  | sort s => intro ρ; rfl
  | app f a ihf iha => intro ρ; simp only [PureTypeSystem.Expr.rename, toTm, ihf, iha, rename_app]
  | lam A b _ ihb =>
      intro ρ
      simp only [PureTypeSystem.Expr.rename, toTm, ihb, rename_lam, liftRen_eq_upr]
  | pi A B ihA ihB =>
      intro ρ
      simp only [PureTypeSystem.Expr.rename, toTm, ihA, ihB, rename_pi, liftRen_eq_upr]

theorem toTm_liftSub (σ : ℕ → PureTypeSystem.Expr ℕ) :
    (fun n => toTm (PureTypeSystem.Expr.liftSub σ n)) = up (fun k => toTm (σ k)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [PureTypeSystem.Expr.liftSub, toTm_rename, up_succ]

theorem toTm_subst (M : PureTypeSystem.Expr ℕ) :
    ∀ σ : ℕ → PureTypeSystem.Expr ℕ, toTm (M.subst σ) = MLTT.subst (fun n => toTm (σ n)) (toTm M) := by
  induction M with
  | var n => intro σ; rfl
  | sort s => intro σ; rfl
  | app f a ihf iha => intro σ; simp only [PureTypeSystem.Expr.subst, toTm, ihf, iha, subst_app]
  | lam A b _ ihb =>
      intro σ
      simp only [PureTypeSystem.Expr.subst, toTm, ihb, subst_lam, toTm_liftSub]
  | pi A B ihA ihB =>
      intro σ
      simp only [PureTypeSystem.Expr.subst, toTm, ihA, ihB, subst_pi, toTm_liftSub]

theorem toTm_instantiate (b a : PureTypeSystem.Expr ℕ) :
    toTm (b.instantiate a) = (toTm b)[toTm a] := by
  rw [PureTypeSystem.Expr.instantiate, toTm_subst]
  show _ = MLTT.subst (scons (toTm a) MLTT.ids) (toTm b)
  exact subst_congr (fun n => by cases n <;> rfl) _

/-! ### Reduction and conversion -/

theorem toTm_beta {M N : PureTypeSystem.Expr ℕ} (h : PureTypeSystem.Beta M N) :
    FSteps (toTm M) (toTm N) := by
  induction h with
  | head A b a =>
      show FSteps (Tm.app (Tm.lam (toTm b)) (toTm a)) _
      rw [toTm_instantiate]
      exact .single (FStep.beta _ _)
  | app_left _ ih => exact FSteps.app ih .refl
  | app_right _ ih => exact FSteps.app .refl ih
  | lam_domain _ _ => exact .refl
  | lam_body _ ih => exact FSteps.lam ih
  | pi_domain _ ih => exact FSteps.pi ih .refl
  | pi_body _ ih => exact FSteps.pi .refl ih

theorem toTm_reduces {M N : PureTypeSystem.Expr ℕ} (h : PureTypeSystem.Reduces M N) :
    FSteps (toTm M) (toTm N) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.trans (toTm_beta hs)

/-- Conversion of the absorbed PTS meets in a common reduct (Church–Rosser). -/
theorem converts_join {M N : PureTypeSystem.Expr ℕ} (h : PureTypeSystem.Converts M N) :
    Relation.Join PureTypeSystem.Reduces M N := by
  induction h with
  | rel x y hxy => exact ⟨y, .single hxy, .refl⟩
  | refl x => exact ⟨x, .refl, .refl⟩
  | symm x y _ ih =>
      obtain ⟨z, h₁, h₂⟩ := ih
      exact ⟨z, h₂, h₁⟩
  | trans x y z _ _ ih₁ ih₂ =>
      obtain ⟨u, hxu, hyu⟩ := ih₁
      obtain ⟨v, hyv, hzv⟩ := ih₂
      obtain ⟨w, huw, hvw⟩ := PureTypeSystem.Reduces.confluent hyu hyv
      exact ⟨w, hxu.trans huw, hzv.trans hvw⟩

/-- **Conversion is judgemental equality of the erasures**, for well-formed erasures. -/
theorem converts_tyEq {Γ : Ctx} {A B : PureTypeSystem.Expr ℕ} (h : PureTypeSystem.Converts A B)
    (hA : WfTy Γ (toTm A)) (hB : WfTy Γ (toTm B)) : TyEq Γ (toTm A) (toTm B) := by
  obtain ⟨C, hAC, hBC⟩ := converts_join h
  exact Der.transT ((toTm_reduces hAC).tyEq hA) (Der.symmT ((toTm_reduces hBC).tyEq hB))

/-! ### Soundness of the erasure -/

/-- **The erasure is sound**: a typing of `mlttPTS` is a typing of MLTT, in a well-formed
context. -/
theorem HasType.toTm {Γ : List (PureTypeSystem.Expr ℕ)} {M A : PureTypeSystem.Expr ℕ}
    (h : PureTypeSystem.HasType mlttPTS Γ M A) :
    WfCtx (toCtx Γ) ∧ HasTy (toCtx Γ) (MLTT.toTm M) (MLTT.toTm A) := by
  induction h with
  | @ax s t hst =>
      obtain rfl : t = s + 1 := hst
      exact ⟨Der.nil, Der.univU s Der.nil⟩
  | var _ ih =>
      have hwf : WfCtx (MLTT.toTm _ :: toCtx _) := Der.cons ih.1 (Der.el ih.2)
      refine ⟨hwf, ?_⟩
      rw [toTm_rename]
      exact Der.var hwf (Lookup.zero _ _)
  | weaken _ _ ihM ihA =>
      have hwf : WfCtx (MLTT.toTm _ :: toCtx _) := Der.cons ihA.1 (Der.el ihA.2)
      refine ⟨hwf, ?_⟩
      rw [toTm_rename, toTm_rename]
      exact ihM.2.weaken hwf
  | product _ _ hr ihA ihB =>
      obtain rfl := hr
      exact ⟨ihA.1, Der.piU ihA.2 ihB.2⟩
  | abstraction _ _ ihb ihPi =>
      obtain ⟨i, j, hA, -, -⟩ := ihPi.2.inv_pi
      exact ⟨ihPi.1, Der.lam (Der.el hA) ihb.2⟩
  | application _ _ ihf iha =>
      refine ⟨ihf.1, ?_⟩
      rw [toTm_instantiate]
      exact Der.app ihf.2 iha.2
  | conversion _ _ hc ihM ihB =>
      exact ⟨ihM.1, Der.conv ihM.2 (converts_tyEq hc ihM.2.wfTy (Der.el ihB.2))⟩

/-- **The erasure of a legal term has a normal form.** -/
theorem Legal.toTm_wn {Γ : List (PureTypeSystem.Expr ℕ)} {M : PureTypeSystem.Expr ℕ}
    (h : PureTypeSystem.Legal mlttPTS Γ M) : WN (MLTT.toTm M) := by
  obtain ⟨A, hM | hA⟩ := h
  · exact (HasType.toTm hM).2.wn
  · exact (HasType.toTm hA).2.wfTy.wn

/-! ### Lifting reductions of erasures -/

theorem toTm_eq_app {M : PureTypeSystem.Expr ℕ} {x y : Tm} (h : MLTT.toTm M = Tm.app x y) :
    ∃ f a, M = .app f a ∧ MLTT.toTm f = x ∧ MLTT.toTm a = y := by
  cases M <;> simp [MLTT.toTm] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem toTm_eq_lam {M : PureTypeSystem.Expr ℕ} {x : Tm} (h : MLTT.toTm M = Tm.lam x) :
    ∃ A b, M = .lam A b ∧ MLTT.toTm b = x := by
  cases M <;> simp [MLTT.toTm] at h
  exact ⟨_, _, rfl, h⟩

theorem toTm_eq_pi {M : PureTypeSystem.Expr ℕ} {x y : Tm} (h : MLTT.toTm M = Tm.pi x y) :
    ∃ A B, M = .pi A B ∧ MLTT.toTm A = x ∧ MLTT.toTm B = y := by
  cases M <;> simp [MLTT.toTm] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

theorem toTm_ne_natrec {M : PureTypeSystem.Expr ℕ} {P z s n : Tm} :
    MLTT.toTm M ≠ Tm.natrec P z s n := by
  cases M <;> simp [MLTT.toTm]

theorem toTm_ne_succ {M : PureTypeSystem.Expr ℕ} {n : Tm} : MLTT.toTm M ≠ Tm.succ n := by
  cases M <;> simp [MLTT.toTm]

theorem toTm_ne_emptyrec {M : PureTypeSystem.Expr ℕ} {P e : Tm} : MLTT.toTm M ≠ Tm.emptyrec P e := by
  cases M <;> simp [MLTT.toTm]

/-- A step of an erasure is the erasure of a step of the PTS. -/
theorem FStep.liftPTS {x u : Tm} (h : FStep x u) :
    ∀ {M : PureTypeSystem.Expr ℕ}, MLTT.toTm M = x →
      ∃ M', PureTypeSystem.Beta M M' ∧ MLTT.toTm M' = u := by
  induction h with
  | beta b a =>
      intro M e
      obtain ⟨f, a₀, rfl, ef, rfl⟩ := toTm_eq_app e
      obtain ⟨A, b₀, rfl, rfl⟩ := toTm_eq_lam ef
      exact ⟨_, .head A b₀ a₀, toTm_instantiate b₀ a₀⟩
  | natrecZero => intro M e; exact absurd e toTm_ne_natrec
  | natrecSucc => intro M e; exact absurd e toTm_ne_natrec
  | piL G _ ih =>
      intro M e
      obtain ⟨A, B, rfl, rfl, rfl⟩ := toTm_eq_pi e
      obtain ⟨A', hA, rfl⟩ := ih rfl
      exact ⟨_, .pi_domain hA, rfl⟩
  | piR F _ ih =>
      intro M e
      obtain ⟨A, B, rfl, rfl, rfl⟩ := toTm_eq_pi e
      obtain ⟨B', hB, rfl⟩ := ih rfl
      exact ⟨_, .pi_body hB, rfl⟩
  | lam _ ih =>
      intro M e
      obtain ⟨A, b, rfl, rfl⟩ := toTm_eq_lam e
      obtain ⟨b', hb, rfl⟩ := ih rfl
      exact ⟨_, .lam_body hb, rfl⟩
  | appL a _ ih =>
      intro M e
      obtain ⟨f, a₀, rfl, rfl, rfl⟩ := toTm_eq_app e
      obtain ⟨f', hf, rfl⟩ := ih rfl
      exact ⟨_, .app_left hf, rfl⟩
  | appR f _ ih =>
      intro M e
      obtain ⟨f₀, a, rfl, rfl, rfl⟩ := toTm_eq_app e
      obtain ⟨a', ha, rfl⟩ := ih rfl
      exact ⟨_, .app_right ha, rfl⟩
  | succ => intro M e; exact absurd e toTm_ne_succ
  | natrecP => intro M e; exact absurd e toTm_ne_natrec
  | natrecZ => intro M e; exact absurd e toTm_ne_natrec
  | natrecS => intro M e; exact absurd e toTm_ne_natrec
  | natrecN => intro M e; exact absurd e toTm_ne_natrec
  | emptyrecP => intro M e; exact absurd e toTm_ne_emptyrec
  | emptyrecE => intro M e; exact absurd e toTm_ne_emptyrec

theorem FSteps.liftPTS {M : PureTypeSystem.Expr ℕ} {u : Tm} (h : FSteps (MLTT.toTm M) u) :
    ∃ M', PureTypeSystem.Reduces M M' ∧ MLTT.toTm M' = u := by
  generalize e : MLTT.toTm M = x at h
  induction h with
  | refl => exact ⟨M, .refl, e⟩
  | tail _ hs ih =>
      obtain ⟨M₁, h₁, rfl⟩ := ih
      obtain ⟨M₂, h₂, rfl⟩ := hs.liftPTS rfl
      exact ⟨M₂, h₁.tail h₂, rfl⟩

/-- A sort does not reduce. -/
theorem reduces_sort {s : ℕ} {M : PureTypeSystem.Expr ℕ}
    (h : PureTypeSystem.Reduces (.sort s) M) : M = .sort s := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; cases hs

/-- Reducts of legal terms are legal (the absorbed subject reduction and regularity). -/
theorem Legal.reduces {Γ : List (PureTypeSystem.Expr ℕ)} {M M' : PureTypeSystem.Expr ℕ}
    (h : PureTypeSystem.Legal mlttPTS Γ M) (hr : PureTypeSystem.Reduces M M') :
    PureTypeSystem.Legal mlttPTS Γ M' := by
  obtain ⟨A, hM | hA⟩ := h
  · exact ⟨A, .inl (hM.subject_reduces hr)⟩
  · rcases hA.regularity with ⟨s, rfl⟩ | ⟨s, hs⟩
    · rw [reduces_sort hr]
      exact ⟨A, .inr hA⟩
    · exact ⟨_, .inl (hs.subject_reduces hr)⟩

/-- **Every legal term reduces to a legal term with a normal erasure.** -/
theorem Legal.reduces_nf {Γ : List (PureTypeSystem.Expr ℕ)} {M : PureTypeSystem.Expr ℕ}
    (h : PureTypeSystem.Legal mlttPTS Γ M) :
    ∃ M', PureTypeSystem.Reduces M M' ∧ PureTypeSystem.Legal mlttPTS Γ M' ∧ Nf (MLTT.toTm M') := by
  obtain ⟨n, hn, hnf⟩ := Legal.toTm_wn h
  obtain ⟨M', hMM', rfl⟩ := FSteps.liftPTS hn
  exact ⟨M', hMM', Legal.reduces h hMM', hnf⟩

/-! ### Normal forms with annotations -/

/-- Every domain annotation is normal. -/
def AnnNormal : PureTypeSystem.Expr ℕ → Prop
  | .var _ => True
  | .sort _ => True
  | .app f a => AnnNormal f ∧ AnnNormal a
  | .lam A b => PureTypeSystem.Normal A ∧ AnnNormal b
  | .pi A B => AnnNormal A ∧ AnnNormal B

/-- **A term with a normal erasure and normal annotations is normal**: the redexes of a term with
a normal erasure lie inside domain annotations. -/
theorem normal_of_nf : ∀ (M : PureTypeSystem.Expr ℕ), Nf (MLTT.toTm M) → AnnNormal M →
    PureTypeSystem.Normal M := by
  intro M
  induction M with
  | var n => intro _ _ N hb; cases hb
  | sort s => intro _ _ N hb; cases hb
  | app f a ihf iha =>
      intro hn ha N hb
      cases hn with
      | ne hne =>
          cases hne with
          | app hf hapart =>
              cases hb with
              | head => cases hf
              | app_left h => exact ihf (NfB.ne hf) ha.1 _ h
              | app_right h => exact iha hapart ha.2 _ h
  | lam A b _ ihb =>
      intro hn ha N hb
      cases hn with
      | lam hb' =>
          cases hb with
          | lam_domain h => exact ha.1 _ h
          | lam_body h => exact ihb hb' ha.2 _ h
      | ne hne => cases hne
  | pi A B ihA ihB =>
      intro hn ha N hb
      cases hn with
      | pi hA hB =>
          cases hb with
          | pi_domain h => exact ihA hA ha.1 _ h
          | pi_body h => exact ihB hB ha.2 _ h
      | ne hne => cases hne

/-! ### Strong normalization of `mlttPTS`, from the annotations -/

/-- **The remaining statement**: legal terms of `mlttPTS` whose erasure is normal are weakly
normalizing (their redexes all lie inside domain annotations). -/
def AnnotationWN : Prop :=
  ∀ (Γ : List (PureTypeSystem.Expr ℕ)) (M : PureTypeSystem.Expr ℕ),
    PureTypeSystem.ValidContext mlttPTS Γ → PureTypeSystem.Legal mlttPTS Γ M →
      Nf (MLTT.toTm M) → PureTypeSystem.WeaklyNormalizing M

theorem mlttPTS_wn_of_annotationWN (h : AnnotationWN) :
    PureTypeSystem.SystemWeaklyNormalizing mlttPTS := by
  intro Γ hΓ M hM
  obtain ⟨M', hMM', hM', hnf⟩ := Legal.reduces_nf hM
  obtain ⟨N, hN, hNn⟩ := h Γ M' hΓ hM' hnf
  exact ⟨N, hMM'.trans hN, hNn⟩

/-- **Strong normalization of `mlttPTS`**, from the normalization of annotations, by the absorbed
theorem `PureTypeSystem.weak_implies_strong`. -/
theorem mlttPTS_sn_of_annotationWN (h : AnnotationWN) :
    PureTypeSystem.SystemStronglyNormalizing mlttPTS :=
  PureTypeSystem.weak_implies_strong _ (mlttPTS_wn_of_annotationWN h)

end MLTT
