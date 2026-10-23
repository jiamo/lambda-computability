import Start.PTSExpansionCCOClFLimit
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Big round 2, run 2, item B1: a set-theoretic classifier for `CC^ω` with a hierarchy of
universes (row M29-EP-CCOMEGA)

`Start/PTSExpansionCCOClF.lean` reduces root β-invariance of an environment-based classifier
`clF D` to the β-law of its combinators, and `Start/PTSExpansionCCOClFLimit.lean` shows that the
law can only hold on *well-classified* arguments.  This module gives a concrete classifier in which
the law holds exactly there.

The class type is `ZFSet` (one Lean universe).  Kind-level functions are genuine set-theoretic
functions (graphs), so the class of `λK:Type ℓ. t` is the graph of `v ↦ class of t at v` over the
class of `Type ℓ`, and the class of a product is the set of dependent functions:

* `cU ℓ = V_(ω·(ℓ+1))` — the class of `Type ℓ`, a level-indexed hierarchy of von Neumann stages
  (`cU_mem_succ : cU ℓ ∈ cU (ℓ+1)`, `cU_mono`);
* `propC = 𝒫 {∅}` — the class of `Prop`, a single fixed set of (proof-irrelevant) truth values,
  `propC_mem_cU : propC ∈ cU 0`;
* `zfLam A f` — the graph of `f` on `A`; `zfApp F x` — the value of the graph `F` at `x`;
  `zfPi A f` — the dependent functions on `A` with values in `f`;
* `ccoD : ClfData ZFSet` and the well-classification predicate `ClfWC`: in every application
  `F U` the class of `U` lies in the domain of the class of `F`, and abstractions and products are
  well classified at every class of their binder;
* **`ccoClf_beta`** — for a well-classified redex, `clF ccoD ρ ((λA. b) U) = clF ccoD ρ (b[U/0])`.
* `zfApp_zfLam`, `mem_zfPi` — the restricted β-law and the membership law of products;
* `zfPi_mem_cU_zero` — `Type 0` (the class `V_ω`) is closed under dependent products over its
  members;
* `zfPi_not_mem_propC` — but a product into `Prop` is not classified inside `propC`, so the
  impredicative rule needs its own combinator.

What remains (see the notes): closure of `ClfWC` under substitution and β, the bound
`clF ρ K ∈ cU ℓ` for kinds `K : Type ℓ` (stages `V_(ω·(ℓ+1))` are not closed under dependent
products indexed by arbitrary sets, so this must use the rank of the syntactic family), and the
interpretation of types by candidates.
-/

set_option autoImplicit false

namespace PureTypeSystem.CCO

open ZFSet

attribute [local instance] Classical.allZFSetDefinable

/-- The graph of `f` on `A`. -/
noncomputable def zfLam (A : ZFSet) (f : ZFSet → ZFSet) : ZFSet := ZFSet.map f A

open Classical in
/-- The value of a graph `F` at `x` (`∅` if `x` is not in its domain). -/
noncomputable def zfApp (F x : ZFSet) : ZFSet :=
  if h : ∃ y, pair x y ∈ F then Classical.choose h else ∅

/-- The dependent functions on `A` with values in `f`. -/
noncomputable def zfPi (A : ZFSet) (f : ZFSet → ZFSet) : ZFSet :=
  ZFSet.sep (fun g => ∀ x ∈ A, ∃ y, pair x y ∈ g ∧ y ∈ f x)
    (funs A (⋃₀ ZFSet.image f A))

/-- The value at a point of a graph is the value of the function. -/
theorem eq_of_pair_mem_zfLam {A x y : ZFSet} {f : ZFSet → ZFSet}
    (h : pair x y ∈ zfLam A f) : y = f x := by
  simp only [zfLam, mem_map] at h
  obtain ⟨z, _, e⟩ := h
  obtain ⟨rfl, e2⟩ := pair_injective e
  exact e2.symm

/-- **The restricted β-law**: application of a graph to a point of its domain. -/
theorem zfApp_zfLam {A x : ZFSet} (f : ZFSet → ZFSet) (hx : x ∈ A) :
    zfApp (zfLam A f) x = f x := by
  have h : ∃ y, pair x y ∈ zfLam A f := ⟨f x, by
    simp only [zfLam, mem_map]; exact ⟨x, hx, rfl⟩⟩
  rw [zfApp, dif_pos h]
  exact eq_of_pair_mem_zfLam (Classical.choose_spec h)

/-- A point of the domain of `zfLam A f` is a point of `A`. -/
theorem mem_of_pair_mem_zfLam {A x y : ZFSet} {f : ZFSet → ZFSet}
    (h : pair x y ∈ zfLam A f) : x ∈ A := by
  simp only [zfLam, mem_map] at h
  obtain ⟨z, hz, e⟩ := h
  obtain ⟨rfl, -⟩ := pair_injective e
  exact hz

/-- Membership in a dependent product. -/
theorem mem_zfPi {A g : ZFSet} {f : ZFSet → ZFSet} :
    g ∈ zfPi A f ↔ IsFunc A (⋃₀ ZFSet.image f A) g ∧ ∀ x ∈ A, ∃ y, pair x y ∈ g ∧ y ∈ f x := by
  rw [zfPi, mem_sep, mem_funs]

/-- A graph whose values lie in the family is a dependent function. -/
theorem zfLam_mem_zfPi {A : ZFSet} {f g : ZFSet → ZFSet} (h : ∀ x ∈ A, g x ∈ f x) :
    zfLam A g ∈ zfPi A f := by
  rw [mem_zfPi]
  refine ⟨?_, fun x hx => ⟨g x, ?_, h x hx⟩⟩
  · rw [zfLam, map_isFunc]
    intro z hz
    exact mem_sUnion_of_mem (h z hz) (by rw [mem_image]; exact ⟨z, hz, rfl⟩)
  · simp only [zfLam, mem_map]; exact ⟨x, hx, rfl⟩

/-- **Application of a dependent function**: the value lies in the family. -/
theorem zfApp_mem_zfPi {A g x : ZFSet} {f : ZFSet → ZFSet} (hg : g ∈ zfPi A f) (hx : x ∈ A) :
    pair x (zfApp g x) ∈ g ∧ zfApp g x ∈ f x := by
  rw [mem_zfPi] at hg
  obtain ⟨⟨-, huniq⟩, hval⟩ := hg
  obtain ⟨y, hy, hyf⟩ := hval x hx
  have h : ∃ y, pair x y ∈ g := ⟨y, hy⟩
  have e : zfApp g x = y := by
    rw [zfApp, dif_pos h]
    exact (huniq x hx).unique (Classical.choose_spec h) hy
  rw [e]
  exact ⟨hy, hyf⟩

/-! ### The hierarchy of universes -/

/-- The class of `Type ℓ`: the von Neumann stage `V_(ω·(ℓ+1))`. -/
noncomputable def cU (ℓ : ℕ) : ZFSet := V_ (Ordinal.omega0 * ((ℓ : Ordinal) + 1))

/-- The class of `Prop`: the proof-irrelevant truth values `𝒫 {∅}`. -/
noncomputable def propC : ZFSet := powerset {∅}

theorem cU_mem_succ (ℓ : ℕ) : cU ℓ ∈ cU (ℓ + 1) := by
  rw [cU, cU, vonNeumann_mem_vonNeumann_iff]
  apply mul_lt_mul_of_pos_left _ Ordinal.omega0_pos
  push_cast
  exact lt_add_one _

theorem cU_mono {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') : cU ℓ ⊆ cU ℓ' := by
  rw [cU, cU, vonNeumann_subset_vonNeumann_iff]
  have : (ℓ : Ordinal) ≤ ℓ' := by exact_mod_cast h
  gcongr

theorem propC_mem_cU : propC ∈ cU 0 := by
  rw [cU, mem_vonNeumann, propC, rank_powerset, rank_singleton, rank_empty]
  simp only [Nat.cast_zero, zero_add, mul_one, Order.succ_eq_add_one]
  have : (1 : Ordinal) + 1 = ((2 : ℕ) : Ordinal) := by norm_num
  rw [this]
  exact Ordinal.natCast_lt_omega0 2

/-! ### The classifier -/

/-- **The set-theoretic classifier data for `CC^ω`.** -/
noncomputable def ccoD : ClfData ZFSet where
  prop := propC
  type := cU
  appF := zfApp
  lamF := zfLam
  piF := zfPi

/-- **Well-classification**: in every application the class of the argument lies in the domain
of the class of the function; binders are well classified at every class of their domain. -/
def ClfWC : (ℕ → ZFSet) → Expr CSrt → Prop
  | _, .var _ => True
  | _, .sort _ => True
  | ρ, .app F U => ClfWC ρ F ∧ ClfWC ρ U ∧ ∃ y, pair (clF ccoD ρ U) y ∈ clF ccoD ρ F
  | ρ, .lam A b => ClfWC ρ A ∧ ∀ v ∈ clF ccoD ρ A, ClfWC (envCons v ρ) b
  | ρ, .pi A B => ClfWC ρ A ∧ ∀ v ∈ clF ccoD ρ A, ClfWC (envCons v ρ) B

/-- **`CCO.ccoClf_beta`**: the classifier is invariant under a well-classified root β-step. -/
theorem ccoClf_beta {ρ : ℕ → ZFSet} {A b U : Expr CSrt} (h : ClfWC ρ (.app (.lam A b) U)) :
    clF ccoD ρ (.app (.lam A b) U) = clF ccoD ρ (b.instantiate U) := by
  obtain ⟨-, -, y, hy⟩ := h
  apply clF_beta_of
  exact zfApp_zfLam _ (mem_of_pair_mem_zfLam hy)

/-- The class of a well-classified redex's argument lies in the class of the binder. -/
theorem ClfWC.arg_mem {ρ : ℕ → ZFSet} {A b U : Expr CSrt} (h : ClfWC ρ (.app (.lam A b) U)) :
    clF ccoD ρ U ∈ clF ccoD ρ A := by
  obtain ⟨-, -, y, hy⟩ := h
  exact mem_of_pair_mem_zfLam hy

/-! ### The kind that blocked an inductive-recursive class type

`ΠK : (ΠY : Type 0. Y → Type 0). ΠY : Type 0. Πy : Y. K Y y → K Y y`: the value space of `K` is a
dependent product over codes of the same level.  In the set-theoretic classifier it is well
classified in every environment. -/

/-- The domain `ΠY : Type 0. Y → Type 0` of `K`. -/
def depDom : Expr CSrt := .pi (.sort (.type 0)) (.pi (.var 0) (.sort (.type 0)))

/-- `ΠK : (ΠY : Type 0. Y → Type 0). ΠY : Type 0. Πy : Y. K Y y → K Y y`. -/
def depKind : Expr CSrt :=
  .pi depDom (.pi (.sort (.type 0)) (.pi (.var 0)
    (.pi (.app (.app (.var 2) (.var 1)) (.var 0)) (.app (.app (.var 3) (.var 2)) (.var 1)))))

theorem clF_depDom (ρ : ℕ → ZFSet) :
    clF ccoD ρ depDom = zfPi (cU 0) (fun Y => zfPi Y (fun _ => cU 0)) := rfl

/-- **`depKind` is well classified in every environment.** -/
theorem depKind_wc (ρ : ℕ → ZFSet) : ClfWC ρ depKind := by
  refine ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩, fun k hk => ?_⟩
  rw [clF_depDom] at hk
  refine ⟨trivial, fun Y hY => ⟨trivial, fun y hy => ?_⟩⟩
  obtain ⟨hkY, hkYmem⟩ := zfApp_mem_zfPi hk hY
  obtain ⟨hkYy, -⟩ := zfApp_mem_zfPi hkYmem hy
  have hwc : ClfWC (envCons y (envCons Y (envCons k ρ)))
      (.app (.app (.var 2) (.var 1)) (.var 0)) :=
    ⟨⟨trivial, trivial, ⟨_, hkY⟩⟩, trivial, ⟨_, hkYy⟩⟩
  exact ⟨hwc, fun _ _ => ⟨⟨trivial, trivial, ⟨_, hkY⟩⟩, trivial, ⟨_, hkYy⟩⟩⟩

/-! ### Well-classification under renaming, substitution and β -/

/-- Well-classification commutes with renaming. -/
theorem ClfWC_rename (M : Expr CSrt) :
    ∀ (r : ℕ → ℕ) (ρ : ℕ → ZFSet), ClfWC ρ (M.rename r) ↔ ClfWC (ρ ∘ r) M := by
  induction M with
  | var n => intros; exact Iff.rfl
  | sort s => intros; exact Iff.rfl
  | app F U ihF ihU =>
    intro r ρ
    simp only [Expr.rename, ClfWC, ihF, ihU, clF_rename]
  | lam A b ihA ihb =>
    intro r ρ
    simp only [Expr.rename, ClfWC, ihA, ihb, clF_rename, envCons_liftRen]
  | pi A B ihA ihB =>
    intro r ρ
    simp only [Expr.rename, ClfWC, ihA, ihB, clF_rename, envCons_liftRen]

theorem ClfWC_liftSub {v : ZFSet} {ρ : ℕ → ZFSet} {σ : ℕ → Expr CSrt}
    (hσ : ∀ n, ClfWC ρ (σ n)) : ∀ n, ClfWC (envCons v ρ) (Expr.liftSub σ n) := by
  intro n
  cases n with
  | zero => exact trivial
  | succ n =>
    simp only [Expr.liftSub]
    rw [ClfWC_rename]
    exact hσ n

/-- **Well-classification under substitution** of well-classified terms. -/
theorem ClfWC_subst (M : Expr CSrt) :
    ∀ (σ : ℕ → Expr CSrt) (ρ : ℕ → ZFSet), (∀ n, ClfWC ρ (σ n)) →
      (ClfWC ρ (M.subst σ) ↔ ClfWC (fun n => clF ccoD ρ (σ n)) M) := by
  induction M with
  | var n =>
    intro σ ρ hσ
    simp only [Expr.subst, ClfWC, iff_true]
    exact hσ n
  | sort s => intros; exact Iff.rfl
  | app F U ihF ihU =>
    intro σ ρ hσ
    simp only [Expr.subst, ClfWC, ihF σ ρ hσ, ihU σ ρ hσ, clF_subst]
  | lam A b ihA ihb =>
    intro σ ρ hσ
    simp only [Expr.subst, ClfWC, ihA σ ρ hσ, clF_subst]
    refine and_congr Iff.rfl (forall₂_congr fun v _ => ?_)
    rw [ihb _ _ (ClfWC_liftSub hσ), clF_liftSub]
  | pi A B ihA ihB =>
    intro σ ρ hσ
    simp only [Expr.subst, ClfWC, ihA σ ρ hσ, clF_subst]
    refine and_congr Iff.rfl (forall₂_congr fun v _ => ?_)
    rw [ihB _ _ (ClfWC_liftSub hσ), clF_liftSub]

/-- Well-classification of an instance. -/
theorem ClfWC_instantiate {ρ : ℕ → ZFSet} {b U : Expr CSrt} (hU : ClfWC ρ U) :
    ClfWC ρ (b.instantiate U) ↔ ClfWC (envCons (clF ccoD ρ U) ρ) b := by
  rw [Expr.instantiate, ClfWC_subst b _ ρ (fun n => by cases n <;> first | exact hU | trivial)]
  have : (fun n => clF ccoD ρ (Expr.single U n)) = envCons (clF ccoD ρ U) ρ := by
    funext n; cases n <;> rfl
  rw [this]

/-- **A well-classified root β-redex has a well-classified contractum.** -/
theorem ClfWC.beta {ρ : ℕ → ZFSet} {A b U : Expr CSrt} (h : ClfWC ρ (.app (.lam A b) U)) :
    ClfWC ρ (b.instantiate U) := by
  have hmem := h.arg_mem
  obtain ⟨⟨-, hb⟩, hU, -⟩ := h
  exact (ClfWC_instantiate hU).2 (hb _ hmem)

/-! ### `Type 0` is closed under dependent products

The class `cU 0 = V_ω` consists of hereditarily finite sets, so a product over a member with values
in `cU 0` stays in `cU 0` (`zfPi_mem_cU_zero`): the (Type 0, Type 0, Type 0) and
(Prop, Type 0, Type 0) rules at the level of classes. -/

theorem mem_cU_zero {x : ZFSet} : x ∈ cU 0 ↔ rank x < Ordinal.omega0 := by
  rw [cU, mem_vonNeumann]; simp

theorem finite_of_mem_cU_zero {A : ZFSet} (h : A ∈ cU 0) : Set.Finite {x | x ∈ A} := by
  rw [mem_cU_zero, Ordinal.lt_omega0] at h
  obtain ⟨n, hn⟩ := h
  have hsub : A ⊆ V_ (n : Ordinal) := subset_vonNeumann.2 hn.le
  have hcard : card A < Cardinal.aleph0 := by
    refine (card_mono hsub).trans_lt ?_
    rw [card_vonNeumann, Cardinal.preBeth_nat]
    exact Cardinal.natCast_lt_aleph0
  have : Finite (Shrink A) := Cardinal.lt_aleph0_iff_finite.1 hcard
  have : Finite A := Finite.of_equiv _ (equivShrink A).symm
  exact Set.finite_coe_iff.mp this

theorem succ_lt_omega0' {o : Ordinal} (h : o < Ordinal.omega0) : Order.succ o < Ordinal.omega0 :=
  Ordinal.isSuccLimit_omega0.succ_lt h

theorem rank_pair_le (a b : ZFSet) :
    rank (pair a b) ≤ Order.succ (Order.succ (max (rank a) (rank b))) := by
  show rank ({{a}, {a, b}} : ZFSet) ≤ _
  rw [rank_pair, rank_singleton, rank_pair]
  apply max_le
  · gcongr; exact le_max_left _ _
  · apply Order.succ_le_succ
    exact (max_le (Order.succ_le_succ (le_max_left _ _)) (Order.succ_le_succ (le_max_right _ _)))

theorem rank_prod_lt {A B : ZFSet} (hA : rank A < Ordinal.omega0) (hB : rank B < Ordinal.omega0) :
    rank (prod A B) < Ordinal.omega0 := by
  have hM : max (rank A) (rank B) < Ordinal.omega0 := max_lt hA hB
  refine lt_of_le_of_lt (rank_le_iff.2 fun z hz => ?_) (succ_lt_omega0' (succ_lt_omega0' hM))
  rw [mem_prod] at hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  refine lt_of_le_of_lt (rank_pair_le a b) ?_
  apply Order.succ_lt_succ
  apply Order.succ_lt_succ
  exact max_lt ((rank_lt_of_mem ha).trans_le (le_max_left _ _))
    ((rank_lt_of_mem hb).trans_le (le_max_right _ _))

/-- **`Type 0` is closed under dependent products over its members.** -/
theorem zfPi_mem_cU_zero {A : ZFSet} {f : ZFSet → ZFSet} (hA : A ∈ cU 0)
    (hf : ∀ v ∈ A, f v ∈ cU 0) : zfPi A f ∈ cU 0 := by
  have hfin := finite_of_mem_cU_zero hA
  set S := (fun v => rank (f v)) '' {x | x ∈ A} with hSdef
  have hS : S.Finite := hfin.image _
  have hb : sSup S < Ordinal.omega0 := by
    rcases S.eq_empty_or_nonempty with he | hne
    · rw [he, csSup_empty]; exact Ordinal.omega0_pos
    · obtain ⟨v, hv, hv'⟩ := hne.csSup_mem hS
      rw [← hv']; exact mem_cU_zero.1 (hf v hv)
  have hle : ∀ v ∈ A, rank (f v) ≤ sSup S := fun v hv =>
    le_csSup (Set.Finite.bddAbove hS) ⟨v, hv, rfl⟩
  have hB : rank (⋃₀ ZFSet.image f A) < Ordinal.omega0 := by
    refine lt_of_le_of_lt (rank_sUnion_le _) (lt_of_le_of_lt ?_ (succ_lt_omega0' hb))
    refine rank_le_iff.2 fun y hy => ?_
    rw [mem_image] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    exact Order.lt_succ_of_le (hle v hv)
  have hP := rank_prod_lt (mem_cU_zero.1 hA) hB
  rw [mem_cU_zero]
  refine lt_of_le_of_lt (rank_mono (y := powerset (prod A (⋃₀ ZFSet.image f A))) ?_) ?_
  · intro g hg
    rw [mem_powerset]
    exact ((mem_zfPi.1 hg).1).1
  · rw [rank_powerset]; exact succ_lt_omega0' hP


/-! ### Impredicative products need their own combinator

With `piF = zfPi`, the class of a product into `Prop` is a set of functions, not a truth value:
for a domain class `{∅}` and the constant family `{∅}` (a true proposition), the product
`zfPi {∅} (fun _ => {∅})` is not in `propC`.  So the typed invariant (the class of `Πx:A. B` with
`B : Prop` lies in the class of `Prop`) fails for `ccoD`; the impredicative rule `(s, Prop, Prop)`
needs a special case of `piF` (see the notes). -/

theorem zfPi_not_mem_propC : zfPi {∅} (fun _ => {∅}) ∉ propC := by
  intro h
  rw [propC, mem_powerset] at h
  have hmem : zfLam {∅} (fun _ => ∅) ∈ zfPi {∅} (fun _ => {∅}) :=
    zfLam_mem_zfPi fun _ _ => mem_singleton.2 rfl
  have h0 : zfLam {∅} (fun _ => ∅) = ∅ := mem_singleton.1 (h hmem)
  have hp : pair ∅ ∅ ∈ zfLam {∅} (fun _ => ∅) := by
    simp only [zfLam, mem_map]
    exact ⟨∅, mem_singleton.2 rfl, rfl⟩
  rw [h0] at hp
  exact notMem_empty _ hp

end PureTypeSystem.CCO
