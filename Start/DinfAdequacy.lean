/-
Adequacy of Scott's `D∞` for the untyped lambda calculus.

`Start/ScottDinfModel.lean` interprets the untyped calculus in the inverse limit `D∞` and proves
the interpretation *sound* for βη, and `Start/DinfHnf.lean` proves the easy converse: a head
normalizable term is somewhere different from the least element.  This file proves **adequacy**:
a term whose denotation is not the least element — in any environment at all — has a head normal
form.  Together the two give `ScottDinf.ddenot_eq_botDinf_iff_not_hasHnf`.

The proof is the classical computability argument, carried out along the *tower*
`D₀ = Bool`, `Dₙ₊₁ = [Dₙ →𝒄 Dₙ]` rather than on a single reflexive object: the level of the tower
is what makes the logical relation well founded, since an application at level `n+1` is a value
at level `n`.

* `ScottDinf.RelD n z t` — the term `t` *realizes* the stage-`n` value `z`.  At level `0` a
  nonbottom value means that `t` head normalizes *after any number of arguments*; at level `n+1`
  it means that applying `t` to a realizer of `x` realizes `toFn z x`.  The stronger level-`0`
  clause is what makes the relation compatible with the embedding `emb`.
* `ScottDinf.relD_emb`, `ScottDinf.relD_prj` — compatibility with the embedding–projection pairs,
  proved by simultaneous induction on the level.  The projection case is where
  `Lambda.HasHnf.app_left` of `Start/HeadReduction.lean` is used.
* `ScottDinf.relD_ωSup` — the relation is admissible (closed under suprema of chains), which is
  what the application map `Φ`, a supremum of finite-stage approximations, needs.
* `ScottDinf.realD_substEnv` — the fundamental lemma.
* `ScottDinf.hasHnf_of_ddenot_ne_botDinf` — **adequacy**.
-/

import Start.DinfHnf
import Start.ParallelSubst
import Start.GraphObs

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace Lambda

/-- A neutral term applied to a list of arguments is neutral. -/
theorem Neutral.appList {t : Lambda} (h : Neutral t) : ∀ args : List Lambda,
    Neutral (Lambda.appList t args) := by
  intro args
  induction args generalizing t with
  | nil => exact h
  | cons a rest ih => exact ih (Neutral.app a h)

end Lambda

namespace ScottDinf

open Lambda

noncomputable section

------------------------------------------------------------------------
-- The computability relation on the stages of the tower
------------------------------------------------------------------------

/-- `RelD n z t`: the term `t` realizes the stage-`n` value `z`.

At the base of the tower a nonbottom value means that `t` has a head normal form after being
applied to any list of arguments; at level `n+1` a value is a function, and realizing it means
that applying `t` to a realizer of `x` realizes the value at `x`.  Arguments are required to be
realizers *in every lifting*, which is what makes the relation stable under the shift that de
Bruijn parallel substitution performs at a binder. -/
def RelD : ∀ (n : ℕ), D n → Lambda → Prop
  | 0, z, t => z ≠ botD 0 → ∀ args : List Lambda, Lambda.HasHnf (Lambda.appList t args)
  | (n + 1), f, t =>
      ∀ (x : D n) (u : Lambda), (∀ k : ℕ, RelD n x (Lambda.lift k 0 u)) →
        RelD n (toFn f x) (Lambda.app t u)

/-- A term realizes a stage-`n` value *stably* when all of its liftings do. -/
def RelArg (n : ℕ) (x : D n) (u : Lambda) : Prop := ∀ k : ℕ, RelD n x (Lambda.lift k 0 u)

theorem relD_zero_iff {z : D 0} {t : Lambda} :
    RelD 0 z t ↔ (z ≠ botD 0 → ∀ args : List Lambda, HasHnf (appList t args)) := Iff.rfl

theorem relD_succ_iff {n : ℕ} {f : D (n + 1)} {t : Lambda} :
    RelD (n + 1) f t ↔ ∀ (x : D n) (u : Lambda), RelArg n x u → RelD n (toFn f x) (app t u) :=
  Iff.rfl

/-- The least element of a stage is realized by every term. -/
theorem relD_botD : ∀ (n : ℕ) (t : Lambda), RelD n (botD n) t := by
  intro n
  induction n with
  | zero => intro t h; exact absurd rfl h
  | succ n ih =>
      intro t
      rw [relD_succ_iff]
      intro x u _
      rw [toFn_botD]
      exact ih _

/-- Realizability is inherited backwards along a reduction. -/
theorem relD_expand : ∀ (n : ℕ) (z : D n) {t t' : Lambda}, Lambda.reduces t t' →
    RelD n z t' → RelD n z t := by
  intro n
  induction n with
  | zero =>
      intro z t t' hr h hz args
      exact HasHnf.of_reduces (reduces_appList hr args) (h hz args)
  | succ n ih =>
      intro z t t' hr h
      rw [relD_succ_iff]
      intro x u hu
      exact ih _ (Lambda.reduces_app_left hr) (h x u hu)

/-- Every neutral term realizes every value of every stage. -/
theorem relD_of_neutral : ∀ (n : ℕ) (z : D n) {t : Lambda}, Neutral t → RelD n z t := by
  intro n
  induction n with
  | zero => intro z t hn _ args; exact hasHnf_of_neutral (hn.appList args)
  | succ n ih =>
      intro z t hn
      rw [relD_succ_iff]
      intro x u _
      exact ih _ (Neutral.app u hn)

theorem relArg_of_neutral (n : ℕ) (x : D n) {u : Lambda} (h : Neutral u) : RelArg n x u :=
  fun k => relD_of_neutral n x (h.lift k 0)

/-- **Extracting a head normal form**: a term realizing a nonbottom value has a head normal
form. -/
theorem hasHnf_of_relD : ∀ (n : ℕ) (z : D n) (t : Lambda), RelD n z t → z ≠ botD n →
    HasHnf t := by
  intro n
  induction n with
  | zero =>
      intro z t h hz
      simpa [appList_nil] using h hz []
  | succ n ih =>
      intro f t h hf
      have hex : ∃ x : D n, toFn f x ≠ botD n := by
        by_contra hc
        push Not at hc
        exact hf (toFn_ext (fun x => by rw [hc x, toFn_botD]))
      obtain ⟨x, hx⟩ := hex
      have hrel : RelD n (toFn f x) (app t (Lambda.var 0)) :=
        h x (Lambda.var 0) (relArg_of_neutral n x (Neutral.var 0))
      exact (ih _ _ hrel hx).app_left

------------------------------------------------------------------------
-- Compatibility with the embedding–projection pairs
------------------------------------------------------------------------

/-- Realizability transfers along the embedding and the projection of the tower.  The two
statements are proved by simultaneous induction on the level. -/
theorem relD_emb_prj : ∀ n : ℕ,
    (∀ (z : D n) (t : Lambda), RelD n z t → RelD (n + 1) (emb n z) t) ∧
      (∀ (f : D (n + 1)) (t : Lambda), RelD (n + 1) f t → RelD n (prj n f) t) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro z t h
        rw [relD_succ_iff]
        intro x u _
        rw [emb_zero_apply]
        intro hz args
        have := h hz (u :: args)
        rwa [appList_cons] at this
      · intro f t h
        rw [prj_zero_apply]
        intro hz args
        cases args with
        | nil =>
            have hrel : RelD 0 (toFn f (botD 0)) (app t (Lambda.var 0)) :=
              h (botD 0) (Lambda.var 0) (fun k => relD_botD 0 _)
            have := hrel hz []
            simpa [appList_nil] using this.app_left
        | cons a rest =>
            have hrel : RelD 0 (toFn f (botD 0)) (app t a) :=
              h (botD 0) a (fun k => relD_botD 0 _)
            have := hrel hz rest
            rwa [← appList_cons] at this
  | succ n ih =>
      obtain ⟨hemb, hprj⟩ := ih
      constructor
      · intro z t h
        rw [relD_succ_iff]
        intro x u hu
        rw [emb_succ_apply]
        refine hemb _ _ ?_
        exact h (prj n x) u (fun k => hprj _ _ (hu k))
      · intro f t h
        rw [relD_succ_iff]
        intro x u hu
        rw [prj_succ_apply]
        refine hprj _ _ ?_
        exact h (emb n x) u (fun k => hemb _ _ (hu k))

theorem relD_emb {n : ℕ} {z : D n} {t : Lambda} (h : RelD n z t) : RelD (n + 1) (emb n z) t :=
  (relD_emb_prj n).1 z t h

theorem relD_prj {n : ℕ} {f : D (n + 1)} {t : Lambda} (h : RelD (n + 1) f t) :
    RelD n (prj n f) t :=
  (relD_emb_prj n).2 f t h

------------------------------------------------------------------------
-- Admissibility
------------------------------------------------------------------------

/-- Realizability is closed under suprema of chains. -/
theorem relD_ωSup : ∀ (n : ℕ) (c : Chain (D n)) (t : Lambda), (∀ i, RelD n (c i) t) →
    RelD n (ωSup c) t := by
  intro n
  induction n with
  | zero =>
      intro c t h hz args
      have hex : ∃ i, c i ≠ botD 0 := by
        by_contra hc
        push Not at hc
        exact hz (le_antisymm (ωSup_le c (botD 0) (fun i => le_of_eq (hc i))) (botD_le 0 _))
      obtain ⟨i, hi⟩ := hex
      exact h i hi args
  | succ n ih =>
      intro c t h
      rw [relD_succ_iff]
      intro x u hu
      rw [toFn_ωSup]
      exact ih _ _ (fun i => h i x u hu)

------------------------------------------------------------------------
-- Moving between the stages of an element of `D∞`
------------------------------------------------------------------------

/-- Realizability of the components of an element of `D∞` descends along the tower. -/
theorem relD_app_down (x : Dinf) (n : ℕ) (t : Lambda) (h : RelD (n + 1) (x.app (n + 1)) t) :
    RelD n (x.app n) t := by
  have := relD_prj h
  rwa [x.coherent n] at this

theorem relD_app_le (x : Dinf) (t : Lambda) : ∀ (j k : ℕ), RelD (k + j) (x.app (k + j)) t →
    RelD k (x.app k) t := by
  intro j
  induction j with
  | zero => exact fun k h => h
  | succ j ih =>
      intro k h
      exact ih k (relD_app_down x (k + j) t h)

/-- A value of stage `m` realized by `t` is realized by `t` at every stage of its image in
`D∞`. -/
theorem relD_psiFun : ∀ (m : ℕ) (w : D m) (t : Lambda), RelD m w t →
    ∀ k : ℕ, RelD k ((psiFun m w).app k) t := by
  intro m w t h k
  have hbase : RelD m ((psiFun m w).app m) t := by
    rw [psiFun_app_self]
    exact h
  have hup : ∀ d : ℕ, RelD (m + d) ((psiFun m w).app (m + d)) t := by
    intro d
    induction d with
    | zero => exact hbase
    | succ d ihd =>
        have hgt : ¬ (m + d + 1 ≤ m) := by omega
        have hstep : (psiFun m w).app (m + d + 1) = emb (m + d) ((psiFun m w).app (m + d)) :=
          psiSeq_of_gt w hgt
        rw [show m + (d + 1) = m + d + 1 from rfl, hstep]
        exact relD_emb ihd
  rcases Nat.le_total k m with hk | hk
  · obtain ⟨j, hj⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
    refine relD_app_le (psiFun m w) t j k ?_
    rw [← hj]
    exact hbase
  · obtain ⟨d, hd⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
    rw [hd]
    exact hup d

------------------------------------------------------------------------
-- Realizability in `D∞`
------------------------------------------------------------------------

/-- A term realizes an element of `D∞` when it realizes all of its components. -/
def RealD (x : Dinf) (t : Lambda) : Prop := ∀ n : ℕ, RelD n (x.app n) t

/-- Stable realizability: all liftings of the term realize the element. -/
def Real (x : Dinf) (t : Lambda) : Prop := ∀ k : ℕ, RealD x (Lambda.lift k 0 t)

theorem Real.realD {x : Dinf} {t : Lambda} (h : Real x t) : RealD x t := by
  simpa [Lambda.lift_zero] using h 0

theorem Real.lift {x : Dinf} {t : Lambda} (h : Real x t) (n : ℕ) :
    Real x (Lambda.lift n 0 t) := by
  intro k
  rw [← Lambda.lift_add]
  exact h (k + n)

theorem real_of_neutral (x : Dinf) {t : Lambda} (h : Neutral t) : Real x t :=
  fun k n => relD_of_neutral n _ (h.lift k 0)

theorem real_psiFun_of_relArg {n : ℕ} {x : D n} {u : Lambda} (h : RelArg n x u) :
    Real (psiFun n x) u :=
  fun k m => relD_psiFun n x (Lambda.lift k 0 u) (h k) m

/-- The image of the least element realizes every term. -/
theorem real_psiFun_botD (t : Lambda) : Real (psiFun 0 (botD 0)) t :=
  fun _ m => relD_psiFun 0 (botD 0) _ (relD_botD 0 _) m

/-- **Application preserves realizability.**  `Φ x y` is the supremum of the stagewise
approximations `psi n (x_{n+1} y_n)`, each of which is realized by `app t u`. -/
theorem realD_app {x y : Dinf} {t u : Lambda} (hx : RealD x t) (hy : Real y u) :
    RealD (Phi x y) (app t u) := by
  intro n
  have happ : (Phi x y).app n = ωSup ((evalChain (appChain x) y).map (Dinf.appMono n)) := by
    rw [Phi_apply, Dinf.ωSup_app]
  rw [happ]
  refine relD_ωSup n _ _ ?_
  intro m
  have hval : ((evalChain (appChain x) y).map (Dinf.appMono n)) m
      = (psiFun m (toFn (x.app (m + 1)) (y.app m))).app n := rfl
  rw [hval]
  refine relD_psiFun m _ _ ?_ n
  exact hx (m + 1) (y.app m) u (fun k => hy k m)

------------------------------------------------------------------------
-- The fundamental lemma
------------------------------------------------------------------------

/-- An environment of terms realizes an environment of values. -/
def Realizes (σ : ℕ → Lambda) (ρ : DEnv) : Prop := ∀ i, Real (ρ i) (σ i)

theorem Realizes.lift {σ : ℕ → Lambda} {ρ : DEnv} (h : Realizes σ ρ) (n : ℕ) :
    Realizes (fun i => Lambda.lift n 0 (σ i)) ρ :=
  fun i => (h i).lift n

theorem realizes_var (ρ : DEnv) : Realizes (fun i => Lambda.var i) ρ :=
  fun i => real_of_neutral (ρ i) (Neutral.var i)

theorem Realizes.envScons {σ : ℕ → Lambda} {ρ : DEnv} (h : Realizes σ ρ) {X : Dinf} {u : Lambda}
    (hu : Real X u) : Realizes (Lambda.envScons u σ) (dcons X ρ) := by
  intro i
  cases i with
  | zero => exact hu
  | succ j => exact h j

theorem Realizes.envCons {σ : ℕ → Lambda} {ρ : DEnv} (h : Realizes σ ρ) (X : Dinf) :
    Realizes (Lambda.envCons σ) (dcons X ρ) := by
  intro i
  cases i with
  | zero => exact real_of_neutral X (Neutral.var 0)
  | succ j => exact (h j).lift 1

/-- The abstraction case of the fundamental lemma, at an arbitrary stage: the value of the body
at the realizer of the argument is realized by the corresponding substitution instance. -/
theorem relD_lam_body {s : Lambda} {ρ : DEnv} {σ : ℕ → Lambda}
    (ih : ∀ (ρ' : DEnv) (σ' : ℕ → Lambda), Realizes σ' ρ' → RealD (ddenot s ρ') (substEnv σ' s))
    (h : Realizes σ ρ) (n : ℕ) {X : Dinf} {u : Lambda} (hX : Real X u) :
    RelD n ((ddenot s (dcons X ρ)).app n)
      (Lambda.app (Lambda.lam (substEnv (Lambda.envCons σ) s)) u) := by
  refine relD_expand n _ (Lambda.reduces.step _ _ _ (Lambda.step.beta _ _)
    (Lambda.reduces.refl _)) ?_
  rw [Lambda.subst_zero_substEnv]
  exact ih (dcons X ρ) (Lambda.envScons u σ) (h.envScons hX) n

/-- **The fundamental lemma.**  If the terms of `σ` realize the values of `ρ`, then the
substitution instance `t[σ]` realizes `⟦t⟧ρ`. -/
theorem realD_substEnv : ∀ (t : Lambda) (ρ : DEnv) (σ : ℕ → Lambda), Realizes σ ρ →
    RealD (ddenot t ρ) (substEnv σ t) := by
  intro t
  induction t with
  | var i => exact fun ρ σ h => (h i).realD
  | app s w ihs ihw =>
      intro ρ σ h
      refine realD_app (ihs ρ σ h) ?_
      intro k
      rw [Lambda.lift_substEnv]
      exact ihw ρ (fun i => Lambda.lift k 0 (σ i)) (h.lift k)
  | lam s ih =>
      intro ρ σ h n
      have hcont := ddenot_cons_cont s ρ
      have hden : ddenot (Lambda.lam s) ρ = Psi (ContinuousHom.ofFun _ hcont) := by
        rw [ddenot_lam, dlamAny_eq hcont]
      rw [hden]
      cases n with
      | zero =>
          intro hne args
          have hbot : RelD 0 ((ddenot s (dcons (psiFun 0 (botD 0)) ρ)).app 0)
              (substEnv (Lambda.envCons σ) s) :=
            ih (dcons (psiFun 0 (botD 0)) ρ) (Lambda.envCons σ)
              (h.envCons (psiFun 0 (botD 0))) 0
          cases args with
          | nil =>
              simpa [appList_nil, Lambda.substEnv] using
                hasHnf_lam (by simpa [appList_nil] using hbot hne [])
          | cons a rest =>
              have hrel : RelD 0 ((ddenot s (dcons (psiFun 0 (botD 0)) ρ)).app 0)
                  (Lambda.app (Lambda.lam (substEnv (Lambda.envCons σ) s)) a) :=
                relD_lam_body ih h 0 (real_psiFun_botD a)
              have := hrel hne rest
              rwa [← appList_cons] at this
      | succ n =>
          intro x u hu
          exact relD_lam_body ih h n (real_psiFun_of_relArg hu)

------------------------------------------------------------------------
-- Adequacy
------------------------------------------------------------------------

theorem exists_app_ne_botD {x : Dinf} (h : x ≠ Dinf.botDinf) : ∃ n, x.app n ≠ botD n := by
  by_contra hc
  push Not at hc
  exact h (Dinf.ext fun n => by rw [hc n, Dinf.botDinf_app])

/-- **Adequacy.**  A term whose denotation in `D∞` is not the least element — in any environment
at all — has a head normal form. -/
theorem hasHnf_of_ddenot_ne_botDinf {t : Lambda} {ρ : DEnv} (h : ddenot t ρ ≠ Dinf.botDinf) :
    Lambda.HasHnf t := by
  obtain ⟨n, hn⟩ := exists_app_ne_botD h
  have hrel := realD_substEnv t ρ (fun i => Lambda.var i) (realizes_var ρ) n
  rw [Lambda.substEnv_var_id] at hrel
  exact hasHnf_of_relD n _ t hrel hn

/-- A term with no head normal form denotes the least element in every environment. -/
theorem ddenot_eq_botDinf_of_not_hasHnf {t : Lambda} (h : ¬ Lambda.HasHnf t) (ρ : DEnv) :
    ddenot t ρ = Dinf.botDinf := by
  by_contra hc
  exact h (hasHnf_of_ddenot_ne_botDinf hc)

/-- **The least element of `D∞` is exactly the head-divergent terms.** -/
theorem exists_ddenot_ne_botDinf_iff_hasHnf {t : Lambda} :
    (∃ ρ : DEnv, ddenot t ρ ≠ Dinf.botDinf) ↔ Lambda.HasHnf t :=
  ⟨fun ⟨_, h⟩ => hasHnf_of_ddenot_ne_botDinf h, exists_ddenot_ne_botDinf_of_hasHnf⟩

/-- A term is unsolvable exactly when it denotes the least element in every environment. -/
theorem ddenot_eq_botDinf_iff_not_solvable {t : Lambda} (hcl : Lambda.IsClosed t) :
    (∀ ρ : DEnv, ddenot t ρ = Dinf.botDinf) ↔ ¬ Lambda.Solvable t := by
  constructor
  · exact not_solvable_of_ddenot_eq_botDinf
  · intro hns ρ
    exact ddenot_eq_botDinf_of_not_hasHnf
      (fun hh => hns (Lambda.solvable_of_hasHnf hcl hh)) ρ

------------------------------------------------------------------------
-- Observational equivalence
------------------------------------------------------------------------

/-- **Compositionality**: a context only sees the denotation of the term in its hole. -/
theorem ddenot_fill_congr {M N : Lambda} (h : ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ) :
    ∀ (C : Ctx) (ρ : DEnv), ddenot (C.fill M) ρ = ddenot (C.fill N) ρ := by
  intro C
  induction C with
  | hole => exact h
  | appL C s ih => intro ρ; simp only [Ctx.fill, ddenot_app, ih ρ]
  | appR s C ih => intro ρ; simp only [Ctx.fill, ddenot_app, ih ρ]
  | lam C ih =>
      intro ρ
      simp only [Ctx.fill, ddenot_lam]
      exact dlamAny_congr fun X => ih (dcons X ρ)

/-- **Adequacy gives observational equivalence**: terms with the same denotation in every
environment are indistinguishable by contexts, as far as head normalization is concerned. -/
theorem obsEqHnf_of_ddenot_eq {M N : Lambda} (h : ∀ ρ : DEnv, ddenot M ρ = ddenot N ρ) :
    ObsEqHnf M N := by
  have key : ∀ (M N : Lambda), (∀ ρ : DEnv, ddenot M ρ = ddenot N ρ) → ∀ C : Ctx,
      HasHnf (C.fill M) → HasHnf (C.fill N) := by
    intro M N h C hM
    obtain ⟨ρ, hρ⟩ := exists_ddenot_ne_botDinf_of_hasHnf hM
    refine hasHnf_of_ddenot_ne_botDinf (ρ := ρ) ?_
    rw [← ddenot_fill_congr h C ρ]
    exact hρ
  exact fun C => ⟨key M N h C, key N M (fun ρ => (h ρ).symm) C⟩

end

end ScottDinf
