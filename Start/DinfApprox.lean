/-
The approximation theorem for Scott's `D∞`.
-/

import Start.DinfAdequacy
import Start.GraphApproxTheorem

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

open Lambda

noncomputable section

/-! ## Every level of the tower is finite -/

instance finite_D : ∀ n : ℕ, Finite (D n)
  | 0 => inferInstanceAs (Finite Bool)
  | (n + 1) => by
      have : Finite (D n) := finite_D n
      exact Finite.of_injective (fun f : D (n + 1) => (toFn f : D n → D n))
        (fun _ _ h => toFn_ext (fun x => congrFun h x))

/-- In a finite level of the tower, the supremum of a chain is attained. -/
theorem exists_ωSup_eq {n : ℕ} (c : Chain (D n)) : ∃ i, ωSup c = c i := by
  obtain ⟨z, hz⟩ :=
    Set.Finite.exists_maximal (Set.toFinite (Set.range (fun i => c i))) ⟨c 0, 0, rfl⟩
  obtain ⟨⟨i, hi⟩, hmax⟩ := hz
  subst hi
  refine ⟨i, le_antisymm (ωSup_le _ _ fun j => ?_) (le_ωSup c i)⟩
  have hk : c j ≤ c (max i j) := c.monotone (le_max_right i j)
  exact hk.trans (hmax ⟨max i j, rfl⟩ (c.monotone (le_max_left i j)))

/-! ## The least element and the embeddings -/

theorem emb_botD : ∀ n : ℕ, emb n (botD n) = botD (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      refine toFn_ext ?_
      intro x
      rw [emb_succ_apply, toFn_botD, ih, toFn_botD]

/-- The image of the least element of the base level is the least element of `D∞`. -/
theorem psiFun_zero_botD : psiFun 0 (botD 0) = Dinf.botDinf := by
  ext k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [psiFun_app, psiSeq_of_gt _ (by omega), ← psiFun_app, ih, Dinf.botDinf_app,
        emb_botD, Dinf.botDinf_app]

/-! ## Application and the levels -/

/-- The level-`n` component of an application dominates the application of the components. -/
theorem toFn_app_le_Phi (x y : Dinf) (n : ℕ) :
    toFn (x.app (n + 1)) (y.app n) ≤ (Phi x y).app n := by
  have h1 : (Phi x (psiFun n (y.app n))).app n = toFn (x.app (n + 1)) (y.app n) :=
    Phi_app_psi x n (y.app n)
  have h2 : Phi x (psiFun n (y.app n)) ≤ Phi x y :=
    (Phi x).monotone (psi_app_le n y)
  exact h1 ▸ Dinf.le_def.mp h2 n

/-- At the base level, applying a term only increases the value. -/
theorem app_zero_le (x y : Dinf) : x.app 0 ≤ (Phi x y).app 0 := by
  refine le_trans ?_ (toFn_app_le_Phi x y 0)
  rw [← x.coherent 0, prj_zero_apply]
  exact (toFn (x.app 1)).monotone (botD_le 0 _)

/-! ## Denotations of abstractions, level by level -/

theorem ddenot_lam_app_zero (s : Lambda) (ρ : DEnv) :
    (ddenot (Lambda.lam s) ρ).app 0 = (ddenot s (dcons (psiFun 0 (botD 0)) ρ)).app 0 := by
  rw [ddenot_lam, dlamAny_eq (ddenot_cons_cont s ρ)]
  rfl

theorem ddenot_lam_app_succ (s : Lambda) (ρ : DEnv) (m : ℕ) (x : D m) :
    toFn ((ddenot (Lambda.lam s) ρ).app (m + 1)) x
      = (ddenot s (dcons (psiFun m x) ρ)).app m := by
  rw [ddenot_lam, dlamAny_eq (ddenot_cons_cont s ρ)]
  rfl

/-! ## The denotation is monotone for the approximation order -/

theorem ddenot_omega (ρ : DEnv) : ddenot Lambda.omega ρ = Dinf.botDinf :=
  ddenot_eq_botDinf_of_not_hasHnf GraphModel.not_hasHnf_omega ρ

theorem dlamAny_le {f g : Dinf → Dinf} (hf : ωScottContinuous f) (hg : ωScottContinuous g)
    (h : ∀ X, f X ≤ g X) : dlamAny f ≤ dlamAny g := by
  rw [dlamAny_eq hf, dlamAny_eq hg]
  exact Psi_mono (fun X => h X)

/-- **The denotation is monotone for the approximation order.** -/
theorem ddenot_approx_le {a t : Lambda} (h : Approx a t) (ρ : DEnv) :
    ddenot a ρ ≤ ddenot t ρ := by
  induction h generalizing ρ with
  | omega t => rw [ddenot_omega]; exact Dinf.botDinf_le _
  | var n => exact le_refl _
  | app _ _ ihf iha =>
      rename_i a b s t _ _
      refine le_trans ?_ ((Phi (ddenot s ρ)).monotone (iha ρ))
      exact Phi_mono (ihf ρ) (ddenot b ρ)
  | lam _ ih =>
      rename_i a s _
      exact dlamAny_le (ddenot_cons_cont a ρ) (ddenot_cons_cont s ρ) fun X => ih (dcons X ρ)

/-- The direct approximant of a term denotes less than the term. -/
theorem ddenot_direct_le (t : Lambda) (ρ : DEnv) : ddenot (direct t) ρ ≤ ddenot t ρ :=
  ddenot_approx_le (approx_direct t) ρ

/-- The direct approximant of a reduct also denotes less than the term. -/
theorem ddenot_direct_reduct_le {t t' : Lambda} (h : Lambda.reduces t t') (ρ : DEnv) :
    ddenot (direct t') ρ ≤ ddenot t ρ := by
  rw [ddenot_reduces h ρ]
  exact ddenot_direct_le t' ρ

/-- Direct approximants only grow along reduction. -/
theorem ddenot_direct_reduces_mono {t t' : Lambda} (h : Lambda.reduces t t') (ρ : DEnv) :
    ddenot (direct t) ρ ≤ ddenot (direct t') ρ := by
  induction h with
  | refl t => exact le_refl _
  | step t₁ t₂ t₃ hs _ ih =>
      exact le_trans (ddenot_approx_le (Lambda.approx_direct_step hs) ρ) ih

/-! ## Merging finitely many reducts -/

/-- **Merging finitely many reducts.**  If a property that only grows along reduction holds,
for each element of a list, at some reduct of `s`, then it holds for all of them at a single
reduct of `s`. -/
theorem exists_reduct_forall_mem {α : Type} (P : Lambda → α → Prop)
    (hmono : ∀ {u u' : Lambda} {a : α}, Lambda.reduces u u' → P u a → P u' a) (s : Lambda) :
    ∀ l : List α, (∀ a ∈ l, ∃ u, Lambda.reduces s u ∧ P u a) →
      ∃ u, Lambda.reduces s u ∧ ∀ a ∈ l, P u a := by
  intro l
  induction l with
  | nil => intro _; exact ⟨s, Lambda.reduces.refl s, by simp⟩
  | cons b l ih =>
      intro h
      obtain ⟨u₁, hu₁, hb⟩ := h b (by simp)
      obtain ⟨u₂, hu₂, hl⟩ := ih fun a ha => h a (by simp [ha])
      obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem hu₁ hu₂
      refine ⟨w, Lambda.reduces_trans hu₁ hw₁, ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hmono hw₁ hb
      · exact hmono hw₂ (hl a ha)

/-- The same, for a property indexed by a finite type. -/
theorem exists_reduct_forall {α : Type} [Finite α] (P : Lambda → α → Prop)
    (hmono : ∀ {u u' : Lambda} {a : α}, Lambda.reduces u u' → P u a → P u' a) (s : Lambda)
    (h : ∀ a, ∃ u, Lambda.reduces s u ∧ P u a) : ∃ u, Lambda.reduces s u ∧ ∀ a, P u a := by
  have : Fintype α := Fintype.ofFinite α
  obtain ⟨u, hu, hall⟩ :=
    exists_reduct_forall_mem P hmono s (Finset.univ : Finset α).toList
      fun a _ => h a
  exact ⟨u, hu, fun a => hall a (by simp)⟩

/-! ## The computability predicate -/

/-- `ARelD n z ρ t`: the term `t` *approximates* the stage-`n` value `z` in the environment `ρ`.

At the base of the tower this means that, applied to any list of arguments, `t` reduces to a term
whose direct approximant already denotes at least `z`; at level `n+1` it means both that some
reduct of `t` has a direct approximant denoting at least `z`, and that applying `t` to a term
approximating `x` approximates the value at `x`.  Arguments are required to approximate in every
weakening of the two environments, which is what makes the predicate stable under the shift that
de Bruijn parallel substitution performs at a binder. -/
def ARelD : ∀ (n : ℕ), D n → DEnv → Lambda → Prop
  | 0, z, ρ, t => ∀ args : List Lambda, ∃ t', Lambda.reduces (Lambda.appList t args) t' ∧
      z ≤ (ddenot (Lambda.direct t') ρ).app 0
  | (n + 1), f, ρ, t =>
      (∃ t', Lambda.reduces t t' ∧ f ≤ (ddenot (Lambda.direct t') ρ).app (n + 1)) ∧
      ∀ (x : D n) (u : Lambda),
        (∀ (k : ℕ) (ρ' : DEnv), (∀ i, ρ' (i + k) = ρ i) → ARelD n x ρ' (Lambda.lift k 0 u)) →
        ARelD n (toFn f x) ρ (Lambda.app t u)

/-- A term approximates a stage-`n` value *stably* when it does so in every weakening. -/
def ARelArg (n : ℕ) (x : D n) (ρ : DEnv) (u : Lambda) : Prop :=
  ∀ (k : ℕ) (ρ' : DEnv), (∀ i, ρ' (i + k) = ρ i) → ARelD n x ρ' (Lambda.lift k 0 u)

theorem arelD_zero_iff {z : D 0} {ρ : DEnv} {t : Lambda} :
    ARelD 0 z ρ t ↔ ∀ args : List Lambda, ∃ t', Lambda.reduces (Lambda.appList t args) t' ∧
      z ≤ (ddenot (Lambda.direct t') ρ).app 0 := Iff.rfl

theorem arelD_succ_iff {n : ℕ} {f : D (n + 1)} {ρ : DEnv} {t : Lambda} :
    ARelD (n + 1) f ρ t ↔
      (∃ t', Lambda.reduces t t' ∧ f ≤ (ddenot (Lambda.direct t') ρ).app (n + 1)) ∧
      ∀ (x : D n) (u : Lambda), ARelArg n x ρ u → ARelD n (toFn f x) ρ (Lambda.app t u) := Iff.rfl

/-- Whatever the level, the predicate exhibits a reduct whose direct approximant sees the
value. -/
theorem ARelD.direct : ∀ {n : ℕ} {z : D n} {ρ : DEnv} {t : Lambda}, ARelD n z ρ t →
    ∃ t', Lambda.reduces t t' ∧ z ≤ (ddenot (Lambda.direct t') ρ).app n := by
  intro n z ρ t h
  cases n with
  | zero =>
      obtain ⟨t', ht', hz⟩ := h []
      rw [Lambda.appList_nil] at ht'
      exact ⟨t', ht', hz⟩
  | succ n => exact h.1

/-- The least element of a stage is approximated by every term. -/
theorem arelD_botD : ∀ (n : ℕ) (ρ : DEnv) (t : Lambda), ARelD n (botD n) ρ t := by
  intro n
  induction n with
  | zero => intro ρ t args; exact ⟨Lambda.appList t args, Lambda.reduces.refl _, botD_le 0 _⟩
  | succ n ih =>
      intro ρ t
      refine ⟨⟨t, Lambda.reduces.refl t, botD_le (n + 1) _⟩, ?_⟩
      intro x u _
      rw [toFn_botD]
      exact ih ρ _

/-- The predicate is downward closed in the value. -/
theorem arelD_mono : ∀ (n : ℕ) {z z' : D n} (ρ : DEnv) (t : Lambda), z ≤ z' →
    ARelD n z' ρ t → ARelD n z ρ t := by
  intro n
  induction n with
  | zero =>
      intro z z' ρ t hle h args
      obtain ⟨t', ht', hz⟩ := h args
      exact ⟨t', ht', le_trans hle hz⟩
  | succ n ih =>
      intro z z' ρ t hle h
      refine ⟨?_, ?_⟩
      · obtain ⟨t', ht', hz⟩ := h.1
        exact ⟨t', ht', le_trans hle hz⟩
      · intro x u hu
        exact ih ρ _ (toFn_le_iff.mp hle x) (h.2 x u hu)

/-- The predicate is inherited backwards along a reduction. -/
theorem arelD_expand : ∀ (n : ℕ) (z : D n) (ρ : DEnv) {t t' : Lambda}, Lambda.reduces t t' →
    ARelD n z ρ t' → ARelD n z ρ t := by
  intro n
  induction n with
  | zero =>
      intro z ρ t t' hr h args
      obtain ⟨w, hw, hz⟩ := h args
      exact ⟨w, Lambda.reduces_trans (Lambda.reduces_appList hr args) hw, hz⟩
  | succ n ih =>
      intro z ρ t t' hr h
      refine ⟨?_, ?_⟩
      · obtain ⟨w, hw, hz⟩ := h.1
        exact ⟨w, Lambda.reduces_trans hr hw, hz⟩
      · intro x u hu
        exact ih _ ρ (Lambda.reduces_app_left hr) (h.2 x u hu)

/-! ## The base case: neutral reducts -/

/-- Applying a neutral term to further arguments only increases the base-level denotation of
its direct approximant. -/
theorem ddenot_direct_appList_zero (ρ : DEnv) : ∀ (args : List Lambda) (t : Lambda), Neutral t →
    (ddenot (Lambda.direct t) ρ).app 0
      ≤ (ddenot (Lambda.direct (Lambda.appList t args)) ρ).app 0 := by
  intro args
  induction args with
  | nil => intro t _; rw [Lambda.appList_nil]
  | cons a rest ih =>
      intro t ht
      rw [Lambda.appList_cons]
      refine le_trans ?_ (ih (Lambda.app t a) (Neutral.app a ht))
      rw [Lambda.direct_app, if_pos (neutral_iff_headVar.1 ht), ddenot_app]
      exact app_zero_le _ _

/-- The level-`n` value of an application dominates the application of the level-`n` values. -/
theorem toFn_le_ddenot_app {n : ℕ} {z : D (n + 1)} {x : D n} {ρ : DEnv} {a b : Lambda}
    (hz : z ≤ (ddenot a ρ).app (n + 1)) (hx : x ≤ (ddenot b ρ).app n) :
    toFn z x ≤ (ddenot (Lambda.app a b) ρ).app n := by
  rw [ddenot_app]
  refine le_trans ?_ (toFn_app_le_Phi (ddenot a ρ) (ddenot b ρ) n)
  exact le_trans (toFn_le_iff.mp hz x) ((toFn ((ddenot a ρ).app (n + 1))).monotone hx)

/-- A term reducing to a *neutral* term whose direct approximant sees the value satisfies the
predicate: this is the base case of the computability argument. -/
theorem arelD_of_neutral_reduct : ∀ (n : ℕ) (z : D n) (ρ : DEnv) (t : Lambda),
    (∃ t₀, Lambda.reduces t t₀ ∧ Neutral t₀ ∧ z ≤ (ddenot (Lambda.direct t₀) ρ).app n) →
    ARelD n z ρ t := by
  intro n
  induction n with
  | zero =>
      rintro z ρ t ⟨t₀, ht₀, hn₀, hz⟩ args
      exact ⟨Lambda.appList t₀ args, Lambda.reduces_appList ht₀ args,
        le_trans hz (ddenot_direct_appList_zero ρ args t₀ hn₀)⟩
  | succ n ih =>
      rintro z ρ t ⟨t₀, ht₀, hn₀, hz⟩
      refine ⟨⟨t₀, ht₀, hz⟩, ?_⟩
      intro x u hu
      have hu0 : ARelD n x ρ u := by
        have := hu 0 ρ (fun _ => rfl)
        rwa [Lambda.lift_zero] at this
      obtain ⟨u', hu', hx⟩ := hu0.direct
      refine ih _ ρ _ ⟨Lambda.app t₀ u', Lambda.reduces_app ht₀ hu', Neutral.app _ hn₀, ?_⟩
      rw [Lambda.direct_app, if_pos (neutral_iff_headVar.1 hn₀)]
      exact toFn_le_ddenot_app hz hx

/-! ## Compatibility with the embedding–projection pairs -/

theorem emb_le_app_succ {n : ℕ} {z : D n} {w : Dinf} (h : z ≤ w.app n) :
    emb n z ≤ w.app (n + 1) := by
  refine le_trans ((emb n).monotone h) ?_
  rw [← w.coherent n]
  exact emb_prj_le n _

theorem prj_le_app {n : ℕ} {f : D (n + 1)} {w : Dinf} (h : f ≤ w.app (n + 1)) :
    prj n f ≤ w.app n := by
  have := (prj n).monotone h
  rwa [w.coherent n] at this

/-- Approximation transfers along the embedding and the projection of the tower.  The two
statements are proved by simultaneous induction on the level. -/
theorem arelD_emb_prj : ∀ n : ℕ,
    (∀ (z : D n) (ρ : DEnv) (t : Lambda), ARelD n z ρ t → ARelD (n + 1) (emb n z) ρ t) ∧
      (∀ (f : D (n + 1)) (ρ : DEnv) (t : Lambda), ARelD (n + 1) f ρ t → ARelD n (prj n f) ρ t) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro z ρ t h
        refine ⟨?_, ?_⟩
        · obtain ⟨t', ht', hz⟩ := h.direct
          exact ⟨t', ht', emb_le_app_succ hz⟩
        · intro x u _
          rw [emb_zero_apply]
          intro args
          obtain ⟨t', ht', hz⟩ := h (u :: args)
          rw [Lambda.appList_cons] at ht'
          exact ⟨t', ht', hz⟩
      · intro f ρ t h args
        cases args with
        | nil =>
            obtain ⟨t', ht', hf⟩ := h.1
            rw [Lambda.appList_nil]
            exact ⟨t', ht', prj_le_app hf⟩
        | cons a rest =>
            have hrel : ARelD 0 (toFn f (botD 0)) ρ (Lambda.app t a) :=
              h.2 (botD 0) a (fun k ρ' _ => arelD_botD 0 ρ' _)
            obtain ⟨t', ht', hz⟩ := hrel rest
            rw [← Lambda.appList_cons] at ht'
            rw [prj_zero_apply]
            exact ⟨t', ht', hz⟩
  | succ n ih =>
      obtain ⟨hemb, hprj⟩ := ih
      constructor
      · intro z ρ t h
        refine ⟨?_, ?_⟩
        · obtain ⟨t', ht', hz⟩ := h.direct
          exact ⟨t', ht', emb_le_app_succ hz⟩
        · intro x u hu
          rw [emb_succ_apply]
          refine hemb _ ρ _ ?_
          exact h.2 (prj n x) u (fun k ρ' hk => hprj _ ρ' _ (hu k ρ' hk))
      · intro f ρ t h
        refine ⟨?_, ?_⟩
        · obtain ⟨t', ht', hf⟩ := h.1
          exact ⟨t', ht', prj_le_app hf⟩
        · intro x u hu
          rw [prj_succ_apply]
          refine hprj _ ρ _ ?_
          exact h.2 (emb n x) u (fun k ρ' hk => hemb _ ρ' _ (hu k ρ' hk))

theorem arelD_emb {n : ℕ} {z : D n} {ρ : DEnv} {t : Lambda} (h : ARelD n z ρ t) :
    ARelD (n + 1) (emb n z) ρ t := (arelD_emb_prj n).1 z ρ t h

theorem arelD_prj {n : ℕ} {f : D (n + 1)} {ρ : DEnv} {t : Lambda} (h : ARelD (n + 1) f ρ t) :
    ARelD n (prj n f) ρ t := (arelD_emb_prj n).2 f ρ t h

/-! ## Admissibility -/

/-- The predicate is closed under suprema of chains: at a finite level of the tower the
supremum is attained. -/
theorem arelD_ωSup {n : ℕ} (c : Chain (D n)) (ρ : DEnv) (t : Lambda) (h : ∀ i, ARelD n (c i) ρ t) :
    ARelD n (ωSup c) ρ t := by
  obtain ⟨i, hi⟩ := exists_ωSup_eq c
  rw [hi]
  exact h i

/-! ## Moving between the stages -/

theorem arelD_app_down (x : Dinf) (n : ℕ) (ρ : DEnv) (t : Lambda)
    (h : ARelD (n + 1) (x.app (n + 1)) ρ t) : ARelD n (x.app n) ρ t := by
  have := arelD_prj h
  rwa [x.coherent n] at this

theorem arelD_app_le (x : Dinf) (ρ : DEnv) (t : Lambda) : ∀ (j k : ℕ),
    ARelD (k + j) (x.app (k + j)) ρ t → ARelD k (x.app k) ρ t := by
  intro j
  induction j with
  | zero => exact fun k h => h
  | succ j ih => exact fun k h => ih k (arelD_app_down x (k + j) ρ t h)

/-- A stage-`m` value approximated by `t` is approximated by `t` at every stage of its image
in `D∞`. -/
theorem arelD_psiFun : ∀ (m : ℕ) (w : D m) (ρ : DEnv) (t : Lambda), ARelD m w ρ t →
    ∀ k : ℕ, ARelD k ((psiFun m w).app k) ρ t := by
  intro m w ρ t h k
  have hbase : ARelD m ((psiFun m w).app m) ρ t := by
    rw [psiFun_app_self]
    exact h
  have hup : ∀ d : ℕ, ARelD (m + d) ((psiFun m w).app (m + d)) ρ t := by
    intro d
    induction d with
    | zero => exact hbase
    | succ d ihd =>
        have hgt : ¬ (m + d + 1 ≤ m) := by omega
        have hstep : (psiFun m w).app (m + d + 1) = emb (m + d) ((psiFun m w).app (m + d)) :=
          psiSeq_of_gt w hgt
        rw [show m + (d + 1) = m + d + 1 from rfl, hstep]
        exact arelD_emb ihd
  rcases Nat.le_total k m with hk | hk
  · obtain ⟨j, hj⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
    refine arelD_app_le (psiFun m w) ρ t j k ?_
    rw [← hj]
    exact hbase
  · obtain ⟨d, hd⟩ : ∃ d, k = m + d := ⟨k - m, by omega⟩
    rw [hd]
    exact hup d

/-! ## Approximation in `D∞` -/

/-- A term approximates an element of `D∞` when it approximates all of its components. -/
def ARealD (x : Dinf) (ρ : DEnv) (t : Lambda) : Prop := ∀ n : ℕ, ARelD n (x.app n) ρ t

/-- Stable approximation: the property survives every weakening of the environment. -/
def AReal (x : Dinf) (ρ : DEnv) (t : Lambda) : Prop :=
  ∀ (k : ℕ) (ρ' : DEnv), (∀ i, ρ' (i + k) = ρ i) → ARealD x ρ' (Lambda.lift k 0 t)

theorem AReal.arealD {x : Dinf} {ρ : DEnv} {t : Lambda} (h : AReal x ρ t) : ARealD x ρ t := by
  have := h 0 ρ (fun _ => rfl)
  rwa [Lambda.lift_zero] at this

theorem AReal.arelArg {x : Dinf} {ρ : DEnv} {t : Lambda} (h : AReal x ρ t) (n : ℕ) :
    ARelArg n (x.app n) ρ t := fun k ρ' hk => h k ρ' hk n

/-- The predicate is closed under weakening of both the environment and the term. -/
theorem AReal.weaken {x : Dinf} {ρ : DEnv} {t : Lambda} (h : AReal x ρ t) (n : ℕ) (ρ' : DEnv)
    (hρ' : ∀ i, ρ' (i + n) = ρ i) : AReal x ρ' (Lambda.lift n 0 t) := by
  intro m ρ'' hρ''
  rw [← Lambda.lift_add]
  refine h (m + n) ρ'' ?_
  intro i
  have h1 := hρ'' (i + n)
  rw [hρ' i] at h1
  rw [show i + (m + n) = i + n + m by omega]
  exact h1

/-- The least element of `D∞` is approximated by every term. -/
theorem areal_botDinf (ρ : DEnv) (t : Lambda) : AReal Dinf.botDinf ρ t := by
  intro k ρ' _ n
  rw [Dinf.botDinf_app]
  exact arelD_botD n ρ' _

/-- A variable is approximated by the value the environment gives it. -/
theorem areal_var (X : Dinf) (ρ : DEnv) (i : ℕ) (h : ρ i = X) : AReal X ρ (Lambda.var i) := by
  intro k ρ' hρ' n
  refine arelD_of_neutral_reduct n _ ρ' _ ⟨Lambda.lift k 0 (Lambda.var i),
    Lambda.reduces.refl _, ?_, ?_⟩
  · simp only [Lambda.lift, if_neg (Nat.not_lt_zero i)]
    exact Neutral.var _
  · simp only [Lambda.lift, if_neg (Nat.not_lt_zero i), Lambda.direct_var, ddenot_var]
    rw [hρ' i, h]

/-- **Application preserves approximation.** -/
theorem arealD_app {x y : Dinf} {ρ : DEnv} {t u : Lambda} (hx : ARealD x ρ t)
    (hy : AReal y ρ u) : ARealD (Phi x y) ρ (Lambda.app t u) := by
  intro n
  have happ : (Phi x y).app n = ωSup ((evalChain (appChain x) y).map (Dinf.appMono n)) := by
    rw [Phi_apply, Dinf.ωSup_app]
  rw [happ]
  refine arelD_ωSup _ ρ _ ?_
  intro m
  have hval : ((evalChain (appChain x) y).map (Dinf.appMono n)) m
      = (psiFun m (toFn (x.app (m + 1)) (y.app m))).app n := rfl
  rw [hval]
  refine arelD_psiFun m _ ρ _ ?_ n
  exact (hx (m + 1)).2 (y.app m) u (fun k ρ' hk => hy k ρ' hk m)

/-! ## The fundamental lemma -/

/-- Extending the two environments and the substitution at a binder. -/
theorem areal_envCons {ρ ρ' : DEnv} {σ : ℕ → Lambda} (h : ∀ i, AReal (ρ i) ρ' (σ i)) (X : Dinf) :
    ∀ i, AReal (dcons X ρ i) (dcons X ρ') (Lambda.envCons σ i) := by
  intro i
  cases i with
  | zero => exact areal_var X (dcons X ρ') 0 rfl
  | succ j => exact (h j).weaken 1 (dcons X ρ') (fun _ => rfl)

/-- **The fundamental lemma.**  If the terms of `σ` approximate the values of `ρ` in the target
environment `ρ'`, then the substitution instance `t[σ]` approximates `⟦t⟧ρ`. -/
theorem arealD_substEnv : ∀ (t : Lambda) (ρ ρ' : DEnv) (σ : ℕ → Lambda),
    (∀ i, AReal (ρ i) ρ' (σ i)) → ARealD (ddenot t ρ) ρ' (Lambda.substEnv σ t) := by
  intro t
  induction t with
  | var i => exact fun ρ ρ' σ h => (h i).arealD
  | app s w ihs ihw =>
      intro ρ ρ' σ h
      refine arealD_app (ihs ρ ρ' σ h) ?_
      intro k ρ'' hk
      rw [Lambda.lift_substEnv]
      exact ihw ρ ρ'' (fun i => Lambda.lift k 0 (σ i)) (fun i => (h i).weaken k ρ'' hk)
  | lam s ih =>
      intro ρ ρ' σ h n
      cases n with
      | zero =>
          rw [ddenot_lam_app_zero, psiFun_zero_botD]
          intro args
          cases args with
          | nil =>
              obtain ⟨B', hB', hle⟩ :=
                (ih (dcons Dinf.botDinf ρ) (dcons Dinf.botDinf ρ') (Lambda.envCons σ)
                  (areal_envCons h Dinf.botDinf) 0).direct
              refine ⟨Lambda.lam B', ?_, ?_⟩
              · rw [Lambda.appList_nil]
                exact Lambda.reduces_lam hB'
              · rw [Lambda.direct_lam, ddenot_lam_app_zero, psiFun_zero_botD]
                exact hle
          | cons a rest =>
              have hkey : ARelD 0 ((ddenot s (dcons Dinf.botDinf ρ)).app 0) ρ'
                  (Lambda.app (Lambda.lam (Lambda.substEnv (Lambda.envCons σ) s)) a) := by
                refine arelD_expand 0 _ ρ'
                  (Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (Lambda.reduces.refl _)) ?_
                rw [Lambda.subst_zero_substEnv]
                refine ih (dcons Dinf.botDinf ρ) ρ' (Lambda.envScons a σ) ?_ 0
                intro i
                cases i with
                | zero => exact areal_botDinf ρ' a
                | succ j => exact h j
              obtain ⟨t', ht', hz⟩ := hkey rest
              rw [← Lambda.appList_cons] at ht'
              exact ⟨t', ht', hz⟩
      | succ m =>
          refine ⟨?_, ?_⟩
          · have hx : ∀ x : D m, ∃ B', Lambda.reduces (Lambda.substEnv (Lambda.envCons σ) s) B' ∧
                (ddenot s (dcons (psiFun m x) ρ)).app m
                  ≤ (ddenot (Lambda.direct B') (dcons (psiFun m x) ρ')).app m := by
              intro x
              exact (ih (dcons (psiFun m x) ρ) (dcons (psiFun m x) ρ') (Lambda.envCons σ)
                (areal_envCons h (psiFun m x)) m).direct
            obtain ⟨B', hB', hall⟩ :=
              exists_reduct_forall
                (fun u x => (ddenot s (dcons (psiFun m x) ρ)).app m
                  ≤ (ddenot (Lambda.direct u) (dcons (psiFun m x) ρ')).app m)
                (fun {u u' x} hr hu =>
                  le_trans hu (Dinf.le_def.mp (ddenot_direct_reduces_mono hr _) m))
                (Lambda.substEnv (Lambda.envCons σ) s) hx
            refine ⟨Lambda.lam B', Lambda.reduces_lam hB', ?_⟩
            rw [Lambda.direct_lam, toFn_le_iff]
            intro x
            rw [ddenot_lam_app_succ, ddenot_lam_app_succ]
            exact hall x
          · intro x u hu
            rw [ddenot_lam_app_succ]
            refine arelD_expand m _ ρ'
              (Lambda.reduces.step _ _ _ (Lambda.step.beta _ _) (Lambda.reduces.refl _)) ?_
            rw [Lambda.subst_zero_substEnv]
            refine ih (dcons (psiFun m x) ρ) ρ' (Lambda.envScons u σ) ?_ m
            intro i
            cases i with
            | zero =>
                intro k ρ'' hk j
                exact arelD_psiFun m x ρ'' _ (hu k ρ'' hk) j
            | succ j => exact h j

/-! ## The approximation theorem -/

/-- **Completeness of approximation.**  Every finite stage of the denotation of a term is
already reached by the direct approximant of one of its reducts. -/
theorem exists_reduct_app_le (t : Lambda) (ρ : DEnv) (n : ℕ) :
    ∃ t', Lambda.reduces t t' ∧ (ddenot t ρ).app n ≤ (ddenot (Lambda.direct t') ρ).app n := by
  have h := arealD_substEnv t ρ ρ (fun i => Lambda.var i)
    (fun i => areal_var (ρ i) ρ i rfl) n
  rw [Lambda.substEnv_var_id] at h
  exact h.direct

/-- Every finite approximation of the denotation of a term is below the denotation of the
direct approximant of one of its reducts. -/
theorem exists_reduct_theta_le (t : Lambda) (ρ : DEnv) (n : ℕ) :
    ∃ t', Lambda.reduces t t' ∧ theta n (ddenot t ρ) ≤ ddenot (Lambda.direct t') ρ := by
  obtain ⟨t', ht', hle⟩ := exists_reduct_app_le t ρ n
  refine ⟨t', ht', ?_⟩
  rw [← psi_theta]
  exact psi_le_iff.mpr hle

/-- **The approximation theorem for `D∞`.**  The denotation of a term is the least upper bound
of the denotations of the direct approximants of its reducts. -/
theorem isLUB_ddenot_direct (t : Lambda) (ρ : DEnv) :
    IsLUB {x : Dinf | ∃ t', Lambda.reduces t t' ∧ x = ddenot (Lambda.direct t') ρ}
      (ddenot t ρ) := by
  constructor
  · rintro x ⟨t', ht', rfl⟩
    exact ddenot_direct_reduct_le ht' ρ
  · intro y hy
    refine Dinf.le_def.mpr fun n => ?_
    obtain ⟨t', ht', hle⟩ := exists_reduct_app_le t ρ n
    exact le_trans hle (Dinf.le_def.mp (hy ⟨t', ht', rfl⟩) n)

/-- **The approximants of a term are directed**, so the least upper bound of
`ScottDinf.isLUB_ddenot_direct` is a supremum of a directed family. -/
theorem exists_reduct_ddenot_direct_sup {t t₁ t₂ : Lambda} (h₁ : Lambda.reduces t t₁)
    (h₂ : Lambda.reduces t t₂) (ρ : DEnv) :
    ∃ t₃, Lambda.reduces t t₃ ∧ ddenot (Lambda.direct t₁) ρ ≤ ddenot (Lambda.direct t₃) ρ ∧
      ddenot (Lambda.direct t₂) ρ ≤ ddenot (Lambda.direct t₃) ρ := by
  obtain ⟨w, hw₁, hw₂⟩ := Lambda.confluence_theorem h₁ h₂
  exact ⟨w, Lambda.reduces_trans h₁ hw₁, ddenot_direct_reduces_mono hw₁ ρ,
    ddenot_direct_reduces_mono hw₂ ρ⟩

/-- If every approximant of `t` is dominated by an approximant of `u`, then `t` denotes less
than `u`: syntactic domination of the Böhm approximants is a semantic inequality. -/
theorem ddenot_le_of_approx_reducts {t u : Lambda}
    (h : ∀ t', Lambda.reduces t t' →
      ∃ u', Lambda.reduces u u' ∧ Approx (Lambda.direct t') (Lambda.direct u')) (ρ : DEnv) :
    ddenot t ρ ≤ ddenot u ρ := by
  refine (isLUB_ddenot_direct t ρ).2 ?_
  rintro x ⟨t', ht', rfl⟩
  obtain ⟨u', hu', happ⟩ := h t' ht'
  exact le_trans (ddenot_approx_le happ ρ) (ddenot_direct_reduct_le hu' ρ)

/-- Two terms whose approximants dominate each other have the same denotation in `D∞`. -/
theorem ddenot_eq_of_approx_reducts {t u : Lambda}
    (h₁ : ∀ t', Lambda.reduces t t' →
      ∃ u', Lambda.reduces u u' ∧ Approx (Lambda.direct t') (Lambda.direct u'))
    (h₂ : ∀ u', Lambda.reduces u u' →
      ∃ t', Lambda.reduces t t' ∧ Approx (Lambda.direct u') (Lambda.direct t')) (ρ : DEnv) :
    ddenot t ρ = ddenot u ρ :=
  le_antisymm (ddenot_le_of_approx_reducts h₁ ρ) (ddenot_le_of_approx_reducts h₂ ρ)

end

end ScottDinf
