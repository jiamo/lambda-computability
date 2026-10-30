/-
**Strong normalisation of typed λμ** — task `M23-LAMBDA-MU-SN`.

The fundamental lemma of reducibility for Parigot's λμ, on the calculus of `Start/LambdaMu.lean`,
with the expansion lemmas of `Start/LambdaMuExpand.lean`:

* `LambdaMu.Tm.msub σ ρ t` — the **simultaneous substitution of terms for term variables and of
  stacks for names**: `σ` replaces a term variable, and the stack `ρ β` is appended to the
  command `[β]u`;
* `LambdaMu.RedK A Δ t` — the reducibility candidates, in Kripke form over context renamings
  (`LambdaMu.RenOK`), carrying the typing; `LambdaMu.RStk Δ A π R` — the reducible stacks taking
  `A` to `R`;
* `LambdaMu.redK_sn` (CR1), `LambdaMu.redK_varHead` (CR3), `LambdaMu.redK_ren`,
  `LambdaMu.redK_apps`, `LambdaMu.redK_of_stk` — the candidate properties;
* `LambdaMu.Good Γ Δ σ ρ` — a reducible substitution for the context `Γ`;
* `LambdaMu.fundamental` — **the fundamental lemma**: `Typ Γ t A → Good Γ Δ σ ρ →
  RedK A Δ (msub σ ρ t)`;
* `LambdaMu.sn_of_typ` — **every typed λμ-term is strongly normalising**;
* `LambdaMu.sn_callcc_proof` — the corollary for classical natural deduction: a proof of a
  Peirce instance built with `call/cc` reduces to a normal form.
-/

import Start.LambdaMuExpand

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaMu

open Tm

namespace Tm

/-! ### Simultaneous substitution of terms and stacks -/

/-- Lifting a stack assignment under a binder. -/
def upR (ρ : ℕ → List Tm) : ℕ → List Tm
  | 0 => []
  | i + 1 => (ρ i).map (Tm.ren Nat.succ)

/-- **Simultaneous substitution**: `σ` for term variables, the stack `ρ β` appended at `[β]`. -/
def msub (σ : ℕ → Tm) (ρ : ℕ → List Tm) : Tm → Tm
  | var i => σ i
  | lam t => lam (msub (upS σ) (upR ρ) t)
  | app t u => app (msub σ ρ t) (msub σ ρ u)
  | mu β t => mu (nameOf (upS σ β)) (apps (msub (upS σ) (upR ρ) t) (upR ρ β))

theorem apps_append (t : Tm) : ∀ (π π' : List Tm), apps t (π ++ π') = apps (apps t π) π'
  | [], _ => rfl
  | u :: π, π' => apps_append (app t u) π π'

theorem ren_apps (r : ℕ → ℕ) (t : Tm) : ∀ (π : List Tm),
    Tm.ren r (apps t π) = apps (Tm.ren r t) (π.map (Tm.ren r))
  | [] => rfl
  | u :: π => ren_apps r (app t u) π

theorem subst_apps (σ : ℕ → Tm) (t : Tm) : ∀ (π : List Tm),
    subst σ (apps t π) = apps (subst σ t) (π.map (subst σ))
  | [] => rfl
  | u :: π => subst_apps σ (app t u) π

theorem sstr_apps (a : ℕ) (w : Tm) (t : Tm) : ∀ (π : List Tm),
    sstr a w (apps t π) = apps (sstr a w t) (π.map (sstr a w))
  | [] => rfl
  | u :: π => sstr_apps a w (app t u) π

theorem map_sstr_nameFree (a : ℕ) (w : Tm) : ∀ (S : List Tm), (∀ y ∈ S, NameFree a y) →
    S.map (sstr a w) = S
  | [], _ => rfl
  | y :: S, h => by
      rw [List.map_cons, sstr_nameFree y a w (h y (by simp)),
        map_sstr_nameFree a w S (fun z hz => h z (by simp [hz]))]

theorem msub_id : ∀ (t : Tm), msub var (fun _ => []) t = t
  | var _ => rfl
  | lam t => by
      have h1 : upS var = var := by funext i; cases i <;> rfl
      have h2 : upR (fun _ => []) = fun _ : ℕ => ([] : List Tm) := by funext i; cases i <;> rfl
      simp only [msub, h1, h2, msub_id t]
  | app t u => by simp only [msub, msub_id t, msub_id u]
  | mu β t => by
      have h1 : upS var = var := by funext i; cases i <;> rfl
      have h2 : upR (fun _ => []) = fun _ : ℕ => ([] : List Tm) := by funext i; cases i <;> rfl
      simp only [msub, h1, h2, msub_id t, nameOf, apps]

/-! ### `msub` and renaming -/

theorem upR_ren (r : ℕ → ℕ) (ρ : ℕ → List Tm) (i : ℕ) :
    (upR ρ i).map (Tm.ren (up r)) = upR (fun j => (ρ j).map (Tm.ren r)) i := by
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upR, List.map_map]
      congr 1
      funext v
      simp only [Function.comp_apply, ren_ren]
      rfl

theorem ren_msub : ∀ (t : Tm) (σ : ℕ → Tm) (ρ : ℕ → List Tm) (r : ℕ → ℕ), NamesVar σ t →
    Tm.ren r (msub σ ρ t) = msub (fun i => Tm.ren r (σ i)) (fun i => (ρ i).map (Tm.ren r)) t
  | var _, _, _, _, _ => rfl
  | lam t, σ, ρ, r, hnv => by
      have h1 : (fun i => Tm.ren (up r) (upS σ i)) = upS (fun j => Tm.ren r (σ j)) :=
        funext (ren_upS r σ)
      have h2 : (fun i => (upR ρ i).map (Tm.ren (up r))) =
          upR (fun j => (ρ j).map (Tm.ren r)) := funext (upR_ren r ρ)
      simp only [msub, Tm.ren, ren_msub t (upS σ) (upR ρ) (up r) hnv, h1, h2]
  | app t u, σ, ρ, r, hnv => by
      simp only [msub, Tm.ren, ren_msub t σ ρ r hnv.1, ren_msub u σ ρ r hnv.2]
  | mu β t, σ, ρ, r, hnv => by
      obtain ⟨⟨j, hj⟩, hnv'⟩ := hnv
      have h1 : (fun i => Tm.ren (up r) (upS σ i)) = upS (fun j => Tm.ren r (σ j)) :=
        funext (ren_upS r σ)
      have h2 : (fun i => (upR ρ i).map (Tm.ren (up r))) =
          upR (fun j => (ρ j).map (Tm.ren r)) := funext (upR_ren r ρ)
      have hname : up r (nameOf (upS σ β)) = nameOf (upS (fun i => Tm.ren r (σ i)) β) := by
        cases β with
        | zero => rfl
        | succ i =>
            simp only [upS] at hj ⊢
            cases hσ : σ i with
            | var k =>
                rw [hσ] at hj
                simp only [Tm.ren, nameOf, up]
            | lam s => rw [hσ] at hj; simp [Tm.ren] at hj
            | app s s' => rw [hσ] at hj; simp [Tm.ren] at hj
            | mu b s => rw [hσ] at hj; simp [Tm.ren] at hj
      simp only [msub, Tm.ren, ren_apps, ren_msub t (upS σ) (upR ρ) (up r) hnv', h1, h2, hname,
        upR_ren r ρ β]

/-! ### `msub` and substitution -/

theorem upR_subst (τ : ℕ → Tm) (ρ : ℕ → List Tm) (i : ℕ) :
    (upR ρ i).map (subst (upS τ)) = upR (fun j => (ρ j).map (subst τ)) i := by
  cases i with
  | zero => rfl
  | succ i =>
      simp only [upR, List.map_map]
      congr 1
      funext v
      simp only [Function.comp_apply]
      exact ren_succ_upS τ v

theorem subst_msub : ∀ (t : Tm) (σ : ℕ → Tm) (ρ : ℕ → List Tm) (τ : ℕ → Tm), NamesVar σ t →
    subst τ (msub σ ρ t) =
      msub (fun i => subst τ (σ i)) (fun i => (ρ i).map (subst τ)) t
  | var _, _, _, _, _ => rfl
  | lam t, σ, ρ, τ, hnv => by
      have h1 : (fun i => subst (upS τ) (upS σ i)) = upS (fun j => subst τ (σ j)) :=
        funext (upS_comp τ σ)
      have h2 : (fun i => (upR ρ i).map (subst (upS τ))) =
          upR (fun j => (ρ j).map (subst τ)) := funext (upR_subst τ ρ)
      simp only [msub, subst, subst_msub t (upS σ) (upR ρ) (upS τ) hnv, h1, h2]
  | app t u, σ, ρ, τ, hnv => by
      simp only [msub, subst, subst_msub t σ ρ τ hnv.1, subst_msub u σ ρ τ hnv.2]
  | mu β t, σ, ρ, τ, hnv => by
      obtain ⟨⟨j, hj⟩, hnv'⟩ := hnv
      have h1 : (fun i => subst (upS τ) (upS σ i)) = upS (fun j => subst τ (σ j)) :=
        funext (upS_comp τ σ)
      have h2 : (fun i => (upR ρ i).map (subst (upS τ))) =
          upR (fun j => (ρ j).map (subst τ)) := funext (upR_subst τ ρ)
      have hname : nameOf (upS τ (nameOf (upS σ β))) =
          nameOf (upS (fun i => subst τ (σ i)) β) := by
        cases β with
        | zero => rfl
        | succ i =>
            simp only [upS] at hj ⊢
            cases hσ : σ i with
            | var k =>
                rw [hσ] at hj
                simp only [Tm.ren, var.injEq] at hj
                subst hj
                simp only [subst, Tm.ren, nameOf]
            | lam s => rw [hσ] at hj; simp [Tm.ren] at hj
            | app s s' => rw [hσ] at hj; simp [Tm.ren] at hj
            | mu b s => rw [hσ] at hj; simp [Tm.ren] at hj
      simp only [msub, subst, subst_apps, subst_msub t (upS σ) (upR ρ) (upS τ) hnv', h1, h2,
        hname, upR_subst τ ρ β]

/-- The substitution `0 ↦ u`, `i + 1 ↦ σ i`. -/
def consT (u : Tm) (σ : ℕ → Tm) : ℕ → Tm
  | 0 => u
  | i + 1 => σ i

/-- The stack assignment `0 ↦ π`, `i + 1 ↦ ρ i`. -/
def consR (π : List Tm) (ρ : ℕ → List Tm) : ℕ → List Tm
  | 0 => π
  | i + 1 => ρ i

theorem subst_single_msub (t : Tm) (σ : ℕ → Tm) (ρ : ℕ → List Tm) (u : Tm)
    (hnv : NamesVar (upS σ) t) :
    subst (single u) (msub (upS σ) (upR ρ) t) = msub (consT u σ) (consR [] ρ) t := by
  rw [subst_msub t (upS σ) (upR ρ) (single u) hnv]
  have h1 : (fun i => subst (single u) (upS σ i)) = consT u σ := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact subst_single_ren u (σ i)
  have h2 : (fun i => (upR ρ i).map (subst (single u))) = consR [] ρ := by
    funext i
    cases i with
    | zero => rfl
    | succ i =>
        show (upR ρ (i + 1)).map (subst (single u)) = ρ i
        simp only [upR, List.map_map]
        rw [show ((subst (single u)) ∘ (Tm.ren Nat.succ)) = id by
          funext v; simp only [Function.comp_apply, id]; exact subst_single_ren u v]
        simp
  rw [h1, h2]

/-! ### `msub` and the structural substitution of a stack -/

/-- Appending `w` to the stack of the name `a`. -/
def updAt (ρ : ℕ → List Tm) (a : ℕ) (w : Tm) : ℕ → List Tm :=
  fun i => if i = a then ρ i ++ [w] else ρ i

theorem upR_updAt (ρ : ℕ → List Tm) (a : ℕ) (w : Tm) :
    upR (updAt ρ a w) = updAt (upR ρ) (a + 1) (Tm.ren Nat.succ w) := by
  funext i
  cases i with
  | zero => simp [upR, updAt]
  | succ i =>
      by_cases h : i = a
      · subst h
        simp [upR, updAt]
      · have h' : ¬ (i + 1 = a + 1) := by omega
        simp [upR, updAt, h]

/-- **The structural substitution of one argument commutes with `msub`.** -/
theorem sstr_msub : ∀ (t : Tm) (τ : ℕ → Tm) (ρ0 : ℕ → List Tm) (a : ℕ) (w : Tm),
    τ a = var a → (∀ i, τ i = var a → i = a) → (∀ i, NameFree a (τ i)) →
    NamesVar τ t → (∀ i, ∀ y ∈ ρ0 i, NameFree a y) →
    sstr a w (msub τ ρ0 t) = msub τ (updAt ρ0 a w) t
  | var i, τ, ρ0, a, w, _, _, hfree, _, _ => sstr_nameFree _ _ _ (hfree i)
  | lam t, τ, ρ0, a, w, hfix, hinj, hfree, hnv, hρ => by
      have hfix' : upS τ (a + 1) = var (a + 1) := by simp [upS, hfix, Tm.ren]
      have hinj' : ∀ i, upS τ i = var (a + 1) → i = a + 1 := by
        intro i hi
        cases i with
        | zero => simp [upS] at hi
        | succ i =>
            simp only [upS] at hi
            cases hσ : τ i with
            | var k =>
                rw [hσ] at hi
                simp only [Tm.ren, var.injEq] at hi
                have hia : i = a := hinj i (by rw [hσ, show k = a by omega])
                omega
            | lam _ => rw [hσ] at hi; simp [Tm.ren] at hi
            | app _ _ => rw [hσ] at hi; simp [Tm.ren] at hi
            | mu _ _ => rw [hσ] at hi; simp [Tm.ren] at hi
      have hfree' : ∀ i, NameFree (a + 1) (upS τ i) := by
        intro i
        cases i with
        | zero => trivial
        | succ i => exact nameFree_ren_succ (hfree i)
      have hρ' : ∀ i, ∀ y ∈ upR ρ0 i, NameFree (a + 1) y := by
        intro i y hy
        cases i with
        | zero => simp [upR] at hy
        | succ i =>
            simp only [upR, List.mem_map] at hy
            obtain ⟨z, hz, rfl⟩ := hy
            exact nameFree_ren_succ (hρ i z hz)
      simp only [msub, sstr,
        sstr_msub t (upS τ) (upR ρ0) (a + 1) (Tm.ren Nat.succ w) hfix' hinj' hfree' hnv hρ',
        upR_updAt]
  | app t u, τ, ρ0, a, w, hfix, hinj, hfree, hnv, hρ => by
      simp only [msub, sstr, sstr_msub t τ ρ0 a w hfix hinj hfree hnv.1 hρ,
        sstr_msub u τ ρ0 a w hfix hinj hfree hnv.2 hρ]
  | mu β t, τ, ρ0, a, w, hfix, hinj, hfree, hnv, hρ => by
      obtain ⟨⟨j, hj⟩, hnv'⟩ := hnv
      have hfix' : upS τ (a + 1) = var (a + 1) := by simp [upS, hfix, Tm.ren]
      have hinj' : ∀ i, upS τ i = var (a + 1) → i = a + 1 := by
        intro i hi
        cases i with
        | zero => simp [upS] at hi
        | succ i =>
            simp only [upS] at hi
            cases hσ : τ i with
            | var k =>
                rw [hσ] at hi
                simp only [Tm.ren, var.injEq] at hi
                have hia : i = a := hinj i (by rw [hσ, show k = a by omega])
                omega
            | lam _ => rw [hσ] at hi; simp [Tm.ren] at hi
            | app _ _ => rw [hσ] at hi; simp [Tm.ren] at hi
            | mu _ _ => rw [hσ] at hi; simp [Tm.ren] at hi
      have hfree' : ∀ i, NameFree (a + 1) (upS τ i) := by
        intro i
        cases i with
        | zero => trivial
        | succ i => exact nameFree_ren_succ (hfree i)
      have hρ' : ∀ i, ∀ y ∈ upR ρ0 i, NameFree (a + 1) y := by
        intro i y hy
        cases i with
        | zero => simp [upR] at hy
        | succ i =>
            simp only [upR, List.mem_map] at hy
            obtain ⟨z, hz, rfl⟩ := hy
            exact nameFree_ren_succ (hρ i z hz)
      have ih := sstr_msub t (upS τ) (upR ρ0) (a + 1) (Tm.ren Nat.succ w) hfix' hinj' hfree'
        hnv' hρ'
      have hstk : (upR ρ0 β).map (sstr (a + 1) (Tm.ren Nat.succ w)) = upR ρ0 β :=
        map_sstr_nameFree _ _ _ (hρ' β)
      have hcond : (β = a + 1) ↔ (nameOf (upS τ β) = a + 1) := by
        constructor
        · rintro rfl; rw [hfix']; rfl
        · intro h
          refine hinj' β ?_
          rw [hj] at h ⊢
          simp only [nameOf] at h
          rw [h]
      by_cases hβ : β = a + 1
      · have h2 : nameOf (upS τ β) = a + 1 := hcond.1 hβ
        simp only [msub, sstr, sstr_apps, ite_eq_left h2, ih, hstk, upR_updAt, updAt, ite_eq_left hβ,
          apps_append]
        rfl
      · have h2 : ¬ nameOf (upS τ β) = a + 1 := fun h => hβ (hcond.2 h)
        simp only [msub, sstr, sstr_apps, ite_eq_right h2, ih, hstk, upR_updAt, updAt, ite_eq_right hβ]

/-- Appending a whole (shifted) stack to the stack of the name `0`. -/
def updStk (ρ : ℕ → List Tm) (π : List Tm) : ℕ → List Tm :=
  fun i => if i = 0 then ρ i ++ π.map (Tm.ren Nat.succ) else ρ i

/-- **The iterated structural substitution of a stack commutes with `msub`.** -/
theorem sbs_msub : ∀ (π : List Tm) (t : Tm) (τ : ℕ → Tm) (ρ0 : ℕ → List Tm) (β : ℕ),
    τ 0 = var 0 → (∀ i, τ i = var 0 → i = 0) → (∀ i, NameFree 0 (τ i)) →
    NamesVar τ t → (∀ i, ∀ y ∈ ρ0 i, NameFree 0 y) → (∃ j, τ β = var j) →
    sbs π (nameOf (τ β)) (apps (msub τ ρ0 t) (ρ0 β)) =
      apps (msub τ (updStk ρ0 π) t) (updStk ρ0 π β)
  | [], t, τ, ρ0, β, _, _, _, _, _, _ => by
      have h : updStk ρ0 [] = ρ0 := by
        funext i; simp [updStk]
      simp [sbs, h]
  | v :: π, t, τ, ρ0, β, hfix, hinj, hfree, hnv, hρ, hvar => by
      obtain ⟨j, hj⟩ := hvar
      set w := Tm.ren Nat.succ v with hw
      have hwfree : NameFree 0 w := nameFree_zero_ren_succ v
      have hmain := sstr_msub t τ ρ0 0 w hfix hinj hfree hnv hρ
      have hstk : (ρ0 β).map (sstr 0 w) = ρ0 β := map_sstr_nameFree _ _ _ (hρ β)
      have hρ1 : ∀ i, ∀ y ∈ updAt ρ0 0 w i, NameFree 0 y := by
        intro i y hy
        by_cases hi : i = 0
        · subst hi
          have hy' : y ∈ ρ0 0 ++ [w] := by simpa [updAt] using hy
          rcases List.mem_append.1 hy' with hy2 | hy2
          · exact hρ 0 y hy2
          · rw [List.mem_singleton.1 hy2]; exact hwfree
        · have hy' : y ∈ ρ0 i := by simpa [updAt, hi] using hy
          exact hρ i y hy'
      have hstep : sb w (nameOf (τ β)) (apps (msub τ ρ0 t) (ρ0 β)) =
          apps (msub τ (updAt ρ0 0 w) t) (updAt ρ0 0 w β) := by
        have hsstr : sstr 0 w (apps (msub τ ρ0 t) (ρ0 β)) =
            apps (msub τ (updAt ρ0 0 w) t) (ρ0 β) := by
          rw [sstr_apps, hmain, hstk]
        by_cases hβ : β = 0
        · subst hβ
          have hn : nameOf (τ 0) = 0 := by rw [hfix]; rfl
          have hupd : updAt ρ0 0 w 0 = ρ0 0 ++ [w] := by simp [updAt]
          rw [hupd]
          simp only [sb, ite_eq_left hn, hsstr, apps_append]
          rfl
        · have hupd : updAt ρ0 0 w β = ρ0 β := by simp [updAt, hβ]
          have hn : ¬ nameOf (τ β) = 0 := by
            rw [hj]
            simp only [nameOf]
            intro h
            exact hβ (hinj β (by rw [hj, h]))
          rw [hupd]
          simp only [sb, ite_eq_right hn, hsstr]
      have ih := sbs_msub π t τ (updAt ρ0 0 w) β hfix hinj hfree hnv hρ1 ⟨j, hj⟩
      have hcomb : updStk (updAt ρ0 0 w) π = updStk ρ0 (v :: π) := by
        funext i
        by_cases hi : i = 0
        · subst hi; simp [updStk, updAt, hw]
        · simp [updStk, updAt, hi]
      show sbs π (nameOf (τ β)) (sb w (nameOf (τ β)) (apps (msub τ ρ0 t) (ρ0 β))) = _
      rw [hstep, ih, hcomb]

end Tm

/-! ### The reducibility candidates -/

/-- A renaming that maps the context `Γ` into `Δ`. -/
def RenOK (r : ℕ → ℕ) (Γ Δ : List Entry) : Prop := ∀ i e, Γ[i]? = some e → Δ[r i]? = some e

theorem RenOK.id (Γ : List Entry) : RenOK _root_.id Γ Γ := fun _ _ h => h

theorem RenOK.comp {r r' : ℕ → ℕ} {Γ Δ Θ : List Entry} (h : RenOK r Γ Δ) (h' : RenOK r' Δ Θ) :
    RenOK (fun i => r' (r i)) Γ Θ := fun i e hi => h' _ _ (h i e hi)

theorem RenOK.succ (Γ : List Entry) (e : Entry) : RenOK Nat.succ Γ (e :: Γ) :=
  fun _ _ h => by simpa using h

theorem RenOK.up {r : ℕ → ℕ} {Γ Δ : List Entry} (h : RenOK r Γ Δ) (e : Entry) :
    RenOK (Tm.up r) (e :: Γ) (e :: Δ) := by
  intro i e' hi
  cases i with
  | zero => simpa [Tm.up] using hi
  | succ i => simpa [Tm.up] using h i e' (by simpa using hi)

/-- **The reducibility candidates**, in Kripke form over context renamings. -/
def RedK : Ty → List Entry → Tm → Prop
  | .atom k, Δ, t => Typ Δ t (.atom k) ∧ SN t
  | .arr A B, Δ, t => Typ Δ t (.arr A B) ∧
      ∀ (Δ' : List Entry) (r : ℕ → ℕ), RenOK r Δ Δ' → ∀ u, RedK A Δ' u →
        RedK B Δ' (app (Tm.ren r t) u)

theorem redK_typ : ∀ {A : Ty} {Δ : List Entry} {t : Tm}, RedK A Δ t → Typ Δ t A
  | .atom _, _, _, h => h.1
  | .arr _ _, _, _, h => h.1

/-- Reducibility is stable under context renamings. -/
theorem redK_ren : ∀ (A : Ty) {Δ Δ' : List Entry} {t : Tm} {r : ℕ → ℕ}, RedK A Δ t →
    RenOK r Δ Δ' → RedK A Δ' (Tm.ren r t)
  | .atom k, Δ, Δ', t, r, h, hr => ⟨h.1.ren r hr, h.2.ren r⟩
  | .arr A B, Δ, Δ', t, r, h, hr => by
      refine ⟨h.1.ren r hr, fun Δ'' r' hr' u hu => ?_⟩
      have := h.2 Δ'' (fun i => r' (r i)) (hr.comp hr') u hu
      rwa [Tm.ren_ren]

theorem varHead_ren {h : Tm} (hv : VarHead h) (r : ℕ → ℕ) : VarHead (Tm.ren r h) := by
  induction hv with
  | var i => exact .var _
  | app u _ ih => exact .app _ ih

/-- **CR1 and CR3**: reducible terms are SN, and typed SN variable-headed spines are reducible. -/
theorem redK_cr : ∀ (A : Ty),
    (∀ {Δ : List Entry} {t : Tm}, RedK A Δ t → SN t) ∧
      (∀ {Δ : List Entry} {h : Tm}, VarHead h → SN h → Typ Δ h A → RedK A Δ h)
  | .atom k => ⟨fun h => h.2, fun hv hsn ht => ⟨ht, hsn⟩⟩
  | .arr A B => by
      obtain ⟨cr1A, cr3A⟩ := redK_cr A
      obtain ⟨cr1B, cr3B⟩ := redK_cr B
      constructor
      · intro Δ t h
        have hvar : RedK A (.tm A :: Δ) (var 0) :=
          cr3A (.var 0) (sn_var 0) (.var (by simp))
        have := h.2 (.tm A :: Δ) Nat.succ (RenOK.succ Δ _) _ hvar
        exact SN.of_ren_succ (sn_app_left (cr1B this))
      · intro Δ h hv hsn ht
        refine ⟨ht, fun Δ' r hr u hu => ?_⟩
        refine cr3B (.app u (varHead_ren hv r)) (sn_app_varHead (varHead_ren hv r)
          (hsn.ren r) (cr1A hu)) (.app (ht.ren r hr) (redK_typ hu))

theorem redK_sn {A : Ty} {Δ : List Entry} {t : Tm} (h : RedK A Δ t) : SN t := (redK_cr A).1 h

theorem redK_varHead {A : Ty} {Δ : List Entry} {h : Tm} (hv : VarHead h) (hsn : SN h)
    (ht : Typ Δ h A) : RedK A Δ h := (redK_cr A).2 hv hsn ht

theorem redK_var {A : Ty} {Δ : List Entry} {i : ℕ} (hi : Δ[i]? = some (.tm A)) :
    RedK A Δ (var i) := redK_varHead (.var i) (sn_var i) (.var hi)

/-- Reducible stacks: applying a reducible term of type `A` to `π` lands in `R`. -/
inductive RStk (Δ : List Entry) : Ty → List Tm → Ty → Prop
  | nil (A : Ty) : RStk Δ A [] A
  | cons {u : Tm} {A B : Ty} {π : List Tm} {R : Ty} :
      RedK A Δ u → RStk Δ B π R → RStk Δ (.arr A B) (u :: π) R

theorem RStk.tstk {Δ : List Entry} {A : Ty} {π : List Tm} {R : Ty} (h : RStk Δ A π R) :
    TStk Δ A π R := by
  induction h with
  | nil A => exact .nil A
  | cons hu _ ih => exact .cons (redK_typ hu) ih

theorem RStk.sn {Δ : List Entry} {A : Ty} {π : List Tm} {R : Ty} (h : RStk Δ A π R) :
    ∀ v ∈ π, SN v := by
  induction h with
  | nil A => intro v hv; simp at hv
  | cons hu _ ih =>
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact redK_sn hu
      · exact ih v hv

theorem RStk.ren {Δ Δ' : List Entry} {A : Ty} {π : List Tm} {R : Ty} {r : ℕ → ℕ}
    (h : RStk Δ A π R) (hr : RenOK r Δ Δ') : RStk Δ' A (π.map (Tm.ren r)) R := by
  induction h with
  | nil A => exact .nil A
  | cons hu _ ih => exact .cons (redK_ren _ hu hr) ih

/-- **Reducible terms applied to reducible stacks are SN.** -/
theorem redK_apps : ∀ {A : Ty} {Δ : List Entry} {t : Tm} {π : List Tm} {R : Ty},
    RedK A Δ t → RStk Δ A π R → SN (apps t π) := by
  intro A
  induction A with
  | atom k =>
      intro Δ t π R ht hπ
      cases hπ with
      | nil => exact redK_sn ht
  | arr A B _ ihB =>
      intro Δ t π R ht hπ
      cases hπ with
      | nil => exact redK_sn ht
      | cons hu hπ' =>
          have := ht.2 Δ _root_.id (RenOK.id Δ) _ hu
          rw [Tm.ren_id] at this
          have h2 := ihB this hπ'
          exact h2

/-- **The stack criterion for reducibility.** -/
theorem redK_of_stk : ∀ (A : Ty) {Δ : List Entry} {t : Tm}, Typ Δ t A →
    (∀ (Δ' : List Entry) (r : ℕ → ℕ), RenOK r Δ Δ' → ∀ (π : List Tm) (R : Ty),
      RStk Δ' A π R → SN (apps (Tm.ren r t) π)) → RedK A Δ t
  | .atom k, Δ, t, ht, h => by
      refine ⟨ht, ?_⟩
      have := h Δ _root_.id (RenOK.id Δ) [] (.atom k) (.nil _)
      rwa [Tm.ren_id] at this
  | .arr A B, Δ, t, ht, h => by
      refine ⟨ht, fun Δ' r hr u hu => ?_⟩
      refine redK_of_stk B (.app (ht.ren r hr) (redK_typ hu)) fun Δ'' r' hr' π R hπ => ?_
      have hstk : RStk Δ'' (.arr A B) (Tm.ren r' u :: π) R :=
        .cons (redK_ren A hu hr') hπ
      have := h Δ'' (fun i => r' (r i)) (hr.comp hr') _ R hstk
      rw [← Tm.ren_ren] at this
      exact this

/-! ### Reducible substitutions -/

/-- A reducible substitution: terms for term variables, names with reducible stacks for names. -/
def Good (Γ Δ : List Entry) (σ : ℕ → Tm) (ρ : ℕ → List Tm) : Prop :=
  (∀ i A, Γ[i]? = some (.tm A) → RedK A Δ (σ i)) ∧
    (∀ i A, Γ[i]? = some (.nm A) → ∃ j R, σ i = var j ∧ Δ[j]? = some (.nm R) ∧
      RStk Δ A (ρ i) R)

theorem Good.namesVar {Γ Δ : List Entry} {σ : ℕ → Tm} {ρ : ℕ → List Tm} (h : Good Γ Δ σ ρ)
    {t : Tm} {A : Ty} (ht : Typ Γ t A) : NamesVar σ t :=
  namesVar_of_typ ht fun i B hi => by
    obtain ⟨j, R, hj, _, _⟩ := h.2 i B hi
    exact ⟨j, hj⟩

theorem Good.ren {Γ Δ Δ' : List Entry} {σ : ℕ → Tm} {ρ : ℕ → List Tm} (h : Good Γ Δ σ ρ)
    {r : ℕ → ℕ} (hr : RenOK r Δ Δ') :
    Good Γ Δ' (fun i => Tm.ren r (σ i)) (fun i => (ρ i).map (Tm.ren r)) := by
  refine ⟨fun i A hi => redK_ren A (h.1 i A hi) hr, fun i A hi => ?_⟩
  obtain ⟨j, R, hj, hΔ, hstk⟩ := h.2 i A hi
  refine ⟨r j, R, ?_, hr _ _ hΔ, hstk.ren hr⟩
  show Tm.ren r (σ i) = var (r j)
  rw [hj]
  rfl

theorem Good.up {Γ Δ : List Entry} {σ : ℕ → Tm} {ρ : ℕ → List Tm} (h : Good Γ Δ σ ρ)
    (e : Entry) : Good (e :: Γ) (e :: Δ) (Tm.upS σ) (Tm.upR ρ) := by
  have hs := h.ren (RenOK.succ Δ e)
  constructor
  · intro i A hi
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact redK_var (by simp)
    | succ i => exact hs.1 i A (by simpa using hi)
  · intro i A hi
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        subst hi
        exact ⟨0, A, rfl, by simp, .nil A⟩
    | succ i =>
        obtain ⟨j, R, hj, hΔ, hstk⟩ := hs.2 i A (by simpa using hi)
        exact ⟨j, R, hj, hΔ, hstk⟩

theorem Good.consT {Γ Δ : List Entry} {σ : ℕ → Tm} {ρ : ℕ → List Tm} (h : Good Γ Δ σ ρ)
    {A : Ty} {u : Tm} (hu : RedK A Δ u) :
    Good (.tm A :: Γ) Δ (Tm.consT u σ) (Tm.consR [] ρ) := by
  constructor
  · intro i B hi
    cases i with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Entry.tm.injEq] at hi
        subst hi
        exact hu
    | succ i => exact h.1 i B (by simpa using hi)
  · intro i B hi
    cases i with
    | zero => simp at hi
    | succ i => exact h.2 i B (by simpa using hi)

/-- The typing of a simultaneous substitution. -/
theorem msub_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {Δ : List Entry} {σ : ℕ → Tm} {ρ : ℕ → List Tm}, Good Γ Δ σ ρ →
      Typ Δ (Tm.msub σ ρ t) A := by
  induction h with
  | var hi => intro Δ σ ρ hg; exact redK_typ (hg.1 _ _ hi)
  | lam _ ih => intro Δ σ ρ hg; exact .lam (ih (hg.up _))
  | app _ _ iht ihu => intro Δ σ ρ hg; exact .app (iht hg) (ihu hg)
  | @mu Γ β t A B _ hβ ih =>
      intro Δ σ ρ hg
      obtain ⟨j, R, hj, hΔ, hstk⟩ := (hg.up (.nm A)).2 β B hβ
      refine .mu (B := R) (typ_apps hstk.tstk (ih (hg.up (.nm A)))) ?_
      rw [hj]
      exact hΔ

/-! ### The fundamental lemma -/

/-- **The fundamental lemma of reducibility for λμ.** -/
theorem fundamental {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) :
    ∀ {Δ : List Entry} {σ : ℕ → Tm} {ρ : ℕ → List Tm}, Good Γ Δ σ ρ →
      RedK A Δ (Tm.msub σ ρ t) := by
  induction h with
  | var hi => intro Δ σ ρ hg; exact hg.1 _ _ hi
  | @app Γ f a A B hf _ ihf iha =>
      intro Δ σ ρ hg
      have h1 := ihf hg
      have := h1.2 Δ _root_.id (RenOK.id Δ) _ (iha hg)
      rwa [Tm.ren_id] at this
  | @lam Γ X A B hX ih =>
      intro Δ σ ρ hg
      have htyp : Typ Δ (Tm.msub σ ρ (lam X)) (.arr A B) := msub_typ (.lam hX) hg
      refine redK_of_stk _ htyp fun Δ' r hr π R hπ => ?_
      have hnvX : NamesVar (Tm.upS σ) X := (hg.up (.tm A)).namesVar hX
      have hren : Tm.ren r (Tm.msub σ ρ (lam X)) =
          lam (Tm.msub (Tm.upS fun i => Tm.ren r (σ i)) (Tm.upR fun i => (ρ i).map (Tm.ren r)) X) := by
        rw [Tm.ren_msub _ σ ρ r (hg.namesVar (Typ.lam hX))]
        rfl
      rw [hren]
      cases hπ with
      | nil =>
          exact sn_lam (redK_sn (ih ((hg.ren hr).up (.tm A))))
      | @cons u A' B' π' R' hu hπ' =>
          have hgr := hg.ren hr
          have hnv' : NamesVar (Tm.upS fun i => Tm.ren r (σ i)) X := hgr.up (.tm A) |>.namesVar hX
          have hXtyp : Typ (.tm A :: Δ') (Tm.msub (Tm.upS fun i => Tm.ren r (σ i))
              (Tm.upR fun i => (ρ i).map (Tm.ren r)) X) B := msub_typ hX (hgr.up (.tm A))
          refine sn_apps_beta (redK_sn hu) hXtyp hπ'.sn ?_
          rw [Tm.subst_single_msub X _ _ u hnv']
          exact redK_apps (ih (hgr.consT hu)) hπ'
  | @mu Γ β t A B ht hβ ih =>
      intro Δ σ ρ hg
      have htyp : Typ Δ (Tm.msub σ ρ (mu β t)) A := msub_typ (.mu ht hβ) hg
      refine redK_of_stk _ htyp fun Δ' r hr π R hπ => ?_
      have hgr := hg.ren hr
      rw [Tm.ren_msub _ σ ρ r (hg.namesVar (Typ.mu ht hβ))]
      set σ' : ℕ → Tm := fun i => Tm.ren r (σ i) with hσ'
      set ρ' : ℕ → List Tm := fun i => (ρ i).map (Tm.ren r) with hρ'
      have hM : Typ Δ' (Tm.msub σ' ρ' (mu β t)) A := msub_typ (.mu ht hβ) hgr
      have hgup := hgr.up (.nm A)
      obtain ⟨j, _, hj, _, _⟩ := hgup.2 β B hβ
      have hnvt : NamesVar (Tm.upS σ') t := hgup.namesVar ht
      have hfix : Tm.upS σ' 0 = var 0 := rfl
      have hinj : ∀ i, Tm.upS σ' i = var 0 → i = 0 := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => simp only [Tm.upS] at hi; cases hs : σ' i <;> rw [hs] at hi <;> simp [Tm.ren] at hi
      have hfree : ∀ i, NameFree 0 (Tm.upS σ' i) := by
        intro i
        cases i with
        | zero => trivial
        | succ i => exact nameFree_zero_ren_succ _
      have hρfree : ∀ i, ∀ y ∈ Tm.upR ρ' i, NameFree 0 y := by
        intro i y hy
        cases i with
        | zero => simp [Tm.upR] at hy
        | succ i =>
            simp only [Tm.upR, List.mem_map] at hy
            obtain ⟨z, _, rfl⟩ := hy
            exact nameFree_zero_ren_succ z
      have hsbs := Tm.sbs_msub π t (Tm.upS σ') (Tm.upR ρ') β hfix hinj hfree hnvt hρfree ⟨j, hj⟩
      have hrs : RenOK Nat.succ Δ' (.nm R :: Δ') := RenOK.succ Δ' _
      have hgood2 : Good (.nm A :: Γ) (.nm R :: Δ') (Tm.upS σ') (Tm.updStk (Tm.upR ρ') π) := by
        constructor
        · intro i A' hi
          cases i with
          | zero => simp at hi
          | succ i =>
              have := redK_ren A' (hgr.1 i A' (by simpa using hi)) hrs
              simpa [Tm.upS] using this
        · intro i A' hi
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq, Entry.nm.injEq] at hi
              subst hi
              refine ⟨0, R, rfl, by simp, ?_⟩
              simpa [Tm.updStk, Tm.upR] using hπ.ren hrs
          | succ i =>
              obtain ⟨j', R', hj', hΔ', hstk'⟩ := hgr.2 i A' (by simpa using hi)
              refine ⟨j' + 1, R', by simp [Tm.upS, hj', Tm.ren], by simpa using hΔ', ?_⟩
              have : Tm.updStk (Tm.upR ρ') π (i + 1) = (ρ' i).map (Tm.ren Nat.succ) := by
                simp [Tm.updStk, Tm.upR]
              rw [this]
              exact hstk'.ren hrs
      have hbody : RedK B (.nm R :: Δ') (Tm.msub (Tm.upS σ') (Tm.updStk (Tm.upR ρ') π) t) :=
        ih hgood2
      obtain ⟨_, R2, _, _, hstk2⟩ := hgood2.2 β B hβ
      have hsn : SN (apps (Tm.msub (Tm.upS σ') (Tm.updStk (Tm.upR ρ') π) t)
          (Tm.updStk (Tm.upR ρ') π β)) := redK_apps hbody hstk2
      refine sn_apps_mu π hM hπ.tstk hπ.sn ?_
      show SN (mu (nameOf (Tm.upS σ' β)) (sbs π (nameOf (Tm.upS σ' β))
        (apps (Tm.msub (Tm.upS σ') (Tm.upR ρ') t) (Tm.upR ρ' β))))
      rw [hsbs]
      exact sn_mu hsn _

/-- **Strong normalisation of typed λμ.** -/
theorem sn_of_typ {Γ : List Entry} {t : Tm} {A : Ty} (h : Typ Γ t A) : SN t := by
  have hgood : Good Γ Γ var (fun _ => []) := by
    refine ⟨fun i A' hi => redK_var hi, fun i A' hi => ⟨i, A', rfl, hi, .nil A'⟩⟩
  have := fundamental h hgood
  rw [Tm.msub_id] at this
  exact redK_sn this

/-- **Normalisation of classical natural deduction**: a proof of an instance of Peirce's law
built with `call/cc` reduces to a normal form. -/
theorem sn_callcc (Γ : List Entry) (A B : Ty) : SN Tm.callcc :=
  sn_of_typ (typ_callcc Γ A B)

/-- Every term obtained by applying `call/cc` to a proof of `(A → B) → A` is SN. -/
theorem sn_callcc_proof {Γ : List Entry} {f : Tm} {A B : Ty}
    (hf : Typ Γ f (.arr (.arr A B) A)) : SN (app Tm.callcc f) :=
  sn_of_typ (.app (typ_callcc Γ A B) hf)

/-- An SN term reduces to a normal form. -/
theorem SN.exists_nf {t : Tm} (h : SN t) :
    ∃ n, Relation.ReflTransGen Step t n ∧ ∀ n', ¬ Step n n' := by
  induction h with
  | intro t _ ih =>
      by_cases hs : ∃ t', Step t t'
      · obtain ⟨t', ht'⟩ := hs
        obtain ⟨n, hn, hnf⟩ := ih t' ht'
        exact ⟨n, .head ht' hn, hnf⟩
      · exact ⟨t, .refl, fun n' hn' => hs ⟨n', hn'⟩⟩

/-- **Normalisation of classical natural deduction**: every proof of a Peirce instance
`((A → B) → A) → A` obtained by applying `call/cc` to a proof of `(A → B) → A` reduces to a
normal form. -/
theorem callcc_proof_normalizes {Γ : List Entry} {f : Tm} {A B : Ty}
    (hf : Typ Γ f (.arr (.arr A B) A)) :
    ∃ n, Relation.ReflTransGen Step (app Tm.callcc f) n ∧ ∀ n', ¬ Step n n' :=
  (sn_callcc_proof hf).exists_nf

end LambdaMu
