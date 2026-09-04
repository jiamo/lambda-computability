/-
Step-counting beta reduction.

`Lambda.reducesIn n t u` says that `t` reduces to `u` in exactly `n` beta steps.  It is the only
*time* measure on lambda terms in the library, and it is used both for the size-explosion family
of `Start/SizeExplosion.lean` (where the point is that few steps can produce a huge term) and for
the time-bounded complexity measures of `Start/LevinKt.lean` (where the point is that a short
program may need many steps).  It lives in its own module so that neither development has to
depend on the other.

Following the pattern of `Start/Reduction.lean`, the relation keeps its own inductive definition
and everything generic about it is imported from the abstract rewriting interface
`Start/Rewriting.lean` through the single bridging lemma `Lambda.reducesIn_iff_starN`.

* `Lambda.reducesIn` — the relation;
* `Lambda.reducesIn_iff_starN` — the bridge: it is `Rewriting.StarN Lambda.step`;
* `Lambda.reduces_of_reducesIn`, `Lambda.exists_reducesIn_of_reduces` — it refines `reduces`, and
  every reduction has a step count;
* `Lambda.reducesIn_trans` — step counts add along composition;
* `Lambda.reducesIn_app_left`, `Lambda.reducesIn_app_right`, `Lambda.reducesIn_app`,
  `Lambda.reducesIn_lam` — the congruences, with the expected step counts.
-/

import Start.Reduction

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

/-- `reducesIn n t u`: `t` reduces to `u` in exactly `n` beta steps. -/
inductive reducesIn : ℕ → Lambda → Lambda → Prop
  | refl (t : Lambda) : reducesIn 0 t t
  | step {n : ℕ} {t₁ t₂ t₃ : Lambda} :
      Lambda.step t₁ t₂ → reducesIn n t₂ t₃ → reducesIn (n + 1) t₁ t₃

/-- **Bridge to the abstract rewriting interface** (`Start/Rewriting.lean`): `reducesIn` is the
counted reflexive–transitive closure of `step`. -/
theorem reducesIn_iff_starN {n : ℕ} {t u : Lambda} :
    reducesIn n t u ↔ Rewriting.StarN Lambda.step n t u := by
  constructor
  · intro h
    induction h with
    | refl t => exact Rewriting.StarN.refl t
    | step hstep _ ih => exact Rewriting.StarN.step hstep ih
  · intro h
    induction h with
    | refl t => exact reducesIn.refl t
    | step hstep _ ih => exact reducesIn.step hstep ih

/-- A counted reduction is in particular a reduction. -/
theorem reduces_of_reducesIn {n : ℕ} {t u : Lambda} (h : reducesIn n t u) :
    Lambda.reduces t u :=
  Lambda.reduces_iff_star.2 (reducesIn_iff_starN.1 h).toStar

/-- Every reduction happens in some number of steps. -/
theorem exists_reducesIn_of_reduces {t u : Lambda} (h : Lambda.reduces t u) :
    ∃ n : ℕ, reducesIn n t u := by
  obtain ⟨n, hn⟩ := Rewriting.exists_starN_of_star (Lambda.reduces_iff_star.1 h)
  exact ⟨n, reducesIn_iff_starN.2 hn⟩

/-- A single beta step is a reduction in one step. -/
theorem reducesIn_one {t u : Lambda} (h : Lambda.step t u) : reducesIn 1 t u :=
  reducesIn.step h (reducesIn.refl u)

/-- Counted reductions compose. -/
theorem reducesIn_trans {m n : ℕ} {t u v : Lambda}
    (h₁ : reducesIn m t u) (h₂ : reducesIn n u v) : reducesIn (m + n) t v :=
  reducesIn_iff_starN.2 ((reducesIn_iff_starN.1 h₁).trans (reducesIn_iff_starN.1 h₂))

/-- Reduction in the left argument of an application, keeping the step count. -/
theorem reducesIn_app_left {n : ℕ} {t₁ t₁' t₂ : Lambda} (h : reducesIn n t₁ t₁') :
    reducesIn n (Lambda.app t₁ t₂) (Lambda.app t₁' t₂) :=
  reducesIn_iff_starN.2
    (Rewriting.StarN.map (fun t => Lambda.app t t₂)
      (fun _ _ hs => Lambda.step.app_left _ _ _ hs) (reducesIn_iff_starN.1 h))

/-- Reduction in the right argument of an application, keeping the step count. -/
theorem reducesIn_app_right {n : ℕ} {t₁ t₂ t₂' : Lambda} (h : reducesIn n t₂ t₂') :
    reducesIn n (Lambda.app t₁ t₂) (Lambda.app t₁ t₂') :=
  reducesIn_iff_starN.2
    (Rewriting.StarN.map (fun t => Lambda.app t₁ t)
      (fun _ _ hs => Lambda.step.app_right _ _ _ hs) (reducesIn_iff_starN.1 h))

/-- Reducing both arguments of an application costs the sum of the two step counts. -/
theorem reducesIn_app {m n : ℕ} {t₁ t₁' t₂ t₂' : Lambda}
    (h₁ : reducesIn m t₁ t₁') (h₂ : reducesIn n t₂ t₂') :
    reducesIn (m + n) (Lambda.app t₁ t₂) (Lambda.app t₁' t₂') :=
  reducesIn_trans (reducesIn_app_left h₁) (reducesIn_app_right h₂)

/-- Reduction under a lambda, keeping the step count. -/
theorem reducesIn_lam {n : ℕ} {t t' : Lambda} (h : reducesIn n t t') :
    reducesIn n (Lambda.lam t) (Lambda.lam t') :=
  reducesIn_iff_starN.2
    (Rewriting.StarN.map Lambda.lam (fun _ _ hs => Lambda.step.lam _ _ hs)
      (reducesIn_iff_starN.1 h))

end Lambda
