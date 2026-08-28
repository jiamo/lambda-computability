/-
Iterated application in `D∞`.

Böhm trees are compared node by node after η-expanding both nodes to a common arity, so the
semantic side of that comparison needs a convenient calculus of *iterated* application in `D∞`.
This file provides it:

* `ScottDinf.dappSeq x F n` — apply `x` to `F 0, …, F (n-1)`, in that order; this matches the
  syntactic `Lambda.appList`;
* `ScottDinf.dappN x A m` — apply `x` to `A (m-1), …, A 0`, in that order; here the argument is
  indexed by the de Bruijn index of the binder it is fed to, which is what makes the comparison
  with the tags of `Start/BohmEta.lean` immediate;
* `ScottDinf.envStack A b e ρ` — the environment inside `b` binders that have consumed the
  arguments `A (e + b - 1), …, A e`;
* `ScottDinf.dappN_lamN` — feeding `b + e` arguments to `λ…λ t` (with `b` binders) leaves the
  body in the environment `envStack A b e ρ`, with `e` arguments still to consume;
* `ScottDinf.ddenot_appList` — the denotation of an application spine is a `dappSeq`;
* `ScottDinf.dinf_ext_dappN` — two elements of `D∞` that behave alike on `m` arguments are
  equal, `D∞` being extensional.
-/

import Start.ScottDinfModel
import Start.Bohm

set_option relaxedAutoImplicit false
set_option autoImplicit false

open OmegaCompletePartialOrder

namespace ScottDinf

open Lambda

noncomputable section

/-! ## Applying a sequence of arguments -/

/-- `dappSeq x F n` applies `x` to `F 0, …, F (n-1)`, in that order. -/
def dappSeq (x : Dinf) (F : ℕ → Dinf) : ℕ → Dinf
  | 0 => x
  | (n + 1) => Phi (dappSeq x F n) (F n)

@[simp] theorem dappSeq_zero (x : Dinf) (F : ℕ → Dinf) : dappSeq x F 0 = x := rfl

theorem dappSeq_succ (x : Dinf) (F : ℕ → Dinf) (n : ℕ) :
    dappSeq x F (n + 1) = Phi (dappSeq x F n) (F n) := rfl

theorem dappSeq_congr {x y : Dinf} {F G : ℕ → Dinf} {n : ℕ} (hxy : x = y)
    (hFG : ∀ r, r < n → F r = G r) : dappSeq x F n = dappSeq y G n := by
  induction n with
  | zero => exact hxy
  | succ n ih =>
      rw [dappSeq_succ, dappSeq_succ, ih (fun r hr => hFG r (by omega)), hFG n (by omega)]

/-- Peeling the first argument off a `dappSeq`. -/
theorem dappSeq_succ_left (x : Dinf) (F : ℕ → Dinf) (n : ℕ) :
    dappSeq x F (n + 1) = dappSeq (Phi x (F 0)) (fun s => F (s + 1)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dappSeq_succ, ih, dappSeq_succ]

theorem dappSeq_add (x : Dinf) (F : ℕ → Dinf) (k e : ℕ) :
    dappSeq x F (k + e) = dappSeq (dappSeq x F k) (fun s => F (k + s)) e := by
  induction e with
  | zero => rfl
  | succ e ih =>
      rw [show k + (e + 1) = (k + e) + 1 from rfl, dappSeq_succ, ih, dappSeq_succ]

/-! ## Applying a stack of arguments -/

/-- `dappN x A m` applies `x` to `A (m-1), …, A 0`, in that order: the argument `A i` is the one
that ends up bound to the de Bruijn index `i`. -/
def dappN (x : Dinf) (A : ℕ → Dinf) : ℕ → Dinf
  | 0 => x
  | (m + 1) => dappN (Phi x (A m)) A m

@[simp] theorem dappN_zero (x : Dinf) (A : ℕ → Dinf) : dappN x A 0 = x := rfl

theorem dappN_succ (x : Dinf) (A : ℕ → Dinf) (m : ℕ) :
    dappN x A (m + 1) = dappN (Phi x (A m)) A m := rfl

theorem dappN_congr {x : Dinf} {A B : ℕ → Dinf} {m : ℕ} (h : ∀ k, k < m → A k = B k) :
    dappN x A m = dappN x B m := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [dappN_succ, dappN_succ, h m (by omega), ih (fun k hk => h k (by omega))]

/-- A stack of arguments is a sequence of arguments, read backwards. -/
theorem dappN_eq_dappSeq (x : Dinf) (A : ℕ → Dinf) : ∀ m : ℕ,
    dappN x A m = dappSeq x (fun s => A (m - 1 - s)) m := by
  intro m
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      rw [dappN_succ, ih, dappSeq_succ_left]
      refine dappSeq_congr rfl ?_
      intro s _
      congr 1
      omega

/-! ## Abstractions -/

/-- The environment inside `b` binders that have consumed the arguments `A (e + b - 1), …, A e`
of a stack. -/
def envStack (A : ℕ → Dinf) (b e : ℕ) (ρ : DEnv) : DEnv :=
  fun i => if i < b then A (e + i) else ρ (i - b)

theorem envStack_zero (A : ℕ → Dinf) (e : ℕ) (ρ : DEnv) : envStack A 0 e ρ = ρ := by
  funext i
  simp [envStack]

theorem envStack_succ (A : ℕ → Dinf) (b e : ℕ) (ρ : DEnv) :
    envStack A b e (dcons (A (b + e)) ρ) = envStack A (b + 1) e ρ := by
  funext i
  by_cases hi : i < b
  · simp only [envStack, if_pos hi, if_pos (by omega : i < b + 1)]
  · by_cases hi2 : i = b
    · subst hi2
      simp only [envStack, if_neg hi, if_pos (by omega : i < i + 1), Nat.sub_self, dcons_zero]
      congr 1
      omega
    · have h1 : ¬ i < b + 1 := by omega
      obtain ⟨j, rfl⟩ : ∃ j, i = b + (j + 1) := ⟨i - b - 1, by omega⟩
      simp only [envStack, if_neg hi, if_neg h1]
      rw [show b + (j + 1) - b = j + 1 from by omega, dcons_succ,
        show b + (j + 1) - (b + 1) = j from by omega]

theorem dappN_lam (t : Lambda) (ρ : DEnv) (A : ℕ → Dinf) (m : ℕ) :
    dappN (ddenot (Lambda.lam t) ρ) A (m + 1) = dappN (ddenot t (dcons (A m) ρ)) A m := by
  rw [dappN_succ, ddenot_lam_apply]

/-- Feeding `b + e` arguments to an abstraction with `b` binders. -/
theorem dappN_lamN : ∀ (b e : ℕ) (t : Lambda) (ρ : DEnv) (A : ℕ → Dinf),
    dappN (ddenot (Lambda.lamN b t) ρ) A (b + e) = dappN (ddenot t (envStack A b e ρ)) A e := by
  intro b
  induction b with
  | zero => intro e t ρ A; rw [Lambda.lamN_zero, envStack_zero, Nat.zero_add]
  | succ b ih =>
      intro e t ρ A
      rw [Lambda.lamN_succ, show b + 1 + e = (b + e) + 1 from by omega, dappN_lam,
        show b + e = b + e from rfl, ih e t (dcons (A (b + e)) ρ) A, envStack_succ]

/-! ## Application spines -/

theorem ddenot_appList : ∀ (l : List Lambda) (t : Lambda) (ρ : DEnv) (F : ℕ → Dinf),
    (∀ r, ∀ h : r < l.length, F r = ddenot l[r] ρ) →
    ddenot (Lambda.appList t l) ρ = dappSeq (ddenot t ρ) F l.length := by
  intro l
  induction l with
  | nil => intro t ρ F _; rfl
  | cons a rest ih =>
      intro t ρ F hF
      rw [Lambda.appList_cons, ih (Lambda.app t a) ρ (fun s => F (s + 1))
        (fun r hr => hF (r + 1) (by simpa using hr))]
      rw [List.length_cons, dappSeq_succ_left, ddenot_app, hF 0 (by simp)]
      rfl

/-! ## Extensionality -/

theorem Phi_inj {x y : Dinf} (h : ∀ a : Dinf, Phi x a = Phi y a) : x = y := by
  have hfun : Phi x = Phi y := DFunLike.ext _ _ h
  rw [← Psi_Phi x, ← Psi_Phi y, hfun]

/-- **`D∞` is extensional**: two elements that behave alike on `m` arguments are equal. -/
theorem dinf_ext_dappN : ∀ (m : ℕ) (x y : Dinf),
    (∀ A : ℕ → Dinf, dappN x A m = dappN y A m) → x = y := by
  intro m
  induction m with
  | zero => intro x y h; simpa using h (fun _ => Dinf.botDinf)
  | succ m ih =>
      intro x y h
      refine Phi_inj fun a => ?_
      refine ih (Phi x a) (Phi y a) fun A => ?_
      have key : ∀ B : ℕ → Dinf, B m = a → (∀ k, k < m → B k = A k) →
          dappN (Phi x a) A m = dappN (Phi y a) A m := by
        intro B hBm hBk
        have hB := h B
        rw [dappN_succ, dappN_succ, hBm] at hB
        rwa [dappN_congr hBk, dappN_congr hBk] at hB
      exact key (fun k => if k = m then a else A k) (by simp)
        (fun k hk => by simp [Nat.ne_of_lt hk])

end

end ScottDinf
