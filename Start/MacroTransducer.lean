/-
**Left-to-right transducers over a finite alphabet, on lists.**

The final state `mlst` and the output `mrun` of a left-to-right transducer with states `σ` reading
words over an alphabet `A`.  `Start/CobhamMacro.lean` compiles them into Cobham terms;
`Start/MultiTapeCobham.lean` uses them to simulate multi-tape machines.
-/

import Mathlib

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Macro

variable {A : Type}

/-! ### Transducers over `A` -/

variable {σ : Type}

/-- The state of a left-to-right transducer after a word. -/
def mlst (δ : σ → A → σ) : σ → List A → σ
  | s, [] => s
  | s, a :: u => mlst δ (δ s a) u

/-- The output of a left-to-right transducer on a word. -/
def mrun (δ : σ → A → σ) (out : σ → A → List A) : σ → List A → List A
  | _, [] => []
  | s, a :: u => out s a ++ mrun δ out (δ s a) u

@[simp] theorem mlst_nil (δ : σ → A → σ) (s : σ) : mlst δ s [] = s := rfl

@[simp] theorem mlst_cons (δ : σ → A → σ) (s : σ) (a : A) (u : List A) :
    mlst δ s (a :: u) = mlst δ (δ s a) u := rfl

@[simp] theorem mrun_nil (δ : σ → A → σ) (out : σ → A → List A) (s : σ) :
    mrun δ out s [] = [] := rfl

@[simp] theorem mrun_cons (δ : σ → A → σ) (out : σ → A → List A) (s : σ) (a : A)
    (u : List A) : mrun δ out s (a :: u) = out s a ++ mrun δ out (δ s a) u := rfl

theorem mlst_append (δ : σ → A → σ) (s : σ) (u v : List A) :
    mlst δ s (u ++ v) = mlst δ (mlst δ s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => exact ih (δ s a)

theorem mrun_append (δ : σ → A → σ) (out : σ → A → List A) (s : σ) (u v : List A) :
    mrun δ out s (u ++ v) = mrun δ out s u ++ mrun δ out (mlst δ s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih =>
    rw [List.cons_append, mrun_cons, mrun_cons, ih, List.append_assoc]
    rfl

end Macro

end Complexity
