/-
**Finite-state transducers over a finite alphabet are Cobham functions.**

`Start/CobhamTransducer.lean` turns finite-state transducers on bits into Cobham terms.  This
module lifts that statement to transducers whose input and output symbols range over an arbitrary
finite alphabet `A` and whose states range over an arbitrary finite type `σ`.  A symbol `a` is
written in binary as the block `1^{code a} 0`, and a word over `A` as the concatenation of the
blocks of its letters (`Macro.enc`).

Main definitions:

* `Complexity.Macro.enc` — the binary encoding of a word over `A`;
* `Complexity.Macro.mlst`, `Complexity.Macro.mrun` — the final state and the output of a
  left-to-right transducer on words over `A`;
* `Complexity.Macro.runTerm` — the Cobham term of the transduction;
* `Complexity.Macro.selectTerm` — a Cobham term choosing one of finitely many terms according to
  the final state of a transducer.

Main results:

* `Complexity.Macro.eval_runTerm` — `runTerm` computes `enc (mrun δ out s₀ u)` from `enc u`;
* `Complexity.Macro.eval_selectTerm` — `selectTerm` evaluates the term chosen by the final state.
-/

import Start.CobhamTransducer
import Start.MacroTransducer

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Macro

variable {A : Type} [Fintype A]

/-! ### The encoding -/

/-- The index of a symbol. -/
noncomputable def codeA (a : A) : ℕ := (Fintype.equivFin A a : ℕ)

theorem codeA_lt (a : A) : codeA a < Fintype.card A := (Fintype.equivFin A a).2

/-- The block of a symbol. -/
noncomputable def encSym (a : A) : Word := List.replicate (codeA a) true ++ [false]

/-- The binary encoding of a word over `A`. -/
noncomputable def enc (u : List A) : Word := u.flatMap encSym

@[simp] theorem enc_nil : enc ([] : List A) = [] := rfl

@[simp] theorem enc_cons (a : A) (u : List A) : enc (a :: u) = encSym a ++ enc u := by
  simp [enc]

@[simp] theorem enc_append (u v : List A) : enc (u ++ v) = enc u ++ enc v := by
  simp [enc]

theorem length_encSym (a : A) : (encSym a).length = codeA a + 1 := by
  simp [encSym]

theorem length_le_length_enc (u : List A) : u.length ≤ (enc u).length := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [enc_cons, List.length_append, length_encSym, List.length_cons]
    omega

theorem length_enc_le (u : List A) : (enc u).length ≤ (Fintype.card A + 1) * u.length := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [enc_cons, List.length_append, length_encSym, List.length_cons]
    have := codeA_lt a
    nlinarith

/-- Decoding an index into a symbol. -/
noncomputable def decA [Inhabited A] (c : ℕ) : A :=
  if h : c < Fintype.card A then (Fintype.equivFin A).symm ⟨c, h⟩ else default

theorem decA_codeA [Inhabited A] (a : A) : decA (codeA a) = a := by
  simp [decA, codeA]

variable {σ : Type}

/-! ### State indices -/

variable [Fintype σ] [DecidableEq σ]

/-- The index of a state, `0` for the initial state `s₀`. -/
noncomputable def codeS (s₀ s : σ) : ℕ := if s = s₀ then 0 else (Fintype.equivFin σ s : ℕ) + 1

theorem codeS_lt (s₀ s : σ) : codeS s₀ s < Fintype.card σ + 1 := by
  unfold codeS
  split
  · omega
  · have := (Fintype.equivFin σ s).2
    omega

theorem codeS_self (s₀ : σ) : codeS s₀ s₀ = 0 := by simp [codeS]

theorem codeS_injective (s₀ : σ) : Function.Injective (codeS s₀) := by
  intro s t h
  unfold codeS at h
  by_cases hs : s = s₀ <;> by_cases ht : t = s₀
  · rw [hs, ht]
  · simp [hs, ht] at h
  · simp [hs, ht] at h
  · simp only [hs, ht, ite_false, add_left_inj] at h
    exact (Fintype.equivFin σ).injective (Fin.ext h)

/-- Decoding a state index. -/
noncomputable def decS (s₀ : σ) (k : ℕ) : σ :=
  if h : ∃ s, codeS s₀ s = k then h.choose else s₀

theorem decS_codeS (s₀ s : σ) : decS s₀ (codeS s₀ s) = s := by
  have h : ∃ t, codeS s₀ t = codeS s₀ s := ⟨s, rfl⟩
  simp only [decS, h, dite_eq_left]
  exact codeS_injective s₀ h.choose_spec

/-! ### The bit-level transducer -/

/-- The width of a block index, `|A| + 1`. -/
abbrev wd (A : Type) [Fintype A] : ℕ := Fintype.card A + 1

variable [Inhabited A] in
/-- The transition of the bit-level transducer: the state is `codeS s * wd A + c`, `c` counting
the ones of the current block. -/
noncomputable def bitδ (δ : σ → A → σ) (s₀ : σ) : ℕ → Bool → ℕ := fun t b =>
  if b then codeS s₀ (decS s₀ (t / wd A)) * wd A + min (t % wd A + 1) (Fintype.card A)
  else codeS s₀ (δ (decS s₀ (t / wd A)) (decA (t % wd A))) * wd A

variable [Inhabited A] in
/-- The output of the bit-level transducer. -/
noncomputable def bitOut (out : σ → A → List A) (s₀ : σ) :
    ℕ → Bool → Word := fun t b =>
  if b then [] else enc (out (decS s₀ (t / wd A)) (decA (t % wd A)))

/-- The number of states of the bit-level transducer. -/
abbrev nst (σ A : Type) [Fintype σ] [Fintype A] : ℕ := (Fintype.card σ + 1) * wd A

omit [DecidableEq σ] in
theorem nst_pos : 0 < nst σ A := by positivity


theorem codeS_mul_add_lt (s₀ s : σ) {c : ℕ} (hc : c < wd A) :
    codeS s₀ s * wd A + c < nst σ A := by
  have h := codeS_lt s₀ s
  unfold nst
  nlinarith

variable [Inhabited A] in
theorem bitδ_lt (δ : σ → A → σ) (s₀ : σ) (t : ℕ) (b : Bool) : bitδ δ s₀ t b < nst σ A := by
  unfold bitδ
  split
  · exact codeS_mul_add_lt s₀ _ (by unfold wd; omega)
  · simpa using codeS_mul_add_lt (A := A) s₀ (δ (decS s₀ (t / wd A)) (decA (t % wd A)))
      (c := 0) (by unfold wd; omega)


theorem div_wd (s₀ s : σ) {c : ℕ} (hc : c < wd A) : (codeS s₀ s * wd A + c) / wd A = codeS s₀ s := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by unfold wd; omega), Nat.div_eq_of_lt hc,
    Nat.zero_add]


theorem mod_wd (s₀ s : σ) {c : ℕ} (hc : c < wd A) : (codeS s₀ s * wd A + c) % wd A = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

variable [Inhabited A]

theorem lrun_append' (δ : ℕ → Bool → ℕ) (out : ℕ → Bool → Word) (s : ℕ) (x y : Word) :
    lrun δ out s (x ++ y) = lrun δ out s x ++ lrun δ out (lst δ s x) y := by
  induction x generalizing s with
  | nil => rfl
  | cons b x ih =>
    rw [List.cons_append, lrun, lrun, ih, List.append_assoc]
    rfl

theorem lst_append' (δ : ℕ → Bool → ℕ) (s : ℕ) (x y : Word) :
    lst δ s (x ++ y) = lst δ (lst δ s x) y := by
  induction x generalizing s with
  | nil => rfl
  | cons b x ih => exact ih (δ s b)

theorem rst_reverse (δ : ℕ → Bool → ℕ) (s : ℕ) (x : Word) : rst δ s x.reverse = lst δ s x := by
  induction x generalizing s with
  | nil => rfl
  | cons b x ih => rw [List.reverse_cons, rst_append_singleton, ih]; rfl

theorem ones_step (δ : σ → A → σ) (out : σ → A → List A) (s₀ s : σ) :
    ∀ (i c : ℕ), c + i ≤ Fintype.card A →
      lst (bitδ δ s₀) (codeS s₀ s * wd A + c) (List.replicate i true) =
        codeS s₀ s * wd A + (c + i) ∧
      lrun (bitδ δ s₀) (bitOut out s₀) (codeS s₀ s * wd A + c) (List.replicate i true) = []
  | 0, c, _ => by simp [lst, lrun]
  | i + 1, c, h => by
    have hc : c < wd A := by unfold wd; omega
    have hstep : bitδ δ s₀ (codeS s₀ s * wd A + c) true = codeS s₀ s * wd A + (c + 1) := by
      simp only [bitδ, ite_true, div_wd s₀ s hc, mod_wd s₀ s hc, decS_codeS]
      congr 1
      omega
    have hout : bitOut out s₀ (codeS s₀ s * wd A + c) true = [] := by simp [bitOut]
    obtain ⟨h1, h2⟩ := ones_step δ out s₀ s i (c + 1) (by omega)
    rw [List.replicate_succ, lst, lrun, hstep, hout, h1, h2]
    exact ⟨by congr 1; omega, rfl⟩

theorem sym_step (δ : σ → A → σ) (out : σ → A → List A) (s₀ s : σ) (a : A) :
    lst (bitδ δ s₀) (codeS s₀ s * wd A) (encSym a) = codeS s₀ (δ s a) * wd A ∧
    lrun (bitδ δ s₀) (bitOut out s₀) (codeS s₀ s * wd A) (encSym a) = enc (out s a) := by
  have h := ones_step δ out s₀ s (codeA a) 0 (by have := codeA_lt a; omega)
  simp only [Nat.add_zero, Nat.zero_add] at h
  have hc : codeA a < wd A := by have := codeA_lt a; unfold wd; omega
  have hδ : bitδ δ s₀ (codeS s₀ s * wd A + codeA a) false = codeS s₀ (δ s a) * wd A := by
    simp only [bitδ, Bool.false_eq_true, ite_false, div_wd s₀ s hc, mod_wd s₀ s hc, decS_codeS,
      decA_codeA]
  have hout : bitOut out s₀ (codeS s₀ s * wd A + codeA a) false = enc (out s a) := by
    simp only [bitOut, Bool.false_eq_true, ite_false, div_wd s₀ s hc, mod_wd s₀ s hc, decS_codeS,
      decA_codeA]
  constructor
  · rw [encSym, lst_append', h.1, lst, lst, hδ]
  · rw [encSym, lrun_append', h.2, h.1, lrun, lrun, hout]
    simp

theorem enc_step (δ : σ → A → σ) (out : σ → A → List A) (s₀ : σ) (u : List A) :
    ∀ s : σ,
      lst (bitδ δ s₀) (codeS s₀ s * wd A) (enc u) = codeS s₀ (mlst δ s u) * wd A ∧
      lrun (bitδ δ s₀) (bitOut out s₀) (codeS s₀ s * wd A) (enc u) = enc (mrun δ out s u) := by
  induction u with
  | nil => intro s; simp [lst, lrun]
  | cons a u ih =>
    intro s
    obtain ⟨h1, h2⟩ := sym_step δ out s₀ s a
    obtain ⟨h3, h4⟩ := ih (δ s a)
    rw [enc_cons, lst_append', lrun_append', h1, h2, h3, h4]
    exact ⟨rfl, by rw [mrun_cons, enc_append]⟩

/-! ### The Cobham terms -/

/-- A bound on the output blocks. -/
noncomputable def outBound (out : σ → A → List A) : ℕ :=
  Finset.univ.sup fun sa : σ × A => (enc (out sa.1 sa.2)).length

theorem length_bitOut_le (out : σ → A → List A) (s₀ : σ) (t : ℕ) (b : Bool) :
    (bitOut out s₀ t b).length ≤ outBound out := by
  unfold bitOut
  split
  · simp
  · exact Finset.le_sup (f := fun sa : σ × A => (enc (out sa.1 sa.2)).length)
      (Finset.mem_univ (decS s₀ (t / wd A), decA (t % wd A)))

/-- **The Cobham term of a transducer over `A`.** -/
noncomputable def runTerm (δ : σ → A → σ) (out : σ → A → List A) (s₀ : σ) : Cob :=
  .comp (lrunTerm (nst σ A) (bitδ δ s₀) (fun t b => Cob.pre (bitOut out s₀ t b) .empty)
    (outBound out)) [.proj 0, .empty]

theorem eval_runTerm (δ : σ → A → σ) (out : σ → A → List A) (s₀ : σ) (u : List A)
    (rest : List Word) :
    (runTerm δ out s₀).eval (enc u :: rest) = enc (mrun δ out s₀ u) := by
  have hK : ∀ t b, ((Cob.pre (bitOut out s₀ t b) .empty).eval [[]]).length ≤
      outBound out + ([] : Word).length := by
    intro t b
    simpa using length_bitOut_le out s₀ t b
  have h := eval_lrunTerm (m := nst σ A) (K := outBound out) nst_pos (bitδ_lt δ s₀)
    (fun t b => Cob.pre (bitOut out s₀ t b) .empty) [] hK (enc u)
  simp only [Cob.eval_pre, Cob.eval_empty, List.append_nil] at h
  have h0 := (enc_step δ out s₀ u s₀).2
  rw [codeS_self, Nat.zero_mul] at h0
  rw [runTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    Cob.eval_empty]
  rw [h, h0]

/-- The Cobham term computing, in unary, the bit-level index of the final state. -/
noncomputable def stateTerm (δ : σ → A → σ) (s₀ : σ) : Cob :=
  .comp (fstStTerm (nst σ A) (bitδ δ s₀)) [.comp Cob.revTerm [.proj 0]]

theorem eval_stateTerm (δ : σ → A → σ) (s₀ : σ) (u : List A) (rest : List Word) :
    (stateTerm δ s₀).eval (enc u :: rest) =
      List.replicate (codeS s₀ (mlst δ s₀ u) * wd A) true := by
  rw [stateTerm]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
    Cob.eval_revTerm]
  rw [eval_fstStTerm nst_pos (bitδ_lt δ s₀), rst_reverse]
  have h0 := (enc_step δ (fun _ _ => []) s₀ u s₀).1
  rw [codeS_self, Nat.zero_mul] at h0
  rw [h0]

/-- **Choosing a term by the final state of a transducer.** -/
noncomputable def selectTerm (δ : σ → A → σ) (s₀ : σ) (F : σ → Cob) : Cob :=
  Cob.tableSel ((List.range (nst σ A)).map fun t => F (decS s₀ (t / wd A))) (stateTerm δ s₀)

theorem eval_selectTerm (δ : σ → A → σ) (s₀ : σ) (F : σ → Cob) (u : List A)
    (rest : List Word) :
    (selectTerm δ s₀ F).eval (enc u :: rest) = (F (mlst δ s₀ u)).eval (enc u :: rest) := by
  rw [selectTerm, Cob.eval_tableSel _ _ _ _ (eval_stateTerm δ s₀ u rest)]
  have hlt : codeS s₀ (mlst δ s₀ u) * wd A < nst σ A := by
    have := codeS_mul_add_lt (A := A) s₀ (mlst δ s₀ u) (c := 0) (Nat.succ_pos _)
    rwa [Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  have hd : codeS s₀ (mlst δ s₀ u) * wd A / wd A = codeS s₀ (mlst δ s₀ u) := by
    have := div_wd (A := A) s₀ (mlst δ s₀ u) (c := 0) (Nat.succ_pos _)
    rwa [Nat.add_zero] at this
  rw [hd, decS_codeS]

end Macro

end Complexity
