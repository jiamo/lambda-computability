/-
**Polynomial-time multi-tape machines decide languages in Cobham's `P`.**

For upstream's `FiniteMultiTapeMachine` (`Start/DepthThreeModel.lean`), a language decided within
`p(n)` steps, `p n ≤ a (n + 1)^k`, is in `Complexity.InP`.  Configurations are encoded as words
over the finite alphabet `Sym M` (`Start/MultiTapeMacro.lean`) and then in binary
(`Macro.enc`).  One machine step is the Cobham term `stepTerm M`: a left-to-right transducer reads
the state and the head symbols, and the matching edit transducer of the transition table rewrites
the word (`Start/CobhamMacro.lean`).  The decider iterates `stepTerm M` exactly `a (n + 1)^k` times
with `Cob.iterT` (`Start/CobhamTimeIter.lean`), starting from the encoded initial configuration,
and reads the accepting bit of the final state.  Once the machine has halted the step term is the
identity, so iterating more often than the running time is harmless.

Main definitions:

* `Complexity.MultiTapeCobham.stepTerm` — one machine step as a Cobham term;
* `Complexity.MultiTapeCobham.initTerm` — the encoded initial configuration;
* `Complexity.MultiTapeCobham.decider` — the decider, iterating `a (n + 1)^k` steps.

Main results:

* `Complexity.MultiTapeCobham.eval_stepTerm` — `stepTerm` maps a word of `c` to a word of the
  next configuration (or of `c` itself, if `c` has halted), at most `2 |K|` symbols longer;
* `Complexity.MultiTapeCobham.eval_decider` — the decider outputs `[true]` or `[]` according to
  the accepting bit of the halting configuration;
* `Complexity.MultiTapeCobham.inP_of_multiTapeHaltsIn` — **the language is in `InP`**.
-/

import Start.CobhamMacro
import Start.MultiTapeMacro
import Start.CobhamTimeIter

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace MultiTapeCobham

open DepthThreeLowerBound Macro Classical

variable (M : FiniteMultiTapeMachine)

/-! ### One step -/

/-- The step of the machine, staying put on halted configurations. -/
def stepOr (c : M.Cfg) : M.Cfg := (M.step c).getD c

/-- The term applied once the state and the heads are known. -/
noncomputable def actTerm (s : InfoSt M) : Cob :=
  match s.1 with
  | none => .proj 0
  | some q =>
    match M.code q s.2.2.2.2 with
    | none => .proj 0
    | some out => runTerm (edδ M out.2.2) (edOut M out.1 out.2.1 out.2.2) (ed0 M)

/-- **One machine step as a Cobham term.** -/
noncomputable def stepTerm : Cob := selectTerm (infoδ M) (info0 M) (actTerm M)

variable {M}

theorem eval_stepTerm {u : List (Sym M)} {c : M.Cfg} (h : Rep M u c) (rest : List Word) :
    ∃ u', (stepTerm M).eval (enc u :: rest) = enc u' ∧ Rep M u' (stepOr M c) ∧
      u'.length ≤ u.length + 2 * Fintype.card M.K := by
  obtain ⟨h1, h2⟩ := rep_heads h
  rw [stepTerm, eval_selectTerm, actTerm, h1, h2]
  simp only
  have hstep : M.step c = (M.code c.q (fun k => (c.tapes k).head)).map
      (fun out => multiTapeUpdate c out.1 out.2.1 out.2.2) := rfl
  cases hc : M.code c.q (fun k => (c.tapes k).head) with
  | none =>
    refine ⟨u, by simp, ?_, by omega⟩
    have : stepOr M c = c := by simp [stepOr, hstep, hc]
    rw [this]
    exact h
  | some out =>
    obtain ⟨q', w, mv⟩ := out
    refine ⟨mrun (edδ M mv) (edOut M q' w mv) (ed0 M) u, eval_runTerm _ _ _ u rest, ?_,
      length_update_le h q' w mv⟩
    have : stepOr M c = multiTapeUpdate c q' w mv := by simp [stepOr, hstep, hc]
    rw [this]
    exact rep_update h q' w mv

variable (M)

/-! ### Acceptance -/

/-- The term reading the accepting bit of the encoded state. -/
noncomputable def accTerm : Cob :=
  selectTerm (infoδ M) (info0 M) fun s =>
    match s.1 with
    | some q => if M.accept q then Cob.pre [true] .empty else .empty
    | none => .empty

variable {M}

theorem eval_accTerm {u : List (Sym M)} {c : M.Cfg} (h : Rep M u c) (rest : List Word) :
    (accTerm M).eval (enc u :: rest) = if M.accept c.q then [true] else [] := by
  rw [accTerm, eval_selectTerm, (rep_heads h).1]
  simp only
  split <;> simp

/-! ### The initial configuration -/

variable (M)

/-- The word of the initial configuration on the input `x`. -/
noncomputable def initWord (x : List Bool) : List (Sym M) :=
  word M M.initialState (fun _ => [])
    (fun k => if k = M.inputTape then x.map M.inputSymbol else [])

variable {M}

theorem rep_initWord (x : List Bool) : Rep M (initWord M x) (M.init x) := by
  refine ⟨fun _ => [], fun k => if k = M.inputTape then x.map M.inputSymbol else [], ?_, rfl⟩
  intro k
  change (if k = M.inputTape then Turing.Tape.mk₁ (x.map M.inputSymbol)
    else Turing.Tape.mk₁ []) = _
  by_cases hk : k = M.inputTape <;>
    simp [hk, tapeOf, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk']

theorem segs_congr (l : List M.K) {Ls Rs Ls' Rs' : M.K → List M.Γ}
    (h : ∀ k ∈ l, Ls k = Ls' k ∧ Rs k = Rs' k) : segs M l Ls Rs = segs M l Ls' Rs' := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [segs, List.flatMap_cons] at ih ⊢
    rw [(h k (by simp)).1, (h k (by simp)).2, ih (fun k' hk' => h k' (by simp [hk']))]

variable (M) in
/-- The input, letter by letter. -/
noncomputable def inTerm : Cob :=
  lrunTerm 1 (fun _ _ => 0) (fun _ b => Cob.pre (enc [sym M (M.inputSymbol b)]) .empty)
    ((enc [sym M (M.inputSymbol true)]).length + (enc [sym M (M.inputSymbol false)]).length)

theorem eval_inTerm (x : List Bool) :
    (inTerm M).eval [x, []] = enc ((x.map M.inputSymbol).map (sym M)) := by
  rw [inTerm, eval_lrunTerm (by omega) (fun _ _ => by omega)]
  · induction x with
    | nil => rfl
    | cons b x ih =>
      rw [lrun]
      simp only [Cob.eval_pre, Cob.eval_empty, List.append_nil] at ih ⊢
      rw [ih]
      simp
  · intro _ b
    cases b <;> simp

variable (M)

/-- The split of the tape list at the input tape. -/
noncomputable def ksPre : List M.K := (List.append_of_mem (mem_ks M M.inputTape)).choose

/-- The tapes after the input tape. -/
noncomputable def ksPost : List M.K := (List.append_of_mem (mem_ks M M.inputTape)).choose_spec.choose

theorem ks_split : ks M = ksPre M ++ M.inputTape :: ksPost M :=
  (List.append_of_mem (mem_ks M M.inputTape)).choose_spec.choose_spec

/-- The encoded part of the initial word before the input. -/
noncomputable def initPre : Word :=
  enc (stSym M M.initialState :: (segs M (ksPre M) (fun _ => []) (fun _ => []) ++
    [sepA M M.inputTape, sepA M M.inputTape]))

/-- The encoded part of the initial word after the input. -/
noncomputable def initPost : Word := enc (segs M (ksPost M) (fun _ => []) (fun _ => []))

/-- **The encoded initial configuration, as a Cobham term.** -/
noncomputable def initTerm : Cob :=
  Cob.pre (initPre M) (.comp Cob.concat [.comp (inTerm M) [.proj 0, .empty],
    Cob.pre (initPost M) .empty])

variable {M}

theorem enc_initWord (x : List Bool) :
    enc (initWord M x) = initPre M ++ (enc ((x.map M.inputSymbol).map (sym M)) ++ initPost M) := by
  have hnd := ks_nodup M
  rw [ks_split] at hnd
  have hnd' := List.nodup_append.mp hnd
  have hpre : ∀ k ∈ ksPre M, k ≠ M.inputTape := by
    intro k hk he
    exact hnd'.2.2 k hk M.inputTape (by simp) he
  have hpost : ∀ k ∈ ksPost M, k ≠ M.inputTape := by
    intro k hk he
    exact (List.nodup_cons.mp hnd'.2.1).1 (he ▸ hk)
  unfold initWord word initPre initPost
  rw [ks_split]
  have hs : segs M (ksPre M ++ M.inputTape :: ksPost M) (fun _ => [])
      (fun k => if k = M.inputTape then x.map M.inputSymbol else []) =
      segs M (ksPre M) (fun _ => []) (fun _ => []) ++
        (seg M M.inputTape [] (x.map M.inputSymbol) ++
          segs M (ksPost M) (fun _ => []) (fun _ => [])) := by
    simp only [segs, List.flatMap_append, List.flatMap_cons]
    congr 1
    · exact segs_congr _ (fun k hk => ⟨rfl, by simp [hpre k hk]⟩)
    · congr 1
      exact segs_congr _ (fun k hk => ⟨rfl, by simp [hpost k hk]⟩)
  rw [hs]
  simp [seg, enc_append, enc_cons, List.append_assoc]

theorem eval_initTerm (x : List Bool) (rest : List Word) :
    (initTerm M).eval (x :: rest) = enc (initWord M x) := by
  rw [enc_initWord, initTerm]
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, Cob.eval_empty, List.append_nil, Cob.eval_concat]
  rw [eval_inTerm]

theorem length_enc_initWord (x : List Bool) :
    (enc (initWord M x)).length ≤
      (initPre M).length + (initPost M).length + (Fintype.card (Sym M) + 1) * x.length := by
  rw [enc_initWord]
  have := length_enc_le ((x.map M.inputSymbol).map (sym M))
  simp only [List.length_map] at this
  simp only [List.length_append]
  omega

/-! ### Polynomial counters -/

/-- The unary word `1^{(|x| + 1)^k}`. -/
def pw : ℕ → Cob
  | 0 => Cob.pre [true] .empty
  | k + 1 => .comp .smash [pw k, Cob.pre [true] (.proj 0)]

theorem eval_pw (k : ℕ) (x : Word) (rest : List Word) :
    (pw k).eval (x :: rest) = List.replicate ((x.length + 1) ^ k) true := by
  induction k with
  | zero => simp [pw]
  | succ k ih =>
    rw [pw]
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, List.getD_cons_zero,
      List.getD_cons_succ, ih, Cob.eval_pre, Cob.eval_proj, List.length_replicate]
    rw [pow_succ]
    simp

/-- The unary word `1^{a (|x| + 1)^k}`. -/
def polyT (a k : ℕ) : Cob := .comp .smash [Cob.pre (List.replicate a true) .empty, pw k]

theorem eval_polyT (a k : ℕ) (x : Word) (rest : List Word) :
    (polyT a k).eval (x :: rest) = List.replicate (a * (x.length + 1) ^ k) true := by
  rw [polyT]
  simp [eval_pw]

/-! ### The decider -/

variable (M)

/-- The constant of the length bound of the iteration. -/
noncomputable def bndConst (a : ℕ) : ℕ :=
  (Fintype.card (Sym M) + 1) *
    ((initPre M).length + (initPost M).length + (Fintype.card (Sym M) + 1) +
      2 * Fintype.card M.K * a)

/-- **The decider**: `a (|x| + 1)^k` steps from the initial configuration, then the accepting bit
of the state. -/
noncomputable def decider (a k : ℕ) : Cob :=
  .comp (accTerm M)
    [.comp (Cob.iterT (initTerm M) (stepTerm M) (polyT (bndConst M a) (k + 1)) 1)
      [polyT a k, .proj 0]]

variable {M}

theorem iterate_stepTerm (x : List Bool) :
    ∀ j : ℕ, ∃ u, (fun s => (stepTerm M).eval (s :: [x]))^[j] (enc (initWord M x)) = enc u ∧
      Rep M u ((stepOr M)^[j] (M.init x)) ∧
      u.length ≤ (initWord M x).length + 2 * Fintype.card M.K * j
  | 0 => ⟨initWord M x, rfl, rep_initWord x, by omega⟩
  | j + 1 => by
    obtain ⟨u, hu, hr, hl⟩ := iterate_stepTerm x j
    obtain ⟨u', hu', hr', hl'⟩ := eval_stepTerm hr [x]
    refine ⟨u', ?_, ?_, ?_⟩
    · rw [Function.iterate_succ_apply', hu, hu']
    · rw [Function.iterate_succ_apply']
      exact hr'
    · rw [Nat.mul_succ]
      omega

theorem stepOr_iterate_of_runSteps (c₀ : M.Cfg) :
    ∀ (j : ℕ) (c : M.Cfg), runSteps M.step j (some c₀) = some c → (stepOr M)^[j] c₀ = c
  | 0, c, h => by simpa [runSteps] using h
  | j + 1, c, h => by
    have h' : (runSteps M.step j (some c₀)).bind M.step = some c := by
      rw [runSteps, Function.iterate_succ_apply'] at h
      exact h
    obtain ⟨c', hc', hstep⟩ := Option.bind_eq_some_iff.mp h'
    rw [Function.iterate_succ_apply', stepOr_iterate_of_runSteps c₀ j c' hc']
    simp [stepOr, hstep]

/-- **What the decider computes**: if the machine halts on `x` within `a (|x| + 1)^k` steps in a
configuration with accepting bit `b`, the decider outputs `[true]` when `b` holds and `[]`
otherwise. -/
theorem eval_decider (a k : ℕ) (x : List Bool) (t : ℕ) (ht : t ≤ a * (x.length + 1) ^ k)
    (c : M.Cfg) (hrun : runSteps M.step t (some (M.init x)) = some c) (hhalt : M.step c = none) :
    (decider M a k).eval [x] = if M.accept c.q then [true] else [] := by
  set T := a * (x.length + 1) ^ k with hT
  have hfix : stepOr M c = c := by simp [stepOr, hhalt]
  have hcT : (stepOr M)^[T] (M.init x) = c := by
    have h1 := stepOr_iterate_of_runSteps (M.init x) t c hrun
    have : T = (T - t) + t := by omega
    rw [this, Function.iterate_add_apply, h1, Function.iterate_fixed hfix]
  have hbound : ∀ j, 1 ≤ j → j ≤ (List.replicate T true).length →
      ((fun s => (stepTerm M).eval (s :: [x]))^[j] ((initTerm M).eval [x])).length ≤
        ((polyT (bndConst M a) (k + 1)).eval [x]).length := by
    intro j _ hj
    rw [List.length_replicate] at hj
    obtain ⟨u, hu, -, hl⟩ := iterate_stepTerm x j
    rw [eval_initTerm, hu, eval_polyT, List.length_replicate]
    have h1 := length_enc_le u
    have h2 := length_le_length_enc (initWord M x)
    have h3 := length_enc_initWord (M := M) x
    set n := x.length
    have hp1 : 1 ≤ (n + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    have hp2 : n ≤ (n + 1) ^ (k + 1) := by
      calc n ≤ n + 1 := by omega
        _ = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hp3 : (n + 1) ^ k ≤ (n + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have hjT : 2 * Fintype.card M.K * j ≤ 2 * Fintype.card M.K * a * (n + 1) ^ (k + 1) := by
      calc 2 * Fintype.card M.K * j ≤ 2 * Fintype.card M.K * (a * (n + 1) ^ k) :=
            Nat.mul_le_mul_left _ hj
        _ ≤ 2 * Fintype.card M.K * (a * (n + 1) ^ (k + 1)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hp3)
        _ = 2 * Fintype.card M.K * a * (n + 1) ^ (k + 1) := by ring
    set C := Fintype.card (Sym M) + 1
    set P := (initPre M).length + (initPost M).length
    have hu' : u.length ≤ (P + C + 2 * Fintype.card M.K * a) * (n + 1) ^ (k + 1) := by
      have e1 : P ≤ P * (n + 1) ^ (k + 1) := Nat.le_mul_of_pos_right _ hp1
      have e2 : C * n ≤ C * (n + 1) ^ (k + 1) := Nat.mul_le_mul_left _ hp2
      calc u.length ≤ (initWord M x).length + 2 * Fintype.card M.K * j := hl
        _ ≤ P + C * n + 2 * Fintype.card M.K * a * (n + 1) ^ (k + 1) := by omega
        _ ≤ P * (n + 1) ^ (k + 1) + C * (n + 1) ^ (k + 1) +
            2 * Fintype.card M.K * a * (n + 1) ^ (k + 1) := by omega
        _ = (P + C + 2 * Fintype.card M.K * a) * (n + 1) ^ (k + 1) := by ring
    calc (enc u).length ≤ C * u.length := h1
      _ ≤ C * ((P + C + 2 * Fintype.card M.K * a) * (n + 1) ^ (k + 1)) :=
          Nat.mul_le_mul_left _ hu'
      _ = bndConst M a * (n + 1) ^ (k + 1) := by
          simp only [bndConst, C, P]
          ring
  have hiter := Cob.eval_iterT (initTerm M) (stepTerm M) (polyT (bndConst M a) (k + 1)) [x]
    (List.replicate T true) hbound
  rw [decider]
  simp only [Cob.eval_comp, List.map_cons, List.map_nil, eval_polyT, Cob.eval_proj,
    List.getD_cons_zero]
  rw [show (Cob.iterT (initTerm M) (stepTerm M) (polyT (bndConst M a) (k + 1)) 1).eval
    [List.replicate T true, x] = _ from hiter, List.length_replicate, eval_initTerm]
  obtain ⟨u, hu, hr, -⟩ := iterate_stepTerm x T
  rw [hu, eval_accTerm hr [], hcT]

/-- **Polynomial-time multi-tape machines decide languages in Cobham's `P`.**  If on every input
`x` the machine halts within `p |x|` steps, `p` polynomially bounded, with accepting bit `b`
such that `L x ↔ b = true`, then `L` is in `InP`; the decider iterates the step term
`a (|x| + 1)^k` times, where `p n ≤ a (n + 1)^k`. -/
theorem inP_of_multiTapeHaltsIn (M : FiniteMultiTapeMachine) (L : Language) (p : ℕ → ℕ)
    (hp : PolyBound p)
    (hM : ∀ x, ∃ b, MultiTapeHaltsIn M x b (p x.length) ∧ (L x ↔ b = true)) : InP L := by
  obtain ⟨a, k, hak⟩ := hp
  refine ⟨decider M a k, fun x => ?_⟩
  obtain ⟨b, ⟨t, ht, c, hrun, hhalt, hacc⟩, hL⟩ := hM x
  rw [eval_decider a k x t (ht.trans (hak _)) c hrun hhalt, hacc, hL]
  cases b <;> simp

end MultiTapeCobham

end Complexity
