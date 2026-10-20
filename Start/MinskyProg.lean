/-
**Structured counter-machine programs and their compilation to `KM`** — task
`M25-KCM-UNIVERSAL` (round 10, part B2), on top of `Start/MinskyPair.lean`.

The frame convention of part B is fixed here once and for all, for *structured* programs:

* `Minsky.Prog` — `inc i`, `dec i` (saturating), `seq p q`, and `loop i p`
  (`while r i ≠ 0 do (r i -= 1; p)`);
* `Minsky.Prog.code p o e` — the block of `p.len` instructions placed at offset `o`, with exit
  label `e` (every jump of the block goes into the block or to `e`);
* `Minsky.Prog.Exec p r r'` — the big-step semantics, deterministic (`Exec.det`);
* `Minsky.Prog.Exec.run` — **completeness**: an execution is a run of the block from its entry
  to its exit, in any program containing the block;
* `Minsky.Prog.exec_of_stepsIn` — **soundness**: a run that starts at the entry, stays in the
  block and then leaves it, leaves it at the exit, with the final registers of an execution;
* `Minsky.Prog.halts_iff_exec` — the machine `p.code 0 p.len` halts from `r` exactly when `p`
  has an execution from `r`.
-/

import Start.MinskyPair

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

open Function Macro

/-- **Structured counter programs.** -/
inductive Prog where
  | inc : ℕ → Prog
  | dec : ℕ → Prog
  | seq : Prog → Prog → Prog
  /-- `while r i ≠ 0 do (r i -= 1; p)`. -/
  | loop : ℕ → Prog → Prog

namespace Macro

theorem Contains.left {M : KM} {o : ℕ} {L₁ L₂ : List KInstr} (h : Contains M o (L₁ ++ L₂)) :
    Contains M o L₁ := by
  intro n hn
  have := h n (by simp; omega)
  rw [this, List.getElem_append_left hn]

theorem Contains.right {M : KM} {o : ℕ} {L₁ L₂ : List KInstr} (h : Contains M o (L₁ ++ L₂)) :
    Contains M (o + L₁.length) L₂ := by
  intro n hn
  have := h (L₁.length + n) (by simp; omega)
  rw [Nat.add_assoc, this, List.getElem_append_right (by omega)]
  simp

theorem Contains.head {M : KM} {o : ℕ} {x : KInstr} {L : List KInstr}
    (h : Contains M o (x :: L)) : M[o]? = some x := by
  have := h 0 (by simp)
  simpa using this

theorem Contains.tail {M : KM} {o : ℕ} {x : KInstr} {L : List KInstr}
    (h : Contains M o (x :: L)) : Contains M (o + 1) L := by
  have := Contains.right (L₁ := [x]) (L₂ := L) h
  simpa using this

end Macro

namespace Prog

/-- The number of instructions of a program. -/
def len : Prog → ℕ
  | inc _ => 1
  | dec _ => 1
  | seq p q => p.len + q.len
  | loop _ p => p.len + 1

/-- **The code of a program** at offset `o` with exit label `e`. -/
def code : Prog → ℕ → ℕ → List KInstr
  | inc i, _, e => [.inc i e]
  | dec i, _, e => [.test i e e]
  | seq p q, o, e => p.code o (o + p.len) ++ q.code (o + p.len) e
  | loop i p, o, e => .test i e (o + 1) :: p.code (o + 1) o

theorem code_length : ∀ (p : Prog) (o e : ℕ), (p.code o e).length = p.len
  | inc _, _, _ => rfl
  | dec _, _, _ => rfl
  | seq p q, o, e => by simp [code, len, code_length p, code_length q]
  | loop _ p, o, e => by simp [code, len, code_length p]

/-- **The big-step semantics.** -/
inductive Exec : Prog → (ℕ → ℕ) → (ℕ → ℕ) → Prop
  | inc {i : ℕ} {r : ℕ → ℕ} : Exec (.inc i) r (update r i (r i + 1))
  | dec {i : ℕ} {r : ℕ → ℕ} : Exec (.dec i) r (update r i (r i - 1))
  | seq {p q : Prog} {r r₁ r₂ : ℕ → ℕ} : Exec p r r₁ → Exec q r₁ r₂ → Exec (.seq p q) r r₂
  | loop0 {i : ℕ} {p : Prog} {r : ℕ → ℕ} : r i = 0 → Exec (.loop i p) r r
  | loopS {i : ℕ} {p : Prog} {r r₁ r₂ : ℕ → ℕ} {v : ℕ} : r i = v + 1 →
      Exec p (update r i v) r₁ → Exec (.loop i p) r₁ r₂ → Exec (.loop i p) r r₂

/-- **Determinism.** -/
theorem Exec.det {p : Prog} {r r₁ r₂ : ℕ → ℕ} (h₁ : Exec p r r₁) (h₂ : Exec p r r₂) :
    r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | inc => cases h₂; rfl
  | dec => cases h₂; rfl
  | seq _ _ ih₁ ih₂ =>
      cases h₂ with
      | seq h h' => exact ih₂ (ih₁ h ▸ h')
  | loop0 h0 =>
      cases h₂ with
      | loop0 => rfl
      | loopS hv => rw [h0] at hv; cases hv
  | loopS hv _ _ ih₁ ih₂ =>
      cases h₂ with
      | loop0 h0 => rw [h0] at hv; cases hv
      | loopS hv' h h' =>
          rw [hv] at hv'
          cases hv'
          exact ih₂ (ih₁ h ▸ h')

/-- **Completeness of the compilation**: an execution is a run from the entry to the exit. -/
theorem Exec.run {p : Prog} {r r' : ℕ → ℕ} (h : Exec p r r') :
    ∀ {M : KM} {o e : ℕ}, Contains M o (p.code o e) → Run M ⟨o, r⟩ ⟨e, r'⟩ := by
  induction h with
  | inc =>
      intro M o e hM
      exact .single (KM.Step.inc (Contains.head hM))
  | @dec i r =>
      intro M o e hM
      rcases hr : r i with _ | v
      · have : update r i (0 - 1) = r := by
          funext j; by_cases hj : j = i <;> simp [hj, hr]
        rw [this]
        exact .single (KM.Step.zero (Contains.head hM) hr)
      · rw [Nat.add_sub_cancel]
        exact .single (KM.Step.dec (Contains.head hM) hr)
  | @seq p q r r₁ r₂ _ _ ih₁ ih₂ =>
      intro M o e hM
      have h₁ := ih₁ (o := o) (e := o + p.len)
        (Contains.left (L₂ := q.code (o + p.len) e) hM)
      have h₂ := ih₂ (o := o + p.len) (e := e) (by
        have := Contains.right (L₁ := p.code o (o + p.len)) (L₂ := q.code (o + p.len) e) hM
        rwa [code_length] at this)
      exact h₁.trans h₂
  | loop0 h0 =>
      intro M o e hM
      exact .single (KM.Step.zero (Contains.head hM) h0)
  | loopS hv _ _ ih₁ ih₂ =>
      intro M o e hM
      have h₁ := ih₁ (Contains.tail hM)
      exact .head (KM.Step.dec (Contains.head hM) hv) (h₁.trans (ih₂ hM))

/-! ### Soundness: runs confined to a block -/

/-- Runs of `n` steps whose source configurations all lie in `[lo, hi)`. -/
inductive StepsIn (M : KM) (lo hi : ℕ) : ℕ → KConf → KConf → Prop
  | refl (c : KConf) : StepsIn M lo hi 0 c c
  | step {n : ℕ} {c c₁ c₂ : KConf} : lo ≤ c.pc → c.pc < hi → KM.Step M c c₁ →
      StepsIn M lo hi n c₁ c₂ → StepsIn M lo hi (n + 1) c c₂

/-- A confined run from outside the block is empty. -/
theorem StepsIn.outside {M : KM} {lo hi n : ℕ} {c c' : KConf} (h : StepsIn M lo hi n c c')
    (hc : ¬ (lo ≤ c.pc ∧ c.pc < hi)) : n = 0 ∧ c' = c := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step h₁ h₂ _ _ => exact absurd ⟨h₁, h₂⟩ hc

/-- **Splitting a confined run at its first exit from a sub-block.** -/
theorem StepsIn.split {M : KM} {lo hi lo' hi' : ℕ} :
    ∀ {n : ℕ} {c c' : KConf}, StepsIn M lo hi n c c' → ¬ (lo' ≤ c'.pc ∧ c'.pc < hi') →
      ∃ n₁ c₁, n₁ ≤ n ∧ StepsIn M lo' hi' n₁ c c₁ ∧ ¬ (lo' ≤ c₁.pc ∧ c₁.pc < hi') ∧
        StepsIn M lo hi (n - n₁) c₁ c' := by
  intro n c c' h hc'
  induction h with
  | refl c => exact ⟨0, c, le_refl _, .refl c, hc', .refl c⟩
  | @step n c c₁ c₂ h₁ h₂ hs hrest ih =>
      by_cases hin : lo' ≤ c.pc ∧ c.pc < hi'
      · obtain ⟨n₁, d, hn₁, hd, hdout, hrest'⟩ := ih hc'
        refine ⟨n₁ + 1, d, by omega, .step hin.1 hin.2 hs hd, hdout, ?_⟩
        have : n + 1 - (n₁ + 1) = n - n₁ := by omega
        rw [this]; exact hrest'
      · exact ⟨0, c, Nat.zero_le _, .refl c, hin, .step h₁ h₂ hs hrest⟩

/-- **Soundness of the compilation**: a run that starts at the entry of the block, stays in it
and then leaves it, leaves it at the exit, with the registers of an execution. -/
theorem exec_of_stepsIn : ∀ (p : Prog) {M : KM} {o e : ℕ}, Contains M o (p.code o e) →
    (e < o ∨ o + p.len ≤ e) → ∀ (n : ℕ) {r : ℕ → ℕ} {c : KConf},
      StepsIn M o (o + p.len) n ⟨o, r⟩ c → ¬ (o ≤ c.pc ∧ c.pc < o + p.len) →
      c.pc = e ∧ Exec p r c.r
  | inc i, M, o, e, hM, he, n, r, c, h, hc => by
      cases h with
      | refl => exact absurd ⟨le_refl o, by simp [len]⟩ hc
      | step _ _ hs hrest =>
          have hM0 := Contains.head hM
          cases hs with
          | inc hi =>
              rw [hM0] at hi; cases hi
              obtain ⟨-, rfl⟩ := hrest.outside (by simp [len]; omega)
              exact ⟨rfl, .inc⟩
          | zero hi _ => rw [hM0] at hi; cases hi
          | dec hi _ => rw [hM0] at hi; cases hi
  | dec i, M, o, e, hM, he, n, r, c, h, hc => by
      cases h with
      | refl => exact absurd ⟨le_refl o, by simp [len]⟩ hc
      | step _ _ hs hrest =>
          have hM0 := Contains.head hM
          cases hs with
          | inc hi => rw [hM0] at hi; cases hi
          | zero hi h0 =>
              rw [hM0] at hi; cases hi
              obtain ⟨-, rfl⟩ := hrest.outside (by simp [len]; omega)
              refine ⟨rfl, ?_⟩
              have h0' : r i = 0 := h0
              have : update r i (r i - 1) = r := by simp [h0']
              have hx := @Exec.dec i r
              rwa [this] at hx
          | @dec _ _ _ v hi hv =>
              rw [hM0] at hi; cases hi
              obtain ⟨-, rfl⟩ := hrest.outside (by simp [len]; omega)
              refine ⟨rfl, ?_⟩
              have : r i - 1 = v := by have : r i = v + 1 := hv; omega
              have hx := @Exec.dec i r
              rwa [this] at hx
  | seq p q, M, o, e, hM, he, n, r, c, h, hc => by
      have hMp : Contains M o (p.code o (o + p.len)) :=
        Contains.left (L₂ := q.code (o + p.len) e) hM
      have hMq : Contains M (o + p.len) (q.code (o + p.len) e) := by
        have := Contains.right (L₁ := p.code o (o + p.len)) (L₂ := q.code (o + p.len) e) hM
        rwa [code_length] at this
      simp only [len] at h hc he
      obtain ⟨n₁, c₁, -, h₁, hc₁, hrest⟩ :=
        h.split (lo' := o) (hi' := o + p.len) (by omega)
      obtain ⟨hpc₁, hex₁⟩ := exec_of_stepsIn p hMp (Or.inr (le_refl _)) n₁ h₁ hc₁
      obtain ⟨pc₁, r₁⟩ := c₁
      simp only at hpc₁ hex₁
      subst hpc₁
      obtain ⟨n₂, c₂, -, h₂, hc₂, hrest₂⟩ :=
        hrest.split (lo' := o + p.len) (hi' := o + p.len + q.len) (by omega)
      obtain ⟨hpc₂, hex₂⟩ := exec_of_stepsIn q hMq (by omega) n₂ h₂ hc₂
      obtain ⟨-, rfl⟩ := hrest₂.outside (by rw [hpc₂]; omega)
      exact ⟨hpc₂, .seq hex₁ hex₂⟩
  | loop i p, M, o, e, hM, he, n, r, c, h, hc => by
      induction n using Nat.strong_induction_on generalizing r with
      | _ n ihn =>
      simp only [len] at h hc he
      have hM0 := Contains.head hM
      have hMp : Contains M (o + 1) (p.code (o + 1) o) := Contains.tail hM
      cases h with
      | refl => exact absurd ⟨le_refl o, by show o < o + (p.len + 1); omega⟩ hc
      | @step m _ c₁ _ _ _ hs hrest =>
          cases hs with
          | inc hi => rw [hM0] at hi; cases hi
          | zero hi h0 =>
              rw [hM0] at hi; cases hi
              obtain ⟨-, rfl⟩ := hrest.outside (by simp; omega)
              exact ⟨rfl, .loop0 h0⟩
          | @dec _ _ _ v hi hv =>
              rw [hM0] at hi; cases hi
              obtain ⟨n₁, c₂, hn₁, h₁, hc₂, hrest₂⟩ :=
                hrest.split (lo' := o + 1) (hi' := o + 1 + p.len) (by omega)
              obtain ⟨hpc₂, hex₂⟩ := exec_of_stepsIn p hMp (Or.inl (by omega)) n₁ h₁ hc₂
              obtain ⟨pc₂, r₂⟩ := c₂
              simp only at hpc₂ hex₂
              subst hpc₂
              obtain ⟨hpc, hex⟩ := ihn (m - n₁) (by omega) r₂ hrest₂
              exact ⟨hpc, .loopS hv hex₂ hex⟩

/-- A run of the whole machine is confined to `[0, M.length)`. -/
theorem stepsIn_of_run {M : KM} {c c' : KConf} (h : Run M c c') :
    ∃ n, StepsIn M 0 M.length n c c' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head hs _ ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n + 1, .step (Nat.zero_le _) ?_ hs hn⟩
      cases hs with
      | inc hi => exact (List.getElem?_eq_some_iff.1 hi).1
      | zero hi _ => exact (List.getElem?_eq_some_iff.1 hi).1
      | dec hi _ => exact (List.getElem?_eq_some_iff.1 hi).1

theorem contains_self (L : List KInstr) : Contains L 0 L := by
  intro n hn; simp [hn]

/-- **The machine of a structured program halts exactly when the program has an execution.** -/
theorem halts_iff_exec (p : Prog) (r : ℕ → ℕ) :
    KM.Halts (p.code 0 p.len) r ↔ ∃ r', Exec p r r' := by
  have hM : Contains (p.code 0 p.len) 0 (p.code 0 p.len) := contains_self _
  constructor
  · rintro ⟨c', hrun, hc'⟩
    obtain ⟨n, hn⟩ := stepsIn_of_run hrun
    rw [code_length] at hn hc'
    have := exec_of_stepsIn p hM (Or.inr (by omega)) n (by simpa using hn) (by omega)
    exact ⟨c'.r, this.2⟩
  · rintro ⟨r', hex⟩
    exact ⟨⟨p.len, r'⟩, hex.run hM, by simp [code_length]⟩

/-- The registers mentioned by a program. -/
def regs : Prog → List ℕ
  | inc i => [i]
  | dec i => [i]
  | seq p q => p.regs ++ q.regs
  | loop i p => i :: p.regs

theorem regsBelow_code : ∀ (p : Prog) (o e k : ℕ), (∀ i ∈ p.regs, i < k) →
    ∀ ins ∈ p.code o e, ins.reg < k
  | inc i, o, e, k, h, ins, hins => by
      simp [code] at hins; subst hins; exact h i (by simp [regs])
  | dec i, o, e, k, h, ins, hins => by
      simp [code] at hins; subst hins; exact h i (by simp [regs])
  | seq p q, o, e, k, h, ins, hins => by
      simp only [code, List.mem_append] at hins
      rcases hins with hins | hins
      · exact regsBelow_code p _ _ k (fun i hi => h i (by simp [regs, hi])) ins hins
      · exact regsBelow_code q _ _ k (fun i hi => h i (by simp [regs, hi])) ins hins
  | loop i p, o, e, k, h, ins, hins => by
      simp only [code, List.mem_cons] at hins
      rcases hins with rfl | hins
      · exact h i (by simp [regs])
      · exact regsBelow_code p _ _ k (fun j hj => h j (by simp [regs, hj])) ins hins

end Prog

end Minsky
