/-
**Word-register programs run on multi-tape machines** — task `M26-UNIFY-DEPTHTHREE-COBMT`, third
layer, second part.

A word-register program is flattened into low-level instructions (`Complexity.CobMT.flat`), and the
interpreter of `Start/CobMultiTape.lean` runs the flattened code with the cost of the program as a
bound on the number of steps.

* `Complexity.CobMT.RProg.Touches`, `Complexity.CobMT.RProg.WF` — the registers a program uses,
  and the condition that a loop does not use its own register in its body;
* `Complexity.CobMT.flat` — the flattening: loops become a branch on the head of their register,
  the two bodies, a step of the head and a jump back;
* **`Complexity.CobMT.sim`** — **the simulation**: started at the code of `p` with the registers
  `p` uses written on their tapes, the interpreter reaches the end of that code within `cost p R`
  steps, with the registers of `run p R` on those tapes and the other tapes untouched.
-/

import Start.CobMultiTape

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace CobMT

open DepthThreeLowerBound

namespace RProg

/-- The registers a program uses. -/
def Touches : RProg → ℕ → Prop
  | .skip, _ => False
  | .clear r, x => x = r
  | .push r _, x => x = r
  | .trunc r s, x => x = r ∨ x = s
  | .seq p q, x => Touches p x ∨ Touches q x
  | .forBits r p₀ p₁, x => x = r ∨ Touches p₀ x ∨ Touches p₁ x
  | .forBitsRev r p₀ p₁, x => x = r ∨ Touches p₀ x ∨ Touches p₁ x

/-- Loops do not use their own register in their bodies; truncation uses two registers. -/
def WF : RProg → Prop
  | .trunc r s => r ≠ s
  | .seq p q => WF p ∧ WF q
  | .forBits r p₀ p₁ => ¬ Touches p₀ r ∧ ¬ Touches p₁ r ∧ WF p₀ ∧ WF p₁
  | .forBitsRev r p₀ p₁ => ¬ Touches p₀ r ∧ ¬ Touches p₁ r ∧ WF p₀ ∧ WF p₁
  | _ => True

theorem foldl_untouched {p₀ p₁ : RProg} {x : ℕ} (h₀ : ∀ R : Regs, run p₀ R x = R x)
    (h₁ : ∀ R : Regs, run p₁ R x = R x) :
    ∀ (L : List Bool) (R : Regs),
      L.foldl (fun R' b => bif b then run p₁ R' else run p₀ R') R x = R x := by
  intro L
  induction L with
  | nil => intro R; rfl
  | cons b L ih =>
      intro R
      rw [List.foldl_cons, ih]
      cases b
      · exact h₀ R
      · exact h₁ R

/-- A program leaves the registers it does not use alone. -/
theorem run_untouched : ∀ (p : RProg) {x : ℕ}, ¬ Touches p x → ∀ R : Regs, run p R x = R x
  | .skip, _, _, _ => rfl
  | .clear r, x, h, R => Function.update_of_ne h _ _
  | .push r _, x, h, R => Function.update_of_ne h _ _
  | .trunc r s, x, h, R => Function.update_of_ne (fun e => h (Or.inl e)) _ _
  | .seq p q, x, h, R => by
      rw [run_seq, run_untouched q (fun hq => h (Or.inr hq)), run_untouched p (fun hp => h (Or.inl hp))]
  | .forBits r p₀ p₁, x, h, R =>
      foldl_untouched (run_untouched p₀ (fun h' => h (Or.inr (Or.inl h'))))
        (run_untouched p₁ (fun h' => h (Or.inr (Or.inr h')))) _ R
  | .forBitsRev r p₀ p₁, x, h, R => by
      show (R r).foldr _ R x = R x
      rw [← List.foldl_reverse]
      exact foldl_untouched (run_untouched p₀ (fun h' => h (Or.inr (Or.inl h'))))
        (run_untouched p₁ (fun h' => h (Or.inr (Or.inr h')))) _ R

end RProg

open RProg

/-! ### Flattening -/

/-- The length of the flattened code. -/
def flen : RProg → ℕ
  | .skip => 0
  | .clear _ => 1
  | .push _ _ => 1
  | .trunc _ _ => 1
  | .seq p q => flen p + flen q
  | .forBits _ p₀ p₁ => flen p₀ + flen p₁ + 7
  | .forBitsRev _ p₀ p₁ => flen p₀ + flen p₁ + 6

/-- **The flattened code** of a program placed at address `a`. -/
def flat : RProg → ℕ → List LInstr
  | .skip, _ => []
  | .clear r, _ => [.clear r]
  | .push r b, _ => [.push r b]
  | .trunc r s, _ => [.trunc r s]
  | .seq p q, a => flat p a ++ flat q (a + flen p)
  | .forBits r p₀ p₁, a =>
      [.adv r, .branch r (a + flen p₀ + flen p₁ + 6) (a + 2) (a + flen p₀ + 4)] ++ flat p₀ (a + 2) ++
        [.adv r, .jmp (a + 1)] ++ flat p₁ (a + flen p₀ + 4) ++ [.adv r, .jmp (a + 1)] ++ [.rewind r]
  | .forBitsRev r p₀ p₁, a =>
      [.toEnd r, .branch r (a + flen p₀ + flen p₁ + 6) (a + 2) (a + flen p₀ + 4)] ++
        flat p₀ (a + 2) ++ [.retreat r, .jmp (a + 1)] ++ flat p₁ (a + flen p₀ + 4) ++
        [.retreat r, .jmp (a + 1)]

theorem flat_length : ∀ (p : RProg) (a : ℕ), (flat p a).length = flen p
  | .skip, _ => rfl
  | .clear _, _ => rfl
  | .push _ _, _ => rfl
  | .trunc _ _, _ => rfl
  | .seq p q, a => by simp [flat, flen, flat_length p, flat_length q]
  | .forBits _ p₀ p₁, a => by simp [flat, flen, flat_length p₀, flat_length p₁]; omega
  | .forBitsRev _ p₀ p₁, a => by simp [flat, flen, flat_length p₀, flat_length p₁]; omega

/-- The program `prog` holds the code `L` at address `a`. -/
def Contains (prog L : List LInstr) (a : ℕ) : Prop := ∀ k (hk : k < L.length), prog[a + k]? = some L[k]

theorem Contains.left {prog L₁ L₂ : List LInstr} {a : ℕ} (h : Contains prog (L₁ ++ L₂) a) :
    Contains prog L₁ a := fun k hk => by
  have := h k (by simp; omega)
  rwa [List.getElem_append_left hk] at this

theorem Contains.right {prog L₁ L₂ : List LInstr} {a : ℕ} (h : Contains prog (L₁ ++ L₂) a) :
    Contains prog L₂ (a + L₁.length) := fun k hk => by
  have := h (L₁.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simp only [Nat.add_sub_cancel_left] at this
  rwa [← Nat.add_assoc] at this

theorem Contains.get {prog L : List LInstr} {a k : ℕ} (h : Contains prog L a) (hk : k < L.length) :
    prog[a + k]? = some L[k] := h k hk

/-! ### The simulation -/

section Sim

variable {prog : List LInstr} {N : ℕ}

theorem reg_ne_of {x y : ℕ} (hx : x < N) (hy : y < N) (h : x ≠ y) : reg N x ≠ reg N y :=
  fun e => h (reg_injective hx hy e)

/-- What the simulation of `p` from address `a` produces. -/
def SimOK (prog : List LInstr) (N : ℕ) (p : RProg) (a : ℕ) (R : Regs)
    (T : Option (Fin N) → Turing.Tape Sym) : Prop :=
  ∃ T', (∀ x, Touches p x → RepT (T' (reg N x)) (enc (run p R x)) 0) ∧
    (∀ k, (∀ x, Touches p x → k ≠ reg N x) → T' k = T k) ∧
    RunsIn (machine prog N).step ⟨at_ prog a 0, T⟩ ⟨at_ prog (a + flen p) 0, T'⟩ (cost p R)

/-- The hypotheses of the simulation of `p` from address `a`. -/
def SimPre (prog : List LInstr) (N : ℕ) (p : RProg) (a : ℕ) (R : Regs)
    (T : Option (Fin N) → Turing.Tape Sym) : Prop :=
  WF p ∧ (∀ x, Touches p x → x < N) ∧ Contains prog (flat p a) a ∧
    (∀ x, Touches p x → RepT (T (reg N x)) (enc (R x)) 0)

theorem sim_seq {p q : RProg} {a : ℕ} {R : Regs} {T : Option (Fin N) → Turing.Tape Sym}
    (ihp : ∀ a R T, SimPre prog N p a R T → SimOK prog N p a R T)
    (ihq : ∀ a R T, SimPre prog N q a R T → SimOK prog N q a R T)
    (h : SimPre prog N (.seq p q) a R T) : SimOK prog N (.seq p q) a R T := by
  obtain ⟨⟨wfp, wfq⟩, hN, hc, hT⟩ := h
  have hcp : Contains prog (flat p a) a := hc.left
  have hcq : Contains prog (flat q (a + flen p)) (a + flen p) := by
    have := hc.right; rwa [flat_length] at this
  obtain ⟨T₁, h1, f1, r1⟩ := ihp a R T ⟨wfp, fun x hx => hN x (Or.inl hx), hcp,
    fun x hx => hT x (Or.inl hx)⟩
  have hT₁ : ∀ x, Touches q x → RepT (T₁ (reg N x)) (enc (run p R x)) 0 := by
    intro x hx
    by_cases hpx : Touches p x
    · exact h1 x hpx
    · rw [f1 _ (fun y hy => reg_ne_of (hN x (Or.inr hx)) (hN y (Or.inl hy))
        (fun e => hpx (e ▸ hy))), run_untouched p hpx]
      exact hT x (Or.inr hx)
  obtain ⟨T₂, h2, f2, r2⟩ := ihq (a + flen p) (run p R) T₁ ⟨wfq, fun x hx => hN x (Or.inr hx),
    hcq, hT₁⟩
  refine ⟨T₂, fun x hx => ?_, fun k hk => ?_, ?_⟩
  · by_cases hqx : Touches q x
    · exact h2 x hqx
    · rw [f2 _ (fun y hy => reg_ne_of (hN x hx) (hN y (Or.inr hy)) (fun e => hqx (e ▸ hy))),
        run_seq, run_untouched q hqx]
      exact h1 x (hx.resolve_right hqx)
  · rw [f2 k (fun y hy => hk y (Or.inr hy)), f1 k (fun y hy => hk y (Or.inl hy))]
  · rw [flen, ← Nat.add_assoc]
    exact r1.trans r2

theorem sim_skip {a : ℕ} {R : Regs} {T : Option (Fin N) → Turing.Tape Sym} :
    SimOK prog N .skip a R T :=
  ⟨T, fun x hx => hx.elim, fun _ _ => rfl, by simpa [flen] using (RunsIn.refl _ _).mono (by simp [cost])⟩

theorem sim_clear {r a : ℕ} {R : Regs} {T : Option (Fin N) → Turing.Tape Sym}
    (h : SimPre prog N (.clear r) a R T) : SimOK prog N (.clear r) a R T := by
  obtain ⟨-, hN, hc, hT⟩ := h
  have ha : prog[a]? = some (.clear r) := by simpa [flat] using hc.get (k := 0) (by simp [flat])
  obtain ⟨t, ht, hrun⟩ := run_clearI ha T (R r) (hT r rfl)
  refine ⟨Function.update T (reg N r) t, fun x hx => ?_, fun k hk => ?_, ?_⟩
  · subst hx; rw [Function.update_self]; simpa using ht
  · exact Function.update_of_ne (hk r rfl) _ _
  · exact hrun.mono (by simp [cost])

theorem sim_push {r a : ℕ} {b : Bool} {R : Regs} {T : Option (Fin N) → Turing.Tape Sym}
    (h : SimPre prog N (.push r b) a R T) : SimOK prog N (.push r b) a R T := by
  obtain ⟨-, hN, hc, hT⟩ := h
  have ha : prog[a]? = some (.push r b) := by simpa [flat] using hc.get (k := 0) (by simp [flat])
  obtain ⟨t, ht, hrun⟩ := run_pushI ha T (R r) (hT r rfl)
  refine ⟨Function.update T (reg N r) t, fun x hx => ?_, fun k hk => ?_, ?_⟩
  · subst hx; rw [Function.update_self]; simpa using ht
  · exact Function.update_of_ne (hk r rfl) _ _
  · exact hrun.mono (by simp [cost])

theorem sim_trunc {r s a : ℕ} {R : Regs} {T : Option (Fin N) → Turing.Tape Sym}
    (h : SimPre prog N (.trunc r s) a R T) : SimOK prog N (.trunc r s) a R T := by
  obtain ⟨hrs, hN, hc, hT⟩ := h
  have ha : prog[a]? = some (.trunc r s) := by simpa [flat] using hc.get (k := 0) (by simp [flat])
  have hne : reg N r ≠ reg N s := reg_ne_of (hN r (Or.inl rfl)) (hN s (Or.inr rfl)) hrs
  obtain ⟨T', h1, h2, h3, hrun⟩ := run_truncI ha hne T (R r) (R s) (hT r (Or.inl rfl))
    (hT s (Or.inr rfl))
  refine ⟨T', fun x hx => ?_, fun k hk => h3 k (hk r (Or.inl rfl)) (hk s (Or.inr rfl)), ?_⟩
  · rcases hx with rfl | rfl
    · simpa using h1
    · simpa [Function.update_of_ne (Ne.symm hrs)] using h2
  · exact hrun.mono (by simp [cost])

theorem Contains.single {prog : List LInstr} {I : LInstr} {a : ℕ} (h : Contains prog [I] a) :
    prog[a]? = some I := by simpa using h.get (k := 0) (by simp)

theorem Contains.pair {prog : List LInstr} {I J : LInstr} {a : ℕ} (h : Contains prog [I, J] a) :
    prog[a]? = some I ∧ prog[a + 1]? = some J :=
  ⟨by simpa using h.get (k := 0) (by simp), by simpa using h.get (k := 1) (by simp)⟩

theorem sim_forBits {r : ℕ} {p₀ p₁ : RProg} {a : ℕ} {R : Regs} {T : Option (Fin N) → Turing.Tape Sym}
    (ih₀ : ∀ a R T, SimPre prog N p₀ a R T → SimOK prog N p₀ a R T)
    (ih₁ : ∀ a R T, SimPre prog N p₁ a R T → SimOK prog N p₁ a R T)
    (h : SimPre prog N (.forBits r p₀ p₁) a R T) : SimOK prog N (.forBits r p₀ p₁) a R T := by
  obtain ⟨⟨hr₀, hr₁, wf₀, wf₁⟩, hN, hc, hT⟩ := h
  have hrN : r < N := hN r (Or.inl rfl)
  -- the code
  simp only [flat] at hc
  have cD := hc.right
  have cC := hc.left.right
  have c1 := hc.left.left.right
  have cB := hc.left.left.left.right
  have c0 := hc.left.left.left.left.right
  have cA := hc.left.left.left.left.left
  simp only [List.length_append, List.length_cons, List.length_nil, flat_length] at cD cC c1 cB c0
  obtain ⟨hadv0, hbr⟩ := cA.pair
  obtain ⟨hadv1', hjmp1'⟩ := cB.pair
  obtain ⟨hadv2', hjmp2'⟩ := cC.pair
  have hrw' := cD.single
  have e1 : a + (0 + 1 + 1 + flen p₀) = a + 2 + flen p₀ := by omega
  have e2 : a + (0 + 1 + 1 + flen p₀ + (0 + 1 + 1)) = a + flen p₀ + 4 := by omega
  have e3 : a + (0 + 1 + 1 + flen p₀ + (0 + 1 + 1) + flen p₁) = a + flen p₀ + 4 + flen p₁ := by
    omega
  have e4 : a + (0 + 1 + 1 + flen p₀ + (0 + 1 + 1) + flen p₁ + (0 + 1 + 1)) =
      a + flen p₀ + flen p₁ + 6 := by omega
  rw [e1] at hadv1' hjmp1'
  rw [e2] at c1
  rw [e3] at hadv2' hjmp2'
  rw [e4] at hrw'
  have hadv1 := hadv1'
  have hjmp1 := hjmp1'
  have hadv2 := hadv2'
  have hjmp2 := hjmp2'
  have hrw := hrw'
  have c0' : Contains prog (flat p₀ (a + 2)) (a + 2) := by simpa using c0
  -- the loop
  have hneq : ∀ x, (Touches p₀ x ∨ Touches p₁ x) → x ≠ r := fun x hx e => by
    subst e; rcases hx with hx | hx
    · exact hr₀ hx
    · exact hr₁ hx
  have loop : ∀ (L : List Bool) (k : ℕ) (S : Regs) (T₁ : Option (Fin N) → Turing.Tape Sym),
      (R r).drop k = L → k ≤ (R r).length → S r = R r →
      RepT (T₁ (reg N r)) (enc (R r)) (k + 1) →
      (∀ x, (Touches p₀ x ∨ Touches p₁ x) → RepT (T₁ (reg N x)) (enc (S x)) 0) →
      (∀ kk, (∀ x, Touches (.forBits r p₀ p₁) x → kk ≠ reg N x) → T₁ kk = T kk) →
      ∃ T', (∀ x, Touches (.forBits r p₀ p₁) x → RepT (T' (reg N x))
          (enc (L.foldl (fun S' b => bif b then run p₁ S' else run p₀ S') S x)) 0) ∧
        (∀ kk, (∀ x, Touches (.forBits r p₀ p₁) x → kk ≠ reg N x) → T' kk = T kk) ∧
        RunsIn (machine prog N).step ⟨at_ prog (a + 1) 0, T₁⟩
          ⟨at_ prog (a + flen (.forBits r p₀ p₁)) 0, T'⟩
          (iterCost (cost p₀) (cost p₁) (run p₀) (run p₁) L S + (R r).length + 3) := by
    intro L
    induction L with
    | nil =>
        intro k S T₁ hL hk hSr hTr hTb hTf
        have hkw : k = (R r).length := by
          have := List.drop_eq_nil_iff.mp hL; omega
        subst hkw
        have hblank : (T₁ (reg N r)).head = .blank := by
          rw [hTr.head]; push_cast; exact cellAt_enc_end _ _ le_rfl
        have s1 := run_branchI_end hbr T₁ (Or.inl hblank)
        obtain ⟨t, ht, hrun⟩ := run_rewindI (r := r) hrw (noMark_enc (R r)) ((R r).length + 1) T₁ hTr
        refine ⟨Function.update T₁ (reg N r) t, fun x hx => ?_, fun kk hkk => ?_, ?_⟩
        · by_cases hxr : x = r
          · subst hxr; rw [Function.update_self]; simpa [hSr] using ht
          · have hb : Touches p₀ x ∨ Touches p₁ x := hx.resolve_left hxr
            rw [Function.update_of_ne (reg_ne_of (hN x hx) hrN hxr)]
            simpa using hTb x hb
        · rw [Function.update_of_ne (hkk r (Or.inl rfl))]; exact hTf kk hkk
        · have := (RunsIn.single s1).trans hrun
          simp only [flen]
          rw [show a + (flen p₀ + flen p₁ + 7) = a + flen p₀ + flen p₁ + 6 + 1 by omega]
          exact this.mono (by simp [iterCost]; omega)
    | cons b L ih =>
        intro k S T₁ hL hk hSr hTr hTb hTf
        have hkw : k < (R r).length := by
          by_contra hc'; rw [List.drop_eq_nil_of_le (by omega)] at hL; cases hL
        have hbk : (R r)[k] = b := by
          rw [List.drop_eq_getElem_cons hkw] at hL; exact (List.cons.inj hL).1
        have hL' : (R r).drop (k + 1) = L := by
          rw [List.drop_eq_getElem_cons hkw] at hL; exact (List.cons.inj hL).2
        have hhead : (T₁ (reg N r)).head = bitSym b := by
          rw [hTr.head]; push_cast; rw [cellAt_enc_pos _ _ hkw, hbk]
        have s1 := run_branchI_bit hbr T₁ b hhead
        -- the body
        have body : ∀ (pb : RProg) (ab : ℕ), (∀ a R T, SimPre prog N pb a R T → SimOK prog N pb a R T) →
            WF pb → ¬ Touches pb r → (∀ x, Touches pb x → Touches p₀ x ∨ Touches p₁ x) →
            Contains prog (flat pb ab) ab →
            prog[ab + flen pb]? = some (.adv r) → prog[ab + flen pb + 1]? = some (.jmp (a + 1)) →
            ∃ T₃, (∀ x, (Touches p₀ x ∨ Touches p₁ x) → RepT (T₃ (reg N x)) (enc (run pb S x)) 0) ∧
              RepT (T₃ (reg N r)) (enc (R r)) (k + 2) ∧
              (∀ kk, (∀ x, Touches (.forBits r p₀ p₁) x → kk ≠ reg N x) → T₃ kk = T kk) ∧
              RunsIn (machine prog N).step ⟨at_ prog ab 0, T₁⟩ ⟨at_ prog (a + 1) 0, T₃⟩ (cost pb S + 2) := by
          intro pb ab ihb wfb hrb hsub hcb hadv hjmp
          obtain ⟨T₂, h2, f2, r2⟩ := ihb ab S T₁ ⟨wfb, fun x hx => hN x (Or.inr (hsub x hx)), hcb,
            fun x hx => hTb x (hsub x hx)⟩
          have hT₂r : T₂ (reg N r) = T₁ (reg N r) :=
            f2 _ (fun y hy => reg_ne_of hrN (hN y (Or.inr (hsub y hy))) (fun e => hrb (e ▸ hy)))
          have s2 := run_advI hadv T₂
          have s3 := run_jmpI hjmp (Function.update T₂ (reg N r) ((T₂ (reg N r)).move .right))
          refine ⟨Function.update T₂ (reg N r) ((T₂ (reg N r)).move .right), fun x hx => ?_, ?_,
            fun kk hkk => ?_, ?_⟩
          · rw [Function.update_of_ne (reg_ne_of (hN x (Or.inr hx)) hrN (hneq x hx))]
            by_cases hbx : Touches pb x
            · exact h2 x hbx
            · rw [f2 _ (fun y hy => reg_ne_of (hN x (Or.inr hx)) (hN y (Or.inr (hsub y hy)))
                (fun e => hbx (e ▸ hy))), run_untouched pb hbx]
              exact hTb x hx
          · rw [Function.update_self, hT₂r]; exact hTr.right
          · rw [Function.update_of_ne (hkk r (Or.inl rfl)),
              f2 kk (fun y hy => hkk y (Or.inr (hsub y hy)))]
            exact hTf kk hkk
          · have := (r2.trans (RunsIn.single s2)).trans (RunsIn.single s3)
            exact this.mono (by omega)
        obtain ⟨T₃, h3b, h3r, h3f, r3⟩ : ∃ T₃,
            (∀ x, (Touches p₀ x ∨ Touches p₁ x) →
              RepT (T₃ (reg N x)) (enc ((bif b then run p₁ S else run p₀ S) x)) 0) ∧
            RepT (T₃ (reg N r)) (enc (R r)) (k + 2) ∧
            (∀ kk, (∀ x, Touches (.forBits r p₀ p₁) x → kk ≠ reg N x) → T₃ kk = T kk) ∧
            RunsIn (machine prog N).step ⟨at_ prog (bif b then a + flen p₀ + 4 else a + 2) 0, T₁⟩
              ⟨at_ prog (a + 1) 0, T₃⟩ ((bif b then cost p₁ S else cost p₀ S) + 2) := by
          cases b with
          | false =>
              exact body p₀ (a + 2) ih₀ wf₀ hr₀ (fun x hx => Or.inl hx) c0' hadv1 hjmp1
          | true =>
              exact body p₁ (a + flen p₀ + 4) ih₁ wf₁ hr₁ (fun x hx => Or.inr hx) c1 hadv2 hjmp2
        have hSr' : (bif b then run p₁ S else run p₀ S) r = R r := by
          cases b
          · rw [Bool.cond_false, run_untouched p₀ hr₀, hSr]
          · rw [Bool.cond_true, run_untouched p₁ hr₁, hSr]
        obtain ⟨T', h4, f4, r4⟩ := ih (k + 1) _ T₃ hL' (by omega) hSr' h3r h3b h3f
        refine ⟨T', fun x hx => ?_, f4, ?_⟩
        · rw [List.foldl_cons]; exact h4 x hx
        · have := ((RunsIn.single s1).trans r3).trans r4
          exact this.mono (by simp only [iterCost]; omega)
  -- the first move
  have s0 := run_advI hadv0 T
  obtain ⟨T', h1, f1, r1⟩ := loop (R r) 0 R (Function.update T (reg N r) ((T (reg N r)).move .right))
    (by simp) (by omega) rfl (by rw [Function.update_self]; simpa using (hT r (Or.inl rfl)).right)
    (fun x hx => by
      rw [Function.update_of_ne (reg_ne_of (hN x (Or.inr hx)) hrN (hneq x hx))]
      exact hT x (Or.inr hx))
    (fun kk hkk => Function.update_of_ne (hkk r (Or.inl rfl)) _ _)
  refine ⟨T', fun x hx => h1 x hx, f1, ?_⟩
  exact ((RunsIn.single s0).trans r1).mono (by simp only [cost]; omega)

theorem take_reverse_succ (w : Word) {k : ℕ} (hk : k < w.length) :
    (w.take (k + 1)).reverse = w[k] :: (w.take k).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.reverse_append]
  rfl

theorem sim_forBitsRev {r : ℕ} {p₀ p₁ : RProg} {a : ℕ} {R : Regs}
    {T : Option (Fin N) → Turing.Tape Sym}
    (ih₀ : ∀ a R T, SimPre prog N p₀ a R T → SimOK prog N p₀ a R T)
    (ih₁ : ∀ a R T, SimPre prog N p₁ a R T → SimOK prog N p₁ a R T)
    (h : SimPre prog N (.forBitsRev r p₀ p₁) a R T) : SimOK prog N (.forBitsRev r p₀ p₁) a R T := by
  obtain ⟨⟨hr₀, hr₁, wf₀, wf₁⟩, hN, hc, hT⟩ := h
  have hrN : r < N := hN r (Or.inl rfl)
  -- the code
  simp only [flat] at hc
  have cC := hc.right
  have c1 := hc.left.right
  have cB := hc.left.left.right
  have c0 := hc.left.left.left.right
  have cA := hc.left.left.left.left
  simp only [List.length_append, List.length_cons, List.length_nil, flat_length] at cC c1 cB c0
  obtain ⟨hend0, hbr⟩ := cA.pair
  obtain ⟨hret1, hjmp1⟩ := cB.pair
  obtain ⟨hret2, hjmp2⟩ := cC.pair
  have e1 : a + (0 + 1 + 1 + flen p₀) = a + 2 + flen p₀ := by omega
  have e2 : a + (0 + 1 + 1 + flen p₀ + (0 + 1 + 1)) = a + flen p₀ + 4 := by omega
  have e3 : a + (0 + 1 + 1 + flen p₀ + (0 + 1 + 1) + flen p₁) = a + flen p₀ + 4 + flen p₁ := by
    omega
  rw [e1] at hret1 hjmp1
  rw [e2] at c1
  rw [e3] at hret2 hjmp2
  have c0' : Contains prog (flat p₀ (a + 2)) (a + 2) := by simpa using c0
  have hneq : ∀ x, (Touches p₀ x ∨ Touches p₁ x) → x ≠ r := fun x hx e => by
    subst e; rcases hx with hx | hx
    · exact hr₀ hx
    · exact hr₁ hx
  -- the loop
  have loop : ∀ (L : List Bool) (k : ℕ) (S : Regs) (T₁ : Option (Fin N) → Turing.Tape Sym),
      ((R r).take k).reverse = L → k ≤ (R r).length → S r = R r →
      RepT (T₁ (reg N r)) (enc (R r)) k →
      (∀ x, (Touches p₀ x ∨ Touches p₁ x) → RepT (T₁ (reg N x)) (enc (S x)) 0) →
      (∀ kk, (∀ x, Touches (.forBitsRev r p₀ p₁) x → kk ≠ reg N x) → T₁ kk = T kk) →
      ∃ T', (∀ x, Touches (.forBitsRev r p₀ p₁) x → RepT (T' (reg N x))
          (enc (L.foldl (fun S' b => bif b then run p₁ S' else run p₀ S') S x)) 0) ∧
        (∀ kk, (∀ x, Touches (.forBitsRev r p₀ p₁) x → kk ≠ reg N x) → T' kk = T kk) ∧
        RunsIn (machine prog N).step ⟨at_ prog (a + 1) 0, T₁⟩
          ⟨at_ prog (a + flen (.forBitsRev r p₀ p₁)) 0, T'⟩
          (iterCost (cost p₀) (cost p₁) (run p₀) (run p₁) L S + 1) := by
    intro L
    induction L with
    | nil =>
        intro k S T₁ hL hk hSr hTr hTb hTf
        have hk0 : k = 0 := by
          have h1 : ((R r).take k).reverse.length = 0 := by rw [hL]; rfl
          rw [List.length_reverse, List.length_take] at h1
          omega
        subst hk0
        have hmark : (T₁ (reg N r)).head = .mark := by
          rw [hTr.head]; exact cellAt_zero _
        have s1 := run_branchI_end hbr T₁ (Or.inr hmark)
        refine ⟨T₁, fun x hx => ?_, hTf, ?_⟩
        · by_cases hxr : x = r
          · subst hxr; simpa [hSr] using hTr
          · simpa using hTb x (hx.resolve_left hxr)
        · simp only [flen]
          rw [show a + (flen p₀ + flen p₁ + 6) = a + flen p₀ + flen p₁ + 6 by omega]
          exact (RunsIn.single s1).mono (by simp [iterCost])
    | cons b L ih =>
        intro k S T₁ hL hk hSr hTr hTb hTf
        have hk1 : 1 ≤ k := by
          by_contra hne
          have hk0 : k = 0 := by omega
          subst hk0; simp at hL
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hkw : k' < (R r).length := by omega
        rw [take_reverse_succ _ hkw] at hL
        have hbk : (R r)[k'] = b := (List.cons.inj hL).1
        have hL' : ((R r).take k').reverse = L := (List.cons.inj hL).2
        have hhead : (T₁ (reg N r)).head = bitSym b := by
          rw [hTr.head]; push_cast; rw [cellAt_enc_pos _ _ hkw, hbk]
        have s1 := run_branchI_bit hbr T₁ b hhead
        have body : ∀ (pb : RProg) (ab : ℕ), (∀ a R T, SimPre prog N pb a R T → SimOK prog N pb a R T) →
            WF pb → ¬ Touches pb r → (∀ x, Touches pb x → Touches p₀ x ∨ Touches p₁ x) →
            Contains prog (flat pb ab) ab →
            prog[ab + flen pb]? = some (.retreat r) →
            prog[ab + flen pb + 1]? = some (.jmp (a + 1)) →
            ∃ T₃, (∀ x, (Touches p₀ x ∨ Touches p₁ x) → RepT (T₃ (reg N x)) (enc (run pb S x)) 0) ∧
              RepT (T₃ (reg N r)) (enc (R r)) k' ∧
              (∀ kk, (∀ x, Touches (.forBitsRev r p₀ p₁) x → kk ≠ reg N x) → T₃ kk = T kk) ∧
              RunsIn (machine prog N).step ⟨at_ prog ab 0, T₁⟩ ⟨at_ prog (a + 1) 0, T₃⟩
                (cost pb S + 2) := by
          intro pb ab ihb wfb hrb hsub hcb hret hjmp
          obtain ⟨T₂, h2, f2, r2⟩ := ihb ab S T₁ ⟨wfb, fun x hx => hN x (Or.inr (hsub x hx)), hcb,
            fun x hx => hTb x (hsub x hx)⟩
          have hT₂r : T₂ (reg N r) = T₁ (reg N r) :=
            f2 _ (fun y hy => reg_ne_of hrN (hN y (Or.inr (hsub y hy))) (fun e => hrb (e ▸ hy)))
          have s2 := run_retreatI hret T₂
          have s3 := run_jmpI hjmp (Function.update T₂ (reg N r) ((T₂ (reg N r)).move .left))
          refine ⟨Function.update T₂ (reg N r) ((T₂ (reg N r)).move .left), fun x hx => ?_, ?_,
            fun kk hkk => ?_, ?_⟩
          · rw [Function.update_of_ne (reg_ne_of (hN x (Or.inr hx)) hrN (hneq x hx))]
            by_cases hbx : Touches pb x
            · exact h2 x hbx
            · rw [f2 _ (fun y hy => reg_ne_of (hN x (Or.inr hx)) (hN y (Or.inr (hsub y hy)))
                (fun e => hbx (e ▸ hy))), run_untouched pb hbx]
              exact hTb x hx
          · rw [Function.update_self, hT₂r]; exact hTr.left
          · rw [Function.update_of_ne (hkk r (Or.inl rfl)),
              f2 kk (fun y hy => hkk y (Or.inr (hsub y hy)))]
            exact hTf kk hkk
          · have := (r2.trans (RunsIn.single s2)).trans (RunsIn.single s3)
            exact this.mono (by omega)
        obtain ⟨T₃, h3b, h3r, h3f, r3⟩ : ∃ T₃,
            (∀ x, (Touches p₀ x ∨ Touches p₁ x) →
              RepT (T₃ (reg N x)) (enc ((bif b then run p₁ S else run p₀ S) x)) 0) ∧
            RepT (T₃ (reg N r)) (enc (R r)) k' ∧
            (∀ kk, (∀ x, Touches (.forBitsRev r p₀ p₁) x → kk ≠ reg N x) → T₃ kk = T kk) ∧
            RunsIn (machine prog N).step ⟨at_ prog (bif b then a + flen p₀ + 4 else a + 2) 0, T₁⟩
              ⟨at_ prog (a + 1) 0, T₃⟩ ((bif b then cost p₁ S else cost p₀ S) + 2) := by
          cases b with
          | false => exact body p₀ (a + 2) ih₀ wf₀ hr₀ (fun x hx => Or.inl hx) c0' hret1 hjmp1
          | true => exact body p₁ (a + flen p₀ + 4) ih₁ wf₁ hr₁ (fun x hx => Or.inr hx) c1 hret2 hjmp2
        have hSr' : (bif b then run p₁ S else run p₀ S) r = R r := by
          cases b
          · rw [Bool.cond_false, run_untouched p₀ hr₀, hSr]
          · rw [Bool.cond_true, run_untouched p₁ hr₁, hSr]
        obtain ⟨T', h4, f4, r4⟩ := ih k' _ T₃ hL' (by omega) hSr' h3r h3b h3f
        refine ⟨T', fun x hx => ?_, f4, ?_⟩
        · rw [List.foldl_cons]; exact h4 x hx
        · have := ((RunsIn.single s1).trans r3).trans r4
          exact this.mono (by simp only [iterCost]; omega)
  -- moving to the end
  obtain ⟨t, ht, s0⟩ := run_toEndI hend0 T (R r) (hT r (Or.inl rfl))
  obtain ⟨T', h1, f1, r1⟩ := loop (R r).reverse (R r).length R (Function.update T (reg N r) t)
    (by rw [List.take_length]) le_rfl rfl (by rw [Function.update_self]; exact ht)
    (fun x hx => by
      rw [Function.update_of_ne (reg_ne_of (hN x (Or.inr hx)) hrN (hneq x hx))]
      exact hT x (Or.inr hx))
    (fun kk hkk => Function.update_of_ne (hkk r (Or.inl rfl)) _ _)
  refine ⟨T', fun x hx => ?_, f1, ?_⟩
  · have := h1 x hx
    rwa [List.foldl_reverse] at this
  · exact (s0.trans r1).mono (by simp only [cost]; omega)

/-- **The simulation of a word-register program by the interpreter.** -/
theorem sim : ∀ (p : RProg) (a : ℕ) (R : Regs) (T : Option (Fin N) → Turing.Tape Sym),
    SimPre prog N p a R T → SimOK prog N p a R T := by
  intro p
  induction p with
  | skip => intro a R T _; exact sim_skip
  | clear r => intro a R T h; exact sim_clear h
  | push r b => intro a R T h; exact sim_push h
  | trunc r s => intro a R T h; exact sim_trunc h
  | seq p q ihp ihq => intro a R T h; exact sim_seq ihp ihq h
  | forBits r p₀ p₁ ih₀ ih₁ => intro a R T h; exact sim_forBits ih₀ ih₁ h
  | forBitsRev r p₀ p₁ ih₀ ih₁ => intro a R T h; exact sim_forBitsRev ih₀ ih₁ h

end Sim

end CobMT

end Complexity
