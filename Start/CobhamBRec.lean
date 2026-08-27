/-
**Bounded recursion on notation, compiled into Boolean circuits.**

This module completes the compiler of `Start/CobhamCircuit.lean` with the one construction that
needs an idea: bounded recursion on notation.  The recursion runs over the first argument, whose
value is not known at compile time, so the step is unrolled once for every position of the
(bounded) recursion argument, and the value at a position is multiplexed between the step value
and the value carried over according to whether the argument really has a bit there.  Dropping a
prefix of a word costs no gates at all in the representation of `Start/WordCircuit.lean`, which is
what makes the unrolling possible.

Main definitions:

* `Complexity.Tseitin.bRecVal` — the value of a bounded recursion as a function of the recursion
  argument.

Main results:

* `Complexity.Tseitin.exists_bRecSig` — the unrolled recursion as a circuit;
* `Complexity.Tseitin.cobCompiles_bRec` — bounded recursion compiles;
* `Complexity.Tseitin.cobCompiles` — **every Cobham term compiles into circuits of polynomial
  size**.
-/

import Start.CobhamCircuit

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### The value of a bounded recursion -/

/-- The value of a bounded recursion on notation with base `g`, steps `h₀`, `h₁`, bound `bd` and
side arguments `rest`, as a function of the recursion argument. -/
def bRecVal (g h₀ h₁ bd : Cob) (rest : List Word) : Word → Word :=
  fun u => List.rec (g.eval rest)
    (fun b x' ih =>
      (if b then h₁.eval (x' :: ih :: rest) else h₀.eval (x' :: ih :: rest)).take
        ((bd.eval ((b :: x') :: rest)).length)) u

@[simp] theorem bRecVal_nil (g h₀ h₁ bd : Cob) (rest : List Word) :
    bRecVal g h₀ h₁ bd rest [] = g.eval rest := rfl

@[simp] theorem bRecVal_cons (g h₀ h₁ bd : Cob) (rest : List Word) (b : Bool) (x' : Word) :
    bRecVal g h₀ h₁ bd rest (b :: x') =
      (if b then h₁.eval (x' :: bRecVal g h₀ h₁ bd rest x' :: rest)
        else h₀.eval (x' :: bRecVal g h₀ h₁ bd rest x' :: rest)).take
        ((bd.eval ((b :: x') :: rest)).length) := rfl

theorem eval_bRec_eq_bRecVal (g h₀ h₁ bd : Cob) (args : List Word) :
    (Cob.bRec g h₀ h₁ bd).eval args = bRecVal g h₀ h₁ bd args.tail (args.headD []) := by
  rw [Cob.eval_bRec]
  rfl

theorem length_bRecVal_le (g h₀ h₁ bd : Cob) (rest : List Word) (u : Word) (B : ℕ)
    (hg : (g.eval rest).length ≤ B) (hbd : ∀ w : Word, (bd.eval (w :: rest)).length ≤ B) :
    (bRecVal g h₀ h₁ bd rest u).length ≤ B := by
  cases u with
  | nil => simpa using hg
  | cons b x' =>
      rw [bRecVal_cons, List.length_take]
      exact le_trans (min_le_left _ _) (hbd (b :: x'))

/-! ### The unrolled recursion -/

/-- **The unrolled bounded recursion as a circuit.**  Signals for the side arguments and for the
recursion argument are given; the recursion is unrolled once per position of the recursion
argument, and at each position the step value is multiplexed against the value carried over. -/
theorem exists_bRecSig {g h₀ h₁ bd : Cob} {m nr Mu Mrv Mhv cg c0 c1 cB K : ℕ}
    (hgc : CompilesAt g Mrv cg) (h0c : CompilesAt h₀ Mhv c0) (h1c : CompilesAt h₁ Mhv c1)
    (hBc : CompilesAt bd Mhv cB)
    (hK : c1 + c0 + cB + 11 * Mhv + 8 * Mrv + 1 ≤ K)
    {C : Circuit} (hC : wf C) {Sr : ℕ → List ℕ × List ℕ} {Fr : ℕ → Word → Word}
    (hSr : ArgSig C m nr Sr Fr) {F0 : Word → Word} {pu bu : List ℕ}
    (hu : WHolds C Mu pu bu F0) (hMu : Mu ≤ m)
    (hgle : ∀ args : List Word, maxLen args ≤ m → (g.eval args).length ≤ Mrv)
    (hBle : ∀ args : List Word, maxLen args ≤ m → (bd.eval args).length ≤ Mrv)
    (h0le : ∀ args : List Word, maxLen args ≤ Mrv → (h₀.eval args).length ≤ Mhv)
    (h1le : ∀ args : List Word, maxLen args ≤ Mrv → (h₁.eval args).length ≤ Mhv)
    (hmr : m ≤ Mrv) (hrh : Mrv ≤ Mhv) :
    ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧
      WHolds C' Mrv ps bs (fun x => bRecVal g h₀ h₁ bd (argsOf Fr nr x) (F0 x)) ∧
      C'.length ≤ C.length + (cg + Mu * K) := by
  have hchain : ∀ t, t ≤ Mu → ∃ (C' : Circuit) (ps bs : List ℕ), Ext C C' ∧ wf C' ∧
      WHolds C' Mrv ps bs
        (fun x => bRecVal g h₀ h₁ bd (argsOf Fr nr x) ((F0 x).drop (Mu - t))) ∧
      C'.length ≤ C.length + (cg + t * K) := by
    intro t
    induction t with
    | zero =>
        intro _
        obtain ⟨C₁, ps, bs, e₁, w₁, hh, l₁⟩ :=
          hgc nr Mrv C Sr Fr hC (hSr.widen hmr) le_rfl (fun x => hgle _ (hSr.maxLen_le x))
        refine ⟨C₁, ps, bs, e₁, w₁, hh.congr fun x => ?_, by omega⟩
        have hnil : (F0 x).drop (Mu - 0) = [] :=
          List.drop_eq_nil_of_le (by simpa using hu.bnd x)
        rw [hnil, bRecVal_nil]
    | succ t iht =>
        intro ht
        obtain ⟨Ck, pk, bk, ek, wk, hk, lk⟩ := iht (by omega)
        obtain ⟨j, hj₁, hj₂⟩ : ∃ j, Mu - t = j + 1 ∧ Mu - (t + 1) = j :=
          ⟨Mu - (t + 1), by omega, rfl⟩
        have hjMu : j < Mu := by omega
        rw [hj₁] at hk
        rw [hj₂]
        have hu' : WHolds Ck Mu pu bu F0 := hu.mono ek
        have hx' : WHolds Ck (Mu - (j + 1)) (pu.drop (j + 1)) (bu.drop (j + 1))
            (fun x => (F0 x).drop (j + 1)) := hu'.drop (j + 1)
        have hDs : WHolds Ck (Mu - j) (pu.drop j) (bu.drop j) (fun x => (F0 x).drop j) :=
          hu'.drop j
        have hbit : Holds Ck (bu.getD j 0) (fun x => (F0 x).getD j false) := hu'.bit j hjMu
        have hpres : Holds Ck (pu.getD j 0) (fun x => decide (j < (F0 x).length)) :=
          hu'.pres j hjMu
        have hSk : ArgSig Ck m nr Sr Fr := hSr.mono ek
        -- the arguments of the step functions: the tail of the recursion argument, the value
        -- carried over, and the side arguments
        have ASh := ((hSk.widen hmr).cons hk le_rfl).cons hx' (by omega)
        have hargsh : ∀ x, argsOf
            (consFun (fun y : Word => (F0 y).drop (j + 1))
              (consFun (fun y : Word => bRecVal g h₀ h₁ bd (argsOf Fr nr y) ((F0 y).drop (j + 1)))
                Fr)) (nr + 1 + 1) x
            = (F0 x).drop (j + 1) ::
              bRecVal g h₀ h₁ bd (argsOf Fr nr x) ((F0 x).drop (j + 1)) :: argsOf Fr nr x := by
          intro x
          rw [argsOf_consFun, argsOf_consFun]
        obtain ⟨C₁, p₁, b₁, e₁, w₁, hh1, l₁⟩ :=
          h1c (nr + 1 + 1) Mhv Ck _ _ wk (ASh.widen hrh) le_rfl
            (fun x => h1le _ (ASh.maxLen_le x))
        obtain ⟨C₂, p₂, b₂, e₂, w₂, hh0, l₂⟩ :=
          h0c (nr + 1 + 1) Mhv C₁ _ _ w₁ ((ASh.widen hrh).mono e₁) le_rfl
            (fun x => h0le _ (ASh.maxLen_le x))
        -- the arguments of the bound: the recursion argument itself and the side arguments
        have ASb := (hSk.mono (e₁.trans e₂)).cons (hDs.mono (e₁.trans e₂)) (by omega)
        have hargsb : ∀ x, argsOf (consFun (fun y : Word => (F0 y).drop j) Fr) (nr + 1) x
            = (F0 x).drop j :: argsOf Fr nr x := fun x => argsOf_consFun _ _ _ _
        obtain ⟨C₃, p₃, b₃, e₃, w₃, hhB, l₃⟩ :=
          hBc (nr + 1) Mhv C₂ _ _ w₂ (ASb.widen (by omega)) le_rfl
            (fun x => le_trans (hBle _ (ASb.maxLen_le x)) hrh)
        obtain ⟨C₄, p₄, b₄, e₄, w₄, l₄, hh4⟩ :=
          exists_iteSig w₃ (hbit.mono (e₁.trans (e₂.trans e₃)))
            (hh1.mono (e₂.trans e₃)) (hh0.mono e₃)
        obtain ⟨C₅, p₅, b₅, e₅, w₅, l₅, hh5⟩ := exists_takeSig w₄ hh4 (hhB.mono e₄)
        have hBsmall : ∀ x,
            (bd.eval (argsOf (consFun (fun y : Word => (F0 y).drop j) Fr) (nr + 1) x)).length
              ≤ Mrv := fun x => hBle _ (ASb.maxLen_le x)
        obtain ⟨C₆, p₆, b₆, e₆, w₆, l₆, hh6⟩ :=
          exists_resize w₅ hh5 Mrv (fun x => by
            rw [List.length_take]
            exact le_trans (min_le_left _ _) (hBsmall x))
        have echain : Ext Ck C₆ := e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans e₆))))
        obtain ⟨C₇, p₇, b₇, e₇, w₇, l₇, hh7⟩ :=
          exists_iteSig w₆ (hpres.mono echain) hh6 (hk.mono echain)
        refine ⟨C₇, p₇, b₇, ek.trans (echain.trans e₇), w₇, hh7.congr fun x => ?_, ?_⟩
        · simp only [hargsh x, hargsb x, decide_eq_true_eq]
          by_cases hlt : j < (F0 x).length
          · rw [if_pos hlt]
            have hdrop : (F0 x).drop j = (F0 x).getD j false :: (F0 x).drop (j + 1) := by
              rw [List.drop_eq_getElem_cons hlt, List.getD_eq_getElem _ _ hlt]
            rw [hdrop, bRecVal_cons]
          · rw [if_neg hlt]
            have h₁' : (F0 x).drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
            have h₂' : (F0 x).drop j = [] := List.drop_eq_nil_of_le (by omega)
            rw [h₁', h₂']
        · have hmul : (t + 1) * K = t * K + K := by ring
          omega
  obtain ⟨C', ps, bs, e, w, hh, l⟩ := hchain Mu le_rfl
  refine ⟨C', ps, bs, e, w, hh.congr fun x => ?_, l⟩
  rw [Nat.sub_self, List.drop_zero]

/-! ### Bounded recursion compiles -/

theorem cobCompiles_bRec (g h₀ h₁ bd : Cob) (hg : CobCompiles g) (hh0 : CobCompiles h₀)
    (hh1 : CobCompiles h₁) (hbdc : CobCompiles bd) : CobCompiles (.bRec g h₀ h₁ bd) := by
  obtain ⟨bg, hbg, hgc⟩ := hg
  obtain ⟨b0, hb0, h0c⟩ := hh0
  obtain ⟨b1, hb1, h1c⟩ := hh1
  obtain ⟨bB, hbB, hBc⟩ := hbdc
  obtain ⟨ag, kg, hag⟩ := Cob.polyLen g
  obtain ⟨aB, kB, haB⟩ := Cob.polyLen bd
  obtain ⟨a0, k0, ha0⟩ := Cob.polyLen h₀
  obtain ⟨a1, k1, ha1⟩ := Cob.polyLen h₁
  obtain ⟨Mr, hMr, hMrle, hMrg, hMrB⟩ :
      ∃ Mr : ℕ → ℕ, MonoPoly Mr ∧ (∀ m, m ≤ Mr m) ∧
        (∀ m args, maxLen args ≤ m → (g.eval args).length ≤ Mr m) ∧
        (∀ m args, maxLen args ≤ m → (bd.eval args).length ≤ Mr m) := by
    refine ⟨fun m => m + ag * (m + 1) ^ kg + aB * (m + 1) ^ kB,
      (MonoPoly.id'.add (MonoPoly.std ag kg)).add (MonoPoly.std aB kB),
      fun m => by change m ≤ m + ag * (m + 1) ^ kg + aB * (m + 1) ^ kB; omega, ?_, ?_⟩
    · intro m args hm
      have hb := hag args
      have hmono : ag * (maxLen args + 1) ^ kg ≤ ag * (m + 1) ^ kg :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      change (g.eval args).length ≤ m + ag * (m + 1) ^ kg + aB * (m + 1) ^ kB
      omega
    · intro m args hm
      have hb := haB args
      have hmono : aB * (maxLen args + 1) ^ kB ≤ aB * (m + 1) ^ kB :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      change (bd.eval args).length ≤ m + ag * (m + 1) ^ kg + aB * (m + 1) ^ kB
      omega
  obtain ⟨Mh, hMh, hMhle, hMh0, hMh1⟩ :
      ∃ Mh : ℕ → ℕ, MonoPoly Mh ∧ (∀ m, Mr m ≤ Mh m) ∧
        (∀ m args, maxLen args ≤ Mr m → (h₀.eval args).length ≤ Mh m) ∧
        (∀ m args, maxLen args ≤ Mr m → (h₁.eval args).length ≤ Mh m) := by
    refine ⟨fun m => Mr m + a0 * (Mr m + 1) ^ k0 + a1 * (Mr m + 1) ^ k1,
      (hMr.add ((MonoPoly.std a0 k0).comp hMr)).add ((MonoPoly.std a1 k1).comp hMr),
      fun m => by
        change Mr m ≤ Mr m + a0 * (Mr m + 1) ^ k0 + a1 * (Mr m + 1) ^ k1
        omega, ?_, ?_⟩
    · intro m args hm
      have hb := ha0 args
      have hmono : a0 * (maxLen args + 1) ^ k0 ≤ a0 * (Mr m + 1) ^ k0 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      change (h₀.eval args).length ≤ Mr m + a0 * (Mr m + 1) ^ k0 + a1 * (Mr m + 1) ^ k1
      omega
    · intro m args hm
      have hb := ha1 args
      have hmono : a1 * (maxLen args + 1) ^ k1 ≤ a1 * (Mr m + 1) ^ k1 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      change (h₁.eval args).length ≤ Mr m + a0 * (Mr m + 1) ^ k0 + a1 * (Mr m + 1) ^ k1
      omega
  have hKpoly : MonoPoly (fun m =>
      b1 (Mh m) + b0 (Mh m) + bB (Mh m) + 11 * Mh m + 8 * Mr m + 1) :=
    ((((hb1.comp hMh).add (hb0.comp hMh)).add (hbB.comp hMh)).add
      ((MonoPoly.const 11).mul hMh)).add ((MonoPoly.const 8).mul hMr) |>.add (MonoPoly.const 1)
  refine ⟨fun m => 3 + bg (Mr m) +
      m * (b1 (Mh m) + b0 (Mh m) + bB (Mh m) + 11 * Mh m + 8 * Mr m + 1),
    ((MonoPoly.const 3).add (hbg.comp hMr)).add (MonoPoly.id'.mul hKpoly), ?_⟩
  intro m n Mout C S F hC hS hMout hbnd
  obtain ⟨C₀, Mu, pu, bu, e₀, w₀, hMu, l₀, hu⟩ := exists_argSig hC hS 0
  obtain ⟨C₁, ps, bs, e₁, w₁, hh, l₁⟩ :=
    exists_bRecSig (hgc (Mr m)) (h0c (Mh m)) (h1c (Mh m)) (hBc (Mh m)) le_rfl w₀
      (hS.tail.mono e₀) hu hMu (hMrg m) (hMrB m) (hMh0 m) (hMh1 m) (hMrle m) (hMhle m)
  have hval : ∀ x, (Cob.bRec g h₀ h₁ bd).eval (argsOf F n x)
      = bRecVal g h₀ h₁ bd (argsOf (fun i => F (i + 1)) (n - 1) x) (F 0 x) := by
    intro x
    rw [eval_bRec_eq_bRecVal, tail_argsOf, headD_argsOf hS.triv]
  obtain ⟨C₂, ps₂, bs₂, e₂, w₂, l₂, hh₂⟩ :=
    exists_resize w₁ hh Mout (fun x => by rw [← hval x]; exact hbnd x)
  refine ⟨C₂, ps₂, bs₂, e₀.trans (e₁.trans e₂), w₂, hh₂.congr fun x => (hval x).symm, ?_⟩
  change C₂.length ≤ C.length +
    (3 + bg (Mr m) + m * (b1 (Mh m) + b0 (Mh m) + bB (Mh m) + 11 * Mh m + 8 * Mr m + 1))
  have hmul : Mu * (b1 (Mh m) + b0 (Mh m) + bB (Mh m) + 11 * Mh m + 8 * Mr m + 1)
      ≤ m * (b1 (Mh m) + b0 (Mh m) + bB (Mh m) + 11 * Mh m + 8 * Mr m + 1) :=
    Nat.mul_le_mul_right _ hMu
  omega

/-! ### Every Cobham term compiles -/

theorem cobCompiles_aux : ∀ (sz : ℕ) (v : Cob), sizeOf v ≤ sz → CobCompiles v := by
  intro sz
  induction sz with
  | zero =>
      intro v hv
      exfalso
      cases v <;> simp at hv
  | succ sz ih =>
      intro v hv
      match v with
      | .proj i => exact cobCompiles_proj i
      | .empty => exact cobCompiles_empty
      | .app b => exact cobCompiles_app b
      | .smash => exact cobCompiles_smash
      | .comp f gs =>
          have hsz : sizeOf f + sizeOf gs < sz + 1 := by
            simp only [Cob.comp.sizeOf_spec] at hv
            omega
          refine cobCompiles_comp f gs (ih f (by omega)) fun g hg => ih g ?_
          have := List.sizeOf_lt_of_mem hg
          omega
      | .bRec g h₀ h₁ bd =>
          have hsz : sizeOf g + sizeOf h₀ + sizeOf h₁ + sizeOf bd < sz + 1 := by
            simp only [Cob.bRec.sizeOf_spec] at hv
            omega
          exact cobCompiles_bRec g h₀ h₁ bd (ih g (by omega)) (ih h₀ (by omega))
            (ih h₁ (by omega)) (ih bd (by omega))

/-- **Every Cobham term compiles into circuits of polynomial size.** -/
theorem cobCompiles (v : Cob) : CobCompiles v := cobCompiles_aux (sizeOf v) v le_rfl

end Tseitin

end Complexity
