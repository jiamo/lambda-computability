/-
Structural folds over lambda terms, and their arithmetizations.

Several later developments (busy beavers, the halting/`K` bridge, the enumeration behind
Chaitin's `Ω`) need *numerical* attributes of a term — its size, its number of free variables,
the length of its binary code — to be computable from the term's code.  All of these attributes
are structural folds:

  `termFold fv fapp flam (var i) = fv i`,
  `termFold fv fapp flam (app a b) = fapp (…a) (…b)`,
  `termFold fv fapp flam (lam u) = flam (…u)`,

so this module arithmetizes the fold once and for all: `Lambda.codeFold` computes
`Lambda.termFold` on codes (`Lambda.codeFold_correct`) and is primitive recursive as soon as the
three components are (`Lambda.codeFold_primrec`).

Instances built here:

* `Lambda.size_code` — the syntactic size `Lambda.size` used by plain Kolmogorov complexity;
* `Lambda.freeMax` / `Lambda.freeMax_code` — one more than the largest free de Bruijn index, so
  that `Lambda.isClosed_iff_freeMax_eq_zero` turns closedness into a primitive recursive test;
* `Lambda.encBound` — a monotone, primitive recursive bound on the code of a term in terms of its
  size (`Lambda.encode_le_encBound`), which is what turns "search all terms of size ≤ n" into a
  bounded search over codes.
-/

import Start.Kolmogorov

set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

------------------------------------------------------------------------
-- Structural folds
------------------------------------------------------------------------

/-- A numerical structural fold over a term. -/
def termFold (fv : ℕ → ℕ) (fapp : ℕ → ℕ → ℕ) (flam : ℕ → ℕ) : Lambda → ℕ
  | Lambda.var i => fv i
  | Lambda.app a b => fapp (termFold fv fapp flam a) (termFold fv fapp flam b)
  | Lambda.lam u => flam (termFold fv fapp flam u)

/-- One layer of the code-level fold: `L` holds the values of the fold at all codes below
`L.length`, and this computes the value at `L.length`. -/
def codeFoldStep (fv : ℕ → ℕ) (fapp : ℕ → ℕ → ℕ) (flam : ℕ → ℕ) (L : List ℕ) : ℕ :=
  let c := L.length
  let m := c.unpair.2
  if c.unpair.1 = 1 then fapp (L.getD m.unpair.1 0) (L.getD m.unpair.2 0)
  else if c.unpair.1 = 2 then flam (L.getD m 0)
  else fv m

/-- The code-level structural fold. -/
def codeFold (fv : ℕ → ℕ) (fapp : ℕ → ℕ → ℕ) (flam : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.strongRecOn n fun n ih =>
    codeFoldStep fv fapp flam ((List.range n).attach.map fun x => ih x.1 (List.mem_range.1 x.2))

/-- Unfolding lemma for `Lambda.codeFold`. -/
theorem codeFold_eq (fv : ℕ → ℕ) (fapp : ℕ → ℕ → ℕ) (flam : ℕ → ℕ) (n : ℕ) :
    codeFold fv fapp flam n =
      codeFoldStep fv fapp flam ((List.range n).map (codeFold fv fapp flam)) := by
  rw [codeFold, Nat.strongRecOn_eq]
  congr! 2
  simp +decide [codeFold]

/-- **The code-level fold computes the term-level fold.** -/
theorem codeFold_correct (fv : ℕ → ℕ) (fapp : ℕ → ℕ → ℕ) (flam : ℕ → ℕ) (t : Lambda) :
    codeFold fv fapp flam (Lambda.encode t) = termFold fv fapp flam t := by
  induction t with
  | var i =>
      rw [codeFold_eq]
      simp [codeFoldStep, Lambda.encode, termFold]
  | app a b iha ihb =>
      have hlen : ((List.range (Lambda.encode (Lambda.app a b))).map
          (codeFold fv fapp flam)).length = Lambda.encode (Lambda.app a b) := by simp
      have hc : Lambda.encode (Lambda.app a b) =
          Nat.pair 1 (Nat.pair (Lambda.encode a) (Lambda.encode b)) := rfl
      have hu : (Lambda.encode (Lambda.app a b)).unpair =
          (1, Nat.pair (Lambda.encode a) (Lambda.encode b)) := by rw [hc, Nat.unpair_pair]
      have hm : (Nat.pair (Lambda.encode a) (Lambda.encode b)).unpair =
          (Lambda.encode a, Lambda.encode b) := Nat.unpair_pair _ _
      have h1 : Lambda.encode a < Lambda.encode (Lambda.app a b) := Lambda.decode_lt_1 hu hm
      have h2 : Lambda.encode b < Lambda.encode (Lambda.app a b) := Lambda.decode_lt_2 hu hm
      rw [codeFold_eq, codeFoldStep]
      simp only [hlen, hu, hm]
      rw [Lambda.getD_range_map h1, Lambda.getD_range_map h2, iha, ihb]
      rfl
  | lam u ih =>
      have hlen : ((List.range (Lambda.encode (Lambda.lam u))).map
          (codeFold fv fapp flam)).length = Lambda.encode (Lambda.lam u) := by simp
      have hc : Lambda.encode (Lambda.lam u) = Nat.pair 2 (Lambda.encode u) := rfl
      have hu : (Lambda.encode (Lambda.lam u)).unpair = (2, Lambda.encode u) := by
        rw [hc, Nat.unpair_pair]
      have h1 : Lambda.encode u < Lambda.encode (Lambda.lam u) := Lambda.decode_lt_3 hu
      rw [codeFold_eq, codeFoldStep]
      simp only [hlen, hu]
      rw [Lambda.getD_range_map h1, ih]
      rfl

theorem codeFoldStep_primrec {fv : ℕ → ℕ} {fapp : ℕ → ℕ → ℕ} {flam : ℕ → ℕ}
    (hv : Primrec fv) (happ : Primrec₂ fapp) (hlam : Primrec flam) :
    Primrec (codeFoldStep fv fapp flam) := by
  have hlen : Primrec (fun L : List ℕ => L.length) := Primrec.list_length
  have hc1 : Primrec (fun L : List ℕ => (Nat.unpair L.length).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hlen)
  have hm : Primrec (fun L : List ℕ => (Nat.unpair L.length).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hlen)
  have hm1 : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair L.length).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hm)
  have hm2 : Primrec (fun L : List ℕ => (Nat.unpair (Nat.unpair L.length).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hm)
  have hget : ∀ {g : List ℕ → ℕ}, Primrec g → Primrec (fun L : List ℕ => L.getD (g L) 0) :=
    fun hg => (Primrec.list_getD 0).comp Primrec.id hg
  have happ' : Primrec (fun L : List ℕ =>
      fapp (L.getD (Nat.unpair (Nat.unpair L.length).2).1 0)
        (L.getD (Nat.unpair (Nat.unpair L.length).2).2 0)) :=
    happ.comp (hget hm1) (hget hm2)
  have hlam' : Primrec (fun L : List ℕ => flam (L.getD (Nat.unpair L.length).2 0)) :=
    hlam.comp (hget hm)
  have hv' : Primrec (fun L : List ℕ => fv (Nat.unpair L.length).2) := hv.comp hm
  exact Primrec.ite (Primrec.eq.comp hc1 (Primrec.const 1)) happ'
    (Primrec.ite (Primrec.eq.comp hc1 (Primrec.const 2)) hlam' hv')

/-- **The code-level fold is primitive recursive** whenever its components are. -/
theorem codeFold_primrec {fv : ℕ → ℕ} {fapp : ℕ → ℕ → ℕ} {flam : ℕ → ℕ}
    (hv : Primrec fv) (happ : Primrec₂ fapp) (hlam : Primrec flam) :
    Primrec (codeFold fv fapp flam) := by
  have h : Primrec₂ (fun (_ : Unit) (L : List ℕ) => some (codeFoldStep fv fapp flam L)) :=
    (Primrec.option_some.comp (codeFoldStep_primrec hv happ hlam)).comp Primrec.snd
  have hstrong : Primrec₂ (fun (_ : Unit) (n : ℕ) => codeFold fv fapp flam n) := by
    refine Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => codeFold fv fapp flam n) h ?_
    intro _ n
    exact congrArg some (codeFold_eq fv fapp flam n).symm
  exact hstrong.comp (Primrec.const ()) Primrec.id

------------------------------------------------------------------------
-- Size
------------------------------------------------------------------------

/-- The code-level syntactic size. -/
def size_code : ℕ → ℕ := codeFold (fun i => i + 1) (fun a b => a + b + 1) (fun a => a + 1)

theorem size_eq_termFold (t : Lambda) :
    size t = termFold (fun i => i + 1) (fun a b => a + b + 1) (fun a => a + 1) t := by
  induction t with
  | var i => rfl
  | app a b iha ihb => simp [size, termFold, iha, ihb]
  | lam u ih => simp [size, termFold, ih]

@[simp] theorem size_code_correct (t : Lambda) : size_code (Lambda.encode t) = size t := by
  rw [size_code, codeFold_correct, size_eq_termFold]

theorem size_code_primrec : Primrec size_code :=
  codeFold_primrec Primrec.succ (Primrec.succ.comp Primrec.nat_add) Primrec.succ

------------------------------------------------------------------------
-- Free variables and closedness
------------------------------------------------------------------------

/-- One more than the largest free de Bruijn index of a term (`0` if the term is closed). -/
def freeMax : Lambda → ℕ := termFold (fun i => i + 1) max (fun a => a - 1)

@[simp] theorem freeMax_var (i : ℕ) : freeMax (Lambda.var i) = i + 1 := rfl
@[simp] theorem freeMax_app (a b : Lambda) :
    freeMax (Lambda.app a b) = max (freeMax a) (freeMax b) := rfl
@[simp] theorem freeMax_lam (u : Lambda) : freeMax (Lambda.lam u) = freeMax u - 1 := rfl

/-- If all free indices are below `k`, substitution above `k` has no effect. -/
theorem isClosedAt_of_freeMax_le : ∀ (t : Lambda) (k : ℕ), freeMax t ≤ k → IsClosedAt t k := by
  intro t
  induction t with
  | var i => intro k hk; exact Lambda.IsClosedAt_var i k (by simpa using hk)
  | app a b iha ihb =>
      intro k hk
      simp only [freeMax_app, max_le_iff] at hk
      exact Lambda.IsClosedAt_app (iha k hk.1) (ihb k hk.2)
  | lam u ih =>
      intro k hk
      simp only [freeMax_lam] at hk
      exact Lambda.IsClosedAt_lam (ih (k + 1) (by omega))

/-- The converse, in the form actually needed: if the "shift" substitutions above `k` have no
effect on `t`, then all free indices of `t` are below `k`. -/
theorem freeMax_le_of_subst_stable : ∀ (t : Lambda) (k : ℕ),
    (∀ x, k ≤ x → Lambda.subst (Lambda.var (x + 1)) x t = t) → freeMax t ≤ k := by
  intro t
  induction t with
  | var i =>
      intro k hk
      by_contra hcon
      have hik : k ≤ i := by simp only [freeMax_var] at hcon; omega
      have := hk i hik
      simp [Lambda.subst] at this
  | app a b iha ihb =>
      intro k hk
      have ha : ∀ x, k ≤ x → Lambda.subst (Lambda.var (x + 1)) x a = a := by
        intro x hx
        have := hk x hx
        simp only [Lambda.subst, Lambda.app.injEq] at this
        exact this.1
      have hb : ∀ x, k ≤ x → Lambda.subst (Lambda.var (x + 1)) x b = b := by
        intro x hx
        have := hk x hx
        simp only [Lambda.subst, Lambda.app.injEq] at this
        exact this.2
      simp only [freeMax_app, max_le_iff]
      exact ⟨iha k ha, ihb k hb⟩
  | lam u ih =>
      intro k hk
      have hu : ∀ x, k + 1 ≤ x → Lambda.subst (Lambda.var (x + 1)) x u = u := by
        intro x hx
        obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
        have hy : k ≤ y := by omega
        have := hk y hy
        simp only [Lambda.subst, Lambda.lam.injEq, Lambda.lift] at this
        exact this
      have := ih (k + 1) hu
      simp only [freeMax_lam]
      omega

theorem isClosedAt_iff_freeMax_le (t : Lambda) (k : ℕ) : IsClosedAt t k ↔ freeMax t ≤ k := by
  constructor
  · intro h
    exact freeMax_le_of_subst_stable t k (fun x hx => h _ x hx)
  · exact isClosedAt_of_freeMax_le t k

/-- **Closedness is a numerical condition on the term**, hence (below) a primitive recursive
test on codes. -/
theorem isClosed_iff_freeMax_eq_zero (t : Lambda) : IsClosed t ↔ freeMax t = 0 := by
  rw [← Lambda.IsClosedAt_zero_iff_IsClosed, isClosedAt_iff_freeMax_le]
  omega

/-- The code-level version of `Lambda.freeMax`. -/
def freeMax_code : ℕ → ℕ := codeFold (fun i => i + 1) max (fun a => a - 1)

@[simp] theorem freeMax_code_correct (t : Lambda) :
    freeMax_code (Lambda.encode t) = freeMax t := codeFold_correct _ _ _ t

theorem freeMax_code_primrec : Primrec freeMax_code :=
  codeFold_primrec Primrec.succ Primrec.nat_max
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))

/-- The primitive recursive closedness test on codes. -/
def isClosed_code (c : ℕ) : Bool := decide (freeMax_code c = 0)

theorem isClosed_code_primrec : Primrec isClosed_code := by
  have h : PrimrecPred (fun c : ℕ => freeMax_code c = 0) :=
    Primrec.eq.comp freeMax_code_primrec (Primrec.const 0)
  obtain ⟨_inst, h⟩ := h
  exact h.of_eq (fun c => by simp [isClosed_code])

@[simp] theorem isClosed_code_correct (t : Lambda) :
    isClosed_code (Lambda.encode t) = Bool.true ↔ IsClosed t := by
  simp [isClosed_code, isClosed_iff_freeMax_eq_zero]

------------------------------------------------------------------------
-- Bounding a code by the size of the term
------------------------------------------------------------------------

/-- Monotonicity of the pairing function. -/
theorem pair_le_pair {a a' b b' : ℕ} (ha : a ≤ a') (hb : b ≤ b') :
    Nat.pair a b ≤ Nat.pair a' b' := by
  unfold Nat.pair
  split_ifs <;> nlinarith

/-- A monotone bound on the code of a term of a given size. -/
def encBound : ℕ → ℕ
  | 0 => 0
  | (n + 1) =>
      encBound n + Nat.pair 0 n + Nat.pair 2 (encBound n) +
        Nat.pair 1 (Nat.pair (encBound n) (encBound n))

theorem encBound_mono : Monotone encBound := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  rw [encBound]
  omega

/-- **Codes are bounded by size**: there are only finitely many codes to inspect if one wants to
enumerate all terms of size at most `n`. -/
theorem encode_le_encBound : ∀ (t : Lambda) (n : ℕ), size t ≤ n → Lambda.encode t ≤ encBound n := by
  intro t
  induction t with
  | var i =>
      intro n hn
      match n with
      | 0 => simp [size] at hn
      | (m + 1) =>
          have hi : i ≤ m := by simp only [size] at hn; omega
          have : Nat.pair 0 i ≤ Nat.pair 0 m := pair_le_pair (le_refl 0) hi
          rw [encBound]
          simp only [Lambda.encode]
          omega
  | app a b iha ihb =>
      intro n hn
      match n with
      | 0 => simp [size] at hn
      | (m + 1) =>
          have hsa : size a ≤ m := by
            have := size_pos b; simp only [size] at hn; omega
          have hsb : size b ≤ m := by
            have := size_pos a; simp only [size] at hn; omega
          have h1 := iha m hsa
          have h2 := ihb m hsb
          have : Nat.pair 1 (Nat.pair (Lambda.encode a) (Lambda.encode b)) ≤
              Nat.pair 1 (Nat.pair (encBound m) (encBound m)) :=
            pair_le_pair (le_refl 1) (pair_le_pair h1 h2)
          rw [encBound]
          simp only [Lambda.encode]
          omega
  | lam u ih =>
      intro n hn
      match n with
      | 0 => simp [size] at hn
      | (m + 1) =>
          have hsu : size u ≤ m := by simp only [size] at hn; omega
          have h1 := ih m hsu
          have : Nat.pair 2 (Lambda.encode u) ≤ Nat.pair 2 (encBound m) :=
            pair_le_pair (le_refl 2) h1
          rw [encBound]
          simp only [Lambda.encode]
          omega

theorem encBound_eq_rec (n : ℕ) : encBound n = Nat.rec (motive := fun _ => ℕ) 0
    (fun n p => p + Nat.pair 0 n + Nat.pair 2 p + Nat.pair 1 (Nat.pair p p)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [encBound, ih]

theorem encBound_primrec : Primrec encBound := by
  have hstep : Primrec₂ (fun (n : ℕ) (p : ℕ) =>
      p + Nat.pair 0 n + Nat.pair 2 p + Nat.pair 1 (Nat.pair p p)) := by
    have h0 : Primrec (fun q : ℕ × ℕ => Nat.pair 0 q.1) :=
      Primrec₂.natPair.comp (Primrec.const 0) Primrec.fst
    have h2 : Primrec (fun q : ℕ × ℕ => Nat.pair 2 q.2) :=
      Primrec₂.natPair.comp (Primrec.const 2) Primrec.snd
    have h1 : Primrec (fun q : ℕ × ℕ => Nat.pair 1 (Nat.pair q.2 q.2)) :=
      Primrec₂.natPair.comp (Primrec.const 1)
        (Primrec₂.natPair.comp Primrec.snd Primrec.snd)
    exact Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd h0) h2) h1
  exact (Primrec.nat_rec₁ 0 hstep).of_eq (fun n => (encBound_eq_rec n).symm)

end Lambda

end
