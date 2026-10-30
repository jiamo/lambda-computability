/-
**Bridge: GL, the abstract Löb theorem and λ-decidability** — milestone M31 (`M31-BRIDGE-LOGIC`).

`Start/ModalGL.lean` and `Start/ModalGLComplete.lean` prove that the provability logic GL is sound
and complete for finite transitive irreflexive Kripke frames.  `Start/AbstractLob.lean` proves
Löb's theorem and the second incompleteness theorem for every *provability system* (a theory with
the Hilbert–Bernays–Löb derivability conditions and the diagonal lemma).  This module connects
the two to each other and to the computability spine.

* `Lambda.Lob.ProvabilitySystem.realize` — a modal formula read in a provability system, `□` as
  the provability operator; **`Lambda.Lob.ProvabilitySystem.gl_sound`** — **GL is sound for every
  classical provability system** under every interpretation of the variables: Löb's axiom is
  `lob_internal`, `K` is `D2`, necessitation is `D1`;
* `ModalGL.Fml.ofNat`, `ModalGL.Fml.toNat` — a numbering of all modal formulas
  (`Fml.ofNat_toNat`);
* `ModalGL.complete_fin` — **completeness with a bound on the model**: a formula with `s`
  subformula occurrences forced in every transitive irreflexive model on `Fin m`, `m ≤ 4 ^ s`, is
  a theorem (the canonical model of `ModalGLComplete` has at most `4 ^ s` worlds);
* `ModalGL.decideGL` — the decision procedure: all models up to that size, with relations and
  valuations given by bit lists, forcing computed by recursion on the code; `ModalGL.decideGL_iff`
  — it is correct; `ModalGL.decideGL_primrec` — it is primitive recursive;
* **`ModalGL.provable_lambdaDecidable`** — **theoremhood of GL is λ-decidable**: a λ-term decides
  `Provable (Fml.ofNat n)`.
-/

import Start.ModalGLComplete
import Start.AbstractLob
import Start.BridgeComputability

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-! ### GL in provability systems -/

namespace Lambda.Lob.ProvabilitySystem

variable (T : ProvabilitySystem)

/-- A provability system is classical when it proves contraposition, the third propositional
axiom of GL. -/
def IsClassical : Prop :=
  ∀ A B, T.Thm (T.imp (T.imp (T.imp A T.bot) (T.imp B T.bot)) (T.imp B A))

/-- A modal formula read in the system: `⊥`, `→` as themselves and `□` as provability. -/
def realize (ι : ℕ → T.Sen) : ModalGL.Fml → T.Sen
  | .var n => ι n
  | .bot => T.bot
  | .imp p q => T.imp (realize ι p) (realize ι q)
  | .box p => T.box (realize ι p)

/-- **GL is sound for every classical provability system**: every theorem of GL is provable in
the system under every interpretation of its variables. -/
theorem gl_sound (hc : T.IsClassical) (ι : ℕ → T.Sen) {φ : ModalGL.Fml}
    (h : ModalGL.Provable φ) : T.Thm (T.realize ι φ) := by
  induction h with
  | ax1 p q => exact T.ax_k _ _
  | ax2 p q r => exact T.ax_s _ _ _
  | ax3 p q => exact hc _ _
  | axK p q => exact T.d2 _ _
  | axLoeb p => exact T.lob_internal _
  | mp _ _ ih1 ih2 => exact T.mp ih1 ih2
  | nec _ ih => exact T.d1 ih

theorem trueBox_isClassical : trueBox.IsClassical := fun A B h b => by
  by_contra ha
  exact h ha b

end Lambda.Lob.ProvabilitySystem

namespace ModalGL

/-! ### Numbering formulas -/

/-- The code of a formula. -/
def Fml.toNat : Fml → ℕ
  | .bot => 0
  | .var k => 3 * k + 1
  | .imp p q => 3 * Nat.pair p.toNat q.toNat + 2
  | .box p => 3 * p.toNat + 3

/-- The formula of a code; every number is a code. -/
def Fml.ofNat (n : ℕ) : Fml :=
  match n with
  | 0 => .bot
  | n + 1 =>
      if n % 3 = 0 then .var (n / 3)
      else if n % 3 = 1 then
        .imp (Fml.ofNat (Nat.unpair (n / 3)).1) (Fml.ofNat (Nat.unpair (n / 3)).2)
      else .box (Fml.ofNat (n / 3))
termination_by n
decreasing_by
  all_goals
    have h1 := Nat.unpair_left_le (n / 3)
    have h2 := Nat.unpair_right_le (n / 3)
    have h3 := Nat.div_le_self n 3
    omega

theorem Fml.ofNat_zero : Fml.ofNat 0 = .bot := by
  rw [Fml.ofNat]

theorem Fml.ofNat_succ (n : ℕ) : Fml.ofNat (n + 1) =
    if n % 3 = 0 then .var (n / 3)
    else if n % 3 = 1 then
      .imp (Fml.ofNat (Nat.unpair (n / 3)).1) (Fml.ofNat (Nat.unpair (n / 3)).2)
    else .box (Fml.ofNat (n / 3)) := by
  rw [Fml.ofNat]

theorem Fml.ofNat_toNat (φ : Fml) : Fml.ofNat φ.toNat = φ := by
  induction φ with
  | var k =>
      rw [Fml.toNat, Fml.ofNat_succ]
      simp
  | bot => exact Fml.ofNat_zero
  | imp p q ihp ihq =>
      rw [Fml.toNat, show 3 * Nat.pair p.toNat q.toNat + 2 = (3 * Nat.pair p.toNat q.toNat + 1) + 1
        by omega, Fml.ofNat_succ]
      have h1 : (3 * Nat.pair p.toNat q.toNat + 1) % 3 = 1 := by omega
      have h2 : (3 * Nat.pair p.toNat q.toNat + 1) / 3 = Nat.pair p.toNat q.toNat := by omega
      rw [ite_eq_right (by omega), ite_eq_left h1, h2, Nat.unpair_pair, ihp, ihq]
  | box p ih =>
      rw [Fml.toNat, show 3 * p.toNat + 3 = (3 * p.toNat + 2) + 1 by omega, Fml.ofNat_succ]
      have h2 : (3 * p.toNat + 2) / 3 = p.toNat := by omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega), h2, ih]

theorem add_le_pair (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split <;> nlinarith

/-- The subformula list of the formula of `n` has at most `n + 1` entries. -/
theorem Fml.sub_length_ofNat (n : ℕ) : (Fml.ofNat n).sub.length ≤ n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [Fml.ofNat_zero]; simp [Fml.sub]
    | succ n =>
        rw [Fml.ofNat_succ]
        have hd := Nat.div_le_self n 3
        split
        · simp [Fml.sub]
        · split
          · have hab := add_le_pair (Nat.unpair (n / 3)).1 (Nat.unpair (n / 3)).2
            rw [Nat.pair_unpair] at hab
            have ha := ih _ (show (Nat.unpair (n / 3)).1 < n + 1 by omega)
            have hb := ih _ (show (Nat.unpair (n / 3)).2 < n + 1 by omega)
            simp only [Fml.sub, List.length_cons, List.length_append]
            omega
          · have h := ih (n / 3) (by omega)
            simp only [Fml.sub, List.length_cons]
            omega

/-- The variables of the formula of `n` are below `n + 1`. -/
theorem Fml.var_lt_ofNat (n : ℕ) : ∀ k, Fml.var k ∈ (Fml.ofNat n).sub → k < n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk
    cases n with
    | zero => rw [Fml.ofNat_zero] at hk; simp [Fml.sub] at hk
    | succ n =>
        rw [Fml.ofNat_succ] at hk
        have hd := Nat.div_le_self n 3
        split at hk
        · simp only [Fml.sub, List.mem_singleton, Fml.var.injEq] at hk
          omega
        · split at hk
          · have h1 := Nat.unpair_left_le (n / 3)
            have h2 := Nat.unpair_right_le (n / 3)
            simp only [Fml.sub, List.mem_cons, reduceCtorEq, List.mem_append, false_or] at hk
            rcases hk with hk | hk
            · have := ih _ (show (Nat.unpair (n / 3)).1 < n + 1 by omega) k hk
              omega
            · have := ih _ (show (Nat.unpair (n / 3)).2 < n + 1 by omega) k hk
              omega
          · simp only [Fml.sub, List.mem_cons, reduceCtorEq, false_or] at hk
            have := ih (n / 3) (by omega) k hk
            omega

/-! ### Completeness with a bound on the model -/

/-- Forcing is invariant under renaming the worlds. -/
theorem forces_equiv {W W' : Type} (e : W ≃ W') (R : W → W → Prop) (V : W → ℕ → Prop) :
    ∀ (φ : Fml) (w : W), Forces (fun a b => R (e.symm a) (e.symm b)) (fun a n => V (e.symm a) n)
      (e w) φ ↔ Forces R V w φ := by
  intro φ
  induction φ with
  | var n => intro w; simp [Forces]
  | bot => intro w; simp [Forces]
  | imp p q ihp ihq => intro w; simp only [Forces, ihp, ihq]
  | box p ih =>
      intro w
      simp only [Forces]
      constructor
      · intro h v hv
        have := h (e v) (by simpa using hv)
        exact (ih v).1 this
      · intro h v' hv'
        have := (ih (e.symm v')).2 (h _ (by simpa using hv'))
        simpa using this

/-- Forcing depends only on the valuation of the variables of the formula. -/
theorem forces_congr_val {W : Type} (R : W → W → Prop) {V V' : W → ℕ → Prop} :
    ∀ φ : Fml, (∀ k, Fml.var k ∈ φ.sub → ∀ w, (V w k ↔ V' w k)) →
      ∀ w, (Forces R V w φ ↔ Forces R V' w φ) := by
  intro φ
  induction φ with
  | var n => intro h w; exact h n (by simp [Fml.sub]) w
  | bot => intro _ w; simp [Forces]
  | imp p q ihp ihq =>
      intro h w
      have hp := ihp fun k hk => h k (by simp [Fml.sub, hk])
      have hq := ihq fun k hk => h k (by simp [Fml.sub, hk])
      simp only [Forces, hp, hq]
  | box p ih =>
      intro h w
      have hp := ih fun k hk => h k (by simp [Fml.sub, hk])
      simp only [Forces, hp]

/-- The canonical model of a list `L` has at most `4 ^ |L|` worlds. -/
theorem card_canWorld_le (L : List Fml) [Fintype (CanWorld L)] :
    Fintype.card (CanWorld L) ≤ 4 ^ L.length := by
  classical
  have hinj : Function.Injective
      (fun w : CanWorld L => (⟨w.1, Finset.mem_powerset.2 w.2.1⟩ : (closureF L).powerset)) := by
    intro a b h
    apply Subtype.ext
    simpa using h
  have h1 := Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_coe, Finset.card_powerset] at h1
  have h2 : (closureF L).card ≤ 2 * L.length := by
    unfold closureF
    refine (List.toFinset_card_le _).trans ?_
    simp only [List.length_append, List.length_map]
    omega
  calc Fintype.card (CanWorld L) ≤ 2 ^ (closureF L).card := h1
    _ ≤ 2 ^ (2 * L.length) := Nat.pow_le_pow_right (by norm_num) h2
    _ = 4 ^ L.length := by rw [pow_mul]; norm_num

/-- **Completeness of GL with a bound on the model**: a formula forced in every transitive
irreflexive model on `Fin m` with `m ≤ B`, where `4 ^ |sub φ| ≤ B`, is a theorem. -/
theorem complete_fin {φ : Fml} {B : ℕ} (hB : 4 ^ φ.sub.length ≤ B)
    (h : ∀ m ≤ B, ∀ R : Fin m → Fin m → Prop, (∀ a b c, R a b → R b c → R a c) →
      (∀ a, ¬ R a a) → ∀ (V : Fin m → ℕ → Prop) (w : Fin m), Forces R V w φ) :
    Provable φ := by
  by_contra hn
  let L := φ.sub
  have hL : ∀ ψ ∈ L, ∀ χ ∈ ψ.sub, χ ∈ L := fun ψ hψ χ hχ => Fml.sub_trans hψ hχ
  have hc : Consistent [φ.neg] := consistent_neg_of_not_der (Γ := []) fun hd => hn hd.provable
  obtain ⟨Δ, hsub, hcΔ, hdec, hrange⟩ := lindenbaum L hc
  have hΔC : Δ.toFinset ⊆ closureF L := by
    intro q hq
    rw [List.mem_toFinset] at hq
    simp only [closureF, List.mem_toFinset, List.mem_append, List.mem_map]
    rcases hrange q hq with hq | ⟨χ, hχ, rfl | rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact .inr ⟨φ, Fml.mem_sub_self φ, rfl⟩
    · exact .inl hχ
    · exact .inr ⟨χ, hχ, rfl⟩
  let w : CanWorld L := ⟨Δ.toFinset, hΔC,
    fun h => hcΔ (h.mono fun q hq => by simpa using hq),
    fun χ hχ => by simpa only [List.mem_toFinset] using hdec χ hχ⟩
  let _ := Fintype.ofFinite (CanWorld L)
  let e := Fintype.equivFin (CanWorld L)
  have hm : Fintype.card (CanWorld L) ≤ B := (card_canWorld_le L).trans hB
  have hf' := h _ hm (fun a b => canRel L (e.symm a) (e.symm b))
    (fun _ _ _ h1 h2 => CanR.trans h1 h2) (fun a => CanR.irrefl _)
    (fun a n => canVal L (e.symm a) n) (e w)
  have hf := (forces_equiv e (canRel L) (canVal L) φ w).1 hf'
  have hφ := (truth hL φ (Fml.mem_sub_self φ) w).1 hf
  have h1 : φ.neg ∈ Δ := hsub _ (by simp)
  exact hcΔ (.mp (.hyp h1) (.hyp (List.mem_toFinset.1 hφ)))

/-! ### Forcing on models given by bit lists -/

/-- Forcing at the worlds `0, …, m-1` of the model whose relation is `i R j ↔ rel[i m + j]` and
whose valuation is `V i k ↔ val[i K + k]`, as a list of booleans. -/
def forceL (m : ℕ) (rel : List Bool) (K : ℕ) (val : List Bool) : Fml → List Bool
  | .bot => (List.range m).map fun _ => false
  | .var k => (List.range m).map fun i => val.getD (i * K + k) false
  | .imp p q => (List.range m).map fun i =>
      !((forceL m rel K val p).getD i false) || (forceL m rel K val q).getD i false
  | .box p => (List.range m).map fun i => (List.range m).all fun j =>
      !(rel.getD (i * m + j) false) || (forceL m rel K val p).getD j false

theorem getD_map_range {β : Type} (f : ℕ → β) (d : β) {m i : ℕ} (h : i < m) :
    ((List.range m).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem forceL_length (m : ℕ) (rel : List Bool) (K : ℕ) (val : List Bool) (φ : Fml) :
    (forceL m rel K val φ).length = m := by
  cases φ <;> simp [forceL]

theorem forceL_spec (m : ℕ) (rel : List Bool) (K : ℕ) (val : List Bool) :
    ∀ (φ : Fml) (i : Fin m), (forceL m rel K val φ).getD i false = true ↔
      Forces (fun a b : Fin m => rel.getD (a * m + b) false = true)
        (fun a k => val.getD (a * K + k) false = true) i φ := by
  intro φ
  induction φ with
  | var k => intro i; simp [forceL, Forces]
  | bot => intro i; simp [forceL, Forces]
  | imp p q ihp ihq =>
      intro i
      rw [forceL, getD_map_range _ _ i.isLt]
      simp only [Forces, ← ihp i, ← ihq i]
      cases (forceL m rel K val p).getD i false <;> cases (forceL m rel K val q).getD i false <;>
        simp
  | box p ih =>
      intro i
      rw [forceL, getD_map_range _ _ i.isLt, List.all_eq_true]
      simp only [Forces]
      constructor
      · intro h v hv
        have := h v (List.mem_range.2 v.isLt)
        rw [hv] at this
        exact (ih v).1 (by simpa using this)
      · intro h j hj
        have hj' := List.mem_range.1 hj
        by_cases hR : rel.getD (i * m + j) false = true
        · have := (ih ⟨j, hj'⟩).2 (h ⟨j, hj'⟩ hR)
          simp only at this
          rw [hR, this]
          rfl
        · rw [Bool.not_eq_true] at hR
          rw [hR]
          rfl

theorem all_id_iff (L : List Bool) : L.all id = true ↔ ∀ i < L.length, L.getD i false = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i hi
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have := h i hi
    rwa [List.getD_eq_getElem _ _ hi] at this

/-! ### The decision procedure -/

/-- All boolean lists of length `k`. -/
def allLists (k : ℕ) : List (List Bool) :=
  (fun L : List (List Bool) => L.flatMap fun l => [false :: l, true :: l])^[k] [[]]

theorem mem_allLists : ∀ (k : ℕ) (l : List Bool), l.length = k → l ∈ allLists k := by
  intro k
  induction k with
  | zero => intro l hl; simp [allLists, List.length_eq_zero_iff.1 hl]
  | succ k ih =>
      intro l hl
      obtain ⟨b, l', rfl⟩ : ∃ b l', l = b :: l' := by
        cases l with
        | nil => simp at hl
        | cons b l' => exact ⟨b, l', rfl⟩
      have h' := ih l' (by simpa using hl)
      simp only [allLists, Function.iterate_succ_apply'] at h' ⊢
      refine List.mem_flatMap.2 ⟨l', h', ?_⟩
      cases b <;> simp

/-- The relation of a bit list is transitive and irreflexive on `0, …, m-1`. -/
def goodRel (m : ℕ) (rel : List Bool) : Bool :=
  (List.range m).all fun a => !(rel.getD (a * m + a) false) && (List.range m).all fun b =>
    (List.range m).all fun c => !(rel.getD (a * m + b) false) || !(rel.getD (b * m + c) false) ||
      rel.getD (a * m + c) false

theorem goodRel_iff (m : ℕ) (rel : List Bool) :
    goodRel m rel = true ↔ (∀ a < m, rel.getD (a * m + a) false = false) ∧
      ∀ a < m, ∀ b < m, ∀ c < m, rel.getD (a * m + b) false = true →
        rel.getD (b * m + c) false = true → rel.getD (a * m + c) false = true := by
  simp only [goodRel, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true]
  constructor
  · intro h
    refine ⟨fun a ha => (h a ha).1, fun a ha b hb c hc hab hbc => ?_⟩
    rcases (h a ha).2 b hb c hc with (h1 | h1) | h1
    · rw [hab] at h1; cases h1
    · rw [hbc] at h1; cases h1
    · exact h1
  · intro h a ha
    refine ⟨h.1 a ha, fun b hb c hc => ?_⟩
    cases hab : rel.getD (a * m + b) false
    · exact .inl (.inl rfl)
    · cases hbc : rel.getD (b * m + c) false
      · exact .inl (.inr rfl)
      · exact .inr (h.2 a ha b hb c hc hab hbc)

/-- **The decision procedure for GL**: the formula of `n` is forced at every world of every model
with `m ≤ 4 ^ (n + 1)` worlds whose relation is transitive and irreflexive, the valuation being
read on the variables below `n + 1`. -/
def decideGL (n : ℕ) : Bool :=
  (List.range (4 ^ (n + 1) + 1)).all fun m =>
    (allLists (m * m)).all fun rel => !(goodRel m rel) ||
      (allLists (m * (n + 1))).all fun val => (forceL m rel (n + 1) val (Fml.ofNat n)).all id

theorem idx_lt {m a b : ℕ} (ha : a < m) (hb : b < m) : a * m + b < m * m := by
  nlinarith

theorem idx_div {m a b : ℕ} (hb : b < m) : (a * m + b) / m = a := by
  have hm : 0 < m := by omega
  rw [show a * m + b = b + m * a by ring, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt hb,
    zero_add]

theorem idx_mod {m a b : ℕ} (hb : b < m) : (a * m + b) % m = b := by
  rw [show a * m + b = b + a * m by ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

open Classical in
theorem decideGL_iff (n : ℕ) : decideGL n = true ↔ Provable (Fml.ofNat n) := by
  constructor
  · intro hdec
    refine complete_fin (B := 4 ^ (n + 1))
      (Nat.pow_le_pow_right (by norm_num) (Fml.sub_length_ofNat n)) ?_
    intro m hm R htrans hirr V w
    have hm0 : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) w.isLt
    let Rn : ℕ → ℕ → Prop := fun i j => ∃ (hi : i < m) (hj : j < m), R ⟨i, hi⟩ ⟨j, hj⟩
    let Vn : ℕ → ℕ → Prop := fun i k => ∃ hi : i < m, V ⟨i, hi⟩ k
    let rel := (List.range (m * m)).map fun p => decide (Rn (p / m) (p % m))
    let val := (List.range (m * (n + 1))).map fun p => decide (Vn (p / (n + 1)) (p % (n + 1)))
    have hrel : ∀ a b : Fin m, rel.getD (a * m + b) false = true ↔ R a b := by
      intro a b
      simp only [rel]
      rw [getD_map_range _ _ (idx_lt a.isLt b.isLt), idx_div b.isLt, idx_mod b.isLt]
      simp [Rn]
    have hval : ∀ (a : Fin m) (k : ℕ), k < n + 1 →
        (val.getD (a * (n + 1) + k) false = true ↔ V a k) := by
      intro a k hk
      simp only [val]
      rw [getD_map_range _ _ (by nlinarith [a.isLt]), idx_div hk, idx_mod hk]
      simp [Vn]
    have hgood : goodRel m rel = true := by
      rw [goodRel_iff]
      refine ⟨fun a ha => ?_, fun a ha b hb c hc hab hbc => ?_⟩
      · have := hrel ⟨a, ha⟩ ⟨a, ha⟩
        simp only at this
        cases hx : rel.getD (a * m + a) false
        · rfl
        · exact absurd (this.1 hx) (hirr _)
      · have h1 := (hrel ⟨a, ha⟩ ⟨b, hb⟩).1 hab
        have h2 := (hrel ⟨b, hb⟩ ⟨c, hc⟩).1 hbc
        exact (hrel ⟨a, ha⟩ ⟨c, hc⟩).2 (htrans _ _ _ h1 h2)
    simp only [decideGL, List.all_eq_true, List.mem_range] at hdec
    have h1 := hdec m (by omega) rel (mem_allLists _ _ (by simp [rel]))
    rw [hgood, Bool.not_true, Bool.false_or, List.all_eq_true] at h1
    have h2 := h1 val (mem_allLists _ _ (by simp [val]))
    rw [all_id_iff, forceL_length] at h2
    have h3 := (forceL_spec m rel (n + 1) val (Fml.ofNat n) w).1 (h2 w w.isLt)
    have hR : (fun a b : Fin m => rel.getD (a * m + b) false = true) = R := by
      funext a b
      exact propext (hrel a b)
    rw [hR] at h3
    exact (forces_congr_val R (Fml.ofNat n)
      (fun k hk a => hval a k (Fml.var_lt_ofNat n k hk)) w).1 h3
  · intro hp
    simp only [decideGL, List.all_eq_true, List.mem_range]
    intro m _ rel _
    cases hg : goodRel m rel
    · rfl
    · rw [Bool.not_true, Bool.false_or, List.all_eq_true]
      intro val _
      rw [all_id_iff, forceL_length]
      intro i hi
      have hgood := (goodRel_iff m rel).1 hg
      refine (forceL_spec m rel (n + 1) val (Fml.ofNat n) ⟨i, hi⟩).2 ?_
      refine sound hp (fun a b : Fin m => rel.getD (a * m + b) false = true)
        (fun a b c hab hbc => hgood.2 a a.isLt b b.isLt c c.isLt hab hbc) (fun a ha => ?_) _ _
      have := hgood.1 a a.isLt
      rw [this] at ha
      cases ha

/-! ### The decision procedure is primitive recursive -/

open Primrec

theorem primrec_all {α β : Type} [Primcodable α] [Primcodable β] {l : α → List β}
    {p : α → β → Bool} (hl : Primrec l) (hp : Primrec₂ p) : Primrec fun a => (l a).all (p a) := by
  have h := Primrec.list_foldr (σ := Bool) hl (Primrec.const true)
    (Primrec.and.comp (hp.comp fst (fst.comp snd)) (snd.comp snd)).to₂
  refine h.of_eq fun a => ?_
  generalize l a = L
  induction L with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, List.all_cons, ih]

/-- The parameters of a model: worlds, relation, number of variables, valuation. -/
abbrev Params := ℕ × List Bool × ℕ × List Bool

/-- Forcing of the formula of a code. -/
def forceN (a : Params) (c : ℕ) : List Bool := forceL a.1 a.2.1 a.2.2.1 a.2.2.2 (Fml.ofNat c)

/-- One step of the recursion on codes: the forcing list of the code `prev.length` from those of
all smaller codes. -/
def stepF (a : Params) (prev : List (List Bool)) : List Bool :=
  bif prev.length == 0 then (List.range a.1).map fun _ => false
  else bif (prev.length - 1) % 3 == 0 then
    (List.range a.1).map fun i => a.2.2.2.getD (i * a.2.2.1 + (prev.length - 1) / 3) false
  else bif (prev.length - 1) % 3 == 1 then
    (List.range a.1).map fun i =>
      !((prev.getD (Nat.unpair ((prev.length - 1) / 3)).1 []).getD i false) ||
        (prev.getD (Nat.unpair ((prev.length - 1) / 3)).2 []).getD i false
  else (List.range a.1).map fun i => (List.range a.1).all fun j =>
    !(a.2.1.getD (i * a.1 + j) false) || (prev.getD ((prev.length - 1) / 3) []).getD j false

theorem stepF_spec (a : Params) (c : ℕ) :
    stepF a ((List.range c).map (forceN a)) = forceN a c := by
  cases c with
  | zero => simp [stepF, forceN, Fml.ofNat_zero, forceL]
  | succ n =>
      have hd := Nat.div_le_self n 3
      have h1 := Nat.unpair_left_le (n / 3)
      have h2 := Nat.unpair_right_le (n / 3)
      have g1 := getD_map_range (forceN a) [] (show (Nat.unpair (n / 3)).1 < n + 1 by omega)
      have g2 := getD_map_range (forceN a) [] (show (Nat.unpair (n / 3)).2 < n + 1 by omega)
      have g3 := getD_map_range (forceN a) [] (show n / 3 < n + 1 by omega)
      simp only [stepF, List.length_map, List.length_range, Nat.add_sub_cancel, g1, g2, g3]
      simp only [forceN, Fml.ofNat_succ]
      rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h | h | h
      · simp [h, forceL]
      · simp [h, forceL]
      · simp [h, forceL]

theorem stepF_primrec : Primrec₂ stepF := by
  have hm : Primrec fun p : Params × List (List Bool) => p.1.1 := fst.comp fst
  have hrel : Primrec fun p : Params × List (List Bool) => p.1.2.1 := fst.comp (snd.comp fst)
  have hK : Primrec fun p : Params × List (List Bool) => p.1.2.2.1 :=
    fst.comp (snd.comp (snd.comp fst))
  have hval : Primrec fun p : Params × List (List Bool) => p.1.2.2.2 :=
    snd.comp (snd.comp (snd.comp fst))
  have hlen : Primrec fun p : Params × List (List Bool) => p.2.length := list_length.comp snd
  have hn : Primrec fun p : Params × List (List Bool) => p.2.length - 1 :=
    nat_sub.comp hlen (const 1)
  have hd : Primrec fun p : Params × List (List Bool) => (p.2.length - 1) / 3 :=
    nat_div.comp hn (const 3)
  have hr : Primrec fun p : Params × List (List Bool) => (p.2.length - 1) % 3 :=
    nat_mod.comp hn (const 3)
  have hu1 : Primrec fun p : Params × List (List Bool) => (Nat.unpair ((p.2.length - 1) / 3)).1 :=
    fst.comp (unpair.comp hd)
  have hu2 : Primrec fun p : Params × List (List Bool) => (Nat.unpair ((p.2.length - 1) / 3)).2 :=
    snd.comp (unpair.comp hd)
  have b0 : Primrec fun p : Params × List (List Bool) => (List.range p.1.1).map fun _ => false :=
    list_map (list_range.comp hm) (Primrec₂.const false)
  have b1 : Primrec fun p : Params × List (List Bool) => (List.range p.1.1).map fun i =>
      p.1.2.2.2.getD (i * p.1.2.2.1 + (p.2.length - 1) / 3) false :=
    list_map (list_range.comp hm)
      ((list_getD false).comp (hval.comp fst)
        (nat_add.comp (nat_mul.comp snd (hK.comp fst)) (hd.comp fst))).to₂
  have b2 : Primrec fun p : Params × List (List Bool) => (List.range p.1.1).map fun i =>
      !((p.2.getD (Nat.unpair ((p.2.length - 1) / 3)).1 []).getD i false) ||
        (p.2.getD (Nat.unpair ((p.2.length - 1) / 3)).2 []).getD i false :=
    list_map (list_range.comp hm)
      (Primrec.or.comp
        (Primrec.not.comp ((list_getD false).comp
          ((list_getD []).comp (snd.comp fst) (hu1.comp fst)) snd))
        ((list_getD false).comp ((list_getD []).comp (snd.comp fst) (hu2.comp fst)) snd)).to₂
  have b3 : Primrec fun p : Params × List (List Bool) => (List.range p.1.1).map fun i =>
      (List.range p.1.1).all fun j =>
        !(p.1.2.1.getD (i * p.1.1 + j) false) ||
          (p.2.getD ((p.2.length - 1) / 3) []).getD j false :=
    list_map (list_range.comp hm)
      (primrec_all (list_range.comp (hm.comp fst))
        (Primrec.or.comp
          (Primrec.not.comp ((list_getD false).comp (hrel.comp (fst.comp fst))
            (nat_add.comp (nat_mul.comp (snd.comp fst) (hm.comp (fst.comp fst))) snd)))
          ((list_getD false).comp
            ((list_getD []).comp (snd.comp (fst.comp fst)) (hd.comp (fst.comp fst))) snd)).to₂).to₂
  exact (Primrec.cond (Primrec.beq.comp hlen (const 0)) b0
    (Primrec.cond (Primrec.beq.comp hr (const 0)) b1
      (Primrec.cond (Primrec.beq.comp hr (const 1)) b2 b3))).of_eq fun p => rfl

theorem forceN_primrec : Primrec₂ forceN :=
  Primrec.nat_strong_rec forceN (g := fun a prev => some (stepF a prev))
    (option_some.comp stepF_primrec).to₂ fun a c => by rw [stepF_spec]

theorem allLists_primrec : Primrec allLists :=
  (nat_iterate Primrec.id (const [[]])
    (list_flatMap snd
      (list_cons.comp (list_cons.comp (const false) snd)
        (list_cons.comp (list_cons.comp (const true) snd) (const []))).to₂).to₂).of_eq
    fun _ => rfl

theorem goodRel_primrec : Primrec₂ goodRel := by
  -- variables: `x = ((m, rel), a)`, `y = (x, b)`, `z = (y, c)`
  have hm : Primrec fun q : ℕ × List Bool => q.1 := fst
  have hrel : Primrec fun q : ℕ × List Bool => q.2 := snd
  have inner : Primrec₂ fun (y : ((ℕ × List Bool) × ℕ) × ℕ) (c : ℕ) =>
      !(y.1.1.2.getD (y.1.2 * y.1.1.1 + y.2) false) ||
        !(y.1.1.2.getD (y.2 * y.1.1.1 + c) false) || y.1.1.2.getD (y.1.2 * y.1.1.1 + c) false :=
    (Primrec.or.comp
      (Primrec.or.comp
        (Primrec.not.comp ((list_getD false).comp (hrel.comp (fst.comp (fst.comp fst)))
          (nat_add.comp (nat_mul.comp (snd.comp (fst.comp fst)) (hm.comp (fst.comp (fst.comp fst))))
            (snd.comp fst))))
        (Primrec.not.comp ((list_getD false).comp (hrel.comp (fst.comp (fst.comp fst)))
          (nat_add.comp (nat_mul.comp (snd.comp fst) (hm.comp (fst.comp (fst.comp fst)))) snd))))
      ((list_getD false).comp (hrel.comp (fst.comp (fst.comp fst)))
        (nat_add.comp (nat_mul.comp (snd.comp (fst.comp fst)) (hm.comp (fst.comp (fst.comp fst))))
          snd))).to₂
  have middle : Primrec₂ fun (x : (ℕ × List Bool) × ℕ) (b : ℕ) =>
      (List.range x.1.1).all fun c =>
        !(x.1.2.getD (x.2 * x.1.1 + b) false) || !(x.1.2.getD (b * x.1.1 + c) false) ||
          x.1.2.getD (x.2 * x.1.1 + c) false :=
    (primrec_all (list_range.comp (hm.comp (fst.comp fst))) inner).to₂
  have outer : Primrec₂ fun (q : ℕ × List Bool) (a : ℕ) =>
      !(q.2.getD (a * q.1 + a) false) && (List.range q.1).all fun b =>
        (List.range q.1).all fun c => !(q.2.getD (a * q.1 + b) false) ||
          !(q.2.getD (b * q.1 + c) false) || q.2.getD (a * q.1 + c) false :=
    (Primrec.and.comp
      (Primrec.not.comp ((list_getD false).comp (hrel.comp fst)
        (nat_add.comp (nat_mul.comp snd (hm.comp fst)) snd)))
      (primrec_all (list_range.comp (hm.comp fst)) middle)).to₂
  exact (primrec_all (list_range.comp hm) outer).to₂.of_eq fun _ _ => rfl

theorem decideGL_primrec : Primrec decideGL := by
  have hB : Primrec fun n : ℕ => 4 ^ (n + 1) + 1 :=
    succ.comp ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (const 4) succ)
  -- variables: `x = (n, m)`, `y = (x, rel)`, `z = (y, val)`
  have hz : Primrec₂ fun (y : (ℕ × ℕ) × List Bool) (val : List Bool) =>
      (forceL y.1.2 y.2 (y.1.1 + 1) val (Fml.ofNat y.1.1)).all id :=
    (primrec_all
      (forceN_primrec.comp
        (pair (snd.comp (fst.comp fst))
          (pair (snd.comp fst) (pair (succ.comp (fst.comp (fst.comp fst))) snd)))
        (fst.comp (fst.comp fst)))
      (snd : Primrec fun q : (((ℕ × ℕ) × List Bool) × List Bool) × Bool => q.2).to₂).to₂
  have hy : Primrec₂ fun (x : ℕ × ℕ) (rel : List Bool) =>
      !(goodRel x.2 rel) || (allLists (x.2 * (x.1 + 1))).all fun val =>
        (forceL x.2 rel (x.1 + 1) val (Fml.ofNat x.1)).all id :=
    (Primrec.or.comp (Primrec.not.comp (goodRel_primrec.comp (snd.comp fst) snd))
      (primrec_all (allLists_primrec.comp
        (nat_mul.comp (snd.comp fst) (succ.comp (fst.comp fst)))) hz)).to₂
  have hx : Primrec₂ fun (n m : ℕ) =>
      (allLists (m * m)).all fun rel => !(goodRel m rel) ||
        (allLists (m * (n + 1))).all fun val => (forceL m rel (n + 1) val (Fml.ofNat n)).all id :=
    (primrec_all (allLists_primrec.comp (nat_mul.comp snd snd)) hy).to₂
  exact (primrec_all (list_range.comp hB) hx).of_eq fun _ => rfl

/-- **Theoremhood of GL is decidable**, by a computable procedure. -/
theorem provable_computablePred : ComputablePred fun n => Provable (Fml.ofNat n) :=
  ComputablePred.computable_iff.2 ⟨decideGL, decideGL_primrec.to_comp,
    funext fun n => propext (decideGL_iff n).symm⟩

/-- **Theoremhood of GL is λ-decidable**: some λ-term decides, on the code `n`, whether the
formula `Fml.ofNat n` is a theorem of GL (every formula has a code, `Fml.ofNat_toNat`). -/
theorem provable_lambdaDecidable : LambdaDecidable fun n => Provable (Fml.ofNat n) :=
  lambdaDecidable_iff_computablePred.2 provable_computablePred

end ModalGL
