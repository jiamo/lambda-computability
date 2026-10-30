/-
**Compiling partial recursive codes to structured counter programs** — task
`M25-KCM-UNIVERSAL` (round 10, part B3).

The frame convention (`Minsky.Prog.Good`): the block `compile c inp out b` reads the register
`inp`, writes the register `out`, and uses scratch registers `≥ b` only.  Started with `r out = 0`
and every register `≥ b` zero, it has an execution exactly when `c.eval (r inp)` is defined, and
then its final registers are `update r out m` with `m` the value: the input, the scratch
registers and every other register are unchanged.  Both directions of the simulation lemma are
in the `↔`: completeness (`m ∈ c.eval n → execution`) and soundness (`execution → m ∈ c.eval n`,
by determinism of `Exec`).

* `Minsky.Prog.compile` — the compiler, one case per constructor of `Nat.Partrec.Code`;
* `Minsky.Prog.good_compile` — **the simulation lemma**, for all eight constructors.
-/

import Start.MinskyUnpair
import Mathlib.Computability.PartrecCode

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Prog

open Function Nat.Partrec

/-! ### Sequencing lemmas -/

theorem total_iff {p : Prog} {r s r' : ℕ → ℕ} (e : Exec p r s) : Exec p r r' ↔ r' = s :=
  ⟨fun h => h.det e, fun h => h ▸ e⟩

theorem seq_total {p q : Prog} {r s r'' : ℕ → ℕ} (e : Exec p r s) :
    Exec (.seq p q) r r'' ↔ Exec q s r'' :=
  ⟨fun h => by cases h with | seq h₁ h₂ => exact (h₁.det e) ▸ h₂, fun h => .seq e h⟩

theorem seq_part {p q : Prog} {r r'' : ℕ → ℕ} {e : Part ℕ} {U : ℕ → ℕ → ℕ}
    (h : ∀ r', Exec p r r' ↔ ∃ m ∈ e, r' = U m) :
    Exec (.seq p q) r r'' ↔ ∃ m ∈ e, Exec q (U m) r'' := by
  rw [exec_seq_iff]
  constructor
  · rintro ⟨r', h₁, h₂⟩
    obtain ⟨m, hm, rfl⟩ := (h r').1 h₁
    exact ⟨m, hm, h₂⟩
  · rintro ⟨m, hm, h₂⟩
    exact ⟨U m, (h _).2 ⟨m, hm, rfl⟩, h₂⟩

theorem exists_mem_congr {e : Part ℕ} {P Q : ℕ → Prop} (h : ∀ m ∈ e, P m ↔ Q m) :
    (∃ m ∈ e, P m) ↔ ∃ m ∈ e, Q m :=
  ⟨fun ⟨m, hm, hp⟩ => ⟨m, hm, (h m hm).1 hp⟩, fun ⟨m, hm, hq⟩ => ⟨m, hm, (h m hm).2 hq⟩⟩

theorem mem_pairSeq {f g : Part ℕ} {v : ℕ} :
    v ∈ (Nat.pair <$> f <*> g) ↔ ∃ m ∈ f, ∃ m' ∈ g, Nat.pair m m' = v := by
  simp [Seq.seq, Part.mem_bind_iff, Part.mem_map_iff]

theorem exists_mem_pairSeq {f g : Part ℕ} {P : ℕ → Prop} :
    (∃ v ∈ (Nat.pair <$> f <*> g), P v) ↔ ∃ m ∈ f, ∃ m' ∈ g, P (Nat.pair m m') := by
  simp only [mem_pairSeq]
  constructor
  · rintro ⟨v, ⟨m, hm, m', hm', rfl⟩, hp⟩
    exact ⟨m, hm, m', hm', hp⟩
  · rintro ⟨m, hm, m', hm', hp⟩
    exact ⟨_, ⟨m, hm, m', hm', rfl⟩, hp⟩

theorem exists_mem_bind {f : Part ℕ} {g : ℕ → Part ℕ} {P : ℕ → Prop} :
    (∃ v ∈ f >>= g, P v) ↔ ∃ m ∈ f, ∃ v ∈ g m, P v := by
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · rintro ⟨v, ⟨m, hm, hv⟩, hp⟩; exact ⟨m, hm, v, hv, hp⟩
  · rintro ⟨m, hm, v, hv, hp⟩; exact ⟨v, ⟨m, hm, hv⟩, hp⟩

theorem zero_above {r : ℕ → ℕ} {b c k v : ℕ} (hr : ∀ j, b ≤ j → r j = 0) (hk : k < c)
    (hbc : b ≤ c) : ∀ j, c ≤ j → update r k v j = 0 := by
  intro j hj
  rw [update_of_ne (by omega)]
  exact hr j (by omega)

theorem exists_mem_congr' {e e' : Part ℕ} {P Q : ℕ → Prop} (he : e = e')
    (h : ∀ m ∈ e', P m ↔ Q m) : (∃ m ∈ e, P m) ↔ ∃ m ∈ e', Q m :=
  by subst he; exact exists_mem_congr h

theorem exists_mem_pure {v : ℕ} {P : ℕ → Prop} : (∃ m ∈ (pure v : Part ℕ), P m) ↔ P v := by
  simp

/-! ### The frame convention -/

/-- **The frame convention**: `P` computes `f` from `inp` into `out`, with scratch registers
`≥ b`. -/
def Good (P : Prog) (f : ℕ →. ℕ) (inp out b : ℕ) : Prop :=
  ∀ r : ℕ → ℕ, r out = 0 → (∀ j, b ≤ j → r j = 0) →
    ∀ r', Exec P r r' ↔ ∃ m ∈ f (r inp), r' = update r out m

/-! ### The compiler -/

/-- The body of the loop of `prec`: registers `a = b`, counter `b + 1`, `y = b + 2`,
`acc = b + 3`, scratch from `b + 4`. -/
def precBody (cg : Prog) (b : ℕ) : Prog :=
  .seq (pairAdd (b + 2) (b + 3) (b + 4) (b + 6))
    (.seq (pairAdd b (b + 4) (b + 5) (b + 6))
      (.seq (clear (b + 4)) (.seq (clear (b + 3)) (.seq cg (.seq (clear (b + 5)) (.inc (b + 2)))))))

/-- The body of the loop of `rfind'`: registers `a = b`, `m = b + 1`, flag `b + 2`,
`t = b + 3`, `v = b + 4`, scratch from `b + 5`. -/
def rfindBody (cf : Prog) (b : ℕ) : Prog :=
  .seq (pairAdd b (b + 1) (b + 3) (b + 5))
    (.seq cf (.seq (clear (b + 3)) (ifPos (b + 4) (.seq (.inc (b + 1)) (.inc (b + 2))))))

/-- **The compiler.** -/
def compile : Code → ℕ → ℕ → ℕ → Prog
  | .zero, _, out, _ => clear out
  | .succ, inp, out, b => .seq (copy inp out b) (.inc out)
  | .left, inp, out, b => .seq (unpairM inp b (b + 1) (b + 2)) (.seq (addTo b out) (clear (b + 1)))
  | .right, inp, out, b =>
      .seq (unpairM inp b (b + 1) (b + 2)) (.seq (addTo (b + 1) out) (clear b))
  | .pair cf cg, inp, out, b =>
      .seq (compile cf inp b (b + 2)) (.seq (compile cg inp (b + 1) (b + 2))
        (.seq (pairAdd b (b + 1) out (b + 2)) (.seq (clear b) (clear (b + 1)))))
  | .comp cf cg, inp, out, b =>
      .seq (compile cg inp b (b + 1)) (.seq (compile cf b out (b + 1)) (clear b))
  | .prec cf cg, inp, out, b =>
      .seq (unpairM inp b (b + 1) (b + 4)) (.seq (compile cf b (b + 3) (b + 4))
        (.seq (.loop (b + 1) (precBody (compile cg (b + 5) (b + 3) (b + 6)) b))
          (.seq (addTo (b + 3) out) (.seq (clear b) (clear (b + 2))))))
  | .rfind' cf, inp, out, b =>
      .seq (unpairM inp b (b + 1) (b + 5)) (.seq (.inc (b + 2))
        (.seq (.loop (b + 2) (rfindBody (compile cf (b + 3) (b + 4) (b + 5)) b))
          (.seq (addTo (b + 1) out) (clear b))))

/-! ### The simulation lemma, case by case -/

theorem good_zero {inp out b : ℕ} : Good (compile .zero inp out b) (Code.eval .zero) inp out b := by
  intro r hout _ r'
  simp only [compile, Code.eval]
  rw [total_iff (exec_clear out r), show (pure 0 : ℕ →. ℕ) (r inp) = (pure 0 : Part ℕ) from rfl,
    exists_mem_pure]

theorem good_succ {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out) :
    Good (compile .succ inp out b) (Code.eval .succ) inp out b := by
  intro r hout hr r'
  have e := exec_copy hio (by omega) (by omega) r (hr b le_rfl)
  simp only [compile, Code.eval]
  rw [seq_total e]
  have : (↑(Nat.succ) : ℕ →. ℕ) (r inp) = pure (r inp + 1) := rfl
  rw [this, exists_mem_pure, total_iff .inc]
  constructor <;> rintro rfl <;> upd_tac

theorem good_left {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out) :
    Good (compile .left inp out b) (Code.eval .left) inp out b := by
  intro r hout hr r'
  have h0 := hr b le_rfl
  have h1 := hr (b + 1) (by omega)
  have e := exec_unpairM (n := inp) (a := b) (b := b + 1) (s := b + 2) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) r h0 h1 (fun j hj => hr j (by omega))
  simp only [compile, Code.eval]
  rw [seq_total e, seq_total (exec_addTo (by omega) _), total_iff (exec_clear _ _)]
  have : (↑(fun n : ℕ => n.unpair.1) : ℕ →. ℕ) (r inp) = pure (r inp).unpair.1 := rfl
  rw [this, exists_mem_pure]
  constructor <;> rintro rfl <;> upd_tac

theorem good_right {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out) :
    Good (compile .right inp out b) (Code.eval .right) inp out b := by
  intro r hout hr r'
  have h0 := hr b le_rfl
  have h1 := hr (b + 1) (by omega)
  have e := exec_unpairM (n := inp) (a := b) (b := b + 1) (s := b + 2) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) r h0 h1 (fun j hj => hr j (by omega))
  simp only [compile, Code.eval]
  rw [seq_total e, seq_total (exec_addTo (by omega) _), total_iff (exec_clear _ _)]
  have : (↑(fun n : ℕ => n.unpair.2) : ℕ →. ℕ) (r inp) = pure (r inp).unpair.2 := rfl
  rw [this, exists_mem_pure]
  constructor <;> rintro rfl <;> upd_tac

theorem good_pair {cf cg : Code} {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out)
    (hf : Good (compile cf inp b (b + 2)) cf.eval inp b (b + 2))
    (hg : Good (compile cg inp (b + 1) (b + 2)) cg.eval inp (b + 1) (b + 2)) :
    Good (compile (.pair cf cg) inp out b) (Code.eval (.pair cf cg)) inp out b := by
  intro r hout hr r'
  have h0 := hr b le_rfl
  have h1 := hr (b + 1) (by omega)
  simp only [compile]
  rw [seq_part (hf r h0 (fun j hj => hr j (by omega))), Code.eval, exists_mem_pairSeq]
  refine exists_mem_congr fun m _ => ?_
  have hg' := hg (update r b m) (by upd_val) (zero_above hr (by omega) (by omega))
  rw [show update r b m inp = r inp by upd_val] at hg'
  rw [seq_part hg']
  refine exists_mem_congr fun m' _ => ?_
  have hr₂ := zero_above (v := m') (k := b + 1) (zero_above (v := m) hr (show b < b + 2 by omega)
    (by omega)) (show b + 1 < b + 2 by omega) le_rfl
  rw [seq_total (exec_pairAdd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    _ hr₂), seq_total (exec_clear _ _), total_iff (exec_clear _ _)]
  constructor <;> rintro rfl <;> upd_tac

theorem good_comp {cf cg : Code} {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out)
    (hf : Good (compile cf b out (b + 1)) cf.eval b out (b + 1))
    (hg : Good (compile cg inp b (b + 1)) cg.eval inp b (b + 1)) :
    Good (compile (.comp cf cg) inp out b) (Code.eval (.comp cf cg)) inp out b := by
  intro r hout hr r'
  have h0 := hr b le_rfl
  simp only [compile]
  rw [seq_part (hg r h0 (fun j hj => hr j (by omega))), Code.eval]
  refine Iff.trans ?_ (exists_mem_bind (f := cg.eval (r inp)) (g := cf.eval)).symm
  refine exists_mem_congr fun m _ => ?_
  have hf' := hf (update r b m) (by upd_val) (zero_above hr (by omega) (by omega))
  rw [show update r b m b = m by simp] at hf'
  rw [seq_part hf']
  refine exists_mem_congr fun v _ => ?_
  rw [total_iff (exec_clear _ _)]
  constructor <;> rintro rfl <;> upd_tac

/-! ### Loops -/

theorem loop_zero_iff {i : ℕ} {p : Prog} {r r' : ℕ → ℕ} (h : r i = 0) :
    Exec (.loop i p) r r' ↔ r' = r := total_iff (.loop0 h)

theorem loop_succ_iff {i v : ℕ} {p : Prog} {r r' : ℕ → ℕ} (h : r i = v + 1) :
    Exec (.loop i p) r r' ↔ ∃ r₁, Exec p (update r i v) r₁ ∧ Exec (.loop i p) r₁ r' := by
  constructor
  · intro e
    cases e with
    | loop0 h' => omega
    | loopS h' e₁ e₂ =>
      rename_i v'
      have : v' = v := by omega
      subst this
      exact ⟨_, e₁, e₂⟩
  · rintro ⟨r₁, e₁, e₂⟩
    exact .loopS h e₁ e₂

/-! ### Primitive recursion -/

theorem precBody_iff {cgP : Prog} {cg : Code} {b a y i : ℕ}
    (hg : Good cgP cg.eval (b + 5) (b + 3) (b + 6)) {r₀ : ℕ → ℕ} (ha : r₀ b = a)
    (hy : r₀ (b + 2) = y) (hi : r₀ (b + 3) = i) (h4 : r₀ (b + 4) = 0) (h5 : r₀ (b + 5) = 0)
    (hr : ∀ j, b + 6 ≤ j → r₀ j = 0) (r₁ : ℕ → ℕ) :
    Exec (precBody cgP b) r₀ r₁ ↔
      ∃ i₁ ∈ cg.eval (Nat.pair a (Nat.pair y i)), r₁ = update (update r₀ (b + 3) i₁) (b + 2) (y + 1) := by
  unfold precBody
  rw [seq_total (exec_pairAdd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    _ hr)]
  rw [seq_total (exec_pairAdd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    _ (zero_above hr (by omega) le_rfl))]
  rw [seq_total (exec_clear _ _), seq_total (exec_clear _ _)]
  refine (seq_part (hg _ (by upd_val) ?_)).trans (exists_mem_congr' ?_ fun m _ => ?_)
  · intro j hj
    simp only [update_apply]
    split_ifs <;> first | omega | exact hr j hj
  · congr 1
    simp only [update_apply]
    split_ifs <;> first | omega | simp_all
  · rw [seq_total (exec_clear _ _), total_iff .inc]
    constructor <;> rintro rfl <;> upd_tac

theorem exists_reg_part {e : Part ℕ} {U : ℕ → ℕ → ℕ} {P : (ℕ → ℕ) → Prop} :
    (∃ r₁, (∃ m ∈ e, r₁ = U m) ∧ P r₁) ↔ ∃ m ∈ e, P (U m) := by
  constructor
  · rintro ⟨r₁, ⟨m, hm, rfl⟩, hp⟩; exact ⟨m, hm, hp⟩
  · rintro ⟨m, hm, hp⟩; exact ⟨U m, ⟨m, hm, rfl⟩, hp⟩

/-- The iteration of the step of `prec` from `y`, with accumulator `i`, `n` times. -/
def precIter (cg : Code) (a : ℕ) : ℕ → ℕ → ℕ → Part ℕ
  | _, i, 0 => pure i
  | y, i, n + 1 => cg.eval (Nat.pair a (Nat.pair y i)) >>= fun i₁ => precIter cg a (y + 1) i₁ n

theorem eval_prec_bind (cf cg : Code) (a : ℕ) : ∀ n k : ℕ,
    Code.eval (.prec cf cg) (Nat.pair a n) >>= (fun i => precIter cg a n i k) =
      cf.eval a >>= fun i => precIter cg a 0 i (n + k)
  | 0, k => by rw [Code.eval_prec_zero, Nat.zero_add]
  | n + 1, k => by
    rw [Code.eval_prec_succ, bind_assoc, show n + 1 + k = n + (k + 1) by omega,
      ← eval_prec_bind cf cg a n (k + 1)]
    rfl

theorem eval_prec_eq (cf cg : Code) (a n : ℕ) :
    Code.eval (.prec cf cg) (Nat.pair a n) = cf.eval a >>= fun i => precIter cg a 0 i n := by
  have := eval_prec_bind cf cg a n 0
  simp only [Nat.add_zero] at this
  rw [← this]
  exact (bind_pure _).symm

theorem precLoop_iff {cgP : Prog} {cg : Code} {b a : ℕ}
    (hg : Good cgP cg.eval (b + 5) (b + 3) (b + 6)) : ∀ (n y i : ℕ) (r : ℕ → ℕ),
    r (b + 1) = n → r b = a → r (b + 2) = y → r (b + 3) = i → r (b + 4) = 0 → r (b + 5) = 0 →
    (∀ j, b + 6 ≤ j → r j = 0) → ∀ r',
    Exec (.loop (b + 1) (precBody cgP b)) r r' ↔
      ∃ i' ∈ precIter cg a y i n,
        r' = update (update (update r (b + 1) 0) (b + 2) (y + n)) (b + 3) i'
  | 0, y, i, r, hn, ha, hy, hi, h4, h5, hr, r' => by
    rw [loop_zero_iff hn, precIter, exists_mem_pure]
    constructor <;> rintro rfl <;> upd_tac
  | n + 1, y, i, r, hn, ha, hy, hi, h4, h5, hr, r' => by
    rw [loop_succ_iff hn]
    simp only [precBody_iff hg (r₀ := update r (b + 1) n) (a := a) (y := y) (i := i)
      (by upd_val) (by upd_val) (by upd_val) (by upd_val) (by upd_val)
      (zero_above hr (by omega) (by omega)), exists_reg_part, precIter]
    refine Iff.trans ?_ (exists_mem_bind (f := cg.eval (Nat.pair a (Nat.pair y i)))).symm
    refine exists_mem_congr fun i₁ _ => ?_
    rw [precLoop_iff hg n (y + 1) i₁ _ (by upd_val) (by upd_val) (by upd_val) (by upd_val)
      (by upd_val) (by upd_val) (zero_above (zero_above (zero_above hr (by omega) le_rfl)
        (by omega) le_rfl) (by omega) le_rfl)]
    refine exists_mem_congr fun i' _ => ?_
    rw [show y + (n + 1) = y + 1 + n by omega]
    constructor <;> rintro rfl <;> upd_tac

theorem good_prec {cf cg : Code} {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out)
    (hf : Good (compile cf b (b + 3) (b + 4)) cf.eval b (b + 3) (b + 4))
    (hg : Good (compile cg (b + 5) (b + 3) (b + 6)) cg.eval (b + 5) (b + 3) (b + 6)) :
    Good (compile (.prec cf cg) inp out b) (Code.eval (.prec cf cg)) inp out b := by
  intro r hout hr r'
  have h0 := hr b le_rfl
  have h1 := hr (b + 1) (by omega)
  have h2 := hr (b + 2) (by omega)
  have h3 := hr (b + 3) (by omega)
  have h4 := hr (b + 4) (by omega)
  have h5 := hr (b + 5) (by omega)
  have hp : Code.eval (.prec cf cg) (r inp) =
      cf.eval (r inp).unpair.1 >>= fun i => precIter cg (r inp).unpair.1 0 i (r inp).unpair.2 := by
    conv_lhs => rw [← Nat.pair_unpair (r inp)]
    exact eval_prec_eq cf cg _ _
  rw [hp]
  refine Iff.trans ?_ (exists_mem_bind (f := cf.eval (r inp).unpair.1)).symm
  simp only [compile]
  rw [seq_total (exec_unpairM (n := inp) (a := b) (b := b + 1) (s := b + 4) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) r h0 h1 (fun j hj => hr j (by omega)))]
  refine (seq_part (hf _ (by upd_val) ?_)).trans (exists_mem_congr' ?_ fun i _ => ?_)
  · intro j hj
    simp only [update_apply]
    split_ifs <;> first | omega | exact hr j (by omega)
  · simp
  · refine (seq_part (precLoop_iff (a := (r inp).unpair.1) hg (r inp).unpair.2 0 i _ ?_ ?_ ?_ ?_
      ?_ ?_ ?_)).trans (exists_mem_congr fun i' _ => ?_)
    · upd_val
    · upd_val
    · upd_val
    · upd_val
    · upd_val
    · upd_val
    · intro j hj
      simp only [update_apply]
      split_ifs <;> first | omega | exact hr j (by omega)
    · rw [seq_total (exec_addTo (by omega) _), seq_total (exec_clear _ _),
        total_iff (exec_clear _ _)]
      constructor <;> rintro rfl <;> upd_tac

/-! ### Unbounded search -/

theorem rfindBody_iff {cfP : Prog} {cf : Code} {b a m : ℕ}
    (hf : Good cfP cf.eval (b + 3) (b + 4) (b + 5)) {r₀ : ℕ → ℕ} (ha : r₀ b = a)
    (hm : r₀ (b + 1) = m) (h2 : r₀ (b + 2) = 0) (h3 : r₀ (b + 3) = 0) (h4 : r₀ (b + 4) = 0)
    (hr : ∀ j, b + 5 ≤ j → r₀ j = 0) (r₁ : ℕ → ℕ) :
    Exec (rfindBody cfP b) r₀ r₁ ↔
      ∃ v ∈ cf.eval (Nat.pair a m),
        r₁ = if v = 0 then r₀ else update (update r₀ (b + 1) (m + 1)) (b + 2) 1 := by
  unfold rfindBody
  rw [seq_total (exec_pairAdd (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    _ hr)]
  refine (seq_part (hf _ (by upd_val) ?_)).trans (exists_mem_congr' ?_ fun v _ => ?_)
  · intro j hj
    simp only [update_apply]
    split_ifs <;> first | omega | exact hr j hj
  · congr 1
    simp only [update_apply]
    split_ifs <;> first | omega | simp_all
  · rw [seq_total (exec_clear _ _)]
    by_cases hv : v = 0
    · rw [ite_eq_left hv, total_iff (exec_ifPos_zero (by simp [hv]))]
      constructor <;> rintro rfl <;> upd_tac
    · rw [ite_eq_right hv, total_iff (exec_ifPos_pos (by simp [hv]) (.seq .inc .inc) (by upd_val))]
      constructor <;> rintro rfl <;> upd_tac

/-- The search condition at `j`: the value of `cf` at `pair a (j + m)` is defined and nonzero. -/
def SearchPos (cf : Code) (a m j : ℕ) : Prop := ∃ v ∈ cf.eval (Nat.pair a (j + m)), v ≠ 0

theorem rfindLoop_sound {cfP : Prog} {cf : Code} {b a : ℕ}
    (hf : Good cfP cf.eval (b + 3) (b + 4) (b + 5)) {P : Prog} {r r' : ℕ → ℕ}
    (h : Exec P r r') (hP : P = .loop (b + 2) (rfindBody cfP b)) : ∀ m : ℕ,
    r b = a → r (b + 1) = m → r (b + 2) = 1 → r (b + 3) = 0 → r (b + 4) = 0 →
    (∀ j, b + 5 ≤ j → r j = 0) →
    ∃ k, (∀ j < k, SearchPos cf a m j) ∧ 0 ∈ cf.eval (Nat.pair a (k + m)) ∧
      r' = update (update r (b + 1) (k + m)) (b + 2) 0 := by
  induction h with
  | inc => cases hP
  | dec => cases hP
  | seq => cases hP
  | loop0 h0 =>
    intro m _ _ h2
    cases hP
    omega
  | @loopS i p r₀ r₁ r₂ v hv e₁ e₂ _ ih₂ =>
    intro m ha hm h2 h3 h4 hr
    cases hP
    have hv0 : v = 0 := by omega
    subst hv0
    obtain ⟨w, hw, rfl⟩ := (rfindBody_iff hf (r₀ := update r₀ (b + 2) 0) (by upd_val)
      (by upd_val) (by upd_val) (by upd_val) (by upd_val) (zero_above hr (by omega) (by omega))
      _).1 e₁
    by_cases hw0 : w = 0
    · rw [ite_eq_left hw0] at e₂
      refine ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j), by simpa [hw0] using hw, ?_⟩
      rw [(loop_zero_iff (by upd_val)).1 e₂]
      subst hm
      upd_tac
    · simp only [ite_eq_right hw0] at e₂ ih₂
      obtain ⟨k, hk, hk0, rfl⟩ := ih₂ trivial (m + 1) (by upd_val) (by upd_val) (by upd_val)
        (by upd_val) (by upd_val)
        (zero_above (c := b + 5) (zero_above (c := b + 5) (zero_above (c := b + 5) hr (by omega)
          (by omega)) (by omega) (by omega))
          (by omega) (by omega))
      refine ⟨k + 1, fun j hj => ?_, by rw [show k + 1 + m = k + (m + 1) by omega]; exact hk0, ?_⟩
      · rcases j with _ | j
        · exact ⟨w, by simpa [hm] using hw, hw0⟩
        · have := hk j (by omega)
          rw [SearchPos, show j + 1 + m = j + (m + 1) by omega]
          exact this
      · upd_tac

theorem rfindLoop_complete {cfP : Prog} {cf : Code} {b a : ℕ}
    (hf : Good cfP cf.eval (b + 3) (b + 4) (b + 5)) : ∀ (k m : ℕ) (r : ℕ → ℕ),
    r b = a → r (b + 1) = m → r (b + 2) = 1 → r (b + 3) = 0 → r (b + 4) = 0 →
    (∀ j, b + 5 ≤ j → r j = 0) → (∀ j < k, SearchPos cf a m j) →
    0 ∈ cf.eval (Nat.pair a (k + m)) →
    Exec (.loop (b + 2) (rfindBody cfP b)) r (update (update r (b + 1) (k + m)) (b + 2) 0)
  | 0, m, r, ha, hm, h2, h3, h4, hr, _, h0 => by
    rw [loop_succ_iff (v := 0) h2]
    refine ⟨update r (b + 2) 0, (rfindBody_iff hf (by upd_val) (by upd_val) (by upd_val)
      (by upd_val) (by upd_val) (zero_above hr (by omega) (by omega)) _).2
      ⟨0, by simpa [hm] using h0, by simp⟩, ?_⟩
    refine (Exec.loop0 (by simp)).congr rfl ?_
    subst hm
    upd_tac
  | k + 1, m, r, ha, hm, h2, h3, h4, hr, hk, h0 => by
    rw [loop_succ_iff (v := 0) h2]
    obtain ⟨w, hw, hw0⟩ := hk 0 (by omega)
    refine ⟨_, (rfindBody_iff hf (r₀ := update r (b + 2) 0) (by upd_val) (by upd_val)
      (by upd_val) (by upd_val) (by upd_val) (zero_above hr (by omega) (by omega)) _).2
      ⟨w, by simpa [hm] using hw, rfl⟩, ?_⟩
    rw [ite_eq_right hw0]
    refine (rfindLoop_complete hf k (m + 1) _ (by upd_val) (by upd_val) (by upd_val)
      (by upd_val) (by upd_val)
      (zero_above (c := b + 5) (zero_above (c := b + 5) (zero_above (c := b + 5) hr (by omega)
          (by omega)) (by omega) (by omega))
        (by omega) (by omega))
      (fun j hj => by
        have := hk (j + 1) (by omega)
        rw [SearchPos, show j + 1 + m = j + (m + 1) by omega] at this
        exact this)
      (by rw [show k + (m + 1) = k + 1 + m by omega]; exact h0)).congr rfl ?_
    rw [show k + (m + 1) = k + 1 + m by omega]
    upd_tac

theorem rfindLoop_iff {cfP : Prog} {cf : Code} {b a m : ℕ}
    (hf : Good cfP cf.eval (b + 3) (b + 4) (b + 5)) {r : ℕ → ℕ} (ha : r b = a)
    (hm : r (b + 1) = m) (h2 : r (b + 2) = 1) (h3 : r (b + 3) = 0) (h4 : r (b + 4) = 0)
    (hr : ∀ j, b + 5 ≤ j → r j = 0) (r' : ℕ → ℕ) :
    Exec (.loop (b + 2) (rfindBody cfP b)) r r' ↔
      ∃ k, (∀ j < k, SearchPos cf a m j) ∧ 0 ∈ cf.eval (Nat.pair a (k + m)) ∧
        r' = update (update r (b + 1) (k + m)) (b + 2) 0 := by
  constructor
  · intro h
    exact rfindLoop_sound hf h rfl m ha hm h2 h3 h4 hr
  · rintro ⟨k, hk, hk0, rfl⟩
    exact rfindLoop_complete hf k m r ha hm h2 h3 h4 hr hk hk0

theorem mem_eval_rfind' (cf : Code) (a m w : ℕ) :
    w ∈ Code.eval (.rfind' cf) (Nat.pair a m) ↔
      ∃ k, (∀ j < k, SearchPos cf a m j) ∧ 0 ∈ cf.eval (Nat.pair a (k + m)) ∧ w = k + m := by
  simp only [Code.eval, Nat.unpaired, Nat.unpair_pair, Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨h1, h2⟩ := Nat.mem_rfind.1 hk
    obtain ⟨x, hx, hx0⟩ := (Part.mem_map_iff _).1 h1
    refine ⟨k, fun j hj => ?_, by simpa using (show x = 0 by simpa using hx0) ▸ hx, rfl⟩
    obtain ⟨v, hv, hv0⟩ := (Part.mem_map_iff _).1 (h2 hj)
    exact ⟨v, hv, by simpa using hv0⟩
  · rintro ⟨k, h2, h1, rfl⟩
    refine ⟨k, Nat.mem_rfind.2 ⟨?_, fun {j} hj => ?_⟩, rfl⟩
    · exact (Part.mem_map_iff _).2 ⟨0, h1, by simp⟩
    · obtain ⟨v, hv, hv0⟩ := h2 j hj
      exact (Part.mem_map_iff _).2 ⟨v, hv, by simp [hv0]⟩

theorem good_rfind' {cf : Code} {inp out b : ℕ} (hi : inp < b) (ho : out < b) (hio : inp ≠ out)
    (hf : Good (compile cf (b + 3) (b + 4) (b + 5)) cf.eval (b + 3) (b + 4) (b + 5)) :
    Good (compile (.rfind' cf) inp out b) (Code.eval (.rfind' cf)) inp out b := by
  intro r hout hr r'
  have h0 := hr b le_rfl
  have h1 := hr (b + 1) (by omega)
  have h2 := hr (b + 2) (by omega)
  have h3 := hr (b + 3) (by omega)
  have h4 := hr (b + 4) (by omega)
  have hmem : ∀ w, w ∈ Code.eval (.rfind' cf) (r inp) ↔
      ∃ k, (∀ j < k, SearchPos cf (r inp).unpair.1 (r inp).unpair.2 j) ∧
        0 ∈ cf.eval (Nat.pair (r inp).unpair.1 (k + (r inp).unpair.2)) ∧
        w = k + (r inp).unpair.2 := by
    intro w
    conv_lhs => rw [← Nat.pair_unpair (r inp)]
    exact mem_eval_rfind' cf _ _ w
  simp only [compile]
  rw [seq_total (exec_unpairM (n := inp) (a := b) (b := b + 1) (s := b + 5) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) r h0 h1 (fun j hj => hr j (by omega))),
    seq_total .inc, exec_seq_iff]
  constructor
  · rintro ⟨R, hR, hrest⟩
    obtain ⟨k, hk, hk0, rfl⟩ := (rfindLoop_iff (a := (r inp).unpair.1) (m := (r inp).unpair.2) hf (by upd_val) (by upd_val) (by upd_val)
      (by upd_val) (by upd_val) (by
        intro j hj; simp only [update_apply]; split_ifs <;> first | omega | exact hr j (by omega))
      R).1 hR
    rw [seq_total (exec_addTo (by omega) _), total_iff (exec_clear _ _)] at hrest
    refine ⟨k + (r inp).unpair.2, (hmem _).2 ⟨k, hk, hk0, rfl⟩, ?_⟩
    subst hrest
    upd_tac
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hk0, rfl⟩ := (hmem w).1 hw
    refine ⟨_, (rfindLoop_iff (a := (r inp).unpair.1) (m := (r inp).unpair.2) hf (by upd_val) (by upd_val) (by upd_val)
      (by upd_val) (by upd_val) (by
        intro j hj; simp only [update_apply]; split_ifs <;> first | omega | exact hr j (by omega))
      _).2 ⟨k, hk, hk0, rfl⟩, ?_⟩
    rw [seq_total (exec_addTo (by omega) _), total_iff (exec_clear _ _)]
    upd_tac

/-! ### The simulation lemma -/

/-- **The simulation lemma** for the compiler, all eight constructors: under the frame
convention, the block `compile c inp out b` has an execution from `r` exactly when
`c.eval (r inp)` is defined, and its final registers are then `update r out m` with `m` the
value. -/
theorem good_compile : ∀ (c : Code) {inp out b : ℕ}, inp < b → out < b → inp ≠ out →
    Good (compile c inp out b) c.eval inp out b
  | .zero, _, _, _, _, _, _ => good_zero
  | .succ, _, _, _, hi, ho, hio => good_succ hi ho hio
  | .left, _, _, _, hi, ho, hio => good_left hi ho hio
  | .right, _, _, _, hi, ho, hio => good_right hi ho hio
  | .pair cf cg, _, _, _, hi, ho, hio =>
      good_pair hi ho hio (good_compile cf (by omega) (by omega) (by omega))
        (good_compile cg (by omega) (by omega) (by omega))
  | .comp cf cg, _, _, _, hi, ho, hio =>
      good_comp hi ho hio (good_compile cf (by omega) (by omega) (by omega))
        (good_compile cg (by omega) (by omega) (by omega))
  | .prec cf cg, _, _, _, hi, ho, hio =>
      good_prec hi ho hio (good_compile cf (by omega) (by omega) (by omega))
        (good_compile cg (by omega) (by omega) (by omega))
  | .rfind' cf, _, _, _, hi, ho, hio =>
      good_rfind' hi ho hio (good_compile cf (by omega) (by omega) (by omega))

end Prog

end Minsky
