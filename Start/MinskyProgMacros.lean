/-
**Macros for structured counter programs** — task `M25-KCM-UNIVERSAL` (round 10, part B1).

All macros are structured programs (`Start/MinskyProg.lean`), with an exact specification of
their execution as an update of the registers; scratch registers are zero before and after.

* `clear`, `addTo`, `copy`, `mulAdd`, `ifPos`, `ltFlag` (the comparison by truncated
  subtraction);
* `ite` — branching on a flag;
* `pairAdd` — `r k += Nat.pair (r x) (r y)`.

The unpairing macro is in `Start/MinskyUnpair.lean`.
-/

import Start.MinskyProg

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Minsky

namespace Prog

open Function

/-- Proves an equality of register files built by `Function.update`, pointwise. -/
macro "upd_tac" : tactic =>
  `(tactic| (funext x; simp only [Function.update_apply]; split_ifs <;> subst_vars <;>
    first | rfl | omega | ring1 | (simp_all; done) | (simp_all <;> omega) | (simp_all <;> ring1)))

/-- Evaluates a register of a register file built by `Function.update`. -/
macro "upd_val" : tactic =>
  `(tactic| ((try simp only [Function.update_apply]) <;> (try split_ifs) <;> omega))

theorem Exec.congr {p : Prog} {r r' s s' : ℕ → ℕ} (h : Exec p r r') (hs : r = s)
    (hs' : r' = s') : Exec p s s' := by subst hs hs'; exact h

theorem exec_seq_iff {p q : Prog} {r r'' : ℕ → ℕ} :
    Exec (.seq p q) r r'' ↔ ∃ r', Exec p r r' ∧ Exec q r' r'' := by
  constructor
  · intro h; cases h with | seq h₁ h₂ => exact ⟨_, h₁, h₂⟩
  · rintro ⟨r', h₁, h₂⟩; exact .seq h₁ h₂

/-- A total program with a functional specification. -/
def Computes (p : Prog) (F : (ℕ → ℕ) → (ℕ → ℕ)) (P : (ℕ → ℕ) → Prop) : Prop :=
  ∀ r, P r → Exec p r (F r)

theorem Computes.iff {p : Prog} {F : (ℕ → ℕ) → (ℕ → ℕ)} {P : (ℕ → ℕ) → Prop}
    (h : Computes p F P) {r r' : ℕ → ℕ} (hr : P r) : Exec p r r' ↔ r' = F r :=
  ⟨fun h' => h'.det (h r hr), fun e => e ▸ h r hr⟩

/-! ### Clearing, adding, copying -/

/-- `r i := 0`. -/
def clear (i : ℕ) : Prog := .loop i (.dec i)

theorem exec_clear (i : ℕ) : ∀ r : ℕ → ℕ, Exec (clear i) r (update r i 0) := by
  intro r
  induction hn : r i using Nat.strong_induction_on generalizing r with
  | _ n ih =>
    rcases n with _ | v
    · exact (Exec.loop0 hn).congr rfl (by upd_tac)
    · refine .loopS hn .dec ?_
      exact (ih (v - 1) (by omega) (update r i (v - 1)) (by simp)).congr
        (by upd_tac) (by upd_tac)

/-- `r j += r i; r i := 0`. -/
def addTo (i j : ℕ) : Prog := .loop i (.inc j)

theorem exec_addTo {i j : ℕ} (hij : i ≠ j) : ∀ r : ℕ → ℕ,
    Exec (addTo i j) r (update (update r j (r j + r i)) i 0) := by
  intro r
  induction hn : r i generalizing r with
  | zero => exact (Exec.loop0 hn).congr rfl (by upd_tac)
  | succ v ih =>
      refine .loopS hn .inc ?_
      exact (ih _ (by simp [hij])).congr rfl (by clear ih; upd_tac)

/-- `r j += r i` through the scratch register `t` (`r t = 0` before and after). -/
def copy (i j t : ℕ) : Prog := .seq (.loop i (.seq (.inc j) (.inc t))) (addTo t i)

theorem exec_loop_add2 {i j t : ℕ} (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t) :
    ∀ r : ℕ → ℕ, Exec (.loop i (.seq (.inc j) (.inc t))) r
      (update (update (update r j (r j + r i)) t (r t + r i)) i 0) := by
  intro r
  induction hn : r i generalizing r with
  | zero => exact (Exec.loop0 hn).congr rfl (by upd_tac)
  | succ v ih =>
      refine .loopS hn (.seq .inc .inc) ?_
      exact (ih _ (by simp [hij, hit])).congr rfl (by clear ih; upd_tac)

theorem exec_copy {i j t : ℕ} (hij : i ≠ j) (hit : i ≠ t) (hjt : j ≠ t) (r : ℕ → ℕ)
    (ht : r t = 0) : Exec (copy i j t) r (update r j (r j + r i)) :=
  .seq (exec_loop_add2 hij hit hjt r) ((exec_addTo (Ne.symm hit) _).congr rfl (by upd_tac))

/-! ### Multiplication -/

/-- `r k += r a * r b` through the scratch registers `s t`. -/
def mulAdd (a b k s t : ℕ) : Prog := .seq (copy a s t) (.loop s (copy b k t))

theorem exec_mulLoop {b k s t : ℕ} (hbk : b ≠ k) (hbs : b ≠ s) (hbt : b ≠ t) (hks : k ≠ s)
    (hkt : k ≠ t) (hst : s ≠ t) : ∀ r : ℕ → ℕ, r t = 0 →
    Exec (.loop s (copy b k t)) r (update (update r k (r k + r s * r b)) s 0) := by
  intro r ht
  induction hn : r s generalizing r with
  | zero => exact (Exec.loop0 hn).congr rfl (by upd_tac)
  | succ v ih =>
      refine .loopS hn (exec_copy hbk hbt hkt _ (by simp [Ne.symm hst, ht])) ?_
      exact (ih _ (by simp [Ne.symm hkt, Ne.symm hst, ht]) (by simp [Ne.symm hks])).congr rfl
        (by clear ih; upd_tac)

theorem exec_mulAdd {a b k s t : ℕ} (hak : a ≠ k) (has : a ≠ s) (hat : a ≠ t)
    (hbk : b ≠ k) (hbs : b ≠ s) (hbt : b ≠ t) (hks : k ≠ s) (hkt : k ≠ t) (hst : s ≠ t)
    (r : ℕ → ℕ) (hs : r s = 0) (ht : r t = 0) :
    Exec (mulAdd a b k s t) r (update r k (r k + r a * r b)) :=
  .seq (exec_copy has hat hst r ht)
    ((exec_mulLoop hbk hbs hbt hks hkt hst _ (by simp [Ne.symm hst, ht])).congr rfl
      (by upd_tac))

/-! ### Conditionals and comparison -/

/-- `if r t ≠ 0 then (r t := 0; p)`. -/
def ifPos (t : ℕ) (p : Prog) : Prog := .loop t (.seq (clear t) p)

theorem exec_ifPos_zero {t : ℕ} {p : Prog} {r : ℕ → ℕ} (h : r t = 0) :
    Exec (ifPos t p) r r := .loop0 h

theorem exec_ifPos_pos {t : ℕ} {p : Prog} {r r' : ℕ → ℕ} (h : r t ≠ 0)
    (hp : Exec p (update r t 0) r') (hp' : r' t = 0) : Exec (ifPos t p) r r' := by
  obtain ⟨v, hv⟩ := Nat.exists_eq_succ_of_ne_zero h
  exact .loopS hv (.seq (exec_clear t _) (hp.congr (by simp) rfl)) (.loop0 hp')

/-- `r j -= r i` (truncated), `r i := 0`. -/
theorem exec_subLoop {i j : ℕ} (hij : i ≠ j) : ∀ r : ℕ → ℕ,
    Exec (.loop i (.dec j)) r (update (update r j (r j - r i)) i 0) := by
  intro r
  induction hn : r i generalizing r with
  | zero => exact (Exec.loop0 hn).congr rfl (by upd_tac)
  | succ v ih =>
      refine .loopS hn .dec ?_
      exact (ih _ (by simp [hij])).congr rfl (by clear ih; upd_tac)

/-- `r f += [r a < r b]`, through the scratch registers `s₁ s₂ t`. -/
def ltFlag (a b f s₁ s₂ t : ℕ) : Prog :=
  .seq (copy b s₁ t) (.seq (copy a s₂ t) (.seq (.loop s₂ (.dec s₁)) (ifPos s₁ (.inc f))))

theorem exec_ltFlag {a b f s₁ s₂ t : ℕ} (hnd : [a, b, f, s₁, s₂, t].Nodup) (r : ℕ → ℕ)
    (h₁ : r s₁ = 0) (h₂ : r s₂ = 0) (ht : r t = 0) :
    Exec (ltFlag a b f s₁ s₂ t) r (update r f (r f + if r a < r b then 1 else 0)) := by
  have hab : a ≠ b := by intro h; simp [h] at hnd
  have haf : a ≠ f := by intro h; simp [h] at hnd
  have has₁ : a ≠ s₁ := by intro h; simp [h] at hnd
  have has₂ : a ≠ s₂ := by intro h; simp [h] at hnd
  have hat : a ≠ t := by intro h; simp [h] at hnd
  have hbf : b ≠ f := by intro h; simp [h] at hnd
  have hbs₁ : b ≠ s₁ := by intro h; simp [h] at hnd
  have hbs₂ : b ≠ s₂ := by intro h; simp [h] at hnd
  have hbt : b ≠ t := by intro h; simp [h] at hnd
  have hfs₁ : f ≠ s₁ := by intro h; simp [h] at hnd
  have hfs₂ : f ≠ s₂ := by intro h; simp [h] at hnd
  have hft : f ≠ t := by intro h; simp [h] at hnd
  have hs₁s₂ : s₁ ≠ s₂ := by intro h; simp [h] at hnd
  have hs₁t : s₁ ≠ t := by intro h; simp [h] at hnd
  have hs₂t : s₂ ≠ t := by intro h; simp [h] at hnd
  refine .seq (exec_copy hbs₁ hbt hs₁t r ht) (.seq (exec_copy has₂ hat hs₂t _
    (by simp [Ne.symm hs₁t, ht])) (.seq (exec_subLoop (Ne.symm hs₁s₂) _) ?_))
  have hv : update (update (update (update r s₁ (r s₁ + r b)) s₂
      (update r s₁ (r s₁ + r b) s₂ + update r s₁ (r s₁ + r b) a)) s₁
      (update (update r s₁ (r s₁ + r b)) s₂
        (update r s₁ (r s₁ + r b) s₂ + update r s₁ (r s₁ + r b) a) s₁ -
       update (update r s₁ (r s₁ + r b)) s₂
        (update r s₁ (r s₁ + r b) s₂ + update r s₁ (r s₁ + r b) a) s₂)) s₂ 0 s₁ =
      r b - r a := by
    have := Ne.symm hs₁s₂
    simp_all
  by_cases hlt : r a < r b
  · refine (exec_ifPos_pos (by rw [hv]; omega) .inc (by simp [Ne.symm hfs₁])).congr rfl ?_
    funext x
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  · refine (exec_ifPos_zero (by rw [hv]; omega)).congr rfl ?_
    funext x
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all


/-! ### Branching on a flag -/

/-- `if r f ≠ 0 then (r f := 0; p) else q`, through the scratch register `g`. -/
def ite (f g : ℕ) (p q : Prog) : Prog :=
  .seq (.inc g) (.seq (ifPos f (.seq (.dec g) p)) (ifPos g q))

theorem exec_ite_pos {f g : ℕ} {p q : Prog} {r r' : ℕ → ℕ} (hfg : f ≠ g) (hf : r f ≠ 0)
    (hg : r g = 0) (hp : Exec p (update r f 0) r') (hf' : r' f = 0) (hg' : r' g = 0) :
    Exec (ite f g p q) r r' := by
  refine .seq .inc (.seq (exec_ifPos_pos (by simp [hfg, hf]) (.seq .dec ?_) hf')
    (exec_ifPos_zero hg'))
  exact hp.congr (by upd_tac) rfl

theorem exec_ite_neg {f g : ℕ} {p q : Prog} {r r' : ℕ → ℕ} (hfg : f ≠ g) (hf : r f = 0)
    (hg : r g = 0) (hq : Exec q r r') (hg' : r' g = 0) : Exec (ite f g p q) r r' := by
  refine .seq .inc (.seq (exec_ifPos_zero (by simp [hfg, hf]))
    (exec_ifPos_pos (by simp) (hq.congr (by upd_tac) rfl) hg'))

/-! ### Pairing -/

/-- `r k += Nat.pair (r x) (r y)`, with scratch registers from `b`. -/
def pairAdd (x y k b : ℕ) : Prog :=
  .seq (ltFlag x y b (b + 2) (b + 3) (b + 4))
    (ite b (b + 1) (.seq (mulAdd y y k (b + 5) (b + 4)) (copy x k (b + 4)))
      (.seq (mulAdd x x k (b + 5) (b + 4)) (.seq (copy x k (b + 4)) (copy y k (b + 4)))))

theorem exec_pairAdd {x y k b : ℕ} (hxy : x ≠ y) (hxk : x ≠ k) (hyk : y ≠ k) (hx : x < b)
    (hy : y < b) (hk : k < b) (r : ℕ → ℕ) (hr : ∀ j, b ≤ j → r j = 0) :
    Exec (pairAdd x y k b) r (update r k (r k + Nat.pair (r x) (r y))) := by
  have h0 := hr b le_rfl
  have h1 := hr (b + 1) (by omega)
  have h2 := hr (b + 2) (by omega)
  have h3 := hr (b + 3) (by omega)
  have h4 := hr (b + 4) (by omega)
  have h5 := hr (b + 5) (by omega)
  have hlt := exec_ltFlag (a := x) (b := y) (f := b) (s₁ := b + 2) (s₂ := b + 3) (t := b + 4)
    (by simp; omega) r h2 h3 h4
  refine .seq hlt ?_
  by_cases hxy' : r x < r y
  · rw [if_pos hxy']
    have e₁ := exec_mulAdd (a := y) (b := y) (k := k) (s := b + 5) (t := b + 4)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) r h5 h4
    have e₂ := exec_copy (i := x) (j := k) (t := b + 4) hxk (by omega) (by omega)
      (update r k (r k + r y * r y)) (by upd_val)
    refine exec_ite_pos (by omega) (by simp) (by upd_val)
      ((Exec.seq e₁ e₂).congr (by upd_tac) ?_) (by upd_val) (by upd_val)
    rw [Nat.pair, if_pos hxy']
    funext z
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> omega
  · rw [if_neg hxy']
    have e₁ := exec_mulAdd (a := x) (b := x) (k := k) (s := b + 5) (t := b + 4)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) r h5 h4
    have e₂ := exec_copy (i := x) (j := k) (t := b + 4) hxk (by omega) (by omega)
      (update r k (r k + r x * r x)) (by upd_val)
    have e₃ := exec_copy (i := y) (j := k) (t := b + 4) hyk (by omega) (by omega)
      (update (update r k (r k + r x * r x)) k
        (update r k (r k + r x * r x) k + update r k (r k + r x * r x) x)) (by upd_val)
    refine exec_ite_neg (by omega) (by simp [h0]) (by upd_val)
      ((Exec.seq e₁ (Exec.seq e₂ e₃)).congr (by upd_tac) ?_) (by upd_val)
    rw [Nat.pair, if_neg hxy']
    funext z
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> omega

end Prog

end Minsky
