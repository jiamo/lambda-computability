/-
**Chaitin's incompleteness theorem**: no sound, recursively enumerable proof system establishes
more than finitely many lower bounds on Kolmogorov complexity.

`Start/Kolmogorov.lean` shows that `kolm` is not computable and that incompressible numbers exist,
and `Start/KolmogorovBinary.lean` that `kolm n = O(log n)`.  Putting the two together gives
Chaitin's form of the incompleteness phenomenon: think of a formal system as a recursively
enumerable set of assertions `kolm x > n`; if all of its assertions are true, then the thresholds
`n` occurring in them are bounded, so from some constant on *no* true assertion `kolm x > c` is
provable, although such assertions are true for all but finitely many `x`.

Main results:

* `Lambda.Post.exists_test_of_rePred` (proved in `Start/PostSimple.lean`) — the converse of
  `Lambda.Post.rePred_of_exists_test`: an r.e. predicate is "some stage of a primitive recursive
  test succeeds";
* `Lambda.exists_partrec_select` — an r.e. relation admits a partial recursive *selection*
  function: it searches for a witness and finds one whenever one exists;
* `Lambda.exists_const_kolm_apply_le_of_partrec` — a partial recursive function raises complexity
  by at most an additive constant, `kolm (V n) ≤ kolm n + c`;
* `Lambda.chaitin_incompleteness` — **Chaitin's theorem**: for a sound r.e. system of lower
  bounds, the thresholds are bounded;
* `Lambda.exists_true_unprovable_kolm_lower_bound` — hence there is a threshold `c` at which the
  system proves nothing, while `kolm x > c` is true for some `x`.
-/

import Start.KolmogorovBinary
import Start.PostSimple

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

open Nat.Partrec (Code)
open Encodable Denumerable

/-- An r.e. relation admits a partial recursive **selection** function: `sel n` searches for an
`x` with `S x n`, returns only such witnesses, and halts whenever one exists. -/
theorem exists_partrec_select {S : ℕ → ℕ → Prop} (hre : REPred fun q : ℕ × ℕ => S q.1 q.2) :
    ∃ sel : ℕ →. ℕ, Partrec sel ∧ (∀ n x, x ∈ sel n → S x n) ∧
      (∀ n, (∃ x, S x n) → (sel n).Dom) := by
  have hpair : Computable fun p : ℕ => ((Nat.unpair p).1, (Nat.unpair p).2) :=
    (Primrec.fst.comp Primrec.unpair).to_comp.pair (Primrec.snd.comp Primrec.unpair).to_comp
  have hre' : REPred fun p : ℕ => S (Nat.unpair p).1 (Nat.unpair p).2 := hre.comp hpair
  obtain ⟨g, hgprim, hg⟩ := Post.exists_test_of_rePred hre'
  refine ⟨fun n => (Nat.rfind fun k =>
      Part.some (g (Nat.pair (Nat.unpair k).1 n) (Nat.unpair k).2)).map fun k => (Nat.unpair k).1,
    ?_, ?_, ?_⟩
  · have hprim : Primrec₂ fun (n k : ℕ) => g (Nat.pair (Nat.unpair k).1 n) (Nat.unpair k).2 :=
      hgprim.comp
        (Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)) Primrec.fst)
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))
    have hr : Partrec fun n : ℕ => Nat.rfind fun k =>
        Part.some (g (Nat.pair (Nat.unpair k).1 n) (Nat.unpair k).2) :=
      Partrec.rfind (Primrec₂.to_comp hprim).partrec
    exact hr.map (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp.to₂
  · intro n x hx
    obtain ⟨k, hk, rfl⟩ := (Part.mem_map_iff _).1 hx
    have := Nat.rfind_spec hk
    simp only [Part.mem_some_iff] at this
    have hS := (hg (Nat.pair (Nat.unpair k).1 n)).2 ⟨(Nat.unpair k).2, this.symm⟩
    simpa using hS
  · rintro n ⟨x, hx⟩
    obtain ⟨k, hk⟩ := (hg (Nat.pair x n)).1 (by simpa using hx)
    refine Part.dom_iff_mem.2 ?_
    have hdom : (Nat.rfind fun k =>
        Part.some (g (Nat.pair (Nat.unpair k).1 n) (Nat.unpair k).2)).Dom := by
      refine Nat.rfind_dom.2 ⟨Nat.pair x k, ?_, fun {_} _ => trivial⟩
      simpa using hk
    exact ⟨_, Part.mem_map _ (Part.get_mem hdom)⟩

/-- Feeding a shortest program to a lambda term realizing a partial recursive function raises
complexity by at most an additive constant. -/
theorem exists_const_kolm_apply_le_of_partrec {V : ℕ →. ℕ} (hV : Partrec V) :
    ∃ c : ℕ, ∀ n x : ℕ, V n = Part.some x → kolm x ≤ kolm n + c := by
  obtain ⟨F, hFc, hF⟩ := lambdaComputable_of_partrec_closed hV
  refine ⟨size F + 1, fun n x hnx => ?_⟩
  obtain ⟨p, hp, hps⟩ := exists_program_of_kolm n
  have hred : Lambda.reduces (Lambda.app F p) (Lambda.church x) :=
    Lambda.reduces_trans (Lambda.reduces_app_right (t1 := F) hp.2) ((hF n x).1 hnx)
  have hle := kolm_le_of_isProgramFor (t := Lambda.app F p) (s := x)
    ⟨Lambda.IsClosed_app hFc hp.1, hred⟩
  simp only [size_app] at hle
  omega

/-- From `4` on, a square is below the corresponding power of two. -/
theorem sq_le_two_pow : ∀ {m : ℕ}, 4 ≤ m → m * m ≤ 2 ^ m := by
  intro m
  induction m with
  | zero => omega
  | succ k ih =>
    intro hm
    rcases Nat.lt_or_ge k 4 with hk | hk
    · have : k = 3 := by omega
      subst this
      norm_num
    · have h := ih (by omega)
      have h2 : 2 * k + 1 ≤ k * k := by nlinarith
      calc (k + 1) * (k + 1) = k * k + (2 * k + 1) := by ring
        _ ≤ 2 ^ k + 2 ^ k := by omega
        _ = 2 ^ (k + 1) := by ring

/-- A linear function is eventually below the powers of two. -/
theorem exists_lt_two_pow (a b : ℕ) : ∃ M : ℕ, ∀ m : ℕ, M ≤ m → a * m + b < 2 ^ m := by
  refine ⟨max 4 (a + b + 1), fun m hm => ?_⟩
  have h4 : 4 ≤ m := le_trans (le_max_left _ _) hm
  have hab : a + b + 1 ≤ m := le_trans (le_max_right _ _) hm
  have hsq := sq_le_two_pow h4
  have hlt : a * m + b < m * m := by nlinarith
  omega

/-- A linear function of the bit length is eventually dominated: the inequality
`n < a * Nat.size n + b` bounds `n`. -/
theorem exists_bound_of_lt_size (a b : ℕ) : ∃ N : ℕ, ∀ n : ℕ, n < a * Nat.size n + b → n < N := by
  obtain ⟨M, hM⟩ := exists_lt_two_pow a (a + b)
  refine ⟨2 ^ (M + 1), fun n hn => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Nat.two_pow_pos _
  have hsz : 0 < Nat.size n := Nat.size_pos.2 hpos
  have hlow : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
  have hj : Nat.size n - 1 < M := by
    by_contra hcon
    have hge : M ≤ Nat.size n - 1 := Nat.le_of_not_lt hcon
    have := hM (Nat.size n - 1) hge
    have hrw : a * (Nat.size n - 1) + (a + b) = a * Nat.size n + b := by
      have : Nat.size n - 1 + 1 = Nat.size n := by omega
      calc a * (Nat.size n - 1) + (a + b) = a * (Nat.size n - 1 + 1) + b := by ring
        _ = a * Nat.size n + b := by rw [this]
    omega
  calc n < 2 ^ Nat.size n := Nat.lt_size_self n
    _ ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Chaitin's incompleteness theorem.**  Read `S x n` as "the system proves `kolm x > n`".  If
the provable assertions are recursively enumerable and all true, then the thresholds `n` occurring
in them are bounded. -/
theorem chaitin_incompleteness {S : ℕ → ℕ → Prop} (hre : REPred fun q : ℕ × ℕ => S q.1 q.2)
    (hsound : ∀ x n, S x n → n < kolm x) : ∃ c : ℕ, ∀ x n, S x n → n < c := by
  obtain ⟨sel, hsel, hsound_sel, hdom_sel⟩ := exists_partrec_select hre
  obtain ⟨c, hc⟩ := exists_const_kolm_apply_le_of_partrec hsel
  obtain ⟨c₁, hc₁⟩ := exists_const_kolm_le_size
  obtain ⟨N, hN⟩ := exists_bound_of_lt_size c₁ (c₁ + c)
  refine ⟨N, fun x n hxn => ?_⟩
  have hdom := hdom_sel n ⟨x, hxn⟩
  have hy : (sel n).get hdom ∈ sel n := Part.get_mem hdom
  have h1 : n < kolm ((sel n).get hdom) := hsound _ n (hsound_sel n _ hy)
  have h2 : kolm ((sel n).get hdom) ≤ kolm n + c := hc n _ (Part.eq_some_iff.2 hy)
  have h3 : kolm n ≤ c₁ * (Nat.size n + 1) := hc₁ n
  refine hN n ?_
  have : c₁ * (Nat.size n + 1) = c₁ * Nat.size n + c₁ := by ring
  omega

/-- A sound r.e. system of complexity lower bounds leaves true assertions unproved: there is a
threshold `c` about which it proves nothing, even though `kolm x > c` holds for some `x`. -/
theorem exists_true_unprovable_kolm_lower_bound {S : ℕ → ℕ → Prop}
    (hre : REPred fun q : ℕ × ℕ => S q.1 q.2) (hsound : ∀ x n, S x n → n < kolm x) :
    ∃ c : ℕ, (∀ x, ¬ S x c) ∧ ∃ x : ℕ, c < kolm x := by
  obtain ⟨c, hc⟩ := chaitin_incompleteness hre hsound
  refine ⟨c, fun x hx => absurd (hc x c hx) (lt_irrefl c), ?_⟩
  obtain ⟨s, hs⟩ := exists_incompressible (c + 1)
  exact ⟨s, by omega⟩

end Lambda

end
