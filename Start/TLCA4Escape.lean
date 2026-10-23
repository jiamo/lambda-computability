import Start.TLCA4Automaton

/-!
# Series V, big round, run 7, item A3: one step past the escape
(row M20-TLCA4-BETAETA)

In an escape state of the automaton (`Start/TLCA4Automaton.lean`) the first fresh argument `z₁`
enters the last fixed argument, `P x z₁ z⃗ =w u a₁ … a_{L-1} (a_L z₁) z⃗`. The pairing and
occurrence contradictions still apply to the later fresh arguments:

* `wrap_BB_contra`, `wrap_BM_contra`, **`wrap_bound`**: if `P x z₁ z⃗ =w m w a⃗ (f z₁) z⃗` for all
  `z⃗` (`w`, `f`, `a⃗` free of the fresh variables), then `m = Bⁿ B` or `m = Bⁿ M` with `n ≤ |a⃗|`
  (or base `I`).
* **`unf_escape_next`**: after an escape at argument count `L`, the next monomial is `Bⁿ B` or
  `Bⁿ M` with `n ≤ L - 1` (or has base `I`).
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

/-- The fresh variables `var 2, …, var (a + 1)`. -/
def freshTail (a : ℕ) : List Tm := (List.range a).map (fun i => Tm.var (i + 2))

theorem fresh_succ_tail (a : ℕ) : fresh (a + 1) = Tm.var 1 :: freshTail a := by
  rw [fresh_succ']; rfl

/-- Pairing exclusion past a wrapped argument. -/
theorem wrap_BB_contra (P w f : Tm) (args : List Tm) (a : ℕ)
    (hGY : ∀ t ∈ f :: w :: args, ∀ i b : ℕ, 0 < b → GY i b (toLam t))
    (hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) (Tm.var 1 :: zs))
      (apps (Tm.app (bpow (args.length + 1 + a) Tm.B) w)
        (args ++ Tm.app f (Tm.var 1) :: zs)))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) : False := by
  have hlen : (args ++ Tm.app f (Tm.var 1) :: freshTail a).length = args.length + 1 + a := by
    simp [freshTail]; omega
  have hL' : Tm.WEq (apps (Tm.app P (Tm.var 0))
        (fresh (a + 1) ++ [Tm.var (a + 2), Tm.var (a + 3)]))
      (apps w ((args ++ Tm.app f (Tm.var 1) :: freshTail a) ++
        [Tm.app (Tm.var (a + 2)) (Tm.var (a + 3))])) := by
    rw [fresh_succ_tail]
    refine (hL _).trans ?_
    have := bpowB_action (args.length + 1 + a) w (args ++ Tm.app f (Tm.var 1) :: freshTail a)
      hlen (Tm.var (a + 2)) (Tm.var (a + 3)) []
    simp only [List.append_assoc, List.cons_append] at this ⊢
    exact this
  refine gy_contra (a + 1) P (fresh (a + 1)) _ ?_
    ((betaEtaConv_symm (toLam_weq hL')).trans (conv_apps hY _))
  refine GY.toLam_apps (hGY w (by simp) _ _ (by omega)) ?_
  intro z hz
  simp only [List.mem_append, List.mem_cons, freshTail, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hz
  rcases hz with (hz | rfl | ⟨i, hi, rfl⟩) | rfl
  · exact hGY z (by simp [hz]) _ _ (by omega)
  · exact .app (hGY f (by simp) _ _ (by omega)) (.var (by omega))
  · exact .var (by omega)
  · exact .pair

/-- Occurrence exclusion past a wrapped argument. -/
theorem wrap_BM_contra (P w f : Tm) (hP : Tm.IsBMI P) (args : List Tm) (a : ℕ)
    (hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) (Tm.var 1 :: zs))
      (apps (Tm.app (bpow (args.length + 1 + a) Tm.M) w)
        (args ++ Tm.app f (Tm.var 1) :: zs)))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) : False := by
  set W := apps w (args ++ Tm.app f (Tm.var 1) :: freshTail a)
  have hlen : (args ++ Tm.app f (Tm.var 1) :: freshTail a).length = args.length + 1 + a := by
    simp [freshTail]; omega
  have hL' : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1)])) (Tm.app W W) := by
    rw [← fresh_succ, fresh_succ_tail]
    refine ((hL _).trans ?_)
    exact bpowM_action _ w _ hlen
  refine occ_contra a P hP (Tm.app W W) ?_
    ((betaEtaConv_symm (toLam_weq hL')).trans (conv_apps hY _))
  have hmem : ∃ t ∈ args ++ Tm.app f (Tm.var 1) :: freshTail a, 1 ≤ occL (a + 1) (toLam t) := by
    cases a with
    | zero => exact ⟨Tm.app f (Tm.var 1), by simp, by simp [toLam, occL]⟩
    | succ a =>
      refine ⟨Tm.var (a + 2), ?_, by simp [toLam, occL]⟩
      simp [freshTail]
  obtain ⟨t, ht, hto⟩ := hmem
  have hW : 1 ≤ occL (a + 1) (toLam W) := by
    simp only [W, occL_toLam_apps]
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun t => occL (a + 1) (toLam t)) ht)
    omega
  simp only [toLam, occL]
  omega

/-- **The bound past a wrapped argument.** -/
theorem wrap_bound (P w f : Tm) (hP : Tm.IsBMI P) (args : List Tm) (m : Mono)
    (hGY : ∀ t ∈ f :: w :: args, ∀ i b : ℕ, 0 < b → GY i b (toLam t))
    (hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) (Tm.var 1 :: zs))
      (apps (Tm.app m.tm w) (args ++ Tm.app f (Tm.var 1) :: zs)))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) :
    (m.base = .B ∧ m.n ≤ args.length) ∨ (m.base = .M ∧ m.n ≤ args.length) ∨ m.base = .I := by
  obtain ⟨n, b⟩ := m
  cases b with
  | I => exact .inr (.inr rfl)
  | B =>
    by_contra hc
    obtain ⟨a, rfl⟩ : ∃ a, n = args.length + 1 + a := ⟨n - args.length - 1, by simp at hc; omega⟩
    exact wrap_BB_contra P w f args a hGY hL hY
  | M =>
    by_contra hc
    obtain ⟨a, rfl⟩ : ∃ a, n = args.length + 1 + a := ⟨n - args.length - 1, by simp at hc; omega⟩
    exact wrap_BM_contra P w f hP args a hL hY

/-- **One step past the escape**: if the automaton escapes at argument count `L` (head monomial
`B^(L-1) B`), the next monomial is `Bⁿ B` or `Bⁿ M` with `n ≤ L - 1`, or has base `I`. -/
theorem unf_escape_next (P : Tm) (hP : Tm.IsBMI P)
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0)))))
    (n : ℕ) (m' : Mono) (ps : List Mono) (args : List Tm) (hn : n + 1 = args.length)
    (h : Unf P ⟨n, .B⟩ (m' :: ps) args) :
    (m'.base = .B ∧ m'.n ≤ n) ∨ (m'.base = .M ∧ m'.n ≤ n) ∨ m'.base = .I := by
  obtain ⟨al, hal⟩ : ∃ al, args.drop n = [al] := by
    rcases hd : args.drop n with _ | ⟨al, _ | ⟨b, rest⟩⟩
    · have := congrArg List.length hd; simp at this; omega
    · exact ⟨al, rfl⟩
    · have := congrArg List.length hd; simp at this; omega
  have hmem : al ∈ args := List.mem_of_mem_drop (by rw [hal]; simp : al ∈ args.drop n)
  have htl : (args.take n).length = n := by simp; omega
  have hsplit : args = args.take n ++ [al] := by
    conv_lhs => rw [← List.take_append_drop n args, hal]
  obtain ⟨u', hu', hGYu'⟩ := poly_tail m' ps
  have hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) (Tm.var 1 :: zs))
      (apps (Tm.app m'.tm u') (args.take n ++ Tm.app al (Tm.var 1) :: zs)) := by
    intro zs
    refine (h.2 (Tm.var 1 :: zs)).trans ?_
    refine (Tm.WEq.apps (comp_action _ _ _) _).trans ?_
    have e : args ++ Tm.var 1 :: zs = args.take n ++ al :: Tm.var 1 :: zs := by
      conv_lhs => rw [hsplit]
      simp
    rw [e]
    refine (bpowB_action n _ _ htl al (Tm.var 1) zs).trans ?_
    exact Tm.WEq.apps hu' _
  have hb := wrap_bound P u' al hP (args.take n) m' (by
    intro t ht i b hb
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · exact h.1 _ hmem i b hb
    · exact hGYu' i b hb
    · exact h.1 t (List.mem_of_mem_take ht) i b hb) hL hY
  rw [htl] at hb
  exact hb

end TLCA4
