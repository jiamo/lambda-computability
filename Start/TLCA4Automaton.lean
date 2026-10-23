import Start.TLCA4PrefixBound

/-!
# Series V, big round, run 7, item A3: the argument-count automaton
(row M20-TLCA4-BETAETA)

`prefix_bound` turned into an invariant that is carried along the whole polynomial.

* `Unf P m ps args`: `P x z⃗ =w (m ∘ ps) x a⃗ z⃗` for every `z⃗`, with the arguments `a⃗` free of the
  fresh variables (`GY`).
* `unf_step`: from a state with `L = |a⃗|` arguments, the monomial `m` is `Bⁿ M` with `n ≤ L`
  (new state with `L + 1` arguments), or `Bⁿ B` with `n + 2 ≤ L` (new state with `L - 1`
  arguments), or `B^(L-1) B` (the "escape": a fresh variable enters an argument), or base `I`.
* `unf_end`: at the last monomial, the head-arity invariant forces `Bⁿ B` with `n ≤ 1` and `L = 2`.
* `Adm L m ps`: the resulting admissibility predicate (an automaton on the argument count).
* **`polyFiveOne_adm`**: if `PolyFiveOne` holds, it has a witness `M ∘ m₂ ∘ … ∘ m_k` without base
  `I` monomials such that `Adm 1 m₂ [m₃, …, m_k]`.
  T = M∘BM∘B and Q = M∘M∘BM∘B∘B are admissible (`adm_T`, `adm_Q`).
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

/-- The unfolding state: `P x z⃗ =w (m ∘ ps) x a⃗ z⃗` for every `z⃗`, with `a⃗` free of the fresh
variables. -/
def Unf (P : Tm) (m : Mono) (ps : List Mono) (args : List Tm) : Prop :=
  (∀ t ∈ args, ∀ a b : ℕ, 0 < b → GY a b (toLam t)) ∧
    ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) zs)
      (apps (Tm.app (polyTm m ps) (Tm.var 0)) (args ++ zs))

/-- The admissibility predicate: the automaton on the argument count `L`. -/
def Adm : ℕ → Mono → List Mono → Prop
  | L, m, [] => m.base = .B ∧ L = 2 ∧ m.n ≤ 1
  | L, m, m' :: ps =>
      (m.base = .M ∧ m.n ≤ L ∧ Adm (L + 1) m' ps) ∨
      (m.base = .B ∧ m.n + 2 ≤ L ∧ Adm (L - 1) m' ps) ∨
      (m.base = .B ∧ m.n + 1 = L)

/-- The weak action of the head monomial of a state: `(m ∘ ps) x a⃗ z⃗ =w m.tm w a⃗ z⃗`. -/
theorem unf_head (P : Tm) (m : Mono) (ps : List Mono) (args : List Tm) (h : Unf P m ps args) :
    ∃ w : Tm, (∀ a b : ℕ, 0 < b → GY a b (toLam w)) ∧
      (∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) zs)
        (apps (Tm.app m.tm w) (args ++ zs))) ∧
      (∀ m' ps', ps = m' :: ps' → w = Tm.app (polyTm m' ps') (Tm.var 0)) := by
  cases ps with
  | nil =>
    exact ⟨Tm.var 0, fun a b hb => .var (by omega), h.2, fun _ _ h => by cases h⟩
  | cons m' ps' =>
    refine ⟨Tm.app (polyTm m' ps') (Tm.var 0), fun a b hb => gy_U _ _ _ _ hb,
      fun zs => (h.2 zs).trans (Tm.WEq.apps (comp_action _ _ _) _), ?_⟩
    intro m'' ps'' he
    cases he
    rfl

theorem gy_apps_of (w : Tm) (l : List Tm) (hw : ∀ a b : ℕ, 0 < b → GY a b (toLam w))
    (hl : ∀ t ∈ l, ∀ a b : ℕ, 0 < b → GY a b (toLam t)) :
    ∀ a b : ℕ, 0 < b → GY a b (toLam (apps w l)) :=
  fun a b hb => GY.toLam_apps (hw a b hb) (fun z hz => hl z hz a b hb)

/-- The `M`-transition: `Bⁿ M w a⃗ z⃗ =w w a₁…aₙ (w a₁…aₙ) aₙ₊₁ … z⃗`. -/
theorem actM_args (n : ℕ) (w : Tm) (args zs : List Tm) (hn : n ≤ args.length) :
    Tm.WEq (apps (Tm.app (bpow n Tm.M) w) (args ++ zs))
      (apps w ((args.take n ++ apps w (args.take n) :: args.drop n) ++ zs)) := by
  have hsplit : args ++ zs = args.take n ++ (args.drop n ++ zs) := by
    rw [← List.append_assoc, List.take_append_drop]
  rw [hsplit, apps_append]
  refine (Tm.WEq.apps (bpowM_action n w _ (by simp; omega)) _).trans ?_
  rw [List.append_assoc, List.cons_append, apps_append w]
  exact .refl _

/-- The `B`-transition: `Bⁿ B w a⃗ z⃗ =w w a₁…aₙ (aₙ₊₁ aₙ₊₂) aₙ₊₃ … z⃗`. -/
theorem actB_args (n : ℕ) (w : Tm) (args zs : List Tm) (a b : Tm) (rest : List Tm)
    (hd : args.drop n = a :: b :: rest) :
    Tm.WEq (apps (Tm.app (bpow n Tm.B) w) (args ++ zs))
      (apps w ((args.take n ++ Tm.app a b :: rest) ++ zs)) := by
  have hn : (args.take n).length = n := by
    have := congrArg List.length hd; simp at this ⊢; omega
  have hsplit : args ++ zs = args.take n ++ a :: b :: (rest ++ zs) := by
    conv_lhs => rw [← List.take_append_drop n args, hd]
    simp
  rw [hsplit]
  refine (bpowB_action n w _ hn a b (rest ++ zs)).trans ?_
  simp only [List.append_assoc, List.cons_append]
  exact .refl _

theorem drop_two {n : ℕ} {args : List Tm} (h2 : n + 2 ≤ args.length) :
    ∃ a b rest, args.drop n = a :: b :: rest := by
  rcases h : args.drop n with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · have := congrArg List.length h; simp at this; omega
  · have := congrArg List.length h; simp at this; omega
  · exact ⟨a, b, rest, rfl⟩

/-- **One transition of the automaton.** -/
theorem unf_step (P : Tm) (hP : Tm.IsBMI P)
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0)))))
    (m m' : Mono) (ps : List Mono) (args : List Tm) (hI : m.base ≠ .I)
    (h : Unf P m (m' :: ps) args) :
    (m.base = .M ∧ m.n ≤ args.length ∧
        ∃ args' : List Tm, args'.length = args.length + 1 ∧ Unf P m' ps args') ∨
      (m.base = .B ∧ m.n + 2 ≤ args.length ∧
        ∃ args' : List Tm, args'.length = args.length - 1 ∧ Unf P m' ps args') ∨
      (m.base = .B ∧ m.n + 1 = args.length) := by
  obtain ⟨w, hw, hL, hwe⟩ := unf_head P m _ args h
  have hwe := hwe m' ps rfl
  have hb := prefix_bound P w hP args m (by
    intro t ht a b hb
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hw a b hb
    · exact h.1 t ht a b hb) hL hY
  obtain ⟨n, base⟩ := m
  rcases hb with ⟨hbase, hn⟩ | ⟨hbase, hn⟩ | hbase
  · simp only at hbase hn; subst hbase
    by_cases h2 : n + 2 ≤ args.length
    · right; left
      refine ⟨rfl, h2, ?_⟩
      obtain ⟨a, b, rest, hd⟩ := drop_two h2
      have hsub : ∀ t ∈ a :: b :: rest, t ∈ args := fun t ht =>
        List.mem_of_mem_drop (by rw [hd]; exact ht : t ∈ args.drop n)
      refine ⟨args.take n ++ Tm.app a b :: rest, ?_, ?_, ?_⟩
      · have := congrArg List.length hd; simp at this ⊢; omega
      · intro t ht a' b' hb''
        simp only [List.mem_append, List.mem_cons] at ht
        rcases ht with ht | rfl | ht
        · exact h.1 t (List.mem_of_mem_take ht) a' b' hb''
        · exact .app (h.1 a (hsub a (by simp)) a' b' hb'') (h.1 b (hsub b (by simp)) a' b' hb'')
        · exact h.1 t (hsub t (by simp [ht])) a' b' hb''
      · intro zs
        rw [← hwe]
        exact (hL zs).trans (actB_args n w args zs a b rest hd)
    · right; right
      exact ⟨rfl, by simp only; omega⟩
  · simp only at hbase hn; subst hbase
    left
    refine ⟨rfl, hn, args.take n ++ apps w (args.take n) :: args.drop n, by simp; omega, ?_, ?_⟩
    · intro t ht a b hb
      simp only [List.mem_append, List.mem_cons] at ht
      rcases ht with ht | rfl | ht
      · exact h.1 t (List.mem_of_mem_take ht) a b hb
      · exact gy_apps_of w _ hw (fun z hz => h.1 z (List.mem_of_mem_take hz)) a b hb
      · exact h.1 t (List.mem_of_mem_drop ht) a b hb
    · intro zs
      rw [← hwe]
      exact (hL zs).trans (actM_args n w args zs hn)
  · exact (hI hbase).elim

/-- **The last monomial.** At the end of the polynomial, the head-arity invariant forces
`Bⁿ B` with `n ≤ 1` and exactly two arguments. -/
theorem unf_end (P : Tm) (hP : Tm.IsBMI P)
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0)))))
    (m : Mono) (args : List Tm) (hpos : 1 ≤ args.length) (hI : m.base ≠ .I)
    (h : Unf P m [] args) : Adm args.length m [] := by
  have hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) zs)
      (apps (Tm.app m.tm (Tm.var 0)) (args ++ zs)) := h.2
  have hw : ∀ a b : ℕ, 0 < b → GY a b (toLam (Tm.var 0)) := fun a b hb => .var (by omega)
  have hb := prefix_bound P (Tm.var 0) hP args m (by
    intro t ht a b hb
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hw a b hb
    · exact h.1 t ht a b hb) hL hY
  obtain ⟨n, base⟩ := m
  rcases hb with ⟨hbase, hn⟩ | ⟨hbase, hn⟩ | hbase
  · simp only at hbase hn; subst hbase
    by_cases h2 : n + 2 ≤ args.length
    · obtain ⟨a, b, rest, hd⟩ := drop_two h2
      have hlen := congrArg List.length hd
      simp at hlen
      by_cases hl2 : args.length = 2
      · exact ⟨rfl, hl2, by show n ≤ 1; omega⟩
      exfalso
      refine arity_contra P [] _ ?_ ((hL []).trans (actB_args n _ args [] a b rest hd)) hY
      simp; omega
    · have h1 : n + 1 = args.length := by omega
      by_cases hl2 : args.length = 2
      · exact ⟨rfl, hl2, by show n ≤ 1; omega⟩
      · exfalso
        have h2' : n + 2 ≤ (args ++ [Tm.var 1]).length := by simp; omega
        obtain ⟨a, b, rest, hd⟩ := drop_two h2'
        have hlen := congrArg List.length hd
        simp at hlen
        have := actB_args n (Tm.var 0) (args ++ [Tm.var 1]) [] a b rest hd
        rw [List.append_nil] at this
        refine arity_contra P [Tm.var 1] _ ?_ ((hL [Tm.var 1]).trans this) hY
        simp; omega
  · simp only at hbase hn; subst hbase
    exfalso
    refine arity_contra P [] _ ?_ ((hL []).trans (actM_args n _ args [] hn)) hY
    simp; omega
  · exact (hI hbase).elim

/-- **The automaton invariant**: every state reached by a fixed-point polynomial is admissible. -/
theorem unf_adm (P : Tm) (hP : Tm.IsBMI P)
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) :
    ∀ (ps : List Mono) (m : Mono) (args : List Tm), 1 ≤ args.length →
      (∀ q ∈ m :: ps, q.base ≠ .I) → Unf P m ps args → Adm args.length m ps := by
  intro ps
  induction ps with
  | nil => intro m args hpos hI h; exact unf_end P hP hY m args hpos (hI m (by simp)) h
  | cons m' ps ih =>
    intro m args hpos hI h
    have hI' : ∀ q ∈ m' :: ps, q.base ≠ .I := fun q hq => hI q (by simp [hq])
    rcases unf_step P hP hY m m' ps args (hI m (by simp)) h with
      ⟨hb, hn, args', hl, h'⟩ | ⟨hb, hn, args', hl, h'⟩ | ⟨hb, hn⟩
    · left
      refine ⟨hb, hn, ?_⟩
      have := ih m' args' (by omega) hI' h'
      rwa [hl] at this
    · right; left
      refine ⟨hb, hn, ?_⟩
      have := ih m' args' (by omega) hI' h'
      rwa [hl] at this
    · right; right; exact ⟨hb, hn⟩

/-- **The automaton constraint on βη fixed-point polynomials**: if `PolyFiveOne` holds, it has a
witness `M ∘ m₂ ∘ … ∘ m_k` without base-`I` monomials whose tail `m₂, …, m_k` is admissible from
the argument count `1`. -/
theorem polyFiveOne_adm (h : PolyFiveOne) :
    ∃ (m' : Mono) (ps : List Mono), (∀ q ∈ (⟨0, .M⟩ : Mono) :: m' :: ps, q.base ≠ .I) ∧
      Adm 1 m' ps ∧
      betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m' :: ps)) (Tm.var 0)))
        (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (m' :: ps)) (Tm.var 0)))) := by
  obtain ⟨m', ps, hI, hfix⟩ := polyFiveOne_head_M h
  refine ⟨m', ps, hI, ?_, hfix⟩
  set u := Tm.app (polyTm m' ps) (Tm.var 0)
  have hU : Unf (polyTm ⟨0, .M⟩ (m' :: ps)) m' ps [u] := by
    refine ⟨fun t ht a b hb => ?_, fun zs => ?_⟩
    · simp only [List.mem_singleton] at ht; subst ht; exact gy_U _ _ _ _ hb
    · refine (Tm.WEq.apps (comp_action _ _ _) zs).trans ?_
      exact Tm.WEq.apps (.step (.m _)) zs
  exact unf_adm _ (polyTm_isBMI _ _) hfix ps m' [u] (by simp)
    (fun q hq => hI q (by simp [hq])) hU

/-- T = M ∘ BM ∘ B passes the automaton. -/
theorem adm_T : Adm 1 ⟨1, .M⟩ [⟨0, .B⟩] := by simp [Adm]

/-- Q = M ∘ M ∘ BM ∘ B ∘ B passes the automaton. -/
theorem adm_Q : Adm 1 ⟨0, .M⟩ [⟨1, .M⟩, ⟨0, .B⟩, ⟨0, .B⟩] := by simp [Adm]

end TLCA4
