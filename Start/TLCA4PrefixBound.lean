import Start.TLCA4ThirdMono

/-!
# Series V, big round, run 6, item A3: a uniform prefix bound for the next monomial
(row M20-TLCA4-BETAETA)

The pairing and occurrence arguments of `Start/TLCA4SecondMono.lean` and
`Start/TLCA4ThirdMono.lean`, stated once for an arbitrary prefix of arguments free of the fresh
variables.

* `prefix_BB_contra`, `prefix_BM_contra`, **`prefix_bound`**: if `P x z⃗ =w m w a⃗ z⃗` for all `z⃗`
  (with `w`, `a⃗` free of the fresh variables) and `P` is a βη fixed-point combinator, then
  `m = Bⁿ B` with `n < |a⃗|` or `m = Bⁿ M` with `n ≤ |a⃗|` (or base `I`);
* `secondM_unfold_cons`, **`fixedPoint_M_fourth`**: in the branches `M ∘ m₂ ∘ m₃ ∘ m₄ ∘ …` with
  `m₂ ∈ {M, B M}`, `m₃ ∈ {B, M, B M, B² M}`, the fourth monomial obeys this bound with
  `|a⃗| = 1` for `m₃ = B` and `|a⃗| = 3` otherwise.
-/
set_option autoImplicit false

namespace TLCA4

open Lambda

/-- **Pairing exclusion, uniform version.** -/
theorem prefix_BB_contra (P w : Tm) (args : List Tm) (a : ℕ)
    (hGY : ∀ t ∈ w :: args, ∀ i b : ℕ, 0 < b → GY i b (toLam t))
    (hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) zs)
      (apps (Tm.app (bpow (args.length + a) Tm.B) w) (args ++ zs)))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) : False := by
  have hlen : (args ++ fresh a).length = args.length + a := by simp [fresh]
  have hL' : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1), Tm.var (a + 2)]))
      (apps w ((args ++ fresh a) ++ [Tm.app (Tm.var (a + 1)) (Tm.var (a + 2))])) := by
    refine (hL _).trans ?_
    have := bpowB_action (args.length + a) w (args ++ fresh a) hlen (Tm.var (a + 1))
      (Tm.var (a + 2)) []
    simp only [List.append_assoc] at this ⊢
    exact this
  refine gy_contra a P (fresh a) _ ?_
    ((betaEtaConv_symm (toLam_weq hL')).trans (conv_apps hY _))
  refine GY.toLam_apps (hGY w (by simp) _ _ (by omega)) ?_
  intro z hz
  simp only [List.mem_append, fresh, List.mem_map, List.mem_range, List.mem_singleton] at hz
  rcases hz with (hz | ⟨i, hi, rfl⟩) | rfl
  · exact hGY z (by simp [hz]) _ _ (by omega)
  · exact .var (by omega)
  · exact .pair

/-- **Occurrence exclusion, uniform version.** -/
theorem prefix_BM_contra (P w : Tm) (hP : Tm.IsBMI P) (args : List Tm) (a : ℕ)
    (hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) zs)
      (apps (Tm.app (bpow (args.length + a + 1) Tm.M) w) (args ++ zs)))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) : False := by
  set W := apps w (args ++ (fresh a ++ [Tm.var (a + 1)]))
  have hlen : (args ++ (fresh a ++ [Tm.var (a + 1)])).length = args.length + a + 1 := by
    simp [fresh]; omega
  have hL' : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1)])) (Tm.app W W) :=
    (hL _).trans (bpowM_action _ w _ hlen)
  refine occ_contra a P hP (Tm.app W W) ?_
    ((betaEtaConv_symm (toLam_weq hL')).trans (conv_apps hY _))
  have hW : 1 ≤ occL (a + 1) (toLam W) := by
    simp only [W, occL_toLam_apps, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil, toLam, occL, ↓reduceIte]
    omega
  simp only [toLam, occL]
  omega

/-- **The prefix bound**: if `P x z⃗ =w m w a⃗ z⃗` for every `z⃗`, with `w` and the arguments `a⃗` free
of the fresh variables, and `P` is a βη fixed-point combinator, then `m = Bⁿ B` with `n < |a⃗|`,
or `m = Bⁿ M` with `n ≤ |a⃗|`, or `m` has base `I`. -/
theorem prefix_bound (P w : Tm) (hP : Tm.IsBMI P) (args : List Tm) (m : Mono)
    (hGY : ∀ t ∈ w :: args, ∀ i b : ℕ, 0 < b → GY i b (toLam t))
    (hL : ∀ zs : List Tm, Tm.WEq (apps (Tm.app P (Tm.var 0)) zs)
      (apps (Tm.app m.tm w) (args ++ zs)))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) :
    (m.base = .B ∧ m.n < args.length) ∨ (m.base = .M ∧ m.n ≤ args.length) ∨ m.base = .I := by
  obtain ⟨n, b⟩ := m
  cases b with
  | I => exact .inr (.inr rfl)
  | B =>
    by_contra hc
    obtain ⟨a, rfl⟩ : ∃ a, n = args.length + a := ⟨n - args.length, by simp at hc; omega⟩
    exact prefix_BB_contra P w args a hGY hL hY
  | M =>
    by_contra hc
    obtain ⟨a, rfl⟩ : ∃ a, n = args.length + a + 1 := ⟨n - args.length - 1, by simp at hc; omega⟩
    exact prefix_BM_contra P w hP args a hL hY

/-- The weak unfolding of `M ∘ m₂ ∘ m₃ ∘ m₄ ∘ …` for `m₂ ∈ {M, B M}`, with the tail kept. -/
theorem secondM_unfold_cons (m₂ m3 m4 : Mono) (ps : List Mono) (hm : m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩) :
    ∃ g h : Tm, (∀ a b : ℕ, 0 < b → GY a b (toLam g) ∧ GY a b (toLam h)) ∧
      ∀ zs : List Tm, Tm.WEq (apps (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m3 :: m4 :: ps)) (Tm.var 0)) zs)
        (apps (Tm.app m3.tm (Tm.app (polyTm m4 ps) (Tm.var 0))) (g :: h :: zs)) := by
  set S := polyTm m3 (m4 :: ps)
  set U := Tm.app S (Tm.var 0)
  have hu : Tm.WEq U (Tm.app m3.tm (Tm.app (polyTm m4 ps) (Tm.var 0))) := comp_action _ _ _
  have hU : ∀ a b : ℕ, 0 < b → GY a b (toLam U) := fun a b hb => gy_U _ _ _ _ hb
  rcases hm with rfl | rfl
  · refine ⟨U, Tm.app U U, fun a b hb => ⟨hU a b hb, .app (hU a b hb) (hU a b hb)⟩, fun zs => ?_⟩
    have h1 : Tm.WEq (Tm.app (comp Tm.M S) (Tm.var 0)) (Tm.app U U) :=
      (comp_action _ _ _).trans (.step (.m _))
    refine (Tm.WEq.apps (comp_action _ _ _) zs).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) zs).trans ?_
    refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) zs).trans ?_
    show Tm.WEq (apps U (U :: Tm.app U U :: zs)) _
    exact Tm.WEq.apps hu _
  · set V := Tm.app (Tm.app Tm.B Tm.M) U
    have hV : ∀ a b : ℕ, 0 < b → GY a b (toLam V) := fun a b hb =>
      .app (GY.toLam_closed (.app .B .M)) (hU a b hb)
    refine ⟨V, Tm.app U V, fun a b hb => ⟨hV a b hb, .app (hU a b hb) (hV a b hb)⟩, fun zs => ?_⟩
    have h1 : Tm.WEq (Tm.app (comp (Tm.app Tm.B Tm.M) S) (Tm.var 0)) V := comp_action _ _ _
    refine (Tm.WEq.apps (comp_action _ _ _) zs).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) zs).trans ?_
    refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) zs).trans ?_
    refine (Tm.WEq.apps (.step (.b _ _ _)) zs).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) zs).trans ?_
    show Tm.WEq (apps U (V :: Tm.app U V :: zs)) _
    exact Tm.WEq.apps hu _

/-- **The fourth monomial in the branches `M ∘ m₂ ∘ m₃ ∘ m₄ ∘ …`, `m₂ ∈ {M, B M}`,
`m₃ ∈ {B, M, B M, B² M}`**: with `c = 1` for `m₃ = B` and `c = 3` otherwise,
`m₄ = Bⁿ B` with `n < c`, or `m₄ = Bⁿ M` with `n ≤ c` (or `m₄` has base `I`). -/
theorem fixedPoint_M_fourth (m₂ m₃ m₄ : Mono) (ps : List Mono)
    (hm2 : m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩)
    (hm3 : m₃ = ⟨0, .B⟩ ∨ m₃ = ⟨0, .M⟩ ∨ m₃ = ⟨1, .M⟩ ∨ m₃ = ⟨2, .M⟩)
    (hfix : betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: m₄ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: m₄ :: ps)) (Tm.var 0))))) :
    let c := if m₃ = ⟨0, .B⟩ then 1 else 3
    (m₄.base = .B ∧ m₄.n < c) ∨ (m₄.base = .M ∧ m₄.n ≤ c) ∨ m₄.base = .I := by
  intro c
  obtain ⟨g, h, hgh, hL⟩ := secondM_unfold_cons m₂ m₃ m₄ ps hm2
  obtain ⟨w, hw, hGYw⟩ := poly_tail m₄ ps
  set u := Tm.app (polyTm m₄ ps) (Tm.var 0)
  have hu : ∀ a b : ℕ, 0 < b → GY a b (toLam u) := fun a b hb => gy_U _ _ _ _ hb
  have key : ∃ args : List Tm, args.length = c ∧
      (∀ t ∈ args, ∀ a b : ℕ, 0 < b → GY a b (toLam t)) ∧
      ∀ zs : List Tm, Tm.WEq (apps (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: m₄ :: ps)) (Tm.var 0)) zs)
        (apps u (args ++ zs)) := by
    rcases hm3 with rfl | rfl | rfl | rfl
    · refine ⟨[Tm.app g h], rfl, ?_, fun zs => (hL zs).trans ?_⟩
      · intro t ht a b hb
        simp only [List.mem_singleton] at ht; subst ht
        exact .app (hgh a b hb).1 (hgh a b hb).2
      · exact Tm.WEq.apps (.step (.b _ _ _)) zs
    · refine ⟨[u, g, h], rfl, ?_, fun zs => (hL zs).trans ?_⟩
      · intro t ht a b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        exacts [hu a b hb, (hgh a b hb).1, (hgh a b hb).2]
      · exact Tm.WEq.apps (Tm.WEq.appL (.step (.m _)) _) _
    · refine ⟨[g, Tm.app u g, h], rfl, ?_, fun zs => (hL zs).trans ?_⟩
      · intro t ht a b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        exacts [(hgh a b hb).1, .app (hu a b hb) (hgh a b hb).1, (hgh a b hb).2]
      · show Tm.WEq (apps (Tm.app (Tm.app (Tm.app Tm.B Tm.M) u) g) (h :: zs)) _
        refine (Tm.WEq.apps (.step (.b _ _ _)) _).trans ?_
        exact Tm.WEq.apps (.step (.m _)) _
    · refine ⟨[g, h, apps u [g, h]], rfl, ?_, fun zs => (hL zs).trans ?_⟩
      · intro t ht a b hb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        exacts [(hgh a b hb).1, (hgh a b hb).2, .app (.app (hu a b hb) (hgh a b hb).1) (hgh a b hb).2]
      · show Tm.WEq (apps (Tm.app (bpow 2 Tm.M) u) ([g, h] ++ zs)) _
        rw [apps_append]
        exact Tm.WEq.apps (bpowM_action 2 u [g, h] rfl) zs
  obtain ⟨args, hlen, hargs, hL'⟩ := key
  have := prefix_bound _ w (polyTm_isBMI _ _) args m₄ ?_ (fun zs => (hL' zs).trans
    (Tm.WEq.apps hw _)) hfix
  · rw [hlen] at this; exact this
  · intro t ht a b hb
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hGYw a b hb
    · exact hargs t ht a b hb

end TLCA4
