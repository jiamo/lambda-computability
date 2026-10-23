import Start.TLCA4SecondMono

/-!
# Series V, big round, run 6, item A3: the third monomial of a βη fixed-point polynomial
(row M20-TLCA4-BETAETA)

The `GY` pairing argument, occurrence counting in the λI-calculus and a new arity comparison
(`arity_contra`, from the βη head-arity invariant `HSp`) applied to the third monomial of
`M ∘ m₂ ∘ m₃ ∘ …` (and the fourth one in the branch `M ∘ B ∘ M ∘ …`).

* `polyMB_not_fixedPoint`, `polyMM_not_fixedPoint`, `polyMBM_not_fixedPoint`,
  `polyMBM'_not_fixedPoint` — the two-monomial candidates `M∘B`, `M∘M`, `M∘BM` and `M∘B∘M`;
* `thirdB_B_not_fixedPoint`, `thirdB_BB_not_fixedPoint`, `thirdB_BM_not_fixedPoint` —
  `M ∘ B ∘ Bᵃ B ∘ …` and `M ∘ B ∘ Bᵃ⁺¹ M ∘ …`;
* `thirdM_BB_not_fixedPoint`, `thirdM_BM_not_fixedPoint` — `M ∘ m₂ ∘ Bᵃ⁺² B ∘ …` and
  `M ∘ m₂ ∘ Bᵃ⁺³ M ∘ …` for `m₂ ∈ {M, B M}`;
* **`polyFiveOne_third`** — `(m₂, m₃) = (B, M)`, or `m₂ ∈ {M, BM}`, `m₃ ∈ {B, BB, M, BM, B²M}`;
* `fourthBM_B1_not_fixedPoint`, `fourthBM_BB_not_fixedPoint`, `fourthBM_BM_not_fixedPoint`,
  `fixedPoint_BM_fourth` — in the branch `M ∘ B ∘ M ∘ m₄ ∘ …`, `m₄ ∈ {B, M, B M}`;
* **`polyFiveOne_fourth`** — the combination.
-/

set_option autoImplicit false

namespace TLCA4

open Lambda

/-- A variable-headed spine has head `y` and arity `l.length`. -/
theorem hsp_toLam_apps_var (y : ℕ) (l : List Tm) :
    HSp (toLam (apps (Tm.var y) l)) y l.length := by
  obtain ⟨cs, hcs⟩ := toLam_apps_spn (y := y) (cs := []) (f := Tm.var y) l rfl
  have hlen : cs.length = l.length := by
    have key : ∀ (l : List Tm) (f : Tm) (cs0 cs : List Lambda), toLam f = spn y cs0 →
        toLam (apps f l) = spn y cs → cs.length = cs0.length + l.length := by
      intro l
      induction l with
      | nil =>
        intro f cs0 cs h1 h2
        rw [apps, h1] at h2
        have := (nsp_spn y cs0).unique (h2 ▸ nsp_spn y cs)
        simp at this ⊢; omega
      | cons z l ih =>
        intro f cs0 cs h1 h2
        have := ih (Tm.app f z) (toLam z :: cs0) cs (by simp [toLam, h1, spn]) h2
        simp at this ⊢; omega
    simpa using key l (Tm.var y) [] cs rfl hcs
  rw [hcs, ← hlen]
  exact .neu (nsp_spn y cs)

/-- **Arity contradiction**: a fixed-point polynomial cannot weakly reduce, after `zs`, to a
`x`-headed spine with an arity other than `zs.length + 1`. -/
theorem arity_contra (P : Tm) (zs l : List Tm) (hl : l.length ≠ zs.length + 1)
    (hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) zs) (apps (Tm.var 0) l))
    (hY : betaEtaConv (toLam (Tm.app P (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app P (Tm.var 0))))) : False := by
  have hc := (betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY zs)
  have h2 := hsp_toLam_apps_var 0 (Tm.app P (Tm.var 0) :: zs)
  simp only [apps] at h2
  have := ((hsp_toLam_apps_var 0 l).betaEtaConv h2 hc).2
  simp at this
  omega

/-- `M ∘ B` is not a βη fixed-point combinator. -/
theorem polyMB_not_fixedPoint :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ [⟨0, .B⟩]) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ [⟨0, .B⟩]) (Tm.var 0)))) := by
  intro hY
  refine arity_contra _ [Tm.var 1] [Tm.app (Tm.app Tm.B (Tm.var 0)) (Tm.var 1)] (by simp) ?_ hY
  refine (comp_action_apps Tm.M Tm.B (Tm.var 0) _).trans ?_
  refine (Tm.WEq.apps (.step (.m _)) _).trans ?_
  exact .step (.b _ _ _)

/-- `M ∘ M` is not a βη fixed-point combinator. -/
theorem polyMM_not_fixedPoint :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ [⟨0, .M⟩]) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ [⟨0, .M⟩]) (Tm.var 0)))) := by
  intro hY
  refine arity_contra _ [] [Tm.var 0, Tm.app (Tm.var 0) (Tm.var 0)] (by simp) ?_ hY
  refine (comp_action Tm.M Tm.M (Tm.var 0)).trans ?_
  refine (Tm.WEq.step (.m _)).trans ?_
  refine (Tm.WEq.appL (.step (.m _)) _).trans ?_
  exact Tm.WEq.appR _ (.step (.m _))

/-- `M ∘ B M` is not a βη fixed-point combinator. -/
theorem polyMBM_not_fixedPoint :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ [⟨1, .M⟩]) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ [⟨1, .M⟩]) (Tm.var 0)))) := by
  intro hY
  set V := Tm.app (Tm.app Tm.B Tm.M) (Tm.var 0)
  refine arity_contra _ [] [V, Tm.app (Tm.var 0) V] (by simp) ?_ hY
  refine (comp_action Tm.M (Tm.app Tm.B Tm.M) (Tm.var 0)).trans ?_
  refine (Tm.WEq.step (.m _)).trans ?_
  refine (Tm.WEq.step (.b _ _ _)).trans ?_
  exact .step (.m _)

/-- The fresh variables `var 1, …, var k`. -/
def fresh (k : ℕ) : List Tm := (List.range k).map (fun i => Tm.var (i + 1))

theorem fresh_succ (k : ℕ) : fresh (k + 1) = fresh k ++ [Tm.var (k + 1)] := by
  simp [fresh, List.range_succ]

theorem fresh_succ' (k : ℕ) :
    fresh (k + 1) = Tm.var 1 :: (List.range k).map (fun i => Tm.var (i + 2)) := by
  simp [fresh, List.range_succ_eq_map, Function.comp]

/-- The weak unfolding of `M ∘ B ∘ m₃ ∘ …` on a first fresh argument. -/
theorem secondB_unfold (m3 : Mono) (ps : List Mono) (z1 : Tm) (rest : List Tm) :
    ∃ u : Tm, Tm.WEq (apps (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: m3 :: ps)) (Tm.var 0)) (z1 :: rest))
      (apps (Tm.app m3.tm u)
        (Tm.app (Tm.app Tm.B (Tm.app (polyTm m3 ps) (Tm.var 0))) z1 :: rest)) ∧
      ∀ a b : ℕ, 0 < b → GY a b (toLam u) := by
  obtain ⟨u, hu, hGY⟩ := poly_tail m3 ps
  refine ⟨u, ?_, hGY⟩
  set S := polyTm m3 ps
  refine (comp_action_apps Tm.M (comp Tm.B S) (Tm.var 0) _).trans ?_
  refine (Tm.WEq.apps (.step (.m _)) _).trans ?_
  have h1 : Tm.WEq (Tm.app (comp Tm.B S) (Tm.var 0)) (Tm.app Tm.B (Tm.app S (Tm.var 0))) :=
    comp_action _ _ _
  refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) (z1 :: rest)).trans ?_
  show Tm.WEq (apps (Tm.app (Tm.app (Tm.app Tm.B _) _) z1) rest) _
  refine (Tm.WEq.apps (.step (.b _ _ _)) rest).trans ?_
  exact Tm.WEq.apps (Tm.WEq.appL hu _) rest

theorem gy_U (m : Mono) (ps : List Mono) (a b : ℕ) (hb : 0 < b) :
    GY a b (toLam (Tm.app (polyTm m ps) (Tm.var 0))) :=
  .app (GY.toLam_closed (polyTm_isBMI _ _)) (.var (by omega))

/-- **`M ∘ B ∘ B ∘ …` is not a βη fixed-point combinator.** -/
theorem thirdB_B_not_fixedPoint (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .B⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .B⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .B⟩ :: ps)
  set U := Tm.app (polyTm ⟨0, .B⟩ ps) (Tm.var 0)
  obtain ⟨u, hu, hGY⟩ := secondB_unfold ⟨0, .B⟩ ps (Tm.var 1) [Tm.var 2]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) ([] ++ [Tm.var 1, Tm.var 2]))
      (Tm.app u (Tm.app U (Tm.app (Tm.var 1) (Tm.var 2)))) := by
    refine hu.trans ?_
    refine (Tm.WEq.step (.b _ _ _)).trans ?_
    exact Tm.WEq.appR _ (.step (.b _ _ _))
  refine gy_contra 0 P [] _ ?_ ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  exact .app (hGY _ _ (by omega)) (.app (gy_U _ _ _ _ (by omega)) .pair)

/-- **`M ∘ B ∘ Bᵃ⁺¹ B ∘ …` is not a βη fixed-point combinator.** -/
theorem thirdB_BB_not_fixedPoint (a : ℕ) (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨a + 1, .B⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨a + 1, .B⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨a + 1, .B⟩ :: ps)
  set U := Tm.app (polyTm ⟨a + 1, .B⟩ ps) (Tm.var 0)
  set tl : List Tm := (List.range a).map (fun i => Tm.var (i + 2)) with htl
  obtain ⟨u, hu, hGY⟩ := secondB_unfold ⟨a + 1, .B⟩ ps (Tm.var 1)
    (tl ++ [Tm.var (a + 2), Tm.var (a + 3)])
  have hlen : (Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl).length = a + 1 := by simp [htl]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh (a + 1) ++ [Tm.var (a + 2), Tm.var (a + 3)]))
      (apps u ((Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl) ++
        [Tm.app (Tm.var (a + 2)) (Tm.var (a + 3))])) := by
    rw [fresh_succ', List.cons_append]
    refine hu.trans ?_
    have := bpowB_action (a + 1) u (Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl) hlen
      (Tm.var (a + 2)) (Tm.var (a + 3)) []
    simp only [List.cons_append] at this
    exact this
  refine gy_contra (a + 1) P (fresh (a + 1)) _ ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  refine GY.toLam_apps (hGY _ _ (by omega)) ?_
  intro z hz
  simp only [List.cons_append, List.mem_cons, List.mem_append, htl, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | ⟨i, hi, rfl⟩ | rfl
  · exact .app (.app (GY.toLam_closed .B) (gy_U _ _ _ _ (by omega))) (.var (by omega))
  · exact .var (by omega)
  · exact .pair

/-- **`M ∘ B ∘ Bᵃ⁺¹ M ∘ …` is not a βη fixed-point combinator.** -/
theorem thirdB_BM_not_fixedPoint (a : ℕ) (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨a + 1, .M⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨a + 1, .M⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨a + 1, .M⟩ :: ps)
  set U := Tm.app (polyTm ⟨a + 1, .M⟩ ps) (Tm.var 0)
  set tl : List Tm := (List.range a).map (fun i => Tm.var (i + 2)) with htl
  obtain ⟨u, hu, -⟩ := secondB_unfold ⟨a + 1, .M⟩ ps (Tm.var 1) tl
  set W := apps u (Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl)
  have hlen : (Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl).length = a + 1 := by simp [htl]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1)])) (Tm.app W W) := by
    rw [← fresh_succ, fresh_succ']
    exact hu.trans (bpowM_action (a + 1) u _ hlen)
  refine occ_contra a P (polyTm_isBMI _ _) (Tm.app W W) ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  have hW : 1 ≤ occL (a + 1) (toLam W) := by
    cases a with
    | zero =>
      simp only [W, occL_toLam_apps, htl, List.map_cons, List.sum_cons, toLam, occL, ↓reduceIte]
      omega
    | succ a =>
      simp only [W, occL_toLam_apps, htl, List.range_succ, List.map_append, List.map_cons,
        List.sum_cons, List.sum_append, List.map_nil, List.sum_nil, toLam, occL, ↓reduceIte]
      omega
  simp only [toLam, occL]
  omega

/-- The weak unfolding of `M ∘ M ∘ m₃ ∘ …` and `M ∘ B M ∘ m₃ ∘ …`: two arguments `g`, `h` (built
from `x` and closed terms) are placed in front of the fresh arguments. -/
theorem secondM_unfold (m₂ m3 : Mono) (ps : List Mono) (hm : m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩)
    (zs : List Tm) :
    ∃ u g h : Tm, Tm.WEq (apps (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m3 :: ps)) (Tm.var 0)) zs)
      (apps (Tm.app m3.tm u) (g :: h :: zs)) ∧
      ∀ a b : ℕ, 0 < b → GY a b (toLam u) ∧ GY a b (toLam g) ∧ GY a b (toLam h) := by
  obtain ⟨u, hu, hGY⟩ := poly_tail m3 ps
  set S := polyTm m3 ps
  set U := Tm.app S (Tm.var 0)
  have hU : ∀ a b : ℕ, 0 < b → GY a b (toLam U) := fun a b hb => gy_U _ _ _ _ hb
  rcases hm with rfl | rfl
  · refine ⟨u, U, Tm.app U U, ?_, fun a b hb => ⟨hGY a b hb, hU a b hb, .app (hU a b hb) (hU a b hb)⟩⟩
    have h1 : Tm.WEq (Tm.app (comp Tm.M S) (Tm.var 0)) (Tm.app U U) :=
      (comp_action _ _ _).trans (.step (.m _))
    refine (Tm.WEq.apps (comp_action _ _ _) zs).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) zs).trans ?_
    refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) zs).trans ?_
    show Tm.WEq (apps U (U :: Tm.app U U :: zs)) _
    exact Tm.WEq.apps (Tm.WEq.appL hu _) _
  · set V := Tm.app (Tm.app Tm.B Tm.M) U
    have hV : ∀ a b : ℕ, 0 < b → GY a b (toLam V) := fun a b hb =>
      .app (GY.toLam_closed (.app .B .M)) (hU a b hb)
    refine ⟨u, V, Tm.app U V, ?_, fun a b hb => ⟨hGY a b hb, hV a b hb, .app (hU a b hb) (hV a b hb)⟩⟩
    have h1 : Tm.WEq (Tm.app (comp (Tm.app Tm.B Tm.M) S) (Tm.var 0)) V := comp_action _ _ _
    refine (Tm.WEq.apps (comp_action _ _ _) zs).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) zs).trans ?_
    refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) zs).trans ?_
    refine (Tm.WEq.apps (.step (.b _ _ _)) zs).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) zs).trans ?_
    show Tm.WEq (apps U (V :: Tm.app U V :: zs)) _
    exact Tm.WEq.apps (Tm.WEq.appL hu _) _

/-- **`M ∘ m₂ ∘ Bᵃ⁺² B ∘ …` with `m₂ ∈ {M, B M}` is not a βη fixed-point combinator.** -/
theorem thirdM_BB_not_fixedPoint (m₂ : Mono) (hm : m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩) (a : ℕ)
    (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: ⟨a + 2, .B⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: ⟨a + 2, .B⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (m₂ :: ⟨a + 2, .B⟩ :: ps)
  obtain ⟨u, g, h, hu, hGY⟩ := secondM_unfold m₂ ⟨a + 2, .B⟩ ps hm
    (fresh a ++ [Tm.var (a + 1), Tm.var (a + 2)])
  have hlen : (g :: h :: fresh a).length = a + 2 := by simp [fresh]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1), Tm.var (a + 2)]))
      (apps u ((g :: h :: fresh a) ++ [Tm.app (Tm.var (a + 1)) (Tm.var (a + 2))])) := by
    refine hu.trans ?_
    have := bpowB_action (a + 2) u (g :: h :: fresh a) hlen (Tm.var (a + 1)) (Tm.var (a + 2)) []
    simp only [List.cons_append] at this ⊢
    exact this
  refine gy_contra a P (fresh a) _ ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  obtain ⟨h1, h2, h3⟩ := hGY (a + 1) (a + 2) (by omega)
  refine GY.toLam_apps h1 ?_
  intro z hz
  simp only [List.cons_append, List.mem_cons, List.mem_append, fresh, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | ⟨i, hi, rfl⟩ | rfl
  · exact h2
  · exact h3
  · exact .var (by omega)
  · exact .pair

/-- **`M ∘ m₂ ∘ Bᵃ⁺³ M ∘ …` with `m₂ ∈ {M, B M}` is not a βη fixed-point combinator.** -/
theorem thirdM_BM_not_fixedPoint (m₂ : Mono) (hm : m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩) (a : ℕ)
    (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: ⟨a + 3, .M⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: ⟨a + 3, .M⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (m₂ :: ⟨a + 3, .M⟩ :: ps)
  obtain ⟨u, g, h, hu, -⟩ := secondM_unfold m₂ ⟨a + 3, .M⟩ ps hm (fresh a ++ [Tm.var (a + 1)])
  set W := apps u (g :: h :: (fresh a ++ [Tm.var (a + 1)]))
  have hlen : (g :: h :: (fresh a ++ [Tm.var (a + 1)])).length = a + 3 := by simp [fresh]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1)])) (Tm.app W W) :=
    hu.trans (bpowM_action (a + 3) u _ hlen)
  refine occ_contra a P (polyTm_isBMI _ _) (Tm.app W W) ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  have hW : 1 ≤ occL (a + 1) (toLam W) := by
    simp only [W, occL_toLam_apps, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, List.map_nil, List.sum_nil, toLam, occL, ↓reduceIte]
    omega
  simp only [toLam, occL]
  omega

/-- **The first three monomials of a βη fixed-point polynomial**: `PolyFiveOne` has a witness
`M ∘ m₂ ∘ m₃ ∘ …` without base-`I` monomials, with at least three monomials, and with
`(m₂, m₃) = (B, M)`, or `m₂ ∈ {M, B M}` and `m₃ ∈ {B, B B, M, B M, B² M}`. -/
theorem polyFiveOne_third (h : PolyFiveOne) :
    ∃ (m₂ m₃ : Mono) (ps : List Mono),
      ((m₂ = ⟨0, .B⟩ ∧ m₃ = ⟨0, .M⟩) ∨
        ((m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩) ∧
          (m₃ = ⟨0, .B⟩ ∨ m₃ = ⟨1, .B⟩ ∨ m₃ = ⟨0, .M⟩ ∨ m₃ = ⟨1, .M⟩ ∨ m₃ = ⟨2, .M⟩))) ∧
      (∀ q ∈ (⟨0, .M⟩ : Mono) :: m₂ :: m₃ :: ps, q.base ≠ .I) ∧
      betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: ps)) (Tm.var 0)))
        (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: ps)) (Tm.var 0)))) := by
  obtain ⟨m₂, ps, hm2, hI, hfix⟩ := polyFiveOne_second h
  cases ps with
  | nil =>
    rcases hm2 with rfl | rfl | rfl
    · exact (polyMB_not_fixedPoint hfix).elim
    · exact (polyMM_not_fixedPoint hfix).elim
    · exact (polyMBM_not_fixedPoint hfix).elim
  | cons m₃ ps =>
    obtain ⟨k, b⟩ := m₃
    cases b with
    | I => exact (hI ⟨k, .I⟩ (by simp) rfl).elim
    | B =>
      rcases hm2 with rfl | hm
      · cases k with
        | zero => exact (thirdB_B_not_fixedPoint ps hfix).elim
        | succ a => exact (thirdB_BB_not_fixedPoint a ps hfix).elim
      · match k with
        | 0 => exact ⟨_, _, ps, .inr ⟨hm, .inl rfl⟩, hI, hfix⟩
        | 1 => exact ⟨_, _, ps, .inr ⟨hm, .inr (.inl rfl)⟩, hI, hfix⟩
        | a + 2 => exact (thirdM_BB_not_fixedPoint m₂ hm a ps hfix).elim
    | M =>
      rcases hm2 with rfl | hm
      · cases k with
        | zero => exact ⟨_, _, ps, .inl ⟨rfl, rfl⟩, hI, hfix⟩
        | succ a => exact (thirdB_BM_not_fixedPoint a ps hfix).elim
      · match k with
        | 0 => exact ⟨_, _, ps, .inr ⟨hm, .inr (.inr (.inl rfl))⟩, hI, hfix⟩
        | 1 => exact ⟨_, _, ps, .inr ⟨hm, .inr (.inr (.inr (.inl rfl)))⟩, hI, hfix⟩
        | 2 => exact ⟨_, _, ps, .inr ⟨hm, .inr (.inr (.inr (.inr rfl)))⟩, hI, hfix⟩
        | a + 3 => exact (thirdM_BM_not_fixedPoint m₂ hm a ps hfix).elim

/-! ### The fourth monomial in the branch `M ∘ B ∘ M ∘ …` -/

/-- The weak unfolding of `M ∘ B ∘ M ∘ m₄ ∘ …` on a first fresh argument. -/
theorem thirdBM_unfold (m4 : Mono) (ps : List Mono) (z1 : Tm) (rest : List Tm) :
    ∃ w : Tm, Tm.WEq
      (apps (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: m4 :: ps)) (Tm.var 0)) (z1 :: rest))
      (apps (Tm.app m4.tm w) (Tm.app (polyTm m4 ps) (Tm.var 0) ::
        Tm.app (Tm.app Tm.B (Tm.app (polyTm ⟨0, .M⟩ (m4 :: ps)) (Tm.var 0))) z1 :: rest)) ∧
      ∀ a b : ℕ, 0 < b → GY a b (toLam w) := by
  obtain ⟨w, hw, hGY⟩ := poly_tail m4 ps
  refine ⟨w, ?_, hGY⟩
  set S4 := polyTm m4 ps
  set S := polyTm ⟨0, .M⟩ (m4 :: ps)
  refine (comp_action_apps Tm.M (comp Tm.B S) (Tm.var 0) _).trans ?_
  refine (Tm.WEq.apps (.step (.m _)) _).trans ?_
  have h1 : Tm.WEq (Tm.app (comp Tm.B S) (Tm.var 0)) (Tm.app Tm.B (Tm.app S (Tm.var 0))) :=
    comp_action _ _ _
  refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) (z1 :: rest)).trans ?_
  show Tm.WEq (apps (Tm.app (Tm.app (Tm.app Tm.B _) _) z1) rest) _
  refine (Tm.WEq.apps (.step (.b _ _ _)) rest).trans ?_
  have h2 : Tm.WEq (Tm.app S (Tm.var 0)) (Tm.app (Tm.app S4 (Tm.var 0)) (Tm.app S4 (Tm.var 0))) :=
    (comp_action _ _ _).trans (.step (.m _))
  refine (Tm.WEq.apps (Tm.WEq.appL h2 _) rest).trans ?_
  show Tm.WEq (apps (Tm.app S4 (Tm.var 0)) (Tm.app S4 (Tm.var 0) :: _ :: rest)) _
  exact Tm.WEq.apps (Tm.WEq.appL hw _) _

/-- `M ∘ B ∘ M` is not a βη fixed-point combinator. -/
theorem polyMBM'_not_fixedPoint :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ [⟨0, .B⟩, ⟨0, .M⟩]) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ [⟨0, .B⟩, ⟨0, .M⟩]) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ [⟨0, .B⟩, ⟨0, .M⟩]
  set c := Tm.app (Tm.app Tm.B (Tm.app Tm.M (Tm.var 0))) (Tm.var 1)
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) [Tm.var 1]) (apps (Tm.var 0) [Tm.var 0, c]) := by
    refine (comp_action_apps Tm.M (comp Tm.B Tm.M) (Tm.var 0) _).trans ?_
    refine (Tm.WEq.apps (.step (.m _)) _).trans ?_
    have h1 : Tm.WEq (Tm.app (comp Tm.B Tm.M) (Tm.var 0)) (Tm.app Tm.B (Tm.app Tm.M (Tm.var 0))) :=
      comp_action _ _ _
    refine (Tm.WEq.apps ((Tm.WEq.appL h1 _).trans (Tm.WEq.appR _ h1)) [Tm.var 1]).trans ?_
    refine (Tm.WEq.step (.b _ _ _)).trans ?_
    exact Tm.WEq.appL (.step (.m _)) _
  have hc := (betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY [Tm.var 1])
  have hc' : betaEtaConv (lamK 0 (spn 0 [toLam c, .var 0]))
      (lamK 0 (spn 0 [.var 1, toLam (Tm.app P (Tm.var 0))])) := by
    simpa [apps, toLam, lamK, spn] using hc
  obtain ⟨-, hf⟩ := lamK_spn_betaEtaConv hc'
  cases hf with
  | cons _ hf2 =>
    cases hf2 with
    | cons h0 _ =>
      have := (HSp.neu (NSp.var 0)).betaEtaConv
        (HSp.neu (NSp.app _ (NSp.var 0))) (h0.trans hY)
      simp at this

/-- **`M ∘ B ∘ M ∘ B B ∘ …` is not a βη fixed-point combinator.** -/
theorem fourthBM_B1_not_fixedPoint (ps : List Mono) :
    ¬ betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨1, .B⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨1, .B⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨1, .B⟩ :: ps)
  set U := Tm.app (polyTm ⟨0, .M⟩ (⟨1, .B⟩ :: ps)) (Tm.var 0)
  set u' := Tm.app (polyTm ⟨1, .B⟩ ps) (Tm.var 0)
  obtain ⟨w, hw, hGY⟩ := thirdBM_unfold ⟨1, .B⟩ ps (Tm.var 1) [Tm.var 2]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) ([] ++ [Tm.var 1, Tm.var 2]))
      (Tm.app (Tm.app w u') (Tm.app U (Tm.app (Tm.var 1) (Tm.var 2)))) := by
    refine hw.trans ?_
    have := bpowB_action 1 w [u'] rfl (Tm.app (Tm.app Tm.B U) (Tm.var 1)) (Tm.var 2) []
    refine this.trans ?_
    exact Tm.WEq.appR _ (.step (.b _ _ _))
  refine gy_contra 0 P [] _ ?_ ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  exact .app (.app (hGY _ _ (by omega)) (gy_U _ _ _ _ (by omega)))
    (.app (gy_U _ _ _ _ (by omega)) .pair)

/-- **`M ∘ B ∘ M ∘ Bᵃ⁺² B ∘ …` is not a βη fixed-point combinator.** -/
theorem fourthBM_BB_not_fixedPoint (a : ℕ) (ps : List Mono) :
    ¬ betaEtaConv
      (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨a + 2, .B⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨a + 2, .B⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨a + 2, .B⟩ :: ps)
  set U := Tm.app (polyTm ⟨0, .M⟩ (⟨a + 2, .B⟩ :: ps)) (Tm.var 0)
  set u' := Tm.app (polyTm ⟨a + 2, .B⟩ ps) (Tm.var 0)
  set tl : List Tm := (List.range a).map (fun i => Tm.var (i + 2)) with htl
  obtain ⟨w, hw, hGY⟩ := thirdBM_unfold ⟨a + 2, .B⟩ ps (Tm.var 1)
    (tl ++ [Tm.var (a + 2), Tm.var (a + 3)])
  have hlen : (u' :: Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl).length = a + 2 := by simp [htl]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh (a + 1) ++ [Tm.var (a + 2), Tm.var (a + 3)]))
      (apps w ((u' :: Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl) ++
        [Tm.app (Tm.var (a + 2)) (Tm.var (a + 3))])) := by
    rw [fresh_succ', List.cons_append]
    refine hw.trans ?_
    have := bpowB_action (a + 2) w (u' :: Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl) hlen
      (Tm.var (a + 2)) (Tm.var (a + 3)) []
    simp only [List.cons_append] at this
    exact this
  refine gy_contra (a + 1) P (fresh (a + 1)) _ ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  refine GY.toLam_apps (hGY _ _ (by omega)) ?_
  intro z hz
  simp only [List.cons_append, List.mem_cons, List.mem_append, htl, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | ⟨i, hi, rfl⟩ | rfl
  · exact gy_U _ _ _ _ (by omega)
  · exact .app (.app (GY.toLam_closed .B) (gy_U _ _ _ _ (by omega))) (.var (by omega))
  · exact .var (by omega)
  · exact .pair

/-- **`M ∘ B ∘ M ∘ Bᵃ⁺² M ∘ …` is not a βη fixed-point combinator.** -/
theorem fourthBM_BM_not_fixedPoint (a : ℕ) (ps : List Mono) :
    ¬ betaEtaConv
      (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨a + 2, .M⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0)
        (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨a + 2, .M⟩ :: ps)) (Tm.var 0)))) := by
  intro hY
  set P := polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ⟨a + 2, .M⟩ :: ps)
  set U := Tm.app (polyTm ⟨0, .M⟩ (⟨a + 2, .M⟩ :: ps)) (Tm.var 0)
  set u' := Tm.app (polyTm ⟨a + 2, .M⟩ ps) (Tm.var 0)
  set tl : List Tm := (List.range a).map (fun i => Tm.var (i + 2)) with htl
  obtain ⟨w, hw, -⟩ := thirdBM_unfold ⟨a + 2, .M⟩ ps (Tm.var 1) tl
  set W := apps w (u' :: Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl)
  have hlen : (u' :: Tm.app (Tm.app Tm.B U) (Tm.var 1) :: tl).length = a + 2 := by simp [htl]
  have hL : Tm.WEq (apps (Tm.app P (Tm.var 0)) (fresh a ++ [Tm.var (a + 1)])) (Tm.app W W) := by
    rw [← fresh_succ, fresh_succ']
    exact hw.trans (bpowM_action (a + 2) w _ hlen)
  refine occ_contra a P (polyTm_isBMI _ _) (Tm.app W W) ?_
    ((betaEtaConv_symm (toLam_weq hL)).trans (conv_apps hY _))
  have hW : 1 ≤ occL (a + 1) (toLam W) := by
    cases a with
    | zero =>
      simp only [W, occL_toLam_apps, htl, List.map_cons, List.sum_cons, toLam, occL, ↓reduceIte]
      omega
    | succ a =>
      simp only [W, occL_toLam_apps, htl, List.range_succ, List.map_append, List.map_cons,
        List.sum_cons, List.sum_append, List.map_nil, List.sum_nil, toLam, occL, ↓reduceIte]
      omega
  simp only [toLam, occL]
  omega

/-- **The fourth monomial in the branch `M ∘ B ∘ M ∘ …`**: it exists and is `B`, `M` or `B M`. -/
theorem fixedPoint_BM_fourth (ps : List Mono) (hI : ∀ q ∈ ps, q.base ≠ .I)
    (hfix : betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ps)) (Tm.var 0)))
      (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (⟨0, .B⟩ :: ⟨0, .M⟩ :: ps)) (Tm.var 0))))) :
    ∃ (m₄ : Mono) (ps' : List Mono), ps = m₄ :: ps' ∧
      (m₄ = ⟨0, .B⟩ ∨ m₄ = ⟨0, .M⟩ ∨ m₄ = ⟨1, .M⟩) := by
  cases ps with
  | nil => exact (polyMBM'_not_fixedPoint hfix).elim
  | cons m₄ ps =>
    obtain ⟨k, b⟩ := m₄
    cases b with
    | I => exact (hI ⟨k, .I⟩ (by simp) rfl).elim
    | B =>
      match k with
      | 0 => exact ⟨_, ps, rfl, .inl rfl⟩
      | 1 => exact (fourthBM_B1_not_fixedPoint ps hfix).elim
      | a + 2 => exact (fourthBM_BB_not_fixedPoint a ps hfix).elim
    | M =>
      match k with
      | 0 => exact ⟨_, ps, rfl, .inr (.inl rfl)⟩
      | 1 => exact ⟨_, ps, rfl, .inr (.inr rfl)⟩
      | a + 2 => exact (fourthBM_BM_not_fixedPoint a ps hfix).elim

/-- **The head of a βη fixed-point polynomial, up to the third or fourth monomial**:
`PolyFiveOne` has a witness without base-`I` monomials of one of the forms
* `M ∘ B ∘ M ∘ m₄ ∘ …` with `m₄ ∈ {B, M, B M}`, or
* `M ∘ m₂ ∘ m₃ ∘ …` with `m₂ ∈ {M, B M}` and `m₃ ∈ {B, B B, M, B M, B² M}`. -/
theorem polyFiveOne_fourth (h : PolyFiveOne) :
    ∃ (m₂ m₃ : Mono) (ps : List Mono),
      ((m₂ = ⟨0, .B⟩ ∧ m₃ = ⟨0, .M⟩ ∧ ∃ (m₄ : Mono) (ps' : List Mono), ps = m₄ :: ps' ∧
          (m₄ = ⟨0, .B⟩ ∨ m₄ = ⟨0, .M⟩ ∨ m₄ = ⟨1, .M⟩)) ∨
        ((m₂ = ⟨0, .M⟩ ∨ m₂ = ⟨1, .M⟩) ∧
          (m₃ = ⟨0, .B⟩ ∨ m₃ = ⟨1, .B⟩ ∨ m₃ = ⟨0, .M⟩ ∨ m₃ = ⟨1, .M⟩ ∨ m₃ = ⟨2, .M⟩))) ∧
      (∀ q ∈ (⟨0, .M⟩ : Mono) :: m₂ :: m₃ :: ps, q.base ≠ .I) ∧
      betaEtaConv (toLam (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: ps)) (Tm.var 0)))
        (toLam (Tm.app (Tm.var 0) (Tm.app (polyTm ⟨0, .M⟩ (m₂ :: m₃ :: ps)) (Tm.var 0)))) := by
  obtain ⟨m₂, m₃, ps, hm | hm, hI, hfix⟩ := polyFiveOne_third h
  · obtain ⟨rfl, rfl⟩ := hm
    exact ⟨_, _, ps, .inl ⟨rfl, rfl, fixedPoint_BM_fourth ps
      (fun q hq => hI q (by simp [hq])) hfix⟩, hI, hfix⟩
  · exact ⟨m₂, m₃, ps, .inr hm, hI, hfix⟩

end TLCA4
