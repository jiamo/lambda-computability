/-
# Böhm out against an arbitrary term

`Start/BohmEta.lean` separates two *Böhm trees of normal forms* that are not η-equal.  Full
abstraction of `D∞` needs more: an *approximant* — a finite term which may contain `Ω` — has to be
separated from an **arbitrary** term.  Two things change.  The nodes of the second object are no
longer given by a tree but have to be produced by head reduction, and the comparison can now fail
in a new way, by the second term having no head normal form at all where the first one has a node.

This module carries out that generalisation.

* `Lambda.TagFail` — a *finite failure witness* for the comparison of two terms, tagged as in
  `Start/BohmEta.lean`: along a path on which the η-expanded nodes agree, either the second term
  head-diverges, or the two η-expanded nodes have different head tags or different arities.
* `Lambda.reduces_csub_node_eta` — one step of the descent, now driven by a head normal form of
  the term rather than by the structure of a tree.
* `Lambda.sepDiv_of_tagFail` — **the Böhm-out**: a failure witness yields a list of closed
  arguments on which the first term head-converges and the second head-diverges
  (`Lambda.SepDiv`).  The tag bound `B` and the arity bound `K` are produced *bottom-up* from the
  witness, since an arbitrary term gives no a priori bound on the arities met along the path.
-/

import Start.HeadSpine
import Start.BohmEta

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Reduction and substitution -/

theorem step_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) {M M' : Lambda}
    (h : Lambda.step M M') : ∀ k : ℕ, Lambda.step (csub ρ k M) (csub ρ k M') := by
  induction h with
  | beta t₁ t₂ =>
      intro k
      rw [csub_app, csub_lam hρ, csub_subst hρ t₁ t₂ 0 k (Nat.zero_le k)]
      exact Lambda.step.beta _ _
  | app_left _ _ _ _ ih => intro k; exact Lambda.step.app_left _ _ _ (ih k)
  | app_right _ _ _ _ ih => intro k; exact Lambda.step.app_right _ _ _ (ih k)
  | lam _ _ _ ih =>
      intro k
      rw [csub_lam hρ, csub_lam hρ]
      exact Lambda.step.lam _ _ (ih (k + 1))

theorem reduces_csub {ρ : ℕ → Lambda} (hρ : ∀ j, Lambda.IsClosed (ρ j)) {M M' : Lambda}
    (h : Lambda.reduces M M') : ∀ k : ℕ, Lambda.reduces (csub ρ k M) (csub ρ k M') := by
  induction h with
  | refl t => intro k; exact .refl _
  | step t₁ t₂ t₃ hs _ ih => intro k; exact .step _ _ _ (step_csub hρ hs k) (ih k)

/-! ## The η-expanded arguments of a node -/

/-- The `r`-th argument of a node η-expanded by `e`: one of the arguments actually present, or
else the variable introduced by the η-expansion. -/
def argTermOf (as : List Lambda) (r : ℕ) : Lambda :=
  if h : r < as.length then as[r] else Lambda.var 0

/-- The tag function to be used with `Lambda.argTermOf`; `k` is the number of arguments actually
present. -/
def argEnvT (base : ℕ) (τ : ℕ → ℕ) (b e k r : ℕ) : ℕ → ℕ :=
  if r < k then expEnv base τ b e else fun _ => base + (k + e - 1 - r)

theorem argEnvT_lt {B base b e k r : ℕ} {τ : ℕ → ℕ} (hτ : ∀ j, τ j < B) (hr : r < k + e)
    (hbB : base + (b + e) ≤ B) : ∀ j, argEnvT base τ b e k r j < B := by
  intro j
  rw [argEnvT]
  by_cases hlt : r < k
  · rw [if_pos hlt, expEnv]
    by_cases hj : j < b
    · rw [if_pos hj]; omega
    · rw [if_neg hj]; exact hτ _
  · rw [if_neg hlt]; omega

/-! ## Failure witnesses -/

/-- `TagFail base τ₁ M τ₂ N`: along a path on which the η-expanded nodes of `M` and `N` agree,
either `N` head-diverges where `M` has a node, or the η-expanded nodes have different head tags
or different arities.  This is the finite witness that `M` is *not* below `N`. -/
inductive TagFail : ℕ → (ℕ → ℕ) → Lambda → (ℕ → ℕ) → Lambda → Prop
  | nohnf {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {M N : Lambda} {b₁ h₁ : ℕ} {as₁ : List Lambda}
      (hM : Lambda.reduces M (lamN b₁ (appList (Lambda.var h₁) as₁)))
      (hN : ¬ HasHnf N) : TagFail base τ₁ M τ₂ N
  | root {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {M N : Lambda} {b₁ h₁ e₁ b₂ h₂ e₂ : ℕ}
      {as₁ as₂ : List Lambda}
      (hM : Lambda.reduces M (lamN b₁ (appList (Lambda.var h₁) as₁)))
      (hN : Lambda.reduces N (lamN b₂ (appList (Lambda.var h₂) as₂)))
      (hmin : e₁ = 0 ∨ e₂ = 0) (hm : b₁ + e₁ = b₂ + e₂)
      (hne : headTag base τ₁ b₁ h₁ e₁ ≠ headTag base τ₂ b₂ h₂ e₂ ∨
        as₁.length + e₁ ≠ as₂.length + e₂) :
      TagFail base τ₁ M τ₂ N
  | arg {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {M N : Lambda} {b₁ h₁ e₁ b₂ h₂ e₂ r : ℕ}
      {as₁ as₂ : List Lambda}
      (hM : Lambda.reduces M (lamN b₁ (appList (Lambda.var h₁) as₁)))
      (hN : Lambda.reduces N (lamN b₂ (appList (Lambda.var h₂) as₂)))
      (hmin : e₁ = 0 ∨ e₂ = 0) (hm : b₁ + e₁ = b₂ + e₂)
      (hhead : headTag base τ₁ b₁ h₁ e₁ = headTag base τ₂ b₂ h₂ e₂)
      (hlen : as₁.length + e₁ = as₂.length + e₂) (hr : r < as₁.length + e₁)
      (hd : TagFail (base + (b₁ + e₁)) (argEnvT base τ₁ b₁ e₁ as₁.length r) (argTermOf as₁ r)
        (argEnvT base τ₂ b₂ e₂ as₂.length r) (argTermOf as₂ r)) :
      TagFail base τ₁ M τ₂ N

/-! ## One step of the descent -/

theorem isClosed_csub_mem_map {B K : ℕ} {σ : ℕ → ℕ} (hB : 0 < B) {as : List Lambda} {a : Lambda}
    (ha : a ∈ as.map (csub (tagEnv B K σ) 0)) : Lambda.IsClosed a := by
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 ha
  exact isClosed_csub_zero (isClosed_tagEnv_pos hB σ) z

theorem isClosed_mem_argsFor_baseTags {B K base e : ℕ} (hB : 0 < B) {a : Lambda}
    (ha : a ∈ argsFor (baseTags B K base) e) : Lambda.IsClosed a := by
  obtain ⟨k, -, rfl⟩ := mem_argsFor ha
  exact isClosed_baseTags hB k

theorem isClosed_expArgs {B K base b e : ℕ} {σ : ℕ → ℕ} (hB : 0 < B) {as : List Lambda} :
    ∀ a ∈ (as.map (csub (tagEnv B K (expEnv base σ b e)) 0)) ++ argsFor (baseTags B K base) e,
      Lambda.IsClosed a := by
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · exact isClosed_csub_mem_map hB ha
  · exact isClosed_mem_argsFor_baseTags hB ha

@[simp] theorem length_expArgs {B K base b e : ℕ} {σ : ℕ → ℕ} {as : List Lambda} :
    ((as.map (csub (tagEnv B K (expEnv base σ b e)) 0)) ++
      argsFor (baseTags B K base) e).length = as.length + e := by
  simp

/-- **One step of the descent.**  Feeding the `b + e` tagged arguments of a node to the
instantiated term exposes the tag of the head of a head normal form of the term, applied to the
instantiated arguments of that head normal form followed by the `e` tags of the η-expansion. -/
theorem reduces_csub_node_eta {B K base b h e : ℕ} {as : List Lambda} {τ : ℕ → ℕ} (hB : 0 < B)
    {M : Lambda} (hM : Lambda.reduces M (lamN b (appList (Lambda.var h) as))) :
    Lambda.reduces (appList (csub (tagEnv B K τ) 0 M) (argsFor (baseTags B K base) (b + e)))
      (appList (tagTuple B K (headTag base τ b h e))
        ((as.map (csub (tagEnv B K (expEnv base τ b e)) 0)) ++
          argsFor (baseTags B K base) e)) := by
  have hρ : ∀ j, Lambda.IsClosed (tagEnv B K τ j) := isClosed_tagEnv_pos hB τ
  have hg : ∀ j, Lambda.IsClosed (baseTags B K base (j + e)) := fun j => isClosed_baseTags hB _
  have hstart : Lambda.reduces (csub (tagEnv B K τ) 0 M)
      (lamN b (csub (tagEnv B K τ) b (appList (Lambda.var h) as))) := by
    have := reduces_csub hρ hM 0
    rwa [csub_lamN hρ, Nat.zero_add] at this
  refine Lambda.reduces_trans (reduces_appList hstart _) ?_
  rw [argsFor_split, appList_append, appList_append]
  refine Lambda.reduces_trans
    (reduces_appList (reduces_appList_csub hg b (tagEnv B K τ) hρ _) _) ?_
  rw [extendEnv_baseTags, csub_appList, csub_var_ge (Nat.zero_le h), Nat.sub_zero]
  exact .refl _

/-- The `r`-th argument of the η-expanded node, as an instantiated term. -/
theorem getD_expArgsT {B K base b e r : ℕ} {as : List Lambda} {τ : ℕ → ℕ}
    (hr : r < as.length + e) :
    ((as.map (csub (tagEnv B K (expEnv base τ b e)) 0)) ++
        argsFor (baseTags B K base) e).getD r (Lambda.var 0)
      = csub (tagEnv B K (argEnvT base τ b e as.length r)) 0 (argTermOf as r) := by
  have hmaplen : (as.map (csub (tagEnv B K (expEnv base τ b e)) 0)).length = as.length := by simp
  by_cases hlt : r < as.length
  · have h1 : r < (as.map (csub (tagEnv B K (expEnv base τ b e)) 0)).length := by
      rw [hmaplen]; exact hlt
    have h2 : r < ((as.map (csub (tagEnv B K (expEnv base τ b e)) 0)) ++
        argsFor (baseTags B K base) e).length := by
      simp only [List.length_append, hmaplen, argsFor_length]
      omega
    rw [← List.getElem_eq_getD (fallback := Lambda.var 0) (h := h2),
      List.getElem_append_left h1, List.getElem_map, argTermOf, dif_pos hlt, argEnvT,
      if_pos hlt]
  · rw [getD_append_right _ _ _ _ (by rw [hmaplen]; omega), hmaplen,
      getD_argsFor _ e (r - as.length) (by omega), argTermOf, dif_neg hlt, argEnvT,
      if_neg hlt, csub_var_ge (Nat.le_refl 0)]
    simp only [tagEnv, baseTags]
    congr 2
    omega

/-! ## The Böhm-out -/

theorem isClosed_lamN_I (n : ℕ) : Lambda.IsClosed (lamN n Lambda.I) :=
  isClosed_of_freeBelow_zero (freeBelow_lamN n
    (freeBelow_mono (Nat.zero_le _) (freeBelow_zero_of_isClosed IsClosed_I)))

theorem hasHnf_I : HasHnf Lambda.I :=
  hasHnf_of_isHnf (IsHnf.lam (IsHnf.neutral (Neutral.var 0)))

/-- Feeding a tagged tuple its `K + 1` arguments, the last of which is a constant function,
produces that constant. -/
theorem reduces_tagTuple_const {B K t : ℕ} (ht : t < B) {A : List Lambda}
    (hcA : ∀ a ∈ A, Lambda.IsClosed a) (hK : A.length ≤ K) :
    Lambda.reduces (appList (appList (tagTuple B K t) A)
        (List.replicate (K - A.length) Lambda.I ++ [lamN (K + 1) Lambda.I])) Lambda.I := by
  set l : List Lambda := A ++ List.replicate (K - A.length) Lambda.I with hl
  have hlcl : ∀ a ∈ l, Lambda.IsClosed a := by
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hcA a ha
    · exact isClosed_mem_replicate_I ha
  have hllen : l.length = K := by simp [hl]; omega
  have hstep := reduces_appList_tagTuple ht l hlcl hllen (isClosed_lamN_I (K + 1))
  have hrw : appList (tagTuple B K t) (l ++ [lamN (K + 1) Lambda.I])
      = appList (appList (tagTuple B K t) A)
        (List.replicate (K - A.length) Lambda.I ++ [lamN (K + 1) Lambda.I]) := by
    rw [hl, List.append_assoc, appList_append]
  rw [hrw] at hstep
  refine Lambda.reduces_trans hstep ?_
  refine reduces_appList_const (X := Lambda.I) IsClosed_I _ ?_
  simp [hllen]

/-- **Böhm out against an arbitrary term.**  A failure witness produces a list of closed
arguments on which the instantiated first term head-converges and the instantiated second term
head-diverges.  The arity bound `a` and the fresh-tag budget `s` are produced bottom-up from the
witness. -/
theorem sepDiv_of_tagFail : ∀ {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {M N : Lambda},
    TagFail base τ₁ M τ₂ N →
    ∃ a s : ℕ, ∀ B K : ℕ, a ≤ K → base + s ≤ B → (∀ j, τ₁ j < B) → (∀ j, τ₂ j < B) →
      SepDiv (csub (tagEnv B K τ₁) 0 M) (csub (tagEnv B K τ₂) 0 N) := by
  intro base τ₁ τ₂ M N hd
  induction hd with
  | @nohnf base τ₁ τ₂ M N b₁ h₁ as₁ hM hN =>
      refine ⟨as₁.length, b₁, ?_⟩
      intro B K hK hbase hτ₁ hτ₂
      have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hτ₁ 0)
      have hcl₁ : ∀ j, Lambda.IsClosed (tagEnv B K τ₁ j) := isClosed_tagEnv_pos hB τ₁
      have hcl₂ : ∀ j, Lambda.IsClosed (tagEnv B K τ₂ j) := isClosed_tagEnv_pos hB τ₂
      set A : List Lambda := as₁.map (csub (tagEnv B K (expEnv base τ₁ b₁ 0)) 0) with hA
      have hAcl : ∀ a ∈ A, Lambda.IsClosed a := fun a ha => isClosed_csub_mem_map hB ha
      have hAlen : A.length = as₁.length := by simp [hA]
      set extra : List Lambda :=
        List.replicate (K - as₁.length) Lambda.I ++ [lamN (K + 1) Lambda.I] with hextra
      refine ⟨argsFor (baseTags B K base) (b₁ + 0) ++ extra, ?_, ?_, ?_⟩
      · intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · exact isClosed_mem_argsFor_baseTags hB ha
        · rw [hextra] at ha
          rcases List.mem_append.1 ha with ha | ha
          · exact isClosed_mem_replicate_I ha
          · rcases List.mem_cons.1 ha with rfl | ha
            · exact isClosed_lamN_I _
            · exact absurd ha List.not_mem_nil
      · rw [appList_append]
        refine HasHnf.of_reduces
          (reduces_appList (reduces_csub_node_eta (e := 0) hB hM) extra) ?_
        have hred : Lambda.reduces
            (appList (appList (tagTuple B K (headTag base τ₁ b₁ h₁ 0))
              (A ++ argsFor (baseTags B K base) 0)) extra) Lambda.I := by
          have h0 : A ++ argsFor (baseTags B K base) 0 = A := by simp [argsFor]
          rw [h0, hextra, ← hAlen]
          exact reduces_tagTuple_const (headTag_lt hτ₁ (by omega)) hAcl (by omega)
        exact HasHnf.of_reduces hred hasHnf_I
      · rw [appList_append, ← appList_append]
        exact not_hasHnf_appList (fun hc => hN (hasHnf_of_hasHnf_csub hcl₂ hc)) _
  | @root base τ₁ τ₂ M N b₁ h₁ e₁ b₂ h₂ e₂ as₁ as₂ hM hN hmin hm hne =>
      refine ⟨max (as₁.length + e₁) (as₂.length + e₂), b₁ + b₂, ?_⟩
      intro B K hK hbase hτ₁ hτ₂
      have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hτ₁ 0)
      have hmle : b₁ + e₁ ≤ b₁ + b₂ := by rcases hmin with rfl | rfl <;> omega
      have hbB : base + (b₁ + e₁) ≤ B := by omega
      have hbB' : base + (b₂ + e₂) ≤ B := by omega
      have ht₁ : headTag base τ₁ b₁ h₁ e₁ < B := headTag_lt hτ₁ hbB
      have ht₂ : headTag base τ₂ b₂ h₂ e₂ < B := headTag_lt hτ₂ hbB'
      have hK₁ : as₁.length + e₁ ≤ K := le_trans (le_max_left _ _) hK
      have hK₂ : as₂.length + e₂ ≤ K := le_trans (le_max_right _ _) hK
      have hcl₁ := isClosed_expArgs (B := B) (K := K) (base := base) (b := b₁) (e := e₁)
        (σ := τ₁) hB (as := as₁)
      have hcl₂ := isClosed_expArgs (B := B) (K := K) (base := base) (b := b₂) (e := e₂)
        (σ := τ₂) hB (as := as₂)
      have hred₂ : Lambda.reduces
          (appList (csub (tagEnv B K τ₂) 0 N) (argsFor (baseTags B K base) (b₁ + e₁)))
          (appList (tagTuple B K (headTag base τ₂ b₂ h₂ e₂))
            ((as₂.map (csub (tagEnv B K (expEnv base τ₂ b₂ e₂)) 0)) ++
              argsFor (baseTags B K base) e₂)) := by
        rw [hm]; exact reduces_csub_node_eta hB hN
      refine SepDiv.of_reduces (argsFor (baseTags B K base) (b₁ + e₁)) ?_
        (reduces_csub_node_eta hB hM) hred₂ (SepDiv.of_separable ?_)
      · intro a ha; exact isClosed_mem_argsFor_baseTags hB ha
      · rcases Nat.lt_trichotomy (as₁.length + e₁) (as₂.length + e₂) with hlt | heq | hlt
        · exact (separable_tagTuple_of_length_lt ht₁ ht₂ hcl₁ hcl₂
            (by rw [length_expArgs, length_expArgs]; omega)
            (by rw [length_expArgs]; omega)).symm
        · have hh : headTag base τ₁ b₁ h₁ e₁ ≠ headTag base τ₂ b₂ h₂ e₂ :=
            hne.resolve_right (fun hc => hc heq)
          exact separable_tagTuple_of_tag_ne ht₂ ht₁ (Ne.symm hh) hcl₂ hcl₁
            (by rw [length_expArgs, length_expArgs]; omega)
            (by rw [length_expArgs]; omega)
        · exact separable_tagTuple_of_length_lt ht₂ ht₁ hcl₂ hcl₁
            (by rw [length_expArgs, length_expArgs]; omega)
            (by rw [length_expArgs]; omega)
  | @arg base τ₁ τ₂ M N b₁ h₁ e₁ b₂ h₂ e₂ r as₁ as₂ hM hN hmin hm hhead hlen hr hd ih =>
      obtain ⟨a', s', ih⟩ := ih
      refine ⟨max a' (max (as₁.length + e₁) (as₂.length + e₂)), (b₁ + b₂) + s', ?_⟩
      intro B K hK hbase hτ₁ hτ₂
      have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hτ₁ 0)
      have hmle : b₁ + e₁ ≤ b₁ + b₂ := by rcases hmin with rfl | rfl <;> omega
      have hbB : base + (b₁ + e₁) ≤ B := by omega
      have hbB' : base + (b₂ + e₂) ≤ B := by omega
      have hK₁ : as₁.length + e₁ ≤ K :=
        le_trans (le_trans (le_max_left _ _) (le_max_right a' _)) hK
      have hKa : a' ≤ K := le_trans (le_max_left _ _) hK
      set extra : List Lambda :=
        List.replicate (K - (as₁.length + e₁)) Lambda.I ++ [projSel (K + 1) r] with hextra
      have hchain : ∀ (σ : ℕ → ℕ) (b e h : ℕ) (as : List Lambda) (P : Lambda),
          Lambda.reduces P (lamN b (appList (Lambda.var h) as)) → (∀ j, σ j < B) →
          b + e = b₁ + e₁ → as.length + e = as₁.length + e₁ →
          Lambda.reduces (appList (csub (tagEnv B K σ) 0 P)
              (argsFor (baseTags B K base) (b₁ + e₁) ++ extra))
            (csub (tagEnv B K (argEnvT base σ b e as.length r)) 0 (argTermOf as r)) := by
        intro σ b e h as P hP hσ hbe hle
        rw [appList_append, ← hbe]
        refine Lambda.reduces_trans (reduces_appList (reduces_csub_node_eta hB hP) _) ?_
        have hAlen : ((as.map (csub (tagEnv B K (expEnv base σ b e)) 0)) ++
            argsFor (baseTags B K base) e).length = as₁.length + e₁ := by
          rw [length_expArgs]; exact hle
        have hex := reduces_tagTuple_extract (B := B) (K := K)
          (t := headTag base σ b h e) (r := r) (headTag_lt hσ (by omega))
          (isClosed_expArgs hB) (by rw [hAlen]; omega) (by rw [hAlen]; omega)
        rw [hAlen, ← hextra] at hex
        refine Lambda.reduces_trans hex ?_
        rw [getD_expArgsT (by omega)]
        exact .refl _
      refine SepDiv.of_reduces (argsFor (baseTags B K base) (b₁ + e₁) ++ extra) ?_
        (hchain τ₁ b₁ e₁ h₁ as₁ M hM hτ₁ rfl rfl)
        (hchain τ₂ b₂ e₂ h₂ as₂ N hN hτ₂ (by omega) (by omega)) ?_
      · intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · exact isClosed_mem_argsFor_baseTags hB ha
        · rw [hextra] at ha
          rcases List.mem_append.1 ha with ha | ha
          · exact isClosed_mem_replicate_I ha
          · rcases List.mem_cons.1 ha with rfl | ha
            · exact isClosed_projSel_pos (Nat.succ_pos K)
            · exact absurd ha List.not_mem_nil
      · exact ih B K hKa (by omega) (argEnvT_lt hτ₁ hr hbB)
          (argEnvT_lt hτ₂ (by omega) hbB')

end Lambda

end
