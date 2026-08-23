/-
# Böhm's separation theorem, η-general form

`Start/BohmOut.lean` separates two Böhm trees that differ along a path on which the two trees
carry the *same* number of binders at every node.  This module removes that restriction: two
Böhm trees are separable as soon as they are not η-equal.

The device is to compare the two trees *after η-expanding each node to the common arity*
`m = max b₁ b₂`, and to name the variables by tags rather than by de Bruijn indices: a tag
function `τ : ℕ → ℕ` records, for each free variable of a tree, the name of the variable it
stands for.  Two trees compared with tag functions `τ₁`, `τ₂` then live in a common name space,
which is what makes the comparison of subtrees across an η-expansion meaningful.

* `Lambda.TagEq` is η-equality of two tagged trees, and `Lambda.TagDiffer` its negation, phrased
  positively as "somewhere along a common path the η-expanded nodes have different heads or
  different numbers of arguments".
* `Lambda.separable_of_tagDiffer` is the Böhm-out induction in this setting, and
  `Lambda.separable_toTerm_of_not_tagEq` the resulting separation theorem for closed normal
  forms.
-/

import Start.BohmOut

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-! ## Tag environments for η-expanded nodes -/

/-- The tags of the arguments used to descend through a node with `m` binders: the binder at
η-expanded level `k` receives the tag `base + k`. -/
def baseTags (B K base : ℕ) : ℕ → Lambda := fun k => tagTuple B K (base + k)

/-- The tag function inside a node with `b` binders which has been η-expanded by `e` further
binders: the binder `j < b` sits at η-expanded level `e + j`, and the variables above the node
keep the tags they had. -/
def expEnv (base : ℕ) (τ : ℕ → ℕ) (b e : ℕ) : ℕ → ℕ :=
  fun j => if j < b then base + e + j else τ (j - b)

/-- The tag of the head variable of a node with `b` binders, η-expanded by `e`. -/
def headTag (base : ℕ) (τ : ℕ → ℕ) (b h e : ℕ) : ℕ := expEnv base τ b e h

/-- The `r`-th argument of a node η-expanded by `e`: one of the arguments actually present, or
else one of the `e` variables bound by the η-expansion, which is the tree `node 0 0 []`. -/
def argTreeOf (as : List BohmNF) (r : ℕ) : BohmNF :=
  if h : r < as.length then as[r] else .node 0 0 []

/-- The tag function to be used with `argTreeOf`. -/
def argEnvOf (base : ℕ) (τ : ℕ → ℕ) (b e : ℕ) (as : List BohmNF) (r : ℕ) : ℕ → ℕ :=
  if r < as.length then expEnv base τ b e else fun _ => base + (as.length + e - 1 - r)

/-! ## η-equality and η-difference of tagged trees -/

/-- `TagEq base τ₁ x τ₂ y`: the trees `x` and `y`, whose free variables are named by `τ₁` and
`τ₂`, are η-equal.  At each node both sides are η-expanded to the common number of binders
`max b₁ b₂` (`e₁ = 0 ∨ e₂ = 0` picks that minimal expansion), the heads must receive the same
tag, the η-expanded argument lists must have the same length, and corresponding arguments must
again be η-equal.  The binders of the node get the fresh tags `base, …, base + m - 1`. -/
inductive TagEq : ℕ → (ℕ → ℕ) → BohmNF → (ℕ → ℕ) → BohmNF → Prop
  | node {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {b₁ h₁ e₁ b₂ h₂ e₂ : ℕ} {as₁ as₂ : List BohmNF}
      (hmin : e₁ = 0 ∨ e₂ = 0) (hm : b₁ + e₁ = b₂ + e₂)
      (hhead : headTag base τ₁ b₁ h₁ e₁ = headTag base τ₂ b₂ h₂ e₂)
      (hlen : as₁.length + e₁ = as₂.length + e₂)
      (hargs : ∀ r, r < as₁.length + e₁ →
        TagEq (base + (b₁ + e₁)) (argEnvOf base τ₁ b₁ e₁ as₁ r) (argTreeOf as₁ r)
          (argEnvOf base τ₂ b₂ e₂ as₂ r) (argTreeOf as₂ r)) :
      TagEq base τ₁ (.node b₁ h₁ as₁) τ₂ (.node b₂ h₂ as₂)

/-- `TagDiffer base τ₁ x τ₂ y`: somewhere along a path on which the η-expanded nodes agree, the
two trees have different head tags or different η-expanded arities.  This is the positive form
of "not η-equal". -/
inductive TagDiffer : ℕ → (ℕ → ℕ) → BohmNF → (ℕ → ℕ) → BohmNF → Prop
  | root {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {b₁ h₁ e₁ b₂ h₂ e₂ : ℕ} {as₁ as₂ : List BohmNF}
      (hmin : e₁ = 0 ∨ e₂ = 0) (hm : b₁ + e₁ = b₂ + e₂)
      (hne : headTag base τ₁ b₁ h₁ e₁ ≠ headTag base τ₂ b₂ h₂ e₂ ∨
        as₁.length + e₁ ≠ as₂.length + e₂) :
      TagDiffer base τ₁ (.node b₁ h₁ as₁) τ₂ (.node b₂ h₂ as₂)
  | arg {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {b₁ h₁ e₁ b₂ h₂ e₂ r : ℕ} {as₁ as₂ : List BohmNF}
      (hmin : e₁ = 0 ∨ e₂ = 0) (hm : b₁ + e₁ = b₂ + e₂)
      (hhead : headTag base τ₁ b₁ h₁ e₁ = headTag base τ₂ b₂ h₂ e₂)
      (hlen : as₁.length + e₁ = as₂.length + e₂) (hr : r < as₁.length + e₁)
      (hd : TagDiffer (base + (b₁ + e₁)) (argEnvOf base τ₁ b₁ e₁ as₁ r) (argTreeOf as₁ r)
        (argEnvOf base τ₂ b₂ e₂ as₂ r) (argTreeOf as₂ r)) :
      TagDiffer base τ₁ (.node b₁ h₁ as₁) τ₂ (.node b₂ h₂ as₂)

/-! ## Descending through an η-expanded node -/

theorem argsFor_split (f : ℕ → Lambda) (b e : ℕ) :
    argsFor f (b + e) = argsFor (fun k => f (k + e)) b ++ argsFor f e := by
  rw [show b + e = e + b from by omega, ← argsFor_take f e b, ← argsFor_drop f e b,
    List.take_append_drop]

theorem instTree_leaf (ρ : ℕ → Lambda) : instTree ρ (.node 0 0 []) = ρ 0 := by
  rw [instTree, BohmNF.toTerm_node, List.map_nil,
    show lamN 0 (appList (Lambda.var 0) ([] : List Lambda)) = Lambda.var 0 from rfl,
    csub_var_ge (Nat.le_refl 0), Nat.sub_self]

/-- A projection is closed as soon as it has at least one argument to choose from: an
out-of-range index selects the last argument. -/
theorem isClosed_projSel_pos {n i : ℕ} (hn : 0 < n) : Lambda.IsClosed (projSel n i) := by
  refine isClosed_of_freeBelow_zero (freeBelow_lamN n ?_)
  change n - 1 - i < 0 + n
  omega

/-- A tagged tuple is closed whatever its tag, as long as there is at least one tag. -/
theorem isClosed_tagTuple_pos {B K i : ℕ} (hB : 0 < B) : Lambda.IsClosed (tagTuple B K i) := by
  refine isClosed_of_freeBelow_zero (freeBelow_lamN (K + 1) ?_)
  refine freeBelow_appList _ (show 0 < 0 + (K + 1) from by omega) ?_
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨k, hk, rfl⟩ := mem_argsFor ha
    change k + 1 < 0 + (K + 1)
    omega
  · rcases List.mem_cons.1 ha with rfl | ha
    · exact freeBelow_mono (Nat.zero_le _)
        (freeBelow_zero_of_isClosed (isClosed_projSel_pos hB))
    · exact absurd ha List.not_mem_nil

theorem isClosed_tagEnv_pos {B K : ℕ} (hB : 0 < B) (τ : ℕ → ℕ) (j : ℕ) :
    Lambda.IsClosed (tagEnv B K τ j) := isClosed_tagTuple_pos hB

theorem isClosed_baseTags {B K base : ℕ} (hB : 0 < B) (k : ℕ) :
    Lambda.IsClosed (baseTags B K base k) := isClosed_tagTuple_pos hB

theorem extendEnv_baseTags {B K base b e : ℕ} (τ : ℕ → ℕ) :
    extendEnv (fun j => baseTags B K base (j + e)) b (tagEnv B K τ)
      = tagEnv B K (expEnv base τ b e) := by
  funext j
  by_cases hj : j < b
  · simp only [extendEnv, if_pos hj, baseTags, tagEnv, expEnv]
    rw [show base + (j + e) = base + e + j from by omega]
  · simp only [extendEnv, if_neg hj, tagEnv, expEnv]

/-- **One step of the η-general descent.**  Feeding the `b + e` tagged arguments of the node to
the instantiated tree exposes the tag of its head, applied to the instantiated arguments of the
node followed by the `e` tags introduced by the η-expansion. -/
theorem reduces_node_eta {B K base b h e : ℕ} {as : List BohmNF} {τ : ℕ → ℕ} (hB : 0 < B) :
    Lambda.reduces (appList (instTree (tagEnv B K τ) (.node b h as))
        (argsFor (baseTags B K base) (b + e)))
      (appList (tagTuple B K (headTag base τ b h e))
        ((as.map (instTree (tagEnv B K (expEnv base τ b e)))) ++
          argsFor (baseTags B K base) e)) := by
  have hρ : ∀ j, Lambda.IsClosed (tagEnv B K τ j) := isClosed_tagEnv_pos hB τ
  have hg : ∀ j, Lambda.IsClosed (baseTags B K base (j + e)) :=
    fun j => isClosed_baseTags hB _
  rw [argsFor_split, appList_append, appList_append]
  refine Lambda.reduces_trans (reduces_appList (reduces_instTree_node hρ hg b h as) _) ?_
  rw [extendEnv_baseTags]
  exact .refl _

theorem getD_append_right (l₁ l₂ : List Lambda) (d : Lambda) (r : ℕ) (h : l₁.length ≤ r) :
    (l₁ ++ l₂).getD r d = l₂.getD (r - l₁.length) d := by
  rw [List.getD, List.getD, List.getElem?_append_right h]

/-- The `r`-th argument of the η-expanded node, as an instantiated tree. -/
theorem getD_expArgs {B K base b e r : ℕ} {as : List BohmNF} {τ : ℕ → ℕ}
    (hr : r < as.length + e) :
    ((as.map (instTree (tagEnv B K (expEnv base τ b e)))) ++
        argsFor (baseTags B K base) e).getD r (Lambda.var 0)
      = instTree (tagEnv B K (argEnvOf base τ b e as r)) (argTreeOf as r) := by
  by_cases hlt : r < as.length
  · have hmaplen : (as.map (instTree (tagEnv B K (expEnv base τ b e)))).length = as.length := by
      simp
    have h1 : r < (as.map (instTree (tagEnv B K (expEnv base τ b e)))).length := by
      rw [hmaplen]; exact hlt
    have h2 : r < ((as.map (instTree (tagEnv B K (expEnv base τ b e)))) ++
        argsFor (baseTags B K base) e).length := by
      simp only [List.length_append, hmaplen, argsFor_length]
      omega
    rw [← List.getElem_eq_getD (fallback := Lambda.var 0) (h := h2),
      List.getElem_append_left h1, List.getElem_map, argTreeOf, dif_pos hlt, argEnvOf,
      if_pos hlt]
  · have hmaplen : (as.map (instTree (tagEnv B K (expEnv base τ b e)))).length = as.length := by
      simp
    rw [getD_append_right _ _ _ _ (by rw [hmaplen]; omega), hmaplen,
      getD_argsFor _ e (r - as.length) (by omega), argTreeOf, dif_neg hlt, argEnvOf,
      if_neg hlt, instTree_leaf, baseTags, tagEnv]
    congr 2
    omega

/-! ## The η-general Böhm-out induction -/

theorem headTag_lt {B base b h e : ℕ} {τ : ℕ → ℕ} (hτ : ∀ j, τ j < B)
    (hbB : base + (b + e) ≤ B) : headTag base τ b h e < B := by
  rw [headTag, expEnv]
  by_cases hh : h < b
  · rw [if_pos hh]; omega
  · rw [if_neg hh]; exact hτ _

theorem argEnvOf_lt {B base b e r : ℕ} {as : List BohmNF} {τ : ℕ → ℕ} (hτ : ∀ j, τ j < B)
    (hr : r < as.length + e) (hbB : base + (b + e) ≤ B) :
    ∀ j, argEnvOf base τ b e as r j < B := by
  intro j
  rw [argEnvOf]
  by_cases hlt : r < as.length
  · rw [if_pos hlt, expEnv]
    by_cases hj : j < b
    · rw [if_pos hj]; omega
    · rw [if_neg hj]; exact hτ _
  · rw [if_neg hlt]; omega

theorem arityLe_argTreeOf {a b h : ℕ} {as : List BohmNF} (ha : BohmNF.ArityLe a (.node b h as))
    (r : ℕ) : BohmNF.ArityLe a (argTreeOf as r) := by
  rw [argTreeOf]
  split
  · cases ha with | node _ hargs => exact hargs _ (List.getElem_mem _)
  · exact .node (by simp) (by simp)

theorem binderRoom_argTreeOf {s b h : ℕ} {as : List BohmNF}
    (hb : BohmNF.BinderRoom s (.node b h as)) (r : ℕ) :
    BohmNF.BinderRoom (s - b) (argTreeOf as r) := by
  rw [argTreeOf]
  split
  · cases hb with | node _ hargs => exact hargs _ (List.getElem_mem _)
  · exact .node (Nat.zero_le _) (by simp)

/-- **Böhm out, η-general form.**  Two tagged Böhm trees that differ somewhere along a common
path are separable once their variables are replaced by the corresponding tagged tuples. -/
theorem separable_of_tagDiffer {B K : ℕ} :
    ∀ {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {x y : BohmNF}, TagDiffer base τ₁ x τ₂ y →
      ∀ {a₁ a₂ s₁ s₂ : ℕ}, BohmNF.ArityLe a₁ x → BohmNF.ArityLe a₂ y →
        BohmNF.BinderRoom s₁ x → BohmNF.BinderRoom s₂ y →
        a₁ + a₂ + s₁ + s₂ ≤ K → base + s₁ + s₂ ≤ B →
        (∀ j, τ₁ j < B) → (∀ j, τ₂ j < B) →
        Separable (instTree (tagEnv B K τ₁) x) (instTree (tagEnv B K τ₂) y) := by
  intro base τ₁ τ₂ x y hd
  induction hd with
  | @root base τ₁ τ₂ b₁ h₁ e₁ b₂ h₂ e₂ as₁ as₂ hmin hm hne =>
      intro a₁ a₂ s₁ s₂ ha₁ ha₂ hb₁ hb₂ hK hbase hτ₁ hτ₂
      have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hτ₁ 0)
      have hbs₁ : b₁ ≤ s₁ := by cases hb₁ with | node hbb _ => exact hbb
      have hbs₂ : b₂ ≤ s₂ := by cases hb₂ with | node hbb _ => exact hbb
      have hk₁ : as₁.length ≤ a₁ := by cases ha₁ with | node hl _ => exact hl
      have hk₂ : as₂.length ≤ a₂ := by cases ha₂ with | node hl _ => exact hl
      have hmle : b₁ + e₁ ≤ b₁ + b₂ := by rcases hmin with rfl | rfl <;> omega
      have hbB : base + (b₁ + e₁) ≤ B := by omega
      have hbB' : base + (b₂ + e₂) ≤ B := by omega
      have ht₁ : headTag base τ₁ b₁ h₁ e₁ < B := headTag_lt hτ₁ hbB
      have ht₂ : headTag base τ₂ b₂ h₂ e₂ < B := headTag_lt hτ₂ hbB'
      have hred₂ : Lambda.reduces (appList (instTree (tagEnv B K τ₂) (.node b₂ h₂ as₂))
          (argsFor (baseTags B K base) (b₁ + e₁)))
          (appList (tagTuple B K (headTag base τ₂ b₂ h₂ e₂))
            ((as₂.map (instTree (tagEnv B K (expEnv base τ₂ b₂ e₂)))) ++
              argsFor (baseTags B K base) e₂)) := by
        rw [hm]; exact reduces_node_eta hB
      have hcl : ∀ (σ : ℕ → ℕ) (as : List BohmNF) (a : Lambda),
          a ∈ (as.map (instTree (tagEnv B K σ))) ++ argsFor (baseTags B K base) e₁ ∨
            a ∈ (as.map (instTree (tagEnv B K σ))) ++ argsFor (baseTags B K base) e₂ →
            Lambda.IsClosed a := by
        intro σ as a ha
        have : a ∈ (as.map (instTree (tagEnv B K σ))) ∨ (∃ k, a = baseTags B K base k) := by
          rcases ha with ha | ha <;> rcases List.mem_append.1 ha with ha | ha
          · exact Or.inl ha
          · obtain ⟨k, -, rfl⟩ := mem_argsFor ha; exact Or.inr ⟨k, rfl⟩
          · exact Or.inl ha
          · obtain ⟨k, -, rfl⟩ := mem_argsFor ha; exact Or.inr ⟨k, rfl⟩
        rcases this with ha | ⟨k, rfl⟩
        · obtain ⟨z, -, rfl⟩ := List.mem_map.1 ha
          exact isClosed_instTree (isClosed_tagEnv_pos hB σ) z
        · exact isClosed_baseTags hB k
      have hcl₁ : ∀ a ∈ (as₁.map (instTree (tagEnv B K (expEnv base τ₁ b₁ e₁)))) ++
          argsFor (baseTags B K base) e₁, Lambda.IsClosed a :=
        fun a ha => hcl _ as₁ a (Or.inl ha)
      have hcl₂ : ∀ a ∈ (as₂.map (instTree (tagEnv B K (expEnv base τ₂ b₂ e₂)))) ++
          argsFor (baseTags B K base) e₂, Lambda.IsClosed a :=
        fun a ha => hcl _ as₂ a (Or.inr ha)
      have hL₁ : ((as₁.map (instTree (tagEnv B K (expEnv base τ₁ b₁ e₁)))) ++
          argsFor (baseTags B K base) e₁).length = as₁.length + e₁ := by simp
      have hL₂ : ((as₂.map (instTree (tagEnv B K (expEnv base τ₂ b₂ e₂)))) ++
          argsFor (baseTags B K base) e₂).length = as₂.length + e₂ := by simp
      refine Separable.of_reduces (argsFor (baseTags B K base) (b₁ + e₁)) ?_
        (reduces_node_eta hB) hred₂ ?_
      · intro a ha
        obtain ⟨k, -, rfl⟩ := mem_argsFor ha
        exact isClosed_baseTags hB k
      · rcases Nat.lt_trichotomy (as₁.length + e₁) (as₂.length + e₂) with hlt | heq | hlt
        · exact separable_tagTuple_of_length_lt ht₁ ht₂ hcl₁ hcl₂ (by rw [hL₁, hL₂]; exact hlt)
            (by rw [hL₂]; omega)
        · have hh : headTag base τ₁ b₁ h₁ e₁ ≠ headTag base τ₂ b₂ h₂ e₂ :=
            hne.resolve_right (fun hc => hc heq)
          exact separable_tagTuple_of_tag_ne ht₁ ht₂ hh hcl₁ hcl₂ (by rw [hL₁, hL₂]; exact heq)
            (by rw [hL₁]; omega)
        · exact (separable_tagTuple_of_length_lt ht₂ ht₁ hcl₂ hcl₁ (by rw [hL₁, hL₂]; exact hlt)
            (by rw [hL₁]; omega)).symm
  | @arg base τ₁ τ₂ b₁ h₁ e₁ b₂ h₂ e₂ r as₁ as₂ hmin hm hhead hlen hr hd ih =>
      intro a₁ a₂ s₁ s₂ ha₁ ha₂ hb₁ hb₂ hK hbase hτ₁ hτ₂
      have hB : 0 < B := Nat.lt_of_le_of_lt (Nat.zero_le _) (hτ₁ 0)
      have hbs₁ : b₁ ≤ s₁ := by cases hb₁ with | node hbb _ => exact hbb
      have hbs₂ : b₂ ≤ s₂ := by cases hb₂ with | node hbb _ => exact hbb
      have hk₁ : as₁.length ≤ a₁ := by cases ha₁ with | node hl _ => exact hl
      have hk₂ : as₂.length ≤ a₂ := by cases ha₂ with | node hl _ => exact hl
      have hmle : b₁ + e₁ ≤ b₁ + b₂ := by rcases hmin with rfl | rfl <;> omega
      have hbB : base + (b₁ + e₁) ≤ B := by omega
      have hbB' : base + (b₂ + e₂) ≤ B := by omega
      have hLK : as₁.length + e₁ ≤ K := by omega
      set extra : List Lambda :=
        List.replicate (K - (as₁.length + e₁)) Lambda.I ++ [projSel (K + 1) r] with hextra
      have hchain : ∀ (σ : ℕ → ℕ) (b e h : ℕ) (as : List BohmNF), (∀ j, σ j < B) →
          b + e = b₁ + e₁ → as.length + e = as₁.length + e₁ →
          Lambda.reduces (appList (instTree (tagEnv B K σ) (.node b h as))
              (argsFor (baseTags B K base) (b₁ + e₁) ++ extra))
            (instTree (tagEnv B K (argEnvOf base σ b e as r)) (argTreeOf as r)) := by
        intro σ b e h as hσ hbe hle
        rw [appList_append, ← hbe]
        refine Lambda.reduces_trans (reduces_appList (reduces_node_eta hB) _) ?_
        have hAcl : ∀ a ∈ (as.map (instTree (tagEnv B K (expEnv base σ b e)))) ++
            argsFor (baseTags B K base) e, Lambda.IsClosed a := by
          intro a ha
          rcases List.mem_append.1 ha with ha | ha
          · obtain ⟨z, -, rfl⟩ := List.mem_map.1 ha
            exact isClosed_instTree (isClosed_tagEnv_pos hB _) z
          · obtain ⟨k, -, rfl⟩ := mem_argsFor ha
            exact isClosed_baseTags hB k
        have hAlen : ((as.map (instTree (tagEnv B K (expEnv base σ b e)))) ++
            argsFor (baseTags B K base) e).length = as₁.length + e₁ := by simp [hle]
        have hex := reduces_tagTuple_extract (B := B) (K := K)
          (t := headTag base σ b h e) (r := r) (headTag_lt hσ (by omega)) hAcl
          (by rw [hAlen]; omega) (by rw [hAlen]; omega)
        rw [hAlen, ← hextra] at hex
        refine Lambda.reduces_trans hex ?_
        rw [getD_expArgs (by omega)]
        exact .refl _
      refine Separable.of_reduces (argsFor (baseTags B K base) (b₁ + e₁) ++ extra) ?_
        (hchain τ₁ b₁ e₁ h₁ as₁ hτ₁ rfl rfl)
        (hchain τ₂ b₂ e₂ h₂ as₂ hτ₂ (by omega) (by omega)) ?_
      · intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · obtain ⟨k, -, rfl⟩ := mem_argsFor ha
          exact isClosed_baseTags hB k
        · rw [hextra] at ha
          rcases List.mem_append.1 ha with ha | ha
          · exact isClosed_mem_replicate_I ha
          · rcases List.mem_cons.1 ha with rfl | ha
            · exact isClosed_projSel_pos (Nat.succ_pos K)
            · exact absurd ha List.not_mem_nil
      · exact ih (a₁ := a₁) (a₂ := a₂) (s₁ := s₁ - b₁) (s₂ := s₂ - b₂)
          (arityLe_argTreeOf ha₁ r) (arityLe_argTreeOf ha₂ r)
          (binderRoom_argTreeOf hb₁ r) (binderRoom_argTreeOf hb₂ r) (by omega) (by omega)
          (argEnvOf_lt hτ₁ hr hbB) (argEnvOf_lt hτ₂ (by omega) hbB')

/-! ## Trees that are not η-equal differ along a path -/

/-- The number of nodes of a Böhm tree. -/
def BohmNF.size : BohmNF → ℕ
  | .node _ _ args => 1 + (args.map BohmNF.size).foldr (· + ·) 0

theorem BohmNF.size_pos (x : BohmNF) : 0 < x.size := by
  cases x with | node b h args => rw [BohmNF.size]; omega

theorem le_foldr_sum_of_mem : ∀ (l : List BohmNF) (a : BohmNF), a ∈ l →
    a.size ≤ (l.map BohmNF.size).foldr (· + ·) 0 := by
  intro l
  induction l with
  | nil => intro a ha; exact absurd ha List.not_mem_nil
  | cons b l ih =>
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · simp
      · have := ih a ha
        simp only [List.map_cons, List.foldr_cons]
        omega

theorem BohmNF.size_lt_of_mem {b h : ℕ} {args : List BohmNF} {a : BohmNF} (ha : a ∈ args) :
    a.size < (BohmNF.node b h args).size := by
  have := le_foldr_sum_of_mem args a ha
  rw [BohmNF.size]
  omega

theorem BohmNF.size_argTreeOf (as : List BohmNF) (r : ℕ) (b h : ℕ) :
    (argTreeOf as r).size ≤ (BohmNF.node b h as).size := by
  rw [argTreeOf]
  split
  · exact le_of_lt (BohmNF.size_lt_of_mem (List.getElem_mem _))
  · rw [BohmNF.size, BohmNF.size]
    simp

theorem BohmNF.size_argTreeOf_lt {b h : ℕ} {as : List BohmNF} {r : ℕ} (hr : r < as.length) :
    (argTreeOf as r).size < (BohmNF.node b h as).size := by
  rw [argTreeOf, dif_pos hr]
  exact BohmNF.size_lt_of_mem (List.getElem_mem _)

/-- Two η-variables carrying the same tag are η-equal. -/
theorem tagEq_leaf {base : ℕ} {σ σ' : ℕ → ℕ} (h : σ 0 = σ' 0) :
    TagEq base σ (.node 0 0 []) σ' (.node 0 0 []) := by
  refine TagEq.node (e₁ := 0) (e₂ := 0) (Or.inl rfl) rfl ?_ rfl (by intro r hr; simp at hr)
  simpa [headTag, expEnv] using h

theorem tagDiffer_of_not_tagEq_aux : ∀ (n : ℕ) {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {x y : BohmNF},
    x.size + y.size ≤ n → ¬ TagEq base τ₁ x τ₂ y → TagDiffer base τ₁ x τ₂ y := by
  intro n
  induction n with
  | zero =>
      intro base τ₁ τ₂ x y hn _
      have := x.size_pos
      have := y.size_pos
      omega
  | succ n ih =>
      intro base τ₁ τ₂ x y hn hne
      cases x with
      | node b₁ h₁ as₁ =>
      cases y with
      | node b₂ h₂ as₂ =>
      set e₁ := max b₁ b₂ - b₁ with he₁
      set e₂ := max b₁ b₂ - b₂ with he₂
      have hmin : e₁ = 0 ∨ e₂ = 0 := by
        rcases Nat.le_total b₁ b₂ with h | h
        · right; omega
        · left; omega
      have hm : b₁ + e₁ = b₂ + e₂ := by omega
      by_cases hhead : headTag base τ₁ b₁ h₁ e₁ = headTag base τ₂ b₂ h₂ e₂
      · by_cases hlen : as₁.length + e₁ = as₂.length + e₂
        · have hex : ∃ r, r < as₁.length + e₁ ∧
              ¬ TagEq (base + (b₁ + e₁)) (argEnvOf base τ₁ b₁ e₁ as₁ r) (argTreeOf as₁ r)
                (argEnvOf base τ₂ b₂ e₂ as₂ r) (argTreeOf as₂ r) := by
            by_contra hc
            push_neg at hc
            exact hne (TagEq.node hmin hm hhead hlen (fun r hr => hc r hr))
          obtain ⟨r, hr, hrne⟩ := hex
          have hone : r < as₁.length ∨ r < as₂.length := by
            by_contra hc
            push_neg at hc
            refine hrne ?_
            have h1 : argTreeOf as₁ r = .node 0 0 [] := by rw [argTreeOf, dif_neg (by omega)]
            have h2 : argTreeOf as₂ r = .node 0 0 [] := by rw [argTreeOf, dif_neg (by omega)]
            rw [h1, h2]
            refine tagEq_leaf ?_
            rw [argEnvOf, if_neg (by omega), argEnvOf, if_neg (by omega)]
            omega
          refine TagDiffer.arg hmin hm hhead hlen hr (ih ?_ hrne)
          have hs₁ : (argTreeOf as₁ r).size ≤ (BohmNF.node b₁ h₁ as₁).size :=
            BohmNF.size_argTreeOf _ _ _ _
          have hs₂ : (argTreeOf as₂ r).size ≤ (BohmNF.node b₂ h₂ as₂).size :=
            BohmNF.size_argTreeOf _ _ _ _
          rcases hone with h | h
          · have := BohmNF.size_argTreeOf_lt (b := b₁) (h := h₁) h
            omega
          · have := BohmNF.size_argTreeOf_lt (b := b₂) (h := h₂) h
            omega
        · exact TagDiffer.root hmin hm (Or.inr hlen)
      · exact TagDiffer.root hmin hm (Or.inl hhead)

/-- Two tagged trees which are not η-equal differ along a path. -/
theorem tagDiffer_of_not_tagEq {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {x y : BohmNF}
    (h : ¬ TagEq base τ₁ x τ₂ y) : TagDiffer base τ₁ x τ₂ y :=
  tagDiffer_of_not_tagEq_aux (x.size + y.size) (le_refl _) h

/-- η-equal trees do not differ along a path: the two relations are exclusive. -/
theorem not_tagDiffer_of_tagEq : ∀ {base : ℕ} {τ₁ τ₂ : ℕ → ℕ} {x y : BohmNF},
    TagDiffer base τ₁ x τ₂ y → TagEq base τ₁ x τ₂ y → False := by
  intro base τ₁ τ₂ x y hd
  induction hd with
  | @root base τ₁ τ₂ b₁ h₁ e₁ b₂ h₂ e₂ as₁ as₂ hmin hm hne =>
      intro h
      cases h with
      | @node _ _ _ _ _ e₁' _ _ e₂' _ _ hmin' hm' hhead' hlen' _ =>
          have hee : e₁ = e₁' ∧ e₂ = e₂' := by
            rcases hmin with h1 | h1 <;> rcases hmin' with h2 | h2 <;> omega
          obtain ⟨rfl, rfl⟩ := hee
          rcases hne with hne | hne
          · exact hne hhead'
          · exact hne hlen'
  | @arg base τ₁ τ₂ b₁ h₁ e₁ b₂ h₂ e₂ r as₁ as₂ hmin hm hhead hlen hr _ ih =>
      intro h
      cases h with
      | @node _ _ _ _ _ e₁' _ _ e₂' _ _ hmin' hm' _ _ hargs' =>
          have hee : e₁ = e₁' ∧ e₂ = e₂' := by
            rcases hmin with h1 | h1 <;> rcases hmin' with h2 | h2 <;> omega
          obtain ⟨rfl, rfl⟩ := hee
          exact ih (hargs' r hr)

/-! ## Böhm's separation theorem -/

/-- **Böhm's theorem.**  Two closed normal forms whose Böhm trees are not η-equal are separable:
a single list of closed arguments sends the first to `true` and the second to `false`. -/
theorem separable_toTerm_of_not_tagEq {x y : BohmNF} (hx : BohmNF.FreeVarsBelow 0 x)
    (hy : BohmNF.FreeVarsBelow 0 y)
    (hne : ¬ TagEq 0 (fun _ => 0) x (fun _ => 0) y) :
    Separable x.toTerm y.toTerm := by
  have h := separable_of_tagDiffer (B := x.binderDepth + y.binderDepth + 1)
    (K := x.maxArity + y.maxArity + x.binderDepth + y.binderDepth)
    (tagDiffer_of_not_tagEq hne) (a₁ := x.maxArity) (a₂ := y.maxArity)
    (s₁ := x.binderDepth) (s₂ := y.binderDepth) x.arityLe_maxArity y.arityLe_maxArity
    x.binderRoom_binderDepth y.binderRoom_binderDepth (le_refl _) (by omega)
    (fun _ => by omega) (fun _ => by omega)
  rwa [instTree_of_closed hx, instTree_of_closed hy] at h

theorem tagEq_refl_aux : ∀ (n : ℕ) {base : ℕ} {τ : ℕ → ℕ} {x : BohmNF}, x.size ≤ n →
    TagEq base τ x τ x := by
  intro n
  induction n with
  | zero =>
      intro base τ x hn
      have := x.size_pos
      omega
  | succ n ih =>
      intro base τ x hn
      cases x with
      | node b h as =>
          refine TagEq.node (e₁ := 0) (e₂ := 0) (Or.inl rfl) rfl rfl rfl ?_
          intro r hr
          have hr' : r < as.length := by omega
          exact ih (by have := BohmNF.size_argTreeOf_lt (b := b) (h := h) hr'; omega)

/-- η-equality is reflexive: a tree is never claimed to differ from itself. -/
theorem tagEq_refl {base : ℕ} {τ : ℕ → ℕ} (x : BohmNF) : TagEq base τ x τ x :=
  tagEq_refl_aux x.size (le_refl _)

/-! ## Two examples

The first shows that the η-difference is genuinely taken into account: the trees of `λz. z` and
of `λz w. z w` are η-equal, hence not claimed to be separable.  The second is a separation which
the earlier, binder-matching form of the theorem does not give, since the two trees carry
different numbers of binders at the root. -/

/-- The Böhm trees of `λz. z` and `λz w. z w` are η-equal. -/
example : TagEq 0 (fun _ => 0) (.node 1 0 []) (fun _ => 0) (.node 2 1 [.node 0 0 []]) := by
  refine TagEq.node (e₁ := 1) (e₂ := 0) (Or.inr rfl) rfl rfl rfl ?_
  intro r hr
  have hr0 : r = 0 := by simpa using hr
  subst hr0
  exact tagEq_leaf rfl

/-- `λz. z` and `λz w. z` are separable, although their trees have different numbers of
binders at the root. -/
theorem separable_I_K :
    Separable (BohmNF.node 1 0 []).toTerm (BohmNF.node 2 1 []).toTerm := by
  refine separable_toTerm_of_not_tagEq (.node (by omega) (by simp)) (.node (by omega) (by simp))
    ?_
  intro h
  cases h with
  | @node _ _ _ _ _ e₁ _ _ e₂ _ _ hmin hm _ hlen _ =>
      rcases hmin with h1 | h1 <;> simp only [List.length_nil] at hlen <;> omega

end Lambda

end
