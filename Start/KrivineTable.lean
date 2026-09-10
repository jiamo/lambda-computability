/-
**The code table: a lambda term flattened into a list of nodes.**

The Krivine machine of `Start/Krivine.lean` carries pieces of code inside its closures.  An
implementation must not copy them: the classical answer is to flatten the initial term **once**
into a table of nodes and to let every closure hold an *address* in that table.  This module
builds the table, its decoding and the flattening, and is used by `Start/KrivineHeap.lean`, which
adds the heap.

Main definitions:

* `Krivine.Impl.Node`, `Krivine.Impl.Tab`, `Krivine.Impl.TabWF` — the nodes of the flattened
  code, the table, and the well-formedness that makes reading it terminate (a node refers only to
  nodes below it);
* `Krivine.Impl.decTerm` — the code at an address;
* `Krivine.Impl.flatten`, `Krivine.Impl.tabOf`, `Krivine.Impl.rootOf` — the flattening of a term
  into a table, and the table of a term.

Main results:

* `Krivine.Impl.decTermF_prefix` — reading an address depends neither on the fuel, as long as
  there is enough of it, nor on nodes appended afterwards;
* `Krivine.Impl.decTerm_var`, `Krivine.Impl.decTerm_app`, `Krivine.Impl.decTerm_lam` — reading a
  node of each shape;
* `Krivine.Impl.decTerm_flatten`, `Krivine.Impl.decTerm_tabOf` — **the table produced from a term
  decodes back to it**, and `Krivine.Impl.tabOf_length` — it has one node per syntax node.
-/

import Start.Krivine

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Krivine

namespace Impl

/-- An address at which a list holds something is an address of the list. -/
theorem lt_length_of_getElem? {α : Type _} {l : List α} {p : ℕ} {x : α} (h : l[p]? = some x) :
    p < l.length := (List.getElem?_eq_some_iff.1 h).1

/-! ### The code table -/

/-- A node of the flattened code: a de Bruijn index, an application of two nodes, or an
abstraction over a node.  The arguments of `app` and `lam` are addresses in the table. -/
inductive Node where
  /-- A de Bruijn index. -/
  | var (n : ℕ)
  /-- An application of the code at `f` to the code at `a`. -/
  | app (f a : ℕ)
  /-- An abstraction over the code at `b`. -/
  | lam (b : ℕ)
  deriving DecidableEq, Inhabited

/-- The code table: the flattened syntax tree of the term being evaluated. -/
abbrev Tab := List Node

/-- The addresses a node refers to are below `k`. -/
def Node.refsLt : Node → ℕ → Prop
  | Node.var _, _ => True
  | Node.app f a, k => f < k ∧ a < k
  | Node.lam b, k => b < k

/-- A table is **well formed** when every node refers only to nodes below it, so that reading it
terminates. -/
def TabWF (tab : Tab) : Prop := ∀ k, ∀ hk : k < tab.length, (tab[k]'hk).refsLt k

theorem tabWF_nil : TabWF ([] : Tab) := by
  intro k hk
  simp at hk

/-- Appending a node that refers only to what is already there preserves well-formedness. -/
theorem tabWF_append {tab : Tab} (hwf : TabWF tab) {nd : Node} (h : nd.refsLt tab.length) :
    TabWF (tab ++ [nd]) := by
  intro k hk
  rcases lt_or_ge k tab.length with hlt | hge
  · rw [List.getElem_append_left hlt]
    exact hwf k hlt
  · have hklen : k = tab.length := by
      simp only [List.length_append, List.length_cons, List.length_nil] at hk
      omega
    subst hklen
    rw [show (tab ++ [nd])[tab.length]'hk = nd by simp]
    exact h

/-- Decoding a table address, with `fuel` bounding the depth of the term read. -/
def decTermF (tab : Tab) : ℕ → ℕ → Lambda
  | 0, _ => Lambda.var 0
  | fuel + 1, p =>
      match tab[p]? with
      | some (Node.var n) => Lambda.var n
      | some (Node.app f a) => Lambda.app (decTermF tab fuel f) (decTermF tab fuel a)
      | some (Node.lam b) => Lambda.lam (decTermF tab fuel b)
      | none => Lambda.var 0

theorem decTermF_var_eq {tab : Tab} {p n fuel : ℕ} (h : tab[p]? = some (Node.var n)) :
    decTermF tab (fuel + 1) p = Lambda.var n := by
  simp only [decTermF, h]

theorem decTermF_app_eq {tab : Tab} {p f a fuel : ℕ} (h : tab[p]? = some (Node.app f a)) :
    decTermF tab (fuel + 1) p = Lambda.app (decTermF tab fuel f) (decTermF tab fuel a) := by
  simp only [decTermF, h]

theorem decTermF_lam_eq {tab : Tab} {p b fuel : ℕ} (h : tab[p]? = some (Node.lam b)) :
    decTermF tab (fuel + 1) p = Lambda.lam (decTermF tab fuel b) := by
  simp only [decTermF, h]

/-- **The code at an address of the table.** -/
def decTerm (tab : Tab) (p : ℕ) : Lambda := decTermF tab (p + 1) p

/-- **Reading a table address is stable**: it does not depend on the fuel, as long as there is
enough of it, nor on nodes appended to the table afterwards. -/
theorem decTermF_prefix {tab tab' : Tab} (hwf : TabWF tab) (hpre : tab <+: tab')
    {p : ℕ} (hp : p < tab.length) {f₁ f₂ : ℕ} (h₁ : p < f₁) (h₂ : p < f₂) :
    decTermF tab f₁ p = decTermF tab' f₂ p := by
  obtain ⟨r, rfl⟩ := hpre
  induction p using Nat.strong_induction_on generalizing f₁ f₂ with
  | _ p ih =>
    obtain ⟨k₁, rfl⟩ : ∃ k, f₁ = k + 1 := ⟨f₁ - 1, by omega⟩
    obtain ⟨k₂, rfl⟩ : ∃ k, f₂ = k + 1 := ⟨f₂ - 1, by omega⟩
    have hnd : tab[p]? = some (tab[p]'hp) := List.getElem?_eq_getElem hp
    have hnd' : (tab ++ r)[p]? = some (tab[p]'hp) := by
      rw [List.getElem?_append_left hp, hnd]
    have hrefs : (tab[p]'hp).refsLt p := hwf p hp
    cases hcase : tab[p]'hp with
    | var n =>
        rw [hcase] at hnd hnd'
        rw [decTermF_var_eq hnd, decTermF_var_eq hnd']
    | app f a =>
        rw [hcase] at hnd hnd' hrefs
        obtain ⟨hf, ha⟩ := hrefs
        rw [decTermF_app_eq hnd, decTermF_app_eq hnd',
          ih f hf (lt_trans hf hp) (f₁ := k₁) (f₂ := k₂) (by omega) (by omega),
          ih a ha (lt_trans ha hp) (f₁ := k₁) (f₂ := k₂) (by omega) (by omega)]
    | lam b =>
        rw [hcase] at hnd hnd' hrefs
        have hb : b < p := hrefs
        rw [decTermF_lam_eq hnd, decTermF_lam_eq hnd',
          ih b hb (lt_trans hb hp) (f₁ := k₁) (f₂ := k₂) (by omega) (by omega)]

/-- Reading an address does not depend on the fuel, as long as there is enough of it. -/
theorem decTermF_eq_decTerm {tab : Tab} (hwf : TabWF tab) {p : ℕ} (hp : p < tab.length) {f : ℕ}
    (hf : p < f) : decTermF tab f p = decTerm tab p :=
  decTermF_prefix hwf (List.prefix_refl tab) hp hf (Nat.lt_succ_self p)

/-- Reading a variable node. -/
theorem decTerm_var {tab : Tab} {p n : ℕ} (hnd : tab[p]? = some (Node.var n)) :
    decTerm tab p = Lambda.var n := decTermF_var_eq hnd

/-- Reading an application node. -/
theorem decTerm_app {tab : Tab} (hwf : TabWF tab) {p f a : ℕ}
    (hnd : tab[p]? = some (Node.app f a)) :
    decTerm tab p = Lambda.app (decTerm tab f) (decTerm tab a) := by
  have hp : p < tab.length := lt_length_of_getElem? hnd
  have hrefs : (tab[p]'hp).refsLt p := hwf p hp
  have hcase : (tab[p]'hp) = Node.app f a := by
    have := List.getElem?_eq_getElem hp
    rw [this] at hnd
    exact Option.some_inj.1 hnd
  rw [hcase] at hrefs
  obtain ⟨hf, ha⟩ := hrefs
  rw [decTerm, decTermF_app_eq hnd, decTermF_eq_decTerm hwf (lt_trans hf hp) hf,
    decTermF_eq_decTerm hwf (lt_trans ha hp) ha]

/-- Reading an abstraction node. -/
theorem decTerm_lam {tab : Tab} (hwf : TabWF tab) {p b : ℕ} (hnd : tab[p]? = some (Node.lam b)) :
    decTerm tab p = Lambda.lam (decTerm tab b) := by
  have hp : p < tab.length := lt_length_of_getElem? hnd
  have hrefs : (tab[p]'hp).refsLt p := hwf p hp
  have hcase : (tab[p]'hp) = Node.lam b := by
    have := List.getElem?_eq_getElem hp
    rw [this] at hnd
    exact Option.some_inj.1 hnd
  rw [hcase] at hrefs
  have hb : b < p := hrefs
  rw [decTerm, decTermF_lam_eq hnd, decTermF_eq_decTerm hwf (lt_trans hb hp) hb]

/-- Flattening a term into a table: the nodes of `t` are appended to `tab`, and the address of
the term itself is returned. -/
def flatten : Lambda → Tab → Tab × ℕ
  | Lambda.var n, tab => (tab ++ [Node.var n], tab.length)
  | Lambda.app a b, tab =>
      let r₁ := flatten a tab
      let r₂ := flatten b r₁.1
      (r₂.1 ++ [Node.app r₁.2 r₂.2], r₂.1.length)
  | Lambda.lam a, tab =>
      let r₁ := flatten a tab
      (r₁.1 ++ [Node.lam r₁.2], r₁.1.length)

/-- Flattening extends the table. -/
theorem flatten_prefix (t : Lambda) (tab : Tab) : tab <+: (flatten t tab).1 := by
  induction t generalizing tab with
  | var n => exact List.prefix_append tab [Node.var n]
  | app a b iha ihb =>
      refine List.IsPrefix.trans (iha tab) ?_
      refine List.IsPrefix.trans (ihb (flatten a tab).1) ?_
      exact List.prefix_append _ _
  | lam a ih =>
      refine List.IsPrefix.trans (ih tab) ?_
      exact List.prefix_append _ _

/-- Flattening a term adds one node per syntax node. -/
theorem flatten_length (t : Lambda) (tab : Tab) :
    (flatten t tab).1.length = tab.length + t.nodes := by
  induction t generalizing tab with
  | var n => simp [flatten]
  | app a b iha ihb =>
      simp only [flatten, List.length_append, List.length_cons, List.length_nil,
        Lambda.nodes_app]
      rw [ihb (flatten a tab).1, iha tab]
      omega
  | lam a ih =>
      simp only [flatten, List.length_append, List.length_cons, List.length_nil,
        Lambda.nodes_lam]
      rw [ih tab]
      omega

/-- The address returned by flattening is the last one used. -/
theorem flatten_lt (t : Lambda) (tab : Tab) : (flatten t tab).2 < (flatten t tab).1.length := by
  cases t <;> simp [flatten]

/-- Flattening preserves well-formedness. -/
theorem flatten_wf {tab : Tab} (hwf : TabWF tab) (t : Lambda) : TabWF (flatten t tab).1 := by
  induction t generalizing tab with
  | var n => exact tabWF_append hwf trivial
  | app a b iha ihb =>
      have h₁ : TabWF (flatten a tab).1 := iha hwf
      have h₂ : TabWF (flatten b (flatten a tab).1).1 := ihb h₁
      refine tabWF_append h₂ ⟨?_, flatten_lt b (flatten a tab).1⟩
      have hle : (flatten a tab).1.length ≤ (flatten b (flatten a tab).1).1.length :=
        (flatten_prefix b (flatten a tab).1).length_le
      exact lt_of_lt_of_le (flatten_lt a tab) hle
  | lam a ih => exact tabWF_append (ih hwf) (flatten_lt a tab)

/-- **The table produced by flattening decodes back to the term.** -/
theorem decTerm_flatten {tab : Tab} (hwf : TabWF tab) (t : Lambda) :
    decTerm (flatten t tab).1 (flatten t tab).2 = t := by
  induction t generalizing tab with
  | var n =>
      refine decTerm_var ?_
      simp [flatten]
  | app a b iha ihb =>
      have h₁ : TabWF (flatten a tab).1 := flatten_wf hwf a
      have h₂ : TabWF (flatten b (flatten a tab).1).1 := flatten_wf h₁ b
      have hwfT : TabWF (flatten (Lambda.app a b) tab).1 := flatten_wf hwf (Lambda.app a b)
      have hnd : (flatten (Lambda.app a b) tab).1[(flatten (Lambda.app a b) tab).2]? =
          some (Node.app (flatten a tab).2 (flatten b (flatten a tab).1).2) := by
        simp [flatten]
      rw [decTerm_app hwfT hnd]
      have hpre₁ : (flatten a tab).1 <+: (flatten (Lambda.app a b) tab).1 := by
        refine List.IsPrefix.trans (flatten_prefix b (flatten a tab).1) ?_
        simp only [flatten]
        exact List.prefix_append _ _
      have hpre₂ : (flatten b (flatten a tab).1).1 <+: (flatten (Lambda.app a b) tab).1 := by
        simp only [flatten]
        exact List.prefix_append _ _
      have e₁ : decTerm (flatten (Lambda.app a b) tab).1 (flatten a tab).2 =
          decTerm (flatten a tab).1 (flatten a tab).2 :=
        (decTermF_prefix h₁ hpre₁ (flatten_lt a tab) (Nat.lt_succ_self _)
          (Nat.lt_succ_self _)).symm
      have e₂ : decTerm (flatten (Lambda.app a b) tab).1 (flatten b (flatten a tab).1).2 =
          decTerm (flatten b (flatten a tab).1).1 (flatten b (flatten a tab).1).2 :=
        (decTermF_prefix h₂ hpre₂ (flatten_lt b (flatten a tab).1) (Nat.lt_succ_self _)
          (Nat.lt_succ_self _)).symm
      rw [e₁, e₂, iha hwf, ihb h₁]
  | lam a ih =>
      have h₁ : TabWF (flatten a tab).1 := flatten_wf hwf a
      have hwfT : TabWF (flatten (Lambda.lam a) tab).1 := flatten_wf hwf (Lambda.lam a)
      have hnd : (flatten (Lambda.lam a) tab).1[(flatten (Lambda.lam a) tab).2]? =
          some (Node.lam (flatten a tab).2) := by
        simp [flatten]
      rw [decTerm_lam hwfT hnd]
      have hpre₁ : (flatten a tab).1 <+: (flatten (Lambda.lam a) tab).1 := by
        simp only [flatten]
        exact List.prefix_append _ _
      have e₁ : decTerm (flatten (Lambda.lam a) tab).1 (flatten a tab).2 =
          decTerm (flatten a tab).1 (flatten a tab).2 :=
        (decTermF_prefix h₁ hpre₁ (flatten_lt a tab) (Nat.lt_succ_self _)
          (Nat.lt_succ_self _)).symm
      rw [e₁, ih hwf]

/-- The table of a term: its own flattening, from the empty table. -/
def tabOf (t : Lambda) : Tab := (flatten t []).1

/-- The address of a term in its own table. -/
def rootOf (t : Lambda) : ℕ := (flatten t []).2

theorem tabWF_tabOf (t : Lambda) : TabWF (tabOf t) := flatten_wf tabWF_nil t

theorem rootOf_lt (t : Lambda) : rootOf t < (tabOf t).length := flatten_lt t []

theorem tabOf_length (t : Lambda) : (tabOf t).length = t.nodes := by
  rw [tabOf, flatten_length]
  simp

theorem decTerm_tabOf (t : Lambda) : decTerm (tabOf t) (rootOf t) = t :=
  decTerm_flatten tabWF_nil t

end Impl

end Krivine
