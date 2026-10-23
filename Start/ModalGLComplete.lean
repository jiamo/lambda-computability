import Start.ModalGL

/-!
# Big round 2, run 3, item W13: completeness of GL for finite transitive irreflexive frames
(row M24-GL)

* `ModalGL.CanWorld L` — the finite canonical model of a list `L` of formulas: consistent sets of
  formulas inside `L ∪ ¬L` that decide every member of `L`; accessibility `ModalGL.canRel`
  (`ModalGL.CanR`: every `□ψ` of `Γ` and its body `ψ` are in `Δ`, and some `□χ ∈ Δ` is not in
  `Γ`), which is transitive and irreflexive; valuation `ModalGL.canVal`;
* **`ModalGL.truth`** — the truth lemma for subformula-closed `L`; the box case uses the modal
  lemma `ModalGL.Der.loeb_rule` (from Löb's axiom and axiom 4) and Lindenbaum's lemma;
* **`ModalGL.complete`** — a formula forced at every world of every finite, transitive,
  irreflexive Kripke model is a theorem of GL;
* **`ModalGL.provable_iff_valid`** — with `ModalGL.sound`, GL is exactly the logic of finite
  transitive irreflexive frames.
-/

set_option autoImplicit false

namespace ModalGL

/-- Formulas in the closure of `L` (members and negations). -/
def closureF (L : List Fml) : Finset Fml := (L ++ L.map Fml.neg).toFinset

/-- Worlds of the canonical model for `L`: consistent sets inside the closure deciding `L`. -/
def CanWorld (L : List Fml) : Type :=
  {Δ : Finset Fml // Δ ⊆ closureF L ∧ Consistent Δ.toList ∧ ∀ ψ ∈ L, ψ ∈ Δ ∨ ψ.neg ∈ Δ}

instance (L : List Fml) : Finite (CanWorld L) := by
  classical
  refine Finite.of_injective (β := (closureF L).powerset)
    (fun w => ⟨w.1, Finset.mem_powerset.2 w.2.1⟩) ?_
  intro a b h
  apply Subtype.ext
  simpa using h

/-- Accessibility of the canonical model. -/
def canRel (L : List Fml) (w v : CanWorld L) : Prop := CanR w.1 v.1

/-- Valuation of the canonical model. -/
def canVal (L : List Fml) (w : CanWorld L) (n : ℕ) : Prop := Fml.var n ∈ w.1

theorem der_toList {Δ : Finset Fml} {l : List Fml} {p : Fml} (h : Der l p)
    (hsub : ∀ q ∈ l, q ∈ Δ) : Der Δ.toList p :=
  h.mono fun q hq => Finset.mem_toList.2 (hsub q hq)

theorem box_mem_closure {L : List Fml} (hL : ∀ ψ ∈ L, ∀ χ ∈ ψ.sub, χ ∈ L) {χ : Fml}
    (h : χ.box ∈ closureF L) : χ.box ∈ L ∧ χ ∈ L := by
  simp only [closureF, List.mem_toFinset, List.mem_append, List.mem_map] at h
  rcases h with h | ⟨ψ, -, e⟩
  · exact ⟨h, hL _ h χ (by simp [Fml.sub, Fml.mem_sub_self])⟩
  · cases e

/-- **Truth lemma** for formulas of a subformula-closed list. -/
theorem truth {L : List Fml} (hL : ∀ ψ ∈ L, ∀ χ ∈ ψ.sub, χ ∈ L) :
    ∀ (ψ : Fml), ψ ∈ L → ∀ w : CanWorld L, Forces (canRel L) (canVal L) w ψ ↔ ψ ∈ w.1 := by
  intro ψ
  induction ψ with
  | var n => intro _ w; rfl
  | bot =>
    intro _ w
    simp only [Forces, false_iff]
    intro h
    exact w.2.2.1 (.hyp (Finset.mem_toList.2 h))
  | imp a b iha ihb =>
    intro hψ w
    have ha : a ∈ L := hL _ hψ a (by simp [Fml.sub, Fml.mem_sub_self])
    have hb : b ∈ L := hL _ hψ b (by simp [Fml.sub, Fml.mem_sub_self])
    have dec : ∀ χ ∈ L, χ ∈ w.1.toList ∨ χ.neg ∈ w.1.toList := fun χ hχ => by
      simpa only [Finset.mem_toList] using w.2.2.2 χ hχ
    have := imp_mem_iff w.2.2.1 (dec a ha) (dec b hb) (dec _ hψ)
    simp only [Finset.mem_toList] at this
    simp only [Forces, iha ha w, ihb hb w, this]
  | box a iha =>
    intro hψ w
    have ha : a ∈ L := hL _ hψ a (by simp [Fml.sub, Fml.mem_sub_self])
    constructor
    · intro hf
      by_contra hn
      classical
      let B : List Fml := (w.1.toList.filterMap fun χ => match χ with | .box c => some c | _ => none)
      have hB : ∀ c, c ∈ B ↔ c.box ∈ w.1 := by
        intro c
        simp only [B, List.mem_filterMap, Finset.mem_toList]
        constructor
        · rintro ⟨χ, hχ, e⟩
          cases χ <;> simp at e
          subst e; exact hχ
        · intro h; exact ⟨_, h, rfl⟩
      have hcons : Consistent (a.neg :: a.box :: (B ++ B.map Fml.box)) := by
        intro hbot
        have h1 : Der (a.box :: (B ++ B.map Fml.box)) a :=
          .mp (.thm (Provable.dne a)) hbot.deduction
        have h2 := Der.loeb_rule h1
        have h3 : Der w.1.toList a.box := der_toList h2 (by
          intro q hq
          obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hq
          exact (hB c).1 hc)
        have h4 := mem_of_der w.2.2.1 (by simpa only [Finset.mem_toList] using w.2.2.2 _ hψ) h3
        exact hn (Finset.mem_toList.1 h4)
      obtain ⟨Δ, hsub, hcΔ, hdec, hrange⟩ := lindenbaum L hcons
      have hΔC : Δ.toFinset ⊆ closureF L := by
        intro q hq
        rw [List.mem_toFinset] at hq
        simp only [closureF, List.mem_toFinset, List.mem_append, List.mem_map]
        rcases hrange q hq with hq | ⟨χ, hχ, rfl | rfl⟩
        · simp only [List.mem_cons, List.mem_append, List.mem_map] at hq
          rcases hq with rfl | rfl | hq | ⟨c, hc, rfl⟩
          · exact .inr ⟨a, ha, rfl⟩
          · exact .inl hψ
          · exact .inl (box_mem_closure hL (w.2.1 ((hB _).1 hq))).2
          · exact .inl (box_mem_closure hL (w.2.1 ((hB _).1 hc))).1
        · exact .inl hχ
        · exact .inr ⟨χ, hχ, rfl⟩
      let v : CanWorld L := ⟨Δ.toFinset, hΔC,
        fun h => hcΔ (h.mono fun q hq => by simpa using hq),
        fun χ hχ => by simpa only [List.mem_toFinset] using hdec χ hχ⟩
      have hR : canRel L w v := by
        refine ⟨fun c hc => ?_, a, ?_, hn⟩
        · have hcB := (hB c).2 hc
          exact ⟨List.mem_toFinset.2 (hsub _ (by simp [hcB])),
            List.mem_toFinset.2 (hsub _ (by simp [hcB]))⟩
        · exact List.mem_toFinset.2 (hsub _ (by simp))
      have hav : a ∉ v.1 := by
        intro h
        have h1 : a.neg ∈ Δ := hsub _ (by simp)
        exact hcΔ (.mp (.hyp h1) (.hyp (List.mem_toFinset.1 h)))
      exact hav ((iha ha v).1 (hf v hR))
    · intro h v hR
      exact (iha ha v).2 (hR.1 a h).1

/-- **Completeness of GL for finite transitive irreflexive frames.** -/
theorem complete {φ : Fml}
    (h : ∀ (W : Type) [Finite W] (R : W → W → Prop), (∀ a b c, R a b → R b c → R a c) →
      (∀ a, ¬ R a a) → ∀ (V : W → ℕ → Prop) (w : W), Forces R V w φ) : Provable φ := by
  by_contra hn
  let L := φ.sub
  have hL : ∀ ψ ∈ L, ∀ χ ∈ ψ.sub, χ ∈ L := fun ψ hψ χ hχ => Fml.sub_trans hψ hχ
  have hc : Consistent [φ.neg] := consistent_neg_of_not_der (Γ := []) fun hd => hn hd.provable
  obtain ⟨Δ, hsub, hcΔ, hdec, hrange⟩ := lindenbaum L hc
  have hΔC : Δ.toFinset ⊆ closureF L := by
    intro q hq
    rw [List.mem_toFinset] at hq
    simp only [closureF, List.mem_toFinset, List.mem_append, List.mem_map]
    rcases hrange q hq with hq | ⟨χ, hχ, rfl | rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      subst hq; exact .inr ⟨φ, Fml.mem_sub_self φ, rfl⟩
    · exact .inl hχ
    · exact .inr ⟨χ, hχ, rfl⟩
  let w : CanWorld L := ⟨Δ.toFinset, hΔC,
    fun h => hcΔ (h.mono fun q hq => by simpa using hq),
    fun χ hχ => by simpa only [List.mem_toFinset] using hdec χ hχ⟩
  have hf := h (CanWorld L) (canRel L) (fun a b c => CanR.trans) (fun a => CanR.irrefl a.1)
    (canVal L) w
  have hφ := (truth hL φ (Fml.mem_sub_self φ) w).1 hf
  have h1 : φ.neg ∈ Δ := hsub _ (by simp)
  exact hcΔ (.mp (.hyp h1) (.hyp (List.mem_toFinset.1 hφ)))

/-- **GL is sound and complete for finite transitive irreflexive frames.** -/
theorem provable_iff_valid (φ : Fml) :
    Provable φ ↔ ∀ (W : Type) [Finite W] (R : W → W → Prop), (∀ a b c, R a b → R b c → R a c) →
      (∀ a, ¬ R a a) → ∀ (V : W → ℕ → Prop) (w : W), Forces R V w φ :=
  ⟨fun h _ _ R ht hi V w => sound h R ht hi V w, complete⟩

end ModalGL
