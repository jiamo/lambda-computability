import Mathlib

/-!
# Big round 2, run 2, item W13: the provability logic GL and its Kripke soundness
(row M24-GL)

* `ModalGL.Fml` — modal formulas (variables, `⊥`, `→`, `□`); `ModalGL.Fml.neg`;
* `ModalGL.Provable` — GL as a Hilbert system: three axiom schemes of classical propositional logic,
  the distribution axiom `K`, Löb's axiom `□(□p → p) → □p`, modus ponens and necessitation;
* `ModalGL.Forces R V w φ` — Kripke semantics;
* **`ModalGL.sound`** — every theorem of GL holds at every world of every finite, transitive,
  irreflexive Kripke model; the Löb axiom is the only scheme that needs the frame conditions
  (`ModalGL.loeb_valid`, through converse well-foundedness of a finite strict order); more
  generally `ModalGL.sound_of_wf` for transitive frames with a well-founded converse relation.

* `ModalGL.loeb_frame_iff` — frame correspondence for Löb's axiom;
* tools for the completeness half: the deduction theorem (`ModalGL.Der.deduction`), axiom 4
  (`ModalGL.Provable.four`), the modal lemma (`ModalGL.Der.loeb_rule`), Lindenbaum's lemma in a
  finite list (`ModalGL.lindenbaum`) and the subformula closure (`ModalGL.Fml.sub`).

Completeness for finite transitive irreflexive frames is the remaining half (see the row).
-/

set_option autoImplicit false

namespace ModalGL

/-- Modal formulas. -/
inductive Fml where
  | var : ℕ → Fml
  | bot : Fml
  | imp : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq

/-- Negation `¬φ := φ → ⊥`. -/
def Fml.neg (φ : Fml) : Fml := .imp φ .bot

/-- **The Hilbert system GL.** -/
inductive Provable : Fml → Prop where
  | ax1 (p q : Fml) : Provable (.imp p (.imp q p))
  | ax2 (p q r : Fml) : Provable (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r)))
  | ax3 (p q : Fml) : Provable (.imp (.imp p.neg q.neg) (.imp q p))
  | axK (p q : Fml) : Provable (.imp (.box (.imp p q)) (.imp (.box p) (.box q)))
  | axLoeb (p : Fml) : Provable (.imp (.box (.imp (.box p) p)) (.box p))
  | mp {p q : Fml} : Provable (.imp p q) → Provable p → Provable q
  | nec {p : Fml} : Provable p → Provable (.box p)

/-- **Kripke semantics**: forcing at a world of a model with accessibility `R` and valuation `V`. -/
def Forces {W : Type} (R : W → W → Prop) (V : W → ℕ → Prop) : W → Fml → Prop
  | w, .var n => V w n
  | _, .bot => False
  | w, .imp p q => Forces R V w p → Forces R V w q
  | w, .box p => ∀ v, R w v → Forces R V v p

/-- **Löb's axiom holds in every transitive model whose converse relation is well-founded.** -/
theorem loeb_valid_of_wf {W : Type} (R : W → W → Prop) (htrans : ∀ a b c, R a b → R b c → R a c)
    (wf : WellFounded fun a b => R b a) (V : W → ℕ → Prop) (w : W) (p : Fml) :
    Forces R V w (.imp (.box (.imp (.box p) p)) (.box p)) := by
  intro hw
  by_contra hne
  simp only [Forces, not_forall] at hne
  obtain ⟨v₀, hv₀, hp₀⟩ := hne
  obtain ⟨v, ⟨hv, hpv⟩, hmin⟩ :=
    wf.has_min {u | R w u ∧ ¬ Forces R V u p} ⟨v₀, hv₀, hp₀⟩
  apply hpv
  apply hw v hv
  intro u hu
  by_contra hpu
  exact hmin u ⟨htrans w v u hv hu, hpu⟩ hu

/-- The converse of a transitive irreflexive relation on a finite type is well-founded. -/
theorem wf_of_finite {W : Type} [Finite W] (R : W → W → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hirr : ∀ a, ¬ R a a) :
    WellFounded fun a b => R b a := by
  let S : W → W → Prop := fun a b => R b a
  have : IsTrans W S := ⟨fun a b c hab hbc => htrans c b a hbc hab⟩
  have : Std.Irrefl S := ⟨fun a => hirr a⟩
  exact Finite.wellFounded_of_trans_of_irrefl S

/-- **Löb's axiom holds in every finite transitive irreflexive model.** -/
theorem loeb_valid {W : Type} [Finite W] (R : W → W → Prop) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hirr : ∀ a, ¬ R a a) (V : W → ℕ → Prop) (w : W) (p : Fml) :
    Forces R V w (.imp (.box (.imp (.box p) p)) (.box p)) :=
  loeb_valid_of_wf R htrans (wf_of_finite R htrans hirr) V w p

/-- **Frame correspondence for Löb's axiom**: on a Kripke frame, Löb's axiom (for one variable)
holds under every valuation iff the accessibility relation is transitive and its converse is
well-founded. -/
theorem loeb_frame_iff {W : Type} (R : W → W → Prop) :
    (∀ (V : W → ℕ → Prop) (w : W), Forces R V w (.imp (.box (.imp (.box (.var 0)) (.var 0)))
      (.box (.var 0)))) ↔
    ((∀ a b c, R a b → R b c → R a c) ∧ WellFounded fun a b => R b a) := by
  classical
  constructor
  · intro hL
    refine ⟨fun w u v hwu huv => ?_, ?_⟩
    · by_contra hwv
      have := hL (fun x _ => x ≠ u ∧ x ≠ v) w ?_ u hwu
      · exact this.1 rfl
      · intro x hwx hbox
        refine ⟨fun hxu => ?_, fun hxv => hwv (hxv ▸ hwx)⟩
        subst hxu
        exact (hbox v huv).2 rfl
    · rw [WellFounded.wellFounded_iff_has_min]
      intro X ⟨w₀, hw₀⟩
      by_contra hno
      push Not at hno
      obtain ⟨y, hy, hwy⟩ := hno w₀ hw₀
      have := hL (fun x _ => x ∉ X) w₀ ?_ y hwy
      · exact this hy
      · intro x _ hbox hx
        obtain ⟨z, hz, hxz⟩ := hno x hx
        exact hbox z hxz hz
  · rintro ⟨htrans, wf⟩ V w
    exact loeb_valid_of_wf R htrans wf V w _

/-- **Kripke soundness of GL** for transitive frames with a well-founded converse relation. -/
theorem sound_of_wf {φ : Fml} (h : Provable φ) {W : Type} (R : W → W → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c) (wf : WellFounded fun a b => R b a)
    (V : W → ℕ → Prop) : ∀ w, Forces R V w φ := by
  induction h with
  | ax1 p q => intro w hp _; exact hp
  | ax2 p q r => intro w hpqr hpq hp; exact hpqr hp (hpq hp)
  | ax3 p q =>
    intro w hnn hq
    by_contra hp
    exact hnn hp hq
  | axK p q => intro w hpq hp v hv; exact hpq v hv (hp v hv)
  | axLoeb p => exact fun w => loeb_valid_of_wf R htrans wf V w p
  | mp _ _ ih1 ih2 => exact fun w => ih1 w (ih2 w)
  | nec _ ih => exact fun w v _ => ih v

/-- **Kripke soundness of GL** for finite, transitive, irreflexive frames. -/
theorem sound {φ : Fml} (h : Provable φ) {W : Type} [Finite W] (R : W → W → Prop)
    (htrans : ∀ a b c, R a b → R b c → R a c) (hirr : ∀ a, ¬ R a a) (V : W → ℕ → Prop) :
    ∀ w, Forces R V w φ :=
  sound_of_wf h R htrans (wf_of_finite R htrans hirr) V

/-- GL does not prove `⊥` (the one-world model). -/
theorem consistent : ¬ Provable .bot := fun h =>
  sound h (W := Unit) (fun _ _ => False) (fun _ _ _ h _ => h) (fun _ h => h) (fun _ _ => True) ()

/-- GL does not prove the reflection scheme `□⊥ → ⊥` (it would contradict Löb's theorem). -/
theorem not_provable_reflection : ¬ Provable (.imp (.box .bot) .bot) := fun h =>
  sound h (W := Unit) (fun _ _ => False) (fun _ _ _ h _ => h) (fun _ h => h) (fun _ _ => True) ()
    (fun _ h => h)

/-! ### Derivations from hypotheses and the deduction theorem

The first tools for the completeness half: derivations from a list of hypotheses (necessitation
only on theorems), `ModalGL.Provable.imp_self`, `ModalGL.Der.deduction`, `ModalGL.Provable.box_mono`. -/

/-- `⊢ p → p`. -/
theorem Provable.imp_self (p : Fml) : Provable (.imp p p) :=
  .mp (.mp (.ax2 p (.imp p p) p) (.ax1 p (.imp p p))) (.ax1 p p)

/-- Derivations from hypotheses `Γ`: theorems of GL, members of `Γ`, and modus ponens. -/
inductive Der (Γ : List Fml) : Fml → Prop where
  | thm {p : Fml} : Provable p → Der Γ p
  | hyp {p : Fml} : p ∈ Γ → Der Γ p
  | mp {p q : Fml} : Der Γ (.imp p q) → Der Γ p → Der Γ q

/-- **The deduction theorem.** -/
theorem Der.deduction {Γ : List Fml} {p q : Fml} (h : Der (p :: Γ) q) : Der Γ (.imp p q) := by
  induction h with
  | thm hq => exact .mp (.thm (.ax1 _ _)) (.thm hq)
  | hyp hq =>
    rcases List.mem_cons.1 hq with rfl | hq
    · exact .thm (Provable.imp_self _)
    · exact .mp (.thm (.ax1 _ _)) (.hyp hq)
  | mp _ _ ih1 ih2 => exact .mp (.mp (.thm (.ax2 _ _ _)) ih1) ih2

/-- A derivation from no hypotheses is a proof. -/
theorem Der.provable {p : Fml} (h : Der [] p) : Provable p := by
  induction h with
  | thm hp => exact hp
  | hyp hp => cases hp
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

/-- Monotonicity of `□`: from `⊢ p → q`, `⊢ □p → □q`. -/
theorem Provable.box_mono {p q : Fml} (h : Provable (.imp p q)) :
    Provable (.imp (.box p) (.box q)) :=
  .mp (.axK p q) (.nec h)

/-- Hypothetical syllogism. -/
theorem Provable.trans {p q r : Fml} (h1 : Provable (.imp p q)) (h2 : Provable (.imp q r)) :
    Provable (.imp p r) := by
  have : Der [p] r := .mp (.thm h2) (.mp (.thm h1) (.hyp (List.mem_singleton.2 rfl)))
  exact this.deduction.provable

/-- Ex falso: `⊢ ⊥ → p`. -/
theorem Provable.bot_imp (p : Fml) : Provable (.imp .bot p) :=
  .mp (.ax3 p .bot) (.mp (.ax1 Fml.bot.neg p.neg) (Provable.imp_self .bot))

/-- Weakening of derivations. -/
theorem Der.mono {Γ Δ : List Fml} {p : Fml} (h : Der Γ p) (hsub : ∀ q ∈ Γ, q ∈ Δ) : Der Δ p := by
  induction h with
  | thm hp => exact .thm hp
  | hyp hp => exact .hyp (hsub _ hp)
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

/-- Double-negation elimination: `⊢ ¬¬p → p`. -/
theorem Provable.dne (p : Fml) : Provable (.imp p.neg.neg p) := by
  have h1 : Der [p.neg.neg, p.neg] Fml.bot :=
    Der.mp (p := p.neg) (Der.hyp (List.mem_cons_self ..))
      (Der.hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have h2 : Provable (.imp p.neg p.neg.neg.neg) := h1.deduction.deduction.provable
  exact .mp (.ax3 p p.neg.neg) h2

/-- A set of hypotheses is consistent when it does not derive `⊥`. -/
def Consistent (Γ : List Fml) : Prop := ¬ Der Γ .bot

/-- If `Γ` does not derive `p`, then `¬p :: Γ` is consistent. -/
theorem consistent_neg_of_not_der {Γ : List Fml} {p : Fml} (h : ¬ Der Γ p) :
    Consistent (p.neg :: Γ) := fun hc =>
  h (.mp (.thm (Provable.dne p)) hc.deduction)

/-- Conjunction `p ∧ q := ¬(p → ¬q)`. -/
def Fml.and (p q : Fml) : Fml := (Fml.imp p q.neg).neg

/-- Membership helpers for short hypothesis lists. -/
private theorem mem0 {a : Fml} {l : List Fml} : a ∈ a :: l := List.mem_cons_self ..
private theorem mem1 {a b : Fml} {l : List Fml} : b ∈ a :: b :: l :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)
private theorem mem2 {a b c : Fml} {l : List Fml} : c ∈ a :: b :: c :: l :=
  List.mem_cons_of_mem _ mem1

/-- `⊢ p → (q → p ∧ q)`. -/
theorem Provable.and_intro (p q : Fml) : Provable (.imp p (.imp q (p.and q))) := by
  have h : Der [Fml.imp p q.neg, q, p] Fml.bot :=
    Der.mp (p := q) (Der.mp (p := p) (Der.hyp mem0) (Der.hyp mem2)) (Der.hyp mem1)
  exact h.deduction.deduction.deduction.provable

/-- `⊢ p ∧ q → p`. -/
theorem Provable.and_left (p q : Fml) : Provable (.imp (p.and q) p) := by
  have h1 : Der [p, p.neg, p.and q] q.neg :=
    Der.mp (Der.thm (Provable.bot_imp _)) (Der.mp (p := p) (Der.hyp mem1) (Der.hyp mem0))
  have h2 : Der [p.neg, p.and q] Fml.bot :=
    Der.mp (p := Fml.imp p q.neg) (Der.hyp mem1) (h1.deduction)
  exact Provable.trans h2.deduction.deduction.provable (Provable.dne p)

/-- `⊢ p ∧ q → q`. -/
theorem Provable.and_right (p q : Fml) : Provable (.imp (p.and q) q) := by
  have h2 : Der [q.neg, p.and q] Fml.bot :=
    Der.mp (p := Fml.imp p q.neg) (Der.hyp mem1) (Der.mp (Der.thm (.ax1 _ _)) (Der.hyp mem0))
  exact Provable.trans h2.deduction.deduction.provable (Provable.dne q)

/-- **GL proves axiom 4**: `⊢ □p → □□p` (Löb's axiom applied to `p ∧ □p`). -/
theorem Provable.four (p : Fml) : Provable (.imp (.box p) (.box (.box p))) := by
  -- `⊢ p → (□(p ∧ □p) → p ∧ □p)`
  have h1 : Der [Fml.box (p.and (.box p)), p] (p.and (.box p)) :=
    Der.mp (Der.mp (Der.thm (Provable.and_intro _ _)) (Der.hyp mem1))
      (Der.mp (Der.thm (Provable.box_mono (Provable.and_left _ _))) (Der.hyp mem0))
  have h2 : Provable (.imp p (.imp (.box (p.and (.box p))) (p.and (.box p)))) :=
    h1.deduction.deduction.provable
  have h3 : Provable (.imp (.box p) (.box (p.and (.box p)))) :=
    Provable.trans (Provable.box_mono h2) (.axLoeb _)
  exact Provable.trans h3 (Provable.box_mono (Provable.and_right _ _))

/-- Cut: hypotheses derivable from `Γ` can be discharged. -/
theorem Der.cut {Γ Δ : List Fml} {p : Fml} (h : Der Δ p) (hΔ : ∀ q ∈ Δ, Der Γ q) : Der Γ p := by
  induction h with
  | thm hp => exact .thm hp
  | hyp hp => exact hΔ _ hp
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2

/-- **Boxing a derivation**: from `Γ ⊢ p`, `□Γ ⊢ □p`. -/
theorem Der.box_of {Γ : List Fml} {p : Fml} (h : Der Γ p) : Der (Γ.map Fml.box) (.box p) := by
  induction Γ generalizing p with
  | nil => exact .thm (.nec h.provable)
  | cons a Γ ih =>
    have h1 : Der (Γ.map Fml.box) (.box (.imp a p)) := ih h.deduction
    have h2 : Der (Γ.map Fml.box) (.imp (.box a) (.box p)) := .mp (.thm (.axK _ _)) h1
    exact .mp (h2.mono fun q hq => List.mem_cons_of_mem _ hq) (.hyp List.mem_cons_self)

/-- **The modal lemma of GL**: if `□ψ` together with the boxed hypotheses `□B` and their bodies `B`
derives `ψ`, then `□B` derives `□ψ` (Löb's axiom and axiom 4). -/
theorem Der.loeb_rule {B : List Fml} {ψ : Fml}
    (h : Der (ψ.box :: (B ++ B.map Fml.box)) ψ) : Der (B.map Fml.box) ψ.box := by
  have h1 : Der ((B ++ B.map Fml.box).map Fml.box) (.box (.imp ψ.box ψ)) := h.deduction.box_of
  have h2 : Der ((B ++ B.map Fml.box).map Fml.box) ψ.box := .mp (.thm (.axLoeb _)) h1
  refine h2.cut fun q hq => ?_
  simp only [List.map_append, List.mem_append, List.mem_map] at hq
  rcases hq with ⟨b, hb, rfl⟩ | ⟨c, ⟨b, hb, rfl⟩, rfl⟩
  · exact .hyp (List.mem_map.2 ⟨b, hb, rfl⟩)
  · exact .mp (.thm (Provable.four b)) (.hyp (List.mem_map.2 ⟨b, hb, rfl⟩))

/-- If `p :: Γ` is inconsistent and `Γ` is consistent, then `¬p :: Γ` is consistent. -/
theorem consistent_neg_of_inconsistent {Γ : List Fml} {p : Fml} (hΓ : Consistent Γ)
    (h : ¬ Consistent (p :: Γ)) : Consistent (p.neg :: Γ) := by
  intro hn
  have h1 : Der Γ p.neg := Classical.not_not.1 h |>.deduction
  have h2 : Der Γ p.neg.neg := hn.deduction
  exact hΓ (.mp h2 h1)

/-- **Lindenbaum's lemma inside a finite list of formulas**: a consistent `Γ` extends to a
consistent `Δ` that decides every formula of `L` (it contains it or its negation), and adds
nothing but members of `L` and their negations. -/
theorem lindenbaum (L : List Fml) : ∀ {Γ : List Fml}, Consistent Γ →
    ∃ Δ : List Fml, (∀ q ∈ Γ, q ∈ Δ) ∧ Consistent Δ ∧ (∀ φ ∈ L, φ ∈ Δ ∨ φ.neg ∈ Δ) ∧
      (∀ q ∈ Δ, q ∈ Γ ∨ ∃ φ ∈ L, q = φ ∨ q = φ.neg) := by
  induction L with
  | nil => intro Γ hΓ; exact ⟨Γ, fun q hq => hq, hΓ, by simp, fun q hq => .inl hq⟩
  | cons φ L ih =>
    intro Γ hΓ
    classical
    by_cases hc : Consistent (φ :: Γ)
    · obtain ⟨Δ, hsub, hcons, hdec, hrange⟩ := ih hc
      refine ⟨Δ, fun q hq => hsub q (List.mem_cons_of_mem _ hq), hcons, ?_, ?_⟩
      · intro ψ hψ
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact .inl (hsub _ List.mem_cons_self)
        · exact hdec ψ hψ
      · intro q hq
        rcases hrange q hq with hq | ⟨χ, hχ, he⟩
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact .inr ⟨q, List.mem_cons_self, .inl rfl⟩
          · exact .inl hq
        · exact .inr ⟨χ, List.mem_cons_of_mem _ hχ, he⟩
    · have hc' := consistent_neg_of_inconsistent hΓ hc
      obtain ⟨Δ, hsub, hcons, hdec, hrange⟩ := ih hc'
      refine ⟨Δ, fun q hq => hsub q (List.mem_cons_of_mem _ hq), hcons, ?_, ?_⟩
      · intro ψ hψ
        rcases List.mem_cons.1 hψ with rfl | hψ
        · exact .inr (hsub _ List.mem_cons_self)
        · exact hdec ψ hψ
      · intro q hq
        rcases hrange q hq with hq | ⟨χ, hχ, he⟩
        · rcases List.mem_cons.1 hq with rfl | hq
          · exact .inr ⟨φ, List.mem_cons_self, .inr rfl⟩
          · exact .inl hq
        · exact .inr ⟨χ, List.mem_cons_of_mem _ hχ, he⟩

/-- The subformulas of a formula (with repetitions). -/
def Fml.sub : Fml → List Fml
  | .var n => [.var n]
  | .bot => [.bot]
  | .imp p q => .imp p q :: (p.sub ++ q.sub)
  | .box p => .box p :: p.sub

theorem Fml.mem_sub_self (p : Fml) : p ∈ p.sub := by
  cases p <;> simp [Fml.sub]

/-- Subformula closure is transitive. -/
theorem Fml.sub_trans {p q r : Fml} (hq : q ∈ p.sub) (hr : r ∈ q.sub) : r ∈ p.sub := by
  induction p with
  | var n => simp [Fml.sub] at hq; subst hq; exact hr
  | bot => simp [Fml.sub] at hq; subst hq; exact hr
  | imp a b iha ihb =>
    simp only [Fml.sub, List.mem_cons, List.mem_append] at hq ⊢
    rcases hq with rfl | hq | hq
    · simpa [Fml.sub] using hr
    · exact .inr (.inl (iha hq))
    · exact .inr (.inr (ihb hq))
  | box a ih =>
    simp only [Fml.sub, List.mem_cons] at hq ⊢
    rcases hq with rfl | hq
    · simpa [Fml.sub] using hr
    · exact .inr (ih hq)

/-- The accessibility relation of the canonical GL model on sets of formulas: every boxed formula
of `Γ` and its body are in `Δ`, and some boxed formula of `Δ` is not in `Γ`. -/
def CanR (Γ Δ : Finset Fml) : Prop :=
  (∀ ψ : Fml, ψ.box ∈ Γ → ψ ∈ Δ ∧ ψ.box ∈ Δ) ∧ ∃ ψ : Fml, ψ.box ∈ Δ ∧ ψ.box ∉ Γ

theorem CanR.trans {Γ Δ Ξ : Finset Fml} (h1 : CanR Γ Δ) (h2 : CanR Δ Ξ) : CanR Γ Ξ := by
  refine ⟨fun ψ hψ => h2.1 ψ (h1.1 ψ hψ).2, ?_⟩
  obtain ⟨χ, hχΞ, hχΔ⟩ := h2.2
  exact ⟨χ, hχΞ, fun hχΓ => hχΔ (h1.1 χ hχΓ).2⟩

theorem CanR.irrefl (Γ : Finset Fml) : ¬ CanR Γ Γ := fun h => by
  obtain ⟨χ, h1, h2⟩ := h.2
  exact h2 h1

/-- A consistent list deciding `L` is deductively closed on `L`. -/
theorem mem_of_der {Δ : List Fml} {ψ : Fml} (hcons : Consistent Δ) (hdec : ψ ∈ Δ ∨ ψ.neg ∈ Δ)
    (h : Der Δ ψ) : ψ ∈ Δ := by
  rcases hdec with h' | h'
  · exact h'
  · exact absurd (.mp (.hyp h') h) hcons

/-- Implication in a consistent list deciding `a`, `b` and `a → b`. -/
theorem imp_mem_iff {Δ : List Fml} {a b : Fml} (hcons : Consistent Δ)
    (ha : a ∈ Δ ∨ a.neg ∈ Δ) (hb : b ∈ Δ ∨ b.neg ∈ Δ) (hab : a.imp b ∈ Δ ∨ (a.imp b).neg ∈ Δ) :
    a.imp b ∈ Δ ↔ (a ∈ Δ → b ∈ Δ) := by
  constructor
  · intro h haΔ
    exact mem_of_der hcons hb (.mp (.hyp h) (.hyp haΔ))
  · intro h
    apply mem_of_der hcons hab
    rcases ha with haΔ | hna
    · exact .mp (.thm (.ax1 _ _)) (.hyp (h haΔ))
    · have : Der (a :: Δ) b :=
        .mp (.thm (Provable.bot_imp b)) (.mp (.hyp (List.mem_cons_of_mem _ hna)) (.hyp mem0))
      exact this.deduction

end ModalGL
