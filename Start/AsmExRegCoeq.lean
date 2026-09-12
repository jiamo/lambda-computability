/-
**Coequalizers of internal equivalence relations in the exact completion of the assemblies.**

`Start/AsmExRegRegular.lean` makes the completion a regular category, and
`Start/AsmExRegNotExact.lean` shows that it is *not* exact: an internal equivalence relation of
the completion need not be the kernel pair of its coequalizer.  What is true, and is proved here,
is the other half of exactness: **every internal equivalence relation of the completion does have
a coequalizer.**

Let `p₁, p₂ : R ⟶ E` be an internal equivalence relation in the sense of
`Realizability.ExReg.NotExact.IsInternalEquiv`, presented by pre-morphisms `f₁, f₂`.  The
quotient is the base of `E` with a *coarser* relation: a proof that `x` and `y` are related is a
point `r` of the base of `R` together with a realizer of it and proofs, in `E`, that `f₁ r` is
related to `x` and `f₂ r` to `y`.  Reflexivity, symmetry and transitivity of that relation are
exactly the diagonal, the swap and the composition of the equivalence relation, read on
realizers; transitivity needs the object of *composable pairs*, which is built here so that the
transitivity morphism can be applied to it.

Main definitions:

* `Realizability.ExReg.Coeq.EqvData` — the computational data of an internal equivalence
  relation, read on representatives, and `Realizability.ExReg.Coeq.eqvData_of_isInternalEquiv` —
  how to obtain it from `Realizability.ExReg.NotExact.IsInternalEquiv`;
* `Realizability.ExReg.Coeq.compERel` — the object of composable pairs, with its two projections
  `.compFst`, `.compSnd`;
* `Realizability.ExReg.Coeq.coeqObj`, `.coeqPre` — the quotient and the map onto it.

Main results:

* `Realizability.ExReg.Coeq.coeqCoforkIsColimit` — **the quotient really is the coequalizer**;
* `Realizability.ExReg.Coeq.hasCoequalizer_of_isInternalEquiv` — **every internal equivalence
  relation of the completion has a coequalizer.**
-/

import Start.AsmExRegNotExact

set_option relaxedAutoImplicit false
set_option autoImplicit false

universe u v

namespace Realizability

open CategoryTheory CategoryTheory.Limits

namespace ExReg

variable {A : Type u} [PCA A]

/-! ### Binary combinators

The proofs below build trackers of two arguments — the two proofs a transitivity tracker
consumes — out of smaller ones.  These four lemmas are the combinators `λab. r a`, `λab. r b`,
`λab. r (X a b)` and `λab. t (X a b) (Y a b)`; with the pairing combinator they express every
binary tracker used here. -/

/-- The combinator `λab. r a`. -/
theorem exists_binLeft (r : A) : ∃ q : A, ∀ a b u : A, u ∈ PCA.app r a →
    u ∈ (Part.some q ⬝ Part.some a) ⬝ Part.some b := by
  refine ⟨PCA.lam2 (Expr.app (Expr.const r) (Expr.var 0)), fun a b u hu => ?_⟩
  refine PCA.lam2_app_app _ a b _ ?_
  have : Part.some u ≤ Part.some r ⬝ Part.some a := by
    rw [papp_some_some]; exact some_le_of_mem hu
  simpa [Expr.eval, Function.update_of_ne] using this _ (Part.mem_some _)

/-- The combinator `λab. r b`. -/
theorem exists_binRight (r : A) : ∃ q : A, ∀ a b u : A, u ∈ PCA.app r b →
    u ∈ (Part.some q ⬝ Part.some a) ⬝ Part.some b := by
  refine ⟨PCA.lam2 (Expr.app (Expr.const r) (Expr.var 1)), fun a b u hu => ?_⟩
  refine PCA.lam2_app_app _ a b _ ?_
  have : Part.some u ≤ Part.some r ⬝ Part.some b := by
    rw [papp_some_some]; exact some_le_of_mem hu
  simpa [Expr.eval, Function.update_of_ne] using this _ (Part.mem_some _)

/-- The combinator `λab. t (X a b) (Y a b)`. -/
theorem exists_binApply (t x y : A) : ∃ q : A, ∀ a b u w v : A,
    u ∈ (Part.some x ⬝ Part.some a) ⬝ Part.some b →
    w ∈ (Part.some y ⬝ Part.some a) ⬝ Part.some b →
    v ∈ (Part.some t ⬝ Part.some u) ⬝ Part.some w →
    v ∈ (Part.some q ⬝ Part.some a) ⬝ Part.some b := by
  refine ⟨PCA.lam2 (Expr.app (Expr.app (Expr.const t)
      (Expr.app (Expr.app (Expr.const x) (Expr.var 0)) (Expr.var 1)))
      (Expr.app (Expr.app (Expr.const y) (Expr.var 0)) (Expr.var 1))),
    fun a b u w v hu hw hv => ?_⟩
  refine PCA.lam2_app_app _ a b _ ?_
  have hmono : (Part.some t ⬝ Part.some u) ⬝ Part.some w
      ≤ (Part.some t ⬝ ((Part.some x ⬝ Part.some a) ⬝ Part.some b))
        ⬝ ((Part.some y ⬝ Part.some a) ⬝ Part.some b) :=
    papp_mono (papp_mono le_rfl (some_le_of_mem hu)) (some_le_of_mem hw)
  simpa [Expr.eval, Function.update_of_ne] using hmono _ hv

/-- The combinator `λab. r (X a b)`. -/
theorem exists_binComp (r x : A) : ∃ q : A, ∀ a b u v : A,
    u ∈ (Part.some x ⬝ Part.some a) ⬝ Part.some b → v ∈ PCA.app r u →
    v ∈ (Part.some q ⬝ Part.some a) ⬝ Part.some b := by
  refine ⟨PCA.lam2 (Expr.app (Expr.const r)
      (Expr.app (Expr.app (Expr.const x) (Expr.var 0)) (Expr.var 1))), fun a b u v hu hv => ?_⟩
  refine PCA.lam2_app_app _ a b _ ?_
  have hmono : Part.some r ⬝ Part.some u
      ≤ Part.some r ⬝ ((Part.some x ⬝ Part.some a) ⬝ Part.some b) :=
    papp_mono le_rfl (some_le_of_mem hu)
  have hmem : v ∈ Part.some r ⬝ ((Part.some x ⬝ Part.some a) ⬝ Part.some b) := by
    refine hmono _ ?_
    rw [papp_some_some]; exact hv
  simpa [Expr.eval, Function.update_of_ne] using hmem

/-- The combinator `λab. pair (X a b) (Y a b)`. -/
theorem exists_binPairOf (x y : A) : ∃ q : A, ∀ a b u w : A,
    u ∈ (Part.some x ⬝ Part.some a) ⬝ Part.some b →
    w ∈ (Part.some y ⬝ Part.some a) ⬝ Part.some b →
    PCA.pairEl u w ∈ (Part.some q ⬝ Part.some a) ⬝ Part.some b := by
  obtain ⟨q, hq⟩ := exists_binApply (PCA.pairComb A) x y
  exact ⟨q, fun a b u w hu hw =>
    hq a b u w _ hu hw (by rw [PCA.pairComb_app]; exact Part.mem_some _)⟩

namespace Coeq

open NotExact

/-! ### Reading the components of a nested pair

Every tracker below consumes a proof that is a nested pair, and the four combinators of this
section apply an element to one of its components. -/

/-- The combinator `λw. r (fst w)`. -/
theorem exists_fThen (r : A) : ∃ q : A, ∀ a b u : A, u ∈ PCA.app r a →
    u ∈ PCA.app q (PCA.pairEl a b) :=
  ⟨PCA.comp r (PCA.fstComb A), fun a b _ hu => mem_comp (mem_fstComb a b) hu⟩

/-- The combinator `λw. r (snd w)`. -/
theorem exists_sThen (r : A) : ∃ q : A, ∀ a b u : A, u ∈ PCA.app r b →
    u ∈ PCA.app q (PCA.pairEl a b) :=
  ⟨PCA.comp r (PCA.sndComb A), fun a b _ hu => mem_comp (mem_sndComb a b) hu⟩

/-- The combinator `λw. r (fst (fst w))`. -/
theorem exists_ffThen (r : A) : ∃ q : A, ∀ a b c u : A, u ∈ PCA.app r a →
    u ∈ PCA.app q (PCA.pairEl (PCA.pairEl a b) c) := by
  obtain ⟨q₁, h₁⟩ := exists_fThen r
  obtain ⟨q₂, h₂⟩ := exists_fThen q₁
  exact ⟨q₂, fun a b c u hu => h₂ _ c u (h₁ a b u hu)⟩

/-- The combinator `λw. r (snd (fst w))`. -/
theorem exists_fsThen (r : A) : ∃ q : A, ∀ a b c u : A, u ∈ PCA.app r b →
    u ∈ PCA.app q (PCA.pairEl (PCA.pairEl a b) c) := by
  obtain ⟨q₁, h₁⟩ := exists_sThen r
  obtain ⟨q₂, h₂⟩ := exists_fThen q₁
  exact ⟨q₂, fun a b c u hu => h₂ _ c u (h₁ a b u hu)⟩

/-- The combinator `λw. r (fst (snd w))`. -/
theorem exists_sfThen (r : A) : ∃ q : A, ∀ a b c u : A, u ∈ PCA.app r b →
    u ∈ PCA.app q (PCA.pairEl a (PCA.pairEl b c)) := by
  obtain ⟨q₁, h₁⟩ := exists_fThen r
  obtain ⟨q₂, h₂⟩ := exists_sThen q₁
  exact ⟨q₂, fun a b c u hu => h₂ a _ u (h₁ b c u hu)⟩

/-- The combinator `λw. r (snd (snd w))`. -/
theorem exists_ssThen (r : A) : ∃ q : A, ∀ a b c u : A, u ∈ PCA.app r c →
    u ∈ PCA.app q (PCA.pairEl a (PCA.pairEl b c)) := by
  obtain ⟨q₁, h₁⟩ := exists_sThen r
  obtain ⟨q₂, h₂⟩ := exists_sThen q₁
  exact ⟨q₂, fun a b c u hu => h₂ a _ u (h₁ b c u hu)⟩

/-- The identity, as a tracker: `λa. a`. -/
theorem mem_i (a : A) : a ∈ PCA.app (PCA.i A) a := by
  rw [PCA.i_app]; exact Part.mem_some _

variable {E R : ERel.{u, v} A}

/-! ### The data of an internal equivalence relation -/

/-- The computational data of an **internal equivalence relation** `f₁, f₂ : R ⟶ E`, read on
pre-morphisms: a diagonal, a swap, and a composition of composable pairs. -/
structure EqvData (f₁ f₂ : Pre R E) where
  /-- The diagonal. -/
  diag : Pre E R
  /-- The first leg of the diagonal is the identity. -/
  diag_fst : Homotopic (diag.comp f₁) (Pre.id E)
  /-- The second leg of the diagonal is the identity. -/
  diag_snd : Homotopic (diag.comp f₂) (Pre.id E)
  /-- The swap. -/
  swap : Pre R R
  /-- The swap exchanges the two legs. -/
  swap_fst : Homotopic (swap.comp f₁) f₂
  /-- The swap exchanges the two legs. -/
  swap_snd : Homotopic (swap.comp f₂) f₁
  /-- Two maps into `R` with matching middle endpoints have a composite. -/
  comp' : ∀ {T : ERel.{u, v} A} (g h : Pre T R), Homotopic (g.comp f₂) (h.comp f₁) →
    ∃ k : Pre T R, Homotopic (k.comp f₁) (g.comp f₁) ∧ Homotopic (k.comp f₂) (h.comp f₂)

/-- A chosen representative of a morphism of the completion. -/
noncomputable def rep {X Y : ERel.{u, v} A} (f : X ⟶ Y) : Pre X Y :=
  (homOf_surjective f).choose

@[simp] theorem homOf_rep {X Y : ERel.{u, v} A} (f : X ⟶ Y) : homOf (rep f) = f :=
  (homOf_surjective f).choose_spec

/-- **An internal equivalence relation carries that data**, read on any representatives of its
two legs. -/
theorem eqvData_of_isInternalEquiv (f₁ f₂ : Pre R E)
    (h : IsInternalEquiv (homOf f₁) (homOf f₂)) : Nonempty (EqvData f₁ f₂) := by
  obtain ⟨d, hd₁, hd₂⟩ := h.refl'
  obtain ⟨s, hs₁, hs₂⟩ := h.symm'
  refine ⟨{ diag := rep d
            diag_fst := ?_
            diag_snd := ?_
            swap := rep s
            swap_fst := ?_
            swap_snd := ?_
            comp' := ?_ }⟩
  · refine homOf_eq_iff.1 ?_
    rw [← homOf_comp, homOf_rep, hd₁, id_eq]
  · refine homOf_eq_iff.1 ?_
    rw [← homOf_comp, homOf_rep, hd₂, id_eq]
  · exact homOf_eq_iff.1 (by rw [← homOf_comp, homOf_rep, hs₁])
  · exact homOf_eq_iff.1 (by rw [← homOf_comp, homOf_rep, hs₂])
  · intro T g k hgk
    have hgk' : homOf g ≫ homOf f₂ = homOf k ≫ homOf f₁ := by
      rw [homOf_comp, homOf_comp]; exact homOf_eq_iff.2 hgk
    obtain ⟨m, hm₁, hm₂⟩ := h.trans' (homOf g) (homOf k) hgk'
    refine ⟨rep m, homOf_eq_iff.1 ?_, homOf_eq_iff.1 ?_⟩
    · rw [← homOf_comp, ← homOf_comp, homOf_rep]; exact hm₁
    · rw [← homOf_comp, ← homOf_comp, homOf_rep]; exact hm₂

/-! ### The object of composable pairs -/

/-- The assembly of **composable pairs**: pairs of points of `R` whose middle endpoints are
related, realized by their realizers together with a proof of that relation. -/
def compAsm (f₁ f₂ : Pre R E) : Assembly.{u, v} A where
  carrier := {q : R.base.carrier × R.base.carrier // E.rel (f₂.toFun q.1) (f₁.toFun q.2)}
  realizes w q := ∃ a b p : A, R.base.realizes a q.val.1 ∧ R.base.realizes b q.val.2 ∧
    E.Prf p (f₂.toFun q.val.1) (f₁.toFun q.val.2) ∧ w = PCA.pairEl (PCA.pairEl a b) p
  exists_realizer q := by
    obtain ⟨a, ha⟩ := R.base.exists_realizer q.val.1
    obtain ⟨b, hb⟩ := R.base.exists_realizer q.val.2
    obtain ⟨p, hp⟩ := q.property
    exact ⟨_, a, b, p, ha, hb, hp, rfl⟩

/-- The object of composable pairs: two of them are related when their components are, a proof
carrying in addition the two middle proofs, which is what keeps the endpoints computable. -/
def compERel (f₁ f₂ : Pre R E) : ERel.{u, v} A where
  base := compAsm f₁ f₂
  Prf w q q' := ∃ s t p p' : A, R.Prf s q.val.1 q'.val.1 ∧ R.Prf t q.val.2 q'.val.2 ∧
    E.Prf p (f₂.toFun q.val.1) (f₁.toFun q.val.2) ∧
    E.Prf p' (f₂.toFun q'.val.1) (f₁.toFun q'.val.2) ∧
    w = PCA.pairEl (PCA.pairEl s t) (PCA.pairEl p p')
  ends := by
    obtain ⟨pf, hpf⟩ := R.exists_fstTracker
    obtain ⟨ps, hps⟩ := R.exists_sndTracker
    obtain ⟨a₁, ha₁⟩ := exists_ffThen pf
    obtain ⟨a₂, ha₂⟩ := exists_fsThen pf
    obtain ⟨a₃, ha₃⟩ := exists_sfThen (PCA.i A)
    obtain ⟨b₁, hb₁⟩ := exists_ffThen ps
    obtain ⟨b₂, hb₂⟩ := exists_fsThen ps
    obtain ⟨b₃, hb₃⟩ := exists_ssThen (PCA.i A)
    obtain ⟨c₁, hc₁⟩ := exists_pairOf a₁ a₂
    obtain ⟨c₂, hc₂⟩ := exists_pairOf c₁ a₃
    obtain ⟨d₁, hd₁⟩ := exists_pairOf b₁ b₂
    obtain ⟨d₂, hd₂⟩ := exists_pairOf d₁ b₃
    obtain ⟨t, ht⟩ := exists_pairOf c₂ d₂
    refine ⟨t, ?_⟩
    rintro w q q' ⟨s, tt, p, p', hs, htt, hp, hp', rfl⟩
    obtain ⟨va, hva, hvar⟩ := hpf s q.val.1 q'.val.1 hs
    obtain ⟨vb, hvb, hvbr⟩ := hpf tt q.val.2 q'.val.2 htt
    obtain ⟨vc, hvc, hvcr⟩ := hps s q.val.1 q'.val.1 hs
    obtain ⟨vd, hvd, hvdr⟩ := hps tt q.val.2 q'.val.2 htt
    refine ⟨_, ht _ _ _ (hc₂ _ _ _ (hc₁ _ _ _ (ha₁ s tt _ va hva) (ha₂ s tt _ vb hvb))
      (ha₃ _ p p' p (mem_i p))) (hd₂ _ _ _ (hd₁ _ _ _ (hb₁ s tt _ vc hvc) (hb₂ s tt _ vd hvd))
      (hb₃ _ p p' p' (mem_i p'))), _, _, ⟨va, vb, p, hvar, hvbr, hp, rfl⟩,
      ⟨vc, vd, p', hvcr, hvdr, hp', rfl⟩, rfl⟩
  refl' := by
    obtain ⟨rr, hrr⟩ := R.refl'
    obtain ⟨a₁, ha₁⟩ := exists_ffThen rr
    obtain ⟨a₂, ha₂⟩ := exists_fsThen rr
    obtain ⟨a₃, ha₃⟩ := exists_sThen (PCA.i A)
    obtain ⟨c₁, hc₁⟩ := exists_pairOf a₁ a₂
    obtain ⟨c₂, hc₂⟩ := exists_pairOf a₃ a₃
    obtain ⟨t, ht⟩ := exists_pairOf c₁ c₂
    refine ⟨t, ?_⟩
    rintro w q ⟨a, b, p, ha, hb, hp, rfl⟩
    obtain ⟨va, hva, hvar⟩ := hrr a q.val.1 ha
    obtain ⟨vb, hvb, hvbr⟩ := hrr b q.val.2 hb
    exact ⟨_, ht _ _ _ (hc₁ _ _ _ (ha₁ a b p va hva) (ha₂ a b p vb hvb))
      (hc₂ _ _ _ (ha₃ _ p p (mem_i p)) (ha₃ _ p p (mem_i p))),
      va, vb, p, p, hvar, hvbr, hp, hp, rfl⟩
  symm' := by
    obtain ⟨sr, hsr⟩ := R.symm'
    obtain ⟨a₁, ha₁⟩ := exists_ffThen sr
    obtain ⟨a₂, ha₂⟩ := exists_fsThen sr
    obtain ⟨a₃, ha₃⟩ := exists_ssThen (PCA.i A)
    obtain ⟨a₄, ha₄⟩ := exists_sfThen (PCA.i A)
    obtain ⟨c₁, hc₁⟩ := exists_pairOf a₁ a₂
    obtain ⟨c₂, hc₂⟩ := exists_pairOf a₃ a₄
    obtain ⟨t, ht⟩ := exists_pairOf c₁ c₂
    refine ⟨t, ?_⟩
    rintro w q q' ⟨s, tt, p, p', hs, htt, hp, hp', rfl⟩
    obtain ⟨va, hva, hvar⟩ := hsr s q.val.1 q'.val.1 hs
    obtain ⟨vb, hvb, hvbr⟩ := hsr tt q.val.2 q'.val.2 htt
    exact ⟨_, ht _ _ _ (hc₁ _ _ _ (ha₁ s tt _ va hva) (ha₂ s tt _ vb hvb))
      (hc₂ _ _ _ (ha₃ _ p p' p' (mem_i p')) (ha₄ _ p p' p (mem_i p))),
      va, vb, p', p, hvar, hvbr, hp', hp, rfl⟩
  trans' := by
    obtain ⟨tr, htr⟩ := R.trans'
    obtain ⟨gs, hgs⟩ := exists_ffThen (PCA.i A)
    obtain ⟨gt, hgt⟩ := exists_fsThen (PCA.i A)
    obtain ⟨gp, hgp⟩ := exists_sfThen (PCA.i A)
    obtain ⟨gp', hgp'⟩ := exists_ssThen (PCA.i A)
    obtain ⟨x₁, hx₁⟩ := exists_binLeft gs
    obtain ⟨y₁, hy₁⟩ := exists_binRight gs
    obtain ⟨c₁, hc₁⟩ := exists_binApply tr x₁ y₁
    obtain ⟨x₂, hx₂⟩ := exists_binLeft gt
    obtain ⟨y₂, hy₂⟩ := exists_binRight gt
    obtain ⟨c₂, hc₂⟩ := exists_binApply tr x₂ y₂
    obtain ⟨c₃, hc₃⟩ := exists_binLeft gp
    obtain ⟨c₄, hc₄⟩ := exists_binRight gp'
    obtain ⟨e₁, he₁⟩ := exists_binPairOf c₁ c₂
    obtain ⟨e₂, he₂⟩ := exists_binPairOf c₃ c₄
    obtain ⟨t, ht⟩ := exists_binPairOf e₁ e₂
    refine ⟨t, ?_⟩
    rintro w w' q q' q'' ⟨s, tt, p, p', hs, htt, hp, hp', rfl⟩
      ⟨s', tt', p'', p''', hs', htt', hp'', hp''', rfl⟩
    obtain ⟨va, hva, hvar⟩ := htr s s' q.val.1 q'.val.1 q''.val.1 hs hs'
    obtain ⟨vb, hvb, hvbr⟩ := htr tt tt' q.val.2 q'.val.2 q''.val.2 htt htt'
    refine ⟨_, ht _ _ _ _
      (he₁ _ _ _ _
        (hc₁ _ _ s s' va (hx₁ _ _ s (hgs s tt _ s (mem_i s)))
          (hy₁ _ _ s' (hgs s' tt' _ s' (mem_i s'))) hva)
        (hc₂ _ _ tt tt' vb (hx₂ _ _ tt (hgt s tt _ tt (mem_i tt)))
          (hy₂ _ _ tt' (hgt s' tt' _ tt' (mem_i tt'))) hvb))
      (he₂ _ _ _ _ (hc₃ _ _ p (hgp _ p p' p (mem_i p)))
        (hc₄ _ _ p''' (hgp' _ p'' p''' p''' (mem_i p''')))),
      va, vb, p, p''', hvar, hvbr, hp, hp''', rfl⟩

/-- The first projection of the object of composable pairs. -/
def compFst (f₁ f₂ : Pre R E) : Pre (compERel f₁ f₂) R where
  toFun q := q.val.1
  tracked := by
    obtain ⟨gs, hgs⟩ := exists_ffThen (PCA.i A)
    refine ⟨gs, ?_⟩
    rintro w q q' ⟨s, tt, p, p', hs, -, -, -, rfl⟩
    exact ⟨s, hgs s tt _ s (mem_i s), hs⟩

/-- The second projection of the object of composable pairs. -/
def compSnd (f₁ f₂ : Pre R E) : Pre (compERel f₁ f₂) R where
  toFun q := q.val.2
  tracked := by
    obtain ⟨gt, hgt⟩ := exists_fsThen (PCA.i A)
    refine ⟨gt, ?_⟩
    rintro w q q' ⟨s, tt, p, p', -, htt, -, -, rfl⟩
    exact ⟨tt, hgt s tt _ tt (mem_i tt), htt⟩

/-- The two projections of the object of composable pairs are composable: the middle proof is
part of every realizer. -/
theorem compHomotopic (f₁ f₂ : Pre R E) :
    Homotopic ((compFst f₁ f₂).comp f₂) ((compSnd f₁ f₂).comp f₁) := by
  refine ⟨PCA.sndComb A, ?_⟩
  rintro w q ⟨a, b, p, -, -, hp, rfl⟩
  exact ⟨p, mem_sndComb _ p, hp⟩

/-- The composite of a composable pair. -/
noncomputable def compPt {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) : Pre (compERel f₁ f₂) R :=
  (d.comp' (compFst f₁ f₂) (compSnd f₁ f₂) (compHomotopic f₁ f₂)).choose

theorem compPt_fst {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) :
    Homotopic ((compPt d).comp f₁) ((compFst f₁ f₂).comp f₁) :=
  (d.comp' (compFst f₁ f₂) (compSnd f₁ f₂) (compHomotopic f₁ f₂)).choose_spec.1

theorem compPt_snd {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) :
    Homotopic ((compPt d).comp f₂) ((compSnd f₁ f₂).comp f₂) :=
  (d.comp' (compFst f₁ f₂) (compSnd f₁ f₂) (compHomotopic f₁ f₂)).choose_spec.2

/-! ### The quotient -/

/-- A proof of the quotient relation: a point of `R` with a realizer, and proofs in `E` that its
two endpoints are related to the two points. -/
def CoeqPrf (f₁ f₂ : Pre R E) (w : A) (x y : E.base.carrier) : Prop :=
  ∃ (r : R.base.carrier) (a c₁ c₂ : A), R.base.realizes a r ∧
    E.Prf c₁ (f₁.toFun r) x ∧ E.Prf c₂ (f₂.toFun r) y ∧ w = PCA.pairEl a (PCA.pairEl c₁ c₂)

/-- **The quotient of an internal equivalence relation**: the base of `E`, with the relation
generated by the two legs. -/
def coeqObj {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) : ERel.{u, v} A where
  base := E.base
  Prf := CoeqPrf f₁ f₂
  ends := by
    obtain ⟨pe, hpe⟩ := E.exists_sndTracker
    obtain ⟨a₁, ha₁⟩ := exists_sfThen pe
    obtain ⟨a₂, ha₂⟩ := exists_ssThen pe
    obtain ⟨t, ht⟩ := exists_pairOf a₁ a₂
    refine ⟨t, ?_⟩
    rintro w x y ⟨r, a, c₁, c₂, -, hc₁, hc₂, rfl⟩
    obtain ⟨vx, hvx, hvxr⟩ := hpe c₁ (f₁.toFun r) x hc₁
    obtain ⟨vy, hvy, hvyr⟩ := hpe c₂ (f₂.toFun r) y hc₂
    exact ⟨_, ht _ _ _ (ha₁ a c₁ c₂ vx hvx) (ha₂ a c₁ c₂ vy hvy), vx, vy, hvxr, hvyr, rfl⟩
  refl' := by
    obtain ⟨td, htd⟩ := d.diag.trackedBase
    obtain ⟨h₁, hh₁⟩ := d.diag_fst
    obtain ⟨h₂, hh₂⟩ := d.diag_snd
    obtain ⟨c, hc⟩ := exists_pairOf h₁ h₂
    obtain ⟨t, ht⟩ := exists_pairOf td c
    refine ⟨t, ?_⟩
    intro a x ha
    obtain ⟨vr, hvr, hvrr⟩ := htd a x ha
    obtain ⟨v₁, hv₁, hv₁p⟩ := hh₁ a x ha
    obtain ⟨v₂, hv₂, hv₂p⟩ := hh₂ a x ha
    exact ⟨_, ht a _ _ hvr (hc a _ _ hv₁ hv₂), d.diag.toFun x, vr, v₁, v₂, hvrr,
      hv₁p, hv₂p, rfl⟩
  symm' := by
    obtain ⟨ts, hts⟩ := d.swap.trackedBase
    obtain ⟨s₁, hs₁⟩ := d.swap_fst
    obtain ⟨s₂, hs₂⟩ := d.swap_snd
    obtain ⟨te, hte⟩ := E.trans'
    obtain ⟨ga, hga⟩ := exists_fThen ts
    obtain ⟨gb, hgb⟩ := exists_fThen s₁
    obtain ⟨gc, hgc⟩ := exists_fThen s₂
    obtain ⟨gd, hgd⟩ := exists_ssThen (PCA.i A)
    obtain ⟨ge, hge⟩ := exists_sfThen (PCA.i A)
    obtain ⟨u₁, hu₁⟩ := exists_pairApply te gb gd
    obtain ⟨u₂, hu₂⟩ := exists_pairApply te gc ge
    obtain ⟨c, hc⟩ := exists_pairOf u₁ u₂
    obtain ⟨t, ht⟩ := exists_pairOf ga c
    refine ⟨t, ?_⟩
    rintro w x y ⟨r, a, c₁, c₂, ha, hc₁, hc₂, rfl⟩
    obtain ⟨vr, hvr, hvrr⟩ := hts a r ha
    obtain ⟨v₁, hv₁, hv₁p⟩ := hs₁ a r ha
    obtain ⟨v₂, hv₂, hv₂p⟩ := hs₂ a r ha
    obtain ⟨w₁, hw₁, hw₁p⟩ := hte v₁ c₂ (f₁.toFun (d.swap.toFun r)) (f₂.toFun r) y hv₁p hc₂
    obtain ⟨w₂, hw₂, hw₂p⟩ := hte v₂ c₁ (f₂.toFun (d.swap.toFun r)) (f₁.toFun r) x hv₂p hc₁
    refine ⟨_, ht _ _ _ (hga a _ vr hvr) (hc _ _ _
      (hu₁ _ v₁ c₂ w₁ (hgb a _ v₁ hv₁) (hgd a c₁ c₂ c₂ (mem_i c₂)) hw₁)
      (hu₂ _ v₂ c₁ w₂ (hgc a _ v₂ hv₂) (hge a c₁ c₂ c₁ (mem_i c₁)) hw₂)),
      d.swap.toFun r, vr, w₁, w₂, hvrr, hw₁p, hw₂p, rfl⟩
  trans' := by
    obtain ⟨te, hte⟩ := E.trans'
    obtain ⟨se, hse⟩ := E.symm'
    obtain ⟨tk, htk⟩ := (compPt d).trackedBase
    obtain ⟨k₁, hk₁⟩ := compPt_fst d
    obtain ⟨k₂, hk₂⟩ := compPt_snd d
    obtain ⟨ga, hga⟩ := exists_fThen (PCA.i A)
    obtain ⟨gc₁, hgc₁⟩ := exists_sfThen (PCA.i A)
    obtain ⟨gc₂, hgc₂⟩ := exists_ssThen (PCA.i A)
    obtain ⟨xa, hxa⟩ := exists_binLeft ga
    obtain ⟨xb, hxb⟩ := exists_binRight ga
    obtain ⟨xp, hxp⟩ := exists_binPairOf xa xb
    obtain ⟨yc, hyc⟩ := exists_binLeft gc₂
    obtain ⟨yd, hyd⟩ := exists_binRight gc₁
    obtain ⟨ye, hye⟩ := exists_binComp se yd
    obtain ⟨yp, hyp⟩ := exists_binApply te yc ye
    obtain ⟨gq, hgq⟩ := exists_binPairOf xp yp
    obtain ⟨z₀, hz₀⟩ := exists_binComp tk gq
    obtain ⟨z₁, hz₁⟩ := exists_binComp k₁ gq
    obtain ⟨z₂, hz₂⟩ := exists_binComp k₂ gq
    obtain ⟨za, hza⟩ := exists_binLeft gc₁
    obtain ⟨zb, hzb⟩ := exists_binRight gc₂
    obtain ⟨w₁, hw₁⟩ := exists_binApply te z₁ za
    obtain ⟨w₂, hw₂⟩ := exists_binApply te z₂ zb
    obtain ⟨c, hc⟩ := exists_binPairOf w₁ w₂
    obtain ⟨t, ht⟩ := exists_binPairOf z₀ c
    refine ⟨t, ?_⟩
    rintro wa wb x y z ⟨r, a, c₁, c₂, ha, hc₁, hc₂, rfl⟩ ⟨r', a', c₁', c₂', ha', hc₁', hc₂', rfl⟩
    -- the middle proof, and the composable pair it makes
    obtain ⟨sc, hsc, hscp⟩ := hse c₁' (f₁.toFun r') y hc₁'
    obtain ⟨pm, hpm, hpmp⟩ := hte c₂ sc (f₂.toFun r) y (f₁.toFun r') hc₂ hscp
    let q : (compAsm f₁ f₂).carrier := ⟨(r, r'), ⟨pm, hpmp⟩⟩
    have hq : (compAsm f₁ f₂).realizes (PCA.pairEl (PCA.pairEl a a') pm) q :=
      ⟨a, a', pm, ha, ha', hpmp, rfl⟩
    have hgqm : PCA.pairEl (PCA.pairEl a a') pm ∈
        (Part.some gq ⬝ Part.some (PCA.pairEl a (PCA.pairEl c₁ c₂))) ⬝
          Part.some (PCA.pairEl a' (PCA.pairEl c₁' c₂')) :=
      hgq _ _ _ _
        (hxp _ _ _ _ (hxa _ _ a (hga a _ a (mem_i a))) (hxb _ _ a' (hga a' _ a' (mem_i a'))))
        (hyp _ _ c₂ sc pm (hyc _ _ c₂ (hgc₂ a c₁ c₂ c₂ (mem_i c₂)))
          (hye _ _ c₁' sc (hyd _ _ c₁' (hgc₁ a' c₁' c₂' c₁' (mem_i c₁'))) hsc) hpm)
    obtain ⟨vr, hvr, hvrr⟩ := htk _ q hq
    obtain ⟨v₁, hv₁, hv₁p⟩ := hk₁ _ q hq
    obtain ⟨v₂, hv₂, hv₂p⟩ := hk₂ _ q hq
    obtain ⟨u₁, hu₁, hu₁p⟩ :=
      hte v₁ c₁ (f₁.toFun ((compPt d).toFun q)) (f₁.toFun r) x hv₁p hc₁
    obtain ⟨u₂, hu₂, hu₂p⟩ :=
      hte v₂ c₂' (f₂.toFun ((compPt d).toFun q)) (f₂.toFun r') z hv₂p hc₂'
    refine ⟨_, ht _ _ _ _ (hz₀ _ _ _ vr hgqm hvr)
      (hc _ _ _ _
        (hw₁ _ _ v₁ c₁ u₁ (hz₁ _ _ _ v₁ hgqm hv₁)
          (hza _ _ c₁ (hgc₁ a c₁ c₂ c₁ (mem_i c₁))) hu₁)
        (hw₂ _ _ v₂ c₂' u₂ (hz₂ _ _ _ v₂ hgqm hv₂)
          (hzb _ _ c₂' (hgc₂ a' c₁' c₂' c₂' (mem_i c₂'))) hu₂)),
      (compPt d).toFun q, vr, u₁, u₂, hvrr, hu₁p, hu₂p, rfl⟩

/-- The map onto the quotient: the identity on points. -/
def coeqPre {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) : Pre E (coeqObj d) where
  toFun x := x
  tracked := by
    obtain ⟨pe, hpe⟩ := E.exists_fstTracker
    obtain ⟨td, htd⟩ := d.diag.trackedBase
    obtain ⟨h₁, hh₁⟩ := d.diag_fst
    obtain ⟨h₂, hh₂⟩ := d.diag_snd
    obtain ⟨te, hte⟩ := E.trans'
    obtain ⟨u₂, hu₂⟩ := exists_pairApply te (PCA.comp h₂ pe) (PCA.i A)
    obtain ⟨c, hc⟩ := exists_pairOf (PCA.comp h₁ pe) u₂
    obtain ⟨t, ht⟩ := exists_pairOf (PCA.comp td pe) c
    refine ⟨t, ?_⟩
    intro w x y hw
    obtain ⟨ax, hax, haxr⟩ := hpe w x y hw
    obtain ⟨vr, hvr, hvrr⟩ := htd ax x haxr
    obtain ⟨v₁, hv₁, hv₁p⟩ := hh₁ ax x haxr
    obtain ⟨v₂, hv₂, hv₂p⟩ := hh₂ ax x haxr
    obtain ⟨v₃, hv₃, hv₃p⟩ := hte v₂ w (f₂.toFun (d.diag.toFun x)) x y hv₂p hw
    exact ⟨_, ht w _ _ (mem_comp hax hvr)
      (hc w _ _ (mem_comp hax hv₁) (hu₂ w v₂ w v₃ (mem_comp hax hv₂) (mem_i w) hv₃)),
      d.diag.toFun x, vr, v₁, v₃, hvrr, hv₁p, hv₃p, rfl⟩

/-- The two legs become homotopic after the quotient map. -/
theorem coeq_homotopic {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) :
    Homotopic (f₁.comp (coeqPre d)) (f₂.comp (coeqPre d)) := by
  obtain ⟨re, hre⟩ := E.refl'
  obtain ⟨t₁, ht₁⟩ := f₁.trackedBase
  obtain ⟨t₂, ht₂⟩ := f₂.trackedBase
  obtain ⟨c, hc⟩ := exists_pairOf (PCA.comp re t₁) (PCA.comp re t₂)
  obtain ⟨t, ht⟩ := exists_pairOf (PCA.i A) c
  refine ⟨t, ?_⟩
  intro a r ha
  obtain ⟨x₁, hx₁, hx₁r⟩ := ht₁ a r ha
  obtain ⟨x₂, hx₂, hx₂r⟩ := ht₂ a r ha
  obtain ⟨p₁, hp₁, hp₁p⟩ := hre x₁ (f₁.toFun r) hx₁r
  obtain ⟨p₂, hp₂, hp₂p⟩ := hre x₂ (f₂.toFun r) hx₂r
  exact ⟨_, ht a a _ (mem_i a) (hc a _ _ (mem_comp hx₁ hp₁) (mem_comp hx₂ hp₂)),
    r, a, p₁, p₂, ha, hp₁p, hp₂p, rfl⟩

/-! ### The universal property -/

/-- A map out of `E` which identifies the two legs descends to the quotient. -/
def descPre {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) {Z : ERel.{u, v} A} (G : Pre E Z)
    (hG : Homotopic (f₁.comp G) (f₂.comp G)) : Pre (coeqObj d) Z where
  toFun := G.toFun
  tracked := by
    obtain ⟨tg, htg⟩ := G.tracked
    obtain ⟨sz, hsz⟩ := Z.symm'
    obtain ⟨tz, htz⟩ := Z.trans'
    obtain ⟨hg, hhg⟩ := hG
    obtain ⟨ga, hga⟩ := exists_fThen (PCA.i A)
    obtain ⟨gc₁, hgc₁⟩ := exists_sfThen (PCA.i A)
    obtain ⟨gc₂, hgc₂⟩ := exists_ssThen (PCA.i A)
    obtain ⟨e₁, he₁⟩ := exists_pairApply tz (PCA.comp sz (PCA.comp tg gc₁))
      (PCA.comp hg ga)
    obtain ⟨t, ht⟩ := exists_pairApply tz e₁ (PCA.comp tg gc₂)
    refine ⟨t, ?_⟩
    rintro w x y ⟨r, a, c₁, c₂, ha, hc₁, hc₂, rfl⟩
    obtain ⟨z₁, hz₁, hz₁p⟩ := htg c₁ (f₁.toFun r) x hc₁
    obtain ⟨z₁', hz₁', hz₁'p⟩ := hsz z₁ (G.toFun (f₁.toFun r)) (G.toFun x) hz₁p
    obtain ⟨z₂, hz₂, hz₂p⟩ := hhg a r ha
    obtain ⟨z₃, hz₃, hz₃p⟩ := htg c₂ (f₂.toFun r) y hc₂
    obtain ⟨y₁, hy₁, hy₁p⟩ :=
      htz z₁' z₂ (G.toFun x) (G.toFun (f₁.toFun r)) (G.toFun (f₂.toFun r)) hz₁'p hz₂p
    obtain ⟨y₂, hy₂, hy₂p⟩ :=
      htz y₁ z₃ (G.toFun x) (G.toFun (f₂.toFun r)) (G.toFun y) hy₁p hz₃p
    refine ⟨y₂, ht _ y₁ z₃ y₂
      (he₁ _ z₁' z₂ y₁
        (mem_comp (mem_comp (hgc₁ a c₁ c₂ c₁ (mem_i c₁)) hz₁) hz₁')
        (mem_comp (hga a _ a (mem_i a)) hz₂) hy₁)
      (mem_comp (hgc₂ a c₁ c₂ c₂ (mem_i c₂)) hz₃) hy₂, hy₂p⟩

theorem coeq_comp_descPre {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) {Z : ERel.{u, v} A}
    (G : Pre E Z) (hG : Homotopic (f₁.comp G) (f₂.comp G)) :
    (coeqPre d).comp (descPre d G hG) = G := Pre.ext rfl

/-- The quotient map is an epimorphism: the quotient has the same base, with the same
realizers. -/
instance epi_coeqPre {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) : Epi (homOf (coeqPre d)) where
  left_cancellation {W} g h hgh := by
    obtain ⟨G, rfl⟩ := homOf_surjective g
    obtain ⟨H, rfl⟩ := homOf_surjective h
    rw [homOf_comp, homOf_comp, homOf_eq_iff] at hgh
    obtain ⟨t, ht⟩ := hgh
    exact homOf_eq_iff.2 ⟨t, fun a x ha => ht a x ha⟩

/-- The cofork given by the quotient map. -/
noncomputable def coeqCofork {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) :
    Cofork (homOf f₁) (homOf f₂) :=
  Cofork.ofπ (homOf (coeqPre d)) (by
    rw [homOf_comp, homOf_comp]
    exact homOf_eq_iff.2 (coeq_homotopic d))

@[simp] theorem coeqCofork_π {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) :
    Cofork.π (coeqCofork d) = homOf (coeqPre d) := rfl

/-- The condition of a cofork, read on a representative of its leg. -/
theorem homotopic_of_cofork {f₁ f₂ : Pre R E} (s : Cofork (homOf f₁) (homOf f₂)) :
    Homotopic (f₁.comp (rep (Cofork.π s))) (f₂.comp (rep (Cofork.π s))) := by
  refine homOf_eq_iff.1 ?_
  rw [← homOf_comp, ← homOf_comp, homOf_rep]
  exact s.condition

/-- **The quotient is the coequalizer of the two legs.** -/
noncomputable def coeqCoforkIsColimit {f₁ f₂ : Pre R E} (d : EqvData f₁ f₂) :
    IsColimit (coeqCofork d) :=
  Cofork.IsColimit.mk _
    (fun s => homOf (descPre d (rep (Cofork.π s)) (homotopic_of_cofork s)))
    (fun s => by
      have h : homOf ((coeqPre d).comp
          (descPre d (rep (Cofork.π s)) (homotopic_of_cofork s)))
          = homOf (rep (Cofork.π s)) := congrArg homOf (coeq_comp_descPre _ _ _)
      rw [homOf_rep] at h
      exact h)
    (fun s m hm => by
      have h : homOf ((coeqPre d).comp
          (descPre d (rep (Cofork.π s)) (homotopic_of_cofork s)))
          = homOf (rep (Cofork.π s)) := congrArg homOf (coeq_comp_descPre _ _ _)
      rw [homOf_rep] at h
      have hfac : Cofork.π (coeqCofork d) ≫
          homOf (descPre d (rep (Cofork.π s)) (homotopic_of_cofork s)) = Cofork.π s := h
      exact (cancel_epi (homOf (coeqPre d))).1 (hm.trans hfac.symm))

/-- **Every internal equivalence relation of the completion has a coequalizer**, even though, by
`Realizability.ExReg.NotExact.exists_internalEquiv_not_kernelPair`, it need not be the kernel
pair of that coequalizer. -/
theorem hasCoequalizer_of_isInternalEquiv {R E : ERel.{u, v} A} (p₁ p₂ : R ⟶ E)
    (h : IsInternalEquiv p₁ p₂) : HasCoequalizer p₁ p₂ := by
  obtain ⟨f₁, rfl⟩ := homOf_surjective p₁
  obtain ⟨f₂, rfl⟩ := homOf_surjective p₂
  obtain ⟨d⟩ := eqvData_of_isInternalEquiv f₁ f₂ h
  exact ⟨⟨⟨coeqCofork d, coeqCoforkIsColimit d⟩⟩⟩

end Coeq

end ExReg

end Realizability
