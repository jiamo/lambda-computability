/-
**Creative sets and Myhill's completeness theorem.**

`Start/PostSimple.lean` and `Start/PostIncomplete.lean` exhibit the *thin* side of Post's
programme: a simple set is r.e., undecidable, and too thin to be many-one complete.  This module
records the opposite extreme.  A set is **creative** when it is r.e. and its complement is
productive; the halting set is the standard example.  Myhill's theorem says that creativity is
exactly a positive form of completeness:

* `Lambda.Post.exists_recursion_index` — **the recursion theorem with parameters**, in the form
  needed here: for a partial recursive `G` of three arguments there is a computable `h` with
  `W (h x) = {y | G (h x) x y ↓}`, i.e. the `x`-th set may refer to its own index;
* `Lambda.Post.manyOneReducible_of_productive_compl` — **Myhill's theorem**: if the complement of
  `C` is productive then every r.e. set many-one reduces to `C`;
* `Lambda.Post.Creative.manyOneComplete`, `Lambda.Post.Creative.manyOneEquiv_haltK` — hence every
  creative set is many-one complete, and so many-one equivalent to the halting set;
* `Lambda.Post.creative_of_manyOneComplete`, `Lambda.Post.creative_iff_manyOneComplete` — the
  converse holds too, so for r.e. sets creativity *is* many-one completeness;
* `Lambda.Post.Creative.not_simple`, `Lambda.Post.not_creative_simpleSet` — no creative set is
  simple, and Post's set in particular is not creative.

The construction behind Myhill's theorem is the classical one: given an r.e. set `A`, use the
recursion theorem to name a set `W (h x)` which is `{p (h x)}` if `x ∈ A` and `∅` otherwise, where
`p` is the production function of the complement of `C`.  Then `x ↦ p (h x)` is a many-one
reduction of `A` to `C`.
-/

import Start.PostIncomplete

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Lambda

namespace Post

open Nat.Partrec (Code)
open Encodable Denumerable

/-! ### The recursion theorem with parameters -/

/-- **The recursion theorem with parameters.**  Given a partial recursive `G e x y` there is a
computable `h` such that the r.e. set named by `h x` is the domain of `G (h x) x`: the set may use
its own index. -/
theorem exists_recursion_index (G : ℕ → ℕ → ℕ →. ℕ)
    (hG : Partrec fun q : ℕ × ℕ × ℕ => G q.1 q.2.1 q.2.2) :
    ∃ h : ℕ → ℕ, Computable h ∧ ∀ x y, (Wset (h x) y ↔ (G (h x) x y).Dom) := by
  have hcurry : Computable fun p : Code × ℕ =>
      Encodable.encode (Code.curry p.1 (Nat.unpair p.2).1) :=
    (Primrec.encode.comp (Code.primrec₂_curry.comp Primrec.fst
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))).to_comp
  have hF : Partrec₂ fun (c : Code) (n : ℕ) =>
      G (Encodable.encode (Code.curry c (Nat.unpair n).1)) (Nat.unpair n).1 (Nat.unpair n).2 :=
    hG.comp (hcurry.pair (((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
      (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd))).to_comp))
  obtain ⟨c, hc⟩ := Code.fixed_point₂ hF
  refine ⟨fun x => Encodable.encode (Code.curry c x),
    (Primrec.encode.comp (Code.primrec₂_curry.comp (Primrec.const c) Primrec.id)).to_comp,
    fun x y => ?_⟩
  simp only [Wset, Denumerable.ofNat_encode, Code.eval_curry, hc, Nat.unpair_pair]

/-- Deciding equality of two computable numerical functions is computable. -/
theorem computable_decide_eq {α : Type} [Primcodable α] {f g : α → ℕ}
    (hf : Computable f) (hg : Computable g) : Computable fun a => decide (f a = g a) :=
  (primrec_decide (Primrec.eq.comp Primrec.fst Primrec.snd)).to_comp.comp (hf.pair hg)

/-! ### Creative sets -/

/-- A set is **creative** when it is r.e. and its complement is productive. -/
def Creative (C : ℕ → Prop) : Prop := REPred C ∧ Productive fun x => ¬ C x

/-- **The halting set is creative.** -/
theorem creative_haltK : Creative HaltK := ⟨rePred_haltK, productive_compl_haltK⟩

/-- **A productive set is not r.e.**: the production function applied to an index of the set
itself produces an element of the set outside it. -/
theorem Productive.not_rePred {P : ℕ → Prop} (hP : Productive P) : ¬ REPred P := by
  obtain ⟨f, -, hf⟩ := hP
  intro hre
  obtain ⟨e, he⟩ := exists_index hre
  obtain ⟨hmem, hnot⟩ := hf e fun x hx => (he x).2 hx
  exact hnot ((he (f e)).1 hmem)

/-- **A creative set is not computable**: its complement is productive, hence not r.e. -/
theorem Creative.not_computablePred {C : ℕ → Prop} (hC : Creative C) : ¬ ComputablePred C := by
  classical
  exact fun hcomp => hC.2.not_rePred (ComputablePred.computable_iff_re_compl_re.1 hcomp).2

/-! ### Myhill's theorem -/

/-- **Myhill's theorem.**  If the complement of `C` is productive, then every r.e. set many-one
reduces to `C`.

Given an r.e. set `A`, the recursion theorem names a set `W (h x)` equal to `{p (h x)}` when
`x ∈ A` and to `∅` otherwise, `p` being the production function.  If `x ∈ A` then `p (h x)` must
lie in `C`, since otherwise `W (h x)` would be an r.e. subset of the complement containing its own
produced element; if `x ∉ A` then `W (h x) = ∅` is a subset of the complement, so `p (h x)` lies
outside `C`. -/
theorem manyOneReducible_of_productive_compl {C A : ℕ → Prop}
    (hC : Productive fun x => ¬ C x) (hA : REPred A) : A ≤₀ C := by
  obtain ⟨p, hp, hprod⟩ := hC
  have hsd : Partrec fun x : ℕ => Part.assert (A x) fun _ => Part.some (0 : ℕ) := by
    have := hA.map (g := fun (_ : ℕ) (_ : Unit) => (0 : ℕ)) (Computable.const 0)
    refine this.of_eq fun x => ?_
    ext v
    simp [Part.mem_assert_iff, eq_comm]
  have hG : Partrec fun q : ℕ × ℕ × ℕ =>
      bif decide (q.2.2 = p q.1) then (Part.assert (A q.2.1) fun _ => Part.some (0 : ℕ))
      else Part.none := by
    have hcond : Computable fun q : ℕ × ℕ × ℕ => decide (q.2.2 = p q.1) :=
      computable_decide_eq (Computable.snd.comp Computable.snd) (hp.comp Computable.fst)
    exact Partrec.cond hcond (hsd.comp (Computable.fst.comp Computable.snd)) Partrec.none
  obtain ⟨h, hh, hspec⟩ := exists_recursion_index
    (fun e x y => bif decide (y = p e) then (Part.assert (A x) fun _ => Part.some (0 : ℕ))
      else Part.none) hG
  refine ⟨fun x => p (h x), hp.comp hh, fun x => ?_⟩
  have hW : ∀ y, Wset (h x) y ↔ (y = p (h x) ∧ A x) := by
    intro y
    rw [hspec x y]
    by_cases hy : y = p (h x) <;> simp [hy, Part.assert]
  constructor
  · intro hAx
    by_contra hnC
    have hsub : ∀ y, Wset (h x) y → ¬ C y := by
      intro y hy
      rw [hW y] at hy
      exact hy.1 ▸ hnC
    exact (hprod (h x) hsub).2 ((hW _).2 ⟨rfl, hAx⟩)
  · intro hCx
    by_contra hAx
    have hsub : ∀ y, Wset (h x) y → ¬ C y := by
      intro y hy
      rw [hW y] at hy
      exact absurd hy.2 hAx
    exact (hprod (h x) hsub).1 hCx

/-- **Every creative set is many-one complete.** -/
theorem Creative.manyOneComplete {C : ℕ → Prop} (hC : Creative C) :
    ∀ q : ℕ → Prop, REPred q → q ≤₀ C :=
  fun _ hq => manyOneReducible_of_productive_compl hC.2 hq

/-- **Every creative set is many-one equivalent to the halting set.** -/
theorem Creative.manyOneEquiv_haltK {C : ℕ → Prop} (hC : Creative C) : ManyOneEquiv C HaltK :=
  ⟨rePred_le_haltK hC.1, hC.manyOneComplete HaltK rePred_haltK⟩

/-- **Any two creative sets are many-one equivalent.** -/
theorem Creative.manyOneEquiv {C D : ℕ → Prop} (hC : Creative C) (hD : Creative D) :
    ManyOneEquiv C D :=
  ⟨hD.manyOneComplete C hC.1, hC.manyOneComplete D hD.1⟩

/-- **The converse of Myhill's completeness theorem**: a many-one complete r.e. set is creative.
The halting set reduces to it, and productivity of a complement travels backwards along a many-one
reduction. -/
theorem creative_of_manyOneComplete {C : ℕ → Prop} (hre : REPred C)
    (hcomplete : ∀ q : ℕ → Prop, REPred q → q ≤₀ C) : Creative C :=
  ⟨hre, Productive.of_manyOneReducible (hcomplete HaltK rePred_haltK) productive_compl_haltK⟩

/-- **Myhill's characterization of many-one completeness**: for r.e. sets, being creative and being
many-one complete are the same thing. -/
theorem creative_iff_manyOneComplete {C : ℕ → Prop} :
    Creative C ↔ REPred C ∧ ∀ q : ℕ → Prop, REPred q → q ≤₀ C :=
  ⟨fun hC => ⟨hC.1, hC.manyOneComplete⟩, fun h => creative_of_manyOneComplete h.1 h.2⟩

/-- **No creative set is simple**: creative sets are many-one complete and simple sets are not. -/
theorem Creative.not_simple {C : ℕ → Prop} (hC : Creative C) : ¬ Simple C :=
  fun hS => hS.not_manyOneComplete hC.manyOneComplete

/-- **Post's simple set is not creative.** -/
theorem not_creative_simpleSet : ¬ Creative simpleSet :=
  fun hC => hC.not_simple simple_simpleSet

end Post

end Lambda
