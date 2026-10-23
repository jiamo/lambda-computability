/-
**`TEq.typeLevel` is false** — task `M23-LF-EQUIV-COMPLETE` (big round 2, run 1, item W2).

The first missing lemma recorded for this task since round 10 was

    TEq.typeLevel : TEq Γ M N T → Wf Γ → (T a kind or □) → TypeLevel Γ M ∧ TypeLevel Γ N.

It is refuted here.  The declarative equality `TEq` (`Start/LambdaPiLFEquiv.lean`) has the η-rule,
while the typing judgement `Typing` converts types by β only.  In the well-formed context

    A0 : ∗,  g : A0 → A0,  Q : (A0 → A0) → ∗,  c : Π h : A0 → A0. Q h,  F : Q (λy:A0. g y) → ∗

the rules `TEq.app`, `TEq.refl` and `TEq.eta` derive `F (c (λy. g y)) ≡ F (c g) : ∗`, and `∗` is a
kind; but `F (c g)` has no type at all: `c g : Q g`, `F` expects `Q (λy. g y)`, and `Q g` and
`Q (λy. g y)` are distinct β-normal forms, hence not β-convertible.

* `LambdaPi.tc_wf`, `LambdaPi.tc_teq` — the context is well formed and the equation is derivable;
* `LambdaPi.tc_N_untyped` — `F (c g)` is not typable (inversion `Typing.app_inv`,
  `Typing.var_inv`, product injectivity and confluence of β);
* **`LambdaPi.teq_typeLevel_counterexample`** — the conjunction: `TEq.typeLevel` fails.

So validity for `TEq` needs a typing judgement whose conversion rule is βη-conversion (or `TEq`
itself, as in Harper–Pfenning); with β-typing it is false already at the type level.
-/

import Start.LambdaPiLFSkelTEq

set_option autoImplicit false

namespace LambdaPi

open Tm

/-- The context `A0 : ∗, g : A0 → A0, Q : (A0 → A0) → ∗, c : Π h. Q h, F : Q (λy. g y) → ∗`. -/
def tcA0 : Tm := sort Srt.star
def tcG : Tm := pi (var 0) (var 1)
def tcQ : Tm := pi (pi (var 1) (var 2)) (sort Srt.star)
def tcC : Tm := pi (pi (var 2) (var 3)) (app (var 1) (var 0))
def tcF : Tm := pi (app (var 1) (lam (var 3) (app (var 3) (var 0)))) (sort Srt.star)
def tcΓ : Ctx := [tcF, tcC, tcQ, tcG, tcA0]

/-- `F (c (λy. g y))` and `F (c g)`. -/
def tcM : Tm := app (var 0) (app (var 1) (lam (var 4) (app (var 4) (var 0))))
def tcN : Tm := app (var 0) (app (var 1) (var 3))

theorem tc_lookup0 : Lookup tcΓ 0 (pi (app (var 2) (lam (var 4) (app (var 4) (var 0))))
    (sort Srt.star)) := Lookup.zero _ _

theorem tc_lookup1 : Lookup tcΓ 1 (pi (pi (var 4) (var 5)) (app (var 3) (var 0))) :=
  Lookup.succ _ (Lookup.zero _ _)

theorem tc_lookup3 : Lookup tcΓ 3 (pi (var 4) (var 5)) :=
  Lookup.succ _ (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _)))

theorem tc_teq : TEq tcΓ tcM tcN (sort Srt.star) := by
  have hc : TEq tcΓ (app (var 1) (lam (var 4) (app (var 4) (var 0)))) (app (var 1) (var 3))
      (app (var 2) (lam (var 4) (app (var 4) (var 0)))) := by
    have := TEq.app (TEq.refl (Typing.var tc_lookup1)) (TEq.eta (Typing.var tc_lookup3))
    exact this
  exact TEq.app (TEq.refl (Typing.var tc_lookup0)) hc

theorem tc_nf1 (w : Tm) (h : Step (app (var 2) (var 3)) w) : False := by
  rcases Step.app_inv h with ⟨_, _, h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;> cases h1

theorem tc_nf2 (w : Tm) (h : Step (app (var 2) (lam (var 4) (app (var 4) (var 0)))) w) : False := by
  rcases Step.app_inv h with ⟨_, _, h1, _⟩ | ⟨_, h1, _⟩ | ⟨_, h1, _⟩
  · cases h1
  · cases h1
  · rcases Step.lam_inv h1 with ⟨_, h2, _⟩ | ⟨_, h2, _⟩
    · cases h2
    · rcases Step.app_inv h2 with ⟨_, _, h3, _⟩ | ⟨_, h3, _⟩ | ⟨_, h3, _⟩ <;> cases h3

theorem Red.eq_of_noStep {t v : Tm} (h : Red t v) (hn : ∀ w, Step t w → False) : v = t := by
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact (hn _ hs).elim

theorem tc_wf : Wf tcΓ := by
  have h1 : Wf [tcA0] := Wf.cons (s := Srt.box) Wf.nil (Typing.ax [])
  have hg : Typing [tcA0] tcG (sort Srt.star) :=
    Typing.pi (s := Srt.star) (t := Srt.star) rfl (Typing.var (Lookup.zero _ _))
      (Typing.var (Lookup.succ _ (Lookup.zero _ _)))
  have h2 : Wf [tcG, tcA0] := Wf.cons h1 hg
  have hq : Typing [tcG, tcA0] tcQ (sort Srt.box) :=
    Typing.pi (s := Srt.star) (t := Srt.box) rfl
      (Typing.pi (s := Srt.star) (t := Srt.star) rfl (Typing.var (Lookup.succ _ (Lookup.zero _ _)))
        (Typing.var (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _)))))
      (Typing.ax _)
  have h3 : Wf [tcQ, tcG, tcA0] := Wf.cons h2 hq
  have hc : Typing [tcQ, tcG, tcA0] tcC (sort Srt.star) :=
    Typing.pi (s := Srt.star) (t := Srt.star) rfl
      (Typing.pi (s := Srt.star) (t := Srt.star) rfl
        (Typing.var (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _))))
        (Typing.var (Lookup.succ _ (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _))))))
      (Typing.app (A := pi (var 3) (var 4)) (B := sort Srt.star)
        (Typing.var (Lookup.succ _ (Lookup.zero _ _))) (Typing.var (Lookup.zero _ _)))
  have h4 : Wf [tcC, tcQ, tcG, tcA0] := Wf.cons h3 hc
  have hpi : Typing [tcC, tcQ, tcG, tcA0] (pi (var 3) (var 4)) (sort Srt.star) :=
    Typing.pi (s := Srt.star) (t := Srt.star) rfl
      (Typing.var (Lookup.succ _ (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _)))))
      (Typing.var (Lookup.succ _ (Lookup.succ _ (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _))))))
  have hbody : Typing (var 3 :: [tcC, tcQ, tcG, tcA0]) (app (var 3) (var 0)) (var 4) :=
    Typing.app (A := var 4) (B := var 5)
      (Typing.var (Lookup.succ _ (Lookup.succ _ (Lookup.succ _ (Lookup.zero _ _)))))
      (Typing.var (Lookup.zero _ _))
  have hlam : Typing [tcC, tcQ, tcG, tcA0] (lam (var 3) (app (var 3) (var 0))) (pi (var 3) (var 4)) :=
    Typing.lam hpi hbody
  have hf : Typing [tcC, tcQ, tcG, tcA0] tcF (sort Srt.box) :=
    Typing.pi (s := Srt.star) (t := Srt.box) rfl
      (Typing.app (A := pi (var 3) (var 4)) (B := sort Srt.star)
        (Typing.var (Lookup.succ _ (Lookup.zero _ _))) hlam) (Typing.ax _)
  exact Wf.cons h4 hf

/-- **`F (c g)` has no type**: its argument has type `Q g`, while `F` expects `Q (λy. g y)`, and
the two are not β-convertible. -/
theorem tc_N_untyped (T : Tm) : ¬ Typing tcΓ tcN T := by
  intro h
  obtain ⟨A, B, hf, ha, -⟩ := h.app_inv
  obtain ⟨A0, hl0, hc0⟩ := hf.var_inv
  have e0 := Lookup.det hl0 tc_lookup0
  subst e0
  have hA := pi_inj_left hc0
  obtain ⟨A', B', hc, -, hconv⟩ := ha.app_inv
  obtain ⟨A1, hl1, hc1⟩ := hc.var_inv
  have e1 := Lookup.det hl1 tc_lookup1
  subst e1
  have hB := (pi_inj_right hc1).subst (scons (var 3) ids)
  have hfin : Conv (app (var 2) (var 3)) (app (var 2) (lam (var 4) (app (var 4) (var 0)))) :=
    (hB.trans hconv).trans hA.symm
  obtain ⟨v, h1, h2⟩ := hfin.church_rosser
  have := (h1.eq_of_noStep tc_nf1).symm.trans (h2.eq_of_noStep tc_nf2)
  simp at this

/-- **`TEq.typeLevel` is false**: `F (c (λy. g y)) ≡ F (c g) : ∗` is derivable, `∗` is a kind,
the context is well formed, and `F (c g)` is not type-level (it has no type at all). -/
theorem teq_typeLevel_counterexample :
    ∃ (Γ : Ctx) (M N T : Tm), Wf Γ ∧ TEq Γ M N T ∧ IsKind Γ T ∧ ¬ TypeLevel Γ N := by
  refine ⟨tcΓ, tcM, tcN, sort Srt.star, tc_wf, tc_teq, isKind_star _, ?_⟩
  intro hN
  obtain ⟨T, hT⟩ := hN.typing
  exact tc_N_untyped T hT

end LambdaPi
