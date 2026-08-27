/-
# Compiling a Cobham term into a P-uniform family of circuits

The modules `Start/UniformSignal.lean`, `Start/UniformSigApp.lean`, `Start/UniformSigComp.lean` and
`Start/UniformSigBound.lean` supply the compiler with one rule per shape of Cobham term: the
projections, the empty word, the successors, and composition.  This module puts those rules
together by structural induction, and so turns a term of the corresponding *fragment* of the
Cobham algebra into a P-uniform family of circuits realizing its value.

The fragment is described by the predicate `Complexity.SigShape`: a term of arity `r` built from
projections of an argument that exists, the empty word, the successors, and composition.  Such a
term lengthens its argument only by a constant, `Complexity.addLen`, so a width of `n + addLen v`
wires suffices for the arguments of length at most `n`, and the compiler needs no further
hypothesis.

The two shapes still missing are `Cob.smash` and `Cob.bRec`; a term using either of them is not
covered by `SigShape`, and compiling those is what remains before an arbitrary Cobham term can be
turned into a stage circuit.

Main definitions:

* `Complexity.addLen` — the constant by which a term of the fragment can lengthen its arguments;
* `Complexity.SigShape` — the fragment of the Cobham algebra that the compiler covers.

Main results:

* `Complexity.length_eval_le_of_sigShape` — a term of the fragment lengthens its arguments by at
  most `addLen`;
* `Complexity.sigUniformB_of_sigShape` — **every term of the fragment is realized** by a P-uniform
  family of circuits, at every width that leaves room for its growth;
* `Complexity.sigUniformB_of_sigShape_std` — the same at the width `n + addLen v`, with no
  hypothesis at all.
-/

import Start.UniformSigBound
import Start.UniformSigApp

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### The growth of a term of the fragment -/

/-- The constant by which a term built from projections, the empty word, the successors and
composition can lengthen its arguments. -/
def addLen : Cob → ℕ
  | .proj _ => 0
  | .empty => 0
  | .app _ => 1
  | .smash => 0
  | .comp f gs => addLen f + (gs.attach.map (fun g => addLen g.1)).sum
  | .bRec _ _ _ _ => 0
decreasing_by
  · simp_wf
    omega
  · simp_wf
    have := List.sizeOf_lt_of_mem g.2
    omega

@[simp] theorem addLen_comp (f : Cob) (gs : List Cob) :
    addLen (.comp f gs) = addLen f + (gs.map addLen).sum := by
  rw [addLen]
  congr 2
  exact List.attach_map_val (l := gs) (f := addLen)

/-- A member of a list of terms grows by no more than the whole list does. -/
theorem addLen_le_sum {gs : List Cob} {g : Cob} (hg : g ∈ gs) :
    addLen g ≤ (gs.map addLen).sum :=
  List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hg)

/-- A bound on every argument bounds the longest one. -/
theorem maxLen_le {args : List Word} {B : ℕ} (h : ∀ u ∈ args, u.length ≤ B) :
    maxLen args ≤ B := by
  induction args with
  | nil => simp [maxLen]
  | cons u us ih =>
      rw [maxLen_cons]
      exact max_le (h u (by simp)) (ih fun u' hu' => h u' (by simp [hu']))

/-! ### The fragment the compiler covers -/

/-- **The fragment of the Cobham algebra that the compiler covers**, at arity `r`: projections of
an argument that exists, the empty word, the successors, and compositions of these. -/
inductive SigShape : ℕ → Cob → Prop
  /-- A projection, provided the argument it names exists. -/
  | proj {r i : ℕ} (hi : i < r) : SigShape r (.proj i)
  /-- The constant empty word. -/
  | empty {r : ℕ} : SigShape r .empty
  /-- A successor, provided there is an argument to prepend a bit to. -/
  | app {r : ℕ} {b : Bool} (hr : 0 < r) : SigShape r (.app b)
  /-- A composition of terms of the fragment. -/
  | comp {r : ℕ} {f : Cob} {gs : List Cob} (hf : SigShape gs.length f)
      (hgs : ∀ g ∈ gs, SigShape r g) : SigShape r (.comp f gs)

/-- **A term of the fragment lengthens its arguments by at most `addLen`.** -/
theorem length_eval_le_of_sigShape {r : ℕ} {v : Cob} (h : SigShape r v) :
    ∀ args : List Word, (v.eval args).length ≤ maxLen args + addLen v := by
  induction h with
  | @proj r i hi =>
      intro args
      simpa [addLen] using length_getD_le_maxLen args i
  | @empty r => intro args; simp [addLen]
  | @app r b hr =>
      intro args
      have := length_getD_le_maxLen args 0
      have hb : addLen (Cob.app b) = 1 := by simp [addLen]
      simp only [Cob.eval_app, List.length_cons, hb]
      omega
  | @comp r f gs hf hgs ihf ihgs =>
      intro args
      have hinner : ∀ g ∈ gs, (g.eval args).length ≤ maxLen args + (gs.map addLen).sum := by
        intro g hg
        exact le_trans (ihgs g hg args)
          (Nat.add_le_add_left (addLen_le_sum hg) _)
      have hmax : maxLen (gs.map fun g => g.eval args) ≤ maxLen args + (gs.map addLen).sum :=
        maxLen_map_le hinner
      have hfv := ihf (gs.map fun g => g.eval args)
      rw [Cob.eval_comp, addLen_comp]
      omega

/-! ### The compiler -/

/-- **Every term of the fragment is realized** by a P-uniform family of circuits, at every width
that leaves room for its growth. -/
theorem sigUniformB_of_sigShape {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    ∀ {r : ℕ} {v : Cob}, SigShape r v → ∀ k : ℕ → ℕ, (∀ n, k n + addLen v ≤ m n) →
      SigUniformB r m k v.eval := by
  intro r v h
  induction h with
  | @proj r i hi =>
      intro k hk
      have heq : (Cob.proj i).eval = fun args : List Word => args.getD i [] := by
        funext args; exact Cob.eval_proj i args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_proj hi hm)
        (fun n => by have := hk n; simp only [addLen] at this; omega)
  | @empty r =>
      intro k hk
      have heq : (Cob.empty).eval = fun _ : List Word => ([] : Word) := by
        funext args; exact Cob.eval_empty args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_empty hm)
        (fun n => by have := hk n; simp only [addLen] at this; omega)
  | @app r b hr =>
      intro k hk
      have heq : (Cob.app b).eval = fun args : List Word => b :: args.getD 0 [] := by
        funext args; exact Cob.eval_app b args
      rw [heq]
      have hb : addLen (Cob.app b) = 1 := by simp [addLen]
      exact sigUniformB_of_sigUniform (sigUniform_app hr hm) (fun n => by
        have := hk n
        rw [hb] at this
        omega)
  | @comp r f gs hf hgs ihf ihgs =>
      intro k hk
      set S : ℕ := (gs.map addLen).sum with hS
      set k' : ℕ → ℕ := fun n => k n + S with hk'
      have hkS : ∀ n, k n + S + addLen f ≤ m n := by
        intro n
        have := hk n
        rw [addLen_comp] at this
        omega
      -- the inner terms, realized at the promise `k`
      have hlist : ∀ hs : List Cob, (∀ g ∈ hs, g ∈ gs) →
          SigListUniformB r m k (hs.map Cob.eval) := by
        intro hs
        induction hs with
        | nil => intro _; simpa using (sigListUniformB_nil (r := r) (m := m) (k := k))
        | cons g hs ih =>
            intro hmem
            have hg : g ∈ gs := hmem g (by simp)
            have hgu : SigUniformB r m k g.eval :=
              ihgs g hg k (fun n => by
                have h1 := hk n
                have h2 : addLen g ≤ S := addLen_le_sum hg
                rw [addLen_comp] at h1
                omega)
            have hrest := ih (fun g' hg' => hmem g' (by simp [hg']))
            simpa using sigListUniformB_cons hgu hrest hm
      have hgsu : SigListUniformB r m k (gs.map Cob.eval) := hlist gs (fun _ hg => hg)
      have hfu : SigUniformB (gs.map Cob.eval).length m k' f.eval := by
        have := ihf k' (fun n => by simpa [hk'] using hkS n)
        simpa using this
      have hbnd : ∀ (n : ℕ) (args : List Word), args.length = r →
          (∀ u ∈ args, u.length ≤ k n) → ∀ F ∈ gs.map Cob.eval, (F args).length ≤ k' n := by
        intro n args _ hle F hF
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hF
        have h1 := length_eval_le_of_sigShape (hgs g hg) args
        have h2 : maxLen args ≤ k n := maxLen_le hle
        have h3 : addLen g ≤ S := addLen_le_sum hg
        simp only [hk']
        omega
      have hcomp := sigUniformB_comp hfu hgsu hbnd hm
      have heq : (Cob.comp f gs).eval
          = fun args : List Word => f.eval ((gs.map Cob.eval).map (fun F => F args)) := by
        funext args
        rw [Cob.eval_comp, List.map_map]
        rfl
      rw [heq]
      exact hcomp

/-- A Cobham term writing `1^{|x| + d}`. -/
theorem exists_lenAddT (d : ℕ) :
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (x.length + d) true := by
  refine ⟨Cob.pre (List.replicate d true) (.comp .smash [.proj 0, Cob.constT [true]]),
    fun x => ?_⟩
  simp only [Cob.eval_pre, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash,
    Cob.eval_proj, Cob.eval_constT, List.getD_cons_zero, List.getD_cons_succ, List.length_cons,
    List.length_nil, ← List.replicate_add]
  congr 1
  omega

/-- **Every term of the fragment is realized at the width `n + addLen v`**, on arguments of length
at most `n`. -/
theorem sigUniformB_of_sigShape_std {r : ℕ} {v : Cob} (h : SigShape r v) :
    SigUniformB r (fun n => n + addLen v) (fun n => n) v.eval := by
  obtain ⟨T, hT⟩ := exists_lenAddT (addLen v)
  exact sigUniformB_of_sigShape (m := fun n => n + addLen v) (mT := T) hT h _ (fun _ => le_rfl)

/-! ### An example -/

/-- Prepending two bits is a term of the fragment, hence realized. -/
example : SigUniformB 1 (fun n => n + 2) (fun n => n)
    (Cob.comp (.app true) [Cob.comp (.app false) [Cob.proj 0]]).eval := by
  have h : SigShape 1 (Cob.comp (.app true) [Cob.comp (.app false) [Cob.proj 0]]) := by
    refine SigShape.comp (by simpa using SigShape.app (b := true) Nat.one_pos) ?_
    intro g hg
    rw [List.mem_singleton.1 hg]
    exact SigShape.comp (by simpa using SigShape.app (b := false) Nat.one_pos)
      (fun g' hg' => by
        rw [List.mem_singleton.1 hg']
        exact SigShape.proj Nat.one_pos)
  have hlen : addLen (Cob.comp (.app true) [Cob.comp (.app false) [Cob.proj 0]]) = 2 := by
    simp [addLen_comp, addLen]
  simpa [hlen] using sigUniformB_of_sigShape_std h

end Complexity
