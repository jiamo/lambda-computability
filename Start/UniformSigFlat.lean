/-
# The compiler for the whole non-recursive fragment

`Start/UniformSigCompile.lean` compiles the terms built from the projections, the empty word, the
successors and composition, and `Start/UniformSigSmash.lean` realizes the smash.  This module puts
the two together: the fragment `Complexity.FlatShape` is the whole Cobham algebra except the
bounded recursion, and every term of it is realized by a P-uniform family of circuits.

Adding the smash changes the bookkeeping of the widths.  A term of the earlier fragment lengthens
its arguments by a constant (`Complexity.addLen`); a smash multiplies two lengths, so the growth is
polynomial and the width has to be a function of the promise rather than the promise plus a
constant.  `Complexity.flatLen` is that function: `flatLen v n` bounds the length of the value of
`v` at arguments of length at most `n`, it is monotone, it dominates `n`, and — this is what makes
it usable as a width — it is computed in unary by a Cobham term
(`Complexity.exists_flatLenT`), so the P-uniformity hypotheses of the rules are met.

Main definitions:

* `Complexity.flatLen` — the growth of a term of the fragment;
* `Complexity.FlatShape` — the fragment: everything but `Cob.bRec`.

Main results:

* `Complexity.length_eval_le_of_flatShape` — `flatLen` really bounds the growth;
* `Complexity.exists_flatLenT` — a Cobham term writes `1^{flatLen v n}` from a word of length `n`;
* `Complexity.sigUniformB_of_flatShape` — **every term of the fragment is realized** by a P-uniform
  family, at every width leaving room for its growth;
* `Complexity.sigUniformB_of_flatShape_std` — the same at the width `flatLen v`, with no hypothesis
  at all.
-/

import Start.UniformSigCompile
import Start.UniformSigSmash

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### The growth of a term of the fragment -/

/-- The length to which a term of the non-recursive fragment can grow arguments of length at most
`n`.  A smash multiplies lengths, so the bound is polynomial rather than additive; the summand `n`
in the composition case, and in the smash case, makes the bound dominate the identity, which is
what the rules for the leaves ask for. -/
def flatLen : Cob → ℕ → ℕ
  | .proj _ => fun n => n
  | .empty => fun n => n
  | .app _ => fun n => n + 1
  | .smash => fun n => n * n + n
  | .comp f gs => fun n =>
      flatLen f ((gs.attach.map (fun g => flatLen g.1 n)).sum + n)
        + ((gs.attach.map (fun g => flatLen g.1 n)).sum + n)
  | .bRec _ _ _ _ => fun n => n
decreasing_by
  · simp_wf
    omega
  all_goals
    have := List.sizeOf_lt_of_mem g.2
    simp_wf
    omega

@[simp] theorem flatLen_proj (i n : ℕ) : flatLen (.proj i) n = n := by simp [flatLen]

@[simp] theorem flatLen_empty (n : ℕ) : flatLen .empty n = n := by simp [flatLen]

@[simp] theorem flatLen_app (b : Bool) (n : ℕ) : flatLen (.app b) n = n + 1 := by simp [flatLen]

@[simp] theorem flatLen_smash (n : ℕ) : flatLen .smash n = n * n + n := by simp [flatLen]

@[simp] theorem flatLen_bRec (g h₀ h₁ bd : Cob) (n : ℕ) :
    flatLen (.bRec g h₀ h₁ bd) n = n := by simp [flatLen]

/-- The sum of the growths of the arguments of a composition, plus the promise itself. -/
def flatSum (gs : List Cob) (n : ℕ) : ℕ := (gs.map (fun g => flatLen g n)).sum + n

@[simp] theorem flatLen_comp (f : Cob) (gs : List Cob) (n : ℕ) :
    flatLen (.comp f gs) n = flatLen f (flatSum gs n) + flatSum gs n := by
  rw [flatLen]
  simp only [flatSum]
  rw [List.attach_map_val (l := gs) (f := fun g => flatLen g n)]

/-- A member of a list of terms grows by no more than the whole list does. -/
theorem flatLen_le_flatSum {gs : List Cob} {g : Cob} (hg : g ∈ gs) (n : ℕ) :
    flatLen g n ≤ flatSum gs n := by
  have : flatLen g n ≤ (gs.map (fun g => flatLen g n)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hg)
  simp only [flatSum]
  omega

theorem le_flatSum (gs : List Cob) (n : ℕ) : n ≤ flatSum gs n := by
  simp only [flatSum]
  omega

/-- The growth of a term dominates the promise. -/
theorem le_flatLen : ∀ (v : Cob) (n : ℕ), n ≤ flatLen v n := by
  intro v
  induction v using flatLen.induct with
  | case1 i => simp
  | case2 => simp
  | case3 b => simp
  | case4 => intro n; simp
  | case5 f gs ihf ihg =>
      intro n
      rw [flatLen_comp]
      have := le_flatSum gs n
      omega
  | case6 g h₀ h₁ bd => simp

/-- The growth of a term is monotone in the promise. -/
theorem flatLen_mono : ∀ (v : Cob) (n n' : ℕ), n ≤ n' → flatLen v n ≤ flatLen v n' := by
  intro v
  induction v using flatLen.induct with
  | case1 i => intro n n' h; simpa using h
  | case2 => intro n n' h; simpa using h
  | case3 b => intro n n' h; simp only [flatLen_app]; omega
  | case4 =>
      intro n n' h
      simp only [flatLen_smash]
      exact Nat.add_le_add (Nat.mul_le_mul h h) h
  | case5 f gs ihf ihg =>
      intro n n' h
      have hsum : (gs.map (fun g => flatLen g n)).sum ≤ (gs.map (fun g => flatLen g n')).sum :=
        List.sum_le_sum (fun g hg => ihg ⟨g, hg⟩ n n' h)
      have hS : flatSum gs n ≤ flatSum gs n' := by
        simp only [flatSum]
        omega
      simp only [flatLen_comp]
      exact Nat.add_le_add (ihf _ _ hS) hS
  | case6 g h₀ h₁ bd => intro n n' h; simpa using h

/-! ### The fragment -/

/-- **The non-recursive fragment of the Cobham algebra**, at arity `r`: projections of an argument
that exists, the empty word, the successors, the smash, and compositions of these. -/
inductive FlatShape : ℕ → Cob → Prop
  /-- A projection, provided the argument it names exists. -/
  | proj {r i : ℕ} (hi : i < r) : FlatShape r (.proj i)
  /-- The constant empty word. -/
  | empty {r : ℕ} : FlatShape r .empty
  /-- A successor, provided there is an argument to prepend a bit to. -/
  | app {r : ℕ} {b : Bool} (hr : 0 < r) : FlatShape r (.app b)
  /-- The smash, provided there are two arguments to smash. -/
  | smash {r : ℕ} (hr : 2 ≤ r) : FlatShape r .smash
  /-- A composition of terms of the fragment. -/
  | comp {r : ℕ} {f : Cob} {gs : List Cob} (hf : FlatShape gs.length f)
      (hgs : ∀ g ∈ gs, FlatShape r g) : FlatShape r (.comp f gs)

/-- **A term of the fragment grows by at most `flatLen`.** -/
theorem length_eval_le_of_flatShape {r : ℕ} {v : Cob} (h : FlatShape r v) :
    ∀ args : List Word, (v.eval args).length ≤ flatLen v (maxLen args) := by
  induction h with
  | @proj r i hi =>
      intro args
      simpa using length_getD_le_maxLen args i
  | @empty r => intro args; simp
  | @app r b hr =>
      intro args
      have := length_getD_le_maxLen args 0
      simp only [Cob.eval_app, List.length_cons, flatLen_app]
      omega
  | @smash r hr =>
      intro args
      have h0 := length_getD_le_maxLen args 0
      have h1 := length_getD_le_maxLen args 1
      simp only [Cob.eval_smash, List.length_replicate, flatLen_smash]
      have := Nat.mul_le_mul h0 h1
      omega
  | @comp r f gs hf hgs ihf ihgs =>
      intro args
      have hinner : ∀ g ∈ gs, (g.eval args).length ≤ flatSum gs (maxLen args) := by
        intro g hg
        exact le_trans (ihgs g hg args) (flatLen_le_flatSum hg _)
      have hmax : maxLen (gs.map fun g => g.eval args) ≤ flatSum gs (maxLen args) :=
        maxLen_map_le hinner
      have hfv := ihf (gs.map fun g => g.eval args)
      have hmono := flatLen_mono f _ _ hmax
      rw [Cob.eval_comp, flatLen_comp]
      omega

/-! ### The growth is computed in unary by a Cobham term -/

theorem exists_flatLenT_aux : ∀ (s : ℕ) (v : Cob), sizeOf v ≤ s →
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (flatLen v x.length) true := by
  intro s
  induction s with
  | zero =>
      intro v hv
      exfalso
      cases v <;> simp at hv
  | succ s ih =>
      intro v hv
      match v with
      | .proj i => exact ⟨Cob.unary (.proj 0), by intro x; simp⟩
      | .empty => exact ⟨Cob.unary (.proj 0), by intro x; simp⟩
      | .bRec g h₀ h₁ bd =>
          exact ⟨Cob.unary (.proj 0), by intro x; simp⟩
      | .app b =>
          refine ⟨Cob.pre [true] (Cob.unary (.proj 0)), fun x => ?_⟩
          simp [List.replicate_succ]
      | .smash =>
          refine ⟨Cob.catL [.comp .smash [Cob.unary (.proj 0), Cob.unary (.proj 0)],
            Cob.unary (.proj 0)], fun x => ?_⟩
          simp
      | .comp f gs =>
          have hsz : sizeOf f + sizeOf gs < s + 1 := by
            simp only [Cob.comp.sizeOf_spec] at hv
            omega
          have hmemsz : ∀ g ∈ gs, sizeOf g ≤ s := by
            intro g hg
            have := List.sizeOf_lt_of_mem hg
            omega
          have hlist : ∀ hs : List Cob, (∀ g ∈ hs, sizeOf g ≤ s) →
              ∃ T : Cob, ∀ x : Word,
                T.eval [x] = List.replicate ((hs.map (fun g => flatLen g x.length)).sum) true := by
            intro hs
            induction hs with
            | nil => exact fun _ => ⟨.empty, by intro x; simp⟩
            | cons g hs ihh =>
                intro hmem
                obtain ⟨Tg, hTg⟩ := ih g (hmem g (by simp))
                obtain ⟨Ts, hTs⟩ := ihh (fun g' hg' => hmem g' (by simp [hg']))
                refine ⟨Cob.catL [Tg, Ts], fun x => ?_⟩
                simp [hTg, hTs]
          obtain ⟨Tsum, hTsum⟩ := hlist gs hmemsz
          obtain ⟨Tf, hTf⟩ := ih f (by omega)
          refine ⟨Cob.catL [.comp Tf [Cob.catL [Tsum, Cob.unary (.proj 0)]],
            Cob.catL [Tsum, Cob.unary (.proj 0)]], fun x => ?_⟩
          have hS : (Cob.catL [Tsum, Cob.unary (.proj 0)]).eval [x]
              = List.replicate (flatSum gs x.length) true := by
            simp [hTsum, flatSum]
          simp only [Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_comp, hS,
            List.flatten_cons, List.flatten_nil, List.append_nil, List.length_replicate,
            hTf, flatLen_comp, ← List.replicate_add]

/-- **A Cobham term writes `1^{flatLen v n}`** from any word of length `n`. -/
theorem exists_flatLenT (v : Cob) :
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (flatLen v x.length) true :=
  exists_flatLenT_aux (sizeOf v) v le_rfl

/-! ### The compiler -/

/-- **Every term of the fragment is realized** by a P-uniform family of circuits, at every width
that leaves room for its growth. -/
theorem sigUniformB_of_flatShape {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    ∀ {r : ℕ} {v : Cob}, FlatShape r v → ∀ k : ℕ → ℕ, (∀ n, flatLen v (k n) ≤ m n) →
      SigUniformB r m k v.eval := by
  intro r v h
  induction h with
  | @proj r i hi =>
      intro k hk
      have heq : (Cob.proj i).eval = fun args : List Word => args.getD i [] := by
        funext args; exact Cob.eval_proj i args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_proj hi hm)
        (fun n => by simpa using hk n)
  | @empty r =>
      intro k hk
      have heq : (Cob.empty).eval = fun _ : List Word => ([] : Word) := by
        funext args; exact Cob.eval_empty args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_empty hm)
        (fun n => by simpa using hk n)
  | @app r b hr =>
      intro k hk
      have heq : (Cob.app b).eval = fun args : List Word => b :: args.getD 0 [] := by
        funext args; exact Cob.eval_app b args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_app hr hm) (fun n => by
        have := hk n
        rw [flatLen_app] at this
        omega)
  | @smash r hr =>
      intro k hk
      have heq : (Cob.smash).eval = fun args : List Word =>
          List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true := by
        funext args; exact Cob.eval_smash args
      rw [heq]
      refine sigUniformB_smash hr (fun n => ?_) hm
      have := hk n
      rw [flatLen_smash] at this
      omega
  | @comp r f gs hf hgs ihf ihgs =>
      intro k hk
      set k' : ℕ → ℕ := fun n => flatSum gs (k n) with hk'
      have hkf : ∀ n, flatLen f (k' n) ≤ m n := by
        intro n
        have := hk n
        rw [flatLen_comp] at this
        simp only [hk']
        omega
      have hkg : ∀ g ∈ gs, ∀ n, flatLen g (k n) ≤ m n := by
        intro g hg n
        have h1 := hk n
        have h2 := flatLen_le_flatSum hg (k n)
        rw [flatLen_comp] at h1
        omega
      have hlist : ∀ hs : List Cob, (∀ g ∈ hs, g ∈ gs) →
          SigListUniformB r m k (hs.map Cob.eval) := by
        intro hs
        induction hs with
        | nil => intro _; simpa using (sigListUniformB_nil (r := r) (m := m) (k := k))
        | cons g hs ih =>
            intro hmem
            have hg : g ∈ gs := hmem g (by simp)
            have hgu : SigUniformB r m k g.eval := ihgs g hg k (hkg g hg)
            have hrest := ih (fun g' hg' => hmem g' (by simp [hg']))
            simpa using sigListUniformB_cons hgu hrest hm
      have hgsu : SigListUniformB r m k (gs.map Cob.eval) := hlist gs (fun _ hg => hg)
      have hfu : SigUniformB (gs.map Cob.eval).length m k' f.eval := by
        have := ihf k' hkf
        simpa using this
      have hbnd : ∀ (n : ℕ) (args : List Word), args.length = r →
          (∀ u ∈ args, u.length ≤ k n) → ∀ F ∈ gs.map Cob.eval, (F args).length ≤ k' n := by
        intro n args _ hle F hF
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hF
        have h1 := length_eval_le_of_flatShape (hgs g hg) args
        have h2 : maxLen args ≤ k n := maxLen_le hle
        have h3 := flatLen_mono g _ _ h2
        have h4 := flatLen_le_flatSum hg (k n)
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

/-- **Every term of the fragment is realized at the width `flatLen v`**, on arguments of length at
most `n`. -/
theorem sigUniformB_of_flatShape_std {r : ℕ} {v : Cob} (h : FlatShape r v) :
    SigUniformB r (flatLen v) (fun n => n) v.eval := by
  obtain ⟨T, hT⟩ := exists_flatLenT v
  exact sigUniformB_of_flatShape hT h _ (fun _ => le_rfl)

/-! ### An example -/

/-- Squaring the length of the argument — a term the earlier fragment does not cover, since it is
not a constant lengthening — is realized. -/
example : SigUniformB 1 (flatLen (Cob.comp .smash [Cob.proj 0, Cob.proj 0])) (fun n => n)
    (Cob.comp .smash [Cob.proj 0, Cob.proj 0]).eval := by
  refine sigUniformB_of_flatShape_std (FlatShape.comp ?_ ?_)
  · exact FlatShape.smash (by simp)
  · intro g hg
    rcases List.mem_cons.1 hg with rfl | hg'
    · exact FlatShape.proj Nat.one_pos
    · rw [List.mem_singleton.1 hg']
      exact FlatShape.proj Nat.one_pos

end Complexity
