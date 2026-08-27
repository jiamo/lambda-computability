/-
# The compiler for the whole Cobham algebra

`Start/UniformSigFlat.lean` compiles every term of the Cobham algebra except the bounded
recursion, and `Start/UniformSigRec.lean` supplies the rule for a bounded recursion.  This module
puts the two together: **every** well-formed term of the Cobham algebra is realized by a P-uniform
family of circuits.

The bookkeeping is the same as in the non-recursive fragment, with one addition.  The loop
compiling a bounded recursion runs its subterms at a *larger* promise than the term itself — the
value of the recursion, and the bound, have to fit — so the growth function has to leave room for
that: `Complexity.cobLen (Cob.bRec g h₀ h₁ bd) n` evaluates the growth of the four subterms at the
promise `Complexity.brecProm g bd n` the loop hands them.  The rule for a bounded recursion also
needs the promise itself to be written in unary by a Cobham term, so the induction carries that
hypothesis along (`Complexity.UnaryLen`).

Main definitions:

* `Complexity.cobLen` — the growth of an arbitrary Cobham term;
* `Complexity.CobShape` — the arity discipline: which terms are well formed at arity `r`;
* `Complexity.UnaryLen` — a length function written in unary by a Cobham term.

Main results:

* `Complexity.length_eval_le_of_cobShape` — `cobLen` really bounds the growth;
* `Complexity.exists_cobLenT` — a Cobham term writes `1^{cobLen v n}` from a word of length `n`;
* `Complexity.sigUniformB_of_cobShape` — **every well-formed Cobham term is realized** by a
  P-uniform family, at every width leaving room for its growth;
* `Complexity.sigUniformB_of_cobShape_std` — the same at the width `cobLen v`, with no hypothesis
  at all.
-/

import Start.UniformSigFlat
import Start.UniformSigRec

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

open Complexity.Tseitin

/-! ### The growth of an arbitrary term -/

/-- The length to which a Cobham term can grow arguments of length at most `n`.  In the case of a
bounded recursion the four subterms are evaluated at the promise the compiling loop hands them,
which is larger than `n`: it has to accommodate the value of the recursion and the bound. -/
def cobLen : Cob → ℕ → ℕ
  | .proj _ => fun n => n
  | .empty => fun n => n
  | .app _ => fun n => n + 1
  | .smash => fun n => n * n + n
  | .comp f gs => fun n =>
      cobLen f ((gs.attach.map (fun g => cobLen g.1 n)).sum + n)
        + ((gs.attach.map (fun g => cobLen g.1 n)).sum + n)
  | .bRec g h₀ h₁ bd => fun n =>
      cobLen g (cobLen g n + cobLen bd n + 1) + cobLen h₀ (cobLen g n + cobLen bd n + 1)
        + cobLen h₁ (cobLen g n + cobLen bd n + 1) + cobLen bd (cobLen g n + cobLen bd n + 1)
        + (cobLen g n + cobLen bd n + 1)
decreasing_by
  all_goals (simp_wf; try omega)
  all_goals
    (have := List.sizeOf_lt_of_mem g.2
     omega)

@[simp] theorem cobLen_proj (i n : ℕ) : cobLen (.proj i) n = n := by simp [cobLen]

@[simp] theorem cobLen_empty (n : ℕ) : cobLen .empty n = n := by simp [cobLen]

@[simp] theorem cobLen_app (b : Bool) (n : ℕ) : cobLen (.app b) n = n + 1 := by simp [cobLen]

@[simp] theorem cobLen_smash (n : ℕ) : cobLen .smash n = n * n + n := by simp [cobLen]

/-- The sum of the growths of the arguments of a composition, plus the promise itself. -/
def cobSum (gs : List Cob) (n : ℕ) : ℕ := (gs.map (fun g => cobLen g n)).sum + n

@[simp] theorem cobLen_comp (f : Cob) (gs : List Cob) (n : ℕ) :
    cobLen (.comp f gs) n = cobLen f (cobSum gs n) + cobSum gs n := by
  rw [cobLen]
  simp only [cobSum]
  rw [List.attach_map_val (l := gs) (f := fun g => cobLen g n)]

/-- The promise the compiling loop of a bounded recursion hands to its subterms: the value of the
recursion, and the bound, have to fit, and one further bit is needed for the bit consumed in a
round. -/
def brecProm (g bd : Cob) (n : ℕ) : ℕ := cobLen g n + cobLen bd n + 1

theorem cobLen_bRec (g h₀ h₁ bd : Cob) (n : ℕ) :
    cobLen (.bRec g h₀ h₁ bd) n =
      cobLen g (brecProm g bd n) + cobLen h₀ (brecProm g bd n) + cobLen h₁ (brecProm g bd n)
        + cobLen bd (brecProm g bd n) + brecProm g bd n := by
  rw [cobLen]
  rfl

/-- A member of a list of terms grows by no more than the whole list does. -/
theorem cobLen_le_cobSum {gs : List Cob} {g : Cob} (hg : g ∈ gs) (n : ℕ) :
    cobLen g n ≤ cobSum gs n := by
  have : cobLen g n ≤ (gs.map (fun g => cobLen g n)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hg)
  simp only [cobSum]
  omega

theorem le_cobSum (gs : List Cob) (n : ℕ) : n ≤ cobSum gs n := by
  simp only [cobSum]
  omega

/-- The growth of a term dominates the promise. -/
theorem le_cobLen : ∀ (v : Cob) (n : ℕ), n ≤ cobLen v n := by
  intro v
  induction v using cobLen.induct with
  | case1 i => intro n; simp
  | case2 => intro n; simp
  | case3 b => intro n; simp
  | case4 => intro n; simp
  | case5 f gs ihf _ =>
      intro n
      rw [cobLen_comp]
      have h1 := le_cobSum gs n
      have h2 := ihf (cobSum gs n)
      omega
  | case6 g h₀ h₁ bd ihg _ _ _ =>
      intro n
      rw [cobLen_bRec]
      have := ihg n
      simp only [brecProm]
      omega

theorem cobLen_mono : ∀ (v : Cob) (n n' : ℕ), n ≤ n' → cobLen v n ≤ cobLen v n' := by
  intro v
  induction v using cobLen.induct with
  | case1 i => intro n n' h; simpa using h
  | case2 => intro n n' h; simpa using h
  | case3 b => intro n n' h; simp only [cobLen_app]; omega
  | case4 =>
      intro n n' h
      simp only [cobLen_smash]
      exact Nat.add_le_add (Nat.mul_le_mul h h) h
  | case5 f gs ihf ihgs =>
      intro n n' h
      have hsum : (gs.map (fun g => cobLen g n)).sum ≤ (gs.map (fun g => cobLen g n')).sum :=
        List.sum_le_sum (fun g hg => ihgs ⟨g, hg⟩ n n' h)
      have hS : cobSum gs n ≤ cobSum gs n' := by
        simp only [cobSum]
        omega
      simp only [cobLen_comp]
      exact Nat.add_le_add (ihf _ _ hS) hS
  | case6 g h₀ h₁ bd ihg ihbd ih0 ih1 =>
      intro n n' h
      have hprom : brecProm g bd n ≤ brecProm g bd n' := by
        simp only [brecProm]
        have := ihg n n' h
        have := ihbd n n' h
        omega
      simp only [cobLen_bRec]
      have a1 := ihg _ _ hprom
      have a2 := ih0 _ _ hprom
      have a3 := ih1 _ _ hprom
      have a4 := ihbd _ _ hprom
      omega

/-! ### The arity discipline -/

/-- **The well-formed terms of the Cobham algebra at arity `r`**: projections of an argument that
exists, the empty word, the successors, the smash, compositions, and bounded recursions whose
subterms have the arities the recursion feeds them. -/
inductive CobShape : ℕ → Cob → Prop
  /-- A projection, provided the argument it names exists. -/
  | proj {r i : ℕ} (hi : i < r) : CobShape r (.proj i)
  /-- The constant empty word. -/
  | empty {r : ℕ} : CobShape r .empty
  /-- A successor, provided there is an argument to prepend a bit to. -/
  | app {r : ℕ} {b : Bool} (hr : 0 < r) : CobShape r (.app b)
  /-- The smash, provided there are two arguments to smash. -/
  | smash {r : ℕ} (hr : 2 ≤ r) : CobShape r .smash
  /-- A composition of well-formed terms. -/
  | comp {r : ℕ} {f : Cob} {gs : List Cob} (hf : CobShape gs.length f)
      (hgs : ∀ g ∈ gs, CobShape r g) : CobShape r (.comp f gs)
  /-- A bounded recursion: the base takes the parameters, the two steps take the tail of the
  recursion argument, the recursive value and the parameters, and the bound takes the recursion
  argument and the parameters. -/
  | bRec {p : ℕ} {g h₀ h₁ bd : Cob} (hg : CobShape p g) (hh₀ : CobShape (p + 2) h₀)
      (hh₁ : CobShape (p + 2) h₁) (hbd : CobShape (p + 1) bd) :
      CobShape (p + 1) (.bRec g h₀ h₁ bd)

/-- **A well-formed term grows by at most `cobLen`.** -/
theorem length_eval_le_of_cobShape {r : ℕ} {v : Cob} (h : CobShape r v) :
    ∀ args : List Word, (v.eval args).length ≤ cobLen v (maxLen args) := by
  induction h with
  | @proj r i hi =>
      intro args
      simpa using length_getD_le_maxLen args i
  | @empty r => intro args; simp
  | @app r b hr =>
      intro args
      have := length_getD_le_maxLen args 0
      simp only [Cob.eval_app, List.length_cons, cobLen_app]
      omega
  | @smash r hr =>
      intro args
      have h0 := length_getD_le_maxLen args 0
      have h1 := length_getD_le_maxLen args 1
      simp only [Cob.eval_smash, List.length_replicate, cobLen_smash]
      have := Nat.mul_le_mul h0 h1
      omega
  | @comp r f gs hf hgs ihf ihgs =>
      intro args
      have hinner : ∀ g ∈ gs, (g.eval args).length ≤ cobSum gs (maxLen args) := by
        intro g hg
        exact le_trans (ihgs g hg args) (cobLen_le_cobSum hg _)
      have hmax : maxLen (gs.map fun g => g.eval args) ≤ cobSum gs (maxLen args) :=
        maxLen_map_le hinner
      have hfv := ihf (gs.map fun g => g.eval args)
      have hmono := cobLen_mono f _ _ hmax
      rw [Cob.eval_comp, cobLen_comp]
      omega
  | @bRec p g h₀ h₁ bd hg hh₀ hh₁ hbd ihg _ _ ihbd =>
      intro args
      have hprom : maxLen args ≤ brecProm g bd (maxLen args) := by
        have := le_cobLen g (maxLen args)
        simp only [brecProm]
        omega
      have hgb : (g.eval args.tail).length ≤ cobLen g (brecProm g bd (maxLen args)) := by
        refine le_trans (ihg args.tail) ?_
        exact cobLen_mono g _ _ (le_trans (maxLen_tail_le args) hprom)
      have hbdb : (bd.eval args).length ≤ cobLen bd (brecProm g bd (maxLen args)) :=
        le_trans (ihbd args) (cobLen_mono bd _ _ hprom)
      rw [cobLen_bRec]
      match args with
      | [] =>
          have hev : (Cob.bRec g h₀ h₁ bd).eval [] = g.eval [] := by
            rw [Cob.eval_bRec]; rfl
          rw [hev]
          have := ihg []
          have hm := cobLen_mono g 0 (brecProm g bd (maxLen ([] : List Word))) (by omega)
          simp only [maxLen_nil] at *
          omega
      | [] :: rest =>
          rw [Cob.eval_bRec_nil]
          have : (g.eval ([] :: rest).tail).length = (g.eval rest).length := by simp
          omega
      | (b :: x) :: rest =>
          rw [Cob.eval_bRec_cons]
          refine le_trans (List.length_take_le _ _) ?_
          omega

/-! ### The growth is computed in unary by a Cobham term -/

/-- A length function written in unary by a Cobham term. -/
def UnaryLen (k : ℕ → ℕ) : Prop :=
  ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (k x.length) true

theorem exists_cobLenT_aux : ∀ (s : ℕ) (v : Cob), sizeOf v ≤ s →
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (cobLen v x.length) true := by
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
                T.eval [x] = List.replicate ((hs.map (fun g => cobLen g x.length)).sum) true := by
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
              = List.replicate (cobSum gs x.length) true := by
            simp [hTsum, cobSum]
          simp only [Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_comp, hS,
            List.flatten_cons, List.flatten_nil, List.append_nil, List.length_replicate,
            hTf, cobLen_comp, ← List.replicate_add]
      | .bRec g h₀ h₁ bd =>
          have hszg : sizeOf g ≤ s := by simp only [Cob.bRec.sizeOf_spec] at hv; omega
          have hsz0 : sizeOf h₀ ≤ s := by simp only [Cob.bRec.sizeOf_spec] at hv; omega
          have hsz1 : sizeOf h₁ ≤ s := by simp only [Cob.bRec.sizeOf_spec] at hv; omega
          have hszb : sizeOf bd ≤ s := by simp only [Cob.bRec.sizeOf_spec] at hv; omega
          obtain ⟨Tg, hTg⟩ := ih g hszg
          obtain ⟨T0, hT0⟩ := ih h₀ hsz0
          obtain ⟨T1, hT1⟩ := ih h₁ hsz1
          obtain ⟨Tb, hTb⟩ := ih bd hszb
          set Tp : Cob := Cob.catL [Tg, Tb, Cob.constT [true]] with hTp
          have hprom : ∀ x : Word,
              Tp.eval [x] = List.replicate (brecProm g bd x.length) true := by
            intro x
            simp only [hTp, Cob.eval_catL, List.map_cons, List.map_nil, hTg, hTb,
              Cob.eval_constT, List.flatten_cons, List.flatten_nil, List.append_nil,
              brecProm, List.replicate_add, List.replicate_one, List.append_assoc]
          refine ⟨Cob.catL [.comp Tg [Tp], .comp T0 [Tp], .comp T1 [Tp], .comp Tb [Tp], Tp],
            fun x => ?_⟩
          simp only [Cob.eval_catL, List.map_cons, List.map_nil, Cob.eval_comp, hprom,
            List.flatten_cons, List.flatten_nil, List.append_nil, hTg, hT0, hT1, hTb,
            List.length_replicate, cobLen_bRec, ← List.replicate_add]
          congr 1
          omega

/-- **A Cobham term writes `1^{cobLen v n}`** from any word of length `n`. -/
theorem exists_cobLenT (v : Cob) :
    ∃ T : Cob, ∀ x : Word, T.eval [x] = List.replicate (cobLen v x.length) true :=
  exists_cobLenT_aux (sizeOf v) v le_rfl

/-- Substituting a unary-computable promise into the growth of a term stays unary-computable. -/
theorem unaryLen_cobLen {k : ℕ → ℕ} (hk : UnaryLen k) (v : Cob) :
    UnaryLen (fun n => cobLen v (k n)) := by
  obtain ⟨kT, hkT⟩ := hk
  obtain ⟨T, hT⟩ := exists_cobLenT v
  refine ⟨.comp T [kT], fun x => ?_⟩
  simp [hkT, hT]

/-- Unary-computable length functions are closed under addition. -/
theorem UnaryLen.add {k k' : ℕ → ℕ} (hk : UnaryLen k) (hk' : UnaryLen k') :
    UnaryLen (fun n => k n + k' n) := by
  obtain ⟨T, hT⟩ := hk
  obtain ⟨T', hT'⟩ := hk'
  refine ⟨Cob.catL [T, T'], fun x => ?_⟩
  simp [hT, hT']

/-- Unary-computable length functions are closed under adding a constant. -/
theorem UnaryLen.succ {k : ℕ → ℕ} (hk : UnaryLen k) : UnaryLen (fun n => k n + 1) := by
  obtain ⟨T, hT⟩ := hk
  refine ⟨Cob.catL [T, Cob.constT [true]], fun x => ?_⟩
  simp only [Cob.eval_catL, List.map_cons, List.map_nil, hT, Cob.eval_constT,
    List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [show ([true] : Word) = List.replicate 1 true from rfl, ← List.replicate_add]

/-- The identity is unary-computable. -/
theorem unaryLen_id : UnaryLen (fun n => n) := ⟨Cob.unary (.proj 0), by intro x; simp⟩

/-- The promise handed to the arguments of a composition is unary-computable. -/
theorem unaryLen_cobSum {k : ℕ → ℕ} (hk : UnaryLen k) (gs : List Cob) :
    UnaryLen (fun n => cobSum gs (k n)) := by
  have hs : ∀ hs : List Cob, UnaryLen (fun n => (hs.map (fun g => cobLen g (k n))).sum) := by
    intro hs
    induction hs with
    | nil => exact ⟨.empty, by intro x; simp⟩
    | cons g hs ih => simpa using (unaryLen_cobLen hk g).add ih
  have := (hs gs).add hk
  simpa [cobSum] using this

/-! ### The compiler -/

/-- **Every well-formed Cobham term is realized** by a P-uniform family of circuits, at every width
that leaves room for its growth. -/
theorem sigUniformB_of_cobShape {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    ∀ {r : ℕ} {v : Cob}, CobShape r v → ∀ k : ℕ → ℕ, UnaryLen k →
      (∀ n, cobLen v (k n) ≤ m n) → SigUniformB r m k v.eval := by
  intro r v h
  induction h with
  | @proj r i hi =>
      intro k _ hk
      have heq : (Cob.proj i).eval = fun args : List Word => args.getD i [] := by
        funext args; exact Cob.eval_proj i args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_proj hi hm)
        (fun n => by simpa using hk n)
  | @empty r =>
      intro k _ hk
      have heq : (Cob.empty).eval = fun _ : List Word => ([] : Word) := by
        funext args; exact Cob.eval_empty args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_empty hm)
        (fun n => by simpa using hk n)
  | @app r b hr =>
      intro k _ hk
      have heq : (Cob.app b).eval = fun args : List Word => b :: args.getD 0 [] := by
        funext args; exact Cob.eval_app b args
      rw [heq]
      exact sigUniformB_of_sigUniform (sigUniform_app hr hm) (fun n => by
        have := hk n
        rw [cobLen_app] at this
        omega)
  | @smash r hr =>
      intro k _ hk
      have heq : (Cob.smash).eval = fun args : List Word =>
          List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true := by
        funext args; exact Cob.eval_smash args
      rw [heq]
      refine sigUniformB_smash hr (fun n => ?_) hm
      have := hk n
      rw [cobLen_smash] at this
      omega
  | @comp r f gs hf hgs ihf ihgs =>
      intro k hkU hk
      set k' : ℕ → ℕ := fun n => cobSum gs (k n) with hk'
      have hk'U : UnaryLen k' := unaryLen_cobSum hkU gs
      have hkf : ∀ n, cobLen f (k' n) ≤ m n := by
        intro n
        have := hk n
        rw [cobLen_comp] at this
        simp only [hk']
        omega
      have hkg : ∀ g ∈ gs, ∀ n, cobLen g (k n) ≤ m n := by
        intro g hg n
        have h1 := hk n
        have h2 := cobLen_le_cobSum hg (k n)
        rw [cobLen_comp] at h1
        omega
      have hlist : ∀ hs : List Cob, (∀ g ∈ hs, g ∈ gs) →
          SigListUniformB r m k (hs.map Cob.eval) := by
        intro hs
        induction hs with
        | nil => intro _; simpa using (sigListUniformB_nil (r := r) (m := m) (k := k))
        | cons g hs ih =>
            intro hmem
            have hg : g ∈ gs := hmem g (by simp)
            have hgu : SigUniformB r m k g.eval := ihgs g hg k hkU (hkg g hg)
            have hrest := ih (fun g' hg' => hmem g' (by simp [hg']))
            simpa using sigListUniformB_cons hgu hrest hm
      have hgsu : SigListUniformB r m k (gs.map Cob.eval) := hlist gs (fun _ hg => hg)
      have hfu : SigUniformB (gs.map Cob.eval).length m k' f.eval := by
        have := ihf k' hk'U hkf
        simpa using this
      have hbnd : ∀ (n : ℕ) (args : List Word), args.length = r →
          (∀ u ∈ args, u.length ≤ k n) → ∀ F ∈ gs.map Cob.eval, (F args).length ≤ k' n := by
        intro n args _ hle F hF
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hF
        have h1 := length_eval_le_of_cobShape (hgs g hg) args
        have h2 : maxLen args ≤ k n := maxLen_le hle
        have h3 := cobLen_mono g _ _ h2
        have h4 := cobLen_le_cobSum hg (k n)
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
  | @bRec p g h₀ h₁ bd hg hh₀ hh₁ hbd ihg ih0 ih1 ihbd =>
      intro k hkU hk
      obtain ⟨kT, hkT⟩ := hkU
      have hkU : UnaryLen k := ⟨kT, hkT⟩
      set kS : ℕ → ℕ := fun n => cobLen g (k n) + cobLen bd (k n) with hkS'
      set kP : ℕ → ℕ := fun n => kS n + 1 with hkP'
      set kI : ℕ → ℕ := fun n =>
        cobLen h₀ (kP n) + cobLen h₁ (kP n) + cobLen bd (kP n) with hkI'
      have hkPprom : ∀ n, kP n = brecProm g bd (k n) := by
        intro n
        simp only [hkP', hkS', brecProm]
      have hkbnd : ∀ n, cobLen g (kP n) + cobLen h₀ (kP n) + cobLen h₁ (kP n)
          + cobLen bd (kP n) + kP n ≤ m n := by
        intro n
        have := hk n
        rw [cobLen_bRec, ← hkPprom n] at this
        exact this
      have hkPU : UnaryLen kP := ((unaryLen_cobLen hkU g).add (unaryLen_cobLen hkU bd)).succ
      have hkS : ∀ n, k n ≤ kS n := by
        intro n
        have := le_cobLen g (k n)
        simp only [hkS']
        omega
      have hkP : ∀ n, kS n + 1 ≤ kP n := fun _ => le_rfl
      have hPI : ∀ n, kP n ≤ kI n := by
        intro n
        have := le_cobLen bd (kP n)
        simp only [hkI']
        omega
      have hIm : ∀ n, kI n ≤ m n := by
        intro n
        have := hkbnd n
        simp only [hkI']
        omega
      have hm0 : ∀ n, 0 < m n := by
        intro n
        have h1 := hkbnd n
        have h2 : 1 ≤ kP n := by simp only [hkP']; omega
        omega
      have hG : SigUniformB p m kP g.eval := by
        refine ihg kP hkPU (fun n => ?_)
        have := hkbnd n
        omega
      have hH0 : SigUniformB (p + 2) m kP h₀.eval := by
        refine ih0 kP hkPU (fun n => ?_)
        have := hkbnd n
        omega
      have hH1 : SigUniformB (p + 2) m kP h₁.eval := by
        refine ih1 kP hkPU (fun n => ?_)
        have := hkbnd n
        omega
      have hBD : SigUniformB (p + 1) m kP bd.eval := by
        refine ihbd kP hkPU (fun n => ?_)
        have := hkbnd n
        omega
      have hGb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ k n) →
          (g.eval args).length ≤ kS n := by
        intro n args hle
        have h1 := length_eval_le_of_cobShape hg args
        have h2 := cobLen_mono g _ _ (maxLen_le hle)
        simp only [hkS']
        omega
      have hBDb : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ k n) →
          (bd.eval args).length ≤ kS n := by
        intro n args hle
        have h1 := length_eval_le_of_cobShape hbd args
        have h2 := cobLen_mono bd _ _ (maxLen_le hle)
        simp only [hkS']
        omega
      have hH0b : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
          (h₀.eval args).length ≤ kI n := by
        intro n args hle
        have h1 := length_eval_le_of_cobShape hh₀ args
        have h2 := cobLen_mono h₀ _ _ (maxLen_le hle)
        simp only [hkI']
        omega
      have hH1b : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
          (h₁.eval args).length ≤ kI n := by
        intro n args hle
        have h1 := length_eval_le_of_cobShape hh₁ args
        have h2 := cobLen_mono h₁ _ _ (maxLen_le hle)
        simp only [hkI']
        omega
      have hBDb' : ∀ (n : ℕ) (args : List Word), (∀ u ∈ args, u.length ≤ kP n) →
          (bd.eval args).length ≤ kI n := by
        intro n args hle
        have h1 := length_eval_le_of_cobShape hbd args
        have h2 := cobLen_mono bd _ _ (maxLen_le hle)
        simp only [hkI']
        omega
      exact sigUniformB_bRec hkS hkP hPI hIm hm0 hG hH0 hH1 hBD hGb hH0b hH1b hBDb hBDb' hm hkT

/-- **Every well-formed Cobham term is realized at the width `cobLen v`**, on arguments of length
at most `n`. -/
theorem sigUniformB_of_cobShape_std {r : ℕ} {v : Cob} (h : CobShape r v) :
    SigUniformB r (cobLen v) (fun n => n) v.eval := by
  obtain ⟨T, hT⟩ := exists_cobLenT v
  exact sigUniformB_of_cobShape hT h _ ⟨Cob.unary (.proj 0), by intro x; simp⟩ (fun _ => le_rfl)

end Complexity
