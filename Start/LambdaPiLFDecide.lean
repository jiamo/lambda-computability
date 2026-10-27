/-
**Termination of the type-directed algorithm, and decidability of the declarative equality of
`λΠ`** — task `M23-LF-EQUIV-COMPLETE`.

The algorithm `EqvE` (`Start/LambdaPiLFAlgE.lean`) is a relation.  Here it is run as a program,
with fuel, and shown to answer on typable terms.

* `LambdaPi.whStep?`, `LambdaPi.whnfF` — one weak head step, and weak head normalization with
  fuel (`whStep?_spec`, `whnfF_sound`, `whnfF_complete`);
* `LambdaPi.baseStep`, `LambdaPi.pathStep`, `LambdaPi.algRun` — the algorithm with fuel `n`:
  `(algRun n).alg Δ M N τ` and `(algRun n).path Δ p q` return `none` when the fuel runs out;
* `algRun_sound` — **an answer is correct**: `some b` means `b = true ↔ AlgEqE Δ M N τ`, and for
  paths `some r` means `PathEqE Δ p q τ ↔ r = some τ`;
* `algRun_terminates` — **termination**: if `M` and `N` each have a derivation of the algorithm
  (with any partner) at `τ`, the run on `M` and `N` answers for all large fuels.  Typable terms
  have such derivations (`TypingE.algEq_refl`), as in Harper and Pfenning;
* **`TEqE.decide_spec`** — for terms typable at `A` in a well-formed context, the run answers
  for all large fuels, and the answer is `true` exactly when `Γ ⊢ M ≡ N : A`;
* **`TEqE.decidable`** — the declarative equality of typable terms is decidable, by the search
  for the least fuel at which the run answers (`decideTEqE`).
-/

import Start.LambdaPiLFSound

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Weak head normalization with fuel -/

/-- One weak head step, if there is one. -/
def whStep? : Tm → Option Tm
  | Tm.var _ => none
  | Tm.sort _ => none
  | Tm.lam _ _ => none
  | Tm.pi _ _ => none
  | Tm.app (Tm.lam _ b) a => some (b[a])
  | Tm.app (Tm.var _) _ => none
  | Tm.app (Tm.sort _) _ => none
  | Tm.app (Tm.pi _ _) _ => none
  | Tm.app (Tm.app f₁ f₂) a => (whStep? (Tm.app f₁ f₂)).map (fun f' => Tm.app f' a)

theorem whStep?_spec {t u : Tm} : whStep? t = some u ↔ WhStep t u := by
  constructor
  · intro h
    induction t generalizing u with
    | var n => simp [whStep?] at h
    | sort s => simp [whStep?] at h
    | lam A b _ _ => simp [whStep?] at h
    | pi A B _ _ => simp [whStep?] at h
    | app f a ihf _ =>
        cases f with
        | lam A b =>
            simp only [whStep?, Option.some.injEq] at h
            subst h
            exact WhStep.beta _ _ _
        | var n => simp [whStep?] at h
        | sort s => simp [whStep?] at h
        | pi A B => simp [whStep?] at h
        | app f₁ f₂ =>
            simp only [whStep?] at h
            obtain ⟨f', hf', rfl⟩ := Option.map_eq_some_iff.mp h
            exact WhStep.appL a (ihf hf')
  · intro h
    induction h with
    | beta A b a => rfl
    | @appL f f' a hs ih =>
        cases f with
        | lam A b => exact absurd hs WhStep.not_lam
        | var n => cases hs
        | sort s => cases hs
        | pi A B => cases hs
        | app f₁ f₂ =>
            simp only [whStep?, ih, Option.map_some]

theorem whStep?_none {t : Tm} : whStep? t = none ↔ WhNF t := by
  constructor
  · intro h u hu
    rw [whStep?_spec.mpr hu] at h
    cases h
  · intro h
    cases e : whStep? t with
    | none => rfl
    | some u => exact absurd (whStep?_spec.mp e) (h u)

/-- Weak head normalization with fuel. -/
def whnfF : ℕ → Tm → Option Tm
  | 0, _ => none
  | n + 1, t =>
      match whStep? t with
      | none => some t
      | some t' => whnfF n t'

theorem whnfF_sound : ∀ {n : ℕ} {t u : Tm}, whnfF n t = some u → WhRed t u ∧ WhNF u
  | 0, _, _, h => by simp [whnfF] at h
  | n + 1, t, u, h => by
      simp only [whnfF] at h
      split at h
      · next hn =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨.refl, whStep?_none.mp hn⟩
      · next t' hs =>
          obtain ⟨hr, hnf⟩ := whnfF_sound h
          exact ⟨Relation.ReflTransGen.head (whStep?_spec.mp hs) hr, hnf⟩

theorem whnfF_complete {t u : Tm} (hr : WhRed t u) (hn : WhNF u) :
    ∃ n₀, ∀ n, n₀ ≤ n → whnfF n t = some u := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl =>
      refine ⟨1, fun n hn' => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp [whnfF, whStep?_none.mpr hn]
  | head hs _ ih =>
      obtain ⟨n₁, hn₁⟩ := ih
      refine ⟨n₁ + 1, fun n hn' => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      simp only [whnfF, whStep?_spec.mpr hs]
      exact hn₁ m (by omega)

/-! ### The algorithm with fuel -/

/-- Is the term a path? -/
def isPathB : Tm → Bool
  | Tm.var _ => true
  | Tm.app p _ => isPathB p
  | _ => false

theorem isPathB_iff {t : Tm} : isPathB t = true ↔ IsPath t := by
  induction t with
  | var n => exact ⟨fun _ => IsPath.var n, fun _ => rfl⟩
  | sort s => simp only [isPathB, Bool.false_eq_true, false_iff]; intro h; cases h
  | lam A b _ _ => simp only [isPathB, Bool.false_eq_true, false_iff]; intro h; cases h
  | pi A B _ _ => simp only [isPathB, Bool.false_eq_true, false_iff]; intro h; cases h
  | app f a ihf _ =>
      simp only [isPathB, ihf]
      exact ⟨fun h => IsPath.app a h, fun h => by cases h with | app _ hp => exact hp⟩

/-- The two components of the algorithm: algorithmic and structural equivalence. -/
structure AlgFns where
  alg : List STy → Tm → Tm → STy → Option Bool
  path : List STy → Tm → Tm → Option (Option STy)

/-- The comparison of two weak head normal forms at the base type. -/
def baseStep (F : AlgFns) (Δ : List STy) : Tm → Tm → Option Bool
  | Tm.sort s, Tm.sort s' => some (decide (s = s'))
  | Tm.pi A B, Tm.pi A' B' =>
      match F.alg Δ A A' STy.base with
      | none => none
      | some false => some false
      | some true => if er A = er A' then F.alg (er A :: Δ) B B' STy.base else some false
  | M', N' =>
      if isPathB M' && isPathB N' then (F.path Δ M' N').map (fun r => decide (r = some STy.base))
      else some false

/-- The comparison of two paths. -/
def pathStep (F : AlgFns) (Δ : List STy) : Tm → Tm → Option (Option STy)
  | Tm.var i, Tm.var j => some (if i = j then some (Δ.getD i STy.base) else none)
  | Tm.app p a, Tm.app q b =>
      match F.path Δ p q with
      | none => none
      | some (some (STy.arrow σ τ)) => (F.alg Δ a b σ).map (fun ok => if ok then some τ else none)
      | some _ => some none
  | _, _ => some none

/-- **The algorithm with fuel `n`.** -/
def algRun : ℕ → AlgFns
  | 0 => ⟨fun _ _ _ _ => none, fun _ _ _ => none⟩
  | n + 1 =>
      { alg := fun Δ M N τ =>
          match τ with
          | STy.arrow σ τ => (algRun n).alg (σ :: Δ) (app (shift M) (var 0)) (app (shift N) (var 0)) τ
          | STy.base =>
              match whnfF n M, whnfF n N with
              | some M', some N' => baseStep (algRun n) Δ M' N'
              | _, _ => none
        path := fun Δ p q => pathStep (algRun n) Δ p q }

/-! ### Answers are correct -/

/-- The comparison at the base of two weak head normal forms, as a relation. -/
inductive BaseCmp (Δ : List STy) : Tm → Tm → Prop
  | sort (s : Srt) : BaseCmp Δ (Tm.sort s) (Tm.sort s)
  | pi {A B A' B' : Tm} : AlgEqE Δ A A' STy.base → er A = er A' →
      AlgEqE (er A :: Δ) B B' STy.base → BaseCmp Δ (Tm.pi A B) (Tm.pi A' B')
  | path {p q : Tm} : PathEqE Δ p q STy.base → BaseCmp Δ p q

/-- Algorithmic equivalence at the base, given the weak head normal forms. -/
theorem algEqE_base_iff {Δ : List STy} {M N M' N' : Tm} (hM : WhRed M M') (hN : WhRed N N')
    (hM' : WhNF M') (hN' : WhNF N') : AlgEqE Δ M N STy.base ↔ BaseCmp Δ M' N' := by
  constructor
  · intro h
    cases h with
    | basePath hM₂ hN₂ hp =>
        have e₁ := WhRed.whnf_unique hM₂ hM (PathEqE.isPath hp).1.whnf hM'
        have e₂ := WhRed.whnf_unique hN₂ hN (PathEqE.isPath hp).2.whnf hN'
        subst e₁; subst e₂
        exact BaseCmp.path hp
    | baseSort hM₂ hN₂ =>
        have e₁ := WhRed.whnf_unique hM₂ hM (whnf_sort _) hM'
        have e₂ := WhRed.whnf_unique hN₂ hN (whnf_sort _) hN'
        subst e₁; subst e₂
        exact BaseCmp.sort _
    | basePi hM₂ hN₂ hA hsk hB =>
        have e₁ := WhRed.whnf_unique hM₂ hM (whnf_pi _ _) hM'
        have e₂ := WhRed.whnf_unique hN₂ hN (whnf_pi _ _) hN'
        subst e₁; subst e₂
        exact BaseCmp.pi hA hsk hB
  · intro h
    cases h with
    | sort s => exact EqvE.baseSort hM hN
    | pi hA hsk hB => exact EqvE.basePi hM hN hA hsk hB
    | path hp => exact EqvE.basePath hM hN hp

/-- What a correct pair of components answers. -/
def AlgFns.Correct (F : AlgFns) : Prop :=
  (∀ {Δ M N τ b}, F.alg Δ M N τ = some b → (b = true ↔ AlgEqE Δ M N τ)) ∧
    (∀ {Δ p q r}, F.path Δ p q = some r → ∀ τ, (PathEqE Δ p q τ ↔ r = some τ))

/-- The base comparison of a path with anything. -/
theorem BaseCmp.of_not_pi_sort {Δ : List STy} {M' N' : Tm}
    (hs : ∀ s s', M' = Tm.sort s → N' = Tm.sort s' → False)
    (hp : ∀ A B A' B', M' = Tm.pi A B → N' = Tm.pi A' B' → False) :
    BaseCmp Δ M' N' ↔ PathEqE Δ M' N' STy.base := by
  constructor
  · intro h
    cases h with
    | sort s => exact (hs s s rfl rfl).elim
    | pi _ _ _ => exact (hp _ _ _ _ rfl rfl).elim
    | path h => exact h
  · exact BaseCmp.path

theorem baseStep_correct {F : AlgFns} (hF : F.Correct) {Δ : List STy} {M' N' : Tm} {b : Bool}
    (h : baseStep F Δ M' N' = some b) : b = true ↔ BaseCmp Δ M' N' := by
  unfold baseStep at h
  split at h
  · next s s' =>
      simp only [Option.some.injEq] at h
      subst h
      constructor
      · intro e
        have : s = s' := of_decide_eq_true e
        subst this
        exact BaseCmp.sort s
      · intro hc
        cases hc with
        | sort => simp
        | path hp => exact absurd (PathEqE.isPath hp).1 (by intro h; cases h)
  · next A B A' B' =>
      split at h
      · cases h
      · next hA =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.false_eq_true, false_iff]
          intro hc
          cases hc with
          | pi hA' _ _ => exact absurd ((hF.1 hA).mpr hA') (by simp)
          | path hp => exact absurd (PathEqE.isPath hp).1 (by intro h; cases h)
      · next hA =>
          have hA' := (hF.1 hA).mp rfl
          split at h
          · next he =>
              rw [hF.1 h]
              constructor
              · intro hB; exact BaseCmp.pi hA' he hB
              · intro hc
                cases hc with
                | pi _ _ hB => exact hB
                | path hp => exact absurd (PathEqE.isPath hp).1 (by intro h; cases h)
          · next he =>
              simp only [Option.some.injEq] at h
              subst h
              simp only [Bool.false_eq_true, false_iff]
              intro hc
              cases hc with
              | pi _ he' _ => exact he he'
              | path hp => exact absurd (PathEqE.isPath hp).1 (by intro h; cases h)
  · next hs hp =>
      rw [BaseCmp.of_not_pi_sort hs hp]
      split at h
      · next hb =>
          simp only [Bool.and_eq_true] at hb
          obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [(hF.2 hr) STy.base]
          simp
      · next hb =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.false_eq_true, false_iff]
          intro hpe
          obtain ⟨h₁, h₂⟩ := PathEqE.isPath hpe
          simp [isPathB_iff.mpr h₁, isPathB_iff.mpr h₂] at hb

theorem pathEqE_var_iff {Δ : List STy} {i j : ℕ} {τ : STy} :
    PathEqE Δ (var i) (var j) τ ↔ i = j ∧ τ = Δ.getD i STy.base := by
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact EqvE.var i

theorem pathEqE_app_iff {Δ : List STy} {p a q b : Tm} {τ : STy} :
    PathEqE Δ (app p a) (app q b) τ ↔ ∃ σ, PathEqE Δ p q (STy.arrow σ τ) ∧ AlgEqE Δ a b σ := by
  constructor
  · intro h; cases h with | app hp ha => exact ⟨_, hp, ha⟩
  · rintro ⟨σ, hp, ha⟩; exact EqvE.app hp ha

/-- The simple type synthesised for a pair of paths is unique. -/
theorem PathEqE.ty_unique {Δ : List STy} {p q : Tm} {τ τ' : STy} (h : PathEqE Δ p q τ)
    (h' : PathEqE Δ p q τ') : τ = τ' :=
  EqvE.path_ty_unique h.symm h'

theorem pathStep_correct {F : AlgFns} (hF : F.Correct) {Δ : List STy} {p q : Tm} {r : Option STy}
    (h : pathStep F Δ p q = some r) : ∀ τ, PathEqE Δ p q τ ↔ r = some τ := by
  intro τ
  unfold pathStep at h
  split at h
  · next i j =>
      simp only [Option.some.injEq] at h
      subst h
      rw [pathEqE_var_iff]
      split
      · next hij => subst hij; simp [eq_comm]
      · next hij => simp [hij]
  · next p a q b =>
      rw [pathEqE_app_iff]
      split at h
      · cases h
      · next σ τ' hpq =>
          obtain ⟨ok, hok, rfl⟩ := Option.map_eq_some_iff.mp h
          have hpq' := (hF.2 hpq)
          constructor
          · rintro ⟨σ', hp, ha⟩
            have e := (hpq' _).mp hp
            simp only [Option.some.injEq, STy.arrow.injEq] at e
            obtain ⟨rfl, rfl⟩ := e
            rw [(hF.1 hok).mpr ha]
            simp
          · intro hr
            cases ok with
            | false => simp at hr
            | true =>
                simp only [ite_true, Option.some.injEq] at hr
                subst hr
                exact ⟨σ, (hpq' _).mpr rfl, (hF.1 hok).mp rfl⟩
      · next r' hr' hpq =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [reduceCtorEq, iff_false]
          rintro ⟨σ', hp, -⟩
          have e := (hF.2 hpq _).mp hp
          subst e
          exact hr' σ' τ rfl
  · next hv ha =>
      simp only [Option.some.injEq] at h
      subst h
      simp only [reduceCtorEq, iff_false]
      intro hpe
      cases hpe with
      | var i => exact hv i i rfl rfl
      | app _ _ => exact ha _ _ _ _ rfl rfl

/-- **The answers of the run are correct.** -/
theorem algRun_correct : ∀ n, (algRun n).Correct
  | 0 => ⟨(fun h => by cases h), fun h => by cases h⟩
  | n + 1 => by
      have hF := algRun_correct n
      refine ⟨fun {Δ M N τ b} h => ?_, fun {Δ p q r} h => pathStep_correct hF h⟩
      cases τ with
      | arrow σ τ =>
          have h' : (algRun n).alg (σ :: Δ) (app (shift M) (var 0)) (app (shift N) (var 0)) τ =
              some b := h
          rw [hF.1 h']
          constructor
          · exact EqvE.arrow
          · intro ha; cases ha with | arrow ha => exact ha
      | base =>
          have h' : (match whnfF n M, whnfF n N with
              | some M', some N' => baseStep (algRun n) Δ M' N'
              | _, _ => none) = some b := h
          split at h'
          · next M' N' hM hN =>
              obtain ⟨hMr, hMn⟩ := whnfF_sound hM
              obtain ⟨hNr, hNn⟩ := whnfF_sound hN
              rw [algEqE_base_iff hMr hNr hMn hNn]
              exact baseStep_correct hF h'
          · cases h'

theorem algRun_alg_correct {n : ℕ} {Δ : List STy} {M N : Tm} {τ : STy} {b : Bool}
    (h : (algRun n).alg Δ M N τ = some b) : b = true ↔ AlgEqE Δ M N τ :=
  (algRun_correct n).1 h

/-! ### Termination -/

theorem baseStep_sort_ne_none (F : AlgFns) (Δ : List STy) (s : Srt) (W : Tm) :
    baseStep F Δ (sort s) W ≠ none := by
  cases W <;> simp [baseStep, isPathB]

theorem baseStep_pi_ne_none (F : AlgFns) (Δ : List STy) (A B W : Tm)
    (hW : ∀ A' B', W ≠ pi A' B') : baseStep F Δ (pi A B) W ≠ none := by
  cases W with
  | pi A' B' => exact absurd rfl (hW A' B')
  | _ => simp [baseStep, isPathB]

theorem baseStep_path_ne_none (F : AlgFns) (Δ : List STy) {P : Tm} (hP : IsPath P) (W : Tm)
    (hW : IsPath W → F.path Δ P W ≠ none) : baseStep F Δ P W ≠ none := by
  have hPb := isPathB_iff.mpr hP
  have key : baseStep F Δ P W =
      if isPathB P && isPathB W then (F.path Δ P W).map (fun r => decide (r = some STy.base))
      else some false := by
    cases hP with
    | var i => cases W <;> rfl
    | app a hp => cases W <;> rfl
  rw [key, hPb, Bool.true_and]
  split
  · next hb =>
      have := hW (isPathB_iff.mp hb)
      intro h
      rw [Option.map_eq_none_iff] at h
      exact this h
  · simp

/-- **Termination**: the run answers on two terms that each have a derivation of the
algorithm at the same simple type. -/
theorem algRun_terminates {k : EqvKind} {Δ : List STy} {M M' : Tm} {τ : STy}
    (h : EqvE k Δ M M' τ) :
    (k = .alg → ∀ {N N' : Tm}, EqvE .alg Δ N N' τ →
      ∃ n₀, ∀ n, n₀ ≤ n → (algRun n).alg Δ M N τ ≠ none) ∧
    (k = .path → ∀ {N N' : Tm} {τ' : STy}, EqvE .path Δ N N' τ' →
      ∃ n₀, ∀ n, n₀ ≤ n → (algRun n).path Δ M N ≠ none) := by
  induction h with
  | @arrow Δ M M' σ τ _ ih =>
      refine ⟨fun _ N N' h2 => ?_, fun h => by cases h⟩
      cases h2 with
      | arrow h2 =>
          obtain ⟨n₁, hn₁⟩ := ih.1 rfl h2
          refine ⟨n₁ + 1, fun n hn => ?_⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          exact hn₁ m (by omega)
  | @basePath Δ M M' P P' hM _ hp ih =>
      refine ⟨fun _ N N' h2 => ?_, fun h => by cases h⟩
      have hPpath := (PathEqE.isPath hp).1
      obtain ⟨w₁, hw₁⟩ := whnfF_complete hM hPpath.whnf
      have hgen : ∀ {W : Tm}, WhRed N W → WhNF W → (IsPath W → ∃ n₂, ∀ n, n₂ ≤ n →
          (algRun n).path Δ P W ≠ none) → ∃ n₀, ∀ n, n₀ ≤ n → (algRun n).alg Δ M N STy.base ≠ none := by
        intro W hNW hWn hpath
        obtain ⟨w₂, hw₂⟩ := whnfF_complete hNW hWn
        by_cases hWp : IsPath W
        · obtain ⟨n₂, hn₂⟩ := hpath hWp
          refine ⟨w₁ + w₂ + n₂ + 1, fun n hn => ?_⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show (match whnfF m M, whnfF m N with
            | some M', some N' => baseStep (algRun m) Δ M' N'
            | _, _ => none) ≠ none
          rw [hw₁ m (by omega), hw₂ m (by omega)]
          exact baseStep_path_ne_none _ _ hPpath W (fun _ => hn₂ m (by omega))
        · refine ⟨w₁ + w₂ + 1, fun n hn => ?_⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show (match whnfF m M, whnfF m N with
            | some M', some N' => baseStep (algRun m) Δ M' N'
            | _, _ => none) ≠ none
          rw [hw₁ m (by omega), hw₂ m (by omega)]
          exact baseStep_path_ne_none _ _ hPpath W (fun h => absurd h hWp)
      cases h2 with
      | basePath hN _ hq => exact hgen hN (PathEqE.isPath hq).1.whnf (fun _ => ih.2 rfl hq)
      | baseSort hN _ =>
          exact hgen hN (whnf_sort _) (fun h => absurd h (by intro h; cases h))
      | basePi hN _ _ _ _ =>
          exact hgen hN (whnf_pi _ _) (fun h => absurd h (by intro h; cases h))
  | @baseSort Δ M M' s hM _ =>
      refine ⟨fun _ N N' h2 => ?_, fun h => by cases h⟩
      obtain ⟨w₁, hw₁⟩ := whnfF_complete hM (whnf_sort s)
      have hgen : ∀ {W : Tm}, WhRed N W → WhNF W →
          ∃ n₀, ∀ n, n₀ ≤ n → (algRun n).alg Δ M N STy.base ≠ none := by
        intro W hNW hWn
        obtain ⟨w₂, hw₂⟩ := whnfF_complete hNW hWn
        refine ⟨w₁ + w₂ + 1, fun n hn => ?_⟩
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        show (match whnfF m M, whnfF m N with
          | some M', some N' => baseStep (algRun m) Δ M' N'
          | _, _ => none) ≠ none
        rw [hw₁ m (by omega), hw₂ m (by omega)]
        exact baseStep_sort_ne_none _ _ s W
      cases h2 with
      | basePath hN _ hq => exact hgen hN (PathEqE.isPath hq).1.whnf
      | baseSort hN _ => exact hgen hN (whnf_sort _)
      | basePi hN _ _ _ _ => exact hgen hN (whnf_pi _ _)
  | @basePi Δ M M' A B A'' B'' hM _ _ _ _ ihA ihB =>
      refine ⟨fun _ N N' h2 => ?_, fun h => by cases h⟩
      obtain ⟨w₁, hw₁⟩ := whnfF_complete hM (whnf_pi A B)
      have hgen : ∀ {W : Tm}, WhRed N W → WhNF W → (∀ A' B', W ≠ pi A' B') →
          ∃ n₀, ∀ n, n₀ ≤ n → (algRun n).alg Δ M N STy.base ≠ none := by
        intro W hNW hWn hWp
        obtain ⟨w₂, hw₂⟩ := whnfF_complete hNW hWn
        refine ⟨w₁ + w₂ + 1, fun n hn => ?_⟩
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        show (match whnfF m M, whnfF m N with
          | some M', some N' => baseStep (algRun m) Δ M' N'
          | _, _ => none) ≠ none
        rw [hw₁ m (by omega), hw₂ m (by omega)]
        exact baseStep_pi_ne_none _ _ A B W hWp
      cases h2 with
      | basePath hN _ hq =>
          exact hgen hN (PathEqE.isPath hq).1.whnf (fun _ _ e => (PathEqE.isPath hq).1.ne_pi e)
      | baseSort hN _ => exact hgen hN (whnf_sort _) (fun _ _ e => by cases e)
      | @basePi _ _ _ A₂ B₂ _ _ hN _ hA₂ _ hB₂ =>
          obtain ⟨w₂, hw₂⟩ := whnfF_complete hN (whnf_pi A₂ B₂)
          obtain ⟨nA, hnA⟩ := ihA.1 rfl hA₂
          have hBall : er A = er A₂ → ∃ nB, ∀ n, nB ≤ n →
              (algRun n).alg (er A :: Δ) B B₂ STy.base ≠ none := by
            intro he
            rw [← he] at hB₂
            exact ihB.1 rfl hB₂
          by_cases he : er A = er A₂
          · obtain ⟨nB, hnB⟩ := hBall he
            refine ⟨w₁ + w₂ + nA + nB + 1, fun n hn => ?_⟩
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            show (match whnfF m M, whnfF m N with
              | some M', some N' => baseStep (algRun m) Δ M' N'
              | _, _ => none) ≠ none
            rw [hw₁ m (by omega), hw₂ m (by omega)]
            simp only [baseStep]
            split
            · next hnone => exact absurd hnone (hnA m (by omega))
            · simp
            · rw [if_pos he]; exact hnB m (by omega)
          · refine ⟨w₁ + w₂ + nA + 1, fun n hn => ?_⟩
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            show (match whnfF m M, whnfF m N with
              | some M', some N' => baseStep (algRun m) Δ M' N'
              | _, _ => none) ≠ none
            rw [hw₁ m (by omega), hw₂ m (by omega)]
            simp only [baseStep]
            split
            · next hnone => exact absurd hnone (hnA m (by omega))
            · simp
            · rw [if_neg he]; simp
  | @var Δ i =>
      refine ⟨(fun h => by cases h), fun _ N N' τ' h2 => ?_⟩
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      show pathStep (algRun m) Δ (var i) N ≠ none
      cases h2 with
      | var j => simp [pathStep]
      | app _ _ => simp [pathStep]
  | @app Δ p p' a a' σ τ hp _ ihp iha =>
      refine ⟨(fun h => by cases h), fun _ N N' τ' h2 => ?_⟩
      cases h2 with
      | var j =>
          refine ⟨1, fun n hn => ?_⟩
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          show pathStep (algRun m) Δ (app p a) (var j) ≠ none
          simp [pathStep]
      | @app _ q q' b b' σ₂ _ hq hb =>
          obtain ⟨np, hnp⟩ := ihp.2 rfl hq
          have key : ∀ m, np ≤ m → (∀ σ' τ'', (algRun m).path Δ p q = some (some (STy.arrow σ' τ'')) →
              (algRun m).alg Δ a b σ' ≠ none) → pathStep (algRun m) Δ (app p a) (app q b) ≠ none := by
            intro m hm hal
            simp only [pathStep]
            split
            · next hnone => exact absurd hnone (hnp m hm)
            · next σ' τ'' hres =>
                intro h
                rw [Option.map_eq_none_iff] at h
                exact hal σ' τ'' hres h
            · simp
          have huniq : ∀ m σ' τ'', (algRun m).path Δ p q = some (some (STy.arrow σ' τ'')) →
              σ' = σ ∧ σ' = σ₂ := by
            intro m σ' τ'' hres
            have hpq := ((algRun_correct m).2 hres (STy.arrow σ' τ'')).mpr rfl
            have e₁ := EqvE.path_ty_unique hp.symm hpq
            have e₂ := EqvE.path_ty_unique hpq hq
            simp only [STy.arrow.injEq] at e₁ e₂
            exact ⟨e₁.1.symm, e₂.1⟩
          by_cases hσ : σ₂ = σ
          · subst hσ
            obtain ⟨na, hna⟩ := iha.1 rfl hb
            refine ⟨np + na + 1, fun n hn => ?_⟩
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            show pathStep (algRun m) Δ (app p a) (app q b) ≠ none
            refine key m (by omega) (fun σ' τ'' hres => ?_)
            obtain ⟨e, -⟩ := huniq m σ' τ'' hres
            subst e
            exact hna m (by omega)
          · refine ⟨np + 1, fun n hn => ?_⟩
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            show pathStep (algRun m) Δ (app p a) (app q b) ≠ none
            refine key m (by omega) (fun σ' τ'' hres => ?_)
            obtain ⟨e₁, e₂⟩ := huniq m σ' τ'' hres
            exact absurd (e₂.symm.trans e₁) hσ

/-! ### Decidability of the declarative equality -/

/-- **The run decides the declarative equality of typable terms**: it answers for all large
fuels, and it answers `true` exactly when `Γ ⊢ M ≡ N : A`. -/
theorem TEqE.decide_spec {Γ : Ctx} {M N A : Tm} (hΓ : WfE Γ) (hM : TypingE Γ M A)
    (hN : TypingE Γ N A) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ b, (algRun n).alg (erCtx Γ) M N (er A) = some b ∧
      (b = true ↔ TEqE Γ M N A) := by
  obtain ⟨n₀, hn₀⟩ := (algRun_terminates (hM.algEq_refl hΓ)).1 rfl (hN.algEq_refl hΓ)
  refine ⟨n₀, fun n hn => ?_⟩
  cases e : (algRun n).alg (erCtx Γ) M N (er A) with
  | none => exact absurd e (hn₀ n hn)
  | some b =>
      refine ⟨b, rfl, ?_⟩
      rw [algRun_alg_correct e, TEqE.iff_algEq hΓ hM hN]

/-- The run answers at some fuel. -/
theorem TEqE.run_answers {Γ : Ctx} {M N A : Tm} (hΓ : WfE Γ) (hM : TypingE Γ M A)
    (hN : TypingE Γ N A) : ∃ n, (algRun n).alg (erCtx Γ) M N (er A) ≠ none := by
  obtain ⟨n₀, hn₀⟩ := (algRun_terminates (hM.algEq_refl hΓ)).1 rfl (hN.algEq_refl hΓ)
  exact ⟨n₀, hn₀ n₀ le_rfl⟩

/-- **The decision procedure**: run the algorithm at the least fuel at which it answers. -/
def decideTEqE (Γ : Ctx) (M N A : Tm) (h : ∃ n, (algRun n).alg (erCtx Γ) M N (er A) ≠ none) :
    Bool :=
  ((algRun (Nat.find h)).alg (erCtx Γ) M N (er A)).getD false

theorem decideTEqE_spec {Γ : Ctx} {M N A : Tm} (hΓ : WfE Γ) (hM : TypingE Γ M A)
    (hN : TypingE Γ N A) :
    decideTEqE Γ M N A (TEqE.run_answers hΓ hM hN) = true ↔ TEqE Γ M N A := by
  have hfind := Nat.find_spec (TEqE.run_answers hΓ hM hN)
  unfold decideTEqE
  cases e : (algRun (Nat.find (TEqE.run_answers hΓ hM hN))).alg (erCtx Γ) M N (er A) with
  | none => exact absurd e hfind
  | some b =>
      simp only [Option.getD_some]
      rw [algRun_alg_correct e, TEqE.iff_algEq hΓ hM hN]

/-- **The declarative equality of typable terms is decidable.** -/
def TEqE.decidable {Γ : Ctx} {M N A : Tm} (hΓ : WfE Γ) (hM : TypingE Γ M A)
    (hN : TypingE Γ N A) : Decidable (TEqE Γ M N A) :=
  decidable_of_iff _ (decideTEqE_spec hΓ hM hN)

end LambdaPi
