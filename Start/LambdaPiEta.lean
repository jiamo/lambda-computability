/-
η-reduction for the dependently typed calculus `λΠ`, and the failure of the Church–Rosser
property for `βη` on *raw* terms.

`Start/LambdaPi.lean` develops β-reduction of `λΠ` and proves it confluent.  The other standard
rule for functions is η, `λ(x : A). f x ⟶ f` when `x` does not occur in `f`; semantically it is
the law that makes the categorical dependent product an actual right adjoint, and its absence is
exactly what `LambdaPiCwa.not_piStruct_weakPi` records about the syntactic model.  This module
adds η to the picture and settles what happens when it is added to the raw calculus.

* `LambdaPi.EtaStep`, `LambdaPi.EtaRed` — one step of η-contraction and its reflexive–transitive
  closure, with the congruence rules and stability under renaming;
* `LambdaPi.rename_factor` — the factorisation lemma for renamings: a commuting square of
  renamings with the pullback property lifts to terms.  It is what lets an η-step under a
  renaming be reflected back through the renaming (`LambdaPi.EtaStep.rename_inv`);
* `LambdaPi.EtaStep.size_lt`, `LambdaPi.exists_etaNf` — η-reduction strictly decreases the size of
  a term, hence terminates: every term has an η-normal form;
* `LambdaPi.EtaStep.strong_confluence`, `LambdaPi.EtaRed.church_rosser` — η-reduction is strongly
  confluent, hence confluent, on all raw terms;
* `LambdaPi.BetaEtaStep`, `LambdaPi.BetaEtaRed`, `LambdaPi.BetaEtaConv` — the union of β and η,
  its closure and the generated conversion;
* `LambdaPi.betaEtaConv_lam_annot` — **βη-conversion forgets the domain annotation of an
  abstraction**: `λ(x : A). b` and `λ(x : A'). b` are βη-convertible for *any* `A`, `A'`, `b`;
* `LambdaPi.not_church_rosser_betaEta` — **βη-reduction on raw `λΠ` terms is not confluent**
  (Nederpelt's counterexample): the term `λ(x : ∗). ((λ(y : □). y) x)` β-reduces to
  `λ(x : ∗). x` and η-reduces to `λ(y : □). y`, and both of those are βη-normal.

The moral is the one the project already follows: for a Church-style calculus, η can only be
added at the level of *typed* conversion, where the two annotations above are provably equal;
the raw rewriting system `β ∪ η` is not confluent, even though each of `β` and `η` is.
-/

import Start.LambdaPi

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace LambdaPi

open Tm

/-! ### Factorisation of renamings -/

/-- A commuting square of renamings with the pullback property: `ρ ∘ θ' = θ ∘ ρ'`, and every
coincidence `ρ n = θ m` comes from a single index `k`.  Such squares are what make an occurrence
of a renamed term inside another renamed term factor through the square. -/
structure RenSquare (ρ θ ρ' θ' : ℕ → ℕ) : Prop where
  /-- The square commutes. -/
  comm : ∀ n, ρ (θ' n) = θ (ρ' n)
  /-- The square is a pullback of index sets. -/
  pb : ∀ n m, ρ n = θ m → ∃ k, n = θ' k ∧ m = ρ' k

theorem RenSquare.upr {ρ θ ρ' θ' : ℕ → ℕ} (h : RenSquare ρ θ ρ' θ') :
    RenSquare (LambdaPi.upr ρ) (LambdaPi.upr θ) (LambdaPi.upr ρ') (LambdaPi.upr θ') := by
  constructor
  · intro n
    cases n with
    | zero => rfl
    | succ n => simp [LambdaPi.upr, h.comm n]
  · intro n m hnm
    cases n with
    | zero =>
        cases m with
        | zero => exact ⟨0, rfl, rfl⟩
        | succ m => simp [LambdaPi.upr] at hnm
    | succ n =>
        cases m with
        | zero => simp [LambdaPi.upr] at hnm
        | succ m =>
            simp only [LambdaPi.upr, Nat.succ.injEq] at hnm
            obtain ⟨k, hk₁, hk₂⟩ := h.pb n m hnm
            exact ⟨k + 1, by simp [LambdaPi.upr, hk₁], by simp [LambdaPi.upr, hk₂]⟩

/-- **Factorisation**: if a renamed term equals another renamed term along a pullback square of
renamings, the two factor through the square. -/
theorem rename_factor {ρ θ ρ' θ' : ℕ → ℕ} (h : RenSquare ρ θ ρ' θ') :
    ∀ (t s : Tm), rename ρ t = rename θ s → ∃ t₀, t = rename θ' t₀ ∧ rename ρ' t₀ = s := by
  intro t
  induction t generalizing ρ θ ρ' θ' with
  | var n =>
      intro s hs
      cases s with
      | var m =>
          simp only [rename_var, Tm.var.injEq] at hs
          obtain ⟨k, hk₁, hk₂⟩ := h.pb n m hs
          exact ⟨var k, by simp [hk₁], by simp [hk₂]⟩
      | _ => simp at hs
  | sort s' =>
      intro s hs
      cases s with
      | sort s'' =>
          simp only [rename_sort, Tm.sort.injEq] at hs
          exact ⟨sort s'', by simp [hs], rfl⟩
      | _ => simp at hs
  | app f a ihf iha =>
      intro s hs
      cases s with
      | app g b =>
          simp only [rename_app, Tm.app.injEq] at hs
          obtain ⟨f₀, hf₁, hf₂⟩ := ihf h g hs.1
          obtain ⟨a₀, ha₁, ha₂⟩ := iha h b hs.2
          exact ⟨app f₀ a₀, by simp [hf₁, ha₁], by simp [hf₂, ha₂]⟩
      | _ => simp at hs
  | lam A b ihA ihb =>
      intro s hs
      cases s with
      | lam A' b' =>
          simp only [rename_lam, Tm.lam.injEq] at hs
          obtain ⟨A₀, hA₁, hA₂⟩ := ihA h A' hs.1
          obtain ⟨b₀, hb₁, hb₂⟩ := ihb h.upr b' hs.2
          exact ⟨lam A₀ b₀, by simp [hA₁, hb₁], by simp [hA₂, hb₂]⟩
      | _ => simp at hs
  | pi A B ihA ihB =>
      intro s hs
      cases s with
      | pi A' B' =>
          simp only [rename_pi, Tm.pi.injEq] at hs
          obtain ⟨A₀, hA₁, hA₂⟩ := ihA h A' hs.1
          obtain ⟨B₀, hB₁, hB₂⟩ := ihB h.upr B' hs.2
          exact ⟨pi A₀ B₀, by simp [hA₁, hB₁], by simp [hA₂, hB₂]⟩
      | _ => simp at hs

/-- Renaming along an injective renaming is injective on terms. -/
theorem rename_injective {ρ : ℕ → ℕ} (hρ : Function.Injective ρ) :
    Function.Injective (rename ρ) := by
  intro t
  induction t generalizing ρ with
  | var n => intro s hs; cases s <;> simp_all [hρ.eq_iff]
  | sort s' => intro s hs; cases s <;> simp_all
  | app f a ihf iha =>
      intro s hs
      cases s with
      | app g b =>
          simp only [rename_app, Tm.app.injEq] at hs
          simp [ihf hρ hs.1, iha hρ hs.2]
      | _ => simp at hs
  | lam A b ihA ihb =>
      intro s hs
      cases s with
      | lam A' b' =>
          simp only [rename_lam, Tm.lam.injEq] at hs
          have hup : Function.Injective (LambdaPi.upr ρ) := by
            intro n m hnm
            cases n <;> cases m <;> simp_all [LambdaPi.upr, hρ.eq_iff]
          simp [ihA hρ hs.1, ihb hup hs.2]
      | _ => simp at hs
  | pi A B ihA ihB =>
      intro s hs
      cases s with
      | pi A' B' =>
          simp only [rename_pi, Tm.pi.injEq] at hs
          have hup : Function.Injective (LambdaPi.upr ρ) := by
            intro n m hnm
            cases n <;> cases m <;> simp_all [LambdaPi.upr, hρ.eq_iff]
          simp [ihA hρ hs.1, ihB hup hs.2]
      | _ => simp at hs

theorem shift_injective : Function.Injective shift :=
  rename_injective Nat.succ_injective

/-- The square that reflects a shift through an arbitrary renaming. -/
theorem renSquare_upr_succ (ρ : ℕ → ℕ) : RenSquare (LambdaPi.upr ρ) Nat.succ ρ Nat.succ where
  comm _ := rfl
  pb n m h := by
    cases n with
    | zero => simp [LambdaPi.upr] at h
    | succ n => exact ⟨n, rfl, by simpa [LambdaPi.upr] using h.symm⟩

/-! ### η-reduction -/

/-- One step of η-contraction: `λ(x : A). f x ⟶ f` when `x` is not free in `f`, together with the
congruence rules.  In de Bruijn form the side condition is that the function part is a `shift`. -/
inductive EtaStep : Tm → Tm → Prop
  | eta (A t : Tm) : EtaStep (lam A (app (shift t) (var 0))) t
  | appL {f f' : Tm} (a : Tm) : EtaStep f f' → EtaStep (app f a) (app f' a)
  | appR (f : Tm) {a a' : Tm} : EtaStep a a' → EtaStep (app f a) (app f a')
  | lamL {A A' : Tm} (b : Tm) : EtaStep A A' → EtaStep (lam A b) (lam A' b)
  | lamR (A : Tm) {b b' : Tm} : EtaStep b b' → EtaStep (lam A b) (lam A b')
  | piL {A A' : Tm} (B : Tm) : EtaStep A A' → EtaStep (pi A B) (pi A' B)
  | piR (A : Tm) {B B' : Tm} : EtaStep B B' → EtaStep (pi A B) (pi A B')

/-- Many-step η-reduction. -/
inductive EtaRed : Tm → Tm → Prop
  | refl (t : Tm) : EtaRed t t
  | tail {t u v : Tm} : EtaRed t u → EtaStep u v → EtaRed t v

namespace EtaRed

theorem single {t u : Tm} (h : EtaStep t u) : EtaRed t u := (EtaRed.refl t).tail h

theorem trans {t u v : Tm} (h₁ : EtaRed t u) (h₂ : EtaRed u v) : EtaRed t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

theorem head {t u v : Tm} (h : EtaStep t u) (h' : EtaRed u v) : EtaRed t v := (single h).trans h'

end EtaRed

/-- No η-step out of a variable. -/
theorem EtaStep.var_inv {n : ℕ} {t : Tm} (h : EtaStep (var n) t) : False := by cases h

/-- No η-step out of a sort. -/
theorem EtaStep.sort_inv {s : Srt} {t : Tm} (h : EtaStep (sort s) t) : False := by cases h

/-- η-reduction is stable under renaming. -/
theorem EtaStep.rename {t t' : Tm} (h : EtaStep t t') (ρ : ℕ → ℕ) :
    EtaStep (LambdaPi.rename ρ t) (LambdaPi.rename ρ t') := by
  induction h generalizing ρ with
  | eta A t =>
      have : LambdaPi.rename (LambdaPi.upr ρ) (shift t) = shift (LambdaPi.rename ρ t) := by
        simp [shift, rename_rename, LambdaPi.upr]
      simpa [this, LambdaPi.upr] using EtaStep.eta (LambdaPi.rename ρ A) (LambdaPi.rename ρ t)
  | appL a _ ih => exact EtaStep.appL _ (ih ρ)
  | appR f _ ih => exact EtaStep.appR _ (ih ρ)
  | lamL b _ ih => exact EtaStep.lamL _ (ih ρ)
  | lamR A _ ih => exact EtaStep.lamR _ (ih (LambdaPi.upr ρ))
  | piL B _ ih => exact EtaStep.piL _ (ih ρ)
  | piR A _ ih => exact EtaStep.piR _ (ih (LambdaPi.upr ρ))

/-- The general form of the reflection of an η-step through a renaming. -/
theorem EtaStep.rename_inv_aux : ∀ {t' w : Tm}, EtaStep t' w → ∀ {ρ : ℕ → ℕ} {t : Tm},
    t' = LambdaPi.rename ρ t → ∃ w₀, w = LambdaPi.rename ρ w₀ ∧ EtaStep t w₀ := by
  intro t' w h
  induction h with
  | eta A s =>
      intro ρ t ht
      cases t with
      | lam A₀ b₀ =>
          simp only [rename_lam, Tm.lam.injEq] at ht
          obtain ⟨-, hb⟩ := ht
          cases b₀ with
          | app f a =>
              simp only [rename_app, Tm.app.injEq] at hb
              obtain ⟨hf, ha⟩ := hb
              have ha0 : a = var 0 := by
                cases a with
                | var k =>
                    cases k with
                    | zero => rfl
                    | succ k => simp [LambdaPi.upr] at ha
                | _ => simp at ha
              obtain ⟨f₀, hf₁, hf₂⟩ :=
                rename_factor (renSquare_upr_succ ρ) f s (by simpa [shift] using hf.symm)
              subst ha0
              subst hf₁
              exact ⟨f₀, hf₂.symm, EtaStep.eta A₀ f₀⟩
          | _ => simp at hb
      | _ => simp at ht
  | @appL f f' a _ ih =>
      intro ρ t ht
      cases t with
      | app f₁ a₁ =>
          simp only [rename_app, Tm.app.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.1
          exact ⟨app w₀ a₁, by simp [hw₁, ht.2], EtaStep.appL _ hw₂⟩
      | _ => simp at ht
  | @appR f a a' _ ih =>
      intro ρ t ht
      cases t with
      | app f₁ a₁ =>
          simp only [rename_app, Tm.app.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.2
          exact ⟨app f₁ w₀, by simp [hw₁, ht.1], EtaStep.appR _ hw₂⟩
      | _ => simp at ht
  | @lamL A A' b _ ih =>
      intro ρ t ht
      cases t with
      | lam A₁ b₁ =>
          simp only [rename_lam, Tm.lam.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.1
          exact ⟨lam w₀ b₁, by simp [hw₁, ht.2], EtaStep.lamL _ hw₂⟩
      | _ => simp at ht
  | @lamR A b b' _ ih =>
      intro ρ t ht
      cases t with
      | lam A₁ b₁ =>
          simp only [rename_lam, Tm.lam.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.2
          exact ⟨lam A₁ w₀, by simp [hw₁, ht.1], EtaStep.lamR _ hw₂⟩
      | _ => simp at ht
  | @piL A A' B _ ih =>
      intro ρ t ht
      cases t with
      | pi A₁ B₁ =>
          simp only [rename_pi, Tm.pi.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.1
          exact ⟨pi w₀ B₁, by simp [hw₁, ht.2], EtaStep.piL _ hw₂⟩
      | _ => simp at ht
  | @piR A B B' _ ih =>
      intro ρ t ht
      cases t with
      | pi A₁ B₁ =>
          simp only [rename_pi, Tm.pi.injEq] at ht
          obtain ⟨w₀, hw₁, hw₂⟩ := ih ht.2
          exact ⟨pi A₁ w₀, by simp [hw₁, ht.1], EtaStep.piR _ hw₂⟩
      | _ => simp at ht

/-- An η-step performed under a renaming comes from an η-step before the renaming. -/
theorem EtaStep.rename_inv {ρ : ℕ → ℕ} {t w : Tm} (h : EtaStep (LambdaPi.rename ρ t) w) :
    ∃ w₀, w = LambdaPi.rename ρ w₀ ∧ EtaStep t w₀ :=
  EtaStep.rename_inv_aux h rfl

/-- An η-step out of a shifted term comes from an η-step before the shift. -/
theorem EtaStep.shift_inv {t w : Tm} (h : EtaStep (shift t) w) :
    ∃ w₀, w = shift w₀ ∧ EtaStep t w₀ := EtaStep.rename_inv h

/-! ### η-reduction terminates -/

/-- The size of a term. -/
def size : Tm → ℕ
  | var _ => 1
  | sort _ => 1
  | app f a => size f + size a + 1
  | lam A b => size A + size b + 1
  | pi A B => size A + size B + 1

@[simp] theorem size_rename (ρ : ℕ → ℕ) (t : Tm) : size (LambdaPi.rename ρ t) = size t := by
  induction t generalizing ρ <;> simp_all [size]

/-- An η-step strictly decreases the size. -/
theorem EtaStep.size_lt {t u : Tm} (h : EtaStep t u) : size u < size t := by
  induction h with
  | eta A t => simp [size, shift]; omega
  | appL _ _ ih => simp [size]; omega
  | appR _ _ ih => simp [size]; omega
  | lamL _ _ ih => simp [size]; omega
  | lamR _ _ ih => simp [size]; omega
  | piL _ _ ih => simp [size]; omega
  | piR _ _ ih => simp [size]; omega

/-- A term is η-normal when no η-step applies to it. -/
def EtaNf (t : Tm) : Prop := ∀ u, ¬ EtaStep t u

theorem size_pos (t : Tm) : 0 < size t := by cases t <;> simp [size]

/-- **η-reduction terminates**: every term has an η-normal form. -/
theorem exists_etaNf (t : Tm) : ∃ u, EtaRed t u ∧ EtaNf u := by
  suffices h : ∀ n t, size t ≤ n → ∃ u, EtaRed t u ∧ EtaNf u from h (size t) t le_rfl
  intro n
  induction n with
  | zero => intro t ht; exact absurd ht (by have := size_pos t; omega)
  | succ n ih =>
      intro t ht
      by_cases h : EtaNf t
      · exact ⟨t, EtaRed.refl t, h⟩
      · simp only [EtaNf, not_forall, not_not] at h
        obtain ⟨u, hu⟩ := h
        obtain ⟨v, hv₁, hv₂⟩ := ih u (by have := hu.size_lt; omega)
        exact ⟨v, EtaRed.head hu hv₁, hv₂⟩

/-! ### η-reduction is confluent -/

/-- The reflexive closure of an η-step. -/
def EtaStep0 (t u : Tm) : Prop := t = u ∨ EtaStep t u

theorem EtaStep0.red {t u : Tm} (h : EtaStep0 t u) : EtaRed t u := by
  rcases h with rfl | h
  · exact EtaRed.refl _
  · exact EtaRed.single h

theorem EtaStep0.appL {f f' : Tm} (a : Tm) (h : EtaStep0 f f') : EtaStep0 (app f a) (app f' a) := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (EtaStep.appL a h)]

theorem EtaStep0.appR (f : Tm) {a a' : Tm} (h : EtaStep0 a a') : EtaStep0 (app f a) (app f a') := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (EtaStep.appR f h)]

theorem EtaStep0.lamL {A A' : Tm} (b : Tm) (h : EtaStep0 A A') : EtaStep0 (lam A b) (lam A' b) := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (EtaStep.lamL b h)]

theorem EtaStep0.lamR (A : Tm) {b b' : Tm} (h : EtaStep0 b b') : EtaStep0 (lam A b) (lam A b') := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (EtaStep.lamR A h)]

theorem EtaStep0.piL {A A' : Tm} (B : Tm) (h : EtaStep0 A A') : EtaStep0 (pi A B) (pi A' B) := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (EtaStep.piL B h)]

theorem EtaStep0.piR (A : Tm) {B B' : Tm} (h : EtaStep0 B B') : EtaStep0 (pi A B) (pi A B') := by
  rcases h with rfl | h
  exacts [Or.inl rfl, Or.inr (EtaStep.piR A h)]

/-- Inversion for an η-step out of an abstraction. -/
theorem EtaStep.lam_inv {A b w : Tm} (h : EtaStep (lam A b) w) :
    (∃ s, b = app (shift s) (var 0) ∧ w = s) ∨
      (∃ A', EtaStep A A' ∧ w = lam A' b) ∨ (∃ b', EtaStep b b' ∧ w = lam A b') := by
  cases h with
  | eta _ _ => exact Or.inl ⟨_, rfl, rfl⟩
  | lamL _ h => exact Or.inr (Or.inl ⟨_, h, rfl⟩)
  | lamR _ h => exact Or.inr (Or.inr ⟨_, h, rfl⟩)

/-- **η-reduction is strongly confluent**: two η-steps out of the same term are joined by at most
one η-step on each side. -/
theorem EtaStep.strong_confluence {t u v : Tm} (h₁ : EtaStep t u) (h₂ : EtaStep t v) :
    ∃ w, EtaStep0 u w ∧ EtaStep0 v w := by
  induction h₁ generalizing v with
  | eta A s =>
      rcases h₂.lam_inv with ⟨s', hs', rfl⟩ | ⟨A', hA', rfl⟩ | ⟨b', hb', rfl⟩
      · simp only [Tm.app.injEq, and_true] at hs'
        exact ⟨s, Or.inl rfl, Or.inl (shift_injective hs').symm⟩
      · exact ⟨s, Or.inl rfl, Or.inr (EtaStep.eta _ s)⟩
      · cases hb' with
        | appL _ hf =>
            obtain ⟨s₀, rfl, hs⟩ := EtaStep.shift_inv hf
            exact ⟨s₀, Or.inr hs, Or.inr (EtaStep.eta _ s₀)⟩
        | appR _ ha => cases ha
  | @appL f f' a hf ih =>
      cases h₂ with
      | appL _ hf₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih hf₂
          exact ⟨app w a, hw₁.appL a, hw₂.appL a⟩
      | appR _ ha₂ =>
          exact ⟨app f' _, Or.inr (EtaStep.appR _ ha₂), Or.inr (EtaStep.appL _ hf)⟩
  | @appR f a a' ha ih =>
      cases h₂ with
      | appL _ hf₂ =>
          exact ⟨app _ a', Or.inr (EtaStep.appL _ hf₂), Or.inr (EtaStep.appR _ ha)⟩
      | appR _ ha₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih ha₂
          exact ⟨app f w, hw₁.appR f, hw₂.appR f⟩
  | @lamL A A' b hA ih =>
      rcases h₂.lam_inv with ⟨s, hbs, hv⟩ | ⟨A₂, hA₂, rfl⟩ | ⟨b₂, hb₂, rfl⟩
      · subst hbs; subst hv
        exact ⟨v, Or.inr (EtaStep.eta A' v), Or.inl rfl⟩
      · obtain ⟨w, hw₁, hw₂⟩ := ih hA₂
        exact ⟨lam w b, hw₁.lamL b, hw₂.lamL b⟩
      · exact ⟨lam A' b₂, Or.inr (EtaStep.lamR _ hb₂), Or.inr (EtaStep.lamL _ hA)⟩
  | @lamR A b b' hb ih =>
      rcases h₂.lam_inv with ⟨s, hs, rfl⟩ | ⟨A₂, hA₂, rfl⟩ | ⟨b₂, hb₂, rfl⟩
      · subst hs
        cases hb with
        | appL _ hf =>
            obtain ⟨s₀, rfl, hs₀⟩ := EtaStep.shift_inv hf
            exact ⟨s₀, Or.inr (EtaStep.eta _ s₀), Or.inr hs₀⟩
        | appR _ ha => cases ha
      · exact ⟨lam A₂ b', Or.inr (EtaStep.lamL _ hA₂), Or.inr (EtaStep.lamR _ hb)⟩
      · obtain ⟨w, hw₁, hw₂⟩ := ih hb₂
        exact ⟨lam A w, hw₁.lamR A, hw₂.lamR A⟩
  | @piL A A' B hA ih =>
      cases h₂ with
      | piL _ hA₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih hA₂
          exact ⟨pi w B, hw₁.piL B, hw₂.piL B⟩
      | piR _ hB₂ =>
          exact ⟨pi A' _, Or.inr (EtaStep.piR _ hB₂), Or.inr (EtaStep.piL _ hA)⟩
  | @piR A B B' hB ih =>
      cases h₂ with
      | piL _ hA₂ =>
          exact ⟨pi _ B', Or.inr (EtaStep.piL _ hA₂), Or.inr (EtaStep.piR _ hB)⟩
      | piR _ hB₂ =>
          obtain ⟨w, hw₁, hw₂⟩ := ih hB₂
          exact ⟨pi A w, hw₁.piR A, hw₂.piR A⟩

/-- Strong confluence tiles along a reduction sequence. -/
theorem EtaStep.strip {t u v : Tm} (h₁ : EtaStep t u) (h₂ : EtaRed t v) :
    ∃ w, EtaRed u w ∧ EtaStep0 v w := by
  induction h₂ with
  | refl => exact ⟨u, EtaRed.refl u, Or.inr h₁⟩
  | @tail v₀ v hv hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      rcases hw₂ with rfl | hw₂
      · exact ⟨v, hw₁.tail hs, Or.inl rfl⟩
      · obtain ⟨z, hz₁, hz₂⟩ := hw₂.strong_confluence hs
        exact ⟨z, hw₁.trans hz₁.red, hz₂⟩

/-- **η-reduction is confluent.** -/
theorem EtaRed.church_rosser {t u v : Tm} (h₁ : EtaRed t u) (h₂ : EtaRed t v) :
    ∃ w, EtaRed u w ∧ EtaRed v w := by
  induction h₁ with
  | refl => exact ⟨v, h₂, EtaRed.refl v⟩
  | @tail u₀ u hu hs ih =>
      obtain ⟨w₀, hw₁, hw₂⟩ := ih
      obtain ⟨z, hz₁, hz₂⟩ := hs.strip hw₁
      exact ⟨z, hz₁, hw₂.trans hz₂.red⟩

/-! ### βη-reduction -/

/-- One step of βη-reduction: a β-step or an η-step. -/
def BetaEtaStep (t u : Tm) : Prop := Step t u ∨ EtaStep t u

/-- Many-step βη-reduction. -/
inductive BetaEtaRed : Tm → Tm → Prop
  | refl (t : Tm) : BetaEtaRed t t
  | tail {t u v : Tm} : BetaEtaRed t u → BetaEtaStep u v → BetaEtaRed t v

/-- βη-conversion: the equivalence relation generated by βη-reduction. -/
inductive BetaEtaConv : Tm → Tm → Prop
  | refl (t : Tm) : BetaEtaConv t t
  | step {t u v : Tm} : BetaEtaConv t u → BetaEtaStep u v → BetaEtaConv t v
  | stepInv {t u v : Tm} : BetaEtaConv t u → BetaEtaStep v u → BetaEtaConv t v

namespace BetaEtaRed

theorem single {t u : Tm} (h : BetaEtaStep t u) : BetaEtaRed t u := (BetaEtaRed.refl t).tail h

theorem ofStep {t u : Tm} (h : Step t u) : BetaEtaRed t u := single (Or.inl h)

theorem ofEtaStep {t u : Tm} (h : EtaStep t u) : BetaEtaRed t u := single (Or.inr h)

theorem trans {t u v : Tm} (h₁ : BetaEtaRed t u) (h₂ : BetaEtaRed u v) : BetaEtaRed t v := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact ih.tail hs

end BetaEtaRed

namespace BetaEtaConv

theorem ofRed {t u : Tm} (h : BetaEtaRed t u) : BetaEtaConv t u := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | tail _ hs ih => exact ih.step hs

theorem trans {t u v : Tm} (h₁ : BetaEtaConv t u) (h₂ : BetaEtaConv u v) : BetaEtaConv t v := by
  induction h₂ with
  | refl => exact h₁
  | step _ hs ih => exact ih.step hs
  | stepInv _ hs ih => exact ih.stepInv hs

theorem symm {t u : Tm} (h : BetaEtaConv t u) : BetaEtaConv u t := by
  induction h with
  | refl => exact BetaEtaConv.refl _
  | step _ hs ih => exact ((BetaEtaConv.refl _).stepInv hs).trans ih
  | stepInv _ hs ih => exact ((BetaEtaConv.refl _).step hs).trans ih

theorem ofJoin {t u v : Tm} (h₁ : BetaEtaRed t v) (h₂ : BetaEtaRed u v) : BetaEtaConv t u :=
  (ofRed h₁).trans (ofRed h₂).symm

end BetaEtaConv

/-! ### βη forgets the domain annotation -/

/-- Instantiating a term that was shifted under one binder at the variable `0` is the identity. -/
theorem inst_zero_rename_upr_succ (b : Tm) :
    (LambdaPi.rename (LambdaPi.upr Nat.succ) b)[var 0] = b := by
  have h : ∀ n, scons (var 0) ids (LambdaPi.upr Nat.succ n) = ids n := by
    intro n; cases n <;> rfl
  simp only [inst, subst_rename]
  rw [subst_congr h b, subst_ids]

/-- **βη-conversion forgets the domain annotation**: the abstractions `λ(x : A). b` and
`λ(x : A'). b` are βη-convertible whatever the annotations `A` and `A'` are.  This is the
pathology of adding η to a Church-style calculus at the level of raw terms. -/
theorem betaEtaConv_lam_annot (A A' b : Tm) : BetaEtaConv (lam A b) (lam A' b) := by
  have hbeta : Step (lam A (app (shift (lam A' b)) (var 0))) (lam A b) := by
    have h := Step.lamR A (Step.beta (LambdaPi.rename Nat.succ A')
      (LambdaPi.rename (LambdaPi.upr Nat.succ) b) (var 0))
    rwa [inst_zero_rename_upr_succ b] at h
  have heta : EtaStep (lam A (app (shift (lam A' b)) (var 0))) (lam A' b) := EtaStep.eta A _
  exact (BetaEtaConv.ofRed (BetaEtaRed.ofStep hbeta)).symm.trans
    (BetaEtaConv.ofRed (BetaEtaRed.ofEtaStep heta))

/-! ### βη is not confluent -/

/-- The two abstractions of the counterexample are βη-normal. -/
theorem betaEtaNf_lam_sort_var (s : Srt) : ∀ u, ¬ BetaEtaStep (lam (sort s) (var 0)) u := by
  intro u h
  rcases h with h | h
  · cases h with
    | lamL _ h => cases h
    | lamR _ h => cases h
  · cases h with
    | lamL _ h => cases h
    | lamR _ h => cases h

/-- A βη-reduction out of a βη-normal term is trivial. -/
theorem BetaEtaRed.eq_of_nf {t u : Tm} (h : BetaEtaRed t u) (hn : ∀ v, ¬ BetaEtaStep t v) :
    u = t := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact absurd (ih ▸ hs) (hn _)

/-- **Nederpelt's counterexample**: βη-reduction on raw `λΠ` terms is *not* confluent, even though
β-reduction is (`LambdaPi.church_rosser`) and η-reduction is (`LambdaPi.EtaRed.church_rosser`).
The witness is `λ(x : ∗). ((λ(y : □). y) x)`, which β-reduces to `λ(x : ∗). x` and η-reduces to
`λ(y : □). y`; both are βη-normal and they are distinct. -/
theorem not_church_rosser_betaEta :
    ¬ ∀ t u v : Tm, BetaEtaRed t u → BetaEtaRed t v → ∃ w, BetaEtaRed u w ∧ BetaEtaRed v w := by
  intro hcr
  have hshift : shift (lam (sort Srt.box) (var 0)) = lam (sort Srt.box) (var 0) := rfl
  have hbeta : BetaEtaRed (lam (sort Srt.star) (app (lam (sort Srt.box) (var 0)) (var 0)))
      (lam (sort Srt.star) (var 0)) :=
    BetaEtaRed.ofStep (Step.lamR _ (Step.beta (sort Srt.box) (var 0) (var 0)))
  have heta : BetaEtaRed (lam (sort Srt.star) (app (lam (sort Srt.box) (var 0)) (var 0)))
      (lam (sort Srt.box) (var 0)) := by
    refine BetaEtaRed.ofEtaStep ?_
    have := EtaStep.eta (sort Srt.star) (lam (sort Srt.box) (var 0))
    rwa [hshift] at this
  obtain ⟨w, hw₁, hw₂⟩ := hcr _ _ _ hbeta heta
  have h₁ := hw₁.eq_of_nf (betaEtaNf_lam_sort_var Srt.star)
  have h₂ := hw₂.eq_of_nf (betaEtaNf_lam_sort_var Srt.box)
  rw [h₁] at h₂
  simp at h₂

end LambdaPi
