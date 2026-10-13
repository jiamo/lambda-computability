/-
**Decidable type checking for the calculus of constructions and every corner of the cube.**

Step (f) of task `M23-COC-SN`.  With strong normalization (`cube_stronglyNormalizing`) and the
normalization function of `Start/PTSNormalize.lean`, type inference is a structural algorithm:

* `CoCInfer.infer f Γ hΓ M` — for a valid context `Γ` of the corner `f` (`cubeSpec f`), returns
  either a type `T` of `M` together with the sort of `T` (or the information `T = □`), or a proof
  that `M` has no type.  It is defined by well-founded recursion on the total size of the context
  and the expression; conversion tests compare normal forms (`normalize`), which exist because
  every legal expression is strongly normalizing.
* `CoCInfer.decidableTypable` — **typability is decidable**: `Decidable (∃ T, Γ ⊢ M : T)`;
* `CoCInfer.decidableTyping` — **type checking is decidable**: `Decidable (Γ ⊢ M : T)`;
* `CoCInfer.decidableWf` — validity of contexts is decidable.

Everything is computable; the strong-normalization proofs are only used as termination
certificates for `normalize`.  The instance `f = coc` gives decidable type checking for the
calculus of constructions (`CoCInfer.coc_decidableTyping`).
-/

import Start.CoCSN
import Start.PTSNormalize

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PureTypeSystem

namespace CoCInfer

open LambdaPi (Srt)

/-! ### Preliminaries -/

instance decAllows (f : CubeFeatures) (s₁ s₂ : Srt) : Decidable (f.allows s₁ s₂) := by
  cases s₁ <;> cases s₂ <;> unfold CubeFeatures.allows <;> infer_instance

/-- The size of an expression. -/
def size : Expr Srt → ℕ
  | .var _ => 1
  | .sort _ => 1
  | .app F a => size F + size a + 1
  | .lam A b => size A + size b + 1
  | .pi A B => size A + size B + 1

/-- The total size of a context. -/
def ctxSize : List (Expr Srt) → ℕ
  | [] => 0
  | A :: Γ => size A + ctxSize Γ

theorem ctxSize_drop_add_le : ∀ (Γ : List (Expr Srt)) (n : ℕ) (hn : n < Γ.length),
    ctxSize (Γ.drop (n + 1)) + size Γ[n] ≤ ctxSize Γ
  | A :: Γ, 0, _ => by simp [ctxSize]; omega
  | A :: Γ, n + 1, hn => by
      have := ctxSize_drop_add_le Γ n (by simpa using hn)
      simp only [List.drop_succ_cons, List.getElem_cons_succ, ctxSize]
      omega

/-- `n`-fold lifting of the free variables. -/
def lift (k : ℕ) (A : Expr Srt) : Expr Srt := (Expr.rename Nat.succ)^[k] A

theorem lift_succ (k : ℕ) (A : Expr Srt) : lift (k + 1) A = (lift k A).rename Nat.succ := by
  simp [lift, Function.iterate_succ_apply']

theorem lift_sort (k : ℕ) (s : Srt) : lift k (.sort s) = .sort s := by
  induction k with
  | zero => rfl
  | succ k ih => rw [lift_succ, ih]; rfl

theorem lookup_lift : ∀ (Γ : List (Expr Srt)) (n : ℕ) (hn : n < Γ.length),
    Lookup Γ n (lift (n + 1) Γ[n])
  | A :: Γ, 0, _ => .zero A Γ
  | A :: Γ, n + 1, hn => by
      rw [lift_succ]
      exact .succ A (lookup_lift Γ n (by simpa using hn))

theorem lookup_lt {Γ : List (Expr Srt)} {n : ℕ} {A : Expr Srt} (h : Lookup Γ n A) :
    n < Γ.length := by
  induction h with
  | zero => simp
  | succ _ _ ih => simpa using ih

variable {f : CubeFeatures}

theorem valid_entry : ∀ {Γ : List (Expr Srt)} (_ : ValidContext (cubeSpec f) Γ) (n : ℕ)
    (hn : n < Γ.length), ∃ s, HasType (cubeSpec f) (Γ.drop (n + 1)) Γ[n] (.sort s)
  | _ :: _, .cons _ hA, 0, _ => ⟨_, hA⟩
  | _ :: _, .cons hΓ _, n + 1, hn => valid_entry hΓ n (by simpa using hn)

theorem valid_drop {Γ : List (Expr Srt)} (hΓ : ValidContext (cubeSpec f) Γ) (n : ℕ)
    (hn : n < Γ.length) : ValidContext (cubeSpec f) (Γ.drop (n + 1)) :=
  (valid_entry hΓ n hn).choose_spec.valid

theorem weaken_drop : ∀ {Γ : List (Expr Srt)} (_ : ValidContext (cubeSpec f) Γ) (n : ℕ)
    (_ : n < Γ.length) {M A : Expr Srt}, HasType (cubeSpec f) (Γ.drop (n + 1)) M A →
      HasType (cubeSpec f) Γ (lift (n + 1) M) (lift (n + 1) A)
  | _ :: _, .cons _ hB, 0, _, _, _, h => .weaken h hB
  | _ :: _, .cons hΓ hB, n + 1, hn, _, _, h => by
      rw [lift_succ, lift_succ (n + 1)]
      exact .weaken (weaken_drop hΓ n (by simpa using hn) h) hB

theorem sn_type {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    StronglyNormalizing T :=
  cube_stronglyNormalizing f Γ h.valid T ⟨M, .inr h⟩

theorem sn_term {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    StronglyNormalizing M :=
  cube_stronglyNormalizing f Γ h.valid M ⟨T, .inl h⟩

theorem normalize_eq_of_converts {T N : Expr Srt} (hT : StronglyNormalizing T)
    (hc : Converts T N) (hN : Normal N) : normalize T hT = N :=
  Normal.eq_of_converts (normal_normalize T hT) hN
    (.trans _ _ _ (.symm _ _ (reduces_normalize T hT).converts) hc)

/-- The sort an expression is, if it is one. -/
def asSort : Expr Srt → Option Srt
  | .sort s => some s
  | _ => none

theorem asSort_eq_some {e : Expr Srt} {s : Srt} (h : asSort e = some s) : e = .sort s := by
  cases e <;> simp_all [asSort]

/-- The domain and codomain of a product, if the expression is one. -/
def asPi : Expr Srt → Option (Expr Srt × Expr Srt)
  | .pi A B => some (A, B)
  | _ => none

theorem asPi_eq_some {e : Expr Srt} {p : Expr Srt × Expr Srt} (h : asPi e = some p) :
    e = .pi p.1 p.2 := by
  cases e with
  | pi A B => simp only [asPi, Option.some.injEq] at h; subst h; rfl
  | _ => simp [asPi] at h

/-! ### Reading a sort or a product off a type -/

theorem toSort_ok {Γ : List (Expr Srt)} {M T : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ M T) (hr : Reduces T (.sort s)) :
    HasType (cubeSpec f) Γ M (.sort s) := by
  rcases h.regularity with ⟨t, rfl⟩ | ⟨t, ht⟩
  · rw [(Normal.sort t).reduces_eq hr] at h
    exact h
  · cases s with
    | star => exact .conversion h (cube_star_box f h.valid) hr.converts
    | box => exact (CoC.not_conv_box ht hr.converts).elim

theorem toSort_fail {Γ : List (Expr Srt)} {M T : Expr Srt} {s : Srt}
    (h : HasType (cubeSpec f) Γ M T) (hs : HasType (cubeSpec f) Γ M (.sort s)) :
    asSort (normalize T (sn_type h)) = some s := by
  rw [normalize_eq_of_converts _ (CoC.type_unique h hs) (Normal.sort s)]
  rfl

/-- The sort of `M` read off one of its types. -/
def toSort {Γ : List (Expr Srt)} {M T : Expr Srt} (h : HasType (cubeSpec f) Γ M T) :
    PSum {s : Srt // HasType (cubeSpec f) Γ M (.sort s)}
      (∀ s, ¬ HasType (cubeSpec f) Γ M (.sort s)) :=
  match hN : asSort (normalize T (sn_type h)) with
  | some s => .inl ⟨s, toSort_ok h (asSort_eq_some hN ▸ reduces_normalize T (sn_type h))⟩
  | none => .inr fun s hs => by rw [toSort_fail h hs] at hN; cases hN

theorem toPi_ok {Γ : List (Expr Srt)} {F T A B : Expr Srt}
    (h : HasType (cubeSpec f) Γ F T) (hr : Reduces T (.pi A B)) :
    HasType (cubeSpec f) Γ F (.pi A B) := by
  rcases h.regularity with ⟨t, rfl⟩ | ⟨t, ht⟩
  · cases (Normal.sort t).reduces_eq hr
  · exact .conversion h (ht.subject_reduces hr) hr.converts

theorem toPi_fail {Γ : List (Expr Srt)} {F T A B : Expr Srt}
    (h : HasType (cubeSpec f) Γ F T) (hp : HasType (cubeSpec f) Γ F (.pi A B)) :
    asPi (normalize T (sn_type h)) ≠ none := by
  have hsn := sn_type hp
  obtain ⟨A', B', hN, -, -⟩ := (reduces_normalize _ hsn).pi_inv
  rw [(converts_iff_normalize_eq (sn_type h) hsn).mp (CoC.type_unique h hp), hN]
  simp [asPi]

/-- The product type of `F` read off one of its types. -/
def toPi {Γ : List (Expr Srt)} {F T : Expr Srt} (h : HasType (cubeSpec f) Γ F T) :
    PSum {p : Expr Srt × Expr Srt // HasType (cubeSpec f) Γ F (.pi p.1 p.2) ∧
        Reduces T (.pi p.1 p.2) ∧ Normal (.pi p.1 p.2)}
      (∀ A B, ¬ HasType (cubeSpec f) Γ F (.pi A B)) :=
  match hN : asPi (normalize T (sn_type h)) with
  | some p =>
      have hr : Reduces T (.pi p.1 p.2) := asPi_eq_some hN ▸ reduces_normalize T (sn_type h)
      have hn : Normal (.pi p.1 p.2) := asPi_eq_some hN ▸ normal_normalize T (sn_type h)
      .inl ⟨p, toPi_ok h hr, hr, hn⟩
  | none => .inr fun _ _ hp => toPi_fail h hp hN

/-! ### Type inference -/

/-- `T` is `□` (`none`) or has sort `s` (`some s`). -/
def SortedBy (f : CubeFeatures) (Γ : List (Expr Srt)) (T : Expr Srt) : Option Srt → Prop
  | none => T = .sort .box
  | some s => HasType (cubeSpec f) Γ T (.sort s)

/-- An inferred type, with its sort. -/
structure Inferred (f : CubeFeatures) (Γ : List (Expr Srt)) (M : Expr Srt) where
  /-- The type. -/
  ty : Expr Srt
  /-- Its sort, or `none` for `□`. -/
  srt : Option Srt
  typed : HasType (cubeSpec f) Γ M ty
  sorted : SortedBy f Γ ty srt

/-- The sort of the type `sort s`. -/
def sortSrt : Srt → Option Srt
  | .star => some .box
  | .box => none

theorem sorted_sort {Γ : List (Expr Srt)} (hΓ : ValidContext (cubeSpec f) Γ) :
    ∀ s, SortedBy f Γ (.sort s) (sortSrt s)
  | .star => cube_star_box f hΓ
  | .box => rfl

theorem sorted_some {Γ : List (Expr Srt)} {T : Expr Srt} {o : Option Srt} {s : Srt}
    (h : SortedBy f Γ T o) (ho : o = some s) : HasType (cubeSpec f) Γ T (.sort s) := by
  subst ho; exact h

theorem sorted_none {Γ : List (Expr Srt)} {T : Expr Srt} {o : Option Srt}
    (h : SortedBy f Γ T o) (ho : o = none) : T = .sort .box := by
  subst ho; exact h

theorem sorted_app {Γ : List (Expr Srt)} {TF D E a : Expr Srt} {o : Option Srt}
    (hs : SortedBy f Γ TF o) (hr : Reduces TF (.pi D E)) (ha : HasType (cubeSpec f) Γ a D) :
    SortedBy f Γ (E.instantiate a) o := by
  cases o with
  | none =>
      have h : TF = .sort .box := hs
      subst h
      cases (Normal.sort _).reduces_eq hr
  | some s =>
      have hP := (show HasType (cubeSpec f) Γ TF (.sort s) from hs).subject_reduces hr
      obtain ⟨t₁, t₂, t₃, -, hE, ⟨h32, -⟩, hc⟩ := hP.generation_pi
      have hst := Converts.sort_inj hc
      subst hst h32
      exact hE.instantiate ha

/-- **Type inference** for the corner `f` of the cube, in a valid context. -/
def infer (f : CubeFeatures) (Γ : List (Expr Srt)) (hΓ : ValidContext (cubeSpec f) Γ) :
    (M : Expr Srt) → PSum (Inferred f Γ M) (∀ T, ¬ HasType (cubeSpec f) Γ M T)
  | .var n =>
      if hn : n < Γ.length then
        match infer f (Γ.drop (n + 1)) (valid_drop hΓ n hn) Γ[n] with
        | .inr hno => .inr (False.elim (by
            obtain ⟨s, hs⟩ := valid_entry hΓ n hn
            exact hno _ hs))
        | .inl r =>
            match toSort r.typed with
            | .inr hno => .inr (False.elim (by
                obtain ⟨s, hs⟩ := valid_entry hΓ n hn
                exact hno _ hs))
            | .inl ⟨s, hs⟩ =>
                .inl ⟨lift (n + 1) Γ[n], some s, HasType.lookup hΓ (lookup_lift Γ n hn),
                  by simpa only [SortedBy, lift_sort] using weaken_drop hΓ n hn hs⟩
      else .inr fun _ hT => by
        obtain ⟨A, hA, -⟩ := hT.generation
        exact hn (lookup_lt hA)
  | .sort .star => .inl ⟨.sort .box, none, cube_star_box f hΓ, rfl⟩
  | .sort .box => .inr fun _ hT => not_hasType_box f hT
  | .pi A B =>
      match infer f Γ hΓ A with
      | .inr hno => .inr fun _ hT => by
          obtain ⟨_, _, _, hA, -⟩ := hT.generation_pi
          exact hno _ hA
      | .inl rA =>
          match toSort rA.typed with
          | .inr hno => .inr fun _ hT => by
              obtain ⟨_, _, _, hA, -⟩ := hT.generation_pi
              exact hno _ hA
          | .inl ⟨s₁, hA⟩ =>
              match infer f (A :: Γ) (.cons hΓ hA) B with
              | .inr hno => .inr fun _ hT => by
                  obtain ⟨_, _, _, -, hB, -⟩ := hT.generation_pi
                  exact hno _ hB
              | .inl rB =>
                  match toSort rB.typed with
                  | .inr hno => .inr fun _ hT => by
                      obtain ⟨_, _, _, -, hB, -⟩ := hT.generation_pi
                      exact hno _ hB
                  | .inl ⟨s₂, hB⟩ =>
                      if hr : f.allows s₁ s₂ then
                        .inl ⟨.sort s₂, sortSrt s₂, .product hA hB ⟨rfl, hr⟩,
                          sorted_sort hΓ s₂⟩
                      else .inr fun _ hT => by
                        obtain ⟨t₁, t₂, t₃, hA', hB', ⟨-, hr'⟩, -⟩ := hT.generation_pi
                        have h1 := Converts.sort_inj (CoC.type_unique hA hA')
                        have h2 := Converts.sort_inj (CoC.type_unique hB hB')
                        subst h1 h2
                        exact hr hr'
  | .lam A b =>
      match infer f Γ hΓ A with
      | .inr hno => .inr fun _ hT => by
          obtain ⟨_, _, -, hPi, -⟩ := hT.generation_lam
          obtain ⟨_, _, _, hA, -⟩ := hPi.generation_pi
          exact hno _ hA
      | .inl rA =>
          match toSort rA.typed with
          | .inr hno => .inr fun _ hT => by
              obtain ⟨_, _, -, hPi, -⟩ := hT.generation_lam
              obtain ⟨_, _, _, hA, -⟩ := hPi.generation_pi
              exact hno _ hA
          | .inl ⟨s₁, hA⟩ =>
              match infer f (A :: Γ) (.cons hΓ hA) b with
              | .inr hno => .inr fun _ hT => by
                  obtain ⟨_, _, hb, -⟩ := hT.generation_lam
                  exact hno _ hb
              | .inl rb =>
                  match hsrt : rb.srt with
                  | none => .inr fun _ hT => by
                      obtain ⟨B', _, hb', hPi, -⟩ := hT.generation_lam
                      obtain ⟨_, _, _, -, hB', -⟩ := hPi.generation_pi
                      have hc := CoC.type_unique hb' rb.typed
                      rw [sorted_none rb.sorted hsrt] at hc
                      exact CoC.not_conv_box hB' hc
                  | some s₂ =>
                      have hB := sorted_some rb.sorted hsrt
                      if hr : f.allows s₁ s₂ then
                        .inl ⟨.pi A rb.ty, some s₂,
                          .abstraction rb.typed (.product hA hB ⟨rfl, hr⟩),
                          .product hA hB ⟨rfl, hr⟩⟩
                      else .inr fun _ hT => by
                        obtain ⟨B', _, hb', hPi, -⟩ := hT.generation_lam
                        obtain ⟨t₁, t₂, t₃, hA', hB', ⟨-, hr'⟩, -⟩ := hPi.generation_pi
                        have h1 := Converts.sort_inj (CoC.type_unique hA hA')
                        have h2 := CoC.sort_unique_conv hB' hB (CoC.type_unique hb' rb.typed)
                        subst h1 h2
                        exact hr hr'
  | .app F a =>
      match infer f Γ hΓ F with
      | .inr hno => .inr fun _ hT => by
          obtain ⟨_, _, hF, -⟩ := hT.generation_app
          exact hno _ hF
      | .inl rF =>
          match toPi rF.typed with
          | .inr hno => .inr fun _ hT => by
              obtain ⟨_, _, hF, -⟩ := hT.generation_app
              exact hno _ _ hF
          | .inl ⟨(D, E), hFDE, hrDE, hnDE⟩ =>
              match infer f Γ hΓ a with
              | .inr hno => .inr fun _ hT => by
                  obtain ⟨_, _, -, ha, -⟩ := hT.generation_app
                  exact hno _ ha
              | .inl ra =>
                  if hc : normalize ra.ty (sn_type ra.typed) =
                      normalize D (Normal.pi_domain hnDE).stronglyNormalizing then
                    have ha : HasType (cubeSpec f) Γ a D := by
                      obtain ⟨s, hP⟩ := hFDE.product_type_sorted
                      obtain ⟨t₁, _, _, hD, -⟩ := hP.generation_pi
                      exact .conversion ra.typed hD ((converts_iff_normalize_eq _ _).mpr hc)
                    .inl ⟨E.instantiate a, rF.srt, .application hFDE ha,
                      sorted_app rF.sorted hrDE ha⟩
                  else .inr fun _ hT => by
                    obtain ⟨A', B', hF', ha', -⟩ := hT.generation_app
                    apply hc
                    apply (converts_iff_normalize_eq _ _).mp
                    exact .trans _ _ _ (CoC.type_unique ra.typed ha')
                      (.symm _ _ (CoC.type_unique hFDE hF').product_compatibility.1)
termination_by M => ctxSize Γ + size M
decreasing_by
  all_goals first
    | (have := ctxSize_drop_add_le Γ n hn; simp only [size]; omega)
    | (simp only [size, ctxSize]; omega)

/-! ### Decision procedures -/

/-- **Typability is decidable** in every corner of the cube. -/
def decidableTypable (f : CubeFeatures) (Γ : List (Expr Srt))
    (hΓ : ValidContext (cubeSpec f) Γ) (M : Expr Srt) :
    Decidable (∃ T, HasType (cubeSpec f) Γ M T) :=
  match infer f Γ hΓ M with
  | .inl r => isTrue ⟨r.ty, r.typed⟩
  | .inr hno => isFalse fun ⟨T, hT⟩ => hno T hT

/-- Whether `M` is a sort or a sorted expression, decidably. -/
def decidableSorted (f : CubeFeatures) (Γ : List (Expr Srt))
    (hΓ : ValidContext (cubeSpec f) Γ) (M : Expr Srt) :
    PSum {s : Srt // HasType (cubeSpec f) Γ M (.sort s)}
      (∀ s, ¬ HasType (cubeSpec f) Γ M (.sort s)) :=
  match infer f Γ hΓ M with
  | .inl r => toSort r.typed
  | .inr hno => .inr fun _ hs => hno _ hs

theorem hasType_iff {Γ : List (Expr Srt)} {M T T₀ : Expr Srt}
    (h₀ : HasType (cubeSpec f) Γ M T₀) :
    HasType (cubeSpec f) Γ M T ↔
      ((∃ s, T = .sort s) ∨ (∃ s, HasType (cubeSpec f) Γ T (.sort s))) ∧ Converts T₀ T := by
  constructor
  · intro h
    exact ⟨h.regularity, CoC.type_unique h₀ h⟩
  · rintro ⟨⟨s, rfl⟩ | ⟨s, hs⟩, hc⟩
    · obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := h₀.regularity
      · rw [Converts.sort_inj hc] at h₀
        exact h₀
      · cases s with
        | star => exact .conversion h₀ (cube_star_box f h₀.valid) hc
        | box => exact (CoC.not_conv_box ht hc).elim
    · exact .conversion h₀ hs hc

/-- **Type checking is decidable** in every corner of the cube. -/
def decidableTyping (f : CubeFeatures) (Γ : List (Expr Srt))
    (hΓ : ValidContext (cubeSpec f) Γ) (M T : Expr Srt) :
    Decidable (HasType (cubeSpec f) Γ M T) :=
  match infer f Γ hΓ M with
  | .inr hno => isFalse (hno T)
  | .inl r =>
      match hT : asSort T with
      | some s =>
          have hsn : StronglyNormalizing T :=
            asSort_eq_some hT ▸ (Normal.sort s).stronglyNormalizing
          if hc : normalize r.ty (sn_type r.typed) = normalize T hsn then
            isTrue ((hasType_iff r.typed).mpr
              ⟨.inl ⟨s, asSort_eq_some hT⟩, (converts_iff_normalize_eq _ _).mpr hc⟩)
          else isFalse fun h => hc ((converts_iff_normalize_eq _ _).mp
            ((hasType_iff r.typed).mp h).2)
      | none =>
          match decidableSorted f Γ hΓ T with
          | .inr hno => isFalse fun h => by
              rcases ((hasType_iff r.typed).mp h).1 with ⟨s, rfl⟩ | ⟨s, hs⟩
              · cases hT
              · exact hno s hs
          | .inl ⟨s, hs⟩ =>
              if hc : normalize r.ty (sn_type r.typed) = normalize T (sn_term hs) then
                isTrue ((hasType_iff r.typed).mpr
                  ⟨.inr ⟨s, hs⟩, (converts_iff_normalize_eq _ _).mpr hc⟩)
              else isFalse fun h => hc ((converts_iff_normalize_eq _ _).mp
                ((hasType_iff r.typed).mp h).2)

/-- **Validity of contexts is decidable** in every corner of the cube. -/
def decidableWf (f : CubeFeatures) : (Γ : List (Expr Srt)) → Decidable (ValidContext (cubeSpec f) Γ)
  | [] => isTrue .nil
  | A :: Γ =>
      match decidableWf f Γ with
      | isFalse h => isFalse fun h' => by cases h'; contradiction
      | isTrue hΓ =>
          match decidableSorted f Γ hΓ A with
          | .inl ⟨_, hs⟩ => isTrue (.cons hΓ hs)
          | .inr hno => isFalse fun h' => by
              cases h' with
              | cons _ hs => exact hno _ hs

/-- **Decidable type checking for the calculus of constructions.** -/
def coc_decidableTyping (Γ : List (Expr Srt)) (hΓ : ValidContext (cubeSpec coc) Γ)
    (M T : Expr Srt) : Decidable (HasType (cubeSpec coc) Γ M T) :=
  decidableTyping coc Γ hΓ M T

/-- Closed typing judgements are decidable in every corner of the cube (in particular in the
calculus of constructions). -/
instance decidableClosedTyping (f : CubeFeatures) (M T : Expr Srt) :
    Decidable (HasType (cubeSpec f) ([]) M T) :=
  decidableTyping f ([]) .nil M T

end CoCInfer

end PureTypeSystem
