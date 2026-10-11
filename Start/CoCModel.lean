import Start.PTSReduction
import Start.LambdaPi

/-!
# A kind-indexed saturated-set model for the calculus of constructions (syntactic part)

This library's own module (task `M23-COC-SN`, route: Geuvers' saturated-set model, "A short and
flexible proof of strong normalization for the calculus of constructions").  Everything here is
purely syntactic: no typing derivation is used.

* `CoC.Sk` — kind skeletons: `∗`, `Π x:A. k` with `A` a type (`arrO k`, the object argument is
  erased), and `Π α:a. k` with `a` a kind (`arr a k`).
* `CoC.Cls` and `CoC.cl` — a syntactic classifier: given the classes of the free variables it
  computes whether an expression is a kind (with its skeleton), a constructor (with the skeleton
  of its kind) or an object.  `cl_rename` and `cl_subst` show that it commutes with renaming and
  with every class-respecting substitution.
* `CoC.V k` — the candidate space of skeleton `k`: sets of expressions at `∗`, functions between
  candidate spaces at `arr`, and the same space at `arrO` (constructors ignore object arguments).
* `CoC.Sat` — saturated sets for the PTS's own `Beta`, which reduces inside annotations and
  products; `CoC.Cand k` — candidates of skeleton `k`.
* `CoC.interp` — the interpretation of kinds and constructors under a valuation, with its
  renaming and substitution lemmas (`interp_rename`, `interp_subst`), its independence from the
  values of irrelevant variables (`interp_agree`) and the fact that it lands in candidates
  (`interp_cand`), for well-classified expressions (`CoC.WC`).
-/

set_option autoImplicit false

namespace PureTypeSystem

namespace CoC

open LambdaPi (Srt)

/-! ### Families indexed by de Bruijn indices -/

/-- Prepend a value to a family indexed by de Bruijn indices. -/
def ncons {α : Sort*} (x : α) (f : Nat → α) : Nat → α
  | 0 => x
  | n + 1 => f n

@[simp] theorem ncons_zero {α : Sort*} (x : α) (f : Nat → α) : ncons x f 0 = x := rfl
@[simp] theorem ncons_succ {α : Sort*} (x : α) (f : Nat → α) (n : Nat) :
    ncons x f (n + 1) = f n := rfl

@[simp] theorem ncons_comp_succ {α : Sort*} (x : α) (f : Nat → α) :
    ncons x f ∘ Nat.succ = f := rfl

theorem ncons_comp_liftRen {α : Sort*} (x : α) (f : Nat → α) (ρ : Nat → Nat) :
    ncons x f ∘ Expr.liftRen ρ = ncons x (f ∘ ρ) := by
  funext n
  cases n <;> rfl

/-! ### Skeletons and classes -/

/-- Kind skeletons. -/
inductive Sk where
  | star : Sk
  /-- `Π x:A. k` with `A` a type: the argument is an object and is erased. -/
  | arrO : Sk → Sk
  /-- `Π α:a. k` with `a` a kind. -/
  | arr : Sk → Sk → Sk
  deriving DecidableEq

/-- Classes of expressions. -/
inductive Cls where
  | kind : Sk → Cls
  | constr : Sk → Cls
  | obj : Cls
  deriving DecidableEq

/-- The class of a variable bound with a domain of the given class. -/
def bindC : Cls → Cls
  | .kind a => .constr a
  | _ => .obj

/-- The skeleton of a product over a domain of the given class. -/
def domSk : Cls → Sk → Sk
  | .kind a, k => .arr a k
  | _, k => .arrO k

def appCls : Cls → Cls
  | .constr (.arr _ k) => .constr k
  | .constr (.arrO k) => .constr k
  | _ => .obj

def lamCls (cA : Cls) : Cls → Cls
  | .constr k => .constr (domSk cA k)
  | _ => .obj

def piCls (cA : Cls) : Cls → Cls
  | .kind k => .kind (domSk cA k)
  | _ => .constr .star

/-- The syntactic classifier. -/
def cl : (Nat → Cls) → Expr Srt → Cls
  | Δ, .var n => Δ n
  | _, .sort .star => .kind .star
  | _, .sort .box => .obj
  | Δ, .app F _ => appCls (cl Δ F)
  | Δ, .lam A b => lamCls (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) b)
  | Δ, .pi A B => piCls (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) B)

theorem cl_rename (M : Expr Srt) (Δ : Nat → Cls) (ρ : Nat → Nat) :
    cl Δ (M.rename ρ) = cl (Δ ∘ ρ) M := by
  induction M generalizing Δ ρ with
  | var n => rfl
  | sort s => cases s <;> rfl
  | app f a ihf iha => simp only [Expr.rename, cl, ihf]
  | lam A b ihA ihb => simp only [Expr.rename, cl, ihA, ihb, ncons_comp_liftRen]
  | pi A B ihA ihB => simp only [Expr.rename, cl, ihA, ihB, ncons_comp_liftRen]

theorem cl_liftSub {Δ Δ' : Nat → Cls} {σ : Nat → Expr Srt} (hσ : ∀ n, cl Δ (σ n) = Δ' n)
    (c : Cls) (n : Nat) : cl (ncons c Δ) (Expr.liftSub σ n) = ncons c Δ' n := by
  cases n with
  | zero => rfl
  | succ n => simp only [Expr.liftSub_succ, cl_rename, ncons_comp_succ, hσ, ncons_succ]

theorem cl_subst (M : Expr Srt) {Δ Δ' : Nat → Cls} {σ : Nat → Expr Srt}
    (hσ : ∀ n, cl Δ (σ n) = Δ' n) : cl Δ (M.subst σ) = cl Δ' M := by
  induction M generalizing Δ Δ' σ with
  | var n => exact hσ n
  | sort s => cases s <;> rfl
  | app f a ihf iha => simp only [Expr.subst, cl, ihf hσ]
  | lam A b ihA ihb =>
      simp only [Expr.subst, cl, ihA hσ]
      rw [ihb (cl_liftSub hσ _)]
  | pi A B ihA ihB =>
      simp only [Expr.subst, cl, ihA hσ]
      rw [ihB (cl_liftSub hσ _)]

/-- The substitution of a single expression. -/
theorem cl_single {Δ : Nat → Cls} (U : Expr Srt) :
    ∀ n, cl Δ (Expr.single U n) = ncons (cl Δ U) Δ n
  | 0 => rfl
  | _ + 1 => rfl

theorem cl_instantiate (b U : Expr Srt) (Δ : Nat → Cls) :
    cl Δ (b.instantiate U) = cl (ncons (cl Δ U) Δ) b :=
  cl_subst b (cl_single U)

/-! ### Inversions for the class combinators -/

theorem appCls_ne_kind (c : Cls) (k : Sk) : appCls c ≠ .kind k := by
  cases c with
  | kind => simp [appCls]
  | constr s => cases s <;> simp [appCls]
  | obj => simp [appCls]

theorem appCls_eq_constr {c : Cls} {k : Sk} (h : appCls c = .constr k) :
    (∃ a, c = .constr (.arr a k)) ∨ c = .constr (.arrO k) := by
  cases c with
  | kind => simp [appCls] at h
  | constr s => cases s <;> simp_all [appCls]
  | obj => simp [appCls] at h

theorem lamCls_ne_kind (cA c : Cls) (k : Sk) : lamCls cA c ≠ .kind k := by
  rcases c with _ | _ | _ <;> simp [lamCls]

theorem lamCls_eq_constr {cA c : Cls} {k : Sk} (h : lamCls cA c = .constr k) :
    ∃ k₀, c = .constr k₀ ∧ k = domSk cA k₀ := by
  rcases c with _ | k₀ | _ <;> simp_all [lamCls]

theorem domSk_eq_arr {cA : Cls} {k₀ a k : Sk} (h : domSk cA k₀ = .arr a k) :
    cA = .kind a ∧ k₀ = k := by
  rcases cA with a' | _ | _ <;> simp_all [domSk]

theorem domSk_eq_arrO {cA : Cls} {k₀ k : Sk} (h : domSk cA k₀ = .arrO k) :
    (∀ a, cA ≠ .kind a) ∧ k₀ = k := by
  rcases cA with a' | _ | _ <;> simp_all [domSk]

theorem domSk_of_not_kind {cA : Cls} (h : ∀ a, cA ≠ .kind a) (k : Sk) : domSk cA k = .arrO k := by
  rcases cA with a' | _ | _
  · exact absurd rfl (h a')
  all_goals rfl

theorem bindC_of_not_kind {cA : Cls} (h : ∀ a, cA ≠ .kind a) : bindC cA = .obj := by
  rcases cA with a' | _ | _
  · exact absurd rfl (h a')
  all_goals rfl

theorem piCls_star_or_kind (cA c : Cls) :
    piCls cA c = .constr .star ∨ ∃ k, piCls cA c = .kind k := by
  rcases c with k | _ | _ <;> simp [piCls]

/-! ### Saturated sets -/

/-- The strongly normalizing expressions. -/
def snSet : Set (Expr Srt) := {M | StronglyNormalizing M}

/-- Saturated sets, for the PTS's own `Beta` (which also reduces annotations). -/
structure Sat (X : Set (Expr Srt)) : Prop where
  sn : ∀ M ∈ X, StronglyNormalizing M
  var : ∀ (n : Nat) (as : List (Expr Srt)), StronglyNormalizingArgs as →
    (Expr.var n).apps as ∈ X
  head : ∀ (A b a : Expr Srt) (as : List (Expr Srt)), StronglyNormalizing A →
    StronglyNormalizing a → (b.instantiate a).apps as ∈ X →
    (Expr.app (.lam A b) a).apps as ∈ X

theorem snArgs_of_apps {f : Expr Srt} {as : List (Expr Srt)}
    (h : StronglyNormalizing (f.apps as)) : StronglyNormalizingArgs as :=
  Subrelation.accessible
    (r := InvImage (fun N M : Expr Srt => Beta M N) (fun as => f.apps as))
    (fun hab => ArgsStep.apps hab f) (InvImage.accessible _ h)

theorem snArgs_append {as : List (Expr Srt)} {N : Expr Srt} (has : StronglyNormalizingArgs as)
    (hN : StronglyNormalizing N) : StronglyNormalizingArgs (as ++ [N]) := by
  apply StronglyNormalizingArgs.of_forall
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact has.of_mem ha
  · simp only [List.mem_singleton] at ha
    subst ha
    exact hN

theorem apps_append_single (f N : Expr Srt) (as : List (Expr Srt)) :
    f.apps (as ++ [N]) = .app (f.apps as) N := by
  rw [Expr.apps_append]
  rfl

theorem sat_snSet : Sat snSet where
  sn _ h := h
  var n _ has := StronglyNormalizing.var_apps n has
  head A b a as hA ha hc := by
    have hc' : StronglyNormalizing ((b.instantiate a).apps as) := hc
    exact StronglyNormalizing.head_expansion hA
      (StronglyNormalizing.of_subst _ hc'.apps_head) ha (snArgs_of_apps hc') hc'

theorem Sat.var_mem {X : Set (Expr Srt)} (hX : Sat X) (n : Nat) : Expr.var n ∈ X :=
  hX.var n List.nil .nil

theorem Sat.head_mem {X : Set (Expr Srt)} (hX : Sat X) {A b a : Expr Srt}
    (hA : StronglyNormalizing A) (ha : StronglyNormalizing a) (h : b.instantiate a ∈ X) :
    Expr.app (.lam A b) a ∈ X :=
  hX.head A b a List.nil hA ha h

/-- Products of saturated sets, indexed by a family of admissible parameters. -/
def piSet {ι : Type} (X : Set (Expr Srt)) (P : ι → Prop) (F : ι → Set (Expr Srt)) :
    Set (Expr Srt) :=
  {M | ∀ N ∈ X, ∀ i, P i → Expr.app M N ∈ F i}

theorem sat_piSet {ι : Type} {X : Set (Expr Srt)} {P : ι → Prop} {F : ι → Set (Expr Srt)}
    (hX : Sat X) (hne : ∃ i, P i) (hF : ∀ i, P i → Sat (F i)) : Sat (piSet X P F) where
  sn M hM := by
    obtain ⟨i, hi⟩ := hne
    exact ((hF i hi).sn _ (hM _ (hX.var_mem 0) i hi)).app_left
  var n as has N hN i hi := by
    rw [← apps_append_single]
    exact (hF i hi).var n _ (snArgs_append has (hX.sn N hN))
  head A b a as hA ha hc N hN i hi := by
    rw [← apps_append_single]
    apply (hF i hi).head A b a _ hA ha
    rw [apps_append_single]
    exact hc N hN i hi

/-! ### Candidate spaces -/

/-- The candidate space of a skeleton. -/
def V : Sk → Type
  | .star => Set (Expr Srt)
  | .arrO k => V k
  | .arr a k => V a → V k

instance : Membership (Expr Srt) (V .star) :=
  inferInstanceAs (Membership (Expr Srt) (Set (Expr Srt)))

/-- The canonical candidate of each skeleton. -/
def canon : (k : Sk) → V k
  | .star => snSet
  | .arrO k => canon k
  | .arr _ k => fun _ => canon k

/-- Candidates: saturated sets at `∗`, functions preserving candidates at `arr`. -/
def Cand : (k : Sk) → V k → Prop
  | .star, X => Sat X
  | .arrO k, v => Cand k v
  | .arr a k, f => ∀ x, Cand a x → Cand k (f x)

theorem cand_canon : ∀ k : Sk, Cand k (canon k)
  | .star => sat_snSet
  | .arrO k => cand_canon k
  | .arr _ k => fun _ _ => cand_canon k

/-- Valuations: every variable receives a value at every skeleton. -/
abbrev Val := Nat → (k : Sk) → V k

/-- The value of a constructor variable of skeleton `a`; canonical at other skeletons. -/
def ext (a : Sk) (v : V a) : (k : Sk) → V k := fun k => if h : a = k then h ▸ v else canon k

@[simp] theorem ext_self (a : Sk) (v : V a) : ext a v a = v := by
  simp [ext]

/-- The canonical valuation. -/
def canonVal : Val := fun _ k => canon k

/-! ### The interpretation -/

/-- The interpretation of kinds and constructors at an expected skeleton.  Kinds and types are
interpreted at `∗` by sets of expressions; object arguments and object binders are ignored. -/
def interp : (Nat → Cls) → Expr Srt → (k : Sk) → Val → V k
  | _, .var n, k, ξ => ξ n k
  | _, .sort .star, .star, _ => snSet
  | _, .sort .star, .arrO k, _ => canon k
  | _, .sort .star, .arr a k, _ => canon (.arr a k)
  | _, .sort .box, k, _ => canon k
  | Δ, .app F U, k, ξ =>
      match cl Δ U with
      | .constr a => interp Δ F (.arr a k) ξ (interp Δ U a ξ)
      | .kind _ => interp Δ F (.arrO k) ξ
      | .obj => interp Δ F (.arrO k) ξ
  | Δ, .lam A b, .arr a k, ξ =>
      fun v => interp (ncons (bindC (cl Δ A)) Δ) b k (ncons (ext a v) ξ)
  | Δ, .lam A b, .arrO k, ξ => interp (ncons (bindC (cl Δ A)) Δ) b k (ncons canon ξ)
  | _, .lam _ _, .star, _ => snSet
  | Δ, .pi A B, .star, ξ =>
      match cl Δ A with
      | .kind a => piSet (interp Δ A .star ξ) (Cand a)
          (fun v => interp (ncons (.constr a) Δ) B .star (ncons (ext a v) ξ))
      | .constr _ => piSet (ι := Unit) (interp Δ A .star ξ) (fun _ => True)
          (fun _ => interp (ncons .obj Δ) B .star (ncons canon ξ))
      | .obj => piSet (ι := Unit) (interp Δ A .star ξ) (fun _ => True)
          (fun _ => interp (ncons .obj Δ) B .star (ncons canon ξ))
  | _, .pi _ _, .arrO k, _ => canon k
  | _, .pi _ _, .arr a k, _ => canon (.arr a k)

theorem interp_rename (M : Expr Srt) (Δ : Nat → Cls) (ρ : Nat → Nat) (k : Sk) (ξ : Val) :
    interp Δ (M.rename ρ) k ξ = interp (Δ ∘ ρ) M k (ξ ∘ ρ) := by
  induction M generalizing Δ ρ k ξ with
  | var n => rfl
  | sort s => cases s <;> cases k <;> rfl
  | app F U ihF ihU =>
      simp only [Expr.rename, interp, cl_rename]
      cases cl (Δ ∘ ρ) U <;> simp only [ihF, ihU] <;> rfl
  | lam A b ihA ihb =>
      cases k with
      | star => rfl
      | arrO k =>
          simp only [Expr.rename, interp, cl_rename, ihb, ncons_comp_liftRen]
          rfl
      | arr a k =>
          funext v
          simp only [Expr.rename, interp, cl_rename, ihb, ncons_comp_liftRen]
  | pi A B ihA ihB =>
      cases k with
      | arrO k => rfl
      | arr a k => rfl
      | star =>
          simp only [Expr.rename, interp, cl_rename]
          cases cl (Δ ∘ ρ) A <;> simp only [ihA, ihB, ncons_comp_liftRen] <;> rfl

/-- The valuation induced by a substitution. -/
def substVal (Δ : Nat → Cls) (σ : Nat → Expr Srt) (ξ : Val) : Val :=
  fun n k => interp Δ (σ n) k ξ

theorem substVal_liftSub (Δ : Nat → Cls) (σ : Nat → Expr Srt) (ξ : Val) (c : Cls)
    (e : (k : Sk) → V k) :
    substVal (ncons c Δ) (Expr.liftSub σ) (ncons e ξ) = ncons e (substVal Δ σ ξ) := by
  funext n k
  cases n with
  | zero => rfl
  | succ n =>
      simp only [substVal, Expr.liftSub_succ, interp_rename, ncons_comp_succ, ncons_succ]

theorem interp_subst (M : Expr Srt) {Δ Δ' : Nat → Cls} {σ : Nat → Expr Srt}
    (hσ : ∀ n, cl Δ (σ n) = Δ' n) (k : Sk) (ξ : Val) :
    interp Δ (M.subst σ) k ξ = interp Δ' M k (substVal Δ σ ξ) := by
  induction M generalizing Δ Δ' σ k ξ with
  | var n => rfl
  | sort s => cases s <;> cases k <;> rfl
  | app F U ihF ihU =>
      simp only [Expr.subst, interp, cl_subst U hσ]
      cases cl Δ' U <;> simp only [ihF hσ, ihU hσ] <;> rfl
  | lam A b ihA ihb =>
      cases k with
      | star => rfl
      | arrO k =>
          simp only [Expr.subst, interp, cl_subst A hσ]
          rw [ihb (cl_liftSub hσ _), substVal_liftSub]
      | arr a k =>
          funext v
          simp only [Expr.subst, interp, cl_subst A hσ]
          rw [ihb (cl_liftSub hσ _), substVal_liftSub]
  | pi A B ihA ihB =>
      cases k with
      | arrO k => rfl
      | arr a k => rfl
      | star =>
          simp only [Expr.subst, interp, cl_subst A hσ]
          cases cl Δ' A with
          | kind a =>
              simp only [ihA hσ]
              congr 1
              funext v
              rw [ihB (cl_liftSub hσ _), substVal_liftSub]
          | constr a =>
              simp only [ihA hσ]
              congr 1
              funext v
              rw [ihB (cl_liftSub hσ _), substVal_liftSub]
          | obj =>
              simp only [ihA hσ]
              congr 1
              funext v
              rw [ihB (cl_liftSub hσ _), substVal_liftSub]

theorem substVal_single (Δ : Nat → Cls) (U : Expr Srt) (ξ : Val) :
    substVal Δ (Expr.single U) ξ = ncons (fun k => interp Δ U k ξ) ξ := by
  funext n k
  cases n <;> rfl

theorem interp_instantiate (b U : Expr Srt) (Δ : Nat → Cls) (k : Sk) (ξ : Val) :
    interp Δ (b.instantiate U) k ξ =
      interp (ncons (cl Δ U) Δ) b k (ncons (fun k => interp Δ U k ξ) ξ) := by
  rw [Expr.instantiate, interp_subst b (cl_single U), substVal_single]

/-! ### Well-classified expressions -/

/-- Admissible argument classes for a head of a given class. -/
def AppOK : Cls → Cls → Prop
  | .constr (.arr a _), c => c = .constr a
  | .constr (.arrO _), c => c = .obj
  | _, _ => True

/-- The classes of domains and codomains of products: kinds and types. -/
def PiOK (c : Cls) : Prop := c = .constr .star ∨ ∃ k, c = .kind k

/-- Well-classified expressions: applications respect the skeleton of their head, and products
are built from kinds and types. -/
def WC : (Nat → Cls) → Expr Srt → Prop
  | _, .var _ => True
  | _, .sort _ => True
  | Δ, .app F U => WC Δ F ∧ WC Δ U ∧ AppOK (cl Δ F) (cl Δ U)
  | Δ, .lam A b => WC Δ A ∧ WC (ncons (bindC (cl Δ A)) Δ) b
  | Δ, .pi A B => WC Δ A ∧ WC (ncons (bindC (cl Δ A)) Δ) B ∧ PiOK (cl Δ A) ∧
      PiOK (cl (ncons (bindC (cl Δ A)) Δ) B)

/-- The skeletons at which an expression of a given class is interpreted. -/
def RelC (c : Cls) (k : Sk) : Prop := c = .constr k ∨ (k = .star ∧ ∃ k', c = .kind k')

theorem RelC.of_piOK {c : Cls} (h : PiOK c) : RelC c .star := by
  rcases h with h | ⟨k, h⟩
  · exact .inl h
  · exact .inr ⟨rfl, k, h⟩

theorem RelC.constr_eq {a k : Sk} (h : RelC (.constr a) k) : k = a := by
  rcases h with h | ⟨_, _, h⟩
  · exact (Cls.constr.inj h).symm
  · cases h

theorem RelC.not_obj {k : Sk} (h : RelC .obj k) : False := by
  rcases h with h | ⟨_, _, h⟩ <;> cases h

/-- Two valuations agree on the relevant values of the variables. -/
def Agree (Δ : Nat → Cls) (ξ ξ' : Val) : Prop := ∀ n k, RelC (Δ n) k → ξ n k = ξ' n k

theorem Agree.ncons {Δ : Nat → Cls} {ξ ξ' : Val} (h : Agree Δ ξ ξ') (c : Cls)
    (e : (k : Sk) → V k) : Agree (ncons c Δ) (ncons e ξ) (ncons e ξ') := by
  intro n k hk
  cases n with
  | zero => rfl
  | succ n => exact h n k hk

theorem RelC.app {Δ : Nat → Cls} {F U : Expr Srt} {k : Sk} (h : RelC (cl Δ (.app F U)) k) :
    (∃ a, cl Δ F = .constr (.arr a k)) ∨ cl Δ F = .constr (.arrO k) := by
  rcases h with h | ⟨_, k', h⟩
  · exact appCls_eq_constr h
  · exact absurd h (appCls_ne_kind _ _)

theorem RelC.lam {Δ : Nat → Cls} {A b : Expr Srt} {k : Sk} (h : RelC (cl Δ (.lam A b)) k) :
    ∃ k₀, cl (ncons (bindC (cl Δ A)) Δ) b = .constr k₀ ∧ k = domSk (cl Δ A) k₀ := by
  rcases h with h | ⟨_, k', h⟩
  · exact lamCls_eq_constr h
  · exact absurd h (lamCls_ne_kind _ _ _)

theorem RelC.pi {Δ : Nat → Cls} {A B : Expr Srt} {k : Sk} (h : RelC (cl Δ (.pi A B)) k) :
    k = .star := by
  rcases h with h | ⟨h, _⟩
  · rcases piCls_star_or_kind (cl Δ A) (cl (ncons (bindC (cl Δ A)) Δ) B) with h' | ⟨k', h'⟩
    · simp only [cl] at h
      rw [h'] at h
      exact (Cls.constr.inj h).symm
    · simp only [cl] at h
      rw [h'] at h
      cases h
  · exact h

/-- **Irrelevant values do not matter.** -/
theorem interp_agree (M : Expr Srt) {Δ : Nat → Cls} {ξ ξ' : Val} {k : Sk} (hM : WC Δ M)
    (hξ : Agree Δ ξ ξ') (hk : RelC (cl Δ M) k) : interp Δ M k ξ = interp Δ M k ξ' := by
  induction M generalizing Δ ξ ξ' k with
  | var n => exact hξ n k hk
  | sort s => cases s <;> cases k <;> rfl
  | app F U ihF ihU =>
      obtain ⟨hF, hU, hok⟩ := hM
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl Δ U = .constr a := hok
        simp only [interp, hcU]
        rw [ihF hF hξ (.inl ha), ihU hU hξ (.inl hcU)]
      · rw [ha] at hok
        have hcU : cl Δ U = .obj := hok
        simp only [interp, hcU]
        exact ihF hF hξ (.inl ha)
  | lam A b ihA ihb =>
      obtain ⟨hA, hb⟩ := hM
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hb hb₀
        simp only [domSk, interp, hcA]
        funext v
        exact ihb hb (hξ.ncons _ _) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interp, hcA]
        exact ihb hb (hξ.ncons _ _) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interp, hcA]
        exact ihb hb (hξ.ncons _ _) (.inl hb₀)
  | pi A B ihA ihB =>
      obtain ⟨hA, hB, hpA, hpB⟩ := hM
      have := hk.pi
      subst this
      simp only [interp]
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hB hpB
        simp only [ihA hA hξ (.of_piOK (hcA ▸ hpA))]
        congr 1
        funext v
        exact ihB hB (hξ.ncons _ _) (.of_piOK hpB)
      · rw [hcA] at hB hpB
        simp only [ihA hA hξ (.of_piOK (hcA ▸ hpA))]
        congr 1
        funext v
        exact ihB hB (hξ.ncons _ _) (.of_piOK hpB)
      · rw [hcA] at hB hpB
        simp only [ihA hA hξ (.of_piOK (hcA ▸ hpA))]
        congr 1
        funext v
        exact ihB hB (hξ.ncons _ _) (.of_piOK hpB)

/-- A valuation is good when it assigns candidates to the relevant values. -/
def Good (Δ : Nat → Cls) (ξ : Val) : Prop := ∀ n k, RelC (Δ n) k → Cand k (ξ n k)

theorem good_canonVal (Δ : Nat → Cls) : Good Δ canonVal := fun _ k _ => cand_canon k

theorem Good.ncons_ext {Δ : Nat → Cls} {ξ : Val} (h : Good Δ ξ) {a : Sk} {v : V a}
    (hv : Cand a v) : Good (ncons (.constr a) Δ) (ncons (ext a v) ξ) := by
  intro n k hk
  cases n with
  | zero =>
      have := RelC.constr_eq hk
      subst this
      simpa using hv
  | succ n => exact h n k hk

theorem Good.ncons_obj {Δ : Nat → Cls} {ξ : Val} (h : Good Δ ξ) (e : (k : Sk) → V k) :
    Good (ncons .obj Δ) (ncons e ξ) := by
  intro n k hk
  cases n with
  | zero => exact hk.not_obj.elim
  | succ n => exact h n k hk

/-- **The interpretation lands in candidates.** -/
theorem interp_cand (M : Expr Srt) {Δ : Nat → Cls} {ξ : Val} {k : Sk} (hM : WC Δ M)
    (hξ : Good Δ ξ) (hk : RelC (cl Δ M) k) : Cand k (interp Δ M k ξ) := by
  induction M generalizing Δ ξ k with
  | var n => exact hξ n k hk
  | sort s =>
      cases s with
      | star =>
          rcases hk with h | ⟨rfl, _⟩
          · cases h
          · exact sat_snSet
      | box => exact hk.not_obj.elim
  | app F U ihF ihU =>
      obtain ⟨hF, hU, hok⟩ := hM
      rcases hk.app with ⟨a, ha⟩ | ha
      · rw [ha] at hok
        have hcU : cl Δ U = .constr a := hok
        simp only [interp, hcU]
        exact ihF hF hξ (.inl ha) _ (ihU hU hξ (.inl hcU))
      · rw [ha] at hok
        have hcU : cl Δ U = .obj := hok
        simp only [interp, hcU]
        exact ihF hF hξ (.inl ha)
  | lam A b ihA ihb =>
      obtain ⟨hA, hb⟩ := hM
      obtain ⟨k₀, hb₀, rfl⟩ := hk.lam
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hb hb₀
        simp only [domSk, interp, hcA]
        intro v hv
        exact ihb hb (hξ.ncons_ext hv) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interp, hcA]
        exact ihb hb (hξ.ncons_obj _) (.inl hb₀)
      · rw [hcA] at hb hb₀
        simp only [domSk, interp, hcA]
        exact ihb hb (hξ.ncons_obj _) (.inl hb₀)
  | pi A B ihA ihB =>
      obtain ⟨hA, hB, hpA, hpB⟩ := hM
      have := hk.pi
      subst this
      have hXA : Sat (interp Δ A .star ξ) := ihA hA hξ (.of_piOK hpA)
      simp only [interp]
      rcases hcA : cl Δ A with a | a | _
      · rw [hcA] at hB hpB
        exact sat_piSet hXA ⟨canon a, cand_canon a⟩
          (fun v hv => ihB hB (hξ.ncons_ext hv) (.of_piOK hpB))
      · rw [hcA] at hB hpB
        exact sat_piSet hXA ⟨(), trivial⟩
          (fun _ _ => ihB hB (hξ.ncons_obj _) (.of_piOK hpB))
      · rw [hcA] at hB hpB
        exact sat_piSet hXA ⟨(), trivial⟩
          (fun _ _ => ihB hB (hξ.ncons_obj _) (.of_piOK hpB))

end CoC

end PureTypeSystem
