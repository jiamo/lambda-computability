/-
Model equivalence for multi-argument functions and for arbitrary encoded data.

The capstone `lambdaComputable_iff_partrec` is stated for partial functions `ℕ →. ℕ` fed to a
lambda term as a single Church numeral.  Two natural extensions are proved here.

* **Several arguments.**  `lambdaComputable2_iff_partrec₂` — a binary partial function is
  computed by a lambda term *in curried form* (`F ⌜n⌝ ⌜m⌝ ↠ ⌜k⌝`) exactly when it is partial
  recursive.  Both directions are explicit term constructions: `Lambda.uncurryTerm` turns a
  curried term into one acting on `Nat.pair`-coded inputs, `Lambda.curryTerm` does the converse.
* **Arbitrary encoded data.**  `lambdaComputableEnc_iff_partrec` — for any `Primcodable` domain
  and codomain, feeding a term the numeral of the encoded input and reading off the numeral of the
  encoded output defines exactly the partial recursive functions.  Machine computability is
  transported the same way (`tm2ComputableEnc_iff_partrec`), so all three models agree on every
  encoded datatype, not just on `ℕ`.
-/

import Start.TM2Capstone

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Lambda

/-- A term reducing both to `u` and to a Church numeral makes `u` reduce to that numeral. -/
theorem reduces_church_of_reduces {t u : Lambda} {k : ℕ} (h1 : Lambda.reduces t u)
    (h2 : Lambda.reduces t (Lambda.church k)) : Lambda.reduces u (Lambda.church k) := by
  obtain ⟨w, hw1, hw2⟩ := Lambda.confluence_theorem h1 h2
  rwa [← Lambda.reduces_normal_eq (Lambda.church_normal k) hw2] at hw1

/-! ## Currying and uncurrying lambda terms -/

/-- From a term expecting two curried numerals, a term expecting the `Nat.pair` code of the two:
`uncurryTerm F = λz. F (fst z) (snd z)`.  `F` is lifted so that it may have free variables. -/
def uncurryTerm (F : Lambda) : Lambda :=
  Lambda.lam (Lambda.app
    (Lambda.app (Lambda.lift 1 0 F) (Lambda.app Lambda.unpairLeft_impl (Lambda.var 0)))
    (Lambda.app Lambda.unpairRight_impl (Lambda.var 0)))

/-- From a closed term expecting the `Nat.pair` code of two numbers, a term expecting them
curried: `curryTerm G = λx y. G (pair x y)`. -/
def curryTerm (G : Lambda) : Lambda :=
  Lambda.lam (Lambda.lam (Lambda.app G
    (Lambda.app (Lambda.app Lambda.natPair' (Lambda.var 1)) (Lambda.var 0))))

theorem uncurryTerm_app_reduces (F : Lambda) (p : ℕ) :
    Lambda.reduces (Lambda.app (uncurryTerm F) (Lambda.church p))
      (Lambda.app (Lambda.app F (Lambda.church p.unpair.1)) (Lambda.church p.unpair.2)) := by
  have hsubst : Lambda.subst (Lambda.church p) 0
      (Lambda.app
        (Lambda.app (Lambda.lift 1 0 F) (Lambda.app Lambda.unpairLeft_impl (Lambda.var 0)))
        (Lambda.app Lambda.unpairRight_impl (Lambda.var 0))) =
      Lambda.app (Lambda.app F (Lambda.app Lambda.unpairLeft_impl (Lambda.church p)))
        (Lambda.app Lambda.unpairRight_impl (Lambda.church p)) := by
    simp [Lambda.subst, Lambda.subst_lift F (Lambda.church p) 0,
      Lambda.unpairLeft_impl_closed _ _, Lambda.unpairRight_impl_closed _ _]
  have hbeta : Lambda.reduces (Lambda.app (uncurryTerm F) (Lambda.church p))
      (Lambda.app (Lambda.app F (Lambda.app Lambda.unpairLeft_impl (Lambda.church p)))
        (Lambda.app Lambda.unpairRight_impl (Lambda.church p))) := by
    rw [uncurryTerm, ← hsubst]
    exact Lambda.beta_reduces
  refine Lambda.reduces_trans hbeta ?_
  refine Lambda.reduces_trans
    (Lambda.reduces_app_left (t2 := Lambda.app Lambda.unpairRight_impl (Lambda.church p))
      (Lambda.reduces_app_right (t1 := F) (Lambda.unpairLeft_works p))) ?_
  exact Lambda.reduces_app_right (Lambda.unpairRight_works p)

theorem curryTerm_app_reduces {G : Lambda} (hG : Lambda.IsClosed G) (n m : ℕ) :
    Lambda.reduces (Lambda.app (Lambda.app (curryTerm G) (Lambda.church n)) (Lambda.church m))
      (Lambda.app G (Lambda.church (Nat.pair n m))) := by
  have hstep1 : Lambda.reduces (Lambda.app (curryTerm G) (Lambda.church n))
      (Lambda.lam (Lambda.app G
        (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.var 0)))) := by
    have hsubst : Lambda.subst (Lambda.church n) 0
        (Lambda.lam (Lambda.app G
          (Lambda.app (Lambda.app Lambda.natPair' (Lambda.var 1)) (Lambda.var 0)))) =
        Lambda.lam (Lambda.app G
          (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.var 0))) := by
      simp [Lambda.subst, Lambda.lift_closed (Lambda.church_closed n), hG _ _,
        Lambda.natPair'_closed _ _]
    rw [curryTerm, ← hsubst]
    exact Lambda.beta_reduces
  have hstep2 : Lambda.reduces
      (Lambda.app (Lambda.lam (Lambda.app G
        (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n)) (Lambda.var 0))))
        (Lambda.church m))
      (Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
        (Lambda.church m))) := by
    have hsubst : Lambda.subst (Lambda.church m) 0
        (Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
          (Lambda.var 0))) =
        Lambda.app G (Lambda.app (Lambda.app Lambda.natPair' (Lambda.church n))
          (Lambda.church m)) := by
      simp [Lambda.subst, hG _ _, Lambda.natPair'_closed _ _, Lambda.church_closed n _ _]
    rw [← hsubst]
    exact Lambda.beta_reduces
  refine Lambda.reduces_trans (Lambda.reduces_app_left hstep1) ?_
  exact Lambda.reduces_trans hstep2 (Lambda.reduces_app_right (Lambda.natPair'_works n m))

end Lambda

/-! ## Binary functions -/

/-- A curried lambda-computable binary function is lambda-computable on paired inputs. -/
theorem lambdaComputable_unpaired_of_lambdaComputable2 {f : ℕ → ℕ →. ℕ}
    (hf : LambdaComputable2 f) : LambdaComputable (Nat.unpaired f) := by
  obtain ⟨F, hF⟩ := hf
  refine ⟨Lambda.uncurryTerm F, fun p k => ⟨fun hp => ?_, fun hred => ?_⟩⟩
  · exact Lambda.reduces_trans (Lambda.uncurryTerm_app_reduces F p) ((hF _ _ k).1 hp)
  · exact (hF _ _ k).2
      (Lambda.reduces_church_of_reduces (Lambda.uncurryTerm_app_reduces F p) hred)

/-- **Lambda-definability in curried form is partial recursiveness**, forward direction. -/
theorem partrec₂_of_lambdaComputable2 {f : ℕ → ℕ →. ℕ} (hf : LambdaComputable2 f) :
    Partrec₂ f :=
  Partrec₂.unpaired.1 (lambdaComputable_iff_partrec.1
    (lambdaComputable_unpaired_of_lambdaComputable2 hf))

/-- **Lambda-definability in curried form is partial recursiveness**, converse direction. -/
theorem lambdaComputable2_of_partrec₂ {f : ℕ → ℕ →. ℕ} (hf : Partrec₂ f) :
    LambdaComputable2 f := by
  obtain ⟨G, hGclosed, hG⟩ :=
    lambdaComputable_of_partrec_closed (Partrec₂.unpaired.2 hf)
  refine ⟨Lambda.curryTerm G, fun n m k => ⟨fun hnm => ?_, fun hred => ?_⟩⟩
  · have hpair : Nat.unpaired f (Nat.pair n m) = Part.some k := by
      simpa [Nat.unpaired] using hnm
    exact Lambda.reduces_trans (Lambda.curryTerm_app_reduces hGclosed n m)
      ((hG _ k).1 hpair)
  · have hval := (hG (Nat.pair n m) k).2
      (Lambda.reduces_church_of_reduces (Lambda.curryTerm_app_reduces hGclosed n m) hred)
    simpa [Nat.unpaired] using hval

/-- **Model equivalence for binary functions.**  A binary partial function on the naturals is
computed by a lambda term in curried form exactly when it is partial recursive. -/
theorem lambdaComputable2_iff_partrec₂ {f : ℕ → ℕ →. ℕ} :
    LambdaComputable2 f ↔ Partrec₂ f :=
  ⟨partrec₂_of_lambdaComputable2, lambdaComputable2_of_partrec₂⟩

/-- A binary partial function is lambda-definable in curried form exactly when it is machine
computable on paired inputs. -/
theorem lambdaComputable2_iff_tm2Computable {f : ℕ → ℕ →. ℕ} :
    LambdaComputable2 f ↔ TM2Partrec.TM2ComputableNat (Nat.unpaired f) :=
  lambdaComputable2_iff_partrec₂.trans
    (Partrec₂.unpaired.symm.trans TM2Partrec.tm2Computable_iff_partrec.symm)

/-! ## Arbitrary encoded data -/

/-- Lambda-definability of a partial function between encoded datatypes: the term is fed the
numeral of the code of its input and must reduce to the numeral of the code of its output. -/
def LambdaComputableEnc {α σ : Type} [Primcodable α] [Primcodable σ] (f : α →. σ) : Prop :=
  LambdaComputable fun n : ℕ =>
    Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode

/-- Machine computability of a partial function between encoded datatypes. -/
def TM2ComputableEnc {α σ : Type} [Primcodable α] [Primcodable σ] (f : α →. σ) : Prop :=
  TM2Partrec.TM2ComputableNat fun n : ℕ =>
    Part.bind (Encodable.decode (α := α) n) fun a => (f a).map Encodable.encode

/-- **Model equivalence for arbitrary encoded data.**  A partial function between `Primcodable`
types is lambda-definable through its encoding exactly when it is partial recursive. -/
theorem lambdaComputableEnc_iff_partrec {α σ : Type} [Primcodable α] [Primcodable σ]
    {f : α →. σ} : LambdaComputableEnc f ↔ Partrec f :=
  lambdaComputable_iff_partrec.trans Partrec.nat_iff

/-- The machine model agrees with it. -/
theorem tm2ComputableEnc_iff_partrec {α σ : Type} [Primcodable α] [Primcodable σ]
    {f : α →. σ} : TM2ComputableEnc f ↔ Partrec f :=
  TM2Partrec.tm2Computable_iff_partrec.trans Partrec.nat_iff

/-- **All three models agree on every encoded datatype.** -/
theorem lambdaComputableEnc_iff_tm2ComputableEnc {α σ : Type} [Primcodable α] [Primcodable σ]
    {f : α →. σ} : LambdaComputableEnc f ↔ TM2ComputableEnc f :=
  lambdaComputableEnc_iff_partrec.trans tm2ComputableEnc_iff_partrec.symm

/-- The total-function form: a function between encoded datatypes is lambda-definable through its
encoding exactly when it is computable. -/
theorem lambdaComputableEnc_iff_computable {α σ : Type} [Primcodable α] [Primcodable σ]
    {f : α → σ} : LambdaComputableEnc (fun a => Part.some (f a)) ↔ Computable f :=
  lambdaComputableEnc_iff_partrec

/-- Non-vacuity: a function on lists of naturals is lambda-definable through the encoding. -/
example : LambdaComputableEnc (fun l : List ℕ => Part.some l.length) :=
  lambdaComputableEnc_iff_computable.2 Computable.list_length

end
