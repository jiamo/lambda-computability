import Start.TypeClassSuperFieldExample

/-!
# Series V, round 4, run 2, part C: the measure at `sup (inst I ds)` under `SuperField`, and the
failure of normalization
(row M25-TYPECLASS-SUPER-FIELD)

Round 4 run 1 showed (`superEnv_sup_inst_step`) that the contraction of `sup (inst I ds)` to the
superclass field derivation of `I` keeps the constraint, so the Paterson size of the constraint
does not decrease, and the contractum can again be of the form `sup (inst J ds')`.

What does decrease is the size of the elaborated term: under `SuperField E I` the dictionary of
`I` is a finite record `recMk (sd :: ms)`, so its superclass field `sd` (with the context
dictionaries `ds` substituted) is strictly smaller than the projection of the substituted record.
This single number replaces the multiset of (Paterson size, field depth) pairs proposed earlier
for this step: the Paterson size is constant at the step (`superEnv_sup_inst_step`), and the field
depth is subsumed by the term size because dictionaries are finite terms.

* `dsize` — the size of an untyped term; `dsize_lift`, `dsize_le_substEnv`, `dsize_le_appsL`,
  `dsize_lt_recMk`;
* **`DEnt.superMeasure_lt`** — under `SuperField E I`, the contractum of `sup (inst I ds)` is
  derivable for the same constraint, is a reduct of the redex, and has strictly smaller size;
* `superEnv_superMeasure` — the test case `superEnv`;
* **`normalize_super_superField_fails`** — `DEnt.normalize_super` is **false** with
  `NormalSuperFields` replaced by `SuperField`, even inside `SuperInstFragment`
  (`loopEnv_superInstFragment`): in the good environment `loopEnv`
  (`instance Eq Base => Eq Base` with a dictionary that ignores its context, and `instance Ord Base`
  whose `Eq` field is derived by `inst EqLoop [sup (inst OrdLoop [])]`), every instance satisfies
  `SuperField`, `Eq Base` has the derivation `sup (inst OrdLoop [])`, and no normal derivation of
  `Eq Base` exists (`loopEnv_DEntN`).  The derivation of a context argument that does not occur in
  the dictionary term may itself be a redex `sup (inst I ds)` for the instance being defined.

So the normal-form route to coherence under `SuperField` is closed; coherence itself is not
refuted (every dictionary for `Eq Base` in `loopEnv` reduces to `eqBaseDict`).
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TypeClass

open SystemF

/-- The size of an untyped term. -/
def dsize : Lambda → ℕ
  | .var _ => 1
  | .app a b => dsize a + dsize b + 1
  | .lam t => dsize t + 1

theorem dsize_pos (t : Lambda) : 1 ≤ dsize t := by
  cases t <;> simp [dsize]

theorem dsize_lift (m : ℕ) (t : Lambda) : ∀ k, dsize (Lambda.lift m k t) = dsize t := by
  induction t with
  | var y => intro k; unfold Lambda.lift; split <;> rfl
  | app a b iha ihb => intro k; simp [Lambda.lift, dsize, iha, ihb]
  | lam t ih => intro k; simp [Lambda.lift, dsize, ih]

theorem dsize_le_substEnv (t : Lambda) : ∀ u : ℕ → Lambda, dsize t ≤ dsize (Lambda.substEnv u t) := by
  induction t with
  | var y => intro u; simpa [dsize, Lambda.substEnv] using dsize_pos (u y)
  | app a b iha ihb =>
    intro u; simp only [Lambda.substEnv, dsize]; have := iha u; have := ihb u; omega
  | lam t ih => intro u; simp only [Lambda.substEnv, dsize]; have := ih (Lambda.envCons u); omega

theorem dsize_le_appsL (us : List Lambda) : ∀ t : Lambda, dsize t ≤ dsize (appsL t us) := by
  induction us with
  | nil => intro t; simp [appsL]
  | cons u us ih => intro t; simp only [appsL]; have := ih (Lambda.app t u); simp only [dsize] at this; omega

/-- A field of a record is strictly smaller than the record. -/
theorem dsize_lt_recMk (sd : Lambda) (ms : List Lambda) : dsize sd < dsize (recMk (sd :: ms)) := by
  simp only [recMk, List.map_cons, appsL, dsize]
  have := dsize_le_appsL (ms.map (Lambda.lift 1 0)) (Lambda.app (Lambda.var 0) (Lambda.lift 1 0 sd))
  simp only [dsize, dsize_lift] at this
  omega

/-- **The measure decreases at `sup (inst I ds)` under `SuperField`.**  For an instance `I` of a
class with superclass `d`, well formed for its superclass, and dictionaries `ds` for its context,
the redex `sup (inst I ds)` (the superclass projection of the instance dictionary) and its
contractum, the superclass field `sd` of `I.dict` with `ds` substituted, satisfy: the contractum is
derivable for the same constraint, the redex reduces to it, and the size of the elaborated term
strictly decreases. -/
theorem DEnt.superMeasure_lt {E : Env} (hE : EnvGood E) {P : List Cstr} {n : ℕ} {I : Inst}
    (hSF : SuperField E I) {D : ClassDecl} {d : ℕ}
    (hc : E.classes[I.cls]? = some D) (hs : D.super = some d) {s : ℕ → Mty} {ds : List Lambda}
    (hds : ds.length = I.ctxt.length)
    (hall : ∀ (k : ℕ) (hk : k < ds.length) (hk' : k < I.ctxt.length),
      DEnt E P n ((I.ctxt[k]).subst s) (ds[k])) :
    ∃ sd, DEnt E P n ⟨d, msubst s I.head⟩ (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) ∧
      Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict))
        (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) ∧
      dsize (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) <
        dsize (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
          (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict)) := by
  obtain ⟨sd, ms, hdict, hlen, hsd⟩ := hSF D d hc hs
  have hsub : DEnt E P n (Cstr.subst s ⟨d, I.head⟩)
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) := by
    refine DEnt.subst hE (fun i C hi => ?_) hsd
    have hi' : i < I.ctxt.length := (List.getElem?_eq_some_iff.mp hi).1
    have hCi : I.ctxt[i] = C := (List.getElem?_eq_some_iff.mp hi).2
    have hid : i < ds.length := hds ▸ hi'
    have := hall i hid hi'
    rw [hCi] at this
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hid] using this
  have hred : Lambda.reduces (recProj (dictFields (dictTy E) D (msubst s I.head)).length 0
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) I.dict))
      (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd) := by
    rw [hdict, Lambda.substEnv_recMk, ← dictFields_length (dictTy E) D I.head, ← hlen]
    have := recProj_recMk ((sd :: ms).map (Lambda.substEnv fun k => ds.getD k (Lambda.var 0))) 0
      (by simp)
    simpa using this
  refine ⟨sd, hsub, hred, ?_⟩
  rw [hdict, Lambda.substEnv_recMk]
  have := dsize_lt_recMk (Lambda.substEnv (fun k => ds.getD k (Lambda.var 0)) sd)
    (ms.map (Lambda.substEnv fun k => ds.getD k (Lambda.var 0)))
  simp only [List.map_cons, recProj, dsize] at this ⊢
  omega

/-- The test case `superEnv`: the contraction of `sup (inst Ord₂Base [])` to
`sup (inst OrdBase [])` (both for `Eq Base`, `superEnv_sup_inst_step`) strictly decreases the
size of the elaborated term. -/
theorem superEnv_superMeasure :
    dsize ord2Field < dsize (recProj 2 0 ord2BaseDict) ∧ dsize ordBaseDict < dsize ord2BaseDict := by
  decide

/-! ### `DEnt.normalize_super` fails under `SuperField` alone -/

/-- `instance Eq Base => Eq Base`, whose dictionary ignores its context. -/
def instEqLoop : Inst := ⟨0, Mty.base, [⟨0, Mty.base⟩], eqBaseDict⟩

/-- `instance Ord Base` with the dictionary `ordBaseDict` (its `Eq` field is `eqBaseDict`). -/
def instOrdLoop : Inst := ⟨1, Mty.base, [], ordBaseDict⟩

/-- The environment `Eq`, `Ord <: Eq` with the two instances above. -/
def loopEnv : Env := ⟨[eqDecl, ordDecl], [instEqLoop, instOrdLoop]⟩

theorem dictTyF_classes {E E' : Env} (h : E.classes = E'.classes) :
    ∀ n c τ, dictTyF E n c τ = dictTyF E' n c τ := by
  intro n
  induction n with
  | zero => intro c τ; rfl
  | succ n ih =>
    intro c τ
    have hf : dictTyF E n = dictTyF E' n := by funext c τ; exact ih c τ
    simp only [dictTyF, h, hf]

theorem loopEnv_dictTy : dictTy loopEnv = dictTy exampleEnv := by
  funext c τ
  exact dictTyF_classes (E := loopEnv) (E' := exampleEnv) rfl _ _ _

theorem loopEnv_ok : EnvOK loopEnv where
  super_lt := exampleEnv_ok.super_lt
  methods_mono := exampleEnv_ok.methods_mono

theorem loopEnv_good : EnvGood loopEnv where
  toEnvOK := loopEnv_ok
  insts_ok := by
    intro I hI
    simp only [loopEnv, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · rw [loopEnv_dictTy]; exact typing_eqBaseDict _
    · rw [loopEnv_dictTy]; exact typing_ordBaseDict

theorem loopEnv_ordBase (P : List Cstr) (n : ℕ) : DEnt loopEnv P n ⟨1, Mty.base⟩ ordBaseDict := by
  have h := DEnt.inst (E := loopEnv) (P := P) (n := n) (I := instOrdLoop)
    (s := fun _ => Mty.base) (ds := []) (by simp [loopEnv]) rfl
    (fun k hk _ => absurd hk (Nat.not_lt_zero k))
  rw [show instOrdLoop.dict = ordBaseDict from rfl, substEnv_nil_closed_ord] at h
  simpa [instOrdLoop, msubst] using h

/-- The superclass projection of the `Ord Base` dictionary derives `Eq Base`. -/
theorem loopEnv_supInst (P : List Cstr) (n : ℕ) :
    DEnt loopEnv P n ⟨0, Mty.base⟩ (recProj 2 0 ordBaseDict) :=
  DEnt.sup (E := loopEnv) (c := 1) (D := ordDecl) (by simp [loopEnv]) rfl (loopEnv_ordBase P n)

/-- Every instance of `loopEnv` is well formed for its superclass: the `Eq` field `eqBaseDict` of
`Ord Base` is derived by `inst EqLoop [sup (inst OrdLoop [])]`. -/
theorem loopEnv_superField : ∀ I ∈ loopEnv.insts, SuperField loopEnv I := by
  intro I hI D d hc hs
  simp only [loopEnv, List.mem_cons, List.not_mem_nil, or_false] at hI
  rcases hI with rfl | rfl
  · simp [loopEnv, instEqLoop, eqDecl] at hc; subst hc; simp at hs
  · simp [loopEnv, instOrdLoop, ordDecl] at hc
    subst hc
    simp only [Option.some.injEq] at hs
    subst hs
    refine ⟨eqBaseDict, [Lambda.lam (Lambda.lam (Lambda.var 1))], rfl, by simp [dictFields], ?_⟩
    have h := DEnt.inst (E := loopEnv) (P := instOrdLoop.ctxt) (n := 0) (I := instEqLoop)
      (s := fun _ => Mty.base) (ds := [recProj 2 0 ordBaseDict]) (by simp [loopEnv]) rfl
      (fun k hk _ => by
        obtain rfl : k = 0 := by simp at hk; omega
        simpa [instEqLoop, Cstr.subst, msubst] using loopEnv_supInst instOrdLoop.ctxt 0)
    have hc : Lambda.substEnv (fun k => [recProj 2 0 ordBaseDict].getD k (Lambda.var 0)) eqBaseDict
        = eqBaseDict := by
      simp [eqBaseDict, recMk, appsL, Lambda.substEnv, Lambda.lift]
    rw [show instEqLoop.dict = eqBaseDict from rfl, hc] at h
    simpa [instEqLoop, instOrdLoop, msubst] using h

/-- In `loopEnv` without hypotheses no normal derivation has the constraint `Eq Base`, and every
normal derivation is an instance node. -/
theorem loopEnv_DEntN {n : ℕ} {b : Bool} {C : Cstr} {d : Lambda}
    (h : DEntN loopEnv [] n b C d) : C ≠ ⟨0, Mty.base⟩ ∧ b = true := by
  induction h with
  | hyp hi => simp at hi
  | sup _ _ _ ih => exact absurd ih.2 (by simp)
  | @inst I s ds bs hI hds _ ih =>
    refine ⟨?_, rfl⟩
    simp only [loopEnv, List.mem_cons, List.not_mem_nil, or_false] at hI
    rcases hI with rfl | rfl
    · intro _
      have hk : 0 < ds.length := by rw [hds]; simp [instEqLoop]
      exact (ih 0 hk (by simp [instEqLoop])).1 (by simp [instEqLoop, Cstr.subst, msubst])
    · simp [instOrdLoop, msubst]

/-- `loopEnv` lies in the fragment of `coherence_unannotated_superInst` (no overlap; no hypotheses),
so normalization fails inside the target fragment. -/
theorem loopEnv_superInstFragment : SuperInstFragment loopEnv [] where
  env_ok := loopEnv_ok
  no_overlap := by
    intro I hI I' hI' s s' hcls _
    simp only [loopEnv, List.mem_cons, List.not_mem_nil, or_false] at hI hI'
    rcases hI with rfl | rfl <;> rcases hI' with rfl | rfl <;>
      simp_all [instEqLoop, instOrdLoop, Cstr.subst, msubst]
  closure_rigid := by intro C hC; simp at hC
  closure_unique := by intro i j Ci Cj c hi; simp at hi

/-- **`DEnt.normalize_super` is false under `SuperField` alone**, even in the fragment
`SuperInstFragment` of `coherence_unannotated_superInst`.  `loopEnv` is a good environment in that
fragment, all of whose instances are well formed for their superclass, the constraint
`Eq Base` has a dictionary derivation (`sup (inst OrdLoop [])`), but it has no normal derivation at
all, so no reduct of that dictionary has one.  (The normal-form route to coherence is closed;
coherence itself is not refuted: every dictionary for `Eq Base` here reduces to `eqBaseDict`.) -/
theorem normalize_super_superField_fails :
    ¬ ∀ (E : Env) (P : List Cstr), EnvGood E → SuperInstFragment E P →
      (∀ I ∈ E.insts, SuperField E I) →
      ∀ (n : ℕ) (C : Cstr) (d : Lambda), DEnt E P n C d →
        ∃ b d', DEntN E P n b C d' ∧ Lambda.reduces d d' := by
  intro h
  obtain ⟨b, d', hd', -⟩ := h loopEnv [] loopEnv_good loopEnv_superInstFragment loopEnv_superField
    0 _ _ (loopEnv_supInst [] 0)
  exact (loopEnv_DEntN hd').1 rfl

end TypeClass
