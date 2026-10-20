import Start.MinskyUndecidable

/-!
# Round 11, part C: codes for F<: types and goals, and non-computability of subtyping

Following Mathlib's treatment of `Nat.Partrec.Code`, F<: types get a bijection with `ℕ`
(`top ↦ 0`, `var i ↦ 2i+1`, `all S T ↦ 2⟨S,T⟩+2`), hence `Denumerable FsubGhelli.Ty` and
`Primcodable` with no decoder obligation; goals are coded through `List Ty × Ty × Ty`.  The
three constructors of `Ty` and `Goal.mk` are primitive recursive.

* `FsubCode.sub_not_computable_of_enc_computable` — **subtyping in full F<: is not computable**,
  given that the encoding `m ↦ FsubPierce.enc M_u (3 ^ m) 0` is computable (through
  `universal_dom_iff_sub` and `universal_dom_undecidable`).

The computability of that encoding is the first missing lemma (`enc_M_u_computable`, see
`docs/goal/evidence/M25-FSUB-SUB-NONCOMPUTABLE.md`).
-/

set_option autoImplicit false

namespace FsubCode

open FsubGhelli

/-- The code of an F<: type. -/
def encodeTy : Ty → ℕ
  | .top => 0
  | .var i => 2 * i + 1
  | .all S T => 2 * Nat.pair (encodeTy S) (encodeTy T) + 2

/-- The decoding of an F<: type. -/
def decodeTy (n : ℕ) : Ty :=
  if h0 : n = 0 then .top
  else if n % 2 = 1 then .var (n / 2)
  else
    have h1 : (Nat.unpair ((n - 2) / 2)).1 < n :=
      lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)
    have h2 : (Nat.unpair ((n - 2) / 2)).2 < n :=
      lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)
    .all (decodeTy (Nat.unpair ((n - 2) / 2)).1) (decodeTy (Nat.unpair ((n - 2) / 2)).2)
termination_by n

theorem decode_encodeTy : ∀ T : Ty, decodeTy (encodeTy T) = T
  | .top => by simp [encodeTy, decodeTy]
  | .var i => by
      rw [encodeTy, decodeTy, dif_neg (by omega), if_pos (by omega)]
      congr 1; omega
  | .all S T => by
      rw [encodeTy, decodeTy, dif_neg (by omega), if_neg (by omega)]
      have : (2 * Nat.pair (encodeTy S) (encodeTy T) + 2 - 2) / 2 =
          Nat.pair (encodeTy S) (encodeTy T) := by omega
      simp only [this, Nat.unpair_pair, decode_encodeTy S, decode_encodeTy T]

theorem encode_decodeTy (n : ℕ) : encodeTy (decodeTy n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [decodeTy]
    split_ifs with h0 h1
    · subst h0; rfl
    · simp only [encodeTy]; omega
    · have h1' : (Nat.unpair ((n - 2) / 2)).1 < n :=
        lt_of_le_of_lt (Nat.unpair_left_le _) (by omega)
      have h2' : (Nat.unpair ((n - 2) / 2)).2 < n :=
        lt_of_le_of_lt (Nat.unpair_right_le _) (by omega)
      simp only [encodeTy, ih _ h1', ih _ h2', Nat.pair_unpair]
      omega

/-- The bijection between F<: types and `ℕ`. -/
def tyEquiv : Ty ≃ ℕ where
  toFun := encodeTy
  invFun := decodeTy
  left_inv := decode_encodeTy
  right_inv := encode_decodeTy

instance : Denumerable Ty := Denumerable.mk' tyEquiv

instance : Primcodable Ty := Primcodable.ofDenumerable Ty

theorem encode_ty (T : Ty) : Encodable.encode T = encodeTy T := rfl

theorem ofNat_ty (n : ℕ) : Denumerable.ofNat Ty n = decodeTy n := rfl

/-- `top` is primitive recursive (a constant). -/
theorem primrec_top : Primrec (fun _ : ℕ => Ty.top) := Primrec.const _

/-- **`var` is primitive recursive.** -/
theorem primrec_var : Primrec Ty.var := by
  have h : Primrec (fun i : ℕ => Denumerable.ofNat Ty (2 * i + 1)) :=
    (Primrec.ofNat Ty).comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
        (Primrec.const 1))
  refine h.of_eq fun i => ?_
  rw [ofNat_ty, ← decode_encodeTy (.var i)]
  rfl

/-- **`all` is primitive recursive.** -/
theorem primrec₂_all : Primrec₂ Ty.all := by
  have h : Primrec₂ (fun S T : Ty => Denumerable.ofNat Ty
      (2 * Nat.pair (Encodable.encode S) (Encodable.encode T) + 2)) :=
    (Primrec.ofNat Ty).comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
            (Primrec.encode.comp Primrec.snd)))
        (Primrec.const 2))
  refine h.of_eq fun S T => ?_
  rw [ofNat_ty, encode_ty, encode_ty, ← decode_encodeTy (.all S T)]
  rfl

/-- Goals as triples. -/
def goalEquiv : Goal ≃ List Ty × Ty × Ty where
  toFun g := (g.ctx, g.lhs, g.rhs)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Goal := Primcodable.ofEquiv _ goalEquiv

/-- **`Goal.mk` is primitive recursive** (as a function of the triple). -/
theorem primrec_goal_mk : Primrec (fun p : List Ty × Ty × Ty => Goal.mk p.1 p.2.1 p.2.2) :=
  (Primrec.of_equiv_symm (e := goalEquiv)).of_eq fun _ => rfl


/-! ### The encoding is primitive recursive -/

open FsubPierce in
/-- A frame whose arguments are variables, as a fold over the indices. -/
theorem frameD_range' (h : ℕ → ℕ) (q : ℕ) : ∀ (m s : ℕ),
    frameD s ((List.range' s m).map (fun k => Ty.var (h k))) (Ty.var q) =
      List.foldr (fun k acc => Ty.all (Ty.var (h k + k)) acc) (neg (Ty.var (q + s + m)))
        (List.range' s m)
  | 0, s => by simp [frameD, Ty.lift]
  | m + 1, s => by
      rw [List.range'_succ, List.map_cons, frameD, frameD_range' h q m (s + 1)]
      simp only [List.foldr_cons, Ty.lift, Nat.not_lt_zero, if_false]
      congr 3
      congr 1
      omega

open FsubPierce in
theorem chain_iterate (n s : ℕ) (v : ℕ) :
    chain n s v = (fun L => succT n s (.var 0) :: L)^[v] [zeroT n] := by
  induction v with
  | zero => rfl
  | succ v ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem primrec_neg : Primrec neg :=
  primrec₂_all.comp Primrec.id (Primrec.const (Ty.var 0))

/-- **The encoding of a machine with counters `(a, 0)` is primitive recursive in `a`.** -/
theorem primrec_enc (M : CM) : Primrec (fun a : ℕ => FsubPierce.enc M a 0) := by
  -- the context
  have hchain : Primrec (fun a : ℕ => FsubPierce.chain M.length 0 a) := by
    have : Primrec (fun a : ℕ =>
        (fun L => FsubPierce.succT M.length 0 (.var 0) :: L)^[a] [FsubPierce.zeroT M.length]) :=
      Primrec.nat_iterate Primrec.id (Primrec.const _)
        (Primrec.list_cons.comp (Primrec.const _) Primrec.snd).to₂
    exact this.of_eq fun a => (chain_iterate _ _ a).symm
  have hctx : Primrec (fun a : ℕ => FsubPierce.initCtx M a 0) :=
    Primrec.list_append.comp
      (Primrec.list_append.comp hchain (Primrec.const _)) (Primrec.const _)
  -- the subject
  have hlhs : Primrec (fun a : ℕ => Ty.var (0 + (a + 0 + 2))) :=
    primrec_var.comp (Primrec.nat_add.comp (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 0))
        (Primrec.const 2)))
  -- the slots
  have hslots : Primrec₂ (fun (a k : ℕ) => FsubPierce.initSlots M a 0 k) := by
    unfold FsubPierce.initSlots
    refine Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0) ?_
    refine Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1))
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)) ?_
    refine Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.const _))
      (Primrec.nat_add.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 4))
        (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 0))
          (Primrec.const 2)))
      (Primrec.nat_add.comp (Primrec.const _)
        (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 0))
          (Primrec.const 2)))
  -- the frame
  have hrhs : Primrec (fun a : ℕ =>
      List.foldr (fun k acc => Ty.all (Ty.var (FsubPierce.initSlots M a 0 k + k)) acc)
        (neg (Ty.var ((M.length + 1 + (a + 0 + 2)) + 0 + (M.length + 6))))
        (List.range' 0 (M.length + 6))) := by
    have hq : Primrec (fun a : ℕ => (M.length + 1 + (a + 0 + 2)) + 0 + (M.length + 6)) :=
      (Primrec.nat_add.comp Primrec.id (Primrec.const (2 * M.length + 9))).of_eq
        fun a => by simp only [id]; omega
    have hh : Primrec₂ (fun (a : ℕ) (p : ℕ × Ty) =>
        Ty.all (Ty.var (FsubPierce.initSlots M a 0 p.1 + p.1)) p.2) :=
      (primrec₂_all.comp
        (primrec_var.comp (Primrec.nat_add.comp
          (hslots.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂
    exact Primrec.list_foldr (f := fun _ : ℕ => List.range' 0 (M.length + 6))
      (g := fun a : ℕ => neg (Ty.var ((M.length + 1 + (a + 0 + 2)) + 0 + (M.length + 6))))
      (Primrec.const _) (primrec_neg.comp (primrec_var.comp hq)) hh
  have hgoal := primrec_goal_mk.comp (Primrec.pair hctx (Primrec.pair hlhs hrhs))
  refine hgoal.of_eq fun a => ?_
  simp only [FsubPierce.enc, FsubPierce.dispGoal, FsubPierce.al]
  rw [List.range_eq_range', ← frameD_range']

/-- **The encoding of the halting problem of `M_u` is computable.** -/
theorem enc_M_u_computable :
    Computable (fun m : ℕ => FsubPierce.enc Minsky.Universal.M_u (3 ^ m) 0) := by
  have hpow : Primrec (fun m : ℕ => 3 ^ m) := by
    have : Primrec (fun m : ℕ => (fun x => 3 * x)^[m] 1) :=
      Primrec.nat_iterate Primrec.id (Primrec.const 1)
        (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd).to₂
    refine this.of_eq fun m => ?_
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, pow_succ, mul_comm]
  exact ((primrec_enc _).comp hpow).to_comp

/-- **Subtyping in full F<: is not computable, given a computable encoding** of the halting
problem of the fixed machine `M_u`. -/
theorem sub_not_computable_of_enc_computable
    (henc : Computable (fun m : ℕ => FsubPierce.enc Minsky.Universal.M_u (3 ^ m) 0)) :
    ¬ ComputablePred (fun g : Goal => Sub g) := by
  intro hsub
  apply Minsky.Universal.universal_dom_undecidable Minsky.Universal.uCode_spec
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.1 hsub
  refine ComputablePred.computable_iff.2
    ⟨fun m => f (FsubPierce.enc Minsky.Universal.M_u (3 ^ m) 0), hf.comp henc, ?_⟩
  funext m
  have := congrFun hfe (FsubPierce.enc Minsky.Universal.M_u (3 ^ m) 0)
  rw [← this]
  exact propext (Minsky.Universal.universal_dom_iff_sub m)

/-- **Subtyping in full F<: is not computable.** -/
theorem sub_not_computable : ¬ ComputablePred (fun g : Goal => Sub g) :=
  sub_not_computable_of_enc_computable enc_M_u_computable

end FsubCode
