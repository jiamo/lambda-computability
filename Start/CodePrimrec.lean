/-
Primitive recursiveness of the code-level operations: the arithmetized
decoder `Lambda.decode_code`, code-level lifting and substitution via the
explicit closure format `ECF`, and the primed code-step `Lambda.code_step'`.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Tactics
import Start.Syntax
import Start.Reduction
import Start.Church
import Start.Encoding
import Start.CodeOps
import Start.Computability


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
If `f` is Lambda-computable, and `Lambda.eval` is correct, then `f` is computed by
`Lambda.compute_fun`.
-/
theorem LambdaComputable_imp_compute_fun_aux
  (h_eval_correct : ∀ t n, Lambda.reduces t (Lambda.church n) ↔ Lambda.eval (Lambda.encode t) =
      Part.some (Lambda.church_code n))
  {f : ℕ →. ℕ} (h : LambdaComputable f) :
  ∃ c, ∀ n, Lambda.compute_fun c n = f n := by
  obtain ⟨F, hF⟩ := h
  refine ⟨Lambda.encode F, fun n => ?_⟩
  have hE : Lambda.app_code (Lambda.encode F) (Lambda.church_code n)
      = Lambda.encode (Lambda.app F (Lambda.church n)) := by
    rw [← Lambda.encode_church_eq_church_code]
    rfl
  unfold Lambda.compute_fun
  rw [hE]
  refine Part.ext fun m => ⟨fun hm => ?_, fun hm => ?_⟩
  · rw [Part.mem_bind_iff] at hm
    obtain ⟨c, hc, hcm⟩ := hm
    have hcm' : Lambda.unchurch_code c = some m := by simpa using hcm
    have hc2 : c = Lambda.church_code m := (Lambda.unchurch_code_eq_some_iff c m).mp hcm'
    have heval : Lambda.eval (Lambda.encode (Lambda.app F (Lambda.church n)))
        = Part.some (Lambda.church_code m) := by
      rw [Part.eq_some_iff, ← hc2]
      exact hc
    have hred := (h_eval_correct (Lambda.app F (Lambda.church n)) m).mpr heval
    exact Part.eq_some_iff.mp ((hF n m).mpr hred)
  · have hred := (hF n m).mp (Part.eq_some_iff.mpr hm)
    have heval := (h_eval_correct (Lambda.app F (Lambda.church n)) m).mp hred
    rw [Part.mem_bind_iff]
    refine ⟨Lambda.church_code m, by rw [heval]; exact Part.mem_some _, ?_⟩
    simp [Lambda.unchurch_code_correct m]


/-
Checking the definition of Primcodable and Primrec to understand how to instantiate Primcodable for
Lambda.
-/

/-
Checking the definition of Option.encodable.
-/

/-
Defining the base case for `decode_code` (variables) and proving it is primitive recursive.
-/
def Lambda.decode_code_case0 (m : ℕ) : ℕ := (Nat.pair 0 m).succ

theorem Lambda.decode_code_case0_primrec : Primrec Lambda.decode_code_case0 := by
  unfold decode_code_case0;
  -- The function $m \mapsto \text{succ}(\text{pair}(0, m))$ is primitive recursive because it is a
  -- composition of primitive recursive functions.
  have h_succ_pair : Primrec (fun m => Nat.pair 0 m) := by
    -- The function `Nat.pair 0` is primitive recursive because it is a composition of primitive
    -- recursive functions: `Nat.pair` and `Nat.zero`.
    have h_pair : Primrec₂ Nat.pair := by
      exact Primrec₂.natPair;
    exact h_pair.comp ( Primrec.const 0 ) ( Primrec.id );
  exact Primrec.succ.comp h_succ_pair

/-
Checking the definition of Nat.Partrec.
-/

/-
Checking if Primrec.list_getD exists.
-/

/-
Checking if Primrec₂ and Primrec.list_getElem? are available.
-/

/-
Defining the inner logic for the application case of `decode_code` and proving it is primitive
recursive.
-/
def Lambda.decode_code_case1_inner (r1 r2 : ℕ) : ℕ :=
  if r1 > 0 ∧ r2 > 0 then
    (Nat.pair 1 (Nat.pair (r1.pred) (r2.pred))).succ
  else 0

theorem Lambda.decode_code_case1_inner_primrec : Primrec₂ Lambda.decode_code_case1_inner := by
  apply Primrec₂.mk;
  unfold decode_code_case1_inner;
  refine Primrec.ite ?_ ?_ ?_;
  · -- The function that checks if two numbers are positive is primitive recursive.
    have h_pos : PrimrecPred (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0) := by
      have h_pos1 : PrimrecPred (fun p : ℕ × ℕ => p.1 > 0) := by
        -- The function that checks if a natural number is positive is primitive recursive.
        have h_pos : PrimrecPred (fun p : ℕ => p > 0) := by
          exact Primrec.nat_lt.comp ( Primrec.const 0 ) ( Primrec.id );
        exact h_pos.comp ( Primrec.fst )
      have h_pos2 : PrimrecPred (fun p : ℕ × ℕ => p.2 > 0) := by
        convert h_pos1.comp ( show Primrec fun p : ℕ × ℕ => ( p.2, p.1 ) from ?_ ) using 1;
        exact Primrec.pair ( Primrec.snd ) ( Primrec.fst )
      exact h_pos1.and h_pos2;
    exact h_pos;
  · -- The function p => (Nat.pair 1 (Nat.pair p.1.pred p.2.pred)).succ is primitive recursive
    -- because it is a composition of primitive recursive functions.
    have h_inner_primrec : Primrec (fun p : ℕ × ℕ => Nat.pair 1 (Nat.pair p.1.pred p.2.pred)) := by
      -- The function p => Nat.pair 1 (Nat.pair p.1.pred p.2.pred) is primitive recursive because it
      -- is a composition of primitive recursive functions.
      have h_inner_primrec : Primrec (fun p : ℕ × ℕ => Nat.pair p.1.pred p.2.pred) := by
        exact Primrec.pair ( Primrec.pred.comp Primrec.fst ) ( Primrec.pred.comp Primrec.snd );
      simp +zetaDelta only [Nat.pred_eq_sub_one] at *
      exact Primrec.pair ( Primrec.const 1 ) h_inner_primrec;
    exact Primrec.succ.comp h_inner_primrec;
  · exact Primrec.const 0

/-
Defining the application case for `decode_code` using the helper function and proving it is
primitive recursive.
-/
def Lambda.decode_code_case1 (L : List ℕ) (m : ℕ) : ℕ :=
  let n := L.length
  let (c₁, c₂) := m.unpair
  if c₁ < n ∧ c₂ < n then
    match L[c₁]?, L[c₂]? with
    | some r1, some r2 => Lambda.decode_code_case1_inner r1 r2
    | _, _ => 0
  else 0

theorem Lambda.decode_code_case1_primrec : Primrec₂ Lambda.decode_code_case1 := by
  unfold decode_code_case1;
  rw [ show ( fun L m => _ ) = fun L m => ( if m.unpair.1 < L.length ∧ m.unpair.2 < L.length then (
      L[m.unpair.1]? |> Option.bind <| fun r1 => ( L[m.unpair.2]? |> Option.bind <| fun r2 => some (
      decode_code_case1_inner r1 r2 ) ) ) else none ) |> Option.getD <| 0 from funext fun L =>
      funext fun m => ?_ ];
  · refine Primrec.option_getD.comp ?_ ?_;
    · apply_rules [ Primrec.ite, Primrec.option_bind, Primrec.option_getD ];
      · -- The length of the list is primitive recursive.
        have h_len : Primrec (fun a : List ℕ × ℕ => a.1.length) := by
          exact Primrec.list_length.comp ( Primrec.fst );
        have h_unpair : Primrec (fun a : ℕ => Nat.unpair a) := by
          exact Primrec.unpair;
        have h_unpair_first : Primrec (fun a : List ℕ × ℕ => (Nat.unpair a.2).1) := by
          exact Primrec.fst.comp ( h_unpair.comp ( Primrec.snd ) );
        have h_unpair_second : Primrec (fun a : List ℕ × ℕ => (Nat.unpair a.2).2) := by
          exact Primrec.snd.comp h_unpair |> Primrec.comp <| Primrec.snd;
        exact PrimrecPred.and ( Primrec.nat_lt.comp h_unpair_first h_len )
            ( Primrec.nat_lt.comp h_unpair_second h_len );
      · -- The function `get?` is the same as `getD` with a default value, and `getD` is primitive
        -- recursive.
        have h_getD_primrec : Primrec (fun (a : List ℕ × ℕ) => a.1[a.2]?) := by
          have h_get? : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l[i]?) := by
            have h_list_get? : Primrec₂ (fun (l : List ℕ) (i : ℕ) => l[i]?) := by
              apply_rules [ Primrec.list_getElem? ]
            aesop;
          exact h_get?;
        convert h_getD_primrec.comp
            ( show Primrec fun a : List ℕ × ℕ => ( a.1, Nat.unpair a.2 |> Prod.fst ) from ?_ ) using
            1;
        apply_rules [ Primrec.pair, Primrec.fst, Primrec.snd, Primrec.const ];
        exact Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.snd ) );
      · -- The `List.getElem?` function is primitive recursive.
        have h_get?_primrec : Primrec₂ (fun (L : List ℕ) (i : ℕ) => L[i]?) := by
          norm_num [ Primrec₂ ];
          exact Primrec.list_getElem?
        exact h_get?_primrec.comp ( Primrec.fst.comp Primrec.fst )
            ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.snd.comp Primrec.fst ) ) );
      · apply_rules [ Primrec.option_some.comp, Primrec₂.comp ];
        · exact Lambda.decode_code_case1_inner_primrec
        all_goals apply_rules [ Primrec.fst, Primrec.snd, Primrec.comp ];
      · exact Primrec.const none;
    · exact Primrec.const 0;
  · cases h : L[(Nat.unpair m |>.1)]? <;> cases h' : L[(Nat.unpair m |>.2)]? <;> aesop

/-
Defining the lambda abstraction case for `decode_code` and proving it is primitive recursive.
-/
def Lambda.decode_code_case2 (L : List ℕ) (m : ℕ) : ℕ :=
  let n := L.length
  if m < n then
    match L[m]? with
    | some r =>
      if r > 0 then
        (Nat.pair 2 (r.pred)).succ
      else 0
    | none => 0
  else 0

theorem Lambda.decode_code_case2_primrec : Primrec₂ Lambda.decode_code_case2 := by
  -- Let's unfold the definition of `decode_code_case2`.
  unfold decode_code_case2;
  -- The function that returns the previous value is primitive recursive.
  have h_prev : Primrec (fun r : ℕ => if r > 0 then (Nat.pair 2 r.pred).succ else 0) := by
    refine Primrec.ite ?_ ?_ ?_
    · exact Primrec.nat_lt.comp (Primrec.const 0) Primrec.id
    · exact Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 2) Primrec.pred)
    · exact Primrec.const 0
  have h_get : Primrec (fun (x : List ℕ × ℕ) => x.1[x.2]?) := by
    norm_num +zetaDelta at *;
    exact Primrec.list_getElem?
  have h_cond : Primrec (fun (x : List ℕ × ℕ) => if x.2 < x.1.length then x.1[x.2]? else none) := by
    refine Primrec.ite ?_ ?_ ?_
    · exact Primrec.nat_lt.comp Primrec.snd (Primrec.list_length.comp Primrec.fst)
    · exact h_get
    · exact Primrec.const none
  have h_bind : Primrec (fun (x : Option ℕ) =>
      match x with
      | some r => if r > 0 then (Nat.pair 2 r.pred).succ else 0
      | none => 0) := by
    have h_some : Primrec₂
        (fun (_ : Option ℕ) (r : ℕ) => if r > 0 then (Nat.pair 2 r.pred).succ else 0) := by
      apply Primrec₂.mk
      simpa using (h_prev.comp (Primrec.snd : Primrec (fun p : Option ℕ × ℕ => p.2)))
    convert Primrec.option_casesOn (show Primrec (fun x : Option ℕ => x) from Primrec.id)
      (show Primrec (fun _ : Option ℕ => 0) from Primrec.const 0)
      h_some using 1
    funext x
    cases x <;> rfl
  convert h_bind.comp h_cond using 1;
  constructor <;> intro h <;> rw [ Primrec₂ ] at * <;>
    simp_all only [gt_iff_lt, Nat.pred_eq_sub_one, Nat.succ_eq_add_one, getElem?_pos];
  · grind;
  · convert h using 1;
    ext; split_ifs <;> rfl;

/-
Redefining `Lambda.decode_code_step` using `if-then-else` for easier Primrec proof, and proving it
is primitive recursive.
-/
def Lambda.decode_code_step (L : List ℕ) : ℕ :=
  let n := L.length
  let (tag, m) := n.unpair
  if tag = 0 then Lambda.decode_code_case0 m
  else if tag = 1 then Lambda.decode_code_case1 L m
  else if tag = 2 then Lambda.decode_code_case2 L m
  else 0

theorem Lambda.decode_code_step_primrec : Primrec Lambda.decode_code_step := by
  unfold Lambda.decode_code_step
  have htag : Primrec (fun L : List ℕ => (Nat.unpair L.length).1) :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length)
  have hm : Primrec (fun L : List ℕ => (Nat.unpair L.length).2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)
  have h0 : Primrec (fun L : List ℕ => Lambda.decode_code_case0 (Nat.unpair L.length).2) :=
    Lambda.decode_code_case0_primrec.comp hm
  have h1 : Primrec (fun L : List ℕ => Lambda.decode_code_case1 L (Nat.unpair L.length).2) :=
    Lambda.decode_code_case1_primrec.comp Primrec.id hm
  have h2 : Primrec (fun L : List ℕ => Lambda.decode_code_case2 L (Nat.unpair L.length).2) :=
    Lambda.decode_code_case2_primrec.comp Primrec.id hm
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0)) h0
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) h1
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 2)) h2 (Primrec.const 0)))

/-
Checking the type of Primrec.nat_strong_rec to ensure correct usage.
-/

/-
Defining `Lambda.decode_code` using strong recursion.
-/
def Lambda.decode_code (n : ℕ) : ℕ :=
  Nat.strongRecOn n (fun n ih =>
    Lambda.decode_code_step ((List.range n).attach.map (fun ⟨m, hm⟩ => ih m (List.mem_range.1 hm))))

/-
Checking the definition of `Lambda.decode_code` since the system claims it is already declared.
-/

/-
Proving `Lambda.decode_code` is primitive recursive using `Primrec.nat_strong_rec`.
-/
/-- The strong-recursion step function computes `Lambda.decode_code` from its earlier values. -/
theorem Lambda.decode_code_eq_step (n : ℕ) :
    Lambda.decode_code_step ((List.range n).map Lambda.decode_code) = Lambda.decode_code n := by
  conv_rhs => unfold Lambda.decode_code
  rw [Nat.strongRecOn_eq]
  congr! 1
  refine List.ext_get ?_ ?_ <;> aesop

theorem Lambda.decode_code_primrec : Primrec Lambda.decode_code := by
  have h_g : Primrec₂ (fun (_ : Unit) (L : List ℕ) => some (Lambda.decode_code_step L)) :=
    (Primrec.option_some.comp Lambda.decode_code_step_primrec).comp Primrec.snd
  have h_rec := @Primrec.nat_strong_rec Unit ℕ _ _ (fun _ n => Lambda.decode_code n) _ h_g
    (fun _ n => congrArg some (Lambda.decode_code_eq_step n))
  exact h_rec.comp (Primrec.const ()) Primrec.id

/-
Checking if `Lambda.decode_code_primrec` was actually proved or contains sorries.
-/

/-
Proving `Lambda.app_code` is primitive recursive (renamed to avoid conflict).
-/
theorem Lambda.app_code_primrec' : Primrec₂ Lambda.app_code := by
  unfold Lambda.app_code
  apply Primrec₂.natPair.comp
  · exact Primrec₂.const 1
  · exact Primrec₂.natPair

/-
Checking if `Lambda.subst_code` is defined.
-/

/-
Checking if `Lambda.subst_code_case0` is defined.
-/

/-
Checking the status of `subst_code` related definitions and theorems.
-/

/-
Proving that `Lambda.app_code` correctly encodes an application.
-/
theorem Lambda.app_code_correct (t1 t2 : Lambda) :
  Lambda.app_code (Lambda.encode t1) (Lambda.encode t2) = Lambda.encode (Lambda.app t1 t2) := by
  rfl

/-
Proving that `Lambda.church_code` correctly encodes `Lambda.church n`.
-/
theorem Lambda.church_code_correct (n : ℕ) :
  Lambda.church_code n = Lambda.encode (Lambda.church n) := by
    exact (Lambda.encode_church_eq_church_code n).symm



/-
`Lambda.lift_code` computes the code of `Lambda.lift n k t` from the code of `t`.
-/
def Lambda.lift_code (t_code : ℕ) : ℕ → ℕ → ℕ :=
  Nat.strongRecOn t_code (fun t_code ih n k =>
    if h0 : t_code.unpair.1 = 0 then
      let y := t_code.unpair.2
      if y < k then Nat.pair 0 y else Nat.pair 0 (y + n)
    else if h1 : t_code.unpair.1 = 1 then
      let m := t_code.unpair.2
      let t1_code := m.unpair.1
      let t2_code := m.unpair.2
      have ht : t_code.unpair = (1, m) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 1 := by simpa [hp] using h1
            simp [m, hp, ha]
      have hm : m.unpair = (t1_code, t2_code) := by
        simp [t1_code, t2_code]
      have hlt1 : t1_code < t_code := Lambda.decode_lt_1 ht hm
      have hlt2 : t2_code < t_code := Lambda.decode_lt_2 ht hm
      Lambda.app_code (ih t1_code hlt1 n k) (ih t2_code hlt2 n k)
    else if h2 : t_code.unpair.1 = 2 then
      let t'_code := t_code.unpair.2
      have ht : t_code.unpair = (2, t'_code) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 2 := by simpa [hp] using h2
            simp [t'_code, hp, ha]
      have hlt : t'_code < t_code := Lambda.decode_lt_3 ht
      Lambda.lam_code (ih t'_code hlt n (k + 1))
    else 0
  )

/-
`Lambda.lift_code` correctly computes the code of `Lambda.lift`.
-/
theorem Lambda.lift_code_correct (t : Lambda) (n k : ℕ) :
  Lambda.lift_code (Lambda.encode t) n k = Lambda.encode (Lambda.lift n k t) := by
  induction t generalizing n k with
  | var y =>
      unfold Lambda.lift_code
      rw [Nat.strongRecOn_eq]
      by_cases hyk : y < k
      · simp [Lambda.encode, Lambda.lift, Nat.unpair_pair, hyk]
      · simp [Lambda.encode, Lambda.lift, Nat.unpair_pair, hyk]
  | app t1 t2 ih1 ih2 =>
      unfold Lambda.lift_code
      rw [Nat.strongRecOn_eq]
      have h1 := ih1 n k
      have h2 := ih2 n k
      unfold Lambda.lift_code at h1 h2
      simpa [Lambda.encode, Lambda.lift, Nat.unpair_pair, Lambda.app_code] using
        And.intro h1 h2
  | lam t ih =>
      unfold Lambda.lift_code
      rw [Nat.strongRecOn_eq]
      have hih := ih n (k + 1)
      unfold Lambda.lift_code at hih
      simpa [Lambda.encode, Lambda.lift, Nat.unpair_pair, Lambda.lam_code] using
        congrArg Lambda.lam_code hih

/-
`Lambda.subst_code'` computes the code of `t[x := s]` given the codes of `s` and `t`, and the
variable index `x`. It uses strong recursion on the code of `t`.
-/
def Lambda.subst_code' (s_code : ℕ) (t_code : ℕ) : ℕ → ℕ :=
  Nat.strongRecOn t_code (fun t_code ih x =>
    if h0 : t_code.unpair.1 = 0 then
      let y := t_code.unpair.2
      if x = y then Lambda.lift_code s_code x 0 else if y > x then Nat.pair 0 (y - 1) else Nat.pair
          0 y
    else if h1 : t_code.unpair.1 = 1 then
      let m := t_code.unpair.2
      let t1_code := m.unpair.1
      let t2_code := m.unpair.2
      have ht : t_code.unpair = (1, m) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 1 := by simpa [hp] using h1
            simp [m, hp, ha]
      have hm : m.unpair = (t1_code, t2_code) := by
        simp [t1_code, t2_code]
      have hlt1 : t1_code < t_code := Lambda.decode_lt_1 ht hm
      have hlt2 : t2_code < t_code := Lambda.decode_lt_2 ht hm
      Lambda.app_code (ih t1_code hlt1 x) (ih t2_code hlt2 x)
    else if h2 : t_code.unpair.1 = 2 then
      let t'_code := t_code.unpair.2
      have ht : t_code.unpair = (2, t'_code) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 2 := by simpa [hp] using h2
            simp [t'_code, hp, ha]
      have hlt : t'_code < t_code := Lambda.decode_lt_3 ht
      Lambda.lam_code (ih t'_code hlt (x + 1))
    else 0
  )

/-
`Lambda.subst_code'` correctly computes substitution under binder depth `x`.
-/
theorem Lambda.subst_code'_correct (s : Lambda) (x : ℕ) (t : Lambda) :
  Lambda.subst_code' (Lambda.encode s) (Lambda.encode t) x =
    Lambda.encode (Lambda.subst (Lambda.lift x 0 s) x t) := by
  revert x
  induction t with
  | var y =>
      intro x
      by_cases hxy : x = y
      · subst hxy
        unfold Lambda.subst_code'
        rw [Nat.strongRecOn_eq]
        simp [Lambda.encode, Nat.unpair_pair, Lambda.subst, Lambda.lift_code_correct]
      · by_cases hyx : x < y
        · unfold Lambda.subst_code'
          rw [Nat.strongRecOn_eq]
          have hyx' : y ≠ x := by
            intro hy
            exact hxy hy.symm
          simp [Lambda.encode, Nat.unpair_pair, Lambda.subst, hxy, hyx, hyx']
        · unfold Lambda.subst_code'
          rw [Nat.strongRecOn_eq]
          have hyx' : y ≠ x := by
            intro hy
            exact hxy hy.symm
          simp [Lambda.encode, Nat.unpair_pair, Lambda.subst, hxy, hyx, hyx']
  | app t1 t2 ih1 ih2 =>
      intro x
      unfold Lambda.subst_code'
      rw [Nat.strongRecOn_eq]
      have h1 := ih1 x
      have h2 := ih2 x
      unfold Lambda.subst_code' at h1 h2
      simpa [Lambda.encode, Nat.unpair_pair, Lambda.subst, Lambda.lift, Lambda.app_code] using
        And.intro h1 h2
  | lam t ih =>
      intro x
      unfold Lambda.subst_code'
      rw [Nat.strongRecOn_eq]
      have hih := ih (x + 1)
      unfold Lambda.subst_code' at hih
      have h_lift :
          Lambda.lift 1 0 (Lambda.lift x 0 s) = Lambda.lift (x + 1) 0 s := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Lambda.lift_add 1 x 0 s).symm
      simpa [Lambda.encode, Nat.unpair_pair, Lambda.subst, Lambda.lam_code, h_lift] using
        congrArg Lambda.lam_code hih

/-
`Lambda.step_code'` is a corrected version of `Lambda.step_code` that uses `Lambda.subst_code'` for
beta reduction. It computes the code of the next step of reduction given a list of previous results.
-/
def Lambda.step_code_case1' (L : List (Option ℕ)) : Option (Option ℕ) :=
  let c := L.length
  let m := c.unpair.2
  let (c1, c2) := m.unpair
  if c1 < c ∧ c2 < c then
    match c1.unpair with
    | (2, c1_body) => some (some (Lambda.subst_code' c2 c1_body 0))
    | _ =>
      (L[c1]?).bind (fun res1 =>
        match res1 with
        | some c1' => some (some (Lambda.app_code c1' c2))
        | none =>
          (L[c2]?).bind (fun res2 =>
            match res2 with
            | some c2' => some (some (Lambda.app_code c1 c2'))
            | none => some none
          )
      )
  else none

def Lambda.step_code' (L : List (Option ℕ)) : Option (Option ℕ) :=
  let c := L.length
  match c.unpair with
  | (0, _) => some none
  | (1, _) => Lambda.step_code_case1' L
  | (2, _) => Lambda.step_code_case2 L
  | _ => some none

/-
`Lambda.app_code` and `Lambda.lam_code` are primitive recursive.
-/
theorem Lambda.app_code_primrec_correct : Primrec₂ Lambda.app_code := by
  exact Lambda.app_code_primrec

theorem Lambda.lam_code_primrec_correct : Primrec Lambda.lam_code := by
  -- The function `Lambda.lam_code` is primitive recursive because it is a composition of primitive
  -- recursive functions.
  apply Lambda.lam_code_primrec

/-
`Lambda.app_code` is primitive recursive.
-/
theorem Lambda.app_code_is_primrec : Primrec₂ Lambda.app_code := by
  exact Primrec₂.natPair.comp (Primrec₂.const 1)
      (Primrec₂.natPair.comp Primrec₂.left Primrec₂.right)

/-
`Lambda.lam_code` is primitive recursive.
-/
theorem Lambda.lam_code_is_primrec : Primrec Lambda.lam_code := by
  exact Lambda.lam_code_primrec



/-
`eval_ecf` is primitive recursive.
-/
/-- Explicit closure format: a list of slots together with a default value.
Declared as an `abbrev` so that it is reducible and unifies with `List ℕ × ℕ`. -/
abbrev ECF := List ℕ × ℕ

instance : Primcodable ECF := inferInstanceAs (Primcodable (List ℕ × ℕ))

def eval_ecf (f : ECF) (x : ℕ) : ℕ :=
  if x < f.1.length then f.1[x]! else f.2

theorem eval_ecf_primrec : Primrec₂ eval_ecf := by
  have h_eq : ∀ (f : ECF) (x : ℕ), eval_ecf f x = (f.1[x]?).getD f.2 := by
    intro f x
    unfold eval_ecf
    by_cases h : x < f.1.length
    · rw [if_pos h, List.getElem?_eq_getElem h, Option.getD_some, getElem!_pos f.1 x h]
    · rw [if_neg h, List.getElem?_eq_none (not_lt.mp h), Option.getD_none]
  have h_get : Primrec (fun p : (List ℕ × ℕ) × ℕ => p.1.1[p.2]?) :=
    Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact Primrec.of_eq (Primrec.option_getD.comp h_get (Primrec.snd.comp Primrec.fst))
    fun p => (h_eq p.1 p.2).symm

/-
`ECF` is primcodable because it is a pair of a list of natural numbers and a natural number, both of
which are primcodable.
-/
instance : Primcodable ECF := inferInstanceAs (Primcodable (List ℕ × ℕ))


/-
`Lambda.var_code` is primitive recursive.
-/
def Lambda.var_code (n : ℕ) : ℕ := Nat.pair 0 n

theorem Lambda.var_code_primrec : Primrec Lambda.var_code := by
  exact Primrec₂.natPair.comp (Primrec.const 0) Primrec.id

/-
`mk_var_ecf` is primitive recursive.
-/
def mk_var_ecf (s_code : ℕ) (y : ℕ) : ECF :=
  let d := Lambda.var_code (y - 1)
  let L := (List.replicate y d) ++ [Lambda.lift_code s_code y 0]
  (L, Lambda.var_code y)

/-
`mk_app_ecf` is primitive recursive.
-/
def mk_app_ecf (f g : ECF) : ECF :=
  let len := max f.1.length g.1.length
  let l := (List.range len).map (fun x => Lambda.app_code (eval_ecf f x) (eval_ecf g x))
  (l, Lambda.app_code f.2 g.2)

theorem mk_app_ecf_primrec : Primrec₂ mk_app_ecf := by
  have h_len : Primrec₂ (fun f g : ECF => max f.1.length g.1.length) :=
    Primrec.nat_max.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
  have h_range : Primrec₂ (fun f g : ECF => List.range (max f.1.length g.1.length)) :=
    Primrec.list_range.comp h_len
  have h_map : Primrec₂ (fun f g : ECF => (List.range (max f.1.length g.1.length)).map (fun x =>
      Lambda.app_code (eval_ecf f x) (eval_ecf g x))) := by
    apply Primrec.list_map h_range
    apply Lambda.app_code_is_primrec.comp
    · exact eval_ecf_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    · exact eval_ecf_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact Primrec.pair h_map (Lambda.app_code_is_primrec.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))

/-
`mk_lam_ecf` is primitive recursive.
-/
def mk_lam_ecf (f : ECF) : ECF :=
  let l := f.1.tail.map (fun c => Lambda.lam_code c)
  (l, Lambda.lam_code f.2)

theorem mk_lam_ecf_primrec : Primrec mk_lam_ecf := by
  have h_tail : Primrec (fun f : ECF => f.1.tail) :=
    Primrec.list_tail.comp Primrec.fst
  have h_map : Primrec (fun f : ECF => f.1.tail.map (fun c => Lambda.lam_code c)) := by
    apply Primrec.list_map h_tail
    exact Lambda.lam_code_is_primrec.comp Primrec.snd
  exact Primrec.pair h_map (Lambda.lam_code_is_primrec.comp Primrec.snd)

/-
`mk_lift_var_ecf` represents the function `k ↦ encode (lift n k (var y))`.
-/
def mk_lift_var_ecf (n y : ℕ) : ECF :=
  (List.replicate (y + 1) (Lambda.var_code (y + n)), Lambda.var_code y)

theorem mk_lift_var_ecf_primrec : Primrec₂ mk_lift_var_ecf := by
  have h_replicate : Primrec
      (fun p : ℕ × ℕ => List.replicate (p.2 + 1) (Lambda.var_code (p.2 + p.1))) := by
    have h_list_replicate : Primrec (fun p : ℕ × ℕ => List.replicate p.2 p.1) := by
      have h_list_replicate_aux : ∀ p : ℕ × ℕ, List.replicate p.2 p.1 = List.map (fun _ => p.1)
          (List.range p.2) := by
        intro p
        simp
      simp +decide only [h_list_replicate_aux]
      apply Primrec.list_map
      · exact Primrec.list_range.comp Primrec.snd
      · exact Primrec.fst.comp Primrec.fst
    convert h_list_replicate.comp
      (Primrec.pair
        (Lambda.var_code_primrec.comp (Primrec.nat_add.comp Primrec.snd Primrec.fst))
        (Primrec.succ.comp Primrec.snd)) using 1
  exact Primrec.pair h_replicate (Lambda.var_code_primrec.comp Primrec.snd)

theorem eval_ecf_mk_lift_var_ecf (n y k : ℕ) :
  eval_ecf (mk_lift_var_ecf n y) k =
    if y < k then Lambda.var_code y else Lambda.var_code (y + n) := by
  unfold eval_ecf mk_lift_var_ecf
  by_cases hk : k < y + 1
  · have hyk : ¬ y < k := Nat.not_lt.mpr (Nat.le_of_lt_succ hk)
    simp [hk, hyk, Lambda.var_code]
  · have hyk : y < k := by
      exact lt_of_not_ge (by
        intro hle
        exact hk (Nat.lt_of_le_of_lt hle (Nat.lt_succ_self y)))
    simp [hk, hyk, Lambda.var_code]

/-
`Lambda.lift_ecf n t_code` represents the function `k ↦ encode (lift n k t)`.
-/
def Lambda.lift_ecf (n : ℕ) (t_code : ℕ) : ECF :=
  Nat.strongRecOn t_code (fun t_code ih =>
    if h0 : t_code.unpair.1 = 0 then
      mk_lift_var_ecf n t_code.unpair.2
    else if h1 : t_code.unpair.1 = 1 then
      let m := t_code.unpair.2
      let t1_code := m.unpair.1
      let t2_code := m.unpair.2
      have ht : t_code.unpair = (1, m) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 1 := by simpa [hp] using h1
            simp [m, hp, ha]
      have hm : m.unpair = (t1_code, t2_code) := by
        simp [t1_code, t2_code]
      have hlt1 : t1_code < t_code := Lambda.decode_lt_1 ht hm
      have hlt2 : t2_code < t_code := Lambda.decode_lt_2 ht hm
      mk_app_ecf (ih t1_code hlt1) (ih t2_code hlt2)
    else if h2 : t_code.unpair.1 = 2 then
      let t'_code := t_code.unpair.2
      have ht : t_code.unpair = (2, t'_code) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 2 := by simpa [hp] using h2
            simp [t'_code, hp, ha]
      have hlt : t'_code < t_code := Lambda.decode_lt_3 ht
      mk_lam_ecf (ih t'_code hlt)
    else ([], 0)
  )

def Lambda.lift_ecf_step_case0 (n : ℕ) (L : List ECF) : Option ECF :=
  some (mk_lift_var_ecf n L.length.unpair.2)

theorem Lambda.lift_ecf_step_case0_primrec (n : ℕ) : Primrec (Lambda.lift_ecf_step_case0 n) := by
  apply Primrec.option_some.comp
  apply mk_lift_var_ecf_primrec.comp
  · exact Primrec.const n
  · exact Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)

def Lambda.lift_ecf_step_case1 (L : List ECF) (m : ℕ) : Option ECF :=
  let (t1, t2) := m.unpair
  let f := (L[t1]?).getD ([], 0)
  let g := (L[t2]?).getD ([], 0)
  some (mk_app_ecf f g)

theorem Lambda.lift_ecf_step_case1_primrec : Primrec₂ Lambda.lift_ecf_step_case1 := by
  apply Primrec₂.mk
  unfold lift_ecf_step_case1
  have h_match : Primrec
      (fun (p : List ECF × ℕ) => match Nat.unpair p.2 with | (t1, t2) => (t1, t2)) := by
    exact Primrec.unpair.comp Primrec.snd
  have h_getD : Primrec (fun (p : List ECF × ℕ) => (p.1[p.2]?).getD ([], 0)) := by
    have h_get : Primrec (fun (p : List ECF × ℕ) => p.1[p.2]?) := by
      simp +zetaDelta only [Prod.mk.eta] at *
      exact Primrec.list_getElem?
    exact Primrec.option_getD.comp h_get (Primrec.const ([], 0))
  have h_mk_app : Primrec (fun (p : ECF × ECF) => some (mk_app_ecf p.1 p.2)) := by
    exact Primrec.option_some.comp mk_app_ecf_primrec
  have h_combined : Primrec (fun (p : List ECF × ℕ) => some (mk_app_ecf ((p.1[(Nat.unpair
      p.2).1]?).getD ([], 0)) ((p.1[(Nat.unpair p.2).2]?).getD ([], 0)))) := by
    have h_getD1 : Primrec (fun (p : List ECF × ℕ) => (p.1[(Nat.unpair p.2).1]?).getD ([], 0)) := by
      exact h_getD.comp
        (Primrec.id.comp (Primrec.fst.comp (Primrec.id.comp (Primrec.id.comp Primrec.id))) |>
          Primrec.pair <|
            Primrec.comp
              (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.id.comp
                  (Primrec.id.comp Primrec.id)))))
              (Primrec.id.comp (Primrec.id.comp (Primrec.id.comp Primrec.id))))
    have h_getD2 : Primrec (fun (p : List ECF × ℕ) => (p.1[(Nat.unpair p.2).2]?).getD ([], 0)) := by
      convert h_getD.comp (show Primrec (fun p : List ECF × ℕ => (p.1, (Nat.unpair p.2).2)) from ?_)
          using 1
      exact Primrec.pair Primrec.fst (Primrec.comp Primrec.snd h_match)
    exact h_mk_app.comp (h_getD1.pair h_getD2) |> Primrec.of_eq <| by aesop
  convert h_combined using 1

def Lambda.lift_ecf_step_case2 (L : List ECF) (t' : ℕ) : Option ECF :=
  let f := (L[t']?).getD ([], 0)
  some (mk_lam_ecf f)

theorem Lambda.lift_ecf_step_case2_primrec : Primrec₂ Lambda.lift_ecf_step_case2 := by
  have h_getD_primrec : Primrec₂ (fun (L : List ECF) (t' : ℕ) => (L[t']?).getD ([], 0)) := by
    have h_getD_primrec : Primrec₂ (fun (L : List ECF) (t' : ℕ) => (L[t']?).getD ([], 0)) := by
      have h_get?_primrec : Primrec₂ (fun (L : List ECF) (t' : ℕ) => L[t']?) := by
        apply Primrec.list_getElem?
      have h_getD_primrec : Primrec₂ (fun (o : Option ECF) (d : ECF) => o.getD d) := by
        exact Primrec.option_getD.comp₂ Primrec.fst Primrec.snd
      exact h_getD_primrec.comp₂ h_get?_primrec (Primrec.const ([], 0))
    exact h_getD_primrec
  have h_mk_lam_primrec : Primrec (fun (f : ECF) => some (mk_lam_ecf f)) := by
    exact Primrec.option_some.comp mk_lam_ecf_primrec
  exact h_mk_lam_primrec.comp₂ h_getD_primrec

def Lambda.lift_ecf_step (n : ℕ) (L : List ECF) : Option ECF :=
  let m := L.length.unpair.2
  if L.length.unpair.1 = 0 then Lambda.lift_ecf_step_case0 n L
  else if L.length.unpair.1 = 1 then Lambda.lift_ecf_step_case1 L m
  else if L.length.unpair.1 = 2 then Lambda.lift_ecf_step_case2 L m
  else some ([], 0)

theorem Lambda.lift_ecf_eq_step (n : ℕ) (m : ℕ) :
  Lambda.lift_ecf_step n ((List.range m).map (Lambda.lift_ecf n)) = some (Lambda.lift_ecf n m) := by
  cases hm : Nat.unpair m with
  | mk tag data =>
      cases tag with
      | zero =>
          simp [Lambda.lift_ecf_step, Lambda.lift_ecf, Lambda.lift_ecf_step_case0,
              Nat.strongRecOn_eq, hm]
      | succ tag =>
          cases tag with
          | zero =>
              let t1_code := data.unpair.1
              let t2_code := data.unpair.2
              have hdata : data.unpair = (t1_code, t2_code) := by
                simp [t1_code, t2_code]
              have htag0 : ¬ (Nat.unpair m).1 = 0 := by
                intro h
                simpa [h] using congrArg Prod.fst hm
              have htag1 : (Nat.unpair m).1 = 1 := by
                simpa using congrArg Prod.fst hm
              have htag2 : ¬ (Nat.unpair m).1 = 2 := by
                intro h
                simpa [h] using congrArg Prod.fst hm
              have hm_data : (Nat.unpair m).2 = data := by
                simpa using congrArg Prod.snd hm
              have hlt1 : t1_code < m := Lambda.decode_lt_1 hm hdata
              have hlt2 : t2_code < m := Lambda.decode_lt_2 hm hdata
              have hget1 : ((List.range m).map (Lambda.lift_ecf n))[t1_code]? = some
                  (Lambda.lift_ecf n t1_code) := by
                simp [List.getElem?_map, List.getElem?_range hlt1]
              have hget2 : ((List.range m).map (Lambda.lift_ecf n))[t2_code]? = some
                  (Lambda.lift_ecf n t2_code) := by
                simp [List.getElem?_map, List.getElem?_range hlt2]
              have hstep :
                  Lambda.lift_ecf_step n ((List.range m).map (Lambda.lift_ecf n)) =
                    some (mk_app_ecf (Lambda.lift_ecf n t1_code) (Lambda.lift_ecf n t2_code)) := by
                rw [Lambda.lift_ecf_step]
                simp [List.length_map, List.length_range, htag1, hm_data,
                  Lambda.lift_ecf_step_case1, hdata, hget1, hget2]
              have htarget :
                  Lambda.lift_ecf n m =
                    mk_app_ecf (Lambda.lift_ecf n t1_code) (Lambda.lift_ecf n t2_code) := by
                unfold Lambda.lift_ecf
                rw [Nat.strongRecOn_eq]
                dsimp
                rw [if_neg htag0, if_pos htag1]
                rw [hm_data, hdata]
              simpa [htarget] using hstep
          | succ tag =>
              cases tag with
              | zero =>
                  have htag0 : ¬ (Nat.unpair m).1 = 0 := by
                    intro h
                    simpa [h] using congrArg Prod.fst hm
                  have htag1 : ¬ (Nat.unpair m).1 = 1 := by
                    intro h
                    simpa [h] using congrArg Prod.fst hm
                  have htag2 : (Nat.unpair m).1 = 2 := by
                    simpa using congrArg Prod.fst hm
                  have hm_data : (Nat.unpair m).2 = data := by
                    simpa using congrArg Prod.snd hm
                  have hlt : data < m := Lambda.decode_lt_3 hm
                  have hget : ((List.range m).map (Lambda.lift_ecf n))[data]? = some
                      (Lambda.lift_ecf n data) := by
                    simp [List.getElem?_map, List.getElem?_range hlt]
                  have hstep :
                      Lambda.lift_ecf_step n ((List.range m).map (Lambda.lift_ecf n)) =
                        some (mk_lam_ecf (Lambda.lift_ecf n data)) := by
                    rw [Lambda.lift_ecf_step]
                    simp [List.length_map, List.length_range, htag2, hm_data,
                      Lambda.lift_ecf_step_case2, hget]
                  have htarget : Lambda.lift_ecf n m = mk_lam_ecf (Lambda.lift_ecf n data) := by
                    unfold Lambda.lift_ecf
                    rw [Nat.strongRecOn_eq]
                    dsimp
                    rw [if_neg htag0, if_neg htag1, if_pos htag2]
                    rw [hm_data]
                  simpa [htarget] using hstep
              | succ tag =>
                  simp [Lambda.lift_ecf_step, Lambda.lift_ecf, Nat.strongRecOn_eq, hm]

theorem Lambda.lift_ecf_step_primrec : Primrec₂ Lambda.lift_ecf_step := by
  apply Primrec₂.mk
  have h_tag : Primrec (fun p : ℕ × List ECF => (Nat.unpair p.2.length).1) := by
    exact Primrec.fst.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd))
  have h_m : Primrec (fun p : ℕ × List ECF => (Nat.unpair p.2.length).2) := by
    exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd))
  have h_case0 : Primrec (fun p : ℕ × List ECF => Lambda.lift_ecf_step_case0 p.1 p.2) := by
    unfold Lambda.lift_ecf_step_case0
    apply Primrec.option_some.comp
    apply mk_lift_var_ecf_primrec.comp
    · exact Primrec.fst
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd))
  have h_case1 : Primrec
      (fun p : ℕ × List ECF => Lambda.lift_ecf_step_case1 p.2 ((Nat.unpair p.2.length).2)) := by
    exact Lambda.lift_ecf_step_case1_primrec.comp Primrec.snd h_m
  have h_case2 : Primrec
      (fun p : ℕ × List ECF => Lambda.lift_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)) := by
    exact Lambda.lift_ecf_step_case2_primrec.comp Primrec.snd h_m
  have h_else : Primrec (fun _ : ℕ × List ECF => (some ([], 0) : Option ECF)) := Primrec.const _
  have h_ite2 :
      Primrec
        (fun p : ℕ × List ECF =>
          if (Nat.unpair p.2.length).1 = 2 then
            Lambda.lift_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)
          else some ([], 0)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp h_tag (Primrec.const 2)
    · exact h_case2
    · exact h_else
  have h_ite1 :
      Primrec
        (fun p : ℕ × List ECF =>
          if (Nat.unpair p.2.length).1 = 1 then
            Lambda.lift_ecf_step_case1 p.2 ((Nat.unpair p.2.length).2)
          else if (Nat.unpair p.2.length).1 = 2 then
            Lambda.lift_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)
          else some ([], 0)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp h_tag (Primrec.const 1)
    · exact h_case1
    · exact h_ite2
  have h_ite0 :
      Primrec
        (fun p : ℕ × List ECF =>
          if (Nat.unpair p.2.length).1 = 0 then
            Lambda.lift_ecf_step_case0 p.1 p.2
          else if (Nat.unpair p.2.length).1 = 1 then
            Lambda.lift_ecf_step_case1 p.2 ((Nat.unpair p.2.length).2)
          else if (Nat.unpair p.2.length).1 = 2 then
            Lambda.lift_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)
          else some ([], 0)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp h_tag (Primrec.const 0)
    · exact h_case0
    · exact h_ite1
  simpa [Lambda.lift_ecf_step] using h_ite0

theorem Lambda.lift_ecf_primrec : Primrec₂ Lambda.lift_ecf :=
  Primrec.nat_strong_rec _ Lambda.lift_ecf_step_primrec Lambda.lift_ecf_eq_step

theorem eval_ecf_mk_app_ecf_aux (f g : ECF) (x : ℕ) :
  eval_ecf (mk_app_ecf f g) x = Lambda.app_code (eval_ecf f x) (eval_ecf g x) := by
  simp +decide [mk_app_ecf, eval_ecf]
  grind

theorem eval_ecf_mk_lam_ecf_aux (f : ECF) (x : ℕ) :
  eval_ecf (mk_lam_ecf f) x = Lambda.lam_code (eval_ecf f (x + 1)) := by
  cases f with
  | mk l c =>
      cases l with
      | nil =>
          simp [eval_ecf, mk_lam_ecf]
      | cons a l =>
          by_cases h : x < l.length
          · simp [eval_ecf, mk_lam_ecf, h]
          · simp [eval_ecf, mk_lam_ecf, h]

theorem Lambda.lift_code_eq_eval_lift_ecf (n t_code k : ℕ) :
  Lambda.lift_code t_code n k = eval_ecf (Lambda.lift_ecf n t_code) k := by
  revert n k
  refine Nat.strong_induction_on t_code ?_
  intro t_code ih n k
  cases hp : t_code.unpair with
  | mk tag data =>
      by_cases h0 : tag = 0
      · subst h0
        rw [Lambda.lift_code, Lambda.lift_ecf]
        rw [Nat.strongRecOn_eq, Nat.strongRecOn_eq]
        simp [hp, eval_ecf_mk_lift_var_ecf, Lambda.var_code]
      · by_cases h1 : tag = 1
        · subst h1
          let t1_code := data.unpair.1
          let t2_code := data.unpair.2
          have hm : data.unpair = (t1_code, t2_code) := by
            simp [t1_code, t2_code]
          have hlt1 : t1_code < t_code := Lambda.decode_lt_1 hp hm
          have hlt2 : t2_code < t_code := Lambda.decode_lt_2 hp hm
          have hcode :
              Lambda.lift_code t_code n k =
                Lambda.app_code (Lambda.lift_code t1_code n k) (Lambda.lift_code t2_code n k) := by
            rw [Lambda.lift_code, Nat.strongRecOn_eq]
            simp only [hp, h0, ↓reduceDIte, app_code, dite_eq_ite, Nat.pair_eq_pair,
              true_and, t1_code, t2_code]
            exact And.intro rfl rfl
          have hecf :
              Lambda.lift_ecf n t_code = mk_app_ecf (Lambda.lift_ecf n t1_code)
                  (Lambda.lift_ecf n t2_code) := by
            rw [Lambda.lift_ecf, Nat.strongRecOn_eq]
            simp only [hp, one_ne_zero, ↓reduceDIte, dite_eq_ite, t1_code, t2_code]
            exact rfl
          rw [hcode, hecf, eval_ecf_mk_app_ecf_aux, ih t1_code hlt1 n k, ih t2_code hlt2 n k]
        · by_cases h2 : tag = 2
          · subst h2
            let t'_code := data
            have hlt : t'_code < t_code := Lambda.decode_lt_3 hp
            have hcode :
                Lambda.lift_code t_code n k = Lambda.lam_code (Lambda.lift_code t'_code n (k + 1))
                    := by
              rw [Lambda.lift_code, Nat.strongRecOn_eq]
              simp [hp, h0, h1, t'_code, Lambda.lam_code, Lambda.lift_code]
            have hecf : Lambda.lift_ecf n t_code = mk_lam_ecf (Lambda.lift_ecf n t'_code) := by
              rw [Lambda.lift_ecf, Nat.strongRecOn_eq]
              simp [hp, t'_code, Lambda.lift_ecf]
            rw [hcode, hecf, eval_ecf_mk_lam_ecf_aux, ih t'_code hlt n (k + 1)]
          · rw [Lambda.lift_code, Lambda.lift_ecf]
            rw [Nat.strongRecOn_eq, Nat.strongRecOn_eq]
            simp [hp, h0, h1, h2, eval_ecf]

def Lambda.lift_code_uncurried (v : ℕ × ℕ × ℕ) : ℕ :=
  Lambda.lift_code v.1 v.2.1 v.2.2

theorem Lambda.lift_code_uncurried_primrec : Primrec Lambda.lift_code_uncurried := by
  rw [Primrec]
  let f : (ℕ × ℕ × ℕ) → ECF := fun v => Lambda.lift_ecf v.2.1 v.1
  let g : (ℕ × ℕ × ℕ) → ℕ := fun v => v.2.2
  have hf : Primrec f := Lambda.lift_ecf_primrec.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hg : Primrec g := Primrec.snd.comp Primrec.snd
  have : Lambda.lift_code_uncurried = fun v => eval_ecf (f v) (g v) := by
    funext v
    simp only [Lambda.lift_code_uncurried, f, g]
    rw [Lambda.lift_code_eq_eval_lift_ecf]
  rw [this]
  exact eval_ecf_primrec.comp hf hg

theorem mk_var_ecf_primrec : Primrec₂ mk_var_ecf := by
  have h_replicate : Primrec (fun p : ℕ × ℕ => List.replicate p.2 (Lambda.var_code (p.2 - 1))) := by
    have h_list_replicate : Primrec (fun p : ℕ × ℕ => List.replicate p.2 p.1) := by
      have h_list_replicate_aux : ∀ p : ℕ × ℕ, List.replicate p.2 p.1 = List.map (fun _ => p.1)
          (List.range p.2) := by
        intro p
        simp
      simp +decide only [h_list_replicate_aux]
      apply Primrec.list_map
      · exact Primrec.list_range.comp Primrec.snd
      · exact Primrec.fst.comp Primrec.fst
    exact h_list_replicate.comp
      (Primrec.pair (Lambda.var_code_primrec.comp (Primrec.pred.comp Primrec.snd)) Primrec.snd)
  have h_lift_slot : Primrec (fun p : ℕ × ℕ => Lambda.lift_code p.1 p.2 0) := by
    exact Lambda.lift_code_uncurried_primrec.comp
      (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd (Primrec.const 0)))
  have h_last : Primrec (fun p : ℕ × ℕ => [Lambda.lift_code p.1 p.2 0]) := by
    exact Primrec.list_cons.comp h_lift_slot (Primrec.const [])
  have h_list : Primrec (fun p : ℕ × ℕ => List.replicate p.2 (Lambda.var_code (p.2 - 1)) ++
      [Lambda.lift_code p.1 p.2 0]) := by
    exact Primrec.list_append.comp h_replicate h_last
  exact Primrec.pair h_list (Lambda.var_code_primrec.comp Primrec.snd)

/-
`Lambda.subst_ecf` computes an ECF representing the substitution `t[x := s]` as a function of `x`.
It is defined by strong recursion on the code of `t`.
-/
def Lambda.subst_ecf (s_code : ℕ) (t_code : ℕ) : ECF :=
  Nat.strongRecOn t_code (fun t_code ih =>
    if h0 : t_code.unpair.1 = 0 then
      mk_var_ecf s_code t_code.unpair.2
    else if h1 : t_code.unpair.1 = 1 then
      let m := t_code.unpair.2
      let t1_code := m.unpair.1
      let t2_code := m.unpair.2
      have ht : t_code.unpair = (1, m) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 1 := by simpa [hp] using h1
            simp [m, hp, ha]
      have hm : m.unpair = (t1_code, t2_code) := by
        simp [t1_code, t2_code]
      have hlt1 : t1_code < t_code := Lambda.decode_lt_1 ht hm
      have hlt2 : t2_code < t_code := Lambda.decode_lt_2 ht hm
      mk_app_ecf (ih t1_code hlt1) (ih t2_code hlt2)
    else if h2 : t_code.unpair.1 = 2 then
      let t'_code := t_code.unpair.2
      have ht : t_code.unpair = (2, t'_code) := by
        cases hp : t_code.unpair with
        | mk a b =>
            have ha : a = 2 := by simpa [hp] using h2
            simp [t'_code, hp, ha]
      have hlt : t'_code < t_code := Lambda.decode_lt_3 ht
      mk_lam_ecf (ih t'_code hlt)
    else ([], 0)
  )

/-
`Lambda.subst_ecf_step_case0` is primitive recursive.
-/
def Lambda.subst_ecf_step_case0 (s_code : ℕ) (L : List ECF) : Option ECF :=
  some (mk_var_ecf s_code L.length.unpair.2)

theorem Lambda.subst_ecf_step_case0_primrec (s_code : ℕ) :
    Primrec (Lambda.subst_ecf_step_case0 s_code) := by
  apply Primrec.option_some.comp
  apply mk_var_ecf_primrec.comp
  · exact Primrec.const s_code
  · exact Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)

/-
`Lambda.subst_ecf_step_case1` is primitive recursive.
-/
def Lambda.subst_ecf_step_case1 (L : List ECF) (m : ℕ) : Option ECF :=
  let (t1, t2) := m.unpair
  let f := (L[t1]?).getD ([], 0)
  let g := (L[t2]?).getD ([], 0)
  some (mk_app_ecf f g)

theorem Lambda.subst_ecf_step_case1_primrec : Primrec₂ Lambda.subst_ecf_step_case1 := by
  apply Primrec₂.mk;
  unfold subst_ecf_step_case1;
  -- The `match` statement is deterministic and can be expressed using `Primrec`'s `casesOn`
  -- function.
  have h_match : Primrec
      (fun (p : List ECF × ℕ) => match Nat.unpair p.2 with | (t1, t2) => (t1, t2)) := by
    exact Primrec.unpair.comp ( Primrec.snd );
  have h_getD : Primrec (fun (p : List ECF × ℕ) => (p.1[p.2]?).getD ([], 0)) := by
    have h_getD : Primrec (fun (p : List ECF × ℕ) => p.1[p.2]?) := by
      simp +zetaDelta only [Prod.mk.eta] at *
      exact Primrec.list_getElem?;
    exact Primrec.option_getD.comp h_getD ( Primrec.const ( [ ], 0 ) );
  have h_mk_app : Primrec (fun (p : ECF × ECF) => some (mk_app_ecf p.1 p.2)) := by
    exact Primrec.option_some.comp ( mk_app_ecf_primrec );
  have h_combined : Primrec (fun (p : List ECF × ℕ) => some (mk_app_ecf ((p.1[(Nat.unpair
      p.2).1]?).getD ([], 0)) ((p.1[(Nat.unpair p.2).2]?).getD ([], 0)))) := by
    have h_getD1 : Primrec (fun (p : List ECF × ℕ) => (p.1[(Nat.unpair p.2).1]?).getD ([], 0)) := by
      exact h_getD.comp ( Primrec.id.comp ( Primrec.fst.comp ( Primrec.id.comp ( Primrec.id.comp (
          Primrec.id ) ) ) ) |> Primrec.pair <| Primrec.comp ( Primrec.fst.comp (
          Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.id.comp ( Primrec.id.comp ( Primrec.id )
          ) ) ) ) ) ( Primrec.id.comp ( Primrec.id.comp ( Primrec.id.comp ( Primrec.id ) ) ) ) )
    have h_getD2 : Primrec (fun (p : List ECF × ℕ) => (p.1[(Nat.unpair p.2).2]?).getD ([], 0)) := by
      convert h_getD.comp
          ( show Primrec ( fun p : List ECF × ℕ => ( p.1, ( Nat.unpair p.2 ).2 ) ) from ?_ ) using
          1;
      exact Primrec.pair ( Primrec.fst ) ( Primrec.comp ( Primrec.snd ) h_match )
    exact h_mk_app.comp ( h_getD1.pair h_getD2 ) |> Primrec.of_eq <| by aesop;
  convert h_combined using 1


/-
`Lambda.subst_ecf_step_case2` is primitive recursive.
-/
def Lambda.subst_ecf_step_case2 (L : List ECF) (t' : ℕ) : Option ECF :=
  let f := (L[t']?).getD ([], 0)
  some (mk_lam_ecf f)

theorem Lambda.subst_ecf_step_case2_primrec : Primrec₂ Lambda.subst_ecf_step_case2 := by
  -- The function `getD` is primitive recursive because it is a composition of primitive recursive
  -- functions.
  have h_getD_primrec : Primrec₂ (fun (L : List ECF) (t' : ℕ) => (L[t']?).getD ([], 0)) := by
    -- The function `getD` is primitive recursive because it is a composition of primitive recursive
    -- functions: `get?` and `getD`.
    have h_getD_primrec : Primrec₂ (fun (L : List ECF) (t' : ℕ) => (L[t']?).getD ([], 0)) := by
      have h_get?_primrec : Primrec₂ (fun (L : List ECF) (t' : ℕ) => L[t']?) := by
        apply Primrec.list_getElem?
      have h_getD_primrec : Primrec₂ (fun (o : Option ECF) (d : ECF) => o.getD d) := by
        exact Primrec.option_getD.comp₂ ( Primrec.fst ) ( Primrec.snd )
      exact h_getD_primrec.comp₂ h_get?_primrec (Primrec.const ([], 0));
    exact h_getD_primrec;
  have h_mk_lam_primrec : Primrec (fun (f : ECF) => some (mk_lam_ecf f)) := by
    exact Primrec.option_some.comp ( mk_lam_ecf_primrec );
  exact h_mk_lam_primrec.comp₂ h_getD_primrec


/-
`Lambda.subst_ecf_step` is primitive recursive.
-/
def Lambda.subst_ecf_step (s_code : ℕ) (L : List ECF) : Option ECF :=
  let n := L.length
  let (tag, m) := n.unpair
  if tag = 0 then Lambda.subst_ecf_step_case0 s_code L
  else if tag = 1 then Lambda.subst_ecf_step_case1 L m
  else if tag = 2 then Lambda.subst_ecf_step_case2 L m
  else some ([], 0)

theorem Lambda.subst_ecf_step_primrec : Primrec₂ Lambda.subst_ecf_step := by
  apply Primrec₂.mk
  have h_tag : Primrec (fun p : ℕ × List ECF => (Nat.unpair p.2.length).1) := by
    exact (Primrec.fst.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd)))
  have h_m : Primrec (fun p : ℕ × List ECF => (Nat.unpair p.2.length).2) := by
    exact (Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd)))
  have h_case0 : Primrec (fun p : ℕ × List ECF => Lambda.subst_ecf_step_case0 p.1 p.2) := by
    unfold Lambda.subst_ecf_step_case0
    apply Primrec.option_some.comp
    apply mk_var_ecf_primrec.comp
    · exact Primrec.fst
    · exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.list_length.comp Primrec.snd))
  have h_case1 :
      Primrec (fun p : ℕ × List ECF => Lambda.subst_ecf_step_case1 p.2 ((Nat.unpair p.2.length).2))
          := by
    exact Lambda.subst_ecf_step_case1_primrec.comp Primrec.snd h_m
  have h_case2 :
      Primrec (fun p : ℕ × List ECF => Lambda.subst_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2))
          := by
    exact Lambda.subst_ecf_step_case2_primrec.comp Primrec.snd h_m
  have h_else : Primrec (fun _ : ℕ × List ECF => (some ([], 0) : Option ECF)) := Primrec.const _
  have h_ite2 :
      Primrec
        (fun p : ℕ × List ECF =>
          if (Nat.unpair p.2.length).1 = 2 then
            Lambda.subst_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)
          else some ([], 0)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp h_tag (Primrec.const 2)
    · exact h_case2
    · exact h_else
  have h_ite1 :
      Primrec
        (fun p : ℕ × List ECF =>
          if (Nat.unpair p.2.length).1 = 1 then
            Lambda.subst_ecf_step_case1 p.2 ((Nat.unpair p.2.length).2)
          else if (Nat.unpair p.2.length).1 = 2 then
            Lambda.subst_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)
          else some ([], 0)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp h_tag (Primrec.const 1)
    · exact h_case1
    · exact h_ite2
  have h_ite0 :
      Primrec
        (fun p : ℕ × List ECF =>
          if (Nat.unpair p.2.length).1 = 0 then
            Lambda.subst_ecf_step_case0 p.1 p.2
          else if (Nat.unpair p.2.length).1 = 1 then
            Lambda.subst_ecf_step_case1 p.2 ((Nat.unpair p.2.length).2)
          else if (Nat.unpair p.2.length).1 = 2 then
            Lambda.subst_ecf_step_case2 p.2 ((Nat.unpair p.2.length).2)
          else some ([], 0)) := by
    apply Primrec.ite
    · exact Primrec.eq.comp h_tag (Primrec.const 0)
    · exact h_case0
    · exact h_ite1
  simpa [Lambda.subst_ecf_step] using h_ite0


-- #check @List.getElem?

/-
Accessing the `k`-th element of a mapped range list returns the function applied to `k`, provided
`k` is within bounds.
-/
theorem List.get!_map_range_eq {α} [Inhabited α] (n : ℕ) (f : ℕ → α) (k : ℕ) (h : k < n) :
  ((List.range n).map f)[k]! = f k := by
    simp +decide [ h ]


-- #check Turing.TM2Computable


/-
`Lambda.step_code_case2_spec` relates the behavior of `Lambda.step_code_case2` to the `Lambda.step`
relation for lambda abstractions.
-/
theorem Lambda.step_code_case2_spec (L : List (Option ℕ)) (t1 : Lambda) (c' : ℕ)
  (h_len : L.length = Lambda.encode (Lambda.lam t1))
  (h_ih : ∀ c1', L[Lambda.encode t1]? = some (some c1') → ∃ t1', Lambda.encode t1' = c1' ∧
      Lambda.step t1 t1')
  (h_res : Lambda.step_code_case2 L = some (some c')) :
  ∃ t', Lambda.encode t' = c' ∧ Lambda.step (Lambda.lam t1) t' := by
    unfold Lambda.step_code_case2 at h_res
    simp only [h_len, show Lambda.encode (Lambda.lam t1) = Nat.pair 2 (Lambda.encode t1) from rfl,
      Nat.unpair_pair] at h_res
    rw [if_pos (Lambda.lt_pair_of_pos (by norm_num) _)] at h_res
    rcases hL : L[Lambda.encode t1]? with _ | res
    · rw [hL] at h_res
      exact absurd h_res (by simp)
    · rcases res with _ | c2'
      · rw [hL] at h_res
        exact absurd h_res (by simp)
      · rw [hL] at h_res
        obtain ⟨t1', ht1', ht1''⟩ := h_ih c2' hL
        refine ⟨Lambda.lam t1', ?_, Lambda.step.lam _ _ ht1''⟩
        simp only [Option.bind_some] at h_res
        have hc : Lambda.lam_code c2' = c' := Option.some_inj.mp (Option.some_inj.mp h_res)
        rw [Lambda.encode, ht1', ← hc, Lambda.lam_code]

/-
`Lambda.subst_code_uncurried` is a helper function that uncurries `Lambda.subst_code'`.
-/
def Lambda.subst_code_uncurried (v : ℕ × ℕ × ℕ) : ℕ :=
  Lambda.subst_code' v.1 v.2.1 v.2.2


-- #check Turing.TM2Computable




theorem LambdaComputable_imp_Partrec_aux
  (h_eval_correct : ∀ t n, Lambda.reduces t (Lambda.church n) ↔ Lambda.eval (Lambda.encode t) =
      Part.some (Lambda.church_code n))
  {f : ℕ →. ℕ} (h : LambdaComputable f) : Partrec f := by
  obtain ⟨c, hc⟩ := LambdaComputable_imp_compute_fun_aux h_eval_correct h
  have : Partrec (Lambda.compute_fun c) := Lambda.compute_fun_partrec c
  refine Partrec.of_eq this (fun n => ?_)
  rw [hc]



-- Unfolding equation for `Lambda.subst_ecf`.
open Lambda in
theorem Lambda.subst_ecf_eq (s_code n : ℕ) :
    Lambda.subst_ecf s_code n =
      if (Nat.unpair n).1 = 0 then mk_var_ecf s_code (Nat.unpair n).2
      else if (Nat.unpair n).1 = 1 then
        mk_app_ecf (Lambda.subst_ecf s_code (Nat.unpair (Nat.unpair n).2).1)
          (Lambda.subst_ecf s_code (Nat.unpair (Nat.unpair n).2).2)
      else if (Nat.unpair n).1 = 2 then mk_lam_ecf (Lambda.subst_ecf s_code (Nat.unpair n).2)
      else ([], 0) := by
  conv_lhs => unfold Lambda.subst_ecf
  rw [Nat.strongRecOn_eq]
  by_cases h0 : (Nat.unpair n).1 = 0
  · rw [dif_pos h0, if_pos h0]
  · rw [dif_neg h0, if_neg h0]
    by_cases h1 : (Nat.unpair n).1 = 1
    · rw [dif_pos h1, if_pos h1]
      rfl
    · rw [dif_neg h1, if_neg h1]
      by_cases h2 : (Nat.unpair n).1 = 2
      · rw [dif_pos h2, if_pos h2]
        rfl
      · rw [dif_neg h2, if_neg h2]

open Lambda in
theorem Lambda.subst_ecf_eq_step (s_code : ℕ) (n : ℕ) :
    Lambda.subst_ecf_step s_code ((List.range n).map (Lambda.subst_ecf s_code))
      = some (Lambda.subst_ecf s_code n) := by
  have hlen : ((List.range n).map (Lambda.subst_ecf s_code)).length = n := by
    rw [List.length_map, List.length_range]
  have hget : ∀ k, k < n →
      ((List.range n).map (Lambda.subst_ecf s_code))[k]?.getD (([], 0) : ECF)
        = Lambda.subst_ecf s_code k := by
    intro k hk
    rw [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
  unfold Lambda.subst_ecf_step Lambda.subst_ecf_step_case0 Lambda.subst_ecf_step_case1
    Lambda.subst_ecf_step_case2
  rw [hlen, Lambda.subst_ecf_eq s_code n]
  rcases htag : Nat.unpair n with ⟨tag, m⟩
  simp only [htag]
  by_cases h0 : tag = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : tag = 1
    · rw [if_pos h1, if_pos h1, hget (Nat.unpair m).1 (Lambda.decode_lt_1 (h1 ▸ htag) rfl),
        hget (Nat.unpair m).2 (Lambda.decode_lt_2 (h1 ▸ htag) rfl)]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : tag = 2
      · rw [if_pos h2, if_pos h2, hget m (Lambda.decode_lt_3 (h2 ▸ htag))]
      · rw [if_neg h2, if_neg h2]

-- `subst_ecf_step` is primitive recursive and satisfies the strong-recursion equation
-- `subst_ecf_step a (List.map (subst_ecf a) (List.range n)) = some (subst_ecf a n)`.
theorem Lambda.subst_ecf_primrec : Primrec₂ Lambda.subst_ecf :=
  Primrec.nat_strong_rec _ Lambda.subst_ecf_step_primrec Lambda.subst_ecf_eq_step

theorem eval_ecf_mk_var_ecf (s_code y x : ℕ) :
  eval_ecf (mk_var_ecf s_code y) x =
    if x = y then Lambda.lift_code s_code y 0 else if y > x then Lambda.var_code (y - 1) else
        Lambda.var_code y := by
  unfold eval_ecf mk_var_ecf
  by_cases hxy : x = y
  · subst hxy
    simp [Lambda.var_code]
  · by_cases hyx : y > x
    · have hxlt : x < y := hyx
      have hxlt' : x < y + 1 := lt_trans hxlt (Nat.lt_succ_self y)
      have hxltRep : x < (List.replicate y (Lambda.var_code (y - 1))).length := by
        simpa
      simp [hxy, hyx, List.length_replicate, hxlt']
    · have hyx' : ¬ y > x := hyx
      have hyxlt : y < x := by
        exact lt_of_le_of_ne (Nat.le_of_not_gt hyx) (by simpa [eq_comm] using hxy)
      have hxlen' : ¬ x < y + 1 := not_lt_of_ge (Nat.succ_le_of_lt hyxlt)
      have hxlen : ¬ x < (List.replicate y (Lambda.var_code (y - 1)) ++ [s_code]).length := by
        simpa [List.length_replicate] using not_lt_of_ge (Nat.succ_le_of_lt hyxlt)
      simp [hxy, hyx', hxlen']

theorem eval_ecf_mk_app_ecf (f g : ECF) (x : ℕ) :
  eval_ecf (mk_app_ecf f g) x = Lambda.app_code (eval_ecf f x) (eval_ecf g x) := by
    simp +decide [ mk_app_ecf, eval_ecf ];
    grind

theorem eval_ecf_mk_lam_ecf (f : ECF) (x : ℕ) :
  eval_ecf (mk_lam_ecf f) x = Lambda.lam_code (eval_ecf f (x + 1)) := by
  cases f with
  | mk l c =>
      cases l with
      | nil =>
          simp [eval_ecf, mk_lam_ecf]
      | cons a l =>
          by_cases h : x < l.length
          · simp [eval_ecf, mk_lam_ecf, h]
          · simp [eval_ecf, mk_lam_ecf, h]

theorem Lambda.subst_code'_eq_eval_subst_ecf (s_code t_code x : ℕ) :
  Lambda.subst_code' s_code t_code x = eval_ecf (Lambda.subst_ecf s_code t_code) x := by
  revert s_code x
  refine Nat.strong_induction_on t_code ?_
  intro t_code ih s_code x
  cases hp : t_code.unpair with
  | mk tag data =>
      by_cases h0 : tag = 0
      · subst h0
        have hcode :
            Lambda.subst_code' s_code t_code x =
              if x = data then Lambda.lift_code s_code data 0
              else if data > x then Lambda.var_code (data - 1) else Lambda.var_code data := by
          rw [Lambda.subst_code', Nat.strongRecOn_eq]
          by_cases hxd : x = data
          · simp [hp, hxd]
          · simp [hp, Lambda.var_code, hxd]
        have hecf : Lambda.subst_ecf s_code t_code = mk_var_ecf s_code data := by
          rw [Lambda.subst_ecf, Nat.strongRecOn_eq]
          simp [hp]
        rw [hcode, hecf, eval_ecf_mk_var_ecf]
      · by_cases h1 : tag = 1
        · subst h1
          let t1_code := data.unpair.1
          let t2_code := data.unpair.2
          have hm : data.unpair = (t1_code, t2_code) := by
            simp [t1_code, t2_code]
          have hlt1 : t1_code < t_code := Lambda.decode_lt_1 hp hm
          have hlt2 : t2_code < t_code := Lambda.decode_lt_2 hp hm
          have hcode :
              Lambda.subst_code' s_code t_code x =
                Lambda.app_code (Lambda.subst_code' s_code t1_code x)
                    (Lambda.subst_code' s_code t2_code x) := by
            rw [Lambda.subst_code', Nat.strongRecOn_eq]
            simp only [hp, h0, ↓reduceDIte, app_code, gt_iff_lt, dite_eq_ite,
              Nat.pair_eq_pair, true_and, t1_code, t2_code]
            exact And.intro rfl rfl
          have hecf :
              Lambda.subst_ecf s_code t_code = mk_app_ecf (Lambda.subst_ecf s_code t1_code)
                  (Lambda.subst_ecf s_code t2_code) := by
            rw [Lambda.subst_ecf, Nat.strongRecOn_eq]
            simp only [hp, one_ne_zero, ↓reduceDIte, dite_eq_ite, t1_code, t2_code]
            exact rfl
          rw [hcode, hecf, eval_ecf_mk_app_ecf, ih t1_code hlt1 s_code x, ih t2_code hlt2 s_code x]
        · by_cases h2 : tag = 2
          · subst h2
            let t'_code := data
            have hlt : t'_code < t_code := Lambda.decode_lt_3 hp
            have hcode :
                Lambda.subst_code' s_code t_code x = Lambda.lam_code
                    (Lambda.subst_code' s_code t'_code (x + 1)) := by
              rw [Lambda.subst_code', Nat.strongRecOn_eq]
              simp [hp, h0, h1, t'_code, Lambda.lam_code, Lambda.subst_code']
            have hecf : Lambda.subst_ecf s_code t_code = mk_lam_ecf
                (Lambda.subst_ecf s_code t'_code) := by
              rw [Lambda.subst_ecf, Nat.strongRecOn_eq]
              simp [hp, t'_code, Lambda.subst_ecf]
            rw [hcode, hecf, eval_ecf_mk_lam_ecf, ih t'_code hlt s_code (x + 1)]
          · have h0' : (Nat.unpair t_code).1 ≠ 0 := by simpa [hp] using h0
            have h1' : (Nat.unpair t_code).1 ≠ 1 := by simpa [hp] using h1
            have h2' : (Nat.unpair t_code).1 ≠ 2 := by simpa [hp] using h2
            rw [Lambda.subst_code', Lambda.subst_ecf]
            rw [Nat.strongRecOn_eq, Nat.strongRecOn_eq]
            simp [hp, h0, h1, h2, eval_ecf]

theorem Lambda.subst_code_uncurried_primrec : Primrec Lambda.subst_code_uncurried := by
  rw [Primrec]
  let f : (ℕ × ℕ × ℕ) → ECF := fun v => Lambda.subst_ecf v.1 v.2.1
  let g : (ℕ × ℕ × ℕ) → ℕ := fun v => v.2.2
  have hf : Primrec f := Lambda.subst_ecf_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  have hg : Primrec g := Primrec.snd.comp Primrec.snd
  have : Lambda.subst_code_uncurried = fun v => eval_ecf (f v) (g v) := by
    funext v
    simp only [Lambda.subst_code_uncurried, f, g]
    rw [Lambda.subst_code'_eq_eval_subst_ecf]
  rw [this]
  exact eval_ecf_primrec.comp hf hg

def Lambda.step_code_case1'_beta (c1 c2 : ℕ) : Option (Option ℕ) :=
  some (some (Lambda.subst_code' c2 c1.unpair.2 0))

theorem Lambda.step_code_case1'_beta_primrec : Primrec₂ Lambda.step_code_case1'_beta := by
  -- The function `step_code_case1'_beta` is equivalent to `Lambda.subst_code_uncurried` with some
  -- compositions, which are primitive recursive by assumption.
  have h_step_code_case1'_beta_primrec : Primrec₂
      (fun (c1 c2 : ℕ) => Lambda.subst_code_uncurried (c2, c1.unpair.2, 0)) := by
    refine Primrec.comp ?_ ?_;
    · exact Lambda.subst_code_uncurried_primrec;
    · exact Primrec.pair ( Primrec.snd ) ( Primrec.pair ( Primrec.snd.comp ( Primrec.unpair.comp
        Primrec.fst ) ) ( Primrec.const 0 ) );
  exact Primrec.option_some.comp ( Primrec.option_some.comp h_step_code_case1'_beta_primrec )




def Lambda.step_code_case1'_inner_combined (L : List (Option ℕ)) (c1 c2 : ℕ) : Option (Option ℕ) :=
  if c1.unpair.1 = 2 then
    Lambda.step_code_case1'_beta c1 c2
  else
    (L[c1]?).bind (Lambda.step_code_case1_inner L c1 c2)

theorem Lambda.step_code_case1'_inner_combined_primrec :
    Primrec (fun x : (List (Option ℕ) × ℕ × ℕ) => Lambda.step_code_case1'_inner_combined x.1 x.2.1
        x.2.2) := by
  unfold Lambda.step_code_case1'_inner_combined
  refine Primrec.ite ?_ ?_ ?_
  · exact Primrec.eq.comp
      ( Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.fst.comp ( Primrec.snd ) ) ) )
      ( Primrec.const 2 )
  · exact Primrec₂.comp Lambda.step_code_case1'_beta_primrec
      ( Primrec.fst.comp Primrec.snd ) ( Primrec.snd.comp Primrec.snd )
  · refine Primrec.option_bind ?_ ?_
    · -- The function `get?` is primitive recursive.
      exact Primrec.list_getElem?.comp Primrec.fst ( Primrec.fst.comp Primrec.snd )
    · exact Lambda.step_code_case1_inner_primrec

theorem Lambda.step_code_case1'_eq (L : List (Option ℕ)) :
  Lambda.step_code_case1' L =
  let c := L.length
  let m := c.unpair.2
  let (c1, c2) := m.unpair
  if c1 < c ∧ c2 < c then
    Lambda.step_code_case1'_inner_combined L c1 c2
  else none := by
    unfold step_code_case1' step_code_case1'_inner_combined;
    unfold step_code_case1_inner;
    unfold step_code_case1'_beta step_code_case1_right;
    grind

theorem Lambda.step_code_case1'_primrec : Primrec Lambda.step_code_case1' := by
  -- By definition of `step_code_case1'`, we can rewrite it using the equality lemma
  -- `step_code_case1'_eq`.
  have h_eq : step_code_case1' = fun L => let c := L.length; let m := c.unpair.2; let (c1, c2) :=
      m.unpair; if c1 < c ∧ c2 < c then Lambda.step_code_case1'_inner_combined L c1 c2 else none :=
      by
    funext L; exact (by
    -- Apply the equality lemma `step_code_case1'_eq` to rewrite the goal in terms of
    -- `step_code_case1'_inner_combined`.
    apply Eq.symm; exact (by
    convert Eq.symm ( Lambda.step_code_case1'_eq L ) using 1));
  convert Primrec.ite _ _ _;
  · -- The length of a list is primitive recursive.
    have h_length_primrec : Primrec (fun L : List (Option ℕ) => L.length) := by
      exact Primrec.list_length;
    -- The function that checks if the unpair of the length of a list satisfies the conditions is
    -- primitive recursive because it is constructed using primitive recursive operations.
    have h_conditions_primrec : Primrec
        (fun L : List (Option ℕ) => (Nat.unpair (Nat.unpair L.length).2).1) ∧ Primrec
        (fun L : List (Option ℕ) => (Nat.unpair (Nat.unpair L.length).2).2) := by
      constructor;
      · exact Primrec.fst.comp
          ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair.comp h_length_primrec ) ) );
      · exact Primrec.comp
          ( show Primrec ( fun x : ℕ => ( Nat.unpair x ).2 ) from by
              exact Primrec.snd.comp ( by exact Primrec.unpair ) )
          ( show Primrec ( fun x : ℕ => ( Nat.unpair x ).2 ) from by
              exact Primrec.snd.comp ( by exact Primrec.unpair ) )
          |> Primrec.comp <| h_length_primrec;
    have h_conditions_primrec : PrimrecPred
        (fun L : List (Option ℕ) => (Nat.unpair (Nat.unpair L.length).2).1 < L.length) ∧ PrimrecPred
        (fun L : List (Option ℕ) => (Nat.unpair (Nat.unpair L.length).2).2 < L.length) := by
      exact ⟨Primrec.nat_lt.comp h_conditions_primrec.1 h_length_primrec,
        Primrec.nat_lt.comp h_conditions_primrec.2 h_length_primrec⟩
    exact h_conditions_primrec.1.and h_conditions_primrec.2;
  · -- The function that takes L, gets c1 and c2 from the unpair of L.length, and then applies
    -- step_code_case1'_inner_combined is primitive recursive because it's a composition of
    -- primitive recursive functions.
    have h_comp : Primrec (fun L : List (Option ℕ) => (L, (Nat.unpair (Nat.unpair L.length).2).1,
        (Nat.unpair (Nat.unpair L.length).2).2)) := by
      have h_transform : Primrec (fun L : List (Option ℕ) => (L, L.length.unpair.2)) := by
        -- The function that maps a list to a pair consisting of the list and the second element of
        -- its length's unpair is primitive recursive.
        have h_unpair : Primrec (fun L : List (Option ℕ) => (Nat.unpair L.length).2) := by
          exact Primrec.comp ( Primrec.snd ) ( Primrec.unpair.comp ( Primrec.list_length ) );
        exact Primrec.pair ( Primrec.id ) h_unpair;
      have h_transform : Primrec (fun p : List (Option ℕ) × ℕ => (p.1, p.2.unpair.1, p.2.unpair.2))
          := by
        exact Primrec.pair ( Primrec.fst ) ( Primrec.unpair.comp ( Primrec.snd ) );
      convert h_transform.comp ‹Primrec
          ( fun L : List ( Option ℕ ) => ( L, ( Nat.unpair L.length ).2 ) ) › using 1;
    convert Lambda.step_code_case1'_inner_combined_primrec.comp h_comp using 1;
  · exact Primrec.const none


theorem Lambda.step_code'_eq (L : List (Option ℕ)) :
  Lambda.step_code' L =
  if L.length.unpair.1 = 0 then some none
  else if L.length.unpair.1 = 1 then Lambda.step_code_case1' L
  else if L.length.unpair.1 = 2 then Lambda.step_code_case2 L
  else some none := by
    unfold step_code';
    cases h : Nat.unpair L.length ; aesop

theorem Lambda.step_code'_primrec : Primrec Lambda.step_code' := by
  have h_step_code_case1' : Primrec Lambda.step_code_case1' := by
    -- Apply the hypothesis that `Lambda.step_code_case1'` is primitive recursive.
    apply Lambda.step_code_case1'_primrec;
  -- The function `step_code'` is defined using `ite` and the three cases.
  have h_step_code' : Primrec (fun L : List (Option ℕ) => ite (L.length.unpair.1 = 0) (some none)
      (ite (L.length.unpair.1 = 1) (Lambda.step_code_case1' L) (ite (L.length.unpair.1 = 2)
      (Lambda.step_code_case2 L) (some none)))) := by
    have h_step_code_case2 : Primrec Lambda.step_code_case2 := by
      convert Lambda.step_code_case2_primrec;
    apply_rules [ Primrec.ite, Primrec.const ];
    · -- The function `Nat.unpair` is primitive recursive, and the length of a list is also
      -- primitive recursive. Therefore, their composition is primitive recursive.
      have h_unpair : Primrec (fun n => (Nat.unpair n).1) := by
        exact Primrec.fst.comp Primrec.unpair;
      exact Primrec.eq.comp ( h_unpair.comp ( Primrec.list_length ) ) ( Primrec.const 0 );
    · -- The function that takes a list and returns the first element of the unpair of its length is
      -- primitive recursive.
      have h_primrec : Primrec (fun a : List (Option ℕ) => (Nat.unpair a.length).1) := by
        exact Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.list_length ) );
      exact Primrec.eq.comp h_primrec ( Primrec.const 1 );
    · -- The function that checks if the first component of the unpair of the length of a list is 2
      -- is primitive recursive.
      have h_unpair : Primrec (fun a : List (Option ℕ) => (Nat.unpair a.length).1) := by
        exact Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.list_length ) );
      exact Primrec.eq.comp h_unpair ( Primrec.const 2 );
  unfold Lambda.step_code'; simp_all only;
  convert h_step_code' using 1;
  ext L; rcases L.length.unpair with ⟨ _ | _ | _ | n, m ⟩ <;> tauto;

def Lambda.code_step' (n : ℕ) : Option ℕ :=
  Nat.strongRecOn n (fun n ih => (Lambda.step_code' ((List.range n).attach.map (fun ⟨m, hm⟩ => ih m
      (List.mem_range.1 hm)))).join)

theorem Lambda.code_step'_primrec : Primrec Lambda.code_step' := by
  -- By definition of `code_step'`, it is the composition of `step_code'` and the `join` function.
  set f := fun L : List (Option ℕ) => (Lambda.step_code' L).join;
  -- Since `f` is primitive recursive, `code_step'` is also primitive recursive.
  have hcode_step'_primrec : Primrec f := by
    apply Primrec.option_bind;
    · convert Lambda.step_code'_primrec;
    · exact Primrec.snd;
  convert Primrec.nat_strong_rec _ _;
  rotate_left;
  · exact Unit
  · exact Option ℕ
  all_goals try infer_instance;
  · exact fun _ n => code_step' n
  · exact fun _ L => some ( f L )
  · -- Since `some` is a constant function, and `f` is primitive recursive, their composition is
    -- also primitive recursive.
    have h_some_f_primrec : Primrec (fun L : List (Option ℕ) => some (f L)) := by
      exact Primrec.option_some.comp hcode_step'_primrec;
    exact h_some_f_primrec.comp Primrec.snd;
  · constructor <;> intro h;
    · intro h;
      exact Primrec.comp ( by assumption ) ( Primrec.snd );
    · convert h _;
      · constructor <;> intro h <;> rw [ Primrec₂ ] at * <;>
          simp_all only [Option.some.injEq, forall_const, implies_true];
        · exact h.comp ( Primrec.snd );
        · exact h.comp ( Primrec.const () |> Primrec.pair <| Primrec.id );
      · intros;
        unfold code_step';
        rw [ Nat.strongRecOn_eq ];
        congr! 2;
        refine List.ext_get ?_ ?_ <;> aesop

end
