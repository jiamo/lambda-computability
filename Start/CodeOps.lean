/-
Code-level operations on encoded lambda terms.

This module holds the arithmetization of the syntax: validity of codes,
codes for variables/applications/abstractions/Church numerals, code-level
substitution (`Lambda.subst_code`), code-level beta steps (`Lambda.step_code`,
`Lambda.code_step`), together with their primitive recursiveness proofs.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Tactics
import Start.Syntax
import Start.Reduction
import Start.Encoding
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Sqrt
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Checking the definition of Primcodable.
-/

/-
Checking the type of Primrec.nat_strong_rec.
-/

/-
Definition of is_valid_code.
-/
def Lambda.is_valid_code (n : ℕ) : Bool :=
  Nat.strongRecOn n (fun n ih =>
    match h : n.unpair with
    | (0, _) => true
    | (1, m) =>
      match hm : m.unpair with
      | (c₁, c₂) =>
        have h₁ : c₁ < n := Lambda.decode_lt_1 h hm
        have h₂ : c₂ < n := Lambda.decode_lt_2 h hm
        ih c₁ h₁ && ih c₂ h₂
    | (2, m) =>
      have h' : m < n := Lambda.decode_lt_3 h
      ih m h'
    | _ => false)

/-
Checking for Primrec lemmas related to list access.
-/

/-
Definition of the step function for isValidCode.
-/
def Lambda.isValidCodeStep (L : List Bool) : Option Bool :=
  let n := L.length
  match n.unpair with
  | (0, _) => some true
  | (1, m) =>
    let (c₁, c₂) := m.unpair
    if c₁ < n ∧ c₂ < n then
      match L[c₁]?, L[c₂]? with
      | some b₁, some b₂ => some (b₁ && b₂)
      | _, _ => none
    else none
  | (2, m) =>
    if m < n then
      match L[m]? with
      | some b => some b
      | none => none
    else none
  | _ => some false

/-
Helper functions for the cases of isValidCodeStep.
-/
def Lambda.case1 (L : List Bool) : Option Bool :=
  let n := L.length
  let m := n.unpair.2
  let c₁ := m.unpair.1
  let c₂ := m.unpair.2
  if c₁ < n ∧ c₂ < n then
    match L[c₁]?, L[c₂]? with
    | some b₁, some b₂ => some (b₁ && b₂)
    | _, _ => none
  else none

def Lambda.case2 (L : List Bool) : Option Bool :=
  let n := L.length
  let m := n.unpair.2
  if m < n then
    L[m]?
  else none

/-
Alternative definition of the step function using helper functions.
-/
def Lambda.isValidCodeStep2 (L : List Bool) : Option Bool :=
  let n := L.length
  match n.unpair with
  | (0, _) => some true
  | (1, _) => Lambda.case1 L
  | (2, _) => Lambda.case2 L
  | _ => some false

/-
Lemma: Lambda.case1 is primitive recursive.
-/
theorem Lambda.case1_primrec : Primrec Lambda.case1 := by
  -- The get? function is primitive recursive, so we can use that to get the elements at c₁ and c₂.
  have h_get : Primrec (fun (L : List Bool) => L[L.length.unpair.2.unpair.1]?) := by
    have h_get : Primrec (fun (p : List Bool × ℕ) => p.1[p.2]?) := by
      convert Primrec.list_getElem? using 1;
    have h_unpair : Primrec (fun (n : ℕ) => Nat.unpair n) := by
      exact Primrec.unpair;
    have h_unpair2 : Primrec (fun (n : ℕ) => (Nat.unpair n).2) := by
      exact Primrec.snd.comp h_unpair;
    have h_compose : Primrec (fun (L : List Bool) => (Nat.unpair (Nat.unpair L.length).2).1) := by
      exact Primrec.comp ( show Primrec fun p : ℕ × ℕ => p.1 from Primrec.fst ) ( h_unpair.comp (
          h_unpair2.comp ( show Primrec fun L : List Bool => L.length from by exact
          Primrec.list_length ) ) );
    convert h_get.comp ( Primrec.id.pair h_compose ) using 1;
  have h_get' : Primrec (fun (L : List Bool) => L[L.length.unpair.2.unpair.2]?) := by
    have h_get : Primrec (fun (L : List Bool) => L.length.unpair.2.unpair.2) := by
      have h_fst : Primrec (fun (L : List Bool) => (Nat.unpair L.length).2) := by
        have h_fst : Primrec (fun (n : ℕ) => (Nat.unpair n).2) := by
          exact Primrec.snd.comp ( Primrec.unpair.comp Primrec.id );
        exact h_fst.comp ( Primrec.list_length );
      have h_snd : Primrec (fun (n : ℕ) => (Nat.unpair n).2) := by
        exact Primrec.comp ( Primrec.snd ) ( Primrec.unpair );
      exact h_snd.comp h_fst;
    have h_get : Primrec (fun (x : List Bool × ℕ) => x.1[x.2]?) := by
      norm_num +zetaDelta at *;
      convert Primrec.list_getElem? using 1;
    convert h_get.comp ( Primrec.id.pair ‹Primrec fun ( L : List Bool ) => ( Nat.unpair ( Nat.unpair
        L.length ).2 ).2› ) using 1;
  have h_case1 : Primrec (fun (L : List Bool) => Option.bind (L[L.length.unpair.2.unpair.1]?) (fun
      b₁ => Option.bind (L[L.length.unpair.2.unpair.2]?) (fun b₂ => some (b₁ && b₂)))) := by
    have h_case1 : Primrec (fun (p : Option Bool × Option Bool) => Option.bind p.1 (fun b₁ =>
        Option.bind p.2 (fun b₂ => some (b₁ && b₂)))) := by
      have h_and : Primrec₂ (fun (b₁ b₂ : Bool) => b₁ && b₂) := Primrec.dom_bool₂ _;
      apply Primrec.option_bind;
      · exact Primrec.fst;
      · apply Primrec.option_bind;
        · exact Primrec.snd.comp Primrec.fst;
        · exact (Primrec.option_some.comp (h_and.comp (Primrec.snd.comp Primrec.fst) Primrec.snd));
    exact h_case1.comp ( h_get.pair h_get' );
  convert h_case1 using 1;
  funext L; simp [Lambda.case1];
  by_cases h₁ : ( Nat.unpair ( Nat.unpair L.length ).2 ).1 < L.length <;> by_cases h₂ :
      ( Nat.unpair ( Nat.unpair L.length ).2 ).2 < L.length <;> simp +decide [ h₁, h₂ ]

/-
Lemma: Lambda.case2 is primitive recursive.
-/
theorem Lambda.case2_primrec : Primrec Lambda.case2 := by
  unfold Lambda.case2;
  norm_num +zetaDelta at *;
  have h_case2 : Primrec (fun L : (List Bool) => L[(Nat.unpair L.length).2]?) := by
    have h_snd_unpair : Primrec (fun L : List Bool => (Nat.unpair L.length).2) :=
      Primrec.snd.comp ( Primrec.unpair.comp Primrec.list_length )
    have h_getElem : Primrec (fun (p : List Bool × ℕ) => p.1[p.2]?) :=
      Primrec.list_getElem?
    exact h_getElem.comp (Primrec.id.pair h_snd_unpair)
  grind

/-
Theorem: Lambda.isValidCodeStep2 is primitive recursive.
-/
theorem Lambda.isValidCodeStep2_primrec : Primrec Lambda.isValidCodeStep2 := by
  -- Since Lambda.case1 and Lambda.case2 are primitive recursive, and the match statement can be
  -- decomposed into these, the entire function is primitive recursive.
  have h_case1 : Primrec Lambda.case1 := Lambda.case1_primrec
  have h_case2 : Primrec Lambda.case2 := Lambda.case2_primrec
  have h_cond : ∀ (L : List Bool), Lambda.isValidCodeStep2 L = if L.length.unpair.1 = 0 then some
      true else if L.length.unpair.1 = 1 then Lambda.case1 L else if L.length.unpair.1 = 2 then
      Lambda.case2 L else some false := by
    intro L
    unfold Lambda.isValidCodeStep2
    rcases hL : Nat.unpair L.length with ⟨a, b⟩
    obtain _ | _ | _ | k := a <;> simp [hL]
  rw [ show Lambda.isValidCodeStep2 = _ from funext h_cond ];
  apply_rules [ Primrec.ite, Primrec.const ];
  · have h_case1_case2 : Primrec (fun (L : List Bool) => (Nat.unpair L.length).1) := by
      have h_primrec : Primrec (fun n : ℕ => (Nat.unpair n).1) := by
        exact Primrec.comp ( Primrec.fst ) ( Primrec.unpair );
      exact h_primrec.comp ( Primrec.list_length );
    convert Primrec.eq.comp h_case1_case2 ( Primrec.const 0 ) using 1;
  · -- The first component of the unpair of a number is primitive recursive.
    have h_unpair_fst : Primrec (fun n : ℕ => (Nat.unpair n).1) := by
      exact Primrec.comp ( Primrec.fst ) ( Primrec.unpair );
    exact Primrec.eq.comp ( h_unpair_fst.comp ( show Primrec ( fun L : List Bool => List.length L )
        from by exact Primrec.list_length ) ) ( show Primrec ( fun _ : List Bool => 1 ) from by
        exact Primrec.const 1 );
  · -- The length of a list is primitive recursive, and the unpair function is also primitive
    -- recursive. Therefore, the composition of these functions is primitive recursive.
    have h_unpair : Primrec (fun L : List Bool => Nat.unpair L.length) := by
      have h_len_unpair : Primrec (fun n : ℕ => Nat.unpair n) := by
        exact Primrec.unpair;
      exact h_len_unpair.comp ( Primrec.list_length );
    exact Primrec.eq.comp ( Primrec.fst.comp h_unpair ) ( Primrec.const 2 )

/-
Theorem: Lambda.isValidCodeStep2 is primitive recursive.
-/
theorem Lambda.isValidCodeStep2_primrec' : Primrec Lambda.isValidCodeStep2 := by
  exact Lambda.isValidCodeStep2_primrec

/-
Theorem: Lambda.isValidCodeStep2 is primitive recursive.
-/
theorem Lambda.isValidCodeStep2_primrec_final : Primrec Lambda.isValidCodeStep2 := by
  exact Lambda.isValidCodeStep2_primrec

/-
Lemma: The step function applied to the list of previous values equals the value of the function.
-/
theorem Lambda.is_valid_code_eq_step (n : ℕ) :
  Lambda.isValidCodeStep2 ((List.range n).map Lambda.is_valid_code) = some (Lambda.is_valid_code n)
      := by
    unfold Lambda.isValidCodeStep2 Lambda.case1 Lambda.case2
    unfold Lambda.is_valid_code
    rw [Nat.strongRecOn_eq]
    have hlt1 : ∀ m : ℕ, Nat.unpair n = (1, m) → (Nat.unpair m).1 < n :=
      fun _ h => Lambda.decode_lt_1 h rfl
    have hlt2 : ∀ m : ℕ, Nat.unpair n = (1, m) → (Nat.unpair m).2 < n :=
      fun _ h => Lambda.decode_lt_2 h rfl
    have hlt3 : ∀ m : ℕ, Nat.unpair n = (2, m) → m < n :=
      fun _ h => Lambda.decode_lt_3 h
    aesop

/-
Checking if Lambda.is_valid_code exists.
-/

/-
Lemma: The step function applied to the list of previous values equals the value of the function.
-/
theorem Lambda.is_valid_code_eq_step_final (n : ℕ) :
  Lambda.isValidCodeStep2 ((List.range n).map Lambda.is_valid_code) = some (Lambda.is_valid_code n)
      := by
    exact Lambda.is_valid_code_eq_step n

/-
Theorem: Lambda.is_valid_code is primitive recursive.
-/
theorem Lambda.is_valid_code_primrec : Primrec Lambda.is_valid_code := by
  have h_step : Primrec (fun (L : List Bool) => Lambda.isValidCodeStep2 L) :=
      Lambda.isValidCodeStep2_primrec_final
  have h_g_primrec : Primrec₂ (fun (_ : Unit) (L : List Bool) => Lambda.isValidCodeStep2 L) :=
    h_step.comp Primrec.snd
  have h_rec := @Primrec.nat_strong_rec Unit Bool _ _ (fun _ n => Lambda.is_valid_code n) _
      h_g_primrec (fun _ n => Lambda.is_valid_code_eq_step_final n)
  exact h_rec.comp (Primrec.const ()) Primrec.id


/-
Check definitions of Partrec, TM2Computable, and Lambda.church.
-/
-- #check Turing.TM2Computable

/-
`Lambda.app_code` encodes the application of two Lambda terms. It is primitive recursive.
-/
def Lambda.app_code (c₁ c₂ : ℕ) : ℕ := Nat.pair 1 (Nat.pair c₁ c₂)

theorem Lambda.app_code_primrec : Primrec₂ Lambda.app_code := by
  exact Primrec₂.natPair.comp ( Primrec₂.const 1 ) ( Primrec₂.natPair )

/-
`Lambda.body_code` constructs the body of a Church numeral. It is primitive recursive.
-/
def Lambda.body_code (n : ℕ) : ℕ :=
  Nat.rec (Nat.pair 0 0) (fun _ c => Lambda.app_code (Nat.pair 0 1) c) n

theorem Lambda.body_code_primrec : Primrec Lambda.body_code := by
  unfold Lambda.body_code
  exact Primrec.nat_rec₁ _ (Lambda.app_code_primrec.comp (Primrec.const _) Primrec.snd)

/-
`Lambda.church_code` encodes a Church numeral. It is primitive recursive.
-/
def Lambda.church_code (n : ℕ) : ℕ :=
  Nat.pair 2 (Nat.pair 2 (Lambda.body_code n))

theorem Lambda.church_code_primrec : Primrec Lambda.church_code := by
  unfold church_code;
  have h_composition : Primrec (fun n => Nat.pair 2 (Nat.pair 2 n)) := by
    have h_pair_primrec : Primrec₂ Nat.pair := by
      apply Primrec₂.natPair;
    exact h_pair_primrec.comp ( Primrec.const _ )
        ( h_pair_primrec.comp ( Primrec.const _ ) ( Primrec.id ) );
  convert h_composition.comp ( Lambda.body_code_primrec ) using 1

/-
The encoding of the Church numeral for `n` is equal to `Lambda.church_code n`.
-/
theorem Lambda.encode_church_eq_church_code (n : ℕ) :
    Lambda.encode (Lambda.church n) = Lambda.church_code n := by
  -- Since the application is already in the form of a pair, the encoding of the application is
  -- trivially equal to the encoding of the Church numeral.
  simp only [church_code, body_code, app_code]
  -- By definition of encode, we can expand the right-hand side.
  simp only [church, encode, Nat.pair_eq_pair, true_and]
  induction n <;>
    simp_all +decide only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [ ← ‹ ( List.foldl ( fun t x => ( var 1 ).app t ) ( var 0 ) ( List.range _ ) ).encode = Nat.rec
      ( Nat.pair 0 0 ) ( fun x c => Nat.pair 1 ( Nat.pair ( Nat.pair 0 1 ) c ) ) _ › ];
  rfl

/-
`Lambda.lam_code` encodes a lambda abstraction. It is primitive recursive.
-/
def Lambda.lam_code (c : ℕ) : ℕ := Nat.pair 2 c

theorem Lambda.lam_code_primrec : Primrec Lambda.lam_code := by
  unfold Lambda.lam_code;
  -- The function c => Nat.pair 2 c is primitive recursive because it is the composition of the
  -- constant function 2 and the identity function, both of which are primitive recursive.
  have h_const : Primrec (fun _ : ℕ => 2) := by
    exact Primrec.const 2;
  exact Primrec.pair h_const Primrec.id

/-
Check the type of Primrec.nat_strong_rec.
-/

/-
`Lambda.subst_code_case0` handles the variable case for substitution. It is primitive recursive.
-/
def Lambda.subst_code_case0 (sx : ℕ × ℕ) (t_code : ℕ) (y : ℕ) : ℕ :=
  if sx.2 = y then sx.1 else t_code

theorem Lambda.subst_code_case0_primrec :
    Primrec (fun x : (ℕ × ℕ) × ℕ × ℕ => Lambda.subst_code_case0 x.1 x.2.1 x.2.2) := by
  apply_rules [ Primrec.ite, Primrec.eq ];
  · -- The equality function is primitive recursive.
    apply Primrec.eq.comp (Primrec.snd.comp (Primrec.fst)) (Primrec.snd.comp (Primrec.snd));
  · exact Primrec.fst.comp ( Primrec.fst );
  · exact Primrec.fst.comp ( Primrec.snd.comp ( Primrec.id ) )

/-
Check the type of Primrec.list_getElem?.
-/

/-
`Lambda.subst_code_case1` handles the application case for substitution. It is defined using
`Option.bind`.
-/
def Lambda.subst_code_case1 (L : List ℕ) : Option ℕ :=
  let t_code := L.length
  let m := t_code.unpair.2
  let (t1_code, t2_code) := m.unpair
  if t1_code < t_code ∧ t2_code < t_code then
    (L[t1_code]?).bind
        (fun res1 => (L[t2_code]?).bind (fun res2 => some (Lambda.app_code res1 res2)))
  else none

/-
`Lambda.subst_code_case1` handles the application case for substitution. It is primitive recursive.
-/
theorem Lambda.subst_code_case1_primrec : Primrec Lambda.subst_code_case1 := by
  -- The `subst_code_case1` function is primitive recursive because it is constructed using
  -- primitive recursive functions and operations.
  have h_case1 : Primrec (fun L : List ℕ => L[L.length.unpair.2.unpair.1]? >>= fun res1 =>
      L[L.length.unpair.2.unpair.2]? >>= fun res2 => some (Lambda.app_code res1 res2)) := by
    apply_rules [ Primrec.option_bind, Primrec.option_map, Primrec.list_getElem? ];
    · -- The `get?` function is primitive recursive because it is a basic list operation.
      have h_get_primrec : Primrec (fun (p : List ℕ × ℕ) => p.1[p.2]?) := by
        convert Primrec.list_getElem? using 1;
      convert h_get_primrec.comp _ using 1;
      rotate_left;
      · exact fun a => ( a, ( Nat.unpair ( Nat.unpair a.length ).2 ).1 )
      · apply Primrec.pair;
        · exact Primrec.id;
        · -- The function that takes a list of natural numbers and returns the first element of the
          -- pair obtained by unpairing the second element of the pair obtained by unpairing the
          -- length of the list is primitive recursive.
          have h_unpair : Primrec (fun (n : ℕ) => (Nat.unpair (Nat.unpair n).2).1) := by
            exact Primrec.fst.comp
                ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.id ) ) ) );
          exact h_unpair.comp ( Primrec.list_length );
      · rfl;
    · have h_get_second : Primrec (fun a : List ℕ => a[(Nat.unpair (Nat.unpair a.length).2).2]?) :=
        by
        have h_unpair : Primrec (fun a : ℕ => Nat.unpair a) := by
          exact Primrec.unpair
        have h_get : Primrec (fun a : List ℕ × ℕ => a.1[a.2]?) := by
          norm_num +zetaDelta at *;
          convert Primrec.list_getElem?
        have h_comp : Primrec (fun a : List ℕ => (a, (Nat.unpair (Nat.unpair a.length).2).2)) := by
          have h_comp : Primrec (fun a : ℕ => (Nat.unpair (Nat.unpair a).2).2) := by
            exact Primrec.snd.comp ( h_unpair.comp ( Primrec.snd.comp h_unpair ) );
          exact Primrec.pair ( Primrec.id ) ( h_comp.comp ( Primrec.list_length ) );
        exact h_get.comp h_comp;
      exact h_get_second.comp ( Primrec.fst );
    · -- The function that returns the application code of the second element and a given number is
      -- primitive recursive.
      apply Primrec.option_some.comp;
      exact Lambda.app_code_primrec.comp ( Primrec.snd.comp ( Primrec.fst.comp Primrec.id ) )
          ( Primrec.snd.comp Primrec.id );
  refine Primrec.of_eq (h_case1.comp Primrec.id) ?_
  unfold subst_code_case1; simp_all
  grind

/-
`Lambda.subst_code_case2` handles the lambda abstraction case for substitution. It is defined using
`Option.bind`.
-/
def Lambda.subst_code_case2 (L : List ℕ) : Option ℕ :=
  let t_code := L.length
  let t'_code := t_code.unpair.2
  if t'_code < t_code then
    (L[t'_code]?).bind (fun res => some (Lambda.lam_code res))
  else none

/-
`Lambda.subst_code_case2` handles the lambda abstraction case for substitution. It is primitive
recursive.
-/
theorem Lambda.subst_code_case2_primrec : Primrec Lambda.subst_code_case2 := by
  -- The function `subst_code_case2` is defined using `Option.bind`, which is primitive recursive.
  have h_bind : Primrec (fun (x : List ℕ) => Option.bind (x[x.length.unpair.2]?) (fun res => some
      (Lambda.lam_code res))) := by
    apply Primrec.option_bind;
    · have h_get? : Primrec (fun (x : List ℕ) => x[(Nat.unpair x.length).2]?) := by
        have h_list_get? : Primrec (fun (x : List ℕ) => x[(Nat.unpair x.length).2]?) := by
          have h_list_get? : Primrec (fun (x : List ℕ × ℕ) => x.1[x.2]?) := by
            convert Primrec.list_getElem? using 1;
          have h_unpair : Primrec (fun (x : List ℕ) => (Nat.unpair x.length).2) := by
            have h_unpair : Primrec (fun (x : ℕ) => (Nat.unpair x).2) := by
              exact Primrec.snd.comp
                  ( show Primrec fun x => Nat.unpair x from by
                      exact Primrec.unpair.comp
                        ( show Primrec fun x => x from by exact Primrec.id ) );
            exact h_unpair.comp ( Primrec.list_length );
          exact h_list_get?.comp ( Primrec.id.pair h_unpair )
        exact h_list_get?;
      exact h_get?;
    · apply Primrec.option_some.comp;
      exact Primrec.comp ( show Primrec fun a => Lambda.lam_code a from Lambda.lam_code_primrec )
          ( Primrec.snd );
  convert h_bind using 1;
  funext x; simp [subst_code_case2];
  cases x <;> aesop

/-
`Lambda.subst_code_step` is the step function for computing substitution codes, defined using helper
functions.
-/
def Lambda.subst_code_step (sx : ℕ × ℕ) (L : List ℕ) : Option ℕ :=
  let t_code := L.length
  match t_code.unpair with
  | (0, y) => some (Lambda.subst_code_case0 sx t_code y)
  | (1, _) => Lambda.subst_code_case1 L
  | (2, _) => Lambda.subst_code_case2 L
  | _ => some 0

/-
`Lambda.subst_code_step` is primitive recursive. This follows from the primitive recursiveness of
its cases.
-/
theorem Lambda.subst_code_step_primrec : Primrec₂ Lambda.subst_code_step := by
  -- The step function is primitive recursive.
  have step_primrec : Primrec (fun x : (ℕ × ℕ) × List ℕ => Lambda.subst_code_step x.1 x.2) := by
    -- We'll use the fact that `subst_code_step` is defined using primitive recursive functions.
    have h_step_primrec : Primrec (fun p : (ℕ × ℕ) × List ℕ => match p with
      | (y, l) => let n := l.length; match n.unpair with
      | (0, m) => some (subst_code_case0 y n m)
      | (1, m) => subst_code_case1 l
      | (2, m) => subst_code_case2 l
      | _ => some 0) := by
        -- Each case in the match expression is handled by a primitive recursive function.
        have h_cases : Primrec (fun p : (ℕ × ℕ) × List ℕ => match p with
          | (y, l) => let n := l.length; match n.unpair with
          | (0, m) => some (subst_code_case0 y n m)
          | (1, m) => subst_code_case1 l
          | (2, m) => subst_code_case2 l
          | _ => some 0) := by
          have h_case0 : Primrec (fun p : (ℕ × ℕ) × List ℕ => some (subst_code_case0 p.1 p.2.length
              (p.2.length.unpair.2))) := by
            apply_rules [ Primrec.option_some, Primrec.comp ];
            convert Lambda.subst_code_case0_primrec using 1;
            constructor <;> intro h;
            · convert Lambda.subst_code_case0_primrec using 1;
            · convert h.comp _ using 1;
              rotate_left;
              · exact fun x => ( x.1, x.2.length, ( Nat.unpair x.2.length ).2 )
              · -- The length of a list is primitive recursive.
                have h_len : Primrec (fun x : List ℕ => x.length) := by
                  exact Primrec.list_length;
                exact Primrec.pair ( Primrec.fst ) ( Primrec.pair ( h_len.comp ( Primrec.snd ) ) (
                    Primrec.comp ( Primrec.snd ) ( Primrec.unpair.comp ( h_len.comp ( Primrec.snd )
                    ) ) ) );
              · rfl
          have h_case1 : Primrec (fun p : (ℕ × ℕ) × List ℕ => subst_code_case1 p.2) := by
            convert Lambda.subst_code_case1_primrec using 1;
            constructor <;> intro h;
            · convert Lambda.subst_code_case1_primrec using 1;
            · exact h.comp ( Primrec.snd )
          have h_case2 : Primrec (fun p : (ℕ × ℕ) × List ℕ => subst_code_case2 p.2) := by
            convert Lambda.subst_code_case2_primrec using 1;
            constructor;
            · exact fun _ => Lambda.subst_code_case2_primrec;
            · exact fun h => h.comp ( Primrec.snd )
          have h_case3 : Primrec (fun p : (ℕ × ℕ) × List ℕ => some 0) := by
            exact Primrec.const _;
          convert Primrec.of_eq _ _;
          · exact fun p => if p.2.length.unpair.1 = 0 then some
                ( subst_code_case0 p.1 p.2.length ( p.2.length.unpair.2 ) ) else if
                p.2.length.unpair.1 = 1 then subst_code_case1 p.2 else
                if p.2.length.unpair.1 = 2 then subst_code_case2 p.2 else some 0
          · apply_rules [ Primrec.ite, Primrec.const ];
            · convert Primrec.eq.comp ( show Primrec ( fun p : ( ℕ × ℕ ) × List ℕ => ( Nat.unpair
                p.2.length ).1 ) from ?_ ) ( show Primrec ( fun p : ( ℕ × ℕ ) × List ℕ => 0 ) from
                ?_ ) using 1;
              · have h_unpair : Primrec (fun p : ℕ => (Nat.unpair p).1) := by
                  exact Primrec.fst.comp ( Primrec.unpair );
                exact h_unpair.comp ( Primrec.list_length.comp ( Primrec.snd ) );
              · exact Primrec.const 0;
            · -- The function that returns the first component of the unpair of the length of the
              -- list is primitive recursive.
              have h_first_comp : Primrec (fun p : (ℕ × ℕ) × List ℕ => (Nat.unpair p.2.length).1) :=
                  by
                have h_cond : Primrec (fun p : List ℕ => (Nat.unpair p.length).1) := by
                  have h_cond : Primrec (fun p : ℕ => (Nat.unpair p).1) := by
                    exact Primrec.fst.comp ( Primrec.unpair );
                  exact h_cond.comp ( Primrec.list_length );
                exact h_cond.comp ( Primrec.snd );
              exact Primrec.eq.comp h_first_comp ( Primrec.const 1 );
            · convert Primrec.eq.comp ( show Primrec ( fun p : ( ℕ × ℕ ) × List ℕ => ( Nat.unpair
                p.2.length ).1 ) from ?_ ) ( show Primrec ( fun _ : ( ℕ × ℕ ) × List ℕ => 2 ) from
                ?_ ) using 1;
              · -- The length of the list is a primitive recursive function.
                have h_len : Primrec (fun l : List ℕ => l.length) := by
                  exact Primrec.list_length;
                exact Primrec.fst.comp ( Primrec.unpair.comp ( h_len.comp ( Primrec.snd ) ) );
              · exact Primrec.const 2;
          · intro n; rcases n with ⟨ ⟨ y, l ⟩, m ⟩ ; rcases n : Nat.unpair m.length with ⟨ a, b ⟩ ;
              aesop;
        exact h_cases;
    convert h_step_primrec using 1;
  exact step_primrec

/-
`Lambda.subst_code` computes the code of `t[x := s]` given the codes of `s`, `x`, and `t`.
-/
def Lambda.subst_code (s_code x t_code : ℕ) : ℕ :=
  Nat.strongRecOn t_code (fun t_code ih =>
    match h : t_code.unpair with
    | (0, y) => if x = y then s_code else t_code
    | (1, m) =>
      match hm : m.unpair with
      | (t1_code, t2_code) =>
        have h1 : t1_code < t_code := Lambda.decode_lt_1 h hm
        have h2 : t2_code < t_code := Lambda.decode_lt_2 h hm
        Lambda.app_code (ih t1_code h1) (ih t2_code h2)
    | (2, t'_code) =>
      have h' : t'_code < t_code := Lambda.decode_lt_3 h
      Lambda.lam_code (ih t'_code h')
    | _ => 0
  )

/-
Accessing the `m`-th element of the list of substitution codes for `0` to `n-1` returns the
substitution code for `m`, provided `m < n`.
-/
theorem Lambda.subst_code_list_get (s_code x n m : ℕ) (h : m < n) :
  ((List.range n).map (Lambda.subst_code s_code x))[m]? = some (Lambda.subst_code s_code x m) := by
    cases m <;> aesop

/-
The step function `Lambda.subst_code_step` correctly computes the next value of `Lambda.subst_code`
given the list of previous values. Use `Lambda.subst_code_list_get`.
-/
theorem Lambda.subst_code_eq_step (s_code x n : ℕ) :
  Lambda.subst_code_step (s_code, x) ((List.range n).map (Lambda.subst_code s_code x)) = some
      (Lambda.subst_code s_code x n) := by
    unfold Lambda.subst_code_step Lambda.subst_code_case1 Lambda.subst_code_case2
    unfold Lambda.subst_code
    rw [Nat.strongRecOn_eq]
    have hlt1 : ∀ m : ℕ, Nat.unpair n = (1, m) → (Nat.unpair m).1 < n :=
      fun _ h => Lambda.decode_lt_1 h rfl
    have hlt2 : ∀ m : ℕ, Nat.unpair n = (1, m) → (Nat.unpair m).2 < n :=
      fun _ h => Lambda.decode_lt_2 h rfl
    have hlt3 : ∀ m : ℕ, Nat.unpair n = (2, m) → m < n :=
      fun _ h => Lambda.decode_lt_3 h
    aesop

/-
`Lambda.subst_code` is primitive recursive. This is proven using `Primrec.nat_strong_rec` and the
helper function `Lambda.subst_code_step`.
-/
theorem Lambda.subst_code_primrec :
    Primrec (fun (v : ℕ × ℕ × ℕ) => Lambda.subst_code v.1 v.2.1 v.2.2) := by
  have h_subst_code_primrec : Primrec₂ (fun (sx : ℕ × ℕ) (n : ℕ) => Lambda.subst_code sx.1 sx.2 n)
      := by
    -- Apply the primrecitivity of `Primrec.nat_strong_rec` with the primitive recursive step
    -- function `Lambda.subst_code_step`.
    exact Primrec.nat_strong_rec _ Lambda.subst_code_step_primrec
      (fun a n => Lambda.subst_code_eq_step a.1 a.2 n)
  convert h_subst_code_primrec.comp _ _ using 1;
  rotate_left;
  · exact fun v => ( v.1, v.2.1 )
  · exact fun v => v.2.2
  · exact Primrec.pair ( Primrec.fst ) ( Primrec.fst.comp ( Primrec.snd ) );
  · exact Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) );
  · rfl

/-
`Lambda.step_code_case1` handles the application case for reduction. It takes a list of previous
results (which are `Option ℕ`) and returns the result for the current code (wrapped in `Option` for
the step function).
-/
def Lambda.step_code_case1 (L : List (Option ℕ)) : Option (Option ℕ) :=
  let c := L.length
  let m := c.unpair.2
  let (c1, c2) := m.unpair
  if c1 < c ∧ c2 < c then
    match c1.unpair with
    | (2, c1_body) => some (some (Lambda.subst_code c2 0 c1_body))
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

/-
`Lambda.step_code_case2` handles the lambda abstraction case for reduction. It takes a list of
previous results and returns the result for the current code.
-/
def Lambda.step_code_case2 (L : List (Option ℕ)) : Option (Option ℕ) :=
  let c := L.length
  let c' := c.unpair.2
  if c' < c then
    (L[c']?).bind (fun res =>
      match res with
      | some c'' => some (some (Lambda.lam_code c''))
      | none => some none
    )
  else none

/-
`Lambda.step_code_case2_inner` is a helper function for `Lambda.step_code_case2`. It is primitive
recursive.
-/
def Lambda.step_code_case2_inner (res : Option ℕ) : Option (Option ℕ) :=
  match res with
  | some c'' => some (some (Lambda.lam_code c''))
  | none => some none

theorem Lambda.step_code_case2_inner_primrec : Primrec Lambda.step_code_case2_inner := by
  unfold step_code_case2_inner;
  have h_step_case2_inner_primrec : Primrec (fun (res : Option ℕ) =>
      match res with
      | some c'' => some (some (Lambda.lam_code c''))
      | none => some none) := by
    have h_lam_code_primrec : Primrec (fun (c'' : ℕ) => Lambda.lam_code c'') := by
      exact Lambda.lam_code_primrec.comp ( Primrec.id )
    have h_step_case2_inner_primrec : Primrec (fun (res : Option ℕ) =>
        match res with
        | some c'' => some (Lambda.lam_code c'')
        | none => none) := by
      -- The match expression is a case split on the Option type, which is handled by the
      -- Primrec.split function.
      have h_match_primrec : Primrec (fun (res : Option ℕ) =>
          match res with
          | some c'' => some (Lambda.lam_code c'')
          | none => none) := by
        have h_match : Primrec (fun (res : Option ℕ) =>
            match res with
            | some c'' => some (Lambda.lam_code c'')
            | none => none) := by
          have h_split : Primrec (fun (res : Option ℕ) => res) := by
            exact Primrec.id
          convert h_split.option_map _ using 1;
          rotate_left;
          · exact fun res c'' => lam_code c''
          · exact h_lam_code_primrec.comp ( Primrec.snd );
          · exact funext fun x => by cases x <;> rfl;
        exact h_match;
      exact h_match_primrec;
    convert Primrec.option_some.comp h_step_case2_inner_primrec using 1;
    exact funext fun x => by cases x <;> rfl;
  exact h_step_case2_inner_primrec


/-
Checking Primrec.option_bind₁
-/

/-
Helper function for the right application case of step code, and its Primrec proof.
-/
def Lambda.step_code_case1_right (c1 : ℕ) (res2 : Option ℕ) : Option (Option ℕ) :=
  match res2 with
  | some c2' => some (some (Lambda.app_code c1 c2'))
  | none => some none

theorem Lambda.step_code_case1_right_primrec : Primrec₂ Lambda.step_code_case1_right := by
  -- Apply the fact that `Option.bind` is primitive recursive.
  have h_opt_bind : Primrec₂ (fun (res2 : Option ℕ) (c1 : ℕ) =>
      match res2 with
      | some c2' => some (some (Lambda.app_code c1 c2'))
      | none => some none) := by
    have h_opt_bind : Primrec₂ (fun (res2 : Option ℕ) (c1 : ℕ) =>
        match res2 with
        | some c2' => some (Lambda.app_code c1 c2')
        | none => none) := by
      have h_opt_bind : Primrec₂
          (fun (res2 : Option ℕ) (c1 : ℕ) => Option.map (fun c2' => Lambda.app_code c1 c2') res2) :=
          by
        have h_map : Primrec (fun (c : ℕ × ℕ) => Lambda.app_code c.1 c.2) := by
          -- The function `app_code` is defined as `Nat.pair 1 (Nat.pair c₁ c₂)`, which is primitive
          -- recursive because it's a composition of primitive recursive functions.
          apply Lambda.app_code_primrec
        apply_rules [ Primrec.option_map ];
        · exact Primrec.fst;
        · exact h_map.comp ( Primrec.snd.comp Primrec.fst |> Primrec.pair <| Primrec.snd );
      grind
    -- If the function that returns a single wrapped Option is primitive recursive, then the
    -- function that returns a double wrapped Option is also primitive recursive because wrapping an
    -- Option in another Option is a simple operation that can be done with a primitive recursive
    -- function.
    have h_double_wrap : Primrec₂ (fun (res2 : Option ℕ) (c1 : ℕ) => some
        (match res2 with
         | some c2' => some (Lambda.app_code c1 c2')
         | none => none)) := by
      apply Primrec.comp;
      · exact Primrec.option_some;
      · exact h_opt_bind;
    convert h_double_wrap using 1;
    exact funext fun x => funext fun y => by cases x <;> rfl;
  exact h_opt_bind.swap

/-
Checking Primrec.option_casesOn
-/

/-
Helper function for the `some` case of `step_code_case1_inner` and its Primrec proof.
-/
def Lambda.step_code_case1_inner_some_case (c2 : ℕ) (c1' : ℕ) : Option (Option ℕ) :=
  some (some (Lambda.app_code c1' c2))

theorem Lambda.step_code_case1_inner_some_case_primrec :
    Primrec₂ Lambda.step_code_case1_inner_some_case := by
  -- The composition of primitive recursive functions is primitive recursive.
  have h_comp : Primrec₂ (fun (c2 c1' : ℕ) => some (some (Lambda.app_code c1' c2))) := by
    have h_some_some : Primrec (fun (c : ℕ) => some (some c)) := by
      exact Primrec.option_some.comp ( Primrec.option_some.comp ( Primrec.id ) )
    exact h_some_some.comp₂ ( Lambda.app_code_primrec.comp₂ ( Primrec.snd ) ( Primrec.fst ) );
  exact h_comp

/-
Helper function for the `none` case of `step_code_case1_inner` and its Primrec proof.
-/
def Lambda.step_code_case1_inner_none_case (L : List (Option ℕ)) (c1 c2 : ℕ) : Option (Option ℕ) :=
  (L[c2]?).bind (Lambda.step_code_case1_right c1)

theorem Lambda.step_code_case1_inner_none_case_primrec :
    Primrec (fun x : (List (Option ℕ) × ℕ × ℕ) => Lambda.step_code_case1_inner_none_case x.1 x.2.1
        x.2.2) := by
  unfold Lambda.step_code_case1_inner_none_case
  have h_get : Primrec (fun x : List (Option ℕ) × ℕ × ℕ => x.1[x.2.2]?) :=
    Primrec.list_getElem?.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  exact Primrec.option_bind h_get
    (Lambda.step_code_case1_right_primrec.comp₂
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)

/-
Definition of Lambda.step_code_case1_inner.
-/
def Lambda.step_code_case1_inner (L : List (Option ℕ)) (c1 c2 : ℕ) (res1 : Option ℕ) : Option
    (Option ℕ) :=
  match res1 with
  | some c1' => some (some (Lambda.app_code c1' c2))
  | none => (L[c2]?).bind (Lambda.step_code_case1_right c1)

/-
Lambda.step_code_case1_inner is primitive recursive.
-/
theorem Lambda.step_code_case1_inner_primrec :
    Primrec (fun x : (List (Option ℕ) × ℕ × ℕ) × Option ℕ => Lambda.step_code_case1_inner x.1.1
        x.1.2.1 x.1.2.2 x.2) := by
  unfold Lambda.step_code_case1_inner
  have hnone : Primrec (fun x : (List (Option ℕ) × ℕ × ℕ) × Option ℕ =>
      (x.1.1[x.1.2.2]?).bind (Lambda.step_code_case1_right x.1.2.1)) :=
    Lambda.step_code_case1_inner_none_case_primrec.comp Primrec.fst
  have hpair : Primrec₂ (fun a b : ℕ => some (some (Lambda.app_code a b))) :=
    Primrec.option_some.comp (Primrec.option_some.comp Lambda.app_code_primrec)
  have hsome : Primrec₂ (fun (x : (List (Option ℕ) × ℕ × ℕ) × Option ℕ) (c1' : ℕ) =>
      some (some (Lambda.app_code c1' x.1.2.2))) :=
    hpair.comp₂ Primrec₂.right
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  exact Primrec.of_eq (Primrec.option_casesOn Primrec.snd hnone hsome) fun x => by
    cases x.2 <;> rfl

/-
Helper function for the beta reduction case of `step_code_case1` and its Primrec proof.
-/
def Lambda.step_code_case1_beta (c1 c2 : ℕ) : Option (Option ℕ) :=
  some (some (Lambda.subst_code c2 0 c1.unpair.2))

theorem Lambda.step_code_case1_beta_primrec : Primrec₂ Lambda.step_code_case1_beta := by
  have h_subst_code : Primrec (fun p : ℕ × ℕ => subst_code p.1 0 p.2) := by
    have h_subst_code : Primrec (fun p : ℕ × ℕ × ℕ => subst_code p.1 p.2.1 p.2.2) := by
      exact Lambda.subst_code_primrec;
    exact h_subst_code.comp ( Primrec.fst.pair ( Primrec.const 0 |> Primrec.pair <| Primrec.snd ) );
  have h_pair : Primrec (fun p : ℕ × ℕ => (p.2, (Nat.unpair p.1).2)) := by
    exact Primrec.pair ( Primrec.snd )
        ( Primrec.comp ( Primrec.snd ) ( Primrec.unpair.comp ( Primrec.fst ) ) );
  exact Primrec.option_some.comp ( Primrec.option_some.comp ( h_subst_code.comp h_pair ) )

/-
Equality lemma rewriting `Lambda.step_code_case1` in terms of helper functions.
-/
theorem Lambda.step_code_case1_eq (L : List (Option ℕ)) :
  Lambda.step_code_case1 L =
  let c := L.length
  let m := c.unpair.2
  let (c1, c2) := m.unpair
  if c1 < c ∧ c2 < c then
    if c1.unpair.1 = 2 then
      Lambda.step_code_case1_beta c1 c2
    else
      (L[c1]?).bind (Lambda.step_code_case1_inner L c1 c2)
  else none := by
  unfold Lambda.step_code_case1
  rcases hm : Nat.unpair (Nat.unpair L.length).2 with ⟨c1, c2⟩
  simp only [hm]
  by_cases hlt : c1 < L.length ∧ c2 < L.length
  · rw [if_pos hlt, if_pos hlt]
    by_cases ha : (Nat.unpair c1).1 = 2
    · rw [if_pos ha, show Nat.unpair c1 = (2, (Nat.unpair c1).2) from Prod.ext ha rfl]
      rfl
    · rw [if_neg ha]
      unfold Lambda.step_code_case1_inner
      rcases hc1 : Nat.unpair c1 with ⟨a, b⟩
      obtain _ | _ | _ | k := a
      · rfl
      · rfl
      · exact absurd (by rw [hc1]) ha
      · rfl
  · rw [if_neg hlt, if_neg hlt]

/-
Helper function combining the inner logic of `step_code_case1` and its Primrec proof.
-/
def Lambda.step_code_case1_inner_combined (L : List (Option ℕ)) (c1 c2 : ℕ) : Option (Option ℕ) :=
  if c1.unpair.1 = 2 then
    Lambda.step_code_case1_beta c1 c2
  else
    (L[c1]?).bind (Lambda.step_code_case1_inner L c1 c2)

theorem Lambda.step_code_case1_inner_combined_primrec :
    Primrec (fun x : (List (Option ℕ) × ℕ × ℕ) => Lambda.step_code_case1_inner_combined x.1 x.2.1
        x.2.2) := by
  have h_true : Primrec
      (fun x : (List (Option ℕ) × ℕ × ℕ) => Lambda.step_code_case1_beta x.2.1 x.2.2) := by
    apply_rules [ Primrec₂.comp, Primrec₂.curry ];
    any_goals exact Primrec.snd;
    · exact Lambda.step_code_case1_beta_primrec
    all_goals apply_rules [ Primrec.fst, Primrec.snd, Primrec.id, Primrec.const, Primrec.comp ];
  refine h_true.ite ?_ ?_;
  · have h_cond_prim : Primrec (fun x : (List (Option ℕ) × ℕ × ℕ) => (Nat.unpair x.2.1).1) := by
      exact Primrec.comp ( Primrec.fst )
          ( Primrec.comp ( Primrec.unpair ) ( Primrec.fst.comp ( Primrec.snd ) ) );
    exact Primrec.eq.comp ( h_cond_prim ) ( Primrec.const 2 );
  · apply_rules [ Primrec.option_bind, Primrec.nat_casesOn ];
    · -- The function `List.getElem?` is primitive recursive.
      have h_get? : Primrec₂ (fun (L : List (Option ℕ)) (i : ℕ) => L[i]?) := by
        norm_num +zetaDelta at *;
        convert Primrec.list_getElem? using 1;
      exact h_get?.comp ( Primrec.fst ) ( Primrec.fst.comp ( Primrec.snd ) );
    · convert Lambda.step_code_case1_inner_primrec using 1

/-
Equality lemma rewriting `Lambda.step_code_case1` in terms of
`Lambda.step_code_case1_inner_combined`.
-/
theorem Lambda.step_code_case1_eq_combined (L : List (Option ℕ)) :
  Lambda.step_code_case1 L =
  let c := L.length
  let m := c.unpair.2
  let (c1, c2) := m.unpair
  if c1 < c ∧ c2 < c then
    Lambda.step_code_case1_inner_combined L c1 c2
  else none := by
    convert Lambda.step_code_case1_eq L using 1

/-
Lambda.step_code_case1 is primitive recursive.
-/
theorem Lambda.step_code_case1_primrec : Primrec Lambda.step_code_case1 := by
  -- Use `Primrec.of_eq` with `Lambda.step_code_case1_eq_combined`.
  have h_primrec_step : Primrec (fun x : List (Option ℕ) => if x.length.unpair.2.unpair.1 < x.length
      ∧ x.length.unpair.2.unpair.2 < x.length then Lambda.step_code_case1_inner_combined x
      x.length.unpair.2.unpair.1 x.length.unpair.2.unpair.2 else none) := by
    have h_primrec_step : Primrec (fun x : List (Option ℕ) × ℕ × ℕ => if x.2.1 < x.1.length ∧ x.2.2
        < x.1.length then Lambda.step_code_case1_inner_combined x.1 x.2.1 x.2.2 else none) := by
      apply Primrec.ite;
      · -- The length function and the less-than relation are both primitive recursive.
        have h_len : Primrec (fun L : List (Option ℕ) => L.length) := by
          exact Primrec.list_length;
        have h_lt : PrimrecPred (fun (a : ℕ × ℕ) => a.1 < a.2) := by
          exact Primrec.nat_lt;
        exact h_lt.comp ( Primrec.fst.comp ( Primrec.snd.comp ( Primrec.id ) ) |> Primrec.pair <|
            h_len.comp ( Primrec.fst.comp ( Primrec.id ) ) ) |> PrimrecPred.and <| h_lt.comp (
            Primrec.snd.comp ( Primrec.snd.comp ( Primrec.id ) ) |> Primrec.pair <| h_len.comp (
            Primrec.fst.comp ( Primrec.id ) ) );
      · exact Lambda.step_code_case1_inner_combined_primrec;
      · exact Primrec.const none;
    convert h_primrec_step.comp ( show Primrec fun x : List ( Option ℕ ) => ( x, ( Nat.unpair (
        Nat.unpair x.length ).2 ).1, ( Nat.unpair ( Nat.unpair x.length ).2 ).2 ) from ?_ ) using 1;
    have h_primrec_step : Primrec
        (fun x : List (Option ℕ) => (x.length.unpair.2.unpair.1, x.length.unpair.2.unpair.2)) := by
      have h_primrec_step : Primrec (fun x : ℕ => (Nat.unpair (Nat.unpair x).2).1) ∧ Primrec
          (fun x : ℕ => (Nat.unpair (Nat.unpair x).2).2) := by
        exact ⟨ by exact Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair
            ) ) ), by exact Primrec.snd.comp ( Primrec.unpair.comp ( Primrec.snd.comp (
            Primrec.unpair ) ) ) ⟩;
      exact Primrec.pair ( h_primrec_step.1.comp ( Primrec.list_length ) )
          ( h_primrec_step.2.comp ( Primrec.list_length ) );
    exact Primrec.pair Primrec.id h_primrec_step;
  convert h_primrec_step using 1;
  exact funext fun x => by simpa using Lambda.step_code_case1_eq_combined x;

/-
Equality lemma rewriting `Lambda.step_code_case2` in terms of `Lambda.step_code_case2_inner`.
-/
theorem Lambda.step_code_case2_eq (L : List (Option ℕ)) :
  Lambda.step_code_case2 L =
  let c := L.length
  let c' := c.unpair.2
  if c' < c then
    (L[c']?).bind Lambda.step_code_case2_inner
  else none := by
    unfold step_code_case2 step_code_case2_inner; rfl

/-
Lambda.step_code_case2 is primitive recursive.
-/
theorem Lambda.step_code_case2_primrec : Primrec Lambda.step_code_case2 := by
  unfold Lambda.step_code_case2
  have hc' : Primrec (fun L : List (Option ℕ) => (Nat.unpair L.length).2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.list_length)
  have hcond : PrimrecPred (fun L : List (Option ℕ) => (Nat.unpair L.length).2 < L.length) :=
    Primrec.nat_lt.comp hc' Primrec.list_length
  have hthen : Primrec (fun L : List (Option ℕ) =>
      (L[(Nat.unpair L.length).2]?).bind Lambda.step_code_case2_inner) :=
    Primrec.option_bind (Primrec.list_getElem?.comp Primrec.id hc')
      (Lambda.step_code_case2_inner_primrec.comp Primrec.snd)
  exact Primrec.ite hcond hthen (Primrec.const none)

/-
Definition of `Lambda.step_code` and its Primrec proof.
-/
def Lambda.step_code (L : List (Option ℕ)) : Option (Option ℕ) :=
  let c := L.length
  match c.unpair with
  | (0, _) => some none
  | (1, _) => Lambda.step_code_case1 L
  | (2, _) => Lambda.step_code_case2 L
  | _ => some none

theorem Lambda.step_code_primrec : Primrec Lambda.step_code := by
  unfold step_code;
  convert Primrec.of_eq _ _;
  · exact fun L => Nat.casesOn ( L.length.unpair.1 ) ( some none ) fun n => Nat.casesOn n
      ( step_code_case1 L ) fun n => Nat.casesOn n ( step_code_case2 L ) fun n => some none
  · apply_rules [ Primrec.nat_casesOn, Primrec.nat_casesOn ];
    any_goals apply_rules [ Primrec.fst, Primrec.snd, Primrec.const ];
    · exact Primrec.fst.comp ( Primrec.unpair.comp ( Primrec.list_length ) );
    · exact Lambda.step_code_case1_primrec.comp ( Primrec.fst );
    · exact Lambda.step_code_case2_primrec.comp ( Primrec.fst.comp ( Primrec.fst ) );
  · intro L; rcases n : Nat.unpair L.length with ⟨ _ | _ | _ | n, _ | _ | _ | m ⟩ <;> simp
      ( config := { decide := Bool.true } ) [ n ] ;

/-
Checking the type of Primrec.nat_strong_rec.
-/

/-
Definition of `Lambda.code_step` and its Primrec proof.
-/
def Lambda.code_step (n : ℕ) : Option ℕ :=
  Nat.strongRecOn n (fun n ih => (Lambda.step_code ((List.range n).attach.map (fun ⟨m, hm⟩ => ih m
      (List.mem_range.1 hm)))).join)

theorem Lambda.code_step_primrec : Primrec Lambda.code_step := by
  set f := fun L : List (Option ℕ) => (Lambda.step_code L).join
  have hcode_step_primrec : Primrec f := by
    apply Primrec.option_bind
    · convert Lambda.step_code_primrec
    · exact Primrec.snd
  convert Primrec.nat_strong_rec _ _
  rotate_left
  · exact Unit
  · exact Option ℕ
  all_goals try infer_instance
  · exact fun _ n => code_step n
  · exact fun _ L => some (f L)
  · have h_some_f_primrec : Primrec (fun L : List (Option ℕ) => some (f L)) := by
      exact Primrec.option_some.comp hcode_step_primrec
    convert h_some_f_primrec.comp _
    exact Primrec.snd
  · constructor <;> intro h
    · intro h
      exact Primrec.comp (by assumption) Primrec.snd
    · convert h _
      · constructor <;> intro h <;> rw [Primrec₂] at * <;>
          simp_all only [Option.some.injEq, forall_const, implies_true]
        · exact h.comp Primrec.snd
        · convert h.comp (Primrec.const () |> Primrec.pair <| Primrec.id) using 1
      · intros
        unfold code_step
        rw [Nat.strongRecOn_eq]
        congr! 2
        refine List.ext_get ?_ ?_ <;> aesop

end
