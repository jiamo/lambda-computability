/-
Evaluation of encoded lambda terms and the resulting computability results.

`Lambda.eval` iterates the code-level beta step `Lambda.code_step` to a normal
form (as a partial recursive function of the code), `Lambda.unchurch_code`
decodes a Church numeral code back to a natural number, and
`Lambda.compute_fun` combines the two into the partial function computed by an
encoded lambda term.

Extracted from `Start/Basic.lean` as part of the modular split.
-/

import Start.Tactics
import Start.Syntax
import Start.Reduction
import Start.Church
import Start.Encoding
import Start.CodeOps
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List


set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Checking for Part.fix and Partrec lemmas.
-/

/-
Definition of `Lambda.step_iter` and its Primrec proof.
-/
def Lambda.step_iter (c : ℕ) : ℕ ⊕ ℕ :=
  match Lambda.code_step c with
  | some c' => Sum.inr c'
  | none => Sum.inl c

theorem Lambda.step_iter_primrec : Primrec Lambda.step_iter := by
  -- By definition, `step_iter n c` computes the result of applying `Lambda.code_step` to `c` `n`
  -- times.
  unfold step_iter;
  -- Use the fact that `lambda.code_step` is `Primrec`.
  have h_lambda_code_step_primrec : Primrec (fun c : ℕ => Lambda.code_step c) := by
    exact Lambda.code_step_primrec;
  convert h_lambda_code_step_primrec.option_casesOn _ _ using 1;
  rotate_left;
  exacts [ fun c => Sum.inl c, fun c c' => Sum.inr c',
    by exact Primrec.sumInl.comp ( Primrec.id ),
    by exact Primrec.sumInr.comp ( Primrec.snd ),
    funext fun c => by cases code_step c <;> rfl ]

/-
Checking if Lambda.church_code_primrec is available.
-/

/-
Definition of `Lambda.eval_step` and its Primrec proof.
-/
def Lambda.eval_step (c : ℕ) : ℕ ⊕ ℕ :=
  match Lambda.code_step c with
  | some c' => Sum.inl c'
  | none => Sum.inr c

theorem Lambda.eval_step_primrec : Primrec Lambda.eval_step := by
  unfold eval_step;
  have h_step_iter_primrec : Primrec
      (fun c => match Lambda.code_step c with | some c' => Option.some c' | none => Option.none) :=
      by
    have h_step_iter_primrec : Primrec Lambda.code_step := by
      exact Lambda.code_step_primrec;
    convert h_step_iter_primrec using 1;
    exact funext fun x => by cases code_step x <;> rfl;
  have := h_step_iter_primrec;
  convert this.option_casesOn _ _ using 1;
  rotate_left;
  · exact fun c => Sum.inr c
  · exact fun c c' => Sum.inl c'
  · exact Primrec.sumInr.comp Primrec.id;
  · exact Primrec.sumInl.comp Primrec.snd;
  · exact funext fun x => by cases code_step x <;> rfl;

/-
Definition of `Lambda.eval_step_part` and its Primrec proof.
-/
def Lambda.eval_step_part (c : ℕ) : ℕ ⊕ ℕ :=
  match Lambda.eval_step c with
  | Sum.inl c' => Sum.inr c'
  | Sum.inr res => Sum.inl res

theorem Lambda.eval_step_part_primrec : Primrec Lambda.eval_step_part :=
  -- `eval_step_part` is literally `step_iter`: both send `c` to `Sum.inr c'` when
  -- `code_step c = some c'` and to `Sum.inl c` otherwise.
  Primrec.of_eq Lambda.step_iter_primrec fun c => by
    unfold Lambda.step_iter Lambda.eval_step_part Lambda.eval_step
    cases Lambda.code_step c <;> rfl

/-
Checking PFun.fix and Partrec.fix.
-/

/-
Definition of `Lambda.eval` and its Partrec proof.
-/
def Lambda.eval (c : ℕ) : Part ℕ :=
  PFun.fix (fun c => Part.some (Lambda.eval_step_part c)) c

theorem Lambda.eval_partrec : Partrec Lambda.eval := by
  convert Partrec.fix _;
  -- Since `eval_step_part` is primitive recursive, its `Part.some` lifting is also primitive
  -- recursive.
  have h_primrec : Primrec Lambda.eval_step_part := by
    exact Lambda.eval_step_part_primrec;
  convert h_primrec.to_comp using 1




/-
`Lambda.unbody_code` attempts to decode a natural number from the body of a Church numeral encoding.
-/
def Lambda.unbody_code (c : ℕ) : Option ℕ :=
  Nat.strongRecOn c (fun c ih =>
    if c = Nat.pair 0 0 then some 0
    else
      match h : c.unpair with
      | (1, m) =>
        match hm : m.unpair with
        | (f, rest) =>
          if f = Nat.pair 0 1 then
            have : rest < c := Lambda.decode_lt_2 h hm
            (ih rest this).map Nat.succ
          else none
      | _ => none
  )

/-
Unfolding equation for `Lambda.unbody_code`: the dependent `match` of the definition is
equivalent to a pair of `if`s on the components of `Nat.unpair`.
-/
theorem Lambda.unbody_code_eq_ite (c : ℕ) :
    Lambda.unbody_code c =
      if c = Nat.pair 0 0 then some 0
      else if c.unpair.1 = 1 ∧ c.unpair.2.unpair.1 = Nat.pair 0 1 then
        (Lambda.unbody_code c.unpair.2.unpair.2).map Nat.succ
      else none := by
  rw [Lambda.unbody_code, Nat.strongRecOn_eq]
  by_cases h1 : c = Nat.pair 0 0
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    split
    · next m heq =>
        split
        next f rest heq2 =>
          simp only [heq, heq2, true_and]
          split_ifs <;> rfl
    · next heq =>
        rw [if_neg]
        rintro ⟨ha, -⟩
        exact heq _ (Prod.ext ha rfl)

/-
`Lambda.unchurch_code` attempts to decode a natural number from a Church numeral encoding.
-/
def Lambda.unchurch_code (c : ℕ) : Option ℕ :=
  match c.unpair with
  | (2, m) =>
    match m.unpair with
    | (2, body) => Lambda.unbody_code body
    | _ => none
  | _ => none




/-
`Lambda.unbody_code_step_inner` is primitive recursive.
-/
def Lambda.unbody_code_step_inner (L : List (Option ℕ)) (rest : ℕ) : Option ℕ :=
  (L[rest]?).bind (fun res => res.map Nat.succ)

theorem Lambda.unbody_code_step_inner_primrec : Primrec₂ Lambda.unbody_code_step_inner := by
  rw [Primrec₂]
  unfold Lambda.unbody_code_step_inner
  have h_get : Primrec (fun p : List (Option ℕ) × ℕ => p.1[p.2]?) := by
    convert Primrec.list_getElem? using 1
  have h_map : Primrec₂ (fun (_p : List (Option ℕ) × ℕ) (res : Option ℕ) => res.map Nat.succ) := by
    rw [Primrec₂]
    simpa using (Primrec.option_map₁ Primrec.succ).comp Primrec.snd
  simpa using Primrec.option_bind h_get h_map

/-
`Lambda.unbody_code_step` is primitive recursive.
-/
def Lambda.unbody_code_step (L : List (Option ℕ)) : Option ℕ :=
  let n := L.length
  if n = Nat.pair 0 0 then some 0
  else
    match n.unpair with
    | (1, m) =>
      match m.unpair with
      | (f, rest) =>
        if f = Nat.pair 0 1 then
          if rest < n then
             Lambda.unbody_code_step_inner L rest
          else none
        else none
    | _ => none

/-
Unfolding equation for `Lambda.unbody_code_step`, in the same shape as
`Lambda.unbody_code_eq_ite`.
-/
theorem Lambda.unbody_code_step_eq_ite (L : List (Option ℕ)) :
    Lambda.unbody_code_step L =
      if L.length = Nat.pair 0 0 then some 0
      else if L.length.unpair.1 = 1 ∧ L.length.unpair.2.unpair.1 = Nat.pair 0 1 then
        (if L.length.unpair.2.unpair.2 < L.length then
          Lambda.unbody_code_step_inner L L.length.unpair.2.unpair.2 else none)
      else none := by
  unfold Lambda.unbody_code_step
  rcases hu : (Nat.unpair L.length) with ⟨a, m⟩
  rcases hm : (Nat.unpair m) with ⟨f, rest⟩
  simp only [hu]
  rcases a with _ | _ | a <;> simp [hm]

theorem Lambda.unbody_code_step_primrec : Primrec Lambda.unbody_code_step := by
  -- The function `unbody_code_step` is defined using primitive recursive components: `if`,
  -- `unpair`, `map`, and `dash`.
  have h_primrec : Primrec (fun c : ℕ => if c = Nat.pair 0 0 then some 0 else none) :=
    -- The function that returns `some 0` if `c = Nat.pair 0 0` and `none` otherwise is an
    -- `if` on a primitive recursive predicate.
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const (Nat.pair 0 0)))
      (Primrec.const (some 0)) (Primrec.const none)
  convert Primrec.cond _ _ _;
  rotate_left;
  · exact fun L => L.length.unpair.1 = 1 ∧ L.length.unpair.2.unpair.1 = Nat.pair 0 1
  · exact fun L =>
      ( L[L.length.unpair.2.unpair.2]? |> Option.bind <| fun res => res.map Nat.succ )
  · exact fun L => if L.length = Nat.pair 0 0 then some 0 else none
  · -- The guard is the conjunction of two primitive recursive equality tests.
    have h_left : Primrec (fun L : List (Option ℕ) => decide ((Nat.unpair L.length).1 = 1)) :=
      Primrec.of_eq
        (Primrec.ite
          (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp Primrec.list_length))
            (Primrec.const 1))
          (Primrec.const true) (Primrec.const false))
        (fun L => by simp)
    have h_right : Primrec (fun L : List (Option ℕ) =>
        decide ((Nat.unpair (Nat.unpair L.length).2).1 = Nat.pair 0 1)) :=
      Primrec.of_eq
        (Primrec.ite
          (Primrec.eq.comp
            (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp
              Primrec.list_length))))
            (Primrec.const (Nat.pair 0 1)))
          (Primrec.const true) (Primrec.const false))
        (fun L => by simp)
    exact Primrec.of_eq (Primrec.cond h_left h_right (Primrec.const false))
      (fun L => by by_cases h : (Nat.unpair L.length).1 = 1 <;> simp [h])
  · -- The function `unbody_code_step_inner` is primitive recursive, as given by `h_primrec`.
    have h_primrec_inner : Primrec
        (fun (L : List (Option ℕ) × ℕ) => (L.1[L.2]?).bind (fun res => res.map Nat.succ)) := by
      convert Lambda.unbody_code_step_inner_primrec using 1;
    convert h_primrec_inner.comp
      ( show Primrec
          ( fun L : List ( Option ℕ ) => ( L, Nat.unpair ( Nat.unpair L.length ).2 |> Prod.snd ) )
        from ?_ ) using 1;
    convert Primrec.pair Primrec.id
      ( Primrec.comp
        ( show Primrec ( fun x : ℕ => ( Nat.unpair ( Nat.unpair x ).2 ).2 ) from ?_ )
        ( show Primrec ( fun L : List ( Option ℕ ) => L.length ) from ?_ ) ) using 1;
    · exact Primrec.snd.comp
        ( Primrec.unpair.comp ( Primrec.snd.comp ( Primrec.unpair.comp Primrec.id ) ) );
    · exact Primrec.list_length;
  · convert h_primrec.comp ( Primrec.list_length ) using 1;
  · rename_i L
    rw [Lambda.unbody_code_step_eq_ite]
    by_cases hP : (Nat.unpair L.length).1 = 1 ∧
        (Nat.unpair (Nat.unpair L.length).2).1 = Nat.pair 0 1
    · have hlen : ¬ L.length = Nat.pair 0 0 := by
        intro h
        rw [h] at hP
        simp at hP
      rw [if_neg hlen]
      simp only [hP, decide_true, cond_true, and_self, if_true]
      unfold Lambda.unbody_code_step_inner
      by_cases hr : (Nat.unpair (Nat.unpair L.length).2).2 < L.length
      · rw [if_pos hr]
      · rw [if_neg hr, List.getElem?_eq_none (by omega)]
        rfl
    · simp only [hP, decide_false, cond_false, if_false]

/-
The step function `Lambda.unbody_code_step` correctly computes `Lambda.unbody_code` given the list
of previous values.
-/
theorem Lambda.unbody_code_eq_step (n : ℕ) :
  Lambda.unbody_code_step ((List.range n).map Lambda.unbody_code) = Lambda.unbody_code n := by
    rw [Lambda.unbody_code_step_eq_ite, Lambda.unbody_code_eq_ite n]
    simp only [List.length_map, List.length_range]
    by_cases hP : (Nat.unpair n).1 = 1 ∧ (Nat.unpair (Nat.unpair n).2).1 = Nat.pair 0 1
    · have hlt : (Nat.unpair (Nat.unpair n).2).2 < n :=
        Lambda.decode_lt_2 (Prod.ext hP.1 rfl) rfl
      have hget : ((List.range n).map Lambda.unbody_code)[(Nat.unpair (Nat.unpair n).2).2]? =
          some (Lambda.unbody_code (Nat.unpair (Nat.unpair n).2).2) := by
        simp [hlt]
      simp only [hP, and_self, if_true, if_pos hlt, Lambda.unbody_code_step_inner, hget,
        Option.bind_some]
    · simp only [hP, if_false]

/-
`Lambda.unbody_code` is primitive recursive.
-/
theorem Lambda.unbody_code_primrec : Primrec Lambda.unbody_code := by
  have hg : Primrec₂ (fun (_ : Unit) (L : List (Option ℕ)) => some (Lambda.unbody_code_step L)) :=
    Primrec.option_some.comp (Lambda.unbody_code_step_primrec.comp Primrec.snd)
  have h := Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => Lambda.unbody_code n) hg
    (fun _ n => congrArg some (Lambda.unbody_code_eq_step n))
  simpa using h.comp (Primrec.const ()) Primrec.id

/-
`Lambda.unchurch_code` is primitive recursive.
-/
theorem Lambda.unchurch_code_primrec : Primrec Lambda.unchurch_code := by
  let g : ℕ → Option ℕ := fun n =>
    if n.unpair.1 = 2 then
      if n.unpair.2.unpair.1 = 2 then
        Lambda.unbody_code n.unpair.2.unpair.2
      else
        none
    else
      none
  have hg : Primrec g := by
    unfold g
    apply Primrec.ite
    · exact Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2)
    · apply Primrec.ite
      · exact
          Primrec.eq.comp
            (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
            (Primrec.const 2)
      · have h_body : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2) := by
          exact Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
        exact Lambda.unbody_code_primrec.comp h_body
      · exact Primrec.const none
    · exact Primrec.const none
  refine Primrec.of_eq hg ?_
  intro n
  dsimp [g]
  rcases h1 : Nat.unpair n with ⟨_ | _ | _ | a, m⟩ <;>
    simp only [OfNat.zero_ne_ofNat, ↓reduceIte, unchurch_code, h1, zero_add,
      OfNat.one_ne_ofNat, Nat.reduceAdd, Nat.reduceEqDiff]
  rcases h2 : Nat.unpair m with ⟨_ | _ | _ | b, body⟩ <;> simp 

/-
`Lambda.unbody_code` correctly decodes the body of a Church numeral.
-/
theorem Lambda.unbody_code_correct (n : ℕ) : Lambda.unbody_code (Lambda.body_code n) = some n := by
  induction n with
  | zero =>
      simp (config := { decide := Bool.true }) 
  | succ n ih =>
      have h_body_code_succ : body_code (n + 1) = app_code (Nat.pair 0 1) (body_code n) := by
        rfl
      unfold app_code at h_body_code_succ
      simp_all only
      unfold Lambda.unbody_code
      rw [Nat.strongRecOn_eq]
      aesop

/-
`Lambda.unchurch_code` correctly decodes a Church numeral.
-/
theorem Lambda.unchurch_code_correct (n : ℕ) :
    Lambda.unchurch_code (Lambda.church_code n) = some n := by
  unfold Lambda.unchurch_code;
  unfold church_code; rw [ Nat.unpair_pair ] ; norm_num [ Lambda.unbody_code_correct ] ;

/-
The function `Lambda.compute_fun` is partial recursive.
-/
def Lambda.compute_fun (F_code : ℕ) (n : ℕ) : Part ℕ :=
  (Lambda.eval (Lambda.app_code F_code (Lambda.church_code n))).bind
      (fun c => Lambda.unchurch_code c)

theorem Lambda.compute_fun_partrec (F_code : ℕ) : Partrec (Lambda.compute_fun F_code) := by
  have h_eval : Partrec Lambda.eval := by
    exact Lambda.eval_partrec
  refine Partrec.bind ?_ ?_
  · have h_app_code : Primrec (fun a => Lambda.app_code F_code (Lambda.church_code a)) := by
      exact Primrec₂.comp Lambda.app_code_primrec (Primrec.const F_code) Lambda.church_code_primrec
    exact h_eval.comp h_app_code.to_comp
  · have h_unchurch : Primrec Lambda.unchurch_code := by
      exact Lambda.unchurch_code_primrec
    apply_rules [Partrec.comp, h_unchurch.to_comp]
    any_goals exact Computable.id
    · apply Computable.ofOption
      exact Computable.id
    · exact Computable.comp h_unchurch.to_comp Computable.snd

/-
`Lambda.unbody_code c` returns `some n` if and only if `c` is the code for the body of the Church
numeral `n`.
-/
theorem Lambda.unbody_code_eq_some_iff (c n : ℕ) :
    Lambda.unbody_code c = some n ↔ c = Lambda.body_code n := by
  constructor
  · induction c using Nat.strong_induction_on generalizing n with
    | _ c ih =>
      intro hc
      rw [Lambda.unbody_code_eq_ite] at hc
      by_cases h0 : c = Nat.pair 0 0
      · rw [if_pos h0, Option.some_inj] at hc
        rw [← hc, h0]
        rfl
      · rw [if_neg h0] at hc
        by_cases hP : c.unpair.1 = 1 ∧ c.unpair.2.unpair.1 = Nat.pair 0 1
        · rw [if_pos hP] at hc
          obtain ⟨k, hk, hkn⟩ := Option.map_eq_some_iff.mp hc
          have hlt : c.unpair.2.unpair.2 < c := Lambda.decode_lt_2 (Prod.ext hP.1 rfl) rfl
          have hbody := ih _ hlt _ hk
          subst hkn
          change c = Nat.pair 1 (Nat.pair (Nat.pair 0 1) (Lambda.body_code k))
          rw [← hbody, ← hP.2, Nat.pair_unpair, ← hP.1, Nat.pair_unpair]
        · rw [if_neg hP] at hc
          exact absurd hc (by simp)
  · exact fun h => h ▸ Lambda.unbody_code_correct n

/-
`Lambda.unchurch_code c` returns `some n` if and only if `c` is the code for the Church numeral `n`.
-/
theorem Lambda.unchurch_code_eq_ite (c : ℕ) :
    Lambda.unchurch_code c =
      if c.unpair.1 = 2 ∧ c.unpair.2.unpair.1 = 2 then Lambda.unbody_code c.unpair.2.unpair.2
      else none := by
  unfold Lambda.unchurch_code
  rcases hu : (Nat.unpair c) with ⟨a, m⟩
  rcases hm : (Nat.unpair m) with ⟨b, body⟩
  rcases a with _ | _ | _ | a <;> rcases b with _ | _ | _ | b <;> simp [hm]

theorem Lambda.unchurch_code_eq_some_iff (c n : ℕ) :
    Lambda.unchurch_code c = some n ↔ c = Lambda.church_code n := by
  constructor
  · intro h
    rw [Lambda.unchurch_code_eq_ite] at h
    by_cases hP : c.unpair.1 = 2 ∧ c.unpair.2.unpair.1 = 2
    · rw [if_pos hP] at h
      have hbody := (Lambda.unbody_code_eq_some_iff _ _).mp h
      have h2 : Nat.pair 2 (Lambda.body_code n) = c.unpair.2 := by
        rw [← hbody, ← hP.2, Nat.pair_unpair]
      change c = Nat.pair 2 (Nat.pair 2 (Lambda.body_code n))
      rw [h2, ← hP.1, Nat.pair_unpair]
    · rw [if_neg hP] at h
      exact absurd h (by simp)
  · exact fun h => h ▸ Lambda.unchurch_code_correct n

/-- Church numeral encoding roundtrips: the encoding of the Church numeral `n`
is the arithmetized Church code of `n`. -/
theorem Lambda.church_code_roundtrip (n : ℕ) :
    Lambda.encode (Lambda.church n) = Lambda.church_code n :=
  Lambda.encode_church_eq_church_code n

end
