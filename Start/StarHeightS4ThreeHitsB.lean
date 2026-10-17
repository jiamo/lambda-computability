import Start.StarHeightS4ThreeBase

/-!
# Lifted certificates for classes of `S₄` over three letters (part B)

Five conjugacy classes of generating triples of `S₄`, in the right-action convention of
`docs/goal/evidence/M28-STARHEIGHT-LIFT-SEARCH.py` (a letter `p` is written as the image tuple
`p 0 p 1 p 2 p 3`):

`0132 1203 1320`, `0132 1203 2310`, `0132 1203 3021`, `0231 1203 2310`, `0231 1302 2310`.

For these classes the good coset automata of `S₄` do not separate `S₄`.  For each, a signed lift
`E` of order `192` inside `Z₂ ≀ S₄` supplies a family of good coset automata of `E` that
determines the value of the morphism (an instance of `height_one_of_lift`).

Each block (namespace `CX`) states the morphism `CX.T` by its three letters (tables of images of
`0, 1, 2, 3` with their inverse tables; the Lean letters are the inverses of the right-action
letters, because `σ * τ` applies `τ` first), the auxiliary automata with the certificates that
their return automata are aperiodic, the decoding table, and the theorem `CX.height_one`: every
language recognized by `CX.T` has generalized star height at most one.
-/

-- The certificates below are checked one at a time, which keeps the peak memory low.
set_option Elab.async false

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-! ### The class `0132 1203 1320` (right action); lift `01324576 12035647 13645720` -/

namespace C0132_1203_1320

/-- The morphism: the three letters as permutations of `Fin 4` (table, inverse table). -/
def T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  FreeMonoid.lift ![mkPerm4 ![0, 1, 3, 2] ![0, 1, 3, 2],
    mkPerm4 ![2, 0, 1, 3] ![1, 2, 0, 3],
    mkPerm4 ![3, 0, 2, 1] ![1, 3, 2, 0]]

/-- The letters as tables. -/
def lt (x : Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk [[0, 1, 3, 2], [2, 0, 1, 3], [3, 0, 2, 1]] x i % 4, Nat.mod_lt _ (by decide)⟩

/-- Auxiliary automaton `a0` (4 states, a coset automaton of the lift). -/
def a0 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 2], [0, 0, 1], [2, 1, 3], [3, 3, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a1` (4 states, a coset automaton of the lift). -/
def a1 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 2], [0, 1, 0], [2, 3, 1], [3, 0, 3]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a2` (3 states, a coset automaton of the lift). -/
def a2 (q : Fin 3) (x : Fin 3) : Fin 3 :=
  ⟨lk [[1, 2, 1], [0, 0, 2], [2, 1, 0]] q x % 3, Nat.mod_lt _ (by decide)⟩

lemma a2_cert : Aperiodic.certOK (stN 3 0) [0, 1, 2] (DFAReturn.retAut a2 0)
    (Aperiodic.dfaCert (stN 3 0) [0, 1, 2] (DFAReturn.retAut a2 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a3` (2 states, a coset automaton of the lift). -/
def a3 (q : Fin 2) (x : Fin 3) : Fin 2 :=
  ⟨lk [[1, 0, 0], [0, 1, 1]] q x % 2, Nat.mod_lt _ (by decide)⟩

lemma a3_cert : Aperiodic.certOK (stN 2 0) [0, 1, 2] (DFAReturn.retAut a3 0)
    (Aperiodic.dfaCert (stN 2 0) [0, 1, 2] (DFAReturn.retAut a3 0) 400) 3 = true := by
  decide +kernel

/-- The joint state of the auxiliary automata. -/
def obs (w : List (Fin 3)) : Fin 4 × Fin 4 × Fin 3 × Fin 2 :=
  (DFAReturn.runQ a0 0 w, DFAReturn.runQ a1 0 w, DFAReturn.runQ a2 0 w, DFAReturn.runQ a3 0 w)

/-- The joint step. -/
def step (o : Fin 4 × Fin 4 × Fin 3 × Fin 2) (x : Fin 3) : Fin 4 × Fin 4 × Fin 3 × Fin 2 :=
  match o with | (o0, o1, o2, o3) => (a0 o0 x, a1 o1 x, a2 o2 x, a3 o3 x)

/-- The decoding table (`[]`: unreachable). -/
def decL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 3, 2, 1], [0, 3, 1, 2], [0, 1, 3, 2], [0, 2, 3, 1], [0, 2, 1, 3],
    [1, 0, 3, 2], [3, 0, 1, 2], [3, 0, 2, 1], [1, 0, 2, 3], [2, 0, 1, 3], [2, 0, 3, 1],
    [2, 3, 0, 1], [2, 1, 0, 3], [1, 2, 0, 3], [3, 2, 0, 1], [3, 1, 0, 2], [1, 3, 0, 2],
    [3, 2, 1, 0], [1, 2, 3, 0], [2, 1, 3, 0], [2, 3, 1, 0], [1, 3, 2, 0], [3, 1, 2, 0],
    [1, 0, 3, 2], [3, 0, 1, 2], [3, 0, 2, 1], [1, 0, 2, 3], [2, 0, 1, 3], [2, 0, 3, 1],
    [0, 1, 2, 3], [0, 3, 2, 1], [0, 3, 1, 2], [0, 1, 3, 2], [0, 2, 3, 1], [0, 2, 1, 3],
    [3, 2, 1, 0], [1, 2, 3, 0], [2, 1, 3, 0], [2, 3, 1, 0], [1, 3, 2, 0], [3, 1, 2, 0],
    [2, 3, 0, 1], [2, 1, 0, 3], [1, 2, 0, 3], [3, 2, 0, 1], [3, 1, 0, 2], [1, 3, 0, 2],
    [3, 2, 1, 0], [1, 2, 3, 0], [2, 1, 3, 0], [2, 3, 1, 0], [1, 3, 2, 0], [3, 1, 2, 0],
    [2, 3, 0, 1], [2, 1, 0, 3], [1, 2, 0, 3], [3, 2, 0, 1], [3, 1, 0, 2], [1, 3, 0, 2],
    [1, 0, 3, 2], [3, 0, 1, 2], [3, 0, 2, 1], [1, 0, 2, 3], [2, 0, 1, 3], [2, 0, 3, 1],
    [0, 1, 2, 3], [0, 3, 2, 1], [0, 3, 1, 2], [0, 1, 3, 2], [0, 2, 3, 1], [0, 2, 1, 3],
    [2, 3, 0, 1], [2, 1, 0, 3], [1, 2, 0, 3], [3, 2, 0, 1], [3, 1, 0, 2], [1, 3, 0, 2],
    [3, 2, 1, 0], [1, 2, 3, 0], [2, 1, 3, 0], [2, 3, 1, 0], [1, 3, 2, 0], [3, 1, 2, 0],
    [0, 1, 2, 3], [0, 3, 2, 1], [0, 3, 1, 2], [0, 1, 3, 2], [0, 2, 3, 1], [0, 2, 1, 3],
    [1, 0, 3, 2], [3, 0, 1, 2], [3, 0, 2, 1], [1, 0, 2, 3], [2, 0, 1, 3], [2, 0, 3, 1]]

/-- The code of an observation. -/
def code (o : Fin 4 × Fin 4 × Fin 3 × Fin 2) : ℕ :=
  match o with | (o0, o1, o2, o3) => (((o0.val) * 4 + o1.val) * 3 + o2.val) * 2 + o3.val

/-- Reachable observations. -/
def reach (o : Fin 4 × Fin 4 × Fin 3 × Fin 2) : Bool := (decL.getD (code o) []) != []

/-- The decoding. -/
def dec (o : Fin 4 × Fin 4 × Fin 3 × Fin 2) (i : Fin 4) : Fin 4 :=
  ⟨lk decL (code o) i % 4, Nat.mod_lt _ (by decide)⟩

lemma start : reach (0, 0, 0, 0) = true ∧ ∀ i : Fin 4, dec (0, 0, 0, 0) i = i := by
  decide

lemma closed : ∀ (o : Fin 4 × Fin 4 × Fin 3 × Fin 2) (x : Fin 3), reach o = true →
    reach (step o x) = true ∧ ∀ i, dec (step o x) i = dec o (lt x i) := by
  decide +kernel

lemma T_of (x : Fin 3) (i : Fin 4) : T (FreeMonoid.of x) i = lt x i := by
  rw [T, FreeMonoid.lift_eval_of]
  revert x i
  decide

lemma obs_append (w : List (Fin 3)) (x : Fin 3) : obs (w ++ [x]) = step (obs w) x := by
  simp only [obs, step, DFAReturn.runQ_append_single]

lemma reach_dec (w : List (Fin 3)) :
    reach (obs w) = true ∧ ∀ i, T (FreeMonoid.ofList w) i = dec (obs w) i := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨start.1, fun i => ?_⟩
      rw [show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one]
      exact (start.2 i).symm
  | append_singleton w x ih =>
      obtain ⟨h1, h2⟩ := closed _ x ih.1
      refine ⟨by rw [obs_append]; exact h1, fun i => ?_⟩
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, Equiv.Perm.mul_apply,
        T_of, ih.2, obs_append, h2]

lemma obs_height (o : Fin 4 × Fin 4 × Fin 3 × Fin 2) : HasHeightAtMost {w | obs w = o} 1 := by
  obtain ⟨p0, p1, p2, p3⟩ := o
  have heq : ({w | obs w = (p0, p1, p2, p3)} : Language (Fin 3)) =
      ((({w | DFAReturn.runQ a0 0 w = p0}
        ⊓ {w | DFAReturn.runQ a1 0 w = p1})
        ⊓ {w | DFAReturn.runQ a2 0 w = p2})
        ⊓ {w | DFAReturn.runQ a3 0 w = p3}) := by
    ext w
    simp only [obs, Prod.mk.injEq]
    exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩,
      fun ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ => ⟨h0, h1, h2, h3⟩⟩
  rw [heq]
  exact (((good_baseN a0 0 _ a0_cert p0
    ).inter (good_baseN a1 0 _ a1_cert p1)
    ).inter (good_baseN a2 0 _ a2_cert p2)
    ).inter (good_baseN a3 0 _ a3_cert p3)

/-- **Every language recognized by `T` has generalized star height at most one.** -/
theorem height_one (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (ι := Unit)
    (X := fun _ => Fin 4 × Fin 4 × Fin 3 × Fin 2) (fun _ => obs) ?_ (fun _ => obs_height) F
  intro u v huv
  exact Equiv.ext fun i => by rw [(reach_dec u).2, (reach_dec v).2, huv ()]

end C0132_1203_1320

/-! ### The class `0132 1203 2310` (right action); lift `01324576 12475603 23106754` -/

namespace C0132_1203_2310

/-- The morphism: the three letters as permutations of `Fin 4` (table, inverse table). -/
def T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  FreeMonoid.lift ![mkPerm4 ![0, 1, 3, 2] ![0, 1, 3, 2],
    mkPerm4 ![2, 0, 1, 3] ![1, 2, 0, 3],
    mkPerm4 ![3, 2, 0, 1] ![2, 3, 1, 0]]

/-- The letters as tables. -/
def lt (x : Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk [[0, 1, 3, 2], [2, 0, 1, 3], [3, 2, 0, 1]] x i % 4, Nat.mod_lt _ (by decide)⟩

/-- Auxiliary automaton `a0` (4 states, a coset automaton of the lift). -/
def a0 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 1, 2], [0, 3, 3], [2, 2, 1], [3, 0, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0) 400) 5 = true := by
  decide +kernel

/-- Auxiliary automaton `a1` (4 states, a coset automaton of the lift). -/
def a1 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 2], [0, 0, 3], [2, 1, 1], [3, 3, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0) 400) 5 = true := by
  decide +kernel

/-- Auxiliary automaton `a2` (4 states, a coset automaton of the lift). -/
def a2 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 1], [0, 1, 0], [2, 3, 2], [3, 0, 3]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a3` (3 states, a coset automaton of the lift). -/
def a3 (q : Fin 3) (x : Fin 3) : Fin 3 :=
  ⟨lk [[1, 2, 1], [0, 0, 0], [2, 1, 2]] q x % 3, Nat.mod_lt _ (by decide)⟩

lemma a3_cert : Aperiodic.certOK (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0)
    (Aperiodic.dfaCert (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0) 400) 4 = true := by
  decide +kernel

/-- The joint state of the auxiliary automata. -/
def obs (w : List (Fin 3)) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  (DFAReturn.runQ a0 0 w, DFAReturn.runQ a1 0 w, DFAReturn.runQ a2 0 w, DFAReturn.runQ a3 0 w)

/-- The joint step. -/
def step (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  match o with | (o0, o1, o2, o3) => (a0 o0 x, a1 o1 x, a2 o2 x, a3 o3 x)

/-- The decoding table (`[]`: unreachable). -/
def decL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [], [1, 0, 3, 2], [1, 0, 2, 3], [], [2, 3, 0, 1], [3, 2, 0, 1],
    [], [3, 2, 1, 0], [2, 3, 1, 0], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [2, 1, 3, 0], [3, 1, 2, 0], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [3, 0, 2, 1], [2, 0, 3, 1],
    [], [0, 3, 1, 2], [0, 2, 1, 3], [2, 1, 0, 3], [], [3, 1, 0, 2], [1, 2, 3, 0], [],
    [1, 3, 2, 0], [0, 3, 2, 1], [], [0, 2, 3, 1], [3, 0, 1, 2], [], [2, 0, 1, 3], [], [], [], [],
    [], [], [], [], [], [], [], [], [1, 0, 3, 2], [1, 0, 2, 3], [], [0, 1, 2, 3], [0, 1, 3, 2],
    [], [3, 2, 1, 0], [2, 3, 1, 0], [], [2, 3, 0, 1], [3, 2, 0, 1], [], [1, 2, 3, 0], [],
    [1, 3, 2, 0], [2, 1, 0, 3], [], [3, 1, 0, 2], [3, 0, 1, 2], [], [2, 0, 1, 3], [0, 3, 2, 1],
    [], [0, 2, 3, 1], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [2, 1, 3, 0], [3, 1, 2, 0], [],
    [0, 3, 1, 2], [0, 2, 1, 3], [], [3, 0, 2, 1], [2, 0, 3, 1], [], [0, 3, 1, 2], [0, 2, 1, 3],
    [], [3, 0, 2, 1], [2, 0, 3, 1], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [2, 1, 3, 0],
    [3, 1, 2, 0], [3, 0, 1, 2], [], [2, 0, 1, 3], [0, 3, 2, 1], [], [0, 2, 3, 1], [1, 2, 3, 0],
    [], [1, 3, 2, 0], [2, 1, 0, 3], [], [3, 1, 0, 2], [3, 2, 1, 0], [2, 3, 1, 0], [],
    [2, 3, 0, 1], [3, 2, 0, 1], [], [1, 0, 3, 2], [1, 0, 2, 3], [], [0, 1, 2, 3], [0, 1, 3, 2],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [0, 3, 2, 1], [], [0, 2, 3, 1],
    [3, 0, 1, 2], [], [2, 0, 1, 3], [2, 1, 0, 3], [], [3, 1, 0, 2], [1, 2, 3, 0], [],
    [1, 3, 2, 0], [], [3, 0, 2, 1], [2, 0, 3, 1], [], [0, 3, 1, 2], [0, 2, 1, 3], [],
    [2, 1, 3, 0], [3, 1, 2, 0], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [], [], [], [], [], [], [],
    [], [], [], [], [2, 3, 0, 1], [3, 2, 0, 1], [], [3, 2, 1, 0], [2, 3, 1, 0], [], [0, 1, 2, 3],
    [0, 1, 3, 2], [], [1, 0, 3, 2], [1, 0, 2, 3], []]

/-- The code of an observation. -/
def code (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : ℕ :=
  match o with | (o0, o1, o2, o3) => (((o0.val) * 4 + o1.val) * 4 + o2.val) * 3 + o3.val

/-- Reachable observations. -/
def reach (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : Bool := (decL.getD (code o) []) != []

/-- The decoding. -/
def dec (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk decL (code o) i % 4, Nat.mod_lt _ (by decide)⟩

lemma start : reach (0, 0, 0, 0) = true ∧ ∀ i : Fin 4, dec (0, 0, 0, 0) i = i := by
  decide

lemma closed : ∀ (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3), reach o = true →
    reach (step o x) = true ∧ ∀ i, dec (step o x) i = dec o (lt x i) := by
  decide +kernel

lemma T_of (x : Fin 3) (i : Fin 4) : T (FreeMonoid.of x) i = lt x i := by
  rw [T, FreeMonoid.lift_eval_of]
  revert x i
  decide

lemma obs_append (w : List (Fin 3)) (x : Fin 3) : obs (w ++ [x]) = step (obs w) x := by
  simp only [obs, step, DFAReturn.runQ_append_single]

lemma reach_dec (w : List (Fin 3)) :
    reach (obs w) = true ∧ ∀ i, T (FreeMonoid.ofList w) i = dec (obs w) i := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨start.1, fun i => ?_⟩
      rw [show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one]
      exact (start.2 i).symm
  | append_singleton w x ih =>
      obtain ⟨h1, h2⟩ := closed _ x ih.1
      refine ⟨by rw [obs_append]; exact h1, fun i => ?_⟩
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, Equiv.Perm.mul_apply,
        T_of, ih.2, obs_append, h2]

lemma obs_height (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : HasHeightAtMost {w | obs w = o} 1 := by
  obtain ⟨p0, p1, p2, p3⟩ := o
  have heq : ({w | obs w = (p0, p1, p2, p3)} : Language (Fin 3)) =
      ((({w | DFAReturn.runQ a0 0 w = p0}
        ⊓ {w | DFAReturn.runQ a1 0 w = p1})
        ⊓ {w | DFAReturn.runQ a2 0 w = p2})
        ⊓ {w | DFAReturn.runQ a3 0 w = p3}) := by
    ext w
    simp only [obs, Prod.mk.injEq]
    exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩,
      fun ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ => ⟨h0, h1, h2, h3⟩⟩
  rw [heq]
  exact (((good_baseN a0 0 _ a0_cert p0
    ).inter (good_baseN a1 0 _ a1_cert p1)
    ).inter (good_baseN a2 0 _ a2_cert p2)
    ).inter (good_baseN a3 0 _ a3_cert p3)

/-- **Every language recognized by `T` has generalized star height at most one.** -/
theorem height_one (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (ι := Unit)
    (X := fun _ => Fin 4 × Fin 4 × Fin 4 × Fin 3) (fun _ => obs) ?_ (fun _ => obs_height) F
  intro u v huv
  exact Equiv.ext fun i => by rw [(reach_dec u).2, (reach_dec v).2, huv ()]

end C0132_1203_2310

/-! ### The class `0132 1203 3021` (right action); lift `01324576 12035647 34617025` -/

namespace C0132_1203_3021

/-- The morphism: the three letters as permutations of `Fin 4` (table, inverse table). -/
def T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  FreeMonoid.lift ![mkPerm4 ![0, 1, 3, 2] ![0, 1, 3, 2],
    mkPerm4 ![2, 0, 1, 3] ![1, 2, 0, 3],
    mkPerm4 ![1, 3, 2, 0] ![3, 0, 2, 1]]

/-- The letters as tables. -/
def lt (x : Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk [[0, 1, 3, 2], [2, 0, 1, 3], [1, 3, 2, 0]] x i % 4, Nat.mod_lt _ (by decide)⟩

/-- Auxiliary automaton `a0` (4 states, a coset automaton of the lift). -/
def a0 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 1], [0, 0, 3], [2, 1, 2], [3, 3, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a1` (4 states, a coset automaton of the lift). -/
def a1 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 2], [0, 1, 1], [2, 3, 3], [3, 0, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a2` (4 states, a coset automaton of the lift). -/
def a2 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 1, 2], [0, 3, 0], [2, 2, 1], [3, 0, 3]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a3` (3 states, a coset automaton of the lift). -/
def a3 (q : Fin 3) (x : Fin 3) : Fin 3 :=
  ⟨lk [[1, 2, 2], [0, 0, 0], [2, 1, 1]] q x % 3, Nat.mod_lt _ (by decide)⟩

lemma a3_cert : Aperiodic.certOK (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0)
    (Aperiodic.dfaCert (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0) 400) 4 = true := by
  decide +kernel

/-- The joint state of the auxiliary automata. -/
def obs (w : List (Fin 3)) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  (DFAReturn.runQ a0 0 w, DFAReturn.runQ a1 0 w, DFAReturn.runQ a2 0 w, DFAReturn.runQ a3 0 w)

/-- The joint step. -/
def step (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  match o with | (o0, o1, o2, o3) => (a0 o0 x, a1 o1 x, a2 o2 x, a3 o3 x)

/-- The decoding table (`[]`: unreachable). -/
def decL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [], [], [], [], [], [0, 3, 1, 2], [0, 2, 1, 3], [0, 3, 2, 1], [],
    [0, 2, 3, 1], [1, 0, 3, 2], [1, 0, 2, 3], [], [], [], [], [], [3, 0, 2, 1], [2, 0, 3, 1],
    [3, 0, 1, 2], [], [2, 0, 1, 3], [2, 3, 0, 1], [3, 2, 0, 1], [], [], [], [], [], [1, 2, 0, 3],
    [1, 3, 0, 2], [2, 1, 0, 3], [], [3, 1, 0, 2], [3, 2, 1, 0], [2, 3, 1, 0], [], [], [], [], [],
    [2, 1, 3, 0], [3, 1, 2, 0], [1, 2, 3, 0], [], [1, 3, 2, 0], [], [], [], [1, 0, 3, 2],
    [1, 0, 2, 3], [], [3, 0, 1, 2], [], [2, 0, 1, 3], [], [3, 0, 2, 1], [2, 0, 3, 1], [], [], [],
    [0, 1, 2, 3], [0, 1, 3, 2], [], [0, 3, 2, 1], [], [0, 2, 3, 1], [], [0, 3, 1, 2],
    [0, 2, 1, 3], [], [], [], [3, 2, 1, 0], [2, 3, 1, 0], [], [1, 2, 3, 0], [], [1, 3, 2, 0], [],
    [2, 1, 3, 0], [3, 1, 2, 0], [], [], [], [2, 3, 0, 1], [3, 2, 0, 1], [], [2, 1, 0, 3], [],
    [3, 1, 0, 2], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [2, 1, 3, 0], [3, 1, 2, 0], [1, 2, 3, 0],
    [], [1, 3, 2, 0], [3, 2, 1, 0], [2, 3, 1, 0], [], [], [], [], [], [1, 2, 0, 3], [1, 3, 0, 2],
    [2, 1, 0, 3], [], [3, 1, 0, 2], [2, 3, 0, 1], [3, 2, 0, 1], [], [], [], [], [], [3, 0, 2, 1],
    [2, 0, 3, 1], [3, 0, 1, 2], [], [2, 0, 1, 3], [1, 0, 3, 2], [1, 0, 2, 3], [], [], [], [], [],
    [0, 3, 1, 2], [0, 2, 1, 3], [0, 3, 2, 1], [], [0, 2, 3, 1], [0, 1, 2, 3], [0, 1, 3, 2], [],
    [], [], [], [2, 1, 0, 3], [], [3, 1, 0, 2], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [], [],
    [2, 3, 0, 1], [3, 2, 0, 1], [], [1, 2, 3, 0], [], [1, 3, 2, 0], [], [2, 1, 3, 0],
    [3, 1, 2, 0], [], [], [], [3, 2, 1, 0], [2, 3, 1, 0], [], [0, 3, 2, 1], [], [0, 2, 3, 1], [],
    [0, 3, 1, 2], [0, 2, 1, 3], [], [], [], [0, 1, 2, 3], [0, 1, 3, 2], [], [3, 0, 1, 2], [],
    [2, 0, 1, 3], [], [3, 0, 2, 1], [2, 0, 3, 1], [], [], [], [1, 0, 3, 2], [1, 0, 2, 3], []]

/-- The code of an observation. -/
def code (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : ℕ :=
  match o with | (o0, o1, o2, o3) => (((o0.val) * 4 + o1.val) * 4 + o2.val) * 3 + o3.val

/-- Reachable observations. -/
def reach (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : Bool := (decL.getD (code o) []) != []

/-- The decoding. -/
def dec (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk decL (code o) i % 4, Nat.mod_lt _ (by decide)⟩

lemma start : reach (0, 0, 0, 0) = true ∧ ∀ i : Fin 4, dec (0, 0, 0, 0) i = i := by
  decide

lemma closed : ∀ (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3), reach o = true →
    reach (step o x) = true ∧ ∀ i, dec (step o x) i = dec o (lt x i) := by
  decide +kernel

lemma T_of (x : Fin 3) (i : Fin 4) : T (FreeMonoid.of x) i = lt x i := by
  rw [T, FreeMonoid.lift_eval_of]
  revert x i
  decide

lemma obs_append (w : List (Fin 3)) (x : Fin 3) : obs (w ++ [x]) = step (obs w) x := by
  simp only [obs, step, DFAReturn.runQ_append_single]

lemma reach_dec (w : List (Fin 3)) :
    reach (obs w) = true ∧ ∀ i, T (FreeMonoid.ofList w) i = dec (obs w) i := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨start.1, fun i => ?_⟩
      rw [show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one]
      exact (start.2 i).symm
  | append_singleton w x ih =>
      obtain ⟨h1, h2⟩ := closed _ x ih.1
      refine ⟨by rw [obs_append]; exact h1, fun i => ?_⟩
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, Equiv.Perm.mul_apply,
        T_of, ih.2, obs_append, h2]

lemma obs_height (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : HasHeightAtMost {w | obs w = o} 1 := by
  obtain ⟨p0, p1, p2, p3⟩ := o
  have heq : ({w | obs w = (p0, p1, p2, p3)} : Language (Fin 3)) =
      ((({w | DFAReturn.runQ a0 0 w = p0}
        ⊓ {w | DFAReturn.runQ a1 0 w = p1})
        ⊓ {w | DFAReturn.runQ a2 0 w = p2})
        ⊓ {w | DFAReturn.runQ a3 0 w = p3}) := by
    ext w
    simp only [obs, Prod.mk.injEq]
    exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩,
      fun ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ => ⟨h0, h1, h2, h3⟩⟩
  rw [heq]
  exact (((good_baseN a0 0 _ a0_cert p0
    ).inter (good_baseN a1 0 _ a1_cert p1)
    ).inter (good_baseN a2 0 _ a2_cert p2)
    ).inter (good_baseN a3 0 _ a3_cert p3)

/-- **Every language recognized by `T` has generalized star height at most one.** -/
theorem height_one (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (ι := Unit)
    (X := fun _ => Fin 4 × Fin 4 × Fin 4 × Fin 3) (fun _ => obs) ?_ (fun _ => obs_height) F
  intro u v huv
  exact Equiv.ext fun i => by rw [(reach_dec u).2, (reach_dec v).2, huv ()]

end C0132_1203_3021

/-! ### The class `0231 1203 2310` (right action); lift `02314675 12475603 23106754` -/

namespace C0231_1203_2310

/-- The morphism: the three letters as permutations of `Fin 4` (table, inverse table). -/
def T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  FreeMonoid.lift ![mkPerm4 ![0, 3, 1, 2] ![0, 2, 3, 1],
    mkPerm4 ![2, 0, 1, 3] ![1, 2, 0, 3],
    mkPerm4 ![3, 2, 0, 1] ![2, 3, 1, 0]]

/-- The letters as tables. -/
def lt (x : Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk [[0, 3, 1, 2], [2, 0, 1, 3], [3, 2, 0, 1]] x i % 4, Nat.mod_lt _ (by decide)⟩

/-- Auxiliary automaton `a0` (4 states, a coset automaton of the lift). -/
def a0 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 1, 2], [2, 3, 3], [0, 2, 1], [3, 0, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0) 400) 5 = true := by
  decide +kernel

/-- Auxiliary automaton `a1` (4 states, a coset automaton of the lift). -/
def a1 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 2], [3, 1, 0], [2, 3, 3], [0, 0, 1]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0) 400) 5 = true := by
  decide +kernel

/-- Auxiliary automaton `a2` (4 states, a coset automaton of the lift). -/
def a2 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 1, 2], [2, 3, 1], [0, 2, 0], [3, 0, 3]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a3` (3 states, a coset automaton of the lift). -/
def a3 (q : Fin 3) (x : Fin 3) : Fin 3 :=
  ⟨lk [[1, 2, 1], [2, 0, 0], [0, 1, 2]] q x % 3, Nat.mod_lt _ (by decide)⟩

lemma a3_cert : Aperiodic.certOK (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0)
    (Aperiodic.dfaCert (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0) 400) 4 = true := by
  decide +kernel

/-- The joint state of the auxiliary automata. -/
def obs (w : List (Fin 3)) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  (DFAReturn.runQ a0 0 w, DFAReturn.runQ a1 0 w, DFAReturn.runQ a2 0 w, DFAReturn.runQ a3 0 w)

/-- The joint step. -/
def step (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  match o with | (o0, o1, o2, o3) => (a0 o0 x, a1 o1 x, a2 o2 x, a3 o3 x)

/-- The decoding table (`[]`: unreachable). -/
def decL : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [], [2, 3, 0, 1], [3, 2, 0, 1], [], [1, 0, 3, 2], [1, 0, 2, 3],
    [], [3, 2, 1, 0], [2, 3, 1, 0], [], [2, 1, 0, 3], [], [3, 1, 0, 2], [0, 3, 2, 1], [],
    [0, 2, 3, 1], [1, 2, 3, 0], [], [1, 3, 2, 0], [3, 0, 1, 2], [], [2, 0, 1, 3], [],
    [2, 1, 3, 0], [3, 1, 2, 0], [], [3, 0, 2, 1], [2, 0, 3, 1], [], [1, 2, 0, 3], [1, 3, 0, 2],
    [], [0, 3, 1, 2], [0, 2, 1, 3], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [0, 3, 1, 2],
    [0, 2, 1, 3], [], [2, 1, 3, 0], [3, 1, 2, 0], [], [3, 0, 2, 1], [2, 0, 3, 1], [1, 2, 3, 0],
    [], [1, 3, 2, 0], [3, 0, 1, 2], [], [2, 0, 1, 3], [2, 1, 0, 3], [], [3, 1, 0, 2],
    [0, 3, 2, 1], [], [0, 2, 3, 1], [1, 0, 3, 2], [1, 0, 2, 3], [], [3, 2, 1, 0], [2, 3, 1, 0],
    [], [0, 1, 2, 3], [0, 1, 3, 2], [], [2, 3, 0, 1], [3, 2, 0, 1], [], [], [0, 3, 1, 2],
    [0, 2, 1, 3], [], [1, 2, 0, 3], [1, 3, 0, 2], [], [3, 0, 2, 1], [2, 0, 3, 1], [],
    [2, 1, 3, 0], [3, 1, 2, 0], [], [], [], [], [], [], [], [], [], [], [], [], [3, 2, 1, 0],
    [2, 3, 1, 0], [], [1, 0, 3, 2], [1, 0, 2, 3], [], [2, 3, 0, 1], [3, 2, 0, 1], [],
    [0, 1, 2, 3], [0, 1, 3, 2], [], [3, 0, 1, 2], [], [2, 0, 1, 3], [1, 2, 3, 0], [],
    [1, 3, 2, 0], [0, 3, 2, 1], [], [0, 2, 3, 1], [2, 1, 0, 3], [], [3, 1, 0, 2], [0, 3, 2, 1],
    [], [0, 2, 3, 1], [2, 1, 0, 3], [], [3, 1, 0, 2], [3, 0, 1, 2], [], [2, 0, 1, 3],
    [1, 2, 3, 0], [], [1, 3, 2, 0], [2, 3, 0, 1], [3, 2, 0, 1], [], [0, 1, 2, 3], [0, 1, 3, 2],
    [], [3, 2, 1, 0], [2, 3, 1, 0], [], [1, 0, 3, 2], [1, 0, 2, 3], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [3, 0, 2, 1], [2, 0, 3, 1], [], [2, 1, 3, 0], [3, 1, 2, 0], [],
    [0, 3, 1, 2], [0, 2, 1, 3], [], [1, 2, 0, 3], [1, 3, 0, 2]]

/-- The code of an observation. -/
def code (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : ℕ :=
  match o with | (o0, o1, o2, o3) => (((o0.val) * 4 + o1.val) * 4 + o2.val) * 3 + o3.val

/-- Reachable observations. -/
def reach (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : Bool := (decL.getD (code o) []) != []

/-- The decoding. -/
def dec (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk decL (code o) i % 4, Nat.mod_lt _ (by decide)⟩

lemma start : reach (0, 0, 0, 0) = true ∧ ∀ i : Fin 4, dec (0, 0, 0, 0) i = i := by
  decide

lemma closed : ∀ (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3), reach o = true →
    reach (step o x) = true ∧ ∀ i, dec (step o x) i = dec o (lt x i) := by
  decide +kernel

lemma T_of (x : Fin 3) (i : Fin 4) : T (FreeMonoid.of x) i = lt x i := by
  rw [T, FreeMonoid.lift_eval_of]
  revert x i
  decide

lemma obs_append (w : List (Fin 3)) (x : Fin 3) : obs (w ++ [x]) = step (obs w) x := by
  simp only [obs, step, DFAReturn.runQ_append_single]

lemma reach_dec (w : List (Fin 3)) :
    reach (obs w) = true ∧ ∀ i, T (FreeMonoid.ofList w) i = dec (obs w) i := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨start.1, fun i => ?_⟩
      rw [show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one]
      exact (start.2 i).symm
  | append_singleton w x ih =>
      obtain ⟨h1, h2⟩ := closed _ x ih.1
      refine ⟨by rw [obs_append]; exact h1, fun i => ?_⟩
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, Equiv.Perm.mul_apply,
        T_of, ih.2, obs_append, h2]

lemma obs_height (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : HasHeightAtMost {w | obs w = o} 1 := by
  obtain ⟨p0, p1, p2, p3⟩ := o
  have heq : ({w | obs w = (p0, p1, p2, p3)} : Language (Fin 3)) =
      ((({w | DFAReturn.runQ a0 0 w = p0}
        ⊓ {w | DFAReturn.runQ a1 0 w = p1})
        ⊓ {w | DFAReturn.runQ a2 0 w = p2})
        ⊓ {w | DFAReturn.runQ a3 0 w = p3}) := by
    ext w
    simp only [obs, Prod.mk.injEq]
    exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩,
      fun ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ => ⟨h0, h1, h2, h3⟩⟩
  rw [heq]
  exact (((good_baseN a0 0 _ a0_cert p0
    ).inter (good_baseN a1 0 _ a1_cert p1)
    ).inter (good_baseN a2 0 _ a2_cert p2)
    ).inter (good_baseN a3 0 _ a3_cert p3)

/-- **Every language recognized by `T` has generalized star height at most one.** -/
theorem height_one (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (ι := Unit)
    (X := fun _ => Fin 4 × Fin 4 × Fin 4 × Fin 3) (fun _ => obs) ?_ (fun _ => obs_height) F
  intro u v huv
  exact Equiv.ext fun i => by rw [(reach_dec u).2, (reach_dec v).2, huv ()]

end C0231_1203_2310

/-! ### The class `0231 1302 2310` (right action); lift `02314675 13025746 23546710` -/

namespace C0231_1302_2310

/-- The morphism: the three letters as permutations of `Fin 4` (table, inverse table). -/
def T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4) :=
  FreeMonoid.lift ![mkPerm4 ![0, 3, 1, 2] ![0, 2, 3, 1],
    mkPerm4 ![2, 0, 3, 1] ![1, 3, 0, 2],
    mkPerm4 ![3, 2, 0, 1] ![2, 3, 1, 0]]

/-- The letters as tables. -/
def lt (x : Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk [[0, 3, 1, 2], [2, 0, 3, 1], [3, 2, 0, 1]] x i % 4, Nat.mod_lt _ (by decide)⟩

/-- Auxiliary automaton `a0` (4 states, a coset automaton of the lift). -/
def a0 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 2], [3, 0, 3], [2, 3, 1], [0, 1, 0]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a0_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a0 0) 400) 5 = true := by
  decide +kernel

/-- Auxiliary automaton `a1` (4 states, a coset automaton of the lift). -/
def a1 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 1, 2], [3, 0, 1], [2, 2, 0], [0, 3, 3]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a1_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a1 0) 400) 4 = true := by
  decide +kernel

/-- Auxiliary automaton `a2` (4 states, a coset automaton of the lift). -/
def a2 (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk [[1, 2, 1], [2, 3, 3], [0, 1, 0], [3, 0, 2]] q x % 4, Nat.mod_lt _ (by decide)⟩

lemma a2_cert : Aperiodic.certOK (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0)
    (Aperiodic.dfaCert (stN 4 0) [0, 1, 2] (DFAReturn.retAut a2 0) 400) 5 = true := by
  decide +kernel

/-- Auxiliary automaton `a3` (3 states, a coset automaton of the lift). -/
def a3 (q : Fin 3) (x : Fin 3) : Fin 3 :=
  ⟨lk [[1, 2, 1], [2, 1, 0], [0, 0, 2]] q x % 3, Nat.mod_lt _ (by decide)⟩

lemma a3_cert : Aperiodic.certOK (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0)
    (Aperiodic.dfaCert (stN 3 0) [0, 1, 2] (DFAReturn.retAut a3 0) 400) 4 = true := by
  decide +kernel

/-- The joint state of the auxiliary automata. -/
def obs (w : List (Fin 3)) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  (DFAReturn.runQ a0 0 w, DFAReturn.runQ a1 0 w, DFAReturn.runQ a2 0 w, DFAReturn.runQ a3 0 w)

/-- The joint step. -/
def step (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3) : Fin 4 × Fin 4 × Fin 4 × Fin 3 :=
  match o with | (o0, o1, o2, o3) => (a0 o0 x, a1 o1 x, a2 o2 x, a3 o3 x)

/-- The decoding table (`[]`: unreachable). -/
def decL : List (List ℕ) :=
  [[0, 1, 2, 3], [], [0, 2, 1, 3], [], [], [], [2, 1, 0, 3], [1, 2, 0, 3], [], [], [1, 0, 2, 3],
    [2, 0, 1, 3], [3, 2, 1, 0], [], [3, 1, 2, 0], [], [], [], [3, 0, 1, 2], [3, 0, 2, 1], [], [],
    [3, 2, 0, 1], [3, 1, 0, 2], [1, 0, 3, 2], [], [2, 0, 3, 1], [], [], [], [1, 2, 3, 0],
    [2, 1, 3, 0], [], [], [0, 1, 3, 2], [0, 2, 3, 1], [2, 3, 0, 1], [], [1, 3, 0, 2], [], [], [],
    [0, 3, 2, 1], [0, 3, 1, 2], [], [], [2, 3, 1, 0], [1, 3, 2, 0], [], [0, 1, 3, 2],
    [0, 2, 3, 1], [1, 2, 3, 0], [2, 1, 3, 0], [], [], [], [], [1, 0, 3, 2], [], [2, 0, 3, 1], [],
    [2, 3, 1, 0], [1, 3, 2, 0], [0, 3, 2, 1], [0, 3, 1, 2], [], [], [], [], [2, 3, 0, 1], [],
    [1, 3, 0, 2], [], [1, 0, 2, 3], [2, 0, 1, 3], [2, 1, 0, 3], [1, 2, 0, 3], [], [], [], [],
    [0, 1, 2, 3], [], [0, 2, 1, 3], [], [3, 2, 0, 1], [3, 1, 0, 2], [3, 0, 1, 2], [3, 0, 2, 1],
    [], [], [], [], [3, 2, 1, 0], [], [3, 1, 2, 0], [0, 3, 2, 1], [0, 3, 1, 2], [], [],
    [2, 3, 1, 0], [1, 3, 2, 0], [2, 3, 0, 1], [], [1, 3, 0, 2], [], [], [], [1, 2, 3, 0],
    [2, 1, 3, 0], [], [], [0, 1, 3, 2], [0, 2, 3, 1], [1, 0, 3, 2], [], [2, 0, 3, 1], [], [], [],
    [3, 0, 1, 2], [3, 0, 2, 1], [], [], [3, 2, 0, 1], [3, 1, 0, 2], [3, 2, 1, 0], [],
    [3, 1, 2, 0], [], [], [], [2, 1, 0, 3], [1, 2, 0, 3], [], [], [1, 0, 2, 3], [2, 0, 1, 3],
    [0, 1, 2, 3], [], [0, 2, 1, 3], [], [], [], [], [], [], [3, 2, 1, 0], [], [3, 1, 2, 0], [],
    [3, 2, 0, 1], [3, 1, 0, 2], [3, 0, 1, 2], [3, 0, 2, 1], [], [], [], [], [0, 1, 2, 3], [],
    [0, 2, 1, 3], [], [1, 0, 2, 3], [2, 0, 1, 3], [2, 1, 0, 3], [1, 2, 0, 3], [], [], [], [],
    [2, 3, 0, 1], [], [1, 3, 0, 2], [], [2, 3, 1, 0], [1, 3, 2, 0], [0, 3, 2, 1], [0, 3, 1, 2],
    [], [], [], [], [1, 0, 3, 2], [], [2, 0, 3, 1], [], [0, 1, 3, 2], [0, 2, 3, 1], [1, 2, 3, 0],
    [2, 1, 3, 0], []]

/-- The code of an observation. -/
def code (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : ℕ :=
  match o with | (o0, o1, o2, o3) => (((o0.val) * 4 + o1.val) * 4 + o2.val) * 3 + o3.val

/-- Reachable observations. -/
def reach (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : Bool := (decL.getD (code o) []) != []

/-- The decoding. -/
def dec (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk decL (code o) i % 4, Nat.mod_lt _ (by decide)⟩

lemma start : reach (0, 0, 0, 0) = true ∧ ∀ i : Fin 4, dec (0, 0, 0, 0) i = i := by
  decide

lemma closed : ∀ (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) (x : Fin 3), reach o = true →
    reach (step o x) = true ∧ ∀ i, dec (step o x) i = dec o (lt x i) := by
  decide +kernel

lemma T_of (x : Fin 3) (i : Fin 4) : T (FreeMonoid.of x) i = lt x i := by
  rw [T, FreeMonoid.lift_eval_of]
  revert x i
  decide

lemma obs_append (w : List (Fin 3)) (x : Fin 3) : obs (w ++ [x]) = step (obs w) x := by
  simp only [obs, step, DFAReturn.runQ_append_single]

lemma reach_dec (w : List (Fin 3)) :
    reach (obs w) = true ∧ ∀ i, T (FreeMonoid.ofList w) i = dec (obs w) i := by
  induction w using List.reverseRecOn with
  | nil =>
      refine ⟨start.1, fun i => ?_⟩
      rw [show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one]
      exact (start.2 i).symm
  | append_singleton w x ih =>
      obtain ⟨h1, h2⟩ := closed _ x ih.1
      refine ⟨by rw [obs_append]; exact h1, fun i => ?_⟩
      rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, Equiv.Perm.mul_apply,
        T_of, ih.2, obs_append, h2]

lemma obs_height (o : Fin 4 × Fin 4 × Fin 4 × Fin 3) : HasHeightAtMost {w | obs w = o} 1 := by
  obtain ⟨p0, p1, p2, p3⟩ := o
  have heq : ({w | obs w = (p0, p1, p2, p3)} : Language (Fin 3)) =
      ((({w | DFAReturn.runQ a0 0 w = p0}
        ⊓ {w | DFAReturn.runQ a1 0 w = p1})
        ⊓ {w | DFAReturn.runQ a2 0 w = p2})
        ⊓ {w | DFAReturn.runQ a3 0 w = p3}) := by
    ext w
    simp only [obs, Prod.mk.injEq]
    exact ⟨fun ⟨h0, h1, h2, h3⟩ => ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩,
      fun ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ => ⟨h0, h1, h2, h3⟩⟩
  rw [heq]
  exact (((good_baseN a0 0 _ a0_cert p0
    ).inter (good_baseN a1 0 _ a1_cert p1)
    ).inter (good_baseN a2 0 _ a2_cert p2)
    ).inter (good_baseN a3 0 _ a3_cert p3)

/-- **Every language recognized by `T` has generalized star height at most one.** -/
theorem height_one (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  refine height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (ι := Unit)
    (X := fun _ => Fin 4 × Fin 4 × Fin 4 × Fin 3) (fun _ => obs) ?_ (fun _ => obs_height) F
  intro u v huv
  exact Equiv.ext fun i => by rw [(reach_dec u).2, (reach_dec v).2, huv ()]

end C0231_1302_2310

end S4Three

end GeneralizedStarHeight
