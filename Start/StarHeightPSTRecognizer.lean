import Start.StarHeightPSTHeightOne

/-!
# Every language recognized by the PST morphism has height at most one

`PST.recog : FreeMonoid AB →* Perm (Fin 4) × Multiplicative (ZMod 2)` (`a ↦ ((2 3), 0)`,
`b ↦ ((0 1 2 3), 1)`) recognizes `L_PST`.  Its value on a word `w` is determined by the joint
state `jstate w` of four automata, each of whose state languages has height at most one:

* `|w|_a mod 2` and `|w|_b mod 2` (commutative counts);
* the `S₃` automaton `stateOf 0` (`stateOf_height`);
* the `S₄` automaton `s4state` (`s4state_height`, star-free first returns).

* `PST.recog_eq_of_jstate`: `jstate w = jstate w' → recog w = recog w'` (the finite check
  `jstep_check` on the 48 joint states, on `Fin`-valued data).
* `PST.recog_languages_height_one`: every language `{w | recog w ∈ F}` has height at most one.
* `PST.pstS4_languages_height_one`: in particular every language recognized by the `S₄` part
  `a ↦ (2 3)`, `b ↦ (0 1 2 3)`.
-/

namespace GeneralizedStarHeight

namespace PST

open AB

/-- The joint step of the four automata. -/
def jstep (j : Fin 2 × Fin 2 × Fin 3 × Fin 4) (x : AB) : Fin 2 × Fin 2 × Fin 3 × Fin 4 :=
  (j.1 + (if x = a then 1 else 0), j.2.1 + (if x = b then 1 else 0), move j.2.2.1 x,
    move4 j.2.2.2 x)

/-- The joint state: `(|w|_a mod 2, |w|_b mod 2, stateOf 0 w, s4state w)`. -/
def jstate (w : List AB) : Fin 2 × Fin 2 × Fin 3 × Fin 4 := w.foldl jstep (0, 0, 0, 0)

/-- The images `i ↦ g⁻¹ i` of the `S₄` part, read off a reachable joint state. -/
def jtup (j : Fin 2 × Fin 2 × Fin 3 × Fin 4) : Fin 4 → Fin 4 :=
  (![![![![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]],
    ![![1, 2, 0, 3], ![0, 3, 1, 2], ![3, 0, 2, 1], ![2, 1, 3, 0]],
    ![![2, 0, 1, 3], ![3, 1, 0, 2], ![0, 2, 3, 1], ![1, 3, 2, 0]]],
    ![![![0, 2, 1, 3], ![1, 3, 0, 2], ![2, 0, 3, 1], ![3, 1, 2, 0]],
    ![![1, 0, 2, 3], ![0, 1, 3, 2], ![3, 2, 0, 1], ![2, 3, 1, 0]],
    ![![2, 1, 0, 3], ![3, 0, 1, 2], ![0, 3, 2, 1], ![1, 2, 3, 0]]]],
    ![![![![0, 2, 1, 3], ![1, 3, 0, 2], ![2, 0, 3, 1], ![3, 1, 2, 0]],
    ![![1, 0, 2, 3], ![0, 1, 3, 2], ![3, 2, 0, 1], ![2, 3, 1, 0]],
    ![![2, 1, 0, 3], ![3, 0, 1, 2], ![0, 3, 2, 1], ![1, 2, 3, 0]]],
    ![![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]],
    ![![1, 2, 0, 3], ![0, 3, 1, 2], ![3, 0, 2, 1], ![2, 1, 3, 0]],
    ![![2, 0, 1, 3], ![3, 1, 0, 2], ![0, 2, 3, 1], ![1, 3, 2, 0]]]]] :
    Fin 2 → Fin 2 → Fin 3 → Fin 4 → Fin 4 → Fin 4) j.1 j.2.1 j.2.2.1 j.2.2.2

/-- The inverses of the images of the letters. -/
def genSymm : AB → Fin 4 → Fin 4
  | a => ![0, 1, 3, 2]
  | b => ![3, 0, 1, 2]

lemma jstep_check_a : ∀ (j : Fin 2 × Fin 2 × Fin 3 × Fin 4) (i : Fin 4),
    jtup (jstep j a) i = genSymm a (jtup j i) := by
  decide +kernel

lemma jstep_check_b : ∀ (j : Fin 2 × Fin 2 × Fin 3 × Fin 4) (i : Fin 4),
    jtup (jstep j b) i = genSymm b (jtup j i) := by
  decide +kernel

/-- The finite step check, on all `48` joint states (all of them are reachable). -/
lemma jstep_check (j : Fin 2 × Fin 2 × Fin 3 × Fin 4) (x : AB) (i : Fin 4) :
    jtup (jstep j x) i = genSymm x (jtup j i) := by
  cases x
  · exact jstep_check_a j i
  · exact jstep_check_b j i

lemma gen_symm_apply (x : AB) (i : Fin 4) : (gen x).1.symm i = genSymm x i := by
  cases x <;> rfl

lemma jstate_append_single (w : List AB) (x : AB) : jstate (w ++ [x]) = jstep (jstate w) x := by
  rw [jstate, List.foldl_append]
  rfl

lemma recog_append_single (w : List AB) (x : AB) :
    recog (FreeMonoid.ofList (w ++ [x])) = recog (FreeMonoid.ofList w) * gen x := by
  rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton, recog,
    FreeMonoid.lift_eval_of]

lemma recog_fst_symm (w : List AB) (i : Fin 4) :
    (recog (FreeMonoid.ofList w)).1.symm i = jtup (jstate w) i := by
  induction w using List.reverseRecOn generalizing i with
  | nil => revert i; decide
  | append_singleton w x ih =>
      rw [jstate_append_single, recog_append_single, Prod.fst_mul, Equiv.Perm.mul_def,
        Equiv.symm_trans_apply, gen_symm_apply, ih, jstep_check]

lemma jstate_fst_val (w : List AB) : (jstate w).1.val = w.count a % 2 := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [jstate_append_single, List.count_append]
      cases x <;> simp [jstep, Fin.val_add, ih]

lemma jstate_snd_val (w : List AB) : (jstate w).2.1.val = w.count b % 2 := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [jstate_append_single, List.count_append]
      cases x <;> simp [jstep, Fin.val_add, ih]

lemma jstate_state (w : List AB) : (jstate w).2.2.1 = stateOf 0 w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [jstate_append_single, stateOf_append_single, ← ih]
      rfl

lemma jstate_s4 (w : List AB) : (jstate w).2.2.2 = s4state w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [jstate_append_single, s4state_append_single, ← ih]
      rfl

lemma recog_snd (w : List AB) :
    recog (FreeMonoid.ofList w) = ((recog (FreeMonoid.ofList w)).1,
      Multiplicative.ofAdd ((w.count b : ℕ) : ZMod 2)) := by
  refine Prod.ext rfl ?_
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w x ih =>
      rw [recog_append_single, Prod.snd_mul, ih, List.count_append]
      cases x
      · simp [gen]
      · simp [gen, ofAdd_add]

/-- **The joint state determines the recognizer.** -/
theorem recog_eq_of_jstate {w w' : List AB} (h : jstate w = jstate w') :
    recog (FreeMonoid.ofList w) = recog (FreeMonoid.ofList w') := by
  rw [recog_snd w, recog_snd w']
  have h1 : (recog (FreeMonoid.ofList w)).1.symm = (recog (FreeMonoid.ofList w')).1.symm :=
    Equiv.ext fun i => by rw [recog_fst_symm, recog_fst_symm, h]
  have h2 : ((w.count b : ℕ) : ZMod 2) = ((w'.count b : ℕ) : ZMod 2) := by
    rw [← ZMod.natCast_mod, ← jstate_snd_val, h, jstate_snd_val, ZMod.natCast_mod]
  rw [Equiv.symm_bijective.injective h1, h2]

/-- The parity of a letter. -/
lemma countParity_height (x : AB) (r : ℕ) : HasHeightAtMost {w : List AB | w.count x % 2 = r} 1 :=
  countIn_height x (K := {k | k % 2 = r}) (m := 0) (p := 2) (by norm_num)
    (fun k _ => by simp [Nat.add_mod_right])

lemma jstate_height (j : Fin 2 × Fin 2 × Fin 3 × Fin 4) :
    HasHeightAtMost {w : List AB | jstate w = j} 1 := by
  have heq : ({w : List AB | jstate w = j} : Language AB) =
      (({w | w.count a % 2 = j.1.val} ⊓ {w | w.count b % 2 = j.2.1.val}) ⊓
        {w | stateOf 0 w = j.2.2.1}) ⊓ {w | s4state w = j.2.2.2} := by
    ext w
    change jstate w = j ↔ ((w.count a % 2 = j.1.val ∧ w.count b % 2 = j.2.1.val) ∧
      stateOf 0 w = j.2.2.1) ∧ s4state w = j.2.2.2
    rw [← jstate_fst_val, ← jstate_snd_val, ← jstate_state, ← jstate_s4, ← Fin.ext_iff,
      ← Fin.ext_iff]
    obtain ⟨j1, j2, j3, j4⟩ := j
    constructor
    · intro h
      rw [h]
      exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))
  rw [heq]
  exact (((countParity_height a _).inter (countParity_height b _)).inter
    (stateOf_height _)).inter (s4state_height _)

/-- **Every language recognized by the PST morphism `S₄ × Z₂` has height at most one.** -/
theorem recog_languages_height_one (F : Set (Equiv.Perm (Fin 4) × Multiplicative (ZMod 2))) :
    HasHeightAtMost {w | recog (FreeMonoid.ofList w) ∈ F} 1 := by
  have heq : ({w | recog (FreeMonoid.ofList w) ∈ F} : Language AB) =
      ⨆ j : {j // ∃ w : List AB, jstate w = j ∧ recog (FreeMonoid.ofList w) ∈ F},
        {w | jstate w = j.1} := by
    ext w
    constructor
    · intro hw
      exact Language.mem_iSup.mpr ⟨⟨jstate w, w, rfl, hw⟩, rfl⟩
    · intro hw
      obtain ⟨⟨j, w', hj, hF⟩, hw⟩ := Language.mem_iSup.mp hw
      have hw' : jstate w = j := hw
      show recog (FreeMonoid.ofList w) ∈ F
      rw [recog_eq_of_jstate (hw'.trans hj.symm)]
      exact hF
  rw [heq]
  exact HasHeightAtMost.iSup _ fun j => jstate_height j.1

/-- The `S₄` part of the PST morphism: `a ↦ (2 3)`, `b ↦ (0 1 2 3)`. -/
def pstS4 : FreeMonoid AB →* Equiv.Perm (Fin 4) :=
  (MonoidHom.fst (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2))).comp recog

/-- **Every language recognized by the `S₄` part of the PST morphism has height at most one.** -/
theorem pstS4_languages_height_one (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w | pstS4 (FreeMonoid.ofList w) ∈ F} 1 :=
  recog_languages_height_one (Prod.fst ⁻¹' F)

end PST

end GeneralizedStarHeight
