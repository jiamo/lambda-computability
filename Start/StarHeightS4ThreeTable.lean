import Start.StarHeightS4ThreeBase

/-!
# Height one from a finite family of automata and a table of joint states

`height_one_of_tableOK` is the generic form of the certificates of `StarHeightS4ThreeHitsA`.
The data are

* `L`: the three letters of a morphism `T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)`, as tables
  (`letT L x i = T (of x) i`);
* `A`: a list of automata on `Fin 4` over three letters (`autT t q x`, rows are states), each with
  base state `0` and every state language of generalized star height at most one;
* `R`: a list of pairs (joint state of the automata, table of `T w`).

`tableOK L A R` checks that `R` contains the start pair, is closed under every letter, and is a
function of the joint state.  Then the joint state of the automata after `w` determines `T w`,
and every language recognized by `T` has generalized star height at most one.
-/

namespace GeneralizedStarHeight

namespace S4Three

open S4Two

/-- An automaton on `Fin 4` over three letters, from a table (row `q`: `δ q 0, δ q 1, δ q 2`). -/
def autT (t : List (List ℕ)) (q : Fin 4) (x : Fin 3) : Fin 4 :=
  ⟨lk t q x % 4, Nat.mod_lt _ (by decide)⟩

/-- Three letters of `S₄`, from a table (row `x` lists the images of `0, 1, 2, 3`). -/
def letT (L : List (List ℕ)) (x : Fin 3) (i : Fin 4) : Fin 4 :=
  ⟨lk L x i % 4, Nat.mod_lt _ (by decide)⟩

/-- The table of a permutation of `Fin 4`. -/
def tbl (σ : Equiv.Perm (Fin 4)) : List (Fin 4) := [σ 0, σ 1, σ 2, σ 3]

/-- The joint state of a list of automata after reading `w` from the base state `0`. -/
def jobs (A : List (List (List ℕ))) (w : List (Fin 3)) : List (Fin 4) :=
  A.map fun t => DFAReturn.runQ (autT t) 0 w

/-- The joint step. -/
def jstep (A : List (List (List ℕ))) (o : List (Fin 4)) (x : Fin 3) : List (Fin 4) :=
  List.zipWith (fun t q => autT t q x) A o

/-- The table after one more letter. -/
def tstep (L : List (List ℕ)) (p : List (Fin 4)) (x : Fin 3) : List (Fin 4) :=
  [p.getD (letT L x 0) 0, p.getD (letT L x 1) 0, p.getD (letT L x 2) 0, p.getD (letT L x 3) 0]

/-- **The certificate.** -/
def tableOK (L : List (List ℕ)) (A : List (List (List ℕ)))
    (R : List (List (Fin 4) × List (Fin 4))) : Bool :=
  decide ((A.map fun _ => (0 : Fin 4), [0, 1, 2, 3]) ∈ R) &&
    decide (R.map Prod.fst).Nodup &&
    R.all fun e => ([0, 1, 2] : List (Fin 3)).all fun x =>
      decide ((jstep A e.1 x, tstep L e.2 x) ∈ R)

lemma jobs_nil (A : List (List (List ℕ))) : jobs A [] = A.map fun _ => (0 : Fin 4) := rfl

lemma zipWith_map_self {β γ δ : Type*} (f : β → γ → δ) (g : β → γ) :
    ∀ A : List β, List.zipWith f A (A.map g) = A.map fun t => f t (g t)
  | [] => rfl
  | t :: A => by simp [zipWith_map_self f g A]

lemma jobs_append (A : List (List (List ℕ))) (w : List (Fin 3)) (x : Fin 3) :
    jobs A (w ++ [x]) = jstep A (jobs A w) x := by
  simp only [jobs, jstep, zipWith_map_self, DFAReturn.runQ_append_single]

lemma tbl_getD (σ : Equiv.Perm (Fin 4)) (j : Fin 4) : (tbl σ).getD j 0 = σ j := by
  fin_cases j <;> rfl

lemma tbl_one : tbl 1 = [0, 1, 2, 3] := rfl

lemma tbl_inj {σ τ : Equiv.Perm (Fin 4)} (h : tbl σ = tbl τ) : σ = τ :=
  Equiv.ext fun j => by rw [← tbl_getD σ j, ← tbl_getD τ j, h]

/-- The invariant: the pair (joint state, table of `T w`) is listed in `R`. -/
lemma mem_of_tableOK {L : List (List ℕ)} {A : List (List (List ℕ))}
    {R : List (List (Fin 4) × List (Fin 4))} (h : tableOK L A R = true)
    (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i)
    (w : List (Fin 3)) : (jobs A w, tbl (T (FreeMonoid.ofList w))) ∈ R := by
  simp only [tableOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hstart, -⟩, hclosed⟩ := h
  induction w using List.reverseRecOn with
  | nil =>
      rw [jobs_nil, show FreeMonoid.ofList ([] : List (Fin 3)) = 1 from rfl, map_one, tbl_one]
      exact hstart
  | append_singleton w x ih =>
      have hx := hclosed _ ih x (by fin_cases x <;> simp)
      have htbl : tbl (T (FreeMonoid.ofList (w ++ [x]))) =
          tstep L (tbl (T (FreeMonoid.ofList w))) x := by
        rw [FreeMonoid.ofList_append, map_mul, FreeMonoid.ofList_singleton]
        simp only [tstep, tbl_getD, ← hT]
        rfl
      rw [jobs_append, htbl]
      exact hx

/-- **A certified family of automata determines the value of `T`.** -/
theorem height_one_of_tableOK (L : List (List ℕ)) (A : List (List (List ℕ)))
    (R : List (List (Fin 4) × List (Fin 4))) (h : tableOK L A R = true)
    (hA : ∀ t ∈ A, ∀ q : Fin 4, HasHeightAtMost {w | DFAReturn.runQ (autT t) 0 w = q} 1)
    (T : FreeMonoid (Fin 3) →* Equiv.Perm (Fin 4)) (hT : ∀ x i, T (FreeMonoid.of x) i = letT L x i)
    (F : Set (Equiv.Perm (Fin 4))) :
    HasHeightAtMost {w : List (Fin 3) | T (FreeMonoid.ofList w) ∈ F} 1 := by
  have hnd : (R.map Prod.fst).Nodup := by
    simp only [tableOK, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.2
  have hdet : ∀ u v : List (Fin 3), (∀ i : Fin A.length,
      DFAReturn.runQ (autT (A.get i)) 0 u = DFAReturn.runQ (autT (A.get i)) 0 v) →
      T (FreeMonoid.ofList u) = T (FreeMonoid.ofList v) := by
    intro u v huv
    have hj : jobs A u = jobs A v := by
      refine List.ext_get (by simp [jobs]) fun n h1 h2 => ?_
      simp only [jobs, List.get_eq_getElem, List.getElem_map]
      have hn : n < A.length := by simpa [jobs] using h1
      exact huv ⟨n, hn⟩
    have hu := mem_of_tableOK h T hT u
    have hv := mem_of_tableOK h T hT v
    rw [hj] at hu
    have := List.inj_on_of_nodup_map hnd hu hv rfl
    exact tbl_inj (Prod.mk.inj this).2
  exact height_one_of_determined (fun w => T (FreeMonoid.ofList w)) (ι := Fin A.length)
    (X := fun _ => Fin 4) (fun i w => DFAReturn.runQ (autT (A.get i)) 0 w) hdet
    (fun i q => hA _ (List.get_mem _ _) q) F


end S4Three

end GeneralizedStarHeight
