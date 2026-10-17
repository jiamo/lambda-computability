import Start.StarHeightHeight

/-!
# Star-free first returns give height one

For an arbitrary automaton `δ : Q → α → Q` (letters need not act bijectively) and a base state
`q₀`:

* `DFAReturn.firstReturn δ q₀`: the nonempty words that come back to `q₀` for the first time at
  their end;
* `DFAReturn.avoidTo δ q₀ q`: the words leading from `q₀` to `q` that never revisit `q₀` after the
  start (for `q = q₀` this is `{ε}`, `DFAReturn.avoidTo_self`);
* `DFAReturn.runQ_eq_kstar_mul`: `{w | q₀·w = q} = (firstReturn δ q₀)∗ · avoidTo δ q₀ q`, by
  factoring at the last visit to `q₀`;
* `height_one_of_starFree_returns`: if both factors are star-free, `{w | q₀·w = q}` has
  generalized star height at most one.

`DFAReturn.retAut` is an automaton (a copy of `δ` that dies after the first return) whose final
state determines membership in both factors (`firstReturn_eq_retAut`, `avoidTo_eq_retAut`), so
star-freeness of the factors can be certified by `Aperiodic.starFree_of_dfa_closed`.
-/

namespace GeneralizedStarHeight

open scoped Computability

namespace DFAReturn

variable {Q α : Type*} (δ : Q → α → Q)

/-- The run of an automaton. -/
def runQ (q : Q) (w : List α) : Q := w.foldl δ q

/-- The first-return code to `q₀`. -/
def firstReturn (q₀ : Q) : Language α :=
  {w | w ≠ [] ∧ runQ δ q₀ w = q₀ ∧ ∀ i, 0 < i → i < w.length → runQ δ q₀ (w.take i) ≠ q₀}

/-- The words leading from `q₀` to `q` without revisiting `q₀`. -/
def avoidTo (q₀ q : Q) : Language α :=
  {w | runQ δ q₀ w = q ∧ ∀ i, 0 < i → i ≤ w.length → runQ δ q₀ (w.take i) ≠ q₀}

lemma runQ_append (q : Q) (u v : List α) : runQ δ q (u ++ v) = runQ δ (runQ δ q u) v :=
  List.foldl_append

lemma runQ_append_single (q : Q) (w : List α) (x : α) :
    runQ δ q (w ++ [x]) = δ (runQ δ q w) x := by
  rw [runQ_append]
  rfl

lemma avoidTo_self (q₀ : Q) : avoidTo δ q₀ q₀ = {[]} := by
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    have hpos : 0 < w.length := List.length_pos_iff.mpr hne
    exact h2 w.length hpos le_rfl (by rw [List.take_length]; exact h1)
  · intro hw
    have hw' : w = [] := hw
    subst hw'
    exact ⟨rfl, fun i hi hle => absurd hle (by simp; omega)⟩

lemma kstar_cons' {l : Language α} {y v : List α} (hy : y ∈ l) (hv : v ∈ l∗) : y ++ v ∈ l∗ := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hv
  refine Language.mem_kstar.mpr ⟨y :: L, by simp, fun z hz => ?_⟩
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hy
  · exact hL z hz

lemma runQ_of_mem_kstar {q₀ : Q} {w : List α} (hw : w ∈ (firstReturn δ q₀)∗) :
    runQ δ q₀ w = q₀ := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hw
  clear hw
  induction L with
  | nil => rfl
  | cons y L ih =>
      rw [List.flatten_cons, runQ_append, (hL y List.mem_cons_self).2.1]
      exact ih fun z hz => hL z (List.mem_cons_of_mem _ hz)

lemma mem_kstar_of_runQ (q₀ : Q) : ∀ (n : ℕ) (w : List α), w.length ≤ n → runQ δ q₀ w = q₀ →
    w ∈ (firstReturn δ q₀)∗ := by
  classical
  intro n
  induction n with
  | zero =>
      intro w hl _
      rw [List.eq_nil_of_length_eq_zero (by omega : w.length = 0)]
      exact Language.nil_mem_kstar _
  | succ n ih =>
      intro w hl hw
      by_cases hne : w = []
      · rw [hne]
        exact Language.nil_mem_kstar _
      have hpos : 0 < w.length := List.length_pos_iff.mpr hne
      have hex : ∃ i, 0 < i ∧ runQ δ q₀ (w.take i) = q₀ :=
        ⟨w.length, hpos, by rw [List.take_length]; exact hw⟩
      set j := Nat.find hex with hj
      have hjspec : 0 < j ∧ runQ δ q₀ (w.take j) = q₀ := Nat.find_spec hex
      have hjle : j ≤ w.length := Nat.find_min' hex ⟨hpos, by rw [List.take_length]; exact hw⟩
      have hfirst : w.take j ∈ firstReturn δ q₀ := by
        refine ⟨?_, hjspec.2, fun i hi hil => ?_⟩
        · intro h
          have h2 := congrArg List.length h
          rw [List.length_take, List.length_nil] at h2
          have := hjspec.1
          omega
        · rw [List.length_take] at hil
          have hij : i < j := by omega
          have hmin := Nat.find_min hex hij
          rw [List.take_take, show min i j = i by omega]
          intro h
          exact hmin ⟨hi, h⟩
      have hdrop : runQ δ q₀ (w.drop j) = q₀ := by
        have h := runQ_append δ q₀ (w.take j) (w.drop j)
        rw [List.take_append_drop, hjspec.2, hw] at h
        exact h.symm
      have hj0 := hjspec.1
      have hrest := ih (w.drop j) (by simp; omega) hdrop
      have := kstar_cons' hfirst hrest
      rwa [List.take_append_drop] at this

/-- **Factoring at the last visit to `q₀`.** -/
theorem runQ_eq_kstar_mul (q₀ q : Q) :
    ({w | runQ δ q₀ w = q} : Language α) = (firstReturn δ q₀)∗ * avoidTo δ q₀ q := by
  classical
  ext w
  constructor
  · intro hw
    have hw' : runQ δ q₀ w = q := hw
    set i := Nat.findGreatest (fun i => runQ δ q₀ (w.take i) = q₀) w.length with hi
    have hispec : runQ δ q₀ (w.take i) = q₀ :=
      Nat.findGreatest_spec (P := fun i => runQ δ q₀ (w.take i) = q₀) (Nat.zero_le _) rfl
    have hile : i ≤ w.length := Nat.findGreatest_le _
    refine Language.mem_mul.mpr ⟨w.take i, mem_kstar_of_runQ δ q₀ _ _ le_rfl hispec,
      w.drop i, ⟨?_, fun k hk hkl => ?_⟩, List.take_append_drop _ _⟩
    · have h := runQ_append δ q₀ (w.take i) (w.drop i)
      rw [List.take_append_drop, hispec] at h
      rw [← h, hw']
    · intro hq
      rw [List.length_drop] at hkl
      have h := runQ_append δ q₀ (w.take i) ((w.drop i).take k)
      rw [hispec, hq, ← List.take_add] at h
      exact Nat.findGreatest_is_greatest (P := fun i => runQ δ q₀ (w.take i) = q₀)
        (show i < i + k by omega) (by omega) h
  · intro hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hw
    show runQ δ q₀ (u ++ v) = q
    rw [runQ_append, runQ_of_mem_kstar δ hu]
    exact hv.1

/-! ### An automaton for the two factors -/

/-- A copy of `δ` started at `q₀`, which records a return to `q₀` and dies on the next letter. -/
def retAut [DecidableEq Q] (q₀ : Q) : Option (Q × Bool) → α → Option (Q × Bool)
  | some (q, false), x => some (δ q x, decide (δ q x = q₀))
  | _, _ => none

/-- No visit to `q₀` after the start. -/
def NoHit (q₀ : Q) (w : List α) : Prop :=
  ∀ i, 0 < i → i ≤ w.length → runQ δ q₀ (w.take i) ≠ q₀

lemma noHit_append_single (q₀ : Q) (w : List α) (x : α) :
    NoHit δ q₀ (w ++ [x]) ↔ NoHit δ q₀ w ∧ runQ δ q₀ (w ++ [x]) ≠ q₀ := by
  constructor
  · intro h
    refine ⟨fun i hi hle => ?_, ?_⟩
    · have := h i hi (by simp; omega)
      rwa [List.take_append_of_le_length hle] at this
    · have := h (w.length + 1) (by omega) (by simp)
      rwa [List.take_of_length_le (by simp)] at this
  · rintro ⟨h1, h2⟩ i hi hle
    simp only [List.length_append, List.length_cons, List.length_nil] at hle
    by_cases hiw : i ≤ w.length
    · rw [List.take_append_of_le_length hiw]
      exact h1 i hi hiw
    · rw [List.take_of_length_le (by simp; omega)]
      exact h2

lemma firstReturn_append_single (q₀ : Q) (w : List α) (x : α) :
    w ++ [x] ∈ firstReturn δ q₀ ↔ NoHit δ q₀ w ∧ runQ δ q₀ (w ++ [x]) = q₀ := by
  constructor
  · rintro ⟨-, h2, h3⟩
    refine ⟨fun i hi hle => ?_, h2⟩
    have := h3 i hi (by simp; omega)
    rwa [List.take_append_of_le_length hle] at this
  · rintro ⟨h1, h2⟩
    refine ⟨by simp, h2, fun i hi hil => ?_⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hil
    rw [List.take_append_of_le_length (by omega)]
    exact h1 i hi (by omega)

lemma retAut_spec [DecidableEq Q] (q₀ : Q) (w : List α) (q : Q) :
    (w.foldl (retAut δ q₀) (some (q₀, false)) = some (q, false) ↔
        runQ δ q₀ w = q ∧ NoHit δ q₀ w) ∧
      (w.foldl (retAut δ q₀) (some (q₀, false)) = some (q, true) ↔
        q = q₀ ∧ w ∈ firstReturn δ q₀) := by
  induction w using List.reverseRecOn generalizing q with
  | nil =>
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => absurd rfl h.2.1⟩⟩
      · have h' : q₀ = q := by simpa using h
        exact ⟨h', fun i hi hle => absurd hle (by simp; omega)⟩
      · rw [← h.1]
        rfl
      · simp at h
  | append_singleton w x ih =>
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil, noHit_append_single,
        firstReturn_append_single, runQ_append_single]
      have ih0 := (ih (runQ δ q₀ w)).1
      generalize hS : w.foldl (retAut δ q₀) (some (q₀, false)) = S at ih ih0
      rcases S with _ | ⟨p, _ | _⟩
      · have hn : ¬ NoHit δ q₀ w := fun h => absurd (ih0.mpr ⟨rfl, h⟩) (by simp)
        simp [retAut, hn]
      · obtain ⟨hp, hnh⟩ := (ih p).1.mp rfl
        subst hp
        simp only [retAut, Option.some.injEq, Prod.mk.injEq, hnh, true_and]
        constructor
        · constructor
          · rintro ⟨h1, h2⟩
            exact ⟨h1, fun h => by simp [h] at h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h1, by simpa using h2⟩
        · constructor
          · rintro ⟨h1, h2⟩
            have h2' : δ (runQ δ q₀ w) x = q₀ := by simpa using h2
            exact ⟨h1.symm.trans h2', h2'⟩
          · rintro ⟨h1, h2⟩
            exact ⟨h2.trans h1.symm, by simpa using h2⟩
      · have hn : ¬ NoHit δ q₀ w := fun h => absurd (ih0.mpr ⟨rfl, h⟩) (by simp)
        simp [retAut, hn]

/-- The first-return code as a language of `retAut`. -/
theorem firstReturn_eq_retAut [DecidableEq Q] (q₀ : Q) :
    firstReturn δ q₀ = {w | w.foldl (retAut δ q₀) (some (q₀, false)) = some (q₀, true)} := by
  ext w
  exact (and_iff_right rfl).symm.trans ((retAut_spec δ q₀ w q₀).2.symm)

/-- The avoiding paths as a language of `retAut`. -/
theorem avoidTo_eq_retAut [DecidableEq Q] (q₀ q : Q) :
    avoidTo δ q₀ q = {w | w.foldl (retAut δ q₀) (some (q₀, false)) = some (q, false)} := by
  ext w
  exact ((retAut_spec δ q₀ w q).1).symm

end DFAReturn

/-- **Star-free first returns give height one.** If the first-return code to `q₀` and the
`q₀`-avoiding paths to `q` are star-free, then `{w | q₀·w = q}` has generalized star height at
most one.  No hypothesis on `δ` (letters need not act bijectively, `Q` need not be finite). -/
theorem height_one_of_starFree_returns {Q α : Type*} (δ : Q → α → Q) (q₀ q : Q)
    (hX : HasHeightAtMost (DFAReturn.firstReturn δ q₀) 0)
    (hP : HasHeightAtMost (DFAReturn.avoidTo δ q₀ q) 0) :
    HasHeightAtMost {w | DFAReturn.runQ δ q₀ w = q} 1 := by
  rw [DFAReturn.runQ_eq_kstar_mul]
  exact hX.star.concat (hP.mono (Nat.zero_le _))

end GeneralizedStarHeight
