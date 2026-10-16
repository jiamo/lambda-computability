import Start.StarHeightCoreIdentity

/-!
# The automata for the stars of the twelve classes

`fStep i` reads a word block by block and remembers the walk state and `comp` of the current block;
it rejects once a completed block lies outside the class `F_{i+1}`.  `fData i` is the strictly
locally testable description of `F_{i+1}∗` (prefixes, suffixes, forbidden factors).  `f_check`
compares the two automata on the reachable part of their product; `f_agree` is the consequence.

The product search is run on natural-number codes of the states (`encP`, `decP`): the explored
list holds numerals, membership is tested with `Nat.beq`, and the check `codeCheck` verifies (with
the Boolean equality `eqP`) that decoding inverts encoding on every state it meets, so no property
of the codes is needed.  This keeps the kernel evaluation small (one `decide +kernel` per class).
-/

namespace GeneralizedStarHeight

/-- The automaton reading the blocks of a word in `Fᵢ∗`: the walk state and `comp` of the current
block; `none` once a completed block lies outside the class. -/
def fStep (i : Fin 12) : Option (ZMod 3 × W3) → Fin 3 → Option (ZMod 3 × W3)
  | none, _ => none
  | some (s, c), a =>
    if s + step3 a = 0 then (if cls (comp (c ++ [a])) = i.succ then some (0, []) else none)
    else some (s + step3 a, comp (c ++ [a]))

/-- Acceptance: no incomplete block. -/
def fAcc : Option (ZMod 3 × W3) → Bool
  | none => false
  | some (s, _) => decide (s = 0)

/-- The strictly locally testable data: prefixes, suffixes and forbidden factors of `Fᵢ∗`. -/
def fData : Fin 12 → List W3 × List W3 × List W3 := ![
  ([[0]], [[2]], [[0, 0], [1], [2, 2]]),
  ([[0, 0, 2], [0, 1, 2]], [[0, 2, 2], [1, 2, 2]],
    [[0, 0, 0], [0, 0, 1], [0, 2, 0, 0], [0, 2, 0, 1], [1, 0], [1, 1], [1, 2, 0, 0], [1, 2, 0, 1],
      [2, 2, 0, 2], [2, 2, 1], [2, 2, 2]]),
  ([[0, 0, 1], [0, 0, 2], [0, 1, 2]], [[0, 0, 1], [2, 0, 1]],
    [[0, 0, 0], [0, 0, 1, 2], [1, 0, 1, 0], [1, 0, 2], [1, 1], [2, 0, 0], [2, 0, 1, 2], [2, 1, 0],
      [2, 2]]),
  ([[0, 0, 2], [0, 1, 0], [0, 1, 2]], [[0, 1, 0], [2, 1, 0]],
    [[0, 0, 0, 0], [0, 0, 0, 1], [1, 0, 0, 2], [1, 0, 1], [1, 0, 2], [1, 1], [2, 0, 0], [2, 0, 1],
      [2, 2]]),
  ([[0, 0], [0, 1]], [[1, 1]],
    [[0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 2], [1, 1, 1], [1, 1, 2], [2, 0, 0], [2, 0, 1],
      [2, 1, 0], [2, 2]]),
  ([[1, 0], [1, 1]], [[0, 0]],
    [[0, 0, 0], [0, 0, 2], [0, 1, 2], [1, 0, 1], [1, 1, 0], [1, 1, 1], [2, 0, 1], [2, 1, 0],
      [2, 1, 1], [2, 2]]),
  ([[1, 0, 1], [1, 0, 2], [1, 1, 2]], [[1, 0, 1], [2, 0, 1]],
    [[0, 0], [0, 1, 0], [0, 1, 1, 2], [0, 1, 2], [1, 1, 1, 0], [1, 1, 1, 1], [2, 1, 0], [2, 1, 1],
      [2, 2]]),
  ([[1, 0, 2], [1, 1, 0], [1, 1, 2]], [[1, 1, 0], [2, 1, 0]],
    [[0, 0], [0, 1, 0, 1], [0, 1, 2], [1, 1, 0, 2], [1, 1, 1], [2, 0, 1], [2, 1, 0, 2], [2, 1, 1],
      [2, 2]]),
  ([[2]], [[0]], [[0, 0], [1], [2, 2]]),
  ([[2, 2, 0], [2, 2, 1]], [[2, 1, 0]],
    [[0, 0], [0, 1], [1, 0, 2, 0], [1, 0, 2, 1], [1, 1], [1, 2, 2], [2, 0, 2, 2], [2, 2, 2]]),
  ([[2, 2, 0], [2, 2, 1]], [[2, 0, 0]],
    [[0, 0, 0], [0, 0, 2, 0], [0, 0, 2, 1], [0, 1], [1, 0], [1, 1], [1, 2, 2], [2, 0, 2, 2],
      [2, 2, 2]]),
  ([[2, 2, 0], [2, 2, 1]], [[2, 0, 1]],
    [[0, 0], [0, 1, 2, 0], [0, 1, 2, 1], [0, 2, 2], [1, 0], [1, 1], [2, 1, 2, 2], [2, 2, 2]])]

/-! ### Product search on numeric codes -/

/-- Membership in a list of numerals, by `Nat.beq` (written with the recursor, which the kernel
evaluates faster than the structural-recursion compilation). -/
def memN (x : ℕ) (l : List ℕ) : Bool := l.rec false fun y _ r => Nat.beq x y || r

lemma memN_spec {x : ℕ} : ∀ {l : List ℕ}, memN x l = true → x ∈ l
  | [], h => by simp [memN] at h
  | y :: l, h => by
    change (Nat.beq x y || memN x l) = true at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.beq_eq] at h; subst h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memN_spec h)

/-- One round of the breadth-first search: the successors of `todo` outside `seen`. -/
def stepN (δ : ℕ → Fin 3 → ℕ) (seen todo : List ℕ) : List ℕ :=
  todo.rec (fun acc => acc) (fun q _ r acc => r (
    let x0 := δ q 0; let acc := if memN x0 seen || memN x0 acc then acc else x0 :: acc
    let x1 := δ q 1; let acc := if memN x1 seen || memN x1 acc then acc else x1 :: acc
    let x2 := δ q 2; if memN x2 seen || memN x2 acc then acc else x2 :: acc)) []

/-- Breadth-first exploration of the codes reachable from `todo`, with fuel. -/
def exploreN (δ : ℕ → Fin 3 → ℕ) (fuel : ℕ) : List ℕ → List ℕ → List ℕ :=
  fuel.rec (fun _ seen => seen) fun _ r todo seen =>
    (stepN δ seen todo).rec seen fun _ _ _ => r (stepN δ seen todo) (stepN δ seen todo ++ seen)

/-- `P` holds on every element of the list (written with the recursor). -/
def allN (P : ℕ → Bool) (l : List ℕ) : Bool := l.rec true fun n _ r => P n && r

lemma allN_spec {P : ℕ → Bool} : ∀ {l : List ℕ}, allN P l = true → ∀ n ∈ l, P n = true
  | [], _ => by simp
  | y :: l, h => by
    change (P y && allN P l) = true at h
    simp only [Bool.and_eq_true] at h
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact h.1
    · exact allN_spec h.2 n hn

/-- `R` contains `n₀`, is closed under `δ`, and satisfies `P`. -/
def checkN (δ : ℕ → Fin 3 → ℕ) (n₀ : ℕ) (P : ℕ → Bool) (R : List ℕ) : Bool :=
  memN n₀ R && allN (fun n => P n && memN (δ n 0) R && memN (δ n 1) R && memN (δ n 2) R) R

lemma checkN_spec {δ : ℕ → Fin 3 → ℕ} {n₀ : ℕ} {P : ℕ → Bool} {R : List ℕ}
    (h : checkN δ n₀ P R = true) (w : List (Fin 3)) : P (w.foldl δ n₀) = true := by
  simp only [checkN, Bool.and_eq_true] at h
  obtain ⟨h0, hR⟩ := h
  have hR := allN_spec hR
  simp only [Bool.and_eq_true] at hR
  have key : ∀ (w : List (Fin 3)) (n : ℕ), n ∈ R → w.foldl δ n ∈ R := by
    intro w
    induction w with
    | nil => intro n hn; exact hn
    | cons a w ih =>
      intro n hn
      obtain ⟨⟨⟨_, h0⟩, h1⟩, h2⟩ := hR n hn
      refine ih _ (memN_spec ?_)
      fin_cases a
      exacts [h0, h1, h2]
  exact (hR _ (key w n₀ (memN_spec h0))).1.1.1

/-- The search for the automaton `δ` on the codes `enc`, decoded by `dec`: every state met is
recovered from its code (as tested by the Boolean equality `eq`), and `P` holds on it. -/
def codeCheck {Q : Type*} (eq : Q → Q → Bool) (δ : Q → Fin 3 → Q) (enc : Q → ℕ) (dec : ℕ → Q)
    (q₀ : Q) (P : Q → Bool) (fuel : ℕ) : Bool :=
  eq (dec (enc q₀)) q₀ &&
  checkN (fun n a => enc (δ (dec n) a)) (enc q₀)
    (fun n => P (dec n) && eq (dec (enc (δ (dec n) 0))) (δ (dec n) 0) &&
      eq (dec (enc (δ (dec n) 1))) (δ (dec n) 1) && eq (dec (enc (δ (dec n) 2))) (δ (dec n) 2))
    (exploreN (fun n a => enc (δ (dec n) a)) fuel [enc q₀] [enc q₀])

lemma codeCheck_spec {Q : Type*} {eq : Q → Q → Bool} (heq : ∀ x y, eq x y = true → x = y)
    {δ : Q → Fin 3 → Q} {enc : Q → ℕ} {dec : ℕ → Q} {q₀ : Q} {P : Q → Bool} {fuel : ℕ}
    (h : codeCheck eq δ enc dec q₀ P fuel = true) (w : List (Fin 3)) :
    P (w.foldl δ q₀) = true := by
  simp only [codeCheck, Bool.and_eq_true] at h
  obtain ⟨h0, h⟩ := h
  have hc := checkN_spec h
  simp only [Bool.and_eq_true] at hc
  have hstep : ∀ (w : List (Fin 3)) (a : Fin 3),
      dec (enc (δ (dec (w.foldl (fun n a => enc (δ (dec n) a)) (enc q₀))) a)) =
        δ (dec (w.foldl (fun n a => enc (δ (dec n) a)) (enc q₀))) a := by
    intro w a
    obtain ⟨⟨⟨_, h0⟩, h1⟩, h2⟩ := hc w
    fin_cases a
    exacts [heq _ _ h0, heq _ _ h1, heq _ _ h2]
  have hdec : ∀ w : List (Fin 3),
      dec (w.foldl (fun n a => enc (δ (dec n) a)) (enc q₀)) = w.foldl δ q₀ := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact heq _ _ h0
    | append_singleton w a ih =>
      rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil, List.foldl_cons,
        List.foldl_nil, hstep w a, ih]
  rw [← hdec w]
  exact (hc w).1.1.1

/-! ### Codes of the product states -/

/-- Base-4 code of a word (digits `a + 1`, least significant first). -/
def encW : W3 → ℕ
  | [] => 0
  | a :: w => a.val + 1 + 4 * encW w

/-- Decoding of `encW`, with fuel. -/
def decW : ℕ → ℕ → W3
  | 0, _ => []
  | k + 1, n =>
    if n % 4 = 0 then [] else ⟨(n % 4 - 1) % 3, Nat.mod_lt _ (by decide)⟩ :: decW k (n / 4)

/-- Code of a state of `fStep`. -/
def encF : Option (ZMod 3 × W3) → ℕ
  | none => 0
  | some (s, c) => 1 + s.val + 3 * encW c

/-- Decoding of `encF`. -/
def decF (n : ℕ) : Option (ZMod 3 × W3) :=
  if n = 0 then none else some (((n - 1) % 3 : ℕ), decW 6 ((n - 1) / 3))

/-- Code of a state of `sltStep`. -/
def encS : Option (W3 × W3) → ℕ
  | none => 0
  | some (p, s) => 1 + encW p + 1024 * encW s

/-- Decoding of `encS`. -/
def decS (n : ℕ) : Option (W3 × W3) :=
  if n = 0 then none else some (decW 6 ((n - 1) % 1024), decW 6 ((n - 1) / 1024))

/-- Code of a product state. -/
def encP (q : Option (ZMod 3 × W3) × Option (W3 × W3)) : ℕ := encF q.1 + 4096 * encS q.2

/-- Decoding of `encP`. -/
def decP (n : ℕ) : Option (ZMod 3 × W3) × Option (W3 × W3) := (decF (n % 4096), decS (n / 4096))

/-- Boolean equality of words (written with the recursor). -/
def beqW (u : W3) : W3 → Bool :=
  u.rec (fun v => v.isEmpty) fun a _ r v =>
    List.rec (motive := fun _ => Bool) false (fun b v' _ => Nat.beq a.val b.val && r v') v

lemma beqW_spec : ∀ u v : W3, beqW u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: u, b :: v, h => by
    change (Nat.beq a.val b.val && beqW u v) = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    rw [Fin.ext h.1, beqW_spec u v h.2]

/-- Boolean equality of states of `fStep`. -/
def eqF : Option (ZMod 3 × W3) → Option (ZMod 3 × W3) → Bool
  | none, none => true
  | some (x, c), some (x', c') => Nat.beq x.val x'.val && beqW c c'
  | _, _ => false

lemma eqF_spec : ∀ x y, eqF x y = true → x = y
  | none, none, _ => rfl
  | some (x, c), some (x', c'), h => by
    change (Nat.beq x.val x'.val && beqW c c') = true at h
    simp only [Bool.and_eq_true, Nat.beq_eq] at h
    rw [ZMod.val_injective _ h.1, beqW_spec _ _ h.2]
  | none, some _, h => by cases h
  | some _, none, h => by cases h

/-- Boolean equality of states of `sltStep`. -/
def eqS : Option (W3 × W3) → Option (W3 × W3) → Bool
  | none, none => true
  | some (p, t), some (p', t') => beqW p p' && beqW t t'
  | _, _ => false

lemma eqS_spec : ∀ x y, eqS x y = true → x = y
  | none, none, _ => rfl
  | some (p, t), some (p', t'), h => by
    change (beqW p p' && beqW t t') = true at h
    simp only [Bool.and_eq_true] at h
    rw [beqW_spec _ _ h.1, beqW_spec _ _ h.2]
  | none, some _, h => by cases h
  | some _, none, h => by cases h

/-- Boolean equality of product states. -/
def eqP (x y : Option (ZMod 3 × W3) × Option (W3 × W3)) : Bool := eqF x.1 y.1 && eqS x.2 y.2

lemma eqP_spec (x y : Option (ZMod 3 × W3) × Option (W3 × W3)) (h : eqP x y = true) : x = y := by
  simp only [eqP, Bool.and_eq_true] at h
  exact Prod.ext (eqF_spec _ _ h.1) (eqS_spec _ _ h.2)

/-- The check for one class: the two automata agree on the reachable part of their product. -/
def fCheck (i : Fin 12) : Bool :=
  codeCheck eqP (fun q a => (fStep i q.1 a, sltStep (fData i).2.2 q.2 a)) encP decP
    (some (0, []), some ([], [])) (fun q => fAcc q.1 == sltAcc true (fData i).1 (fData i).2.1 q.2)
    12

/- The twelve kernel checks are run one after the other: this keeps the peak memory of the module
at that of a single check. -/
set_option Elab.async false

lemma f_check_0 : fCheck 0 = true := by decide +kernel
lemma f_check_1 : fCheck 1 = true := by decide +kernel
lemma f_check_2 : fCheck 2 = true := by decide +kernel
lemma f_check_3 : fCheck 3 = true := by decide +kernel
lemma f_check_4 : fCheck 4 = true := by decide +kernel
lemma f_check_5 : fCheck 5 = true := by decide +kernel
lemma f_check_6 : fCheck 6 = true := by decide +kernel
lemma f_check_7 : fCheck 7 = true := by decide +kernel
lemma f_check_8 : fCheck 8 = true := by decide +kernel
lemma f_check_9 : fCheck 9 = true := by decide +kernel
lemma f_check_10 : fCheck 10 = true := by decide +kernel
lemma f_check_11 : fCheck 11 = true := by decide +kernel

lemma f_check : ∀ i : Fin 12, fCheck i = true := by
  intro i
  fin_cases i
  exacts [f_check_0, f_check_1, f_check_2, f_check_3, f_check_4, f_check_5, f_check_6, f_check_7,
    f_check_8, f_check_9, f_check_10, f_check_11]

/-- **The two automata accept the same words.** -/
lemma f_agree (i : Fin 12) (w : W3) :
    fAcc (w.foldl (fStep i) (some (0, []))) =
      sltAcc true (fData i).1 (fData i).2.1 (w.foldl (sltStep (fData i).2.2) (some ([], []))) := by
  have := codeCheck_spec eqP_spec (f_check i) w
  rw [foldl_prod] at this
  simpa using this

lemma fData_ok : ∀ i : Fin 12, (∀ p ∈ (fData i).1, p.length ≤ 3) ∧
    (∀ s ∈ (fData i).2.1, s.length ≤ 3) ∧ ∀ g ∈ (fData i).2.2, g ≠ [] ∧ g.length ≤ 4 := by
  decide

end GeneralizedStarHeight
