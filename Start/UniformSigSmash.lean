/-
# The smash function on wires

The compiler of `Start/UniformSigCompile.lean` covers the projections, the empty word, the
successors and composition.  This module adds the remaining *non-recursive* shape of the Cobham
algebra, the smash `x # y = 1^{|x|·|y|}`.

Unlike the other shapes, a smash is not a layer of flat gates: the wire `c` of its value has to
decide whether `c < |x|·|y|`, and the two lengths are presented in unary on the presence wires of
the two arguments.  The identity used is

  `c < |x|·|y|  ↔  ∃ a ∈ [1, m], a ≤ |x| ∧ c / a < |y|`,

valid as soon as `|x| ≤ m`, so the circuit is a row of `m` disjunctions per output wire, the `a`-th
of them conjoining the presence wire `a - 1` of `x` with the presence wire `c / a` of `y`.  The
divisions are performed by the *description-writing* term, not by the circuit: the gate at row `i`
and column `j` of the grid is named by arithmetic on `i` and `j`, which is what
`Complexity.codeUniform_gridLayerP` asks for.

Main definitions:

* `Complexity.Tseitin.smashG` — the gate at a given row and column of the grid;
* `Complexity.Tseitin.smashC` — the circuit: a layer of input gates, the grid, and a layer copying
  the last gate of every row to the top;
* `Complexity.CircCode.smBlkT` — the Cobham term writing the gate of the grid from its row and
  its column, in unary.

Main results:

* `Complexity.Tseitin.topVals_smashC` — **the topmost `2 * m` gates carry the signal of
  `1^{|x|·|y|}`**;
* `Complexity.codeUniform_smashC` — **the family is P-uniform**;
* `Complexity.sigUniformB_smash` — **the smash is realized**, at every arity of at least two and
  at every width admitting its first argument.
-/

import Start.UniformSigBound
import Start.UniformSigApp

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace Tseitin

/-! ### The circuit -/

/-- The output wire `i` of a smash stage belongs to the presence block when `i < m` and to the
value block otherwise; in both cases it has to decide `ccOf m i < |x|·|y|`. -/
def ccOf (M i : ℕ) : ℕ := if i < M then i else i - M

/-- The gate at row `i`, column `j` of the grid of a smash stage.  Column `0` starts the chain of
disjunctions; an odd column `2a-1` conjoins the presence wire `a-1` of the first argument with the
presence wire `(ccOf m i)/a` of the second; an even column `2a` disjoins the two gates below it. -/
def smashG (M i j : ℕ) : Gate :=
  if j = 0 then .cst false
  else if j % 2 = 1 then
    .conj ((j - 1) / 2) (2 * M + ccOf M i / ((j + 1) / 2))
  else
    .disj (4 * M + (2 * M + 1) * i + (j - 2)) (4 * M + (2 * M + 1) * i + (j - 1))

/-- The layer of input gates a smash stage reads its two argument signals through. -/
def smashBase (M : ℕ) : Circuit := inpLayer (fun c => c) (4 * M)

/-- The grid of a smash stage: `2 * m` rows of `2 * m + 1` columns. -/
def smashGrid (M : ℕ) : Circuit :=
  CircCode.layer (fun c => smashG M (c / (2 * M + 1)) (c % (2 * M + 1))) (2 * M * (2 * M + 1))

/-- **The circuit of a smash stage**: the input layer, the grid, and a layer copying the last gate
of every row to the top. -/
def smashC (M : ℕ) : Circuit :=
  wireLayer (fun c => 4 * M + (2 * M + 1) * c + 2 * M) (2 * M) ++ (smashGrid M ++ smashBase M)

/-! ### What the gates carry -/

/-- The value of the chain of disjunctions of the row `i` after `a` steps. -/
def sigOr (X : Word) (M i : ℕ) : ℕ → Bool
  | 0 => false
  | a + 1 => sigOr X M i a || (X.getD a false && X.getD (2 * M + ccOf M i / (a + 1)) false)

/-- The value the gate at row `i`, column `j` of the grid ought to carry. -/
def gridSpec (X : Word) (M i j : ℕ) : Bool :=
  if j = 0 then false
  else if j % 2 = 1 then
    (X.getD ((j - 1) / 2) false && X.getD (2 * M + ccOf M i / ((j + 1) / 2)) false)
  else sigOr X M i (j / 2)

theorem length_smashBase (M : ℕ) : (smashBase M).length = 4 * M := by
  simp [smashBase]

theorem getD_vals_smashBase (X : Word) (M : ℕ) {z : ℕ} (h : z < 4 * M) :
    (vals X (smashBase M)).getD z false = X.getD z false := by
  rw [smashBase, vals_inpLayer]
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

/-- **The values of the grid.** -/
theorem getD_vals_smashGrid (X : Word) (M : ℕ) :
    ∀ k : ℕ, k ≤ 2 * M * (2 * M + 1) → ∀ z : ℕ, z < 4 * M + k →
      (vals X (CircCode.layer
          (fun c => smashG M (c / (2 * M + 1)) (c % (2 * M + 1))) k ++ smashBase M)).getD z false
        = (if z < 4 * M then X.getD z false
            else gridSpec X M ((z - 4 * M) / (2 * M + 1)) ((z - 4 * M) % (2 * M + 1))) := by
  intro k
  induction k with
  | zero =>
      intro _ z hz
      have hz' : z < 4 * M := by omega
      rw [if_pos hz']
      have hnil : CircCode.layer (fun c => smashG M (c / (2 * M + 1)) (c % (2 * M + 1))) 0 = [] :=
        rfl
      rw [hnil, List.nil_append]
      exact getD_vals_smashBase X M hz'
  | succ k ih =>
      intro hk z hz
      set W : ℕ := 2 * M + 1 with hW
      set tmplF : ℕ → Gate := fun c => smashG M (c / W) (c % W) with htmplF
      set C : Circuit := CircCode.layer tmplF k ++ smashBase M with hC
      have hClen : C.length = k + 4 * M := by simp [hC, length_smashBase]
      have heq : CircCode.layer tmplF (k + 1) ++ smashBase M = tmplF k :: C := rfl
      rcases Nat.lt_or_ge z (4 * M + k) with hz1 | hz2
      · rw [heq, vals_cons_getD_lt X _ _ (by omega)]
        exact ih (by omega) z hz1
      · have hzeq : z = C.length := by omega
        rw [heq, hzeq, vals_cons_getD_length, if_neg (by omega), show C.length - 4 * M = k by omega]
        have hIH := ih (by omega)
        have hWpos : 0 < W := by omega
        have hjW : k % W < W := Nat.mod_lt _ hWpos
        have hkij : W * (k / W) + k % W = k := Nat.div_add_mod k W
        have hi2M : k / W < 2 * M := by
          by_contra hcon
          push Not at hcon
          have : 2 * M * W ≤ W * (k / W) := by
            rw [Nat.mul_comm (2 * M) W]
            exact Nat.mul_le_mul_left W hcon
          omega
        have hM1 : 1 ≤ M := Nat.pos_of_ne_zero (fun h => by simp [h] at hi2M)
        set i : ℕ := k / W with hi
        set j : ℕ := k % W with hj
        change gateVal X (vals X C) (smashG M i j) = gridSpec X M i j
        have hcc : ccOf M i < M := by
          rw [ccOf]; split_ifs with h <;> omega
        rw [smashG]
        split_ifs with h0 hodd
        · simp [gateVal, gridSpec, h0]
        · -- an odd column conjoins two presence wires
          have hdivle : ccOf M i / ((j + 1) / 2) ≤ ccOf M i := Nat.div_le_self _ _
          have hr : (j - 1) / 2 < 4 * M := by omega
          have hs : 2 * M + ccOf M i / ((j + 1) / 2) < 4 * M := by omega
          rw [gateVal, hIH _ (by omega), hIH _ (by omega), if_pos hr, if_pos hs,
            gridSpec, if_neg h0, if_pos hodd]
        · -- an even column continues the chain of disjunctions
          have hj2 : 2 ≤ j := by omega
          have hr1 : 4 * M + W * i + (j - 2) = 4 * M + (k - 2) := by omega
          have hr2 : 4 * M + W * i + (j - 1) = 4 * M + (k - 1) := by omega
          have hd1 : (4 * M + (k - 2) - 4 * M) / W = i ∧ (4 * M + (k - 2) - 4 * M) % W = j - 2 := by
            have hval : 4 * M + (k - 2) - 4 * M = W * i + (j - 2) := by omega
            rw [hval]
            exact ⟨by rw [Nat.mul_add_div hWpos, Nat.div_eq_of_lt (by omega), Nat.add_zero],
              by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]⟩
          have hd2 : (4 * M + (k - 1) - 4 * M) / W = i ∧ (4 * M + (k - 1) - 4 * M) % W = j - 1 := by
            have hval : 4 * M + (k - 1) - 4 * M = W * i + (j - 1) := by omega
            rw [hval]
            exact ⟨by rw [Nat.mul_add_div hWpos, Nat.div_eq_of_lt (by omega), Nat.add_zero],
              by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]⟩
          rw [gateVal, hr1, hr2, hIH _ (by omega), hIH _ (by omega), if_neg (by omega),
            if_neg (by omega), hd1.1, hd1.2, hd2.1, hd2.2]
          set a : ℕ := j / 2 with ha
          have hja : j = 2 * a := by omega
          have ha1 : 1 ≤ a := by omega
          have hg1 : gridSpec X M i (j - 2) = sigOr X M i (a - 1) := by
            rw [gridSpec]
            split_ifs with e1 e2
            · have hone : a = 1 := by omega
              rw [hone]
              rfl
            · omega
            · congr 1
              omega
          have hg2 : gridSpec X M i (j - 1)
              = (X.getD (a - 1) false && X.getD (2 * M + ccOf M i / a) false) := by
            rw [gridSpec, if_neg (by omega), if_pos (by omega),
              show (j - 1 - 1) / 2 = a - 1 by omega, show (j - 1 + 1) / 2 = a by omega]
          have hg3 : gridSpec X M i j = sigOr X M i a := by
            rw [gridSpec, if_neg h0, if_neg hodd]
          have hrec : sigOr X M i a
              = (sigOr X M i (a - 1) || (X.getD (a - 1) false
                  && X.getD (2 * M + ccOf M i / a) false)) := by
            conv_lhs => rw [show a = (a - 1) + 1 by omega]
            rw [sigOr, show a - 1 + 1 = a by omega]
          rw [hg1, hg2, hg3, hrec]

/-- A row that is already true stays true. -/
theorem sigOr_mono (X : Word) (M i : ℕ) {a a' : ℕ} (h : a ≤ a') (hv : sigOr X M i a = true) :
    sigOr X M i a' = true := by
  induction a' with
  | zero =>
      have hz : a = 0 := by omega
      rwa [← hz]
  | succ b ih =>
      rcases Nat.lt_or_ge a (b + 1) with hlt | hge
      · rw [sigOr, ih (by omega), Bool.true_or]
      · have hb : a = b + 1 := by omega
        rwa [← hb]

/-- A true disjunct of a row witnesses the inequality. -/
theorem sigOr_true_bound (X : Word) (M i lx ly : ℕ) (hcc : ccOf M i < M)
    (hp : ∀ a, a < M → X.getD a false = decide (a < lx))
    (hq : ∀ t, t < M → X.getD (2 * M + t) false = decide (t < ly)) :
    ∀ a, a ≤ M → sigOr X M i a = true → ccOf M i < lx * ly := by
  intro a
  induction a with
  | zero => intro _ h; simp [sigOr] at h
  | succ b ih =>
      intro hb h
      rw [sigOr, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ih (by omega) h
      · have hdle : ccOf M i / (b + 1) ≤ ccOf M i := Nat.div_le_self _ _
        rw [Bool.and_eq_true, hp b (by omega), hq (ccOf M i / (b + 1)) (by omega),
          decide_eq_true_eq, decide_eq_true_eq] at h
        obtain ⟨h1, h2⟩ := h
        have hdiv : ccOf M i < ly * (b + 1) :=
          (Nat.div_lt_iff_lt_mul (Nat.succ_pos b)).1 h2
        calc ccOf M i < ly * (b + 1) := hdiv
          _ ≤ ly * lx := Nat.mul_le_mul_left ly (by omega)
          _ = lx * ly := Nat.mul_comm _ _

/-- **The chain of a row ends on the verdict.** -/
theorem sigOr_eq_decide (X : Word) (M i lx ly : ℕ) (hx : lx ≤ M) (hcc : ccOf M i < M)
    (hp : ∀ a, a < M → X.getD a false = decide (a < lx))
    (hq : ∀ t, t < M → X.getD (2 * M + t) false = decide (t < ly)) :
    sigOr X M i M = decide (ccOf M i < lx * ly) := by
  by_cases hz : sigOr X M i M = true
  · rw [hz, eq_comm, decide_eq_true_eq]
    exact sigOr_true_bound X M i lx ly hcc hp hq M le_rfl hz
  · rw [Bool.not_eq_true] at hz
    rw [hz, eq_comm, decide_eq_false_iff_not]
    intro hcon
    have hlx : 0 < lx := by
      rcases Nat.eq_zero_or_pos lx with rfl | h
      · simp at hcon
      · exact h
    have hstep : sigOr X M i lx = true := by
      have hlx' : lx - 1 + 1 = lx := by omega
      have hdle : ccOf M i / lx ≤ ccOf M i := Nat.div_le_self _ _
      rw [← hlx', sigOr, Bool.or_eq_true]
      right
      rw [Bool.and_eq_true, hp (lx - 1) (by omega), hlx', hq (ccOf M i / lx) (by omega),
        decide_eq_true_eq, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      exact Nat.div_lt_of_lt_mul hcon
    have hall := sigOr_mono X M i hx hstep
    rw [hz] at hall
    exact Bool.false_ne_true hall

/-- **The topmost `2 * m` gates of a smash stage carry the signal of `1^{lx·ly}`**, whenever the
input word presents on its first `4 * M` wires the signals of two words of lengths `lx` and `ly`.
Only the first length has to fit in the width: the wires of the second argument are read at fewer
than `M` places, so no bound on `ly` is needed. -/
theorem topVals_smashC_of (M : ℕ) (X : Word) (lx ly : ℕ) (hx : lx ≤ M)
    (hp : ∀ a, a < M → X.getD a false = decide (a < lx))
    (hq : ∀ t, t < M → X.getD (2 * M + t) false = decide (t < ly)) :
    topVals (2 * M) (vals X (smashC M)) = encSig M (List.replicate (lx * ly) true) := by
  set W : ℕ := 2 * M + 1 with hW
  set G : Circuit := smashGrid M ++ smashBase M with hG
  have hlenG : G.length = 2 * M * W + 4 * M := by
    simp [hG, smashGrid, length_smashBase, hW]
  have hidx : ∀ c, c < 2 * M → 4 * M + W * c + 2 * M < G.length := by
    intro c hc
    rw [hlenG]
    have hstep : W * c + W ≤ W * (2 * M) :=
      calc W * c + W = W * (c + 1) := by ring
        _ ≤ W * (2 * M) := Nat.mul_le_mul_left _ (by omega)
    have h2 : W * (2 * M) = 2 * M * W := by ring
    omega
  rw [smashC, vals_wireLayer_append X (2 * M) hidx]
  have hlen2 : ((List.range (2 * M)).map
      (fun c => (vals X G).getD (4 * M + W * c + 2 * M) false)).length = 2 * M := by simp
  have htop := topVals_append_right (vals X G)
    ((List.range (2 * M)).map (fun c => (vals X G).getD (4 * M + W * c + 2 * M) false))
  rw [hlen2] at htop
  rw [htop]
  have hrow : ∀ c, c < 2 * M →
      (vals X G).getD (4 * M + W * c + 2 * M) false
        = decide (ccOf M c < lx * ly) := by
    intro c hc
    have hM1 : 1 ≤ M := by omega
    have hz : 4 * M + W * c + 2 * M < 4 * M + 2 * M * W := by
      have hstep : W * c + W ≤ W * (2 * M) :=
        calc W * c + W = W * (c + 1) := by ring
          _ ≤ W * (2 * M) := Nat.mul_le_mul_left _ (by omega)
      have h2 : W * (2 * M) = 2 * M * W := by ring
      omega
    have hgrid := getD_vals_smashGrid X M (2 * M * W) le_rfl (4 * M + W * c + 2 * M) hz
    have hdiv : (4 * M + W * c + 2 * M - 4 * M) / W = c := by
      have hval : 4 * M + W * c + 2 * M - 4 * M = W * c + 2 * M := by omega
      rw [hval, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
    have hmod : (4 * M + W * c + 2 * M - 4 * M) % W = 2 * M := by
      have hval : 4 * M + W * c + 2 * M - 4 * M = W * c + 2 * M := by omega
      rw [hval, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hcc : ccOf M c < M := by
      rw [ccOf]; split_ifs with h <;> omega
    rw [hG, smashGrid]
    rw [hgrid, if_neg (by omega), hdiv, hmod, gridSpec, if_neg (by omega), if_neg (by omega),
      show 2 * M / 2 = M by omega]
    exact sigOr_eq_decide X M c lx ly hx hcc hp hq
  have hmapeq : (List.range (2 * M)).map (fun c => (vals X G).getD (4 * M + W * c + 2 * M) false)
      = (List.range (2 * M)).map (fun c => decide (ccOf M c < lx * ly)) :=
    List.map_congr_left (fun c hc => hrow c (List.mem_range.1 hc))
  rw [hmapeq, encSig]
  refine List.ext_getElem (by simp; omega) ?_
  intro j h1 h2
  have hj : j < 2 * M := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  rcases Nat.lt_or_ge j M with hlt | hge
  · rw [List.getElem_append_left (by simpa using hlt)]
    simp only [List.getElem_map, List.getElem_range, List.length_replicate]
    rw [ccOf, if_pos hlt]
  · rw [List.getElem_append_right (by simpa using hge)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    rw [ccOf, if_neg (by omega)]
    exact (getD_replicate_true _ _).symm

/-- **The topmost `2 * m` gates of a smash stage carry the signal of the value**, on the word
presenting the arguments. -/
theorem topVals_smashC (M : ℕ) (args : List Word) (h1 : 1 < args.length)
    (hx : (args.getD 0 []).length ≤ M) :
    topVals (2 * M) (vals (encArgs M args) (smashC M))
      = encSig M (List.replicate
          ((args.getD 0 []).length * (args.getD 1 []).length) true) := by
  refine topVals_smashC_of M _ _ _ hx ?_ ?_
  · intro a ha
    have h := getD_encArgs M args (i := 0) (j := a) (by omega) (by omega)
    simp only [Nat.zero_mul, Nat.zero_add] at h
    rw [h, getD_encSig_lt _ ha]
  · intro t ht
    have h := getD_encArgs M args (i := 1) (j := t) h1 (by omega)
    simp only [Nat.one_mul] at h
    rw [h, getD_encSig_lt _ ht]

/-- A layer over a base is well formed as soon as its gates refer below themselves. -/
theorem wf_layer_append {tmpl : ℕ → Gate} {B : Circuit} (hB : wf B) :
    ∀ k : ℕ, (∀ c, c < k → gateWf (B.length + c) (tmpl c)) →
      wf (CircCode.layer tmpl k ++ B) := by
  intro k
  induction k with
  | zero => intro _; simpa [CircCode.layer] using hB
  | succ k ih =>
      intro h
      have hlen : (CircCode.layer tmpl k ++ B).length = B.length + k := by
        simp [Nat.add_comm]
      have heq : CircCode.layer tmpl (k + 1) ++ B = tmpl k :: (CircCode.layer tmpl k ++ B) := rfl
      rw [heq]
      exact ⟨by rw [hlen]; exact h k (Nat.lt_succ_self k),
        ih (fun c hc => h c (Nat.lt_succ_of_lt hc))⟩

theorem wf_smashBase (M : ℕ) : wf (smashBase M) := by
  have h := wf_inpLayer_append (C := ([] : Circuit)) (idx := fun c => c) trivial (4 * M)
  simpa [smashBase] using h

theorem inpsLt_smashBase (M : ℕ) : inpsLt (2 * (2 * M)) (smashBase M) := by
  have h := inpsLt_inpLayer_append (C := ([] : Circuit)) (idx := fun c => c) (w := 2 * (2 * M))
    (fun g hg => absurd hg (by simp)) (4 * M) (fun c hc => by omega)
  simpa [smashBase] using h

theorem wf_smashC (M : ℕ) : wf (smashC M) := by
  have hgrid : wf (smashGrid M ++ smashBase M) := by
    refine wf_layer_append (wf_smashBase M) _ ?_
    intro c hc
    have hW : 0 < 2 * M + 1 := by omega
    have hi : c / (2 * M + 1) < 2 * M := by
      by_contra hcon
      push Not at hcon
      have hle : 2 * M * (2 * M + 1) ≤ (2 * M + 1) * (c / (2 * M + 1)) := by
        rw [Nat.mul_comm (2 * M) (2 * M + 1)]
        exact Nat.mul_le_mul_left _ hcon
      have hdm := Nat.div_add_mod c (2 * M + 1)
      omega
    have hM1 : 1 ≤ M := Nat.pos_of_ne_zero (fun h => by simp [h] at hi)
    have hj : c % (2 * M + 1) < 2 * M + 1 := Nat.mod_lt _ hW
    have hdm := Nat.div_add_mod c (2 * M + 1)
    have hcc : ccOf M (c / (2 * M + 1)) < M := by
      rw [ccOf]; split_ifs with h <;> omega
    rw [length_smashBase, smashG]
    split_ifs with h0 hodd
    · exact trivial
    · refine ⟨?_, ?_⟩
      · have := Nat.div_le_self (c % (2 * M + 1) - 1) 2
        omega
      · have := Nat.div_le_self (ccOf M (c / (2 * M + 1))) ((c % (2 * M + 1) + 1) / 2)
        omega
    · exact ⟨by omega, by omega⟩
  refine wf_wireLayer_append hgrid _ ?_
  intro c hc
  have hlen : (smashGrid M ++ smashBase M).length = 2 * M * (2 * M + 1) + 4 * M := by
    simp [smashGrid, length_smashBase]
  rw [hlen]
  have hstep : (2 * M + 1) * c + (2 * M + 1) ≤ (2 * M + 1) * (2 * M) :=
    calc (2 * M + 1) * c + (2 * M + 1) = (2 * M + 1) * (c + 1) := by ring
      _ ≤ (2 * M + 1) * (2 * M) := Nat.mul_le_mul_left _ (by omega)
  have h2 : (2 * M + 1) * (2 * M) = 2 * M * (2 * M + 1) := by ring
  omega

theorem inpsLt_smashC (M : ℕ) : inpsLt (2 * (2 * M)) (smashC M) := by
  have hgrid : inpsLt (2 * (2 * M)) (smashGrid M ++ smashBase M) := by
    intro g hg
    rcases List.mem_append.1 hg with hg' | hg'
    · have hflat : ∀ c, inpLt (2 * (2 * M)) (smashG M (c / (2 * M + 1)) (c % (2 * M + 1))) := by
        intro c
        rw [smashG]
        split_ifs <;> exact trivial
      exact inpsLt_layer_of_flat _ (fun c _ => hflat c) g hg'
    · exact inpsLt_smashBase M g hg'
  exact inpsLt_wireLayer_append hgrid _

theorem length_smashC (M : ℕ) :
    (smashC M).length = 2 * M + (2 * M * (2 * M + 1) + 4 * M) := by
  simp [smashC, smashGrid, length_smashBase]

end Tseitin

open Complexity.Tseitin

/-! ### The description of a smash stage -/

namespace CircCode

/-! #### The terms of the layout -/

/-- The width of a signal, in unary, read off the parameter word (argument `3`). -/
def smMT (mT : Cob) : Cob := .comp mT [.comp Cob.leadOnes [.proj 3]]

/-- Twice the width, in unary. -/
def smTwoT (mT : Cob) : Cob := Cob.catL [smMT mT, smMT mT]

/-- The number of columns of the grid, in unary. -/
def smWT (mT : Cob) : Cob :=
  Cob.catL [smMT mT, smMT mT, Cob.constT (List.replicate 1 true)]

/-- The index of the presence wire of the first argument that an odd column reads. -/
def smHalfT : Cob := Cob.divT (Cob.tailN 1 (.proj 2)) (Cob.constT (List.replicate 2 true))

/-- The output wire the row is about, in unary. -/
def smCcT (mT : Cob) : Cob :=
  Cob.iteT (.comp Cob.dropU [.proj 1, smMT mT]) (.proj 1)
    (.comp Cob.dropU [smMT mT, .proj 1])

/-- The identifier of the presence wire of the second argument that an odd column reads. -/
def smConjBT (mT : Cob) : Cob :=
  Cob.catL [smMT mT, smMT mT,
    Cob.divT (smCcT mT) (Cob.catL [smHalfT, Cob.constT (List.replicate 1 true)])]

/-- The identifier of the first gate of the row of the grid. -/
def smRowT (mT : Cob) : Cob :=
  Cob.catL [smMT mT, smMT mT, smMT mT, smMT mT, .comp .smash [smWT mT, .proj 1]]

/-- **The Cobham term writing the gate of the grid of a smash stage**, from its row, its column
and the parameter word, the first two in unary. -/
def smBlkT (mT : Cob) : Cob :=
  Cob.iteT (.proj 2)
    (Cob.iteT (Cob.modT (.proj 2) (Cob.constT (List.replicate 2 true)))
      (tokTerm 5 smHalfT (smConjBT mT))
      (tokTerm 6 (Cob.catL [smRowT mT, Cob.tailN 2 (.proj 2)])
        (Cob.catL [smRowT mT, Cob.tailN 1 (.proj 2)])))
    (tokTerm 2 Cob.empty Cob.empty)

/-! #### What the term writes -/

section Eval

variable {m : ℕ → ℕ} {mT : Cob} {n i j : ℕ} {y : Word}

theorem eval_smMT (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (smMT mT).eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (m n) true := by
  simp only [smMT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
    List.getD_cons_zero, List.getD_cons_succ, Cob.eval_leadOnes, lead1_dmW]
  rw [hm (List.replicate n true), List.length_replicate]

theorem eval_smWT (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (smWT mT).eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (2 * m n + 1) true := by
  simp only [smWT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, eval_smMT hm, Cob.eval_constT, ← List.replicate_add]
  congr 1
  omega

theorem eval_smHalfT :
    smHalfT.eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate ((j - 1) / 2) true := by
  refine Cob.eval_divT (by norm_num) ?_ (by simp [Cob.eval_constT])
  rw [Cob.eval_tailN]
  simp

theorem eval_smCcT (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (smCcT mT).eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (Tseitin.ccOf (m n) i) true := by
  have hcond : (Cob.comp Cob.dropU [Cob.proj 1, smMT mT]).eval
      [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (m n - i) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      List.getD_cons_succ, eval_smMT hm, Cob.eval_dropU, List.length_replicate,
      List.drop_replicate]
  have hi : (Cob.proj 1).eval
      [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate i true := by simp
  have hsub : (Cob.comp Cob.dropU [smMT mT, Cob.proj 1]).eval
      [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (i - m n) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj, List.getD_cons_zero,
      List.getD_cons_succ, eval_smMT hm, Cob.eval_dropU, List.length_replicate,
      List.drop_replicate]
  rw [smCcT, eval_iteT_eval, hcond, Tseitin.ccOf]
  by_cases h : i < m n
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_pos h, hi]
  · rw [if_pos (by simp only [List.replicate_eq_nil_iff]; omega), if_neg h, hsub]

theorem eval_smConjBT (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (smConjBT mT).eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (2 * m n + Tseitin.ccOf (m n) i / ((j - 1) / 2 + 1)) true := by
  have hdiv : (Cob.divT (smCcT mT)
      (Cob.catL [smHalfT, Cob.constT (List.replicate 1 true)])).eval
        [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (Tseitin.ccOf (m n) i / ((j - 1) / 2 + 1)) true := by
    refine Cob.eval_divT (by omega) (eval_smCcT hm) ?_
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, eval_smHalfT, Cob.eval_constT, ← List.replicate_add]
  simp only [smConjBT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, eval_smMT hm, hdiv, ← List.replicate_add]
  congr 1
  omega

theorem eval_smRowT (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (smRowT mT).eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate (4 * m n + (2 * m n + 1) * i) true := by
  have hsm : (Cob.comp .smash [smWT mT, Cob.proj 1]).eval
      [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate ((2 * m n + 1) * i) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_proj,
      eval_smWT hm, List.getD_cons_zero, List.getD_cons_succ, List.length_replicate]
  simp only [smRowT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, eval_smMT hm, hsm, ← List.replicate_add]
  congr 1
  omega

/-- **The term writes exactly the gates of the grid.** -/
theorem eval_smBlkT (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    (smBlkT mT).eval [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = encGate (Tseitin.smashG (m n) i j) := by
  have hj : (Cob.proj 2).eval
      [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
      = List.replicate j true := by simp
  rw [smBlkT, eval_iteT_eval, hj, Tseitin.smashG]
  by_cases h0 : j = 0
  · rw [if_pos (by simp [h0]), if_pos h0]
    exact eval_tokTerm (Tseitin.Gate.cst false) (by simp [fld1]) (by simp [fld2])
  · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_neg h0, eval_iteT_eval]
    have hmod : (Cob.modT (Cob.proj 2) (Cob.constT (List.replicate 2 true))).eval
        [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
        = List.replicate (j % 2) true :=
      Cob.eval_modT (by norm_num) hj (by simp [Cob.eval_constT])
    rw [hmod]
    by_cases hodd : j % 2 = 1
    · rw [if_neg (by simp only [List.replicate_eq_nil_iff]; omega), if_pos hodd]
      have hhalf : (j + 1) / 2 = (j - 1) / 2 + 1 := by omega
      refine eval_tokTerm (Tseitin.Gate.conj ((j - 1) / 2)
        (2 * m n + Tseitin.ccOf (m n) i / ((j + 1) / 2))) eval_smHalfT ?_
      rw [show fld2 (Tseitin.Gate.conj ((j - 1) / 2)
        (2 * m n + Tseitin.ccOf (m n) i / ((j + 1) / 2)))
          = 2 * m n + Tseitin.ccOf (m n) i / ((j + 1) / 2) from rfl, hhalf]
      exact eval_smConjBT hm
    · rw [if_pos (by simp only [List.replicate_eq_nil_iff]; omega), if_neg hodd]
      have hcat : ∀ d : ℕ, (Cob.catL [smRowT mT, Cob.tailN d (Cob.proj 2)]).eval
          [y, List.replicate i true, List.replicate j true, dmW n (4 * m n)]
          = List.replicate (4 * m n + (2 * m n + 1) * i + (j - d)) true := by
        intro d
        simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
          List.flatten_nil, List.append_nil, eval_smRowT hm, Cob.eval_tailN, hj,
          List.drop_replicate, ← List.replicate_add]
      exact eval_tokTerm (Tseitin.Gate.disj (4 * m n + (2 * m n + 1) * i + (j - 2))
        (4 * m n + (2 * m n + 1) * i + (j - 1))) (hcat 2) (hcat 1)

end Eval

/-! #### The size of a gate -/

theorem length_encGate_smashG (M n i j l : ℕ) (hl : (2 * M + 1) * i + j ≤ l) :
    (encGate (Tseitin.smashG M i j)).length ≤ 13 * (l + (dmW n (4 * M)).length + 1) := by
  have hi : i ≤ (2 * M + 1) * i := Nat.le_mul_of_pos_left i (by omega)
  have hlen : (dmW n (4 * M)).length = n + 4 * M + 1 := by simp
  have hcc : Tseitin.ccOf M i ≤ i := by rw [Tseitin.ccOf]; split_ifs <;> omega
  have hdiv : Tseitin.ccOf M i / ((j + 1) / 2) ≤ Tseitin.ccOf M i := Nat.div_le_self _ _
  rw [length_encGate, Tseitin.smashG]
  split_ifs
  · simp only [tag, fld1, fld2]
    omega
  · simp only [tag, fld1, fld2]
    omega
  · simp only [tag, fld1, fld2]
    omega

end CircCode

/-! ### Uniformity -/

/-- The base of a smash stage is P-uniform. -/
theorem codeUniform_smashBase {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    CodeUniform (fun n => Tseitin.smashBase (m n)) := by
  have h := codeUniform_inpLayer (idx := fun _ c => c) (m := fun n => 4 * m n) (S := fun _ => 0)
    (fun _ c => by simp) (mT := Cob.catL [mT, mT, mT, mT]) (sT := Cob.empty)
    (idxT := Cob.proj 1) ?_ ?_ ?_
  · exact h
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, hm x, ← List.replicate_add]
    congr 1
    omega
  · intro x; simp
  · intro n c y; simp

/-- The grid of a smash stage is P-uniform. -/
theorem codeUniform_smashGrid {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    CodeUniform (fun n => Tseitin.smashGrid (m n)) := by
  refine codeUniform_gridLayerP (K := 13) (w := fun n => 2 * m n + 1)
    (k := fun n => 2 * m n * (2 * m n + 1)) (pw := fun n => dmW n (4 * m n))
    (tmpl := fun n i j => Tseitin.smashG (m n) i j)
    (cnt := .comp .smash [Cob.catL [mT, mT],
      Cob.catL [mT, mT, Cob.constT (List.replicate 1 true)]])
    (widT := Cob.catL [.comp mT [.comp Cob.leadOnes [.proj 0]],
      .comp mT [.comp Cob.leadOnes [.proj 0]], Cob.constT (List.replicate 1 true)])
    (gblk := CircCode.smBlkT mT)
    (padT := Cob.catL [.comp .smash [Cob.proj 0, Cob.constT (List.replicate 1 true)],
      Cob.constT [false], mT, mT, mT, mT])
    (fun n => by omega) ?_ ?_ ?_ ?_ ?_
  · intro x
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, Cob.eval_catL,
      List.flatten_cons, List.flatten_nil, List.append_nil, Cob.eval_constT, hm x,
      List.getD_cons_zero, List.getD_cons_succ, List.length_append, List.length_replicate]
    congr 1
    ring
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_comp, Cob.eval_smash, Cob.eval_proj, Cob.eval_constT,
      List.getD_cons_zero, List.getD_cons_succ, hm x, List.length_replicate]
    rw [dmW]
    simp only [Nat.mul_one, List.cons_append, ← List.replicate_add]
    congr 2
    rw [List.nil_append]
    congr 1
    omega
  · intro n
    have hlead : (Cob.comp mT [Cob.comp Cob.leadOnes [Cob.proj 0]]).eval [dmW n (4 * m n)]
        = List.replicate (m n) true := by
      simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
        List.getD_cons_zero, Cob.eval_leadOnes, lead1_dmW]
      rw [hm (List.replicate n true), List.length_replicate]
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, hlead, Cob.eval_constT, ← List.replicate_add]
    congr 1
    omega
  · intro n i j y _
    exact CircCode.eval_smBlkT hm
  · intro n i j l _ hl
    exact CircCode.length_encGate_smashG (m n) n i j l hl

namespace CircCode

/-- The width of a signal, in unary, read off the parameter word of the copying layer. -/
def smTopMT (mT : Cob) : Cob := .comp mT [.comp Cob.leadOnes [.proj 2]]

/-- The identifier of the gate that the copy gate `c` of the topmost layer of a smash stage
reads, in unary; the identifier is capped so as to stay bounded by the parameter word. -/
def smTopIdxT (mT : Cob) : Cob :=
  Cob.catL [smTopMT mT, smTopMT mT, smTopMT mT, smTopMT mT,
    .comp .smash [Cob.catL [smTopMT mT, smTopMT mT, Cob.constT (List.replicate 1 true)],
      .comp Cob.dropU
        [.comp Cob.dropU [Cob.catL [smTopMT mT, smTopMT mT], .proj 1], .proj 1]],
    smTopMT mT, smTopMT mT]

theorem eval_smTopIdxT {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) (n c r : ℕ) (y : Word) :
    (smTopIdxT mT).eval [y, List.replicate c true, dmW n r]
      = List.replicate (4 * m n + (2 * m n + 1) * min c (2 * m n) + 2 * m n) true := by
  have hMT : (smTopMT mT).eval [y, List.replicate c true, dmW n r]
      = List.replicate (m n) true := by
    simp only [smTopMT, Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, Cob.eval_leadOnes, lead1_dmW]
    rw [hm (List.replicate n true), List.length_replicate]
  have htwo : (Cob.catL [smTopMT mT, smTopMT mT]).eval [y, List.replicate c true, dmW n r]
      = List.replicate (2 * m n) true := by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, hMT, ← List.replicate_add]
    congr 1
    omega
  have hwid : (Cob.catL [smTopMT mT, smTopMT mT, Cob.constT (List.replicate 1 true)]).eval
      [y, List.replicate c true, dmW n r] = List.replicate (2 * m n + 1) true := by
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, hMT, Cob.eval_constT, ← List.replicate_add]
    congr 1
    omega
  have hmin : (Cob.comp Cob.dropU
      [.comp Cob.dropU [Cob.catL [smTopMT mT, smTopMT mT], Cob.proj 1], Cob.proj 1]).eval
        [y, List.replicate c true, dmW n r] = List.replicate (min c (2 * m n)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_proj,
      List.getD_cons_zero, List.getD_cons_succ, htwo, Cob.eval_dropU,
      List.length_replicate, List.drop_replicate]
    congr 1
    omega
  have hsm : (Cob.comp .smash
      [Cob.catL [smTopMT mT, smTopMT mT, Cob.constT (List.replicate 1 true)],
        .comp Cob.dropU
          [.comp Cob.dropU [Cob.catL [smTopMT mT, smTopMT mT], Cob.proj 1], Cob.proj 1]]).eval
        [y, List.replicate c true, dmW n r]
      = List.replicate ((2 * m n + 1) * min c (2 * m n)) true := by
    simp only [Cob.eval_comp, List.map_cons, List.map_nil, Cob.eval_smash, hwid, hmin,
      List.getD_cons_zero, List.getD_cons_succ, List.length_replicate]
  simp only [smTopIdxT, Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil, hMT, hsm, ← List.replicate_add]
  congr 1
  omega

end CircCode

/-- The layer copying the last gate of every row of the grid is P-uniform. -/
theorem codeUniform_smashTop {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    CodeUniform (fun n =>
      Tseitin.wireLayer (fun c => 4 * m n + (2 * m n + 1) * c + 2 * m n) (2 * m n)) := by
  have hcong : (fun n => Tseitin.wireLayer
      (fun c => 4 * m n + (2 * m n + 1) * c + 2 * m n) (2 * m n))
      = fun n => Tseitin.wireLayer
        (fun c => 4 * m n + (2 * m n + 1) * min c (2 * m n) + 2 * m n) (2 * m n) := by
    funext n
    rw [Tseitin.wireLayer, Tseitin.wireLayer]
    refine CircCode.layer_congr (fun c hc => ?_)
    rw [show min c (2 * m n) = c by omega]
  rw [hcong]
  refine codeUniform_wireLayer
    (idx := fun n c => 4 * m n + (2 * m n + 1) * min c (2 * m n) + 2 * m n)
    (S := fun n => 4 * m n + (2 * m n + 1) * (2 * m n) + 2 * m n)
    (fun n c => ?_)
    (mT := Cob.catL [mT, mT])
    (sT := Cob.catL [mT, mT, mT, mT,
      .comp .smash [Cob.catL [mT, mT, Cob.constT (List.replicate 1 true)], Cob.catL [mT, mT]],
      mT, mT])
    (idxT := CircCode.smTopIdxT mT) ?_ ?_ ?_
  · have h : (2 * m n + 1) * min c (2 * m n) ≤ (2 * m n + 1) * (2 * m n) :=
      Nat.mul_le_mul_left _ (min_le_right _ _)
    change 4 * m n + (2 * m n + 1) * min c (2 * m n) + 2 * m n
      ≤ 4 * m n + (2 * m n + 1) * (2 * m n) + 2 * m n + c
    omega
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, hm x, ← List.replicate_add]
    congr 1
    omega
  · intro x
    simp only [Cob.eval_catL, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, Cob.eval_comp, Cob.eval_smash, Cob.eval_constT, hm x,
      List.getD_cons_zero, List.getD_cons_succ, List.length_replicate,
      ← List.replicate_add]
    congr 1
    ring
  · intro n c y
    exact CircCode.eval_smTopIdxT hm n c _ y

/-- **The family of smash stages is P-uniform.** -/
theorem codeUniform_smashC {m : ℕ → ℕ} {mT : Cob}
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    CodeUniform (fun n => Tseitin.smashC (m n)) :=
  codeUniform_append (codeUniform_smashTop hm)
    (codeUniform_append (codeUniform_smashGrid hm) (codeUniform_smashBase hm))

/-- Reading fewer circuit inputs is reading fewer circuit inputs. -/
theorem Tseitin.inpsLt_mono {w w' : ℕ} {C : Tseitin.Circuit} (h : Tseitin.inpsLt w C)
    (hw : w ≤ w') : Tseitin.inpsLt w' C := by
  intro g hg
  have hg' := h g hg
  cases g with
  | inp i =>
      simp only [Tseitin.inpLt] at hg' ⊢
      omega
  | _ => exact trivial

/-- **The smash is realized**: at every arity of at least two, and at every width admitting its
first argument. -/
theorem sigUniformB_smash {r : ℕ} {m k : ℕ → ℕ} {mT : Cob} (hr : 2 ≤ r) (hk : ∀ n, k n ≤ m n)
    (hm : ∀ x : Word, mT.eval [x] = List.replicate (m x.length) true) :
    SigUniformB r m k (fun args =>
      List.replicate ((args.getD 0 []).length * (args.getD 1 []).length) true) := by
  refine ⟨fun n => Tseitin.smashC (m n), fun n => Tseitin.wf_smashC (m n), fun n => ?_,
    fun n => ?_, codeUniform_smashC hm, ?_⟩
  · exact Tseitin.inpsLt_mono (Tseitin.inpsLt_smashC (m n)) (Nat.mul_le_mul_right _ hr)
  · rw [Tseitin.length_smashC]
    omega
  · intro n args hlen hle
    have h1 : 1 < args.length := by omega
    have hmem : args.getD 0 [] ∈ args := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem (by omega)
    exact Tseitin.topVals_smashC (m n) args h1 (le_trans (hle _ hmem) (hk n))

end Complexity
