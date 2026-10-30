import Start.StarHeightTransfer
import Start.StarHeightAperiodic

/-!
# Walks on `ZMod p`: the first-return code and its star-freeness for prime `p`

Alphabet `β`; letter `a` moves the state in `ZMod p` by `σ a`.  Words are read from state `0`.

* `starFree_of_pow_stable`: if an automaton satisfies `w^(N+1) ≡ w^N` on every state for every
  word `w`, all its languages `{w | P (w.foldl δ q₀)}` are star-free (Schützenberger's theorem,
  `Aperiodic.starFree_of_aperiodic`, applied to its transition monoid).
* `zpX σ` (first returns to `0`), `zpNR σ` (no nonempty prefix in state `0`), the factorization
  `zpSplit σ u = (e₁ ⋯ e_r, t)` (`zpSplit_spec`, unique: `zpSplit_flatten`) and
  `bcount_split_eq`: counting the blocks of a class `K` modulo `m` on all words is
  `bmod (zpX σ) K m r · zpNR σ`.
* `zpX_starFree`, `zpNR_starFree`: for `p` prime both are star-free.  The walk automaton
  `zpWalk` satisfies `w^(p+2) ≡ w^(p+1)`: if `σ(w) ≠ 0`, some power `wᵏ` with `1 ≤ k ≤ p` brings
  every state back to `0` (as `σ(w)` generates `ZMod p`), and the next copy kills the run; if
  `σ(w) = 0`, `w` fixes the states it does not kill.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability

/-! ### Aperiodicity on words -/

section WordAperiodic

variable {A Q : Type u}

lemma ofList_wpow (w : List A) : ∀ n : ℕ, FreeMonoid.ofList (wpow w n) = (FreeMonoid.ofList w) ^ n
  | 0 => rfl
  | n + 1 => by rw [wpow_succ, FreeMonoid.ofList_append, ofList_wpow w n, pow_succ']

open Aperiodic in
/-- **Star-freeness from stable powers.** -/
theorem starFree_of_pow_stable [Finite A] [Finite Q] (δ : Q → A → Q) (N : ℕ)
    (h : ∀ (w : List A) (q : Q), (wpow w (N + 1)).foldl δ q = (wpow w N).foldl δ q)
    (q₀ : Q) (P : Q → Prop) : HasHeightAtMost {w : List A | P (w.foldl δ q₀)} 0 := by
  have hFE : Finite (RT Q) := inferInstanceAs (Finite (Q → Q))
  let Φ := transMor (A := A) δ
  have hMap : ∀ x : MonoidHom.mrange Φ, ∃ n : ℕ, x ^ (n + 1) = x ^ n := by
    rintro ⟨x, y, rfl⟩
    refine ⟨N, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow]
    have key : ∀ n, (Φ y) ^ n = Φ (FreeMonoid.ofList (wpow (FreeMonoid.toList y) n)) :=
      fun n => by rw [ofList_wpow, map_pow, FreeMonoid.ofList_toList]
    rw [key, key]
    funext q
    show (transMor δ (FreeMonoid.ofList _) : Q → Q) q = (transMor δ (FreeMonoid.ofList _) : Q → Q) q
    rw [transMor_apply, transMor_apply]
    exact h _ q
  let Ψ := Φ.mrangeRestrict
  have heq : ({w : List A | P (w.foldl δ q₀)} : Language A) =
      ⨆ y : {y : MonoidHom.mrange Φ // P (RT.ap y.1 q₀)},
        ({w : List A | Ψ (FreeMonoid.ofList w) = y.1} : Language A) := by
    ext w
    refine Iff.trans ?_ Language.mem_iSup.symm
    constructor
    · intro hw
      refine ⟨⟨Ψ (FreeMonoid.ofList w), ?_⟩, rfl⟩
      show P (RT.ap (Φ (FreeMonoid.ofList w)) q₀)
      rw [RT.ap, transMor_apply]
      exact hw
    · rintro ⟨⟨y, hy⟩, hwy⟩
      have hwy' : Ψ (FreeMonoid.ofList w) = y := hwy
      show P (w.foldl δ q₀)
      have h1 : Φ (FreeMonoid.ofList w) = y.1 := congrArg Subtype.val hwy'
      have h2 := transMor_apply δ w q₀
      rw [h1] at h2
      rw [← h2]
      exact hy
  rw [heq]
  exact HasHeightAtMost.iSup _ fun y => starFree_of_aperiodic hMap Ψ y.1

end WordAperiodic

/-! ### The first-return code -/

section Walk

variable {β : Type} {p : ℕ} (σ : β → ZMod p)

/-- The total displacement. -/
def zpSum (w : List β) : ZMod p := (w.map σ).sum

lemma zpSum_append (u w : List β) : zpSum σ (u ++ w) = zpSum σ u + zpSum σ w := by
  simp [zpSum]

lemma zpSum_cons (b : β) (w : List β) : zpSum σ (b :: w) = σ b + zpSum σ w := by
  simp [zpSum]

@[simp] lemma zpSum_nil : zpSum σ [] = 0 := rfl

lemma zpSum_single (b : β) : zpSum σ [b] = σ b := by simp [zpSum]

lemma zpSum_wpow (w : List β) : ∀ n : ℕ, zpSum σ (wpow w n) = n * zpSum σ w
  | 0 => by simp [wpow]
  | n + 1 => by rw [wpow_succ, zpSum_append, zpSum_wpow w n]; push_cast; ring

/-- **The first-return code** to state `0`. -/
def zpX : Language β :=
  {w | w ≠ [] ∧ zpSum σ w = 0 ∧ ∀ q, q <+: w → q ≠ [] → q ≠ w → zpSum σ q ≠ 0}

/-- Words with no nonempty prefix in state `0`. -/
def zpNR : Language β := {t | ∀ q, q <+: t → q ≠ [] → zpSum σ q ≠ 0}

lemma nil_mem_zpNR : ([] : List β) ∈ zpNR σ :=
  fun _ hq hne => absurd (List.prefix_nil.mp hq) hne

lemma zpNR_eq_nil {t : List β} (ht : t ∈ zpNR σ) (h0 : zpSum σ t = 0) : t = [] := by
  by_contra hne
  exact ht t List.prefix_rfl hne h0

/-- One step of the factorization. -/
def zpSplitStep (x : List (List β) × List β) (a : β) : List (List β) × List β :=
  if zpSum σ (x.2 ++ [a]) = 0 then (x.1 ++ [x.2 ++ [a]], []) else (x.1, x.2 ++ [a])

/-- The factorization into first returns and a tail. -/
def zpSplit (u : List β) : List (List β) × List β := u.foldl (zpSplitStep σ) ([], [])

lemma zpSplit_snoc (u : List β) (a : β) :
    zpSplit σ (u ++ [a]) = zpSplitStep σ (zpSplit σ u) a := by
  rw [zpSplit, List.foldl_append]; rfl

lemma mem_zpX_snoc {t : List β} (ht : t ∈ zpNR σ) {a : β} (h0 : zpSum σ (t ++ [a]) = 0) :
    t ++ [a] ∈ zpX σ := by
  refine ⟨by simp, h0, fun q hq hne hqe => ?_⟩
  rcases List.prefix_concat_iff.mp hq with h | h
  · exact absurd h hqe
  · exact ht q h hne

lemma zpSplit_spec (u : List β) : (zpSplit σ u).1.flatten ++ (zpSplit σ u).2 = u ∧
    AllIn (zpX σ) (zpSplit σ u).1 ∧ (zpSplit σ u).2 ∈ zpNR σ := by
  induction u using List.reverseRecOn with
  | nil => exact ⟨rfl, fun e he => by simp [zpSplit] at he, nil_mem_zpNR σ⟩
  | append_singleton u a ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [zpSplit_snoc]
      unfold zpSplitStep
      split_ifs with h0
      · refine ⟨?_, ?_, nil_mem_zpNR σ⟩
        · simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
          rw [← List.append_assoc, h1]
        · refine AllIn.append h2 ?_
          intro e he
          simp only [List.mem_singleton] at he
          subst he
          exact mem_zpX_snoc σ h3 h0
      · refine ⟨?_, h2, ?_⟩
        · simp only; rw [← List.append_assoc, h1]
        · intro q hq hne
          rcases List.prefix_concat_iff.mp hq with h | h
          · rw [h]; exact h0
          · exact h3 q h hne

lemma foldl_zpSplitStep_noRet (es₀ : List (List β)) :
    ∀ (v t₀ : List β), (∀ q, q <+: v → q ≠ [] → zpSum σ (t₀ ++ q) ≠ 0) →
      v.foldl (zpSplitStep σ) (es₀, t₀) = (es₀, t₀ ++ v)
  | [], t₀, _ => by simp
  | b :: v, t₀, h => by
      rw [List.foldl_cons]
      have hb : zpSum σ (t₀ ++ [b]) ≠ 0 := h [b] (by simp) (by simp)
      rw [show zpSplitStep σ (es₀, t₀) b = (es₀, t₀ ++ [b]) by simp [zpSplitStep, hb]]
      rw [foldl_zpSplitStep_noRet es₀ v (t₀ ++ [b])]
      · simp
      · intro q hq hne
        have := h (b :: q) (List.cons_prefix_cons.mpr ⟨rfl, hq⟩) (by simp)
        simpa using this

lemma foldl_zpSplitStep_X (es₀ : List (List β)) {e : List β} (he : e ∈ zpX σ) :
    e.foldl (zpSplitStep σ) (es₀, []) = (es₀ ++ [e], []) := by
  obtain ⟨hne, h0, hpre⟩ := he
  rcases List.eq_nil_or_concat e with rfl | ⟨e', a, rfl⟩
  · exact absurd rfl hne
  simp only [List.concat_eq_append] at h0 hpre ⊢
  rw [List.foldl_append, foldl_zpSplitStep_noRet σ es₀ e' []]
  · simp [zpSplitStep, h0]
  · intro q hq hqne
    simp only [List.nil_append]
    refine hpre q (hq.trans (List.prefix_append _ _)) hqne ?_
    intro hqe
    have := hq.length_le
    rw [hqe] at this
    simp at this

lemma foldl_zpSplitStep_flatten (t : List β) (ht : t ∈ zpNR σ) :
    ∀ (es es₀ : List (List β)), AllIn (zpX σ) es →
      (es.flatten ++ t).foldl (zpSplitStep σ) (es₀, []) = (es₀ ++ es, t)
  | [], es₀, _ => by
      simp only [List.flatten_nil, List.nil_append, List.append_nil]
      rw [foldl_zpSplitStep_noRet σ es₀ t []]
      · simp
      · intro q hq hne; simpa using ht q hq hne
  | e :: es, es₀, hes => by
      rw [List.flatten_cons, List.append_assoc, List.foldl_append,
        foldl_zpSplitStep_X σ es₀ (hes e (by simp)),
        foldl_zpSplitStep_flatten t ht es _ (fun f hf => hes f (by simp [hf]))]
      simp

/-- **Uniqueness of the factorization.** -/
lemma zpSplit_flatten {es : List (List β)} (hes : AllIn (zpX σ) es) {t : List β}
    (ht : t ∈ zpNR σ) : zpSplit σ (es.flatten ++ t) = (es, t) := by
  have := foldl_zpSplitStep_flatten σ t ht es [] hes
  simpa [zpSplit] using this

lemma zpX_prefixCode : PrefixCode (zpX σ) := by
  refine ⟨fun h => h.1 rfl, fun e he f hf hef => ?_⟩
  by_contra hne
  exact hf.2.2 e hef he.1 hne he.2.1

lemma zpSum_flatten_X : ∀ {es : List (List β)}, AllIn (zpX σ) es → zpSum σ es.flatten = 0
  | [], _ => by simp
  | e :: es, hes => by
      rw [List.flatten_cons, zpSum_append, (hes e (by simp)).2.1,
        zpSum_flatten_X (fun f hf => hes f (by simp [hf]))]
      simp

/-- Counting the blocks of a class on all words: the blocks, then a tail. -/
lemma bcount_split_eq (K : Language β) (m r : ℕ) :
    ({u | bcount K (zpSplit σ u).1 % m = r} : Language β) = bmod (zpX σ) K m r * zpNR σ := by
  ext u
  constructor
  · intro hu
    obtain ⟨h1, h2, h3⟩ := zpSplit_spec σ u
    exact Language.mem_mul.mpr ⟨_, ⟨(zpSplit σ u).1, h2, rfl, hu⟩, _, h3, h1⟩
  · intro hu
    obtain ⟨y, ⟨es, hes, rfl, hk⟩, t, ht, rfl⟩ := Language.mem_mul.mp hu
    show bcount K (zpSplit σ (es.flatten ++ t)).1 % m = r
    rw [zpSplit_flatten σ hes ht]
    exact hk

/-! ### The walk automaton -/

/-- The walk automaton: `some (some s)` = in state `s` (the start is `some (some 0)`), `some none` =
just returned to `0`, `none` = dead. -/
def zpWalk : Option (Option (ZMod p)) → β → Option (Option (ZMod p))
  | some (some s), a => if s + σ a = 0 then some none else some (some (s + σ a))
  | _, _ => none

open Classical in
/-- The state of `zpWalk` after a word, from `some (some s)`, described directly. -/
noncomputable def zpWalkState (s : ZMod p) (u : List β) : Option (Option (ZMod p)) :=
  if u = [] then some (some s)
  else if ∀ q, q <+: u → q ≠ [] → q ≠ u → s + zpSum σ q ≠ 0 then
    (if s + zpSum σ u = 0 then some none else some (some (s + zpSum σ u)))
  else none

lemma zpWalkState_snoc (s : ZMod p) (u : List β) (a : β) :
    zpWalkState σ s (u ++ [a]) = zpWalk σ (zpWalkState σ s u) a := by
  have hs : zpSum σ (u ++ [a]) = zpSum σ u + σ a := by rw [zpSum_append, zpSum_single]
  unfold zpWalkState
  rw [ite_eq_right (by simp)]
  by_cases hu : u = []
  · subst hu
    rw [ite_eq_left rfl, ite_eq_left]
    · simp [zpWalk, zpSum_single]
    · intro q hq hne hqe
      rcases List.prefix_concat_iff.mp hq with h | h
      · exact absurd h hqe
      · exact absurd (List.prefix_nil.mp h) hne
  rw [ite_eq_right hu]
  by_cases hc : ∀ q, q <+: u → q ≠ [] → q ≠ u → s + zpSum σ q ≠ 0
  · rw [ite_eq_left hc]
    by_cases h0 : s + zpSum σ u = 0
    · rw [ite_eq_left h0, ite_eq_right]
      · simp [zpWalk]
      · intro h
        exact h u (List.prefix_append _ _) hu (by simp) h0
    · rw [ite_eq_right h0, ite_eq_left]
      · simp only [zpWalk, hs, add_assoc]
      · intro q hq hne hqe
        rcases List.prefix_concat_iff.mp hq with h | h
        · exact absurd h hqe
        · by_cases hqu : q = u
          · rw [hqu]; exact h0
          · exact hc q h hne hqu
  · rw [ite_eq_right hc, ite_eq_right]
    · simp [zpWalk]
    · intro h
      apply hc
      intro q hq hne hqe
      refine h q (hq.trans (List.prefix_append _ _)) hne ?_
      intro hqe'
      have := hq.length_le
      rw [hqe'] at this
      simp at this

lemma zpWalkState_eq_foldl (s : ZMod p) (u : List β) :
    zpWalkState σ s u = u.foldl (zpWalk σ) (some (some s)) := by
  induction u using List.reverseRecOn with
  | nil => simp [zpWalkState]
  | append_singleton u a ih => rw [zpWalkState_snoc, ih, List.foldl_append]; rfl

lemma zpX_eq_walk : zpX σ = {u | u.foldl (zpWalk σ) (some (some 0)) = some none} := by
  ext u
  show u ∈ zpX σ ↔ u.foldl (zpWalk σ) (some (some 0)) = some none
  rw [← zpWalkState_eq_foldl]
  unfold zpWalkState
  constructor
  · rintro ⟨hne, h0, hpre⟩
    rw [ite_eq_right hne, ite_eq_left (fun q h1 h2 h3 => by rw [zero_add]; exact hpre q h1 h2 h3),
      ite_eq_left (by rw [zero_add]; exact h0)]
  · intro h
    split_ifs at h with hne hc h0
    all_goals first
      | (simp at h; done)
      | exact ⟨hne, by simpa using h0, fun q h1 h2 h3 => by simpa using hc q h1 h2 h3⟩

lemma zpNR_eq_walk : zpNR σ = {u | ∃ s, u.foldl (zpWalk σ) (some (some 0)) = some (some s)} := by
  ext u
  show u ∈ zpNR σ ↔ ∃ s, u.foldl (zpWalk σ) (some (some 0)) = some (some s)
  rw [← zpWalkState_eq_foldl]
  unfold zpWalkState
  constructor
  · intro h
    split_ifs with hne hc h0
    all_goals first
      | exact ⟨_, rfl⟩
      | exact absurd (by simpa using h0) (h u List.prefix_rfl hne)
      | exact absurd (fun q h1 h2 _ => by simpa using h q h1 h2) hc
  · rintro ⟨s, h⟩ q hq hne
    split_ifs at h with hu hc h0
    all_goals first
      | (simp at h; done)
      | (subst hu; exact absurd (List.prefix_nil.mp hq) hne)
      | (by_cases hqu : q = u
         · rw [hqu]; simpa using h0
         · simpa using hc q hq hne hqu)

lemma zpWalk_dead : ∀ u : List β, u.foldl (zpWalk σ) none = none
  | [] => rfl
  | _ :: u => by rw [List.foldl_cons]; exact zpWalk_dead u

lemma zpWalk_ret {u : List β} (hu : u ≠ []) : u.foldl (zpWalk σ) (some none) = none := by
  obtain ⟨a, u', rfl⟩ := List.exists_cons_of_ne_nil hu
  rw [List.foldl_cons]
  exact zpWalk_dead σ u'

/-- A nonempty word bringing the state `s` to `0` ends returned or dead. -/
lemma zpWalk_land {s : ZMod p} {u : List β} (hu : u ≠ []) (h0 : s + zpSum σ u = 0) :
    u.foldl (zpWalk σ) (some (some s)) = some none ∨
      u.foldl (zpWalk σ) (some (some s)) = none := by
  rw [← zpWalkState_eq_foldl]
  unfold zpWalkState
  rw [ite_eq_right hu]
  split_ifs <;> simp_all

/-- A word of displacement `0` fixes the state, or kills it. -/
lemma zpWalk_rot0 {s : ZMod p} {u : List β} (h0 : zpSum σ u = 0) :
    u.foldl (zpWalk σ) (some (some s)) = some (some s) ∨
      u.foldl (zpWalk σ) (some (some s)) = some none ∨
      u.foldl (zpWalk σ) (some (some s)) = none := by
  rw [← zpWalkState_eq_foldl]
  unfold zpWalkState
  split_ifs <;> simp_all

lemma foldl_wpow_succ (δ : Option (Option (ZMod p)) → β → Option (Option (ZMod p)))
    (w : List β) (n : ℕ) (q : Option (Option (ZMod p))) :
    (wpow w (n + 1)).foldl δ q = (wpow w n).foldl δ (w.foldl δ q) := by
  rw [wpow_succ, List.foldl_append]

/-- Some `k ∈ [1, p]` brings `s` to `0` in steps of `r ≠ 0`. -/
lemma exists_land [hp : Fact p.Prime] (s r : ZMod p) (hr : r ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ p ∧ s + (k : ZMod p) * r = 0 := by
  have hp1 : 1 < p := hp.out.one_lt
  have : NeZero p := ⟨hp.out.ne_zero⟩
  by_cases hk0 : ((-s) * r⁻¹).val = 0
  · refine ⟨p, hp1.le, le_rfl, ?_⟩
    have hs : -s * r⁻¹ = 0 := (ZMod.val_eq_zero _).mp hk0
    have : s = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact neg_eq_zero.mp h
      · exact absurd (inv_eq_zero.mp h) hr
    simp [this]
  · refine ⟨((-s) * r⁻¹).val, Nat.one_le_iff_ne_zero.mpr hk0, (ZMod.val_lt _).le, ?_⟩
    rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hr]
    ring

/-- **The walk automaton has stable powers** for `p` prime. -/
lemma zpWalk_pow_stable [hp : Fact p.Prime] (w : List β) (q : Option (Option (ZMod p))) :
    (wpow w (p + 2)).foldl (zpWalk σ) q = (wpow w (p + 1)).foldl (zpWalk σ) q := by
  by_cases hw : w = []
  · subst hw
    have : ∀ n, wpow ([] : List β) n = [] := fun n => by simp [wpow]
    rw [this, this]
  -- `w^(n+2)` from a returned or dead state is dead
  have hdead : ∀ q' : Option (Option (ZMod p)), (q' = some none ∨ q' = none) →
      ∀ n, (wpow w (n + 1)).foldl (zpWalk σ) q' = none := by
    intro q' hq' n
    rw [foldl_wpow_succ]
    rcases hq' with rfl | rfl
    · rw [zpWalk_ret σ hw, zpWalk_dead]
    · rw [zpWalk_dead, zpWalk_dead]
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hboth : ∀ q', (∀ n, (wpow w (n + 2)).foldl (zpWalk σ) q' = none) →
      (wpow w (p + 2)).foldl (zpWalk σ) q' = (wpow w (p + 1)).foldl (zpWalk σ) q' := by
    intro q' h
    rw [h p, show p + 1 = (p - 1) + 2 by omega, h]
  rcases q with _ | _ | s
  · rw [zpWalk_dead, zpWalk_dead]
  · rw [hdead _ (Or.inl rfl), hdead _ (Or.inl rfl)]
  by_cases hr : zpSum σ w = 0
  · rcases zpWalk_rot0 σ (s := s) hr with h | h | h
    · have hfix : ∀ n, (wpow w n).foldl (zpWalk σ) (some (some s)) = some (some s) := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [wpow_succ', List.foldl_append, ih, h]
      rw [hfix, hfix]
    · exact hboth _ fun n => by rw [foldl_wpow_succ, h, hdead _ (Or.inl rfl)]
    · exact hboth _ fun n => by rw [foldl_wpow_succ, h, zpWalk_dead]
  · obtain ⟨k, hk1, hkp, hk⟩ := exists_land s (zpSum σ w) hr
    have hkne : wpow w k ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [wpow_length] at this
      simp only [List.length_nil, mul_eq_zero] at this
      rcases this with h1 | h1
      · omega
      · exact hw (List.eq_nil_of_length_eq_zero h1)
    have hland := zpWalk_land σ hkne (by rw [zpSum_wpow]; exact hk)
    have hsplit : ∀ j, wpow w (k + (j + 1)) = wpow w k ++ wpow w (j + 1) := by
      intro j; unfold wpow; rw [List.replicate_add, List.flatten_append]
    obtain ⟨j, hj⟩ : ∃ j, p + 1 = k + (j + 1) := ⟨p - k, by omega⟩
    rw [show p + 2 = k + (j + 1 + 1) by omega, hj, hsplit, hsplit, List.foldl_append,
      List.foldl_append, hdead _ hland, hdead _ hland]

theorem zpWalk_starFree [Fact p.Prime] [Finite β] (P : Option (Option (ZMod p)) → Prop) :
    HasHeightAtMost {u : List β | P (u.foldl (zpWalk σ) (some (some 0)))} 0 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact starFree_of_pow_stable (zpWalk σ) (p + 1) (fun w q => zpWalk_pow_stable σ w q) _ P

theorem zpX_starFree [Fact p.Prime] [Finite β] : HasHeightAtMost (zpX σ) 0 := by
  rw [zpX_eq_walk]; exact zpWalk_starFree σ (fun q => q = some none)

theorem zpNR_starFree [Fact p.Prime] [Finite β] : HasHeightAtMost (zpNR σ) 0 := by
  rw [zpNR_eq_walk]; exact zpWalk_starFree σ (fun q => ∃ s, q = some (some s))

/-- **Counting blocks of a class.** If `K ⊆ zpX σ`, `K` and `K∗` are star-free, counting the
blocks of `K` in the factorization of a word modulo `m` has height at most one. -/
theorem bcount_split_height [Fact p.Prime] [Finite β] [DecidableEq β] (K : Language β)
    (hK : K ≤ zpX σ) (h0 : HasHeightAtMost K 0) (hs : HasHeightAtMost K∗ 0) {m r : ℕ}
    (hr : r < m) : HasHeightAtMost {u | bcount K (zpSplit σ u).1 % m = r} 1 := by
  rw [bcount_split_eq]
  have hsplit : K + (zpX σ ⊓ Kᶜ) = zpX σ := by
    ext e
    rw [Language.mem_add]
    constructor
    · rintro (h | h)
      · exact hK h
      · exact h.1
    · intro h
      by_cases hk : e ∈ K
      · exact Or.inl hk
      · exact Or.inr ⟨h, hk⟩
  have hpc : PrefixCode (K + (zpX σ ⊓ Kᶜ)) := by rw [hsplit]; exact zpX_prefixCode σ
  have hdis : Disjoint K (zpX σ ⊓ Kᶜ) := Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1
  have h1 : HasHeightAtMost (zpX σ ⊓ Kᶜ) 0 := (zpX_starFree σ).inter h0.compl
  have h := transfer_height_one hpc hdis h0 h1 hs hr
  rw [hsplit] at h
  exact h.concat ((zpNR_starFree σ).mono (by omega))

end Walk

end GeneralizedStarHeight
