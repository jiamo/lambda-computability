import Start.StarHeightZpPairs
import Start.StarHeightIndexFour
import Start.StarHeightPrimeCount
import Start.StarHeightCommutative

/-!
# The `Z_p` core for every prime `p`

`ZpCoreHeightOne p`: for every finite alphabet `α`, displacements `δ : α → ZMod p` and letter `x`,
the number of positions reading `x` in state `0` (`vcount δ 0 x`) is, modulo every `n`, a language
of generalized star height at most one.  `zpcore` proves it for every prime `p`; `z5core` is the
case `p = 5` (Bourne's Question 5.8 for `r = 5`).

* Reductions: letters of displacement `0` other than `x` are erased (inverse alphabetic
  morphism); if `δ x ≠ 0`, multiplying by the unit `(δ x)⁻¹` makes `δ x = 1`.
* `δ x = 0` (`zpcore_fixed`): `x` is read in state `0` exactly when `[x]` is a block of the
  first-return factorization; the Transfer Lemma applies to `{[x]}`, whose star is star-free.
* `δ x = 1` (`zpcore_moving`), every other letter of nonzero displacement: the identity
  (`zp_identity`), with `φ(s) = (-s).val` and `s` the state between two adjacent letters,
  `p·N₀ + Σ_{(a ≠ x, x)} φ(s) = |u|ₓ + Σ_{(x, c ≠ x)} φ(s) + [u ends with x]·φ(σ(u))`.
  It telescopes along the maximal runs of `x`, by `p·[s = 0] + φ(s) = 1 + φ(s + 1)`.  The pairs in
  state `s₀` whose second letter has displacement `d` are the blocks of the class
  `pcls` ("first returns ending with the pair") on the word shifted by a fresh first letter of
  displacement `-(s₀ + d)`; these classes and their stars are star-free
  (`Start/StarHeightZpPairs.lean`), so the Transfer Lemma gives their residues height one.
-/

namespace GeneralizedStarHeight

universe u

open EpisodeAlgebra
open scoped Computability
open Classical

section Counts

variable {β : Type} {p : ℕ} (σ : β → ZMod p)

/-- The last letter of `u`, or `prev`. -/
def lastOr : Option β → List β → Option β
  | prev, [] => prev
  | _, c :: u => lastOr (some c) u

lemma lastOr_append (prev : Option β) (u v : List β) :
    lastOr prev (u ++ v) = lastOr (lastOr prev u) v := by
  induction u generalizing prev with
  | nil => rfl
  | cons c u ih => exact ih (some c)

lemma lastOr_snoc (prev : Option β) (u : List β) (a : β) : lastOr prev (u ++ [a]) = some a := by
  rw [lastOr_append]; rfl

/-- Pairs `(a, c)` with `Q a c` landing on `0` (the state after `c` is `0`), reading from `s`
after `prev`. -/
noncomputable def pc0 (Q : β → β → Prop) : ZMod p → Option β → List β → ℕ
  | _, _, [] => 0
  | s, prev, c :: u =>
      (if (∃ a, prev = some a ∧ Q a c) ∧ s + σ c = 0 then 1 else 0) + pc0 Q (s + σ c) (some c) u

/-- Pairs `(a, c)` with `Q a c` whose state before `c` is `s₀`. -/
noncomputable def pcB (Q : β → β → Prop) (s₀ : ZMod p) : ZMod p → Option β → List β → ℕ
  | _, _, [] => 0
  | s, prev, c :: u =>
      (if (∃ a, prev = some a ∧ Q a c) ∧ s = s₀ then 1 else 0) + pcB Q s₀ (s + σ c) (some c) u

/-- `φ(s) = (-s).val`. -/
def zphi (s : ZMod p) : ℕ := (-s).val

/-- Pairs `(a, c)` with `Q a c`, weighted by `φ` of the state before `c`. -/
noncomputable def pairW (Q : β → β → Prop) : ZMod p → Option β → List β → ℕ
  | _, _, [] => 0
  | s, prev, c :: u =>
      (if ∃ a, prev = some a ∧ Q a c then zphi s else 0) + pairW Q (s + σ c) (some c) u

lemma pc0_append (Q : β → β → Prop) (u v : List β) (s : ZMod p) (prev : Option β) :
    pc0 σ Q s prev (u ++ v) = pc0 σ Q s prev u + pc0 σ Q (s + zpSum σ u) (lastOr prev u) v := by
  induction u generalizing s prev with
  | nil => simp [pc0, lastOr]
  | cons c u ih =>
      simp only [List.cons_append, pc0, ih, zpSum_cons, lastOr, add_assoc]

lemma pc0_zero (Q : β → β → Prop) :
    ∀ (u : List β) (s : ZMod p) (prev : Option β),
      (∀ q, q <+: u → q ≠ [] → s + zpSum σ q ≠ 0) → pc0 σ Q s prev u = 0
  | [], _, _, _ => rfl
  | c :: u, s, prev, h => by
      have h1 : s + σ c ≠ 0 := by
        have := h [c] (List.cons_prefix_cons.mpr ⟨rfl, List.nil_prefix⟩) (by simp)
        rwa [zpSum_single] at this
      rw [pc0, if_neg (fun h' => h1 h'.2), zero_add]
      refine pc0_zero Q u _ _ fun q hq hne => ?_
      have := h (c :: q) (List.cons_prefix_cons.mpr ⟨rfl, hq⟩) (by simp)
      rwa [zpSum_cons, ← add_assoc] at this

lemma not_mem_pairEnd_single (P : β → β → Prop) (c : β) : [c] ∉ PairEnd P := by
  rintro ⟨v, a, c', hv, -⟩
  have := congrArg List.length hv
  simp at this

lemma mem_pairEnd_snoc2 (P : β → β → Prop) (t : List β) (a c : β) :
    t ++ [a] ++ [c] ∈ PairEnd P ↔ P a c := by
  constructor
  · rintro ⟨v, a', c', hv, hP⟩
    rw [List.append_assoc, show [a] ++ [c] = [a, c] from rfl] at hv
    have h2 := List.append_inj' hv rfl
    simp only [List.cons.injEq, and_true] at h2
    rw [h2.2.1, h2.2.2]
    exact hP
  · intro h
    exact ⟨t, a, c, by simp, h⟩

/-- On a first return, `pc0` counts whether it ends with a `Q`-pair. -/
lemma pc0_block (Q : β → β → Prop) (hQ : ∀ a c, Q a c → σ c ≠ 0) {e : List β}
    (he : e ∈ zpX σ) (prev : Option β) :
    pc0 σ Q 0 prev e = if e ∈ PairEnd Q then 1 else 0 := by
  obtain ⟨hne, h0, hpre⟩ := he
  rcases List.eq_nil_or_concat e with rfl | ⟨e', c, rfl⟩
  · exact absurd rfl hne
  simp only [List.concat_eq_append] at h0 hpre ⊢
  rw [pc0_append, pc0_zero σ Q e' 0 prev, zero_add]
  swap
  · intro q hq hqne
    rw [zero_add]
    exact hpre q (hq.trans (List.prefix_append _ _)) hqne
      (fun h => by have := hq.length_le; rw [h] at this; simp at this)
  rw [zpSum_append, zpSum_single] at h0
  simp only [pc0, zero_add, add_zero, h0, and_true]
  rcases List.eq_nil_or_concat e' with rfl | ⟨t, a, rfl⟩
  · simp only [List.nil_append, zpSum_nil, zero_add] at h0 ⊢
    rw [if_neg (not_mem_pairEnd_single Q c), if_neg]
    rintro ⟨a, -, hac⟩
    exact hQ a c hac (by simpa using h0)
  · simp only [List.concat_eq_append] at h0 ⊢
    rw [lastOr_snoc]
    by_cases hP : Q a c
    · rw [if_pos ⟨a, rfl, hP⟩, if_pos ((mem_pairEnd_snoc2 Q t a c).mpr hP)]
    · rw [if_neg (fun ⟨a', ha', h'⟩ => hP (by cases ha'; exact h')),
        if_neg (fun h => hP ((mem_pairEnd_snoc2 Q t a c).mp h))]

lemma pc0_flatten (Q : β → β → Prop) (hQ : ∀ a c, Q a c → σ c ≠ 0) {t : List β}
    (ht : t ∈ zpNR σ) :
    ∀ (es : List (List β)) (prev : Option β), AllIn (zpX σ) es →
      pc0 σ Q 0 prev (es.flatten ++ t) = bcount (pcls σ Q) es
  | [], prev, _ => by
      simp only [List.flatten_nil, List.nil_append]
      rw [pc0_zero σ Q t 0 prev (fun q hq hne => by rw [zero_add]; exact ht q hq hne)]
      simp [bcount]
  | e :: es, prev, hes => by
      have he := hes e (by simp)
      rw [List.flatten_cons, List.append_assoc, pc0_append, pc0_block σ Q hQ he, zero_add,
        he.2.1, pc0_flatten Q hQ ht es _ (fun f hf => hes f (by simp [hf]))]
      simp only [bcount, List.countP_cons]
      rw [add_comm]
      congr 1
      by_cases hP : e ∈ PairEnd Q
      · have hm : e ∈ pcls σ Q := ⟨he, hP⟩
        simp [hm, hP]
      · have hm : e ∉ pcls σ Q := fun h => hP h.2
        simp [hm, hP]

/-- **`pc0` is a block count** of the class `pcls σ Q`. -/
lemma pc0_eq_bcount (Q : β → β → Prop) (hQ : ∀ a c, Q a c → σ c ≠ 0) (u : List β)
    (prev : Option β) : pc0 σ Q 0 prev u = bcount (pcls σ Q) (zpSplit σ u).1 := by
  obtain ⟨h1, h2, h3⟩ := zpSplit_spec σ u
  conv_lhs => rw [← h1]
  exact pc0_flatten σ Q hQ h3 _ prev h2

end Counts

/-! ### The shift by a fresh first letter -/

section Shift

variable {β : Type} {p : ℕ} (σ : β → ZMod p)

/-- The displacements on `Option β`: the fresh letter `none` moves by `-J`. -/
def shiftσ (J : ZMod p) : Option β → ZMod p := fun o => o.elim (-J) σ

/-- The lifted relation. -/
def liftQ (Q : β → β → Prop) : Option β → Option β → Prop :=
  fun o o' => ∃ a c, o = some a ∧ o' = some c ∧ Q a c

/-- The lifted previous letter. -/
def liftP : Option β → Option (Option β)
  | none => some none
  | some a => some (some a)

lemma pcB_eq_shift (Q : β → β → Prop) {d s₀ : ZMod p} (hd : ∀ a c, Q a c → σ c = d) :
    ∀ (u : List β) (s : ZMod p) (prev : Option β),
      pc0 (shiftσ σ (s₀ + d)) (liftQ Q) (s - (s₀ + d)) (liftP prev) (u.map some) =
        pcB σ Q s₀ s prev u
  | [], _, _ => rfl
  | c :: u, s, prev => by
      rw [List.map_cons, pc0, pcB]
      have hrec := pcB_eq_shift (s₀ := s₀) Q hd u (s + σ c) (some c)
      simp only [liftP] at hrec
      rw [show s - (s₀ + d) + shiftσ σ (s₀ + d) (some c) = s + σ c - (s₀ + d) by
        simp only [shiftσ, Option.elim]; ring, hrec]
      congr 1
      have hiff : ((∃ a, liftP prev = some a ∧ liftQ Q a (some c)) ∧
          s + σ c - (s₀ + d) = 0) ↔ (∃ a, prev = some a ∧ Q a c) ∧ s = s₀ := by
        constructor
        · rintro ⟨⟨a', ha', a, c', rfl, hc', hQ⟩, h0⟩
          simp only [Option.some.injEq] at hc'
          subst hc'
          cases prev with
          | none => simp [liftP] at ha'
          | some b =>
              simp only [liftP, Option.some.injEq] at ha'
              subst ha'
              refine ⟨⟨_, rfl, hQ⟩, ?_⟩
              rw [hd _ _ hQ] at h0
              linear_combination h0
        · rintro ⟨⟨a, rfl, hQ⟩, rfl⟩
          refine ⟨⟨some a, rfl, a, c, rfl, rfl, hQ⟩, ?_⟩
          rw [hd a c hQ]; ring
      by_cases h : (∃ a, prev = some a ∧ Q a c) ∧ s = s₀
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

lemma pcB_eq_bcount (Q : β → β → Prop) {d s₀ : ZMod p} (hd : ∀ a c, Q a c → σ c = d)
    (hQ : ∀ a c, Q a c → σ c ≠ 0) (u : List β) :
    pcB σ Q s₀ 0 none u = bcount (pcls (shiftσ σ (s₀ + d)) (liftQ Q))
      (zpSplit (shiftσ σ (s₀ + d)) (none :: u.map some)).1 := by
  rw [← pc0_eq_bcount (shiftσ σ (s₀ + d)) (liftQ Q) ?_ _ none, ← pcB_eq_shift σ Q hd u 0 none,
    pc0]
  · rw [if_neg (fun h => by obtain ⟨⟨a, ha, -⟩, -⟩ := h; simp at ha)]
    simp [shiftσ, liftP, sub_eq_add_neg]
  · rintro _ _ ⟨a, c, rfl, rfl, h⟩
    exact hQ a c h

/-- **Pair counts have height one.** -/
theorem pcB_height [Fact p.Prime] [Finite β] [DecidableEq β] (Q : β → β → Prop) {d s₀ : ZMod p}
    (hd : ∀ a c, Q a c → σ c = d) (hQ : ∀ a c, Q a c → σ c ≠ 0) {y : β}
    (hP : (∀ a c, Q a c → a = y ∧ c ≠ y) ∨ (∀ a c, Q a c → a ≠ y ∧ c = y)) {m r : ℕ}
    (hr : r < m) : HasHeightAtMost {u : List β | pcB σ Q s₀ 0 none u % m = r} 1 := by
  set σ' := shiftσ σ (s₀ + d)
  have hP' : (∀ a c, liftQ Q a c → a = some y ∧ c ≠ some y) ∨
      (∀ a c, liftQ Q a c → a ≠ some y ∧ c = some y) := by
    rcases hP with h | h
    · left
      rintro _ _ ⟨a, c, rfl, rfl, hQ⟩
      obtain ⟨h1, h2⟩ := h a c hQ
      exact ⟨by rw [h1], by simpa using h2⟩
    · right
      rintro _ _ ⟨a, c, rfl, rfl, hQ⟩
      obtain ⟨h1, h2⟩ := h a c hQ
      exact ⟨by simpa using h1, by rw [h2]⟩
  have hL := bcount_split_height σ' (pcls σ' (liftQ Q)) (pcls_le σ' _) (pcls_starFree σ' _)
    (pcls_kstar_starFree σ' _ hP') hr
  let φ : β → Option (Option β) := fun a => some (some a)
  have heq : {u : List β | pcB σ Q s₀ 0 none u % m = r} =
      invAlph φ (leftQuot none {v | bcount (pcls σ' (liftQ Q)) (zpSplit σ' v).1 % m = r}) := by
    ext u
    have hfm : u.filterMap φ = u.map some := by
      induction u with
      | nil => rfl
      | cons b u ih => simp [φ, ih]
    show _ % m = r ↔ bcount _ (zpSplit σ' (none :: u.filterMap φ)).1 % m = r
    rw [hfm, pcB_eq_bcount σ Q hd hQ]
  rw [heq]
  exact (hL.leftQuot none).invAlph φ

end Shift

/-! ### The identity -/

section Identity

variable {β : Type} [DecidableEq β] {p : ℕ} (σ : β → ZMod p)

lemma zphi_step [Fact p.Prime] (s : ZMod p) :
    p * (if s = 0 then 1 else 0) + zphi s = 1 + zphi (s + 1) := by
  have hp := (Fact.out : p.Prime).two_le
  have : NeZero p := ⟨by omega⟩
  unfold zphi
  rw [ZMod.neg_val, ZMod.neg_val]
  have hv := ZMod.val_lt s
  have h1 : (s + 1).val = (s.val + 1) % p := by
    rw [ZMod.val_add, ZMod.val_one]
  have hs0 : s = 0 ↔ s.val = 0 := (ZMod.val_eq_zero s).symm
  have hs1 : s + 1 = 0 ↔ (s + 1).val = 0 := (ZMod.val_eq_zero _).symm
  by_cases h : s.val + 1 = p
  · have e1 : (s + 1).val = 0 := by rw [h1, h, Nat.mod_self]
    have hn : ¬ s = 0 := fun h' => by rw [hs0] at h'; omega
    rw [if_pos (hs1.mpr e1), if_neg hn, if_neg hn]
    omega
  · have e1 : (s + 1).val = s.val + 1 := by rw [h1, Nat.mod_eq_of_lt (by omega)]
    have hn : ¬ s + 1 = 0 := fun h' => by rw [hs1, e1] at h'; omega
    rw [if_neg hn, e1]
    by_cases h0 : s = 0
    · rw [if_pos h0, if_pos h0]; rw [hs0] at h0; omega
    · rw [if_neg h0, if_neg h0]; rw [hs0] at h0; omega

/-- `QA a c`: `a ≠ x`, `c = x`. -/
def QA (x : β) : β → β → Prop := fun a c => a ≠ x ∧ c = x

/-- `QB a c`: `a = x`, `c ≠ x`. -/
def QB (x : β) : β → β → Prop := fun a c => a = x ∧ c ≠ x

/-- **The identity**, read from a state `s` after the letter `prev`. -/
lemma zp_identity_aux [Fact p.Prime] (x : β) (hx : σ x = 1) :
    ∀ (u : List β) (s : ZMod p) (prev : Option β), (prev = none → s = 0) →
      p * vcountFrom σ 0 x s u + pairW σ (QA x) s prev u +
          (if prev = some x then zphi s else 0) =
        u.count x + pairW σ (QB x) s prev u +
          (if lastOr prev u = some x then zphi (s + zpSum σ u) else 0)
  | [], s, prev, _ => by simp [vcountFrom_nil, pairW, lastOr]
  | c :: u, s, prev, hs => by
      have ih := zp_identity_aux x hx u (s + σ c) (some c) (fun h => by simp at h)
      have e1 : vcountFrom σ 0 x s (c :: u) =
          (if c = x ∧ s = 0 then 1 else 0) + vcountFrom σ 0 x (s + σ c) u := by
        rw [vcountFrom_cons]; congr
      have e2 : pairW σ (QA x) s prev (c :: u) = (if ∃ a, prev = some a ∧ QA x a c then zphi s
          else 0) + pairW σ (QA x) (s + σ c) (some c) u := rfl
      have e3 : pairW σ (QB x) s prev (c :: u) = (if ∃ a, prev = some a ∧ QB x a c then zphi s
          else 0) + pairW σ (QB x) (s + σ c) (some c) u := rfl
      have e4 : (c :: u).count x = u.count x + (if c = x then 1 else 0) := by
        simp [List.count_cons]
      have e5 : lastOr prev (c :: u) = lastOr (some c) u := rfl
      have e6 : s + zpSum σ (c :: u) = s + σ c + zpSum σ u := by rw [zpSum_cons, add_assoc]
      rw [e1, e2, e3, e4, e5, e6, mul_add]
      generalize vcountFrom σ 0 x (s + σ c) u = N at ih ⊢
      generalize pairW σ (QA x) (s + σ c) (some c) u = WA at ih ⊢
      generalize pairW σ (QB x) (s + σ c) (some c) u = WB at ih ⊢
      generalize (if lastOr (some c) u = some x then zphi (s + σ c + zpSum σ u) else 0) = E at ih ⊢
      by_cases hc : c = x
      · have i1 : (if c = x ∧ s = 0 then 1 else 0) = if s = 0 then 1 else 0 := by simp [hc]
        have i2 : (if c = x then 1 else 0) = 1 := by simp [hc]
        have i3 : (if ∃ a, prev = some a ∧ QB x a c then zphi s else 0) = 0 := by simp [QB, hc]
        have i4 : (if some c = some x then zphi (s + σ c) else 0) = zphi (s + 1) := by
          simp [hc, hx]
        rw [i1, i2, i3]
        rw [i4] at ih
        have hstep := zphi_step s
        cases prev with
        | none =>
            have h0 := hs rfl
            subst h0
            have i5 : (if ∃ a, (none : Option β) = some a ∧ QA x a c then zphi (0 : ZMod p)
                else 0) = 0 := by simp
            have i6 : (if (none : Option β) = some x then zphi (0 : ZMod p) else 0) = 0 := by simp
            have i7 : zphi (0 : ZMod p) = 0 := by simp [zphi]
            rw [i5, i6, if_pos rfl]
            rw [i7, if_pos rfl] at hstep
            rw [zero_add] at ih hstep
            omega
        | some b =>
            have i5 : (if ∃ a, some b = some a ∧ QA x a c then zphi s else 0) +
                (if some b = some x then zphi s else 0) = zphi s := by
              by_cases hb : b = x
              · simp [QA, hb]
              · simp [QA, hb, hc]
            omega
      · have i1 : (if c = x ∧ s = 0 then 1 else 0) = 0 := by simp [hc]
        have i2 : (if c = x then 1 else 0) = 0 := by simp [hc]
        have i3 : (if ∃ a, prev = some a ∧ QA x a c then zphi s else 0) = 0 := by simp [QA, hc]
        have i4 : (if some c = some x then zphi (s + σ c) else 0) = 0 := by simp [hc]
        have i5 : (if ∃ a, prev = some a ∧ QB x a c then zphi s else 0) =
            if prev = some x then zphi s else 0 := by
          cases prev with
          | none => simp
          | some b =>
              by_cases hb : b = x
              · simp [QB, hb, hc]
              · simp [QB, hb]
        rw [i1, i2, i3, i5]
        rw [i4] at ih
        omega

end Identity

end GeneralizedStarHeight
