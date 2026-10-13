/-
**One step of a multi-tape machine as two left-to-right transductions.**

A configuration of upstream's `FiniteMultiTapeMachine` (`Start/DepthThreeModel.lean`) is written
as a word over the finite alphabet `Sym M = Γ ⊕ Q ⊕ K`:

  `stSym q :: seg k₁ L₁ R₁ ++ … ++ seg kₙ Lₙ Rₙ`,  `seg k L R = sepA k :: (L ++ sepA k :: R)`,

where `k₁, …, kₙ` lists the tapes, `L` is the left part of tape `k` read from the head outwards,
and `R` is the head cell followed by the right part (`tapeOf L R`; trailing blanks may or may not
be written).  The *info* transducer reads the state and the head symbols; for each action of the
transition table the *edit* transducer rewrites the word into the word of the next configuration.

Main definitions:

* `Complexity.MultiTapeCobham.word`, `Complexity.MultiTapeCobham.Rep` — the encoding;
* `Complexity.MultiTapeCobham.infoδ` — the info transducer;
* `Complexity.MultiTapeCobham.edδ`, `Complexity.MultiTapeCobham.edOut` — the edit transducer.

Main results:

* `Complexity.MultiTapeCobham.info_word` — the info transducer computes the state and the heads;
* `Complexity.MultiTapeCobham.edit_word` — the edit transducer computes the next word;
* `Complexity.MultiTapeCobham.rep_update` — the next word represents the next configuration.
-/

import Start.MacroTransducer
import Start.DepthThreeModel

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Complexity

namespace MultiTapeCobham

open DepthThreeLowerBound Macro

variable (M : FiniteMultiTapeMachine)

/-- The alphabet of encoded configurations: tape symbols, states and tape separators. -/
abbrev Sym := M.Γ ⊕ M.Q ⊕ M.K

instance : Inhabited (Sym M) := ⟨Sum.inl default⟩

/-- A tape symbol. -/
def sym (γ : M.Γ) : Sym M := Sum.inl γ

/-- A state symbol. -/
def stSym (q : M.Q) : Sym M := Sum.inr (Sum.inl q)

/-- The separator of tape `k`. -/
def sepA (k : M.K) : Sym M := Sum.inr (Sum.inr k)

/-- The tapes, in a fixed order. -/
noncomputable def ks : List M.K := Finset.univ.toList

theorem ks_nodup : (ks M).Nodup := Finset.nodup_toList _

theorem mem_ks (k : M.K) : k ∈ ks M := Finset.mem_toList.mpr (Finset.mem_univ k)

/-- The segment of tape `k`. -/
def seg (k : M.K) (L R : List M.Γ) : List (Sym M) :=
  sepA M k :: (L.map (sym M) ++ sepA M k :: R.map (sym M))

/-- The segments of the tapes `l`. -/
def segs (l : List M.K) (Ls Rs : M.K → List M.Γ) : List (Sym M) :=
  l.flatMap fun k => seg M k (Ls k) (Rs k)

/-- The word of a configuration given by its state and the two halves of every tape. -/
noncomputable def word (q : M.Q) (Ls Rs : M.K → List M.Γ) : List (Sym M) :=
  stSym M q :: segs M (ks M) Ls Rs

/-- The tape with left part `L` (read outwards from the head) and head-and-right part `R`. -/
def tapeOf (L R : List M.Γ) : Turing.Tape M.Γ :=
  ⟨R.headI, Turing.ListBlank.mk L, Turing.ListBlank.mk R.tail⟩

/-- `u` is a word of the configuration `c`. -/
def Rep (u : List (Sym M)) (c : M.Cfg) : Prop :=
  ∃ Ls Rs : M.K → List M.Γ, (∀ k, c.tapes k = tapeOf M (Ls k) (Rs k)) ∧ u = word M c.q Ls Rs

/-! ### The info transducer -/

/-- States of the info transducer: the state read, a phase (`1` inside a left part, `2` inside a
right part), the current tape, whether the head cell is still to be read, and the heads read. -/
abbrev InfoSt := Option M.Q × Fin 3 × Option M.K × Bool × (M.K → M.Γ)

/-- The transition of the info transducer. -/
def infoδ : InfoSt M → Sym M → InfoSt M
  | (_, ph, tp, pd, h), Sum.inr (Sum.inl q') => (some q', ph, tp, pd, h)
  | (q, ph, tp, _, h), Sum.inr (Sum.inr k) =>
      if ph = 1 then (q, 2, tp, true, h) else (q, 1, some k, false, h)
  | (q, ph, tp, pd, h), Sum.inl γ =>
      if ph = 2 ∧ pd = true then
        (q, ph, tp, false, match tp with
          | some k => Function.update h k γ
          | none => h)
      else (q, ph, tp, false, h)

/-- The initial state of the info transducer. -/
def info0 : InfoSt M := (none, 0, none, false, fun _ => default)

theorem info_L (q : Option M.Q) (k : M.K) (pd : Bool) (h : M.K → M.Γ) (L : List M.Γ) :
    mlst (infoδ M) (q, 1, some k, pd, h) (L.map (sym M)) =
      if L = [] then (q, 1, some k, pd, h) else (q, 1, some k, false, h) := by
  induction L generalizing pd with
  | nil => simp
  | cons γ L ih =>
    simp only [List.map_cons, mlst_cons, reduceCtorEq, if_false]
    simp only [infoδ, sym]
    rw [if_neg (by simp)]
    rw [ih]
    split <;> rfl

theorem info_R_tail (q : Option M.Q) (k : M.K) (h : M.K → M.Γ) (R : List M.Γ) :
    mlst (infoδ M) (q, 2, some k, false, h) (R.map (sym M)) = (q, 2, some k, false, h) := by
  induction R with
  | nil => rfl
  | cons γ R ih =>
    simp only [List.map_cons, mlst_cons]
    simp only [infoδ, sym]
    rw [if_neg (by simp)]
    exact ih

theorem info_seg (q : Option M.Q) (ph : Fin 3) (tp : Option M.K) (pd : Bool)
    (h : M.K → M.Γ) (hph : ph ≠ 1) (k : M.K) (hk : h k = default) (L R : List M.Γ) :
    ∃ tp' pd', mlst (infoδ M) (q, ph, tp, pd, h) (seg M k L R) =
      (q, 2, tp', pd', Function.update h k R.headI) := by
  unfold seg
  rw [mlst_cons, mlst_append]
  have h1 : infoδ M (q, ph, tp, pd, h) (sepA M k) = (q, 1, some k, false, h) := by
    simp [infoδ, sepA, hph]
  rw [h1, info_L]
  have h2 : ∀ pd0 : Bool, mlst (infoδ M) (q, 1, some k, pd0, h) (sepA M k :: R.map (sym M)) =
      mlst (infoδ M) (q, 2, some k, true, h) (R.map (sym M)) := by
    intro pd0
    rfl
  have h3 : mlst (infoδ M) (q, 2, some k, true, h) (R.map (sym M)) =
      if R = [] then (q, 2, some k, true, h)
      else (q, 2, some k, false, Function.update h k R.headI) := by
    cases R with
    | nil => rfl
    | cons γ R =>
      simp only [List.map_cons, mlst_cons, reduceCtorEq, if_false, List.headI_cons]
      simp only [infoδ, sym]
      exact info_R_tail M q k _ R
  split
  · rw [h2, h3]
    split
    · rename_i hR
      subst hR
      refine ⟨some k, true, ?_⟩
      simp [List.headI, ← hk]
    · exact ⟨some k, false, rfl⟩
  · rw [h2, h3]
    split
    · rename_i _ hR
      subst hR
      refine ⟨some k, true, ?_⟩
      simp [List.headI, ← hk]
    · exact ⟨some k, false, rfl⟩

theorem info_segs (Ls Rs : M.K → List M.Γ) :
    ∀ (l : List M.K), l.Nodup → ∀ (q : Option M.Q) (ph : Fin 3) (tp : Option M.K) (pd : Bool)
      (h : M.K → M.Γ), ph ≠ 1 → (∀ k ∈ l, h k = default) →
      ∃ ph' tp' pd', ph' ≠ 1 ∧ mlst (infoδ M) (q, ph, tp, pd, h) (segs M l Ls Rs) =
        (q, ph', tp', pd', fun k => if k ∈ l then (Rs k).headI else h k)
  | [], _, q, ph, tp, pd, h, hph, _ => ⟨ph, tp, pd, hph, by simp [segs]⟩
  | k :: l, hnd, q, ph, tp, pd, h, hph, hdef => by
    obtain ⟨tp', pd', hseg⟩ := info_seg M q ph tp pd h hph k (hdef k (by simp)) (Ls k) (Rs k)
    have hnd' := List.nodup_cons.mp hnd
    have hdef' : ∀ k' ∈ l, Function.update h k (Rs k).headI k' = default := by
      intro k' hk'
      have hne : k' ≠ k := fun he => hnd'.1 (he ▸ hk')
      rw [Function.update_of_ne hne]
      exact hdef k' (by simp [hk'])
    obtain ⟨ph'', tp'', pd'', hph'', hrest⟩ :=
      info_segs Ls Rs l hnd'.2 q 2 tp' pd' _ (by decide) hdef'
    refine ⟨ph'', tp'', pd'', hph'', ?_⟩
    have hsplit : segs M (k :: l) Ls Rs = seg M k (Ls k) (Rs k) ++ segs M l Ls Rs := by
      simp [segs]
    rw [hsplit, mlst_append, hseg, hrest]
    congr
    funext k'
    by_cases h1 : k' ∈ l
    · have hne : k' ≠ k := fun he => hnd'.1 (he ▸ h1)
      simp [h1]
    · by_cases h2 : k' = k
      · subst h2
        simp [h1]
      · simp [h1, h2]

/-- **The info transducer reads the state and the head symbols.** -/
theorem info_word (q : M.Q) (Ls Rs : M.K → List M.Γ) :
    (mlst (infoδ M) (info0 M) (word M q Ls Rs)).1 = some q ∧
    (mlst (infoδ M) (info0 M) (word M q Ls Rs)).2.2.2.2 = fun k => (Rs k).headI := by
  unfold word
  rw [mlst_cons]
  have h0 : infoδ M (info0 M) (stSym M q) = (some q, 0, none, false, fun _ => default) := rfl
  rw [h0]
  obtain ⟨ph', tp', pd', -, h⟩ := info_segs M Ls Rs (ks M) (ks_nodup M) (some q) 0 none false
    (fun _ => default) (by decide) (fun _ _ => rfl)
  rw [h]
  refine ⟨rfl, ?_⟩
  funext k
  simp [mem_ks]

/-! ### The edit transducer -/

/-- Whether a move goes left. -/
def isLeft : HeadMove → Bool
  | .left => true
  | _ => false

/-- States of the edit transducer: a phase, the current tape, the cell held back for a left move,
and whether the first cell of the current half is still to be treated. -/
abbrev EdSt := Fin 3 × Option M.K × Option M.Γ × Bool

/-- The initial state of the edit transducer. -/
def ed0 : EdSt M := (0, none, none, false)

/-- Whether the current tape moves left. -/
def tpLeft (mv : M.K → HeadMove) : Option M.K → Bool
  | some k => isLeft (mv k)
  | none => false

/-- The transition of the edit transducer. -/
def edδ (mv : M.K → HeadMove) : EdSt M → Sym M → EdSt M
  | st, Sum.inr (Sum.inl _) => st
  | (ph, tp, hd, _), Sum.inr (Sum.inr k) =>
      if ph = 1 then (2, tp, hd, true) else (1, some k, none, true)
  | (ph, tp, hd, pd), Sum.inl γ =>
      if ph = 1 then
        (if pd = true ∧ tpLeft M mv tp = true then (1, tp, some γ, false) else (1, tp, hd, false))
      else (ph, tp, hd, false)

/-- What the middle separator becomes, for the move of its tape. -/
def midOut (k : M.K) (m : HeadMove) (wk : M.Γ) (hd : Option M.Γ) : List (Sym M) :=
  match m with
  | .left => [sepA M k, sym M (hd.getD default), sym M wk]
  | .right => [sepA M k]
  | .stay => [sepA M k, sym M wk]

/-- What the opening separator becomes. -/
def openOut (k : M.K) (m : HeadMove) (wk : M.Γ) : List (Sym M) :=
  match m with
  | .right => [sepA M k, sym M wk]
  | _ => [sepA M k]

/-- The output of the edit transducer for the action `(q', w, mv)`. -/
def edOut (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) : EdSt M → Sym M → List (Sym M)
  | _, Sum.inr (Sum.inl _) => [stSym M q']
  | (ph, tp, hd, _), Sum.inr (Sum.inr k) =>
      if ph = 1 then
        (match tp with
          | some k0 => midOut M k (mv k0) (w k0) hd
          | none => [sepA M k])
      else openOut M k (mv k) (w k)
  | (ph, tp, _, pd), Sum.inl γ =>
      if ph = 1 then (if pd = true ∧ tpLeft M mv tp = true then [] else [sym M γ])
      else if pd = true then [] else [sym M γ]

/-- The new left part of a tape. -/
def newL (m : HeadMove) (wk : M.Γ) (L : List M.Γ) : List M.Γ :=
  match m with
  | .left => L.tail
  | .right => wk :: L
  | .stay => L

/-- The new head-and-right part of a tape. -/
def newR (m : HeadMove) (wk : M.Γ) (L R : List M.Γ) : List M.Γ :=
  match m with
  | .left => L.headI :: wk :: R.tail
  | .right => R.tail
  | .stay => wk :: R.tail

variable {M}

theorem ed_L_copy (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (k : M.K)
    (hd : Option M.Γ) (L : List M.Γ) :
    mrun (edδ M mv) (edOut M q' w mv) (1, some k, hd, false) (L.map (sym M)) = L.map (sym M) ∧
    mlst (edδ M mv) (1, some k, hd, false) (L.map (sym M)) = (1, some k, hd, false) := by
  induction L with
  | nil => simp
  | cons γ L ih =>
    simp only [List.map_cons, mrun_cons, mlst_cons]
    simp only [edδ, edOut, sym, if_true, Bool.false_eq_true, false_and, if_false]
    rw [ih.1, ih.2]
    exact ⟨rfl, rfl⟩

theorem ed_L (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (k : M.K) (L : List M.Γ) :
    mrun (edδ M mv) (edOut M q' w mv) (1, some k, none, true) (L.map (sym M)) =
      (if isLeft (mv k) then L.tail else L).map (sym M) ∧
    ∃ pd', mlst (edδ M mv) (1, some k, none, true) (L.map (sym M)) =
      (1, some k, if isLeft (mv k) then L.head? else none, pd') := by
  cases L with
  | nil =>
    refine ⟨by split <;> rfl, true, ?_⟩
    split <;> rfl
  | cons γ L =>
    simp only [List.map_cons, mrun_cons, mlst_cons]
    by_cases hl : isLeft (mv k) = true
    · have e1 : edδ M mv (1, some k, none, true) (sym M γ) = (1, some k, some γ, false) := by
        simp [edδ, sym, tpLeft, hl]
      have e2 : edOut M q' w mv (1, some k, none, true) (sym M γ) = [] := by
        simp [edOut, sym, tpLeft, hl]
      rw [e1, e2, (ed_L_copy q' w mv k (some γ) L).1, (ed_L_copy q' w mv k (some γ) L).2]
      simp [hl]
    · have e1 : edδ M mv (1, some k, none, true) (sym M γ) = (1, some k, none, false) := by
        simp [edδ, sym, tpLeft, hl]
      have e2 : edOut M q' w mv (1, some k, none, true) (sym M γ) = [sym M γ] := by
        simp [edOut, sym, tpLeft, hl]
      rw [e1, e2, (ed_L_copy q' w mv k none L).1, (ed_L_copy q' w mv k none L).2]
      simp [hl]

theorem ed_R_copy (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (tp : Option M.K)
    (hd : Option M.Γ) (R : List M.Γ) :
    mrun (edδ M mv) (edOut M q' w mv) (2, tp, hd, false) (R.map (sym M)) = R.map (sym M) ∧
    mlst (edδ M mv) (2, tp, hd, false) (R.map (sym M)) = (2, tp, hd, false) := by
  induction R with
  | nil => simp
  | cons γ R ih =>
    simp only [List.map_cons, mrun_cons, mlst_cons]
    have e1 : edδ M mv (2, tp, hd, false) (sym M γ) = (2, tp, hd, false) := by
      simp [edδ, sym]
    have e2 : edOut M q' w mv (2, tp, hd, false) (sym M γ) = [sym M γ] := by
      simp [edOut, sym]
    rw [e1, e2, ih.1, ih.2]
    exact ⟨rfl, rfl⟩

theorem ed_R (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (tp : Option M.K)
    (hd : Option M.Γ) (R : List M.Γ) :
    mrun (edδ M mv) (edOut M q' w mv) (2, tp, hd, true) (R.map (sym M)) = R.tail.map (sym M) ∧
    ∃ pd', mlst (edδ M mv) (2, tp, hd, true) (R.map (sym M)) = (2, tp, hd, pd') := by
  cases R with
  | nil => exact ⟨rfl, true, rfl⟩
  | cons γ R =>
    simp only [List.map_cons, mrun_cons, mlst_cons, List.tail_cons]
    have e1 : edδ M mv (2, tp, hd, true) (sym M γ) = (2, tp, hd, false) := by
      simp [edδ, sym]
    have e2 : edOut M q' w mv (2, tp, hd, true) (sym M γ) = [] := by
      simp [edOut, sym]
    rw [e1, e2, (ed_R_copy q' w mv tp hd R).1, (ed_R_copy q' w mv tp hd R).2]
    exact ⟨rfl, false, rfl⟩

theorem ed_seg (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (st : EdSt M) (hst : st.1 ≠ 1)
    (k : M.K) (L R : List M.Γ) :
    mrun (edδ M mv) (edOut M q' w mv) st (seg M k L R) =
      seg M k (newL M (mv k) (w k) L) (newR M (mv k) (w k) L R) ∧
    (mlst (edδ M mv) st (seg M k L R)).1 = 2 := by
  obtain ⟨ph, tp, hd, pd⟩ := st
  change ph ≠ 1 at hst
  unfold seg
  rw [mrun_cons, mlst_cons, mrun_append, mlst_append]
  have e1 : edδ M mv (ph, tp, hd, pd) (sepA M k) = (1, some k, none, true) := by
    simp [edδ, sepA, hst]
  have e2 : edOut M q' w mv (ph, tp, hd, pd) (sepA M k) = openOut M k (mv k) (w k) := by
    simp [edOut, sepA, hst]
  rw [e1, e2]
  obtain ⟨hL, pd', hLs⟩ := ed_L q' w mv k L
  rw [hL, hLs, mrun_cons, mlst_cons]
  have e3 : edδ M mv (1, some k, if isLeft (mv k) then L.head? else none, pd') (sepA M k) =
      (2, some k, if isLeft (mv k) then L.head? else none, true) := by
    simp [edδ, sepA]
  have e4 : edOut M q' w mv (1, some k, if isLeft (mv k) then L.head? else none, pd')
      (sepA M k) = midOut M k (mv k) (w k) (if isLeft (mv k) then L.head? else none) := by
    simp [edOut, sepA]
  rw [e3, e4]
  obtain ⟨hR, pd'', hRs⟩ := ed_R q' w mv (some k)
    (if isLeft (mv k) then L.head? else none) R
  rw [hR, hRs]
  refine ⟨?_, rfl⟩
  cases hm : mv k with
  | left =>
    simp only [isLeft, if_true, openOut, midOut, newL, newR, List.map_cons, List.cons_append,
      List.nil_append]
    cases L with
    | nil => rfl
    | cons γ L => rfl
  | right =>
    simp [isLeft, openOut, midOut, newL, newR]
  | stay =>
    simp [isLeft, openOut, midOut, newL, newR]

theorem ed_segs (q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (Ls Rs : M.K → List M.Γ) :
    ∀ (l : List M.K) (st : EdSt M), st.1 ≠ 1 →
      mrun (edδ M mv) (edOut M q' w mv) st (segs M l Ls Rs) =
        segs M l (fun k => newL M (mv k) (w k) (Ls k)) (fun k => newR M (mv k) (w k) (Ls k) (Rs k))
  | [], _, _ => rfl
  | k :: l, st, hst => by
    have hsplit : ∀ (Ls' Rs' : M.K → List M.Γ),
        segs M (k :: l) Ls' Rs' = seg M k (Ls' k) (Rs' k) ++ segs M l Ls' Rs' := by
      intro Ls' Rs'
      simp [segs]
    rw [hsplit, hsplit, mrun_append, (ed_seg q' w mv st hst k (Ls k) (Rs k)).1]
    rw [ed_segs q' w mv Ls Rs l _ (by rw [(ed_seg q' w mv st hst k (Ls k) (Rs k)).2]; decide)]

/-- **The edit transducer computes the word of the next configuration.** -/
theorem edit_word (q q' : M.Q) (w : M.K → M.Γ) (mv : M.K → HeadMove) (Ls Rs : M.K → List M.Γ) :
    mrun (edδ M mv) (edOut M q' w mv) (ed0 M) (word M q Ls Rs) =
      word M q' (fun k => newL M (mv k) (w k) (Ls k))
        (fun k => newR M (mv k) (w k) (Ls k) (Rs k)) := by
  unfold word
  rw [mrun_cons]
  have e1 : edδ M mv (ed0 M) (stSym M q) = ed0 M := rfl
  have e2 : edOut M q' w mv (ed0 M) (stSym M q) = [stSym M q'] := rfl
  rw [e1, e2, ed_segs q' w mv Ls Rs (ks M) (ed0 M) (by simp [ed0])]
  rfl

/-! ### The next configuration -/

theorem tape_update (m : HeadMove) (wk : M.Γ) (L R : List M.Γ) :
    m.apply ((tapeOf M L R).write wk) = tapeOf M (newL M m wk L) (newR M m wk L R) := by
  cases m with
  | left =>
    simp [HeadMove.apply, tapeOf, newL, newR, Turing.Tape.write, Turing.Tape.move,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]
  | right =>
    simp [HeadMove.apply, tapeOf, newL, newR, Turing.Tape.write, Turing.Tape.move,
      Turing.ListBlank.head_mk, Turing.ListBlank.tail_mk, Turing.ListBlank.cons_mk]
  | stay =>
    simp [HeadMove.apply, tapeOf, newL, newR, Turing.Tape.write]

/-- **The edited word represents the updated configuration.** -/
theorem rep_update {u : List (Sym M)} {c : M.Cfg} (h : Rep M u c) (q' : M.Q)
    (w : M.K → M.Γ) (mv : M.K → HeadMove) :
    Rep M (mrun (edδ M mv) (edOut M q' w mv) (ed0 M) u) (multiTapeUpdate c q' w mv) := by
  obtain ⟨Ls, Rs, ht, rfl⟩ := h
  refine ⟨fun k => newL M (mv k) (w k) (Ls k), fun k => newR M (mv k) (w k) (Ls k) (Rs k),
    fun k => ?_, edit_word c.q q' w mv Ls Rs⟩
  change (mv k).apply ((c.tapes k).write (w k)) = _
  rw [ht k, tape_update]

theorem rep_heads {u : List (Sym M)} {c : M.Cfg} (h : Rep M u c) :
    (mlst (infoδ M) (info0 M) u).1 = some c.q ∧
    (mlst (infoδ M) (info0 M) u).2.2.2.2 = fun k => (c.tapes k).head := by
  obtain ⟨Ls, Rs, ht, rfl⟩ := h
  obtain ⟨h1, h2⟩ := info_word M c.q Ls Rs
  refine ⟨h1, ?_⟩
  rw [h2]
  funext k
  rw [ht k]
  rfl

/-! ### Lengths -/

theorem length_seg (k : M.K) (L R : List M.Γ) : (seg M k L R).length = L.length + R.length + 2 := by
  simp [seg]
  omega

theorem length_segs (l : List M.K) (Ls Rs : M.K → List M.Γ) :
    (segs M l Ls Rs).length = (l.map fun k => (Ls k).length + (Rs k).length + 2).sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [segs, List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, length_seg]

theorem length_new_le (m : HeadMove) (wk : M.Γ) (L R : List M.Γ) :
    (newL M m wk L).length + (newR M m wk L R).length ≤ L.length + R.length + 2 := by
  cases m <;> simp [newL, newR] <;> omega

theorem length_segs_new_le (l : List M.K) (mv : M.K → HeadMove) (w : M.K → M.Γ)
    (Ls Rs : M.K → List M.Γ) :
    (segs M l (fun k => newL M (mv k) (w k) (Ls k))
      (fun k => newR M (mv k) (w k) (Ls k) (Rs k))).length ≤
      (segs M l Ls Rs).length + 2 * l.length := by
  induction l with
  | nil => simp [segs]
  | cons k l ih =>
    have hsplit : ∀ (Ls' Rs' : M.K → List M.Γ),
        segs M (k :: l) Ls' Rs' = seg M k (Ls' k) (Rs' k) ++ segs M l Ls' Rs' := by
      intro Ls' Rs'
      simp [segs]
    rw [hsplit, hsplit, List.length_append, List.length_append, length_seg, length_seg]
    have := length_new_le (M := M) (mv k) (w k) (Ls k) (Rs k)
    simp only [List.length_cons]
    omega

theorem length_update_le {u : List (Sym M)} {c : M.Cfg} (h : Rep M u c) (q' : M.Q)
    (w : M.K → M.Γ) (mv : M.K → HeadMove) :
    (mrun (edδ M mv) (edOut M q' w mv) (ed0 M) u).length ≤ u.length + 2 * Fintype.card M.K := by
  obtain ⟨Ls, Rs, -, rfl⟩ := h
  rw [edit_word]
  unfold word
  have h1 := length_segs_new_le (ks M) mv w Ls Rs
  have h2 : (ks M).length = Fintype.card M.K := by
    simp [ks, Finset.length_toList]
  simp only [List.length_cons]
  omega

end MultiTapeCobham

end Complexity
