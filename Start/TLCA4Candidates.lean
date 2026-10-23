import Start.TLCA4QUnfold

/-!
# TLCA open problem 4: the length-7 candidates of the spine search
(row M20-TLCA4-BETAETA; series V, big round, run 3, item A2)

The bounded spine search (experiment, not Lean-checked; `docs/goal/evidence/M20-TLCA4-BETAETA.md`)
found 14 polynomials whose `x`-spine reaches the cap: `T` (length 3), `Q` (length 5) and twelve of
length 7.  This module records them and their relation to `T = M ∘ BM ∘ B` in Lean.

* `WEq.actList` — congruence of the λ-action;
* **`factor_T`** — `(C ∘ T ∘ F) x =w C (T (F x))` for monomial lists `C`, `F`;
* `hit1` … `hit12` — the twelve length-7 hits as polynomials;
* **`hit1_weq`**, `hit2_weq`, `hit3_weq`, `hit4_weq`, `hit11_weq`, `hit12_weq` — six of them are
  `C ∘ T ∘ F`:
  `hit1 = M∘M∘B∘T∘B`, `hit2 = M∘M∘T∘B∘B = M∘Q∘B` (`Q₂` of the family `Q_k = M∘Q_{k-1}∘B`),
  `hit3 = M∘T∘BM∘BB∘B`, `hit4 = M∘T∘B²M∘BB∘B`, `hit11 = T∘T∘B`, `hit12 = M∘BM∘T∘B∘B`;
* `hit2_weq_Q` — `hit2 x =w M (Q (B x))`;
* `hit5_weq` … `hit10_weq` — the other six have no factor `T`: they unfold to
  `M (M (BM (G x)))` (`hit5`–`hit9`) and `M (M (B²M (G x)))` (`hit10`), with `G` a composite of
  `B`, `BB`, `B²B`, `BM`, `B²M`, `B³M`.
-/

set_option autoImplicit false

namespace TLCA4

open Tm

theorem WEq.actList : ∀ (C : List Mono) {u v : Tm}, WEq u v → WEq (TLCA4.actList C u) (TLCA4.actList C v)
  | [], _, _, h => h
  | _ :: C, _, _, h => Tm.WEq.appR _ (WEq.actList C h)

/-- The monomials of `T = M ∘ BM ∘ B`. -/
def tTList : List Mono := [⟨0, .M⟩, ⟨1, .M⟩, ⟨0, .B⟩]

/-- **`(C ∘ T ∘ F) x =w C (T (F x))`.** -/
theorem factor_T (C F : List Mono) (x : Tm) :
    WEq (actList (C ++ tTList ++ F) x) (actList C (app tT (actList F x))) := by
  rw [actList_append, actList_append]
  refine WEq.actList C ?_
  rw [tT_eq_poly]
  exact (polyTm_action _ _ _).symm

/-- The polynomial of a nonempty monomial list. -/
def polyOf : List Mono → Tm
  | [] => I
  | m :: ps => polyTm m ps

theorem polyOf_action (m : Mono) (ps : List Mono) (x : Tm) :
    WEq (app (polyOf (m :: ps)) x) (actList (m :: ps) x) := polyTm_action m ps x

/-! ### The twelve length-7 hits -/

def mM : Mono := ⟨0, .M⟩
def mB : Mono := ⟨0, .B⟩
def mBM : Mono := ⟨1, .M⟩
def mB2M : Mono := ⟨2, .M⟩
def mB3M : Mono := ⟨3, .M⟩
def mBB : Mono := ⟨1, .B⟩
def mB2B : Mono := ⟨2, .B⟩

def hit1 : List Mono := [mM, mM, mB, mM, mBM, mB, mB]
def hit2 : List Mono := [mM, mM, mM, mBM, mB, mB, mB]
def hit3 : List Mono := [mM, mM, mBM, mB, mBM, mBB, mB]
def hit4 : List Mono := [mM, mM, mBM, mB, mB2M, mBB, mB]
def hit5 : List Mono := [mM, mM, mBM, mBB, mBM, mB, mB]
def hit6 : List Mono := [mM, mM, mBM, mB2M, mB, mBB, mB]
def hit7 : List Mono := [mM, mM, mBM, mB2M, mB2B, mB, mB]
def hit8 : List Mono := [mM, mM, mBM, mB3M, mB, mBB, mB]
def hit9 : List Mono := [mM, mM, mBM, mB3M, mB2B, mB, mB]
def hit10 : List Mono := [mM, mM, mB2M, mBB, mBM, mB, mB]
def hit11 : List Mono := [mM, mBM, mB, mM, mBM, mB, mB]
def hit12 : List Mono := [mM, mBM, mM, mBM, mB, mB, mB]

/-! ### Six hits factor through `T` -/

theorem hit1_weq (x : Tm) :
    WEq (app (polyOf hit1) x) (actList [mM, mM, mB] (app tT (actList [mB] x))) :=
  (polyOf_action _ _ x).trans (factor_T [mM, mM, mB] [mB] x)

theorem hit2_weq (x : Tm) :
    WEq (app (polyOf hit2) x) (actList [mM, mM] (app tT (actList [mB, mB] x))) :=
  (polyOf_action _ _ x).trans (factor_T [mM, mM] [mB, mB] x)

theorem hit3_weq (x : Tm) :
    WEq (app (polyOf hit3) x) (actList [mM] (app tT (actList [mBM, mBB, mB] x))) :=
  (polyOf_action _ _ x).trans (factor_T [mM] [mBM, mBB, mB] x)

theorem hit4_weq (x : Tm) :
    WEq (app (polyOf hit4) x) (actList [mM] (app tT (actList [mB2M, mBB, mB] x))) :=
  (polyOf_action _ _ x).trans (factor_T [mM] [mB2M, mBB, mB] x)

theorem hit11_weq (x : Tm) :
    WEq (app (polyOf hit11) x) (app tT (actList [mM, mBM, mB, mB] x)) :=
  (polyOf_action _ _ x).trans (factor_T [] [mM, mBM, mB, mB] x)

/-- `hit11 = T ∘ T ∘ B`: `hit11 x =w T (T (B x))`. -/
theorem hit11_weq_TT (x : Tm) : WEq (app (polyOf hit11) x) (app tT (app tT (app B x))) := by
  refine (hit11_weq x).trans (Tm.WEq.appR _ ?_)
  exact factor_T [] [mB] x

theorem hit12_weq (x : Tm) :
    WEq (app (polyOf hit12) x) (actList [mM, mBM] (app tT (actList [mB, mB] x))) :=
  (polyOf_action _ _ x).trans (factor_T [mM, mBM] [mB, mB] x)

/-- `hit2 = M ∘ Q ∘ B`: `hit2 x =w M (Q (B x))`. -/
theorem hit2_weq_Q (x : Tm) : WEq (app (polyOf hit2) x) (app M (app tQ (app B x))) := by
  refine (polyOf_action _ _ x).trans (Tm.WEq.appR _ ?_)
  have h := polyTm_action ⟨0, .M⟩ [⟨0, .M⟩, ⟨1, .M⟩, ⟨0, .B⟩, ⟨0, .B⟩] (app B x)
  rw [← tQ_eq_poly] at h
  exact h.symm

/-! ### Six hits without a factor `T` -/

theorem hit_unfold (L : List Mono) (hL : L ≠ []) (x : Tm) :
    WEq (app (polyOf L) x) (actList L x) := by
  cases L with
  | nil => exact absurd rfl hL
  | cons m ps => exact polyOf_action m ps x

theorem hit5_weq (x : Tm) : WEq (app (polyOf hit5) x) (actList hit5 x) :=
  hit_unfold _ (by simp [hit5]) x
theorem hit6_weq (x : Tm) : WEq (app (polyOf hit6) x) (actList hit6 x) :=
  hit_unfold _ (by simp [hit6]) x
theorem hit7_weq (x : Tm) : WEq (app (polyOf hit7) x) (actList hit7 x) :=
  hit_unfold _ (by simp [hit7]) x
theorem hit8_weq (x : Tm) : WEq (app (polyOf hit8) x) (actList hit8 x) :=
  hit_unfold _ (by simp [hit8]) x
theorem hit9_weq (x : Tm) : WEq (app (polyOf hit9) x) (actList hit9 x) :=
  hit_unfold _ (by simp [hit9]) x
theorem hit10_weq (x : Tm) : WEq (app (polyOf hit10) x) (actList hit10 x) :=
  hit_unfold _ (by simp [hit10]) x

end TLCA4
