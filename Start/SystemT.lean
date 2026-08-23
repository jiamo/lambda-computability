/-
Gödel's System T: typing, β/ι-reduction, and **strong normalization**.

This is the typed counterpart of the untyped development, and the setting in which Gödel's
Dialectica functionals live.  Building on the syntax of `Start/SystemTSyntax.lean`:

* `GodelT.Ty` — the types `nat` and `A ⇒ B`;
* `GodelT.Typing` — the six typing rules, including the recursor
  `natrec : A → (nat → A → A) → nat → A`;
* `GodelT.step` — β-reduction together with the two ι-rules for the recursor;
* `GodelT.SN` — strong normalization, `Acc` of the reverse of `step`;
* `GodelT.Red` — Tait's reducibility predicate.  At an arrow type it is the usual function space;
  at `nat` it is the *inductively generated* candidate `GodelT.RedNat`, which is what makes the
  recursor case of the fundamental lemma go through;
* `GodelT.cr` — the reducibility candidate conditions CR1, CR2, CR3;
* `GodelT.red_natrec` — reducibility of the recursor, by induction on the `RedNat` derivation with
  nested inductions on the strong normalization of the two other arguments;
* `GodelT.sn_of_typing` — **strong normalization: every typable term of System T is strongly
  normalizing**, hence (`GodelT.hasNormalForm_of_typing`) has a normal form.

Because reduction includes the ι-rules, this is a genuinely stronger statement than strong
normalization for the simply typed calculus (`Start/SimpleTypes.lean`): System T defines every
provably total function of first-order arithmetic, so no primitive recursive bound on reduction
lengths is available.
-/

import Start.SystemTSyntax

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace GodelT

------------------------------------------------------------------------
-- Types and typing
------------------------------------------------------------------------

/-- The types of System T. -/
inductive Ty where
  | nat : Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

/-- Typing: contexts list the types of the free variables, index `0` first. -/
inductive Typing : List Ty → Tm → Ty → Prop
  | var {Γ : List Ty} {i : ℕ} {A : Ty} : Γ[i]? = some A → Typing Γ (Tm.var i) A
  | app {Γ : List Ty} {a b : Tm} {A B : Ty} :
      Typing Γ a (Ty.arrow A B) → Typing Γ b A → Typing Γ (Tm.app a b) B
  | lam {Γ : List Ty} {t : Tm} {A B : Ty} :
      Typing (A :: Γ) t B → Typing Γ (Tm.lam t) (Ty.arrow A B)
  | zero {Γ : List Ty} : Typing Γ Tm.zero Ty.nat
  | succ {Γ : List Ty} {t : Tm} : Typing Γ t Ty.nat → Typing Γ (Tm.succ t) Ty.nat
  | natrec {Γ : List Ty} {z f n : Tm} {A : Ty} :
      Typing Γ z A → Typing Γ f (Ty.arrow Ty.nat (Ty.arrow A A)) → Typing Γ n Ty.nat →
      Typing Γ (Tm.natrec z f n) A

------------------------------------------------------------------------
-- Reduction
------------------------------------------------------------------------

/-- β-reduction together with the two ι-rules of the recursor. -/
inductive step : Tm → Tm → Prop
  | beta (a b : Tm) : step (Tm.app (Tm.lam a) b) (subst b 0 a)
  | appL (a a' b : Tm) : step a a' → step (Tm.app a b) (Tm.app a' b)
  | appR (a b b' : Tm) : step b b' → step (Tm.app a b) (Tm.app a b')
  | lam (t t' : Tm) : step t t' → step (Tm.lam t) (Tm.lam t')
  | succ (t t' : Tm) : step t t' → step (Tm.succ t) (Tm.succ t')
  | recZero (z f : Tm) : step (Tm.natrec z f Tm.zero) z
  | recSucc (z f n : Tm) :
      step (Tm.natrec z f (Tm.succ n)) (Tm.app (Tm.app f n) (Tm.natrec z f n))
  | recL (z z' f n : Tm) : step z z' → step (Tm.natrec z f n) (Tm.natrec z' f n)
  | recM (z f f' n : Tm) : step f f' → step (Tm.natrec z f n) (Tm.natrec z f' n)
  | recR (z f n n' : Tm) : step n n' → step (Tm.natrec z f n) (Tm.natrec z f n')

/-- Reduction is a congruence for substitution. -/
theorem step_subst {t t' : Tm} (h : step t t') :
    ∀ (v : Tm) (x : ℕ), step (subst v x t) (subst v x t') := by
  induction h with
  | beta a b =>
      intro v x
      have hb := step.beta (subst (lift 1 0 v) (x + 1) a) (subst v x b)
      simpa [subst, subst_subst_zero a v b x] using hb
  | appL a a' b _ ih => intro v x; exact step.appL _ _ _ (ih v x)
  | appR a b b' _ ih => intro v x; exact step.appR _ _ _ (ih v x)
  | lam t t' _ ih => intro v x; exact step.lam _ _ (ih (lift 1 0 v) (x + 1))
  | succ t t' _ ih => intro v x; exact step.succ _ _ (ih v x)
  | recZero z f => intro v x; exact step.recZero _ _
  | recSucc z f n => intro v x; exact step.recSucc _ _ _
  | recL z z' f n _ ih => intro v x; exact step.recL _ _ _ _ (ih v x)
  | recM z f f' n _ ih => intro v x; exact step.recM _ _ _ _ (ih v x)
  | recR z f n n' _ ih => intro v x; exact step.recR _ _ _ _ (ih v x)

------------------------------------------------------------------------
-- Strong normalization
------------------------------------------------------------------------

/-- Strong normalization. -/
def SN (t : Tm) : Prop := Acc (fun a b => step b a) t

theorem SN.step {t t' : Tm} (h : SN t) (hs : GodelT.step t t') : SN t' := h.inv hs

theorem SN.intro {t : Tm} (h : ∀ t', GodelT.step t t' → SN t') : SN t := Acc.intro t h

theorem not_step_var {i : ℕ} {t : Tm} : ¬ step (Tm.var i) t := by intro h; cases h

theorem not_step_zero {t : Tm} : ¬ step Tm.zero t := by intro h; cases h

theorem sn_var (i : ℕ) : SN (Tm.var i) := SN.intro fun _ h => absurd h not_step_var

theorem sn_zero : SN Tm.zero := SN.intro fun _ h => absurd h not_step_zero

/-- If a step-preserving map sends `t` to a strongly normalizing term, `t` is strongly
normalizing. -/
theorem sn_of_map (F : Tm → Tm) (hF : ∀ a b, step a b → step (F a) (F b)) :
    ∀ {s : Tm}, SN s → ∀ t : Tm, F t = s → SN t := by
  intro s hs
  induction hs with
  | intro s _ ih =>
      intro t ht
      exact SN.intro fun t' hstep => ih (F t') (by rw [← ht]; exact hF t t' hstep) t' rfl

theorem sn_of_sn_subst {v : Tm} {x : ℕ} {t : Tm} (h : SN (subst v x t)) : SN t :=
  sn_of_map (subst v x) (fun _ _ hs => step_subst hs v x) h t rfl

theorem sn_app_left {t u : Tm} (h : SN (Tm.app t u)) : SN t :=
  sn_of_map (fun a => Tm.app a u) (fun _ _ hs => step.appL _ _ _ hs) h t rfl

theorem sn_succ {t : Tm} (h : SN t) : SN (Tm.succ t) := by
  induction h with
  | intro t _ ih =>
      refine SN.intro fun w hw => ?_
      cases hw with
      | succ _ t' hs => exact ih t' hs

------------------------------------------------------------------------
-- Neutral terms
------------------------------------------------------------------------

/-- A term is neutral when it is neither an abstraction nor a numeral constructor: no reduction
rule fires because of its own head. -/
def Neutral : Tm → Prop
  | Tm.lam _ => False
  | Tm.zero => False
  | Tm.succ _ => False
  | _ => True

theorem neutral_var (i : ℕ) : Neutral (Tm.var i) := trivial
theorem neutral_app (a b : Tm) : Neutral (Tm.app a b) := trivial
theorem neutral_natrec (z f n : Tm) : Neutral (Tm.natrec z f n) := trivial

------------------------------------------------------------------------
-- Reducibility
------------------------------------------------------------------------

/-- The reducibility candidate at type `nat`, generated inductively by the numerals and by the
neutral terms all of whose reducts are reducible. -/
inductive RedNat : Tm → Prop
  | zero : RedNat Tm.zero
  | succ {t : Tm} : RedNat t → RedNat (Tm.succ t)
  | ne {t : Tm} : Neutral t → (∀ t', step t t' → RedNat t') → RedNat t

theorem RedNat.sn {t : Tm} (h : RedNat t) : SN t := by
  induction h with
  | zero => exact sn_zero
  | succ _ ih => exact sn_succ ih
  | ne _ _ ih => exact SN.intro ih

theorem RedNat.step {t t' : Tm} (h : RedNat t) (hs : GodelT.step t t') : RedNat t' := by
  induction h generalizing t' with
  | zero => exact absurd hs not_step_zero
  | @succ m _ ih =>
      cases hs with
      | succ _ m' hm => exact RedNat.succ (ih hm)
  | ne _ hall _ => exact hall t' hs

/-- Tait's reducibility predicate. -/
def Red : Ty → Tm → Prop
  | Ty.nat, t => RedNat t
  | Ty.arrow A B, t => ∀ u : Tm, Red A u → Red B (Tm.app t u)

/-- The reducibility candidate conditions CR1, CR2, CR3. -/
theorem cr (A : Ty) :
    (∀ t, Red A t → SN t) ∧
    (∀ t t', Red A t → step t t' → Red A t') ∧
    (∀ t, Neutral t → (∀ t', step t t' → Red A t') → Red A t) := by
  induction A with
  | nat =>
      exact ⟨fun _ h => h.sn, fun _ _ h hs => h.step hs, fun _ hn h => RedNat.ne hn h⟩
  | arrow A B ihA ihB =>
      obtain ⟨ihA1, ihA2, ihA3⟩ := ihA
      obtain ⟨ihB1, ihB2, ihB3⟩ := ihB
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        have hv : Red A (Tm.var 0) :=
          ihA3 _ (neutral_var 0) fun _ h => absurd h not_step_var
        exact sn_app_left (ihB1 _ (ht _ hv))
      · intro t t' ht hs u hu
        exact ihB2 _ _ (ht u hu) (step.appL _ _ _ hs)
      · intro t hn h u hu
        have hsn : SN u := ihA1 u hu
        induction hsn with
        | intro u hacc ihu =>
            refine ihB3 _ (neutral_app t u) fun w hw => ?_
            cases hw with
            | beta a b => exact hn.elim
            | appL _ t' _ hstep => exact h t' hstep u hu
            | appR _ _ u' hstep => exact ihu u' hstep (ihA2 _ _ hu hstep)

theorem cr1 (A : Ty) {t : Tm} (h : Red A t) : SN t := (cr A).1 t h

theorem cr2 (A : Ty) {t t' : Tm} (h : Red A t) (hs : step t t') : Red A t' :=
  (cr A).2.1 t t' h hs

theorem cr3 (A : Ty) {t : Tm} (hn : Neutral t) (h : ∀ t', step t t' → Red A t') : Red A t :=
  (cr A).2.2 t hn h

theorem red_var (A : Ty) (i : ℕ) : Red A (Tm.var i) :=
  cr3 A (neutral_var i) fun _ h => absurd h not_step_var

------------------------------------------------------------------------
-- The abstraction lemma
------------------------------------------------------------------------

theorem red_app_lam_aux (A B : Ty) :
    ∀ s : Tm, SN s → (∀ v, Red A v → Red B (subst v 0 s)) →
      ∀ u : Tm, SN u → Red A u → Red B (Tm.app (Tm.lam s) u) := by
  intro s hs
  induction hs with
  | intro s _ ihs =>
      intro hsub u hu
      induction hu with
      | intro u hacc ihu =>
          intro hru
          refine cr3 B (neutral_app _ _) fun w hw => ?_
          cases hw with
          | beta a b => exact hsub u hru
          | appL _ t₁' _ hstep =>
              cases hstep with
              | lam _ s' hs' =>
                  exact ihs s' hs' (fun v hv => cr2 B (hsub v hv) (step_subst hs' v 0)) u
                    (Acc.intro u hacc) hru
          | appR _ _ u' hstep => exact ihu u' hstep (cr2 A hru hstep)

theorem red_lam {A B : Ty} {s : Tm} (h : ∀ v, Red A v → Red B (subst v 0 s)) :
    Red (Ty.arrow A B) (Tm.lam s) := by
  intro u hu
  have hsns : SN s := sn_of_sn_subst (cr1 B (h _ (red_var A 0)))
  exact red_app_lam_aux A B s hsns h u (cr1 A hu) hu

------------------------------------------------------------------------
-- Reducibility of the recursor
------------------------------------------------------------------------

theorem red_natrec_zero (A : Ty) :
    ∀ z, SN z → ∀ f, SN f → Red A z → Red (Ty.arrow Ty.nat (Ty.arrow A A)) f →
      Red A (Tm.natrec z f Tm.zero) := by
  intro z hz
  induction hz with
  | intro z hzacc ihz =>
      intro f hf
      induction hf with
      | intro f hfacc ihf =>
          intro hrz hrf
          refine cr3 A (neutral_natrec _ _ _) fun w hw => ?_
          cases hw with
          | recZero _ _ => exact hrz
          | recL _ z' _ _ hs =>
              exact ihz z' hs f (Acc.intro f hfacc) (cr2 A hrz hs) hrf
          | recM _ _ f' _ hs =>
              exact ihf f' hs hrz (cr2 _ hrf hs)
          | recR _ _ _ n' hs => exact absurd hs not_step_zero

theorem red_natrec_succ (A : Ty) :
    ∀ z, SN z → ∀ f, SN f → ∀ m, SN m →
      Red A z → Red (Ty.arrow Ty.nat (Ty.arrow A A)) f → RedNat m →
      Red A (Tm.natrec z f m) → Red A (Tm.natrec z f (Tm.succ m)) := by
  intro z hz
  induction hz with
  | intro z hzacc ihz =>
      intro f hf
      induction hf with
      | intro f hfacc ihf =>
          intro m hm
          induction hm with
          | intro m hmacc ihm =>
              intro hrz hrf hnm hrec
              refine cr3 A (neutral_natrec _ _ _) fun w hw => ?_
              cases hw with
              | recSucc _ _ _ => exact hrf m hnm _ hrec
              | recL _ z' _ _ hs =>
                  exact ihz z' hs f (Acc.intro f hfacc) m (Acc.intro m hmacc)
                    (cr2 A hrz hs) hrf hnm (cr2 A hrec (step.recL _ _ _ _ hs))
              | recM _ _ f' _ hs =>
                  exact ihf f' hs m (Acc.intro m hmacc) hrz (cr2 _ hrf hs) hnm
                    (cr2 A hrec (step.recM _ _ _ _ hs))
              | recR _ _ _ n' hs =>
                  cases hs with
                  | succ _ m' hm' =>
                      exact ihm m' hm' hrz hrf (hnm.step hm')
                        (cr2 A hrec (step.recR _ _ _ _ hm'))

theorem red_natrec_ne (A : Ty) (n : Tm) (hne : Neutral n)
    (hrec : ∀ z' f' n', Red A z' → Red (Ty.arrow Ty.nat (Ty.arrow A A)) f' → step n n' →
      Red A (Tm.natrec z' f' n')) :
    ∀ z, SN z → ∀ f, SN f → Red A z → Red (Ty.arrow Ty.nat (Ty.arrow A A)) f →
      Red A (Tm.natrec z f n) := by
  intro z hz
  induction hz with
  | intro z hzacc ihz =>
      intro f hf
      induction hf with
      | intro f hfacc ihf =>
          intro hrz hrf
          refine cr3 A (neutral_natrec _ _ _) fun w hw => ?_
          cases hw with
          | recZero _ _ => exact hne.elim
          | recSucc _ _ _ => exact hne.elim
          | recL _ z' _ _ hs =>
              exact ihz z' hs f (Acc.intro f hfacc) (cr2 A hrz hs) hrf
          | recM _ _ f' _ hs => exact ihf f' hs hrz (cr2 _ hrf hs)
          | recR _ _ _ n' hs => exact hrec z f n' hrz hrf hs

/-- **The recursor is reducible.** -/
theorem red_natrec (A : Ty) : ∀ n, RedNat n → ∀ z f, Red A z →
    Red (Ty.arrow Ty.nat (Ty.arrow A A)) f → Red A (Tm.natrec z f n) := by
  intro n hn
  induction hn with
  | zero =>
      intro z f hz hf
      exact red_natrec_zero A z (cr1 A hz) f (cr1 _ hf) hz hf
  | @succ m hm ih =>
      intro z f hz hf
      exact red_natrec_succ A z (cr1 A hz) f (cr1 _ hf) m hm.sn hz hf hm (ih z f hz hf)
  | @ne t hne _ ih =>
      intro z f hz hf
      exact red_natrec_ne A t hne (fun z' f' n' hz' hf' hs => ih n' hs z' f' hz' hf')
        z (cr1 A hz) f (cr1 _ hf) hz hf

------------------------------------------------------------------------
-- The fundamental lemma and strong normalization
------------------------------------------------------------------------

/-- **Fundamental lemma of the reducibility method for System T.** -/
theorem red_substEnv {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    ∀ u : ℕ → Tm, (∀ i A', Γ[i]? = some A' → Red A' (u i)) → Red A (substEnv u t) := by
  induction h with
  | var hi => intro u hu; exact hu _ _ hi
  | app _ _ iha ihb => intro u hu; exact iha u hu _ (ihb u hu)
  | @lam Γ t A B _ ih =>
      intro u hu
      have hsub : substEnv u (Tm.lam t) = Tm.lam (substEnv (envCons u) t) := rfl
      rw [hsub]
      refine red_lam fun v hv => ?_
      rw [subst_zero_substEnv]
      refine ih (envScons v u) fun i A' hi => ?_
      cases i with
      | zero =>
          have hA : A = A' := by simpa using hi
          subst hA
          exact hv
      | succ i => exact hu i A' (by simpa using hi)
  | zero => intro u _; exact RedNat.zero
  | succ _ ih => intro u hu; exact RedNat.succ (ih u hu)
  | @natrec Γ z f n A _ _ _ ihz ihf ihn =>
      intro u hu
      exact red_natrec A (substEnv u n) (ihn u hu) (substEnv u z) (substEnv u f)
        (ihz u hu) (ihf u hu)

/-- **Strong normalization for System T.** -/
theorem sn_of_typing {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) : SN t := by
  have := red_substEnv h (fun k => Tm.var k) fun i A' _ => red_var A' i
  rw [substEnv_var_id] at this
  exact cr1 A this

------------------------------------------------------------------------
-- Consequences
------------------------------------------------------------------------

/-- A term is in normal form when no reduction applies. -/
def IsNormal (t : Tm) : Prop := ∀ t', ¬ step t t'

/-- Reflexive transitive closure of reduction. -/
inductive reduces : Tm → Tm → Prop
  | refl (t : Tm) : reduces t t
  | step {t u v : Tm} : step t u → reduces u v → reduces t v

theorem exists_normal_of_sn {t : Tm} (h : SN t) : ∃ u, reduces t u ∧ IsNormal u := by
  induction h with
  | intro t _ ih =>
      by_cases hn : ∃ t', step t t'
      · obtain ⟨t', ht'⟩ := hn
        obtain ⟨u, hu, hnu⟩ := ih t' ht'
        exact ⟨u, reduces.step ht' hu, hnu⟩
      · exact ⟨t, reduces.refl t, fun t' ht' => hn ⟨t', ht'⟩⟩

/-- Every typable term of System T has a normal form. -/
theorem hasNormalForm_of_typing {Γ : List Ty} {t : Tm} {A : Ty} (h : Typing Γ t A) :
    ∃ u, reduces t u ∧ IsNormal u := exists_normal_of_sn (sn_of_typing h)

/-- The numeral of a natural number. -/
def num : ℕ → Tm
  | 0 => Tm.zero
  | n + 1 => Tm.succ (num n)

theorem typing_num (Γ : List Ty) (n : ℕ) : Typing Γ (num n) Ty.nat := by
  induction n with
  | zero => exact Typing.zero
  | succ n ih => exact Typing.succ ih

/-- Non-vacuity: addition is definable, and typable. -/
def addTm : Tm :=
  Tm.lam (Tm.lam (Tm.natrec (Tm.var 0) (Tm.lam (Tm.lam (Tm.succ (Tm.var 0)))) (Tm.var 1)))

theorem typing_addTm : Typing [] addTm (Ty.arrow Ty.nat (Ty.arrow Ty.nat Ty.nat)) :=
  Typing.lam (Typing.lam
    (Typing.natrec (Typing.var (by simp))
      (Typing.lam (Typing.lam (Typing.succ (Typing.var (by simp)))))
      (Typing.var (by simp))))

theorem sn_addTm : SN addTm := sn_of_typing typing_addTm

end GodelT
