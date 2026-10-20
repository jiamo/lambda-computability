/-
**Identity types in the groupoid model: the explicit constructions** (support for
`M23-GROUPOID-MODEL` / `M23-UIP-INDEPENDENT`).

For `A : Γ ⥤ Grpd` (over any category `Γ`), with `∫` the Grothendieck construction of
`Start/GrpdGrothendieck.lean`:

* `IdT A : ∫ (disp A ⋙ A) ⥤ Grpd` — the identity type: at `⟨⟨γ, a⟩, b⟩` it is the *discrete*
  groupoid on the morphisms `a ⟶ b` of the fibre `A γ`;
* `diagT`, `reflT`, `rhoT` — the diagonal, reflexivity (the identity morphism) and the map
  `x ↦ (x, x, refl x)`; `llT`, `xiT` — a substitution extended past `x y : A` and past `p : Id x y`;
* `piT A : ∫ (IdT A) ⥤ ∫ A` — the projection `(x, y, p) ↦ x`; it is faithful (`piT_faithful`),
  and any two objects over the same point are joined by a morphism over the identity (`overHom`);
* `transportAlong S Q τ` — transport of a section `S` along a natural transformation `τ` with
  target `Q`, and its laws (`transportAlong_precomp`, `_extend`, `_congr`, `_id`);
* `Jexp A M d` — the eliminator: transport of `d` along the morphism `(x, x, refl) ⟶ (x, y, p)`;
  `Jexp_comp` (the computation rule) and `Jexp_sub` (stability under substitution).
-/

import Start.GrpdGrothendieck

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Transport

variable {E : Type u} [Category.{u} E] {X : Type u} [Category.{u} X] (M : E ⥤ Grpd.{u, u})

theorem heq_eqToHom_comp_map {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {a a' b : C}
    (f : a ⟶ b) (f' : a' ⟶ b) (ha : a = a') (hf : HEq f f') {y y' : D} (h : y = F.obj a)
    (h' : y' = F.obj a') : HEq (eqToHom h ≫ F.map f) (eqToHom h' ≫ F.map f') := by
  subst ha
  cases hf
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

theorem map_eqToHom_heq {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {a b : C}
    (e : a = b) {c d : D} (e' : c = d) (hc : F.obj a = c) (hd : F.obj b = d) :
    HEq (F.map (eqToHom e)) (eqToHom e') := by
  subst e hc hd
  simp only [eqToHom_refl]
  exact heq_of_eq (F.map_id a)

theorem transport_eq {S : X ⥤ GObj M} {Q : X ⥤ E} (τ : S ⋙ disp M ⟶ Q) {x y : X} (m : x ⟶ y) :
    (M.map (Q.map m)).obj ((M.map (τ.app x)).obj (S.obj x).fib) =
      (M.map (τ.app y)).obj ((M.map (S.map m).base).obj (S.obj x).fib) :=
  (map_comp_obj _ _ _).symm.trans
    ((congrArg (fun f => (M.map f).obj (S.obj x).fib) (τ.naturality m).symm).trans
      (map_comp_obj _ _ _))

/-- Transport of a section `S` along a natural transformation `τ : S ⋙ disp M ⟶ Q`. -/
def transportAlong (S : X ⥤ GObj M) (Q : X ⥤ E) (τ : S ⋙ disp M ⟶ Q) : X ⥤ GObj M where
  obj x := ⟨Q.obj x, (M.map (τ.app x)).obj (S.obj x).fib⟩
  map {x y} m := ⟨Q.map m, eqToHom (transport_eq M τ m) ≫ (M.map (τ.app y)).map (S.map m).fib⟩
  map_id x := by
    refine GHom.hext (Q.map_id x) ?_
    refine (heq_eqToHom_comp_map (M.map (τ.app x)) _ (GHom.fib (𝟙 (S.obj x))) (by rw [S.map_id])
      (congr_arg_heq GHom.fib (S.map_id x)) _ rfl).trans ?_
    simp only [id_fib]
    exact (eqToHom_comp_heq _ _).trans (map_eqToHom_heq _ _ _
      ((congrArg (M.map (τ.app x)).obj (map_id_obj _ _)).trans (map_id_obj _ _).symm) rfl)
  map_comp {x y z} m n := by
    apply GHom.ext' (Q.map_comp m n)
    have e := S.map_comp m n
    have key := heq_eqToHom_comp_map (M.map (τ.app z)) _ (S.map m ≫ S.map n).fib
      (by rw [S.map_comp]) (congr_arg_heq GHom.fib e) (transport_eq M τ (m ≫ n))
      (transport_eq M τ (m ≫ n) |>.trans (by rw [S.map_comp]))
    rw [← heq_iff_eq]
    refine key.trans ?_
    simp only [comp_fib, Functor.map_comp, eqToHom_map, Category.assoc]
    have nat : (S.map n).base ≫ τ.app z = τ.app y ≫ Q.map n := τ.naturality n
    simp only [map_map, map_congr_map nat, Category.assoc, eqToHom_trans_assoc]
    exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _).symm

@[simp] theorem transportAlong_disp (S : X ⥤ GObj M) (Q : X ⥤ E) (τ : S ⋙ disp M ⟶ Q) :
    transportAlong M S Q τ ⋙ disp M = Q := rfl

theorem transportAlong_precomp {Y : Type u} [Category.{u} Y] (G : Y ⥤ X) (S : X ⥤ GObj M)
    (Q : X ⥤ E) (τ : S ⋙ disp M ⟶ Q) :
    G ⋙ transportAlong M S Q τ = transportAlong M (G ⋙ S) (G ⋙ Q) (Functor.whiskerLeft G τ) :=
  rfl

theorem transportAlong_extend {E' : Type u} [Category.{u} E'] (ξ : E' ⥤ E)
    (S : X ⥤ GObj (ξ ⋙ M)) (Q : X ⥤ E') (τ : S ⋙ disp (ξ ⋙ M) ⟶ Q) :
    transportAlong (ξ ⋙ M) S Q τ ⋙ extend ξ M =
      transportAlong M (S ⋙ extend ξ M) (Q ⋙ ξ) (Functor.whiskerRight τ ξ) :=
  rfl

theorem transportAlong_congr {S₁ S₂ : X ⥤ GObj M} {Q₁ Q₂ : X ⥤ E} (τ₁ : S₁ ⋙ disp M ⟶ Q₁)
    (τ₂ : S₂ ⋙ disp M ⟶ Q₂) (hS : S₁ = S₂) (hQ : Q₁ = Q₂) (hτ : ∀ x, HEq (τ₁.app x) (τ₂.app x)) :
    transportAlong M S₁ Q₁ τ₁ = transportAlong M S₂ Q₂ τ₂ := by
  subst hS hQ
  have : τ₁ = τ₂ := NatTrans.ext (funext fun x => eq_of_heq (hτ x))
  subst this
  rfl

theorem transportAlong_id (S : X ⥤ GObj M) :
    transportAlong M S (S ⋙ disp M) (𝟙 _) = S := by
  refine functor_ext rfl (fun x => heq_of_eq (map_id_obj _ _)) (fun {x y} m => ?_)
  refine (eqToHom_comp_heq _ _).trans ?_
  change HEq ((M.map (𝟙 (S.obj y).base)).map (S.map m).fib) _
  rw [map_id_map]
  exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)

theorem transportAlong_eq_self (S : X ⥤ GObj M) (Q : X ⥤ E) (τ : S ⋙ disp M ⟶ Q)
    (hQ : Q = S ⋙ disp M) (hτ : ∀ x, HEq (τ.app x) (𝟙 ((S ⋙ disp M).obj x))) :
    transportAlong M S Q τ = S := by
  subst hQ
  have : τ = 𝟙 _ := NatTrans.ext (funext fun x => eq_of_heq (hτ x))
  subst this
  exact transportAlong_id M S

end Transport

section Id

variable {Γ : Type u} [Category.{u} Γ] (A : Γ ⥤ Grpd.{u, u})

/-- The action of a morphism of `Γ.A.A⁺` on the identity proofs: `r ↦ φ⁻¹ ≫ A(f)(r) ≫ ψ`. -/
def idAct {P Q : GObj (disp A ⋙ A)} (f : P ⟶ Q) (r : P.base.fib ⟶ P.fib) : Q.base.fib ⟶ Q.fib :=
  Groupoid.inv f.base.fib ≫ (A.map f.base.base).map r ≫ f.fib

theorem idAct_id (P : GObj (disp A ⋙ A)) (r : P.base.fib ⟶ P.fib) : idAct A (𝟙 P) r = r := by
  simp [idAct, map_id_map]

theorem idAct_comp {P Q R : GObj (disp A ⋙ A)} (f : P ⟶ Q) (g : Q ⟶ R) (r : P.base.fib ⟶ P.fib) :
    idAct A (f ≫ g) r = idAct A g (idAct A f r) := by
  simp [idAct, map_comp_map]
  rfl

theorem dhom_eq {α : Type u} {a b : Discrete α} (f g : a ⟶ b) : f = g := Subsingleton.elim _ _

theorem IdT_map_id (P : GObj (disp A ⋙ A)) :
    (Discrete.functor fun r => Discrete.mk (idAct A (𝟙 P) r) :
      Discrete (P.base.fib ⟶ P.fib) ⥤ Discrete (P.base.fib ⟶ P.fib)) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun r => congrArg Discrete.mk (idAct_id A P r.as)) (fun _ _ _ => dhom_eq _ _)

theorem IdT_map_comp {P Q R : GObj (disp A ⋙ A)} (f : P ⟶ Q) (g : Q ⟶ R) :
    (Discrete.functor fun r => Discrete.mk (idAct A (f ≫ g) r) :
      Discrete (P.base.fib ⟶ P.fib) ⥤ Discrete (R.base.fib ⟶ R.fib)) =
    (Discrete.functor fun r => Discrete.mk (idAct A f r) :
      Discrete (P.base.fib ⟶ P.fib) ⥤ Discrete (Q.base.fib ⟶ Q.fib)) ⋙
    (Discrete.functor fun r => Discrete.mk (idAct A g r) :
      Discrete (Q.base.fib ⟶ Q.fib) ⥤ Discrete (R.base.fib ⟶ R.fib)) :=
  CategoryTheory.Functor.ext (fun r => congrArg Discrete.mk (idAct_comp A f g r.as)) (fun _ _ _ => dhom_eq _ _)

/-- **The identity type of the groupoid model**: at `⟨⟨γ, a⟩, b⟩`, the discrete groupoid on the
morphisms `a ⟶ b` of the fibre `A γ`. -/
def IdT : GObj (disp A ⋙ A) ⥤ Grpd.{u, u} where
  obj P := Grpd.of (Discrete (P.base.fib ⟶ P.fib))
  map f := Discrete.functor fun r => Discrete.mk (idAct A f r)
  map_id P := IdT_map_id A P
  map_comp f g := IdT_map_comp A f g

/-- The diagonal `Γ.A ⥤ Γ.A.A⁺`, `x ↦ (x, x)`. -/
def diagT : GObj A ⥤ GObj (disp A ⋙ A) where
  obj x := ⟨x, x.fib⟩
  map m := ⟨m, m.fib⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem idAct_diag {x y : GObj A} (m : x ⟶ y) : idAct A ((diagT A).map m) (𝟙 x.fib) = 𝟙 y.fib := by
  simp [idAct, diagT]

/-- Reflexivity: the section `x ↦ 𝟙` of `Id` over the diagonal. -/
def reflT : GObj A ⥤ GObj (diagT A ⋙ IdT A) where
  obj x := ⟨x, Discrete.mk (𝟙 x.fib)⟩
  map m := ⟨m, Discrete.eqToHom (idAct_diag A m)⟩
  map_id _ := GHom.hext rfl (heq_of_eq (dhom_eq _ _))
  map_comp _ _ := GHom.hext rfl (heq_of_eq (dhom_eq _ _))

/-- The map `Γ.A ⥤ Γ.A.A⁺.Id`, `x ↦ (x, x, refl x)`. -/
def rhoT : GObj A ⥤ GObj (IdT A) := reflT A ⋙ extend (diagT A) (IdT A)

/-- The projection `Γ.A.A⁺.Id ⥤ Γ.A`, `(x, y, p) ↦ x`. -/
def piT : GObj (IdT A) ⥤ GObj A := disp (IdT A) ⋙ disp (disp A ⋙ A)

theorem rhoT_piT : rhoT A ⋙ piT A = 𝟭 _ := rfl

/-- **The projection `(x, y, p) ↦ x` is faithful.** -/
theorem piT_faithful {P Q : GObj (IdT A)} (u v : P ⟶ Q) (h : u.base.base = v.base.base) :
    u = v := by
  have hu : idAct A u.base P.fib.as = Q.fib.as := Discrete.eq_of_hom u.fib
  have hv : idAct A v.base P.fib.as = Q.fib.as := Discrete.eq_of_hom v.fib
  obtain ⟨⟨ub, uf⟩, ud⟩ := u
  obtain ⟨⟨vb, vf⟩, vd⟩ := v
  change ub = vb at h
  subst h
  have : uf = vf := by
    simp only [idAct] at hu hv
    rw [← hv, ← Category.assoc, ← Category.assoc] at hu
    exact (cancel_epi _).mp hu
  subst this
  exact GHom.hext rfl (heq_of_eq (dhom_eq _ _))

theorem piT_hext {P Q P' Q' : GObj (IdT A)} (hP : P = P') (hQ : Q = Q') (u : P ⟶ Q) (v : P' ⟶ Q')
    (h : HEq u.base.base v.base.base) : HEq u v := by
  subst hP hQ
  exact heq_of_eq (piT_faithful A u v (eq_of_heq h))

/-- The morphism over the identity between two objects of `Γ.A.A⁺.Id` over the same point. -/
def overHom (P Q : GObj (IdT A)) (h : P.base.base = Q.base.base) : P ⟶ Q :=
  ⟨⟨eqToHom h, Groupoid.inv ((A.map (eqToHom h).base).map P.fib.as) ≫ (eqToHom h).fib ≫ Q.fib.as⟩,
    Discrete.eqToHom (by
      change idAct A _ P.fib.as = Q.fib.as
      simp [idAct])⟩

@[simp] theorem overHom_base_base (P Q : GObj (IdT A)) (h : P.base.base = Q.base.base) :
    (overHom A P Q h).base.base = eqToHom h := rfl

section J

variable (M : GObj (IdT A) ⥤ Grpd.{u, u}) (d : GObj A ⥤ GObj (rhoT A ⋙ M))
  (hd : d ⋙ disp (rhoT A ⋙ M) = 𝟭 _)

/-- The section to be transported, `(x, y, p) ↦ d x`. -/
def jS : GObj (IdT A) ⥤ GObj M := piT A ⋙ d ⋙ extend (rhoT A) M

/-- The transport morphisms `(x, x, refl x) ⟶ (x, y, p)`. -/
def jTau : jS A M d ⋙ disp M ⟶ 𝟭 _ where
  app e := overHom A _ e (Functor.congr_obj hd ((piT A).obj e))
  naturality e e' m := by
    apply piT_faithful
    have := Functor.congr_hom hd ((piT A).map m)
    simp only [comp_base, overHom_base_base, Functor.id_map]
    change (d ⋙ disp (rhoT A ⋙ M)).map ((piT A).map m) ≫ _ = _
    rw [this]
    simp [piT, disp]

/-- **The eliminator `J` of the groupoid model**: transport of `d` along the morphism
`(x, x, refl x) ⟶ (x, y, p)`. -/
def Jexp : GObj (IdT A) ⥤ GObj M := transportAlong M (jS A M d) (𝟭 _) (jTau A M d hd)

theorem Jexp_disp : Jexp A M d hd ⋙ disp M = 𝟭 _ := rfl

/-- **The computation rule**: `J` at reflexivity is `d`. -/
theorem Jexp_comp : rhoT A ⋙ Jexp A M d hd = d ⋙ extend (rhoT A) M := by
  rw [Jexp, transportAlong_precomp]
  have hQ : rhoT A ⋙ 𝟭 _ = (d ⋙ extend (rhoT A) M) ⋙ disp M := by
    change rhoT A = (d ⋙ disp _) ⋙ rhoT A
    rw [hd]; rfl
  refine transportAlong_eq_self M (d ⋙ extend (rhoT A) M) _ _ hQ (fun x => ?_)
  refine piT_hext A rfl (Functor.congr_obj hQ x) _ _ ?_
  exact eqToHom_heq_id_dom _ _ (Functor.congr_obj hd ((piT A).obj ((rhoT A).obj x)))

end J

end Id

section Sub

variable {Γ : Type u} [Category.{u} Γ] {Δ : Type u} [Category.{u} Δ] (σ : Δ ⥤ Γ)
  (A : Γ ⥤ Grpd.{u, u})

/-- A substitution `σ` extended past the two variables `x y : A`. -/
def llT : GObj (disp (σ ⋙ A) ⋙ σ ⋙ A) ⥤ GObj (disp A ⋙ A) := extend (extend σ A) (disp A ⋙ A)

theorem llT_IdT : llT σ A ⋙ IdT A = IdT (σ ⋙ A) := rfl

/-- A substitution `σ` extended past `x y : A` and `p : Id x y`. -/
def xiT : GObj (IdT (σ ⋙ A)) ⥤ GObj (IdT A) := extend (llT σ A) (IdT A)

theorem rhoT_xiT : rhoT (σ ⋙ A) ⋙ xiT σ A = extend σ A ⋙ rhoT A := rfl

theorem xiT_piT : xiT σ A ⋙ piT A = piT (σ ⋙ A) ⋙ extend σ A := rfl

/-- **Stability of `J` under substitution.** -/
theorem Jexp_sub (M : GObj (IdT A) ⥤ Grpd.{u, u}) (d : GObj A ⥤ GObj (rhoT A ⋙ M))
    (hd : d ⋙ disp (rhoT A ⋙ M) = 𝟭 _)
    (d' : GObj (σ ⋙ A) ⥤ GObj (rhoT (σ ⋙ A) ⋙ xiT σ A ⋙ M))
    (hd' : d' ⋙ disp (rhoT (σ ⋙ A) ⋙ xiT σ A ⋙ M) = 𝟭 _)
    (hdd : d' ⋙ extend (extend σ A) (rhoT A ⋙ M) = extend σ A ⋙ d) :
    Jexp (σ ⋙ A) (xiT σ A ⋙ M) d' hd' ⋙ extend (xiT σ A) M = xiT σ A ⋙ Jexp A M d hd := by
  rw [Jexp, Jexp, transportAlong_extend, transportAlong_precomp]
  have hS : jS (σ ⋙ A) (xiT σ A ⋙ M) d' ⋙ extend (xiT σ A) M = xiT σ A ⋙ jS A M d := by
    change piT (σ ⋙ A) ⋙ (d' ⋙ extend (extend σ A) (rhoT A ⋙ M)) ⋙ extend (rhoT A) M = _
    rw [hdd]
    rfl
  refine transportAlong_congr M _ _ hS rfl (fun e => ?_)
  refine piT_hext A (Functor.congr_obj (congrArg (· ⋙ disp M) hS) e) rfl _ _ ?_
  exact map_eqToHom_heq (extend σ A) (Functor.congr_obj hd' ((piT (σ ⋙ A)).obj e))
    (Functor.congr_obj hd ((piT A).obj ((xiT σ A).obj e)))
    (congrArg (fun P => P.base.base) (Functor.congr_obj (congrArg (· ⋙ disp M) hS) e)) rfl

end Sub

end GrpdModel
