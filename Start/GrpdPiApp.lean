/-
**Application for the groupoid Π-type, and the Π-structure of the groupoid model** (task
`M23-GROUPOID-PI`, round 6).

For `A : Γ ⥤ Grpd`, `B : ∫ A ⥤ Grpd` and a section `σ` of `Π A B`:

* `GrpdModel.fibTil` / `GrpdModel.fibI_fibTil` — every morphism `m : (γ, a) ⟶ (γ', a')` of `∫ A`
  factors as a fibre morphism followed by the fibre comparison: `m = ι_γ(φ̃) ≫ θ_g(a')`, uniquely
  (`GrpdModel.fibTil_unique`);
* `GrpdModel.appPhi σ γ` — the fibre part, the functor `A γ ⥤ ∫ B` given by the section `σ γ`;
  `GrpdModel.appPsi σ g a'` — the transport part, the morphism of `∫ B` over `θ_g(a')` given by the
  section's own morphism part `(σ.map g).app a'`;
* `GrpdModel.appPsi_comp` (the strict law of `σ.map` on composites, through `σ.map_comp` and
  `piTheta_comp_heq`), `GrpdModel.appPsi_nat` (the naturality of `σ.map g`, the interchange of the
  two parts);
* `GrpdModel.uncurryF σ : ∫ A ⥤ ∫ B` — **application**: on `m = ι(φ̃) ≫ θ`, the composite
  `Φ(φ̃) ≫ Ψ`; its `map_comp` is proved from the three laws above, `map_id` from `map_comp` in the
  groupoid `∫ B`;
* `GrpdModel.grpdApp` — application on terms; `GrpdModel.grpd_app_lam` (β) and
  `GrpdModel.grpd_lam_app` (η);
* `GrpdModel.grpdPiStruct : Cwa.PiStruct grpdCwa` — **the groupoid model has Π-types**.
-/

import Start.GrpdPiLam

set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace GrpdModel

section Factor

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u})

theorem map_inv_obj_eq {γ γ' : Γ} (g : γ ⟶ γ') (a : A.obj γ) :
    a = (A.map (Groupoid.inv g)).obj ((A.map g).obj a) := by
  have h : (A.map (g ≫ Groupoid.inv g)).obj a = a := by rw [Groupoid.comp_inv, map_id_obj]
  exact h.symm.trans (map_comp_obj _ _ _)

/-- The fibre component of a morphism of `∫ A`, moved to the source fibre. -/
def fibTil {p q : GObj A} (m : p ⟶ q) : p.fib ⟶ (A.map (Groupoid.inv m.base)).obj q.fib :=
  eqToHom (map_inv_obj_eq A m.base p.fib) ≫ (A.map (Groupoid.inv m.base)).map m.fib

/-- **Factorisation of a morphism of `∫ A`**: a fibre morphism, then the fibre comparison. -/
theorem fibI_fibTil {p q : GObj A} (m : p ⟶ q) :
    (fibI A p.base).map (fibTil A m) ≫ (piTheta A m.base).app q.fib = m := by
  refine (GHom.ext' (Category.id_comp _).symm ?_).symm
  have key : (A.map m.base).map ((A.map (Groupoid.inv m.base)).map m.fib) =
      eqToHom (map_comp_obj (A := A) (Groupoid.inv m.base) m.base _).symm ≫
        (A.map (Groupoid.inv m.base ≫ m.base)).map m.fib ≫
          eqToHom (map_comp_obj (A := A) (Groupoid.inv m.base) m.base _) := map_map _ _ _
  simp only [fibTil, comp_fib, fibI_map, piTheta, Functor.map_comp, eqToHom_map, key,
    map_congr_map (Groupoid.inv_comp m.base), map_id_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]
  simp

/-- **Uniqueness of the factorisation.** -/
theorem fibTil_unique {γ γ' : Γ} (g : γ ⟶ γ') {a : A.obj γ} {a' : A.obj γ'}
    {φ₁ φ₂ : a ⟶ (A.map (Groupoid.inv g)).obj a'}
    (h : (fibI A γ).map φ₁ ≫ (piTheta A g).app a' = (fibI A γ).map φ₂ ≫ (piTheta A g).app a') :
    φ₁ = φ₂ := by
  have h1 := (cancel_mono _).1 h
  have h2 : eqToHom (map_id_obj (A := A) γ a) ≫ φ₁ = eqToHom (map_id_obj (A := A) γ a) ≫ φ₂ := by
    have := congr_arg_heq GHom.fib h1
    simp only [fibI_map] at this
    exact eq_of_heq this
  exact (cancel_epi _).1 h2

theorem fibTil_eq {p q : GObj A} (m : p ⟶ q) {φ : p.fib ⟶ (A.map (Groupoid.inv m.base)).obj q.fib}
    (h : (fibI A p.base).map φ ≫ (piTheta A m.base).app q.fib = m) : fibTil A m = φ :=
  fibTil_unique A m.base ((fibI_fibTil A m).trans h.symm)

theorem piTheta_id_eq (γ : Γ) (a : A.obj γ)
    (h : (A.map (Groupoid.inv (𝟙 γ)) ⋙ fibI A γ).obj a = (fibI A γ).obj a) :
    (piTheta A (𝟙 γ)).app a = eqToHom h :=
  eq_of_heq ((piTheta_id_heq A γ a).trans (eqToHom_heq_id_cod _ _ _).symm)

end Factor

section App

variable {Γ : Type u} [Groupoid.{u} Γ] {A : Γ ⥤ Grpd.{u, u}} {B : GObj A ⥤ Grpd.{u, u}}
  (σ : Sect (PiF A B))

/-- The value of a section of `Π A B` at `γ`, as a section over the fibre. -/
abbrev sfib (γ : Γ) : Sect (fibI A γ ⋙ B) := σ.obj γ

/-- The morphism part of a section of `Π A B` over `g`. -/
abbrev shom {γ γ' : Γ} (g : γ ⟶ γ') : (piMap A B g).obj (sfib σ γ) ⟶ sfib σ γ' := σ.map g

/-- The fibre part of application: the section `σ γ` as a functor `A γ ⥤ ∫ B`. -/
def appPhi (γ : Γ) : A.obj γ ⥤ GObj B := (sfib σ γ).toFunctor ⋙ extend (fibI A γ) B

@[simp] theorem appPhi_obj (γ : Γ) (a : A.obj γ) :
    (appPhi σ γ).obj a = ⟨⟨γ, a⟩, (sfib σ γ).obj a⟩ := rfl

@[simp] theorem appPhi_map (γ : Γ) {a b : A.obj γ} (φ : a ⟶ b) :
    (appPhi σ γ).map φ = ⟨(fibI A γ).map φ, (sfib σ γ).map φ⟩ := rfl

/-- The transport part of application: the morphism of `∫ B` over `θ_g(a')` given by the
section's own morphism part over `g`. -/
def appPsi {γ γ' : Γ} (g : γ ⟶ γ') (a' : A.obj γ') :
    (appPhi σ γ).obj ((A.map (Groupoid.inv g)).obj a') ⟶ (appPhi σ γ').obj a' :=
  ⟨(piTheta A g).app a', (shom σ g).app a'⟩

@[simp] theorem appPsi_base {γ γ' : Γ} (g : γ ⟶ γ') (a' : A.obj γ') :
    (appPsi σ g a').base = (piTheta A g).app a' := rfl

@[simp] theorem appPsi_fib {γ γ' : Γ} (g : γ ⟶ γ') (a' : A.obj γ') :
    (appPsi σ g a').fib = (shom σ g).app a' := rfl

theorem shom_comp_app {γ γ' γ'' : Γ} (g₁ : γ ⟶ γ') (g₂ : γ' ⟶ γ'') (a₂ : A.obj γ'') :
    HEq ((shom σ (g₁ ≫ g₂)).app a₂)
      ((B.map ((piTheta A g₂).app a₂)).map ((shom σ g₁).app ((A.map (Groupoid.inv g₂)).obj a₂)) ≫
        (shom σ g₂).app a₂) := by
  have e := congrArg (fun α => SectHom.app α a₂) (σ.map_comp g₁ g₂)
  refine (heq_of_eq e).trans ?_
  erw [Sect.comp_app, Sect.comp_app, Sect.eqToHom_app]
  refine (eqToHom_comp_heq _ _).trans ?_
  rfl

/-- **The transport part on a composite.** -/
theorem appPsi_comp {γ γ' γ'' : Γ} (g₁ : γ ⟶ γ') (g₂ : γ' ⟶ γ'') (a₂ : A.obj γ'') :
    HEq (appPsi σ g₁ ((A.map (Groupoid.inv g₂)).obj a₂) ≫ appPsi σ g₂ a₂)
      (appPsi σ (g₁ ≫ g₂) a₂) := by
  have hobj : (A.map (Groupoid.inv (g₁ ≫ g₂))).obj a₂ =
      (A.map (Groupoid.inv g₁)).obj ((A.map (Groupoid.inv g₂)).obj a₂) := by
    rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, IsIso.inv_comp,
      Functor.map_comp]
    rfl
  refine GHom.hext' (congrArg (appPhi σ γ).obj hobj.symm) rfl
    (piTheta_comp_heq A g₁ g₂ a₂).symm ?_
  simp only [comp_fib, appPsi_fib, appPsi_base]
  exact (eqToHom_comp_heq _ _).trans (shom_comp_app σ g₁ g₂ a₂).symm

/-- **The interchange of the two parts** (the naturality of `σ.map g`). -/
theorem appPsi_nat {γ γ' : Γ} (g : γ ⟶ γ') {a' b' : A.obj γ'} (ψ : a' ⟶ b') :
    appPsi σ g a' ≫ (appPhi σ γ').map ψ =
      (appPhi σ γ).map ((A.map (Groupoid.inv g)).map ψ) ≫ appPsi σ g b' := by
  refine GHom.hext ((piTheta A g).naturality ψ).symm ?_
  have hn := (shom σ g).nat ψ
  erw [transObj_map] at hn
  simp only [comp_fib, appPsi_fib, appPsi_base, appPhi_map]
  refine (eqToHom_comp_heq _ _).trans ?_
  refine (heq_of_eq hn.symm).trans ?_
  rw [Category.assoc]
  refine (eqToHom_comp_heq _ _).trans ?_
  exact (eqToHom_comp_heq _ _).symm

theorem piTheta_comp_eq {γ γ' γ'' : Γ} (g₁ : γ ⟶ γ') (g₂ : γ' ⟶ γ'') (a₂ : A.obj γ'')
    (h : (A.map (Groupoid.inv (g₁ ≫ g₂))).obj a₂ =
      (A.map (Groupoid.inv g₁)).obj ((A.map (Groupoid.inv g₂)).obj a₂)) :
    (piTheta A (g₁ ≫ g₂)).app a₂ = eqToHom (congrArg (fibI A γ).obj h) ≫
      ((piTheta A g₁).app ((A.map (Groupoid.inv g₂)).obj a₂) ≫ (piTheta A g₂).app a₂) :=
  eq_of_heq ((piTheta_comp_heq A g₁ g₂ a₂).trans (eqToHom_comp_heq _ _).symm)

theorem appPsi_comp_eq {γ γ' γ'' : Γ} (g₁ : γ ⟶ γ') (g₂ : γ' ⟶ γ'') (a₂ : A.obj γ'')
    (h : (A.map (Groupoid.inv (g₁ ≫ g₂))).obj a₂ =
      (A.map (Groupoid.inv g₁)).obj ((A.map (Groupoid.inv g₂)).obj a₂)) :
    appPsi σ (g₁ ≫ g₂) a₂ = eqToHom (congrArg (appPhi σ γ).obj h) ≫
      (appPsi σ g₁ ((A.map (Groupoid.inv g₂)).obj a₂) ≫ appPsi σ g₂ a₂) :=
  (eq_of_heq ((eqToHom_comp_heq _ _).trans (appPsi_comp σ g₁ g₂ a₂))).symm

/-- **The factorisation of a composite.** -/
theorem fibTil_comp {p q r : GObj A} (m₁ : p ⟶ q) (m₂ : q ⟶ r)
    (h : (A.map (Groupoid.inv (m₁.base ≫ m₂.base))).obj r.fib =
      (A.map (Groupoid.inv m₁.base)).obj ((A.map (Groupoid.inv m₂.base)).obj r.fib)) :
    fibTil A (m₁ ≫ m₂) =
      fibTil A m₁ ≫ (A.map (Groupoid.inv m₁.base)).map (fibTil A m₂) ≫ eqToHom h.symm := by
  refine fibTil_eq A (m₁ ≫ m₂) ?_
  have hnat : (fibI A p.base).map ((A.map (Groupoid.inv m₁.base)).map (fibTil A m₂)) ≫
      (piTheta A m₁.base).app ((A.map (Groupoid.inv m₂.base)).obj r.fib) =
      (piTheta A m₁.base).app q.fib ≫ (fibI A q.base).map (fibTil A m₂) :=
    (piTheta A m₁.base).naturality (fibTil A m₂)
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    eqToHom_map (fibI A p.base) h.symm]
  have hθ := piTheta_comp_eq (A := A) m₁.base m₂.base r.fib h
  show (fibI A p.base).map (fibTil A m₁) ≫
      (fibI A p.base).map ((A.map (Groupoid.inv m₁.base)).map (fibTil A m₂)) ≫
        eqToHom (congrArg (fibI A p.base).obj h.symm) ≫
          (piTheta A (m₁.base ≫ m₂.base)).app r.fib = _
  rw [hθ, ← Category.assoc (eqToHom (congrArg (fibI A p.base).obj h.symm)), eqToHom_trans,
    eqToHom_refl, Category.id_comp]
  rw [← Category.assoc ((fibI A p.base).map ((A.map (Groupoid.inv m₁.base)).map (fibTil A m₂))),
    hnat, Category.assoc, fibI_fibTil A m₂, ← Category.assoc,
    fibI_fibTil A m₁]

/-- Application: the object part. -/
def uobj (p : GObj A) : GObj B := (appPhi σ p.base).obj p.fib

/-- Application: the morphism part, through the factorisation. -/
def umap {p q : GObj A} (m : p ⟶ q) : uobj σ p ⟶ uobj σ q :=
  (appPhi σ p.base).map (fibTil A m) ≫ appPsi σ m.base q.fib

theorem umap_base {p q : GObj A} (m : p ⟶ q) : (umap σ m).base = m := by
  show (fibI A p.base).map (fibTil A m) ≫ (piTheta A m.base).app q.fib = m
  exact fibI_fibTil A m

theorem umap_comp {p q r : GObj A} (m₁ : p ⟶ q) (m₂ : q ⟶ r) :
    umap σ (m₁ ≫ m₂) = umap σ m₁ ≫ umap σ m₂ := by
  have h : (A.map (Groupoid.inv (m₁.base ≫ m₂.base))).obj r.fib =
      (A.map (Groupoid.inv m₁.base)).obj ((A.map (Groupoid.inv m₂.base)).obj r.fib) := by
    rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, Groupoid.inv_eq_inv, IsIso.inv_comp,
      Functor.map_comp]
    rfl
  have hψ := appPsi_comp_eq σ m₁.base m₂.base r.fib h
  have hnat := appPsi_nat σ m₁.base (fibTil A m₂)
  show (appPhi σ p.base).map (fibTil A (m₁ ≫ m₂)) ≫ appPsi σ (m₁.base ≫ m₂.base) r.fib = _
  rw [fibTil_comp m₁ m₂ h, Functor.map_comp, Functor.map_comp, hψ,
    eqToHom_map (appPhi σ p.base) h.symm, Category.assoc, Category.assoc,
    ← Category.assoc (eqToHom (congrArg (appPhi σ p.base).obj h.symm)), eqToHom_trans,
    eqToHom_refl, Category.id_comp, ← Category.assoc
      ((appPhi σ p.base).map ((A.map (Groupoid.inv m₁.base)).map (fibTil A m₂))), ← hnat]
  show _ = ((appPhi σ p.base).map (fibTil A m₁) ≫ appPsi σ m₁.base q.fib) ≫
    ((appPhi σ q.base).map (fibTil A m₂) ≫ appPsi σ m₂.base r.fib)
  simp only [Category.assoc]

theorem umap_id (p : GObj A) : umap σ (𝟙 p) = 𝟙 (uobj σ p) := by
  have h := umap_comp σ (𝟙 p) (𝟙 p)
  rw [Category.comp_id] at h
  have h' : umap σ (𝟙 p) ≫ 𝟙 (uobj σ p) = umap σ (𝟙 p) ≫ umap σ (𝟙 p) := by
    rw [Category.comp_id]
    exact h
  exact ((cancel_epi (umap σ (𝟙 p))).1 h').symm

/-- **Application**: the functor `∫ A ⥤ ∫ B` determined by a section of `Π A B`. -/
def uncurryF : GObj A ⥤ GObj B where
  obj := uobj σ
  map := umap σ
  map_id := umap_id σ
  map_comp := umap_comp σ

theorem uncurryF_disp : uncurryF σ ⋙ disp B = 𝟭 (GObj A) :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun p q m => by
    simp only [Functor.comp_map, Functor.id_map, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    exact umap_base σ m

/-- **Application on sections**: the inverse of `curry`. -/
def uncurry : Sect B :=
  cast (congrArg Sect (by rw [uncurryF_disp]; rfl)) (Sect.ofOver (uncurryF σ))

theorem appPsi_id (γ : Γ) (a : A.obj γ)
    (e : (appPhi σ γ).obj ((A.map (Groupoid.inv (𝟙 γ))).obj a) = (appPhi σ γ).obj a) :
    appPsi σ (𝟙 γ) a = eqToHom e := by
  have hobj : (A.map (Groupoid.inv (𝟙 γ))).obj a = a := by
    rw [Groupoid.inv_eq_inv, IsIso.inv_id]; exact map_id_obj γ a
  refine eq_of_heq (HEq.trans ?_ (eqToHom_heq_id_cod _ _ _).symm)
  refine GHom.hext' (congrArg (appPhi σ γ).obj hobj) rfl (piTheta_id_heq A γ a) ?_
  simp only [appPsi_fib, id_fib]
  have e1 := congrArg (fun α => SectHom.app α a) (σ.map_id γ)
  refine (heq_of_eq e1).trans ?_
  erw [Sect.eqToHom_app]
  exact (eqToHom_heq_id_cod _ _ _).trans (eqToHom_heq_id_cod _ _ _).symm

/-- Application on a fibre morphism is the section's own fibre morphism. -/
theorem umap_fibI (γ : Γ) {a a' : A.obj γ} (φ : a ⟶ a') :
    umap σ ((fibI A γ).map φ) = (appPhi σ γ).map φ := by
  have hobj : a' = (A.map (Groupoid.inv (𝟙 γ))).obj a' := by
    rw [Groupoid.inv_eq_inv, IsIso.inv_id]; exact (map_id_obj γ a').symm
  have hf : fibTil A ((fibI A γ).map φ) = φ ≫ eqToHom hobj := by
    refine fibTil_eq A _ ?_
    show (fibI A γ).map (φ ≫ eqToHom hobj) ≫ (piTheta A (𝟙 γ)).app a' = (fibI A γ).map φ
    rw [piTheta_id_eq A γ a' (congrArg (fibI A γ).obj hobj.symm), Functor.map_comp,
      eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  show (appPhi σ γ).map (fibTil A ((fibI A γ).map φ)) ≫ appPsi σ (𝟙 γ) a' = _
  rw [hf, appPsi_id σ γ a' (congrArg (appPhi σ γ).obj hobj.symm), Functor.map_comp,
    eqToHom_map, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Application on a fibre comparison is the transport part. -/
theorem umap_theta {γ γ' : Γ} (g : γ ⟶ γ') (a : A.obj γ') :
    umap σ ((piTheta A g).app a) = appPsi σ g a := by
  have hf : fibTil A ((piTheta A g).app a) = 𝟙 _ := by
    refine fibTil_eq A _ ?_
    show (fibI A γ).map (𝟙 _) ≫ (piTheta A g).app a = (piTheta A g).app a
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  show (appPhi σ γ).map (fibTil A ((piTheta A g).app a)) ≫ appPsi σ g a = _
  rw [hf]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

end App

section Uncurry

variable {Γ : Type u} [Groupoid.{u} Γ] (A : Γ ⥤ Grpd.{u, u}) (B : GObj A ⥤ Grpd.{u, u})

/-- **β on functors**: applying a curried section gives the section back. -/
theorem uncurryF_curry (τ : Sect B) : uncurryF (curry A B τ) = τ.toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) fun p q m => ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  show τ.toFunctor.map ((fibI A p.base).map (fibTil A m)) ≫
    τ.toFunctor.map ((piTheta A m.base).app q.fib) = τ.toFunctor.map m
  rw [← Functor.map_comp, fibI_fibTil A m]

end Uncurry

section Terms

variable {Γ : Grpd.{u, u}} (A : grpdCwa.Ty Γ) (B : grpdCwa.Ty (grpdCwa.ext Γ A))

/-- **Application in the groupoid model.** -/
def grpdApp (f : grpdCwa.Tm Γ (PiF A B)) : grpdCwa.Tm (grpdCwa.ext Γ A) B :=
  ⟨uncurryF (B := B) (sectOfTm f), uncurryF_disp _⟩

/-- **β in the groupoid model.** -/
theorem grpd_app_lam (b : grpdCwa.Tm (grpdCwa.ext Γ A) B) : grpdApp A B (grpdLam A B b) = b := by
  apply Subtype.ext
  show uncurryF (sectOfTm (tmOfSect (curry A B (sectOfTm b)))) = b.1
  rw [show sectOfTm (tmOfSect (curry A B (sectOfTm b))) = curry A B (sectOfTm b) from
    (tmEquivSect Γ (PiF A B)).right_inv _, uncurryF_curry]
  exact congrArg Subtype.val ((tmEquivSect (grpdCwa.ext Γ A) B).left_inv b)

/-- **η in the groupoid model.** -/
theorem grpd_lam_app (f : grpdCwa.Tm Γ (PiF A B)) : grpdLam A B (grpdApp A B f) = f := by
  set σ := sectOfTm f with hσ
  set τ := sectOfTm (grpdApp A B f) with hτ
  have hcast : (uncurryF (B := B) σ ⋙ disp B) ⋙ B = B := by rw [uncurryF_disp]; rfl
  have hobj : ∀ p, τ.obj p = (uobj σ p).fib := fun p =>
    eq_of_heq (Sect.cast_obj_heq hcast _ p)
  have hmap : ∀ {p q : GObj A} (m : p ⟶ q), HEq (τ.map m) (umap σ m).fib := fun m =>
    Sect.cast_map_heq hcast _ m
  have hfib : ∀ γ : Γ, curryObj A B τ γ = σ.obj γ := by
    intro γ
    refine Sect.hext (funext fun a => hobj ⟨γ, a⟩) fun {a a'} φ => ?_
    refine (hmap ((fibI A γ).map φ)).trans ?_
    rw [umap_fibI]
    rfl
  have hc : curry A B τ = σ := by
    refine Sect.hext (funext hfib) fun {γ γ'} g => ?_
    refine SectHom.hext' (congrArg (piMap A B g).obj (hfib γ)) (hfib γ') fun a => ?_
    refine (hmap ((piTheta A g).app a)).trans ?_
    rw [umap_theta]
    rfl
  show tmOfSect (curry A B τ) = f
  rw [hc]
  exact (tmEquivSect Γ (PiF A B)).left_inv f

/-- **The groupoid model has Π-types.** -/
def grpdPiStruct : Cwa.PiStruct grpdCwa where
  Pi A B := PiF A B
  Pi_sub σ A B := PiF_sub σ A B
  lam {_} {A} {B} b := grpdLam A B b
  app {_} {A} {B} f := grpdApp A B f
  app_lam {_} {A} {B} b := grpd_app_lam A B b
  lam_app {_} {A} {B} f := grpd_lam_app A B f

end Terms

end GrpdModel
