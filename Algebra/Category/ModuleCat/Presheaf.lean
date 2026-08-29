/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Presheaves of modules over a presheaf of rings.

Given a presheaf of rings `R : Cᵒᵖ ⥤ RingCat`, we define the category `PresheafOfModules R`.
An object `M : PresheafOfModules R` consists of a family of modules
`M.obj X : ModuleCat (R.obj X)` for all `X : Cᵒᵖ`, together with the data, for all `f : X ⟶ Y`,
of a functorial linear map `M.map f` from `M.obj X` to the restriction
of scalars of `M.obj Y` via `R.map f`.


## Future work

* Compare this to the definition as a presheaf of pairs `(R, M)` with specified first part.
* Compare this to the definition as a module object of the presheaf of rings
  thought of as a monoid object.
* Presheaves of modules over a presheaf of commutative rings form a monoidal category.
* Pushforward and pullback.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory LinearMap Opposite

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

variable (R) in
/--
Definition of `PresheafOfModules` / `PresheafOfModules` 的定义

English:
structure PresheafOfModules
  parameters: where
  axioms and operations (4):
    - obj((X : Cᵒᵖ)) : ModuleCat.{v} (R.obj X)
    - map({X Y : Cᵒᵖ} (f : X ⟶ Y)) : obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y)
    - map_id((X : Cᵒᵖ)) : map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)).hom (congrArg RingCat.Hom.hom (R.map_id X))).inv.app _  [default: by cat_disch]
    - map_comp({X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)) : map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫ (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _  [default: by cat_disch]

中文:
结构 预模层
  参数: where
  公理与运算 (4 个):
    - obj((X : Cᵒᵖ)) : 模范畴.{v} (R.obj X)
    - map({X Y : Cᵒᵖ} (f : X ⟶ Y)) : obj X ⟶ (模范畴.restrictScalars (R.map f).hom).obj (obj Y)
    - map_id((X : Cᵒᵖ)) : map (𝟙 X) = (模范畴.restrictScalarsId' (R.map (𝟙 X)).hom (congrArg 环范畴.态射.hom (R.map_id X))).inv.app _  [默认: by cat_disch]
    - map_comp({X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)) : map (f ≫ g) = map f ≫ (模范畴.restrictScalars _).map (map g) ≫ (模范畴.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom (congrArg 环范畴.态射.hom <| R.map_comp f g)).inv.app _  [默认: by cat_disch]

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalars, ModuleCat.restrictScalarsComp, R.map, R.map_comp, RingCat, RingCat.Hom.hom, cat_disch, inv.app, map_comp, restrictScalars, restrictScalarsComp
-/
structure PresheafOfModules where
  /-- a family of modules over `R.obj X` for all `X` -/
  obj (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X)
  /-- the restriction maps of a presheaf of modules -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y)
  map_id (X : Cᵒᵖ) :
    map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)).hom
      (congrArg RingCat.Hom.hom (R.map_id X))).inv.app _ := by
        cat_disch
  map_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom <| R.map_comp f g)).inv.app _ := by cat_disch

namespace PresheafOfModules

attribute [simp] map_id map_comp
attribute [reassoc] map_comp

#adaptation_note /-- https://github.com/leanprover/lean4/pull/12564
This is required for `Algebra.Category.ModuleCat.Differentials.Presheaf` -/
instance {R : Cᵒᵖ ⥤ CommRingCat.{u}} (X : Cᵒᵖ) (M : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) :
    Module (R.obj X) (M.obj X) := (M.obj X).isModule

variable (M M₁ M₂ : PresheafOfModules.{v} R)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X)
  proof: by simp

中文:
引理 map_smul
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X)
  证明: by simp

Depends on / 依赖: isLeftAdjoint, restrictCoextendScalarsAdj
-/
protected lemma map_smul {X Y : Cᵒᵖ} (f : X ⟶ Y) (r : R.obj X) (m : M.obj X) :
    M.map f (r • m) = R.map f r • M.map f m := by simp

/--
lemma `congr_map_apply` / 引理 `congr_map_apply`

English:
lemma congr_map_apply
  given: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X)
  proof: by rw [h]

中文:
引理 congr_map_apply
  条件: {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X)
  证明: by rw [h]

Depends on / 依赖: isRightAdjoint, restrictCoextendScalarsAdj
-/
lemma congr_map_apply {X Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g) (m : M.obj X) :
    M.map f m = M.map g m := by rw [h]

/--
lemma `map_comp_apply` / 引理 `map_comp_apply`

English:
lemma map_comp_apply
  given: {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x)
  proof: by
  rw [M.map_comp]; rfl

中文:
引理 map_comp_apply
  条件: {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x)
  证明: by
  rw [M.map_comp]; rfl

Depends on / 依赖: M.map_comp, map_comp
-/
lemma map_comp_apply {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) (x) :
    M.map (i ≫ j) x = M.map j (M.map i x) := by
  rw [M.map_comp]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `restrictₛₗ` / `restrictₛₗ` 的定义

English:
definition restrictₛₗ
  signature: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  body: M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]

中文:
定义 restrictₛₗ
  签名: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  定义体: M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]

Depends on / 依赖: M.map
-/
noncomputable def restrictₛₗ {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.obj X ->ₛₗ[(R.map f).hom] M.obj Y where
  toFun m := M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]
/--
lemma `restrictₛₗ_apply` / 引理 `restrictₛₗ_apply`

English:
lemma restrictₛₗ_apply
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X)
  proof: rfl

中文:
引理 restrictₛₗ_apply
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X)
  证明: rfl
-/
lemma restrictₛₗ_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X) :
    M.restrictₛₗ f m = M.map f m := rfl

/-- A morphism of presheaves of modules consists of a family of linear maps which
satisfy the naturality condition. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (2):
    - app((X : Cᵒᵖ)) : M₁.obj X ⟶ M₂.obj X
    - naturality({X Y : Cᵒᵖ} (f : X ⟶ Y)) : M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) = app X ≫ M₂.map f  [default: by cat_disch]

中文:
结构 态射
  参数: where
  公理与运算 (2 个):
    - app((X : Cᵒᵖ)) : M₁.obj X ⟶ M₂.obj X
    - naturality({X Y : Cᵒᵖ} (f : X ⟶ Y)) : M₁.map f ≫ (模范畴.restrictScalars (R.map f).hom).map (app Y) = app X ≫ M₂.map f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom where
  /-- a family of linear maps `M₁.obj X ⟶ M₂.obj X` for all `X`. -/
  app (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) =
        app X ≫ M₂.map f := by cat_disch

attribute [reassoc (attr := simp)] Hom.naturality

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (PresheafOfModules.{v} R)
  body: Hom
  id _ := { app := fun _ => 𝟙 _ }
  comp f g := { app := fun _ => f.app _ ≫ g.app _ }

中文:
实例 :
  签名: 范畴 (预模层.{v} R)
  定义体: Hom
  id _ := { app := fun _ => 𝟙 _ }
  comp f g := { app := fun _ => f.app _ ≫ g.app _ }
-/
instance : Category (PresheafOfModules.{v} R) where
  Hom := Hom
  id _ := { app := fun _ => 𝟙 _ }
  comp f g := { app := fun _ => f.app _ ≫ g.app _ }

variable {M₁ M₂}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ), f.app X = g.app X)
  proof: Hom.ext (by ext1; apply h)

@[simp]

中文:
引理 hom_ext
  条件: {f g : M₁ ⟶ M₂} (h : 对任意 (X : Cᵒᵖ), f.app X = g.app X)
  证明: Hom.ext (by ext1; apply h)

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ), f.app X = g.app X) :
    f = g := Hom.ext (by ext1; apply h)

@[simp]
/--
lemma `id_app` / 引理 `id_app`

English:
lemma id_app
  given: (M : PresheafOfModules R) (X : Cᵒᵖ)
  statement: Hom.app (𝟙 M) X = 𝟙 _
  proof: by
  rfl

@[simp]

中文:
引理 id_app
  条件: (M : 预模层 R) (X : Cᵒᵖ)
  结论: 态射.app (𝟙 M) X = 𝟙 _
  证明: by
  rfl

@[simp]
-/
lemma id_app (M : PresheafOfModules R) (X : Cᵒᵖ) : Hom.app (𝟙 M) X = 𝟙 _ := by
  rfl

@[simp]
/--
lemma `comp_app` / 引理 `comp_app`

English:
lemma comp_app
  given: {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ)
  proof: by
  rfl

中文:
引理 comp_app
  条件: {M₁ M₂ M₃ : 预模层 R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ)
  证明: by
  rfl
-/
lemma comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    (f ≫ g).app X = f.app X ≫ g.app X := by
  rfl

/--
lemma `naturality_apply` / 引理 `naturality_apply`

English:
lemma naturality_apply
  given: (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X)
  proof: CategoryTheory.congr_fun (Hom.naturality f g) x

中文:
引理 naturality_apply
  条件: (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X)
  证明: CategoryTheory.congr_fun (Hom.naturality f g) x

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, Hom.naturality, congr_fun, naturality
-/
lemma naturality_apply (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    Hom.app f Y (M₁.map g x) = M₂.map g (Hom.app f X x) :=
  CategoryTheory.congr_fun (Hom.naturality f g) x

/-- Constructor for isomorphisms in the category of presheaves of modules. -/
@[simps!]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (app : forall (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
  body: { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv
      naturality := fun {X Y} f => by
        rw [← cancel_epi (app X).hom]; rw [← reassoc_of% (naturality f)]; rw [Iso.map_hom_inv_id]; rw [Category.comp_id]; rw [Iso.hom_inv_id_assoc] }

中文:
定义 isoMk
  签名: (app : 对任意 (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
  定义体: { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv
      naturality := fun {X Y} f => by
        rw [← cancel_epi (app X).hom]; rw [← reassoc_of% (naturality f)]; rw [Iso.map_hom_inv_id]; rw [Category.comp_id]; rw [Iso.hom_inv_id_assoc] }

Depends on / 依赖: Category, Category.comp_id, Iso.hom_inv_id_assoc, Iso.map_hom_inv_id, cancel_epi, cat_disch, comp_id, hom_inv_id_assoc, map_hom_inv_id, naturality, reassoc_of
-/
def isoMk (app : forall (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
    (naturality : forall ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y).hom =
        (app X).hom ≫ M₂.map f := by cat_disch) : M₁ ≅ M₂ where
  hom := { app := fun X => (app X).hom }
  inv :=
    { app := fun X => (app X).inv
      naturality := fun {X Y} f => by
        rw [← cancel_epi (app X).hom]; rw [← reassoc_of% (naturality f)]; rw [Iso.map_hom_inv_id]; rw [Category.comp_id]; rw [Iso.hom_inv_id_assoc] }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `presheaf` / `presheaf` 的定义

English:
definition presheaf
  signature: : Cᵒᵖ ⥤ Ab where
  body: (forget₂ _ _).obj (M.obj X)
map f := AddCommGrpCat.ofHom AddMonoidHom.mk' (M.map f) (by simp)

@[simp]

中文:
定义 presheaf
  签名: : Cᵒᵖ ⥤ Ab where
  定义体: (forget₂ _ _).obj (M.obj X)
map f := AddCommGrpCat.ofHom AddMonoidHom.mk' (M.map f) (by simp)

@[simp]

Depends on / 依赖: M.obj
-/
noncomputable def presheaf : Cᵒᵖ ⥤ Ab where
  obj X := (forget₂ _ _).obj (M.obj X)
map f := AddCommGrpCat.ofHom AddMonoidHom.mk' (M.map f) (by simp)

@[simp]
/--
lemma `presheaf_obj_coe` / 引理 `presheaf_obj_coe`

English:
lemma presheaf_obj_coe
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 presheaf_obj_coe
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]
-/
lemma presheaf_obj_coe (X : Cᵒᵖ) :
    (M.presheaf.obj X : Type _) = M.obj X := rfl

@[simp]
/--
lemma `presheaf_map_apply_coe` / 引理 `presheaf_map_apply_coe`

English:
lemma presheaf_map_apply_coe
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X)
  proof: rfl

@[reassoc]

中文:
引理 presheaf_map_apply_coe
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X)
  证明: rfl

@[reassoc]

Depends on / 依赖: M.map, M.obj, M.presheaf.map, presheaf
-/
lemma presheaf_map_apply_coe {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M.obj X) :
    DFunLike.coe (α := M.obj X) (β := fun _ => M.obj Y) (M.presheaf.map f).hom x = M.map f x := rfl

@[reassoc]
/--
lemma `smul_map` / 引理 `smul_map`

English:
lemma smul_map
  given: {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj U)
  proof: by
  ext x
  exact (M.map f).hom.map_smul r x

中文:
引理 smul_map
  条件: {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj U)
  证明: by
  ext x
  exact (M.map f).hom.map_smul r x

Depends on / 依赖: M.map, extendRestrictScalarsAdj, hom.map_smul, isLeftAdjoint, map_smul
-/
lemma smul_map {U V : Cᵒᵖ} (f : U ⟶ V) (r : R.obj U) :
    dsimp% ModuleCat.smul _ r ≫ M.presheaf.map f =
      M.presheaf.map f ≫ ModuleCat.smul _ (R.map f r) := by
  ext x
  exact (M.map f).hom.map_smul r x

instance (M : PresheafOfModules R) (X : Cᵒᵖ) :
    Module (R.obj X) (M.presheaf.obj X) :=
  inferInstanceAs (Module (R.obj X) (M.obj X))

variable (R) in
/--
Definition of `toPresheaf` / `toPresheaf` 的定义

English:
definition toPresheaf
  signature: : PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ Ab where
  body: M.presheaf
  map f :=
    { app := fun X => AddCommGrpCat.ofHom <| AddMonoidHom.mk' (Hom.app f X) (by simp)
      naturality := fun X Y g => by ext x; exact naturality_apply f g x }

@[simp]

中文:
定义 toPresheaf
  签名: : 预模层.{v} R ⥤ Cᵒᵖ ⥤ Ab where
  定义体: M.presheaf
  map f :=
    { app := fun X => AddCommGrpCat.ofHom <| AddMonoidHom.mk' (Hom.app f X) (by simp)
      naturality := fun X Y g => by ext x; exact naturality_apply f g x }

@[simp]

Depends on / 依赖: M.presheaf, extendRestrictScalarsAdj, isRightAdjoint, presheaf
-/
noncomputable def toPresheaf : PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ Ab where
  obj M := M.presheaf
  map f :=
    { app := fun X => AddCommGrpCat.ofHom <| AddMonoidHom.mk' (Hom.app f X) (by simp)
      naturality := fun X Y g => by ext x; exact naturality_apply f g x }

@[simp]
/--
lemma `toPresheaf_obj_coe` / 引理 `toPresheaf_obj_coe`

English:
lemma toPresheaf_obj_coe
  given: (X : Cᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 toPresheaf_obj_coe
  条件: (X : Cᵒᵖ)
  证明: rfl

@[simp]
-/
lemma toPresheaf_obj_coe (X : Cᵒᵖ) :
    (((toPresheaf R).obj M).obj X : Type _) = M.obj X := rfl

@[simp]
/--
lemma `toPresheaf_map_app_apply` / 引理 `toPresheaf_map_app_apply`

English:
lemma toPresheaf_map_app_apply
  given: (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X)
  proof: rfl

中文:
引理 toPresheaf_map_app_apply
  条件: (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X)
  证明: rfl
-/
lemma toPresheaf_map_app_apply (f : M₁ ⟶ M₂) (X : Cᵒᵖ) (x : M₁.obj X) :
    DFunLike.coe (α := M₁.obj X) (β := fun _ => M₂.obj X)
      (((toPresheaf R).map f).app X).hom x = f.app X x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheaf R).Faithful
  body: by
    ext X x
    exact ConcreteCategory.congr_hom (((evaluation _ _).obj X ⋙ forget Ab).congr_map h) x

中文:
实例 :
  签名: (toPresheaf R).忠实
  定义体: by
    ext X x
    exact ConcreteCategory.congr_hom (((evaluation _ _).obj X ⋙ forget Ab).congr_map h) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, congr_map, evaluation, forget
-/
instance : (toPresheaf R).Faithful where
  map_injective {_ _ f g} h := by
    ext X x
    exact ConcreteCategory.congr_hom (((evaluation _ _).obj X ⋙ forget Ab).congr_map h) x

section

variable (M : Cᵒᵖ ⥤ Ab.{v}) [forall X, Module (R.obj X) (M.obj X)]
  (map_smul : forall ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) (r : R.obj X) (m : M.obj X),
    M.map f (r • m) = R.map f r • M.map f m)

set_option backward.isDefEq.respectTransparency false in
/-- The object in `PresheafOfModules R` that is obtained from `M : Cᵒᵖ ⥤ Ab.{v}` such
that for all `X : Cᵒᵖ`, `M.obj X` is a `R.obj X` module, in such a way that the
restriction maps are semilinear. (This constructor should be used only in cases
when the preferred constructor `PresheafOfModules.mk` is not as convenient as this one.) -/
@[simps]
/--
Definition of `ofPresheaf` / `ofPresheaf` 的定义

English:
definition ofPresheaf
  signature: : PresheafOfModules.{v} R where
  body: ModuleCat.of _ (M.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of _ (M.obj Y)))
    { toFun := fun x => M.map f x
      map_add' := by simp
      map_smul' := fun r m => map_smul f r m }

@[simp]

中文:
定义 ofPresheaf
  签名: : 预模层.{v} R where
  定义体: ModuleCat.of _ (M.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of _ (M.obj Y)))
    { toFun := fun x => M.map f x
      map_add' := by simp
      map_smul' := fun r m => map_smul f r m }

@[simp]

Depends on / 依赖: M.obj, ModuleCat, ModuleCat.of
-/
noncomputable def ofPresheaf : PresheafOfModules.{v} R where
  obj X := ModuleCat.of _ (M.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of _ (M.obj Y)))
    { toFun := fun x => M.map f x
      map_add' := by simp
      map_smul' := fun r m => map_smul f r m }

@[simp]
/--
lemma `ofPresheaf_presheaf` / 引理 `ofPresheaf_presheaf`

English:
lemma ofPresheaf_presheaf
  statement: (ofPresheaf M map_smul).presheaf = M
  proof: rfl

中文:
引理 ofPresheaf_presheaf
  结论: (ofPresheaf M map_smul).presheaf = M
  证明: rfl
-/
lemma ofPresheaf_presheaf : (ofPresheaf M map_smul).presheaf = M := rfl

end

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism of presheaves of modules `M₁ ⟶ M₂` given by a morphism
of abelian presheaves `M₁.presheaf ⟶ M₂.presheaf`
which satisfy a suitable linearity condition. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: (φ : M₁.presheaf ⟶ M₂.presheaf)
  body: ModuleCat.ofHom
    { toFun := φ.app X
      map_add' := by simp +instances
      map_smul' := hφ X }
  naturality := fun f => by
    ext x
    exact CategoryTheory.congr_fun (φ.naturality f) x

中文:
定义 homMk
  签名: (φ : M₁.presheaf ⟶ M₂.presheaf)
  定义体: ModuleCat.ofHom
    { toFun := φ.app X
      map_add' := by simp +instances
      map_smul' := hφ X }
  naturality := fun f => by
    ext x
    exact CategoryTheory.congr_fun (φ.naturality f) x

Depends on / 依赖: ModuleCat, ModuleCat.ofHom
-/
noncomputable def homMk (φ : M₁.presheaf ⟶ M₂.presheaf)
    (hφ : forall (X : Cᵒᵖ) (r : R.obj X) (m : M₁.obj X), φ.app X (r • m) = r • φ.app X m) :
    M₁ ⟶ M₂ where
  app X := ModuleCat.ofHom
    { toFun := φ.app X
      map_add' := by simp +instances
      map_smul' := hφ X }
  naturality := fun f => by
    ext x
    exact CategoryTheory.congr_fun (φ.naturality f) x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M₁ ⟶ M₂)
  body: { app := fun _ => 0 }

中文:
实例 :
  签名: 零 (M₁ ⟶ M₂)
  定义体: { app := fun _ => 0 }
-/
instance : Zero (M₁ ⟶ M₂) where
  zero := { app := fun _ => 0 }

variable (M₁ M₂) in
/--
lemma `zero_app` / 引理 `zero_app`

English:
lemma zero_app
  given: (X : Cᵒᵖ)
  statement: (0 : M₁ ⟶ M₂).app X = 0
  proof: rfl

中文:
引理 zero_app
  条件: (X : Cᵒᵖ)
  结论: (0 : M₁ ⟶ M₂).app X = 0
  证明: rfl
-/
@[simp] lemma zero_app (X : Cᵒᵖ) : (0 : M₁ ⟶ M₂).app X = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (M₁ ⟶ M₂)
  body: { app := fun X => -f.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

中文:
实例 :
  签名: 取负 (M₁ ⟶ M₂)
  定义体: { app := fun X => -f.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

Depends on / 依赖: f.app, naturality, naturality_apply
-/
instance : Neg (M₁ ⟶ M₂) where
  neg f :=
    { app := fun X => -f.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (M₁ ⟶ M₂)
  body: { app := fun X => f.app X + g.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

中文:
实例 :
  签名: 加法 (M₁ ⟶ M₂)
  定义体: { app := fun X => f.app X + g.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

Depends on / 依赖: f.app, g.app, naturality, naturality_apply
-/
instance : Add (M₁ ⟶ M₂) where
  add f g :=
    { app := fun X => f.app X + g.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (M₁ ⟶ M₂)
  body: { app := fun X => f.app X - g.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

中文:
实例 :
  签名: 减法 (M₁ ⟶ M₂)
  定义体: { app := fun X => f.app X - g.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

Depends on / 依赖: f.app, g.app, naturality, naturality_apply
-/
instance : Sub (M₁ ⟶ M₂) where
  sub f g :=
    { app := fun X => f.app X - g.app X
      naturality := fun {X Y} h => by
        ext x
        simp [← naturality_apply] }

/--
lemma `neg_app` / 引理 `neg_app`

English:
lemma neg_app
  given: (f : M₁ ⟶ M₂) (X : Cᵒᵖ)
  statement: (-f).app X = -f.app X
  proof: rfl

中文:
引理 neg_app
  条件: (f : M₁ ⟶ M₂) (X : Cᵒᵖ)
  结论: (-f).app X = -f.app X
  证明: rfl
-/
@[simp] lemma neg_app (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (-f).app X = -f.app X := rfl
/--
lemma `add_app` / 引理 `add_app`

English:
lemma add_app
  given: (f g : M₁ ⟶ M₂) (X : Cᵒᵖ)
  statement: (f + g).app X = f.app X + g.app X
  proof: rfl

中文:
引理 add_app
  条件: (f g : M₁ ⟶ M₂) (X : Cᵒᵖ)
  结论: (f + g).app X = f.app X + g.app X
  证明: rfl
-/
@[simp] lemma add_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f + g).app X = f.app X + g.app X := rfl
/--
lemma `sub_app` / 引理 `sub_app`

English:
lemma sub_app
  given: (f g : M₁ ⟶ M₂) (X : Cᵒᵖ)
  statement: (f - g).app X = f.app X - g.app X
  proof: rfl

中文:
引理 sub_app
  条件: (f g : M₁ ⟶ M₂) (X : Cᵒᵖ)
  结论: (f - g).app X = f.app X - g.app X
  证明: rfl
-/
@[simp] lemma sub_app (f g : M₁ ⟶ M₂) (X : Cᵒᵖ) : (f - g).app X = f.app X - g.app X := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (M₁ ⟶ M₂)
  body: by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  neg_add_cancel := by intros; ext1; simp only [add_app, neg_app, neg_add_cancel, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

中文:
实例 :
  签名: 加法交换群 (M₁ ⟶ M₂)
  定义体: by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  neg_add_cancel := by intros; ext1; simp only [add_app, neg_app, neg_add_cancel, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

Depends on / 依赖: add_app, add_assoc, add_comm, add_zero, intros, neg_add_cancel, neg_app, nsmulRec, sub_app, sub_eq_add_neg, zero_add, zero_app, zsmulRec
-/
instance : AddCommGroup (M₁ ⟶ M₂) where
  add_assoc := by intros; ext1; simp only [add_app, add_assoc]
  zero_add := by intros; ext1; simp only [add_app, zero_app, zero_add]
  neg_add_cancel := by intros; ext1; simp only [add_app, neg_app, neg_add_cancel, zero_app]
  add_zero := by intros; ext1; simp only [add_app, zero_app, add_zero]
  add_comm := by intros; ext1; simp only [add_app]; apply add_comm
  sub_eq_add_neg := by intros; ext1; simp only [add_app, sub_app, neg_app, sub_eq_add_neg]
  nsmul := nsmulRec
  zsmul := zsmulRec

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (PresheafOfModules R)

中文:
实例 :
  签名: 预加性 (预模层 R)
-/
instance : Preadditive (PresheafOfModules R) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toPresheaf R).Additive

中文:
实例 :
  签名: (toPresheaf R).加性
-/
instance : (toPresheaf R).Additive where

/--
lemma `zsmul_app` / 引理 `zsmul_app`

English:
lemma zsmul_app
  given: (n : Int) (f : M₁ ⟶ M₂) (X : Cᵒᵖ)
  statement: (n • f).app X = n • f.app X
  proof: by
  ext x
  change (toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

中文:
引理 zsmul_app
  条件: (n : 整数) (f : M₁ ⟶ M₂) (X : Cᵒᵖ)
  结论: (n • f).app X = n • f.app X
  证明: by
  ext x
  change (toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

Depends on / 依赖: Functor, Functor.map_zsmul, evaluation, map_zsmul, toPresheaf
-/
lemma zsmul_app (n : Int) (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : (n • f).app X = n • f.app X := by
  ext x
  change (toPresheaf R ⋙ (evaluation _ _).obj X).map (n • f) x = _
  rw [Functor.map_zsmul]
  rfl

variable (R)

/-- Evaluation on an object `X` gives a functor
`PresheafOfModules R ⥤ ModuleCat (R.obj X)`. -/
@[simps]
/--
Definition of `evaluation` / `evaluation` 的定义

English:
definition evaluation
  signature: (X : Cᵒᵖ)
  body: M.obj X
  map f := f.app X

中文:
定义 evaluation
  签名: (X : Cᵒᵖ)
  定义体: M.obj X
  map f := f.app X

Depends on / 依赖: M.obj
-/
def evaluation (X : Cᵒᵖ) : PresheafOfModules.{v} R ⥤ ModuleCat (R.obj X) where
  obj M := M.obj X
  map f := f.app X

instance (X : Cᵒᵖ) : (evaluation.{v} R X).Additive where

set_option backward.defeqAttrib.useBackward true in
/-- The restriction natural transformation on presheaves of modules, considered as linear maps
to restriction of scalars. -/
@[simps]
/--
Definition of `restriction` / `restriction` 的定义

English:
definition restriction
  signature: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  body: M.map f

中文:
定义 restriction
  签名: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  定义体: M.map f

Depends on / 依赖: M.map
-/
noncomputable def restriction {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    evaluation R X ⟶ evaluation R Y ⋙ ModuleCat.restrictScalars (R.map f).hom where
  app M := M.map f

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: : PresheafOfModules R where
  body: ModuleCat.of _ (R.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (R.obj Y)))
    { toFun := fun x => R.map f x
      map_add' := by simp
      map_smul' := by cat_disch }

中文:
定义 unit
  签名: : 预模层 R where
  定义体: ModuleCat.of _ (R.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (R.obj Y)))
    { toFun := fun x => R.map f x
      map_add' := by simp
      map_smul' := by cat_disch }

Depends on / 依赖: ModuleCat, ModuleCat.of, R.obj
-/
noncomputable def unit : PresheafOfModules R where
  obj X := ModuleCat.of _ (R.obj X)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj (ModuleCat.of (R.obj Y) (R.obj Y)))
    { toFun := fun x => R.map f x
      map_add' := by simp
      map_smul' := by cat_disch }

/--
lemma `unit_map_one` / 引理 `unit_map_one`

English:
lemma unit_map_one
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  statement: (unit R).map f (1 : R.obj X) = (1 : R.obj Y)
  proof: (R.map f).hom.map_one

中文:
引理 unit_map_one
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  结论: (unit R).map f (1 : R.obj X) = (1 : R.obj Y)
  证明: (R.map f).hom.map_one

Depends on / 依赖: R.map, hom.map_one, map_one
-/
lemma unit_map_one {X Y : Cᵒᵖ} (f : X ⟶ Y) : (unit R).map f (1 : R.obj X) = (1 : R.obj Y) :=
  (R.map f).hom.map_one

variable {R}

/--
Definition of `sections` / `sections` 的定义

English:
definition sections
  signature: (M : PresheafOfModules.{v} R)
  body: (M.presheaf ⋙ forget _).sections

中文:
定义 sections
  签名: (M : 预模层.{v} R)
  定义体: (M.presheaf ⋙ forget _).sections

Depends on / 依赖: M.presheaf, forget, presheaf, sections
-/
def sections (M : PresheafOfModules.{v} R) : Type _ := (M.presheaf ⋙ forget _).sections

/--
Definition of `sections.eval` / `sections.eval` 的定义

English:
abbreviation sections.eval
  signature: {M : PresheafOfModules.{v} R} (s : M.sections) (X : Cᵒᵖ)
  body: s.1 X

@[simp]

中文:
缩写 sections.eval
  签名: {M : 预模层.{v} R} (s : M.sections) (X : Cᵒᵖ)
  定义体: s.1 X

@[simp]
-/
abbrev sections.eval {M : PresheafOfModules.{v} R} (s : M.sections) (X : Cᵒᵖ) : M.obj X := s.1 X

@[simp]
/--
lemma `sections_property` / 引理 `sections_property`

English:
lemma sections_property
  statement: {M : PresheafOfModules.{v} R} (s : M.sections)
  proof: s.2 f

中文:
引理 sections_property
  结论: {M : 预模层.{v} R} (s : M.sections)
  证明: s.2 f
-/
lemma sections_property {M : PresheafOfModules.{v} R} (s : M.sections)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : M.map f (s.1 X) = s.1 Y := s.2 f

/-- Constructor for sections of a presheaf of modules. -/
@[simps]
/--
Definition of `sectionsMk` / `sectionsMk` 的定义

English:
definition sectionsMk
  signature: {M : PresheafOfModules.{v} R} (s : forall X, M.obj X)
  body: s
  property f := hs f

@[ext]

中文:
定义 sectionsMk
  签名: {M : 预模层.{v} R} (s : 对任意 X, M.obj X)
  定义体: s
  property f := hs f

@[ext]
-/
def sectionsMk {M : PresheafOfModules.{v} R} (s : forall X, M.obj X)
    (hs : forall ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y), M.map f (s X) = s Y) : M.sections where
  val := s
  property f := hs f

@[ext]
/--
lemma `sections_ext` / 引理 `sections_ext`

English:
lemma sections_ext
  statement: {M : PresheafOfModules.{v} R} (s t : M.sections)
  proof: Subtype.ext (by ext; apply h)

中文:
引理 sections_ext
  结论: {M : 预模层.{v} R} (s t : M.sections)
  证明: Subtype.ext (by ext; apply h)

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma sections_ext {M : PresheafOfModules.{v} R} (s t : M.sections)
    (h : forall (X : Cᵒᵖ), s.val X = t.val X) : s = t :=
  Subtype.ext (by ext; apply h)

set_option backward.isDefEq.respectTransparency.types false in
/-- The map `M.sections → N.sections` induced by a morphisms `M ⟶ N` of presheaves of modules. -/
@[simps!]
/--
Definition of `sectionsMap` / `sectionsMap` 的定义

English:
definition sectionsMap
  signature: {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections)
  body: N.sectionsMk (fun X => f.app X (s.1 _))
    (fun X Y g => by rw [← naturality_apply, sections_property])

@[simp]

中文:
定义 sectionsMap
  签名: {M N : 预模层.{v} R} (f : M ⟶ N) (s : M.sections)
  定义体: N.sectionsMk (fun X => f.app X (s.1 _))
    (fun X Y g => by rw [← naturality_apply, sections_property])

@[simp]

Depends on / 依赖: N.sectionsMk, f.app, naturality_apply, sectionsMk, sections_property
-/
def sectionsMap {M N : PresheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  N.sectionsMk (fun X => f.app X (s.1 _))
    (fun X Y g => by rw [← naturality_apply, sections_property])

@[simp]
/--
lemma `sectionsMap_comp` / 引理 `sectionsMap_comp`

English:
lemma sectionsMap_comp
  given: {M N P : PresheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections)
  proof: rfl

@[simp]

中文:
引理 sectionsMap_comp
  条件: {M N P : 预模层.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections)
  证明: rfl

@[simp]
-/
lemma sectionsMap_comp {M N P : PresheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

@[simp]
/--
lemma `sectionsMap_id` / 引理 `sectionsMap_id`

English:
lemma sectionsMap_id
  given: {M : PresheafOfModules.{v} R} (s : M.sections)
  proof: rfl

中文:
引理 sectionsMap_id
  条件: {M : 预模层.{v} R} (s : M.sections)
  证明: rfl
-/
lemma sectionsMap_id {M : PresheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(unit R ⟶ M) ≃ M.sections` for `M : PresheafOfModules R`. -/
@[simps! apply_coe]
/--
Definition of `unitHomEquiv` / `unitHomEquiv` 的定义

English:
definition unitHomEquiv
  signature: (M : PresheafOfModules R)
  body: sectionsMk (fun X => Hom.app f X (1 : R.obj X))
    (by intros; rw [← naturality_apply, unit_map_one])
  invFun s :=
    { app := fun X => ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).symm (s.val X))
      naturality := fun {X Y} f => by
        ext
        dsimp
        change R.map f 1 • s.eval Y = M.map f (1 • s.eval X)
        simp }
  left_inv f := by
    ext X : 2
    exact (LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).symm_apply_apply (f.app X).hom
  right_inv s := by
    ext X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).apply_symm_apply (s.val X)

中文:
定义 unitHomEquiv
  签名: (M : 预模层 R)
  定义体: sectionsMk (fun X => Hom.app f X (1 : R.obj X))
    (by intros; rw [← naturality_apply, unit_map_one])
  invFun s :=
    { app := fun X => ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).symm (s.val X))
      naturality := fun {X Y} f => by
        ext
        dsimp
        change R.map f 1 • s.eval Y = M.map f (1 • s.eval X)
        simp }
  left_inv f := by
    ext X : 2
    exact (LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).symm_apply_apply (f.app X).hom
  right_inv s := by
    ext X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).apply_symm_apply (s.val X)

Depends on / 依赖: Hom.app, R.obj, sectionsMk
-/
noncomputable def unitHomEquiv (M : PresheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections where
  toFun f := sectionsMk (fun X => Hom.app f X (1 : R.obj X))
    (by intros; rw [← naturality_apply, unit_map_one])
  invFun s :=
    { app := fun X => ModuleCat.ofHom
        ((LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).symm (s.val X))
      naturality := fun {X Y} f => by
        ext
        dsimp
        change R.map f 1 • s.eval Y = M.map f (1 • s.eval X)
        simp }
  left_inv f := by
    ext X : 2
    exact (LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).symm_apply_apply (f.app X).hom
  right_inv s := by
    ext X
    exact (LinearMap.ringLmapEquivSelf (R.obj X) Int (M.obj X)).apply_symm_apply (s.val X)

section module_over_initial

variable (X : Cᵒᵖ) (hX : Limits.IsInitial X)

/-!
## `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)` when `X` is initial

When `X` is initial, we have `Module (R.obj X) (M.obj c)` for any `c : Cᵒᵖ`.

-/

section

variable (M : PresheafOfModules.{v} R)

/--
Definition of `forgetToPresheafModuleCatObjObj` / `forgetToPresheafModuleCatObjObj` 的定义

English:
abbreviation forgetToPresheafModuleCatObjObj
  signature: (Y : Cᵒᵖ)
  body: (ModuleCat.restrictScalars (R.map (hX.to Y)).hom).obj (M.obj Y)

中文:
缩写 forgetToPresheafModuleCatObjObj
  签名: (Y : Cᵒᵖ)
  定义体: (ModuleCat.restrictScalars (R.map (hX.to Y)).hom).obj (M.obj Y)

Depends on / 依赖: M.obj, ModuleCat, ModuleCat.restrictScalars, R.map, hX.to, restrictScalars
-/
noncomputable abbrev forgetToPresheafModuleCatObjObj (Y : Cᵒᵖ) : ModuleCat (R.obj X) :=
  (ModuleCat.restrictScalars (R.map (hX.to Y)).hom).obj (M.obj Y)

-- This should not be a `simp` lemma because `M.obj Y` is missing the `Module (R.obj X)` instance,
-- so `simp`ing breaks downstream proofs.
/--
lemma `forgetToPresheafModuleCatObjObj_coe` / 引理 `forgetToPresheafModuleCatObjObj_coe`

English:
lemma forgetToPresheafModuleCatObjObj_coe
  given: (Y : Cᵒᵖ)
  proof: rfl

中文:
引理 forgetToPresheafModuleCatObjObj_coe
  条件: (Y : Cᵒᵖ)
  证明: rfl
-/
lemma forgetToPresheafModuleCatObjObj_coe (Y : Cᵒᵖ) :
    (forgetToPresheafModuleCatObjObj X hX M Y : Type _) = M.obj Y := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `forgetToPresheafModuleCatObjMap` / `forgetToPresheafModuleCatObjMap` 的定义

English:
definition forgetToPresheafModuleCatObjMap
  signature: {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
  body: ModuleCat.ofHom
    (X := forgetToPresheafModuleCatObjObj X hX M Y) (Y := forgetToPresheafModuleCatObjObj X hX M Z)
  { toFun := fun x => M.map f x
    map_add' := by simp
    map_smul' := fun r x => by
      simp only [ModuleCat.restrictScalars.smul_def (R := R.obj X), RingHom.id_apply, M.map_smul]
      rw [← RingCat.comp_apply]; rw [← R.map_comp]
      congr
      apply hX.hom_ext }

@[simp]

中文:
定义 forgetToPresheafModuleCatObjMap
  签名: {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
  定义体: ModuleCat.ofHom
    (X := forgetToPresheafModuleCatObjObj X hX M Y) (Y := forgetToPresheafModuleCatObjObj X hX M Z)
  { toFun := fun x => M.map f x
    map_add' := by simp
    map_smul' := fun r x => by
      simp only [ModuleCat.restrictScalars.smul_def (R := R.obj X), RingHom.id_apply, M.map_smul]
      rw [← RingCat.comp_apply]; rw [← R.map_comp]
      congr
      apply hX.hom_ext }

@[simp]

Depends on / 依赖: M.map, M.map_smul, ModuleCat, ModuleCat.ofHom, ModuleCat.restrictScalars.smul_def, R.map_comp, R.obj, RingCat, RingCat.comp_apply, RingHom, RingHom.id_apply, comp_apply, forgetToPresheafModuleCatObjObj, hX.hom_ext, hom_ext, id_apply, map_add, map_comp, map_smul, restrictScalars
-/
noncomputable def forgetToPresheafModuleCatObjMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    forgetToPresheafModuleCatObjObj X hX M Y ⟶
      forgetToPresheafModuleCatObjObj X hX M Z :=
  ModuleCat.ofHom
    (X := forgetToPresheafModuleCatObjObj X hX M Y) (Y := forgetToPresheafModuleCatObjObj X hX M Z)
  { toFun := fun x => M.map f x
    map_add' := by simp
    map_smul' := fun r x => by
      simp only [ModuleCat.restrictScalars.smul_def (R := R.obj X), RingHom.id_apply, M.map_smul]
      rw [← RingCat.comp_apply]; rw [← R.map_comp]
      congr
      apply hX.hom_ext }

@[simp]
/--
lemma `forgetToPresheafModuleCatObjMap_apply` / 引理 `forgetToPresheafModuleCatObjMap_apply`

English:
lemma forgetToPresheafModuleCatObjMap_apply
  given: {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y)
  proof: rfl

中文:
引理 forgetToPresheafModuleCatObjMap_apply
  条件: {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y)
  证明: rfl
-/
lemma forgetToPresheafModuleCatObjMap_apply {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (m : M.obj Y) :
    (forgetToPresheafModuleCatObjMap X hX M f).hom m = M.map f m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Implementation of the functor `PresheafOfModules R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X)`
when `X` is initial.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
@[simps]
/--
Definition of `forgetToPresheafModuleCatObj` / `forgetToPresheafModuleCatObj` 的定义

English:
definition forgetToPresheafModuleCatObj
  body: forgetToPresheafModuleCatObjObj X hX M Y
  map f := forgetToPresheafModuleCatObjMap X hX M f

中文:
定义 forgetToPresheafModuleCatObj
  定义体: forgetToPresheafModuleCatObjObj X hX M Y
  map f := forgetToPresheafModuleCatObjMap X hX M f

Depends on / 依赖: forgetToPresheafModuleCatObjObj
-/
noncomputable def forgetToPresheafModuleCatObj
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) (M : PresheafOfModules.{v} R) :
    Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj Y := forgetToPresheafModuleCatObjObj X hX M Y
  map f := forgetToPresheafModuleCatObjMap X hX M f

end

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `forgetToPresheafModuleCatMap` / `forgetToPresheafModuleCatMap` 的定义

English:
definition forgetToPresheafModuleCatMap
  body: ModuleCat.ofHom
      (X := (forgetToPresheafModuleCatObj X hX M).obj Y)
      (Y := (forgetToPresheafModuleCatObj X hX N).obj Y)
    { toFun := f.app Y
      map_add' := by simp
      map_smul' := fun r => (f.app Y).hom.map_smul (R.map (hX.to Y) _) }
  naturality Y Z g := by
    ext x
    exact naturality_apply f g x

中文:
定义 forgetToPresheafModuleCatMap
  定义体: ModuleCat.ofHom
      (X := (forgetToPresheafModuleCatObj X hX M).obj Y)
      (Y := (forgetToPresheafModuleCatObj X hX N).obj Y)
    { toFun := f.app Y
      map_add' := by simp
      map_smul' := fun r => (f.app Y).hom.map_smul (R.map (hX.to Y) _) }
  naturality Y Z g := by
    ext x
    exact naturality_apply f g x

Depends on / 依赖: ModuleCat, ModuleCat.ofHom
-/
noncomputable def forgetToPresheafModuleCatMap
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) {M N : PresheafOfModules.{v} R} (f : M ⟶ N) :
    forgetToPresheafModuleCatObj X hX M ⟶ forgetToPresheafModuleCatObj X hX N where
  app Y := ModuleCat.ofHom
      (X := (forgetToPresheafModuleCatObj X hX M).obj Y)
      (Y := (forgetToPresheafModuleCatObj X hX N).obj Y)
    { toFun := f.app Y
      map_add' := by simp
      map_smul' := fun r => (f.app Y).hom.map_smul (R.map (hX.to Y) _) }
  naturality Y Z g := by
    ext x
    exact naturality_apply f g x

set_option backward.isDefEq.respectTransparency.types false in
/--
The forgetful functor from presheaves of modules over a presheaf of rings `R` to presheaves of
`R(X)`-modules where `X` is an initial object.

The functor is implemented as, on object level `M ↦ (c ↦ M(c))` where the `R(X)`-module structure
on `M(c)` is given by restriction of scalars along the unique morphism `R(c) ⟶ R(X)`; and on
morphism level `(f : M ⟶ N) ↦ (c ↦ f(c))`.
-/
@[simps]
/--
Definition of `forgetToPresheafModuleCat` / `forgetToPresheafModuleCat` 的定义

English:
definition forgetToPresheafModuleCat
  signature: (X : Cᵒᵖ) (hX : Limits.IsInitial X)
  body: forgetToPresheafModuleCatObj X hX M
  map f := forgetToPresheafModuleCatMap X hX f

中文:
定义 forgetToPresheafModuleCat
  签名: (X : Cᵒᵖ) (hX : Limits.IsInitial X)
  定义体: forgetToPresheafModuleCatObj X hX M
  map f := forgetToPresheafModuleCatMap X hX f

Depends on / 依赖: forgetToPresheafModuleCatObj
-/
noncomputable def forgetToPresheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    PresheafOfModules.{v} R ⥤ Cᵒᵖ ⥤ ModuleCat (R.obj X) where
  obj M := forgetToPresheafModuleCatObj X hX M
  map f := forgetToPresheafModuleCatMap X hX f

end module_over_initial

end PresheafOfModules
