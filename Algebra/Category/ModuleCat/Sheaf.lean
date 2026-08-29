/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.AlgCat.TensorAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Sheaves of modules over a sheaf of rings

In this file, we define the category `SheafOfModules R` when `R : Sheaf J RingCat`
is a sheaf of rings on a category `C` equipped with a Grothendieck topology `J`.

-/

@[expose] public section

universe v v₁ u₁ u w

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/--
Definition of `SheafOfModules` / `SheafOfModules` 的定义

English:
structure SheafOfModules
  parameters: where
  axioms and operations (2):
    - val : PresheafOfModules.{v} R.obj
    - isSheaf : Presheaf.IsSheaf J val.presheaf

中文:
结构 模层
  参数: where
  公理与运算 (2 个):
    - val : 预模层.{v} R.obj
    - isSheaf : 预层.是层 J val.presheaf
-/
structure SheafOfModules where
  /-- the underlying presheaf of modules of a sheaf of modules -/
  val : PresheafOfModules.{v} R.obj
  isSheaf : Presheaf.IsSheaf J val.presheaf

namespace SheafOfModules

variable {R}

/-- A morphism between sheaves of modules is a morphism between the underlying
presheaves of modules. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : SheafOfModules.{v} R)
  axioms and operations (1):
    - val : X.val ⟶ Y.val

中文:
结构 态射
  参数: (X Y : 模层.{v} R)
  公理与运算 (1 个):
    - val : X.val ⟶ Y.val
-/
structure Hom (X Y : SheafOfModules.{v} R) where
  /-- a morphism between the underlying presheaves of modules -/
  val : X.val ⟶ Y.val

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SheafOfModules.{v} R)
  body: Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩

@[ext]

中文:
实例 :
  签名: 范畴 (模层.{v} R)
  定义体: Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩

@[ext]
-/
instance : Category (SheafOfModules.{v} R) where
  Hom := Hom
  id _ := ⟨𝟙 _⟩
  comp f g := ⟨f.val ≫ g.val⟩

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : SheafOfModules.{v} R} {f g : X ⟶ Y} (h : f.val = g.val)
  statement: f = g
  proof: Hom.ext h

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 模层.{v} R} {f g : X ⟶ Y} (h : f.val = g.val)
  结论: f = g
  证明: Hom.ext h

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ Y} (h : f.val = g.val) : f = g :=
  Hom.ext h

@[simp]
/--
lemma `id_val` / 引理 `id_val`

English:
lemma id_val
  given: (X : SheafOfModules.{v} R)
  statement: Hom.val (𝟙 X) = 𝟙 X.val
  proof: rfl

@[simp, reassoc]

中文:
引理 id_val
  条件: (X : 模层.{v} R)
  结论: 态射.val (𝟙 X) = 𝟙 X.val
  证明: rfl

@[simp, reassoc]
-/
lemma id_val (X : SheafOfModules.{v} R) : Hom.val (𝟙 X) = 𝟙 X.val := rfl

@[simp, reassoc]
/--
lemma `comp_val` / 引理 `comp_val`

English:
lemma comp_val
  given: {X Y Z : SheafOfModules.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 comp_val
  条件: {X Y Z : 模层.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma comp_val {X Y Z : SheafOfModules.{v} R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val ≫ g.val := rfl

variable (R)
/-- The forgetful functor `SheafOfModules.{v} R ⥤ PresheafOfModules R.val`. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : SheafOfModules.{v} R ⥤ PresheafOfModules R.obj where
  body: F.val
  map φ := φ.val

中文:
定义 forget
  签名: : 模层.{v} R ⥤ 预模层 R.obj where
  定义体: F.val
  map φ := φ.val

Depends on / 依赖: F.val, addCommGroup, fullyFaithfulForget, homEquiv, homEquiv.addCommGroup
-/
def forget : SheafOfModules.{v} R ⥤ PresheafOfModules R.obj where
  obj F := F.val
  map φ := φ.val

/-- The forget functor `SheafOfModules R ⥤ PresheafOfModules R.val` is fully faithful. -/
@[simps]
/--
Definition of `fullyFaithfulForget` / `fullyFaithfulForget` 的定义

English:
definition fullyFaithfulForget
  signature: : (forget.{v} R).FullyFaithful where
  body: ⟨φ⟩

中文:
定义 fullyFaithfulForget
  签名: : (forget.{v} R).满忠实 where
  定义体: ⟨φ⟩
-/
def fullyFaithfulForget : (forget.{v} R).FullyFaithful where
  preimage φ := ⟨φ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget.{v} R).Faithful
  body: (fullyFaithfulForget R).faithful

中文:
实例 :
  签名: (forget.{v} R).忠实
  定义体: (fullyFaithfulForget R).faithful

Depends on / 依赖: faithful, fullyFaithfulForget
-/
instance : (forget.{v} R).Faithful := (fullyFaithfulForget R).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget.{v} R).Full
  body: (fullyFaithfulForget R).full

中文:
实例 :
  签名: (forget.{v} R).满
  定义体: (fullyFaithfulForget R).full

Depends on / 依赖: fullyFaithfulForget
-/
instance : (forget.{v} R).Full := (fullyFaithfulForget R).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget.{v} R).ReflectsIsomorphisms
  body: (fullyFaithfulForget R).reflectsIsomorphisms

中文:
实例 :
  签名: (forget.{v} R).反映同构
  定义体: (fullyFaithfulForget R).reflectsIsomorphisms

Depends on / 依赖: fullyFaithfulForget, reflectsIsomorphisms
-/
instance : (forget.{v} R).ReflectsIsomorphisms := (fullyFaithfulForget R).reflectsIsomorphisms

/--
Definition of `evaluation` / `evaluation` 的定义

English:
definition evaluation
  signature: (X : Cᵒᵖ)
  body: forget _ ⋙ PresheafOfModules.evaluation _ X

中文:
定义 evaluation
  签名: (X : Cᵒᵖ)
  定义体: forget _ ⋙ PresheafOfModules.evaluation _ X

Depends on / 依赖: PresheafOfModules, PresheafOfModules.evaluation, evaluation, forget
-/
def evaluation (X : Cᵒᵖ) : SheafOfModules.{v} R ⥤ ModuleCat.{v} (R.obj.obj X) :=
  forget _ ⋙ PresheafOfModules.evaluation _ X

/-- The forget functor `SheafOfModules R ⥤ Sheaf J AddCommGrpCat`. -/
@[simps]
/--
Definition of `toSheaf` / `toSheaf` 的定义

English:
definition toSheaf
  signature: : SheafOfModules.{v} R ⥤ Sheaf J AddCommGrpCat.{v} where
  body: ⟨_, M.isSheaf⟩
  map f := { hom := (forget R ⋙ PresheafOfModules.toPresheaf R.obj).map f }

中文:
定义 toSheaf
  签名: : 模层.{v} R ⥤ 层 J 加法交换群范畴.{v} where
  定义体: ⟨_, M.isSheaf⟩
  map f := { hom := (forget R ⋙ PresheafOfModules.toPresheaf R.obj).map f }

Depends on / 依赖: M.isSheaf, isSheaf
-/
noncomputable def toSheaf : SheafOfModules.{v} R ⥤ Sheaf J AddCommGrpCat.{v} where
  obj M := ⟨_, M.isSheaf⟩
  map f := { hom := (forget R ⋙ PresheafOfModules.toPresheaf R.obj).map f }

/--
The forgetful functor from sheaves of modules over sheaf of ring `R` to sheaves of `R(X)`-module
when `X` is initial.
-/
@[simps]
/--
Definition of `forgetToSheafModuleCat` / `forgetToSheafModuleCat` 的定义

English:
definition forgetToSheafModuleCat
  body: ⟨(PresheafOfModules.forgetToPresheafModuleCat X hX).obj M.1,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{w} (R.1.obj X)) AddCommGrpCat.{w}) M.isSheaf⟩
  map f := { hom := (PresheafOfModules.forgetToPresheafModuleCat X hX).map f.1 }

中文:
定义 forgetToSheafModuleCat
  定义体: ⟨(PresheafOfModules.forgetToPresheafModuleCat X hX).obj M.1,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{w} (R.1.obj X)) AddCommGrpCat.{w}) M.isSheaf⟩
  map f := { hom := (PresheafOfModules.forgetToPresheafModuleCat X hX).map f.1 }

Depends on / 依赖: PresheafOfModules, PresheafOfModules.forgetToPresheafModuleCat, forgetToPresheafModuleCat
-/
noncomputable def forgetToSheafModuleCat
      (X : Cᵒᵖ) (hX : Limits.IsInitial X) :
    SheafOfModules.{w} R ⥤ Sheaf J (ModuleCat.{w} (R.1.obj X)) where
  obj M := ⟨(PresheafOfModules.forgetToPresheafModuleCat X hX).obj M.1,
    Presheaf.isSheaf_of_isSheaf_comp _ _
      (forget₂ (ModuleCat.{w} (R.1.obj X)) AddCommGrpCat.{w}) M.isSheaf⟩
  map f := { hom := (PresheafOfModules.forgetToPresheafModuleCat X hX).map f.1 }

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `forgetToSheafModuleCatOfIso` / `forgetToSheafModuleCatOfIso` 的定义

English:
definition forgetToSheafModuleCatOfIso
  signature: (X Y : Cᵒᵖ) (hX : Limits.IsInitial X)
  body: by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · dsimp [PresheafOfModules.forgetToPresheafModuleCatObjObj]
      refine ModuleCat.restrictScalarsComp'App _ _ _ ?_ _
      simpa using congr((R.obj.map $(hX.hom_ext (hX.to U) 

中文:
定义 forgetToSheafModuleCatOfIso
  签名: (X Y : Cᵒᵖ) (hX : Limits.IsInitial X)
  定义体: by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · dsimp [PresheafOfModules.forgetToPresheafModuleCatObjObj]
      refine ModuleCat.restrictScalarsComp'App _ _ _ ?_ _
      simpa using congr((R.obj.map $(hX.hom_ext (hX.to U) 

Depends on / 依赖: ModuleCat, ModuleCat.restrictScalarsComp, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.isoMk, PresheafOfModules, PresheafOfModules.forgetToPresheafModuleCatObjObj, R.obj.map, cat_disch, forgetToPresheafModuleCatObjObj, hX.hom_ext, hX.to, hY.to, hom_ext, ofComponents, restrictScalarsComp
-/
noncomputable def forgetToSheafModuleCatOfIso (X Y : Cᵒᵖ) (hX : Limits.IsInitial X)
    (hY : Limits.IsInitial Y) (φ : X ≅ Y) :
    forgetToSheafModuleCat R X hX ≅ forgetToSheafModuleCat R Y hY ⋙
      sheafCompose J (ModuleCat.restrictScalars (R.obj.map φ.hom).hom) := by
  refine NatIso.ofComponents (fun M => ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U => ?_) ?_
    · dsimp [PresheafOfModules.forgetToPresheafModuleCatObjObj]
      refine ModuleCat.restrictScalarsComp'App _ _ _ ?_ _
      simpa using congr((R.obj.map $(hX.hom_ext (hX.to U) (φ.hom ≫ hY.to U))).hom)
    cat_disch
  cat_disch

/--
Definition of `toSheafCompSheafToPresheafIso` / `toSheafCompSheafToPresheafIso` 的定义

English:
definition toSheafCompSheafToPresheafIso
  signature: :
  body: Iso.refl _

中文:
定义 toSheafCompSheafToPresheafIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
noncomputable def toSheafCompSheafToPresheafIso :
    toSheaf R ⋙ sheafToPresheaf J AddCommGrpCat.{v} ≅
      forget R ⋙ PresheafOfModules.toPresheaf R.obj := Iso.refl _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toSheaf.{v} R).Faithful
  body: Functor.Faithful.of_comp_iso (toSheafCompSheafToPresheafIso.{v} R)

中文:
实例 :
  签名: (toSheaf.{v} R).忠实
  定义体: Functor.Faithful.of_comp_iso (toSheafCompSheafToPresheafIso.{v} R)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_comp_iso, of_comp_iso, toSheafCompSheafToPresheafIso
-/
instance : (toSheaf.{v} R).Faithful :=
  Functor.Faithful.of_comp_iso (toSheafCompSheafToPresheafIso.{v} R)

instance (M N : SheafOfModules.{v} R) : AddCommGroup (M ⟶ N) :=
  (fullyFaithfulForget R).homEquiv.addCommGroup

@[simp]
/--
lemma `add_val` / 引理 `add_val`

English:
lemma add_val
  given: {M N : SheafOfModules.{v} R} (f g : M ⟶ N)
  proof: rfl

中文:
引理 add_val
  条件: {M N : 模层.{v} R} (f g : M ⟶ N)
  证明: rfl
-/
lemma add_val {M N : SheafOfModules.{v} R} (f g : M ⟶ N) :
    (f + g).val = f.val + g.val := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive (SheafOfModules.{v} R)
  body: by intros; ext1; dsimp; simp only [Preadditive.add_comp]
  comp_add := by tauto

中文:
实例 :
  签名: 预加性 (模层.{v} R)
  定义体: by intros; ext1; dsimp; simp only [Preadditive.add_comp]
  comp_add := by tauto

Depends on / 依赖: Preadditive, Preadditive.add_comp, add_comp, comp_add, intros
-/
instance : Preadditive (SheafOfModules.{v} R) where
  add_comp := by intros; ext1; dsimp; simp only [Preadditive.add_comp]
  comp_add := by tauto

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget R).Additive

中文:
实例 :
  签名: (forget R).加性
-/
instance : (forget R).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toSheaf R).Additive

中文:
实例 :
  签名: (toSheaf R).加性
-/
instance : (toSheaf R).Additive where

variable {R}

/--
Definition of `sections` / `sections` 的定义

English:
abbreviation sections
  signature: (M : SheafOfModules.{v} R)
  body: M.val.sections

中文:
缩写 sections
  签名: (M : 模层.{v} R)
  定义体: M.val.sections

Depends on / 依赖: M.val.sections, sections
-/
abbrev sections (M : SheafOfModules.{v} R) : Type _ := M.val.sections

/--
Definition of `sectionsMap` / `sectionsMap` 的定义

English:
abbreviation sectionsMap
  signature: {M N : SheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections)
  body: PresheafOfModules.sectionsMap f.val s

@[simp]

中文:
缩写 sectionsMap
  签名: {M N : 模层.{v} R} (f : M ⟶ N) (s : M.sections)
  定义体: PresheafOfModules.sectionsMap f.val s

@[simp]

Depends on / 依赖: PresheafOfModules, PresheafOfModules.sectionsMap, f.val, sectionsMap
-/
abbrev sectionsMap {M N : SheafOfModules.{v} R} (f : M ⟶ N) (s : M.sections) : N.sections :=
  PresheafOfModules.sectionsMap f.val s

@[simp]
/--
lemma `sectionsMap_comp` / 引理 `sectionsMap_comp`

English:
lemma sectionsMap_comp
  given: {M N P : SheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections)
  proof: rfl

@[simp]

中文:
引理 sectionsMap_comp
  条件: {M N P : 模层.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections)
  证明: rfl

@[simp]
-/
lemma sectionsMap_comp {M N P : SheafOfModules.{v} R} (f : M ⟶ N) (g : N ⟶ P) (s : M.sections) :
    sectionsMap (f ≫ g) s = sectionsMap g (sectionsMap f s) := rfl

@[simp]
/--
lemma `sectionsMap_id` / 引理 `sectionsMap_id`

English:
lemma sectionsMap_id
  given: {M : SheafOfModules.{v} R} (s : M.sections)
  proof: rfl

中文:
引理 sectionsMap_id
  条件: {M : 模层.{v} R} (s : M.sections)
  证明: rfl
-/
lemma sectionsMap_id {M : SheafOfModules.{v} R} (s : M.sections) :
    sectionsMap (𝟙 M) s = s := rfl

variable (R) in
/-- The functor which sends a sheaf of modules to its type of sections. -/
@[simps]
/--
Definition of `sectionsFunctor` / `sectionsFunctor` 的定义

English:
definition sectionsFunctor
  signature: : SheafOfModules.{v} R ⥤ Type _ where
  body: M.sections
  map f := ↾(sectionsMap f)

中文:
定义 sectionsFunctor
  签名: : 模层.{v} R ⥤ 类型 _ where
  定义体: M.sections
  map f := ↾(sectionsMap f)

Depends on / 依赖: M.sections, sections
-/
def sectionsFunctor : SheafOfModules.{v} R ⥤ Type _ where
  obj M := M.sections
  map f := ↾(sectionsMap f)

variable (R) in
/-- The obvious free sheaf of modules of rank `1`. -/
@[simps]
/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: : SheafOfModules R where
  body: PresheafOfModules.unit R.obj
  isSheaf := ((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj R).property

中文:
定义 unit
  签名: : 模层 R where
  定义体: PresheafOfModules.unit R.obj
  isSheaf := ((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj R).property

Depends on / 依赖: PresheafOfModules, PresheafOfModules.unit, R.obj
-/
noncomputable def unit : SheafOfModules R where
  val := PresheafOfModules.unit R.obj
  isSheaf := ((sheafCompose J (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj R).property

/--
Definition of `unitHomEquiv` / `unitHomEquiv` 的定义

English:
definition unitHomEquiv
  signature: (M : SheafOfModules R)
  body: (fullyFaithfulForget R).homEquiv.trans M.val.unitHomEquiv

@[simp]

中文:
定义 unitHomEquiv
  签名: (M : 模层 R)
  定义体: (fullyFaithfulForget R).homEquiv.trans M.val.unitHomEquiv

@[simp]

Depends on / 依赖: M.val.unitHomEquiv, fullyFaithfulForget, homEquiv, homEquiv.trans, unitHomEquiv
-/
noncomputable def unitHomEquiv (M : SheafOfModules R) :
    (unit R ⟶ M) ≃ M.sections :=
  (fullyFaithfulForget R).homEquiv.trans M.val.unitHomEquiv

@[simp]
/--
lemma `unitHomEquiv_apply_coe` / 引理 `unitHomEquiv_apply_coe`

English:
lemma unitHomEquiv_apply_coe
  given: (M : SheafOfModules R) (f : unit R ⟶ M) (X : Cᵒᵖ)
  proof: rfl

中文:
引理 unitHomEquiv_apply_coe
  条件: (M : 模层 R) (f : unit R ⟶ M) (X : Cᵒᵖ)
  证明: rfl
-/
lemma unitHomEquiv_apply_coe (M : SheafOfModules R) (f : unit R ⟶ M) (X : Cᵒᵖ) :
    (M.unitHomEquiv f).val X = f.val.app X (1 : R.obj.obj X) := rfl

/--
lemma `unitHomEquiv_comp_apply` / 引理 `unitHomEquiv_comp_apply`

English:
lemma unitHomEquiv_comp_apply
  statement: {M N : SheafOfModules.{u} R}
  proof: rfl

中文:
引理 unitHomEquiv_comp_apply
  结论: {M N : 模层.{u} R}
  证明: rfl
-/
lemma unitHomEquiv_comp_apply {M N : SheafOfModules.{u} R}
    (f : unit R ⟶ M) (p : M ⟶ N) :
    N.unitHomEquiv (f ≫ p) = sectionsMap p (M.unitHomEquiv f) := rfl

/--
lemma `unitHomEquiv_symm_comp` / 引理 `unitHomEquiv_symm_comp`

English:
lemma unitHomEquiv_symm_comp
  given: {M N : SheafOfModules.{u} R} (s : M.sections) (p : M ⟶ N)
  proof: N.unitHomEquiv.injective (by simp [unitHomEquiv_comp_apply])

中文:
引理 unitHomEquiv_symm_comp
  条件: {M N : 模层.{u} R} (s : M.sections) (p : M ⟶ N)
  证明: N.unitHomEquiv.injective (by simp [unitHomEquiv_comp_apply])

Depends on / 依赖: N.unitHomEquiv.injective, injective, unitHomEquiv, unitHomEquiv_comp_apply
-/
lemma unitHomEquiv_symm_comp {M N : SheafOfModules.{u} R} (s : M.sections) (p : M ⟶ N) :
    M.unitHomEquiv.symm s ≫ p = N.unitHomEquiv.symm (sectionsMap p s) :=
  N.unitHomEquiv.injective (by simp [unitHomEquiv_comp_apply])

end SheafOfModules

namespace PresheafOfModules

variable (J)
variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M₁ M₂ : PresheafOfModules.{v} R} (f : M₁ ⟶ M₂)

/--
Definition of `IsLocallySurjective` / `IsLocallySurjective` 的定义

English:
abbreviation IsLocallySurjective
  signature: : Prop
  body: Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map f)

中文:
缩写 是LocallySurjective
  签名: : 命题
  定义体: Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map f)

Depends on / 依赖: IsColimit, IsLocallySurjective, Limits, Limits.IsColimit.module, Limits.colimit.isColimit, Limits.isColimitOfPreserves, M.map_smul, M.presheaf, Module, OpenNhds, OpenNhds.inclusion, Presheaf, Presheaf.IsLocallySurjective, PresheafOfModules, PresheafOfModules.toPresheaf, RingCat, colimit, inclusion, infer_instance, isColimit
-/
abbrev IsLocallySurjective : Prop :=
  Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map f)

/--
Definition of `IsLocallyInjective` / `IsLocallyInjective` 的定义

English:
abbreviation IsLocallyInjective
  signature: : Prop
  body: Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map f)

中文:
缩写 是LocallyInjective
  签名: : 命题
  定义体: Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map f)

Depends on / 依赖: IsLocallyInjective, Presheaf, Presheaf.IsLocallyInjective, PresheafOfModules, PresheafOfModules.toPresheaf, toPresheaf
-/
abbrev IsLocallyInjective : Prop :=
  Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R).map f)

variable {N : PresheafOfModules.{v} R} (hN : Presheaf.IsSheaf J N.presheaf)
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [IsLocallySurjective J f] [IsLocallyInjective J f]

variable {J}

set_option backward.isDefEq.respectTransparency false in
/-- The bijection `(M₂ ⟶ N) ≃ (M₁ ⟶ N)` induced by a locally bijective morphism
`f : M₁ ⟶ M₂` of presheaves of modules, when `N` is a sheaf. -/
@[simps]
/--
Definition of `homEquivOfIsLocallyBijective` / `homEquivOfIsLocallyBijective` 的定义

English:
definition homEquivOfIsLocallyBijective
  signature: : (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  body: f ≫ φ
  invFun ψ := homMk (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).symm
      ((PresheafOfModules.toPresheaf R).map ψ)) (by
        obtain ⟨φ, hφ⟩ := ((J.W_of_isLocallyBijective
          ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).surj

中文:
定义 homEquivOfIsLocallyBijective
  签名: : (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  定义体: f ≫ φ
  invFun ψ := homMk (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).symm
      ((PresheafOfModules.toPresheaf R).map ψ)) (by
        obtain ⟨φ, hφ⟩ := ((J.W_of_isLocallyBijective
          ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).surj
-/
noncomputable def homEquivOfIsLocallyBijective : (M₂ ⟶ N) ≃ (M₁ ⟶ N) where
  toFun φ := f ≫ φ
  invFun ψ := homMk (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).symm
      ((PresheafOfModules.toPresheaf R).map ψ)) (by
        obtain ⟨φ, hφ⟩ := ((J.W_of_isLocallyBijective
          ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).surjective
          ((PresheafOfModules.toPresheaf R).map ψ)
        simp only [← hφ, Equiv.symm_apply_apply]
        replace hφ : forall (Z : Cᵒᵖ) (x : M₁.obj Z), φ.app Z (f.app Z x) = ψ.app Z x :=
          fun Z x => CategoryTheory.congr_fun (congr_app hφ Z) x
        intro X r y
        apply hN.isSeparated _ _
          (Presheaf.imageSieve_mem J ((toPresheaf R).map f) y)
        rintro Y p ⟨x : M₁.obj _, hx : f.app _ x = M₂.map p.op y⟩
        have hφ' : forall (z : M₂.obj X), φ.app _ (M₂.map p.op z) =
            N.map p.op (φ.app _ z) := CategoryTheory.congr_fun (φ.naturality p.op)
        change N.map p.op (φ.app X (r • y)) = N.map p.op (r • φ.app X y)
        rw [← hφ']; rw [M₂.map_smul]; rw [← hx]; rw [← (f.app _).hom.map_smul]; rw [hφ]; rw [(ψ.app _).hom.map_smul]; rw [← hφ]; rw [hx]; rw [N.map_smul]; rw [hφ'])
  left_inv φ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).left_inv
      ((PresheafOfModules.toPresheaf R).map φ))
  right_inv ψ := (toPresheaf _).map_injective
    (((J.W_of_isLocallyBijective
      ((PresheafOfModules.toPresheaf R).map f)).homEquiv _ hN).right_inv
      ((PresheafOfModules.toPresheaf R).map ψ))

end PresheafOfModules
