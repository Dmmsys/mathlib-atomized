/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : obj ⟶ obj⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/

@[expose] public section


open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C] [HasShift C S]

/--
Definition of `DifferentialObject` / `DifferentialObject` 的定义

English:
structure DifferentialObject
  parameters: where
  axioms and operations (3):
    - obj : C
    - d : obj ⟶ obj⟦(1 : S)⟧
    - d_squared : d ≫ d⟦(1 : S)⟧' = 0  [default: by cat_disch]

中文:
结构 微分对象
  参数: where
  公理与运算 (3 个):
    - obj : C
    - d : obj ⟶ obj⟦(1 : S)⟧
    - d_squared : d ≫ d⟦(1 : S)⟧' = 0  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure DifferentialObject where
  /-- The underlying object of a differential object. -/
  obj : C
  /-- The differential of a differential object. -/
  d : obj ⟶ obj⟦(1 : S)⟧
  /-- The differential `d` satisfies that `d² = 0`. -/
  d_squared : d ≫ d⟦(1 : S)⟧' = 0 := by cat_disch

attribute [reassoc (attr := simp)] DifferentialObject.d_squared

variable {S C}

namespace DifferentialObject

/-- A morphism of differential objects is a morphism commuting with the differentials. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : DifferentialObject S C)
  axioms and operations (2):
    - f : X.obj ⟶ Y.obj
    - comm : X.d ≫ f⟦1⟧' = f ≫ Y.d  [default: by cat_disch]

中文:
结构 态射
  参数: (X Y : 微分对象 S C)
  公理与运算 (2 个):
    - f : X.obj ⟶ Y.obj
    - comm : X.d ≫ f⟦1⟧' = f ≫ Y.d  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (X Y : DifferentialObject S C) where
  /-- The morphism between underlying objects of the two differentiable objects. -/
  f : X.obj ⟶ Y.obj
  comm : X.d ≫ f⟦1⟧' = f ≫ Y.d := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

namespace Hom

/-- The identity morphism of a differential object. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : DifferentialObject S C)
  body: 𝟙 X.obj

中文:
定义 id
  签名: (X : 微分对象 S C)
  定义体: 𝟙 X.obj

Depends on / 依赖: X.obj
-/
def id (X : DifferentialObject S C) : Hom X X where
  f := 𝟙 X.obj

/-- The composition of morphisms of differential objects. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z)
  body: f.f ≫ g.f

中文:
定义 comp
  签名: {X Y Z : 微分对象 S C} (f : 态射 X Y) (g : 态射 Y Z)
  定义体: f.f ≫ g.f
-/
def comp {X Y Z : DifferentialObject S C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f

end Hom

/--
Instance `categoryOfDifferentialObjects` / 实例 `categoryOfDifferentialObjects`

English:
instance categoryOfDifferentialObjects
  signature: : Category (DifferentialObject S C) where
  body: Hom
  id := Hom.id
  comp f g := Hom.comp f g

@[ext]

中文:
实例 categoryOfDifferentialObjects
  签名: : 范畴 (微分对象 S C) where
  定义体: Hom
  id := Hom.id
  comp f g := Hom.comp f g

@[ext]
-/
instance categoryOfDifferentialObjects : Category (DifferentialObject S C) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch)
  statement: f = g
  proof: Hom.ext w

@[simp]

中文:
定理 ext
  条件: {A B : 微分对象 S C} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch)
  结论: f = g
  证明: Hom.ext w

@[simp]

Depends on / 依赖: Hom.ext, cat_disch
-/
theorem ext {A B : DifferentialObject S C} {f g : A ⟶ B} (w : f.f = g.f := by cat_disch) : f = g :=
  Hom.ext w

@[simp]
/--
theorem `id_f` / 定理 `id_f`

English:
theorem id_f
  given: (X : DifferentialObject S C)
  statement: (𝟙 X : X ⟶ X).f = 𝟙 X.obj
  proof: rfl

@[simp]

中文:
定理 id_f
  条件: (X : 微分对象 S C)
  结论: (𝟙 X : X ⟶ X).f = 𝟙 X.obj
  证明: rfl

@[simp]
-/
theorem id_f (X : DifferentialObject S C) : (𝟙 X : X ⟶ X).f = 𝟙 X.obj := rfl

@[simp]
/--
theorem `comp_f` / 定理 `comp_f`

English:
theorem comp_f
  given: {X Y Z : DifferentialObject S C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 comp_f
  条件: {X Y Z : 微分对象 S C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem comp_f {X Y Z : DifferentialObject S C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).f = f.f ≫ g.f :=
  rfl

@[simp]
/--
theorem `eqToHom_f` / 定理 `eqToHom_f`

English:
theorem eqToHom_f
  given: {X Y : DifferentialObject S C} (h : X = Y)
  proof: by
  subst h
  rw [eqToHom_refl]; rw [eqToHom_refl]
  rfl

中文:
定理 eqToHom_f
  条件: {X Y : 微分对象 S C} (h : X = Y)
  证明: by
  subst h
  rw [eqToHom_refl]; rw [eqToHom_refl]
  rfl

Depends on / 依赖: eqToHom_refl
-/
theorem eqToHom_f {X Y : DifferentialObject S C} (h : X = Y) :
    Hom.f (eqToHom h) = eqToHom (congr_arg _ h) := by
  subst h
  rw [eqToHom_refl]; rw [eqToHom_refl]
  rfl

variable (S C)

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : DifferentialObject S C ⥤ C where
  body: X.obj
  map f := f.f

中文:
定义 forget
  签名: : 微分对象 S C ⥤ C where
  定义体: X.obj
  map f := f.f

Depends on / 依赖: X.obj
-/
def forget : DifferentialObject S C ⥤ C where
  obj X := X.obj
  map f := f.f

/--
Instance `forget_faithful` / 实例 `forget_faithful`

English:
instance forget_faithful
  signature: : (forget S C).Faithful where

中文:
实例 forget_faithful
  签名: : (forget S C).忠实 where
-/
instance forget_faithful : (forget S C).Faithful where

variable {S C}

section
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]

instance {X Y : DifferentialObject S C} : Zero (X ⟶ Y) := ⟨{f := 0}⟩

@[simp]
/--
theorem `zero_f` / 定理 `zero_f`

English:
theorem zero_f
  given: (P Q : DifferentialObject S C)
  statement: (0 : P ⟶ Q).f = 0
  proof: rfl

中文:
定理 zero_f
  条件: (P Q : 微分对象 S C)
  结论: (0 : P ⟶ Q).f = 0
  证明: rfl
-/
theorem zero_f (P Q : DifferentialObject S C) : (0 : P ⟶ Q).f = 0 := rfl

/--
Instance `hasZeroMorphisms` / 实例 `hasZeroMorphisms`

English:
instance hasZeroMorphisms
  signature: : HasZeroMorphisms (DifferentialObject S C) where

中文:
实例 hasZeroMorphisms
  签名: : 有ZeroMorphisms (微分对象 S C) where
-/
instance hasZeroMorphisms : HasZeroMorphisms (DifferentialObject S C) where

end

/-- An isomorphism of differential objects gives an isomorphism of the underlying objects. -/
@[simps]
/--
Definition of `isoApp` / `isoApp` 的定义

English:
definition isoApp
  signature: {X Y : DifferentialObject S C} (f : X ≅ Y)
  body: f.hom.f
  inv := f.inv.f
  hom_inv_id := by rw [← comp_f, Iso.hom_inv_id, id_f]
  inv_hom_id := by rw [← comp_f, Iso.inv_hom_id, id_f]

@[simp]

中文:
定义 isoApp
  签名: {X Y : 微分对象 S C} (f : X ≅ Y)
  定义体: f.hom.f
  inv := f.inv.f
  hom_inv_id := by rw [← comp_f, Iso.hom_inv_id, id_f]
  inv_hom_id := by rw [← comp_f, Iso.inv_hom_id, id_f]

@[simp]

Depends on / 依赖: f.hom.f
-/
def isoApp {X Y : DifferentialObject S C} (f : X ≅ Y) : X.obj ≅ Y.obj where
  hom := f.hom.f
  inv := f.inv.f
  hom_inv_id := by rw [← comp_f, Iso.hom_inv_id, id_f]
  inv_hom_id := by rw [← comp_f, Iso.inv_hom_id, id_f]

@[simp]
/--
theorem `isoApp_refl` / 定理 `isoApp_refl`

English:
theorem isoApp_refl
  given: (X : DifferentialObject S C)
  statement: isoApp (Iso.refl X) = Iso.refl X.obj
  proof: rfl

@[simp]

中文:
定理 isoApp_refl
  条件: (X : 微分对象 S C)
  结论: isoApp (同构.refl X) = 同构.refl X.obj
  证明: rfl

@[simp]
-/
theorem isoApp_refl (X : DifferentialObject S C) : isoApp (Iso.refl X) = Iso.refl X.obj := rfl

@[simp]
/--
theorem `isoApp_symm` / 定理 `isoApp_symm`

English:
theorem isoApp_symm
  given: {X Y : DifferentialObject S C} (f : X ≅ Y)
  statement: isoApp f.symm = (isoApp f).symm
  proof: rfl

@[simp]

中文:
定理 isoApp_symm
  条件: {X Y : 微分对象 S C} (f : X ≅ Y)
  结论: isoApp f.symm = (isoApp f).symm
  证明: rfl

@[simp]
-/
theorem isoApp_symm {X Y : DifferentialObject S C} (f : X ≅ Y) : isoApp f.symm = (isoApp f).symm :=
  rfl

@[simp]
/--
theorem `isoApp_trans` / 定理 `isoApp_trans`

English:
theorem isoApp_trans
  given: {X Y Z : DifferentialObject S C} (f : X ≅ Y) (g : Y ≅ Z)
  proof: rfl

中文:
定理 isoApp_trans
  条件: {X Y Z : 微分对象 S C} (f : X ≅ Y) (g : Y ≅ Z)
  证明: rfl
-/
theorem isoApp_trans {X Y Z : DifferentialObject S C} (f : X ≅ Y) (g : Y ≅ Z) :
    isoApp (f ≪≫ g) = isoApp f ≪≫ isoApp g := rfl

/-- An isomorphism of differential objects can be constructed
from an isomorphism of the underlying objects that commutes with the differentials. -/
@[simps]
/--
Definition of `mkIso` / `mkIso` 的定义

English:
definition mkIso
  signature: {X Y : DifferentialObject S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d)
  body: ⟨f.hom, hf⟩
  inv := ⟨f.inv, by
    rw [← Functor.mapIso_inv]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Iso.eq_inv_comp]; rw [Functor.mapIso_hom]; rw [hf]⟩
  hom_inv_id := by ext1; dsimp; exact f.hom_inv_id
  inv_hom_id := by ext1; dsimp; exact f.inv_hom_id

中文:
定义 mkIso
  签名: {X Y : 微分对象 S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d)
  定义体: ⟨f.hom, hf⟩
  inv := ⟨f.inv, by
    rw [← Functor.mapIso_inv]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Iso.eq_inv_comp]; rw [Functor.mapIso_hom]; rw [hf]⟩
  hom_inv_id := by ext1; dsimp; exact f.hom_inv_id
  inv_hom_id := by ext1; dsimp; exact f.inv_hom_id

Depends on / 依赖: f.hom
-/
def mkIso {X Y : DifferentialObject S C} (f : X.obj ≅ Y.obj) (hf : X.d ≫ f.hom⟦1⟧' = f.hom ≫ Y.d) :
    X ≅ Y where
  hom := ⟨f.hom, hf⟩
  inv := ⟨f.inv, by
    rw [← Functor.mapIso_inv]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [Iso.eq_inv_comp]; rw [Functor.mapIso_hom]; rw [hf]⟩
  hom_inv_id := by ext1; dsimp; exact f.hom_inv_id
  inv_hom_id := by ext1; dsimp; exact f.inv_hom_id

end DifferentialObject

namespace Functor

universe v' u'

variable (D : Type u') [Category.{v'} D]
variable [HasZeroMorphisms D] [HasShift D S]

set_option backward.isDefEq.respectTransparency false in
/-- A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero
morphisms can be lifted to a functor `DifferentialObject S C ⥤ DifferentialObject S D`. -/
@[simps]
/--
Definition of `mapDifferentialObject` / `mapDifferentialObject` 的定义

English:
definition mapDifferentialObject
  signature: (F : C ⥤ D)
  body: { obj := F.obj X.obj
      d := F.map X.d ≫ η.app X.obj
      d_squared := by
        rw [Functor.map_comp]; rw [← Functor.comp_map F (shiftFunctor D (1 : S))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [Functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
 

中文:
定义 mapDifferentialObject
  签名: (F : C ⥤ D)
  定义体: { obj := F.obj X.obj
      d := F.map X.d ≫ η.app X.obj
      d_squared := by
        rw [Functor.map_comp]; rw [← Functor.comp_map F (shiftFunctor D (1 : S))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [Functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
 

Depends on / 依赖: F.map, F.map_comp, F.obj, Functor, Functor.comp_map, Functor.map_comp, X.d_squared, X.obj, comp_map, d_squared, f.comm, map_comp, naturality, shiftFunctor, slice_lhs, zero_comp
-/
def mapDifferentialObject (F : C ⥤ D)
    (η : (shiftFunctor C (1 : S)).comp F ⟶ F.comp (shiftFunctor D (1 : S)))
    (hF : forall c c', F.map (0 : c ⟶ c') = 0) : DifferentialObject S C ⥤ DifferentialObject S D where
  obj X :=
    { obj := F.obj X.obj
      d := F.map X.d ≫ η.app X.obj
      d_squared := by
        rw [Functor.map_comp]; rw [← Functor.comp_map F (shiftFunctor D (1 : S))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [Functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
        rw [zero_comp]; rw [zero_comp] }
  map f :=
    { f := F.map f.f
      comm := by
        dsimp
        slice_lhs 2 3 => rw [← Functor.comp_map F (shiftFunctor D (1 : S)), ← η.naturality f.f]
        slice_lhs 1 2 => rw [Functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
        rw [Category.assoc] }
  map_id := by intros; ext; simp
  map_comp := by intros; ext; simp

end Functor

end CategoryTheory

namespace CategoryTheory

namespace DifferentialObject

variable (S : Type*) [AddMonoidWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroObject C] [HasZeroMorphisms C] [HasShift C S]
variable [(shiftFunctor C (1 : S)).PreservesZeroMorphisms]

open scoped ZeroObject

/--
Instance `hasZeroObject` / 实例 `hasZeroObject`

English:
instance hasZeroObject
  signature: : HasZeroObject (DifferentialObject S C) where
  body: ⟨{ obj := 0, d := 0 },
    { unique_to := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩,
      unique_from := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩ }⟩

中文:
实例 hasZeroObject
  签名: : 有ZeroObject (微分对象 S C) where
  定义体: ⟨{ obj := 0, d := 0 },
    { unique_to := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩,
      unique_from := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩ }⟩
-/
instance hasZeroObject : HasZeroObject (DifferentialObject S C) where
  zero := ⟨{ obj := 0, d := 0 },
    { unique_to := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩,
      unique_from := fun X => ⟨⟨⟨{ f := 0 }⟩, fun f => by ext⟩⟩ }⟩

end DifferentialObject

namespace DifferentialObject

section ConcreteCategory

variable (S : Type*) [AddMonoidWithOne S]
variable (C : Type (u + 1)) [LargeCategory C] [HasZeroMorphisms C]
variable {FC : C -> C -> Type*} {CC : C -> Type*} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC] [HasShift C S]

/--
Definition of `HomSubtype` / `HomSubtype` 的定义

English:
abbreviation HomSubtype
  signature: (X Y : DifferentialObject S C)
  body: { f : FC X.obj Y.obj // X.d ≫ (ConcreteCategory.ofHom f)⟦1⟧' = (ConcreteCategory.ofHom f) ≫ Y.d }

中文:
缩写 HomSubtype
  签名: (X Y : 微分对象 S C)
  定义体: { f : FC X.obj Y.obj // X.d ≫ (ConcreteCategory.ofHom f)⟦1⟧' = (ConcreteCategory.ofHom f) ≫ Y.d }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, X.obj, Y.obj
-/
abbrev HomSubtype (X Y : DifferentialObject S C) :=
  { f : FC X.obj Y.obj // X.d ≫ (ConcreteCategory.ofHom f)⟦1⟧' = (ConcreteCategory.ofHom f) ≫ Y.d }

instance (X Y : DifferentialObject S C) :
    FunLike (HomSubtype S C X Y) (CC X.obj) (CC Y.obj) where
  coe f := f.1
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

/--
Instance `concreteCategoryOfDifferentialObjects` / 实例 `concreteCategoryOfDifferentialObjects`

English:
instance concreteCategoryOfDifferentialObjects
  signature: :
  body: ⟨ConcreteCategory.hom (C := C) f.1, by simp [ConcreteCategory.ofHom_hom]⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := C) f, by simpa [ConcreteCategory.hom_ofHom] using f.2⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  i

中文:
实例 concreteCategoryOfDifferentialObjects
  签名: :
  定义体: ⟨ConcreteCategory.hom (C := C) f.1, by simp [ConcreteCategory.ofHom_hom]⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := C) f, by simpa [ConcreteCategory.hom_ofHom] using f.2⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  i

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, ConcreteCategory.ofHom_hom, ofHom_hom
-/
instance concreteCategoryOfDifferentialObjects :
    ConcreteCategory (DifferentialObject S C) (HomSubtype S C) where
  hom f := ⟨ConcreteCategory.hom (C := C) f.1, by simp [ConcreteCategory.ofHom_hom]⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := C) f, by simpa [ConcreteCategory.hom_ofHom] using f.2⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  id_apply := ConcreteCategory.id_apply (C := C)
  comp_apply _ _ := ConcreteCategory.comp_apply (C := C) _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ (DifferentialObject S C) C
  body: forget S C

中文:
实例 :
  签名: 有Forget₂ (微分对象 S C) C
  定义体: forget S C

Depends on / 依赖: forget
-/
instance : HasForget₂ (DifferentialObject S C) C where
  forget₂ := forget S C

end ConcreteCategory

end DifferentialObject

/-! The category of differential objects itself has a shift functor. -/


namespace DifferentialObject

variable {S : Type*} [AddCommGroupWithOne S] (C : Type u) [Category.{v} C]
variable [HasZeroMorphisms C] [HasShift C S]

noncomputable section

set_option backward.defeqAttrib.useBackward true in
/-- The shift functor on `DifferentialObject S C`. -/
@[simps]
/--
Definition of `shiftFunctor` / `shiftFunctor` 的定义

English:
definition shiftFunctor
  signature: (n : S)
  body: { obj := X.obj⟦n⟧
      d := X.d⟦n⟧' ≫ (shiftComm _ _ _).hom
      d_squared := by
        rw [Functor.map_comp]; rw [Category.assoc]; rw [shiftComm_hom_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [X.d_squared]; rw [Functor.map_zero]; rw [zero_comp] }
  map f :=
    { f := f.f⟦n⟧'
      comm := b

中文:
定义 shiftFunctor
  签名: (n : S)
  定义体: { obj := X.obj⟦n⟧
      d := X.d⟦n⟧' ≫ (shiftComm _ _ _).hom
      d_squared := by
        rw [Functor.map_comp]; rw [Category.assoc]; rw [shiftComm_hom_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [X.d_squared]; rw [Functor.map_zero]; rw [zero_comp] }
  map f :=
    { f := f.f⟦n⟧'
      comm := b

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Functor.map_comp_assoc, Functor.map_id, Functor.map_zero, X.d_squared, X.obj, d_squared, f.comm, map_comp, map_comp_assoc, map_id, map_zero, shiftComm, shiftComm_hom_comp, shiftComm_hom_comp_assoc, zero_comp
-/
def shiftFunctor (n : S) : DifferentialObject S C ⥤ DifferentialObject S C where
  obj X :=
    { obj := X.obj⟦n⟧
      d := X.d⟦n⟧' ≫ (shiftComm _ _ _).hom
      d_squared := by
        rw [Functor.map_comp]; rw [Category.assoc]; rw [shiftComm_hom_comp_assoc]; rw [← Functor.map_comp_assoc]; rw [X.d_squared]; rw [Functor.map_zero]; rw [zero_comp] }
  map f :=
    { f := f.f⟦n⟧'
      comm := by
        dsimp
        rw [Category.assoc]
        erw [shiftComm_hom_comp]
        rw [← Functor.map_comp_assoc]; rw [f.comm]; rw [Functor.map_comp_assoc]
        rfl }
  map_id X := by ext1; dsimp; rw [Functor.map_id]
  map_comp f g := by ext1; dsimp; rw [Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
/-- The shift functor on `DifferentialObject S C` is additive. -/
@[simps!]
nonrec def shiftFunctorAdd (m n : S) :
    shiftFunctor C (m + n) ≅ shiftFunctor C m ⋙ shiftFunctor C n := by
  refine NatIso.ofComponents (fun X => mkIso (shiftAdd X.obj _ _) ?_) (fun f => ?_)
  · dsimp
    rw [← cancel_epi ((shiftFunctorAdd C m n).inv.app X.obj)]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← NatTrans.naturality_assoc]
    dsimp
    simp only [Functor.map_comp, Category.assoc,
      shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app 1 m n X.obj,
      Iso.inv_hom_id_app_assoc]
  · ext; dsimp; exact NatTrans.naturality _ _

section

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The shift by zero is naturally isomorphic to the identity. -/
@[simps!]
/--
Definition of `shiftZero` / `shiftZero` 的定义

English:
definition shiftZero
  signature: : shiftFunctor C (0 : S) ≅ 𝟭 (DifferentialObject S C)
  body: by
  refine NatIso.ofComponents (fun X => mkIso ((shiftFunctorZero C S).app X.obj) ?_) (fun f => ?_)
  · erw [← NatTrans.naturality]
    dsimp
    simp only [shiftFunctorZero_hom_app_shift, Category.assoc]
  · cat_disch

中文:
定义 shiftZero
  签名: : shiftFunctor C (0 : S) ≅ 𝟭 (微分对象 S C)
  定义体: by
  refine NatIso.ofComponents (fun X => mkIso ((shiftFunctorZero C S).app X.obj) ?_) (fun f => ?_)
  · erw [← NatTrans.naturality]
    dsimp
    simp only [shiftFunctorZero_hom_app_shift, Category.assoc]
  · cat_disch

Depends on / 依赖: Category, Category.assoc, NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality, X.obj, cat_disch, naturality, ofComponents, shiftFunctorZero, shiftFunctorZero_hom_app_shift
-/
def shiftZero : shiftFunctor C (0 : S) ≅ 𝟭 (DifferentialObject S C) := by
  refine NatIso.ofComponents (fun X => mkIso ((shiftFunctorZero C S).app X.obj) ?_) (fun f => ?_)
  · erw [← NatTrans.naturality]
    dsimp
    simp only [shiftFunctorZero_hom_app_shift, Category.assoc]
  · cat_disch

end

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasShift (DifferentialObject S C) S
  body: hasShiftMk _ _
    { F := shiftFunctor C
      zero := shiftZero C
      add := shiftFunctorAdd C
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext1
        convert! shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj
        dsimp [shiftFunctorAdd']
        simp
      zero_add_hom_app := fun n X => 

中文:
实例 :
  签名: 有Shift (微分对象 S C) S
  定义体: hasShiftMk _ _
    { F := shiftFunctor C
      zero := shiftZero C
      add := shiftFunctorAdd C
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext1
        convert! shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj
        dsimp [shiftFunctorAdd']
        simp
      zero_add_hom_app := fun n X => 

Depends on / 依赖: X.obj, add_zero_hom_app, assoc_hom_app, convert, hasShiftMk, shiftFunctor, shiftFunctorAdd, shiftFunctorAdd_add_zero_hom_app, shiftFunctorAdd_assoc_hom_app, shiftFunctorAdd_zero_add_hom_app, shiftZero, zero_add_hom_app
-/
instance : HasShift (DifferentialObject S C) S :=
  hasShiftMk _ _
    { F := shiftFunctor C
      zero := shiftZero C
      add := shiftFunctorAdd C
      assoc_hom_app := fun m₁ m₂ m₃ X => by
        ext1
        convert! shiftFunctorAdd_assoc_hom_app m₁ m₂ m₃ X.obj
        dsimp [shiftFunctorAdd']
        simp
      zero_add_hom_app := fun n X => by
        ext1
        convert! shiftFunctorAdd_zero_add_hom_app n X.obj
        simp
      add_zero_hom_app := fun n X => by
        ext1
        convert! shiftFunctorAdd_add_zero_hom_app n X.obj
        simp }

end

end DifferentialObject

end CategoryTheory
