/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Limits -- shake: keep (used in `example` only)
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.UniformSpace.Completion

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

@[expose] public section


universe u

open CategoryTheory


/--
Definition of `UniformSpaceCat` / `UniformSpaceCat` 的定义

English:
structure UniformSpaceCat
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [str : UniformSpace carrier]

中文:
结构 一致空间范畴
  参数: : 类型 (u + 1) where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [str : 一致空间 carrier]
-/
structure UniformSpaceCat : Type (u + 1) where
  /-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
  of ::
  /-- The underlying uniform space. -/
  carrier : Type u
  [str : UniformSpace carrier]

attribute [instance] UniformSpaceCat.str

namespace UniformSpaceCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort UniformSpaceCat Type*
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort 一致空间范畴 类型
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort UniformSpaceCat Type* :=
  ⟨carrier⟩

/-- A bundled uniform continuous map. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : UniformSpaceCat)
  axioms and operations (1):
    - hom' : { f : X -> Y // UniformContinuous f }

中文:
结构 态射
  参数: (X Y : 一致空间范畴)
  公理与运算 (1 个):
    - hom' : { f : X -> Y // 一致连续 f }
-/
structure Hom (X Y : UniformSpaceCat) where
  /-- The underlying `UniformContinuous` function. -/
  hom' : { f : X -> Y // UniformContinuous f }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory.{u} UniformSpaceCat.{u}
  body: Hom
  id X := ⟨id, uniformContinuous_id⟩
  comp f g := ⟨⟨g.hom'.val ∘ f.hom'.val, g.hom'.property.comp f.hom'.property⟩⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; ext; simp

中文:
实例 :
  签名: 大范畴.{u} 一致空间范畴.{u}
  定义体: Hom
  id X := ⟨id, uniformContinuous_id⟩
  comp f g := ⟨⟨g.hom'.val ∘ f.hom'.val, g.hom'.property.comp f.hom'.property⟩⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; ext; simp
-/
instance : LargeCategory.{u} UniformSpaceCat.{u} where
  Hom := Hom
  id X := ⟨id, uniformContinuous_id⟩
  comp f g := ⟨⟨g.hom'.val ∘ f.hom'.val, g.hom'.property.comp f.hom'.property⟩⟩
  id_comp := by intros; apply Hom.ext; simp
  comp_id := by intros; apply Hom.ext; simp
  assoc := by intros; apply Hom.ext; ext; simp

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: (X Y : UniformSpaceCat)
  body: Subtype.val
  coe_injective _ _ h := Subtype.ext h

中文:
实例 instFunLike
  签名: (X Y : 一致空间范畴)
  定义体: Subtype.val
  coe_injective _ _ h := Subtype.ext h

Depends on / 依赖: Subtype, Subtype.val
-/
instance instFunLike (X Y : UniformSpaceCat) :
    FunLike { f : X -> Y // UniformContinuous f } X Y where
  coe := Subtype.val
  coe_injective _ _ h := Subtype.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory UniformSpaceCat ({ f : · -> · // UniformContinuous f })
  body: f.hom'
  ofHom f := ⟨f⟩

中文:
实例 :
  签名: 余ncrete范畴 一致空间范畴 ({ f : · -> · // 一致连续 f })
  定义体: f.hom'
  ofHom f := ⟨f⟩

Depends on / 依赖: f.hom
-/
instance : ConcreteCategory UniformSpaceCat ({ f : · -> · // UniformContinuous f }) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : UniformSpaceCat} (f : Hom X Y)
  body: ConcreteCategory.hom (C := UniformSpaceCat) f

中文:
缩写 态射.hom
  签名: {X Y : 一致空间范畴} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := UniformSpaceCat) f
-/
abbrev Hom.hom {X Y : UniformSpaceCat} (f : Hom X Y) :=
  ConcreteCategory.hom (C := UniformSpaceCat) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [UniformSpace X] [UniformSpace Y]
  body: ConcreteCategory.ofHom f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [一致空间 X] [一致空间 Y]
  定义体: ConcreteCategory.ofHom f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X -> Y // UniformContinuous f }) : of X ⟶ of Y :=
  ConcreteCategory.ofHom f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited UniformSpaceCat
  body: ⟨UniformSpaceCat.of Empty⟩

中文:
实例 :
  签名: 可居 一致空间范畴
  定义体: ⟨UniformSpaceCat.of Empty⟩

Depends on / 依赖: UniformSpaceCat, UniformSpaceCat.of
-/
instance : Inhabited UniformSpaceCat :=
  ⟨UniformSpaceCat.of Empty⟩

/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [UniformSpace X]
  statement: (of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [一致空间 X]
  结论: (of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

@[simp]
/--
theorem `hom_comp` / 定理 `hom_comp`

English:
theorem hom_comp
  given: {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 hom_comp
  条件: {X Y Z : 一致空间范畴} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem hom_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = ⟨g ∘ f, g.hom.prop.comp f.hom.prop⟩ :=
  rfl

@[simp]
/--
theorem `hom_id` / 定理 `hom_id`

English:
theorem hom_id
  given: (X : UniformSpaceCat)
  statement: (𝟙 X : X ⟶ X).hom = ⟨id, uniformContinuous_id⟩
  proof: rfl

@[simp]

中文:
定理 hom_id
  条件: (X : 一致空间范畴)
  结论: (𝟙 X : X ⟶ X).hom = ⟨id, uniformContinuous_id⟩
  证明: rfl

@[simp]
-/
theorem hom_id (X : UniformSpaceCat) : (𝟙 X : X ⟶ X).hom = ⟨id, uniformContinuous_id⟩ :=
  rfl

@[simp]
/--
theorem `hom_ofHom` / 定理 `hom_ofHom`

English:
theorem hom_ofHom
  statement: {X Y : Type u} [UniformSpace X] [UniformSpace Y]
  proof: rfl

中文:
定理 hom_ofHom
  结论: {X Y : 类型u} [一致空间 X] [一致空间 Y]
  证明: rfl
-/
theorem hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X -> Y // UniformContinuous f }) : (ofHom f).hom = f :=
  rfl

/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z)
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

中文:
定理 coe_comp
  条件: {X Y Z : 一致空间范畴} (f : X ⟶ Y) (g : Y ⟶ Z)
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl
-/
theorem coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X -> Z) = g ∘ f :=
  rfl

/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  given: (X : UniformSpaceCat)
  statement: (𝟙 X : X -> X) = id
  proof: rfl

中文:
定理 coe_id
  条件: (X : 一致空间范畴)
  结论: (𝟙 X : X -> X) = id
  证明: rfl
-/
theorem coe_id (X : UniformSpaceCat) : (𝟙 X : X -> X) = id :=
  rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {X Y : UniformSpaceCat} (f : X -> Y) (hf : UniformContinuous f)
  proof: rfl

@[ext]

中文:
定理 coe_mk
  条件: {X Y : 一致空间范畴} (f : X -> Y) (hf : 一致连续 f)
  证明: rfl

@[ext]
-/
theorem coe_mk {X Y : UniformSpaceCat} (f : X -> Y) (hf : UniformContinuous f) :
    (⟨f, hf⟩ : X ⟶ Y).hom = f :=
  rfl

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {X Y : UniformSpaceCat} {f g : X ⟶ Y} (h : (f : X -> Y) = g)
  statement: f = g
  proof: Hom.ext (Subtype.ext h)

中文:
定理 hom_ext
  条件: {X Y : 一致空间范畴} {f g : X ⟶ Y} (h : (f : X -> Y) = g)
  结论: f = g
  证明: Hom.ext (Subtype.ext h)

Depends on / 依赖: Hom.ext, Subtype, Subtype.ext
-/
theorem hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} (h : (f : X -> Y) = g) : f = g :=
  Hom.ext (Subtype.ext h)

/--
Instance `hasForgetToTop` / 实例 `hasForgetToTop`

English:
instance hasForgetToTop
  signature: : HasForget₂ UniformSpaceCat.{u} TopCat.{u} where
  body: { obj := fun X => TopCat.of X
      map := fun f => TopCat.ofHom
        { toFun := f
          continuous_toFun := f.hom.property.continuous } }

中文:
实例 hasForgetToTop
  签名: : 有Forget₂ 一致空间范畴.{u} 顶元素范畴.{u} where
  定义体: { obj := fun X => TopCat.of X
      map := fun f => TopCat.ofHom
        { toFun := f
          continuous_toFun := f.hom.property.continuous } }

Depends on / 依赖: TopCat, TopCat.of, TopCat.ofHom, continuous, continuous_toFun, f.hom.property.continuous, property
-/
instance hasForgetToTop : HasForget₂ UniformSpaceCat.{u} TopCat.{u} where
  forget₂ :=
    { obj := fun X => TopCat.of X
      map := fun f => TopCat.ofHom
        { toFun := f
          continuous_toFun := f.hom.property.continuous } }

end UniformSpaceCat

/--
Definition of `CpltSepUniformSpace` / `CpltSepUniformSpace` 的定义

English:
structure CpltSepUniformSpace
  parameters: where
  axioms and operations (4):
    - α : Type u
    - [isUniformSpace : UniformSpace α]
    - [isCompleteSpace : CompleteSpace α]
    - [isT0 : T0Space α]

中文:
结构 CpltSepUniform空间
  参数: where
  公理与运算 (4 个):
    - α : 类型u
    - [isUniformSpace : 一致空间 α]
    - [isCompleteSpace : 完备空间 α]
    - [isT0 : T0空间 α]
-/
structure CpltSepUniformSpace where
  /-- The underlying space -/
  α : Type u
  [isUniformSpace : UniformSpace α]
  [isCompleteSpace : CompleteSpace α]
  [isT0 : T0Space α]

namespace CpltSepUniformSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CpltSepUniformSpace (Type u)
  body: ⟨CpltSepUniformSpace.α⟩

中文:
实例 :
  签名: CoeSort CpltSepUniform空间 (类型u)
  定义体: ⟨CpltSepUniformSpace.α⟩

Depends on / 依赖: CpltSepUniformSpace
-/
instance : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] isUniformSpace isCompleteSpace isT0

/--
Definition of `toUniformSpace` / `toUniformSpace` 的定义

English:
definition toUniformSpace
  signature: (X : CpltSepUniformSpace)
  body: UniformSpaceCat.of X

中文:
定义 toUniformSpace
  签名: (X : CpltSepUniform空间)
  定义体: UniformSpaceCat.of X

Depends on / 依赖: UniformSpaceCat, UniformSpaceCat.of
-/
def toUniformSpace (X : CpltSepUniformSpace) : UniformSpaceCat :=
  UniformSpaceCat.of X

/--
Instance `completeSpace` / 实例 `completeSpace`

English:
instance completeSpace
  signature: (X : CpltSepUniformSpace)
  body: CpltSepUniformSpace.isCompleteSpace X

中文:
实例 completeSpace
  签名: (X : CpltSepUniform空间)
  定义体: CpltSepUniformSpace.isCompleteSpace X

Depends on / 依赖: CpltSepUniformSpace, CpltSepUniformSpace.isCompleteSpace, isCompleteSpace
-/
instance completeSpace (X : CpltSepUniformSpace) : CompleteSpace (toUniformSpace X).carrier :=
  CpltSepUniformSpace.isCompleteSpace X

/--
Instance `t0Space` / 实例 `t0Space`

English:
instance t0Space
  signature: (X : CpltSepUniformSpace)
  body: CpltSepUniformSpace.isT0 X

中文:
实例 t0Space
  签名: (X : CpltSepUniform空间)
  定义体: CpltSepUniformSpace.isT0 X

Depends on / 依赖: CpltSepUniformSpace, CpltSepUniformSpace.isT0
-/
instance t0Space (X : CpltSepUniformSpace) : T0Space (toUniformSpace X).carrier :=
  CpltSepUniformSpace.isT0 X

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X]
  body: ⟨X⟩

@[simp]

中文:
定义 of
  签名: (X : 类型u) [一致空间 X] [完备空间 X] [T0空间 X]
  定义体: ⟨X⟩

@[simp]
-/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] : CpltSepUniformSpace :=
  ⟨X⟩

@[simp]
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X]
  proof: rfl

中文:
定理 coe_of
  条件: (X : 类型u) [一致空间 X] [完备空间 X] [T0空间 X]
  证明: rfl
-/
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [T0Space X] :
    (of X : Type u) = X :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CpltSepUniformSpace
  body: ⟨CpltSepUniformSpace.of Empty⟩

中文:
实例 :
  签名: 可居 CpltSepUniform空间
  定义体: ⟨CpltSepUniformSpace.of Empty⟩

Depends on / 依赖: CpltSepUniformSpace, CpltSepUniformSpace.of
-/
instance : Inhabited CpltSepUniformSpace :=
  ⟨CpltSepUniformSpace.of Empty⟩

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : LargeCategory CpltSepUniformSpace
  body: inferInstanceAs Category (InducedCategory _ toUniformSpace)

中文:
实例 category
  签名: : 大范畴 CpltSepUniform空间
  定义体: inferInstanceAs Category (InducedCategory _ toUniformSpace)

Depends on / 依赖: Category, InducedCategory, toUniformSpace
-/
instance category : LargeCategory CpltSepUniformSpace :=
inferInstanceAs Category (InducedCategory _ toUniformSpace)

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: (X Y : CpltSepUniformSpace)
  body: Subtype.val
  coe_injective _ _ h := Subtype.ext h

中文:
实例 instFunLike
  签名: (X Y : CpltSepUniform空间)
  定义体: Subtype.val
  coe_injective _ _ h := Subtype.ext h

Depends on / 依赖: Subtype, Subtype.val
-/
instance instFunLike (X Y : CpltSepUniformSpace) :
    FunLike { f : X -> Y // UniformContinuous f } X Y where
  coe := Subtype.val
  coe_injective _ _ h := Subtype.ext h

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `concreteCategory` / 实例 `concreteCategory`

English:
instance concreteCategory
  signature: : ConcreteCategory CpltSepUniformSpace
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toUniformSpace) _

中文:
实例 concreteCategory
  签名: : 余ncrete范畴 CpltSepUniform空间
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toUniformSpace) _

Depends on / 依赖: ConcreteCategory, InducedCategory, toUniformSpace
-/
instance concreteCategory : ConcreteCategory CpltSepUniformSpace
    ({ f : · -> · // UniformContinuous f }) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toUniformSpace) _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `hasForgetToUniformSpace` / 实例 `hasForgetToUniformSpace`

English:
instance hasForgetToUniformSpace
  signature: : HasForget₂ CpltSepUniformSpace UniformSpaceCat
  body: inferInstanceAs HasForget₂ (InducedCategory _ toUniformSpace) _

中文:
实例 hasForgetToUniformSpace
  签名: : 有Forget₂ CpltSepUniform空间 一致空间范畴
  定义体: inferInstanceAs HasForget₂ (InducedCategory _ toUniformSpace) _

Depends on / 依赖: InducedCategory, toUniformSpace
-/
instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpace UniformSpaceCat :=
inferInstanceAs HasForget₂ (InducedCategory _ toUniformSpace) _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `hom_comp` / 定理 `hom_comp`

English:
theorem hom_comp
  given: {X Y Z : CpltSepUniformSpace} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 hom_comp
  条件: {X Y Z : CpltSepUniform空间} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem hom_comp {X Y Z : CpltSepUniformSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ConcreteCategory.hom (f ≫ g) = ⟨g ∘ f, g.hom.hom.prop.comp f.hom.hom.prop⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `hom_id` / 定理 `hom_id`

English:
theorem hom_id
  given: (X : CpltSepUniformSpace)
  proof: rfl

@[simp]

中文:
定理 hom_id
  条件: (X : CpltSepUniform空间)
  证明: rfl

@[simp]
-/
theorem hom_id (X : CpltSepUniformSpace) :
    ConcreteCategory.hom (𝟙 X : X ⟶ X) = ⟨id, uniformContinuous_id⟩ :=
  rfl

@[simp]
/--
theorem `hom_ofHom` / 定理 `hom_ofHom`

English:
theorem hom_ofHom
  statement: {X Y : Type u} [UniformSpace X] [UniformSpace Y]
  proof: rfl

中文:
定理 hom_ofHom
  结论: {X Y : 类型u} [一致空间 X] [一致空间 Y]
  证明: rfl
-/
theorem hom_ofHom {X Y : Type u} [UniformSpace X] [UniformSpace Y]
    (f : { f : X -> Y // UniformContinuous f }) : (UniformSpaceCat.ofHom f).hom = f :=
  rfl

end CpltSepUniformSpace

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpace

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor turning uniform spaces into complete separated uniform spaces. -/
@[simps map]
/--
Definition of `completionFunctor` / `completionFunctor` 的定义

English:
definition completionFunctor
  signature: : UniformSpaceCat ⥤ CpltSepUniformSpace where
  body: CpltSepUniformSpace.of (Completion X)
  map f := ConcreteCategory.ofHom ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id _ := InducedCategory.hom_ext (hom_ext (by apply Completion.map_id))
  map_comp f g := InducedCategory.hom_ext (hom_ext (by
    exact (Completion.map_comp g.hom.property f.hom.property).symm))

中文:
定义 completionFunctor
  签名: : 一致空间范畴 ⥤ CpltSepUniform空间 where
  定义体: CpltSepUniformSpace.of (Completion X)
  map f := ConcreteCategory.ofHom ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id _ := InducedCategory.hom_ext (hom_ext (by apply Completion.map_id))
  map_comp f g := InducedCategory.hom_ext (hom_ext (by
    exact (Completion.map_comp g.hom.property f.hom.property).symm))

Depends on / 依赖: Completion, CpltSepUniformSpace, CpltSepUniformSpace.of
-/
noncomputable def completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpace where
  obj X := CpltSepUniformSpace.of (Completion X)
  map f := ConcreteCategory.ofHom ⟨Completion.map f.1, Completion.uniformContinuous_map⟩
  map_id _ := InducedCategory.hom_ext (hom_ext (by apply Completion.map_id))
  map_comp f g := InducedCategory.hom_ext (hom_ext (by
    exact (Completion.map_comp g.hom.property f.hom.property).symm))

/--
Definition of `completionHom` / `completionHom` 的定义

English:
definition completionHom
  signature: (X : UniformSpaceCat)
  body: ((↑) : X -> Completion X)
  hom'.property := Completion.uniformContinuous_coe X

@[simp]

中文:
定义 completionHom
  签名: (X : 一致空间范畴)
  定义体: ((↑) : X -> Completion X)
  hom'.property := Completion.uniformContinuous_coe X

@[simp]

Depends on / 依赖: Completion
-/
noncomputable def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj (completionFunctor.obj X) where
  hom'.val := ((↑) : X -> Completion X)
  hom'.property := Completion.uniformContinuous_coe X

@[simp]
/--
theorem `completionHom_val` / 定理 `completionHom_val`

English:
theorem completionHom_val
  given: (X : UniformSpaceCat) (x)
  statement: (completionHom X) x = (x : Completion X)
  proof: rfl

中文:
定理 completionHom_val
  条件: (X : 一致空间范畴) (x)
  结论: (completionHom X) x = (x : 完备化 X)
  证明: rfl
-/
theorem completionHom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : Completion X) :=
  rfl

/--
Definition of `extensionHom` / `extensionHom` 的定义

English:
definition extensionHom
  signature: {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
  body: ConcreteCategory.ofHom ⟨Completion.extension f, Completion.uniformContinuous_extension⟩

@[simp]

中文:
定义 extensionHom
  签名: {X : 一致空间范畴} {Y : CpltSepUniform空间}
  定义体: ConcreteCategory.ofHom ⟨Completion.extension f, Completion.uniformContinuous_extension⟩

@[simp]

Depends on / 依赖: Completion, Completion.extension, Completion.uniformContinuous_extension, ConcreteCategory, ConcreteCategory.ofHom, extension, uniformContinuous_extension
-/
noncomputable def extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceCat).obj Y) :
    completionFunctor.obj X ⟶ Y :=
  ConcreteCategory.ofHom ⟨Completion.extension f, Completion.uniformContinuous_extension⟩

@[simp]
/--
theorem `extensionHom_val` / 定理 `extensionHom_val`

English:
theorem extensionHom_val
  statement: {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
  proof: rfl

@[simp]

中文:
定理 extensionHom_val
  结论: {X : 一致空间范畴} {Y : CpltSepUniform空间}
  证明: rfl

@[simp]
-/
theorem extensionHom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : X ⟶ (forget₂ _ _).obj Y) (x) : (extensionHom f) x = Completion.extension f x :=
  rfl

@[simp]
/--
theorem `extension_comp_hom` / 定理 `extension_comp_hom`

English:
theorem extension_comp_hom
  statement: {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
  proof: by
  ext x
  exact congr_fun (Completion.extension_comp_coe f.hom.property) x

中文:
定理 extension_comp_hom
  结论: {X : 一致空间范畴} {Y : CpltSepUniform空间}
  证明: by
  ext x
  exact congr_fun (Completion.extension_comp_coe f.hom.property) x

Depends on / 依赖: Completion, Completion.extension_comp_coe, congr_fun, extension_comp_coe, f.hom.property, property
-/
theorem extension_comp_hom {X : UniformSpaceCat} {Y : CpltSepUniformSpace}
    (f : toUniformSpace (CpltSepUniformSpace.of (Completion X)) ⟶ toUniformSpace Y) :
    (extensionHom (completionHom X ≫ f)).hom = f := by
  ext x
  exact congr_fun (Completion.extension_comp_coe f.hom.property) x

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f.hom
          invFun := fun f => extensionHom f
          left_inv := fun f => InducedCategory.hom_ext (by simp)
          right_inv := fun f => by
            ext x
            rcases f with ⟨⟨_, _⟩⟩
            exact @Completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.t0Space _)
              ‹_› _ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        ext x
        dsimp [-Function.comp_apply]
        erw [Completion.extension_map (γ := Y) g.hom.2 f.hom.2]
        rfl }

中文:
定义 adj
  签名: : completionFunctor ⊣ forget₂ CpltSepUniform空间 一致空间范畴
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f.hom
          invFun := fun f => extensionHom f
          left_inv := fun f => InducedCategory.hom_ext (by simp)
          right_inv := fun f => by
            ext x
            rcases f with ⟨⟨_, _⟩⟩
            exact @Completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.t0Space _)
              ‹_› _ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        ext x
        dsimp [-Function.comp_apply]
        erw [Completion.extension_map (γ := Y) g.hom.2 f.hom.2]
        rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Completion, Completion.extension_coe, Completion.extension_map, CpltSepUniformSpace, CpltSepUniformSpace.t0Space, Function, Function.comp_apply, InducedCategory, InducedCategory.hom_ext, comp_apply, completionHom, extensionHom, extension_coe, extension_map, f.hom, g.hom, homEquiv, homEquiv_naturality_left_symm
-/
noncomputable def adj : completionFunctor ⊣ forget₂ CpltSepUniformSpace UniformSpaceCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f.hom
          invFun := fun f => extensionHom f
          left_inv := fun f => InducedCategory.hom_ext (by simp)
          right_inv := fun f => by
            ext x
            rcases f with ⟨⟨_, _⟩⟩
            exact @Completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.t0Space _)
              ‹_› _ }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        ext x
        dsimp [-Function.comp_apply]
        erw [Completion.extension_map (γ := Y) g.hom.2 f.hom.2]
        rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Reflective (forget₂ CpltSepUniformSpace UniformSpaceCat)
  body: completionFunctor
  adj := adj
  map_surjective f := ⟨ConcreteCategory.ofHom f.hom, rfl⟩

中文:
实例 :
  签名: 反射 (forget₂ CpltSepUniform空间 一致空间范畴)
  定义体: completionFunctor
  adj := adj
  map_surjective f := ⟨ConcreteCategory.ofHom f.hom, rfl⟩

Depends on / 依赖: completionFunctor
-/
noncomputable instance : Reflective (forget₂ CpltSepUniformSpace UniformSpaceCat) where
  L := completionFunctor
  adj := adj
  map_surjective f := ⟨ConcreteCategory.ofHom f.hom, rfl⟩

open CategoryTheory.Limits

-- TODO Once someone defines `HasLimits UniformSpace`, turn this into an instance.
example [HasLimits.{u} UniformSpaceCat.{u}] : HasLimits.{u} CpltSepUniformSpace.{u} :=
hasLimits_of_reflective forget₂ CpltSepUniformSpace UniformSpaceCat.{u}

end UniformSpaceCat
