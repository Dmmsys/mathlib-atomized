/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`).

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Functor Topology

universe u v w' w

variable (C : Type u) [Category.{v} C]


-- We could enable the following line:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opposite
-- but may need
-- https://github.com/leanprover-community/aesop/issues/59

namespace AlgebraicGeometry

/-- A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s. -/
/-
**AlgebraicGeometry.SheafedSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max (max u (u_1 
+ 1)) v)
参数：max u (u_1 + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SheafedSpace C` is a topological space equipped with a sheaf of `C`s.
-/
structure SheafedSpace extends PresheafedSpace C where
  /-- A sheafed space is a presheafed space which happens to be a sheaf. -/
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpace

/-
**AlgebraicGeometry.SheafedSpace.coeCarrier** 是 Mathlib 中的一个实例，位于命名空间 `Algebraic
Geometry.SheafedSpace`。
形式化陈述：coeCarrier : CoeOut (SheafedSpace C) TopCat where coe X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeCarrier : CoeOut (SheafedSpace C) TopCat where coe X := X.carrier
/-
**AlgebraicGeometry.SheafedSpace.coeSort** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeo
metry.SheafedSpace`。
形式化陈述：coeSort : CoeSort (SheafedSpace C) Type* where coe X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeSort : CoeSort (SheafedSpace C) Type* where
  coe X := X.1

/-- Extract the `sheaf C (X : Top)` from a `SheafedSpace C`. -/
/-
**AlgebraicGeometry.SheafedSpace.sheaf** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.SheafedSpace`。
形式化陈述：sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat)
参数：X : SheafedSpace C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.IsSheaf`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] (self : AlgebraicGeometry.SheafedSpace C),   self.presh
eaf.IsSheaf

--- 原说明 ---
Extract the `sheaf C (X : Top)` from a `SheafedSpace C`.
-/
def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat) :=
  ⟨X.presheaf, X.IsSheaf⟩

/-- Not `@[simp]` since it already reduces to `carrier = carrier`. -/
/-
**AlgebraicGeometry.SheafedSpace.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.SheafedSpace`。
形式化陈述：mk_coe (carrier) (presheaf) (h) : (({ carrier presheaf IsSheaf
参数：carrier；presheaf；h。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Not `@[simp]` since it already reduces to `carrier = carrier`.
-/
theorem mk_coe (carrier) (presheaf) (h) :
    (({ carrier
        presheaf
        IsSheaf := h } : SheafedSpace C) : TopCat) = carrier :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : SheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

/-- The trivial `unit`-valued sheaf on any topological space. -/
/-
**AlgebraicGeometry.SheafedSpace.unit** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.SheafedSpace`。
形式化陈述：unit (X : TopCat) : SheafedSpace (Discrete Unit)
参数：X : TopCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial `unit`-valued sheaf on any topological space.
-/
def unit (X : TopCat) : SheafedSpace (Discrete Unit) :=
  { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SheafedSpace (Discrete Unit)) :=
  ⟨unit (TopCat.of PEmpty)⟩
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (SheafedSpace C) :=
  inferInstanceAs <| Category (InducedCategory (PresheafedSpace C) SheafedSpace.toPresheafedSpace)

@[ext (iff := false)]
/-
**AlgebraicGeometry.SheafedSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.SheafedSpace`。
形式化陈述：ext {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.hom.base = β.hom.base) (h 
: α.hom.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.hom.c) : α = β
参数：α β : X ⟶ Y；w : α.hom.base = β.hom.base；h : α.hom.c ≫ whiskerRight (eqToHom (
by rw [w])) _ = β.hom.c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.InducedCategory.hom_ext`：hom_ext {X Y : InducedCategory D
 F} {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ext`：ext {X Y : PresheafedSpace C} (α 
β : X ⟶ Y) (w : α.base = β.base) (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _
 = β.c) : α = β
-/
theorem ext {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.hom.base = β.hom.base)
    (h : α.hom.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.hom.c) : α = β :=
  InducedCategory.hom_ext (PresheafedSpace.ext _ _ w h)

/-- Constructor for isomorphisms in the category `SheafedSpace C`. -/
@[simps]
/-
**AlgebraicGeometry.SheafedSpace.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.SheafedSpace`。
形式化陈述：isoMk {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpac
e) : X ≅ Y where hom
参数：e : X.toPresheafedSpace ≅ Y.toPresheafedSpace。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in the category `SheafedSpace C`.
-/
def isoMk {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpace) : X ≅ Y where
  hom := InducedCategory.homMk e.hom
  inv := InducedCategory.homMk e.inv
  hom_inv_id := InducedCategory.hom_ext e.hom_inv_id
  inv_hom_id := InducedCategory.hom_ext e.inv_hom_id

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
@[simps! obj map]
/-
**AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forgetting the sheaf condition is a functor from `SheafedSpace C` to `Presheafed
Space C`.
-/
def forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

/-- The functor `forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C`
is fully faithful. -/
/-
**AlgebraicGeometry.SheafedSpace.fullyFaithfulForgetToPresheafedSpace** 是 Mathli
b 中的一个定义，位于命名空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：fullyFaithfulForgetToPresheafedSpace : (forgetToPresheafedSpace (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C`
is fully faithful.
-/
def fullyFaithfulForgetToPresheafedSpace :
    (forgetToPresheafedSpace (C := C)).FullyFaithful where
  preimage f := InducedCategory.homMk f

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.fullyFaithfulForgetToPresheafedSpace_preimage_h
om** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：fullyFaithfulForgetToPresheafedSpace_preimage_hom {X Y : SheafedSpace C} (
f : forgetToPresheafedSpace.obj X ⟶ forgetToPresheafedSpace.obj Y) : (fullyFaith
fulForgetToPresheafedSpace.preimage f).hom = f
参数：f : forgetToPresheafedSpace.obj X ⟶ forgetToPresheafedSpace.obj Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fullyFaithfulForgetToPresheafedSpace_preimage_hom {X Y : SheafedSpace C}
    (f : forgetToPresheafedSpace.obj X ⟶ forgetToPresheafedSpace.obj Y) :
    (fullyFaithfulForgetToPresheafedSpace.preimage f).hom = f := rfl
/-
**AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace_full** 是 Mathlib 中的一个实例
，位于命名空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：forgetToPresheafedSpace_full : (forgetToPresheafedSpace (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.full`：full : F.Full where map_surje
ctive
-/
instance forgetToPresheafedSpace_full : (forgetToPresheafedSpace (C := C)).Full :=
  fullyFaithfulForgetToPresheafedSpace.full
/-
**AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace_faithful** 是 Mathlib 中的
一个实例，位于命名空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：forgetToPresheafedSpace_faithful : (forgetToPresheafedSpace (C
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.FullyFaithful.faithful`：faithful : F.Faithful whe
re map_injective
-/
instance forgetToPresheafedSpace_faithful : (forgetToPresheafedSpace (C := C)).Faithful :=
  fullyFaithfulForgetToPresheafedSpace.faithful
/-
**AlgebraicGeometry.SheafedSpace.is_presheafedSpace_iso** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：is_presheafedSpace_iso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] : IsIs
o f.hom
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance is_presheafedSpace_iso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsIso f.hom :=
  SheafedSpace.forgetToPresheafedSpace.map_isIso f

section

attribute [local simp] id comp

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.id_hom** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.SheafedSpace`。
形式化陈述：id_hom (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toPresheafedSpace
参数：X : SheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toPresheafedSpace :=
  rfl

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.id_hom_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.SheafedSpace`。
形式化陈述：id_hom_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom.base = 𝟙 (X : TopCat)
参数：X : SheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom.base = 𝟙 (X : TopCat) :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.id_hom_c** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.SheafedSpace`。
形式化陈述：id_hom_c (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom.c = eqToHom (Presheaf.Pu
shforward.id_eq X.presheaf).symm
参数：X : SheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom_c (X : SheafedSpace C) :
    (𝟙 X : X ⟶ X).hom.c = eqToHom (Presheaf.Pushforward.id_eq X.presheaf).symm :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.id_hom_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.SheafedSpace`。
形式化陈述：id_hom_c_app (X : SheafedSpace C) (U) : (𝟙 X : X ⟶ X).hom.c.app U = 𝟙 _
参数：X : SheafedSpace C；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).hom.c.app U = 𝟙 _ := rfl

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.comp_hom_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.SheafedSpace`。
形式化陈述：comp_hom_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).h
om.base = f.hom.base ≫ g.hom.base
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.base = f.hom.base ≫ g.hom.base :=
  rfl

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.comp_hom_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.SheafedSpace`。
形式化陈述：comp_hom_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α ≫
 β).hom.c.app U = β.hom.c.app U ≫ α.hom.c.app (op ((Opens.map β.hom.base).obj (u
nop U)))
参数：α : X ⟶ Y；β : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).hom.c.app U =
      β.hom.c.app U ≫ α.hom.c.app (op ((Opens.map β.hom.base).obj (unop U))) :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.comp_hom_c_app'** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.SheafedSpace`。
形式化陈述：comp_hom_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α 
≫ β).hom.c.app (op U) = β.hom.c.app (op U) ≫ α.hom.c.app (op ((Opens.map β.hom.b
ase).obj U))
参数：α : X ⟶ Y；β : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).hom.c.app (op U) =
      β.hom.c.app (op U) ≫ α.hom.c.app (op ((Opens.map β.hom.base).obj U)) :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.congr_hom_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.SheafedSpace`。
形式化陈述：congr_hom_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) : α.hom
.c.app U = β.hom.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl))
参数：h : α = β；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.congr_app`：congr_app {X Y : Presheafed
Space C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.app U = β.c.app U ≫ X.presheaf.map 
(eqToHom (by subst h; rfl))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_hom_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.hom.c.app U = β.hom.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) :=
  (PresheafedSpace.congr_app (by rw [h]) U)

variable (C)

/-- The forgetful functor from `SheafedSpace` to `Top`. -/
/-
**AlgebraicGeometry.SheafedSpace.forget** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.SheafedSpace`。
形式化陈述：forget : SheafedSpace C ⥤ TopCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `SheafedSpace` to `Top`.
-/
def forget : SheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map {_ _} f := f.hom.base

end

open TopCat.Presheaf

/-- The restriction of a sheafed space along an open embedding into the space.
-/
/-
**AlgebraicGeometry.SheafedSpace.restrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.SheafedSpace`。
形式化陈述：restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsO
penEmbedding f) : SheafedSpace C
参数：X : SheafedSpace C；X : TopCat；h : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a sheafed space along an open embedding into the space.
-/
def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) :
    SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_isOpenEmbedding h X.IsSheaf }

/-- The map from the restriction of a presheafed space.
-/
@[simps!]
/-
**AlgebraicGeometry.SheafedSpace.ofRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.SheafedSpace`。
形式化陈述：ofRestrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : I
sOpenEmbedding f) : X.restrict h ⟶ X
参数：X : SheafedSpace C；X : TopCat；h : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the restriction of a presheafed space.
-/
def ofRestrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X :=
  InducedCategory.homMk (X.toPresheafedSpace.ofRestrict h)

/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
@[simps! hom inv]
/-
**AlgebraicGeometry.SheafedSpace.restrictTopIso** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.SheafedSpace`。
形式化陈述：restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤)
 ≅ X
参数：X : SheafedSpace C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` 
itself.
-/
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoMk (X.toPresheafedSpace.restrictTopIso)

/-- The global sections, notated Gamma.
-/
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global sections, notated Gamma.
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.hom.c.app (op ⊤) :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.hom.c.app (op ⊤) :=
  rfl
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    CreatesColimitsOfShape J (forgetToPresheafedSpace : SheafedSpace.{_, _, v} C ⥤ _) :=
  ⟨fun {K} =>
    createsColimitOfFullyFaithfulOfIso
      ⟨(PresheafedSpace.colimitCocone (K ⋙ forgetToPresheafedSpace)).pt,
        limit_isSheaf _ fun j ↦ Sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
      (colimit.isoColimitCocone ⟨_, PresheafedSpace.colimitCoconeIsColimit _⟩).symm⟩
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasLimits C] :
    CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) where
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J (SheafedSpace.{_, _, v} C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape forgetToPresheafedSpace
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimits C] : HasColimits.{v} (SheafedSpace C) where
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    PreservesColimitsOfShape J (forget.{_, _, v} C) :=
  Limits.comp_preservesColimitsOfShape forgetToPresheafedSpace (PresheafedSpace.forget C)
/-
**AlgebraicGeometry.SheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
heafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [HasLimits C] : PreservesColimits (forget.{_, _, v} C) where

section ConcreteCategory

variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [instCC : ConcreteCategory.{v} C FC] [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local ext] DFunLike.ext in
include instCC in
/-
**AlgebraicGeometry.SheafedSpace.hom_stalk_ext** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.SheafedSpace`。
形式化陈述：hom_stalk_ext {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom
.base) (h' : forall x, f.hom.stalkMap x = (Y.presheaf.stalkCongr (h ▸ rfl)).hom 
≫ g.hom.stalkMap x) : f = g
参数：f g : X ⟶ Y；h : f.hom.base = g.hom.base；h' : forall x, f.hom.stalkMap x = (Y.
presheaf.stalkCongr (h ▸ rfl)).hom ≫ g.hom.stalkMap x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `TopCat.Presheaf.section_ext`：section_ext (F : Sheaf C X) (U : Opens X) (
s t : ToType (F.1.obj (op U))) (h : forall (x : X) (hx : x in U), F.presheaf.ger
m U x hx s = F.pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColim
its C]   {X Y : AlgebraicGeometry.Presheafe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma hom_stalk_ext {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom.base)
    (h' : ∀ x, f.hom.stalkMap x = (Y.presheaf.stalkCongr (h ▸ rfl)).hom ≫ g.hom.stalkMap x) :
    f = g := by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  refine section_ext X.sheaf _ _ _ fun x hx ↦
    show X.presheaf.germ _ x _ _ = X.presheaf.germ _ x _ _ from ?_
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f, gc⟩]
  simp [h']

attribute [local ext] DFunLike.ext in
include instCC in
/-
**AlgebraicGeometry.SheafedSpace.mono_of_base_injective_of_stalk_epi** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：mono_of_base_injective_of_stalk_epi {X Y : SheafedSpace C} (f : X ⟶ Y) (h₁
 : Function.Injective f.hom.base) (h₂ : forall x, Epi (f.hom.stalkMap x)) : Mono
 f
参数：f : X ⟶ Y；h₁ : Function.Injective f.hom.base；h₂ : forall x, Epi (f.hom.stalkM
ap x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.SheafedSpace.hom_stalk_ext`：hom_stalk_ext {X Y : Sheaf
edSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom.base) (h' : forall x, f.hom.sta
lkMap x = (Y.presheaf.stalkCongr (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.comp`：comp {X Y Z : Presheafe
dSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) : (α ≫ β).stalkMap x = (β.st
alkMap (α.base x) : Z.presheaf.stalk …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma mono_of_base_injective_of_stalk_epi {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Injective f.hom.base)
    (h₂ : ∀ x, Epi (f.hom.stalkMap x)) : Mono f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x ↦ h₁ congr(($e).hom.base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x ↦ ?_
  rw [← cancel_epi (f.hom.stalkMap (g x)), stalkCongr_hom, stalkSpecializes_refl, Category.id_comp,
    ← PresheafedSpace.stalkMap.comp ⟨g, gc⟩ f.hom, ← PresheafedSpace.stalkMap.comp ⟨g, hc⟩ f.hom]
  replace e := congr_arg InducedCategory.Hom.hom e
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
attribute [local ext] DFunLike.ext in
include instCC in
/-
**AlgebraicGeometry.SheafedSpace.epi_of_base_surjective_of_stalk_mono** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.SheafedSpace`。
形式化陈述：epi_of_base_surjective_of_stalk_mono {X Y : SheafedSpace C} (f : X ⟶ Y) (h
₁ : Function.Surjective f.hom.base) (h₂ : forall x, Mono (f.hom.stalkMap x)) : E
pi f
参数：f : X ⟶ Y；h₁ : Function.Surjective f.hom.base；h₂ : forall x, Mono (f.hom.stal
kMap x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.SheafedSpace.hom_stalk_ext`：hom_stalk_ext {X Y : Sheaf
edSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom.base) (h' : forall x, f.hom.sta
lkMap x = (Y.presheaf.stalkCongr (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `specializes_refl`：specializes_refl (x : X) : x ⤳ x
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap.comp`：comp {X Y Z : Presheafe
dSpace.{_, _, v} C} (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) : (α ≫ β).stalkMap x = (β.st
alkMap (α.base x) : Z.presheaf.stalk …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma epi_of_base_surjective_of_stalk_mono {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.hom.base)
    (h₂ : ∀ x, Mono (f.hom.stalkMap x)) : Epi f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  apply_fun InducedCategory.Hom.hom at e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y ↦ by
    rw [← (h₁ y).choose_spec]
    simpa using congr(($e).base.hom (h₁ y).choose)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun y ↦ ?_
  rw [← (h₁ y).choose_spec, ← cancel_mono (f.hom.stalkMap (h₁ y).choose), stalkCongr_hom,
    stalkSpecializes_refl, Category.id_comp, ← PresheafedSpace.stalkMap.comp f.hom ⟨g, gc⟩,
    ← PresheafedSpace.stalkMap.comp f.hom ⟨g, hc⟩]
  congr 1

end ConcreteCategory

end SheafedSpace

end AlgebraicGeometry

