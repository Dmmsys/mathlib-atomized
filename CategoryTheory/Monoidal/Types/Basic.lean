/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The category of types is a (symmetric) monoidal category
-/

@[expose] public section


open CategoryTheory Limits MonoidalCategory

universe v u

namespace CategoryTheory

/--
Instance `typesCartesianMonoidalCategory` / 实例 `typesCartesianMonoidalCategory`

English:
instance typesCartesianMonoidalCategory
  signature: : CartesianMonoidalCategory (Type u) where
  body: X × Y
  tensorUnit := PUnit
  __ := CartesianMonoidalCategory.ofChosenFiniteProducts
    Types.terminalLimitCone Types.binaryProductLimitCone

中文:
实例 typesCartesianMonoidalCategory
  签名: : CartesianMonoidal范畴 (类型u) where
  定义体: X × Y
  tensorUnit := PUnit
  __ := CartesianMonoidalCategory.ofChosenFiniteProducts
    Types.terminalLimitCone Types.binaryProductLimitCone
-/
instance typesCartesianMonoidalCategory : CartesianMonoidalCategory (Type u) where
  tensorObj X Y := X × Y
  tensorUnit := PUnit
  __ := CartesianMonoidalCategory.ofChosenFiniteProducts
    Types.terminalLimitCone Types.binaryProductLimitCone

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BraidedCategory (Type u)
  body: .ofCartesianMonoidalCategory

中文:
实例 :
  签名: 辫范畴 (类型u)
  定义体: .ofCartesianMonoidalCategory

Depends on / 依赖: ofCartesianMonoidalCategory
-/
instance : BraidedCategory (Type u) := .ofCartesianMonoidalCategory

/--
theorem `types_tensorObj_def` / 定理 `types_tensorObj_def`

English:
theorem types_tensorObj_def
  given: {X Y : Type u}
  statement: X otimes Y = (X × Y)
  proof: rfl

中文:
定理 types_tensorObj_def
  条件: {X Y : 类型u}
  结论: X otimes Y = (X × Y)
  证明: rfl

Depends on / 依赖: Subobject, Subobject.boundedOrder, Subobject.completeSemilatticeInf, Subobject.completeSemilatticeSup, Subobject.semilatticeInf, Subobject.semilatticeSup, boundedOrder, completeSemilatticeInf, completeSemilatticeSup, semilatticeInf, semilatticeSup
-/
theorem types_tensorObj_def {X Y : Type u} : X otimes Y = (X × Y) := rfl

/--
theorem `types_tensorUnit_def` / 定理 `types_tensorUnit_def`

English:
theorem types_tensorUnit_def
  statement: 𝟙_ (Type u) = PUnit
  proof: rfl

中文:
定理 types_tensorUnit_def
  结论: 𝟙_ (类型u) = 命题单元
  证明: rfl
-/
theorem types_tensorUnit_def : 𝟙_ (Type u) = PUnit := rfl

attribute [local simp] types_tensorObj_def types_tensorUnit_def

@[simp]
/--
theorem `tensor_apply` / 定理 `tensor_apply`

English:
theorem tensor_apply
  given: {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W otimes Y)
  proof: rfl

@[simp]

中文:
定理 tensor_apply
  条件: {W X Y Z : 类型u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W otimes Y)
  证明: rfl

@[simp]
-/
theorem tensor_apply {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W otimes Y) :
    dsimp% (f otimesₘ g) p = (f p.1, g p.2) :=
  rfl

@[simp]
/--
theorem `whiskerLeft_apply` / 定理 `whiskerLeft_apply`

English:
theorem whiskerLeft_apply
  given: (X : Type u) {Y Z : Type u} (f : Y ⟶ Z) (p : X otimes Y)
  proof: rfl

@[simp]

中文:
定理 whiskerLeft_apply
  条件: (X : 类型u) {Y Z : 类型u} (f : Y ⟶ Z) (p : X otimes Y)
  证明: rfl

@[simp]
-/
theorem whiskerLeft_apply (X : Type u) {Y Z : Type u} (f : Y ⟶ Z) (p : X otimes Y) :
    dsimp% (X ◁ f) p = (p.1, f p.2) :=
  rfl

@[simp]
/--
theorem `whiskerRight_apply` / 定理 `whiskerRight_apply`

English:
theorem whiskerRight_apply
  given: {Y Z : Type u} (f : Y ⟶ Z) (X : Type u) (p : Y otimes X)
  proof: rfl

@[simp]

中文:
定理 whiskerRight_apply
  条件: {Y Z : 类型u} (f : Y ⟶ Z) (X : 类型u) (p : Y otimes X)
  证明: rfl

@[simp]
-/
theorem whiskerRight_apply {Y Z : Type u} (f : Y ⟶ Z) (X : Type u) (p : Y otimes X) :
    dsimp% (f ▷ X) p = (f p.1, p.2) :=
  rfl

@[simp]
/--
theorem `leftUnitor_hom_apply` / 定理 `leftUnitor_hom_apply`

English:
theorem leftUnitor_hom_apply
  given: {X : Type u} {x : X} {p : PUnit}
  proof: rfl

@[simp]

中文:
定理 leftUnitor_hom_apply
  条件: {X : 类型u} {x : X} {p : 命题单元}
  证明: rfl

@[simp]
-/
theorem leftUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} :
    dsimp% (fun_ X).hom (p, x) = x :=
  rfl

@[simp]
/--
theorem `leftUnitor_inv_apply` / 定理 `leftUnitor_inv_apply`

English:
theorem leftUnitor_inv_apply
  given: {X : Type u} {x : X}
  proof: rfl

@[simp]

中文:
定理 leftUnitor_inv_apply
  条件: {X : 类型u} {x : X}
  证明: rfl

@[simp]
-/
theorem leftUnitor_inv_apply {X : Type u} {x : X} :
    dsimp% (fun_ X).inv x = (PUnit.unit, x) :=
  rfl

@[simp]
/--
theorem `rightUnitor_hom_apply` / 定理 `rightUnitor_hom_apply`

English:
theorem rightUnitor_hom_apply
  given: {X : Type u} {x : X} {p : PUnit}
  proof: rfl

@[simp]

中文:
定理 rightUnitor_hom_apply
  条件: {X : 类型u} {x : X} {p : 命题单元}
  证明: rfl

@[simp]
-/
theorem rightUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} :
    dsimp% (ρ_ X).hom (x, p) = x :=
  rfl

@[simp]
/--
theorem `rightUnitor_inv_apply` / 定理 `rightUnitor_inv_apply`

English:
theorem rightUnitor_inv_apply
  given: {X : Type u} {x : X}
  proof: rfl

@[simp]

中文:
定理 rightUnitor_inv_apply
  条件: {X : 类型u} {x : X}
  证明: rfl

@[simp]
-/
theorem rightUnitor_inv_apply {X : Type u} {x : X} :
    dsimp% (ρ_ X).inv x = (x, PUnit.unit) :=
  rfl

@[simp]
/--
theorem `associator_hom_apply` / 定理 `associator_hom_apply`

English:
theorem associator_hom_apply
  given: {X Y Z : Type u} {x : X} {y : Y} {z : Z}
  proof: rfl

@[simp]

中文:
定理 associator_hom_apply
  条件: {X Y Z : 类型u} {x : X} {y : Y} {z : Z}
  证明: rfl

@[simp]
-/
theorem associator_hom_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
    dsimp% (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) :=
  rfl

@[simp]
/--
theorem `associator_inv_apply` / 定理 `associator_inv_apply`

English:
theorem associator_inv_apply
  given: {X Y Z : Type u} {x : X} {y : Y} {z : Z}
  proof: rfl

中文:
定理 associator_inv_apply
  条件: {X Y Z : 类型u} {x : X} {y : Y} {z : Z}
  证明: rfl
-/
theorem associator_inv_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
    dsimp% (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) :=
  rfl

/--
theorem `associator_hom_apply_1` / 定理 `associator_hom_apply_1`

English:
theorem associator_hom_apply_1
  given: {X Y Z : Type u} {x}
  proof: rfl

中文:
定理 associator_hom_apply_1
  条件: {X Y Z : 类型u} {x}
  证明: rfl
-/
@[simp] theorem associator_hom_apply_1 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).hom x).1 = x.1.1 :=
  rfl

/--
theorem `associator_hom_apply_2_1` / 定理 `associator_hom_apply_2_1`

English:
theorem associator_hom_apply_2_1
  given: {X Y Z : Type u} {x}
  proof: rfl

中文:
定理 associator_hom_apply_2_1
  条件: {X Y Z : 类型u} {x}
  证明: rfl
-/
@[simp] theorem associator_hom_apply_2_1 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).hom x).2.1 = x.1.2 :=
  rfl

/--
theorem `associator_hom_apply_2_2` / 定理 `associator_hom_apply_2_2`

English:
theorem associator_hom_apply_2_2
  given: {X Y Z : Type u} {x}
  proof: rfl

中文:
定理 associator_hom_apply_2_2
  条件: {X Y Z : 类型u} {x}
  证明: rfl
-/
@[simp] theorem associator_hom_apply_2_2 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).hom x).2.2 = x.2 :=
  rfl

/--
theorem `associator_inv_apply_1_1` / 定理 `associator_inv_apply_1_1`

English:
theorem associator_inv_apply_1_1
  given: {X Y Z : Type u} {x}
  proof: rfl

中文:
定理 associator_inv_apply_1_1
  条件: {X Y Z : 类型u} {x}
  证明: rfl
-/
@[simp] theorem associator_inv_apply_1_1 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).inv x).1.1 = x.1 :=
  rfl

/--
theorem `associator_inv_apply_1_2` / 定理 `associator_inv_apply_1_2`

English:
theorem associator_inv_apply_1_2
  given: {X Y Z : Type u} {x}
  proof: rfl

中文:
定理 associator_inv_apply_1_2
  条件: {X Y Z : 类型u} {x}
  证明: rfl
-/
@[simp] theorem associator_inv_apply_1_2 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).inv x).1.2 = x.2.1 :=
  rfl

/--
theorem `associator_inv_apply_2` / 定理 `associator_inv_apply_2`

English:
theorem associator_inv_apply_2
  given: {X Y Z : Type u} {x}
  proof: rfl

@[simp]

中文:
定理 associator_inv_apply_2
  条件: {X Y Z : 类型u} {x}
  证明: rfl

@[simp]
-/
@[simp] theorem associator_inv_apply_2 {X Y Z : Type u} {x} :
    dsimp% ((α_ X Y Z).inv x).2 = x.2.2 :=
  rfl

@[simp]
/--
theorem `braiding_hom_apply` / 定理 `braiding_hom_apply`

English:
theorem braiding_hom_apply
  given: {X Y : Type u} {x : X} {y : Y}
  proof: rfl

@[simp]

中文:
定理 braiding_hom_apply
  条件: {X Y : 类型u} {x : X} {y : Y}
  证明: rfl

@[simp]
-/
theorem braiding_hom_apply {X Y : Type u} {x : X} {y : Y} :
    dsimp% (β_ X Y).hom (x, y) = (y, x) :=
  rfl

@[simp]
/--
theorem `braiding_inv_apply` / 定理 `braiding_inv_apply`

English:
theorem braiding_inv_apply
  given: {X Y : Type u} {x : X} {y : Y}
  proof: rfl

@[simp]

中文:
定理 braiding_inv_apply
  条件: {X Y : 类型u} {x : X} {y : Y}
  证明: rfl

@[simp]
-/
theorem braiding_inv_apply {X Y : Type u} {x : X} {y : Y} :
    dsimp% (β_ X Y).inv (y, x) = (x, y) :=
  rfl

@[simp]
/--
theorem `CartesianMonoidalCategory.lift_apply` / 定理 `CartesianMonoidalCategory.lift_apply`

English:
theorem CartesianMonoidalCategory.lift_apply
  given: {X Y Z : Type u} {f : X ⟶ Y} {g : X ⟶ Z} {x : X}
  proof: rfl

中文:
定理 CartesianMonoidal范畴.lift_apply
  条件: {X Y Z : 类型u} {f : X ⟶ Y} {g : X ⟶ Z} {x : X}
  证明: rfl
-/
theorem CartesianMonoidalCategory.lift_apply {X Y Z : Type u} {f : X ⟶ Y} {g : X ⟶ Z} {x : X} :
    dsimp% lift f g x = (f x, g x) :=
  rfl

-- We don't yet have an API for tensor products indexed by finite ordered types,
-- but it would be nice to state how monoidal functors preserve these.
/--
Definition of `MonoidalFunctor.mapPi` / `MonoidalFunctor.mapPi` 的定义

English:
definition MonoidalFunctor.mapPi
  signature: {C : Type*} [Category* C] [MonoidalCategory C]
  body: Functor.mapIso _ (Fin.consEquiv _).symm.toIso ≪≫ (Functor.Monoidal.μIso F β (Fin n -> β)).symm

中文:
定义 MonoidalFunctor.mapPi
  签名: {C : 类型} [范畴* C] [幺半群范畴 C]
  定义体: Functor.mapIso _ (Fin.consEquiv _).symm.toIso ≪≫ (Functor.Monoidal.μIso F β (Fin n -> β)).symm

Depends on / 依赖: Fin.consEquiv, Functor, Functor.Monoidal, Functor.mapIso, Monoidal, consEquiv, mapIso, symm.toIso
-/
noncomputable def MonoidalFunctor.mapPi {C : Type*} [Category* C] [MonoidalCategory C]
    (F : Type _ ⥤ C) [F.Monoidal] (n : Nat) (β : Type*) :
    F.obj (Fin (n + 1) -> β) ≅ F.obj β otimes F.obj (Fin n -> β) :=
  Functor.mapIso _ (Fin.consEquiv _).symm.toIso ≪≫ (Functor.Monoidal.μIso F β (Fin n -> β)).symm

end CategoryTheory
