/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.Algebra.Module.LinearMap.Rat

/-!
# Linear Functors

An additive functor between two `R`-linear categories is called *linear*
if the induced map on hom types is a morphism of `R`-modules.

## Implementation details

`Functor.Linear` is a `Prop`-valued class, defined by saying that
for every two objects `X` and `Y`, the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)` is a morphism of `R`-modules.

-/

@[expose] public section


namespace CategoryTheory

variable (R : Type*) [Semiring R] {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
  (F : C ⥤ D)

/--
Definition of `Functor.Linear` / `Functor.Linear` 的定义

English:
class Functor.Linear
  parameters: : Prop where
  axioms and operations (1):
    - map_smul : forall {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f  [default: by cat_disch]

中文:
类 函子.线性
  参数: : 命题 where
  公理与运算 (1 个):
    - map_smul : 对任意 {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
class Functor.Linear : Prop where
  /-- the functor induces a linear map on morphisms -/
  map_smul : forall {X Y : C} (f : X ⟶ Y) (r : R), F.map (r • f) = r • F.map f := by cat_disch

/--
lemma `Functor.linear_iff` / 引理 `Functor.linear_iff`

English:
lemma Functor.linear_iff
  given: (F : C ⥤ D)
  proof: by
  constructor
  · intro h X r
    rw [h.map_smul]; rw [F.map_id]
  · refine fun h => ⟨fun {X Y} f r => ?_⟩
    have : r • f = (r • 𝟙 X) ≫ f := by simp
    rw [this]; rw [F.map_comp]; rw [h]; rw [Linear.smul_comp]; rw [Category.id_comp]

中文:
引理 函子.linear_iff
  条件: (F : C ⥤ D)
  证明: by
  constructor
  · intro h X r
    rw [h.map_smul]; rw [F.map_id]
  · refine fun h => ⟨fun {X Y} f r => ?_⟩
    have : r • f = (r • 𝟙 X) ≫ f := by simp
    rw [this]; rw [F.map_comp]; rw [h]; rw [Linear.smul_comp]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, F.map_comp, F.map_id, Linear, Linear.smul_comp, h.map_smul, id_comp, map_comp, map_id, map_smul, smul_comp
-/
lemma Functor.linear_iff (F : C ⥤ D) :
    Functor.Linear R F ↔ forall (X : C) (r : R), F.map (r • 𝟙 X) = r • 𝟙 (F.obj X) := by
  constructor
  · intro h X r
    rw [h.map_smul]; rw [F.map_id]
  · refine fun h => ⟨fun {X Y} f r => ?_⟩
    have : r • f = (r • 𝟙 X) ≫ f := by simp
    rw [this]; rw [F.map_comp]; rw [h]; rw [Linear.smul_comp]; rw [Category.id_comp]

section Linear

namespace Functor

section

variable {R} [Linear R F]

@[simp]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: {X Y : C} (r : R) (f : X ⟶ Y)
  statement: F.map (r • f) = r • F.map f
  proof: Functor.Linear.map_smul _ _

@[simp]

中文:
定理 map_smul
  条件: {X Y : C} (r : R) (f : X ⟶ Y)
  结论: F.map (r • f) = r • F.map f
  证明: Functor.Linear.map_smul _ _

@[simp]

Depends on / 依赖: Functor, Functor.Linear.map_smul, Linear, map_smul
-/
theorem map_smul {X Y : C} (r : R) (f : X ⟶ Y) : F.map (r • f) = r • F.map f :=
  Functor.Linear.map_smul _ _

@[simp]
/--
theorem `map_units_smul` / 定理 `map_units_smul`

English:
theorem map_units_smul
  given: {X Y : C} (r : Rˣ) (f : X ⟶ Y)
  statement: F.map (r • f) = r • F.map f
  proof: by
  apply map_smul

中文:
定理 map_units_smul
  条件: {X Y : C} (r : Rˣ) (f : X ⟶ Y)
  结论: F.map (r • f) = r • F.map f
  证明: by
  apply map_smul

Depends on / 依赖: map_smul
-/
theorem map_units_smul {X Y : C} (r : Rˣ) (f : X ⟶ Y) : F.map (r • f) = r • F.map f := by
  apply map_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Linear R (𝟭 C)

中文:
实例 :
  签名: 线性 R (𝟭 C)
-/
instance : Linear R (𝟭 C) where

section

variable {E : Type*} [Category* E] [Preadditive E] [CategoryTheory.Linear R E] (G : D ⥤ E)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Linear
  signature: R G] : Linear R (F ⋙ G) where

中文:
实例 [线性
  签名: R G] : 线性 R (F ⋙ G) where
-/
instance [Linear R G] : Linear R (F ⋙ G) where

set_option backward.isDefEq.respectTransparency false in
/--
lemma `linear_of_full_essSurj_comp` / 引理 `linear_of_full_essSurj_comp`

English:
lemma linear_of_full_essSurj_comp
  given: [F.Full] [F.EssSurj] [Functor.Linear R (F ⋙ G)]
  proof: by
  refine ⟨fun {X Y} f r => ?_⟩
  obtain ⟨X', Y', eX, eY, f', rfl⟩ :
      exists (X' Y' : C) (eX : F.obj X' ≅ X) (eY : F.obj Y' ≅ Y)
        (f' : X' ⟶ Y'), f = eX.inv ≫ F.map f' ≫ eY.hom := by
    obtain ⟨f', hf'⟩ :=
      F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso 

中文:
引理 linear_of_full_essSurj_comp
  条件: [F.满] [F.本质满射] [函子.线性 R (F ⋙ G)]
  证明: by
  refine ⟨fun {X Y} f r => ?_⟩
  obtain ⟨X', Y', eX, eY, f', rfl⟩ :
      exists (X' Y' : C) (eX : F.obj X' ≅ X) (eY : F.obj Y' ≅ Y)
        (f' : X' ⟶ Y'), f = eX.inv ≫ F.map f' ≫ eY.hom := by
    obtain ⟨f', hf'⟩ :=
      F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso 

Depends on / 依赖: F.map, F.map_surjective, F.obj, F.objObjPreimageIso, G.map, G.map_comp, Linear, Linear.comp_smul, Linear.smul_comp, cat_disch, comp_map, comp_smul, eX.inv, eY.hom, map_comp, map_smul, map_surjective, objObjPreimageIso, smul_comp
-/
lemma linear_of_full_essSurj_comp [F.Full] [F.EssSurj] [Functor.Linear R (F ⋙ G)] :
    Functor.Linear R G := by
  refine ⟨fun {X Y} f r => ?_⟩
  obtain ⟨X', Y', eX, eY, f', rfl⟩ :
      exists (X' Y' : C) (eX : F.obj X' ≅ X) (eY : F.obj Y' ≅ Y)
        (f' : X' ⟶ Y'), f = eX.inv ≫ F.map f' ≫ eY.hom := by
    obtain ⟨f', hf'⟩ :=
      F.map_surjective ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
    exact ⟨_, _, F.objObjPreimageIso X, F.objObjPreimageIso Y, f', by cat_disch⟩
  simpa only [comp_map, map_smul, Linear.smul_comp, Linear.comp_smul, ← G.map_comp]
    using G.map eX.inv ≫= ((F ⋙ G).map_smul r f') =≫ G.map eY.hom

/--
lemma `linear_comp_iff_of_full_of_essSurj` / 引理 `linear_comp_iff_of_full_of_essSurj`

English:
lemma linear_comp_iff_of_full_of_essSurj
  given: [F.Full] [F.EssSurj]
  proof: ⟨fun _ => linear_of_full_essSurj_comp F G, fun _ => inferInstance⟩

中文:
引理 linear_comp_iff_of_full_of_essSurj
  条件: [F.满] [F.本质满射]
  证明: ⟨fun _ => linear_of_full_essSurj_comp F G, fun _ => inferInstance⟩

Depends on / 依赖: linear_of_full_essSurj_comp
-/
lemma linear_comp_iff_of_full_of_essSurj [F.Full] [F.EssSurj] :
    Functor.Linear R (F ⋙ G) ↔ Functor.Linear R G :=
  ⟨fun _ => linear_of_full_essSurj_comp F G, fun _ => inferInstance⟩

end

variable (R) [F.Additive]

/-- `F.mapLinearMap` is an `R`-linear map whose underlying function is `F.map`. -/
@[simps]
/--
Definition of `mapLinearMap` / `mapLinearMap` 的定义

English:
definition mapLinearMap
  signature: {X Y : C}
  body: { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }

中文:
定义 mapLinearMap
  签名: {X Y : C}
  定义体: { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }

Depends on / 依赖: F.mapAddHom, F.map_smul, mapAddHom, map_smul
-/
def mapLinearMap {X Y : C} : (X ⟶ Y) ->ₗ[R] F.obj X ⟶ F.obj Y :=
  { F.mapAddHom with map_smul' := fun r f => F.map_smul r f }

/--
theorem `coe_mapLinearMap` / 定理 `coe_mapLinearMap`

English:
theorem coe_mapLinearMap
  given: {X Y : C}
  statement: ⇑(F.mapLinearMap R : (X ⟶ Y) ->ₗ[R] _) = F.map
  proof: rfl

中文:
定理 coe_mapLinearMap
  条件: {X Y : C}
  结论: ⇑(F.mapLinearMap R : (X ⟶ Y) ->ₗ[R] _) = F.map
  证明: rfl
-/
theorem coe_mapLinearMap {X Y : C} : ⇑(F.mapLinearMap R : (X ⟶ Y) ->ₗ[R] _) = F.map := rfl

end

variable {F} in
/--
lemma `linear_of_iso` / 引理 `linear_of_iso`

English:
lemma linear_of_iso
  given: {G : C ⥤ D} (e : F ≅ G) [F.Linear R]
  statement: G.Linear R
  proof: by
  exact
    { map_smul := fun f r => by
        simp only [← NatIso.naturality_1 e (r • f), F.map_smul, Linear.smul_comp,
          NatTrans.naturality, Linear.comp_smul, Iso.inv_hom_id_app_assoc] }

中文:
引理 linear_of_iso
  条件: {G : C ⥤ D} (e : F ≅ G) [F.线性 R]
  结论: G.线性 R
  证明: by
  exact
    { map_smul := fun f r => by
        simp only [← NatIso.naturality_1 e (r • f), F.map_smul, Linear.smul_comp,
          NatTrans.naturality, Linear.comp_smul, Iso.inv_hom_id_app_assoc] }

Depends on / 依赖: F.map_smul, Iso.inv_hom_id_app_assoc, Linear, Linear.comp_smul, Linear.smul_comp, NatIso, NatIso.naturality_1, NatTrans, NatTrans.naturality, comp_smul, inv_hom_id_app_assoc, map_smul, naturality, naturality_1, smul_comp
-/
lemma linear_of_iso {G : C ⥤ D} (e : F ≅ G) [F.Linear R] : G.Linear R := by
  exact
    { map_smul := fun f r => by
        simp only [← NatIso.naturality_1 e (r • f), F.map_smul, Linear.smul_comp,
          NatTrans.naturality, Linear.comp_smul, Iso.inv_hom_id_app_assoc] }

section InducedCategory

/--
Instance `inducedFunctorLinear` / 实例 `inducedFunctorLinear`

English:
instance inducedFunctorLinear
  signature: (F : C -> D)

中文:
实例 inducedFunctorLinear
  签名: (F : C -> D)
-/
instance inducedFunctorLinear (F : C -> D) : Functor.Linear R (inducedFunctor F) where

end InducedCategory

/--
Instance `fullSubcategoryInclusionLinear` / 实例 `fullSubcategoryInclusionLinear`

English:
instance fullSubcategoryInclusionLinear
  signature: {C : Type*} [Category* C] [Preadditive C]

中文:
实例 fullSubcategoryInclusionLinear
  签名: {C : 类型} [范畴* C] [预加性 C]
-/
instance fullSubcategoryInclusionLinear {C : Type*} [Category* C] [Preadditive C]
    [CategoryTheory.Linear R C] (Z : ObjectProperty C) : Z.ι.Linear R where

section

variable {R} [Additive F]

/--
Instance `natLinear` / 实例 `natLinear`

English:
instance natLinear
  signature: : F.Linear Nat where
  body: F.mapAddHom.map_nsmul r f

中文:
实例 natLinear
  签名: : F.线性 自然数 where
  定义体: F.mapAddHom.map_nsmul r f

Depends on / 依赖: F.mapAddHom.map_nsmul, mapAddHom, map_nsmul
-/
instance natLinear : F.Linear Nat where
  map_smul f r := F.mapAddHom.map_nsmul r f

/--
Instance `intLinear` / 实例 `intLinear`

English:
instance intLinear
  signature: : F.Linear Int where
  body: F.mapAddHom.map_zsmul r f

中文:
实例 intLinear
  签名: : F.线性 整数 where
  定义体: F.mapAddHom.map_zsmul r f

Depends on / 依赖: F.mapAddHom.map_zsmul, mapAddHom, map_zsmul
-/
instance intLinear : F.Linear Int where
  map_smul f r := F.mapAddHom.map_zsmul r f

variable [CategoryTheory.Linear Rat C] [CategoryTheory.Linear Rat D]

/--
Instance `ratLinear` / 实例 `ratLinear`

English:
instance ratLinear
  signature: : F.Linear Rat where
  body: F.mapAddHom.toRatLinearMap.map_smul r f

中文:
实例 ratLinear
  签名: : F.线性 有理数 where
  定义体: F.mapAddHom.toRatLinearMap.map_smul r f

Depends on / 依赖: F.mapAddHom.toRatLinearMap.map_smul, mapAddHom, map_smul, toRatLinearMap
-/
instance ratLinear : F.Linear Rat where
  map_smul f r := F.mapAddHom.toRatLinearMap.map_smul r f

end

end Functor

namespace Equivalence

set_option backward.defeqAttrib.useBackward true in
/--
Instance `inverseLinear` / 实例 `inverseLinear`

English:
instance inverseLinear
  signature: (e : C ≌ D) [e.functor.Linear R]
  body: by
    apply e.functor.map_injective
    simp

中文:
实例 inverseLinear
  签名: (e : C ≌ D) [e.functor.线性 R]
  定义体: by
    apply e.functor.map_injective
    simp

Depends on / 依赖: e.functor.map_injective, functor, map_injective
-/
instance inverseLinear (e : C ≌ D) [e.functor.Linear R] : e.inverse.Linear R where
  map_smul r f := by
    apply e.functor.map_injective
    simp

end Equivalence

end Linear

end CategoryTheory
