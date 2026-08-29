/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Center.Preadditive

/-!
# Center of a linear category

If `C` is an `R`-linear category, we define a ring morphism `R →+* CatCenter C`
and conversely, if `C` is a preadditive category, and `φ : R →+* CatCenter C`
is a ring morphism, we define an `R`-linear structure on `C` attached to `φ`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Category Limits

namespace Linear

variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C]

open scoped IsMulCommutative in
/-- The canonical morphism `R →+* CatCenter C` when `C` is an `R`-linear category. -/
@[simps]
/--
Definition of `toCatCenter` / `toCatCenter` 的定义

English:
definition toCatCenter
  signature: [Linear R C]
  body: { app := fun X => a • 𝟙 X }
  map_one' := by cat_disch
  map_mul' a b := by
    rw [mul_comm]
    ext X
    dsimp only [CatCenter.mul_app']
    rw [Linear.smul_comp]; rw [Linear.comp_smul]; rw [smul_smul]
    simp
  map_zero' := by cat_disch
  map_add' a b := by ext X; simp [add_smul]

中文:
定义 toCatCenter
  签名: [线性 R C]
  定义体: { app := fun X => a • 𝟙 X }
  map_one' := by cat_disch
  map_mul' a b := by
    rw [mul_comm]
    ext X
    dsimp only [CatCenter.mul_app']
    rw [Linear.smul_comp]; rw [Linear.comp_smul]; rw [smul_smul]
    simp
  map_zero' := by cat_disch
  map_add' a b := by ext X; simp [add_smul]

Depends on / 依赖: CatCenter, CatCenter.mul_app, Linear, Linear.comp_smul, Linear.smul_comp, add_smul, cat_disch, comp_smul, map_add, map_mul, map_one, map_zero, mul_app, mul_comm, smul_comp, smul_smul
-/
def toCatCenter [Linear R C] : R ->+* CatCenter C where
  toFun a :=
    { app := fun X => a • 𝟙 X }
  map_one' := by cat_disch
  map_mul' a b := by
    rw [mul_comm]
    ext X
    dsimp only [CatCenter.mul_app']
    rw [Linear.smul_comp]; rw [Linear.comp_smul]; rw [smul_smul]
    simp
  map_zero' := by cat_disch
  map_add' a b := by ext X; simp [add_smul]

section

variable {R C}
variable (φ : R ->+* CatCenter C) (X Y : C)

/-- The scalar multiplication by `R` on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
/--
Definition of `smulOfRingMorphism` / `smulOfRingMorphism` 的定义

English:
definition smulOfRingMorphism
  signature: : SMul R (X ⟶ Y) where
  body: (φ a).app X ≫ f

中文:
定义 smulOfRingMorphism
  签名: : 标量乘法 R (X ⟶ Y) where
  定义体: (φ a).app X ≫ f
-/
def smulOfRingMorphism : SMul R (X ⟶ Y) where
  smul a f := (φ a).app X ≫ f

variable {X Y}

/--
lemma `smulOfRingMorphism_smul_eq` / 引理 `smulOfRingMorphism_smul_eq`

English:
lemma smulOfRingMorphism_smul_eq
  given: (a : R) (f : X ⟶ Y)
  proof: smulOfRingMorphism φ X Y
    a • f = (φ a).app X ≫ f := rfl

中文:
引理 smulOfRingMorphism_smul_eq
  条件: (a : R) (f : X ⟶ Y)
  证明: smulOfRingMorphism φ X Y
    a • f = (φ a).app X ≫ f := rfl

Depends on / 依赖: smulOfRingMorphism
-/
lemma smulOfRingMorphism_smul_eq (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = (φ a).app X ≫ f := rfl

/--
lemma `smulOfRingMorphism_smul_eq'` / 引理 `smulOfRingMorphism_smul_eq'`

English:
lemma smulOfRingMorphism_smul_eq'
  given: (a : R) (f : X ⟶ Y)
  proof: smulOfRingMorphism φ X Y
    a • f = f ≫ (φ a).app Y := by
  rw [smulOfRingMorphism_smul_eq]
  exact ((φ a).naturality f).symm

中文:
引理 smulOfRingMorphism_smul_eq'
  条件: (a : R) (f : X ⟶ Y)
  证明: smulOfRingMorphism φ X Y
    a • f = f ≫ (φ a).app Y := by
  rw [smulOfRingMorphism_smul_eq]
  exact ((φ a).naturality f).symm

Depends on / 依赖: smulOfRingMorphism
-/
lemma smulOfRingMorphism_smul_eq' (a : R) (f : X ⟶ Y) :
    letI := smulOfRingMorphism φ X Y
    a • f = f ≫ (φ a).app Y := by
  rw [smulOfRingMorphism_smul_eq]
  exact ((φ a).naturality f).symm

variable (X Y)

set_option backward.isDefEq.respectTransparency false in
/-- The `R`-module structure on the type `X ⟶ Y` of morphisms in
a category `C` equipped with a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
/--
Definition of `homModuleOfRingMorphism` / `homModuleOfRingMorphism` 的定义

English:
definition homModuleOfRingMorphism
  signature: : Module R (X ⟶ Y)
  body: by
  letI := smulOfRingMorphism φ X Y
  exact
  { one_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq,
        Functor.id_obj, map_one, End.one_def, NatTrans.id_app, id_comp]
    mul_smul := fun a b f => by
      simp only [smulOfRingMorphism_smul_eq', Functor.id_obj, map_mul, End.mul_def,
        NatTrans.comp_app, assoc]
    smul_zero := fun a => by
      simp only [smulOfRingMorphism_smul_eq, comp_zero]
    zero_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq, map_zero,
        zero_app, zero_comp]
    smul_add := fun a b => by
      simp [smulOfRingMorphism_smul_eq]
    add_smul := fun a b f => by
      simp [smulOfRingMorphism_smul_eq] }

中文:
定义 homModuleOfRingMorphism
  签名: : 模 R (X ⟶ Y)
  定义体: by
  letI := smulOfRingMorphism φ X Y
  exact
  { one_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq,
        Functor.id_obj, map_one, End.one_def, NatTrans.id_app, id_comp]
    mul_smul := fun a b f => by
      simp only [smulOfRingMorphism_smul_eq', Functor.id_obj, map_mul, End.mul_def,
        NatTrans.comp_app, assoc]
    smul_zero := fun a => by
      simp only [smulOfRingMorphism_smul_eq, comp_zero]
    zero_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq, map_zero,
        zero_app, zero_comp]
    smul_add := fun a b => by
      simp [smulOfRingMorphism_smul_eq]
    add_smul := fun a b f => by
      simp [smulOfRingMorphism_smul_eq] }

Depends on / 依赖: End.mul_def, End.one_def, Functor, Functor.id_obj, NatTrans, NatTrans.comp_app, NatTrans.id_app, comp_app, comp_zero, id_app, id_comp, id_obj, map_mul, map_one, map_zero, mul_def, mul_smul, one_def, one_smul, smulOfRingMorphism
-/
def homModuleOfRingMorphism : Module R (X ⟶ Y) := by
  letI := smulOfRingMorphism φ X Y
  exact
  { one_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq,
        Functor.id_obj, map_one, End.one_def, NatTrans.id_app, id_comp]
    mul_smul := fun a b f => by
      simp only [smulOfRingMorphism_smul_eq', Functor.id_obj, map_mul, End.mul_def,
        NatTrans.comp_app, assoc]
    smul_zero := fun a => by
      simp only [smulOfRingMorphism_smul_eq, comp_zero]
    zero_smul := fun a => by
      simp only [smulOfRingMorphism_smul_eq, map_zero,
        zero_app, zero_comp]
    smul_add := fun a b => by
      simp [smulOfRingMorphism_smul_eq]
    add_smul := fun a b f => by
      simp [smulOfRingMorphism_smul_eq] }

/-- The `R`-linear structure on a preadditive category `C` equipped with
a ring morphism `R →+* CatCenter C`. -/
@[instance_reducible]
/--
Definition of `ofRingMorphism` / `ofRingMorphism` 的定义

English:
definition ofRingMorphism
  signature: : Linear R C
  body: by
  letI := homModuleOfRingMorphism φ
  exact
    { smul_comp := fun X Y Z r f g => by simp only [smulOfRingMorphism_smul_eq, assoc]
      comp_smul := fun X Y Z f r g => by simp only [smulOfRingMorphism_smul_eq', assoc] }

中文:
定义 ofRingMorphism
  签名: : 线性 R C
  定义体: by
  letI := homModuleOfRingMorphism φ
  exact
    { smul_comp := fun X Y Z r f g => by simp only [smulOfRingMorphism_smul_eq, assoc]
      comp_smul := fun X Y Z f r g => by simp only [smulOfRingMorphism_smul_eq', assoc] }

Depends on / 依赖: comp_smul, homModuleOfRingMorphism, smulOfRingMorphism_smul_eq, smul_comp
-/
def ofRingMorphism : Linear R C := by
  letI := homModuleOfRingMorphism φ
  exact
    { smul_comp := fun X Y Z r f g => by simp only [smulOfRingMorphism_smul_eq, assoc]
      comp_smul := fun X Y Z f r g => by simp only [smulOfRingMorphism_smul_eq', assoc] }

end

end Linear

end CategoryTheory
