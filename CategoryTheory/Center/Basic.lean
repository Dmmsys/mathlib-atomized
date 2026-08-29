/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Endomorphism

/-!
# The center of a category

Given a category `C`, we introduce an abbreviation `CatCenter C` for
the center of the category `C`, which is `End (𝟭 C)`, the
type of endomorphisms of the identity functor of `C`.

## References
* https://ncatlab.org/nlab/show/center+of+a+category

-/

public section
universe v u

namespace CategoryTheory

open Category

variable (C : Type u) [Category.{v} C]

/--
Definition of `CatCenter` / `CatCenter` 的定义

English:
abbreviation CatCenter
  body: End (𝟭 C)

中文:
缩写 CatCenter
  定义体: End (𝟭 C)
-/
abbrev CatCenter := End (𝟭 C)

namespace CatCenter

variable {C}

/--
Definition of `app` / `app` 的定义

English:
abbreviation app
  signature: (x : CatCenter C) (X : C)
  body: NatTrans.app x X

@[ext]

中文:
缩写 app
  签名: (x : CatCenter C) (X : C)
  定义体: NatTrans.app x X

@[ext]

Depends on / 依赖: NatTrans, NatTrans.app
-/
abbrev app (x : CatCenter C) (X : C) : X ⟶ X := NatTrans.app x X

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (x y : CatCenter C) (h : forall (X : C), x.app X = y.app X)
  statement: x = y
  proof: NatTrans.ext (funext h)

@[reassoc]

中文:
引理 ext
  条件: (x y : CatCenter C) (h : 对任意 (X : C), x.app X = y.app X)
  结论: x = y
  证明: NatTrans.ext (funext h)

@[reassoc]

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma ext (x y : CatCenter C) (h : forall (X : C), x.app X = y.app X) : x = y :=
  NatTrans.ext (funext h)

@[reassoc]
/--
lemma `naturality` / 引理 `naturality`

English:
lemma naturality
  given: (z : CatCenter C) {X Y : C} (f : X ⟶ Y)
  proof: NatTrans.naturality z f

@[reassoc]

中文:
引理 naturality
  条件: (z : CatCenter C) {X Y : C} (f : X ⟶ Y)
  证明: NatTrans.naturality z f

@[reassoc]

Depends on / 依赖: NatTrans, NatTrans.naturality, naturality
-/
lemma naturality (z : CatCenter C) {X Y : C} (f : X ⟶ Y) :
    f ≫ z.app Y = z.app X ≫ f := NatTrans.naturality z f

@[reassoc]
/--
lemma `mul_app'` / 引理 `mul_app'`

English:
lemma mul_app'
  given: (x y : CatCenter C) (X : C)
  statement: (x * y).app X = y.app X ≫ x.app X
  proof: rfl

@[reassoc]

中文:
引理 mul_app'
  条件: (x y : CatCenter C) (X : C)
  结论: (x * y).app X = y.app X ≫ x.app X
  证明: rfl

@[reassoc]
-/
lemma mul_app' (x y : CatCenter C) (X : C) : (x * y).app X = y.app X ≫ x.app X := rfl

@[reassoc]
/--
lemma `mul_app` / 引理 `mul_app`

English:
lemma mul_app
  given: (x y : CatCenter C) (X : C)
  statement: (x * y).app X = x.app X ≫ y.app X
  proof: by
  rw [mul_app']
  exact x.naturality (y.app X)

中文:
引理 mul_app
  条件: (x y : CatCenter C) (X : C)
  结论: (x * y).app X = x.app X ≫ y.app X
  证明: by
  rw [mul_app']
  exact x.naturality (y.app X)

Depends on / 依赖: mul_app, naturality, x.naturality, y.app
-/
lemma mul_app (x y : CatCenter C) (X : C) : (x * y).app X = x.app X ≫ y.app X := by
  rw [mul_app']
  exact x.naturality (y.app X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMulCommutative (CatCenter C)
  body: by
    ext X
    rw [mul_app' x y]; rw [mul_app y x]

中文:
实例 :
  签名: IsMulCommutative (CatCenter C)
  定义体: by
    ext X
    rw [mul_app' x y]; rw [mul_app y x]

Depends on / 依赖: mul_app
-/
instance : IsMulCommutative (CatCenter C) where
  is_comm.comm x y := by
    ext X
    rw [mul_app' x y]; rw [mul_app y x]

instance {X Y : C} : SMul (CatCenter C) (X ⟶ Y) where
  smul z f := f ≫ z.app Y

/--
lemma `smul_eq` / 引理 `smul_eq`

English:
lemma smul_eq
  given: (z : CatCenter C) {X Y : C} (f : X ⟶ Y)
  statement: z • f = f ≫ z.app Y
  proof: rfl

中文:
引理 smul_eq
  条件: (z : CatCenter C) {X Y : C} (f : X ⟶ Y)
  结论: z • f = f ≫ z.app Y
  证明: rfl
-/
lemma smul_eq (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = f ≫ z.app Y := rfl

/--
lemma `smul_eq'` / 引理 `smul_eq'`

English:
lemma smul_eq'
  given: (z : CatCenter C) {X Y : C} (f : X ⟶ Y)
  statement: z • f = z.app X ≫ f
  proof: z.naturality f

中文:
引理 smul_eq'
  条件: (z : CatCenter C) {X Y : C} (f : X ⟶ Y)
  结论: z • f = z.app X ≫ f
  证明: z.naturality f

Depends on / 依赖: naturality, z.naturality
-/
lemma smul_eq' (z : CatCenter C) {X Y : C} (f : X ⟶ Y) : z • f = z.app X ≫ f :=
  z.naturality f

instance {X Y : C} : SMul (CatCenter C)ˣ (X ≅ Y) where
  smul z e :=
    { hom := z.1 • e.hom
      inv := (z⁻¹).1 • e.inv
      hom_inv_id := by
        rw [smul_eq]; rw [smul_eq']; rw [Category.assoc]; rw [← mul_app_assoc]
        simp
      inv_hom_id := by
        rw [smul_eq]; rw [smul_eq']; rw [Category.assoc]; rw [← mul_app_assoc]
        simp }

@[reassoc]
/--
lemma `smul_iso_hom_eq` / 引理 `smul_iso_hom_eq`

English:
lemma smul_iso_hom_eq
  given: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  proof: rfl

@[reassoc]

中文:
引理 smul_iso_hom_eq
  条件: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  证明: rfl

@[reassoc]
-/
lemma smul_iso_hom_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).hom = f.hom ≫ z.1.app Y := rfl

@[reassoc]
/--
lemma `smul_iso_hom_eq'` / 引理 `smul_iso_hom_eq'`

English:
lemma smul_iso_hom_eq'
  given: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  proof: z.1.naturality f.hom

@[reassoc]

中文:
引理 smul_iso_hom_eq'
  条件: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  证明: z.1.naturality f.hom

@[reassoc]

Depends on / 依赖: f.hom, naturality
-/
lemma smul_iso_hom_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).hom = z.1.app X ≫ f.hom :=
  z.1.naturality f.hom

@[reassoc]
/--
lemma `smul_iso_inv_eq` / 引理 `smul_iso_inv_eq`

English:
lemma smul_iso_inv_eq
  given: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  proof: rfl

@[reassoc]

中文:
引理 smul_iso_inv_eq
  条件: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  证明: rfl

@[reassoc]
-/
lemma smul_iso_inv_eq (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).inv = f.inv ≫ (z⁻¹.1).app X := rfl

@[reassoc]
/--
lemma `smul_iso_inv_eq'` / 引理 `smul_iso_inv_eq'`

English:
lemma smul_iso_inv_eq'
  given: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  proof: z.2.naturality f.inv

中文:
引理 smul_iso_inv_eq'
  条件: (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y)
  证明: z.2.naturality f.inv

Depends on / 依赖: f.inv, naturality
-/
lemma smul_iso_inv_eq' (z : (CatCenter C)ˣ) {X Y : C} (f : X ≅ Y) :
    (z • f).inv = (z⁻¹.1).app Y ≫ f.inv :=
  z.2.naturality f.inv

end CatCenter

end CategoryTheory
