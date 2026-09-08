/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-!
# Cartesian monoidal structure on slices induced by chosen pullbacks

## Main declarations

- `cartesianMonoidalCategoryOver` provides a cartesian monoidal structure on the slice categories
  `Over X` for all objects `X : C`, induced by chosen pullbacks in the base category `C`.
  This is the computable analogue of the noncomputable instance
  `CategoryTheory.Over.cartesianMonoidalCategory`.

- For a cartesian monoidal category `C`, and for any object `X` of `C`,
  `toOver X` is a functor from `C` to `Over X` which maps an object `A : C` to the projection
  `A ⊗ X ⟶ X` in `Over X`. This is the computable analogue of the functor `Over.star`.

## Main results

- `cartesianMonoidalCategoryOver` proves that the slices of a category with chosen pullbacks are
  cartesian monoidal.

- `toOverPullbackIsoToOver` shows that in a category with chosen pullbacks, for any morphism
  `f : Y ⟶ X`, the functors `toOver X ⋙ pullback f` and `toOver Y` are naturally isomorphic.

- `toOverIteratedSliceForwardIsoPullback` shows that in a category with chosen pullbacks the functor
  `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
  `toOver (Over.mk f) : Over X ⥤ Over (Over.mk f)` post-composed with the iterated slice equivalence
  `Over (Over.mk f) ⥤ Over Y`. Note that the functor `toOver (Over.mk f)` exists by the result
  `cartesianMonoidalCategoryOver`.

### TODO

- Show that the functors `pullback f` are monoidal with respect to
  the cartesian monoidal structures on slices.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category

namespace ChosenPullbacksAlong

open CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]

section

open Limits

variable {X : C} (Y Z : Over X)

/-- The binary fan provided by `fst'` and `snd'`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.binaryFan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cat
egoryTheory.ChosenPullbacksAlong`。
形式化陈述：binaryFan [ChosenPullbacksAlong Z.hom] : BinaryFan Y Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary fan provided by `fst'` and `snd'`.
-/
abbrev binaryFan [ChosenPullbacksAlong Z.hom] : BinaryFan Y Z :=
  BinaryFan.mk (P := (pullback Z.hom ⋙ Over.map Z.hom).obj (Over.mk Y.hom))
    (fst' Y.hom Z.hom) (snd' Y.hom Z.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The binary fan provided by `fst'` and `snd'` is a binary product in `Over X`. -/
/-
**CategoryTheory.ChosenPullbacksAlong.binaryFanIsBinaryProduct** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：binaryFanIsBinaryProduct [ChosenPullbacksAlong Z.hom] : IsLimit (binaryFan
 Y Z)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary fan provided by `fst'` and `snd'` is a binary product in `Over X`.
-/
def binaryFanIsBinaryProduct [ChosenPullbacksAlong Z.hom] :
    IsLimit (binaryFan Y Z) :=
  BinaryFan.IsLimit.mk (binaryFan Y Z)
    (fun u v => Over.homMk (lift (u.left) (v.left) (by rw [Over.w u, Over.w v])) (by simp))
    (by cat_disch) (by cat_disch)
    (fun a b m h₁ h₂ => by
      ext
      dsimp [Over.map, Comma.mapRight]
      cat_disch)

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A computable instance of `CartesianMonoidalCategory` for `Over X` when `C` has
chosen pullbacks. Contrast this with the noncomputable instance provided by
`CategoryTheory.Over.cartesianMonoidalCategory`.
-/
@[instance_reducible]
/-
**CategoryTheory.ChosenPullbacksAlong.cartesianMonoidalCategoryOver** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.ChosenPullbacksAlong`。
形式化陈述：cartesianMonoidalCategoryOver [ChosenPullbacks C] (X : C) : CartesianMonoi
dalCategory (Over X)
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A computable instance of `CartesianMonoidalCategory` for `Over X` when `C` has
chosen pullbacks. Contrast this with the noncomputable instance provided by
`CategoryTheory.Over.cartesianMonoidalCategory`.
-/
def cartesianMonoidalCategoryOver [ChosenPullbacks C] (X : C) :
    CartesianMonoidalCategory (Over X) :=
  ofChosenFiniteProducts (C := Over X)
    ⟨Limits.asEmptyCone (Over.mk (𝟙 X)), Limits.IsTerminal.ofUniqueHom (fun Y ↦ Over.homMk Y.hom)
      fun Y m ↦ Over.OverMorphism.ext (by simpa using m.w)⟩
    (fun Y Z ↦ ⟨ _ , binaryFanIsBinaryProduct Y Z⟩)

namespace Over

open MonoidalCategory

variable [ChosenPullbacks C] {X : C}

attribute [local instance] cartesianMonoidalCategoryOver

@[ext]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorObj_ext** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorObj_ext {A : C} {Y Z : Over X} (f₁ f₂ : A ⟶ (Y otimes Z).left) (e₁ :
 f₁ ≫ fst Y.hom Z.hom = f₂ ≫ fst Y.hom Z.hom) (e₂ : f₁ ≫ snd Y.hom Z.hom = f₂ ≫ 
snd Y.hom Z.hom) : f₁ = f₂
参数：f₁ f₂ : A ⟶ (Y otimes Z).left；e₁ : f₁ ≫ fst Y.hom Z.hom = f₂ ≫ fst Y.hom Z.ho
m；e₂ : f₁ ≫ snd Y.hom Z.hom = f₂ ≫ snd Y.hom Z.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ChosenPullbacksAlong.hom_ext`：hom_ext {W : C} {φ₁ φ₂ : W 
⟶ pullbackObj f g} (h₁ : φ₁ ≫ fst _ _ = φ₂ ≫ fst _ _) (h₂ : φ₁ ≫ snd _ _ = φ₂ ≫ 
snd _ _) : φ₁ = φ₂
-/
lemma tensorObj_ext {A : C} {Y Z : Over X} (f₁ f₂ : A ⟶ (Y ⊗ Z).left)
    (e₁ : f₁ ≫ fst Y.hom Z.hom = f₂ ≫ fst Y.hom Z.hom)
    (e₂ : f₁ ≫ snd Y.hom Z.hom = f₂ ≫ snd Y.hom Z.hom) : f₁ = f₂ :=
  hom_ext Y.hom Z.hom e₁ e₂

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorObj_left** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorObj_left (Y Z : Over X) : (Y otimes Z).left = pullbackObj Y.hom Z.ho
m
参数：Y Z : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_left (Y Z : Over X) : (Y ⊗ Z).left = pullbackObj Y.hom Z.hom := rfl

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorObj_hom** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorObj_hom (Y Z : Over X) : (Y otimes Z).hom = snd Y.hom Z.hom ≫ Z.hom
参数：Y Z : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorObj_hom (Y Z : Over X) : (Y ⊗ Z).hom = snd Y.hom Z.hom ≫ Z.hom := rfl

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorUnit_left** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorUnit_left : (𝟙_ (Over X)).left = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_left : (𝟙_ (Over X)).left = X := rfl

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorUnit_hom** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl
/-
**CategoryTheory.ChosenPullbacksAlong.Over.fst_eq_fst'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：fst_eq_fst' (Y Z : Over X) : CartesianMonoidalCategory.fst Y Z = fst' Y.ho
m Z.hom
参数：Y Z : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fst_eq_fst' (Y Z : Over X) :
    CartesianMonoidalCategory.fst Y Z = fst' Y.hom Z.hom :=
  rfl
/-
**CategoryTheory.ChosenPullbacksAlong.Over.snd_eq_snd'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：snd_eq_snd' (Y Z : Over X) : CartesianMonoidalCategory.snd Y Z = snd' Y.ho
m Z.hom
参数：Y Z : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma snd_eq_snd' (Y Z : Over X) :
    CartesianMonoidalCategory.snd Y Z = snd' Y.hom Z.hom :=
  rfl

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.lift_left** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：lift_left {W Y Z : Over X} (f : W ⟶ Y) (g : W ⟶ Z) : (CartesianMonoidalCat
egory.lift f g).left = lift f.left g.left
参数：f : W ⟶ Y；g : W ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_left {W Y Z : Over X} (f : W ⟶ Y) (g : W ⟶ Z) :
    (CartesianMonoidalCategory.lift f g).left = lift f.left g.left := rfl

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.toUnit_left** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：toUnit_left {Z : Over X} : (toUnit Z).left = Z.hom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toUnit_left {Z : Over X} : (toUnit Z).left = Z.hom := rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.associator_hom_left_fst** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：associator_hom_left_fst (R S T : Over X) : (α_ R S T).hom.left ≫ fst R.hom
 (snd S.hom T.hom ≫ T.hom) = fst (R otimes S).hom T.hom ≫ fst R.hom S.hom
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_fst`：associator_
hom_fst (X Y Z : C) : (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma associator_hom_left_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ fst R.hom (snd S.hom T.hom ≫ T.hom) =
      fst (R ⊗ S).hom T.hom ≫ fst R.hom S.hom :=
  congr_arg CommaMorphism.left (associator_hom_fst R S T)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.associator_hom_left_snd_fst** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：associator_hom_left_snd_fst (R S T : Over X) : (α_ R S T).hom.left ≫ snd R
.hom (snd S.hom T.hom ≫ T.hom) ≫ fst S.hom T.hom = fst (R otimes S).hom T.hom ≫ 
snd R.hom S.hom
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_snd_fst`：associa
tor_hom_snd_fst (X Y Z : C) : (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd
 _ _

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma associator_hom_left_snd_fst (R S T : Over X) :
    (α_ R S T).hom.left ≫ snd R.hom (snd S.hom T.hom ≫ T.hom) ≫ fst S.hom T.hom =
      fst (R ⊗ S).hom T.hom ≫ snd R.hom S.hom :=
  congr_arg CommaMorphism.left (associator_hom_snd_fst R S T)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.associator_hom_left_snd_snd** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：associator_hom_left_snd_snd (R S T : Over X) : (α_ R S T).hom.left ≫ snd R
.hom (snd S.hom T.hom ≫ T.hom) ≫ snd S.hom T.hom = snd (R otimes S).hom T.hom
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_hom_snd_snd`：associa
tor_hom_snd_snd (X Y Z : C) : (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _
-/
lemma associator_hom_left_snd_snd (R S T : Over X) :
    (α_ R S T).hom.left ≫ snd R.hom (snd S.hom T.hom ≫ T.hom) ≫ snd S.hom T.hom =
      snd (R ⊗ S).hom T.hom :=
  congr_arg CommaMorphism.left (associator_hom_snd_snd R S T)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.associator_inv_left_fst_fst** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：associator_inv_left_fst_fst (R S T : Over X) : (α_ R S T).inv.left ≫ fst (
snd R.hom S.hom ≫ S.hom) T.hom ≫ fst R.hom S.hom = fst R.hom (S otimes T).hom
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_inv_fst_fst`：associa
tor_inv_fst_fst (X Y Z : C) : (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _
-/
lemma associator_inv_left_fst_fst (R S T : Over X) :
    (α_ R S T).inv.left ≫ fst (snd R.hom S.hom ≫ S.hom) T.hom ≫ fst R.hom S.hom =
      fst R.hom (S ⊗ T).hom :=
  congr_arg CommaMorphism.left (associator_inv_fst_fst R S T)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.associator_inv_left_fst_snd** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：associator_inv_left_fst_snd (R S T : Over X) : (α_ R S T).inv.left ≫ fst (
snd R.hom S.hom ≫ S.hom) T.hom ≫ snd R.hom S.hom = snd R.hom (S otimes T).hom ≫ 
fst S.hom T.hom
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_inv_fst_snd`：associa
tor_inv_fst_snd (X Y Z : C) : (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst
 _ _

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma associator_inv_left_fst_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ fst (snd R.hom S.hom ≫ S.hom) T.hom ≫ snd R.hom S.hom =
      snd R.hom (S ⊗ T).hom ≫ fst S.hom T.hom :=
  congr_arg CommaMorphism.left (associator_inv_fst_snd R S T)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.associator_inv_left_snd** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：associator_inv_left_snd (R S T : Over X) : (α_ R S T).inv.left ≫ snd (snd 
R.hom S.hom ≫ S.hom) T.hom = snd R.hom (S otimes T).hom ≫ snd S.hom T.hom
参数：R S T : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.associator_inv_snd`：associator_
inv_snd (X Y Z : C) : (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma associator_inv_left_snd (R S T : Over X) :
    (α_ R S T).inv.left ≫ snd (snd R.hom S.hom ≫ S.hom) T.hom =
      snd R.hom (S ⊗ T).hom ≫ snd S.hom T.hom :=
  congr_arg CommaMorphism.left (associator_inv_snd R S T)

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.leftUnitor_hom_left** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：leftUnitor_hom_left (Z : Over X) : (fun_ Z).hom.left = snd _ Z.hom
参数：Z : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftUnitor_hom_left (Z : Over X) :
    (λ_ Z).hom.left = snd _ Z.hom := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.leftUnitor_inv_left_fst** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：leftUnitor_inv_left_fst (Z : Over X) : (fun_ Z).inv.left ≫ fst (𝟙 X) Z.hom
 = Z.hom
参数：Z : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_fst`：leftUnitor_
inv_fst (X : C) : (fun_ X).inv ≫ fst _ _ = toUnit _
-/
lemma leftUnitor_inv_left_fst (Z : Over X) :
    (λ_ Z).inv.left ≫ fst (𝟙 X) Z.hom = Z.hom :=
  congr_arg CommaMorphism.left (leftUnitor_inv_fst Z)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.leftUnitor_inv_left_snd** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：leftUnitor_inv_left_snd (Y : Over X) : (fun_ Y).inv.left ≫ snd (𝟙 X) Y.hom
 = 𝟙 Y.left
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.leftUnitor_inv_snd`：leftUnitor_
inv_snd (X : C) : (fun_ X).inv ≫ snd _ _ = 𝟙 X
-/
lemma leftUnitor_inv_left_snd (Y : Over X) :
    (λ_ Y).inv.left ≫ snd (𝟙 X) Y.hom = 𝟙 Y.left :=
  congr_arg CommaMorphism.left (leftUnitor_inv_snd Y)

@[simp]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.rightUnitor_hom_left** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：rightUnitor_hom_left (Y : Over X) : (ρ_ Y).hom.left = fst _ (𝟙 X)
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma rightUnitor_hom_left (Y : Over X) :
    (ρ_ Y).hom.left = fst _ (𝟙 X) := rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.rightUnitor_inv_left_fst** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：rightUnitor_inv_left_fst (Y : Over X) : (ρ_ Y).inv.left ≫ fst Y.hom (𝟙 X) 
= 𝟙 Y.left
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_fst`：rightUnito
r_inv_fst (X : C) : (ρ_ X).inv ≫ fst _ _ = 𝟙 X
-/
lemma rightUnitor_inv_left_fst (Y : Over X) :
    (ρ_ Y).inv.left ≫ fst Y.hom (𝟙 X) = 𝟙 Y.left :=
  congr_arg CommaMorphism.left (rightUnitor_inv_fst Y)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.rightUnitor_inv_left_snd** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：rightUnitor_inv_left_snd (Y : Over X) : (ρ_ Y).inv.left ≫ snd Y.hom (𝟙 X) 
= Y.hom
参数：Y : Over X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.rightUnitor_inv_snd`：rightUnito
r_inv_snd (X : C) : (ρ_ X).inv ≫ snd _ _ = toUnit _
-/
lemma rightUnitor_inv_left_snd (Y : Over X) :
    (ρ_ Y).inv.left ≫ snd Y.hom (𝟙 X) = Y.hom :=
  congr_arg CommaMorphism.left (rightUnitor_inv_snd Y)
/-
**CategoryTheory.ChosenPullbacksAlong.Over.whiskerLeft_left** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：whiskerLeft_left {R S T : Over X} (f : S ⟶ T) : (R ◁ f).left = pullbackMap
 R.hom T.hom R.hom S.hom (𝟙 _) f.left (𝟙 _)
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_left {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left = pullbackMap R.hom T.hom R.hom S.hom (𝟙 _) f.left (𝟙 _) :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.whiskerLeft_left_fst** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) : (R ◁ f).left ≫ fst R.h
om T.hom = fst R.hom S.hom
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_fst`：whiskerLeft_fs
t (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ fst _ _ = fst _ _
-/
lemma whiskerLeft_left_fst {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ fst R.hom T.hom = fst R.hom S.hom :=
  congr_arg CommaMorphism.left (whiskerLeft_fst R f)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.whiskerLeft_left_snd** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) : (R ◁ f).left ≫ snd R.h
om T.hom = snd R.hom S.hom ≫ f.left
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerLeft_snd`：whiskerLeft_sn
d (X : C) {Y Z : C} (f : Y ⟶ Z) : X ◁ f ≫ snd _ _ = snd _ _ ≫ f

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma whiskerLeft_left_snd {R S T : Over X} (f : S ⟶ T) :
    (R ◁ f).left ≫ snd R.hom T.hom = snd R.hom S.hom ≫ f.left :=
  congr_arg CommaMorphism.left (whiskerLeft_snd R f)
/-
**CategoryTheory.ChosenPullbacksAlong.Over.whiskerRight_left** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：whiskerRight_left {R S T : Over X} (f : S ⟶ T) : (f ▷ R).left = pullbackMa
p T.hom R.hom S.hom R.hom f.left (𝟙 _) (𝟙 _)
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_left {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left = pullbackMap T.hom R.hom S.hom R.hom f.left (𝟙 _) (𝟙 _) :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.whiskerRight_left_fst** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) : (f ▷ R).left ≫ fst T.
hom R.hom = fst S.hom R.hom ≫ f.left
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_fst`：whiskerRight_
fst {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ fst _ _ = fst _ _ ≫ f

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma whiskerRight_left_fst {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ fst T.hom R.hom = fst S.hom R.hom ≫ f.left :=
  congr_arg CommaMorphism.left (whiskerRight_fst f R)

@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.whiskerRight_left_snd** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) : (f ▷ R).left ≫ snd T.
hom R.hom = snd S.hom R.hom
参数：f : S ⟶ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.whiskerRight_snd`：whiskerRight_
snd {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z ≫ snd _ _ = snd _ _
-/
lemma whiskerRight_left_snd {R S T : Over X} (f : S ⟶ T) :
    (f ▷ R).left ≫ snd T.hom R.hom = snd S.hom R.hom :=
  congr_arg CommaMorphism.left (whiskerRight_snd f R)
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorHom_left** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) : (f otimesₘ g).
left = pullbackMap S.hom U.hom R.hom T.hom f.left g.left (𝟙 _)
参数：f : R ⟶ S；g : T ⟶ U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom_left {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left = pullbackMap S.hom U.hom R.hom T.hom f.left g.left (𝟙 _) :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorHom_left_fst** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorHom_left_fst {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) : (f otimesₘ
 g).left ≫ fst S.hom U.hom = fst R.hom T.hom ≫ f.left
参数：f : R ⟶ S；g : T ⟶ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_fst`：tensorHom_fst {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ fst _ _ = fst _ _ 
≫ f

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma tensorHom_left_fst {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left ≫ fst S.hom U.hom = fst R.hom T.hom ≫ f.left :=
  congr_arg CommaMorphism.left (tensorHom_fst f g)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.ChosenPullbacksAlong.Over.tensorHom_left_snd** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.ChosenPullbacksAlong.Over`。
形式化陈述：tensorHom_left_snd {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) : (f otimesₘ
 g).left ≫ snd S.hom U.hom = snd R.hom T.hom ≫ g.left
参数：f : R ⟶ S；g : T ⟶ U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.tensorHom_snd`：tensorHom_snd {X
₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) : (f otimesₘ g) ≫ snd _ _ = snd _ _ 
≫ g

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma tensorHom_left_snd {R S T U : Over X} (f : R ⟶ S) (g : T ⟶ U) :
    (f ⊗ₘ g).left ≫ snd S.hom U.hom = snd R.hom T.hom ≫ g.left :=
  congr_arg CommaMorphism.left (tensorHom_snd f g)

end Over

end ChosenPullbacksAlong

section ToOver

open ChosenPullbacksAlong CartesianMonoidalCategory MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]

set_option backward.defeqAttrib.useBackward true in
/-- The functor which maps an object `A` in `C` to the projection `A ⊗ X ⟶ X` in `Over X`.
This is the computable analogue of the functor `Over.star`. -/
@[simps! obj_left obj_hom]
/-
**CategoryTheory.toOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：toOver (X : C) : C ⥤ Over X where obj A
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor which maps an object `A` in `C` to the projection `A ⊗ X ⟶ X` in `Ov
er X`.
This is the computable analogue of the functor `Over.star`.
-/
def toOver (X : C) : C ⥤ Over X where
  obj A := Over.mk <| CartesianMonoidalCategory.snd A X
  map f := Over.homMk (f ▷ X)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.toOver_map** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：toOver_map {X : C} {A A' : C} (f : A ⟶ A') : (toOver X).map f = Over.homMk
 (f ▷ X)
参数：f : A ⟶ A'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toOver_map {X : C} {A A' : C} (f : A ⟶ A') :
    (toOver X).map f = Over.homMk (f ▷ X) := by
  simp [toOver]

variable (C)

/-- The functor from `C` to `Over (𝟙_ C)` which sends `X : C` to `Over.mk <| toUnit X`. -/
@[simps! obj_left obj_hom map_left]
/-
**CategoryTheory.toOverUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：toOverUnit : C ⥤ Over (𝟙_ C) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `C` to `Over (𝟙_ C)` which sends `X : C` to `Over.mk <| toUnit 
X`.
-/
def toOverUnit : C ⥤ Over (𝟙_ C) where
  obj X := Over.mk <| toUnit X
  map f := Over.homMk f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The slice category over the terminal unit object is equivalent to the original category. -/
@[simps]
/-
**CategoryTheory.equivToOverUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：equivToOverUnit : Over (𝟙_ C) ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The slice category over the terminal unit object is equivalent to the original c
ategory.
-/
def equivToOverUnit : Over (𝟙_ C) ≌ C where
  functor := Over.forget _
  inverse := toOverUnit _
  unitIso := NatIso.ofComponents fun X => Over.isoMk (Iso.refl _)
  counitIso := NatIso.ofComponents fun X => Iso.refl _

variable {C}

attribute [local instance] ChosenPullbacksAlong.cartesianMonoidalCategoryToUnit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The isomorphism of functors `toOverUnit C ⋙ ChosenPullbacksAlong.pullback (toUnit X)` and
`toOver X`. -/
@[simps!]
/-
**CategoryTheory.toOverUnitPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：toOverUnitPullback (X : C) : toOverUnit C ⋙ pullback (toUnit X) ≅ toOver X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of functors `toOverUnit C ⋙ ChosenPullbacksAlong.pullback (toUni
t X)` and
`toOver X`.
-/
def toOverUnitPullback (X : C) :
    toOverUnit C ⋙ pullback (toUnit X) ≅ toOver X :=
  NatIso.ofComponents fun X => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `toOver X` is the right adjoint to the functor `Over.forget X`. -/
@[simps! unit_app counit_app]
/-
**CategoryTheory.forgetAdjToOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：forgetAdjToOver (X : C) : Over.forget X ⊣ toOver X where unit.app Z
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `toOver X` is the right adjoint to the functor `Over.forget X`.
-/
def forgetAdjToOver (X : C) : Over.forget X ⊣ toOver X where
  unit.app Z := Over.homMk (lift (𝟙 Z.left) (Z.hom))
  counit.app Z := fst Z X
/-
**CategoryTheory.forgetAdjToOver.homEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.forgetAdjToOver`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.CartesianMonoidalCategory C]   {X : C} (Z : CategoryTheory.Over X) (A
 : C) (f : Z ⟶ (CategoryTheory.toOver X).obj A),   ((CategoryTheory.forgetAdjToO
ver X).homEquiv Z A).symm f =     CategoryTheory.CategoryStruct.comp (CategoryTh
eory.Over.Hom.left f)       (CategoryTheory.SemiCartesianMonoidalCategory.fst A 
X)
参数：Z : CategoryTheory.Over X；A : C；f : Z ⟶ (CategoryTheory.toOver X).obj A；(Cate
goryTheory.forgetAdjToOver X).homEquiv Z A；CategoryTheory.Over.Hom.left f；Catego
ryTheory.SemiCartesianMonoidalCategory.fst A X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.forgetAdjToOver_counit_app`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.CartesianMonoidalCategor
y C]   (X Z : C), (CategoryTheo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem forgetAdjToOver.homEquiv_symm {X : C} (Z : Over X) (A : C) (f : Z ⟶ (toOver X).obj A) :
    ((forgetAdjToOver X).homEquiv Z A).symm f = f.left ≫ (fst _ _) := by
  rw [Adjunction.homEquiv_counit, forgetAdjToOver_counit_app]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of functors `toOver (𝟙_ C)` and `toOverUnit C`. -/
@[simps!]
/-
**CategoryTheory.toOverIsoToOverUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：toOverIsoToOverUnit : toOver (𝟙_ C) ≅ toOverUnit C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of functors `toOver (𝟙_ C)` and `toOverUnit C`.
-/
def toOverIsoToOverUnit : toOver (𝟙_ C) ≅ toOverUnit C :=
  (forgetAdjToOver (𝟙_ C)).rightAdjointUniq (equivToOverUnit C |>.toAdjunction)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism between the functors `toOver Y` and `toOver X ⋙ pullback f`
for any morphism `f : X ⟶ Y`. -/
@[simps!]
/-
**CategoryTheory.toOverPullbackIsoToOver** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：toOverPullbackIsoToOver {X Y : C} (f : Y ⟶ X) [ChosenPullbacksAlong f] : t
oOver X ⋙ pullback f ≅ toOver Y
参数：f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism between the functors `toOver Y` and `toOver X ⋙ pullback f
`
for any morphism `f : X ⟶ Y`.
-/
def toOverPullbackIsoToOver {X Y : C} (f : Y ⟶ X) [ChosenPullbacksAlong f] :
    toOver X ⋙ pullback f ≅ toOver Y :=
  conjugateIsoEquiv ((mapPullbackAdj f).comp (forgetAdjToOver X))
    (forgetAdjToOver Y) (Over.mapForget f)

attribute [local instance] cartesianMonoidalCategoryOver

set_option backward.isDefEq.respectTransparency.types false in
omit [CartesianMonoidalCategory C] in
/-- The functor `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
`toOver : Over X ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivalence `Over (Over.mk f) ⥤ Over Y`. -/
@[simps!]
/-
**CategoryTheory.toOverIteratedSliceForwardIsoPullback** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory`。
形式化陈述：toOverIteratedSliceForwardIsoPullback [ChosenPullbacks C] {X Y : C} (f : Y
 ⟶ X) : toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f
参数：f : Y ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `pullback f : Over X ⥤ Over Y` is naturally isomorphic to
`toOver : Over X ⥤ Over (Over.mk f)` post-composed with the
iterated slice equivalence `Over (Over.mk f) ⥤ Over Y`.
-/
def toOverIteratedSliceForwardIsoPullback [ChosenPullbacks C] {X Y : C} (f : Y ⟶ X) :
    toOver (Over.mk f) ⋙ (Over.mk f).iteratedSliceForward ≅ pullback f :=
  conjugateIsoEquiv ((Over.mk f).iteratedSliceEquiv.symm.toAdjunction.comp (forgetAdjToOver _))
  (mapPullbackAdj f) (eqToIso (Over.iteratedSliceBackward_forget (Over.mk f)))

end ToOver

end CategoryTheory

