/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.QuadraticModuleCat
public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct.Isometries

/-!
# The monoidal category structure on quadratic R-modules

The monoidal structure is simply the structure on the underlying modules, where the tensor product
of two modules is equipped with the form constructed via `QuadraticForm.tmul`.

As with the monoidal structure on `ModuleCat`,
the universe level of the modules must be at least the universe level of the ring,
so that we have a monoidal unit.
For now, we simplify by insisting both universe levels are the same.

## Implementation notes

This file essentially mirrors `Mathlib/Algebra/Category/AlgCat/Monoidal.lean`.
-/

public section

open CategoryTheory
open scoped MonoidalCategory

universe v u

variable {R : Type u} [CommRing R] [Invertible (2 : R)]

namespace QuadraticModuleCat

open QuadraticMap QuadraticForm

namespace instMonoidalCategory

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`. -/
@[simps! form]
/-
**QuadraticModuleCat.instMonoidalCategory.tensorObj** 是 Mathlib 中的一个缩写定义，位于命名空间 
`QuadraticModuleCat.instMonoidalCategory`。
形式化陈述：tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R
参数：X Y : QuadraticModuleCat.{u} R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`.
-/
abbrev tensorObj (X Y : QuadraticModuleCat.{u} R) : QuadraticModuleCat.{u} R :=
  of (X.form.tmul Y.form)

/-- Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`.

We want this up front so that we can re-use it to define `whiskerLeft` and `whiskerRight`. -/
/-
**QuadraticModuleCat.instMonoidalCategory.tensorHom** 是 Mathlib 中的一个缩写定义，位于命名空间 
`QuadraticModuleCat.instMonoidalCategory`。
形式化陈述：tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) : t
ensorObj W Y ⟶ tensorObj X Z
参数：f : W ⟶ X；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition used to build `QuadraticModuleCat.instMonoidalCategory`.

We want this up front so that we can re-use it to define `whiskerLeft` and `whis
kerRight`.
-/
abbrev tensorHom {W X Y Z : QuadraticModuleCat.{u} R} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorObj W Y ⟶ tensorObj X Z :=
  ⟨f.toIsometry.tmul g.toIsometry⟩

end instMonoidalCategory

open instMonoidalCategory


/-
**QuadraticModuleCat.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalCategoryStruct (QuadraticModuleCat.{u} R) where
  tensorObj := instMonoidalCategory.tensorObj
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight {X₁ X₂} (f : X₁ ⟶ X₂) Y := tensorHom f (𝟙 Y)
  tensorHom := tensorHom
  tensorUnit := of (sq (R := R))
  associator X Y Z := ofIso (tensorAssoc X.form Y.form Z.form)
  leftUnitor X := ofIso (tensorLId X.form)
  rightUnitor X := ofIso (tensorRId X.form)
/-
**QuadraticModuleCat.toIsometry_tensorHom** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMo
duleCat`。
形式化陈述：toIsometry_tensorHom {K L M N : QuadraticModuleCat.{u} R} (f : K ⟶ L) (g :
 M ⟶ N) : (f otimesₘ g).toIsometry = f.toIsometry.tmul g.toIsometry
参数：f : K ⟶ L；g : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_tensorHom {K L M N : QuadraticModuleCat.{u} R} (f : K ⟶ L) (g : M ⟶ N) :
    (f ⊗ₘ g).toIsometry = f.toIsometry.tmul g.toIsometry :=
  rfl
/-
**QuadraticModuleCat.toIsometry_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Quadratic
ModuleCat`。
形式化陈述：toIsometry_whiskerLeft (L : QuadraticModuleCat.{u} R) {M N : QuadraticModu
leCat.{u} R} (f : M ⟶ N) : (L ◁ f).toIsometry = .tmul (.id _) f.toIsometry
参数：L : QuadraticModuleCat.{u} R；f : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_whiskerLeft
    (L : QuadraticModuleCat.{u} R) {M N : QuadraticModuleCat.{u} R} (f : M ⟶ N) :
    (L ◁ f).toIsometry = .tmul (.id _) f.toIsometry :=
  rfl
/-
**QuadraticModuleCat.toIsometry_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Quadrati
cModuleCat`。
形式化陈述：toIsometry_whiskerRight {L M : QuadraticModuleCat.{u} R} (f : L ⟶ M) (N : 
QuadraticModuleCat.{u} R) : (f ▷ N).toIsometry = .tmul f.toIsometry (.id _)
参数：f : L ⟶ M；N : QuadraticModuleCat.{u} R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_whiskerRight
    {L M : QuadraticModuleCat.{u} R} (f : L ⟶ M) (N : QuadraticModuleCat.{u} R) :
    (f ▷ N).toIsometry = .tmul f.toIsometry (.id _) :=
  rfl
/-
**QuadraticModuleCat.toIsometry_hom_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Quadra
ticModuleCat`。
形式化陈述：toIsometry_hom_leftUnitor {M : QuadraticModuleCat.{u} R} : (fun_ M).hom.to
Isometry = (tensorLId _).toIsometry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_hom_leftUnitor {M : QuadraticModuleCat.{u} R} :
    (λ_ M).hom.toIsometry = (tensorLId _).toIsometry :=
  rfl
/-
**QuadraticModuleCat.toIsometry_inv_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Quadra
ticModuleCat`。
形式化陈述：toIsometry_inv_leftUnitor {M : QuadraticModuleCat.{u} R} : (fun_ M).inv.to
Isometry = (tensorLId _).symm.toIsometry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_inv_leftUnitor {M : QuadraticModuleCat.{u} R} :
    (λ_ M).inv.toIsometry = (tensorLId _).symm.toIsometry :=
  rfl
/-
**QuadraticModuleCat.toIsometry_hom_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Quadr
aticModuleCat`。
形式化陈述：toIsometry_hom_rightUnitor {M : QuadraticModuleCat.{u} R} : (ρ_ M).hom.toI
sometry = (tensorRId _).toIsometry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_hom_rightUnitor {M : QuadraticModuleCat.{u} R} :
    (ρ_ M).hom.toIsometry = (tensorRId _).toIsometry :=
  rfl
/-
**QuadraticModuleCat.toIsometry_inv_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Quadr
aticModuleCat`。
形式化陈述：toIsometry_inv_rightUnitor {M : QuadraticModuleCat.{u} R} : (ρ_ M).inv.toI
sometry = (tensorRId _).symm.toIsometry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem toIsometry_inv_rightUnitor {M : QuadraticModuleCat.{u} R} :
    (ρ_ M).inv.toIsometry = (tensorRId _).symm.toIsometry :=
  rfl
/-
**QuadraticModuleCat.hom_hom_associator** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModu
leCat`。
形式化陈述：hom_hom_associator {M N K : QuadraticModuleCat.{u} R} : (α_ M N K).hom.toI
sometry = (tensorAssoc _ _ _).toIsometry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem hom_hom_associator {M N K : QuadraticModuleCat.{u} R} :
    (α_ M N K).hom.toIsometry = (tensorAssoc _ _ _).toIsometry :=
  rfl
/-
**QuadraticModuleCat.hom_inv_associator** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModu
leCat`。
形式化陈述：hom_inv_associator {M N K : QuadraticModuleCat.{u} R} : (α_ M N K).inv.toI
sometry = (tensorAssoc _ _ _).symm.toIsometry
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem hom_inv_associator {M N K : QuadraticModuleCat.{u} R} :
    (α_ M N K).inv.toIsometry = (tensorAssoc _ _ _).symm.toIsometry :=
  rfl
/-
**QuadraticModuleCat.toModuleCat_tensor** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModu
leCat`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : Invertible 2] (X Y : Quadrati
cModuleCat R),   (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y).toModuleC
at =     CategoryTheory.MonoidalCategoryStruct.tensorObj X.toModuleCat Y.toModul
eCat
参数：X Y : QuadraticModuleCat R；CategoryTheory.MonoidalCategoryStruct.tensorObj X 
Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
@[simp] theorem toModuleCat_tensor (X Y : QuadraticModuleCat.{u} R) :
    (X ⊗ Y).toModuleCat = X.toModuleCat ⊗ Y.toModuleCat := rfl
/-
**QuadraticModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_map_associator_hom (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (α_ X Y Z).hom =
      (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).hom := rfl
/-
**QuadraticModuleCat.forget** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget₂_map_associator_inv (X Y Z : QuadraticModuleCat.{u} R) :
    (forget₂ (QuadraticModuleCat R) (ModuleCat R)).map (α_ X Y Z).inv =
      (α_ X.toModuleCat Y.toModuleCat Z.toModuleCat).inv := rfl
/-
**QuadraticModuleCat.instMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMo
duleCat`。
形式化陈述：instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidalCategory : MonoidalCategory (QuadraticModuleCat.{u} R) :=
  Monoidal.induced
    (forget₂ (QuadraticModuleCat R) (ModuleCat R))
    { μIso := fun _ _ => Iso.refl _
      εIso := Iso.refl _
      leftUnitor_eq := fun X => by
        simp only [forget₂_obj, forget₂_map, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.refl_hom, MonoidalCategory.tensorIso_hom, MonoidalCategory.tensorHom_id]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        erw [MonoidalCategory.id_whiskerRight]
        simp
        rfl
      rightUnitor_eq := fun X => by
        simp only [forget₂_obj, forget₂_map, Iso.refl_symm, Iso.trans_assoc, Iso.trans_hom,
          Iso.refl_hom, MonoidalCategory.tensorIso_hom, MonoidalCategory.id_tensorHom]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        erw [MonoidalCategory.whiskerLeft_id]
        simp
        rfl
      associator_eq := fun X Y Z => by
        dsimp only [forget₂_obj, forget₂_map_associator_hom]
        simp only [Iso.refl_symm, Iso.trans_hom,
          MonoidalCategory.tensorIso_hom, Iso.refl_hom, MonoidalCategory.id_tensorHom_id]
        dsimp only [toModuleCat_tensor, ModuleCat.of_coe]
        rw [Category.id_comp, Category.id_comp, Category.comp_id, MonoidalCategory.id_tensorHom_id,
          Category.id_comp] }

/-- `forget₂ (QuadraticModuleCat R) (ModuleCat R)` is a monoidal functor. -/
/-
**QuadraticModuleCat.** 是 Mathlib 中的一个示例，位于命名空间 `QuadraticModuleCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`forget₂ (QuadraticModuleCat R) (ModuleCat R)` is a monoidal functor.
-/
example : (forget₂ (QuadraticModuleCat R) (ModuleCat R)).Monoidal := inferInstance

end QuadraticModuleCat

