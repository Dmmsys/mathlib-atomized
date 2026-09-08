/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Action.Concrete
public import Mathlib.CategoryTheory.Action.Limits

/-!
# Induced monoidal structure on `Action V G`

We show:

* When `V` is monoidal, braided, or symmetric, so is `Action V G`.
* When `V` is rigid and `G` is a group, `Action V G` is also rigid.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

variable {V : Type*} [Category* V] {G : Type*} [Monoid G]

namespace Action

section Monoidal

open MonoidalCategory

variable [MonoidalCategory V]

@[simps! tensorUnit_V tensorObj_V tensorHom_hom whiskerLeft_hom whiskerRight_hom
  associator_hom_hom associator_inv_hom leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom, reducible]
/-
**Action.instMonoidalCategory** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：instMonoidalCategory : MonoidalCategory (Action V G) where tensorObj X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidalCategory : MonoidalCategory (Action V G) where
  tensorObj X Y := Action.mk (X.V ⊗ Y.V) _
  tensorUnit := Action.mk (𝟙_ _) _
  __ := Monoidal.transport (Action.functorCategoryEquivalence _ _).symm

@[simp]
/-
**Action.tensorUnit_** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorUnit_ρ {g : G} :
    @DFunLike.coe (G →* End (𝟙_ V)) _ _ _ (𝟙_ (Action V G)).ρ g = 𝟙 (𝟙_ V) :=
  rfl

@[simp]
/-
**Action.tensor_** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensor_ρ {X Y : Action V G} {g : G} :
    @DFunLike.coe (G →* End (X.V ⊗ Y.V)) _ _ _ (X ⊗ Y).ρ g = X.ρ g ⊗ₘ Y.ρ g :=
  rfl

/-- Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the trivial action
is isomorphic to the tensor unit of `Action V G`. -/
/-
**Action.tensorUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1
参数：f : 𝟙_ V ≅ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an object `X` isomorphic to the tensor unit of `V`, `X` equipped with the 
trivial action
is isomorphic to the tensor unit of `Action V G`.
-/
def tensorUnitIso {X : V} (f : 𝟙_ V ≅ X) : 𝟙_ (Action V G) ≅ Action.mk X 1 :=
  Action.mkIso f

variable (V G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Action.forget V G).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.forget_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_ε : ε (Action.forget V G) = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.forget_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_η : η (Action.forget V G) = 𝟙 _ := rfl

variable {V G}

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.forget_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_μ (X Y : Action V G) : μ (Action.forget V G) X Y = 𝟙 _ := rfl
set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.forget_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma forget_δ (X Y : Action V G) : δ (Action.forget V G) X Y = 𝟙 _ := rfl

variable (V G)

section

variable [BraidedCategory V]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BraidedCategory (Action V G) :=
  .ofFaithful (Action.forget V G) fun X Y ↦ mkIso (β_ _ _) fun g ↦ by simp

@[simp]
/-
**Action.** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem β_hom_hom {X Y : Action V G} : (β_ X Y).hom.hom = (β_ X.V Y.V).hom := rfl

@[simp]
/-
**Action.** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem β_inv_hom {X Y : Action V G} : (β_ X Y).inv.hom = (β_ X.V Y.V).inv := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When `V` is braided the forgetful functor `Action V G` to `V` is braided. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `V` is braided the forgetful functor `Action V G` to `V` is braided.
-/
instance : (Action.forget V G).Braided where

end

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SymmetricCategory V] : SymmetricCategory (Action V G) :=
  .ofFaithful (Action.forget V G)

section

variable [Preadditive V] [MonoidalPreadditive V]

attribute [local simp] MonoidalPreadditive.whiskerLeft_add MonoidalPreadditive.add_whiskerRight

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalPreadditive (Action V G) where

variable {R : Type*} [Semiring R] [Linear R V] [MonoidalLinear R V]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidalLinear R (Action V G) where

end

noncomputable section

/-- Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor. -/
/-
**Action.FunctorCategoryEquivalence.functorMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `A
ction.FunctorCategoryEquivalence`。
形式化陈述：(V : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} V] →     (G 
: Type u_2) →       [inst_1 : Monoid G] →         [inst_2 : CategoryTheory.Monoi
dalCategory V] → Action.FunctorCategoryEquivalence.functor.Monoidal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrading the functor `Action V G ⥤ (SingleObj G ⥤ V)` to a monoidal functor.
-/
instance FunctorCategoryEquivalence.functorMonoidal :
    (FunctorCategoryEquivalence.functor (V := V) (G := G)).Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).inverse.Monoidal
/-
**Action.functorCategoryEquivalenceFunctorMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `Ac
tion`。
形式化陈述：functorCategoryEquivalenceFunctorMonoidal : (functorCategoryEquivalence V 
G).functor.Monoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorCategoryEquivalenceFunctorMonoidal :
    (functorCategoryEquivalence V G).functor.Monoidal :=
  inferInstanceAs FunctorCategoryEquivalence.functor.Monoidal

/-- Upgrading the functor `(SingleObj G ⥤ V) ⥤ Action V G` to a monoidal functor. -/
/-
**Action.FunctorCategoryEquivalence.inverseMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `A
ction.FunctorCategoryEquivalence`。
形式化陈述：(V : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} V] →     (G 
: Type u_2) →       [inst_1 : Monoid G] →         [inst_2 : CategoryTheory.Monoi
dalCategory V] → Action.FunctorCategoryEquivalence.inverse.Monoidal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upgrading the functor `(SingleObj G ⥤ V) ⥤ Action V G` to a monoidal functor.
-/
instance FunctorCategoryEquivalence.inverseMonoidal :
    (FunctorCategoryEquivalence.inverse (V := V) (G := G)).Monoidal :=
  inferInstanceAs (Monoidal.equivalenceTransported
    (Action.functorCategoryEquivalence V G).symm).functor.Monoidal
/-
**Action.functorCategoryEquivalenceInverseMonoidal** 是 Mathlib 中的一个实例，位于命名空间 `Ac
tion`。
形式化陈述：functorCategoryEquivalenceInverseMonoidal : (functorCategoryEquivalence V 
G).inverse.Monoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorCategoryEquivalenceInverseMonoidal :
    (functorCategoryEquivalence V G).inverse.Monoidal :=
  inferInstanceAs FunctorCategoryEquivalence.inverse.Monoidal

@[simp]
/-
**Action.FunctorCategoryEquivalence.functor_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FunctorCategoryEquivalence.functor_ε :
    ε (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _ := rfl

@[simp]
/-
**Action.FunctorCategoryEquivalence.functor_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FunctorCategoryEquivalence.functor_η :
    η (FunctorCategoryEquivalence.functor (V := V) (G := G)) = 𝟙 _ := rfl

@[simp]
/-
**Action.FunctorCategoryEquivalence.functor_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FunctorCategoryEquivalence.functor_μ (A B : Action V G) :
    μ FunctorCategoryEquivalence.functor A B = 𝟙 _ := rfl

@[simp]
/-
**Action.FunctorCategoryEquivalence.functor_** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma FunctorCategoryEquivalence.functor_δ (A B : Action V G) :
    δ FunctorCategoryEquivalence.functor A B = 𝟙 _ := rfl


variable (H : Type*) [Group H]
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RightRigidCategory V] : RightRigidCategory (SingleObj H ⥤ V) := by
  infer_instance

/-- If `V` is right rigid, so is `Action V G`. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` is right rigid, so is `Action V G`.
-/
instance [RightRigidCategory V] : RightRigidCategory (Action V H) :=
  rightRigidCategoryOfEquivalence
    (functorCategoryEquivalence V H).toAdjunction
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LeftRigidCategory V] : LeftRigidCategory (SingleObj H ⥤ V) := by
  infer_instance

/-- If `V` is left rigid, so is `Action V G`. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` is left rigid, so is `Action V G`.
-/
instance [LeftRigidCategory V] : LeftRigidCategory (Action V H) :=
  leftRigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RigidCategory V] : RigidCategory (SingleObj H ⥤ V) := by
  infer_instance

/-- If `V` is rigid, so is `Action V G`. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` is rigid, so is `Action V G`.
-/
instance [RigidCategory V] : RigidCategory (Action V H) :=
  rigidCategoryOfEquivalence (functorCategoryEquivalence V H).toAdjunction

variable {V H}
variable (X : Action V H)

@[simp]
/-
**Action.rightDual_v** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDual_v [RightRigidCategory V] : Xᘁ.V = X.Vᘁ :=
  rfl

@[simp]
/-
**Action.leftDual_v** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDual_v [LeftRigidCategory V] : (ᘁX).V = ᘁX.V :=
  rfl
/-
**Action.rightDual_** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rightDual_ρ [RightRigidCategory V] (h : H) : Xᘁ.ρ h = (X.ρ (h⁻¹ : H))ᘁ := by
  rw [← SingleObj.inv_as_inv]; rfl
/-
**Action.leftDual_** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leftDual_ρ [LeftRigidCategory V] (h : H) : (ᘁX).ρ h = ᘁX.ρ (h⁻¹ : H) := by
  rw [← SingleObj.inv_as_inv]; rfl

end

end Monoidal

section

open MonoidalCategory

variable (G : Type u)

/-- The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on
each factor. -/
@[simps! hom_hom inv_hom]
/-
**Action.diagonalSuccIsoTensorDiagonal** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：diagonalSuccIsoTensorDiagonal [Monoid G] (n : Nat) : diagonal G (n + 1) ≅ 
leftRegular G otimes diagonal G n
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left mult
iplication on
each factor.
-/
noncomputable def diagonalSuccIsoTensorDiagonal [Monoid G] (n : ℕ) :
    diagonal G (n + 1) ≅ leftRegular G ⊗ diagonal G n :=
  mkIso (Fin.consEquiv _).symm.toIso fun _ => rfl

variable [Group G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `X : Action (Type u) G` for `G` a group, then `G × X` (with `G` acting as left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and trivially on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`. -/
@[simps! hom_hom inv_hom]
/-
**Action.leftRegularTensorIso** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：leftRegularTensorIso (X : Action (Type u) G) : leftRegular G otimes X ≅ le
ftRegular G otimes trivial G X.V
参数：X : Action (Type u) G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : Action (Type u) G` for `G` a group, then `G × X` (with `G` acting as 
left
multiplication on the first factor and by `X.ρ` on the second) is isomorphic as 
a `G`-set to
`G × X` (with `G` acting as left multiplication on the first factor and triviall
y on the second).
The isomorphism is given by `(g, x) ↦ (g, g⁻¹ • x)`.
-/
noncomputable def leftRegularTensorIso (X : Action (Type u) G) :
    leftRegular G ⊗ X ≅ leftRegular G ⊗ trivial G X.V :=
  mkIso (Equiv.toIso {
    toFun g := ⟨g.1, (X.ρ (g.1⁻¹ : G) g.2 : X.V)⟩
    invFun g := ⟨g.1, X.ρ g.1 g.2⟩
    left_inv _ := Prod.ext rfl <| by simp
    right_inv _ := Prod.ext rfl <| by simp }) <| fun _ => by
      ext _
      simp only [tensorObj_V, tensor_ρ]
      simp [types_tensorObj_def]
      rfl


/-- An isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplication on `Gⁿ⁺¹` and
`G` but trivially on `Gⁿ`. The map sends `(g₀, ..., gₙ) ↦ (g₀, (g₀⁻¹g₁, g₁⁻¹g₂, ..., gₙ₋₁⁻¹gₙ))`,
and the inverse is `(g₀, (g₁, ..., gₙ)) ↦ (g₀, g₀g₁, g₀g₁g₂, ..., g₀g₁...gₙ).` -/
/-
**Action.diagonalSuccIsoTensorTrivial** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：(G : Type u) →   [inst : Group G] →     (n : ℕ) →       Action.diagonal G 
(n + 1) ≅         CategoryTheory.MonoidalCategoryStruct.tensorObj (Action.leftRe
gular G) (Action.trivial G (Fin n → G))
参数：Fin n → G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of `G`-sets `Gⁿ⁺¹ ≅ G × Gⁿ`, where `G` acts by left multiplicatio
n on `Gⁿ⁺¹` and
`G` but trivially on `Gⁿ`. The map sends `(g₀, ..., gₙ) ↦ (g₀, (g₀⁻¹g₁, g₁⁻¹g₂, 
..., gₙ₋₁⁻¹gₙ))`,
and the inverse is `(g₀, (g₁, ..., gₙ)) ↦ (g₀, g₀g₁, g₀g₁g₂, ..., g₀g₁...gₙ).`
-/
noncomputable def diagonalSuccIsoTensorTrivial :
    ∀ n : ℕ, diagonal G (n + 1) ≅ leftRegular G ⊗ trivial G (Fin n → G)
  | 0 =>
    diagonalOneIsoLeftRegular G ≪≫
      (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorUnitIso (Equiv.ofUnique PUnit _).toIso)
  | n + 1 =>
    diagonalSuccIsoTensorDiagonal _ _ ≪≫
      tensorIso (Iso.refl _) (diagonalSuccIsoTensorTrivial n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Fin.insertNthEquiv (fun _ => G) 0).toIso fun _ => rfl)

variable {G}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Action.diagonalSuccIsoTensorTrivial_hom_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `A
ction`。
形式化陈述：diagonalSuccIsoTensorTrivial_hom_hom_apply {n : Nat} (f : Fin (n + 1) -> G
) : dsimp% (diagonalSuccIsoTensorTrivial G n).hom.hom f = (f 0, fun i => (f (Fin
.castSucc i))⁻¹ * f i.succ)
参数：f : Fin (n + 1) -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Fin.insertNthEquiv_zero`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_3), Fin.ins
ertNthEquiv α 0 = Fin.consEquiv α
· 使用定理 `Action.mkIso.congr_simp`：∀ {V : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (f f_1 :
 M.V ≅ N.V) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.MonoidalCategory.tensorIso_hom`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] {X 
Y X' Y' : C}   (f : X ≅ Y) (g : X' …
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `Action.diagonalSuccIsoTensorDiagonal_hom_hom`：∀ (G : Type u) [inst : Mon
oid G] (n : ℕ),   (Action.diagonalSuccIsoTensorDiagonal G n).hom.hom = (Fin.cons
Equiv fun a => G).symm.toIso.hom
· 使用定理 `Action.whiskerLeft_hom`：∀ {V : Type u_1} [inst : CategoryTheory.Category
.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory.Mon
oidalCategor…
· 使用定理 `Action.leftRegularTensorIso_hom_hom`：∀ (G : Type u) [inst : Group G] (X 
: Action (Type u) G),   (Action.leftRegularTensorIso G X).hom.hom =     { toFun 
:= fun g => (g.1, (Catego…
· 使用定理 `Action.mkIso_hom_hom`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{
v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (f : M.V ≅ 
N.V)   (co…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Equiv.toIso_hom_hom_apply`：∀ {X Y : Type u} (e : X ≃ Y) (x : X), (Catego
ryTheory.ConcreteCategory.hom e.toIso.hom) x = e x
-/
theorem diagonalSuccIsoTensorTrivial_hom_hom_apply {n : ℕ} (f : Fin (n + 1) → G) :
    dsimp% (diagonalSuccIsoTensorTrivial G n).hom.hom f =
      (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) := by
  induction n with
  | zero => exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  | succ n hn =>
    refine Prod.ext rfl (funext fun x => ?_)
    induction x using Fin.cases
    <;> simp_all [diagonalSuccIsoTensorTrivial, types_tensorObj_def]
    <;> rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Action.diagonalSuccIsoTensorTrivial_inv_hom_apply** 是 Mathlib 中的一个定理，位于命名空间 `A
ction`。
形式化陈述：diagonalSuccIsoTensorTrivial_inv_hom_apply {n : Nat} (g : G) (f : Fin n ->
 G) : dsimp% (diagonalSuccIsoTensorTrivial G n).inv.hom (g, f) = (g • Fin.partia
lProd f : Fin (n + 1) -> G)
参数：g : G；f : Fin n -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.id_tensorHom`：id_tensorHom (X : C) {Y₁ Y
₂ : C} (f : Y₁ ⟶ Y₂) : 𝟙 X otimesₘ f = X ◁ f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Action.rightUnitor_hom_hom`：∀ {V : Type u_1} [inst : CategoryTheory.Cate
gory.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G]   [inst_2 : CategoryTheory
.MonoidalCategor…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `Fin.partialProd_zero`：partialProd_zero (f : Fin n -> M) : partialProd f 
0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fin.insertNthEquiv_zero`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_3), Fin.ins
ertNthEquiv α 0 = Fin.consEquiv α
· 使用定理 `Action.mkIso.congr_simp`：∀ {V : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (f f_1 :
 M.V ≅ N.V) (…
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `Fin.partialProd_succ'`：partialProd_succ' (f : Fin (n + 1) -> M) (j : Fin
 (n + 1)) : partialProd f j.succ = f 0 * partialProd (Fin.tail f) j
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem diagonalSuccIsoTensorTrivial_inv_hom_apply {n : ℕ} (g : G) (f : Fin n → G) :
    dsimp% (diagonalSuccIsoTensorTrivial G n).inv.hom (g, f) =
      (g • Fin.partialProd f : Fin (n + 1) → G) := by
  induction n generalizing g with
  | zero =>
    funext (x : Fin 1)
    simp [diagonalSuccIsoTensorTrivial, diagonalOneIsoLeftRegular, Subsingleton.elim x 0,
      ofMulAction_V, types_tensorObj_def, types_tensorUnit_def]
  | succ n hn =>
    funext x
    induction x using Fin.cases with
    | zero => simp; rfl
    | succ i =>
      simpa [diagonalSuccIsoTensorTrivial, types_tensorObj_def, mul_assoc, Fin.partialProd_succ',
        ofMulAction_V] using! congrFun (hn (g * f 0) (Fin.tail f)) i

end

end Action

namespace CategoryTheory.Functor

open Action

variable {W : Type*} [Category* W] [MonoidalCategory V] [MonoidalCategory W]
  (F : V ⥤ W)

open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A lax monoidal functor induces a lax monoidal functor between
the categories of `G`-actions within those categories. -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lax monoidal functor induces a lax monoidal functor between
the categories of `G`-actions within those categories.
-/
instance [F.LaxMonoidal] : (F.mapAction G).LaxMonoidal where
  ε :=
    { hom := ε F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [Category.id_comp, F.map_id, Category.comp_id] }
  μ X Y :=
    { hom := μ F X.V Y.V
      comm := fun g => μ_natural F (X.ρ g) (Y.ρ g) }
  μ_natural_left _ _ := by ext; simp
  μ_natural_right _ _ := by ext; simp
  associativity _ _ _ := by ext; simp
  left_unitality _ := by ext; simp
  right_unitality _ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Functor.mapAction_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAction_ε_hom [F.LaxMonoidal] : (ε (F.mapAction G)).hom = ε F := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Functor.mapAction_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAction_μ_hom [F.LaxMonoidal] (X Y : Action V G) :
    (μ (F.mapAction G) X Y).hom = μ F X.V Y.V := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An oplax monoidal functor induces an oplax monoidal functor between
the categories of `G`-actions within those categories. -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oplax monoidal functor induces an oplax monoidal functor between
the categories of `G`-actions within those categories.
-/
instance [F.OplaxMonoidal] : (F.mapAction G).OplaxMonoidal where
  η :=
    { hom := η F
      comm := fun g => by
        dsimp [FunctorCategoryEquivalence.inverse, Functor.mapAction]
        rw [map_id, Category.id_comp, Category.comp_id] }
  δ X Y :=
    { hom := δ F X.V Y.V
      comm := fun g => (δ_natural F (X.ρ g) (Y.ρ g)).symm }
  δ_natural_left _ _ := by ext; simp
  δ_natural_right _ _ := by ext; simp
  oplax_associativity _ _ _ := by ext; simp
  oplax_left_unitality _ := by ext; simp
  oplax_right_unitality _ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Functor.mapAction_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAction_η_hom [F.OplaxMonoidal] : (η (F.mapAction G)).hom = η F := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Functor.mapAction_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Fu
nctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapAction_δ_hom [F.OplaxMonoidal] (X Y : Action V G) :
    (δ (F.mapAction G) X Y).hom = δ F X.V Y.V := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories. -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal functor induces a monoidal functor between
the categories of `G`-actions within those categories.
-/
instance [F.Monoidal] : (F.mapAction G).Monoidal where
  η_ε := by ext; dsimp; rw [η_ε]
  ε_η := by ext; dsimp; rw [ε_η]
  μ_δ _ _ := by ext; dsimp; rw [μ_δ]
  δ_μ _ _ := by ext; dsimp; rw [δ_μ]

end CategoryTheory.Functor

