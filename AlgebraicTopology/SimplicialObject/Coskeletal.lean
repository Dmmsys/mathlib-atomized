/-
Copyright (c) 2024 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic

/-!
# Coskeletal simplicial objects

The identity natural transformation exhibits a simplicial object `X` as a right extension of its
restriction along `(Truncated.inclusion n).op` recorded by `rightExtensionInclusion X n`.

The simplicial object `X` is *n-coskeletal* if `rightExtensionInclusion X n` is a right Kan
extension.

When the ambient category admits right Kan extensions along `(Truncated.inclusion n).op`,
then when `X` is `n`-coskeletal, the unit of `coskAdj n` defines an isomorphism:
`isoCoskOfIsCoskeletal : X ≅ (cosk n).obj X`.

TODO: Prove that `X` is `n`-coskeletal whenever a certain canonical cone is a limit cone.
-/

@[expose] public section

open Opposite

open CategoryTheory

open CategoryTheory.Limits CategoryTheory.Functor SimplexCategory

universe v u v' u'

namespace CategoryTheory

namespace SimplicialObject
variable {C : Type u} [Category.{v} C]
variable (X : SimplicialObject C) (n : ℕ)

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion n).op`. -/
@[simps!]
/-
**CategoryTheory.SimplicialObject.Truncated.rightExtensionInclusion** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.SimplicialObject.Truncated`。
形式化陈述：rightExtensionInclusion : RightExtension (Truncated.inclusion n).op ((Trun
cated.inclusion n).op ⋙ X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity natural transformation exhibits a simplicial set as a right extensi
on of its
restriction along `(Truncated.inclusion n).op`.
-/
def rightExtensionInclusion :
    RightExtension (Truncated.inclusion n).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

open Truncated

/-- A simplicial object `X` is `n`-coskeletal when it is the right Kan extension of its restriction
along `(Truncated.inclusion n).op` via the identity natural transformation. -/
@[mk_iff]
/-
**CategoryTheory.SimplicialObject.IsCoskeletal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.SimplicialObject`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
SimplicialObject C → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplicial object `X` is `n`-coskeletal when it is the right Kan extension of 
its restriction
along `(Truncated.inclusion n).op` via the identity natural transformation.
-/
class IsCoskeletal : Prop where
  isRightKanExtension : IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X))

attribute [instance] IsCoskeletal.isRightKanExtension

section

variable [∀ (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/-- If `X` is `n`-coskeletal, then `Truncated.rightExtensionInclusion X n` is a terminal object in
the category `RightExtension (Truncated.inclusion n).op (Truncated.inclusion.op ⋙ X)`. -/
/-
**CategoryTheory.SimplicialObject.IsCoskeletal.isUniversalOfIsRightKanExtension*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SimplicialObject.IsCoskeletal`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (X : Cate
goryTheory.SimplicialObject C) →       (n : ℕ) →         [X.IsCoskeletal n] →   
        CategoryTheory.CostructuredArrow.IsUniversal             (CategoryTheory
.SimplicialObject.Truncated.rightExtensionInclusion X n)
参数：X : CategoryTheory.SimplicialObject C；n : ℕ；CategoryTheory.SimplicialObject.T
runcated.rightExtensionInclusion X n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.IsCoskeletal.isRightKanExtension`：∀ {C :
 Type u} {inst : CategoryTheory.Category.{v, u} C} {X : CategoryTheory.Simplicia
lObject C} {n : ℕ}   [self : X.IsCoskeletal n],   Cate…

--- 原说明 ---
If `X` is `n`-coskeletal, then `Truncated.rightExtensionInclusion X n` is a term
inal object in
the category `RightExtension (Truncated.inclusion n).op (Truncated.inclusion.op 
⋙ X)`.
-/
noncomputable def IsCoskeletal.isUniversalOfIsRightKanExtension [X.IsCoskeletal n] :
    (rightExtensionInclusion X n).IsUniversal := by
  apply Functor.isUniversalOfIsRightKanExtension
/-
**CategoryTheory.SimplicialObject.isCoskeletal_iff_isIso** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.SimplicialObject`。
形式化陈述：isCoskeletal_iff_isIso : X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SimplicialObject.isCoskeletal_iff`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] (X : CategoryTheory.SimplicialObject C) (n : 
ℕ),   X.IsCoskeletal n ↔     CategoryT…
· 使用引理 `CategoryTheory.Functor.isRightKanExtension_iff_isIso`：isRightKanExtensio
n_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F') {L : C ⥤ D} {F : C ⥤ H} (α
 : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : …
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.SimplicialObject.instIsRightKanExtensionOppositeTruncated
SimplexCategoryObjCoskAppTruncatedCounitCoskAdjTruncation`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (X : CategoryTheory.SimplicialObject C) (n :
 ℕ)   [inst_1 :     ∀ (F : CategoryTheo…
-/
theorem isCoskeletal_iff_isIso : X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X) := by
  rw [isCoskeletal_iff]
  exact isRightKanExtension_iff_isIso ((coskAdj n).unit.app X)
    ((coskAdj n).counit.app _) (𝟙 _) ((coskAdj n).left_triangle_components X)
/-
**CategoryTheory.SimplicialObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sim
plicialObject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.IsCoskeletal n] : IsIso ((coskAdj n).unit.app X) := by
  rw [← isCoskeletal_iff_isIso]
  infer_instance

/-- The canonical isomorphism `X ≅ (cosk n).obj X` defined when `X` is coskeletal and the
`n`-coskeleton functor exists. -/
@[simps! hom]
/-
**CategoryTheory.SimplicialObject.isoCoskOfIsCoskeletal** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.SimplicialObject`。
形式化陈述：isoCoskOfIsCoskeletal [X.IsCoskeletal n] : X ≅ (cosk n).obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SimplicialObject.instIsIsoAppUnitTruncatedCoskAdj`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] (X : CategoryTheory.Simplicia
lObject C) (n : ℕ)   [inst_1 :     ∀ (F : CategoryTheo…

--- 原说明 ---
The canonical isomorphism `X ≅ (cosk n).obj X` defined when `X` is coskeletal an
d the
`n`-coskeleton functor exists.
-/
noncomputable def isoCoskOfIsCoskeletal [X.IsCoskeletal n] : X ≅ (cosk n).obj X :=
  asIso ((coskAdj n).unit.app X)

end

end SimplicialObject

end CategoryTheory

