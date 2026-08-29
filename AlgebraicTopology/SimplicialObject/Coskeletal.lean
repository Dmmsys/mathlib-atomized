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
variable (X : SimplicialObject C) (n : Nat)

namespace Truncated

/-- The identity natural transformation exhibits a simplicial set as a right extension of its
restriction along `(Truncated.inclusion n).op`. -/
@[simps!]
/--
Definition of `rightExtensionInclusion` / `rightExtensionInclusion` 的定义

English:
definition rightExtensionInclusion
  signature: :
  body: RightExtension.mk _ (𝟙 _)

中文:
定义 rightExtensionInclusion
  签名: :
  定义体: RightExtension.mk _ (𝟙 _)

Depends on / 依赖: RightExtension, RightExtension.mk
-/
def rightExtensionInclusion :
    RightExtension (Truncated.inclusion n).op
      ((Truncated.inclusion n).op ⋙ X) := RightExtension.mk _ (𝟙 _)

end Truncated

open Truncated

/-- A simplicial object `X` is `n`-coskeletal when it is the right Kan extension of its restriction
along `(Truncated.inclusion n).op` via the identity natural transformation. -/
@[mk_iff]
/--
Definition of `IsCoskeletal` / `IsCoskeletal` 的定义

English:
class IsCoskeletal
  parameters: : Prop where
  axioms and operations (1):
    - isRightKanExtension : IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X))

中文:
类 IsCoskeletal
  参数: : 命题 where
  公理与运算 (1 个):
    - isRightKanExtension : IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X))
-/
class IsCoskeletal : Prop where
  isRightKanExtension : IsRightKanExtension X (𝟙 ((Truncated.inclusion n).op ⋙ X))

attribute [instance] IsCoskeletal.isRightKanExtension

section

variable [forall (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C),
    (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/--
Definition of `IsCoskeletal.isUniversalOfIsRightKanExtension` / `IsCoskeletal.isUniversalOfIsRightKanExtension` 的定义

English:
definition IsCoskeletal.isUniversalOfIsRightKanExtension
  signature: [X.IsCoskeletal n]
  body: by
  apply Functor.isUniversalOfIsRightKanExtension

中文:
定义 IsCoskeletal.isUniversalOfIsRightKanExtension
  签名: [X.IsCoskeletal n]
  定义体: by
  apply Functor.isUniversalOfIsRightKanExtension

Depends on / 依赖: Functor, Functor.isUniversalOfIsRightKanExtension, isUniversalOfIsRightKanExtension
-/
noncomputable def IsCoskeletal.isUniversalOfIsRightKanExtension [X.IsCoskeletal n] :
    (rightExtensionInclusion X n).IsUniversal := by
  apply Functor.isUniversalOfIsRightKanExtension

/--
theorem `isCoskeletal_iff_isIso` / 定理 `isCoskeletal_iff_isIso`

English:
theorem isCoskeletal_iff_isIso
  statement: X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X)
  proof: by
  rw [isCoskeletal_iff]
  exact isRightKanExtension_iff_isIso ((coskAdj n).unit.app X)
    ((coskAdj n).counit.app _) (𝟙 _) ((coskAdj n).left_triangle_components X)

中文:
定理 isCoskeletal_iff_isIso
  结论: X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X)
  证明: by
  rw [isCoskeletal_iff]
  exact isRightKanExtension_iff_isIso ((coskAdj n).unit.app X)
    ((coskAdj n).counit.app _) (𝟙 _) ((coskAdj n).left_triangle_components X)

Depends on / 依赖: coskAdj, counit, counit.app, isCoskeletal_iff, isRightKanExtension_iff_isIso, left_triangle_components, unit.app
-/
theorem isCoskeletal_iff_isIso : X.IsCoskeletal n ↔ IsIso ((coskAdj n).unit.app X) := by
  rw [isCoskeletal_iff]
  exact isRightKanExtension_iff_isIso ((coskAdj n).unit.app X)
    ((coskAdj n).counit.app _) (𝟙 _) ((coskAdj n).left_triangle_components X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.IsCoskeletal
  signature: n] : IsIso ((coskAdj n).unit.app X)
  body: by
  rw [← isCoskeletal_iff_isIso]
  infer_instance

中文:
实例 [X.IsCoskeletal
  签名: n] : IsIso ((coskAdj n).unit.app X)
  定义体: by
  rw [← isCoskeletal_iff_isIso]
  infer_instance

Depends on / 依赖: infer_instance, isCoskeletal_iff_isIso
-/
instance [X.IsCoskeletal n] : IsIso ((coskAdj n).unit.app X) := by
  rw [← isCoskeletal_iff_isIso]
  infer_instance

/-- The canonical isomorphism `X ≅ (cosk n).obj X` defined when `X` is coskeletal and the
`n`-coskeleton functor exists. -/
@[simps! hom]
/--
Definition of `isoCoskOfIsCoskeletal` / `isoCoskOfIsCoskeletal` 的定义

English:
definition isoCoskOfIsCoskeletal
  signature: [X.IsCoskeletal n]
  body: asIso ((coskAdj n).unit.app X)

中文:
定义 isoCoskOfIsCoskeletal
  签名: [X.IsCoskeletal n]
  定义体: asIso ((coskAdj n).unit.app X)

Depends on / 依赖: coskAdj, unit.app
-/
noncomputable def isoCoskOfIsCoskeletal [X.IsCoskeletal n] : X ≅ (cosk n).obj X :=
  asIso ((coskAdj n).unit.app X)

end

end SimplicialObject

end CategoryTheory
