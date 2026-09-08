/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Sheaves.Sheaf

/-!
# Checking the sheaf condition on the underlying presheaf of types.

If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in `C`),
then checking the sheaf condition for a presheaf `F : Presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices
to check it on the underlying sheaf of types.

## References
* https://stacks.math.columbia.edu/tag/0073
-/

public section

universe v v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits

namespace TopCat.Presheaf

/-- If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in `C`),
then checking the sheaf condition for a presheaf `F : Presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices to check it on the underlying sheaf of types.

Another useful example is the forgetful functor `TopCommRingCat ⥤ TopCat`. -/
@[stacks 0073 "In fact we prove a stronger version with arbitrary target category."]
/-
**TopCat.Presheaf.isSheaf_iff_isSheaf_comp'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pr
esheaf`。
形式化陈述：isSheaf_iff_isSheaf_comp' {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [C
ategory.{v₂} D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [HasLimitsOfSize.{v, v} C] 
[PreservesLimitsOfSize.{v, v} G] {X : TopCat.{v}} (F : Presheaf C X) : Presheaf.
IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G)
参数：G : C ⥤ D；F : Presheaf C X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp`：isSheaf_iff_isSheaf_co
mp (s : A ⥤ B) [HasLimitsOfSize.{v₁, max v₁ u₁} A] [PreservesLimitsOfSize.{v₁, m
ax v₁ u₁} s] [s.ReflectsIsomorphisms] …

--- 原说明 ---
If `G : C ⥤ D` is a functor which reflects isomorphisms and preserves limits
(we assume all limits exist in `C`),
then checking the sheaf condition for a presheaf `F : Presheaf C X`
is equivalent to checking the sheaf condition for `F ⋙ G`.

The important special case is when
`C` is a concrete category with a forgetful functor
that preserves limits and reflects isomorphisms.
Then to check the sheaf condition it suffices to check it on the underlying shea
f of types.

Another useful example is the forgetful functor `TopCommRingCat ⥤ TopCat`.
-/
theorem isSheaf_iff_isSheaf_comp' {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) [G.ReflectsIsomorphisms] [HasLimitsOfSize.{v, v} C] [PreservesLimitsOfSize.{v, v} G]
    {X : TopCat.{v}} (F : Presheaf C X) : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G) :=
  Presheaf.isSheaf_iff_isSheaf_comp _ F G
/-
**TopCat.Presheaf.isSheaf_iff_isSheaf_comp** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Pre
sheaf`。
形式化陈述：isSheaf_iff_isSheaf_comp {C : Type u₁} [Category.{v} C] {D : Type u₂} [Cat
egory.{v} D] (G : C ⥤ D) [G.ReflectsIsomorphisms] [HasLimits C] [PreservesLimits
 G] {X : TopCat.{v}} (F : Presheaf C X) : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf 
(F ⋙ G)
参数：G : C ⥤ D；F : Presheaf C X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.isSheaf_iff_isSheaf_comp'`：isSheaf_iff_isSheaf_comp' {C 
: Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D) [G.Refl
ectsIsomorphisms] [HasLimitsOfS…
-/
theorem isSheaf_iff_isSheaf_comp {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (G : C ⥤ D) [G.ReflectsIsomorphisms] [HasLimits C] [PreservesLimits G]
    {X : TopCat.{v}} (F : Presheaf C X) : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G) :=
  isSheaf_iff_isSheaf_comp' G F

end TopCat.Presheaf

