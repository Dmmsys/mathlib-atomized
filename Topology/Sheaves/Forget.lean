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
/--
theorem `isSheaf_iff_isSheaf_comp'` / 定理 `isSheaf_iff_isSheaf_comp'`

English:
theorem isSheaf_iff_isSheaf_comp'
  statement: {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  proof: Presheaf.isSheaf_iff_isSheaf_comp _ F G

中文:
定理 isSheaf_iff_isSheaf_comp'
  结论: {C : 类型u₁} [Category.{v₁} C] {D : 类型u₂} [Category.{v₂} D]
  证明: Presheaf.isSheaf_iff_isSheaf_comp _ F G

Depends on / 依赖: Presheaf, Presheaf.isSheaf_iff_isSheaf_comp, isSheaf_iff_isSheaf_comp
-/
theorem isSheaf_iff_isSheaf_comp' {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) [G.ReflectsIsomorphisms] [HasLimitsOfSize.{v, v} C] [PreservesLimitsOfSize.{v, v} G]
    {X : TopCat.{v}} (F : Presheaf C X) : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G) :=
  Presheaf.isSheaf_iff_isSheaf_comp _ F G

/--
theorem `isSheaf_iff_isSheaf_comp` / 定理 `isSheaf_iff_isSheaf_comp`

English:
theorem isSheaf_iff_isSheaf_comp
  statement: {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  proof: isSheaf_iff_isSheaf_comp' G F

中文:
定理 isSheaf_iff_isSheaf_comp
  结论: {C : 类型u₁} [Category.{v} C] {D : 类型u₂} [Category.{v} D]
  证明: isSheaf_iff_isSheaf_comp' G F

Depends on / 依赖: isSheaf_iff_isSheaf_comp
-/
theorem isSheaf_iff_isSheaf_comp {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
    (G : C ⥤ D) [G.ReflectsIsomorphisms] [HasLimits C] [PreservesLimits G]
    {X : TopCat.{v}} (F : Presheaf C X) : Presheaf.IsSheaf F ↔ Presheaf.IsSheaf (F ⋙ G) :=
  isSheaf_iff_isSheaf_comp' G F

end TopCat.Presheaf
