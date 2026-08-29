/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Well-powered categories

A category `(C : Type u) [Category.{v} C]` is `[WellPowered.{w} C]`
if `C` is locally small relative to `w` and for every `X : C`,
we have `Small.{w} (Subobject X)`. The most common case is when `w = v`,
in which case, it only involves the condition `Small.{v} (Subobject X)`

(Note that in this situation `Subobject X : Type (max u v)`,
so this is a nontrivial condition for large categories,
but automatic for small categories.)

This is equivalent to the category `MonoOver X` being `EssentiallySmall.{w}` for all `X : C`.

When a category is well-powered, you can obtain nonconstructive witnesses as
`Shrink (Subobject X) : Type w`
and
`equivShrink (Subobject X) : Subobject X ≃ Shrink (Subobject X)`.
-/

public section


universe w v v₂ u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v} C]

/--
A category (with morphisms in `Type v`) is well-powered relative to a universe `w`
if it is locally small and `Subobject X` is `w`-small for every `X`.

We show in `wellPowered_of_essentiallySmall_monoOver` and `essentiallySmall_monoOver`
that this is the case if and only if `MonoOver X` is `w`-essentially small for every `X`.
-/
@[pp_with_univ]
/--
Definition of `WellPowered` / `WellPowered` 的定义

English:
class WellPowered
  parameters: [LocallySmall.{w} C]
  axioms and operations (1):
    - subobject_small : forall X : C, Small.{w} (Subobject X)  [default: by infer_instance]

中文:
类 WellPowered
  参数: [LocallySmall.{w} C]
  公理与运算 (1 个):
    - subobject_small : 对任意 X : C, Small.{w} (Subobject X)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class WellPowered [LocallySmall.{w} C] : Prop where
  subobject_small : forall X : C, Small.{w} (Subobject X) := by infer_instance

/--
Instance `small_subobject` / 实例 `small_subobject`

English:
instance small_subobject
  signature: [LocallySmall.{w} C] [WellPowered C] (X : C)
  body: WellPowered.subobject_small X

中文:
实例 small_subobject
  签名: [LocallySmall.{w} C] [WellPowered C] (X : C)
  定义体: WellPowered.subobject_small X

Depends on / 依赖: WellPowered, WellPowered.subobject_small, subobject_small
-/
instance small_subobject [LocallySmall.{w} C] [WellPowered C] (X : C) :
    Small.{w} (Subobject X) :=
  WellPowered.subobject_small X

instance (priority := 100) wellPowered_of_smallCategory (C : Type u₁) [SmallCategory C] :
    WellPowered.{u₁} C where

variable {C}

/--
theorem `essentiallySmall_monoOver_iff_small_subobject` / 定理 `essentiallySmall_monoOver_iff_small_subobject`

English:
theorem essentiallySmall_monoOver_iff_small_subobject
  given: (X : C)
  proof: essentiallySmall_iff_of_thin

中文:
定理 essentiallySmall_monoOver_iff_small_subobject
  条件: (X : C)
  证明: essentiallySmall_iff_of_thin

Depends on / 依赖: essentiallySmall_iff_of_thin
-/
theorem essentiallySmall_monoOver_iff_small_subobject (X : C) :
    EssentiallySmall.{w} (MonoOver X) ↔ Small.{w} (Subobject X) :=
  essentiallySmall_iff_of_thin

/--
theorem `wellPowered_of_essentiallySmall_monoOver` / 定理 `wellPowered_of_essentiallySmall_monoOver`

English:
theorem wellPowered_of_essentiallySmall_monoOver
  statement: [LocallySmall.{w} C]
  proof: { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }

中文:
定理 wellPowered_of_essentiallySmall_monoOver
  结论: [LocallySmall.{w} C]
  证明: { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }

Depends on / 依赖: essentiallySmall_monoOver_iff_small_subobject, subobject_small
-/
theorem wellPowered_of_essentiallySmall_monoOver [LocallySmall.{w} C]
    (h : forall X : C, EssentiallySmall.{w} (MonoOver X)) :
    WellPowered.{w} C :=
  { subobject_small := fun X => (essentiallySmall_monoOver_iff_small_subobject X).mp (h X) }

section

variable [LocallySmall.{w} C] [WellPowered.{w} C]

/--
Instance `essentiallySmall_monoOver` / 实例 `essentiallySmall_monoOver`

English:
instance essentiallySmall_monoOver
  signature: (X : C)
  body: (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)

中文:
实例 essentiallySmall_monoOver
  签名: (X : C)
  定义体: (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)

Depends on / 依赖: WellPowered, WellPowered.subobject_small, essentiallySmall_monoOver_iff_small_subobject, subobject_small
-/
instance essentiallySmall_monoOver (X : C) : EssentiallySmall.{w} (MonoOver X) :=
  (essentiallySmall_monoOver_iff_small_subobject X).mpr (WellPowered.subobject_small X)

end

section Equivalence

variable {D : Type u₂} [Category.{v₂} D]

/--
theorem `wellPowered_of_equiv` / 定理 `wellPowered_of_equiv`

English:
theorem wellPowered_of_equiv
  statement: (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
  proof: wellPowered_of_essentiallySmall_monoOver fun X =>
(essentiallySmall_congr (MonoOver.congr X e.symm)).2 by infer_instance

中文:
定理 wellPowered_of_equiv
  结论: (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
  证明: wellPowered_of_essentiallySmall_monoOver fun X =>
(essentiallySmall_congr (MonoOver.congr X e.symm)).2 by infer_instance

Depends on / 依赖: MonoOver, MonoOver.congr, e.symm, essentiallySmall_congr, infer_instance, wellPowered_of_essentiallySmall_monoOver
-/
theorem wellPowered_of_equiv (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
    [WellPowered.{w} C] : WellPowered.{w} D :=
  wellPowered_of_essentiallySmall_monoOver fun X =>
(essentiallySmall_congr (MonoOver.congr X e.symm)).2 by infer_instance

/--
theorem `wellPowered_congr` / 定理 `wellPowered_congr`

English:
theorem wellPowered_congr
  given: (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
  proof: ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩

中文:
定理 wellPowered_congr
  条件: (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D]
  证明: ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩

Depends on / 依赖: e.symm, wellPowered_of_equiv
-/
theorem wellPowered_congr (e : C ≌ D) [LocallySmall.{w} C] [LocallySmall.{w} D] :
    WellPowered.{w} C ↔ WellPowered.{w} D :=
  ⟨fun _ => wellPowered_of_equiv e, fun _ => wellPowered_of_equiv e.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LocallySmall.{w}
  signature: C] [WellPowered.{w} C] :
  body: wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C)

中文:
实例 [LocallySmall.{w}
  签名: C] [WellPowered.{w} C] :
  定义体: wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C)

Depends on / 依赖: ShrinkHoms, ShrinkHoms.equivalence, equivalence, wellPowered_of_equiv
-/
instance [LocallySmall.{w} C] [WellPowered.{w} C] :
    WellPowered.{w, w} (ShrinkHoms C) :=
  wellPowered_of_equiv.{w} (ShrinkHoms.equivalence.{w} C)

end Equivalence

end CategoryTheory
