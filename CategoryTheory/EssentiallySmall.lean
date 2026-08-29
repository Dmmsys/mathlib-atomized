/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.UnivLE
public import Mathlib.Logic.Small.Basic

/-!
# Essentially small categories.

A category given by `(C : Type u) [Category.{v} C]` is `w`-essentially small
if there exists a `SmallModel C : Type w` equipped with `[SmallCategory (SmallModel C)]` and an
equivalence `C ≌ SmallModel C`.

A category is `w`-locally small if every hom type is `w`-small.

The main theorem here is that a category is `w`-essentially small iff
the type `Skeleton C` is `w`-small, and `C` is `w`-locally small.
-/

@[expose] public section


universe w w' v v' u u'

open CategoryTheory

variable (C : Type u) [Category.{v} C]

namespace CategoryTheory

/-- A category is `EssentiallySmall.{w}` if there exists
an equivalence to some `S : Type w` with `[SmallCategory S]`. -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the smallness universe `w` in
-- `EssentiallySmall` and `LocallySmall` would default to a universe output parameter.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ]
/--
Definition of `EssentiallySmall` / `EssentiallySmall` 的定义

English:
class EssentiallySmall
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - equiv_smallCategory : exists (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)

中文:
类 EssentiallySmall
  参数: (C : 类型u) [范畴.{v} C]
  公理与运算 (1 个):
    - equiv_smallCategory : 存在 (S : 类型 w) (_ : 小范畴 S), 非空 (C ≌ S)
-/
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- An essentially small category is equivalent to some small category. -/
  equiv_smallCategory : exists (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)

/--
theorem `EssentiallySmall.mk'` / 定理 `EssentiallySmall.mk'`

English:
theorem EssentiallySmall.mk'
  statement: {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
  proof: ⟨⟨S, _, ⟨e⟩⟩⟩

中文:
定理 EssentiallySmall.mk'
  结论: {C : 类型u} [范畴.{v} C] {S : 类型 w} [小范畴 S]
  证明: ⟨⟨S, _, ⟨e⟩⟩⟩
-/
theorem EssentiallySmall.mk' {C : Type u} [Category.{v} C] {S : Type w} [SmallCategory S]
    (e : C ≌ S) : EssentiallySmall.{w} C :=
  ⟨⟨S, _, ⟨e⟩⟩⟩

/-- An arbitrarily chosen small model for an essentially small category.
-/
@[pp_with_univ]
/--
Definition of `SmallModel` / `SmallModel` 的定义

English:
definition SmallModel
  signature: (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C]
  body: Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)

中文:
定义 SmallModel
  签名: (C : 类型u) [范畴.{v} C] [EssentiallySmall.{w} C]
  定义体: Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)

Depends on / 依赖: Classical, Classical.choose, EssentiallySmall, EssentiallySmall.equiv_smallCategory, equiv_smallCategory
-/
def SmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : Type w :=
  Classical.choose (@EssentiallySmall.equiv_smallCategory C _ _)

/--
Instance `smallCategorySmallModel` / 实例 `smallCategorySmallModel`

English:
instance smallCategorySmallModel
  signature: (C : Type u) [Category.{v} C]
  body: Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))

中文:
实例 smallCategorySmallModel
  签名: (C : 类型u) [范畴.{v} C]
  定义体: Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, EssentiallySmall, EssentiallySmall.equiv_smallCategory, choose_spec, equiv_smallCategory
-/
noncomputable instance smallCategorySmallModel (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : SmallCategory (SmallModel C) :=
  Classical.choose (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _))

/--
Definition of `equivSmallModel` / `equivSmallModel` 的定义

English:
definition equivSmallModel
  signature: (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C]
  body: Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))

中文:
定义 equivSmallModel
  签名: (C : 类型u) [范畴.{v} C] [EssentiallySmall.{w} C]
  定义体: Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))

Depends on / 依赖: Classical, Classical.choose_spec, EssentiallySmall, EssentiallySmall.equiv_smallCategory, Nonempty, Nonempty.some, choose_spec, equiv_smallCategory
-/
noncomputable def equivSmallModel (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] :
    C ≌ SmallModel C :=
  Nonempty.some
    (Classical.choose_spec (Classical.choose_spec (@EssentiallySmall.equiv_smallCategory C _ _)))

instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] : EssentiallySmall.{w} Cᵒᵖ :=
  EssentiallySmall.mk' (equivSmallModel C).op

/--
theorem `essentiallySmall_congr` / 定理 `essentiallySmall_congr`

English:
theorem essentiallySmall_congr
  statement: {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  proof: by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)

中文:
定理 essentiallySmall_congr
  结论: {C : 类型u} [范畴.{v} C] {D : 类型u'} [范畴.{v'} D]
  证明: by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)

Depends on / 依赖: EssentiallySmall, EssentiallySmall.mk, e.symm.trans, e.trans, fconstructor
-/
theorem essentiallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : EssentiallySmall.{w} C ↔ EssentiallySmall.{w} D := by
  fconstructor
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.symm.trans f)
  · rintro ⟨S, 𝒮, ⟨f⟩⟩
    exact EssentiallySmall.mk' (e.trans f)

/--
theorem `Discrete.essentiallySmallOfSmall` / 定理 `Discrete.essentiallySmallOfSmall`

English:
theorem Discrete.essentiallySmallOfSmall
  given: {α : Type u} [Small.{w} α]
  proof: ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩

中文:
定理 离散.essentiallySmallOfSmall
  条件: {α : 类型u} [Small.{w} α]
  证明: ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩

Depends on / 依赖: Discrete, Discrete.equivalence, Shrink, equivShrink, equivalence
-/
theorem Discrete.essentiallySmallOfSmall {α : Type u} [Small.{w} α] :
    EssentiallySmall.{w} (Discrete α) :=
  ⟨⟨Discrete (Shrink α), ⟨inferInstance, ⟨Discrete.equivalence (equivShrink _)⟩⟩⟩⟩

/--
theorem `essentiallySmallSelf` / 定理 `essentiallySmallSelf`

English:
theorem essentiallySmallSelf
  statement: EssentiallySmall.{max w v u} C
  proof: EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)

中文:
定理 essentiallySmallSelf
  结论: EssentiallySmall.{最大值 w v u} C
  证明: EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)

Depends on / 依赖: AsSmall, AsSmall.equiv, EssentiallySmall, EssentiallySmall.mk
-/
theorem essentiallySmallSelf : EssentiallySmall.{max w v u} C :=
  EssentiallySmall.mk' (AsSmall.equiv : C ≌ AsSmall.{w} C)

/-- A category is `w`-locally small if every hom set is `w`-small.

See `ShrinkHoms C` for a category instance where every hom set has been replaced by a small model.
-/
-- See comment on `EssentiallySmall` above.
@[univ_out_params, pp_with_univ]
/--
Definition of `LocallySmall` / `LocallySmall` 的定义

English:
class LocallySmall
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (1):
    - hom_small : forall X Y : C, Small.{w} (X ⟶ Y)  [default: by infer_instance]

中文:
类 LocallySmall
  参数: (C : 类型u) [范畴.{v} C]
  公理与运算 (1 个):
    - hom_small : 对任意 X Y : C, Small.{w} (X ⟶ Y)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  /-- A locally small category has small hom-types. -/
  hom_small : forall X Y : C, Small.{w} (X ⟶ Y) := by infer_instance

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (X Y : C) : Small.{w, v} (X ⟶ Y) :=
  LocallySmall.hom_small X Y

instance (C : Type u) [Category.{v} C] [LocallySmall.{w} C] : LocallySmall.{w} Cᵒᵖ where
  hom_small X Y := small_of_injective (opEquiv X Y).injective

/--
theorem `locallySmall_of_faithful` / 定理 `locallySmall_of_faithful`

English:
theorem locallySmall_of_faithful
  statement: {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  proof: small_of_injective F.map_injective

中文:
定理 locallySmall_of_faithful
  结论: {C : 类型u} [范畴.{v} C] {D : 类型u'} [范畴.{v'} D]
  证明: small_of_injective F.map_injective

Depends on / 依赖: F.map_injective, map_injective, small_of_injective
-/
theorem locallySmall_of_faithful {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] : LocallySmall.{w} C where
  hom_small {_ _} := small_of_injective F.map_injective

/--
theorem `locallySmall_congr` / 定理 `locallySmall_congr`

English:
theorem locallySmall_congr
  statement: {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  proof: ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩

中文:
定理 locallySmall_congr
  结论: {C : 类型u} [范畴.{v} C] {D : 类型u'} [范畴.{v'} D]
  证明: ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩

Depends on / 依赖: e.functor, e.inverse, functor, inverse, locallySmall_of_faithful
-/
theorem locallySmall_congr {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (e : C ≌ D) : LocallySmall.{w} C ↔ LocallySmall.{w} D :=
  ⟨fun _ => locallySmall_of_faithful e.inverse, fun _ => locallySmall_of_faithful e.functor⟩

instance (C : Type u) [Category.{v} C] [EssentiallySmall.{w} C] [LocallySmall.{w'} C] :
    LocallySmall.{w'} (SmallModel.{w} C) :=
  (locallySmall_congr (equivSmallModel.{w} C)).1 inferInstance

instance (priority := 100) locallySmall_self (C : Type u) [Category.{v} C] :
    LocallySmall.{v} C where

instance (priority := 100) locallySmall_of_univLE (C : Type u) [Category.{v} C] [UnivLE.{v, w}] :
    LocallySmall.{w} C where

/--
theorem `locallySmall_max` / 定理 `locallySmall_max`

English:
theorem locallySmall_max
  given: {C : Type u} [Category.{v} C]
  statement: LocallySmall.{max v w} C where
  proof: small_max.{w} _

中文:
定理 locallySmall_max
  条件: {C : 类型u} [范畴.{v} C]
  结论: LocallySmall.{最大值 v w} C where
  证明: small_max.{w} _

Depends on / 依赖: small_max
-/
theorem locallySmall_max {C : Type u} [Category.{v} C] : LocallySmall.{max v w} C where
  hom_small _ _ := small_max.{w} _

instance (priority := 100) locallySmall_of_essentiallySmall (C : Type u) [Category.{v} C]
    [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  (locallySmall_congr (equivSmallModel C)).mpr (CategoryTheory.locallySmall_self _)

/-- We define a type alias `ShrinkHoms C` for `C`. When we have `LocallySmall.{w} C`,
we'll put a `Category.{w}` instance on `ShrinkHoms C`.
-/
@[pp_with_univ]
/--
Definition of `ShrinkHoms` / `ShrinkHoms` 的定义

English:
definition ShrinkHoms
  signature: (C : Type u)
  body: C

中文:
定义 ShrinkHoms
  签名: (C : 类型u)
  定义体: C
-/
def ShrinkHoms (C : Type u) :=
  C

namespace ShrinkHoms

section

variable {C' : Type*}

-- a fresh variable with no category instance attached
/--
Definition of `toShrinkHoms` / `toShrinkHoms` 的定义

English:
definition toShrinkHoms
  signature: {C' : Type*} (X : C')
  body: X

中文:
定义 toShrinkHoms
  签名: {C' : 类型} (X : C')
  定义体: X
-/
def toShrinkHoms {C' : Type*} (X : C') : ShrinkHoms C' :=
  X

/--
Definition of `fromShrinkHoms` / `fromShrinkHoms` 的定义

English:
definition fromShrinkHoms
  signature: {C' : Type*} (X : ShrinkHoms C')
  body: X

@[simp]

中文:
定义 fromShrinkHoms
  签名: {C' : 类型} (X : ShrinkHoms C')
  定义体: X

@[simp]
-/
def fromShrinkHoms {C' : Type*} (X : ShrinkHoms C') : C' :=
  X

@[simp]
/--
theorem `to_from` / 定理 `to_from`

English:
theorem to_from
  given: (X : C')
  statement: fromShrinkHoms (toShrinkHoms X) = X
  proof: rfl

@[simp]

中文:
定理 to_from
  条件: (X : C')
  结论: fromShrinkHoms (toShrinkHoms X) = X
  证明: rfl

@[simp]
-/
theorem to_from (X : C') : fromShrinkHoms (toShrinkHoms X) = X :=
  rfl

@[simp]
/--
theorem `from_to` / 定理 `from_to`

English:
theorem from_to
  given: (X : ShrinkHoms C')
  statement: toShrinkHoms (fromShrinkHoms X) = X
  proof: rfl

中文:
定理 from_to
  条件: (X : ShrinkHoms C')
  结论: toShrinkHoms (fromShrinkHoms X) = X
  证明: rfl
-/
theorem from_to (X : ShrinkHoms C') : toShrinkHoms (fromShrinkHoms X) = X :=
  rfl

end

variable [LocallySmall.{w} C]

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category.{w} (ShrinkHoms C)
  body: Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

中文:
实例 :
  签名: 范畴.{w} (ShrinkHoms C)
  定义体: Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

Depends on / 依赖: Shrink, fromShrinkHoms
-/
noncomputable instance : Category.{w} (ShrinkHoms C) where
  Hom X Y := Shrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)
  id X := equivShrink _ (𝟙 (fromShrinkHoms X))
  comp f g := equivShrink _ ((equivShrink _).symm f ≫ (equivShrink _).symm g)

set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : C ⥤ ShrinkHoms C where
  body: toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f

中文:
定义 functor
  签名: : C ⥤ ShrinkHoms C where
  定义体: toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f

Depends on / 依赖: toShrinkHoms
-/
noncomputable def functor : C ⥤ ShrinkHoms C where
  obj X := toShrinkHoms X
  map {X Y} f := equivShrink (X ⟶ Y) f

/-- Implementation of `ShrinkHoms.equivalence`. -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : ShrinkHoms C ⥤ C where
  body: fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f

中文:
定义 inverse
  签名: : ShrinkHoms C ⥤ C where
  定义体: fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f

Depends on / 依赖: fromShrinkHoms
-/
noncomputable def inverse : ShrinkHoms C ⥤ C where
  obj X := fromShrinkHoms X
  map {X Y} f := (equivShrink (fromShrinkHoms X ⟶ fromShrinkHoms Y)).symm f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The categorical equivalence between `C` and `ShrinkHoms C`, when `C` is locally small.
-/
@[simps]
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : C ≌ ShrinkHoms C where
  body: functor C
  inverse := inverse C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 equivalence
  签名: : C ≌ ShrinkHoms C where
  定义体: functor C
  inverse := inverse C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: functor
-/
noncomputable def equivalence : C ≌ ShrinkHoms C where
  functor := functor C
  inverse := inverse C
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor C).IsEquivalence
  body: (equivalence C).isEquivalence_functor

中文:
实例 :
  签名: (functor C).是等价
  定义体: (equivalence C).isEquivalence_functor

Depends on / 依赖: equivalence, isEquivalence_functor
-/
instance : (functor C).IsEquivalence := (equivalence C).isEquivalence_functor
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inverse C).IsEquivalence
  body: (equivalence C).isEquivalence_inverse

中文:
实例 :
  签名: (inverse C).是等价
  定义体: (equivalence C).isEquivalence_inverse

Depends on / 依赖: equivalence, isEquivalence_inverse
-/
instance : (inverse C).IsEquivalence := (equivalence C).isEquivalence_inverse

instance {T : Type u} [Unique T] : Unique (ShrinkHoms.{u} T) where
  default := ShrinkHoms.toShrinkHoms (default : T)
  uniq _ := congr_arg ShrinkHoms.fromShrinkHoms (Unique.uniq _ _)

instance {T : Type u} [Category.{v} T] [IsDiscrete T] : IsDiscrete (ShrinkHoms.{u} T) where
  subsingleton _ _ := { allEq _ _ := Shrink.ext (Subsingleton.elim _ _) }
  eq_of_hom f := IsDiscrete.eq_of_hom (C := T) ((equivShrink _).symm f)

end ShrinkHoms

namespace Shrink

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: C] : Category.{v} (Shrink.{w} C)
  body: inferInstanceAs (Category (InducedCategory _ (equivShrink C).symm))

中文:
实例 [Small.{w}
  签名: C] : 范畴.{v} (Shrink.{w} C)
  定义体: inferInstanceAs (Category (InducedCategory _ (equivShrink C).symm))

Depends on / 依赖: Category, InducedCategory, equivShrink
-/
noncomputable instance [Small.{w} C] : Category.{v} (Shrink.{w} C) :=
  inferInstanceAs (Category (InducedCategory _ (equivShrink C).symm))

/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: [Small.{w} C]
  body: (Equivalence.induced _).symm

中文:
定义 equivalence
  签名: [Small.{w} C]
  定义体: (Equivalence.induced _).symm

Depends on / 依赖: Equivalence, Equivalence.induced, induced
-/
noncomputable def equivalence [Small.{w} C] : C ≌ Shrink.{w} C :=
  (Equivalence.induced _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w'}
  signature: C] [LocallySmall.{w} C] :
  body: locallySmall_of_faithful.{w} (equivalence.{w'} C).inverse

中文:
实例 [Small.{w'}
  签名: C] [LocallySmall.{w} C] :
  定义体: locallySmall_of_faithful.{w} (equivalence.{w'} C).inverse

Depends on / 依赖: equivalence, inverse, locallySmall_of_faithful
-/
instance [Small.{w'} C] [LocallySmall.{w} C] :
    LocallySmall.{w} (Shrink.{w'} C) :=
  locallySmall_of_faithful.{w} (equivalence.{w'} C).inverse

end Shrink

/--
theorem `essentiallySmall_iff` / 定理 `essentiallySmall_iff`

English:
theorem essentiallySmall_iff
  given: (C : Type u) [Category.{v} C]
  proof: by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      refine ⟨⟨Skeleton S, ⟨?_⟩⟩⟩
      exact e.skeletonEquiv
    · infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    let e' := (ShrinkHoms.equivalence C).skeletonEqu

中文:
定理 essentiallySmall_iff
  条件: (C : 类型u) [范畴.{v} C]
  证明: by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      refine ⟨⟨Skeleton S, ⟨?_⟩⟩⟩
      exact e.skeletonEquiv
    · infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    let e' := (ShrinkHoms.equivalence C).skeletonEqu
-/
theorem essentiallySmall_iff (C : Type u) [Category.{v} C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) ∧ LocallySmall.{w} C := by
  -- This theorem is the only bit of real work in this file.
  fconstructor
  · intro h
    fconstructor
    · rcases h with ⟨S, 𝒮, ⟨e⟩⟩
      refine ⟨⟨Skeleton S, ⟨?_⟩⟩⟩
      exact e.skeletonEquiv
    · infer_instance
  · rintro ⟨⟨S, ⟨e⟩⟩, L⟩
    let e' := (ShrinkHoms.equivalence C).skeletonEquiv.symm
    exact ⟨⟨InducedCategory _ (e'.trans e).symm, inferInstance,
      ⟨(ShrinkHoms.equivalence C).trans
      ((skeletonEquivalence (ShrinkHoms C)).symm.trans
      (inducedFunctor _).asEquivalence.symm)⟩⟩⟩

/--
Instance `essentiallySmall_of_small_of_locallySmall` / 实例 `essentiallySmall_of_small_of_locallySmall`

English:
instance essentiallySmall_of_small_of_locallySmall
  signature: [Small.{w} C] [LocallySmall.{w} C]
  body: (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩

example (C : Type w) [SmallCategory C] : EssentiallySmall.{w} C := inferInstance

中文:
实例 essentiallySmall_of_small_of_locallySmall
  签名: [Small.{w} C] [LocallySmall.{w} C]
  定义体: (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩

example (C : Type w) [SmallCategory C] : EssentiallySmall.{w} C := inferInstance

Depends on / 依赖: Quotient, Quotient.exists_rep, essentiallySmall_iff, exists_rep, infer_instance, small_of_surjective
-/
instance essentiallySmall_of_small_of_locallySmall [Small.{w} C] [LocallySmall.{w} C] :
    EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_surjective Quotient.exists_rep, by infer_instance⟩

example (C : Type w) [SmallCategory C] : EssentiallySmall.{w} C := inferInstance

/--
Instance `small_skeleton_of_essentiallySmall` / 实例 `small_skeleton_of_essentiallySmall`

English:
instance small_skeleton_of_essentiallySmall
  signature: [h : EssentiallySmall.{w} C]
  body: .1 .1 h essentiallySmall_iff C

中文:
实例 small_skeleton_of_essentiallySmall
  签名: [h : EssentiallySmall.{w} C]
  定义体: .1 .1 h essentiallySmall_iff C

Depends on / 依赖: essentiallySmall_iff
-/
instance small_skeleton_of_essentiallySmall [h : EssentiallySmall.{w} C] : Small.{w} (Skeleton C) :=
.1 .1 h essentiallySmall_iff C

variable {C} in
/--
theorem `essentiallySmall_of_fully_faithful` / 定理 `essentiallySmall_of_fully_faithful`

English:
theorem essentiallySmall_of_fully_faithful
  statement: {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
  proof: (essentiallySmall_iff C).2 ⟨small_of_injective F.mapSkeleton_injective,
    locallySmall_of_faithful F⟩

中文:
定理 essentiallySmall_of_fully_faithful
  结论: {D : 类型u'} [范畴.{v'} D] (F : C ⥤ D)
  证明: (essentiallySmall_iff C).2 ⟨small_of_injective F.mapSkeleton_injective,
    locallySmall_of_faithful F⟩

Depends on / 依赖: F.mapSkeleton_injective, essentiallySmall_iff, locallySmall_of_faithful, mapSkeleton_injective, small_of_injective
-/
theorem essentiallySmall_of_fully_faithful {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
    [F.Full] [F.Faithful] [EssentiallySmall.{w} D] : EssentiallySmall.{w} C :=
  (essentiallySmall_iff C).2 ⟨small_of_injective F.mapSkeleton_injective,
    locallySmall_of_faithful F⟩

section FullSubcategory

/--
Instance `locallySmall_fullSubcategory` / 实例 `locallySmall_fullSubcategory`

English:
instance locallySmall_fullSubcategory
  signature: [LocallySmall.{w} C] (P : ObjectProperty C)
  body: locallySmall_of_faithful P.ι

中文:
实例 locallySmall_fullSubcategory
  签名: [LocallySmall.{w} C] (P : ObjectProperty C)
  定义体: locallySmall_of_faithful P.ι

Depends on / 依赖: locallySmall_of_faithful
-/
instance locallySmall_fullSubcategory [LocallySmall.{w} C] (P : ObjectProperty C) :
    LocallySmall.{w} P.FullSubcategory :=
locallySmall_of_faithful P.ι

/--
Instance `essentiallySmall_fullSubcategory_mem` / 实例 `essentiallySmall_fullSubcategory_mem`

English:
instance essentiallySmall_fullSubcategory_mem
  signature: (s : Set C) [Small.{w} s] [LocallySmall.{w} C]
  body: suffices Small.{w} (ObjectProperty.FullSubcategory (· in s)) from
    essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by cat_disch)

中文:
实例 essentiallySmall_fullSubcategory_mem
  签名: (s : 集合 C) [Small.{w} s] [LocallySmall.{w} C]
  定义体: suffices Small.{w} (ObjectProperty.FullSubcategory (· in s)) from
    essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by cat_disch)

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory, cat_disch, essentiallySmall_of_small_of_locallySmall, small_of_injective
-/
instance essentiallySmall_fullSubcategory_mem (s : Set C) [Small.{w} s] [LocallySmall.{w} C] :
    EssentiallySmall.{w} (ObjectProperty.FullSubcategory (· in s)) :=
  suffices Small.{w} (ObjectProperty.FullSubcategory (· in s)) from
    essentiallySmall_of_small_of_locallySmall _
  small_of_injective (f := fun x => (⟨x.1, x.2⟩ : s)) (by cat_disch)

end FullSubcategory

/-- Any thin category is locally small.
-/
instance (priority := 100) locallySmall_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    LocallySmall.{w} C where

/--
theorem `essentiallySmall_iff_of_thin` / 定理 `essentiallySmall_iff_of_thin`

English:
theorem essentiallySmall_iff_of_thin
  given: {C : Type u} [Category.{v} C] [Quiver.IsThin C]
  proof: by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]

中文:
定理 essentiallySmall_iff_of_thin
  条件: {C : 类型u} [范畴.{v} C] [箭图.IsThin C]
  证明: by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]

Depends on / 依赖: CategoryTheory, CategoryTheory.locallySmall_of_thin, essentiallySmall_iff, locallySmall_of_thin
-/
theorem essentiallySmall_iff_of_thin {C : Type u} [Category.{v} C] [Quiver.IsThin C] :
    EssentiallySmall.{w} C ↔ Small.{w} (Skeleton C) := by
  simp [essentiallySmall_iff, CategoryTheory.locallySmall_of_thin]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: C] : Small.{w} (Discrete C)
  body: small_map discreteEquiv

中文:
实例 [Small.{w}
  签名: C] : Small.{w} (离散 C)
  定义体: small_map discreteEquiv

Depends on / 依赖: discreteEquiv, small_map
-/
instance [Small.{w} C] : Small.{w} (Discrete C) := small_map discreteEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: C] [LocallySmall.{w} C] :
  body: by
  let φ (f : Arrow C) : Σ (s t : C), s ⟶ t := ⟨_, _, f.hom⟩
  refine small_of_injective (f := φ) ?_
  rintro ⟨s, t, f⟩ ⟨s', t', f'⟩ h
  obtain rfl : s = s' := congr_arg Sigma.fst h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, φ] at h
  obtain rfl : t = t' := h.1
  obtain rfl : f = f' := by s

中文:
实例 [Small.{w}
  签名: C] [LocallySmall.{w} C] :
  定义体: by
  let φ (f : Arrow C) : Σ (s t : C), s ⟶ t := ⟨_, _, f.hom⟩
  refine small_of_injective (f := φ) ?_
  rintro ⟨s, t, f⟩ ⟨s', t', f'⟩ h
  obtain rfl : s = s' := congr_arg Sigma.fst h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, φ] at h
  obtain rfl : t = t' := h.1
  obtain rfl : f = f' := by s

Depends on / 依赖: Sigma.fst, Sigma.mk.injEq, congr_arg, f.hom, heq_eq_eq, small_of_injective, true_and
-/
instance [Small.{w} C] [LocallySmall.{w} C] :
    Small.{w} (Arrow C) := by
  let φ (f : Arrow C) : Σ (s t : C), s ⟶ t := ⟨_, _, f.hom⟩
  refine small_of_injective (f := φ) ?_
  rintro ⟨s, t, f⟩ ⟨s', t', f'⟩ h
  obtain rfl : s = s' := congr_arg Sigma.fst h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and, φ] at h
  obtain rfl : t = t' := h.1
  obtain rfl : f = f' := by simpa using h
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{w}
  signature: C] [LocallySmall.{w} C]
  body: by
  refine small_of_injective (f := fun F (f : Arrow C) => Arrow.mk (F.map f.hom))
    (fun F G h => Functor.ext (fun X => ?_) (fun X Y f => ?_))
  · exact congr_arg Comma.left (congr_fun h (Arrow.mk (𝟙 X)))
  · have : Arrow.mk (F.map f) = Arrow.mk (G.map f) := congr_fun h (Arrow.mk f)
    rw [Arro

中文:
实例 [Small.{w}
  签名: C] [LocallySmall.{w} C]
  定义体: by
  refine small_of_injective (f := fun F (f : Arrow C) => Arrow.mk (F.map f.hom))
    (fun F G h => Functor.ext (fun X => ?_) (fun X Y f => ?_))
  · exact congr_arg Comma.left (congr_fun h (Arrow.mk (𝟙 X)))
  · have : Arrow.mk (F.map f) = Arrow.mk (G.map f) := congr_fun h (Arrow.mk f)
    rw [Arro

Depends on / 依赖: Arrow.mk, Arrow.mk_eq_mk_iff, Comma.left, F.map, Functor, Functor.ext, G.map, congr_arg, congr_fun, f.hom, mk_eq_mk_iff, small_of_injective
-/
instance [Small.{w} C] [LocallySmall.{w} C]
    {D : Type u'} [Category.{v'} D] [Small.{w} D] [LocallySmall.{w} D] :
    Small.{w} (C ⥤ D) := by
  refine small_of_injective (f := fun F (f : Arrow C) => Arrow.mk (F.map f.hom))
    (fun F G h => Functor.ext (fun X => ?_) (fun X Y f => ?_))
  · exact congr_arg Comma.left (congr_fun h (Arrow.mk (𝟙 X)))
  · have : Arrow.mk (F.map f) = Arrow.mk (G.map f) := congr_fun h (Arrow.mk f)
    rw [Arrow.mk_eq_mk_iff] at this
    tauto

instance {A : Type u'} [Category.{v'} A] [LocallySmall.{w} A] (C : Type w) [SmallCategory C] :
    LocallySmall.{w} (C ⥤ A) where
  hom_small P Q :=
    small_of_injective (f := NatTrans.app) (fun f g h => by aesop)

end CategoryTheory
