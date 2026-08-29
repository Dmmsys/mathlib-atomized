/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# The category of (commutative) (additive) monoids has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

@[expose] public section

assert_not_exists MonoidWithZero

noncomputable section

open CategoryTheory Limits

universe v u w

namespace MonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ MonCat.{u})

@[to_additive]
/--
Instance `monoidObj` / 实例 `monoidObj`

English:
instance monoidObj
  signature: (j : J)
  body: inferInstanceAs Monoid (F.obj j)

中文:
实例 monoidObj
  签名: (j : J)
  定义体: inferInstanceAs Monoid (F.obj j)

Depends on / 依赖: F.obj, Monoid
-/
instance monoidObj (j : J) : Monoid (F.obj j) :=
inferInstanceAs Monoid (F.obj j)

/-- The flat sections of a functor into `MonCat` form a submonoid of all sections. -/
@[to_additive
/-- The flat sections of a functor into `AddMonCat` form an additive submonoid of all sections. -/]
/--
Definition of `sectionsSubmonoid` / `sectionsSubmonoid` 的定义

English:
definition sectionsSubmonoid
  signature: : Submonoid (forall j, F.obj j) where
  body: (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by simp [← ah f, ← bh f]

@[to_additive]

中文:
定义 sectionsSubmonoid
  签名: : 子幺半群 (对任意 j, F.obj j) where
  定义体: (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by simp [← ah f, ← bh f]

@[to_additive]

Depends on / 依赖: MonCat, forget, sections
-/
def sectionsSubmonoid : Submonoid (forall j, F.obj j) where
  carrier := (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by simp [← ah f, ← bh f]

@[to_additive]
/--
Instance `sectionsMonoid` / 实例 `sectionsMonoid`

English:
instance sectionsMonoid
  signature: : Monoid (F ⋙ forget MonCat.{u}).sections
  body: (sectionsSubmonoid F).toMonoid

中文:
实例 sectionsMonoid
  签名: : 幺半群 (F ⋙ forget 幺半群范畴.{u}).sections
  定义体: (sectionsSubmonoid F).toMonoid

Depends on / 依赖: sectionsSubmonoid, toMonoid
-/
instance sectionsMonoid : Monoid (F ⋙ forget MonCat.{u}).sections :=
  (sectionsSubmonoid F).toMonoid

variable [Small.{u} (Functor.sections (F ⋙ forget MonCat))]

set_option backward.inferInstanceAs.wrap.data false in
@[to_additive]
/--
Instance `limitMonoid` / 实例 `limitMonoid`

English:
instance limitMonoid
  signature: :
  body: inferInstanceAs Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)

中文:
实例 limitMonoid
  签名: :
  定义体: inferInstanceAs Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)

Depends on / 依赖: MonCat, Monoid, Shrink, forget, sections
-/
noncomputable instance limitMonoid :
    Monoid (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt :=
inferInstanceAs Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limit.π (F ⋙ forget MonCat) j` as a `MonoidHom`. -/
@[to_additive /-- `limit.π (F ⋙ forget AddMonCat) j` as an `AddMonoidHom`. -/]
/--
Definition of `limitπMonoidHom` / `limitπMonoidHom` 的定义

English:
definition limitπMonoidHom
  signature: (j : J)
  body: (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).π.app j
  map_one' := by simp; rfl
  map_mul' _ _ := by simp; rfl

中文:
定义 limitπMonoidHom
  签名: (j : J)
  定义体: (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).π.app j
  map_one' := by simp; rfl
  map_mul' _ _ := by simp; rfl

Depends on / 依赖: MonCat, Types.Small.limitCone, forget, limitCone
-/
noncomputable def limitπMonoidHom (j : J) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt ->*
      F.obj j where
  toFun := (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).π.app j
  map_one' := by simp; rfl
  map_mul' _ _ := by simp; rfl

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits MonCat`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/-- Construction of a limit cone in `MonCat`.
(Internal use only; use the limits API.)
-/
@[to_additive /-- (Internal use only; use the limits API.) -/]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
    { app j := ofHom (limitπMonoidHom F j)
      naturality := fun _ _ f => MonCat.ext fun x =>
        ConcreteCategory.congr_hom ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) x } }

中文:
定义 limitCone
  签名: : 锥 F
  定义体: { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
    { app j := ofHom (limitπMonoidHom F j)
      naturality := fun _ _ f => MonCat.ext fun x =>
        ConcreteCategory.congr_hom ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) x } }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, MonCat, MonCat.ext, MonCat.of, Types.Small.limitCone, congr_hom, forget, limitCone, naturality
-/
noncomputable def limitCone : Cone F :=
  { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
    { app j := ofHom (limitπMonoidHom F j)
      naturality := fun _ _ f => MonCat.ext fun x =>
        ConcreteCategory.congr_hom ((Types.Small.limitCone (F ⋙ forget _)).π.naturality f) x } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Witness that the limit cone in `MonCat` is a limit cone.
(Internal use only; use the limits API.)
-/
@[to_additive /-- (Internal use only; use the limits API.) -/]
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone F)
  body: by
  refine IsLimit.ofFaithful (forget MonCat) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_ }) (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone F)
  定义体: by
  refine IsLimit.ofFaithful (forget MonCat) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_ }) (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl

Depends on / 依赖: IsLimit, IsLimit.ofFaithful, MonCat, Types.Small.limitConeIsLimit, equivShrink_mul, forget, limitConeIsLimit, map_mul, map_one, ofFaithful
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget MonCat) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_ }) (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl

/-- If `(F ⋙ forget MonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddMonCat).sections` is `u`-small, `F` has a limit. -/]
/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

Depends on / 依赖: CommRing, HasLimit, HasLimit.mk, R.obj, isLimit, limitCone, limitConeIsLimit
-/
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `MonCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddMonCat.{u}` has limits of shape `J`. -/]
/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]
  body: inferInstance

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
  定义体: inferInstance
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J MonCat.{u} where
  has_limit _ := inferInstance

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive /-- The category of additive monoids has all limits. -/]
/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

@[to_additive]

中文:
实例 hasLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }

@[to_additive]
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} MonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits MonCat.{u}
  body: MonCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 幺半群范畴.{u}
  定义体: MonCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: MonCat, MonCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits MonCat.{u} :=
  MonCat.hasLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `MonCat.{u}` preserves limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddMonCat.{u}` preserves limits
of shape `J`. -/]
/--
Instance `forget_preservesLimitsOfShape` / 实例 `forget_preservesLimitsOfShape`

English:
instance forget_preservesLimitsOfShape
  signature: [Small.{u} J]
  body: preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

中文:
实例 forget_preservesLimitsOfShape
  签名: [Small.{u} J]
  定义体: preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

Depends on / 依赖: limitConeIsLimit, preservesLimit_of_preserves_limit_cone
-/
noncomputable instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget MonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
/-- The forgetful functor from additive monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/]
/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

@[to_additive]

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }

@[to_additive]
-/
noncomputable instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  preservesLimitsOfShape := { }

@[to_additive]
/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget MonCat.{u})
  body: MonCat.forget_preservesLimitsOfSize.{u, u}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 幺半群范畴.{u})
  定义体: MonCat.forget_preservesLimitsOfSize.{u, u}

Depends on / 依赖: MonCat, MonCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
noncomputable instance forget_preservesLimits : PreservesLimits (forget MonCat.{u}) :=
  MonCat.forget_preservesLimitsOfSize.{u, u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
Instance `forget_createsLimit` / 实例 `forget_createsLimit`

English:
instance forget_createsLimit
  signature: :
  body: by
  apply createsLimitOfReflectsIso
  intro c t
  have : Small.{u} (Functor.sections (F ⋙ forget MonCat)) :=
    (Types.hasLimit_iff_small_sections _).mp (HasLimit.mk { cone := c, isLimit := t })
  refine LiftsToLimit.mk (LiftableCone.mk
    { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget MonC

中文:
实例 forget_createsLimit
  签名: :
  定义体: by
  apply createsLimitOfReflectsIso
  intro c t
  have : Small.{u} (Functor.sections (F ⋙ forget MonCat)) :=
    (Types.hasLimit_iff_small_sections _).mp (HasLimit.mk { cone := c, isLimit := t })
  refine LiftsToLimit.mk (LiftableCone.mk
    { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget MonC

Depends on / 依赖: Cone.ext, Functor, Functor.sections, HasLimit, HasLimit.mk, HasLimits, LiftableCone, LiftableCone.mk, LiftsToLimit, LiftsToLimit.mk, MonCat, MonCat.HasLimits.limitCone, MonCat.of, NatTrans, NatTrans.mk, Types.Small.limitCone, Types.hasLimit_iff_small_sections, Types.isLimitEquivSections, createsLimitOfReflectsIso, equivShrink
-/
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget MonCat.{u}) := by
  apply createsLimitOfReflectsIso
  intro c t
  have : Small.{u} (Functor.sections (F ⋙ forget MonCat)) :=
    (Types.hasLimit_iff_small_sections _).mp (HasLimit.mk { cone := c, isLimit := t })
  refine LiftsToLimit.mk (LiftableCone.mk
    { pt := MonCat.of (Types.Small.limitCone (F ⋙ forget MonCat)).pt,
      π := NatTrans.mk
        (fun j => ofHom (limitπMonoidHom F j))
        (MonCat.HasLimits.limitCone F).π.naturality }
    (Cone.ext
      ((Types.isLimitEquivSections t).trans (equivShrink _)).symm.toIso
      (fun _ => ?_))) ?_
  · ext
    simp [Types.isLimitEquivSections]
    simp [← CategoryTheory.comp_apply]
    rfl
  refine IsLimit.ofFaithful (forget MonCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _) ?_ ?_
  · intro _
    refine ofHom
      { toFun := (Types.Small.limitConeIsLimit.{v, u} _).lift ((forget MonCat).mapCone _),
        map_one' := by simp; rfl, map_mul' := ?_ }
    · intro x y
      simp only [Types.Small.limitCone_pt, Functor.comp_obj, Functor.mapCone_pt,
        Types.Small.limitConeIsLimit_lift, Functor.const_obj_obj, Functor.mapCone_π_app,
        ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk, map_mul]
      rw [← equivShrink_mul]
      rfl
  · exact fun _ => rfl

@[to_additive]
/--
Instance `forget_createsLimitsOfShape` / 实例 `forget_createsLimitsOfShape`

English:
instance forget_createsLimitsOfShape
  signature: :
  body: inferInstance

中文:
实例 forget_createsLimitsOfShape
  签名: :
  定义体: inferInstance
-/
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget MonCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from monoids to types preserves all limits. -/
@[to_additive /-- The forgetful functor from additive monoids to types preserves all limits. -/]
/--
Instance `forget_createsLimitsOfSize` / 实例 `forget_createsLimitsOfSize`

English:
instance forget_createsLimitsOfSize
  signature: :
  body: inferInstance

@[to_additive]

中文:
实例 forget_createsLimitsOfSize
  签名: :
  定义体: inferInstance

@[to_additive]
-/
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  CreatesLimitsOfShape := inferInstance

@[to_additive]
/--
Instance `forget_createsLimits` / 实例 `forget_createsLimits`

English:
instance forget_createsLimits
  signature: : CreatesLimits (forget MonCat.{u})
  body: MonCat.forget_createsLimitsOfSize.{u, u}

中文:
实例 forget_createsLimits
  签名: : CreatesLimits (forget 幺半群范畴.{u})
  定义体: MonCat.forget_createsLimitsOfSize.{u, u}

Depends on / 依赖: MonCat, MonCat.forget_createsLimitsOfSize, forget_createsLimitsOfSize
-/
noncomputable instance forget_createsLimits : CreatesLimits (forget MonCat.{u}) :=
  MonCat.forget_createsLimitsOfSize.{u, u}

end MonCat

open MonCat

namespace CommMonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommMonCat.{u})

@[to_additive]
/--
Instance `commMonoidObj` / 实例 `commMonoidObj`

English:
instance commMonoidObj
  signature: (j)
  body: inferInstanceAs CommMonoid (F.obj j)

中文:
实例 commMonoidObj
  签名: (j)
  定义体: inferInstanceAs CommMonoid (F.obj j)

Depends on / 依赖: CommMonoid, F.obj
-/
instance commMonoidObj (j) : CommMonoid ((F ⋙ forget CommMonCat.{u}).obj j) :=
inferInstanceAs CommMonoid (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommMonCat))]

@[to_additive]
/--
Instance `limitCommMonoid` / 实例 `limitCommMonoid`

English:
instance limitCommMonoid
  signature: :
  body: letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (forall j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
inferInstanceAs CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)

@[to_additive]

中文:
实例 limitCommMonoid
  签名: :
  定义体: letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (forall j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
inferInstanceAs CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)

@[to_additive]

Depends on / 依赖: CommMonCat, CommMonoid, F.obj, MonCat, MonCat.sectionsSubmonoid, Shrink, Submonoid, Submonoid.toCommMonoid, forget, sections, sectionsSubmonoid, toCommMonoid
-/
noncomputable instance limitCommMonoid :
    CommMonoid (Types.Small.limitCone (F ⋙ forget CommMonCat.{u})).pt :=
  letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (forall j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
inferInstanceAs CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{u} (Functor.sections ((F ⋙ forget₂ CommMonCat MonCat) ⋙ forget MonCat))
  body: inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

中文:
实例 :
  签名: Small.{u} (函子.sections ((F ⋙ forget₂ 交换幺半群范畴 幺半群范畴) ⋙ forget 幺半群范畴))
  定义体: inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

Depends on / 依赖: CommMonCat, Functor, Functor.sections, forget, sections
-/
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ CommMonCat MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

/-- We show that the forgetful functor `CommMonCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `CommMonoid` instance available,
and then reuse the existing limit. -/
@[to_additive /-- We show that the forgetful functor `AddCommMonCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddCommMonoid` instance available,
and then reuse the existing limit. -/]
/--
Instance `forget₂CreatesLimit` / 实例 `forget₂CreatesLimit`

English:
instance forget₂CreatesLimit
  signature: : CreatesLimit F (forget₂ CommMonCat MonCat.{u})
  body: createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app j := ofHom (MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}) j)
naturality _ _ j := ext fun x => ConcreteCategory.

中文:
实例 forget₂CreatesLimit
  签名: : 创造极限 F (forget₂ 交换幺半群范畴 幺半群范畴.{u})
  定义体: createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app j := ofHom (MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}) j)
naturality _ _ j := ext fun x => ConcreteCategory.

Depends on / 依赖: CommMonCat, CommMonCat.of, ConcreteCategory, ConcreteCategory.congr_hom, HasLimits, IsLimit, IsLimit.ofFaithful, IsLimit.uniqueUpToIso, MonCat, MonCat.HasLimits.limitCone, MonCat.HasLimits.limitConeIsLimit, MonCat.limit, Types.Small.limitCone, congr_hom, createsLimitOfReflectsIso, forget, liftedCone, limitCone, limitConeIsLimit, makesLimit
-/
noncomputable instance forget₂CreatesLimit : CreatesLimit F (forget₂ CommMonCat MonCat.{u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app j := ofHom (MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}) j)
naturality _ _ j := ext fun x => ConcreteCategory.congr_hom
                ((MonCat.HasLimits.limitCone
                  (F ⋙ forget₂ CommMonCat MonCat.{u})).π.naturality j) x } }
      validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ CommMonCat MonCat.{u})
          (MonCat.HasLimits.limitConeIsLimit _) (fun _ => _) fun _ => rfl }

/-- A choice of limit cone for a functor into `CommMonCat`.
(Generally, you'll just want to use `limit F`.)
-/
@[to_additive /-- A choice of limit cone for a functor into `AddCommMonCat`.
(Generally, you'll just want to use `limit F`.) -/]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))

中文:
定义 limitCone
  签名: : 锥 F
  定义体: liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))

Depends on / 依赖: CommMonCat, MonCat, isLimit, liftLimit, limit.isLimit
-/
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone F)
  body: liftedLimitIsLimit _

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone F)
  定义体: liftedLimitIsLimit _

Depends on / 依赖: liftedLimitIsLimit
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommMonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddCommMonCat).sections` is `u`-small, `F` has a limit. -/]
/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

Depends on / 依赖: HasLimit, HasLimit.mk, isLimit, limitCone, limitConeIsLimit
-/
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `CommMonCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddCommMonCat.{u}` has limits of shape `J`. -/]
/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]
  body: inferInstance

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
  定义体: inferInstance
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommMonCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative monoids has all limits. -/
@[to_additive /-- The category of additive commutative monoids has all limits. -/]
/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

@[to_additive]

中文:
实例 hasLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }

@[to_additive]
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommMonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits CommMonCat.{u}
  body: CommMonCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 交换幺半群范畴.{u}
  定义体: CommMonCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: CommMonCat, CommMonCat.hasLimitsOfSize, evaluationJointlyReflectsColimits, hasLimitsOfSize
-/
instance hasLimits : HasLimits CommMonCat.{u} :=
  CommMonCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from commutative monoids to monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of monoids. -/
@[to_additive AddCommMonCat.forget₂AddMonPreservesLimitsOfSize
/-- The forgetful functor from
additive commutative monoids to additive monoids preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of additive
monoids. -/]
/--
Instance `forget₂Mon_preservesLimitsOfSize` / 实例 `forget₂Mon_preservesLimitsOfSize`

English:
instance forget₂Mon_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

@[to_additive]

中文:
实例 forget₂Mon_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }

@[to_additive]

Depends on / 依赖: preservesColimits_of_natIso, tensorLeftIsoTensorRight
-/
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommMonCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J} 𝒥 := { }

@[to_additive]
/--
Instance `forget₂Mon_preservesLimits` / 实例 `forget₂Mon_preservesLimits`

English:
instance forget₂Mon_preservesLimits
  signature: :
  body: CommMonCat.forget₂Mon_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂Mon_preservesLimits
  签名: :
  定义体: CommMonCat.forget₂Mon_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommMonCat, CommMonCat.forget
-/
instance forget₂Mon_preservesLimits :
    PreservesLimits (forget₂ CommMonCat.{u} MonCat.{u}) :=
  CommMonCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `CommMonCat.{u}` preserves limits of
shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddCommMonCat.{u}`
preserves limits of shape `J`. -/]
/--
Instance `forget_preservesLimitsOfShape` / 实例 `forget_preservesLimitsOfShape`

English:
instance forget_preservesLimitsOfShape
  signature: [Small.{u} J]
  body: preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

中文:
实例 forget_preservesLimitsOfShape
  签名: [Small.{u} J]
  定义体: preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

Depends on / 依赖: limitConeIsLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget CommMonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative monoids to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive /-- The forgetful functor from additive commutative monoids to types preserves all
limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/]
/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget CommMonCat.{u}) where
  preservesLimitsOfShape {_} _ := { }

/--
Instance `_root_.AddCommMonCat.forget_preservesLimits` / 实例 `_root_.AddCommMonCat.forget_preservesLimits`

English:
instance _root_.AddCommMonCat.forget_preservesLimits
  signature: :
  body: AddCommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]

中文:
实例 _root_.加法交换幺半群范畴.forget_preservesLimits
  签名: :
  定义体: AddCommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]

Depends on / 依赖: AddCommMonCat, AddCommMonCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance _root_.AddCommMonCat.forget_preservesLimits :
    PreservesLimits (forget AddCommMonCat.{u}) :=
  AddCommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]
/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget CommMonCat.{u})
  body: CommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 交换幺半群范畴.{u})
  定义体: CommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]

Depends on / 依赖: CommMonCat, CommMonCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget CommMonCat.{u}) :=
  CommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
/--
Instance `forget_createsLimit` / 实例 `forget_createsLimit`

English:
instance forget_createsLimit
  signature: :
  body: by
  set e : forget CommMonCat.{u} ≅ forget₂ CommMonCat.{u} MonCat.{u} ⋙ forget MonCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact createsLimitOfNatIso e.symm

@[to_additive]

中文:
实例 forget_createsLimit
  签名: :
  定义体: by
  set e : forget CommMonCat.{u} ≅ forget₂ CommMonCat.{u} MonCat.{u} ⋙ forget MonCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact createsLimitOfNatIso e.symm

@[to_additive]

Depends on / 依赖: CommMonCat, Iso.refl, MonCat, NatIso, NatIso.ofComponents, createsLimitOfNatIso, e.symm, forget, ofComponents
-/
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget CommMonCat.{u}) := by
  set e : forget CommMonCat.{u} ≅ forget₂ CommMonCat.{u} MonCat.{u} ⋙ forget MonCat.{u} :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  exact createsLimitOfNatIso e.symm

@[to_additive]
/--
Instance `forget_createsLimitsOfShape` / 实例 `forget_createsLimitsOfShape`

English:
instance forget_createsLimitsOfShape
  signature: :
  body: inferInstance

中文:
实例 forget_createsLimitsOfShape
  签名: :
  定义体: inferInstance
-/
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget MonCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from commutative monoids to types preserves all limits. -/
@[to_additive
/-- The forgetful functor from commutative additive monoids to types preserves all limits. -/]
/--
Instance `forget_createsLimitsOfSize` / 实例 `forget_createsLimitsOfSize`

English:
instance forget_createsLimitsOfSize
  signature: :
  body: inferInstance

@[to_additive]

中文:
实例 forget_createsLimitsOfSize
  签名: :
  定义体: inferInstance

@[to_additive]
-/
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  CreatesLimitsOfShape := inferInstance

@[to_additive]
/--
Instance `forget_createsLimits` / 实例 `forget_createsLimits`

English:
instance forget_createsLimits
  signature: : CreatesLimits (forget MonCat.{u})
  body: CommMonCat.forget_createsLimitsOfSize.{u, u}

中文:
实例 forget_createsLimits
  签名: : CreatesLimits (forget 幺半群范畴.{u})
  定义体: CommMonCat.forget_createsLimitsOfSize.{u, u}

Depends on / 依赖: CommMonCat, CommMonCat.forget_createsLimitsOfSize, forget_createsLimitsOfSize
-/
noncomputable instance forget_createsLimits : CreatesLimits (forget MonCat.{u}) :=
  CommMonCat.forget_createsLimitsOfSize.{u, u}

end CommMonCat
