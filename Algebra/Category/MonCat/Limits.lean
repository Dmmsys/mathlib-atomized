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
/-
**MonCat.monoidObj** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：monoidObj (j : J) : Monoid (F.obj j)
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidObj (j : J) : Monoid (F.obj j) :=
  inferInstanceAs <| Monoid (F.obj j)

/-- The flat sections of a functor into `MonCat` form a submonoid of all sections. -/
@[to_additive
/-- The flat sections of a functor into `AddMonCat` form an additive submonoid of all sections. -/]
/-
**MonCat.sectionsSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：sectionsSubmonoid : Submonoid (forall j, F.obj j) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sectionsSubmonoid : Submonoid (∀ j, F.obj j) where
  carrier := (F ⋙ forget MonCat).sections
  one_mem' {j} {j'} f := by simp
  mul_mem' {a} {b} ah bh {j} {j'} f := by simp [← ah f, ← bh f]

@[to_additive]
/-
**MonCat.sectionsMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：sectionsMonoid : Monoid (F ⋙ forget MonCat.{u}).sections
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sectionsMonoid : Monoid (F ⋙ forget MonCat.{u}).sections :=
  (sectionsSubmonoid F).toMonoid

variable [Small.{u} (Functor.sections (F ⋙ forget MonCat))]

set_option backward.inferInstanceAs.wrap.data false in
@[to_additive]
/-
**MonCat.limitMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：limitMonoid : Monoid (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})
).pt
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
noncomputable instance limitMonoid :
    Monoid (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt :=
  inferInstanceAs <| Monoid (Shrink (F ⋙ forget MonCat.{u}).sections)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limit.π (F ⋙ forget MonCat) j` as a `MonoidHom`. -/
@[to_additive /-- `limit.π (F ⋙ forget AddMonCat) j` as an `AddMonoidHom`. -/]
/-
**MonCat.limit** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limit.π (F ⋙ forget MonCat) j` as a `MonoidHom`.
-/
noncomputable def limitπMonoidHom (j : J) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget MonCat.{u})).pt →*
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
/-
**MonCat.HasLimits.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.HasLimits`。
形式化陈述：limitCone : Cone F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of a limit cone in `MonCat`.
(Internal use only; use the limits API.)
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
/-
**MonCat.HasLimits.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `MonCat.HasLimits`
。
形式化陈述：limitConeIsLimit : IsLimit (limitCone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Witness that the limit cone in `MonCat` is a limit cone.
(Internal use only; use the limits API.)
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
/-
**MonCat.HasLimits.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `MonCat.HasLimits`。
形式化陈述：hasLimit : HasLimit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If `(F ⋙ forget MonCat).sections` is `u`-small, `F` has a limit.
-/
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `MonCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddMonCat.{u}` has limits of shape `J`. -/]
/-
**MonCat.HasLimits.hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `MonCat.HasLimits`
。
形式化陈述：hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J MonCat.{u} where has_l
imit _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
If `J` is `u`-small, `MonCat.{u}` has limits of shape `J`.
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J MonCat.{u} where
  has_limit _ := inferInstance

end HasLimits

open HasLimits

/-- The category of monoids has all limits. -/
@[to_additive /-- The category of additive monoids has all limits. -/]
/-
**MonCat.hasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} MonCat.{u} where 
has_limits_of_shape _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The category of monoids has all limits.
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} MonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
/-
**MonCat.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：hasLimits : HasLimits MonCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasLimits : HasLimits MonCat.{u} :=
  MonCat.hasLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `MonCat.{u}` preserves limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddMonCat.{u}` preserves limits
of shape `J`. -/]
/-
**MonCat.forget_preservesLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_preservesLimitsOfShape [Small.{u} J] : PreservesLimitsOfShape J (fo
rget MonCat.{u}) where preservesLimit {F}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
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
/-
**MonCat.forget_preservesLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_preservesLimitsOfSize [UnivLE.{v, u}] : PreservesLimitsOfSize.{w, v
} (forget MonCat.{u}) where preservesLimitsOfShape
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  preservesLimitsOfShape := { }

@[to_additive]
/-
**MonCat.forget_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_preservesLimits : PreservesLimits (forget MonCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_preservesLimits : PreservesLimits (forget MonCat.{u}) :=
  MonCat.forget_preservesLimitsOfSize.{u, u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**MonCat.forget_createsLimit** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_createsLimit : CreatesLimit F (forget MonCat.{u})
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
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
      (fun _ ↦ ?_))) ?_
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
  · exact fun _ ↦ rfl

@[to_additive]
/-
**MonCat.forget_createsLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_createsLimitsOfShape : CreatesLimitsOfShape J (forget MonCat.{u}) w
here CreatesLimit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget MonCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from monoids to types preserves all limits. -/
@[to_additive /-- The forgetful functor from additive monoids to types preserves all limits. -/]
/-
**MonCat.forget_createsLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_createsLimitsOfSize : CreatesLimitsOfSize.{w, v} (forget MonCat.{u}
) where CreatesLimitsOfShape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from monoids to types preserves all limits.
-/
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  CreatesLimitsOfShape := inferInstance

@[to_additive]
/-
**MonCat.forget_createsLimits** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：forget_createsLimits : CreatesLimits (forget MonCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_createsLimits : CreatesLimits (forget MonCat.{u}) :=
  MonCat.forget_createsLimitsOfSize.{u, u}

end MonCat

open MonCat

namespace CommMonCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommMonCat.{u})

@[to_additive]
/-
**CommMonCat.commMonoidObj** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：commMonoidObj (j) : CommMonoid ((F ⋙ forget CommMonCat.{u}).obj j)
参数：j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoidObj (j) : CommMonoid ((F ⋙ forget CommMonCat.{u}).obj j) :=
  inferInstanceAs <| CommMonoid (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommMonCat))]

@[to_additive]
/-
**CommMonCat.limitCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：limitCommMonoid : CommMonoid (Types.Small.limitCone (F ⋙ forget CommMonCat
.{u})).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance limitCommMonoid :
    CommMonoid (Types.Small.limitCone (F ⋙ forget CommMonCat.{u})).pt :=
  letI : CommMonoid (F ⋙ forget CommMonCat.{u}).sections :=
    @Submonoid.toCommMonoid (∀ j, F.obj j) _
      (MonCat.sectionsSubmonoid (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))
  inferInstanceAs <| CommMonoid (Shrink (F ⋙ forget CommMonCat.{u}).sections)

@[to_additive]
/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ CommMonCat MonCat) ⋙ forget MonCat)) :=
  inferInstanceAs <| Small.{u} (Functor.sections (F ⋙ forget CommMonCat))

/-- We show that the forgetful functor `CommMonCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `CommMonoid` instance available,
and then reuse the existing limit. -/
@[to_additive /-- We show that the forgetful functor `AddCommMonCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddCommMonoid` instance available,
and then reuse the existing limit. -/]
/-
**CommMonCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget₂CreatesLimit : CreatesLimit F (forget₂ CommMonCat MonCat.{u}) :=
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone :=
        { pt := CommMonCat.of (Types.Small.limitCone (F ⋙ forget CommMonCat)).pt
          π :=
            { app j := ofHom (MonCat.limitπMonoidHom (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}) j)
              naturality _ _ j := ext <| fun x => ConcreteCategory.congr_hom
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
/-
**CommMonCat.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `CommMonCat`。
形式化陈述：limitCone : Cone F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ CommMonCat.{u} MonCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.)
-/
@[to_additive
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
/-
**CommMonCat.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CommMonCat`。
形式化陈述：limitConeIsLimit : IsLimit (limitCone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommMonCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddCommMonCat).sections` is `u`-small, `F` has a limit. -/]
/-
**CommMonCat.hasLimit** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：hasLimit : HasLimit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
If `(F ⋙ forget CommMonCat).sections` is `u`-small, `F` has a limit.
-/
instance hasLimit : HasLimit F :=
  HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/-- If `J` is `u`-small, `CommMonCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddCommMonCat.{u}` has limits of shape `J`. -/]
/-
**CommMonCat.hasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommMonCat.{u} where h
as_limit _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
If `J` is `u`-small, `CommMonCat.{u}` has limits of shape `J`.
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommMonCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative monoids has all limits. -/
@[to_additive /-- The category of additive commutative monoids has all limits. -/]
/-
**CommMonCat.hasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommMonCat.{u} wh
ere has_limits_of_shape _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The category of commutative monoids has all limits.
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommMonCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
/-
**CommMonCat.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：hasLimits : HasLimits CommMonCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**CommMonCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommMonCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J} 𝒥 := { }

@[to_additive]
/-
**CommMonCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂Mon_preservesLimits :
    PreservesLimits (forget₂ CommMonCat.{u} MonCat.{u}) :=
  CommMonCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `CommMonCat.{u}` preserves limits of
shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddCommMonCat.{u}`
preserves limits of shape `J`. -/]
/-
**CommMonCat.forget_preservesLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat
`。
形式化陈述：forget_preservesLimitsOfShape [Small.{u} J] : PreservesLimitsOfShape J (fo
rget CommMonCat.{u}) where preservesLimit {F}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
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
/-
**CommMonCat.forget_preservesLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`
。
形式化陈述：forget_preservesLimitsOfSize [UnivLE.{v, u}] : PreservesLimitsOfSize.{v, v
} (forget CommMonCat.{u}) where preservesLimitsOfShape {_} _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget CommMonCat.{u}) where
  preservesLimitsOfShape {_} _ := { }
/-
**CommMonCat._root_.AddCommMonCat.forget_preservesLimits** 是 Mathlib 中的一个实例，位于命名
空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AddCommMonCat.forget_preservesLimits :
    PreservesLimits (forget AddCommMonCat.{u}) :=
  AddCommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]
/-
**CommMonCat.forget_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：forget_preservesLimits : PreservesLimits (forget CommMonCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_preservesLimits : PreservesLimits (forget CommMonCat.{u}) :=
  CommMonCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
/-
**CommMonCat.forget_createsLimit** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：forget_createsLimit : CreatesLimit F (forget CommMonCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget CommMonCat.{u}) := by
  set e : forget CommMonCat.{u} ≅ forget₂ CommMonCat.{u} MonCat.{u} ⋙ forget MonCat.{u} :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)
  exact createsLimitOfNatIso e.symm

@[to_additive]
/-
**CommMonCat.forget_createsLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：forget_createsLimitsOfShape : CreatesLimitsOfShape J (forget MonCat.{u}) w
here CreatesLimit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_createsLimitsOfShape :
    CreatesLimitsOfShape J (forget MonCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from commutative monoids to types preserves all limits. -/
@[to_additive
/-- The forgetful functor from commutative additive monoids to types preserves all limits. -/]
/-
**CommMonCat.forget_createsLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：forget_createsLimitsOfSize : CreatesLimitsOfSize.{w, v} (forget MonCat.{u}
) where CreatesLimitsOfShape
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget MonCat.{u}) where
  CreatesLimitsOfShape := inferInstance

@[to_additive]
/-
**CommMonCat.forget_createsLimits** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
形式化陈述：forget_createsLimits : CreatesLimits (forget MonCat.{u})
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance forget_createsLimits : CreatesLimits (forget MonCat.{u}) :=
  CommMonCat.forget_createsLimitsOfSize.{u, u}

end CommMonCat

