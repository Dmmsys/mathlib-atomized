/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Category.MonCat.ForgetCorepresentable
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.CategoryTheory.ConcreteCategory.ReflectsIso
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The category of (commutative) (additive) groups has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.

-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

noncomputable section

variable {J : Type v} [Category.{w} J]

namespace GrpCat

variable (F : J ⥤ GrpCat.{u})

@[to_additive]
/--
Instance `groupObj` / 实例 `groupObj`

English:
instance groupObj
  signature: (j)
  body: inferInstanceAs Group (F.obj j)

中文:
实例 groupObj
  签名: (j)
  定义体: inferInstanceAs Group (F.obj j)

Depends on / 依赖: F.obj
-/
instance groupObj (j) : Group ((F ⋙ forget GrpCat).obj j) :=
inferInstanceAs Group (F.obj j)

/-- The flat sections of a functor into `GrpCat` form a subgroup of all sections. -/
@[to_additive
/-- The flat sections of a functor into `AddGrpCat` form an additive subgroup of all sections. -/]
/--
Definition of `sectionsSubgroup` / `sectionsSubgroup` 的定义

English:
definition sectionsSubgroup
  signature: : Subgroup (forall j, F.obj j)
  body: { MonCat.sectionsSubmonoid (F ⋙ forget₂ GrpCat MonCat) with
    carrier := (F ⋙ forget GrpCat).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).hom.map_inv (a j)]; rw [ah f] }

@[to_additive]

中文:
定义 sectionsSubgroup
  签名: : 子群 (对任意 j, F.obj j)
  定义体: { MonCat.sectionsSubmonoid (F ⋙ forget₂ GrpCat MonCat) with
    carrier := (F ⋙ forget GrpCat).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).hom.map_inv (a j)]; rw [ah f] }

@[to_additive]

Depends on / 依赖: F.map, Functor, Functor.comp_map, Functor.sections, GrpCat, MonCat, MonCat.sectionsSubmonoid, Pi.inv_apply, carrier, comp_map, forget, hom.map_inv, inv_apply, inv_mem, map_inv, sections, sectionsSubmonoid
-/
def sectionsSubgroup : Subgroup (forall j, F.obj j) :=
  { MonCat.sectionsSubmonoid (F ⋙ forget₂ GrpCat MonCat) with
    carrier := (F ⋙ forget GrpCat).sections
    inv_mem' := fun {a} ah j j' f => by
      simp only [Functor.comp_map, Pi.inv_apply]
      dsimp [Functor.sections] at ah ⊢
      rw [(F.map f).hom.map_inv (a j)]; rw [ah f] }

@[to_additive]
/--
Instance `sectionsGroup` / 实例 `sectionsGroup`

English:
instance sectionsGroup
  signature: : Group (F ⋙ forget GrpCat.{u}).sections
  body: (sectionsSubgroup F).toGroup

中文:
实例 sectionsGroup
  签名: : 群 (F ⋙ forget 群范畴.{u}).sections
  定义体: (sectionsSubgroup F).toGroup

Depends on / 依赖: sectionsSubgroup, toGroup
-/
instance sectionsGroup : Group (F ⋙ forget GrpCat.{u}).sections :=
  (sectionsSubgroup F).toGroup

/-- The projection from `Functor.sections` to a factor as a `MonoidHom`. -/
@[to_additive /-- The projection from `Functor.sections` to a factor as an `AddMonoidHom`. -/]
/--
Definition of `sectionsπMonoidHom` / `sectionsπMonoidHom` 的定义

English:
definition sectionsπMonoidHom
  signature: (j : J)
  body: x.val j
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 sectionsπMonoidHom
  签名: (j : J)
  定义体: x.val j
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: x.val
-/
def sectionsπMonoidHom (j : J) : (F ⋙ forget GrpCat.{u}).sections ->* F.obj j where
  toFun x := x.val j
  map_one' := rfl
  map_mul' _ _ := rfl

section

variable [Small.{u} (Functor.sections (F ⋙ forget GrpCat))]

@[to_additive]
/--
Instance `limitGroup` / 实例 `limitGroup`

English:
instance limitGroup
  signature: :
  body: inferInstanceAs Group (Shrink (F ⋙ forget GrpCat.{u}).sections)

@[to_additive]

中文:
实例 limitGroup
  签名: :
  定义体: inferInstanceAs Group (Shrink (F ⋙ forget GrpCat.{u}).sections)

@[to_additive]

Depends on / 依赖: GrpCat, Shrink, forget, sections
-/
noncomputable instance limitGroup :
    Group (Types.Small.limitCone.{v, u} (F ⋙ forget GrpCat.{u})).pt :=
inferInstanceAs Group (Shrink (F ⋙ forget GrpCat.{u}).sections)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat))
  body: inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget GrpCat))

中文:
实例 :
  签名: Small.{u} (函子.sections ((F ⋙ forget₂ 群范畴 幺半群范畴) ⋙ forget 幺半群范畴))
  定义体: inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget GrpCat))

Depends on / 依赖: Functor, Functor.sections, GrpCat, forget, sections
-/
instance : Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget GrpCat))

/-- We show that the forgetful functor `GrpCat ⥤ MonCat` creates limits.

All we need to do is notice that the limit point has a `Group` instance available, and then reuse
the existing limit. -/
@[to_additive /-- We show that the forgetful functor `AddGrpCat ⥤ AddMonCat` creates limits.

All we need to do is notice that the limit point has an `AddGroup` instance available, and then
reuse the existing limit. -/]
/--
Instance `Forget₂.createsLimit` / 实例 `Forget₂.createsLimit`

English:
instance Forget₂.createsLimit
  signature: :
  body: -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : (forget₂ GrpCat.{u} MonCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ GrpCat.{u} MonCat.{u}))
    fun c' t =>
      have : Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat)) := by
        have : HasLimit (F ⋙ forget₂ GrpCat MonCat) := ⟨_, t⟩
        apply Concrete.small_sections_of_hasLimit (F ⋙ forget₂ GrpCat MonCat)
have : Small.{u} (Functor.sections (F ⋙ forget GrpCat)) := inferInstanceAs Small.{u}
        (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat))
      { liftedCone :=
          { pt := GrpCat.of (Types.Small.limitCone (F ⋙ forget GrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom (F ⋙ forget₂ GrpCat MonCat) j
naturality i j h := hom_ext congr_arg MonCat.Hom.hom
                  (MonCat.HasLimits.limitCone
                        (F ⋙ forget₂ GrpCat MonCat.{u})).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
        makesLimit :=
         IsLimit.ofFaithful (forget₂ GrpCat MonCat.{u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun _ => _) fun _ => rfl }

中文:
实例 Forget₂.createsLimit
  签名: :
  定义体: -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : (forget₂ GrpCat.{u} MonCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ GrpCat.{u} MonCat.{u}))
    fun c' t =>
      have : Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat)) := by
        have : HasLimit (F ⋙ forget₂ GrpCat MonCat) := ⟨_, t⟩
        apply Concrete.small_sections_of_hasLimit (F ⋙ forget₂ GrpCat MonCat)
have : Small.{u} (Functor.sections (F ⋙ forget GrpCat)) := inferInstanceAs Small.{u}
        (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat))
      { liftedCone :=
          { pt := GrpCat.of (Types.Small.limitCone (F ⋙ forget GrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom (F ⋙ forget₂ GrpCat MonCat) j
naturality i j h := hom_ext congr_arg MonCat.Hom.hom
                  (MonCat.HasLimits.limitCone
                        (F ⋙ forget₂ GrpCat MonCat.{u})).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
        makesLimit :=
         IsLimit.ofFaithful (forget₂ GrpCat MonCat.{u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun _ => _) fun _ => rfl }
-/
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ GrpCat.{u} MonCat.{u}) :=
  -- Porting note: need to add `forget₂ GrpCat MonCat` reflects isomorphism
  letI : (forget₂ GrpCat.{u} MonCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  createsLimitOfReflectsIso (K := F) (F := (forget₂ GrpCat.{u} MonCat.{u}))
    fun c' t =>
      have : Small.{u} (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat)) := by
        have : HasLimit (F ⋙ forget₂ GrpCat MonCat) := ⟨_, t⟩
        apply Concrete.small_sections_of_hasLimit (F ⋙ forget₂ GrpCat MonCat)
have : Small.{u} (Functor.sections (F ⋙ forget GrpCat)) := inferInstanceAs Small.{u}
        (Functor.sections ((F ⋙ forget₂ GrpCat MonCat) ⋙ forget MonCat))
      { liftedCone :=
          { pt := GrpCat.of (Types.Small.limitCone (F ⋙ forget GrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom (F ⋙ forget₂ GrpCat MonCat) j
naturality i j h := hom_ext congr_arg MonCat.Hom.hom
                  (MonCat.HasLimits.limitCone
                        (F ⋙ forget₂ GrpCat MonCat.{u})).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (MonCat.HasLimits.limitConeIsLimit.{v, u} _) t
        makesLimit :=
         IsLimit.ofFaithful (forget₂ GrpCat MonCat.{u}) (MonCat.HasLimits.limitConeIsLimit _)
          (fun _ => _) fun _ => rfl }

/-- A choice of limit cone for a functor into `GrpCat`.
(Generally, you'll just want to use `limit F`.) -/
@[to_additive /-- A choice of limit cone for a functor into `GrpCat`.
  (Generally, you'll just want to use `limit F`.) -/]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: liftLimit (limit.isLimit (F ⋙ forget₂ GrpCat.{u} MonCat.{u}))

中文:
定义 limitCone
  签名: : 锥 F
  定义体: liftLimit (limit.isLimit (F ⋙ forget₂ GrpCat.{u} MonCat.{u}))

Depends on / 依赖: GrpCat, MonCat, isLimit, liftLimit, limit.isLimit
-/
noncomputable def limitCone : Cone F :=
  liftLimit (limit.isLimit (F ⋙ forget₂ GrpCat.{u} MonCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/
@[to_additive /-- The chosen cone is a limit cone.
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

Depends on / 依赖: CommBialgCat, ConcreteCategory, ConcreteCategory.hom, liftedLimitIsLimit
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget GrpCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddGrpCat).sections` is `u`-small, `F` has a limit. -/]
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

end

/-- A functor `F : J ⥤ GrpCat.{u}` has a limit iff `(F ⋙ forget GrpCat).sections` is
`u`-small. -/
@[to_additive /-- A functor `F : J ⥤ AddGrpCat.{u}` has a limit iff
`(F ⋙ forget AddGrpCat).sections` is `u`-small. -/]
/--
lemma `hasLimit_iff_small_sections` / 引理 `hasLimit_iff_small_sections`

English:
lemma hasLimit_iff_small_sections
  proof: by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

中文:
引理 hasLimit_iff_small_sections
  证明: by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

Depends on / 依赖: Concrete, Concrete.small_sections_of_hasLimit, infer_instance, small_sections_of_hasLimit
-/
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget GrpCat).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

/-- If `J` is `u`-small, `GrpCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddGrpCat.{u}` has limits of shape `J`. -/]
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
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J GrpCat.{u} where
  has_limit _ := inferInstance

/-- The category of groups has all limits. -/
@[to_additive /-- The category of additive groups has all limits. -/]
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
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} GrpCat.{u} where
  has_limits_of_shape J _ := { }

@[to_additive]
/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits GrpCat.{u}
  body: GrpCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 群范畴.{u}
  定义体: GrpCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: GrpCat, GrpCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits GrpCat.{u} :=
  GrpCat.hasLimitsOfSize.{u, u}

/-- The forgetful functor from groups to monoids preserves all limits.

This means the underlying monoid of a limit can be computed as a limit in the category of monoids.
-/
@[to_additive AddGrpCat.forget₂AddMonPreservesLimitsOfSize
/-- The forgetful functor from additive groups to additive monoids preserves all limits.

This means the underlying additive monoid of a limit can be computed as a limit in the category of
additive monoids. -/]
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
-/
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ GrpCat.{u} MonCat.{u}) where
  preservesLimitsOfShape {J _} := { }

@[to_additive]
/--
Instance `forget₂Mon_preservesLimits` / 实例 `forget₂Mon_preservesLimits`

English:
instance forget₂Mon_preservesLimits
  signature: : PreservesLimits (forget₂ GrpCat.{u} MonCat.{u})
  body: GrpCat.forget₂Mon_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂Mon_preservesLimits
  签名: : PreservesLimits (forget₂ 群范畴.{u} 幺半群范畴.{u})
  定义体: GrpCat.forget₂Mon_preservesLimitsOfSize.{u, u}

Depends on / 依赖: GrpCat, GrpCat.forget
-/
instance forget₂Mon_preservesLimits : PreservesLimits (forget₂ GrpCat.{u} MonCat.{u}) :=
  GrpCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/-- If `J` is `u`-small, the forgetful functor from `GrpCat.{u}` preserves limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddGrpCat.{u}` preserves limits
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
instance forget_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget GrpCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/
@[to_additive
/-- The forgetful functor from additive groups to types preserves all limits.

This means the underlying type of a limit can be computed as a limit in the category of types. -/]
/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: :
  body: inferInstance

@[to_additive]

中文:
实例 forget_preservesLimitsOfSize
  签名: :
  定义体: inferInstance

@[to_additive]
-/
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget GrpCat.{u}) := inferInstance

@[to_additive]
/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget GrpCat.{u})
  body: GrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 群范畴.{u})
  定义体: GrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]

Depends on / 依赖: GrpCat, GrpCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget GrpCat.{u}) :=
  GrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
/--
Instance `forget_createsLimit` / 实例 `forget_createsLimit`

English:
instance forget_createsLimit
  signature: :
  body: by
  set e : forget₂ GrpCat.{u} MonCat.{u} ⋙ forget MonCat.{u} ≅ forget GrpCat.{u} := Iso.refl _
  exact createsLimitOfNatIso e

@[to_additive]

中文:
实例 forget_createsLimit
  签名: :
  定义体: by
  set e : forget₂ GrpCat.{u} MonCat.{u} ⋙ forget MonCat.{u} ≅ forget GrpCat.{u} := Iso.refl _
  exact createsLimitOfNatIso e

@[to_additive]

Depends on / 依赖: GrpCat, Iso.refl, MonCat, createsLimitOfNatIso, forget
-/
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget GrpCat.{u}) := by
  set e : forget₂ GrpCat.{u} MonCat.{u} ⋙ forget MonCat.{u} ≅ forget GrpCat.{u} := Iso.refl _
  exact createsLimitOfNatIso e

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
    CreatesLimitsOfShape J (forget GrpCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from groups to types creates all limits.
-/
@[to_additive
/-- The forgetful functor from additive groups to types creates all limits. -/]
/--
Instance `forget_createsLimitsOfSize` / 实例 `forget_createsLimitsOfSize`

English:
instance forget_createsLimitsOfSize
  signature: :
  body: inferInstance

中文:
实例 forget_createsLimitsOfSize
  签名: :
  定义体: inferInstance
-/
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget GrpCat.{u}) where
  CreatesLimitsOfShape := inferInstance
end GrpCat

namespace CommGrpCat

variable (F : J ⥤ CommGrpCat.{u})

@[to_additive]
/--
Instance `commGroupObj` / 实例 `commGroupObj`

English:
instance commGroupObj
  signature: (j)
  body: inferInstanceAs CommGroup (F.obj j)

@[to_additive]

中文:
实例 commGroupObj
  签名: (j)
  定义体: inferInstanceAs CommGroup (F.obj j)

@[to_additive]

Depends on / 依赖: CommGroup, F.obj
-/
instance commGroupObj (j) : CommGroup ((F ⋙ forget CommGrpCat).obj j) :=
inferInstanceAs CommGroup (F.obj j)

@[to_additive]
/--
Instance `limitCommGroup` / 实例 `limitCommGroup`

English:
instance limitCommGroup
  body: letI : CommGroup (F ⋙ forget CommGrpCat.{u}).sections :=
    @Subgroup.toCommGroup (forall j, F.obj j) _
      (GrpCat.sectionsSubgroup (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))
inferInstanceAs CommGroup (Shrink (F ⋙ forget CommGrpCat.{u}).sections)

@[to_additive]

中文:
实例 limitCommGroup
  定义体: letI : CommGroup (F ⋙ forget CommGrpCat.{u}).sections :=
    @Subgroup.toCommGroup (forall j, F.obj j) _
      (GrpCat.sectionsSubgroup (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))
inferInstanceAs CommGroup (Shrink (F ⋙ forget CommGrpCat.{u}).sections)

@[to_additive]

Depends on / 依赖: CommGroup, CommGrpCat, F.obj, GrpCat, GrpCat.sectionsSubgroup, Shrink, Subgroup, Subgroup.toCommGroup, forget, sections, sectionsSubgroup, toCommGroup
-/
noncomputable instance limitCommGroup
    [Small.{u} (Functor.sections (F ⋙ forget CommGrpCat))] :
    CommGroup (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrpCat.{u})).pt :=
  letI : CommGroup (F ⋙ forget CommGrpCat.{u}).sections :=
    @Subgroup.toCommGroup (forall j, F.obj j) _
      (GrpCat.sectionsSubgroup (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))
inferInstanceAs CommGroup (Shrink (F ⋙ forget CommGrpCat.{u}).sections)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ CommGrpCat.{u} GrpCat.{u}).ReflectsIsomorphisms
  body: reflectsIsomorphisms_forget₂ _ _

中文:
实例 :
  签名: (forget₂ 交换群范畴.{u} 群范畴.{u}).反映同构
  定义体: reflectsIsomorphisms_forget₂ _ _
-/
instance : (forget₂ CommGrpCat.{u} GrpCat.{u}).ReflectsIsomorphisms :=
    reflectsIsomorphisms_forget₂ _ _

/-- We show that the forgetful functor `CommGrpCat ⥤ GrpCat` creates limits.

All we need to do is notice that the limit point has a `CommGroup` instance available,
and then reuse the existing limit.
-/
@[to_additive /-- We show that the forgetful functor `AddCommGrpCat ⥤ AddGrpCat` creates limits.

All we need to do is notice that the limit point has an `AddCommGroup` instance available,
and then reuse the existing limit. -/]
/--
Instance `Forget₂.createsLimit` / 实例 `Forget₂.createsLimit`

English:
instance Forget₂.createsLimit
  signature: :
  body: createsLimitOfReflectsIso (fun c hc => by
    have : HasLimit _ := ⟨_, hc⟩
    have : Small.{u} (F ⋙ forget CommGrpCat).sections :=
      Concrete.small_sections_of_hasLimit (F ⋙ forget₂ CommGrpCat GrpCat)
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat) ⋙
      forget MonCat).sections := this
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).sections := this
    exact
      { liftedCone :=
          { pt := CommGrpCat.of (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGrpCat GrpCat.{u} ⋙ forget₂ GrpCat MonCat.{u}) j
naturality i j h := hom_ext congr_arg MonCat.Hom.hom
                  (MonCat.HasLimits.limitCone _).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (GrpCat.limitConeIsLimit _) hc
        makesLimit :=
          IsLimit.ofFaithful (forget₂ _ GrpCat.{u} ⋙ forget₂ _ MonCat.{u})
            (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl })

中文:
实例 Forget₂.createsLimit
  签名: :
  定义体: createsLimitOfReflectsIso (fun c hc => by
    have : HasLimit _ := ⟨_, hc⟩
    have : Small.{u} (F ⋙ forget CommGrpCat).sections :=
      Concrete.small_sections_of_hasLimit (F ⋙ forget₂ CommGrpCat GrpCat)
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat) ⋙
      forget MonCat).sections := this
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).sections := this
    exact
      { liftedCone :=
          { pt := CommGrpCat.of (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGrpCat GrpCat.{u} ⋙ forget₂ GrpCat MonCat.{u}) j
naturality i j h := hom_ext congr_arg MonCat.Hom.hom
                  (MonCat.HasLimits.limitCone _).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (GrpCat.limitConeIsLimit _) hc
        makesLimit :=
          IsLimit.ofFaithful (forget₂ _ GrpCat.{u} ⋙ forget₂ _ MonCat.{u})
            (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl })
-/
noncomputable instance Forget₂.createsLimit :
    CreatesLimit F (forget₂ CommGrpCat GrpCat.{u}) :=
  createsLimitOfReflectsIso (fun c hc => by
    have : HasLimit _ := ⟨_, hc⟩
    have : Small.{u} (F ⋙ forget CommGrpCat).sections :=
      Concrete.small_sections_of_hasLimit (F ⋙ forget₂ CommGrpCat GrpCat)
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat) ⋙
      forget MonCat).sections := this
    have : Small.{u} ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).sections := this
    exact
      { liftedCone :=
          { pt := CommGrpCat.of (Types.Small.limitCone.{v, u} (F ⋙ forget CommGrpCat)).pt
            π :=
              { app j := ofHom <| MonCat.limitπMonoidHom
                  (F ⋙ forget₂ CommGrpCat GrpCat.{u} ⋙ forget₂ GrpCat MonCat.{u}) j
naturality i j h := hom_ext congr_arg MonCat.Hom.hom
                  (MonCat.HasLimits.limitCone _).π.naturality h } }
        validLift := by apply IsLimit.uniqueUpToIso (GrpCat.limitConeIsLimit _) hc
        makesLimit :=
          IsLimit.ofFaithful (forget₂ _ GrpCat.{u} ⋙ forget₂ _ MonCat.{u})
            (by apply MonCat.HasLimits.limitConeIsLimit _) (fun s => _) fun s => rfl })

section

variable [Small.{u} (Functor.sections (F ⋙ forget CommGrpCat))]

/-- A choice of limit cone for a functor into `CommGrpCat`.
(Generally, you'll just want to use `limit F`.) -/
@[to_additive
/-- A choice of limit cone for a functor into `AddCommGrpCat`.
(Generally, you'll just want to use `limit F`.) -/]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat)) :=
inferInstanceAs Small (Functor.sections (F ⋙ forget CommGrpCat))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))

中文:
定义 limitCone
  签名: : 锥 F
  定义体: letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat)) :=
inferInstanceAs Small (Functor.sections (F ⋙ forget CommGrpCat))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))

Depends on / 依赖: CommGrpCat, Functor, Functor.sections, GrpCat, forget, isLimit, liftLimit, limit.isLimit, sections
-/
noncomputable def limitCone : Cone F :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat)) :=
inferInstanceAs Small (Functor.sections (F ⋙ forget CommGrpCat))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommGrpCat.{u} GrpCat.{u}))

/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/
@[to_additive
/-- The chosen cone is a limit cone.
(Generally, you'll just want to use `limit.cone F`.) -/]
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone.{v, u} F)
  body: liftedLimitIsLimit _

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone.{v, u} F)
  定义体: liftedLimitIsLimit _

Depends on / 依赖: liftedLimitIsLimit
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

/-- If `(F ⋙ forget CommGrpCat).sections` is `u`-small, `F` has a limit. -/
@[to_additive /-- If `(F ⋙ forget AddCommGrpCat).sections` is `u`-small, `F` has a limit. -/]
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

end

/-- A functor `F : J ⥤ CommGrpCat.{u}` has a limit iff `(F ⋙ forget CommGrpCat).sections` is
`u`-small. -/
@[to_additive /-- A functor `F : J ⥤ AddCommGrpCat.{u}` has a limit iff
`(F ⋙ forget AddCommGrpCat).sections` is `u`-small. -/]
/--
lemma `hasLimit_iff_small_sections` / 引理 `hasLimit_iff_small_sections`

English:
lemma hasLimit_iff_small_sections
  proof: by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

中文:
引理 hasLimit_iff_small_sections
  证明: by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

Depends on / 依赖: Concrete, Concrete.small_sections_of_hasLimit, infer_instance, small_sections_of_hasLimit
-/
lemma hasLimit_iff_small_sections :
    HasLimit F ↔ Small.{u} (F ⋙ forget CommGrpCat).sections := by
  constructor
  · apply Concrete.small_sections_of_hasLimit
  · intro
    infer_instance

/-- If `J` is `u`-small, `CommGrpCat.{u}` has limits of shape `J`. -/
@[to_additive /-- If `J` is `u`-small, `AddCommGrpCat.{u}` has limits of shape `J`. -/]
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
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommGrpCat.{u} where
  has_limit _ := inferInstance

/-- The category of commutative groups has all limits. -/
@[to_additive
/-- The category of additive commutative groups has all limits. -/]
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

Depends on / 依赖: comm_comul
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommGrpCat.{u} where
  has_limits_of_shape _ _ := { }

@[to_additive]
/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits CommGrpCat.{u}
  body: CommGrpCat.hasLimitsOfSize.{u, u}

@[to_additive]

中文:
实例 hasLimits
  签名: : 有极限 交换群范畴.{u}
  定义体: CommGrpCat.hasLimitsOfSize.{u, u}

@[to_additive]

Depends on / 依赖: CommGrpCat, CommGrpCat.hasLimitsOfSize, MonObj, MonObj.mul_assoc_flip, MonObj.mul_one, MonObj.one_mul, hasLimitsOfSize, mul_assoc_flip, mul_one, ofAlgHom, one_mul, unop.hom
-/
instance hasLimits : HasLimits CommGrpCat.{u} :=
  CommGrpCat.hasLimitsOfSize.{u, u}

@[to_additive]
/--
Instance `forget₂Group_preservesLimit` / 实例 `forget₂Group_preservesLimit`

English:
instance forget₂Group_preservesLimit
  signature: :
  body: ⟨by
    have : HasLimit (F ⋙ forget₂ CommGrpCat GrpCat) := by
      rw [GrpCat.hasLimit_iff_small_sections]
      change Small.{u} (F ⋙ forget CommGrpCat).sections
      rw [← CommGrpCat.hasLimit_iff_small_sections]
      exact ⟨_, hc⟩
    exact isLimitOfPreserves _ hc⟩

@[to_additive]

中文:
实例 forget₂Group_preservesLimit
  签名: :
  定义体: ⟨by
    have : HasLimit (F ⋙ forget₂ CommGrpCat GrpCat) := by
      rw [GrpCat.hasLimit_iff_small_sections]
      change Small.{u} (F ⋙ forget CommGrpCat).sections
      rw [← CommGrpCat.hasLimit_iff_small_sections]
      exact ⟨_, hc⟩
    exact isLimitOfPreserves _ hc⟩

@[to_additive]

Depends on / 依赖: CommGrpCat, CommGrpCat.hasLimit_iff_small_sections, GrpCat, GrpCat.hasLimit_iff_small_sections, HasLimit, forget, hasLimit_iff_small_sections, isLimitOfPreserves, sections
-/
instance forget₂Group_preservesLimit :
    PreservesLimit F (forget₂ CommGrpCat.{u} GrpCat.{u}) where
  preserves {c} hc := ⟨by
    have : HasLimit (F ⋙ forget₂ CommGrpCat GrpCat) := by
      rw [GrpCat.hasLimit_iff_small_sections]
      change Small.{u} (F ⋙ forget CommGrpCat).sections
      rw [← CommGrpCat.hasLimit_iff_small_sections]
      exact ⟨_, hc⟩
    exact isLimitOfPreserves _ hc⟩

@[to_additive]
/--
Instance `forget₂Group_preservesLimitsOfShape` / 实例 `forget₂Group_preservesLimitsOfShape`

English:
instance forget₂Group_preservesLimitsOfShape
  signature: :

中文:
实例 forget₂Group_preservesLimitsOfShape
  签名: :
-/
instance forget₂Group_preservesLimitsOfShape :
    PreservesLimitsOfShape J (forget₂ CommGrpCat.{u} GrpCat.{u}) where

/-- The forgetful functor from commutative groups to groups preserves all limits.
(That is, the underlying group could have been computed instead as limits in the category
of groups.)
-/
@[to_additive
/-- The forgetful functor from additive commutative groups to additive groups preserves all
limits. (That is, the underlying group could have been computed instead as limits in the
category of additive groups.) -/]
/--
Instance `forget₂Group_preservesLimitsOfSize` / 实例 `forget₂Group_preservesLimitsOfSize`

English:
instance forget₂Group_preservesLimitsOfSize
  signature: :

中文:
实例 forget₂Group_preservesLimitsOfSize
  签名: :
-/
instance forget₂Group_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGrpCat.{u} GrpCat.{u}) where

@[to_additive]
/--
Instance `forget₂Group_preservesLimits` / 实例 `forget₂Group_preservesLimits`

English:
instance forget₂Group_preservesLimits
  signature: :
  body: CommGrpCat.forget₂Group_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂Group_preservesLimits
  签名: :
  定义体: CommGrpCat.forget₂Group_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommAlgCat, CommAlgCat.of, CommGrpCat, CommGrpCat.forget, IsCommMonObj
-/
instance forget₂Group_preservesLimits :
    PreservesLimits (forget₂ CommGrpCat GrpCat.{u}) :=
  CommGrpCat.forget₂Group_preservesLimitsOfSize.{u, u}

/-- An auxiliary declaration to speed up typechecking. -/
@[to_additive AddCommGrpCat.forget₂AddCommMon_preservesLimitsAux
/-- An auxiliary declaration to speed up typechecking. -/]
/--
Definition of `forget₂CommMon_preservesLimitsAux` / `forget₂CommMon_preservesLimitsAux` 的定义

English:
definition forget₂CommMon_preservesLimitsAux
  body: letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ CommMonCat) ⋙ forget CommMonCat)) :=
inferInstanceAs Small (Functor.sections (F ⋙ forget CommGrpCat))
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGrpCat.{u} CommMonCat.{u})

中文:
定义 forget₂CommMon_preservesLimitsAux
  定义体: letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ CommMonCat) ⋙ forget CommMonCat)) :=
inferInstanceAs Small (Functor.sections (F ⋙ forget CommGrpCat))
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGrpCat.{u} CommMonCat.{u})

Depends on / 依赖: CommGrpCat, CommMonCat, CommMonCat.limitConeIsLimit, Functor, Functor.sections, forget, limitConeIsLimit, sections
-/
noncomputable def forget₂CommMon_preservesLimitsAux
    [Small.{u} (F ⋙ forget CommGrpCat).sections] :
    IsLimit ((forget₂ CommGrpCat.{u} CommMonCat.{u}).mapCone (limitCone.{v, u} F)) :=
  letI : Small.{u} (Functor.sections ((F ⋙ forget₂ _ CommMonCat) ⋙ forget CommMonCat)) :=
inferInstanceAs Small (Functor.sections (F ⋙ forget CommGrpCat))
  CommMonCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommGrpCat.{u} CommMonCat.{u})

/-- If `J` is `u`-small, the forgetful functor from `CommGrpCat.{u}` to `CommMonCat.{u}`
preserves limits of shape `J`. -/
@[to_additive AddCommGrpCat.forget₂AddCommMon_preservesLimitsOfShape
/-- If `J` is `u`-small, the forgetful functor from `AddCommGrpCat.{u}`
to `AddCommMonCat.{u}` preserves limits of shape `J`. -/]
/--
Instance `forget₂CommMon_preservesLimitsOfShape` / 实例 `forget₂CommMon_preservesLimitsOfShape`

English:
instance forget₂CommMon_preservesLimitsOfShape
  signature: [Small.{u} J]
  body: preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
      (forget₂CommMon_preservesLimitsAux.{v, u} F)

中文:
实例 forget₂CommMon_preservesLimitsOfShape
  签名: [Small.{u} J]
  定义体: preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
      (forget₂CommMon_preservesLimitsAux.{v, u} F)

Depends on / 依赖: limitConeIsLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂CommMon_preservesLimitsOfShape [Small.{u} J] :
    PreservesLimitsOfShape J (forget₂ CommGrpCat.{u} CommMonCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
      (forget₂CommMon_preservesLimitsAux.{v, u} F)

/-- The forgetful functor from commutative groups to commutative monoids preserves all limits.
(That is, the underlying commutative monoids could have been computed instead as limits
in the category of commutative monoids.)
-/
@[to_additive AddCommGrpCat.forget₂AddCommMon_preservesLimitsOfSize
/-- The forgetful functor from additive commutative groups to additive commutative monoids
preserves all limits. (That is, the underlying additive commutative monoids could have been
computed instead as limits in the category of additive commutative monoids.) -/]
/--
Instance `forget₂CommMon_preservesLimitsOfSize` / 实例 `forget₂CommMon_preservesLimitsOfSize`

English:
instance forget₂CommMon_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

中文:
实例 forget₂CommMon_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }
-/
instance forget₂CommMon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommGrpCat CommMonCat.{u}) where
  preservesLimitsOfShape := { }

/-- If `J` is `u`-small, the forgetful functor from `CommGrpCat.{u}` preserves limits of
shape `J`. -/
@[to_additive /-- If `J` is `u`-small, the forgetful functor from `AddCommGrpCat.{u}`
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
    PreservesLimitsOfShape J (forget CommGrpCat.{u}) where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (Types.Small.limitConeIsLimit (F ⋙ forget _))

/-- The forgetful functor from commutative groups to types preserves all limits. (That is, the
underlying types could have been computed instead as limits in the category of types.)
-/
@[to_additive
/-- The forgetful functor from additive commutative groups to types preserves all limits.
(That is, the underlying types could have been computed instead as limits in the category of
types.) -/]
/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: :
  body: inferInstance

中文:
实例 forget_preservesLimitsOfSize
  签名: :
  定义体: inferInstance

Depends on / 依赖: CommHopfAlgCat, ConcreteCategory, ConcreteCategory.hom
-/
instance forget_preservesLimitsOfSize :
    PreservesLimitsOfSize.{w, v} (forget CommGrpCat.{u}) := inferInstance

/--
Instance `_root_.AddCommGrpCat.forget_preservesLimits` / 实例 `_root_.AddCommGrpCat.forget_preservesLimits`

English:
instance _root_.AddCommGrpCat.forget_preservesLimits
  signature: :
  body: AddCommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]

中文:
实例 _root_.加法交换群范畴.forget_preservesLimits
  签名: :
  定义体: AddCommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
noncomputable instance _root_.AddCommGrpCat.forget_preservesLimits :
    PreservesLimits (forget AddCommGrpCat.{u}) :=
  AddCommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive existing]
/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget CommGrpCat.{u})
  body: CommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 交换群范畴.{u})
  定义体: CommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]

Depends on / 依赖: CommGrpCat, CommGrpCat.forget_preservesLimitsOfSize, f.hom, forget_preservesLimitsOfSize
-/
noncomputable instance forget_preservesLimits : PreservesLimits (forget CommGrpCat.{u}) :=
  CommGrpCat.forget_preservesLimitsOfSize.{u, u}

@[to_additive]
/--
Instance `forget_createsLimit` / 实例 `forget_createsLimit`

English:
instance forget_createsLimit
  signature: :
  body: by
  set e : forget₂ CommGrpCat.{u} GrpCat.{u} ⋙ forget GrpCat.{u} ≅ forget CommGrpCat.{u} := .refl _
  exact createsLimitOfNatIso e

@[to_additive]

中文:
实例 forget_createsLimit
  签名: :
  定义体: by
  set e : forget₂ CommGrpCat.{u} GrpCat.{u} ⋙ forget GrpCat.{u} ≅ forget CommGrpCat.{u} := .refl _
  exact createsLimitOfNatIso e

@[to_additive]

Depends on / 依赖: CommGrpCat, GrpCat, createsLimitOfNatIso, forget
-/
noncomputable instance forget_createsLimit :
    CreatesLimit F (forget CommGrpCat.{u}) := by
  set e : forget₂ CommGrpCat.{u} GrpCat.{u} ⋙ forget GrpCat.{u} ≅ forget CommGrpCat.{u} := .refl _
  exact createsLimitOfNatIso e

@[to_additive]
/--
Instance `forget_createsLimitsOfShape` / 实例 `forget_createsLimitsOfShape`

English:
instance forget_createsLimitsOfShape
  signature: (J : Type v) [Category.{w} J]
  body: inferInstance

中文:
实例 forget_createsLimitsOfShape
  签名: (J : 类型v) [范畴.{w} J]
  定义体: inferInstance
-/
noncomputable instance forget_createsLimitsOfShape (J : Type v) [Category.{w} J] :
    CreatesLimitsOfShape J (forget CommGrpCat.{u}) where
  CreatesLimit := inferInstance

/-- The forgetful functor from commutative groups to types creates all limits.
-/
@[to_additive
/-- The forgetful functor from additive commutative groups to types creates all limits. -/]
/--
Instance `forget_createsLimitsOfSize` / 实例 `forget_createsLimitsOfSize`

English:
instance forget_createsLimitsOfSize
  signature: :
  body: inferInstance

中文:
实例 forget_createsLimitsOfSize
  签名: :
  定义体: inferInstance
-/
noncomputable instance forget_createsLimitsOfSize :
    CreatesLimitsOfSize.{w, v} (forget CommGrpCat.{u}) where
  CreatesLimitsOfShape := inferInstance

-- Verify we can form limits indexed over smaller categories.
example (f : Nat -> AddCommGrpCat) : HasProduct f := by infer_instance

end CommGrpCat

namespace AddCommGrpCat

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `kernelIsoKer` / `kernelIsoKer` 的定义

English:
definition kernelIsoKer
  signature: {G H : AddCommGrpCat.{u}} (f : G ⟶ H)
  body: ofHom
    { toFun := fun g => ⟨kernel.ι f g, ConcreteCategory.congr_hom (kernel.condition f) g⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := fun g g' => by
        refine Subtype.ext ?_
        simp }
inv := kernel.lift f (ofHom (AddSubgroup.subtype f.hom.ker)) by ext x; exact x.2
  hom_inv_id := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): it would be nice to do the next two steps by a single `ext`,
    -- but this will require thinking carefully about the relative priorities of `@[ext]` lemmas.
    refine equalizer.hom_ext ?_
    ext
    simp
  inv_hom_id := by
    apply AddCommGrpCat.ext
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    apply ConcreteCategory.congr_hom (kernel.lift_ι f _ _)

@[simp]

中文:
定义 kernelIsoKer
  签名: {G H : 加法交换群范畴.{u}} (f : G ⟶ H)
  定义体: ofHom
    { toFun := fun g => ⟨kernel.ι f g, ConcreteCategory.congr_hom (kernel.condition f) g⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := fun g g' => by
        refine Subtype.ext ?_
        simp }
inv := kernel.lift f (ofHom (AddSubgroup.subtype f.hom.ker)) by ext x; exact x.2
  hom_inv_id := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): it would be nice to do the next two steps by a single `ext`,
    -- but this will require thinking carefully about the relative priorities of `@[ext]` lemmas.
    refine equalizer.hom_ext ?_
    ext
    simp
  inv_hom_id := by
    apply AddCommGrpCat.ext
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    apply ConcreteCategory.congr_hom (kernel.lift_ι f _ _)

@[simp]
-/
def kernelIsoKer {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    kernel f ≅ AddCommGrpCat.of f.hom.ker where
  hom := ofHom
    { toFun := fun g => ⟨kernel.ι f g, ConcreteCategory.congr_hom (kernel.condition f) g⟩
      map_zero' := by
        refine Subtype.ext ?_
        simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := fun g g' => by
        refine Subtype.ext ?_
        simp }
inv := kernel.lift f (ofHom (AddSubgroup.subtype f.hom.ker)) by ext x; exact x.2
  hom_inv_id := by
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): it would be nice to do the next two steps by a single `ext`,
    -- but this will require thinking carefully about the relative priorities of `@[ext]` lemmas.
    refine equalizer.hom_ext ?_
    ext
    simp
  inv_hom_id := by
    apply AddCommGrpCat.ext
    rintro ⟨x, mem⟩
    refine Subtype.ext ?_
    apply ConcreteCategory.congr_hom (kernel.lift_ι f _ _)

@[simp]
/--
theorem `kernelIsoKer_hom_comp_subtype` / 定理 `kernelIsoKer_hom_comp_subtype`

English:
theorem kernelIsoKer_hom_comp_subtype
  given: {G H : AddCommGrpCat.{u}} (f : G ⟶ H)
  proof: by ext; rfl

@[simp]

中文:
定理 kernelIsoKer_hom_comp_subtype
  条件: {G H : 加法交换群范畴.{u}} (f : G ⟶ H)
  证明: by ext; rfl

@[simp]
-/
theorem kernelIsoKer_hom_comp_subtype {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).hom ≫ ofHom (AddSubgroup.subtype f.hom.ker) = kernel.ι f := by ext; rfl

@[simp]
/--
theorem `kernelIsoKer_inv_comp_ι` / 定理 `kernelIsoKer_inv_comp_ι`

English:
theorem kernelIsoKer_inv_comp_ι
  given: {G H : AddCommGrpCat.{u}} (f : G ⟶ H)
  proof: by
  simp [kernelIsoKer]

中文:
定理 kernelIsoKer_inv_comp_ι
  条件: {G H : 加法交换群范畴.{u}} (f : G ⟶ H)
  证明: by
  simp [kernelIsoKer]

Depends on / 依赖: kernelIsoKer
-/
theorem kernelIsoKer_inv_comp_ι {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ kernel.ι f = ofHom (AddSubgroup.subtype f.hom.ker) := by
  simp [kernelIsoKer]

/--
Definition of `kernelIsoKerOver` / `kernelIsoKerOver` 的定义

English:
definition kernelIsoKerOver
  signature: {G H : AddCommGrpCat.{u}} (f : G ⟶ H)
  body: Over.isoMk (kernelIsoKer f)

中文:
定义 kernelIsoKerOver
  签名: {G H : 加法交换群范畴.{u}} (f : G ⟶ H)
  定义体: Over.isoMk (kernelIsoKer f)

Depends on / 依赖: Over.isoMk, kernelIsoKer
-/
def kernelIsoKerOver {G H : AddCommGrpCat.{u}} (f : G ⟶ H) :
    Over.mk (kernel.ι f) ≅ @Over.mk _ _ G (AddCommGrpCat.of f.hom.ker)
      (ofHom (AddSubgroup.subtype f.hom.ker)) :=
  Over.isoMk (kernelIsoKer f)

end AddCommGrpCat
