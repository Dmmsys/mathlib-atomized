/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.Ring.Shrink -- shake: keep (Semiring (Shrink ...)), cf. lean#13417
public import Mathlib.Algebra.Ring.Subring.Defs

/-!
# The category of (commutative) rings has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

@[expose] public section


-- We use the following trick a lot of times in this file.
library_note «change elaboration strategy with `by apply`» /--
Some definitions may be extremely slow to elaborate, when the target type to be constructed
is complicated and when the type of the term given in the definition is also complicated and does
not obviously match the target type. In this case, instead of just giving the term, prefixing it
with `by apply` may speed up things considerably as the types are not elaborated in the same order.
-/

open CategoryTheory Limits

universe v u w

noncomputable section

namespace SemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ SemiRingCat.{u})

/--
Instance `semiringObj` / 实例 `semiringObj`

English:
instance semiringObj
  signature: (j)
  body: inferInstanceAs Semiring (F.obj j)

中文:
实例 semiringObj
  签名: (j)
  定义体: inferInstanceAs Semiring (F.obj j)

Depends on / 依赖: F.obj, Semiring
-/
instance semiringObj (j) : Semiring ((F ⋙ forget SemiRingCat).obj j) :=
inferInstanceAs Semiring (F.obj j)

/--
Definition of `sectionsSubsemiring` / `sectionsSubsemiring` 的定义

English:
definition sectionsSubsemiring
  signature: : Subsemiring (forall j, F.obj j)
  body: { (MonCat.sectionsSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} MonCat.{u})),
    (AddMonCat.sectionsAddSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
      forget₂ AddCommMonCat AddMonCat)) with
    carrier := (F ⋙ forget SemiRingCat).sections }

中文:
定义 sectionsSubsemiring
  签名: : 子半环 (对任意 j, F.obj j)
  定义体: { (MonCat.sectionsSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} MonCat.{u})),
    (AddMonCat.sectionsAddSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
      forget₂ AddCommMonCat AddMonCat)) with
    carrier := (F ⋙ forget SemiRingCat).sections }

Depends on / 依赖: AddCommMonCat, AddMonCat, AddMonCat.sectionsAddSubmonoid, MonCat, MonCat.sectionsSubmonoid, SemiRingCat, carrier, forget, sections, sectionsAddSubmonoid, sectionsSubmonoid
-/
def sectionsSubsemiring : Subsemiring (forall j, F.obj j) :=
  { (MonCat.sectionsSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} MonCat.{u})),
    (AddMonCat.sectionsAddSubmonoid (J := J) (F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
      forget₂ AddCommMonCat AddMonCat)) with
    carrier := (F ⋙ forget SemiRingCat).sections }

/--
Instance `sectionsSemiring` / 实例 `sectionsSemiring`

English:
instance sectionsSemiring
  signature: : Semiring (F ⋙ forget SemiRingCat.{u}).sections
  body: (sectionsSubsemiring F).toSemiring

中文:
实例 sectionsSemiring
  签名: : 半环 (F ⋙ forget Semi环范畴.{u}).sections
  定义体: (sectionsSubsemiring F).toSemiring

Depends on / 依赖: sectionsSubsemiring, toSemiring
-/
instance sectionsSemiring : Semiring (F ⋙ forget SemiRingCat.{u}).sections :=
  (sectionsSubsemiring F).toSemiring

variable [Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))]

/--
Instance `limitSemiring` / 实例 `limitSemiring`

English:
instance limitSemiring
  signature: :
  body: let _ : Semiring (F ⋙ forget SemiRingCat).sections := (sectionsSubsemiring F).toSemiring
inferInstanceAs Semiring (Shrink (F ⋙ forget SemiRingCat).sections)

中文:
实例 limitSemiring
  签名: :
  定义体: let _ : Semiring (F ⋙ forget SemiRingCat).sections := (sectionsSubsemiring F).toSemiring
inferInstanceAs Semiring (Shrink (F ⋙ forget SemiRingCat).sections)

Depends on / 依赖: SemiRingCat, Semiring, Shrink, forget, sections, sectionsSubsemiring, toSemiring
-/
instance limitSemiring :
    Semiring (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat.{u})).pt :=
  let _ : Semiring (F ⋙ forget SemiRingCat).sections := (sectionsSubsemiring F).toSemiring
inferInstanceAs Semiring (Shrink (F ⋙ forget SemiRingCat).sections)

/--
Definition of `limitπRingHom` / `limitπRingHom` 的定义

English:
definition limitπRingHom
  signature: (j)
  body: let f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  let _ : Small.{u} (Functor.s

中文:
定义 limitπRingHom
  签名: (j)
  定义体: let f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  let _ : Small.{u} (Functor.s

Depends on / 依赖: AddCommMonCat, AddMonCat, AddMonCat.limit, Functor, Functor.sections, MonCat, MonCat.limit, SemiRingCat, forget, sections
-/
def limitπRingHom (j) :
    (Types.Small.limitCone.{v, u} (F ⋙ forget SemiRingCat)).pt ->+* (F ⋙ forget SemiRingCat).obj j :=
  let f : J ⥤ AddMonCat.{u} := F ⋙ forget₂ SemiRingCat.{u} AddCommMonCat.{u} ⋙
    forget₂ AddCommMonCat AddMonCat
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  let _ : Small.{u} (Functor.sections (f ⋙ forget AddMonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat.{u}))
  { AddMonCat.limitπAddMonoidHom f j,
    MonCat.limitπMonoidHom (F ⋙ forget₂ SemiRingCat MonCat.{u}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget SemiRingCat)).π.app j }

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits SemiRingCat`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F where
  body: SemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j => SemiRingCat.ofHom <| limitπRingHom.{v, u} F j
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

中文:
定义 limitCone
  签名: : 锥 F where
  定义体: SemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j => SemiRingCat.ofHom <| limitπRingHom.{v, u} F j
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

Depends on / 依赖: SemiRingCat, SemiRingCat.of, Types.Small.limitCone, forget, limitCone
-/
def limitCone : Cone F where
  pt := SemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j => SemiRingCat.ofHom <| limitπRingHom.{v, u} F j
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone F)
  body: by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ })
    (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl
  · simp
    rfl

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone F)
  定义体: by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ })
    (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl
  · simp
    rfl

Depends on / 依赖: IsLimit, IsLimit.ofFaithful, SemiRingCat, Types.Small.limitConeIsLimit, equivShrink_add, equivShrink_mul, forget, limitConeIsLimit, map_add, map_mul, map_one, map_zero, ofFaithful
-/
def limitConeIsLimit : IsLimit (limitCone F) := by
  refine IsLimit.ofFaithful (forget SemiRingCat.{u}) (Types.Small.limitConeIsLimit.{v, u} _)
    (fun s => ofHom { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ })
    (fun s => rfl)
  · simp
    rfl
  · intro x y
    simp [← equivShrink_mul]
    rfl
  · simp
    rfl
  · intro x y
    simp [← equivShrink_add]
    rfl

end HasLimits

open HasLimits

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

Depends on / 依赖: limitCone, limitConeIsLimit
-/
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J SemiRingCat.{u} where

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { }

中文:
实例 hasLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { }
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} SemiRingCat.{u} where
  has_limits_of_shape _ _ := { }

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits SemiRingCat.{u}
  body: SemiRingCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 Semi环范畴.{u}
  定义体: SemiRingCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: SemiRingCat, SemiRingCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits SemiRingCat.{u} :=
  SemiRingCat.hasLimitsOfSize.{u, u}

/--
Definition of `forget₂AddCommMonPreservesLimitsAux` / `forget₂AddCommMonPreservesLimitsAux` 的定义

English:
definition forget₂AddCommMonPreservesLimitsAux
  signature: :
  body: by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}

中文:
定义 forget₂AddCommMonPreservesLimitsAux
  签名: :
  定义体: by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}

Depends on / 依赖: AddCommMonCat, AddCommMonCat.limitConeIsLimit, Functor, Functor.sections, SemiRingCat, forget, limitConeIsLimit, sections
-/
def forget₂AddCommMonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat AddCommMonCat).mapCone (limitCone F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ AddCommMonCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply AddCommMonCat.limitConeIsLimit.{v, u}

/--
Instance `forget₂AddCommMon_preservesLimitsOfSize` / 实例 `forget₂AddCommMon_preservesLimitsOfSize`

English:
instance forget₂AddCommMon_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommMonPreservesLimitsAux F) }

中文:
实例 forget₂AddCommMon_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommMonPreservesLimitsAux F) }

Depends on / 依赖: limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂AddCommMon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat AddCommMonCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommMonPreservesLimitsAux F) }

/--
Instance `forget₂AddCommMon_preservesLimits` / 实例 `forget₂AddCommMon_preservesLimits`

English:
instance forget₂AddCommMon_preservesLimits
  signature: :
  body: SemiRingCat.forget₂AddCommMon_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂AddCommMon_preservesLimits
  签名: :
  定义体: SemiRingCat.forget₂AddCommMon_preservesLimitsOfSize.{u, u}

Depends on / 依赖: SemiRingCat, SemiRingCat.forget
-/
instance forget₂AddCommMon_preservesLimits :
    PreservesLimits (forget₂ SemiRingCat AddCommMonCat.{u}) :=
  SemiRingCat.forget₂AddCommMon_preservesLimitsOfSize.{u, u}

/--
Definition of `forget₂MonPreservesLimitsAux` / `forget₂MonPreservesLimitsAux` 的定义

English:
definition forget₂MonPreservesLimitsAux
  signature: :
  body: by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})

中文:
定义 forget₂MonPreservesLimitsAux
  签名: :
  定义体: by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})

Depends on / 依赖: Functor, Functor.sections, HasLimits, MonCat, MonCat.HasLimits.limitConeIsLimit, SemiRingCat, forget, limitConeIsLimit, sections
-/
def forget₂MonPreservesLimitsAux :
    IsLimit ((forget₂ SemiRingCat MonCat).mapCone (limitCone F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ MonCat) ⋙ forget MonCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget SemiRingCat))
  apply MonCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ SemiRingCat MonCat.{u})

/--
Instance `forget₂Mon_preservesLimitsOfSize` / 实例 `forget₂Mon_preservesLimitsOfSize`

English:
instance forget₂Mon_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forget₂MonPreservesLimitsAux.{v, u} F) }

中文:
实例 forget₂Mon_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forget₂MonPreservesLimitsAux.{v, u} F) }

Depends on / 依赖: limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂Mon_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ SemiRingCat MonCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (forget₂MonPreservesLimitsAux.{v, u} F) }

/--
Instance `forget₂Mon_preservesLimits` / 实例 `forget₂Mon_preservesLimits`

English:
instance forget₂Mon_preservesLimits
  signature: : PreservesLimits (forget₂ SemiRingCat MonCat.{u})
  body: SemiRingCat.forget₂Mon_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂Mon_preservesLimits
  签名: : PreservesLimits (forget₂ Semi环范畴 幺半群范畴.{u})
  定义体: SemiRingCat.forget₂Mon_preservesLimitsOfSize.{u, u}

Depends on / 依赖: SemiRingCat, SemiRingCat.forget
-/
instance forget₂Mon_preservesLimits : PreservesLimits (forget₂ SemiRingCat MonCat.{u}) :=
  SemiRingCat.forget₂Mon_preservesLimitsOfSize.{u, u}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (Types.Small.limitConeIsLimit.{v, u} (F ⋙ forget _)) }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (Types.Small.limitConeIsLimit.{v, u} (F ⋙ forget _)) }

Depends on / 依赖: Types.Small.limitConeIsLimit, forget, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
          (Types.Small.limitConeIsLimit.{v, u} (F ⋙ forget _)) }

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget SemiRingCat.{u})
  body: SemiRingCat.forget_preservesLimitsOfSize.{u, u}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget Semi环范畴.{u})
  定义体: SemiRingCat.forget_preservesLimitsOfSize.{u, u}

Depends on / 依赖: SemiRingCat, SemiRingCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget SemiRingCat.{u}) :=
  SemiRingCat.forget_preservesLimitsOfSize.{u, u}

end SemiRingCat

namespace CommSemiRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommSemiRingCat.{u})

/--
Instance `commSemiringObj` / 实例 `commSemiringObj`

English:
instance commSemiringObj
  signature: (j)
  body: inferInstanceAs CommSemiring (F.obj j)

中文:
实例 commSemiringObj
  签名: (j)
  定义体: inferInstanceAs CommSemiring (F.obj j)

Depends on / 依赖: CommSemiring, F.obj
-/
instance commSemiringObj (j) :
    CommSemiring ((F ⋙ forget CommSemiRingCat).obj j) :=
inferInstanceAs CommSemiring (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))]

/--
Instance `limitCommSemiring` / 实例 `limitCommSemiring`

English:
instance limitCommSemiring
  signature: :
  body: let _ : CommSemiring (F ⋙ forget CommSemiRingCat.{u}).sections :=
    @Subsemiring.toCommSemiring (forall j, F.obj j) _
      (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
inferInstanceAs CommSemiring (Shrink (F ⋙ forget CommSemiRingCat.{u}).sections)

中文:
实例 limitCommSemiring
  签名: :
  定义体: let _ : CommSemiring (F ⋙ forget CommSemiRingCat.{u}).sections :=
    @Subsemiring.toCommSemiring (forall j, F.obj j) _
      (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
inferInstanceAs CommSemiring (Shrink (F ⋙ forget CommSemiRingCat.{u}).sections)

Depends on / 依赖: CommSemiRingCat, CommSemiring, F.obj, SemiRingCat, SemiRingCat.sectionsSubsemiring, Shrink, Subsemiring, Subsemiring.toCommSemiring, forget, sections, sectionsSubsemiring, toCommSemiring
-/
instance limitCommSemiring :
    CommSemiring (Types.Small.limitCone.{v, u} (F ⋙ forget CommSemiRingCat.{u})).pt :=
  let _ : CommSemiring (F ⋙ forget CommSemiRingCat.{u}).sections :=
    @Subsemiring.toCommSemiring (forall j, F.obj j) _
      (SemiRingCat.sectionsSubsemiring.{v, u} (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))
inferInstanceAs CommSemiring (Shrink (F ⋙ forget CommSemiRingCat.{u}).sections)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: -- Porting note: Lean cannot see `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism, so this
  -- instance is added.
  let _ : (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCat.{u} SemiRingCat.{u}
  let _ : Small.{

中文:
实例 :
  定义体: -- Porting note: Lean cannot see `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism, so this
  -- instance is added.
  let _ : (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCat.{u} SemiRingCat.{u}
  let _ : Small.{
-/
instance :
    CreatesLimit F (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) :=
  -- Porting note: Lean cannot see `CommSemiRingCat ⥤ SemiRingCat` reflects isomorphism, so this
  -- instance is added.
  let _ : (forget₂ CommSemiRingCat.{u} SemiRingCat.{u}).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ CommSemiRingCat.{u} SemiRingCat.{u}
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget CommSemiRingCat))
  let c : Cone F :=
    { pt := CommSemiRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun j => CommSemiRingCat.ofHom <| SemiRingCat.limitπRingHom.{v, u} (J := J)
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}) j
naturality := fun _ _ f => hom_ext congrArg SemiRingCat.Hom.hom
            (SemiRingCat.HasLimits.limitCone.{v, u}
            (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u})).π.naturality f } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) t
      makesLimit := by
        refine IsLimit.ofFaithful (forget₂ CommSemiRingCat.{u} SemiRingCat.{u})
          (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) (fun s => _) fun s => rfl }

/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))

中文:
定义 limitCone
  签名: : 锥 F
  定义体: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))

Depends on / 依赖: CommSemiRingCat, Functor, Functor.sections, SemiRingCat, forget, isLimit, liftLimit, limit.isLimit, sections
-/
def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat.{u}) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommSemiRingCat.{u} SemiRingCat.{u}))

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
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

Depends on / 依赖: limitCone, limitConeIsLimit
-/
instance hasLimit : HasLimit F := ⟨limitCone.{v, u} F, limitConeIsLimit.{v, u} F⟩

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommSemiRingCat.{u} where

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [UnivLE.{v, u}]

中文:
实例 hasLimitsOfSize
  签名: [UnivLE.{v, u}]
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommSemiRingCat.{u} where

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits CommSemiRingCat.{u}
  body: CommSemiRingCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 交换Semi环范畴.{u}
  定义体: CommSemiRingCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: CommSemiRingCat, CommSemiRingCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits CommSemiRingCat.{u} :=
  CommSemiRingCat.hasLimitsOfSize.{u, u}

/--
Instance `forget₂SemiRing_preservesLimitsOfSize` / 实例 `forget₂SemiRing_preservesLimitsOfSize`

English:
instance forget₂SemiRing_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ _ SemiRingCat)) }

中文:
实例 forget₂SemiRing_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ _ SemiRingCat)) }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, HasLimits, MonCat, SemiRingCat, SemiRingCat.HasLimits.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂SemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommSemiRingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (SemiRingCat.HasLimits.limitConeIsLimit (F ⋙ forget₂ _ SemiRingCat)) }

/--
Instance `forget₂SemiRing_preservesLimits` / 实例 `forget₂SemiRing_preservesLimits`

English:
instance forget₂SemiRing_preservesLimits
  signature: :
  body: CommSemiRingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂SemiRing_preservesLimits
  签名: :
  定义体: CommSemiRingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommSemiRingCat, CommSemiRingCat.forget
-/
instance forget₂SemiRing_preservesLimits :
    PreservesLimits (forget₂ CommSemiRingCat SemiRingCat.{u}) :=
  CommSemiRingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

Depends on / 依赖: Types.Small.limitConeIsLimit, f.hom, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget CommSemiRingCat.{u})
  body: CommSemiRingCat.forget_preservesLimitsOfSize.{u, u}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 交换Semi环范畴.{u})
  定义体: CommSemiRingCat.forget_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommSemiRingCat, CommSemiRingCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget CommSemiRingCat.{u}) :=
  CommSemiRingCat.forget_preservesLimitsOfSize.{u, u}

end CommSemiRingCat

namespace RingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ RingCat.{u})

/--
Instance `ringObj` / 实例 `ringObj`

English:
instance ringObj
  signature: (j)
  body: inferInstanceAs Ring (F.obj j)

中文:
实例 ringObj
  签名: (j)
  定义体: inferInstanceAs Ring (F.obj j)

Depends on / 依赖: F.obj
-/
instance ringObj (j) : Ring ((F ⋙ forget RingCat).obj j) :=
inferInstanceAs Ring (F.obj j)

/--
Definition of `sectionsSubring` / `sectionsSubring` 的定义

English:
definition sectionsSubring
  signature: : Subring (forall j, F.obj j)
  body: let f : J ⥤ AddGrpCat.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙
    forget₂ AddCommGrpCat.{u} AddGrpCat.{u}
  let g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrpCat.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carr

中文:
定义 sectionsSubring
  签名: : 子环 (对任意 j, F.obj j)
  定义体: let f : J ⥤ AddGrpCat.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙
    forget₂ AddCommGrpCat.{u} AddGrpCat.{u}
  let g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrpCat.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carr

Depends on / 依赖: AddCommGrpCat, AddGrpCat, AddGrpCat.sectionsAddSubgroup, RingCat, SemiRingCat, SemiRingCat.sectionsSubsemiring, carrier, forget, sections, sectionsAddSubgroup, sectionsSubsemiring
-/
def sectionsSubring : Subring (forall j, F.obj j) :=
  let f : J ⥤ AddGrpCat.{u} :=
    F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙
    forget₂ AddCommGrpCat.{u} AddGrpCat.{u}
  let g : J ⥤ SemiRingCat.{u} := F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
  { AddGrpCat.sectionsAddSubgroup (J := J) f,
    SemiRingCat.sectionsSubsemiring (J := J) g with
    carrier := (F ⋙ forget RingCat.{u}).sections }

variable [Small.{u} (Functor.sections (F ⋙ forget RingCat.{u}))]

/--
Instance `limitRing` / 实例 `limitRing`

English:
instance limitRing
  signature: : Ring.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget RingCat.{u})).pt
  body: let _ : Ring (F ⋙ forget RingCat.{u}).sections := (sectionsSubring F).toRing
inferInstanceAs Ring (Shrink _)

中文:
实例 limitRing
  签名: : 环.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget 环范畴.{u})).pt
  定义体: let _ : Ring (F ⋙ forget RingCat.{u}).sections := (sectionsSubring F).toRing
inferInstanceAs Ring (Shrink _)

Depends on / 依赖: RingCat, Shrink, forget, sections, sectionsSubring, toRing
-/
instance limitRing : Ring.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget RingCat.{u})).pt :=
  let _ : Ring (F ⋙ forget RingCat.{u}).sections := (sectionsSubring F).toRing
inferInstanceAs Ring (Shrink _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimit F (forget₂ RingCat.{u} SemiRingCat.{u})
  body: have : (forget₂ RingCat SemiRingCat).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  have : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  let c : Cone F :=
  { pt := RingCat.of (Typ

中文:
实例 :
  签名: 创造极限 F (forget₂ 环范畴.{u} Semi环范畴.{u})
  定义体: have : (forget₂ RingCat SemiRingCat).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  have : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  let c : Cone F :=
  { pt := RingCat.of (Typ

Depends on / 依赖: CategoryTheory, CategoryTheory.reflectsIsomorphisms_forget, Functor, Functor.sections, ReflectsIsomorphisms, RingCat, RingCat.of, SemiRingCat, SemiRingCat.limit, Types.Small.limitCone, forget, limitCone, naturality, sections
-/
instance : CreatesLimit F (forget₂ RingCat.{u} SemiRingCat.{u}) :=
  have : (forget₂ RingCat SemiRingCat).ReflectsIsomorphisms :=
    CategoryTheory.reflectsIsomorphisms_forget₂ _ _
  have : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  let c : Cone F :=
  { pt := RingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
    π :=
      { app := fun x => ofHom <| SemiRingCat.limitπRingHom.{v, u} (F ⋙ forget₂ _ SemiRingCat) x
        naturality _ _ f := by
          ext
          simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ } }
  createsLimitOfReflectsIso fun c' t =>
    { liftedCone := c
      validLift := by apply IsLimit.uniqueUpToIso (SemiRingCat.HasLimits.limitConeIsLimit _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ RingCat SemiRingCat.{u})
          (by apply SemiRingCat.HasLimits.limitConeIsLimit _) (fun _ => _) fun _ => rfl }

/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))

中文:
定义 limitCone
  签名: : 锥 F
  定义体: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))

Depends on / 依赖: Functor, Functor.sections, RingCat, SemiRingCat, forget, isLimit, liftLimit, limit.isLimit, sections
-/
def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ RingCat.{u} SemiRingCat.{u}))

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
def limitConeIsLimit : IsLimit (limitCone F) :=
  liftedLimitIsLimit _

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ RingCat.{u} SemiRingCat.{u})

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ RingCat.{u} SemiRingCat.{u})

Depends on / 依赖: Functor, Functor.sections, RingCat, SemiRingCat, forget, hasLimit_of_created, sections
-/
instance hasLimit : HasLimit F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ RingCat.{u} SemiRingCat.{u})

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J RingCat.{u} where

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [UnivLE.{v, u}]

中文:
实例 hasLimitsOfSize
  签名: [UnivLE.{v, u}]
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} RingCat.{u} where

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits RingCat.{u}
  body: RingCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 环范畴.{u}
  定义体: RingCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: RingCat, RingCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits RingCat.{u} :=
  RingCat.hasLimitsOfSize.{u, u}

/--
Instance `forget₂SemiRing_preservesLimitsOfSize` / 实例 `forget₂SemiRing_preservesLimitsOfSize`

English:
instance forget₂SemiRing_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
          preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
            (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) }

中文:
实例 forget₂SemiRing_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
          preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
            (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) }

Depends on / 依赖: HasLimits, SemiRingCat, SemiRingCat.HasLimits.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂SemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ RingCat SemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
      { preservesLimit := fun {F} =>
          preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
            (SemiRingCat.HasLimits.limitConeIsLimit.{v, u} _) }

/--
Instance `forget₂SemiRing_preservesLimits` / 实例 `forget₂SemiRing_preservesLimits`

English:
instance forget₂SemiRing_preservesLimits
  signature: : PreservesLimits (forget₂ RingCat SemiRingCat.{u})
  body: RingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂SemiRing_preservesLimits
  签名: : PreservesLimits (forget₂ 环范畴 Semi环范畴.{u})
  定义体: RingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

Depends on / 依赖: RingCat, RingCat.forget
-/
instance forget₂SemiRing_preservesLimits : PreservesLimits (forget₂ RingCat SemiRingCat.{u}) :=
  RingCat.forget₂SemiRing_preservesLimitsOfSize.{u, u}

/--
Definition of `forget₂AddCommGroupPreservesLimitsAux` / `forget₂AddCommGroupPreservesLimitsAux` 的定义

English:
definition forget₂AddCommGroupPreservesLimitsAux
  signature: :
  body: by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrpCat.limitConeIsLimit.{v, u} _

中文:
定义 forget₂AddCommGroupPreservesLimitsAux
  签名: :
  定义体: by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrpCat.limitConeIsLimit.{v, u} _

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.limitConeIsLimit, Functor, Functor.sections, RingCat, forget, limitConeIsLimit, sections
-/
def forget₂AddCommGroupPreservesLimitsAux :
    IsLimit ((forget₂ RingCat.{u} AddCommGrpCat).mapCone (limitCone.{v, u} F)) := by
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙ forget _)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  apply AddCommGrpCat.limitConeIsLimit.{v, u} _

/--
Instance `forget₂AddCommGroup_preservesLimitsOfSize` / 实例 `forget₂AddCommGroup_preservesLimitsOfSize`

English:
instance forget₂AddCommGroup_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }

中文:
实例 forget₂AddCommGroup_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }

Depends on / 依赖: limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget₂ RingCat.{u} AddCommGrpCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂AddCommGroupPreservesLimitsAux F) }

/--
Instance `forget₂AddCommGroup_preservesLimits` / 实例 `forget₂AddCommGroup_preservesLimits`

English:
instance forget₂AddCommGroup_preservesLimits
  signature: :
  body: RingCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂AddCommGroup_preservesLimits
  签名: :
  定义体: RingCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u}

Depends on / 依赖: RingCat, RingCat.forget
-/
instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ RingCat AddCommGrpCat.{u}) :=
  RingCat.forget₂AddCommGroup_preservesLimitsOfSize.{u, u}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

Depends on / 依赖: Types.Small.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{v, v} (forget RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget RingCat.{u})
  body: RingCat.forget_preservesLimitsOfSize.{u, u}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 环范畴.{u})
  定义体: RingCat.forget_preservesLimitsOfSize.{u, u}

Depends on / 依赖: RingCat, RingCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget RingCat.{u}) :=
  RingCat.forget_preservesLimitsOfSize.{u, u}

end RingCat

namespace CommRingCat

variable {J : Type v} [Category.{w} J] (F : J ⥤ CommRingCat.{u})

/--
Instance `commRingObj` / 实例 `commRingObj`

English:
instance commRingObj
  signature: (j)
  body: inferInstanceAs CommRing (F.obj j)

中文:
实例 commRingObj
  签名: (j)
  定义体: inferInstanceAs CommRing (F.obj j)

Depends on / 依赖: CommRing, F.obj
-/
instance commRingObj (j) : CommRing ((F ⋙ forget CommRingCat).obj j) :=
inferInstanceAs CommRing (F.obj j)

variable [Small.{u} (Functor.sections (F ⋙ forget CommRingCat))]

/--
Instance `limitCommRing` / 实例 `limitCommRing`

English:
instance limitCommRing
  signature: :
  body: let _ : CommRing (F ⋙ forget CommRingCat).sections := @Subring.toCommRing (forall j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))
inferInstanceAs CommRing (Shrink _)

中文:
实例 limitCommRing
  签名: :
  定义体: let _ : CommRing (F ⋙ forget CommRingCat).sections := @Subring.toCommRing (forall j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))
inferInstanceAs CommRing (Shrink _)

Depends on / 依赖: CommRing, CommRingCat, F.obj, RingCat, RingCat.sectionsSubring, Shrink, Subring, Subring.toCommRing, forget, sections, sectionsSubring, toCommRing
-/
instance limitCommRing :
    CommRing.{u} (Types.Small.limitCone.{v, u} (F ⋙ forget CommRingCat.{u})).pt :=
  let _ : CommRing (F ⋙ forget CommRingCat).sections := @Subring.toCommRing (forall j, F.obj j) _
    (RingCat.sectionsSubring.{v, u} (F ⋙ forget₂ CommRingCat RingCat.{u}))
inferInstanceAs CommRing (Shrink _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimit F (forget₂ CommRingCat.{u} RingCat.{u})
  body: /-
    A terse solution here would be
    ```
    createsLimitOfFullyFaithfulOfIso (CommRingCat.of (limit (F ⋙ forget _))) (Iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    -- Porting note: need to add these instances manually
    have 

中文:
实例 :
  签名: 创造极限 F (forget₂ 交换环范畴.{u} 环范畴.{u})
  定义体: /-
    A terse solution here would be
    ```
    createsLimitOfFullyFaithfulOfIso (CommRingCat.of (limit (F ⋙ forget _))) (Iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    -- Porting note: need to add these instances manually
    have 
-/
instance : CreatesLimit F (forget₂ CommRingCat.{u} RingCat.{u}) :=
  /-
    A terse solution here would be
    ```
    createsLimitOfFullyFaithfulOfIso (CommRingCat.of (limit (F ⋙ forget _))) (Iso.refl _)
    ```
    but it seems this would introduce additional identity morphisms in `limit.π`.
    -/
    -- Porting note: need to add these instances manually
    have : (forget₂ CommRingCat.{u} RingCat.{u}).ReflectsIsomorphisms :=
      CategoryTheory.reflectsIsomorphisms_forget₂ _ _
    have : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
    let F' := F ⋙ forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} SemiRingCat.{u}
    have : Small.{u} (Functor.sections (F' ⋙ forget _)) :=
inferInstanceAs Small.{u} (F ⋙ forget _).sections
    let c : Cone F :=
    { pt := CommRingCat.of (Types.Small.limitCone (F ⋙ forget _)).pt
      π :=
        { app := fun x => ofHom <| SemiRingCat.limitπRingHom.{v, u} F' x
          naturality _ _ f := by
            ext
            simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ } }
    createsLimitOfReflectsIso fun _ t =>
    { liftedCone := c
      validLift := IsLimit.uniqueUpToIso (RingCat.limitConeIsLimit.{v, u} _) t
      makesLimit :=
        IsLimit.ofFaithful (forget₂ _ RingCat.{u})
          (RingCat.limitConeIsLimit.{v, u} (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
          (fun s : Cone F => CommRingCat.ofHom <|
              (RingCat.limitConeIsLimit.{v, u}
                (F ⋙ forget₂ CommRingCat.{u} RingCat.{u})).lift
.hom) fun _ => rfl } ((forget₂ _ RingCat.{u}).mapCone s)

/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F
  body: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

中文:
定义 limitCone
  签名: : 锥 F
  定义体: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

Depends on / 依赖: CommRingCat, Functor, Functor.sections, RingCat, forget, isLimit, liftLimit, limit.isLimit, sections
-/
def limitCone : Cone F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  liftLimit (limit.isLimit (F ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

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
def limitConeIsLimit : IsLimit (limitCone.{v, u} F) :=
  liftedLimitIsLimit _

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: : HasLimit F
  body: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ CommRingCat.{u} RingCat.{u})

中文:
实例 hasLimit
  签名: : 有极限 F
  定义体: let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ CommRingCat.{u} RingCat.{u})

Depends on / 依赖: CommRingCat, Functor, Functor.sections, RingCat, forget, hasLimit_of_created, sections
-/
instance hasLimit : HasLimit F :=
  let _ : Small.{u} (Functor.sections ((F ⋙ forget₂ CommRingCat RingCat) ⋙ forget RingCat)) :=
inferInstanceAs Small.{u} (Functor.sections (F ⋙ forget _))
  hasLimit_of_created F (forget₂ CommRingCat.{u} RingCat.{u})

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J CommRingCat.{u} where

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [UnivLE.{v, u}]

中文:
实例 hasLimitsOfSize
  签名: [UnivLE.{v, u}]
-/
instance hasLimitsOfSize [UnivLE.{v, u}] : HasLimitsOfSize.{w, v} CommRingCat.{u} where

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits CommRingCat.{u}
  body: CommRingCat.hasLimitsOfSize.{u, u}

中文:
实例 hasLimits
  签名: : 有极限 交换环范畴.{u}
  定义体: CommRingCat.hasLimitsOfSize.{u, u}

Depends on / 依赖: CommRingCat, CommRingCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits CommRingCat.{u} :=
  CommRingCat.hasLimitsOfSize.{u, u}

/--
Instance `forget₂Ring_preservesLimitsOfSize` / 实例 `forget₂Ring_preservesLimitsOfSize`

English:
instance forget₂Ring_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }

中文:
实例 forget₂Ring_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }

Depends on / 依赖: RingCat, RingCat.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat RingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (RingCat.limitConeIsLimit.{v, u} _) }

/--
Instance `forget₂Ring_preservesLimits` / 实例 `forget₂Ring_preservesLimits`

English:
instance forget₂Ring_preservesLimits
  signature: : PreservesLimits (forget₂ CommRingCat RingCat.{u})
  body: CommRingCat.forget₂Ring_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂Ring_preservesLimits
  签名: : PreservesLimits (forget₂ 交换环范畴 环范畴.{u})
  定义体: CommRingCat.forget₂Ring_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommMonCat, CommRingCat, CommRingCat.forget, ConcreteCategory, ConcreteCategory.hom
-/
instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ CommRingCat RingCat.{u}) :=
  CommRingCat.forget₂Ring_preservesLimitsOfSize.{u, u}

/--
Definition of `forget₂CommSemiRingPreservesLimitsAux` / `forget₂CommSemiRingPreservesLimitsAux` 的定义

English:
definition forget₂CommSemiRingPreservesLimitsAux
  signature: :
  body: by
  let _ : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
inferInstanceAs Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})

中文:
定义 forget₂CommSemiRingPreservesLimitsAux
  签名: :
  定义体: by
  let _ : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
inferInstanceAs Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})

Depends on / 依赖: CommRingCat, CommSemiRingCat, CommSemiRingCat.limitConeIsLimit, forget, limitConeIsLimit, sections
-/
def forget₂CommSemiRingPreservesLimitsAux :
    IsLimit ((forget₂ CommRingCat CommSemiRingCat).mapCone (limitCone F)) := by
  let _ : Small.{u} ((F ⋙ forget₂ _ CommSemiRingCat) ⋙ forget _).sections :=
inferInstanceAs Small.{u} (F ⋙ forget _).sections
  apply CommSemiRingCat.limitConeIsLimit (F ⋙ forget₂ CommRingCat CommSemiRingCat.{u})

/--
Instance `forget₂CommSemiRing_preservesLimitsOfSize` / 实例 `forget₂CommSemiRing_preservesLimitsOfSize`

English:
instance forget₂CommSemiRing_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂CommSemiRingPreservesLimitsAux.{v, u} F) }

中文:
实例 forget₂CommSemiRing_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂CommSemiRingPreservesLimitsAux.{v, u} F) }

Depends on / 依赖: f.hom, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂CommSemiRing_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget₂ CommRingCat CommSemiRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit.{v, u} F)
          (forget₂CommSemiRingPreservesLimitsAux.{v, u} F) }

/--
Instance `forget₂CommSemiRing_preservesLimits` / 实例 `forget₂CommSemiRing_preservesLimits`

English:
instance forget₂CommSemiRing_preservesLimits
  signature: :
  body: CommRingCat.forget₂CommSemiRing_preservesLimitsOfSize.{u, u}

中文:
实例 forget₂CommSemiRing_preservesLimits
  签名: :
  定义体: CommRingCat.forget₂CommSemiRing_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommRingCat, CommRingCat.forget
-/
instance forget₂CommSemiRing_preservesLimits :
    PreservesLimits (forget₂ CommRingCat CommSemiRingCat.{u}) :=
  CommRingCat.forget₂CommSemiRing_preservesLimitsOfSize.{u, u}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, u}]
  body: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, u}]
  定义体: { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

Depends on / 依赖: Types.Small.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, u}] :
    PreservesLimitsOfSize.{w, v} (forget CommRingCat.{u}) where
  preservesLimitsOfShape {_ _} :=
    { preservesLimit := fun {F} =>
        preservesLimit_of_preserves_limit_cone.{w, v} (limitConeIsLimit.{v, u} F)
          (Types.Small.limitConeIsLimit.{v, u} _) }

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget CommRingCat.{u})
  body: CommRingCat.forget_preservesLimitsOfSize.{u, u}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget 交换环范畴.{u})
  定义体: CommRingCat.forget_preservesLimitsOfSize.{u, u}

Depends on / 依赖: CommRingCat, CommRingCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget CommRingCat.{u}) :=
  CommRingCat.forget_preservesLimitsOfSize.{u, u}

end CommRingCat
