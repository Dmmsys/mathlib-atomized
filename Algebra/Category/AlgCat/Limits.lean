/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# The category of R-algebras has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


open CategoryTheory Limits

universe v w u t

-- `u` is determined by the ring, so can come later
noncomputable section

namespace AlgCat

variable {R : Type u} [CommRing R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ AlgCat.{w} R)

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
instance semiringObj (j) : Semiring ((F ⋙ forget (AlgCat R)).obj j) :=
inferInstanceAs Semiring (F.obj j)

/--
Instance `algebraObj` / 实例 `algebraObj`

English:
instance algebraObj
  signature: (j)
  body: inferInstanceAs Algebra R (F.obj j)

中文:
实例 algebraObj
  签名: (j)
  定义体: inferInstanceAs Algebra R (F.obj j)

Depends on / 依赖: Algebra, F.obj
-/
instance algebraObj (j) :
    Algebra R ((F ⋙ forget (AlgCat R)).obj j) :=
inferInstanceAs Algebra R (F.obj j)

/--
Definition of `sectionsSubalgebra` / `sectionsSubalgebra` 的定义

English:
definition sectionsSubalgebra
  signature: : Subalgebra R (forall j, F.obj j)
  body: { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }

中文:
定义 sectionsSubalgebra
  签名: : 子代数 R (对任意 j, F.obj j)
  定义体: { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }

Depends on / 依赖: AlgCat, F.map, RingCat, SemiRingCat, SemiRingCat.sectionsSubsemiring, algebraMap_mem, commutes, hom.commutes, sectionsSubsemiring
-/
def sectionsSubalgebra : Subalgebra R (forall j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }

instance (F : J ⥤ AlgCat.{w} R) : Ring (F ⋙ forget _).sections :=
inferInstanceAs Ring (sectionsSubalgebra F)

instance (F : J ⥤ AlgCat.{w} R) : Algebra R (F ⋙ forget _).sections :=
inferInstanceAs Algebra R (sectionsSubalgebra F)

variable [Small.{w} (F ⋙ forget (AlgCat.{w} R)).sections]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{w} (sectionsSubalgebra F)
  body: inferInstanceAs Small.{w} (F ⋙ forget _).sections

中文:
实例 :
  签名: Small.{w} (sectionsSubalgebra F)
  定义体: inferInstanceAs Small.{w} (F ⋙ forget _).sections

Depends on / 依赖: forget, sections
-/
instance : Small.{w} (sectionsSubalgebra F) :=
inferInstanceAs Small.{w} (F ⋙ forget _).sections

/--
Instance `limitSemiring` / 实例 `limitSemiring`

English:
instance limitSemiring
  signature: :
  body: inferInstanceAs Ring (Shrink (sectionsSubalgebra F))

中文:
实例 limitSemiring
  签名: :
  定义体: inferInstanceAs Ring (Shrink (sectionsSubalgebra F))

Depends on / 依赖: Shrink, sectionsSubalgebra
-/
instance limitSemiring :
    Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgCat.{w} R))).pt :=
inferInstanceAs Ring (Shrink (sectionsSubalgebra F))

/--
Instance `limitAlgebra` / 实例 `limitAlgebra`

English:
instance limitAlgebra
  signature: :
  body: inferInstanceAs Algebra R (Shrink (sectionsSubalgebra F))

中文:
实例 limitAlgebra
  签名: :
  定义体: inferInstanceAs Algebra R (Shrink (sectionsSubalgebra F))

Depends on / 依赖: Algebra, Shrink, sectionsSubalgebra
-/
instance limitAlgebra :
    Algebra R (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).pt :=
inferInstanceAs Algebra R (Shrink (sectionsSubalgebra F))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitπAlgHom` / `limitπAlgHom` 的定义

English:
definition limitπAlgHom
  signature: (j)
  body: letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limi

中文:
定义 limitπAlgHom
  签名: (j)
  定义体: letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limi

Depends on / 依赖: AlgCat, ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.comp_obj, Functor.const_obj_obj, Functor.sections, RingCat, SemiRingCat, SemiRingCat.limit, TypeCat, TypeCat.Fun.coe, Types.Small.limitCone, Types.Small.limitCone_, Types.Small.limitCone_pt, commutes, comp_obj, const_obj_obj, forget, hom_ofHom
-/
def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgCat R))).pt ->ₐ[R]
      (F ⋙ forget (AlgCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
inferInstanceAs Small.{w} (F ⋙ forget _).sections
  { SemiRingCat.limitπRingHom
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) j with
    toFun := (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).π.app j
    commutes' := fun x => by
      simp only [Functor.comp_obj, Types.Small.limitCone_pt, Functor.const_obj_obj,
        Types.Small.limitCone_π_app, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk,
        ← Shrink.algEquiv_apply R, AlgEquiv.commutes]
      rfl
    }

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (AlgCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F where
  body: AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j => ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

中文:
定义 limitCone
  签名: : 锥 F where
  定义体: AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j => ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

Depends on / 依赖: AlgCat, AlgCat.of, Types.Small.limitCone, forget, limitCone
-/
def limitCone : Cone F where
  pt := AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j => ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone.{v, w} F)
  body: by
  refine
    IsLimit.ofFaithful (forget (AlgCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp
  · intro x y
   

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone.{v, w} F)
  定义体: by
  refine
    IsLimit.ofFaithful (forget (AlgCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp
  · intro x y
   

Depends on / 依赖: AlgCat, Equiv.algebraMap_def, Equiv.symm_symm, IsLimit, IsLimit.ofFaithful, Subtype, Subtype.ext, Types.Small.limitConeIsLimit, algebraMap_def, commutes, forget, hom.commutes, limitConeIsLimit, map_add, map_mul, map_one, map_zero, ofFaithful, symm_symm
-/
def limitConeIsLimit : IsLimit (limitCone.{v, w} F) := by
  refine
    IsLimit.ofFaithful (forget (AlgCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
      (fun s => ofHom
        { toFun := _, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_,
          commutes' := ?_ })
      (fun s => rfl)
  · congr
    ext j
    simp
  · intro x y
    ext j
    simp
    rfl
  · ext j
    simp
    rfl
  · intro x y
    ext j
    simp
    rfl
  · intro r
    simp only [Equiv.algebraMap_def, Equiv.symm_symm]
    apply congrArg
    apply Subtype.ext
    ext j
    exact (s.π.app j).hom.commutes r

end HasLimits

open HasLimits

/--
lemma `hasLimitsOfSize` / 引理 `hasLimitsOfSize`

English:
lemma hasLimitsOfSize
  given: [UnivLE.{v, w}]
  statement: HasLimitsOfSize.{t, v} (AlgCat.{w} R)
  proof: { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

中文:
引理 hasLimitsOfSize
  条件: [UnivLE.{v, w}]
  结论: 有LimitsOfSize.{t, v} (Alg范畴.{w} R)
  证明: { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

Depends on / 依赖: HasLimit, HasLimit.mk, has_limit, has_limits_of_shape, isLimit, limitCone, limitConeIsLimit
-/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits (AlgCat.{w} R)
  body: AlgCat.hasLimitsOfSize.{w, w, u}

中文:
实例 hasLimits
  签名: : 有极限 (Alg范畴.{w} R)
  定义体: AlgCat.hasLimitsOfSize.{w, w, u}

Depends on / 依赖: AlgCat, AlgCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits (AlgCat.{w} R) :=
  AlgCat.hasLimitsOfSize.{w, w, u}

/--
Instance `forget₂Ring_preservesLimitsOfSize` / 实例 `forget₂Ring_preservesLimitsOfSize`

English:
instance forget₂Ring_preservesLimitsOfSize
  signature: [UnivLE.{v, w}]
  body: { preservesLimit := fun {K} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgCat.{w} R) RingCat.{w})) }

中文:
实例 forget₂Ring_preservesLimitsOfSize
  签名: [UnivLE.{v, w}]
  定义体: { preservesLimit := fun {K} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgCat.{w} R) RingCat.{w})) }

Depends on / 依赖: AlgCat, RingCat, RingCat.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget₂ (AlgCat.{w} R) RingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgCat.{w} R) RingCat.{w})) }

/--
Instance `forget₂Ring_preservesLimits` / 实例 `forget₂Ring_preservesLimits`

English:
instance forget₂Ring_preservesLimits
  signature: : PreservesLimits (forget₂ (AlgCat R) RingCat.{w})
  body: AlgCat.forget₂Ring_preservesLimitsOfSize.{w, w}

中文:
实例 forget₂Ring_preservesLimits
  签名: : PreservesLimits (forget₂ (Alg范畴 R) 环范畴.{w})
  定义体: AlgCat.forget₂Ring_preservesLimitsOfSize.{w, w}

Depends on / 依赖: AlgCat, AlgCat.forget
-/
instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ (AlgCat R) RingCat.{w}) :=
  AlgCat.forget₂Ring_preservesLimitsOfSize.{w, w}

/--
Instance `forget₂Module_preservesLimitsOfSize` / 实例 `forget₂Module_preservesLimitsOfSize`

English:
instance forget₂Module_preservesLimitsOfSize
  signature: [UnivLE.{v, w}]
  body: { preservesLimit := fun {K} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) }

中文:
实例 forget₂Module_preservesLimitsOfSize
  签名: [UnivLE.{v, w}]
  定义体: { preservesLimit := fun {K} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) }

Depends on / 依赖: AlgCat, HasLimits, ModuleCat, ModuleCat.HasLimits.limitConeIsLimit, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂Module_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v}
    (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} =>
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) }

/--
Instance `forget₂Module_preservesLimits` / 实例 `forget₂Module_preservesLimits`

English:
instance forget₂Module_preservesLimits
  signature: :
  body: AlgCat.forget₂Module_preservesLimitsOfSize.{w, w}

中文:
实例 forget₂Module_preservesLimits
  签名: :
  定义体: AlgCat.forget₂Module_preservesLimitsOfSize.{w, w}

Depends on / 依赖: AlgCat, AlgCat.forget
-/
instance forget₂Module_preservesLimits :
    PreservesLimits (forget₂ (AlgCat R) (ModuleCat.{w} R)) :=
  AlgCat.forget₂Module_preservesLimitsOfSize.{w, w}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, w}]
  body: { preservesLimit := fun {K} =>
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, w}]
  定义体: { preservesLimit := fun {K} =>
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }

Depends on / 依赖: Types.Small.limitConeIsLimit, forget, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (AlgCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} =>
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget (AlgCat.{w} R))
  body: AlgCat.forget_preservesLimitsOfSize.{w, w}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget (Alg范畴.{w} R))
  定义体: AlgCat.forget_preservesLimitsOfSize.{w, w}

Depends on / 依赖: AlgCat, AlgCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize
-/
instance forget_preservesLimits : PreservesLimits (forget (AlgCat.{w} R)) :=
  AlgCat.forget_preservesLimitsOfSize.{w, w}

end AlgCat
