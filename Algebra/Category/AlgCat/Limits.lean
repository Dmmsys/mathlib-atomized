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

/-
**AlgCat.semiringObj** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：semiringObj (j) : Semiring ((F ⋙ forget (AlgCat R)).obj j)
参数：j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiringObj (j) : Semiring ((F ⋙ forget (AlgCat R)).obj j) :=
  inferInstanceAs <| Semiring (F.obj j)
/-
**AlgCat.algebraObj** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：algebraObj (j) : Algebra R ((F ⋙ forget (AlgCat R)).obj j)
参数：j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraObj (j) :
    Algebra R ((F ⋙ forget (AlgCat R)).obj j) :=
  inferInstanceAs <| Algebra R (F.obj j)

/-- The flat sections of a functor into `AlgCat R` form a submodule of all sections.
-/
/-
**AlgCat.sectionsSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
形式化陈述：sectionsSubalgebra : Subalgebra R (forall j, F.obj j)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The flat sections of a functor into `AlgCat R` form a submodule of all sections.
-/
def sectionsSubalgebra : Subalgebra R (∀ j, F.obj j) :=
  { SemiRingCat.sectionsSubsemiring
      (F ⋙ forget₂ (AlgCat R) RingCat.{w} ⋙ forget₂ RingCat SemiRingCat.{w}) with
    algebraMap_mem' := fun r _ _ f => (F.map f).hom.commutes r }
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : J ⥤ AlgCat.{w} R) : Ring (F ⋙ forget _).sections :=
  inferInstanceAs <| Ring (sectionsSubalgebra F)
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : J ⥤ AlgCat.{w} R) : Algebra R (F ⋙ forget _).sections :=
  inferInstanceAs <| Algebra R (sectionsSubalgebra F)

variable [Small.{w} (F ⋙ forget (AlgCat.{w} R)).sections]
/-
**AlgCat.** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Small.{w} (sectionsSubalgebra F) :=
  inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
/-
**AlgCat.limitSemiring** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：limitSemiring : Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgCat
.{w} R))).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance limitSemiring :
    Ring.{w} (Types.Small.limitCone.{v, w} (F ⋙ forget (AlgCat.{w} R))).pt :=
  inferInstanceAs <| Ring (Shrink (sectionsSubalgebra F))
/-
**AlgCat.limitAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：limitAlgebra : Algebra R (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R)
)).pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance limitAlgebra :
    Algebra R (Types.Small.limitCone (F ⋙ forget (AlgCat.{w} R))).pt :=
  inferInstanceAs <| Algebra R (Shrink (sectionsSubalgebra F))

set_option backward.isDefEq.respectTransparency false in
/-- `limit.π (F ⋙ forget (AlgCat R)) j` as an `AlgHom`. -/
/-
**AlgCat.limit** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limit.π (F ⋙ forget (AlgCat R)) j` as an `AlgHom`.
-/
def limitπAlgHom (j) :
    (Types.Small.limitCone (F ⋙ forget (AlgCat R))).pt →ₐ[R]
      (F ⋙ forget (AlgCat.{w} R)).obj j :=
  letI : Small.{w}
      (Functor.sections ((F ⋙ forget₂ _ RingCat ⋙ forget₂ _ SemiRingCat) ⋙ forget _)) :=
    inferInstanceAs <| Small.{w} (F ⋙ forget _).sections
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
/-- Construction of a limit cone in `AlgCat R`.
(Internal use only; use the limits API.)
-/
/-
**AlgCat.HasLimits.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat.HasLimits`。
形式化陈述：limitCone : Cone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construction of a limit cone in `AlgCat R`.
(Internal use only; use the limits API.)
-/
def limitCone : Cone F where
  pt := AlgCat.of R (Types.Small.limitCone (F ⋙ forget _)).pt
  π :=
    { app := fun j ↦ ofHom <| limitπAlgHom F j
      naturality := fun _ _ f => by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.isDefEq.respectTransparency false in
/-- Witness that the limit cone in `AlgCat R` is a limit cone.
(Internal use only; use the limits API.)
-/
/-
**AlgCat.HasLimits.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `AlgCat.HasLimits`
。
形式化陈述：limitConeIsLimit : IsLimit (limitCone.{v, w} F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Witness that the limit cone in `AlgCat R` is a limit cone.
(Internal use only; use the limits API.)
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

/-- The category of R-algebras has all limits. -/
/-
**AlgCat.hasLimitsOfSize** 是 Mathlib 中的一个引理，位于命名空间 `AlgCat`。
形式化陈述：hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The category of R-algebras has all limits.
-/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (AlgCat.{w} R) :=
  { has_limits_of_shape := fun _ _ =>
    { has_limit := fun F => HasLimit.mk
        { cone := limitCone F
          isLimit := limitConeIsLimit F } } }
/-
**AlgCat.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：hasLimits : HasLimits (AlgCat.{w} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgCat.hasLimitsOfSize`：hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSiz
e.{t, v} (AlgCat.{w} R)
-/
instance hasLimits : HasLimits (AlgCat.{w} R) :=
  AlgCat.hasLimitsOfSize.{w, w, u}

/-- The forgetful functor from R-algebras to rings preserves all limits.
-/
/-
**AlgCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from R-algebras to rings preserves all limits.
-/
instance forget₂Ring_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget₂ (AlgCat.{w} R) RingCat.{w}) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (RingCat.limitConeIsLimit.{v, w}
            (_ ⋙ forget₂ (AlgCat.{w} R) RingCat.{w})) }
/-
**AlgCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂Ring_preservesLimits : PreservesLimits (forget₂ (AlgCat R) RingCat.{w}) :=
  AlgCat.forget₂Ring_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to R-modules preserves all limits.
-/
/-
**AlgCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from R-algebras to R-modules preserves all limits.
-/
instance forget₂Module_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v}
    (forget₂ (AlgCat.{w} R) (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
        preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (ModuleCat.HasLimits.limitConeIsLimit
            (K ⋙ forget₂ (AlgCat.{w} R) (ModuleCat.{w} R))) }
/-
**AlgCat.forget** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂Module_preservesLimits :
    PreservesLimits (forget₂ (AlgCat R) (ModuleCat.{w} R)) :=
  AlgCat.forget₂Module_preservesLimitsOfSize.{w, w}

/-- The forgetful functor from R-algebras to types preserves all limits.
-/
/-
**AlgCat.forget_preservesLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：forget_preservesLimitsOfSize [UnivLE.{v, w}] : PreservesLimitsOfSize.{t, v
} (forget (AlgCat.{w} R)) where preservesLimitsOfShape
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The forgetful functor from R-algebras to types preserves all limits.
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (AlgCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} ↦
       preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
          (Types.Small.limitConeIsLimit.{v} (K ⋙ forget _)) }
/-
**AlgCat.forget_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `AlgCat`。
形式化陈述：forget_preservesLimits : PreservesLimits (forget (AlgCat.{w} R))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget_preservesLimits : PreservesLimits (forget (AlgCat.{w} R)) :=
  AlgCat.forget_preservesLimitsOfSize.{w, w}

end AlgCat

