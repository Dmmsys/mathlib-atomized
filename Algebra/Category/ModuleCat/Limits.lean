/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Colimit.Module
public import Mathlib.Algebra.Module.Shrink -- shake: keep (Module R (Shrink.{w, max v w} ↥(sectionsSubmodule F))), cf. lean#13417

/-!
# The category of R-modules has all limits

Further, these limits are preserved by the forgetful functor --- that is,
the underlying types are just the limits in the category of types.
-/

@[expose] public section


open CategoryTheory Limits

universe t v w u

-- `u` is determined by the ring, so can come later
noncomputable section

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {J : Type v} [Category.{t} J] (F : J ⥤ ModuleCat.{w} R)

/--
Instance `addCommGroupObj` / 实例 `addCommGroupObj`

English:
instance addCommGroupObj
  signature: (j)
  body: inferInstanceAs AddCommGroup (F.obj j)

中文:
实例 addCommGroupObj
  签名: (j)
  定义体: inferInstanceAs AddCommGroup (F.obj j)

Depends on / 依赖: AddCommGroup, F.obj
-/
instance addCommGroupObj (j) :
    AddCommGroup ((F ⋙ forget (ModuleCat R)).obj j) :=
inferInstanceAs AddCommGroup (F.obj j)

/--
Instance `moduleObj` / 实例 `moduleObj`

English:
instance moduleObj
  signature: (j)
  body: inferInstanceAs Module R (F.obj j)

中文:
实例 moduleObj
  签名: (j)
  定义体: inferInstanceAs Module R (F.obj j)

Depends on / 依赖: F.obj, Module
-/
instance moduleObj (j) :
    Module.{u, w} R ((F ⋙ forget (ModuleCat R)).obj j) :=
inferInstanceAs Module R (F.obj j)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sectionsSubmodule` / `sectionsSubmodule` 的定义

English:
definition sectionsSubmodule
  signature: : Submodule R (forall j, F.obj j)
  body: { AddGrpCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{w} ⋙
          forget₂ AddCommGrpCat AddGrpCat.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simpa [Functor.sections] using congr_arg (r • ·) (sh f) }

中文:
定义 sectionsSubmodule
  签名: : 子模 R (对任意 j, F.obj j)
  定义体: { AddGrpCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{w} ⋙
          forget₂ AddCommGrpCat AddGrpCat.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simpa [Functor.sections] using congr_arg (r • ·) (sh f) }

Depends on / 依赖: AddCommGrpCat, AddGrpCat, AddGrpCat.sectionsAddSubgroup, Functor, Functor.sections, ModuleCat, carrier, congr_arg, forget, sections, sectionsAddSubgroup, smul_mem
-/
def sectionsSubmodule : Submodule R (forall j, F.obj j) :=
  { AddGrpCat.sectionsAddSubgroup.{v, w}
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{w} ⋙
          forget₂ AddCommGrpCat AddGrpCat.{w}) with
    carrier := (F ⋙ forget (ModuleCat R)).sections
    smul_mem' := fun r s sh j j' f => by
      simpa [Functor.sections] using congr_arg (r • ·) (sh f) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (F ⋙ forget (ModuleCat R)).sections
  body: inferInstanceAs AddCommMonoid (sectionsSubmodule F)

中文:
实例 :
  签名: 加法交换幺半群 (F ⋙ forget (模范畴 R)).sections
  定义体: inferInstanceAs AddCommMonoid (sectionsSubmodule F)

Depends on / 依赖: AddCommMonoid, sectionsSubmodule
-/
instance : AddCommMonoid (F ⋙ forget (ModuleCat R)).sections :=
inferInstanceAs AddCommMonoid (sectionsSubmodule F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (F ⋙ forget (ModuleCat R)).sections
  body: inferInstanceAs Module R (sectionsSubmodule F)

中文:
实例 :
  签名: 模 R (F ⋙ forget (模范畴 R)).sections
  定义体: inferInstanceAs Module R (sectionsSubmodule F)

Depends on / 依赖: Module, sectionsSubmodule
-/
instance : Module R (F ⋙ forget (ModuleCat R)).sections :=
inferInstanceAs Module R (sectionsSubmodule F)

section

variable [Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{w} (sectionsSubmodule F)
  body: inferInstanceAs Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))

中文:
实例 :
  签名: Small.{w} (sectionsSubmodule F)
  定义体: inferInstanceAs Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))

Depends on / 依赖: Functor, Functor.sections, ModuleCat, forget, sections
-/
instance : Small.{w} (sectionsSubmodule F) :=
inferInstanceAs Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))

-- Adding the following instance speeds up `limitModule` noticeably,
-- by preventing a bad unfold of `limitAddCommGroup`.
/--
Instance `limitAddCommMonoid` / 实例 `limitAddCommMonoid`

English:
instance limitAddCommMonoid
  signature: :
  body: inferInstanceAs AddCommMonoid (Shrink (sectionsSubmodule F))

中文:
实例 limitAddCommMonoid
  签名: :
  定义体: inferInstanceAs AddCommMonoid (Shrink (sectionsSubmodule F))

Depends on / 依赖: AddCommMonoid, Shrink, sectionsSubmodule
-/
instance limitAddCommMonoid :
    AddCommMonoid (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
inferInstanceAs AddCommMonoid (Shrink (sectionsSubmodule F))

/--
Instance `limitAddCommGroup` / 实例 `limitAddCommGroup`

English:
instance limitAddCommGroup
  signature: :
  body: inferInstanceAs AddCommGroup (Shrink.{w} (sectionsSubmodule F))

中文:
实例 limitAddCommGroup
  签名: :
  定义体: inferInstanceAs AddCommGroup (Shrink.{w} (sectionsSubmodule F))

Depends on / 依赖: AddCommGroup, Shrink, sectionsSubmodule
-/
instance limitAddCommGroup :
    AddCommGroup (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
inferInstanceAs AddCommGroup (Shrink.{w} (sectionsSubmodule F))

/--
Instance `limitModule` / 实例 `limitModule`

English:
instance limitModule
  signature: :
  body: inferInstanceAs Module R (Shrink (sectionsSubmodule F))

中文:
实例 limitModule
  签名: :
  定义体: inferInstanceAs Module R (Shrink (sectionsSubmodule F))

Depends on / 依赖: Module, Shrink, sectionsSubmodule
-/
instance limitModule :
    Module R (Types.Small.limitCone.{v, w} (F ⋙ forget (ModuleCat.{w} R))).pt :=
inferInstanceAs Module R (Shrink (sectionsSubmodule F))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitπLinearMap` / `limitπLinearMap` 的定义

English:
definition limitπLinearMap
  signature: (j)
  body: (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by simp; rfl
  map_add' _ _ := by simp; rfl

中文:
定义 limitπLinearMap
  签名: (j)
  定义体: (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by simp; rfl
  map_add' _ _ := by simp; rfl

Depends on / 依赖: ModuleCat, Types.Small.limitCone, forget, limitCone
-/
def limitπLinearMap (j) :
    (Types.Small.limitCone (F ⋙ forget (ModuleCat.{w} R))).pt ->ₗ[R]
      (F ⋙ forget (ModuleCat R)).obj j where
  toFun := (Types.Small.limitCone (F ⋙ forget (ModuleCat R))).π.app j
  map_smul' _ _ := by simp; rfl
  map_add' _ _ := by simp; rfl

namespace HasLimits

-- The next two definitions are used in the construction of `HasLimits (ModuleCat R)`.
-- After that, the limits should be constructed using the generic limits API,
-- e.g. `limit F`, `limit.cone F`, and `limit.isLimit F`.
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F where
  body: ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app j := ofHom (limitπLinearMap F j)
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

中文:
定义 limitCone
  签名: : 锥 F where
  定义体: ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app j := ofHom (limitπLinearMap F j)
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

Depends on / 依赖: ModuleCat, ModuleCat.of, Types.Small.limitCone, forget, limitCone
-/
def limitCone : Cone F where
  pt := ModuleCat.of R (Types.Small.limitCone.{v, w} (F ⋙ forget _)).pt
  π :=
    { app j := ofHom (limitπLinearMap F j)
      naturality _ _ f := by
        ext
        simpa using! (Types.Small.limitCone (F ⋙ forget _)).π.naturality_apply f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone.{t, v, w} F)
  body: by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ofHom ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp [← equivShrink_add]
    rfl
  · int

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone.{t, v, w} F)
  定义体: by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ofHom ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp [← equivShrink_add]
    rfl
  · int

Depends on / 依赖: IsLimit, IsLimit.ofFaithful, ModuleCat, Types.Small.limitConeIsLimit, equivShrink_add, equivShrink_smul, forget, limitConeIsLimit, mapCone, ofFaithful
-/
def limitConeIsLimit : IsLimit (limitCone.{t, v, w} F) := by
  refine IsLimit.ofFaithful (forget (ModuleCat R)) (Types.Small.limitConeIsLimit.{v, w} _)
    (fun s => ofHom ⟨⟨(Types.Small.limitConeIsLimit.{v, w} _).lift
                ((forget (ModuleCat R)).mapCone s), ?_⟩, ?_⟩)
    (fun s => rfl)
  · intro x y
    simp [← equivShrink_add]
    rfl
  · intro r x
    simp [← equivShrink_smul]
    rfl

end HasLimits

open HasLimits

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

Depends on / 依赖: HasLimit, HasLimit.mk
-/
instance hasLimit : HasLimit F := HasLimit.mk {
    cone := limitCone F
    isLimit := limitConeIsLimit F
  }

/--
lemma `hasLimitsOfShape` / 引理 `hasLimitsOfShape`

English:
lemma hasLimitsOfShape
  given: [Small.{w} J]
  statement: HasLimitsOfShape J (ModuleCat.{w} R) where

中文:
引理 hasLimitsOfShape
  条件: [Small.{w} J]
  结论: 有形状极限 J (模范畴.{w} R) where
-/
lemma hasLimitsOfShape [Small.{w} J] : HasLimitsOfShape J (ModuleCat.{w} R) where

/--
lemma `hasLimitsOfSize` / 引理 `hasLimitsOfSize`

English:
lemma hasLimitsOfSize
  given: [UnivLE.{v, w}]
  statement: HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  proof: hasLimitsOfShape

中文:
引理 hasLimitsOfSize
  条件: [UnivLE.{v, w}]
  结论: 有LimitsOfSize.{t, v} (模范畴.{w} R) where
  证明: hasLimitsOfShape

Depends on / 依赖: hasLimitsOfShape
-/
lemma hasLimitsOfSize [UnivLE.{v, w}] : HasLimitsOfSize.{t, v} (ModuleCat.{w} R) where
  has_limits_of_shape _ := hasLimitsOfShape

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : HasLimits (ModuleCat.{w} R)
  body: ModuleCat.hasLimitsOfSize.{w, w, w, u}

中文:
实例 hasLimits
  签名: : 有极限 (模范畴.{w} R)
  定义体: ModuleCat.hasLimitsOfSize.{w, w, w, u}

Depends on / 依赖: ModuleCat, ModuleCat.hasLimitsOfSize, hasLimitsOfSize
-/
instance hasLimits : HasLimits (ModuleCat.{w} R) :=
  ModuleCat.hasLimitsOfSize.{w, w, w, u}

instance (priority := high) hasLimits' : HasLimits (ModuleCat.{u} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u}

/--
Definition of `forget₂AddCommGroup_preservesLimitsAux` / `forget₂AddCommGroup_preservesLimitsAux` 的定义

English:
definition forget₂AddCommGroup_preservesLimitsAux
  signature: :
  body: letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrpCat) ⋙ forget _)) :=
inferInstanceAs Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrpCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrpCat.{w})

中文:
定义 forget₂AddCommGroup_preservesLimitsAux
  签名: :
  定义体: letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrpCat) ⋙ forget _)) :=
inferInstanceAs Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrpCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrpCat.{w})

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.limitConeIsLimit, Functor, Functor.sections, ModuleCat, forget, limitConeIsLimit, sections
-/
def forget₂AddCommGroup_preservesLimitsAux :
    IsLimit ((forget₂ (ModuleCat R) AddCommGrpCat).mapCone (limitCone F)) :=
  letI : Small.{w} (Functor.sections ((F ⋙ forget₂ _ AddCommGrpCat) ⋙ forget _)) :=
inferInstanceAs Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R)))
  AddCommGrpCat.limitConeIsLimit
    (F ⋙ forget₂ (ModuleCat.{w} R) _ : J ⥤ AddCommGrpCat.{w})

/--
Instance `forget₂AddCommGroup_preservesLimit` / 实例 `forget₂AddCommGroup_preservesLimit`

English:
instance forget₂AddCommGroup_preservesLimit
  signature: :
  body: preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (forget₂AddCommGroup_preservesLimitsAux F)

中文:
实例 forget₂AddCommGroup_preservesLimit
  签名: :
  定义体: preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (forget₂AddCommGroup_preservesLimitsAux F)

Depends on / 依赖: limitConeIsLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget₂AddCommGroup_preservesLimit :
    PreservesLimit F (forget₂ (ModuleCat R) AddCommGrpCat) :=
  preservesLimit_of_preserves_limit_cone (limitConeIsLimit F)
    (forget₂AddCommGroup_preservesLimitsAux F)

/--
Instance `forget₂AddCommGroup_preservesLimitsOfSize` / 实例 `forget₂AddCommGroup_preservesLimitsOfSize`

English:
instance forget₂AddCommGroup_preservesLimitsOfSize
  signature: [UnivLE.{v, w}]
  body: { preservesLimit := inferInstance }

中文:
实例 forget₂AddCommGroup_preservesLimitsOfSize
  签名: [UnivLE.{v, w}]
  定义体: { preservesLimit := inferInstance }

Depends on / 依赖: preservesLimit
-/
instance forget₂AddCommGroup_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v}
      (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) where
  preservesLimitsOfShape := { preservesLimit := inferInstance }

/--
Instance `forget₂AddCommGroup_preservesLimits` / 实例 `forget₂AddCommGroup_preservesLimits`

English:
instance forget₂AddCommGroup_preservesLimits
  signature: :
  body: ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w}

中文:
实例 forget₂AddCommGroup_preservesLimits
  签名: :
  定义体: ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w}

Depends on / 依赖: ModuleCat, ModuleCat.forget
-/
instance forget₂AddCommGroup_preservesLimits :
    PreservesLimits (forget₂ (ModuleCat R) AddCommGrpCat.{w}) :=
  ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{w, w}

/--
Instance `forget_preservesLimitsOfSize` / 实例 `forget_preservesLimitsOfSize`

English:
instance forget_preservesLimitsOfSize
  signature: [UnivLE.{v, w}]
  body: { preservesLimit := fun {K} => preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }

中文:
实例 forget_preservesLimitsOfSize
  签名: [UnivLE.{v, w}]
  定义体: { preservesLimit := fun {K} => preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }

Depends on / 依赖: G.toGrp, Types.Small.limitConeIsLimit, forget, limitConeIsLimit, preservesLimit, preservesLimit_of_preserves_limit_cone
-/
instance forget_preservesLimitsOfSize [UnivLE.{v, w}] :
    PreservesLimitsOfSize.{t, v} (forget (ModuleCat.{w} R)) where
  preservesLimitsOfShape :=
    { preservesLimit := fun {K} => preservesLimit_of_preserves_limit_cone (limitConeIsLimit K)
        (Types.Small.limitConeIsLimit.{v} (_ ⋙ forget _)) }

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : PreservesLimits (forget (ModuleCat.{w} R))
  body: ModuleCat.forget_preservesLimitsOfSize.{w, w}

中文:
实例 forget_preservesLimits
  签名: : PreservesLimits (forget (模范畴.{w} R))
  定义体: ModuleCat.forget_preservesLimitsOfSize.{w, w}

Depends on / 依赖: G.isFinite, ModuleCat, ModuleCat.forget_preservesLimitsOfSize, forget_preservesLimitsOfSize, isFinite
-/
instance forget_preservesLimits : PreservesLimits (forget (ModuleCat.{w} R)) :=
  ModuleCat.forget_preservesLimitsOfSize.{w, w}

end

/--
Instance `forget₂AddCommGroup_reflectsLimit` / 实例 `forget₂AddCommGroup_reflectsLimit`

English:
instance forget₂AddCommGroup_reflectsLimit
  signature: :
  body: ⟨by
    have : HasLimit (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) := ⟨_, hc⟩
    have : Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R))) := by
      simpa only [AddCommGrpCat.hasLimit_iff_small_sections] using! this
    have := reflectsLimit_of_reflectsIsomorphisms F (forget₂ (ModuleCat R) Ad

中文:
实例 forget₂AddCommGroup_reflectsLimit
  签名: :
  定义体: ⟨by
    have : HasLimit (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) := ⟨_, hc⟩
    have : Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R))) := by
      simpa only [AddCommGrpCat.hasLimit_iff_small_sections] using! this
    have := reflectsLimit_of_reflectsIsomorphisms F (forget₂ (ModuleCat R) Ad

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.hasLimit_iff_small_sections, Functor, Functor.sections, HasLimit, ModuleCat, forget, hasLimit_iff_small_sections, isLimitOfReflects, reflectsLimit_of_reflectsIsomorphisms, sections
-/
instance forget₂AddCommGroup_reflectsLimit :
    ReflectsLimit F (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where
  reflects {c} hc := ⟨by
    have : HasLimit (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) := ⟨_, hc⟩
    have : Small.{w} (Functor.sections (F ⋙ forget (ModuleCat R))) := by
      simpa only [AddCommGrpCat.hasLimit_iff_small_sections] using! this
    have := reflectsLimit_of_reflectsIsomorphisms F (forget₂ (ModuleCat R) AddCommGrpCat)
    exact isLimitOfReflects _ hc⟩

/--
Instance `forget₂AddCommGroup_reflectsLimitOfShape` / 实例 `forget₂AddCommGroup_reflectsLimitOfShape`

English:
instance forget₂AddCommGroup_reflectsLimitOfShape
  signature: :

中文:
实例 forget₂AddCommGroup_reflectsLimitOfShape
  签名: :
-/
instance forget₂AddCommGroup_reflectsLimitOfShape :
    ReflectsLimitsOfShape J (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where

/--
Instance `forget₂AddCommGroup_reflectsLimitOfSize` / 实例 `forget₂AddCommGroup_reflectsLimitOfSize`

English:
instance forget₂AddCommGroup_reflectsLimitOfSize
  signature: :

中文:
实例 forget₂AddCommGroup_reflectsLimitOfSize
  签名: :
-/
instance forget₂AddCommGroup_reflectsLimitOfSize :
    ReflectsLimitsOfSize.{t, v} (forget₂ (ModuleCat.{w} R) AddCommGrpCat) where

section DirectLimit

open Module

variable {ι : Type v}
variable [DecidableEq ι] [Preorder ι]
variable (G : ι -> Type v)
variable [forall i, AddCommGroup (G i)] [forall i, Module R (G i)]
variable (f : forall i j, i <= j -> G i ->ₗ[R] G j) [DirectedSystem G fun i j h => f i j h]

/-- The diagram (in the sense of `CategoryTheory`) of an unbundled `directLimit` of modules. -/
@[simps]
/--
Definition of `directLimitDiagram` / `directLimitDiagram` 的定义

English:
definition directLimitDiagram
  signature: : ι ⥤ ModuleCat R where
  body: ModuleCat.of R (G i)
  map hij := ofHom (f _ _ hij.le)
  map_id i := by
    ext
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    ext
    symm
    apply Module.DirectedSystem.map_map f

中文:
定义 directLimitDiagram
  签名: : ι ⥤ 模范畴 R where
  定义体: ModuleCat.of R (G i)
  map hij := ofHom (f _ _ hij.le)
  map_id i := by
    ext
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    ext
    symm
    apply Module.DirectedSystem.map_map f

Depends on / 依赖: ModuleCat, ModuleCat.of
-/
def directLimitDiagram : ι ⥤ ModuleCat R where
  obj i := ModuleCat.of R (G i)
  map hij := ofHom (f _ _ hij.le)
  map_id i := by
    ext
    apply Module.DirectedSystem.map_self
  map_comp hij hjk := by
    ext
    symm
    apply Module.DirectedSystem.map_map f

/-- The `Cocone` on `directLimitDiagram` corresponding to
the unbundled `directLimit` of modules.

In `directLimitIsColimit` we show that it is a colimit cocone. -/
@[simps]
/--
Definition of `directLimitCocone` / `directLimitCocone` 的定义

English:
definition directLimitCocone
  signature: : Cocone (directLimitDiagram G f) where
  body: ModuleCat.of R DirectLimit G f
  ι :=
    { app := fun x => ofHom (Module.DirectLimit.of R ι G f x)
      naturality := fun _ _ hij => by
        ext
        exact DirectLimit.of_f }

中文:
定义 directLimitCocone
  签名: : 余锥 (directLimitDiagram G f) where
  定义体: ModuleCat.of R DirectLimit G f
  ι :=
    { app := fun x => ofHom (Module.DirectLimit.of R ι G f x)
      naturality := fun _ _ hij => by
        ext
        exact DirectLimit.of_f }

Depends on / 依赖: DirectLimit, ModuleCat, ModuleCat.of
-/
def directLimitCocone : Cocone (directLimitDiagram G f) where
pt := ModuleCat.of R DirectLimit G f
  ι :=
    { app := fun x => ofHom (Module.DirectLimit.of R ι G f x)
      naturality := fun _ _ hij => by
        ext
        exact DirectLimit.of_f }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unbundled `directLimit` of modules is a colimit
in the sense of `CategoryTheory`. -/
@[simps]
/--
Definition of `directLimitIsColimit` / `directLimitIsColimit` 的定义

English:
definition directLimitIsColimit
  signature: : IsColimit (directLimitCocone G f) where
  body: ofHom
    Module.DirectLimit.lift R ι G f (fun i => (s.ι.app i).hom) fun i j h x => by
      simp only [Functor.const_obj_obj]
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    ext
    dsimp only [hom_comp, directLimitCocone, hom_ofHom, LinearMap.comp_apply]
    apply DirectLimit.lift_of
  

中文:
定义 directLimitIsColimit
  签名: : 是余极限 (directLimitCocone G f) where
  定义体: ofHom
    Module.DirectLimit.lift R ι G f (fun i => (s.ι.app i).hom) fun i j h x => by
      simp only [Functor.const_obj_obj]
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    ext
    dsimp only [hom_comp, directLimitCocone, hom_ofHom, LinearMap.comp_apply]
    apply DirectLimit.lift_of
  
-/
def directLimitIsColimit : IsColimit (directLimitCocone G f) where
desc s := ofHom
    Module.DirectLimit.lift R ι G f (fun i => (s.ι.app i).hom) fun i j h x => by
      simp only [Functor.const_obj_obj]
      rw [← s.w (homOfLE h)]
      rfl
  fac s i := by
    ext
    dsimp only [hom_comp, directLimitCocone, hom_ofHom, LinearMap.comp_apply]
    apply DirectLimit.lift_of
  uniq s m h := by
    have :
      s.ι.app = fun i =>
        (ofHom (DirectLimit.of R ι (fun i => G i) (fun i j H => f i j H) i)) ≫ m := by
      funext i
      rw [← h]
      rfl
    ext
    simp [this]

end DirectLimit

end ModuleCat
