/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Limits in the category of types.

We show that the category of types has all limits, by providing the usual concrete models.

-/

@[expose] public section

universe u' v u w

namespace CategoryTheory.Limits.Types

open ConcreteCategory

section limit_characterization

variable {J : Type v} [Category.{w} J] {F : J ⥤ Type u}

/--
Definition of `coneOfSection` / `coneOfSection` 的定义

English:
definition coneOfSection
  signature: {s} (hs : s in F.sections)
  body: PUnit
  π := { app j := ↾fun _ => s j, naturality _ _ f := by ext; exact (hs f).symm }

中文:
定义 coneOfSection
  签名: {s} (hs : s in F.sections)
  定义体: PUnit
  π := { app j := ↾fun _ => s j, naturality _ _ f := by ext; exact (hs f).symm }
-/
def coneOfSection {s} (hs : s in F.sections) : Cone F where
  pt := PUnit
  π := { app j := ↾fun _ => s j, naturality _ _ f := by ext; exact (hs f).symm }

/--
Definition of `sectionOfCone` / `sectionOfCone` 的定义

English:
definition sectionOfCone
  signature: (c : Cone F) (x : c.pt)
  body: ⟨fun j => c.π.app j x, fun f => congr_hom (c.π.naturality f).symm x⟩

中文:
定义 sectionOfCone
  签名: (c : 锥 F) (x : c.pt)
  定义体: ⟨fun j => c.π.app j x, fun f => congr_hom (c.π.naturality f).symm x⟩

Depends on / 依赖: congr_hom, naturality
-/
def sectionOfCone (c : Cone F) (x : c.pt) : F.sections :=
  ⟨fun j => c.π.app j x, fun f => congr_hom (c.π.naturality f).symm x⟩

/--
theorem `isLimit_iff` / 定理 `isLimit_iff`

English:
theorem isLimit_iff
  given: (c : Cone F)
  proof: by
  refine ⟨fun ⟨t⟩ s hs => ?_, fun h => ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j => congr_hom (t.fac cs j) ⟨⟩,
      fun x hx => congr_hom (CC := fun X => X)
        (t.uniq cs (↾fun _ => x) fun j => by ext; exact hx j) ⟨⟩⟩
  · have := fun c y => h _ (sectionOfCone c y).

中文:
定理 isLimit_iff
  条件: (c : 锥 F)
  证明: by
  refine ⟨fun ⟨t⟩ s hs => ?_, fun h => ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j => congr_hom (t.fac cs j) ⟨⟩,
      fun x hx => congr_hom (CC := fun X => X)
        (t.uniq cs (↾fun _ => x) fun j => by ext; exact hx j) ⟨⟩⟩
  · have := fun c y => h _ (sectionOfCone c y).

Depends on / 依赖: coneOfSection, congr_hom, sectionOfCone, t.fac, t.lift, t.uniq
-/
theorem isLimit_iff (c : Cone F) :
    Nonempty (IsLimit c) ↔ forall s in F.sections, exists! x : c.pt, forall j, c.π.app j x = s j := by
  refine ⟨fun ⟨t⟩ s hs => ?_, fun h => ⟨?_⟩⟩
  · let cs := coneOfSection hs
    exact ⟨t.lift cs ⟨⟩, fun j => congr_hom (t.fac cs j) ⟨⟩,
      fun x hx => congr_hom (CC := fun X => X)
        (t.uniq cs (↾fun _ => x) fun j => by ext; exact hx j) ⟨⟩⟩
  · have := fun c y => h _ (sectionOfCone c y).2
    choose x hx using fun c y => h _ (sectionOfCone c y).2
    exact ⟨fun d => ↾(x d), fun c j => by ext y; exact (hx c y).1 j,
      fun c f hf => by ext y; exact (hx c y).2 (f y) (fun j => congr_hom (hf j) y)⟩

/--
theorem `isLimit_iff_bijective_sectionOfCone` / 定理 `isLimit_iff_bijective_sectionOfCone`

English:
theorem isLimit_iff_bijective_sectionOfCone
  given: (c : Cone F)
  proof: by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]

中文:
定理 isLimit_iff_bijective_sectionOfCone
  条件: (c : 锥 F)
  证明: by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]

Depends on / 依赖: F.sections_ext_iff, Function, Function.bijective_iff_existsUnique, Subtype, Subtype.forall, bijective_iff_existsUnique, isLimit_iff, sections_ext_iff, simp_rw
-/
theorem isLimit_iff_bijective_sectionOfCone (c : Cone F) :
    Nonempty (IsLimit c) ↔ (Types.sectionOfCone c).Bijective := by
  simp_rw [isLimit_iff, Function.bijective_iff_existsUnique, Subtype.forall, F.sections_ext_iff,
    sectionOfCone]

/--
Definition of `isLimitEquivSections` / `isLimitEquivSections` 的定义

English:
definition isLimitEquivSections
  signature: {c : Cone F} (t : IsLimit c)
  body: sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_hom (t.uniq (coneOfSection _)
    (↾fun _ => x) fun _ => rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j => congr_hom (t.fac (coneOfSection s.2) j) ⟨⟩)

@[simp]

中文:
定义 isLimitEquivSections
  签名: {c : 锥 F} (t : 是极限 c)
  定义体: sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_hom (t.uniq (coneOfSection _)
    (↾fun _ => x) fun _ => rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j => congr_hom (t.fac (coneOfSection s.2) j) ⟨⟩)

@[simp]

Depends on / 依赖: sectionOfCone
-/
noncomputable def isLimitEquivSections {c : Cone F} (t : IsLimit c) :
    c.pt ≃ F.sections where
  toFun := sectionOfCone c
  invFun s := t.lift (coneOfSection s.2) ⟨⟩
  left_inv x := (congr_hom (t.uniq (coneOfSection _)
    (↾fun _ => x) fun _ => rfl) ⟨⟩).symm
  right_inv s := Subtype.ext (funext fun j => congr_hom (t.fac (coneOfSection s.2) j) ⟨⟩)

@[simp]
/--
theorem `isLimitEquivSections_apply` / 定理 `isLimitEquivSections_apply`

English:
theorem isLimitEquivSections_apply
  statement: {c : Cone F} (t : IsLimit c) (j : J)
  proof: rfl

@[simp]

中文:
定理 isLimitEquivSections_apply
  结论: {c : 锥 F} (t : 是极限 c) (j : J)
  证明: rfl

@[simp]
-/
theorem isLimitEquivSections_apply {c : Cone F} (t : IsLimit c) (j : J)
    (x : c.pt) : (isLimitEquivSections t x : forall j, F.obj j) j = c.π.app j x := rfl

@[simp]
/--
theorem `isLimitEquivSections_symm_apply` / 定理 `isLimitEquivSections_symm_apply`

English:
theorem isLimitEquivSections_symm_apply
  statement: {c : Cone F} (t : IsLimit c)
  proof: by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
  rfl

中文:
定理 isLimitEquivSections_symm_apply
  结论: {c : 锥 F} (t : 是极限 c)
  证明: by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
  rfl

Depends on / 依赖: conv_rhs, isLimitEquivSections, right_inv
-/
theorem isLimitEquivSections_symm_apply {c : Cone F} (t : IsLimit c)
    (x : F.sections) (j : J) :
    dsimp% c.π.app j ((isLimitEquivSections t).symm x) = (x : forall j, F.obj j) j := by
  conv_rhs => rw [← (isLimitEquivSections t).right_inv x]
  rfl

end limit_characterization

variable {J : Type v} [Category.{w} J]

/-! We now provide two distinct implementations in the category of types.

The first, in the `CategoryTheory.Limits.Types.Small` namespace,
assumes `Small.{u} J` and constructs `J`-indexed limits in `Type u`.

The second, in the `CategoryTheory.Limits.Types.TypeMax` namespace
constructs limits for functors `F : J ⥤ Type (max v u)`, for `J : Type v`.
This construction is slightly nicer, as the limit is definitionally just `F.sections`,
rather than `Shrink F.sections`, which makes an arbitrary choice of `u`-small representative.

Hopefully we might be able to entirely remove the `TypeMax` constructions,
but for now they are useful glue for the later parts of the library.
-/

namespace Small

variable (F : J ⥤ Type u)

section

variable [Small.{u} F.sections]

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: : Cone F where
  body: Shrink F.sections
  π :=
    { app j := ↾fun u => ((equivShrink F.sections).symm u).val j }

中文:
定义 limitCone
  签名: : 锥 F where
  定义体: Shrink F.sections
  π :=
    { app j := ↾fun u => ((equivShrink F.sections).symm u).val j }

Depends on / 依赖: F.sections, Shrink, sections
-/
noncomputable def limitCone : Cone F where
  pt := Shrink F.sections
  π :=
    { app j := ↾fun u => ((equivShrink F.sections).symm u).val j }

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/--
lemma `limitCone_pt_ext` / 引理 `limitCone_pt_ext`

English:
lemma limitCone_pt_ext
  statement: {x y : (limitCone F).pt}
  proof: by
  simp_all

中文:
引理 limitCone_pt_ext
  结论: {x y : (limitCone F).pt}
  证明: by
  simp_all
-/
lemma limitCone_pt_ext {x y : (limitCone F).pt}
    (w : (equivShrink F.sections).symm x = (equivShrink F.sections).symm y) : x = y := by
  simp_all

set_option backward.defeqAttrib.useBackward true in
/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: : IsLimit (limitCone.{v, u} F) where
  body: ↾fun v => equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using! congr_hom (w j) x

中文:
定义 limitConeIsLimit
  签名: : 是极限 (limitCone.{v, u} F) where
  定义体: ↾fun v => equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using! congr_hom (w j) x

Depends on / 依赖: F.sections, equivShrink, sections
-/
noncomputable def limitConeIsLimit : IsLimit (limitCone.{v, u} F) where
  lift s := ↾fun v => equivShrink F.sections
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x j
    simpa using! congr_hom (w j) x

end

end Small

/--
theorem `hasLimit_iff_small_sections` / 定理 `hasLimit_iff_small_sections`

English:
theorem hasLimit_iff_small_sections
  given: (F : J ⥤ Type u)
  statement: HasLimit F ↔ Small.{u} F.sections
  proof: ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isLimit_iff_bijective_sectionOfCone (limit.cone F)).mp ⟨limit.isLimit _⟩)).symm⟩⟩,
   fun _ => ⟨_, Small.limitConeIsLimit F⟩⟩

中文:
定理 hasLimit_iff_small_sections
  条件: (F : J ⥤ 类型u)
  结论: 有极限 F ↔ Small.{u} F.sections
  证明: ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isLimit_iff_bijective_sectionOfCone (limit.cone F)).mp ⟨limit.isLimit _⟩)).symm⟩⟩,
   fun _ => ⟨_, Small.limitConeIsLimit F⟩⟩

Depends on / 依赖: Equiv.ofBijective, Small.limitConeIsLimit, isLimit, isLimit_iff_bijective_sectionOfCone, limit.cone, limit.isLimit, limitConeIsLimit, ofBijective
-/
theorem hasLimit_iff_small_sections (F : J ⥤ Type u) : HasLimit F ↔ Small.{u} F.sections :=
  ⟨fun _ => .mk ⟨_, ⟨(Equiv.ofBijective _
    ((isLimit_iff_bijective_sectionOfCone (limit.cone F)).mp ⟨limit.isLimit _⟩)).symm⟩⟩,
   fun _ => ⟨_, Small.limitConeIsLimit F⟩⟩

-- TODO: If `UnivLE` works out well, we will eventually want to deprecate these
-- definitions, and probably as a first step put them in namespace or otherwise rename them.
section TypeMax

/-- (internal implementation) the limit cone of a functor,
implemented as flat sections of a pi type
-/
@[simps]
/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: (F : J ⥤ Type (max v u))
  body: F.sections
  π := { app j := ↾fun u => u.val j }

中文:
定义 limitCone
  签名: (F : J ⥤ 类型 (最大值 v u))
  定义体: F.sections
  π := { app j := ↾fun u => u.val j }

Depends on / 依赖: F.sections, sections
-/
noncomputable def limitCone (F : J ⥤ Type (max v u)) : Cone F where
  pt := F.sections
  π := { app j := ↾fun u => u.val j }

/-- (internal implementation) the fact that the proposed limit cone is the limit -/
@[simps]
/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: (F : J ⥤ Type (max v u))
  body: ↾fun v =>
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x
    apply Subtype.ext
    funext j
    exact congr_hom (w j) x

中文:
定义 limitConeIsLimit
  签名: (F : J ⥤ 类型 (最大值 v u))
  定义体: ↾fun v =>
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x
    apply Subtype.ext
    funext j
    exact congr_hom (w j) x
-/
noncomputable def limitConeIsLimit (F : J ⥤ Type (max v u)) : IsLimit (limitCone F) where
  lift s := ↾fun v =>
    { val := fun j => s.π.app j v
      property := fun f => congr_hom (Cone.w s f) _ }
  uniq := fun _ _ w => by
    ext x
    apply Subtype.ext
    funext j
    exact congr_hom (w j) x

end TypeMax


/-!
The results in this section have a `UnivLE.{v, u}` hypothesis,
but as they only use the constructions from the `CategoryTheory.Limits.Types.UnivLE` namespace
in their definitions (rather than their statements),
we leave them in the main `CategoryTheory.Limits.Types` namespace.
-/
section UnivLE

open UnivLE

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: [Small.{u} J] (F : J ⥤ Type u)
  body: (hasLimit_iff_small_sections F).mpr inferInstance

中文:
实例 hasLimit
  签名: [Small.{u} J] (F : J ⥤ 类型u)
  定义体: (hasLimit_iff_small_sections F).mpr inferInstance

Depends on / 依赖: hasLimit_iff_small_sections
-/
instance hasLimit [Small.{u} J] (F : J ⥤ Type u) : HasLimit F :=
  (hasLimit_iff_small_sections F).mpr inferInstance

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [Small.{u} J]

中文:
实例 hasLimitsOfShape
  签名: [Small.{u} J]
-/
instance hasLimitsOfShape [Small.{u} J] : HasLimitsOfShape J (Type u) where

/--
The category of types has all limits.

More specifically, when `UnivLE.{v, u}`, the category `Type u` has all `v`-small limits. -/
@[stacks 002U]
instance (priority := 1300) hasLimitsOfSize [UnivLE.{v, u}] :
    HasLimitsOfSize.{w, v} (Type u) where
  has_limits_of_shape _ := { }

variable (F : J ⥤ Type u) [HasLimit F]

/--
Definition of `limitEquivSections` / `limitEquivSections` 的定义

English:
definition limitEquivSections
  signature: : limit F ≃ F.sections
  body: isLimitEquivSections (limit.isLimit F)

@[simp]

中文:
定义 limitEquivSections
  签名: : limit F ≃ F.sections
  定义体: isLimitEquivSections (limit.isLimit F)

@[simp]

Depends on / 依赖: isLimit, isLimitEquivSections, limit.isLimit
-/
noncomputable def limitEquivSections : limit F ≃ F.sections :=
  isLimitEquivSections (limit.isLimit F)

@[simp]
/--
theorem `limitEquivSections_apply` / 定理 `limitEquivSections_apply`

English:
theorem limitEquivSections_apply
  given: (x : limit F) (j : J)
  proof: rfl

@[simp]

中文:
定理 limitEquivSections_apply
  条件: (x : limit F) (j : J)
  证明: rfl

@[simp]
-/
theorem limitEquivSections_apply (x : limit F) (j : J) :
    dsimp% ((limitEquivSections F) x : forall j, F.obj j) j = limit.π F j x :=
  rfl

@[simp]
/--
theorem `limitEquivSections_symm_apply` / 定理 `limitEquivSections_symm_apply`

English:
theorem limitEquivSections_symm_apply
  given: (x : F.sections) (j : J)
  proof: isLimitEquivSections_symm_apply _ _ _

中文:
定理 limitEquivSections_symm_apply
  条件: (x : F.sections) (j : J)
  证明: isLimitEquivSections_symm_apply _ _ _

Depends on / 依赖: isLimitEquivSections_symm_apply
-/
theorem limitEquivSections_symm_apply (x : F.sections) (j : J) :
    limit.π F j ((limitEquivSections F).symm x) = (x : forall j, F.obj j) j :=
  isLimitEquivSections_symm_apply _ _ _

/--
Definition of `limNatIsoSectionsFunctor` / `limNatIsoSectionsFunctor` 的定义

English:
definition limNatIsoSectionsFunctor
  signature: :
  body: NatIso.ofComponents (fun F => (limitEquivSections F).toIso)
    fun f => by ext x; exact Subtype.ext (funext fun j => congr_hom (limMap_π f j) x)

中文:
定义 lim自然数IsoSectionsFunctor
  签名: :
  定义体: NatIso.ofComponents (fun F => (limitEquivSections F).toIso)
    fun f => by ext x; exact Subtype.ext (funext fun j => congr_hom (limMap_π f j) x)

Depends on / 依赖: NatIso, NatIso.ofComponents, Subtype, Subtype.ext, congr_hom, limitEquivSections, ofComponents
-/
noncomputable def limNatIsoSectionsFunctor :
    (lim : (J ⥤ Type (max u v)) ⥤ Type (max u v)) ≅ Functor.sectionsFunctor J :=
  NatIso.ofComponents (fun F => (limitEquivSections F).toIso)
    fun f => by ext x; exact Subtype.ext (funext fun j => congr_hom (limMap_π f j) x)

/--
Definition of `Limit.mk` / `Limit.mk` 的定义

English:
definition Limit.mk
  signature: (x : forall j, F.obj j) (h : forall (j j') (f : j ⟶ j'), F.map f (x j) = x j')
  body: (limitEquivSections F).symm ⟨x, h _ _⟩

@[simp]

中文:
定义 极限.mk
  签名: (x : 对任意 j, F.obj j) (h : 对任意 (j j') (f : j ⟶ j'), F.map f (x j) = x j')
  定义体: (limitEquivSections F).symm ⟨x, h _ _⟩

@[simp]

Depends on / 依赖: limitEquivSections
-/
noncomputable def Limit.mk (x : forall j, F.obj j) (h : forall (j j') (f : j ⟶ j'), F.map f (x j) = x j') :
    limit F :=
  (limitEquivSections F).symm ⟨x, h _ _⟩

@[simp]
/--
theorem `Limit.π_mk` / 定理 `Limit.π_mk`

English:
theorem Limit.π_mk
  given: (x : forall j, F.obj j) (h : forall (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j)
  proof: by
  dsimp [Limit.mk]
  simp

中文:
定理 极限.π_mk
  条件: (x : 对任意 j, F.obj j) (h : 对任意 (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j)
  证明: by
  dsimp [Limit.mk]
  simp

Depends on / 依赖: Limit.mk
-/
theorem Limit.π_mk (x : forall j, F.obj j) (h : forall (j j') (f : j ⟶ j'), F.map f (x j) = x j') (j) :
    limit.π F j (Limit.mk F x h) = x j := by
  dsimp [Limit.mk]
  simp

-- PROJECT: prove this for concrete categories where the forgetful functor preserves limits
@[ext]
/--
theorem `limit_ext` / 定理 `limit_ext`

English:
theorem limit_ext
  given: (x y : limit F) (w : forall j, limit.π F j x = limit.π F j y)
  proof: by
  apply (limitEquivSections F).injective
  ext j
  simp [w j]

@[ext]

中文:
定理 limit_ext
  条件: (x y : limit F) (w : 对任意 j, limit.π F j x = limit.π F j y)
  证明: by
  apply (limitEquivSections F).injective
  ext j
  simp [w j]

@[ext]

Depends on / 依赖: injective, limitEquivSections
-/
theorem limit_ext (x y : limit F) (w : forall j, limit.π F j x = limit.π F j y) :
    x = y := by
  apply (limitEquivSections F).injective
  ext j
  simp [w j]

@[ext]
/--
theorem `limit_ext'` / 定理 `limit_ext'`

English:
theorem limit_ext'
  statement: (F' : J ⥤ Type v) (x y : limit F')
  proof: limit_ext F' x y w

中文:
定理 limit_ext'
  结论: (F' : J ⥤ 类型v) (x y : limit F')
  证明: limit_ext F' x y w

Depends on / 依赖: limit_ext
-/
theorem limit_ext' (F' : J ⥤ Type v) (x y : limit F')
    (w : forall j, limit.π F' j x = limit.π F' j y) : x = y :=
  limit_ext F' x y w

/--
theorem `limit_ext_iff'` / 定理 `limit_ext_iff'`

English:
theorem limit_ext_iff'
  given: (F' : J ⥤ Type v) (x y : limit F')
  proof: ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩

中文:
定理 limit_ext_iff'
  条件: (F' : J ⥤ 类型v) (x y : limit F')
  证明: ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩

Depends on / 依赖: limit_ext
-/
theorem limit_ext_iff' (F' : J ⥤ Type v) (x y : limit F') :
    x = y ↔ forall j, limit.π F' j x = limit.π F' j y :=
  ⟨fun t _ => t ▸ rfl, limit_ext' _ _ _⟩

-- `limit.lift_π_apply` and `limit.w_apply` are generated (and tagged `simp`)
-- in `Mathlib/CategoryTheory/ConcreteCategory/Elementwise.lean`.
attribute [elementwise] limMap_π
attribute [simp] limMap_π_apply

variable {F} in
@[deprecated limit.w_apply (since := "2026-02-17")]
/--
theorem `Limit.w_apply` / 定理 `Limit.w_apply`

English:
theorem Limit.w_apply
  given: {j j' : J} {x : (limit F : Type u)} (f : j ⟶ j')
  proof: limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]

中文:
定理 极限.w_apply
  条件: {j j' : J} {x : (limit F : 类型u)} (f : j ⟶ j')
  证明: limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]

Depends on / 依赖: limit.w_apply, w_apply
-/
theorem Limit.w_apply {j j' : J} {x : (limit F : Type u)} (f : j ⟶ j') :
    F.map f (limit.π F j x) = limit.π F j' x :=
  limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]
/--
theorem `Limit.lift_π_apply` / 定理 `Limit.lift_π_apply`

English:
theorem Limit.lift_π_apply
  given: (s : Cone F) (j : J) (x : s.pt)
  proof: limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]

中文:
定理 极限.lift_π_apply
  条件: (s : 锥 F) (j : J) (x : s.pt)
  证明: limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]

Depends on / 依赖: limit.lift_
-/
theorem Limit.lift_π_apply (s : Cone F) (j : J) (x : s.pt) :
    limit.π F j (limit.lift F s x) = s.π.app j x :=
  limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]
/--
theorem `Limit.map_π_apply` / 定理 `Limit.map_π_apply`

English:
theorem Limit.map_π_apply
  statement: {F G : J ⥤ Type u} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
  proof: limMap_π_apply _ _ _

@[deprecated limit.w_apply (since := "2026-02-17")]

中文:
定理 极限.map_π_apply
  结论: {F G : J ⥤ 类型u} [有极限 F] [有极限 G] (α : F ⟶ G) (j : J)
  证明: limMap_π_apply _ _ _

@[deprecated limit.w_apply (since := "2026-02-17")]
-/
theorem Limit.map_π_apply {F G : J ⥤ Type u} [HasLimit F] [HasLimit G] (α : F ⟶ G) (j : J)
    (x : limit F) : limit.π G j (limMap α x) = α.app j (limit.π F j x) :=
  limMap_π_apply _ _ _

@[deprecated limit.w_apply (since := "2026-02-17")]
/--
theorem `Limit.w_apply'` / 定理 `Limit.w_apply'`

English:
theorem Limit.w_apply'
  statement: {F' : J ⥤ Type v} {j j' : J} {x : (limit F' : Type v)}
  proof: limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]

中文:
定理 极限.w_apply'
  结论: {F' : J ⥤ 类型v} {j j' : J} {x : (limit F' : 类型v)}
  证明: limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]

Depends on / 依赖: limit.w_apply, w_apply
-/
theorem Limit.w_apply' {F' : J ⥤ Type v} {j j' : J} {x : (limit F' : Type v)}
    (f : j ⟶ j') : F'.map f (limit.π F' j x) = limit.π F' j' x :=
  limit.w_apply _ _ _

@[deprecated limit.lift_π_apply (since := "2026-02-17")]
/--
theorem `Limit.lift_π_apply'` / 定理 `Limit.lift_π_apply'`

English:
theorem Limit.lift_π_apply'
  given: (F' : J ⥤ Type v) (s : Cone F') (j : J) (x : s.pt)
  proof: limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]

中文:
定理 极限.lift_π_apply'
  条件: (F' : J ⥤ 类型v) (s : 锥 F') (j : J) (x : s.pt)
  证明: limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]

Depends on / 依赖: limit.lift_
-/
theorem Limit.lift_π_apply' (F' : J ⥤ Type v) (s : Cone F') (j : J) (x : s.pt) :
    limit.π F' j (limit.lift F' s x) = s.π.app j x :=
  limit.lift_π_apply _ _ _

@[deprecated limMap_π_apply (since := "2026-02-17")]
/--
theorem `Limit.map_π_apply'` / 定理 `Limit.map_π_apply'`

English:
theorem Limit.map_π_apply'
  statement: {F' G' : J ⥤ Type v} (α : F' ⟶ G') (j : J)
  proof: limMap_π_apply _ _ _

中文:
定理 极限.map_π_apply'
  结论: {F' G' : J ⥤ 类型v} (α : F' ⟶ G') (j : J)
  证明: limMap_π_apply _ _ _
-/
theorem Limit.map_π_apply' {F' G' : J ⥤ Type v} (α : F' ⟶ G') (j : J)
    (x : (limit F' : Type v)) : limit.π G' j (limMap α x) = α.app j (limit.π F' j x) :=
  limMap_π_apply _ _ _

end UnivLE

/-!
In this section we verify that instances are available as expected.
-/
section instances

example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max w v)) := inferInstance
example : HasLimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max v w)) := inferInstance

example : HasLimitsOfSize.{0, 0, v, v + 1} (Type v) := inferInstance
example : HasLimitsOfSize.{v, v, v, v + 1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasLimitsOfSize.{v, v, u, u + 1} (Type u) := inferInstance

end instances

end CategoryTheory.Limits.Types
