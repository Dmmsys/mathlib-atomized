/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Joël Riou
-/
module

public import Mathlib.Logic.UnivLE
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise

/-!
# Colimits in the category of types

We show that the category of types has all colimits, by providing the usual concrete models.

-/

@[expose] public section

universe u' v u w

namespace CategoryTheory

open Limits ConcreteCategory

variable {J : Type v} [Category.{w} J]

namespace Functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Small.{u}
  signature: J] (F
  body: small_of_surjective Quot.mk_surjective

中文:
实例 [Small.{u}
  签名: J] (F
  定义体: small_of_surjective Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective, small_of_surjective
-/
instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (F.ColimitType) :=
  small_of_surjective Quot.mk_surjective

variable (F : J ⥤ Type u)

/-- If `F : J ⥤ Type u`, then the data of a "type-theoretic" cocone of `F`
with a point in `Type u` is the same as the data of a cocone (in a categorical sense). -/
@[simps apply_pt symm_apply_pt apply_ι_app symm_apply_ι]
/--
Definition of `coconeTypesEquiv` / `coconeTypesEquiv` 的定义

English:
definition coconeTypesEquiv
  signature: : CoconeTypes.{u} F ≃ Cocone F where
  body: { pt := c.pt
      ι := { app j := ↾(c.ι j) } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x }
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 coconeTypesEquiv
  签名: : 余coneTypes.{u} F ≃ 余锥 F where
  定义体: { pt := c.pt
      ι := { app j := ↾(c.ι j) } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x }
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, c.pt, congr_hom, invFun, left_inv, right_inv
-/
def coconeTypesEquiv : CoconeTypes.{u} F ≃ Cocone F where
  toFun c :=
    { pt := c.pt
      ι := { app j := ↾(c.ι j) } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x }
  left_inv _ := rfl
  right_inv _ := rfl

variable {F}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `CoconeTypes.isColimit_iff` / 引理 `CoconeTypes.isColimit_iff`

English:
lemma CoconeTypes.isColimit_iff
  given: (c : CoconeTypes.{u} F)
  proof: by
  constructor
  · intro hc
    exact
     ⟨{ desc s := ↾fun x => hc.desc (F.coconeTypesEquiv.symm s) x
        fac s j := by
          ext x
          exact congr_fun (hc.fac (F.coconeTypesEquiv.symm s) j) x
        uniq s m hm := by
          ext x
          exact congr_fun (hc.funext fun j => funext fun y => by simp [← hm j]) x }⟩
  · rintro ⟨hc⟩
    classical
    refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
    · let f (z : F.ColimitType) : ULift.{u} Bool := ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      suffices forall z, hc.desc (F.coconeTypesEquiv (F.coconeTypes.postcomp f))
          (F.descColimitType c z) = f z by rw [← this x, h, ← this y]
      intro z
      obtain ⟨j, z, rfl⟩ := F.ιColimitType_jointly_surjective z
      exact ConcreteCategory.congr_hom (hc.fac _ j) z
    · let f₁ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun _ => ULift.up true
      let f₂ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun x => ULift.up (exists a, F.descColimitType c a = x)
      suffices f₁ = f₂ by
        have := ConcreteCategory.congr_hom this x
        simpa [f₁, f₂] using this
      refine hc.hom_ext fun j => ?_
      ext x
      simpa [f₁, f₂] using ⟨F.ιColimitType j x, by simp⟩

中文:
引理 余coneTypes.isColimit_iff
  条件: (c : 余coneTypes.{u} F)
  证明: by
  constructor
  · intro hc
    exact
     ⟨{ desc s := ↾fun x => hc.desc (F.coconeTypesEquiv.symm s) x
        fac s j := by
          ext x
          exact congr_fun (hc.fac (F.coconeTypesEquiv.symm s) j) x
        uniq s m hm := by
          ext x
          exact congr_fun (hc.funext fun j => funext fun y => by simp [← hm j]) x }⟩
  · rintro ⟨hc⟩
    classical
    refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
    · let f (z : F.ColimitType) : ULift.{u} Bool := ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      suffices forall z, hc.desc (F.coconeTypesEquiv (F.coconeTypes.postcomp f))
          (F.descColimitType c z) = f z by rw [← this x, h, ← this y]
      intro z
      obtain ⟨j, z, rfl⟩ := F.ιColimitType_jointly_surjective z
      exact ConcreteCategory.congr_hom (hc.fac _ j) z
    · let f₁ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun _ => ULift.up true
      let f₂ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun x => ULift.up (exists a, F.descColimitType c a = x)
      suffices f₁ = f₂ by
        have := ConcreteCategory.congr_hom this x
        simpa [f₁, f₂] using this
      refine hc.hom_ext fun j => ?_
      ext x
      simpa [f₁, f₂] using ⟨F.ιColimitType j x, by simp⟩

Depends on / 依赖: ColimitType, F.ColimitType, F.coconeTyp, F.coconeTypesEquiv, F.coconeTypesEquiv.symm, ULift.up, classical, coconeTyp, coconeTypesEquiv, congr_fun, hc.desc, hc.fac, hc.funext
-/
lemma CoconeTypes.isColimit_iff (c : CoconeTypes.{u} F) :
    c.IsColimit ↔ Nonempty (Limits.IsColimit (F.coconeTypesEquiv c)) := by
  constructor
  · intro hc
    exact
     ⟨{ desc s := ↾fun x => hc.desc (F.coconeTypesEquiv.symm s) x
        fac s j := by
          ext x
          exact congr_fun (hc.fac (F.coconeTypesEquiv.symm s) j) x
        uniq s m hm := by
          ext x
          exact congr_fun (hc.funext fun j => funext fun y => by simp [← hm j]) x }⟩
  · rintro ⟨hc⟩
    classical
    refine ⟨⟨fun x y h => ?_, fun x => ?_⟩⟩
    · let f (z : F.ColimitType) : ULift.{u} Bool := ULift.up (x = z)
      suffices f x = f y by simpa [f] using this
      suffices forall z, hc.desc (F.coconeTypesEquiv (F.coconeTypes.postcomp f))
          (F.descColimitType c z) = f z by rw [← this x, h, ← this y]
      intro z
      obtain ⟨j, z, rfl⟩ := F.ιColimitType_jointly_surjective z
      exact ConcreteCategory.congr_hom (hc.fac _ j) z
    · let f₁ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun _ => ULift.up true
      let f₂ : (F.coconeTypesEquiv c).pt ⟶ (ULift.{u} Bool) :=
        ↾fun x => ULift.up (exists a, F.descColimitType c a = x)
      suffices f₁ = f₂ by
        have := ConcreteCategory.congr_hom this x
        simpa [f₁, f₂] using this
      refine hc.hom_ext fun j => ?_
      ext x
      simpa [f₁, f₂] using ⟨F.ιColimitType j x, by simp⟩

end Functor

namespace Limits.Types

/--
theorem `isColimit_iff_coconeTypesIsColimit` / 定理 `isColimit_iff_coconeTypesIsColimit`

English:
theorem isColimit_iff_coconeTypesIsColimit
  given: {F : J ⥤ Type u} (c : Cocone F)
  proof: by
  simp only [Functor.CoconeTypes.isColimit_iff, Equiv.apply_symm_apply]

中文:
定理 isColimit_iff_coconeTypesIsColimit
  条件: {F : J ⥤ 类型u} (c : 余锥 F)
  证明: by
  simp only [Functor.CoconeTypes.isColimit_iff, Equiv.apply_symm_apply]

Depends on / 依赖: CoconeTypes, Equiv.apply_symm_apply, Functor, Functor.CoconeTypes.isColimit_iff, apply_symm_apply, isColimit_iff
-/
theorem isColimit_iff_coconeTypesIsColimit {F : J ⥤ Type u} (c : Cocone F) :
    Nonempty (IsColimit c) ↔ (F.coconeTypesEquiv.symm c).IsColimit := by
  simp only [Functor.CoconeTypes.isColimit_iff, Equiv.apply_symm_apply]

/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
abbreviation colimitCocone
  signature: (F : J ⥤ Type u) [Small.{u} F.ColimitType]
  body: F.coconeTypesEquiv (F.coconeTypes.postcomp (equivShrink.{u} F.ColimitType))

中文:
缩写 colimitCocone
  签名: (F : J ⥤ 类型u) [Small.{u} F.ColimitType]
  定义体: F.coconeTypesEquiv (F.coconeTypes.postcomp (equivShrink.{u} F.ColimitType))

Depends on / 依赖: ColimitType, F.ColimitType, F.coconeTypes.postcomp, F.coconeTypesEquiv, coconeTypes, coconeTypesEquiv, equivShrink, postcomp
-/
noncomputable abbrev colimitCocone (F : J ⥤ Type u) [Small.{u} F.ColimitType] : Cocone F :=
  F.coconeTypesEquiv (F.coconeTypes.postcomp (equivShrink.{u} F.ColimitType))

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: (F : J ⥤ Type u) [Small.{u} F.ColimitType]
  body: Nonempty.some ((isColimit_iff_coconeTypesIsColimit _).2
    (F.isColimit_coconeTypes.of_equiv (equivShrink.{u} F.ColimitType) (by aesop)))

中文:
定义 colimitCoconeIsColimit
  签名: (F : J ⥤ 类型u) [Small.{u} F.ColimitType]
  定义体: Nonempty.some ((isColimit_iff_coconeTypesIsColimit _).2
    (F.isColimit_coconeTypes.of_equiv (equivShrink.{u} F.ColimitType) (by aesop)))

Depends on / 依赖: ColimitType, F.ColimitType, F.isColimit_coconeTypes.of_equiv, Nonempty, Nonempty.some, equivShrink, isColimit_coconeTypes, isColimit_iff_coconeTypesIsColimit, of_equiv
-/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type u) [Small.{u} F.ColimitType] :
    IsColimit (colimitCocone F) :=
  Nonempty.some ((isColimit_iff_coconeTypesIsColimit _).2
    (F.isColimit_coconeTypes.of_equiv (equivShrink.{u} F.ColimitType) (by aesop)))

/--
theorem `hasColimit_iff_small_colimitType` / 定理 `hasColimit_iff_small_colimitType`

English:
theorem hasColimit_iff_small_colimitType
  given: (F : J ⥤ Type u)
  proof: ⟨fun _ => small_of_injective
      ((isColimit_iff_coconeTypesIsColimit _).1 ⟨colimit.isColimit F⟩).bijective.1,
    fun _ => ⟨_, colimitCoconeIsColimit F⟩⟩

中文:
定理 hasColimit_iff_small_colimitType
  条件: (F : J ⥤ 类型u)
  证明: ⟨fun _ => small_of_injective
      ((isColimit_iff_coconeTypesIsColimit _).1 ⟨colimit.isColimit F⟩).bijective.1,
    fun _ => ⟨_, colimitCoconeIsColimit F⟩⟩

Depends on / 依赖: bijective, colimit, colimit.isColimit, colimitCoconeIsColimit, isColimit, isColimit_iff_coconeTypesIsColimit, small_of_injective
-/
theorem hasColimit_iff_small_colimitType (F : J ⥤ Type u) :
    HasColimit F ↔ Small.{u} F.ColimitType :=
  ⟨fun _ => small_of_injective
      ((isColimit_iff_coconeTypesIsColimit _).1 ⟨colimit.isColimit F⟩).bijective.1,
    fun _ => ⟨_, colimitCoconeIsColimit F⟩⟩

/--
theorem `small_colimitType_of_hasColimit` / 定理 `small_colimitType_of_hasColimit`

English:
theorem small_colimitType_of_hasColimit
  given: (F : J ⥤ Type u) [HasColimit F]
  proof: (hasColimit_iff_small_colimitType F).mp inferInstance

中文:
定理 small_colimitType_of_hasColimit
  条件: (F : J ⥤ 类型u) [有余极限 F]
  证明: (hasColimit_iff_small_colimitType F).mp inferInstance

Depends on / 依赖: hasColimit_iff_small_colimitType
-/
theorem small_colimitType_of_hasColimit (F : J ⥤ Type u) [HasColimit F] :
    Small.{u} F.ColimitType :=
  (hasColimit_iff_small_colimitType F).mp inferInstance

/--
Instance `hasColimit` / 实例 `hasColimit`

English:
instance hasColimit
  signature: [Small.{u} J] (F : J ⥤ Type u)
  body: (hasColimit_iff_small_colimitType F).mpr inferInstance

中文:
实例 hasColimit
  签名: [Small.{u} J] (F : J ⥤ 类型u)
  定义体: (hasColimit_iff_small_colimitType F).mpr inferInstance

Depends on / 依赖: hasColimit_iff_small_colimitType
-/
instance hasColimit [Small.{u} J] (F : J ⥤ Type u) : HasColimit F :=
  (hasColimit_iff_small_colimitType F).mpr inferInstance

/--
Instance `hasColimitsOfShape` / 实例 `hasColimitsOfShape`

English:
instance hasColimitsOfShape
  signature: [Small.{u} J]

中文:
实例 hasColimitsOfShape
  签名: [Small.{u} J]
-/
instance hasColimitsOfShape [Small.{u} J] : HasColimitsOfShape J (Type u) where

/-- The category of types has all colimits. -/
@[stacks 002U]
instance (priority := 1300) hasColimitsOfSize [UnivLE.{v, u}] :
    HasColimitsOfSize.{w, v} (Type u) where

section instances

example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max w v)) :=
  inferInstance
example : HasColimitsOfSize.{w, w, max v w, max (v + 1) (w + 1)} (Type (max v w)) :=
  inferInstance

example : HasColimitsOfSize.{0, 0, v, v + 1} (Type v) := inferInstance
example : HasColimitsOfSize.{v, v, v, v + 1} (Type v) := inferInstance

example [UnivLE.{v, u}] : HasColimitsOfSize.{v, v, u, u + 1} (Type u) := inferInstance

end instances

namespace TypeMax

/--
Definition of `colimitCocone` / `colimitCocone` 的定义

English:
abbreviation colimitCocone
  signature: (F : J ⥤ Type (max v u))
  body: F.coconeTypesEquiv F.coconeTypes

中文:
缩写 colimitCocone
  签名: (F : J ⥤ 类型 (最大值 v u))
  定义体: F.coconeTypesEquiv F.coconeTypes

Depends on / 依赖: F.coconeTypes, F.coconeTypesEquiv, coconeTypes, coconeTypesEquiv
-/
abbrev colimitCocone (F : J ⥤ Type (max v u)) : Cocone F :=
  F.coconeTypesEquiv F.coconeTypes

/--
Definition of `colimitCoconeIsColimit` / `colimitCoconeIsColimit` 的定义

English:
definition colimitCoconeIsColimit
  signature: (F : J ⥤ Type (max v u))
  body: (F.coconeTypes.isColimit_iff.1 F.isColimit_coconeTypes).some

中文:
定义 colimitCoconeIsColimit
  签名: (F : J ⥤ 类型 (最大值 v u))
  定义体: (F.coconeTypes.isColimit_iff.1 F.isColimit_coconeTypes).some

Depends on / 依赖: F.coconeTypes.isColimit_iff, F.isColimit_coconeTypes, coconeTypes, isColimit_coconeTypes, isColimit_iff
-/
noncomputable def colimitCoconeIsColimit (F : J ⥤ Type (max v u)) :
    IsColimit (colimitCocone F) :=
  (F.coconeTypes.isColimit_iff.1 F.isColimit_coconeTypes).some

end TypeMax

variable (F : J ⥤ Type u) [HasColimit F]

attribute [local instance] small_colimitType_of_hasColimit

/--
Definition of `colimitEquivColimitType` / `colimitEquivColimitType` 的定义

English:
definition colimitEquivColimitType
  signature: : (colimit F : Type u) ≃ F.ColimitType
  body: (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm

@[simp]

中文:
定义 colimitEquivColimitType
  签名: : (colimit F : 类型u) ≃ F.ColimitType
  定义体: (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm

@[simp]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, colimitCoconeIsColimit, equivShrink, isColimit, toEquiv, toEquiv.trans
-/
noncomputable def colimitEquivColimitType : (colimit F : Type u) ≃ F.ColimitType :=
  (IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit F) (colimitCoconeIsColimit F)).toEquiv.trans (equivShrink _).symm

@[simp]
/--
theorem `colimitEquivColimitType_symm_apply` / 定理 `colimitEquivColimitType_symm_apply`

English:
theorem colimitEquivColimitType_symm_apply
  given: (j : J) (x : F.obj j)
  proof: congr_hom (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x

@[simp]

中文:
定理 colimitEquivColimitType_symm_apply
  条件: (j : J) (x : F.obj j)
  证明: congr_hom (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x

@[simp]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_inv, congr_hom, isColimit
-/
theorem colimitEquivColimitType_symm_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F).symm (Quot.mk _ ⟨j, x⟩) = colimit.ι F j x :=
  congr_hom (IsColimit.comp_coconePointUniqueUpToIso_inv (colimit.isColimit F) _ _) x

@[simp]
/--
theorem `colimitEquivColimitType_apply` / 定理 `colimitEquivColimitType_apply`

English:
theorem colimitEquivColimitType_apply
  given: (j : J) (x : F.obj j)
  proof: by
  apply (colimitEquivColimitType F).symm.injective
  simp

中文:
定理 colimitEquivColimitType_apply
  条件: (j : J) (x : F.obj j)
  证明: by
  apply (colimitEquivColimitType F).symm.injective
  simp

Depends on / 依赖: colimitEquivColimitType, injective, symm.injective
-/
theorem colimitEquivColimitType_apply (j : J) (x : F.obj j) :
    (colimitEquivColimitType F) (colimit.ι F j x) = Quot.mk _ ⟨j, x⟩ := by
  apply (colimitEquivColimitType F).symm.injective
  simp

-- We don’t want to add `simp` to the original lemmas here.
-- `colimit.w_apply` and `colimit.ι_desc_apply` are generated (and tagged `simp`)
-- in `Mathlib/CategoryTheory/ConcreteCategory/Elementwise.lean`.
attribute [elementwise] colimit.ι_map
attribute [simp] colimit.ι_map_apply

variable {F} in
@[deprecated colimit.w_apply (since := "2026-03-06")]
/--
theorem `Colimit.w_apply` / 定理 `Colimit.w_apply`

English:
theorem Colimit.w_apply
  given: {j j' : J} {x : F.obj j} (f : j ⟶ j')
  proof: by
  rw [← comp_apply]
  exact congr_hom (colimit.w F f) x

@[deprecated colimit.ι_desc_apply (since := "2026-03-06")]

中文:
定理 余极限.w_apply
  条件: {j j' : J} {x : F.obj j} (f : j ⟶ j')
  证明: by
  rw [← comp_apply]
  exact congr_hom (colimit.w F f) x

@[deprecated colimit.ι_desc_apply (since := "2026-03-06")]

Depends on / 依赖: colimit, colimit.w, comp_apply, congr_hom
-/
theorem Colimit.w_apply {j j' : J} {x : F.obj j} (f : j ⟶ j') :
    colimit.ι F j' (F.map f x) = colimit.ι F j x := by
  rw [← comp_apply]
  exact congr_hom (colimit.w F f) x

@[deprecated colimit.ι_desc_apply (since := "2026-03-06")]
/--
theorem `Colimit.ι_desc_apply` / 定理 `Colimit.ι_desc_apply`

English:
theorem Colimit.ι_desc_apply
  given: (s : Cocone F) (j : J) (x : F.obj j)
  proof: congr_hom (colimit.ι_desc s j) x

@[deprecated colimit.ι_map_apply (since := "2026-03-06")]

中文:
定理 余极限.ι_desc_apply
  条件: (s : 余锥 F) (j : J) (x : F.obj j)
  证明: congr_hom (colimit.ι_desc s j) x

@[deprecated colimit.ι_map_apply (since := "2026-03-06")]

Depends on / 依赖: colimit, congr_hom
-/
theorem Colimit.ι_desc_apply (s : Cocone F) (j : J) (x : F.obj j) :
    colimit.desc F s (colimit.ι F j x) = s.ι.app j x :=
  congr_hom (colimit.ι_desc s j) x

@[deprecated colimit.ι_map_apply (since := "2026-03-06")]
/--
theorem `Colimit.ι_map_apply` / 定理 `Colimit.ι_map_apply`

English:
theorem Colimit.ι_map_apply
  statement: {F G : J ⥤ Type u} [HasColimitsOfShape J (Type u)]
  proof: congr_hom (colimit.ι_map α j) x

中文:
定理 余极限.ι_map_apply
  结论: {F G : J ⥤ 类型u} [有形状余极限 J (类型u)]
  证明: congr_hom (colimit.ι_map α j) x

Depends on / 依赖: colimit, congr_hom
-/
theorem Colimit.ι_map_apply {F G : J ⥤ Type u} [HasColimitsOfShape J (Type u)]
    (α : F ⟶ G) (j : J) (x : F.obj j) :
    colim.map α (colimit.ι F j x) = colimit.ι G j (α.app j x) :=
  congr_hom (colimit.ι_map α j) x

-- These were variations of the aliased lemmas with different universe variables.
-- It appears those are now strictly more powerful.
variable {F} in
/--
theorem `colimit_sound` / 定理 `colimit_sound`

English:
theorem colimit_sound
  statement: {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
  proof: by
  rw [← w]; rw [colimit.w_apply]

中文:
定理 colimit_sound
  结论: {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
  证明: by
  rw [← w]; rw [colimit.w_apply]

Depends on / 依赖: colimit, colimit.w_apply, w_apply
-/
theorem colimit_sound {j j' : J} {x : F.obj j} {x' : F.obj j'} (f : j ⟶ j')
    (w : F.map f x = x') : colimit.ι F j x = colimit.ι F j' x' := by
  rw [← w]; rw [colimit.w_apply]

variable {F} in
/--
theorem `colimit_sound'` / 定理 `colimit_sound'`

English:
theorem colimit_sound'
  statement: {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
  proof: by
  rw [← colimit.w_apply _ f]; rw [← colimit.w_apply _ f']; rw [w]

中文:
定理 colimit_sound'
  结论: {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
  证明: by
  rw [← colimit.w_apply _ f]; rw [← colimit.w_apply _ f']; rw [w]

Depends on / 依赖: colimit, colimit.w_apply, w_apply
-/
theorem colimit_sound' {j j' : J} {x : F.obj j} {x' : F.obj j'} {j'' : J}
    (f : j ⟶ j'') (f' : j' ⟶ j'') (w : F.map f x = F.map f' x') :
    colimit.ι F j x = colimit.ι F j' x' := by
  rw [← colimit.w_apply _ f]; rw [← colimit.w_apply _ f']; rw [w]

variable {F} in
/--
theorem `colimit_eq` / 定理 `colimit_eq`

English:
theorem colimit_eq
  statement: {j j' : J} {x : F.obj j} {x' : F.obj j'}
  proof: by
  apply Quot.eq.1
  simpa using! congr_arg (colimitEquivColimitType F) w

中文:
定理 colimit_eq
  结论: {j j' : J} {x : F.obj j} {x' : F.obj j'}
  证明: by
  apply Quot.eq.1
  simpa using! congr_arg (colimitEquivColimitType F) w

Depends on / 依赖: Quot.eq, colimitEquivColimitType, congr_arg
-/
theorem colimit_eq {j j' : J} {x : F.obj j} {x' : F.obj j'}
    (w : colimit.ι F j x = colimit.ι F j' x') :
      Relation.EqvGen F.ColimitTypeRel ⟨j, x⟩ ⟨j', x'⟩ := by
  apply Quot.eq.1
  simpa using! congr_arg (colimitEquivColimitType F) w

set_option backward.defeqAttrib.useBackward true in
/--
theorem `jointly_surjective_of_isColimit` / 定理 `jointly_surjective_of_isColimit`

English:
theorem jointly_surjective_of_isColimit
  statement: {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t)
  proof: by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (↾fun _ => ULift.up True :
      t.pt ⟶ (ULift.{u} Prop)) !=
    (↾fun y => ULift.up (y != x)))
  · refine h.hom_ext fun j => ?_
    ext y
    simp only [TypeCat.Fun.toFun_apply, comp_apply, hom_ofHom,
      TypeCat.Fun.coe_mk, ne_eq, true_iff]
    exact hx j y
  · intro he
    have := ConcreteCategory.congr_hom he x
    dsimp at this
    exact of_eq_true (congrArg ULift.down this).symm rfl

中文:
定理 jointly_surjective_of_isColimit
  结论: {F : J ⥤ 类型u} {t : 余锥 F} (h : 是余极限 t)
  证明: by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (↾fun _ => ULift.up True :
      t.pt ⟶ (ULift.{u} Prop)) !=
    (↾fun y => ULift.up (y != x)))
  · refine h.hom_ext fun j => ?_
    ext y
    simp only [TypeCat.Fun.toFun_apply, comp_apply, hom_ofHom,
      TypeCat.Fun.coe_mk, ne_eq, true_iff]
    exact hx j y
  · intro he
    have := ConcreteCategory.congr_hom he x
    dsimp at this
    exact of_eq_true (congrArg ULift.down this).symm rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, TypeCat, TypeCat.Fun.coe_mk, TypeCat.Fun.toFun_apply, ULift.down, ULift.up, coe_mk, comp_apply, congr_hom, h.hom_ext, hom_ext, hom_ofHom, ne_eq, not_exists, of_eq_true, simp_rw, t.pt, toFun_apply, true_iff
-/
theorem jointly_surjective_of_isColimit {F : J ⥤ Type u} {t : Cocone F} (h : IsColimit t)
    (x : t.pt) : exists j y, t.ι.app j y = x := by
  by_contra hx
  simp_rw [not_exists] at hx
  apply (_ : (↾fun _ => ULift.up True :
      t.pt ⟶ (ULift.{u} Prop)) !=
    (↾fun y => ULift.up (y != x)))
  · refine h.hom_ext fun j => ?_
    ext y
    simp only [TypeCat.Fun.toFun_apply, comp_apply, hom_ofHom,
      TypeCat.Fun.coe_mk, ne_eq, true_iff]
    exact hx j y
  · intro he
    have := ConcreteCategory.congr_hom he x
    dsimp at this
    exact of_eq_true (congrArg ULift.down this).symm rfl

/--
theorem `jointly_surjective` / 定理 `jointly_surjective`

English:
theorem jointly_surjective
  given: (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt)
  proof: jointly_surjective_of_isColimit h x

中文:
定理 jointly_surjective
  条件: (F : J ⥤ 类型u) {t : 余锥 F} (h : 是余极限 t) (x : t.pt)
  证明: jointly_surjective_of_isColimit h x

Depends on / 依赖: jointly_surjective_of_isColimit
-/
theorem jointly_surjective (F : J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) :
    exists (j : J) (y : F.obj j), t.ι.app j y = x := jointly_surjective_of_isColimit h x

variable {F} in
/--
theorem `jointly_surjective'` / 定理 `jointly_surjective'`

English:
theorem jointly_surjective'
  given: (x : colimit F)
  proof: jointly_surjective F (colimit.isColimit F) x

中文:
定理 jointly_surjective'
  条件: (x : colimit F)
  证明: jointly_surjective F (colimit.isColimit F) x

Depends on / 依赖: colimit, colimit.isColimit, isColimit, jointly_surjective
-/
theorem jointly_surjective' (x : colimit F) :
    exists (j : J) (y : F.obj j), colimit.ι F j y = x :=
  jointly_surjective F (colimit.isColimit F) x

/--
theorem `nonempty_of_nonempty_colimit` / 定理 `nonempty_of_nonempty_colimit`

English:
theorem nonempty_of_nonempty_colimit
  given: {F : J ⥤ Type u} [HasColimit F]
  proof: Nonempty.map Sigma.fst ∘ Quot.out ∘ (colimitEquivColimitType F).toFun

中文:
定理 nonempty_of_nonempty_colimit
  条件: {F : J ⥤ 类型u} [有余极限 F]
  证明: Nonempty.map Sigma.fst ∘ Quot.out ∘ (colimitEquivColimitType F).toFun

Depends on / 依赖: Nonempty, Nonempty.map, Quot.out, Sigma.fst, colimitEquivColimitType
-/
theorem nonempty_of_nonempty_colimit {F : J ⥤ Type u} [HasColimit F] :
    Nonempty (colimit F) -> Nonempty J :=
Nonempty.map Sigma.fst ∘ Quot.out ∘ (colimitEquivColimitType F).toFun

end CategoryTheory.Limits.Types
