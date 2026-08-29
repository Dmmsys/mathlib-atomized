/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
a property of objects in the functor category `J ⥤ C`, and show that
it is stable under colimits of shape `K'` when they
commute to limits of shape `K` (resp. to finite limits).

-/

public section

namespace CategoryTheory

open Limits

variable {J J' C D : Type*} (K K' : Type*)
  [Category* K] [Category* K'] [Category* J] [Category* J'] [Category* C] [Category* D]

namespace ObjectProperty

variable {K} in
/--
Definition of `preservesLimit` / `preservesLimit` 的定义

English:
abbreviation preservesLimit
  signature: (F : K ⥤ J)
  body: PreservesLimit F

@[simp]

中文:
缩写 preservesLimit
  签名: (F : K ⥤ J)
  定义体: PreservesLimit F

@[simp]

Depends on / 依赖: PreservesLimit
-/
abbrev preservesLimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesLimit F

@[simp]
/--
lemma `preservesLimit_iff` / 引理 `preservesLimit_iff`

English:
lemma preservesLimit_iff
  given: (F : K ⥤ J) (G : J ⥤ C)
  proof: Iff.rfl

中文:
引理 preservesLimit_iff
  条件: (F : K ⥤ J) (G : J ⥤ C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma preservesLimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesLimit F G ↔ PreservesLimit F G := Iff.rfl

/--
lemma `congr_preservesLimit` / 引理 `congr_preservesLimit`

English:
lemma congr_preservesLimit
  given: {F F' : K ⥤ J} (e : F ≅ F')
  proof: by
  ext G
  simp_rw [preservesLimit_iff]
  exact ⟨fun h => preservesLimit_of_iso_diagram _ e,
    fun h => preservesLimit_of_iso_diagram _ e.symm⟩

中文:
引理 congr_preservesLimit
  条件: {F F' : K ⥤ J} (e : F ≅ F')
  证明: by
  ext G
  simp_rw [preservesLimit_iff]
  exact ⟨fun h => preservesLimit_of_iso_diagram _ e,
    fun h => preservesLimit_of_iso_diagram _ e.symm⟩

Depends on / 依赖: e.symm, preservesLimit, preservesLimit_iff, preservesLimit_of_iso_diagram, simp_rw
-/
lemma congr_preservesLimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesLimit (C := C) F = preservesLimit (C := C) F' := by
  ext G
  simp_rw [preservesLimit_iff]
  exact ⟨fun h => preservesLimit_of_iso_diagram _ e,
    fun h => preservesLimit_of_iso_diagram _ e.symm⟩

instance (F : K ⥤ J) : (preservesLimit (C := C) F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesLimit_of_natIso _ e

variable {K} in
/--
Definition of `preservesColimit` / `preservesColimit` 的定义

English:
abbreviation preservesColimit
  signature: (F : K ⥤ J)
  body: PreservesColimit F

@[simp]

中文:
缩写 preservesColimit
  签名: (F : K ⥤ J)
  定义体: PreservesColimit F

@[simp]

Depends on / 依赖: PreservesColimit
-/
abbrev preservesColimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesColimit F

@[simp]
/--
lemma `preservesColimit_iff` / 引理 `preservesColimit_iff`

English:
lemma preservesColimit_iff
  given: (F : K ⥤ J) (G : J ⥤ C)
  proof: Iff.rfl

中文:
引理 preservesColimit_iff
  条件: (F : K ⥤ J) (G : J ⥤ C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma preservesColimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesColimit F G ↔ PreservesColimit F G := Iff.rfl

/--
lemma `congr_preservesColimit` / 引理 `congr_preservesColimit`

English:
lemma congr_preservesColimit
  given: {F F' : K ⥤ J} (e : F ≅ F')
  proof: by
  ext G
  simp_rw [preservesColimit_iff]
  exact ⟨fun h => preservesColimit_of_iso_diagram _ e,
    fun h => preservesColimit_of_iso_diagram _ e.symm⟩

中文:
引理 congr_preservesColimit
  条件: {F F' : K ⥤ J} (e : F ≅ F')
  证明: by
  ext G
  simp_rw [preservesColimit_iff]
  exact ⟨fun h => preservesColimit_of_iso_diagram _ e,
    fun h => preservesColimit_of_iso_diagram _ e.symm⟩

Depends on / 依赖: e.symm, preservesColimit, preservesColimit_iff, preservesColimit_of_iso_diagram, simp_rw
-/
lemma congr_preservesColimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesColimit (C := C) F = preservesColimit (C := C) F' := by
  ext G
  simp_rw [preservesColimit_iff]
  exact ⟨fun h => preservesColimit_of_iso_diagram _ e,
    fun h => preservesColimit_of_iso_diagram _ e.symm⟩

instance (F : K ⥤ J) : (preservesColimit (C := C) F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesColimit_of_natIso _ e

/--
Definition of `preservesLimitsOfShape` / `preservesLimitsOfShape` 的定义

English:
abbreviation preservesLimitsOfShape
  signature: : ObjectProperty (J ⥤ C)
  body: PreservesLimitsOfShape K

@[simp]

中文:
缩写 preservesLimitsOfShape
  签名: : Object命题erty (J ⥤ C)
  定义体: PreservesLimitsOfShape K

@[simp]

Depends on / 依赖: PreservesLimitsOfShape
-/
abbrev preservesLimitsOfShape : ObjectProperty (J ⥤ C) := PreservesLimitsOfShape K

@[simp]
/--
lemma `preservesLimitsOfShape_iff` / 引理 `preservesLimitsOfShape_iff`

English:
lemma preservesLimitsOfShape_iff
  given: (F : J ⥤ C)
  proof: Iff.rfl

中文:
引理 preservesLimitsOfShape_iff
  条件: (F : J ⥤ C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl

/--
lemma `preservesLimitsOfShape_eq_iSup` / 引理 `preservesLimitsOfShape_eq_iSup`

English:
lemma preservesLimitsOfShape_eq_iSup
  proof: by
  ext G
  simp only [preservesLimitsOfShape_iff, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ => inferInstance, fun _ => ⟨inferInstance⟩⟩

中文:
引理 preservesLimitsOfShape_eq_iSup
  证明: by
  ext G
  simp only [preservesLimitsOfShape_iff, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ => inferInstance, fun _ => ⟨inferInstance⟩⟩
-/
lemma preservesLimitsOfShape_eq_iSup :
    preservesLimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesLimit F := by
  ext G
  simp only [preservesLimitsOfShape_iff, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ => inferInstance, fun _ => ⟨inferInstance⟩⟩

variable (J C) {K K'} in
/--
lemma `congr_preservesLimitsOfShape` / 引理 `congr_preservesLimitsOfShape`

English:
lemma congr_preservesLimitsOfShape
  given: (e : K ≌ K')
  proof: by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ => preservesLimitsOfShape_of_equiv e _,
    fun _ => preservesLimitsOfShape_of_equiv e.symm _⟩

中文:
引理 congr_preservesLimitsOfShape
  条件: (e : K ≌ K')
  证明: by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ => preservesLimitsOfShape_of_equiv e _,
    fun _ => preservesLimitsOfShape_of_equiv e.symm _⟩

Depends on / 依赖: e.symm, preservesLimitsOfShape, preservesLimitsOfShape_iff, preservesLimitsOfShape_of_equiv
-/
lemma congr_preservesLimitsOfShape (e : K ≌ K') :
    preservesLimitsOfShape (J := J) (C := C) K = preservesLimitsOfShape K' := by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ => preservesLimitsOfShape_of_equiv e _,
    fun _ => preservesLimitsOfShape_of_equiv e.symm _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (preservesLimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms
  body: by
  rw [preservesLimitsOfShape_eq_iSup]
  infer_instance

中文:
实例 :
  签名: (preservesLimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms
  定义体: by
  rw [preservesLimitsOfShape_eq_iSup]
  infer_instance

Depends on / 依赖: IsClosedUnderIsomorphisms, infer_instance, preservesLimitsOfShape_eq_iSup
-/
instance : (preservesLimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms := by
  rw [preservesLimitsOfShape_eq_iSup]
  infer_instance

/--
Definition of `preservesColimitsOfShape` / `preservesColimitsOfShape` 的定义

English:
abbreviation preservesColimitsOfShape
  signature: : ObjectProperty (J ⥤ C)
  body: PreservesColimitsOfShape K

@[simp]

中文:
缩写 preservesColimitsOfShape
  签名: : Object命题erty (J ⥤ C)
  定义体: PreservesColimitsOfShape K

@[simp]

Depends on / 依赖: PreservesColimitsOfShape
-/
abbrev preservesColimitsOfShape : ObjectProperty (J ⥤ C) := PreservesColimitsOfShape K

@[simp]
/--
lemma `preservesColimitsOfShape_iff` / 引理 `preservesColimitsOfShape_iff`

English:
lemma preservesColimitsOfShape_iff
  given: (F : J ⥤ C)
  proof: Iff.rfl

中文:
引理 preservesColimitsOfShape_iff
  条件: (F : J ⥤ C)
  证明: Iff.rfl

Depends on / 依赖: Cofan.inj_jointly_surjective_of_isColimit, Iff.rfl, IsStableUnderCoproductsOfShape, IsStableUnderCoproductsOfShape.mk, cofan_mk_inj, congr_hom, coproductIsCoproduct, inj_jointly_surjective_of_isColimit, mono_iff_injective, monomorphisms, monomorphisms.iff, replace
-/
lemma preservesColimitsOfShape_iff (F : J ⥤ C) :
    preservesColimitsOfShape K F ↔ PreservesColimitsOfShape K F := Iff.rfl

/--
lemma `preservesColimitsOfShape_eq_iSup` / 引理 `preservesColimitsOfShape_eq_iSup`

English:
lemma preservesColimitsOfShape_eq_iSup
  proof: by
  ext G
  simp only [preservesColimitsOfShape_iff, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ => inferInstance, fun _ => ⟨inferInstance⟩⟩

中文:
引理 preservesColimitsOfShape_eq_iSup
  证明: by
  ext G
  simp only [preservesColimitsOfShape_iff, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ => inferInstance, fun _ => ⟨inferInstance⟩⟩
-/
lemma preservesColimitsOfShape_eq_iSup :
    preservesColimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesColimit F := by
  ext G
  simp only [preservesColimitsOfShape_iff, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ => inferInstance, fun _ => ⟨inferInstance⟩⟩

variable (J C) {K K'} in
/--
lemma `congr_preservesColimitsOfShape` / 引理 `congr_preservesColimitsOfShape`

English:
lemma congr_preservesColimitsOfShape
  given: (e : K ≌ K')
  proof: by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ => preservesColimitsOfShape_of_equiv e _,
    fun _ => preservesColimitsOfShape_of_equiv e.symm _⟩

中文:
引理 congr_preservesColimitsOfShape
  条件: (e : K ≌ K')
  证明: by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ => preservesColimitsOfShape_of_equiv e _,
    fun _ => preservesColimitsOfShape_of_equiv e.symm _⟩

Depends on / 依赖: e.symm, preservesColimitsOfShape, preservesColimitsOfShape_iff, preservesColimitsOfShape_of_equiv
-/
lemma congr_preservesColimitsOfShape (e : K ≌ K') :
    preservesColimitsOfShape (J := J) (C := C) K = preservesColimitsOfShape K' := by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ => preservesColimitsOfShape_of_equiv e _,
    fun _ => preservesColimitsOfShape_of_equiv e.symm _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (preservesColimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms
  body: by
  rw [preservesColimitsOfShape_eq_iSup]
  infer_instance

中文:
实例 :
  签名: (preservesColimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms
  定义体: by
  rw [preservesColimitsOfShape_eq_iSup]
  infer_instance

Depends on / 依赖: IsClosedUnderIsomorphisms, infer_instance, preservesColimitsOfShape_eq_iSup
-/
instance : (preservesColimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms := by
  rw [preservesColimitsOfShape_eq_iSup]
  infer_instance

/--
Definition of `preservesFiniteLimits` / `preservesFiniteLimits` 的定义

English:
abbreviation preservesFiniteLimits
  signature: : ObjectProperty (J ⥤ C)
  body: PreservesFiniteLimits

@[simp]

中文:
缩写 preservesFiniteLimits
  签名: : Object命题erty (J ⥤ C)
  定义体: PreservesFiniteLimits

@[simp]

Depends on / 依赖: PreservesFiniteLimits
-/
abbrev preservesFiniteLimits : ObjectProperty (J ⥤ C) := PreservesFiniteLimits

@[simp]
/--
lemma `preservesFiniteLimits_iff` / 引理 `preservesFiniteLimits_iff`

English:
lemma preservesFiniteLimits_iff
  given: (F : J ⥤ C)
  proof: Iff.rfl

中文:
引理 preservesFiniteLimits_iff
  条件: (F : J ⥤ C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (preservesFiniteLimits (J := J) (C := C)).IsClosedUnderIsomorphisms
  body: preservesFiniteLimits_of_natIso e

中文:
实例 :
  签名: (preservesFiniteLimits (J := J) (C := C)).IsClosedUnderIsomorphisms
  定义体: preservesFiniteLimits_of_natIso e

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
instance : (preservesFiniteLimits (J := J) (C := C)).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesFiniteLimits_of_natIso e

/--
Definition of `preservesFiniteColimits` / `preservesFiniteColimits` 的定义

English:
abbreviation preservesFiniteColimits
  signature: : ObjectProperty (J ⥤ C)
  body: PreservesFiniteColimits

中文:
缩写 preservesFiniteColimits
  签名: : Object命题erty (J ⥤ C)
  定义体: PreservesFiniteColimits

Depends on / 依赖: PreservesFiniteColimits
-/
abbrev preservesFiniteColimits : ObjectProperty (J ⥤ C) := PreservesFiniteColimits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (preservesFiniteColimits (J := J) (C := C)).IsClosedUnderIsomorphisms
  body: preservesFiniteColimits_of_natIso e

@[simp]

中文:
实例 :
  签名: (preservesFiniteColimits (J := J) (C := C)).IsClosedUnderIsomorphisms
  定义体: preservesFiniteColimits_of_natIso e

@[simp]

Depends on / 依赖: IsClosedUnderIsomorphisms
-/
instance : (preservesFiniteColimits (J := J) (C := C)).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesFiniteColimits_of_natIso e

@[simp]
/--
lemma `preservesFiniteColimits_iff` / 引理 `preservesFiniteColimits_iff`

English:
lemma preservesFiniteColimits_iff
  given: (F : J ⥤ C)
  proof: Iff.rfl

中文:
引理 preservesFiniteColimits_iff
  条件: (F : J ⥤ C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma preservesFiniteColimits_iff (F : J ⥤ C) :
    preservesFiniteColimits F ↔ PreservesFiniteColimits F := Iff.rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: K' C]
  body: by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} => ⟨fun {c} hc =>
      ⟨evaluationJointlyReflectsLimits _
        (fun k' => isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents
       

中文:
实例 [HasColimitsOfShape
  签名: K' C]
  定义体: by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} => ⟨fun {c} hc =>
      ⟨evaluationJointlyReflectsLimits _
        (fun k' => isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents
       
-/
instance [HasColimitsOfShape K' C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderColimitsOfShape K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} => ⟨fun {c} hc =>
      ⟨evaluationJointlyReflectsLimits _
        (fun k' => isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents
        (fun j => (colimit.isColimit (h.diag.flip.obj j)).coconePointUniqueUpToIso
          (isColimitOfPreserves ((evaluation _ _).obj j) h.isColimit))
    exact preservesLimitsOfShape_of_natIso e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasColimitsOfShape
  signature: K' C] [HasExactColimitsOfShape K' C] :
  body: by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ => (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

中文:
实例 [HasColimitsOfShape
  签名: K' C] [HasExactColimitsOfShape K' C] :
  定义体: by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ => (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

Depends on / 依赖: h.isColimit, h.prop_diag_obj, isColimit, preservesLimitsOfShape, prop_diag_obj, prop_of_isColimit
-/
instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ => (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

end ObjectProperty

end CategoryTheory
