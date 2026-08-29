/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Bhavik Mehta, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Compactification.StoneCech
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Category.CompHausLike.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `TopCat`.
The fully faithful functor `CompHaus ⥤ TopCat` is denoted `compHausToTop`.

**Note:** The file `Mathlib/Topology/Category/Compactum.lean` provides the equivalence between
`Compactum`, which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`CompactumToCompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `CompactumToCompHaus.isEquivalence`.
See `Mathlib/Topology/Category/Compactum.lean` for a more detailed discussion where these
definitions are introduced.

## Implementation

The category `CompHaus` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

@[expose] public section


universe v u

open CategoryTheory CompHausLike

/--
Definition of `CompHaus` / `CompHaus` 的定义

English:
abbreviation CompHaus
  body: CompHausLike (fun _ => True)

中文:
缩写 CompHaus
  定义体: CompHausLike (fun _ => True)

Depends on / 依赖: CompHausLike
-/
abbrev CompHaus := CompHausLike (fun _ => True)

namespace CompHaus

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CompHaus
  body: ⟨{ toTop := TopCat.of PEmpty, prop := trivial}⟩

中文:
实例 :
  签名: 可居 CompHaus
  定义体: ⟨{ toTop := TopCat.of PEmpty, prop := trivial}⟩

Depends on / 依赖: PEmpty, TopCat, TopCat.of
-/
instance : Inhabited CompHaus :=
  ⟨{ toTop := TopCat.of PEmpty, prop := trivial}⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort CompHaus Type*
  body: ⟨fun X => X.toTop⟩

中文:
实例 :
  签名: CoeSort CompHaus 类型
  定义体: ⟨fun X => X.toTop⟩

Depends on / 依赖: X.toTop
-/
instance : CoeSort CompHaus Type* :=
  ⟨fun X => X.toTop⟩

instance {X : CompHaus} : CompactSpace X :=
  X.is_compact

instance {X : CompHaus} : T2Space X :=
  X.is_hausdorff

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasProp (fun _ => True) X
  body: ⟨trivial⟩

中文:
实例 :
  签名: 有命题 (fun _ => 真) X
  定义体: ⟨trivial⟩
-/
instance : HasProp (fun _ => True) X := ⟨trivial⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: : CompHaus
  body: CompHausLike.of _ X

中文:
缩写 of
  签名: : CompHaus
  定义体: CompHausLike.of _ X

Depends on / 依赖: CompHausLike, CompHausLike.of
-/
abbrev of : CompHaus := CompHausLike.of _ X

end CompHaus

/--
Definition of `compHausToTop` / `compHausToTop` 的定义

English:
abbreviation compHausToTop
  signature: : CompHaus.{u} ⥤ TopCat.{u}
  body: CompHausLike.compHausLikeToTop _

中文:
缩写 compHausToTop
  签名: : CompHaus.{u} ⥤ 顶元素范畴.{u}
  定义体: CompHausLike.compHausLikeToTop _

Depends on / 依赖: CompHausLike, CompHausLike.compHausLikeToTop, compHausLikeToTop
-/
abbrev compHausToTop : CompHaus.{u} ⥤ TopCat.{u} :=
  CompHausLike.compHausLikeToTop _

/-- (Implementation) The object part of the compactification functor from topological spaces to
compact Hausdorff spaces.
-/
@[simps!]
/--
Definition of `stoneCechObj` / `stoneCechObj` 的定义

English:
definition stoneCechObj
  signature: (X : TopCat)
  body: CompHaus.of (StoneCech X)

中文:
定义 stoneCechObj
  签名: (X : 顶元素范畴)
  定义体: CompHaus.of (StoneCech X)

Depends on / 依赖: CompHaus, CompHaus.of, StoneCech
-/
def stoneCechObj (X : TopCat) : CompHaus :=
  CompHaus.of (StoneCech X)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `stoneCechEquivalence` / `stoneCechEquivalence` 的定义

English:
definition stoneCechEquivalence
  signature: (X : TopCat.{u}) (Y : CompHaus.{u})
  body: TopCat.ofHom
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.hom.hom.2.comp (@continuous_stoneCechUnit X _) }
  invFun f := CompHausLike.ofHom _
    { toFun := stoneCechExtend f.hom.2
      continuous_toFun := continuous_stoneCechExtend f.hom.2 }
  left_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext x
    refine congr_fun ?_ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    · rintro _ ⟨y, rfl⟩
      apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
      apply continuous_stoneCechUnit
  right_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext
    exact congr_fun (stoneCechExtend_extends hf) _

中文:
定义 stoneCechEquivalence
  签名: (X : 顶元素范畴.{u}) (Y : CompHaus.{u})
  定义体: TopCat.ofHom
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.hom.hom.2.comp (@continuous_stoneCechUnit X _) }
  invFun f := CompHausLike.ofHom _
    { toFun := stoneCechExtend f.hom.2
      continuous_toFun := continuous_stoneCechExtend f.hom.2 }
  left_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext x
    refine congr_fun ?_ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    · rintro _ ⟨y, rfl⟩
      apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
      apply continuous_stoneCechUnit
  right_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext
    exact congr_fun (stoneCechExtend_extends hf) _

Depends on / 依赖: TopCat, TopCat.ofHom
-/
noncomputable def stoneCechEquivalence (X : TopCat.{u}) (Y : CompHaus.{u}) :
    (stoneCechObj X ⟶ Y) ≃ (X ⟶ compHausToTop.obj Y) where
  toFun f := TopCat.ofHom
    { toFun := f ∘ stoneCechUnit
      continuous_toFun := f.hom.hom.2.comp (@continuous_stoneCechUnit X _) }
  invFun f := CompHausLike.ofHom _
    { toFun := stoneCechExtend f.hom.2
      continuous_toFun := continuous_stoneCechExtend f.hom.2 }
  left_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext x
    refine congr_fun ?_ x
    apply Continuous.ext_on denseRange_stoneCechUnit (continuous_stoneCechExtend _) hf
    · rintro _ ⟨y, rfl⟩
      apply congr_fun (stoneCechExtend_extends (hf.comp _)) y
      apply continuous_stoneCechUnit
  right_inv := by
    rintro ⟨f, hf : Continuous f⟩
    ext
    exact congr_fun (stoneCechExtend_extends hf) _

/--
Definition of `topToCompHaus` / `topToCompHaus` 的定义

English:
definition topToCompHaus
  signature: : TopCat.{u} ⥤ CompHaus.{u}
  body: Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

中文:
定义 topToCompHaus
  签名: : 顶元素范畴.{u} ⥤ CompHaus.{u}
  定义体: Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

Depends on / 依赖: Adjunction, Adjunction.leftAdjointOfEquiv, leftAdjointOfEquiv, stoneCechEquivalence
-/
noncomputable def topToCompHaus : TopCat.{u} ⥤ CompHaus.{u} :=
  Adjunction.leftAdjointOfEquiv stoneCechEquivalence.{u} fun _ _ _ _ _ => rfl

/--
theorem `topToCompHaus_obj` / 定理 `topToCompHaus_obj`

English:
theorem topToCompHaus_obj
  given: (X : TopCat)
  statement: ↥(topToCompHaus.obj X) = StoneCech X
  proof: rfl

中文:
定理 topToCompHaus_obj
  条件: (X : 顶元素范畴)
  结论: ↥(topToCompHaus.obj X) = StoneCech X
  证明: rfl
-/
theorem topToCompHaus_obj (X : TopCat) : ↥(topToCompHaus.obj X) = StoneCech X :=
  rfl

/--
Instance `compHausToTop.reflective` / 实例 `compHausToTop.reflective`

English:
instance compHausToTop.reflective
  signature: : Reflective compHausToTop where
  body: topToCompHaus
  adj := Adjunction.adjunctionOfEquivLeft _ _

中文:
实例 compHausToTop.reflective
  签名: : 反射 compHausToTop where
  定义体: topToCompHaus
  adj := Adjunction.adjunctionOfEquivLeft _ _

Depends on / 依赖: topToCompHaus
-/
noncomputable instance compHausToTop.reflective : Reflective compHausToTop where
  L := topToCompHaus
  adj := Adjunction.adjunctionOfEquivLeft _ _

/--
Instance `compHausToTop.createsLimits` / 实例 `compHausToTop.createsLimits`

English:
instance compHausToTop.createsLimits
  signature: : CreatesLimits compHausToTop
  body: monadicCreatesLimits _

中文:
实例 compHausToTop.createsLimits
  签名: : CreatesLimits compHausToTop
  定义体: monadicCreatesLimits _

Depends on / 依赖: monadicCreatesLimits
-/
noncomputable instance compHausToTop.createsLimits : CreatesLimits compHausToTop :=
  monadicCreatesLimits _

/--
Instance `CompHaus.hasLimits` / 实例 `CompHaus.hasLimits`

English:
instance CompHaus.hasLimits
  signature: : Limits.HasLimits CompHaus
  body: hasLimits_of_hasLimits_createsLimits compHausToTop

中文:
实例 CompHaus.hasLimits
  签名: : Limits.有极限 CompHaus
  定义体: hasLimits_of_hasLimits_createsLimits compHausToTop

Depends on / 依赖: compHausToTop, hasLimits_of_hasLimits_createsLimits
-/
instance CompHaus.hasLimits : Limits.HasLimits CompHaus :=
  hasLimits_of_hasLimits_createsLimits compHausToTop

/--
Instance `CompHaus.hasColimits` / 实例 `CompHaus.hasColimits`

English:
instance CompHaus.hasColimits
  signature: : Limits.HasColimits CompHaus
  body: hasColimits_of_reflective compHausToTop

中文:
实例 CompHaus.hasColimits
  签名: : Limits.有余极限 CompHaus
  定义体: hasColimits_of_reflective compHausToTop

Depends on / 依赖: compHausToTop, hasColimits_of_reflective
-/
instance CompHaus.hasColimits : Limits.HasColimits CompHaus :=
  hasColimits_of_reflective compHausToTop

namespace CompHaus

/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u})
  body: letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { pt := {
      toTop := (TopCat.limitCone FF).pt
      is_compact := by
        change CompactSpace { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        have :
          { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } := by
          ext1
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        rw [this]
        apply isClosed_iInter
        intro i
        apply isClosed_iInter
        intro j
        apply isClosed_iInter
        intro f
        apply isClosed_eq
        · exact ((F.map f).hom.hom.continuous).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance
      prop := trivial }
    π := {
      app := fun j => InducedCategory.homMk ((TopCat.limitCone FF).π.app j)
      naturality := by
        intro _ _ f
        ext ⟨x, hx⟩
        simp only [Functor.const_obj_map]
        exact (hx f).symm } }

中文:
定义 limitCone
  签名: {J : 类型v} [小范畴 J] (F : J ⥤ CompHaus.{最大值 v u})
  定义体: letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { pt := {
      toTop := (TopCat.limitCone FF).pt
      is_compact := by
        change CompactSpace { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        have :
          { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } := by
          ext1
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        rw [this]
        apply isClosed_iInter
        intro i
        apply isClosed_iInter
        intro j
        apply isClosed_iInter
        intro f
        apply isClosed_eq
        · exact ((F.map f).hom.hom.continuous).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance
      prop := trivial }
    π := {
      app := fun j => InducedCategory.homMk ((TopCat.limitCone FF).π.app j)
      naturality := by
        intro _ _ f
        ext ⟨x, hx⟩
        simp only [Functor.const_obj_map]
        exact (hx f).symm } }

Depends on / 依赖: CompactSpace, F.map, F.obj, IsClosed, IsClosed.isCompact, Set.mem_iInter, Set.mem_ofPred_eq, TopCat, TopCat.limitCone, compHausToTop, isClosed_iInter, isCompact, isCompact_iff_compactSpace, is_compact, limitCone, mem_iInter, mem_ofPred_eq
-/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) : Limits.Cone F :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { pt := {
      toTop := (TopCat.limitCone FF).pt
      is_compact := by
        change CompactSpace { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j }
        rw [← isCompact_iff_compactSpace]
        apply IsClosed.isCompact
        have :
          { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), F.map f (u i) = u j } =
            ⋂ (i : J) (j : J) (f : i ⟶ j), { u | F.map f (u i) = u j } := by
          ext1
          simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        rw [this]
        apply isClosed_iInter
        intro i
        apply isClosed_iInter
        intro j
        apply isClosed_iInter
        intro f
        apply isClosed_eq
        · exact ((F.map f).hom.hom.continuous).comp (continuous_apply i)
        · exact continuous_apply j
      is_hausdorff :=
        show T2Space { u : forall j, F.obj j | forall {i j : J} (f : i ⟶ j), (F.map f) (u i) = u j } from
          inferInstance
      prop := trivial }
    π := {
      app := fun j => InducedCategory.homMk ((TopCat.limitCone FF).π.app j)
      naturality := by
        intro _ _ f
        ext ⟨x, hx⟩
        simp only [Functor.const_obj_map]
        exact (hx f).symm } }

/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u})
  body: letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { lift := fun S => InducedCategory.homMk
      ((TopCat.limitConeIsLimit FF).lift (compHausToTop.mapCone S))
    uniq := fun S m hm => InducedCategory.hom_ext
      ((TopCat.limitConeIsLimit FF).uniq (compHausToTop.mapCone S) _ (fun j => by
        simp [← hm]
        rfl)) }

中文:
定义 limitConeIsLimit
  签名: {J : 类型v} [小范畴 J] (F : J ⥤ CompHaus.{最大值 v u})
  定义体: letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { lift := fun S => InducedCategory.homMk
      ((TopCat.limitConeIsLimit FF).lift (compHausToTop.mapCone S))
    uniq := fun S m hm => InducedCategory.hom_ext
      ((TopCat.limitConeIsLimit FF).uniq (compHausToTop.mapCone S) _ (fun j => by
        simp [← hm]
        rfl)) }

Depends on / 依赖: InducedCategory, InducedCategory.homMk, InducedCategory.hom_ext, TopCat, TopCat.limitConeIsLimit, compHausToTop, compHausToTop.mapCone, hom_ext, limitConeIsLimit, mapCone
-/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ CompHaus.{max v u}) :
    Limits.IsLimit.{v} (limitCone.{v, u} F) :=
  letI FF : J ⥤ TopCat := F ⋙ compHausToTop
  { lift := fun S => InducedCategory.homMk
      ((TopCat.limitConeIsLimit FF).lift (compHausToTop.mapCone S))
    uniq := fun S m hm => InducedCategory.hom_ext
      ((TopCat.limitConeIsLimit FF).uniq (compHausToTop.mapCone S) _ (fun j => by
        simp [← hm]
        rfl)) }

/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {X Y : CompHaus.{u}} (f : X ⟶ Y)
  statement: Epi f ↔ Function.Surjective f
  proof: by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let D := ({y} : Set Y)
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
    have : CompactSpace (ULift.{u} <| Set.Icc (0 : Real) 1) := Homeomorph.ulift.symm.compactSpace
    have : T2Space (ULift.{u} <| Set.Icc (0 : Real) 1) := Homeomorph.ulift.symm.t2Space
    let Z := of (ULift.{u} <| Set.Icc (0 : Real) 1)
    let g : Y ⟶ Z := ofHom _
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uliftUp.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ofHom _
      ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x : 4
      simp [g, h, Z, hφ0 (Set.mem_range_self x)]
    apply_fun fun e => (e y).down.1 at H
    dsimp [g, h, Z] at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map

中文:
定理 epi_iff_surjective
  条件: {X Y : CompHaus.{u}} (f : X ⟶ Y)
  结论: 满态射 f ↔ 函数.满射 f
  证明: by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let D := ({y} : Set Y)
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
    have : CompactSpace (ULift.{u} <| Set.Icc (0 : Real) 1) := Homeomorph.ulift.symm.compactSpace
    have : T2Space (ULift.{u} <| Set.Icc (0 : Real) 1) := Homeomorph.ulift.symm.t2Space
    let Z := of (ULift.{u} <| Set.Icc (0 : Real) 1)
    let g : Y ⟶ Z := ofHom _
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uliftUp.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ofHom _
      ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x : 4
      simp [g, h, Z, hφ0 (Set.mem_range_self x)]
    apply_fun fun e => (e y).down.1 at H
    dsimp [g, h, Z] at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map

Depends on / 依赖: CompactSpace, Disjoint, Function, Function.Surjective, Homeomorph, Homeomorph.ulift.symm.compactSp, IsClosed, Set.Icc, Set.disjoint_singleton_right, Set.range, Surjective, compactSp, continuous, contrapose, disjoint_singleton_right, exists_continuous_zero_one_of_isClosed, f.hom.hom.continuous, isClosed, isClosed_singleton, isCompact_range
-/
theorem epi_iff_surjective {X Y : CompHaus.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let D := ({y} : Set Y)
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
    have : CompactSpace (ULift.{u} <| Set.Icc (0 : Real) 1) := Homeomorph.ulift.symm.compactSpace
    have : T2Space (ULift.{u} <| Set.Icc (0 : Real) 1) := Homeomorph.ulift.symm.t2Space
    let Z := of (ULift.{u} <| Set.Icc (0 : Real) 1)
    let g : Y ⟶ Z := ofHom _
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uliftUp.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ofHom _
      ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x : 4
      simp [g, h, Z, hφ0 (Set.mem_range_self x)]
    apply_fun fun e => (e y).down.1 at H
    dsimp [g, h, Z] at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget CompHaus).epi_of_epi_map

end CompHaus

/--
Definition of `compHausLikeToCompHaus` / `compHausLikeToCompHaus` 的定义

English:
abbreviation compHausLikeToCompHaus
  signature: (P : TopCat -> Prop)
  body: CompHausLike.toCompHausLike (by simp only [implies_true])

中文:
缩写 compHausLikeToCompHaus
  签名: (P : 顶元素范畴 -> 命题)
  定义体: CompHausLike.toCompHausLike (by simp only [implies_true])

Depends on / 依赖: CompHausLike, CompHausLike.toCompHausLike, implies_true, toCompHausLike
-/
abbrev compHausLikeToCompHaus (P : TopCat -> Prop) : CompHausLike P ⥤ CompHaus :=
  CompHausLike.toCompHausLike (by simp only [implies_true])
