/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Topology.Category.Profinite.AsLimit
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.ClopenBox
/-!

# Light profinite spaces

We construct the category `LightProfinite` of light profinite topological spaces. These are
implemented as totally disconnected second countable compact Hausdorff spaces.

This file also defines the category `LightDiagram`, which consists of those spaces that can be
written as a sequential limit (in `Profinite`) of finite sets.

We define an equivalence of categories `LightProfinite ≌ LightDiagram` and prove that these are
essentially small categories.

## Implementation

The category `LightProfinite` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

@[expose] public section

/- The basic API for `LightProfinite` is largely copied from the API of `Profinite`;
where possible, try to keep them in sync -/

universe v u

open CategoryTheory Limits Opposite FintypeCat Topology TopologicalSpace CompHausLike

/--
Definition of `LightProfinite` / `LightProfinite` 的定义

English:
abbreviation LightProfinite
  body: CompHausLike
  (fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X)

中文:
缩写 LightProfinite
  定义体: CompHausLike
  (fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X)

Depends on / 依赖: CompHausLike
-/
abbrev LightProfinite := CompHausLike
  (fun X => TotallyDisconnectedSpace X ∧ SecondCountableTopology X)

namespace LightProfinite

instance (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] : HasProp (fun Y =>
      TotallyDisconnectedSpace Y ∧ SecondCountableTopology Y) X :=
  ⟨⟨(inferInstance : TotallyDisconnectedSpace X), (inferInstance : SecondCountableTopology X)⟩⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  body: CompHausLike.of _ X

中文:
缩写 of
  签名: (X : 类型) [拓扑空间 X] [紧空间 X] [T2空间 X]
  定义体: CompHausLike.of _ X

Depends on / 依赖: CompHausLike, CompHausLike.of
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] : LightProfinite :=
  CompHausLike.of _ X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited LightProfinite
  body: ⟨LightProfinite.of PEmpty⟩

中文:
实例 :
  签名: 可居 LightProfinite
  定义体: ⟨LightProfinite.of PEmpty⟩

Depends on / 依赖: LightProfinite, LightProfinite.of, PEmpty
-/
instance : Inhabited LightProfinite :=
  ⟨LightProfinite.of PEmpty⟩

instance {X : LightProfinite} : TotallyDisconnectedSpace X :=
  X.prop.1

instance {X : LightProfinite} : SecondCountableTopology X :=
  X.prop.2

end LightProfinite

/--
Definition of `lightToProfinite` / `lightToProfinite` 的定义

English:
abbreviation lightToProfinite
  signature: : LightProfinite ⥤ Profinite
  body: CompHausLike.toCompHausLike (fun _ => inferInstance)

中文:
缩写 lightToProfinite
  签名: : LightProfinite ⥤ Profinite
  定义体: CompHausLike.toCompHausLike (fun _ => inferInstance)

Depends on / 依赖: CompHausLike, CompHausLike.toCompHausLike, toCompHausLike
-/
abbrev lightToProfinite : LightProfinite ⥤ Profinite :=
  CompHausLike.toCompHausLike (fun _ => inferInstance)

/--
Definition of `lightToProfiniteFullyFaithful` / `lightToProfiniteFullyFaithful` 的定义

English:
abbreviation lightToProfiniteFullyFaithful
  signature: : lightToProfinite.FullyFaithful
  body: fullyFaithfulToCompHausLike _

中文:
缩写 lightToProfiniteFullyFaithful
  签名: : lightToProfinite.满忠实
  定义体: fullyFaithfulToCompHausLike _

Depends on / 依赖: fullyFaithfulToCompHausLike
-/
abbrev lightToProfiniteFullyFaithful : lightToProfinite.FullyFaithful :=
  fullyFaithfulToCompHausLike _

/--
Definition of `lightProfiniteToCompHaus` / `lightProfiniteToCompHaus` 的定义

English:
abbreviation lightProfiniteToCompHaus
  signature: : LightProfinite ⥤ CompHaus
  body: compHausLikeToCompHaus _

中文:
缩写 lightProfiniteToCompHaus
  签名: : LightProfinite ⥤ CompHaus
  定义体: compHausLikeToCompHaus _

Depends on / 依赖: compHausLikeToCompHaus
-/
abbrev lightProfiniteToCompHaus : LightProfinite ⥤ CompHaus :=
  compHausLikeToCompHaus _

/--
Definition of `LightProfinite.toTopCat` / `LightProfinite.toTopCat` 的定义

English:
abbreviation LightProfinite.toTopCat
  signature: : LightProfinite ⥤ TopCat
  body: CompHausLike.compHausLikeToTop _

中文:
缩写 LightProfinite.toTopCat
  签名: : LightProfinite ⥤ 顶元素范畴
  定义体: CompHausLike.compHausLikeToTop _

Depends on / 依赖: CompHausLike, CompHausLike.compHausLikeToTop, compHausLikeToTop
-/
abbrev LightProfinite.toTopCat : LightProfinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology
attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `LightProfinite`, endowing a finite type with the
discrete topology. -/
@[simps! -isSimp map_hom_hom_apply obj]
/--
Definition of `FintypeCat.toLightProfinite` / `FintypeCat.toLightProfinite` 的定义

English:
definition FintypeCat.toLightProfinite
  signature: : FintypeCat ⥤ LightProfinite where
  body: LightProfinite.of A
  map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩

中文:
定义 FintypeCat.toLightProfinite
  签名: : FintypeCat ⥤ LightProfinite where
  定义体: LightProfinite.of A
  map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩

Depends on / 依赖: LightProfinite, LightProfinite.of
-/
def FintypeCat.toLightProfinite : FintypeCat ⥤ LightProfinite where
  obj A := LightProfinite.of A
  map f := CompHausLike.ofHom _ ⟨f, by fun_prop⟩

/--
Definition of `FintypeCat.toLightProfiniteFullyFaithful` / `FintypeCat.toLightProfiniteFullyFaithful` 的定义

English:
definition FintypeCat.toLightProfiniteFullyFaithful
  signature: : toLightProfinite.FullyFaithful where
  body: InducedCategory.homMk (↾(f.hom.hom.1))
  map_preimage _ := rfl
  preimage_map _ := rfl

中文:
定义 FintypeCat.toLightProfiniteFullyFaithful
  签名: : toLightProfinite.满忠实 where
  定义体: InducedCategory.homMk (↾(f.hom.hom.1))
  map_preimage _ := rfl
  preimage_map _ := rfl

Depends on / 依赖: InducedCategory, InducedCategory.homMk, f.hom.hom
-/
def FintypeCat.toLightProfiniteFullyFaithful : toLightProfinite.FullyFaithful where
  preimage f := InducedCategory.homMk (↾(f.hom.hom.1))
  map_preimage _ := rfl
  preimage_map _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FintypeCat.toLightProfinite.Faithful
  body: FintypeCat.toLightProfiniteFullyFaithful.faithful

中文:
实例 :
  签名: FintypeCat.toLightProfinite.忠实
  定义体: FintypeCat.toLightProfiniteFullyFaithful.faithful
-/
instance : FintypeCat.toLightProfinite.Faithful :=
  FintypeCat.toLightProfiniteFullyFaithful.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FintypeCat.toLightProfinite.Full
  body: FintypeCat.toLightProfiniteFullyFaithful.full

中文:
实例 :
  签名: FintypeCat.toLightProfinite.满
  定义体: FintypeCat.toLightProfiniteFullyFaithful.full

Depends on / 依赖: FintypeCat, FintypeCat.toLightProfiniteFullyFaithful.full, toLightProfiniteFullyFaithful
-/
instance : FintypeCat.toLightProfinite.Full :=
  FintypeCat.toLightProfiniteFullyFaithful.full

instance (X : FintypeCat.{u}) : Finite (FintypeCat.toLightProfinite.obj X) :=
  inferInstanceAs (Finite X)

instance (X : FintypeCat.{u}) : Finite (LightProfinite.of X) :=
  inferInstanceAs (Finite X)

end DiscreteTopology

namespace LightProfinite

instance {J : Type v} [SmallCategory J] (F : J ⥤ LightProfinite.{max u v}) :
    TotallyDisconnectedSpace
      (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop := by
  change TotallyDisconnectedSpace ({ u : forall j : J, F.obj j | _ } : Type _)
  exact Subtype.totallyDisconnectedSpace

/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: {J : Type v} [SmallCategory J] [CountableCategory J]
  body: { toTop := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop
      prop := by
        constructor
        · infer_instance
        · change SecondCountableTopology ({ u : forall j : J, F.obj j | _ } : Type _)
          apply IsInducing.subtypeVal.secondCountableTopology }
  π :=
  { app j :=
      ConcreteCategory.ofHom
        ((CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).π.app j).hom.hom
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

中文:
定义 limitCone
  签名: {J : 类型v} [小范畴 J] [余untable范畴 J]
  定义体: { toTop := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop
      prop := by
        constructor
        · infer_instance
        · change SecondCountableTopology ({ u : forall j : J, F.obj j | _ } : Type _)
          apply IsInducing.subtypeVal.secondCountableTopology }
  π :=
  { app j :=
      ConcreteCategory.ofHom
        ((CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).π.app j).hom.hom
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

Depends on / 依赖: CompHaus, CompHaus.limitCone, ConcreteCategory, ConcreteCategory.ofHom, F.obj, IsInducing, IsInducing.subtypeVal.secondCountableTopology, SecondCountableTopology, hom.hom, infer_instance, lightProfiniteToCompHaus, limitCone, naturality, pt.toTop, secondCountableTopology, subtypeVal
-/
def limitCone {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightProfinite.{max u v}) :
    Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).pt.toTop
      prop := by
        constructor
        · infer_instance
        · change SecondCountableTopology ({ u : forall j : J, F.obj j | _ } : Type _)
          apply IsInducing.subtypeVal.secondCountableTopology }
  π :=
  { app j :=
      ConcreteCategory.ofHom
        ((CompHaus.limitCone.{v, u} (F ⋙ lightProfiniteToCompHaus)).π.app j).hom.hom
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: {J : Type v} [SmallCategory J] [CountableCategory J]
  body: ConcreteCategory.ofHom
    ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightProfiniteToCompHaus)).lift
      (lightProfiniteToCompHaus.mapCone S)).hom.hom
  uniq S _ h := by
    apply lightProfiniteToCompHaus.map_injective
    apply (CompHaus.limitConeIsLimit.{v, u} _).uniq (lightProfiniteToCompHaus.mapCone S)
    intro j
    simp [← h]
    rfl

中文:
定义 limitConeIsLimit
  签名: {J : 类型v} [小范畴 J] [余untable范畴 J]
  定义体: ConcreteCategory.ofHom
    ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightProfiniteToCompHaus)).lift
      (lightProfiniteToCompHaus.mapCone S)).hom.hom
  uniq S _ h := by
    apply lightProfiniteToCompHaus.map_injective
    apply (CompHaus.limitConeIsLimit.{v, u} _).uniq (lightProfiniteToCompHaus.mapCone S)
    intro j
    simp [← h]
    rfl

Depends on / 依赖: CompHaus, CompHaus.limitConeIsLimit, ConcreteCategory, ConcreteCategory.ofHom, hom.hom, lightProfiniteToCompHaus, lightProfiniteToCompHaus.mapCone, lightProfiniteToCompHaus.map_injective, limitConeIsLimit, mapCone, map_injective
-/
def limitConeIsLimit {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightProfinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    ConcreteCategory.ofHom
    ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightProfiniteToCompHaus)).lift
      (lightProfiniteToCompHaus.mapCone S)).hom.hom
  uniq S _ h := by
    apply lightProfiniteToCompHaus.map_injective
    apply (CompHaus.limitConeIsLimit.{v, u} _).uniq (lightProfiniteToCompHaus.mapCone S)
    intro j
    simp [← h]
    rfl

/--
Instance `createsCountableLimits` / 实例 `createsCountableLimits`

English:
instance createsCountableLimits
  signature: {J : Type v} [SmallCategory J] [CountableCategory J]
  body: createsLimitOfFullyFaithfulOfIso (limitCone.{v, u} F).pt
      (Profinite.limitConeIsLimit.{v, u} (F ⋙ lightToProfinite)).conePointUniqueUpToIso
        (limit.isLimit _)

中文:
实例 createsCountableLimits
  签名: {J : 类型v} [小范畴 J] [余untable范畴 J]
  定义体: createsLimitOfFullyFaithfulOfIso (limitCone.{v, u} F).pt
      (Profinite.limitConeIsLimit.{v, u} (F ⋙ lightToProfinite)).conePointUniqueUpToIso
        (limit.isLimit _)

Depends on / 依赖: Profinite, Profinite.limitConeIsLimit, conePointUniqueUpToIso, createsLimitOfFullyFaithfulOfIso, isLimit, lightToProfinite, limit.isLimit, limitCone, limitConeIsLimit
-/
noncomputable instance createsCountableLimits {J : Type v} [SmallCategory J] [CountableCategory J] :
    CreatesLimitsOfShape J lightToProfinite.{max v u} where
  CreatesLimit {F} :=
createsLimitOfFullyFaithfulOfIso (limitCone.{v, u} F).pt
      (Profinite.limitConeIsLimit.{v, u} (F ⋙ lightToProfinite)).conePointUniqueUpToIso
        (limit.isLimit _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCountableLimits LightProfinite
  body: { has_limit := fun F => ⟨limitCone F, limitConeIsLimit F⟩ }

中文:
实例 :
  签名: 有余untableLimits LightProfinite
  定义体: { has_limit := fun F => ⟨limitCone F, limitConeIsLimit F⟩ }

Depends on / 依赖: has_limit, limitCone, limitConeIsLimit
-/
instance : HasCountableLimits LightProfinite where
  out _ := { has_limit := fun F => ⟨limitCone F, limitConeIsLimit F⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfShape Natᵒᵖ (forget LightProfinite.{u})
  body: have : PreservesLimitsOfSize.{0, 0} (forget Profinite.{u}) := preservesLimitsOfSize_shrink _
  inferInstanceAs (PreservesLimitsOfShape Natᵒᵖ (lightToProfinite ⋙ forget Profinite))

中文:
实例 :
  签名: 保持形状极限 自然数ᵒᵖ (forget LightProfinite.{u})
  定义体: have : PreservesLimitsOfSize.{0, 0} (forget Profinite.{u}) := preservesLimitsOfSize_shrink _
  inferInstanceAs (PreservesLimitsOfShape Natᵒᵖ (lightToProfinite ⋙ forget Profinite))

Depends on / 依赖: PreservesLimitsOfShape, PreservesLimitsOfSize, Profinite, forget, lightToProfinite, preservesLimitsOfSize_shrink
-/
instance : PreservesLimitsOfShape Natᵒᵖ (forget LightProfinite.{u}) :=
  have : PreservesLimitsOfSize.{0, 0} (forget Profinite.{u}) := preservesLimitsOfSize_shrink _
  inferInstanceAs (PreservesLimitsOfShape Natᵒᵖ (lightToProfinite ⋙ forget Profinite))

variable {X Y : LightProfinite.{u}} (f : X ⟶ Y)

/--
theorem `isClosedMap` / 定理 `isClosedMap`

English:
theorem isClosedMap
  statement: IsClosedMap f
  proof: CompHausLike.isClosedMap _

中文:
定理 isClosedMap
  结论: 是闭映射 f
  证明: CompHausLike.isClosedMap _

Depends on / 依赖: CompHausLike, CompHausLike.isClosedMap, isClosedMap
-/
theorem isClosedMap : IsClosedMap f :=
  CompHausLike.isClosedMap _

/--
theorem `isIso_of_bijective` / 定理 `isIso_of_bijective`

English:
theorem isIso_of_bijective
  given: (bij : Function.Bijective f)
  statement: IsIso f
  proof: haveI := CompHausLike.isIso_of_bijective (lightProfiniteToCompHaus.map f) bij
  isIso_of_fully_faithful lightProfiniteToCompHaus _

中文:
定理 isIso_of_bijective
  条件: (bij : 函数.双射 f)
  结论: 是同构 f
  证明: haveI := CompHausLike.isIso_of_bijective (lightProfiniteToCompHaus.map f) bij
  isIso_of_fully_faithful lightProfiniteToCompHaus _

Depends on / 依赖: CompHausLike, CompHausLike.isIso_of_bijective, isIso_of_bijective, isIso_of_fully_faithful, lightProfiniteToCompHaus, lightProfiniteToCompHaus.map
-/
theorem isIso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHausLike.isIso_of_bijective (lightProfiniteToCompHaus.map f) bij
  isIso_of_fully_faithful lightProfiniteToCompHaus _

/--
Definition of `isoOfBijective` / `isoOfBijective` 的定义

English:
definition isoOfBijective
  signature: (bij : Function.Bijective f)
  body: letI := LightProfinite.isIso_of_bijective f bij
  asIso f

中文:
定义 isoOfBijective
  签名: (bij : 函数.双射 f)
  定义体: letI := LightProfinite.isIso_of_bijective f bij
  asIso f

Depends on / 依赖: LightProfinite, LightProfinite.isIso_of_bijective, isIso_of_bijective
-/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := LightProfinite.isIso_of_bijective f bij
  asIso f

/--
Instance `forget_reflectsIsomorphisms` / 实例 `forget_reflectsIsomorphisms`

English:
instance forget_reflectsIsomorphisms
  signature: : (forget LightProfinite).ReflectsIsomorphisms
  body: by
  constructor
  intro A B f hf
  rw [isIso_iff_bijective] at hf
  exact LightProfinite.isIso_of_bijective _ hf

中文:
实例 forget_reflectsIsomorphisms
  签名: : (forget LightProfinite).反映同构
  定义体: by
  constructor
  intro A B f hf
  rw [isIso_iff_bijective] at hf
  exact LightProfinite.isIso_of_bijective _ hf

Depends on / 依赖: LightProfinite, LightProfinite.isIso_of_bijective, isIso_iff_bijective, isIso_of_bijective
-/
instance forget_reflectsIsomorphisms : (forget LightProfinite).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  rw [isIso_iff_bijective] at hf
  exact LightProfinite.isIso_of_bijective _ hf

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {X Y : LightProfinite.{u}} (f : X ⟶ Y)
  proof: by
  constructor
  · -- Note: in mathlib3 `contrapose` saw through `Function.Surjective`.
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y in U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U in 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := CompHausLike.ofHom _
        ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := CompHausLike.ofHom _ ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        dsimp [g, LocallyConstant.ofIsClopen]
        rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [hom_ofHom]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_neg]
        refine mt (fun α => hVU α) ?_
        simp [U, C]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

中文:
定理 epi_iff_surjective
  条件: {X Y : LightProfinite.{u}} (f : X ⟶ Y)
  证明: by
  constructor
  · -- Note: in mathlib3 `contrapose` saw through `Function.Surjective`.
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y in U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U in 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := CompHausLike.ofHom _
        ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := CompHausLike.ofHom _ ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        dsimp [g, LocallyConstant.ofIsClopen]
        rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [hom_ofHom]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_neg]
        refine mt (fun α => hVU α) ?_
        simp [U, C]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

Depends on / 依赖: Function, Function.Surjective, IsClosed, Set.mem_compl, Set.range, Surjective, classical, compl_mem_nhds, continuous, contrapose, f.hom.hom.continuous, hC.compl_mem_nhds, isClosed, isCompact_range, isTopologicalBasis_isClopen, isTopologicalBasis_isClopen.mem_nhds_iff.mp, mathlib3, mem_compl, mem_nhds_iff, through
-/
theorem epi_iff_surjective {X Y : LightProfinite.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · -- Note: in mathlib3 `contrapose` saw through `Function.Surjective`.
    dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y in U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U in 𝓝 y := hC.compl_mem_nhds hyU
    obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
    classical
      let Z := of (ULift.{u} <| Fin 2)
      let g : Y ⟶ Z := CompHausLike.ofHom _
        ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := CompHausLike.ofHom _ ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        dsimp [g, LocallyConstant.ofIsClopen]
        rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [hom_ofHom]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_neg]
        refine mt (fun α => hVU α) ?_
        simp [U, C]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget LightProfinite).epi_of_epi_map

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightToProfinite.PreservesEpimorphisms
  body: (Profinite.epi_iff_surjective _).mpr ((epi_iff_surjective f).mp inferInstance)

中文:
实例 :
  签名: lightToProfinite.保持Epimorphisms
  定义体: (Profinite.epi_iff_surjective _).mpr ((epi_iff_surjective f).mp inferInstance)

Depends on / 依赖: Profinite, Profinite.epi_iff_surjective, epi_iff_surjective
-/
instance : lightToProfinite.PreservesEpimorphisms where
  preserves f _ := (Profinite.epi_iff_surjective _).mpr ((epi_iff_surjective f).mp inferInstance)

end LightProfinite

/--
Definition of `LightDiagram` / `LightDiagram` 的定义

English:
structure LightDiagram
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - diagram : Natᵒᵖ ⥤ FintypeCat
    - cone : Cone (diagram ⋙ FintypeCat.toProfinite.{u})
    - isLimit : IsLimit cone

中文:
结构 LightDiagram
  参数: : 类型 (u + 1) where
  公理与运算 (3 个):
    - diagram : 自然数ᵒᵖ ⥤ FintypeCat
    - cone : 锥 (diagram ⋙ FintypeCat.toProfinite.{u})
    - isLimit : 是极限 cone
-/
structure LightDiagram : Type (u + 1) where
  /-- The indexing diagram. -/
  diagram : Natᵒᵖ ⥤ FintypeCat
  /-- The limit cone. -/
  cone : Cone (diagram ⋙ FintypeCat.toProfinite.{u})
  /-- The limit cone is limiting. -/
  isLimit : IsLimit cone

namespace LightDiagram

/--
Definition of `toProfinite` / `toProfinite` 的定义

English:
definition toProfinite
  signature: (S : LightDiagram)
  body: S.cone.pt

@[simps!]

中文:
定义 toProfinite
  签名: (S : LightDiagram)
  定义体: S.cone.pt

@[simps!]

Depends on / 依赖: S.cone.pt
-/
def toProfinite (S : LightDiagram) : Profinite := S.cone.pt

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category LightDiagram
  body: inferInstanceAs Category (InducedCategory _ toProfinite)

中文:
实例 :
  签名: 范畴 LightDiagram
  定义体: inferInstanceAs Category (InducedCategory _ toProfinite)

Depends on / 依赖: Category, InducedCategory, toProfinite
-/
instance : Category LightDiagram :=
inferInstanceAs Category (InducedCategory _ toProfinite)

/--
Instance `hasForget` / 实例 `hasForget`

English:
instance hasForget
  signature: : ConcreteCategory LightDiagram (fun X Y => C(X.toProfinite, Y.toProfinite))
  body: inferInstanceAs ConcreteCategory (InducedCategory _ toProfinite) _

中文:
实例 hasForget
  签名: : 余ncrete范畴 LightDiagram (fun X Y => C(X.toProfinite, Y.toProfinite))
  定义体: inferInstanceAs ConcreteCategory (InducedCategory _ toProfinite) _

Depends on / 依赖: ConcreteCategory, InducedCategory, toProfinite
-/
instance hasForget : ConcreteCategory LightDiagram (fun X Y => C(X.toProfinite, Y.toProfinite)) :=
inferInstanceAs ConcreteCategory (InducedCategory _ toProfinite) _

end LightDiagram

/-- The fully faithful embedding `LightDiagram ⥤ Profinite` -/
@[simps!]
/--
Definition of `lightDiagramToProfinite` / `lightDiagramToProfinite` 的定义

English:
definition lightDiagramToProfinite
  signature: : LightDiagram ⥤ Profinite
  body: inducedFunctor _

中文:
定义 lightDiagramToProfinite
  签名: : LightDiagram ⥤ Profinite
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def lightDiagramToProfinite : LightDiagram ⥤ Profinite := inducedFunctor _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightDiagramToProfinite.Faithful
  body: show (inducedFunctor _).Faithful from inferInstance

中文:
实例 :
  签名: lightDiagramToProfinite.忠实
  定义体: show (inducedFunctor _).Faithful from inferInstance

Depends on / 依赖: Faithful, inducedFunctor
-/
instance : lightDiagramToProfinite.Faithful := show (inducedFunctor _).Faithful from inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightDiagramToProfinite.Full
  body: show (inducedFunctor _).Full from inferInstance

中文:
实例 :
  签名: lightDiagramToProfinite.满
  定义体: show (inducedFunctor _).Full from inferInstance
-/
instance : lightDiagramToProfinite.Full := show (inducedFunctor _).Full from inferInstance

namespace LightProfinite

instance (S : LightProfinite) : Countable (Clopens S) := by
  rw [TopologicalSpace.Clopens.countable_iff_secondCountable]
  infer_instance

/--
Instance `instCountableDiscreteQuotient` / 实例 `instCountableDiscreteQuotient`

English:
instance instCountableDiscreteQuotient
  signature: (S : LightProfinite)
  body: (DiscreteQuotient.finsetClopens_inj S).countable

中文:
实例 instCountableDiscreteQuotient
  签名: (S : LightProfinite)
  定义体: (DiscreteQuotient.finsetClopens_inj S).countable

Depends on / 依赖: DiscreteQuotient, DiscreteQuotient.finsetClopens_inj, countable, finsetClopens_inj
-/
instance instCountableDiscreteQuotient (S : LightProfinite) :
    Countable (DiscreteQuotient ((lightToProfinite.obj S))) :=
  (DiscreteQuotient.finsetClopens_inj S).countable

/--
Definition of `toLightDiagram` / `toLightDiagram` 的定义

English:
definition toLightDiagram
  signature: (S : LightProfinite.{u})
  body: IsCofiltered.sequentialFunctor _ ⋙ (lightToProfinite.obj S).fintypeDiagram
  cone := (Functor.Initial.limitConeComp (IsCofiltered.sequentialFunctor _)
    (lightToProfinite.obj S).lim).cone
  isLimit := (Functor.Initial.limitConeComp (IsCofiltered.sequentialFunctor _)
    (lightToProfinite.obj S).lim).isLimit

中文:
定义 toLightDiagram
  签名: (S : LightProfinite.{u})
  定义体: IsCofiltered.sequentialFunctor _ ⋙ (lightToProfinite.obj S).fintypeDiagram
  cone := (Functor.Initial.limitConeComp (IsCofiltered.sequentialFunctor _)
    (lightToProfinite.obj S).lim).cone
  isLimit := (Functor.Initial.limitConeComp (IsCofiltered.sequentialFunctor _)
    (lightToProfinite.obj S).lim).isLimit

Depends on / 依赖: IsCofiltered, IsCofiltered.sequentialFunctor, fintypeDiagram, lightToProfinite, lightToProfinite.obj, sequentialFunctor
-/
noncomputable def toLightDiagram (S : LightProfinite.{u}) : LightDiagram.{u} where
  diagram := IsCofiltered.sequentialFunctor _ ⋙ (lightToProfinite.obj S).fintypeDiagram
  cone := (Functor.Initial.limitConeComp (IsCofiltered.sequentialFunctor _)
    (lightToProfinite.obj S).lim).cone
  isLimit := (Functor.Initial.limitConeComp (IsCofiltered.sequentialFunctor _)
    (lightToProfinite.obj S).lim).isLimit

end LightProfinite

/-- The functor part of the equivalence `LightProfinite ≌ LightDiagram` -/
@[simps]
/--
Definition of `lightProfiniteToLightDiagram` / `lightProfiniteToLightDiagram` 的定义

English:
definition lightProfiniteToLightDiagram
  signature: : LightProfinite.{u} ⥤ LightDiagram.{u} where
  body: X.toLightDiagram
  map f := InducedCategory.homMk (InducedCategory.homMk f.hom)

中文:
定义 lightProfiniteToLightDiagram
  签名: : LightProfinite.{u} ⥤ LightDiagram.{u} where
  定义体: X.toLightDiagram
  map f := InducedCategory.homMk (InducedCategory.homMk f.hom)

Depends on / 依赖: X.toLightDiagram, toLightDiagram
-/
noncomputable def lightProfiniteToLightDiagram : LightProfinite.{u} ⥤ LightDiagram.{u} where
  obj X := X.toLightDiagram
  map f := InducedCategory.homMk (InducedCategory.homMk f.hom)

open scoped Classical in
instance (S : LightDiagram.{u}) : SecondCountableTopology S.cone.pt := by
  rw [← TopologicalSpace.Clopens.countable_iff_secondCountable]
  refine @Countable.of_equiv _ _ ?_ (LocallyConstant.equivClopens (X := S.cone.pt))
  refine @Function.Surjective.countable
    (Σ (n : Nat), LocallyConstant ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩) (Fin 2)) _ ?_ ?_ ?_
  · apply @instCountableSigma _ _ _ ?_
    intro n
    refine @Finite.to_countable _ ?_
    refine @Finite.of_injective _ ((S.diagram ⋙ FintypeCat.toProfinite).obj ⟨n⟩ -> (Fin 2)) ?_ _
      LocallyConstant.coe_injective
    refine @Pi.finite _ _ ?_ _
    simp only [Functor.comp_obj]
    exact show (Finite (S.diagram.obj _)) from inferInstance
  · exact fun a => a.snd.comap (S.cone.π.app ⟨a.fst⟩).hom.hom
  · intro a
    obtain ⟨n, g, h⟩ := Profinite.exists_locallyConstant S.cone S.isLimit a
    exact ⟨⟨unop n, g⟩, h.symm⟩

/-- The inverse part of the equivalence `LightProfinite ≌ LightDiagram` -/
@[simps obj map]
/--
Definition of `lightDiagramToLightProfinite` / `lightDiagramToLightProfinite` 的定义

English:
definition lightDiagramToLightProfinite
  signature: : LightDiagram.{u} ⥤ LightProfinite.{u} where
  body: LightProfinite.of X.cone.pt
  map f := InducedCategory.homMk f.hom.hom

中文:
定义 lightDiagramToLightProfinite
  签名: : LightDiagram.{u} ⥤ LightProfinite.{u} where
  定义体: LightProfinite.of X.cone.pt
  map f := InducedCategory.homMk f.hom.hom

Depends on / 依赖: LightProfinite, LightProfinite.of, X.cone.pt
-/
def lightDiagramToLightProfinite : LightDiagram.{u} ⥤ LightProfinite.{u} where
  obj X := LightProfinite.of X.cone.pt
  map f := InducedCategory.homMk f.hom.hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LightProfinite.equivDiagram` / `LightProfinite.equivDiagram` 的定义

English:
definition LightProfinite.equivDiagram
  signature: : LightProfinite.{u} ≌ LightDiagram.{u} where
  body: lightProfiniteToLightDiagram
  inverse := lightDiagramToLightProfinite
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun _ => lightDiagramToProfinite.preimageIso (Iso.refl _)) (by
      intro _ _ f
      dsimp
      apply lightDiagramToProfinite.map_injective
      apply InducedCategory.hom_ext
      simp only [Functor.map_comp, Functor.map_preimage]
      simp)
  functor_unitIso_comp _ := by simpa using! lightDiagramToProfinite.preimage_id

中文:
定义 LightProfinite.equivDiagram
  签名: : LightProfinite.{u} ≌ LightDiagram.{u} where
  定义体: lightProfiniteToLightDiagram
  inverse := lightDiagramToLightProfinite
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun _ => lightDiagramToProfinite.preimageIso (Iso.refl _)) (by
      intro _ _ f
      dsimp
      apply lightDiagramToProfinite.map_injective
      apply InducedCategory.hom_ext
      simp only [Functor.map_comp, Functor.map_preimage]
      simp)
  functor_unitIso_comp _ := by simpa using! lightDiagramToProfinite.preimage_id

Depends on / 依赖: lightProfiniteToLightDiagram
-/
noncomputable def LightProfinite.equivDiagram : LightProfinite.{u} ≌ LightDiagram.{u} where
  functor := lightProfiniteToLightDiagram
  inverse := lightDiagramToLightProfinite
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun _ => lightDiagramToProfinite.preimageIso (Iso.refl _)) (by
      intro _ _ f
      dsimp
      apply lightDiagramToProfinite.map_injective
      apply InducedCategory.hom_ext
      simp only [Functor.map_comp, Functor.map_preimage]
      simp)
  functor_unitIso_comp _ := by simpa using! lightDiagramToProfinite.preimage_id

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightProfiniteToLightDiagram.IsEquivalence
  body: show LightProfinite.equivDiagram.functor.IsEquivalence from inferInstance

中文:
实例 :
  签名: lightProfiniteToLightDiagram.是等价
  定义体: show LightProfinite.equivDiagram.functor.IsEquivalence from inferInstance

Depends on / 依赖: IsEquivalence, LightProfinite, LightProfinite.equivDiagram.functor.IsEquivalence, equivDiagram, functor
-/
instance : lightProfiniteToLightDiagram.IsEquivalence :=
  show LightProfinite.equivDiagram.functor.IsEquivalence from inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: lightDiagramToLightProfinite.IsEquivalence
  body: show LightProfinite.equivDiagram.inverse.IsEquivalence from inferInstance

noncomputable section EssentiallySmall

中文:
实例 :
  签名: lightDiagramToLightProfinite.是等价
  定义体: show LightProfinite.equivDiagram.inverse.IsEquivalence from inferInstance

noncomputable section EssentiallySmall

Depends on / 依赖: IsEquivalence, LightProfinite, LightProfinite.equivDiagram.inverse.IsEquivalence, equivDiagram, inverse
-/
instance : lightDiagramToLightProfinite.IsEquivalence :=
  show LightProfinite.equivDiagram.inverse.IsEquivalence from inferInstance

noncomputable section EssentiallySmall

open LightDiagram

/--
Definition of `LightDiagram'` / `LightDiagram'` 的定义

English:
structure LightDiagram'
  parameters: : Type u where
  axioms and operations (1):
    - diagram : Natᵒᵖ ⥤ FintypeCat.Skeleton.{u}

中文:
结构 LightDiagram'
  参数: : 类型u where
  公理与运算 (1 个):
    - diagram : 自然数ᵒᵖ ⥤ FintypeCat.Skeleton.{u}
-/
structure LightDiagram' : Type u where
  /-- The diagram takes values in a small category equivalent to `FintypeCat`. -/
  diagram : Natᵒᵖ ⥤ FintypeCat.Skeleton.{u}

/--
Definition of `LightDiagram'.toProfinite` / `LightDiagram'.toProfinite` 的定义

English:
definition LightDiagram'.toProfinite
  signature: (S : LightDiagram')
  body: limit (S.diagram ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

中文:
定义 LightDiagram'.toProfinite
  签名: (S : LightDiagram')
  定义体: limit (S.diagram ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

Depends on / 依赖: FintypeCat, FintypeCat.Skeleton.equivalence.functor, FintypeCat.toProfinite, S.diagram, Skeleton, diagram, equivalence, functor, toProfinite
-/
def LightDiagram'.toProfinite (S : LightDiagram') : Profinite :=
  limit (S.diagram ⋙ FintypeCat.Skeleton.equivalence.functor ⋙ FintypeCat.toProfinite.{u})

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category LightDiagram'
  body: inferInstanceAs (Category (InducedCategory _ LightDiagram'.toProfinite))

中文:
实例 :
  签名: 范畴 LightDiagram'
  定义体: inferInstanceAs (Category (InducedCategory _ LightDiagram'.toProfinite))
-/
instance : Category LightDiagram' :=
  inferInstanceAs (Category (InducedCategory _ LightDiagram'.toProfinite))

/--
Definition of `LightDiagram'.toLightFunctor` / `LightDiagram'.toLightFunctor` 的定义

English:
definition LightDiagram'.toLightFunctor
  signature: : LightDiagram'.{u} ⥤ LightDiagram.{u} where
  body: ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := InducedCategory.homMk f.hom

中文:
定义 LightDiagram'.toLightFunctor
  签名: : LightDiagram'.{u} ⥤ LightDiagram.{u} where
  定义体: ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := InducedCategory.homMk f.hom
-/
def LightDiagram'.toLightFunctor : LightDiagram'.{u} ⥤ LightDiagram.{u} where
  obj X := ⟨X.diagram ⋙ Skeleton.equivalence.functor, _, limit.isLimit _⟩
  map f := InducedCategory.homMk f.hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LightDiagram'.toLightFunctor.{u}.Faithful
  body: by
    apply InducedCategory.homEquiv.injective
    apply InducedCategory.homEquiv.symm.injective h

中文:
实例 :
  签名: LightDiagram'.toLightFunctor.{u}.忠实
  定义体: by
    apply InducedCategory.homEquiv.injective
    apply InducedCategory.homEquiv.symm.injective h

Depends on / 依赖: InducedCategory, InducedCategory.homEquiv.injective, InducedCategory.homEquiv.symm.injective, homEquiv, injective
-/
instance : LightDiagram'.toLightFunctor.{u}.Faithful where
  map_injective h := by
    apply InducedCategory.homEquiv.injective
    apply InducedCategory.homEquiv.symm.injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LightDiagram'.toLightFunctor.{u}.Full
  body: ⟨InducedCategory.homMk f.hom, rfl⟩

中文:
实例 :
  签名: LightDiagram'.toLightFunctor.{u}.满
  定义体: ⟨InducedCategory.homMk f.hom, rfl⟩
-/
instance : LightDiagram'.toLightFunctor.{u}.Full where
  map_surjective f := ⟨InducedCategory.homMk f.hom, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LightDiagram'.toLightFunctor.{u}.EssSurj
  body: ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨lightDiagramToProfinite.preimageIso (
      (Limits.lim.mapIso (Functor.isoWhiskerRight ((Functor.isoWhiskerLeft Y.diagram
      Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso Y.isLimit)⟩⟩

中文:
实例 :
  签名: LightDiagram'.toLightFunctor.{u}.本质满射
  定义体: ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨lightDiagramToProfinite.preimageIso (
      (Limits.lim.mapIso (Functor.isoWhiskerRight ((Functor.isoWhiskerLeft Y.diagram
      Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso Y.isLimit)⟩⟩
-/
instance : LightDiagram'.toLightFunctor.{u}.EssSurj where
  mem_essImage Y :=
    ⟨⟨Y.diagram ⋙ Skeleton.equivalence.inverse⟩, ⟨lightDiagramToProfinite.preimageIso (
      (Limits.lim.mapIso (Functor.isoWhiskerRight ((Functor.isoWhiskerLeft Y.diagram
      Skeleton.equivalence.counitIso)) toProfinite)) ≪≫
      (limit.isLimit _).conePointUniqueUpToIso Y.isLimit)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LightDiagram'.toLightFunctor.IsEquivalence

中文:
实例 :
  签名: LightDiagram'.toLightFunctor.是等价
-/
instance : LightDiagram'.toLightFunctor.IsEquivalence where

/--
Definition of `LightDiagram.equivSmall` / `LightDiagram.equivSmall` 的定义

English:
definition LightDiagram.equivSmall
  signature: : LightDiagram.{u} ≌ LightDiagram'.{u}
  body: LightDiagram'.toLightFunctor.asEquivalence.symm

中文:
定义 LightDiagram.equivSmall
  签名: : LightDiagram.{u} ≌ LightDiagram'.{u}
  定义体: LightDiagram'.toLightFunctor.asEquivalence.symm

Depends on / 依赖: LightDiagram, asEquivalence, toLightFunctor, toLightFunctor.asEquivalence.symm
-/
def LightDiagram.equivSmall : LightDiagram.{u} ≌ LightDiagram'.{u} :=
  LightDiagram'.toLightFunctor.asEquivalence.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{u} LightDiagram.{u}
  body: ⟨LightDiagram', inferInstance, ⟨LightDiagram.equivSmall⟩⟩

中文:
实例 :
  签名: EssentiallySmall.{u} LightDiagram.{u}
  定义体: ⟨LightDiagram', inferInstance, ⟨LightDiagram.equivSmall⟩⟩
-/
instance : EssentiallySmall.{u} LightDiagram.{u} where
  equiv_smallCategory := ⟨LightDiagram', inferInstance, ⟨LightDiagram.equivSmall⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EssentiallySmall.{u} LightProfinite.{u}
  body: ⟨LightDiagram', inferInstance,
    ⟨LightProfinite.equivDiagram.trans LightDiagram.equivSmall⟩⟩

中文:
实例 :
  签名: EssentiallySmall.{u} LightProfinite.{u}
  定义体: ⟨LightDiagram', inferInstance,
    ⟨LightProfinite.equivDiagram.trans LightDiagram.equivSmall⟩⟩

Depends on / 依赖: LightDiagram
-/
instance : EssentiallySmall.{u} LightProfinite.{u} where
  equiv_smallCategory := ⟨LightDiagram', inferInstance,
    ⟨LightProfinite.equivDiagram.trans LightDiagram.equivSmall⟩⟩

end EssentiallySmall
