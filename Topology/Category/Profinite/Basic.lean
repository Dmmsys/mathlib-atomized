/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne, Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Separation.Profinite

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `TopCat`. The fully faithful functor
is called `Profinite.toTop`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

The category `Profinite` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

## TODO

* Define procategories and prove that `Profinite` is equivalent to `Pro (FintypeCat)`.

## Tags

profinite

-/

@[expose] public section

universe v u

open CategoryTheory Topology CompHausLike

/-- The type of profinite topological spaces. -/
@[to_additive_do_translate] -- This is required
/--
Definition of `Profinite` / `Profinite` 的定义

English:
abbreviation Profinite
  body: CompHausLike (fun X => TotallyDisconnectedSpace X)

中文:
缩写 Profinite
  定义体: CompHausLike (fun X => TotallyDisconnectedSpace X)
-/
abbrev Profinite := CompHausLike (fun X => TotallyDisconnectedSpace X)

namespace Profinite

instance (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : HasProp (fun Y => TotallyDisconnectedSpace Y) X :=
  ⟨(inferInstance : TotallyDisconnectedSpace X)⟩

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
    [TotallyDisconnectedSpace X] : Profinite :=
  CompHausLike.of _ X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Profinite
  body: ⟨Profinite.of PEmpty⟩

中文:
实例 :
  签名: 可居 Profinite
  定义体: ⟨Profinite.of PEmpty⟩

Depends on / 依赖: PEmpty, Profinite, Profinite.of
-/
instance : Inhabited Profinite :=
  ⟨Profinite.of PEmpty⟩

instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.prop

end Profinite

/--
Definition of `profiniteToCompHaus` / `profiniteToCompHaus` 的定义

English:
abbreviation profiniteToCompHaus
  signature: : Profinite ⥤ CompHaus
  body: compHausLikeToCompHaus _

中文:
缩写 profiniteToCompHaus
  签名: : Profinite ⥤ CompHaus
  定义体: compHausLikeToCompHaus _

Depends on / 依赖: compHausLikeToCompHaus
-/
abbrev profiniteToCompHaus : Profinite ⥤ CompHaus :=
  compHausLikeToCompHaus _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

instance {X : Profinite} : TotallyDisconnectedSpace (profiniteToCompHaus.obj X) :=
  X.prop

/--
Definition of `Profinite.toTopCat` / `Profinite.toTopCat` 的定义

English:
abbreviation Profinite.toTopCat
  signature: : Profinite ⥤ TopCat
  body: CompHausLike.compHausLikeToTop _

中文:
缩写 Profinite.toTopCat
  签名: : Profinite ⥤ 顶元素范畴
  定义体: CompHausLike.compHausLikeToTop _

Depends on / 依赖: CompHausLike, CompHausLike.compHausLikeToTop, compHausLikeToTop
-/
abbrev Profinite.toTopCat : Profinite ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

section Profinite

-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
/--
(Implementation) The object part of the `connectedComponents` functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components. -/
@[stacks 0900]
/--
Definition of `CompHaus.toProfiniteObj` / `CompHaus.toProfiniteObj` 的定义

English:
definition CompHaus.toProfiniteObj
  signature: (X : CompHaus.{u})
  body: TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace

中文:
定义 CompHaus.toProfiniteObj
  签名: (X : CompHaus.{u})
  定义体: TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace

Depends on / 依赖: ConnectedComponents, TopCat, TopCat.of
-/
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toTop := TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Profinite.toCompHausEquivalence` / `Profinite.toCompHausEquivalence` 的定义

English:
definition Profinite.toCompHausEquivalence
  signature: (X : CompHaus.{u}) (Y : Profinite.{u})
  body: ofHom _ (f.hom.hom.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩)
  invFun g := ConcreteCategory.ofHom
    { toFun := Continuous.connectedComponentsLift g.hom.hom.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.hom.hom.2 }
  left_inv f :=
    InducedCategory.hom_ext (TopC

中文:
定义 Profinite.toCompHausEquivalence
  签名: (X : CompHaus.{u}) (Y : Profinite.{u})
  定义体: ofHom _ (f.hom.hom.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩)
  invFun g := ConcreteCategory.ofHom
    { toFun := Continuous.connectedComponentsLift g.hom.hom.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.hom.hom.2 }
  left_inv f :=
    InducedCategory.hom_ext (TopC

Depends on / 依赖: Quotient, Quotient.mk, continuous_quotient_mk, f.hom.hom.comp
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := ofHom _ (f.hom.hom.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩)
  invFun g := ConcreteCategory.ofHom
    { toFun := Continuous.connectedComponentsLift g.hom.hom.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.hom.hom.2 }
  left_inv f :=
    InducedCategory.hom_ext (TopCat.ext (fun y => by
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
      rfl))

/--
Definition of `CompHaus.toProfinite` / `CompHaus.toProfinite` 的定义

English:
definition CompHaus.toProfinite
  signature: : CompHaus ⥤ Profinite
  body: Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl

中文:
定义 CompHaus.toProfinite
  签名: : CompHaus ⥤ Profinite
  定义体: Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl

Depends on / 依赖: Adjunction, Adjunction.leftAdjointOfEquiv, Profinite, Profinite.toCompHausEquivalence, leftAdjointOfEquiv, toCompHausEquivalence
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl

/--
theorem `CompHaus.toProfinite_obj'` / 定理 `CompHaus.toProfinite_obj'`

English:
theorem CompHaus.toProfinite_obj'
  given: (X : CompHaus)
  proof: rfl

中文:
定理 CompHaus.toProfinite_obj'
  条件: (X : CompHaus)
  证明: rfl
-/
theorem CompHaus.toProfinite_obj' (X : CompHaus) :
    ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl

/-- Finite types are given the discrete topology. -/
@[instance_reducible]
/--
Definition of `FintypeCat.botTopology` / `FintypeCat.botTopology` 的定义

English:
definition FintypeCat.botTopology
  signature: (A : FintypeCat)
  body: ⊥

中文:
定义 FintypeCat.botTopology
  签名: (A : FintypeCat)
  定义体: ⊥
-/
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A := ⊥

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

/--
theorem `FintypeCat.discreteTopology` / 定理 `FintypeCat.discreteTopology`

English:
theorem FintypeCat.discreteTopology
  given: (A : FintypeCat)
  statement: DiscreteTopology A
  proof: ⟨rfl⟩

中文:
定理 FintypeCat.discreteTopology
  条件: (A : FintypeCat)
  结论: 离散拓扑 A
  证明: ⟨rfl⟩
-/
theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩

attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps! -isSimp map_hom_hom_apply obj]
/--
Definition of `FintypeCat.toProfinite` / `FintypeCat.toProfinite` 的定义

English:
definition FintypeCat.toProfinite
  signature: : FintypeCat ⥤ Profinite where
  body: Profinite.of A
  map f := ofHom _ ⟨f, by fun_prop⟩

中文:
定义 FintypeCat.toProfinite
  签名: : FintypeCat ⥤ Profinite where
  定义体: Profinite.of A
  map f := ofHom _ ⟨f, by fun_prop⟩

Depends on / 依赖: Profinite, Profinite.of
-/
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite where
  obj A := Profinite.of A
  map f := ofHom _ ⟨f, by fun_prop⟩

/--
Definition of `FintypeCat.toProfiniteFullyFaithful` / `FintypeCat.toProfiniteFullyFaithful` 的定义

English:
definition FintypeCat.toProfiniteFullyFaithful
  signature: : toProfinite.FullyFaithful where
  body: InducedCategory.homMk ↾(f : _ -> _)
  map_preimage _ := rfl
  preimage_map _ := rfl

中文:
定义 FintypeCat.toProfiniteFullyFaithful
  签名: : toProfinite.满忠实 where
  定义体: InducedCategory.homMk ↾(f : _ -> _)
  map_preimage _ := rfl
  preimage_map _ := rfl

Depends on / 依赖: InducedCategory, InducedCategory.homMk
-/
def FintypeCat.toProfiniteFullyFaithful : toProfinite.FullyFaithful where
preimage f := InducedCategory.homMk ↾(f : _ -> _)
  map_preimage _ := rfl
  preimage_map _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FintypeCat.toProfinite.Faithful
  body: FintypeCat.toProfiniteFullyFaithful.faithful

中文:
实例 :
  签名: FintypeCat.toProfinite.忠实
  定义体: FintypeCat.toProfiniteFullyFaithful.faithful

Depends on / 依赖: FintypeCat, FintypeCat.toProfiniteFullyFaithful.faithful, faithful, toProfiniteFullyFaithful
-/
instance : FintypeCat.toProfinite.Faithful := FintypeCat.toProfiniteFullyFaithful.faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FintypeCat.toProfinite.Full
  body: FintypeCat.toProfiniteFullyFaithful.full

中文:
实例 :
  签名: FintypeCat.toProfinite.满
  定义体: FintypeCat.toProfiniteFullyFaithful.full
-/
instance : FintypeCat.toProfinite.Full := FintypeCat.toProfiniteFullyFaithful.full

instance (X : FintypeCat) : Finite (FintypeCat.toProfinite.obj X) := inferInstanceAs (Finite X)

instance (X : FintypeCat) : Finite (Profinite.of X) := inferInstanceAs (Finite X)

end DiscreteTopology

end Profinite

namespace Profinite

/--
Definition of `limitCone` / `limitCone` 的定义

English:
definition limitCone
  signature: {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v})
  body: { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : forall j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app j := InducedCategory.homMk
        (((CompHaus.limitCone.{v,

中文:
定义 limitCone
  签名: {J : 类型v} [小范畴 J] (F : J ⥤ Profinite.{最大值 u v})
  定义体: { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : forall j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app j := InducedCategory.homMk
        (((CompHaus.limitCone.{v,

Depends on / 依赖: CompHaus, CompHaus.limitCone, F.obj, InducedCategory, InducedCategory.homMk, Subtype, Subtype.totallyDisconnectedSpace, TotallyDisconnectedSpace, limitCone, profiniteToCompHaus, pt.toTop, totallyDisconnectedSpace
-/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : forall j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app j := InducedCategory.homMk
        (((CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).π.app j).hom)
    -- Porting note: was `by tidy`:
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/--
Definition of `limitConeIsLimit` / `limitConeIsLimit` 的定义

English:
definition limitConeIsLimit
  signature: {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v})
  body: InducedCategory.homMk
      ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
        (profiniteToCompHaus.mapCone S)).hom
  uniq S _ h :=
    profiniteToCompHaus.map_injective
      ((CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _
        (fun j => by
  

中文:
定义 limitConeIsLimit
  签名: {J : 类型v} [小范畴 J] (F : J ⥤ Profinite.{最大值 u v})
  定义体: InducedCategory.homMk
      ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
        (profiniteToCompHaus.mapCone S)).hom
  uniq S _ h :=
    profiniteToCompHaus.map_injective
      ((CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _
        (fun j => by
  

Depends on / 依赖: CompHaus, CompHaus.limitConeIsLimit, InducedCategory, InducedCategory.homMk, limitConeIsLimit, mapCone, map_injective, profiniteToCompHaus, profiniteToCompHaus.mapCone, profiniteToCompHaus.map_injective
-/
def limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    InducedCategory.homMk
      ((CompHaus.limitConeIsLimit.{v, u} (F ⋙ profiniteToCompHaus)).lift
        (profiniteToCompHaus.mapCone S)).hom
  uniq S _ h :=
    profiniteToCompHaus.map_injective
      ((CompHaus.limitConeIsLimit.{v, u} _).uniq (profiniteToCompHaus.mapCone S) _
        (fun j => by
          simp [← h]
          rfl))

/--
Definition of `toProfiniteAdjToCompHaus` / `toProfiniteAdjToCompHaus` 的定义

English:
definition toProfiniteAdjToCompHaus
  signature: : CompHaus.toProfinite ⊣ profiniteToCompHaus
  body: Adjunction.adjunctionOfEquivLeft _ _

中文:
定义 toProfiniteAdjToCompHaus
  签名: : CompHaus.toProfinite ⊣ profiniteToCompHaus
  定义体: Adjunction.adjunctionOfEquivLeft _ _

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivLeft, adjunctionOfEquivLeft
-/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _

/--
Instance `toCompHaus.reflective` / 实例 `toCompHaus.reflective`

English:
instance toCompHaus.reflective
  signature: : Reflective profiniteToCompHaus where
  body: CompHaus.toProfinite
  adj := Profinite.toProfiniteAdjToCompHaus

中文:
实例 toCompHaus.reflective
  签名: : 反射 profiniteToCompHaus where
  定义体: CompHaus.toProfinite
  adj := Profinite.toProfiniteAdjToCompHaus

Depends on / 依赖: CompHaus, CompHaus.toProfinite, toProfinite
-/
instance toCompHaus.reflective : Reflective profiniteToCompHaus where
  L := CompHaus.toProfinite
  adj := Profinite.toProfiniteAdjToCompHaus

/--
Instance `toCompHaus.createsLimits` / 实例 `toCompHaus.createsLimits`

English:
instance toCompHaus.createsLimits
  signature: : CreatesLimits profiniteToCompHaus
  body: monadicCreatesLimits _

中文:
实例 toCompHaus.createsLimits
  签名: : CreatesLimits profiniteToCompHaus
  定义体: monadicCreatesLimits _

Depends on / 依赖: monadicCreatesLimits
-/
noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _

/--
Instance `toTopCat.reflective` / 实例 `toTopCat.reflective`

English:
instance toTopCat.reflective
  signature: : Reflective Profinite.toTopCat
  body: Reflective.comp profiniteToCompHaus compHausToTop

中文:
实例 toTopCat.reflective
  签名: : 反射 Profinite.toTopCat
  定义体: Reflective.comp profiniteToCompHaus compHausToTop

Depends on / 依赖: Reflective, Reflective.comp, compHausToTop, profiniteToCompHaus
-/
noncomputable instance toTopCat.reflective : Reflective Profinite.toTopCat :=
  Reflective.comp profiniteToCompHaus compHausToTop

/--
Instance `toTopCat.createsLimits` / 实例 `toTopCat.createsLimits`

English:
instance toTopCat.createsLimits
  signature: : CreatesLimits Profinite.toTopCat
  body: monadicCreatesLimits _

中文:
实例 toTopCat.createsLimits
  签名: : CreatesLimits Profinite.toTopCat
  定义体: monadicCreatesLimits _

Depends on / 依赖: monadicCreatesLimits
-/
noncomputable instance toTopCat.createsLimits : CreatesLimits Profinite.toTopCat :=
  monadicCreatesLimits _

/--
Instance `hasLimits` / 实例 `hasLimits`

English:
instance hasLimits
  signature: : Limits.HasLimits Profinite
  body: hasLimits_of_hasLimits_createsLimits Profinite.toTopCat

中文:
实例 hasLimits
  签名: : Limits.有极限 Profinite
  定义体: hasLimits_of_hasLimits_createsLimits Profinite.toTopCat

Depends on / 依赖: Profinite, Profinite.toTopCat, hasLimits_of_hasLimits_createsLimits, toTopCat
-/
instance hasLimits : Limits.HasLimits Profinite :=
  hasLimits_of_hasLimits_createsLimits Profinite.toTopCat

/--
Instance `hasColimits` / 实例 `hasColimits`

English:
instance hasColimits
  signature: : Limits.HasColimits Profinite
  body: hasColimits_of_reflective profiniteToCompHaus

中文:
实例 hasColimits
  签名: : Limits.有余极限 Profinite
  定义体: hasColimits_of_reflective profiniteToCompHaus

Depends on / 依赖: hasColimits_of_reflective, profiniteToCompHaus
-/
instance hasColimits : Limits.HasColimits Profinite :=
  hasColimits_of_reflective profiniteToCompHaus

/--
Instance `forget_preservesLimits` / 实例 `forget_preservesLimits`

English:
instance forget_preservesLimits
  signature: : Limits.PreservesLimits (forget Profinite)
  body: by
  apply Limits.comp_preservesLimits Profinite.toTopCat (forget TopCat)

中文:
实例 forget_preservesLimits
  签名: : Limits.PreservesLimits (forget Profinite)
  定义体: by
  apply Limits.comp_preservesLimits Profinite.toTopCat (forget TopCat)

Depends on / 依赖: Limits, Limits.comp_preservesLimits, Profinite, Profinite.toTopCat, TopCat, comp_preservesLimits, forget, toTopCat
-/
instance forget_preservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply Limits.comp_preservesLimits Profinite.toTopCat (forget TopCat)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {X Y : Profinite.{u}} (f : X ⟶ Y)
  statement: Epi f ↔ Function.Surjective f
  proof: by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y in U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy 

中文:
定理 epi_iff_surjective
  条件: {X Y : Profinite.{u}} (f : X ⟶ Y)
  结论: 满态射 f ↔ 函数.满射 f
  证明: by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y in U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy 

Depends on / 依赖: Function, Function.Surjective, IsClosed, LocallyConstant, LocallyConstant.ofIsClopen, Set.mem_compl, Set.range, Surjective, ULift.up, classical, compl_mem_nhds, continuous, contrapose, f.hom.hom.continuous, hC.compl_mem_nhds, isClosed, isCompact_range, isTopologicalBasis_isClopen, isTopologicalBasis_isClopen.mem_nhds_iff.mp, mem_compl
-/
theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
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
      let g : Y ⟶ Z := ofHom _
        ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
      let h : Y ⟶ Z := ofHom _ ⟨fun _ => ⟨1⟩, continuous_const⟩
      have H : h = g := by
        rw [← cancel_epi f]
        ext x
        dsimp [g, LocallyConstant.ofIsClopen]
        rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [ConcreteCategory.hom_ofHom]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_neg]
        refine mt (fun α => hVU α) ?_
        simp [U, C]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      rw [ContinuousMap.coe_mk]; rw [ContinuousMap.coe_mk]; rw [Function.comp_apply]; rw [if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {α : Type u} (β : α -> Profinite)
  body: .of (Π (a : α), β a)

中文:
定义 pi
  签名: {α : 类型u} (β : α -> Profinite)
  定义体: .of (Π (a : α), β a)
-/
def pi {α : Type u} (β : α -> Profinite) : Profinite := .of (Π (a : α), β a)

end Profinite
