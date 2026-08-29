/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# The category of `X`-generated spaces

Let `X i` be a family of topological spaces. In this file, we define
the category `GeneratedByTopCat X` of `X`-generated spaces: this is
defined as a full subcategory of `TopCat`.

We also introduce an equivalent category `ContinuousGeneratedByCat X` whose
objects are all topological spaces, but morphisms from `Y` to `Z` identify
to the type `ContinuousMapGeneratedBy X Y Z` of `X`-continuous maps from
`Y` to `Z`. While `GeneratedByTopCat X` is defined as a full subcategory
of `TopCat`, `ContinuousGeneratedByCat X` should be thought of as
a localization of the category `TopCat` (for a proof of this fact, see the file
`Mathlib/Topology/Convenient/Localization.lean`). This alternative point of view
from the article by Martín Escardó, Jimmie Lawson and Alex Simpson
shall allow a very nice construction of a cartesian monoidal closed
structure on `GeneratedByTopCat X` under suitable assumptions (TODO @joelriou).

## References
* [Martín Escardó, Jimmie Lawson and Alex Simpson, *Comparing Cartesian closed
  categories of (core) compactly generated spaces*][escardo-lawson-simpson-2004]

-/

@[expose] public section

universe v t u

open CategoryTheory Topology Limits

variable {ι : Type t} (X : ι -> Type u) [forall i, TopologicalSpace (X i)]

/--
Definition of `TopCat.generatedBy` / `TopCat.generatedBy` 的定义

English:
abbreviation TopCat.generatedBy
  signature: : ObjectProperty TopCat.{v}
  body: fun Y => IsGeneratedBy X Y

中文:
缩写 顶元素范畴.generatedBy
  签名: : ObjectProperty 顶元素范畴.{v}
  定义体: fun Y => IsGeneratedBy X Y

Depends on / 依赖: IsGeneratedBy
-/
abbrev TopCat.generatedBy : ObjectProperty TopCat.{v} :=
  fun Y => IsGeneratedBy X Y

/--
lemma `TopCat.generatedBy_def` / 引理 `TopCat.generatedBy_def`

English:
lemma TopCat.generatedBy_def
  given: (Y : TopCat.{v})
  proof: Iff.rfl

中文:
引理 顶元素范畴.generatedBy_def
  条件: (Y : 顶元素范畴.{v})
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma TopCat.generatedBy_def (Y : TopCat.{v}) :
    generatedBy X Y ↔ IsGeneratedBy X Y := Iff.rfl

/--
Definition of `GeneratedByTopCat` / `GeneratedByTopCat` 的定义

English:
abbreviation GeneratedByTopCat
  body: (TopCat.generatedBy.{v} X).FullSubcategory

中文:
缩写 GeneratedByTopCat
  定义体: (TopCat.generatedBy.{v} X).FullSubcategory

Depends on / 依赖: FullSubcategory, TopCat, TopCat.generatedBy, generatedBy
-/
abbrev GeneratedByTopCat := (TopCat.generatedBy.{v} X).FullSubcategory

namespace GeneratedByTopCat

variable {X} in
/--
Definition of `toTopCat` / `toTopCat` 的定义

English:
abbreviation toTopCat
  signature: : GeneratedByTopCat.{v} X ⥤ TopCat.{v}
  body: ObjectProperty.ι _

中文:
缩写 toTopCat
  签名: : GeneratedByTopCat.{v} X ⥤ 顶元素范畴.{v}
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev toTopCat : GeneratedByTopCat.{v} X ⥤ TopCat.{v} := ObjectProperty.ι _

instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X (toTopCat.obj Y) := Y.property

/--
Definition of `fullyFaithfulToTopCat` / `fullyFaithfulToTopCat` 的定义

English:
abbreviation fullyFaithfulToTopCat
  signature: : (toTopCat.{v} (X := X)).FullyFaithful
  body: ObjectProperty.fullyFaithfulι _

中文:
缩写 fullyFaithfulToTopCat
  签名: : (toTopCat.{v} (X := X)).满忠实
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: FullyFaithful
-/
abbrev fullyFaithfulToTopCat : (toTopCat.{v} (X := X)).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {X} in
/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y]
  body: TopCat.of Y
  property := by assumption

中文:
缩写 of
  签名: (Y : 类型v) [拓扑空间 Y] [是GeneratedBy X Y]
  定义体: TopCat.of Y
  property := by assumption

Depends on / 依赖: TopCat, TopCat.of
-/
abbrev of (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] :
    GeneratedByTopCat.{v} X where
  obj := TopCat.of Y
  property := by assumption

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (GeneratedByTopCat.{v} X) (Type v)
  body: (Y.obj : Type v)

中文:
实例 :
  签名: CoeSort (GeneratedByTopCat.{v} X) (类型v)
  定义体: (Y.obj : Type v)

Depends on / 依赖: Y.obj
-/
instance : CoeSort (GeneratedByTopCat.{v} X) (Type v) where
  coe Y := (Y.obj : Type v)

instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X Y := Y.property

end GeneratedByTopCat

/--
Definition of `ContinuousGeneratedByCat` / `ContinuousGeneratedByCat` 的定义

English:
structure ContinuousGeneratedByCat
  parameters: (X : ι -> Type u) [forall i, TopologicalSpace (X i)]
  axioms and operations (3):
    - of : :
    - carrier : Type v
    - [str : TopologicalSpace carrier]

中文:
结构 余ntinuousGeneratedBy范畴
  参数: (X : ι -> 类型u) [对任意 i, 拓扑空间 (X i)]
  公理与运算 (3 个):
    - of : :
    - carrier : 类型v
    - [str : 拓扑空间 carrier]
-/
structure ContinuousGeneratedByCat (X : ι -> Type u) [forall i, TopologicalSpace (X i)] where
  /-- Constructor for objects in `ContinuousGeneratedByCat X`. -/
  of ::
  /-- The underlying type of an object in `ContinuousGeneratedByCat X`. -/
  carrier : Type v
  [str : TopologicalSpace carrier]

namespace ContinuousGeneratedByCat

variable {X}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (ContinuousGeneratedByCat.{v} X) (Type v)
  body: ⟨carrier⟩

中文:
实例 :
  签名: CoeSort (余ntinuousGeneratedBy范畴.{v} X) (类型v)
  定义体: ⟨carrier⟩

Depends on / 依赖: carrier
-/
instance : CoeSort (ContinuousGeneratedByCat.{v} X) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] str

/--
lemma `coe_of` / 引理 `coe_of`

English:
lemma coe_of
  given: (Y : Type v) [TopologicalSpace Y]
  statement: (of (X := X) Y : Type v) = Y
  proof: rfl

中文:
引理 coe_of
  条件: (Y : 类型v) [拓扑空间 Y]
  结论: (of (X := X) Y : 类型v) = Y
  证明: rfl
-/
lemma coe_of (Y : Type v) [TopologicalSpace Y] : (of (X := X) Y : Type v) = Y := rfl

/--
lemma `of_carrier` / 引理 `of_carrier`

English:
lemma of_carrier
  given: (Y : ContinuousGeneratedByCat.{v} X)
  statement: of (X := X) Y = Y
  proof: rfl

中文:
引理 of_carrier
  条件: (Y : 余ntinuousGeneratedBy范畴.{v} X)
  结论: of (X := X) Y = Y
  证明: rfl
-/
lemma of_carrier (Y : ContinuousGeneratedByCat.{v} X) : of (X := X) Y = Y := rfl

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (Y Z : ContinuousGeneratedByCat.{v} X)
  axioms and operations (1):
    - hom : ContinuousMapGeneratedBy X Y Z

中文:
结构 态射
  参数: (Y Z : 余ntinuousGeneratedBy范畴.{v} X)
  公理与运算 (1 个):
    - hom : 余ntinuousMapGeneratedBy X Y Z
-/
structure Hom (Y Z : ContinuousGeneratedByCat.{v} X) where
  /-- the underlying `X`-continuous map of a morphism in `ContinuousGeneratedByCat X`. -/
  hom : ContinuousMapGeneratedBy X Y Z

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (ContinuousGeneratedByCat.{v} X)
  body: Hom
  id X := { hom := .id }
  comp f g := {hom := g.hom.comp f.hom }

中文:
实例 :
  签名: 范畴 (余ntinuousGeneratedBy范畴.{v} X)
  定义体: Hom
  id X := { hom := .id }
  comp f g := {hom := g.hom.comp f.hom }
-/
instance : Category (ContinuousGeneratedByCat.{v} X) where
  Hom := Hom
  id X := { hom := .id }
  comp f g := {hom := g.hom.comp f.hom }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory.{v} (ContinuousGeneratedByCat.{v} X)
  body: Hom.hom
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴.{v} (余ntinuousGeneratedBy范畴.{v} X)
  定义体: Hom.hom
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory.{v} (ContinuousGeneratedByCat.{v} X)
    (fun Y Z => ContinuousMapGeneratedBy X Y Z) where
  hom := Hom.hom
  ofHom := Hom.mk

/-- Constructor for morphisms in `ContinuousGeneratedByCat X`. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y -> Z) (hf : ContinuousGeneratedBy X f)
  body: f
  hom.prop := hf

中文:
定义 homMk
  签名: {Y Z : 余ntinuousGeneratedBy范畴.{v} X} (f : Y -> Z) (hf : ContinuousGeneratedBy X f)
  定义体: f
  hom.prop := hf
-/
def homMk {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y -> Z) (hf : ContinuousGeneratedBy X f) :
    Y ⟶ Z where
  hom.toFun := f
  hom.prop := hf

/-- Use the abbreviation `TopCat.toContinuousGeneratedByCat` for the faithful
functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`. -/
@[simps! +dsimpLhs forget₂_obj forget₂_map_hom_apply]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasForget₂ TopCat.{v} (ContinuousGeneratedByCat.{v} X)
  body: .of Y
  forget₂.map f := ContinuousGeneratedByCat.homMk f (f.hom.continuous.continuousGeneratedBy)

中文:
实例 :
  签名: 有Forget₂ 顶元素范畴.{v} (余ntinuousGeneratedBy范畴.{v} X)
  定义体: .of Y
  forget₂.map f := ContinuousGeneratedByCat.homMk f (f.hom.continuous.continuousGeneratedBy)
-/
instance : HasForget₂ TopCat.{v} (ContinuousGeneratedByCat.{v} X) where
  forget₂.obj Y := .of Y
  forget₂.map f := ContinuousGeneratedByCat.homMk f (f.hom.continuous.continuousGeneratedBy)

end ContinuousGeneratedByCat

/--
Definition of `TopCat.toContinuousGeneratedByCat` / `TopCat.toContinuousGeneratedByCat` 的定义

English:
abbreviation TopCat.toContinuousGeneratedByCat
  signature: :
  body: forget₂ _ _

中文:
缩写 顶元素范畴.toContinuousGeneratedByCat
  签名: :
  定义体: forget₂ _ _
-/
abbrev TopCat.toContinuousGeneratedByCat :
    TopCat.{v} ⥤ ContinuousGeneratedByCat.{v} X := forget₂ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toContinuousGeneratedByCat.{v} X).Faithful
  body: inferInstance

中文:
实例 :
  签名: (顶元素范畴.toContinuousGeneratedByCat.{v} X).忠实
  定义体: inferInstance
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).Faithful := inferInstance

namespace ContinuousGeneratedByCat

/-- The functor `ContinuousGeneratedByCat X ⥤ TopCat` which sends a
topological space `Y` in the category `ContinuousGeneratedByCat X` to
the topological space `WithGeneratedByTopology X Y`. -/
@[simps obj]
/--
Definition of `toTopCat` / `toTopCat` 的定义

English:
definition toTopCat
  signature: : ContinuousGeneratedByCat.{v} X ⥤ TopCat where
  body: TopCat.of (WithGeneratedByTopology X Y)
  map f := TopCat.ofHom (f.hom.prop.continuousMap)

中文:
定义 toTopCat
  签名: : 余ntinuousGeneratedBy范畴.{v} X ⥤ 顶元素范畴 where
  定义体: TopCat.of (WithGeneratedByTopology X Y)
  map f := TopCat.ofHom (f.hom.prop.continuousMap)

Depends on / 依赖: TopCat, TopCat.of, WithGeneratedByTopology
-/
def toTopCat : ContinuousGeneratedByCat.{v} X ⥤ TopCat where
  obj Y := TopCat.of (WithGeneratedByTopology X Y)
  map f := TopCat.ofHom (f.hom.prop.continuousMap)

variable {X} in
/--
lemma `toTopCat_map_apply` / 引理 `toTopCat_map_apply`

English:
lemma toTopCat_map_apply
  statement: {Y Z : ContinuousGeneratedByCat.{v} X}
  proof: rfl

中文:
引理 toTopCat_map_apply
  结论: {Y Z : 余ntinuousGeneratedBy范畴.{v} X}
  证明: rfl
-/
lemma toTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X}
    (f : Y ⟶ Z) (y : WithGeneratedByTopology X ↑Y) :
    dsimp% (toTopCat X).map f y =
      (WithGeneratedByTopology.equiv (X := X)).symm
        (f (WithGeneratedByTopology.equiv y)) :=
  rfl

/--
Definition of `fullyFaithfulToTopCat` / `fullyFaithfulToTopCat` 的定义

English:
definition fullyFaithfulToTopCat
  signature: : (toTopCat.{v} X).FullyFaithful where
  body: homMk (WithGeneratedByTopology.equiv (X := X) ∘ g.hom ∘
      (WithGeneratedByTopology.equiv (X := X)).symm) (by
      rw [continuousGeneratedBy_iff]
      exact g.hom.continuous)

中文:
定义 fullyFaithfulToTopCat
  签名: : (toTopCat.{v} X).满忠实 where
  定义体: homMk (WithGeneratedByTopology.equiv (X := X) ∘ g.hom ∘
      (WithGeneratedByTopology.equiv (X := X)).symm) (by
      rw [continuousGeneratedBy_iff]
      exact g.hom.continuous)

Depends on / 依赖: WithGeneratedByTopology, WithGeneratedByTopology.equiv, continuous, continuousGeneratedBy_iff, g.hom, g.hom.continuous
-/
def fullyFaithfulToTopCat : (toTopCat.{v} X).FullyFaithful where
  preimage {Y Z} g :=
    homMk (WithGeneratedByTopology.equiv (X := X) ∘ g.hom ∘
      (WithGeneratedByTopology.equiv (X := X)).symm) (by
      rw [continuousGeneratedBy_iff]
      exact g.hom.continuous)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toTopCat.{v} X).Full
  body: (fullyFaithfulToTopCat X).full

中文:
实例 :
  签名: (toTopCat.{v} X).满
  定义体: (fullyFaithfulToTopCat X).full

Depends on / 依赖: fullyFaithfulToTopCat
-/
instance : (toTopCat.{v} X).Full := (fullyFaithfulToTopCat X).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toTopCat.{v} X).Faithful
  body: (fullyFaithfulToTopCat X).faithful

中文:
实例 :
  签名: (toTopCat.{v} X).忠实
  定义体: (fullyFaithfulToTopCat X).faithful

Depends on / 依赖: faithful, fullyFaithfulToTopCat
-/
instance : (toTopCat.{v} X).Faithful := (fullyFaithfulToTopCat X).faithful

variable {X}

/--
Definition of `adjUnitIso` / `adjUnitIso` 的定义

English:
definition adjUnitIso
  signature: :
  body: NatIso.ofComponents (fun Y =>
    { hom := { hom := WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X Y }
      inv := { hom := WithGeneratedByTopology.equivAsContinuousMapGeneratedBy X Y }})

中文:
定义 adjUnitIso
  签名: :
  定义体: NatIso.ofComponents (fun Y =>
    { hom := { hom := WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X Y }
      inv := { hom := WithGeneratedByTopology.equivAsContinuousMapGeneratedBy X Y }})

Depends on / 依赖: NatIso, NatIso.ofComponents, WithGeneratedByTopology, WithGeneratedByTopology.equivAsContinuousMapGeneratedBy, WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy, equivAsContinuousMapGeneratedBy, equivSymmAsContinuousMapGeneratedBy, ofComponents
-/
def adjUnitIso :
    𝟭 (ContinuousGeneratedByCat.{v} X) ≅ toTopCat X ⋙ TopCat.toContinuousGeneratedByCat X :=
  NatIso.ofComponents (fun Y =>
    { hom := { hom := WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X Y }
      inv := { hom := WithGeneratedByTopology.equivAsContinuousMapGeneratedBy X Y }})

/--
Definition of `adjCounit` / `adjCounit` 的定义

English:
definition adjCounit
  signature: : TopCat.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 TopCat where
  body: TopCat.ofHom (⟨_, WithGeneratedByTopology.continuous_equiv⟩)

中文:
定义 adjCounit
  签名: : 顶元素范畴.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 顶元素范畴 where
  定义体: TopCat.ofHom (⟨_, WithGeneratedByTopology.continuous_equiv⟩)

Depends on / 依赖: TopCat, TopCat.ofHom, WithGeneratedByTopology, WithGeneratedByTopology.continuous_equiv, continuous_equiv
-/
def adjCounit : TopCat.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 TopCat where
  app Z := TopCat.ofHom (⟨_, WithGeneratedByTopology.continuous_equiv⟩)

/-- The adjunction between the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
@[simps]
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : toTopCat.{v} X ⊣ TopCat.toContinuousGeneratedByCat X where
  body: adjUnitIso.hom
  counit := adjCounit

中文:
定义 adj
  签名: : toTopCat.{v} X ⊣ 顶元素范畴.toContinuousGeneratedByCat X where
  定义体: adjUnitIso.hom
  counit := adjCounit

Depends on / 依赖: adjUnitIso, adjUnitIso.hom
-/
def adj : toTopCat.{v} X ⊣ TopCat.toContinuousGeneratedByCat X where
  unit := adjUnitIso.hom
  counit := adjCounit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toTopCat.{v} X).IsLeftAdjoint
  body: adj.isLeftAdjoint

中文:
实例 :
  签名: (toTopCat.{v} X).是左伴随
  定义体: adj.isLeftAdjoint

Depends on / 依赖: adj.isLeftAdjoint, isLeftAdjoint
-/
instance : (toTopCat.{v} X).IsLeftAdjoint := adj.isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toContinuousGeneratedByCat.{v} X).IsRightAdjoint
  body: adj.isRightAdjoint

中文:
实例 :
  签名: (顶元素范畴.toContinuousGeneratedByCat.{v} X).是右伴随
  定义体: adj.isRightAdjoint

Depends on / 依赖: adj.isRightAdjoint, isRightAdjoint
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).IsRightAdjoint := adj.isRightAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toContinuousGeneratedByCat.{v} X).Faithful
  body: by ext x; exact ConcreteCategory.congr_hom h x

中文:
实例 :
  签名: (顶元素范畴.toContinuousGeneratedByCat.{v} X).忠实
  定义体: by ext x; exact ConcreteCategory.congr_hom h x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (adj.{v} (X := X)).unit
  body: inferInstanceAs (IsIso adjUnitIso.hom)

中文:
实例 :
  签名: 是同构 (adj.{v} (X := X)).unit
  定义体: inferInstanceAs (IsIso adjUnitIso.hom)

Depends on / 依赖: adjUnitIso, adjUnitIso.hom
-/
instance : IsIso (adj.{v} (X := X)).unit := inferInstanceAs (IsIso adjUnitIso.hom)

/-- The functor `GeneratedByTopCat X ⥤ ContinuousGeneratedByCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. It sends
an `X`-generated topological space `Y` to the topological space `Y`, considered as
an object of `ContinuousGeneratedByCat X`. -/
@[simps +dsimpLhs obj map_hom_apply]
/--
Definition of `fromGeneratedByTopCat` / `fromGeneratedByTopCat` 的定义

English:
definition fromGeneratedByTopCat
  signature: : GeneratedByTopCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  body: .of Y.obj
  map f := ⟨f, f.hom.hom.continuous.continuousGeneratedBy⟩

中文:
定义 fromGeneratedByTopCat
  签名: : GeneratedByTopCat.{v} X ⥤ 余ntinuousGeneratedBy范畴.{v} X where
  定义体: .of Y.obj
  map f := ⟨f, f.hom.hom.continuous.continuousGeneratedBy⟩

Depends on / 依赖: Y.obj
-/
def fromGeneratedByTopCat : GeneratedByTopCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Y := .of Y.obj
  map f := ⟨f, f.hom.hom.continuous.continuousGeneratedBy⟩

/--
Definition of `equivalenceFunctorIso` / `equivalenceFunctorIso` 的定义

English:
definition equivalenceFunctorIso
  signature: :
  body: NatIso.ofComponents (fun Y => TopCat.isoOfHomeo
    (IsGeneratedBy.homeomorph (Y := GeneratedByTopCat.toTopCat.obj Y)))

中文:
定义 equivalenceFunctorIso
  签名: :
  定义体: NatIso.ofComponents (fun Y => TopCat.isoOfHomeo
    (IsGeneratedBy.homeomorph (Y := GeneratedByTopCat.toTopCat.obj Y)))

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.toTopCat.obj, IsGeneratedBy, IsGeneratedBy.homeomorph, NatIso, NatIso.ofComponents, TopCat, TopCat.isoOfHomeo, homeomorph, isoOfHomeo, ofComponents, toTopCat
-/
def equivalenceFunctorIso :
    fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTopCat.toTopCat :=
  NatIso.ofComponents (fun Y => TopCat.isoOfHomeo
    (IsGeneratedBy.homeomorph (Y := GeneratedByTopCat.toTopCat.obj Y)))

/-- The functor `ContinuousGeneratedByCat X ⥤ GeneratedByTopCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
@[simps! obj]
/--
Definition of `toGeneratedByTopCat` / `toGeneratedByTopCat` 的定义

English:
definition toGeneratedByTopCat
  signature: : ContinuousGeneratedByCat.{v} X ⥤ GeneratedByTopCat.{v} X
  body: ObjectProperty.lift _ (toTopCat X) (fun Y => by
    rw [TopCat.generatedBy_def]
    exact inferInstanceAs (IsGeneratedBy X (WithGeneratedByTopology X ↑Y)))

中文:
定义 toGeneratedByTopCat
  签名: : 余ntinuousGeneratedBy范畴.{v} X ⥤ GeneratedByTopCat.{v} X
  定义体: ObjectProperty.lift _ (toTopCat X) (fun Y => by
    rw [TopCat.generatedBy_def]
    exact inferInstanceAs (IsGeneratedBy X (WithGeneratedByTopology X ↑Y)))

Depends on / 依赖: IsGeneratedBy, ObjectProperty, ObjectProperty.lift, TopCat, TopCat.generatedBy_def, WithGeneratedByTopology, generatedBy_def, toTopCat
-/
def toGeneratedByTopCat : ContinuousGeneratedByCat.{v} X ⥤ GeneratedByTopCat.{v} X :=
  ObjectProperty.lift _ (toTopCat X) (fun Y => by
    rw [TopCat.generatedBy_def]
    exact inferInstanceAs (IsGeneratedBy X (WithGeneratedByTopology X ↑Y)))

/--
lemma `toGeneratedByTopCat_map_apply` / 引理 `toGeneratedByTopCat_map_apply`

English:
lemma toGeneratedByTopCat_map_apply
  statement: {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y ⟶ Z)
  proof: rfl

中文:
引理 toGeneratedByTopCat_map_apply
  结论: {Y Z : 余ntinuousGeneratedBy范畴.{v} X} (f : Y ⟶ Z)
  证明: rfl
-/
lemma toGeneratedByTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y ⟶ Z)
    (y : WithGeneratedByTopology X Y) :
    dsimp% toGeneratedByTopCat.map f y =
      (WithGeneratedByTopology.equiv (X := X)).symm
        (f (WithGeneratedByTopology.equiv y)) := rfl

/--
Definition of `equivalenceUnitIso` / `equivalenceUnitIso` 的定义

English:
definition equivalenceUnitIso
  signature: :
  body: NatIso.ofComponents (fun Y =>
    (GeneratedByTopCat.fullyFaithfulToTopCat X).preimageIso
      (TopCat.isoOfHomeo IsGeneratedBy.homeomorph.symm))

中文:
定义 equivalenceUnitIso
  签名: :
  定义体: NatIso.ofComponents (fun Y =>
    (GeneratedByTopCat.fullyFaithfulToTopCat X).preimageIso
      (TopCat.isoOfHomeo IsGeneratedBy.homeomorph.symm))

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.fullyFaithfulToTopCat, IsGeneratedBy, IsGeneratedBy.homeomorph.symm, NatIso, NatIso.ofComponents, TopCat, TopCat.isoOfHomeo, fullyFaithfulToTopCat, homeomorph, isoOfHomeo, ofComponents, preimageIso
-/
def equivalenceUnitIso :
    𝟭 (GeneratedByTopCat.{v} X) ≅ fromGeneratedByTopCat ⋙ toGeneratedByTopCat :=
  NatIso.ofComponents (fun Y =>
    (GeneratedByTopCat.fullyFaithfulToTopCat X).preimageIso
      (TopCat.isoOfHomeo IsGeneratedBy.homeomorph.symm))

/--
Definition of `equivalenceCounitIso` / `equivalenceCounitIso` 的定义

English:
abbreviation equivalenceCounitIso
  signature: :
  body: adjUnitIso.symm

中文:
缩写 equivalenceCounitIso
  签名: :
  定义体: adjUnitIso.symm

Depends on / 依赖: adjUnitIso, adjUnitIso.symm
-/
abbrev equivalenceCounitIso :
    toGeneratedByTopCat ⋙ fromGeneratedByTopCat ≅ 𝟭 (ContinuousGeneratedByCat X) :=
  adjUnitIso.symm

/-- The equivalence of categories `GeneratedByTopCat X ≌ ContinuousGeneratedByCat X`. -/
@[simps]
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : GeneratedByTopCat.{v} X ≌ ContinuousGeneratedByCat.{v} X where
  body: fromGeneratedByTopCat
  inverse := toGeneratedByTopCat
  unitIso := equivalenceUnitIso
  counitIso := equivalenceCounitIso

中文:
定义 equivalence
  签名: : GeneratedByTopCat.{v} X ≌ 余ntinuousGeneratedBy范畴.{v} X where
  定义体: fromGeneratedByTopCat
  inverse := toGeneratedByTopCat
  unitIso := equivalenceUnitIso
  counitIso := equivalenceCounitIso

Depends on / 依赖: fromGeneratedByTopCat
-/
def equivalence : GeneratedByTopCat.{v} X ≌ ContinuousGeneratedByCat.{v} X where
  functor := fromGeneratedByTopCat
  inverse := toGeneratedByTopCat
  unitIso := equivalenceUnitIso
  counitIso := equivalenceCounitIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (fromGeneratedByTopCat.{v} (X := X)).IsEquivalence
  body: equivalence.isEquivalence_functor

中文:
实例 :
  签名: (fromGeneratedByTopCat.{v} (X := X)).是等价
  定义体: equivalence.isEquivalence_functor

Depends on / 依赖: IsEquivalence
-/
instance : (fromGeneratedByTopCat.{v} (X := X)).IsEquivalence :=
  equivalence.isEquivalence_functor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toGeneratedByTopCat.{v} (X := X)).IsEquivalence
  body: equivalence.isEquivalence_inverse

中文:
实例 :
  签名: (toGeneratedByTopCat.{v} (X := X)).是等价
  定义体: equivalence.isEquivalence_inverse

Depends on / 依赖: IsEquivalence
-/
instance : (toGeneratedByTopCat.{v} (X := X)).IsEquivalence :=
  equivalence.isEquivalence_inverse

end ContinuousGeneratedByCat

variable {X}

/--
Definition of `TopCat.toGeneratedByTopCat` / `TopCat.toGeneratedByTopCat` 的定义

English:
definition TopCat.toGeneratedByTopCat
  signature: : TopCat.{v} ⥤ GeneratedByTopCat X
  body: TopCat.toContinuousGeneratedByCat X ⋙ ContinuousGeneratedByCat.toGeneratedByTopCat

中文:
定义 顶元素范畴.toGeneratedByTopCat
  签名: : 顶元素范畴.{v} ⥤ GeneratedByTopCat X
  定义体: TopCat.toContinuousGeneratedByCat X ⋙ ContinuousGeneratedByCat.toGeneratedByTopCat

Depends on / 依赖: ContinuousGeneratedByCat, ContinuousGeneratedByCat.toGeneratedByTopCat, TopCat, TopCat.toContinuousGeneratedByCat, toContinuousGeneratedByCat, toGeneratedByTopCat
-/
def TopCat.toGeneratedByTopCat : TopCat.{v} ⥤ GeneratedByTopCat X :=
  TopCat.toContinuousGeneratedByCat X ⋙ ContinuousGeneratedByCat.toGeneratedByTopCat

namespace GeneratedByTopCat

/--
Definition of `adjUnitIso` / `adjUnitIso` 的定义

English:
definition adjUnitIso
  signature: : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ TopCat.toGeneratedByTopCat
  body: ContinuousGeneratedByCat.equivalenceUnitIso

中文:
定义 adjUnitIso
  签名: : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ 顶元素范畴.toGeneratedByTopCat
  定义体: ContinuousGeneratedByCat.equivalenceUnitIso

Depends on / 依赖: ContinuousGeneratedByCat, ContinuousGeneratedByCat.equivalenceUnitIso, equivalenceUnitIso
-/
def adjUnitIso : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ TopCat.toGeneratedByTopCat :=
  ContinuousGeneratedByCat.equivalenceUnitIso

/--
Definition of `adjCounit` / `adjCounit` 的定义

English:
definition adjCounit
  signature: : TopCat.toGeneratedByTopCat.{v} (X := X) ⋙ toTopCat ⟶ 𝟭 TopCat
  body: ContinuousGeneratedByCat.adjCounit

中文:
定义 adjCounit
  签名: : 顶元素范畴.toGeneratedByTopCat.{v} (X := X) ⋙ toTopCat ⟶ 𝟭 顶元素范畴
  定义体: ContinuousGeneratedByCat.adjCounit

Depends on / 依赖: TopCat, toTopCat
-/
def adjCounit : TopCat.toGeneratedByTopCat.{v} (X := X) ⋙ toTopCat ⟶ 𝟭 TopCat :=
  ContinuousGeneratedByCat.adjCounit

/-- The adjunction between the categories `GeneratedByTopCat X` and `TopCat`.
The left adjoint is the inclusion functor, and the right adjoint sends
a topological space `Y` to the underlying type of `Y` endowed with
the `X`-generated topology. -/
@[simps]
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : toTopCat.{v} (X := X) ⊣ TopCat.toGeneratedByTopCat where
  body: adjUnitIso.hom
  counit := adjCounit

中文:
定义 adj
  签名: : toTopCat.{v} (X := X) ⊣ 顶元素范畴.toGeneratedByTopCat where
  定义体: adjUnitIso.hom
  counit := adjCounit

Depends on / 依赖: TopCat, TopCat.toGeneratedByTopCat, toGeneratedByTopCat
-/
def adj : toTopCat.{v} (X := X) ⊣ TopCat.toGeneratedByTopCat where
  unit := adjUnitIso.hom
  counit := adjCounit

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (adj.{v} (X := X)).unit
  body: inferInstanceAs (IsIso adjUnitIso.hom)

中文:
实例 :
  签名: 是同构 (adj.{v} (X := X)).unit
  定义体: inferInstanceAs (IsIso adjUnitIso.hom)

Depends on / 依赖: adjUnitIso, adjUnitIso.hom
-/
instance : IsIso (adj.{v} (X := X)).unit := inferInstanceAs (IsIso adjUnitIso.hom)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (toTopCat.{v} (X := X)).IsLeftAdjoint
  body: adj.isLeftAdjoint

中文:
实例 :
  签名: (toTopCat.{v} (X := X)).是左伴随
  定义体: adj.isLeftAdjoint

Depends on / 依赖: IsLeftAdjoint, adj.isLeftAdjoint, isLeftAdjoint
-/
instance : (toTopCat.{v} (X := X)).IsLeftAdjoint := adj.isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toGeneratedByTopCat.{v} (X := X)).IsRightAdjoint
  body: adj.isRightAdjoint

中文:
实例 :
  签名: (顶元素范畴.toGeneratedByTopCat.{v} (X := X)).是右伴随
  定义体: adj.isRightAdjoint

Depends on / 依赖: IsRightAdjoint, adj.isRightAdjoint, isRightAdjoint
-/
instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).IsRightAdjoint := adj.isRightAdjoint

instance (Z : TopCat.{v}) :
    IsIso ((TopCat.toGeneratedByTopCat (X := X)).map
      ((GeneratedByTopCat.adjCounit (X := X)).app Z)) :=
  inferInstanceAs (IsIso (TopCat.toGeneratedByTopCat.map (GeneratedByTopCat.adj.counit.app Z)))

instance (Z : TopCat.{v}) :
    IsIso ((TopCat.toContinuousGeneratedByCat.{v} X).map
      ((GeneratedByTopCat.adjCounit (X := X)).app Z)) :=
  inferInstanceAs (IsIso ((TopCat.toContinuousGeneratedByCat X).map
    (ContinuousGeneratedByCat.adj.counit.app Z)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (TopCat.toGeneratedByTopCat.{v} (X := X)).Faithful
  body: by ext x; exact ConcreteCategory.congr_hom h x

中文:
实例 :
  签名: (顶元素范畴.toGeneratedByTopCat.{v} (X := X)).忠实
  定义体: by ext x; exact ConcreteCategory.congr_hom h x

Depends on / 依赖: Faithful
-/
instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coreflective (toTopCat.{v} (X := X))
  body: TopCat.toGeneratedByTopCat
  adj := adj

中文:
实例 :
  签名: 余反射 (toTopCat.{v} (X := X))
  定义体: TopCat.toGeneratedByTopCat
  adj := adj
-/
instance : Coreflective (toTopCat.{v} (X := X)) where
  R := TopCat.toGeneratedByTopCat
  adj := adj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesColimits (toTopCat.{v} (X := X))
  body: comonadicCreatesColimits _

中文:
实例 :
  签名: CreatesColimits (toTopCat.{v} (X := X))
  定义体: comonadicCreatesColimits _
-/
noncomputable instance : CreatesColimits (toTopCat.{v} (X := X)) :=
  comonadicCreatesColimits _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimits (GeneratedByTopCat X)
  body: hasLimits_of_coreflective toTopCat

中文:
实例 :
  签名: 有极限 (GeneratedByTopCat X)
  定义体: hasLimits_of_coreflective toTopCat

Depends on / 依赖: hasLimits_of_coreflective, toTopCat
-/
instance : HasLimits (GeneratedByTopCat X) :=
  hasLimits_of_coreflective toTopCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimits (GeneratedByTopCat X)
  body: hasColimits_of_hasColimits_createsColimits toTopCat

中文:
实例 :
  签名: 有余极限 (GeneratedByTopCat X)
  定义体: hasColimits_of_hasColimits_createsColimits toTopCat

Depends on / 依赖: hasColimits_of_hasColimits_createsColimits, toTopCat
-/
instance : HasColimits (GeneratedByTopCat X) :=
  hasColimits_of_hasColimits_createsColimits toTopCat

end GeneratedByTopCat
