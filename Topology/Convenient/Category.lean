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

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

/-- The property of objects of `TopCat` which is satisfied by `X`-generated spaces. -/
/-
**TopCat.generatedBy** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopCat.generatedBy : ObjectProperty TopCat.{v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects of `TopCat` which is satisfied by `X`-generated spaces.
-/
abbrev TopCat.generatedBy : ObjectProperty TopCat.{v} :=
  fun Y ↦ IsGeneratedBy X Y
/-
**TopCat.generatedBy_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopCat.generatedBy_def (Y : TopCat.{v}) : generatedBy X Y ↔ IsGeneratedBy 
X Y
参数：Y : TopCat.{v}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma TopCat.generatedBy_def (Y : TopCat.{v}) :
    generatedBy X Y ↔ IsGeneratedBy X Y := Iff.rfl

/-- The full subcategory of `TopCat` consisting of `X`-generated spaces. -/
/-
**GeneratedByTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GeneratedByTopCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of `TopCat` consisting of `X`-generated spaces.
-/
abbrev GeneratedByTopCat := (TopCat.generatedBy.{v} X).FullSubcategory

namespace GeneratedByTopCat

variable {X} in
/-- The inclusion functor `GeneratedByTopCat X ⥤ TopCat`. -/
/-
**GeneratedByTopCat.toTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `GeneratedByTopCat`。
形式化陈述：toTopCat : GeneratedByTopCat.{v} X ⥤ TopCat.{v}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `GeneratedByTopCat X ⥤ TopCat`.
-/
abbrev toTopCat : GeneratedByTopCat.{v} X ⥤ TopCat.{v} := ObjectProperty.ι _
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X (toTopCat.obj Y) := Y.property

/-- The inclusion functor `toTopCat : GeneratedByTopCat X ⥤ TopCat`
is fully faithful. -/
/-
**GeneratedByTopCat.fullyFaithfulToTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `Generated
ByTopCat`。
形式化陈述：fullyFaithfulToTopCat : (toTopCat.{v} (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `toTopCat : GeneratedByTopCat X ⥤ TopCat`
is fully faithful.
-/
abbrev fullyFaithfulToTopCat : (toTopCat.{v} (X := X)).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

variable {X} in
/-- Constructor for objects in the category of `X`-generated spaces. -/
/-
**GeneratedByTopCat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `GeneratedByTopCat`。
形式化陈述：of (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] : GeneratedByTopC
at.{v} X where obj
参数：Y : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects in the category of `X`-generated spaces.
-/
abbrev of (Y : Type v) [TopologicalSpace Y] [IsGeneratedBy X Y] :
    GeneratedByTopCat.{v} X where
  obj := TopCat.of Y
  property := by assumption
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (GeneratedByTopCat.{v} X) (Type v) where
  coe Y := (Y.obj : Type v)
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Y : GeneratedByTopCat.{v} X) : IsGeneratedBy X Y := Y.property

end GeneratedByTopCat

/-- Let `X i` be a family of topological spaces. This is the type of objects
in a category ` ContinuousGeneratedByCat X` where:
* objects are topological spaces;
* morphisms are `X`-continuous maps. -/
/-
**ContinuousGeneratedByCat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type t} → (X : ι → Type u) → [(i : ι) → TopologicalSpace (X i)] → Typ
e (v + 1)
参数：X : ι → Type u；i : ι；X i；v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `X i` be a family of topological spaces. This is the type of objects
in a category ` ContinuousGeneratedByCat X` where:
* objects are topological spaces;
* morphisms are `X`-continuous maps.
-/
structure ContinuousGeneratedByCat (X : ι → Type u) [∀ i, TopologicalSpace (X i)] where
  /-- Constructor for objects in `ContinuousGeneratedByCat X`. -/
  of ::
  /-- The underlying type of an object in `ContinuousGeneratedByCat X`. -/
  carrier : Type v
  [str : TopologicalSpace carrier]

namespace ContinuousGeneratedByCat

variable {X}

/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (ContinuousGeneratedByCat.{v} X) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

attribute [instance] str
/-
**ContinuousGeneratedByCat.coe_of** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousGenerated
ByCat`。
形式化陈述：coe_of (Y : Type v) [TopologicalSpace Y] : (of (X
参数：Y : Type v。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_of (Y : Type v) [TopologicalSpace Y] : (of (X := X) Y : Type v) = Y := rfl
/-
**ContinuousGeneratedByCat.of_carrier** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousGener
atedByCat`。
形式化陈述：of_carrier (Y : ContinuousGeneratedByCat.{v} X) : of (X
参数：Y : ContinuousGeneratedByCat.{v} X。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma of_carrier (Y : ContinuousGeneratedByCat.{v} X) : of (X := X) Y = Y := rfl

/-- The type of morphisms in the category `ContinuousGeneratedByCat X` is
a one-field structure containing a field of type `ContinuousMapGeneratedBy`,
i.e. `X`-continuous maps. -/
/-
**ContinuousGeneratedByCat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousGeneratedB
yCat`。
形式化陈述：{ι : Type t} →   {X : ι → Type u} →     [inst : (i : ι) → TopologicalSpace
 (X i)] → ContinuousGeneratedByCat X → ContinuousGeneratedByCat X → Type v
参数：i : ι；X i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `ContinuousGeneratedByCat X` is
a one-field structure containing a field of type `ContinuousMapGeneratedBy`,
i.e. `X`-continuous maps.
-/
structure Hom (Y Z : ContinuousGeneratedByCat.{v} X) where
  /-- the underlying `X`-continuous map of a morphism in `ContinuousGeneratedByCat X`. -/
  hom : ContinuousMapGeneratedBy X Y Z
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (ContinuousGeneratedByCat.{v} X) where
  Hom := Hom
  id X := { hom := .id }
  comp f g := {hom := g.hom.comp f.hom }
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory.{v} (ContinuousGeneratedByCat.{v} X)
    (fun Y Z ↦ ContinuousMapGeneratedBy X Y Z) where
  hom := Hom.hom
  ofHom := Hom.mk

/-- Constructor for morphisms in `ContinuousGeneratedByCat X`. -/
@[simps]
/-
**ContinuousGeneratedByCat.homMk** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousGeneratedB
yCat`。
形式化陈述：homMk {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y -> Z) (hf : Continuous
GeneratedBy X f) : Y ⟶ Z where hom.toFun
参数：f : Y -> Z；hf : ContinuousGeneratedBy X f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ContinuousGeneratedByCat X`.
-/
def homMk {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y → Z) (hf : ContinuousGeneratedBy X f) :
    Y ⟶ Z where
  hom.toFun := f
  hom.prop := hf

/-- Use the abbreviation `TopCat.toContinuousGeneratedByCat` for the faithful
functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`. -/
@[simps! +dsimpLhs forget₂_obj forget₂_map_hom_apply]
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the abbreviation `TopCat.toContinuousGeneratedByCat` for the faithful
functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`.
-/
instance : HasForget₂ TopCat.{v} (ContinuousGeneratedByCat.{v} X) where
  forget₂.obj Y := .of Y
  forget₂.map f := ContinuousGeneratedByCat.homMk f (f.hom.continuous.continuousGeneratedBy)

end ContinuousGeneratedByCat

/-- The faithful functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`. -/
/-
**TopCat.toContinuousGeneratedByCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopCat.toContinuousGeneratedByCat : TopCat.{v} ⥤ ContinuousGeneratedByCat.
{v} X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The faithful functor `TopCat ⥤ ContinuousGeneratedByCat X` which sends
a topological space `Y` to the same type `Y`, with the same topology, but
considered as an object of `ContinuousGeneratedByCat X`.
-/
abbrev TopCat.toContinuousGeneratedByCat :
    TopCat.{v} ⥤ ContinuousGeneratedByCat.{v} X := forget₂ _ _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).Faithful := inferInstance

namespace ContinuousGeneratedByCat

/-- The functor `ContinuousGeneratedByCat X ⥤ TopCat` which sends a
topological space `Y` in the category `ContinuousGeneratedByCat X` to
the topological space `WithGeneratedByTopology X Y`. -/
@[simps obj]
/-
**ContinuousGeneratedByCat.toTopCat** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousGenerat
edByCat`。
形式化陈述：toTopCat : ContinuousGeneratedByCat.{v} X ⥤ TopCat where obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ContinuousGeneratedByCat X ⥤ TopCat` which sends a
topological space `Y` in the category `ContinuousGeneratedByCat X` to
the topological space `WithGeneratedByTopology X Y`.
-/
def toTopCat : ContinuousGeneratedByCat.{v} X ⥤ TopCat where
  obj Y := TopCat.of (WithGeneratedByTopology X Y)
  map f := TopCat.ofHom (f.hom.prop.continuousMap)

variable {X} in
/-
**ContinuousGeneratedByCat.toTopCat_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousGeneratedByCat`。
形式化陈述：toTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y ⟶ Z) (y :
 WithGeneratedByTopology X ↑Y) : dsimp% (toTopCat X).map f y = (WithGeneratedByT
opology.equiv (X
参数：f : Y ⟶ Z；y : WithGeneratedByTopology X ↑Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X}
    (f : Y ⟶ Z) (y : WithGeneratedByTopology X ↑Y) :
    dsimp% (toTopCat X).map f y =
      (WithGeneratedByTopology.equiv (X := X)).symm
        (f (WithGeneratedByTopology.equiv y)) :=
  rfl

/-- The functor `ContinuousGeneratedByCat.toTopCat : ContinuousGeneratedByCat X ⥤ TopCat`
is fully faithful. -/
/-
**ContinuousGeneratedByCat.fullyFaithfulToTopCat** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousGeneratedByCat`。
形式化陈述：fullyFaithfulToTopCat : (toTopCat.{v} X).FullyFaithful where preimage {Y Z
} g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The functor `ContinuousGeneratedByCat.toTopCat : ContinuousGeneratedByCat X ⥤ To
pCat`
is fully faithful.
-/
def fullyFaithfulToTopCat : (toTopCat.{v} X).FullyFaithful where
  preimage {Y Z} g :=
    homMk (WithGeneratedByTopology.equiv (X := X) ∘ g.hom ∘
      (WithGeneratedByTopology.equiv (X := X)).symm) (by
      rw [continuousGeneratedBy_iff]
      exact g.hom.continuous)
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toTopCat.{v} X).Full := (fullyFaithfulToTopCat X).full
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toTopCat.{v} X).Faithful := (fullyFaithfulToTopCat X).faithful

variable {X}

/-- The unit (isomorphism) of the adjunction `ContinuousGeneratedByCat.adj` between
the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
/-
**ContinuousGeneratedByCat.adjUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousGener
atedByCat`。
形式化陈述：adjUnitIso : 𝟭 (ContinuousGeneratedByCat.{v} X) ≅ toTopCat X ⋙ TopCat.toCo
ntinuousGeneratedByCat X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit (isomorphism) of the adjunction `ContinuousGeneratedByCat.adj` between
the categories `ContinuousGeneratedByCat X` and `TopCat`.
-/
def adjUnitIso :
    𝟭 (ContinuousGeneratedByCat.{v} X) ≅ toTopCat X ⋙ TopCat.toContinuousGeneratedByCat X :=
  NatIso.ofComponents (fun Y ↦
    { hom := { hom := WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy X Y }
      inv := { hom := WithGeneratedByTopology.equivAsContinuousMapGeneratedBy X Y }})

/-- The counit of the adjunction `ContinuousGeneratedByCat.adj` between
the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
/-
**ContinuousGeneratedByCat.adjCounit** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousGenera
tedByCat`。
形式化陈述：adjCounit : TopCat.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 TopCa
t where app Z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the adjunction `ContinuousGeneratedByCat.adj` between
the categories `ContinuousGeneratedByCat X` and `TopCat`.
-/
def adjCounit : TopCat.toContinuousGeneratedByCat.{v} X ⋙ toTopCat X ⟶ 𝟭 TopCat where
  app Z := TopCat.ofHom (⟨_,  WithGeneratedByTopology.continuous_equiv⟩)

/-- The adjunction between the categories `ContinuousGeneratedByCat X` and `TopCat`. -/
@[simps]
/-
**ContinuousGeneratedByCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousGeneratedByC
at`。
形式化陈述：adj : toTopCat.{v} X ⊣ TopCat.toContinuousGeneratedByCat X where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the categories `ContinuousGeneratedByCat X` and `TopCat`.
-/
def adj : toTopCat.{v} X ⊣ TopCat.toContinuousGeneratedByCat X where
  unit := adjUnitIso.hom
  counit := adjCounit
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toTopCat.{v} X).IsLeftAdjoint := adj.isLeftAdjoint
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).IsRightAdjoint := adj.isRightAdjoint
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (TopCat.toContinuousGeneratedByCat.{v} X).Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (adj.{v} (X := X)).unit := inferInstanceAs (IsIso adjUnitIso.hom)

/-- The functor `GeneratedByTopCat X ⥤ ContinuousGeneratedByCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. It sends
an `X`-generated topological space `Y` to the topological space `Y`, considered as
an object of `ContinuousGeneratedByCat X`. -/
@[simps +dsimpLhs obj map_hom_apply]
/-
**ContinuousGeneratedByCat.fromGeneratedByTopCat** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousGeneratedByCat`。
形式化陈述：fromGeneratedByTopCat : GeneratedByTopCat.{v} X ⥤ ContinuousGeneratedByCat
.{v} X where obj Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `GeneratedByTopCat X ⥤ ContinuousGeneratedByCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. It sends
an `X`-generated topological space `Y` to the topological space `Y`, considered 
as
an object of `ContinuousGeneratedByCat X`.
-/
def fromGeneratedByTopCat : GeneratedByTopCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Y := .of Y.obj
  map f := ⟨f, f.hom.hom.continuous.continuousGeneratedBy⟩

/-- The isomorphism between
`fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTopCat.toTopCat`. -/
/-
**ContinuousGeneratedByCat.equivalenceFunctorIso** 是 Mathlib 中的一个定义，位于命名空间 `Cont
inuousGeneratedByCat`。
形式化陈述：equivalenceFunctorIso : fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTo
pCat.toTopCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GeneratedByTopCat.instIsGeneratedByCarrierObjTopCatToTopCat`：∀ {ι : Type
 t} (X : ι → Type u) [inst : (i : ι) → TopologicalSpace (X i)] (Y : GeneratedByT
opCat X),   Topology.IsGeneratedBy X ↑(GeneratedB…

--- 原说明 ---
The isomorphism between
`fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTopCat.toTopCat`.
-/
def equivalenceFunctorIso :
    fromGeneratedByTopCat ⋙ toTopCat X ≅ GeneratedByTopCat.toTopCat :=
  NatIso.ofComponents (fun Y ↦ TopCat.isoOfHomeo
    (IsGeneratedBy.homeomorph (Y := GeneratedByTopCat.toTopCat.obj Y)))

/-- The functor `ContinuousGeneratedByCat X ⥤ GeneratedByTopCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
@[simps! obj]
/-
**ContinuousGeneratedByCat.toGeneratedByTopCat** 是 Mathlib 中的一个定义，位于命名空间 `Contin
uousGeneratedByCat`。
形式化陈述：toGeneratedByTopCat : ContinuousGeneratedByCat.{v} X ⥤ GeneratedByTopCat.{
v} X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ContinuousGeneratedByCat X ⥤ GeneratedByTopCat X` which is
part of the equivalence `ContinuousGeneratedByCat.equivalence`.
-/
def toGeneratedByTopCat : ContinuousGeneratedByCat.{v} X ⥤ GeneratedByTopCat.{v} X :=
  ObjectProperty.lift _ (toTopCat X) (fun Y ↦ by
    rw [TopCat.generatedBy_def]
    exact inferInstanceAs (IsGeneratedBy X (WithGeneratedByTopology X ↑Y)))
/-
**ContinuousGeneratedByCat.toGeneratedByTopCat_map_apply** 是 Mathlib 中的一个引理，位于命名
空间 `ContinuousGeneratedByCat`。
形式化陈述：toGeneratedByTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X} (f : 
Y ⟶ Z) (y : WithGeneratedByTopology X Y) : dsimp% toGeneratedByTopCat.map f y = 
(WithGeneratedByTopology.equiv (X
参数：f : Y ⟶ Z；y : WithGeneratedByTopology X Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toGeneratedByTopCat_map_apply {Y Z : ContinuousGeneratedByCat.{v} X} (f : Y ⟶ Z)
    (y : WithGeneratedByTopology X Y) :
    dsimp% toGeneratedByTopCat.map f y =
      (WithGeneratedByTopology.equiv (X := X)).symm
        (f (WithGeneratedByTopology.equiv y)) := rfl

/-- The unit isomorphism of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
/-
**ContinuousGeneratedByCat.equivalenceUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `Continu
ousGeneratedByCat`。
形式化陈述：equivalenceUnitIso : 𝟭 (GeneratedByTopCat.{v} X) ≅ fromGeneratedByTopCat ⋙
 toGeneratedByTopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit isomorphism of the equivalence `ContinuousGeneratedByCat.equivalence`.
-/
def equivalenceUnitIso :
    𝟭 (GeneratedByTopCat.{v} X) ≅ fromGeneratedByTopCat ⋙ toGeneratedByTopCat :=
  NatIso.ofComponents (fun Y ↦
    (GeneratedByTopCat.fullyFaithfulToTopCat X).preimageIso
      (TopCat.isoOfHomeo IsGeneratedBy.homeomorph.symm))

/-- The counit isomorphism of the equivalence `ContinuousGeneratedByCat.equivalence`. -/
/-
**ContinuousGeneratedByCat.equivalenceCounitIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `Con
tinuousGeneratedByCat`。
形式化陈述：equivalenceCounitIso : toGeneratedByTopCat ⋙ fromGeneratedByTopCat ≅ 𝟭 (Co
ntinuousGeneratedByCat X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit isomorphism of the equivalence `ContinuousGeneratedByCat.equivalence`
.
-/
abbrev equivalenceCounitIso :
    toGeneratedByTopCat ⋙ fromGeneratedByTopCat ≅ 𝟭 (ContinuousGeneratedByCat X) :=
  adjUnitIso.symm

/-- The equivalence of categories `GeneratedByTopCat X ≌ ContinuousGeneratedByCat X`. -/
@[simps]
/-
**ContinuousGeneratedByCat.equivalence** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousGene
ratedByCat`。
形式化陈述：equivalence : GeneratedByTopCat.{v} X ≌ ContinuousGeneratedByCat.{v} X whe
re functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `GeneratedByTopCat X ≌ ContinuousGeneratedByCat X`
.
-/
def equivalence : GeneratedByTopCat.{v} X ≌ ContinuousGeneratedByCat.{v} X where
  functor := fromGeneratedByTopCat
  inverse := toGeneratedByTopCat
  unitIso := equivalenceUnitIso
  counitIso := equivalenceCounitIso
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (fromGeneratedByTopCat.{v} (X := X)).IsEquivalence :=
  equivalence.isEquivalence_functor
/-
**ContinuousGeneratedByCat.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousGeneratedByCat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toGeneratedByTopCat.{v} (X := X)).IsEquivalence :=
  equivalence.isEquivalence_inverse

end ContinuousGeneratedByCat

variable {X}

/-- The functor `TopCat.{v} ⥤ GeneratedByTopCat X`. -/
/-
**TopCat.toGeneratedByTopCat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TopCat.toGeneratedByTopCat : TopCat.{v} ⥤ GeneratedByTopCat X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `TopCat.{v} ⥤ GeneratedByTopCat X`.
-/
def TopCat.toGeneratedByTopCat : TopCat.{v} ⥤ GeneratedByTopCat X :=
  TopCat.toContinuousGeneratedByCat X ⋙ ContinuousGeneratedByCat.toGeneratedByTopCat

namespace GeneratedByTopCat

/-- The unit (isomorphism) of the adjunction `GeneratedByTopCat.adj` between
the categories `GeneratedByTopCat X` and `TopCat`. -/
/-
**GeneratedByTopCat.adjUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `GeneratedByTopCat`。
形式化陈述：adjUnitIso : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ TopCat.toGeneratedBy
TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit (isomorphism) of the adjunction `GeneratedByTopCat.adj` between
the categories `GeneratedByTopCat X` and `TopCat`.
-/
def adjUnitIso : 𝟭 (GeneratedByTopCat.{v} X) ≅ toTopCat ⋙ TopCat.toGeneratedByTopCat :=
  ContinuousGeneratedByCat.equivalenceUnitIso

/-- The counit of the adjunction `GeneratedByTopCat.adj` between
the categories `GeneratedByTopCat X` and `TopCat`. -/
/-
**GeneratedByTopCat.adjCounit** 是 Mathlib 中的一个定义，位于命名空间 `GeneratedByTopCat`。
形式化陈述：adjCounit : TopCat.toGeneratedByTopCat.{v} (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit of the adjunction `GeneratedByTopCat.adj` between
the categories `GeneratedByTopCat X` and `TopCat`.
-/
def adjCounit : TopCat.toGeneratedByTopCat.{v} (X := X) ⋙ toTopCat ⟶ 𝟭 TopCat :=
  ContinuousGeneratedByCat.adjCounit

/-- The adjunction between the categories `GeneratedByTopCat X` and `TopCat`.
The left adjoint is the inclusion functor, and the right adjoint sends
a topological space `Y` to the underlying type of `Y` endowed with
the `X`-generated topology. -/
@[simps]
/-
**GeneratedByTopCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `GeneratedByTopCat`。
形式化陈述：adj : toTopCat.{v} (X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between the categories `GeneratedByTopCat X` and `TopCat`.
The left adjoint is the inclusion functor, and the right adjoint sends
a topological space `Y` to the underlying type of `Y` endowed with
the `X`-generated topology.
-/
def adj : toTopCat.{v} (X := X) ⊣ TopCat.toGeneratedByTopCat where
  unit := adjUnitIso.hom
  counit := adjCounit
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (adj.{v} (X := X)).unit := inferInstanceAs (IsIso adjUnitIso.hom)
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toTopCat.{v} (X := X)).IsLeftAdjoint := adj.isLeftAdjoint
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).IsRightAdjoint := adj.isRightAdjoint
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Z : TopCat.{v}) :
    IsIso ((TopCat.toGeneratedByTopCat (X := X)).map
      ((GeneratedByTopCat.adjCounit (X := X)).app Z)) :=
  inferInstanceAs (IsIso (TopCat.toGeneratedByTopCat.map (GeneratedByTopCat.adj.counit.app Z)))
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Z : TopCat.{v}) :
    IsIso ((TopCat.toContinuousGeneratedByCat.{v} X).map
      ((GeneratedByTopCat.adjCounit (X := X)).app Z)) :=
  inferInstanceAs (IsIso ((TopCat.toContinuousGeneratedByCat X).map
    (ContinuousGeneratedByCat.adj.counit.app Z)))
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (TopCat.toGeneratedByTopCat.{v} (X := X)).Faithful where
  map_injective h := by ext x; exact ConcreteCategory.congr_hom h x

/-- The category of `X`-generated spaces is coreflective in the category of topological spaces. -/
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of `X`-generated spaces is coreflective in the category of topologi
cal spaces.
-/
instance : Coreflective (toTopCat.{v} (X := X)) where
  R := TopCat.toGeneratedByTopCat
  adj := adj
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesColimits (toTopCat.{v} (X := X)) :=
  comonadicCreatesColimits _
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimits (GeneratedByTopCat X) :=
  hasLimits_of_coreflective toTopCat
/-
**GeneratedByTopCat.** 是 Mathlib 中的一个实例，位于命名空间 `GeneratedByTopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasColimits (GeneratedByTopCat X) :=
  hasColimits_of_hasColimits_createsColimits toTopCat

end GeneratedByTopCat

