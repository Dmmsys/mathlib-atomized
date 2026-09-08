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
/-
**Profinite** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：Profinite where toCompHaus : CompHaus [isTotallyDisconnected : TotallyDisc
onnectedSpace toCompHaus] ```  The categories `Stonean` consisting of extremally
 disconnected compact Hausdorff spaces and `LightProfinite` consisting of totall
y disconnected, second countable compact Hausdorff spaces were defined in a simi
lar way. This resulted in code duplication, and reducing this duplication was pa
rt of the motivation for introducing `CompHausLike`.  Using `CompHausLike`, we c
an now define `CompHaus
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of profinite topological spaces.
-/
abbrev Profinite := CompHausLike (fun X ↦ TotallyDisconnectedSpace X)

namespace Profinite

/-
**Profinite.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] : HasProp (fun Y ↦ TotallyDisconnectedSpace Y) X :=
  ⟨(inferInstance : TotallyDisconnectedSpace X)⟩

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
/-
**Profinite.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Profinite`。
形式化陈述：of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyD
isconnectedSpace X] : Profinite
参数：X : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X

--- 原说明 ---
Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] : Profinite :=
  CompHausLike.of _ X
/-
**Profinite.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Profinite :=
  ⟨Profinite.of PEmpty⟩
/-
**Profinite.** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Profinite} : TotallyDisconnectedSpace X :=
  X.prop

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
/-
**profiniteToCompHaus** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：profiniteToCompHaus : Profinite ⥤ CompHaus
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful embedding of `Profinite` in `CompHaus`.
-/
abbrev profiniteToCompHaus : Profinite ⥤ CompHaus :=
  compHausLikeToCompHaus _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Profinite} : TotallyDisconnectedSpace (profiniteToCompHaus.obj X) :=
  X.prop

/-- The fully faithful embedding of `Profinite` in `TopCat`.
This is definitionally the same as the obvious composite. -/
/-
**Profinite.toTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Profinite.toTopCat : Profinite ⥤ TopCat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully faithful embedding of `Profinite` in `TopCat`.
This is definitionally the same as the obvious composite.
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
/-
**CompHaus.toProfiniteObj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where toTop
参数：X : CompHaus.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) The object part of the `connectedComponents` functor from compa
ct Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
-/
def CompHaus.toProfiniteObj (X : CompHaus.{u}) : Profinite.{u} where
  toTop := TopCat.of (ConnectedComponents X)
  is_compact := Quotient.compactSpace
  is_hausdorff := ConnectedComponents.t2
  prop := ConnectedComponents.totallyDisconnectedSpace

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
/-
**Profinite.toCompHausEquivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) : (
CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where toFun f
参数：X : CompHaus.{u}；Y : Profinite.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop

--- 原说明 ---
(Implementation) The bijection of homsets to establish the reflective adjunction
 of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.toCompHausEquivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
    (CompHaus.toProfiniteObj X ⟶ Y) ≃ (X ⟶ profiniteToCompHaus.obj Y) where
  toFun f := ofHom _ (f.hom.hom.comp ⟨Quotient.mk'', continuous_quotient_mk'⟩)
  invFun g := ConcreteCategory.ofHom
    { toFun := Continuous.connectedComponentsLift g.hom.hom.2
      continuous_toFun := Continuous.connectedComponentsLift_continuous g.hom.hom.2 }
  left_inv f :=
    InducedCategory.hom_ext (TopCat.ext (fun y ↦ by
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe y
      rfl))

/-- The `connectedComponents` functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
/-
**CompHaus.toProfinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompHaus.toProfinite : CompHaus ⥤ Profinite
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `connectedComponents` functor from compact Hausdorff spaces to profinite spa
ces,
left adjoint to the inclusion functor.
-/
def CompHaus.toProfinite : CompHaus ⥤ Profinite :=
  Adjunction.leftAdjointOfEquiv Profinite.toCompHausEquivalence fun _ _ _ _ _ => rfl
/-
**CompHaus.toProfinite_obj'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompHaus.toProfinite_obj' (X : CompHaus) : ↥(CompHaus.toProfinite.obj X) =
 ConnectedComponents X
参数：X : CompHaus。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CompHaus.toProfinite_obj' (X : CompHaus) :
    ↥(CompHaus.toProfinite.obj X) = ConnectedComponents X :=
  rfl

/-- Finite types are given the discrete topology. -/
@[instance_reducible]
/-
**FintypeCat.botTopology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A
参数：A : FintypeCat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite types are given the discrete topology.
-/
def FintypeCat.botTopology (A : FintypeCat) : TopologicalSpace A := ⊥

section DiscreteTopology

attribute [local instance] FintypeCat.botTopology

/-
**FintypeCat.discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A
参数：A : FintypeCat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem FintypeCat.discreteTopology (A : FintypeCat) : DiscreteTopology A :=
  ⟨rfl⟩

attribute [local instance] FintypeCat.discreteTopology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps! -isSimp map_hom_hom_apply obj]
/-
**FintypeCat.toProfinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FintypeCat.toProfinite : FintypeCat ⥤ Profinite where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural functor from `Fintype` to `Profinite`, endowing a finite type with t
he
discrete topology.
-/
def FintypeCat.toProfinite : FintypeCat ⥤ Profinite where
  obj A := Profinite.of A
  map f := ofHom _ ⟨f, by fun_prop⟩

/-- `FintypeCat.toLightProfinite` is fully faithful. -/
/-
**FintypeCat.toProfiniteFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FintypeCat.toProfiniteFullyFaithful : toProfinite.FullyFaithful where prei
mage f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`FintypeCat.toLightProfinite` is fully faithful.
-/
def FintypeCat.toProfiniteFullyFaithful : toProfinite.FullyFaithful where
  preimage f := InducedCategory.homMk <| ↾(f : _ → _)
  map_preimage _ := rfl
  preimage_map _ := rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FintypeCat.toProfinite.Faithful := FintypeCat.toProfiniteFullyFaithful.faithful
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FintypeCat.toProfinite.Full := FintypeCat.toProfiniteFullyFaithful.full
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FintypeCat) : Finite (FintypeCat.toProfinite.obj X) := inferInstanceAs (Finite X)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : FintypeCat) : Finite (Profinite.of X) := inferInstanceAs (Finite X)

end DiscreteTopology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
/-
**Profinite.limitCone** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : L
imits.Cone F where pt
参数：F : J ⥤ Profinite.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`.
-/
def limitCone {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u v}) : Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).pt.toTop
      prop := by
        change TotallyDisconnectedSpace ({ u : ∀ j : J, F.obj j | _ } : Type _)
        exact Subtype.totallyDisconnectedSpace }
  π :=
  { app j := InducedCategory.homMk
        (((CompHaus.limitCone.{v, u} (F ⋙ profiniteToCompHaus)).π.app j).hom)
    -- Porting note: was `by tidy`:
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/-- The limit cone `Profinite.limitCone F` is indeed a limit cone. -/
/-
**Profinite.limitConeIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：limitConeIsLimit {J : Type v} [SmallCategory J] (F : J ⥤ Profinite.{max u 
v}) : Limits.IsLimit (limitCone F) where lift S
参数：F : J ⥤ Profinite.{max u v}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone `Profinite.limitCone F` is indeed a limit cone.
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
        (fun j ↦ by
          simp [← h]
          rfl))

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
/-
**Profinite.toProfiniteAdjToCompHaus** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus
-/
def toProfiniteAdjToCompHaus : CompHaus.toProfinite ⊣ profiniteToCompHaus :=
  Adjunction.adjunctionOfEquivLeft _ _

/-- The category of profinite sets is reflective in the category of compact Hausdorff spaces -/
/-
**Profinite.toCompHaus.reflective** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.toCompHau
s`。
形式化陈述：CategoryTheory.Reflective profiniteToCompHaus
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of profinite sets is reflective in the category of compact Hausdorf
f spaces
-/
instance toCompHaus.reflective : Reflective profiniteToCompHaus where
  L := CompHaus.toProfinite
  adj := Profinite.toProfiniteAdjToCompHaus
/-
**Profinite.toCompHaus.createsLimits** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.toComp
Haus`。
形式化陈述：CategoryTheory.CreatesLimits profiniteToCompHaus
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance toCompHaus.createsLimits : CreatesLimits profiniteToCompHaus :=
  monadicCreatesLimits _
/-
**Profinite.toTopCat.reflective** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.toTopCat`。
形式化陈述：CategoryTheory.Reflective Profinite.toTopCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance toTopCat.reflective : Reflective Profinite.toTopCat :=
  Reflective.comp profiniteToCompHaus compHausToTop
/-
**Profinite.toTopCat.createsLimits** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.toTopCat
`。
形式化陈述：CategoryTheory.CreatesLimits Profinite.toTopCat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance toTopCat.createsLimits : CreatesLimits Profinite.toTopCat :=
  monadicCreatesLimits _
/-
**Profinite.hasLimits** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：hasLimits : Limits.HasLimits Profinite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimits_of_hasLimits_createsLimits`：hasLimits_of_hasLim
its_createsLimits (F : C ⥤ D) [HasLimitsOfSize.{w, w'} D] [CreatesLimitsOfSize.{
w, w'} F] : HasLimitsOfSize.{w, w'} C
-/
instance hasLimits : Limits.HasLimits Profinite :=
  hasLimits_of_hasLimits_createsLimits Profinite.toTopCat
/-
**Profinite.hasColimits** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：hasColimits : Limits.HasColimits Profinite
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimits_of_reflective`：hasColimits_of_reflective (R :
 D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] : HasColimitsOfSize.{v, u} D
-/
instance hasColimits : Limits.HasColimits Profinite :=
  hasColimits_of_reflective profiniteToCompHaus
/-
**Profinite.forget_preservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Profinite`。
形式化陈述：forget_preservesLimits : Limits.PreservesLimits (forget Profinite)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.instIsRightAdjointOfMonadicRightAdjoint`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   (R : CategoryTheor…
· 使用定理 `TopCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLimits (Ca
tegoryTheory.forget TopCat)
-/
instance forget_preservesLimits : Limits.PreservesLimits (forget Profinite) := by
  apply Limits.comp_preservesLimits Profinite.toTopCat (forget TopCat)

set_option backward.isDefEq.respectTransparency false in
/-
**Profinite.epi_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Profinite`。
形式化陈述：epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Su
rjective f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `IsClosed.compl_mem_nhds`：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx :
 x ∉ s) : sᶜ in 𝓝 x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `isTopologicalBasis_isClopen`：isTopologicalBasis_isClopen : IsTopological
Basis { s : Set X | IsClopen s }
· 使用定理 `Profinite.instTotallyDisconnectedSpaceCarrierToTop`：∀ {X : Profinite}, T
otallyDisconnectedSpace ↑X.toTop
· 使用定理 `Finite.compactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Finite 
X], CompactSpace X
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.DiscreteTopology.metrizableSpace`：∀ {X : Type u_2} [ins
t : TopologicalSpace X] [DiscreteTopology X], TopologicalSpace.MetrizableSpace X
· 使用定理 `instDiscreteTopologyFin`：∀ {n : ℕ}, DiscreteTopology (Fin n)
· 使用定理 `TotallySeparatedSpace.totallyDisconnectedSpace`：∀ (α : Type u) [inst : T
opologicalSpace α] [TotallySeparatedSpace α], TotallyDisconnectedSpace α
· 使用定理 `TotallySeparatedSpace.of_discrete`：∀ (α : Type u_3) [inst : TopologicalS
pace α] [DiscreteTopology α], TotallySeparatedSpace α
· 使用定理 `instDiscreteTopologyULift`：∀ {X : Type u} [inst : TopologicalSpace X] [D
iscreteTopology X], DiscreteTopology (ULift.{u_5, u} X)
· 使用定理 `Profinite.instHasPropTotallyDisconnectedSpaceCarrier`：∀ (X : Type u_1) [
inst : TopologicalSpace X] [TotallyDisconnectedSpace X],   CompHausLike.HasProp 
(fun Y => TotallyDisconnectedSpace ↑Y) X
· 使用定理 `LocallyConstant.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topo
logicalSpace X] [inst_1 : TopologicalSpace Y] (f : LocallyConstant X Y),   Conti
nuous ⇑f
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 52 条，此处仅展示前 30 条）
-/
theorem epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
    let U := Cᶜ
    have hyU : y ∈ U := by
      refine Set.mem_compl ?_
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    have hUy : U ∈ 𝓝 y := hC.compl_mem_nhds hyU
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
        rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, ConcreteCategory.hom_ofHom,
          ContinuousMap.coe_mk, Function.comp_apply, if_neg]
        refine mt (fun α => hVU α) ?_
        simp [U, C]
      apply_fun fun e => (e y).down at H
      dsimp [g, LocallyConstant.ofIsClopen] at H
      rw [ContinuousMap.coe_mk, ContinuousMap.coe_mk, Function.comp_apply, if_pos hyV] at H
      exact top_ne_bot H
  · rw [← CategoryTheory.ofHom_epi_iff_surjective]
    apply (forget Profinite).epi_of_epi_map

/-- The pi-type of profinite spaces is profinite. -/
/-
**Profinite.pi** 是 Mathlib 中的一个定义，位于命名空间 `Profinite`。
形式化陈述：pi {α : Type u} (β : α -> Profinite) : Profinite
参数：β : α -> Profinite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pi-type of profinite spaces is profinite.
-/
def pi {α : Type u} (β : α → Profinite) : Profinite := .of (Π (a : α), β a)

end Profinite

