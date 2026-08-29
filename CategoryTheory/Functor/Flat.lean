/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Bicones
public import Mathlib.CategoryTheory.Limits.Comma
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
/-!
# Representably flat functors

We define representably flat functors as functors such that the category of structured arrows
over `X` is cofiltered for each `X`. This concept is also known as flat functors as in [Elephant]
Remark C2.3.7, and this name is suggested by Mike Shulman in
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html to avoid
confusion with other notions of flatness (e.g. see the notion of flat type-valued
functor in the file `Mathlib/CategoryTheory/Functor/TypeValuedFlat.lean`).

This definition is equivalent to left exact functors (functors that preserves finite limits) when
`C` has all finite limits.

## Main results

* `flat_of_preservesFiniteLimits`: If `F : C ⥤ D` preserves finite limits and `C` has all finite
  limits, then `F` is flat.
* `preservesFiniteLimits_of_flat`: If `F : C ⥤ D` is flat, then it preserves all finite limits.
* `preservesFiniteLimits_iff_flat`: If `C` has all finite limits,
  then `F` is flat iff `F` is left exact.
* `lan_preservesFiniteLimits_of_flat`: If `F : C ⥤ D` is a flat functor between small categories,
  then the functor `Lan F.op` between presheaves of sets preserves all finite limits.
* `flat_iff_lan_flat`: If `C`, `D` are small and `C` has all finite limits, then `F` is flat iff
  `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)` is flat.
* `preservesFiniteLimits_iff_lanPreservesFiniteLimits`: If `C`, `D` are small and `C` has all
  finite limits, then `F` preserves finite limits iff `Lan F.op : (Cᵒᵖ ⥤ Type*) ⥤ (Dᵒᵖ ⥤ Type*)`
  does.

-/

@[expose] public section


universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory

open CategoryTheory.Limits

open Opposite

namespace CategoryTheory

section RepresentablyFlat

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]

/--
Definition of `RepresentablyFlat` / `RepresentablyFlat` 的定义

English:
class RepresentablyFlat
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - cofiltered : forall X : D, IsCofiltered (StructuredArrow X F)

中文:
类 RepresentablyFlat
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - cofiltered : 对任意 X : D, IsCofiltered (StructuredArrow X F)
-/
class RepresentablyFlat (F : C ⥤ D) : Prop where
  cofiltered : forall X : D, IsCofiltered (StructuredArrow X F)

/--
Definition of `RepresentablyCoflat` / `RepresentablyCoflat` 的定义

English:
class RepresentablyCoflat
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - filtered : forall X : D, IsFiltered (CostructuredArrow F X)

中文:
类 RepresentablyCoflat
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - filtered : 对任意 X : D, IsFiltered (CostructuredArrow F X)
-/
class RepresentablyCoflat (F : C ⥤ D) : Prop where
  filtered : forall X : D, IsFiltered (CostructuredArrow F X)

attribute [instance] RepresentablyFlat.cofiltered RepresentablyCoflat.filtered

variable (F : C ⥤ D)

/--
Instance `RepresentablyFlat.of_isRightAdjoint` / 实例 `RepresentablyFlat.of_isRightAdjoint`

English:
instance RepresentablyFlat.of_isRightAdjoint
  signature: [F.IsRightAdjoint]
  body: IsCofiltered.of_isInitial _ (mkInitialOfLeftAdjoint _ (.ofIsRightAdjoint F) _)

中文:
实例 RepresentablyFlat.of_isRightAdjoint
  签名: [F.IsRightAdjoint]
  定义体: IsCofiltered.of_isInitial _ (mkInitialOfLeftAdjoint _ (.ofIsRightAdjoint F) _)

Depends on / 依赖: IsCofiltered, IsCofiltered.of_isInitial, mkInitialOfLeftAdjoint, ofIsRightAdjoint, of_isInitial
-/
instance RepresentablyFlat.of_isRightAdjoint [F.IsRightAdjoint] : RepresentablyFlat F where
  cofiltered _ := IsCofiltered.of_isInitial _ (mkInitialOfLeftAdjoint _ (.ofIsRightAdjoint F) _)

/--
Instance `RepresentablyCoflat.of_isLeftAdjoint` / 实例 `RepresentablyCoflat.of_isLeftAdjoint`

English:
instance RepresentablyCoflat.of_isLeftAdjoint
  signature: [F.IsLeftAdjoint]
  body: IsFiltered.of_isTerminal _ (mkTerminalOfRightAdjoint _ (.ofIsLeftAdjoint F) _)

中文:
实例 RepresentablyCoflat.of_isLeftAdjoint
  签名: [F.IsLeftAdjoint]
  定义体: IsFiltered.of_isTerminal _ (mkTerminalOfRightAdjoint _ (.ofIsLeftAdjoint F) _)

Depends on / 依赖: IsFiltered, IsFiltered.of_isTerminal, mkTerminalOfRightAdjoint, ofIsLeftAdjoint, of_isTerminal
-/
instance RepresentablyCoflat.of_isLeftAdjoint [F.IsLeftAdjoint] : RepresentablyCoflat F where
  filtered _ := IsFiltered.of_isTerminal _ (mkTerminalOfRightAdjoint _ (.ofIsLeftAdjoint F) _)

/--
theorem `RepresentablyFlat.id` / 定理 `RepresentablyFlat.id`

English:
theorem RepresentablyFlat.id
  statement: RepresentablyFlat (𝟭 C)
  proof: inferInstance

中文:
定理 RepresentablyFlat.id
  结论: RepresentablyFlat (𝟭 C)
  证明: inferInstance
-/
theorem RepresentablyFlat.id : RepresentablyFlat (𝟭 C) := inferInstance

/--
theorem `RepresentablyCoflat.id` / 定理 `RepresentablyCoflat.id`

English:
theorem RepresentablyCoflat.id
  statement: RepresentablyCoflat (𝟭 C)
  proof: inferInstance

中文:
定理 RepresentablyCoflat.id
  结论: RepresentablyCoflat (𝟭 C)
  证明: inferInstance
-/
theorem RepresentablyCoflat.id : RepresentablyCoflat (𝟭 C) := inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `RepresentablyFlat.comp` / 实例 `RepresentablyFlat.comp`

English:
instance RepresentablyFlat.comp
  signature: (G : D ⥤ E) [RepresentablyFlat F]
  body: by
  refine ⟨fun X => IsCofiltered.of_cone_nonempty.{0} _ (fun {J} _ _ H => ?_)⟩
  obtain ⟨c₁⟩ := IsCofiltered.cone_nonempty (H ⋙ StructuredArrow.pre X F G)
  let H₂ : J ⥤ StructuredArrow c₁.pt.right F :=
    { obj := fun j => StructuredArrow.mk (c₁.π.app j).right
      map := fun {j j'} f =>
      

中文:
实例 RepresentablyFlat.comp
  签名: (G : D ⥤ E) [RepresentablyFlat F]
  定义体: by
  refine ⟨fun X => IsCofiltered.of_cone_nonempty.{0} _ (fun {J} _ _ H => ?_)⟩
  obtain ⟨c₁⟩ := IsCofiltered.cone_nonempty (H ⋙ StructuredArrow.pre X F G)
  let H₂ : J ⥤ StructuredArrow c₁.pt.right F :=
    { obj := fun j => StructuredArrow.mk (c₁.π.app j).right
      map := fun {j j'} f =>
      

Depends on / 依赖: CommaMorphism, CommaMorphism.right, G.map, H.map, IsCofiltered, IsCofiltered.cone_nonempty, IsCofiltered.of_cone_nonempty, Structur, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk, StructuredArrow.pre, cone_nonempty, of_cone_nonempty, pt.hom, pt.right
-/
instance RepresentablyFlat.comp (G : D ⥤ E) [RepresentablyFlat F]
    [RepresentablyFlat G] : RepresentablyFlat (F ⋙ G) := by
  refine ⟨fun X => IsCofiltered.of_cone_nonempty.{0} _ (fun {J} _ _ H => ?_)⟩
  obtain ⟨c₁⟩ := IsCofiltered.cone_nonempty (H ⋙ StructuredArrow.pre X F G)
  let H₂ : J ⥤ StructuredArrow c₁.pt.right F :=
    { obj := fun j => StructuredArrow.mk (c₁.π.app j).right
      map := fun {j j'} f =>
        StructuredArrow.homMk (H.map f).right (congrArg CommaMorphism.right (c₁.w f)) }
  obtain ⟨c₂⟩ := IsCofiltered.cone_nonempty H₂
  simp only [H₂] at c₂
  exact ⟨⟨StructuredArrow.mk (c₁.pt.hom ≫ G.map c₂.pt.hom),
    ⟨fun j => StructuredArrow.homMk (c₂.π.app j).right (by simp [← G.map_comp]),
     fun j j' f => by simpa using (c₂.w f).symm⟩⟩⟩

section

variable {F}

/--
theorem `RepresentablyFlat.of_iso` / 定理 `RepresentablyFlat.of_iso`

English:
theorem RepresentablyFlat.of_iso
  given: [RepresentablyFlat F] {G : C ⥤ D} (α : F ≅ G)
  proof: IsCofiltered.of_equivalence (StructuredArrow.mapNatIso α)

中文:
定理 RepresentablyFlat.of_iso
  条件: [RepresentablyFlat F] {G : C ⥤ D} (α : F ≅ G)
  证明: IsCofiltered.of_equivalence (StructuredArrow.mapNatIso α)

Depends on / 依赖: IsCofiltered, IsCofiltered.of_equivalence, StructuredArrow, StructuredArrow.mapNatIso, mapNatIso, of_equivalence
-/
theorem RepresentablyFlat.of_iso [RepresentablyFlat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyFlat G where
  cofiltered _ := IsCofiltered.of_equivalence (StructuredArrow.mapNatIso α)

/--
theorem `RepresentablyCoflat.of_iso` / 定理 `RepresentablyCoflat.of_iso`

English:
theorem RepresentablyCoflat.of_iso
  given: [RepresentablyCoflat F] {G : C ⥤ D} (α : F ≅ G)
  proof: IsFiltered.of_equivalence (CostructuredArrow.mapNatIso α)

中文:
定理 RepresentablyCoflat.of_iso
  条件: [RepresentablyCoflat F] {G : C ⥤ D} (α : F ≅ G)
  证明: IsFiltered.of_equivalence (CostructuredArrow.mapNatIso α)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapNatIso, IsFiltered, IsFiltered.of_equivalence, mapNatIso, of_equivalence
-/
theorem RepresentablyCoflat.of_iso [RepresentablyCoflat F] {G : C ⥤ D} (α : F ≅ G) :
    RepresentablyCoflat G where
  filtered _ := IsFiltered.of_equivalence (CostructuredArrow.mapNatIso α)

end

/--
theorem `representablyCoflat_op_iff` / 定理 `representablyCoflat_op_iff`

English:
theorem representablyCoflat_op_iff
  statement: RepresentablyCoflat F.op ↔ RepresentablyFlat F
  proof: by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsFiltered (StructuredArrow X F)ᵒᵖ from isCofiltered_of_isFiltered_op _
    apply IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _).symm
  · suffices IsCofiltered (CostructuredArrow F.op (op X))ᵒᵖ from isFiltered_

中文:
定理 representablyCoflat_op_iff
  结论: RepresentablyCoflat F.op ↔ RepresentablyFlat F
  证明: by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsFiltered (StructuredArrow X F)ᵒᵖ from isCofiltered_of_isFiltered_op _
    apply IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _).symm
  · suffices IsCofiltered (CostructuredArrow F.op (op X))ᵒᵖ from isFiltered_

Depends on / 依赖: CostructuredArrow, F.op, IsCofiltered, IsCofiltered.of_equivalence, IsFiltered, IsFiltered.of_equivalence, StructuredArrow, isCofiltered_of_isFiltered_op, isFiltered_of_isCofiltered_op, of_equivalence, opOpEquivalence, structuredArrowOpEquivalence
-/
theorem representablyCoflat_op_iff : RepresentablyCoflat F.op ↔ RepresentablyFlat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsFiltered (StructuredArrow X F)ᵒᵖ from isCofiltered_of_isFiltered_op _
    apply IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _).symm
  · suffices IsCofiltered (CostructuredArrow F.op (op X))ᵒᵖ from isFiltered_of_isCofiltered_op _
    suffices IsCofiltered (StructuredArrow X F)ᵒᵖᵒᵖ from
      IsCofiltered.of_equivalence (structuredArrowOpEquivalence _ _).op
    apply IsCofiltered.of_equivalence (opOpEquivalence _)

/--
theorem `representablyFlat_op_iff` / 定理 `representablyFlat_op_iff`

English:
theorem representablyFlat_op_iff
  statement: RepresentablyFlat F.op ↔ RepresentablyCoflat F
  proof: by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsCofiltered (CostructuredArrow F X)ᵒᵖ from isFiltered_of_isCofiltered_op _
    apply IsCofiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  · suffices IsFiltered (StructuredArrow (op X) F.op)ᵒᵖ from isCofil

中文:
定理 representablyFlat_op_iff
  结论: RepresentablyFlat F.op ↔ RepresentablyCoflat F
  证明: by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsCofiltered (CostructuredArrow F X)ᵒᵖ from isFiltered_of_isCofiltered_op _
    apply IsCofiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  · suffices IsFiltered (StructuredArrow (op X) F.op)ᵒᵖ from isCofil

Depends on / 依赖: CostructuredArrow, F.op, IsCofiltered, IsCofiltered.of_equivalence, IsFiltered, IsFiltered.of_equivalence, StructuredArrow, costructuredArrowOpEquivalence, isCofiltered_of_isFiltered_op, isFiltered_of_isCofiltered_op, of_equivalence, opOpEquivalence
-/
theorem representablyFlat_op_iff : RepresentablyFlat F.op ↔ RepresentablyCoflat F := by
  refine ⟨fun _ => ⟨fun X => ?_⟩, fun _ => ⟨fun ⟨X⟩ => ?_⟩⟩
  · suffices IsCofiltered (CostructuredArrow F X)ᵒᵖ from isFiltered_of_isCofiltered_op _
    apply IsCofiltered.of_equivalence (costructuredArrowOpEquivalence _ _).symm
  · suffices IsFiltered (StructuredArrow (op X) F.op)ᵒᵖ from isCofiltered_of_isFiltered_op _
    suffices IsFiltered (CostructuredArrow F X)ᵒᵖᵒᵖ from
      IsFiltered.of_equivalence (costructuredArrowOpEquivalence _ _).op
    apply IsFiltered.of_equivalence (opOpEquivalence _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RepresentablyFlat
  signature: F] : RepresentablyCoflat F.op
  body: (representablyCoflat_op_iff F).2 inferInstance

中文:
实例 [RepresentablyFlat
  签名: F] : RepresentablyCoflat F.op
  定义体: (representablyCoflat_op_iff F).2 inferInstance

Depends on / 依赖: representablyCoflat_op_iff
-/
instance [RepresentablyFlat F] : RepresentablyCoflat F.op :=
  (representablyCoflat_op_iff F).2 inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RepresentablyCoflat
  signature: F] : RepresentablyFlat F.op
  body: (representablyFlat_op_iff F).2 inferInstance

中文:
实例 [RepresentablyCoflat
  签名: F] : RepresentablyFlat F.op
  定义体: (representablyFlat_op_iff F).2 inferInstance

Depends on / 依赖: representablyFlat_op_iff
-/
instance [RepresentablyCoflat F] : RepresentablyFlat F.op :=
  (representablyFlat_op_iff F).2 inferInstance

/--
Instance `RepresentablyCoflat.comp` / 实例 `RepresentablyCoflat.comp`

English:
instance RepresentablyCoflat.comp
  signature: (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G]
  body: (representablyFlat_op_iff _).1 inferInstanceAs RepresentablyFlat (F.op ⋙ G.op)

中文:
实例 RepresentablyCoflat.comp
  签名: (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G]
  定义体: (representablyFlat_op_iff _).1 inferInstanceAs RepresentablyFlat (F.op ⋙ G.op)

Depends on / 依赖: F.op, G.op, RepresentablyFlat, representablyFlat_op_iff
-/
instance RepresentablyCoflat.comp (G : D ⥤ E) [RepresentablyCoflat F] [RepresentablyCoflat G] :
    RepresentablyCoflat (F ⋙ G) :=
(representablyFlat_op_iff _).1 inferInstanceAs RepresentablyFlat (F.op ⋙ G.op)

/--
lemma `final_of_representablyFlat` / 引理 `final_of_representablyFlat`

English:
lemma final_of_representablyFlat
  given: [h : RepresentablyFlat F]
  statement: F.Final where
  proof: IsCofiltered.isConnected _

中文:
引理 final_of_representablyFlat
  条件: [h : RepresentablyFlat F]
  结论: F.Final where
  证明: IsCofiltered.isConnected _

Depends on / 依赖: IsCofiltered, IsCofiltered.isConnected, isConnected
-/
lemma final_of_representablyFlat [h : RepresentablyFlat F] : F.Final where
  out _ := IsCofiltered.isConnected _

/--
lemma `initial_of_representablyCoflat` / 引理 `initial_of_representablyCoflat`

English:
lemma initial_of_representablyCoflat
  given: [h : RepresentablyCoflat F]
  statement: F.Initial where
  proof: IsFiltered.isConnected _

中文:
引理 initial_of_representablyCoflat
  条件: [h : RepresentablyCoflat F]
  结论: F.Initial where
  证明: IsFiltered.isConnected _

Depends on / 依赖: IsFiltered, IsFiltered.isConnected, isConnected
-/
lemma initial_of_representablyCoflat [h : RepresentablyCoflat F] : F.Initial where
  out _ := IsFiltered.isConnected _

end RepresentablyFlat

section HasLimit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/--
theorem `flat_of_preservesFiniteLimits` / 定理 `flat_of_preservesFiniteLimits`

English:
theorem flat_of_preservesFiniteLimits
  given: [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F]
  proof: ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      exact fun _ _ _ => HasLimitsOfShape.mk
    IsCofiltered.of_hasFiniteLimits _⟩

中文:
定理 flat_of_preservesFiniteLimits
  条件: [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F]
  证明: ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      exact fun _ _ _ => HasLimitsOfShape.mk
    IsCofiltered.of_hasFiniteLimits _⟩

Depends on / 依赖: HasFiniteLimits, HasLimitsOfShape, HasLimitsOfShape.mk, IsCofiltered, IsCofiltered.of_hasFiniteLimits, StructuredArrow, hasFiniteLimits_of_hasFiniteLimits_of_size, of_hasFiniteLimits
-/
theorem flat_of_preservesFiniteLimits [HasFiniteLimits C] (F : C ⥤ D) [PreservesFiniteLimits F] :
    RepresentablyFlat F :=
  ⟨fun X =>
    haveI : HasFiniteLimits (StructuredArrow X F) := by
      apply hasFiniteLimits_of_hasFiniteLimits_of_size.{v₁} (StructuredArrow X F)
      exact fun _ _ _ => HasLimitsOfShape.mk
    IsCofiltered.of_hasFiniteLimits _⟩

/--
theorem `coflat_of_preservesFiniteColimits` / 定理 `coflat_of_preservesFiniteColimits`

English:
theorem coflat_of_preservesFiniteColimits
  statement: [HasFiniteColimits C] (F : C ⥤ D)
  proof: let _ := preservesFiniteLimits_op F
  (representablyFlat_op_iff _).1 (flat_of_preservesFiniteLimits _)

中文:
定理 coflat_of_preservesFiniteColimits
  结论: [HasFiniteColimits C] (F : C ⥤ D)
  证明: let _ := preservesFiniteLimits_op F
  (representablyFlat_op_iff _).1 (flat_of_preservesFiniteLimits _)

Depends on / 依赖: flat_of_preservesFiniteLimits, preservesFiniteLimits_op, representablyFlat_op_iff
-/
theorem coflat_of_preservesFiniteColimits [HasFiniteColimits C] (F : C ⥤ D)
    [PreservesFiniteColimits F] : RepresentablyCoflat F :=
  let _ := preservesFiniteLimits_op F
  (representablyFlat_op_iff _).1 (flat_of_preservesFiniteLimits _)

namespace PreservesFiniteLimitsOfFlat

open StructuredArrow

variable {J : Type v₁} [SmallCategory J] [FinCategory J] {K : J ⥤ C}
variable (F : C ⥤ D) [RepresentablyFlat F] {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : s.pt ⟶ F.obj c.pt
  body: let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
hc.lift
        (Cone.postcompose
              ({ app := fun _ => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F)

中文:
定义 lift
  签名: : s.pt ⟶ F.obj c.pt
  定义体: let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
hc.lift
        (Cone.postcompose
              ({ app := fun _ => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F)

Depends on / 依赖: Cone.postcompose, F.map, IsCofiltered, IsCofiltered.cone, StructuredArrow, StructuredArrow.pre, StructuredArrow.proj, hc.lift, mapCone, postcompose, pt.hom, s.pt, s.toStructuredArrow, toStructuredArrow
-/
noncomputable def lift : s.pt ⟶ F.obj c.pt :=
  let s' := IsCofiltered.cone (s.toStructuredArrow ⋙ StructuredArrow.pre _ K F)
  s'.pt.hom ≫
    (F.map <|
hc.lift
        (Cone.postcompose
              ({ app := fun _ => 𝟙 _ } :
                (s.toStructuredArrow ⋙ pre s.pt K F) ⋙ proj s.pt F ⟶ K)).obj <|
          (StructuredArrow.proj s.pt F).mapCone s')

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `fac` / 定理 `fac`

English:
theorem fac
  given: (x : J)
  statement: lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x
  proof: by
  simp [lift, ← Functor.map_comp]

中文:
定理 fac
  条件: (x : J)
  结论: lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x
  证明: by
  simp [lift, ← Functor.map_comp]

Depends on / 依赖: Functor, Functor.map_comp, map_comp
-/
theorem fac (x : J) : lift F hc s ≫ (F.mapCone c).π.app x = s.π.app x := by
  simp [lift, ← Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `uniq` / 定理 `uniq`

English:
theorem uniq
  statement: {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
  proof: by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁]) }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eq

中文:
定理 uniq
  结论: {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
  证明: by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁]) }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eq
-/
theorem uniq {K : J ⥤ C} {c : Cone K} (hc : IsLimit c) (s : Cone (K ⋙ F))
    (f₁ f₂ : s.pt ⟶ F.obj c.pt) (h₁ : forall j : J, f₁ ≫ (F.mapCone c).π.app j = s.π.app j)
    (h₂ : forall j : J, f₂ ≫ (F.mapCone c).π.app j = s.π.app j) : f₁ = f₂ := by
  -- We can make two cones over the diagram of `s` via `f₁` and `f₂`.
  let α₁ : (F.mapCone c).toStructuredArrow ⋙ map f₁ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₁]) }
  let α₂ : (F.mapCone c).toStructuredArrow ⋙ map f₂ ⟶ s.toStructuredArrow :=
    { app := fun X => eqToHom (by simp [← h₂]) }
  let c₁ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cone.postcompose (Functor.whiskerRight α₁ (pre s.pt K F) :)).obj
      (c.toStructuredArrowCone F f₁)
  let c₂ : Cone (s.toStructuredArrow ⋙ pre s.pt K F) :=
    (Cone.postcompose (Functor.whiskerRight α₂ (pre s.pt K F) :)).obj
      (c.toStructuredArrowCone F f₂)
  -- The two cones can then be combined and we may obtain a cone over the two cones since
  -- `StructuredArrow s.pt F` is cofiltered.
  let c₀ := IsCofiltered.cone (biconeMk _ c₁ c₂)
  let g₁ : c₀.pt ⟶ c₁.pt := c₀.π.app Bicone.left
  let g₂ : c₀.pt ⟶ c₂.pt := c₀.π.app Bicone.right
  -- Then `g₁.right` and `g₂.right` are two maps from the same cone into the `c`.
  have : forall j : J, g₁.right ≫ c.π.app j = g₂.right ≫ c.π.app j := by
    intro j
    injection c₀.π.naturality (BiconeHom.left j) with _ e₁
    injection c₀.π.naturality (BiconeHom.right j) with _ e₂
    convert! e₁.symm.trans e₂ <;> simp [c₁, c₂]
  have : c.extend g₁.right = c.extend g₂.right := by
    unfold Cone.extend
    congr 1
    ext x
    apply this
  -- And thus they are equal as `c` is the limit.
  have : g₁.right = g₂.right := calc
    g₁.right = hc.lift (c.extend g₁.right) := by
      apply hc.uniq (c.extend _)
      simp
    _ = hc.lift (c.extend g₂.right) := by
      congr
    _ = g₂.right := by
      symm
      apply hc.uniq (c.extend _)
      simp
  -- Finally, since `fᵢ` factors through `F(gᵢ)`, the result follows.
  calc
    f₁ = c₀.pt.hom ≫ F.map g₁.right := g₁.w.symm
    _ = c₀.pt.hom ≫ F.map g₂.right := by rw [this]
    _ = f₂ := g₂.w

end PreservesFiniteLimitsOfFlat

/--
lemma `preservesFiniteLimits_of_flat` / 引理 `preservesFiniteLimits_of_flat`

English:
lemma preservesFiniteLimits_of_flat
  given: (F : C ⥤ D) [RepresentablyFlat F]
  proof: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  constructor
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply Prese

中文:
引理 preservesFiniteLimits_of_flat
  条件: (F : C ⥤ D) [RepresentablyFlat F]
  证明: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  constructor
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply Prese

Depends on / 依赖: PreservesFiniteLimitsOfFlat, PreservesFiniteLimitsOfFlat.fac, PreservesFiniteLimitsOfFlat.lift, PreservesFiniteLimitsOfFlat.uniq, preservesFiniteLimits_of_preservesFiniteLimitsOfSize
-/
lemma preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits F := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  intro J _ _; constructor
  intro K; constructor
  intro c hc
  constructor
  exact
    { lift := PreservesFiniteLimitsOfFlat.lift F hc
      fac := PreservesFiniteLimitsOfFlat.fac F hc
      uniq := fun s m h => by
        apply PreservesFiniteLimitsOfFlat.uniq F hc
        · exact h
        · exact PreservesFiniteLimitsOfFlat.fac F hc s }

/--
lemma `preservesFiniteColimits_of_coflat` / 引理 `preservesFiniteColimits_of_coflat`

English:
lemma preservesFiniteColimits_of_coflat
  given: (F : C ⥤ D) [RepresentablyCoflat F]
  proof: letI _ := preservesFiniteLimits_of_flat F.op
  preservesFiniteColimits_of_op _

中文:
引理 preservesFiniteColimits_of_coflat
  条件: (F : C ⥤ D) [RepresentablyCoflat F]
  证明: letI _ := preservesFiniteLimits_of_flat F.op
  preservesFiniteColimits_of_op _

Depends on / 依赖: F.op, preservesFiniteColimits_of_op, preservesFiniteLimits_of_flat
-/
lemma preservesFiniteColimits_of_coflat (F : C ⥤ D) [RepresentablyCoflat F] :
    PreservesFiniteColimits F :=
  letI _ := preservesFiniteLimits_of_flat F.op
  preservesFiniteColimits_of_op _

/--
lemma `preservesFiniteLimits_iff_flat` / 引理 `preservesFiniteLimits_iff_flat`

English:
lemma preservesFiniteLimits_iff_flat
  given: [HasFiniteLimits C] (F : C ⥤ D)
  proof: ⟨fun _ => preservesFiniteLimits_of_flat F, fun _ => flat_of_preservesFiniteLimits F⟩

中文:
引理 preservesFiniteLimits_iff_flat
  条件: [HasFiniteLimits C] (F : C ⥤ D)
  证明: ⟨fun _ => preservesFiniteLimits_of_flat F, fun _ => flat_of_preservesFiniteLimits F⟩

Depends on / 依赖: flat_of_preservesFiniteLimits, preservesFiniteLimits_of_flat
-/
lemma preservesFiniteLimits_iff_flat [HasFiniteLimits C] (F : C ⥤ D) :
    RepresentablyFlat F ↔ PreservesFiniteLimits F :=
  ⟨fun _ => preservesFiniteLimits_of_flat F, fun _ => flat_of_preservesFiniteLimits F⟩

/--
lemma `preservesFiniteColimits_iff_coflat` / 引理 `preservesFiniteColimits_iff_coflat`

English:
lemma preservesFiniteColimits_iff_coflat
  given: [HasFiniteColimits C] (F : C ⥤ D)
  proof: ⟨fun _ => preservesFiniteColimits_of_coflat F, fun _ => coflat_of_preservesFiniteColimits F⟩

中文:
引理 preservesFiniteColimits_iff_coflat
  条件: [HasFiniteColimits C] (F : C ⥤ D)
  证明: ⟨fun _ => preservesFiniteColimits_of_coflat F, fun _ => coflat_of_preservesFiniteColimits F⟩

Depends on / 依赖: coflat_of_preservesFiniteColimits, preservesFiniteColimits_of_coflat
-/
lemma preservesFiniteColimits_iff_coflat [HasFiniteColimits C] (F : C ⥤ D) :
    RepresentablyCoflat F ↔ PreservesFiniteColimits F :=
  ⟨fun _ => preservesFiniteColimits_of_coflat F, fun _ => coflat_of_preservesFiniteColimits F⟩

end HasLimit

section SmallCategory

variable {C D : Type u₁} [SmallCategory C] [SmallCategory D] (E : Type u₂) [Category.{u₁} E]


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `lanEvaluationIsoColim` / `lanEvaluationIsoColim` 的定义

English:
definition lanEvaluationIsoColim
  signature: (F : C ⥤ D) (X : D)
  body: NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ :=

中文:
定义 lanEvaluationIsoColim
  签名: (F : C ⥤ D) (X : D)
  定义体: NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ :=

Depends on / 依赖: F.lanUnit.naturality, Functor, Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUpToIso_hom, NatIso, NatIso.ofComponents, T.left, coconePointUniqueUpToIso, colimit, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, congr_app, hom_ext, isColimit, isPointwiseLeftKanExtensionLeftKanExtensionUnit, lanUnit, naturality, ofComponents
-/
noncomputable def lanEvaluationIsoColim (F : C ⥤ D) (X : D)
    [forall X : D, HasColimitsOfShape (CostructuredArrow F X) E] :
    F.lan ⋙ (evaluation D E).obj X ≅
      (Functor.whiskeringLeft _ _ E).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ := fun (G : C ⥤ E) => IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁]; rw [NatTrans.naturality_assoc]; rw [← reassoc_of% h₂]; rw [h₁]; rw [ι_colimMap]; rw [Functor.whiskerLeft_app]
      rfl)

variable {FE : E -> E -> Type*} {CE : E -> Type u₁} [forall X Y, FunLike (FE X Y) (CE X) (CE Y)]
    [ConcreteCategory E FE] [HasLimits E] [HasColimits E]
variable [ReflectsLimits (forget E)] [PreservesFilteredColimits (forget E)]
variable [PreservesLimits (forget E)]

/--
Instance `lan_preservesFiniteLimits_of_flat` / 实例 `lan_preservesFiniteLimits_of_flat`

English:
instance lan_preservesFiniteLimits_of_flat
  signature: (F : C ⥤ D) [RepresentablyFlat F]
  body: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exa

中文:
实例 lan_preservesFiniteLimits_of_flat
  签名: (F : C ⥤ D) [RepresentablyFlat F]
  定义体: by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exa

Depends on / 依赖: CostructuredArrow, F.op, F.op.lan, IsFiltered, IsFiltered.of_equivalence, lanEvaluationIsoColim, of_equivalence, preservesFiniteLimits_of_preservesFiniteLimitsOfSize, preservesLimitsOfShape_of_evaluation, preservesLimitsOfShape_of_natIso, structuredArrowOpEquivalence
-/
noncomputable instance lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ E) ⥤ Dᵒᵖ ⥤ E) J
  intro K
  have : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop K))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim _ _ _).symm

/--
Instance `lan_flat_of_flat` / 实例 `lan_flat_of_flat`

English:
instance lan_flat_of_flat
  signature: (F : C ⥤ D) [RepresentablyFlat F]
  body: flat_of_preservesFiniteLimits _

中文:
实例 lan_flat_of_flat
  签名: (F : C ⥤ D) [RepresentablyFlat F]
  定义体: flat_of_preservesFiniteLimits _

Depends on / 依赖: flat_of_preservesFiniteLimits
-/
instance lan_flat_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) :=
  flat_of_preservesFiniteLimits _

variable [HasFiniteLimits C]

/--
Instance `lan_preservesFiniteLimits_of_preservesFiniteLimits` / 实例 `lan_preservesFiniteLimits_of_preservesFiniteLimits`

English:
instance lan_preservesFiniteLimits_of_preservesFiniteLimits
  signature: (F : C ⥤ D)
  body: by
  have := flat_of_preservesFiniteLimits F
  infer_instance

中文:
实例 lan_preservesFiniteLimits_of_preservesFiniteLimits
  签名: (F : C ⥤ D)
  定义体: by
  have := flat_of_preservesFiniteLimits F
  infer_instance

Depends on / 依赖: flat_of_preservesFiniteLimits, infer_instance
-/
instance lan_preservesFiniteLimits_of_preservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] : PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ E) := by
  have := flat_of_preservesFiniteLimits F
  infer_instance

/--
theorem `flat_iff_lan_flat` / 定理 `flat_iff_lan_flat`

English:
theorem flat_iff_lan_flat
  given: (F : C ⥤ D)
  proof: ⟨fun _ => inferInstance, fun H => by
    have := preservesFiniteLimits_of_flat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    have : PreservesFiniteLimits F := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
      intros; apply preservesLimit_of_lan_preservesLimit
    apply flat_of_pres

中文:
定理 flat_iff_lan_flat
  条件: (F : C ⥤ D)
  证明: ⟨fun _ => inferInstance, fun H => by
    have := preservesFiniteLimits_of_flat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    have : PreservesFiniteLimits F := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
      intros; apply preservesLimit_of_lan_preservesLimit
    apply flat_of_pres

Depends on / 依赖: F.op.lan, PreservesFiniteLimits, flat_of_preservesFiniteLimits, intros, preservesFiniteLimits_of_flat, preservesFiniteLimits_of_preservesFiniteLimitsOfSize, preservesLimit_of_lan_preservesLimit
-/
theorem flat_iff_lan_flat (F : C ⥤ D) :
    RepresentablyFlat F ↔ RepresentablyFlat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun _ => inferInstance, fun H => by
    have := preservesFiniteLimits_of_flat (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁)
    have : PreservesFiniteLimits F := by
      apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁}
      intros; apply preservesLimit_of_lan_preservesLimit
    apply flat_of_preservesFiniteLimits⟩

/--
lemma `preservesFiniteLimits_iff_lan_preservesFiniteLimits` / 引理 `preservesFiniteLimits_iff_lan_preservesFiniteLimits`

English:
lemma preservesFiniteLimits_iff_lan_preservesFiniteLimits
  given: (F : C ⥤ D)
  proof: ⟨fun _ => inferInstance,
    fun _ => preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁} _
      (fun _ _ _ => preservesLimit_of_lan_preservesLimit _ _)⟩

中文:
引理 preservesFiniteLimits_iff_lan_preservesFiniteLimits
  条件: (F : C ⥤ D)
  证明: ⟨fun _ => inferInstance,
    fun _ => preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁} _
      (fun _ _ _ => preservesLimit_of_lan_preservesLimit _ _)⟩

Depends on / 依赖: preservesFiniteLimits_of_preservesFiniteLimitsOfSize, preservesLimit_of_lan_preservesLimit
-/
lemma preservesFiniteLimits_iff_lan_preservesFiniteLimits (F : C ⥤ D) :
    PreservesFiniteLimits F ↔ PreservesFiniteLimits (F.op.lan : _ ⥤ Dᵒᵖ ⥤ Type u₁) :=
  ⟨fun _ => inferInstance,
    fun _ => preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u₁} _
      (fun _ _ _ => preservesLimit_of_lan_preservesLimit _ _)⟩

end SmallCategory

section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)

attribute [local instance] IsCofiltered.isConnected IsFiltered.isConnected

instance (X : E) [RepresentablyFlat F] : (StructuredArrow.pre X F G).Final :=
  ⟨fun _ => isConnected_of_equivalent (StructuredArrow.preEquivalence _ _).symm⟩

instance (X : E) [RepresentablyCoflat F] : (CostructuredArrow.pre F G X).Initial :=
  ⟨fun _ => isConnected_of_equivalent (CostructuredArrow.preEquivalence _ _).symm⟩

set_option backward.isDefEq.respectTransparency false in
instance (X : E) [RepresentablyFlat F] [IsCofiltered (StructuredArrow X G)] :
    IsCofiltered (StructuredArrow X (F ⋙ G)) := by
  let T := StructuredArrow.pre X F G
  obtain ⟨Y⟩ := IsCofiltered.nonempty (C := StructuredArrow X G)
  obtain ⟨A⟩ := IsCofiltered.nonempty (C := StructuredArrow Y.right F)
  have : Nonempty (StructuredArrow X (F ⋙ G)) := ⟨.mk (Y.hom ≫ G.map A.hom)⟩
  suffices IsCofilteredOrEmpty (StructuredArrow X (F ⋙ G)) by constructor
  refine ⟨fun A B => ?_, fun A B f g => ?_⟩
  · let U := IsCofiltered.min (T.obj A) (T.obj B)
    let A' : StructuredArrow U.right F := .mk (IsCofiltered.minToLeft (T.obj A) (T.obj B)).right
    let B' : StructuredArrow U.right F := .mk (IsCofiltered.minToRight (T.obj A) (T.obj B)).right
refine ⟨.mk U.hom ≫ G.map (IsCofiltered.min A' B').hom,
      StructuredArrow.homMk (IsCofiltered.minToLeft A' B').right ?_,
      StructuredArrow.homMk (IsCofiltered.minToRight A' B').right ?_, trivial⟩
    · simp [← Functor.map_comp, A', T]
    · simp [← Functor.map_comp, B', T]
  · let U := IsCofiltered.eq (T.map f) (T.map g)
    let A' : StructuredArrow _ F := .mk (IsCofiltered.eqHom (T.map f) (T.map g)).right
    let B' : StructuredArrow _ F := .mk (IsCofiltered.eqHom (T.map f) (T.map g) ≫ T.map f).right
    let f' : A' ⟶ B' := StructuredArrow.homMk f.right rfl
    let g' : A' ⟶ B' := StructuredArrow.homMk g.right
      congr($(IsCofiltered.eq_condition (T.map f) (T.map g)).right).symm
refine ⟨.mk U.hom ≫ G.map (IsCofiltered.eq f' g').hom,
      StructuredArrow.homMk (IsCofiltered.eqHom f' g').right ?_, ?_⟩
    · simp [← Functor.map_comp, A', T]
    · ext
      exact congr($(IsCofiltered.eq_condition f' g').right)

instance (X : E) [RepresentablyCoflat F] [h : IsFiltered (CostructuredArrow G X)] :
    IsFiltered (CostructuredArrow (F ⋙ G) X) := by
  rw [← isCofiltered_op_iff_isFiltered]; rw [IsCofiltered.iff_of_equivalence
    (costructuredArrowOpEquivalence _ _)] at h ⊢
exact inferInstanceAs IsCofiltered (StructuredArrow (op X) (F.op ⋙ G.op))

instance (G : D ⥤ Type*) [RepresentablyFlat F] [IsCofiltered G.Elements] :
    IsCofiltered (F ⋙ G).Elements := by
  suffices h : IsCofiltered (StructuredArrow PUnit (F ⋙ G)) from
    .of_equivalence (CategoryOfElements.structuredArrowEquivalence _).symm
  have : IsCofiltered (StructuredArrow PUnit G) :=
    .of_equivalence (CategoryOfElements.structuredArrowEquivalence _)
  infer_instance

end

end CategoryTheory
