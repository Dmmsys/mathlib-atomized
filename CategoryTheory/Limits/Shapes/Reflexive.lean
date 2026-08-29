/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-!
# Reflexive coequalizers

This file deals with reflexive pairs, which are pairs of morphisms with a common section.

A reflexive coequalizer is a coequalizer of such a pair. These kind of coequalizers often enjoy
nicer properties than general coequalizers, and feature heavily in some versions of the monadicity
theorem.

We also give some examples of reflexive pairs: for an adjunction `F ⊣ G` with counit `ε`, the pair
`(FGε_B, ε_FGB)` is reflexive. If a pair `f,g` is a kernel pair for some morphism, then it is
reflexive.

## Main definitions

* `IsReflexivePair` is the predicate that f and g have a common section.
* `WalkingReflexivePair` is the diagram indexing pairs with a common section.
* A `reflexiveCofork` is a cocone on a diagram indexed by `WalkingReflexivePair`.
* `WalkingReflexivePair.inclusionWalkingReflexivePair` is the inclusion functor from
  `WalkingParallelPair` to `WalkingReflexivePair`. It acts on reflexive pairs as forgetting
  the common section.
* `HasReflexiveCoequalizers` is the predicate that a category has all colimits of reflexive pairs.
* `reflexiveCoequalizerIsoCoequalizer`: an isomorphism promoting the coequalizer of a reflexive pair
  to the colimit of a diagram out of the walking reflexive pair.

## Main statements

* `IsKernelPair.isReflexivePair`: A kernel pair is a reflexive pair
* `WalkingParallelPair.inclusionWalkingReflexivePair_final`: The inclusion functor is final.
* `hasReflexiveCoequalizers_iff`: A category has coequalizers of reflexive pairs if and only if it
  has all colimits of shape `WalkingReflexivePair`.

## TODO
* If `C` has binary coproducts and reflexive coequalizers, then it has all coequalizers.
* If `T` is a monad on cocomplete category `C`, then `Algebra T` is cocomplete iff it has reflexive
  coequalizers.
* If `C` is locally Cartesian closed and has reflexive coequalizers, then it has images: in fact
  regular epi (and hence strong epi) images.
* Bundle the reflexive pairs of kernel pairs and of adjunction as functors out of the walking
  reflexive pair.
-/

@[expose] public section


namespace CategoryTheory

universe v v₂ u u₂

variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {A B : C} {f g : A ⟶ B}

/--
Definition of `IsReflexivePair` / `IsReflexivePair` 的定义

English:
class IsReflexivePair
  parameters: (f g : A ⟶ B)
  axioms and operations (1):
    - common_section' : exists s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B

中文:
类 是ReflexivePair
  参数: (f g : A ⟶ B)
  公理与运算 (1 个):
    - common_section' : 存在 s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B
-/
class IsReflexivePair (f g : A ⟶ B) : Prop where
  common_section' : exists s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B

/--
theorem `IsReflexivePair.common_section` / 定理 `IsReflexivePair.common_section`

English:
theorem IsReflexivePair.common_section
  given: (f g : A ⟶ B) [IsReflexivePair f g]
  proof: IsReflexivePair.common_section'

中文:
定理 是ReflexivePair.common_section
  条件: (f g : A ⟶ B) [是ReflexivePair f g]
  证明: IsReflexivePair.common_section'

Depends on / 依赖: IsReflexivePair, IsReflexivePair.common_section, common_section
-/
theorem IsReflexivePair.common_section (f g : A ⟶ B) [IsReflexivePair f g] :
    exists s : B ⟶ A, s ≫ f = 𝟙 B ∧ s ≫ g = 𝟙 B := IsReflexivePair.common_section'

/--
Definition of `IsCoreflexivePair` / `IsCoreflexivePair` 的定义

English:
class IsCoreflexivePair
  parameters: (f g : A ⟶ B)
  axioms and operations (1):
    - common_retraction' : exists s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A

中文:
类 是余reflexivePair
  参数: (f g : A ⟶ B)
  公理与运算 (1 个):
    - common_retraction' : 存在 s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A
-/
class IsCoreflexivePair (f g : A ⟶ B) : Prop where
  common_retraction' : exists s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A

/--
theorem `IsCoreflexivePair.common_retraction` / 定理 `IsCoreflexivePair.common_retraction`

English:
theorem IsCoreflexivePair.common_retraction
  given: (f g : A ⟶ B) [IsCoreflexivePair f g]
  proof: IsCoreflexivePair.common_retraction'

中文:
定理 是余reflexivePair.common_retraction
  条件: (f g : A ⟶ B) [是余reflexivePair f g]
  证明: IsCoreflexivePair.common_retraction'

Depends on / 依赖: IsCoreflexivePair, IsCoreflexivePair.common_retraction, common_retraction
-/
theorem IsCoreflexivePair.common_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    exists s : B ⟶ A, f ≫ s = 𝟙 A ∧ g ≫ s = 𝟙 A := IsCoreflexivePair.common_retraction'

/--
theorem `IsReflexivePair.mk'` / 定理 `IsReflexivePair.mk'`

English:
theorem IsReflexivePair.mk'
  given: (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B)
  proof: ⟨⟨s, sf, sg⟩⟩

中文:
定理 是ReflexivePair.mk'
  条件: (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B)
  证明: ⟨⟨s, sf, sg⟩⟩
-/
theorem IsReflexivePair.mk' (s : B ⟶ A) (sf : s ≫ f = 𝟙 B) (sg : s ≫ g = 𝟙 B) :
    IsReflexivePair f g :=
  ⟨⟨s, sf, sg⟩⟩

/--
theorem `IsCoreflexivePair.mk'` / 定理 `IsCoreflexivePair.mk'`

English:
theorem IsCoreflexivePair.mk'
  given: (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A)
  proof: ⟨⟨s, fs, gs⟩⟩

中文:
定理 是余reflexivePair.mk'
  条件: (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A)
  证明: ⟨⟨s, fs, gs⟩⟩
-/
theorem IsCoreflexivePair.mk' (s : B ⟶ A) (fs : f ≫ s = 𝟙 A) (gs : g ≫ s = 𝟙 A) :
    IsCoreflexivePair f g :=
  ⟨⟨s, fs, gs⟩⟩

/--
Definition of `commonSection` / `commonSection` 的定义

English:
definition commonSection
  signature: (f g : A ⟶ B) [IsReflexivePair f g]
  body: (IsReflexivePair.common_section f g).choose

@[reassoc (attr := simp)]

中文:
定义 commonSection
  签名: (f g : A ⟶ B) [是ReflexivePair f g]
  定义体: (IsReflexivePair.common_section f g).choose

@[reassoc (attr := simp)]

Depends on / 依赖: IsReflexivePair, IsReflexivePair.common_section, common_section
-/
noncomputable def commonSection (f g : A ⟶ B) [IsReflexivePair f g] : B ⟶ A :=
  (IsReflexivePair.common_section f g).choose

@[reassoc (attr := simp)]
/--
theorem `section_comp_left` / 定理 `section_comp_left`

English:
theorem section_comp_left
  given: (f g : A ⟶ B) [IsReflexivePair f g]
  statement: commonSection f g ≫ f = 𝟙 B
  proof: (IsReflexivePair.common_section f g).choose_spec.1

@[reassoc (attr := simp)]

中文:
定理 section_comp_left
  条件: (f g : A ⟶ B) [是ReflexivePair f g]
  结论: commonSection f g ≫ f = 𝟙 B
  证明: (IsReflexivePair.common_section f g).choose_spec.1

@[reassoc (attr := simp)]

Depends on / 依赖: IsReflexivePair, IsReflexivePair.common_section, choose_spec, common_section
-/
theorem section_comp_left (f g : A ⟶ B) [IsReflexivePair f g] : commonSection f g ≫ f = 𝟙 B :=
  (IsReflexivePair.common_section f g).choose_spec.1

@[reassoc (attr := simp)]
/--
theorem `section_comp_right` / 定理 `section_comp_right`

English:
theorem section_comp_right
  given: (f g : A ⟶ B) [IsReflexivePair f g]
  statement: commonSection f g ≫ g = 𝟙 B
  proof: (IsReflexivePair.common_section f g).choose_spec.2

中文:
定理 section_comp_right
  条件: (f g : A ⟶ B) [是ReflexivePair f g]
  结论: commonSection f g ≫ g = 𝟙 B
  证明: (IsReflexivePair.common_section f g).choose_spec.2

Depends on / 依赖: IsReflexivePair, IsReflexivePair.common_section, choose_spec, common_section
-/
theorem section_comp_right (f g : A ⟶ B) [IsReflexivePair f g] : commonSection f g ≫ g = 𝟙 B :=
  (IsReflexivePair.common_section f g).choose_spec.2

/--
Definition of `commonRetraction` / `commonRetraction` 的定义

English:
definition commonRetraction
  signature: (f g : A ⟶ B) [IsCoreflexivePair f g]
  body: (IsCoreflexivePair.common_retraction f g).choose

@[reassoc (attr := simp)]

中文:
定义 commonRetraction
  签名: (f g : A ⟶ B) [是余reflexivePair f g]
  定义体: (IsCoreflexivePair.common_retraction f g).choose

@[reassoc (attr := simp)]

Depends on / 依赖: IsCoreflexivePair, IsCoreflexivePair.common_retraction, common_retraction
-/
noncomputable def commonRetraction (f g : A ⟶ B) [IsCoreflexivePair f g] : B ⟶ A :=
  (IsCoreflexivePair.common_retraction f g).choose

@[reassoc (attr := simp)]
/--
theorem `left_comp_retraction` / 定理 `left_comp_retraction`

English:
theorem left_comp_retraction
  given: (f g : A ⟶ B) [IsCoreflexivePair f g]
  proof: (IsCoreflexivePair.common_retraction f g).choose_spec.1

@[reassoc (attr := simp)]

中文:
定理 left_comp_retraction
  条件: (f g : A ⟶ B) [是余reflexivePair f g]
  证明: (IsCoreflexivePair.common_retraction f g).choose_spec.1

@[reassoc (attr := simp)]

Depends on / 依赖: IsCoreflexivePair, IsCoreflexivePair.common_retraction, choose_spec, common_retraction
-/
theorem left_comp_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    f ≫ commonRetraction f g = 𝟙 A :=
  (IsCoreflexivePair.common_retraction f g).choose_spec.1

@[reassoc (attr := simp)]
/--
theorem `right_comp_retraction` / 定理 `right_comp_retraction`

English:
theorem right_comp_retraction
  given: (f g : A ⟶ B) [IsCoreflexivePair f g]
  proof: (IsCoreflexivePair.common_retraction f g).choose_spec.2

中文:
定理 right_comp_retraction
  条件: (f g : A ⟶ B) [是余reflexivePair f g]
  证明: (IsCoreflexivePair.common_retraction f g).choose_spec.2

Depends on / 依赖: IsCoreflexivePair, IsCoreflexivePair.common_retraction, choose_spec, common_retraction
-/
theorem right_comp_retraction (f g : A ⟶ B) [IsCoreflexivePair f g] :
    g ≫ commonRetraction f g = 𝟙 A :=
  (IsCoreflexivePair.common_retraction f g).choose_spec.2

/--
theorem `IsKernelPair.isReflexivePair` / 定理 `IsKernelPair.isReflexivePair`

English:
theorem IsKernelPair.isReflexivePair
  given: {R : C} {f g : R ⟶ A} {q : A ⟶ B} (h : IsKernelPair q f g)
  proof: IsReflexivePair.mk' _ (h.lift' _ _ rfl).2.1 (h.lift' _ _ _).2.2

中文:
定理 IsKernelPair.isReflexivePair
  条件: {R : C} {f g : R ⟶ A} {q : A ⟶ B} (h : IsKernelPair q f g)
  证明: IsReflexivePair.mk' _ (h.lift' _ _ rfl).2.1 (h.lift' _ _ _).2.2

Depends on / 依赖: IsReflexivePair, IsReflexivePair.mk, h.lift
-/
theorem IsKernelPair.isReflexivePair {R : C} {f g : R ⟶ A} {q : A ⟶ B} (h : IsKernelPair q f g) :
    IsReflexivePair f g :=
  IsReflexivePair.mk' _ (h.lift' _ _ rfl).2.1 (h.lift' _ _ _).2.2

-- This shouldn't be an instance as it would instantly loop.
/--
theorem `IsReflexivePair.swap` / 定理 `IsReflexivePair.swap`

English:
theorem IsReflexivePair.swap
  given: [IsReflexivePair f g]
  statement: IsReflexivePair g f
  proof: IsReflexivePair.mk' _ (section_comp_right f g) (section_comp_left f g)

中文:
定理 是ReflexivePair.swap
  条件: [是ReflexivePair f g]
  结论: 是ReflexivePair g f
  证明: IsReflexivePair.mk' _ (section_comp_right f g) (section_comp_left f g)

Depends on / 依赖: IsReflexivePair, IsReflexivePair.mk, section_comp_left, section_comp_right
-/
theorem IsReflexivePair.swap [IsReflexivePair f g] : IsReflexivePair g f :=
  IsReflexivePair.mk' _ (section_comp_right f g) (section_comp_left f g)

-- This shouldn't be an instance as it would instantly loop.
/--
theorem `IsCoreflexivePair.swap` / 定理 `IsCoreflexivePair.swap`

English:
theorem IsCoreflexivePair.swap
  given: [IsCoreflexivePair f g]
  statement: IsCoreflexivePair g f
  proof: IsCoreflexivePair.mk' _ (right_comp_retraction f g) (left_comp_retraction f g)

中文:
定理 是余reflexivePair.swap
  条件: [是余reflexivePair f g]
  结论: 是余reflexivePair g f
  证明: IsCoreflexivePair.mk' _ (right_comp_retraction f g) (left_comp_retraction f g)

Depends on / 依赖: IsCoreflexivePair, IsCoreflexivePair.mk, left_comp_retraction, right_comp_retraction
-/
theorem IsCoreflexivePair.swap [IsCoreflexivePair f g] : IsCoreflexivePair g f :=
  IsCoreflexivePair.mk' _ (right_comp_retraction f g) (left_comp_retraction f g)

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- For an adjunction `F ⊣ G` with counit `ε`, the pair `(FGε_B, ε_FGB)` is reflexive. -/
instance (B : D) :
    IsReflexivePair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B))) :=
  IsReflexivePair.mk' (F.map (adj.unit.app (G.obj B)))
    (by
      rw [← F.map_comp]; rw [adj.right_triangle_components]
      apply F.map_id)
    (adj.left_triangle_components _)

namespace Limits

variable (C)

/--
Definition of `HasReflexiveCoequalizers` / `HasReflexiveCoequalizers` 的定义

English:
class HasReflexiveCoequalizers
  parameters: : Prop where
  axioms and operations (1):
    - has_coeq : forall ⦃A B : C⦄ (f g : A ⟶ B) [IsReflexivePair f g], HasCoequalizer f g

中文:
类 有ReflexiveCoequalizers
  参数: : 命题 where
  公理与运算 (1 个):
    - has_coeq : 对任意 ⦃A B : C⦄ (f g : A ⟶ B) [是ReflexivePair f g], HasCoequalizer f g
-/
class HasReflexiveCoequalizers : Prop where
  has_coeq : forall ⦃A B : C⦄ (f g : A ⟶ B) [IsReflexivePair f g], HasCoequalizer f g

/--
Definition of `HasCoreflexiveEqualizers` / `HasCoreflexiveEqualizers` 的定义

English:
class HasCoreflexiveEqualizers
  parameters: : Prop where
  axioms and operations (1):
    - has_eq : forall ⦃A B : C⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], HasEqualizer f g

中文:
类 有余reflexiveEqualizers
  参数: : 命题 where
  公理与运算 (1 个):
    - has_eq : 对任意 ⦃A B : C⦄ (f g : A ⟶ B) [是余reflexivePair f g], HasEqualizer f g
-/
class HasCoreflexiveEqualizers : Prop where
  has_eq : forall ⦃A B : C⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], HasEqualizer f g

attribute [instance 1] HasReflexiveCoequalizers.has_coeq

attribute [instance 1] HasCoreflexiveEqualizers.has_eq

/--
theorem `hasCoequalizer_of_common_section` / 定理 `hasCoequalizer_of_common_section`

English:
theorem hasCoequalizer_of_common_section
  statement: [HasReflexiveCoequalizers C] {A B : C} {f g : A ⟶ B}
  proof: by
  let := IsReflexivePair.mk' r rf rg
  infer_instance

中文:
定理 hasCoequalizer_of_common_section
  结论: [有ReflexiveCoequalizers C] {A B : C} {f g : A ⟶ B}
  证明: by
  let := IsReflexivePair.mk' r rf rg
  infer_instance

Depends on / 依赖: IsReflexivePair, IsReflexivePair.mk, infer_instance
-/
theorem hasCoequalizer_of_common_section [HasReflexiveCoequalizers C] {A B : C} {f g : A ⟶ B}
    (r : B ⟶ A) (rf : r ≫ f = 𝟙 _) (rg : r ≫ g = 𝟙 _) : HasCoequalizer f g := by
  let := IsReflexivePair.mk' r rf rg
  infer_instance

/--
theorem `hasEqualizer_of_common_retraction` / 定理 `hasEqualizer_of_common_retraction`

English:
theorem hasEqualizer_of_common_retraction
  statement: [HasCoreflexiveEqualizers C] {A B : C} {f g : A ⟶ B}
  proof: by
  let := IsCoreflexivePair.mk' r fr gr
  infer_instance

中文:
定理 hasEqualizer_of_common_retraction
  结论: [有余reflexiveEqualizers C] {A B : C} {f g : A ⟶ B}
  证明: by
  let := IsCoreflexivePair.mk' r fr gr
  infer_instance

Depends on / 依赖: Discrete, HasTerminal, IsClosedUnderLimitsOfShape, IsCoreflexivePair, IsCoreflexivePair.mk, P.IsClosedUnderLimitsOfShape, PEmpty, infer_instance
-/
theorem hasEqualizer_of_common_retraction [HasCoreflexiveEqualizers C] {A B : C} {f g : A ⟶ B}
    (r : B ⟶ A) (fr : f ≫ r = 𝟙 _) (gr : g ≫ r = 𝟙 _) : HasEqualizer f g := by
  let := IsCoreflexivePair.mk' r fr gr
  infer_instance

/-- If `C` has coequalizers, then it has reflexive coequalizers. -/
instance (priority := 100) hasReflexiveCoequalizers_of_hasCoequalizers [HasCoequalizers C] :
    HasReflexiveCoequalizers C where has_coeq A B f g _ := by infer_instance

/-- If `C` has equalizers, then it has coreflexive equalizers. -/
instance (priority := 100) hasCoreflexiveEqualizers_of_hasEqualizers [HasEqualizers C] :
    HasCoreflexiveEqualizers C where has_eq A B f g _ := by infer_instance

end Limits

end CategoryTheory

namespace CategoryTheory

universe v v₂ u u₂

namespace Limits

/--
Inductive type `WalkingReflexivePair` / 归纳类型 `WalkingReflexivePair`

English:
inductive WalkingReflexivePair
  parameters: : Type where
  constructors (2):
    - zero: 
    - one: 

中文:
归纳类型 WalkingReflexivePair
  参数: : 类型 where
  构造子 (2 个):
    - zero: 
    - one: 
-/
inductive WalkingReflexivePair : Type where
  | zero
  | one
  deriving DecidableEq, Inhabited

open WalkingReflexivePair

namespace WalkingReflexivePair

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `Hom` / 归纳类型 `Hom`

English:
inductive Hom
  parameters: : (WalkingReflexivePair -> WalkingReflexivePair -> Type)
  constructors (6):
    - left: Hom one zero
    - right: Hom one zero
    - reflexion: Hom zero one
    - leftCompReflexion: Hom one one
    - rightCompReflexion: Hom one one
    - id: (X : WalkingReflexivePair) : Hom X X

中文:
归纳类型 态射
  参数: : (WalkingReflexivePair -> WalkingReflexivePair -> 类型)
  构造子 (6 个):
    - left: 态射 one zero
    - right: 态射 one zero
    - reflexion: 态射 zero one
    - leftCompReflexion: 态射 one one
    - rightCompReflexion: 态射 one one
    - id: (X : WalkingReflexivePair) : 态射 X X
-/
inductive Hom : (WalkingReflexivePair -> WalkingReflexivePair -> Type)
  | left : Hom one zero
  | right : Hom one zero
  | reflexion : Hom zero one
  | leftCompReflexion : Hom one one
  | rightCompReflexion : Hom one one
  | id (X : WalkingReflexivePair) : Hom X X
  deriving DecidableEq

/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: :

中文:
定义 态射.comp
  签名: :
-/
def Hom.comp :
    forall {X Y Z : WalkingReflexivePair} (_ : Hom X Y)
      (_ : Hom Y Z), Hom X Z
  | _, _, _, id _, h => h
  | _, _, _, h, id _ => h
  | _, _, _, reflexion, left => id zero
  | _, _, _, reflexion, right => id zero
  | _, _, _, reflexion, rightCompReflexion => reflexion
  | _, _, _, reflexion, leftCompReflexion => reflexion
  | _, _, _, left, reflexion => leftCompReflexion
  | _, _, _, right, reflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, rightCompReflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, leftCompReflexion => rightCompReflexion
  | _, _, _, rightCompReflexion, right => right
  | _, _, _, rightCompReflexion, left => right
  | _, _, _, leftCompReflexion, left => left
  | _, _, _, leftCompReflexion, right => left
  | _, _, _, leftCompReflexion, rightCompReflexion => leftCompReflexion
  | _, _, _, leftCompReflexion, leftCompReflexion => leftCompReflexion

/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : SmallCategory WalkingReflexivePair where
  body: Hom
  id := Hom.id
  comp := Hom.comp
  comp_id := by intro _ _ f; cases f <;> rfl
  id_comp := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl

中文:
实例 category
  签名: : 小范畴 WalkingReflexivePair where
  定义体: Hom
  id := Hom.id
  comp := Hom.comp
  comp_id := by intro _ _ f; cases f <;> rfl
  id_comp := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl
-/
instance category : SmallCategory WalkingReflexivePair where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  comp_id := by intro _ _ f; cases f <;> rfl
  id_comp := by intro _ _ f; cases f <;> rfl
  assoc := by intro _ _ _ _ f g h; cases f <;> cases g <;> cases h <;> rfl

open Hom

@[simp]
/--
lemma `Hom.id_eq` / 引理 `Hom.id_eq`

English:
lemma Hom.id_eq
  given: (X : WalkingReflexivePair)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 态射.id_eq
  条件: (X : WalkingReflexivePair)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma Hom.id_eq (X : WalkingReflexivePair) :
    Hom.id X = 𝟙 X := rfl

@[reassoc (attr := simp)]
/--
lemma `reflexion_comp_left` / 引理 `reflexion_comp_left`

English:
lemma reflexion_comp_left
  statement: reflexion ≫ left = 𝟙 zero
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 reflexion_comp_left
  结论: reflexion ≫ left = 𝟙 zero
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma reflexion_comp_left : reflexion ≫ left = 𝟙 zero := rfl

@[reassoc (attr := simp)]
/--
lemma `reflexion_comp_right` / 引理 `reflexion_comp_right`

English:
lemma reflexion_comp_right
  statement: reflexion ≫ right = 𝟙 zero
  proof: rfl

@[simp]

中文:
引理 reflexion_comp_right
  结论: reflexion ≫ right = 𝟙 zero
  证明: rfl

@[simp]
-/
lemma reflexion_comp_right : reflexion ≫ right = 𝟙 zero := rfl

@[simp]
/--
lemma `leftCompReflexion_eq` / 引理 `leftCompReflexion_eq`

English:
lemma leftCompReflexion_eq
  statement: leftCompReflexion = (left ≫ reflexion : one ⟶ one)
  proof: rfl

@[simp]

中文:
引理 leftCompReflexion_eq
  结论: leftCompReflexion = (left ≫ reflexion : one ⟶ one)
  证明: rfl

@[simp]
-/
lemma leftCompReflexion_eq : leftCompReflexion = (left ≫ reflexion : one ⟶ one) := rfl

@[simp]
/--
lemma `rightCompReflexion_eq` / 引理 `rightCompReflexion_eq`

English:
lemma rightCompReflexion_eq
  statement: rightCompReflexion = (right ≫ reflexion : one ⟶ one)
  proof: rfl

中文:
引理 rightCompReflexion_eq
  结论: rightCompReflexion = (right ≫ reflexion : one ⟶ one)
  证明: rfl
-/
lemma rightCompReflexion_eq : rightCompReflexion = (right ≫ reflexion : one ⟶ one) := rfl

section FunctorsOutOfWalkingReflexivePair

variable {C : Type u} [Category.{v} C]

@[reassoc (attr := simp)]
/--
lemma `map_reflexion_comp_map_left` / 引理 `map_reflexion_comp_map_left`

English:
lemma map_reflexion_comp_map_left
  given: (F : WalkingReflexivePair ⥤ C)
  proof: by
  rw [← F.map_comp]; rw [reflexion_comp_left]; rw [F.map_id]

@[reassoc (attr := simp)]

中文:
引理 map_reflexion_comp_map_left
  条件: (F : WalkingReflexivePair ⥤ C)
  证明: by
  rw [← F.map_comp]; rw [reflexion_comp_left]; rw [F.map_id]

@[reassoc (attr := simp)]

Depends on / 依赖: F.map_comp, F.map_id, map_comp, map_id, reflexion_comp_left
-/
lemma map_reflexion_comp_map_left (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map left = 𝟙 (F.obj zero) := by
  rw [← F.map_comp]; rw [reflexion_comp_left]; rw [F.map_id]

@[reassoc (attr := simp)]
/--
lemma `map_reflexion_comp_map_right` / 引理 `map_reflexion_comp_map_right`

English:
lemma map_reflexion_comp_map_right
  given: (F : WalkingReflexivePair ⥤ C)
  proof: by
  rw [← F.map_comp]; rw [reflexion_comp_right]; rw [F.map_id]

中文:
引理 map_reflexion_comp_map_right
  条件: (F : WalkingReflexivePair ⥤ C)
  证明: by
  rw [← F.map_comp]; rw [reflexion_comp_right]; rw [F.map_id]

Depends on / 依赖: F.map_comp, F.map_id, map_comp, map_id, reflexion_comp_right
-/
lemma map_reflexion_comp_map_right (F : WalkingReflexivePair ⥤ C) :
    F.map reflexion ≫ F.map right = 𝟙 (F.obj zero) := by
  rw [← F.map_comp]; rw [reflexion_comp_right]; rw [F.map_id]

end FunctorsOutOfWalkingReflexivePair

end WalkingReflexivePair

namespace WalkingParallelPair

/-- The inclusion functor forgetting the common section -/
@[simps!]
/--
Definition of `inclusionWalkingReflexivePair` / `inclusionWalkingReflexivePair` 的定义

English:
definition inclusionWalkingReflexivePair
  signature: : WalkingParallelPair ⥤ WalkingReflexivePair where
  body: fun x => match x with
    | one => WalkingReflexivePair.zero
    | zero => WalkingReflexivePair.one
  map := fun f => match f with
    | .left => WalkingReflexivePair.Hom.left
    | .right => WalkingReflexivePair.Hom.right
    | .id _ => WalkingReflexivePair.Hom.id _
  map_comp := by
    intro _ _ _

中文:
定义 inclusionWalkingReflexivePair
  签名: : WalkingParallelPair ⥤ WalkingReflexivePair where
  定义体: fun x => match x with
    | one => WalkingReflexivePair.zero
    | zero => WalkingReflexivePair.one
  map := fun f => match f with
    | .left => WalkingReflexivePair.Hom.left
    | .right => WalkingReflexivePair.Hom.right
    | .id _ => WalkingReflexivePair.Hom.id _
  map_comp := by
    intro _ _ _
-/
def inclusionWalkingReflexivePair : WalkingParallelPair ⥤ WalkingReflexivePair where
  obj := fun x => match x with
    | one => WalkingReflexivePair.zero
    | zero => WalkingReflexivePair.one
  map := fun f => match f with
    | .left => WalkingReflexivePair.Hom.left
    | .right => WalkingReflexivePair.Hom.right
    | .id _ => WalkingReflexivePair.Hom.id _
  map_comp := by
    intro _ _ _ f g; cases f <;> cases g <;> rfl

variable {C : Type u} [Category.{v} C]

instance (X : WalkingReflexivePair) :
    Nonempty (StructuredArrow X inclusionWalkingReflexivePair) := by
  cases X with
  | zero => exact ⟨StructuredArrow.mk (Y := one) (𝟙 _)⟩
  | one => exact ⟨StructuredArrow.mk (Y := zero) (𝟙 _)⟩

open WalkingReflexivePair.Hom in
instance (X : WalkingReflexivePair) :
    IsConnected (StructuredArrow X inclusionWalkingReflexivePair) := by
  cases X with
  | zero =>
      refine IsConnected.of_induct (j₀ := StructuredArrow.mk (Y := one) (𝟙 _)) ?_
      rintro p h₁ h₂ ⟨⟨⟨⟩⟩, (_ | _), ⟨_⟩⟩
      · exact (h₂ (StructuredArrow.homMk .left)).2 h₁
      · exact h₁
  | one =>
      refine IsConnected.of_induct (j₀ := StructuredArrow.mk (Y := zero) (𝟙 _))
        (fun p h₁ h₂ => ?_)
      have hₗ : StructuredArrow.mk left in p := (h₂ (StructuredArrow.homMk .left)).1 h₁
      have hᵣ : StructuredArrow.mk right in p := (h₂ (StructuredArrow.homMk .right)).1 h₁
      rintro ⟨⟨⟨⟩⟩, (_ | _), ⟨_⟩⟩
      · exact (h₂ (StructuredArrow.homMk .left)).2 hₗ
      · exact (h₂ (StructuredArrow.homMk .right)).2 hᵣ
      all_goals assumption

/--
Instance `inclusionWalkingReflexivePair_final` / 实例 `inclusionWalkingReflexivePair_final`

English:
instance inclusionWalkingReflexivePair_final
  signature: : Functor.Final inclusionWalkingReflexivePair where
  body: inferInstance

中文:
实例 inclusionWalkingReflexivePair_final
  签名: : 函子.终 inclusionWalkingReflexivePair where
  定义体: inferInstance
-/
instance inclusionWalkingReflexivePair_final : Functor.Final inclusionWalkingReflexivePair where
  out := inferInstance

end WalkingParallelPair

end Limits

namespace Limits

open WalkingReflexivePair

variable {C : Type u} [Category.{v} C]

variable {A B : C}

/--
Definition of `reflexivePair` / `reflexivePair` 的定义

English:
definition reflexivePair
  signature: (f g : A ⟶ B) (s : B ⟶ A)
  body: match x with
    | zero => B
    | one => A
  map h :=
    match h with
    | .id _ => 𝟙 _
    | .left => f
    | .right => g
    | .reflexion => s
    | .rightCompReflexion => g ≫ s
    | .leftCompReflexion => f ≫ s
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;>
      simp only [Category.id

中文:
定义 reflexivePair
  签名: (f g : A ⟶ B) (s : B ⟶ A)
  定义体: match x with
    | zero => B
    | one => A
  map h :=
    match h with
    | .id _ => 𝟙 _
    | .left => f
    | .right => g
    | .reflexion => s
    | .rightCompReflexion => g ≫ s
    | .leftCompReflexion => f ≫ s
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;>
      simp only [Category.id

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, WalkingReflexivePair, cat_disch, comp_id, id_comp, leftCompReflexion, map_comp, reassoc_of, reflexion, rightCompReflexion
-/
def reflexivePair (f g : A ⟶ B) (s : B ⟶ A)
    (sl : s ≫ f = 𝟙 B := by cat_disch) (sr : s ≫ g = 𝟙 B := by cat_disch) :
    (WalkingReflexivePair ⥤ C) where
  obj x :=
    match x with
    | zero => B
    | one => A
  map h :=
    match h with
    | .id _ => 𝟙 _
    | .left => f
    | .right => g
    | .reflexion => s
    | .rightCompReflexion => g ≫ s
    | .leftCompReflexion => f ≫ s
  map_comp := by
    rintro _ _ _ ⟨⟩ g <;> cases g <;>
      simp only [Category.id_comp, Category.comp_id, Category.assoc, sl, sr,
        reassoc_of% sl, reassoc_of% sr] <;> rfl

section

variable {A B : C}
variable (f g : A ⟶ B) (s : B ⟶ A) {sl : s ≫ f = 𝟙 B} {sr : s ≫ g = 𝟙 B}

/--
lemma `reflexivePair_obj_zero` / 引理 `reflexivePair_obj_zero`

English:
lemma reflexivePair_obj_zero
  statement: (reflexivePair f g s sl sr).obj zero = B
  proof: rfl

中文:
引理 reflexivePair_obj_zero
  结论: (reflexivePair f g s sl sr).obj zero = B
  证明: rfl
-/
@[simp] lemma reflexivePair_obj_zero : (reflexivePair f g s sl sr).obj zero = B := rfl

/--
lemma `reflexivePair_obj_one` / 引理 `reflexivePair_obj_one`

English:
lemma reflexivePair_obj_one
  statement: (reflexivePair f g s sl sr).obj one = A
  proof: rfl

中文:
引理 reflexivePair_obj_one
  结论: (reflexivePair f g s sl sr).obj one = A
  证明: rfl
-/
@[simp] lemma reflexivePair_obj_one : (reflexivePair f g s sl sr).obj one = A := rfl

/--
lemma `reflexivePair_map_right` / 引理 `reflexivePair_map_right`

English:
lemma reflexivePair_map_right
  statement: (reflexivePair f g s sl sr).map .left = f
  proof: rfl

中文:
引理 reflexivePair_map_right
  结论: (reflexivePair f g s sl sr).map .left = f
  证明: rfl

Depends on / 依赖: Discrete, HasInitial, IsClosedUnderColimitsOfShape, P.IsClosedUnderColimitsOfShape, PEmpty
-/
@[simp] lemma reflexivePair_map_right : (reflexivePair f g s sl sr).map .left = f := rfl

/--
lemma `reflexivePair_map_left` / 引理 `reflexivePair_map_left`

English:
lemma reflexivePair_map_left
  statement: (reflexivePair f g s sl sr).map .right = g
  proof: rfl

中文:
引理 reflexivePair_map_left
  结论: (reflexivePair f g s sl sr).map .right = g
  证明: rfl
-/
@[simp] lemma reflexivePair_map_left : (reflexivePair f g s sl sr).map .right = g := rfl

/--
lemma `reflexivePair_map_reflexion` / 引理 `reflexivePair_map_reflexion`

English:
lemma reflexivePair_map_reflexion
  statement: (reflexivePair f g s sl sr).map .reflexion = s
  proof: rfl

中文:
引理 reflexivePair_map_reflexion
  结论: (reflexivePair f g s sl sr).map .reflexion = s
  证明: rfl
-/
@[simp] lemma reflexivePair_map_reflexion : (reflexivePair f g s sl sr).map .reflexion = s := rfl

end

/--
Definition of `ofIsReflexivePair` / `ofIsReflexivePair` 的定义

English:
definition ofIsReflexivePair
  signature: (f g : A ⟶ B) [IsReflexivePair f g]
  body: reflexivePair f g (commonSection f g)

@[simp]

中文:
定义 ofIsReflexivePair
  签名: (f g : A ⟶ B) [是ReflexivePair f g]
  定义体: reflexivePair f g (commonSection f g)

@[simp]

Depends on / 依赖: commonSection, reflexivePair
-/
noncomputable def ofIsReflexivePair (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingReflexivePair ⥤ C := reflexivePair f g (commonSection f g)

@[simp]
/--
lemma `ofIsReflexivePair_map_left` / 引理 `ofIsReflexivePair_map_left`

English:
lemma ofIsReflexivePair_map_left
  given: (f g : A ⟶ B) [IsReflexivePair f g]
  proof: rfl

@[simp]

中文:
引理 ofIsReflexivePair_map_left
  条件: (f g : A ⟶ B) [是ReflexivePair f g]
  证明: rfl

@[simp]
-/
lemma ofIsReflexivePair_map_left (f g : A ⟶ B) [IsReflexivePair f g] :
    (ofIsReflexivePair f g).map .left = f := rfl

@[simp]
/--
lemma `ofIsReflexivePair_map_right` / 引理 `ofIsReflexivePair_map_right`

English:
lemma ofIsReflexivePair_map_right
  given: (f g : A ⟶ B) [IsReflexivePair f g]
  proof: rfl

中文:
引理 ofIsReflexivePair_map_right
  条件: (f g : A ⟶ B) [是ReflexivePair f g]
  证明: rfl
-/
lemma ofIsReflexivePair_map_right (f g : A ⟶ B) [IsReflexivePair f g] :
    (ofIsReflexivePair f g).map .right = g := rfl

/--
Definition of `inclusionWalkingReflexivePairOfIsReflexivePairIso` / `inclusionWalkingReflexivePairOfIsReflexivePairIso` 的定义

English:
definition inclusionWalkingReflexivePairOfIsReflexivePairIso
  body: diagramIsoParallelPair _

中文:
定义 inclusionWalkingReflexivePairOfIsReflexivePairIso
  定义体: diagramIsoParallelPair _

Depends on / 依赖: diagramIsoParallelPair
-/
noncomputable def inclusionWalkingReflexivePairOfIsReflexivePairIso
    (f g : A ⟶ B) [IsReflexivePair f g] :
    WalkingParallelPair.inclusionWalkingReflexivePair ⋙ (ofIsReflexivePair f g) ≅
      parallelPair f g :=
  diagramIsoParallelPair _

end Limits

namespace Limits

variable {C : Type u} [Category.{v} C]

namespace reflexivePair

open WalkingReflexivePair WalkingReflexivePair.Hom

section
section NatTrans

variable {F G : WalkingReflexivePair ⥤ C}
  (e₀ : F.obj zero ⟶ G.obj zero) (e₁ : F.obj one ⟶ G.obj one)
  (h₁ : F.map left ≫ e₀ = e₁ ≫ G.map left := by cat_disch)
  (h₂ : F.map right ≫ e₀ = e₁ ≫ G.map right := by cat_disch)
  (h₃ : F.map reflexion ≫ e₁ = e₀ ≫ G.map reflexion := by cat_disch)

set_option backward.privateInPublic true in
/--
Definition of `mkNatTrans` / `mkNatTrans` 的定义

English:
definition mkNatTrans
  signature: : F ⟶ G where
  body: fun x => match x with
    | zero => e₀
    | one => e₁
  naturality _ _ f := by
    cases f
    all_goals
      dsimp
      simp only [Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp, h₁, h₂, h₃,
        reassoc_of% h₁, reassoc_of% h₂, Category.assoc]

中文:
定义 mk自然数Trans
  签名: : F ⟶ G where
  定义体: fun x => match x with
    | zero => e₀
    | one => e₁
  naturality _ _ f := by
    cases f
    all_goals
      dsimp
      simp only [Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp, h₁, h₂, h₃,
        reassoc_of% h₁, reassoc_of% h₂, Category.assoc]
-/
def mkNatTrans : F ⟶ G where
  app := fun x => match x with
    | zero => e₀
    | one => e₁
  naturality _ _ f := by
    cases f
    all_goals
      dsimp
      simp only [Functor.map_id, Category.id_comp, Category.comp_id, Functor.map_comp, h₁, h₂, h₃,
        reassoc_of% h₁, reassoc_of% h₂, Category.assoc]

set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatTrans_app_zero` / 引理 `mkNatTrans_app_zero`

English:
lemma mkNatTrans_app_zero
  statement: (mkNatTrans e₀ e₁ h₁ h₂ h₃).app zero = e₀
  proof: rfl

中文:
引理 mk自然数Trans_app_zero
  结论: (mk自然数Trans e₀ e₁ h₁ h₂ h₃).app zero = e₀
  证明: rfl
-/
lemma mkNatTrans_app_zero : (mkNatTrans e₀ e₁ h₁ h₂ h₃).app zero = e₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/--
lemma `mkNatTrans_app_one` / 引理 `mkNatTrans_app_one`

English:
lemma mkNatTrans_app_one
  statement: (mkNatTrans e₀ e₁ h₁ h₂ h₃).app one = e₁
  proof: rfl

中文:
引理 mk自然数Trans_app_one
  结论: (mk自然数Trans e₀ e₁ h₁ h₂ h₃).app one = e₁
  证明: rfl
-/
lemma mkNatTrans_app_one : (mkNatTrans e₀ e₁ h₁ h₂ h₃).app one = e₁ := rfl

end NatTrans
section NatIso

variable {F G : WalkingReflexivePair ⥤ C}
/-- Constructor for natural isomorphisms between functors out of `WalkingReflexivePair`. -/
@[simps!]
/--
Definition of `mkNatIso` / `mkNatIso` 的定义

English:
definition mkNatIso
  signature: (e₀ : F.obj zero ≅ G.obj zero) (e₁ : F.obj one ≅ G.obj one)
  body: mkNatTrans e₀.hom e₁.hom
  inv := mkNatTrans e₀.inv e₁.inv
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₁, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₂, e₀.hom_inv_id,
            Category.comp_id

中文:
定义 mk自然数Iso
  签名: (e₀ : F.obj zero ≅ G.obj zero) (e₁ : F.obj one ≅ G.obj one)
  定义体: mkNatTrans e₀.hom e₁.hom
  inv := mkNatTrans e₀.inv e₁.inv
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₁, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₂, e₀.hom_inv_id,
            Category.comp_id

Depends on / 依赖: Category, Category.comp_id, F.map, G.map, cancel_epi, cat_disch, comp_id, hom_inv_id, hom_inv_id_assoc, mkNatTrans, reassoc_of, reflexion
-/
def mkNatIso (e₀ : F.obj zero ≅ G.obj zero) (e₁ : F.obj one ≅ G.obj one)
    (h₁ : F.map left ≫ e₀.hom = e₁.hom ≫ G.map left := by cat_disch)
    (h₂ : F.map right ≫ e₀.hom = e₁.hom ≫ G.map right := by cat_disch)
    (h₃ : F.map reflexion ≫ e₁.hom = e₀.hom ≫ G.map reflexion := by cat_disch) :
    F ≅ G where
  hom := mkNatTrans e₀.hom e₁.hom
  inv := mkNatTrans e₀.inv e₁.inv
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₁, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc, ← reassoc_of% h₂, e₀.hom_inv_id,
            Category.comp_id])
        (by rw [← cancel_epi e₀.hom, e₀.hom_inv_id_assoc, ← reassoc_of% h₃, e₁.hom_inv_id,
            Category.comp_id])
  hom_inv_id := by ext x; cases x <;> simp
  inv_hom_id := by ext x; cases x <;> simp

variable (F)

/-- Every functor out of `WalkingReflexivePair` is isomorphic to the `reflexivePair` given by
its components -/
@[simps!]
/--
Definition of `diagramIsoReflexivePair` / `diagramIsoReflexivePair` 的定义

English:
definition diagramIsoReflexivePair
  signature: :
  body: mkNatIso (Iso.refl _) (Iso.refl _)

中文:
定义 diagramIsoReflexivePair
  签名: :
  定义体: mkNatIso (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, mkNatIso
-/
def diagramIsoReflexivePair :
    F ≅ reflexivePair (F.map left) (F.map right) (F.map reflexion) :=
  mkNatIso (Iso.refl _) (Iso.refl _)

end NatIso

set_option backward.defeqAttrib.useBackward true in
/-- A `reflexivePair` composed with a functor is isomorphic to the `reflexivePair` obtained by
applying the functor at each map. -/
@[simps!]
/--
Definition of `compRightIso` / `compRightIso` 的定义

English:
definition compRightIso
  signature: {D : Type u₂} [Category.{v₂} D] {A B : C}
  body: mkNatIso (Iso.refl _) (Iso.refl _)

中文:
定义 compRightIso
  签名: {D : 类型u₂} [范畴.{v₂} D] {A B : C}
  定义体: mkNatIso (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, mkNatIso
-/
def compRightIso {D : Type u₂} [Category.{v₂} D] {A B : C}
    (f g : A ⟶ B) (s : B ⟶ A) (sl : s ≫ f = 𝟙 B) (sr : s ≫ g = 𝟙 B) (F : C ⥤ D) :
    (reflexivePair f g s sl sr) ⋙ F ≅ reflexivePair (F.map f) (F.map g) (F.map s)
      (by simp only [← Functor.map_comp, sl, Functor.map_id])
      (by simp only [← Functor.map_comp, sr, Functor.map_id]) :=
  mkNatIso (Iso.refl _) (Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `whiskerRightMkNatTrans` / 引理 `whiskerRightMkNatTrans`

English:
lemma whiskerRightMkNatTrans
  statement: {F G : WalkingReflexivePair ⥤ C}
  proof: by
  ext x; cases x <;> simp

中文:
引理 whiskerRightMk自然数Trans
  结论: {F G : WalkingReflexivePair ⥤ C}
  证明: by
  ext x; cases x <;> simp
-/
lemma whiskerRightMkNatTrans {F G : WalkingReflexivePair ⥤ C}
    (e₀ : F.obj zero ⟶ G.obj zero) (e₁ : F.obj one ⟶ G.obj one)
    {h₁ : F.map left ≫ e₀ = e₁ ≫ G.map left}
    {h₂ : F.map right ≫ e₀ = e₁ ≫ G.map right}
    {h₃ : F.map reflexion ≫ e₁ = e₀ ≫ G.map reflexion}
    {D : Type u₂} [Category.{v₂} D] (H : C ⥤ D) :
    Functor.whiskerRight (mkNatTrans e₀ e₁ : F ⟶ G) H =
      mkNatTrans (H.map e₀) (H.map e₁)
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₁])
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₂])
          (by simp only [Functor.comp_obj, Functor.comp_map, ← Functor.map_comp, h₃]) := by
  ext x; cases x <;> simp

end

/--
Instance `to_isReflexivePair` / 实例 `to_isReflexivePair`

English:
instance to_isReflexivePair
  signature: {F : WalkingReflexivePair ⥤ C}
  body: ⟨F.map .reflexion, map_reflexion_comp_map_left F, map_reflexion_comp_map_right F⟩

中文:
实例 to_isReflexivePair
  签名: {F : WalkingReflexivePair ⥤ C}
  定义体: ⟨F.map .reflexion, map_reflexion_comp_map_left F, map_reflexion_comp_map_right F⟩

Depends on / 依赖: F.map, map_reflexion_comp_map_left, map_reflexion_comp_map_right, reflexion
-/
instance to_isReflexivePair {F : WalkingReflexivePair ⥤ C} :
    IsReflexivePair (F.map .left) (F.map .right) :=
  ⟨F.map .reflexion, map_reflexion_comp_map_left F, map_reflexion_comp_map_right F⟩

end reflexivePair

/--
Definition of `ReflexiveCofork` / `ReflexiveCofork` 的定义

English:
abbreviation ReflexiveCofork
  signature: (F : WalkingReflexivePair ⥤ C)
  body: Cocone F

中文:
缩写 ReflexiveCofork
  签名: (F : WalkingReflexivePair ⥤ C)
  定义体: Cocone F

Depends on / 依赖: Cocone
-/
abbrev ReflexiveCofork (F : WalkingReflexivePair ⥤ C) := Cocone F

namespace ReflexiveCofork

open WalkingReflexivePair WalkingReflexivePair.Hom

variable {F : WalkingReflexivePair ⥤ C}

/--
Definition of `π` / `π` 的定义

English:
abbreviation π
  signature: (G : ReflexiveCofork F)
  body: G.ι.app zero

中文:
缩写 π
  签名: (G : ReflexiveCofork F)
  定义体: G.ι.app zero
-/
abbrev π (G : ReflexiveCofork F) : F.obj zero ⟶ G.pt := G.ι.app zero

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for `ReflexiveCofork` -/
@[simps pt]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π)
  body: X
  ι := reflexivePair.mkNatTrans π (F.map left ≫ π)

@[simp]

中文:
定义 mk
  签名: {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π)
  定义体: X
  ι := reflexivePair.mkNatTrans π (F.map left ≫ π)

@[simp]
-/
def mk {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π) :
    ReflexiveCofork F where
  pt := X
  ι := reflexivePair.mkNatTrans π (F.map left ≫ π)

@[simp]
/--
lemma `mk_π` / 引理 `mk_π`

English:
lemma mk_π
  given: {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π)
  proof: rfl

中文:
引理 mk_π
  条件: {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π)
  证明: rfl
-/
lemma mk_π {X : C} (π : F.obj zero ⟶ X) (h : F.map left ≫ π = F.map right ≫ π) :
    (mk π h).π = π := rfl

/--
lemma `condition` / 引理 `condition`

English:
lemma condition
  given: (G : ReflexiveCofork F)
  statement: F.map left ≫ G.π = F.map right ≫ G.π
  proof: by
  rw [Cocone.w G left]; rw [Cocone.w G right]

@[simp]

中文:
引理 condition
  条件: (G : ReflexiveCofork F)
  结论: F.map left ≫ G.π = F.map right ≫ G.π
  证明: by
  rw [Cocone.w G left]; rw [Cocone.w G right]

@[simp]

Depends on / 依赖: Cocone, Cocone.w
-/
lemma condition (G : ReflexiveCofork F) : F.map left ≫ G.π = F.map right ≫ G.π := by
  rw [Cocone.w G left]; rw [Cocone.w G right]

@[simp]
/--
lemma `app_one_eq_π` / 引理 `app_one_eq_π`

English:
lemma app_one_eq_π
  given: (G : ReflexiveCofork F)
  statement: G.ι.app zero = G.π
  proof: rfl

中文:
引理 app_one_eq_π
  条件: (G : ReflexiveCofork F)
  结论: G.ι.app zero = G.π
  证明: rfl
-/
lemma app_one_eq_π (G : ReflexiveCofork F) : G.ι.app zero = G.π := rfl

/--
Definition of `toCofork` / `toCofork` 的定义

English:
abbreviation toCofork
  signature: (G : ReflexiveCofork F)
  body: Cofork.ofπ G.π (by simp)

中文:
缩写 toCofork
  签名: (G : ReflexiveCofork F)
  定义体: Cofork.ofπ G.π (by simp)

Depends on / 依赖: Cofork, Cofork.of
-/
abbrev toCofork (G : ReflexiveCofork F) : Cofork (F.map left) (F.map right) :=
  Cofork.ofπ G.π (by simp)

end ReflexiveCofork

noncomputable section
open WalkingReflexivePair WalkingReflexivePair.Hom

variable (F : WalkingReflexivePair ⥤ C)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Forgetting the reflexion yields an equivalence between cocones over a bundled reflexive pair and
coforks on the underlying parallel pair. -/
@[simps! functor_obj_pt inverse_obj_pt]
/--
Definition of `reflexiveCoforkEquivCofork` / `reflexiveCoforkEquivCofork` 的定义

English:
definition reflexiveCoforkEquivCofork
  signature: :
  body: (Functor.Final.coconesEquiv _ F).symm.trans (Cocone.precomposeEquivalence
    (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F)))

中文:
定义 reflexiveCoforkEquivCofork
  签名: :
  定义体: (Functor.Final.coconesEquiv _ F).symm.trans (Cocone.precomposeEquivalence
    (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F)))

Depends on / 依赖: Cocone, Cocone.precomposeEquivalence, Functor, Functor.Final.coconesEquiv, WalkingParallelPair, WalkingParallelPair.inclusionWalkingReflexivePair, coconesEquiv, diagramIsoParallelPair, inclusionWalkingReflexivePair, precomposeEquivalence, symm.trans
-/
def reflexiveCoforkEquivCofork :
    ReflexiveCofork F ≌ Cofork (F.map left) (F.map right) :=
  (Functor.Final.coconesEquiv _ F).symm.trans (Cocone.precomposeEquivalence
    (diagramIsoParallelPair (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ F)))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `reflexiveCoforkEquivCofork_functor_obj_π` / 引理 `reflexiveCoforkEquivCofork_functor_obj_π`

English:
lemma reflexiveCoforkEquivCofork_functor_obj_π
  given: (G : ReflexiveCofork F)
  proof: by
  dsimp [reflexiveCoforkEquivCofork]
  rw [ReflexiveCofork.π]; rw [Cofork.π]
  simp

中文:
引理 reflexiveCoforkEquivCofork_functor_obj_π
  条件: (G : ReflexiveCofork F)
  证明: by
  dsimp [reflexiveCoforkEquivCofork]
  rw [ReflexiveCofork.π]; rw [Cofork.π]
  simp

Depends on / 依赖: Cofork, ReflexiveCofork, reflexiveCoforkEquivCofork
-/
lemma reflexiveCoforkEquivCofork_functor_obj_π (G : ReflexiveCofork F) :
    ((reflexiveCoforkEquivCofork F).functor.obj G).π = G.π := by
  dsimp [reflexiveCoforkEquivCofork]
  rw [ReflexiveCofork.π]; rw [Cofork.π]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `reflexiveCoforkEquivCofork_inverse_obj_π` / 引理 `reflexiveCoforkEquivCofork_inverse_obj_π`

English:
lemma reflexiveCoforkEquivCofork_inverse_obj_π
  proof: by
  dsimp only [reflexiveCoforkEquivCofork, Equivalence.symm, Equivalence.trans,
    ReflexiveCofork.π, Cocone.precomposeEquivalence, Cocone.precompose,
    Functor.comp, Functor.Final.coconesEquiv]
  rw [Functor.Final.extendCocone_obj_ι_app' (Y := .one) (f := 𝟙 zero)]
  simp

中文:
引理 reflexiveCoforkEquivCofork_inverse_obj_π
  证明: by
  dsimp only [reflexiveCoforkEquivCofork, Equivalence.symm, Equivalence.trans,
    ReflexiveCofork.π, Cocone.precomposeEquivalence, Cocone.precompose,
    Functor.comp, Functor.Final.coconesEquiv]
  rw [Functor.Final.extendCocone_obj_ι_app' (Y := .one) (f := 𝟙 zero)]
  simp

Depends on / 依赖: Cocone, Cocone.precompose, Cocone.precomposeEquivalence, Equivalence, Equivalence.symm, Equivalence.trans, Functor, Functor.Final.coconesEquiv, Functor.Final.extendCocone_obj_, Functor.comp, ReflexiveCofork, coconesEquiv, precompose, precomposeEquivalence, reflexiveCoforkEquivCofork
-/
lemma reflexiveCoforkEquivCofork_inverse_obj_π
    (G : Cofork (F.map left) (F.map right)) :
    ((reflexiveCoforkEquivCofork F).inverse.obj G).π = G.π := by
  dsimp only [reflexiveCoforkEquivCofork, Equivalence.symm, Equivalence.trans,
    ReflexiveCofork.π, Cocone.precomposeEquivalence, Cocone.precompose,
    Functor.comp, Functor.Final.coconesEquiv]
  rw [Functor.Final.extendCocone_obj_ι_app' (Y := .one) (f := 𝟙 zero)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `reflexiveCoforkEquivCoforkObjIso` / `reflexiveCoforkEquivCoforkObjIso` 的定义

English:
definition reflexiveCoforkEquivCoforkObjIso
  signature: (G : ReflexiveCofork F)
  body: Cofork.ext (Iso.refl _)
    (by simp [reflexiveCoforkEquivCofork, Cofork.π])

中文:
定义 reflexiveCoforkEquivCoforkObjIso
  签名: (G : ReflexiveCofork F)
  定义体: Cofork.ext (Iso.refl _)
    (by simp [reflexiveCoforkEquivCofork, Cofork.π])

Depends on / 依赖: Cofork, Cofork.ext, Iso.refl, reflexiveCoforkEquivCofork
-/
def reflexiveCoforkEquivCoforkObjIso (G : ReflexiveCofork F) :
    (reflexiveCoforkEquivCofork F).functor.obj G ≅ G.toCofork :=
  Cofork.ext (Iso.refl _)
    (by simp [reflexiveCoforkEquivCofork, Cofork.π])

/--
lemma `hasReflexiveCoequalizer_iff_hasCoequalizer` / 引理 `hasReflexiveCoequalizer_iff_hasCoequalizer`

English:
lemma hasReflexiveCoequalizer_iff_hasCoequalizer
  proof: by
  simpa only [hasColimit_iff_hasInitial_cocone]
    using Equivalence.hasInitial_iff (reflexiveCoforkEquivCofork F)

中文:
引理 hasReflexiveCoequalizer_iff_hasCoequalizer
  证明: by
  simpa only [hasColimit_iff_hasInitial_cocone]
    using Equivalence.hasInitial_iff (reflexiveCoforkEquivCofork F)

Depends on / 依赖: Equivalence, Equivalence.hasInitial_iff, hasColimit_iff_hasInitial_cocone, hasInitial_iff, reflexiveCoforkEquivCofork
-/
lemma hasReflexiveCoequalizer_iff_hasCoequalizer :
    HasColimit F ↔ HasCoequalizer (F.map left) (F.map right) := by
  simpa only [hasColimit_iff_hasInitial_cocone]
    using Equivalence.hasInitial_iff (reflexiveCoforkEquivCofork F)

/--
Instance `reflexivePair_hasColimit_of_hasCoequalizer` / 实例 `reflexivePair_hasColimit_of_hasCoequalizer`

English:
instance reflexivePair_hasColimit_of_hasCoequalizer
  body: .mpr h hasReflexiveCoequalizer_iff_hasCoequalizer _

中文:
实例 reflexivePair_hasColimit_of_hasCoequalizer
  定义体: .mpr h hasReflexiveCoequalizer_iff_hasCoequalizer _

Depends on / 依赖: hasReflexiveCoequalizer_iff_hasCoequalizer
-/
instance reflexivePair_hasColimit_of_hasCoequalizer
    [h : HasCoequalizer (F.map left) (F.map right)] : HasColimit F :=
.mpr h hasReflexiveCoequalizer_iff_hasCoequalizer _

/--
Definition of `ReflexiveCofork.isColimitEquiv` / `ReflexiveCofork.isColimitEquiv` 的定义

English:
definition ReflexiveCofork.isColimitEquiv
  signature: (G : ReflexiveCofork F)
  body: .trans IsColimit.equivIsoColimit (reflexiveCoforkEquivCoforkObjIso F G).symm
(IsColimit.precomposeHomEquiv (diagramIsoParallelPair _).symm (G.whisker _)).trans
      Functor.Final.isColimitWhiskerEquiv _ _

中文:
定义 ReflexiveCofork.isColimitEquiv
  签名: (G : ReflexiveCofork F)
  定义体: .trans IsColimit.equivIsoColimit (reflexiveCoforkEquivCoforkObjIso F G).symm
(IsColimit.precomposeHomEquiv (diagramIsoParallelPair _).symm (G.whisker _)).trans
      Functor.Final.isColimitWhiskerEquiv _ _

Depends on / 依赖: Functor, Functor.Final.isColimitWhiskerEquiv, G.whisker, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, diagramIsoParallelPair, equivIsoColimit, isColimitWhiskerEquiv, precomposeHomEquiv, reflexiveCoforkEquivCoforkObjIso, whisker
-/
def ReflexiveCofork.isColimitEquiv (G : ReflexiveCofork F) :
    IsColimit (G.toCofork) ≃ IsColimit G :=
.trans IsColimit.equivIsoColimit (reflexiveCoforkEquivCoforkObjIso F G).symm
(IsColimit.precomposeHomEquiv (diagramIsoParallelPair _).symm (G.whisker _)).trans
      Functor.Final.isColimitWhiskerEquiv _ _

section

variable [HasCoequalizer (F.map left) (F.map right)]

/--
Definition of `reflexiveCoequalizerIsoCoequalizer` / `reflexiveCoequalizerIsoCoequalizer` 的定义

English:
definition reflexiveCoequalizerIsoCoequalizer
  signature: :
  body: ((ReflexiveCofork.isColimitEquiv _ _).symm (colimit.isColimit F)).coconePointUniqueUpToIso
    (colimit.isColimit _)

@[reassoc (attr := simp)]

中文:
定义 reflexiveCoequalizerIsoCoequalizer
  签名: :
  定义体: ((ReflexiveCofork.isColimitEquiv _ _).symm (colimit.isColimit F)).coconePointUniqueUpToIso
    (colimit.isColimit _)

@[reassoc (attr := simp)]

Depends on / 依赖: ReflexiveCofork, ReflexiveCofork.isColimitEquiv, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitEquiv, map_isIso
-/
def reflexiveCoequalizerIsoCoequalizer :
    colimit F ≅ coequalizer (F.map left) (F.map right) :=
  ((ReflexiveCofork.isColimitEquiv _ _).symm (colimit.isColimit F)).coconePointUniqueUpToIso
    (colimit.isColimit _)

@[reassoc (attr := simp)]
/--
lemma `ι_reflexiveCoequalizerIsoCoequalizer_hom` / 引理 `ι_reflexiveCoequalizerIsoCoequalizer_hom`

English:
lemma ι_reflexiveCoequalizerIsoCoequalizer_hom
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom
    ((ReflexiveCofork.isColimitEquiv F _).symm _) _ WalkingParallelPair.one

中文:
引理 ι_reflexiveCoequalizerIsoCoequalizer_hom
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom
    ((ReflexiveCofork.isColimitEquiv F _).symm _) _ WalkingParallelPair.one

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, ReflexiveCofork, ReflexiveCofork.isColimitEquiv, WalkingParallelPair, WalkingParallelPair.one, comp_coconePointUniqueUpToIso_hom, isColimitEquiv
-/
lemma ι_reflexiveCoequalizerIsoCoequalizer_hom :
    colimit.ι F zero ≫ (reflexiveCoequalizerIsoCoequalizer F).hom =
      coequalizer.π (F.map left) (F.map right) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    ((ReflexiveCofork.isColimitEquiv F _).symm _) _ WalkingParallelPair.one

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `π_reflexiveCoequalizerIsoCoequalizer_inv` / 引理 `π_reflexiveCoequalizerIsoCoequalizer_inv`

English:
lemma π_reflexiveCoequalizerIsoCoequalizer_inv
  proof: by
  rw [reflexiveCoequalizerIsoCoequalizer]
  simp only [colimit.comp_coconePointUniqueUpToIso_inv,
    Cofork.ofπ_ι_app, ReflexiveCofork.π, colimit.cocone_ι]

中文:
引理 π_reflexiveCoequalizerIsoCoequalizer_inv
  证明: by
  rw [reflexiveCoequalizerIsoCoequalizer]
  simp only [colimit.comp_coconePointUniqueUpToIso_inv,
    Cofork.ofπ_ι_app, ReflexiveCofork.π, colimit.cocone_ι]

Depends on / 依赖: Cofork, Cofork.of, ReflexiveCofork, colimit, colimit.cocone_, colimit.comp_coconePointUniqueUpToIso_inv, comp_coconePointUniqueUpToIso_inv, reflexiveCoequalizerIsoCoequalizer
-/
lemma π_reflexiveCoequalizerIsoCoequalizer_inv :
    coequalizer.π _ _ ≫ (reflexiveCoequalizerIsoCoequalizer F).inv = colimit.ι F _ := by
  rw [reflexiveCoequalizerIsoCoequalizer]
  simp only [colimit.comp_coconePointUniqueUpToIso_inv,
    Cofork.ofπ_ι_app, ReflexiveCofork.π, colimit.cocone_ι]

end

variable {A B : C} {f g : A ⟶ B} [IsReflexivePair f g] [h : HasCoequalizer f g]

/--
Instance `ofIsReflexivePair_hasColimit_of_hasCoequalizer` / 实例 `ofIsReflexivePair_hasColimit_of_hasCoequalizer`

English:
instance ofIsReflexivePair_hasColimit_of_hasCoequalizer
  signature: :
  body: .mpr h hasReflexiveCoequalizer_iff_hasCoequalizer _

中文:
实例 ofIsReflexivePair_hasColimit_of_hasCoequalizer
  签名: :
  定义体: .mpr h hasReflexiveCoequalizer_iff_hasCoequalizer _

Depends on / 依赖: hasReflexiveCoequalizer_iff_hasCoequalizer
-/
instance ofIsReflexivePair_hasColimit_of_hasCoequalizer :
    HasColimit (ofIsReflexivePair f g) :=
.mpr h hasReflexiveCoequalizer_iff_hasCoequalizer _

/--
Definition of `colimitOfIsReflexivePairIsoCoequalizer` / `colimitOfIsReflexivePairIsoCoequalizer` 的定义

English:
definition colimitOfIsReflexivePairIsoCoequalizer
  signature: :
  body: @reflexiveCoequalizerIsoCoequalizer _ _ (ofIsReflexivePair f g) h


@[reassoc (attr := simp)]

中文:
定义 colimitOfIsReflexivePairIsoCoequalizer
  签名: :
  定义体: @reflexiveCoequalizerIsoCoequalizer _ _ (ofIsReflexivePair f g) h


@[reassoc (attr := simp)]

Depends on / 依赖: ofIsReflexivePair, reflexiveCoequalizerIsoCoequalizer
-/
def colimitOfIsReflexivePairIsoCoequalizer :
    colimit (ofIsReflexivePair f g) ≅ coequalizer f g :=
  @reflexiveCoequalizerIsoCoequalizer _ _ (ofIsReflexivePair f g) h


@[reassoc (attr := simp)]
/--
lemma `ι_colimitOfIsReflexivePairIsoCoequalizer_hom` / 引理 `ι_colimitOfIsReflexivePairIsoCoequalizer_hom`

English:
lemma ι_colimitOfIsReflexivePairIsoCoequalizer_hom
  proof: @ι_reflexiveCoequalizerIsoCoequalizer_hom _ _ _ h

@[reassoc (attr := simp)]

中文:
引理 ι_colimitOfIsReflexivePairIsoCoequalizer_hom
  证明: @ι_reflexiveCoequalizerIsoCoequalizer_hom _ _ _ h

@[reassoc (attr := simp)]
-/
lemma ι_colimitOfIsReflexivePairIsoCoequalizer_hom :
    colimit.ι (ofIsReflexivePair f g) zero ≫ colimitOfIsReflexivePairIsoCoequalizer.hom =
      coequalizer.π f g := @ι_reflexiveCoequalizerIsoCoequalizer_hom _ _ _ h

@[reassoc (attr := simp)]
/--
lemma `π_colimitOfIsReflexivePairIsoCoequalizer_inv` / 引理 `π_colimitOfIsReflexivePairIsoCoequalizer_inv`

English:
lemma π_colimitOfIsReflexivePairIsoCoequalizer_inv
  proof: @π_reflexiveCoequalizerIsoCoequalizer_inv _ _ (ofIsReflexivePair f g) h

中文:
引理 π_colimitOfIsReflexivePairIsoCoequalizer_inv
  证明: @π_reflexiveCoequalizerIsoCoequalizer_inv _ _ (ofIsReflexivePair f g) h

Depends on / 依赖: ofIsReflexivePair
-/
lemma π_colimitOfIsReflexivePairIsoCoequalizer_inv :
    coequalizer.π f g ≫ colimitOfIsReflexivePairIsoCoequalizer.inv =
      colimit.ι (ofIsReflexivePair f g) zero :=
  @π_reflexiveCoequalizerIsoCoequalizer_inv _ _ (ofIsReflexivePair f g) h

end
end Limits

namespace Limits

open WalkingReflexivePair

variable {C : Type u} [Category.{v} C]

/--
theorem `hasReflexiveCoequalizers_iff` / 定理 `hasReflexiveCoequalizers_iff`

English:
theorem hasReflexiveCoequalizers_iff
  proof: ⟨fun _ => ⟨fun _ _ f g _ => (hasReflexiveCoequalizer_iff_hasCoequalizer
      (reflexivePair f g (commonSection f g))).1 inferInstance⟩,
    fun _ => ⟨inferInstance⟩⟩

中文:
定理 hasReflexiveCoequalizers_iff
  证明: ⟨fun _ => ⟨fun _ _ f g _ => (hasReflexiveCoequalizer_iff_hasCoequalizer
      (reflexivePair f g (commonSection f g))).1 inferInstance⟩,
    fun _ => ⟨inferInstance⟩⟩

Depends on / 依赖: commonSection, hasReflexiveCoequalizer_iff_hasCoequalizer, reflexivePair
-/
theorem hasReflexiveCoequalizers_iff :
    HasColimitsOfShape WalkingReflexivePair C ↔ HasReflexiveCoequalizers C :=
  ⟨fun _ => ⟨fun _ _ f g _ => (hasReflexiveCoequalizer_iff_hasCoequalizer
      (reflexivePair f g (commonSection f g))).1 inferInstance⟩,
    fun _ => ⟨inferInstance⟩⟩

end Limits

end CategoryTheory
