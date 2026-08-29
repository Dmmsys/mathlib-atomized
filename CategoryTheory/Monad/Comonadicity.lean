/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Equalizer
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Comonadicity theorems

We prove comonadicity theorems which can establish a given functor is comonadic. In particular, we
show three versions of Beck's comonadicity theorem, and the coreflexive (crude)
comonadicity theorem:

`F` is a comonadic left adjoint if it has a right adjoint, and:

* `C` has, `F` preserves and reflects `F`-split equalizers, see
  `CategoryTheory.Monad.comonadicOfHasPreservesReflectsFSplitEqualizers`
* `F` creates `F`-split coequalizers, see
  `CategoryTheory.Monad.comonadicOfCreatesFSplitEqualizers`
  (The converse of this is also shown, see
  `CategoryTheory.Monad.createsFSplitEqualizersOfComonadic`)
* `C` has and `F` preserves `F`-split equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`
* `C` has and `F` preserves coreflexive equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms`

This file has been adapted from `Mathlib/CategoryTheory/Monad/Monadicity.lean`.
Please try to keep them in sync.

## Tags

Beck, comonadicity, descent

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Comonad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `main_pair_coreflexive` / 实例 `main_pair_coreflexive`

English:
instance main_pair_coreflexive
  signature: (A : adj.toComonad.Coalgebra)
  body: by
  apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
  · rw [← G.map_comp, ← G.map_id]
    exact congr_arg G.map A.counit
  · rw [adj.right_triangle_components]
    rfl

中文:
实例 main_pair_coreflexive
  签名: (A : adj.toComonad.Coalgebra)
  定义体: by
  apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
  · rw [← G.map_comp, ← G.map_id]
    exact congr_arg G.map A.counit
  · rw [adj.right_triangle_components]
    rfl

Depends on / 依赖: A.counit, G.map, G.map_comp, G.map_id, IsCoreflexivePair, IsCoreflexivePair.mk, adj.counit.app, adj.right_triangle_components, congr_arg, counit, map_comp, map_id, right_triangle_components
-/
instance main_pair_coreflexive (A : adj.toComonad.Coalgebra) :
    IsCoreflexivePair (G.map A.a) (adj.unit.app (G.obj A.A)) := by
  apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
  · rw [← G.map_comp, ← G.map_id]
    exact congr_arg G.map A.counit
  · rw [adj.right_triangle_components]
    rfl

/--
Instance `main_pair_F_cosplit` / 实例 `main_pair_F_cosplit`

English:
instance main_pair_F_cosplit
  signature: (A : adj.toComonad.Coalgebra)
  body: ⟨_, _, ⟨beckSplitEqualizer A⟩⟩

中文:
实例 main_pair_F_cosplit
  签名: (A : adj.toComonad.Coalgebra)
  定义体: ⟨_, _, ⟨beckSplitEqualizer A⟩⟩

Depends on / 依赖: beckSplitEqualizer
-/
instance main_pair_F_cosplit (A : adj.toComonad.Coalgebra) :
    F.IsCosplitPair (G.map A.a)
      (adj.unit.app (G.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitEqualizer A⟩⟩

/--
Definition of `comparisonRightAdjointObj` / `comparisonRightAdjointObj` 的定义

English:
definition comparisonRightAdjointObj
  signature: (A : adj.toComonad.Coalgebra)
  body: equalizer (G.map A.a) (adj.unit.app _)

中文:
定义 comparisonRightAdjointObj
  签名: (A : adj.toComonad.Coalgebra)
  定义体: equalizer (G.map A.a) (adj.unit.app _)

Depends on / 依赖: G.map, adj.unit.app, equalizer
-/
def comparisonRightAdjointObj (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app _)] : C :=
  equalizer (G.map A.a) (adj.unit.app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
We have a bijection of homsets which will be used to construct the right adjoint to the comparison
functor.
-/
@[simps!]
/--
Definition of `comparisonRightAdjointHomEquiv` / `comparisonRightAdjointHomEquiv` 的定义

English:
definition comparisonRightAdjointHomEquiv
  signature: (A : adj.toComonad.Coalgebra) (B : C)
  body: by
        refine equalizer.lift (adj.homEquiv _ _ f.f) ?_
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, Adjunction.homEquiv_unit,
          Category.assoc, ← G.map_comp, ← f.h, comparison_obj_A, comparison_obj_a]
        rw [Functor.comp_map]; rw [Functor.map_comp]; rw [Adjunction.

中文:
定义 comparisonRightAdjointHomEquiv
  签名: (A : adj.toComonad.Coalgebra) (B : C)
  定义体: by
        refine equalizer.lift (adj.homEquiv _ _ f.f) ?_
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, Adjunction.homEquiv_unit,
          Category.assoc, ← G.map_comp, ← f.h, comparison_obj_A, comparison_obj_a]
        rw [Functor.comp_map]; rw [Functor.map_comp]; rw [Adjunction.

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.toComonad_coe, Adjunction.unit_naturality, Adjunction.unit_naturality_assoc, Category, Category.assoc, Functor, Functor.comp_map, Functor.comp_obj, Functor.map_comp, G.map_comp, adj.homEquiv, comp_map, comp_obj, comparison_obj_A, comparison_obj_a, equalizer, equalizer.lift, homEquiv
-/
def comparisonRightAdjointHomEquiv (A : adj.toComonad.Coalgebra) (B : C)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    ((comparison adj).obj B ⟶ A) ≃ (B ⟶ comparisonRightAdjointObj adj A) where
      toFun f := by
        refine equalizer.lift (adj.homEquiv _ _ f.f) ?_
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, Adjunction.homEquiv_unit,
          Category.assoc, ← G.map_comp, ← f.h, comparison_obj_A, comparison_obj_a]
        rw [Functor.comp_map]; rw [Functor.map_comp]; rw [Adjunction.unit_naturality_assoc]; rw [Adjunction.unit_naturality]
      invFun f := by
        refine ⟨(adj.homEquiv _ _).symm (f ≫ (equalizer.ι _ _)), (adj.homEquiv _ _).injective ?_⟩
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, comparison_obj_A, comparison_obj_a,
          Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
          Functor.comp_map, Adjunction.homEquiv_unit, Adjunction.unit_naturality_assoc,
          Adjunction.unit_naturality, Adjunction.right_triangle_components_assoc]
        congr 1
        exact (equalizer.condition _ _).symm
      left_inv f := by aesop
      right_inv f := by apply equalizer.hom_ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `rightAdjointComparison` / `rightAdjointComparison` 的定义

English:
definition rightAdjointComparison
  body: by
  refine
    Adjunction.rightAdjointOfEquiv (F := comparison adj)
      (G_obj := fun A => comparisonRightAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonRightAdjointHomEquiv
  · intro A B B' g h
    apply equalizer.hom_ext
    simp [Adjunction.homEquiv_unit]

#adaptation_note

中文:
定义 rightAdjointComparison
  定义体: by
  refine
    Adjunction.rightAdjointOfEquiv (F := comparison adj)
      (G_obj := fun A => comparisonRightAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonRightAdjointHomEquiv
  · intro A B B' g h
    apply equalizer.hom_ext
    simp [Adjunction.homEquiv_unit]

#adaptation_note

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.rightAdjointOfEquiv, G_obj, comparison, comparisonRightAdjointHomEquiv, comparisonRightAdjointObj, equalizer, equalizer.hom_ext, homEquiv_unit, hom_ext, rightAdjointOfEquiv
-/
def rightAdjointComparison
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    adj.toComonad.Coalgebra ⥤ C := by
  refine
    Adjunction.rightAdjointOfEquiv (F := comparison adj)
      (G_obj := fun A => comparisonRightAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonRightAdjointHomEquiv
  · intro A B B' g h
    apply equalizer.hom_ext
    simp [Adjunction.homEquiv_unit]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Provided we have the appropriate equalizers, we have an adjunction to the comparison functor.
-/
@[simps! counit]
/--
Definition of `comparisonAdjunction` / `comparisonAdjunction` 的定义

English:
definition comparisonAdjunction
  body: Adjunction.adjunctionOfEquivRight _ _

中文:
定义 comparisonAdjunction
  定义体: Adjunction.adjunctionOfEquivRight _ _

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivRight, adjunctionOfEquivRight
-/
def comparisonAdjunction
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    comparison adj ⊣ rightAdjointComparison adj :=
  Adjunction.adjunctionOfEquivRight _ _

variable {adj}

/--
theorem `comparisonAdjunction_counit_f_aux` / 定理 `comparisonAdjunction_counit_f_aux`

English:
theorem comparisonAdjunction_counit_f_aux
  proof: congr_arg (adj.homEquiv _ _).symm (Category.id_comp _)

中文:
定理 comparisonAdjunction_counit_f_aux
  证明: congr_arg (adj.homEquiv _ _).symm (Category.id_comp _)

Depends on / 依赖: Category, Category.id_comp, adj.homEquiv, congr_arg, homEquiv, id_comp
-/
theorem comparisonAdjunction_counit_f_aux
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f =
      (adj.homEquiv _ A.A).symm (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  congr_arg (adj.homEquiv _ _).symm (Category.id_comp _)

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a fork which is helpful for establishing comonadicity: the morphism from this fork to
the Beck equalizer is the counit for the adjunction on the comparison functor.
-/
@[simps! pt]
/--
Definition of `counitFork` / `counitFork` 的定义

English:
definition counitFork
  signature: (A : adj.toComonad.Coalgebra)
  body: Fork.ofι (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))))
    (by rw [← F.map_comp, equalizer.condition, F.map_comp])

@[simp]

中文:
定义 counitFork
  签名: (A : adj.toComonad.Coalgebra)
  定义体: Fork.ofι (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))))
    (by rw [← F.map_comp, equalizer.condition, F.map_comp])

@[simp]

Depends on / 依赖: F.map, F.map_comp, Fork.of, G.map, G.obj, adj.unit.app, condition, equalizer, equalizer.condition, map_comp
-/
def counitFork (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    Fork (F.map (G.map A.a)) (F.map (adj.unit.app (G.obj A.A))) :=
  Fork.ofι (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))))
    (by rw [← F.map_comp, equalizer.condition, F.map_comp])

@[simp]
/--
theorem `unitFork_ι` / 定理 `unitFork_ι`

English:
theorem unitFork_ι
  statement: (A : adj.toComonad.Coalgebra)
  proof: rfl

中文:
定理 unitFork_ι
  结论: (A : adj.toComonad.Coalgebra)
  证明: rfl
-/
theorem unitFork_ι (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    (counitFork A).ι = F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comparisonAdjunction_counit_f` / 定理 `comparisonAdjunction_counit_f`

English:
theorem comparisonAdjunction_counit_f
  proof: by
  simp [Adjunction.homEquiv_counit]

中文:
定理 comparisonAdjunction_counit_f
  证明: by
  simp [Adjunction.homEquiv_counit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, homEquiv_counit
-/
theorem comparisonAdjunction_counit_f
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f = (beckEqualizer A).lift (counitFork A) := by
  simp [Adjunction.homEquiv_counit]

variable (adj)

/-- The fork which describes the unit of the adjunction: the morphism from this fork to the
equalizer of this pair is the unit.
-/
@[simps!]
/--
Definition of `unitFork` / `unitFork` 的定义

English:
definition unitFork
  signature: (B : C)
  body: Fork.ofι (adj.unit.app B) (adj.unit_naturality _)

中文:
定义 unitFork
  签名: (B : C)
  定义体: Fork.ofι (adj.unit.app B) (adj.unit_naturality _)

Depends on / 依赖: Fork.of, adj.unit.app, adj.unit_naturality, unit_naturality
-/
def unitFork (B : C) :
    Fork (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B))) :=
  Fork.ofι (adj.unit.app B) (adj.unit_naturality _)

set_option backward.isDefEq.respectTransparency.types false in
variable {adj} in
/--
Definition of `counitLimitOfPreservesEqualizer` / `counitLimitOfPreservesEqualizer` 的定义

English:
definition counitLimitOfPreservesEqualizer
  signature: (A : adj.toComonad.Coalgebra)
  body: isLimitOfHasEqualizerOfPreservesLimit F _ _

中文:
定义 counitLimitOfPreservesEqualizer
  签名: (A : adj.toComonad.Coalgebra)
  定义体: isLimitOfHasEqualizerOfPreservesLimit F _ _
-/
def counitLimitOfPreservesEqualizer (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    [PreservesLimit (parallelPair (G.map A.a) (adj.unit.app (G.obj A.A))) F] :
    IsLimit (counitFork (G := G) A) :=
  isLimitOfHasEqualizerOfPreservesLimit F _ _

/--
Definition of `unitEqualizerOfCoreflectsEqualizer` / `unitEqualizerOfCoreflectsEqualizer` 的定义

English:
definition unitEqualizerOfCoreflectsEqualizer
  signature: (B : C)
  body: isLimitOfIsLimitForkMap F _ (beckEqualizer ((comparison adj).obj B))

instance
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    (B : C) : HasLimit (parallelPair
      (G.map (F.map (NatTrans.app adj.unit B)))
      (NatTrans.app adj.unit (G.obj (F.obj

中文:
定义 unitEqualizerOfCoreflectsEqualizer
  签名: (B : C)
  定义体: isLimitOfIsLimitForkMap F _ (beckEqualizer ((comparison adj).obj B))

instance
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    (B : C) : HasLimit (parallelPair
      (G.map (F.map (NatTrans.app adj.unit B)))
      (NatTrans.app adj.unit (G.obj (F.obj
-/
def unitEqualizerOfCoreflectsEqualizer (B : C)
    [ReflectsLimit (parallelPair (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B)))) F] :
    IsLimit (unitFork (adj := adj) B) :=
  isLimitOfIsLimitForkMap F _ (beckEqualizer ((comparison adj).obj B))

instance
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    (B : C) : HasLimit (parallelPair
      (G.map (F.map (NatTrans.app adj.unit B)))
      (NatTrans.app adj.unit (G.obj (F.obj B)))) :=
inferInstanceAs HasEqualizer
    (G.map ((comparison adj).obj B).a)
    (adj.unit.app (G.obj ((comparison adj).obj B).A))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `comparisonAdjunction_unit_app` / 定理 `comparisonAdjunction_unit_app`

English:
theorem comparisonAdjunction_unit_app
  proof: by
  apply equalizer.hom_ext
  change
    equalizer.lift ((adj.homEquiv B _) (𝟙 _)) _ ≫ equalizer.ι _ _ =
      equalizer.lift _ _ ≫ equalizer.ι _ _
  simp [Adjunction.homEquiv_unit]

中文:
定理 comparisonAdjunction_unit_app
  证明: by
  apply equalizer.hom_ext
  change
    equalizer.lift ((adj.homEquiv B _) (𝟙 _)) _ ≫ equalizer.ι _ _ =
      equalizer.lift _ _ ≫ equalizer.ι _ _
  simp [Adjunction.homEquiv_unit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, adj.homEquiv, equalizer, equalizer.hom_ext, equalizer.lift, homEquiv, homEquiv_unit, hom_ext
-/
theorem comparisonAdjunction_unit_app
    [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] (B : C) :
    (comparisonAdjunction adj).unit.app B = limit.lift _ (unitFork adj B) := by
  apply equalizer.hom_ext
  change
    equalizer.lift ((adj.homEquiv B _) (𝟙 _)) _ ≫ equalizer.ι _ _ =
      equalizer.lift _ _ ≫ equalizer.ι _ _
  simp [Adjunction.homEquiv_unit]

end ComonadicityInternal

open CategoryTheory Adjunction Comonad ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.defeqAttrib.useBackward true in
variable (G) in
/--
If `F` is comonadic, it creates limits of `F`-cosplit pairs. This is the "boring" direction of
Beck's comonadicity theorem, the converse is given in `comonadicOfCreatesFSplitEqualizers`.
-/
@[instance_reducible]
/--
Definition of `createsFSplitEqualizersOfComonadic` / `createsFSplitEqualizersOfComonadic` 的定义

English:
definition createsFSplitEqualizersOfComonadic
  signature: [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A ⟶ B)
  body: by
  apply +allowSynthFailures comonadicCreatesLimitOfPreservesLimit
  all_goals
    apply @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

中文:
定义 createsFSplitEqualizersOfComonadic
  签名: [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A ⟶ B)
  定义体: by
  apply +allowSynthFailures comonadicCreatesLimitOfPreservesLimit
  all_goals
    apply @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

Depends on / 依赖: all_goals, allowSynthFailures, comonadicCreatesLimitOfPreservesLimit, diagramIsoParallelPair, infer_instance, preservesLimit_of_iso_diagram
-/
def createsFSplitEqualizersOfComonadic [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A ⟶ B)
    [F.IsCosplitPair f g] : CreatesLimit (parallelPair f g) F := by
  apply +allowSynthFailures comonadicCreatesLimitOfPreservesLimit
  all_goals
    apply @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckComonadicity

/--
Definition of `HasEqualizerOfIsCosplitPair` / `HasEqualizerOfIsCosplitPair` 的定义

English:
class HasEqualizerOfIsCosplitPair
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], HasEqualizer f g

中文:
类 HasEqualizerOfIsCosplitPair
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], HasEqualizer f g
-/
class HasEqualizerOfIsCosplitPair (F : C ⥤ D) : Prop where
  /-- If `f, g` is an `F`-cosplit pair, then they have an equalizer. -/
  out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], HasEqualizer f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasEqualizerOfIsCosplitPair
  signature: F] : forall (A
  body: fun _ => HasEqualizerOfIsCosplitPair.out F _ _

中文:
实例 [HasEqualizerOfIsCosplitPair
  签名: F] : 对任意 (A
  定义体: fun _ => HasEqualizerOfIsCosplitPair.out F _ _

Depends on / 依赖: HasEqualizerOfIsCosplitPair, HasEqualizerOfIsCosplitPair.out
-/
instance [HasEqualizerOfIsCosplitPair F] : forall (A : Coalgebra adj.toComonad),
    HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A)) :=
  fun _ => HasEqualizerOfIsCosplitPair.out F _ _

/--
Definition of `PreservesLimitOfIsCosplitPair` / `PreservesLimitOfIsCosplitPair` 的定义

English:
class PreservesLimitOfIsCosplitPair
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], PreservesLimit (parallelPair f g) F

中文:
类 PreservesLimitOfIsCosplitPair
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], PreservesLimit (parallelPair f g) F
-/
class PreservesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` preserves limits of `parallelPair f g`. -/
  out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], PreservesLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [PreservesLimitOfIsCosplitPair F] :
    PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCosplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimitOfIsCosplitPair
  signature: F] : forall (A
  body: fun _ => PreservesLimitOfIsCosplitPair.out _ _

中文:
实例 [PreservesLimitOfIsCosplitPair
  签名: F] : 对任意 (A
  定义体: fun _ => PreservesLimitOfIsCosplitPair.out _ _

Depends on / 依赖: PreservesLimitOfIsCosplitPair, PreservesLimitOfIsCosplitPair.out
-/
instance [PreservesLimitOfIsCosplitPair F] : forall (A : Coalgebra adj.toComonad),
    PreservesLimit (parallelPair (G.map A.a) (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => PreservesLimitOfIsCosplitPair.out _ _

/--
Definition of `ReflectsLimitOfIsCosplitPair` / `ReflectsLimitOfIsCosplitPair` 的定义

English:
class ReflectsLimitOfIsCosplitPair
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], ReflectsLimit (parallelPair f g) F

中文:
类 ReflectsLimitOfIsCosplitPair
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], ReflectsLimit (parallelPair f g) F
-/
class ReflectsLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` reflects limits for `parallelPair f g`. -/
  out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], ReflectsLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [ReflectsLimitOfIsCosplitPair F] :
    ReflectsLimit (parallelPair f g) F := ReflectsLimitOfIsCosplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ReflectsLimitOfIsCosplitPair
  signature: F] : forall (A
  body: fun _ => ReflectsLimitOfIsCosplitPair.out _ _

中文:
实例 [ReflectsLimitOfIsCosplitPair
  签名: F] : 对任意 (A
  定义体: fun _ => ReflectsLimitOfIsCosplitPair.out _ _

Depends on / 依赖: Limits, Limits.Types.limit_ext, ReflectsLimitOfIsCosplitPair, ReflectsLimitOfIsCosplitPair.out, limit_ext
-/
instance [ReflectsLimitOfIsCosplitPair F] : forall (A : Coalgebra adj.toComonad),
    ReflectsLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => ReflectsLimitOfIsCosplitPair.out _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- To show `F` is a comonadic left adjoint, we can show it preserves and reflects `F`-split
equalizers, and `C` has them.
-/
@[instance_reducible]
/--
Definition of `comonadicOfHasPreservesReflectsFSplitEqualizers` / `comonadicOfHasPreservesReflectsFSplitEqualizers` 的定义

English:
definition comonadicOfHasPreservesReflectsFSplitEqualizers
  signature: [HasEqualizerOfIsCosplitPair F]
  body: G
  adj := adj
  eqv := by
    have : forall (X : Coalgebra adj.toComonad), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
      

中文:
定义 comonadicOfHasPreservesReflectsFSplitEqualizers
  签名: [HasEqualizerOfIsCosplitPair F]
  定义体: G
  adj := adj
  eqv := by
    have : forall (X : Coalgebra adj.toComonad), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
      
-/
def comonadicOfHasPreservesReflectsFSplitEqualizers [HasEqualizerOfIsCosplitPair F]
    [PreservesLimitOfIsCosplitPair F] [ReflectsLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F where
  R := G
  adj := adj
  eqv := by
    have : forall (X : Coalgebra adj.toComonad), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        change
          IsIso
            (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
                (counitLimitOfPreservesEqualizer X)).inv
        exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv
    have : forall (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      · infer_instance
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      let _ :
        F.IsCosplitPair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) :=
        ComonadicityInternal.main_pair_F_cosplit _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

/--
Definition of `CreatesLimitOfIsCosplitPair` / `CreatesLimitOfIsCosplitPair` 的定义

English:
class CreatesLimitOfIsCosplitPair
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], CreatesLimit (parallelPair f g) F

中文:
类 CreatesLimitOfIsCosplitPair
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], CreatesLimit (parallelPair f g) F

Depends on / 依赖: Limits, Limits.Types.limit_ext, limit_ext
-/
class CreatesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` creates limits of `parallelPair f g`. -/
  out : forall {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], CreatesLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [CreatesLimitOfIsCosplitPair F] :
    CreatesLimit (parallelPair f g) F := CreatesLimitOfIsCosplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CreatesLimitOfIsCosplitPair
  signature: F] : forall (A
  body: fun _ => CreatesLimitOfIsCosplitPair.out _ _

中文:
实例 [CreatesLimitOfIsCosplitPair
  签名: F] : 对任意 (A
  定义体: fun _ => CreatesLimitOfIsCosplitPair.out _ _

Depends on / 依赖: CreatesLimitOfIsCosplitPair, CreatesLimitOfIsCosplitPair.out
-/
instance [CreatesLimitOfIsCosplitPair F] : forall (A : Coalgebra adj.toComonad),
    CreatesLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => CreatesLimitOfIsCosplitPair.out _ _

/--
Beck's comonadicity theorem. If `F` has a right adjoint and creates equalizers of `F`-cosplit pairs,
then it is comonadic.
This is the converse of `createsFSplitEqualizersOfComonadic`.
-/
@[instance_reducible]
/--
Definition of `comonadicOfCreatesFSplitEqualizers` / `comonadicOfCreatesFSplitEqualizers` 的定义

English:
definition comonadicOfCreatesFSplitEqualizers
  signature: [CreatesLimitOfIsCosplitPair F]
  body: by
  have I {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] : HasLimit (parallelPair f g ⋙ F) := by
    rw [hasLimit_iff_of_iso (diagramIsoParallelPair _)]
exact inferInstanceAs HasEqualizer (F.map f) (F.map g)
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ => hasLimit_of_created (parallelPair _ _) F⟩

中文:
定义 comonadicOfCreatesFSplitEqualizers
  签名: [CreatesLimitOfIsCosplitPair F]
  定义体: by
  have I {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] : HasLimit (parallelPair f g ⋙ F) := by
    rw [hasLimit_iff_of_iso (diagramIsoParallelPair _)]
exact inferInstanceAs HasEqualizer (F.map f) (F.map g)
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ => hasLimit_of_created (parallelPair _ _) F⟩

Depends on / 依赖: F.IsCosplitPair, F.map, HasEqualizer, HasEqualizerOfIsCosplitPair, HasLimit, IsCosplitPair, PreservesLimitOfIsCosplitPair, ReflectsLimitOfIsCosplitPair, comonadicOfHasPreservesReflectsFSplitEqualizers, diagramIsoParallelPair, hasLimit_iff_of_iso, hasLimit_of_created, infer_instance, intros, parallelPair
-/
def comonadicOfCreatesFSplitEqualizers [CreatesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  have I {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] : HasLimit (parallelPair f g ⋙ F) := by
    rw [hasLimit_iff_of_iso (diagramIsoParallelPair _)]
exact inferInstanceAs HasEqualizer (F.map f) (F.map g)
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ => hasLimit_of_created (parallelPair _ _) F⟩
  have : PreservesLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  have : ReflectsLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  exact comonadicOfHasPreservesReflectsFSplitEqualizers adj

/-- An alternate version of Beck's comonadicity theorem. If `F` reflects isomorphisms, preserves
equalizers of `F`-cosplit pairs and `C` has equalizers of `F`-cosplit pairs, then it is comonadic.
-/
@[instance_reducible]
/--
Definition of `comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms` / `comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms` 的定义

English:
definition comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
  signature: [F.ReflectsIsomorphisms]
  body: by
  have : ReflectsLimitOfIsCosplitPair F := ⟨fun f g _ => by
    have := HasEqualizerOfIsCosplitPair.out F f g
    apply reflectsLimit_of_reflectsIsomorphisms⟩
  apply comonadicOfHasPreservesReflectsFSplitEqualizers adj

中文:
定义 comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms
  签名: [F.ReflectsIsomorphisms]
  定义体: by
  have : ReflectsLimitOfIsCosplitPair F := ⟨fun f g _ => by
    have := HasEqualizerOfIsCosplitPair.out F f g
    apply reflectsLimit_of_reflectsIsomorphisms⟩
  apply comonadicOfHasPreservesReflectsFSplitEqualizers adj

Depends on / 依赖: HasEqualizerOfIsCosplitPair, HasEqualizerOfIsCosplitPair.out, ReflectsLimitOfIsCosplitPair, comonadicOfHasPreservesReflectsFSplitEqualizers, reflectsLimit_of_reflectsIsomorphisms
-/
def comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms [F.ReflectsIsomorphisms]
    [HasEqualizerOfIsCosplitPair F] [PreservesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  have : ReflectsLimitOfIsCosplitPair F := ⟨fun f g _ => by
    have := HasEqualizerOfIsCosplitPair.out F f g
    apply reflectsLimit_of_reflectsIsomorphisms⟩
  apply comonadicOfHasPreservesReflectsFSplitEqualizers adj

end BeckComonadicity

section CoreflexiveComonadicity

variable [HasCoreflexiveEqualizers C] [F.ReflectsIsomorphisms]

/--
Definition of `PreservesLimitOfIsCoreflexivePair` / `PreservesLimitOfIsCoreflexivePair` 的定义

English:
class PreservesLimitOfIsCoreflexivePair
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - out : forall ⦃A B⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F

中文:
类 PreservesLimitOfIsCoreflexivePair
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - out : 对任意 ⦃A B⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F
-/
class PreservesLimitOfIsCoreflexivePair (F : C ⥤ D) where
  /-- `f, g` is a coreflexive pair, then `F` preserves limits of `parallelPair f g`. -/
  out : forall ⦃A B⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F

instance {A B} (f g : A ⟶ B) [IsCoreflexivePair f g] [PreservesLimitOfIsCoreflexivePair F] :
    PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCoreflexivePair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimitOfIsCoreflexivePair
  signature: F] : forall X : Coalgebra adj.toComonad,
  body: fun _ => PreservesLimitOfIsCoreflexivePair.out _ _

中文:
实例 [PreservesLimitOfIsCoreflexivePair
  签名: F] : 对任意 X : Coalgebra adj.toComonad,
  定义体: fun _ => PreservesLimitOfIsCoreflexivePair.out _ _

Depends on / 依赖: PreservesLimitOfIsCoreflexivePair, PreservesLimitOfIsCoreflexivePair.out
-/
instance [PreservesLimitOfIsCoreflexivePair F] : forall X : Coalgebra adj.toComonad,
    PreservesLimit (parallelPair (G.map X.a)
      (NatTrans.app adj.unit (G.obj X.A))) F :=
  fun _ => PreservesLimitOfIsCoreflexivePair.out _ _

variable [PreservesLimitOfIsCoreflexivePair F]

set_option backward.isDefEq.respectTransparency.types false in
/-- Coreflexive (crude) comonadicity theorem. If `F` has a right adjoint, `C` has and `F` preserves
coreflexive equalizers and `F` reflects isomorphisms, then `F` is comonadic.
-/
@[instance_reducible]
/--
Definition of `comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms` / `comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms` 的定义

English:
definition comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
  signature: :
  body: G
  adj := adj
  eqv := by
    have : forall (X : adj.toComonad.Coalgebra), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).

中文:
定义 comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
  签名: :
  定义体: G
  adj := adj
  eqv := by
    have : forall (X : adj.toComonad.Coalgebra), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).
-/
def comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms :
    ComonadicLeftAdjoint F where
  R := G
  adj := adj
  eqv := by
    have : forall (X : adj.toComonad.Coalgebra), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        exact (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
          (counitLimitOfPreservesEqualizer X)).isIso_inv
    have : forall (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      · infer_instance
      have : IsCoreflexivePair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) := by
        apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
        · rw [← G.map_comp, ← G.map_id]
          exact congr_arg G.map (adj.left_triangle_components Y)
        · rw [← G.map_id]
          simp
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      apply reflectsLimit_of_reflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

end CoreflexiveComonadicity

end

end Comonad

end CategoryTheory
