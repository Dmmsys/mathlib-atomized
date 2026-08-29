/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Coequalizer
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a left adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`
* `G` creates `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers`
  (The converse of this is also shown, see
  `CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms`

This file has been adapted to `Mathlib/CategoryTheory/Monad/Comonadicity.lean`.
Please try to keep them in sync.

## Tags

Beck, monadicity, descent

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `main_pair_reflexive` / 实例 `main_pair_reflexive`

English:
instance main_pair_reflexive
  signature: (A : adj.toMonad.Algebra)
  body: by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg F.map A.unit
  · dsimp
    rw [adj.left_triangle_components]

中文:
实例 main_pair_reflexive
  签名: (A : adj.toMonad.Algebra)
  定义体: by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg F.map A.unit
  · dsimp
    rw [adj.left_triangle_components]

Depends on / 依赖: A.unit, F.map, F.map_comp, F.map_id, IsReflexivePair, IsReflexivePair.mk, adj.left_triangle_components, adj.unit.app, congr_arg, left_triangle_components, map_comp, map_id
-/
instance main_pair_reflexive (A : adj.toMonad.Algebra) :
    IsReflexivePair (F.map A.a) (adj.counit.app (F.obj A.A)) := by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg F.map A.unit
  · dsimp
    rw [adj.left_triangle_components]

/--
Instance `main_pair_G_split` / 实例 `main_pair_G_split`

English:
instance main_pair_G_split
  signature: (A : adj.toMonad.Algebra)
  body: ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩

中文:
实例 main_pair_G_split
  签名: (A : adj.toMonad.Algebra)
  定义体: ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩

Depends on / 依赖: beckSplitCoequalizer
-/
instance main_pair_G_split (A : adj.toMonad.Algebra) :
    G.IsSplitPair (F.map A.a)
      (adj.counit.app (F.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩

/--
Definition of `comparisonLeftAdjointObj` / `comparisonLeftAdjointObj` 的定义

English:
definition comparisonLeftAdjointObj
  signature: (A : adj.toMonad.Algebra)
  body: coequalizer (F.map A.a) (adj.counit.app _)

中文:
定义 comparisonLeftAdjointObj
  签名: (A : adj.toMonad.Algebra)
  定义体: coequalizer (F.map A.a) (adj.counit.app _)

Depends on / 依赖: F.map, adj.counit.app, coequalizer, counit
-/
def comparisonLeftAdjointObj (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps!]
/--
Definition of `comparisonLeftAdjointHomEquiv` / `comparisonLeftAdjointHomEquiv` 的定义

English:
definition comparisonLeftAdjointHomEquiv
  signature: (A : adj.toMonad.Algebra) (B : D)
  body: calc
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine (adj.homEquiv _ _).subtypeEquiv ?_
      intro f
      rw [← (a

中文:
定义 comparisonLeftAdjointHomEquiv
  签名: (A : adj.toMonad.Algebra) (B : D)
  定义体: calc
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine (adj.homEquiv _ _).subtypeEquiv ?_
      intro f
      rw [← (a

Depends on / 依赖: Adjunction, Adjunction.homEquiv_naturality_left, Cofork, Cofork.IsColimit.homIso, F.map, F.map_comp, F.obj, G.map, G.map_comp, G.obj, IsColimit, adj.counit.app, adj.homEquiv, adj.homEquiv_unit, adj.right_triangle_components_assoc, colimit, colimit.isColimit, comparisonLeftAdjointObj, counit, eq_iff
-/
def comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine (adj.homEquiv _ _).subtypeEquiv ?_
      intro f
      rw [← (adj.homEquiv _ _).injective.eq_iff]; rw [Adjunction.homEquiv_naturality_left]; rw [adj.homEquiv_unit]; rw [adj.homEquiv_unit]; rw [G.map_comp]
      dsimp
      rw [adj.right_triangle_components_assoc]; rw [← G.map_comp]; rw [F.map_comp]; rw [Category.assoc]; rw [adj.counit_naturality]; rw [adj.left_triangle_components_assoc]
      apply eq_comm
    _ ≃ (A ⟶ (comparison adj).obj B) :=
      { toFun := fun g =>
          { f := _
            h := g.prop }
        invFun := fun f => ⟨f.f, f.h⟩ }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `leftAdjointComparison` / `leftAdjointComparison` 的定义

English:
definition leftAdjointComparison
  body: by
  refine
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    simp [Cofork.IsColimit.homIso, Adjunction.homEquiv_unit]

中文:
定义 leftAdjointComparison
  定义体: by
  refine
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    simp [Cofork.IsColimit.homIso, Adjunction.homEquiv_unit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, Adjunction.leftAdjointOfEquiv, Cofork, Cofork.IsColimit.homIso, F_obj, IsColimit, comparison, comparisonLeftAdjointHomEquiv, comparisonLeftAdjointObj, homEquiv_unit, homIso, leftAdjointOfEquiv
-/
def leftAdjointComparison
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    adj.toMonad.Algebra ⥤ D := by
  refine
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    simp [Cofork.IsColimit.homIso, Adjunction.homEquiv_unit]

/-- Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps! counit]
/--
Definition of `comparisonAdjunction` / `comparisonAdjunction` 的定义

English:
definition comparisonAdjunction
  body: Adjunction.adjunctionOfEquivLeft _ _

中文:
定义 comparisonAdjunction
  定义体: Adjunction.adjunctionOfEquivLeft _ _

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivLeft, adjunctionOfEquivLeft
-/
def comparisonAdjunction
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    leftAdjointComparison adj ⊣ comparison adj :=
  Adjunction.adjunctionOfEquivLeft _ _

variable {adj}

/--
theorem `comparisonAdjunction_unit_f_aux` / 定理 `comparisonAdjunction_unit_f_aux`

English:
theorem comparisonAdjunction_unit_f_aux
  proof: congr_arg (adj.homEquiv _ _) (Category.comp_id _)

中文:
定理 comparisonAdjunction_unit_f_aux
  证明: congr_arg (adj.homEquiv _ _) (Category.comp_id _)

Depends on / 依赖: Category, Category.comp_id, adj.homEquiv, comp_id, congr_arg, homEquiv
-/
theorem comparisonAdjunction_unit_f_aux
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f =
      adj.homEquiv A.A _
        (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps! pt]
/--
Definition of `unitCofork` / `unitCofork` 的定义

English:
definition unitCofork
  signature: (A : adj.toMonad.Algebra)
  body: Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by rw [← G.map_comp, coequalizer.condition, G.map_comp])

中文:
定义 unitCofork
  签名: (A : adj.toMonad.Algebra)
  定义体: Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by rw [← G.map_comp, coequalizer.condition, G.map_comp])

Depends on / 依赖: Cofork, Cofork.of, F.map, F.obj, G.map, G.map_comp, adj.counit.app, coequalizer, coequalizer.condition, condition, counit, map_comp
-/
def unitCofork (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.A))) :=
  Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by rw [← G.map_comp, coequalizer.condition, G.map_comp])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `unitCofork_π` / 定理 `unitCofork_π`

English:
theorem unitCofork_π
  statement: (A : adj.toMonad.Algebra)
  proof: rfl

中文:
定理 unitCofork_π
  结论: (A : adj.toMonad.Algebra)
  证明: rfl
-/
theorem unitCofork_π (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (unitCofork A).π = G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comparisonAdjunction_unit_f` / 定理 `comparisonAdjunction_unit_f`

English:
theorem comparisonAdjunction_unit_f
  proof: by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux]; rw [← adj.homEquiv_naturality_left A.a]; rw [coequalizer.condition]; rw [adj.homEquiv_naturality_right]; rw [adj.homEquiv_un

中文:
定理 comparisonAdjunction_unit_f
  证明: by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux]; rw [← adj.homEquiv_naturality_left A.a]; rw [coequalizer.condition]; rw [adj.homEquiv_naturality_right]; rw [adj.homEquiv_un

Depends on / 依赖: Category, Category.assoc, Cofork, Cofork.IsColimit, IsColimit, Limits, Limits.Cofork.IsColimit.hom_ext, adj.homEquiv_naturality_left, adj.homEquiv_naturality_right, adj.homEquiv_unit, adj.right_triangle_components_assoc, beckCoequalizer, coequalizer, coequalizer.condition, comparisonAdjunction_unit_f_aux, condition, homEquiv_naturality_left, homEquiv_naturality_right, homEquiv_unit, hom_ext
-/
theorem comparisonAdjunction_unit_f
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f = (beckCoequalizer A).desc (unitCofork A) := by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux]; rw [← adj.homEquiv_naturality_left A.a]; rw [coequalizer.condition]; rw [adj.homEquiv_naturality_right]; rw [adj.homEquiv_unit]; rw [Category.assoc]
  apply adj.right_triangle_components_assoc

variable (adj)

/-- The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps!]
/--
Definition of `counitCofork` / `counitCofork` 的定义

English:
definition counitCofork
  signature: (B : D)
  body: Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)

中文:
定义 counitCofork
  签名: (B : D)
  定义体: Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)

Depends on / 依赖: Cofork, Cofork.of, adj.counit.app, adj.counit_naturality, counit, counit_naturality
-/
def counitCofork (B : D) :
    Cofork (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)

set_option backward.isDefEq.respectTransparency.types false in
variable {adj} in
/--
Definition of `unitColimitOfPreservesCoequalizer` / `unitColimitOfPreservesCoequalizer` 的定义

English:
definition unitColimitOfPreservesCoequalizer
  signature: (A : adj.toMonad.Algebra)
  body: isColimitOfHasCoequalizerOfPreservesColimit G _ _

中文:
定义 unitColimitOfPreservesCoequalizer
  签名: (A : adj.toMonad.Algebra)
  定义体: isColimitOfHasCoequalizerOfPreservesColimit G _ _
-/
def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app (F.obj A.A))) G] :
    IsColimit (unitCofork (G := G) A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _

/--
Definition of `counitCoequalizerOfReflectsCoequalizer` / `counitCoequalizerOfReflectsCoequalizer` 的定义

English:
definition counitCoequalizerOfReflectsCoequalizer
  signature: (B : D)
  body: isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))

instance
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    (B : D) : HasColimit (parallelPair
      (F.map (G.map (NatTrans.app adj.counit B)))
      (NatTrans.app adj.counit

中文:
定义 counitCoequalizerOfReflectsCoequalizer
  签名: (B : D)
  定义体: isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))

instance
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    (B : D) : HasColimit (parallelPair
      (F.map (G.map (NatTrans.app adj.counit B)))
      (NatTrans.app adj.counit
-/
def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit (parallelPair (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B)))) G] :
    IsColimit (counitCofork (adj := adj) B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))

instance
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    (B : D) : HasColimit (parallelPair
      (F.map (G.map (NatTrans.app adj.counit B)))
      (NatTrans.app adj.counit (F.obj (G.obj B)))) :=
inferInstanceAs HasCoequalizer
    (F.map ((comparison adj).obj B).a)
    (adj.counit.app (F.obj ((comparison adj).obj B).A))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comparisonAdjunction_counit_app` / 定理 `comparisonAdjunction_counit_app`

English:
theorem comparisonAdjunction_counit_app
  proof: by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp [Adjunction.homEquiv_counit]

中文:
定理 comparisonAdjunction_counit_app
  证明: by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp [Adjunction.homEquiv_counit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, adj.homEquiv, coequalizer, coequalizer.desc, coequalizer.hom_ext, homEquiv, homEquiv_counit, hom_ext
-/
theorem comparisonAdjunction_counit_app
    [forall A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) :
    (comparisonAdjunction adj).counit.app B = colimit.desc _ (counitCofork adj B) := by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp [Adjunction.homEquiv_counit]

end MonadicityInternal

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

set_option backward.defeqAttrib.useBackward true in
variable (G) in
/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadicOfCreatesGSplitCoequalizers`.
-/
@[instance_reducible]
/--
Definition of `createsGSplitCoequalizersOfMonadic` / `createsGSplitCoequalizersOfMonadic` 的定义

English:
definition createsGSplitCoequalizersOfMonadic
  signature: [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
  body: by
  apply +allowSynthFailures monadicCreatesColimitOfPreservesColimit
    -- Porting note: oddly +allowSynthFailures had no effect here and below
  all_goals
    apply @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

中文:
定义 createsGSplitCoequalizersOfMonadic
  签名: [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
  定义体: by
  apply +allowSynthFailures monadicCreatesColimitOfPreservesColimit
    -- Porting note: oddly +allowSynthFailures had no effect here and below
  all_goals
    apply @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

Depends on / 依赖: allowSynthFailures, monadicCreatesColimitOfPreservesColimit
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G := by
  apply +allowSynthFailures monadicCreatesColimitOfPreservesColimit
    -- Porting note: oddly +allowSynthFailures had no effect here and below
  all_goals
    apply @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckMonadicity

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- When this is fixed the proofs below that struggle with instances should be reviewed.
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
/--
Definition of `HasCoequalizerOfIsSplitPair` / `HasCoequalizerOfIsSplitPair` 的定义

English:
class HasCoequalizerOfIsSplitPair
  parameters: (G : D ⥤ C)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

中文:
类 HasCoequalizerOfIsSplitPair
  参数: (G : D ⥤ C)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

Depends on / 依赖: HasCoequalizerOfIsSplitPair, HasCoequalizerOfIsSplitPair.out
-/
class HasCoequalizerOfIsSplitPair (G : D ⥤ C) : Prop where
  out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

-- Porting note: cannot find synth order
-- instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [HasCoequalizerOfIsSplitPair G] :
-- HasCoequalizer f g := HasCoequalizerOfIsSplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasCoequalizerOfIsSplitPair
  signature: G] : forall (A
  body: fun _ => HasCoequalizerOfIsSplitPair.out G _ _

中文:
实例 [HasCoequalizerOfIsSplitPair
  签名: G] : 对任意 (A
  定义体: fun _ => HasCoequalizerOfIsSplitPair.out G _ _

Depends on / 依赖: HasCoequalizerOfIsSplitPair, HasCoequalizerOfIsSplitPair.out
-/
instance [HasCoequalizerOfIsSplitPair G] : forall (A : Algebra adj.toMonad),
    HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A)) :=
  fun _ => HasCoequalizerOfIsSplitPair.out G _ _

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
/--
Definition of `PreservesColimitOfIsSplitPair` / `PreservesColimitOfIsSplitPair` 的定义

English:
class PreservesColimitOfIsSplitPair
  parameters: (G : D ⥤ C)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G

中文:
类 PreservesColimitOfIsSplitPair
  参数: (G : D ⥤ C)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G
-/
class PreservesColimitOfIsSplitPair (G : D ⥤ C) where
  out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [PreservesColimitOfIsSplitPair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsSplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesColimitOfIsSplitPair
  signature: G] : forall (A
  body: fun _ => PreservesColimitOfIsSplitPair.out _ _

中文:
实例 [PreservesColimitOfIsSplitPair
  签名: G] : 对任意 (A
  定义体: fun _ => PreservesColimitOfIsSplitPair.out _ _

Depends on / 依赖: PreservesColimitOfIsSplitPair, PreservesColimitOfIsSplitPair.out
-/
instance [PreservesColimitOfIsSplitPair G] : forall (A : Algebra adj.toMonad),
    PreservesColimit (parallelPair (F.map A.a) (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => PreservesColimitOfIsSplitPair.out _ _

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] :
/--
Definition of `ReflectsColimitOfIsSplitPair` / `ReflectsColimitOfIsSplitPair` 的定义

English:
class ReflectsColimitOfIsSplitPair
  parameters: (G : D ⥤ C)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G

中文:
类 ReflectsColimitOfIsSplitPair
  参数: (G : D ⥤ C)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G
-/
class ReflectsColimitOfIsSplitPair (G : D ⥤ C) where
  out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [ReflectsColimitOfIsSplitPair G] :
    ReflectsColimit (parallelPair f g) G := ReflectsColimitOfIsSplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ReflectsColimitOfIsSplitPair
  signature: G] : forall (A
  body: fun _ => ReflectsColimitOfIsSplitPair.out _ _

中文:
实例 [ReflectsColimitOfIsSplitPair
  签名: G] : 对任意 (A
  定义体: fun _ => ReflectsColimitOfIsSplitPair.out _ _

Depends on / 依赖: ReflectsColimitOfIsSplitPair, ReflectsColimitOfIsSplitPair.out
-/
instance [ReflectsColimitOfIsSplitPair G] : forall (A : Algebra adj.toMonad),
    ReflectsColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => ReflectsColimitOfIsSplitPair.out _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `D` has them.
-/
@[instance_reducible]
/--
Definition of `monadicOfHasPreservesReflectsGSplitCoequalizers` / `monadicOfHasPreservesReflectsGSplitCoequalizers` 的定义

English:
definition monadicOfHasPreservesReflectsGSplitCoequalizers
  signature: [HasCoequalizerOfIsSplitPair G]
  body: F
  adj := adj
  eqv := by
    have : forall (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [compar

中文:
定义 monadicOfHasPreservesReflectsGSplitCoequalizers
  签名: [HasCoequalizerOfIsSplitPair G]
  定义体: F
  adj := adj
  eqv := by
    have : forall (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [compar
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers [HasCoequalizerOfIsSplitPair G]
    [PreservesColimitOfIsSplitPair G] [ReflectsColimitOfIsSplitPair G] :
    MonadicRightAdjoint G where
  L := F
  adj := adj
  eqv := by
    have : forall (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        change
          IsIso
            (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
                (unitColimitOfPreservesCoequalizer X)).hom
        exact (IsColimit.coconePointUniqueUpToIso _ _).isIso_hom
    have : forall (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      · infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      let _ :
        G.IsSplitPair (F.map (G.map (adj.counit.app Y)))
          (adj.counit.app (F.obj (G.obj Y))) :=
        MonadicityInternal.main_pair_G_split _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] :
/--
Definition of `CreatesColimitOfIsSplitPair` / `CreatesColimitOfIsSplitPair` 的定义

English:
class CreatesColimitOfIsSplitPair
  parameters: (G : D ⥤ C)
  axioms and operations (1):
    - out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G

中文:
类 CreatesColimitOfIsSplitPair
  参数: (G : D ⥤ C)
  公理与运算 (1 个):
    - out : 对任意 {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G
-/
class CreatesColimitOfIsSplitPair (G : D ⥤ C) where
  /-- For all `G`-split pairs `f,g`, `G` creates colimits of `parallelPair f g`. -/
  out : forall {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [CreatesColimitOfIsSplitPair G] :
    CreatesColimit (parallelPair f g) G := CreatesColimitOfIsSplitPair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CreatesColimitOfIsSplitPair
  signature: G] : forall (A
  body: fun _ => CreatesColimitOfIsSplitPair.out _ _

中文:
实例 [CreatesColimitOfIsSplitPair
  签名: G] : 对任意 (A
  定义体: fun _ => CreatesColimitOfIsSplitPair.out _ _

Depends on / 依赖: CreatesColimitOfIsSplitPair, CreatesColimitOfIsSplitPair.out
-/
instance [CreatesColimitOfIsSplitPair G] : forall (A : Algebra adj.toMonad),
    CreatesColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => CreatesColimitOfIsSplitPair.out _ _

/--
**Beck's monadicity theorem**: if `G` has a left adjoint and creates coequalizers of `G`-split
pairs, then it is monadic.
This is the converse of `createsGSplitCoequalizersOfMonadic`.
-/
@[instance_reducible]
/--
Definition of `monadicOfCreatesGSplitCoequalizers` / `monadicOfCreatesGSplitCoequalizers` 的定义

English:
definition monadicOfCreatesGSplitCoequalizers
  signature: [CreatesColimitOfIsSplitPair G]
  body: by
  have I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    rw [hasColimit_iff_of_iso (diagramIsoParallelPair.{v₁} _)]
exact inferInstanceAs HasCoequalizer (G.map f) (G.map g)
  have : HasCoequalizerOfIsSplitPair G := ⟨fun _ _ => hasColimit_of_created (parallelP

中文:
定义 monadicOfCreatesGSplitCoequalizers
  签名: [CreatesColimitOfIsSplitPair G]
  定义体: by
  have I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    rw [hasColimit_iff_of_iso (diagramIsoParallelPair.{v₁} _)]
exact inferInstanceAs HasCoequalizer (G.map f) (G.map g)
  have : HasCoequalizerOfIsSplitPair G := ⟨fun _ _ => hasColimit_of_created (parallelP

Depends on / 依赖: G.IsSplitPair, G.map, HasCoequalizer, HasCoequalizerOfIsSplitPair, HasColimit, IsSplitPair, PreservesColimitOfIsSplitPair, ReflectsColimitOfIsSplitPair, diagramIsoParallelPair, hasColimit_iff_of_iso, hasColimit_of_created, infer_instance, intros, monadicOfHasPreservesReflectsGSplitCoequalizers, parallelPair
-/
def monadicOfCreatesGSplitCoequalizers [CreatesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  have I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    rw [hasColimit_iff_of_iso (diagramIsoParallelPair.{v₁} _)]
exact inferInstanceAs HasCoequalizer (G.map f) (G.map g)
  have : HasCoequalizerOfIsSplitPair G := ⟨fun _ _ => hasColimit_of_created (parallelPair _ _) G⟩
  have : PreservesColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  have : ReflectsColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  exact monadicOfHasPreservesReflectsGSplitCoequalizers adj

/-- An alternate version of **Beck's monadicity theorem**: if `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
@[instance_reducible]
/--
Definition of `monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms` / `monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms` 的定义

English:
definition monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms
  signature: [G.ReflectsIsomorphisms]
  body: by
  have : ReflectsColimitOfIsSplitPair G := ⟨fun f g _ => by
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimit_of_reflectsIsomorphisms⟩
  apply monadicOfHasPreservesReflectsGSplitCoequalizers adj

中文:
定义 monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms
  签名: [G.ReflectsIsomorphisms]
  定义体: by
  have : ReflectsColimitOfIsSplitPair G := ⟨fun f g _ => by
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimit_of_reflectsIsomorphisms⟩
  apply monadicOfHasPreservesReflectsGSplitCoequalizers adj

Depends on / 依赖: HasCoequalizerOfIsSplitPair, HasCoequalizerOfIsSplitPair.out, ReflectsColimitOfIsSplitPair, monadicOfHasPreservesReflectsGSplitCoequalizers, reflectsColimit_of_reflectsIsomorphisms
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [G.ReflectsIsomorphisms]
    [HasCoequalizerOfIsSplitPair G] [PreservesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  have : ReflectsColimitOfIsSplitPair G := ⟨fun f g _ => by
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimit_of_reflectsIsomorphisms⟩
  apply monadicOfHasPreservesReflectsGSplitCoequalizers adj

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [G.ReflectsIsomorphisms]

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsReflexivePair f g], PreservesColimit (parallelPair f g) G] :
/--
Definition of `PreservesColimitOfIsReflexivePair` / `PreservesColimitOfIsReflexivePair` 的定义

English:
class PreservesColimitOfIsReflexivePair
  parameters: (G : C ⥤ D)
  axioms and operations (1):
    - out : forall ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G

中文:
类 PreservesColimitOfIsReflexivePair
  参数: (G : C ⥤ D)
  公理与运算 (1 个):
    - out : 对任意 ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G
-/
class PreservesColimitOfIsReflexivePair (G : C ⥤ D) where
  out : forall ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G

instance {A B} (f g : A ⟶ B) [IsReflexivePair f g] [PreservesColimitOfIsReflexivePair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsReflexivePair.out f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesColimitOfIsReflexivePair
  signature: G] : forall X : Algebra adj.toMonad,
  body: fun _ => PreservesColimitOfIsReflexivePair.out _ _

中文:
实例 [PreservesColimitOfIsReflexivePair
  签名: G] : 对任意 X : Algebra adj.toMonad,
  定义体: fun _ => PreservesColimitOfIsReflexivePair.out _ _

Depends on / 依赖: PreservesColimitOfIsReflexivePair, PreservesColimitOfIsReflexivePair.out
-/
instance [PreservesColimitOfIsReflexivePair G] : forall X : Algebra adj.toMonad,
    PreservesColimit (parallelPair (F.map X.a)
      (NatTrans.app adj.counit (F.obj X.A))) G :=
  fun _ => PreservesColimitOfIsReflexivePair.out _ _

variable [PreservesColimitOfIsReflexivePair G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
@[instance_reducible]
/--
Definition of `monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms` / `monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms` 的定义

English:
definition monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms
  signature: : MonadicRightAdjoint G where
  body: F
  adj := adj
  eqv := by
    have : forall (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw

中文:
定义 monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms
  签名: : MonadicRightAdjoint G where
  定义体: F
  adj := adj
  eqv := by
    have : forall (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G where
  L := F
  adj := adj
  eqv := by
    have : forall (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        exact (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
          (unitColimitOfPreservesCoequalizer X)).isIso_hom
    have : forall (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      · infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      apply reflectsColimit_of_reflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse

end ReflexiveMonadicity

end

end Monad

end CategoryTheory
