/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ᶜ F.obj (U i)` and `∏ᶜ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the "pairwise intersections" sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/

@[expose] public section


universe v' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]
variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι -> Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

/--
Definition of `piOpens` / `piOpens` 的定义

English:
definition piOpens
  signature: : C
  body: ∏ᶜ fun i : ι => F.obj (op (U i))

中文:
定义 piOpens
  签名: : C
  定义体: ∏ᶜ fun i : ι => F.obj (op (U i))

Depends on / 依赖: F.obj
-/
def piOpens : C :=
  ∏ᶜ fun i : ι => F.obj (op (U i))

/--
Definition of `piInters` / `piInters` 的定义

English:
definition piInters
  signature: : C
  body: ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

中文:
定义 pi整数ers
  签名: : C
  定义体: ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

Depends on / 依赖: F.obj
-/
def piInters : C :=
  ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

/--
Definition of `leftRes` / `leftRes` 的定义

English:
definition leftRes
  signature: : piOpens F U ⟶ piInters.{v'} F U
  body: Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

中文:
定义 leftRes
  签名: : piOpens F U ⟶ pi整数ers.{v'} F U
  定义体: Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

Depends on / 依赖: F.map, Pi.lift, infLELeft
-/
def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

/--
Definition of `rightRes` / `rightRes` 的定义

English:
definition rightRes
  signature: : piOpens F U ⟶ piInters.{v'} F U
  body: Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

中文:
定义 rightRes
  签名: : piOpens F U ⟶ pi整数ers.{v'} F U
  定义体: Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

Depends on / 依赖: F.map, Pi.lift, infLERight
-/
def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

/--
Definition of `res` / `res` 的定义

English:
definition res
  signature: : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U
  body: Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

中文:
定义 res
  签名: : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U
  定义体: Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

Depends on / 依赖: F.map, Pi.lift, TopologicalSpace, TopologicalSpace.Opens.leSupr, leSupr
-/
def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

set_option backward.isDefEq.respectTransparency false in
@[simp, elementwise]
/--
theorem `res_π` / 定理 `res_π`

English:
theorem res_π
  given: (i : ι)
  statement: res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op
  proof: by
  rw [res]; rw [limit.lift_π]; rw [Fan.mk_π_app]

中文:
定理 res_π
  条件: (i : ι)
  结论: res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op
  证明: by
  rw [res]; rw [limit.lift_π]; rw [Fan.mk_π_app]

Depends on / 依赖: Fan.mk_, limit.lift_
-/
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res]; rw [limit.lift_π]; rw [Fan.mk_π_app]

/--
theorem `piOpens.hom_ext` / 定理 `piOpens.hom_ext`

English:
theorem piOpens.hom_ext
  proof: limit.hom_ext w

中文:
定理 piOpens.hom_ext
  证明: limit.hom_ext w
-/
@[ext] theorem piOpens.hom_ext
    {X : C} {f f' : X ⟶ piOpens F U} (w : forall j, f ≫ limit.π _ j = f' ≫ limit.π _ j) : f = f' :=
  limit.hom_ext w

/--
theorem `piInters.hom_ext` / 定理 `piInters.hom_ext`

English:
theorem piInters.hom_ext
  proof: limit.hom_ext w

中文:
定理 pi整数ers.hom_ext
  证明: limit.hom_ext w
-/
@[ext] theorem piInters.hom_ext
    {X : C} {f f' : X ⟶ piInters F U} (w : forall j, f ≫ limit.π _ j = f' ≫ limit.π _ j) : f = f' :=
  limit.hom_ext w

set_option backward.isDefEq.respectTransparency false in
@[elementwise]
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: res F U ≫ leftRes F U = res F U ≫ rightRes F U
  proof: by
  dsimp [res, leftRes, rightRes]
  ext
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr 1

中文:
定理 w
  结论: res F U ≫ leftRes F U = res F U ≫ rightRes F U
  证明: by
  dsimp [res, leftRes, rightRes]
  ext
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr 1

Depends on / 依赖: Category, Category.assoc, F.map_comp, Fan.mk_, leftRes, limit.lift_, map_comp, rightRes
-/
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U := by
  dsimp [res, leftRes, rightRes]
  ext
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr 1

/--
Definition of `diagram` / `diagram` 的定义

English:
abbreviation diagram
  signature: : WalkingParallelPair ⥤ C
  body: parallelPair (leftRes.{v'} F U) (rightRes F U)

中文:
缩写 diagram
  签名: : WalkingParallelPair ⥤ C
  定义体: parallelPair (leftRes.{v'} F U) (rightRes F U)

Depends on / 依赖: leftRes, parallelPair, rightRes
-/
abbrev diagram : WalkingParallelPair ⥤ C :=
  parallelPair (leftRes.{v'} F U) (rightRes F U)

/--
Definition of `fork` / `fork` 的定义

English:
definition fork
  signature: : Fork.{v} (leftRes F U) (rightRes F U)
  body: Fork.ofι _ (w F U)

@[simp]

中文:
定义 fork
  签名: : 叉.{v} (leftRes F U) (rightRes F U)
  定义体: Fork.ofι _ (w F U)

@[simp]

Depends on / 依赖: Fork.of
-/
def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)

@[simp]
/--
theorem `fork_pt` / 定理 `fork_pt`

English:
theorem fork_pt
  statement: (fork F U).pt = F.obj (op (iSup U))
  proof: rfl

@[simp]

中文:
定理 fork_pt
  结论: (fork F U).pt = F.obj (op (iSup U))
  证明: rfl

@[simp]
-/
theorem fork_pt : (fork F U).pt = F.obj (op (iSup U)) :=
  rfl

@[simp]
/--
theorem `fork_ι` / 定理 `fork_ι`

English:
theorem fork_ι
  statement: (fork F U).ι = res F U
  proof: rfl

@[simp]

中文:
定理 fork_ι
  结论: (fork F U).ι = res F U
  证明: rfl

@[simp]
-/
theorem fork_ι : (fork F U).ι = res F U :=
  rfl

@[simp]
/--
theorem `fork_π_app_walkingParallelPair_zero` / 定理 `fork_π_app_walkingParallelPair_zero`

English:
theorem fork_π_app_walkingParallelPair_zero
  statement: (fork F U).π.app WalkingParallelPair.zero = res F U
  proof: rfl

@[simp]

中文:
定理 fork_π_app_walkingParallelPair_zero
  结论: (fork F U).π.app WalkingParallelPair.zero = res F U
  证明: rfl

@[simp]
-/
theorem fork_π_app_walkingParallelPair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl

@[simp]
/--
theorem `fork_π_app_walkingParallelPair_one` / 定理 `fork_π_app_walkingParallelPair_one`

English:
theorem fork_π_app_walkingParallelPair_one
  proof: rfl

中文:
定理 fork_π_app_walkingParallelPair_one
  证明: rfl
-/
theorem fork_π_app_walkingParallelPair_one :
    (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl

variable {F} {G : Presheaf C X}

/-- Isomorphic presheaves have isomorphic `piOpens` for any cover `U`. -/
@[simp]
/--
Definition of `piOpens.isoOfIso` / `piOpens.isoOfIso` 的定义

English:
definition piOpens.isoOfIso
  signature: (α : F ≅ G)
  body: Pi.mapIso fun _ => α.app _

中文:
定义 piOpens.isoOfIso
  签名: (α : F ≅ G)
  定义体: Pi.mapIso fun _ => α.app _

Depends on / 依赖: Pi.mapIso, mapIso
-/
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens.{v'} G U :=
  Pi.mapIso fun _ => α.app _

/-- Isomorphic presheaves have isomorphic `piInters` for any cover `U`. -/
@[simp]
/--
Definition of `piInters.isoOfIso` / `piInters.isoOfIso` 的定义

English:
definition piInters.isoOfIso
  signature: (α : F ≅ G)
  body: Pi.mapIso fun _ => α.app _

中文:
定义 pi整数ers.isoOfIso
  签名: (α : F ≅ G)
  定义体: Pi.mapIso fun _ => α.app _

Depends on / 依赖: Pi.mapIso, mapIso
-/
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters.{v'} G U :=
  Pi.mapIso fun _ => α.app _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `diagram.isoOfIso` / `diagram.isoOfIso` 的定义

English:
definition diagram.isoOfIso
  signature: (α : F ≅ G)
  body: NatIso.ofComponents (by
    rintro ⟨⟩
    · exact piOpens.isoOfIso U α
    · exact piInters.isoOfIso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · dsimp
        refine Pi.hom_ext _ _ fun b => ?_
        simp [leftRes]
      · dsimp [diagram]
        refine Pi.hom_ext _ _ fun b => ?_
        simp [rightRes]
      · simp)

中文:
定义 diagram.isoOfIso
  签名: (α : F ≅ G)
  定义体: NatIso.ofComponents (by
    rintro ⟨⟩
    · exact piOpens.isoOfIso U α
    · exact piInters.isoOfIso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · dsimp
        refine Pi.hom_ext _ _ fun b => ?_
        simp [leftRes]
      · dsimp [diagram]
        refine Pi.hom_ext _ _ fun b => ?_
        simp [rightRes]
      · simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, Pi.hom_ext, diagram, hom_ext, isoOfIso, leftRes, ofComponents, piInters, piInters.isoOfIso, piOpens, piOpens.isoOfIso, rightRes
-/
def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
  NatIso.ofComponents (by
    rintro ⟨⟩
    · exact piOpens.isoOfIso U α
    · exact piInters.isoOfIso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · dsimp
        refine Pi.hom_ext _ _ fun b => ?_
        simp [leftRes]
      · dsimp [diagram]
        refine Pi.hom_ext _ _ fun b => ?_
        simp [rightRes]
      · simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fork.isoOfIso` / `fork.isoOfIso` 的定义

English:
definition fork.isoOfIso
  signature: (α : F ≅ G)
  body: by
  fapply Fork.ext
  · apply α.app
  · dsimp
    refine Pi.hom_ext _ _ fun b => ?_
    dsimp only [Fork.ι]
    simp [res, diagram.isoOfIso]

中文:
定义 fork.isoOfIso
  签名: (α : F ≅ G)
  定义体: by
  fapply Fork.ext
  · apply α.app
  · dsimp
    refine Pi.hom_ext _ _ fun b => ?_
    dsimp only [Fork.ι]
    simp [res, diagram.isoOfIso]

Depends on / 依赖: Fork.ext, Pi.hom_ext, diagram, diagram.isoOfIso, fapply, hom_ext, isoOfIso
-/
def fork.isoOfIso (α : F ≅ G) :
    fork F U ≅ (Cone.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) := by
  fapply Fork.ext
  · apply α.app
  · dsimp
    refine Pi.hom_ext _ _ fun b => ?_
    dsimp only [Fork.ι]
    simp [res, diagram.isoOfIso]

end SheafConditionEqualizerProducts

/--
Definition of `IsSheafEqualizerProducts` / `IsSheafEqualizerProducts` 的定义

English:
definition IsSheafEqualizerProducts
  signature: (F : Presheaf.{v', v, u} C X)
  body: forall ⦃ι : Type v'⦄ (U : ι -> Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

中文:
定义 IsSheafEqualizerProducts
  签名: (F : 预层.{v', v, u} C X)
  定义体: forall ⦃ι : Type v'⦄ (U : ι -> Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

Depends on / 依赖: IsLimit, Nonempty, SheafConditionEqualizerProducts, SheafConditionEqualizerProducts.fork
-/
def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  forall ⦃ι : Type v'⦄ (U : ι -> Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

/-!
The remainder of this file shows that the "equalizer products" sheaf condition is equivalent
to the "pairwise intersections" sheaf condition.
-/


namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
/--
Definition of `coneEquivFunctorObj` / `coneEquivFunctorObj` 的定义

English:
definition coneEquivFunctorObj
  signature: (c : Cone ((diagram U).op ⋙ F))
  body: c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · dsimp
          ext
          simp
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.leftRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.left i j))
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.rightRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.right i j))
        · dsimp
          ext
          simp }

中文:
定义 coneEquivFunctorObj
  签名: (c : 锥 ((diagram U).op ⋙ F))
  定义体: c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · dsimp
          ext
          simp
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.leftRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.left i j))
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.rightRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.right i j))
        · dsimp
          ext
          simp }

Depends on / 依赖: c.pt
-/
def coneEquivFunctorObj (c : Cone ((diagram U).op ⋙ F)) :
    Cone (SheafConditionEqualizerProducts.diagram F U) where
  pt := c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · dsimp
          ext
          simp
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.leftRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.left i j))
        · dsimp
          ext ij
          rcases ij with ⟨i, j⟩
          simpa [SheafConditionEqualizerProducts.rightRes]
            using! c.π.naturality (Quiver.Hom.op (Hom.right i j))
        · dsimp
          ext
          simp }

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/--
Definition of `coneEquivFunctor` / `coneEquivFunctor` 的定义

English:
definition coneEquivFunctor
  signature: :
  body: coneEquivFunctorObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := fun j => by
        cases j <;>
          · dsimp
            ext
            simp }

中文:
定义 coneEquivFunctor
  签名: :
  定义体: coneEquivFunctorObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := fun j => by
        cases j <;>
          · dsimp
            ext
            simp }

Depends on / 依赖: coneEquivFunctorObj
-/
def coneEquivFunctor :
    Limits.Cone ((diagram U).op ⋙ F) ⥤
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  obj c := coneEquivFunctorObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := fun j => by
        cases j <;>
          · dsimp
            ext
            simp }

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
/--
Definition of `coneEquivInverseObj` / `coneEquivInverseObj` 的定义

English:
definition coneEquivInverseObj
  signature: (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U))
  body: c.pt
  π :=
    { app := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
      naturality := by
        intro x y f
        induction x with | op x => ?_
        induction y with | op y => ?_
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          rw [F.map_id]
          simp
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.left
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (i, j)
          rw [h']
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          rfl
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.right
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          rw [F.map_id]
          simp }

中文:
定义 coneEquivInverseObj
  签名: (c : Limits.锥 (SheafConditionEqualizerProducts.diagram F U))
  定义体: c.pt
  π :=
    { app := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
      naturality := by
        intro x y f
        induction x with | op x => ?_
        induction y with | op y => ?_
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          rw [F.map_id]
          simp
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.left
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (i, j)
          rw [h']
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          rfl
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.right
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          rw [F.map_id]
          simp }

Depends on / 依赖: c.pt
-/
def coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :
    Limits.Cone ((diagram U).op ⋙ F) where
  pt := c.pt
  π :=
    { app := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
      naturality := by
        intro x y f
        induction x with | op x => ?_
        induction y with | op y => ?_
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          rw [F.map_id]
          simp
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.left
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (i, j)
          rw [h']
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          rfl
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.right
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          rw [F.map_id]
          simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/--
Definition of `coneEquivInverse` / `coneEquivInverse` 的定义

English:
definition coneEquivInverse
  signature: :
  body: coneEquivInverseObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [Fork.ι]
          rw [← f.w WalkingParallelPair.zero]; rw [Category.assoc]
        · dsimp
          rw [← f.w WalkingParallelPair.one]; rw [Category.assoc] }

中文:
定义 coneEquivInverse
  签名: :
  定义体: coneEquivInverseObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [Fork.ι]
          rw [← f.w WalkingParallelPair.zero]; rw [Category.assoc]
        · dsimp
          rw [← f.w WalkingParallelPair.one]; rw [Category.assoc] }

Depends on / 依赖: coneEquivInverseObj
-/
def coneEquivInverse :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤
      Limits.Cone ((diagram U).op ⋙ F) where
  obj c := coneEquivInverseObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := by
        intro x
        induction x with | op x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [Fork.ι]
          rw [← f.w WalkingParallelPair.zero]; rw [Category.assoc]
        · dsimp
          rw [← f.w WalkingParallelPair.one]; rw [Category.assoc] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps]
/--
Definition of `coneEquivUnitIsoApp` / `coneEquivUnitIsoApp` 的定义

English:
definition coneEquivUnitIsoApp
  signature: (c : Cone ((diagram U).op ⋙ F))
  body: { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
  inv :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }

中文:
定义 coneEquivUnitIsoApp
  签名: (c : 锥 ((diagram U).op ⋙ F))
  定义体: { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
  inv :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }

Depends on / 依赖: Category, Category.id_comp, Limits, Limits.Fan.mk_, Limits.limit.lift_, coneEquivInverse, id_comp
-/
def coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅
      (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c where
  hom :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
  inv :=
    { hom := 𝟙 _
      w := fun j => by
        induction j with | op j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }

set_option backward.defeqAttrib.useBackward true in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/--
Definition of `coneEquivUnitIso` / `coneEquivUnitIso` 的定义

English:
definition coneEquivUnitIso
  signature: :
  body: NatIso.ofComponents (coneEquivUnitIsoApp F U)

中文:
定义 coneEquivUnitIso
  签名: :
  定义体: NatIso.ofComponents (coneEquivUnitIsoApp F U)

Depends on / 依赖: NatIso, NatIso.ofComponents, coneEquivUnitIsoApp, ofComponents
-/
def coneEquivUnitIso :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Implementation of `SheafConditionPairwiseIntersections.coneEquiv`. -/
@[simps!]
/--
Definition of `coneEquivCounitIso` / `coneEquivCounitIso` 的定义

English:
definition coneEquivCounitIso
  signature: :
  body: NatIso.ofComponents
    (fun c =>
      { hom :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp }
        inv :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp } })
    fun {c d} f => by
    ext
    dsimp
    simp only [Category.comp_id, Category.id_comp]

中文:
定义 coneEquivCounitIso
  签名: :
  定义体: NatIso.ofComponents
    (fun c =>
      { hom :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp }
        inv :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp } })
    fun {c d} f => by
    ext
    dsimp
    simp only [Category.comp_id, Category.id_comp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, NatIso, NatIso.ofComponents, comp_id, id_comp, ofComponents
-/
def coneEquivCounitIso :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅
      𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { hom :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp }
        inv :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · dsimp
                ext
                simp
              · dsimp
                ext
                simp } })
    fun {c d} f => by
    ext
    dsimp
    simp only [Category.comp_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
/--
Cones over `diagram U ⋙ F` are the same as a cones over the usual sheaf condition equalizer diagram.
-/
@[simps]
/--
Definition of `coneEquiv` / `coneEquiv` 的定义

English:
definition coneEquiv
  signature: :
  body: coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

中文:
定义 coneEquiv
  签名: :
  定义体: coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

Depends on / 依赖: coneEquivFunctor
-/
def coneEquiv :
    Limits.Cone ((diagram U).op ⋙ F) ≌
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitMapConeOfIsLimitSheafConditionFork` / `isLimitMapConeOfIsLimitSheafConditionFork` 的定义

English:
definition isLimitMapConeOfIsLimitSheafConditionFork
  body: IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

中文:
定义 isLimitMapConeOfIsLimitSheafConditionFork
  定义体: IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.map_comp, Fan.mk_, IsLimit, IsLimit.ofConeEquiv, IsLimit.ofIsoLimit, SheafConditionEqualizerProducts, SheafConditionEqualizerProducts.leftRes, SheafConditionEqualizerProducts.res, coneEqui, coneEquiv, coneEquivInverse, id_comp, leftRes, limit.lift_, map_comp, ofConeEquiv, ofIsoLimit
-/
def isLimitMapConeOfIsLimitSheafConditionFork
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | op x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitSheafConditionForkOfIsLimitMapCone` / `isLimitSheafConditionForkOfIsLimitMapCone` 的定义

English:
definition isLimitSheafConditionForkOfIsLimitMapCone
  signature: (Q : IsLimit (F.mapCone (cocone U).op))
  body: IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

中文:
定义 isLimitSheafConditionForkOfIsLimitMapCone
  签名: (Q : 是极限 (F.mapCone (cocone U).op))
  定义体: IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.map_comp, Fan.mk_, IsLimit, IsLimit.ofConeEquiv, IsLimit.ofIsoLimit, SheafConditionEqualizerProdu, SheafConditionEqualizerProducts, SheafConditionEqualizerProducts.leftRes, SheafConditionEqualizerProducts.res, coneEquiv, coneEquivInverse, id_comp, leftRes, limit.lift_, map_comp, ofConeEquiv, ofIsoLimit
-/
def isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone U).op)) :
    IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · dsimp
              ext
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

/--
theorem `isSheaf_iff_isSheafEqualizerProducts` / 定理 `isSheaf_iff_isSheafEqualizerProducts`

English:
theorem isSheaf_iff_isSheafEqualizerProducts
  given: (F : Presheaf C X)
  proof: (isSheaf_iff_isSheafPairwiseIntersections F).trans
    Iff.intro (fun h _ U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h _ U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩

中文:
定理 isSheaf_iff_isSheafEqualizerProducts
  条件: (F : 预层 C X)
  证明: (isSheaf_iff_isSheafPairwiseIntersections F).trans
    Iff.intro (fun h _ U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h _ U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩

Depends on / 依赖: Iff.intro, isLimitMapConeOfIsLimitSheafConditionFork, isLimitSheafConditionForkOfIsLimitMapCone, isSheaf_iff_isSheafPairwiseIntersections
-/
theorem isSheaf_iff_isSheafEqualizerProducts (F : Presheaf C X) :
    F.IsSheaf ↔ F.IsSheafEqualizerProducts :=
(isSheaf_iff_isSheafPairwiseIntersections F).trans
    Iff.intro (fun h _ U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h _ U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩

end Presheaf

end TopCat
