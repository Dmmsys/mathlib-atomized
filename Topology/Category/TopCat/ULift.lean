/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Lifting topological spaces to a higher universe

In this file, we construct the functor `uliftFunctor.{v, u} : TopCat.{u} ⥤ TopCat.{max u v}`
which sends a topological space `X : Type u` to a homeomorphic space in `Type (max u v)`.

-/

@[expose] public section

universe w w' v u

open CategoryTheory

namespace TopCat

-- Note: no `@[simps!]` attribute here in order to get good simplification lemmas
-- like `uliftFunctorObjHomeo_naturality_apply` below. We should access
-- `uliftFunctor.obj X` via the homeomorphism `X.uliftFunctorObjHomeo`.
/--
Definition of `uliftFunctor` / `uliftFunctor` 的定义

English:
definition uliftFunctor
  signature: : TopCat.{u} ⥤ TopCat.{max u v} where
  body: TopCat.of (ULift.{v} X)
  map {X Y} f := ofHom ⟨ULift.map f, by fun_prop⟩

中文:
定义 uliftFunctor
  签名: : TopCat.{u} ⥤ TopCat.{max u v} where
  定义体: TopCat.of (ULift.{v} X)
  map {X Y} f := ofHom ⟨ULift.map f, by fun_prop⟩

Depends on / 依赖: TopCat, TopCat.of
-/
def uliftFunctor : TopCat.{u} ⥤ TopCat.{max u v} where
  obj X := TopCat.of (ULift.{v} X)
  map {X Y} f := ofHom ⟨ULift.map f, by fun_prop⟩

/--
Definition of `uliftFunctorObjHomeo` / `uliftFunctorObjHomeo` 的定义

English:
definition uliftFunctorObjHomeo
  signature: (X : TopCat.{u})
  body: Homeomorph.ulift.symm

@[simp]

中文:
定义 uliftFunctorObjHomeo
  签名: (X : TopCat.{u})
  定义体: Homeomorph.ulift.symm

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.ulift.symm
-/
def uliftFunctorObjHomeo (X : TopCat.{u}) : X ≃ₜ uliftFunctor.{v}.obj X :=
  Homeomorph.ulift.symm

@[simp]
/--
lemma `uliftFunctorObjHomeo_naturality_apply` / 引理 `uliftFunctorObjHomeo_naturality_apply`

English:
lemma uliftFunctorObjHomeo_naturality_apply
  given: {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
  proof: rfl

@[simp]

中文:
引理 uliftFunctorObjHomeo_naturality_apply
  条件: {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
  证明: rfl

@[simp]
-/
lemma uliftFunctorObjHomeo_naturality_apply {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    uliftFunctor.{v}.map f (X.uliftFunctorObjHomeo x) =
      Y.uliftFunctorObjHomeo (f x) := rfl

@[simp]
/--
lemma `uliftFunctorObjHomeo_symm_naturality_apply` / 引理 `uliftFunctorObjHomeo_symm_naturality_apply`

English:
lemma uliftFunctorObjHomeo_symm_naturality_apply
  statement: {X Y : TopCat.{u}} (f : X ⟶ Y)
  proof: rfl

中文:
引理 uliftFunctorObjHomeo_symm_naturality_apply
  结论: {X Y : TopCat.{u}} (f : X ⟶ Y)
  证明: rfl
-/
lemma uliftFunctorObjHomeo_symm_naturality_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (x : uliftFunctor.{v}.obj X) :
    Y.uliftFunctorObjHomeo.symm (uliftFunctor.{v}.map f x) =
      f (X.uliftFunctorObjHomeo.symm x) :=
  rfl

/-- The `ULift` functor on categories of topological spaces is compatible
with the one defined on categories of types. -/
@[simps!]
/--
Definition of `uliftFunctorCompForgetIso` / `uliftFunctorCompForgetIso` 的定义

English:
definition uliftFunctorCompForgetIso
  signature: : uliftFunctor.{v, u} ⋙ forget TopCat.{max u v} ≅
  body: Iso.refl _

中文:
定义 uliftFunctorCompForgetIso
  签名: : uliftFunctor.{v, u} ⋙ forget TopCat.{max u v} ≅
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def uliftFunctorCompForgetIso : uliftFunctor.{v, u} ⋙ forget TopCat.{max u v} ≅
    forget TopCat.{u} ⋙ CategoryTheory.uliftFunctor.{v, u} := Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `uliftFunctorFullyFaithful` / `uliftFunctorFullyFaithful` 的定义

English:
definition uliftFunctorFullyFaithful
  signature: : uliftFunctor.{v, u}.FullyFaithful where
  body: ofHom ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩

中文:
定义 uliftFunctorFullyFaithful
  签名: : uliftFunctor.{v, u}.FullyFaithful where
  定义体: ofHom ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩

Depends on / 依赖: ULift.down, ULift.up, fun_prop
-/
def uliftFunctorFullyFaithful : uliftFunctor.{v, u}.FullyFaithful where
  preimage f := ofHom ⟨ULift.down ∘ f ∘ ULift.up, by fun_prop⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: uliftFunctor.{v, u}.Full
  body: uliftFunctorFullyFaithful.full

中文:
实例 :
  签名: uliftFunctor.{v, u}.Full
  定义体: uliftFunctorFullyFaithful.full

Depends on / 依赖: uliftFunctorFullyFaithful, uliftFunctorFullyFaithful.full
-/
instance : uliftFunctor.{v, u}.Full :=
  uliftFunctorFullyFaithful.full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: uliftFunctor.{v, u}.Faithful
  body: uliftFunctorFullyFaithful.faithful

中文:
实例 :
  签名: uliftFunctor.{v, u}.Faithful
  定义体: uliftFunctorFullyFaithful.faithful

Depends on / 依赖: faithful, uliftFunctorFullyFaithful, uliftFunctorFullyFaithful.faithful
-/
instance : uliftFunctor.{v, u}.Faithful :=
  uliftFunctorFullyFaithful.faithful

open Limits

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u}
  body: by
  refine ⟨⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  rw [nonempty_isLimit_iff_eq_induced]
  · refine le_antisymm ?_ ?_
    · rw [le_iInf_iff]
      rintro j s ⟨t, ht, rfl⟩
      refine ⟨Homeomorph.ulift.symm ⁻¹' ((uliftFunctor.map (c.π.app j)) ⁻¹' t), ?_, rfl⟩
      apply Homeomorph.ulift.continuous_invF

中文:
实例 :
  签名: PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u}
  定义体: by
  refine ⟨⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  rw [nonempty_isLimit_iff_eq_induced]
  · refine le_antisymm ?_ ?_
    · rw [le_iInf_iff]
      rintro j s ⟨t, ht, rfl⟩
      refine ⟨Homeomorph.ulift.symm ⁻¹' ((uliftFunctor.map (c.π.app j)) ⁻¹' t), ?_, rfl⟩
      apply Homeomorph.ulift.continuous_invF

Depends on / 依赖: Homeomorph, Homeomorph.ulift.continuous_invFun.isOpen_preimage, Homeomorph.ulift.symm, TopologicalSpace, TopologicalSpace.induced, continuous_invFun, continuous_toFun, generateFrom_iUnion_isOpen, hom.continuous_toFun.isOpen_preimage, induced, induced_iInf, induced_of_isLimit, isOpen_preimage, le_antisymm, le_iInf_iff, nonempty_isLimit_iff_eq_induced, uliftFunctor, uliftFunctor.map
-/
instance : PreservesLimitsOfSize.{w', w} uliftFunctor.{v, u} := by
  refine ⟨⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  rw [nonempty_isLimit_iff_eq_induced]
  · refine le_antisymm ?_ ?_
    · rw [le_iInf_iff]
      rintro j s ⟨t, ht, rfl⟩
      refine ⟨Homeomorph.ulift.symm ⁻¹' ((uliftFunctor.map (c.π.app j)) ⁻¹' t), ?_, rfl⟩
      apply Homeomorph.ulift.continuous_invFun.isOpen_preimage
      apply (uliftFunctor.map (c.π.app j)).hom.continuous_toFun.isOpen_preimage _ ht
    · change _ <= TopologicalSpace.induced _ _
      rw [← generateFrom_iUnion_isOpen]; rw [induced_of_isLimit _ hc]; rw [induced_iInf]; rw [le_iInf_iff]
      rintro i s ⟨-, ⟨t, ht, rfl⟩, rfl⟩
      refine .basic _ ?_
      rw [Set.mem_iUnion]
      exact ⟨i, ULift.down ⁻¹' t, Homeomorph.ulift.continuous_toFun.isOpen_preimage _ ht, rfl⟩
  · exact isLimitOfPreserves (forget TopCat ⋙ CategoryTheory.uliftFunctor) hc

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u}
  body: by
  refine ⟨⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  rw [nonempty_isColimit_iff_eq_coinduced]
  · ext s
    rw [Homeomorph.ulift.symm.isOpenEmbedding.isOpen_iff_preimage_isOpen (by simp)]; rw [isOpen_iff_of_isColimit _ hc]; rw [isOpen_iSup_iff]
    congr!
    rw [Homeomorph.ulift.isOpenEmbedding.isOpen_i

中文:
实例 :
  签名: PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u}
  定义体: by
  refine ⟨⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  rw [nonempty_isColimit_iff_eq_coinduced]
  · ext s
    rw [Homeomorph.ulift.symm.isOpenEmbedding.isOpen_iff_preimage_isOpen (by simp)]; rw [isOpen_iff_of_isColimit _ hc]; rw [isOpen_iSup_iff]
    congr!
    rw [Homeomorph.ulift.isOpenEmbedding.isOpen_i

Depends on / 依赖: CategoryTheory, CategoryTheory.uliftFunctor, Homeomorph, Homeomorph.ulift.isOpenEmbedding.isOpen_iff_preimage_isOpen, Homeomorph.ulift.symm.isOpenEmbedding.isOpen_iff_preimage_isOpen, TopCat, forget, isColimitOfPreserves, isOpenEmbedding, isOpen_iSup_iff, isOpen_iff_of_isColimit, isOpen_iff_preimage_isOpen, nonempty_isColimit_iff_eq_coinduced, uliftFunctor
-/
instance : PreservesColimitsOfSize.{w', w} uliftFunctor.{v, u} := by
  refine ⟨⟨fun {K} => ⟨fun {c} hc => ?_⟩⟩⟩
  rw [nonempty_isColimit_iff_eq_coinduced]
  · ext s
    rw [Homeomorph.ulift.symm.isOpenEmbedding.isOpen_iff_preimage_isOpen (by simp)]; rw [isOpen_iff_of_isColimit _ hc]; rw [isOpen_iSup_iff]
    congr!
    rw [Homeomorph.ulift.isOpenEmbedding.isOpen_iff_preimage_isOpen (by simp)]
    rfl
  · exact isColimitOfPreserves (forget TopCat ⋙ CategoryTheory.uliftFunctor) hc

end TopCat
