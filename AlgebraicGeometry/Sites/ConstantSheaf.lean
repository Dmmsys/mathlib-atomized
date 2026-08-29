/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Terminal

/-!
# Sheaf of continuous maps associated to topological space

Given a topological space `T`, we consider the presheaf on `Scheme` given by `U ↦ C(U, T)`
and show that it is a Zariski sheaf (TODO: show that it is a fpqc sheaf).
When `T` is discrete, this is the constant sheaf associated to `T` (TODO).

## Main declarations

- `AlgebraicGeometry.continuousMapPresheaf`: The sheaf `U ↦ C(U, T)` for a topological space `T`.
- `AlgebraicGeometry.continuousMapPresheafAb`: For a topological abelian group `A`, this is
  `continuousMapPresheaf A` viewed as a sheaf of abelian groups.

## TODOs

- Show that `continuousMapPresheaf` is a sheaf for the fpqc topology (@chrisflav).
-/

@[expose] public section

open CategoryTheory Limits

universe w' w v₂ u₂ v u

namespace AlgebraicGeometry

variable (S : Scheme.{u}) (T : Type v) [TopologicalSpace T]

/--
The yoneda embedding of `TopCat` precomposed with the forgetful functor from `Scheme`. This is the
presheaf `U ↦ C(U, T)`. For universe reasons, we implement it by hand.
-/
@[simps]
/--
Definition of `continuousMapPresheaf` / `continuousMapPresheaf` 的定义

English:
definition continuousMapPresheaf
  signature: (T : Type v) [TopologicalSpace T]
  body: C(U.unop, T)
  map {U V} f := ↾fun g => ContinuousMap.comp g f.unop.base.hom

中文:
定义 continuousMapPresheaf
  签名: (T : 类型v) [拓扑空间 T]
  定义体: C(U.unop, T)
  map {U V} f := ↾fun g => ContinuousMap.comp g f.unop.base.hom

Depends on / 依赖: U.unop
-/
def continuousMapPresheaf (T : Type v) [TopologicalSpace T] : Scheme.{u}ᵒᵖ ⥤ Type (max v u) where
  obj U := C(U.unop, T)
  map {U V} f := ↾fun g => ContinuousMap.comp g f.unop.base.hom

/--
Definition of `continuousMapPresheafIsoUlift` / `continuousMapPresheafIsoUlift` 的定义

English:
definition continuousMapPresheafIsoUlift
  signature: :
  body: NatIso.ofComponents fun U => equivEquivIso
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| Scheme.forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm

中文:
定义 continuousMapPresheafIsoUlift
  签名: :
  定义体: NatIso.ofComponents fun U => equivEquivIso
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| Scheme.forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm

Depends on / 依赖: ContinuousMap, ContinuousMap.uliftEquiv, NatIso, NatIso.ofComponents, Scheme, Scheme.forgetToTop.obj, TopCat, TopCat.Hom.equivContinuousMap, TopCat.of, TopCat.uliftFunctor.obj, equivContinuousMap, equivEquivIso, forgetToTop, ofComponents, symm.trans, uliftEquiv, uliftFunctor
-/
def continuousMapPresheafIsoUlift :
    continuousMapPresheaf T ≅
      Scheme.forgetToTop.op ⋙ TopCat.uliftFunctor.op ⋙ yoneda.obj (.of <| ULift T) :=
NatIso.ofComponents fun U => equivEquivIso
    (ContinuousMap.uliftEquiv U.1 T).symm.trans
    (TopCat.Hom.equivContinuousMap
      (TopCat.uliftFunctor.obj <| Scheme.forgetToTop.obj U.1)
      (TopCat.uliftFunctor.obj (TopCat.of T))).symm

/--
lemma `isSheaf_zariskiTopology_continuousMapPresheaf` / 引理 `isSheaf_zariskiTopology_continuousMapPresheaf`

English:
lemma isSheaf_zariskiTopology_continuousMapPresheaf
  proof: by
  rw [Presheaf.isSheaf_of_iso_iff (continuousMapPresheafIsoUlift T)]
  apply Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopo

中文:
引理 isSheaf_zariskiTopology_continuousMapPresheaf
  证明: by
  rw [Presheaf.isSheaf_of_iso_iff (continuousMapPresheafIsoUlift T)]
  apply Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopo

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable, Presheaf, Presheaf.isSheaf_of_iso_iff, Scheme, Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf, Subcanonical, TopCat, TopCat.grothendieckTopology, TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf, continuousMapPresheafIsoUlift, forgetToTop, grothendieckTopology, isSheaf_iff_isSheaf_of_type, isSheaf_of_isRepresentable, isSheaf_of_iso_iff, op_comp_isSheaf_of_isSheaf, uliftFunctor
-/
lemma isSheaf_zariskiTopology_continuousMapPresheaf :
    Presheaf.IsSheaf Scheme.zariskiTopology (continuousMapPresheaf T) := by
  rw [Presheaf.isSheaf_of_iso_iff (continuousMapPresheafIsoUlift T)]
  apply Scheme.forgetToTop.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  apply TopCat.uliftFunctor.op_comp_isSheaf_of_isSheaf _ TopCat.grothendieckTopology
  rw [isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isSheaf_fpqcTopology_continuousMapPresheaf` / 引理 `isSheaf_fpqcTopology_continuousMapPresheaf`

English:
lemma isSheaf_fpqcTopology_continuousMapPresheaf
  proof: by
  rw [isSheaf_iff_isSheaf_of_type]; rw [Scheme.fpqcTopology_eq_propQCTopology]; rw [isSheaf_type_propQCTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ => ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_zariskiTopology_continuousMapPresheaf _
  · rw [Presieve.isSheafFor_singleton]
   

中文:
引理 isSheaf_fpqcTopology_continuousMapPresheaf
  证明: by
  rw [isSheaf_iff_isSheaf_of_type]; rw [Scheme.fpqcTopology_eq_propQCTopology]; rw [isSheaf_type_propQCTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ => ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_zariskiTopology_continuousMapPresheaf _
  · rw [Presieve.isSheafFor_singleton]
   

Depends on / 依赖: Flat.isQuotientMap_of_surjective, IsQuotientMap, Presieve, Presieve.isSheafFor_singleton, Scheme, Scheme.fpqcTopology_eq_propQCTopology, Spec.map, Topology, Topology.IsQuotientMap, Topology.IsQuotientMap.lift, fpqcTopology_eq_propQCTopology, isQuotientMap_of_surjective, isSheafFor_singleton, isSheaf_iff_isSheaf_of_type, isSheaf_type_propQCTopology_iff, isSheaf_zariskiTopology_continuousMapPresheaf
-/
lemma isSheaf_fpqcTopology_continuousMapPresheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheaf T) := by
  rw [isSheaf_iff_isSheaf_of_type]; rw [Scheme.fpqcTopology_eq_propQCTopology]; rw [isSheaf_type_propQCTopology_iff]
  refine ⟨?_, fun {R S} f hf₁ hf₂ => ?_⟩
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_zariskiTopology_continuousMapPresheaf _
  · rw [Presieve.isSheafFor_singleton]
    have : Topology.IsQuotientMap (Spec.map f) := Flat.isQuotientMap_of_surjective _
    intro (x : C(Spec S, T)) h
    refine ⟨?_, ?_, ?_⟩
    · refine Topology.IsQuotientMap.lift this x fun a b hfab => ?_
      obtain ⟨c, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback a b hfab
      exact congr($(h (pullback.fst (Spec.map f) (Spec.map f))
        (pullback.snd _ _) pullback.condition).1 c)
    · apply Topology.IsQuotientMap.lift_comp
    · intro y hy
      rwa [← ContinuousMap.cancel_right (Spec.map f).surjective, Topology.IsQuotientMap.lift_comp]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `continuousMapPresheafEquivOfTotallyDisconnectedSpace` / `continuousMapPresheafEquivOfTotallyDisconnectedSpace` 的定义

English:
definition continuousMapPresheafEquivOfTotallyDisconnectedSpace
  signature: [TotallyDisconnectedSpace T]
  body: ⟨f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous⟩
  invFun f := .comp f ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  right_inv f := by
    apply ContinuousMap.coe_injective
    dsimp
    exact (Continuous.connectedComponentsLift_unique _ _ (by 

中文:
定义 continuousMapPresheafEquivOfTotallyDisconnectedSpace
  签名: [全不连通空间 T]
  定义体: ⟨f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous⟩
  invFun f := .comp f ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  right_inv f := by
    apply ContinuousMap.coe_injective
    dsimp
    exact (Continuous.connectedComponentsLift_unique _ _ (by 

Depends on / 依赖: connectedComponentsLift, connectedComponentsLift_continuous, continuous, f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous
-/
def continuousMapPresheafEquivOfTotallyDisconnectedSpace [TotallyDisconnectedSpace T]
    (U : Scheme.{u}) :
    (continuousMapPresheaf T).obj (.op U) ≃ C(ConnectedComponents U, T) where
  toFun f := ⟨f.continuous.connectedComponentsLift, f.continuous.connectedComponentsLift_continuous⟩
  invFun f := .comp f ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  right_inv f := by
    apply ContinuousMap.coe_injective
    dsimp
    exact (Continuous.connectedComponentsLift_unique _ _ (by simp)).symm

/--
Definition of `continuousMapPresheafAb` / `continuousMapPresheafAb` 的定义

English:
definition continuousMapPresheafAb
  signature: (A : Type v) [TopologicalSpace A] [AddCommGroup A]
  body: AddCommGrpCat.of C(U.unop, A)
  map {U V} f := AddCommGrpCat.ofHom (ContinuousMap.compAddMonoidHom' f.unop.base.hom)

中文:
定义 continuousMapPresheafAb
  签名: (A : 类型v) [拓扑空间 A] [加法交换群 A]
  定义体: AddCommGrpCat.of C(U.unop, A)
  map {U V} f := AddCommGrpCat.ofHom (ContinuousMap.compAddMonoidHom' f.unop.base.hom)

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, U.unop
-/
def continuousMapPresheafAb (A : Type v) [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] :
    Scheme.{u}ᵒᵖ ⥤ Ab.{max v u} where
  obj U := AddCommGrpCat.of C(U.unop, A)
  map {U V} f := AddCommGrpCat.ofHom (ContinuousMap.compAddMonoidHom' f.unop.base.hom)

variable (A : Type v) [TopologicalSpace A] [AddCommGroup A] [IsTopologicalAddGroup A]

/--
Definition of `continuousMapPresheafAbForgetIso` / `continuousMapPresheafAbForgetIso` 的定义

English:
definition continuousMapPresheafAbForgetIso
  signature: :
  body: Iso.refl _

中文:
定义 continuousMapPresheafAbForgetIso
  签名: :
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def continuousMapPresheafAbForgetIso :
    continuousMapPresheafAb A ⋙ CategoryTheory.forget Ab ≅ continuousMapPresheaf A :=
  Iso.refl _

/--
lemma `isSheaf_fpqcTopology_continuousMapPresheafAb` / 引理 `isSheaf_fpqcTopology_continuousMapPresheafAb`

English:
lemma isSheaf_fpqcTopology_continuousMapPresheafAb
  proof: by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact isSheaf_fpqcTopology_continuousMapPresheaf _

中文:
引理 isSheaf_fpqcTopology_continuousMapPresheafAb
  证明: by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact isSheaf_fpqcTopology_continuousMapPresheaf _

Depends on / 依赖: Presheaf, Presheaf.isSheaf_of_isSheaf_comp, forget, isSheaf_fpqcTopology_continuousMapPresheaf, isSheaf_of_isSheaf_comp
-/
lemma isSheaf_fpqcTopology_continuousMapPresheafAb :
    Presheaf.IsSheaf Scheme.fpqcTopology (continuousMapPresheafAb A) := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact isSheaf_fpqcTopology_continuousMapPresheaf _

end AlgebraicGeometry
